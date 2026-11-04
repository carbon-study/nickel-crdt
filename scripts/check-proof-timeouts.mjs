// Tests actual make/GNU timeout wiring with an explicitly simulated compiler.
// These temporary .checked files never enter the immutable real-model cache.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {verify,proofFlags} from './proof-cache.mjs';
export async function checkTimeoutBudgets() {
  const report=console.log,output=[];
  console.log=(...args)=>output.push(args.join(' '));
  const dir=await fs.mkdtemp(path.join(os.tmpdir(),'nickel-timeout-test-'));
  try {
    const fake=path.join(dir,'simulated-fstar.mjs'),control=path.join(dir,'control.json');
    await fs.writeFile(fake,`#!${process.execPath}
import fs from 'node:fs';import path from 'node:path';
const args=process.argv.slice(2),root=args.at(-1),cache=args[args.indexOf('--cache_dir')+1];
if(args.includes('--dep')) {console.log(cache+'/'+path.basename(root)+'.checked: '+root);}
else {
 const c=JSON.parse(fs.readFileSync(${JSON.stringify(control)},'utf8'));
 fs.writeFileSync(${JSON.stringify(path.join(dir,'args.json'))},JSON.stringify(args));
 await new Promise(r=>setTimeout(r,c.delay));
 if(c.status)process.exit(c.status);
 fs.mkdirSync(cache,{recursive:true});fs.writeFileSync(cache+'/'+path.basename(root)+'.checked','simulated compiler result, not a proof');
}
`,{mode:0o755});
    const check=async(name,options={})=> {
      const work=path.join(dir,name);await fs.mkdir(work,{recursive:true});
      const root=path.join(work,'Test.fst');await fs.writeFile(root,'module Test\n');
      return {work,result:await verify({dir:work,roots:[root],fstar:fake,models:dir,...options})};
    };
    await fs.writeFile(control,JSON.stringify({delay:0,status:0}));
    const normal=await check('normal');assert.equal(normal.result.status,0,normal.result.log);
    assert.match(await fs.readFile(path.join(normal.work,'Makefile'),'utf8'),/'60s'/);
    const extended=await check('bootstrap',{moduleSeconds:180,seconds:600});assert.equal(extended.result.status,0,extended.result.log);
    assert.match(await fs.readFile(path.join(extended.work,'Makefile'),'utf8'),/'180s'/);
    const args=JSON.parse(await fs.readFile(path.join(dir,'args.json'),'utf8'));
    assert.deepEqual(args.slice(args.indexOf('--cmi'),args.indexOf('--cmi')+proofFlags.length),proofFlags);
    assert.equal(args[args.indexOf('--z3rlimit')+1],'100');
    for(const n of [0,-1,181,NaN,1.5])await assert.rejects(()=>check('invalid-'+String(n),{moduleSeconds:n}),/moduleSeconds/);
    await assert.rejects(()=>check('project-override',{modelCache:dir,moduleSeconds:180}),/project module budget/);
    await fs.writeFile(control,JSON.stringify({delay:1200,status:0}));
    const timed=await check('bounded',{moduleSeconds:1,seconds:10});assert.equal(timed.result.status,2,timed.result.log);
    assert.match(timed.result.log,/Error 124/);
    await assert.rejects(()=>fs.access(path.join(timed.work,'checked','Test.fst.checked')));
    const recovered=await check('bounded',{moduleSeconds:2,seconds:10});assert.equal(recovered.result.status,0,recovered.result.log);
    await fs.writeFile(control,JSON.stringify({delay:0,status:2}));
    const failed=await check('failure',{moduleSeconds:180,seconds:600});assert.equal(failed.result.status,2,failed.result.log);
    await assert.rejects(()=>fs.access(path.join(failed.work,'checked','Test.fst.checked')));
    report('PASS simulated compiler: default 60s, cold-only 180s, actual timeout/retry and failure remain nonzero; solver flags unchanged');
  } catch(error) {report(output.join('\n'));throw error;}
  finally {console.log=report;await fs.rm(dir,{recursive:true,force:true});}
}
if(process.argv[1]===fileURLToPath(import.meta.url))await checkTimeoutBudgets();
