// Tests actual make/GNU timeout wiring with an explicitly simulated compiler.
// These temporary .checked files never enter the immutable real-model cache.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {verify,proofFlags,projectCompilerTargets,aggregateProofSeconds} from './proof-cache.mjs';
export async function checkTimeoutBudgets() {
  const report=console.log,output=[];
  console.log=(...args)=>output.push(args.join(' '));
  const dir=await fs.mkdtemp(path.join(os.tmpdir(),'nickel-timeout-test-'));
  try {
    const fake=path.join(dir,'simulated-fstar.mjs'),control=path.join(dir,'control.json');
    await fs.writeFile(fake,`#!${process.execPath}
import fs from 'node:fs';import path from 'node:path';
const args=process.argv.slice(2),root=args.at(-1),cache=args[args.indexOf('--cache_dir')+1];
const c=JSON.parse(fs.readFileSync(${JSON.stringify(control)},'utf8'));
if(args.includes('--dep')) {
 const names=c.chain??[path.basename(root)];
 for(let i=0;i<names.length;i++)console.log(cache+'/'+names[i]+'.checked: '+path.join(path.dirname(root),names[i])+(i?' '+cache+'/'+names[i-1]+'.checked':''));
 if(c.unused)console.log(cache+'/Unused.fst.checked: '+path.join(path.dirname(root),'Unused.fst'));
}
else {
 fs.writeFileSync(${JSON.stringify(path.join(dir,'args.json'))},JSON.stringify(args));
 if(c.ignoreTerm){process.on('SIGTERM',()=>{});fs.writeFileSync(${JSON.stringify(path.join(dir,'compiler.pid'))},String(process.pid));}
 await new Promise(r=>setTimeout(r,c.delay));
 if(c.status)process.exit(c.status);
 fs.mkdirSync(cache,{recursive:true});fs.writeFileSync(cache+'/'+path.basename(root)+'.checked','simulated compiler result, not a proof');
}
`,{mode:0o755});
    const check=async(name,options={},names=['Test.fst'])=> {
      const work=path.join(dir,name);await fs.mkdir(work,{recursive:true});
      for(const name of [...names,'Unused.fst'])await fs.writeFile(path.join(work,name),'module '+name.replace(/\.fst$/,'')+'\n');
      const root=path.join(work,names.at(-1));
      return {work,result:await verify({dir:work,roots:[root],fstar:fake,models:dir,...options})};
    };
    const checked=name=>path.join(dir,'checked',name+'.checked');
    const graph=[
      '# ignored: '+checked('Unused.fst'),
      checked('A.fsti')+': '+path.join(dir,'A.fsti'),
      checked('A.fst')+': \\\n '+path.join(dir,'A.fst')+' '+checked('A.fsti'),
      checked('B.fst')+': '+path.join(dir,'B.fst')+' '+checked('A.fst')+' '+checked('A.fst')+' /immutable/Model.fst.checked',
      checked('Unused.fst')+': '+path.join(dir,'Unused.fst'),
    ].join('\n');
    const targets=projectCompilerTargets(graph,dir,['A.fsti','A.fst','B.fst','Unused.fst'],[checked('B.fst'),checked('B.fst')]);
    assert.deepEqual(targets,[checked('A.fst'),checked('A.fsti'),checked('B.fst')].sort());
    assert.equal(aggregateProofSeconds(targets.length,60),196);
    assert.equal(aggregateProofSeconds(7,60),444);
    assert.throws(()=>aggregateProofSeconds(0,60),/aggregate/);
    assert.throws(()=>aggregateProofSeconds(Number.MAX_SAFE_INTEGER,60),/aggregate/);
    assert.throws(()=>projectCompilerTargets('',dir,['A.fst'],[checked('A.fst')]),/missing compiler dependency rule/);
    assert.throws(()=>projectCompilerTargets(graph,dir,['B.fst'],[checked('B.fst')]),/unexpected local compiler target/);
    await fs.writeFile(control,JSON.stringify({delay:0,status:0}));
    const normal=await check('normal');assert.equal(normal.result.status,0,normal.result.log);
    assert.match(await fs.readFile(path.join(normal.work,'Makefile'),'utf8'),/'60s'/);
    assert.equal(normal.result.budget.policy,'graph-derived');
    assert.equal(normal.result.budget.seconds,72);
    assert.equal(normal.result.budget.compilerTargets.length,1);
    const extended=await check('bootstrap',{moduleSeconds:180,seconds:600});assert.equal(extended.result.status,0,extended.result.log);
    assert.match(await fs.readFile(path.join(extended.work,'Makefile'),'utf8'),/'180s'/);
    const args=JSON.parse(await fs.readFile(path.join(dir,'args.json'),'utf8'));
    assert.deepEqual(args.slice(args.indexOf('--cmi'),args.indexOf('--cmi')+proofFlags.length),proofFlags);
    assert.equal(args[args.indexOf('--z3rlimit')+1],'100');
    for(const n of [0,-1,181,NaN,1.5])await assert.rejects(()=>check('invalid-'+String(n),{moduleSeconds:n}),/moduleSeconds/);
    for(const n of [0,-1,NaN,1.5])await assert.rejects(()=>check('invalid-driver-'+String(n),{seconds:n}),/aggregate seconds/);
    await assert.rejects(()=>check('project-override',{modelCache:dir,moduleSeconds:180}),/project module budget/);
    await assert.rejects(()=>check('project-driver-override',{modelCache:dir,seconds:999}),/project aggregate override/);
    await fs.writeFile(control,JSON.stringify({delay:1200,status:0}));
    const timed=await check('bounded',{moduleSeconds:1,seconds:10});assert.equal(timed.result.status,2,timed.result.log);
    assert.match(timed.result.log,/Error 124/);
    await assert.rejects(()=>fs.access(path.join(timed.work,'checked','Test.fst.checked')));
    const recovered=await check('bounded',{moduleSeconds:2,seconds:10});assert.equal(recovered.result.status,0,recovered.result.log);
    const chain=['A.fst','B.fst','Test.fst'];
    await fs.writeFile(control,JSON.stringify({delay:1100,status:0,chain,unused:true}));
    const serial=await check('serial',{moduleSeconds:2,modelCache:dir},chain);
    assert.equal(serial.result.status,0,serial.result.log);
    assert.equal(serial.result.budget.policy,'graph-derived');
    assert.equal(serial.result.budget.compilerTargets.length,3);
    assert.equal(serial.result.budget.seconds,22);
    for(const name of chain)await fs.access(path.join(serial.work,'checked',name+'.checked'));
    // The same serial chain cannot fit in one compiler's allowance. This
    // exercises the outer make timeout, separately from the per-process cap.
    const aggregate=await check('serial-too-short',{moduleSeconds:2,seconds:2,modelCache:dir},chain);
    assert.equal(aggregate.result.status,124,aggregate.result.log);
    await assert.rejects(()=>fs.access(path.join(aggregate.work,'checked','Test.fst.checked')));
    await fs.writeFile(control,JSON.stringify({delay:5000,status:0,ignoreTerm:true}));
    const killed=await check('kill-grace',{moduleSeconds:1,seconds:10});
    assert.equal(killed.result.status,2,killed.result.log);assert.match(killed.result.log,/Error 137|Killed/);
    const pid=Number(await fs.readFile(path.join(dir,'compiler.pid'),'utf8'));
    assert.throws(()=>process.kill(pid,0),error=>error.code==='ESRCH','compiler survived kill grace');
    await assert.rejects(()=>fs.access(path.join(killed.work,'checked','Test.fst.checked')));
    await fs.writeFile(control,JSON.stringify({delay:0,status:2}));
    const failed=await check('failure',{moduleSeconds:180,seconds:600});assert.equal(failed.result.status,2,failed.result.log);
    await assert.rejects(()=>fs.access(path.join(failed.work,'checked','Test.fst.checked')));
    report('PASS simulated compiler: graph-derived serial aggregate, default 60s/compiler, cold-only 180s, per-process timeout/retry, aggregate timeout, kill grace and compiler failure; solver flags unchanged');
  } catch(error) {report(output.join('\n'));throw error;}
  finally {console.log=report;await fs.rm(dir,{recursive:true,force:true});}
}
if(process.argv[1]===fileURLToPath(import.meta.url))await checkTimeoutBudgets();
