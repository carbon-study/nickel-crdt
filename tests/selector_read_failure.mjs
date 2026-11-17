// Regression for missing dependency edges after an enumerated proof blob cannot be read.
// No prover is run. Supply source-matched base/head exports from the declared gate environment.
// node tests/selector_read_failure.mjs <repo> <base> <head> <base-plans> <head-plans> [selector]
import assert from 'node:assert/strict';
import {execFileSync,spawnSync} from 'node:child_process';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
const [repo,baseArg,headArg,basePlans,headPlans,override]=process.argv.slice(2);
assert(repo&&baseArg&&headArg&&basePlans&&headPlans,'supply repo, two refs and their own exports');
const git=execFileSync('which',['git'],{encoding:'utf8'}).trim();
const rev=r=>execFileSync(git,['-C',repo,'rev-parse',r+'^{commit}'],{encoding:'utf8'}).trim();
const base=rev(baseArg),head=rev(headArg);
assert.notEqual(base,head,'use distinct base/head commits so each side is tested separately');
const selector=override??path.join(repo,'scripts/select-affected.mjs');
const tmp=fs.mkdtempSync(path.join(os.tmpdir(),'nickel-selector-read-'));
const file='proofs/generated/Nickel.EditPast.fst';
try {
 fs.writeFileSync(path.join(tmp,'git'),`#!${process.execPath}\nimport {spawnSync} from 'node:child_process';\nimport fs from 'node:fs';\nconst a=process.argv.slice(2);\nif(a[2]==='show'&&a[3]===process.env.FAIL_BLOB){fs.appendFileSync(process.env.FAIL_LOG,a[3]+'\\n');process.stderr.write('injected proof blob read failure\\n');process.exit(73);}\nconst r=spawnSync(${JSON.stringify(git)},a,{stdio:'inherit'});process.exit(r.status??1);\n`,{mode:0o755});
 const run=blob=>{
  const log=path.join(tmp,'fault.log');fs.writeFileSync(log,'');
  const r=spawnSync(process.execPath,[selector,base,head,'--repo',repo,'--base-plans',basePlans,'--head-plans',headPlans],{
   encoding:'utf8',env:{...process.env,PATH:tmp+path.delimiter+process.env.PATH,FAIL_BLOB:blob,FAIL_LOG:log}});
  assert.equal(r.status,0,r.stderr);
  return {record:JSON.parse(r.stdout),hits:fs.readFileSync(log,'utf8').trim().split('\n').filter(Boolean)};
 };
 const healthy=run('');
 assert.equal(healthy.record.full,false,'healthy fixture must not already force full');
 assert.equal(healthy.record.register.run,'none','healthy fixture must have no register proof change');
 console.log('PASS healthy source-matched fixture: register none');
 for(const [side,ref] of [['base',base],['head',head]]){
  const blob=ref+':'+file;
  const {record,hits}=run(blob);
  assert.deepEqual(hits,[blob],'fault must hit exactly the intended graph read');
  assert.equal(record.full,true,side+' unreadable enumerated proof must force full');
  assert.equal(record.register.run,'full');assert.equal(record.text.run,'full');
  assert(record.reasons.some(r=>r.full==='unreadable enumerated proof file'&&r.why===blob),'retain exact failed ref/path');
  console.log('PASS '+side+' graph read failure: all gates full, exact ref/path retained');
 }
} finally {fs.rmSync(tmp,{recursive:true,force:true});}
