// Run only the generated oracle, with no directed/run-family witnesses loaded.
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
const here=path.dirname(fileURLToPath(import.meta.url));
const source=fs.readFileSync(path.join(here,'fugue.mjs'),'utf8');
const oracle=fs.readFileSync(path.join(here,'fugue-max-oracle.mjs'),'utf8');
const controls={
  reverseRightRank:{file:'fugue.mjs',from:'rank.get(op.rightOrigin)>rank.get(old.rightOrigin)',to:'rank.get(op.rightOrigin)<rank.get(old.rightOrigin)'},
  reverseRightTie:{file:'fugue.mjs',from:'op.rightOrigin===old.rightOrigin&&compareId(op.id,id)<0',to:'op.rightOrigin===old.rightOrigin&&compareId(op.id,id)>0'},
  plain:{file:'fugue.mjs',from:"op.side==='right'&&!this.options.plain",to:'false'},
  reverseLeftTie:{file:'fugue.mjs',from:'else at=siblings.findIndex(id=>compareId(op.id,id)<0)',to:'else at=siblings.findIndex(id=>compareId(op.id,id)>0)'},
  oracleNoForward:{file:'fugue-max-oracle.mjs',from:'if(pos.get(B.id)!==pos.get(A)+1)return false;',to:'if(false)return false;'},
  oracleNoBackward:{file:'fugue-max-oracle.mjs',from:'if(!exception&&pos.get(B)!==pos.get(A.id)+1)return false;',to:'// control: backward clause removed'},
  oracleNoTie:{file:'fugue-max-oracle.mjs',from:'if(pos.get(A.id)>=pos.get(B.id))return false;',to:'if(false)return false;'},
};
const receipt={};
for(const [name,control]of Object.entries(controls)) {
  const dir=fs.mkdtempSync(path.join(os.tmpdir(),'nickel-max-control-'));
  try {
    fs.copyFileSync(path.join(here,'order.mjs'),path.join(dir,'order.mjs'));
    for(const [file,original]of [['fugue.mjs',source],['fugue-max-oracle.mjs',oracle]]) {
      const changed=file===control.file?original.replace(control.from,control.to):original;
      if(file===control.file)assert.notEqual(changed,original,'mutation target must exist');
      fs.writeFileSync(path.join(dir,file),changed);
    }
    const run=spawnSync(process.execPath,[path.join(dir,'fugue-max-oracle.mjs')],{encoding:'utf8',timeout:10000});
    assert(!run.error&&!run.signal,'timeout/spawn failure is not rejection evidence');
    assert.equal(run.status,1,'mutant must fail an assertion');
    const expected=control.file==='fugue.mjs'?'generated Definition 4 order':'finite specification must determine one order';
    assert(run.stderr.includes(`AssertionError [ERR_ASSERTION]: ${expected}`),'intended oracle assertion must reject');
    receipt[name]=expected;
  } finally {fs.rmSync(dir,{recursive:true,force:true});}
}
console.log(JSON.stringify(receipt,null,2));
