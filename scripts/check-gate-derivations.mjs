// Evaluate actual Nix derivation identities on both declared architectures.
// Temporary copies contain tracked working bytes only; no project files mutate.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import {spawnSync} from 'node:child_process';
import {fileURLToPath} from 'node:url';
const root=fileURLToPath(new URL('..',import.meta.url));
const out=process.argv[2]; assert(out,'usage: node scripts/check-gate-derivations.mjs <new-output-directory>');
await fs.mkdir(out); // refuse overwriting retained evidence
function run(bin,args,cwd=root) {
  const r=spawnSync(bin,args,{cwd,encoding:'utf8',maxBuffer:16*1024*1024,env:{...process.env,NIX_REMOTE:'daemon'}});
  assert.equal(r.status,0,bin+' '+args.join(' ')+'\n'+r.stderr);return r.stdout;
}
const apply='ps: builtins.mapAttrs (_: p: builtins.mapAttrs (_: v: v.drvPath) (builtins.removeAttrs p ["default" "hax" "hax-fstar"])) ps';
function evaluate(dir){return JSON.parse(run('nix',['eval','--json','--no-write-lock-file',`path:${dir}#packages`,'--apply',apply]));}
const temp=await fs.mkdtemp(path.join(os.tmpdir(),'nickel-inputs-'));
const text=['proofs','proofs-core-a','proofs-core-b','proofs-shard-0','proofs-shard-1','proofs-shard-2'];
const cases=[
  ['setup helper','scripts/latte-hax-lane.mjs',['gate-inputs']],
  ['unrelated comparison tool','scripts/compare-edit-storage.mjs',['gate-inputs']],
  ['packaging guard','scripts/check-gate-inputs.mjs',['gate-inputs']],
  ['text contract','scripts/check-accepted-contracts.mjs',[...text,'gate-inputs']],
  ['causal checker','scripts/check-causal-envelope.mjs',['shared-proofs','gate-inputs']],
  ['shared native checker','scripts/check-shared-native.mjs',['shared-native','gate-inputs']],
  ['shared mutation scope','scripts/mutation-scope.mjs',[...text,'shared-native','shared-proofs','gate-inputs']],
  ['shared proof runtime','scripts/proof-cache.mjs',[...text,'proof-models','shared-native','shared-proofs','gate-inputs']],
  ['model builder','scripts/build-proof-models.mjs',[...text,'proof-models','shared-proofs','gate-inputs']],
  ['model budget checker','scripts/check-proof-timeouts.mjs',[...text,'proof-models','shared-proofs','gate-inputs']],
  ['text authored proof','proofs/EditPast.lt',[...text,'gate-inputs']],
  ['text Rust implementation','src/edit.rs',[...text,'native','edit-reference','shared-native','gate-inputs']],
];
const results=[];
try {
  const files=run('git',['ls-files','-z']).split('\0').filter(Boolean);
  for(const file of files){const to=path.join(temp,file);await fs.mkdir(path.dirname(to),{recursive:true});await fs.copyFile(path.join(root,file),to);}
  const base=evaluate(temp);await fs.writeFile(path.join(out,'baseline.json'),JSON.stringify(base,null,2)+'\n');
  assert.deepEqual(Object.keys(base).sort(),['aarch64-linux','x86_64-linux']);
  for(const [name,file,wanted] of cases){
    const target=path.join(temp,file), original=await fs.readFile(target,'utf8');
    await fs.writeFile(target,original+'\n// gate input dependency probe\n');
    let actual;try{actual=evaluate(temp);}finally{await fs.writeFile(target,original);}
    const changed={};
    for(const system of Object.keys(base)){
      assert.deepEqual(Object.keys(actual[system]).sort(),Object.keys(base[system]).sort());
      changed[system]=Object.keys(base[system]).filter(k=>base[system][k]!==actual[system][k]).sort();
      assert.deepEqual(changed[system],[...wanted].sort(),name+' consumers on '+system);
    }
    results.push({name,file,changed,derivations:actual});console.log('PASS '+name+': '+changed['x86_64-linux'].join(', '));
    await fs.writeFile(path.join(out,'results.json'),JSON.stringify(results,null,2)+'\n');
  }
}finally{await fs.rm(temp,{recursive:true,force:true});}
