// Actual edit/admit extraction and universal error/empty neutrality lemmas.
// This gate does not prove valid-fact acceptance, convergence or FugueMax.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {digest,run,verify,put} from './proof-cache.mjs';
const root=fileURLToPath(new URL('..',import.meta.url));
const {NICKEL_HAX_BIN:hax,NICKEL_PROOF_FSTAR:fstar,NICKEL_HAX_SOURCE:models,NICKEL_FSTAR_MODEL_CACHE:modelCache}=process.env;
assert(hax&&fstar&&models&&modelCache,'use the locked .#proofs environment');
const output=process.argv[2];assert(output,'output directory required');
await fs.mkdir(output,{recursive:true});
const identity=JSON.parse(await fs.readFile(path.join(modelCache,'identity.json'),'utf8'));
assert.equal(identity.models,models);assert.equal(identity.fstar,fstar);
const views=new Map();
for(const name of ['Prelude','EditAtomic']) {
  const source=`proofs/${name}.lt`,view=`proofs/generated/Nickel.${name}.fst`;
  const code=await fs.readFile(path.join(root,view),'utf8');
  const receipt=(await fs.readFile(path.join(root,`proofs/generated/${name}.sha256`),'utf8')).trim().split('\n');
  assert.deepEqual(receipt,[digest(await fs.readFile(path.join(root,source)))+'  '+source,digest(code)+'  '+view]);
  assert(!/\b(?:admit|admit_smt_queries|assume|lax)\b/.test(code),'no authored admissions');
  views.set(`Nickel.${name}.fst`,code);
}
const original=await fs.readFile(path.join(root,'src/edit.rs'),'utf8');
let positive;
for(const mode of ['positive','receive-error-corrupts-counter','edit-error-corrupts-counter','edit-success-reuses-counter']) {
  const work=path.join(root,'.cache','edit-proofs',mode),crate=path.join(work,'crate'),proof=path.join(work,'proof');
  await fs.mkdir(crate,{recursive:true});await fs.mkdir(proof,{recursive:true});
  for(const name of ['Cargo.toml','Cargo.lock','src','tests','proof-smoke'])await fs.cp(path.join(root,name),path.join(crate,name),{recursive:true});
  if(mode!=='positive') {
    const start=original.indexOf(mode.startsWith('receive')?'pub fn receive(':'pub fn edit(');assert(start>=0);
    const success=mode==='edit-success-reuses-counter';
    const needle=success?'next.next_counter = self.next_counter + 1;':'Err(error) => (self, Err(error)),';
    const at=original.indexOf(needle,start);assert(at>=start);
    const mutant=original.slice(0,at)+original.slice(at).replace(needle,success?'next.next_counter = self.next_counter;':'Err(error) => { let mut damaged = self; damaged.next_counter = 0; (damaged, Err(error)) },');
    await fs.writeFile(path.join(crate,'src/edit.rs'),mutant);
  }
  const env={...process.env,CARGO_TARGET_DIR:path.join(root,'target','edit-proof-check')};
  const native=run('edit native '+mode,'cargo',['test','--offline','--locked','-p','nickel-crdt','--test','edit_admit'],crate,{env});
  await fs.writeFile(path.join(output,mode+'.native.log'),native.log);
  if(mode==='positive')assert.equal(native.status,0,native.log);
  else {assert.equal(native.status,101,native.log);assert.match(native.log,/test result: FAILED/);}
  const extracted=run('edit hax '+mode,hax,['-C','--offline','--locked','-p','nickel-crdt',';','into','--output-dir',proof,'-i','-** +nickel_crdt::edit::**::receive +nickel_crdt::edit::**::edit','fstar'],crate,{env});
  await fs.writeFile(path.join(output,mode+'.hax.log'),extracted.log);
  assert.equal(extracted.status,0,extracted.log);
  const code=await fs.readFile(path.join(proof,'Nickel_crdt.Edit.fst'),'utf8');
  assert.match(code,/let impl_Replica__receive /);assert.match(code,/let impl_Replica__edit/);
  assert(!/\b(?:admit|assume|admit_smt_queries)\b/.test(code),'no assumptions in extracted project code');
  if(mode==='positive')positive=code;else assert.notEqual(code,positive);
  for(const [name,code] of views)await put(path.join(proof,name),code);
  const checked=await verify({dir:proof,roots:[path.join(proof,'Nickel.EditAtomic.fst')],fstar,models,modelCache});
  await fs.writeFile(path.join(output,mode+'.proof.log'),checked.log);
  if(mode==='positive') {
    assert.equal(checked.status,0,checked.log);
    await fs.copyFile(path.join(proof,'Nickel_crdt.Edit.fst'),path.join(output,'Nickel_crdt.Edit.fst'));
  } else {
    assert.equal(checked.status,2,'require ordinary proof rejection, not extraction failure/timeout');
    const theorem=mode.startsWith('receive')?'receive_rejection_unchanged':mode==='edit-success-reuses-counter'?'authored_edit_advances_once':'edit_rejection_or_empty_unchanged';
    assert.match(checked.log,new RegExp(`Query-stats \\(Nickel\\.EditAtomic\\.${theorem},[^\\n]*failed`));
    assert.match(checked.log,/Could not prove post-condition|Assertion failed/);
  }
  console.log(`PASS ${mode}: native and unchanged actual-Rust neutrality theorem ${mode==='positive'?'verified':'reject the corrupted return'}`);
}
