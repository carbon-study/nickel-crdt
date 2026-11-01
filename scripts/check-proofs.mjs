import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import {run,verify} from './proof-cache.mjs';
const root=fileURLToPath(new URL('..',import.meta.url));
const {NICKEL_HAX_BIN:hax,NICKEL_PROOF_FSTAR:fstar,NICKEL_HAX_SOURCE:models,NICKEL_FSTAR_MODEL_CACHE:modelCache}=process.env;
assert(hax&&fstar&&models&&modelCache,'run the locked .#proofs derivation');
const out=process.argv[2];assert(out,'output directory required');
const identity=JSON.parse(await fs.readFile(path.join(modelCache,'identity.json'),'utf8'));
assert.equal(identity.models,models);assert.equal(identity.fstar,fstar);
const hash=data=>createHash('sha256').update(data).digest('hex');
const views=new Map();
for(const name of ['Prelude','LoopUtil','Smoke']) {
  const source='proofs/'+name+'.lt',view='proofs/generated/Nickel.'+name+'.fst';
  const receipt=(await fs.readFile(path.join(root,'proofs/generated/'+name+'.sha256'),'utf8')).trim().split('\n');
  assert.deepEqual(receipt,[hash(await fs.readFile(path.join(root,source)))+'  '+source,hash(await fs.readFile(path.join(root,view)))+'  '+view]);
  const code=await fs.readFile(path.join(root,view),'utf8');
  assert(!/\b(?:admit|admit_smt_queries|assume|lax)\b/.test(code),'authored admissions are forbidden');
  views.set('Nickel.'+name+'.fst',code);
}
const original=await fs.readFile(path.join(root,'proof-smoke/src/lib.rs'),'utf8');
let positive;
for(const mode of ['positive','wrong-loop-body']) {
  const work=path.join(process.cwd(),'.cache',mode);
  const crate=path.join(work,'crate'),proof=path.join(work,'proof');
  await fs.mkdir(crate,{recursive:true});await fs.mkdir(proof,{recursive:true});
  for(const name of ['Cargo.toml','Cargo.lock','src','proof-smoke'])await fs.cp(path.join(root,name),path.join(crate,name),{recursive:true});
  if(mode!=='positive') {
    assert.equal(original.split('value = !value;').length,2);
    await fs.writeFile(path.join(crate,'proof-smoke/src/lib.rs'),original.replace('value = !value;','value = value;'));
  }
  const env={...process.env,CARGO_TARGET_DIR:path.join(work,'target')};
  const native=run('native '+mode,'cargo',['test','--workspace','--offline','--locked'],crate,{env});
  if(mode==='positive')assert.equal(native.status,0,native.log);
  else {assert.equal(native.status,101,native.log);assert.match(native.log,/test result: FAILED/);}
  const extracted=run('hax '+mode,hax,['-C','--offline','--locked','-p','nickel-proof-smoke',';','into','-i','-** +!nickel_proof_smoke::flip','fstar'],crate,{env});
  assert.equal(extracted.status,0,extracted.log);
  const nativeCode=await fs.readFile(path.join(crate,'proof-smoke/proofs/fstar/extraction/Nickel_proof_smoke.fst'),'utf8');
  assert.match(nativeCode,/let flip /);assert(!/\b(?:admit|assume)\b/.test(nativeCode));
  if(mode==='positive')positive=nativeCode;else assert.notEqual(nativeCode,positive);
  for(const [name,code] of views)await fs.writeFile(path.join(proof,name),code);
  await fs.writeFile(path.join(proof,'Nickel_proof_smoke.fst'),nativeCode);
  const result=await verify({dir:proof,roots:[path.join(proof,'Nickel.Smoke.fst')],fstar,models,modelCache});
  if(mode==='positive')assert.equal(result.status,0,result.log);
  else {
    assert.equal(result.status,2,'require ordinary proof rejection, not timeout/signal');
    assert.match(result.log,/Query-stats \(Nickel\.Smoke\.flip_bridge,[^\n]*failed/);
    assert.match(result.log,/Could not prove post-condition|Assertion failed/);
    assert(result.modules.includes('Nickel_proof_smoke.fst'));
    assert(result.modules.includes('Nickel.Smoke.fst'));
  }
  await fs.mkdir(out,{recursive:true});
  await fs.writeFile(path.join(out,mode+'.log'),result.log);
  if(mode==='positive')await fs.copyFile(path.join(proof,'Nickel_proof_smoke.fst'),path.join(out,'Nickel_proof_smoke.fst'));
  console.log(mode==='positive'?'PASS actual Rust loop, LoopUtil bridge, parity and involution':'PASS wrong native loop fails the unchanged bridge theorem');
}
