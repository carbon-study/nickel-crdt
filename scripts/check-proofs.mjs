import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import {readFileSync} from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import {run,verify} from './proof-cache.mjs';
import {hasOrdinaryTheoremRejection} from './negative-proof-evidence.mjs';
import {checkProofReform} from './proof-reform.mjs';
import {smokeUnits,smokePlans,retainedSmokeFile,wrongLoopSource,SMOKE_VIEWS,SMOKE_CARGO,SMOKE_HAX,SMOKE_SOURCE} from './smoke-units.mjs';
import {runViewUnits,familyPlanDigest} from './text-family-run.mjs';
import {auditUnits} from './edit-native-plans.mjs';
import {checkSmokeSelection} from './text-native-code.mjs';
import './check-proof-reform.mjs';
const root=fileURLToPath(new URL('..',import.meta.url));
await checkProofReform(root);
// The smoke units (#198) come from smoke-units.mjs; check-edit-proofs.mjs export-plans exports the same enumeration.
// Planned tuples are enumerated from the retained files; executed tuples record what each unit actually did, and the
// two must be equal field for field at the end of every run.
const hash=data=>createHash('sha256').update(data).digest('hex');
const retainedRead=file=>{const rel=retainedSmokeFile(file);assert(rel,'not a smoke workspace file: '+file);return readFileSync(path.join(root,rel),'utf8');};
const repoRead=file=>readFileSync(path.join(root,file),'utf8');
const planned=smokePlans(retainedRead,repoRead);
const out=process.argv[2];assert(out,'output directory required');
// Selection consumer (#198): `check-proofs.mjs <out> selection:<file>` runs smoke only if the text selection record
// selects it. The record must be bound to this tree (its inputs, every unit group's code closure and the smoke plan
// digest) before the no-work exit. Every module this runner loads is a static import, so its code closure (parsed and
// recorded) is exactly what it loads; there is no dynamic import to audit.
const selectionArg=process.argv.slice(3).find(a=>a.startsWith('selection:'));
assert(process.argv.length===3||(process.argv.length===4&&selectionArg),'usage: check-proofs.mjs <out> [selection:<file>]');
if(selectionArg){
  const decision=await checkSmokeSelection(root,selectionArg.slice('selection:'.length),familyPlanDigest(planned));
  console.log('smoke selection: '+decision.why);
  if(!decision.run){
    await fs.mkdir(out,{recursive:true});
    await fs.writeFile(path.join(out,'smoke-planned.json'),'[]\n');await fs.writeFile(path.join(out,'smoke-results.json'),'[]\n');
    console.log('selection runs nothing in this job\'s smoke gate: not affected (no build of these units ran; no result is claimed)');
    process.exit(0);
  }
}
const {NICKEL_HAX_BIN:hax,NICKEL_PROOF_FSTAR:fstar,NICKEL_HAX_SOURCE:models,NICKEL_FSTAR_MODEL_CACHE:modelCache}=process.env;
assert(hax&&fstar&&models&&modelCache,'run the locked .#proofs derivation');
const identity=JSON.parse(await fs.readFile(path.join(modelCache,'identity.json'),'utf8'));
assert.equal(identity.models,models);assert.equal(identity.fstar,fstar);
const views=new Map();
for(const name of SMOKE_VIEWS) {
  const source='proofs/'+name+'.lt',view='proofs/generated/Nickel.'+name+'.fst';
  const receipt=(await fs.readFile(path.join(root,'proofs/generated/'+name+'.sha256'),'utf8')).trim().split('\n');
  assert.deepEqual(receipt,[hash(await fs.readFile(path.join(root,source)))+'  '+source,hash(await fs.readFile(path.join(root,view)))+'  '+view]);
  const code=await fs.readFile(path.join(root,view),'utf8');
  assert(!/\b(?:admit|admit_smt_queries|assume|lax)\b/.test(code),'authored admissions are forbidden');
  views.set('Nickel.'+name+'.fst',code);
}
const original=await fs.readFile(path.join(root,SMOKE_SOURCE),'utf8');
const executed=new Map(),record=ran=>{assert(!executed.has(ran.id),'unit executed twice: '+ran.id);executed.set(ran.id,ran);};
let positive;
for(const mode of ['positive','wrong-loop-body']) {
  const work=path.join(process.cwd(),'.cache',mode);
  const crate=path.join(work,'crate'),proof=path.join(work,'proof');
  const ran={id:'smoke:'+mode,kind:'smoke-native',family:'smoke',owner:null,expect:null,roots:null,mutation:[],native:null};
  await fs.mkdir(crate,{recursive:true});await fs.mkdir(proof,{recursive:true});
  for(const name of ['Cargo.toml','Cargo.lock','src','proof-smoke'])await fs.cp(path.join(root,name),path.join(crate,name),{recursive:true});
  if(mode!=='positive') {
    await fs.writeFile(path.join(crate,SMOKE_SOURCE),wrongLoopSource(original));
    ran.mutation=[{file:SMOKE_SOURCE,sha256:hash(await fs.readFile(path.join(crate,SMOKE_SOURCE)))}];
  }
  const env={...process.env,CARGO_TARGET_DIR:path.join(work,'target')};
  const native=run('native '+mode,'cargo',SMOKE_CARGO,crate,{env});ran.native={cargoArgs:[...SMOKE_CARGO],baselines:[],extraction:false};
  if(mode==='positive')assert.equal(native.status,0,native.log);
  else {assert.equal(native.status,101,native.log);assert.match(native.log,/test result: FAILED/);}
  const extracted=run('hax '+mode,hax,SMOKE_HAX,crate,{env});ran.native.extraction=true;
  assert.equal(extracted.status,0,extracted.log);
  const nativeCode=await fs.readFile(path.join(crate,'proof-smoke/proofs/fstar/extraction/Nickel_proof_smoke.fst'),'utf8');
  assert.match(nativeCode,/let flip /);assert(!/\b(?:admit|assume)\b/.test(nativeCode));
  if(mode==='positive') {
    const committed=await fs.readFile(path.join(root,'proofs/generated/hax/Nickel_proof_smoke.fst'),'utf8');
    assert(nativeCode===committed,'fresh hax smoke extraction differs from proofs/generated/hax/Nickel_proof_smoke.fst; review and refresh the committed translation');
    positive=nativeCode;
  } else assert.notEqual(nativeCode,positive);
  for(const [name,code] of views)await fs.writeFile(path.join(proof,name),code);
  await fs.writeFile(path.join(proof,'Nickel_proof_smoke.fst'),nativeCode);
  ran.roots=['Nickel.Smoke.fst'];
  const result=await verify({dir:proof,roots:[path.join(proof,'Nickel.Smoke.fst')],fstar,models,modelCache});
  if(mode==='positive'){assert.equal(result.status,0,result.log);ran.expect='verify';}
  else {
    assert.equal(result.status,2,'require ordinary proof rejection, not timeout/signal');
    assert(hasOrdinaryTheoremRejection({status:result.status,log:result.log,theorem:'Nickel.Smoke.flip_bridge',view:views.get('Nickel.Smoke.fst')}),
      'require a final ordinary bridge-query failure with a semantic error in that declaration: '+result.log);
    assert(result.modules.includes('Nickel_proof_smoke.fst'));
    assert(result.modules.includes('Nickel.Smoke.fst'));
    ran.expect='reject';ran.owner='Nickel.Smoke.flip_bridge';
  }
  record(ran);
  await fs.mkdir(out,{recursive:true});
  await fs.writeFile(path.join(out,mode+'.log'),result.log);
  // This workspace's own controls, enumerated from the workspace itself (its extraction is this mode's).
  const actual=smokeUnits(file=>readFileSync(path.join(proof,file),'utf8'),repoRead)[mode];
  const ctx={proof,output:out,fstar,models,modelCache};
  if(mode==='positive') {
    await fs.copyFile(path.join(proof,'Nickel_proof_smoke.fst'),path.join(out,'Nickel_proof_smoke.fst'));
    await runViewUnits(actual.loop,ctx,record);
  }
  await runViewUnits(actual.parity,ctx,record);
  console.log(mode==='positive'?'PASS actual Rust loop, LoopUtil bridge, parity and involution':'PASS wrong native loop fails the unchanged bridge theorem');
}
await fs.writeFile(path.join(out,'smoke-planned.json'),JSON.stringify(planned,null,1)+'\n');
await fs.writeFile(path.join(out,'smoke-results.json'),JSON.stringify([...executed.values()],null,1)+'\n');
auditUnits(planned,executed);
console.log('PASS smoke exact-tuple audit: '+planned.length+' planned units executed exactly as planned (two native chains, '+planned.filter(p=>p.kind==='family-control'&&p.expect==='reject').length+' rejections, '+planned.filter(p=>p.kind==='family-control'&&p.expect==='verify').length+' healthy direct parity)');
