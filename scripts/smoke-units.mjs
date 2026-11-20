// The smoke gate's units (#198), from one enumeration that check-proofs.mjs executes and check-edit-proofs.mjs
// export-plans exports. read(file) serves the smoke positive workspace (its authored views and the retained
// Nickel_proof_smoke.fst extraction, which the positive chain asserts equal to a fresh one); repo(file) reads the checkout.
// Execution order: the healthy native chain, its 18 loop-contract controls and the healthy direct parity check (expect
// "verify"), then the wrong-loop native chain and the direct parity check on its extraction (expect "reject").
import {digest} from './proof-cache.mjs';
import {loopUnits,directParityUnits} from './check-loop-contracts.mjs';
export const SMOKE_VIEWS=['Prelude','LoopUtil','Smoke'];
export const SMOKE_EXTRACTION='Nickel_proof_smoke.fst';
export const SMOKE_CARGO=['test','--workspace','--offline','--locked'];
export const SMOKE_HAX=['-C','--offline','--locked','-p','nickel-proof-smoke',';','into','-i','-** +!nickel_proof_smoke::flip','fstar'];
export const SMOKE_SOURCE='proof-smoke/src/lib.rs',SMOKE_NEEDLE='value = !value;',SMOKE_FAULT='value = value;';
/** The retained file a smoke workspace file is installed from, or null. */
export function retainedSmokeFile(file){
  if(file===SMOKE_EXTRACTION)return 'proofs/generated/hax/'+file;
  const m=/^Nickel\.(\w+)\.fst$/.exec(file);
  return m&&SMOKE_VIEWS.includes(m[1])?'proofs/generated/'+file:null;
}
export const wrongLoopSource=source=>{
  if(source.split(SMOKE_NEEDLE).length!==2)throw Error('smoke wrong-loop anchor must occur exactly once');
  return source.replace(SMOKE_NEEDLE,SMOKE_FAULT);
};
const nativeUnit=(mode,repo)=>{
  const positive=mode==='positive';
  return {plan:{id:'smoke:'+mode,kind:'smoke-native',family:'smoke',owner:positive?null:'Nickel.Smoke.flip_bridge',expect:positive?'verify':'reject',
    roots:['Nickel.Smoke.fst'],mutation:positive?[]:[{file:SMOKE_SOURCE,sha256:digest(wrongLoopSource(repo(SMOKE_SOURCE)))}],
    native:{cargoArgs:[...SMOKE_CARGO],baselines:[],extraction:true}},mode};
};
/** Every smoke unit, in execution order, grouped by the workspace that runs it. */
export function smokeUnits(read,repo){
  return {positive:{native:nativeUnit('positive',repo),loop:loopUnits(read),parity:directParityUnits(read,'positive')},
    'wrong-loop-body':{native:nativeUnit('wrong-loop-body',repo),parity:directParityUnits(read,'wrong-loop-body')}};
}
export const smokePlans=(read,repo)=>{const u=smokeUnits(read,repo);
  return [u.positive.native,...u.positive.loop,...u.positive.parity,u['wrong-loop-body'].native,...u['wrong-loop-body'].parity].map(x=>x.plan);};
/** Smoke as a unit group for the family export: its workspace is served from the retained files through repo (so the
 *  export's recorded sources name them); the text positive workspace reader is not used. */
export function smokeGroupUnits(_read,repo){
  const read=file=>{const rel=retainedSmokeFile(file);if(!rel)throw Error('not a smoke workspace file: '+file);return repo(rel);};
  const u=smokeUnits(read,repo);
  return [u.positive.native,...u.positive.loop,...u.positive.parity,u['wrong-loop-body'].native,...u['wrong-loop-body'].parity];
}
