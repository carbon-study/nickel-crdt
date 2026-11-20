// The text gate's contract families (#197, #199). Each family is loaded by its own literal dynamic import, only when
// that family is enumerated or run, so a run that executes some families never loads the others' modules (selected
// runs audit that at runtime). check-edit-proofs.mjs loads this index only for families, cache-safety or gatepreflight.
// A converted family exports units(read, repo): its complete control inventory from the shared enumeration that both
// export-plans and execution consume. remaining, spec and accepted (core-a, #198) are not converted: they keep their
// opaque check functions, export no plans, and are never selected (they run whenever their job runs).
import {readFileSync} from 'node:fs';
import {join} from 'node:path';
import {runViewUnits} from './text-family-run.mjs';
// Execution order.
export const FAMILY_ORDER=['delete','event','operation','replay','basis','schedule','past','remaining','counter','push','vector','scalar','identity','writer','plan','containment','accepted','spec','private','shared','commit'];
export const UNCONVERTED=['remaining','accepted','spec'];
// Each family's module (its code input is that module's import closure) and its loader.
export const FAMILY_MODULES={delete:'check-delete-contracts.mjs',event:'check-event-contracts.mjs',operation:'check-operation-contracts.mjs',replay:'check-replay-contracts.mjs',basis:'check-basis-contracts.mjs',schedule:'check-schedule-contracts.mjs',past:'check-past-contracts.mjs',remaining:'check-remaining-contracts.mjs',counter:'check-counter-contracts.mjs',push:'check-push-contracts.mjs',vector:'check-vector-contracts.mjs',scalar:'check-loop-contracts.mjs',identity:'check-identity-contracts.mjs',writer:'check-writer-contracts.mjs',plan:'check-plan-contracts.mjs',containment:'check-containment-contracts.mjs',accepted:'check-accepted-contracts.mjs',spec:'check-spec-contracts.mjs',private:'check-private-contracts.mjs',shared:'check-shared-contracts.mjs',commit:'check-commit-contracts.mjs'};
const load={
  delete:async()=>{const m=await import('./check-delete-contracts.mjs');return {units:m.deleteUnits,run:m.runDeleteUnits};},
  event:async()=>({units:(await import('./check-event-contracts.mjs')).eventUnits}),
  operation:async()=>({units:(await import('./check-operation-contracts.mjs')).operationUnits}),
  replay:async()=>({units:(await import('./check-replay-contracts.mjs')).replayUnits}),
  basis:async()=>({units:(await import('./check-basis-contracts.mjs')).basisUnits}),
  schedule:async()=>({units:(await import('./check-schedule-contracts.mjs')).scheduleUnits}),
  past:async()=>({units:(await import('./check-past-contracts.mjs')).pastUnits}),
  remaining:async()=>({check:(await import('./check-remaining-contracts.mjs')).checkRemainingContracts}),
  counter:async()=>({units:(await import('./check-counter-contracts.mjs')).counterUnits}),
  push:async()=>({units:(await import('./check-push-contracts.mjs')).pushUnits}),
  vector:async()=>({units:(await import('./check-vector-contracts.mjs')).vectorUnits}),
  scalar:async()=>({units:(await import('./check-loop-contracts.mjs')).scalarUnits}),
  identity:async()=>({units:(await import('./check-identity-contracts.mjs')).identityUnits}),
  writer:async()=>({units:(await import('./check-writer-contracts.mjs')).writerUnits}),
  plan:async()=>({units:(await import('./check-plan-contracts.mjs')).planUnits}),
  containment:async()=>({units:(await import('./check-containment-contracts.mjs')).containmentUnits}),
  accepted:async()=>({check:(await import('./check-accepted-contracts.mjs')).checkAcceptedContracts}),
  spec:async()=>({check:(await import('./check-spec-contracts.mjs')).checkSpecContracts}),
  private:async()=>({units:(await import('./check-private-contracts.mjs')).privateUnits}),
  shared:async()=>({units:(await import('./check-shared-contracts.mjs')).sharedUnits}),
  commit:async()=>({units:(await import('./check-commit-contracts.mjs')).commitUnits}),
};
export async function loadFamily(name){
  if(!Object.hasOwn(load,name))throw Error('unknown contract family '+name);
  const f=await load[name]();
  if(UNCONVERTED.includes(name)!==Boolean(f.check))throw Error('family '+name+' conversion state disagrees with UNCONVERTED');
  return f;
}
/** A converted family's units. read(file) reads the positive workspace; repo(file) reads the checkout. */
export async function familyUnits(name,read,repo){
  const f=await loadFamily(name);if(!f.units)throw Error('family '+name+' is not converted');
  return f.units(read,repo);
}
/** Runs one family. A converted family executes exactly the given units (default: its complete inventory read from
 *  ctx.proof) and reports each executed tuple to record; an unconverted family runs its own check. */
export async function runFamily(name,ctx,{units,record=()=>{},repo}={}){
  const f=await loadFamily(name);
  if(f.check)return f.check(ctx);
  const list=units??await f.units(file=>readFileSync(join(ctx.proof,file),'utf8'),repo??(file=>{throw Error('no checkout reader for '+file);}));
  return (f.run??runViewUnits)(list,ctx,record);
}
export async function checkRemainingCallLocator(){return (await import('./check-remaining-contracts.mjs')).checkRemainingCallLocator();}
export async function checkCacheSafety(ctx){return (await import('./check-cache-safety.mjs')).checkCacheSafety(ctx);}
