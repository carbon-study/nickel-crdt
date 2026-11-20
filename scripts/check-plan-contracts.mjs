// Separate constructor information from the planner's duplicate/error prefix.
import assert from 'node:assert/strict';
import {viewUnits} from './text-family-run.mjs';
export function planUnits(read) {
  const atomicFile='Nickel.EditAtomic.fst';
  const identityFile='Nickel.EditIdentity.fst';
  const atomic=read(atomicFile);
  const identity=read(identityFile);
  const needle='Tactics.prune "Nickel_crdt.Edit.impl_Replica__plan";';
  const pattern=' [SMTPat (Native.impl_Replica__plan before fact)]';
  assert.equal(atomic.split(pattern).length,3);
  function withholdShapeAtCaller() {
    const start=atomic.indexOf('let authored_edit_advances_once ');assert(start>=0);
    const next=/\nlet (?:rec )?\w+ /.exec(atomic.slice(start+4));
    const end=next?start+4+next.index:atomic.length;
    const body=atomic.slice(start,end);assert.equal(body.split(needle).length,2);
    return atomic.slice(0,start)+body.replace(needle,
      needle+'\n    Tactics.prune "Nickel.EditAtomic.plan_has_result_shape";')+atomic.slice(end);
  }
  function withoutPattern(name) {
    const start=atomic.indexOf('let '+name+' ');assert(start>=0);
    const at=atomic.indexOf(pattern,start);assert(at>start);
    assert(!atomic.slice(start,at).includes('\nlet '));
    return atomic.slice(0,at)+atomic.slice(at+pattern.length);
  }
  const cases=[
    ['plan-without-shape-pattern',atomicFile,withoutPattern('plan_has_result_shape'),atomicFile,'Nickel.EditAtomic.authored_edit_advances_once'],
    ['plan-without-shape-contract',atomicFile,withholdShapeAtCaller(),atomicFile,'Nickel.EditAtomic.authored_edit_advances_once'],
    ['plan-without-prefix-pattern',atomicFile,withoutPattern('plan_preserves_duplicate_result'),identityFile,'Nickel.EditIdentity.receive_known_identity'],
  ];
  for(const name of ['receive_known_identity','receive_invalid_counter','receive_added_has_fresh_event_id']) {
    const start=identity.indexOf('let '+name+' ');assert(start>=0);
    const next=/\nlet (?:rec )?\w+ /.exec(identity.slice(start+4));
    const end=next?start+4+next.index:identity.length;
    const body=identity.slice(start,end);assert.equal(body.split(needle).length,2);
    const view=identity.slice(0,start)+body.replace(needle,needle+'\n    Tactics.prune "Nickel.EditAtomic.plan_preserves_duplicate_result";')+identity.slice(end);
    cases.push(['plan-without-prefix-'+name,identityFile,view,identityFile,'Nickel.EditIdentity.'+name]);
  }
  // The owner is judged against its module as verified (the mutated file, or the unchanged identity module).
  return viewUnits('plan',cases.map(([name,file,view,root,theorem])=>({name,files:{[file]:view},roots:[root],theorem,inPlace:true,
    log:name+'.proof.log',pass:name+': actual caller requires the selected plan contract',failure:'require ordinary plan-contract dependency rejection'})),read);
}
