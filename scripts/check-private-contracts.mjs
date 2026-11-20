// Tree publication -> plan -> receive: private-state contracts must carry callers.
import assert from 'node:assert/strict';
import {viewUnits} from './text-family-run.mjs';
export function privateUnits(read) {
  const file='Nickel.EditCommit.fst',original=read(file);
  const treePattern=' [SMTPat (Native.impl_Replica__with_tree state tree)]';
  const planPattern=' [SMTPat (Native.impl_Replica__plan before fact)]';
  const treePrune='Tactics.prune "Nickel_crdt.Edit.impl_Replica__with_tree";';
  const planPrune='Tactics.prune "Nickel_crdt.Edit.impl_Replica__plan";';
  for(const needle of [treePattern,planPattern])assert.equal(original.split(needle).length,2);
  function withholdAt(name,needle,law) {
    const start=original.indexOf('let '+name+' ');assert(start>=0);
    const next=/\nlet (?:rec )?\w+ /.exec(original.slice(start+4));
    const end=next?start+4+next.index:original.length,body=original.slice(start,end);
    assert.equal(body.split(needle).length,2);
    return original.slice(0,start)+body.replace(needle,needle+'\n    Tactics.prune "'+law+'";')+original.slice(end);
  }
  const units=[];
  for(const [name,view,theorem]of[
    ['private-without-tree-pattern',original.replace(treePattern,''),'plan_preserves_private_state'],
    ['private-without-tree-contract',withholdAt('plan_preserves_private_state',treePrune,'Nickel.EditCommit.tree_publication_keeps_private'),'plan_preserves_private_state'],
    ['private-without-plan-pattern',original.replace(planPattern,''),'receive_preserves_private_state'],
    ['private-without-plan-contract',withholdAt('receive_preserves_private_state',planPrune,'Nickel.EditCommit.plan_preserves_private_state'),'receive_preserves_private_state'],
  ]) units.push({name,files:{[file]:view},roots:[file],theorem:'Nickel.EditCommit.'+theorem,inPlace:true,
    log:name+'.proof.log',pass:name+': actual private-state caller requires its contract',failure:'require ordinary private-state contract dependency rejection'});
  return viewUnits('private',units,read);
}
