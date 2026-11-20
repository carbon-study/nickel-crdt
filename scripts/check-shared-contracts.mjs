// The same-history admission law must compose checked relational callees.
import assert from 'node:assert/strict';
import {viewUnits} from './text-family-run.mjs';
export function sharedUnits(read) {
  const file='Nickel.EditCommit.fst',original=read(file);
  const treePattern=' [SMTPat (Native.impl_Replica__with_tree left tree); SMTPat (Native.impl_Replica__with_tree right tree)]';
  const planPattern=' [SMTPat (Native.impl_Replica__plan before fact); SMTPat (Native.impl_Replica__plan remote fact)]';
  for(const p of [treePattern,planPattern])assert.equal(original.split(p).length,2);
  function withholdAt(name,needle,law) {
    const start=original.indexOf('let '+name+' ');assert(start>=0);
    const next=/\nlet (?:rec )?\w+ /.exec(original.slice(start+4));
    const end=next?start+4+next.index:original.length,body=original.slice(start,end);
    assert.equal(body.split(needle).length,2);
    return original.slice(0,start)+body.replace(needle,needle+'\n    Tactics.prune "'+law+'";')+original.slice(end);
  }
  const units=[];
  for(const [name,view,theorem]of[
    ['shared-without-tree-pattern',original.replace(treePattern,''),'plan_ignores_private_state'],
    ['shared-without-tree-contract',withholdAt('plan_ignores_private_state','Tactics.prune "Nickel_crdt.Edit.impl_Replica__with_tree";','Nickel.EditCommit.tree_publication_respects_shared'),'plan_ignores_private_state'],
    ['shared-without-plan-pattern',original.replace(planPattern,''),'admission_ignores_private_state'],
    ['shared-without-plan-contract',withholdAt('admission_ignores_private_state','Tactics.prune "Nickel_crdt.Edit.impl_Replica__plan";','Nickel.EditCommit.plan_ignores_private_state'),'admission_ignores_private_state'],
  ]) units.push({name,files:{[file]:view},roots:[file],theorem:'Nickel.EditCommit.'+theorem,inPlace:true,
    log:name+'.proof.log',pass:name+': actual same-history caller requires its contract',failure:'require ordinary shared-state contract dependency rejection'});
  return viewUnits('shared',units,read);
}
