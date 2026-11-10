import assert from 'node:assert/strict';
import {assertReformedSource} from './proof-reform.mjs';
for(const namespace of ['Nickel_crdt.Edit.impl_Tree__add','Nickel_crdt.Edit.has_event','Nickel_crdt.Edit.replay_nodes','Nickel_crdt.Edit.replay_author','Nickel_crdt.Edit.event_basis','Nickel.EditReplay.author_prefix']) {
  const source='Tactics.prune('+JSON.stringify(namespace)+')';
  assertReformedSource('EditReplay',source);
  for(const name of ['fixture','LoopUtil','Vector'])
    assert.throws(()=>assertReformedSource(name,source),new RegExp(name+' reform:'));
}
assert.throws(()=>assertReformedSource('EditReplay','normalize(true)'),/EditReplay reform:/);
