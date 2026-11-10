// Keep this slice's fixtures separate from the append-heavy shared list.
import assert from 'node:assert/strict';
import {assertReformedSource} from './proof-reform.mjs';
for(const namespace of ['clone_selected_fact','has_event','past','select_basis']) {
  const source='Tactics.prune("Nickel_crdt.Edit.'+namespace+'")';
  assertReformedSource('EditBasis',source);
  for(const name of ['fixture','LoopUtil','Vector'])
    assert.throws(()=>assertReformedSource(name,source),new RegExp(name+' reform:'));
}
assert.throws(()=>assertReformedSource('EditBasis','Tactics.prune("Nickel.EditBasis.selected_prefix")'),/EditBasis reform:/);
assert.throws(()=>assertReformedSource('EditBasis','normalize(true)'),/EditBasis reform:/);
