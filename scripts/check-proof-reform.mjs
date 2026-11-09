import assert from 'node:assert/strict';
import {assertReformedSource} from './proof-reform.mjs';
export function checkProofReformFence() {
  const good="import Tactics = FStar.Tactics.V2\nproof p(): unit gives True { assert(True) by { Tactics.smt_sync'(1, 1) } }";
  assertReformedSource('fixture',good);
  for(const namespace of ['Nickel_crdt.Edit.impl_Replica__with_tree','Nickel_crdt.Edit.impl_Replica__plan','Nickel_crdt.Edit.impl_Replica__duplicate','Nickel_crdt.Edit.invalid','Nickel_crdt.Edit.writer_index','Nickel_crdt.Edit.fact_equal','Alloc.Vec.from_seq','Alloc.Vec.impl_1__as_slice','Alloc.Vec.impl_1__len','Core_models.Slice.impl__len','Rust_primitives.Slice.slice_index','Nickel_crdt.Edit.next_counter_after','Rust_primitives.Hax.Folds.fold_range','Rust_primitives.Hax.Folds.fold_range_return','Nickel.LoopUtil.option_run','Nickel.LoopUtil.step_safe','Nickel.LoopUtil.output_safe'])
    assertReformedSource('fixture','import Tactics = FStar.Tactics.V2\nTactics.prune('+JSON.stringify(namespace)+')');
  assertReformedSource('fixture','// norm_spec is prohibited\nfunction name(): string { "Tactics.compute()" }');
  assertReformedSource('fixture','Tactics.prune("Nickel_crdt.Edit.push")');
  for(const bad of [
    'norm_spec([delta_only(["x"])] , x)', 'assert_norm(x)', 'normalize_term(x)', 'normalize(x)', 'FStar.Pervasives.normalize(x)', 'reveal_opaque(x)',
    'Tactics.compute()', 'delta_namespace(["x"])', 'Tactics.unfold_def(x)',
    'let n = Tactics.norm in n(x)', 'import Other = FStar.Tactics.V2',
    'FStar.Tactics.V2.norm(x)', 'import FStar.NormSteps',
    "let solve = Tactics.smt_sync'", "Tactics.smt_sync'(4, 4)",
    'Tactics.set_options("--fuel 100")', 'Tactics.prune("Other")', 'let hide = Tactics.prune',
  ])assert.throws(()=>assertReformedSource('fixture',bad),/fixture reform:/,bad);
  assertReformedSource('EditCausal','Tactics.prune("Nickel.EditCausal.causal_rank")');
  for(const name of ['fixture','EditSchedule','EditPast','EditWellFormed'])
    assert.throws(()=>assertReformedSource(name,'Tactics.prune("Nickel.EditCausal.causal_rank")'),new RegExp(name+' reform:'));
  assertReformedSource('EditWellFormed','Tactics.prune("Nickel.EditIdentity.prefix_absent")');
  assert.throws(()=>assertReformedSource('fixture','Tactics.prune("Nickel.EditIdentity.prefix_absent")'),/fixture reform:/);
  assert.throws(()=>assertReformedSource('EditWellFormed','assert_norm(true)'),/EditWellFormed reform:/);
  assertReformedSource('Spec','Tactics.prune("Nickel_crdt.Edit.impl_Replica__receive")');
  assert.throws(()=>assertReformedSource('fixture','Tactics.prune("Nickel_crdt.Edit.impl_Replica__receive")'),/fixture reform:/);
  assert.throws(()=>assertReformedSource('Spec','assert_norm(true)'),/Spec reform:/);

  assertReformedSource('EditCommit','Tactics.prune("Nickel_crdt.Edit.impl_Replica__receive")');
  assert.throws(()=>assertReformedSource('fixture','Tactics.prune("Nickel_crdt.Edit.impl_Replica__receive")'),/fixture reform:/);
  assert.throws(()=>assertReformedSource('EditCommit','assert_norm(true)'),/EditCommit reform:/);

  for(const namespace of ['Nickel_crdt.Edit.has_event','Nickel_crdt.Edit.extend_past','Nickel_crdt.Edit.past_pass','Nickel_crdt.Edit.past']) {
    assertReformedSource('EditPast','Tactics.prune('+JSON.stringify(namespace)+')');
    assertReformedSource('EditPastTotal','Tactics.prune('+JSON.stringify(namespace)+')');
    assert.throws(()=>assertReformedSource('fixture','Tactics.prune('+JSON.stringify(namespace)+')'),/fixture reform:/);
  }
  for(const native of ['has_event','ready','choose_ready']) {
    assertReformedSource('EditSchedule','Tactics.prune("Nickel_crdt.Edit.'+native+'")');
    assert.throws(()=>assertReformedSource('fixture','Tactics.prune("Nickel_crdt.Edit.'+native+'")'),/fixture reform:/);
  }
  assertReformedSource('EditPastTotal','Tactics.prune("Nickel_crdt.Edit.validate_after")');
  assertReformedSource('EditPastTotal','Tactics.prune("Nickel_crdt.Edit.duplicate_events")');
  assert.throws(()=>assertReformedSource('EditPast','Tactics.prune("Nickel_crdt.Edit.duplicate_events")'),/EditPast reform:/);
  assert.throws(()=>assertReformedSource('EditPast','Tactics.prune("Nickel_crdt.Edit.validate_after")'),/EditPast reform:/);
  for(const name of ['EditCausal','EditAtomic','EditWellFormed','EditPast','EditPastTotal','EditSchedule']) {
    assert.throws(()=>assertReformedSource(name,'assert_norm(true)'),new RegExp(name+' reform:'));
  }
  assertReformedSource('LoopUtil','Tactics.prune("Rust_primitives.Hax.Folds.fold_range_cf")');
  assert.throws(()=>assertReformedSource('fixture','Tactics.prune("Rust_primitives.Hax.Folds.fold_range_cf")'),/fixture reform:/);
  console.log('PASS proof-reform fence: approved direct tactic, normalization/import/alias controls');
}
checkProofReformFence();
