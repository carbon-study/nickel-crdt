import './check-replay-reform.mjs';
import './check-basis-reform.mjs';
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
  for(const namespace of ['Nickel_crdt.Edit.v_TEXT_OPS','Nickel_crdt.Event_layer.graph_ops','Nickel_crdt.Event_layer.event_ops']) {
    for(const name of ['EventGraphText','EditIdentity','EditAccepted','EditPast','EditSchedule','EditWellFormed','EditPastTotal','EditBasis'])
      assertReformedSource(name,'Tactics.prune('+JSON.stringify(namespace)+')');
    for(const name of ['fixture','EventGraph','EditAtomic','EditCommit','Spec'])
      assert.throws(()=>assertReformedSource(name,'Tactics.prune('+JSON.stringify(namespace)+')'),new RegExp(name+' reform:'));
  }
  assertReformedSource('EditCausal','Tactics.prune("Nickel.EditCausal.causal_rank")');
  assertReformedSource('EditSchedule','Tactics.prune("Nickel.EditCausal.causal_rank")');
  for(const name of ['fixture','EditPast','EditPastTotal','EditWellFormed'])
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
  for(const boundary of ['Nickel.EditSchedule.cut_order','Nickel.EditPast.ancestor','Nickel_crdt.Edit.past','Nickel_crdt.Edit.duplicate_events']) {
    assertReformedSource('EditSchedule','Tactics.prune("'+boundary+'")');
    assert.throws(()=>assertReformedSource('fixture','Tactics.prune("'+boundary+'")'),/fixture reform:/);
  }
  assertReformedSource('EditSchedule','Tactics.prune("Nickel.EditSchedule.no_eligible_prefix")');
  assertReformedSource('EditSchedule','Tactics.prune("Nickel.EditSchedule.causal_trace")');
  assertReformedSource('EditSchedule',"Tactics.smt_sync'(0, 0)");
  for(const name of ['fixture','EditCausal','EditPast','EditPastTotal','EditAccepted'])
    assert.throws(()=>assertReformedSource(name,"Tactics.smt_sync'(0, 0)"),new RegExp(name+' reform:'));
  assertReformedSource('EditSchedule','Tactics.prune("Nickel.EditSchedule.event_work_prefix")');
  for(const name of ['fixture','EditCausal','EditPast','EditPastTotal','EditAccepted'])
    assert.throws(()=>assertReformedSource(name,'Tactics.prune("Nickel.EditSchedule.event_work_prefix")'),new RegExp(name+' reform:'));
  assertReformedSource('EditSchedule','Tactics.prune("Nickel.EditPastTotal.unique_selection")');
  for(const name of ['fixture','EditCausal','EditPast'])
    assert.throws(()=>assertReformedSource(name,'Tactics.prune("Nickel.EditPastTotal.unique_selection")'),new RegExp(name+' reform:'));
  for(const name of ['fixture','EditCausal','EditPast'])
    assert.throws(()=>assertReformedSource(name,'Tactics.prune("Nickel.EditSchedule.causal_trace")'),new RegExp(name+' reform:'));
  for(const name of ['fixture','EditCausal','EditPast'])
    assert.throws(()=>assertReformedSource(name,'Tactics.prune("Nickel.EditSchedule.no_eligible_prefix")'),new RegExp(name+' reform:'));
  for(const ghost of ['Nickel.EditPast.ancestor','Nickel.EditPast.fact_id_present','Nickel.EditPast.exact_past_result','Nickel.EditPastTotal.shared_ancestry','Nickel.EditPastTotal.same_members']) {
    assertReformedSource('EditPastTotal','Tactics.prune('+JSON.stringify(ghost)+')');
    // EditSchedule may also prune `ancestor` (its cut-order boundary, #83); every
    // other ghost here is EditPastTotal-only.
    for(const name of ['fixture','EditPast','EditSchedule','EditCausal'].filter(name=>!(name==='EditSchedule'&&ghost==='Nickel.EditPast.ancestor')))
      assert.throws(()=>assertReformedSource(name,'Tactics.prune('+JSON.stringify(ghost)+')'),new RegExp(name+' reform:'));
  }
  for(const native of ['has_event','ready','choose_ready','interpret','interpret_event','interpret_scheduled']) {
    assertReformedSource('EditSchedule','Tactics.prune("Nickel_crdt.Edit.'+native+'")');
    assert.throws(()=>assertReformedSource('fixture','Tactics.prune("Nickel_crdt.Edit.'+native+'")'),/fixture reform:/);
  }
  for(const native of ['interpret_event','interpret_scheduled'])
    for(const name of ['EditCausal','EditPast'])
      assert.throws(()=>assertReformedSource(name,'Tactics.prune("Nickel_crdt.Edit.'+native+'")'),new RegExp(name+' reform:'));
  assertReformedSource('EditPast','Tactics.prune("Nickel.EventGraph.membership_is_exact")');
  for(const name of ['fixture','EditCausal','EditAtomic','EditIdentity','EditWellFormed','EditPastTotal','EditSchedule'])
    assert.throws(()=>assertReformedSource(name,'Tactics.prune("Nickel.EventGraph.membership_is_exact")'),new RegExp(name+' reform:'));
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
