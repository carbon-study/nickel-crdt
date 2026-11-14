// A source-style fence, not an isolation boundary or a proof about arbitrary aliases.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
const forbidden=new Set(['norm','norm_spec','assert_norm','normalize_term','normalize','norm_term','reveal_opaque',
  'compute','delta','delta_only','delta_once','delta_namespace','unfold_def',
  'iota','zeta','zeta_full','primops','unmeta','unascribe']);
function tokens(source) {
  return [...source.matchAll(/\/\/[^\n]*|\/\*[\s\S]*?\*\/|"(?:\\.|[^"\\])*"|[A-Za-z_][A-Za-z0-9_']*|[^\s]/g)]
    .map(m=>m[0]).filter(t=>!t.startsWith('//')&&!t.startsWith('/*'));
}
const pastVisibility=new Set(['"Nickel_crdt.Edit.has_event"','"Nickel_crdt.Edit.extend_past"','"Nickel_crdt.Edit.past_pass"','"Nickel_crdt.Edit.past"']);
// Two-receiver past selection: ghost visibility at query-local composition steps.
const receiverPastVisibility=['"Nickel.EditPast.ancestor"','"Nickel.EditPast.fact_id_present"','"Nickel.EditPast.exact_past_result"','"Nickel.EditPastTotal.shared_ancestry"','"Nickel.EditPastTotal.same_members"'];
const pastTotalVisibility=new Set([...pastVisibility,'"Nickel_crdt.Edit.validate_after"','"Nickel_crdt.Edit.duplicate_events"',...receiverPastVisibility]);
const causalVisibility=new Set([
  '"Nickel.EditCausal.causal_rank"',
  '"Nickel.EditIdentity.prefix_absent"','"Nickel_crdt.Edit.has_fact"','"Nickel_crdt.Edit.impl_Replica__new"','"Nickel_crdt.Edit.impl_Replica__receive"','"Nickel_crdt.Edit.impl_Replica__edit"']);
const atomicVisibility=new Set([
  '"Nickel_crdt.Edit.frontier"',
'"Alloc.Vec.impl__new"','"Nickel_crdt.Edit.impl_Replica__validate_new"','"Nickel_crdt.Edit.canonical"','"Nickel_crdt.Edit.interpret"']);
const wellFormedVisibility=new Set([
  '"Nickel_crdt.Edit.impl_Replica__new"',
  '"Nickel_crdt.Edit.validate_after"','"Nickel_crdt.Edit.past"','"Nickel_crdt.Edit.impl_Replica__validate_new"',
  '"Nickel_crdt.Edit.impl_Replica__receive"','"Nickel_crdt.Edit.impl_Replica__edit"',
  '"Nickel_crdt.Edit.validate_scalars"',
  '"Nickel.Vector.slice_index"','"Nickel.Vector.slice_length"','"Nickel_crdt.Edit.has_fact"',
  '"Nickel.EditIdentity.prefix_absent"'
]);
// Only the public Spec composition may hide these native operation facts.
const specVisibility=new Set([
  '"Nickel_crdt.Edit.impl_Replica__new"',
  '"Nickel_crdt.Edit.impl_Replica__receive"',
  '"Nickel_crdt.Edit.impl_Replica__edit"',
]);
const commitVisibility=new Set([
  '"Nickel_crdt.Edit.frontier"','"Nickel_crdt.Edit.impl_Replica__receive"','"Nickel_crdt.Edit.impl_Replica__edit"',
]);
// Accepted callers may hide these callee bodies, so their proofs go through the callee contracts.
const acceptedVisibility=new Set([
  '"Alloc.Vec.impl__new"','"Nickel_crdt.Edit.impl_Replica__new"',
  '"Nickel_crdt.Edit.canonical_step"','"Nickel_crdt.Edit.choose_unseen"','"Nickel_crdt.Edit.canonical"',
  '"Nickel_crdt.Edit.has_fact"','"Nickel_crdt.Edit.event_lt"','"Nickel_crdt.Edit.clone_selected_fact"','"Nickel_crdt.Edit.interpret"',
]);
// Generic owners get only the specific callee visibility used in their proofs.
const genericVisibility={
  EventGraph:new Set(["\"Nickel_crdt.Event_layer.has_id\"","\"Nickel_crdt.Event_layer.ready\""]),
  EventGraphText:new Set(["\"Nickel_crdt.Edit.v_TEXT_OPS\"","\"Nickel_crdt.Event_layer.graph_ops\"","\"Nickel_crdt.Event_layer.event_ops\""]),
  EventClassifier:new Set([]),
  EventShell:new Set(["\"Nickel_crdt.Event_shell.receive_into\""]),
  EditAtomic:new Set(["\"Nickel_crdt.Event_shell.plan\"","\"Nickel_crdt.Event_layer.push\"","\"Nickel_crdt.Event_layer.canonical\"","\"Nickel_crdt.Event_shell.receive\"","\"Nickel_crdt.Event_shell.receive_into\"","\"Nickel_crdt.Event_layer.frontier\""]),
  EditCommit:new Set(["\"Nickel_crdt.Event_shell.plan\"","\"Nickel_crdt.Event_layer.frontier\"","\"Nickel_crdt.Event_shell.receive\"","\"Nickel_crdt.Event_shell.receive_into\""]),
  EditIdentity:new Set(["\"Nickel_crdt.Edit.v_TEXT_OPS\"","\"Nickel_crdt.Event_layer.graph_ops\"","\"Nickel_crdt.Event_layer.event_ops\"","\"Nickel_crdt.Event_layer.classify\"","\"Nickel_crdt.Event_shell.plan\""]),
  EditBasis:new Set(["\"Nickel_crdt.Edit.v_TEXT_OPS\"","\"Nickel_crdt.Event_layer.graph_ops\"","\"Nickel_crdt.Event_layer.event_ops\"","\"Nickel_crdt.Event_layer.clone_selected_fact\"","\"Nickel_crdt.Event_layer.has_id\"","\"Nickel_crdt.Event_layer.push\"","\"Nickel_crdt.Event_layer.select_basis\"","\"Nickel_crdt.Event_layer.past\""]),
  EditPast:new Set(["\"Nickel_crdt.Edit.v_TEXT_OPS\"","\"Nickel_crdt.Event_layer.graph_ops\"","\"Nickel_crdt.Event_layer.event_ops\"","\"Nickel.EventGraph.membership_is_exact\"","\"Nickel_crdt.Event_layer.has_id\"","\"Nickel_crdt.Event_layer.push\"","\"Nickel_crdt.Event_layer.extend_past\"","\"Nickel_crdt.Event_layer.past_pass\"","\"Nickel_crdt.Event_layer.past\""]),
  EditPastTotal:new Set(["\"Nickel_crdt.Edit.v_TEXT_OPS\"","\"Nickel_crdt.Event_layer.graph_ops\"","\"Nickel_crdt.Event_layer.event_ops\"","\"Nickel_crdt.Event_layer.push\"","\"Nickel_crdt.Event_layer.has_id\"","\"Nickel_crdt.Event_layer.extend_past\"","\"Nickel_crdt.Event_layer.past_pass\"","\"Nickel_crdt.Event_layer.validate_after\"","\"Nickel_crdt.Event_layer.past\"","\"Nickel_crdt.Event_layer.duplicate_ids\""]),
  EditSchedule:new Set(["\"Nickel_crdt.Edit.v_TEXT_OPS\"","\"Nickel_crdt.Event_layer.graph_ops\"","\"Nickel_crdt.Event_layer.event_ops\"","\"Nickel_crdt.Event_layer.ready\"","\"Nickel_crdt.Event_layer.choose_ready\"","\"Nickel_crdt.Event_layer.push\"","\"Nickel_crdt.Event_shell.scheduled\"","\"Nickel_crdt.Event_layer.duplicate_ids\"","\"Nickel_crdt.Event_layer.past\""]),
  EditAccepted:new Set(["\"Nickel_crdt.Edit.v_TEXT_OPS\"","\"Nickel_crdt.Event_layer.graph_ops\"","\"Nickel_crdt.Event_layer.event_ops\"","\"Nickel_crdt.Event_layer.has_fact\"","\"Nickel_crdt.Event_layer.push\"","\"Nickel_crdt.Event_layer.canonical_step\"","\"Nickel_crdt.Event_layer.canonical\"","\"Nickel_crdt.Event_layer.choose_unseen\""]),
  EditWellFormed:new Set(["\"Nickel_crdt.Edit.v_TEXT_OPS\"","\"Nickel_crdt.Event_layer.graph_ops\"","\"Nickel_crdt.Event_layer.event_ops\"","\"Nickel_crdt.Event_shell.plan\"","\"Nickel_crdt.Event_shell.receive\"","\"Nickel_crdt.Event_shell.receive_into\"","\"Nickel_crdt.Event_layer.has_fact\"","\"Nickel_crdt.Event_layer.validate_after\"","\"Nickel_crdt.Event_layer.past\""]),
  EditCausal:new Set(["\"Nickel_crdt.Event_layer.has_fact\"","\"Nickel_crdt.Event_shell.receive\"","\"Nickel_crdt.Event_shell.receive_into\""]),
  Spec:new Set(["\"Nickel_crdt.Event_shell.receive\"","\"Nickel_crdt.Event_shell.receive_into\""]),
  Canonical:new Set(["\"Nickel.Canonical.push_is_exact\"","\"Nickel_crdt.Event_layer.canonical\"","\"Alloc.Vec.impl__new\"","\"Nickel_crdt.Event_layer.has_fact\"","\"Nickel_crdt.Event_layer.push\"","\"Nickel_crdt.Event_layer.choose_unseen\"","\"Nickel_crdt.Event_layer.clone_selected_fact\"","\"Nickel_crdt.Event_layer.canonical_step\""]),
  Register:new Set(["\"Nickel_crdt.Register.fact_equal\"","\"Nickel_crdt.Register.copy_fact\"","\"Nickel_crdt.Register.same_id\"","\"Nickel_crdt.Register.v_OPS\"","\"Nickel_crdt.Event_layer.graph_ops\"","\"Nickel_crdt.Event_layer.event_ops\"","\"Nickel_crdt.Register.impl_Replica__write\"","\"Nickel.Register.planned_checks_payload\"","\"Nickel_crdt.Event_layer.validate_event\"","\"Nickel_crdt.Event_layer.select_basis\"","\"Nickel_crdt.Register.read_history\"","\"Nickel.Register.planned_preserves_private\"","\"Nickel_crdt.Event_layer.push\"","\"Nickel_crdt.Event_layer.canonical\"","\"Nickel_crdt.Event_shell.plan\"","\"Nickel_crdt.Register.prepare\"","\"Nickel_crdt.Register.execute\"","\"Nickel_crdt.Register.duplicate\"","\"Nickel_crdt.Register.validate\"","\"Nickel_crdt.Register.impl_Replica__receive\"","\"Nickel_crdt.Event_layer.frontier\"","\"Nickel_crdt.Register.next_lamport\"","\"Nickel_crdt.Register.later\"","\"Nickel_crdt.Register.winner\"","\"Nickel_crdt.Register.bytes_equal\"","\"Nickel_crdt.Register.planned\"","\"Nickel_crdt.Register.impl_Replica__read\"","\"Nickel_crdt.Register.write_equal\"","\"Nickel_crdt.Event_shell.receive_into\"","\"Nickel_crdt.Causal.event_equal\""]),
  // Success-only register exact past: shared past/basis bodies only, no client names.
  RegisterPast:new Set(["\"Nickel_crdt.Event_layer.has_id\"","\"Nickel_crdt.Event_layer.push\"","\"Rust_primitives.Hax.Folds.fold_range_return\"","\"Nickel_crdt.Event_layer.extend_past\"","\"Nickel_crdt.Event_layer.past_pass\"","\"Nickel_crdt.Event_layer.validate_after\"","\"Nickel_crdt.Event_layer.past\"","\"Nickel_crdt.Event_layer.clone_selected_fact\"","\"Nickel.LoopUtil.step_safe\"","\"Nickel.LoopUtil.output_safe\"","\"Nickel_crdt.Event_layer.duplicate_ids\"","\"Nickel_crdt.Event_layer.validate_event\""]),
  Vector:new Set([])
};
export function assertReformedSource(name,source) {
  const ts=tokens(source),fail=message=>assert.fail(name+' reform: '+message);
  for(let i=0;i<ts.length;i++) {
    if(ts.slice(i,i+8).join(' ')==="import Tactics = FStar . Tactics . V2") { i+=7;continue; }
    if(forbidden.has(ts[i]))fail('explicit normalization is prohibited: '+ts[i]);
    if(ts[i]==='FStar'&&ts[i+1]==='.'&&ts[i+2]==='NormSteps')fail('normalizer imports are prohibited');
    if(ts[i]==='FStar'&&ts[i+1]==='.'&&ts[i+2]==='Tactics')
      fail('only the canonical Tactics import is approved');
    if(genericVisibility[name]?.has(ts[i+4])&&ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+5]===')') { i+=5;continue; }
    if(ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+5]===')'&&
      ['"Nickel_crdt.Edit.impl_Replica__with_tree"','"Nickel_crdt.Edit.impl_Replica__plan"','"Nickel_crdt.Edit.impl_Replica__duplicate"','"Nickel_crdt.Edit.invalid"','"Nickel_crdt.Edit.writer_index"','"Nickel_crdt.Edit.fact_equal"','"Alloc.Vec.from_seq"','"Alloc.Vec.impl_1__as_slice"','"Alloc.Vec.impl_1__len"','"Core_models.Slice.impl__len"','"Rust_primitives.Slice.slice_index"','"Nickel_crdt.Edit.push"','"Nickel_crdt.Edit.impl_Replica__with_counter"','"Nickel_crdt.Edit.next_counter_after"','"Rust_primitives.Hax.Folds.fold_range"','"Rust_primitives.Hax.Folds.fold_range_return"','"Nickel.LoopUtil.option_run"','"Nickel.LoopUtil.step_safe"','"Nickel.LoopUtil.output_safe"','"Nickel_proof_smoke.flip"'].includes(ts[i+4])) { i+=5;continue; }
    if(name==='LoopUtil'&&ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+4]==='"Rust_primitives.Hax.Folds.fold_range_cf"'&&ts[i+5]===')') { i+=5;continue; }
    if(name==='EditWellFormed'&&ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+5]===')'&&wellFormedVisibility.has(ts[i+4])) { i+=5;continue; }
    if(name==='Spec'&&ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+5]===')'&&specVisibility.has(ts[i+4])) { i+=5;continue; }
    if(name==='EditAccepted'&&ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+5]===')'&&acceptedVisibility.has(ts[i+4])) { i+=5;continue; }
    if(name==='EditCommit'&&ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+5]===')'&&commitVisibility.has(ts[i+4])) { i+=5;continue; }
    if(name==='EditAtomic'&&ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+5]===')'&&atomicVisibility.has(ts[i+4])) { i+=5;continue; }
    if(name==='EditSchedule'&&ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+5]===')'&&['"Nickel.EditCausal.causal_rank"','"Nickel.EditSchedule.event_work_prefix"','"Nickel_crdt.Edit.duplicate_events"','"Nickel.EditSchedule.cut_order"','"Nickel.EditPast.ancestor"','"Nickel_crdt.Edit.past"','"Nickel.EditPastTotal.unique_selection"','"Nickel.EditSchedule.causal_trace"','"Nickel_crdt.Edit.interpret"','"Nickel_crdt.Edit.interpret_event"','"Nickel_crdt.Edit.interpret_scheduled"','"Nickel.EditSchedule.no_eligible_prefix"','"Nickel_crdt.Edit.has_event"','"Nickel_crdt.Edit.ready"','"Nickel_crdt.Edit.choose_ready"'].includes(ts[i+4])) { i+=5;continue; }
    if(name==='EditReplay'&&ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+5]===')'&&['"Nickel_crdt.Edit.impl_Tree__add"','"Nickel_crdt.Edit.has_event"','"Nickel_crdt.Edit.replay_nodes"','"Nickel_crdt.Edit.replay_author"','"Nickel_crdt.Edit.event_basis"','"Nickel.EditReplay.author_prefix"','"Nickel.EditReplay.group_follows"'].includes(ts[i+4])) { i+=5;continue; }
    if(name==='EditBasis'&&ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+5]===')'&&['"Nickel_crdt.Edit.clone_selected_fact"','"Nickel_crdt.Edit.has_event"','"Nickel_crdt.Edit.past"','"Nickel_crdt.Edit.select_basis"'].includes(ts[i+4])) { i+=5;continue; }
    if(name==='EditPast'&&ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+5]===')'&&pastVisibility.has(ts[i+4])) { i+=5;continue; }
    if(name==='EditPastTotal'&&ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+5]===')'&&pastTotalVisibility.has(ts[i+4])) { i+=5;continue; }
    if(name==='EditCausal'&&ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+5]===')'&&causalVisibility.has(ts[i+4])) { i+=5;continue; }
    if(ts[i]==='Tactics') {
      // No aliasing even of approved methods: only this direct call is admitted.
      if(ts.slice(i,i+8).join(' ')!=="Tactics . smt_sync' ( 1 , 1 )" &&
        !(name==='EditSchedule'&&ts.slice(i,i+8).join(' ')==="Tactics . smt_sync' ( 0 , 0 )"))
        fail('only approved direct SMT/visibility tactic calls are permitted');
      i+=7;
    }
  }
}
export async function checkProofReform(root,names=['LoopEquality','EventGraph','EventGraphText','EventShell','EventClassifier','EditAtomic','LoopUtil','Smoke','Vector','EditCausal','EditIdentity','EditWellFormed','Spec','EditCommit','EditAccepted','EditPast','EditPastTotal','EditSchedule','EditBasis','EditReplay']) {
  for(const name of names)assertReformedSource(name,await fs.readFile(path.join(root,'proofs',name+'.lt'),'utf8'));
}
