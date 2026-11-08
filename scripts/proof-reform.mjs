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
const causalVisibility=new Set([
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
export function assertReformedSource(name,source) {
  const ts=tokens(source),fail=message=>assert.fail(name+' reform: '+message);
  for(let i=0;i<ts.length;i++) {
    if(ts.slice(i,i+8).join(' ')==="import Tactics = FStar . Tactics . V2") { i+=7;continue; }
    if(forbidden.has(ts[i]))fail('explicit normalization is prohibited: '+ts[i]);
    if(ts[i]==='FStar'&&ts[i+1]==='.'&&ts[i+2]==='NormSteps')fail('normalizer imports are prohibited');
    if(ts[i]==='FStar'&&ts[i+1]==='.'&&ts[i+2]==='Tactics')
      fail('only the canonical Tactics import is approved');
    if(ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+5]===')'&&
      ['"Nickel_crdt.Edit.impl_Replica__with_tree"','"Nickel_crdt.Edit.impl_Replica__plan"','"Nickel_crdt.Edit.impl_Replica__duplicate"','"Nickel_crdt.Edit.invalid"','"Nickel_crdt.Edit.writer_index"','"Nickel_crdt.Edit.fact_equal"','"Alloc.Vec.from_seq"','"Alloc.Vec.impl_1__as_slice"','"Alloc.Vec.impl_1__len"','"Core_models.Slice.impl__len"','"Rust_primitives.Slice.slice_index"','"Nickel_crdt.Edit.push"','"Nickel_crdt.Edit.impl_Replica__with_counter"','"Nickel_crdt.Edit.next_counter_after"','"Rust_primitives.Hax.Folds.fold_range"','"Rust_primitives.Hax.Folds.fold_range_return"','"Nickel.LoopUtil.option_run"','"Nickel.LoopUtil.step_safe"','"Nickel.LoopUtil.output_safe"','"Nickel_proof_smoke.flip"'].includes(ts[i+4])) { i+=5;continue; }
    if(name==='LoopUtil'&&ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+4]==='"Rust_primitives.Hax.Folds.fold_range_cf"'&&ts[i+5]===')') { i+=5;continue; }
    if(name==='EditWellFormed'&&ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+5]===')'&&wellFormedVisibility.has(ts[i+4])) { i+=5;continue; }
    if(name==='Spec'&&ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+5]===')'&&specVisibility.has(ts[i+4])) { i+=5;continue; }
    if(name==='EditCommit'&&ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+5]===')'&&commitVisibility.has(ts[i+4])) { i+=5;continue; }
    if(name==='EditAtomic'&&ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+5]===')'&&atomicVisibility.has(ts[i+4])) { i+=5;continue; }
    if(name==='EditCausal'&&ts[i]==='Tactics'&&ts[i+1]==='.'&&ts[i+2]==='prune'&&ts[i+3]==='('&&ts[i+5]===')'&&causalVisibility.has(ts[i+4])) { i+=5;continue; }
    if(ts[i]==='Tactics') {
      // No aliasing even of approved methods: only this direct call is admitted.
      if(ts.slice(i,i+8).join(' ')!=="Tactics . smt_sync' ( 1 , 1 )")
        fail('only approved direct SMT/visibility tactic calls are permitted');
      i+=7;
    }
  }
}
export async function checkProofReform(root,names=['EditAtomic','LoopUtil','Smoke','Vector','EditCausal','EditIdentity','EditWellFormed','Spec','EditCommit']) {
  for(const name of names)assertReformedSource(name,await fs.readFile(path.join(root,'proofs',name+'.lt'),'utf8'));
  const accepted=await fs.readFile(path.join(root,'proofs','EditAccepted.lt'),'utf8');
  for(const name of ['push_outcome','push_result_is_exact','append_fresh_preserves_unique','append_whole_fact','push_has_exact_contents','push_membership','member_lookup','absent_lookup','event_order_is_key_order','canonical_has_unique_ids','canonical_is_permutation_independent','canonical_selects_whole_facts','canonical_step_preserves_order','canonical_step_preserves_unique','canonical_step_selects_whole_facts','choice_always_returns','empty_has_unique_ids','find_id_position','membership_exact','new_establishes_fact_order','new_establishes_unique_ids','ordered_contents_determine_vector','receive_added_facts_are_ordered','receive_added_has_exact_contents','receive_added_ids_are_unique','receive_added_shared_state_agrees','selected_fact_is_exact','selected_fact_keeps_id','selected_id_is_unseen','shorter_output_has_unseen','strict_nat_pair','successful_plan_pushed_fact','tree_installation_preserves_facts','unique_nat_positions','unique_slice_nat_positions']) {
    const match=new RegExp('^(?:function!?|proof!?) '+name+'[<(]','m').exec(accepted);assert(match,'missing reformed Accepted declaration '+name);
    const tail=accepted.slice(match.index+match[0].length),next=/\n(?:function|proof!?|type|import) /.exec(tail);
    const end=next?match.index+match[0].length+next.index:accepted.length;
    assertReformedSource('EditAccepted.'+name,accepted.slice(match.index,end));
  }
}
