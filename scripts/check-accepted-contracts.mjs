// Accepted callers withhold their callee bodies; each must then fail at its owner
// when the contract it composes is withheld too.
import assert from 'node:assert/strict';
import {fstarDeclaration,replaceUniqueInFstarDeclaration} from './fstar-mutation-scope.mjs';
import {viewUnits} from './text-family-run.mjs';
export function acceptedUnits(read) {
  const file='Nickel.EditAccepted.fst',original=read(file);
  const declaration=theorem=>fstarDeclaration(original,theorem);
  const withhold=(theorem,needle,replacement)=>replaceUniqueInFstarDeclaration(original,theorem,needle,replacement);
  const step=' [SMTPat (Native.canonical_step input out)]',tree=' [SMTPat (Native.impl_Replica__with_tree state tree)]';
  const cases=[
    ['accepted-push-without-length-value','push_result_is_exact','  length_value ();','  ();'],
    ['accepted-push-without-value','push_result_is_exact','Nickel.Vector.vector_from_seq_value (Seq.append (Alloc.Vec.impl_1__as_slice before) (Seq.create 1 fact));','();'],
    ['accepted-unique-without-step-interface','canonical_has_unique_ids','canonical_step_preserves_unique facts out;','();'],
    ['accepted-content-without-step-interface','canonical_selects_whole_facts','canonical_step_selects_whole_facts input out (v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice out)));','();'],
    ['accepted-initial-value-canonical_has_unique_ids','canonical_has_unique_ids','Nickel.Vector.empty_vector_value #Native.t_Fact ();','();'],
    ['accepted-initial-value-canonical_selects_whole_facts','canonical_selects_whole_facts','Nickel.Vector.empty_vector_value #Native.t_Fact ();','();'],
    ['accepted-initial-value-canonical_orders_facts','canonical_orders_facts','Nickel.Vector.empty_vector_value #Native.t_Fact ();','();'],
    ['accepted-initial-value-canonical_succeeds_for_unique_ids','canonical_succeeds_for_unique_ids','Nickel.Vector.empty_vector_value #Native.t_Fact ();','();'],
    ['accepted-unseen-without-boolean-shape','selected_id_is_unseen',' [SMTPat (Native.has_fact xs id)]',''],
    ['accepted-absence-without-membership','membership_absence_exact','membership_exact input id;','();'],
    ['accepted-absence-without-forward','membership_absence_exact','membership_absent input id;','();'],
    ['accepted-absence-without-reverse','membership_absence_exact','absent_lookup input id (mk_usize 0);','();'],
    ['accepted-member-without-step','member_lookup','Nickel.LoopUtil.option_run_step (Nickel.EditIdentity.length facts) at () (member_next facts id) member_stop member_done;','();'],
    ['accepted-member-without-end','member_lookup','Nickel.LoopUtil.option_run_end (Nickel.EditIdentity.length facts) at () (member_next facts id) member_stop member_done;','();'],
    ['accepted-member-without-induction','member_lookup','member_lookup facts id (at +! mk_int 1);','();'],
    ['accepted-membership-without-interpreter','membership_exact','Nickel.LoopUtil.option_interpret_any (mk_usize 0) (Nickel.EditIdentity.length facts) (member_next facts id) member_stop member_done;','();'],
    ['accepted-membership-without-lookup','membership_exact','member_lookup facts id (mk_usize 0);','();'],
    ['accepted-empty-without-vector-contract','empty_has_unique_ids','Nickel.Vector.empty_vector_contents #Native.t_Fact ();','();'],
    ['accepted-new-order-without-empty-contract','new_establishes_fact_order','Nickel.EditAtomic.new_has_empty_facts writer;','();'],
    ['accepted-least-without-step','selected_id_is_least','least_extends_all input out;','();'],
    ['accepted-order-without-step-contract','canonical_orders_facts',step,''],
    ['accepted-progress-without-step-contract','canonical_succeeds_for_unique_ids',step,''],
    ['accepted-step-without-push-contract','canonical_step_succeeds','push_result_is_exact out (Native.clone_selected_fact (Rust_primitives.Slice.slice_index input k));','();'],
    ['accepted-frontier-without-bound','append_least_preserves_frontier','frontier_bounds_unseen input out i j;','();'],
    ['accepted-frontier-without-membership','append_least_preserves_frontier','push_membership out fact (Rust_primitives.Slice.slice_index input j).f_id;','();'],
    ['accepted-publication-without-tree-contract','plan_publishes_canonical_facts',tree,''],
    // Result-shape patterns restore only the withheld callees' declared result types.
    ['accepted-publication-without-canonical-shape','canonical_has_result_shape',' [SMTPat (Native.canonical input)]','','plan_publishes_canonical_facts'],
    ['accepted-publication-without-interpret-shape','interpret_has_result_shape',' [SMTPat (Native.interpret input)]','','plan_publishes_canonical_facts'],
    ['accepted-interpretation-without-tree-contract','plan_publishes_interpretation','f_tree == tree)'+tree,'f_tree == tree)'],
  ];
  for(const owner of ['selected_id_is_unseen','canonical_has_unique_ids','canonical_selects_whole_facts','selected_id_is_least','canonical_orders_facts','choice_always_returns','canonical_succeeds_for_unique_ids']) {
    const {body}=declaration(owner);
    const calls=[...body.matchAll(/^  Nickel\.LoopUtil\.result_preserve_any [^\n]+;$/gm)];
    assert.equal(calls.length,1,owner+': one Result-rule call');
    cases.push(['accepted-loop-without-result-rule-'+owner,owner,calls[0][0],'  ();']);
  }
  for(const owner of ['canonical_has_unique_ids','canonical_selects_whole_facts','canonical_orders_facts','canonical_succeeds_for_unique_ids']) {
    const {body}=declaration(owner);
    const calls=[...body.matchAll(/^  canonical_uses_complete_range [^\n]+;$/gm)];
    assert.equal(calls.length,1,owner+': one source-frame call');
    cases.push(['accepted-loop-without-source-frame-'+owner,owner,calls[0][0],'  ();']);
  }
  const units=cases.map(([name,scope,needle,replacement,owner=scope])=>({name,files:{[file]:withhold(scope,needle,replacement)},roots:[file],
    theorem:'Nickel.EditAccepted.'+owner,inPlace:true,log:name+'.proof.log',pass:name+': caller needs its checked contract',failure:'require ordinary accepted dependency rejection'}));
  return viewUnits('accepted',[...units,...canonicalFrameControls(read)],read);
}

// Test-only semantic faults in the ghost loop frame. The production proof and
// native translation remain unchanged; the false trust cut must never escape
// this family's disposable workspace or be counted as positive proof evidence.
// The healthy frame is an explicit expect "verify" unit (#198): it must verify with the test-only trust cut, and it is
// neither a rejection nor production proof evidence. Every unit here runs in place in the family's disposable workspace
// copy, which is restored after each unit; the extracted native program is checked unchanged before and after each.
export function canonicalFrameControls(read) {
  const cases=[
    ['accepted-frame-refuses','Result.Result_Err Native.Error_Internal','canonical_succeeds_for_unique_ids'],
    ['accepted-frame-drops-facts','Result.Result_Ok (Alloc.Vec.impl__new ())','canonical_selects_whole_facts'],
  ];
  const file='Nickel.EditAccepted.fst',nativeFile='Nickel_crdt.Edit.fst';
  const original=read(file);
  const bounds=(view,name)=>{const {start,end}=fstarDeclaration(view,name);return [start,end];};
  const[a,b]=bounds(original,'canonical_uses_complete_range');
  assert.equal(original.slice(a,b).split('\n')[0],'let canonical_uses_complete_range (input: t_Slice Native.t_Fact) : Lemma (ensures Native.canonical input == canonical_loop_result input) =');
  // Deliberately trust only the exact source-to-frame equation. Otherwise a
  // faulty frame is rejected there and never tests the unchanged public laws.
  const trustCut='// TEST-ONLY: assume the transcription equation, never a consumer theorem.\nassume val canonical_uses_complete_range : input:t_Slice Native.t_Fact -> Lemma (ensures Native.canonical input == canonical_loop_result input)\n';
  const healthy=original.slice(0,a)+trustCut+original.slice(b);
  const[c,d]=bounds(healthy,'canonical_loop_result'),header=healthy.slice(c,d).split('\n')[0];
  assert.equal(header,'let canonical_loop_result (input: t_Slice Native.t_Fact) : Result.t_Result facts_vec Native.t_Error =');
  return [
    {name:'accepted-frame-healthy',expect:'verify',files:{[file]:healthy},roots:[file],inPlace:true,unchanged:[nativeFile],
      log:'accepted-frame-healthy.proof.log',pass:'accepted-frame-healthy: test-only trust cut preserves the healthy consumer checks',failure:'the healthy frame must still verify with this test-only trust cut'},
    ...cases.map(([name,result,owner])=>({name,files:{[file]:healthy.slice(0,c)+header+'\n  '+result+'\n'+healthy.slice(d)},roots:[file],
      theorem:'Nickel.EditAccepted.'+owner,inPlace:true,unchanged:[nativeFile],log:name+'.proof.log',
      pass:name+': unchanged '+owner+' rejects independently of transcription',failure:'require ordinary public frame rejection'})),
  ];
}
