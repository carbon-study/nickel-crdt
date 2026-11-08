// Accepted callers withhold their callee bodies; each must then fail at its owner
// when the contract it composes is withheld too.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import {put,verify} from './proof-cache.mjs';
import {hasOrdinaryTheoremRejection} from './negative-proof-evidence.mjs';
export async function checkAcceptedContracts({proof,output,fstar,models,modelCache,select=()=>true}) {
  const file=path.join(proof,'Nickel.EditAccepted.fst'),original=await fs.readFile(file,'utf8');
  function declaration(theorem) {
    const match=new RegExp('^let (?:rec )?'+theorem+' ','m').exec(original);assert(match,theorem);
    const start=match.index;
    const next=/\n(?:let (?:rec )?\w+ |open |type |module |val )/.exec(original.slice(start+4));
    const end=next?start+4+next.index:original.length;
    return {start,end,body:original.slice(start,end)};
  }
  // Replace one needle inside one named declaration only.
  function withhold(theorem,needle,replacement) {
    const {start,end,body}=declaration(theorem);
    assert.equal(body.split(needle).length,2,theorem+': '+needle);
    return original.slice(0,start)+body.replace(needle,replacement)+original.slice(end);
  }
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
    ['accepted-new-order-without-empty-contract','new_establishes_fact_order','Nickel.EditAtomic.new_has_empty_facts writer limits;','();'],
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
  for(const[name,scope,needle,replacement,owner=scope]of cases.filter(([name])=>select(name))) {
    const view=withhold(scope,needle,replacement),theorem=owner;
    try {await put(file,view);const result=await verify({dir:proof,roots:[file],fstar,models,modelCache});
      await fs.writeFile(path.join(output,name+'.proof.log'),result.log);
      assert(hasOrdinaryTheoremRejection({status:result.status,log:result.log,theorem:'Nickel.EditAccepted.'+theorem,view}),'require ordinary accepted dependency rejection: '+result.log);
      console.log('PASS '+name+': caller needs its checked contract');
    }finally{await put(file,original);}
  }
  await checkCanonicalFrameControls({proof,output,fstar,models,modelCache,select});
}

// Test-only semantic faults in the ghost loop frame. The production proof and
// native translation remain unchanged; the false trust cut must never escape
// this family's disposable workspace or be counted as positive proof evidence.
export async function checkCanonicalFrameControls({proof,output,fstar,models,modelCache,select=()=>true}) {
  const cases=[
    ['accepted-frame-refuses','Result.Result_Err Native.Error_Internal','canonical_succeeds_for_unique_ids'],
    ['accepted-frame-drops-facts','Result.Result_Ok (Alloc.Vec.impl__new ())','canonical_selects_whole_facts'],
  ].filter(([name])=>select(name));
  if(cases.length===0)return;
  const file=path.join(proof,'Nickel.EditAccepted.fst'),nativeFile=path.join(proof,'Nickel_crdt.Edit.fst');
  const original=await fs.readFile(file,'utf8'),native=await fs.readFile(nativeFile,'utf8');
  function bounds(view,name) {
    const matches=[...view.matchAll(new RegExp('^let '+name+' ','gm'))];assert.equal(matches.length,1,name);
    const a=matches[0].index,n=/\n(?:let |type |open |val |module |assume val )/.exec(view.slice(a+4));
    return [a,n?a+4+n.index:view.length];
  }
  const[a,b]=bounds(original,'canonical_uses_complete_range');
  assert.equal(original.slice(a,b).split('\n')[0],'let canonical_uses_complete_range (input: t_Slice Native.t_Fact) : Lemma (ensures Native.canonical input == canonical_loop_result input) =');
  // Deliberately trust only the exact source-to-frame equation. Otherwise a
  // faulty frame is rejected there and never tests the unchanged public laws.
  const trustCut='// TEST-ONLY: assume the transcription equation, never a consumer theorem.\nassume val canonical_uses_complete_range : input:t_Slice Native.t_Fact -> Lemma (ensures Native.canonical input == canonical_loop_result input)\n';
  const healthy=original.slice(0,a)+trustCut+original.slice(b);
  const[c,d]=bounds(healthy,'canonical_loop_result'),header=healthy.slice(c,d).split('\n')[0];
  assert.equal(header,'let canonical_loop_result (input: t_Slice Native.t_Fact) : Result.t_Result (Alloc.Vec.t_Vec Native.t_Fact Alloc.Alloc.t_Global) Native.t_Error =');
  try {
    await put(file,healthy);
    const positive=await verify({dir:proof,roots:[file],fstar,models,modelCache});
    await fs.writeFile(path.join(output,'accepted-frame-healthy.proof.log'),positive.log);
    assert.equal(positive.status,0,'the healthy frame must still verify with this test-only trust cut: '+positive.log);
    console.log('PASS accepted-frame-healthy: test-only trust cut preserves the healthy consumer checks');
    for(const[name,result,owner]of cases) {
      const view=healthy.slice(0,c)+header+'\n  '+result+'\n'+healthy.slice(d);
      await put(file,view);
      assert.equal(await fs.readFile(nativeFile,'utf8'),native,'ghost fault must not mutate the extracted native program');
      const checked=await verify({dir:proof,roots:[file],fstar,models,modelCache});
      await fs.writeFile(path.join(output,name+'.proof.log'),checked.log);
      assert(hasOrdinaryTheoremRejection({status:checked.status,log:checked.log,theorem:'Nickel.EditAccepted.'+owner,view}),'require ordinary public frame rejection: '+checked.log);
      console.log('PASS '+name+': unchanged '+owner+' rejects independently of transcription');
    }
  } finally {
    await put(file,original);
    assert.equal(await fs.readFile(file,'utf8'),original,'restore production frame proof after every fault');
    assert.equal(await fs.readFile(nativeFile,'utf8'),native,'native program remains unchanged');
  }
}
