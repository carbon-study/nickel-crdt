(* Latte generated F* view *)
module Nickel.EditAccepted

open Nickel.Prelude

open Rust_primitives

open Core_models

open FStar.Pervasives

open Nickel.LoopUtil

open Nickel.LoopEquality

open Nickel.EventGraphText

open Nickel.EditIdentity

module Native = Nickel_crdt.Edit

module Result = Core_models.Result

module Option = Core_models.Option

module Tactics = FStar.Tactics.V2

open Nickel.Vector

module Seq = FStar.Seq

unfold type facts_vec = Alloc.Vec.t_Vec Native.t_Fact Alloc.Alloc.t_Global

let ids_unique (facts: facts_vec) : Type0 =
  Nickel.EditIdentity.unique_ids (Alloc.Vec.impl_1__as_slice facts)

let member_next (facts: t_Slice Native.t_Fact) (id: Native.t_EventId) : Nickel.LoopUtil.transition unit (Nickel.EditIdentity.length facts) =
  fun _ at -> if (Rust_primitives.Slice.slice_index facts at).f_id ==? id then
    begin Option.Option_None end
  else
    begin Option.Option_Some () end

let member_stop (value: unit) (at: usize) : bool =
  true

let member_done (value: unit) : bool =
  false

let member_value (found: Option.t_Option Native.t_Fact) : bool =
  match found with | Option.Option_None -> begin false end | Option.Option_Some _ -> begin true end

let member_run (facts: t_Slice Native.t_Fact) (id: Native.t_EventId) (at: usize{v at <= v (Nickel.EditIdentity.length facts)}) : bool =
  Nickel.LoopUtil.option_run (Nickel.EditIdentity.length facts) at () (member_next facts id) member_stop member_done

let rec member_lookup (facts: t_Slice Native.t_Fact) (id: Native.t_EventId) (at: usize{v at <= v (Nickel.EditIdentity.length facts)}) : Lemma (ensures member_run facts id at == member_value (Nickel.EditIdentity.first_id facts id at)) (decreases v (Nickel.EditIdentity.length facts) - v at) =
  if v at < v (Nickel.EditIdentity.length facts) then
    begin Nickel.LoopUtil.option_run_step (Nickel.EditIdentity.length facts) at () (member_next facts id) member_stop member_done;
    if not ((Rust_primitives.Slice.slice_index facts at).f_id ==? id) then
      begin member_lookup facts id (at +! mk_int 1);
      assert (member_run facts id at == member_value (Nickel.EditIdentity.first_id facts id at)) by (
        Tactics.prune "Nickel.LoopUtil.option_run";
        Tactics.prune "Core_models.Slice.impl__len";
        Tactics.prune "Rust_primitives.Slice.slice_index";
        Tactics.smt_sync' 1 1
      ) end
    else
      begin assert (member_run facts id at == member_value (Nickel.EditIdentity.first_id facts id at)) by (
        Tactics.prune "Nickel.LoopUtil.option_run";
        Tactics.prune "Core_models.Slice.impl__len";
        Tactics.prune "Rust_primitives.Slice.slice_index";
        Tactics.smt_sync' 1 1
      ) end end
  else
    begin Nickel.LoopUtil.option_run_end (Nickel.EditIdentity.length facts) at () (member_next facts id) member_stop member_done;
    assert (member_run facts id at == member_value (Nickel.EditIdentity.first_id facts id at)) by (
      Tactics.prune "Nickel.LoopUtil.option_run";
      Tactics.prune "Core_models.Slice.impl__len";
      Tactics.prune "Rust_primitives.Slice.slice_index";
      Tactics.smt_sync' 1 1
    ) end

let membership_exact (facts: t_Slice Native.t_Fact) (id: Native.t_EventId) : Lemma (ensures Native.has_fact facts id == member_value (Nickel.EditIdentity.first_id facts id (mk_usize 0))) =
  Nickel.LoopUtil.option_interpret_any (mk_usize 0) (Nickel.EditIdentity.length facts) (member_next facts id) member_stop member_done;
  member_lookup facts id (mk_usize 0);
  assert (Native.has_fact facts id == member_value (Nickel.EditIdentity.first_id facts id (mk_usize 0))) by (
    Tactics.prune "Nickel.LoopUtil.option_run";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Core_models.Slice.impl__len";
    Tactics.prune "Rust_primitives.Slice.slice_index";
    Tactics.smt_sync' 1 1
  )

let membership_absent (facts: t_Slice Native.t_Fact) (id: Native.t_EventId) : Lemma (requires Native.has_fact facts id == false) (ensures Nickel.EditIdentity.prefix_absent facts id (mk_usize 0) (Nickel.EditIdentity.length facts)) =
  membership_exact facts id;
  Nickel.EditIdentity.lookup_none facts id (mk_usize 0)

let choice_safe (facts: t_Slice Native.t_Fact) (out: t_Slice Native.t_Fact) (choice: Option.t_Option usize) : Type0 =
  match choice with | Option.Option_None -> begin Prims.l_True end | Option.Option_Some i -> begin if v i < v (Nickel.EditIdentity.length facts) then
    begin Native.has_fact out (Rust_primitives.Slice.slice_index facts i).f_id == false end
  else
    begin Prims.l_False end end

let choice_invariant (facts: t_Slice Native.t_Fact) (out: t_Slice Native.t_Fact) : nat -> Option.t_Option usize -> Type0 =
  fun _ choice -> choice_safe facts out choice

let choice_post (facts: t_Slice Native.t_Fact) (out: t_Slice Native.t_Fact) : Option.t_Option usize -> Type0 =
  fun choice -> choice_safe facts out choice

let choice_returned (facts: t_Slice Native.t_Fact) (out: t_Slice Native.t_Fact) : Result.t_Result (Option.t_Option usize) Native.t_Error -> Type0 =
  fun result -> match result with | Result.Result_Err _ -> begin Prims.l_True end | Result.Result_Ok choice -> begin choice_safe facts out choice end

let selected_id_is_unseen (facts: t_Slice Native.t_Fact) (out: t_Slice Native.t_Fact) : Lemma (ensures (choice_returned facts out) (Native.choose_unseen facts out)) =
  Nickel.EventGraphText.text_graph_policy_is_exact ();
  Nickel.EventGraphText.text_graph_callbacks_are_exact ();
  let each_membership_boolean (xs: t_Slice Native.t_Fact) (id: Native.t_EventId) : Lemma (ensures Prims.l_or (Native.has_fact xs id == true) (Native.has_fact xs id == false)) [SMTPat (Native.has_fact xs id)] = () in
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Nickel.EditIdentity.length facts) (choice_invariant facts out) (fun (choice: Option.t_Option usize) -> choice) (choice_post facts out) (fun (_: Native.t_Error) -> Prims.l_True);
  assert ((choice_returned facts out) (Native.choose_unseen facts out)) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.prune "Nickel_crdt.Edit.has_fact";
    Tactics.prune "Nickel_crdt.Event_layer.has_fact";
    Tactics.prune "Nickel.LoopUtil.step_safe";
    Tactics.prune "Nickel.LoopUtil.output_safe";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.smt_sync' 1 1
  )

let push_outcome (#item: Type0) (before: Alloc.Vec.t_Vec item Alloc.Alloc.t_Global) (fact: item) : Alloc.Vec.t_Vec item Alloc.Alloc.t_Global & Result.t_Result unit Native.t_Error =
  if v (Alloc.Vec.impl_1__len before) ==? max_usize then
    begin (before, Result.Result_Err Native.Error_Internal) end
  else
    begin (Alloc.Vec.from_seq (Seq.append (Alloc.Vec.impl_1__as_slice before) (Seq.create 1 fact)), Result.Result_Ok ()) end

let push_result_is_exact (#item: Type0) (before: Alloc.Vec.t_Vec item Alloc.Alloc.t_Global) (fact: item) : Lemma (ensures Native.push before fact == push_outcome before fact) [SMTPat (Native.push before fact)] =
  let length_value () : Lemma (ensures Alloc.Vec.impl_1__len before == mk_usize (Seq.length (Alloc.Vec.impl_1__as_slice before))) = () in
  length_value ();
  if v (Alloc.Vec.impl_1__len before) ==? max_usize then
    begin assert (Native.push before fact == push_outcome before fact) by (
      Tactics.prune "Alloc.Vec.from_seq";
      Tactics.prune "Alloc.Vec.impl_1__as_slice";
      Tactics.prune "Alloc.Vec.impl_1__len";
      Tactics.prune "Core_models.Slice.impl__len";
      Tactics.prune "Rust_primitives.Slice.slice_index";
      Tactics.prune "Alloc.Vec.impl__new";
      Tactics.smt_sync' 1 1
    ) end
  else
    begin Nickel.Vector.vector_from_seq_value (Seq.append (Alloc.Vec.impl_1__as_slice before) (Seq.create 1 fact));
    assert (Native.push before fact == push_outcome before fact) by (
      Tactics.prune "Alloc.Vec.from_seq";
      Tactics.prune "Alloc.Vec.impl_1__as_slice";
      Tactics.prune "Alloc.Vec.impl_1__len";
      Tactics.prune "Core_models.Slice.impl__len";
      Tactics.prune "Rust_primitives.Slice.slice_index";
      Tactics.prune "Alloc.Vec.impl__new";
      Tactics.smt_sync' 1 1
    ) end

let push_result_unique (outcome: facts_vec & Result.t_Result unit Native.t_Error) : Type0 =
  match outcome with | (next, Result.Result_Ok _) -> begin ids_unique next end | _ -> begin Prims.l_True end

let append_fresh_preserves_unique (facts: facts_vec) (fact: Native.t_Fact) : Lemma (requires (ids_unique facts /\ Native.has_fact (Alloc.Vec.impl_1__as_slice facts) fact.f_id == false)) (ensures push_result_unique (Native.push facts fact)) =
  membership_absent (Alloc.Vec.impl_1__as_slice facts) fact.f_id;
  assert (push_result_unique (Native.push facts fact)) by (
    Tactics.prune "Nickel_crdt.Edit.push";
    Tactics.prune "Nickel_crdt.Event_layer.push";
    Tactics.prune "Alloc.Vec.impl_1__as_slice";
    Tactics.prune "Alloc.Vec.from_seq";
    Tactics.prune "Alloc.Vec.impl_1__len";
    Tactics.prune "Core_models.Slice.impl__len";
    Tactics.prune "Rust_primitives.Slice.slice_index";
    Tactics.smt_sync' 1 1
  )

let unique_invariant (at: nat) (facts: facts_vec) : Type0 =
  ids_unique facts

let canonical_result_unique (result: Result.t_Result facts_vec Native.t_Error) : Type0 =
  match result with | Result.Result_Ok facts -> begin ids_unique facts end | _ -> begin Prims.l_True end

let selected_fact_keeps_id (fact: Native.t_Fact) : Lemma (ensures (Native.clone_selected_fact fact).f_id == fact.f_id) =
  ()

let canonical_step_preserves_unique (facts: t_Slice Native.t_Fact) (out: facts_vec) : Lemma (requires ids_unique out) (ensures canonical_result_unique (Native.canonical_step facts out)) =
  selected_id_is_unseen facts (Alloc.Vec.impl_1__as_slice out);
  match Native.choose_unseen facts (Alloc.Vec.impl_1__as_slice out) with | Result.Result_Ok (Option.Option_Some i) -> begin if v i < v (Nickel.EditIdentity.length facts) then
    begin selected_fact_keeps_id (Rust_primitives.Slice.slice_index facts i);
    append_fresh_preserves_unique out (Native.clone_selected_fact (Rust_primitives.Slice.slice_index facts i)) end
  else
    begin () end end | _ -> begin () end

let empty_has_unique_ids () : Lemma (ensures ids_unique (Alloc.Vec.impl__new ())) =
  Nickel.Vector.empty_vector_contents #Native.t_Fact ();
  assert (ids_unique (Alloc.Vec.impl__new ())) by (
    Tactics.prune "Alloc.Vec.impl__new";
    Tactics.prune "Alloc.Vec.impl_1__as_slice";
    Tactics.prune "Core_models.Slice.impl__len";
    Tactics.prune "Rust_primitives.Slice.slice_index";
    Tactics.smt_sync' 1 1
  )

let canonical_loop_result (input: t_Slice Native.t_Fact) : Result.t_Result facts_vec Native.t_Error =
  let loop = Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0) (Core_models.Slice.impl__len input) (fun _ _ -> true) (((Alloc.Vec.impl__new ()) <: facts_vec)) (fun out _ -> match Native.canonical_step input out with | Result.Result_Ok next -> begin Core_models.Ops.Control_flow.ControlFlow_Continue next end | Result.Result_Err error -> begin Core_models.Ops.Control_flow.ControlFlow_Break (Core_models.Ops.Control_flow.ControlFlow_Break (Result.Result_Err error)) end) in
  match loop with | Core_models.Ops.Control_flow.ControlFlow_Break ret -> begin ret end | Core_models.Ops.Control_flow.ControlFlow_Continue out -> begin Result.Result_Ok out end

let canonical_uses_complete_range (input: t_Slice Native.t_Fact) : Lemma (ensures Native.canonical input == canonical_loop_result input) =
  Nickel.EventGraphText.text_graph_policy_is_exact ();
  Nickel.LoopEquality.pointwise_callbacks_any #facts_vec #(Result.t_Result facts_vec Native.t_Error) (mk_usize 0) (Core_models.Slice.impl__len input);
  assert (Native.canonical input == canonical_loop_result input) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.prune "Nickel_crdt.Edit.canonical_step";
    Tactics.prune "Nickel_crdt.Event_layer.canonical_step";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.smt_sync' 1 1
  )

let canonical_has_unique_ids (facts: t_Slice Native.t_Fact) : Lemma (ensures canonical_result_unique (Native.canonical facts)) =
  canonical_uses_complete_range facts;
  Nickel.Vector.empty_vector_value #Native.t_Fact ();
  let each_step (out: facts_vec) : Lemma (requires ids_unique out) (ensures canonical_result_unique (Native.canonical_step facts out)) [SMTPat (Native.canonical_step facts out)] =
    canonical_step_preserves_unique facts out;
    assert (canonical_result_unique (Native.canonical_step facts out)) by (
      Tactics.prune "Nickel_crdt.Edit.canonical_step";
      Tactics.prune "Nickel_crdt.Event_layer.canonical_step";
      Tactics.smt_sync' 1 1
    ) in
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Nickel.EditIdentity.length facts) unique_invariant (fun (out: facts_vec) -> out) ids_unique (fun (_: Native.t_Error) -> Prims.l_True);
  assert (canonical_result_unique (Native.canonical facts)) by (
    Tactics.prune "Nickel_crdt.Edit.canonical";
    Tactics.prune "Nickel_crdt.Event_layer.canonical";
    Tactics.prune "Alloc.Vec.impl__new";
    Tactics.prune "Nickel_crdt.Edit.canonical_step";
    Tactics.prune "Nickel_crdt.Event_layer.canonical_step";
    Tactics.prune "Nickel.LoopUtil.step_safe";
    Tactics.prune "Nickel.LoopUtil.output_safe";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.smt_sync' 1 1
  )

let tree_installation_installs_tree (state: Native.t_Replica) (tree: Native.t_Tree) : Lemma (ensures (Native.impl_Replica__with_tree state tree).f_tree == tree) =
  ()

let tree_installation_preserves_facts (state: Native.t_Replica) (tree: Native.t_Tree) : Lemma (ensures (Native.impl_Replica__with_tree state tree).f_facts == state.f_facts) =
  ()

let candidate_facts (before: Native.t_Replica) (fact: Native.t_Fact) : facts_vec =
  match Native.push before.f_facts fact with | (facts, _) -> begin facts end

let canonical_publication (before: Native.t_Replica) (fact: Native.t_Fact) (outcome: Result.t_Result (Option.t_Option Native.t_Replica) Native.t_Error) : Type0 =
  match outcome with | Result.Result_Ok (Option.Option_Some next) -> begin Native.canonical (Alloc.Vec.impl_1__as_slice (candidate_facts before fact)) == Result.Result_Ok next.f_facts end | _ -> begin Prims.l_True end

let result_shape (#value: Type0) (result: Result.t_Result value Native.t_Error) : Type0 =
  Prims.l_or (exists(error: Native.t_Error). result == Result.Result_Err error) (exists(out: value). result == Result.Result_Ok out)

let canonical_has_result_shape (input: t_Slice Native.t_Fact) : Lemma (ensures result_shape (Native.canonical input)) [SMTPat (Native.canonical input)] =
  ()

let interpret_has_result_shape (input: t_Slice Native.t_Fact) : Lemma (ensures result_shape (Native.interpret input)) [SMTPat (Native.interpret input)] =
  ()

let plan_publishes_canonical_facts (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (ensures canonical_publication before fact (Native.impl_Replica__plan before fact)) =
  let each_tree_facts (state: Native.t_Replica) (tree: Native.t_Tree) : Lemma (ensures (Native.impl_Replica__with_tree state tree).f_facts == state.f_facts) [SMTPat (Native.impl_Replica__with_tree state tree)] = tree_installation_preserves_facts state tree in
  assert (canonical_publication before fact (Native.impl_Replica__plan before fact)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__with_tree";
    Tactics.prune "Nickel_crdt.Edit.canonical";
    Tactics.prune "Nickel_crdt.Event_layer.canonical";
    Tactics.prune "Nickel_crdt.Edit.interpret";
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__duplicate";
    Tactics.prune "Nickel_crdt.Edit.push";
    Tactics.prune "Nickel_crdt.Event_layer.push";
    Tactics.smt_sync' 1 1
  )

let added_state_unique (outcome: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) : Type0 =
  match outcome with | (next, Result.Result_Ok Native.Admission_Added) -> begin ids_unique next.f_facts end | _ -> begin Prims.l_True end

let receive_added_ids_are_unique (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (ensures added_state_unique (Native.impl_Replica__receive before fact)) =
  plan_publishes_canonical_facts before fact;
  canonical_has_unique_ids (Alloc.Vec.impl_1__as_slice (candidate_facts before fact))

let receive_state_unique (outcome: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) : Type0 =
  match outcome with | (next, _) -> begin ids_unique next.f_facts end

let receive_preserves_unique_ids (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (requires ids_unique before.f_facts) (ensures receive_state_unique (Native.impl_Replica__receive before fact)) =
  Nickel.EditAtomic.receive_rejection_unchanged before fact;
  receive_added_ids_are_unique before fact;
  ()

let edit_state_unique (outcome: Native.t_Replica & Result.t_Result Native.t_Local Native.t_Error) : Type0 =
  match outcome with | (next, _) -> begin ids_unique next.f_facts end

let edit_preserves_unique_ids (before: Native.t_Replica) (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (delete: Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global) : Lemma (requires ids_unique before.f_facts) (ensures edit_state_unique (Native.impl_Replica__edit before gap insert delete)) =
  Nickel.EditAtomic.edit_rejection_or_empty_unchanged before gap insert delete;
  Nickel.EditCommit.authored_fact_replays_same_commit before gap insert delete;
  match Native.impl_Replica__edit before gap insert delete with | (_, Result.Result_Ok (Native.Local_Authored fact)) -> begin receive_added_ids_are_unique before fact end | _ -> begin () end;
  ()

let new_state_unique (outcome: Result.t_Result Native.t_Replica Native.t_Error) : Type0 =
  match outcome with | Result.Result_Ok state -> begin ids_unique state.f_facts end | _ -> begin Prims.l_True end

let new_establishes_unique_ids (writer: Option.t_Option Native.t_Writer) (limits: Native.t_Limits) : Lemma (ensures new_state_unique (Native.impl_Replica__new writer limits)) =
  empty_has_unique_ids ()

let selected_fact_is_exact (fact: Native.t_Fact) : Lemma (ensures Native.clone_selected_fact fact == fact) =
  ()

let fact_present (facts: t_Slice Native.t_Fact) (fact: Native.t_Fact) : Type0 =
  exists(i: nat). Prims.l_and (i < FStar.Seq.length facts) (FStar.Seq.index facts i == fact)

let selected_whole_facts (input: t_Slice Native.t_Fact) (output: facts_vec) : Type0 =
  forall(i: nat). i < FStar.Seq.length (Alloc.Vec.impl_1__as_slice output) ==> fact_present input (FStar.Seq.index (Alloc.Vec.impl_1__as_slice output) i)

let content_invariant (input: t_Slice Native.t_Fact) (at: nat) (out: facts_vec) : Type0 =
  Prims.l_and (v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice out)) == at) (selected_whole_facts input out)

let content_step_result (input: t_Slice Native.t_Fact) (at: nat) (result: Result.t_Result facts_vec Native.t_Error) : Type0 =
  match result with | Result.Result_Ok out -> begin content_invariant input (at + 1) out end | _ -> begin Prims.l_True end

let append_content_result (input: t_Slice Native.t_Fact) (out: facts_vec) (outcome: facts_vec & Result.t_Result unit Native.t_Error) : Type0 =
  match outcome with | (next, Result.Result_Ok _) -> begin content_invariant input (v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice out)) + 1) next end | _ -> begin Prims.l_True end

let append_whole_fact (input: t_Slice Native.t_Fact) (out: facts_vec) (fact: Native.t_Fact) : Lemma (requires (selected_whole_facts input out /\ fact_present input fact)) (ensures append_content_result input out (Native.push out fact)) =
  assert (append_content_result input out (Native.push out fact)) by (
    Tactics.prune "Nickel_crdt.Edit.push";
    Tactics.prune "Nickel_crdt.Event_layer.push";
    Tactics.prune "Alloc.Vec.impl_1__as_slice";
    Tactics.prune "Alloc.Vec.from_seq";
    Tactics.prune "Alloc.Vec.impl_1__len";
    Tactics.prune "Core_models.Slice.impl__len";
    Tactics.prune "Rust_primitives.Slice.slice_index";
    Tactics.smt_sync' 1 1
  )

let canonical_step_selects_whole_facts (input: t_Slice Native.t_Fact) (out: facts_vec) (at: nat) : Lemma (requires content_invariant input at out) (ensures content_step_result input at (Native.canonical_step input out)) =
  match Native.choose_unseen input (Alloc.Vec.impl_1__as_slice out) with | Result.Result_Ok (Option.Option_Some i) -> begin if v i < v (Nickel.EditIdentity.length input) then
    begin selected_fact_is_exact (Rust_primitives.Slice.slice_index input i);
    assert (fact_present input (Rust_primitives.Slice.slice_index input i));
    append_whole_fact input out (Rust_primitives.Slice.slice_index input i) end
  else
    begin () end end | _ -> begin () end

let canonical_content_result (input: t_Slice Native.t_Fact) (result: Result.t_Result facts_vec Native.t_Error) : Type0 =
  match result with | Result.Result_Ok out -> begin content_invariant input (v (Nickel.EditIdentity.length input)) out end | _ -> begin Prims.l_True end

let canonical_selects_whole_facts (input: t_Slice Native.t_Fact) : Lemma (ensures canonical_content_result input (Native.canonical input)) =
  canonical_uses_complete_range input;
  Nickel.Vector.empty_vector_value #Native.t_Fact ();
  let each_content_step (out: facts_vec) : Lemma (requires selected_whole_facts input out) (ensures content_step_result input (v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice out))) (Native.canonical_step input out)) [SMTPat (Native.canonical_step input out)] =
    canonical_step_selects_whole_facts input out (v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice out)));
    assert (content_step_result input (v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice out))) (Native.canonical_step input out)) by (
      Tactics.prune "Nickel_crdt.Edit.canonical_step";
      Tactics.prune "Nickel_crdt.Event_layer.canonical_step";
      Tactics.smt_sync' 1 1
    ) in
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Nickel.EditIdentity.length input) (content_invariant input) (fun (out: facts_vec) -> out) (content_invariant input (v (Nickel.EditIdentity.length input))) (fun (_: Native.t_Error) -> Prims.l_True);
  assert (canonical_content_result input (Native.canonical input)) by (
    Tactics.prune "Nickel_crdt.Edit.canonical";
    Tactics.prune "Nickel_crdt.Event_layer.canonical";
    Tactics.prune "Alloc.Vec.impl__new";
    Tactics.prune "Nickel_crdt.Edit.canonical_step";
    Tactics.prune "Nickel_crdt.Event_layer.canonical_step";
    Tactics.prune "Nickel.LoopUtil.step_safe";
    Tactics.prune "Nickel.LoopUtil.output_safe";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.smt_sync' 1 1
  )

open FStar.Classical

open FStar.Fin

type fact_position (input: t_Slice Native.t_Fact) (fact: Native.t_Fact) = i: nat{Prims.l_and (i < Seq.length input) (Seq.index input i == fact)}

let find_fact_position (input: t_Slice Native.t_Fact) (fact: Native.t_Fact{fact_present input fact}) : fact_position input fact =
  match FStar.Fin.find input (fun old -> old ==? fact) 0 with | Some i -> begin i end | None -> begin 0 end

let squeezed_position (input: t_Slice Native.t_Fact{Seq.length input > 1}) (out: facts_vec{selected_whole_facts input out}) (missing: nat{Prims.l_and (missing < Seq.length input) (Prims.l_not (fact_present (Alloc.Vec.impl_1__as_slice out) (Seq.index input missing)))}) (at: nat{at < Seq.length (Alloc.Vec.impl_1__as_slice out)}) : FStar.Fin.under (Seq.length input - 1) =
  let position = find_fact_position input (Seq.index (Alloc.Vec.impl_1__as_slice out) at) in
  if position < missing then
    begin position end
  else
    begin position - 1 end

let squeezed_equal_facts (input: t_Slice Native.t_Fact{Seq.length input > 1}) (out: facts_vec{selected_whole_facts input out}) (missing: nat{Prims.l_and (missing < Seq.length input) (Prims.l_not (fact_present (Alloc.Vec.impl_1__as_slice out) (Seq.index input missing)))}) (i: nat{i < Seq.length (Alloc.Vec.impl_1__as_slice out)}) (j: nat{j < Seq.length (Alloc.Vec.impl_1__as_slice out)}) : Lemma (requires squeezed_position input out missing i == squeezed_position input out missing j) (ensures Seq.index (Alloc.Vec.impl_1__as_slice out) i == Seq.index (Alloc.Vec.impl_1__as_slice out) j) =
  ()

let unique_positions (out: facts_vec) (i: usize{v i < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice out))}) (j: usize{v j < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice out))}) : Lemma (requires (ids_unique out /\ (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice out) i).f_id == (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice out) j).f_id)) (ensures i == j) =
  ()

let unique_nat_positions (out: facts_vec) (i: nat{i < Seq.length (Alloc.Vec.impl_1__as_slice out)}) (j: nat{j < Seq.length (Alloc.Vec.impl_1__as_slice out)}) : Lemma (requires (ids_unique out /\ Seq.index (Alloc.Vec.impl_1__as_slice out) i == Seq.index (Alloc.Vec.impl_1__as_slice out) j)) (ensures i == j) =
  unique_positions out (mk_usize i) (mk_usize j)

let whole_selection_covers (input: t_Slice Native.t_Fact) (out: facts_vec) : Lemma (requires (content_invariant input (v (Nickel.EditIdentity.length input)) out /\ ids_unique out)) (ensures forall(at: nat{at < Seq.length input}). fact_present (Alloc.Vec.impl_1__as_slice out) (Seq.index input at)) =
  let no_missing (at: nat{at < Seq.length input}) : Lemma (requires Prims.l_not (fact_present (Alloc.Vec.impl_1__as_slice out) (Seq.index input at))) (ensures Prims.l_False) [SMTPat (fact_present (Alloc.Vec.impl_1__as_slice out) (Seq.index input at))] = if Seq.length input > 1 then
    begin let positions = Seq.init (Seq.length input) (squeezed_position input out at) in
    Seq.lemma_init_len (Seq.length input) (squeezed_position input out at);
    Seq.init_index (Seq.length input) (squeezed_position input out at);
    match FStar.Fin.pigeonhole positions with | (i, j) -> begin assert (i < j);
    assert (squeezed_position input out at i == squeezed_position input out at j);
    squeezed_equal_facts input out at i j;
    unique_nat_positions out i j end end
  else
    begin assert (Seq.length input == 1);
    assert (fact_present input (Seq.index (Alloc.Vec.impl_1__as_slice out) 0));
    assert (Seq.index (Alloc.Vec.impl_1__as_slice out) 0 == Seq.index input at);
    assert (fact_present (Alloc.Vec.impl_1__as_slice out) (Seq.index input at)) end in
  ()

let same_fact_contents (input: t_Slice Native.t_Fact) (out: facts_vec) : Type0 =
  forall(fact: Native.t_Fact). fact_present input fact <==> fact_present (Alloc.Vec.impl_1__as_slice out) fact

let canonical_exact_result (input: t_Slice Native.t_Fact) (result: Result.t_Result facts_vec Native.t_Error) : Type0 =
  match result with | Result.Result_Ok out -> begin Prims.l_and (same_fact_contents input out) (v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice out)) == v (Nickel.EditIdentity.length input)) end | _ -> begin Prims.l_True end

let canonical_preserves_exact_contents (input: t_Slice Native.t_Fact) : Lemma (ensures canonical_exact_result input (Native.canonical input)) =
  canonical_selects_whole_facts input;
  canonical_has_unique_ids input;
  match Native.canonical input with | Result.Result_Ok out -> begin whole_selection_covers input out end | _ -> begin () end;
  ()

let appended_contents (before: facts_vec) (fact: Native.t_Fact) (next: facts_vec) : Type0 =
  Prims.l_and (v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice next)) == v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice before)) + 1) (forall(item: Native.t_Fact). fact_present (Alloc.Vec.impl_1__as_slice next) item <==> Prims.l_or (fact_present (Alloc.Vec.impl_1__as_slice before) item) (item == fact))

let push_exact_result (before: facts_vec) (fact: Native.t_Fact) (outcome: facts_vec & Result.t_Result unit Native.t_Error) : Type0 =
  match outcome with | (next, Result.Result_Ok _) -> begin appended_contents before fact next end | _ -> begin Prims.l_True end

let push_has_exact_contents (before: facts_vec) (fact: Native.t_Fact) : Lemma (ensures push_exact_result before fact (Native.push before fact)) =
  assert (push_exact_result before fact (Native.push before fact)) by (
    Tactics.prune "Nickel_crdt.Edit.push";
    Tactics.prune "Nickel_crdt.Event_layer.push";
    Tactics.prune "Alloc.Vec.impl_1__as_slice";
    Tactics.prune "Alloc.Vec.from_seq";
    Tactics.prune "Alloc.Vec.impl_1__len";
    Tactics.prune "Core_models.Slice.impl__len";
    Tactics.prune "Rust_primitives.Slice.slice_index";
    Tactics.smt_sync' 1 1
  )

let plan_push_succeeded (before: Native.t_Replica) (fact: Native.t_Fact) (outcome: Result.t_Result (Option.t_Option Native.t_Replica) Native.t_Error) : Type0 =
  match outcome with | Result.Result_Ok (Option.Option_Some _) -> begin match Native.push before.f_facts fact with | (_, result) -> begin result == Result.Result_Ok () end end | _ -> begin Prims.l_True end

let successful_plan_pushed_fact (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (ensures plan_push_succeeded before fact (Native.impl_Replica__plan before fact)) =
  ()

let plan_exact_contents (before: Native.t_Replica) (fact: Native.t_Fact) (outcome: Result.t_Result (Option.t_Option Native.t_Replica) Native.t_Error) : Type0 =
  match outcome with | Result.Result_Ok (Option.Option_Some next) -> begin appended_contents before.f_facts fact next.f_facts end | _ -> begin Prims.l_True end

let successful_plan_has_exact_contents (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (ensures plan_exact_contents before fact (Native.impl_Replica__plan before fact)) =
  successful_plan_pushed_fact before fact;
  push_has_exact_contents before.f_facts fact;
  plan_publishes_canonical_facts before fact;
  canonical_preserves_exact_contents (Alloc.Vec.impl_1__as_slice (candidate_facts before fact));
  ()

let added_exact_contents (before: Native.t_Replica) (fact: Native.t_Fact) (outcome: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) : Type0 =
  match outcome with | (next, Result.Result_Ok Native.Admission_Added) -> begin appended_contents before.f_facts fact next.f_facts end | _ -> begin Prims.l_True end

let receive_added_has_exact_contents (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (ensures added_exact_contents before fact (Native.impl_Replica__receive before fact)) =
  successful_plan_has_exact_contents before fact

let authored_exact_contents (before: Native.t_Replica) (outcome: Native.t_Replica & Result.t_Result Native.t_Local Native.t_Error) : Type0 =
  match outcome with | (next, Result.Result_Ok (Native.Local_Authored fact)) -> begin appended_contents before.f_facts fact next.f_facts end | _ -> begin Prims.l_True end

let edit_authored_has_exact_contents (before: Native.t_Replica) (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (delete: Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global) : Lemma (ensures authored_exact_contents before (Native.impl_Replica__edit before gap insert delete)) =
  Nickel.EditCommit.authored_fact_replays_same_commit before gap insert delete;
  match Native.impl_Replica__edit before gap insert delete with | (_, Result.Result_Ok (Native.Local_Authored fact)) -> begin receive_added_has_exact_contents before fact end | _ -> begin () end;
  ()

let event_key (id: Native.t_EventId) : nat =
  let rank = match id.f_writer with | Native.Writer_Alice -> begin 0 end | Native.Writer_Bo -> begin 18446744073709551616 end in
  rank + v id.f_counter

let event_order_is_key_order (a: Native.t_EventId) (b: Native.t_EventId) : Lemma (ensures Native.event_lt a b == true <==> event_key a < event_key b) =
  assert (Native.event_lt a b == true <==> event_key a < event_key b) by (
    Tactics.prune "Nickel_crdt.Edit.writer_index";
    Tactics.smt_sync' 1 1
  )

let least_choice (input: t_Slice Native.t_Fact) (out: t_Slice Native.t_Fact) (at: nat) (choice: Option.t_Option usize) : Type0 =
  match choice with | Option.Option_None -> begin forall(j: usize{v j < v (Nickel.EditIdentity.length input)}). v j < at ==> Native.has_fact out (Rust_primitives.Slice.slice_index input j).f_id end | Option.Option_Some k -> begin Prims.l_and (Prims.l_and (v k < v (Nickel.EditIdentity.length input)) (Native.has_fact out (Rust_primitives.Slice.slice_index input k).f_id == false)) (forall(j: usize{v j < v (Nickel.EditIdentity.length input)}). Prims.l_and (v j < at) (Native.has_fact out (Rust_primitives.Slice.slice_index input j).f_id == false) ==> event_key (Rust_primitives.Slice.slice_index input k).f_id <= event_key (Rust_primitives.Slice.slice_index input j).f_id) end

let least_result (input: t_Slice Native.t_Fact) (out: t_Slice Native.t_Fact) (result: Result.t_Result (Option.t_Option usize) Native.t_Error) : Type0 =
  match result with | Result.Result_Ok choice -> begin least_choice input out (v (Nickel.EditIdentity.length input)) choice end | _ -> begin Prims.l_True end

let least_next (input: t_Slice Native.t_Fact) (out: t_Slice Native.t_Fact) (j: usize{v j < v (Nickel.EditIdentity.length input)}) (choice: Option.t_Option usize) : Option.t_Option usize =
  if Native.has_fact out (Rust_primitives.Slice.slice_index input j).f_id then
    begin choice end
  else
    begin match choice with | Option.Option_None -> begin Option.Option_Some j end | Option.Option_Some k -> begin if v k < v (Nickel.EditIdentity.length input) && event_key (Rust_primitives.Slice.slice_index input j).f_id < event_key (Rust_primitives.Slice.slice_index input k).f_id then
      begin Option.Option_Some j end
    else
      begin choice end end end

let least_extends_all (input: t_Slice Native.t_Fact) (out: t_Slice Native.t_Fact) : Lemma (ensures forall(j: usize{v j < v (Nickel.EditIdentity.length input)}) (choice: Option.t_Option usize). least_choice input out (v j) choice ==> least_choice input out (v j + 1) (least_next input out j choice)) =
  let each (j: usize{v j < v (Nickel.EditIdentity.length input)}) (choice: Option.t_Option usize) : Lemma (ensures least_choice input out (v j) choice ==> least_choice input out (v j + 1) (least_next input out j choice)) = () in
  FStar.Classical.forall_intro_2 each

let selected_id_is_least (input: t_Slice Native.t_Fact) (out: t_Slice Native.t_Fact) : Lemma (ensures least_result input out (Native.choose_unseen input out)) =
  Nickel.EventGraphText.text_graph_policy_is_exact ();
  Nickel.EventGraphText.text_graph_callbacks_are_exact ();
  let each_order (a: Native.t_EventId) (b: Native.t_EventId) : Lemma (ensures Native.event_lt a b == true <==> event_key a < event_key b) [SMTPat (Native.event_lt a b)] = event_order_is_key_order a b in
  least_extends_all input out;
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Nickel.EditIdentity.length input) (least_choice input out) (fun (choice: Option.t_Option usize) -> choice) (least_choice input out (v (Nickel.EditIdentity.length input))) (fun (_: Native.t_Error) -> Prims.l_True);
  assert (least_result input out (Native.choose_unseen input out)) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.prune "Nickel.LoopUtil.step_safe";
    Tactics.prune "Nickel.LoopUtil.output_safe";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel_crdt.Edit.has_fact";
    Tactics.prune "Nickel_crdt.Event_layer.has_fact";
    Tactics.prune "Nickel_crdt.Edit.event_lt";
    Tactics.smt_sync' 1 1
  )

let rec absent_lookup (input: t_Slice Native.t_Fact) (id: Native.t_EventId) (at: usize{v at <= v (Nickel.EditIdentity.length input)}) : Lemma (requires Nickel.EditIdentity.prefix_absent input id at (Nickel.EditIdentity.length input)) (ensures Nickel.EditIdentity.first_id input id at == Option.Option_None) (decreases v (Nickel.EditIdentity.length input) - v at) =
  if v at < v (Nickel.EditIdentity.length input) then
    begin absent_lookup input id (at +! mk_int 1) end
  else
    begin () end

let membership_absence_exact (input: t_Slice Native.t_Fact) (id: Native.t_EventId) : Lemma (ensures Native.has_fact input id == false <==> Nickel.EditIdentity.prefix_absent input id (mk_usize 0) (Nickel.EditIdentity.length input)) =
  let reverse (dummy: unit) : Lemma (requires Nickel.EditIdentity.prefix_absent input id (mk_usize 0) (Nickel.EditIdentity.length input)) (ensures Native.has_fact input id == false) =
    membership_exact input id;
    absent_lookup input id (mk_usize 0);
    assert (Native.has_fact input id == false) by (
      Tactics.prune "Nickel_crdt.Edit.has_fact";
      Tactics.prune "Nickel_crdt.Event_layer.has_fact";
      Tactics.prune "Core_models.Slice.impl__len";
      Tactics.prune "Rust_primitives.Slice.slice_index";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.move_requires reverse ();
  if Native.has_fact input id then
    begin assert (Native.has_fact input id == false <==> Nickel.EditIdentity.prefix_absent input id (mk_usize 0) (Nickel.EditIdentity.length input)) by (
      Tactics.prune "Nickel_crdt.Edit.has_fact";
      Tactics.prune "Nickel_crdt.Event_layer.has_fact";
      Tactics.prune "Core_models.Slice.impl__len";
      Tactics.prune "Rust_primitives.Slice.slice_index";
      Tactics.smt_sync' 1 1
    ) end
  else
    begin membership_absent input id;
    assert (Native.has_fact input id == false <==> Nickel.EditIdentity.prefix_absent input id (mk_usize 0) (Nickel.EditIdentity.length input)) by (
      Tactics.prune "Nickel_crdt.Edit.has_fact";
      Tactics.prune "Nickel_crdt.Event_layer.has_fact";
      Tactics.prune "Core_models.Slice.impl__len";
      Tactics.prune "Rust_primitives.Slice.slice_index";
      Tactics.smt_sync' 1 1
    ) end

let facts_ordered (facts: facts_vec) : Type0 =
  forall(i: usize{v i < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice facts))}) (j: usize{v j < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice facts))}). v i < v j ==> event_key (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice facts) i).f_id <= event_key (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice facts) j).f_id

let order_frontier (input: t_Slice Native.t_Fact) (out: facts_vec) : Type0 =
  Prims.l_and (facts_ordered out) (forall(i: usize{v i < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice out))}) (j: usize{v j < v (Nickel.EditIdentity.length input)}). Native.has_fact (Alloc.Vec.impl_1__as_slice out) (Rust_primitives.Slice.slice_index input j).f_id == false ==> event_key (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice out) i).f_id <= event_key (Rust_primitives.Slice.slice_index input j).f_id)

let ordered_push_result (input: t_Slice Native.t_Fact) (result: facts_vec & Result.t_Result unit Native.t_Error) : Type0 =
  match result with | (next, Result.Result_Ok _) -> begin order_frontier input next end | _ -> begin Prims.l_True end

let absent_after_push (out: facts_vec) (fact: Native.t_Fact) (id: Native.t_EventId) (result: facts_vec & Result.t_Result unit Native.t_Error) : Type0 =
  match result with | (next, Result.Result_Ok _) -> begin Native.has_fact (Alloc.Vec.impl_1__as_slice next) id == false <==> Prims.l_and (Native.has_fact (Alloc.Vec.impl_1__as_slice out) id == false) (Prims.l_not (fact.f_id == id)) end | _ -> begin Prims.l_True end

let push_membership (out: facts_vec) (fact: Native.t_Fact) (id: Native.t_EventId) : Lemma (ensures absent_after_push out fact id (Native.push out fact)) =
  membership_absence_exact (Alloc.Vec.impl_1__as_slice out) id;
  match Native.push out fact with | (next, Result.Result_Ok _) -> begin membership_absence_exact (Alloc.Vec.impl_1__as_slice next) id;
  assert (absent_after_push out fact id (Native.push out fact)) by (
    Tactics.prune "Nickel_crdt.Edit.push";
    Tactics.prune "Nickel_crdt.Event_layer.push";
    Tactics.prune "Alloc.Vec.impl_1__as_slice";
    Tactics.prune "Alloc.Vec.from_seq";
    Tactics.prune "Alloc.Vec.impl_1__len";
    Tactics.prune "Core_models.Slice.impl__len";
    Tactics.prune "Rust_primitives.Slice.slice_index";
    Tactics.smt_sync' 1 1
  ) end | _ -> begin () end

let frontier_bounds_unseen (input: t_Slice Native.t_Fact) (out: facts_vec) (i: usize{v i < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice out))}) (k: usize{v k < v (Nickel.EditIdentity.length input)}) : Lemma (requires (order_frontier input out /\ Native.has_fact (Alloc.Vec.impl_1__as_slice out) (Rust_primitives.Slice.slice_index input k).f_id == false)) (ensures event_key (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice out) i).f_id <= event_key (Rust_primitives.Slice.slice_index input k).f_id) =
  ()

let append_least_preserves_frontier (input: t_Slice Native.t_Fact) (out: facts_vec) (k: usize{v k < v (Nickel.EditIdentity.length input)}) : Lemma (requires (order_frontier input out /\ least_choice input (Alloc.Vec.impl_1__as_slice out) (v (Nickel.EditIdentity.length input)) (Option.Option_Some k))) (ensures ordered_push_result input (Native.push out (Rust_primitives.Slice.slice_index input k))) =
  let fact = Rust_primitives.Slice.slice_index input k in
  match Native.push out fact with | (next, Result.Result_Ok _) -> begin let each_frontier (i: usize{v i < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice next))}) (j: usize{v j < v (Nickel.EditIdentity.length input)}) : Lemma (requires Native.has_fact (Alloc.Vec.impl_1__as_slice next) (Rust_primitives.Slice.slice_index input j).f_id == false) (ensures event_key (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice next) i).f_id <= event_key (Rust_primitives.Slice.slice_index input j).f_id) =
    push_membership out fact (Rust_primitives.Slice.slice_index input j).f_id;
    assert (Native.push out fact == (next, Result.Result_Ok ()));
    assert (Native.has_fact (Alloc.Vec.impl_1__as_slice out) (Rust_primitives.Slice.slice_index input j).f_id == false) by (
      Tactics.prune "Nickel_crdt.Edit.push";
      Tactics.prune "Nickel_crdt.Event_layer.push";
      Tactics.smt_sync' 1 1
    );
    if v i < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice out)) then
      begin assert (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice next) i == Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice out) i);
      frontier_bounds_unseen input out i j;
      assert (event_key (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice out) i).f_id <= event_key (Rust_primitives.Slice.slice_index input j).f_id) end
    else
      begin assert (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice next) i == fact);
      assert (event_key fact.f_id <= event_key (Rust_primitives.Slice.slice_index input j).f_id) end in
  let each_frontier_imp (i: usize{v i < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice next))}) (j: usize{v j < v (Nickel.EditIdentity.length input)}) : Lemma (ensures Native.has_fact (Alloc.Vec.impl_1__as_slice next) (Rust_primitives.Slice.slice_index input j).f_id == false ==> event_key (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice next) i).f_id <= event_key (Rust_primitives.Slice.slice_index input j).f_id) = FStar.Classical.move_requires_2 each_frontier i j in
  FStar.Classical.forall_intro_2 each_frontier_imp;
  let each_pair (i: usize{v i < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice next))}) (j: usize{v j < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice next))}) : Lemma (ensures v i < v j ==> event_key (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice next) i).f_id <= event_key (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice next) j).f_id) =
    assert (Alloc.Vec.impl_1__as_slice next == Seq.append (Alloc.Vec.impl_1__as_slice out) (Seq.create 1 fact)) by (
      Tactics.prune "Nickel_crdt.Edit.push";
      Tactics.prune "Nickel_crdt.Event_layer.push";
      Tactics.prune "Alloc.Vec.impl_1__as_slice";
      Tactics.prune "Alloc.Vec.from_seq";
      Tactics.prune "Alloc.Vec.impl_1__len";
      Tactics.smt_sync' 1 1
    );
    if v i < v j then
      begin assert (v i < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice out)));
      assert (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice next) i == Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice out) i);
      if v j < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice out)) then
        begin assert (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice next) j == Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice out) j);
        assert (event_key (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice out) i).f_id <= event_key (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice out) j).f_id) end
      else
        begin assert (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice next) j == fact);
        frontier_bounds_unseen input out i k;
        assert (event_key (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice out) i).f_id <= event_key fact.f_id) end end
    else
      begin () end in
  FStar.Classical.forall_intro_2 each_pair end | _ -> begin () end

let order_step_result (input: t_Slice Native.t_Fact) (result: Result.t_Result facts_vec Native.t_Error) : Type0 =
  match result with | Result.Result_Ok next -> begin order_frontier input next end | _ -> begin Prims.l_True end

let canonical_step_preserves_order (input: t_Slice Native.t_Fact) (out: facts_vec) : Lemma (requires order_frontier input out) (ensures order_step_result input (Native.canonical_step input out)) =
  selected_id_is_least input (Alloc.Vec.impl_1__as_slice out);
  match Native.choose_unseen input (Alloc.Vec.impl_1__as_slice out) with | Result.Result_Ok (Option.Option_Some k) -> begin if v k < v (Nickel.EditIdentity.length input) then
    begin selected_fact_is_exact (Rust_primitives.Slice.slice_index input k);
    append_least_preserves_frontier input out k end
  else
    begin () end end | _ -> begin () end

let order_invariant (input: t_Slice Native.t_Fact) (at: nat) (out: facts_vec) : Type0 =
  order_frontier input out

let canonical_orders_facts (input: t_Slice Native.t_Fact) : Lemma (ensures order_step_result input (Native.canonical input)) =
  canonical_uses_complete_range input;
  Nickel.Vector.empty_vector_value #Native.t_Fact ();
  let each_order_step (out: facts_vec) : Lemma (requires order_frontier input out) (ensures order_step_result input (Native.canonical_step input out)) [SMTPat (Native.canonical_step input out)] = canonical_step_preserves_order input out in
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Nickel.EditIdentity.length input) (order_invariant input) (fun (out: facts_vec) -> out) (order_frontier input) (fun (_: Native.t_Error) -> Prims.l_True);
  assert (order_step_result input (Native.canonical input)) by (
    Tactics.prune "Nickel_crdt.Edit.canonical";
    Tactics.prune "Nickel_crdt.Event_layer.canonical";
    Tactics.prune "Alloc.Vec.impl__new";
    Tactics.prune "Nickel.LoopUtil.step_safe";
    Tactics.prune "Nickel.LoopUtil.output_safe";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel_crdt.Edit.canonical_step";
    Tactics.prune "Nickel_crdt.Event_layer.canonical_step";
    Tactics.prune "Nickel_crdt.Edit.choose_unseen";
    Tactics.prune "Nickel_crdt.Event_layer.choose_unseen";
    Tactics.prune "Nickel_crdt.Edit.push";
    Tactics.prune "Nickel_crdt.Event_layer.push";
    Tactics.smt_sync' 1 1
  )

let added_ordered (outcome: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) : Type0 =
  match outcome with | (next, Result.Result_Ok Native.Admission_Added) -> begin facts_ordered next.f_facts end | _ -> begin Prims.l_True end

let receive_added_facts_are_ordered (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (ensures added_ordered (Native.impl_Replica__receive before fact)) =
  plan_publishes_canonical_facts before fact;
  canonical_orders_facts (Alloc.Vec.impl_1__as_slice (candidate_facts before fact))

let authored_ordered (outcome: Native.t_Replica & Result.t_Result Native.t_Local Native.t_Error) : Type0 =
  match outcome with | (next, Result.Result_Ok (Native.Local_Authored _)) -> begin facts_ordered next.f_facts end | _ -> begin Prims.l_True end

let authored_facts_are_ordered (before: Native.t_Replica) (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (delete: Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global) : Lemma (ensures authored_ordered (Native.impl_Replica__edit before gap insert delete)) =
  Nickel.EditCommit.authored_fact_replays_same_commit before gap insert delete;
  match Native.impl_Replica__edit before gap insert delete with | (_, Result.Result_Ok (Native.Local_Authored fact)) -> begin receive_added_facts_are_ordered before fact end | _ -> begin () end;
  ()

let receive_state_ordered (outcome: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) : Type0 =
  match outcome with | (next, _) -> begin facts_ordered next.f_facts end

let receive_preserves_fact_order (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (requires facts_ordered before.f_facts) (ensures receive_state_ordered (Native.impl_Replica__receive before fact)) =
  Nickel.EditAtomic.receive_rejection_unchanged before fact;
  receive_added_facts_are_ordered before fact;
  ()

let edit_state_ordered (outcome: Native.t_Replica & Result.t_Result Native.t_Local Native.t_Error) : Type0 =
  match outcome with | (next, _) -> begin facts_ordered next.f_facts end

let edit_preserves_fact_order (before: Native.t_Replica) (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (delete: Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global) : Lemma (requires facts_ordered before.f_facts) (ensures edit_state_ordered (Native.impl_Replica__edit before gap insert delete)) =
  Nickel.EditAtomic.edit_rejection_or_empty_unchanged before gap insert delete;
  authored_facts_are_ordered before gap insert delete;
  ()

let new_state_ordered (outcome: Result.t_Result Native.t_Replica Native.t_Error) : Type0 =
  match outcome with | Result.Result_Ok state -> begin facts_ordered state.f_facts end | _ -> begin Prims.l_True end

let new_establishes_fact_order (writer: Option.t_Option Native.t_Writer) (limits: Native.t_Limits) : Lemma (ensures new_state_ordered (Native.impl_Replica__new writer limits)) =
  Nickel.EditAtomic.new_has_empty_facts writer limits;
  assert (new_state_ordered (Native.impl_Replica__new writer limits)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__new";
    Tactics.prune "Alloc.Vec.impl_1__as_slice";
    Tactics.prune "Core_models.Slice.impl__len";
    Tactics.prune "Rust_primitives.Slice.slice_index";
    Tactics.smt_sync' 1 1
  )

let event_key_identifies_event (a: Native.t_EventId) (b: Native.t_EventId) : Lemma (requires event_key a == event_key b) (ensures a == b) =
  ()

let facts_strictly_ordered (facts: facts_vec) : Type0 =
  forall(i: usize{v i < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice facts))}) (j: usize{v j < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice facts))}). v i < v j ==> Native.event_lt (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice facts) i).f_id (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice facts) j).f_id == true

let ordered_unique_is_strict (facts: facts_vec) : Lemma (requires (ids_unique facts /\ facts_ordered facts)) (ensures facts_strictly_ordered facts) =
  let each_pair (i: usize{v i < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice facts))}) (j: usize{v j < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice facts))}) : Lemma (ensures v i < v j ==> Native.event_lt (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice facts) i).f_id (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice facts) j).f_id == true) =
    let a = (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice facts) i).f_id in
    let b = (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice facts) j).f_id in
    if v i < v j then
      begin assert (event_key a <= event_key b);
      if event_key a ==? event_key b then
        begin event_key_identifies_event a b;
        unique_positions facts i j end
      else
        begin () end;
      event_order_is_key_order a b end
    else
      begin () end in
  FStar.Classical.forall_intro_2 each_pair;
  ()

let strict_canonical_result (result: Result.t_Result facts_vec Native.t_Error) : Type0 =
  match result with | Result.Result_Ok facts -> begin facts_strictly_ordered facts end | _ -> begin Prims.l_True end

let canonical_facts_are_strictly_ordered (input: t_Slice Native.t_Fact) : Lemma (ensures strict_canonical_result (Native.canonical input)) =
  canonical_has_unique_ids input;
  canonical_orders_facts input;
  match Native.canonical input with | Result.Result_Ok out -> begin ordered_unique_is_strict out end | _ -> begin () end;
  ()

let prefix_equal (left: facts_vec) (right: facts_vec) (at: nat) : Type0 =
  forall(i: nat{Prims.l_and (i < Seq.length (Alloc.Vec.impl_1__as_slice left)) (i < Seq.length (Alloc.Vec.impl_1__as_slice right))}). i < at ==> Seq.index (Alloc.Vec.impl_1__as_slice left) i == Seq.index (Alloc.Vec.impl_1__as_slice right) i

let strict_nat_pair (facts: facts_vec) (i: nat{i < Seq.length (Alloc.Vec.impl_1__as_slice facts)}) (j: nat{j < Seq.length (Alloc.Vec.impl_1__as_slice facts)}) : Lemma (requires (facts_strictly_ordered facts /\ i < j)) (ensures event_key (Seq.index (Alloc.Vec.impl_1__as_slice facts) i).f_id < event_key (Seq.index (Alloc.Vec.impl_1__as_slice facts) j).f_id) =
  let ii = mk_usize i in
  let jj = mk_usize j in
  assert (Native.event_lt (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice facts) ii).f_id (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice facts) jj).f_id == true);
  event_order_is_key_order (Seq.index (Alloc.Vec.impl_1__as_slice facts) i).f_id (Seq.index (Alloc.Vec.impl_1__as_slice facts) j).f_id

let ordered_vectors_next (left: facts_vec) (right: facts_vec) (at: nat{Prims.l_and (at < Seq.length (Alloc.Vec.impl_1__as_slice left)) (at < Seq.length (Alloc.Vec.impl_1__as_slice right))}) : Lemma (requires (Prims.l_and (ids_unique left) (ids_unique right) /\ Prims.l_and (facts_strictly_ordered left) (facts_strictly_ordered right) /\ same_fact_contents (Alloc.Vec.impl_1__as_slice left) right /\ prefix_equal left right at)) (ensures Seq.index (Alloc.Vec.impl_1__as_slice left) at == Seq.index (Alloc.Vec.impl_1__as_slice right) at) =
  let a = Seq.index (Alloc.Vec.impl_1__as_slice left) at in
  let b = Seq.index (Alloc.Vec.impl_1__as_slice right) at in
  assert (fact_present (Alloc.Vec.impl_1__as_slice left) a);
  assert (fact_present (Alloc.Vec.impl_1__as_slice right) b);
  let j = find_fact_position (Alloc.Vec.impl_1__as_slice right) a in
  let k = find_fact_position (Alloc.Vec.impl_1__as_slice left) b in
  if j < at then
    begin unique_nat_positions left j at end
  else
    begin () end;
  if k < at then
    begin unique_nat_positions right k at end
  else
    begin () end;
  if at < j then
    begin strict_nat_pair right at j;
    if at < k then
      begin strict_nat_pair left at k end
    else
      begin assert (k == at) end;
    assert Prims.l_False end
  else
    begin assert (j == at) end

let rec ordered_vectors_prefix (left: facts_vec) (right: facts_vec) (at: nat{at <= Seq.length (Alloc.Vec.impl_1__as_slice left)}) : Lemma (requires (Seq.length (Alloc.Vec.impl_1__as_slice left) == Seq.length (Alloc.Vec.impl_1__as_slice right) /\ Prims.l_and (ids_unique left) (ids_unique right) /\ Prims.l_and (facts_strictly_ordered left) (facts_strictly_ordered right) /\ same_fact_contents (Alloc.Vec.impl_1__as_slice left) right /\ prefix_equal left right at)) (ensures prefix_equal left right (Seq.length (Alloc.Vec.impl_1__as_slice left))) (decreases Seq.length (Alloc.Vec.impl_1__as_slice left) - at) =
  if at < Seq.length (Alloc.Vec.impl_1__as_slice left) then
    begin ordered_vectors_next left right at;
    assert (prefix_equal left right (at + 1));
    ordered_vectors_prefix left right (at + 1) end
  else
    begin () end

let ordered_contents_determine_vector (left: facts_vec) (right: facts_vec) : Lemma (requires (Seq.length (Alloc.Vec.impl_1__as_slice left) == Seq.length (Alloc.Vec.impl_1__as_slice right) /\ Prims.l_and (ids_unique left) (ids_unique right) /\ Prims.l_and (facts_strictly_ordered left) (facts_strictly_ordered right) /\ same_fact_contents (Alloc.Vec.impl_1__as_slice left) right)) (ensures left == right) =
  ordered_vectors_prefix left right 0;
  Seq.lemma_eq_intro (Alloc.Vec.impl_1__as_slice left) (Alloc.Vec.impl_1__as_slice right);
  Seq.lemma_eq_elim (Alloc.Vec.impl_1__as_slice left) (Alloc.Vec.impl_1__as_slice right)

let same_input_contents_and_length (left: t_Slice Native.t_Fact) (right: t_Slice Native.t_Fact) : Type0 =
  Prims.l_and (Seq.length left == Seq.length right) (forall(fact: Native.t_Fact). fact_present left fact <==> fact_present right fact)

let canonical_agreement (left: Result.t_Result facts_vec Native.t_Error) (right: Result.t_Result facts_vec Native.t_Error) : Type0 =
  match (left, right) with | (Result.Result_Ok a, Result.Result_Ok b) -> begin a == b end | _ -> begin Prims.l_True end

let canonical_is_permutation_independent (left: t_Slice Native.t_Fact) (right: t_Slice Native.t_Fact) : Lemma (requires same_input_contents_and_length left right) (ensures canonical_agreement (Native.canonical left) (Native.canonical right)) =
  canonical_preserves_exact_contents left;
  canonical_preserves_exact_contents right;
  canonical_has_unique_ids left;
  canonical_has_unique_ids right;
  canonical_facts_are_strictly_ordered left;
  canonical_facts_are_strictly_ordered right;
  match (Native.canonical left, Native.canonical right) with | (Result.Result_Ok a, Result.Result_Ok b) -> begin ordered_contents_determine_vector a b end | _ -> begin () end;
  ()

let plan_interpretation (outcome: Result.t_Result (Option.t_Option Native.t_Replica) Native.t_Error) : Type0 =
  match outcome with | Result.Result_Ok (Option.Option_Some next) -> begin Native.interpret (Alloc.Vec.impl_1__as_slice next.f_facts) == Result.Result_Ok next.f_tree end | _ -> begin Prims.l_True end

let plan_publishes_interpretation (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (ensures plan_interpretation (Native.impl_Replica__plan before fact)) =
  let each_tree_facts (state: Native.t_Replica) (tree: Native.t_Tree) : Lemma (ensures (Native.impl_Replica__with_tree state tree).f_facts == state.f_facts) [SMTPat (Native.impl_Replica__with_tree state tree)] = tree_installation_preserves_facts state tree in
  let each_tree (state: Native.t_Replica) (tree: Native.t_Tree) : Lemma (ensures (Native.impl_Replica__with_tree state tree).f_tree == tree) [SMTPat (Native.impl_Replica__with_tree state tree)] = tree_installation_installs_tree state tree in
  assert (plan_interpretation (Native.impl_Replica__plan before fact)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__with_tree";
    Tactics.prune "Nickel_crdt.Edit.canonical";
    Tactics.prune "Nickel_crdt.Event_layer.canonical";
    Tactics.prune "Nickel_crdt.Edit.interpret";
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__duplicate";
    Tactics.prune "Nickel_crdt.Edit.push";
    Tactics.prune "Nickel_crdt.Event_layer.push";
    Tactics.smt_sync' 1 1
  )

let added_shared_agreement (left: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) (right: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) : Type0 =
  match left with | (a, Result.Result_Ok Native.Admission_Added) -> begin match right with | (b, Result.Result_Ok Native.Admission_Added) -> begin Prims.l_and (a.f_facts == b.f_facts) (a.f_tree == b.f_tree) end | _ -> begin Prims.l_True end end | _ -> begin Prims.l_True end

let receive_added_shared_state_agrees (left: Native.t_Replica) (left_fact: Native.t_Fact) (right: Native.t_Replica) (right_fact: Native.t_Fact) : Lemma (requires same_input_contents_and_length (Alloc.Vec.impl_1__as_slice (candidate_facts left left_fact)) (Alloc.Vec.impl_1__as_slice (candidate_facts right right_fact))) (ensures added_shared_agreement (Native.impl_Replica__receive left left_fact) (Native.impl_Replica__receive right right_fact)) =
  plan_publishes_canonical_facts left left_fact;
  plan_publishes_canonical_facts right right_fact;
  plan_publishes_interpretation left left_fact;
  plan_publishes_interpretation right right_fact;
  canonical_is_permutation_independent (Alloc.Vec.impl_1__as_slice (candidate_facts left left_fact)) (Alloc.Vec.impl_1__as_slice (candidate_facts right right_fact))

let choice_total (result: Result.t_Result (Option.t_Option usize) Native.t_Error) : Type0 =
  match result with | Result.Result_Ok _ -> begin Prims.l_True end | _ -> begin Prims.l_False end

let choice_bounds (input: t_Slice Native.t_Fact) (at: nat) (choice: Option.t_Option usize) : Type0 =
  match choice with | Option.Option_None -> begin Prims.l_True end | Option.Option_Some k -> begin Prims.l_and (v k < at) (v k < Seq.length input) end

let choice_always_returns (input: t_Slice Native.t_Fact) (out: t_Slice Native.t_Fact) : Lemma (ensures choice_total (Native.choose_unseen input out)) =
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Nickel.EditIdentity.length input) (choice_bounds input) (fun (choice: Option.t_Option usize) -> choice) (fun (_: Option.t_Option usize) -> Prims.l_True) (fun (_: Native.t_Error) -> Prims.l_False);
  assert (choice_total (Native.choose_unseen input out)) by (
    Tactics.prune "Nickel.LoopUtil.step_safe";
    Tactics.prune "Nickel.LoopUtil.output_safe";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.smt_sync' 1 1
  )

let find_id_position (input: t_Slice Native.t_Fact) (id: Native.t_EventId{Native.has_fact input id}) : i: nat{Prims.l_and (i < Seq.length input) ((Seq.index input i).f_id == id)} =
  membership_absence_exact input id;
  match FStar.Fin.find input (fun old -> old.f_id ==? id) 0 with | Some i -> begin i end | None -> begin 0 end

let unique_slice_nat_positions (input: t_Slice Native.t_Fact) (i: nat{i < Seq.length input}) (j: nat{j < Seq.length input}) : Lemma (requires (Nickel.EditIdentity.unique_ids input /\ (Seq.index input i).f_id == (Seq.index input j).f_id)) (ensures i == j) =
  assert ((Rust_primitives.Slice.slice_index input (mk_usize i)).f_id == (Rust_primitives.Slice.slice_index input (mk_usize j)).f_id);
  assert (mk_usize i == mk_usize j)

let mapped_id_position (input: t_Slice Native.t_Fact) (out: t_Slice Native.t_Fact{Prims.l_and (Prims.l_and (Seq.length out > 0) (Seq.length out < Seq.length input)) (forall(i: nat{i < Seq.length input}). Native.has_fact out (Seq.index input i).f_id)}) (i: nat{i < Seq.length out + 1}) : FStar.Fin.under (Seq.length out) =
  find_id_position out (Seq.index input i).f_id

let shorter_output_has_unseen (input: t_Slice Native.t_Fact) (out: t_Slice Native.t_Fact) : Lemma (requires (Nickel.EditIdentity.unique_ids input /\ Seq.length out < Seq.length input)) (ensures Prims.l_not (forall(i: nat{i < Seq.length input}). Native.has_fact out (Seq.index input i).f_id)) =
  let impossible () : Lemma (requires forall(i: nat{i < Seq.length input}). Native.has_fact out (Seq.index input i).f_id) (ensures Prims.l_False) = if Seq.length out ==? 0 then
    begin membership_absence_exact out (Seq.index input 0).f_id end
  else
    begin let position = mapped_id_position input out in
    let positions = Seq.init (Seq.length out + 1) position in
    Seq.lemma_init_len (Seq.length out + 1) position;
    Seq.init_index (Seq.length out + 1) position;
    match FStar.Fin.pigeonhole positions with | (i, j) -> begin assert (i < j);
    assert (position i == position j);
    unique_slice_nat_positions input i j end end in
  FStar.Classical.move_requires impossible ()

let canonical_total (result: Result.t_Result facts_vec Native.t_Error) : Type0 =
  match result with | Result.Result_Ok _ -> begin Prims.l_True end | _ -> begin Prims.l_False end

let canonical_step_succeeds (input: t_Slice Native.t_Fact) (out: facts_vec) : Lemma (requires (Nickel.EditIdentity.unique_ids input /\ Seq.length (Alloc.Vec.impl_1__as_slice out) < Seq.length input)) (ensures canonical_total (Native.canonical_step input out)) =
  Nickel.EventGraphText.text_graph_policy_is_exact ();
  Nickel.EventGraphText.text_graph_callbacks_are_exact ();
  choice_always_returns input (Alloc.Vec.impl_1__as_slice out);
  selected_id_is_least input (Alloc.Vec.impl_1__as_slice out);
  shorter_output_has_unseen input (Alloc.Vec.impl_1__as_slice out);
  match Native.choose_unseen input (Alloc.Vec.impl_1__as_slice out) with | Result.Result_Ok (Option.Option_Some k) -> begin assert (v k < Seq.length input);
  push_result_is_exact out (Native.clone_selected_fact (Rust_primitives.Slice.slice_index input k));
  assert (canonical_total (Native.canonical_step input out)) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.prune "Nickel_crdt.Edit.choose_unseen";
    Tactics.prune "Nickel_crdt.Event_layer.choose_unseen";
    Tactics.prune "Nickel_crdt.Edit.push";
    Tactics.prune "Nickel_crdt.Event_layer.push";
    Tactics.prune "Nickel_crdt.Edit.clone_selected_fact";
    Tactics.prune "Nickel_crdt.Edit.has_fact";
    Tactics.prune "Nickel_crdt.Event_layer.has_fact";
    Tactics.smt_sync' 1 1
  ) end | Result.Result_Ok Option.Option_None -> begin let all_seen (i: nat{i < Seq.length input}) : Lemma (ensures Native.has_fact (Alloc.Vec.impl_1__as_slice out) (Seq.index input i).f_id) [SMTPat (Native.has_fact (Alloc.Vec.impl_1__as_slice out) (Seq.index input i).f_id)] = assert (Native.has_fact (Alloc.Vec.impl_1__as_slice out) (Rust_primitives.Slice.slice_index input (mk_usize i)).f_id) in
  assert Prims.l_False end | _ -> begin () end

let progress_invariant (input: t_Slice Native.t_Fact) (at: nat) (out: facts_vec) : Type0 =
  content_invariant input at out

let canonical_succeeds_for_unique_ids (input: t_Slice Native.t_Fact) : Lemma (requires Nickel.EditIdentity.unique_ids input) (ensures canonical_total (Native.canonical input)) =
  canonical_uses_complete_range input;
  Nickel.Vector.empty_vector_value #Native.t_Fact ();
  let each_step (out: facts_vec) : Lemma (requires (Seq.length (Alloc.Vec.impl_1__as_slice out) < Seq.length input /\ selected_whole_facts input out)) (ensures Prims.l_and (canonical_total (Native.canonical_step input out)) (match Native.canonical_step input out with | Result.Result_Ok next -> begin progress_invariant input (Seq.length (Alloc.Vec.impl_1__as_slice out) + 1) next end | _ -> begin Prims.l_False end)) [SMTPat (Native.canonical_step input out)] =
    canonical_step_succeeds input out;
    canonical_step_selects_whole_facts input out (v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice out))) in
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Nickel.EditIdentity.length input) (progress_invariant input) (fun (out: facts_vec) -> out) (fun (_: facts_vec) -> Prims.l_True) (fun (_: Native.t_Error) -> Prims.l_False);
  assert (canonical_total (Native.canonical input)) by (
    Tactics.prune "Nickel_crdt.Edit.canonical";
    Tactics.prune "Nickel_crdt.Event_layer.canonical";
    Tactics.prune "Alloc.Vec.impl__new";
    Tactics.prune "Nickel.LoopUtil.step_safe";
    Tactics.prune "Nickel.LoopUtil.output_safe";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel_crdt.Edit.canonical_step";
    Tactics.prune "Nickel_crdt.Event_layer.canonical_step";
    Tactics.prune "Nickel_crdt.Edit.choose_unseen";
    Tactics.prune "Nickel_crdt.Event_layer.choose_unseen";
    Tactics.prune "Nickel_crdt.Edit.push";
    Tactics.prune "Nickel_crdt.Event_layer.push";
    Tactics.smt_sync' 1 1
  )

let total_canonical_agreement (left: Result.t_Result facts_vec Native.t_Error) (right: Result.t_Result facts_vec Native.t_Error) : Type0 =
  match left with | Result.Result_Ok a -> begin match right with | Result.Result_Ok b -> begin a == b end | _ -> begin Prims.l_False end end | _ -> begin Prims.l_False end

let unique_inputs_canonicalize_identically (left: t_Slice Native.t_Fact) (right: t_Slice Native.t_Fact) : Lemma (requires (Nickel.EditIdentity.unique_ids left /\ Nickel.EditIdentity.unique_ids right /\ same_input_contents_and_length left right)) (ensures total_canonical_agreement (Native.canonical left) (Native.canonical right)) =
  canonical_succeeds_for_unique_ids left;
  canonical_succeeds_for_unique_ids right;
  canonical_is_permutation_independent left right;
  ()