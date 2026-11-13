(* Latte generated F* view *)
module Nickel.EditWellFormed

open Nickel.Prelude

open Nickel.EventGraphText

open Rust_primitives

open Core_models

open FStar.Pervasives

open Nickel.LoopUtil

open Nickel.Vector

open Nickel.EditIdentity

module Native = Nickel_crdt.Edit

module Result = Core_models.Result

module Option = Core_models.Option

module Tactics = FStar.Tactics.V2

open Nickel.EditAccepted

open FStar.Classical

open FStar.Fin

module Seq = FStar.Seq

let unicode_scalar (scalar: u32) : Type0 =
  Prims.l_and (v scalar <= 1114111) (Prims.l_or (v scalar < 55296) (v scalar > 57343))

let scalar_prefix (scalars: t_Slice u32) (finish: nat) : Type0 =
  forall(i: usize{v i < v (Core_models.Slice.impl__len scalars)}). v i < finish ==> unicode_scalar (Rust_primitives.Slice.slice_index scalars i)

let scalars_valid (scalars: t_Slice u32) : Type0 =
  scalar_prefix scalars (v (Core_models.Slice.impl__len scalars))

let scalar_check_result (scalars: t_Slice u32) (result: Result.t_Result unit Native.t_Error) : Type0 =
  match result with | Result.Result_Ok _ -> begin scalars_valid scalars end | _ -> begin Prims.l_True end

let scalar_check_invariant (scalars: t_Slice u32) (at: nat) (state: unit) : Type0 =
  scalar_prefix scalars at

let scalar_validation_is_sound (scalars: t_Slice u32) : Lemma (ensures scalar_check_result scalars (Native.validate_scalars scalars)) =
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len scalars) (scalar_check_invariant scalars) (fun (_: unit) -> ()) (fun (_: unit) -> scalars_valid scalars) (fun (_: Native.t_Error) -> Prims.l_True);
  assert (scalar_check_result scalars (Native.validate_scalars scalars)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel.LoopUtil.step_safe";
    Tactics.prune "Nickel.LoopUtil.output_safe";
    Tactics.prune "Alloc.Vec.from_seq";
    Tactics.prune "Alloc.Vec.impl_1__as_slice";
    Tactics.prune "Alloc.Vec.impl_1__len";
    Tactics.prune "Core_models.Slice.impl__len";
    Tactics.prune "Rust_primitives.Slice.slice_index";
    Tactics.smt_sync' 1 1
  )

let valid_scalar_input_succeeds (scalars: t_Slice u32) : Lemma (requires scalars_valid scalars) (ensures Native.validate_scalars scalars == Result.Result_Ok ()) =
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len scalars) (fun (_: nat) (_: unit) -> Prims.l_True) (fun (_: unit) -> ()) (fun (_: unit) -> Prims.l_True) (fun (_: Native.t_Error) -> Prims.l_False);
  assert (Native.validate_scalars scalars == Result.Result_Ok ()) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel.LoopUtil.step_safe";
    Tactics.prune "Nickel.LoopUtil.output_safe";
    Tactics.prune "Alloc.Vec.from_seq";
    Tactics.prune "Alloc.Vec.impl_1__as_slice";
    Tactics.prune "Alloc.Vec.impl_1__len";
    Tactics.prune "Core_models.Slice.impl__len";
    Tactics.prune "Rust_primitives.Slice.slice_index";
    Tactics.smt_sync' 1 1
  )

let fact_scalars_valid (fact: Native.t_Fact) : Type0 =
  scalars_valid (Alloc.Vec.impl_1__as_slice fact.f_insert)

let validated_scalars (fact: Native.t_Fact) (result: Result.t_Result unit Native.t_Error) : Type0 =
  match result with | Result.Result_Ok _ -> begin fact_scalars_valid fact end | _ -> begin Prims.l_True end

let no_validation_success (result: Result.t_Result unit Native.t_Error) : Type0 =
  match result with | Result.Result_Err _ -> begin Prims.l_True end | _ -> begin Prims.l_False end

let successful_validation_has_valid_scalars (facts: t_Slice Native.t_Fact) (fact: Native.t_Fact) : Lemma (ensures validated_scalars fact (Native.impl_Replica__validate_new facts fact)) =
  scalar_validation_is_sound (Alloc.Vec.impl_1__as_slice fact.f_insert);
  assert (validated_scalars fact (Native.impl_Replica__validate_new facts fact)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel.LoopUtil.step_safe";
    Tactics.prune "Nickel.LoopUtil.output_safe";
    Tactics.prune "Nickel_crdt.Edit.validate_scalars";
    Tactics.prune "Alloc.Vec.from_seq";
    Tactics.prune "Alloc.Vec.impl_1__as_slice";
    Tactics.prune "Alloc.Vec.impl_1__len";
    Tactics.prune "Core_models.Slice.impl__len";
    Tactics.prune "Rust_primitives.Slice.slice_index";
    Tactics.smt_sync' 1 1
  )

let added_scalars (fact: Native.t_Fact) (outcome: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) : Type0 =
  match outcome with | (_, Result.Result_Ok Native.Admission_Added) -> begin fact_scalars_valid fact end | _ -> begin Prims.l_True end

let receive_added_fact_has_valid_scalars (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (ensures added_scalars fact (Native.impl_Replica__receive before fact)) =
  successful_validation_has_valid_scalars (Alloc.Vec.impl_1__as_slice before.f_facts) fact;
  Nickel.EditAtomic.successful_plan_requires_validation before fact;
  Nickel.EditCommit.receive_uses_plan before fact;
  assert (added_scalars fact (Native.impl_Replica__receive before fact)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__validate_new";
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__plan";
    Tactics.prune "Nickel_crdt.Event_shell.plan";
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive_into";
    Tactics.prune "Alloc.Vec.from_seq";
    Tactics.prune "Alloc.Vec.impl_1__as_slice";
    Tactics.prune "Alloc.Vec.impl_1__len";
    Tactics.prune "Core_models.Slice.impl__len";
    Tactics.prune "Rust_primitives.Slice.slice_index";
    Tactics.smt_sync' 1 1
  )

let facts_scalars_valid (facts: facts_vec) : Type0 =
  forall(fact: Native.t_Fact). fact_present (Alloc.Vec.impl_1__as_slice facts) fact ==> fact_scalars_valid fact

let receive_scalars_preserved (outcome: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) : Type0 =
  match outcome with | (next, _) -> begin facts_scalars_valid next.f_facts end

let receive_preserves_scalar_validity (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (requires facts_scalars_valid before.f_facts) (ensures receive_scalars_preserved (Native.impl_Replica__receive before fact)) =
  Nickel.EditAtomic.receive_rejection_unchanged before fact;
  receive_added_has_exact_contents before fact;
  receive_added_fact_has_valid_scalars before fact;
  match Native.impl_Replica__receive before fact with | (next, Result.Result_Ok Native.Admission_Added) -> begin assert (receive_scalars_preserved (Native.impl_Replica__receive before fact)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive_into";
    Tactics.prune "Alloc.Vec.from_seq";
    Tactics.prune "Alloc.Vec.impl_1__as_slice";
    Tactics.prune "Alloc.Vec.impl_1__len";
    Tactics.prune "Core_models.Slice.impl__len";
    Tactics.prune "Rust_primitives.Slice.slice_index";
    Tactics.smt_sync' 1 1
  ) end | _ -> begin assert (receive_scalars_preserved (Native.impl_Replica__receive before fact)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive_into";
    Tactics.prune "Alloc.Vec.from_seq";
    Tactics.prune "Alloc.Vec.impl_1__as_slice";
    Tactics.prune "Alloc.Vec.impl_1__len";
    Tactics.prune "Core_models.Slice.impl__len";
    Tactics.prune "Rust_primitives.Slice.slice_index";
    Tactics.smt_sync' 1 1
  ) end

let authored_scalars (outcome: Native.t_Replica & Result.t_Result Native.t_Local Native.t_Error) : Type0 =
  match outcome with | (_, Result.Result_Ok (Native.Local_Authored fact)) -> begin fact_scalars_valid fact end | _ -> begin Prims.l_True end

let edit_authors_only_valid_scalars (before: Native.t_Replica) (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (delete: Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global) : Lemma (ensures authored_scalars (Native.impl_Replica__edit before gap insert delete)) =
  Nickel.EditCommit.authored_fact_replays_same_commit before gap insert delete;
  match Native.impl_Replica__edit before gap insert delete with | (_, Result.Result_Ok (Native.Local_Authored fact)) -> begin receive_added_fact_has_valid_scalars before fact end | _ -> begin () end;
  assert (authored_scalars (Native.impl_Replica__edit before gap insert delete)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive_into";
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__edit";
    Tactics.prune "Alloc.Vec.from_seq";
    Tactics.prune "Alloc.Vec.impl_1__as_slice";
    Tactics.prune "Alloc.Vec.impl_1__len";
    Tactics.prune "Core_models.Slice.impl__len";
    Tactics.prune "Rust_primitives.Slice.slice_index";
    Tactics.smt_sync' 1 1
  )

let edit_scalars_preserved (outcome: Native.t_Replica & Result.t_Result Native.t_Local Native.t_Error) : Type0 =
  match outcome with | (next, _) -> begin facts_scalars_valid next.f_facts end

let edit_preserves_scalar_validity (before: Native.t_Replica) (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (delete: Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global) : Lemma (requires facts_scalars_valid before.f_facts) (ensures edit_scalars_preserved (Native.impl_Replica__edit before gap insert delete)) =
  Nickel.EditAtomic.edit_rejection_or_empty_unchanged before gap insert delete;
  edit_authored_has_exact_contents before gap insert delete;
  edit_authors_only_valid_scalars before gap insert delete;
  match Native.impl_Replica__edit before gap insert delete with | (next, Result.Result_Ok (Native.Local_Authored fact)) -> begin assert (edit_scalars_preserved (Native.impl_Replica__edit before gap insert delete)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__edit";
    Tactics.prune "Alloc.Vec.from_seq";
    Tactics.prune "Alloc.Vec.impl_1__as_slice";
    Tactics.prune "Alloc.Vec.impl_1__len";
    Tactics.prune "Core_models.Slice.impl__len";
    Tactics.prune "Rust_primitives.Slice.slice_index";
    Tactics.smt_sync' 1 1
  ) end | _ -> begin assert (edit_scalars_preserved (Native.impl_Replica__edit before gap insert delete)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__edit";
    Tactics.prune "Alloc.Vec.from_seq";
    Tactics.prune "Alloc.Vec.impl_1__as_slice";
    Tactics.prune "Alloc.Vec.impl_1__len";
    Tactics.prune "Core_models.Slice.impl__len";
    Tactics.prune "Rust_primitives.Slice.slice_index";
    Tactics.smt_sync' 1 1
  ) end

let new_scalars_valid (outcome: Result.t_Result Native.t_Replica Native.t_Error) : Type0 =
  match outcome with | Result.Result_Ok state -> begin facts_scalars_valid state.f_facts end | _ -> begin Prims.l_True end

let new_establishes_scalar_validity (writer: Option.t_Option Native.t_Writer) : Lemma (ensures new_scalars_valid (Native.impl_Replica__new writer)) =
  Nickel.EditAtomic.new_has_empty_facts writer;
  assert (new_scalars_valid (Native.impl_Replica__new writer)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__new";
    Tactics.prune "Alloc.Vec.from_seq";
    Tactics.prune "Alloc.Vec.impl_1__as_slice";
    Tactics.prune "Alloc.Vec.impl_1__len";
    Tactics.prune "Core_models.Slice.impl__len";
    Tactics.prune "Rust_primitives.Slice.slice_index";
    Tactics.smt_sync' 1 1
  )

let event_present (facts: t_Slice Native.t_Fact) (id: Native.t_EventId) : Type0 =
  Prims.l_not (Nickel.EditIdentity.prefix_absent facts id (mk_usize 0) (Nickel.EditIdentity.length facts))

let event_membership_is_presence (facts: t_Slice Native.t_Fact) (id: Native.t_EventId) : Lemma (ensures Native.has_fact facts id == true <==> event_present facts id) =
  membership_absence_exact facts id

let membership_result (facts: t_Slice Native.t_Fact) (id: Native.t_EventId) (found: bool) : Type0 =
  Prims.l_or (Prims.l_and (found == true) (event_present facts id)) (Prims.l_and (found == false) (Prims.l_not (event_present facts id)))

let membership_result_is_exact (facts: t_Slice Native.t_Fact) (id: Native.t_EventId) : Lemma (ensures membership_result facts id (Native.has_fact facts id)) [SMTPat (Native.has_fact facts id)] =
  event_membership_is_presence facts id;
  match Native.has_fact facts id with | true -> begin assert (membership_result facts id (Native.has_fact facts id)) by (
    Tactics.prune "Nickel_crdt.Edit.has_fact";
    Tactics.prune "Nickel_crdt.Event_layer.has_fact";
    Tactics.smt_sync' 1 1
  ) end | false -> begin assert (membership_result facts id (Native.has_fact facts id)) by (
    Tactics.prune "Nickel_crdt.Edit.has_fact";
    Tactics.prune "Nickel_crdt.Event_layer.has_fact";
    Tactics.smt_sync' 1 1
  ) end

let dependency_prefix (facts: t_Slice Native.t_Fact) (after: t_Slice Native.t_EventId) (finish: nat) : Type0 =
  forall(i: usize{v i < v (Core_models.Slice.impl__len after)}). v i < finish ==> event_present facts (Rust_primitives.Slice.slice_index after i)

let dependencies_present (facts: t_Slice Native.t_Fact) (after: t_Slice Native.t_EventId) : Type0 =
  dependency_prefix facts after (v (Core_models.Slice.impl__len after))

let dependency_check_result (facts: t_Slice Native.t_Fact) (after: t_Slice Native.t_EventId) (result: Result.t_Result unit Native.t_Error) : Type0 =
  match result with | Result.Result_Ok _ -> begin dependencies_present facts after end | _ -> begin Prims.l_True end

let dependency_check_invariant (facts: t_Slice Native.t_Fact) (after: t_Slice Native.t_EventId) (at: nat) (state: unit) : Type0 =
  dependency_prefix facts after at

let dependency_validation_is_sound (facts: t_Slice Native.t_Fact) (after: t_Slice Native.t_EventId) : Lemma (ensures dependency_check_result facts after (Native.validate_after facts after)) =
  Nickel.EventGraphText.text_graph_policy_is_exact ();
  Nickel.EventGraphText.text_graph_callbacks_are_exact ();
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len after) (dependency_check_invariant facts after) (fun (_: unit) -> ()) (fun (_: unit) -> dependencies_present facts after) (fun (_: Native.t_Error) -> Prims.l_True);
  assert (dependency_check_result facts after (Native.validate_after facts after)) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel.LoopUtil.step_safe";
    Tactics.prune "Nickel.LoopUtil.output_safe";
    Tactics.prune "Nickel_crdt.Edit.has_fact";
    Tactics.prune "Nickel_crdt.Event_layer.has_fact";
    Tactics.prune "Alloc.Vec.from_seq";
    Tactics.prune "Alloc.Vec.impl_1__as_slice";
    Tactics.prune "Alloc.Vec.impl_1__len";
    Tactics.prune "Core_models.Slice.impl__len";
    Tactics.prune "Rust_primitives.Slice.slice_index";
    Tactics.smt_sync' 1 1
  )

let present_dependencies_pass_guard (facts: t_Slice Native.t_Fact) (after: t_Slice Native.t_EventId) : Lemma (requires dependencies_present facts after) (ensures Native.validate_after facts after == Result.Result_Ok ()) =
  Nickel.EventGraphText.text_graph_policy_is_exact ();
  Nickel.EventGraphText.text_graph_callbacks_are_exact ();
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len after) (fun (_: nat) (_: unit) -> Prims.l_True) (fun (_: unit) -> ()) (fun (_: unit) -> Prims.l_True) (fun (_: Native.t_Error) -> Prims.l_False);
  assert (Native.validate_after facts after == Result.Result_Ok ()) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel.LoopUtil.step_safe";
    Tactics.prune "Nickel.LoopUtil.output_safe";
    Tactics.prune "Nickel_crdt.Edit.has_fact";
    Tactics.prune "Nickel_crdt.Event_layer.has_fact";
    Tactics.prune "Alloc.Vec.from_seq";
    Tactics.prune "Alloc.Vec.impl_1__as_slice";
    Tactics.prune "Alloc.Vec.impl_1__len";
    Tactics.prune "Core_models.Slice.impl__len";
    Tactics.prune "Rust_primitives.Slice.slice_index";
    Tactics.smt_sync' 1 1
  )

let past_has_dependencies (facts: t_Slice Native.t_Fact) (after: t_Slice Native.t_EventId) (result: Result.t_Result (Alloc.Vec.t_Vec Native.t_EventId Alloc.Alloc.t_Global) Native.t_Error) : Type0 =
  match result with | Result.Result_Ok _ -> begin dependencies_present facts after end | _ -> begin Prims.l_True end

let successful_past_has_direct_dependencies (facts: t_Slice Native.t_Fact) (after: t_Slice Native.t_EventId) : Lemma (ensures past_has_dependencies facts after (Native.past facts after)) =
  Nickel.EventGraphText.text_graph_policy_is_exact ();
  Nickel.EventGraphText.text_graph_callbacks_are_exact ();
  dependency_validation_is_sound facts after;
  assert (past_has_dependencies facts after (Native.past facts after)) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.prune "Nickel_crdt.Edit.validate_after";
    Tactics.prune "Nickel_crdt.Event_layer.validate_after";
    Tactics.prune "Alloc.Vec.from_seq";
    Tactics.prune "Alloc.Vec.impl_1__as_slice";
    Tactics.prune "Alloc.Vec.impl_1__len";
    Tactics.prune "Core_models.Slice.impl__len";
    Tactics.prune "Rust_primitives.Slice.slice_index";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel.LoopUtil.step_safe";
    Tactics.prune "Nickel.LoopUtil.output_safe";
    Tactics.smt_sync' 1 1
  )

let fact_dependencies_present (facts: t_Slice Native.t_Fact) (fact: Native.t_Fact) : Type0 =
  dependencies_present facts (Alloc.Vec.impl_1__as_slice fact.f_after)

let validation_has_dependencies (facts: t_Slice Native.t_Fact) (fact: Native.t_Fact) (result: Result.t_Result unit Native.t_Error) : Type0 =
  match result with | Result.Result_Ok _ -> begin fact_dependencies_present facts fact end | _ -> begin Prims.l_True end

let successful_validation_has_direct_dependencies (facts: t_Slice Native.t_Fact) (fact: Native.t_Fact) : Lemma (ensures validation_has_dependencies facts fact (Native.impl_Replica__validate_new facts fact)) =
  Nickel.EventGraphText.text_graph_policy_is_exact ();
  Nickel.EventGraphText.text_graph_callbacks_are_exact ();
  successful_past_has_direct_dependencies facts (Alloc.Vec.impl_1__as_slice fact.f_after);
  assert (validation_has_dependencies facts fact (Native.impl_Replica__validate_new facts fact)) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.prune "Nickel_crdt.Edit.past";
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.prune "Alloc.Vec.from_seq";
    Tactics.prune "Alloc.Vec.impl_1__as_slice";
    Tactics.prune "Alloc.Vec.impl_1__len";
    Tactics.prune "Core_models.Slice.impl__len";
    Tactics.prune "Rust_primitives.Slice.slice_index";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel.LoopUtil.step_safe";
    Tactics.prune "Nickel.LoopUtil.output_safe";
    Tactics.smt_sync' 1 1
  )

let added_dependencies (before: Native.t_Replica) (fact: Native.t_Fact) (outcome: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) : Type0 =
  match outcome with | (_, Result.Result_Ok Native.Admission_Added) -> begin fact_dependencies_present (Alloc.Vec.impl_1__as_slice before.f_facts) fact end | _ -> begin Prims.l_True end

let receive_added_has_direct_dependencies (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (ensures added_dependencies before fact (Native.impl_Replica__receive before fact)) =
  successful_validation_has_direct_dependencies (Alloc.Vec.impl_1__as_slice before.f_facts) fact;
  Nickel.EditAtomic.successful_plan_requires_validation before fact;
  Nickel.EditCommit.receive_uses_plan before fact;
  assert (added_dependencies before fact (Native.impl_Replica__receive before fact)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__validate_new";
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__plan";
    Tactics.prune "Nickel_crdt.Event_shell.plan";
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive_into";
    Tactics.prune "Alloc.Vec.from_seq";
    Tactics.prune "Alloc.Vec.impl_1__as_slice";
    Tactics.prune "Alloc.Vec.impl_1__len";
    Tactics.prune "Core_models.Slice.impl__len";
    Tactics.prune "Rust_primitives.Slice.slice_index";
    Tactics.smt_sync' 1 1
  )

let facts_contained (before: t_Slice Native.t_Fact) (next: t_Slice Native.t_Fact) : Type0 =
  forall(fact: Native.t_Fact). fact_present before fact ==> fact_present next fact

let absence_on_whole_facts (facts: t_Slice Native.t_Fact) (id: Native.t_EventId) : Lemma (ensures Nickel.EditIdentity.prefix_absent facts id (mk_usize 0) (Nickel.EditIdentity.length facts) <==> (forall(fact: Native.t_Fact). fact_present facts fact ==> Prims.l_not (fact.f_id == id))) =
  membership_absence_exact facts id;
  let forward (fact: Native.t_Fact) : Lemma (requires (Nickel.EditIdentity.prefix_absent facts id (mk_usize 0) (Nickel.EditIdentity.length facts) /\ fact_present facts fact)) (ensures Prims.l_not (fact.f_id == id)) =
    let i = find_fact_position facts fact in
    Nickel.Vector.slice_index facts (mk_usize i);
    Nickel.Vector.slice_length facts;
    assert (Prims.l_not (fact.f_id == id)) by (
      Tactics.prune "Nickel_crdt.Edit.has_fact";
      Tactics.prune "Nickel_crdt.Event_layer.has_fact";
      Tactics.prune "Nickel.Vector.slice_index";
      Tactics.prune "Nickel.Vector.slice_length";
      Tactics.prune "Rust_primitives.Slice.slice_index";
      Tactics.prune "Core_models.Slice.impl__len";
      Tactics.prune "Alloc.Vec.from_seq";
      Tactics.prune "Alloc.Vec.impl_1__as_slice";
      Tactics.prune "Alloc.Vec.impl_1__len";
      Tactics.smt_sync' 1 1
    ) in
  let reverse (dummy: unit) : Lemma (requires forall(fact: Native.t_Fact). fact_present facts fact ==> Prims.l_not (fact.f_id == id)) (ensures Nickel.EditIdentity.prefix_absent facts id (mk_usize 0) (Nickel.EditIdentity.length facts)) = if Native.has_fact facts id then
    begin let i = find_id_position facts id in
    assert (fact_present facts (Seq.index facts i));
    assert Prims.l_False end
  else
    begin () end in
  let all_forward (fact: Native.t_Fact) : Lemma (ensures Prims.l_and (Nickel.EditIdentity.prefix_absent facts id (mk_usize 0) (Nickel.EditIdentity.length facts)) (fact_present facts fact) ==> Prims.l_not (fact.f_id == id)) = FStar.Classical.move_requires forward fact in
  FStar.Classical.forall_intro all_forward;
  FStar.Classical.move_requires reverse ()

let presence_survives_containment (before: t_Slice Native.t_Fact) (next: t_Slice Native.t_Fact) (id: Native.t_EventId) : Lemma (requires (facts_contained before next /\ event_present before id)) (ensures event_present next id) =
  event_membership_is_presence before id;
  let i = find_id_position before id in
  let witness = Seq.index before i in
  assert (fact_present before witness);
  assert (fact_present next witness);
  absence_on_whole_facts next id;
  assert (event_present next id) by (
    Tactics.prune "Nickel.EditIdentity.prefix_absent";
    Tactics.prune "Alloc.Vec.from_seq";
    Tactics.prune "Alloc.Vec.impl_1__as_slice";
    Tactics.prune "Alloc.Vec.impl_1__len";
    Tactics.prune "Core_models.Slice.impl__len";
    Tactics.prune "Rust_primitives.Slice.slice_index";
    Tactics.smt_sync' 1 1
  )

let dependencies_survive_containment (before: t_Slice Native.t_Fact) (next: t_Slice Native.t_Fact) (fact: Native.t_Fact) : Lemma (requires (facts_contained before next /\ fact_dependencies_present before fact)) (ensures fact_dependencies_present next fact) =
  let each_id (id: Native.t_EventId) : Lemma (requires event_present before id) (ensures event_present next id) = presence_survives_containment before next id in
  let all_id (id: Native.t_EventId) : Lemma (ensures event_present before id ==> event_present next id) = FStar.Classical.move_requires each_id id in
  FStar.Classical.forall_intro all_id

let facts_causally_closed (facts: facts_vec) : Type0 =
  forall(fact: Native.t_Fact). fact_present (Alloc.Vec.impl_1__as_slice facts) fact ==> fact_dependencies_present (Alloc.Vec.impl_1__as_slice facts) fact

let exact_extension_preserves_causal_closure (before: facts_vec) (fact: Native.t_Fact) (next: facts_vec) : Lemma (requires (facts_causally_closed before /\ fact_dependencies_present (Alloc.Vec.impl_1__as_slice before) fact /\ appended_contents before fact next)) (ensures facts_causally_closed next) =
  assert (facts_contained (Alloc.Vec.impl_1__as_slice before) (Alloc.Vec.impl_1__as_slice next));
  let each_fact (item: Native.t_Fact) : Lemma (requires fact_present (Alloc.Vec.impl_1__as_slice next) item) (ensures fact_dependencies_present (Alloc.Vec.impl_1__as_slice next) item) =
    assert (fact_dependencies_present (Alloc.Vec.impl_1__as_slice before) item);
    dependencies_survive_containment (Alloc.Vec.impl_1__as_slice before) (Alloc.Vec.impl_1__as_slice next) item in
  let all_fact (item: Native.t_Fact) : Lemma (ensures fact_present (Alloc.Vec.impl_1__as_slice next) item ==> fact_dependencies_present (Alloc.Vec.impl_1__as_slice next) item) = FStar.Classical.move_requires each_fact item in
  FStar.Classical.forall_intro all_fact

let receive_causally_closed (outcome: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) : Type0 =
  match outcome with | (next, _) -> begin facts_causally_closed next.f_facts end

let receive_preserves_causal_closure (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (requires facts_causally_closed before.f_facts) (ensures receive_causally_closed (Native.impl_Replica__receive before fact)) =
  Nickel.EditAtomic.receive_rejection_unchanged before fact;
  receive_added_has_exact_contents before fact;
  receive_added_has_direct_dependencies before fact;
  match Native.impl_Replica__receive before fact with | (next, Result.Result_Ok Native.Admission_Added) -> begin exact_extension_preserves_causal_closure before.f_facts fact next.f_facts end | _ -> begin () end;
  assert (receive_causally_closed (Native.impl_Replica__receive before fact)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive_into";
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__edit";
    Tactics.prune "Alloc.Vec.from_seq";
    Tactics.prune "Alloc.Vec.impl_1__as_slice";
    Tactics.prune "Alloc.Vec.impl_1__len";
    Tactics.prune "Core_models.Slice.impl__len";
    Tactics.prune "Rust_primitives.Slice.slice_index";
    Tactics.smt_sync' 1 1
  )

let edit_causally_closed (outcome: Native.t_Replica & Result.t_Result Native.t_Local Native.t_Error) : Type0 =
  match outcome with | (next, _) -> begin facts_causally_closed next.f_facts end

let edit_preserves_causal_closure (before: Native.t_Replica) (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (delete: Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global) : Lemma (requires facts_causally_closed before.f_facts) (ensures edit_causally_closed (Native.impl_Replica__edit before gap insert delete)) =
  Nickel.EditAtomic.edit_rejection_or_empty_unchanged before gap insert delete;
  edit_authored_has_exact_contents before gap insert delete;
  Nickel.EditCommit.authored_fact_replays_same_commit before gap insert delete;
  match Native.impl_Replica__edit before gap insert delete with | (next, Result.Result_Ok (Native.Local_Authored fact)) -> begin receive_added_has_direct_dependencies before fact;
  exact_extension_preserves_causal_closure before.f_facts fact next.f_facts end | _ -> begin () end;
  assert (edit_causally_closed (Native.impl_Replica__edit before gap insert delete)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive_into";
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__edit";
    Tactics.prune "Alloc.Vec.from_seq";
    Tactics.prune "Alloc.Vec.impl_1__as_slice";
    Tactics.prune "Alloc.Vec.impl_1__len";
    Tactics.prune "Core_models.Slice.impl__len";
    Tactics.prune "Rust_primitives.Slice.slice_index";
    Tactics.smt_sync' 1 1
  )

let new_causally_closed (outcome: Result.t_Result Native.t_Replica Native.t_Error) : Type0 =
  match outcome with | Result.Result_Ok state -> begin facts_causally_closed state.f_facts end | _ -> begin Prims.l_True end

let new_establishes_causal_closure (writer: Option.t_Option Native.t_Writer) : Lemma (ensures new_causally_closed (Native.impl_Replica__new writer)) =
  Nickel.EditAtomic.new_has_empty_facts writer;
  assert (new_causally_closed (Native.impl_Replica__new writer)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__new";
    Tactics.prune "Alloc.Vec.from_seq";
    Tactics.prune "Alloc.Vec.impl_1__as_slice";
    Tactics.prune "Alloc.Vec.impl_1__len";
    Tactics.prune "Core_models.Slice.impl__len";
    Tactics.prune "Rust_primitives.Slice.slice_index";
    Tactics.smt_sync' 1 1
  )