(* Latte generated F* view *)
module Nickel.Spec

open Nickel.Prelude

open Rust_primitives

open Core_models

open FStar.Pervasives

module Native = Nickel_crdt.Edit

module Result = Core_models.Result

module Option = Core_models.Option

module Atomic = Nickel.EditAtomic

module Commit = Nickel.EditCommit

module Identity = Nickel.EditIdentity

module Accepted = Nickel.EditAccepted

module WellFormed = Nickel.EditWellFormed

module Tactics = FStar.Tactics.V2

let stored_facts_valid (state: Native.t_Replica) : Type0 =
  Prims.l_and (Prims.l_and (Prims.l_and (Accepted.ids_unique state.f_facts) (Accepted.facts_ordered state.f_facts)) (WellFormed.facts_scalars_valid state.f_facts)) (WellFormed.facts_causally_closed state.f_facts)

let constructed_facts_valid (result: Result.t_Result Native.t_Replica Native.t_Error) : Type0 =
  match result with | Result.Result_Ok state -> begin stored_facts_valid state end | _ -> begin Prims.l_True end

let received_facts_valid (result: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) : Type0 =
  match result with | (state, _) -> begin stored_facts_valid state end

let edited_facts_valid (result: Native.t_Replica & Result.t_Result Native.t_Local Native.t_Error) : Type0 =
  match result with | (state, _) -> begin stored_facts_valid state end

let new_establishes_valid_facts (writer: Option.t_Option Native.t_Writer) : Lemma (ensures constructed_facts_valid (Native.impl_Replica__new writer)) =
  Accepted.new_establishes_unique_ids writer;
  Accepted.new_establishes_fact_order writer;
  WellFormed.new_establishes_scalar_validity writer;
  WellFormed.new_establishes_causal_closure writer;
  assert (constructed_facts_valid (Native.impl_Replica__new writer)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__new";
    Tactics.smt_sync' 1 1
  )

let receive_preserves_valid_facts (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (requires stored_facts_valid before) (ensures received_facts_valid (Native.impl_Replica__receive before fact)) =
  Accepted.receive_preserves_unique_ids before fact;
  Accepted.receive_preserves_fact_order before fact;
  WellFormed.receive_preserves_scalar_validity before fact;
  WellFormed.receive_preserves_causal_closure before fact;
  assert (received_facts_valid (Native.impl_Replica__receive before fact)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive_into";
    Tactics.smt_sync' 1 1
  )

let edit_preserves_valid_facts (before: Native.t_Replica) (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (delete: Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global) : Lemma (requires stored_facts_valid before) (ensures edited_facts_valid (Native.impl_Replica__edit before gap insert delete)) =
  Accepted.edit_preserves_unique_ids before gap insert delete;
  Accepted.edit_preserves_fact_order before gap insert delete;
  WellFormed.edit_preserves_scalar_validity before gap insert delete;
  WellFormed.edit_preserves_causal_closure before gap insert delete;
  assert (edited_facts_valid (Native.impl_Replica__edit before gap insert delete)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__edit";
    Tactics.smt_sync' 1 1
  )

let receive_contract (before: Native.t_Replica) (fact: Native.t_Fact) (outcome: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) : Type0 =
  Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Atomic.receive_neutral before outcome) (Commit.private_unchanged before outcome)) (Accepted.added_exact_contents before fact outcome)) (Identity.added_is_fresh before fact outcome)) (Accepted.added_state_unique outcome)) (Accepted.added_ordered outcome)) (WellFormed.added_scalars fact outcome)) (WellFormed.added_dependencies before fact outcome)

let receive_obeys_contract (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (ensures receive_contract before fact (Native.impl_Replica__receive before fact)) =
  Atomic.receive_rejection_unchanged before fact;
  Commit.receive_preserves_private_state before fact;
  Accepted.receive_added_has_exact_contents before fact;
  Identity.receive_added_has_fresh_event_id before fact;
  Accepted.receive_added_ids_are_unique before fact;
  Accepted.receive_added_facts_are_ordered before fact;
  WellFormed.receive_added_fact_has_valid_scalars before fact;
  WellFormed.receive_added_has_direct_dependencies before fact;
  assert (receive_contract before fact (Native.impl_Replica__receive before fact)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive_into";
    Tactics.smt_sync' 1 1
  )

let edit_contract (before: Native.t_Replica) (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (delete: Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global) (outcome: Native.t_Replica & Result.t_Result Native.t_Local Native.t_Error) : Type0 =
  Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Atomic.edit_neutral before outcome) (Atomic.edit_counter_step before outcome)) (Commit.request_bound before gap insert delete outcome)) (Commit.same_commit before outcome)) (Accepted.authored_exact_contents before outcome)) (Identity.authored_id_is_fresh before outcome)) (Accepted.authored_ordered outcome)) (WellFormed.authored_scalars outcome)

let edit_obeys_contract (before: Native.t_Replica) (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (delete: Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global) : Lemma (ensures edit_contract before gap insert delete (Native.impl_Replica__edit before gap insert delete)) =
  Atomic.edit_rejection_or_empty_unchanged before gap insert delete;
  Atomic.authored_edit_advances_once before gap insert delete;
  Commit.authored_fact_binds_request before gap insert delete;
  Commit.authored_fact_replays_same_commit before gap insert delete;
  Accepted.edit_authored_has_exact_contents before gap insert delete;
  Identity.authored_event_id_is_fresh before gap insert delete;
  Accepted.authored_facts_are_ordered before gap insert delete;
  WellFormed.edit_authors_only_valid_scalars before gap insert delete;
  assert (edit_contract before gap insert delete (Native.impl_Replica__edit before gap insert delete)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__edit";
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive_into";
    Tactics.smt_sync' 1 1
  )

let known_identity_is_classified (before: Native.t_Replica) (fact: Native.t_Fact) (index: usize{v index < v (Identity.length (Alloc.Vec.impl_1__as_slice before.f_facts))}) : Lemma (requires (Identity.unique_ids (Alloc.Vec.impl_1__as_slice before.f_facts) /\ (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice before.f_facts) index).f_id == fact.f_id /\ Prims.l_and (0 < v fact.f_id.f_counter) (v fact.f_id.f_counter <= 9007199254740991))) (ensures Native.impl_Replica__receive before fact == Identity.known_identity before (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice before.f_facts) index) fact) =
  Identity.receive_known_identity before fact index;
  assert (Native.impl_Replica__receive before fact == Identity.known_identity before (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice before.f_facts) index) fact) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive_into";
    Tactics.smt_sync' 1 1
  )

let invalid_counter_is_rejected (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (requires Prims.l_or (v fact.f_id.f_counter == 0) (v fact.f_id.f_counter > 9007199254740991)) (ensures Native.impl_Replica__receive before fact == (before, Result.Result_Err (Native.Error_Invalid Native.Invalid_Counter))) =
  Identity.receive_invalid_counter before fact;
  assert (Native.impl_Replica__receive before fact == (before, Result.Result_Err (Native.Error_Invalid Native.Invalid_Counter))) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive_into";
    Tactics.smt_sync' 1 1
  )

let equal_shared_history_gives_same_admission (before: Native.t_Replica) (remote: Native.t_Replica) (fact: Native.t_Fact) : Lemma (requires Commit.same_shared before remote) (ensures Commit.same_admission (Native.impl_Replica__receive before fact) (Native.impl_Replica__receive remote fact)) =
  Commit.admission_ignores_private_state before remote fact;
  assert (Commit.same_admission (Native.impl_Replica__receive before fact) (Native.impl_Replica__receive remote fact)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive_into";
    Tactics.smt_sync' 1 1
  )

let authored_fact_admits_on_equal_shared_history (before: Native.t_Replica) (remote: Native.t_Replica) (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (delete: Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global) : Lemma (requires Commit.same_shared before remote) (ensures Commit.delivered_commit remote (Native.impl_Replica__edit before gap insert delete)) =
  Commit.local_author_remote_admit before remote gap insert delete;
  assert (Commit.delivered_commit remote (Native.impl_Replica__edit before gap insert delete)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__edit";
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive_into";
    Tactics.smt_sync' 1 1
  )

let equal_candidate_contents_give_same_rebuild (left: Native.t_Replica) (left_fact: Native.t_Fact) (right: Native.t_Replica) (right_fact: Native.t_Fact) : Lemma (requires Accepted.same_input_contents_and_length (Alloc.Vec.impl_1__as_slice (Accepted.candidate_facts left left_fact)) (Alloc.Vec.impl_1__as_slice (Accepted.candidate_facts right right_fact))) (ensures Accepted.added_shared_agreement (Native.impl_Replica__receive left left_fact) (Native.impl_Replica__receive right right_fact)) =
  Accepted.receive_added_shared_state_agrees left left_fact right right_fact;
  assert (Accepted.added_shared_agreement (Native.impl_Replica__receive left left_fact) (Native.impl_Replica__receive right right_fact)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive_into";
    Tactics.smt_sync' 1 1
  )