(* Latte generated F* view *)
module Nickel.EventGraphText

open Nickel.Prelude

open Rust_primitives

open Core_models

open FStar.Pervasives

module Native = Nickel_crdt.Edit

module Shared = Nickel_crdt.Event_layer

let has_fact_is_text_call (facts: t_Slice Native.t_Fact) (id: Native.t_EventId) : Lemma (ensures Shared.has_fact facts id Native.fact_id Native.same_event_id == Native.has_fact facts id) [SMTPat (Shared.has_fact facts id Native.fact_id Native.same_event_id)] =
  ()

let validate_after_is_text_call (facts: t_Slice Native.t_Fact) (after: t_Slice Native.t_EventId) : Lemma (ensures Shared.validate_after facts after Native.fact_id Native.same_event_id Native.missing_error == Native.validate_after facts after) [SMTPat (Shared.validate_after facts after Native.fact_id Native.same_event_id Native.missing_error)] =
  ()

let extend_past_is_text_call (fact: Native.t_Fact) (selected: Alloc.Vec.t_Vec Native.t_EventId Alloc.Alloc.t_Global) : Lemma (ensures Shared.extend_past fact selected Native.fact_id Native.fact_after Native.same_event_id Native.internal_error == Native.extend_past fact selected) [SMTPat (Shared.extend_past fact selected Native.fact_id Native.fact_after Native.same_event_id Native.internal_error)] =
  ()

let past_pass_is_text_call (facts: t_Slice Native.t_Fact) (selected: Alloc.Vec.t_Vec Native.t_EventId Alloc.Alloc.t_Global) : Lemma (ensures Shared.past_pass facts selected Native.fact_id Native.fact_after Native.same_event_id Native.internal_error == Native.past_pass facts selected) [SMTPat (Shared.past_pass facts selected Native.fact_id Native.fact_after Native.same_event_id Native.internal_error)] =
  ()

let past_is_text_call (facts: t_Slice Native.t_Fact) (roots: t_Slice Native.t_EventId) : Lemma (ensures Shared.past facts roots Native.fact_id Native.fact_after Native.same_event_id Native.internal_error Native.missing_error == Native.past facts roots) [SMTPat (Shared.past facts roots Native.fact_id Native.fact_after Native.same_event_id Native.internal_error Native.missing_error)] =
  ()

let choose_unseen_is_text_call (facts: t_Slice Native.t_Fact) (out: t_Slice Native.t_Fact) : Lemma (ensures Shared.choose_unseen facts out Native.fact_id Native.same_event_id Native.earlier_event_id Native.internal_error == Native.choose_unseen facts out) [SMTPat (Shared.choose_unseen facts out Native.fact_id Native.same_event_id Native.earlier_event_id Native.internal_error)] =
  ()

let canonical_step_is_text_call (facts: t_Slice Native.t_Fact) (out: Alloc.Vec.t_Vec Native.t_Fact Alloc.Alloc.t_Global) : Lemma (ensures Shared.canonical_step facts out Native.fact_id Native.same_event_id Native.earlier_event_id Native.internal_error Native.clone_selected_fact == Native.canonical_step facts out) [SMTPat (Shared.canonical_step facts out Native.fact_id Native.same_event_id Native.earlier_event_id Native.internal_error Native.clone_selected_fact)] =
  ()

let canonical_is_text_call (facts: t_Slice Native.t_Fact) : Lemma (ensures Shared.canonical facts Native.fact_id Native.same_event_id Native.earlier_event_id Native.internal_error Native.clone_selected_fact == Native.canonical facts) [SMTPat (Shared.canonical facts Native.fact_id Native.same_event_id Native.earlier_event_id Native.internal_error Native.clone_selected_fact)] =
  ()

let select_basis_is_text_call (facts: t_Slice Native.t_Fact) (selected: t_Slice Native.t_EventId) : Lemma (ensures Shared.select_basis facts selected Native.fact_id Native.same_event_id Native.internal_error Native.clone_selected_fact == Native.select_basis facts selected) [SMTPat (Shared.select_basis facts selected Native.fact_id Native.same_event_id Native.internal_error Native.clone_selected_fact)] =
  ()

let event_basis_is_text_call (facts: t_Slice Native.t_Fact) (event: Native.t_Fact) : Lemma (ensures Shared.event_basis facts event Native.fact_id Native.fact_after Native.same_event_id Native.internal_error Native.missing_error Native.clone_selected_fact == Native.event_basis facts event) [SMTPat (Shared.event_basis facts event Native.fact_id Native.fact_after Native.same_event_id Native.internal_error Native.missing_error Native.clone_selected_fact)] =
  ()

let frontier_is_text_call (facts: t_Slice Native.t_Fact) : Lemma (ensures Shared.frontier facts Native.fact_id Native.fact_after Native.same_event_id Native.internal_error == Native.frontier facts) [SMTPat (Shared.frontier facts Native.fact_id Native.fact_after Native.same_event_id Native.internal_error)] =
  ()

let duplicate_ids_is_text_call (ids: t_Slice Native.t_EventId) : Lemma (ensures Shared.duplicate_ids ids Native.same_event_id == Native.duplicate_events ids) [SMTPat (Shared.duplicate_ids ids Native.same_event_id)] =
  ()

let push_is_text_call (#item: Type0) (before: Alloc.Vec.t_Vec item Alloc.Alloc.t_Global) (value: item) : Lemma (ensures Shared.push before value Native.internal_error == Native.push before value) [SMTPat (Shared.push before value Native.internal_error)] =
  ()

let clone_is_text_call (fact: Native.t_Fact) : Lemma (ensures Shared.clone_selected_fact fact Native.clone_selected_fact == Native.clone_selected_fact fact) [SMTPat (Shared.clone_selected_fact fact Native.clone_selected_fact)] =
  ()

let scheduler_choice_is_text_call (facts: t_Slice Native.t_Fact) (done: t_Slice Native.t_EventId) : Lemma (ensures Native.scheduled_choose () facts done == Native.choose_ready facts done) [SMTPat (Native.scheduled_choose () facts done)] =
  ()

let scheduler_application_is_text_call (facts: t_Slice Native.t_Fact) (event: Native.t_Fact) (operations: t_Slice (Native.t_EventId & Alloc.Vec.t_Vec Native.t_Node Alloc.Alloc.t_Global)) (tree: Native.t_Tree) : Lemma (ensures Native.scheduled_apply () facts event operations tree == Native.interpret_event facts event operations tree) [SMTPat (Native.scheduled_apply () facts event operations tree)] =
  ()