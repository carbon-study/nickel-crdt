(* Latte generated F* view *)
module Nickel.EventGraphText

open Nickel.Prelude

open Rust_primitives

open Core_models

open FStar.Pervasives

module Native = Nickel_crdt.Edit

module Shared = Nickel_crdt.Event_layer

open Nickel.EventGraph

module Tactics = FStar.Tactics.V2

let text_graph_ops () : Nickel.EventGraph.graph_ops Native.t_Fact Native.t_EventId Native.t_Error =
  Shared.graph_ops Native.fact_id Native.fact_after Native.same_event_id Native.earlier_event_id Native.clone_selected_fact Native.fact_equal Native.internal_error Native.missing_error

let text_event_ops () : Nickel.EventGraph.event_ops Native.t_Fact Native.t_EventId Native.t_Error =
  Shared.event_ops (text_graph_ops ()) Native.required_predecessor Native.forbidden_ancestor Native.duplicate_dependency_error Native.predecessor_error

let text_graph_callbacks_are_exact () : Lemma (ensures Nickel.EventGraph.graph_callbacks_match (text_graph_ops ()) Native.fact_id Native.fact_after Native.same_event_id Native.earlier_event_id Native.clone_selected_fact Native.fact_equal Native.internal_error Native.missing_error) =
  Nickel.EventGraph.graph_ops_preserve_callbacks Native.fact_id Native.fact_after Native.same_event_id Native.earlier_event_id Native.clone_selected_fact Native.fact_equal Native.internal_error Native.missing_error;
  assert (Nickel.EventGraph.graph_callbacks_match (text_graph_ops ()) Native.fact_id Native.fact_after Native.same_event_id Native.earlier_event_id Native.clone_selected_fact Native.fact_equal Native.internal_error Native.missing_error) by (
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.smt_sync' 1 1
  )

let text_policy_is_exact () : Lemma (ensures Native.v_TEXT_OPS == text_event_ops ()) =
  ()

let text_graph_policy_is_exact () : Lemma (ensures Native.v_TEXT_OPS._1 == text_graph_ops ()) =
  text_policy_is_exact ();
  Nickel.EventGraph.event_ops_preserve_callbacks (text_graph_ops ()) Native.required_predecessor Native.forbidden_ancestor Native.duplicate_dependency_error Native.predecessor_error;
  assert (Native.v_TEXT_OPS._1 == text_graph_ops ()) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.smt_sync' 1 1
  )

let has_fact_is_text_call (facts: t_Slice Native.t_Fact) (id: Native.t_EventId) : Lemma (ensures Shared.has_fact facts id (text_graph_ops ()) == Native.has_fact facts id) [SMTPat (Shared.has_fact facts id (text_graph_ops ()))] =
  text_graph_policy_is_exact ();
  assert (Shared.has_fact facts id (text_graph_ops ()) == Native.has_fact facts id) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.smt_sync' 1 1
  )

let validate_after_is_text_call (facts: t_Slice Native.t_Fact) (after: t_Slice Native.t_EventId) : Lemma (ensures Shared.validate_after facts after (text_graph_ops ()) == Native.validate_after facts after) [SMTPat (Shared.validate_after facts after (text_graph_ops ()))] =
  text_graph_policy_is_exact ();
  assert (Shared.validate_after facts after (text_graph_ops ()) == Native.validate_after facts after) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.smt_sync' 1 1
  )

let extend_past_is_text_call (fact: Native.t_Fact) (selected: Alloc.Vec.t_Vec Native.t_EventId Alloc.Alloc.t_Global) : Lemma (ensures Shared.extend_past fact selected (text_graph_ops ()) == Native.extend_past fact selected) [SMTPat (Shared.extend_past fact selected (text_graph_ops ()))] =
  text_graph_policy_is_exact ();
  assert (Shared.extend_past fact selected (text_graph_ops ()) == Native.extend_past fact selected) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.smt_sync' 1 1
  )

let past_pass_is_text_call (facts: t_Slice Native.t_Fact) (selected: Alloc.Vec.t_Vec Native.t_EventId Alloc.Alloc.t_Global) : Lemma (ensures Shared.past_pass facts selected (text_graph_ops ()) == Native.past_pass facts selected) [SMTPat (Shared.past_pass facts selected (text_graph_ops ()))] =
  text_graph_policy_is_exact ();
  assert (Shared.past_pass facts selected (text_graph_ops ()) == Native.past_pass facts selected) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.smt_sync' 1 1
  )

let past_is_text_call (facts: t_Slice Native.t_Fact) (roots: t_Slice Native.t_EventId) : Lemma (ensures Shared.past facts roots (text_graph_ops ()) == Native.past facts roots) [SMTPat (Shared.past facts roots (text_graph_ops ()))] =
  text_graph_policy_is_exact ();
  assert (Shared.past facts roots (text_graph_ops ()) == Native.past facts roots) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.smt_sync' 1 1
  )

let choose_unseen_is_text_call (facts: t_Slice Native.t_Fact) (out: t_Slice Native.t_Fact) : Lemma (ensures Shared.choose_unseen facts out (text_graph_ops ()) == Native.choose_unseen facts out) [SMTPat (Shared.choose_unseen facts out (text_graph_ops ()))] =
  text_graph_policy_is_exact ();
  assert (Shared.choose_unseen facts out (text_graph_ops ()) == Native.choose_unseen facts out) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.smt_sync' 1 1
  )

let canonical_step_is_text_call (facts: t_Slice Native.t_Fact) (out: Alloc.Vec.t_Vec Native.t_Fact Alloc.Alloc.t_Global) : Lemma (ensures Shared.canonical_step facts out (text_graph_ops ()) == Native.canonical_step facts out) [SMTPat (Shared.canonical_step facts out (text_graph_ops ()))] =
  text_graph_policy_is_exact ();
  assert (Shared.canonical_step facts out (text_graph_ops ()) == Native.canonical_step facts out) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.smt_sync' 1 1
  )

let canonical_is_text_call (facts: t_Slice Native.t_Fact) : Lemma (ensures Shared.canonical facts (text_graph_ops ()) == Native.canonical facts) [SMTPat (Shared.canonical facts (text_graph_ops ()))] =
  text_graph_policy_is_exact ();
  assert (Shared.canonical facts (text_graph_ops ()) == Native.canonical facts) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.smt_sync' 1 1
  )

let select_basis_is_text_call (facts: t_Slice Native.t_Fact) (selected: t_Slice Native.t_EventId) : Lemma (ensures Shared.select_basis facts selected (text_graph_ops ()) == Native.select_basis facts selected) [SMTPat (Shared.select_basis facts selected (text_graph_ops ()))] =
  text_graph_policy_is_exact ();
  assert (Shared.select_basis facts selected (text_graph_ops ()) == Native.select_basis facts selected) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.smt_sync' 1 1
  )

let event_basis_is_text_call (facts: t_Slice Native.t_Fact) (event: Native.t_Fact) : Lemma (ensures Shared.event_basis facts event (text_graph_ops ()) == Native.event_basis facts event) [SMTPat (Shared.event_basis facts event (text_graph_ops ()))] =
  text_graph_policy_is_exact ();
  assert (Shared.event_basis facts event (text_graph_ops ()) == Native.event_basis facts event) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.smt_sync' 1 1
  )

let frontier_is_text_call (facts: t_Slice Native.t_Fact) : Lemma (ensures Shared.frontier facts (text_graph_ops ()) == Native.frontier facts) [SMTPat (Shared.frontier facts (text_graph_ops ()))] =
  text_graph_policy_is_exact ();
  assert (Shared.frontier facts (text_graph_ops ()) == Native.frontier facts) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.smt_sync' 1 1
  )

let duplicate_ids_is_text_call (ids: t_Slice Native.t_EventId) : Lemma (ensures Shared.duplicate_ids ids (text_graph_ops ()) == Native.duplicate_events ids) [SMTPat (Shared.duplicate_ids ids (text_graph_ops ()))] =
  text_graph_policy_is_exact ();
  assert (Shared.duplicate_ids ids (text_graph_ops ()) == Native.duplicate_events ids) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.smt_sync' 1 1
  )

let push_is_text_call (#item: Type0) (before: Alloc.Vec.t_Vec item Alloc.Alloc.t_Global) (value: item) : Lemma (ensures Shared.push before value Native.internal_error == Native.push before value) [SMTPat (Shared.push before value Native.internal_error)] =
  ()

let clone_is_text_call (fact: Native.t_Fact) : Lemma (ensures Shared.clone_selected_fact fact Native.clone_selected_fact == Native.clone_selected_fact fact) [SMTPat (Shared.clone_selected_fact fact Native.clone_selected_fact)] =
  ()

let scheduler_choice_is_text_call (facts: t_Slice Native.t_Fact) (done: t_Slice Native.t_EventId) : Lemma (ensures Native.scheduled_choose () facts done == Native.choose_ready facts done) [SMTPat (Native.scheduled_choose () facts done)] =
  ()

let scheduler_application_is_text_call (facts: t_Slice Native.t_Fact) (event: Native.t_Fact) (operations: t_Slice (Native.t_EventId & Alloc.Vec.t_Vec Native.t_Node Alloc.Alloc.t_Global)) (tree: Native.t_Tree) : Lemma (ensures Native.scheduled_apply () facts event operations tree == Native.interpret_event facts event operations tree) [SMTPat (Native.scheduled_apply () facts event operations tree)] =
  ()