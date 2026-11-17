(* Latte generated F* view *)
module Nickel.EditPast

open Nickel.Prelude

open Nickel.PastExact

module Shared = Nickel_crdt.Event_layer

module Graph = Nickel.EventGraph

open Nickel.EventGraphText

open Rust_primitives

open Core_models

open FStar.Pervasives

open FStar.Classical

open Nickel.Vector

open Nickel.LoopUtil

open Nickel.EditAccepted

open Nickel.EditCausal

module List = FStar.List.Tot

module Native = Nickel_crdt.Edit

module Result = Core_models.Result

module Seq = FStar.Seq

let text_past_ids_are_exact () : Lemma (ensures Nickel.PastExact.ids_exact (Nickel.EventGraphText.text_graph_ops ())) =
  Nickel.EventGraphText.text_graph_callbacks_are_exact ();
  ()

let absent_prefix (ids: t_Slice Native.t_EventId) (id: Native.t_EventId) (finish: nat) : Type0 =
  forall(i: usize{v i < Seq.length ids}). v i < finish ==> Seq.index ids (v i) =!= id

let member (ids: t_Slice Native.t_EventId) (id: Native.t_EventId) : Type0 =
  Prims.l_not (absent_prefix ids id (Seq.length ids))

let event_membership_is_exact (ids: t_Slice Native.t_EventId) (id: Native.t_EventId) : Lemma (ensures Native.has_event ids id == true <==> member ids id) [SMTPat (Native.has_event ids id)] =
  Nickel.EventGraphText.text_graph_policy_is_exact ();
  Nickel.EventGraphText.text_graph_callbacks_are_exact ();
  assert (Shared.has_id ids id (Nickel.EventGraphText.text_graph_ops ()) == Native.has_event ids id) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.smt_sync' 1 1
  );
  Graph.membership_is_exact ids id (Nickel.EventGraphText.text_graph_ops ());
  assert (Native.has_event ids id == true <==> member ids id) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.prune "Nickel_crdt.Edit.has_event";
    Tactics.prune "Nickel_crdt.Event_layer.has_id";
    Tactics.smt_sync' 1 1
  )

let id_membership_is_text_call (ids: t_Slice Native.t_EventId) (id: Native.t_EventId) : Lemma (ensures Shared.has_id ids id (Nickel.EventGraphText.text_graph_ops ()) == Native.has_event ids id) [SMTPat (Shared.has_id ids id (Nickel.EventGraphText.text_graph_ops ()))] =
  Nickel.EventGraphText.text_graph_policy_is_exact ();
  assert (Shared.has_id ids id (Nickel.EventGraphText.text_graph_ops ()) == Native.has_event ids id) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.smt_sync' 1 1
  )

unfold type ids_vec = Alloc.Vec.t_Vec Native.t_EventId Alloc.Alloc.t_Global

let all_ids (ids: t_Slice Native.t_EventId) (p: Native.t_EventId -> Type0) : Type0 =
  forall(i: usize{v i < Seq.length ids}). p (Seq.index ids (v i))

let retains (roots: t_Slice Native.t_EventId) (selected: ids_vec) : Type0 =
  forall(i: usize{v i < Seq.length roots}). member (Alloc.Vec.impl_1__as_slice selected) (Seq.index roots (v i))

let selection_ok (roots: t_Slice Native.t_EventId) (p: Native.t_EventId -> Type0) (selected: ids_vec) : Type0 =
  Prims.l_and (all_ids (Alloc.Vec.impl_1__as_slice selected) p) (retains roots selected)

let selection_result (roots: t_Slice Native.t_EventId) (p: Native.t_EventId -> Type0) (result: Result.t_Result ids_vec Native.t_Error) : Type0 =
  match result with | Result.Result_Ok selected -> begin selection_ok roots p selected end | _ -> begin Prims.l_True end

let member_satisfies (ids: t_Slice Native.t_EventId) (p: Native.t_EventId -> Type0) (id: Native.t_EventId) : Lemma (requires (all_ids ids p /\ member ids id)) (ensures p id) =
  ()

let push_selection_result (roots: t_Slice Native.t_EventId) (p: Native.t_EventId -> Type0) (outcome: ids_vec & Result.t_Result unit Native.t_Error) : Type0 =
  match outcome with | (next, Result.Result_Ok _) -> begin selection_ok roots p next end | _ -> begin Prims.l_True end

let selected_push_preserves (roots: t_Slice Native.t_EventId) (p: Native.t_EventId -> Type0) (before: ids_vec) (id: Native.t_EventId) : Lemma (requires (selection_ok roots p before /\ p id)) (ensures push_selection_result roots p (Native.push before id)) =
  push_result_is_exact before id;
  assert (push_selection_result roots p (Native.push before id)) by (
    Tactics.prune "Nickel_crdt.Edit.push";
    Tactics.prune "Nickel_crdt.Event_layer.push";
    Tactics.smt_sync' 1 1
  )

let fact_closed (fact: Native.t_Fact) (p: Native.t_EventId -> Type0) : Type0 =
  p fact.f_id ==> all_ids (Alloc.Vec.impl_1__as_slice fact.f_after) p

let extend_past_preserves (roots: t_Slice Native.t_EventId) (p: Native.t_EventId -> Type0) (fact: Native.t_Fact) (before: ids_vec) : Lemma (requires (selection_ok roots p before /\ fact_closed fact p)) (ensures selection_result roots p (Native.extend_past fact before)) =
  text_past_ids_are_exact ();
  Nickel.EventGraphText.text_graph_callbacks_are_exact ();
  Nickel.EventGraphText.extend_past_is_text_call fact before;
  Nickel.PastExact.extend_past_preserves (Nickel.EventGraphText.text_graph_ops ()) roots p fact before;
  assert (selection_result roots p (Native.extend_past fact before)) by (
    Tactics.prune "Nickel_crdt.Edit.extend_past";
    Tactics.prune "Nickel_crdt.Event_layer.extend_past";
    Tactics.prune "Nickel.PastExact.extend_past_preserves";
    Tactics.smt_sync' 1 1
  )

let facts_closed (facts: t_Slice Native.t_Fact) (p: Native.t_EventId -> Type0) : Type0 =
  forall(i: usize{v i < Seq.length facts}). fact_closed (Seq.index facts (v i)) p

let past_pass_preserves (roots: t_Slice Native.t_EventId) (p: Native.t_EventId -> Type0) (facts: t_Slice Native.t_Fact) (before: ids_vec) : Lemma (requires (selection_ok roots p before /\ facts_closed facts p)) (ensures selection_result roots p (Native.past_pass facts before)) =
  text_past_ids_are_exact ();
  Nickel.EventGraphText.text_graph_callbacks_are_exact ();
  Nickel.EventGraphText.past_pass_is_text_call facts before;
  Nickel.PastExact.past_pass_preserves (Nickel.EventGraphText.text_graph_ops ()) roots p facts before;
  assert (selection_result roots p (Native.past_pass facts before)) by (
    Tactics.prune "Nickel_crdt.Edit.past_pass";
    Tactics.prune "Nickel_crdt.Event_layer.past_pass";
    Tactics.prune "Nickel.PastExact.past_pass_preserves";
    Tactics.smt_sync' 1 1
  )

let initial_selection_is_valid (roots: t_Slice Native.t_EventId) (p: Native.t_EventId -> Type0) : Lemma (requires all_ids roots p) (ensures selection_ok roots p (Alloc.Slice.impl__to_vec roots)) =
  ()

let past_stays_in_closed_set (facts: t_Slice Native.t_Fact) (roots: t_Slice Native.t_EventId) (p: Native.t_EventId -> Type0) : Lemma (requires (all_ids roots p /\ facts_closed facts p)) (ensures selection_result roots p (Native.past facts roots)) =
  text_past_ids_are_exact ();
  Nickel.EventGraphText.text_graph_callbacks_are_exact ();
  Nickel.EventGraphText.past_is_text_call facts roots;
  Nickel.PastExact.past_stays_in_closed_set (Nickel.EventGraphText.text_graph_ops ()) facts roots p;
  assert (selection_result roots p (Native.past facts roots)) by (
    Tactics.prune "Nickel_crdt.Edit.past";
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.prune "Nickel.PastExact.past_stays_in_closed_set";
    Tactics.smt_sync' 1 1
  )

let ancestor (facts: facts_vec) (roots: t_Slice Native.t_EventId) (id: Native.t_EventId) : Type0 =
  exists(root: Native.t_EventId) (steps: Prims.list Native.t_EventId). Prims.l_and (member roots root) (Nickel.EditCausal.causal_path facts root steps id)

let rec append_path_edge (facts: facts_vec) (root: Native.t_EventId) (steps: Prims.list Native.t_EventId) (parent: Native.t_EventId) (child: Native.t_EventId) : Lemma (requires (Nickel.EditCausal.causal_path facts root steps parent /\ Nickel.EditCausal.causal_edge facts parent child)) (ensures Nickel.EditCausal.causal_path facts root (List.append steps (Prims.Cons child Prims.Nil)) child) (decreases steps) =
  match steps with | Prims.Nil -> begin () end | Prims.Cons next rest -> begin append_path_edge facts next rest parent child end

let ancestor_follows_edge (facts: facts_vec) (roots: t_Slice Native.t_EventId) (parent: Native.t_EventId) (child: Native.t_EventId) : Lemma (requires (ancestor facts roots parent /\ Nickel.EditCausal.causal_edge facts parent child)) (ensures ancestor facts roots child) =
  let each_path (root: Native.t_EventId) (steps: Prims.list Native.t_EventId) : Lemma (requires (member roots root /\ Nickel.EditCausal.causal_path facts root steps parent)) (ensures ancestor facts roots child) =
    append_path_edge facts root steps parent child;
    assert (Prims.l_and (member roots root) (Nickel.EditCausal.causal_path facts root (List.append steps (Prims.Cons child Prims.Nil)) child));
    () in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_path);
  ()

let text_causal_edge_is_shared (facts: facts_vec) : Lemma (ensures forall(parent: Native.t_EventId) (child: Native.t_EventId). Nickel.PastExact.causal_edge (Nickel.EventGraphText.text_graph_ops ()) (Alloc.Vec.impl_1__as_slice facts) parent child <==> Nickel.EditCausal.causal_edge facts parent child) =
  Nickel.EventGraphText.text_graph_callbacks_are_exact ();
  ()

let rec shared_path_is_text (facts: facts_vec) (start: Native.t_EventId) (steps: Prims.list Native.t_EventId) (finish: Native.t_EventId) : Lemma (ensures Nickel.PastExact.causal_path (Nickel.EventGraphText.text_graph_ops ()) (Alloc.Vec.impl_1__as_slice facts) start steps finish <==> Nickel.EditCausal.causal_path facts start steps finish) (decreases steps) =
  text_causal_edge_is_shared facts;
  Nickel.PastExact.causal_path_equations (Nickel.EventGraphText.text_graph_ops ()) (Alloc.Vec.impl_1__as_slice facts);
  match steps with | Prims.Nil -> begin () end | Prims.Cons next rest -> begin shared_path_is_text facts next rest finish end

let all_shared_paths_are_text (facts: facts_vec) : Lemma (ensures forall(start: Native.t_EventId) (steps: Prims.list Native.t_EventId) (finish: Native.t_EventId). Nickel.PastExact.causal_path (Nickel.EventGraphText.text_graph_ops ()) (Alloc.Vec.impl_1__as_slice facts) start steps finish <==> Nickel.EditCausal.causal_path facts start steps finish) =
  let each (start: Native.t_EventId) (steps: Prims.list Native.t_EventId) (finish: Native.t_EventId) : Lemma (ensures Nickel.PastExact.causal_path (Nickel.EventGraphText.text_graph_ops ()) (Alloc.Vec.impl_1__as_slice facts) start steps finish <==> Nickel.EditCausal.causal_path facts start steps finish) = shared_path_is_text facts start steps finish in
  FStar.Classical.forall_intro_3 each

let past_has_only_ancestors_and_keeps_roots (facts: facts_vec) (roots: t_Slice Native.t_EventId) : Lemma (ensures selection_result roots (ancestor facts roots) (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) =
  text_past_ids_are_exact ();
  Nickel.EventGraphText.text_graph_callbacks_are_exact ();
  Nickel.EventGraphText.past_is_text_call (Alloc.Vec.impl_1__as_slice facts) roots;
  all_shared_paths_are_text facts;
  Nickel.PastExact.past_has_only_ancestors_and_keeps_roots (Nickel.EventGraphText.text_graph_ops ()) (Alloc.Vec.impl_1__as_slice facts) roots;
  match Native.past (Alloc.Vec.impl_1__as_slice facts) roots with | Result.Result_Ok selected -> begin assert (selection_result roots (ancestor facts roots) (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) by (
    Tactics.prune "Nickel_crdt.Edit.past";
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.prune "Nickel.PastExact.past_has_only_ancestors_and_keeps_roots";
    Tactics.smt_sync' 1 1
  ) end | Result.Result_Err _ -> begin assert (selection_result roots (ancestor facts roots) (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) by (
    Tactics.prune "Nickel_crdt.Edit.past";
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.prune "Nickel.PastExact.past_has_only_ancestors_and_keeps_roots";
    Tactics.smt_sync' 1 1
  ) end

let expanded_prefix (fact: Native.t_Fact) (finish: nat) (selected: ids_vec) : Type0 =
  forall(i: usize{v i < Seq.length (Alloc.Vec.impl_1__as_slice fact.f_after)}). v i < finish ==> member (Alloc.Vec.impl_1__as_slice selected) (Seq.index (Alloc.Vec.impl_1__as_slice fact.f_after) (v i))

let expansion_ok (fact: Native.t_Fact) (before: ids_vec) (next: ids_vec) : Type0 =
  Prims.l_and (retains (Alloc.Vec.impl_1__as_slice before) next) (member (Alloc.Vec.impl_1__as_slice before) fact.f_id ==> expanded_prefix fact (Seq.length (Alloc.Vec.impl_1__as_slice fact.f_after)) next)

let expansion_result (fact: Native.t_Fact) (before: ids_vec) (result: Result.t_Result ids_vec Native.t_Error) : Type0 =
  match result with | Result.Result_Ok next -> begin expansion_ok fact before next end | _ -> begin Prims.l_True end

let extend_past_covers_predecessors (fact: Native.t_Fact) (before: ids_vec) : Lemma (ensures expansion_result fact before (Native.extend_past fact before)) =
  text_past_ids_are_exact ();
  Nickel.EventGraphText.text_graph_callbacks_are_exact ();
  Nickel.EventGraphText.extend_past_is_text_call fact before;
  Nickel.PastExact.extend_past_covers_predecessors (Nickel.EventGraphText.text_graph_ops ()) fact before;
  assert (expansion_result fact before (Native.extend_past fact before)) by (
    Tactics.prune "Nickel_crdt.Edit.extend_past";
    Tactics.prune "Nickel_crdt.Event_layer.extend_past";
    Tactics.prune "Nickel.PastExact.extend_past_covers_predecessors";
    Tactics.smt_sync' 1 1
  )

let pass_prefix (facts: t_Slice Native.t_Fact) (before: ids_vec) (finish: nat) (next: ids_vec) : Type0 =
  Prims.l_and (retains (Alloc.Vec.impl_1__as_slice before) next) (forall(i: usize{v i < Seq.length facts}). v i < finish ==> expansion_ok (Seq.index facts (v i)) before next)

let pass_result (facts: t_Slice Native.t_Fact) (before: ids_vec) (result: Result.t_Result ids_vec Native.t_Error) : Type0 =
  match result with | Result.Result_Ok next -> begin pass_prefix facts before (Seq.length facts) next end | _ -> begin Prims.l_True end

let retains_member (before: ids_vec) (next: ids_vec) (id: Native.t_EventId) : Lemma (requires (retains (Alloc.Vec.impl_1__as_slice before) next /\ member (Alloc.Vec.impl_1__as_slice before) id)) (ensures member (Alloc.Vec.impl_1__as_slice next) id) =
  ()

let expansion_composes (facts: t_Slice Native.t_Fact) (before: ids_vec) (at: usize{v at < Seq.length facts}) (selected: ids_vec) (next: ids_vec) : Lemma (requires (pass_prefix facts before (v at) selected /\ expansion_ok (Seq.index facts (v at)) selected next)) (ensures pass_prefix facts before (v at + 1) next) =
  let each_id (id: Native.t_EventId) : Lemma (requires member (Alloc.Vec.impl_1__as_slice selected) id) (ensures member (Alloc.Vec.impl_1__as_slice next) id) = retains_member selected next id in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each_id);
  let prior_member (id: Native.t_EventId) : Lemma (requires member (Alloc.Vec.impl_1__as_slice before) id) (ensures member (Alloc.Vec.impl_1__as_slice selected) id) = retains_member before selected id in
  FStar.Classical.forall_intro (FStar.Classical.move_requires prior_member);
  ()

let past_pass_covers_edges (facts: t_Slice Native.t_Fact) (before: ids_vec) : Lemma (ensures pass_result facts before (Native.past_pass facts before)) =
  text_past_ids_are_exact ();
  Nickel.EventGraphText.text_graph_callbacks_are_exact ();
  Nickel.EventGraphText.past_pass_is_text_call facts before;
  Nickel.PastExact.past_pass_covers_edges (Nickel.EventGraphText.text_graph_ops ()) facts before;
  assert (pass_result facts before (Native.past_pass facts before)) by (
    Tactics.prune "Nickel_crdt.Edit.past_pass";
    Tactics.prune "Nickel_crdt.Event_layer.past_pass";
    Tactics.prune "Nickel.PastExact.past_pass_covers_edges";
    Tactics.smt_sync' 1 1
  )

let rec reachable_within (facts: facts_vec) (roots: t_Slice Native.t_EventId) (depth: nat) (id: Native.t_EventId) : Tot Type0 (decreases depth) =
  Prims.l_or (member roots id) (if depth ==? 0 then
    begin Prims.l_False end
  else
    begin exists(parent: Native.t_EventId). Prims.l_and (reachable_within facts roots (depth - 1) parent) (Nickel.EditCausal.causal_edge facts parent id) end)

let covers_depth (facts: facts_vec) (roots: t_Slice Native.t_EventId) (depth: nat) (selected: ids_vec) : Type0 =
  forall(id: Native.t_EventId). reachable_within facts roots depth id ==> member (Alloc.Vec.impl_1__as_slice selected) id

let pass_edge_is_covered (facts: facts_vec) (before: ids_vec) (next: ids_vec) (parent: Native.t_EventId) (child: Native.t_EventId) : Lemma (requires (pass_prefix (Alloc.Vec.impl_1__as_slice facts) before (Seq.length (Alloc.Vec.impl_1__as_slice facts)) next /\ member (Alloc.Vec.impl_1__as_slice before) parent /\ Nickel.EditCausal.causal_edge facts parent child)) (ensures member (Alloc.Vec.impl_1__as_slice next) child) =
  let each_fact (fact: Native.t_Fact) : Lemma (requires (fact_present (Alloc.Vec.impl_1__as_slice facts) fact /\ fact.f_id == parent)) (ensures all_ids (Alloc.Vec.impl_1__as_slice fact.f_after) (fun (id: Native.t_EventId) -> member (Alloc.Vec.impl_1__as_slice next) id)) =
    let at = find_fact_position (Alloc.Vec.impl_1__as_slice facts) fact in
    let index = mk_usize at in
    assert (v index == at);
    assert (expansion_ok (Seq.index (Alloc.Vec.impl_1__as_slice facts) (v index)) before next);
    assert (expansion_ok fact before next);
    () in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each_fact);
  ()

let pass_covers_next_depth (facts: facts_vec) (roots: t_Slice Native.t_EventId) (depth: nat) (before: ids_vec) (next: ids_vec) : Lemma (requires (covers_depth facts roots depth before /\ pass_prefix (Alloc.Vec.impl_1__as_slice facts) before (Seq.length (Alloc.Vec.impl_1__as_slice facts)) next)) (ensures covers_depth facts roots (depth + 1) next) =
  let old_member (id: Native.t_EventId) : Lemma (requires member (Alloc.Vec.impl_1__as_slice before) id) (ensures member (Alloc.Vec.impl_1__as_slice next) id) = retains_member before next id in
  FStar.Classical.forall_intro (FStar.Classical.move_requires old_member);
  let each_parent (parent: Native.t_EventId) (child: Native.t_EventId) : Lemma (requires (reachable_within facts roots depth parent /\ Nickel.EditCausal.causal_edge facts parent child)) (ensures member (Alloc.Vec.impl_1__as_slice next) child) = pass_edge_is_covered facts before next parent child in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_parent);
  let each_id (id: Native.t_EventId) : Lemma (requires reachable_within facts roots (depth + 1) id) (ensures member (Alloc.Vec.impl_1__as_slice next) id) = () in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each_id);
  ()

let depth_result (facts: facts_vec) (roots: t_Slice Native.t_EventId) (depth: nat) (result: Result.t_Result ids_vec Native.t_Error) : Type0 =
  match result with | Result.Result_Ok selected -> begin covers_depth facts roots depth selected end | _ -> begin Prims.l_True end

let rec shared_reachable_is_text (facts: facts_vec) (roots: t_Slice Native.t_EventId) (depth: nat) : Lemma (ensures forall(id: Native.t_EventId). Nickel.PastExact.reachable_within (Nickel.EventGraphText.text_graph_ops ()) (Alloc.Vec.impl_1__as_slice facts) roots depth id <==> reachable_within facts roots depth id) (decreases depth) =
  text_causal_edge_is_shared facts;
  Nickel.PastExact.reachable_within_equations (Nickel.EventGraphText.text_graph_ops ()) (Alloc.Vec.impl_1__as_slice facts) roots;
  if depth ==? 0 then
    begin () end
  else
    begin shared_reachable_is_text facts roots (depth - 1) end

let past_covers_bounded_predecessor_paths (facts: facts_vec) (roots: t_Slice Native.t_EventId) : Lemma (ensures depth_result facts roots (Seq.length (Alloc.Vec.impl_1__as_slice facts)) (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) =
  text_past_ids_are_exact ();
  Nickel.EventGraphText.text_graph_callbacks_are_exact ();
  Nickel.EventGraphText.past_is_text_call (Alloc.Vec.impl_1__as_slice facts) roots;
  shared_reachable_is_text facts roots (Seq.length (Alloc.Vec.impl_1__as_slice facts));
  Nickel.PastExact.past_covers_bounded_predecessor_paths (Nickel.EventGraphText.text_graph_ops ()) (Alloc.Vec.impl_1__as_slice facts) roots;
  assert (depth_result facts roots (Seq.length (Alloc.Vec.impl_1__as_slice facts)) (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) by (
    Tactics.prune "Nickel_crdt.Edit.past";
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.prune "Nickel.PastExact.past_covers_bounded_predecessor_paths";
    Tactics.smt_sync' 1 1
  )

let past_contains_short_paths (facts: facts_vec) (roots: t_Slice Native.t_EventId) (root: Native.t_EventId) (steps: Prims.list Native.t_EventId) (id: Native.t_EventId) : Lemma (requires (member roots root /\ Nickel.EditCausal.causal_path facts root steps id /\ List.length steps <= Seq.length (Alloc.Vec.impl_1__as_slice facts))) (ensures ((match Native.past (Alloc.Vec.impl_1__as_slice facts) roots with | Result.Result_Ok selected -> begin member (Alloc.Vec.impl_1__as_slice selected) id end | _ -> begin Prims.l_True end) <: Type0)) =
  text_past_ids_are_exact ();
  Nickel.EventGraphText.text_graph_callbacks_are_exact ();
  Nickel.EventGraphText.past_is_text_call (Alloc.Vec.impl_1__as_slice facts) roots;
  all_shared_paths_are_text facts;
  Nickel.PastExact.past_contains_short_paths (Nickel.EventGraphText.text_graph_ops ()) (Alloc.Vec.impl_1__as_slice facts) roots root steps id;
  assert (((match Native.past (Alloc.Vec.impl_1__as_slice facts) roots with | Result.Result_Ok selected -> begin member (Alloc.Vec.impl_1__as_slice selected) id end | _ -> begin Prims.l_True end) <: Type0)) by (
    Tactics.prune "Nickel_crdt.Edit.past";
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.prune "Nickel.PastExact.past_contains_short_paths";
    Tactics.smt_sync' 1 1
  )

open FStar.Fin

let fact_id_present (facts: facts_vec) (id: Native.t_EventId) : Type0 =
  exists(fact: Native.t_Fact). Prims.l_and (fact_present (Alloc.Vec.impl_1__as_slice facts) fact) (fact.f_id == id)

let parent_fact_position (facts: facts_vec) (id: Native.t_EventId{fact_id_present facts id}) : i: nat{Prims.l_and (i < Seq.length (Alloc.Vec.impl_1__as_slice facts)) ((Seq.index (Alloc.Vec.impl_1__as_slice facts) i).f_id == id)} =
  match FStar.Fin.find (Alloc.Vec.impl_1__as_slice facts) (fun (fact: Native.t_Fact) -> fact.f_id ==? id) 0 with | Some i -> begin i end | None -> begin 0 end

let rec every_path_has_short_path (facts: facts_vec) (start: Native.t_EventId) (steps: Prims.list Native.t_EventId) (finish: Native.t_EventId) : Lemma (requires Nickel.EditCausal.causal_path facts start steps finish) (ensures exists(short: Prims.list Native.t_EventId). Prims.l_and (List.length short <= Seq.length (Alloc.Vec.impl_1__as_slice facts)) (Nickel.EditCausal.causal_path facts start short finish)) (decreases List.length steps) =
  all_shared_paths_are_text facts;
  Nickel.PastExact.every_path_has_short_path (Nickel.EventGraphText.text_graph_ops ()) (Alloc.Vec.impl_1__as_slice facts) start steps finish;
  assert (exists(short: Prims.list Native.t_EventId). Prims.l_and (List.length short <= Seq.length (Alloc.Vec.impl_1__as_slice facts)) (Nickel.EditCausal.causal_path facts start short finish)) by (
    Tactics.prune "Nickel_crdt.Edit.past";
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.prune "Nickel.PastExact.every_path_has_short_path";
    Tactics.smt_sync' 1 1
  )

let past_contains_every_causal_path (facts: facts_vec) (roots: t_Slice Native.t_EventId) (root: Native.t_EventId) (steps: Prims.list Native.t_EventId) (id: Native.t_EventId) : Lemma (requires (member roots root /\ Nickel.EditCausal.causal_path facts root steps id)) (ensures ((match Native.past (Alloc.Vec.impl_1__as_slice facts) roots with | Result.Result_Ok selected -> begin member (Alloc.Vec.impl_1__as_slice selected) id end | _ -> begin Prims.l_True end) <: Type0)) =
  text_past_ids_are_exact ();
  Nickel.EventGraphText.text_graph_callbacks_are_exact ();
  Nickel.EventGraphText.past_is_text_call (Alloc.Vec.impl_1__as_slice facts) roots;
  all_shared_paths_are_text facts;
  Nickel.PastExact.past_contains_every_causal_path (Nickel.EventGraphText.text_graph_ops ()) (Alloc.Vec.impl_1__as_slice facts) roots root steps id;
  assert (((match Native.past (Alloc.Vec.impl_1__as_slice facts) roots with | Result.Result_Ok selected -> begin member (Alloc.Vec.impl_1__as_slice selected) id end | _ -> begin Prims.l_True end) <: Type0)) by (
    Tactics.prune "Nickel_crdt.Edit.past";
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.prune "Nickel.PastExact.past_contains_every_causal_path";
    Tactics.smt_sync' 1 1
  )

let exact_past_result (facts: facts_vec) (roots: t_Slice Native.t_EventId) (result: Result.t_Result ids_vec Native.t_Error) : Type0 =
  match result with | Result.Result_Ok selected -> begin forall(id: Native.t_EventId). member (Alloc.Vec.impl_1__as_slice selected) id <==> ancestor facts roots id end | _ -> begin Prims.l_True end

let successful_past_is_exact_closure (facts: facts_vec) (roots: t_Slice Native.t_EventId) : Lemma (ensures exact_past_result facts roots (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) =
  text_past_ids_are_exact ();
  Nickel.EventGraphText.text_graph_callbacks_are_exact ();
  Nickel.EventGraphText.past_is_text_call (Alloc.Vec.impl_1__as_slice facts) roots;
  all_shared_paths_are_text facts;
  Nickel.PastExact.successful_past_is_exact_closure (Nickel.EventGraphText.text_graph_ops ()) (Alloc.Vec.impl_1__as_slice facts) roots;
  match Native.past (Alloc.Vec.impl_1__as_slice facts) roots with | Result.Result_Ok selected -> begin assert (Nickel.PastExact.exact_past_result (Nickel.EventGraphText.text_graph_ops ()) (Alloc.Vec.impl_1__as_slice facts) roots (Result.Result_Ok selected)) by (
    Tactics.prune "Nickel_crdt.Edit.past";
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.prune "Nickel.PastExact.successful_past_is_exact_closure";
    Tactics.smt_sync' 1 1
  );
  Nickel.PastExact.exact_selection_members (Nickel.EventGraphText.text_graph_ops ()) (Alloc.Vec.impl_1__as_slice facts) roots selected;
  assert (exact_past_result facts roots (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) by (
    Tactics.prune "Nickel_crdt.Edit.past";
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.prune "Nickel.PastExact.successful_past_is_exact_closure";
    Tactics.smt_sync' 1 1
  ) end | Result.Result_Err _ -> begin assert (exact_past_result facts roots (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) by (
    Tactics.prune "Nickel_crdt.Edit.past";
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.prune "Nickel.PastExact.successful_past_is_exact_closure";
    Tactics.smt_sync' 1 1
  ) end