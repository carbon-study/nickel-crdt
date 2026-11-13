(* Latte generated F* view *)
module Nickel.EditPast

open Nickel.Prelude

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
  let each_push (selected: ids_vec) (id: Native.t_EventId) : Lemma (requires (selection_ok roots p selected /\ p id)) (ensures push_selection_result roots p (Native.push selected id)) = selected_push_preserves roots p selected id in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_push);
  if Native.has_event (Alloc.Vec.impl_1__as_slice before) fact.f_id then
    begin assert (member (Alloc.Vec.impl_1__as_slice before) fact.f_id) by (
      Tactics.prune "Nickel.EventGraph.membership_is_exact";
      Tactics.prune "Nickel_crdt.Edit.has_event";
      Tactics.prune "Nickel_crdt.Event_layer.has_id";
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.smt_sync' 1 1
    );
    member_satisfies (Alloc.Vec.impl_1__as_slice before) p fact.f_id;
    assert (all_ids (Alloc.Vec.impl_1__as_slice fact.f_after) p);
    Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Alloc.Vec.impl_1__len fact.f_after) (fun (_: nat) (selected: ids_vec) -> selection_ok roots p selected) (fun (selected: ids_vec) -> selected) (selection_ok roots p) (fun (_: Native.t_Error) -> Prims.l_True);
    assert (selection_result roots p (Native.extend_past fact before)) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.prune "Nickel_crdt.Edit.has_event";
      Tactics.prune "Nickel_crdt.Event_layer.has_id";
      Tactics.prune "Nickel_crdt.Edit.push";
      Tactics.prune "Nickel_crdt.Event_layer.push";
      Tactics.smt_sync' 1 1
    ) end
  else
    begin assert (selection_result roots p (Native.extend_past fact before)) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.prune "Nickel_crdt.Edit.has_event";
      Tactics.prune "Nickel_crdt.Event_layer.has_id";
      Tactics.prune "Nickel_crdt.Edit.push";
      Tactics.prune "Nickel_crdt.Event_layer.push";
      Tactics.smt_sync' 1 1
    ) end

let facts_closed (facts: t_Slice Native.t_Fact) (p: Native.t_EventId -> Type0) : Type0 =
  forall(i: usize{v i < Seq.length facts}). fact_closed (Seq.index facts (v i)) p

let past_pass_preserves (roots: t_Slice Native.t_EventId) (p: Native.t_EventId -> Type0) (facts: t_Slice Native.t_Fact) (before: ids_vec) : Lemma (requires (selection_ok roots p before /\ facts_closed facts p)) (ensures selection_result roots p (Native.past_pass facts before)) =
  Nickel.EventGraphText.text_graph_policy_is_exact ();
  let each_extend (selected: ids_vec) (i: usize{v i < Seq.length facts}) : Lemma (requires selection_ok roots p selected) (ensures selection_result roots p (Native.extend_past (Seq.index facts (v i)) selected)) = extend_past_preserves roots p (Seq.index facts (v i)) selected in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_extend);
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len facts) (fun (_: nat) (selected: ids_vec) -> selection_ok roots p selected) (fun (selected: ids_vec) -> selected) (selection_ok roots p) (fun (_: Native.t_Error) -> Prims.l_True);
  assert (selection_result roots p (Native.past_pass facts before)) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel_crdt.Edit.extend_past";
    Tactics.prune "Nickel_crdt.Event_layer.extend_past";
    Tactics.smt_sync' 1 1
  )

let initial_selection_is_valid (roots: t_Slice Native.t_EventId) (p: Native.t_EventId -> Type0) : Lemma (requires all_ids roots p) (ensures selection_ok roots p (Alloc.Slice.impl__to_vec roots)) =
  ()

let past_stays_in_closed_set (facts: t_Slice Native.t_Fact) (roots: t_Slice Native.t_EventId) (p: Native.t_EventId -> Type0) : Lemma (requires (all_ids roots p /\ facts_closed facts p)) (ensures selection_result roots p (Native.past facts roots)) =
  Nickel.EventGraphText.text_graph_policy_is_exact ();
  initial_selection_is_valid roots p;
  let each_pass (selected: ids_vec) : Lemma (requires selection_ok roots p selected) (ensures selection_result roots p (Native.past_pass facts selected)) = past_pass_preserves roots p facts selected in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each_pass);
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len facts) (fun (_: nat) (state: bool & ids_vec) -> selection_ok roots p state._2) (fun (state: bool & ids_vec) -> state._2) (selection_ok roots p) (fun (_: Native.t_Error) -> Prims.l_True);
  assert (selection_result roots p (Native.past facts roots)) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel_crdt.Edit.past_pass";
    Tactics.prune "Nickel_crdt.Event_layer.past_pass";
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

let ancestor_roots_and_edges (facts: facts_vec) (roots: t_Slice Native.t_EventId) : Lemma (ensures Prims.l_and (all_ids roots (ancestor facts roots)) (facts_closed (Alloc.Vec.impl_1__as_slice facts) (ancestor facts roots))) =
  let each_root (i: usize{v i < Seq.length roots}) : Lemma (ensures ancestor facts roots (Seq.index roots (v i))) =
    assert (member roots (Seq.index roots (v i)));
    assert (Nickel.EditCausal.causal_path facts (Seq.index roots (v i)) Prims.Nil (Seq.index roots (v i)));
    () in
  FStar.Classical.forall_intro each_root;
  let each_fact (i: usize{v i < Seq.length (Alloc.Vec.impl_1__as_slice facts)}) : Lemma (ensures fact_closed (Seq.index (Alloc.Vec.impl_1__as_slice facts) (v i)) (ancestor facts roots)) =
    let fact = Seq.index (Alloc.Vec.impl_1__as_slice facts) (v i) in
    let each_child (j: usize{v j < Seq.length (Alloc.Vec.impl_1__as_slice fact.f_after)}) : Lemma (requires ancestor facts roots fact.f_id) (ensures ancestor facts roots (Seq.index (Alloc.Vec.impl_1__as_slice fact.f_after) (v j))) =
      assert (Nickel.EditCausal.causal_edge facts fact.f_id (Seq.index (Alloc.Vec.impl_1__as_slice fact.f_after) (v j)));
      ancestor_follows_edge facts roots fact.f_id (Seq.index (Alloc.Vec.impl_1__as_slice fact.f_after) (v j)) in
    FStar.Classical.forall_intro (FStar.Classical.move_requires each_child);
    () in
  FStar.Classical.forall_intro each_fact;
  ()

let past_has_only_ancestors_and_keeps_roots (facts: facts_vec) (roots: t_Slice Native.t_EventId) : Lemma (ensures selection_result roots (ancestor facts roots) (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) =
  ancestor_roots_and_edges facts roots;
  past_stays_in_closed_set (Alloc.Vec.impl_1__as_slice facts) roots (ancestor facts roots);
  assert (selection_result roots (ancestor facts roots) (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) by (
    Tactics.prune "Nickel_crdt.Edit.past";
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.smt_sync' 1 1
  )

let expanded_prefix (fact: Native.t_Fact) (finish: nat) (selected: ids_vec) : Type0 =
  forall(i: usize{v i < Seq.length (Alloc.Vec.impl_1__as_slice fact.f_after)}). v i < finish ==> member (Alloc.Vec.impl_1__as_slice selected) (Seq.index (Alloc.Vec.impl_1__as_slice fact.f_after) (v i))

let expansion_ok (fact: Native.t_Fact) (before: ids_vec) (next: ids_vec) : Type0 =
  Prims.l_and (retains (Alloc.Vec.impl_1__as_slice before) next) (member (Alloc.Vec.impl_1__as_slice before) fact.f_id ==> expanded_prefix fact (Seq.length (Alloc.Vec.impl_1__as_slice fact.f_after)) next)

let expansion_result (fact: Native.t_Fact) (before: ids_vec) (result: Result.t_Result ids_vec Native.t_Error) : Type0 =
  match result with | Result.Result_Ok next -> begin expansion_ok fact before next end | _ -> begin Prims.l_True end

let extend_past_covers_predecessors (fact: Native.t_Fact) (before: ids_vec) : Lemma (ensures expansion_result fact before (Native.extend_past fact before)) =
  Nickel.EventGraphText.text_graph_policy_is_exact ();
  Nickel.EventGraphText.text_graph_callbacks_are_exact ();
  let membership_boolean (ids: t_Slice Native.t_EventId) (id: Native.t_EventId) : Lemma (ensures Prims.l_or (Native.has_event ids id == true) (Native.has_event ids id == false)) [SMTPat (Native.has_event ids id)] = () in
  extend_past_preserves (Alloc.Vec.impl_1__as_slice before) (fun (_: Native.t_EventId) -> Prims.l_True) fact before;
  let each_push (at: usize{v at < Seq.length (Alloc.Vec.impl_1__as_slice fact.f_after)}) (selected: ids_vec) : Lemma (requires expanded_prefix fact (v at) selected) (ensures ((match Native.push selected (Seq.index (Alloc.Vec.impl_1__as_slice fact.f_after) (v at)) with | (next, Result.Result_Ok _) -> begin expanded_prefix fact (v at + 1) next end | _ -> begin Prims.l_True end) <: Type0)) =
    push_result_is_exact selected (Seq.index (Alloc.Vec.impl_1__as_slice fact.f_after) (v at));
    assert (((match Native.push selected (Seq.index (Alloc.Vec.impl_1__as_slice fact.f_after) (v at)) with | (next, Result.Result_Ok _) -> begin expanded_prefix fact (v at + 1) next end | _ -> begin Prims.l_True end) <: Type0)) by (
      Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
      Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
      Tactics.prune "Nickel_crdt.Event_layer.event_ops";
      Tactics.prune "Nickel_crdt.Edit.push";
      Tactics.prune "Nickel_crdt.Event_layer.push";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_push);
  let skip_existing (at: usize{v at < Seq.length (Alloc.Vec.impl_1__as_slice fact.f_after)}) (selected: ids_vec) : Lemma (requires (expanded_prefix fact (v at) selected /\ Native.has_event (Alloc.Vec.impl_1__as_slice selected) (Seq.index (Alloc.Vec.impl_1__as_slice fact.f_after) (v at)) == true)) (ensures expanded_prefix fact (v at + 1) selected) =
    event_membership_is_exact (Alloc.Vec.impl_1__as_slice selected) (Seq.index (Alloc.Vec.impl_1__as_slice fact.f_after) (v at));
    () in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 skip_existing);
  if Native.has_event (Alloc.Vec.impl_1__as_slice before) fact.f_id then
    begin Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Alloc.Vec.impl_1__len fact.f_after) (fun (at: nat) (selected: ids_vec) -> expanded_prefix fact at selected) (fun (selected: ids_vec) -> selected) (fun (selected: ids_vec) -> expanded_prefix fact (Seq.length (Alloc.Vec.impl_1__as_slice fact.f_after)) selected) (fun (_: Native.t_Error) -> Prims.l_True);
    assert (expansion_result fact before (Native.extend_past fact before)) by (
      Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
      Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
      Tactics.prune "Nickel_crdt.Event_layer.event_ops";
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.prune "Nickel_crdt.Edit.has_event";
      Tactics.prune "Nickel_crdt.Event_layer.has_id";
      Tactics.prune "Nickel_crdt.Edit.push";
      Tactics.prune "Nickel_crdt.Event_layer.push";
      Tactics.smt_sync' 1 1
    ) end
  else
    begin assert (expansion_result fact before (Native.extend_past fact before)) by (
      Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
      Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
      Tactics.prune "Nickel_crdt.Event_layer.event_ops";
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.prune "Nickel_crdt.Edit.has_event";
      Tactics.prune "Nickel_crdt.Event_layer.has_id";
      Tactics.prune "Nickel_crdt.Edit.push";
      Tactics.prune "Nickel_crdt.Event_layer.push";
      Tactics.smt_sync' 1 1
    ) end

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
  Nickel.EventGraphText.text_graph_policy_is_exact ();
  let each_extend (selected: ids_vec) (at: usize{v at < Seq.length facts}) : Lemma (requires pass_prefix facts before (v at) selected) (ensures ((match Native.extend_past (Seq.index facts (v at)) selected with | Result.Result_Ok next -> begin pass_prefix facts before (v at + 1) next end | _ -> begin Prims.l_True end) <: Type0)) =
    extend_past_covers_predecessors (Seq.index facts (v at)) selected;
    let each_next (next: ids_vec) : Lemma (requires expansion_ok (Seq.index facts (v at)) selected next) (ensures pass_prefix facts before (v at + 1) next) = expansion_composes facts before at selected next in
    FStar.Classical.forall_intro (FStar.Classical.move_requires each_next);
    assert (((match Native.extend_past (Seq.index facts (v at)) selected with | Result.Result_Ok next -> begin pass_prefix facts before (v at + 1) next end | _ -> begin Prims.l_True end) <: Type0)) by (
      Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
      Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
      Tactics.prune "Nickel_crdt.Event_layer.event_ops";
      Tactics.prune "Nickel_crdt.Edit.extend_past";
      Tactics.prune "Nickel_crdt.Event_layer.extend_past";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_extend);
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len facts) (pass_prefix facts before) (fun (selected: ids_vec) -> selected) (fun (next: ids_vec) -> pass_prefix facts before (Seq.length facts) next) (fun (_: Native.t_Error) -> Prims.l_True);
  assert (pass_result facts before (Native.past_pass facts before)) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel_crdt.Edit.extend_past";
    Tactics.prune "Nickel_crdt.Event_layer.extend_past";
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

let prefix_of (before: ids_vec) (next: ids_vec) : Type0 =
  Prims.l_and (Seq.length (Alloc.Vec.impl_1__as_slice before) <= Seq.length (Alloc.Vec.impl_1__as_slice next)) (forall(i: nat{Prims.l_and (i < Seq.length (Alloc.Vec.impl_1__as_slice before)) (i < Seq.length (Alloc.Vec.impl_1__as_slice next))}). Seq.index (Alloc.Vec.impl_1__as_slice next) i == Seq.index (Alloc.Vec.impl_1__as_slice before) i)

let prefix_result (before: ids_vec) (result: Result.t_Result ids_vec Native.t_Error) : Type0 =
  match result with | Result.Result_Ok next -> begin prefix_of before next end | _ -> begin Prims.l_True end

let prefix_trans (a: ids_vec) (b: ids_vec) (c: ids_vec) : Lemma (requires (prefix_of a b /\ prefix_of b c)) (ensures prefix_of a c) =
  ()

let extend_past_appends (fact: Native.t_Fact) (before: ids_vec) : Lemma (ensures prefix_result before (Native.extend_past fact before)) =
  Nickel.EventGraphText.text_graph_policy_is_exact ();
  Nickel.EventGraphText.text_graph_callbacks_are_exact ();
  let each_push (at: usize{v at < Seq.length (Alloc.Vec.impl_1__as_slice fact.f_after)}) (selected: ids_vec) : Lemma (requires prefix_of before selected) (ensures ((match Native.push selected (Seq.index (Alloc.Vec.impl_1__as_slice fact.f_after) (v at)) with | (next, Result.Result_Ok _) -> begin prefix_of before next end | _ -> begin Prims.l_True end) <: Type0)) =
    push_result_is_exact selected (Seq.index (Alloc.Vec.impl_1__as_slice fact.f_after) (v at));
    assert (((match Native.push selected (Seq.index (Alloc.Vec.impl_1__as_slice fact.f_after) (v at)) with | (next, Result.Result_Ok _) -> begin prefix_of before next end | _ -> begin Prims.l_True end) <: Type0)) by (
      Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
      Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
      Tactics.prune "Nickel_crdt.Event_layer.event_ops";
      Tactics.prune "Nickel_crdt.Edit.push";
      Tactics.prune "Nickel_crdt.Event_layer.push";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_push);
  if Native.has_event (Alloc.Vec.impl_1__as_slice before) fact.f_id then
    begin Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Alloc.Vec.impl_1__len fact.f_after) (fun (_: nat) (selected: ids_vec) -> prefix_of before selected) (fun (selected: ids_vec) -> selected) (prefix_of before) (fun (_: Native.t_Error) -> Prims.l_True);
    assert (prefix_result before (Native.extend_past fact before)) by (
      Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
      Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
      Tactics.prune "Nickel_crdt.Event_layer.event_ops";
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.prune "Nickel_crdt.Edit.has_event";
      Tactics.prune "Nickel_crdt.Event_layer.has_id";
      Tactics.prune "Nickel_crdt.Edit.push";
      Tactics.prune "Nickel_crdt.Event_layer.push";
      Tactics.smt_sync' 1 1
    ) end
  else
    begin assert (prefix_result before (Native.extend_past fact before)) by (
      Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
      Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
      Tactics.prune "Nickel_crdt.Event_layer.event_ops";
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.prune "Nickel_crdt.Edit.has_event";
      Tactics.prune "Nickel_crdt.Event_layer.has_id";
      Tactics.prune "Nickel_crdt.Edit.push";
      Tactics.prune "Nickel_crdt.Event_layer.push";
      Tactics.smt_sync' 1 1
    ) end

let past_pass_appends (facts: t_Slice Native.t_Fact) (before: ids_vec) : Lemma (ensures prefix_result before (Native.past_pass facts before)) =
  Nickel.EventGraphText.text_graph_policy_is_exact ();
  let each_extend (selected: ids_vec) (at: usize{v at < Seq.length facts}) : Lemma (requires prefix_of before selected) (ensures prefix_result before (Native.extend_past (Seq.index facts (v at)) selected)) =
    extend_past_appends (Seq.index facts (v at)) selected;
    assert (prefix_result selected (Native.extend_past (Seq.index facts (v at)) selected)) by (
      Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
      Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
      Tactics.prune "Nickel_crdt.Event_layer.event_ops";
      Tactics.prune "Nickel_crdt.Edit.extend_past";
      Tactics.prune "Nickel_crdt.Event_layer.extend_past";
      Tactics.smt_sync' 1 1
    );
    match Native.extend_past (Seq.index facts (v at)) selected with | Result.Result_Ok next -> begin prefix_trans before selected next end | Result.Result_Err _ -> begin () end in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_extend);
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len facts) (fun (_: nat) (selected: ids_vec) -> prefix_of before selected) (fun (selected: ids_vec) -> selected) (prefix_of before) (fun (_: Native.t_Error) -> Prims.l_True);
  assert (prefix_result before (Native.past_pass facts before)) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel_crdt.Edit.extend_past";
    Tactics.prune "Nickel_crdt.Event_layer.extend_past";
    Tactics.smt_sync' 1 1
  )

let same_length_extension_is_closed (facts: t_Slice Native.t_Fact) (before: ids_vec) (next: ids_vec) : Lemma (requires (pass_prefix facts before (Seq.length facts) next /\ prefix_of before next /\ Seq.length (Alloc.Vec.impl_1__as_slice next) == Seq.length (Alloc.Vec.impl_1__as_slice before))) (ensures pass_prefix facts next (Seq.length facts) next) =
  let back (id: Native.t_EventId) : Lemma (requires member (Alloc.Vec.impl_1__as_slice next) id) (ensures member (Alloc.Vec.impl_1__as_slice before) id) = () in
  FStar.Classical.forall_intro (FStar.Classical.move_requires back);
  let own (i: usize{v i < Seq.length (Alloc.Vec.impl_1__as_slice next)}) : Lemma (ensures member (Alloc.Vec.impl_1__as_slice next) (Seq.index (Alloc.Vec.impl_1__as_slice next) (v i))) = () in
  FStar.Classical.forall_intro own;
  ()

let closed_depth (facts: facts_vec) (roots: t_Slice Native.t_EventId) (depth: nat) (state: bool & ids_vec) : Type0 =
  Prims.l_and (covers_depth facts roots depth state._2) (state._1 == true ==> pass_prefix (Alloc.Vec.impl_1__as_slice facts) state._2 (Seq.length (Alloc.Vec.impl_1__as_slice facts)) state._2)

let open_pass_result (facts: facts_vec) (roots: t_Slice Native.t_EventId) (depth: nat) (selected: ids_vec) (result: Result.t_Result ids_vec Native.t_Error) : Lemma (requires (covers_depth facts roots depth selected /\ pass_result (Alloc.Vec.impl_1__as_slice facts) selected result /\ prefix_result selected result)) (ensures ((match result with | Result.Result_Ok next -> begin Prims.l_and (covers_depth facts roots (depth + 1) next) (v (Alloc.Vec.impl_1__len next) == v (Alloc.Vec.impl_1__len selected) ==> pass_prefix (Alloc.Vec.impl_1__as_slice facts) next (Seq.length (Alloc.Vec.impl_1__as_slice facts)) next) end | _ -> begin Prims.l_True end) <: Type0)) =
  match result with | Result.Result_Ok next -> begin pass_covers_next_depth facts roots depth selected next;
  if v (Alloc.Vec.impl_1__len next) ==? v (Alloc.Vec.impl_1__len selected) then
    begin same_length_extension_is_closed (Alloc.Vec.impl_1__as_slice facts) selected next end
  else
    begin () end end | Result.Result_Err _ -> begin () end

let open_pass_covers (facts: facts_vec) (roots: t_Slice Native.t_EventId) (depth: nat) (selected: ids_vec) : Lemma (requires covers_depth facts roots depth selected) (ensures ((match Native.past_pass (Alloc.Vec.impl_1__as_slice facts) selected with | Result.Result_Ok next -> begin Prims.l_and (covers_depth facts roots (depth + 1) next) (v (Alloc.Vec.impl_1__len next) == v (Alloc.Vec.impl_1__len selected) ==> pass_prefix (Alloc.Vec.impl_1__as_slice facts) next (Seq.length (Alloc.Vec.impl_1__as_slice facts)) next) end | _ -> begin Prims.l_True end) <: Type0)) =
  past_pass_covers_edges (Alloc.Vec.impl_1__as_slice facts) selected;
  assert (pass_result (Alloc.Vec.impl_1__as_slice facts) selected (Native.past_pass (Alloc.Vec.impl_1__as_slice facts) selected)) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.prune "Nickel_crdt.Edit.past_pass";
    Tactics.prune "Nickel_crdt.Event_layer.past_pass";
    Tactics.smt_sync' 1 1
  );
  past_pass_appends (Alloc.Vec.impl_1__as_slice facts) selected;
  assert (prefix_result selected (Native.past_pass (Alloc.Vec.impl_1__as_slice facts) selected)) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.prune "Nickel_crdt.Edit.past_pass";
    Tactics.prune "Nickel_crdt.Event_layer.past_pass";
    Tactics.smt_sync' 1 1
  );
  open_pass_result facts roots depth selected (Native.past_pass (Alloc.Vec.impl_1__as_slice facts) selected)

let closed_pass_covers (facts: facts_vec) (roots: t_Slice Native.t_EventId) (depth: nat) (selected: ids_vec) : Lemma (requires (covers_depth facts roots depth selected /\ pass_prefix (Alloc.Vec.impl_1__as_slice facts) selected (Seq.length (Alloc.Vec.impl_1__as_slice facts)) selected)) (ensures covers_depth facts roots (depth + 1) selected) =
  pass_covers_next_depth facts roots depth selected selected

let past_covers_bounded_predecessor_paths (facts: facts_vec) (roots: t_Slice Native.t_EventId) : Lemma (ensures depth_result facts roots (Seq.length (Alloc.Vec.impl_1__as_slice facts)) (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) =
  Nickel.EventGraphText.text_graph_policy_is_exact ();
  let each_open (selected: ids_vec) (at: nat) : Lemma (requires covers_depth facts roots at selected) (ensures ((match Native.past_pass (Alloc.Vec.impl_1__as_slice facts) selected with | Result.Result_Ok next -> begin Prims.l_and (covers_depth facts roots (at + 1) next) (v (Alloc.Vec.impl_1__len next) == v (Alloc.Vec.impl_1__len selected) ==> pass_prefix (Alloc.Vec.impl_1__as_slice facts) next (Seq.length (Alloc.Vec.impl_1__as_slice facts)) next) end | _ -> begin Prims.l_True end) <: Type0)) =
    open_pass_covers facts roots at selected;
    assert (((match Native.past_pass (Alloc.Vec.impl_1__as_slice facts) selected with | Result.Result_Ok next -> begin Prims.l_and (covers_depth facts roots (at + 1) next) (v (Alloc.Vec.impl_1__len next) == v (Alloc.Vec.impl_1__len selected) ==> pass_prefix (Alloc.Vec.impl_1__as_slice facts) next (Seq.length (Alloc.Vec.impl_1__as_slice facts)) next) end | _ -> begin Prims.l_True end) <: Type0)) by (
      Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
      Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
      Tactics.prune "Nickel_crdt.Event_layer.event_ops";
      Tactics.prune "Nickel_crdt.Edit.past_pass";
      Tactics.prune "Nickel_crdt.Event_layer.past_pass";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_open);
  let each_closed (selected: ids_vec) (at: nat) : Lemma (requires (covers_depth facts roots at selected /\ pass_prefix (Alloc.Vec.impl_1__as_slice facts) selected (Seq.length (Alloc.Vec.impl_1__as_slice facts)) selected)) (ensures covers_depth facts roots (at + 1) selected) = closed_pass_covers facts roots at selected in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_closed);
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Alloc.Vec.impl_1__len facts) (closed_depth facts roots) (fun (state: bool & ids_vec) -> state._2) (covers_depth facts roots (Seq.length (Alloc.Vec.impl_1__as_slice facts))) (fun (_: Native.t_Error) -> Prims.l_True);
  assert (depth_result facts roots (Seq.length (Alloc.Vec.impl_1__as_slice facts)) (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel_crdt.Edit.past_pass";
    Tactics.prune "Nickel_crdt.Event_layer.past_pass";
    Tactics.smt_sync' 1 1
  )

let rec path_extends_reach (facts: facts_vec) (roots: t_Slice Native.t_EventId) (depth: nat) (start: Native.t_EventId) (steps: Prims.list Native.t_EventId) (finish: Native.t_EventId) : Lemma (requires (reachable_within facts roots depth start /\ Nickel.EditCausal.causal_path facts start steps finish)) (ensures reachable_within facts roots (depth + List.length steps) finish) (decreases steps) =
  match steps with | Prims.Nil -> begin () end | Prims.Cons next rest -> begin assert (reachable_within facts roots (depth + 1) next);
  path_extends_reach facts roots (depth + 1) next rest finish end

let rec reach_allows_more_edges (facts: facts_vec) (roots: t_Slice Native.t_EventId) (depth: nat) (extra: nat) (id: Native.t_EventId) : Lemma (requires reachable_within facts roots depth id) (ensures reachable_within facts roots (depth + extra) id) (decreases depth) =
  if depth ==? 0 then
    begin () end
  else
    begin let each_parent (parent: Native.t_EventId) : Lemma (requires (reachable_within facts roots (depth - 1) parent /\ Nickel.EditCausal.causal_edge facts parent id)) (ensures reachable_within facts roots (depth + extra) id) =
      reach_allows_more_edges facts roots (depth - 1) extra parent;
      () in
    FStar.Classical.forall_intro (FStar.Classical.move_requires each_parent);
    () end

let past_contains_short_paths (facts: facts_vec) (roots: t_Slice Native.t_EventId) (root: Native.t_EventId) (steps: Prims.list Native.t_EventId) (id: Native.t_EventId) : Lemma (requires (member roots root /\ Nickel.EditCausal.causal_path facts root steps id /\ List.length steps <= Seq.length (Alloc.Vec.impl_1__as_slice facts))) (ensures ((match Native.past (Alloc.Vec.impl_1__as_slice facts) roots with | Result.Result_Ok selected -> begin member (Alloc.Vec.impl_1__as_slice selected) id end | _ -> begin Prims.l_True end) <: Type0)) =
  path_extends_reach facts roots 0 root steps id;
  reach_allows_more_edges facts roots (List.length steps) (Seq.length (Alloc.Vec.impl_1__as_slice facts) - List.length steps) id;
  past_covers_bounded_predecessor_paths facts roots;
  assert (((match Native.past (Alloc.Vec.impl_1__as_slice facts) roots with | Result.Result_Ok selected -> begin member (Alloc.Vec.impl_1__as_slice selected) id end | _ -> begin Prims.l_True end) <: Type0)) by (
    Tactics.prune "Nickel_crdt.Edit.past";
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.smt_sync' 1 1
  )

open FStar.Fin

let rec path_node (start: Native.t_EventId) (steps: Prims.list Native.t_EventId) (at: nat{at <= List.length steps}) : Tot Native.t_EventId (decreases steps) =
  match steps with | Prims.Nil -> begin start end | Prims.Cons next rest -> begin if at ==? 0 then
    begin start end
  else
    begin path_node next rest (at - 1) end end

let rec drop_edges (steps: Prims.list Native.t_EventId) (count: nat{count <= List.length steps}) : Tot (Prims.list Native.t_EventId) (decreases steps) =
  if count ==? 0 then
    begin steps end
  else
    begin match steps with | Prims.Nil -> begin Prims.Nil end | Prims.Cons _ rest -> begin drop_edges rest (count - 1) end end

let rec cut_path_loop (steps: Prims.list Native.t_EventId) (first: nat) (last: nat{Prims.l_and (first < last) (last <= List.length steps)}) : Tot (Prims.list Native.t_EventId) (decreases steps) =
  if first ==? 0 then
    begin drop_edges steps last end
  else
    begin match steps with | Prims.Nil -> begin Prims.Nil end | Prims.Cons next rest -> begin Prims.Cons next (cut_path_loop rest (first - 1) (last - 1)) end end

let rec dropped_edge_count (steps: Prims.list Native.t_EventId) (count: nat{count <= List.length steps}) : Lemma (ensures List.length (drop_edges steps count) == List.length steps - count) (decreases steps) =
  if count ==? 0 then
    begin () end
  else
    begin match steps with | Prims.Nil -> begin () end | Prims.Cons _ rest -> begin dropped_edge_count rest (count - 1) end end

let rec cut_path_is_shorter (steps: Prims.list Native.t_EventId) (first: nat) (last: nat{Prims.l_and (first < last) (last <= List.length steps)}) : Lemma (ensures Prims.l_and (List.length (cut_path_loop steps first last) == List.length steps - last + first) (List.length (cut_path_loop steps first last) < List.length steps)) (decreases steps) =
  if first ==? 0 then
    begin dropped_edge_count steps last end
  else
    begin match steps with | Prims.Nil -> begin () end | Prims.Cons _ rest -> begin cut_path_is_shorter rest (first - 1) (last - 1) end end

let rec dropped_path_starts_at_node (facts: facts_vec) (start: Native.t_EventId) (steps: Prims.list Native.t_EventId) (finish: Native.t_EventId) (count: nat{count <= List.length steps}) : Lemma (requires Nickel.EditCausal.causal_path facts start steps finish) (ensures Nickel.EditCausal.causal_path facts (path_node start steps count) (drop_edges steps count) finish) (decreases steps) =
  if count ==? 0 then
    begin () end
  else
    begin match steps with | Prims.Nil -> begin () end | Prims.Cons next rest -> begin dropped_path_starts_at_node facts next rest finish (count - 1) end end

let rec cutting_repeated_node_preserves_path (facts: facts_vec) (start: Native.t_EventId) (steps: Prims.list Native.t_EventId) (finish: Native.t_EventId) (first: nat) (last: nat{Prims.l_and (first < last) (last <= List.length steps)}) : Lemma (requires (Nickel.EditCausal.causal_path facts start steps finish /\ path_node start steps first == path_node start steps last)) (ensures Nickel.EditCausal.causal_path facts start (cut_path_loop steps first last) finish) (decreases steps) =
  if first ==? 0 then
    begin dropped_path_starts_at_node facts start steps finish last end
  else
    begin match steps with | Prims.Nil -> begin () end | Prims.Cons next rest -> begin cutting_repeated_node_preserves_path facts next rest finish (first - 1) (last - 1) end end

let fact_id_present (facts: facts_vec) (id: Native.t_EventId) : Type0 =
  exists(fact: Native.t_Fact). Prims.l_and (fact_present (Alloc.Vec.impl_1__as_slice facts) fact) (fact.f_id == id)

let rec path_parent_is_present (facts: facts_vec) (start: Native.t_EventId) (steps: Prims.list Native.t_EventId) (finish: Native.t_EventId) (at: nat{at < List.length steps}) : Lemma (requires Nickel.EditCausal.causal_path facts start steps finish) (ensures fact_id_present facts (path_node start steps at)) (decreases steps) =
  match steps with | Prims.Nil -> begin () end | Prims.Cons next rest -> begin if at ==? 0 then
    begin () end
  else
    begin path_parent_is_present facts next rest finish (at - 1) end end

let parent_fact_position (facts: facts_vec) (id: Native.t_EventId{fact_id_present facts id}) : i: nat{Prims.l_and (i < Seq.length (Alloc.Vec.impl_1__as_slice facts)) ((Seq.index (Alloc.Vec.impl_1__as_slice facts) i).f_id == id)} =
  match FStar.Fin.find (Alloc.Vec.impl_1__as_slice facts) (fun (fact: Native.t_Fact) -> fact.f_id ==? id) 0 with | Some i -> begin i end | None -> begin 0 end

let path_parent_position (facts: facts_vec) (start: Native.t_EventId) (finish: Native.t_EventId) (steps: Prims.list Native.t_EventId{Nickel.EditCausal.causal_path facts start steps finish}) (at: nat{at < List.length steps}) : position: FStar.Fin.under (Seq.length (Alloc.Vec.impl_1__as_slice facts)){(Seq.index (Alloc.Vec.impl_1__as_slice facts) position).f_id == path_node start steps at} =
  path_parent_is_present facts start steps finish at;
  parent_fact_position facts (path_node start steps at)

let rec every_path_has_short_path (facts: facts_vec) (start: Native.t_EventId) (steps: Prims.list Native.t_EventId) (finish: Native.t_EventId) : Lemma (requires Nickel.EditCausal.causal_path facts start steps finish) (ensures exists(short: Prims.list Native.t_EventId). Prims.l_and (List.length short <= Seq.length (Alloc.Vec.impl_1__as_slice facts)) (Nickel.EditCausal.causal_path facts start short finish)) (decreases List.length steps) =
  let count = Seq.length (Alloc.Vec.impl_1__as_slice facts) in
  if List.length steps <= count then
    begin assert (Prims.l_and (List.length steps <= count) (Nickel.EditCausal.causal_path facts start steps finish));
    () end
  else
    begin if count ==? 0 then
      begin path_parent_is_present facts start steps finish 0;
      let position = parent_fact_position facts start in
      assert (position < count);
      () end
    else
      begin let position = path_parent_position facts start finish steps in
      let positions = Seq.init (count + 1) position in
      Seq.lemma_init_len (count + 1) position;
      Seq.init_index (count + 1) position;
      match FStar.Fin.pigeonhole positions with | (i, j) -> begin assert (Prims.l_and (i < j) (j < count + 1));
      assert (position i == position j);
      assert (path_node start steps i == path_node start steps j);
      cutting_repeated_node_preserves_path facts start steps finish i j;
      cut_path_is_shorter steps i j;
      let shorter = cut_path_loop steps i j in
      every_path_has_short_path facts start shorter finish end end end

let past_contains_every_causal_path (facts: facts_vec) (roots: t_Slice Native.t_EventId) (root: Native.t_EventId) (steps: Prims.list Native.t_EventId) (id: Native.t_EventId) : Lemma (requires (member roots root /\ Nickel.EditCausal.causal_path facts root steps id)) (ensures ((match Native.past (Alloc.Vec.impl_1__as_slice facts) roots with | Result.Result_Ok selected -> begin member (Alloc.Vec.impl_1__as_slice selected) id end | _ -> begin Prims.l_True end) <: Type0)) =
  every_path_has_short_path facts root steps id;
  let each_short (short: Prims.list Native.t_EventId) : Lemma (requires (List.length short <= Seq.length (Alloc.Vec.impl_1__as_slice facts) /\ Nickel.EditCausal.causal_path facts root short id)) (ensures ((match Native.past (Alloc.Vec.impl_1__as_slice facts) roots with | Result.Result_Ok selected -> begin member (Alloc.Vec.impl_1__as_slice selected) id end | _ -> begin Prims.l_True end) <: Type0)) = past_contains_short_paths facts roots root short id in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each_short);
  assert (((match Native.past (Alloc.Vec.impl_1__as_slice facts) roots with | Result.Result_Ok selected -> begin member (Alloc.Vec.impl_1__as_slice selected) id end | _ -> begin Prims.l_True end) <: Type0)) by (
    Tactics.prune "Nickel_crdt.Edit.past";
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.smt_sync' 1 1
  )

let exact_past_result (facts: facts_vec) (roots: t_Slice Native.t_EventId) (result: Result.t_Result ids_vec Native.t_Error) : Type0 =
  match result with | Result.Result_Ok selected -> begin forall(id: Native.t_EventId). member (Alloc.Vec.impl_1__as_slice selected) id <==> ancestor facts roots id end | _ -> begin Prims.l_True end

let successful_past_is_exact_closure (facts: facts_vec) (roots: t_Slice Native.t_EventId) : Lemma (ensures exact_past_result facts roots (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) =
  past_has_only_ancestors_and_keeps_roots facts roots;
  match Native.past (Alloc.Vec.impl_1__as_slice facts) roots with | Result.Result_Ok selected -> begin let each_id (id: Native.t_EventId) : Lemma (ensures member (Alloc.Vec.impl_1__as_slice selected) id <==> ancestor facts roots id) =
    let each_selected () : Lemma (requires member (Alloc.Vec.impl_1__as_slice selected) id) (ensures ancestor facts roots id) = member_satisfies (Alloc.Vec.impl_1__as_slice selected) (ancestor facts roots) id in
    FStar.Classical.move_requires each_selected ();
    let each_path (root: Native.t_EventId) (steps: Prims.list Native.t_EventId) : Lemma (requires (member roots root /\ Nickel.EditCausal.causal_path facts root steps id)) (ensures member (Alloc.Vec.impl_1__as_slice selected) id) =
      past_contains_every_causal_path facts roots root steps id;
      assert (member (Alloc.Vec.impl_1__as_slice selected) id) by (
        Tactics.prune "Nickel_crdt.Edit.past";
        Tactics.prune "Nickel_crdt.Event_layer.past";
        Tactics.smt_sync' 1 1
      ) in
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_path);
    () in
  FStar.Classical.forall_intro each_id;
  assert (exact_past_result facts roots (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) by (
    Tactics.prune "Nickel_crdt.Edit.past";
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.smt_sync' 1 1
  ) end | Result.Result_Err _ -> begin assert (exact_past_result facts roots (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) by (
    Tactics.prune "Nickel_crdt.Edit.past";
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.smt_sync' 1 1
  ) end