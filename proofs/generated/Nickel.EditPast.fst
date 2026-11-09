(* Latte generated F* view *)
module Nickel.EditPast

open Nickel.Prelude

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
  Nickel.LoopUtil.preserve_any (mk_usize 0) (Core_models.Slice.impl__len ids) (fun (at: nat) (_: unit) -> absent_prefix ids id at) (fun (_: unit) -> Prims.l_not (member ids id)) (fun (b: bool) -> Prims.l_and (b == true) (member ids id));
  assert (Native.has_event ids id == true <==> member ids id) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
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
    Tactics.smt_sync' 1 1
  )

let fact_closed (fact: Native.t_Fact) (p: Native.t_EventId -> Type0) : Type0 =
  p fact.f_id ==> all_ids (Alloc.Vec.impl_1__as_slice fact.f_after) p

let extend_past_preserves (roots: t_Slice Native.t_EventId) (p: Native.t_EventId -> Type0) (fact: Native.t_Fact) (before: ids_vec) : Lemma (requires (selection_ok roots p before /\ fact_closed fact p)) (ensures selection_result roots p (Native.extend_past fact before)) =
  let each_push (selected: ids_vec) (id: Native.t_EventId) : Lemma (requires (selection_ok roots p selected /\ p id)) (ensures push_selection_result roots p (Native.push selected id)) = selected_push_preserves roots p selected id in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_push);
  if Native.has_event (Alloc.Vec.impl_1__as_slice before) fact.f_id then
    begin member_satisfies (Alloc.Vec.impl_1__as_slice before) p fact.f_id;
    assert (all_ids (Alloc.Vec.impl_1__as_slice fact.f_after) p);
    Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Alloc.Vec.impl_1__len fact.f_after) (fun (_: nat) (selected: ids_vec) -> selection_ok roots p selected) (fun (selected: ids_vec) -> selected) (selection_ok roots p) (fun (_: Native.t_Error) -> Prims.l_True);
    assert (selection_result roots p (Native.extend_past fact before)) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.prune "Nickel_crdt.Edit.has_event";
      Tactics.prune "Nickel_crdt.Edit.push";
      Tactics.smt_sync' 1 1
    ) end
  else
    begin assert (selection_result roots p (Native.extend_past fact before)) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.prune "Nickel_crdt.Edit.has_event";
      Tactics.prune "Nickel_crdt.Edit.push";
      Tactics.smt_sync' 1 1
    ) end

let facts_closed (facts: t_Slice Native.t_Fact) (p: Native.t_EventId -> Type0) : Type0 =
  forall(i: usize{v i < Seq.length facts}). fact_closed (Seq.index facts (v i)) p

let past_pass_preserves (roots: t_Slice Native.t_EventId) (p: Native.t_EventId -> Type0) (facts: t_Slice Native.t_Fact) (before: ids_vec) : Lemma (requires (selection_ok roots p before /\ facts_closed facts p)) (ensures selection_result roots p (Native.past_pass facts before)) =
  let each_extend (selected: ids_vec) (i: usize{v i < Seq.length facts}) : Lemma (requires selection_ok roots p selected) (ensures selection_result roots p (Native.extend_past (Seq.index facts (v i)) selected)) = extend_past_preserves roots p (Seq.index facts (v i)) selected in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_extend);
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len facts) (fun (_: nat) (selected: ids_vec) -> selection_ok roots p selected) (fun (selected: ids_vec) -> selected) (selection_ok roots p) (fun (_: Native.t_Error) -> Prims.l_True);
  assert (selection_result roots p (Native.past_pass facts before)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel_crdt.Edit.extend_past";
    Tactics.smt_sync' 1 1
  )

let initial_selection_is_valid (roots: t_Slice Native.t_EventId) (p: Native.t_EventId -> Type0) : Lemma (requires all_ids roots p) (ensures selection_ok roots p (Alloc.Slice.impl__to_vec roots)) =
  ()

let past_stays_in_closed_set (facts: t_Slice Native.t_Fact) (roots: t_Slice Native.t_EventId) (p: Native.t_EventId -> Type0) : Lemma (requires (all_ids roots p /\ facts_closed facts p)) (ensures selection_result roots p (Native.past facts roots)) =
  initial_selection_is_valid roots p;
  let each_pass (selected: ids_vec) : Lemma (requires selection_ok roots p selected) (ensures selection_result roots p (Native.past_pass facts selected)) = past_pass_preserves roots p facts selected in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each_pass);
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len facts) (fun (_: nat) (selected: ids_vec) -> selection_ok roots p selected) (fun (selected: ids_vec) -> selected) (selection_ok roots p) (fun (_: Native.t_Error) -> Prims.l_True);
  assert (selection_result roots p (Native.past facts roots)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel_crdt.Edit.past_pass";
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
    Tactics.smt_sync' 1 1
  )