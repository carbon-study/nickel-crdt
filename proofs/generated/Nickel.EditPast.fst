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

let expanded_prefix (fact: Native.t_Fact) (finish: nat) (selected: ids_vec) : Type0 =
  forall(i: usize{v i < Seq.length (Alloc.Vec.impl_1__as_slice fact.f_after)}). v i < finish ==> member (Alloc.Vec.impl_1__as_slice selected) (Seq.index (Alloc.Vec.impl_1__as_slice fact.f_after) (v i))

let expansion_ok (fact: Native.t_Fact) (before: ids_vec) (next: ids_vec) : Type0 =
  Prims.l_and (retains (Alloc.Vec.impl_1__as_slice before) next) (member (Alloc.Vec.impl_1__as_slice before) fact.f_id ==> expanded_prefix fact (Seq.length (Alloc.Vec.impl_1__as_slice fact.f_after)) next)

let expansion_result (fact: Native.t_Fact) (before: ids_vec) (result: Result.t_Result ids_vec Native.t_Error) : Type0 =
  match result with | Result.Result_Ok next -> begin expansion_ok fact before next end | _ -> begin Prims.l_True end

let extend_past_covers_predecessors (fact: Native.t_Fact) (before: ids_vec) : Lemma (ensures expansion_result fact before (Native.extend_past fact before)) =
  let membership_boolean (ids: t_Slice Native.t_EventId) (id: Native.t_EventId) : Lemma (ensures Prims.l_or (Native.has_event ids id == true) (Native.has_event ids id == false)) [SMTPat (Native.has_event ids id)] = () in
  extend_past_preserves (Alloc.Vec.impl_1__as_slice before) (fun (_: Native.t_EventId) -> Prims.l_True) fact before;
  let each_push (at: usize{v at < Seq.length (Alloc.Vec.impl_1__as_slice fact.f_after)}) (selected: ids_vec) : Lemma (requires expanded_prefix fact (v at) selected) (ensures ((match Native.push selected (Seq.index (Alloc.Vec.impl_1__as_slice fact.f_after) (v at)) with | (next, Result.Result_Ok _) -> begin expanded_prefix fact (v at + 1) next end | _ -> begin Prims.l_True end) <: Type0)) =
    push_result_is_exact selected (Seq.index (Alloc.Vec.impl_1__as_slice fact.f_after) (v at));
    assert (((match Native.push selected (Seq.index (Alloc.Vec.impl_1__as_slice fact.f_after) (v at)) with | (next, Result.Result_Ok _) -> begin expanded_prefix fact (v at + 1) next end | _ -> begin Prims.l_True end) <: Type0)) by (
      Tactics.prune "Nickel_crdt.Edit.push";
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
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.prune "Nickel_crdt.Edit.has_event";
      Tactics.prune "Nickel_crdt.Edit.push";
      Tactics.smt_sync' 1 1
    ) end
  else
    begin assert (expansion_result fact before (Native.extend_past fact before)) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.prune "Nickel_crdt.Edit.has_event";
      Tactics.prune "Nickel_crdt.Edit.push";
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
  let each_extend (selected: ids_vec) (at: usize{v at < Seq.length facts}) : Lemma (requires pass_prefix facts before (v at) selected) (ensures ((match Native.extend_past (Seq.index facts (v at)) selected with | Result.Result_Ok next -> begin pass_prefix facts before (v at + 1) next end | _ -> begin Prims.l_True end) <: Type0)) =
    extend_past_covers_predecessors (Seq.index facts (v at)) selected;
    let each_next (next: ids_vec) : Lemma (requires expansion_ok (Seq.index facts (v at)) selected next) (ensures pass_prefix facts before (v at + 1) next) = expansion_composes facts before at selected next in
    FStar.Classical.forall_intro (FStar.Classical.move_requires each_next);
    assert (((match Native.extend_past (Seq.index facts (v at)) selected with | Result.Result_Ok next -> begin pass_prefix facts before (v at + 1) next end | _ -> begin Prims.l_True end) <: Type0)) by (
      Tactics.prune "Nickel_crdt.Edit.extend_past";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_extend);
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len facts) (pass_prefix facts before) (fun (selected: ids_vec) -> selected) (fun (next: ids_vec) -> pass_prefix facts before (Seq.length facts) next) (fun (_: Native.t_Error) -> Prims.l_True);
  assert (pass_result facts before (Native.past_pass facts before)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel_crdt.Edit.extend_past";
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

let past_covers_bounded_predecessor_paths (facts: facts_vec) (roots: t_Slice Native.t_EventId) : Lemma (ensures depth_result facts roots (Seq.length (Alloc.Vec.impl_1__as_slice facts)) (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) =
  let each_pass (selected: ids_vec) (at: usize{v at < Seq.length (Alloc.Vec.impl_1__as_slice facts)}) : Lemma (requires covers_depth facts roots (v at) selected) (ensures depth_result facts roots (v at + 1) (Native.past_pass (Alloc.Vec.impl_1__as_slice facts) selected)) =
    past_pass_covers_edges (Alloc.Vec.impl_1__as_slice facts) selected;
    assert (pass_result (Alloc.Vec.impl_1__as_slice facts) selected (Native.past_pass (Alloc.Vec.impl_1__as_slice facts) selected)) by (
      Tactics.prune "Nickel_crdt.Edit.past_pass";
      Tactics.smt_sync' 1 1
    );
    match Native.past_pass (Alloc.Vec.impl_1__as_slice facts) selected with | Result.Result_Ok next -> begin pass_covers_next_depth facts roots (v at) selected next;
    assert (depth_result facts roots (v at + 1) (Native.past_pass (Alloc.Vec.impl_1__as_slice facts) selected)) by (
      Tactics.prune "Nickel_crdt.Edit.past_pass";
      Tactics.smt_sync' 1 1
    ) end | Result.Result_Err _ -> begin assert (depth_result facts roots (v at + 1) (Native.past_pass (Alloc.Vec.impl_1__as_slice facts) selected)) by (
      Tactics.prune "Nickel_crdt.Edit.past_pass";
      Tactics.smt_sync' 1 1
    ) end in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_pass);
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Alloc.Vec.impl_1__len facts) (covers_depth facts roots) (fun (selected: ids_vec) -> selected) (covers_depth facts roots (Seq.length (Alloc.Vec.impl_1__as_slice facts))) (fun (_: Native.t_Error) -> Prims.l_True);
  assert (depth_result facts roots (Seq.length (Alloc.Vec.impl_1__as_slice facts)) (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel_crdt.Edit.past_pass";
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
        Tactics.smt_sync' 1 1
      ) in
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_path);
    () in
  FStar.Classical.forall_intro each_id;
  assert (exact_past_result facts roots (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) by (
    Tactics.prune "Nickel_crdt.Edit.past";
    Tactics.smt_sync' 1 1
  ) end | Result.Result_Err _ -> begin assert (exact_past_result facts roots (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) by (
    Tactics.prune "Nickel_crdt.Edit.past";
    Tactics.smt_sync' 1 1
  ) end

open Nickel.EditWellFormed

let stored_id_presence_agrees (facts: facts_vec) (id: Native.t_EventId) : Lemma (ensures fact_id_present facts id <==> Nickel.EditWellFormed.event_present (Alloc.Vec.impl_1__as_slice facts) id) [SMTPat (fact_id_present facts id)] =
  Nickel.EditWellFormed.absence_on_whole_facts (Alloc.Vec.impl_1__as_slice facts) id;
  ()

let stored_roots_are_present (facts: facts_vec) (roots: t_Slice Native.t_EventId) : Lemma (requires all_ids roots (fact_id_present facts)) (ensures Nickel.EditWellFormed.dependencies_present (Alloc.Vec.impl_1__as_slice facts) roots) =
  ()

let unique_selection (ids: Seq.seq Native.t_EventId) : Type0 =
  forall(i: FStar.Fin.under (Seq.length ids)) (j: FStar.Fin.under (Seq.length ids)). i < j ==> Prims.l_not (Seq.index ids i == Seq.index ids j)

let unique_positions_differ (ids: Seq.seq Native.t_EventId) (i: nat{i < Seq.length ids}) (j: nat{Prims.l_and (i < j) (j < Seq.length ids)}) : Lemma (requires unique_selection ids) (ensures Prims.l_not (Seq.index ids i == Seq.index ids j)) =
  ()

let empty_and_singleton_roots_are_unique (id: Native.t_EventId) : Lemma (ensures Prims.l_and (unique_selection Seq.empty) (unique_selection (Seq.create 1 id))) =
  ()

let stored_selection (facts: facts_vec) (selected: ids_vec) : Type0 =
  Prims.l_and (unique_selection (Alloc.Vec.impl_1__as_slice selected)) (all_ids (Alloc.Vec.impl_1__as_slice selected) (fact_id_present facts))

let selected_fact_position (facts: facts_vec) (ids: t_Slice Native.t_EventId{all_ids ids (fact_id_present facts)}) (at: nat{at < Seq.length ids}) : position: FStar.Fin.under (Seq.length (Alloc.Vec.impl_1__as_slice facts)){(Seq.index (Alloc.Vec.impl_1__as_slice facts) position).f_id == Seq.index ids at} =
  assert (fact_id_present facts (Rust_primitives.Slice.slice_index ids (mk_usize at)));
  assert (fact_id_present facts (Seq.index ids at));
  parent_fact_position facts (Seq.index ids at)

let missing_position (facts: facts_vec) (selected: ids_vec{stored_selection facts selected}) (id: Native.t_EventId{fact_id_present facts id}) (at: nat{at <= Seq.length (Alloc.Vec.impl_1__as_slice selected)}) : position: FStar.Fin.under (Seq.length (Alloc.Vec.impl_1__as_slice facts)){(Seq.index (Alloc.Vec.impl_1__as_slice facts) position).f_id == (if at ==? Seq.length (Alloc.Vec.impl_1__as_slice selected) then
  begin id end
else
  begin Seq.index (Alloc.Vec.impl_1__as_slice selected) at end)} =
  if at ==? Seq.length (Alloc.Vec.impl_1__as_slice selected) then
    begin parent_fact_position facts id end
  else
    begin selected_fact_position facts (Alloc.Vec.impl_1__as_slice selected) at end

let missing_stored_id_leaves_room (facts: facts_vec) (selected: ids_vec) (id: Native.t_EventId) : Lemma (requires (stored_selection facts selected /\ fact_id_present facts id /\ Prims.l_not (member (Alloc.Vec.impl_1__as_slice selected) id))) (ensures Seq.length (Alloc.Vec.impl_1__as_slice selected) < Seq.length (Alloc.Vec.impl_1__as_slice facts)) =
  let ids = Alloc.Vec.impl_1__as_slice selected in
  let count = Seq.length ids in
  assert (unique_selection ids);
  assert (absent_prefix ids id count);
  if count < Seq.length (Alloc.Vec.impl_1__as_slice facts) then
    begin () end
  else
    begin if count ==? 0 then
      begin let position = parent_fact_position facts id in
      assert (position < count) end
    else
      begin let position = fun (at: nat{at <= count}) -> ((missing_position facts selected id at) <: FStar.Fin.under count) in
      let positions = Seq.init (count + 1) position in
      Seq.lemma_init_len (count + 1) position;
      Seq.init_index (count + 1) position;
      match FStar.Fin.pigeonhole positions with | (i, j) -> begin assert (Prims.l_and (i < j) (j <= count));
      assert (position i == position j);
      if j ==? count then
        begin assert (Seq.index ids i == id);
        assert (Seq.index ids (v (mk_usize i)) == id);
        assert (Prims.l_not (Seq.index ids (v (mk_usize i)) == id)) end
      else
        begin assert (j < count);
        assert (Seq.index ids i == Seq.index ids j);
        unique_positions_differ ids i j;
        assert (Prims.l_not (Seq.index ids i == Seq.index ids j));
        assert (i == j) end end end end

let stored_result (facts: facts_vec) (result: Result.t_Result ids_vec Native.t_Error) : Type0 =
  match result with | Result.Result_Ok selected -> begin stored_selection facts selected end | _ -> begin Prims.l_False end

let stored_push_result (facts: facts_vec) (result: ids_vec & Result.t_Result unit Native.t_Error) : Type0 =
  match result with | (selected, Result.Result_Ok _) -> begin stored_selection facts selected end | _ -> begin Prims.l_False end

let fresh_append_is_unique (before: t_Slice Native.t_EventId) (id: Native.t_EventId) : Lemma (requires (unique_selection before /\ Prims.l_not (member before id))) (ensures unique_selection (Seq.append before (Seq.create 1 id))) =
  let next = Seq.append before (Seq.create 1 id) in
  assert (absent_prefix before id (Seq.length before));
  let pair (i: FStar.Fin.under (Seq.length next)) (j: FStar.Fin.under (Seq.length next)) : Lemma (ensures i < j ==> Prims.l_not (Seq.index next i == Seq.index next j)) = if i < j then
    begin if j < Seq.length before then
      begin unique_positions_differ before i j;
      assert (Seq.index next i == Seq.index before i);
      assert (Seq.index next j == Seq.index before j) end
    else
      begin assert (j == Seq.length before);
      assert (i < Seq.length before);
      assert (Prims.l_not (Seq.index before (v (mk_usize i)) == id));
      assert (Seq.index next i == Seq.index before i);
      assert (Seq.index next j == id) end;
    assert (Prims.l_not (Seq.index next i == Seq.index next j)) end
  else
    begin () end in
  FStar.Classical.forall_intro_2 #(FStar.Fin.under (Seq.length next)) #(fun (_: FStar.Fin.under (Seq.length next)) -> FStar.Fin.under (Seq.length next)) #(fun (i: FStar.Fin.under (Seq.length next)) (j: FStar.Fin.under (Seq.length next)) -> i < j ==> Prims.l_not (Seq.index next i == Seq.index next j)) pair;
  assert (unique_selection next)

let fresh_stored_push_succeeds (facts: facts_vec) (selected: ids_vec) (id: Native.t_EventId) : Lemma (requires (stored_selection facts selected /\ fact_id_present facts id /\ Prims.l_not (member (Alloc.Vec.impl_1__as_slice selected) id))) (ensures stored_push_result facts (Native.push selected id)) =
  missing_stored_id_leaves_room facts selected id;
  fresh_append_is_unique (Alloc.Vec.impl_1__as_slice selected) id;
  selected_push_preserves Seq.empty (fact_id_present facts) selected id;
  push_result_is_exact selected id;
  assert (stored_push_result facts (Native.push selected id)) by (
    Tactics.prune "Nickel_crdt.Edit.push";
    Tactics.smt_sync' 1 1
  )

let extend_stored_selection_succeeds (facts: facts_vec) (fact: Native.t_Fact) (before: ids_vec) : Lemma (requires (stored_selection facts before /\ all_ids (Alloc.Vec.impl_1__as_slice fact.f_after) (fact_id_present facts))) (ensures stored_result facts (Native.extend_past fact before)) =
  let each_push (selected: ids_vec) (id: Native.t_EventId) : Lemma (requires (stored_selection facts selected /\ fact_id_present facts id /\ Prims.l_not (member (Alloc.Vec.impl_1__as_slice selected) id))) (ensures stored_push_result facts (Native.push selected id)) =
    fresh_stored_push_succeeds facts selected id;
    assert (stored_push_result facts (Native.push selected id)) by (
      Tactics.prune "Nickel_crdt.Edit.push";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_push);
  let membership_boolean (ids: t_Slice Native.t_EventId) (id: Native.t_EventId) : Lemma (ensures Prims.l_or (Native.has_event ids id == true) (Native.has_event ids id == false)) [SMTPat (Native.has_event ids id)] = () in
  if Native.has_event (Alloc.Vec.impl_1__as_slice before) fact.f_id then
    begin Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Alloc.Vec.impl_1__len fact.f_after) (fun (_: nat) (selected: ids_vec) -> stored_selection facts selected) (fun (selected: ids_vec) -> selected) (stored_selection facts) (fun (_: Native.t_Error) -> Prims.l_False);
    assert (stored_result facts (Native.extend_past fact before)) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.prune "Nickel.LoopUtil.step_safe";
      Tactics.prune "Nickel.LoopUtil.output_safe";
      Tactics.prune "Nickel_crdt.Edit.has_event";
      Tactics.prune "Nickel_crdt.Edit.push";
      Tactics.smt_sync' 1 1
    ) end
  else
    begin assert (stored_result facts (Native.extend_past fact before)) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.prune "Nickel_crdt.Edit.has_event";
      Tactics.prune "Nickel_crdt.Edit.push";
      Tactics.smt_sync' 1 1
    ) end

let history_references_present (facts: facts_vec) : Type0 =
  forall(i: nat{i < Seq.length (Alloc.Vec.impl_1__as_slice facts)}). all_ids (Alloc.Vec.impl_1__as_slice (Seq.index (Alloc.Vec.impl_1__as_slice facts) i).f_after) (fact_id_present facts)

let stored_pass_succeeds (facts: facts_vec) (before: ids_vec) : Lemma (requires (history_references_present facts /\ stored_selection facts before)) (ensures stored_result facts (Native.past_pass (Alloc.Vec.impl_1__as_slice facts) before)) =
  let each_extend (selected: ids_vec) (i: usize{v i < Seq.length (Alloc.Vec.impl_1__as_slice facts)}) : Lemma (requires stored_selection facts selected) (ensures stored_result facts (Native.extend_past (Seq.index (Alloc.Vec.impl_1__as_slice facts) (v i)) selected)) =
    extend_stored_selection_succeeds facts (Seq.index (Alloc.Vec.impl_1__as_slice facts) (v i)) selected;
    assert (stored_result facts (Native.extend_past (Seq.index (Alloc.Vec.impl_1__as_slice facts) (v i)) selected)) by (
      Tactics.prune "Nickel_crdt.Edit.extend_past";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_extend);
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Alloc.Vec.impl_1__len facts) (fun (_: nat) (selected: ids_vec) -> stored_selection facts selected) (fun (selected: ids_vec) -> selected) (stored_selection facts) (fun (_: Native.t_Error) -> Prims.l_False);
  assert (stored_result facts (Native.past_pass (Alloc.Vec.impl_1__as_slice facts) before)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel.LoopUtil.step_safe";
    Tactics.prune "Nickel.LoopUtil.output_safe";
    Tactics.prune "Nickel_crdt.Edit.extend_past";
    Tactics.smt_sync' 1 1
  )

let fitting_closed_history_computes_past (facts: facts_vec) (roots: t_Slice Native.t_EventId) : Lemma (requires (history_references_present facts /\ unique_selection roots /\ all_ids roots (fact_id_present facts))) (ensures stored_result facts (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) =
  stored_roots_are_present facts roots;
  Nickel.EditWellFormed.present_dependencies_pass_guard (Alloc.Vec.impl_1__as_slice facts) roots;
  assert (stored_selection facts (Alloc.Slice.impl__to_vec roots));
  let each_pass (selected: ids_vec) : Lemma (requires stored_selection facts selected) (ensures stored_result facts (Native.past_pass (Alloc.Vec.impl_1__as_slice facts) selected)) =
    stored_pass_succeeds facts selected;
    assert (stored_result facts (Native.past_pass (Alloc.Vec.impl_1__as_slice facts) selected)) by (
      Tactics.prune "Nickel_crdt.Edit.past_pass";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each_pass);
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Alloc.Vec.impl_1__len facts) (fun (_: nat) (selected: ids_vec) -> stored_selection facts selected) (fun (selected: ids_vec) -> selected) (stored_selection facts) (fun (_: Native.t_Error) -> Prims.l_False);
  assert (stored_result facts (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel.LoopUtil.step_safe";
    Tactics.prune "Nickel.LoopUtil.output_safe";
    Tactics.prune "Nickel_crdt.Edit.past_pass";
    Tactics.prune "Nickel_crdt.Edit.validate_after";
    Tactics.smt_sync' 1 1
  )

let fitting_past_is_total_and_exact (facts: facts_vec) (roots: t_Slice Native.t_EventId) : Lemma (requires (history_references_present facts /\ unique_selection roots /\ all_ids roots (fact_id_present facts))) (ensures Prims.l_and (stored_result facts (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) (exact_past_result facts roots (Native.past (Alloc.Vec.impl_1__as_slice facts) roots))) =
  fitting_closed_history_computes_past facts roots;
  successful_past_is_exact_closure facts roots;
  assert (Prims.l_and (stored_result facts (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) (exact_past_result facts roots (Native.past (Alloc.Vec.impl_1__as_slice facts) roots))) by (
    Tactics.prune "Nickel_crdt.Edit.past";
    Tactics.smt_sync' 1 1
  )

let causally_closed_history_computes_exact_past (facts: facts_vec) (roots: t_Slice Native.t_EventId) : Lemma (requires (Nickel.EditWellFormed.facts_causally_closed facts /\ Nickel.EditWellFormed.dependencies_present (Alloc.Vec.impl_1__as_slice facts) roots /\ unique_selection roots)) (ensures Prims.l_and (stored_result facts (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) (exact_past_result facts roots (Native.past (Alloc.Vec.impl_1__as_slice facts) roots))) =
  assert (history_references_present facts);
  assert (all_ids roots (fact_id_present facts));
  fitting_past_is_total_and_exact facts roots;
  assert (Prims.l_and (stored_result facts (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) (exact_past_result facts roots (Native.past (Alloc.Vec.impl_1__as_slice facts) roots))) by (
    Tactics.prune "Nickel_crdt.Edit.past";
    Tactics.smt_sync' 1 1
  )