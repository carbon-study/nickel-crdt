(* Latte generated F* view *)
module Nickel.RegisterPast

open Nickel.Prelude

open Rust_primitives

open Core_models

open FStar.Pervasives

open FStar.Classical

open Nickel.LoopUtil

open Nickel.EventGraph

open Nickel.Canonical

open Nickel.Vector

module Shared = Nickel_crdt.Event_layer

module Native = Nickel_crdt.Register

module Envelope = Nickel_crdt.Causal

module List = FStar.List.Tot

module Result = Core_models.Result

module Seq = FStar.Seq

module Tactics = FStar.Tactics.V2

type fact = Envelope.t_Event Native.t_Write

unfold type rid = Envelope.t_Id

unfold type rops = Nickel.EventGraph.graph_ops fact Envelope.t_Id Native.t_Error

unfold type ids_vec = Alloc.Vec.t_Vec Envelope.t_Id Alloc.Alloc.t_Global

let ids_exact (ops: rops) : Type0 =
  forall(a: Envelope.t_Id) (b: Envelope.t_Id). ops._1._3 a b == true <==> a == b

let absent_prefix (ids: t_Slice Envelope.t_Id) (id: Envelope.t_Id) (finish: nat) : Type0 =
  forall(i: usize{v i < Seq.length ids}). v i < finish ==> Seq.index ids (v i) =!= id

let member (ids: t_Slice Envelope.t_Id) (id: Envelope.t_Id) : Type0 =
  Prims.l_not (absent_prefix ids id (Seq.length ids))

let id_membership_is_exact (ids: t_Slice Envelope.t_Id) (id: Envelope.t_Id) (ops: rops) : Lemma (requires ids_exact ops) (ensures Shared.has_id ids id ops == true <==> member ids id) =
  Nickel.EventGraph.membership_is_exact ids id ops;
  assert (Shared.has_id ids id ops == true <==> member ids id) by (
    Tactics.prune "Nickel_crdt.Event_layer.has_id";
    Tactics.smt_sync' 1 1
  )

let all_ids (ids: t_Slice Envelope.t_Id) (p: Envelope.t_Id -> Type0) : Type0 =
  forall(i: usize{v i < Seq.length ids}). p (Seq.index ids (v i))

let retains (roots: t_Slice Envelope.t_Id) (selected: ids_vec) : Type0 =
  forall(i: usize{v i < Seq.length roots}). member (Alloc.Vec.impl_1__as_slice selected) (Seq.index roots (v i))

let selection_ok (roots: t_Slice Envelope.t_Id) (p: Envelope.t_Id -> Type0) (selected: ids_vec) : Type0 =
  Prims.l_and (all_ids (Alloc.Vec.impl_1__as_slice selected) p) (retains roots selected)

let selection_result (roots: t_Slice Envelope.t_Id) (p: Envelope.t_Id -> Type0) (result: Result.t_Result ids_vec Native.t_Error) : Type0 =
  match result with | Result.Result_Ok selected -> begin selection_ok roots p selected end | _ -> begin Prims.l_True end

let member_satisfies (ids: t_Slice Envelope.t_Id) (p: Envelope.t_Id -> Type0) (id: Envelope.t_Id) : Lemma (requires (all_ids ids p /\ member ids id)) (ensures p id) =
  ()

let push_selection_result (roots: t_Slice Envelope.t_Id) (p: Envelope.t_Id -> Type0) (outcome: ids_vec & Result.t_Result unit Native.t_Error) : Type0 =
  match outcome with | (next, Result.Result_Ok _) -> begin selection_ok roots p next end | _ -> begin Prims.l_True end

let selected_push_preserves (roots: t_Slice Envelope.t_Id) (p: Envelope.t_Id -> Type0) (before: ids_vec) (id: Envelope.t_Id) (internal: unit -> Native.t_Error) : Lemma (requires (selection_ok roots p before /\ p id)) (ensures push_selection_result roots p (Shared.push before id internal)) =
  Nickel.Canonical.push_is_exact before id internal;
  assert (push_selection_result roots p (Shared.push before id internal)) by (
    Tactics.prune "Nickel_crdt.Event_layer.push";
    Tactics.smt_sync' 1 1
  )

let ops_shape (ops: rops) : Lemma (ensures ops == ((ops._1._1, ops._1._2, ops._1._3, ops._1._4, ops._1._5, ops._1._6), (ops._2._1, ops._2._2))) =
  ()

let fact_closed (ops: rops) (fact: fact) (p: Envelope.t_Id -> Type0) : Type0 =
  p (ops._1._1 fact) ==> all_ids (ops._1._2 fact) p

let extend_past_preserves (ops: rops) (roots: t_Slice Envelope.t_Id) (p: Envelope.t_Id -> Type0) (fact: fact) (before: ids_vec) : Lemma (requires (ids_exact ops /\ selection_ok roots p before /\ fact_closed ops fact p)) (ensures selection_result roots p (Shared.extend_past fact before ops)) =
  let each_push (selected: ids_vec) (id: Envelope.t_Id) : Lemma (requires (selection_ok roots p selected /\ p id)) (ensures push_selection_result roots p (Shared.push selected id ops._2._1)) = selected_push_preserves roots p selected id ops._2._1 in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_push);
  id_membership_is_exact (Alloc.Vec.impl_1__as_slice before) (ops._1._1 fact) ops;
  ops_shape ops;
  if Shared.has_id (Alloc.Vec.impl_1__as_slice before) (ops._1._1 fact) ops then
    begin member_satisfies (Alloc.Vec.impl_1__as_slice before) p (ops._1._1 fact);
    assert (all_ids (ops._1._2 fact) p);
    Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len (ops._1._2 fact)) (fun (_: nat) (selected: ids_vec) -> selection_ok roots p selected) (fun (selected: ids_vec) -> selected) (selection_ok roots p) (fun (_: Native.t_Error) -> Prims.l_True);
    assert (selection_result roots p (Shared.extend_past fact before ops)) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.prune "Nickel_crdt.Event_layer.has_id";
      Tactics.prune "Nickel_crdt.Event_layer.push";
      Tactics.smt_sync' 1 1
    ) end
  else
    begin assert (selection_result roots p (Shared.extend_past fact before ops)) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.prune "Nickel_crdt.Event_layer.has_id";
      Tactics.prune "Nickel_crdt.Event_layer.push";
      Tactics.smt_sync' 1 1
    ) end

let facts_closed (ops: rops) (facts: t_Slice fact) (p: Envelope.t_Id -> Type0) : Type0 =
  forall(i: usize{v i < Seq.length facts}). fact_closed ops (Seq.index facts (v i)) p

let past_pass_preserves (ops: rops) (roots: t_Slice Envelope.t_Id) (p: Envelope.t_Id -> Type0) (facts: t_Slice fact) (before: ids_vec) : Lemma (requires (ids_exact ops /\ selection_ok roots p before /\ facts_closed ops facts p)) (ensures selection_result roots p (Shared.past_pass facts before ops)) =
  let each_extend (selected: ids_vec) (i: usize{v i < Seq.length facts}) : Lemma (requires selection_ok roots p selected) (ensures selection_result roots p (Shared.extend_past (Seq.index facts (v i)) selected ops)) = extend_past_preserves ops roots p (Seq.index facts (v i)) selected in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_extend);
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len facts) (fun (_: nat) (selected: ids_vec) -> selection_ok roots p selected) (fun (selected: ids_vec) -> selected) (selection_ok roots p) (fun (_: Native.t_Error) -> Prims.l_True);
  assert (selection_result roots p (Shared.past_pass facts before ops)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel_crdt.Event_layer.extend_past";
    Tactics.smt_sync' 1 1
  )

let initial_selection_is_valid (roots: t_Slice Envelope.t_Id) (p: Envelope.t_Id -> Type0) : Lemma (requires all_ids roots p) (ensures selection_ok roots p (Alloc.Slice.impl__to_vec roots)) =
  ()

let past_stays_in_closed_set (ops: rops) (facts: t_Slice fact) (roots: t_Slice Envelope.t_Id) (p: Envelope.t_Id -> Type0) : Lemma (requires (ids_exact ops /\ all_ids roots p /\ facts_closed ops facts p)) (ensures selection_result roots p (Shared.past facts roots ops)) =
  initial_selection_is_valid roots p;
  ops_shape ops;
  let each_pass (selected: ids_vec) : Lemma (requires selection_ok roots p selected) (ensures selection_result roots p (Shared.past_pass facts selected ops)) = past_pass_preserves ops roots p facts selected in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each_pass);
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len facts) (fun (_: nat) (selected: ids_vec) -> selection_ok roots p selected) (fun (selected: ids_vec) -> selected) (selection_ok roots p) (fun (_: Native.t_Error) -> Prims.l_True);
  assert (selection_result roots p (Shared.past facts roots ops)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel_crdt.Event_layer.past_pass";
    Tactics.prune "Nickel_crdt.Event_layer.validate_after";
    Tactics.smt_sync' 1 1
  )

let causal_edge (ops: rops) (facts: t_Slice fact) (newer: Envelope.t_Id) (older: Envelope.t_Id) : Type0 =
  exists(k: nat). Prims.l_and (Prims.l_and (k < Seq.length facts) (ops._1._1 (Seq.index facts k) == newer)) (member (ops._1._2 (Seq.index facts k)) older)

let rec causal_path (ops: rops) (facts: t_Slice fact) (start: Envelope.t_Id) (steps: Prims.list Envelope.t_Id) (finish: Envelope.t_Id) : Tot Type0 (decreases steps) =
  match steps with | Prims.Nil -> begin start == finish end | Prims.Cons next rest -> begin Prims.l_and (causal_edge ops facts start next) (causal_path ops facts next rest finish) end

let ancestor (ops: rops) (facts: t_Slice fact) (roots: t_Slice Envelope.t_Id) (id: Envelope.t_Id) : Type0 =
  exists(root: Envelope.t_Id) (steps: Prims.list Envelope.t_Id). Prims.l_and (member roots root) (causal_path ops facts root steps id)

let rec append_path_edge (ops: rops) (facts: t_Slice fact) (root: Envelope.t_Id) (steps: Prims.list Envelope.t_Id) (parent: Envelope.t_Id) (child: Envelope.t_Id) : Lemma (requires (causal_path ops facts root steps parent /\ causal_edge ops facts parent child)) (ensures causal_path ops facts root (List.append steps (Prims.Cons child Prims.Nil)) child) (decreases steps) =
  match steps with | Prims.Nil -> begin () end | Prims.Cons next rest -> begin append_path_edge ops facts next rest parent child end

let ancestor_follows_edge (ops: rops) (facts: t_Slice fact) (roots: t_Slice Envelope.t_Id) (parent: Envelope.t_Id) (child: Envelope.t_Id) : Lemma (requires (ancestor ops facts roots parent /\ causal_edge ops facts parent child)) (ensures ancestor ops facts roots child) =
  let each_path (root: Envelope.t_Id) (steps: Prims.list Envelope.t_Id) : Lemma (requires (member roots root /\ causal_path ops facts root steps parent)) (ensures ancestor ops facts roots child) =
    append_path_edge ops facts root steps parent child;
    assert (Prims.l_and (member roots root) (causal_path ops facts root (List.append steps (Prims.Cons child Prims.Nil)) child)) in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_path)

let ancestor_roots_and_edges (ops: rops) (facts: t_Slice fact) (roots: t_Slice Envelope.t_Id) : Lemma (ensures Prims.l_and (all_ids roots (ancestor ops facts roots)) (facts_closed ops facts (ancestor ops facts roots))) =
  let each_root (i: usize{v i < Seq.length roots}) : Lemma (ensures ancestor ops facts roots (Seq.index roots (v i))) =
    assert (member roots (Seq.index roots (v i)));
    assert (causal_path ops facts (Seq.index roots (v i)) Prims.Nil (Seq.index roots (v i))) in
  FStar.Classical.forall_intro each_root;
  let each_fact (i: usize{v i < Seq.length facts}) : Lemma (ensures fact_closed ops (Seq.index facts (v i)) (ancestor ops facts roots)) =
    let f = Seq.index facts (v i) in
    let each_child (j: usize{v j < Seq.length (ops._1._2 f)}) : Lemma (requires ancestor ops facts roots (ops._1._1 f)) (ensures ancestor ops facts roots (Seq.index (ops._1._2 f) (v j))) =
      assert (member (ops._1._2 f) (Seq.index (ops._1._2 f) (v j)));
      assert (causal_edge ops facts (ops._1._1 f) (Seq.index (ops._1._2 f) (v j)));
      ancestor_follows_edge ops facts roots (ops._1._1 f) (Seq.index (ops._1._2 f) (v j)) in
    FStar.Classical.forall_intro (FStar.Classical.move_requires each_child) in
  FStar.Classical.forall_intro each_fact

let past_has_only_ancestors_and_keeps_roots (ops: rops) (facts: t_Slice fact) (roots: t_Slice Envelope.t_Id) : Lemma (requires ids_exact ops) (ensures selection_result roots (ancestor ops facts roots) (Shared.past facts roots ops)) =
  ancestor_roots_and_edges ops facts roots;
  past_stays_in_closed_set ops facts roots (ancestor ops facts roots)

let expanded_prefix (ops: rops) (fact: fact) (finish: nat) (selected: ids_vec) : Type0 =
  forall(i: usize{v i < Seq.length (ops._1._2 fact)}). v i < finish ==> member (Alloc.Vec.impl_1__as_slice selected) (Seq.index (ops._1._2 fact) (v i))

let expansion_ok (ops: rops) (fact: fact) (before: ids_vec) (next: ids_vec) : Type0 =
  Prims.l_and (retains (Alloc.Vec.impl_1__as_slice before) next) (member (Alloc.Vec.impl_1__as_slice before) (ops._1._1 fact) ==> expanded_prefix ops fact (Seq.length (ops._1._2 fact)) next)

let expansion_result (ops: rops) (fact: fact) (before: ids_vec) (result: Result.t_Result ids_vec Native.t_Error) : Type0 =
  match result with | Result.Result_Ok next -> begin expansion_ok ops fact before next end | _ -> begin Prims.l_True end

let extend_past_covers_predecessors (ops: rops) (fact: fact) (before: ids_vec) : Lemma (requires ids_exact ops) (ensures expansion_result ops fact before (Shared.extend_past fact before ops)) =
  ops_shape ops;
  let membership_boolean (ids: t_Slice Envelope.t_Id) (id: Envelope.t_Id) : Lemma (ensures Prims.l_or (Shared.has_id ids id ops == true) (Shared.has_id ids id ops == false)) [SMTPat (Shared.has_id ids id ops)] = () in
  extend_past_preserves ops (Alloc.Vec.impl_1__as_slice before) (fun (_: Envelope.t_Id) -> Prims.l_True) fact before;
  let each_push (at: usize{v at < Seq.length (ops._1._2 fact)}) (selected: ids_vec) : Lemma (requires expanded_prefix ops fact (v at) selected) (ensures ((match Shared.push selected (Seq.index (ops._1._2 fact) (v at)) ops._2._1 with | (next, Result.Result_Ok _) -> begin expanded_prefix ops fact (v at + 1) next end | _ -> begin Prims.l_True end) <: Type0)) =
    Nickel.Canonical.push_is_exact selected (Seq.index (ops._1._2 fact) (v at)) ops._2._1;
    assert (((match Shared.push selected (Seq.index (ops._1._2 fact) (v at)) ops._2._1 with | (next, Result.Result_Ok _) -> begin expanded_prefix ops fact (v at + 1) next end | _ -> begin Prims.l_True end) <: Type0)) by (
      Tactics.prune "Nickel_crdt.Event_layer.push";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_push);
  let skip_existing (at: usize{v at < Seq.length (ops._1._2 fact)}) (selected: ids_vec) : Lemma (requires (expanded_prefix ops fact (v at) selected /\ Shared.has_id (Alloc.Vec.impl_1__as_slice selected) (Seq.index (ops._1._2 fact) (v at)) ops == true)) (ensures expanded_prefix ops fact (v at + 1) selected) = id_membership_is_exact (Alloc.Vec.impl_1__as_slice selected) (Seq.index (ops._1._2 fact) (v at)) ops in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 skip_existing);
  id_membership_is_exact (Alloc.Vec.impl_1__as_slice before) (ops._1._1 fact) ops;
  if Shared.has_id (Alloc.Vec.impl_1__as_slice before) (ops._1._1 fact) ops then
    begin Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len (ops._1._2 fact)) (fun (at: nat) (selected: ids_vec) -> expanded_prefix ops fact at selected) (fun (selected: ids_vec) -> selected) (fun (selected: ids_vec) -> expanded_prefix ops fact (Seq.length (ops._1._2 fact)) selected) (fun (_: Native.t_Error) -> Prims.l_True);
    assert (expansion_result ops fact before (Shared.extend_past fact before ops)) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.prune "Nickel_crdt.Event_layer.has_id";
      Tactics.prune "Nickel_crdt.Event_layer.push";
      Tactics.smt_sync' 1 1
    ) end
  else
    begin assert (expansion_result ops fact before (Shared.extend_past fact before ops)) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.prune "Nickel_crdt.Event_layer.has_id";
      Tactics.prune "Nickel_crdt.Event_layer.push";
      Tactics.smt_sync' 1 1
    ) end

let pass_prefix (ops: rops) (facts: t_Slice fact) (before: ids_vec) (finish: nat) (next: ids_vec) : Type0 =
  Prims.l_and (retains (Alloc.Vec.impl_1__as_slice before) next) (forall(i: usize{v i < Seq.length facts}). v i < finish ==> expansion_ok ops (Seq.index facts (v i)) before next)

let pass_result (ops: rops) (facts: t_Slice fact) (before: ids_vec) (result: Result.t_Result ids_vec Native.t_Error) : Type0 =
  match result with | Result.Result_Ok next -> begin pass_prefix ops facts before (Seq.length facts) next end | _ -> begin Prims.l_True end

let retains_member (before: ids_vec) (next: ids_vec) (id: Envelope.t_Id) : Lemma (requires (retains (Alloc.Vec.impl_1__as_slice before) next /\ member (Alloc.Vec.impl_1__as_slice before) id)) (ensures member (Alloc.Vec.impl_1__as_slice next) id) =
  ()

let expansion_composes (ops: rops) (facts: t_Slice fact) (before: ids_vec) (at: usize{v at < Seq.length facts}) (selected: ids_vec) (next: ids_vec) : Lemma (requires (pass_prefix ops facts before (v at) selected /\ expansion_ok ops (Seq.index facts (v at)) selected next)) (ensures pass_prefix ops facts before (v at + 1) next) =
  let each_id (id: Envelope.t_Id) : Lemma (requires member (Alloc.Vec.impl_1__as_slice selected) id) (ensures member (Alloc.Vec.impl_1__as_slice next) id) = retains_member selected next id in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each_id);
  let prior_member (id: Envelope.t_Id) : Lemma (requires member (Alloc.Vec.impl_1__as_slice before) id) (ensures member (Alloc.Vec.impl_1__as_slice selected) id) = retains_member before selected id in
  FStar.Classical.forall_intro (FStar.Classical.move_requires prior_member)

let past_pass_covers_edges (ops: rops) (facts: t_Slice fact) (before: ids_vec) : Lemma (requires ids_exact ops) (ensures pass_result ops facts before (Shared.past_pass facts before ops)) =
  let each_extend (selected: ids_vec) (at: usize{v at < Seq.length facts}) : Lemma (requires pass_prefix ops facts before (v at) selected) (ensures ((match Shared.extend_past (Seq.index facts (v at)) selected ops with | Result.Result_Ok next -> begin pass_prefix ops facts before (v at + 1) next end | _ -> begin Prims.l_True end) <: Type0)) =
    extend_past_covers_predecessors ops (Seq.index facts (v at)) selected;
    let each_next (next: ids_vec) : Lemma (requires expansion_ok ops (Seq.index facts (v at)) selected next) (ensures pass_prefix ops facts before (v at + 1) next) = expansion_composes ops facts before at selected next in
    FStar.Classical.forall_intro (FStar.Classical.move_requires each_next);
    assert (((match Shared.extend_past (Seq.index facts (v at)) selected ops with | Result.Result_Ok next -> begin pass_prefix ops facts before (v at + 1) next end | _ -> begin Prims.l_True end) <: Type0)) by (
      Tactics.prune "Nickel_crdt.Event_layer.extend_past";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_extend);
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len facts) (pass_prefix ops facts before) (fun (selected: ids_vec) -> selected) (fun (next: ids_vec) -> pass_prefix ops facts before (Seq.length facts) next) (fun (_: Native.t_Error) -> Prims.l_True);
  assert (pass_result ops facts before (Shared.past_pass facts before ops)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel_crdt.Event_layer.extend_past";
    Tactics.smt_sync' 1 1
  )

let rec reachable_within (ops: rops) (facts: t_Slice fact) (roots: t_Slice Envelope.t_Id) (depth: nat) (id: Envelope.t_Id) : Tot Type0 (decreases depth) =
  Prims.l_or (member roots id) (if depth ==? 0 then
    begin Prims.l_False end
  else
    begin exists(parent: Envelope.t_Id). Prims.l_and (reachable_within ops facts roots (depth - 1) parent) (causal_edge ops facts parent id) end)

let covers_depth (ops: rops) (facts: t_Slice fact) (roots: t_Slice Envelope.t_Id) (depth: nat) (selected: ids_vec) : Type0 =
  forall(id: Envelope.t_Id). reachable_within ops facts roots depth id ==> member (Alloc.Vec.impl_1__as_slice selected) id

let pass_edge_is_covered (ops: rops) (facts: t_Slice fact) (before: ids_vec) (next: ids_vec) (parent: Envelope.t_Id) (child: Envelope.t_Id) : Lemma (requires (pass_prefix ops facts before (Seq.length facts) next /\ member (Alloc.Vec.impl_1__as_slice before) parent /\ causal_edge ops facts parent child)) (ensures member (Alloc.Vec.impl_1__as_slice next) child) =
  let each_position (k: nat) : Lemma (requires (Prims.l_and (k < Seq.length facts) (ops._1._1 (Seq.index facts k) == parent) /\ member (ops._1._2 (Seq.index facts k)) child)) (ensures member (Alloc.Vec.impl_1__as_slice next) child) =
    let index = mk_usize k in
    assert (expansion_ok ops (Seq.index facts (v index)) before next) in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each_position)

let pass_covers_next_depth (ops: rops) (facts: t_Slice fact) (roots: t_Slice Envelope.t_Id) (depth: nat) (before: ids_vec) (next: ids_vec) : Lemma (requires (covers_depth ops facts roots depth before /\ pass_prefix ops facts before (Seq.length facts) next)) (ensures covers_depth ops facts roots (depth + 1) next) =
  let old_member (id: Envelope.t_Id) : Lemma (requires member (Alloc.Vec.impl_1__as_slice before) id) (ensures member (Alloc.Vec.impl_1__as_slice next) id) = retains_member before next id in
  FStar.Classical.forall_intro (FStar.Classical.move_requires old_member);
  let each_parent (parent: Envelope.t_Id) (child: Envelope.t_Id) : Lemma (requires (reachable_within ops facts roots depth parent /\ causal_edge ops facts parent child)) (ensures member (Alloc.Vec.impl_1__as_slice next) child) = pass_edge_is_covered ops facts before next parent child in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_parent);
  let each_id (id: Envelope.t_Id) : Lemma (requires reachable_within ops facts roots (depth + 1) id) (ensures member (Alloc.Vec.impl_1__as_slice next) id) = () in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each_id)

let depth_result (ops: rops) (facts: t_Slice fact) (roots: t_Slice Envelope.t_Id) (depth: nat) (result: Result.t_Result ids_vec Native.t_Error) : Type0 =
  match result with | Result.Result_Ok selected -> begin covers_depth ops facts roots depth selected end | _ -> begin Prims.l_True end

let past_covers_bounded_predecessor_paths (ops: rops) (facts: t_Slice fact) (roots: t_Slice Envelope.t_Id) : Lemma (requires ids_exact ops) (ensures depth_result ops facts roots (Seq.length facts) (Shared.past facts roots ops)) =
  ops_shape ops;
  let each_pass (selected: ids_vec) (at: usize{v at < Seq.length facts}) : Lemma (requires covers_depth ops facts roots (v at) selected) (ensures depth_result ops facts roots (v at + 1) (Shared.past_pass facts selected ops)) =
    past_pass_covers_edges ops facts selected;
    match Shared.past_pass facts selected ops with | Result.Result_Ok next -> begin pass_covers_next_depth ops facts roots (v at) selected next;
    assert (depth_result ops facts roots (v at + 1) (Shared.past_pass facts selected ops)) by (
      Tactics.prune "Nickel_crdt.Event_layer.past_pass";
      Tactics.smt_sync' 1 1
    ) end | Result.Result_Err _ -> begin assert (depth_result ops facts roots (v at + 1) (Shared.past_pass facts selected ops)) by (
      Tactics.prune "Nickel_crdt.Event_layer.past_pass";
      Tactics.smt_sync' 1 1
    ) end in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_pass);
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len facts) (covers_depth ops facts roots) (fun (selected: ids_vec) -> selected) (covers_depth ops facts roots (Seq.length facts)) (fun (_: Native.t_Error) -> Prims.l_True);
  assert (depth_result ops facts roots (Seq.length facts) (Shared.past facts roots ops)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel_crdt.Event_layer.past_pass";
    Tactics.prune "Nickel_crdt.Event_layer.validate_after";
    Tactics.smt_sync' 1 1
  )

let rec path_extends_reach (ops: rops) (facts: t_Slice fact) (roots: t_Slice Envelope.t_Id) (depth: nat) (start: Envelope.t_Id) (steps: Prims.list Envelope.t_Id) (finish: Envelope.t_Id) : Lemma (requires (reachable_within ops facts roots depth start /\ causal_path ops facts start steps finish)) (ensures reachable_within ops facts roots (depth + List.length steps) finish) (decreases steps) =
  match steps with | Prims.Nil -> begin () end | Prims.Cons next rest -> begin assert (reachable_within ops facts roots (depth + 1) next);
  path_extends_reach ops facts roots (depth + 1) next rest finish end

let rec reach_allows_more_edges (ops: rops) (facts: t_Slice fact) (roots: t_Slice Envelope.t_Id) (depth: nat) (extra: nat) (id: Envelope.t_Id) : Lemma (requires reachable_within ops facts roots depth id) (ensures reachable_within ops facts roots (depth + extra) id) (decreases depth) =
  if depth ==? 0 then
    begin () end
  else
    begin let each_parent (parent: Envelope.t_Id) : Lemma (requires (reachable_within ops facts roots (depth - 1) parent /\ causal_edge ops facts parent id)) (ensures reachable_within ops facts roots (depth + extra) id) = reach_allows_more_edges ops facts roots (depth - 1) extra parent in
    FStar.Classical.forall_intro (FStar.Classical.move_requires each_parent) end

let past_contains_short_paths (ops: rops) (facts: t_Slice fact) (roots: t_Slice Envelope.t_Id) (root: Envelope.t_Id) (steps: Prims.list Envelope.t_Id) (id: Envelope.t_Id) : Lemma (requires (ids_exact ops /\ member roots root /\ causal_path ops facts root steps id /\ List.length steps <= Seq.length facts)) (ensures ((match Shared.past facts roots ops with | Result.Result_Ok selected -> begin member (Alloc.Vec.impl_1__as_slice selected) id end | _ -> begin Prims.l_True end) <: Type0)) =
  path_extends_reach ops facts roots 0 root steps id;
  reach_allows_more_edges ops facts roots (List.length steps) (Seq.length facts - List.length steps) id;
  past_covers_bounded_predecessor_paths ops facts roots;
  assert (((match Shared.past facts roots ops with | Result.Result_Ok selected -> begin member (Alloc.Vec.impl_1__as_slice selected) id end | _ -> begin Prims.l_True end) <: Type0)) by (
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.smt_sync' 1 1
  )

open FStar.Fin

let rec path_node (start: Envelope.t_Id) (steps: Prims.list Envelope.t_Id) (at: nat{at <= List.length steps}) : Tot Envelope.t_Id (decreases steps) =
  match steps with | Prims.Nil -> begin start end | Prims.Cons next rest -> begin if at ==? 0 then
    begin start end
  else
    begin path_node next rest (at - 1) end end

let rec drop_edges (steps: Prims.list Envelope.t_Id) (count: nat{count <= List.length steps}) : Tot (Prims.list Envelope.t_Id) (decreases steps) =
  if count ==? 0 then
    begin steps end
  else
    begin match steps with | Prims.Nil -> begin Prims.Nil end | Prims.Cons _ rest -> begin drop_edges rest (count - 1) end end

let rec cut_path_loop (steps: Prims.list Envelope.t_Id) (first: nat) (last: nat{Prims.l_and (first < last) (last <= List.length steps)}) : Tot (Prims.list Envelope.t_Id) (decreases steps) =
  if first ==? 0 then
    begin drop_edges steps last end
  else
    begin match steps with | Prims.Nil -> begin Prims.Nil end | Prims.Cons next rest -> begin Prims.Cons next (cut_path_loop rest (first - 1) (last - 1)) end end

let rec dropped_edge_count (steps: Prims.list Envelope.t_Id) (count: nat{count <= List.length steps}) : Lemma (ensures List.length (drop_edges steps count) == List.length steps - count) (decreases steps) =
  if count ==? 0 then
    begin () end
  else
    begin match steps with | Prims.Nil -> begin () end | Prims.Cons _ rest -> begin dropped_edge_count rest (count - 1) end end

let rec cut_path_is_shorter (steps: Prims.list Envelope.t_Id) (first: nat) (last: nat{Prims.l_and (first < last) (last <= List.length steps)}) : Lemma (ensures Prims.l_and (List.length (cut_path_loop steps first last) == List.length steps - last + first) (List.length (cut_path_loop steps first last) < List.length steps)) (decreases steps) =
  if first ==? 0 then
    begin dropped_edge_count steps last end
  else
    begin match steps with | Prims.Nil -> begin () end | Prims.Cons _ rest -> begin cut_path_is_shorter rest (first - 1) (last - 1) end end

let rec dropped_path_starts_at_node (ops: rops) (facts: t_Slice fact) (start: Envelope.t_Id) (steps: Prims.list Envelope.t_Id) (finish: Envelope.t_Id) (count: nat{count <= List.length steps}) : Lemma (requires causal_path ops facts start steps finish) (ensures causal_path ops facts (path_node start steps count) (drop_edges steps count) finish) (decreases steps) =
  if count ==? 0 then
    begin () end
  else
    begin match steps with | Prims.Nil -> begin () end | Prims.Cons next rest -> begin dropped_path_starts_at_node ops facts next rest finish (count - 1) end end

let rec cutting_repeated_node_preserves_path (ops: rops) (facts: t_Slice fact) (start: Envelope.t_Id) (steps: Prims.list Envelope.t_Id) (finish: Envelope.t_Id) (first: nat) (last: nat{Prims.l_and (first < last) (last <= List.length steps)}) : Lemma (requires (causal_path ops facts start steps finish /\ path_node start steps first == path_node start steps last)) (ensures causal_path ops facts start (cut_path_loop steps first last) finish) (decreases steps) =
  if first ==? 0 then
    begin dropped_path_starts_at_node ops facts start steps finish last end
  else
    begin match steps with | Prims.Nil -> begin () end | Prims.Cons next rest -> begin cutting_repeated_node_preserves_path ops facts next rest finish (first - 1) (last - 1) end end

let fact_id_present (ops: rops) (facts: t_Slice fact) (id: Envelope.t_Id) : Type0 =
  exists(k: nat). Prims.l_and (k < Seq.length facts) (ops._1._1 (Seq.index facts k) == id)

let rec path_parent_is_present (ops: rops) (facts: t_Slice fact) (start: Envelope.t_Id) (steps: Prims.list Envelope.t_Id) (finish: Envelope.t_Id) (at: nat{at < List.length steps}) : Lemma (requires causal_path ops facts start steps finish) (ensures fact_id_present ops facts (path_node start steps at)) (decreases steps) =
  match steps with | Prims.Nil -> begin () end | Prims.Cons next rest -> begin if at ==? 0 then
    begin () end
  else
    begin path_parent_is_present ops facts next rest finish (at - 1) end end

let parent_fact_position (ops: rops) (facts: t_Slice fact) (id: Envelope.t_Id{fact_id_present ops facts id}) : i: nat{Prims.l_and (i < Seq.length facts) (ops._1._1 (Seq.index facts i) == id)} =
  match FStar.Fin.find facts (fun (f: fact) -> ops._1._1 f ==? id) 0 with | Some i -> begin i end | None -> begin 0 end

let path_parent_position (ops: rops) (facts: t_Slice fact) (start: Envelope.t_Id) (finish: Envelope.t_Id) (steps: Prims.list Envelope.t_Id{causal_path ops facts start steps finish}) (at: nat{at < List.length steps}) : position: FStar.Fin.under (Seq.length facts){ops._1._1 (Seq.index facts position) == path_node start steps at} =
  path_parent_is_present ops facts start steps finish at;
  parent_fact_position ops facts (path_node start steps at)

let rec every_path_has_short_path (ops: rops) (facts: t_Slice fact) (start: Envelope.t_Id) (steps: Prims.list Envelope.t_Id) (finish: Envelope.t_Id) : Lemma (requires causal_path ops facts start steps finish) (ensures exists(short: Prims.list Envelope.t_Id). Prims.l_and (List.length short <= Seq.length facts) (causal_path ops facts start short finish)) (decreases List.length steps) =
  let count = Seq.length facts in
  if List.length steps <= count then
    begin assert (Prims.l_and (List.length steps <= count) (causal_path ops facts start steps finish)) end
  else
    begin if count ==? 0 then
      begin path_parent_is_present ops facts start steps finish 0;
      let position = parent_fact_position ops facts start in
      assert (position < count) end
    else
      begin let position = path_parent_position ops facts start finish steps in
      let positions = Seq.init (count + 1) position in
      Seq.lemma_init_len (count + 1) position;
      Seq.init_index (count + 1) position;
      match FStar.Fin.pigeonhole positions with | (i, j) -> begin assert (Prims.l_and (i < j) (j < count + 1));
      assert (position i == position j);
      assert (path_node start steps i == path_node start steps j);
      cutting_repeated_node_preserves_path ops facts start steps finish i j;
      cut_path_is_shorter steps i j;
      let shorter = cut_path_loop steps i j in
      every_path_has_short_path ops facts start shorter finish end end end

let past_contains_every_causal_path (ops: rops) (facts: t_Slice fact) (roots: t_Slice Envelope.t_Id) (root: Envelope.t_Id) (steps: Prims.list Envelope.t_Id) (id: Envelope.t_Id) : Lemma (requires (ids_exact ops /\ member roots root /\ causal_path ops facts root steps id)) (ensures ((match Shared.past facts roots ops with | Result.Result_Ok selected -> begin member (Alloc.Vec.impl_1__as_slice selected) id end | _ -> begin Prims.l_True end) <: Type0)) =
  every_path_has_short_path ops facts root steps id;
  let each_short (short: Prims.list Envelope.t_Id) : Lemma (requires (List.length short <= Seq.length facts /\ causal_path ops facts root short id)) (ensures ((match Shared.past facts roots ops with | Result.Result_Ok selected -> begin member (Alloc.Vec.impl_1__as_slice selected) id end | _ -> begin Prims.l_True end) <: Type0)) = past_contains_short_paths ops facts roots root short id in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each_short);
  assert (((match Shared.past facts roots ops with | Result.Result_Ok selected -> begin member (Alloc.Vec.impl_1__as_slice selected) id end | _ -> begin Prims.l_True end) <: Type0)) by (
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.smt_sync' 1 1
  )

let exact_past_result (ops: rops) (facts: t_Slice fact) (roots: t_Slice Envelope.t_Id) (result: Result.t_Result ids_vec Native.t_Error) : Type0 =
  match result with | Result.Result_Ok selected -> begin forall(id: Envelope.t_Id). member (Alloc.Vec.impl_1__as_slice selected) id <==> ancestor ops facts roots id end | _ -> begin Prims.l_True end

let successful_past_is_exact_closure (ops: rops) (facts: t_Slice fact) (roots: t_Slice Envelope.t_Id) : Lemma (requires ids_exact ops) (ensures exact_past_result ops facts roots (Shared.past facts roots ops)) =
  past_has_only_ancestors_and_keeps_roots ops facts roots;
  match Shared.past facts roots ops with | Result.Result_Ok selected -> begin let each_id (id: Envelope.t_Id) : Lemma (ensures member (Alloc.Vec.impl_1__as_slice selected) id <==> ancestor ops facts roots id) =
    let each_selected () : Lemma (requires member (Alloc.Vec.impl_1__as_slice selected) id) (ensures ancestor ops facts roots id) = member_satisfies (Alloc.Vec.impl_1__as_slice selected) (ancestor ops facts roots) id in
    FStar.Classical.move_requires each_selected ();
    let each_path (root: Envelope.t_Id) (steps: Prims.list Envelope.t_Id) : Lemma (requires (member roots root /\ causal_path ops facts root steps id)) (ensures member (Alloc.Vec.impl_1__as_slice selected) id) =
      past_contains_every_causal_path ops facts roots root steps id;
      assert (member (Alloc.Vec.impl_1__as_slice selected) id) by (
        Tactics.prune "Nickel_crdt.Event_layer.past";
        Tactics.smt_sync' 1 1
      ) in
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_path) in
  FStar.Classical.forall_intro each_id;
  assert (exact_past_result ops facts roots (Shared.past facts roots ops)) by (
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.smt_sync' 1 1
  ) end | Result.Result_Err _ -> begin assert (exact_past_result ops facts roots (Shared.past facts roots ops)) by (
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.smt_sync' 1 1
  ) end

let copies_exact (ops: rops) : Type0 =
  forall(a: fact). ops._1._5 a == a

unfold type facts_vec = Alloc.Vec.t_Vec fact Alloc.Alloc.t_Global

let rec selected_prefix (ops: rops) (facts: t_Slice fact) (selected: t_Slice Envelope.t_Id) (finish: nat{finish <= Seq.length facts}) (output: Seq.seq fact) : Tot Type0 (decreases finish) =
  if finish ==? 0 then
    begin output == Seq.empty end
  else
    begin let f = Seq.index facts (finish - 1) in
    Prims.l_or (Prims.l_and (member selected (ops._1._1 f)) (exists(before: Seq.seq fact). Prims.l_and (selected_prefix ops facts selected (finish - 1) before) (output == Seq.append before (Seq.create 1 f)))) (Prims.l_and (Prims.l_not (member selected (ops._1._1 f))) (selected_prefix ops facts selected (finish - 1) output)) end

let basis_prefix (ops: rops) (facts: t_Slice fact) (selected: t_Slice Envelope.t_Id) (at: nat) (basis: facts_vec) : Type0 =
  Prims.l_and (Prims.l_and (at <= Seq.length facts) (at <= Seq.length facts ==> selected_prefix ops facts selected at (Alloc.Vec.impl_1__as_slice basis))) (Seq.length (Alloc.Vec.impl_1__as_slice basis) <= at)

let actual_basis_is_exact_filter (ops: rops) (facts: t_Slice fact) (selected: t_Slice Envelope.t_Id) : Lemma (requires Prims.l_and (ids_exact ops) (copies_exact ops)) (ensures Nickel.LoopUtil.result_safe (fun (basis: facts_vec) -> selected_prefix ops facts selected (Seq.length facts) (Alloc.Vec.impl_1__as_slice basis)) (fun (_: Native.t_Error) -> Prims.l_False) (Shared.select_basis facts selected ops)) =
  ops_shape ops;
  let clone (f: fact) : Lemma (ensures Shared.clone_selected_fact f ops._1._5 == f) = () in
  FStar.Classical.forall_intro clone;
  let membership (ids: t_Slice Envelope.t_Id) (id: Envelope.t_Id) : Lemma (ensures Prims.l_and (Shared.has_id ids id ops == true <==> member ids id) (Prims.l_or (Shared.has_id ids id ops == true) (Shared.has_id ids id ops == false))) = id_membership_is_exact ids id ops in
  FStar.Classical.forall_intro_2 membership;
  let push (xs: facts_vec) (item: fact) : Lemma (ensures Shared.push xs item ops._2._1 == Nickel.Canonical.push_outcome xs item ops._2._1) = Nickel.Canonical.push_is_exact xs item ops._2._1 in
  FStar.Classical.forall_intro_2 push;
  Nickel.Vector.empty_vector_contents #fact ();
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len facts) (basis_prefix ops facts selected) (fun (basis: facts_vec) -> basis) (fun (basis: facts_vec) -> selected_prefix ops facts selected (Seq.length facts) (Alloc.Vec.impl_1__as_slice basis)) (fun (_: Native.t_Error) -> Prims.l_False);
  assert (Nickel.LoopUtil.result_safe (fun (basis: facts_vec) -> selected_prefix ops facts selected (Seq.length facts) (Alloc.Vec.impl_1__as_slice basis)) (fun (_: Native.t_Error) -> Prims.l_False) (Shared.select_basis facts selected ops)) by (
    Tactics.prune "Nickel_crdt.Event_layer.clone_selected_fact";
    Tactics.prune "Nickel_crdt.Event_layer.has_id";
    Tactics.prune "Nickel_crdt.Event_layer.push";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel.LoopUtil.step_safe";
    Tactics.prune "Nickel.LoopUtil.output_safe";
    Tactics.smt_sync' 1 1
  )

unfold type reops = Nickel.EventGraph.event_ops fact Envelope.t_Id Native.t_Error

let validated_selection_is_past (facts: t_Slice fact) (offered: fact) (events: usize) (dependencies: usize) (eops: reops) : Lemma (ensures forall(selected: ids_vec). Shared.validate_event facts offered events dependencies eops == Result.Result_Ok selected ==> Shared.past facts (eops._1._1._2 offered) eops._1 == Result.Result_Ok selected) =
  assert (eops == (eops._1, (eops._2._1, eops._2._2, (eops._2._3._1, eops._2._3._2, eops._2._3._3, eops._2._3._4))));
  ops_shape eops._1;
  let membership_boolean (ids: t_Slice Envelope.t_Id) (id: Envelope.t_Id) : Lemma (ensures Prims.l_or (Shared.has_id ids id eops._1 == true) (Shared.has_id ids id eops._1 == false)) [SMTPat (Shared.has_id ids id eops._1)] = () in
  match Shared.past facts (eops._1._1._2 offered) eops._1 with | Result.Result_Ok past_ids -> begin Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len facts) (fun (_: nat) (_: unit) -> Prims.l_True) (fun (_: unit) -> past_ids) (fun (x: ids_vec) -> x == past_ids) (fun (_: Native.t_Error) -> Prims.l_True);
  assert (forall(selected: ids_vec). Shared.validate_event facts offered events dependencies eops == Result.Result_Ok selected ==> Shared.past facts (eops._1._1._2 offered) eops._1 == Result.Result_Ok selected) by (
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.prune "Nickel_crdt.Event_layer.has_id";
    Tactics.prune "Nickel_crdt.Event_layer.duplicate_ids";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.smt_sync' 1 1
  ) end | Result.Result_Err _ -> begin assert (forall(selected: ids_vec). Shared.validate_event facts offered events dependencies eops == Result.Result_Ok selected ==> Shared.past facts (eops._1._1._2 offered) eops._1 == Result.Result_Ok selected) by (
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.prune "Nickel_crdt.Event_layer.has_id";
    Tactics.prune "Nickel_crdt.Event_layer.duplicate_ids";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.smt_sync' 1 1
  ) end

let exact_selection_members (ops: rops) (facts: t_Slice fact) (roots: t_Slice Envelope.t_Id) (selected: ids_vec) : Lemma (requires exact_past_result ops facts roots (Result.Result_Ok selected)) (ensures forall(id: Envelope.t_Id). member (Alloc.Vec.impl_1__as_slice selected) id <==> ancestor ops facts roots id) =
  ()

let exact_filter_output (ops: rops) (facts: t_Slice fact) (selected: t_Slice Envelope.t_Id) (basis: facts_vec) : Lemma (requires Nickel.LoopUtil.result_safe (fun (out: facts_vec) -> selected_prefix ops facts selected (Seq.length facts) (Alloc.Vec.impl_1__as_slice out)) (fun (_: Native.t_Error) -> Prims.l_False) (Result.Result_Ok basis)) (ensures selected_prefix ops facts selected (Seq.length facts) (Alloc.Vec.impl_1__as_slice basis)) =
  ()

let validated_selection_is_exact (facts: t_Slice fact) (offered: fact) (events: usize) (dependencies: usize) (eops: reops) : Lemma (requires ids_exact eops._1) (ensures forall(selected: ids_vec). Shared.validate_event facts offered events dependencies eops == Result.Result_Ok selected ==> (forall(id: Envelope.t_Id). member (Alloc.Vec.impl_1__as_slice selected) id <==> ancestor eops._1 facts (eops._1._1._2 offered) id)) =
  validated_selection_is_past facts offered events dependencies eops;
  successful_past_is_exact_closure eops._1 facts (eops._1._1._2 offered);
  let each (selected: ids_vec) : Lemma (requires Shared.past facts (eops._1._1._2 offered) eops._1 == Result.Result_Ok selected) (ensures forall(id: Envelope.t_Id). member (Alloc.Vec.impl_1__as_slice selected) id <==> ancestor eops._1 facts (eops._1._1._2 offered) id) =
    assert (exact_past_result eops._1 facts (eops._1._1._2 offered) (Result.Result_Ok selected)) by (
      Tactics.prune "Nickel_crdt.Event_layer.past";
      Tactics.smt_sync' 1 1
    );
    exact_selection_members eops._1 facts (eops._1._1._2 offered) selected in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each);
  assert (forall(selected: ids_vec). Shared.validate_event facts offered events dependencies eops == Result.Result_Ok selected ==> (forall(id: Envelope.t_Id). member (Alloc.Vec.impl_1__as_slice selected) id <==> ancestor eops._1 facts (eops._1._1._2 offered) id)) by (
    Tactics.prune "Nickel_crdt.Event_layer.validate_event";
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.smt_sync' 1 1
  )