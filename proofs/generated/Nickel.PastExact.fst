(* Latte generated F* view *)
module Nickel.PastExact

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

module List = FStar.List.Tot

module Result = Core_models.Result

module Seq = FStar.Seq

module Tactics = FStar.Tactics.V2

let ids_exact (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) : Type0 =
  forall(a: it) (b: it). ops._1._3 a b == true <==> a == b

let ids_exact_elim (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) : Lemma (requires ids_exact ops) (ensures forall(a: it) (b: it). ops._1._3 a b == true <==> a == b) =
  ()

let ids_exact_intro (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) : Lemma (requires forall(a: it) (b: it). ops._1._3 a b == true <==> a == b) (ensures ids_exact ops) =
  ()

let absent_prefix (#it: eqtype) (ids: t_Slice it) (id: it) (finish: nat) : Type0 =
  forall(i: usize{v i < Seq.length ids}). v i < finish ==> Seq.index ids (v i) =!= id

let member (#it: eqtype) (ids: t_Slice it) (id: it) : Type0 =
  Prims.l_not (absent_prefix ids id (Seq.length ids))

let id_membership_is_exact (#ft: Type0) (#it: eqtype) (#et: Type0) (ids: t_Slice it) (id: it) (ops: Nickel.EventGraph.graph_ops ft it et) : Lemma (requires ids_exact ops) (ensures Shared.has_id ids id ops == true <==> member ids id) =
  Nickel.EventGraph.membership_is_exact ids id ops;
  assert (Shared.has_id ids id ops == true <==> member ids id) by (
    Tactics.prune "Nickel_crdt.Event_layer.has_id";
    Tactics.smt_sync' 1 1
  )

let all_ids (#it: eqtype) (ids: t_Slice it) (p: it -> Type0) : Type0 =
  forall(i: usize{v i < Seq.length ids}). p (Seq.index ids (v i))

let retains (#it: eqtype) (roots: t_Slice it) (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) : Type0 =
  forall(i: usize{v i < Seq.length roots}). member (Alloc.Vec.impl_1__as_slice selected) (Seq.index roots (v i))

let selection_ok (#it: eqtype) (roots: t_Slice it) (p: it -> Type0) (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) : Type0 =
  Prims.l_and (all_ids (Alloc.Vec.impl_1__as_slice selected) p) (retains roots selected)

let selection_result (#it: eqtype) (#et: Type0) (roots: t_Slice it) (p: it -> Type0) (result: Result.t_Result (Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) et) : Type0 =
  match result with | Result.Result_Ok selected -> begin selection_ok roots p selected end | _ -> begin Prims.l_True end

let member_satisfies (#it: eqtype) (ids: t_Slice it) (p: it -> Type0) (id: it) : Lemma (requires (all_ids ids p /\ member ids id)) (ensures p id) =
  ()

let push_selection_result (#it: eqtype) (#et: Type0) (roots: t_Slice it) (p: it -> Type0) (outcome: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global & Result.t_Result unit et) : Type0 =
  match outcome with | (next, Result.Result_Ok _) -> begin selection_ok roots p next end | _ -> begin Prims.l_True end

let selected_push_preserves (#it: eqtype) (#et: Type0) (roots: t_Slice it) (p: it -> Type0) (before: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) (id: it) (internal: unit -> et) : Lemma (requires (selection_ok roots p before /\ p id)) (ensures push_selection_result roots p (Shared.push before id internal)) =
  Nickel.Canonical.push_is_exact before id internal;
  assert (push_selection_result roots p (Shared.push before id internal)) by (
    Tactics.prune "Nickel_crdt.Event_layer.push";
    Tactics.smt_sync' 1 1
  )

let ops_shape (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) : Lemma (ensures ops == ((ops._1._1, ops._1._2, ops._1._3, ops._1._4, ops._1._5, ops._1._6), (ops._2._1, ops._2._2))) =
  ()

let fact_closed (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (fact: ft) (p: it -> Type0) : Type0 =
  p (ops._1._1 fact) ==> all_ids (ops._1._2 fact) p

let extend_past_preserves (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (roots: t_Slice it) (p: it -> Type0) (fact: ft) (before: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) : Lemma (requires (ids_exact ops /\ selection_ok roots p before /\ fact_closed ops fact p)) (ensures selection_result roots p (Shared.extend_past fact before ops)) =
  let each_push (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) (id: it) : Lemma (requires (selection_ok roots p selected /\ p id)) (ensures push_selection_result roots p (Shared.push selected id ops._2._1)) = selected_push_preserves roots p selected id ops._2._1 in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_push);
  id_membership_is_exact (Alloc.Vec.impl_1__as_slice before) (ops._1._1 fact) ops;
  ops_shape ops;
  if Shared.has_id (Alloc.Vec.impl_1__as_slice before) (ops._1._1 fact) ops then
    begin assert (member (Alloc.Vec.impl_1__as_slice before) (ops._1._1 fact)) by (
      Tactics.prune "Nickel_crdt.Event_layer.has_id";
      Tactics.prune "Nickel.EventGraph.membership_is_exact";
      Tactics.smt_sync' 1 1
    );
    member_satisfies (Alloc.Vec.impl_1__as_slice before) p (ops._1._1 fact);
    assert (all_ids (ops._1._2 fact) p);
    Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len (ops._1._2 fact)) (fun (_: nat) (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) -> selection_ok roots p selected) (fun (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) -> selected) (selection_ok roots p) (fun (_: et) -> Prims.l_True);
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

let facts_closed (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (p: it -> Type0) : Type0 =
  forall(i: usize{v i < Seq.length facts}). fact_closed ops (Seq.index facts (v i)) p

let past_pass_preserves (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (roots: t_Slice it) (p: it -> Type0) (facts: t_Slice ft) (before: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) : Lemma (requires (ids_exact ops /\ selection_ok roots p before /\ facts_closed ops facts p)) (ensures selection_result roots p (Shared.past_pass facts before ops)) =
  let each_extend (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) (i: usize{v i < Seq.length facts}) : Lemma (requires selection_ok roots p selected) (ensures selection_result roots p (Shared.extend_past (Seq.index facts (v i)) selected ops)) = extend_past_preserves ops roots p (Seq.index facts (v i)) selected in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_extend);
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len facts) (fun (_: nat) (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) -> selection_ok roots p selected) (fun (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) -> selected) (selection_ok roots p) (fun (_: et) -> Prims.l_True);
  assert (selection_result roots p (Shared.past_pass facts before ops)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel_crdt.Event_layer.extend_past";
    Tactics.smt_sync' 1 1
  )

let initial_selection_is_valid (#it: eqtype) (roots: t_Slice it) (p: it -> Type0) : Lemma (requires all_ids roots p) (ensures selection_ok roots p (Alloc.Slice.impl__to_vec roots)) =
  ()

let past_stays_in_closed_set (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (roots: t_Slice it) (p: it -> Type0) : Lemma (requires (ids_exact ops /\ all_ids roots p /\ facts_closed ops facts p)) (ensures selection_result roots p (Shared.past facts roots ops)) =
  initial_selection_is_valid roots p;
  ops_shape ops;
  let each_pass (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) : Lemma (requires selection_ok roots p selected) (ensures selection_result roots p (Shared.past_pass facts selected ops)) = past_pass_preserves ops roots p facts selected in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each_pass);
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len facts) (fun (_: nat) (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) -> selection_ok roots p selected) (fun (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) -> selected) (selection_ok roots p) (fun (_: et) -> Prims.l_True);
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (mk_usize 0) (fun (_: nat) (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) -> selection_ok roots p selected) (fun (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) -> selected) (selection_ok roots p) (fun (_: et) -> Prims.l_True);
  assert (selection_result roots p (Shared.past facts roots ops)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel_crdt.Event_layer.past_pass";
    Tactics.prune "Nickel_crdt.Event_layer.validate_after";
    Tactics.smt_sync' 1 1
  )