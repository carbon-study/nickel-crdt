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
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (mk_usize 0) (fun (_: nat) (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) -> selection_ok roots p selected) (fun (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) -> selected) (selection_ok roots p) (fun (_: et) -> Prims.l_True);
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

let causal_edge (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (newer: it) (older: it) : Type0 =
  exists(k: nat). Prims.l_and (Prims.l_and (k < Seq.length facts) (ops._1._1 (Seq.index facts k) == newer)) (member (ops._1._2 (Seq.index facts k)) older)

let expanded_prefix (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (fact: ft) (finish: nat) (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) : Type0 =
  forall(i: usize{v i < Seq.length (ops._1._2 fact)}). v i < finish ==> member (Alloc.Vec.impl_1__as_slice selected) (Seq.index (ops._1._2 fact) (v i))

let expansion_ok (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (fact: ft) (before: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) (next: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) : Type0 =
  Prims.l_and (retains (Alloc.Vec.impl_1__as_slice before) next) (member (Alloc.Vec.impl_1__as_slice before) (ops._1._1 fact) ==> expanded_prefix ops fact (Seq.length (ops._1._2 fact)) next)

let expansion_result (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (fact: ft) (before: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) (result: Result.t_Result (Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) et) : Type0 =
  match result with | Result.Result_Ok next -> begin expansion_ok ops fact before next end | _ -> begin Prims.l_True end

let extend_past_covers_predecessors (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (fact: ft) (before: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) : Lemma (requires ids_exact ops) (ensures expansion_result ops fact before (Shared.extend_past fact before ops)) =
  ops_shape ops;
  let membership_boolean (ids: t_Slice it) (id: it) : Lemma (ensures Prims.l_or (Shared.has_id ids id ops == true) (Shared.has_id ids id ops == false)) [SMTPat (Shared.has_id ids id ops)] = () in
  extend_past_preserves ops (Alloc.Vec.impl_1__as_slice before) (fun (_: it) -> Prims.l_True) fact before;
  let each_push (at: usize{v at < Seq.length (ops._1._2 fact)}) (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) : Lemma (requires expanded_prefix ops fact (v at) selected) (ensures ((match Shared.push selected (Seq.index (ops._1._2 fact) (v at)) ops._2._1 with | (next, Result.Result_Ok _) -> begin expanded_prefix ops fact (v at + 1) next end | _ -> begin Prims.l_True end) <: Type0)) =
    Nickel.Canonical.push_is_exact selected (Seq.index (ops._1._2 fact) (v at)) ops._2._1;
    assert (((match Shared.push selected (Seq.index (ops._1._2 fact) (v at)) ops._2._1 with | (next, Result.Result_Ok _) -> begin expanded_prefix ops fact (v at + 1) next end | _ -> begin Prims.l_True end) <: Type0)) by (
      Tactics.prune "Nickel_crdt.Event_layer.push";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_push);
  let skip_existing (at: usize{v at < Seq.length (ops._1._2 fact)}) (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) : Lemma (requires (expanded_prefix ops fact (v at) selected /\ Shared.has_id (Alloc.Vec.impl_1__as_slice selected) (Seq.index (ops._1._2 fact) (v at)) ops == true)) (ensures expanded_prefix ops fact (v at + 1) selected) = id_membership_is_exact (Alloc.Vec.impl_1__as_slice selected) (Seq.index (ops._1._2 fact) (v at)) ops in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 skip_existing);
  id_membership_is_exact (Alloc.Vec.impl_1__as_slice before) (ops._1._1 fact) ops;
  if Shared.has_id (Alloc.Vec.impl_1__as_slice before) (ops._1._1 fact) ops then
    begin Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len (ops._1._2 fact)) (fun (at: nat) (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) -> expanded_prefix ops fact at selected) (fun (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) -> selected) (fun (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) -> expanded_prefix ops fact (Seq.length (ops._1._2 fact)) selected) (fun (_: et) -> Prims.l_True);
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

let pass_prefix (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (before: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) (finish: nat) (next: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) : Type0 =
  Prims.l_and (retains (Alloc.Vec.impl_1__as_slice before) next) (forall(i: usize{v i < Seq.length facts}). v i < finish ==> expansion_ok ops (Seq.index facts (v i)) before next)

let pass_result (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (before: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) (result: Result.t_Result (Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) et) : Type0 =
  match result with | Result.Result_Ok next -> begin pass_prefix ops facts before (Seq.length facts) next end | _ -> begin Prims.l_True end

let retains_member (#it: eqtype) (before: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) (next: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) (id: it) : Lemma (requires (retains (Alloc.Vec.impl_1__as_slice before) next /\ member (Alloc.Vec.impl_1__as_slice before) id)) (ensures member (Alloc.Vec.impl_1__as_slice next) id) =
  ()

let expansion_composes (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (before: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) (at: usize{v at < Seq.length facts}) (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) (next: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) : Lemma (requires (pass_prefix ops facts before (v at) selected /\ expansion_ok ops (Seq.index facts (v at)) selected next)) (ensures pass_prefix ops facts before (v at + 1) next) =
  let each_id (id: it) : Lemma (requires member (Alloc.Vec.impl_1__as_slice selected) id) (ensures member (Alloc.Vec.impl_1__as_slice next) id) = retains_member selected next id in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each_id);
  let prior_member (id: it) : Lemma (requires member (Alloc.Vec.impl_1__as_slice before) id) (ensures member (Alloc.Vec.impl_1__as_slice selected) id) = retains_member before selected id in
  FStar.Classical.forall_intro (FStar.Classical.move_requires prior_member)

let past_pass_covers_edges (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (before: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) : Lemma (requires ids_exact ops) (ensures pass_result ops facts before (Shared.past_pass facts before ops)) =
  let each_extend (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) (at: usize{v at < Seq.length facts}) : Lemma (requires pass_prefix ops facts before (v at) selected) (ensures ((match Shared.extend_past (Seq.index facts (v at)) selected ops with | Result.Result_Ok next -> begin pass_prefix ops facts before (v at + 1) next end | _ -> begin Prims.l_True end) <: Type0)) =
    extend_past_covers_predecessors ops (Seq.index facts (v at)) selected;
    let each_next (next: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) : Lemma (requires expansion_ok ops (Seq.index facts (v at)) selected next) (ensures pass_prefix ops facts before (v at + 1) next) = expansion_composes ops facts before at selected next in
    FStar.Classical.forall_intro (FStar.Classical.move_requires each_next);
    assert (((match Shared.extend_past (Seq.index facts (v at)) selected ops with | Result.Result_Ok next -> begin pass_prefix ops facts before (v at + 1) next end | _ -> begin Prims.l_True end) <: Type0)) by (
      Tactics.prune "Nickel_crdt.Event_layer.extend_past";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_extend);
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len facts) (pass_prefix ops facts before) (fun (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) -> selected) (fun (next: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) -> pass_prefix ops facts before (Seq.length facts) next) (fun (_: et) -> Prims.l_True);
  assert (pass_result ops facts before (Shared.past_pass facts before ops)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel_crdt.Event_layer.extend_past";
    Tactics.smt_sync' 1 1
  )

let rec reachable_within (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (roots: t_Slice it) (depth: nat) (id: it) : Tot Type0 (decreases depth) =
  Prims.l_or (member roots id) (if depth ==? 0 then
    begin Prims.l_False end
  else
    begin exists(parent: it). Prims.l_and (reachable_within ops facts roots (depth - 1) parent) (causal_edge ops facts parent id) end)

let reachable_within_equations (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (roots: t_Slice it) : Lemma (ensures Prims.l_and (forall(id: it). reachable_within ops facts roots 0 id <==> member roots id) (forall(depth: nat{depth > 0}) (id: it). reachable_within ops facts roots depth id <==> Prims.l_or (member roots id) (exists(parent: it). Prims.l_and (reachable_within ops facts roots (depth - 1) parent) (causal_edge ops facts parent id)))) =
  ()

let covers_depth (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (roots: t_Slice it) (depth: nat) (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) : Type0 =
  forall(id: it). reachable_within ops facts roots depth id ==> member (Alloc.Vec.impl_1__as_slice selected) id

let pass_edge_is_covered (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (before: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) (next: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) (parent: it) (child: it) : Lemma (requires (pass_prefix ops facts before (Seq.length facts) next /\ member (Alloc.Vec.impl_1__as_slice before) parent /\ causal_edge ops facts parent child)) (ensures member (Alloc.Vec.impl_1__as_slice next) child) =
  let each_position (k: nat) : Lemma (requires (Prims.l_and (k < Seq.length facts) (ops._1._1 (Seq.index facts k) == parent) /\ member (ops._1._2 (Seq.index facts k)) child)) (ensures member (Alloc.Vec.impl_1__as_slice next) child) =
    let index = mk_usize k in
    assert (expansion_ok ops (Seq.index facts (v index)) before next) in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each_position)

let pass_covers_next_depth (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (roots: t_Slice it) (depth: nat) (before: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) (next: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) : Lemma (requires (covers_depth ops facts roots depth before /\ pass_prefix ops facts before (Seq.length facts) next)) (ensures covers_depth ops facts roots (depth + 1) next) =
  let old_member (id: it) : Lemma (requires member (Alloc.Vec.impl_1__as_slice before) id) (ensures member (Alloc.Vec.impl_1__as_slice next) id) = retains_member before next id in
  FStar.Classical.forall_intro (FStar.Classical.move_requires old_member);
  let each_parent (parent: it) (child: it) : Lemma (requires (reachable_within ops facts roots depth parent /\ causal_edge ops facts parent child)) (ensures member (Alloc.Vec.impl_1__as_slice next) child) = pass_edge_is_covered ops facts before next parent child in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_parent);
  let each_id (id: it) : Lemma (requires reachable_within ops facts roots (depth + 1) id) (ensures member (Alloc.Vec.impl_1__as_slice next) id) = () in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each_id)

let depth_result (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (roots: t_Slice it) (depth: nat) (result: Result.t_Result (Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) et) : Type0 =
  match result with | Result.Result_Ok selected -> begin covers_depth ops facts roots depth selected end | _ -> begin Prims.l_True end

let past_covers_bounded_predecessor_paths (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (roots: t_Slice it) : Lemma (requires ids_exact ops) (ensures depth_result ops facts roots (Seq.length facts) (Shared.past facts roots ops)) =
  ops_shape ops;
  let each_pass (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) (at: usize{v at < Seq.length facts}) : Lemma (requires covers_depth ops facts roots (v at) selected) (ensures depth_result ops facts roots (v at + 1) (Shared.past_pass facts selected ops)) =
    past_pass_covers_edges ops facts selected;
    assert (pass_result ops facts selected (Shared.past_pass facts selected ops)) by (
      Tactics.prune "Nickel_crdt.Event_layer.past_pass";
      Tactics.prune "Nickel.PastExact.past_pass_covers_edges";
      Tactics.smt_sync' 1 1
    );
    match Shared.past_pass facts selected ops with | Result.Result_Ok next -> begin pass_covers_next_depth ops facts roots (v at) selected next;
    assert (depth_result ops facts roots (v at + 1) (Shared.past_pass facts selected ops)) by (
      Tactics.prune "Nickel_crdt.Event_layer.past_pass";
      Tactics.smt_sync' 1 1
    ) end | Result.Result_Err _ -> begin assert (depth_result ops facts roots (v at + 1) (Shared.past_pass facts selected ops)) by (
      Tactics.prune "Nickel_crdt.Event_layer.past_pass";
      Tactics.smt_sync' 1 1
    ) end in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_pass);
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len facts) (covers_depth ops facts roots) (fun (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) -> selected) (covers_depth ops facts roots (Seq.length facts)) (fun (_: et) -> Prims.l_True);
  assert (depth_result ops facts roots (Seq.length facts) (Shared.past facts roots ops)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel_crdt.Event_layer.past_pass";
    Tactics.prune "Nickel_crdt.Event_layer.validate_after";
    Tactics.smt_sync' 1 1
  )

let rec causal_path (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (start: it) (steps: Prims.list it) (finish: it) : Tot Type0 (decreases steps) =
  match steps with | Prims.Nil -> begin start == finish end | Prims.Cons next rest -> begin Prims.l_and (causal_edge ops facts start next) (causal_path ops facts next rest finish) end

let causal_path_equations (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) : Lemma (ensures Prims.l_and (forall(start: it) (finish: it). causal_path ops facts start Prims.Nil finish <==> start == finish) (forall(start: it) (next: it) (rest: Prims.list it) (finish: it). causal_path ops facts start (Prims.Cons next rest) finish <==> Prims.l_and (causal_edge ops facts start next) (causal_path ops facts next rest finish))) =
  ()

let ancestor (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (roots: t_Slice it) (id: it) : Type0 =
  exists(root: it) (steps: Prims.list it). Prims.l_and (member roots root) (causal_path ops facts root steps id)

let rec append_path_edge (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (root: it) (steps: Prims.list it) (parent: it) (child: it) : Lemma (requires (causal_path ops facts root steps parent /\ causal_edge ops facts parent child)) (ensures causal_path ops facts root (List.append steps (Prims.Cons child Prims.Nil)) child) (decreases steps) =
  causal_path_equations ops facts;
  match steps with | Prims.Nil -> begin () end | Prims.Cons next rest -> begin append_path_edge ops facts next rest parent child end

let ancestor_follows_edge (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (roots: t_Slice it) (parent: it) (child: it) : Lemma (requires (ancestor ops facts roots parent /\ causal_edge ops facts parent child)) (ensures ancestor ops facts roots child) =
  let each_path (root: it) (steps: Prims.list it) : Lemma (requires (member roots root /\ causal_path ops facts root steps parent)) (ensures ancestor ops facts roots child) =
    append_path_edge ops facts root steps parent child;
    assert (Prims.l_and (member roots root) (causal_path ops facts root (List.append steps (Prims.Cons child Prims.Nil)) child)) in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_path)

let ancestor_roots_and_edges (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (roots: t_Slice it) : Lemma (ensures Prims.l_and (all_ids roots (ancestor ops facts roots)) (facts_closed ops facts (ancestor ops facts roots))) =
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

let past_has_only_ancestors_and_keeps_roots (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (roots: t_Slice it) : Lemma (requires ids_exact ops) (ensures selection_result roots (ancestor ops facts roots) (Shared.past facts roots ops)) =
  ancestor_roots_and_edges ops facts roots;
  past_stays_in_closed_set ops facts roots (ancestor ops facts roots)

let rec path_extends_reach (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (roots: t_Slice it) (depth: nat) (start: it) (steps: Prims.list it) (finish: it) : Lemma (requires (reachable_within ops facts roots depth start /\ causal_path ops facts start steps finish)) (ensures reachable_within ops facts roots (depth + List.length steps) finish) (decreases steps) =
  causal_path_equations ops facts;
  reachable_within_equations ops facts roots;
  match steps with | Prims.Nil -> begin () end | Prims.Cons next rest -> begin assert (reachable_within ops facts roots (depth + 1) next);
  path_extends_reach ops facts roots (depth + 1) next rest finish end

let rec reach_allows_more_edges (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (roots: t_Slice it) (depth: nat) (extra: nat) (id: it) : Lemma (requires reachable_within ops facts roots depth id) (ensures reachable_within ops facts roots (depth + extra) id) (decreases depth) =
  reachable_within_equations ops facts roots;
  if depth ==? 0 then
    begin () end
  else
    begin let each_parent (parent: it) : Lemma (requires (reachable_within ops facts roots (depth - 1) parent /\ causal_edge ops facts parent id)) (ensures reachable_within ops facts roots (depth + extra) id) = reach_allows_more_edges ops facts roots (depth - 1) extra parent in
    FStar.Classical.forall_intro (FStar.Classical.move_requires each_parent) end

let past_contains_short_paths (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (roots: t_Slice it) (root: it) (steps: Prims.list it) (id: it) : Lemma (requires (ids_exact ops /\ member roots root /\ causal_path ops facts root steps id /\ List.length steps <= Seq.length facts)) (ensures ((match Shared.past facts roots ops with | Result.Result_Ok selected -> begin member (Alloc.Vec.impl_1__as_slice selected) id end | _ -> begin Prims.l_True end) <: Type0)) =
  path_extends_reach ops facts roots 0 root steps id;
  reach_allows_more_edges ops facts roots (List.length steps) (Seq.length facts - List.length steps) id;
  past_covers_bounded_predecessor_paths ops facts roots;
  assert (((match Shared.past facts roots ops with | Result.Result_Ok selected -> begin member (Alloc.Vec.impl_1__as_slice selected) id end | _ -> begin Prims.l_True end) <: Type0)) by (
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.smt_sync' 1 1
  )

open FStar.Fin

let rec path_node (#it: eqtype) (start: it) (steps: Prims.list it) (at: nat{at <= List.length steps}) : Tot it (decreases steps) =
  match steps with | Prims.Nil -> begin start end | Prims.Cons next rest -> begin if at ==? 0 then
    begin start end
  else
    begin path_node next rest (at - 1) end end

let rec drop_edges (#it: eqtype) (steps: Prims.list it) (count: nat{count <= List.length steps}) : Tot (Prims.list it) (decreases steps) =
  if count ==? 0 then
    begin steps end
  else
    begin match steps with | Prims.Nil -> begin Prims.Nil end | Prims.Cons _ rest -> begin drop_edges rest (count - 1) end end

let rec cut_path_loop (#it: eqtype) (steps: Prims.list it) (first: nat) (last: nat{Prims.l_and (first < last) (last <= List.length steps)}) : Tot (Prims.list it) (decreases steps) =
  if first ==? 0 then
    begin drop_edges steps last end
  else
    begin match steps with | Prims.Nil -> begin Prims.Nil end | Prims.Cons next rest -> begin Prims.Cons next (cut_path_loop rest (first - 1) (last - 1)) end end

let rec dropped_edge_count (#it: eqtype) (steps: Prims.list it) (count: nat{count <= List.length steps}) : Lemma (ensures List.length (drop_edges steps count) == List.length steps - count) (decreases steps) =
  if count ==? 0 then
    begin () end
  else
    begin match steps with | Prims.Nil -> begin () end | Prims.Cons _ rest -> begin dropped_edge_count rest (count - 1) end end

let rec cut_path_is_shorter (#it: eqtype) (steps: Prims.list it) (first: nat) (last: nat{Prims.l_and (first < last) (last <= List.length steps)}) : Lemma (ensures Prims.l_and (List.length (cut_path_loop steps first last) == List.length steps - last + first) (List.length (cut_path_loop steps first last) < List.length steps)) (decreases steps) =
  if first ==? 0 then
    begin dropped_edge_count steps last end
  else
    begin match steps with | Prims.Nil -> begin () end | Prims.Cons _ rest -> begin cut_path_is_shorter rest (first - 1) (last - 1) end end

let rec dropped_path_starts_at_node (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (start: it) (steps: Prims.list it) (finish: it) (count: nat{count <= List.length steps}) : Lemma (requires causal_path ops facts start steps finish) (ensures causal_path ops facts (path_node start steps count) (drop_edges steps count) finish) (decreases steps) =
  causal_path_equations ops facts;
  if count ==? 0 then
    begin () end
  else
    begin match steps with | Prims.Nil -> begin () end | Prims.Cons next rest -> begin dropped_path_starts_at_node ops facts next rest finish (count - 1) end end

let rec cutting_repeated_node_preserves_path (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (start: it) (steps: Prims.list it) (finish: it) (first: nat) (last: nat{Prims.l_and (first < last) (last <= List.length steps)}) : Lemma (requires (causal_path ops facts start steps finish /\ path_node start steps first == path_node start steps last)) (ensures causal_path ops facts start (cut_path_loop steps first last) finish) (decreases steps) =
  causal_path_equations ops facts;
  if first ==? 0 then
    begin dropped_path_starts_at_node ops facts start steps finish last end
  else
    begin match steps with | Prims.Nil -> begin () end | Prims.Cons next rest -> begin cutting_repeated_node_preserves_path ops facts next rest finish (first - 1) (last - 1) end end

let fact_id_present (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (id: it) : Type0 =
  exists(k: nat). Prims.l_and (k < Seq.length facts) (ops._1._1 (Seq.index facts k) == id)

let rec path_parent_is_present (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (start: it) (steps: Prims.list it) (finish: it) (at: nat{at < List.length steps}) : Lemma (requires causal_path ops facts start steps finish) (ensures fact_id_present ops facts (path_node start steps at)) (decreases steps) =
  causal_path_equations ops facts;
  match steps with | Prims.Nil -> begin () end | Prims.Cons next rest -> begin if at ==? 0 then
    begin () end
  else
    begin path_parent_is_present ops facts next rest finish (at - 1) end end

let parent_fact_position (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (id: it{fact_id_present ops facts id}) : i: nat{Prims.l_and (i < Seq.length facts) (ops._1._1 (Seq.index facts i) == id)} =
  match FStar.Fin.find facts (fun (f: ft) -> ops._1._1 f ==? id) 0 with | Some i -> begin i end | None -> begin 0 end

let path_parent_position (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (start: it) (finish: it) (steps: Prims.list it{causal_path ops facts start steps finish}) (at: nat{at < List.length steps}) : position: FStar.Fin.under (Seq.length facts){ops._1._1 (Seq.index facts position) == path_node start steps at} =
  path_parent_is_present ops facts start steps finish at;
  parent_fact_position ops facts (path_node start steps at)

let rec every_path_has_short_path (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (start: it) (steps: Prims.list it) (finish: it) : Lemma (requires causal_path ops facts start steps finish) (ensures exists(short: Prims.list it). Prims.l_and (List.length short <= Seq.length facts) (causal_path ops facts start short finish)) (decreases List.length steps) =
  causal_path_equations ops facts;
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

let past_contains_every_causal_path (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (roots: t_Slice it) (root: it) (steps: Prims.list it) (id: it) : Lemma (requires (ids_exact ops /\ member roots root /\ causal_path ops facts root steps id)) (ensures ((match Shared.past facts roots ops with | Result.Result_Ok selected -> begin member (Alloc.Vec.impl_1__as_slice selected) id end | _ -> begin Prims.l_True end) <: Type0)) =
  every_path_has_short_path ops facts root steps id;
  let each_short (short: Prims.list it) : Lemma (requires (List.length short <= Seq.length facts /\ causal_path ops facts root short id)) (ensures ((match Shared.past facts roots ops with | Result.Result_Ok selected -> begin member (Alloc.Vec.impl_1__as_slice selected) id end | _ -> begin Prims.l_True end) <: Type0)) = past_contains_short_paths ops facts roots root short id in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each_short);
  assert (((match Shared.past facts roots ops with | Result.Result_Ok selected -> begin member (Alloc.Vec.impl_1__as_slice selected) id end | _ -> begin Prims.l_True end) <: Type0)) by (
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.smt_sync' 1 1
  )

let exact_past_result (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (roots: t_Slice it) (result: Result.t_Result (Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) et) : Type0 =
  match result with | Result.Result_Ok selected -> begin forall(id: it). member (Alloc.Vec.impl_1__as_slice selected) id <==> ancestor ops facts roots id end | _ -> begin Prims.l_True end

let successful_past_is_exact_closure (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (roots: t_Slice it) : Lemma (requires ids_exact ops) (ensures exact_past_result ops facts roots (Shared.past facts roots ops)) =
  past_has_only_ancestors_and_keeps_roots ops facts roots;
  match Shared.past facts roots ops with | Result.Result_Ok selected -> begin let each_id (id: it) : Lemma (ensures member (Alloc.Vec.impl_1__as_slice selected) id <==> ancestor ops facts roots id) =
    let each_selected () : Lemma (requires member (Alloc.Vec.impl_1__as_slice selected) id) (ensures ancestor ops facts roots id) = member_satisfies (Alloc.Vec.impl_1__as_slice selected) (ancestor ops facts roots) id in
    FStar.Classical.move_requires each_selected ();
    let each_path (root: it) (steps: Prims.list it) : Lemma (requires (member roots root /\ causal_path ops facts root steps id)) (ensures member (Alloc.Vec.impl_1__as_slice selected) id) =
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

let exact_selection_members (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (roots: t_Slice it) (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) : Lemma (requires exact_past_result ops facts roots (Result.Result_Ok selected)) (ensures forall(id: it). member (Alloc.Vec.impl_1__as_slice selected) id <==> ancestor ops facts roots id) =
  ()

let same_parents (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (into: t_Slice ft) (other: t_Slice ft) (id: it) : Type0 =
  forall(older: it). causal_edge ops into id older <==> causal_edge ops other id older

let shared_ancestry (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (into: t_Slice ft) (other: t_Slice ft) (roots: t_Slice it) : Type0 =
  forall(id: it). ancestor ops into roots id ==> same_parents ops into other id

let rec shared_path_stays_shared (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (into: t_Slice ft) (other: t_Slice ft) (roots: t_Slice it) (start: it) (steps: Prims.list it) (finish: it) : Lemma (requires (shared_ancestry ops into other roots /\ ancestor ops into roots start /\ ancestor ops other roots start /\ Prims.l_or (causal_path ops into start steps finish) (causal_path ops other start steps finish))) (ensures Prims.l_and (ancestor ops into roots finish) (ancestor ops other roots finish)) (decreases steps) =
  causal_path_equations ops into;
  causal_path_equations ops other;
  match steps with | Prims.Nil -> begin () end | Prims.Cons next rest -> begin assert (Prims.l_and (causal_edge ops into start next) (causal_edge ops other start next)) by (
    Tactics.prune "Nickel.PastExact.ancestor";
    Tactics.smt_sync' 1 1
  );
  ancestor_follows_edge ops into roots start next;
  ancestor_follows_edge ops other roots start next;
  assert (Prims.l_and (Prims.l_and (ancestor ops into roots next) (ancestor ops other roots next)) (Prims.l_or (causal_path ops into next rest finish) (causal_path ops other next rest finish))) by (
    Tactics.prune "Nickel.PastExact.ancestor";
    Tactics.prune "Nickel.PastExact.shared_ancestry";
    Tactics.smt_sync' 1 1
  );
  shared_path_stays_shared ops into other roots next rest finish;
  assert (Prims.l_and (ancestor ops into roots finish) (ancestor ops other roots finish)) by (
    Tactics.prune "Nickel.PastExact.ancestor";
    Tactics.prune "Nickel.PastExact.shared_ancestry";
    Tactics.smt_sync' 1 1
  ) end

let shared_ancestry_agrees (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (into: t_Slice ft) (other: t_Slice ft) (roots: t_Slice it) : Lemma (requires shared_ancestry ops into other roots) (ensures forall(id: it). ancestor ops into roots id <==> ancestor ops other roots id) =
  causal_path_equations ops into;
  causal_path_equations ops other;
  let each_path (root: it) (steps: Prims.list it) (id: it) : Lemma (requires (member roots root /\ Prims.l_or (causal_path ops into root steps id) (causal_path ops other root steps id))) (ensures Prims.l_and (ancestor ops into roots id) (ancestor ops other roots id)) =
    assert (causal_path ops into root Prims.Nil root);
    assert (causal_path ops other root Prims.Nil root);
    shared_path_stays_shared ops into other roots root steps id;
    assert (Prims.l_and (ancestor ops into roots id) (ancestor ops other roots id)) by (
      Tactics.prune "Nickel.PastExact.ancestor";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 each_path)

let unique_selection (#it: eqtype) (ids: Seq.seq it) : Type0 =
  forall(i: FStar.Fin.under (Seq.length ids)) (j: FStar.Fin.under (Seq.length ids)). i < j ==> Prims.l_not (Seq.index ids i == Seq.index ids j)

let unique_positions_differ (#it: eqtype) (ids: Seq.seq it) (i: nat{i < Seq.length ids}) (j: nat{Prims.l_and (i < j) (j < Seq.length ids)}) : Lemma (requires unique_selection ids) (ensures Prims.l_not (Seq.index ids i == Seq.index ids j)) =
  ()

let empty_and_singleton_roots_are_unique (#it: eqtype) (id: it) : Lemma (ensures Prims.l_and (unique_selection ((Seq.empty <: Seq.seq it))) (unique_selection (Seq.create 1 id))) =
  ()

let stored_selection (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) : Type0 =
  Prims.l_and (unique_selection (Alloc.Vec.impl_1__as_slice selected)) (all_ids (Alloc.Vec.impl_1__as_slice selected) (fact_id_present ops facts))

let selected_fact_position (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (ids: t_Slice it{all_ids ids (fact_id_present ops facts)}) (at: nat{at < Seq.length ids}) : position: FStar.Fin.under (Seq.length facts){ops._1._1 (Seq.index facts position) == Seq.index ids at} =
  assert (fact_id_present ops facts (Rust_primitives.Slice.slice_index ids (mk_usize at)));
  assert (fact_id_present ops facts (Seq.index ids at));
  parent_fact_position ops facts (Seq.index ids at)

let missing_position (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global{stored_selection ops facts selected}) (id: it{fact_id_present ops facts id}) (at: nat{at <= Seq.length (Alloc.Vec.impl_1__as_slice selected)}) : position: FStar.Fin.under (Seq.length facts){ops._1._1 (Seq.index facts position) == (if at ==? Seq.length (Alloc.Vec.impl_1__as_slice selected) then
  begin id end
else
  begin Seq.index (Alloc.Vec.impl_1__as_slice selected) at end)} =
  if at ==? Seq.length (Alloc.Vec.impl_1__as_slice selected) then
    begin parent_fact_position ops facts id end
  else
    begin selected_fact_position ops facts (Alloc.Vec.impl_1__as_slice selected) at end

let missing_stored_id_leaves_room (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) (id: it) : Lemma (requires (stored_selection ops facts selected /\ fact_id_present ops facts id /\ Prims.l_not (member (Alloc.Vec.impl_1__as_slice selected) id))) (ensures Seq.length (Alloc.Vec.impl_1__as_slice selected) < Seq.length facts) =
  let ids = Alloc.Vec.impl_1__as_slice selected in
  let count = Seq.length ids in
  assert (unique_selection ids);
  assert (absent_prefix ids id count);
  if count < Seq.length facts then
    begin () end
  else
    begin if count ==? 0 then
      begin let position = parent_fact_position ops facts id in
      assert (position < count) end
    else
      begin let position = fun (at: nat{at <= count}) -> ((missing_position ops facts selected id at) <: FStar.Fin.under count) in
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

let stored_result (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (result: Result.t_Result (Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) et) : Type0 =
  match result with | Result.Result_Ok selected -> begin stored_selection ops facts selected end | _ -> begin Prims.l_False end

let stored_push_result (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (result: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global & Result.t_Result unit et) : Type0 =
  match result with | (selected, Result.Result_Ok _) -> begin stored_selection ops facts selected end | _ -> begin Prims.l_False end

let fresh_append_is_unique (#it: eqtype) (before: t_Slice it) (id: it) : Lemma (requires (unique_selection before /\ Prims.l_not (member before id))) (ensures unique_selection (Seq.append before (Seq.create 1 id))) =
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

let distinct_pair_roots_are_unique (#it: eqtype) (a: it) (b: it) : Lemma (requires Prims.l_not (a == b)) (ensures unique_selection (Seq.append (Seq.create 1 a) (Seq.create 1 b))) =
  empty_and_singleton_roots_are_unique a;
  assert (Prims.l_not (member (Seq.create 1 a) b));
  fresh_append_is_unique (Seq.create 1 a) b

let fresh_stored_push_succeeds (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) (id: it) : Lemma (requires (stored_selection ops facts selected /\ fact_id_present ops facts id /\ Prims.l_not (member (Alloc.Vec.impl_1__as_slice selected) id))) (ensures stored_push_result ops facts (Shared.push selected id ops._2._1)) =
  missing_stored_id_leaves_room ops facts selected id;
  fresh_append_is_unique (Alloc.Vec.impl_1__as_slice selected) id;
  selected_push_preserves Seq.empty (fact_id_present ops facts) selected id ops._2._1;
  Nickel.Canonical.push_is_exact selected id ops._2._1;
  assert (stored_push_result ops facts (Shared.push selected id ops._2._1)) by (
    Tactics.prune "Nickel_crdt.Event_layer.push";
    Tactics.smt_sync' 1 1
  )

let extend_stored_selection_succeeds (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (fact: ft) (before: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) : Lemma (requires (stored_selection ops facts before /\ all_ids (ops._1._2 fact) (fact_id_present ops facts) /\ ids_exact ops)) (ensures stored_result ops facts (Shared.extend_past fact before ops)) =
  ops_shape ops;
  let each_push (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) (id: it) : Lemma (requires (stored_selection ops facts selected /\ fact_id_present ops facts id /\ Prims.l_not (member (Alloc.Vec.impl_1__as_slice selected) id))) (ensures stored_push_result ops facts (Shared.push selected id ops._2._1)) =
    fresh_stored_push_succeeds ops facts selected id;
    assert (stored_push_result ops facts (Shared.push selected id ops._2._1)) by (
      Tactics.prune "Nickel_crdt.Event_layer.push";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_push);
  let selected_membership (ids: t_Slice it) (id: it) : Lemma (ensures Shared.has_id ids id ops == true <==> member ids id) [SMTPat (Shared.has_id ids id ops)] = id_membership_is_exact ids id ops in
  if Shared.has_id (Alloc.Vec.impl_1__as_slice before) (ops._1._1 fact) ops then
    begin Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len (ops._1._2 fact)) (fun (_: nat) (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) -> stored_selection ops facts selected) (fun (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) -> selected) (stored_selection ops facts) (fun (_: et) -> Prims.l_False);
    assert (stored_result ops facts (Shared.extend_past fact before ops)) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.prune "Nickel.LoopUtil.step_safe";
      Tactics.prune "Nickel.LoopUtil.output_safe";
      Tactics.prune "Nickel_crdt.Event_layer.has_id";
      Tactics.prune "Nickel_crdt.Event_layer.push";
      Tactics.smt_sync' 1 1
    ) end
  else
    begin assert (stored_result ops facts (Shared.extend_past fact before ops)) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.prune "Nickel_crdt.Event_layer.has_id";
      Tactics.prune "Nickel_crdt.Event_layer.push";
      Tactics.smt_sync' 1 1
    ) end

let history_references_present (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) : Type0 =
  forall(i: nat{i < Seq.length facts}). all_ids (ops._1._2 (Seq.index facts i)) (fact_id_present ops facts)

let stored_pass_succeeds (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (before: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) : Lemma (requires (history_references_present ops facts /\ stored_selection ops facts before /\ ids_exact ops)) (ensures stored_result ops facts (Shared.past_pass facts before ops)) =
  ops_shape ops;
  let each_extend (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) (i: usize{v i < Seq.length facts}) : Lemma (requires stored_selection ops facts selected) (ensures stored_result ops facts (Shared.extend_past (Seq.index facts (v i)) selected ops)) =
    extend_stored_selection_succeeds ops facts (Seq.index facts (v i)) selected;
    assert (stored_result ops facts (Shared.extend_past (Seq.index facts (v i)) selected ops)) by (
      Tactics.prune "Nickel_crdt.Event_layer.extend_past";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_extend);
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len facts) (fun (_: nat) (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) -> stored_selection ops facts selected) (fun (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) -> selected) (stored_selection ops facts) (fun (_: et) -> Prims.l_False);
  assert (stored_result ops facts (Shared.past_pass facts before ops)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel.LoopUtil.step_safe";
    Tactics.prune "Nickel.LoopUtil.output_safe";
    Tactics.prune "Nickel_crdt.Event_layer.extend_past";
    Tactics.smt_sync' 1 1
  )

let present_dependencies_pass_guard (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (after: t_Slice it) : Lemma (requires (ids_exact ops /\ all_ids after (fact_id_present ops facts))) (ensures Shared.validate_after facts after ops == Result.Result_Ok ()) =
  let each_id (id: it) : Lemma (requires fact_id_present ops facts id) (ensures Shared.has_fact facts id ops == true) [SMTPat (Shared.has_fact facts id ops)] =
    let position = parent_fact_position ops facts id in
    Nickel.EventGraph.fact_membership_is_exact facts id ops;
    assert (v (mk_usize position) == position);
    assert (ops._1._3 (ops._1._1 (Seq.index facts (v (mk_usize position)))) id == true) in
  ops_shape ops;
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len after) (fun (_: nat) (_: unit) -> Prims.l_True) (fun (_: unit) -> ()) (fun (_: unit) -> Prims.l_True) (fun (_: et) -> Prims.l_False);
  assert (Shared.validate_after facts after ops == Result.Result_Ok ()) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel.LoopUtil.step_safe";
    Tactics.prune "Nickel.LoopUtil.output_safe";
    Tactics.prune "Nickel_crdt.Event_layer.has_fact";
    Tactics.smt_sync' 1 1
  )

let fitting_closed_history_computes_past (#ft: Type0) (#it: eqtype) (#et: Type0) (ops: Nickel.EventGraph.graph_ops ft it et) (facts: t_Slice ft) (roots: t_Slice it) : Lemma (requires (history_references_present ops facts /\ unique_selection roots /\ all_ids roots (fact_id_present ops facts) /\ ids_exact ops)) (ensures stored_result ops facts (Shared.past facts roots ops)) =
  ops_shape ops;
  present_dependencies_pass_guard ops facts roots;
  assert (stored_selection ops facts (Alloc.Slice.impl__to_vec roots));
  let each_pass (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) : Lemma (requires stored_selection ops facts selected) (ensures stored_result ops facts (Shared.past_pass facts selected ops)) =
    stored_pass_succeeds ops facts selected;
    assert (stored_result ops facts (Shared.past_pass facts selected ops)) by (
      Tactics.prune "Nickel_crdt.Event_layer.past_pass";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each_pass);
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len facts) (fun (_: nat) (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) -> stored_selection ops facts selected) (fun (selected: Alloc.Vec.t_Vec it Alloc.Alloc.t_Global) -> selected) (stored_selection ops facts) (fun (_: et) -> Prims.l_False);
  assert (stored_result ops facts (Shared.past facts roots ops)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel.LoopUtil.step_safe";
    Tactics.prune "Nickel.LoopUtil.output_safe";
    Tactics.prune "Nickel_crdt.Event_layer.past_pass";
    Tactics.prune "Nickel_crdt.Event_layer.validate_after";
    Tactics.smt_sync' 1 1
  )