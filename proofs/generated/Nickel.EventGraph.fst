(* Latte generated F* view *)
module Nickel.EventGraph

open Nickel.Prelude

open Rust_primitives

open Core_models

open FStar.Pervasives

open Nickel.LoopUtil

module Native = Nickel_crdt.Event_layer

module Seq = FStar.Seq

module Option = Core_models.Option

unfold type graph_fields (f: Type0) (i: Type0) = (f -> i) & (f -> t_Slice i) & (i -> i -> bool) & (i -> i -> bool) & (f -> f) & (f -> f -> bool)

unfold type graph_errors (e: Type0) = (unit -> e) & (unit -> e)

unfold type graph_ops (f: Type0) (i: Type0) (e: Type0) = graph_fields f i & graph_errors e

unfold type admission_errors (e: Type0) = (unit -> e) & (unit -> e)

unfold type admission_fields (i: Type0) (e: Type0) = (i -> Option.t_Option i) & (i -> i -> bool) & admission_errors e

unfold type event_ops (f: Type0) (i: Type0) (e: Type0) = graph_ops f i e & admission_fields i e

let graph_callbacks_match (#f: Type0) (#i: Type0) (#e: Type0) (ops: graph_ops f i e) (id: f -> i) (after: f -> t_Slice i) (eq: i -> i -> bool) (lt: i -> i -> bool) (copy: f -> f) (same: f -> f -> bool) (internal: unit -> e) (missing: unit -> e) : Type0 =
  Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (ops._1._1 == id) (ops._1._2 == after)) (ops._1._3 == eq)) (ops._1._4 == lt)) (ops._1._5 == copy)) (ops._1._6 == same)) (ops._2._1 == internal)) (ops._2._2 == missing)

let graph_ops_preserve_callbacks (#f: Type0) (#i: Type0) (#e: Type0) (id: f -> i) (after: f -> t_Slice i) (eq: i -> i -> bool) (lt: i -> i -> bool) (copy: f -> f) (same: f -> f -> bool) (internal: unit -> e) (missing: unit -> e) : Lemma (ensures graph_callbacks_match (Native.graph_ops id after eq lt copy same internal missing) id after eq lt copy same internal missing) =
  ()

let event_callbacks_match (#f: Type0) (#i: Type0) (#e: Type0) (ops: event_ops f i e) (graph: graph_ops f i e) (predecessor: i -> Option.t_Option i) (forbidden: i -> i -> bool) (duplicate: unit -> e) (producer: unit -> e) : Type0 =
  Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (ops._1 == graph) (ops._2._1 == predecessor)) (ops._2._2 == forbidden)) (ops._2._3._1 == duplicate)) (ops._2._3._2 == producer)

let event_ops_preserve_callbacks (#f: Type0) (#i: Type0) (#e: Type0) (graph: graph_ops f i e) (predecessor: i -> Option.t_Option i) (forbidden: i -> i -> bool) (duplicate: unit -> e) (producer: unit -> e) : Lemma (ensures event_callbacks_match (Native.event_ops graph predecessor forbidden duplicate producer) graph predecessor forbidden duplicate producer) =
  ()

let absent_prefix (#i: Type0) (ids: t_Slice i) (wanted: i) (eq: i -> i -> bool) (finish: nat) : Type0 =
  forall(at: usize{v at < Seq.length ids}). v at < finish ==> eq (Seq.index ids (v at)) wanted == false

let member (#i: Type0) (ids: t_Slice i) (wanted: i) (eq: i -> i -> bool) : Type0 =
  Prims.l_not (absent_prefix ids wanted eq (Seq.length ids))

let membership_is_exact (#f: Type0) (#i: Type0) (#e: Type0) (ids: t_Slice i) (wanted: i) (ops: graph_ops f i e) : Lemma (ensures Native.has_id ids wanted ops == true <==> member ids wanted ops._1._3) [SMTPat (Native.has_id ids wanted ops)] =
  Nickel.LoopUtil.preserve_any (mk_usize 0) (Core_models.Slice.impl__len ids) (fun (at: nat) (_: unit) -> absent_prefix ids wanted ops._1._3 at) (fun (_: unit) -> Prims.l_not (member ids wanted ops._1._3)) (fun (b: bool) -> Prims.l_and (b == true) (member ids wanted ops._1._3));
  assert (Native.has_id ids wanted ops == true <==> member ids wanted ops._1._3) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.smt_sync' 1 1
  )

let all_ids (#i: Type0) (ids: t_Slice i) (p: i -> Type0) : Type0 =
  forall(at: usize{v at < Seq.length ids}). p (Seq.index ids (v at))

let ready_prefix (#i: Type0) (after: t_Slice i) (done: t_Slice i) (eq: i -> i -> bool) (finish: nat) : Type0 =
  forall(at: usize{v at < Seq.length after}). v at < finish ==> member done (Seq.index after (v at)) eq

let readiness_is_exact (#f: Type0) (#i: Type0) (#e: Type0) (after: t_Slice i) (done: t_Slice i) (ops: graph_ops f i e) : Lemma (ensures Native.ready after done ops == true <==> all_ids after (fun (wanted: i) -> member done wanted ops._1._3)) [SMTPat (Native.ready after done ops)] =
  Nickel.LoopUtil.preserve_any (mk_usize 0) (Core_models.Slice.impl__len after) (fun (at: nat) (_: unit) -> ready_prefix after done ops._1._3 at) (fun (_: unit) -> all_ids after (fun (wanted: i) -> member done wanted ops._1._3)) (fun (b: bool) -> Prims.l_and (b == false) (Prims.l_not (all_ids after (fun (wanted: i) -> member done wanted ops._1._3))));
  assert (Native.ready after done ops == true <==> all_ids after (fun (wanted: i) -> member done wanted ops._1._3)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel_crdt.Event_layer.has_id";
    Tactics.smt_sync' 1 1
  )

let eligible (#f: Type0) (#i: Type0) (facts: t_Slice f) (done: t_Slice i) (id: f -> i) (after: f -> t_Slice i) (eq: i -> i -> bool) (at: nat{at < Seq.length facts}) : Type0 =
  Prims.l_and (Prims.l_not (member done (id (Seq.index facts at)) eq)) (all_ids (after (Seq.index facts at)) (fun (wanted: i) -> member done wanted eq))

let no_eligible_prefix (#f: Type0) (#i: Type0) (facts: t_Slice f) (done: t_Slice i) (id: f -> i) (after: f -> t_Slice i) (eq: i -> i -> bool) (finish: nat) : Type0 =
  forall(at: usize{v at < Seq.length facts}). v at < finish ==> Prims.l_not (eligible facts done id after eq (v at))

let chosen_is_first (#f: Type0) (#i: Type0) (facts: t_Slice f) (done: t_Slice i) (id: f -> i) (after: f -> t_Slice i) (eq: i -> i -> bool) (result: Option.t_Option usize) : Type0 =
  match result with | Option.Option_None -> begin no_eligible_prefix facts done id after eq (Seq.length facts) end | Option.Option_Some at -> begin Prims.l_and (v at < Seq.length facts) (Prims.l_and (v at < Seq.length facts ==> eligible facts done id after eq (v at)) (no_eligible_prefix facts done id after eq (v at))) end

let scheduler_choice_is_exact (#f: Type0) (#i: Type0) (#e: Type0) (facts: t_Slice f) (done: t_Slice i) (ops: graph_ops f i e) : Lemma (ensures chosen_is_first facts done ops._1._1 ops._1._2 ops._1._3 (Native.choose_ready facts done ops)) =
  Nickel.LoopUtil.preserve_any (mk_usize 0) (Core_models.Slice.impl__len facts) (fun (at: nat) (_: unit) -> no_eligible_prefix facts done ops._1._1 ops._1._2 ops._1._3 at) (fun (_: unit) -> no_eligible_prefix facts done ops._1._1 ops._1._2 ops._1._3 (Seq.length facts)) (chosen_is_first facts done ops._1._1 ops._1._2 ops._1._3);
  assert (chosen_is_first facts done ops._1._1 ops._1._2 ops._1._3 (Native.choose_ready facts done ops)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel_crdt.Event_layer.has_id";
    Tactics.prune "Nickel_crdt.Event_layer.ready";
    Tactics.smt_sync' 1 1
  )

let fact_absent_prefix (#f: Type0) (#i: Type0) (facts: t_Slice f) (wanted: i) (id: f -> i) (eq: i -> i -> bool) (finish: nat) : Type0 =
  forall(at: usize{v at < Seq.length facts}). v at < finish ==> eq (id (Seq.index facts (v at))) wanted == false

let fact_membership_is_exact (#f: Type0) (#i: Type0) (#e: Type0) (facts: t_Slice f) (wanted: i) (ops: graph_ops f i e) : Lemma (ensures Native.has_fact facts wanted ops == true <==> Prims.l_not (fact_absent_prefix facts wanted ops._1._1 ops._1._3 (Seq.length facts))) [SMTPat (Native.has_fact facts wanted ops)] =
  Nickel.LoopUtil.preserve_any (mk_usize 0) (Core_models.Slice.impl__len facts) (fun (at: nat) (_: unit) -> fact_absent_prefix facts wanted ops._1._1 ops._1._3 at) (fun (_: unit) -> fact_absent_prefix facts wanted ops._1._1 ops._1._3 (Seq.length facts)) (fun (b: bool) -> Prims.l_and (b == true) (Prims.l_not (fact_absent_prefix facts wanted ops._1._1 ops._1._3 (Seq.length facts))));
  assert (Native.has_fact facts wanted ops == true <==> Prims.l_not (fact_absent_prefix facts wanted ops._1._1 ops._1._3 (Seq.length facts))) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.smt_sync' 1 1
  )