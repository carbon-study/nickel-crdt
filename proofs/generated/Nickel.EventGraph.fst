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

let absent_prefix (#i: Type0) (ids: t_Slice i) (wanted: i) (eq: i -> i -> bool) (finish: nat) : Type0 =
  forall(at: usize{v at < Seq.length ids}). v at < finish ==> eq (Seq.index ids (v at)) wanted == false

let member (#i: Type0) (ids: t_Slice i) (wanted: i) (eq: i -> i -> bool) : Type0 =
  Prims.l_not (absent_prefix ids wanted eq (Seq.length ids))

let membership_is_exact (#i: Type0) (ids: t_Slice i) (wanted: i) (eq: i -> i -> bool) : Lemma (ensures Native.has_id ids wanted eq == true <==> member ids wanted eq) [SMTPat (Native.has_id ids wanted eq)] =
  Nickel.LoopUtil.preserve_any (mk_usize 0) (Core_models.Slice.impl__len ids) (fun (at: nat) (_: unit) -> absent_prefix ids wanted eq at) (fun (_: unit) -> Prims.l_not (member ids wanted eq)) (fun (b: bool) -> Prims.l_and (b == true) (member ids wanted eq));
  assert (Native.has_id ids wanted eq == true <==> member ids wanted eq) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.smt_sync' 1 1
  )

let all_ids (#i: Type0) (ids: t_Slice i) (p: i -> Type0) : Type0 =
  forall(at: usize{v at < Seq.length ids}). p (Seq.index ids (v at))

let ready_prefix (#i: Type0) (after: t_Slice i) (done: t_Slice i) (eq: i -> i -> bool) (finish: nat) : Type0 =
  forall(at: usize{v at < Seq.length after}). v at < finish ==> member done (Seq.index after (v at)) eq

let readiness_is_exact (#i: Type0) (after: t_Slice i) (done: t_Slice i) (eq: i -> i -> bool) : Lemma (ensures Native.ready after done eq == true <==> all_ids after (fun (wanted: i) -> member done wanted eq)) [SMTPat (Native.ready after done eq)] =
  Nickel.LoopUtil.preserve_any (mk_usize 0) (Core_models.Slice.impl__len after) (fun (at: nat) (_: unit) -> ready_prefix after done eq at) (fun (_: unit) -> all_ids after (fun (wanted: i) -> member done wanted eq)) (fun (b: bool) -> Prims.l_and (b == false) (Prims.l_not (all_ids after (fun (wanted: i) -> member done wanted eq))));
  assert (Native.ready after done eq == true <==> all_ids after (fun (wanted: i) -> member done wanted eq)) by (
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

let scheduler_choice_is_exact (#f: Type0) (#i: Type0) (facts: t_Slice f) (done: t_Slice i) (id: f -> i) (after: f -> t_Slice i) (eq: i -> i -> bool) : Lemma (ensures chosen_is_first facts done id after eq (Native.choose_ready facts done id after eq)) =
  Nickel.LoopUtil.preserve_any (mk_usize 0) (Core_models.Slice.impl__len facts) (fun (at: nat) (_: unit) -> no_eligible_prefix facts done id after eq at) (fun (_: unit) -> no_eligible_prefix facts done id after eq (Seq.length facts)) (chosen_is_first facts done id after eq);
  assert (chosen_is_first facts done id after eq (Native.choose_ready facts done id after eq)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel_crdt.Event_layer.has_id";
    Tactics.prune "Nickel_crdt.Event_layer.ready";
    Tactics.smt_sync' 1 1
  )

let fact_absent_prefix (#f: Type0) (#i: Type0) (facts: t_Slice f) (wanted: i) (id: f -> i) (eq: i -> i -> bool) (finish: nat) : Type0 =
  forall(at: usize{v at < Seq.length facts}). v at < finish ==> eq (id (Seq.index facts (v at))) wanted == false

let fact_membership_is_exact (#f: Type0) (#i: Type0) (facts: t_Slice f) (wanted: i) (id: f -> i) (eq: i -> i -> bool) : Lemma (ensures Native.has_fact facts wanted id eq == true <==> Prims.l_not (fact_absent_prefix facts wanted id eq (Seq.length facts))) [SMTPat (Native.has_fact facts wanted id eq)] =
  Nickel.LoopUtil.preserve_any (mk_usize 0) (Core_models.Slice.impl__len facts) (fun (at: nat) (_: unit) -> fact_absent_prefix facts wanted id eq at) (fun (_: unit) -> fact_absent_prefix facts wanted id eq (Seq.length facts)) (fun (b: bool) -> Prims.l_and (b == true) (Prims.l_not (fact_absent_prefix facts wanted id eq (Seq.length facts))));
  assert (Native.has_fact facts wanted id eq == true <==> Prims.l_not (fact_absent_prefix facts wanted id eq (Seq.length facts))) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.smt_sync' 1 1
  )