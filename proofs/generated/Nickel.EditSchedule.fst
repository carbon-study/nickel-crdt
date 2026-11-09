(* Latte generated F* view *)
module Nickel.EditSchedule

open Nickel.Prelude

open Rust_primitives

open Core_models

open FStar.Pervasives

open Nickel.Vector

open Nickel.LoopUtil

open Nickel.EditPast

module Native = Nickel_crdt.Edit

module Seq = FStar.Seq

module Option = Core_models.Option

let ready_prefix (after: t_Slice Native.t_EventId) (done: t_Slice Native.t_EventId) (finish: nat) : Type0 =
  forall(i: usize{v i < Seq.length after}). v i < finish ==> member done (Seq.index after (v i))

let readiness_is_exact (after: t_Slice Native.t_EventId) (done: t_Slice Native.t_EventId) : Lemma (ensures Native.ready after done == true <==> all_ids after (member done)) [SMTPat (Native.ready after done)] =
  Nickel.LoopUtil.preserve_any (mk_usize 0) (Core_models.Slice.impl__len after) (fun (at: nat) (_: unit) -> ready_prefix after done at) (fun (_: unit) -> all_ids after (member done)) (fun (b: bool) -> Prims.l_and (b == false) (Prims.l_not (all_ids after (member done))));
  assert (Native.ready after done == true <==> all_ids after (member done)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel_crdt.Edit.has_event";
    Tactics.smt_sync' 1 1
  )

let eligible (facts: t_Slice Native.t_Fact) (done: t_Slice Native.t_EventId) (i: nat{i < Seq.length facts}) : Type0 =
  Prims.l_and (Prims.l_not (member done (Seq.index facts i).f_id)) (all_ids (Alloc.Vec.impl_1__as_slice (Seq.index facts i).f_after) (member done))

let no_eligible_prefix (facts: t_Slice Native.t_Fact) (done: t_Slice Native.t_EventId) (finish: nat) : Type0 =
  forall(i: usize{v i < Seq.length facts}). v i < finish ==> Prims.l_not (eligible facts done (v i))

let chosen_is_first (facts: t_Slice Native.t_Fact) (done: t_Slice Native.t_EventId) (result: Option.t_Option usize) : Type0 =
  match result with | Option.Option_None -> begin no_eligible_prefix facts done (Seq.length facts) end | Option.Option_Some i -> begin Prims.l_and (v i < Seq.length facts) (Prims.l_and (v i < Seq.length facts ==> eligible facts done (v i)) (no_eligible_prefix facts done (v i))) end

let scheduler_choice_is_exact (facts: t_Slice Native.t_Fact) (done: t_Slice Native.t_EventId) : Lemma (ensures chosen_is_first facts done (Native.choose_ready facts done)) =
  Nickel.LoopUtil.preserve_any (mk_usize 0) (Core_models.Slice.impl__len facts) (fun (at: nat) (_: unit) -> no_eligible_prefix facts done at) (fun (_: unit) -> no_eligible_prefix facts done (Seq.length facts)) (chosen_is_first facts done);
  assert (chosen_is_first facts done (Native.choose_ready facts done)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel_crdt.Edit.has_event";
    Tactics.prune "Nickel_crdt.Edit.ready";
    Tactics.smt_sync' 1 1
  )

let available_event_is_chosen (facts: t_Slice Native.t_Fact) (done: t_Slice Native.t_EventId) (available: usize{v available < Seq.length facts}) : Lemma (requires eligible facts done (v available)) (ensures Prims.l_not (Native.choose_ready facts done == Option.Option_None)) =
  scheduler_choice_is_exact facts done;
  assert (Prims.l_not (Native.choose_ready facts done == Option.Option_None)) by (
    Tactics.prune "Nickel_crdt.Edit.choose_ready";
    Tactics.smt_sync' 1 1
  )