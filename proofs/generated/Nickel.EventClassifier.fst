(* Latte generated F* view *)
module Nickel.EventClassifier

open Nickel.Prelude

open Rust_primitives

open Core_models

open FStar.Pervasives

open Nickel.LoopUtil

module Native = Nickel_crdt.Event_layer

module Option = Core_models.Option

module Tactics = FStar.Tactics.V2

let rec lookup (#f: Type0) (#i: Type0) (facts: t_Slice f) (fact: f) (id: f -> i) (eq: i -> i -> bool) (same: f -> f -> bool) (at: usize{v at <= v (Core_models.Slice.impl__len facts)}) : Tot (Option.t_Option bool) (decreases v (Core_models.Slice.impl__len facts) - v at) =
  if v at < v (Core_models.Slice.impl__len facts) then
    begin let old = Rust_primitives.Slice.slice_index facts at in
    if eq (id old) (id fact) then
      begin Option.Option_Some (same old fact) end
    else
      begin lookup facts fact id eq same (at +! mk_usize 1) end end
  else
    begin Option.Option_None end

let scan_next (#f: Type0) (#i: Type0) (facts: t_Slice f) (fact: f) (id: f -> i) (eq: i -> i -> bool) : Nickel.LoopUtil.transition unit (Core_models.Slice.impl__len facts) =
  fun _ at -> if eq (id (Rust_primitives.Slice.slice_index facts at)) (id fact) then
    begin Option.Option_None end
  else
    begin Option.Option_Some () end

let scan_stop (#f: Type0) (facts: t_Slice f) (fact: f) (same: f -> f -> bool) (_: unit) (at: usize{v at < v (Core_models.Slice.impl__len facts)}) : Option.t_Option bool =
  Option.Option_Some (same (Rust_primitives.Slice.slice_index facts at) fact)

let scan_done (_: unit) : Option.t_Option bool =
  Option.Option_None

let run (#f: Type0) (#i: Type0) (facts: t_Slice f) (fact: f) (id: f -> i) (eq: i -> i -> bool) (same: f -> f -> bool) (at: usize{v at <= v (Core_models.Slice.impl__len facts)}) : Option.t_Option bool =
  Nickel.LoopUtil.option_run (Core_models.Slice.impl__len facts) at () (scan_next facts fact id eq) (scan_stop facts fact same) scan_done

let rec scan_matches_lookup (#f: Type0) (#i: Type0) (facts: t_Slice f) (fact: f) (id: f -> i) (eq: i -> i -> bool) (same: f -> f -> bool) (at: usize{v at <= v (Core_models.Slice.impl__len facts)}) : Lemma (ensures run facts fact id eq same at == lookup facts fact id eq same at) (decreases v (Core_models.Slice.impl__len facts) - v at) =
  if v at < v (Core_models.Slice.impl__len facts) then
    begin Nickel.LoopUtil.option_run_step (Core_models.Slice.impl__len facts) at () (scan_next facts fact id eq) (scan_stop facts fact same) scan_done;
    if not (eq (id (Rust_primitives.Slice.slice_index facts at)) (id fact)) then
      begin scan_matches_lookup facts fact id eq same (at +! mk_usize 1) end
    else
      begin () end end
  else
    begin Nickel.LoopUtil.option_run_end (Core_models.Slice.impl__len facts) at () (scan_next facts fact id eq) (scan_stop facts fact same) scan_done end

let classification_is_exact (#f: Type0) (#i: Type0) (facts: t_Slice f) (fact: f) (id: f -> i) (eq: i -> i -> bool) (same: f -> f -> bool) : Lemma (ensures Native.classify facts fact id eq same == lookup facts fact id eq same (mk_usize 0)) [SMTPat (Native.classify facts fact id eq same)] =
  Nickel.LoopUtil.option_interpret_any (mk_usize 0) (Core_models.Slice.impl__len facts) (scan_next facts fact id eq) (scan_stop facts fact same) scan_done;
  scan_matches_lookup facts fact id eq same (mk_usize 0);
  assert (Native.classify facts fact id eq same == lookup facts fact id eq same (mk_usize 0)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel.LoopUtil.option_run";
    Tactics.smt_sync' 1 1
  )