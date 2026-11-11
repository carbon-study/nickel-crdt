(* Latte generated F* view *)
module Nickel.LoopEquality

open Nickel.Prelude

open Rust_primitives

open Rust_primitives.Hax.Folds

open Core_models.Ops.Control_flow

open FStar.Pervasives

open FStar.Classical

open Nickel.LoopUtil

module Tactics = FStar.Tactics.V2

let rec pointwise_callbacks (#state: Type0) (#result: Type0) (start: usize) (finish: usize{v start <= v finish}) (left_inv: Nickel.LoopUtil.invariant state start finish) (right_inv: Nickel.LoopUtil.invariant state start finish) (value: state) (left: Nickel.LoopUtil.callback state result start finish) (right: Nickel.LoopUtil.callback state result start finish) : Lemma (requires forall(s: state) (i: Nickel.LoopUtil.position start finish). left s i == right s i) (ensures fold_range_return start finish left_inv value left == fold_range_return start finish right_inv value right) (decreases v finish - v start) =
  if v start < v finish then
    begin Nickel.LoopUtil.unroll start finish left_inv value left;
    Nickel.LoopUtil.unroll start finish right_inv value right;
    match left value start with | ControlFlow_Continue next -> begin pointwise_callbacks (start +! mk_usize 1) finish left_inv right_inv next left right end | _ -> begin () end;
    assert (fold_range_return start finish left_inv value left == fold_range_return start finish right_inv value right) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.smt_sync' 1 1
    ) end
  else
    begin Nickel.LoopUtil.empty start finish left_inv value left;
    Nickel.LoopUtil.empty start finish right_inv value right end

let pointwise_callbacks_any (#state: Type0) (#result: Type0) (start: usize) (finish: usize{v start <= v finish}) : Lemma (ensures forall(left_inv: Nickel.LoopUtil.invariant state start finish) (right_inv: Nickel.LoopUtil.invariant state start finish) (value: state) (left: Nickel.LoopUtil.callback state result start finish) (right: Nickel.LoopUtil.callback state result start finish). (forall(s: state) (i: Nickel.LoopUtil.position start finish). left s i == right s i) ==> fold_range_return start finish left_inv value left == fold_range_return start finish right_inv value right) =
  let annotations (left_inv: Nickel.LoopUtil.invariant state start finish) (right_inv: Nickel.LoopUtil.invariant state start finish) (value: state) : Lemma (ensures forall(left: Nickel.LoopUtil.callback state result start finish) (right: Nickel.LoopUtil.callback state result start finish). (forall(s: state) (i: Nickel.LoopUtil.position start finish). left s i == right s i) ==> fold_range_return start finish left_inv value left == fold_range_return start finish right_inv value right) =
    let each (left: Nickel.LoopUtil.callback state result start finish) (right: Nickel.LoopUtil.callback state result start finish) : Lemma (requires forall(s: state) (i: Nickel.LoopUtil.position start finish). left s i == right s i) (ensures fold_range_return start finish left_inv value left == fold_range_return start finish right_inv value right) = pointwise_callbacks start finish left_inv right_inv value left right in
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each) in
  FStar.Classical.forall_intro_3 annotations