(* Latte generated F* view *)
module Nickel.EditDeletePermutation

open Nickel.Prelude

open Rust_primitives

open Core_models

open Nickel.Vector

open Nickel.LoopUtil

open FStar.Pervasives

open FStar.Classical

open FStar.Mul

module Seq = FStar.Seq

module Props = FStar.Seq.Properties

module Native = Nickel_crdt.Edit

module Flow = Core_models.Ops.Control_flow

module Folds = Rust_primitives.Hax.Folds

module Tactics = FStar.Tactics.V2

type births = Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global

let same_births (before: t_Slice Native.t_BirthId) (after: t_Slice Native.t_BirthId) : Type0 =
  Prims.l_and (Seq.length before == Seq.length after) (forall(id: Native.t_BirthId). Seq.count id before == Seq.count id after)

let copy_births_exact (xs: t_Slice Native.t_BirthId) : Lemma (ensures Alloc.Vec.impl_1__as_slice (Alloc.Slice.impl__to_vec xs) == xs) [SMTPat (Alloc.Slice.impl__to_vec xs)] =
  assert (Alloc.Vec.impl_1__as_slice (Alloc.Slice.impl__to_vec xs) == Seq.append Seq.empty xs);
  Seq.append_empty_l xs;
  ()

let exchange (values: births) (left: usize{v left < Seq.length (Alloc.Vec.impl_1__as_slice values)}) (right: usize{v right < Seq.length (Alloc.Vec.impl_1__as_slice values)}) : births =
  let before = Alloc.Vec.impl_1__as_slice values in
  let one = Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize before left (Rust_primitives.Slice.slice_index before right)) in
  Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (Alloc.Vec.impl_1__as_slice one) right (Rust_primitives.Slice.slice_index before left))

let exchange_preserves_births (values: births) (left: usize{v left < Seq.length (Alloc.Vec.impl_1__as_slice values)}) (right: usize{Prims.l_and (v left <= v right) (v right < Seq.length (Alloc.Vec.impl_1__as_slice values))}) : Lemma (ensures same_births (Alloc.Vec.impl_1__as_slice values) (Alloc.Vec.impl_1__as_slice (exchange values left right))) =
  Props.lemma_swap_permutes (Alloc.Vec.impl_1__as_slice values) (v left) (v right);
  let before = Alloc.Vec.impl_1__as_slice values in
  let after = Alloc.Vec.impl_1__as_slice (exchange values left right) in
  let swapped = Seq.swap before (v left) (v right) in
  assert (forall(i: nat{i < Seq.length before}). Seq.index after i == Seq.index swapped i);
  Seq.lemma_eq_intro after swapped;
  Seq.lemma_eq_elim after swapped;
  ()

let break_keeps (#state: Type0) (p: state -> Type0) (out: Flow.t_ControlFlow (unit & state) state) : Type0 =
  match out with | Flow.ControlFlow_Break (_, next) -> begin p next end | Flow.ControlFlow_Continue next -> begin p next end

let rec break_preserve (#state: Type0) (start: usize) (finish: usize{v start <= v finish}) (inv: Nickel.LoopUtil.total_invariant state start finish) (value: state) (f: Nickel.LoopUtil.break_callback state start finish) (p: state -> Type0) : Lemma (requires (p value /\ (forall(s: state) (at: Nickel.LoopUtil.position start finish). p s ==> break_keeps p (f s at)))) (ensures p (Folds.fold_range_cf start finish inv value f)) (decreases v finish - v start) =
  if v start < v finish then
    begin Nickel.LoopUtil.break_step start finish inv value f;
    match f value start with | Flow.ControlFlow_Break (_, next) -> begin assert (p (Folds.fold_range_cf start finish inv value f)) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_cf";
      Tactics.smt_sync' 1 1
    ) end | Flow.ControlFlow_Continue next -> begin break_preserve (start +! mk_usize 1) finish inv next f p;
    assert (p (Folds.fold_range_cf start finish inv value f)) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_cf";
      Tactics.smt_sync' 1 1
    ) end end
  else
    begin Nickel.LoopUtil.break_end start finish inv value f;
    assert (p (Folds.fold_range_cf start finish inv value f)) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_cf";
      Tactics.smt_sync' 1 1
    ) end

let break_preserve_any (#state: Type0) (start: usize) (finish: usize{v start <= v finish}) (p: state -> Type0) : Lemma (ensures forall(inv: Nickel.LoopUtil.total_invariant state start finish) (value: state) (f: Nickel.LoopUtil.break_callback state start finish). Prims.l_and (p value) (forall(s: state) (at: Nickel.LoopUtil.position start finish). p s ==> break_keeps p (f s at)) ==> p (Folds.fold_range_cf start finish inv value f)) =
  let each (inv: Nickel.LoopUtil.total_invariant state start finish) (value: state) (f: Nickel.LoopUtil.break_callback state start finish) : Lemma (requires (p value /\ (forall(s: state) (at: Nickel.LoopUtil.position start finish). p s ==> break_keeps p (f s at)))) (ensures p (Folds.fold_range_cf start finish inv value f)) =
    break_preserve start finish inv value f p;
    assert (p (Folds.fold_range_cf start finish inv value f)) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_cf";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 each)

let indexed_exchange_preserves (values: births) (left: usize{v left < Seq.length (Alloc.Vec.impl_1__as_slice values)}) (right: usize{Prims.l_and (v left <= v right) (v right < Seq.length (Alloc.Vec.impl_1__as_slice values))}) : Lemma (ensures same_births (Alloc.Vec.impl_1__as_slice values) (Alloc.Vec.impl_1__as_slice (Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (Alloc.Vec.impl_1__as_slice (Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (Alloc.Vec.impl_1__as_slice values) left (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice values) right)))) right (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice values) left))))) [SMTPat (Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (Alloc.Vec.impl_1__as_slice (Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (Alloc.Vec.impl_1__as_slice values) left (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice values) right)))) right (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice values) left)))] =
  exchange_preserves_births values left right;
  ()

type sift_state = usize & births

let sift_items (before: t_Slice Native.t_BirthId) (state: sift_state) : Type0 =
  same_births before (Alloc.Vec.impl_1__as_slice state._2)

let sift_preserves_births (values: births) (start: usize) (finish: usize) : Lemma (ensures same_births (Alloc.Vec.impl_1__as_slice values) (Alloc.Vec.impl_1__as_slice (Native.sift_births values start finish))) [SMTPat (Native.sift_births values start finish)] =
  break_preserve_any (mk_usize 0) (((Rust_primitives.Integers.cast Core_models.Num.impl_usize__BITS) <: usize)) (sift_items (Alloc.Vec.impl_1__as_slice values));
  assert (same_births (Alloc.Vec.impl_1__as_slice values) (Alloc.Vec.impl_1__as_slice (Native.sift_births values start finish))) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_cf";
    Tactics.prune "Alloc.Slice.impl__to_vec";
    Tactics.smt_sync' 1 1
  )

let heap_preserves_births (values: births) (len: usize) : Lemma (ensures same_births (Alloc.Vec.impl_1__as_slice values) (Alloc.Vec.impl_1__as_slice (Native.heap_births values len))) [SMTPat (Native.heap_births values len)] =
  Nickel.LoopUtil.plain_preserve_any (mk_usize 0) (len /! mk_usize 2) (fun (_: nat) (current: births) -> same_births (Alloc.Vec.impl_1__as_slice values) (Alloc.Vec.impl_1__as_slice current)) (fun (current: births) -> same_births (Alloc.Vec.impl_1__as_slice values) (Alloc.Vec.impl_1__as_slice current));
  assert (same_births (Alloc.Vec.impl_1__as_slice values) (Alloc.Vec.impl_1__as_slice (Native.heap_births values len))) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range";
    Tactics.prune "Nickel_crdt.Edit.sift_births";
    Tactics.smt_sync' 1 1
  )

let vector_items (before: t_Slice Native.t_BirthId) (values: births) : Type0 =
  same_births before (Alloc.Vec.impl_1__as_slice values)

let vector_index_exact (values: births) (at: usize{v at < Seq.length (Alloc.Vec.impl_1__as_slice values)}) : Lemma (ensures Core_models.Ops.Index.f_index values at == Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice values) at) [SMTPat (Core_models.Ops.Index.f_index values at)] =
  ()

let drain_step (len: usize) (current: births) (step: Nickel.LoopUtil.position (mk_usize 0) len) : Flow.t_ControlFlow (unit & births) births =
  let finish = len -! mk_usize 1 -! step in
  if Alloc.Vec.impl_1__is_empty current || Rust_primitives.Integers.gte finish (Alloc.Vec.impl_1__len current) then
    begin Flow.ControlFlow_Break ((), current) end
  else
    begin let before = Alloc.Vec.impl_1__as_slice current in
    let one = Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize before (mk_usize 0) (Core_models.Ops.Index.f_index current finish)) in
    let swapped = Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (Alloc.Vec.impl_1__as_slice one) finish (Core_models.Ops.Index.f_index current (mk_usize 0))) in
    Flow.ControlFlow_Continue (Native.sift_births swapped (mk_usize 0) finish) end

let drain_step_preserves (original: t_Slice Native.t_BirthId) (len: usize) (current: births) (step: Nickel.LoopUtil.position (mk_usize 0) len) : Lemma (requires vector_items original current) (ensures break_keeps (vector_items original) (drain_step len current step)) =
  let finish = len -! mk_usize 1 -! step in
  if Alloc.Vec.impl_1__is_empty current || Rust_primitives.Integers.gte finish (Alloc.Vec.impl_1__len current) then
    begin assert (break_keeps (vector_items original) (drain_step len current step));
    () end
  else
    begin let before = Alloc.Vec.impl_1__as_slice current in
    let one = Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize before (mk_usize 0) (Core_models.Ops.Index.f_index current finish)) in
    let swapped = Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (Alloc.Vec.impl_1__as_slice one) finish (Core_models.Ops.Index.f_index current (mk_usize 0))) in
    indexed_exchange_preserves current (mk_usize 0) finish;
    sift_preserves_births swapped (mk_usize 0) finish;
    assert (break_keeps (vector_items original) (drain_step len current step)) by (
      Tactics.prune "Nickel_crdt.Edit.sift_births";
      Tactics.prune "Alloc.Slice.impl__to_vec";
      Tactics.smt_sync' 1 1
    ) end

let drain_callbacks_preserve (original: t_Slice Native.t_BirthId) (len: usize) : Lemma (ensures forall(inv: Nickel.LoopUtil.total_invariant births (mk_usize 0) len) (initial: births) (f: Nickel.LoopUtil.break_callback births (mk_usize 0) len). Prims.l_and (vector_items original initial) (forall(current: births) (at: Nickel.LoopUtil.position (mk_usize 0) len). f current at == drain_step len current at) ==> vector_items original (Folds.fold_range_cf (mk_usize 0) len inv initial f)) =
  let each (inv: Nickel.LoopUtil.total_invariant births (mk_usize 0) len) (initial: births) (f: Nickel.LoopUtil.break_callback births (mk_usize 0) len) : Lemma (requires (vector_items original initial /\ (forall(current: births) (at: Nickel.LoopUtil.position (mk_usize 0) len). f current at == drain_step len current at))) (ensures vector_items original (Folds.fold_range_cf (mk_usize 0) len inv initial f)) =
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (drain_step_preserves original len));
    break_preserve_any (mk_usize 0) len (vector_items original);
    assert (vector_items original (Folds.fold_range_cf (mk_usize 0) len inv initial f)) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_cf";
      Tactics.prune "Nickel.EditDeletePermutation.drain_step";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 each)

let drain_preserves_births (values: births) (len: usize) : Lemma (ensures same_births (Alloc.Vec.impl_1__as_slice values) (Alloc.Vec.impl_1__as_slice (Native.drain_births values len))) [SMTPat (Native.drain_births values len)] =
  drain_callbacks_preserve (Alloc.Vec.impl_1__as_slice values) len;
  assert (vector_items (Alloc.Vec.impl_1__as_slice values) (Native.drain_births values len)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_cf";
    Tactics.prune "Nickel_crdt.Edit.sift_births";
    Tactics.prune "Alloc.Slice.impl__to_vec";
    Tactics.smt_sync' 1 1
  )

let ordered_preserves_births (xs: t_Slice Native.t_BirthId) : Lemma (ensures same_births xs (Alloc.Vec.impl_1__as_slice (Native.ordered_births xs))) [SMTPat (Native.ordered_births xs)] =
  let copied = Alloc.Slice.impl__to_vec xs in
  let len = Alloc.Vec.impl_1__len copied in
  copy_births_exact xs;
  heap_preserves_births copied len;
  drain_preserves_births (Native.heap_births copied len) len;
  assert (same_births xs (Alloc.Vec.impl_1__as_slice (Native.ordered_births xs))) by (
    Tactics.prune "Nickel_crdt.Edit.heap_births";
    Tactics.prune "Nickel_crdt.Edit.drain_births";
    Tactics.prune "Alloc.Slice.impl__to_vec";
    Tactics.smt_sync' 1 1
  )