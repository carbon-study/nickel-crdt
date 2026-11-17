(* Latte generated F* view *)
module Nickel.EditDeleteHeap

open Nickel.Prelude

open Rust_primitives

open Core_models

open Nickel.Vector

open Nickel.LoopUtil

open Nickel.EditDeletePermutation

open FStar.Pervasives

open FStar.Classical

open FStar.Mul

module Math = FStar.Math.Lemmas

module Seq = FStar.Seq

module Native = Nickel_crdt.Edit

module P = Nickel.EditDeletePermutation

module Flow = Core_models.Ops.Control_flow

module Folds = Rust_primitives.Hax.Folds

module Tactics = FStar.Tactics.V2

type births = P.births

let le (a: Native.t_BirthId) (b: Native.t_BirthId) : Type0 =
  Native.birth_lt b a == false

let order_transitive (a: Native.t_BirthId) (b: Native.t_BirthId) (c: Native.t_BirthId) : Lemma (ensures Prims.l_and (le a b) (le b c) ==> le a c) =
  ()

let order_antisymmetric (a: Native.t_BirthId) (b: Native.t_BirthId) : Lemma (ensures Prims.l_and (le a b) (le b a) ==> a == b) =
  ()

let order_total (a: Native.t_BirthId) (b: Native.t_BirthId) : Lemma (ensures Prims.l_and (Prims.l_and (Native.birth_lt a b == true ==> le a b) (Prims.l_or (le a b) (le b a))) (le a a)) =
  ()

let child_of (parent: nat) (child: nat) : Type0 =
  Prims.l_or (child == parent * 2 + 1) (child == parent * 2 + 2)

let heap_from (xs: t_Slice Native.t_BirthId) (base: nat) (finish: nat) : Type0 =
  forall(parent: nat) (child: nat). Prims.l_and (Prims.l_and (Prims.l_and (base <= parent) (child_of parent child)) (child < finish)) (finish <= Seq.length xs) ==> le (Seq.index xs child) (Seq.index xs parent)

let heap_except (xs: t_Slice Native.t_BirthId) (base: nat) (finish: nat) (hole: nat) : Type0 =
  Prims.l_and (forall(parent: nat) (child: nat). Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (base <= parent) (parent <> hole)) (child_of parent child)) (child < finish)) (finish <= Seq.length xs) ==> le (Seq.index xs child) (Seq.index xs parent)) (forall(parent: nat) (child: nat). Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (base <= parent) (child_of parent hole)) (child_of hole child)) (child < finish)) (finish <= Seq.length xs) ==> le (Seq.index xs child) (Seq.index xs parent))

let unchanged_outside (before: t_Slice Native.t_BirthId) (after: t_Slice Native.t_BirthId) (base: nat) (finish: nat) : Type0 =
  Prims.l_and (Seq.length after == Seq.length before) (forall(i: nat{i < Seq.length before}). Prims.l_or (i < base) (finish <= i) ==> Seq.index after i == Seq.index before i)

let segment_reordering (before: t_Slice Native.t_BirthId) (after: t_Slice Native.t_BirthId) (base: nat) (finish: nat) : Type0 =
  Prims.l_and (unchanged_outside before after base finish) (forall(i: nat{i < Seq.length after}). Prims.l_and (base <= i) (i < finish) ==> (exists(j: nat). Prims.l_and (Prims.l_and (Prims.l_and (base <= j) (j < finish)) (j < Seq.length before)) (Seq.index after i == Seq.index before j)))

let segment_reordering_transitive (before: t_Slice Native.t_BirthId) (middle: t_Slice Native.t_BirthId) (after: t_Slice Native.t_BirthId) (base: nat) (finish: nat) : Lemma (requires (segment_reordering before middle base finish /\ segment_reordering middle after base finish)) (ensures segment_reordering before after base finish) =
  ()

let exchange_entries (values: births) (left: usize{v left < Seq.length (Alloc.Vec.impl_1__as_slice values)}) (right: usize{v right < Seq.length (Alloc.Vec.impl_1__as_slice values)}) : Lemma (ensures Prims.l_and (Seq.length (Alloc.Vec.impl_1__as_slice (P.exchange values left right)) == Seq.length (Alloc.Vec.impl_1__as_slice values)) (forall(i: nat{i < Seq.length (Alloc.Vec.impl_1__as_slice values)}). Seq.index (Alloc.Vec.impl_1__as_slice (P.exchange values left right)) i == (if i ==? v left then
  begin Seq.index (Alloc.Vec.impl_1__as_slice values) (v right) end
else
  begin if i ==? v right then
    begin Seq.index (Alloc.Vec.impl_1__as_slice values) (v left) end
  else
    begin Seq.index (Alloc.Vec.impl_1__as_slice values) i end end))) =
  ()

let largest_child (xs: t_Slice Native.t_BirthId) (root: nat) (child: nat) (finish: nat) : Type0 =
  Prims.l_and (Prims.l_and (Prims.l_and (child_of root child) (child < finish)) (finish <= Seq.length xs)) (forall(other: nat). Prims.l_and (child_of root other) (other < finish) ==> le (Seq.index xs other) (Seq.index xs child))

let swap_repairs_hole (values: births) (base: nat) (finish: nat) (root: usize{v root < Seq.length (Alloc.Vec.impl_1__as_slice values)}) (child: usize{v child < Seq.length (Alloc.Vec.impl_1__as_slice values)}) : Lemma (requires (base <= v root /\ heap_except (Alloc.Vec.impl_1__as_slice values) base finish (v root) /\ largest_child (Alloc.Vec.impl_1__as_slice values) (v root) (v child) finish /\ le (Seq.index (Alloc.Vec.impl_1__as_slice values) (v root)) (Seq.index (Alloc.Vec.impl_1__as_slice values) (v child)))) (ensures Prims.l_and (heap_except (Alloc.Vec.impl_1__as_slice (P.exchange values root child)) base finish (v child)) (segment_reordering (Alloc.Vec.impl_1__as_slice values) (Alloc.Vec.impl_1__as_slice (P.exchange values root child)) base finish)) =
  exchange_entries values root child;
  ()

let fitting_root_completes (xs: t_Slice Native.t_BirthId) (base: nat) (finish: nat) (root: nat) (child: nat) : Lemma (requires (base <= root /\ heap_except xs base finish root /\ largest_child xs root child finish /\ le (Seq.index xs child) (Seq.index xs root))) (ensures heap_from xs base finish) =
  let each (other: nat{other < Seq.length xs}) : Lemma (requires Prims.l_and (child_of root other) (other < finish)) (ensures le (Seq.index xs other) (Seq.index xs root)) =
    order_transitive (Seq.index xs other) (Seq.index xs child) (Seq.index xs root);
    () in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each);
  ()

let sift_invariant (before: t_Slice Native.t_BirthId) (base: nat) (finish: nat) (at: nat) (state: P.sift_state) : Type0 =
  Prims.l_and (Prims.l_and (Prims.l_and (base <= v state._1) (Prims.pow2 at <= v state._1 + 1)) (segment_reordering before (Alloc.Vec.impl_1__as_slice state._2) base finish)) (heap_except (Alloc.Vec.impl_1__as_slice state._2) base finish (v state._1))

let sift_post (before: t_Slice Native.t_BirthId) (base: nat) (finish: nat) (state: P.sift_state) : Type0 =
  Prims.l_and (segment_reordering before (Alloc.Vec.impl_1__as_slice state._2) base finish) (heap_from (Alloc.Vec.impl_1__as_slice state._2) base finish)

let break_step_keeps (#state: Type0) (p: nat -> state -> Type0) (post: state -> Type0) (at: nat) (out: Flow.t_ControlFlow (unit & state) state) : Type0 =
  match out with | Flow.ControlFlow_Break (_, next) -> begin post next end | Flow.ControlFlow_Continue next -> begin p (at + 1) next end

let rec break_complete (#state: Type0) (start: usize) (finish: usize{v start <= v finish}) (inv: Nickel.LoopUtil.total_invariant state start finish) (value: state) (f: Nickel.LoopUtil.break_callback state start finish) (p: nat -> state -> Type0) (post: state -> Type0) : Lemma (requires (p (v start) value /\ (forall(s: state) (at: Nickel.LoopUtil.position start finish). p (v at) s ==> break_step_keeps p post (v at) (f s at)) /\ (forall(s: state). p (v finish) s ==> post s))) (ensures post (Folds.fold_range_cf start finish inv value f)) (decreases v finish - v start) =
  if v start < v finish then
    begin Nickel.LoopUtil.break_step start finish inv value f;
    match f value start with | Flow.ControlFlow_Break (_, next) -> begin assert (post (Folds.fold_range_cf start finish inv value f)) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_cf";
      Tactics.smt_sync' 1 1
    ) end | Flow.ControlFlow_Continue next -> begin break_complete (start +! mk_usize 1) finish inv next f p post;
    assert (post (Folds.fold_range_cf start finish inv value f)) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_cf";
      Tactics.smt_sync' 1 1
    ) end end
  else
    begin Nickel.LoopUtil.break_end start finish inv value f;
    assert (post (Folds.fold_range_cf start finish inv value f)) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_cf";
      Tactics.smt_sync' 1 1
    ) end

let leaf_completes (xs: t_Slice Native.t_BirthId) (base: nat) (finish: nat) (root: nat) : Lemma (requires (root >= finish / 2 /\ heap_except xs base finish root)) (ensures heap_from xs base finish) =
  ()

let actual_sift_limit () : Lemma (ensures v (((Rust_primitives.Integers.cast Core_models.Num.impl_usize__BITS) <: usize)) == Rust_primitives.Integers.size_bits) =
  ()

let exhausted_sift_completes (before: t_Slice Native.t_BirthId) (base: nat) (finish: nat) (state: P.sift_state) : Lemma (requires (finish <= Seq.length before /\ sift_invariant before base finish Rust_primitives.Integers.size_bits state)) (ensures sift_post before base finish state) =
  assert (v state._1 >= finish / 2) by (
    Tactics.prune "Nickel.EditDeleteHeap.heap_except";
    Tactics.prune "Nickel.EditDeleteHeap.segment_reordering";
    Tactics.smt_sync' 1 1
  );
  leaf_completes (Alloc.Vec.impl_1__as_slice state._2) base finish (v state._1);
  ()

let chosen_child (values: births) (left: usize{v left < Seq.length (Alloc.Vec.impl_1__as_slice values)}) (finish: usize) : usize =
  if Rust_primitives.Integers.lt (left +! mk_usize 1) finish && Rust_primitives.Integers.lt (left +! mk_usize 1) (Alloc.Vec.impl_1__len values) && Native.birth_lt (Core_models.Ops.Index.f_index values left) (Core_models.Ops.Index.f_index values (left +! mk_usize 1)) then
    begin left +! mk_usize 1 end
  else
    begin left end

let chosen_is_largest (values: births) (root: usize) (finish: usize) : Lemma (requires Prims.l_and (v root < v finish / 2) (v finish <= Seq.length (Alloc.Vec.impl_1__as_slice values))) (ensures largest_child (Alloc.Vec.impl_1__as_slice values) (v root) (v (chosen_child values (root *! mk_usize 2 +! mk_usize 1) finish)) (v finish)) =
  let left = root *! mk_usize 2 +! mk_usize 1 in
  order_total (Core_models.Ops.Index.f_index values left) (Core_models.Ops.Index.f_index values left);
  if v left + 1 < v finish then
    begin order_total (Core_models.Ops.Index.f_index values left) (Core_models.Ops.Index.f_index values (left +! mk_usize 1));
    () end
  else
    begin () end

let sift_step (finish: usize) (current: P.sift_state) (at: usize) : Flow.t_ControlFlow (unit & P.sift_state) P.sift_state =
  let root = (current._1 <: usize) in
  let values = (current._2 <: births) in
  if Rust_primitives.Integers.gte root (finish /! mk_usize 2) then
    begin Flow.ControlFlow_Break ((), current) end
  else
    begin let left = ((root *! mk_usize 2 +! mk_usize 1) <: usize) in
    if Rust_primitives.Integers.gte root (Alloc.Vec.impl_1__len values) || Rust_primitives.Integers.gte left (Alloc.Vec.impl_1__len values) then
      begin Flow.ControlFlow_Break ((), current) end
    else
      begin let child = ((if Rust_primitives.Integers.lt (left +! mk_usize 1) finish && Rust_primitives.Integers.lt (left +! mk_usize 1) (Alloc.Vec.impl_1__len values) && Native.birth_lt (Rust_primitives.Notations.op_String_Access values left) (Rust_primitives.Notations.op_String_Access values (left +! mk_usize 1)) then
        begin left +! mk_usize 1 end
      else
        begin left end) <: usize) in
      if Rust_primitives.Integers.gte child (Alloc.Vec.impl_1__len values) || Rust_primitives.Integers.op_Tilde_Dot (Native.birth_lt (Rust_primitives.Notations.op_String_Access values root) (Rust_primitives.Notations.op_String_Access values child)) then
        begin Flow.ControlFlow_Break ((), current) end
      else
        begin let old = ((Rust_primitives.Notations.op_String_Access values root) <: Native.t_BirthId) in
        let one = ((Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (Alloc.Vec.impl_1__as_slice values) root (((Rust_primitives.Notations.op_String_Access values child) <: Native.t_BirthId)))) <: births) in
        let swapped = ((Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (Alloc.Vec.impl_1__as_slice one) child old)) <: births) in
        Flow.ControlFlow_Continue (child, swapped) end end end

let sift_step_correct (before: t_Slice Native.t_BirthId) (base: nat) (finish: usize) (current: P.sift_state) (at: usize) : Lemma (requires (v finish <= Seq.length before /\ sift_invariant before base (v finish) (v at) current)) (ensures break_step_keeps (sift_invariant before base (v finish)) (sift_post before base (v finish)) (v at) (sift_step finish current at)) =
  let root = current._1 in
  let values = current._2 in
  if v root >= v finish / 2 then
    begin leaf_completes (Alloc.Vec.impl_1__as_slice values) base (v finish) (v root);
    () end
  else
    begin let left = root *! mk_usize 2 +! mk_usize 1 in
    let child = chosen_child values left finish in
    chosen_is_largest values root finish;
    if Native.birth_lt (Core_models.Ops.Index.f_index values root) (Core_models.Ops.Index.f_index values child) then
      begin order_total (Core_models.Ops.Index.f_index values root) (Core_models.Ops.Index.f_index values child);
      swap_repairs_hole values base (v finish) root child;
      segment_reordering_transitive before (Alloc.Vec.impl_1__as_slice values) (Alloc.Vec.impl_1__as_slice (P.exchange values root child)) base (v finish);
      Math.pow2_double_sum (v at);
      assert (sift_step finish current at == Flow.ControlFlow_Continue (child, P.exchange values root child)) by (
        Tactics.prune "Nickel.EditDeleteHeap.heap_except";
        Tactics.prune "Nickel.EditDeleteHeap.segment_reordering";
        Tactics.smt_sync' 1 1
      );
      assert (sift_invariant before base (v finish) (v at + 1) (child, P.exchange values root child)) by (
        Tactics.prune "Nickel.EditDeletePermutation.exchange";
        Tactics.prune "Nickel.EditDeleteHeap.sift_step";
        Tactics.smt_sync' 1 1
      );
      assert (break_step_keeps (sift_invariant before base (v finish)) (sift_post before base (v finish)) (v at) (sift_step finish current at)) by (
        Tactics.prune "Nickel.EditDeletePermutation.exchange";
        Tactics.prune "Nickel.EditDeleteHeap.sift_step";
        Tactics.smt_sync' 1 1
      ) end
    else
      begin fitting_root_completes (Alloc.Vec.impl_1__as_slice values) base (v finish) (v root) (v child);
      () end end

let sift_callbacks_complete (before: t_Slice Native.t_BirthId) (base: nat) (finish: usize) : Lemma (requires v finish <= Seq.length before) (ensures forall(inv: Nickel.LoopUtil.total_invariant P.sift_state (mk_usize 0) ((Rust_primitives.Integers.cast Core_models.Num.impl_usize__BITS) <: usize)) (initial: P.sift_state) (f: Nickel.LoopUtil.break_callback P.sift_state (mk_usize 0) ((Rust_primitives.Integers.cast Core_models.Num.impl_usize__BITS) <: usize)). Prims.l_and (sift_invariant before base (v finish) 0 initial) (forall(current: P.sift_state) (at: Nickel.LoopUtil.position (mk_usize 0) ((Rust_primitives.Integers.cast Core_models.Num.impl_usize__BITS) <: usize)). f current at == sift_step finish current at) ==> Prims.l_and (heap_from (Alloc.Vec.impl_1__as_slice (Folds.fold_range_cf (mk_usize 0) (((Rust_primitives.Integers.cast Core_models.Num.impl_usize__BITS) <: usize)) inv initial f)._2) base (v finish)) (segment_reordering before (Alloc.Vec.impl_1__as_slice (Folds.fold_range_cf (mk_usize 0) (((Rust_primitives.Integers.cast Core_models.Num.impl_usize__BITS) <: usize)) inv initial f)._2) base (v finish))) =
  let limit = ((Rust_primitives.Integers.cast Core_models.Num.impl_usize__BITS) <: usize) in
  let each (inv: Nickel.LoopUtil.total_invariant P.sift_state (mk_usize 0) limit) (initial: P.sift_state) (f: Nickel.LoopUtil.break_callback P.sift_state (mk_usize 0) limit) : Lemma (requires (sift_invariant before base (v finish) 0 initial /\ (forall(current: P.sift_state) (at: Nickel.LoopUtil.position (mk_usize 0) limit). f current at == sift_step finish current at))) (ensures sift_post before base (v finish) (Folds.fold_range_cf (mk_usize 0) limit inv initial f)) =
    actual_sift_limit ();
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (sift_step_correct before base finish));
    FStar.Classical.forall_intro (FStar.Classical.move_requires (exhausted_sift_completes before base (v finish)));
    break_complete (mk_usize 0) limit inv initial f (sift_invariant before base (v finish)) (sift_post before base (v finish));
    () in
  FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 each);
  ()

let initial_sift_state (values: births) (start: usize) (finish: usize) : Lemma (requires (v finish <= Seq.length (Alloc.Vec.impl_1__as_slice values) /\ heap_from (Alloc.Vec.impl_1__as_slice values) (v start + 1) (v finish))) (ensures sift_invariant (Alloc.Vec.impl_1__as_slice values) (v start) (v finish) 0 (start, values)) =
  ()

let rec break_pointwise (#state: Type0) (start: usize) (finish: usize{v start <= v finish}) (left_inv: Nickel.LoopUtil.total_invariant state start finish) (right_inv: Nickel.LoopUtil.total_invariant state start finish) (value: state) (left: Nickel.LoopUtil.break_callback state start finish) (right: Nickel.LoopUtil.break_callback state start finish) : Lemma (requires forall(s: state) (at: Nickel.LoopUtil.position start finish). left s at == right s at) (ensures Folds.fold_range_cf start finish left_inv value left == Folds.fold_range_cf start finish right_inv value right) (decreases v finish - v start) =
  if v start < v finish then
    begin Nickel.LoopUtil.break_step start finish left_inv value left;
    Nickel.LoopUtil.break_step start finish right_inv value right;
    match left value start with | Flow.ControlFlow_Break (_, next) -> begin assert (Folds.fold_range_cf start finish left_inv value left == Folds.fold_range_cf start finish right_inv value right) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_cf";
      Tactics.smt_sync' 1 1
    ) end | Flow.ControlFlow_Continue next -> begin break_pointwise (start +! mk_usize 1) finish left_inv right_inv next left right;
    assert (Folds.fold_range_cf start finish left_inv value left == Folds.fold_range_cf start finish right_inv value right) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_cf";
      Tactics.smt_sync' 1 1
    ) end end
  else
    begin Nickel.LoopUtil.break_end start finish left_inv value left;
    Nickel.LoopUtil.break_end start finish right_inv value right;
    () end

let break_pointwise_any (#state: Type0) (start: usize) (finish: usize{v start <= v finish}) (value: state) : Lemma (ensures forall(left_inv: Nickel.LoopUtil.total_invariant state start finish) (right_inv: Nickel.LoopUtil.total_invariant state start finish) (left: Nickel.LoopUtil.break_callback state start finish) (right: Nickel.LoopUtil.break_callback state start finish). (forall(s: state) (at: Nickel.LoopUtil.position start finish). left s at == right s at) ==> Folds.fold_range_cf start finish left_inv value left == Folds.fold_range_cf start finish right_inv value right) =
  let annotations (left_inv: Nickel.LoopUtil.total_invariant state start finish) (right_inv: Nickel.LoopUtil.total_invariant state start finish) : Lemma (ensures forall(left: Nickel.LoopUtil.break_callback state start finish) (right: Nickel.LoopUtil.break_callback state start finish). (forall(s: state) (at: Nickel.LoopUtil.position start finish). left s at == right s at) ==> Folds.fold_range_cf start finish left_inv value left == Folds.fold_range_cf start finish right_inv value right) =
    let each (left: Nickel.LoopUtil.break_callback state start finish) (right: Nickel.LoopUtil.break_callback state start finish) : Lemma (requires forall(s: state) (at: Nickel.LoopUtil.position start finish). left s at == right s at) (ensures Folds.fold_range_cf start finish left_inv value left == Folds.fold_range_cf start finish right_inv value right) = break_pointwise start finish left_inv right_inv value left right in
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each);
    () in
  FStar.Classical.forall_intro_2 annotations;
  ()

let sift_model (values: births) (start: usize) (finish: usize) : P.sift_state =
  let limit = ((Rust_primitives.Integers.cast Core_models.Num.impl_usize__BITS) <: usize) in
  Folds.fold_range_cf (mk_usize 0) limit (fun (_: P.sift_state) (_: Nickel.LoopUtil.inv_position (mk_usize 0) limit) -> Prims.l_True) (start, values) (fun (current: P.sift_state) (at: Nickel.LoopUtil.position (mk_usize 0) limit) -> sift_step finish current at)

let sift_is_model (values: births) (start: usize) (finish: usize) : Lemma (ensures Native.sift_births values start finish == (sift_model values start finish)._2) =
  break_pointwise_any (mk_usize 0) (((Rust_primitives.Integers.cast Core_models.Num.impl_usize__BITS) <: usize)) (start, values);
  assert (Native.sift_births values start finish == (sift_model values start finish)._2) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_cf";
    Tactics.smt_sync' 1 1
  )

let sift_restores_heap (values: births) (start: usize) (finish: usize) : Lemma (requires (v finish <= Seq.length (Alloc.Vec.impl_1__as_slice values) /\ heap_from (Alloc.Vec.impl_1__as_slice values) (v start + 1) (v finish))) (ensures Prims.l_and (heap_from (Alloc.Vec.impl_1__as_slice (Native.sift_births values start finish)) (v start) (v finish)) (segment_reordering (Alloc.Vec.impl_1__as_slice values) (Alloc.Vec.impl_1__as_slice (Native.sift_births values start finish)) (v start) (v finish))) [SMTPat (Native.sift_births values start finish)] =
  initial_sift_state values start finish;
  sift_callbacks_complete (Alloc.Vec.impl_1__as_slice values) (v start) finish;
  assert (sift_post (Alloc.Vec.impl_1__as_slice values) (v start) (v finish) (sift_model values start finish)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_cf";
    Tactics.smt_sync' 1 1
  );
  sift_is_model values start finish;
  assert (Prims.l_and (heap_from (Alloc.Vec.impl_1__as_slice (Native.sift_births values start finish)) (v start) (v finish)) (segment_reordering (Alloc.Vec.impl_1__as_slice values) (Alloc.Vec.impl_1__as_slice (Native.sift_births values start finish)) (v start) (v finish))) by (
    Tactics.prune "Nickel_crdt.Edit.sift_births";
    Tactics.prune "Nickel.EditDeleteHeap.sift_model";
    Tactics.prune "Nickel.EditDeleteHeap.heap_from";
    Tactics.prune "Nickel.EditDeleteHeap.segment_reordering";
    Tactics.smt_sync' 1 1
  )

let leaf_suffix (xs: t_Slice Native.t_BirthId) (base: nat) (finish: nat) : Lemma (requires base >= finish / 2) (ensures heap_from xs base finish) =
  ()

let build_invariant (len: usize) (at: nat) (current: births) : Type0 =
  Prims.l_and (Prims.l_and (at <= v len / 2) (Seq.length (Alloc.Vec.impl_1__as_slice current) == v len)) (heap_from (Alloc.Vec.impl_1__as_slice current) (v len / 2 - at) (v len))

let built_heap (len: usize) (current: births) : Type0 =
  Prims.l_and (Seq.length (Alloc.Vec.impl_1__as_slice current) == v len) (heap_from (Alloc.Vec.impl_1__as_slice current) 0 (v len))

let heap_builds (values: births) (len: usize) : Lemma (requires v len == Seq.length (Alloc.Vec.impl_1__as_slice values)) (ensures built_heap len (Native.heap_births values len)) [SMTPat (Native.heap_births values len)] =
  leaf_suffix (Alloc.Vec.impl_1__as_slice values) (v len / 2) (v len);
  Nickel.LoopUtil.plain_preserve_any (mk_usize 0) (len /! mk_usize 2) (build_invariant len) (built_heap len);
  assert (built_heap len (Native.heap_births values len)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range";
    Tactics.prune "Nickel_crdt.Edit.sift_births";
    Tactics.smt_sync' 1 1
  )

let rec root_dominates (xs: t_Slice Native.t_BirthId) (finish: nat) (at: nat) : Lemma (requires (Prims.l_and (at < finish) (finish <= Seq.length xs) /\ heap_from xs 0 finish)) (ensures le (Seq.index xs at) (Seq.index xs 0)) (decreases at) =
  if at > 0 then
    begin let parent = (at - 1) / 2 in
    root_dominates xs finish parent;
    order_transitive (Seq.index xs at) (Seq.index xs parent) (Seq.index xs 0);
    () end
  else
    begin order_total (Seq.index xs 0) (Seq.index xs 0);
    () end

let tail_ordered (xs: t_Slice Native.t_BirthId) (start: nat) : Type0 =
  forall(i: nat) (j: nat). Prims.l_and (Prims.l_and (start <= i) (i < j)) (j < Seq.length xs) ==> le (Seq.index xs i) (Seq.index xs j)

let below_tail (xs: t_Slice Native.t_BirthId) (start: nat) : Type0 =
  forall(i: nat) (j: nat). Prims.l_and (Prims.l_and (i < start) (start <= j)) (j < Seq.length xs) ==> le (Seq.index xs i) (Seq.index xs j)

let drain_invariant (len: usize) (at: nat) (current: births) : Type0 =
  Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (at <= v len) (Seq.length (Alloc.Vec.impl_1__as_slice current) == v len)) (heap_from (Alloc.Vec.impl_1__as_slice current) 0 (v len - at))) (tail_ordered (Alloc.Vec.impl_1__as_slice current) (v len - at))) (below_tail (Alloc.Vec.impl_1__as_slice current) (v len - at))

let sorted (xs: t_Slice Native.t_BirthId) : Type0 =
  tail_ordered xs 0

let drain_swap (values: births) (len: usize) (step: Nickel.LoopUtil.position (mk_usize 0) len) : Lemma (requires drain_invariant len (v step) values) (ensures Prims.l_and (Prims.l_and (Prims.l_and (heap_from (Alloc.Vec.impl_1__as_slice (P.exchange values (mk_usize 0) (len -! mk_usize 1 -! step))) 1 (v len - 1 - v step)) (tail_ordered (Alloc.Vec.impl_1__as_slice (P.exchange values (mk_usize 0) (len -! mk_usize 1 -! step))) (v len - 1 - v step))) (below_tail (Alloc.Vec.impl_1__as_slice (P.exchange values (mk_usize 0) (len -! mk_usize 1 -! step))) (v len - 1 - v step))) (Seq.length (Alloc.Vec.impl_1__as_slice (P.exchange values (mk_usize 0) (len -! mk_usize 1 -! step))) == v len)) =
  let before = Alloc.Vec.impl_1__as_slice values in
  let finish = len -! mk_usize 1 -! step in
  exchange_entries values (mk_usize 0) finish;
  let each (i: nat{i < v len - v step}) : Lemma (ensures le (Seq.index before i) (Seq.index before 0)) = root_dominates before (v len - v step) i in
  FStar.Classical.forall_intro each;
  ()

let reordering_keeps_tail (before: t_Slice Native.t_BirthId) (after: t_Slice Native.t_BirthId) (finish: nat) : Lemma (requires (segment_reordering before after 0 finish /\ Prims.l_and (tail_ordered before finish) (below_tail before finish))) (ensures Prims.l_and (tail_ordered after finish) (below_tail after finish)) =
  ()

let sorted_births (len: usize) (values: births) : Type0 =
  Prims.l_and (Seq.length (Alloc.Vec.impl_1__as_slice values) == v len) (sorted (Alloc.Vec.impl_1__as_slice values))

let drain_step_orders (len: usize) (current: births) (at: Nickel.LoopUtil.position (mk_usize 0) len) : Lemma (requires drain_invariant len (v at) current) (ensures break_step_keeps (drain_invariant len) (sorted_births len) (v at) (P.drain_step len current at)) =
  let finish = len -! mk_usize 1 -! at in
  let swapped = P.exchange current (mk_usize 0) finish in
  drain_swap current len at;
  sift_restores_heap swapped (mk_usize 0) finish;
  reordering_keeps_tail (Alloc.Vec.impl_1__as_slice swapped) (Alloc.Vec.impl_1__as_slice (Native.sift_births swapped (mk_usize 0) finish)) (v finish);
  assert (P.drain_step len current at == Flow.ControlFlow_Continue (Native.sift_births swapped (mk_usize 0) finish)) by (
    Tactics.prune "Nickel_crdt.Edit.sift_births";
    Tactics.smt_sync' 1 1
  );
  assert (break_step_keeps (drain_invariant len) (sorted_births len) (v at) (P.drain_step len current at)) by (
    Tactics.prune "Nickel_crdt.Edit.sift_births";
    Tactics.prune "Nickel.EditDeletePermutation.exchange";
    Tactics.prune "Nickel.EditDeletePermutation.drain_step";
    Tactics.smt_sync' 1 1
  )

let drain_callbacks_complete (len: usize) : Lemma (ensures forall(inv: Nickel.LoopUtil.total_invariant births (mk_usize 0) len) (initial: births) (f: Nickel.LoopUtil.break_callback births (mk_usize 0) len). Prims.l_and (drain_invariant len 0 initial) (forall(current: births) (at: Nickel.LoopUtil.position (mk_usize 0) len). f current at == P.drain_step len current at) ==> sorted_births len (Folds.fold_range_cf (mk_usize 0) len inv initial f)) =
  let each (inv: Nickel.LoopUtil.total_invariant births (mk_usize 0) len) (initial: births) (f: Nickel.LoopUtil.break_callback births (mk_usize 0) len) : Lemma (requires (drain_invariant len 0 initial /\ (forall(current: births) (at: Nickel.LoopUtil.position (mk_usize 0) len). f current at == P.drain_step len current at))) (ensures sorted_births len (Folds.fold_range_cf (mk_usize 0) len inv initial f)) =
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (drain_step_orders len));
    break_complete (mk_usize 0) len inv initial f (drain_invariant len) (sorted_births len);
    () in
  FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 each);
  ()

let drain_model (values: births) (len: usize) : births =
  Folds.fold_range_cf (mk_usize 0) len (fun (_: births) (_: Nickel.LoopUtil.inv_position (mk_usize 0) len) -> Prims.l_True) values (fun (current: births) (at: Nickel.LoopUtil.position (mk_usize 0) len) -> P.drain_step len current at)

let drain_is_model (values: births) (len: usize) : Lemma (ensures Native.drain_births values len == drain_model values len) =
  break_pointwise_any (mk_usize 0) len values;
  assert (Native.drain_births values len == drain_model values len) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_cf";
    Tactics.prune "Nickel_crdt.Edit.sift_births";
    Tactics.smt_sync' 1 1
  )

let drain_sorts (values: births) (len: usize) : Lemma (requires built_heap len values) (ensures sorted_births len (Native.drain_births values len)) [SMTPat (Native.drain_births values len)] =
  assert (drain_invariant len 0 values);
  drain_callbacks_complete len;
  assert (sorted_births len (drain_model values len)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_cf";
    Tactics.smt_sync' 1 1
  );
  drain_is_model values len;
  assert (sorted_births len (Native.drain_births values len)) by (
    Tactics.prune "Nickel_crdt.Edit.drain_births";
    Tactics.prune "Nickel.EditDeleteHeap.drain_model";
    Tactics.smt_sync' 1 1
  )

let ordered_births_sorted (xs: t_Slice Native.t_BirthId) : Lemma (ensures sorted (Alloc.Vec.impl_1__as_slice (Native.ordered_births xs))) [SMTPat (Native.ordered_births xs)] =
  let copied = Alloc.Slice.impl__to_vec xs in
  let len = Alloc.Vec.impl_1__len copied in
  heap_builds copied len;
  assert (built_heap len (Native.heap_births copied len)) by (
    Tactics.prune "Nickel_crdt.Edit.heap_births";
    Tactics.smt_sync' 1 1
  );
  drain_sorts (Native.heap_births copied len) len;
  assert (sorted (Alloc.Vec.impl_1__as_slice (Native.ordered_births xs))) by (
    Tactics.prune "Nickel_crdt.Edit.heap_births";
    Tactics.prune "Nickel_crdt.Edit.drain_births";
    Tactics.smt_sync' 1 1
  )