(* Latte generated F* view *)
module Nickel.EditDeleteComplete

open Nickel.Prelude

open Rust_primitives

open Core_models

open Nickel.Vector

open Nickel.LoopUtil

open Nickel.EditDeleteHeap

open Nickel.EditDeleteAnswer

open Nickel.EditDeletePermutation

open FStar.Pervasives

open FStar.Classical

module Seq = FStar.Seq

module Native = Nickel_crdt.Edit

module H = Nickel.EditDeleteHeap

module A = Nickel.EditDeleteAnswer

module P = Nickel.EditDeletePermutation

module Result = Core_models.Result

module Tactics = FStar.Tactics.V2

let adjacent_free_before (xs: t_Slice Native.t_BirthId) (finish: nat) : Type0 =
  forall(i: usize{Prims.l_and (0 < v i) (v i < Seq.length xs)}). v i < finish ==> Seq.index xs (v i - 1) <> Seq.index xs (v i)

let sorted_adjacent_free_disallows_pair (xs: t_Slice Native.t_BirthId) : Lemma (ensures Prims.l_and (H.sorted xs) (adjacent_free_before xs (Seq.length xs)) ==> Prims.l_not (A.repeated xs)) =
  let each (i: nat) (j: nat) : Lemma (requires (Prims.l_and (H.sorted xs) (adjacent_free_before xs (Seq.length xs)) /\ Prims.l_and (Prims.l_and (i < j) (j < Seq.length xs)) (Seq.index xs i == Seq.index xs j))) (ensures Prims.l_False) =
    let next = mk_usize (i + 1) in
    H.order_antisymmetric (Seq.index xs i) (Seq.index xs (i + 1));
    assert (Seq.index xs i == Seq.index xs (v next)) by (
      Tactics.prune "Nickel_crdt.Edit.birth_lt";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each);
  ()

let duplicate_births_complete (xs: t_Slice Native.t_BirthId) : Lemma (ensures A.repeated xs ==> Native.duplicate_births xs == true) [SMTPat (Native.duplicate_births xs)] =
  if Seq.length xs >= 2 then
    begin let ordered = Native.ordered_births xs in
    let after = Alloc.Vec.impl_1__as_slice ordered in
    P.ordered_preserves_births xs;
    assert (P.same_births after xs) by (
      Tactics.prune "Nickel_crdt.Edit.ordered_births";
      Tactics.prune "FStar.Seq.count";
      Tactics.prune "FStar.Seq.Properties.count";
      Tactics.smt_sync' 1 1
    );
    A.same_births_transports_pair after xs;
    H.ordered_births_sorted xs;
    sorted_adjacent_free_disallows_pair after;
    Nickel.LoopUtil.preserve_any (mk_usize 1) (Alloc.Vec.impl_1__len ordered) (fun (at: nat) (_: unit) -> adjacent_free_before after at) (fun (_: unit) -> adjacent_free_before after (Seq.length after)) (fun (answer: bool) -> answer == true);
    assert (A.repeated xs ==> Native.duplicate_births xs == true) by (
      Tactics.prune "Nickel_crdt.Edit.ordered_births";
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.smt_sync' 1 1
    ) end
  else
    begin () end

let duplicate_births_exact (xs: t_Slice Native.t_BirthId) : Lemma (ensures Native.duplicate_births xs == true <==> A.repeated xs) =
  A.duplicate_answer_has_original_pair xs;
  duplicate_births_complete xs;
  assert (Native.duplicate_births xs == true <==> A.repeated xs) by (
    Tactics.prune "Nickel_crdt.Edit.duplicate_births";
    Tactics.smt_sync' 1 1
  )

let repeated_delete_rejected_before_admission (facts: t_Slice Native.t_Fact) (fact: Native.t_Fact) : Lemma (requires (Native.validate_scalars (Alloc.Vec.impl_1__as_slice fact.f_insert) == Result.Result_Ok () /\ A.repeated (Alloc.Vec.impl_1__as_slice fact.f_delete))) (ensures Native.impl_Replica__validate_new facts fact == Result.Result_Err (Native.Error_Invalid Native.Invalid_DeleteDuplicate)) =
  duplicate_births_complete (Alloc.Vec.impl_1__as_slice fact.f_delete);
  assert (Native.impl_Replica__validate_new facts fact == Result.Result_Err (Native.Error_Invalid Native.Invalid_DeleteDuplicate)) by (
    Tactics.prune "Nickel_crdt.Edit.duplicate_births";
    Tactics.smt_sync' 1 1
  )