(* Latte generated F* view *)
module Nickel.EditDeleteAnswer

open Nickel.Prelude

open Rust_primitives

open Core_models

open Nickel.Vector

open Nickel.LoopUtil

open Nickel.EditDeletePermutation

open FStar.Pervasives

open FStar.Classical

module Seq = FStar.Seq

module Props = FStar.Seq.Properties

module Native = Nickel_crdt.Edit

module Flow = Core_models.Ops.Control_flow

module Result = Core_models.Result

module Option = Core_models.Option

module Tactics = FStar.Tactics.V2

let repeated (xs: t_Slice Native.t_BirthId) : Type0 =
  exists(i: nat) (j: nat). Prims.l_and (Prims.l_and (i < j) (j < Seq.length xs)) (Seq.index xs i == Seq.index xs j)

let rec index_has_count (xs: t_Slice Native.t_BirthId) (i: nat) : Lemma (requires i < Seq.length xs) (ensures Seq.count (Seq.index xs i) xs >= 1) (decreases Seq.length xs) =
  if i > 0 then
    begin index_has_count (Seq.slice xs 1 (Seq.length xs)) (i - 1);
    () end
  else
    begin () end

let rec equal_positions_count (xs: t_Slice Native.t_BirthId) (i: nat) (j: nat) : Lemma (requires (Prims.l_and (i < j) (j < Seq.length xs) /\ Seq.index xs i == Seq.index xs j)) (ensures Seq.count (Seq.index xs i) xs >= 2) (decreases Seq.length xs) =
  if i < 1 then
    begin let tail = Seq.slice xs 1 (Seq.length xs) in
    index_has_count tail (j - 1);
    () end
  else
    begin equal_positions_count (Seq.slice xs 1 (Seq.length xs)) (i - 1) (j - 1);
    () end

let rec count_has_equal_positions (xs: t_Slice Native.t_BirthId) (id: Native.t_BirthId) : Lemma (requires Seq.count id xs >= 2) (ensures repeated xs) (decreases Seq.length xs) =
  let tail = Seq.slice xs 1 (Seq.length xs) in
  if Seq.index xs 0 ==? id then
    begin let at = Props.index_mem id tail in
    assert (Prims.l_and (Prims.l_and (0 < at + 1) (at + 1 < Seq.length xs)) (Seq.index xs 0 == Seq.index xs (at + 1)));
    () end
  else
    begin count_has_equal_positions tail id;
    assert (repeated xs);
    () end

let same_births_transports_pair (before: t_Slice Native.t_BirthId) (after: t_Slice Native.t_BirthId) : Lemma (ensures Prims.l_and (Nickel.EditDeletePermutation.same_births before after) (repeated after) ==> repeated before) =
  let each (i: nat) (j: nat) : Lemma (requires (Nickel.EditDeletePermutation.same_births before after /\ Prims.l_and (Prims.l_and (i < j) (j < Seq.length after)) (Seq.index after i == Seq.index after j))) (ensures repeated before) =
    equal_positions_count after i j;
    assert (Seq.count (Seq.index after i) before >= 2) by (
      Tactics.prune "FStar.Seq.count";
      Tactics.prune "FStar.Seq.Properties.count";
      Tactics.smt_sync' 1 1
    );
    count_has_equal_positions before (Seq.index after i);
    assert (repeated before) by (
      Tactics.prune "FStar.Seq.count";
      Tactics.prune "FStar.Seq.Properties.count";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each);
  ()

let duplicate_answer_has_original_pair (xs: t_Slice Native.t_BirthId) : Lemma (ensures Native.duplicate_births xs == true ==> repeated xs) [SMTPat (Native.duplicate_births xs)] =
  if Seq.length xs >= 2 then
    begin let ordered = Native.ordered_births xs in
    Nickel.EditDeletePermutation.ordered_preserves_births xs;
    same_births_transports_pair xs (Alloc.Vec.impl_1__as_slice ordered);
    Nickel.LoopUtil.preserve_any (mk_usize 1) (Alloc.Vec.impl_1__len ordered) (fun (_: nat) (_: unit) -> Prims.l_True) (fun (_: unit) -> Prims.l_True) (fun (answer: bool) -> answer == true ==> repeated (Alloc.Vec.impl_1__as_slice ordered));
    assert (Native.duplicate_births xs == true ==> repeated xs) by (
      Tactics.prune "Nickel_crdt.Edit.ordered_births";
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.smt_sync' 1 1
    ) end
  else
    begin () end

let distinct_delete_keeps_placement_error (facts: t_Slice Native.t_Fact) (fact: Native.t_Fact) : Lemma (requires (Native.validate_scalars (Alloc.Vec.impl_1__as_slice fact.f_insert) == Result.Result_Ok () /\ Prims.l_not (repeated (Alloc.Vec.impl_1__as_slice fact.f_delete)) /\ Alloc.Vec.impl_1__is_empty fact.f_insert == true /\ Core_models.Option.impl__is_some fact.f_gap == true)) (ensures Native.impl_Replica__validate_new facts fact == Result.Result_Err (Native.Error_Invalid Native.Invalid_PlacementWithoutBirth)) =
  duplicate_answer_has_original_pair (Alloc.Vec.impl_1__as_slice fact.f_delete);
  assert (Native.impl_Replica__validate_new facts fact == Result.Result_Err (Native.Error_Invalid Native.Invalid_PlacementWithoutBirth)) by (
    Tactics.prune "Nickel_crdt.Edit.duplicate_births";
    Tactics.smt_sync' 1 1
  )