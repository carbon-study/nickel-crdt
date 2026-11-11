(* Latte generated F* view *)
module Nickel.CausalEnvelope

open Nickel.Prelude

open Rust_primitives

open Core_models

open FStar.Pervasives

open Nickel.LoopUtil

module Native = Nickel_crdt.Causal

module Option = Core_models.Option

module Seq = FStar.Seq

module Tactics = FStar.Tactics.V2

let same_id (a: Native.t_Id) (b: Native.t_Id) : Type0 =
  Prims.l_and (a.f_peer == b.f_peer) (a.f_counter == b.f_counter)

let absent (#p: Type0) {| i0 : Core_models.Clone.t_Clone p |} (facts: t_Slice (Native.t_Event p)) (id: Native.t_Id) (at: nat) : Type0 =
  forall(j: nat). Prims.l_and (j < at) (j < Seq.length facts) ==> Prims.l_not (same_id (Seq.index facts j).f_id id)

let classified (#p: Type0) {| i0 : Core_models.Clone.t_Clone p |} (facts: t_Slice (Native.t_Event p)) (fact: Native.t_Event p) (eq: p -> p -> bool) (r: Option.t_Option bool) : Type0 =
  match r with | Option.Option_Some b -> begin exists(i: nat). Prims.l_and (Prims.l_and (Prims.l_and (i < Seq.length facts) (absent facts fact.f_id i)) (same_id (Seq.index facts i).f_id fact.f_id)) (b == Native.event_equal #p (Seq.index facts i) fact eq) end | Option.Option_None -> begin absent facts fact.f_id (Seq.length facts) end

let id_equal_exact (a: Native.t_Id) (b: Native.t_Id) : Lemma (ensures Native.impl.f_eq a b == true <==> same_id a b) =
  ()

let classify_first_match (#p: Type0) {| i0 : Core_models.Clone.t_Clone p |} (facts: t_Slice (Native.t_Event p)) (fact: Native.t_Event p) (eq: p -> p -> bool) : Lemma (ensures classified facts fact eq (Native.classify #p facts fact eq)) =
  Nickel.LoopUtil.preserve_any #unit #(Option.t_Option bool) (mk_usize 0) (Core_models.Slice.impl__len #(Native.t_Event p) facts) (fun (at: nat) (_: unit) -> absent facts fact.f_id at) (fun (_: unit) -> absent facts fact.f_id (Seq.length facts)) (fun (r: Option.t_Option bool) -> classified facts fact eq r);
  assert (classified facts fact eq (Native.classify #p facts fact eq)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel_crdt.Causal.event_equal";
    Tactics.smt_sync' 1 1
  )

let ids_prefix (a: t_Slice Native.t_Id) (b: t_Slice Native.t_Id) (at: nat) : Type0 =
  forall(j: nat). Prims.l_and (Prims.l_and (j < at) (j < Seq.length a)) (j < Seq.length b) ==> same_id (Seq.index a j) (Seq.index b j)

let ids_equal (a: t_Slice Native.t_Id) (b: t_Slice Native.t_Id) : Type0 =
  Prims.l_and (Seq.length a == Seq.length b) (ids_prefix a b (Seq.length a))

let ids_eq_exact (a: t_Slice Native.t_Id) (b: t_Slice Native.t_Id) : Lemma (ensures Prims.l_and (Native.ids_eq a b == true <==> ids_equal a b) (Native.ids_eq a b == false <==> Prims.l_not (ids_equal a b))) [SMTPat (Native.ids_eq a b)] =
  if Seq.length a ==? Seq.length b then
    begin Nickel.LoopUtil.preserve_any #unit #bool (mk_usize 0) (Core_models.Slice.impl__len #Native.t_Id a) (fun (at: nat) (_: unit) -> ids_prefix a b at) (fun (_: unit) -> ids_equal a b) (fun (r: bool) -> Prims.l_and (r == false) (Prims.l_not (ids_equal a b)));
    assert (Native.ids_eq a b == true <==> ids_equal a b) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.smt_sync' 1 1
    ) end
  else
    begin () end

let event_equal_exact (#p: Type0) {| i0 : Core_models.Clone.t_Clone p |} (left: Native.t_Event p) (right: Native.t_Event p) (eq: p -> p -> bool) : Lemma (requires forall(a: p) (b: p). eq a b == true <==> a == b) (ensures Native.event_equal #p left right eq == true <==> Prims.l_and (Prims.l_and (same_id left.f_id right.f_id) (ids_equal (Alloc.Vec.impl_1__as_slice left.f_after) (Alloc.Vec.impl_1__as_slice right.f_after))) (left.f_payload == right.f_payload)) =
  ids_eq_exact (Alloc.Vec.impl_1__as_slice left.f_after) (Alloc.Vec.impl_1__as_slice right.f_after);
  assert (Native.event_equal #p left right eq == true <==> Prims.l_and (Prims.l_and (same_id left.f_id right.f_id) (ids_equal (Alloc.Vec.impl_1__as_slice left.f_after) (Alloc.Vec.impl_1__as_slice right.f_after))) (left.f_payload == right.f_payload)) by (
    Tactics.prune "Nickel_crdt.Causal.ids_eq";
    Tactics.smt_sync' 1 1
  )