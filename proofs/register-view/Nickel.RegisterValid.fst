(* Latte generated F* view *)
module Nickel.RegisterValid

open Nickel.Prelude

open Rust_primitives

open Core_models

open FStar.Pervasives

open Nickel.LoopUtil

module Native = Nickel_crdt.Register

module Envelope = Nickel_crdt.Causal

module Option = Core_models.Option

module Seq = FStar.Seq

module Tactics = FStar.Tactics.V2

open Nickel.EventShell

module Result = Core_models.Result

module Shell = Nickel_crdt.Event_shell

open Nickel.CausalEnvelope

open Nickel.Canonical

open Nickel.Register

open Nickel.RegisterPast

open Nickel.EventClassifier

open Nickel.RegisterHistory

let parents_clock_below (before: Native.t_Replica) (offered: Nickel.Register.fact) : Type0 =
  forall(fb: Nickel.Register.fact). Prims.l_and (stored (Alloc.Vec.impl_1__as_slice before.f_facts) fb) (Nickel.RegisterPast.member (Alloc.Vec.impl_1__as_slice offered.f_after) fb.f_id) ==> v fb.f_payload.f_lamport < v offered.f_payload.f_lamport

let basis_bounds_parent_clocks (before: Native.t_Replica) (offered: Nickel.Register.fact) (selected: Alloc.Vec.t_Vec Envelope.t_Id Alloc.Alloc.t_Global) (basis: Alloc.Vec.t_Vec Nickel.Register.fact Alloc.Alloc.t_Global) : Lemma (requires ((forall(id: Envelope.t_Id). Nickel.RegisterPast.member (Alloc.Vec.impl_1__as_slice selected) id <==> Nickel.RegisterPast.ancestor Native.v_OPS._1 (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice offered.f_after) id) /\ Nickel.RegisterPast.selected_prefix Native.v_OPS._1 (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice selected) (Seq.length (Alloc.Vec.impl_1__as_slice before.f_facts)) (Alloc.Vec.impl_1__as_slice basis) /\ Nickel.Register.clock_successor (Alloc.Vec.impl_1__as_slice basis) offered.f_payload.f_lamport)) (ensures parents_clock_below before offered) =
  let facts = Alloc.Vec.impl_1__as_slice before.f_facts in
  register_ops_are_exact ();
  filter_has_selected_facts Native.v_OPS._1 facts (Alloc.Vec.impl_1__as_slice selected) (Seq.length facts) (Alloc.Vec.impl_1__as_slice basis);
  let each (fb: Nickel.Register.fact) : Lemma (requires Prims.l_and (stored facts fb) (Nickel.RegisterPast.member (Alloc.Vec.impl_1__as_slice offered.f_after) fb.f_id)) (ensures v fb.f_payload.f_lamport < v offered.f_payload.f_lamport) =
    assert (Nickel.RegisterPast.causal_path Native.v_OPS._1 facts fb.f_id Prims.Nil fb.f_id);
    assert (Nickel.RegisterPast.ancestor Native.v_OPS._1 facts (Alloc.Vec.impl_1__as_slice offered.f_after) fb.f_id);
    assert (stored (Alloc.Vec.impl_1__as_slice basis) fb) in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each)

let frozen_basis_bounds_parents (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (requires exact_selected_basis before offered) (ensures parents_clock_below before offered) =
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (basis_bounds_parent_clocks before offered));
  assert (parents_clock_below before offered) by (
    Tactics.prune "Nickel_crdt.Event_layer.validate_event";
    Tactics.prune "Nickel_crdt.Event_layer.select_basis";
    Tactics.smt_sync' 1 1
  )

let ids_and_clocks_extend (h: Seq.seq Nickel.Register.fact) (h2: Seq.seq Nickel.Register.fact) (fnew: Nickel.Register.fact) : Lemma (requires (Prims.l_and (extends_by h h2 fnew) (unreferenced h2 fnew.f_id) /\ Prims.l_and (stored_unique h) (id_clocks_increase h) /\ (forall(g: Nickel.Register.fact). stored h g ==> g.f_id =!= fnew.f_id) /\ (forall(fb: Nickel.Register.fact). Prims.l_and (stored h fb) (Nickel.RegisterPast.member (Alloc.Vec.impl_1__as_slice fnew.f_after) fb.f_id) ==> v fb.f_payload.f_lamport < v fnew.f_payload.f_lamport))) (ensures Prims.l_and (stored_unique h2) (id_clocks_increase h2)) =
  ()

let invariant_kept (before: Native.t_Replica) (next: Native.t_Replica) : Type0 =
  observation_invariant before ==> observation_invariant next

let invariant_from_parts (before: Native.t_Replica) (offered: Nickel.Register.fact) (next: Native.t_Replica) : Lemma (requires (Prims.l_and (observations_kept_on before next) (history_extended_soundly before offered next) /\ Prims.l_and (Prims.l_and (Nickel.Register.appended_facts before offered next) (fresh_id before offered)) (parents_clock_below before offered))) (ensures invariant_kept before next) =
  let h = Alloc.Vec.impl_1__as_slice before.f_facts in
  let h2 = Alloc.Vec.impl_1__as_slice next.f_facts in
  assert (extends_by h h2 offered);
  FStar.Classical.move_requires (ids_and_clocks_extend h h2) offered

let receive_added_preserves_invariant (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (ensures forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> invariant_kept before next) =
  receive_added_keeps_observations before offered;
  receive_added_extends_soundly before offered;
  Nickel.Register.receive_added_retains_exact_facts before offered;
  receive_added_offer_is_fresh before offered;
  receive_added_basis_is_exact_ancestry before offered;
  FStar.Classical.move_requires (frozen_basis_bounds_parents before) offered;
  FStar.Classical.forall_intro (FStar.Classical.move_requires (invariant_from_parts before offered));
  assert (forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> invariant_kept before next) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.smt_sync' 1 1
  )

let clock_exact_in (h: Seq.seq Nickel.Register.fact) (sel: Envelope.t_Id -> Type0) (c: u64) : Type0 =
  Prims.l_and (Prims.l_and (v c > 0) (forall(g: Nickel.Register.fact). Prims.l_and (stored h g) (sel g.f_id) ==> v g.f_payload.f_lamport < v c)) (Prims.l_or (v c == 1) (exists(g: Nickel.Register.fact). Prims.l_and (Prims.l_and (stored h g) (sel g.f_id)) (v g.f_payload.f_lamport + 1 == v c)))

let clocks_exact (h: Seq.seq Nickel.Register.fact) : Type0 =
  forall(f: Nickel.Register.fact). stored h f ==> clock_exact_in h (anc_of h f) f.f_payload.f_lamport

let values_changed (h: Seq.seq Nickel.Register.fact) : Type0 =
  forall(f: Nickel.Register.fact). stored h f ==> Prims.l_not (Nickel.Register.bytes_same (Alloc.Vec.impl_1__as_slice f.f_payload.f_value) (Alloc.Vec.impl_1__as_slice f.f_payload.f_observed))

let clock_exact_from_basis (basis: t_Slice Nickel.Register.fact) (h: Seq.seq Nickel.Register.fact) (sel: Envelope.t_Id -> Type0) (c: u64) : Lemma (requires (holds_selected basis h sel /\ Nickel.Register.clock_successor basis c)) (ensures clock_exact_in h sel c) =
  ()

let clock_respects_sel (h: Seq.seq Nickel.Register.fact) (s1: Envelope.t_Id -> Type0) (s2: Envelope.t_Id -> Type0) (c: u64) : Lemma (requires forall(id: Envelope.t_Id). s1 id <==> s2 id) (ensures clock_exact_in h s1 c <==> clock_exact_in h s2 c) =
  ()

let clock_unchanged_by_extension (h: Seq.seq Nickel.Register.fact) (h2: Seq.seq Nickel.Register.fact) (fnew: Nickel.Register.fact) (sel: Envelope.t_Id -> Type0) (c: u64) : Lemma (requires (extends_by h h2 fnew /\ Prims.l_not (sel fnew.f_id))) (ensures clock_exact_in h2 sel c <==> clock_exact_in h sel c) =
  ()

let clock_kept (h: Seq.seq Nickel.Register.fact) (h2: Seq.seq Nickel.Register.fact) (fnew: Nickel.Register.fact) (g: Nickel.Register.fact) : Lemma (requires (Prims.l_and (extends_by h h2 fnew) (unreferenced h2 fnew.f_id) /\ stored h2 g /\ clock_exact_in h (anc_of h g) g.f_payload.f_lamport)) (ensures clock_exact_in h2 (anc_of h2 g) g.f_payload.f_lamport) =
  ancestry_unchanged_by_extension h h2 fnew (Alloc.Vec.impl_1__as_slice g.f_after);
  assert (Prims.l_and (Prims.l_not ((anc_of h2 g) fnew.f_id)) (forall(id: Envelope.t_Id). (anc_of h2 g) id <==> (anc_of h g) id)) by (
    Tactics.prune "Nickel.RegisterHistory.id_ancestor";
    Tactics.prune "Nickel.RegisterHistory.id_path";
    Tactics.smt_sync' 1 1
  );
  clock_unchanged_by_extension h h2 fnew (anc_of h2 g) g.f_payload.f_lamport;
  clock_respects_sel h (anc_of h2 g) (anc_of h g) g.f_payload.f_lamport

let clocks_and_values_preserved (h: Seq.seq Nickel.Register.fact) (h2: Seq.seq Nickel.Register.fact) (fnew: Nickel.Register.fact) : Lemma (requires (Prims.l_and (extends_by h h2 fnew) (unreferenced h2 fnew.f_id) /\ Prims.l_and (clocks_exact h) (clock_exact_in h (anc_of h fnew) fnew.f_payload.f_lamport) /\ Prims.l_and (values_changed h) (Prims.l_not (Nickel.Register.bytes_same (Alloc.Vec.impl_1__as_slice fnew.f_payload.f_value) (Alloc.Vec.impl_1__as_slice fnew.f_payload.f_observed))))) (ensures Prims.l_and (clocks_exact h2) (values_changed h2)) =
  let each (g: Nickel.Register.fact) : Lemma (requires stored h2 g) (ensures clock_exact_in h2 (anc_of h2 g) g.f_payload.f_lamport) = clock_kept h h2 fnew g in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each)

let offered_clock_and_value (before: Native.t_Replica) (offered: Nickel.Register.fact) : Type0 =
  Prims.l_and (clock_exact_in (Alloc.Vec.impl_1__as_slice before.f_facts) (anc_of (Alloc.Vec.impl_1__as_slice before.f_facts) offered) offered.f_payload.f_lamport) (Prims.l_not (Nickel.Register.bytes_same (Alloc.Vec.impl_1__as_slice offered.f_payload.f_value) (Alloc.Vec.impl_1__as_slice offered.f_payload.f_observed)))

let witness_clock_and_value (before: Native.t_Replica) (offered: Nickel.Register.fact) (selected: Alloc.Vec.t_Vec Envelope.t_Id Alloc.Alloc.t_Global) (basis: Alloc.Vec.t_Vec Nickel.Register.fact Alloc.Alloc.t_Global) : Lemma (requires ((forall(id: Envelope.t_Id). Nickel.RegisterPast.member (Alloc.Vec.impl_1__as_slice selected) id <==> Nickel.RegisterPast.ancestor Native.v_OPS._1 (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice offered.f_after) id) /\ Nickel.RegisterPast.selected_prefix Native.v_OPS._1 (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice selected) (Seq.length (Alloc.Vec.impl_1__as_slice before.f_facts)) (Alloc.Vec.impl_1__as_slice basis) /\ frozen_causal_observation before offered basis)) (ensures offered_clock_and_value before offered) =
  let facts = Alloc.Vec.impl_1__as_slice before.f_facts in
  let b = Alloc.Vec.impl_1__as_slice basis in
  register_ops_are_exact ();
  filter_has_selected_facts Native.v_OPS._1 facts (Alloc.Vec.impl_1__as_slice selected) (Seq.length facts) b;
  assert (holds_selected b facts (sel_of selected));
  clock_exact_from_basis b facts (sel_of selected) offered.f_payload.f_lamport;
  FStar.Classical.forall_intro (register_ancestor_is_id_ancestor facts (Alloc.Vec.impl_1__as_slice offered.f_after));
  clock_respects_sel facts (sel_of selected) (anc_of facts offered) offered.f_payload.f_lamport

let exact_basis_gives_clock_and_value (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (requires exact_selected_basis before offered) (ensures offered_clock_and_value before offered) =
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (witness_clock_and_value before offered));
  assert (offered_clock_and_value before offered) by (
    Tactics.prune "Nickel_crdt.Event_layer.validate_event";
    Tactics.prune "Nickel_crdt.Event_layer.select_basis";
    Tactics.smt_sync' 1 1
  )

let no_forbidden_prefix (facts: t_Slice Nickel.Register.fact) (offered: Nickel.Register.fact) (eops: Nickel.RegisterPast.reops) (selected: Nickel.RegisterPast.ids_vec) (at: nat) : Type0 =
  forall(j: nat). Prims.l_and (j < at) (j < Seq.length facts) ==> Prims.l_not (Prims.l_and (Nickel_crdt.Event_layer.has_id (Alloc.Vec.impl_1__as_slice selected) (eops._1._1._1 (Seq.index facts j)) eops._1 == true) (eops._2._2 (eops._1._1._1 (Seq.index facts j)) (eops._1._1._1 offered) == true))

let stream_checks (facts: t_Slice Nickel.Register.fact) (offered: Nickel.Register.fact) (eops: Nickel.RegisterPast.reops) (selected: Nickel.RegisterPast.ids_vec) : Type0 =
  Prims.l_and (((match eops._2._1 (eops._1._1._1 offered) with | Option.Option_Some prev -> begin Nickel_crdt.Event_layer.has_id (Alloc.Vec.impl_1__as_slice selected) prev eops._1 == true end | Option.Option_None -> begin Prims.l_True end) <: Type0)) (no_forbidden_prefix facts offered eops selected (Seq.length facts))

let validated_stream_checks (facts: t_Slice Nickel.Register.fact) (offered: Nickel.Register.fact) (eops: Nickel.RegisterPast.reops) : Lemma (ensures forall(selected: Nickel.RegisterPast.ids_vec). Nickel_crdt.Event_layer.validate_event facts offered eops == Result.Result_Ok selected ==> stream_checks facts offered eops selected) =
  Nickel.EventGraph.validated_stream_checks facts offered eops;
  assert (forall(selected: Nickel.RegisterPast.ids_vec). Nickel_crdt.Event_layer.validate_event facts offered eops == Result.Result_Ok selected ==> stream_checks facts offered eops selected) by (
    Tactics.prune "Nickel_crdt.Event_layer.validate_event";
    Tactics.prune "Nickel.EventGraph.validated_stream_checks";
    Tactics.smt_sync' 1 1
  )

let stream_ok_in (h: Seq.seq Nickel.Register.fact) (sel: Envelope.t_Id -> Type0) (f: Nickel.Register.fact) : Type0 =
  Prims.l_and (Prims.l_and (v f.f_id.f_counter >= 1) (v f.f_id.f_counter > 1 ==> (exists(g: Nickel.Register.fact). Prims.l_and (Prims.l_and (Prims.l_and (stored h g) (sel g.f_id)) (g.f_id.f_peer == f.f_id.f_peer)) (v g.f_id.f_counter + 1 == v f.f_id.f_counter)))) (forall(g: Nickel.Register.fact). Prims.l_and (Prims.l_and (stored h g) (sel g.f_id)) (g.f_id.f_peer == f.f_id.f_peer) ==> v g.f_id.f_counter < v f.f_id.f_counter)

let streams_ok (h: Seq.seq Nickel.Register.fact) : Type0 =
  forall(f: Nickel.Register.fact). stored h f ==> stream_ok_in h (anc_of h f) f

let stream_respects_sel (h: Seq.seq Nickel.Register.fact) (s1: Envelope.t_Id -> Type0) (s2: Envelope.t_Id -> Type0) (f: Nickel.Register.fact) : Lemma (requires forall(id: Envelope.t_Id). s1 id <==> s2 id) (ensures stream_ok_in h s1 f <==> stream_ok_in h s2 f) =
  ()

let stream_unchanged_by_extension (h: Seq.seq Nickel.Register.fact) (h2: Seq.seq Nickel.Register.fact) (fnew: Nickel.Register.fact) (sel: Envelope.t_Id -> Type0) (f: Nickel.Register.fact) : Lemma (requires (extends_by h h2 fnew /\ Prims.l_not (sel fnew.f_id))) (ensures stream_ok_in h2 sel f <==> stream_ok_in h sel f) =
  ()

let stream_kept (h: Seq.seq Nickel.Register.fact) (h2: Seq.seq Nickel.Register.fact) (fnew: Nickel.Register.fact) (g: Nickel.Register.fact) : Lemma (requires (Prims.l_and (extends_by h h2 fnew) (unreferenced h2 fnew.f_id) /\ stored h2 g /\ stream_ok_in h (anc_of h g) g)) (ensures stream_ok_in h2 (anc_of h2 g) g) =
  ancestry_unchanged_by_extension h h2 fnew (Alloc.Vec.impl_1__as_slice g.f_after);
  assert (Prims.l_and (Prims.l_not ((anc_of h2 g) fnew.f_id)) (forall(id: Envelope.t_Id). (anc_of h2 g) id <==> (anc_of h g) id)) by (
    Tactics.prune "Nickel.RegisterHistory.id_ancestor";
    Tactics.prune "Nickel.RegisterHistory.id_path";
    Tactics.smt_sync' 1 1
  );
  stream_unchanged_by_extension h h2 fnew (anc_of h2 g) g;
  stream_respects_sel h (anc_of h2 g) (anc_of h g) g

let streams_preserved (h: Seq.seq Nickel.Register.fact) (h2: Seq.seq Nickel.Register.fact) (fnew: Nickel.Register.fact) : Lemma (requires (Prims.l_and (extends_by h h2 fnew) (unreferenced h2 fnew.f_id) /\ Prims.l_and (streams_ok h) (stream_ok_in h (anc_of h fnew) fnew))) (ensures streams_ok h2) =
  let each (g: Nickel.Register.fact) : Lemma (requires stored h2 g) (ensures stream_ok_in h2 (anc_of h2 g) g) = stream_kept h h2 fnew g in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each)

let rec closed_path_ends_stored (h: Seq.seq Nickel.Register.fact) (start: Envelope.t_Id) (steps: Prims.list Envelope.t_Id) (finish: Envelope.t_Id) : Lemma (requires (closed h /\ (exists(g: Nickel.Register.fact). Prims.l_and (stored h g) (g.f_id == start)) /\ id_path h start steps finish)) (ensures exists(g: Nickel.Register.fact). Prims.l_and (stored h g) (g.f_id == finish)) (decreases steps) =
  match steps with | Prims.Nil -> begin () end | Prims.Cons next rest -> begin assert (exists(g: Nickel.Register.fact). Prims.l_and (stored h g) (g.f_id == next));
  closed_path_ends_stored h next rest finish end

let ancestors_stored (before: Native.t_Replica) (offered: Nickel.Register.fact) : Type0 =
  forall(x: Envelope.t_Id). (anc_of (Alloc.Vec.impl_1__as_slice before.f_facts) offered) x ==> (exists(g: Nickel.Register.fact). Prims.l_and (stored (Alloc.Vec.impl_1__as_slice before.f_facts) g) (g.f_id == x))

let closed_ancestors_stored (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (requires Prims.l_and (closed (Alloc.Vec.impl_1__as_slice before.f_facts)) (parents_stored before offered)) (ensures ancestors_stored before offered) =
  let h = Alloc.Vec.impl_1__as_slice before.f_facts in
  let each (root: Envelope.t_Id) (steps: Prims.list Envelope.t_Id) (x: Envelope.t_Id) : Lemma (requires (Nickel.RegisterPast.member (Alloc.Vec.impl_1__as_slice offered.f_after) root /\ id_path h root steps x)) (ensures exists(g: Nickel.Register.fact). Prims.l_and (stored h g) (g.f_id == x)) = closed_path_ends_stored h root steps x in
  FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 each)

let prev_id (id: Envelope.t_Id) : Envelope.t_Id =
  match Native.previous id with | Option.Option_Some p -> begin p end | Option.Option_None -> begin id end

let offered_stream_from_checks (before: Native.t_Replica) (offered: Nickel.Register.fact) (selected: Alloc.Vec.t_Vec Envelope.t_Id Alloc.Alloc.t_Global) : Lemma (requires ((forall(id: Envelope.t_Id). Nickel.RegisterPast.member (Alloc.Vec.impl_1__as_slice selected) id <==> Nickel.RegisterPast.ancestor Native.v_OPS._1 (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice offered.f_after) id) /\ stream_checks (Alloc.Vec.impl_1__as_slice before.f_facts) offered Native.v_OPS selected /\ v offered.f_id.f_counter > 0 /\ ancestors_stored before offered)) (ensures stream_ok_in (Alloc.Vec.impl_1__as_slice before.f_facts) (anc_of (Alloc.Vec.impl_1__as_slice before.f_facts) offered) offered) =
  let facts = Alloc.Vec.impl_1__as_slice before.f_facts in
  let sel = Alloc.Vec.impl_1__as_slice selected in
  register_ops_are_exact ();
  FStar.Classical.forall_intro (register_ancestor_is_id_ancestor facts (Alloc.Vec.impl_1__as_slice offered.f_after));
  let membership (id: Envelope.t_Id) : Lemma (ensures Nickel_crdt.Event_layer.has_id sel id Native.v_OPS._1 == true <==> Nickel.RegisterPast.member sel id) = Nickel.RegisterPast.id_membership_is_exact sel id Native.v_OPS._1 in
  FStar.Classical.forall_intro membership;
  let predecessor_at (p: Envelope.t_Id) : Lemma (requires Native.previous offered.f_id == Option.Option_Some p) (ensures exists(g: Nickel.Register.fact). Prims.l_and (Prims.l_and (Prims.l_and (stored facts g) ((anc_of facts offered) g.f_id)) (g.f_id.f_peer == offered.f_id.f_peer)) (v g.f_id.f_counter + 1 == v offered.f_id.f_counter)) =
    assert (Nickel_crdt.Event_layer.has_id sel p Native.v_OPS._1 == true) by (
      Tactics.prune "Nickel.RegisterHistory.anc_of";
      Tactics.prune "Nickel.RegisterValid.ancestors_stored";
      Tactics.smt_sync' 1 1
    );
    assert ((anc_of facts offered) p) by (
      Tactics.prune "Nickel.RegisterValid.stream_checks";
      Tactics.prune "Nickel.RegisterValid.ancestors_stored";
      Tactics.smt_sync' 1 1
    );
    assert (Prims.l_and (p.f_peer == offered.f_id.f_peer) (v p.f_counter + 1 == v offered.f_id.f_counter)) by (
      Tactics.prune "Nickel.RegisterHistory.anc_of";
      Tactics.prune "Nickel.RegisterValid.stream_checks";
      Tactics.prune "Nickel.RegisterValid.ancestors_stored";
      Tactics.smt_sync' 1 1
    ) in
  let predecessor (u: unit) : Lemma (requires v offered.f_id.f_counter > 1) (ensures exists(g: Nickel.Register.fact). Prims.l_and (Prims.l_and (Prims.l_and (stored facts g) ((anc_of facts offered) g.f_id)) (g.f_id.f_peer == offered.f_id.f_peer)) (v g.f_id.f_counter + 1 == v offered.f_id.f_counter)) = predecessor_at (prev_id offered.f_id) in
  FStar.Classical.move_requires predecessor ();
  let no_forbidden_at (j: nat) : Lemma (requires Prims.l_and (Prims.l_and (j < Seq.length facts) ((anc_of facts offered) (Seq.index facts j).f_id)) ((Seq.index facts j).f_id.f_peer == offered.f_id.f_peer)) (ensures v (Seq.index facts j).f_id.f_counter < v offered.f_id.f_counter) =
    assert (Nickel_crdt.Event_layer.has_id sel (Seq.index facts j).f_id Native.v_OPS._1 == true) by (
      Tactics.prune "Nickel_crdt.Register.forbidden";
      Tactics.prune "Nickel.RegisterValid.stream_checks";
      Tactics.prune "Nickel.RegisterValid.ancestors_stored";
      Tactics.smt_sync' 1 1
    );
    assert (Prims.l_not (Prims.l_and (Nickel_crdt.Event_layer.has_id sel (Native.v_OPS._1._1._1 (Seq.index facts j)) Native.v_OPS._1 == true) (Native.v_OPS._2._2 (Native.v_OPS._1._1._1 (Seq.index facts j)) (Native.v_OPS._1._1._1 offered) == true))) by (
      Tactics.prune "Nickel_crdt.Register.forbidden";
      Tactics.prune "Nickel.RegisterHistory.anc_of";
      Tactics.prune "Nickel.RegisterValid.ancestors_stored";
      Tactics.smt_sync' 1 1
    );
    assert (Native.forbidden (Seq.index facts j).f_id offered.f_id == false) by (
      Tactics.prune "Nickel.RegisterValid.stream_checks";
      Tactics.prune "Nickel.RegisterHistory.anc_of";
      Tactics.prune "Nickel.RegisterValid.ancestors_stored";
      Tactics.smt_sync' 1 1
    );
    assert (v (Seq.index facts j).f_id.f_counter < v offered.f_id.f_counter) by (
      Tactics.prune "Nickel.RegisterHistory.anc_of";
      Tactics.prune "Nickel.RegisterValid.stream_checks";
      Tactics.prune "Nickel.RegisterValid.ancestors_stored";
      Tactics.smt_sync' 1 1
    ) in
  let no_forbidden_stored (g: Nickel.Register.fact) (i: nat) : Lemma (requires Prims.l_and (Prims.l_and (Prims.l_and (i < Seq.length facts) (Seq.index facts i == g)) ((anc_of facts offered) g.f_id)) (g.f_id.f_peer == offered.f_id.f_peer)) (ensures v g.f_id.f_counter < v offered.f_id.f_counter) = no_forbidden_at i in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 no_forbidden_stored);
  assert (v offered.f_id.f_counter > 1 ==> (exists(g: Nickel.Register.fact). Prims.l_and (Prims.l_and (Prims.l_and (stored facts g) ((anc_of facts offered) g.f_id)) (g.f_id.f_peer == offered.f_id.f_peer)) (v g.f_id.f_counter + 1 == v offered.f_id.f_counter))) by (
    Tactics.prune "Nickel.RegisterHistory.anc_of";
    Tactics.prune "Nickel.RegisterValid.stream_checks";
    Tactics.prune "Nickel.RegisterValid.ancestors_stored";
    Tactics.prune "Nickel_crdt.Register.forbidden";
    Tactics.smt_sync' 1 1
  );
  assert (forall(g: Nickel.Register.fact). Prims.l_and (Prims.l_and (stored facts g) ((anc_of facts offered) g.f_id)) (g.f_id.f_peer == offered.f_id.f_peer) ==> v g.f_id.f_counter < v offered.f_id.f_counter) by (
    Tactics.prune "Nickel.RegisterHistory.anc_of";
    Tactics.prune "Nickel.RegisterValid.stream_checks";
    Tactics.prune "Nickel.RegisterValid.ancestors_stored";
    Tactics.prune "Nickel_crdt.Register.forbidden";
    Tactics.smt_sync' 1 1
  );
  assert (stream_ok_in facts (anc_of facts offered) offered) by (
    Tactics.prune "Nickel.RegisterValid.stream_checks";
    Tactics.prune "Nickel.RegisterValid.ancestors_stored";
    Tactics.prune "Nickel_crdt.Register.forbidden";
    Tactics.smt_sync' 1 1
  )

let history_invariant (r: Native.t_Replica) : Type0 =
  Prims.l_and (Prims.l_and (Prims.l_and (observation_invariant r) (clocks_exact (Alloc.Vec.impl_1__as_slice r.f_facts))) (values_changed (Alloc.Vec.impl_1__as_slice r.f_facts))) (streams_ok (Alloc.Vec.impl_1__as_slice r.f_facts))

let offered_stream_ok (before: Native.t_Replica) (offered: Nickel.Register.fact) : Type0 =
  closed (Alloc.Vec.impl_1__as_slice before.f_facts) ==> stream_ok_in (Alloc.Vec.impl_1__as_slice before.f_facts) (anc_of (Alloc.Vec.impl_1__as_slice before.f_facts) offered) offered

let stream_witness (before: Native.t_Replica) (offered: Nickel.Register.fact) (selected: Alloc.Vec.t_Vec Envelope.t_Id Alloc.Alloc.t_Global) (basis: Alloc.Vec.t_Vec Nickel.Register.fact Alloc.Alloc.t_Global) : Lemma (requires (Prims.l_and (Prims.l_and (Nickel_crdt.Event_layer.validate_event (Alloc.Vec.impl_1__as_slice before.f_facts) offered Native.v_OPS == Result.Result_Ok selected) (Nickel_crdt.Event_layer.select_basis (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice selected) Native.v_OPS._1 == Result.Result_Ok basis)) (Nickel.Register.basis_payload_checks before offered basis) /\ parents_stored before offered)) (ensures offered_stream_ok before offered) =
  selected_basis_is_exact before offered selected basis;
  validated_stream_checks (Alloc.Vec.impl_1__as_slice before.f_facts) offered Native.v_OPS;
  assert (stream_checks (Alloc.Vec.impl_1__as_slice before.f_facts) offered Native.v_OPS selected) by (
    Tactics.prune "Nickel_crdt.Event_layer.validate_event";
    Tactics.smt_sync' 1 1
  );
  FStar.Classical.move_requires (closed_ancestors_stored before) offered;
  FStar.Classical.move_requires (offered_stream_from_checks before offered) selected

let receive_added_offer_stream (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (ensures forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> offered_stream_ok before offered) =
  Nickel.Register.receive_added_checks_payload before offered;
  receive_added_parents_stored before offered;
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (stream_witness before offered));
  assert (forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> offered_stream_ok before offered) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel_crdt.Event_layer.validate_event";
    Tactics.prune "Nickel_crdt.Event_layer.select_basis";
    Tactics.smt_sync' 1 1
  )

let history_kept (before: Native.t_Replica) (next: Native.t_Replica) : Type0 =
  history_invariant before ==> history_invariant next

let history_from_parts (before: Native.t_Replica) (offered: Nickel.Register.fact) (next: Native.t_Replica) : Lemma (requires (Prims.l_and (invariant_kept before next) (history_extended_soundly before offered next) /\ Prims.l_and (Nickel.Register.appended_facts before offered next) (offered_clock_and_value before offered) /\ offered_stream_ok before offered)) (ensures history_kept before next) =
  let h = Alloc.Vec.impl_1__as_slice before.f_facts in
  let h2 = Alloc.Vec.impl_1__as_slice next.f_facts in
  assert (extends_by h h2 offered);
  FStar.Classical.move_requires (clocks_and_values_preserved h h2) offered;
  FStar.Classical.move_requires (streams_preserved h h2) offered;
  assert (history_kept before next) by (
    Tactics.prune "Nickel.RegisterValid.streams_ok";
    Tactics.prune "Nickel.RegisterValid.stream_ok_in";
    Tactics.prune "Nickel.RegisterValid.clocks_exact";
    Tactics.prune "Nickel.RegisterValid.values_changed";
    Tactics.prune "Nickel.RegisterValid.clock_exact_in";
    Tactics.prune "Nickel.RegisterHistory.observations_ok";
    Tactics.smt_sync' 1 1
  )

let receive_added_preserves_history (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (ensures forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> history_kept before next) =
  receive_added_preserves_invariant before offered;
  receive_added_extends_soundly before offered;
  Nickel.Register.receive_added_retains_exact_facts before offered;
  receive_added_basis_is_exact_ancestry before offered;
  FStar.Classical.move_requires (exact_basis_gives_clock_and_value before) offered;
  receive_added_offer_stream before offered;
  FStar.Classical.forall_intro (FStar.Classical.move_requires (history_from_parts before offered));
  assert (forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> history_kept before next) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.RegisterValid.history_kept";
    Tactics.prune "Nickel.RegisterHistory.exact_selected_basis";
    Tactics.prune "Nickel.RegisterValid.offered_clock_and_value";
    Tactics.prune "Nickel.RegisterValid.offered_stream_ok";
    Tactics.prune "Nickel.RegisterHistory.history_extended_soundly";
    Tactics.prune "Nickel.RegisterValid.invariant_kept";
    Tactics.prune "Nickel.Register.appended_facts";
    Tactics.prune "Nickel.Register.receive_preserves_private";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel.Register.planned_adds_exact_fact";
    Tactics.smt_sync' 1 1
  )

let planned_preserves_history (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (ensures forall(candidate: Native.t_Replica). Native.planned () before offered == Result.Result_Ok (Option.Option_Some candidate) ==> history_kept before candidate) =
  Nickel.Register.receive_publication_is_exact before offered;
  receive_added_preserves_history before offered;
  assert (forall(candidate: Native.t_Replica). Native.planned () before offered == Result.Result_Ok (Option.Option_Some candidate) ==> history_kept before candidate) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.RegisterValid.history_kept";
    Tactics.smt_sync' 1 1
  )

let kept_transfers (before: Native.t_Replica) (candidate: Native.t_Replica) (next: Native.t_Replica) : Lemma (requires (history_kept before candidate /\ Prims.l_and (next.f_facts == candidate.f_facts) (next.f_initial == candidate.f_initial))) (ensures history_kept before next) =
  ()

let write_counted_preserves_history (before: Native.t_Replica) (key: u64) (value: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) : Lemma (ensures forall(next: Native.t_Replica) (authored: Nickel.Register.fact). Native.impl_Replica__write before key value == (next, Result.Result_Ok (Option.Option_Some authored)) ==> history_kept before next) =
  Nickel.Register.write_installs_successful_candidate before key value;
  FStar.Classical.forall_intro (planned_preserves_history before);
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (kept_transfers before));
  assert (forall(next: Native.t_Replica) (authored: Nickel.Register.fact). Native.impl_Replica__write before key value == (next, Result.Result_Ok (Option.Option_Some authored)) ==> history_kept before next) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__write";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.RegisterValid.history_kept";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel.Register.planned_adds_exact_fact";
    Tactics.smt_sync' 1 1
  )

let kept_reflexive (before: Native.t_Replica) : Lemma (ensures history_kept before before) =
  ()

let receive_preserves_history (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (ensures history_kept before (Native.impl_Replica__receive before offered)._1) =
  kept_reflexive before;
  Nickel.Register.receive_publication_is_exact before offered;
  receive_added_preserves_history before offered;
  match Native.planned () before offered with | Result.Result_Err _ -> begin assert (history_kept before (Native.impl_Replica__receive before offered)._1) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.RegisterValid.history_kept";
    Tactics.prune "Nickel.Register.receive_preserves_private";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel.Register.planned_adds_exact_fact";
    Tactics.smt_sync' 1 1
  ) end | Result.Result_Ok option -> begin match option with | Option.Option_None -> begin assert (history_kept before (Native.impl_Replica__receive before offered)._1) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.RegisterValid.history_kept";
    Tactics.prune "Nickel.Register.receive_preserves_private";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel.Register.planned_adds_exact_fact";
    Tactics.smt_sync' 1 1
  ) end | Option.Option_Some candidate -> begin assert (history_kept before (Native.impl_Replica__receive before offered)._1) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.RegisterValid.history_kept";
    Tactics.prune "Nickel.Register.receive_preserves_private";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel.Register.planned_adds_exact_fact";
    Tactics.smt_sync' 1 1
  ) end end

let write_preserves_history (before: Native.t_Replica) (key: u64) (value: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) : Lemma (ensures history_kept before (Native.impl_Replica__write before key value)._1) =
  kept_reflexive before;
  Nickel.Register.write_installs_successful_candidate before key value;
  write_counted_preserves_history before key value;
  match Native.impl_Replica__write before key value with | (next, result) -> begin match result with | Result.Result_Err _ -> begin assert (history_kept before (Native.impl_Replica__write before key value)._1) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__write";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.RegisterValid.history_kept";
    Tactics.prune "Nickel.Register.receive_preserves_private";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel.Register.planned_adds_exact_fact";
    Tactics.smt_sync' 1 1
  ) end | Result.Result_Ok option -> begin match option with | Option.Option_None -> begin assert (history_kept before (Native.impl_Replica__write before key value)._1) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__write";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.RegisterValid.history_kept";
    Tactics.prune "Nickel.Register.receive_preserves_private";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel.Register.planned_adds_exact_fact";
    Tactics.smt_sync' 1 1
  ) end | Option.Option_Some authored -> begin assert (history_kept before (Native.impl_Replica__write before key value)._1) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__write";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.RegisterValid.history_kept";
    Tactics.prune "Nickel.Register.receive_preserves_private";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel.Register.planned_adds_exact_fact";
    Tactics.smt_sync' 1 1
  ) end end end

let new_establishes_history (writer: u64) (initial: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) : Lemma (ensures forall(r: Native.t_Replica). Native.impl_Replica__new writer initial == Result.Result_Ok r ==> history_invariant r) =
  Nickel.Vector.empty_vector_contents #Nickel.Register.fact ();
  let each (r: Native.t_Replica) : Lemma (requires Native.impl_Replica__new writer initial == Result.Result_Ok r) (ensures history_invariant r) =
    assert (Seq.length (Alloc.Vec.impl_1__as_slice r.f_facts) == 0);
    assert (forall(f: Nickel.Register.fact). Prims.l_not (stored (Alloc.Vec.impl_1__as_slice r.f_facts) f)) in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each)