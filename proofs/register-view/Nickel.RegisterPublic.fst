(* Latte generated F* view *)
module Nickel.RegisterPublic

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

open Nickel.RegisterValid

let positional_ids_are_stored_unique (facts: Alloc.Vec.t_Vec Nickel.Register.fact Alloc.Alloc.t_Global) : Lemma (requires Nickel.Register.fact_ids_unique facts) (ensures stored_unique (Alloc.Vec.impl_1__as_slice facts)) =
  let items = Alloc.Vec.impl_1__as_slice facts in
  let each (f: Nickel.Register.fact) (g: Nickel.Register.fact) (i: nat) (j: nat) : Lemma (requires (Prims.l_and (i < Seq.length items) (Seq.index items i == f) /\ Prims.l_and (j < Seq.length items) (Seq.index items j == g) /\ f.f_id == g.f_id)) (ensures f == g) = () in
  FStar.Classical.forall_intro_4 (FStar.Classical.move_requires_4 each)

let public_history (r: Native.t_Replica) : Type0 =
  Prims.l_and (history_invariant r) (Nickel.Register.fact_ids_unique r.f_facts)

let receive_preserves_public_history (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (requires public_history before) (ensures public_history (Native.impl_Replica__receive before offered)._1) =
  receive_preserves_history before offered;
  Nickel.Register.receive_preserves_unique_ids before offered;
  assert (public_history (Native.impl_Replica__receive before offered)._1) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.Register.receive_preserves_private";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel.Register.planned_adds_exact_fact";
    Tactics.prune "Nickel.RegisterValid.history_invariant";
    Tactics.prune "Nickel.Register.fact_ids_unique";
    Tactics.smt_sync' 1 1
  )

let write_preserves_public_history (before: Native.t_Replica) (key: u64) (value: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) : Lemma (requires public_history before) (ensures public_history (Native.impl_Replica__write before key value)._1) =
  write_preserves_history before key value;
  Nickel.Register.write_preserves_unique_ids before key value;
  assert (public_history (Native.impl_Replica__write before key value)._1) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__write";
    Tactics.prune "Nickel.RegisterValid.history_invariant";
    Tactics.prune "Nickel.Register.fact_ids_unique";
    Tactics.smt_sync' 1 1
  )

let new_establishes_public_history (writer: u64) (initial: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) (limits: Native.t_Limits) : Lemma (ensures forall(r: Native.t_Replica). Native.impl_Replica__new writer initial limits == Result.Result_Ok r ==> public_history r) =
  new_establishes_history writer initial limits;
  Nickel.Register.new_has_unique_ids writer initial limits;
  assert (forall(r: Native.t_Replica). Native.impl_Replica__new writer initial limits == Result.Result_Ok r ==> public_history r) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__new";
    Tactics.prune "Nickel.RegisterValid.history_invariant";
    Tactics.prune "Nickel.Register.fact_ids_unique";
    Tactics.smt_sync' 1 1
  )

let index_is_member (ids: t_Slice Envelope.t_Id) (k: nat) : Lemma (requires k < Seq.length ids) (ensures Nickel.RegisterPast.member ids (Seq.index ids k)) =
  assert (v (mk_usize k) == k)

let positional_clocks_from_ids (facts: t_Slice Nickel.Register.fact) : Lemma (requires id_clocks_increase facts) (ensures clocks_increase facts) =
  let each (newer: nat) (older: nat) (k: nat) : Lemma (requires (Prims.l_and (newer < Seq.length facts) (older < Seq.length facts) /\ Prims.l_and (k < Seq.length (Alloc.Vec.impl_1__as_slice (Seq.index facts newer).f_after)) (Seq.index (Alloc.Vec.impl_1__as_slice (Seq.index facts newer).f_after) k == (Seq.index facts older).f_id))) (ensures clock_below facts older newer) =
    index_is_member (Alloc.Vec.impl_1__as_slice (Seq.index facts newer).f_after) k;
    assert (stored facts (Seq.index facts newer));
    assert (stored facts (Seq.index facts older)) in
  FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 each)

let stream_step_at (h: t_Slice Nickel.Register.fact) (i: nat) : Lemma (requires (Prims.l_and (Prims.l_and (stored_unique h) (id_clocks_increase h)) (streams_ok h) /\ Prims.l_and (i < Seq.length h) (v (Seq.index h i).f_id.f_counter > 1))) (ensures exists(j: nat). Prims.l_and (predecessor_of h i j) (clock_below h j i)) =
  let f = Seq.index h i in
  assert (stored h f);
  let via (g: Nickel.Register.fact) (j: nat) (root: Envelope.t_Id) (steps: Prims.list Envelope.t_Id) : Lemma (requires (Prims.l_and (j < Seq.length h) (Seq.index h j == g) /\ Prims.l_and (g.f_id.f_peer == f.f_id.f_peer) (v g.f_id.f_counter + 1 == v f.f_id.f_counter) /\ Prims.l_and (Nickel.RegisterPast.member (Alloc.Vec.impl_1__as_slice f.f_after) root) (id_path h root steps g.f_id))) (ensures exists(j: nat). Prims.l_and (predecessor_of h i j) (clock_below h j i)) =
    assert (id_edge h f.f_id root);
    assert (id_path h f.f_id (Prims.Cons root steps) g.f_id);
    assert (stored h g);
    id_path_clock_decreases h f root steps g;
    assert (Prims.l_and (predecessor_of h i j) (clock_below h j i)) by (
      Tactics.prune "Nickel.RegisterHistory.id_path";
      Tactics.prune "Nickel.RegisterHistory.id_edge";
      Tactics.prune "Nickel.RegisterHistory.id_clocks_increase";
      Tactics.prune "Nickel.RegisterHistory.stored_unique";
      Tactics.prune "Nickel.RegisterValid.streams_ok";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_4 (FStar.Classical.move_requires_4 via);
  assert (exists(j: nat). Prims.l_and (predecessor_of h i j) (clock_below h j i)) by (
    Tactics.prune "Nickel.RegisterHistory.id_path";
    Tactics.prune "Nickel.RegisterHistory.id_clocks_increase";
    Tactics.prune "Nickel.RegisterHistory.stored_unique";
    Tactics.smt_sync' 1 1
  )

let counter_positive_at (h: t_Slice Nickel.Register.fact) (i: nat) : Lemma (requires (streams_ok h /\ i < Seq.length h)) (ensures v (Seq.index h i).f_id.f_counter >= 1) =
  assert (stored h (Seq.index h i))

let public_single_value_premises (r: Native.t_Replica) : Lemma (requires public_history r) (ensures Prims.l_and (Prims.l_and (stream_steps (Alloc.Vec.impl_1__as_slice r.f_facts)) (ids_unique (Alloc.Vec.impl_1__as_slice r.f_facts))) (counters_positive (Alloc.Vec.impl_1__as_slice r.f_facts))) =
  let h = Alloc.Vec.impl_1__as_slice r.f_facts in
  positional_ids_are_stored_unique r.f_facts;
  let positive (i: nat) : Lemma (ensures i < Seq.length h ==> v (Seq.index h i).f_id.f_counter >= 1) = if i < Seq.length h then
    begin counter_positive_at h i end
  else
    begin () end in
  let step (i: nat) : Lemma (ensures Prims.l_and (i < Seq.length h) (v (Seq.index h i).f_id.f_counter > 1) ==> (exists(j: nat). Prims.l_and (predecessor_of h i j) (clock_below h j i))) = if i < Seq.length h then
    begin if v (Seq.index h i).f_id.f_counter > 1 then
      begin stream_step_at h i end
    else
      begin () end end
  else
    begin () end in
  FStar.Classical.forall_intro positive;
  FStar.Classical.forall_intro step;
  assert (Prims.l_and (Prims.l_and (stream_steps h) (ids_unique h)) (counters_positive h)) by (
    Tactics.prune "Nickel.RegisterValid.streams_ok";
    Tactics.prune "Nickel.RegisterHistory.stored_unique";
    Tactics.prune "Nickel.RegisterHistory.id_clocks_increase";
    Tactics.smt_sync' 1 1
  )

let causal_read_is_single_valued_by_steps (facts: t_Slice Nickel.Register.fact) (key: u64) (initial: t_Slice u8) (x: t_Slice u8) (y: t_Slice u8) : Lemma (requires (Prims.l_and (Prims.l_and (stream_steps facts) (ids_unique facts)) (counters_positive facts) /\ causal_read facts key initial x /\ causal_read facts key initial y)) (ensures Nickel.Register.bytes_same x y) =
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (maximal_pair_is_one_fact facts key));
  FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 bytes_same_through)

let public_clocks_increase (r: Native.t_Replica) : Lemma (requires public_history r) (ensures clocks_increase (Alloc.Vec.impl_1__as_slice r.f_facts)) =
  positional_clocks_from_ids (Alloc.Vec.impl_1__as_slice r.f_facts);
  assert (clocks_increase (Alloc.Vec.impl_1__as_slice r.f_facts)) by (
    Tactics.prune "Nickel.RegisterHistory.clocks_increase";
    Tactics.prune "Nickel.RegisterHistory.stored_unique";
    Tactics.prune "Nickel.RegisterHistory.closed";
    Tactics.prune "Nickel.RegisterHistory.observations_ok";
    Tactics.prune "Nickel.RegisterValid.clocks_exact";
    Tactics.prune "Nickel.RegisterValid.values_changed";
    Tactics.prune "Nickel.RegisterValid.streams_ok";
    Tactics.prune "Nickel.Register.fact_ids_unique";
    Tactics.prune "Nickel.Register.receive_preserves_private";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel.Register.planned_adds_exact_fact";
    Tactics.smt_sync' 1 1
  )

let public_read_is_the_causal_read (r: Native.t_Replica) (key: u64) (x: t_Slice u8) : Lemma (requires public_history r) (ensures Prims.l_and (causal_read (Alloc.Vec.impl_1__as_slice r.f_facts) key (Alloc.Vec.impl_1__as_slice r.f_initial) (Alloc.Vec.impl_1__as_slice (Native.impl_Replica__read r key))) (causal_read (Alloc.Vec.impl_1__as_slice r.f_facts) key (Alloc.Vec.impl_1__as_slice r.f_initial) x ==> Nickel.Register.bytes_same (Alloc.Vec.impl_1__as_slice (Native.impl_Replica__read r key)) x)) =
  let h = Alloc.Vec.impl_1__as_slice r.f_facts in
  let init = Alloc.Vec.impl_1__as_slice r.f_initial in
  Nickel.Register.public_read_is_history r key;
  public_clocks_increase r;
  assert (clocks_increase h) by (
    Tactics.prune "Nickel.RegisterPublic.public_history";
    Tactics.prune "Nickel.Register.public_read_is_history";
    Tactics.prune "Nickel_crdt.Register.impl_Replica__read";
    Tactics.prune "Nickel_crdt.Register.read_history";
    Tactics.prune "Nickel_crdt.Register.winner";
    Tactics.prune "Nickel.RegisterHistory.id_clocks_increase";
    Tactics.prune "Nickel.RegisterHistory.parent_edge";
    Tactics.prune "Nickel.RegisterHistory.clock_below";
    Tactics.prune "Nickel.RegisterHistory.clocks_increase";
    Tactics.prune "Nickel.RegisterHistory.stored_unique";
    Tactics.prune "Nickel.RegisterHistory.closed";
    Tactics.prune "Nickel.RegisterHistory.observations_ok";
    Tactics.prune "Nickel.RegisterValid.clocks_exact";
    Tactics.prune "Nickel.RegisterValid.values_changed";
    Tactics.prune "Nickel.RegisterValid.streams_ok";
    Tactics.prune "Nickel.Register.fact_ids_unique";
    Tactics.prune "Nickel.Register.receive_preserves_private";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel.Register.planned_adds_exact_fact";
    Tactics.smt_sync' 1 1
  );
  read_history_is_causal_read h init key;
  public_single_value_premises r;
  FStar.Classical.move_requires (causal_read_is_single_valued_by_steps h key init (Alloc.Vec.impl_1__as_slice (Native.impl_Replica__read r key))) x;
  assert (Prims.l_and (causal_read h key init (Alloc.Vec.impl_1__as_slice (Native.impl_Replica__read r key))) (causal_read h key init x ==> Nickel.Register.bytes_same (Alloc.Vec.impl_1__as_slice (Native.impl_Replica__read r key)) x)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__read";
    Tactics.prune "Nickel.Register.public_read_is_history";
    Tactics.prune "Nickel_crdt.Register.read_history";
    Tactics.prune "Nickel_crdt.Register.winner";
    Tactics.prune "Nickel.RegisterHistory.causal_read";
    Tactics.prune "Nickel.RegisterPublic.public_history";
    Tactics.prune "Nickel.RegisterHistory.clocks_increase";
    Tactics.prune "Nickel.RegisterHistory.id_clocks_increase";
    Tactics.prune "Nickel.RegisterHistory.stream_steps";
    Tactics.smt_sync' 1 1
  )

let new_public_producer (writer: u64) (initial: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) (limits: Native.t_Limits) : Lemma (ensures forall(r: Native.t_Replica). Native.impl_Replica__new writer initial limits == Result.Result_Ok r ==> Prims.l_and (Prims.l_and (public_history r) (r.f_writer == writer)) (v r.f_next_counter == 1)) =
  new_establishes_public_history writer initial limits;
  let each (r: Native.t_Replica) : Lemma (requires Native.impl_Replica__new writer initial limits == Result.Result_Ok r) (ensures Prims.l_and (r.f_writer == writer) (v r.f_next_counter == 1)) = () in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each);
  assert (forall(r: Native.t_Replica). Native.impl_Replica__new writer initial limits == Result.Result_Ok r ==> Prims.l_and (Prims.l_and (public_history r) (r.f_writer == writer)) (v r.f_next_counter == 1)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__new";
    Tactics.prune "Nickel.RegisterPublic.public_history";
    Tactics.smt_sync' 1 1
  )

let receive_public_producer (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (requires public_history before) (ensures Prims.l_and (public_history (Native.impl_Replica__receive before offered)._1) (Nickel.Register.private_frame before (Native.impl_Replica__receive before offered)._1)) =
  receive_preserves_public_history before offered;
  Nickel.Register.receive_preserves_private before offered;
  assert (Prims.l_and (public_history (Native.impl_Replica__receive before offered)._1) (Nickel.Register.private_frame before (Native.impl_Replica__receive before offered)._1)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.RegisterPublic.public_history";
    Tactics.prune "Nickel.Register.private_frame";
    Tactics.prune "Nickel.Register.receive_preserves_private";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel.Register.planned_adds_exact_fact";
    Tactics.smt_sync' 1 1
  )

let write_public_producer (before: Native.t_Replica) (key: u64) (value: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) : Lemma (requires public_history before) (ensures Prims.l_and (Prims.l_and (public_history (Native.impl_Replica__write before key value)._1) (Nickel.Register.write_outcome before (Native.impl_Replica__write before key value))) (Nickel.Register.write_installation before key value (Native.impl_Replica__write before key value))) =
  write_preserves_public_history before key value;
  Nickel.Register.write_publication_on_every_return before key value;
  Nickel.Register.write_installs_successful_candidate before key value;
  assert (Prims.l_and (Prims.l_and (public_history (Native.impl_Replica__write before key value)._1) (Nickel.Register.write_outcome before (Native.impl_Replica__write before key value))) (Nickel.Register.write_installation before key value (Native.impl_Replica__write before key value))) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__write";
    Tactics.prune "Nickel.RegisterPublic.public_history";
    Tactics.prune "Nickel.Register.write_outcome";
    Tactics.prune "Nickel.Register.write_installation";
    Tactics.smt_sync' 1 1
  )

let counted_write_does_not_wrap (before: Native.t_Replica) (key: u64) (value: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) : Lemma (ensures forall(next: Native.t_Replica) (authored: Nickel.Register.fact). Native.impl_Replica__write before key value == (next, Result.Result_Ok (Option.Option_Some authored)) ==> v before.f_next_counter < Rust_primitives.Integers.maxint Rust_primitives.Integers.U64) =
  Nickel.Register.write_publication_on_every_return before key value;
  assert (forall(next: Native.t_Replica) (authored: Nickel.Register.fact). Native.impl_Replica__write before key value == (next, Result.Result_Ok (Option.Option_Some authored)) ==> v before.f_next_counter < Rust_primitives.Integers.maxint Rust_primitives.Integers.U64) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__write";
    Tactics.smt_sync' 1 1
  )