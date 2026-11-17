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

let new_establishes_public_history (writer: u64) (initial: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) : Lemma (ensures forall(r: Native.t_Replica). Native.impl_Replica__new writer initial == Result.Result_Ok r ==> public_history r) =
  new_establishes_history writer initial;
  Nickel.Register.new_has_unique_ids writer initial;
  assert (forall(r: Native.t_Replica). Native.impl_Replica__new writer initial == Result.Result_Ok r ==> public_history r) by (
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

let new_public_producer (writer: u64) (initial: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) : Lemma (ensures forall(r: Native.t_Replica). Native.impl_Replica__new writer initial == Result.Result_Ok r ==> Prims.l_and (Prims.l_and (public_history r) (r.f_writer == writer)) (v r.f_next_counter == 1)) =
  new_establishes_public_history writer initial;
  let each (r: Native.t_Replica) : Lemma (requires Native.impl_Replica__new writer initial == Result.Result_Ok r) (ensures Prims.l_and (r.f_writer == writer) (v r.f_next_counter == 1)) = () in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each);
  assert (forall(r: Native.t_Replica). Native.impl_Replica__new writer initial == Result.Result_Ok r ==> Prims.l_and (Prims.l_and (public_history r) (r.f_writer == writer)) (v r.f_next_counter == 1)) by (
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

let rec lookup_some_hits (#f: Type0) (#i: Type0) (facts: t_Slice f) (fact: f) (id: f -> i) (eq: i -> i -> bool) (same: f -> f -> bool) (at: usize{v at <= v (Core_models.Slice.impl__len facts)}) (b: bool) : Lemma (requires Nickel.EventClassifier.lookup facts fact id eq same at == Option.Option_Some b) (ensures exists(k: nat). Prims.l_and (Prims.l_and (Prims.l_and (v at <= k) (k < Seq.length facts)) (eq (id (Seq.index facts k)) (id fact) == true)) (same (Seq.index facts k) fact == b)) (decreases v (Core_models.Slice.impl__len facts) - v at) =
  if v at < v (Core_models.Slice.impl__len facts) then
    begin if eq (id (Rust_primitives.Slice.slice_index facts at)) (id fact) then
      begin assert (Prims.l_and (Prims.l_and (v at < Seq.length facts) (eq (id (Seq.index facts (v at))) (id fact) == true)) (same (Seq.index facts (v at)) fact == b)) end
    else
      begin lookup_some_hits facts fact id eq same (at +! mk_usize 1) b end end
  else
    begin () end

let rec lookup_single_hit (#f: Type0) (#i: Type0) (facts: t_Slice f) (fact: f) (id: f -> i) (eq: i -> i -> bool) (same: f -> f -> bool) (at: usize{v at <= v (Core_models.Slice.impl__len facts)}) (j: nat) : Lemma (requires ((forall(k: nat). Prims.l_and (k < Seq.length facts) (eq (id (Seq.index facts k)) (id fact) == true) ==> k == j) /\ Prims.l_and (Prims.l_and (v at <= j) (j < Seq.length facts)) (eq (id (Seq.index facts j)) (id fact) == true))) (ensures Nickel.EventClassifier.lookup facts fact id eq same at == Option.Option_Some (same (Seq.index facts j) fact)) (decreases v (Core_models.Slice.impl__len facts) - v at) =
  if v at < v (Core_models.Slice.impl__len facts) then
    begin if eq (id (Rust_primitives.Slice.slice_index facts at)) (id fact) then
      begin () end
    else
      begin lookup_single_hit facts fact id eq same (at +! mk_usize 1) j end end
  else
    begin () end

let stored_id_classifies (h: t_Slice Nickel.Register.fact) (offered: Nickel.Register.fact) (j: nat) : Lemma (requires (ids_unique h /\ Prims.l_and (j < Seq.length h) ((Seq.index h j).f_id == offered.f_id))) (ensures Nickel_crdt.Event_layer.classify h offered Native.v_OPS._1 == Option.Option_Some (Native.fact_equal (Seq.index h j) offered)) =
  register_ops_are_exact ();
  Nickel.EventClassifier.classification_is_exact h offered Native.v_OPS._1;
  lookup_single_hit h offered Native.v_OPS._1._1._1 Native.v_OPS._1._1._3 Native.v_OPS._1._1._6 (mk_usize 0) j;
  assert (Nickel_crdt.Event_layer.classify h offered Native.v_OPS._1 == Option.Option_Some (Native.fact_equal (Seq.index h j) offered)) by (
    Tactics.prune "Nickel_crdt.Event_layer.classify";
    Tactics.prune "Nickel.EventClassifier.lookup";
    Tactics.prune "Nickel.RegisterHistory.ids_unique";
    Tactics.prune "Nickel.EventClassifier.classification_is_exact";
    Tactics.prune "Nickel_crdt.Register.write_equal";
    Tactics.prune "Nickel_crdt.Register.bytes_equal";
    Tactics.prune "Nickel_crdt.Causal.event_equal";
    Tactics.smt_sync' 1 1
  )

let duplicate_classification_is_stored (h: t_Slice Nickel.Register.fact) (offered: Nickel.Register.fact) : Lemma (requires Nickel_crdt.Event_layer.classify h offered Native.v_OPS._1 == Option.Option_Some true) (ensures stored h offered) =
  register_ops_are_exact ();
  Nickel.EventClassifier.classification_is_exact h offered Native.v_OPS._1;
  assert (Nickel.EventClassifier.lookup h offered Native.v_OPS._1._1._1 Native.v_OPS._1._1._3 Native.v_OPS._1._1._6 (mk_usize 0) == Option.Option_Some true) by (
    Tactics.prune "Nickel_crdt.Event_layer.classify";
    Tactics.prune "Nickel.EventClassifier.lookup";
    Tactics.prune "Nickel.EventClassifier.classification_is_exact";
    Tactics.smt_sync' 1 1
  );
  lookup_some_hits h offered Native.v_OPS._1._1._1 Native.v_OPS._1._1._3 Native.v_OPS._1._1._6 (mk_usize 0) true;
  FStar.Classical.forall_intro_2 Nickel.Register.fact_equal_is_whole_value;
  assert (stored h offered) by (
    Tactics.prune "Nickel_crdt.Event_layer.classify";
    Tactics.prune "Nickel.EventClassifier.lookup";
    Tactics.prune "Nickel.EventClassifier.classification_is_exact";
    Tactics.smt_sync' 1 1
  )

let receive_by_plan (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (ensures Prims.l_and (Prims.l_and (Prims.l_and (Native.planned () before offered == Result.Result_Ok Option.Option_None ==> Native.impl_Replica__receive before offered == (before, Result.Result_Ok Native.Admission_Duplicate)) (forall(e: Native.t_Error). Native.planned () before offered == Result.Result_Err e ==> Native.impl_Replica__receive before offered == (before, Result.Result_Err e))) (forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Duplicate) ==> Prims.l_and (next == before) (Native.planned () before offered == Result.Result_Ok Option.Option_None))) (forall(next: Native.t_Replica) (e: Native.t_Error). Native.impl_Replica__receive before offered == (next, Result.Result_Err e) ==> next == before)) =
  Nickel.Register.receive_publication_is_exact before offered;
  match Native.planned () before offered with | Result.Result_Err _ -> begin assert (Prims.l_and (Prims.l_and (Prims.l_and (Native.planned () before offered == Result.Result_Ok Option.Option_None ==> Native.impl_Replica__receive before offered == (before, Result.Result_Ok Native.Admission_Duplicate)) (forall(e: Native.t_Error). Native.planned () before offered == Result.Result_Err e ==> Native.impl_Replica__receive before offered == (before, Result.Result_Err e))) (forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Duplicate) ==> Prims.l_and (next == before) (Native.planned () before offered == Result.Result_Ok Option.Option_None))) (forall(next: Native.t_Replica) (e: Native.t_Error). Native.impl_Replica__receive before offered == (next, Result.Result_Err e) ==> next == before)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.Register.receive_preserves_private";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel.Register.planned_adds_exact_fact";
    Tactics.prune "Nickel.Register.receive_publication_is_exact";
    Tactics.smt_sync' 1 1
  ) end | Result.Result_Ok option -> begin match option with | Option.Option_None -> begin assert (Prims.l_and (Prims.l_and (Prims.l_and (Native.planned () before offered == Result.Result_Ok Option.Option_None ==> Native.impl_Replica__receive before offered == (before, Result.Result_Ok Native.Admission_Duplicate)) (forall(e: Native.t_Error). Native.planned () before offered == Result.Result_Err e ==> Native.impl_Replica__receive before offered == (before, Result.Result_Err e))) (forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Duplicate) ==> Prims.l_and (next == before) (Native.planned () before offered == Result.Result_Ok Option.Option_None))) (forall(next: Native.t_Replica) (e: Native.t_Error). Native.impl_Replica__receive before offered == (next, Result.Result_Err e) ==> next == before)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.Register.receive_preserves_private";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel.Register.planned_adds_exact_fact";
    Tactics.prune "Nickel.Register.receive_publication_is_exact";
    Tactics.smt_sync' 1 1
  ) end | Option.Option_Some _ -> begin assert (Prims.l_and (Prims.l_and (Prims.l_and (Native.planned () before offered == Result.Result_Ok Option.Option_None ==> Native.impl_Replica__receive before offered == (before, Result.Result_Ok Native.Admission_Duplicate)) (forall(e: Native.t_Error). Native.planned () before offered == Result.Result_Err e ==> Native.impl_Replica__receive before offered == (before, Result.Result_Err e))) (forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Duplicate) ==> Prims.l_and (next == before) (Native.planned () before offered == Result.Result_Ok Option.Option_None))) (forall(next: Native.t_Replica) (e: Native.t_Error). Native.impl_Replica__receive before offered == (next, Result.Result_Err e) ==> next == before)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.Register.receive_preserves_private";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel.Register.planned_adds_exact_fact";
    Tactics.prune "Nickel.Register.receive_publication_is_exact";
    Tactics.smt_sync' 1 1
  ) end end

let plan_by_duplicate (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (ensures Prims.l_and (Prims.l_and (Native.duplicate () before offered == Result.Result_Ok true ==> Native.planned () before offered == Result.Result_Ok Option.Option_None) (forall(e: Native.t_Error). Native.duplicate () before offered == Result.Result_Err e ==> Native.planned () before offered == Result.Result_Err e)) (Native.planned () before offered == Result.Result_Ok Option.Option_None ==> Native.duplicate () before offered == Result.Result_Ok true)) =
  Nickel.EventShell.planning_is_exact before offered () Native.duplicate Native.validate Native.prepare Native.execute;
  assert (Prims.l_and (Prims.l_and (Native.duplicate () before offered == Result.Result_Ok true ==> Native.planned () before offered == Result.Result_Ok Option.Option_None) (forall(e: Native.t_Error). Native.duplicate () before offered == Result.Result_Err e ==> Native.planned () before offered == Result.Result_Err e)) (Native.planned () before offered == Result.Result_Ok Option.Option_None ==> Native.duplicate () before offered == Result.Result_Ok true)) by (
    Tactics.prune "Nickel_crdt.Event_shell.plan";
    Tactics.prune "Nickel_crdt.Event_layer.classify";
    Tactics.prune "Nickel_crdt.Event_layer.validate_event";
    Tactics.prune "Nickel_crdt.Event_layer.push";
    Tactics.prune "Nickel_crdt.Event_layer.canonical";
    Tactics.prune "Nickel.Register.receive_preserves_private";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel.Register.planned_adds_exact_fact";
    Tactics.prune "Nickel.EventShell.planning_is_exact";
    Tactics.smt_sync' 1 1
  )

let duplicate_by_classify (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (ensures Prims.l_and (Prims.l_and (Nickel_crdt.Event_layer.classify (Alloc.Vec.impl_1__as_slice before.f_facts) offered Native.v_OPS._1 == Option.Option_Some true ==> Native.duplicate () before offered == Result.Result_Ok true) (Nickel_crdt.Event_layer.classify (Alloc.Vec.impl_1__as_slice before.f_facts) offered Native.v_OPS._1 == Option.Option_Some false ==> Native.duplicate () before offered == Result.Result_Err Native.Error_Conflict)) (Native.duplicate () before offered == Result.Result_Ok true ==> Nickel_crdt.Event_layer.classify (Alloc.Vec.impl_1__as_slice before.f_facts) offered Native.v_OPS._1 == Option.Option_Some true)) =
  assert (Prims.l_and (Prims.l_and (Nickel_crdt.Event_layer.classify (Alloc.Vec.impl_1__as_slice before.f_facts) offered Native.v_OPS._1 == Option.Option_Some true ==> Native.duplicate () before offered == Result.Result_Ok true) (Nickel_crdt.Event_layer.classify (Alloc.Vec.impl_1__as_slice before.f_facts) offered Native.v_OPS._1 == Option.Option_Some false ==> Native.duplicate () before offered == Result.Result_Err Native.Error_Conflict)) (Native.duplicate () before offered == Result.Result_Ok true ==> Nickel_crdt.Event_layer.classify (Alloc.Vec.impl_1__as_slice before.f_facts) offered Native.v_OPS._1 == Option.Option_Some true)) by (
    Tactics.prune "Nickel_crdt.Event_layer.classify";
    Tactics.prune "Nickel.Register.receive_preserves_private";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel.Register.planned_adds_exact_fact";
    Tactics.smt_sync' 1 1
  )

let receive_duplicate_meaning (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (requires public_history before) (ensures Prims.l_and (Prims.l_and (Prims.l_and (stored (Alloc.Vec.impl_1__as_slice before.f_facts) offered ==> Native.impl_Replica__receive before offered == (before, Result.Result_Ok Native.Admission_Duplicate)) ((exists(g: Nickel.Register.fact). Prims.l_and (Prims.l_and (stored (Alloc.Vec.impl_1__as_slice before.f_facts) g) (g.f_id == offered.f_id)) (g =!= offered)) ==> Native.impl_Replica__receive before offered == (before, Result.Result_Err Native.Error_Conflict))) (forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Duplicate) ==> Prims.l_and (next == before) (stored (Alloc.Vec.impl_1__as_slice before.f_facts) offered))) (forall(next: Native.t_Replica) (e: Native.t_Error). Native.impl_Replica__receive before offered == (next, Result.Result_Err e) ==> next == before)) =
  let h = Alloc.Vec.impl_1__as_slice before.f_facts in
  public_single_value_premises before;
  receive_by_plan before offered;
  plan_by_duplicate before offered;
  duplicate_by_classify before offered;
  let hit (g: Nickel.Register.fact) (j: nat) : Lemma (requires Prims.l_and (Prims.l_and (j < Seq.length h) (Seq.index h j == g)) (g.f_id == offered.f_id)) (ensures Nickel_crdt.Event_layer.classify (Alloc.Vec.impl_1__as_slice before.f_facts) offered Native.v_OPS._1 == Option.Option_Some (Native.fact_equal g offered)) = stored_id_classifies h offered j in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 hit);
  FStar.Classical.move_requires (duplicate_classification_is_stored h) offered;
  FStar.Classical.forall_intro_2 Nickel.Register.fact_equal_is_whole_value;
  let conflict (g: Nickel.Register.fact) (j: nat) : Lemma (requires Prims.l_and (Prims.l_and (Prims.l_and (j < Seq.length h) (Seq.index h j == g)) (g.f_id == offered.f_id)) (g =!= offered)) (ensures Native.impl_Replica__receive before offered == (before, Result.Result_Err Native.Error_Conflict)) =
    hit g j;
    assert (Nickel_crdt.Event_layer.classify h offered Native.v_OPS._1 == Option.Option_Some false);
    assert (Native.duplicate () before offered == Result.Result_Err Native.Error_Conflict) by (
      Tactics.prune "Nickel_crdt.Event_layer.classify";
      Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
      Tactics.prune "Nickel_crdt.Register.planned";
      Tactics.smt_sync' 1 1
    );
    assert (Native.planned () before offered == Result.Result_Err Native.Error_Conflict) by (
      Tactics.prune "Nickel_crdt.Register.duplicate";
      Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
      Tactics.prune "Nickel_crdt.Register.planned";
      Tactics.smt_sync' 1 1
    );
    assert (Native.impl_Replica__receive before offered == (before, Result.Result_Err Native.Error_Conflict)) by (
      Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
      Tactics.prune "Nickel_crdt.Register.planned";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 conflict);
  let identical (j: nat) : Lemma (requires Prims.l_and (j < Seq.length h) (Seq.index h j == offered)) (ensures Native.impl_Replica__receive before offered == (before, Result.Result_Ok Native.Admission_Duplicate)) =
    hit offered j;
    Nickel.Register.fact_equal_is_whole_value offered offered;
    assert (Nickel_crdt.Event_layer.classify h offered Native.v_OPS._1 == Option.Option_Some true);
    assert (Native.duplicate () before offered == Result.Result_Ok true) by (
      Tactics.prune "Nickel_crdt.Event_layer.classify";
      Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
      Tactics.prune "Nickel_crdt.Register.planned";
      Tactics.smt_sync' 1 1
    );
    assert (Native.planned () before offered == Result.Result_Ok Option.Option_None) by (
      Tactics.prune "Nickel_crdt.Register.duplicate";
      Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
      Tactics.prune "Nickel_crdt.Register.planned";
      Tactics.smt_sync' 1 1
    );
    assert (Native.impl_Replica__receive before offered == (before, Result.Result_Ok Native.Admission_Duplicate)) by (
      Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
      Tactics.prune "Nickel_crdt.Register.planned";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro (FStar.Classical.move_requires identical);
  assert (stored (Alloc.Vec.impl_1__as_slice before.f_facts) offered ==> Native.impl_Replica__receive before offered == (before, Result.Result_Ok Native.Admission_Duplicate)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel_crdt.Register.duplicate";
    Tactics.prune "Nickel_crdt.Event_layer.classify";
    Tactics.prune "Nickel.RegisterPublic.public_history";
    Tactics.prune "Nickel.RegisterHistory.stream_steps";
    Tactics.prune "Nickel.RegisterHistory.ids_unique";
    Tactics.prune "Nickel.RegisterHistory.counters_positive";
    Tactics.prune "Nickel.Register.receive_preserves_private";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel.Register.planned_adds_exact_fact";
    Tactics.smt_sync' 1 1
  );
  assert ((exists(g: Nickel.Register.fact). Prims.l_and (Prims.l_and (stored (Alloc.Vec.impl_1__as_slice before.f_facts) g) (g.f_id == offered.f_id)) (g =!= offered)) ==> Native.impl_Replica__receive before offered == (before, Result.Result_Err Native.Error_Conflict)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel_crdt.Register.duplicate";
    Tactics.prune "Nickel_crdt.Event_layer.classify";
    Tactics.prune "Nickel.RegisterPublic.public_history";
    Tactics.prune "Nickel.RegisterHistory.stream_steps";
    Tactics.prune "Nickel.RegisterHistory.ids_unique";
    Tactics.prune "Nickel.RegisterHistory.counters_positive";
    Tactics.prune "Nickel.Register.receive_preserves_private";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel.Register.planned_adds_exact_fact";
    Tactics.smt_sync' 1 1
  );
  assert (forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Duplicate) ==> Prims.l_and (next == before) (stored (Alloc.Vec.impl_1__as_slice before.f_facts) offered)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel_crdt.Register.duplicate";
    Tactics.prune "Nickel_crdt.Event_layer.classify";
    Tactics.prune "Nickel.RegisterPublic.public_history";
    Tactics.prune "Nickel.RegisterHistory.stream_steps";
    Tactics.prune "Nickel.RegisterHistory.ids_unique";
    Tactics.prune "Nickel.RegisterHistory.counters_positive";
    Tactics.prune "Nickel.Register.receive_preserves_private";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel.Register.planned_adds_exact_fact";
    Tactics.smt_sync' 1 1
  );
  assert (forall(next: Native.t_Replica) (e: Native.t_Error). Native.impl_Replica__receive before offered == (next, Result.Result_Err e) ==> next == before) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel_crdt.Register.duplicate";
    Tactics.prune "Nickel_crdt.Event_layer.classify";
    Tactics.prune "Nickel.RegisterPublic.public_history";
    Tactics.prune "Nickel.RegisterHistory.stream_steps";
    Tactics.prune "Nickel.RegisterHistory.ids_unique";
    Tactics.prune "Nickel.RegisterHistory.counters_positive";
    Tactics.prune "Nickel.Register.receive_preserves_private";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel.Register.planned_adds_exact_fact";
    Tactics.smt_sync' 1 1
  );
  ()

let valid_offer (h: Seq.seq Nickel.Register.fact) (initial: t_Slice u8) (f: Nickel.Register.fact) : Type0 =
  Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (forall(p: Envelope.t_Id). Nickel.RegisterPast.member (Alloc.Vec.impl_1__as_slice f.f_after) p ==> (exists(g: Nickel.Register.fact). Prims.l_and (stored h g) (g.f_id == p))) (observation_ok h initial f)) (clock_exact_in h (anc_of h f) f.f_payload.f_lamport)) (Prims.l_not (Nickel.Register.bytes_same (Alloc.Vec.impl_1__as_slice f.f_payload.f_value) (Alloc.Vec.impl_1__as_slice f.f_payload.f_observed)))) (stream_ok_in h (anc_of h f) f)

let receive_added_meaning (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (requires public_history before) (ensures forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> Prims.l_and (Prims.l_and (Prims.l_and (fresh_id before offered) (valid_offer (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice before.f_initial) offered)) (extends_by (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice next.f_facts) offered)) (public_history next)) =
  receive_added_offer_is_fresh before offered;
  receive_added_parents_stored before offered;
  receive_added_freezes_id_read before offered;
  FStar.Classical.move_requires (id_frozen_gives_observation before) offered;
  receive_added_basis_is_exact_ancestry before offered;
  FStar.Classical.move_requires (exact_basis_gives_clock_and_value before) offered;
  receive_added_offer_stream before offered;
  Nickel.Register.receive_added_retains_exact_facts before offered;
  receive_preserves_public_history before offered;
  assert (forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> Prims.l_and (Prims.l_and (Prims.l_and (fresh_id before offered) (valid_offer (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice before.f_initial) offered)) (extends_by (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice next.f_facts) offered)) (public_history next)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.RegisterHistory.fresh_id";
    Tactics.prune "Nickel.RegisterHistory.observation_ok";
    Tactics.prune "Nickel.RegisterValid.clock_exact_in";
    Tactics.prune "Nickel.RegisterValid.stream_ok_in";
    Tactics.prune "Nickel.RegisterHistory.id_frozen_admission";
    Tactics.prune "Nickel.RegisterHistory.exact_selected_basis";
    Tactics.prune "Nickel.RegisterHistory.stored_unique";
    Tactics.prune "Nickel.RegisterHistory.id_clocks_increase";
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

let receive_added_meaning_at (before: Native.t_Replica) (offered: Nickel.Register.fact) (next: Native.t_Replica) : Lemma (requires (public_history before /\ Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added))) (ensures Prims.l_and (Prims.l_and (Prims.l_and (fresh_id before offered) (valid_offer (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice before.f_initial) offered)) (extends_by (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice next.f_facts) offered)) (public_history next)) =
  receive_added_meaning before offered;
  assert (Prims.l_and (Prims.l_and (Prims.l_and (fresh_id before offered) (valid_offer (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice before.f_initial) offered)) (extends_by (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice next.f_facts) offered)) (public_history next)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel.RegisterHistory.fresh_id";
    Tactics.prune "Nickel.RegisterPublic.valid_offer";
    Tactics.prune "Nickel.RegisterPublic.public_history";
    Tactics.prune "Nickel.RegisterHistory.extends_by";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.Register.receive_preserves_private";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel.Register.planned_adds_exact_fact";
    Tactics.smt_sync' 1 1
  )

let planned_some_is_added (before: Native.t_Replica) (offered: Nickel.Register.fact) (candidate: Native.t_Replica) : Lemma (requires Native.planned () before offered == Result.Result_Ok (Option.Option_Some candidate)) (ensures Native.impl_Replica__receive before offered == (candidate, Result.Result_Ok Native.Admission_Added)) =
  Nickel.Register.receive_publication_is_exact before offered;
  assert (Native.impl_Replica__receive before offered == (candidate, Result.Result_Ok Native.Admission_Added)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.Register.receive_publication_is_exact";
    Tactics.prune "Nickel.Register.receive_preserves_private";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel.Register.planned_adds_exact_fact";
    Tactics.smt_sync' 1 1
  )

let write_counted_is_added_receive (before: Native.t_Replica) (key: u64) (value: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) (next: Native.t_Replica) (authored: Nickel.Register.fact) : Lemma (requires Native.impl_Replica__write before key value == (next, Result.Result_Ok (Option.Option_Some authored))) (ensures Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Native.impl_Replica__receive before authored == ((Native.impl_Replica__receive before authored)._1, Result.Result_Ok Native.Admission_Added)) ((Native.impl_Replica__receive before authored)._1.f_facts == next.f_facts)) (authored.f_id.f_peer == before.f_writer)) (authored.f_id.f_counter == before.f_next_counter)) (authored.f_payload.f_key == key)) (authored.f_payload.f_value == value)) (authored.f_payload.f_observed == Native.impl_Replica__read before key)) =
  Nickel.Register.write_installs_successful_candidate before key value;
  let via (candidate: Native.t_Replica) : Lemma (requires (Native.planned () before authored == Result.Result_Ok (Option.Option_Some candidate) /\ Nickel.Register.installed_candidate candidate next)) (ensures Prims.l_and (Native.impl_Replica__receive before authored == ((Native.impl_Replica__receive before authored)._1, Result.Result_Ok Native.Admission_Added)) ((Native.impl_Replica__receive before authored)._1.f_facts == next.f_facts)) = planned_some_is_added before authored candidate in
  FStar.Classical.forall_intro (FStar.Classical.move_requires via);
  assert (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Native.impl_Replica__receive before authored == ((Native.impl_Replica__receive before authored)._1, Result.Result_Ok Native.Admission_Added)) ((Native.impl_Replica__receive before authored)._1.f_facts == next.f_facts)) (authored.f_id.f_peer == before.f_writer)) (authored.f_id.f_counter == before.f_next_counter)) (authored.f_payload.f_key == key)) (authored.f_payload.f_value == value)) (authored.f_payload.f_observed == Native.impl_Replica__read before key)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__write";
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel_crdt.Register.impl_Replica__read";
    Tactics.prune "Nickel_crdt.Event_layer.frontier";
    Tactics.prune "Nickel_crdt.Register.next_lamport";
    Tactics.prune "Nickel.Register.receive_preserves_private";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel.Register.planned_adds_exact_fact";
    Tactics.smt_sync' 1 1
  )

let write_counted_meaning (before: Native.t_Replica) (key: u64) (value: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) : Lemma (requires public_history before) (ensures forall(next: Native.t_Replica) (authored: Nickel.Register.fact). Native.impl_Replica__write before key value == (next, Result.Result_Ok (Option.Option_Some authored)) ==> Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (authored.f_id.f_peer == before.f_writer) (authored.f_id.f_counter == before.f_next_counter)) (authored.f_payload.f_key == key)) (authored.f_payload.f_value == value)) (causal_read (Alloc.Vec.impl_1__as_slice before.f_facts) key (Alloc.Vec.impl_1__as_slice before.f_initial) (Alloc.Vec.impl_1__as_slice authored.f_payload.f_observed))) (fresh_id before authored)) (valid_offer (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice before.f_initial) authored)) (extends_by (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice next.f_facts) authored)) =
  public_read_is_the_causal_read before key (Alloc.Vec.impl_1__as_slice (Native.impl_Replica__read before key));
  let counted (next: Native.t_Replica) (authored: Nickel.Register.fact) : Lemma (requires Native.impl_Replica__write before key value == (next, Result.Result_Ok (Option.Option_Some authored))) (ensures Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (authored.f_id.f_peer == before.f_writer) (authored.f_id.f_counter == before.f_next_counter)) (authored.f_payload.f_key == key)) (authored.f_payload.f_value == value)) (causal_read (Alloc.Vec.impl_1__as_slice before.f_facts) key (Alloc.Vec.impl_1__as_slice before.f_initial) (Alloc.Vec.impl_1__as_slice authored.f_payload.f_observed))) (fresh_id before authored)) (valid_offer (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice before.f_initial) authored)) (extends_by (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice next.f_facts) authored)) =
    write_counted_is_added_receive before key value next authored;
    receive_added_meaning_at before authored (Native.impl_Replica__receive before authored)._1;
    assert (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (authored.f_id.f_peer == before.f_writer) (authored.f_id.f_counter == before.f_next_counter)) (authored.f_payload.f_key == key)) (authored.f_payload.f_value == value)) (causal_read (Alloc.Vec.impl_1__as_slice before.f_facts) key (Alloc.Vec.impl_1__as_slice before.f_initial) (Alloc.Vec.impl_1__as_slice authored.f_payload.f_observed))) (fresh_id before authored)) (valid_offer (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice before.f_initial) authored)) (extends_by (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice next.f_facts) authored)) by (
      Tactics.prune "Nickel_crdt.Register.impl_Replica__write";
      Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
      Tactics.prune "Nickel_crdt.Register.planned";
      Tactics.prune "Nickel_crdt.Register.impl_Replica__read";
      Tactics.prune "Nickel_crdt.Event_layer.frontier";
      Tactics.prune "Nickel_crdt.Register.next_lamport";
      Tactics.prune "Nickel.RegisterHistory.fresh_id";
      Tactics.prune "Nickel.RegisterPublic.valid_offer";
      Tactics.prune "Nickel.RegisterHistory.causal_read";
      Tactics.prune "Nickel.RegisterPublic.public_history";
      Tactics.prune "Nickel.Register.write_installation";
      Tactics.prune "Nickel.Register.receive_publication_is_exact";
      Tactics.prune "Nickel.Register.receive_preserves_private";
      Tactics.prune "Nickel.Register.planned_preserves_private";
      Tactics.prune "Nickel.Register.planned_checks_payload";
      Tactics.prune "Nickel.Register.planned_adds_exact_fact";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 counted);
  assert (forall(next: Native.t_Replica) (authored: Nickel.Register.fact). Native.impl_Replica__write before key value == (next, Result.Result_Ok (Option.Option_Some authored)) ==> Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (authored.f_id.f_peer == before.f_writer) (authored.f_id.f_counter == before.f_next_counter)) (authored.f_payload.f_key == key)) (authored.f_payload.f_value == value)) (causal_read (Alloc.Vec.impl_1__as_slice before.f_facts) key (Alloc.Vec.impl_1__as_slice before.f_initial) (Alloc.Vec.impl_1__as_slice authored.f_payload.f_observed))) (fresh_id before authored)) (valid_offer (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice before.f_initial) authored)) (extends_by (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice next.f_facts) authored)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__write";
    Tactics.prune "Nickel.RegisterHistory.fresh_id";
    Tactics.prune "Nickel.RegisterPublic.valid_offer";
    Tactics.prune "Nickel.RegisterHistory.causal_read";
    Tactics.prune "Nickel.RegisterPublic.public_history";
    Tactics.prune "Nickel.Register.receive_preserves_private";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel.Register.planned_adds_exact_fact";
    Tactics.smt_sync' 1 1
  )

let noedit_write_is_equal_value (before: Native.t_Replica) (key: u64) (value: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) : Lemma (ensures forall(next: Native.t_Replica). Native.impl_Replica__write before key value == (next, Result.Result_Ok Option.Option_None) ==> Prims.l_and (next == before) (Nickel.Register.bytes_same (Alloc.Vec.impl_1__as_slice value) (Alloc.Vec.impl_1__as_slice (Native.impl_Replica__read before key)))) =
  Nickel.Register.bytes_equal_exact (Alloc.Vec.impl_1__as_slice value) (Alloc.Vec.impl_1__as_slice (Native.impl_Replica__read before key));
  match Core_models.Num.impl_u64__checked_add before.f_next_counter (mk_u64 1) with | Option.Option_None -> begin assert (forall(next: Native.t_Replica). Native.impl_Replica__write before key value == (next, Result.Result_Ok Option.Option_None) ==> Prims.l_and (next == before) (Nickel.Register.bytes_same (Alloc.Vec.impl_1__as_slice value) (Alloc.Vec.impl_1__as_slice (Native.impl_Replica__read before key)))) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Event_layer.frontier";
    Tactics.prune "Nickel_crdt.Register.next_lamport";
    Tactics.prune "Nickel_crdt.Register.bytes_equal";
    Tactics.prune "Nickel_crdt.Register.impl_Replica__read";
    Tactics.prune "Nickel.Register.bytes_same";
    Tactics.prune "Nickel.Register.bytes_equal_exact";
    Tactics.smt_sync' 1 1
  ) end | Option.Option_Some next -> begin match Nickel_crdt.Event_layer.frontier (Alloc.Vec.impl_1__as_slice before.f_facts) Native.v_OPS._1 with | Result.Result_Err _ -> begin assert (forall(next: Native.t_Replica). Native.impl_Replica__write before key value == (next, Result.Result_Ok Option.Option_None) ==> Prims.l_and (next == before) (Nickel.Register.bytes_same (Alloc.Vec.impl_1__as_slice value) (Alloc.Vec.impl_1__as_slice (Native.impl_Replica__read before key)))) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Event_layer.frontier";
    Tactics.prune "Nickel_crdt.Register.next_lamport";
    Tactics.prune "Nickel_crdt.Register.bytes_equal";
    Tactics.prune "Nickel_crdt.Register.impl_Replica__read";
    Tactics.prune "Nickel.Register.bytes_same";
    Tactics.prune "Nickel.Register.bytes_equal_exact";
    Tactics.smt_sync' 1 1
  ) end | Result.Result_Ok parents -> begin match Native.next_lamport (Alloc.Vec.impl_1__as_slice before.f_facts) with | Result.Result_Err _ -> begin assert (forall(next: Native.t_Replica). Native.impl_Replica__write before key value == (next, Result.Result_Ok Option.Option_None) ==> Prims.l_and (next == before) (Nickel.Register.bytes_same (Alloc.Vec.impl_1__as_slice value) (Alloc.Vec.impl_1__as_slice (Native.impl_Replica__read before key)))) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Event_layer.frontier";
    Tactics.prune "Nickel_crdt.Register.next_lamport";
    Tactics.prune "Nickel_crdt.Register.bytes_equal";
    Tactics.prune "Nickel_crdt.Register.impl_Replica__read";
    Tactics.prune "Nickel.Register.bytes_same";
    Tactics.prune "Nickel.Register.bytes_equal_exact";
    Tactics.smt_sync' 1 1
  ) end | Result.Result_Ok clock -> begin assert (forall(next: Native.t_Replica). Native.impl_Replica__write before key value == (next, Result.Result_Ok Option.Option_None) ==> Prims.l_and (next == before) (Nickel.Register.bytes_same (Alloc.Vec.impl_1__as_slice value) (Alloc.Vec.impl_1__as_slice (Native.impl_Replica__read before key)))) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Event_layer.frontier";
    Tactics.prune "Nickel_crdt.Register.next_lamport";
    Tactics.prune "Nickel_crdt.Register.bytes_equal";
    Tactics.prune "Nickel_crdt.Register.impl_Replica__read";
    Tactics.prune "Nickel.Register.bytes_same";
    Tactics.prune "Nickel.Register.bytes_equal_exact";
    Tactics.smt_sync' 1 1
  ) end end end

let bytes_same_trans (a: t_Slice u8) (b: t_Slice u8) (c: t_Slice u8) : Lemma (requires Prims.l_and (Nickel.Register.bytes_same a b) (Nickel.Register.bytes_same b c)) (ensures Nickel.Register.bytes_same a c) =
  ()

let write_noedit_meaning (before: Native.t_Replica) (key: u64) (value: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) : Lemma (requires public_history before) (ensures forall(next: Native.t_Replica) (x: t_Slice u8). Prims.l_and (Native.impl_Replica__write before key value == (next, Result.Result_Ok Option.Option_None)) (causal_read (Alloc.Vec.impl_1__as_slice before.f_facts) key (Alloc.Vec.impl_1__as_slice before.f_initial) x) ==> Prims.l_and (next == before) (Nickel.Register.bytes_same (Alloc.Vec.impl_1__as_slice value) x)) =
  noedit_write_is_equal_value before key value;
  let each (next: Native.t_Replica) (x: t_Slice u8) : Lemma (requires (Native.impl_Replica__write before key value == (next, Result.Result_Ok Option.Option_None) /\ causal_read (Alloc.Vec.impl_1__as_slice before.f_facts) key (Alloc.Vec.impl_1__as_slice before.f_initial) x)) (ensures Prims.l_and (next == before) (Nickel.Register.bytes_same (Alloc.Vec.impl_1__as_slice value) x)) =
    public_read_is_the_causal_read before key x;
    assert (Prims.l_and (Nickel.Register.bytes_same (Alloc.Vec.impl_1__as_slice value) (Alloc.Vec.impl_1__as_slice (Native.impl_Replica__read before key))) (Nickel.Register.bytes_same (Alloc.Vec.impl_1__as_slice (Native.impl_Replica__read before key)) x)) by (
      Tactics.prune "Nickel_crdt.Register.impl_Replica__write";
      Tactics.prune "Nickel_crdt.Register.impl_Replica__read";
      Tactics.prune "Nickel_crdt.Register.read_history";
      Tactics.prune "Nickel_crdt.Register.winner";
      Tactics.prune "Nickel.Register.bytes_same";
      Tactics.prune "Nickel.RegisterHistory.causal_read";
      Tactics.prune "Nickel.RegisterPublic.public_history";
      Tactics.smt_sync' 1 1
    );
    bytes_same_trans (Alloc.Vec.impl_1__as_slice value) (Alloc.Vec.impl_1__as_slice (Native.impl_Replica__read before key)) x;
    assert (Prims.l_and (next == before) (Nickel.Register.bytes_same (Alloc.Vec.impl_1__as_slice value) x)) by (
      Tactics.prune "Nickel_crdt.Register.impl_Replica__write";
      Tactics.prune "Nickel_crdt.Register.impl_Replica__read";
      Tactics.prune "Nickel.Register.bytes_same";
      Tactics.prune "Nickel.RegisterHistory.causal_read";
      Tactics.prune "Nickel.RegisterPublic.public_history";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each);
  assert (forall(next: Native.t_Replica) (x: t_Slice u8). Prims.l_and (Native.impl_Replica__write before key value == (next, Result.Result_Ok Option.Option_None)) (causal_read (Alloc.Vec.impl_1__as_slice before.f_facts) key (Alloc.Vec.impl_1__as_slice before.f_initial) x) ==> Prims.l_and (next == before) (Nickel.Register.bytes_same (Alloc.Vec.impl_1__as_slice value) x)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__write";
    Tactics.prune "Nickel.Register.bytes_same";
    Tactics.prune "Nickel.RegisterHistory.causal_read";
    Tactics.prune "Nickel.RegisterPublic.public_history";
    Tactics.smt_sync' 1 1
  )