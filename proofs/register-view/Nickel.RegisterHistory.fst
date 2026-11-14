(* Latte generated F* view *)
module Nickel.RegisterHistory

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

let parent_edge (facts: t_Slice Nickel.Register.fact) (newer: nat) (older: nat) : Type0 =
  Prims.l_and (Prims.l_and (newer < Seq.length facts) (older < Seq.length facts)) (exists(k: nat). Prims.l_and (k < Seq.length (Alloc.Vec.impl_1__as_slice (Seq.index facts newer).f_after)) (Seq.index (Alloc.Vec.impl_1__as_slice (Seq.index facts newer).f_after) k == (Seq.index facts older).f_id))

let rec strict_ancestor_path (facts: t_Slice Nickel.Register.fact) (newer: nat) (steps: Prims.list nat) (older: nat) : Tot Type0 (decreases steps) =
  match steps with | Prims.Nil -> begin parent_edge facts newer older end | Prims.Cons next rest -> begin Prims.l_and (parent_edge facts newer next) (strict_ancestor_path facts next rest older) end

let clock_below (facts: t_Slice Nickel.Register.fact) (older: nat) (newer: nat) : Type0 =
  Prims.l_and (Prims.l_and (older < Seq.length facts) (newer < Seq.length facts)) (v (Seq.index facts older).f_payload.f_lamport < v (Seq.index facts newer).f_payload.f_lamport)

let clocks_increase (facts: t_Slice Nickel.Register.fact) : Type0 =
  forall(newer: nat) (older: nat). parent_edge facts newer older ==> clock_below facts older newer

let rec ancestor_clock_is_smaller (facts: t_Slice Nickel.Register.fact) (newer: nat) (steps: Prims.list nat) (older: nat) : Lemma (requires (clocks_increase facts /\ strict_ancestor_path facts newer steps older)) (ensures clock_below facts older newer) (decreases steps) =
  match steps with | Prims.Nil -> begin () end | Prims.Cons next rest -> begin ancestor_clock_is_smaller facts next rest older end

let causal_maximal (facts: t_Slice Nickel.Register.fact) (key: u64) (i: nat) : Type0 =
  Prims.l_and (Prims.l_and (i < Seq.length facts) ((Seq.index facts i).f_payload.f_key == key)) (Prims.l_not (exists(j: nat) (steps: Prims.list nat). Prims.l_and (Prims.l_and (j < Seq.length facts) ((Seq.index facts j).f_payload.f_key == key)) (strict_ancestor_path facts j steps i)))

let causal_read (facts: t_Slice Nickel.Register.fact) (key: u64) (initial: t_Slice u8) (value: t_Slice u8) : Type0 =
  Prims.l_or (Prims.l_and (forall(j: nat). j < Seq.length facts ==> (Seq.index facts j).f_payload.f_key =!= key) (Nickel.Register.bytes_same value initial)) (exists(i: nat). Prims.l_and (Prims.l_and (causal_maximal facts key i) (Nickel.Register.bytes_same value (Alloc.Vec.impl_1__as_slice (Seq.index facts i).f_payload.f_value))) (forall(j: nat). causal_maximal facts key j ==> Prims.l_not (Nickel.Register.higher (Seq.index facts j) (Seq.index facts i))))

let priority_maximum_is_causal_maximum (facts: t_Slice Nickel.Register.fact) (key: u64) (i: nat) : Lemma (requires (clocks_increase facts /\ Prims.l_and (Prims.l_and (i < Seq.length facts) ((Seq.index facts i).f_payload.f_key == key)) (forall(j: nat). Prims.l_and (j < Seq.length facts) ((Seq.index facts j).f_payload.f_key == key) ==> Prims.l_not (Nickel.Register.higher (Seq.index facts j) (Seq.index facts i))))) (ensures causal_maximal facts key i) =
  let dominated_is_impossible (j: nat) (steps: Prims.list nat) : Lemma (requires (Prims.l_and (j < Seq.length facts) ((Seq.index facts j).f_payload.f_key == key) /\ strict_ancestor_path facts j steps i)) (ensures Prims.l_False) = ancestor_clock_is_smaller facts j steps i in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 dominated_is_impossible)

let read_history_is_causal_read (facts: t_Slice Nickel.Register.fact) (initial: t_Slice u8) (key: u64) : Lemma (requires clocks_increase facts) (ensures causal_read facts key initial (Alloc.Vec.impl_1__as_slice (Native.read_history facts initial key))) =
  Nickel.Register.read_history_selects_maximum facts initial key;
  FStar.Classical.forall_intro (FStar.Classical.move_requires (priority_maximum_is_causal_maximum facts key))

let ids_unique (facts: t_Slice Nickel.Register.fact) : Type0 =
  forall(i: nat) (j: nat). Prims.l_and (Prims.l_and (i < Seq.length facts) (j < Seq.length facts)) ((Seq.index facts i).f_id == (Seq.index facts j).f_id) ==> i == j

let counters_positive (facts: t_Slice Nickel.Register.fact) : Type0 =
  forall(i: nat). i < Seq.length facts ==> v (Seq.index facts i).f_id.f_counter >= 1

let predecessor_of (facts: t_Slice Nickel.Register.fact) (later: nat) (earlier: nat) : Type0 =
  Prims.l_and (Prims.l_and (Prims.l_and (later < Seq.length facts) (earlier < Seq.length facts)) ((Seq.index facts earlier).f_id.f_peer == (Seq.index facts later).f_id.f_peer)) (v (Seq.index facts earlier).f_id.f_counter + 1 == v (Seq.index facts later).f_id.f_counter)

let streams_chained (facts: t_Slice Nickel.Register.fact) : Type0 =
  forall(i: nat). Prims.l_and (i < Seq.length facts) (v (Seq.index facts i).f_id.f_counter > 1) ==> (exists(j: nat) (steps: Prims.list nat). Prims.l_and (predecessor_of facts i j) (strict_ancestor_path facts i steps j))

let stream_steps (facts: t_Slice Nickel.Register.fact) : Type0 =
  forall(i: nat). Prims.l_and (i < Seq.length facts) (v (Seq.index facts i).f_id.f_counter > 1) ==> (exists(j: nat). Prims.l_and (predecessor_of facts i j) (clock_below facts j i))

let chained_streams_step_clocks (facts: t_Slice Nickel.Register.fact) : Lemma (requires Prims.l_and (clocks_increase facts) (streams_chained facts)) (ensures stream_steps facts) =
  let each (i: nat) (j: nat) (steps: Prims.list nat) : Lemma (requires strict_ancestor_path facts i steps j) (ensures clock_below facts j i) = ancestor_clock_is_smaller facts i steps j in
  FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 each)

let same_stream_order (facts: t_Slice Nickel.Register.fact) (low: nat) (high: nat) : Type0 =
  Prims.l_and (Prims.l_and (Prims.l_and (low < Seq.length facts) (high < Seq.length facts)) ((Seq.index facts low).f_id.f_peer == (Seq.index facts high).f_id.f_peer)) (v (Seq.index facts low).f_id.f_counter < v (Seq.index facts high).f_id.f_counter)

let same_fields_same_id (facts: t_Slice Nickel.Register.fact) (a: nat) (b: nat) : Lemma (requires (Prims.l_and (a < Seq.length facts) (b < Seq.length facts) /\ (Seq.index facts a).f_id.f_peer == (Seq.index facts b).f_id.f_peer /\ (Seq.index facts a).f_id.f_counter == (Seq.index facts b).f_id.f_counter)) (ensures (Seq.index facts a).f_id == (Seq.index facts b).f_id) =
  ()

let later_stream_fact_has_step (facts: t_Slice Nickel.Register.fact) (low: nat) (high: nat) : Lemma (requires (Prims.l_and (stream_steps facts) (counters_positive facts) /\ same_stream_order facts low high)) (ensures exists(j: nat). Prims.l_and (predecessor_of facts high j) (clock_below facts j high)) =
  ()

let stream_step_composes (facts: t_Slice Nickel.Register.fact) (low: nat) (j: nat) (high: nat) : Lemma (requires (same_stream_order facts low high /\ Prims.l_and (predecessor_of facts high j) (clock_below facts j high) /\ Prims.l_or (clock_below facts low j) (j == low))) (ensures clock_below facts low high) =
  ()

let rec stream_clock_increases (facts: t_Slice Nickel.Register.fact) (gap: nat) (low: nat) (high: nat) : Lemma (requires (Prims.l_and (Prims.l_and (stream_steps facts) (ids_unique facts)) (counters_positive facts) /\ same_stream_order facts low high /\ gap == v (Seq.index facts high).f_id.f_counter - v (Seq.index facts low).f_id.f_counter)) (ensures clock_below facts low high) (decreases gap) =
  let via (j: nat) : Lemma (requires Prims.l_and (predecessor_of facts high j) (clock_below facts j high)) (ensures clock_below facts low high) =
    if v (Seq.index facts j).f_id.f_counter > v (Seq.index facts low).f_id.f_counter then
      begin stream_clock_increases facts (gap - 1) low j end
    else
      begin same_fields_same_id facts j low end;
    stream_step_composes facts low j high in
  later_stream_fact_has_step facts low high;
  FStar.Classical.forall_intro (FStar.Classical.move_requires via)

let same_priority (a: Nickel.Register.fact) (b: Nickel.Register.fact) : Type0 =
  Prims.l_and (a.f_payload.f_lamport == b.f_payload.f_lamport) (a.f_id.f_peer == b.f_id.f_peer)

let priority_identifies_fact (facts: t_Slice Nickel.Register.fact) (a: nat) (b: nat) : Lemma (requires (Prims.l_and (Prims.l_and (stream_steps facts) (ids_unique facts)) (counters_positive facts) /\ Prims.l_and (a < Seq.length facts) (b < Seq.length facts) /\ same_priority (Seq.index facts a) (Seq.index facts b))) (ensures a == b) =
  let ca = v (Seq.index facts a).f_id.f_counter in
  let cb = v (Seq.index facts b).f_id.f_counter in
  if ca < cb then
    begin stream_clock_increases facts (cb - ca) a b end
  else
    begin if cb < ca then
      begin stream_clock_increases facts (ca - cb) b a end
    else
      begin same_fields_same_id facts a b end end

let bytes_same_through (x: t_Slice u8) (y: t_Slice u8) (z: t_Slice u8) : Lemma (requires Prims.l_and (Nickel.Register.bytes_same x z) (Nickel.Register.bytes_same y z)) (ensures Nickel.Register.bytes_same x y) =
  ()

let maximal_pair_is_one_fact (facts: t_Slice Nickel.Register.fact) (key: u64) (i: nat) (k: nat) : Lemma (requires (Prims.l_and (Prims.l_and (stream_steps facts) (ids_unique facts)) (counters_positive facts) /\ Prims.l_and (causal_maximal facts key i) (causal_maximal facts key k) /\ Prims.l_and (Prims.l_not (Nickel.Register.higher (Seq.index facts i) (Seq.index facts k))) (Prims.l_not (Nickel.Register.higher (Seq.index facts k) (Seq.index facts i))))) (ensures i == k) =
  priority_identifies_fact facts i k

let causal_read_is_single_valued (facts: t_Slice Nickel.Register.fact) (key: u64) (initial: t_Slice u8) (x: t_Slice u8) (y: t_Slice u8) : Lemma (requires (Prims.l_and (Prims.l_and (Prims.l_and (clocks_increase facts) (streams_chained facts)) (ids_unique facts)) (counters_positive facts) /\ causal_read facts key initial x /\ causal_read facts key initial y)) (ensures Nickel.Register.bytes_same x y) =
  chained_streams_step_clocks facts;
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (maximal_pair_is_one_fact facts key));
  FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 bytes_same_through)

let frozen_causal_observation (before: Native.t_Replica) (offered: Nickel.Register.fact) (basis: Alloc.Vec.t_Vec Nickel.Register.fact Alloc.Alloc.t_Global) : Type0 =
  Prims.l_and (Prims.l_and (clocks_increase (Alloc.Vec.impl_1__as_slice basis) ==> causal_read (Alloc.Vec.impl_1__as_slice basis) offered.f_payload.f_key (Alloc.Vec.impl_1__as_slice before.f_initial) (Alloc.Vec.impl_1__as_slice offered.f_payload.f_observed)) (Prims.l_not (Nickel.Register.bytes_same (Alloc.Vec.impl_1__as_slice offered.f_payload.f_value) (Alloc.Vec.impl_1__as_slice offered.f_payload.f_observed)))) (Nickel.Register.clock_successor (Alloc.Vec.impl_1__as_slice basis) offered.f_payload.f_lamport)

let selected_basis_frozen (before: Native.t_Replica) (offered: Nickel.Register.fact) : Type0 =
  exists(selected: Alloc.Vec.t_Vec Envelope.t_Id Alloc.Alloc.t_Global) (basis: Alloc.Vec.t_Vec Nickel.Register.fact Alloc.Alloc.t_Global). Prims.l_and (Prims.l_and (Nickel_crdt.Event_layer.validate_event (Alloc.Vec.impl_1__as_slice before.f_facts) offered before.f_limits.f_events before.f_limits.f_dependencies Native.v_OPS == Result.Result_Ok selected) (Nickel_crdt.Event_layer.select_basis (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice selected) Native.v_OPS._1 == Result.Result_Ok basis)) (frozen_causal_observation before offered basis)

let observed_basis_read_is_causal (before: Native.t_Replica) (offered: Nickel.Register.fact) (basis: Alloc.Vec.t_Vec Nickel.Register.fact Alloc.Alloc.t_Global) : Lemma (requires Nickel.Register.bytes_same (Alloc.Vec.impl_1__as_slice offered.f_payload.f_observed) (Alloc.Vec.impl_1__as_slice (Native.read_history (Alloc.Vec.impl_1__as_slice basis) (Alloc.Vec.impl_1__as_slice before.f_initial) offered.f_payload.f_key))) (ensures clocks_increase (Alloc.Vec.impl_1__as_slice basis) ==> causal_read (Alloc.Vec.impl_1__as_slice basis) offered.f_payload.f_key (Alloc.Vec.impl_1__as_slice before.f_initial) (Alloc.Vec.impl_1__as_slice offered.f_payload.f_observed)) =
  FStar.Classical.move_requires (read_history_is_causal_read (Alloc.Vec.impl_1__as_slice basis) (Alloc.Vec.impl_1__as_slice before.f_initial)) offered.f_payload.f_key

let basis_checks_freeze (before: Native.t_Replica) (offered: Nickel.Register.fact) (basis: Alloc.Vec.t_Vec Nickel.Register.fact Alloc.Alloc.t_Global) : Lemma (requires (Nickel.Register.basis_payload_checks before offered basis /\ Nickel.Register.clock_successor (Alloc.Vec.impl_1__as_slice basis) offered.f_payload.f_lamport)) (ensures frozen_causal_observation before offered basis) =
  observed_basis_read_is_causal before offered basis

let selected_checks_freeze (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (requires (Nickel.Register.selected_basis_checks before offered /\ Nickel.Register.selected_basis_clock_successor before offered)) (ensures selected_basis_frozen before offered) =
  FStar.Classical.forall_intro (FStar.Classical.move_requires (basis_checks_freeze before offered))

let receive_added_freezes_causal_observation (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (ensures forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> selected_basis_frozen before offered) =
  Nickel.Register.receive_added_checks_payload before offered;
  Nickel.Register.receive_added_clock_is_maximum_successor before offered;
  FStar.Classical.move_requires (selected_checks_freeze before) offered;
  assert (forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> selected_basis_frozen before offered) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel_crdt.Register.next_lamport";
    Tactics.prune "Nickel_crdt.Event_layer.validate_event";
    Tactics.prune "Nickel_crdt.Event_layer.select_basis";
    Tactics.smt_sync' 1 1
  )

let register_ops_are_exact () : Lemma (ensures Prims.l_and (Prims.l_and (Prims.l_and (Nickel.RegisterPast.ids_exact Native.v_OPS._1) (Nickel.RegisterPast.copies_exact Native.v_OPS._1)) (forall(f: Nickel.Register.fact). Native.v_OPS._1._1._1 f == f.f_id)) (forall(f: Nickel.Register.fact). Native.v_OPS._1._1._2 f == Alloc.Vec.impl_1__as_slice f.f_after)) =
  let graph = Nickel_crdt.Event_layer.graph_ops Native.identity Native.parents Native.same_id Native.less_id Native.copy_fact Native.fact_equal Native.invalid Native.missing in
  Nickel.EventGraph.graph_ops_preserve_callbacks Native.identity Native.parents Native.same_id Native.less_id Native.copy_fact Native.fact_equal Native.invalid Native.missing;
  Nickel.EventGraph.event_ops_preserve_callbacks graph Native.previous Native.forbidden Native.capacity Native.capacity Native.invalid Native.invalid;
  assert (Native.v_OPS._1 == graph) by (
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.smt_sync' 1 1
  );
  Nickel.Register.register_canonical_values_are_exact ();
  let each_identity (f: Nickel.Register.fact) : Lemma (ensures graph._1._1 f == f.f_id) = assert (graph._1._1 == Native.identity) in
  let each_parents (f: Nickel.Register.fact) : Lemma (ensures graph._1._2 f == Alloc.Vec.impl_1__as_slice f.f_after) = assert (graph._1._2 == Native.parents) in
  FStar.Classical.forall_intro each_identity;
  FStar.Classical.forall_intro each_parents

let exact_selected_basis (before: Native.t_Replica) (offered: Nickel.Register.fact) : Type0 =
  exists(selected: Alloc.Vec.t_Vec Envelope.t_Id Alloc.Alloc.t_Global) (basis: Alloc.Vec.t_Vec Nickel.Register.fact Alloc.Alloc.t_Global). Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Nickel_crdt.Event_layer.validate_event (Alloc.Vec.impl_1__as_slice before.f_facts) offered before.f_limits.f_events before.f_limits.f_dependencies Native.v_OPS == Result.Result_Ok selected) (Nickel_crdt.Event_layer.select_basis (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice selected) Native.v_OPS._1 == Result.Result_Ok basis)) (forall(id: Envelope.t_Id). Nickel.RegisterPast.member (Alloc.Vec.impl_1__as_slice selected) id <==> Nickel.RegisterPast.ancestor Native.v_OPS._1 (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice offered.f_after) id)) (Nickel.RegisterPast.selected_prefix Native.v_OPS._1 (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice selected) (Seq.length (Alloc.Vec.impl_1__as_slice before.f_facts)) (Alloc.Vec.impl_1__as_slice basis))) (frozen_causal_observation before offered basis)

let selected_basis_is_exact (before: Native.t_Replica) (offered: Nickel.Register.fact) (selected: Alloc.Vec.t_Vec Envelope.t_Id Alloc.Alloc.t_Global) (basis: Alloc.Vec.t_Vec Nickel.Register.fact Alloc.Alloc.t_Global) : Lemma (requires (Nickel_crdt.Event_layer.validate_event (Alloc.Vec.impl_1__as_slice before.f_facts) offered before.f_limits.f_events before.f_limits.f_dependencies Native.v_OPS == Result.Result_Ok selected /\ Nickel_crdt.Event_layer.select_basis (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice selected) Native.v_OPS._1 == Result.Result_Ok basis)) (ensures Prims.l_and (forall(id: Envelope.t_Id). Nickel.RegisterPast.member (Alloc.Vec.impl_1__as_slice selected) id <==> Nickel.RegisterPast.ancestor Native.v_OPS._1 (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice offered.f_after) id) (Nickel.RegisterPast.selected_prefix Native.v_OPS._1 (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice selected) (Seq.length (Alloc.Vec.impl_1__as_slice before.f_facts)) (Alloc.Vec.impl_1__as_slice basis))) =
  let facts = Alloc.Vec.impl_1__as_slice before.f_facts in
  let roots = Alloc.Vec.impl_1__as_slice offered.f_after in
  register_ops_are_exact ();
  Nickel.RegisterPast.validated_selection_is_exact facts offered before.f_limits.f_events before.f_limits.f_dependencies Native.v_OPS;
  assert (forall(id: Envelope.t_Id). Nickel.RegisterPast.member (Alloc.Vec.impl_1__as_slice selected) id <==> Nickel.RegisterPast.ancestor Native.v_OPS._1 facts roots id) by (
    Tactics.prune "Nickel_crdt.Event_layer.validate_event";
    Tactics.smt_sync' 1 1
  );
  Nickel.RegisterPast.actual_basis_is_exact_filter Native.v_OPS._1 facts (Alloc.Vec.impl_1__as_slice selected);
  assert (Nickel.LoopUtil.result_safe (fun (out: Alloc.Vec.t_Vec Nickel.Register.fact Alloc.Alloc.t_Global) -> Nickel.RegisterPast.selected_prefix Native.v_OPS._1 facts (Alloc.Vec.impl_1__as_slice selected) (Seq.length facts) (Alloc.Vec.impl_1__as_slice out)) (fun (_: Native.t_Error) -> Prims.l_False) (Result.Result_Ok basis)) by (
    Tactics.prune "Nickel_crdt.Event_layer.select_basis";
    Tactics.smt_sync' 1 1
  );
  Nickel.RegisterPast.exact_filter_output Native.v_OPS._1 facts (Alloc.Vec.impl_1__as_slice selected) basis;
  assert (Nickel.RegisterPast.selected_prefix Native.v_OPS._1 facts (Alloc.Vec.impl_1__as_slice selected) (Seq.length facts) (Alloc.Vec.impl_1__as_slice basis)) by (
    Tactics.prune "Nickel_crdt.Event_layer.select_basis";
    Tactics.smt_sync' 1 1
  );
  assert (Prims.l_and (forall(id: Envelope.t_Id). Nickel.RegisterPast.member (Alloc.Vec.impl_1__as_slice selected) id <==> Nickel.RegisterPast.ancestor Native.v_OPS._1 facts roots id) (Nickel.RegisterPast.selected_prefix Native.v_OPS._1 facts (Alloc.Vec.impl_1__as_slice selected) (Seq.length facts) (Alloc.Vec.impl_1__as_slice basis))) by (
    Tactics.prune "Nickel_crdt.Event_layer.validate_event";
    Tactics.prune "Nickel_crdt.Event_layer.select_basis";
    Tactics.smt_sync' 1 1
  )

let witness_is_exact (before: Native.t_Replica) (offered: Nickel.Register.fact) (selected: Alloc.Vec.t_Vec Envelope.t_Id Alloc.Alloc.t_Global) (basis: Alloc.Vec.t_Vec Nickel.Register.fact Alloc.Alloc.t_Global) : Lemma (requires Prims.l_and (Prims.l_and (Nickel_crdt.Event_layer.validate_event (Alloc.Vec.impl_1__as_slice before.f_facts) offered before.f_limits.f_events before.f_limits.f_dependencies Native.v_OPS == Result.Result_Ok selected) (Nickel_crdt.Event_layer.select_basis (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice selected) Native.v_OPS._1 == Result.Result_Ok basis)) (frozen_causal_observation before offered basis)) (ensures exact_selected_basis before offered) =
  selected_basis_is_exact before offered selected basis;
  assert (exact_selected_basis before offered) by (
    Tactics.prune "Nickel_crdt.Event_layer.validate_event";
    Tactics.prune "Nickel_crdt.Event_layer.select_basis";
    Tactics.smt_sync' 1 1
  )

let selected_frozen_is_exact (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (requires selected_basis_frozen before offered) (ensures exact_selected_basis before offered) =
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (witness_is_exact before offered));
  assert (exact_selected_basis before offered) by (
    Tactics.prune "Nickel_crdt.Event_layer.validate_event";
    Tactics.prune "Nickel_crdt.Event_layer.select_basis";
    Tactics.smt_sync' 1 1
  )

let receive_added_basis_is_exact_ancestry (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (ensures forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> exact_selected_basis before offered) =
  receive_added_freezes_causal_observation before offered;
  FStar.Classical.move_requires (selected_frozen_is_exact before) offered;
  assert (forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> exact_selected_basis before offered) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel_crdt.Register.next_lamport";
    Tactics.prune "Nickel_crdt.Event_layer.validate_event";
    Tactics.prune "Nickel_crdt.Event_layer.select_basis";
    Tactics.smt_sync' 1 1
  )