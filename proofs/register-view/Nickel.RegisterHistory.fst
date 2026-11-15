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

open Nickel.PastExact

open Nickel.EventClassifier

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
  FStar.Classical.forall_intro (FStar.Classical.move_requires (priority_maximum_is_causal_maximum facts key));
  assert (causal_read facts key initial (Alloc.Vec.impl_1__as_slice (Native.read_history facts initial key))) by (
    Tactics.prune "Nickel_crdt.Register.read_history";
    Tactics.prune "Nickel_crdt.Register.winner";
    Tactics.smt_sync' 1 1
  )

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

let stream_recursion_ready (facts: t_Slice Nickel.Register.fact) (gap: nat) (low: nat) (high: nat) (j: nat) : Lemma (requires (Prims.l_and (same_stream_order facts low high) (predecessor_of facts high j) /\ gap == v (Seq.index facts high).f_id.f_counter - v (Seq.index facts low).f_id.f_counter /\ v (Seq.index facts j).f_id.f_counter > v (Seq.index facts low).f_id.f_counter)) (ensures Prims.l_and (Prims.l_and (same_stream_order facts low j) (gap > 0)) (gap - 1 == v (Seq.index facts j).f_id.f_counter - v (Seq.index facts low).f_id.f_counter)) =
  ()

let stream_bottom_is_low (facts: t_Slice Nickel.Register.fact) (low: nat) (high: nat) (j: nat) : Lemma (requires (ids_unique facts /\ Prims.l_and (same_stream_order facts low high) (predecessor_of facts high j) /\ Prims.l_not (v (Seq.index facts j).f_id.f_counter > v (Seq.index facts low).f_id.f_counter))) (ensures j == low) =
  same_fields_same_id facts j low

let rec stream_clock_increases (facts: t_Slice Nickel.Register.fact) (gap: nat) (low: nat) (high: nat) : Lemma (requires (Prims.l_and (Prims.l_and (stream_steps facts) (ids_unique facts)) (counters_positive facts) /\ same_stream_order facts low high /\ gap == v (Seq.index facts high).f_id.f_counter - v (Seq.index facts low).f_id.f_counter)) (ensures clock_below facts low high) (decreases gap) =
  let via (j: nat) : Lemma (requires Prims.l_and (predecessor_of facts high j) (clock_below facts j high)) (ensures clock_below facts low high) =
    if v (Seq.index facts j).f_id.f_counter > v (Seq.index facts low).f_id.f_counter then
      begin stream_recursion_ready facts gap low high j;
      stream_clock_increases facts (gap - 1) low j end
    else
      begin stream_bottom_is_low facts low high j end;
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

let register_ops_are_exact () : Lemma (ensures Prims.l_and (Prims.l_and (Prims.l_and (Nickel.PastExact.ids_exact Native.v_OPS._1) (Nickel.PastExact.copies_exact Native.v_OPS._1)) (forall(f: Nickel.Register.fact). Native.v_OPS._1._1._1 f == f.f_id)) (forall(f: Nickel.Register.fact). Native.v_OPS._1._1._2 f == Alloc.Vec.impl_1__as_slice f.f_after)) =
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
  exists(selected: Alloc.Vec.t_Vec Envelope.t_Id Alloc.Alloc.t_Global) (basis: Alloc.Vec.t_Vec Nickel.Register.fact Alloc.Alloc.t_Global). Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Nickel_crdt.Event_layer.validate_event (Alloc.Vec.impl_1__as_slice before.f_facts) offered before.f_limits.f_events before.f_limits.f_dependencies Native.v_OPS == Result.Result_Ok selected) (Nickel_crdt.Event_layer.select_basis (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice selected) Native.v_OPS._1 == Result.Result_Ok basis)) (forall(id: Envelope.t_Id). Nickel.PastExact.member (Alloc.Vec.impl_1__as_slice selected) id <==> Nickel.PastExact.ancestor Native.v_OPS._1 (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice offered.f_after) id)) (Nickel.PastExact.selected_prefix Native.v_OPS._1 (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice selected) (Seq.length (Alloc.Vec.impl_1__as_slice before.f_facts)) (Alloc.Vec.impl_1__as_slice basis))) (frozen_causal_observation before offered basis)

let selected_basis_is_exact (before: Native.t_Replica) (offered: Nickel.Register.fact) (selected: Alloc.Vec.t_Vec Envelope.t_Id Alloc.Alloc.t_Global) (basis: Alloc.Vec.t_Vec Nickel.Register.fact Alloc.Alloc.t_Global) : Lemma (requires (Nickel_crdt.Event_layer.validate_event (Alloc.Vec.impl_1__as_slice before.f_facts) offered before.f_limits.f_events before.f_limits.f_dependencies Native.v_OPS == Result.Result_Ok selected /\ Nickel_crdt.Event_layer.select_basis (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice selected) Native.v_OPS._1 == Result.Result_Ok basis)) (ensures Prims.l_and (forall(id: Envelope.t_Id). Nickel.PastExact.member (Alloc.Vec.impl_1__as_slice selected) id <==> Nickel.PastExact.ancestor Native.v_OPS._1 (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice offered.f_after) id) (Nickel.PastExact.selected_prefix Native.v_OPS._1 (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice selected) (Seq.length (Alloc.Vec.impl_1__as_slice before.f_facts)) (Alloc.Vec.impl_1__as_slice basis))) =
  let facts = Alloc.Vec.impl_1__as_slice before.f_facts in
  let roots = Alloc.Vec.impl_1__as_slice offered.f_after in
  register_ops_are_exact ();
  Nickel.PastExact.validated_selection_is_exact facts offered before.f_limits.f_events before.f_limits.f_dependencies Native.v_OPS;
  assert (forall(id: Envelope.t_Id). Nickel.PastExact.member (Alloc.Vec.impl_1__as_slice selected) id <==> Nickel.PastExact.ancestor Native.v_OPS._1 facts roots id) by (
    Tactics.prune "Nickel_crdt.Event_layer.validate_event";
    Tactics.smt_sync' 1 1
  );
  Nickel.PastExact.actual_basis_is_exact_filter Native.v_OPS._1 facts (Alloc.Vec.impl_1__as_slice selected);
  assert (Nickel.LoopUtil.result_safe (fun (out: Alloc.Vec.t_Vec Nickel.Register.fact Alloc.Alloc.t_Global) -> Nickel.PastExact.selected_prefix Native.v_OPS._1 facts (Alloc.Vec.impl_1__as_slice selected) (Seq.length facts) (Alloc.Vec.impl_1__as_slice out)) (fun (_: Native.t_Error) -> Prims.l_False) (Result.Result_Ok basis)) by (
    Tactics.prune "Nickel_crdt.Event_layer.select_basis";
    Tactics.smt_sync' 1 1
  );
  Nickel.PastExact.exact_filter_output Native.v_OPS._1 facts (Alloc.Vec.impl_1__as_slice selected) basis;
  assert (Nickel.PastExact.selected_prefix Native.v_OPS._1 facts (Alloc.Vec.impl_1__as_slice selected) (Seq.length facts) (Alloc.Vec.impl_1__as_slice basis)) by (
    Tactics.prune "Nickel_crdt.Event_layer.select_basis";
    Tactics.smt_sync' 1 1
  );
  assert (Prims.l_and (forall(id: Envelope.t_Id). Nickel.PastExact.member (Alloc.Vec.impl_1__as_slice selected) id <==> Nickel.PastExact.ancestor Native.v_OPS._1 facts roots id) (Nickel.PastExact.selected_prefix Native.v_OPS._1 facts (Alloc.Vec.impl_1__as_slice selected) (Seq.length facts) (Alloc.Vec.impl_1__as_slice basis))) by (
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

let stored (xs: Seq.seq Nickel.Register.fact) (f: Nickel.Register.fact) : Type0 =
  exists(i: nat). Prims.l_and (i < Seq.length xs) (Seq.index xs i == f)

let present_append_one (xs: Seq.seq Nickel.Register.fact) (x: Nickel.Register.fact) (f: Nickel.Register.fact) : Lemma (ensures stored (Seq.append xs (Seq.create 1 x)) f <==> Prims.l_or (stored xs f) (x == f)) =
  let ys = Seq.append xs (Seq.create 1 x) in
  let fwd (i: nat) : Lemma (requires Prims.l_and (i < Seq.length ys) (Seq.index ys i == f)) (ensures Prims.l_or (stored xs f) (x == f)) = if i < Seq.length xs then
    begin assert (Seq.index xs i == f) end
  else
    begin () end in
  FStar.Classical.forall_intro (FStar.Classical.move_requires fwd);
  let back (i: nat) : Lemma (requires Prims.l_and (i < Seq.length xs) (Seq.index xs i == f)) (ensures stored ys f) = assert (Seq.index ys i == f) in
  FStar.Classical.forall_intro (FStar.Classical.move_requires back);
  assert (Seq.index ys (Seq.length xs) == x)

let selected_below (ops: Nickel.RegisterPast.rops) (facts: t_Slice Nickel.Register.fact) (sel: t_Slice Envelope.t_Id) (n: nat) (f: Nickel.Register.fact) : Type0 =
  exists(i: nat). Prims.l_and (Prims.l_and (Prims.l_and (i < n) (i < Seq.length facts)) (Seq.index facts i == f)) (Nickel.PastExact.member sel (ops._1._1 (Seq.index facts i)))

let below_step (ops: Nickel.RegisterPast.rops) (facts: t_Slice Nickel.Register.fact) (sel: t_Slice Envelope.t_Id) (n: nat{Prims.l_and (0 < n) (n <= Seq.length facts)}) (f: Nickel.Register.fact) : Lemma (ensures selected_below ops facts sel n f <==> Prims.l_or (selected_below ops facts sel (n - 1) f) (Prims.l_and (Seq.index facts (n - 1) == f) (Nickel.PastExact.member sel (ops._1._1 (Seq.index facts (n - 1)))))) =
  ()

let rec filter_has_selected_facts (ops: Nickel.RegisterPast.rops) (facts: t_Slice Nickel.Register.fact) (sel: t_Slice Envelope.t_Id) (n: nat{n <= Seq.length facts}) (out: Seq.seq Nickel.Register.fact) : Lemma (requires Nickel.PastExact.selected_prefix ops facts sel n out) (ensures forall(f: Nickel.Register.fact). stored out f <==> selected_below ops facts sel n f) (decreases n) =
  if n ==? 0 then
    begin Nickel.PastExact.selected_prefix_zero ops facts sel out end
  else
    begin let x = Seq.index facts (n - 1) in
    Nickel.PastExact.selected_prefix_step ops facts sel n out;
    let grow (before: Seq.seq Nickel.Register.fact) : Lemma (requires (Nickel.PastExact.selected_prefix ops facts sel (n - 1) before /\ out == Seq.append before (Seq.create 1 x) /\ Nickel.PastExact.member sel (ops._1._1 x))) (ensures forall(f: Nickel.Register.fact). stored out f <==> selected_below ops facts sel n f) =
      filter_has_selected_facts ops facts sel (n - 1) before;
      FStar.Classical.forall_intro (present_append_one before x);
      FStar.Classical.forall_intro (below_step ops facts sel n) in
    let kept () : Lemma (requires Nickel.PastExact.member sel (ops._1._1 x)) (ensures forall(f: Nickel.Register.fact). stored out f <==> selected_below ops facts sel n f) = FStar.Classical.forall_intro (FStar.Classical.move_requires grow) in
    let skipped () : Lemma (requires Prims.l_not (Nickel.PastExact.member sel (ops._1._1 x))) (ensures forall(f: Nickel.Register.fact). stored out f <==> selected_below ops facts sel n f) =
      filter_has_selected_facts ops facts sel (n - 1) out;
      FStar.Classical.forall_intro (below_step ops facts sel n) in
    FStar.Classical.move_requires kept ();
    FStar.Classical.move_requires skipped () end

let stored_unique (facts: Seq.seq Nickel.Register.fact) : Type0 =
  forall(f: Nickel.Register.fact) (g: Nickel.Register.fact). Prims.l_and (Prims.l_and (stored facts f) (stored facts g)) (f.f_id == g.f_id) ==> f == g

let id_edge (facts: Seq.seq Nickel.Register.fact) (newer: Envelope.t_Id) (older: Envelope.t_Id) : Type0 =
  exists(f: Nickel.Register.fact). Prims.l_and (Prims.l_and (stored facts f) (f.f_id == newer)) (Nickel.PastExact.member (Alloc.Vec.impl_1__as_slice f.f_after) older)

let rec id_path (facts: Seq.seq Nickel.Register.fact) (start: Envelope.t_Id) (steps: Prims.list Envelope.t_Id) (finish: Envelope.t_Id) : Tot Type0 (decreases steps) =
  match steps with | Prims.Nil -> begin start == finish end | Prims.Cons next rest -> begin Prims.l_and (id_edge facts start next) (id_path facts next rest finish) end

let id_strictly_below (facts: Seq.seq Nickel.Register.fact) (newer: Envelope.t_Id) (older: Envelope.t_Id) : Type0 =
  exists(next: Envelope.t_Id) (rest: Prims.list Envelope.t_Id). id_path facts newer (Prims.Cons next rest) older

let id_clocks_increase (facts: Seq.seq Nickel.Register.fact) : Type0 =
  forall(fa: Nickel.Register.fact) (fb: Nickel.Register.fact). Prims.l_and (Prims.l_and (stored facts fa) (stored facts fb)) (Nickel.PastExact.member (Alloc.Vec.impl_1__as_slice fa.f_after) fb.f_id) ==> v fb.f_payload.f_lamport < v fa.f_payload.f_lamport

let rec id_path_clock_decreases (facts: Seq.seq Nickel.Register.fact) (fa: Nickel.Register.fact) (next: Envelope.t_Id) (rest: Prims.list Envelope.t_Id) (fb: Nickel.Register.fact) : Lemma (requires (Prims.l_and (stored_unique facts) (id_clocks_increase facts) /\ Prims.l_and (stored facts fa) (stored facts fb) /\ id_path facts fa.f_id (Prims.Cons next rest) fb.f_id)) (ensures v fb.f_payload.f_lamport < v fa.f_payload.f_lamport) (decreases rest) =
  match rest with | Prims.Nil -> begin () end | Prims.Cons next2 rest2 -> begin let via (fn: Nickel.Register.fact) : Lemma (requires (Prims.l_and (stored facts fn) (fn.f_id == next) /\ Nickel.PastExact.member (Alloc.Vec.impl_1__as_slice fn.f_after) next2)) (ensures v fb.f_payload.f_lamport < v fa.f_payload.f_lamport) = id_path_clock_decreases facts fn next2 rest2 fb in
  FStar.Classical.forall_intro (FStar.Classical.move_requires via) end

let maximal_in (facts: Seq.seq Nickel.Register.fact) (sel: Envelope.t_Id -> Type0) (key: u64) (f: Nickel.Register.fact) : Type0 =
  Prims.l_and (Prims.l_and (Prims.l_and (stored facts f) (sel f.f_id)) (f.f_payload.f_key == key)) (Prims.l_not (exists(g: Nickel.Register.fact). Prims.l_and (Prims.l_and (Prims.l_and (stored facts g) (sel g.f_id)) (g.f_payload.f_key == key)) (id_strictly_below facts g.f_id f.f_id)))

let causal_read_in (facts: Seq.seq Nickel.Register.fact) (sel: Envelope.t_Id -> Type0) (key: u64) (initial: t_Slice u8) (value: t_Slice u8) : Type0 =
  Prims.l_or (Prims.l_and (forall(g: Nickel.Register.fact). Prims.l_and (stored facts g) (sel g.f_id) ==> g.f_payload.f_key =!= key) (Nickel.Register.bytes_same value initial)) (exists(f: Nickel.Register.fact). Prims.l_and (Prims.l_and (maximal_in facts sel key f) (Nickel.Register.bytes_same value (Alloc.Vec.impl_1__as_slice f.f_payload.f_value))) (forall(g: Nickel.Register.fact). maximal_in facts sel key g ==> Prims.l_not (Nickel.Register.higher g f)))

let holds_selected (basis: Seq.seq Nickel.Register.fact) (facts: Seq.seq Nickel.Register.fact) (sel: Envelope.t_Id -> Type0) : Type0 =
  forall(f: Nickel.Register.fact). stored basis f <==> Prims.l_and (stored facts f) (sel f.f_id)

let maximum_is_maximal_in (basis: Seq.seq Nickel.Register.fact) (facts: Seq.seq Nickel.Register.fact) (sel: Envelope.t_Id -> Type0) (key: u64) (f: Nickel.Register.fact) : Lemma (requires (Prims.l_and (Prims.l_and (holds_selected basis facts sel) (stored_unique facts)) (id_clocks_increase facts) /\ Prims.l_and (stored basis f) (f.f_payload.f_key == key) /\ (forall(j: nat). Prims.l_and (j < Seq.length basis) ((Seq.index basis j).f_payload.f_key == key) ==> Prims.l_not (Nickel.Register.higher (Seq.index basis j) f)))) (ensures maximal_in facts sel key f) =
  let no_dominator (g: Nickel.Register.fact) (next: Envelope.t_Id) (rest: Prims.list Envelope.t_Id) : Lemma (requires (Prims.l_and (Prims.l_and (stored facts g) (sel g.f_id)) (g.f_payload.f_key == key) /\ id_path facts g.f_id (Prims.Cons next rest) f.f_id)) (ensures Prims.l_False) = id_path_clock_decreases facts g next rest f in
  FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 no_dominator)

let selected_maximum_is_causal_read_in (basis: t_Slice Nickel.Register.fact) (facts: Seq.seq Nickel.Register.fact) (sel: Envelope.t_Id -> Type0) (key: u64) (initial: t_Slice u8) (value: t_Slice u8) : Lemma (requires (Prims.l_and (Prims.l_and (holds_selected basis facts sel) (stored_unique facts)) (id_clocks_increase facts) /\ Nickel.Register.selected_value basis key initial value)) (ensures causal_read_in facts sel key initial value) =
  let from_index (i: nat) (f: Nickel.Register.fact) : Lemma (requires (Prims.l_and (Prims.l_and (i < Seq.length basis) (Seq.index basis i == f)) (f.f_payload.f_key == key) /\ (forall(j: nat). Prims.l_and (j < Seq.length basis) ((Seq.index basis j).f_payload.f_key == key) ==> Prims.l_not (Nickel.Register.higher (Seq.index basis j) f)))) (ensures Prims.l_and (maximal_in facts sel key f) (forall(g: Nickel.Register.fact). maximal_in facts sel key g ==> Prims.l_not (Nickel.Register.higher g f))) = maximum_is_maximal_in basis facts sel key f in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 from_index)

let sel_of (selected: Alloc.Vec.t_Vec Envelope.t_Id Alloc.Alloc.t_Global) : Envelope.t_Id -> Type0 =
  fun (id: Envelope.t_Id) -> Nickel.PastExact.member (Alloc.Vec.impl_1__as_slice selected) id

let frozen_id_read (before: Native.t_Replica) (offered: Nickel.Register.fact) (selected: Alloc.Vec.t_Vec Envelope.t_Id Alloc.Alloc.t_Global) : Type0 =
  Prims.l_and (stored_unique (Alloc.Vec.impl_1__as_slice before.f_facts)) (id_clocks_increase (Alloc.Vec.impl_1__as_slice before.f_facts)) ==> causal_read_in (Alloc.Vec.impl_1__as_slice before.f_facts) (sel_of selected) offered.f_payload.f_key (Alloc.Vec.impl_1__as_slice before.f_initial) (Alloc.Vec.impl_1__as_slice offered.f_payload.f_observed)

let selected_value_respects_bytes (facts: t_Slice Nickel.Register.fact) (key: u64) (initial: t_Slice u8) (x: t_Slice u8) (y: t_Slice u8) : Lemma (requires Prims.l_and (Nickel.Register.selected_value facts key initial y) (Nickel.Register.bytes_same x y)) (ensures Nickel.Register.selected_value facts key initial x) =
  ()

let freeze_from_maximum (before: Native.t_Replica) (offered: Nickel.Register.fact) (selected: Alloc.Vec.t_Vec Envelope.t_Id Alloc.Alloc.t_Global) (basis: Alloc.Vec.t_Vec Nickel.Register.fact Alloc.Alloc.t_Global) (r: t_Slice u8) : Lemma (requires (holds_selected (Alloc.Vec.impl_1__as_slice basis) (Alloc.Vec.impl_1__as_slice before.f_facts) (sel_of selected) /\ Nickel.Register.selected_value (Alloc.Vec.impl_1__as_slice basis) offered.f_payload.f_key (Alloc.Vec.impl_1__as_slice before.f_initial) r /\ Nickel.Register.bytes_same (Alloc.Vec.impl_1__as_slice offered.f_payload.f_observed) r)) (ensures frozen_id_read before offered selected) =
  let b = Alloc.Vec.impl_1__as_slice basis in
  selected_value_respects_bytes b offered.f_payload.f_key (Alloc.Vec.impl_1__as_slice before.f_initial) (Alloc.Vec.impl_1__as_slice offered.f_payload.f_observed) r;
  FStar.Classical.move_requires (selected_maximum_is_causal_read_in b (Alloc.Vec.impl_1__as_slice before.f_facts) (sel_of selected) offered.f_payload.f_key (Alloc.Vec.impl_1__as_slice before.f_initial)) (Alloc.Vec.impl_1__as_slice offered.f_payload.f_observed)

let basis_freezes_id_read (before: Native.t_Replica) (offered: Nickel.Register.fact) (selected: Alloc.Vec.t_Vec Envelope.t_Id Alloc.Alloc.t_Global) (basis: Alloc.Vec.t_Vec Nickel.Register.fact Alloc.Alloc.t_Global) : Lemma (requires (Nickel.PastExact.selected_prefix Native.v_OPS._1 (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice selected) (Seq.length (Alloc.Vec.impl_1__as_slice before.f_facts)) (Alloc.Vec.impl_1__as_slice basis) /\ Nickel.Register.basis_payload_checks before offered basis)) (ensures frozen_id_read before offered selected) =
  let facts = Alloc.Vec.impl_1__as_slice before.f_facts in
  let b = Alloc.Vec.impl_1__as_slice basis in
  register_ops_are_exact ();
  filter_has_selected_facts Native.v_OPS._1 facts (Alloc.Vec.impl_1__as_slice selected) (Seq.length facts) b;
  assert (holds_selected b facts (sel_of selected));
  FStar.Classical.forall_intro (FStar.Classical.move_requires (freeze_from_maximum before offered selected basis));
  Nickel.Register.read_history_selects_maximum b (Alloc.Vec.impl_1__as_slice before.f_initial) offered.f_payload.f_key;
  assert (frozen_id_read before offered selected) by (
    Tactics.prune "Nickel_crdt.Register.read_history";
    Tactics.prune "Nickel_crdt.Register.winner";
    Tactics.prune "Nickel.RegisterHistory.frozen_id_read";
    Tactics.prune "Nickel.RegisterHistory.causal_read_in";
    Tactics.smt_sync' 1 1
  )

let id_frozen_admission (before: Native.t_Replica) (offered: Nickel.Register.fact) : Type0 =
  exists(selected: Alloc.Vec.t_Vec Envelope.t_Id Alloc.Alloc.t_Global). Prims.l_and (Prims.l_and (Nickel_crdt.Event_layer.validate_event (Alloc.Vec.impl_1__as_slice before.f_facts) offered before.f_limits.f_events before.f_limits.f_dependencies Native.v_OPS == Result.Result_Ok selected) (forall(id: Envelope.t_Id). Nickel.PastExact.member (Alloc.Vec.impl_1__as_slice selected) id <==> Nickel.PastExact.ancestor Native.v_OPS._1 (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice offered.f_after) id)) (frozen_id_read before offered selected)

let id_witness (before: Native.t_Replica) (offered: Nickel.Register.fact) (selected: Alloc.Vec.t_Vec Envelope.t_Id Alloc.Alloc.t_Global) (basis: Alloc.Vec.t_Vec Nickel.Register.fact Alloc.Alloc.t_Global) : Lemma (requires Prims.l_and (Prims.l_and (Nickel_crdt.Event_layer.validate_event (Alloc.Vec.impl_1__as_slice before.f_facts) offered before.f_limits.f_events before.f_limits.f_dependencies Native.v_OPS == Result.Result_Ok selected) (Nickel_crdt.Event_layer.select_basis (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice selected) Native.v_OPS._1 == Result.Result_Ok basis)) (Nickel.Register.basis_payload_checks before offered basis)) (ensures id_frozen_admission before offered) =
  selected_basis_is_exact before offered selected basis;
  basis_freezes_id_read before offered selected basis;
  assert (id_frozen_admission before offered) by (
    Tactics.prune "Nickel_crdt.Event_layer.validate_event";
    Tactics.prune "Nickel_crdt.Event_layer.select_basis";
    Tactics.smt_sync' 1 1
  )

let checks_give_id_frozen (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (requires Nickel.Register.selected_basis_checks before offered) (ensures id_frozen_admission before offered) =
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (id_witness before offered));
  assert (id_frozen_admission before offered) by (
    Tactics.prune "Nickel_crdt.Event_layer.validate_event";
    Tactics.prune "Nickel_crdt.Event_layer.select_basis";
    Tactics.smt_sync' 1 1
  )

let receive_added_freezes_id_read (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (ensures forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> id_frozen_admission before offered) =
  Nickel.Register.receive_added_checks_payload before offered;
  FStar.Classical.move_requires (checks_give_id_frozen before) offered;
  assert (forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> id_frozen_admission before offered) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel_crdt.Register.next_lamport";
    Tactics.prune "Nickel_crdt.Event_layer.validate_event";
    Tactics.prune "Nickel_crdt.Event_layer.select_basis";
    Tactics.smt_sync' 1 1
  )

let same_members (a: Seq.seq Nickel.Register.fact) (b: Seq.seq Nickel.Register.fact) : Type0 =
  forall(f: Nickel.Register.fact). stored a f <==> stored b f

let rec id_path_same (a: Seq.seq Nickel.Register.fact) (b: Seq.seq Nickel.Register.fact) (start: Envelope.t_Id) (steps: Prims.list Envelope.t_Id) (finish: Envelope.t_Id) : Lemma (requires same_members a b) (ensures id_path a start steps finish <==> id_path b start steps finish) (decreases steps) =
  match steps with | Prims.Nil -> begin () end | Prims.Cons next rest -> begin id_path_same a b next rest finish end

let order_free_meaning (a: Seq.seq Nickel.Register.fact) (b: Seq.seq Nickel.Register.fact) (sel: Envelope.t_Id -> Type0) (key: u64) (initial: t_Slice u8) (value: t_Slice u8) : Lemma (requires same_members a b) (ensures Prims.l_and (Prims.l_and (stored_unique a <==> stored_unique b) (id_clocks_increase a <==> id_clocks_increase b)) (causal_read_in a sel key initial value <==> causal_read_in b sel key initial value)) =
  FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 (id_path_same a b));
  assert (forall(x: Envelope.t_Id) (y: Envelope.t_Id). id_strictly_below a x y <==> id_strictly_below b x y);
  assert (forall(f: Nickel.Register.fact). maximal_in a sel key f <==> maximal_in b sel key f)

let extends_by (h: Seq.seq Nickel.Register.fact) (h2: Seq.seq Nickel.Register.fact) (f: Nickel.Register.fact) : Type0 =
  forall(g: Nickel.Register.fact). stored h2 g <==> Prims.l_or (stored h g) (g == f)

let unreferenced (h: Seq.seq Nickel.Register.fact) (x: Envelope.t_Id) : Type0 =
  forall(g: Nickel.Register.fact). stored h g ==> Prims.l_not (Nickel.PastExact.member (Alloc.Vec.impl_1__as_slice g.f_after) x)

let rec id_path_extend (h: Seq.seq Nickel.Register.fact) (h2: Seq.seq Nickel.Register.fact) (f: Nickel.Register.fact) (start: Envelope.t_Id) (steps: Prims.list Envelope.t_Id) (finish: Envelope.t_Id) : Lemma (requires (Prims.l_and (extends_by h h2 f) (unreferenced h2 f.f_id) /\ start =!= f.f_id)) (ensures id_path h2 start steps finish <==> id_path h start steps finish) (decreases steps) =
  match steps with | Prims.Nil -> begin () end | Prims.Cons next rest -> begin let next_is_old () : Lemma (requires id_edge h2 start next) (ensures next =!= f.f_id) = () in
  FStar.Classical.move_requires next_is_old ();
  let deeper () : Lemma (requires next =!= f.f_id) (ensures id_path h2 next rest finish <==> id_path h next rest finish) = id_path_extend h h2 f next rest finish in
  FStar.Classical.move_requires deeper () end

let read_unchanged_by_extension (h: Seq.seq Nickel.Register.fact) (h2: Seq.seq Nickel.Register.fact) (f: Nickel.Register.fact) (sel: Envelope.t_Id -> Type0) (key: u64) (initial: t_Slice u8) (value: t_Slice u8) : Lemma (requires (Prims.l_and (extends_by h h2 f) (unreferenced h2 f.f_id) /\ Prims.l_not (sel f.f_id))) (ensures causal_read_in h2 sel key initial value <==> causal_read_in h sel key initial value) =
  let walks (start: Envelope.t_Id) (steps: Prims.list Envelope.t_Id) (finish: Envelope.t_Id) : Lemma (requires sel start) (ensures id_path h2 start steps finish <==> id_path h start steps finish) = id_path_extend h h2 f start steps finish in
  FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 walks);
  assert (forall(x: Envelope.t_Id) (y: Envelope.t_Id). sel x ==> (id_strictly_below h2 x y <==> id_strictly_below h x y));
  assert (forall(g: Nickel.Register.fact). maximal_in h2 sel key g <==> maximal_in h sel key g)

let id_ancestor (facts: Seq.seq Nickel.Register.fact) (roots: t_Slice Envelope.t_Id) (id: Envelope.t_Id) : Type0 =
  exists(root: Envelope.t_Id) (steps: Prims.list Envelope.t_Id). Prims.l_and (Nickel.PastExact.member roots root) (id_path facts root steps id)

let register_edge_is_id_edge (facts: t_Slice Nickel.Register.fact) (a: Envelope.t_Id) (b: Envelope.t_Id) : Lemma (ensures Nickel.PastExact.causal_edge Native.v_OPS._1 facts a b <==> id_edge facts a b) =
  register_ops_are_exact ()

let rec register_path_is_id_path (facts: t_Slice Nickel.Register.fact) (start: Envelope.t_Id) (steps: Prims.list Envelope.t_Id) (finish: Envelope.t_Id) : Lemma (ensures Nickel.PastExact.causal_path Native.v_OPS._1 facts start steps finish <==> id_path facts start steps finish) (decreases steps) =
  Nickel.PastExact.causal_path_equations Native.v_OPS._1 facts;
  match steps with | Prims.Nil -> begin assert (Nickel.PastExact.causal_path Native.v_OPS._1 facts start steps finish <==> start == finish);
  assert (id_path facts start steps finish <==> start == finish) end | Prims.Cons next rest -> begin register_edge_is_id_edge facts start next;
  register_path_is_id_path facts next rest finish;
  assert (Nickel.PastExact.causal_path Native.v_OPS._1 facts start steps finish <==> Prims.l_and (Nickel.PastExact.causal_edge Native.v_OPS._1 facts start next) (Nickel.PastExact.causal_path Native.v_OPS._1 facts next rest finish));
  assert (id_path facts start steps finish <==> Prims.l_and (id_edge facts start next) (id_path facts next rest finish)) end

let register_ancestor_is_id_ancestor (facts: t_Slice Nickel.Register.fact) (roots: t_Slice Envelope.t_Id) (id: Envelope.t_Id) : Lemma (ensures Nickel.PastExact.ancestor Native.v_OPS._1 facts roots id <==> id_ancestor facts roots id) =
  FStar.Classical.forall_intro_3 (register_path_is_id_path facts)

let anc_of (h: Seq.seq Nickel.Register.fact) (f: Nickel.Register.fact) : Envelope.t_Id -> Type0 =
  fun (id: Envelope.t_Id) -> id_ancestor h (Alloc.Vec.impl_1__as_slice f.f_after) id

let observation_ok (h: Seq.seq Nickel.Register.fact) (initial: t_Slice u8) (f: Nickel.Register.fact) : Type0 =
  causal_read_in h (anc_of h f) f.f_payload.f_key initial (Alloc.Vec.impl_1__as_slice f.f_payload.f_observed)

let observations_ok (h: Seq.seq Nickel.Register.fact) (initial: t_Slice u8) : Type0 =
  forall(f: Nickel.Register.fact). stored h f ==> observation_ok h initial f

let rec never_reaches_new (h2: Seq.seq Nickel.Register.fact) (x: Envelope.t_Id) (root: Envelope.t_Id) (steps: Prims.list Envelope.t_Id) : Lemma (requires (unreferenced h2 x /\ root =!= x)) (ensures Prims.l_not (id_path h2 root steps x)) (decreases steps) =
  match steps with | Prims.Nil -> begin () end | Prims.Cons next rest -> begin let deeper () : Lemma (requires id_edge h2 root next) (ensures Prims.l_not (id_path h2 next rest x)) = never_reaches_new h2 x next rest in
  FStar.Classical.move_requires deeper () end

let ancestry_unchanged_by_extension (h: Seq.seq Nickel.Register.fact) (h2: Seq.seq Nickel.Register.fact) (fnew: Nickel.Register.fact) (roots: t_Slice Envelope.t_Id) : Lemma (requires (Prims.l_and (extends_by h h2 fnew) (unreferenced h2 fnew.f_id) /\ Prims.l_not (Nickel.PastExact.member roots fnew.f_id))) (ensures Prims.l_and (forall(id: Envelope.t_Id). id_ancestor h2 roots id <==> id_ancestor h roots id) (Prims.l_not (id_ancestor h2 roots fnew.f_id))) =
  let walks (root: Envelope.t_Id) (steps: Prims.list Envelope.t_Id) (finish: Envelope.t_Id) : Lemma (requires Nickel.PastExact.member roots root) (ensures id_path h2 root steps finish <==> id_path h root steps finish) = id_path_extend h h2 fnew root steps finish in
  FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 walks);
  let never_reaches (root: Envelope.t_Id) (steps: Prims.list Envelope.t_Id) : Lemma (requires Nickel.PastExact.member roots root) (ensures Prims.l_not (id_path h2 root steps fnew.f_id)) = never_reaches_new h2 fnew.f_id root steps in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 never_reaches)

let read_respects_sel (h: Seq.seq Nickel.Register.fact) (s1: Envelope.t_Id -> Type0) (s2: Envelope.t_Id -> Type0) (key: u64) (initial: t_Slice u8) (value: t_Slice u8) : Lemma (requires forall(id: Envelope.t_Id). s1 id <==> s2 id) (ensures causal_read_in h s1 key initial value <==> causal_read_in h s2 key initial value) =
  assert (forall(g: Nickel.Register.fact). maximal_in h s1 key g <==> maximal_in h s2 key g)

let observation_kept (h: Seq.seq Nickel.Register.fact) (h2: Seq.seq Nickel.Register.fact) (fnew: Nickel.Register.fact) (initial: t_Slice u8) (g: Nickel.Register.fact) : Lemma (requires (Prims.l_and (extends_by h h2 fnew) (unreferenced h2 fnew.f_id) /\ stored h2 g /\ observation_ok h initial g)) (ensures observation_ok h2 initial g) =
  ancestry_unchanged_by_extension h h2 fnew (Alloc.Vec.impl_1__as_slice g.f_after);
  read_unchanged_by_extension h h2 fnew (anc_of h2 g) g.f_payload.f_key initial (Alloc.Vec.impl_1__as_slice g.f_payload.f_observed);
  read_respects_sel h (anc_of h2 g) (anc_of h g) g.f_payload.f_key initial (Alloc.Vec.impl_1__as_slice g.f_payload.f_observed)

let observations_preserved (h: Seq.seq Nickel.Register.fact) (h2: Seq.seq Nickel.Register.fact) (fnew: Nickel.Register.fact) (initial: t_Slice u8) : Lemma (requires (Prims.l_and (extends_by h h2 fnew) (unreferenced h2 fnew.f_id) /\ Prims.l_and (observations_ok h initial) (observation_ok h initial fnew))) (ensures observations_ok h2 initial) =
  let each (g: Nickel.Register.fact) : Lemma (requires stored h2 g) (ensures observation_ok h2 initial g) = observation_kept h h2 fnew initial g in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each)

let selected_read_is_observation (before: Native.t_Replica) (offered: Nickel.Register.fact) (selected: Alloc.Vec.t_Vec Envelope.t_Id Alloc.Alloc.t_Global) : Lemma (requires ((forall(id: Envelope.t_Id). Nickel.PastExact.member (Alloc.Vec.impl_1__as_slice selected) id <==> Nickel.PastExact.ancestor Native.v_OPS._1 (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice offered.f_after) id) /\ frozen_id_read before offered selected)) (ensures Prims.l_and (stored_unique (Alloc.Vec.impl_1__as_slice before.f_facts)) (id_clocks_increase (Alloc.Vec.impl_1__as_slice before.f_facts)) ==> observation_ok (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice before.f_initial) offered) =
  let facts = Alloc.Vec.impl_1__as_slice before.f_facts in
  FStar.Classical.forall_intro (register_ancestor_is_id_ancestor facts (Alloc.Vec.impl_1__as_slice offered.f_after));
  read_respects_sel facts (sel_of selected) (anc_of facts offered) offered.f_payload.f_key (Alloc.Vec.impl_1__as_slice before.f_initial) (Alloc.Vec.impl_1__as_slice offered.f_payload.f_observed)

let offered_observation_ok (before: Native.t_Replica) (offered: Nickel.Register.fact) : Type0 =
  Prims.l_and (stored_unique (Alloc.Vec.impl_1__as_slice before.f_facts)) (id_clocks_increase (Alloc.Vec.impl_1__as_slice before.f_facts)) ==> observation_ok (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice before.f_initial) offered

let id_frozen_gives_observation (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (requires id_frozen_admission before offered) (ensures offered_observation_ok before offered) =
  FStar.Classical.forall_intro (FStar.Classical.move_requires (selected_read_is_observation before offered));
  assert (offered_observation_ok before offered) by (
    Tactics.prune "Nickel_crdt.Event_layer.validate_event";
    Tactics.smt_sync' 1 1
  )

let observations_carried (before: Native.t_Replica) (offered: Nickel.Register.fact) (next: Native.t_Replica) : Type0 =
  Prims.l_and (Prims.l_and (Prims.l_and (observations_ok (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice before.f_initial)) (stored_unique (Alloc.Vec.impl_1__as_slice before.f_facts))) (id_clocks_increase (Alloc.Vec.impl_1__as_slice before.f_facts))) (unreferenced (Alloc.Vec.impl_1__as_slice next.f_facts) offered.f_id) ==> observations_ok (Alloc.Vec.impl_1__as_slice next.f_facts) (Alloc.Vec.impl_1__as_slice before.f_initial)

let carried_from_parts (before: Native.t_Replica) (offered: Nickel.Register.fact) (next: Native.t_Replica) : Lemma (requires (Nickel.Register.appended_facts before offered next /\ offered_observation_ok before offered)) (ensures observations_carried before offered next) =
  let h = Alloc.Vec.impl_1__as_slice before.f_facts in
  let h2 = Alloc.Vec.impl_1__as_slice next.f_facts in
  assert (extends_by h h2 offered);
  FStar.Classical.move_requires (observations_preserved h h2 offered) (Alloc.Vec.impl_1__as_slice before.f_initial)

let receive_added_carries_observations (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (ensures forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> observations_carried before offered next) =
  receive_added_freezes_id_read before offered;
  Nickel.Register.receive_added_retains_exact_facts before offered;
  FStar.Classical.move_requires (id_frozen_gives_observation before) offered;
  FStar.Classical.forall_intro (FStar.Classical.move_requires (carried_from_parts before offered));
  assert (forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> observations_carried before offered next) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel_crdt.Register.next_lamport";
    Tactics.prune "Nickel_crdt.Event_layer.validate_event";
    Tactics.prune "Nickel_crdt.Event_layer.select_basis";
    Tactics.smt_sync' 1 1
  )

let rec lookup_none_misses (#f: Type0) (#i: Type0) (facts: t_Slice f) (fact: f) (id: f -> i) (eq: i -> i -> bool) (same: f -> f -> bool) (at: usize{v at <= v (Core_models.Slice.impl__len facts)}) : Lemma (requires Nickel.EventClassifier.lookup facts fact id eq same at == Option.Option_None) (ensures forall(k: nat). Prims.l_and (v at <= k) (k < Seq.length facts) ==> eq (id (Seq.index facts k)) (id fact) == false) (decreases v (Core_models.Slice.impl__len facts) - v at) =
  if v at < v (Core_models.Slice.impl__len facts) then
    begin lookup_none_misses facts fact id eq same (at +! mk_usize 1) end
  else
    begin () end

let fresh_id (before: Native.t_Replica) (offered: Nickel.Register.fact) : Type0 =
  forall(g: Nickel.Register.fact). stored (Alloc.Vec.impl_1__as_slice before.f_facts) g ==> g.f_id =!= offered.f_id

let not_duplicate_is_fresh (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (requires Native.duplicate () before offered == Result.Result_Ok false) (ensures fresh_id before offered) =
  let facts = Alloc.Vec.impl_1__as_slice before.f_facts in
  register_ops_are_exact ();
  let classify_shape () : Lemma (ensures Prims.l_or (Prims.l_or (Nickel_crdt.Event_layer.classify facts offered Native.v_OPS._1 == Option.Option_None) (Nickel_crdt.Event_layer.classify facts offered Native.v_OPS._1 == Option.Option_Some true)) (Nickel_crdt.Event_layer.classify facts offered Native.v_OPS._1 == Option.Option_Some false)) = match Nickel_crdt.Event_layer.classify facts offered Native.v_OPS._1 with | Option.Option_None -> begin () end | Option.Option_Some _ -> begin () end in
  classify_shape ();
  assert (Nickel_crdt.Event_layer.classify facts offered Native.v_OPS._1 == Option.Option_None) by (
    Tactics.prune "Nickel_crdt.Event_layer.classify";
    Tactics.smt_sync' 1 1
  );
  Nickel.EventClassifier.classification_is_exact facts offered Native.v_OPS._1;
  assert (Nickel.EventClassifier.lookup facts offered Native.v_OPS._1._1._1 Native.v_OPS._1._1._3 Native.v_OPS._1._1._6 (mk_usize 0) == Option.Option_None) by (
    Tactics.prune "Nickel_crdt.Event_layer.classify";
    Tactics.smt_sync' 1 1
  );
  lookup_none_misses facts offered Native.v_OPS._1._1._1 Native.v_OPS._1._1._3 Native.v_OPS._1._1._6 (mk_usize 0)

let planned_offer_is_fresh (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (ensures forall(next: Native.t_Replica). Native.planned () before offered == Result.Result_Ok (Option.Option_Some next) ==> fresh_id before offered) =
  Nickel.Register.shared_success_stages before offered () Native.duplicate Native.validate Native.prepare Native.execute;
  FStar.Classical.move_requires (not_duplicate_is_fresh before) offered;
  assert (forall(next: Native.t_Replica). Native.planned () before offered == Result.Result_Ok (Option.Option_Some next) ==> fresh_id before offered) by (
    Tactics.prune "Nickel_crdt.Event_shell.plan";
    Tactics.prune "Nickel_crdt.Register.duplicate";
    Tactics.smt_sync' 1 1
  )

let present_prefix (ops: Nickel.RegisterPast.rops) (facts: t_Slice Nickel.Register.fact) (after: t_Slice Envelope.t_Id) (at: nat) : Type0 =
  forall(j: nat). Prims.l_and (j < at) (j < Seq.length after) ==> Nickel_crdt.Event_layer.has_fact facts (Seq.index after j) ops == true

let validate_after_checks_presence (ops: Nickel.RegisterPast.rops) (facts: t_Slice Nickel.Register.fact) (after: t_Slice Envelope.t_Id) : Lemma (ensures Nickel.LoopUtil.result_safe (fun (_: unit) -> present_prefix ops facts after (Seq.length after)) (fun (_: Native.t_Error) -> Prims.l_True) (Nickel_crdt.Event_layer.validate_after facts after ops)) =
  Nickel.PastExact.ops_shape ops;
  let membership_boolean (wanted: Envelope.t_Id) : Lemma (ensures Prims.l_or (Nickel_crdt.Event_layer.has_fact facts wanted ops == true) (Nickel_crdt.Event_layer.has_fact facts wanted ops == false)) = () in
  FStar.Classical.forall_intro membership_boolean;
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len after) (fun (at: nat) (_: unit) -> present_prefix ops facts after at) (fun (_: unit) -> ()) (fun (_: unit) -> present_prefix ops facts after (Seq.length after)) (fun (_: Native.t_Error) -> Prims.l_True);
  assert (Nickel.LoopUtil.result_safe (fun (_: unit) -> present_prefix ops facts after (Seq.length after)) (fun (_: Native.t_Error) -> Prims.l_True) (Nickel_crdt.Event_layer.validate_after facts after ops)) by (
    Tactics.prune "Nickel_crdt.Event_layer.has_fact";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel.LoopUtil.step_safe";
    Tactics.prune "Nickel.LoopUtil.output_safe";
    Tactics.smt_sync' 1 1
  )

let past_checked_parents (ops: Nickel.RegisterPast.rops) (facts: t_Slice Nickel.Register.fact) (roots: t_Slice Envelope.t_Id) : Lemma (ensures forall(s: Nickel.RegisterPast.ids_vec). Nickel_crdt.Event_layer.past facts roots ops == Result.Result_Ok s ==> Nickel_crdt.Event_layer.validate_after facts roots ops == Result.Result_Ok ()) =
  Nickel.PastExact.ops_shape ops;
  let result_shape () : Lemma (ensures Prims.l_or (Nickel_crdt.Event_layer.validate_after facts roots ops == Result.Result_Ok ()) (exists(e: Native.t_Error). Nickel_crdt.Event_layer.validate_after facts roots ops == Result.Result_Err e)) = match Nickel_crdt.Event_layer.validate_after facts roots ops with | Result.Result_Ok _ -> begin () end | Result.Result_Err _ -> begin () end in
  result_shape ();
  assert (forall(s: Nickel.RegisterPast.ids_vec). Nickel_crdt.Event_layer.past facts roots ops == Result.Result_Ok s ==> Nickel_crdt.Event_layer.validate_after facts roots ops == Result.Result_Ok ()) by (
    Tactics.prune "Nickel_crdt.Event_layer.validate_after";
    Tactics.prune "Nickel_crdt.Event_layer.past_pass";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.smt_sync' 1 1
  )

let parents_stored (before: Native.t_Replica) (offered: Nickel.Register.fact) : Type0 =
  forall(p: Envelope.t_Id). Nickel.PastExact.member (Alloc.Vec.impl_1__as_slice offered.f_after) p ==> (exists(g: Nickel.Register.fact). Prims.l_and (stored (Alloc.Vec.impl_1__as_slice before.f_facts) g) (g.f_id == p))

let present_parents_are_stored (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (requires present_prefix Native.v_OPS._1 (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice offered.f_after) (Seq.length (Alloc.Vec.impl_1__as_slice offered.f_after))) (ensures parents_stored before offered) =
  let facts = Alloc.Vec.impl_1__as_slice before.f_facts in
  register_ops_are_exact ();
  let each (p: Envelope.t_Id) : Lemma (requires Nickel.PastExact.member (Alloc.Vec.impl_1__as_slice offered.f_after) p) (ensures exists(g: Nickel.Register.fact). Prims.l_and (stored facts g) (g.f_id == p)) = Nickel.EventGraph.fact_membership_is_exact facts p Native.v_OPS._1 in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each)

let validated_parents_stored (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (ensures forall(s: Nickel.RegisterPast.ids_vec). Nickel_crdt.Event_layer.validate_event (Alloc.Vec.impl_1__as_slice before.f_facts) offered before.f_limits.f_events before.f_limits.f_dependencies Native.v_OPS == Result.Result_Ok s ==> parents_stored before offered) =
  let facts = Alloc.Vec.impl_1__as_slice before.f_facts in
  let roots = Alloc.Vec.impl_1__as_slice offered.f_after in
  register_ops_are_exact ();
  Nickel.PastExact.validated_selection_is_past facts offered before.f_limits.f_events before.f_limits.f_dependencies Native.v_OPS;
  past_checked_parents Native.v_OPS._1 facts roots;
  validate_after_checks_presence Native.v_OPS._1 facts roots;
  FStar.Classical.move_requires (present_parents_are_stored before) offered;
  assert (forall(s: Nickel.RegisterPast.ids_vec). Nickel_crdt.Event_layer.validate_event facts offered before.f_limits.f_events before.f_limits.f_dependencies Native.v_OPS == Result.Result_Ok s ==> parents_stored before offered) by (
    Tactics.prune "Nickel_crdt.Event_layer.validate_event";
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.prune "Nickel_crdt.Event_layer.validate_after";
    Tactics.smt_sync' 1 1
  )

let closed (h: Seq.seq Nickel.Register.fact) : Type0 =
  forall(g: Nickel.Register.fact) (p: Envelope.t_Id). Prims.l_and (stored h g) (Nickel.PastExact.member (Alloc.Vec.impl_1__as_slice g.f_after) p) ==> (exists(k: Nickel.Register.fact). Prims.l_and (stored h k) (k.f_id == p))

let receive_added_offer_is_fresh (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (ensures forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> fresh_id before offered) =
  Nickel.Register.receive_publication_is_exact before offered;
  planned_offer_is_fresh before offered;
  match Native.planned () before offered with | Result.Result_Err _ -> begin assert (forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> fresh_id before offered) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.smt_sync' 1 1
  ) end | Result.Result_Ok option -> begin match option with | Option.Option_None -> begin assert (forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> fresh_id before offered) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.smt_sync' 1 1
  ) end | Option.Option_Some candidate -> begin assert (forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> fresh_id before offered) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.smt_sync' 1 1
  ) end end

let receive_added_parents_stored (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (ensures forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> parents_stored before offered) =
  Nickel.Register.receive_added_checks_payload before offered;
  validated_parents_stored before offered;
  assert (forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> parents_stored before offered) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel_crdt.Event_layer.validate_event";
    Tactics.prune "Nickel_crdt.Event_layer.select_basis";
    Tactics.smt_sync' 1 1
  )

let closure_gives_unreferenced (h: Seq.seq Nickel.Register.fact) (h2: Seq.seq Nickel.Register.fact) (fnew: Nickel.Register.fact) : Lemma (requires (Prims.l_and (extends_by h h2 fnew) (closed h) /\ (forall(g: Nickel.Register.fact). stored h g ==> g.f_id =!= fnew.f_id) /\ (forall(p: Envelope.t_Id). Nickel.PastExact.member (Alloc.Vec.impl_1__as_slice fnew.f_after) p ==> (exists(k: Nickel.Register.fact). Prims.l_and (stored h k) (k.f_id == p))))) (ensures Prims.l_and (unreferenced h2 fnew.f_id) (closed h2)) =
  ()

let history_extended_soundly (before: Native.t_Replica) (offered: Nickel.Register.fact) (next: Native.t_Replica) : Type0 =
  closed (Alloc.Vec.impl_1__as_slice before.f_facts) ==> Prims.l_and (unreferenced (Alloc.Vec.impl_1__as_slice next.f_facts) offered.f_id) (closed (Alloc.Vec.impl_1__as_slice next.f_facts))

let extended_from_parts (before: Native.t_Replica) (offered: Nickel.Register.fact) (next: Native.t_Replica) : Lemma (requires Prims.l_and (Prims.l_and (Nickel.Register.appended_facts before offered next) (fresh_id before offered)) (parents_stored before offered)) (ensures history_extended_soundly before offered next) =
  let h = Alloc.Vec.impl_1__as_slice before.f_facts in
  let h2 = Alloc.Vec.impl_1__as_slice next.f_facts in
  assert (extends_by h h2 offered);
  FStar.Classical.move_requires (closure_gives_unreferenced h h2) offered

let receive_added_extends_soundly (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (ensures forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> history_extended_soundly before offered next) =
  Nickel.Register.receive_added_retains_exact_facts before offered;
  receive_added_offer_is_fresh before offered;
  receive_added_parents_stored before offered;
  FStar.Classical.forall_intro (FStar.Classical.move_requires (extended_from_parts before offered));
  assert (forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> history_extended_soundly before offered next) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.smt_sync' 1 1
  )

let observation_invariant (r: Native.t_Replica) : Type0 =
  Prims.l_and (Prims.l_and (Prims.l_and (stored_unique (Alloc.Vec.impl_1__as_slice r.f_facts)) (id_clocks_increase (Alloc.Vec.impl_1__as_slice r.f_facts))) (closed (Alloc.Vec.impl_1__as_slice r.f_facts))) (observations_ok (Alloc.Vec.impl_1__as_slice r.f_facts) (Alloc.Vec.impl_1__as_slice r.f_initial))

let observations_kept_on (before: Native.t_Replica) (next: Native.t_Replica) : Type0 =
  observation_invariant before ==> Prims.l_and (closed (Alloc.Vec.impl_1__as_slice next.f_facts)) (observations_ok (Alloc.Vec.impl_1__as_slice next.f_facts) (Alloc.Vec.impl_1__as_slice next.f_initial))

let kept_from_parts (before: Native.t_Replica) (offered: Nickel.Register.fact) (next: Native.t_Replica) : Lemma (requires (Prims.l_and (observations_carried before offered next) (history_extended_soundly before offered next) /\ Nickel.Register.private_frame before next)) (ensures observations_kept_on before next) =
  ()

let receive_added_keeps_observations (before: Native.t_Replica) (offered: Nickel.Register.fact) : Lemma (ensures forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> observations_kept_on before next) =
  receive_added_carries_observations before offered;
  receive_added_extends_soundly before offered;
  Nickel.Register.receive_preserves_private before offered;
  FStar.Classical.forall_intro (FStar.Classical.move_requires (kept_from_parts before offered));
  assert (forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> observations_kept_on before next) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.smt_sync' 1 1
  )