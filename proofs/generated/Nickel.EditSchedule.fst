(* Latte generated F* view *)
module Nickel.EditSchedule

open Nickel.Prelude

open Rust_primitives

open Core_models

open FStar.Pervasives

open Nickel.Vector

open Nickel.LoopUtil

open Nickel.EditPast

module Native = Nickel_crdt.Edit

module Seq = FStar.Seq

module Option = Core_models.Option

let ready_prefix (after: t_Slice Native.t_EventId) (done: t_Slice Native.t_EventId) (finish: nat) : Type0 =
  forall(i: usize{v i < Seq.length after}). v i < finish ==> member done (Seq.index after (v i))

let readiness_is_exact (after: t_Slice Native.t_EventId) (done: t_Slice Native.t_EventId) : Lemma (ensures Native.ready after done == true <==> all_ids after (member done)) [SMTPat (Native.ready after done)] =
  Nickel.LoopUtil.preserve_any (mk_usize 0) (Core_models.Slice.impl__len after) (fun (at: nat) (_: unit) -> ready_prefix after done at) (fun (_: unit) -> all_ids after (member done)) (fun (b: bool) -> Prims.l_and (b == false) (Prims.l_not (all_ids after (member done))));
  assert (Native.ready after done == true <==> all_ids after (member done)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel_crdt.Edit.has_event";
    Tactics.smt_sync' 1 1
  )

let eligible (facts: t_Slice Native.t_Fact) (done: t_Slice Native.t_EventId) (i: nat{i < Seq.length facts}) : Type0 =
  Prims.l_and (Prims.l_not (member done (Seq.index facts i).f_id)) (all_ids (Alloc.Vec.impl_1__as_slice (Seq.index facts i).f_after) (member done))

let no_eligible_prefix (facts: t_Slice Native.t_Fact) (done: t_Slice Native.t_EventId) (finish: nat) : Type0 =
  forall(i: usize{v i < Seq.length facts}). v i < finish ==> Prims.l_not (eligible facts done (v i))

let chosen_is_first (facts: t_Slice Native.t_Fact) (done: t_Slice Native.t_EventId) (result: Option.t_Option usize) : Type0 =
  match result with | Option.Option_None -> begin no_eligible_prefix facts done (Seq.length facts) end | Option.Option_Some i -> begin Prims.l_and (v i < Seq.length facts) (Prims.l_and (v i < Seq.length facts ==> eligible facts done (v i)) (no_eligible_prefix facts done (v i))) end

let scheduler_choice_is_exact (facts: t_Slice Native.t_Fact) (done: t_Slice Native.t_EventId) : Lemma (ensures chosen_is_first facts done (Native.choose_ready facts done)) =
  Nickel.LoopUtil.preserve_any (mk_usize 0) (Core_models.Slice.impl__len facts) (fun (at: nat) (_: unit) -> no_eligible_prefix facts done at) (fun (_: unit) -> no_eligible_prefix facts done (Seq.length facts)) (chosen_is_first facts done);
  assert (chosen_is_first facts done (Native.choose_ready facts done)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel_crdt.Edit.has_event";
    Tactics.prune "Nickel_crdt.Edit.ready";
    Tactics.smt_sync' 1 1
  )

let available_event_is_chosen (facts: t_Slice Native.t_Fact) (done: t_Slice Native.t_EventId) (available: usize{v available < Seq.length facts}) : Lemma (requires eligible facts done (v available)) (ensures Prims.l_not (Native.choose_ready facts done == Option.Option_None)) =
  scheduler_choice_is_exact facts done;
  assert (Prims.l_not (Native.choose_ready facts done == Option.Option_None)) by (
    Tactics.prune "Nickel_crdt.Edit.choose_ready";
    Tactics.smt_sync' 1 1
  )

open Nickel.EditCausal

open Nickel.EditAccepted

open Nickel.EditWellFormed

open FStar.Classical

open FStar.Fin

let ranked_prefix_done (facts: facts_vec) (done: t_Slice Native.t_EventId) (rank: Native.t_EventId -> nat) (finish: nat) : Type0 =
  forall(i: usize{v i < Seq.length (Alloc.Vec.impl_1__as_slice facts)}). rank (Seq.index (Alloc.Vec.impl_1__as_slice facts) (v i)).f_id < finish ==> member done (Seq.index (Alloc.Vec.impl_1__as_slice facts) (v i)).f_id

let rec no_choice_finishes_lower_ranks (facts: facts_vec) (done: t_Slice Native.t_EventId) (rank: Native.t_EventId -> nat) (bound: nat) (finish: nat) : Lemma (requires (causal_rank facts rank bound /\ no_eligible_prefix (Alloc.Vec.impl_1__as_slice facts) done (Seq.length (Alloc.Vec.impl_1__as_slice facts)))) (ensures ranked_prefix_done facts done rank finish) (decreases finish) =
  if finish ==? 0 then
    begin () end
  else
    begin no_choice_finishes_lower_ranks facts done rank bound (finish - 1);
    let input = Alloc.Vec.impl_1__as_slice facts in
    let each (i: usize{v i < Seq.length input}) : Lemma (ensures rank (Seq.index input (v i)).f_id < finish ==> member done (Seq.index input (v i)).f_id) =
      let fact = Seq.index input (v i) in
      if rank fact.f_id < finish then
        begin assert (fact_present input fact);
        let dependency (j: usize{v j < Seq.length (Alloc.Vec.impl_1__as_slice fact.f_after)}) : Lemma (ensures member done (Seq.index (Alloc.Vec.impl_1__as_slice fact.f_after) (v j))) =
          let id = Seq.index (Alloc.Vec.impl_1__as_slice fact.f_after) (v j) in
          assert (rank id < rank fact.f_id);
          assert (fact_id_present facts id);
          let position = parent_fact_position facts id in
          assert (rank (Seq.index input position).f_id < finish - 1);
          assert (member done (Seq.index input (v (mk_usize position))).f_id) by (
            Tactics.prune "Nickel.EditSchedule.no_eligible_prefix";
            Tactics.smt_sync' 1 1
          );
          assert (member done id) in
        FStar.Classical.forall_intro dependency;
        assert (all_ids (Alloc.Vec.impl_1__as_slice fact.f_after) (member done));
        assert (Prims.l_not (eligible input done (v i)));
        assert (member done fact.f_id) end
      else
        begin () end in
    FStar.Classical.forall_intro each;
    assert (ranked_prefix_done facts done rank finish) end

let ranked_unfinished_has_eligible (facts: facts_vec) (done: t_Slice Native.t_EventId) (rank: Native.t_EventId -> nat) (bound: nat) (unfinished: usize{v unfinished < Seq.length (Alloc.Vec.impl_1__as_slice facts)}) : Lemma (requires (causal_rank facts rank bound /\ Prims.l_not (member done (Seq.index (Alloc.Vec.impl_1__as_slice facts) (v unfinished)).f_id))) (ensures Prims.l_not (no_eligible_prefix (Alloc.Vec.impl_1__as_slice facts) done (Seq.length (Alloc.Vec.impl_1__as_slice facts)))) =
  let input = Alloc.Vec.impl_1__as_slice facts in
  let impossible (dummy: unit) : Lemma (requires no_eligible_prefix input done (Seq.length input)) (ensures Prims.l_False) =
    no_choice_finishes_lower_ranks facts done rank bound bound;
    assert (fact_present input (Seq.index input (v unfinished)));
    assert (rank (Seq.index input (v unfinished)).f_id < bound);
    assert (member done (Seq.index input (v unfinished)).f_id) by (
      Tactics.prune "Nickel.EditSchedule.no_eligible_prefix";
      Tactics.smt_sync' 1 1
    );
    assert Prims.l_False in
  FStar.Classical.move_requires impossible ()

let all_stored_done (facts: t_Slice Native.t_Fact) (done: t_Slice Native.t_EventId) : Type0 =
  forall(i: FStar.Fin.under (Seq.length facts)). member done (Seq.index facts i).f_id

let done_position (done: t_Slice Native.t_EventId) (id: Native.t_EventId{member done id}) : i: FStar.Fin.under (Seq.length done){Seq.index done i == id} =
  match FStar.Fin.find done (fun (item: Native.t_EventId) -> item ==? id) 0 with | Some i -> begin i end | None -> begin 0 end

let shorter_done_is_unfinished (facts: t_Slice Native.t_Fact) (done: t_Slice Native.t_EventId) : Lemma (requires (Nickel.EditIdentity.unique_ids facts /\ Seq.length done < Seq.length facts)) (ensures Prims.l_not (all_stored_done facts done)) =
  let impossible (dummy: unit) : Lemma (requires all_stored_done facts done) (ensures Prims.l_False) = if Seq.length done ==? 0 then
    begin assert (member done (Seq.index facts 0).f_id);
    assert (absent_prefix done (Seq.index facts 0).f_id 0);
    assert Prims.l_False end
  else
    begin let position = fun (i: nat{i < Seq.length done + 1}) -> done_position done (Seq.index facts i).f_id in
    let positions = Seq.init (Seq.length done + 1) position in
    Seq.lemma_init_len (Seq.length done + 1) position;
    Seq.init_index (Seq.length done + 1) position;
    match FStar.Fin.pigeonhole positions with | (i, j) -> begin assert (Prims.l_and (i < j) (j < Seq.length facts));
    assert (position i == position j);
    assert ((Seq.index facts i).f_id == (Seq.index facts j).f_id);
    unique_slice_nat_positions facts i j;
    assert (i == j) end end in
  FStar.Classical.move_requires impossible ()

let ranked_incomplete_has_eligible (facts: facts_vec) (done: t_Slice Native.t_EventId) (rank: Native.t_EventId -> nat) (bound: nat) : Lemma (requires (causal_rank facts rank bound /\ ids_unique facts /\ Seq.length done < Seq.length (Alloc.Vec.impl_1__as_slice facts))) (ensures Prims.l_not (no_eligible_prefix (Alloc.Vec.impl_1__as_slice facts) done (Seq.length (Alloc.Vec.impl_1__as_slice facts)))) =
  let input = Alloc.Vec.impl_1__as_slice facts in
  let impossible (dummy: unit) : Lemma (requires no_eligible_prefix input done (Seq.length input)) (ensures Prims.l_False) =
    no_choice_finishes_lower_ranks facts done rank bound bound;
    let each (i: FStar.Fin.under (Seq.length input)) : Lemma (ensures member done (Seq.index input i).f_id) =
      assert (fact_present input (Seq.index input i));
      assert (rank (Seq.index input i).f_id < bound);
      assert (member done (Seq.index input (v (mk_usize i))).f_id) by (
        Tactics.prune "Nickel.EditSchedule.no_eligible_prefix";
        Tactics.smt_sync' 1 1
      ) in
    FStar.Classical.forall_intro each;
    assert (all_stored_done input done);
    shorter_done_is_unfinished input done;
    assert Prims.l_False in
  FStar.Classical.move_requires impossible ()

let ranked_incomplete_scan_progress (facts: facts_vec) (done: t_Slice Native.t_EventId) (rank: Native.t_EventId -> nat) (bound: nat) : Lemma (requires (causal_rank facts rank bound /\ ids_unique facts /\ Seq.length done < Seq.length (Alloc.Vec.impl_1__as_slice facts))) (ensures Prims.l_not (Native.choose_ready (Alloc.Vec.impl_1__as_slice facts) done == Option.Option_None)) =
  let input = Alloc.Vec.impl_1__as_slice facts in
  ranked_incomplete_has_eligible facts done rank bound;
  scheduler_choice_is_exact input done;
  assert (Prims.l_not (Native.choose_ready input done == Option.Option_None)) by (
    Tactics.prune "Nickel_crdt.Edit.choose_ready";
    Tactics.smt_sync' 1 1
  )