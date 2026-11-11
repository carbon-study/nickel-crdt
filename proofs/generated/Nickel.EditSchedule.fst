(* Latte generated F* view *)
module Nickel.EditSchedule

open Nickel.Prelude

module Shared = Nickel_crdt.Event_layer

module Graph = Nickel.EventGraph

open Nickel.EventGraphText

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
  Nickel.EventGraphText.text_graph_policy_is_exact ();
  Nickel.EventGraphText.text_graph_callbacks_are_exact ();
  assert (Shared.ready after done (Nickel.EventGraphText.text_graph_ops ()) == Native.ready after done) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.smt_sync' 1 1
  );
  Graph.readiness_is_exact after done (Nickel.EventGraphText.text_graph_ops ());
  assert (Native.ready after done == true <==> all_ids after (member done)) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.prune "Nickel_crdt.Edit.ready";
    Tactics.prune "Nickel_crdt.Event_layer.ready";
    Tactics.smt_sync' 1 1
  )

let ready_is_text_call (after: t_Slice Native.t_EventId) (done: t_Slice Native.t_EventId) : Lemma (ensures Shared.ready after done (Nickel.EventGraphText.text_graph_ops ()) == Native.ready after done) [SMTPat (Shared.ready after done (Nickel.EventGraphText.text_graph_ops ()))] =
  Nickel.EventGraphText.text_graph_policy_is_exact ();
  assert (Shared.ready after done (Nickel.EventGraphText.text_graph_ops ()) == Native.ready after done) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.smt_sync' 1 1
  )

let eligible (facts: t_Slice Native.t_Fact) (done: t_Slice Native.t_EventId) (i: nat{i < Seq.length facts}) : Type0 =
  Prims.l_and (Prims.l_not (member done (Seq.index facts i).f_id)) (all_ids (Alloc.Vec.impl_1__as_slice (Seq.index facts i).f_after) (member done))

let no_eligible_prefix (facts: t_Slice Native.t_Fact) (done: t_Slice Native.t_EventId) (finish: nat) : Type0 =
  forall(i: usize{v i < Seq.length facts}). v i < finish ==> Prims.l_not (eligible facts done (v i))

let chosen_is_first (facts: t_Slice Native.t_Fact) (done: t_Slice Native.t_EventId) (result: Option.t_Option usize) : Type0 =
  match result with | Option.Option_None -> begin no_eligible_prefix facts done (Seq.length facts) end | Option.Option_Some i -> begin Prims.l_and (v i < Seq.length facts) (Prims.l_and (v i < Seq.length facts ==> eligible facts done (v i)) (no_eligible_prefix facts done (v i))) end

let scheduler_choice_is_exact (facts: t_Slice Native.t_Fact) (done: t_Slice Native.t_EventId) : Lemma (ensures chosen_is_first facts done (Native.choose_ready facts done)) =
  Nickel.EventGraphText.text_graph_policy_is_exact ();
  Nickel.EventGraphText.text_graph_callbacks_are_exact ();
  assert (Shared.choose_ready facts done (Nickel.EventGraphText.text_graph_ops ()) == Native.choose_ready facts done) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.smt_sync' 1 1
  );
  Graph.scheduler_choice_is_exact facts done (Nickel.EventGraphText.text_graph_ops ());
  assert (chosen_is_first facts done (Native.choose_ready facts done)) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.prune "Nickel_crdt.Edit.choose_ready";
    Tactics.prune "Nickel_crdt.Event_layer.choose_ready";
    Tactics.smt_sync' 1 1
  )

let choose_ready_is_text_call (facts: t_Slice Native.t_Fact) (done: t_Slice Native.t_EventId) : Lemma (ensures Shared.choose_ready facts done (Nickel.EventGraphText.text_graph_ops ()) == Native.choose_ready facts done) [SMTPat (Shared.choose_ready facts done (Nickel.EventGraphText.text_graph_ops ()))] =
  Nickel.EventGraphText.text_graph_policy_is_exact ();
  assert (Shared.choose_ready facts done (Nickel.EventGraphText.text_graph_ops ()) == Native.choose_ready facts done) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.smt_sync' 1 1
  )

let available_event_is_chosen (facts: t_Slice Native.t_Fact) (done: t_Slice Native.t_EventId) (available: usize{v available < Seq.length facts}) : Lemma (requires eligible facts done (v available)) (ensures Prims.l_not (Native.choose_ready facts done == Option.Option_None)) =
  scheduler_choice_is_exact facts done;
  assert (Prims.l_not (Native.choose_ready facts done == Option.Option_None)) by (
    Tactics.prune "Nickel_crdt.Edit.choose_ready";
    Tactics.prune "Nickel_crdt.Event_layer.choose_ready";
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
    Tactics.prune "Nickel_crdt.Event_layer.choose_ready";
    Tactics.smt_sync' 1 1
  )

open Nickel.EditPastTotal

let causal_position (facts: t_Slice Native.t_Fact) (ids: t_Slice Native.t_EventId) (at: FStar.Fin.under (Seq.length ids)) : Type0 =
  exists(index: FStar.Fin.under (Seq.length facts)). Prims.l_and ((Seq.index facts index).f_id == Seq.index ids at) (all_ids (Alloc.Vec.impl_1__as_slice (Seq.index facts index).f_after) (fun (id: Native.t_EventId) -> Prims.l_not (absent_prefix ids id at)))

let causal_trace (facts: t_Slice Native.t_Fact) (ids: t_Slice Native.t_EventId) : Type0 =
  forall(at: FStar.Fin.under (Seq.length ids)). causal_position facts ids at

let append_retains_earlier (before: t_Slice Native.t_EventId) (id: Native.t_EventId) (wanted: Native.t_EventId) (finish: nat{finish <= Seq.length before}) : Lemma (requires (Seq.length before < max_usize /\ Prims.l_not (absent_prefix before wanted finish))) (ensures Prims.l_not (absent_prefix (Seq.append before (Seq.create 1 id)) wanted finish)) =
  let next = Seq.append before (Seq.create 1 id) in
  let impossible (dummy: unit) : Lemma (requires absent_prefix next wanted finish) (ensures Prims.l_False) =
    let each (i: usize{v i < Seq.length before}) : Lemma (ensures v i < finish ==> Prims.l_not (Seq.index before (v i) == wanted)) =
      assert (v i < Seq.length next);
      assert (Seq.index next (v i) == Seq.index before (v i));
      () in
    FStar.Classical.forall_intro each;
    assert (absent_prefix before wanted finish);
    () in
  FStar.Classical.forall_intro (FStar.Classical.move_requires impossible);
  ()

let eligible_append_keeps_causal_trace (facts: t_Slice Native.t_Fact) (before: t_Slice Native.t_EventId) (index: nat{index < Seq.length facts}) : Lemma (requires (Seq.length before < max_usize /\ causal_trace facts before /\ eligible facts before index)) (ensures causal_trace facts (Seq.append before (Seq.create 1 (Seq.index facts index).f_id))) =
  let fact = Seq.index facts index in
  let next = Seq.append before (Seq.create 1 fact.f_id) in
  let position (at: FStar.Fin.under (Seq.length next)) : Lemma (ensures causal_position facts next at) = if at < Seq.length before then
    begin assert (causal_position facts before at);
    let transfer (k: FStar.Fin.under (Seq.length facts)) : Lemma (requires ((Seq.index facts k).f_id == Seq.index before at /\ all_ids (Alloc.Vec.impl_1__as_slice (Seq.index facts k).f_after) (fun (id: Native.t_EventId) -> Prims.l_not (absent_prefix before id at)))) (ensures Prims.l_and ((Seq.index facts k).f_id == Seq.index next at) (all_ids (Alloc.Vec.impl_1__as_slice (Seq.index facts k).f_after) (fun (id: Native.t_EventId) -> Prims.l_not (absent_prefix next id at)))) =
      let dependency (j: usize{v j < Seq.length (Alloc.Vec.impl_1__as_slice (Seq.index facts k).f_after)}) : Lemma (ensures Prims.l_not (absent_prefix next (Seq.index (Alloc.Vec.impl_1__as_slice (Seq.index facts k).f_after) (v j)) at)) = append_retains_earlier before fact.f_id (Seq.index (Alloc.Vec.impl_1__as_slice (Seq.index facts k).f_after) (v j)) at in
      FStar.Classical.forall_intro dependency;
      () in
    FStar.Classical.forall_intro (FStar.Classical.move_requires transfer);
    () end
  else
    begin assert (at == Seq.length before);
    let dependency (j: usize{v j < Seq.length (Alloc.Vec.impl_1__as_slice fact.f_after)}) : Lemma (ensures Prims.l_not (absent_prefix next (Seq.index (Alloc.Vec.impl_1__as_slice fact.f_after) (v j)) at)) = append_retains_earlier before fact.f_id (Seq.index (Alloc.Vec.impl_1__as_slice fact.f_after) (v j)) at in
    FStar.Classical.forall_intro dependency;
    assert ((Seq.index facts index).f_id == Seq.index next at);
    assert (all_ids (Alloc.Vec.impl_1__as_slice (Seq.index facts index).f_after) (fun (id: Native.t_EventId) -> Prims.l_not (absent_prefix next id at)));
    () end in
  FStar.Classical.forall_intro position;
  ()

module Result = Core_models.Result

unfold type operations_vec = Alloc.Vec.t_Vec (Native.t_EventId & Alloc.Vec.t_Vec Native.t_Node Alloc.Alloc.t_Global) Alloc.Alloc.t_Global

unfold type schedule_state = ids_vec & operations_vec & Native.t_Tree

let schedule_done (state: schedule_state) : Native.t_Tree & ids_vec =
  match state with | (done, _, tree) -> begin (tree, done) end

let schedule_invariant (facts: t_Slice Native.t_Fact) (at: nat) (state: schedule_state) : Type0 =
  match state with | (done, _, _) -> begin Prims.l_and (Prims.l_and (Seq.length (Alloc.Vec.impl_1__as_slice done) == at) (unique_selection (Alloc.Vec.impl_1__as_slice done))) (causal_trace facts (Alloc.Vec.impl_1__as_slice done)) end

let complete_causal_trace (facts: t_Slice Native.t_Fact) (pair: Native.t_Tree & ids_vec) : Type0 =
  match pair with | (_, done) -> begin Prims.l_and (Prims.l_and (Seq.length (Alloc.Vec.impl_1__as_slice done) == Seq.length facts) (unique_selection (Alloc.Vec.impl_1__as_slice done))) (causal_trace facts (Alloc.Vec.impl_1__as_slice done)) end

let choice_keeps_trace (facts: t_Slice Native.t_Fact) (before: t_Slice Native.t_EventId{Seq.length before < max_usize}) : Type0 =
  match Native.choose_ready facts before with | Option.Option_None -> begin Prims.l_True end | Option.Option_Some index -> begin Prims.l_and (v index < Seq.length facts) (Prims.l_and (v index < Seq.length facts ==> unique_selection (Seq.append before (Seq.create 1 (Seq.index facts (v index)).f_id))) (causal_trace facts (Seq.append before (Seq.create 1 (Seq.index facts (v index)).f_id)))) end

let chosen_append_keeps_trace (facts: t_Slice Native.t_Fact) (before: t_Slice Native.t_EventId) : Lemma (requires (Seq.length before < max_usize /\ Prims.l_and (unique_selection before) (causal_trace facts before))) (ensures choice_keeps_trace facts before) [SMTPat (Native.choose_ready facts before)] =
  scheduler_choice_is_exact facts before;
  match Native.choose_ready facts before with | Option.Option_None -> begin () end | Option.Option_Some index -> begin if v index < Seq.length facts then
    begin eligible_append_keeps_causal_trace facts before (v index);
    fresh_append_is_unique before (Seq.index facts (v index)).f_id end
  else
    begin () end end

let empty_trace_is_valid (facts: t_Slice Native.t_Fact) : Lemma (ensures Prims.l_and (unique_selection Seq.empty) (causal_trace facts Seq.empty)) =
  ()

let successful_schedule_is_once_only_and_causal (facts: t_Slice Native.t_Fact) : Lemma (ensures Nickel.LoopUtil.result_safe (complete_causal_trace facts) (fun (_: Native.t_Error) -> Prims.l_True) (Native.interpret_scheduled facts)) =
  let event_shape (event: Native.t_Fact) (operations: t_Slice (Native.t_EventId & Alloc.Vec.t_Vec Native.t_Node Alloc.Alloc.t_Global)) (tree: Native.t_Tree) : Lemma (ensures result_shape (Native.interpret_event facts event operations tree)) [SMTPat (Native.interpret_event facts event operations tree)] = () in
  let choice_shape (done: t_Slice Native.t_EventId) : Lemma (ensures Prims.l_or (Native.choose_ready facts done == Option.Option_None) (exists(i: usize). Native.choose_ready facts done == Option.Option_Some i)) [SMTPat (Native.choose_ready facts done)] = () in
  empty_trace_is_valid facts;
  Nickel.Vector.empty_vector_contents #Native.t_EventId ();
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len facts) (schedule_invariant facts) schedule_done (complete_causal_trace facts) (fun (_: Native.t_Error) -> Prims.l_True);
  assert (Nickel.LoopUtil.result_safe (complete_causal_trace facts) (fun (_: Native.t_Error) -> Prims.l_True) (Native.interpret_scheduled facts)) by (
    Tactics.prune "Nickel.EditSchedule.causal_trace";
    Tactics.prune "Nickel_crdt.Edit.interpret_event";
    Tactics.prune "Nickel_crdt.Edit.choose_ready";
    Tactics.prune "Nickel_crdt.Event_layer.choose_ready";
    Tactics.prune "Nickel_crdt.Edit.push";
    Tactics.prune "Nickel_crdt.Event_layer.push";
    Tactics.prune "Nickel.LoopUtil.step_safe";
    Tactics.prune "Nickel.LoopUtil.output_safe";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.smt_sync' 1 1
  )

let causal_trace_uses_stored_ids (facts: facts_vec) (done: ids_vec) : Lemma (requires causal_trace (Alloc.Vec.impl_1__as_slice facts) (Alloc.Vec.impl_1__as_slice done)) (ensures all_ids (Alloc.Vec.impl_1__as_slice done) (fact_id_present facts)) =
  let input = Alloc.Vec.impl_1__as_slice facts in
  let ids = Alloc.Vec.impl_1__as_slice done in
  let each (at: usize{v at < Seq.length ids}) : Lemma (ensures fact_id_present facts (Seq.index ids (v at))) =
    assert (causal_position input ids (v at));
    assert (exists(index: FStar.Fin.under (Seq.length input)). Prims.l_and ((Seq.index input index).f_id == Seq.index ids (v at)) (all_ids (Alloc.Vec.impl_1__as_slice (Seq.index input index).f_after) (fun (id: Native.t_EventId) -> Prims.l_not (absent_prefix ids id (v at)))));
    assert (exists(index: FStar.Fin.under (Seq.length input)). (Seq.index input index).f_id == Seq.index ids (v at));
    let stored (index: FStar.Fin.under (Seq.length input)) : Lemma (requires (Seq.index input index).f_id == Seq.index ids (v at)) (ensures fact_id_present facts (Seq.index ids (v at))) =
      assert (fact_present input (Seq.index input index));
      () in
    FStar.Classical.forall_intro (FStar.Classical.move_requires stored);
    () in
  FStar.Classical.forall_intro each;
  ()

let full_trace_covers_storage (facts: t_Slice Native.t_Fact) (done: ids_vec) : Lemma (requires (Seq.length (Alloc.Vec.impl_1__as_slice done) == Seq.length facts /\ unique_selection (Alloc.Vec.impl_1__as_slice done) /\ causal_trace facts (Alloc.Vec.impl_1__as_slice done))) (ensures forall(i: FStar.Fin.under (Seq.length facts)). member (Alloc.Vec.impl_1__as_slice done) (Seq.index facts i).f_id) =
  let stored = Alloc.Vec.from_seq #Native.t_Fact #Alloc.Alloc.t_Global facts in
  Nickel.Vector.vector_from_seq #Native.t_Fact facts;
  causal_trace_uses_stored_ids stored done;
  let each (i: FStar.Fin.under (Seq.length facts)) : Lemma (ensures member (Alloc.Vec.impl_1__as_slice done) (Seq.index facts i).f_id) =
    let id = (Seq.index facts i).f_id in
    assert (fact_present facts (Seq.index facts i));
    assert (fact_id_present stored id);
    if Native.has_event (Alloc.Vec.impl_1__as_slice done) id then
      begin () end
    else
      begin missing_stored_id_leaves_room stored done id;
      assert (Prims.l_False) by (
        Tactics.prune "Nickel.EditSchedule.causal_trace";
        Tactics.prune "Nickel.EditPastTotal.unique_selection";
        Tactics.smt_sync' 1 1
      ) end in
  FStar.Classical.forall_intro each;
  ()

let erase_schedule (out: Result.t_Result (Native.t_Tree & ids_vec) Native.t_Error) : Result.t_Result Native.t_Tree Native.t_Error =
  match out with | Result.Result_Err error -> begin Result.Result_Err error end | Result.Result_Ok (tree, _) -> begin Result.Result_Ok tree end

let interpret_erases_only_schedule (facts: t_Slice Native.t_Fact) : Lemma (ensures Native.interpret facts == erase_schedule (Native.interpret_scheduled facts)) =
  let shape () : Lemma (ensures result_shape (Native.interpret_scheduled facts)) = () in
  shape ();
  assert (Native.interpret facts == erase_schedule (Native.interpret_scheduled facts)) by (
    Tactics.prune "Nickel_crdt.Edit.interpret_scheduled";
    Tactics.prune "Nickel_crdt.Event_shell.scheduled";
    Tactics.smt_sync' 1 1
  )

let interpretation_schedule (facts: t_Slice Native.t_Fact) (tree: Native.t_Tree) : Type0 =
  exists(done: ids_vec). Prims.l_and (Prims.l_and (Native.interpret_scheduled facts == Result.Result_Ok (tree, done)) (complete_causal_trace facts (tree, done))) (forall(i: FStar.Fin.under (Seq.length facts)). member (Alloc.Vec.impl_1__as_slice done) (Seq.index facts i).f_id)

let successful_interpretation_has_causal_schedule (facts: t_Slice Native.t_Fact) (tree: Native.t_Tree) : Lemma (requires Native.interpret facts == Result.Result_Ok tree) (ensures interpretation_schedule facts tree) =
  successful_schedule_is_once_only_and_causal facts;
  interpret_erases_only_schedule facts;
  let each (done: ids_vec) : Lemma (requires (Native.interpret_scheduled facts == Result.Result_Ok (tree, done) /\ complete_causal_trace facts (tree, done))) (ensures interpretation_schedule facts tree) =
    full_trace_covers_storage facts done;
    assert (interpretation_schedule facts tree) by (
      Tactics.prune "Nickel_crdt.Edit.interpret";
      Tactics.prune "Nickel_crdt.Edit.interpret_scheduled";
      Tactics.prune "Nickel_crdt.Event_shell.scheduled";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each);
  let shape () : Lemma (ensures result_shape (Native.interpret_scheduled facts)) = () in
  shape ();
  assert (interpretation_schedule facts tree) by (
    Tactics.prune "Nickel_crdt.Edit.interpret";
    Tactics.prune "Nickel_crdt.Edit.interpret_scheduled";
    Tactics.prune "Nickel_crdt.Event_shell.scheduled";
    Tactics.smt_sync' 1 1
  )

let strictly_before (ids: t_Slice Native.t_EventId) (first: Native.t_EventId) (second: Native.t_EventId) : Type0 =
  exists(i: usize{v i < Seq.length ids}) (j: usize{v j < Seq.length ids}). Prims.l_and (Prims.l_and (v i < v j) (Seq.index ids (v i) == first)) (Seq.index ids (v j) == second)

let trace_orders_stored_dependencies (facts: t_Slice Native.t_Fact) (ids: t_Slice Native.t_EventId) (index: FStar.Fin.under (Seq.length facts)) (at: FStar.Fin.under (Seq.length ids)) : Lemma (requires (Nickel.EditIdentity.unique_ids facts /\ causal_trace facts ids /\ (Seq.index facts index).f_id == Seq.index ids at)) (ensures all_ids (Alloc.Vec.impl_1__as_slice (Seq.index facts index).f_after) (fun (id: Native.t_EventId) -> Prims.l_not (absent_prefix ids id at))) =
  assert (causal_position facts ids at);
  let each (k: FStar.Fin.under (Seq.length facts)) : Lemma (requires ((Seq.index facts k).f_id == Seq.index ids at /\ all_ids (Alloc.Vec.impl_1__as_slice (Seq.index facts k).f_after) (fun (id: Native.t_EventId) -> Prims.l_not (absent_prefix ids id at)))) (ensures all_ids (Alloc.Vec.impl_1__as_slice (Seq.index facts index).f_after) (fun (id: Native.t_EventId) -> Prims.l_not (absent_prefix ids id at))) =
    unique_slice_nat_positions facts index k;
    assert (index == k);
    () in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each);
  ()

let earlier_member_has_strict_order (ids: t_Slice Native.t_EventId) (id: Native.t_EventId) (at: FStar.Fin.under (Seq.length ids)) : Lemma (requires Prims.l_not (absent_prefix ids id at)) (ensures strictly_before ids id (Seq.index ids at)) =
  assert (v (mk_usize at) == at);
  let each (i: usize{v i < Seq.length ids}) : Lemma (ensures Prims.l_and (v i < at) (Seq.index ids (v i) == id) ==> strictly_before ids id (Seq.index ids at)) = () in
  FStar.Classical.forall_intro each;
  ()

let exact_cut_keeps_dependencies (facts: facts_vec) (roots: t_Slice Native.t_EventId) (selected: ids_vec) (index: FStar.Fin.under (Seq.length (Alloc.Vec.impl_1__as_slice facts))) : Lemma (requires (exact_past_result facts roots (Result.Result_Ok selected) /\ member (Alloc.Vec.impl_1__as_slice selected) (Seq.index (Alloc.Vec.impl_1__as_slice facts) index).f_id)) (ensures all_ids (Alloc.Vec.impl_1__as_slice (Seq.index (Alloc.Vec.impl_1__as_slice facts) index).f_after) (member (Alloc.Vec.impl_1__as_slice selected))) =
  let fact = Seq.index (Alloc.Vec.impl_1__as_slice facts) index in
  assert (ancestor facts roots fact.f_id);
  let each (j: usize{v j < Seq.length (Alloc.Vec.impl_1__as_slice fact.f_after)}) : Lemma (ensures member (Alloc.Vec.impl_1__as_slice selected) (Seq.index (Alloc.Vec.impl_1__as_slice fact.f_after) (v j))) =
    let id = Seq.index (Alloc.Vec.impl_1__as_slice fact.f_after) (v j) in
    assert (fact_present (Alloc.Vec.impl_1__as_slice facts) fact);
    assert (Nickel.EditCausal.causal_edge facts fact.f_id id);
    ancestor_follows_edge facts roots fact.f_id id;
    assert (member (Alloc.Vec.impl_1__as_slice selected) id) by (
      Tactics.prune "Nickel.EditPast.ancestor";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro each;
  ()

let cut_order (facts: facts_vec) (selected: ids_vec) (done: ids_vec) : Type0 =
  Prims.l_and (all_ids (Alloc.Vec.impl_1__as_slice selected) (member (Alloc.Vec.impl_1__as_slice done))) (forall(index: FStar.Fin.under (Seq.length (Alloc.Vec.impl_1__as_slice facts))). member (Alloc.Vec.impl_1__as_slice selected) (Seq.index (Alloc.Vec.impl_1__as_slice facts) index).f_id ==> all_ids (Alloc.Vec.impl_1__as_slice (Seq.index (Alloc.Vec.impl_1__as_slice facts) index).f_after) (fun (id: Native.t_EventId) -> Prims.l_and (member (Alloc.Vec.impl_1__as_slice selected) id) (strictly_before (Alloc.Vec.impl_1__as_slice done) id (Seq.index (Alloc.Vec.impl_1__as_slice facts) index).f_id)))

let full_execution_orders_exact_cut (facts: facts_vec) (roots: t_Slice Native.t_EventId) (selected: ids_vec) (done: ids_vec) : Lemma (requires (ids_unique facts /\ stored_selection facts selected /\ exact_past_result facts roots (Result.Result_Ok selected) /\ Seq.length (Alloc.Vec.impl_1__as_slice done) == Seq.length (Alloc.Vec.impl_1__as_slice facts) /\ unique_selection (Alloc.Vec.impl_1__as_slice done) /\ causal_trace (Alloc.Vec.impl_1__as_slice facts) (Alloc.Vec.impl_1__as_slice done))) (ensures cut_order facts selected done) =
  let input = Alloc.Vec.impl_1__as_slice facts in
  let ids = Alloc.Vec.impl_1__as_slice done in
  full_trace_covers_storage input done;
  let selected_member (i: usize{v i < Seq.length (Alloc.Vec.impl_1__as_slice selected)}) : Lemma (ensures member ids (Seq.index (Alloc.Vec.impl_1__as_slice selected) (v i))) =
    let id = Seq.index (Alloc.Vec.impl_1__as_slice selected) (v i) in
    let index = parent_fact_position facts id in
    assert (member ids (Seq.index input index).f_id);
    () in
  FStar.Classical.forall_intro selected_member;
  let selected_fact (index: FStar.Fin.under (Seq.length input)) : Lemma (requires member (Alloc.Vec.impl_1__as_slice selected) (Seq.index input index).f_id) (ensures all_ids (Alloc.Vec.impl_1__as_slice (Seq.index input index).f_after) (fun (id: Native.t_EventId) -> Prims.l_and (member (Alloc.Vec.impl_1__as_slice selected) id) (strictly_before ids id (Seq.index input index).f_id))) =
    let at = done_position ids (Seq.index input index).f_id in
    trace_orders_stored_dependencies input ids index at;
    exact_cut_keeps_dependencies facts roots selected index;
    let dependency (j: usize{v j < Seq.length (Alloc.Vec.impl_1__as_slice (Seq.index input index).f_after)}) : Lemma (ensures Prims.l_and (member (Alloc.Vec.impl_1__as_slice selected) (Seq.index (Alloc.Vec.impl_1__as_slice (Seq.index input index).f_after) (v j))) (strictly_before ids (Seq.index (Alloc.Vec.impl_1__as_slice (Seq.index input index).f_after) (v j)) (Seq.index input index).f_id)) = earlier_member_has_strict_order ids (Seq.index (Alloc.Vec.impl_1__as_slice (Seq.index input index).f_after) (v j)) at in
    FStar.Classical.forall_intro dependency;
    () in
  FStar.Classical.forall_intro (FStar.Classical.move_requires selected_fact);
  ()

let interpreted_cut (facts: facts_vec) (roots: t_Slice Native.t_EventId) (tree: Native.t_Tree) : Type0 =
  exists(selected: ids_vec) (done: ids_vec). Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Native.past (Alloc.Vec.impl_1__as_slice facts) roots == Result.Result_Ok selected) (Native.interpret_scheduled (Alloc.Vec.impl_1__as_slice facts) == Result.Result_Ok (tree, done))) (stored_selection facts selected)) (complete_causal_trace (Alloc.Vec.impl_1__as_slice facts) (tree, done))) (cut_order facts selected done)

let successful_execution_orders_its_exact_past_cut (facts: facts_vec) (roots: t_Slice Native.t_EventId) (tree: Native.t_Tree) : Lemma (requires (Nickel.EditWellFormed.facts_causally_closed facts /\ Nickel.EditWellFormed.dependencies_present (Alloc.Vec.impl_1__as_slice facts) roots /\ Native.duplicate_events roots == false /\ ids_unique facts /\ Native.interpret (Alloc.Vec.impl_1__as_slice facts) == Result.Result_Ok tree)) (ensures interpreted_cut facts roots tree) =
  let shape () : Lemma (ensures result_shape (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) = () in
  shape ();
  assert (history_references_present facts);
  assert (all_ids roots (fact_id_present facts));
  scanned_roots_compute_exact_past facts roots;
  successful_interpretation_has_causal_schedule (Alloc.Vec.impl_1__as_slice facts) tree;
  let combine (selected: ids_vec) (done: ids_vec) : Lemma (requires (Native.past (Alloc.Vec.impl_1__as_slice facts) roots == Result.Result_Ok selected /\ stored_selection facts selected /\ exact_past_result facts roots (Result.Result_Ok selected) /\ Native.interpret_scheduled (Alloc.Vec.impl_1__as_slice facts) == Result.Result_Ok (tree, done) /\ complete_causal_trace (Alloc.Vec.impl_1__as_slice facts) (tree, done))) (ensures interpreted_cut facts roots tree) =
    full_execution_orders_exact_cut facts roots selected done;
    assert (interpreted_cut facts roots tree) by (
      Tactics.prune "Nickel.EditSchedule.cut_order";
      Tactics.prune "Nickel_crdt.Edit.duplicate_events";
      Tactics.prune "Nickel_crdt.Event_layer.duplicate_ids";
      Tactics.prune "Nickel_crdt.Edit.past";
      Tactics.prune "Nickel_crdt.Event_layer.past";
      Tactics.prune "Nickel_crdt.Edit.interpret_scheduled";
      Tactics.prune "Nickel_crdt.Event_shell.scheduled";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 combine);
  assert (interpreted_cut facts roots tree) by (
    Tactics.prune "Nickel_crdt.Edit.past";
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.prune "Nickel_crdt.Edit.interpret";
    Tactics.prune "Nickel_crdt.Edit.interpret_scheduled";
    Tactics.prune "Nickel_crdt.Event_shell.scheduled";
    Tactics.smt_sync' 1 1
  )

unfold type operation_pair = Native.t_EventId & Alloc.Vec.t_Vec Native.t_Node Alloc.Alloc.t_Global

unfold type node_vec = Alloc.Vec.t_Vec Native.t_Node Alloc.Alloc.t_Global

unfold type event_work_step = ids_vec & operations_vec & Native.t_Tree & node_vec & usize

let prefix_step_valid (facts: t_Slice Native.t_Fact) (done: ids_vec) (operations: operations_vec) (tree: Native.t_Tree) (step: event_work_step) : Type0 =
  match step with | (previous_done, previous_operations, previous_tree, new_operations, index) -> begin if v index < Seq.length facts then
    begin Prims.l_and (Prims.l_and (Prims.l_and (Native.choose_ready facts (Alloc.Vec.impl_1__as_slice previous_done) == Option.Option_Some index) (Native.interpret_event facts (Seq.index facts (v index)) (Alloc.Vec.impl_1__as_slice previous_operations) previous_tree == Result.Result_Ok (tree, new_operations))) (Alloc.Vec.impl_1__as_slice done == Seq.append (Alloc.Vec.impl_1__as_slice previous_done) (Seq.create 1 (Seq.index facts (v index)).f_id))) (Alloc.Vec.impl_1__as_slice operations == Seq.append (Alloc.Vec.impl_1__as_slice previous_operations) (Seq.create 1 ((Seq.index facts (v index)).f_id, new_operations))) end
  else
    begin Prims.l_False end end

let rec event_work_prefix (facts: t_Slice Native.t_Fact) (count: nat) (done: ids_vec) (operations: operations_vec) (tree: Native.t_Tree) : Tot Type0 (decreases count) =
  if count ==? 0 then
    begin Prims.l_and (Prims.l_and (Alloc.Vec.impl_1__as_slice done == Seq.empty) (Alloc.Vec.impl_1__as_slice operations == Seq.empty)) (tree == Core_models.Default.f_default #Native.t_Tree #Native.impl_5 ()) end
  else
    begin exists(step: event_work_step). Prims.l_and (match step with | (previous_done, previous_operations, previous_tree, _, _) -> begin event_work_prefix facts (count - 1) previous_done previous_operations previous_tree end) (prefix_step_valid facts done operations tree step) end

let prefix_can_extend_at (facts: t_Slice Native.t_Fact) (count: nat) (done: ids_vec) (operations: operations_vec) (tree: Native.t_Tree) (index: usize{v index < Seq.length facts}) : Type0 =
  forall(next_tree: Native.t_Tree) (new_operations: node_vec) (next_done: ids_vec) (next_operations: operations_vec). Prims.l_and (Prims.l_and (Prims.l_and (Native.choose_ready facts (Alloc.Vec.impl_1__as_slice done) == Option.Option_Some index) (Native.interpret_event facts (Seq.index facts (v index)) (Alloc.Vec.impl_1__as_slice operations) tree == Result.Result_Ok (next_tree, new_operations))) (Alloc.Vec.impl_1__as_slice next_done == Seq.append (Alloc.Vec.impl_1__as_slice done) (Seq.create 1 (Seq.index facts (v index)).f_id))) (Alloc.Vec.impl_1__as_slice next_operations == Seq.append (Alloc.Vec.impl_1__as_slice operations) (Seq.create 1 ((Seq.index facts (v index)).f_id, new_operations))) ==> event_work_prefix facts (count + 1) next_done next_operations next_tree

let prefix_extension_is_actual_work (facts: t_Slice Native.t_Fact) (count: nat) (done: ids_vec) (operations: operations_vec) (tree: Native.t_Tree) (index: usize{v index < Seq.length facts}) : Lemma (requires event_work_prefix facts count done operations tree) (ensures prefix_can_extend_at facts count done operations tree index) =
  let next (next_tree: Native.t_Tree) (new_operations: node_vec) (next_done: ids_vec) (next_operations: operations_vec) : Lemma (requires (Native.choose_ready facts (Alloc.Vec.impl_1__as_slice done) == Option.Option_Some index /\ Native.interpret_event facts (Seq.index facts (v index)) (Alloc.Vec.impl_1__as_slice operations) tree == Result.Result_Ok (next_tree, new_operations) /\ Alloc.Vec.impl_1__as_slice next_done == Seq.append (Alloc.Vec.impl_1__as_slice done) (Seq.create 1 (Seq.index facts (v index)).f_id) /\ Alloc.Vec.impl_1__as_slice next_operations == Seq.append (Alloc.Vec.impl_1__as_slice operations) (Seq.create 1 ((Seq.index facts (v index)).f_id, new_operations)))) (ensures event_work_prefix facts (count + 1) next_done next_operations next_tree) =
    let witness = ((done, operations, tree, new_operations, index) <: event_work_step) in
    assert (prefix_step_valid facts next_done next_operations next_tree witness);
    FStar.Classical.exists_intro (fun (step: event_work_step) -> Prims.l_and (match step with | (previous_done, previous_operations, previous_tree, _, _) -> begin event_work_prefix facts count previous_done previous_operations previous_tree end) (prefix_step_valid facts next_done next_operations next_tree step)) witness;
    assert (event_work_prefix facts (count + 1) next_done next_operations next_tree) by (
      Tactics.prune "Nickel_crdt.Edit.interpret_event";
      Tactics.prune "Nickel_crdt.Edit.choose_ready";
      Tactics.prune "Nickel_crdt.Event_layer.choose_ready";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_4 (FStar.Classical.move_requires_4 next)

let prefix_starts_at_actual_empty (facts: t_Slice Native.t_Fact) : Lemma (ensures event_work_prefix facts 0 (Alloc.Vec.impl__new #Native.t_EventId ()) (Alloc.Vec.impl__new #operation_pair ()) (Core_models.Default.f_default #Native.t_Tree #Native.impl_5 ())) =
  ()

let tree_work_failed (facts: facts_vec) (error: Native.t_Error) : Type0 =
  exists(done: ids_vec) (operations: operations_vec) (tree: Native.t_Tree) (index: FStar.Fin.under (Seq.length (Alloc.Vec.impl_1__as_slice facts))). Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Seq.length (Alloc.Vec.impl_1__as_slice done) < Seq.length (Alloc.Vec.impl_1__as_slice facts)) (Seq.length (Alloc.Vec.impl_1__as_slice operations) == Seq.length (Alloc.Vec.impl_1__as_slice done))) (unique_selection (Alloc.Vec.impl_1__as_slice done))) (causal_trace (Alloc.Vec.impl_1__as_slice facts) (Alloc.Vec.impl_1__as_slice done))) (eligible (Alloc.Vec.impl_1__as_slice facts) (Alloc.Vec.impl_1__as_slice done) index)) (event_work_prefix (Alloc.Vec.impl_1__as_slice facts) (Seq.length (Alloc.Vec.impl_1__as_slice done)) done operations tree)) (Native.choose_ready (Alloc.Vec.impl_1__as_slice facts) (Alloc.Vec.impl_1__as_slice done) == Option.Option_Some (mk_usize index))) (Native.interpret_event (Alloc.Vec.impl_1__as_slice facts) (Seq.index (Alloc.Vec.impl_1__as_slice facts) index) (Alloc.Vec.impl_1__as_slice operations) tree == Result.Result_Err error)

let schedule_progress_invariant (facts: t_Slice Native.t_Fact) (at: nat) (state: schedule_state) : Type0 =
  Prims.l_and (schedule_invariant facts at state) (match state with | (done, operations, tree) -> begin Prims.l_and (Seq.length (Alloc.Vec.impl_1__as_slice operations) == at) (event_work_prefix facts at done operations tree) end)

let ranked_outer_errors_come_from_tree_work (facts: facts_vec) (rank: Native.t_EventId -> nat) (bound: nat) : Lemma (requires (causal_rank facts rank bound /\ ids_unique facts)) (ensures Nickel.LoopUtil.result_safe (complete_causal_trace (Alloc.Vec.impl_1__as_slice facts)) (tree_work_failed facts) (Native.interpret_scheduled (Alloc.Vec.impl_1__as_slice facts))) =
  let input = Alloc.Vec.impl_1__as_slice facts in
  let progress (done: t_Slice Native.t_EventId) : Lemma (requires Seq.length done < Seq.length input) (ensures Prims.l_and (Prims.l_not (Native.choose_ready input done == Option.Option_None)) (chosen_is_first input done (Native.choose_ready input done))) [SMTPat (Native.choose_ready input done)] =
    ranked_incomplete_scan_progress facts done rank bound;
    scheduler_choice_is_exact input done;
    assert (Prims.l_and (Prims.l_not (Native.choose_ready input done == Option.Option_None)) (chosen_is_first input done (Native.choose_ready input done))) by (
      Tactics.prune "Nickel.EditCausal.causal_rank";
      Tactics.prune "Nickel_crdt.Edit.choose_ready";
      Tactics.prune "Nickel_crdt.Event_layer.choose_ready";
      Tactics.smt_sync' 1 1
    ) in
  let choice_shape (done: t_Slice Native.t_EventId) : Lemma (ensures Prims.l_or (Native.choose_ready input done == Option.Option_None) (exists(index: usize). Native.choose_ready input done == Option.Option_Some index)) [SMTPat (Native.choose_ready input done)] = () in
  let event_shape (event: Native.t_Fact) (operations: t_Slice (Native.t_EventId & Alloc.Vec.t_Vec Native.t_Node Alloc.Alloc.t_Global)) (tree: Native.t_Tree) : Lemma (ensures result_shape (Native.interpret_event input event operations tree)) [SMTPat (Native.interpret_event input event operations tree)] = () in
  let extend_at_call (done: ids_vec) (operations: operations_vec) (tree: Native.t_Tree) (index: usize{v index < Seq.length input}) : Lemma (requires (event_work_prefix input (Seq.length (Alloc.Vec.impl_1__as_slice done)) done operations tree /\ Seq.length (Alloc.Vec.impl_1__as_slice done) < Seq.length input)) (ensures prefix_can_extend_at input (Seq.length (Alloc.Vec.impl_1__as_slice done)) done operations tree index) [SMTPat (Native.choose_ready input (Alloc.Vec.impl_1__as_slice done)); SMTPat (Native.interpret_event input (Seq.index input (v index)) (Alloc.Vec.impl_1__as_slice operations) tree)] =
    prefix_extension_is_actual_work input (Seq.length (Alloc.Vec.impl_1__as_slice done)) done operations tree index;
    assert (prefix_can_extend_at input (Seq.length (Alloc.Vec.impl_1__as_slice done)) done operations tree index) by (
      Tactics.prune "Nickel.EditCausal.causal_rank";
      Tactics.prune "Nickel.EditSchedule.event_work_prefix";
      Tactics.prune "Nickel_crdt.Edit.interpret_event";
      Tactics.prune "Nickel_crdt.Edit.choose_ready";
      Tactics.prune "Nickel_crdt.Event_layer.choose_ready";
      Tactics.smt_sync' 0 0
    ) in
  prefix_starts_at_actual_empty input;
  empty_trace_is_valid input;
  Nickel.Vector.empty_vector_contents #Native.t_EventId ();
  Nickel.Vector.empty_vector_contents #operation_pair ();
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len input) (schedule_progress_invariant input) schedule_done (complete_causal_trace input) (tree_work_failed facts);
  assert (Nickel.LoopUtil.result_safe (complete_causal_trace input) (tree_work_failed facts) (Native.interpret_scheduled input)) by (
    Tactics.prune "Nickel.EditSchedule.event_work_prefix";
    Tactics.prune "Nickel.EditCausal.causal_rank";
    Tactics.prune "Nickel.EditSchedule.causal_trace";
    Tactics.prune "Nickel_crdt.Edit.interpret_event";
    Tactics.prune "Nickel_crdt.Edit.choose_ready";
    Tactics.prune "Nickel_crdt.Event_layer.choose_ready";
    Tactics.prune "Nickel_crdt.Edit.push";
    Tactics.prune "Nickel_crdt.Event_layer.push";
    Tactics.prune "Nickel.LoopUtil.step_safe";
    Tactics.prune "Nickel.LoopUtil.output_safe";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.smt_sync' 1 1
  )

let interpret_errors_come_from_tree_work (facts: facts_vec) (rank: Native.t_EventId -> nat) (bound: nat) (error: Native.t_Error) : Lemma (requires (causal_rank facts rank bound /\ ids_unique facts /\ Native.interpret (Alloc.Vec.impl_1__as_slice facts) == Result.Result_Err error)) (ensures tree_work_failed facts error) =
  ranked_outer_errors_come_from_tree_work facts rank bound;
  interpret_erases_only_schedule (Alloc.Vec.impl_1__as_slice facts);
  let shape () : Lemma (ensures result_shape (Native.interpret_scheduled (Alloc.Vec.impl_1__as_slice facts))) = () in
  shape ();
  assert (tree_work_failed facts error) by (
    Tactics.prune "Nickel_crdt.Edit.interpret";
    Tactics.prune "Nickel_crdt.Edit.interpret_scheduled";
    Tactics.prune "Nickel_crdt.Event_shell.scheduled";
    Tactics.smt_sync' 1 1
  )

let complete_event_work (facts: t_Slice Native.t_Fact) (pair: Native.t_Tree & ids_vec) : Type0 =
  match pair with | (tree, done) -> begin Prims.l_and (complete_causal_trace facts pair) (exists(operations: operations_vec). Prims.l_and (Seq.length (Alloc.Vec.impl_1__as_slice operations) == Seq.length facts) (event_work_prefix facts (Seq.length facts) done operations tree)) end

let successful_schedule_has_complete_event_work (facts: t_Slice Native.t_Fact) : Lemma (ensures Nickel.LoopUtil.result_safe (complete_event_work facts) (fun (_: Native.t_Error) -> Prims.l_True) (Native.interpret_scheduled facts)) =
  let choice_shape (done: t_Slice Native.t_EventId) : Lemma (ensures Prims.l_or (Native.choose_ready facts done == Option.Option_None) (exists(i: usize). Native.choose_ready facts done == Option.Option_Some i)) [SMTPat (Native.choose_ready facts done)] = () in
  let event_shape (event: Native.t_Fact) (operations: t_Slice operation_pair) (tree: Native.t_Tree) : Lemma (ensures result_shape (Native.interpret_event facts event operations tree)) [SMTPat (Native.interpret_event facts event operations tree)] = () in
  let extend_at_call (done: ids_vec) (operations: operations_vec) (tree: Native.t_Tree) (index: usize{v index < Seq.length facts}) : Lemma (requires (event_work_prefix facts (Seq.length (Alloc.Vec.impl_1__as_slice done)) done operations tree /\ Seq.length (Alloc.Vec.impl_1__as_slice done) < Seq.length facts)) (ensures prefix_can_extend_at facts (Seq.length (Alloc.Vec.impl_1__as_slice done)) done operations tree index) [SMTPat (Native.choose_ready facts (Alloc.Vec.impl_1__as_slice done)); SMTPat (Native.interpret_event facts (Seq.index facts (v index)) (Alloc.Vec.impl_1__as_slice operations) tree)] =
    prefix_extension_is_actual_work facts (Seq.length (Alloc.Vec.impl_1__as_slice done)) done operations tree index;
    assert (prefix_can_extend_at facts (Seq.length (Alloc.Vec.impl_1__as_slice done)) done operations tree index) by (
      Tactics.prune "Nickel.EditSchedule.event_work_prefix";
      Tactics.prune "Nickel_crdt.Edit.interpret_event";
      Tactics.prune "Nickel_crdt.Edit.choose_ready";
      Tactics.prune "Nickel_crdt.Event_layer.choose_ready";
      Tactics.smt_sync' 0 0
    ) in
  prefix_starts_at_actual_empty facts;
  empty_trace_is_valid facts;
  Nickel.Vector.empty_vector_contents #Native.t_EventId ();
  Nickel.Vector.empty_vector_contents #operation_pair ();
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len facts) (schedule_progress_invariant facts) schedule_done (complete_event_work facts) (fun (_: Native.t_Error) -> Prims.l_True);
  assert (Nickel.LoopUtil.result_safe (complete_event_work facts) (fun (_: Native.t_Error) -> Prims.l_True) (Native.interpret_scheduled facts)) by (
    Tactics.prune "Nickel.EditSchedule.event_work_prefix";
    Tactics.prune "Nickel.EditSchedule.causal_trace";
    Tactics.prune "Nickel_crdt.Edit.interpret_event";
    Tactics.prune "Nickel_crdt.Edit.choose_ready";
    Tactics.prune "Nickel_crdt.Event_layer.choose_ready";
    Tactics.prune "Nickel_crdt.Edit.push";
    Tactics.prune "Nickel_crdt.Event_layer.push";
    Tactics.prune "Nickel.LoopUtil.step_safe";
    Tactics.prune "Nickel.LoopUtil.output_safe";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.smt_sync' 1 1
  )

let operation_labels_match (done: ids_vec) (operations: operations_vec) : Type0 =
  let ids = Alloc.Vec.impl_1__as_slice done in
  let groups = Alloc.Vec.impl_1__as_slice operations in
  Prims.l_and (Seq.length ids == Seq.length groups) (forall(i: FStar.Fin.under (Seq.length ids)). (match Seq.index groups i with | (id, _) -> begin id end) == Seq.index ids i)

let rec actual_prefix_groups_match_trace (facts: t_Slice Native.t_Fact) (count: nat) (done: ids_vec) (operations: operations_vec) (tree: Native.t_Tree) : Lemma (requires event_work_prefix facts count done operations tree) (ensures operation_labels_match done operations) (decreases count) =
  if count ==? 0 then
    begin () end
  else
    begin let transfer (step: event_work_step) : Lemma (requires (match step with | (previous_done, previous_operations, previous_tree, _, _) -> begin event_work_prefix facts (count - 1) previous_done previous_operations previous_tree end /\ prefix_step_valid facts done operations tree step)) (ensures operation_labels_match done operations) = match step with | (previous_done, previous_operations, previous_tree, new_operations, index) -> begin if v index < Seq.length facts then
      begin actual_prefix_groups_match_trace facts (count - 1) previous_done previous_operations previous_tree;
      assert (operation_labels_match previous_done previous_operations) by (
        Tactics.prune "Nickel.EditSchedule.event_work_prefix";
        Tactics.prune "Nickel_crdt.Edit.interpret_event";
        Tactics.prune "Nickel_crdt.Edit.choose_ready";
        Tactics.prune "Nickel_crdt.Event_layer.choose_ready";
        Tactics.smt_sync' 0 0
      );
      () end
    else
      begin () end end in
    FStar.Classical.forall_intro (FStar.Classical.move_requires transfer);
    assert (operation_labels_match done operations) by (
      Tactics.prune "Nickel_crdt.Edit.interpret_event";
      Tactics.prune "Nickel_crdt.Edit.choose_ready";
      Tactics.prune "Nickel_crdt.Event_layer.choose_ready";
      Tactics.smt_sync' 1 1
    ) end

let interpretation_event_work (facts: t_Slice Native.t_Fact) (tree: Native.t_Tree) : Type0 =
  exists(done: ids_vec) (operations: operations_vec). Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Native.interpret_scheduled facts == Result.Result_Ok (tree, done)) (complete_causal_trace facts (tree, done))) (forall(i: FStar.Fin.under (Seq.length facts)). member (Alloc.Vec.impl_1__as_slice done) (Seq.index facts i).f_id)) (Seq.length (Alloc.Vec.impl_1__as_slice operations) == Seq.length facts)) (operation_labels_match done operations)) (event_work_prefix facts (Seq.length facts) done operations tree)

let successful_interpretation_has_operation_provenance (facts: t_Slice Native.t_Fact) (tree: Native.t_Tree) : Lemma (requires Native.interpret facts == Result.Result_Ok tree) (ensures interpretation_event_work facts tree) =
  successful_schedule_has_complete_event_work facts;
  interpret_erases_only_schedule facts;
  let each (done: ids_vec) (operations: operations_vec) : Lemma (requires (Native.interpret_scheduled facts == Result.Result_Ok (tree, done) /\ complete_causal_trace facts (tree, done) /\ Seq.length (Alloc.Vec.impl_1__as_slice operations) == Seq.length facts /\ event_work_prefix facts (Seq.length facts) done operations tree)) (ensures interpretation_event_work facts tree) =
    full_trace_covers_storage facts done;
    actual_prefix_groups_match_trace facts (Seq.length facts) done operations tree;
    assert (interpretation_event_work facts tree) by (
      Tactics.prune "Nickel.EditSchedule.event_work_prefix";
      Tactics.prune "Nickel_crdt.Edit.interpret_scheduled";
      Tactics.prune "Nickel_crdt.Event_shell.scheduled";
      Tactics.prune "Nickel_crdt.Edit.interpret";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each);
  let shape () : Lemma (ensures result_shape (Native.interpret_scheduled facts)) = () in
  shape ();
  assert (interpretation_event_work facts tree) by (
    Tactics.prune "Nickel.EditSchedule.event_work_prefix";
    Tactics.prune "Nickel_crdt.Edit.interpret_scheduled";
    Tactics.prune "Nickel_crdt.Event_shell.scheduled";
    Tactics.prune "Nickel_crdt.Edit.interpret";
    Tactics.smt_sync' 1 1
  )