(* Latte generated F* view *)
module Nickel.EditPastTotal

open Nickel.Prelude

open Nickel.EventGraphText

open Rust_primitives

open Core_models

open FStar.Pervasives

open FStar.Classical

open Nickel.Vector

open Nickel.LoopUtil

open Nickel.EditAccepted

open Nickel.EditCausal

module List = FStar.List.Tot

module Native = Nickel_crdt.Edit

module Result = Core_models.Result

module Seq = FStar.Seq

open Nickel.EditPast

open FStar.Fin

open Nickel.EditWellFormed

let stored_id_presence_agrees (facts: facts_vec) (id: Native.t_EventId) : Lemma (ensures fact_id_present facts id <==> Nickel.EditWellFormed.event_present (Alloc.Vec.impl_1__as_slice facts) id) [SMTPat (fact_id_present facts id)] =
  Nickel.EditWellFormed.absence_on_whole_facts (Alloc.Vec.impl_1__as_slice facts) id;
  ()

let stored_roots_are_present (facts: facts_vec) (roots: t_Slice Native.t_EventId) : Lemma (requires all_ids roots (fact_id_present facts)) (ensures Nickel.EditWellFormed.dependencies_present (Alloc.Vec.impl_1__as_slice facts) roots) =
  ()

let unique_selection (ids: Seq.seq Native.t_EventId) : Type0 =
  forall(i: FStar.Fin.under (Seq.length ids)) (j: FStar.Fin.under (Seq.length ids)). i < j ==> Prims.l_not (Seq.index ids i == Seq.index ids j)

let unique_positions_differ (ids: Seq.seq Native.t_EventId) (i: nat{i < Seq.length ids}) (j: nat{Prims.l_and (i < j) (j < Seq.length ids)}) : Lemma (requires unique_selection ids) (ensures Prims.l_not (Seq.index ids i == Seq.index ids j)) =
  ()

let empty_and_singleton_roots_are_unique (id: Native.t_EventId) : Lemma (ensures Prims.l_and (unique_selection Seq.empty) (unique_selection (Seq.create 1 id))) =
  ()

let stored_selection (facts: facts_vec) (selected: ids_vec) : Type0 =
  Prims.l_and (unique_selection (Alloc.Vec.impl_1__as_slice selected)) (all_ids (Alloc.Vec.impl_1__as_slice selected) (fact_id_present facts))

let selected_fact_position (facts: facts_vec) (ids: t_Slice Native.t_EventId{all_ids ids (fact_id_present facts)}) (at: nat{at < Seq.length ids}) : position: FStar.Fin.under (Seq.length (Alloc.Vec.impl_1__as_slice facts)){(Seq.index (Alloc.Vec.impl_1__as_slice facts) position).f_id == Seq.index ids at} =
  assert (fact_id_present facts (Rust_primitives.Slice.slice_index ids (mk_usize at)));
  assert (fact_id_present facts (Seq.index ids at));
  parent_fact_position facts (Seq.index ids at)

let missing_position (facts: facts_vec) (selected: ids_vec{stored_selection facts selected}) (id: Native.t_EventId{fact_id_present facts id}) (at: nat{at <= Seq.length (Alloc.Vec.impl_1__as_slice selected)}) : position: FStar.Fin.under (Seq.length (Alloc.Vec.impl_1__as_slice facts)){(Seq.index (Alloc.Vec.impl_1__as_slice facts) position).f_id == (if at ==? Seq.length (Alloc.Vec.impl_1__as_slice selected) then
  begin id end
else
  begin Seq.index (Alloc.Vec.impl_1__as_slice selected) at end)} =
  if at ==? Seq.length (Alloc.Vec.impl_1__as_slice selected) then
    begin parent_fact_position facts id end
  else
    begin selected_fact_position facts (Alloc.Vec.impl_1__as_slice selected) at end

let missing_stored_id_leaves_room (facts: facts_vec) (selected: ids_vec) (id: Native.t_EventId) : Lemma (requires (stored_selection facts selected /\ fact_id_present facts id /\ Prims.l_not (member (Alloc.Vec.impl_1__as_slice selected) id))) (ensures Seq.length (Alloc.Vec.impl_1__as_slice selected) < Seq.length (Alloc.Vec.impl_1__as_slice facts)) =
  let ids = Alloc.Vec.impl_1__as_slice selected in
  let count = Seq.length ids in
  assert (unique_selection ids);
  assert (absent_prefix ids id count);
  if count < Seq.length (Alloc.Vec.impl_1__as_slice facts) then
    begin () end
  else
    begin if count ==? 0 then
      begin let position = parent_fact_position facts id in
      assert (position < count) end
    else
      begin let position = fun (at: nat{at <= count}) -> ((missing_position facts selected id at) <: FStar.Fin.under count) in
      let positions = Seq.init (count + 1) position in
      Seq.lemma_init_len (count + 1) position;
      Seq.init_index (count + 1) position;
      match FStar.Fin.pigeonhole positions with | (i, j) -> begin assert (Prims.l_and (i < j) (j <= count));
      assert (position i == position j);
      if j ==? count then
        begin assert (Seq.index ids i == id);
        assert (Seq.index ids (v (mk_usize i)) == id);
        assert (Prims.l_not (Seq.index ids (v (mk_usize i)) == id)) end
      else
        begin assert (j < count);
        assert (Seq.index ids i == Seq.index ids j);
        unique_positions_differ ids i j;
        assert (Prims.l_not (Seq.index ids i == Seq.index ids j));
        assert (i == j) end end end end

let stored_result (facts: facts_vec) (result: Result.t_Result ids_vec Native.t_Error) : Type0 =
  match result with | Result.Result_Ok selected -> begin stored_selection facts selected end | _ -> begin Prims.l_False end

let stored_push_result (facts: facts_vec) (result: ids_vec & Result.t_Result unit Native.t_Error) : Type0 =
  match result with | (selected, Result.Result_Ok _) -> begin stored_selection facts selected end | _ -> begin Prims.l_False end

let fresh_append_is_unique (before: t_Slice Native.t_EventId) (id: Native.t_EventId) : Lemma (requires (unique_selection before /\ Prims.l_not (member before id))) (ensures unique_selection (Seq.append before (Seq.create 1 id))) =
  let next = Seq.append before (Seq.create 1 id) in
  assert (absent_prefix before id (Seq.length before));
  let pair (i: FStar.Fin.under (Seq.length next)) (j: FStar.Fin.under (Seq.length next)) : Lemma (ensures i < j ==> Prims.l_not (Seq.index next i == Seq.index next j)) = if i < j then
    begin if j < Seq.length before then
      begin unique_positions_differ before i j;
      assert (Seq.index next i == Seq.index before i);
      assert (Seq.index next j == Seq.index before j) end
    else
      begin assert (j == Seq.length before);
      assert (i < Seq.length before);
      assert (Prims.l_not (Seq.index before (v (mk_usize i)) == id));
      assert (Seq.index next i == Seq.index before i);
      assert (Seq.index next j == id) end;
    assert (Prims.l_not (Seq.index next i == Seq.index next j)) end
  else
    begin () end in
  FStar.Classical.forall_intro_2 #(FStar.Fin.under (Seq.length next)) #(fun (_: FStar.Fin.under (Seq.length next)) -> FStar.Fin.under (Seq.length next)) #(fun (i: FStar.Fin.under (Seq.length next)) (j: FStar.Fin.under (Seq.length next)) -> i < j ==> Prims.l_not (Seq.index next i == Seq.index next j)) pair;
  assert (unique_selection next)

let distinct_pair_roots_are_unique (a: Native.t_EventId) (b: Native.t_EventId) : Lemma (requires Prims.l_not (a == b)) (ensures unique_selection (Seq.append (Seq.create 1 a) (Seq.create 1 b))) =
  empty_and_singleton_roots_are_unique a;
  assert (Prims.l_not (member (Seq.create 1 a) b));
  fresh_append_is_unique (Seq.create 1 a) b

let fresh_stored_push_succeeds (facts: facts_vec) (selected: ids_vec) (id: Native.t_EventId) : Lemma (requires (stored_selection facts selected /\ fact_id_present facts id /\ Prims.l_not (member (Alloc.Vec.impl_1__as_slice selected) id))) (ensures stored_push_result facts (Native.push selected id)) =
  missing_stored_id_leaves_room facts selected id;
  fresh_append_is_unique (Alloc.Vec.impl_1__as_slice selected) id;
  selected_push_preserves Seq.empty (fact_id_present facts) selected id;
  push_result_is_exact selected id;
  assert (stored_push_result facts (Native.push selected id)) by (
    Tactics.prune "Nickel_crdt.Edit.push";
    Tactics.prune "Nickel_crdt.Event_layer.push";
    Tactics.smt_sync' 1 1
  )

let extend_stored_selection_succeeds (facts: facts_vec) (fact: Native.t_Fact) (before: ids_vec) : Lemma (requires (stored_selection facts before /\ all_ids (Alloc.Vec.impl_1__as_slice fact.f_after) (fact_id_present facts))) (ensures stored_result facts (Native.extend_past fact before)) =
  let each_push (selected: ids_vec) (id: Native.t_EventId) : Lemma (requires (stored_selection facts selected /\ fact_id_present facts id /\ Prims.l_not (member (Alloc.Vec.impl_1__as_slice selected) id))) (ensures stored_push_result facts (Native.push selected id)) =
    fresh_stored_push_succeeds facts selected id;
    assert (stored_push_result facts (Native.push selected id)) by (
      Tactics.prune "Nickel_crdt.Edit.push";
      Tactics.prune "Nickel_crdt.Event_layer.push";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_push);
  let membership_boolean (ids: t_Slice Native.t_EventId) (id: Native.t_EventId) : Lemma (ensures Prims.l_or (Native.has_event ids id == true) (Native.has_event ids id == false)) [SMTPat (Native.has_event ids id)] = () in
  if Native.has_event (Alloc.Vec.impl_1__as_slice before) fact.f_id then
    begin Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Alloc.Vec.impl_1__len fact.f_after) (fun (_: nat) (selected: ids_vec) -> stored_selection facts selected) (fun (selected: ids_vec) -> selected) (stored_selection facts) (fun (_: Native.t_Error) -> Prims.l_False);
    assert (stored_result facts (Native.extend_past fact before)) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.prune "Nickel.LoopUtil.step_safe";
      Tactics.prune "Nickel.LoopUtil.output_safe";
      Tactics.prune "Nickel_crdt.Edit.has_event";
      Tactics.prune "Nickel_crdt.Event_layer.has_id";
      Tactics.prune "Nickel_crdt.Edit.push";
      Tactics.prune "Nickel_crdt.Event_layer.push";
      Tactics.smt_sync' 1 1
    ) end
  else
    begin assert (stored_result facts (Native.extend_past fact before)) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.prune "Nickel_crdt.Edit.has_event";
      Tactics.prune "Nickel_crdt.Event_layer.has_id";
      Tactics.prune "Nickel_crdt.Edit.push";
      Tactics.prune "Nickel_crdt.Event_layer.push";
      Tactics.smt_sync' 1 1
    ) end

let history_references_present (facts: facts_vec) : Type0 =
  forall(i: nat{i < Seq.length (Alloc.Vec.impl_1__as_slice facts)}). all_ids (Alloc.Vec.impl_1__as_slice (Seq.index (Alloc.Vec.impl_1__as_slice facts) i).f_after) (fact_id_present facts)

let stored_pass_succeeds (facts: facts_vec) (before: ids_vec) : Lemma (requires (history_references_present facts /\ stored_selection facts before)) (ensures stored_result facts (Native.past_pass (Alloc.Vec.impl_1__as_slice facts) before)) =
  Nickel.EventGraphText.text_graph_policy_is_exact ();
  let each_extend (selected: ids_vec) (i: usize{v i < Seq.length (Alloc.Vec.impl_1__as_slice facts)}) : Lemma (requires stored_selection facts selected) (ensures stored_result facts (Native.extend_past (Seq.index (Alloc.Vec.impl_1__as_slice facts) (v i)) selected)) =
    extend_stored_selection_succeeds facts (Seq.index (Alloc.Vec.impl_1__as_slice facts) (v i)) selected;
    assert (stored_result facts (Native.extend_past (Seq.index (Alloc.Vec.impl_1__as_slice facts) (v i)) selected)) by (
      Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
      Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
      Tactics.prune "Nickel_crdt.Event_layer.event_ops";
      Tactics.prune "Nickel_crdt.Edit.extend_past";
      Tactics.prune "Nickel_crdt.Event_layer.extend_past";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_extend);
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Alloc.Vec.impl_1__len facts) (fun (_: nat) (selected: ids_vec) -> stored_selection facts selected) (fun (selected: ids_vec) -> selected) (stored_selection facts) (fun (_: Native.t_Error) -> Prims.l_False);
  assert (stored_result facts (Native.past_pass (Alloc.Vec.impl_1__as_slice facts) before)) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel.LoopUtil.step_safe";
    Tactics.prune "Nickel.LoopUtil.output_safe";
    Tactics.prune "Nickel_crdt.Edit.extend_past";
    Tactics.prune "Nickel_crdt.Event_layer.extend_past";
    Tactics.smt_sync' 1 1
  )

let fitting_closed_history_computes_past (facts: facts_vec) (roots: t_Slice Native.t_EventId) : Lemma (requires (history_references_present facts /\ unique_selection roots /\ all_ids roots (fact_id_present facts))) (ensures stored_result facts (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) =
  Nickel.EventGraphText.text_graph_policy_is_exact ();
  Nickel.EventGraphText.text_graph_callbacks_are_exact ();
  stored_roots_are_present facts roots;
  Nickel.EditWellFormed.present_dependencies_pass_guard (Alloc.Vec.impl_1__as_slice facts) roots;
  assert (stored_selection facts (Alloc.Slice.impl__to_vec roots));
  let each_pass (selected: ids_vec) : Lemma (requires stored_selection facts selected) (ensures stored_result facts (Native.past_pass (Alloc.Vec.impl_1__as_slice facts) selected)) =
    stored_pass_succeeds facts selected;
    assert (stored_result facts (Native.past_pass (Alloc.Vec.impl_1__as_slice facts) selected)) by (
      Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
      Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
      Tactics.prune "Nickel_crdt.Event_layer.event_ops";
      Tactics.prune "Nickel_crdt.Edit.past_pass";
      Tactics.prune "Nickel_crdt.Event_layer.past_pass";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each_pass);
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Alloc.Vec.impl_1__len facts) (fun (_: nat) (state: bool & ids_vec) -> stored_selection facts state._2) (fun (state: bool & ids_vec) -> state._2) (stored_selection facts) (fun (_: Native.t_Error) -> Prims.l_False);
  assert (stored_result facts (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel.LoopUtil.step_safe";
    Tactics.prune "Nickel.LoopUtil.output_safe";
    Tactics.prune "Nickel_crdt.Edit.past_pass";
    Tactics.prune "Nickel_crdt.Event_layer.past_pass";
    Tactics.prune "Nickel_crdt.Edit.validate_after";
    Tactics.prune "Nickel_crdt.Event_layer.validate_after";
    Tactics.smt_sync' 1 1
  )

let fitting_past_is_total_and_exact (facts: facts_vec) (roots: t_Slice Native.t_EventId) : Lemma (requires (history_references_present facts /\ unique_selection roots /\ all_ids roots (fact_id_present facts))) (ensures Prims.l_and (stored_result facts (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) (exact_past_result facts roots (Native.past (Alloc.Vec.impl_1__as_slice facts) roots))) =
  fitting_closed_history_computes_past facts roots;
  successful_past_is_exact_closure facts roots;
  assert (Prims.l_and (stored_result facts (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) (exact_past_result facts roots (Native.past (Alloc.Vec.impl_1__as_slice facts) roots))) by (
    Tactics.prune "Nickel_crdt.Edit.past";
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.smt_sync' 1 1
  )

let causally_closed_history_computes_exact_past (facts: facts_vec) (roots: t_Slice Native.t_EventId) : Lemma (requires (Nickel.EditWellFormed.facts_causally_closed facts /\ Nickel.EditWellFormed.dependencies_present (Alloc.Vec.impl_1__as_slice facts) roots /\ unique_selection roots)) (ensures Prims.l_and (stored_result facts (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) (exact_past_result facts roots (Native.past (Alloc.Vec.impl_1__as_slice facts) roots))) =
  assert (history_references_present facts);
  assert (all_ids roots (fact_id_present facts));
  fitting_past_is_total_and_exact facts roots;
  assert (Prims.l_and (stored_result facts (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) (exact_past_result facts roots (Native.past (Alloc.Vec.impl_1__as_slice facts) roots))) by (
    Tactics.prune "Nickel_crdt.Edit.past";
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.smt_sync' 1 1
  )

let earlier_differs (ids: t_Slice Native.t_EventId) (row: nat{row < Seq.length ids}) (finish: nat) : Type0 =
  forall(j: FStar.Fin.under (Seq.length ids)). j < finish ==> Prims.l_not (Seq.index ids row == Seq.index ids j)

let rows_differ (ids: t_Slice Native.t_EventId) (finish: nat) : Type0 =
  forall(i: FStar.Fin.under (Seq.length ids)). i < finish ==> earlier_differs ids i i

let scan_found (ids: t_Slice Native.t_EventId) (found: bool) : Type0 =
  Prims.l_and (found == true) (Prims.l_not (unique_selection ids))

let duplicate_scan_is_exact (ids: t_Slice Native.t_EventId) : Lemma (ensures Native.duplicate_events ids == false <==> unique_selection ids) =
  Nickel.EventGraphText.text_graph_policy_is_exact ();
  Nickel.EventGraphText.text_graph_callbacks_are_exact ();
  let each_row (i: usize{v i < Seq.length ids}) : Lemma (ensures forall(inv: Nickel.LoopUtil.invariant unit (mk_usize 0) i) (value: unit) (f: Nickel.LoopUtil.callback unit bool (mk_usize 0) i). Prims.l_and (Prims.l_and (earlier_differs ids (v i) 0) (forall(s: unit) (j: Nickel.LoopUtil.position (mk_usize 0) i). earlier_differs ids (v i) (v j) ==> Nickel.LoopUtil.step_safe (fun (at: nat) (_: unit) -> earlier_differs ids (v i) at) (fun (_: unit) -> earlier_differs ids (v i) (v i)) (scan_found ids) (v j) (f s j))) (forall(s: unit). earlier_differs ids (v i) (v i) ==> earlier_differs ids (v i) (v i)) ==> Nickel.LoopUtil.output_safe (fun (_: unit) -> earlier_differs ids (v i) (v i)) (scan_found ids) (Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0) i inv value f)) = Nickel.LoopUtil.preserve_any (mk_usize 0) i (fun (at: nat) (_: unit) -> earlier_differs ids (v i) at) (fun (_: unit) -> earlier_differs ids (v i) (v i)) (scan_found ids) in
  FStar.Classical.forall_intro each_row;
  Nickel.LoopUtil.preserve_any (mk_usize 0) (Core_models.Slice.impl__len ids) (fun (at: nat) (_: unit) -> rows_differ ids at) (fun (_: unit) -> rows_differ ids (Seq.length ids)) (scan_found ids);
  assert (Native.duplicate_events ids == false <==> unique_selection ids) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.smt_sync' 1 1
  )

let scanned_roots_compute_exact_past (facts: facts_vec) (roots: t_Slice Native.t_EventId) : Lemma (requires (history_references_present facts /\ Native.duplicate_events roots == false /\ all_ids roots (fact_id_present facts))) (ensures Prims.l_and (stored_result facts (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) (exact_past_result facts roots (Native.past (Alloc.Vec.impl_1__as_slice facts) roots))) =
  duplicate_scan_is_exact roots;
  fitting_past_is_total_and_exact facts roots;
  assert (Prims.l_and (stored_result facts (Native.past (Alloc.Vec.impl_1__as_slice facts) roots)) (exact_past_result facts roots (Native.past (Alloc.Vec.impl_1__as_slice facts) roots))) by (
    Tactics.prune "Nickel_crdt.Edit.duplicate_events";
    Tactics.prune "Nickel_crdt.Event_layer.duplicate_ids";
    Tactics.prune "Nickel_crdt.Edit.past";
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.smt_sync' 1 1
  )

let same_parents (into: facts_vec) (other: facts_vec) (id: Native.t_EventId) : Type0 =
  forall(older: Native.t_EventId). Nickel.EditCausal.causal_edge into id older <==> Nickel.EditCausal.causal_edge other id older

let shared_ancestry (into: facts_vec) (other: facts_vec) (roots: t_Slice Native.t_EventId) : Type0 =
  forall(id: Native.t_EventId). ancestor into roots id ==> same_parents into other id

let rec shared_path_stays_shared (into: facts_vec) (other: facts_vec) (roots: t_Slice Native.t_EventId) (start: Native.t_EventId) (steps: Prims.list Native.t_EventId) (finish: Native.t_EventId) : Lemma (requires (shared_ancestry into other roots /\ ancestor into roots start /\ ancestor other roots start /\ Prims.l_or (Nickel.EditCausal.causal_path into start steps finish) (Nickel.EditCausal.causal_path other start steps finish))) (ensures Prims.l_and (ancestor into roots finish) (ancestor other roots finish)) (decreases steps) =
  match steps with | Prims.Nil -> begin () end | Prims.Cons next rest -> begin assert (Prims.l_and (Nickel.EditCausal.causal_edge into start next) (Nickel.EditCausal.causal_edge other start next)) by (
    Tactics.prune "Nickel.EditPast.ancestor";
    Tactics.smt_sync' 1 1
  );
  ancestor_follows_edge into roots start next;
  ancestor_follows_edge other roots start next;
  assert (Prims.l_and (Prims.l_and (ancestor into roots next) (ancestor other roots next)) (Prims.l_or (Nickel.EditCausal.causal_path into next rest finish) (Nickel.EditCausal.causal_path other next rest finish))) by (
    Tactics.prune "Nickel.EditPast.ancestor";
    Tactics.prune "Nickel.EditPastTotal.shared_ancestry";
    Tactics.smt_sync' 1 1
  );
  shared_path_stays_shared into other roots next rest finish;
  assert (Prims.l_and (ancestor into roots finish) (ancestor other roots finish)) by (
    Tactics.prune "Nickel.EditPast.ancestor";
    Tactics.prune "Nickel.EditPastTotal.shared_ancestry";
    Tactics.smt_sync' 1 1
  ) end

let shared_ancestry_agrees (into: facts_vec) (other: facts_vec) (roots: t_Slice Native.t_EventId) : Lemma (requires shared_ancestry into other roots) (ensures forall(id: Native.t_EventId). ancestor into roots id <==> ancestor other roots id) =
  let each_path (root: Native.t_EventId) (steps: Prims.list Native.t_EventId) (id: Native.t_EventId) : Lemma (requires (member roots root /\ Prims.l_or (Nickel.EditCausal.causal_path into root steps id) (Nickel.EditCausal.causal_path other root steps id))) (ensures Prims.l_and (ancestor into roots id) (ancestor other roots id)) =
    assert (Nickel.EditCausal.causal_path into root Prims.Nil root);
    assert (Nickel.EditCausal.causal_path other root Prims.Nil root);
    shared_path_stays_shared into other roots root steps id;
    assert (Prims.l_and (ancestor into roots id) (ancestor other roots id)) by (
      Tactics.prune "Nickel.EditPast.ancestor";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 each_path)

let shared_past_facts (into: facts_vec) (other: facts_vec) (roots: t_Slice Native.t_EventId) : Type0 =
  forall(fact: Native.t_Fact). Prims.l_and (fact_present (Alloc.Vec.impl_1__as_slice into) fact) (ancestor into roots fact.f_id ==> fact_present (Alloc.Vec.impl_1__as_slice other) fact)

let rec path_end_is_present (facts: facts_vec) (start: Native.t_EventId) (steps: Prims.list Native.t_EventId) (finish: Native.t_EventId) : Lemma (requires (history_references_present facts /\ fact_id_present facts start /\ Nickel.EditCausal.causal_path facts start steps finish)) (ensures fact_id_present facts finish) (decreases steps) =
  match steps with | Prims.Nil -> begin () end | Prims.Cons next rest -> begin assert (fact_id_present facts next);
  path_end_is_present facts next rest finish;
  assert (fact_id_present facts finish) by (
    Tactics.prune "Nickel.EditPast.fact_id_present";
    Tactics.smt_sync' 1 1
  ) end

let ancestor_is_present (facts: facts_vec) (roots: t_Slice Native.t_EventId) (id: Native.t_EventId) : Lemma (requires (history_references_present facts /\ all_ids roots (fact_id_present facts) /\ ancestor facts roots id)) (ensures fact_id_present facts id) =
  let each_path (root: Native.t_EventId) (steps: Prims.list Native.t_EventId) : Lemma (requires (member roots root /\ Nickel.EditCausal.causal_path facts root steps id)) (ensures fact_id_present facts id) =
    path_end_is_present facts root steps id;
    assert (fact_id_present facts id) by (
      Tactics.prune "Nickel.EditPast.fact_id_present";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each_path)

let unique_present_facts_agree (facts: facts_vec) (left: Native.t_Fact) (right: Native.t_Fact) : Lemma (requires (ids_unique facts /\ fact_present (Alloc.Vec.impl_1__as_slice facts) left /\ fact_present (Alloc.Vec.impl_1__as_slice facts) right /\ left.f_id == right.f_id)) (ensures left == right) =
  let each (i: nat) (j: nat) : Lemma (requires (i < Seq.length (Alloc.Vec.impl_1__as_slice facts) /\ j < Seq.length (Alloc.Vec.impl_1__as_slice facts) /\ Seq.index (Alloc.Vec.impl_1__as_slice facts) i == left /\ Seq.index (Alloc.Vec.impl_1__as_slice facts) j == right)) (ensures left == right) = unique_slice_nat_positions (Alloc.Vec.impl_1__as_slice facts) i j in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each)

let whole_facts_give_shared_ancestry (into: facts_vec) (other: facts_vec) (roots: t_Slice Native.t_EventId) : Lemma (requires (history_references_present into /\ all_ids roots (fact_id_present into) /\ ids_unique other /\ shared_past_facts into other roots)) (ensures shared_ancestry into other roots) =
  let each (id: Native.t_EventId) (older: Native.t_EventId) : Lemma (requires ancestor into roots id) (ensures Nickel.EditCausal.causal_edge into id older <==> Nickel.EditCausal.causal_edge other id older) =
    ancestor_is_present into roots id;
    assert (fact_id_present into id) by (
      Tactics.prune "Nickel.EditPast.fact_id_present";
      Tactics.smt_sync' 1 1
    );
    let backward (fact: Native.t_Fact) (stored: Native.t_Fact) : Lemma (requires (fact_present (Alloc.Vec.impl_1__as_slice other) fact /\ fact.f_id == id /\ fact_present (Alloc.Vec.impl_1__as_slice into) stored /\ stored.f_id == id)) (ensures fact == stored) = unique_present_facts_agree other fact stored in
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 backward) in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each)

let same_members (left: Result.t_Result ids_vec Native.t_Error) (right: Result.t_Result ids_vec Native.t_Error) : Type0 =
  match (left, right) with | (Result.Result_Ok l, Result.Result_Ok r) -> begin forall(id: Native.t_EventId). member (Alloc.Vec.impl_1__as_slice l) id <==> member (Alloc.Vec.impl_1__as_slice r) id end | _ -> begin Prims.l_True end

let both_ok (left: Result.t_Result ids_vec Native.t_Error) (right: Result.t_Result ids_vec Native.t_Error) : Type0 =
  match (left, right) with | (Result.Result_Ok _, Result.Result_Ok _) -> begin Prims.l_True end | _ -> begin Prims.l_False end

let shared_ancestry_selects_same_past (into: facts_vec) (other: facts_vec) (roots: t_Slice Native.t_EventId) : Lemma (requires shared_ancestry into other roots) (ensures same_members (Native.past (Alloc.Vec.impl_1__as_slice into) roots) (Native.past (Alloc.Vec.impl_1__as_slice other) roots)) =
  successful_past_is_exact_closure into roots;
  successful_past_is_exact_closure other roots;
  shared_ancestry_agrees into other roots;
  assert (Prims.l_and (Prims.l_and (exact_past_result into roots (Native.past (Alloc.Vec.impl_1__as_slice into) roots)) (exact_past_result other roots (Native.past (Alloc.Vec.impl_1__as_slice other) roots))) (forall(id: Native.t_EventId). ancestor into roots id <==> ancestor other roots id)) by (
    Tactics.prune "Nickel_crdt.Edit.past";
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.prune "Nickel.EditPast.exact_past_result";
    Tactics.prune "Nickel.EditPast.ancestor";
    Tactics.smt_sync' 1 1
  )

let two_closed_receivers_select_same_past (into: facts_vec) (other: facts_vec) (roots: t_Slice Native.t_EventId) : Lemma (requires (Nickel.EditWellFormed.facts_causally_closed into /\ Nickel.EditWellFormed.facts_causally_closed other /\ Nickel.EditWellFormed.dependencies_present (Alloc.Vec.impl_1__as_slice into) roots /\ Nickel.EditWellFormed.dependencies_present (Alloc.Vec.impl_1__as_slice other) roots /\ unique_selection roots /\ ids_unique other /\ shared_past_facts into other roots)) (ensures Prims.l_and (both_ok (Native.past (Alloc.Vec.impl_1__as_slice into) roots) (Native.past (Alloc.Vec.impl_1__as_slice other) roots)) (same_members (Native.past (Alloc.Vec.impl_1__as_slice into) roots) (Native.past (Alloc.Vec.impl_1__as_slice other) roots))) =
  assert (history_references_present into);
  assert (all_ids roots (fact_id_present into));
  whole_facts_give_shared_ancestry into other roots;
  assert (shared_ancestry into other roots) by (
    Tactics.prune "Nickel.EditPastTotal.shared_ancestry";
    Tactics.smt_sync' 1 1
  );
  causally_closed_history_computes_exact_past into roots;
  causally_closed_history_computes_exact_past other roots;
  shared_ancestry_selects_same_past into other roots;
  assert (Prims.l_and (both_ok (Native.past (Alloc.Vec.impl_1__as_slice into) roots) (Native.past (Alloc.Vec.impl_1__as_slice other) roots)) (same_members (Native.past (Alloc.Vec.impl_1__as_slice into) roots) (Native.past (Alloc.Vec.impl_1__as_slice other) roots))) by (
    Tactics.prune "Nickel_crdt.Edit.past";
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.prune "Nickel.EditPastTotal.same_members";
    Tactics.smt_sync' 1 1
  )