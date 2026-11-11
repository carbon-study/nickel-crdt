(* Latte generated F* view *)
module Nickel.EditBasis

open Nickel.Prelude

open Nickel.EventGraphText

open Rust_primitives

open Core_models

open FStar.Pervasives

open FStar.Classical

open Nickel.Vector

open Nickel.LoopUtil

open Nickel.EditAccepted

open Nickel.EditPast

module Native = Nickel_crdt.Edit

module Seq = FStar.Seq

module Result = Core_models.Result

let rec selected_prefix (facts: t_Slice Native.t_Fact) (selected: t_Slice Native.t_EventId) (finish: nat{finish <= Seq.length facts}) (output: Seq.seq Native.t_Fact) : Tot Type0 (decreases finish) =
  if finish ==? 0 then
    begin output == Seq.empty end
  else
    begin let fact = Seq.index facts (finish - 1) in
    Prims.l_or (Prims.l_and (member selected fact.f_id) (exists(before: Seq.seq Native.t_Fact). Prims.l_and (selected_prefix facts selected (finish - 1) before) (output == Seq.append before (Seq.create 1 fact)))) (Prims.l_and (Prims.l_not (member selected fact.f_id)) (selected_prefix facts selected (finish - 1) output)) end

let basis_prefix (facts: t_Slice Native.t_Fact) (selected: t_Slice Native.t_EventId) (at: nat) (basis: facts_vec) : Type0 =
  Prims.l_and (Prims.l_and (at <= Seq.length facts) (at <= Seq.length facts ==> selected_prefix facts selected at (Alloc.Vec.impl_1__as_slice basis))) (Seq.length (Alloc.Vec.impl_1__as_slice basis) <= at)

let actual_basis_is_exact_filter (facts: t_Slice Native.t_Fact) (selected: t_Slice Native.t_EventId) : Lemma (ensures Nickel.LoopUtil.result_safe (fun (basis: facts_vec) -> selected_prefix facts selected (Seq.length facts) (Alloc.Vec.impl_1__as_slice basis)) (fun (_: Native.t_Error) -> Prims.l_False) (Native.select_basis facts selected)) =
  Nickel.EventGraphText.text_graph_policy_is_exact ();
  Nickel.EventGraphText.text_graph_callbacks_are_exact ();
  let clone (fact: Native.t_Fact) : Lemma (ensures Native.clone_selected_fact fact == fact) [SMTPat (Native.clone_selected_fact fact)] =
    selected_fact_is_exact fact;
    assert (Native.clone_selected_fact fact == fact) by (
      Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
      Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
      Tactics.prune "Nickel_crdt.Event_layer.event_ops";
      Tactics.prune "Nickel_crdt.Edit.clone_selected_fact";
      Tactics.prune "Nickel_crdt.Event_layer.clone_selected_fact";
      Tactics.smt_sync' 1 1
    ) in
  Nickel.Vector.empty_vector_contents #Native.t_Fact ();
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len facts) (basis_prefix facts selected) (fun (basis: facts_vec) -> basis) (fun (basis: facts_vec) -> selected_prefix facts selected (Seq.length facts) (Alloc.Vec.impl_1__as_slice basis)) (fun (_: Native.t_Error) -> Prims.l_False);
  assert (Nickel.LoopUtil.result_safe (fun (basis: facts_vec) -> selected_prefix facts selected (Seq.length facts) (Alloc.Vec.impl_1__as_slice basis)) (fun (_: Native.t_Error) -> Prims.l_False) (Native.select_basis facts selected)) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.prune "Nickel_crdt.Edit.clone_selected_fact";
    Tactics.prune "Nickel_crdt.Event_layer.clone_selected_fact";
    Tactics.prune "Nickel_crdt.Edit.has_event";
    Tactics.prune "Nickel_crdt.Event_layer.has_id";
    Tactics.prune "Nickel_crdt.Edit.push";
    Tactics.prune "Nickel_crdt.Event_layer.push";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel.LoopUtil.step_safe";
    Tactics.prune "Nickel.LoopUtil.output_safe";
    Tactics.smt_sync' 1 1
  )

open Nickel.EditPastTotal

let exact_event_basis (facts: facts_vec) (roots: t_Slice Native.t_EventId) (result: Result.t_Result (ids_vec & facts_vec) Native.t_Error) : Type0 =
  match result with | Result.Result_Ok (selected, basis) -> begin Prims.l_and (exact_past_result facts roots (Result.Result_Ok selected)) (selected_prefix (Alloc.Vec.impl_1__as_slice facts) (Alloc.Vec.impl_1__as_slice selected) (Seq.length (Alloc.Vec.impl_1__as_slice facts)) (Alloc.Vec.impl_1__as_slice basis)) end | Result.Result_Err _ -> begin Prims.l_False end

let closed_event_basis_is_exact (facts: facts_vec) (event: Native.t_Fact) : Lemma (requires (history_references_present facts /\ Native.duplicate_events (Alloc.Vec.impl_1__as_slice event.f_after) == false /\ all_ids (Alloc.Vec.impl_1__as_slice event.f_after) (fact_id_present facts))) (ensures exact_event_basis facts (Alloc.Vec.impl_1__as_slice event.f_after) (Native.event_basis (Alloc.Vec.impl_1__as_slice facts) event)) =
  Nickel.EventGraphText.text_graph_policy_is_exact ();
  Nickel.EventGraphText.text_graph_callbacks_are_exact ();
  let input = Alloc.Vec.impl_1__as_slice facts in
  let roots = Alloc.Vec.impl_1__as_slice event.f_after in
  let shape () : Lemma (ensures result_shape (Native.past input roots)) = () in
  shape ();
  scanned_roots_compute_exact_past facts roots;
  let each (selected: ids_vec) : Lemma (ensures Prims.l_and (result_shape (Native.select_basis input (Alloc.Vec.impl_1__as_slice selected))) (Nickel.LoopUtil.result_safe (fun (basis: facts_vec) -> selected_prefix input (Alloc.Vec.impl_1__as_slice selected) (Seq.length input) (Alloc.Vec.impl_1__as_slice basis)) (fun (_: Native.t_Error) -> Prims.l_False) (Native.select_basis input (Alloc.Vec.impl_1__as_slice selected)))) [SMTPat (Native.select_basis input (Alloc.Vec.impl_1__as_slice selected))] =
    actual_basis_is_exact_filter input (Alloc.Vec.impl_1__as_slice selected);
    let shape () : Lemma (ensures result_shape (Native.select_basis input (Alloc.Vec.impl_1__as_slice selected))) = () in
    shape ();
    assert (Prims.l_and (result_shape (Native.select_basis input (Alloc.Vec.impl_1__as_slice selected))) (Nickel.LoopUtil.result_safe (fun (basis: facts_vec) -> selected_prefix input (Alloc.Vec.impl_1__as_slice selected) (Seq.length input) (Alloc.Vec.impl_1__as_slice basis)) (fun (_: Native.t_Error) -> Prims.l_False) (Native.select_basis input (Alloc.Vec.impl_1__as_slice selected)))) by (
      Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
      Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
      Tactics.prune "Nickel_crdt.Event_layer.event_ops";
      Tactics.prune "Nickel_crdt.Edit.select_basis";
      Tactics.prune "Nickel_crdt.Event_layer.select_basis";
      Tactics.smt_sync' 1 1
    ) in
  assert (exact_event_basis facts roots (Native.event_basis input event)) by (
    Tactics.prune "Nickel_crdt.Edit.v_TEXT_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.prune "Nickel_crdt.Edit.past";
    Tactics.prune "Nickel_crdt.Event_layer.past";
    Tactics.prune "Nickel_crdt.Edit.select_basis";
    Tactics.prune "Nickel_crdt.Event_layer.select_basis";
    Tactics.smt_sync' 1 1
  )