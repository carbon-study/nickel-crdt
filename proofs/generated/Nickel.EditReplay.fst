(* Latte generated F* view *)
module Nickel.EditReplay

open Nickel.Prelude

open Rust_primitives

open Core_models

open FStar.Pervasives

open FStar.Classical

open Nickel.Vector

open Nickel.LoopUtil

module Native = Nickel_crdt.Edit

module Seq = FStar.Seq

module Result = Core_models.Result

let add_node (tree: Native.t_Tree) (node: Native.t_Node) : Result.t_Result Native.t_Tree Native.t_Error =
  match Native.impl_Tree__add tree node with | (next, Result.Result_Ok _) -> begin Result.Result_Ok next end | (_, Result.Result_Err error) -> begin Result.Result_Err error end

let rec node_prefix (nodes: t_Slice Native.t_Node) (initial: Native.t_Tree) (finish: nat{finish <= Seq.length nodes}) : Tot (Result.t_Result Native.t_Tree Native.t_Error) (decreases finish) =
  if finish ==? 0 then
    begin Result.Result_Ok initial end
  else
    begin match node_prefix nodes initial (finish - 1) with | Result.Result_Err error -> begin Result.Result_Err error end | Result.Result_Ok tree -> begin add_node tree (Seq.index nodes (finish - 1)) end end

let rec node_error_is_terminal (nodes: t_Slice Native.t_Node) (initial: Native.t_Tree) (from: nat) (finish: nat{Prims.l_and (from <= finish) (finish <= Seq.length nodes)}) (error: Native.t_Error) : Lemma (requires node_prefix nodes initial from == Result.Result_Err error) (ensures node_prefix nodes initial finish == Result.Result_Err error) (decreases finish - from) =
  if finish ==? from then
    begin () end
  else
    begin node_error_is_terminal nodes initial from (finish - 1) error;
    assert (node_prefix nodes initial finish == Result.Result_Err error) by (
      Tactics.prune "Nickel_crdt.Edit.impl_Tree__add";
      Tactics.smt_sync' 1 1
    ) end

let node_step_condition (nodes: t_Slice Native.t_Node) (initial: Native.t_Tree) (index: usize{v index < Seq.length nodes}) (outcome: Native.t_Tree & Result.t_Result unit Native.t_Error) : Type0 =
  match outcome with | (next, Result.Result_Ok _) -> begin node_prefix nodes initial (v index + 1) == Result.Result_Ok next end | (_, Result.Result_Err error) -> begin node_prefix nodes initial (Seq.length nodes) == Result.Result_Err error end

let actual_nodes_replay_in_order (nodes: t_Slice Native.t_Node) (initial: Native.t_Tree) : Lemma (ensures Native.replay_nodes initial nodes == node_prefix nodes initial (Seq.length nodes)) =
  let step (tree: Native.t_Tree) (index: usize{v index < Seq.length nodes}) : Lemma (requires node_prefix nodes initial (v index) == Result.Result_Ok tree) (ensures node_step_condition nodes initial index (Native.impl_Tree__add tree (Seq.index nodes (v index)))) [SMTPat (Native.impl_Tree__add tree (Seq.index nodes (v index)))] =
    assert (node_prefix nodes initial (v index + 1) == add_node tree (Seq.index nodes (v index)));
    match Native.impl_Tree__add tree (Seq.index nodes (v index)) with | (_, Result.Result_Ok _) -> begin () end | (_, Result.Result_Err error) -> begin node_error_is_terminal nodes initial (v index + 1) (Seq.length nodes) error end in
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len nodes) (fun (at: nat) (tree: Native.t_Tree) -> Prims.l_and (at <= Seq.length nodes) (at <= Seq.length nodes ==> node_prefix nodes initial at == Result.Result_Ok tree)) (fun (tree: Native.t_Tree) -> tree) (fun (tree: Native.t_Tree) -> node_prefix nodes initial (Seq.length nodes) == Result.Result_Ok tree) (fun (error: Native.t_Error) -> node_prefix nodes initial (Seq.length nodes) == Result.Result_Err error);
  assert (Native.replay_nodes initial nodes == node_prefix nodes initial (Seq.length nodes)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Tree__add";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel.LoopUtil.step_safe";
    Tactics.prune "Nickel.LoopUtil.output_safe";
    Tactics.smt_sync' 1 1
  )

open Nickel.EditPast

unfold type event_operations = Native.t_EventId & Alloc.Vec.t_Vec Native.t_Node Alloc.Alloc.t_Global

let group_id (group: event_operations) : Native.t_EventId =
  match group with | (id, _) -> begin id end

let group_nodes (group: event_operations) : Alloc.Vec.t_Vec Native.t_Node Alloc.Alloc.t_Global =
  match group with | (_, nodes) -> begin nodes end

unfold type tree_result = Result.t_Result Native.t_Tree Native.t_Error

let group_follows (selected: t_Slice Native.t_EventId) (group: event_operations) (previous: tree_result) (outcome: tree_result) : Type0 =
  match previous with | Result.Result_Err error -> begin outcome == Result.Result_Err error end | Result.Result_Ok tree -> begin match group with | (id, nodes) -> begin Prims.l_or (Prims.l_and (member selected id) (outcome == node_prefix (Alloc.Vec.impl_1__as_slice nodes) tree (Seq.length (Alloc.Vec.impl_1__as_slice nodes)))) (Prims.l_and (Prims.l_not (member selected id)) (outcome == Result.Result_Ok tree)) end end

let rec author_prefix (operations: t_Slice event_operations) (selected: t_Slice Native.t_EventId) (finish: nat{finish <= Seq.length operations}) (outcome: tree_result) : Tot Type0 (decreases finish) =
  if finish ==? 0 then
    begin outcome == Result.Result_Ok (Core_models.Default.f_default #Native.t_Tree #Native.impl_5 ()) end
  else
    begin exists(previous: tree_result). Prims.l_and (author_prefix operations selected (finish - 1) previous) (group_follows selected (Seq.index operations (finish - 1)) previous outcome) end

let rec author_prefix_is_deterministic (operations: t_Slice event_operations) (selected: t_Slice Native.t_EventId) (finish: nat{finish <= Seq.length operations}) (left: tree_result) (right: tree_result) : Lemma (requires (author_prefix operations selected finish left /\ author_prefix operations selected finish right)) (ensures left == right) (decreases finish) =
  if finish ==? 0 then
    begin () end
  else
    begin let each (previous_left: tree_result) (previous_right: tree_result) : Lemma (requires (author_prefix operations selected (finish - 1) previous_left /\ author_prefix operations selected (finish - 1) previous_right /\ group_follows selected (Seq.index operations (finish - 1)) previous_left left /\ group_follows selected (Seq.index operations (finish - 1)) previous_right right)) (ensures left == right) =
      author_prefix_is_deterministic operations selected (finish - 1) previous_left previous_right;
      assert (left == right) by (
        Tactics.prune "Nickel.EditReplay.author_prefix";
        Tactics.prune "Nickel_crdt.Edit.impl_Tree__add";
        Tactics.smt_sync' 1 1
      ) in
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each);
    () end

let author_prefix_extends (operations: t_Slice event_operations) (selected: t_Slice Native.t_EventId) (at: nat{at < Seq.length operations}) (previous: tree_result) (outcome: tree_result) : Lemma (requires (author_prefix operations selected at previous /\ group_follows selected (Seq.index operations at) previous outcome)) (ensures author_prefix operations selected (at + 1) outcome) =
  FStar.Classical.exists_intro (fun (before: tree_result) -> Prims.l_and (author_prefix operations selected at before) (group_follows selected (Seq.index operations at) before outcome)) previous;
  ()

let rec author_error_is_terminal (operations: t_Slice event_operations) (selected: t_Slice Native.t_EventId) (from: nat) (finish: nat{Prims.l_and (from <= finish) (finish <= Seq.length operations)}) (error: Native.t_Error) : Lemma (requires author_prefix operations selected from (Result.Result_Err error)) (ensures author_prefix operations selected finish (Result.Result_Err error)) (decreases finish - from) =
  if finish ==? from then
    begin () end
  else
    begin author_error_is_terminal operations selected from (finish - 1) error;
    author_prefix_extends operations selected (finish - 1) (Result.Result_Err error) (Result.Result_Err error) end

let group_step_condition (operations: t_Slice event_operations) (selected: t_Slice Native.t_EventId) (index: usize{v index < Seq.length operations}) (result: tree_result) : Type0 =
  match result with | Result.Result_Ok tree -> begin author_prefix operations selected (v index + 1) (Result.Result_Ok tree) end | Result.Result_Err error -> begin author_prefix operations selected (Seq.length operations) (Result.Result_Err error) end

let actual_author_replays_selected_groups (operations: t_Slice event_operations) (selected: t_Slice Native.t_EventId) : Lemma (ensures author_prefix operations selected (Seq.length operations) (Native.replay_author operations selected)) =
  let step (tree: Native.t_Tree) (index: usize{v index < Seq.length operations}) : Lemma (requires (author_prefix operations selected (v index) (Result.Result_Ok tree) /\ member selected (group_id (Seq.index operations (v index))))) (ensures group_step_condition operations selected index (Native.replay_nodes tree (Alloc.Vec.impl_1__as_slice (group_nodes (Seq.index operations (v index)))))) [SMTPat (author_prefix operations selected (v index) (Result.Result_Ok tree)); SMTPat (Seq.index operations (v index))] = match Seq.index operations (v index) with | (id, nodes) -> begin actual_nodes_replay_in_order (Alloc.Vec.impl_1__as_slice nodes) tree;
  assert (Native.replay_nodes tree (Alloc.Vec.impl_1__as_slice nodes) == node_prefix (Alloc.Vec.impl_1__as_slice nodes) tree (Seq.length (Alloc.Vec.impl_1__as_slice nodes))) by (
    Tactics.prune "Nickel_crdt.Edit.replay_nodes";
    Tactics.prune "Nickel_crdt.Edit.impl_Tree__add";
    Tactics.smt_sync' 1 1
  );
  match Native.replay_nodes tree (Alloc.Vec.impl_1__as_slice nodes) with | Result.Result_Ok next -> begin author_prefix_extends operations selected (v index) (Result.Result_Ok tree) (Result.Result_Ok next) end | Result.Result_Err error -> begin author_prefix_extends operations selected (v index) (Result.Result_Ok tree) (Result.Result_Err error);
  author_error_is_terminal operations selected (v index + 1) (Seq.length operations) error end end in
  let skip (tree: Native.t_Tree) (index: usize{v index < Seq.length operations}) : Lemma (requires (author_prefix operations selected (v index) (Result.Result_Ok tree) /\ Prims.l_not (member selected (group_id (Seq.index operations (v index)))))) (ensures author_prefix operations selected (v index + 1) (Result.Result_Ok tree)) [SMTPat (author_prefix operations selected (v index) (Result.Result_Ok tree))] = author_prefix_extends operations selected (v index) (Result.Result_Ok tree) (Result.Result_Ok tree) in
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len operations) (fun (at: nat) (tree: Native.t_Tree) -> Prims.l_and (at <= Seq.length operations) (at <= Seq.length operations ==> author_prefix operations selected at (Result.Result_Ok tree))) (fun (tree: Native.t_Tree) -> tree) (fun (tree: Native.t_Tree) -> author_prefix operations selected (Seq.length operations) (Result.Result_Ok tree)) (fun (error: Native.t_Error) -> author_prefix operations selected (Seq.length operations) (Result.Result_Err error));
  assert (author_prefix operations selected (Seq.length operations) (Native.replay_author operations selected)) by (
    Tactics.prune "Nickel_crdt.Edit.has_event";
    Tactics.prune "Nickel_crdt.Edit.replay_nodes";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.prune "Nickel.LoopUtil.step_safe";
    Tactics.prune "Nickel.LoopUtil.output_safe";
    Tactics.smt_sync' 1 1
  )

open Nickel.EditAccepted

open Nickel.EditPastTotal

open Nickel.EditBasis

let exact_author_context (facts: facts_vec) (event: Native.t_Fact) (operations: t_Slice event_operations) (result: Result.t_Result (facts_vec & Native.t_Tree) Native.t_Error) : Type0 =
  match result with | Result.Result_Ok (basis, author) -> begin exists(selected: ids_vec). Prims.l_and (Prims.l_and (Native.event_basis (Alloc.Vec.impl_1__as_slice facts) event == Result.Result_Ok (selected, basis)) (exact_event_basis facts (Alloc.Vec.impl_1__as_slice event.f_after) (Result.Result_Ok (selected, basis)))) (author_prefix operations (Alloc.Vec.impl_1__as_slice selected) (Seq.length operations) (Result.Result_Ok author)) end | Result.Result_Err error -> begin exists(selected: ids_vec) (basis: facts_vec). Prims.l_and (Prims.l_and (Native.event_basis (Alloc.Vec.impl_1__as_slice facts) event == Result.Result_Ok (selected, basis)) (exact_event_basis facts (Alloc.Vec.impl_1__as_slice event.f_after) (Result.Result_Ok (selected, basis)))) (author_prefix operations (Alloc.Vec.impl_1__as_slice selected) (Seq.length operations) (Result.Result_Err error)) end

let closed_author_context_is_exact (facts: facts_vec) (event: Native.t_Fact) (operations: t_Slice event_operations) : Lemma (requires (history_references_present facts /\ Native.duplicate_events (Alloc.Vec.impl_1__as_slice event.f_after) == false /\ all_ids (Alloc.Vec.impl_1__as_slice event.f_after) (fact_id_present facts))) (ensures exact_author_context facts event operations (Native.author_context (Alloc.Vec.impl_1__as_slice facts) event operations)) =
  closed_event_basis_is_exact facts event;
  let basis_shape () : Lemma (ensures result_shape (Native.event_basis (Alloc.Vec.impl_1__as_slice facts) event)) = () in
  basis_shape ();
  let each (selected: ids_vec) : Lemma (ensures Prims.l_and (author_prefix operations (Alloc.Vec.impl_1__as_slice selected) (Seq.length operations) (Native.replay_author operations (Alloc.Vec.impl_1__as_slice selected))) (result_shape (Native.replay_author operations (Alloc.Vec.impl_1__as_slice selected)))) [SMTPat (Native.replay_author operations (Alloc.Vec.impl_1__as_slice selected))] =
    actual_author_replays_selected_groups operations (Alloc.Vec.impl_1__as_slice selected);
    let shape () : Lemma (ensures result_shape (Native.replay_author operations (Alloc.Vec.impl_1__as_slice selected))) = () in
    shape ();
    assert (Prims.l_and (author_prefix operations (Alloc.Vec.impl_1__as_slice selected) (Seq.length operations) (Native.replay_author operations (Alloc.Vec.impl_1__as_slice selected))) (result_shape (Native.replay_author operations (Alloc.Vec.impl_1__as_slice selected)))) by (
      Tactics.prune "Nickel.EditReplay.group_follows";
      Tactics.prune "Nickel_crdt.Edit.replay_author";
      Tactics.prune "Nickel.EditReplay.author_prefix";
      Tactics.smt_sync' 1 1
    ) in
  assert (exact_author_context facts event operations (Native.author_context (Alloc.Vec.impl_1__as_slice facts) event operations)) by (
    Tactics.prune "Nickel_crdt.Edit.event_basis";
    Tactics.prune "Nickel_crdt.Edit.replay_author";
    Tactics.prune "Nickel.EditReplay.author_prefix";
    Tactics.smt_sync' 1 1
  )