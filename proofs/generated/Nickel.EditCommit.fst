(* Latte generated F* view *)
module Nickel.EditCommit

open Nickel.Prelude

open Rust_primitives

open Core_models

open FStar.Pervasives

open FStar.NormSteps

module Tactics = FStar.Tactics.V2

open Nickel.EditAtomic

module Native = Nickel_crdt.Edit

module Result = Core_models.Result

let same_commit (before: Native.t_Replica) (outcome: Native.t_Replica & Result.t_Result Native.t_Local Native.t_Error) : Type0 =
  match outcome with | (next, Result.Result_Ok (Native.Local_Authored fact)) -> begin match Native.impl_Replica__receive before fact with | (admitted, Result.Result_Ok Native.Admission_Added) -> begin Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (next.f_facts == admitted.f_facts) (next.f_tree == admitted.f_tree)) (next.f_writer == admitted.f_writer)) (next.f_limits == admitted.f_limits)) (v next.f_next_counter == v before.f_next_counter + 1) end | _ -> begin Prims.l_False end end | _ -> begin Prims.l_True end

let requested_gap (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) : Core_models.Option.t_Option usize =
  if Alloc.Vec.impl_1__is_empty insert then
    begin Core_models.Option.Option_None end
  else
    begin Core_models.Option.Option_Some gap end

let request_bound (before: Native.t_Replica) (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (delete: Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global) (outcome: Native.t_Replica & Result.t_Result Native.t_Local Native.t_Error) : Type0 =
  match outcome with | (_, Result.Result_Ok (Native.Local_Authored fact)) -> begin Prims.l_and (Prims.l_and (Prims.l_and (fact.f_insert == insert) (fact.f_delete == delete)) (Core_models.Option.Option_Some fact.f_id.f_writer == before.f_writer)) (fact.f_gap == requested_gap gap insert) end | _ -> begin Prims.l_True end

let authored_fact_binds_request (before: Native.t_Replica) (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (delete: Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global) : Lemma (ensures request_bound before gap insert delete (Native.impl_Replica__edit before gap insert delete)) =
  assert (request_bound before gap insert delete (Native.impl_Replica__edit before gap insert delete)) by (
    Tactics.norm [delta_only ["Nickel_crdt.Edit.impl_Replica__edit"; "Nickel.EditCommit.request_bound"; "Nickel.EditCommit.requested_gap"]; iota; zeta_full; primops; simplify; unmeta; unascribe];
    Tactics.smt_sync' 1 1
  )

let authored_fact_replays_same_commit (before: Native.t_Replica) (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (delete: Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global) : Lemma (ensures same_commit before (Native.impl_Replica__edit before gap insert delete)) =
  Nickel.EditAtomic.authored_edit_advances_once before gap insert delete;
  assert (same_commit before (Native.impl_Replica__edit before gap insert delete)) by (
    Tactics.norm [delta_only ["Nickel_crdt.Edit.impl_Replica__edit"; "Nickel_crdt.Edit.next_counter_after"; "Nickel_crdt.Edit.impl_Replica__with_counter"; "Nickel_crdt.Edit.impl_Replica__receive"; "Nickel.EditCommit.same_commit"]; iota; zeta_full; primops; simplify; unmeta; unascribe];
    Tactics.smt_sync' 1 1
  )

let same_private (before: Native.t_Replica) (next: Native.t_Replica) : Type0 =
  Prims.l_and (Prims.l_and (next.f_writer == before.f_writer) (next.f_next_counter == before.f_next_counter)) (next.f_limits == before.f_limits)

let tree_publication_keeps_private (state: Native.t_Replica) (tree: Native.t_Tree) : Lemma (ensures same_private state (Native.impl_Replica__with_tree state tree)) [SMTPat (Native.impl_Replica__with_tree state tree)] =
  ()

let planned_private (before: Native.t_Replica) (result: Nickel.EditAtomic.plan_result) : Type0 =
  match result with | Result.Result_Ok (Core_models.Option.Option_Some next) -> begin same_private before next end | _ -> begin Prims.l_True end

let plan_preserves_private_state (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (ensures planned_private before (Native.impl_Replica__plan before fact)) [SMTPat (Native.impl_Replica__plan before fact)] =
  assert (planned_private before (Native.impl_Replica__plan before fact)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__with_tree";
    Tactics.smt_sync' 1 1
  )

let private_unchanged (before: Native.t_Replica) (outcome: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) : Type0 =
  match outcome with | (next, _) -> begin same_private before next end

let receive_preserves_private_state (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (ensures private_unchanged before (Native.impl_Replica__receive before fact)) =
  assert (private_unchanged before (Native.impl_Replica__receive before fact)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__plan";
    Tactics.smt_sync' 1 1
  )

let same_shared (left: Native.t_Replica) (right: Native.t_Replica) : Type0 =
  Prims.l_and (Prims.l_and (left.f_facts == right.f_facts) (left.f_tree == right.f_tree)) (left.f_limits == right.f_limits)

let tree_publication_respects_shared (left: Native.t_Replica) (right: Native.t_Replica) (tree: Native.t_Tree) : Lemma (requires same_shared left right) (ensures same_shared (Native.impl_Replica__with_tree left tree) (Native.impl_Replica__with_tree right tree)) [SMTPat (Native.impl_Replica__with_tree left tree); SMTPat (Native.impl_Replica__with_tree right tree)] =
  ()

let planned_shared (left: Nickel.EditAtomic.plan_result) (right: Nickel.EditAtomic.plan_result) : Type0 =
  match (left, right) with | (Result.Result_Err a, Result.Result_Err b) -> begin a == b end | (Result.Result_Ok Core_models.Option.Option_None, Result.Result_Ok Core_models.Option.Option_None) -> begin Prims.l_True end | (Result.Result_Ok (Core_models.Option.Option_Some a), Result.Result_Ok (Core_models.Option.Option_Some b)) -> begin same_shared a b end | _ -> begin Prims.l_False end

let plan_ignores_private_state (before: Native.t_Replica) (remote: Native.t_Replica) (fact: Native.t_Fact) : Lemma (requires same_shared before remote) (ensures planned_shared (Native.impl_Replica__plan before fact) (Native.impl_Replica__plan remote fact)) [SMTPat (Native.impl_Replica__plan before fact); SMTPat (Native.impl_Replica__plan remote fact)] =
  assert (planned_shared (Native.impl_Replica__plan before fact) (Native.impl_Replica__plan remote fact)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__with_tree";
    Tactics.smt_sync' 1 1
  )

let same_admission (left: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) (right: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) : Type0 =
  match (left, right) with | ((a, x), (b, y)) -> begin Prims.l_and (x == y) (same_shared a b) end

let admission_ignores_private_state (before: Native.t_Replica) (remote: Native.t_Replica{same_shared before remote}) (fact: Native.t_Fact) : Lemma (ensures same_admission (Native.impl_Replica__receive before fact) (Native.impl_Replica__receive remote fact)) =
  assert (same_admission (Native.impl_Replica__receive before fact) (Native.impl_Replica__receive remote fact)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__plan";
    Tactics.smt_sync' 1 1
  )

let delivered_commit (remote: Native.t_Replica) (outcome: Native.t_Replica & Result.t_Result Native.t_Local Native.t_Error) : Type0 =
  match outcome with | (next, Result.Result_Ok (Native.Local_Authored fact)) -> begin match Native.impl_Replica__receive remote fact with | (admitted, Result.Result_Ok Native.Admission_Added) -> begin Prims.l_and (Prims.l_and (same_shared next admitted) (admitted.f_writer == remote.f_writer)) (admitted.f_next_counter == remote.f_next_counter) end | _ -> begin Prims.l_False end end | _ -> begin Prims.l_True end

let local_author_remote_admit (before: Native.t_Replica) (remote: Native.t_Replica{same_shared before remote}) (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (delete: Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global) : Lemma (ensures delivered_commit remote (Native.impl_Replica__edit before gap insert delete)) =
  authored_fact_replays_same_commit before gap insert delete;
  match Native.impl_Replica__edit before gap insert delete with | (_, Result.Result_Ok (Native.Local_Authored fact)) -> begin admission_ignores_private_state before remote fact;
  receive_preserves_private_state remote fact end | _ -> begin () end;
  norm_spec [delta_only ["Nickel.EditCommit.delivered_commit"; "Nickel.EditCommit.same_commit"; "Nickel.EditCommit.same_admission"; "Nickel.EditCommit.same_shared"; "Nickel.EditCommit.private_unchanged"]; iota; zeta_full; primops; unmeta; unascribe] (delivered_commit remote (Native.impl_Replica__edit before gap insert delete))