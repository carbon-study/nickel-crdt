(* Latte generated F* view *)
module Nickel.EditAtomic

open Nickel.Prelude

open Rust_primitives

open Core_models

open FStar.Pervasives

module Tactics = FStar.Tactics.V2

module Native = Nickel_crdt.Edit

module Result = Core_models.Result

module Option = Core_models.Option

open Nickel.Vector

open Nickel.EventShell

type plan_result = Result.t_Result (Option.t_Option Native.t_Replica) Native.t_Error

let plan_result_shape (result: plan_result) : Type0 =
  Prims.l_or (Prims.l_or (exists(error: Native.t_Error). result == Result.Result_Err error) (result == Result.Result_Ok Option.Option_None)) (exists(next: Native.t_Replica). result == Result.Result_Ok (Option.Option_Some next))

let plan_has_result_shape (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (ensures plan_result_shape (Native.impl_Replica__plan before fact)) [SMTPat (Native.impl_Replica__plan before fact)] =
  ()

let plan_duplicate_prefix (duplicate: Result.t_Result bool Native.t_Error) (result: plan_result) : Type0 =
  match duplicate with | Result.Result_Err error -> begin result == Result.Result_Err error end | Result.Result_Ok found -> begin if found then
    begin result == Result.Result_Ok Option.Option_None end
  else
    begin Prims.l_True end end

let plan_preserves_duplicate_result (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (ensures plan_duplicate_prefix (Native.impl_Replica__duplicate (Alloc.Vec.impl_1__as_slice before.f_facts) fact) (Native.impl_Replica__plan before fact)) [SMTPat (Native.impl_Replica__plan before fact)] =
  assert (plan_duplicate_prefix (Native.impl_Replica__duplicate (Alloc.Vec.impl_1__as_slice before.f_facts) fact) (Native.impl_Replica__plan before fact)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__duplicate";
    Tactics.prune "Nickel_crdt.Event_shell.plan";
    Tactics.smt_sync' 1 1
  )

let validation_succeeded (result: Result.t_Result unit Native.t_Error) : Type0 =
  match result with | Result.Result_Ok _ -> begin Prims.l_True end | _ -> begin Prims.l_False end

let plan_was_validated (validation: Result.t_Result unit Native.t_Error) (result: plan_result) : Type0 =
  match result with | Result.Result_Ok (Option.Option_Some _) -> begin validation_succeeded validation end | _ -> begin Prims.l_True end

let successful_plan_requires_validation (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (ensures plan_was_validated (Native.impl_Replica__validate_new (Alloc.Vec.impl_1__as_slice before.f_facts) before.f_limits fact) (Native.impl_Replica__plan before fact)) =
  assert (plan_was_validated (Native.impl_Replica__validate_new (Alloc.Vec.impl_1__as_slice before.f_facts) before.f_limits fact) (Native.impl_Replica__plan before fact)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__validate_new";
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__duplicate";
    Tactics.prune "Nickel_crdt.Edit.push";
    Tactics.prune "Nickel_crdt.Event_layer.push";
    Tactics.prune "Nickel_crdt.Edit.canonical";
    Tactics.prune "Nickel_crdt.Event_layer.canonical";
    Tactics.prune "Nickel_crdt.Edit.interpret";
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__with_tree";
    Tactics.prune "Nickel_crdt.Event_shell.plan";
    Tactics.smt_sync' 1 1
  )

let receive_neutral (before: Native.t_Replica) (outcome: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) : Type0 =
  match outcome with | (next, Result.Result_Err _) -> begin next == before end | (next, Result.Result_Ok Native.Admission_Duplicate) -> begin next == before end | _ -> begin Prims.l_True end

let receive_rejection_unchanged (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (ensures receive_neutral before (Native.impl_Replica__receive before fact)) =
  assert (receive_neutral before (Native.impl_Replica__receive before fact)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__plan";
    Tactics.prune "Nickel_crdt.Event_shell.plan";
    Tactics.prune "Nickel_crdt.Event_shell.receive";
    Tactics.prune "Nickel_crdt.Event_shell.receive_into";
    Tactics.smt_sync' 1 1
  )

let edit_neutral (before: Native.t_Replica) (outcome: Native.t_Replica & Result.t_Result Native.t_Local Native.t_Error) : Type0 =
  match outcome with | (_, Result.Result_Ok (Native.Local_Authored _)) -> begin Prims.l_True end | (next, _) -> begin next == before end

let edit_rejection_or_empty_unchanged (before: Native.t_Replica) (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (delete: Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global) : Lemma (ensures edit_neutral before (Native.impl_Replica__edit before gap insert delete)) =
  assert (edit_neutral before (Native.impl_Replica__edit before gap insert delete)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__plan";
    Tactics.prune "Nickel_crdt.Event_shell.plan";
    Tactics.prune "Nickel_crdt.Edit.frontier";
    Tactics.prune "Nickel_crdt.Event_layer.frontier";
    Tactics.prune "Nickel_crdt.Edit.next_counter_after";
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__with_counter";
    Tactics.smt_sync' 1 1
  )

let edit_counter_step (before: Native.t_Replica) (outcome: Native.t_Replica & Result.t_Result Native.t_Local Native.t_Error) : Type0 =
  match outcome with | (next, Result.Result_Ok (Native.Local_Authored fact)) -> begin Prims.l_and (v next.f_next_counter == v before.f_next_counter + 1) (fact.f_id.f_counter == before.f_next_counter) end | _ -> begin Prims.l_True end

let counter_result_step (counter: u64) (result: Result.t_Result u64 Native.t_Error) : Type0 =
  match result with | Result.Result_Ok next -> begin Prims.l_and (v counter <= v Native.v_MAX_COUNTER) (v next == v counter + 1) end | Result.Result_Err error -> begin Prims.l_and (v counter > v Native.v_MAX_COUNTER) (error == Native.Error_Capacity Native.Capacity_Counter) end

let counter_result_advances_once (counter: u64) : Lemma (ensures counter_result_step counter (Native.next_counter_after counter)) [SMTPat (Native.next_counter_after counter)] =
  ()

let counter_installation_is_exact (state: Native.t_Replica) (counter: u64) : Lemma (ensures Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and ((Native.impl_Replica__with_counter state counter).f_next_counter == counter) ((Native.impl_Replica__with_counter state counter).f_writer == state.f_writer)) ((Native.impl_Replica__with_counter state counter).f_limits == state.f_limits)) ((Native.impl_Replica__with_counter state counter).f_facts == state.f_facts)) ((Native.impl_Replica__with_counter state counter).f_tree == state.f_tree)) [SMTPat (Native.impl_Replica__with_counter state counter)] =
  ()

let counter_outcome (counter: u64) : Result.t_Result u64 Native.t_Error =
  if v counter > v Native.v_MAX_COUNTER then
    begin Result.Result_Err (Native.Error_Capacity Native.Capacity_Counter) end
  else
    begin Result.Result_Ok (counter +! mk_u64 1) end

let counter_result_is_exact (counter: u64) : Lemma (ensures Native.next_counter_after counter == counter_outcome counter) =
  ()

let result_has_constructor (#ok: Type0) (#err: Type0) (out: Result.t_Result ok err) : Lemma (ensures Prims.l_or (exists(value: ok). out == Result.Result_Ok value) (exists(error: err). out == Result.Result_Err error)) =
  match out with | Result.Result_Ok _ -> begin () end | Result.Result_Err _ -> begin () end

let authored_edit_advances_once (before: Native.t_Replica) (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (delete: Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global) : Lemma (ensures edit_counter_step before (Native.impl_Replica__edit before gap insert delete)) =
  counter_result_is_exact before.f_next_counter;
  result_has_constructor (Native.frontier (Alloc.Vec.impl_1__as_slice before.f_facts));
  assert (edit_counter_step before (Native.impl_Replica__edit before gap insert delete)) by (
    Tactics.prune "Nickel_crdt.Edit.frontier";
    Tactics.prune "Nickel_crdt.Event_layer.frontier";
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__with_counter";
    Tactics.prune "Nickel_crdt.Edit.next_counter_after";
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__plan";
    Tactics.prune "Nickel_crdt.Event_shell.plan";
    Tactics.smt_sync' 1 1
  )

let constructed_empty (result: Result.t_Result Native.t_Replica Native.t_Error) : Type0 =
  match result with | Result.Result_Ok state -> begin Alloc.Vec.impl_1__as_slice state.f_facts == FStar.Seq.empty end | _ -> begin Prims.l_True end

let new_has_empty_facts (writer: Option.t_Option Native.t_Writer) (limits: Native.t_Limits) : Lemma (ensures constructed_empty (Native.impl_Replica__new writer limits)) =
  Nickel.Vector.empty_vector_contents #Native.t_Fact ();
  assert (constructed_empty (Native.impl_Replica__new writer limits)) by (
    Tactics.prune "Alloc.Vec.impl__new";
    Tactics.prune "Alloc.Vec.impl_1__as_slice";
    Tactics.smt_sync' 1 1
  )