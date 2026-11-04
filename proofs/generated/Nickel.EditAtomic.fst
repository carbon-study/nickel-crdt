(* Latte generated F* view *)
module Nickel.EditAtomic

open Nickel.Prelude

open Rust_primitives

open Core_models

open FStar.Pervasives

open FStar.NormSteps

module Native = Nickel_crdt.Edit

module Result = Core_models.Result

let receive_neutral (before: Native.t_Replica) (outcome: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) : Type0 =
  match outcome with | (next, Result.Result_Err _) -> begin next == before end | (next, Result.Result_Ok Native.Admission_Duplicate) -> begin next == before end | _ -> begin Prims.l_True end

let receive_rejection_unchanged (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (ensures receive_neutral before (Native.impl_Replica__receive before fact)) =
  norm_spec [delta_only ["Nickel_crdt.Edit.impl_Replica__receive"; "Nickel.EditAtomic.receive_neutral"]; iota; zeta_full; primops; unmeta; unascribe] (receive_neutral before (Native.impl_Replica__receive before fact))

let edit_neutral (before: Native.t_Replica) (outcome: Native.t_Replica & Result.t_Result Native.t_Local Native.t_Error) : Type0 =
  match outcome with | (_, Result.Result_Ok (Native.Local_Authored _)) -> begin Prims.l_True end | (next, _) -> begin next == before end

let edit_rejection_or_empty_unchanged (before: Native.t_Replica) (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (delete: Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global) : Lemma (ensures edit_neutral before (Native.impl_Replica__edit before gap insert delete)) =
  norm_spec [delta_only ["Nickel_crdt.Edit.impl_Replica__edit"; "Nickel_crdt.Edit.next_counter_after"; "Nickel_crdt.Edit.impl_Replica__with_counter"; "Nickel.EditAtomic.edit_neutral"]; iota; zeta_full; primops; unmeta; unascribe] (edit_neutral before (Native.impl_Replica__edit before gap insert delete))

let edit_counter_step (before: Native.t_Replica) (outcome: Native.t_Replica & Result.t_Result Native.t_Local Native.t_Error) : Type0 =
  match outcome with | (next, Result.Result_Ok (Native.Local_Authored fact)) -> begin Prims.l_and (v next.f_next_counter == v before.f_next_counter + 1) (fact.f_id.f_counter == before.f_next_counter) end | _ -> begin Prims.l_True end

let counter_result_step (counter: u64) (result: Result.t_Result u64 Native.t_Error) : Type0 =
  match result with | Result.Result_Ok next -> begin Prims.l_and (v counter <= v Native.v_MAX_COUNTER) (v next == v counter + 1) end | Result.Result_Err error -> begin Prims.l_and (v counter > v Native.v_MAX_COUNTER) (error == Native.Error_Capacity Native.Capacity_Counter) end

let counter_result_advances_once (counter: u64) : Lemma (ensures counter_result_step counter (Native.next_counter_after counter)) [SMTPat (Native.next_counter_after counter)] =
  norm_spec [delta_only ["Nickel_crdt.Edit.next_counter_after"; "Nickel_crdt.Edit.impl_Replica__with_counter"; "Nickel.EditAtomic.counter_result_step"]; iota; zeta_full; primops; unmeta; unascribe] (counter_result_step counter (Native.next_counter_after counter))

let counter_installation_is_exact (state: Native.t_Replica) (counter: u64) : Lemma (ensures Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and ((Native.impl_Replica__with_counter state counter).f_next_counter == counter) ((Native.impl_Replica__with_counter state counter).f_writer == state.f_writer)) ((Native.impl_Replica__with_counter state counter).f_limits == state.f_limits)) ((Native.impl_Replica__with_counter state counter).f_facts == state.f_facts)) ((Native.impl_Replica__with_counter state counter).f_tree == state.f_tree)) =
  norm_spec [delta_only ["Nickel_crdt.Edit.impl_Replica__with_counter"]; iota; zeta_full; primops] (Native.impl_Replica__with_counter state counter)

let authored_edit_advances_once (before: Native.t_Replica) (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (delete: Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global) : Lemma (ensures edit_counter_step before (Native.impl_Replica__edit before gap insert delete)) =
  norm_spec [delta_only ["Nickel_crdt.Edit.impl_Replica__edit"; "Nickel_crdt.Edit.next_counter_after"; "Nickel_crdt.Edit.impl_Replica__with_counter"; "Nickel.EditAtomic.edit_counter_step"]; iota; zeta_full; primops; unmeta; unascribe] (edit_counter_step before (Native.impl_Replica__edit before gap insert delete))