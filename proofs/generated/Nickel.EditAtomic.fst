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
  norm_spec [delta_only ["Nickel_crdt.Edit.impl_Replica__edit"; "Nickel.EditAtomic.edit_neutral"]; iota; zeta_full; primops; unmeta; unascribe] (edit_neutral before (Native.impl_Replica__edit before gap insert delete))

let edit_counter_step (before: Native.t_Replica) (outcome: Native.t_Replica & Result.t_Result Native.t_Local Native.t_Error) : Type0 =
  match outcome with | (next, Result.Result_Ok (Native.Local_Authored fact)) -> begin Prims.l_and (v next.f_next_counter == v before.f_next_counter + 1) (fact.f_id.f_counter == before.f_next_counter) end | _ -> begin Prims.l_True end

let authored_edit_advances_once (before: Native.t_Replica) (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (delete: Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global) : Lemma (ensures edit_counter_step before (Native.impl_Replica__edit before gap insert delete)) =
  norm_spec [delta_only ["Nickel_crdt.Edit.impl_Replica__edit"; "Nickel.EditAtomic.edit_counter_step"]; iota; zeta_full; primops; unmeta; unascribe] (edit_counter_step before (Native.impl_Replica__edit before gap insert delete))