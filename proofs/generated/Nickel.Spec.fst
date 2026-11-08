(* Latte generated F* view *)
module Nickel.Spec

open Nickel.Prelude

open Rust_primitives

open Core_models

open FStar.Pervasives

module Native = Nickel_crdt.Edit

module Result = Core_models.Result

module Option = Core_models.Option

module Accepted = Nickel.EditAccepted

module WellFormed = Nickel.EditWellFormed

module Tactics = FStar.Tactics.V2

let stored_facts_valid (state: Native.t_Replica) : Type0 =
  Prims.l_and (Prims.l_and (Prims.l_and (Accepted.ids_unique state.f_facts) (Accepted.facts_ordered state.f_facts)) (WellFormed.facts_scalars_valid state.f_facts)) (WellFormed.facts_causally_closed state.f_facts)

let constructed_facts_valid (result: Result.t_Result Native.t_Replica Native.t_Error) : Type0 =
  match result with | Result.Result_Ok state -> begin stored_facts_valid state end | _ -> begin Prims.l_True end

let received_facts_valid (result: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) : Type0 =
  match result with | (state, _) -> begin stored_facts_valid state end

let edited_facts_valid (result: Native.t_Replica & Result.t_Result Native.t_Local Native.t_Error) : Type0 =
  match result with | (state, _) -> begin stored_facts_valid state end

let new_establishes_valid_facts (writer: Option.t_Option Native.t_Writer) (limits: Native.t_Limits) : Lemma (ensures constructed_facts_valid (Native.impl_Replica__new writer limits)) =
  Accepted.new_establishes_unique_ids writer limits;
  Accepted.new_establishes_fact_order writer limits;
  WellFormed.new_establishes_scalar_validity writer limits;
  WellFormed.new_establishes_causal_closure writer limits;
  assert (constructed_facts_valid (Native.impl_Replica__new writer limits)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__new";
    Tactics.smt_sync' 1 1
  )

let receive_preserves_valid_facts (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (requires stored_facts_valid before) (ensures received_facts_valid (Native.impl_Replica__receive before fact)) =
  Accepted.receive_preserves_unique_ids before fact;
  Accepted.receive_preserves_fact_order before fact;
  WellFormed.receive_preserves_scalar_validity before fact;
  WellFormed.receive_preserves_causal_closure before fact;
  assert (received_facts_valid (Native.impl_Replica__receive before fact)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__receive";
    Tactics.smt_sync' 1 1
  )

let edit_preserves_valid_facts (before: Native.t_Replica) (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (delete: Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global) : Lemma (requires stored_facts_valid before) (ensures edited_facts_valid (Native.impl_Replica__edit before gap insert delete)) =
  Accepted.edit_preserves_unique_ids before gap insert delete;
  Accepted.edit_preserves_fact_order before gap insert delete;
  WellFormed.edit_preserves_scalar_validity before gap insert delete;
  WellFormed.edit_preserves_causal_closure before gap insert delete;
  assert (edited_facts_valid (Native.impl_Replica__edit before gap insert delete)) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__edit";
    Tactics.smt_sync' 1 1
  )