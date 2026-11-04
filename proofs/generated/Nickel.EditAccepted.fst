(* Latte generated F* view *)
module Nickel.EditAccepted

open Nickel.Prelude

open Rust_primitives

open Core_models

open FStar.Pervasives

open FStar.NormSteps

open Nickel.LoopUtil

open Nickel.EditIdentity

module Native = Nickel_crdt.Edit

module Result = Core_models.Result

module Option = Core_models.Option

type facts_vec = Alloc.Vec.t_Vec Native.t_Fact Alloc.Alloc.t_Global

let ids_unique (facts: facts_vec) : Type0 =
  Nickel.EditIdentity.unique_ids (Alloc.Vec.impl_1__as_slice facts)

let member_next (facts: t_Slice Native.t_Fact) (id: Native.t_EventId) : Nickel.LoopUtil.transition unit (Nickel.EditIdentity.length facts) =
  fun _ at -> if (Rust_primitives.Slice.slice_index facts at).f_id ==? id then
    begin Option.Option_None end
  else
    begin Option.Option_Some () end

let member_stop (value: unit) (at: usize) : bool =
  true

let member_done (value: unit) : bool =
  false

let member_value (found: Option.t_Option Native.t_Fact) : bool =
  match found with | Option.Option_None -> begin false end | Option.Option_Some _ -> begin true end

let member_run (facts: t_Slice Native.t_Fact) (id: Native.t_EventId) (at: usize{v at <= v (Nickel.EditIdentity.length facts)}) : bool =
  Nickel.LoopUtil.option_run (Nickel.EditIdentity.length facts) at () (member_next facts id) member_stop member_done

let rec member_lookup (facts: t_Slice Native.t_Fact) (id: Native.t_EventId) (at: usize{v at <= v (Nickel.EditIdentity.length facts)}) : Lemma (ensures member_run facts id at == member_value (Nickel.EditIdentity.first_id facts id at)) (decreases v (Nickel.EditIdentity.length facts) - v at) =
  if v at < v (Nickel.EditIdentity.length facts) then
    begin Nickel.LoopUtil.option_run_step (Nickel.EditIdentity.length facts) at () (member_next facts id) member_stop member_done;
    if not ((Rust_primitives.Slice.slice_index facts at).f_id ==? id) then
      begin member_lookup facts id (at +! mk_int 1) end
    else
      begin () end;
    norm_spec [delta_once ["Nickel.EditIdentity.first_id"]; iota; zeta; primops] (Nickel.EditIdentity.first_id facts id at) end
  else
    begin Nickel.LoopUtil.option_run_end (Nickel.EditIdentity.length facts) at () (member_next facts id) member_stop member_done end

let membership_exact (facts: t_Slice Native.t_Fact) (id: Native.t_EventId) : Lemma (ensures Native.has_fact facts id == member_value (Nickel.EditIdentity.first_id facts id (mk_usize 0))) =
  Nickel.LoopUtil.option_interpret_any (mk_usize 0) (Nickel.EditIdentity.length facts) (member_next facts id) member_stop member_done;
  member_lookup facts id (mk_usize 0);
  norm_spec [delta_only ["Nickel_crdt.Edit.has_fact"; "Nickel.EditAccepted.member_run"]; iota; zeta_full; primops; unmeta; unascribe] (Native.has_fact facts id)

let membership_absent (facts: t_Slice Native.t_Fact) (id: Native.t_EventId) : Lemma (requires Native.has_fact facts id == false) (ensures Nickel.EditIdentity.prefix_absent facts id (mk_usize 0) (Nickel.EditIdentity.length facts)) =
  membership_exact facts id;
  Nickel.EditIdentity.lookup_none facts id (mk_usize 0)

let choice_safe (facts: t_Slice Native.t_Fact) (out: t_Slice Native.t_Fact) (choice: Option.t_Option usize) : Type0 =
  match choice with | Option.Option_None -> begin Prims.l_True end | Option.Option_Some i -> begin if v i < v (Nickel.EditIdentity.length facts) then
    begin Native.has_fact out (Rust_primitives.Slice.slice_index facts i).f_id == false end
  else
    begin Prims.l_False end end

let choice_invariant (facts: t_Slice Native.t_Fact) (out: t_Slice Native.t_Fact) : nat -> Option.t_Option usize -> Type0 =
  fun _ choice -> choice_safe facts out choice

let choice_post (facts: t_Slice Native.t_Fact) (out: t_Slice Native.t_Fact) : Option.t_Option usize -> Type0 =
  fun choice -> choice_safe facts out choice

let choice_returned (facts: t_Slice Native.t_Fact) (out: t_Slice Native.t_Fact) : Result.t_Result (Option.t_Option usize) Native.t_Error -> Type0 =
  fun result -> match result with | Result.Result_Err _ -> begin Prims.l_True end | Result.Result_Ok choice -> begin choice_safe facts out choice end

let selected_id_is_unseen (facts: t_Slice Native.t_Fact) (out: t_Slice Native.t_Fact) : Lemma (ensures (choice_returned facts out) (Native.choose_unseen facts out)) =
  Nickel.LoopUtil.preserve_any (mk_usize 0) (Nickel.EditIdentity.length facts) (choice_invariant facts out) (choice_post facts out) (choice_returned facts out);
  norm_spec [delta_only ["Nickel_crdt.Edit.choose_unseen"; "Nickel.EditAccepted.choice_returned"; "Nickel.EditAccepted.choice_invariant"; "Nickel.EditAccepted.choice_post"; "Nickel.EditAccepted.choice_safe"; "Nickel.LoopUtil.output_safe"; "Nickel.LoopUtil.step_safe"]; iota; zeta_full; primops; unmeta; unascribe] (Native.choose_unseen facts out)

let push_result_unique (outcome: facts_vec & Result.t_Result unit Native.t_Error) : Type0 =
  match outcome with | (next, Result.Result_Ok _) -> begin ids_unique next end | _ -> begin Prims.l_True end

let append_fresh_preserves_unique (facts: facts_vec) (fact: Native.t_Fact) : Lemma (requires (ids_unique facts /\ Native.has_fact (Alloc.Vec.impl_1__as_slice facts) fact.f_id == false)) (ensures push_result_unique (Native.push facts fact)) =
  membership_absent (Alloc.Vec.impl_1__as_slice facts) fact.f_id;
  norm_spec [delta_only ["Nickel_crdt.Edit.push"; "Alloc.Vec.impl_1__push"; "Alloc.Vec.impl_1__as_slice"; "Alloc.Vec.impl_1__len"; "Rust_primitives.Sequence.seq_push"; "Rust_primitives.Sequence.seq_len"; "Rust_primitives.Sequence.seq_to_slice"; "Nickel.EditAccepted.push_result_unique"; "Nickel.EditAccepted.ids_unique"; "Nickel.EditIdentity.unique_ids"; "Nickel.EditIdentity.prefix_absent"; "Nickel.EditIdentity.length"; "Core_models.Slice.impl__len"; "Rust_primitives.Slice.slice_index"]; iota; zeta_full; primops; unmeta; unascribe] (Native.push facts fact)

let unique_invariant (at: nat) (facts: facts_vec) : Type0 =
  ids_unique facts

let canonical_result_unique (result: Result.t_Result facts_vec Native.t_Error) : Type0 =
  match result with | Result.Result_Ok facts -> begin ids_unique facts end | _ -> begin Prims.l_True end

let canonical_step_preserves_unique (facts: t_Slice Native.t_Fact) (out: facts_vec) : Lemma (requires ids_unique out) (ensures canonical_result_unique (Native.canonical_step facts out)) =
  selected_id_is_unseen facts (Alloc.Vec.impl_1__as_slice out);
  match Native.choose_unseen facts (Alloc.Vec.impl_1__as_slice out) with | Result.Result_Ok (Option.Option_Some i) -> begin if v i < v (Nickel.EditIdentity.length facts) then
    begin append_fresh_preserves_unique out (Rust_primitives.Slice.slice_index facts i) end
  else
    begin () end end | _ -> begin () end;
  norm_spec [delta_only ["Nickel_crdt.Edit.canonical_step"; "Core_models.Bundle.impl__ok_or"; "Core_models.Option.impl__ok_or"; "Core_models.Clone.f_clone"; "Nickel_crdt.Edit.impl_26"; "Nickel.EditAccepted.canonical_result_unique"; "Nickel.EditAccepted.choice_returned"; "Nickel.EditAccepted.choice_safe"; "Nickel.EditAccepted.push_result_unique"]; iota; zeta_full; primops; unmeta; unascribe] (Native.canonical_step facts out)

let empty_has_unique_ids () : Lemma (ensures ids_unique (Alloc.Vec.impl__new ())) =
  norm_spec [delta_only ["Nickel.EditAccepted.ids_unique"; "Nickel.EditIdentity.unique_ids"; "Nickel.EditIdentity.length"; "Core_models.Slice.impl__len"; "Alloc.Vec.impl__new"; "Alloc.Vec.impl_1__as_slice"; "Rust_primitives.Sequence.seq_empty"; "Rust_primitives.Sequence.seq_to_slice"]; iota; zeta_full; primops] (ids_unique (Alloc.Vec.impl__new ()))

let canonical_has_unique_ids (facts: t_Slice Native.t_Fact) : Lemma (ensures canonical_result_unique (Native.canonical facts)) =
  let each_step (out: facts_vec) : Lemma (requires ids_unique out) (ensures canonical_result_unique (Native.canonical_step facts out)) [SMTPat (Native.canonical_step facts out)] = canonical_step_preserves_unique facts out in
  empty_has_unique_ids ();
  Nickel.LoopUtil.preserve_any (mk_usize 0) (Nickel.EditIdentity.length facts) unique_invariant ids_unique canonical_result_unique;
  norm_spec [delta_only ["Nickel_crdt.Edit.canonical"; "Nickel.EditAccepted.unique_invariant"; "Nickel.EditAccepted.canonical_result_unique"; "Nickel.LoopUtil.output_safe"; "Nickel.LoopUtil.step_safe"]; iota; zeta_full; primops; unmeta; unascribe] (Native.canonical facts)

let tree_installation_preserves_facts (state: Native.t_Replica) (tree: Native.t_Tree) : Lemma (ensures (Native.impl_Replica__with_tree state tree).f_facts == state.f_facts) =
  norm_spec [delta_only ["Nickel_crdt.Edit.impl_Replica__with_tree"]; iota; zeta_full; primops] (Native.impl_Replica__with_tree state tree)

let candidate_facts (before: Native.t_Replica) (fact: Native.t_Fact) : facts_vec =
  match Native.push before.f_facts fact with | (facts, _) -> begin facts end

let canonical_publication (before: Native.t_Replica) (fact: Native.t_Fact) (outcome: Result.t_Result (Option.t_Option Native.t_Replica) Native.t_Error) : Type0 =
  match outcome with | Result.Result_Ok (Option.Option_Some next) -> begin Native.canonical (Alloc.Vec.impl_1__as_slice (candidate_facts before fact)) == Result.Result_Ok next.f_facts end | _ -> begin Prims.l_True end

let plan_publishes_canonical_facts (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (ensures canonical_publication before fact (Native.impl_Replica__plan before fact)) =
  norm_spec [delta_only ["Nickel_crdt.Edit.impl_Replica__plan"; "Nickel_crdt.Edit.impl_Replica__with_tree"; "Nickel.EditAccepted.canonical_publication"; "Nickel.EditAccepted.candidate_facts"; "Core_models.Clone.f_clone"; "Nickel_crdt.Edit.impl_26"; "Nickel_crdt.Edit.impl_82"]; iota; zeta_full; primops; unmeta; unascribe] (canonical_publication before fact (Native.impl_Replica__plan before fact))

let added_state_unique (outcome: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) : Type0 =
  match outcome with | (next, Result.Result_Ok Native.Admission_Added) -> begin ids_unique next.f_facts end | _ -> begin Prims.l_True end

let receive_added_ids_are_unique (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (ensures added_state_unique (Native.impl_Replica__receive before fact)) =
  plan_publishes_canonical_facts before fact;
  canonical_has_unique_ids (Alloc.Vec.impl_1__as_slice (candidate_facts before fact));
  norm_spec [delta_only ["Nickel_crdt.Edit.impl_Replica__receive"; "Nickel.EditAccepted.added_state_unique"; "Nickel.EditAccepted.canonical_publication"; "Nickel.EditAccepted.canonical_result_unique"]; iota; zeta_full; primops; unmeta; unascribe] (added_state_unique (Native.impl_Replica__receive before fact))

let receive_state_unique (outcome: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) : Type0 =
  match outcome with | (next, _) -> begin ids_unique next.f_facts end

let receive_preserves_unique_ids (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (requires ids_unique before.f_facts) (ensures receive_state_unique (Native.impl_Replica__receive before fact)) =
  Nickel.EditAtomic.receive_rejection_unchanged before fact;
  receive_added_ids_are_unique before fact;
  norm_spec [delta_only ["Nickel.EditAccepted.receive_state_unique"; "Nickel.EditAccepted.added_state_unique"; "Nickel.EditAtomic.receive_neutral"]; iota; zeta_full; primops] (receive_state_unique (Native.impl_Replica__receive before fact))

let edit_state_unique (outcome: Native.t_Replica & Result.t_Result Native.t_Local Native.t_Error) : Type0 =
  match outcome with | (next, _) -> begin ids_unique next.f_facts end

let edit_preserves_unique_ids (before: Native.t_Replica) (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (delete: Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global) : Lemma (requires ids_unique before.f_facts) (ensures edit_state_unique (Native.impl_Replica__edit before gap insert delete)) =
  Nickel.EditAtomic.edit_rejection_or_empty_unchanged before gap insert delete;
  Nickel.EditCommit.authored_fact_replays_same_commit before gap insert delete;
  match Native.impl_Replica__edit before gap insert delete with | (_, Result.Result_Ok (Native.Local_Authored fact)) -> begin receive_added_ids_are_unique before fact end | _ -> begin () end;
  norm_spec [delta_only ["Nickel.EditAccepted.edit_state_unique"; "Nickel.EditAccepted.added_state_unique"; "Nickel.EditAtomic.edit_neutral"; "Nickel.EditCommit.same_commit"]; iota; zeta_full; primops] (edit_state_unique (Native.impl_Replica__edit before gap insert delete))

let new_state_unique (outcome: Result.t_Result Native.t_Replica Native.t_Error) : Type0 =
  match outcome with | Result.Result_Ok state -> begin ids_unique state.f_facts end | _ -> begin Prims.l_True end

let new_establishes_unique_ids (writer: Option.t_Option Native.t_Writer) (limits: Native.t_Limits) : Lemma (ensures new_state_unique (Native.impl_Replica__new writer limits)) =
  empty_has_unique_ids ();
  norm_spec [delta_only ["Nickel_crdt.Edit.impl_Replica__new"; "Nickel.EditAccepted.new_state_unique"]; iota; zeta_full; primops] (new_state_unique (Native.impl_Replica__new writer limits))