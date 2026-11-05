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

module Tactics = FStar.Tactics.V2

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

let selected_fact_keeps_id (fact: Native.t_Fact) : Lemma (ensures (Native.clone_selected_fact fact).f_id == fact.f_id) =
  norm_spec [delta_only ["Nickel_crdt.Edit.clone_selected_fact"; "Core_models.Clone.f_clone"; "Nickel_crdt.Edit.impl_26"]; iota; zeta_full; primops; unmeta; unascribe] (Native.clone_selected_fact fact)

let canonical_step_preserves_unique (facts: t_Slice Native.t_Fact) (out: facts_vec) : Lemma (requires ids_unique out) (ensures canonical_result_unique (Native.canonical_step facts out)) =
  selected_id_is_unseen facts (Alloc.Vec.impl_1__as_slice out);
  match Native.choose_unseen facts (Alloc.Vec.impl_1__as_slice out) with | Result.Result_Ok (Option.Option_Some i) -> begin if v i < v (Nickel.EditIdentity.length facts) then
    begin selected_fact_keeps_id (Rust_primitives.Slice.slice_index facts i);
    append_fresh_preserves_unique out (Native.clone_selected_fact (Rust_primitives.Slice.slice_index facts i)) end
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
  assert (canonical_publication before fact (Native.impl_Replica__plan before fact)) by (
    Tactics.norm [delta_only ["Nickel_crdt.Edit.impl_Replica__plan"; "Nickel_crdt.Edit.impl_Replica__with_tree"; "Nickel.EditAccepted.canonical_publication"; "Nickel.EditAccepted.candidate_facts"; "Core_models.Clone.f_clone"; "Nickel_crdt.Edit.impl_26"; "Nickel_crdt.Edit.impl_82"]; iota; zeta_full; primops; unmeta; unascribe];
    Tactics.smt_sync' 1 1
  )

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

let selected_fact_is_exact (fact: Native.t_Fact) : Lemma (ensures Native.clone_selected_fact fact == fact) =
  norm_spec [delta_only ["Nickel_crdt.Edit.clone_selected_fact"; "Core_models.Clone.f_clone"; "Nickel_crdt.Edit.impl_26"]; iota; zeta_full; primops; unmeta; unascribe] (Native.clone_selected_fact fact)

let fact_present (facts: t_Slice Native.t_Fact) (fact: Native.t_Fact) : Type0 =
  exists(i: nat). Prims.l_and (i < FStar.Seq.length facts) (FStar.Seq.index facts i == fact)

let selected_whole_facts (input: t_Slice Native.t_Fact) (output: facts_vec) : Type0 =
  forall(i: nat). i < FStar.Seq.length (Alloc.Vec.impl_1__as_slice output) ==> fact_present input (FStar.Seq.index (Alloc.Vec.impl_1__as_slice output) i)

let content_invariant (input: t_Slice Native.t_Fact) (at: nat) (out: facts_vec) : Type0 =
  Prims.l_and (v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice out)) == at) (selected_whole_facts input out)

let content_step_result (input: t_Slice Native.t_Fact) (at: nat) (result: Result.t_Result facts_vec Native.t_Error) : Type0 =
  match result with | Result.Result_Ok out -> begin content_invariant input (at + 1) out end | _ -> begin Prims.l_True end

let append_content_result (input: t_Slice Native.t_Fact) (out: facts_vec) (outcome: facts_vec & Result.t_Result unit Native.t_Error) : Type0 =
  match outcome with | (next, Result.Result_Ok _) -> begin content_invariant input (v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice out)) + 1) next end | _ -> begin Prims.l_True end

let append_whole_fact (input: t_Slice Native.t_Fact) (out: facts_vec) (fact: Native.t_Fact) : Lemma (requires (selected_whole_facts input out /\ fact_present input fact)) (ensures append_content_result input out (Native.push out fact)) =
  norm_spec [delta_only ["Nickel_crdt.Edit.push"; "Alloc.Vec.impl_1__push"; "Alloc.Vec.impl_1__as_slice"; "Alloc.Vec.impl_1__len"; "Rust_primitives.Sequence.seq_push"; "Rust_primitives.Sequence.seq_len"; "Rust_primitives.Sequence.seq_to_slice"; "Nickel.EditAccepted.append_content_result"; "Nickel.EditAccepted.content_invariant"; "Nickel.EditAccepted.selected_whole_facts"; "Nickel.EditIdentity.length"; "Core_models.Slice.impl__len"; "Rust_primitives.Slice.slice_index"]; iota; zeta_full; primops; unmeta; unascribe] (Native.push out fact)

let canonical_step_selects_whole_facts (input: t_Slice Native.t_Fact) (out: facts_vec) (at: nat) : Lemma (requires content_invariant input at out) (ensures content_step_result input at (Native.canonical_step input out)) =
  match Native.choose_unseen input (Alloc.Vec.impl_1__as_slice out) with | Result.Result_Ok (Option.Option_Some i) -> begin if v i < v (Nickel.EditIdentity.length input) then
    begin selected_fact_is_exact (Rust_primitives.Slice.slice_index input i);
    assert (fact_present input (Rust_primitives.Slice.slice_index input i));
    append_whole_fact input out (Rust_primitives.Slice.slice_index input i) end
  else
    begin () end end | _ -> begin () end;
  norm_spec [delta_only ["Nickel_crdt.Edit.canonical_step"; "Core_models.Bundle.impl__ok_or"; "Core_models.Option.impl__ok_or"; "Core_models.Clone.f_clone"; "Nickel_crdt.Edit.impl_26"; "Nickel.EditAccepted.content_step_result"; "Nickel.EditAccepted.content_invariant"]; iota; zeta_full; primops; unmeta; unascribe] (Native.canonical_step input out)

let canonical_content_result (input: t_Slice Native.t_Fact) (result: Result.t_Result facts_vec Native.t_Error) : Type0 =
  match result with | Result.Result_Ok out -> begin content_invariant input (v (Nickel.EditIdentity.length input)) out end | _ -> begin Prims.l_True end

let canonical_selects_whole_facts (input: t_Slice Native.t_Fact) : Lemma (ensures canonical_content_result input (Native.canonical input)) =
  let each_content_step (out: facts_vec) : Lemma (requires selected_whole_facts input out) (ensures content_step_result input (v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice out))) (Native.canonical_step input out)) [SMTPat (Native.canonical_step input out)] = canonical_step_selects_whole_facts input out (v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice out))) in
  norm_spec [delta_only ["Nickel.EditAccepted.content_invariant"; "Nickel.EditAccepted.selected_whole_facts"; "Nickel.EditIdentity.length"; "Core_models.Slice.impl__len"; "Alloc.Vec.impl__new"; "Alloc.Vec.impl_1__as_slice"; "Rust_primitives.Sequence.seq_empty"; "Rust_primitives.Sequence.seq_to_slice"]; iota; zeta_full; primops] (content_invariant input 0 (Alloc.Vec.impl__new ()));
  Nickel.LoopUtil.preserve_any (mk_usize 0) (Nickel.EditIdentity.length input) (content_invariant input) (content_invariant input (v (Nickel.EditIdentity.length input))) (canonical_content_result input);
  norm_spec [delta_only ["Nickel_crdt.Edit.canonical"; "Nickel.EditAccepted.content_invariant"; "Nickel.EditAccepted.content_step_result"; "Nickel.EditAccepted.canonical_content_result"; "Nickel.LoopUtil.output_safe"; "Nickel.LoopUtil.step_safe"]; iota; zeta_full; primops; unmeta; unascribe] (Native.canonical input)

open FStar.Classical

open FStar.Fin

module Seq = FStar.Seq

type fact_position (input: t_Slice Native.t_Fact) (fact: Native.t_Fact) = i: nat{Prims.l_and (i < Seq.length input) (Seq.index input i == fact)}

let find_fact_position (input: t_Slice Native.t_Fact) (fact: Native.t_Fact{fact_present input fact}) : fact_position input fact =
  match FStar.Fin.find input (fun old -> old ==? fact) 0 with | Some i -> begin i end | None -> begin 0 end

let squeezed_position (input: t_Slice Native.t_Fact{Seq.length input > 1}) (out: facts_vec{selected_whole_facts input out}) (missing: nat{Prims.l_and (missing < Seq.length input) (Prims.l_not (fact_present (Alloc.Vec.impl_1__as_slice out) (Seq.index input missing)))}) (at: nat{at < Seq.length (Alloc.Vec.impl_1__as_slice out)}) : FStar.Fin.under (Seq.length input - 1) =
  let position = find_fact_position input (Seq.index (Alloc.Vec.impl_1__as_slice out) at) in
  if position < missing then
    begin position end
  else
    begin position - 1 end

let squeezed_equal_facts (input: t_Slice Native.t_Fact{Seq.length input > 1}) (out: facts_vec{selected_whole_facts input out}) (missing: nat{Prims.l_and (missing < Seq.length input) (Prims.l_not (fact_present (Alloc.Vec.impl_1__as_slice out) (Seq.index input missing)))}) (i: nat{i < Seq.length (Alloc.Vec.impl_1__as_slice out)}) (j: nat{j < Seq.length (Alloc.Vec.impl_1__as_slice out)}) : Lemma (requires squeezed_position input out missing i == squeezed_position input out missing j) (ensures Seq.index (Alloc.Vec.impl_1__as_slice out) i == Seq.index (Alloc.Vec.impl_1__as_slice out) j) =
  norm_spec [delta_only ["Nickel.EditAccepted.squeezed_position"]; iota; zeta_full; primops] (squeezed_position input out missing i);
  norm_spec [delta_only ["Nickel.EditAccepted.squeezed_position"]; iota; zeta_full; primops] (squeezed_position input out missing j)

let unique_positions (out: facts_vec) (i: usize{v i < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice out))}) (j: usize{v j < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice out))}) : Lemma (requires (ids_unique out /\ (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice out) i).f_id == (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice out) j).f_id)) (ensures i == j) =
  norm_spec [delta_only ["Nickel.EditAccepted.ids_unique"; "Nickel.EditIdentity.unique_ids"]; iota; zeta_full; primops] (ids_unique out)

let unique_nat_positions (out: facts_vec) (i: nat{i < Seq.length (Alloc.Vec.impl_1__as_slice out)}) (j: nat{j < Seq.length (Alloc.Vec.impl_1__as_slice out)}) : Lemma (requires (ids_unique out /\ Seq.index (Alloc.Vec.impl_1__as_slice out) i == Seq.index (Alloc.Vec.impl_1__as_slice out) j)) (ensures i == j) =
  norm_spec [delta_only ["Rust_primitives.Slice.slice_index"]; iota; zeta_full; primops] (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice out) (mk_usize i));
  norm_spec [delta_only ["Rust_primitives.Slice.slice_index"]; iota; zeta_full; primops] (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice out) (mk_usize j));
  unique_positions out (mk_usize i) (mk_usize j)

let whole_selection_covers (input: t_Slice Native.t_Fact) (out: facts_vec) : Lemma (requires (content_invariant input (v (Nickel.EditIdentity.length input)) out /\ ids_unique out)) (ensures forall(at: nat{at < Seq.length input}). fact_present (Alloc.Vec.impl_1__as_slice out) (Seq.index input at)) =
  let no_missing (at: nat{at < Seq.length input}) : Lemma (requires Prims.l_not (fact_present (Alloc.Vec.impl_1__as_slice out) (Seq.index input at))) (ensures Prims.l_False) [SMTPat (fact_present (Alloc.Vec.impl_1__as_slice out) (Seq.index input at))] = if Seq.length input > 1 then
    begin let positions = Seq.init (Seq.length input) (squeezed_position input out at) in
    Seq.lemma_init_len (Seq.length input) (squeezed_position input out at);
    Seq.init_index (Seq.length input) (squeezed_position input out at);
    match FStar.Fin.pigeonhole positions with | (i, j) -> begin assert (i < j);
    assert (squeezed_position input out at i == squeezed_position input out at j);
    squeezed_equal_facts input out at i j;
    unique_nat_positions out i j end end
  else
    begin assert (Seq.length input == 1);
    assert (fact_present input (Seq.index (Alloc.Vec.impl_1__as_slice out) 0));
    assert (Seq.index (Alloc.Vec.impl_1__as_slice out) 0 == Seq.index input at);
    assert (fact_present (Alloc.Vec.impl_1__as_slice out) (Seq.index input at)) end in
  ()

let same_fact_contents (input: t_Slice Native.t_Fact) (out: facts_vec) : Type0 =
  forall(fact: Native.t_Fact). fact_present input fact <==> fact_present (Alloc.Vec.impl_1__as_slice out) fact

let canonical_exact_result (input: t_Slice Native.t_Fact) (result: Result.t_Result facts_vec Native.t_Error) : Type0 =
  match result with | Result.Result_Ok out -> begin Prims.l_and (same_fact_contents input out) (v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice out)) == v (Nickel.EditIdentity.length input)) end | _ -> begin Prims.l_True end

let canonical_preserves_exact_contents (input: t_Slice Native.t_Fact) : Lemma (ensures canonical_exact_result input (Native.canonical input)) =
  canonical_selects_whole_facts input;
  canonical_has_unique_ids input;
  match Native.canonical input with | Result.Result_Ok out -> begin whole_selection_covers input out end | _ -> begin () end;
  norm_spec [delta_only ["Nickel.EditAccepted.canonical_exact_result"; "Nickel.EditAccepted.canonical_content_result"; "Nickel.EditAccepted.canonical_result_unique"; "Nickel.EditAccepted.content_invariant"; "Nickel.EditAccepted.same_fact_contents"; "Nickel.EditAccepted.selected_whole_facts"; "Nickel.EditAccepted.fact_present"]; iota; zeta_full; primops] (canonical_exact_result input (Native.canonical input))

let appended_contents (before: facts_vec) (fact: Native.t_Fact) (next: facts_vec) : Type0 =
  Prims.l_and (v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice next)) == v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice before)) + 1) (forall(item: Native.t_Fact). fact_present (Alloc.Vec.impl_1__as_slice next) item <==> Prims.l_or (fact_present (Alloc.Vec.impl_1__as_slice before) item) (item == fact))

let push_exact_result (before: facts_vec) (fact: Native.t_Fact) (outcome: facts_vec & Result.t_Result unit Native.t_Error) : Type0 =
  match outcome with | (next, Result.Result_Ok _) -> begin appended_contents before fact next end | _ -> begin Prims.l_True end

let push_has_exact_contents (before: facts_vec) (fact: Native.t_Fact) : Lemma (ensures push_exact_result before fact (Native.push before fact)) =
  norm_spec [delta_only ["Nickel_crdt.Edit.push"; "Alloc.Vec.impl_1__push"; "Alloc.Vec.impl_1__as_slice"; "Alloc.Vec.impl_1__len"; "Rust_primitives.Sequence.seq_push"; "Rust_primitives.Sequence.seq_len"; "Rust_primitives.Sequence.seq_to_slice"; "Nickel.EditAccepted.push_exact_result"; "Nickel.EditAccepted.appended_contents"; "Nickel.EditAccepted.fact_present"; "Nickel.EditIdentity.length"; "Core_models.Slice.impl__len"]; iota; zeta_full; primops; unmeta; unascribe] (Native.push before fact)

let plan_push_succeeded (before: Native.t_Replica) (fact: Native.t_Fact) (outcome: Result.t_Result (Option.t_Option Native.t_Replica) Native.t_Error) : Type0 =
  match outcome with | Result.Result_Ok (Option.Option_Some _) -> begin match Native.push before.f_facts fact with | (_, result) -> begin result == Result.Result_Ok () end end | _ -> begin Prims.l_True end

let successful_plan_pushed_fact (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (ensures plan_push_succeeded before fact (Native.impl_Replica__plan before fact)) =
  norm_spec [delta_only ["Nickel_crdt.Edit.impl_Replica__plan"; "Nickel.EditAccepted.plan_push_succeeded"; "Core_models.Clone.f_clone"; "Nickel_crdt.Edit.impl_26"; "Nickel_crdt.Edit.impl_82"]; iota; zeta_full; primops; unmeta; unascribe] (plan_push_succeeded before fact (Native.impl_Replica__plan before fact))

let plan_exact_contents (before: Native.t_Replica) (fact: Native.t_Fact) (outcome: Result.t_Result (Option.t_Option Native.t_Replica) Native.t_Error) : Type0 =
  match outcome with | Result.Result_Ok (Option.Option_Some next) -> begin appended_contents before.f_facts fact next.f_facts end | _ -> begin Prims.l_True end

let successful_plan_has_exact_contents (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (ensures plan_exact_contents before fact (Native.impl_Replica__plan before fact)) =
  successful_plan_pushed_fact before fact;
  push_has_exact_contents before.f_facts fact;
  plan_publishes_canonical_facts before fact;
  canonical_preserves_exact_contents (Alloc.Vec.impl_1__as_slice (candidate_facts before fact));
  norm_spec [delta_only ["Nickel.EditAccepted.plan_exact_contents"; "Nickel.EditAccepted.appended_contents"; "Nickel.EditAccepted.plan_push_succeeded"; "Nickel.EditAccepted.push_exact_result"; "Nickel.EditAccepted.canonical_publication"; "Nickel.EditAccepted.candidate_facts"; "Nickel.EditAccepted.canonical_exact_result"; "Nickel.EditAccepted.same_fact_contents"]; iota; zeta_full; primops] (plan_exact_contents before fact (Native.impl_Replica__plan before fact))

let added_exact_contents (before: Native.t_Replica) (fact: Native.t_Fact) (outcome: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) : Type0 =
  match outcome with | (next, Result.Result_Ok Native.Admission_Added) -> begin appended_contents before.f_facts fact next.f_facts end | _ -> begin Prims.l_True end

let receive_added_has_exact_contents (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (ensures added_exact_contents before fact (Native.impl_Replica__receive before fact)) =
  successful_plan_has_exact_contents before fact;
  norm_spec [delta_only ["Nickel_crdt.Edit.impl_Replica__receive"; "Nickel.EditAccepted.added_exact_contents"; "Nickel.EditAccepted.plan_exact_contents"]; iota; zeta_full; primops] (added_exact_contents before fact (Native.impl_Replica__receive before fact))

let authored_exact_contents (before: Native.t_Replica) (outcome: Native.t_Replica & Result.t_Result Native.t_Local Native.t_Error) : Type0 =
  match outcome with | (next, Result.Result_Ok (Native.Local_Authored fact)) -> begin appended_contents before.f_facts fact next.f_facts end | _ -> begin Prims.l_True end

let edit_authored_has_exact_contents (before: Native.t_Replica) (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (delete: Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global) : Lemma (ensures authored_exact_contents before (Native.impl_Replica__edit before gap insert delete)) =
  Nickel.EditCommit.authored_fact_replays_same_commit before gap insert delete;
  match Native.impl_Replica__edit before gap insert delete with | (_, Result.Result_Ok (Native.Local_Authored fact)) -> begin receive_added_has_exact_contents before fact end | _ -> begin () end;
  norm_spec [delta_only ["Nickel.EditAccepted.authored_exact_contents"; "Nickel.EditAccepted.added_exact_contents"; "Nickel.EditCommit.same_commit"]; iota; zeta_full; primops] (authored_exact_contents before (Native.impl_Replica__edit before gap insert delete))

let event_key (id: Native.t_EventId) : nat =
  let rank = match id.f_writer with | Native.Writer_Alice -> begin 0 end | Native.Writer_Bo -> begin 18446744073709551616 end in
  rank + v id.f_counter

let event_order_is_key_order (a: Native.t_EventId) (b: Native.t_EventId) : Lemma (ensures Native.event_lt a b == true <==> event_key a < event_key b) =
  norm_spec [delta_only ["Nickel_crdt.Edit.event_lt"; "Nickel_crdt.Edit.writer_index"; "Nickel.EditAccepted.event_key"]; iota; zeta_full; primops] (Native.event_lt a b)

let least_choice (input: t_Slice Native.t_Fact) (out: t_Slice Native.t_Fact) (at: nat) (choice: Option.t_Option usize) : Type0 =
  match choice with | Option.Option_None -> begin forall(j: usize{v j < v (Nickel.EditIdentity.length input)}). v j < at ==> Native.has_fact out (Rust_primitives.Slice.slice_index input j).f_id end | Option.Option_Some k -> begin Prims.l_and (Prims.l_and (v k < v (Nickel.EditIdentity.length input)) (Native.has_fact out (Rust_primitives.Slice.slice_index input k).f_id == false)) (forall(j: usize{v j < v (Nickel.EditIdentity.length input)}). Prims.l_and (v j < at) (Native.has_fact out (Rust_primitives.Slice.slice_index input j).f_id == false) ==> event_key (Rust_primitives.Slice.slice_index input k).f_id <= event_key (Rust_primitives.Slice.slice_index input j).f_id) end

let least_result (input: t_Slice Native.t_Fact) (out: t_Slice Native.t_Fact) (result: Result.t_Result (Option.t_Option usize) Native.t_Error) : Type0 =
  match result with | Result.Result_Ok choice -> begin least_choice input out (v (Nickel.EditIdentity.length input)) choice end | _ -> begin Prims.l_True end

let selected_id_is_least (input: t_Slice Native.t_Fact) (out: t_Slice Native.t_Fact) : Lemma (ensures least_result input out (Native.choose_unseen input out)) =
  let each_order (a: Native.t_EventId) (b: Native.t_EventId) : Lemma (ensures Native.event_lt a b == true <==> event_key a < event_key b) [SMTPat (Native.event_lt a b)] = event_order_is_key_order a b in
  Nickel.LoopUtil.preserve_any (mk_usize 0) (Nickel.EditIdentity.length input) (least_choice input out) (least_choice input out (v (Nickel.EditIdentity.length input))) (least_result input out);
  norm_spec [delta_only ["Nickel_crdt.Edit.choose_unseen"; "Nickel.EditAccepted.least_choice"; "Nickel.EditAccepted.least_result"; "Nickel.LoopUtil.output_safe"; "Nickel.LoopUtil.step_safe"]; iota; zeta_full; primops; unmeta; unascribe] (Native.choose_unseen input out)

let rec absent_lookup (input: t_Slice Native.t_Fact) (id: Native.t_EventId) (at: usize{v at <= v (Nickel.EditIdentity.length input)}) : Lemma (requires Nickel.EditIdentity.prefix_absent input id at (Nickel.EditIdentity.length input)) (ensures Nickel.EditIdentity.first_id input id at == Option.Option_None) (decreases v (Nickel.EditIdentity.length input) - v at) =
  if v at < v (Nickel.EditIdentity.length input) then
    begin absent_lookup input id (at +! mk_int 1) end
  else
    begin () end;
  norm_spec [delta_once ["Nickel.EditIdentity.first_id"]; iota; zeta; primops] (Nickel.EditIdentity.first_id input id at)

let membership_absence_exact (input: t_Slice Native.t_Fact) (id: Native.t_EventId) : Lemma (ensures Native.has_fact input id == false <==> Nickel.EditIdentity.prefix_absent input id (mk_usize 0) (Nickel.EditIdentity.length input)) =
  membership_exact input id;
  if Native.has_fact input id then
    begin () end
  else
    begin membership_absent input id end;
  let reverse (dummy: unit) : Lemma (requires Nickel.EditIdentity.prefix_absent input id (mk_usize 0) (Nickel.EditIdentity.length input)) (ensures Native.has_fact input id == false) =
    absent_lookup input id (mk_usize 0);
    norm_spec [delta_only ["Nickel.EditAccepted.member_value"]; iota] (member_value (Nickel.EditIdentity.first_id input id (mk_usize 0))) in
  FStar.Classical.move_requires reverse ();
  norm_spec [delta_only ["Nickel.EditAccepted.member_value"]; iota] (member_value (Nickel.EditIdentity.first_id input id (mk_usize 0)))

let facts_ordered (facts: facts_vec) : Type0 =
  forall(i: usize{v i < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice facts))}) (j: usize{v j < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice facts))}). v i < v j ==> event_key (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice facts) i).f_id <= event_key (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice facts) j).f_id

let order_frontier (input: t_Slice Native.t_Fact) (out: facts_vec) : Type0 =
  Prims.l_and (facts_ordered out) (forall(i: usize{v i < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice out))}) (j: usize{v j < v (Nickel.EditIdentity.length input)}). Native.has_fact (Alloc.Vec.impl_1__as_slice out) (Rust_primitives.Slice.slice_index input j).f_id == false ==> event_key (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice out) i).f_id <= event_key (Rust_primitives.Slice.slice_index input j).f_id)

let ordered_push_result (input: t_Slice Native.t_Fact) (result: facts_vec & Result.t_Result unit Native.t_Error) : Type0 =
  match result with | (next, Result.Result_Ok _) -> begin order_frontier input next end | _ -> begin Prims.l_True end

let absent_after_push (out: facts_vec) (fact: Native.t_Fact) (id: Native.t_EventId) (result: facts_vec & Result.t_Result unit Native.t_Error) : Type0 =
  match result with | (next, Result.Result_Ok _) -> begin Native.has_fact (Alloc.Vec.impl_1__as_slice next) id == false <==> Prims.l_and (Native.has_fact (Alloc.Vec.impl_1__as_slice out) id == false) (Prims.l_not (fact.f_id == id)) end | _ -> begin Prims.l_True end

let push_membership (out: facts_vec) (fact: Native.t_Fact) (id: Native.t_EventId) : Lemma (ensures absent_after_push out fact id (Native.push out fact)) =
  membership_absence_exact (Alloc.Vec.impl_1__as_slice out) id;
  match Native.push out fact with | (next, Result.Result_Ok _) -> begin membership_absence_exact (Alloc.Vec.impl_1__as_slice next) id;
  norm_spec [delta_only ["Nickel_crdt.Edit.push"; "Alloc.Vec.impl_1__push"; "Alloc.Vec.impl_1__as_slice"; "Alloc.Vec.impl_1__len"; "Rust_primitives.Sequence.seq_push"; "Rust_primitives.Sequence.seq_len"; "Rust_primitives.Sequence.seq_to_slice"; "Rust_primitives.Slice.slice_index"; "Nickel.EditIdentity.length"; "Core_models.Slice.impl__len"; "Nickel.EditIdentity.prefix_absent"; "Nickel.EditAccepted.absent_after_push"]; iota; zeta_full; primops; unmeta; unascribe] (absent_after_push out fact id (Native.push out fact)) end | _ -> begin () end

let append_least_preserves_frontier (input: t_Slice Native.t_Fact) (out: facts_vec) (k: usize{v k < v (Nickel.EditIdentity.length input)}) : Lemma (requires (order_frontier input out /\ least_choice input (Alloc.Vec.impl_1__as_slice out) (v (Nickel.EditIdentity.length input)) (Option.Option_Some k))) (ensures ordered_push_result input (Native.push out (Rust_primitives.Slice.slice_index input k))) =
  norm_spec [delta_only ["Nickel.EditAccepted.order_frontier"; "Nickel.EditAccepted.facts_ordered"]; iota; zeta_full] (order_frontier input out);
  norm_spec [delta_only ["Nickel.EditAccepted.least_choice"]; iota; zeta_full] (least_choice input (Alloc.Vec.impl_1__as_slice out) (v (Nickel.EditIdentity.length input)) (Option.Option_Some k));
  let fact = Rust_primitives.Slice.slice_index input k in
  match Native.push out fact with | (next, Result.Result_Ok _) -> begin let each_frontier (i: usize{v i < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice next))}) (j: usize{v j < v (Nickel.EditIdentity.length input)}) : Lemma (requires Native.has_fact (Alloc.Vec.impl_1__as_slice next) (Rust_primitives.Slice.slice_index input j).f_id == false) (ensures event_key (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice next) i).f_id <= event_key (Rust_primitives.Slice.slice_index input j).f_id) =
    push_membership out fact (Rust_primitives.Slice.slice_index input j).f_id;
    norm_spec [delta_only ["Nickel.EditAccepted.absent_after_push"]; iota; zeta_full] (absent_after_push out fact (Rust_primitives.Slice.slice_index input j).f_id (Native.push out fact));
    norm_spec [delta_only ["Nickel_crdt.Edit.push"; "Alloc.Vec.impl_1__push"; "Alloc.Vec.impl_1__as_slice"; "Alloc.Vec.impl_1__len"; "Rust_primitives.Sequence.seq_push"; "Rust_primitives.Sequence.seq_len"; "Rust_primitives.Sequence.seq_to_slice"; "Rust_primitives.Slice.slice_index"; "Nickel.EditIdentity.length"; "Core_models.Slice.impl__len"]; iota; zeta_full; primops; unmeta; unascribe] (Native.push out fact);
    assert (Native.has_fact (Alloc.Vec.impl_1__as_slice out) (Rust_primitives.Slice.slice_index input j).f_id == false);
    if v i < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice out)) then
      begin assert (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice next) i == Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice out) i);
      assert (event_key (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice out) i).f_id <= event_key (Rust_primitives.Slice.slice_index input j).f_id) end
    else
      begin assert (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice next) i == fact);
      assert (event_key fact.f_id <= event_key (Rust_primitives.Slice.slice_index input j).f_id) end in
  let each_frontier_imp (i: usize{v i < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice next))}) (j: usize{v j < v (Nickel.EditIdentity.length input)}) : Lemma (ensures Native.has_fact (Alloc.Vec.impl_1__as_slice next) (Rust_primitives.Slice.slice_index input j).f_id == false ==> event_key (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice next) i).f_id <= event_key (Rust_primitives.Slice.slice_index input j).f_id) = FStar.Classical.move_requires_2 each_frontier i j in
  FStar.Classical.forall_intro_2 each_frontier_imp;
  let each_pair (i: usize{v i < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice next))}) (j: usize{v j < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice next))}) : Lemma (ensures v i < v j ==> event_key (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice next) i).f_id <= event_key (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice next) j).f_id) =
    norm_spec [delta_only ["Nickel_crdt.Edit.push"; "Alloc.Vec.impl_1__push"; "Alloc.Vec.impl_1__as_slice"; "Alloc.Vec.impl_1__len"; "Rust_primitives.Sequence.seq_push"; "Rust_primitives.Sequence.seq_len"; "Rust_primitives.Sequence.seq_to_slice"; "Rust_primitives.Slice.slice_index"; "Nickel.EditIdentity.length"; "Core_models.Slice.impl__len"]; iota; zeta_full; primops; unmeta; unascribe] (Native.push out fact);
    if v i < v j then
      begin assert (v i < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice out)));
      assert (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice next) i == Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice out) i);
      if v j < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice out)) then
        begin assert (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice next) j == Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice out) j);
        assert (event_key (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice out) i).f_id <= event_key (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice out) j).f_id) end
      else
        begin assert (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice next) j == fact);
        assert (event_key (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice out) i).f_id <= event_key fact.f_id) end end
    else
      begin () end in
  FStar.Classical.forall_intro_2 each_pair;
  norm_spec [delta_only ["Nickel.EditAccepted.ordered_push_result"; "Nickel.EditAccepted.order_frontier"; "Nickel.EditAccepted.facts_ordered"]; iota; zeta_full] (ordered_push_result input (Native.push out fact)) end | _ -> begin () end

let order_step_result (input: t_Slice Native.t_Fact) (result: Result.t_Result facts_vec Native.t_Error) : Type0 =
  match result with | Result.Result_Ok next -> begin order_frontier input next end | _ -> begin Prims.l_True end

let canonical_step_preserves_order (input: t_Slice Native.t_Fact) (out: facts_vec) : Lemma (requires order_frontier input out) (ensures order_step_result input (Native.canonical_step input out)) =
  selected_id_is_least input (Alloc.Vec.impl_1__as_slice out);
  match Native.choose_unseen input (Alloc.Vec.impl_1__as_slice out) with | Result.Result_Ok (Option.Option_Some k) -> begin if v k < v (Nickel.EditIdentity.length input) then
    begin selected_fact_is_exact (Rust_primitives.Slice.slice_index input k);
    append_least_preserves_frontier input out k end
  else
    begin () end end | _ -> begin () end;
  norm_spec [delta_only ["Nickel_crdt.Edit.canonical_step"; "Core_models.Bundle.impl__ok_or"; "Core_models.Option.impl__ok_or"; "Nickel.EditAccepted.least_result"; "Nickel.EditAccepted.order_step_result"; "Nickel.EditAccepted.ordered_push_result"]; iota; zeta_full; primops; unmeta; unascribe] (order_step_result input (Native.canonical_step input out))

let order_invariant (input: t_Slice Native.t_Fact) (at: nat) (out: facts_vec) : Type0 =
  order_frontier input out

let canonical_orders_facts (input: t_Slice Native.t_Fact) : Lemma (ensures order_step_result input (Native.canonical input)) =
  let each_order_step (out: facts_vec) : Lemma (requires order_frontier input out) (ensures order_step_result input (Native.canonical_step input out)) [SMTPat (Native.canonical_step input out)] = canonical_step_preserves_order input out in
  norm_spec [delta_only ["Nickel.EditAccepted.order_frontier"; "Nickel.EditAccepted.facts_ordered"; "Nickel.EditIdentity.length"; "Core_models.Slice.impl__len"; "Alloc.Vec.impl__new"; "Alloc.Vec.impl_1__as_slice"; "Rust_primitives.Sequence.seq_empty"; "Rust_primitives.Sequence.seq_to_slice"]; iota; zeta_full; primops] (order_frontier input (Alloc.Vec.impl__new ()));
  Nickel.LoopUtil.preserve_any (mk_usize 0) (Nickel.EditIdentity.length input) (order_invariant input) (order_frontier input) (order_step_result input);
  norm_spec [delta_only ["Nickel_crdt.Edit.canonical"; "Nickel.EditAccepted.order_invariant"; "Nickel.EditAccepted.order_step_result"; "Nickel.LoopUtil.output_safe"; "Nickel.LoopUtil.step_safe"]; iota; zeta_full; primops; unmeta; unascribe] (order_step_result input (Native.canonical input))

let added_ordered (outcome: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) : Type0 =
  match outcome with | (next, Result.Result_Ok Native.Admission_Added) -> begin facts_ordered next.f_facts end | _ -> begin Prims.l_True end

let receive_added_facts_are_ordered (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (ensures added_ordered (Native.impl_Replica__receive before fact)) =
  plan_publishes_canonical_facts before fact;
  canonical_orders_facts (Alloc.Vec.impl_1__as_slice (candidate_facts before fact));
  norm_spec [delta_only ["Nickel_crdt.Edit.impl_Replica__receive"; "Nickel.EditAccepted.added_ordered"; "Nickel.EditAccepted.canonical_publication"; "Nickel.EditAccepted.order_step_result"; "Nickel.EditAccepted.order_frontier"]; iota; zeta_full; primops; unmeta; unascribe] (added_ordered (Native.impl_Replica__receive before fact))

let authored_ordered (outcome: Native.t_Replica & Result.t_Result Native.t_Local Native.t_Error) : Type0 =
  match outcome with | (next, Result.Result_Ok (Native.Local_Authored _)) -> begin facts_ordered next.f_facts end | _ -> begin Prims.l_True end

let authored_facts_are_ordered (before: Native.t_Replica) (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (delete: Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global) : Lemma (ensures authored_ordered (Native.impl_Replica__edit before gap insert delete)) =
  Nickel.EditCommit.authored_fact_replays_same_commit before gap insert delete;
  match Native.impl_Replica__edit before gap insert delete with | (_, Result.Result_Ok (Native.Local_Authored fact)) -> begin receive_added_facts_are_ordered before fact end | _ -> begin () end;
  norm_spec [delta_only ["Nickel.EditAccepted.authored_ordered"; "Nickel.EditAccepted.added_ordered"; "Nickel.EditCommit.same_commit"]; iota; zeta_full; primops; unmeta; unascribe] (authored_ordered (Native.impl_Replica__edit before gap insert delete))

let receive_state_ordered (outcome: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) : Type0 =
  match outcome with | (next, _) -> begin facts_ordered next.f_facts end

let receive_preserves_fact_order (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (requires facts_ordered before.f_facts) (ensures receive_state_ordered (Native.impl_Replica__receive before fact)) =
  Nickel.EditAtomic.receive_rejection_unchanged before fact;
  receive_added_facts_are_ordered before fact;
  norm_spec [delta_only ["Nickel.EditAccepted.receive_state_ordered"; "Nickel.EditAccepted.added_ordered"; "Nickel.EditAtomic.receive_neutral"]; iota; zeta_full; primops] (receive_state_ordered (Native.impl_Replica__receive before fact))

let edit_state_ordered (outcome: Native.t_Replica & Result.t_Result Native.t_Local Native.t_Error) : Type0 =
  match outcome with | (next, _) -> begin facts_ordered next.f_facts end

let edit_preserves_fact_order (before: Native.t_Replica) (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (delete: Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global) : Lemma (requires facts_ordered before.f_facts) (ensures edit_state_ordered (Native.impl_Replica__edit before gap insert delete)) =
  Nickel.EditAtomic.edit_rejection_or_empty_unchanged before gap insert delete;
  authored_facts_are_ordered before gap insert delete;
  norm_spec [delta_only ["Nickel.EditAccepted.edit_state_ordered"; "Nickel.EditAccepted.authored_ordered"; "Nickel.EditAtomic.edit_neutral"]; iota; zeta_full; primops] (edit_state_ordered (Native.impl_Replica__edit before gap insert delete))

let new_state_ordered (outcome: Result.t_Result Native.t_Replica Native.t_Error) : Type0 =
  match outcome with | Result.Result_Ok state -> begin facts_ordered state.f_facts end | _ -> begin Prims.l_True end

let new_establishes_fact_order (writer: Option.t_Option Native.t_Writer) (limits: Native.t_Limits) : Lemma (ensures new_state_ordered (Native.impl_Replica__new writer limits)) =
  norm_spec [delta_only ["Nickel_crdt.Edit.impl_Replica__new"; "Nickel.EditAccepted.new_state_ordered"; "Nickel.EditAccepted.facts_ordered"; "Nickel.EditIdentity.length"; "Core_models.Slice.impl__len"; "Alloc.Vec.impl__new"; "Alloc.Vec.impl_1__as_slice"; "Rust_primitives.Sequence.seq_empty"; "Rust_primitives.Sequence.seq_to_slice"]; iota; zeta_full; primops] (new_state_ordered (Native.impl_Replica__new writer limits))

let event_key_identifies_event (a: Native.t_EventId) (b: Native.t_EventId) : Lemma (requires event_key a == event_key b) (ensures a == b) =
  norm_spec [delta_only ["Nickel.EditAccepted.event_key"]; iota; zeta_full; primops] (event_key a);
  norm_spec [delta_only ["Nickel.EditAccepted.event_key"]; iota; zeta_full; primops] (event_key b)

let facts_strictly_ordered (facts: facts_vec) : Type0 =
  forall(i: usize{v i < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice facts))}) (j: usize{v j < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice facts))}). v i < v j ==> Native.event_lt (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice facts) i).f_id (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice facts) j).f_id == true

let ordered_unique_is_strict (facts: facts_vec) : Lemma (requires (ids_unique facts /\ facts_ordered facts)) (ensures facts_strictly_ordered facts) =
  norm_spec [delta_only ["Nickel.EditAccepted.facts_ordered"]; iota; zeta_full] (facts_ordered facts);
  let each_pair (i: usize{v i < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice facts))}) (j: usize{v j < v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice facts))}) : Lemma (ensures v i < v j ==> Native.event_lt (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice facts) i).f_id (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice facts) j).f_id == true) =
    let a = (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice facts) i).f_id in
    let b = (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice facts) j).f_id in
    if v i < v j then
      begin assert (event_key a <= event_key b);
      if event_key a ==? event_key b then
        begin event_key_identifies_event a b;
        unique_positions facts i j end
      else
        begin () end;
      event_order_is_key_order a b end
    else
      begin () end in
  FStar.Classical.forall_intro_2 each_pair;
  norm_spec [delta_only ["Nickel.EditAccepted.facts_strictly_ordered"]; iota; zeta_full] (facts_strictly_ordered facts)

let strict_canonical_result (result: Result.t_Result facts_vec Native.t_Error) : Type0 =
  match result with | Result.Result_Ok facts -> begin facts_strictly_ordered facts end | _ -> begin Prims.l_True end

let canonical_facts_are_strictly_ordered (input: t_Slice Native.t_Fact) : Lemma (ensures strict_canonical_result (Native.canonical input)) =
  canonical_has_unique_ids input;
  canonical_orders_facts input;
  match Native.canonical input with | Result.Result_Ok out -> begin ordered_unique_is_strict out end | _ -> begin () end;
  norm_spec [delta_only ["Nickel.EditAccepted.strict_canonical_result"; "Nickel.EditAccepted.canonical_result_unique"; "Nickel.EditAccepted.order_step_result"; "Nickel.EditAccepted.order_frontier"]; iota; zeta_full] (strict_canonical_result (Native.canonical input))

let prefix_equal (left: facts_vec) (right: facts_vec) (at: nat) : Type0 =
  forall(i: nat{Prims.l_and (i < Seq.length (Alloc.Vec.impl_1__as_slice left)) (i < Seq.length (Alloc.Vec.impl_1__as_slice right))}). i < at ==> Seq.index (Alloc.Vec.impl_1__as_slice left) i == Seq.index (Alloc.Vec.impl_1__as_slice right) i

let strict_nat_pair (facts: facts_vec) (i: nat{i < Seq.length (Alloc.Vec.impl_1__as_slice facts)}) (j: nat{j < Seq.length (Alloc.Vec.impl_1__as_slice facts)}) : Lemma (requires (facts_strictly_ordered facts /\ i < j)) (ensures event_key (Seq.index (Alloc.Vec.impl_1__as_slice facts) i).f_id < event_key (Seq.index (Alloc.Vec.impl_1__as_slice facts) j).f_id) =
  norm_spec [delta_only ["Nickel.EditAccepted.facts_strictly_ordered"; "Nickel.EditIdentity.length"; "Core_models.Slice.impl__len"; "Rust_primitives.Slice.slice_index"]; iota; zeta_full; primops] (facts_strictly_ordered facts);
  let ii = mk_usize i in
  let jj = mk_usize j in
  norm_spec [delta_only ["Rust_primitives.Slice.slice_index"]; iota; zeta_full; primops] (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice facts) ii);
  norm_spec [delta_only ["Rust_primitives.Slice.slice_index"]; iota; zeta_full; primops] (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice facts) jj);
  assert (Native.event_lt (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice facts) ii).f_id (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice facts) jj).f_id == true);
  event_order_is_key_order (Seq.index (Alloc.Vec.impl_1__as_slice facts) i).f_id (Seq.index (Alloc.Vec.impl_1__as_slice facts) j).f_id

let ordered_vectors_next (left: facts_vec) (right: facts_vec) (at: nat{Prims.l_and (at < Seq.length (Alloc.Vec.impl_1__as_slice left)) (at < Seq.length (Alloc.Vec.impl_1__as_slice right))}) : Lemma (requires (Prims.l_and (ids_unique left) (ids_unique right) /\ Prims.l_and (facts_strictly_ordered left) (facts_strictly_ordered right) /\ same_fact_contents (Alloc.Vec.impl_1__as_slice left) right /\ prefix_equal left right at)) (ensures Seq.index (Alloc.Vec.impl_1__as_slice left) at == Seq.index (Alloc.Vec.impl_1__as_slice right) at) =
  let a = Seq.index (Alloc.Vec.impl_1__as_slice left) at in
  let b = Seq.index (Alloc.Vec.impl_1__as_slice right) at in
  assert (fact_present (Alloc.Vec.impl_1__as_slice left) a);
  assert (fact_present (Alloc.Vec.impl_1__as_slice right) b);
  norm_spec [delta_only ["Nickel.EditAccepted.same_fact_contents"; "Nickel.EditAccepted.prefix_equal"]; iota; zeta_full] (same_fact_contents (Alloc.Vec.impl_1__as_slice left) right);
  norm_spec [delta_only ["Nickel.EditAccepted.prefix_equal"]; iota; zeta_full] (prefix_equal left right at);
  let j = find_fact_position (Alloc.Vec.impl_1__as_slice right) a in
  let k = find_fact_position (Alloc.Vec.impl_1__as_slice left) b in
  if j < at then
    begin unique_nat_positions left j at end
  else
    begin () end;
  if k < at then
    begin unique_nat_positions right k at end
  else
    begin () end;
  if at < j then
    begin strict_nat_pair right at j;
    if at < k then
      begin strict_nat_pair left at k end
    else
      begin assert (k == at) end;
    assert Prims.l_False end
  else
    begin assert (j == at) end

let rec ordered_vectors_prefix (left: facts_vec) (right: facts_vec) (at: nat{at <= Seq.length (Alloc.Vec.impl_1__as_slice left)}) : Lemma (requires (Seq.length (Alloc.Vec.impl_1__as_slice left) == Seq.length (Alloc.Vec.impl_1__as_slice right) /\ Prims.l_and (ids_unique left) (ids_unique right) /\ Prims.l_and (facts_strictly_ordered left) (facts_strictly_ordered right) /\ same_fact_contents (Alloc.Vec.impl_1__as_slice left) right /\ prefix_equal left right at)) (ensures prefix_equal left right (Seq.length (Alloc.Vec.impl_1__as_slice left))) (decreases Seq.length (Alloc.Vec.impl_1__as_slice left) - at) =
  if at < Seq.length (Alloc.Vec.impl_1__as_slice left) then
    begin ordered_vectors_next left right at;
    assert (prefix_equal left right (at + 1));
    ordered_vectors_prefix left right (at + 1) end
  else
    begin () end

let ordered_contents_determine_vector (left: facts_vec) (right: facts_vec) : Lemma (requires (Seq.length (Alloc.Vec.impl_1__as_slice left) == Seq.length (Alloc.Vec.impl_1__as_slice right) /\ Prims.l_and (ids_unique left) (ids_unique right) /\ Prims.l_and (facts_strictly_ordered left) (facts_strictly_ordered right) /\ same_fact_contents (Alloc.Vec.impl_1__as_slice left) right)) (ensures left == right) =
  norm_spec [delta_only ["Nickel.EditAccepted.prefix_equal"]; iota; zeta_full] (prefix_equal left right 0);
  ordered_vectors_prefix left right 0;
  norm_spec [delta_only ["Nickel.EditAccepted.prefix_equal"]; iota; zeta_full] (prefix_equal left right (Seq.length (Alloc.Vec.impl_1__as_slice left)));
  Seq.lemma_eq_intro (Alloc.Vec.impl_1__as_slice left) (Alloc.Vec.impl_1__as_slice right);
  Seq.lemma_eq_elim (Alloc.Vec.impl_1__as_slice left) (Alloc.Vec.impl_1__as_slice right);
  norm_spec [delta_only ["Alloc.Vec.impl_1__as_slice"; "Rust_primitives.Sequence.seq_to_slice"]; iota; zeta_full] (Alloc.Vec.impl_1__as_slice left);
  norm_spec [delta_only ["Alloc.Vec.impl_1__as_slice"; "Rust_primitives.Sequence.seq_to_slice"]; iota; zeta_full] (Alloc.Vec.impl_1__as_slice right)

let same_input_contents_and_length (left: t_Slice Native.t_Fact) (right: t_Slice Native.t_Fact) : Type0 =
  Prims.l_and (Seq.length left == Seq.length right) (forall(fact: Native.t_Fact). fact_present left fact <==> fact_present right fact)

let canonical_agreement (left: Result.t_Result facts_vec Native.t_Error) (right: Result.t_Result facts_vec Native.t_Error) : Type0 =
  match (left, right) with | (Result.Result_Ok a, Result.Result_Ok b) -> begin a == b end | _ -> begin Prims.l_True end

let canonical_is_permutation_independent (left: t_Slice Native.t_Fact) (right: t_Slice Native.t_Fact) : Lemma (requires same_input_contents_and_length left right) (ensures canonical_agreement (Native.canonical left) (Native.canonical right)) =
  canonical_preserves_exact_contents left;
  canonical_preserves_exact_contents right;
  canonical_has_unique_ids left;
  canonical_has_unique_ids right;
  canonical_facts_are_strictly_ordered left;
  canonical_facts_are_strictly_ordered right;
  norm_spec [delta_only ["Nickel.EditAccepted.same_input_contents_and_length"]; iota; zeta_full] (same_input_contents_and_length left right);
  match (Native.canonical left, Native.canonical right) with | (Result.Result_Ok a, Result.Result_Ok b) -> begin norm_spec [delta_only ["Nickel.EditAccepted.canonical_exact_result"; "Nickel.EditAccepted.same_fact_contents"; "Nickel.EditIdentity.length"; "Core_models.Slice.impl__len"]; iota; zeta_full] (canonical_exact_result left (Native.canonical left));
  norm_spec [delta_only ["Nickel.EditAccepted.canonical_exact_result"; "Nickel.EditAccepted.same_fact_contents"; "Nickel.EditIdentity.length"; "Core_models.Slice.impl__len"]; iota; zeta_full] (canonical_exact_result right (Native.canonical right));
  norm_spec [delta_only ["Nickel.EditAccepted.same_fact_contents"]; iota; zeta_full] (same_fact_contents (Alloc.Vec.impl_1__as_slice a) b);
  ordered_contents_determine_vector a b end | _ -> begin () end;
  norm_spec [delta_only ["Nickel.EditAccepted.canonical_agreement"; "Nickel.EditAccepted.canonical_result_unique"; "Nickel.EditAccepted.strict_canonical_result"]; iota; zeta_full] (canonical_agreement (Native.canonical left) (Native.canonical right))

let plan_interpretation (outcome: Result.t_Result (Option.t_Option Native.t_Replica) Native.t_Error) : Type0 =
  match outcome with | Result.Result_Ok (Option.Option_Some next) -> begin Native.interpret (Alloc.Vec.impl_1__as_slice next.f_facts) == Result.Result_Ok next.f_tree end | _ -> begin Prims.l_True end

let plan_publishes_interpretation (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (ensures plan_interpretation (Native.impl_Replica__plan before fact)) =
  assert (plan_interpretation (Native.impl_Replica__plan before fact)) by (
    Tactics.norm [delta_only ["Nickel_crdt.Edit.impl_Replica__plan"; "Nickel_crdt.Edit.impl_Replica__with_tree"; "Nickel.EditAccepted.plan_interpretation"; "Core_models.Clone.f_clone"; "Nickel_crdt.Edit.impl_26"; "Nickel_crdt.Edit.impl_82"]; iota; zeta_full; primops; unmeta; unascribe];
    Tactics.smt_sync' 1 1
  )

let added_shared_agreement (left: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) (right: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) : Type0 =
  match left with | (a, Result.Result_Ok Native.Admission_Added) -> begin match right with | (b, Result.Result_Ok Native.Admission_Added) -> begin Prims.l_and (a.f_facts == b.f_facts) (a.f_tree == b.f_tree) end | _ -> begin Prims.l_True end end | _ -> begin Prims.l_True end

let receive_added_shared_state_agrees (left: Native.t_Replica) (left_fact: Native.t_Fact) (right: Native.t_Replica) (right_fact: Native.t_Fact) : Lemma (requires same_input_contents_and_length (Alloc.Vec.impl_1__as_slice (candidate_facts left left_fact)) (Alloc.Vec.impl_1__as_slice (candidate_facts right right_fact))) (ensures added_shared_agreement (Native.impl_Replica__receive left left_fact) (Native.impl_Replica__receive right right_fact)) =
  plan_publishes_canonical_facts left left_fact;
  plan_publishes_canonical_facts right right_fact;
  plan_publishes_interpretation left left_fact;
  plan_publishes_interpretation right right_fact;
  canonical_is_permutation_independent (Alloc.Vec.impl_1__as_slice (candidate_facts left left_fact)) (Alloc.Vec.impl_1__as_slice (candidate_facts right right_fact));
  norm_spec [delta_only ["Nickel_crdt.Edit.impl_Replica__receive"; "Nickel.EditAccepted.added_shared_agreement"; "Nickel.EditAccepted.canonical_publication"; "Nickel.EditAccepted.canonical_agreement"; "Nickel.EditAccepted.plan_interpretation"]; iota; zeta_full; primops; unmeta; unascribe] (added_shared_agreement (Native.impl_Replica__receive left left_fact) (Native.impl_Replica__receive right right_fact))

let choice_total (result: Result.t_Result (Option.t_Option usize) Native.t_Error) : Type0 =
  match result with | Result.Result_Ok _ -> begin Prims.l_True end | _ -> begin Prims.l_False end

let choice_bounds (input: t_Slice Native.t_Fact) (at: nat) (choice: Option.t_Option usize) : Type0 =
  match choice with | Option.Option_None -> begin Prims.l_True end | Option.Option_Some k -> begin Prims.l_and (v k < at) (v k < Seq.length input) end

let choice_always_returns (input: t_Slice Native.t_Fact) (out: t_Slice Native.t_Fact) : Lemma (ensures choice_total (Native.choose_unseen input out)) =
  Nickel.LoopUtil.preserve_any (mk_usize 0) (Nickel.EditIdentity.length input) (choice_bounds input) (choice_bounds input (Seq.length input)) choice_total;
  norm_spec [delta_only ["Nickel_crdt.Edit.choose_unseen"; "Nickel.EditAccepted.choice_total"; "Nickel.EditAccepted.choice_bounds"; "Nickel.EditIdentity.length"; "Core_models.Slice.impl__len"; "Nickel.LoopUtil.step_safe"; "Nickel.LoopUtil.output_safe"]; iota; zeta_full; primops; unmeta; unascribe] (choice_total (Native.choose_unseen input out))

let find_id_position (input: t_Slice Native.t_Fact) (id: Native.t_EventId{Native.has_fact input id}) : i: nat{Prims.l_and (i < Seq.length input) ((Seq.index input i).f_id == id)} =
  membership_absence_exact input id;
  match FStar.Fin.find input (fun old -> old.f_id ==? id) 0 with | Some i -> begin i end | None -> begin norm_spec [delta_only ["Nickel.EditIdentity.prefix_absent"; "Nickel.EditIdentity.length"; "Core_models.Slice.impl__len"; "Rust_primitives.Slice.slice_index"]; iota; zeta_full; primops] (Nickel.EditIdentity.prefix_absent input id (mk_usize 0) (Nickel.EditIdentity.length input));
  0 end

let unique_slice_nat_positions (input: t_Slice Native.t_Fact) (i: nat{i < Seq.length input}) (j: nat{j < Seq.length input}) : Lemma (requires (Nickel.EditIdentity.unique_ids input /\ (Seq.index input i).f_id == (Seq.index input j).f_id)) (ensures i == j) =
  norm_spec [delta_only ["Nickel.EditIdentity.unique_ids"; "Nickel.EditIdentity.length"; "Core_models.Slice.impl__len"]; iota; zeta_full; primops] (Nickel.EditIdentity.unique_ids input);
  assert ((Rust_primitives.Slice.slice_index input (mk_usize i)).f_id == (Rust_primitives.Slice.slice_index input (mk_usize j)).f_id);
  assert (mk_usize i == mk_usize j)

let mapped_id_position (input: t_Slice Native.t_Fact) (out: t_Slice Native.t_Fact{Prims.l_and (Prims.l_and (Seq.length out > 0) (Seq.length out < Seq.length input)) (forall(i: nat{i < Seq.length input}). Native.has_fact out (Seq.index input i).f_id)}) (i: nat{i < Seq.length out + 1}) : FStar.Fin.under (Seq.length out) =
  find_id_position out (Seq.index input i).f_id

let shorter_output_has_unseen (input: t_Slice Native.t_Fact) (out: t_Slice Native.t_Fact) : Lemma (requires (Nickel.EditIdentity.unique_ids input /\ Seq.length out < Seq.length input)) (ensures Prims.l_not (forall(i: nat{i < Seq.length input}). Native.has_fact out (Seq.index input i).f_id)) =
  let impossible () : Lemma (requires forall(i: nat{i < Seq.length input}). Native.has_fact out (Seq.index input i).f_id) (ensures Prims.l_False) = if Seq.length out ==? 0 then
    begin membership_absence_exact out (Seq.index input 0).f_id;
    norm_spec [delta_only ["Nickel.EditIdentity.prefix_absent"; "Nickel.EditIdentity.length"; "Core_models.Slice.impl__len"]; iota; zeta_full; primops] (Nickel.EditIdentity.prefix_absent out (Seq.index input 0).f_id (mk_usize 0) (Nickel.EditIdentity.length out)) end
  else
    begin let position = mapped_id_position input out in
    let positions = Seq.init (Seq.length out + 1) position in
    Seq.lemma_init_len (Seq.length out + 1) position;
    Seq.init_index (Seq.length out + 1) position;
    match FStar.Fin.pigeonhole positions with | (i, j) -> begin assert (i < j);
    assert (position i == position j);
    unique_slice_nat_positions input i j end end in
  FStar.Classical.move_requires impossible ()

let canonical_total (result: Result.t_Result facts_vec Native.t_Error) : Type0 =
  match result with | Result.Result_Ok _ -> begin Prims.l_True end | _ -> begin Prims.l_False end

let canonical_step_succeeds (input: t_Slice Native.t_Fact) (out: facts_vec) : Lemma (requires (Nickel.EditIdentity.unique_ids input /\ Seq.length (Alloc.Vec.impl_1__as_slice out) < Seq.length input)) (ensures canonical_total (Native.canonical_step input out)) =
  choice_always_returns input (Alloc.Vec.impl_1__as_slice out);
  selected_id_is_least input (Alloc.Vec.impl_1__as_slice out);
  shorter_output_has_unseen input (Alloc.Vec.impl_1__as_slice out);
  norm_spec [delta_only ["Nickel.EditAccepted.choice_total"]; iota; zeta_full] (choice_total (Native.choose_unseen input (Alloc.Vec.impl_1__as_slice out)));
  norm_spec [delta_only ["Nickel.EditAccepted.least_result"; "Nickel.EditAccepted.least_choice"]; iota; zeta_full; primops] (least_result input (Alloc.Vec.impl_1__as_slice out) (Native.choose_unseen input (Alloc.Vec.impl_1__as_slice out)));
  match Native.choose_unseen input (Alloc.Vec.impl_1__as_slice out) with | Result.Result_Ok (Option.Option_Some k) -> begin assert (v k < Seq.length input);
  assert (canonical_total (Native.canonical_step input out)) by (
    Tactics.norm [delta_only ["Nickel_crdt.Edit.canonical_step"; "Nickel_crdt.Edit.push"; "Alloc.Vec.impl_1__len"; "Alloc.Vec.impl_1__as_slice"; "Core_models.Bundle.impl__ok_or"; "Core_models.Option.impl__ok_or"; "Nickel.EditAccepted.canonical_total"; "Nickel.EditIdentity.length"; "Core_models.Slice.impl__len"; "Rust_primitives.Sequence.seq_len"; "Rust_primitives.Sequence.seq_to_slice"]; iota; zeta_full; primops; unmeta; unascribe];
    Tactics.smt_sync' 1 1
  ) end | Result.Result_Ok Option.Option_None -> begin let all_seen (i: nat{i < Seq.length input}) : Lemma (ensures Native.has_fact (Alloc.Vec.impl_1__as_slice out) (Seq.index input i).f_id) [SMTPat (Native.has_fact (Alloc.Vec.impl_1__as_slice out) (Seq.index input i).f_id)] =
    assert (Native.has_fact (Alloc.Vec.impl_1__as_slice out) (Rust_primitives.Slice.slice_index input (mk_usize i)).f_id);
    norm_spec [delta_only ["Rust_primitives.Slice.slice_index"]; iota; zeta_full; primops] (Rust_primitives.Slice.slice_index input (mk_usize i)) in
  assert Prims.l_False end | _ -> begin () end

let progress_invariant (input: t_Slice Native.t_Fact) (at: nat) (out: facts_vec) : Type0 =
  content_invariant input at out

let canonical_succeeds_for_unique_ids (input: t_Slice Native.t_Fact) : Lemma (requires Nickel.EditIdentity.unique_ids input) (ensures canonical_total (Native.canonical input)) =
  let each_step (out: facts_vec) : Lemma (requires (Seq.length (Alloc.Vec.impl_1__as_slice out) < Seq.length input /\ selected_whole_facts input out)) (ensures Prims.l_and (canonical_total (Native.canonical_step input out)) (match Native.canonical_step input out with | Result.Result_Ok next -> begin progress_invariant input (Seq.length (Alloc.Vec.impl_1__as_slice out) + 1) next end | _ -> begin Prims.l_False end)) [SMTPat (Native.canonical_step input out)] =
    canonical_step_succeeds input out;
    canonical_step_selects_whole_facts input out (v (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice out))) in
  Nickel.LoopUtil.preserve_any (mk_usize 0) (Nickel.EditIdentity.length input) (progress_invariant input) (fun out -> Prims.l_True) (fun (result: Result.t_Result facts_vec Native.t_Error) -> Prims.l_False);
  assert (canonical_total (Native.canonical input)) by (
    Tactics.norm [delta_only ["Nickel_crdt.Edit.canonical"; "Nickel.EditAccepted.canonical_total"; "Nickel.EditAccepted.progress_invariant"; "Nickel.EditAccepted.content_step_result"; "Nickel.EditAccepted.content_invariant"; "Nickel.LoopUtil.step_safe"; "Nickel.LoopUtil.output_safe"; "Nickel.EditIdentity.length"; "Core_models.Slice.impl__len"; "Alloc.Vec.impl__new"; "Alloc.Vec.impl_1__as_slice"; "Rust_primitives.Sequence.seq_empty"; "Rust_primitives.Sequence.seq_to_slice"]; iota; zeta_full; primops; unmeta; unascribe];
    Tactics.smt_sync' 1 1
  )

let total_canonical_agreement (left: Result.t_Result facts_vec Native.t_Error) (right: Result.t_Result facts_vec Native.t_Error) : Type0 =
  match left with | Result.Result_Ok a -> begin match right with | Result.Result_Ok b -> begin a == b end | _ -> begin Prims.l_False end end | _ -> begin Prims.l_False end

let unique_inputs_canonicalize_identically (left: t_Slice Native.t_Fact) (right: t_Slice Native.t_Fact) : Lemma (requires (Nickel.EditIdentity.unique_ids left /\ Nickel.EditIdentity.unique_ids right /\ same_input_contents_and_length left right)) (ensures total_canonical_agreement (Native.canonical left) (Native.canonical right)) =
  canonical_succeeds_for_unique_ids left;
  canonical_succeeds_for_unique_ids right;
  canonical_is_permutation_independent left right;
  norm_spec [delta_only ["Nickel.EditAccepted.canonical_total"; "Nickel.EditAccepted.canonical_agreement"; "Nickel.EditAccepted.total_canonical_agreement"]; iota; zeta_full; primops] (total_canonical_agreement (Native.canonical left) (Native.canonical right))

let unicode_scalar (scalar: u32) : Type0 =
  Prims.l_and (v scalar <= 1114111) (Prims.l_or (v scalar < 55296) (v scalar > 57343))

let scalar_prefix (scalars: t_Slice u32) (finish: nat) : Type0 =
  forall(i: usize{v i < v (Core_models.Slice.impl__len scalars)}). v i < finish ==> unicode_scalar (Rust_primitives.Slice.slice_index scalars i)

let scalars_valid (scalars: t_Slice u32) : Type0 =
  scalar_prefix scalars (v (Core_models.Slice.impl__len scalars))

let scalar_check_result (scalars: t_Slice u32) (result: Result.t_Result unit Native.t_Error) : Type0 =
  match result with | Result.Result_Ok _ -> begin scalars_valid scalars end | _ -> begin Prims.l_True end

let scalar_check_invariant (scalars: t_Slice u32) (at: nat) (state: unit) : Type0 =
  scalar_prefix scalars at

let scalar_validation_is_sound (scalars: t_Slice u32) : Lemma (ensures scalar_check_result scalars (Native.validate_scalars scalars)) =
  Nickel.LoopUtil.preserve_any (mk_usize 0) (Core_models.Slice.impl__len scalars) (scalar_check_invariant scalars) (fun (_: unit) -> scalars_valid scalars) (scalar_check_result scalars);
  norm_spec [delta_only ["Nickel_crdt.Edit.validate_scalars"; "Nickel_crdt.Edit.invalid"; "Nickel.EditAccepted.scalar_check_result"; "Nickel.EditAccepted.scalar_check_invariant"; "Nickel.EditAccepted.scalars_valid"; "Nickel.EditAccepted.scalar_prefix"; "Nickel.EditAccepted.unicode_scalar"; "Nickel.LoopUtil.step_safe"; "Nickel.LoopUtil.output_safe"]; iota; zeta_full; primops; unmeta; unascribe] (scalar_check_result scalars (Native.validate_scalars scalars))

let valid_scalar_input_succeeds (scalars: t_Slice u32) : Lemma (requires scalars_valid scalars) (ensures Native.validate_scalars scalars == Result.Result_Ok ()) =
  Nickel.LoopUtil.preserve_any (mk_usize 0) (Core_models.Slice.impl__len scalars) (fun (_: nat) (_: unit) -> Prims.l_True) (fun (_: unit) -> Prims.l_True) (fun (_: Result.t_Result unit Native.t_Error) -> Prims.l_False);
  norm_spec [delta_only ["Nickel_crdt.Edit.validate_scalars"; "Nickel_crdt.Edit.invalid"; "Nickel.EditAccepted.scalars_valid"; "Nickel.EditAccepted.scalar_prefix"; "Nickel.EditAccepted.unicode_scalar"; "Nickel.LoopUtil.step_safe"; "Nickel.LoopUtil.output_safe"]; iota; zeta_full; primops; unmeta; unascribe] (Native.validate_scalars scalars)

let fact_scalars_valid (fact: Native.t_Fact) : Type0 =
  scalars_valid (Alloc.Vec.impl_1__as_slice fact.f_insert)

let validated_scalars (fact: Native.t_Fact) (result: Result.t_Result unit Native.t_Error) : Type0 =
  match result with | Result.Result_Ok _ -> begin fact_scalars_valid fact end | _ -> begin Prims.l_True end

let no_validation_success (result: Result.t_Result unit Native.t_Error) : Type0 =
  match result with | Result.Result_Err _ -> begin Prims.l_True end | _ -> begin Prims.l_False end

let successful_validation_has_valid_scalars (facts: t_Slice Native.t_Fact) (limits: Native.t_Limits) (fact: Native.t_Fact) : Lemma (ensures validated_scalars fact (Native.impl_Replica__validate_new facts limits fact)) =
  Nickel.LoopUtil.preserve_any (mk_usize 0) (Nickel.EditIdentity.length facts) (fun (_: nat) (_: unit) -> Prims.l_True) (fun (_: unit) -> Prims.l_True) no_validation_success;
  Nickel.LoopUtil.preserve_any (mk_usize 0) (Nickel.EditIdentity.length facts) (fun (_: nat) (_: usize) -> Prims.l_True) (fun (_: usize) -> Prims.l_True) no_validation_success;
  scalar_validation_is_sound (Alloc.Vec.impl_1__as_slice fact.f_insert);
  norm_spec [delta_only ["Nickel.EditAccepted.scalar_check_result"]; iota; zeta_full] (scalar_check_result (Alloc.Vec.impl_1__as_slice fact.f_insert) (Native.validate_scalars (Alloc.Vec.impl_1__as_slice fact.f_insert)));
  assert (validated_scalars fact (Native.impl_Replica__validate_new facts limits fact)) by (
    Tactics.norm [delta_only ["Nickel_crdt.Edit.impl_Replica__validate_new"; "Nickel.EditAccepted.validated_scalars"; "Nickel.EditAccepted.fact_scalars_valid"; "Nickel.EditAccepted.scalar_check_result"; "Nickel.EditAccepted.no_validation_success"; "Nickel.LoopUtil.step_safe"; "Nickel.LoopUtil.output_safe"; "Nickel.EditIdentity.length"; "Core_models.Slice.impl__len"]; iota; zeta_full; primops; unmeta; unascribe];
    Tactics.smt_sync' 1 1
  )

let added_scalars (fact: Native.t_Fact) (outcome: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) : Type0 =
  match outcome with | (_, Result.Result_Ok Native.Admission_Added) -> begin fact_scalars_valid fact end | _ -> begin Prims.l_True end

let receive_added_fact_has_valid_scalars (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (ensures added_scalars fact (Native.impl_Replica__receive before fact)) =
  successful_validation_has_valid_scalars (Alloc.Vec.impl_1__as_slice before.f_facts) before.f_limits fact;
  norm_spec [delta_only ["Nickel.EditAccepted.validated_scalars"]; iota; zeta_full] (validated_scalars fact (Native.impl_Replica__validate_new (Alloc.Vec.impl_1__as_slice before.f_facts) before.f_limits fact));
  assert (added_scalars fact (Native.impl_Replica__receive before fact)) by (
    Tactics.norm [delta_only ["Nickel_crdt.Edit.impl_Replica__receive"; "Nickel_crdt.Edit.impl_Replica__plan"; "Nickel.EditAccepted.added_scalars"; "Nickel.EditAccepted.validated_scalars"]; iota; zeta_full; primops; unmeta; unascribe];
    Tactics.smt_sync' 1 1
  )

let facts_scalars_valid (facts: facts_vec) : Type0 =
  forall(fact: Native.t_Fact). fact_present (Alloc.Vec.impl_1__as_slice facts) fact ==> fact_scalars_valid fact

let receive_scalars_preserved (outcome: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) : Type0 =
  match outcome with | (next, _) -> begin facts_scalars_valid next.f_facts end

let receive_preserves_scalar_validity (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (requires facts_scalars_valid before.f_facts) (ensures receive_scalars_preserved (Native.impl_Replica__receive before fact)) =
  Nickel.EditAtomic.receive_rejection_unchanged before fact;
  receive_added_has_exact_contents before fact;
  receive_added_fact_has_valid_scalars before fact;
  norm_spec [delta_only ["Nickel.EditAccepted.receive_scalars_preserved"; "Nickel.EditAccepted.facts_scalars_valid"; "Nickel.EditAccepted.added_exact_contents"; "Nickel.EditAccepted.appended_contents"; "Nickel.EditAccepted.added_scalars"; "Nickel.EditAtomic.receive_neutral"]; iota; zeta_full; primops] (receive_scalars_preserved (Native.impl_Replica__receive before fact))

let authored_scalars (outcome: Native.t_Replica & Result.t_Result Native.t_Local Native.t_Error) : Type0 =
  match outcome with | (_, Result.Result_Ok (Native.Local_Authored fact)) -> begin fact_scalars_valid fact end | _ -> begin Prims.l_True end

let edit_authors_only_valid_scalars (before: Native.t_Replica) (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (delete: Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global) : Lemma (ensures authored_scalars (Native.impl_Replica__edit before gap insert delete)) =
  Nickel.EditCommit.authored_fact_replays_same_commit before gap insert delete;
  match Native.impl_Replica__edit before gap insert delete with | (_, Result.Result_Ok (Native.Local_Authored fact)) -> begin receive_added_fact_has_valid_scalars before fact end | _ -> begin () end;
  norm_spec [delta_only ["Nickel.EditAccepted.authored_scalars"; "Nickel.EditAccepted.added_scalars"; "Nickel.EditCommit.same_commit"]; iota; zeta_full; primops] (authored_scalars (Native.impl_Replica__edit before gap insert delete))

let edit_scalars_preserved (outcome: Native.t_Replica & Result.t_Result Native.t_Local Native.t_Error) : Type0 =
  match outcome with | (next, _) -> begin facts_scalars_valid next.f_facts end

let edit_preserves_scalar_validity (before: Native.t_Replica) (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (delete: Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global) : Lemma (requires facts_scalars_valid before.f_facts) (ensures edit_scalars_preserved (Native.impl_Replica__edit before gap insert delete)) =
  Nickel.EditAtomic.edit_rejection_or_empty_unchanged before gap insert delete;
  edit_authored_has_exact_contents before gap insert delete;
  edit_authors_only_valid_scalars before gap insert delete;
  norm_spec [delta_only ["Nickel.EditAccepted.edit_scalars_preserved"; "Nickel.EditAccepted.facts_scalars_valid"; "Nickel.EditAccepted.authored_exact_contents"; "Nickel.EditAccepted.appended_contents"; "Nickel.EditAccepted.authored_scalars"; "Nickel.EditAtomic.edit_neutral"]; iota; zeta_full; primops] (edit_scalars_preserved (Native.impl_Replica__edit before gap insert delete))

let new_scalars_valid (outcome: Result.t_Result Native.t_Replica Native.t_Error) : Type0 =
  match outcome with | Result.Result_Ok state -> begin facts_scalars_valid state.f_facts end | _ -> begin Prims.l_True end

let new_establishes_scalar_validity (writer: Option.t_Option Native.t_Writer) (limits: Native.t_Limits) : Lemma (ensures new_scalars_valid (Native.impl_Replica__new writer limits)) =
  norm_spec [delta_only ["Nickel_crdt.Edit.impl_Replica__new"; "Nickel.EditAccepted.new_scalars_valid"; "Nickel.EditAccepted.facts_scalars_valid"; "Nickel.EditAccepted.fact_present"; "Alloc.Vec.impl__new"; "Alloc.Vec.impl_1__as_slice"; "Rust_primitives.Sequence.seq_empty"; "Rust_primitives.Sequence.seq_to_slice"]; iota; zeta_full; primops] (new_scalars_valid (Native.impl_Replica__new writer limits))

let event_present (facts: t_Slice Native.t_Fact) (id: Native.t_EventId) : Type0 =
  Prims.l_not (Nickel.EditIdentity.prefix_absent facts id (mk_usize 0) (Nickel.EditIdentity.length facts))

let event_membership_is_presence (facts: t_Slice Native.t_Fact) (id: Native.t_EventId) : Lemma (ensures Native.has_fact facts id == true <==> event_present facts id) =
  membership_absence_exact facts id;
  norm_spec [delta_only ["Nickel.EditAccepted.event_present"]; iota] (event_present facts id)

let dependency_prefix (facts: t_Slice Native.t_Fact) (after: t_Slice Native.t_EventId) (finish: nat) : Type0 =
  forall(i: usize{v i < v (Core_models.Slice.impl__len after)}). v i < finish ==> event_present facts (Rust_primitives.Slice.slice_index after i)

let dependencies_present (facts: t_Slice Native.t_Fact) (after: t_Slice Native.t_EventId) : Type0 =
  dependency_prefix facts after (v (Core_models.Slice.impl__len after))

let dependency_check_result (facts: t_Slice Native.t_Fact) (after: t_Slice Native.t_EventId) (result: Result.t_Result unit Native.t_Error) : Type0 =
  match result with | Result.Result_Ok _ -> begin dependencies_present facts after end | _ -> begin Prims.l_True end

let dependency_check_invariant (facts: t_Slice Native.t_Fact) (after: t_Slice Native.t_EventId) (at: nat) (state: unit) : Type0 =
  dependency_prefix facts after at

let dependency_validation_is_sound (facts: t_Slice Native.t_Fact) (after: t_Slice Native.t_EventId) : Lemma (ensures dependency_check_result facts after (Native.validate_after facts after)) =
  let each_member (id: Native.t_EventId) : Lemma (ensures Native.has_fact facts id == true <==> event_present facts id) [SMTPat (Native.has_fact facts id)] = event_membership_is_presence facts id in
  Nickel.LoopUtil.preserve_any (mk_usize 0) (Core_models.Slice.impl__len after) (dependency_check_invariant facts after) (fun (_: unit) -> dependencies_present facts after) (dependency_check_result facts after);
  norm_spec [delta_only ["Nickel_crdt.Edit.validate_after"; "Nickel.EditAccepted.dependency_check_result"; "Nickel.EditAccepted.dependencies_present"; "Nickel.EditAccepted.dependency_prefix"; "Nickel.EditAccepted.dependency_check_invariant"; "Nickel.LoopUtil.step_safe"; "Nickel.LoopUtil.output_safe"]; iota; zeta_full; primops; unmeta; unascribe] (dependency_check_result facts after (Native.validate_after facts after))

let present_dependencies_pass_guard (facts: t_Slice Native.t_Fact) (after: t_Slice Native.t_EventId) : Lemma (requires dependencies_present facts after) (ensures Native.validate_after facts after == Result.Result_Ok ()) =
  let each_member (id: Native.t_EventId) : Lemma (ensures Native.has_fact facts id == true <==> event_present facts id) [SMTPat (Native.has_fact facts id)] = event_membership_is_presence facts id in
  Nickel.LoopUtil.preserve_any (mk_usize 0) (Core_models.Slice.impl__len after) (fun (_: nat) (_: unit) -> Prims.l_True) (fun (_: unit) -> Prims.l_True) (fun (_: Result.t_Result unit Native.t_Error) -> Prims.l_False);
  norm_spec [delta_only ["Nickel_crdt.Edit.validate_after"; "Nickel.EditAccepted.dependencies_present"; "Nickel.EditAccepted.dependency_prefix"; "Nickel.LoopUtil.step_safe"; "Nickel.LoopUtil.output_safe"]; iota; zeta_full; primops; unmeta; unascribe] (Native.validate_after facts after)

let past_has_dependencies (facts: t_Slice Native.t_Fact) (after: t_Slice Native.t_EventId) (result: Result.t_Result (Alloc.Vec.t_Vec Native.t_EventId Alloc.Alloc.t_Global) Native.t_Error) : Type0 =
  match result with | Result.Result_Ok _ -> begin dependencies_present facts after end | _ -> begin Prims.l_True end

let successful_past_has_direct_dependencies (facts: t_Slice Native.t_Fact) (after: t_Slice Native.t_EventId) : Lemma (ensures past_has_dependencies facts after (Native.past facts after)) =
  dependency_validation_is_sound facts after;
  norm_spec [delta_only ["Nickel_crdt.Edit.past"; "Nickel.EditAccepted.past_has_dependencies"; "Nickel.EditAccepted.dependency_check_result"]; iota; zeta_full; primops; unmeta; unascribe] (past_has_dependencies facts after (Native.past facts after))

let fact_dependencies_present (facts: t_Slice Native.t_Fact) (fact: Native.t_Fact) : Type0 =
  dependencies_present facts (Alloc.Vec.impl_1__as_slice fact.f_after)

let validation_has_dependencies (facts: t_Slice Native.t_Fact) (fact: Native.t_Fact) (result: Result.t_Result unit Native.t_Error) : Type0 =
  match result with | Result.Result_Ok _ -> begin fact_dependencies_present facts fact end | _ -> begin Prims.l_True end

let successful_validation_has_direct_dependencies (facts: t_Slice Native.t_Fact) (limits: Native.t_Limits) (fact: Native.t_Fact) : Lemma (ensures validation_has_dependencies facts fact (Native.impl_Replica__validate_new facts limits fact)) =
  successful_past_has_direct_dependencies facts (Alloc.Vec.impl_1__as_slice fact.f_after);
  assert (validation_has_dependencies facts fact (Native.impl_Replica__validate_new facts limits fact)) by (
    Tactics.norm [delta_only ["Nickel_crdt.Edit.impl_Replica__validate_new"; "Nickel.EditAccepted.validation_has_dependencies"; "Nickel.EditAccepted.fact_dependencies_present"; "Nickel.EditAccepted.past_has_dependencies"]; iota; zeta_full; primops; unmeta; unascribe];
    Tactics.smt_sync' 1 1
  )

let added_dependencies (before: Native.t_Replica) (fact: Native.t_Fact) (outcome: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) : Type0 =
  match outcome with | (_, Result.Result_Ok Native.Admission_Added) -> begin fact_dependencies_present (Alloc.Vec.impl_1__as_slice before.f_facts) fact end | _ -> begin Prims.l_True end

let receive_added_has_direct_dependencies (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (ensures added_dependencies before fact (Native.impl_Replica__receive before fact)) =
  successful_validation_has_direct_dependencies (Alloc.Vec.impl_1__as_slice before.f_facts) before.f_limits fact;
  assert (added_dependencies before fact (Native.impl_Replica__receive before fact)) by (
    Tactics.norm [delta_only ["Nickel_crdt.Edit.impl_Replica__receive"; "Nickel_crdt.Edit.impl_Replica__plan"; "Nickel.EditAccepted.added_dependencies"; "Nickel.EditAccepted.validation_has_dependencies"]; iota; zeta_full; primops; unmeta; unascribe];
    Tactics.smt_sync' 1 1
  )

let facts_contained (before: t_Slice Native.t_Fact) (next: t_Slice Native.t_Fact) : Type0 =
  forall(fact: Native.t_Fact). fact_present before fact ==> fact_present next fact

let absence_on_whole_facts (facts: t_Slice Native.t_Fact) (id: Native.t_EventId) : Lemma (ensures Nickel.EditIdentity.prefix_absent facts id (mk_usize 0) (Nickel.EditIdentity.length facts) <==> forall(fact: Native.t_Fact). fact_present facts fact ==> Prims.l_not (fact.f_id == id)) =
  membership_absence_exact facts id;
  let forward (fact: Native.t_Fact) : Lemma (requires (Nickel.EditIdentity.prefix_absent facts id (mk_usize 0) (Nickel.EditIdentity.length facts) /\ fact_present facts fact)) (ensures Prims.l_not (fact.f_id == id)) =
    let i = find_fact_position facts fact in
    norm_spec [delta_only ["Rust_primitives.Slice.slice_index"]; iota; zeta_full; primops] (Rust_primitives.Slice.slice_index facts (mk_usize i));
    norm_spec [delta_only ["Nickel.EditIdentity.prefix_absent"]; iota; zeta_full] (Nickel.EditIdentity.prefix_absent facts id (mk_usize 0) (Nickel.EditIdentity.length facts)) in
  let reverse (dummy: unit) : Lemma (requires forall(fact: Native.t_Fact). fact_present facts fact ==> Prims.l_not (fact.f_id == id)) (ensures Nickel.EditIdentity.prefix_absent facts id (mk_usize 0) (Nickel.EditIdentity.length facts)) = if Native.has_fact facts id then
    begin let i = find_id_position facts id in
    assert (fact_present facts (Seq.index facts i));
    assert Prims.l_False end
  else
    begin () end in
  let all_forward (fact: Native.t_Fact) : Lemma (ensures Prims.l_and (Nickel.EditIdentity.prefix_absent facts id (mk_usize 0) (Nickel.EditIdentity.length facts)) (fact_present facts fact) ==> Prims.l_not (fact.f_id == id)) = FStar.Classical.move_requires forward fact in
  FStar.Classical.forall_intro all_forward;
  FStar.Classical.move_requires reverse ()

let presence_survives_containment (before: t_Slice Native.t_Fact) (next: t_Slice Native.t_Fact) (id: Native.t_EventId) : Lemma (requires (facts_contained before next /\ event_present before id)) (ensures event_present next id) =
  event_membership_is_presence before id;
  let i = find_id_position before id in
  assert (fact_present before (Seq.index before i));
  norm_spec [delta_only ["Nickel.EditAccepted.facts_contained"]; iota] (facts_contained before next);
  assert (fact_present next (Seq.index before i));
  let j = find_fact_position next (Seq.index before i) in
  membership_absence_exact next id;
  if not (Native.has_fact next id) then
    begin norm_spec [delta_only ["Rust_primitives.Slice.slice_index"]; iota; zeta_full; primops] (Rust_primitives.Slice.slice_index next (mk_usize j));
    norm_spec [delta_only ["Nickel.EditIdentity.prefix_absent"]; iota; zeta_full] (Nickel.EditIdentity.prefix_absent next id (mk_usize 0) (Nickel.EditIdentity.length next));
    assert Prims.l_False end
  else
    begin () end;
  event_membership_is_presence next id

let dependencies_survive_containment (before: t_Slice Native.t_Fact) (next: t_Slice Native.t_Fact) (fact: Native.t_Fact) : Lemma (requires (facts_contained before next /\ fact_dependencies_present before fact)) (ensures fact_dependencies_present next fact) =
  let each_id (id: Native.t_EventId) : Lemma (requires event_present before id) (ensures event_present next id) = presence_survives_containment before next id in
  let all_id (id: Native.t_EventId) : Lemma (ensures event_present before id ==> event_present next id) = FStar.Classical.move_requires each_id id in
  FStar.Classical.forall_intro all_id;
  norm_spec [delta_only ["Nickel.EditAccepted.fact_dependencies_present"; "Nickel.EditAccepted.dependencies_present"; "Nickel.EditAccepted.dependency_prefix"]; iota] (fact_dependencies_present next fact)

let facts_causally_closed (facts: facts_vec) : Type0 =
  forall(fact: Native.t_Fact). fact_present (Alloc.Vec.impl_1__as_slice facts) fact ==> fact_dependencies_present (Alloc.Vec.impl_1__as_slice facts) fact

let exact_extension_preserves_causal_closure (before: facts_vec) (fact: Native.t_Fact) (next: facts_vec) : Lemma (requires (facts_causally_closed before /\ fact_dependencies_present (Alloc.Vec.impl_1__as_slice before) fact /\ appended_contents before fact next)) (ensures facts_causally_closed next) =
  assert (facts_contained (Alloc.Vec.impl_1__as_slice before) (Alloc.Vec.impl_1__as_slice next));
  let each_fact (item: Native.t_Fact) : Lemma (requires fact_present (Alloc.Vec.impl_1__as_slice next) item) (ensures fact_dependencies_present (Alloc.Vec.impl_1__as_slice next) item) =
    assert (fact_dependencies_present (Alloc.Vec.impl_1__as_slice before) item);
    dependencies_survive_containment (Alloc.Vec.impl_1__as_slice before) (Alloc.Vec.impl_1__as_slice next) item in
  let all_fact (item: Native.t_Fact) : Lemma (ensures fact_present (Alloc.Vec.impl_1__as_slice next) item ==> fact_dependencies_present (Alloc.Vec.impl_1__as_slice next) item) = FStar.Classical.move_requires each_fact item in
  FStar.Classical.forall_intro all_fact;
  norm_spec [delta_only ["Nickel.EditAccepted.facts_causally_closed"]; iota] (facts_causally_closed next)

let receive_causally_closed (outcome: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) : Type0 =
  match outcome with | (next, _) -> begin facts_causally_closed next.f_facts end

let receive_preserves_causal_closure (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (requires facts_causally_closed before.f_facts) (ensures receive_causally_closed (Native.impl_Replica__receive before fact)) =
  Nickel.EditAtomic.receive_rejection_unchanged before fact;
  receive_added_has_exact_contents before fact;
  receive_added_has_direct_dependencies before fact;
  match Native.impl_Replica__receive before fact with | (next, Result.Result_Ok Native.Admission_Added) -> begin exact_extension_preserves_causal_closure before.f_facts fact next.f_facts end | _ -> begin () end;
  norm_spec [delta_only ["Nickel.EditAccepted.receive_causally_closed"; "Nickel.EditAtomic.receive_neutral"]; iota; zeta_full] (receive_causally_closed (Native.impl_Replica__receive before fact))

let edit_causally_closed (outcome: Native.t_Replica & Result.t_Result Native.t_Local Native.t_Error) : Type0 =
  match outcome with | (next, _) -> begin facts_causally_closed next.f_facts end

let edit_preserves_causal_closure (before: Native.t_Replica) (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (delete: Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global) : Lemma (requires facts_causally_closed before.f_facts) (ensures edit_causally_closed (Native.impl_Replica__edit before gap insert delete)) =
  Nickel.EditAtomic.edit_rejection_or_empty_unchanged before gap insert delete;
  edit_authored_has_exact_contents before gap insert delete;
  Nickel.EditCommit.authored_fact_replays_same_commit before gap insert delete;
  match Native.impl_Replica__edit before gap insert delete with | (next, Result.Result_Ok (Native.Local_Authored fact)) -> begin receive_added_has_direct_dependencies before fact;
  exact_extension_preserves_causal_closure before.f_facts fact next.f_facts end | _ -> begin () end;
  norm_spec [delta_only ["Nickel.EditAccepted.edit_causally_closed"; "Nickel.EditAtomic.edit_neutral"]; iota; zeta_full] (edit_causally_closed (Native.impl_Replica__edit before gap insert delete))

let new_causally_closed (outcome: Result.t_Result Native.t_Replica Native.t_Error) : Type0 =
  match outcome with | Result.Result_Ok state -> begin facts_causally_closed state.f_facts end | _ -> begin Prims.l_True end

let new_establishes_causal_closure (writer: Option.t_Option Native.t_Writer) (limits: Native.t_Limits) : Lemma (ensures new_causally_closed (Native.impl_Replica__new writer limits)) =
  norm_spec [delta_only ["Nickel_crdt.Edit.impl_Replica__new"; "Nickel.EditAccepted.new_causally_closed"; "Nickel.EditAccepted.facts_causally_closed"; "Nickel.EditAccepted.fact_present"; "Alloc.Vec.impl__new"; "Alloc.Vec.impl_1__as_slice"; "Rust_primitives.Sequence.seq_empty"; "Rust_primitives.Sequence.seq_to_slice"]; iota; zeta_full; primops] (new_causally_closed (Native.impl_Replica__new writer limits))