(* Latte generated F* view *)
module Nickel.EditCausal

open Nickel.Prelude

open Rust_primitives

open Core_models

open FStar.Pervasives

open FStar.NormSteps

open Nickel.EditWellFormed

open Nickel.EditAccepted

module Native = Nickel_crdt.Edit

module Result = Core_models.Result

module Option = Core_models.Option

module Seq = FStar.Seq

open FStar.Classical

let fact_descends (rank: Native.t_EventId -> nat) (fact: Native.t_Fact) : Type0 =
  forall(i: usize{v i < v (Core_models.Slice.impl__len (Alloc.Vec.impl_1__as_slice fact.f_after))}). rank (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice fact.f_after) i) < rank fact.f_id

let causal_rank (facts: facts_vec) (rank: Native.t_EventId -> nat) (bound: nat) : Type0 =
  Prims.l_and (facts_causally_closed facts) (forall(fact: Native.t_Fact). fact_present (Alloc.Vec.impl_1__as_slice facts) fact ==> Prims.l_and (rank fact.f_id < bound) (fact_descends rank fact))

let extend_rank (rank: Native.t_EventId -> nat) (bound: nat) (fresh: Native.t_EventId) : Native.t_EventId -> nat =
  fun (id: Native.t_EventId) -> if id ==? fresh then
    begin bound end
  else
    begin rank id end

let present_fact_has_id (facts: t_Slice Native.t_Fact) (fact: Native.t_Fact) : Lemma (requires fact_present facts fact) (ensures event_present facts fact.f_id) =
  absence_on_whole_facts facts fact.f_id;
  norm_spec [delta_only ["Nickel.EditWellFormed.event_present"]; iota] (event_present facts fact.f_id)

let present_id_rank_bound (facts: facts_vec) (rank: Native.t_EventId -> nat) (bound: nat) (id: Native.t_EventId) : Lemma (requires (causal_rank facts rank bound /\ event_present (Alloc.Vec.impl_1__as_slice facts) id)) (ensures rank id < bound) =
  event_membership_is_presence (Alloc.Vec.impl_1__as_slice facts) id;
  let i = find_id_position (Alloc.Vec.impl_1__as_slice facts) id in
  assert (fact_present (Alloc.Vec.impl_1__as_slice facts) (Seq.index (Alloc.Vec.impl_1__as_slice facts) i));
  norm_spec [delta_only ["Nickel.EditCausal.causal_rank"]; iota] (causal_rank facts rank bound)

let old_rank_unchanged (facts: facts_vec) (rank: Native.t_EventId -> nat) (bound: nat) (fresh: Native.t_EventId) (id: Native.t_EventId) : Lemma (requires (Nickel.EditIdentity.prefix_absent (Alloc.Vec.impl_1__as_slice facts) fresh (mk_usize 0) (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice facts)) /\ event_present (Alloc.Vec.impl_1__as_slice facts) id)) (ensures (extend_rank rank bound fresh) id == rank id) =
  absence_on_whole_facts (Alloc.Vec.impl_1__as_slice facts) fresh;
  event_membership_is_presence (Alloc.Vec.impl_1__as_slice facts) id;
  let i = find_id_position (Alloc.Vec.impl_1__as_slice facts) id in
  assert (fact_present (Alloc.Vec.impl_1__as_slice facts) (Seq.index (Alloc.Vec.impl_1__as_slice facts) i));
  norm_spec [delta_only ["Nickel.EditCausal.extend_rank"]; iota; zeta_full] ((extend_rank rank bound fresh) id)

let exact_extension_extends_rank (before: facts_vec) (fact: Native.t_Fact) (next: facts_vec) (rank: Native.t_EventId -> nat) (bound: nat) : Lemma (requires (causal_rank before rank bound /\ fact_dependencies_present (Alloc.Vec.impl_1__as_slice before) fact /\ Nickel.EditIdentity.prefix_absent (Alloc.Vec.impl_1__as_slice before) fact.f_id (mk_usize 0) (Nickel.EditIdentity.length (Alloc.Vec.impl_1__as_slice before)) /\ appended_contents before fact next)) (ensures causal_rank next (extend_rank rank bound fact.f_id) (bound + 1)) =
  exact_extension_preserves_causal_closure before fact next;
  let each_fact (item: Native.t_Fact) : Lemma (requires fact_present (Alloc.Vec.impl_1__as_slice next) item) (ensures Prims.l_and ((extend_rank rank bound fact.f_id) item.f_id < bound + 1) (fact_descends (extend_rank rank bound fact.f_id) item)) = if item ==? fact then
    begin let each_dependency (i: usize{v i < v (Core_models.Slice.impl__len (Alloc.Vec.impl_1__as_slice fact.f_after))}) : Lemma (ensures (extend_rank rank bound fact.f_id) (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice fact.f_after) i) < bound) =
      let id = Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice fact.f_after) i in
      assert (event_present (Alloc.Vec.impl_1__as_slice before) id);
      present_id_rank_bound before rank bound id;
      old_rank_unchanged before rank bound fact.f_id id in
    FStar.Classical.forall_intro each_dependency;
    norm_spec [delta_only ["Nickel.EditCausal.fact_descends"; "Nickel.EditCausal.extend_rank"]; iota; zeta_full] (fact_descends (extend_rank rank bound fact.f_id) item) end
  else
    begin assert (fact_present (Alloc.Vec.impl_1__as_slice before) item);
    present_fact_has_id (Alloc.Vec.impl_1__as_slice before) item;
    old_rank_unchanged before rank bound fact.f_id item.f_id;
    let each_dependency (i: usize{v i < v (Core_models.Slice.impl__len (Alloc.Vec.impl_1__as_slice item.f_after))}) : Lemma (ensures (extend_rank rank bound fact.f_id) (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice item.f_after) i) < (extend_rank rank bound fact.f_id) item.f_id) =
      let id = Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice item.f_after) i in
      assert (event_present (Alloc.Vec.impl_1__as_slice before) id);
      old_rank_unchanged before rank bound fact.f_id id in
    FStar.Classical.forall_intro each_dependency;
    norm_spec [delta_only ["Nickel.EditCausal.fact_descends"]; iota] (fact_descends (extend_rank rank bound fact.f_id) item) end in
  let all_fact (item: Native.t_Fact) : Lemma (ensures fact_present (Alloc.Vec.impl_1__as_slice next) item ==> Prims.l_and ((extend_rank rank bound fact.f_id) item.f_id < bound + 1) (fact_descends (extend_rank rank bound fact.f_id) item)) = FStar.Classical.move_requires each_fact item in
  FStar.Classical.forall_intro all_fact;
  norm_spec [delta_only ["Nickel.EditCausal.causal_rank"]; iota] (causal_rank next (extend_rank rank bound fact.f_id) (bound + 1))

let receive_ranked (rank: Native.t_EventId -> nat) (bound: nat) (fact: Native.t_Fact) (outcome: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) : Type0 =
  match outcome with | (next, Result.Result_Ok Native.Admission_Added) -> begin causal_rank next.f_facts (extend_rank rank bound fact.f_id) (bound + 1) end | (next, _) -> begin causal_rank next.f_facts rank bound end

let receive_preserves_causal_rank (before: Native.t_Replica) (fact: Native.t_Fact) (rank: Native.t_EventId -> nat) (bound: nat) : Lemma (requires causal_rank before.f_facts rank bound) (ensures receive_ranked rank bound fact (Native.impl_Replica__receive before fact)) =
  Nickel.EditAtomic.receive_rejection_unchanged before fact;
  receive_added_has_exact_contents before fact;
  receive_added_has_direct_dependencies before fact;
  Nickel.EditIdentity.receive_added_has_fresh_event_id before fact;
  match Native.impl_Replica__receive before fact with | (next, Result.Result_Ok Native.Admission_Added) -> begin exact_extension_extends_rank before.f_facts fact next.f_facts rank bound end | _ -> begin () end;
  norm_spec [delta_only ["Nickel.EditCausal.receive_ranked"; "Nickel.EditAtomic.receive_neutral"]; iota; zeta_full] (receive_ranked rank bound fact (Native.impl_Replica__receive before fact))

let edit_ranked (rank: Native.t_EventId -> nat) (bound: nat) (outcome: Native.t_Replica & Result.t_Result Native.t_Local Native.t_Error) : Type0 =
  match outcome with | (next, Result.Result_Ok (Native.Local_Authored fact)) -> begin causal_rank next.f_facts (extend_rank rank bound fact.f_id) (bound + 1) end | (next, _) -> begin causal_rank next.f_facts rank bound end

let edit_preserves_causal_rank (before: Native.t_Replica) (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (delete: Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global) (rank: Native.t_EventId -> nat) (bound: nat) : Lemma (requires causal_rank before.f_facts rank bound) (ensures edit_ranked rank bound (Native.impl_Replica__edit before gap insert delete)) =
  Nickel.EditAtomic.edit_rejection_or_empty_unchanged before gap insert delete;
  edit_authored_has_exact_contents before gap insert delete;
  Nickel.EditCommit.authored_fact_replays_same_commit before gap insert delete;
  Nickel.EditIdentity.authored_event_id_is_fresh before gap insert delete;
  match Native.impl_Replica__edit before gap insert delete with | (next, Result.Result_Ok (Native.Local_Authored fact)) -> begin receive_added_has_direct_dependencies before fact;
  exact_extension_extends_rank before.f_facts fact next.f_facts rank bound end | _ -> begin () end;
  norm_spec [delta_only ["Nickel.EditCausal.edit_ranked"; "Nickel.EditAtomic.edit_neutral"]; iota; zeta_full] (edit_ranked rank bound (Native.impl_Replica__edit before gap insert delete))

let new_ranked (outcome: Result.t_Result Native.t_Replica Native.t_Error) : Type0 =
  match outcome with | Result.Result_Ok state -> begin causal_rank state.f_facts (fun (_: Native.t_EventId) -> 0) 0 end | _ -> begin Prims.l_True end

let new_establishes_causal_rank (writer: Option.t_Option Native.t_Writer) (limits: Native.t_Limits) : Lemma (ensures new_ranked (Native.impl_Replica__new writer limits)) =
  new_establishes_causal_closure writer limits;
  norm_spec [delta_only ["Nickel.EditCausal.new_ranked"; "Nickel.EditCausal.causal_rank"; "Nickel_crdt.Edit.impl_Replica__new"; "Nickel.EditAccepted.fact_present"; "Alloc.Vec.impl_1__as_slice"; "Alloc.Vec.impl__new"; "Rust_primitives.Sequence.seq_empty"; "Rust_primitives.Sequence.seq_to_slice"; "Core_models.Slice.impl__len"; "Nickel.EditIdentity.length"]; iota; zeta_full; primops] (new_ranked (Native.impl_Replica__new writer limits))

let causal_edge (facts: facts_vec) (newer: Native.t_EventId) (older: Native.t_EventId) : Type0 =
  exists(fact: Native.t_Fact). Prims.l_and (Prims.l_and (fact_present (Alloc.Vec.impl_1__as_slice facts) fact) (fact.f_id == newer)) (exists(i: usize). Prims.l_and (v i < v (Core_models.Slice.impl__len (Alloc.Vec.impl_1__as_slice fact.f_after))) (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice fact.f_after) i == older))

let causal_edge_descends (facts: facts_vec) (rank: Native.t_EventId -> nat) (bound: nat) (newer: Native.t_EventId) (older: Native.t_EventId) : Lemma (requires (causal_rank facts rank bound /\ causal_edge facts newer older)) (ensures rank older < rank newer) =
  norm_spec [delta_only ["Nickel.EditCausal.causal_rank"; "Nickel.EditCausal.causal_edge"; "Nickel.EditCausal.fact_descends"]; iota; zeta_full] (causal_edge facts newer older)

let rec causal_path (facts: facts_vec) (start: Native.t_EventId) (steps: Prims.list Native.t_EventId) (finish: Native.t_EventId) : Tot Type0 (decreases steps) =
  match steps with | Prims.Nil -> begin start == finish end | Prims.Cons next rest -> begin Prims.l_and (causal_edge facts start next) (causal_path facts next rest finish) end

let rec causal_path_descends (facts: facts_vec) (rank: Native.t_EventId -> nat) (bound: nat) (start: Native.t_EventId) (steps: Prims.list Native.t_EventId) (finish: Native.t_EventId) : Lemma (requires (causal_rank facts rank bound /\ causal_path facts start steps finish)) (ensures Prims.l_and (rank finish <= rank start) (Prims.l_not (steps == Prims.Nil) ==> rank finish < rank start)) (decreases steps) =
  norm_spec [delta_once ["Nickel.EditCausal.causal_path"]; iota; zeta_full] (causal_path facts start steps finish);
  match steps with | Prims.Nil -> begin () end | Prims.Cons next rest -> begin causal_edge_descends facts rank bound start next;
  causal_path_descends facts rank bound next rest finish end

let rank_excludes_nonempty_cycles (facts: facts_vec) (rank: Native.t_EventId -> nat) (bound: nat) (start: Native.t_EventId) (steps: Prims.list Native.t_EventId) : Lemma (requires (causal_rank facts rank bound /\ causal_path facts start steps start)) (ensures steps == Prims.Nil) =
  causal_path_descends facts rank bound start steps start

let clone_preserves_causal_rank (before: Native.t_Replica) (rank: Native.t_EventId -> nat) (bound: nat) : Lemma (requires causal_rank before.f_facts rank bound) (ensures causal_rank (Native.impl_82.f_clone before).f_facts rank bound) =
  norm_spec [delta_only ["Nickel_crdt.Edit.impl_82"]; iota; zeta_full] (Native.impl_82.f_clone before)

let actual_reference_is_edge (facts: facts_vec) (fact: Native.t_Fact) (i: usize{v i < v (Core_models.Slice.impl__len (Alloc.Vec.impl_1__as_slice fact.f_after))}) : Lemma (requires fact_present (Alloc.Vec.impl_1__as_slice facts) fact) (ensures causal_edge facts fact.f_id (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice fact.f_after) i)) =
  norm_spec [delta_only ["Nickel.EditCausal.causal_edge"]; iota] (causal_edge facts fact.f_id (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice fact.f_after) i))

let self_reference_has_no_rank (facts: facts_vec) (fact: Native.t_Fact) (i: usize{v i < v (Core_models.Slice.impl__len (Alloc.Vec.impl_1__as_slice fact.f_after))}) (rank: Native.t_EventId -> nat) (bound: nat) : Lemma (requires (fact_present (Alloc.Vec.impl_1__as_slice facts) fact /\ Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice fact.f_after) i == fact.f_id)) (ensures Prims.l_not (causal_rank facts rank bound)) =
  let impossible (dummy: unit) : Lemma (requires causal_rank facts rank bound) (ensures Prims.l_False) =
    actual_reference_is_edge facts fact i;
    causal_edge_descends facts rank bound fact.f_id fact.f_id;
    assert Prims.l_False in
  FStar.Classical.move_requires impossible ()