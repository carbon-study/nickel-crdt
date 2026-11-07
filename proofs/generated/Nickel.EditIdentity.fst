(* Latte generated F* view *)
module Nickel.EditIdentity

open Nickel.Prelude

open Rust_primitives

open Rust_primitives.Slice

open Core_models

open FStar.Pervasives

module Tactics = FStar.Tactics.V2

open Nickel.LoopUtil

open Nickel.EditAtomic

module Native = Nickel_crdt.Edit

module Result = Core_models.Result

module Option = Core_models.Option

let writer_code (writer: Native.t_Writer) : u8 =
  match writer with | Native.Writer_Alice -> begin mk_u8 0 end | Native.Writer_Bo -> begin mk_u8 1 end

let writer_index_is_exact (writer: Native.t_Writer) : Lemma (ensures Native.writer_index writer == writer_code writer) [SMTPat (Native.writer_index writer)] =
  ()

let writer_equality_exact (a: Native.t_Writer) (b: Native.t_Writer) : Lemma (ensures Native.impl_1.f_eq a b == (a ==? b)) =
  assert (Native.impl_1.f_eq a b == (a ==? b)) by (
    Tactics.prune "Nickel_crdt.Edit.writer_index";
    Tactics.smt_sync' 1 1
  )

let event_equality_exact (a: Native.t_EventId) (b: Native.t_EventId) : Lemma (ensures Native.impl_2.f_eq a b == (a ==? b)) =
  ()

let birth_equality_exact (a: Native.t_BirthId) (b: Native.t_BirthId) : Lemma (ensures Native.impl_3.f_eq a b == (a ==? b)) =
  ()

let fact_equality_exact (a: Native.t_Fact) (b: Native.t_Fact) : Lemma (ensures Native.fact_equal a b == (a ==? b)) [SMTPat (Native.fact_equal a b)] =
  ()

let invalid_is_exact (reason: Native.t_Invalid) : Lemma (ensures Native.invalid reason == Native.Error_Invalid reason) [SMTPat (Native.invalid reason)] =
  ()

let length (facts: t_Slice Native.t_Fact) : usize =
  Core_models.Slice.impl__len facts

let rec first_id (facts: t_Slice Native.t_Fact) (id: Native.t_EventId) (at: usize{v at <= v (length facts)}) : Tot (Option.t_Option Native.t_Fact) (decreases v (length facts) - v at) =
  if v at < v (length facts) then
    begin let old = Rust_primitives.Slice.slice_index facts at in
    if old.f_id ==? id then
      begin Option.Option_Some old end
    else
      begin first_id facts id (at +! mk_int 1) end end
  else
    begin Option.Option_None end

let classify (found: Option.t_Option Native.t_Fact) (fact: Native.t_Fact) : Result.t_Result bool Native.t_Error =
  match found with | Option.Option_None -> begin Result.Result_Ok false end | Option.Option_Some old -> begin if old ==? fact then
    begin Result.Result_Ok true end
  else
    begin Result.Result_Err (Native.Error_Invalid Native.Invalid_Conflict) end end

let scan_next (facts: t_Slice Native.t_Fact) (fact: Native.t_Fact) : Nickel.LoopUtil.transition unit (length facts) =
  fun _ at -> if (Rust_primitives.Slice.slice_index facts at).f_id ==? fact.f_id then
    begin Option.Option_None end
  else
    begin Option.Option_Some () end

let scan_stop (facts: t_Slice Native.t_Fact) (fact: Native.t_Fact) (value: unit) (at: usize{v at < v (length facts)}) : Result.t_Result bool Native.t_Error =
  classify (Option.Option_Some (Rust_primitives.Slice.slice_index facts at)) fact

let scan_done (value: unit) : Result.t_Result bool Native.t_Error =
  Result.Result_Ok false

let scan_run (facts: t_Slice Native.t_Fact) (fact: Native.t_Fact) (at: usize{v at <= v (length facts)}) : Result.t_Result bool Native.t_Error =
  Nickel.LoopUtil.option_run (length facts) at () (scan_next facts fact) (scan_stop facts fact) scan_done

let rec scan_lookup (facts: t_Slice Native.t_Fact) (fact: Native.t_Fact) (at: usize{v at <= v (length facts)}) : Lemma (ensures scan_run facts fact at == classify (first_id facts fact.f_id at) fact) (decreases v (length facts) - v at) =
  if v at < v (length facts) then
    begin Nickel.LoopUtil.option_run_step (length facts) at () (scan_next facts fact) (scan_stop facts fact) scan_done;
    if not ((Rust_primitives.Slice.slice_index facts at).f_id ==? fact.f_id) then
      begin scan_lookup facts fact (at +! mk_int 1) end
    else
      begin () end end
  else
    begin Nickel.LoopUtil.option_run_end (length facts) at () (scan_next facts fact) (scan_stop facts fact) scan_done end

let identity_result (facts: t_Slice Native.t_Fact) (fact: Native.t_Fact) : Result.t_Result bool Native.t_Error =
  if v fact.f_id.f_counter ==? 0 || v fact.f_id.f_counter > 9007199254740991 then
    begin Result.Result_Err (Native.Error_Invalid Native.Invalid_Counter) end
  else
    begin classify (first_id facts fact.f_id (mk_usize 0)) fact end

let duplicate_matches_lookup (facts: t_Slice Native.t_Fact) (fact: Native.t_Fact) : Lemma (ensures Native.impl_Replica__duplicate facts fact == identity_result facts fact) =
  Nickel.LoopUtil.option_interpret_any (mk_usize 0) (length facts) (scan_next facts fact) (scan_stop facts fact) scan_done;
  scan_lookup facts fact (mk_usize 0);
  assert (Native.impl_Replica__duplicate facts fact == identity_result facts fact) by (
    Tactics.prune "Nickel_crdt.Edit.fact_equal";
    Tactics.prune "Nickel_crdt.Edit.invalid";
    Tactics.smt_sync' 1 1
  )

let prefix_absent (facts: t_Slice Native.t_Fact) (id: Native.t_EventId) (at: usize) (finish: usize) : Type0 =
  forall(i: usize{v i < v (length facts)}). Prims.l_and (v at <= v i) (v i < v finish) ==> Prims.l_not ((Rust_primitives.Slice.slice_index facts i).f_id == id)

let rec lookup_at (facts: t_Slice Native.t_Fact) (id: Native.t_EventId) (found: usize{v found < v (length facts)}) (at: usize{v at <= v found}) : Lemma (requires (prefix_absent facts id at found /\ (Rust_primitives.Slice.slice_index facts found).f_id == id)) (ensures first_id facts id at == Option.Option_Some (Rust_primitives.Slice.slice_index facts found)) (decreases v found - v at) =
  if v at < v found then
    begin lookup_at facts id found (at +! mk_int 1) end
  else
    begin () end

let unique_ids (facts: t_Slice Native.t_Fact) : Type0 =
  forall(i: usize{v i < v (length facts)}) (j: usize{v j < v (length facts)}). (Rust_primitives.Slice.slice_index facts i).f_id == (Rust_primitives.Slice.slice_index facts j).f_id ==> i == j

let known_identity (before: Native.t_Replica) (old: Native.t_Fact) (fact: Native.t_Fact) : Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error =
  if old ==? fact then
    begin (before, Result.Result_Ok Native.Admission_Duplicate) end
  else
    begin (before, Result.Result_Err (Native.Error_Invalid Native.Invalid_Conflict)) end

let receive_known_identity (before: Native.t_Replica) (fact: Native.t_Fact) (index: usize{v index < v (length (Alloc.Vec.impl_1__as_slice before.f_facts))}) : Lemma (requires (unique_ids (Alloc.Vec.impl_1__as_slice before.f_facts) /\ (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice before.f_facts) index).f_id == fact.f_id /\ Prims.l_and (0 < v fact.f_id.f_counter) (v fact.f_id.f_counter <= 9007199254740991))) (ensures Native.impl_Replica__receive before fact == known_identity before (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice before.f_facts) index) fact) =
  lookup_at (Alloc.Vec.impl_1__as_slice before.f_facts) fact.f_id index (mk_usize 0);
  duplicate_matches_lookup (Alloc.Vec.impl_1__as_slice before.f_facts) fact;
  assert (Native.impl_Replica__receive before fact == known_identity before (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice before.f_facts) index) fact) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__plan";
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__duplicate";
    Tactics.smt_sync' 1 1
  )

let receive_invalid_counter (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (requires Prims.l_or (v fact.f_id.f_counter == 0) (v fact.f_id.f_counter > 9007199254740991)) (ensures Native.impl_Replica__receive before fact == (before, Result.Result_Err (Native.Error_Invalid Native.Invalid_Counter))) =
  duplicate_matches_lookup (Alloc.Vec.impl_1__as_slice before.f_facts) fact;
  assert (Native.impl_Replica__receive before fact == (before, Result.Result_Err (Native.Error_Invalid Native.Invalid_Counter))) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__plan";
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__duplicate";
    Tactics.smt_sync' 1 1
  )

let rec lookup_none (facts: t_Slice Native.t_Fact) (id: Native.t_EventId) (at: usize{v at <= v (length facts)}) : Lemma (requires first_id facts id at == Option.Option_None) (ensures prefix_absent facts id at (length facts)) (decreases v (length facts) - v at) =
  if v at < v (length facts) then
    begin lookup_none facts id (at +! mk_int 1) end
  else
    begin () end

let added_is_fresh (before: Native.t_Replica) (fact: Native.t_Fact) (outcome: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) : Type0 =
  match outcome with | (_, Result.Result_Ok Native.Admission_Added) -> begin prefix_absent (Alloc.Vec.impl_1__as_slice before.f_facts) fact.f_id (mk_usize 0) (length (Alloc.Vec.impl_1__as_slice before.f_facts)) end | _ -> begin Prims.l_True end

let receive_added_has_fresh_event_id (before: Native.t_Replica) (fact: Native.t_Fact) : Lemma (ensures added_is_fresh before fact (Native.impl_Replica__receive before fact)) =
  duplicate_matches_lookup (Alloc.Vec.impl_1__as_slice before.f_facts) fact;
  match Native.impl_Replica__receive before fact with | (_, Result.Result_Ok Native.Admission_Added) -> begin assert (first_id (Alloc.Vec.impl_1__as_slice before.f_facts) fact.f_id (mk_usize 0) == Option.Option_None) by (
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__plan";
    Tactics.prune "Nickel_crdt.Edit.impl_Replica__duplicate";
    Tactics.smt_sync' 1 1
  );
  lookup_none (Alloc.Vec.impl_1__as_slice before.f_facts) fact.f_id (mk_usize 0) end | _ -> begin () end

open Nickel.EditCommit

let authored_id_is_fresh (before: Native.t_Replica) (outcome: Native.t_Replica & Result.t_Result Native.t_Local Native.t_Error) : Type0 =
  match outcome with | (_, Result.Result_Ok (Native.Local_Authored fact)) -> begin prefix_absent (Alloc.Vec.impl_1__as_slice before.f_facts) fact.f_id (mk_usize 0) (length (Alloc.Vec.impl_1__as_slice before.f_facts)) end | _ -> begin Prims.l_True end

let authored_event_id_is_fresh (before: Native.t_Replica) (gap: usize) (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (delete: Alloc.Vec.t_Vec Native.t_BirthId Alloc.Alloc.t_Global) : Lemma (ensures authored_id_is_fresh before (Native.impl_Replica__edit before gap insert delete)) =
  Nickel.EditCommit.authored_fact_replays_same_commit before gap insert delete;
  match Native.impl_Replica__edit before gap insert delete with | (_, Result.Result_Ok (Native.Local_Authored fact)) -> begin receive_added_has_fresh_event_id before fact end | _ -> begin () end