(* Latte generated F* view *)
module Nickel.Register

open Nickel.Prelude

open Rust_primitives

open Core_models

open FStar.Pervasives

open Nickel.LoopUtil

module Native = Nickel_crdt.Register

module Envelope = Nickel_crdt.Causal

module Option = Core_models.Option

module Seq = FStar.Seq

module Tactics = FStar.Tactics.V2

type fact = Envelope.t_Event Native.t_Write

let bytes_prefix (a: t_Slice u8) (b: t_Slice u8) (at: nat) : Type0 =
  forall(j: nat). Prims.l_and (Prims.l_and (j < at) (j < Seq.length a)) (j < Seq.length b) ==> Seq.index a j == Seq.index b j

let bytes_same (a: t_Slice u8) (b: t_Slice u8) : Type0 =
  Prims.l_and (Seq.length a == Seq.length b) (bytes_prefix a b (Seq.length a))

let bytes_equal_exact (a: t_Slice u8) (b: t_Slice u8) : Lemma (ensures Prims.l_and (Native.bytes_equal a b == true <==> bytes_same a b) (Native.bytes_equal a b == false <==> Prims.l_not (bytes_same a b))) [SMTPat (Native.bytes_equal a b)] =
  if Seq.length a ==? Seq.length b then
    begin Nickel.LoopUtil.preserve_any #unit #bool (mk_usize 0) (Core_models.Slice.impl__len #u8 a) (fun (at: nat) (_: unit) -> bytes_prefix a b at) (fun (_: unit) -> bytes_same a b) (fun (r: bool) -> Prims.l_and (r == false) (Prims.l_not (bytes_same a b)));
    assert (Prims.l_and (Native.bytes_equal a b == true <==> bytes_same a b) (Native.bytes_equal a b == false <==> Prims.l_not (bytes_same a b))) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.smt_sync' 1 1
    ) end
  else
    begin () end

let higher (a: fact) (b: fact) : Type0 =
  Prims.l_or (v a.f_payload.f_lamport > v b.f_payload.f_lamport) (Prims.l_and (a.f_payload.f_lamport == b.f_payload.f_lamport) (v a.f_id.f_peer > v b.f_id.f_peer))

let later_is_priority (a: fact) (b: fact) : Lemma (ensures Prims.l_and (Native.later a b == true <==> higher a b) (Native.later a b == false <==> Prims.l_not (higher a b))) [SMTPat (Native.later a b)] =
  ()

let winner_prefix (facts: t_Slice fact) (key: u64) (at: nat) (choice: Option.t_Option usize) : Type0 =
  match choice with | Option.Option_None -> begin forall(j: nat). Prims.l_and (j < at) (j < Seq.length facts) ==> (Seq.index facts j).f_payload.f_key =!= key end | Option.Option_Some i -> begin Prims.l_and (Prims.l_and (Prims.l_and (v i < at) (v i < Seq.length facts)) ((Seq.index facts (v i)).f_payload.f_key == key)) (forall(j: nat). Prims.l_and (Prims.l_and (j < at) (j < Seq.length facts)) ((Seq.index facts j).f_payload.f_key == key) ==> Prims.l_not (higher (Seq.index facts j) (Seq.index facts (v i)))) end

let winner_next (facts: t_Slice fact) (key: u64) (j: usize{v j < Seq.length facts}) (choice: Option.t_Option usize) : Option.t_Option usize =
  if (Rust_primitives.Slice.slice_index facts j).f_payload.f_key ==? key then
    begin match choice with | Option.Option_None -> begin Option.Option_Some j end | Option.Option_Some k -> begin if v k < Seq.length facts && Native.later (Rust_primitives.Slice.slice_index facts j) (Rust_primitives.Slice.slice_index facts k) then
      begin Option.Option_Some j end
    else
      begin choice end end end
  else
    begin choice end

let winner_step_preserves (facts: t_Slice fact) (key: u64) : Lemma (ensures forall(j: usize{v j < Seq.length facts}) (choice: Option.t_Option usize). winner_prefix facts key (v j) choice ==> winner_prefix facts key (v j + 1) (winner_next facts key j choice)) =
  let each (j: usize{v j < Seq.length facts}) (choice: Option.t_Option usize) : Lemma (requires winner_prefix facts key (v j) choice) (ensures winner_prefix facts key (v j + 1) (winner_next facts key j choice)) = match choice with | Option.Option_None -> begin assert (winner_prefix facts key (v j + 1) (winner_next facts key j choice)) by (
    Tactics.prune "Nickel_crdt.Register.later";
    Tactics.smt_sync' 1 1
  ) end | Option.Option_Some k -> begin if v k < Seq.length facts then
    begin later_is_priority (Rust_primitives.Slice.slice_index facts j) (Rust_primitives.Slice.slice_index facts k);
    assert (winner_prefix facts key (v j + 1) (winner_next facts key j choice)) by (
      Tactics.prune "Nickel_crdt.Register.later";
      Tactics.smt_sync' 1 1
    ) end
  else
    begin () end end in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each)

let winner_is_priority_maximum (facts: t_Slice fact) (key: u64) : Lemma (ensures winner_prefix facts key (Seq.length facts) (Native.winner facts key)) =
  let each_priority (a: fact) (b: fact) : Lemma (ensures Prims.l_and (Native.later a b == true <==> higher a b) (Native.later a b == false <==> Prims.l_not (higher a b))) [SMTPat (Native.later a b)] = later_is_priority a b in
  winner_step_preserves facts key;
  Nickel.LoopUtil.plain_preserve_any #(Option.t_Option usize) (mk_usize 0) (Core_models.Slice.impl__len #fact facts) (fun (at: nat{at <= v (Core_models.Slice.impl__len #fact facts)}) (choice: Option.t_Option usize) -> winner_prefix facts key at choice) (fun (choice: Option.t_Option usize) -> winner_prefix facts key (Seq.length facts) choice);
  assert (winner_prefix facts key (Seq.length facts) (Native.winner facts key)) by (
    Tactics.prune "Nickel_crdt.Register.later";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range";
    Tactics.smt_sync' 1 1
  )

let selected_value (facts: t_Slice fact) (key: u64) (initial: t_Slice u8) (value: t_Slice u8) : Type0 =
  Prims.l_or (Prims.l_and (forall(j: nat). j < Seq.length facts ==> (Seq.index facts j).f_payload.f_key =!= key) (bytes_same value initial)) (exists(i: nat). Prims.l_and (Prims.l_and (Prims.l_and (i < Seq.length facts) ((Seq.index facts i).f_payload.f_key == key)) (bytes_same value (Alloc.Vec.impl_1__as_slice (Seq.index facts i).f_payload.f_value))) (forall(j: nat). Prims.l_and (j < Seq.length facts) ((Seq.index facts j).f_payload.f_key == key) ==> Prims.l_not (higher (Seq.index facts j) (Seq.index facts i))))

let none_prefix_is_absent (facts: t_Slice fact) (key: u64) (at: nat) : Lemma (requires winner_prefix facts key at Option.Option_None) (ensures forall(j: nat). Prims.l_and (j < at) (j < Seq.length facts) ==> (Seq.index facts j).f_payload.f_key =!= key) =
  ()

let initial_copy_preserves_bytes (initial: t_Slice u8) : Lemma (ensures bytes_same (Alloc.Vec.impl_1__as_slice (Alloc.Slice.impl__to_vec #u8 initial)) initial) =
  ()

let read_history_selects_maximum (facts: t_Slice fact) (initial: t_Slice u8) (key: u64) : Lemma (ensures selected_value facts key initial (Alloc.Vec.impl_1__as_slice (Native.read_history facts initial key))) =
  winner_is_priority_maximum facts key;
  initial_copy_preserves_bytes initial;
  match Native.winner facts key with | Option.Option_None -> begin assert (winner_prefix facts key (Seq.length facts) Option.Option_None) by (
    Tactics.prune "Nickel_crdt.Register.winner";
    Tactics.smt_sync' 1 1
  );
  none_prefix_is_absent facts key (Seq.length facts);
  assert (Native.read_history facts initial key == Alloc.Slice.impl__to_vec #u8 initial) by (
    Tactics.prune "Nickel_crdt.Register.winner";
    Tactics.smt_sync' 1 1
  );
  assert (selected_value facts key initial (Alloc.Vec.impl_1__as_slice (Native.read_history facts initial key))) by (
    Tactics.prune "Nickel_crdt.Register.winner";
    Tactics.smt_sync' 1 1
  ) end | Option.Option_Some i -> begin assert (selected_value facts key initial (Alloc.Vec.impl_1__as_slice (Native.read_history facts initial key))) by (
    Tactics.prune "Nickel_crdt.Register.winner";
    Tactics.smt_sync' 1 1
  ) end

open Nickel.EventShell

module Result = Core_models.Result

module Shell = Nickel_crdt.Event_shell

let receive_publication_is_exact (before: Native.t_Replica) (offered: fact) : Lemma (ensures Native.impl_Replica__receive before offered == Nickel.EventShell.received before (Native.planned () before offered) Native.Admission_Added Native.Admission_Duplicate) [SMTPat (Native.impl_Replica__receive before offered)] =
  Nickel.EventShell.borrowed_publication_is_exact before offered () Native.planned Native.Admission_Added Native.Admission_Duplicate;
  match Shell.receive_into before offered () Native.planned Native.Admission_Added Native.Admission_Duplicate with | (next, result) -> begin assert (Native.impl_Replica__receive before offered == Nickel.EventShell.received before (Native.planned () before offered) Native.Admission_Added Native.Admission_Duplicate) by (
    Tactics.prune "Nickel_crdt.Event_shell.receive_into";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.smt_sync' 1 1
  ) end

let public_read_is_history (before: Native.t_Replica) (key: u64) : Lemma (ensures Native.impl_Replica__read before key == Native.read_history (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice before.f_initial) key) [SMTPat (Native.impl_Replica__read before key)] =
  ()

let equal_value_write_is_neutral (before: Native.t_Replica) (key: u64) (value: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) : Lemma (requires (Seq.length (Alloc.Vec.impl_1__as_slice value) <= v before.f_limits.f_value_bytes /\ bytes_same (Alloc.Vec.impl_1__as_slice value) (Alloc.Vec.impl_1__as_slice (Native.impl_Replica__read before key)))) (ensures Native.impl_Replica__write before key value == (before, Result.Result_Ok Option.Option_None)) =
  bytes_equal_exact (Alloc.Vec.impl_1__as_slice value) (Alloc.Vec.impl_1__as_slice (Native.impl_Replica__read before key));
  assert (Native.impl_Replica__write before key value == (before, Result.Result_Ok Option.Option_None)) by (
    Tactics.prune "Nickel_crdt.Register.bytes_equal";
    Tactics.prune "Nickel_crdt.Register.impl_Replica__read";
    Tactics.smt_sync' 1 1
  )

let vector_bytes_extensional (a: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) (b: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) : Lemma (requires bytes_same (Alloc.Vec.impl_1__as_slice a) (Alloc.Vec.impl_1__as_slice b)) (ensures a == b) =
  match (a, b) with | (Alloc.Vec.Vec xs _, Alloc.Vec.Vec ys _) -> begin Seq.lemma_eq_intro xs ys;
  Seq.lemma_eq_elim xs ys end

let bytes_same_reflexive (a: t_Slice u8) : Lemma (ensures bytes_same a a) =
  ()

let write_equal_is_exact (a: Native.t_Write) (b: Native.t_Write) : Lemma (ensures Native.write_equal a b == true <==> a == b) [SMTPat (Native.write_equal a b)] =
  bytes_same_reflexive (Alloc.Vec.impl_1__as_slice a.f_value);
  bytes_same_reflexive (Alloc.Vec.impl_1__as_slice a.f_observed);
  bytes_equal_exact (Alloc.Vec.impl_1__as_slice a.f_value) (Alloc.Vec.impl_1__as_slice b.f_value);
  bytes_equal_exact (Alloc.Vec.impl_1__as_slice a.f_observed) (Alloc.Vec.impl_1__as_slice b.f_observed);
  if Native.write_equal a b then
    begin assert (Prims.l_and (bytes_same (Alloc.Vec.impl_1__as_slice a.f_value) (Alloc.Vec.impl_1__as_slice b.f_value)) (bytes_same (Alloc.Vec.impl_1__as_slice a.f_observed) (Alloc.Vec.impl_1__as_slice b.f_observed))) by (
      Tactics.prune "Nickel_crdt.Register.bytes_equal";
      Tactics.smt_sync' 1 1
    );
    vector_bytes_extensional a.f_value b.f_value;
    vector_bytes_extensional a.f_observed b.f_observed;
    assert (a == b) by (
      Tactics.prune "Nickel_crdt.Register.bytes_equal";
      Tactics.smt_sync' 1 1
    ) end
  else
    begin assert (a =!= b) by (
      Tactics.prune "Nickel_crdt.Register.bytes_equal";
      Tactics.smt_sync' 1 1
    ) end

let copy_fact_is_exact (f: fact) : Lemma (ensures Native.copy_fact f == f) =
  ()

open Nickel.CausalEnvelope

let fact_equal_is_complete (a: fact) (b: fact) : Lemma (ensures Native.fact_equal a b == true <==> Prims.l_and (Prims.l_and (Nickel.CausalEnvelope.same_id a.f_id b.f_id) (Nickel.CausalEnvelope.ids_equal (Alloc.Vec.impl_1__as_slice a.f_after) (Alloc.Vec.impl_1__as_slice b.f_after))) (a.f_payload == b.f_payload)) =
  let each_payload (x: Native.t_Write) (y: Native.t_Write) : Lemma (ensures Native.write_equal x y == true <==> x == y) [SMTPat (Native.write_equal x y)] = write_equal_is_exact x y in
  Nickel.CausalEnvelope.event_equal_exact a b Native.write_equal;
  assert (Native.fact_equal a b == true <==> Prims.l_and (Prims.l_and (Nickel.CausalEnvelope.same_id a.f_id b.f_id) (Nickel.CausalEnvelope.ids_equal (Alloc.Vec.impl_1__as_slice a.f_after) (Alloc.Vec.impl_1__as_slice b.f_after))) (a.f_payload == b.f_payload)) by (
    Tactics.prune "Nickel_crdt.Causal.event_equal";
    Tactics.prune "Nickel_crdt.Register.write_equal";
    Tactics.smt_sync' 1 1
  )

let write_outcome (before: Native.t_Replica) (outcome: Native.t_Replica & Result.t_Result (Option.t_Option fact) Native.t_Error) : Type0 =
  match outcome with | (next, result) -> begin match result with | Result.Result_Err _ -> begin next == before end | Result.Result_Ok option -> begin match option with | Option.Option_None -> begin next == before end | Option.Option_Some authored -> begin Prims.l_and (Prims.l_and (authored.f_id.f_peer == before.f_writer) (authored.f_id.f_counter == before.f_next_counter)) (v next.f_next_counter == v before.f_next_counter + 1) end end end

let write_publication_on_every_return (before: Native.t_Replica) (key: u64) (value: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) : Lemma (ensures write_outcome before (Native.impl_Replica__write before key value)) =
  match Core_models.Num.impl_u64__checked_add before.f_next_counter (mk_u64 1) with | Option.Option_None -> begin assert (write_outcome before (Native.impl_Replica__write before key value)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Event_layer.frontier";
    Tactics.prune "Nickel_crdt.Register.next_lamport";
    Tactics.prune "Nickel_crdt.Register.bytes_equal";
    Tactics.prune "Nickel_crdt.Register.impl_Replica__read";
    Tactics.smt_sync' 1 1
  ) end | Option.Option_Some next -> begin match Nickel_crdt.Event_layer.frontier (Alloc.Vec.impl_1__as_slice before.f_facts) Native.v_OPS._1 with | Result.Result_Err _ -> begin assert (write_outcome before (Native.impl_Replica__write before key value)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Event_layer.frontier";
    Tactics.prune "Nickel_crdt.Register.next_lamport";
    Tactics.prune "Nickel_crdt.Register.bytes_equal";
    Tactics.prune "Nickel_crdt.Register.impl_Replica__read";
    Tactics.smt_sync' 1 1
  ) end | Result.Result_Ok parents -> begin match Native.next_lamport (Alloc.Vec.impl_1__as_slice before.f_facts) with | Result.Result_Err _ -> begin assert (write_outcome before (Native.impl_Replica__write before key value)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Event_layer.frontier";
    Tactics.prune "Nickel_crdt.Register.next_lamport";
    Tactics.prune "Nickel_crdt.Register.bytes_equal";
    Tactics.prune "Nickel_crdt.Register.impl_Replica__read";
    Tactics.smt_sync' 1 1
  ) end | Result.Result_Ok clock -> begin assert (write_outcome before (Native.impl_Replica__write before key value)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Event_layer.frontier";
    Tactics.prune "Nickel_crdt.Register.next_lamport";
    Tactics.prune "Nickel_crdt.Register.bytes_equal";
    Tactics.prune "Nickel_crdt.Register.impl_Replica__read";
    Tactics.smt_sync' 1 1
  ) end end end