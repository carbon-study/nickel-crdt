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

let private_frame (before: Native.t_Replica) (next: Native.t_Replica) : Type0 =
  Prims.l_and (Prims.l_and (Prims.l_and (next.f_writer == before.f_writer) (next.f_next_counter == before.f_next_counter)) (next.f_initial == before.f_initial)) (next.f_limits == before.f_limits)

let prepare_preserves_private (before: Native.t_Replica) (offered: fact) : Lemma (ensures forall(next: Native.t_Replica). Native.prepare () before offered == Result.Result_Ok next ==> private_frame before next) [SMTPat (Native.prepare () before offered)] =
  assert (forall(next: Native.t_Replica). Native.prepare () before offered == Result.Result_Ok next ==> private_frame before next) by (
    Tactics.prune "Nickel_crdt.Event_layer.push";
    Tactics.smt_sync' 1 1
  )

let execute_preserves_private (before: Native.t_Replica) : Lemma (ensures forall(next: Native.t_Replica). Native.execute () before == Result.Result_Ok next ==> private_frame before next) [SMTPat (Native.execute () before)] =
  assert (forall(next: Native.t_Replica). Native.execute () before == Result.Result_Ok next ==> private_frame before next) by (
    Tactics.prune "Nickel_crdt.Event_layer.canonical";
    Tactics.smt_sync' 1 1
  )

let shared_success_stages (#r: Type0) (#f: Type0) (#c: Type0) (#e: Type0) {| i0 : Core_models.Clone.t_Clone r |} (before: r) (offered: f) (context: c) (duplicate: c -> r -> f -> Result.t_Result bool e) (validate: c -> r -> f -> Result.t_Result unit e) (prepare: c -> r -> f -> Result.t_Result r e) (execute: c -> r -> Result.t_Result r e) : Lemma (ensures forall(next: r). Shell.plan before offered context duplicate validate prepare execute == Result.Result_Ok (Option.Option_Some next) ==> Prims.l_and (Prims.l_and (duplicate context before offered == Result.Result_Ok false) (validate context before offered == Result.Result_Ok ())) (exists(candidate: r). Prims.l_and (prepare context before offered == Result.Result_Ok candidate) (execute context candidate == Result.Result_Ok next))) =
  Nickel.EventShell.planning_is_exact before offered context duplicate validate prepare execute;
  assert (forall(next: r). Shell.plan before offered context duplicate validate prepare execute == Result.Result_Ok (Option.Option_Some next) ==> Prims.l_and (Prims.l_and (duplicate context before offered == Result.Result_Ok false) (validate context before offered == Result.Result_Ok ())) (exists(candidate: r). Prims.l_and (prepare context before offered == Result.Result_Ok candidate) (execute context candidate == Result.Result_Ok next))) by (
    Tactics.prune "Nickel_crdt.Event_shell.plan";
    Tactics.smt_sync' 1 1
  )

let planned_preserves_private (before: Native.t_Replica) (offered: fact) : Lemma (ensures forall(next: Native.t_Replica). Native.planned () before offered == Result.Result_Ok (Option.Option_Some next) ==> private_frame before next) [SMTPat (Native.planned () before offered)] =
  shared_success_stages before offered () Native.duplicate Native.validate Native.prepare Native.execute;
  prepare_preserves_private before offered;
  assert (forall(next: Native.t_Replica). Native.planned () before offered == Result.Result_Ok (Option.Option_Some next) ==> private_frame before next) by (
    Tactics.prune "Nickel_crdt.Event_shell.plan";
    Tactics.prune "Nickel_crdt.Register.prepare";
    Tactics.prune "Nickel_crdt.Register.execute";
    Tactics.prune "Nickel_crdt.Register.duplicate";
    Tactics.prune "Nickel_crdt.Register.validate";
    Tactics.smt_sync' 1 1
  )

let receive_frame (before: Native.t_Replica) (outcome: Native.t_Replica & Result.t_Result Native.t_Admission Native.t_Error) : Type0 =
  match outcome with | (next, _) -> begin private_frame before next end

let receive_preserves_private (before: Native.t_Replica) (offered: fact) : Lemma (ensures receive_frame before (Native.impl_Replica__receive before offered)) [SMTPat (Native.impl_Replica__receive before offered)] =
  receive_publication_is_exact before offered;
  planned_preserves_private before offered;
  match Native.planned () before offered with | Result.Result_Err _ -> begin assert (receive_frame before (Native.impl_Replica__receive before offered)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.smt_sync' 1 1
  ) end | Result.Result_Ok option -> begin match option with | Option.Option_None -> begin assert (receive_frame before (Native.impl_Replica__receive before offered)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.smt_sync' 1 1
  ) end | Option.Option_Some candidate -> begin assert (private_frame before candidate) by (
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.smt_sync' 1 1
  );
  assert (receive_frame before (Native.impl_Replica__receive before offered)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.smt_sync' 1 1
  ) end end

let installed_candidate (candidate: Native.t_Replica) (next: Native.t_Replica) : Type0 =
  Prims.l_and (Prims.l_and (Prims.l_and (next.f_writer == candidate.f_writer) (next.f_initial == candidate.f_initial)) (next.f_limits == candidate.f_limits)) (next.f_facts == candidate.f_facts)

let write_installation (before: Native.t_Replica) (key: u64) (value: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) (outcome: Native.t_Replica & Result.t_Result (Option.t_Option fact) Native.t_Error) : Type0 =
  match outcome with | (next, result) -> begin match result with | Result.Result_Err _ -> begin next == before end | Result.Result_Ok option -> begin match option with | Option.Option_None -> begin next == before end | Option.Option_Some authored -> begin Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (authored.f_id.f_peer == before.f_writer) (authored.f_id.f_counter == before.f_next_counter)) (authored.f_payload.f_key == key)) (authored.f_payload.f_value == value)) (authored.f_payload.f_observed == Native.impl_Replica__read before key)) (Nickel_crdt.Event_layer.frontier (Alloc.Vec.impl_1__as_slice before.f_facts) Native.v_OPS._1 == Result.Result_Ok authored.f_after)) (Native.next_lamport (Alloc.Vec.impl_1__as_slice before.f_facts) == Result.Result_Ok authored.f_payload.f_lamport)) (exists(candidate: Native.t_Replica). Prims.l_and (Prims.l_and (Native.planned () before authored == Result.Result_Ok (Option.Option_Some candidate)) (installed_candidate candidate next)) (private_frame before candidate)) end end end

let write_installs_successful_candidate (before: Native.t_Replica) (key: u64) (value: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) : Lemma (ensures write_installation before key value (Native.impl_Replica__write before key value)) =
  match Core_models.Num.impl_u64__checked_add before.f_next_counter (mk_u64 1) with | Option.Option_None -> begin assert (write_installation before key value (Native.impl_Replica__write before key value)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel_crdt.Event_layer.frontier";
    Tactics.prune "Nickel_crdt.Register.next_lamport";
    Tactics.prune "Nickel_crdt.Register.bytes_equal";
    Tactics.prune "Nickel_crdt.Register.impl_Replica__read";
    Tactics.smt_sync' 1 1
  ) end | Option.Option_Some counter -> begin match Nickel_crdt.Event_layer.frontier (Alloc.Vec.impl_1__as_slice before.f_facts) Native.v_OPS._1 with | Result.Result_Err _ -> begin assert (write_installation before key value (Native.impl_Replica__write before key value)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel_crdt.Event_layer.frontier";
    Tactics.prune "Nickel_crdt.Register.next_lamport";
    Tactics.prune "Nickel_crdt.Register.bytes_equal";
    Tactics.prune "Nickel_crdt.Register.impl_Replica__read";
    Tactics.smt_sync' 1 1
  ) end | Result.Result_Ok parents -> begin match Native.next_lamport (Alloc.Vec.impl_1__as_slice before.f_facts) with | Result.Result_Err _ -> begin assert (write_installation before key value (Native.impl_Replica__write before key value)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel_crdt.Event_layer.frontier";
    Tactics.prune "Nickel_crdt.Register.next_lamport";
    Tactics.prune "Nickel_crdt.Register.bytes_equal";
    Tactics.prune "Nickel_crdt.Register.impl_Replica__read";
    Tactics.smt_sync' 1 1
  ) end | Result.Result_Ok clock -> begin let (authored: fact) = { Envelope.f_id = { Envelope.f_peer = before.f_writer; f_counter = before.f_next_counter }; f_after = parents; f_payload = { Native.f_key = key; f_value = value; f_observed = Native.impl_Replica__read before key; f_lamport = clock } } in
  receive_publication_is_exact before authored;
  receive_preserves_private before authored;
  match Native.planned () before authored with | Result.Result_Err _ -> begin assert (write_installation before key value (Native.impl_Replica__write before key value)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel_crdt.Event_layer.frontier";
    Tactics.prune "Nickel_crdt.Register.next_lamport";
    Tactics.prune "Nickel_crdt.Register.bytes_equal";
    Tactics.prune "Nickel_crdt.Register.impl_Replica__read";
    Tactics.smt_sync' 1 1
  ) end | Result.Result_Ok option -> begin match option with | Option.Option_None -> begin assert (write_installation before key value (Native.impl_Replica__write before key value)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel_crdt.Event_layer.frontier";
    Tactics.prune "Nickel_crdt.Register.next_lamport";
    Tactics.prune "Nickel_crdt.Register.bytes_equal";
    Tactics.prune "Nickel_crdt.Register.impl_Replica__read";
    Tactics.smt_sync' 1 1
  ) end | Option.Option_Some candidate -> begin assert (write_installation before key value (Native.impl_Replica__write before key value)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.Register.planned_preserves_private";
    Tactics.prune "Nickel_crdt.Event_layer.frontier";
    Tactics.prune "Nickel_crdt.Register.next_lamport";
    Tactics.prune "Nickel_crdt.Register.bytes_equal";
    Tactics.prune "Nickel_crdt.Register.impl_Replica__read";
    Tactics.smt_sync' 1 1
  ) end end end end end

let basis_payload_checks (before: Native.t_Replica) (offered: fact) (basis: Alloc.Vec.t_Vec fact Alloc.Alloc.t_Global) : Type0 =
  Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (v offered.f_id.f_counter > 0) (Seq.length (Alloc.Vec.impl_1__as_slice offered.f_payload.f_value) <= v before.f_limits.f_value_bytes)) (Seq.length (Alloc.Vec.impl_1__as_slice offered.f_payload.f_observed) <= v before.f_limits.f_value_bytes)) (bytes_same (Alloc.Vec.impl_1__as_slice offered.f_payload.f_observed) (Alloc.Vec.impl_1__as_slice (Native.read_history (Alloc.Vec.impl_1__as_slice basis) (Alloc.Vec.impl_1__as_slice before.f_initial) offered.f_payload.f_key)))) (Prims.l_not (bytes_same (Alloc.Vec.impl_1__as_slice offered.f_payload.f_value) (Alloc.Vec.impl_1__as_slice offered.f_payload.f_observed)))) (Native.next_lamport (Alloc.Vec.impl_1__as_slice basis) == Result.Result_Ok offered.f_payload.f_lamport)

let selected_basis_checks (before: Native.t_Replica) (offered: fact) : Type0 =
  exists(selected: Alloc.Vec.t_Vec Envelope.t_Id Alloc.Alloc.t_Global) (basis: Alloc.Vec.t_Vec fact Alloc.Alloc.t_Global). Prims.l_and (Prims.l_and (Nickel_crdt.Event_layer.validate_event (Alloc.Vec.impl_1__as_slice before.f_facts) offered before.f_limits.f_events before.f_limits.f_dependencies Native.v_OPS == Result.Result_Ok selected) (Nickel_crdt.Event_layer.select_basis (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice selected) Native.v_OPS._1 == Result.Result_Ok basis)) (basis_payload_checks before offered basis)

let validation_is_exact_basis_checks (before: Native.t_Replica) (offered: fact) : Lemma (ensures Native.validate () before offered == Result.Result_Ok () <==> selected_basis_checks before offered) [SMTPat (Native.validate () before offered)] =
  match Nickel_crdt.Event_layer.validate_event (Alloc.Vec.impl_1__as_slice before.f_facts) offered before.f_limits.f_events before.f_limits.f_dependencies Native.v_OPS with | Result.Result_Err _ -> begin assert (Native.validate () before offered == Result.Result_Ok () <==> selected_basis_checks before offered) by (
    Tactics.prune "Nickel_crdt.Event_layer.validate_event";
    Tactics.prune "Nickel_crdt.Event_layer.select_basis";
    Tactics.prune "Nickel_crdt.Register.next_lamport";
    Tactics.prune "Nickel_crdt.Register.read_history";
    Tactics.prune "Nickel_crdt.Register.bytes_equal";
    Tactics.smt_sync' 1 1
  ) end | Result.Result_Ok selected -> begin match Nickel_crdt.Event_layer.select_basis (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice selected) Native.v_OPS._1 with | Result.Result_Err _ -> begin assert (Native.validate () before offered == Result.Result_Ok () <==> selected_basis_checks before offered) by (
    Tactics.prune "Nickel_crdt.Event_layer.validate_event";
    Tactics.prune "Nickel_crdt.Event_layer.select_basis";
    Tactics.prune "Nickel_crdt.Register.next_lamport";
    Tactics.prune "Nickel_crdt.Register.read_history";
    Tactics.prune "Nickel_crdt.Register.bytes_equal";
    Tactics.smt_sync' 1 1
  ) end | Result.Result_Ok basis -> begin bytes_equal_exact (Alloc.Vec.impl_1__as_slice offered.f_payload.f_observed) (Alloc.Vec.impl_1__as_slice (Native.read_history (Alloc.Vec.impl_1__as_slice basis) (Alloc.Vec.impl_1__as_slice before.f_initial) offered.f_payload.f_key));
  bytes_equal_exact (Alloc.Vec.impl_1__as_slice offered.f_payload.f_value) (Alloc.Vec.impl_1__as_slice offered.f_payload.f_observed);
  match Native.next_lamport (Alloc.Vec.impl_1__as_slice basis) with | Result.Result_Err _ -> begin assert (Native.validate () before offered == Result.Result_Ok () <==> selected_basis_checks before offered) by (
    Tactics.prune "Nickel_crdt.Event_layer.validate_event";
    Tactics.prune "Nickel_crdt.Event_layer.select_basis";
    Tactics.prune "Nickel_crdt.Register.next_lamport";
    Tactics.prune "Nickel_crdt.Register.read_history";
    Tactics.prune "Nickel_crdt.Register.bytes_equal";
    Tactics.smt_sync' 1 1
  ) end | Result.Result_Ok clock -> begin assert (selected_basis_checks before offered <==> basis_payload_checks before offered basis) by (
    Tactics.prune "Nickel_crdt.Event_layer.validate_event";
    Tactics.prune "Nickel_crdt.Event_layer.select_basis";
    Tactics.prune "Nickel_crdt.Register.next_lamport";
    Tactics.prune "Nickel_crdt.Register.read_history";
    Tactics.prune "Nickel_crdt.Register.bytes_equal";
    Tactics.smt_sync' 1 1
  );
  assert (Native.validate () before offered == Result.Result_Ok () <==> selected_basis_checks before offered) by (
    Tactics.prune "Nickel_crdt.Event_layer.validate_event";
    Tactics.prune "Nickel_crdt.Event_layer.select_basis";
    Tactics.prune "Nickel_crdt.Register.next_lamport";
    Tactics.prune "Nickel_crdt.Register.read_history";
    Tactics.prune "Nickel_crdt.Register.bytes_equal";
    Tactics.smt_sync' 1 1
  ) end end end

let planned_checks_payload (before: Native.t_Replica) (offered: fact) : Lemma (ensures forall(next: Native.t_Replica). Native.planned () before offered == Result.Result_Ok (Option.Option_Some next) ==> selected_basis_checks before offered) [SMTPat (Native.planned () before offered)] =
  shared_success_stages before offered () Native.duplicate Native.validate Native.prepare Native.execute;
  validation_is_exact_basis_checks before offered;
  assert (forall(next: Native.t_Replica). Native.planned () before offered == Result.Result_Ok (Option.Option_Some next) ==> selected_basis_checks before offered) by (
    Tactics.prune "Nickel_crdt.Event_shell.plan";
    Tactics.prune "Nickel_crdt.Register.validate";
    Tactics.prune "Nickel_crdt.Register.duplicate";
    Tactics.prune "Nickel_crdt.Register.prepare";
    Tactics.prune "Nickel_crdt.Register.execute";
    Tactics.smt_sync' 1 1
  )

let receive_added_checks_payload (before: Native.t_Replica) (offered: fact) : Lemma (ensures forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> selected_basis_checks before offered) =
  receive_publication_is_exact before offered;
  planned_checks_payload before offered;
  match Native.planned () before offered with | Result.Result_Err _ -> begin assert (forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> selected_basis_checks before offered) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.smt_sync' 1 1
  ) end | Result.Result_Ok option -> begin match option with | Option.Option_None -> begin assert (forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> selected_basis_checks before offered) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.smt_sync' 1 1
  ) end | Option.Option_Some candidate -> begin assert (forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> selected_basis_checks before offered) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.smt_sync' 1 1
  ) end end

let clock_maximum_prefix (facts: t_Slice fact) (at: nat) (highest: u64) : Type0 =
  Prims.l_and (forall(j: nat). Prims.l_and (j < at) (j < Seq.length facts) ==> v (Seq.index facts j).f_payload.f_lamport <= v highest) (Prims.l_or (v highest == 0) (exists(j: nat). Prims.l_and (Prims.l_and (j < at) (j < Seq.length facts)) ((Seq.index facts j).f_payload.f_lamport == highest)))

let clock_successor (facts: t_Slice fact) (clock: u64) : Type0 =
  Prims.l_and (Prims.l_and (v clock > 0) (forall(j: nat). j < Seq.length facts ==> v (Seq.index facts j).f_payload.f_lamport < v clock)) (Prims.l_or (v clock == 1) (exists(j: nat). Prims.l_and (j < Seq.length facts) (v (Seq.index facts j).f_payload.f_lamport + 1 == v clock)))

let clock_result (facts: t_Slice fact) (result: Result.t_Result u64 Native.t_Error) : Type0 =
  match result with | Result.Result_Ok clock -> begin clock_successor facts clock end | Result.Result_Err error -> begin Prims.l_and (error == Native.Error_ClockExhausted) (exists(j: nat). Prims.l_and (j < Seq.length facts) (v (Seq.index facts j).f_payload.f_lamport == 18446744073709551615)) end

let next_lamport_is_maximum_successor (facts: t_Slice fact) : Lemma (ensures clock_result facts (Native.next_lamport facts)) [SMTPat (Native.next_lamport facts)] =
  Nickel.LoopUtil.plain_preserve_any #u64 (mk_usize 0) (Core_models.Slice.impl__len #fact facts) (fun (at: nat{at <= v (Core_models.Slice.impl__len #fact facts)}) (highest: u64) -> clock_maximum_prefix facts at highest) (fun (highest: u64) -> clock_maximum_prefix facts (Seq.length facts) highest);
  assert (clock_result facts (Native.next_lamport facts)) by (
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range";
    Tactics.smt_sync' 1 1
  )

let selected_basis_clock_successor (before: Native.t_Replica) (offered: fact) : Type0 =
  exists(selected: Alloc.Vec.t_Vec Envelope.t_Id Alloc.Alloc.t_Global) (basis: Alloc.Vec.t_Vec fact Alloc.Alloc.t_Global). Prims.l_and (Prims.l_and (Nickel_crdt.Event_layer.validate_event (Alloc.Vec.impl_1__as_slice before.f_facts) offered before.f_limits.f_events before.f_limits.f_dependencies Native.v_OPS == Result.Result_Ok selected) (Nickel_crdt.Event_layer.select_basis (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice selected) Native.v_OPS._1 == Result.Result_Ok basis)) (clock_successor (Alloc.Vec.impl_1__as_slice basis) offered.f_payload.f_lamport)

let receive_added_clock_is_maximum_successor (before: Native.t_Replica) (offered: fact) : Lemma (ensures forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> selected_basis_clock_successor before offered) =
  let each_basis (basis: Alloc.Vec.t_Vec fact Alloc.Alloc.t_Global) : Lemma (requires Native.next_lamport (Alloc.Vec.impl_1__as_slice basis) == Result.Result_Ok offered.f_payload.f_lamport) (ensures clock_successor (Alloc.Vec.impl_1__as_slice basis) offered.f_payload.f_lamport) =
    next_lamport_is_maximum_successor (Alloc.Vec.impl_1__as_slice basis);
    assert (clock_successor (Alloc.Vec.impl_1__as_slice basis) offered.f_payload.f_lamport) by (
      Tactics.prune "Nickel_crdt.Register.next_lamport";
      Tactics.smt_sync' 1 1
    ) in
  receive_added_checks_payload before offered;
  FStar.Classical.forall_intro (FStar.Classical.move_requires each_basis);
  assert (forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> selected_basis_clock_successor before offered) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel_crdt.Register.next_lamport";
    Tactics.prune "Nickel_crdt.Event_layer.validate_event";
    Tactics.prune "Nickel_crdt.Event_layer.select_basis";
    Tactics.smt_sync' 1 1
  )

open Nickel.Canonical

let id_vectors_are_extensional (a: Alloc.Vec.t_Vec Envelope.t_Id Alloc.Alloc.t_Global) (b: Alloc.Vec.t_Vec Envelope.t_Id Alloc.Alloc.t_Global) : Lemma (requires Nickel.CausalEnvelope.ids_equal (Alloc.Vec.impl_1__as_slice a) (Alloc.Vec.impl_1__as_slice b)) (ensures a == b) =
  match (a, b) with | (Alloc.Vec.Vec xs _, Alloc.Vec.Vec ys _) -> begin Seq.lemma_eq_intro xs ys;
  Seq.lemma_eq_elim xs ys end

let fact_equal_is_whole_value (a: fact) (b: fact) : Lemma (ensures Native.fact_equal a b == true <==> a == b) =
  fact_equal_is_complete a b;
  if Native.fact_equal a b then
    begin id_vectors_are_extensional a.f_after b.f_after;
    assert (a == b) by (
      Tactics.prune "Nickel_crdt.Register.fact_equal";
      Tactics.smt_sync' 1 1
    ) end
  else
    begin () end

let id_policy_is_native_call (eq: Envelope.t_Id -> Envelope.t_Id -> bool) (a: Envelope.t_Id) (b: Envelope.t_Id) : Lemma (requires eq == Native.same_id) (ensures eq a b == Native.same_id a b) =
  ()

let copy_policy_is_native_call (copy: fact -> fact) (item: fact) : Lemma (requires copy == Native.copy_fact) (ensures copy item == Native.copy_fact item) =
  ()

let fact_policy_is_native_call (same: fact -> fact -> bool) (a: fact) (b: fact) : Lemma (requires same == Native.fact_equal) (ensures same a b == Native.fact_equal a b) =
  ()

let id_before (a: Envelope.t_Id) (b: Envelope.t_Id) : Type0 =
  Prims.l_or (v a.f_peer < v b.f_peer) (Prims.l_and (a.f_peer == b.f_peer) (v a.f_counter < v b.f_counter))

let less_id_is_lexicographic (a: Envelope.t_Id) (b: Envelope.t_Id) : Lemma (ensures Prims.l_and (Native.less_id a b == true <==> id_before a b) (Native.less_id a b == false <==> Prims.l_not (id_before a b))) [SMTPat (Native.less_id a b)] =
  ()

let less_policy_is_native_call (less: Envelope.t_Id -> Envelope.t_Id -> bool) (a: Envelope.t_Id) (b: Envelope.t_Id) : Lemma (requires less == Native.less_id) (ensures less a b == Native.less_id a b) =
  ()

let register_order_policy_is_exact () : Lemma (ensures Prims.l_and (Prims.l_and (Prims.l_and (Native.v_OPS._1._1._1 == Native.identity) (Native.v_OPS._1._1._4 == Native.less_id)) (forall(item: fact). Native.v_OPS._1._1._1 item == item.f_id)) (Nickel.Canonical.strict_order Native.v_OPS._1._1._4)) =
  let graph = Nickel_crdt.Event_layer.graph_ops Native.identity Native.parents Native.same_id Native.less_id Native.copy_fact Native.fact_equal Native.invalid Native.missing in
  Nickel.EventGraph.graph_ops_preserve_callbacks Native.identity Native.parents Native.same_id Native.less_id Native.copy_fact Native.fact_equal Native.invalid Native.missing;
  Nickel.EventGraph.event_ops_preserve_callbacks graph Native.previous Native.forbidden Native.capacity Native.capacity Native.invalid Native.invalid;
  assert (Prims.l_and (Prims.l_and (Native.v_OPS._1 == graph) (graph._1._1 == Native.identity)) (graph._1._4 == Native.less_id)) by (
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.smt_sync' 1 1
  );
  let each_id (item: fact) : Lemma (ensures Native.identity item == item.f_id) = () in
  FStar.Classical.forall_intro each_id;
  assert (Nickel.Canonical.strict_order Native.less_id);
  assert (Prims.l_and (Native.v_OPS._1._1._1 == Native.identity) (Native.v_OPS._1._1._4 == Native.less_id));
  assert (forall(item: fact). Native.v_OPS._1._1._1 item == item.f_id);
  assert (Nickel.Canonical.strict_order Native.v_OPS._1._1._4);
  assert (Prims.l_and (Prims.l_and (Prims.l_and (Native.v_OPS._1._1._1 == Native.identity) (Native.v_OPS._1._1._4 == Native.less_id)) (forall(item: fact). Native.v_OPS._1._1._1 item == item.f_id)) (Nickel.Canonical.strict_order Native.v_OPS._1._1._4)) by (
    Tactics.prune "Nickel_crdt.Register.v_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.prune "Nickel_crdt.Register.identity";
    Tactics.prune "Nickel_crdt.Register.less_id";
    Tactics.smt_sync' 1 1
  )

let register_canonical_values_are_exact () : Lemma (ensures Nickel.Canonical.exact_values Native.v_OPS._1) =
  let graph = Nickel_crdt.Event_layer.graph_ops Native.identity Native.parents Native.same_id Native.less_id Native.copy_fact Native.fact_equal Native.invalid Native.missing in
  Nickel.EventGraph.graph_ops_preserve_callbacks Native.identity Native.parents Native.same_id Native.less_id Native.copy_fact Native.fact_equal Native.invalid Native.missing;
  Nickel.EventGraph.event_ops_preserve_callbacks graph Native.previous Native.forbidden Native.capacity Native.capacity Native.invalid Native.invalid;
  assert (Prims.l_and (Prims.l_and (Prims.l_and (Native.v_OPS._1 == graph) (graph._1._3 == Native.same_id)) (graph._1._5 == Native.copy_fact)) (graph._1._6 == Native.fact_equal)) by (
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.smt_sync' 1 1
  );
  let native_id (a: Envelope.t_Id) (b: Envelope.t_Id) : Lemma (ensures Native.same_id a b == true <==> a == b) = () in
  let each_id (a: Envelope.t_Id) (b: Envelope.t_Id) : Lemma (ensures graph._1._3 a b == true <==> a == b) =
    native_id a b;
    id_policy_is_native_call graph._1._3 a b;
    assert (graph._1._3 a b == true <==> a == b) by (
      Tactics.prune "Nickel_crdt.Register.same_id";
      Tactics.smt_sync' 1 1
    ) in
  let each_copy (item: fact) : Lemma (ensures graph._1._5 item == item) =
    copy_fact_is_exact item;
    copy_policy_is_native_call graph._1._5 item;
    assert (graph._1._5 item == item) by (
      Tactics.prune "Nickel_crdt.Register.copy_fact";
      Tactics.smt_sync' 1 1
    ) in
  let each_same (a: fact) (b: fact) : Lemma (ensures graph._1._6 a b == true <==> a == b) =
    fact_equal_is_whole_value a b;
    fact_policy_is_native_call graph._1._6 a b;
    assert (graph._1._6 a b == true <==> a == b) by (
      Tactics.prune "Nickel_crdt.Register.fact_equal";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_2 each_id;
  FStar.Classical.forall_intro each_copy;
  FStar.Classical.forall_intro_2 each_same;
  assert (Nickel.Canonical.exact_values Native.v_OPS._1) by (
    Tactics.prune "Nickel_crdt.Register.same_id";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.prune "Nickel_crdt.Register.copy_fact";
    Tactics.prune "Nickel_crdt.Register.fact_equal";
    Tactics.smt_sync' 1 1
  )

let appended_facts (before: Native.t_Replica) (offered: fact) (next: Native.t_Replica) : Type0 =
  Prims.l_and (Seq.length (Alloc.Vec.impl_1__as_slice next.f_facts) == Seq.length (Alloc.Vec.impl_1__as_slice before.f_facts) + 1) (forall(item: fact). Nickel.Canonical.present (Alloc.Vec.impl_1__as_slice next.f_facts) item <==> Prims.l_or (Nickel.Canonical.present (Alloc.Vec.impl_1__as_slice before.f_facts) item) (item == offered))

let prepare_appends_exact_fact (before: Native.t_Replica) (offered: fact) : Lemma (ensures forall(next: Native.t_Replica). Native.prepare () before offered == Result.Result_Ok next ==> appended_facts before offered next) [SMTPat (Native.prepare () before offered)] =
  Nickel.Canonical.push_is_exact before.f_facts offered Native.invalid;
  assert (forall(next: Native.t_Replica). Native.prepare () before offered == Result.Result_Ok next ==> appended_facts before offered next) by (
    Tactics.prune "Nickel_crdt.Event_layer.push";
    Tactics.smt_sync' 1 1
  )

let execute_preserves_exact_fact_contents (before: Native.t_Replica) : Lemma (ensures forall(next: Native.t_Replica). Native.execute () before == Result.Result_Ok next ==> Nickel.Canonical.exact_contents (Alloc.Vec.impl_1__as_slice before.f_facts) next.f_facts) [SMTPat (Native.execute () before)] =
  register_canonical_values_are_exact ();
  assert (Nickel.Canonical.exact_values Native.v_OPS._1) by (
    Tactics.prune "Nickel_crdt.Register.v_OPS";
    Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
    Tactics.prune "Nickel_crdt.Event_layer.event_ops";
    Tactics.smt_sync' 1 1
  );
  Nickel.Canonical.canonical_preserves_exact_contents (Alloc.Vec.impl_1__as_slice before.f_facts) Native.v_OPS._1;
  assert (forall(next: Native.t_Replica). Native.execute () before == Result.Result_Ok next ==> Nickel.Canonical.exact_contents (Alloc.Vec.impl_1__as_slice before.f_facts) next.f_facts) by (
    Tactics.prune "Nickel_crdt.Event_layer.canonical";
    Tactics.prune "Nickel_crdt.Register.v_OPS";
    Tactics.smt_sync' 1 1
  )

let planned_adds_exact_fact (before: Native.t_Replica) (offered: fact) : Lemma (ensures forall(next: Native.t_Replica). Native.planned () before offered == Result.Result_Ok (Option.Option_Some next) ==> appended_facts before offered next) [SMTPat (Native.planned () before offered)] =
  shared_success_stages before offered () Native.duplicate Native.validate Native.prepare Native.execute;
  prepare_appends_exact_fact before offered;
  let each_execute (prepared: Native.t_Replica) : Lemma (ensures forall(next: Native.t_Replica). Native.execute () prepared == Result.Result_Ok next ==> Nickel.Canonical.exact_contents (Alloc.Vec.impl_1__as_slice prepared.f_facts) next.f_facts) [SMTPat (Native.execute () prepared)] = execute_preserves_exact_fact_contents prepared in
  assert (forall(next: Native.t_Replica). Native.planned () before offered == Result.Result_Ok (Option.Option_Some next) ==> appended_facts before offered next) by (
    Tactics.prune "Nickel_crdt.Event_shell.plan";
    Tactics.prune "Nickel_crdt.Register.prepare";
    Tactics.prune "Nickel_crdt.Register.execute";
    Tactics.smt_sync' 1 1
  )

let receive_added_retains_exact_facts (before: Native.t_Replica) (offered: fact) : Lemma (ensures forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> appended_facts before offered next) =
  receive_publication_is_exact before offered;
  planned_adds_exact_fact before offered;
  match Native.planned () before offered with | Result.Result_Err _ -> begin assert (forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> appended_facts before offered next) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.smt_sync' 1 1
  ) end | Result.Result_Ok option -> begin match option with | Option.Option_None -> begin assert (forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> appended_facts before offered next) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.smt_sync' 1 1
  ) end | Option.Option_Some candidate -> begin assert (forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> appended_facts before offered next) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.smt_sync' 1 1
  ) end end

let write_counted_retains_exact_facts (before: Native.t_Replica) (key: u64) (value: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) : Lemma (ensures forall(next: Native.t_Replica) (authored: fact). Native.impl_Replica__write before key value == (next, Result.Result_Ok (Option.Option_Some authored)) ==> appended_facts before authored next) =
  write_installs_successful_candidate before key value;
  let each_authored (authored: fact) : Lemma (ensures forall(candidate: Native.t_Replica). Native.planned () before authored == Result.Result_Ok (Option.Option_Some candidate) ==> appended_facts before authored candidate) [SMTPat (Native.planned () before authored)] = planned_adds_exact_fact before authored in
  assert (forall(next: Native.t_Replica) (authored: fact). Native.impl_Replica__write before key value == (next, Result.Result_Ok (Option.Option_Some authored)) ==> appended_facts before authored next) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__write";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.smt_sync' 1 1
  )

let facts_in_id_order (facts: Alloc.Vec.t_Vec fact Alloc.Alloc.t_Global) : Type0 =
  forall(p: usize{v p < Seq.length (Alloc.Vec.impl_1__as_slice facts)}) (q: usize{v q < Seq.length (Alloc.Vec.impl_1__as_slice facts)}). v p < v q ==> id_before (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice facts) p).f_id (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice facts) q).f_id

let policy_order_refines_id_order (facts: Alloc.Vec.t_Vec fact Alloc.Alloc.t_Global) : Lemma (requires Nickel.Canonical.strictly_ordered facts Native.v_OPS._1) (ensures facts_in_id_order facts) =
  register_order_policy_is_exact ();
  let each (p: usize{v p < Seq.length (Alloc.Vec.impl_1__as_slice facts)}) (q: usize{v q < Seq.length (Alloc.Vec.impl_1__as_slice facts)}) : Lemma (requires v p < v q) (ensures id_before (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice facts) p).f_id (Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice facts) q).f_id) =
    Nickel.Canonical.strict_order_at facts Native.v_OPS._1 p q;
    let a = Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice facts) p in
    let b = Rust_primitives.Slice.slice_index (Alloc.Vec.impl_1__as_slice facts) q in
    less_id_is_lexicographic a.f_id b.f_id;
    less_policy_is_native_call Native.v_OPS._1._1._4 a.f_id b.f_id;
    assert (Prims.l_and (Native.v_OPS._1._1._1 a == a.f_id) (Native.v_OPS._1._1._1 b == b.f_id)) by (
      Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
      Tactics.prune "Nickel_crdt.Event_layer.event_ops";
      Tactics.prune "Nickel_crdt.Register.identity";
      Tactics.prune "Nickel_crdt.Register.less_id";
      Tactics.smt_sync' 1 1
    );
    assert (Native.v_OPS._1._1._4 (Native.v_OPS._1._1._1 a) (Native.v_OPS._1._1._1 b) == true) by (
      Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
      Tactics.prune "Nickel_crdt.Event_layer.event_ops";
      Tactics.prune "Nickel_crdt.Register.identity";
      Tactics.prune "Nickel_crdt.Register.less_id";
      Tactics.smt_sync' 1 1
    );
    assert (Native.v_OPS._1._1._4 a.f_id b.f_id == true) by (
      Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
      Tactics.prune "Nickel_crdt.Event_layer.event_ops";
      Tactics.prune "Nickel_crdt.Register.identity";
      Tactics.prune "Nickel_crdt.Register.less_id";
      Tactics.smt_sync' 1 1
    );
    assert (id_before a.f_id b.f_id) by (
      Tactics.prune "Nickel_crdt.Event_layer.graph_ops";
      Tactics.prune "Nickel_crdt.Event_layer.event_ops";
      Tactics.prune "Nickel_crdt.Register.identity";
      Tactics.prune "Nickel_crdt.Register.less_id";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 each)

let execute_orders_fact_history (before: Native.t_Replica) : Lemma (ensures forall(next: Native.t_Replica). Native.execute () before == Result.Result_Ok next ==> facts_in_id_order next.f_facts) [SMTPat (Native.execute () before)] =
  register_canonical_values_are_exact ();
  register_order_policy_is_exact ();
  Nickel.Canonical.canonical_outputs_strict_id_order (Alloc.Vec.impl_1__as_slice before.f_facts) Native.v_OPS._1;
  match Nickel_crdt.Event_layer.canonical (Alloc.Vec.impl_1__as_slice before.f_facts) Native.v_OPS._1 with | Result.Result_Ok facts -> begin policy_order_refines_id_order facts;
  assert (forall(next: Native.t_Replica). Native.execute () before == Result.Result_Ok next ==> facts_in_id_order next.f_facts) by (
    Tactics.prune "Nickel_crdt.Event_layer.canonical";
    Tactics.prune "Nickel_crdt.Register.v_OPS";
    Tactics.prune "Nickel_crdt.Register.less_id";
    Tactics.prune "Nickel_crdt.Register.identity";
    Tactics.smt_sync' 1 1
  ) end | Result.Result_Err _ -> begin assert (forall(next: Native.t_Replica). Native.execute () before == Result.Result_Ok next ==> facts_in_id_order next.f_facts) by (
    Tactics.prune "Nickel_crdt.Event_layer.canonical";
    Tactics.prune "Nickel_crdt.Register.v_OPS";
    Tactics.prune "Nickel_crdt.Register.less_id";
    Tactics.prune "Nickel_crdt.Register.identity";
    Tactics.smt_sync' 1 1
  ) end

let planned_orders_fact_history (before: Native.t_Replica) (offered: fact) : Lemma (ensures forall(next: Native.t_Replica). Native.planned () before offered == Result.Result_Ok (Option.Option_Some next) ==> facts_in_id_order next.f_facts) =
  shared_success_stages before offered () Native.duplicate Native.validate Native.prepare Native.execute;
  let each_execute (prepared: Native.t_Replica) : Lemma (ensures forall(next: Native.t_Replica). Native.execute () prepared == Result.Result_Ok next ==> facts_in_id_order next.f_facts) [SMTPat (Native.execute () prepared)] = execute_orders_fact_history prepared in
  assert (forall(next: Native.t_Replica). Native.planned () before offered == Result.Result_Ok (Option.Option_Some next) ==> facts_in_id_order next.f_facts) by (
    Tactics.prune "Nickel_crdt.Event_shell.plan";
    Tactics.prune "Nickel_crdt.Register.prepare";
    Tactics.prune "Nickel_crdt.Register.execute";
    Tactics.smt_sync' 1 1
  )

let receive_added_orders_fact_history (before: Native.t_Replica) (offered: fact) : Lemma (ensures forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> facts_in_id_order next.f_facts) =
  receive_publication_is_exact before offered;
  planned_orders_fact_history before offered;
  match Native.planned () before offered with | Result.Result_Err _ -> begin assert (forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> facts_in_id_order next.f_facts) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.smt_sync' 1 1
  ) end | Result.Result_Ok option -> begin match option with | Option.Option_None -> begin assert (forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> facts_in_id_order next.f_facts) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.smt_sync' 1 1
  ) end | Option.Option_Some candidate -> begin assert (forall(next: Native.t_Replica). Native.impl_Replica__receive before offered == (next, Result.Result_Ok Native.Admission_Added) ==> facts_in_id_order next.f_facts) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.smt_sync' 1 1
  ) end end

let write_counted_orders_fact_history (before: Native.t_Replica) (key: u64) (value: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) : Lemma (ensures forall(next: Native.t_Replica) (authored: fact). Native.impl_Replica__write before key value == (next, Result.Result_Ok (Option.Option_Some authored)) ==> facts_in_id_order next.f_facts) =
  write_installs_successful_candidate before key value;
  FStar.Classical.forall_intro (planned_orders_fact_history before);
  assert (forall(next: Native.t_Replica) (authored: fact). Native.impl_Replica__write before key value == (next, Result.Result_Ok (Option.Option_Some authored)) ==> facts_in_id_order next.f_facts) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__write";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.smt_sync' 1 1
  )