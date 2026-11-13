module Nickel_crdt.Register
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Nickel_crdt.Causal in
  ()

type t_Error =
  | Error_Conflict : t_Error
  | Error_Missing : t_Error
  | Error_Invalid : t_Error
  | Error_ClockExhausted : t_Error
  | Error_CounterExhausted : t_Error

type t_Admission =
  | Admission_Added : t_Admission
  | Admission_Duplicate : t_Admission

type t_Write = {
  f_key:u64;
  f_value:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global;
  f_observed:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global;
  f_lamport:u64
}

let impl_13: Core_models.Clone.t_Clone t_Write =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

type t_Replica = {
  f_writer:u64;
  f_next_counter:u64;
  f_initial:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global;
  f_facts:Alloc.Vec.t_Vec (Nickel_crdt.Causal.t_Event t_Write) Alloc.Alloc.t_Global
}

let impl_15: Core_models.Clone.t_Clone t_Replica =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

let bytes_equal (a b: t_Slice u8) : bool =
  if (Core_models.Slice.impl__len #u8 a <: usize) <>. (Core_models.Slice.impl__len #u8 b <: usize)
  then false
  else
    match
      Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
        (Core_models.Slice.impl__len #u8 a <: usize)
        (fun temp_0_ temp_1_ ->
            let _:Prims.unit = temp_0_ in
            let _:usize = temp_1_ in
            true)
        ()
        (fun temp_0_ i ->
            let _:Prims.unit = temp_0_ in
            let i:usize = i in
            if (a.[ i ] <: u8) <>. (b.[ i ] <: u8) <: bool
            then
              Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Ops.Control_flow.ControlFlow_Break false
                <:
                Core_models.Ops.Control_flow.t_ControlFlow bool (Prims.unit & Prims.unit))
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Ops.Control_flow.t_ControlFlow bool (Prims.unit & Prims.unit))
                Prims.unit
            else
              Core_models.Ops.Control_flow.ControlFlow_Continue ()
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Ops.Control_flow.t_ControlFlow bool (Prims.unit & Prims.unit))
                Prims.unit)
      <:
      Core_models.Ops.Control_flow.t_ControlFlow bool Prims.unit
    with
    | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
    | Core_models.Ops.Control_flow.ControlFlow_Continue _ -> true

let write_equal (a b: t_Write) : bool =
  a.f_key =. b.f_key && a.f_lamport =. b.f_lamport &&
  bytes_equal (Alloc.Vec.impl_1__as_slice a.f_value <: t_Slice u8)
    (Alloc.Vec.impl_1__as_slice b.f_value <: t_Slice u8) &&
  bytes_equal (Alloc.Vec.impl_1__as_slice a.f_observed <: t_Slice u8)
    (Alloc.Vec.impl_1__as_slice b.f_observed <: t_Slice u8)

let fact_equal (a b: Nickel_crdt.Causal.t_Event t_Write) : bool =
  Nickel_crdt.Causal.event_equal #t_Write a b write_equal

let identity (f: Nickel_crdt.Causal.t_Event t_Write) : Nickel_crdt.Causal.t_Id =
  f.Nickel_crdt.Causal.f_id

let parents (f: Nickel_crdt.Causal.t_Event t_Write) : t_Slice Nickel_crdt.Causal.t_Id =
  Alloc.Vec.impl_1__as_slice f.Nickel_crdt.Causal.f_after

let same_id (a b: Nickel_crdt.Causal.t_Id) : bool =
  a.Nickel_crdt.Causal.f_peer =. b.Nickel_crdt.Causal.f_peer &&
  a.Nickel_crdt.Causal.f_counter =. b.Nickel_crdt.Causal.f_counter

let less_id (a b: Nickel_crdt.Causal.t_Id) : bool =
  a.Nickel_crdt.Causal.f_peer <. b.Nickel_crdt.Causal.f_peer ||
  a.Nickel_crdt.Causal.f_peer =. b.Nickel_crdt.Causal.f_peer &&
  a.Nickel_crdt.Causal.f_counter <. b.Nickel_crdt.Causal.f_counter

let copy_fact (f: Nickel_crdt.Causal.t_Event t_Write) : Nickel_crdt.Causal.t_Event t_Write =
  Core_models.Clone.f_clone #(Nickel_crdt.Causal.t_Event t_Write) #FStar.Tactics.Typeclasses.solve f

let invalid (_: Prims.unit) : t_Error = Error_Invalid <: t_Error

let missing (_: Prims.unit) : t_Error = Error_Missing <: t_Error

let previous (id: Nickel_crdt.Causal.t_Id) : Core_models.Option.t_Option Nickel_crdt.Causal.t_Id =
  if id.Nickel_crdt.Causal.f_counter >. mk_u64 1
  then
    Core_models.Option.Option_Some
    ({
        Nickel_crdt.Causal.f_peer = id.Nickel_crdt.Causal.f_peer;
        Nickel_crdt.Causal.f_counter = id.Nickel_crdt.Causal.f_counter -! mk_u64 1
      }
      <:
      Nickel_crdt.Causal.t_Id)
    <:
    Core_models.Option.t_Option Nickel_crdt.Causal.t_Id
  else Core_models.Option.Option_None <: Core_models.Option.t_Option Nickel_crdt.Causal.t_Id

let forbidden (ancestor offered: Nickel_crdt.Causal.t_Id) : bool =
  ancestor.Nickel_crdt.Causal.f_peer =. offered.Nickel_crdt.Causal.f_peer &&
  ancestor.Nickel_crdt.Causal.f_counter >=. offered.Nickel_crdt.Causal.f_counter

let v_OPS: ((((Nickel_crdt.Causal.t_Event t_Write -> Nickel_crdt.Causal.t_Id) &
      (Nickel_crdt.Causal.t_Event t_Write -> t_Slice Nickel_crdt.Causal.t_Id) &
      (Nickel_crdt.Causal.t_Id -> Nickel_crdt.Causal.t_Id -> bool) &
      (Nickel_crdt.Causal.t_Id -> Nickel_crdt.Causal.t_Id -> bool) &
      (Nickel_crdt.Causal.t_Event t_Write -> Nickel_crdt.Causal.t_Event t_Write) &
      (Nickel_crdt.Causal.t_Event t_Write -> Nickel_crdt.Causal.t_Event t_Write -> bool)) &
    ((Prims.unit -> t_Error) & (Prims.unit -> t_Error))) &
  ((Nickel_crdt.Causal.t_Id -> Core_models.Option.t_Option Nickel_crdt.Causal.t_Id) &
    (Nickel_crdt.Causal.t_Id -> Nickel_crdt.Causal.t_Id -> bool) &
    ((Prims.unit -> t_Error) & (Prims.unit -> t_Error)))) =
  Nickel_crdt.Event_layer.event_ops #(Nickel_crdt.Causal.t_Event t_Write)
    #Nickel_crdt.Causal.t_Id
    #t_Error
    (Nickel_crdt.Event_layer.graph_ops #(Nickel_crdt.Causal.t_Event t_Write)
        #Nickel_crdt.Causal.t_Id #t_Error identity parents same_id less_id copy_fact fact_equal
        invalid missing
      <:
      (((Nickel_crdt.Causal.t_Event t_Write -> Nickel_crdt.Causal.t_Id) &
          (Nickel_crdt.Causal.t_Event t_Write -> t_Slice Nickel_crdt.Causal.t_Id) &
          (Nickel_crdt.Causal.t_Id -> Nickel_crdt.Causal.t_Id -> bool) &
          (Nickel_crdt.Causal.t_Id -> Nickel_crdt.Causal.t_Id -> bool) &
          (Nickel_crdt.Causal.t_Event t_Write -> Nickel_crdt.Causal.t_Event t_Write) &
          (Nickel_crdt.Causal.t_Event t_Write -> Nickel_crdt.Causal.t_Event t_Write -> bool)) &
        ((Prims.unit -> t_Error) & (Prims.unit -> t_Error))))
    previous
    forbidden
    invalid
    invalid

/// Strict visible-write priority, not the shared writer-first storage order.
let later (a b: Nickel_crdt.Causal.t_Event t_Write) : bool =
  a.Nickel_crdt.Causal.f_payload.f_lamport >. b.Nickel_crdt.Causal.f_payload.f_lamport ||
  a.Nickel_crdt.Causal.f_payload.f_lamport =. b.Nickel_crdt.Causal.f_payload.f_lamport &&
  a.Nickel_crdt.Causal.f_id.Nickel_crdt.Causal.f_peer >.
  b.Nickel_crdt.Causal.f_id.Nickel_crdt.Causal.f_peer

/// Native winner scan. Its semantic domain is valid admitted histories.
/// A successful scan returns an index into this exact input, not a cached value.
let winner (facts: t_Slice (Nickel_crdt.Causal.t_Event t_Write)) (key: u64)
    : Core_models.Option.t_Option usize =
  let found:Core_models.Option.t_Option usize =
    Core_models.Option.Option_None <: Core_models.Option.t_Option usize
  in
  let found:Core_models.Option.t_Option usize =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Core_models.Slice.impl__len #(Nickel_crdt.Causal.t_Event t_Write) facts <: usize)
      (fun found temp_1_ ->
          let found:Core_models.Option.t_Option usize = found in
          let _:usize = temp_1_ in
          true)
      found
      (fun found i ->
          let found:Core_models.Option.t_Option usize = found in
          let i:usize = i in
          if
            (facts.[ i ] <: Nickel_crdt.Causal.t_Event t_Write).Nickel_crdt.Causal.f_payload.f_key =.
            key
            <:
            bool
          then
            match found <: Core_models.Option.t_Option usize with
            | Core_models.Option.Option_None  ->
              Core_models.Option.Option_Some i <: Core_models.Option.t_Option usize
            | Core_models.Option.Option_Some j ->
              if
                (j <.
                  (Core_models.Slice.impl__len #(Nickel_crdt.Causal.t_Event t_Write) facts <: usize)
                  <:
                  bool) &&
                (later (facts.[ i ] <: Nickel_crdt.Causal.t_Event t_Write)
                    (facts.[ j ] <: Nickel_crdt.Causal.t_Event t_Write)
                  <:
                  bool)
              then
                let found:Core_models.Option.t_Option usize =
                  Core_models.Option.Option_Some i <: Core_models.Option.t_Option usize
                in
                found
              else found
          else found)
  in
  found

let read_history
      (facts: t_Slice (Nickel_crdt.Causal.t_Event t_Write))
      (initial: t_Slice u8)
      (key: u64)
    : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  match winner facts key <: Core_models.Option.t_Option usize with
  | Core_models.Option.Option_None  -> Alloc.Slice.impl__to_vec #u8 initial
  | Core_models.Option.Option_Some i ->
    if i <. (Core_models.Slice.impl__len #(Nickel_crdt.Causal.t_Event t_Write) facts <: usize)
    then
      Core_models.Clone.f_clone #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        #FStar.Tactics.Typeclasses.solve
        (facts.[ i ] <: Nickel_crdt.Causal.t_Event t_Write).Nickel_crdt.Causal.f_payload.f_value
    else Alloc.Slice.impl__to_vec #u8 initial

/// Every replicated fact advances logical time, even a write to another key.
let next_lamport (facts: t_Slice (Nickel_crdt.Causal.t_Event t_Write))
    : Core_models.Result.t_Result u64 t_Error =
  let highest:u64 = mk_u64 0 in
  let highest:u64 =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Core_models.Slice.impl__len #(Nickel_crdt.Causal.t_Event t_Write) facts <: usize)
      (fun highest temp_1_ ->
          let highest:u64 = highest in
          let _:usize = temp_1_ in
          true)
      highest
      (fun highest i ->
          let highest:u64 = highest in
          let i:usize = i in
          let fact:Nickel_crdt.Causal.t_Event t_Write = facts.[ i ] in
          if fact.Nickel_crdt.Causal.f_payload.f_lamport >. highest
          then
            let highest:u64 = fact.Nickel_crdt.Causal.f_payload.f_lamport in
            highest
          else highest)
  in
  Core_models.Option.impl__ok_or #u64
    #t_Error
    (Core_models.Num.impl_u64__checked_add highest (mk_u64 1) <: Core_models.Option.t_Option u64)
    (Error_ClockExhausted <: t_Error)

let impl_Replica__new (writer: u64) (initial: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
    : Core_models.Result.t_Result t_Replica t_Error =
  Core_models.Result.Result_Ok
  ({
      f_writer = writer;
      f_next_counter = mk_u64 1;
      f_initial = initial;
      f_facts = Alloc.Vec.impl__new #(Nickel_crdt.Causal.t_Event t_Write) ()
    }
    <:
    t_Replica)
  <:
  Core_models.Result.t_Result t_Replica t_Error

let impl_Replica__read (self: t_Replica) (key: u64) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  read_history (Alloc.Vec.impl_1__as_slice self.f_facts
      <:
      t_Slice (Nickel_crdt.Causal.t_Event t_Write))
    (Alloc.Vec.impl_1__as_slice self.f_initial <: t_Slice u8)
    key

let duplicate (_: Prims.unit) (before: t_Replica) (fact: Nickel_crdt.Causal.t_Event t_Write)
    : Core_models.Result.t_Result bool t_Error =
  match
    Nickel_crdt.Event_layer.classify #(Nickel_crdt.Causal.t_Event t_Write)
      #Nickel_crdt.Causal.t_Id
      #t_Error
      (Alloc.Vec.impl_1__as_slice before.f_facts <: t_Slice (Nickel_crdt.Causal.t_Event t_Write))
      fact
      v_OPS._1
    <:
    Core_models.Option.t_Option bool
  with
  | Core_models.Option.Option_None  ->
    Core_models.Result.Result_Ok false <: Core_models.Result.t_Result bool t_Error
  | Core_models.Option.Option_Some true ->
    Core_models.Result.Result_Ok true <: Core_models.Result.t_Result bool t_Error
  | Core_models.Option.Option_Some false ->
    Core_models.Result.Result_Err (Error_Conflict <: t_Error)
    <:
    Core_models.Result.t_Result bool t_Error

let validate (_: Prims.unit) (before: t_Replica) (fact: Nickel_crdt.Causal.t_Event t_Write)
    : Core_models.Result.t_Result Prims.unit t_Error =
  if fact.Nickel_crdt.Causal.f_id.Nickel_crdt.Causal.f_counter =. mk_u64 0
  then
    Core_models.Result.Result_Err (Error_Invalid <: t_Error)
    <:
    Core_models.Result.t_Result Prims.unit t_Error
  else
    match
      Nickel_crdt.Event_layer.validate_event #(Nickel_crdt.Causal.t_Event t_Write)
        #Nickel_crdt.Causal.t_Id
        #t_Error
        (Alloc.Vec.impl_1__as_slice before.f_facts <: t_Slice (Nickel_crdt.Causal.t_Event t_Write))
        fact
        v_OPS
      <:
      Core_models.Result.t_Result (Alloc.Vec.t_Vec Nickel_crdt.Causal.t_Id Alloc.Alloc.t_Global)
        t_Error
    with
    | Core_models.Result.Result_Ok selected ->
      (match
          Nickel_crdt.Event_layer.select_basis #(Nickel_crdt.Causal.t_Event t_Write)
            #Nickel_crdt.Causal.t_Id
            #t_Error
            (Alloc.Vec.impl_1__as_slice before.f_facts
              <:
              t_Slice (Nickel_crdt.Causal.t_Event t_Write))
            (Alloc.Vec.impl_1__as_slice selected <: t_Slice Nickel_crdt.Causal.t_Id)
            v_OPS._1
          <:
          Core_models.Result.t_Result
            (Alloc.Vec.t_Vec (Nickel_crdt.Causal.t_Event t_Write) Alloc.Alloc.t_Global) t_Error
        with
        | Core_models.Result.Result_Ok basis ->
          if
            ~.(bytes_equal (Alloc.Vec.impl_1__as_slice fact.Nickel_crdt.Causal.f_payload.f_observed
                  <:
                  t_Slice u8)
                (Alloc.Vec.impl_1__as_slice (read_history (Alloc.Vec.impl_1__as_slice basis
                          <:
                          t_Slice (Nickel_crdt.Causal.t_Event t_Write))
                        (Alloc.Vec.impl_1__as_slice before.f_initial <: t_Slice u8)
                        fact.Nickel_crdt.Causal.f_payload.f_key
                      <:
                      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                  <:
                  t_Slice u8)
              <:
              bool) ||
            bytes_equal (Alloc.Vec.impl_1__as_slice fact.Nickel_crdt.Causal.f_payload.f_value
                <:
                t_Slice u8)
              (Alloc.Vec.impl_1__as_slice fact.Nickel_crdt.Causal.f_payload.f_observed <: t_Slice u8
              )
          then
            Core_models.Result.Result_Err (Error_Invalid <: t_Error)
            <:
            Core_models.Result.t_Result Prims.unit t_Error
          else
            (match
                next_lamport (Alloc.Vec.impl_1__as_slice basis
                    <:
                    t_Slice (Nickel_crdt.Causal.t_Event t_Write))
                <:
                Core_models.Result.t_Result u64 t_Error
              with
              | Core_models.Result.Result_Ok hoist36 ->
                if fact.Nickel_crdt.Causal.f_payload.f_lamport <>. hoist36
                then
                  Core_models.Result.Result_Err (Error_Invalid <: t_Error)
                  <:
                  Core_models.Result.t_Result Prims.unit t_Error
                else
                  Core_models.Result.Result_Ok (() <: Prims.unit)
                  <:
                  Core_models.Result.t_Result Prims.unit t_Error
              | Core_models.Result.Result_Err err ->
                Core_models.Result.Result_Err err <: Core_models.Result.t_Result Prims.unit t_Error)
        | Core_models.Result.Result_Err err ->
          Core_models.Result.Result_Err err <: Core_models.Result.t_Result Prims.unit t_Error)
    | Core_models.Result.Result_Err err ->
      Core_models.Result.Result_Err err <: Core_models.Result.t_Result Prims.unit t_Error

let prepare (_: Prims.unit) (next: t_Replica) (fact: Nickel_crdt.Causal.t_Event t_Write)
    : Core_models.Result.t_Result t_Replica t_Error =
  let
  (tmp0: Alloc.Vec.t_Vec (Nickel_crdt.Causal.t_Event t_Write) Alloc.Alloc.t_Global),
  (out: Core_models.Result.t_Result Prims.unit t_Error) =
    Nickel_crdt.Event_layer.push #(Nickel_crdt.Causal.t_Event t_Write)
      #t_Error
      next.f_facts
      (Core_models.Clone.f_clone #(Nickel_crdt.Causal.t_Event t_Write)
          #FStar.Tactics.Typeclasses.solve
          fact
        <:
        Nickel_crdt.Causal.t_Event t_Write)
      invalid
  in
  let next:t_Replica = { next with f_facts = tmp0 } <: t_Replica in
  match out <: Core_models.Result.t_Result Prims.unit t_Error with
  | Core_models.Result.Result_Ok _ ->
    Core_models.Result.Result_Ok next <: Core_models.Result.t_Result t_Replica t_Error
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err <: Core_models.Result.t_Result t_Replica t_Error

let execute (_: Prims.unit) (next: t_Replica) : Core_models.Result.t_Result t_Replica t_Error =
  match
    Nickel_crdt.Event_layer.canonical #(Nickel_crdt.Causal.t_Event t_Write)
      #Nickel_crdt.Causal.t_Id
      #t_Error
      (Alloc.Vec.impl_1__as_slice next.f_facts <: t_Slice (Nickel_crdt.Causal.t_Event t_Write))
      v_OPS._1
    <:
    Core_models.Result.t_Result
      (Alloc.Vec.t_Vec (Nickel_crdt.Causal.t_Event t_Write) Alloc.Alloc.t_Global) t_Error
  with
  | Core_models.Result.Result_Ok hoist40 ->
    let next:t_Replica = { next with f_facts = hoist40 } <: t_Replica in
    Core_models.Result.Result_Ok next <: Core_models.Result.t_Result t_Replica t_Error
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err <: Core_models.Result.t_Result t_Replica t_Error

let planned (_: Prims.unit) (before: t_Replica) (fact: Nickel_crdt.Causal.t_Event t_Write)
    : Core_models.Result.t_Result (Core_models.Option.t_Option t_Replica) t_Error =
  Nickel_crdt.Event_shell.plan #t_Replica #(Nickel_crdt.Causal.t_Event t_Write) #Prims.unit #t_Error
    before fact (() <: Prims.unit) duplicate validate prepare execute

/// Duplicate before payload validation. Only a successful detached plan
/// publishes, through the same shell used by the actual text engine.
let impl_Replica__receive (self: t_Replica) (fact: Nickel_crdt.Causal.t_Event t_Write)
    : (t_Replica & Core_models.Result.t_Result t_Admission t_Error) =
  let (tmp0: t_Replica), (out: Core_models.Result.t_Result t_Admission t_Error) =
    Nickel_crdt.Event_shell.receive_into #t_Replica #(Nickel_crdt.Causal.t_Event t_Write) #t_Error
      #t_Admission #Prims.unit self fact (() <: Prims.unit) planned (Admission_Added <: t_Admission)
      (Admission_Duplicate <: t_Admission)
  in
  let self:t_Replica = tmp0 in
  let hax_temp_output:Core_models.Result.t_Result t_Admission t_Error = out in
  self, hax_temp_output <: (t_Replica & Core_models.Result.t_Result t_Admission t_Error)

/// None is an equal-to-observed no-edit: no event, counter or facts change.
let impl_Replica__write
      (self: t_Replica)
      (key: u64)
      (value: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
    : (t_Replica &
      Core_models.Result.t_Result (Core_models.Option.t_Option (Nickel_crdt.Causal.t_Event t_Write))
        t_Error) =
  let observed:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = impl_Replica__read self key in
  if
    bytes_equal (Alloc.Vec.impl_1__as_slice value <: t_Slice u8)
      (Alloc.Vec.impl_1__as_slice observed <: t_Slice u8)
  then
    self,
    (Core_models.Result.Result_Ok
      (Core_models.Option.Option_None
        <:
        Core_models.Option.t_Option (Nickel_crdt.Causal.t_Event t_Write))
      <:
      Core_models.Result.t_Result (Core_models.Option.t_Option (Nickel_crdt.Causal.t_Event t_Write))
        t_Error)
    <:
    (t_Replica &
      Core_models.Result.t_Result (Core_models.Option.t_Option (Nickel_crdt.Causal.t_Event t_Write))
        t_Error)
  else
    match
      Core_models.Option.impl__ok_or #u64
        #t_Error
        (Core_models.Num.impl_u64__checked_add self.f_next_counter (mk_u64 1)
          <:
          Core_models.Option.t_Option u64)
        (Error_CounterExhausted <: t_Error)
      <:
      Core_models.Result.t_Result u64 t_Error
    with
    | Core_models.Result.Result_Ok next ->
      (match
          Nickel_crdt.Event_layer.frontier #(Nickel_crdt.Causal.t_Event t_Write)
            #Nickel_crdt.Causal.t_Id
            #t_Error
            (Alloc.Vec.impl_1__as_slice self.f_facts <: t_Slice (Nickel_crdt.Causal.t_Event t_Write)
            )
            v_OPS._1
          <:
          Core_models.Result.t_Result (Alloc.Vec.t_Vec Nickel_crdt.Causal.t_Id Alloc.Alloc.t_Global)
            t_Error
        with
        | Core_models.Result.Result_Ok hoist31 ->
          (match
              next_lamport (Alloc.Vec.impl_1__as_slice self.f_facts
                  <:
                  t_Slice (Nickel_crdt.Causal.t_Event t_Write))
              <:
              Core_models.Result.t_Result u64 t_Error
            with
            | Core_models.Result.Result_Ok hoist29 ->
              let fact:Nickel_crdt.Causal.t_Event t_Write =
                {
                  Nickel_crdt.Causal.f_id
                  =
                  {
                    Nickel_crdt.Causal.f_peer = self.f_writer;
                    Nickel_crdt.Causal.f_counter = self.f_next_counter
                  }
                  <:
                  Nickel_crdt.Causal.t_Id;
                  Nickel_crdt.Causal.f_after = hoist31;
                  Nickel_crdt.Causal.f_payload
                  =
                  { f_key = key; f_value = value; f_observed = observed; f_lamport = hoist29 }
                  <:
                  t_Write
                }
                <:
                Nickel_crdt.Causal.t_Event t_Write
              in
              let candidate:t_Replica =
                Core_models.Clone.f_clone #t_Replica #FStar.Tactics.Typeclasses.solve self
              in
              let (tmp0: t_Replica), (out: Core_models.Result.t_Result t_Admission t_Error) =
                impl_Replica__receive candidate
                  (Core_models.Clone.f_clone #(Nickel_crdt.Causal.t_Event t_Write)
                      #FStar.Tactics.Typeclasses.solve
                      fact
                    <:
                    Nickel_crdt.Causal.t_Event t_Write)
              in
              let candidate:t_Replica = tmp0 in
              (match out <: Core_models.Result.t_Result t_Admission t_Error with
                | Core_models.Result.Result_Ok hoist33 ->
                  let
                  ((candidate: t_Replica), (self: t_Replica)),
                  (hax_temp_output:
                    Core_models.Result.t_Result
                      (Core_models.Option.t_Option (Nickel_crdt.Causal.t_Event t_Write)) t_Error) =
                    match hoist33 <: t_Admission with
                    | Admission_Duplicate  ->
                      (candidate, self <: (t_Replica & t_Replica)),
                      (Core_models.Result.Result_Err (Error_Conflict <: t_Error)
                        <:
                        Core_models.Result.t_Result
                          (Core_models.Option.t_Option (Nickel_crdt.Causal.t_Event t_Write)) t_Error
                      )
                      <:
                      ((t_Replica & t_Replica) &
                        Core_models.Result.t_Result
                          (Core_models.Option.t_Option (Nickel_crdt.Causal.t_Event t_Write)) t_Error
                      )
                    | Admission_Added  ->
                      let candidate:t_Replica =
                        { candidate with f_next_counter = next } <: t_Replica
                      in
                      let self:t_Replica = candidate in
                      (candidate, self <: (t_Replica & t_Replica)),
                      (Core_models.Result.Result_Ok
                        (Core_models.Option.Option_Some fact
                          <:
                          Core_models.Option.t_Option (Nickel_crdt.Causal.t_Event t_Write))
                        <:
                        Core_models.Result.t_Result
                          (Core_models.Option.t_Option (Nickel_crdt.Causal.t_Event t_Write)) t_Error
                      )
                      <:
                      ((t_Replica & t_Replica) &
                        Core_models.Result.t_Result
                          (Core_models.Option.t_Option (Nickel_crdt.Causal.t_Event t_Write)) t_Error
                      )
                  in
                  self, hax_temp_output
                  <:
                  (t_Replica &
                    Core_models.Result.t_Result
                      (Core_models.Option.t_Option (Nickel_crdt.Causal.t_Event t_Write)) t_Error)
                | Core_models.Result.Result_Err err ->
                  self,
                  (Core_models.Result.Result_Err err
                    <:
                    Core_models.Result.t_Result
                      (Core_models.Option.t_Option (Nickel_crdt.Causal.t_Event t_Write)) t_Error)
                  <:
                  (t_Replica &
                    Core_models.Result.t_Result
                      (Core_models.Option.t_Option (Nickel_crdt.Causal.t_Event t_Write)) t_Error))
            | Core_models.Result.Result_Err err ->
              self,
              (Core_models.Result.Result_Err err
                <:
                Core_models.Result.t_Result
                  (Core_models.Option.t_Option (Nickel_crdt.Causal.t_Event t_Write)) t_Error)
              <:
              (t_Replica &
                Core_models.Result.t_Result
                  (Core_models.Option.t_Option (Nickel_crdt.Causal.t_Event t_Write)) t_Error))
        | Core_models.Result.Result_Err err ->
          self,
          (Core_models.Result.Result_Err err
            <:
            Core_models.Result.t_Result
              (Core_models.Option.t_Option (Nickel_crdt.Causal.t_Event t_Write)) t_Error)
          <:
          (t_Replica &
            Core_models.Result.t_Result
              (Core_models.Option.t_Option (Nickel_crdt.Causal.t_Event t_Write)) t_Error))
    | Core_models.Result.Result_Err err ->
      self,
      (Core_models.Result.Result_Err err
        <:
        Core_models.Result.t_Result
          (Core_models.Option.t_Option (Nickel_crdt.Causal.t_Event t_Write)) t_Error)
      <:
      (t_Replica &
        Core_models.Result.t_Result
          (Core_models.Option.t_Option (Nickel_crdt.Causal.t_Event t_Write)) t_Error)
