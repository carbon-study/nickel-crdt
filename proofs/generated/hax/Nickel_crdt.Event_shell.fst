module Nickel_crdt.Event_shell
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// Calculate a detached candidate before the caller chooses to publish it.
/// Duplicate detection precedes validation and candidate construction.
let plan
      (#v_R #v_F #v_C #v_E: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_R)
      (before: v_R)
      (fact: v_F)
      (context: v_C)
      (duplicate: (v_C -> v_R -> v_F -> Core_models.Result.t_Result bool v_E))
      (validate: (v_C -> v_R -> v_F -> Core_models.Result.t_Result Prims.unit v_E))
      (prepare: (v_C -> v_R -> v_F -> Core_models.Result.t_Result v_R v_E))
      (execute: (v_C -> v_R -> Core_models.Result.t_Result v_R v_E))
    : Core_models.Result.t_Result (Core_models.Option.t_Option v_R) v_E =
  match duplicate context before fact <: Core_models.Result.t_Result bool v_E with
  | Core_models.Result.Result_Ok hoist91 ->
    if hoist91
    then
      Core_models.Result.Result_Ok
      (Core_models.Option.Option_None <: Core_models.Option.t_Option v_R)
      <:
      Core_models.Result.t_Result (Core_models.Option.t_Option v_R) v_E
    else
      (match validate context before fact <: Core_models.Result.t_Result Prims.unit v_E with
        | Core_models.Result.Result_Ok _ ->
          let next:v_R = Core_models.Clone.f_clone #v_R #FStar.Tactics.Typeclasses.solve before in
          (match prepare context next fact <: Core_models.Result.t_Result v_R v_E with
            | Core_models.Result.Result_Ok next ->
              (match execute context next <: Core_models.Result.t_Result v_R v_E with
                | Core_models.Result.Result_Ok next ->
                  Core_models.Result.Result_Ok
                  (Core_models.Option.Option_Some next <: Core_models.Option.t_Option v_R)
                  <:
                  Core_models.Result.t_Result (Core_models.Option.t_Option v_R) v_E
                | Core_models.Result.Result_Err err ->
                  Core_models.Result.Result_Err err
                  <:
                  Core_models.Result.t_Result (Core_models.Option.t_Option v_R) v_E)
            | Core_models.Result.Result_Err err ->
              Core_models.Result.Result_Err err
              <:
              Core_models.Result.t_Result (Core_models.Option.t_Option v_R) v_E)
        | Core_models.Result.Result_Err err ->
          Core_models.Result.Result_Err err
          <:
          Core_models.Result.t_Result (Core_models.Option.t_Option v_R) v_E)
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err
    <:
    Core_models.Result.t_Result (Core_models.Option.t_Option v_R) v_E

/// Publish exactly a successful candidate; errors and duplicates do not assign.
let receive_into
      (#v_R #v_F #v_E #v_A #v_C: Type0)
      (state: v_R)
      (fact: v_F)
      (context: v_C)
      (plan:
          (v_C -> v_R -> v_F -> Core_models.Result.t_Result (Core_models.Option.t_Option v_R) v_E))
      (added duplicate: v_A)
    : (v_R & Core_models.Result.t_Result v_A v_E) =
  let (state: v_R), (hax_temp_output: Core_models.Result.t_Result v_A v_E) =
    match
      plan context state fact <: Core_models.Result.t_Result (Core_models.Option.t_Option v_R) v_E
    with
    | Core_models.Result.Result_Err error ->
      state, (Core_models.Result.Result_Err error <: Core_models.Result.t_Result v_A v_E)
      <:
      (v_R & Core_models.Result.t_Result v_A v_E)
    | Core_models.Result.Result_Ok (Core_models.Option.Option_None ) ->
      state, (Core_models.Result.Result_Ok duplicate <: Core_models.Result.t_Result v_A v_E)
      <:
      (v_R & Core_models.Result.t_Result v_A v_E)
    | Core_models.Result.Result_Ok (Core_models.Option.Option_Some next) ->
      let state:v_R = next in
      state, (Core_models.Result.Result_Ok added <: Core_models.Result.t_Result v_A v_E)
      <:
      (v_R & Core_models.Result.t_Result v_A v_E)
  in
  state, hax_temp_output <: (v_R & Core_models.Result.t_Result v_A v_E)

/// Owned-state adapter around the same publication boundary.
let receive
      (#v_R #v_F #v_E #v_A #v_C: Type0)
      (state: v_R)
      (fact: v_F)
      (context: v_C)
      (plan:
          (v_C -> v_R -> v_F -> Core_models.Result.t_Result (Core_models.Option.t_Option v_R) v_E))
      (added duplicate: v_A)
    : (v_R & Core_models.Result.t_Result v_A v_E) =
  let (tmp0: v_R), (out: Core_models.Result.t_Result v_A v_E) =
    receive_into #v_R #v_F #v_E #v_A #v_C state fact context plan added duplicate
  in
  let state:v_R = tmp0 in
  let result:Core_models.Result.t_Result v_A v_E = out in
  state, result <: (v_R & Core_models.Result.t_Result v_A v_E)

/// Replay one chosen event per iteration, retaining its operation result for
/// later callbacks and returning the actual completion vector.
let scheduled
      (#v_F #v_I #v_S #v_O #v_E #v_C: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_I)
      (facts: t_Slice v_F)
      (initial: v_S)
      (context: v_C)
      (id: (v_F -> v_I))
      (choose: (v_C -> t_Slice v_F -> t_Slice v_I -> Core_models.Option.t_Option usize))
      (apply:
          (v_C -> t_Slice v_F -> v_F -> t_Slice (v_I & v_O) -> v_S
              -> Core_models.Result.t_Result (v_S & v_O) v_E))
      (internal: (Prims.unit -> v_E))
    : Core_models.Result.t_Result (v_S & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E =
  let result:v_S = initial in
  let (done: Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global):Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global =
    Alloc.Vec.impl__new #v_I ()
  in
  let (operations: Alloc.Vec.t_Vec (v_I & v_O) Alloc.Alloc.t_Global):Alloc.Vec.t_Vec (v_I & v_O)
    Alloc.Alloc.t_Global =
    Alloc.Vec.impl__new #(v_I & v_O) ()
  in
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
      (Core_models.Slice.impl__len #v_F facts <: usize)
      (fun temp_0_ temp_1_ ->
          let
          (done: Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global),
          (operations: Alloc.Vec.t_Vec (v_I & v_O) Alloc.Alloc.t_Global),
          (result: v_S) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (done, operations, result
        <:
        (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global & Alloc.Vec.t_Vec (v_I & v_O) Alloc.Alloc.t_Global &
          v_S))
      (fun temp_0_ temp_1_ ->
          let
          (done: Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global),
          (operations: Alloc.Vec.t_Vec (v_I & v_O) Alloc.Alloc.t_Global),
          (result: v_S) =
            temp_0_
          in
          let _:usize = temp_1_ in
          match
            Core_models.Option.impl__ok_or #usize
              #v_E
              (choose context facts (Alloc.Vec.impl_1__as_slice done <: t_Slice v_I))
              (internal ())
            <:
            Core_models.Result.t_Result usize v_E
          with
          | Core_models.Result.Result_Ok index ->
            if index >=. (Core_models.Slice.impl__len #v_F facts <: usize) <: bool
            then
              Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Ops.Control_flow.ControlFlow_Break
                (Core_models.Result.Result_Err (internal ())
                  <:
                  Core_models.Result.t_Result (v_S & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result (v_S & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                  (Prims.unit &
                    (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global &
                      Alloc.Vec.t_Vec (v_I & v_O) Alloc.Alloc.t_Global &
                      v_S)))
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result (v_S & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global)
                        v_E)
                    (Prims.unit &
                      (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global &
                        Alloc.Vec.t_Vec (v_I & v_O) Alloc.Alloc.t_Global &
                        v_S)))
                (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global &
                  Alloc.Vec.t_Vec (v_I & v_O) Alloc.Alloc.t_Global &
                  v_S)
            else
              let event:v_F = facts.[ index ] in
              (match
                  apply context facts event (Alloc.Vec.impl_1__as_slice operations) result
                  <:
                  Core_models.Result.t_Result (v_S & v_O) v_E
                with
                | Core_models.Result.Result_Ok pair ->
                  let (next: v_S), (ops: v_O) = pair in
                  let result:v_S = next in
                  let event_id:v_I = id event in
                  let
                  (tmp0: Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global),
                  (out: Core_models.Result.t_Result Prims.unit v_E) =
                    Nickel_crdt.Event_layer.push #v_I
                      #v_E
                      done
                      (Core_models.Clone.f_clone #v_I #FStar.Tactics.Typeclasses.solve event_id
                        <:
                        v_I)
                      internal
                  in
                  let done:Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global = tmp0 in
                  (match out <: Core_models.Result.t_Result Prims.unit v_E with
                    | Core_models.Result.Result_Ok _ ->
                      let
                      (tmp0: Alloc.Vec.t_Vec (v_I & v_O) Alloc.Alloc.t_Global),
                      (out: Core_models.Result.t_Result Prims.unit v_E) =
                        Nickel_crdt.Event_layer.push #(v_I & v_O)
                          #v_E
                          operations
                          (event_id, ops <: (v_I & v_O))
                          internal
                      in
                      let operations:Alloc.Vec.t_Vec (v_I & v_O) Alloc.Alloc.t_Global = tmp0 in
                      (match out <: Core_models.Result.t_Result Prims.unit v_E with
                        | Core_models.Result.Result_Ok _ ->
                          Core_models.Ops.Control_flow.ControlFlow_Continue
                          (done, operations, result
                            <:
                            (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global &
                              Alloc.Vec.t_Vec (v_I & v_O) Alloc.Alloc.t_Global &
                              v_S))
                          <:
                          Core_models.Ops.Control_flow.t_ControlFlow
                            (Core_models.Ops.Control_flow.t_ControlFlow
                                (Core_models.Result.t_Result
                                    (v_S & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                                (Prims.unit &
                                  (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global &
                                    Alloc.Vec.t_Vec (v_I & v_O) Alloc.Alloc.t_Global &
                                    v_S)))
                            (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global &
                              Alloc.Vec.t_Vec (v_I & v_O) Alloc.Alloc.t_Global &
                              v_S)
                        | Core_models.Result.Result_Err err ->
                          Core_models.Ops.Control_flow.ControlFlow_Break
                          (Core_models.Ops.Control_flow.ControlFlow_Break
                            (Core_models.Result.Result_Err err
                              <:
                              Core_models.Result.t_Result
                                (v_S & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                            <:
                            Core_models.Ops.Control_flow.t_ControlFlow
                              (Core_models.Result.t_Result
                                  (v_S & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                              (Prims.unit &
                                (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global &
                                  Alloc.Vec.t_Vec (v_I & v_O) Alloc.Alloc.t_Global &
                                  v_S)))
                          <:
                          Core_models.Ops.Control_flow.t_ControlFlow
                            (Core_models.Ops.Control_flow.t_ControlFlow
                                (Core_models.Result.t_Result
                                    (v_S & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                                (Prims.unit &
                                  (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global &
                                    Alloc.Vec.t_Vec (v_I & v_O) Alloc.Alloc.t_Global &
                                    v_S)))
                            (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global &
                              Alloc.Vec.t_Vec (v_I & v_O) Alloc.Alloc.t_Global &
                              v_S))
                    | Core_models.Result.Result_Err err ->
                      Core_models.Ops.Control_flow.ControlFlow_Break
                      (Core_models.Ops.Control_flow.ControlFlow_Break
                        (Core_models.Result.Result_Err err
                          <:
                          Core_models.Result.t_Result
                            (v_S & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                        <:
                        Core_models.Ops.Control_flow.t_ControlFlow
                          (Core_models.Result.t_Result
                              (v_S & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                          (Prims.unit &
                            (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global &
                              Alloc.Vec.t_Vec (v_I & v_O) Alloc.Alloc.t_Global &
                              v_S)))
                      <:
                      Core_models.Ops.Control_flow.t_ControlFlow
                        (Core_models.Ops.Control_flow.t_ControlFlow
                            (Core_models.Result.t_Result
                                (v_S & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                            (Prims.unit &
                              (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global &
                                Alloc.Vec.t_Vec (v_I & v_O) Alloc.Alloc.t_Global &
                                v_S)))
                        (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global &
                          Alloc.Vec.t_Vec (v_I & v_O) Alloc.Alloc.t_Global &
                          v_S))
                | Core_models.Result.Result_Err err ->
                  Core_models.Ops.Control_flow.ControlFlow_Break
                  (Core_models.Ops.Control_flow.ControlFlow_Break
                    (Core_models.Result.Result_Err err
                      <:
                      Core_models.Result.t_Result (v_S & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global)
                        v_E)
                    <:
                    Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Result.t_Result (v_S & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global)
                          v_E)
                      (Prims.unit &
                        (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global &
                          Alloc.Vec.t_Vec (v_I & v_O) Alloc.Alloc.t_Global &
                          v_S)))
                  <:
                  Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Ops.Control_flow.t_ControlFlow
                        (Core_models.Result.t_Result
                            (v_S & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                        (Prims.unit &
                          (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global &
                            Alloc.Vec.t_Vec (v_I & v_O) Alloc.Alloc.t_Global &
                            v_S)))
                    (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global &
                      Alloc.Vec.t_Vec (v_I & v_O) Alloc.Alloc.t_Global &
                      v_S))
          | Core_models.Result.Result_Err err ->
            Core_models.Ops.Control_flow.ControlFlow_Break
            (Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Result.Result_Err err
                <:
                Core_models.Result.t_Result (v_S & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Result.t_Result (v_S & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                (Prims.unit &
                  (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global &
                    Alloc.Vec.t_Vec (v_I & v_O) Alloc.Alloc.t_Global &
                    v_S)))
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result (v_S & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                  (Prims.unit &
                    (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global &
                      Alloc.Vec.t_Vec (v_I & v_O) Alloc.Alloc.t_Global &
                      v_S)))
              (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global &
                Alloc.Vec.t_Vec (v_I & v_O) Alloc.Alloc.t_Global &
                v_S))
    <:
    Core_models.Ops.Control_flow.t_ControlFlow
      (Core_models.Result.t_Result (v_S & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
      (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global & Alloc.Vec.t_Vec (v_I & v_O) Alloc.Alloc.t_Global &
        v_S)
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue (done, operations, result) ->
    Core_models.Result.Result_Ok (result, done <: (v_S & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global))
    <:
    Core_models.Result.t_Result (v_S & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E
