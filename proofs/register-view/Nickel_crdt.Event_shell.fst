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
  | Core_models.Result.Result_Ok hoist26 ->
    if hoist26
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
