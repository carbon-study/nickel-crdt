module Nickel_crdt.Event_layer
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// Classify the first stored identity match, preserving storage-order behavior.
/// None is a new identity; Some(true) is exact duplicate; Some(false) conflict.
let classify
      (#v_F #v_I: Type0)
      (facts: t_Slice v_F)
      (fact: v_F)
      (id: (v_F -> v_I))
      (id_eq: (v_I -> v_I -> bool))
      (fact_eq: (v_F -> v_F -> bool))
    : Core_models.Option.t_Option bool =
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
      (Core_models.Slice.impl__len #v_F facts <: usize)
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:usize = temp_1_ in
          true)
      ()
      (fun temp_0_ i ->
          let _:Prims.unit = temp_0_ in
          let i:usize = i in
          let old:v_F = facts.[ i ] in
          if id_eq (id old) (id fact)
          then
            Core_models.Ops.Control_flow.ControlFlow_Break
            (Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Option.Option_Some (fact_eq old fact) <: Core_models.Option.t_Option bool
              )
              <:
              Core_models.Ops.Control_flow.t_ControlFlow (Core_models.Option.t_Option bool)
                (Prims.unit & Prims.unit))
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow (Core_models.Option.t_Option bool)
                  (Prims.unit & Prims.unit)) Prims.unit
          else
            Core_models.Ops.Control_flow.ControlFlow_Continue ()
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow (Core_models.Option.t_Option bool)
                  (Prims.unit & Prims.unit)) Prims.unit)
    <:
    Core_models.Ops.Control_flow.t_ControlFlow (Core_models.Option.t_Option bool) Prims.unit
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue _ ->
    Core_models.Option.Option_None <: Core_models.Option.t_Option bool

let push
      (#v_T #v_E: Type0)
      (xs: Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global)
      (value: v_T)
      (internal: (Prims.unit -> v_E))
    : (Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global & Core_models.Result.t_Result Prims.unit v_E) =
  if
    (Alloc.Vec.impl_1__len #v_T #Alloc.Alloc.t_Global xs <: usize) =.
    Core_models.Num.impl_usize__MAX
  then
    xs, (Core_models.Result.Result_Err (internal ()) <: Core_models.Result.t_Result Prims.unit v_E)
    <:
    (Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global & Core_models.Result.t_Result Prims.unit v_E)
  else
    let xs:Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global =
      Alloc.Vec.impl_1__push #v_T #Alloc.Alloc.t_Global xs value
    in
    let hax_temp_output:Core_models.Result.t_Result Prims.unit v_E =
      Core_models.Result.Result_Ok (() <: Prims.unit) <: Core_models.Result.t_Result Prims.unit v_E
    in
    xs, hax_temp_output
    <:
    (Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global & Core_models.Result.t_Result Prims.unit v_E)

let has_id (#v_I: Type0) (ids: t_Slice v_I) (wanted: v_I) (id_eq: (v_I -> v_I -> bool)) : bool =
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
      (Core_models.Slice.impl__len #v_I ids <: usize)
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:usize = temp_1_ in
          true)
      ()
      (fun temp_0_ i ->
          let _:Prims.unit = temp_0_ in
          let i:usize = i in
          if id_eq (ids.[ i ] <: v_I) wanted
          then
            Core_models.Ops.Control_flow.ControlFlow_Break
            (Core_models.Ops.Control_flow.ControlFlow_Break true
              <:
              Core_models.Ops.Control_flow.t_ControlFlow bool (Prims.unit & Prims.unit))
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow bool (Prims.unit & Prims.unit)) Prims.unit
          else
            Core_models.Ops.Control_flow.ControlFlow_Continue ()
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow bool (Prims.unit & Prims.unit)) Prims.unit
      )
    <:
    Core_models.Ops.Control_flow.t_ControlFlow bool Prims.unit
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue _ -> false

let duplicate_ids (#v_I: Type0) (xs: t_Slice v_I) (id_eq: (v_I -> v_I -> bool)) : bool =
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
      (Core_models.Slice.impl__len #v_I xs <: usize)
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:usize = temp_1_ in
          true)
      ()
      (fun temp_0_ i ->
          let _:Prims.unit = temp_0_ in
          let i:usize = i in
          match
            Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
              i
              (fun temp_0_ temp_1_ ->
                  let _:Prims.unit = temp_0_ in
                  let _:usize = temp_1_ in
                  true)
              ()
              (fun temp_0_ j ->
                  let _:Prims.unit = temp_0_ in
                  let j:usize = j in
                  if id_eq (xs.[ i ] <: v_I) (xs.[ j ] <: v_I)
                  then
                    Core_models.Ops.Control_flow.ControlFlow_Break
                    (Core_models.Ops.Control_flow.ControlFlow_Break true
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
          | Core_models.Ops.Control_flow.ControlFlow_Break ret ->
            Core_models.Ops.Control_flow.ControlFlow_Break
            (Core_models.Ops.Control_flow.ControlFlow_Break ret
              <:
              Core_models.Ops.Control_flow.t_ControlFlow bool (Prims.unit & Prims.unit))
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow bool (Prims.unit & Prims.unit)) Prims.unit
          | Core_models.Ops.Control_flow.ControlFlow_Continue loop_res ->
            Core_models.Ops.Control_flow.ControlFlow_Continue loop_res
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow bool (Prims.unit & Prims.unit)) Prims.unit
      )
    <:
    Core_models.Ops.Control_flow.t_ControlFlow bool Prims.unit
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue _ -> false

let has_fact
      (#v_F #v_I: Type0)
      (facts: t_Slice v_F)
      (wanted: v_I)
      (id: (v_F -> v_I))
      (id_eq: (v_I -> v_I -> bool))
    : bool =
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
      (Core_models.Slice.impl__len #v_F facts <: usize)
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:usize = temp_1_ in
          true)
      ()
      (fun temp_0_ i ->
          let _:Prims.unit = temp_0_ in
          let i:usize = i in
          if id_eq (id (facts.[ i ] <: v_F)) wanted
          then
            Core_models.Ops.Control_flow.ControlFlow_Break
            (Core_models.Ops.Control_flow.ControlFlow_Break true
              <:
              Core_models.Ops.Control_flow.t_ControlFlow bool (Prims.unit & Prims.unit))
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow bool (Prims.unit & Prims.unit)) Prims.unit
          else
            Core_models.Ops.Control_flow.ControlFlow_Continue ()
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow bool (Prims.unit & Prims.unit)) Prims.unit
      )
    <:
    Core_models.Ops.Control_flow.t_ControlFlow bool Prims.unit
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue _ -> false

let validate_after
      (#v_F #v_I #v_E: Type0)
      (facts: t_Slice v_F)
      (after: t_Slice v_I)
      (id: (v_F -> v_I))
      (id_eq: (v_I -> v_I -> bool))
      (missing: (Prims.unit -> v_E))
    : Core_models.Result.t_Result Prims.unit v_E =
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
      (Core_models.Slice.impl__len #v_I after <: usize)
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:usize = temp_1_ in
          true)
      ()
      (fun temp_0_ i ->
          let _:Prims.unit = temp_0_ in
          let i:usize = i in
          if ~.(has_fact #v_F #v_I facts (after.[ i ] <: v_I) id id_eq <: bool) <: bool
          then
            Core_models.Ops.Control_flow.ControlFlow_Break
            (Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Result.Result_Err (missing ())
                <:
                Core_models.Result.t_Result Prims.unit v_E)
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Result.t_Result Prims.unit v_E) (Prims.unit & Prims.unit))
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result Prims.unit v_E) (Prims.unit & Prims.unit)) Prims.unit
          else
            Core_models.Ops.Control_flow.ControlFlow_Continue ()
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result Prims.unit v_E) (Prims.unit & Prims.unit)) Prims.unit
      )
    <:
    Core_models.Ops.Control_flow.t_ControlFlow (Core_models.Result.t_Result Prims.unit v_E)
      Prims.unit
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue _ ->
    Core_models.Result.Result_Ok (() <: Prims.unit) <: Core_models.Result.t_Result Prims.unit v_E

let extend_past
      (#v_F #v_I #v_E: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_I)
      (fact: v_F)
      (selected: Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global)
      (id: (v_F -> v_I))
      (after: (v_F -> t_Slice v_I))
      (id_eq: (v_I -> v_I -> bool))
      (internal: (Prims.unit -> v_E))
    : Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E =
  if has_id #v_I (Alloc.Vec.impl_1__as_slice selected <: t_Slice v_I) (id fact) id_eq
  then
    match
      Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
        (Core_models.Slice.impl__len #v_I (after fact) <: usize)
        (fun selected temp_1_ ->
            let selected:Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global = selected in
            let _:usize = temp_1_ in
            true)
        selected
        (fun selected i ->
            let selected:Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global = selected in
            let i:usize = i in
            let predecessor:v_I =
              Core_models.Clone.f_clone #v_I
                #FStar.Tactics.Typeclasses.solve
                ((after fact).[ i ] <: v_I)
            in
            if
              ~.(has_id #v_I (Alloc.Vec.impl_1__as_slice selected <: t_Slice v_I) predecessor id_eq
                <:
                bool)
            then
              let
              (tmp0: Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global),
              (out: Core_models.Result.t_Result Prims.unit v_E) =
                push #v_I #v_E selected predecessor internal
              in
              let selected:Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global = tmp0 in
              match out <: Core_models.Result.t_Result Prims.unit v_E with
              | Core_models.Result.Result_Ok _ ->
                Core_models.Ops.Control_flow.ControlFlow_Continue selected
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                      (Prims.unit & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global))
                  (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global)
              | Core_models.Result.Result_Err err ->
                Core_models.Ops.Control_flow.ControlFlow_Break
                (Core_models.Ops.Control_flow.ControlFlow_Break
                  (Core_models.Result.Result_Err err
                    <:
                    Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                  <:
                  Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                    (Prims.unit & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global))
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                      (Prims.unit & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global))
                  (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global)
            else
              Core_models.Ops.Control_flow.ControlFlow_Continue selected
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                    (Prims.unit & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global))
                (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global))
      <:
      Core_models.Ops.Control_flow.t_ControlFlow
        (Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
        (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global)
    with
    | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
    | Core_models.Ops.Control_flow.ControlFlow_Continue selected ->
      Core_models.Result.Result_Ok selected
      <:
      Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E
  else
    Core_models.Result.Result_Ok selected
    <:
    Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E

let past_pass
      (#v_F #v_I #v_E: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_I)
      (facts: t_Slice v_F)
      (selected: Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global)
      (id: (v_F -> v_I))
      (after: (v_F -> t_Slice v_I))
      (id_eq: (v_I -> v_I -> bool))
      (internal: (Prims.unit -> v_E))
    : Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E =
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
      (Core_models.Slice.impl__len #v_F facts <: usize)
      (fun selected temp_1_ ->
          let selected:Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global = selected in
          let _:usize = temp_1_ in
          true)
      selected
      (fun selected i ->
          let selected:Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global = selected in
          let i:usize = i in
          match
            extend_past #v_F #v_I #v_E (facts.[ i ] <: v_F) selected id after id_eq internal
            <:
            Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E
          with
          | Core_models.Result.Result_Ok hoist76 ->
            Core_models.Ops.Control_flow.ControlFlow_Continue hoist76
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                  (Prims.unit & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global))
              (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global)
          | Core_models.Result.Result_Err err ->
            Core_models.Ops.Control_flow.ControlFlow_Break
            (Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Result.Result_Err err
                <:
                Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                (Prims.unit & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global))
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                  (Prims.unit & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global))
              (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global))
    <:
    Core_models.Ops.Control_flow.t_ControlFlow
      (Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
      (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global)
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue selected ->
    Core_models.Result.Result_Ok selected
    <:
    Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E

let past
      (#v_F #v_I #v_E: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_I)
      (facts: t_Slice v_F)
      (after_ids: t_Slice v_I)
      (id: (v_F -> v_I))
      (after: (v_F -> t_Slice v_I))
      (id_eq: (v_I -> v_I -> bool))
      (internal missing: (Prims.unit -> v_E))
    : Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E =
  let selected:Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global = Alloc.Slice.impl__to_vec #v_I after_ids in
  match
    validate_after #v_F #v_I #v_E facts after_ids id id_eq missing
    <:
    Core_models.Result.t_Result Prims.unit v_E
  with
  | Core_models.Result.Result_Ok _ ->
    (match
        Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
          (Core_models.Slice.impl__len #v_F facts <: usize)
          (fun selected temp_1_ ->
              let selected:Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global = selected in
              let _:usize = temp_1_ in
              true)
          selected
          (fun selected temp_1_ ->
              let selected:Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global = selected in
              let _:usize = temp_1_ in
              match
                past_pass #v_F #v_I #v_E facts selected id after id_eq internal
                <:
                Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E
              with
              | Core_models.Result.Result_Ok hoist77 ->
                Core_models.Ops.Control_flow.ControlFlow_Continue hoist77
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                      (Prims.unit & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global))
                  (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global)
              | Core_models.Result.Result_Err err ->
                Core_models.Ops.Control_flow.ControlFlow_Break
                (Core_models.Ops.Control_flow.ControlFlow_Break
                  (Core_models.Result.Result_Err err
                    <:
                    Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                  <:
                  Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                    (Prims.unit & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global))
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                      (Prims.unit & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global))
                  (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global))
        <:
        Core_models.Ops.Control_flow.t_ControlFlow
          (Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
          (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global)
      with
      | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
      | Core_models.Ops.Control_flow.ControlFlow_Continue selected ->
        Core_models.Result.Result_Ok selected
        <:
        Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err
    <:
    Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E

let choose_unseen
      (#v_F #v_I #v_E: Type0)
      (facts out: t_Slice v_F)
      (id: (v_F -> v_I))
      (id_eq id_lt: (v_I -> v_I -> bool))
      (internal: (Prims.unit -> v_E))
    : Core_models.Result.t_Result (Core_models.Option.t_Option usize) v_E =
  let chosen:Core_models.Option.t_Option usize =
    Core_models.Option.Option_None <: Core_models.Option.t_Option usize
  in
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
      (Core_models.Slice.impl__len #v_F facts <: usize)
      (fun chosen temp_1_ ->
          let chosen:Core_models.Option.t_Option usize = chosen in
          let _:usize = temp_1_ in
          true)
      chosen
      (fun chosen j ->
          let chosen:Core_models.Option.t_Option usize = chosen in
          let j:usize = j in
          if ~.(has_fact #v_F #v_I out (id (facts.[ j ] <: v_F)) id id_eq <: bool) <: bool
          then
            match chosen <: Core_models.Option.t_Option usize with
            | Core_models.Option.Option_None  ->
              Core_models.Ops.Control_flow.ControlFlow_Continue
              (Core_models.Option.Option_Some j <: Core_models.Option.t_Option usize)
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result (Core_models.Option.t_Option usize) v_E)
                    (Prims.unit & Core_models.Option.t_Option usize))
                (Core_models.Option.t_Option usize)
            | Core_models.Option.Option_Some k ->
              if k >=. (Core_models.Slice.impl__len #v_F facts <: usize) <: bool
              then
                Core_models.Ops.Control_flow.ControlFlow_Break
                (Core_models.Ops.Control_flow.ControlFlow_Break
                  (Core_models.Result.Result_Err (internal ())
                    <:
                    Core_models.Result.t_Result (Core_models.Option.t_Option usize) v_E)
                  <:
                  Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result (Core_models.Option.t_Option usize) v_E)
                    (Prims.unit & Core_models.Option.t_Option usize))
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Result.t_Result (Core_models.Option.t_Option usize) v_E)
                      (Prims.unit & Core_models.Option.t_Option usize))
                  (Core_models.Option.t_Option usize)
              else
                if id_lt (id (facts.[ j ] <: v_F)) (id (facts.[ k ] <: v_F))
                then
                  let chosen:Core_models.Option.t_Option usize =
                    Core_models.Option.Option_Some j <: Core_models.Option.t_Option usize
                  in
                  Core_models.Ops.Control_flow.ControlFlow_Continue chosen
                  <:
                  Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Ops.Control_flow.t_ControlFlow
                        (Core_models.Result.t_Result (Core_models.Option.t_Option usize) v_E)
                        (Prims.unit & Core_models.Option.t_Option usize))
                    (Core_models.Option.t_Option usize)
                else
                  Core_models.Ops.Control_flow.ControlFlow_Continue chosen
                  <:
                  Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Ops.Control_flow.t_ControlFlow
                        (Core_models.Result.t_Result (Core_models.Option.t_Option usize) v_E)
                        (Prims.unit & Core_models.Option.t_Option usize))
                    (Core_models.Option.t_Option usize)
          else
            Core_models.Ops.Control_flow.ControlFlow_Continue chosen
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result (Core_models.Option.t_Option usize) v_E)
                  (Prims.unit & Core_models.Option.t_Option usize))
              (Core_models.Option.t_Option usize))
    <:
    Core_models.Ops.Control_flow.t_ControlFlow
      (Core_models.Result.t_Result (Core_models.Option.t_Option usize) v_E)
      (Core_models.Option.t_Option usize)
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue chosen ->
    Core_models.Result.Result_Ok chosen
    <:
    Core_models.Result.t_Result (Core_models.Option.t_Option usize) v_E

let clone_selected_fact (#v_F: Type0) (fact: v_F) (clone_fact: (v_F -> v_F)) : v_F = clone_fact fact

let canonical_step
      (#v_F #v_I #v_E: Type0)
      (facts: t_Slice v_F)
      (out: Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global)
      (id: (v_F -> v_I))
      (id_eq id_lt: (v_I -> v_I -> bool))
      (internal: (Prims.unit -> v_E))
      (clone_fact: (v_F -> v_F))
    : Core_models.Result.t_Result (Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global) v_E =
  match
    choose_unseen #v_F
      #v_I
      #v_E
      facts
      (Alloc.Vec.impl_1__as_slice out <: t_Slice v_F)
      id
      id_eq
      id_lt
      internal
    <:
    Core_models.Result.t_Result (Core_models.Option.t_Option usize) v_E
  with
  | Core_models.Result.Result_Ok chosen ->
    (match
        Core_models.Option.impl__ok_or #usize #v_E chosen (internal ())
        <:
        Core_models.Result.t_Result usize v_E
      with
      | Core_models.Result.Result_Ok i ->
        if i >=. (Core_models.Slice.impl__len #v_F facts <: usize)
        then
          Core_models.Result.Result_Err (internal ())
          <:
          Core_models.Result.t_Result (Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global) v_E
        else
          let
          (tmp0: Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global),
          (out1: Core_models.Result.t_Result Prims.unit v_E) =
            push #v_F
              #v_E
              out
              (clone_selected_fact #v_F (facts.[ i ] <: v_F) clone_fact <: v_F)
              internal
          in
          let out:Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global = tmp0 in
          (match out1 <: Core_models.Result.t_Result Prims.unit v_E with
            | Core_models.Result.Result_Ok _ ->
              Core_models.Result.Result_Ok out
              <:
              Core_models.Result.t_Result (Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global) v_E
            | Core_models.Result.Result_Err err ->
              Core_models.Result.Result_Err err
              <:
              Core_models.Result.t_Result (Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global) v_E)
      | Core_models.Result.Result_Err err ->
        Core_models.Result.Result_Err err
        <:
        Core_models.Result.t_Result (Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global) v_E)
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err
    <:
    Core_models.Result.t_Result (Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global) v_E

let canonical
      (#v_F #v_I #v_E: Type0)
      (facts: t_Slice v_F)
      (id: (v_F -> v_I))
      (id_eq id_lt: (v_I -> v_I -> bool))
      (internal: (Prims.unit -> v_E))
      (clone_fact: (v_F -> v_F))
    : Core_models.Result.t_Result (Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global) v_E =
  let out:Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global = Alloc.Vec.impl__new #v_F () in
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
      (Core_models.Slice.impl__len #v_F facts <: usize)
      (fun out temp_1_ ->
          let out:Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global = out in
          let _:usize = temp_1_ in
          true)
      out
      (fun out temp_1_ ->
          let out:Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global = out in
          let _:usize = temp_1_ in
          match
            canonical_step #v_F #v_I #v_E facts out id id_eq id_lt internal clone_fact
            <:
            Core_models.Result.t_Result (Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global) v_E
          with
          | Core_models.Result.Result_Ok hoist81 ->
            Core_models.Ops.Control_flow.ControlFlow_Continue hoist81
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result (Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global) v_E)
                  (Prims.unit & Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global))
              (Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global)
          | Core_models.Result.Result_Err err ->
            Core_models.Ops.Control_flow.ControlFlow_Break
            (Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Result.Result_Err err
                <:
                Core_models.Result.t_Result (Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global) v_E)
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Result.t_Result (Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global) v_E)
                (Prims.unit & Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global))
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result (Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global) v_E)
                  (Prims.unit & Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global))
              (Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global))
    <:
    Core_models.Ops.Control_flow.t_ControlFlow
      (Core_models.Result.t_Result (Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global) v_E)
      (Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global)
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue out ->
    Core_models.Result.Result_Ok out
    <:
    Core_models.Result.t_Result (Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global) v_E

let ready (#v_I: Type0) (after done: t_Slice v_I) (id_eq: (v_I -> v_I -> bool)) : bool =
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
      (Core_models.Slice.impl__len #v_I after <: usize)
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:usize = temp_1_ in
          true)
      ()
      (fun temp_0_ i ->
          let _:Prims.unit = temp_0_ in
          let i:usize = i in
          if has_id #v_I done (after.[ i ] <: v_I) id_eq <: bool
          then
            Core_models.Ops.Control_flow.ControlFlow_Continue ()
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow bool (Prims.unit & Prims.unit)) Prims.unit
          else
            Core_models.Ops.Control_flow.ControlFlow_Break
            (Core_models.Ops.Control_flow.ControlFlow_Break false
              <:
              Core_models.Ops.Control_flow.t_ControlFlow bool (Prims.unit & Prims.unit))
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow bool (Prims.unit & Prims.unit)) Prims.unit
      )
    <:
    Core_models.Ops.Control_flow.t_ControlFlow bool Prims.unit
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue _ -> true

let choose_ready
      (#v_F #v_I: Type0)
      (facts: t_Slice v_F)
      (done: t_Slice v_I)
      (id: (v_F -> v_I))
      (after: (v_F -> t_Slice v_I))
      (id_eq: (v_I -> v_I -> bool))
    : Core_models.Option.t_Option usize =
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
      (Core_models.Slice.impl__len #v_F facts <: usize)
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:usize = temp_1_ in
          true)
      ()
      (fun temp_0_ i ->
          let _:Prims.unit = temp_0_ in
          let i:usize = i in
          if has_id #v_I done (id (facts.[ i ] <: v_F)) id_eq <: bool
          then
            Core_models.Ops.Control_flow.ControlFlow_Continue ()
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow (Core_models.Option.t_Option usize)
                  (Prims.unit & Prims.unit)) Prims.unit
          else
            if ready #v_I (after (facts.[ i ] <: v_F)) done id_eq <: bool
            then
              Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Ops.Control_flow.ControlFlow_Break
                (Core_models.Option.Option_Some i <: Core_models.Option.t_Option usize)
                <:
                Core_models.Ops.Control_flow.t_ControlFlow (Core_models.Option.t_Option usize)
                  (Prims.unit & Prims.unit))
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Ops.Control_flow.t_ControlFlow (Core_models.Option.t_Option usize)
                    (Prims.unit & Prims.unit)) Prims.unit
            else
              Core_models.Ops.Control_flow.ControlFlow_Continue ()
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Ops.Control_flow.t_ControlFlow (Core_models.Option.t_Option usize)
                    (Prims.unit & Prims.unit)) Prims.unit)
    <:
    Core_models.Ops.Control_flow.t_ControlFlow (Core_models.Option.t_Option usize) Prims.unit
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue _ ->
    Core_models.Option.Option_None <: Core_models.Option.t_Option usize

let frontier
      (#v_F #v_I #v_E: Type0)
      (facts: t_Slice v_F)
      (id: (v_F -> v_I))
      (after: (v_F -> t_Slice v_I))
      (id_eq: (v_I -> v_I -> bool))
      (internal: (Prims.unit -> v_E))
    : Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E =
  let out:Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global = Alloc.Vec.impl__new #v_I () in
  match
    Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter #(t_Slice v_F
          )
          #FStar.Tactics.Typeclasses.solve
          facts
        <:
        Core_models.Slice.Iter.t_Iter v_F)
      out
      (fun out f ->
          let out:Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global = out in
          let f:v_F = f in
          let child:bool = false in
          let child:bool =
            Core_models.Iter.Traits.Iterator.f_fold (Core_models.Iter.Traits.Collect.f_into_iter #(t_Slice
                    v_F)
                  #FStar.Tactics.Typeclasses.solve
                  facts
                <:
                Core_models.Slice.Iter.t_Iter v_F)
              child
              (fun child e ->
                  let child:bool = child in
                  let e:v_F = e in
                  if has_id #v_I (after e) (id f) id_eq <: bool
                  then
                    let child:bool = true in
                    child
                  else child)
          in
          if ~.child
          then
            let
            (tmp0: Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global),
            (out1: Core_models.Result.t_Result Prims.unit v_E) =
              push #v_I #v_E out (id f) internal
            in
            let out:Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global = tmp0 in
            match out1 <: Core_models.Result.t_Result Prims.unit v_E with
            | Core_models.Result.Result_Ok _ ->
              Core_models.Ops.Control_flow.ControlFlow_Continue out
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                    (Prims.unit & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global))
                (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global)
            | Core_models.Result.Result_Err err ->
              Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Ops.Control_flow.ControlFlow_Break
                (Core_models.Result.Result_Err err
                  <:
                  Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                  (Prims.unit & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global))
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                    (Prims.unit & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global))
                (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global)
          else
            Core_models.Ops.Control_flow.ControlFlow_Continue out
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                  (Prims.unit & Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global))
              (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global))
    <:
    Core_models.Ops.Control_flow.t_ControlFlow
      (Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
      (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global)
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue out ->
    Core_models.Result.Result_Ok out
    <:
    Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E

let select_basis
      (#v_F #v_I #v_E: Type0)
      (facts: t_Slice v_F)
      (selected: t_Slice v_I)
      (id: (v_F -> v_I))
      (id_eq: (v_I -> v_I -> bool))
      (internal: (Prims.unit -> v_E))
      (clone_fact: (v_F -> v_F))
    : Core_models.Result.t_Result (Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global) v_E =
  let basis:Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global = Alloc.Vec.impl__new #v_F () in
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
      (Core_models.Slice.impl__len #v_F facts <: usize)
      (fun basis temp_1_ ->
          let basis:Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global = basis in
          let _:usize = temp_1_ in
          true)
      basis
      (fun basis i ->
          let basis:Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global = basis in
          let i:usize = i in
          let fact:v_F = facts.[ i ] in
          if has_id #v_I selected (id fact) id_eq
          then
            let
            (tmp0: Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global),
            (out: Core_models.Result.t_Result Prims.unit v_E) =
              push #v_F #v_E basis (clone_selected_fact #v_F fact clone_fact <: v_F) internal
            in
            let basis:Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global = tmp0 in
            match out <: Core_models.Result.t_Result Prims.unit v_E with
            | Core_models.Result.Result_Ok _ ->
              Core_models.Ops.Control_flow.ControlFlow_Continue basis
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result (Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global) v_E)
                    (Prims.unit & Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global))
                (Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global)
            | Core_models.Result.Result_Err err ->
              Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Ops.Control_flow.ControlFlow_Break
                (Core_models.Result.Result_Err err
                  <:
                  Core_models.Result.t_Result (Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global) v_E)
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result (Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global) v_E)
                  (Prims.unit & Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global))
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result (Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global) v_E)
                    (Prims.unit & Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global))
                (Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global)
          else
            Core_models.Ops.Control_flow.ControlFlow_Continue basis
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result (Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global) v_E)
                  (Prims.unit & Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global))
              (Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global))
    <:
    Core_models.Ops.Control_flow.t_ControlFlow
      (Core_models.Result.t_Result (Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global) v_E)
      (Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global)
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue basis ->
    Core_models.Result.Result_Ok basis
    <:
    Core_models.Result.t_Result (Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global) v_E

let event_basis
      (#v_F #v_I #v_E: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_I)
      (facts: t_Slice v_F)
      (event: v_F)
      (id: (v_F -> v_I))
      (after: (v_F -> t_Slice v_I))
      (id_eq: (v_I -> v_I -> bool))
      (internal missing: (Prims.unit -> v_E))
      (clone_fact: (v_F -> v_F))
    : Core_models.Result.t_Result
      (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global & Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global) v_E =
  match
    past #v_F #v_I #v_E facts (after event) id after id_eq internal missing
    <:
    Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E
  with
  | Core_models.Result.Result_Ok selected ->
    (match
        select_basis #v_F
          #v_I
          #v_E
          facts
          (Alloc.Vec.impl_1__as_slice selected <: t_Slice v_I)
          id
          id_eq
          internal
          clone_fact
        <:
        Core_models.Result.t_Result (Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global) v_E
      with
      | Core_models.Result.Result_Ok basis ->
        Core_models.Result.Result_Ok
        (selected, basis
          <:
          (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global & Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global))
        <:
        Core_models.Result.t_Result
          (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global & Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global) v_E
      | Core_models.Result.Result_Err err ->
        Core_models.Result.Result_Err err
        <:
        Core_models.Result.t_Result
          (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global & Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global) v_E)
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err
    <:
    Core_models.Result.t_Result
      (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global & Alloc.Vec.t_Vec v_F Alloc.Alloc.t_Global) v_E

/// Shared graph admission, before application-specific payload validation.
/// `forbidden` receives the selected ancestor identity, then the offered one.
let validate_event
      (#v_F #v_I #v_E: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_I)
      (facts: t_Slice v_F)
      (fact: v_F)
      (events_limit dependencies_limit: usize)
      (id: (v_F -> v_I))
      (after: (v_F -> t_Slice v_I))
      (id_eq: (v_I -> v_I -> bool))
      (predecessor: (v_I -> Core_models.Option.t_Option v_I))
      (forbidden: (v_I -> v_I -> bool))
      (event_capacity dep_capacity duplicate_error predecessor_error internal missing:
          (Prims.unit -> v_E))
    : Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E =
  if (Core_models.Slice.impl__len #v_F facts <: usize) >=. events_limit
  then
    Core_models.Result.Result_Err (event_capacity ())
    <:
    Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E
  else
    if (Core_models.Slice.impl__len #v_I (after fact) <: usize) >. dependencies_limit
    then
      Core_models.Result.Result_Err (dep_capacity ())
      <:
      Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E
    else
      if duplicate_ids #v_I (after fact) id_eq
      then
        Core_models.Result.Result_Err (duplicate_error ())
        <:
        Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E
      else
        match
          past #v_F #v_I #v_E facts (after fact) id after id_eq internal missing
          <:
          Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E
        with
        | Core_models.Result.Result_Ok selected ->
          (match predecessor (id fact) <: Core_models.Option.t_Option v_I with
            | Core_models.Option.Option_Some previous ->
              if
                ~.(has_id #v_I (Alloc.Vec.impl_1__as_slice selected <: t_Slice v_I) previous id_eq
                  <:
                  bool)
              then
                Core_models.Result.Result_Err (predecessor_error ())
                <:
                Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E
              else
                (match
                    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
                      (Core_models.Slice.impl__len #v_F facts <: usize)
                      (fun temp_0_ temp_1_ ->
                          let _:Prims.unit = temp_0_ in
                          let _:usize = temp_1_ in
                          true)
                      ()
                      (fun temp_0_ i ->
                          let _:Prims.unit = temp_0_ in
                          let i:usize = i in
                          let e:v_F = facts.[ i ] in
                          if
                            has_id #v_I
                              (Alloc.Vec.impl_1__as_slice selected <: t_Slice v_I)
                              (id e)
                              id_eq &&
                            forbidden (id e) (id fact)
                          then
                            Core_models.Ops.Control_flow.ControlFlow_Break
                            (Core_models.Ops.Control_flow.ControlFlow_Break
                              (Core_models.Result.Result_Err (predecessor_error ())
                                <:
                                Core_models.Result.t_Result
                                  (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                              <:
                              Core_models.Ops.Control_flow.t_ControlFlow
                                (Core_models.Result.t_Result
                                    (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                                (Prims.unit & Prims.unit))
                            <:
                            Core_models.Ops.Control_flow.t_ControlFlow
                              (Core_models.Ops.Control_flow.t_ControlFlow
                                  (Core_models.Result.t_Result
                                      (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                                  (Prims.unit & Prims.unit)) Prims.unit
                          else
                            Core_models.Ops.Control_flow.ControlFlow_Continue ()
                            <:
                            Core_models.Ops.Control_flow.t_ControlFlow
                              (Core_models.Ops.Control_flow.t_ControlFlow
                                  (Core_models.Result.t_Result
                                      (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                                  (Prims.unit & Prims.unit)) Prims.unit)
                    <:
                    Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                      Prims.unit
                  with
                  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
                  | Core_models.Ops.Control_flow.ControlFlow_Continue _ ->
                    Core_models.Result.Result_Ok selected
                    <:
                    Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
            | Core_models.Option.Option_None  ->
              match
                Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
                  (Core_models.Slice.impl__len #v_F facts <: usize)
                  (fun temp_0_ temp_1_ ->
                      let _:Prims.unit = temp_0_ in
                      let _:usize = temp_1_ in
                      true)
                  ()
                  (fun temp_0_ i ->
                      let _:Prims.unit = temp_0_ in
                      let i:usize = i in
                      let e:v_F = facts.[ i ] in
                      if
                        has_id #v_I
                          (Alloc.Vec.impl_1__as_slice selected <: t_Slice v_I)
                          (id e)
                          id_eq &&
                        forbidden (id e) (id fact)
                      then
                        Core_models.Ops.Control_flow.ControlFlow_Break
                        (Core_models.Ops.Control_flow.ControlFlow_Break
                          (Core_models.Result.Result_Err (predecessor_error ())
                            <:
                            Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global)
                              v_E)
                          <:
                          Core_models.Ops.Control_flow.t_ControlFlow
                            (Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global)
                                v_E) (Prims.unit & Prims.unit))
                        <:
                        Core_models.Ops.Control_flow.t_ControlFlow
                          (Core_models.Ops.Control_flow.t_ControlFlow
                              (Core_models.Result.t_Result
                                  (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                              (Prims.unit & Prims.unit)) Prims.unit
                      else
                        Core_models.Ops.Control_flow.ControlFlow_Continue ()
                        <:
                        Core_models.Ops.Control_flow.t_ControlFlow
                          (Core_models.Ops.Control_flow.t_ControlFlow
                              (Core_models.Result.t_Result
                                  (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                              (Prims.unit & Prims.unit)) Prims.unit)
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
                  Prims.unit
              with
              | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
              | Core_models.Ops.Control_flow.ControlFlow_Continue _ ->
                Core_models.Result.Result_Ok selected
                <:
                Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E)
        | Core_models.Result.Result_Err err ->
          Core_models.Result.Result_Err err
          <:
          Core_models.Result.t_Result (Alloc.Vec.t_Vec v_I Alloc.Alloc.t_Global) v_E
