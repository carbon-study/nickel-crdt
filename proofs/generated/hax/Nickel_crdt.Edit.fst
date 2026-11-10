module Nickel_crdt.Edit
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_Writer =
  | Writer_Alice : t_Writer
  | Writer_Bo : t_Writer

let writer_index (w: t_Writer) : u8 =
  match w <: t_Writer with
  | Writer_Alice  -> mk_u8 0
  | Writer_Bo  -> mk_u8 1

type t_EventId = {
  f_writer:t_Writer;
  f_counter:u64
}

let impl_14: Core_models.Clone.t_Clone t_EventId =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

type t_BirthId = {
  f_event:t_EventId;
  f_index:usize
}

let impl_20: Core_models.Clone.t_Clone t_BirthId =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

type t_Fact = {
  f_id:t_EventId;
  f_after:Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global;
  f_insert:Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global;
  f_delete:Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global;
  f_gap:Core_models.Option.t_Option usize
}

let impl_26: Core_models.Clone.t_Clone t_Fact =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

type t_Limits = {
  f_events:usize;
  f_births:usize;
  f_scalars:usize;
  f_dependencies:usize;
  f_ordering_links:usize
}

type t_Invalid =
  | Invalid_Counter : t_Invalid
  | Invalid_Conflict : t_Invalid
  | Invalid_DependencyDuplicate : t_Invalid
  | Invalid_Predecessor : t_Invalid
  | Invalid_DeleteDuplicate : t_Invalid
  | Invalid_DeleteNotVisible : t_Invalid
  | Invalid_Scalar : t_Invalid
  | Invalid_Gap : t_Invalid
  | Invalid_PlacementWithoutBirth : t_Invalid
  | Invalid_NoWriter : t_Invalid
  | Invalid_Profile : t_Invalid

type t_Capacity =
  | Capacity_Events : t_Capacity
  | Capacity_Births : t_Capacity
  | Capacity_Scalars : t_Capacity
  | Capacity_Dependencies : t_Capacity
  | Capacity_DeleteTargets : t_Capacity
  | Capacity_OrderingLinks : t_Capacity
  | Capacity_Counter : t_Capacity

type t_Error =
  | Error_Invalid : t_Invalid -> t_Error
  | Error_Missing : t_Error
  | Error_Capacity : t_Capacity -> t_Error
  | Error_Internal : t_Error

type t_Admission =
  | Admission_Added : t_Admission
  | Admission_Duplicate : t_Admission

type t_Local =
  | Local_Empty : t_Local
  | Local_Authored : t_Fact -> t_Local

type t_Side =
  | Side_Left : t_Side
  | Side_Right : t_Side

type t_Node = {
  f_id:t_BirthId;
  f_scalar:u32;
  f_left_origin:Core_models.Option.t_Option t_BirthId;
  f_right_origin:Core_models.Option.t_Option t_BirthId;
  f_parent:Core_models.Option.t_Option t_BirthId;
  f_side:t_Side;
  f_left:Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global;
  f_right:Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global
}

let impl_70: Core_models.Clone.t_Clone t_Node =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

type t_Tree = {
  f_nodes:Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global;
  f_root_right:Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global
}

type t_Visit =
  | Visit_Enter : t_BirthId -> t_Visit
  | Visit_Emit : t_BirthId -> t_Visit

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core_models.Cmp.t_PartialEq t_Writer t_Writer =
  {
    f_eq_pre = (fun (self: t_Writer) (other: t_Writer) -> true);
    f_eq_post = (fun (self: t_Writer) (other: t_Writer) (out: bool) -> true);
    f_eq
    =
    fun (self: t_Writer) (other: t_Writer) ->
      (writer_index self <: u8) =. (writer_index other <: u8)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core_models.Cmp.t_PartialEq t_EventId t_EventId =
  {
    f_eq_pre = (fun (self: t_EventId) (other: t_EventId) -> true);
    f_eq_post = (fun (self: t_EventId) (other: t_EventId) (out: bool) -> true);
    f_eq
    =
    fun (self: t_EventId) (other: t_EventId) ->
      self.f_writer =. other.f_writer && self.f_counter =. other.f_counter
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core_models.Cmp.t_PartialEq t_BirthId t_BirthId =
  {
    f_eq_pre = (fun (self: t_BirthId) (other: t_BirthId) -> true);
    f_eq_post = (fun (self: t_BirthId) (other: t_BirthId) (out: bool) -> true);
    f_eq
    =
    fun (self: t_BirthId) (other: t_BirthId) ->
      self.f_event =. other.f_event && self.f_index =. other.f_index
  }

let fact_equal (left right: t_Fact) : bool =
  left.f_id =. right.f_id && left.f_after =. right.f_after && left.f_insert =. right.f_insert &&
  left.f_delete =. right.f_delete &&
  left.f_gap =. right.f_gap

let event_lt (a b: t_EventId) : bool =
  (writer_index a.f_writer <: u8) <. (writer_index b.f_writer <: u8) ||
  a.f_writer =. b.f_writer && a.f_counter <. b.f_counter

let birth_lt (a b: t_BirthId) : bool =
  event_lt a.f_event b.f_event || a.f_event =. b.f_event && a.f_index <. b.f_index

let v_MAX_COUNTER: u64 = mk_u64 9007199254740991

let invalid (reason: t_Invalid) : t_Error = Error_Invalid reason <: t_Error

let validate_scalars (scalars: t_Slice u32) : Core_models.Result.t_Result Prims.unit t_Error =
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
      (Core_models.Slice.impl__len #u32 scalars <: usize)
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:usize = temp_1_ in
          true)
      ()
      (fun temp_0_ i ->
          let _:Prims.unit = temp_0_ in
          let i:usize = i in
          let scalar:u32 = scalars.[ i ] in
          if scalar >. mk_u32 1114111 || scalar >=. mk_u32 55296 && scalar <=. mk_u32 57343
          then
            Core_models.Ops.Control_flow.ControlFlow_Break
            (Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Result.Result_Err (invalid (Invalid_Scalar <: t_Invalid))
                <:
                Core_models.Result.t_Result Prims.unit t_Error)
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Result.t_Result Prims.unit t_Error) (Prims.unit & Prims.unit))
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result Prims.unit t_Error) (Prims.unit & Prims.unit))
              Prims.unit
          else
            Core_models.Ops.Control_flow.ControlFlow_Continue ()
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result Prims.unit t_Error) (Prims.unit & Prims.unit))
              Prims.unit)
    <:
    Core_models.Ops.Control_flow.t_ControlFlow (Core_models.Result.t_Result Prims.unit t_Error)
      Prims.unit
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue _ ->
    Core_models.Result.Result_Ok (() <: Prims.unit)
    <:
    Core_models.Result.t_Result Prims.unit t_Error

let duplicate_events (xs: t_Slice t_EventId) : bool =
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
      (Core_models.Slice.impl__len #t_EventId xs <: usize)
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
                  if (xs.[ i ] <: t_EventId) =. (xs.[ j ] <: t_EventId) <: bool
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

let duplicate_births (xs: t_Slice t_BirthId) : bool =
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
      (Core_models.Slice.impl__len #t_BirthId xs <: usize)
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
                  if (xs.[ i ] <: t_BirthId) =. (xs.[ j ] <: t_BirthId) <: bool
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

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: Core_models.Default.t_Default t_Tree =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_Tree) -> true);
    f_default
    =
    fun (_: Prims.unit) ->
      { f_nodes = Alloc.Vec.impl__new #t_Node (); f_root_right = Alloc.Vec.impl__new #t_BirthId () }
      <:
      t_Tree
  }

let add (a b: usize) : Core_models.Result.t_Result usize t_Error =
  if b >. (Core_models.Num.impl_usize__MAX -! a <: usize)
  then
    Core_models.Result.Result_Err (Error_Internal <: t_Error)
    <:
    Core_models.Result.t_Result usize t_Error
  else Core_models.Result.Result_Ok (a +! b) <: Core_models.Result.t_Result usize t_Error

let push (#v_T: Type0) (xs: Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global) (value: v_T)
    : (Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global & Core_models.Result.t_Result Prims.unit t_Error) =
  if
    (Alloc.Vec.impl_1__len #v_T #Alloc.Alloc.t_Global xs <: usize) =.
    Core_models.Num.impl_usize__MAX
  then
    xs,
    (Core_models.Result.Result_Err (Error_Internal <: t_Error)
      <:
      Core_models.Result.t_Result Prims.unit t_Error)
    <:
    (Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global & Core_models.Result.t_Result Prims.unit t_Error)
  else
    let xs:Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global =
      Alloc.Vec.impl_1__push #v_T #Alloc.Alloc.t_Global xs value
    in
    let hax_temp_output:Core_models.Result.t_Result Prims.unit t_Error =
      Core_models.Result.Result_Ok (() <: Prims.unit)
      <:
      Core_models.Result.t_Result Prims.unit t_Error
    in
    xs, hax_temp_output
    <:
    (Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global & Core_models.Result.t_Result Prims.unit t_Error)

let insert (#v_T: Type0) (xs: Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global) (at: usize) (value: v_T)
    : (Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global & Core_models.Result.t_Result Prims.unit t_Error) =
  if
    at >. (Alloc.Vec.impl_1__len #v_T #Alloc.Alloc.t_Global xs <: usize) ||
    (Alloc.Vec.impl_1__len #v_T #Alloc.Alloc.t_Global xs <: usize) =.
    Core_models.Num.impl_usize__MAX
  then
    xs,
    (Core_models.Result.Result_Err (Error_Internal <: t_Error)
      <:
      Core_models.Result.t_Result Prims.unit t_Error)
    <:
    (Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global & Core_models.Result.t_Result Prims.unit t_Error)
  else
    let xs:Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global =
      Alloc.Vec.impl_1__insert #v_T #Alloc.Alloc.t_Global xs at value
    in
    let hax_temp_output:Core_models.Result.t_Result Prims.unit t_Error =
      Core_models.Result.Result_Ok (() <: Prims.unit)
      <:
      Core_models.Result.t_Result Prims.unit t_Error
    in
    xs, hax_temp_output
    <:
    (Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global & Core_models.Result.t_Result Prims.unit t_Error)

let impl_Tree__position (self: t_Tree) (id: t_BirthId) : Core_models.Result.t_Result usize t_Error =
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
      (Alloc.Vec.impl_1__len #t_Node #Alloc.Alloc.t_Global self.f_nodes <: usize)
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:usize = temp_1_ in
          true)
      ()
      (fun temp_0_ i ->
          let _:Prims.unit = temp_0_ in
          let i:usize = i in
          if (self.f_nodes.[ i ] <: t_Node).f_id =. id <: bool
          then
            Core_models.Ops.Control_flow.ControlFlow_Break
            (Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Result.Result_Ok i <: Core_models.Result.t_Result usize t_Error)
              <:
              Core_models.Ops.Control_flow.t_ControlFlow (Core_models.Result.t_Result usize t_Error)
                (Prims.unit & Prims.unit))
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result usize t_Error) (Prims.unit & Prims.unit)) Prims.unit
          else
            Core_models.Ops.Control_flow.ControlFlow_Continue ()
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result usize t_Error) (Prims.unit & Prims.unit)) Prims.unit)
    <:
    Core_models.Ops.Control_flow.t_ControlFlow (Core_models.Result.t_Result usize t_Error)
      Prims.unit
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue _ ->
    Core_models.Result.Result_Err (Error_Internal <: t_Error)
    <:
    Core_models.Result.t_Result usize t_Error

let impl_Tree__node (self: t_Tree) (id: t_BirthId) : Core_models.Result.t_Result t_Node t_Error =
  match impl_Tree__position self id <: Core_models.Result.t_Result usize t_Error with
  | Core_models.Result.Result_Ok p ->
    if p >=. (Alloc.Vec.impl_1__len #t_Node #Alloc.Alloc.t_Global self.f_nodes <: usize)
    then
      Core_models.Result.Result_Err (Error_Internal <: t_Error)
      <:
      Core_models.Result.t_Result t_Node t_Error
    else
      Core_models.Result.Result_Ok
      (Core_models.Clone.f_clone #t_Node
          #FStar.Tactics.Typeclasses.solve
          (self.f_nodes.[ p ] <: t_Node))
      <:
      Core_models.Result.t_Result t_Node t_Error
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err <: Core_models.Result.t_Result t_Node t_Error

let impl_Tree__whole (self: t_Tree)
    : Core_models.Result.t_Result (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error =
  if (Alloc.Vec.impl_1__len #t_Node #Alloc.Alloc.t_Global self.f_nodes <: usize) >. mk_usize 512
  then
    Core_models.Result.Result_Err (Error_Internal <: t_Error)
    <:
    Core_models.Result.t_Result (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error
  else
    let stack:Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global = Alloc.Vec.impl__new #t_Visit () in
    let out:Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global = Alloc.Vec.impl__new #t_BirthId () in
    match
      Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
        (Alloc.Vec.impl_1__len #t_BirthId #Alloc.Alloc.t_Global self.f_root_right <: usize)
        (fun stack temp_1_ ->
            let stack:Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global = stack in
            let _:usize = temp_1_ in
            true)
        stack
        (fun stack offset ->
            let stack:Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global = stack in
            let offset:usize = offset in
            let i:usize =
              ((Alloc.Vec.impl_1__len #t_BirthId #Alloc.Alloc.t_Global self.f_root_right <: usize) -!
                mk_usize 1
                <:
                usize) -!
              offset
            in
            let
            (tmp0: Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global),
            (out1: Core_models.Result.t_Result Prims.unit t_Error) =
              push #t_Visit stack (Visit_Enter (self.f_root_right.[ i ] <: t_BirthId) <: t_Visit)
            in
            let stack:Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global = tmp0 in
            match out1 <: Core_models.Result.t_Result Prims.unit t_Error with
            | Core_models.Result.Result_Ok _ ->
              Core_models.Ops.Control_flow.ControlFlow_Continue stack
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
                        t_Error) (Prims.unit & Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global))
                (Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global)
            | Core_models.Result.Result_Err err ->
              Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Ops.Control_flow.ControlFlow_Break
                (Core_models.Result.Result_Err err
                  <:
                  Core_models.Result.t_Result (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
                    t_Error)
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
                      t_Error) (Prims.unit & Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global))
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
                        t_Error) (Prims.unit & Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global))
                (Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global))
      <:
      Core_models.Ops.Control_flow.t_ControlFlow
        (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error)
        (Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global)
    with
    | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
    | Core_models.Ops.Control_flow.ControlFlow_Continue stack ->
      match
        Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
          ((Alloc.Vec.impl_1__len #t_Node #Alloc.Alloc.t_Global self.f_nodes <: usize) *! mk_usize 2
            <:
            usize)
          (fun temp_0_ temp_1_ ->
              let
              (out: Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global),
              (stack: Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global) =
                temp_0_
              in
              let _:usize = temp_1_ in
              true)
          (out, stack
            <:
            (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global &
              Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global))
          (fun temp_0_ temp_1_ ->
              let
              (out: Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global),
              (stack: Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global) =
                temp_0_
              in
              let _:usize = temp_1_ in
              let
              (tmp0: Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global),
              (out1: Core_models.Option.t_Option t_Visit) =
                Alloc.Vec.impl_1__pop #t_Visit #Alloc.Alloc.t_Global stack
              in
              let stack:Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global = tmp0 in
              match
                Core_models.Option.impl__ok_or #t_Visit #t_Error out1 (Error_Internal <: t_Error)
                <:
                Core_models.Result.t_Result t_Visit t_Error
              with
              | Core_models.Result.Result_Ok visit ->
                (match visit <: t_Visit with
                  | Visit_Emit id ->
                    let
                    (tmp0: Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global),
                    (out1: Core_models.Result.t_Result Prims.unit t_Error) =
                      push #t_BirthId out id
                    in
                    let out:Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global = tmp0 in
                    (match out1 <: Core_models.Result.t_Result Prims.unit t_Error with
                      | Core_models.Result.Result_Ok ok ->
                        Core_models.Ops.Control_flow.ControlFlow_Continue
                        (out, stack
                          <:
                          (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global &
                            Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global))
                        <:
                        Core_models.Ops.Control_flow.t_ControlFlow
                          (Core_models.Ops.Control_flow.t_ControlFlow
                              (Core_models.Result.t_Result
                                  (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error)
                              (Prims.unit &
                                (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global &
                                  Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global)))
                          (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global &
                            Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global)
                      | Core_models.Result.Result_Err err ->
                        Core_models.Ops.Control_flow.ControlFlow_Break
                        (Core_models.Ops.Control_flow.ControlFlow_Break
                          (Core_models.Result.Result_Err err
                            <:
                            Core_models.Result.t_Result
                              (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error)
                          <:
                          Core_models.Ops.Control_flow.t_ControlFlow
                            (Core_models.Result.t_Result
                                (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error)
                            (Prims.unit &
                              (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global &
                                Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global)))
                        <:
                        Core_models.Ops.Control_flow.t_ControlFlow
                          (Core_models.Ops.Control_flow.t_ControlFlow
                              (Core_models.Result.t_Result
                                  (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error)
                              (Prims.unit &
                                (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global &
                                  Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global)))
                          (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global &
                            Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global))
                  | Visit_Enter id ->
                    match impl_Tree__node self id <: Core_models.Result.t_Result t_Node t_Error with
                    | Core_models.Result.Result_Ok node ->
                      (match
                          Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
                            (Alloc.Vec.impl_1__len #t_BirthId #Alloc.Alloc.t_Global node.f_right
                              <:
                              usize)
                            (fun stack temp_1_ ->
                                let stack:Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global = stack in
                                let _:usize = temp_1_ in
                                true)
                            stack
                            (fun stack offset ->
                                let stack:Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global = stack in
                                let offset:usize = offset in
                                let i:usize =
                                  ((Alloc.Vec.impl_1__len #t_BirthId
                                        #Alloc.Alloc.t_Global
                                        node.f_right
                                      <:
                                      usize) -!
                                    mk_usize 1
                                    <:
                                    usize) -!
                                  offset
                                in
                                let
                                (tmp0: Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global),
                                (out1: Core_models.Result.t_Result Prims.unit t_Error) =
                                  push #t_Visit
                                    stack
                                    (Visit_Enter (node.f_right.[ i ] <: t_BirthId) <: t_Visit)
                                in
                                let stack:Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global = tmp0 in
                                match out1 <: Core_models.Result.t_Result Prims.unit t_Error with
                                | Core_models.Result.Result_Ok _ ->
                                  Core_models.Ops.Control_flow.ControlFlow_Continue stack
                                  <:
                                  Core_models.Ops.Control_flow.t_ControlFlow
                                    (Core_models.Ops.Control_flow.t_ControlFlow
                                        (Core_models.Result.t_Result
                                            (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error
                                        )
                                        (Prims.unit & Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global))
                                    (Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global)
                                | Core_models.Result.Result_Err err ->
                                  Core_models.Ops.Control_flow.ControlFlow_Break
                                  (Core_models.Ops.Control_flow.ControlFlow_Break
                                    (Core_models.Result.Result_Err err
                                      <:
                                      Core_models.Result.t_Result
                                        (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error)
                                    <:
                                    Core_models.Ops.Control_flow.t_ControlFlow
                                      (Core_models.Result.t_Result
                                          (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error)
                                      (Prims.unit & Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global))
                                  <:
                                  Core_models.Ops.Control_flow.t_ControlFlow
                                    (Core_models.Ops.Control_flow.t_ControlFlow
                                        (Core_models.Result.t_Result
                                            (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error
                                        )
                                        (Prims.unit & Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global))
                                    (Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global))
                          <:
                          Core_models.Ops.Control_flow.t_ControlFlow
                            (Core_models.Result.t_Result
                                (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error)
                            (Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global)
                        with
                        | Core_models.Ops.Control_flow.ControlFlow_Break ret ->
                          Core_models.Ops.Control_flow.ControlFlow_Break
                          (Core_models.Ops.Control_flow.ControlFlow_Break ret
                            <:
                            Core_models.Ops.Control_flow.t_ControlFlow
                              (Core_models.Result.t_Result
                                  (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error)
                              (Prims.unit &
                                (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global &
                                  Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global)))
                          <:
                          Core_models.Ops.Control_flow.t_ControlFlow
                            (Core_models.Ops.Control_flow.t_ControlFlow
                                (Core_models.Result.t_Result
                                    (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error)
                                (Prims.unit &
                                  (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global &
                                    Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global)))
                            (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global &
                              Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global)
                        | Core_models.Ops.Control_flow.ControlFlow_Continue stack ->
                          let
                          (tmp0: Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global),
                          (out1: Core_models.Result.t_Result Prims.unit t_Error) =
                            push #t_Visit stack (Visit_Emit id <: t_Visit)
                          in
                          let stack:Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global = tmp0 in
                          match out1 <: Core_models.Result.t_Result Prims.unit t_Error with
                          | Core_models.Result.Result_Ok _ ->
                            (match
                                Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
                                  (Alloc.Vec.impl_1__len #t_BirthId
                                      #Alloc.Alloc.t_Global
                                      node.f_left
                                    <:
                                    usize)
                                  (fun stack temp_1_ ->
                                      let stack:Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global =
                                        stack
                                      in
                                      let _:usize = temp_1_ in
                                      true)
                                  stack
                                  (fun stack offset ->
                                      let stack:Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global =
                                        stack
                                      in
                                      let offset:usize = offset in
                                      let i:usize =
                                        ((Alloc.Vec.impl_1__len #t_BirthId
                                              #Alloc.Alloc.t_Global
                                              node.f_left
                                            <:
                                            usize) -!
                                          mk_usize 1
                                          <:
                                          usize) -!
                                        offset
                                      in
                                      let
                                      (tmp0: Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global),
                                      (out1: Core_models.Result.t_Result Prims.unit t_Error) =
                                        push #t_Visit
                                          stack
                                          (Visit_Enter (node.f_left.[ i ] <: t_BirthId) <: t_Visit)
                                      in
                                      let stack:Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global =
                                        tmp0
                                      in
                                      match
                                        out1 <: Core_models.Result.t_Result Prims.unit t_Error
                                      with
                                      | Core_models.Result.Result_Ok _ ->
                                        Core_models.Ops.Control_flow.ControlFlow_Continue stack
                                        <:
                                        Core_models.Ops.Control_flow.t_ControlFlow
                                          (Core_models.Ops.Control_flow.t_ControlFlow
                                              (Core_models.Result.t_Result
                                                  (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
                                                  t_Error)
                                              (Prims.unit &
                                                Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global))
                                          (Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global)
                                      | Core_models.Result.Result_Err err ->
                                        Core_models.Ops.Control_flow.ControlFlow_Break
                                        (Core_models.Ops.Control_flow.ControlFlow_Break
                                          (Core_models.Result.Result_Err err
                                            <:
                                            Core_models.Result.t_Result
                                              (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
                                              t_Error)
                                          <:
                                          Core_models.Ops.Control_flow.t_ControlFlow
                                            (Core_models.Result.t_Result
                                                (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
                                                t_Error)
                                            (Prims.unit &
                                              Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global))
                                        <:
                                        Core_models.Ops.Control_flow.t_ControlFlow
                                          (Core_models.Ops.Control_flow.t_ControlFlow
                                              (Core_models.Result.t_Result
                                                  (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
                                                  t_Error)
                                              (Prims.unit &
                                                Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global))
                                          (Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global))
                                <:
                                Core_models.Ops.Control_flow.t_ControlFlow
                                  (Core_models.Result.t_Result
                                      (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error)
                                  (Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global)
                              with
                              | Core_models.Ops.Control_flow.ControlFlow_Break ret ->
                                Core_models.Ops.Control_flow.ControlFlow_Break
                                (Core_models.Ops.Control_flow.ControlFlow_Break ret
                                  <:
                                  Core_models.Ops.Control_flow.t_ControlFlow
                                    (Core_models.Result.t_Result
                                        (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error)
                                    (Prims.unit &
                                      (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global &
                                        Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global)))
                                <:
                                Core_models.Ops.Control_flow.t_ControlFlow
                                  (Core_models.Ops.Control_flow.t_ControlFlow
                                      (Core_models.Result.t_Result
                                          (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error)
                                      (Prims.unit &
                                        (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global &
                                          Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global)))
                                  (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global &
                                    Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global)
                              | Core_models.Ops.Control_flow.ControlFlow_Continue stack ->
                                Core_models.Ops.Control_flow.ControlFlow_Continue
                                (out, stack
                                  <:
                                  (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global &
                                    Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global))
                                <:
                                Core_models.Ops.Control_flow.t_ControlFlow
                                  (Core_models.Ops.Control_flow.t_ControlFlow
                                      (Core_models.Result.t_Result
                                          (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error)
                                      (Prims.unit &
                                        (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global &
                                          Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global)))
                                  (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global &
                                    Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global))
                          | Core_models.Result.Result_Err err ->
                            Core_models.Ops.Control_flow.ControlFlow_Break
                            (Core_models.Ops.Control_flow.ControlFlow_Break
                              (Core_models.Result.Result_Err err
                                <:
                                Core_models.Result.t_Result
                                  (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error)
                              <:
                              Core_models.Ops.Control_flow.t_ControlFlow
                                (Core_models.Result.t_Result
                                    (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error)
                                (Prims.unit &
                                  (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global &
                                    Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global)))
                            <:
                            Core_models.Ops.Control_flow.t_ControlFlow
                              (Core_models.Ops.Control_flow.t_ControlFlow
                                  (Core_models.Result.t_Result
                                      (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error)
                                  (Prims.unit &
                                    (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global &
                                      Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global)))
                              (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global &
                                Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global))
                    | Core_models.Result.Result_Err err ->
                      Core_models.Ops.Control_flow.ControlFlow_Break
                      (Core_models.Ops.Control_flow.ControlFlow_Break
                        (Core_models.Result.Result_Err err
                          <:
                          Core_models.Result.t_Result
                            (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error)
                        <:
                        Core_models.Ops.Control_flow.t_ControlFlow
                          (Core_models.Result.t_Result
                              (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error)
                          (Prims.unit &
                            (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global &
                              Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global)))
                      <:
                      Core_models.Ops.Control_flow.t_ControlFlow
                        (Core_models.Ops.Control_flow.t_ControlFlow
                            (Core_models.Result.t_Result
                                (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error)
                            (Prims.unit &
                              (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global &
                                Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global)))
                        (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global &
                          Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global))
              | Core_models.Result.Result_Err err ->
                Core_models.Ops.Control_flow.ControlFlow_Break
                (Core_models.Ops.Control_flow.ControlFlow_Break
                  (Core_models.Result.Result_Err err
                    <:
                    Core_models.Result.t_Result (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
                      t_Error)
                  <:
                  Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
                        t_Error)
                    (Prims.unit &
                      (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global &
                        Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global)))
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
                          t_Error)
                      (Prims.unit &
                        (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global &
                          Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global)))
                  (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global &
                    Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global))
        <:
        Core_models.Ops.Control_flow.t_ControlFlow
          (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error)
          (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global &
            Alloc.Vec.t_Vec t_Visit Alloc.Alloc.t_Global)
      with
      | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
      | Core_models.Ops.Control_flow.ControlFlow_Continue (out, stack) ->
        if ~.(Alloc.Vec.impl_1__is_empty #t_Visit #Alloc.Alloc.t_Global stack <: bool)
        then
          Core_models.Result.Result_Err (Error_Internal <: t_Error)
          <:
          Core_models.Result.t_Result (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error
        else
          Core_models.Result.Result_Ok out
          <:
          Core_models.Result.t_Result (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error

let impl_Tree__rank (order: t_Slice t_BirthId) (origin: Core_models.Option.t_Option t_BirthId)
    : Core_models.Result.t_Result usize t_Error =
  match origin <: Core_models.Option.t_Option t_BirthId with
  | Core_models.Option.Option_Some id ->
    (match
        Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
          (Core_models.Slice.impl__len #t_BirthId order <: usize)
          (fun temp_0_ temp_1_ ->
              let _:Prims.unit = temp_0_ in
              let _:usize = temp_1_ in
              true)
          ()
          (fun temp_0_ i ->
              let _:Prims.unit = temp_0_ in
              let i:usize = i in
              if (order.[ i ] <: t_BirthId) =. id <: bool
              then
                Core_models.Ops.Control_flow.ControlFlow_Break
                (Core_models.Ops.Control_flow.ControlFlow_Break
                  (Core_models.Result.Result_Ok i <: Core_models.Result.t_Result usize t_Error)
                  <:
                  Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result usize t_Error) (Prims.unit & Prims.unit))
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Result.t_Result usize t_Error) (Prims.unit & Prims.unit))
                  Prims.unit
              else
                Core_models.Ops.Control_flow.ControlFlow_Continue ()
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Result.t_Result usize t_Error) (Prims.unit & Prims.unit))
                  Prims.unit)
        <:
        Core_models.Ops.Control_flow.t_ControlFlow (Core_models.Result.t_Result usize t_Error)
          Prims.unit
      with
      | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
      | Core_models.Ops.Control_flow.ControlFlow_Continue _ ->
        Core_models.Result.Result_Err (Error_Internal <: t_Error)
        <:
        Core_models.Result.t_Result usize t_Error)
  | _ ->
    Core_models.Result.Result_Ok Core_models.Num.impl_usize__MAX
    <:
    Core_models.Result.t_Result usize t_Error

let impl_Tree__add (self: t_Tree) (node: t_Node)
    : (t_Tree & Core_models.Result.t_Result Prims.unit t_Error) =
  match
    Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter #(Core_models.Slice.Iter.t_Iter
            t_Node)
          #FStar.Tactics.Typeclasses.solve
          (Core_models.Slice.impl__iter #t_Node
              (Alloc.Vec.impl_1__as_slice self.f_nodes <: t_Slice t_Node)
            <:
            Core_models.Slice.Iter.t_Iter t_Node)
        <:
        Core_models.Slice.Iter.t_Iter t_Node)
      ()
      (fun temp_0_ old ->
          let _:Prims.unit = temp_0_ in
          let old:t_Node = old in
          if old.f_id =. node.f_id <: bool
          then
            Core_models.Ops.Control_flow.ControlFlow_Break
            (Core_models.Ops.Control_flow.ControlFlow_Break
              (self,
                (Core_models.Result.Result_Err (Error_Internal <: t_Error)
                  <:
                  Core_models.Result.t_Result Prims.unit t_Error)
                <:
                (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (t_Tree & Core_models.Result.t_Result Prims.unit t_Error) (Prims.unit & Prims.unit))
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                  (Prims.unit & Prims.unit)) Prims.unit
          else
            Core_models.Ops.Control_flow.ControlFlow_Continue ()
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                  (Prims.unit & Prims.unit)) Prims.unit)
    <:
    Core_models.Ops.Control_flow.t_ControlFlow
      (t_Tree & Core_models.Result.t_Result Prims.unit t_Error) Prims.unit
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue _ ->
    match
      impl_Tree__whole self
      <:
      Core_models.Result.t_Result (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error
    with
    | Core_models.Result.Result_Ok whole ->
      (match node.f_parent <: Core_models.Option.t_Option t_BirthId with
        | Core_models.Option.Option_Some id ->
          (match impl_Tree__position self id <: Core_models.Result.t_Result usize t_Error with
            | Core_models.Result.Result_Ok hoist20 ->
              let parent:Core_models.Option.t_Option usize =
                Core_models.Option.Option_Some hoist20 <: Core_models.Option.t_Option usize
              in
              (match parent <: Core_models.Option.t_Option usize with
                | Core_models.Option.Option_Some p ->
                  if
                    p >=.
                    (Alloc.Vec.impl_1__len #t_Node #Alloc.Alloc.t_Global self.f_nodes <: usize)
                  then
                    self,
                    (Core_models.Result.Result_Err (Error_Internal <: t_Error)
                      <:
                      Core_models.Result.t_Result Prims.unit t_Error)
                    <:
                    (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                  else
                    let siblings:Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global =
                      match node.f_side <: t_Side with
                      | Side_Left  ->
                        Core_models.Clone.f_clone #(Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
                          #FStar.Tactics.Typeclasses.solve
                          (self.f_nodes.[ p ] <: t_Node).f_left
                      | Side_Right  ->
                        Core_models.Clone.f_clone #(Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
                          #FStar.Tactics.Typeclasses.solve
                          (self.f_nodes.[ p ] <: t_Node).f_right
                    in
                    let at:usize =
                      Alloc.Vec.impl_1__len #t_BirthId #Alloc.Alloc.t_Global siblings
                    in
                    (match
                        impl_Tree__rank (Alloc.Vec.impl_1__as_slice whole <: t_Slice t_BirthId)
                          node.f_right_origin
                        <:
                        Core_models.Result.t_Result usize t_Error
                      with
                      | Core_models.Result.Result_Ok rank ->
                        (match
                            Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
                              (Alloc.Vec.impl_1__len #t_BirthId #Alloc.Alloc.t_Global siblings
                                <:
                                usize)
                              (fun at temp_1_ ->
                                  let at:usize = at in
                                  let _:usize = temp_1_ in
                                  true)
                              at
                              (fun at i ->
                                  let at:usize = at in
                                  let i:usize = i in
                                  match
                                    impl_Tree__node self (siblings.[ i ] <: t_BirthId)
                                    <:
                                    Core_models.Result.t_Result t_Node t_Error
                                  with
                                  | Core_models.Result.Result_Ok old ->
                                    if
                                      match node.f_side <: t_Side with
                                      | Side_Right  -> true
                                      | _ -> false
                                    then
                                      match
                                        impl_Tree__rank (Alloc.Vec.impl_1__as_slice whole
                                            <:
                                            t_Slice t_BirthId)
                                          old.f_right_origin
                                        <:
                                        Core_models.Result.t_Result usize t_Error
                                      with
                                      | Core_models.Result.Result_Ok hoist23 ->
                                        let before:bool =
                                          rank >. hoist23 ||
                                          node.f_right_origin =. old.f_right_origin &&
                                          birth_lt node.f_id old.f_id
                                        in
                                        if before
                                        then
                                          let at:usize = i in
                                          Core_models.Ops.Control_flow.ControlFlow_Break
                                          (Core_models.Ops.Control_flow.ControlFlow_Continue
                                            ((), at <: (Prims.unit & usize))
                                            <:
                                            Core_models.Ops.Control_flow.t_ControlFlow
                                              (t_Tree &
                                                Core_models.Result.t_Result Prims.unit t_Error)
                                              (Prims.unit & usize))
                                          <:
                                          Core_models.Ops.Control_flow.t_ControlFlow
                                            (Core_models.Ops.Control_flow.t_ControlFlow
                                                (t_Tree &
                                                  Core_models.Result.t_Result Prims.unit t_Error)
                                                (Prims.unit & usize)) usize
                                        else
                                          Core_models.Ops.Control_flow.ControlFlow_Continue at
                                          <:
                                          Core_models.Ops.Control_flow.t_ControlFlow
                                            (Core_models.Ops.Control_flow.t_ControlFlow
                                                (t_Tree &
                                                  Core_models.Result.t_Result Prims.unit t_Error)
                                                (Prims.unit & usize)) usize
                                      | Core_models.Result.Result_Err err ->
                                        Core_models.Ops.Control_flow.ControlFlow_Break
                                        (Core_models.Ops.Control_flow.ControlFlow_Break
                                          (self,
                                            (Core_models.Result.Result_Err err
                                              <:
                                              Core_models.Result.t_Result Prims.unit t_Error)
                                            <:
                                            (t_Tree & Core_models.Result.t_Result Prims.unit t_Error
                                            ))
                                          <:
                                          Core_models.Ops.Control_flow.t_ControlFlow
                                            (t_Tree & Core_models.Result.t_Result Prims.unit t_Error
                                            ) (Prims.unit & usize))
                                        <:
                                        Core_models.Ops.Control_flow.t_ControlFlow
                                          (Core_models.Ops.Control_flow.t_ControlFlow
                                              (t_Tree &
                                                Core_models.Result.t_Result Prims.unit t_Error)
                                              (Prims.unit & usize)) usize
                                    else
                                      let before:bool = birth_lt node.f_id old.f_id in
                                      if before
                                      then
                                        let at:usize = i in
                                        Core_models.Ops.Control_flow.ControlFlow_Break
                                        (Core_models.Ops.Control_flow.ControlFlow_Continue
                                          ((), at <: (Prims.unit & usize))
                                          <:
                                          Core_models.Ops.Control_flow.t_ControlFlow
                                            (t_Tree & Core_models.Result.t_Result Prims.unit t_Error
                                            ) (Prims.unit & usize))
                                        <:
                                        Core_models.Ops.Control_flow.t_ControlFlow
                                          (Core_models.Ops.Control_flow.t_ControlFlow
                                              (t_Tree &
                                                Core_models.Result.t_Result Prims.unit t_Error)
                                              (Prims.unit & usize)) usize
                                      else
                                        Core_models.Ops.Control_flow.ControlFlow_Continue at
                                        <:
                                        Core_models.Ops.Control_flow.t_ControlFlow
                                          (Core_models.Ops.Control_flow.t_ControlFlow
                                              (t_Tree &
                                                Core_models.Result.t_Result Prims.unit t_Error)
                                              (Prims.unit & usize)) usize
                                  | Core_models.Result.Result_Err err ->
                                    Core_models.Ops.Control_flow.ControlFlow_Break
                                    (Core_models.Ops.Control_flow.ControlFlow_Break
                                      (self,
                                        (Core_models.Result.Result_Err err
                                          <:
                                          Core_models.Result.t_Result Prims.unit t_Error)
                                        <:
                                        (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
                                      <:
                                      Core_models.Ops.Control_flow.t_ControlFlow
                                        (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                        (Prims.unit & usize))
                                    <:
                                    Core_models.Ops.Control_flow.t_ControlFlow
                                      (Core_models.Ops.Control_flow.t_ControlFlow
                                          (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                          (Prims.unit & usize)) usize)
                            <:
                            Core_models.Ops.Control_flow.t_ControlFlow
                              (t_Tree & Core_models.Result.t_Result Prims.unit t_Error) usize
                          with
                          | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
                          | Core_models.Ops.Control_flow.ControlFlow_Continue at ->
                            match parent <: Core_models.Option.t_Option usize with
                            | Core_models.Option.Option_Some p ->
                              if
                                p >=.
                                (Alloc.Vec.impl_1__len #t_Node #Alloc.Alloc.t_Global self.f_nodes
                                  <:
                                  usize)
                              then
                                self,
                                (Core_models.Result.Result_Err (Error_Internal <: t_Error)
                                  <:
                                  Core_models.Result.t_Result Prims.unit t_Error)
                                <:
                                (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                              else
                                (match node.f_side <: t_Side with
                                  | Side_Left  ->
                                    let
                                    (tmp0: Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global),
                                    (out: Core_models.Result.t_Result Prims.unit t_Error) =
                                      insert #t_BirthId
                                        (self.f_nodes.[ p ] <: t_Node).f_left
                                        at
                                        node.f_id
                                    in
                                    let self:t_Tree =
                                      {
                                        self with
                                        f_nodes
                                        =
                                        Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                                              (Alloc.Vec.impl_1__as_slice self.f_nodes
                                                <:
                                                t_Slice t_Node)
                                              p
                                              ({ (self.f_nodes.[ p ] <: t_Node) with f_left = tmp0 }
                                                <:
                                                t_Node)
                                            <:
                                            t_Slice t_Node)
                                      }
                                      <:
                                      t_Tree
                                    in
                                    (match
                                        out <: Core_models.Result.t_Result Prims.unit t_Error
                                      with
                                      | Core_models.Result.Result_Ok ok ->
                                        let node:t_Node =
                                          { node with f_left = Alloc.Vec.impl__new #t_BirthId () }
                                          <:
                                          t_Node
                                        in
                                        let node:t_Node =
                                          { node with f_right = Alloc.Vec.impl__new #t_BirthId () }
                                          <:
                                          t_Node
                                        in
                                        let
                                        (tmp0: Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global),
                                        (out: Core_models.Result.t_Result Prims.unit t_Error) =
                                          push #t_Node self.f_nodes node
                                        in
                                        let self:t_Tree = { self with f_nodes = tmp0 } <: t_Tree in
                                        (match
                                            out <: Core_models.Result.t_Result Prims.unit t_Error
                                          with
                                          | Core_models.Result.Result_Ok _ ->
                                            let hax_temp_output:Core_models.Result.t_Result
                                              Prims.unit t_Error =
                                              Core_models.Result.Result_Ok (() <: Prims.unit)
                                              <:
                                              Core_models.Result.t_Result Prims.unit t_Error
                                            in
                                            self, hax_temp_output
                                            <:
                                            (t_Tree & Core_models.Result.t_Result Prims.unit t_Error
                                            )
                                          | Core_models.Result.Result_Err err ->
                                            self,
                                            (Core_models.Result.Result_Err err
                                              <:
                                              Core_models.Result.t_Result Prims.unit t_Error)
                                            <:
                                            (t_Tree & Core_models.Result.t_Result Prims.unit t_Error
                                            ))
                                      | Core_models.Result.Result_Err err ->
                                        self,
                                        (Core_models.Result.Result_Err err
                                          <:
                                          Core_models.Result.t_Result Prims.unit t_Error)
                                        <:
                                        (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
                                  | Side_Right  ->
                                    let
                                    (tmp0: Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global),
                                    (out: Core_models.Result.t_Result Prims.unit t_Error) =
                                      insert #t_BirthId
                                        (self.f_nodes.[ p ] <: t_Node).f_right
                                        at
                                        node.f_id
                                    in
                                    let self:t_Tree =
                                      {
                                        self with
                                        f_nodes
                                        =
                                        Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                                              (Alloc.Vec.impl_1__as_slice self.f_nodes
                                                <:
                                                t_Slice t_Node)
                                              p
                                              ({
                                                  (self.f_nodes.[ p ] <: t_Node) with
                                                  f_right = tmp0
                                                }
                                                <:
                                                t_Node)
                                            <:
                                            t_Slice t_Node)
                                      }
                                      <:
                                      t_Tree
                                    in
                                    match out <: Core_models.Result.t_Result Prims.unit t_Error with
                                    | Core_models.Result.Result_Ok ok ->
                                      let node:t_Node =
                                        { node with f_left = Alloc.Vec.impl__new #t_BirthId () }
                                        <:
                                        t_Node
                                      in
                                      let node:t_Node =
                                        { node with f_right = Alloc.Vec.impl__new #t_BirthId () }
                                        <:
                                        t_Node
                                      in
                                      let
                                      (tmp0: Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global),
                                      (out: Core_models.Result.t_Result Prims.unit t_Error) =
                                        push #t_Node self.f_nodes node
                                      in
                                      let self:t_Tree = { self with f_nodes = tmp0 } <: t_Tree in
                                      (match
                                          out <: Core_models.Result.t_Result Prims.unit t_Error
                                        with
                                        | Core_models.Result.Result_Ok _ ->
                                          let hax_temp_output:Core_models.Result.t_Result Prims.unit
                                            t_Error =
                                            Core_models.Result.Result_Ok (() <: Prims.unit)
                                            <:
                                            Core_models.Result.t_Result Prims.unit t_Error
                                          in
                                          self, hax_temp_output
                                          <:
                                          (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                        | Core_models.Result.Result_Err err ->
                                          self,
                                          (Core_models.Result.Result_Err err
                                            <:
                                            Core_models.Result.t_Result Prims.unit t_Error)
                                          <:
                                          (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
                                    | Core_models.Result.Result_Err err ->
                                      self,
                                      (Core_models.Result.Result_Err err
                                        <:
                                        Core_models.Result.t_Result Prims.unit t_Error)
                                      <:
                                      (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
                            | Core_models.Option.Option_None  ->
                              let
                              (tmp0: Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global),
                              (out: Core_models.Result.t_Result Prims.unit t_Error) =
                                insert #t_BirthId self.f_root_right at node.f_id
                              in
                              let self:t_Tree = { self with f_root_right = tmp0 } <: t_Tree in
                              match out <: Core_models.Result.t_Result Prims.unit t_Error with
                              | Core_models.Result.Result_Ok ok ->
                                let node:t_Node =
                                  { node with f_left = Alloc.Vec.impl__new #t_BirthId () } <: t_Node
                                in
                                let node:t_Node =
                                  { node with f_right = Alloc.Vec.impl__new #t_BirthId () }
                                  <:
                                  t_Node
                                in
                                let
                                (tmp0: Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global),
                                (out: Core_models.Result.t_Result Prims.unit t_Error) =
                                  push #t_Node self.f_nodes node
                                in
                                let self:t_Tree = { self with f_nodes = tmp0 } <: t_Tree in
                                (match out <: Core_models.Result.t_Result Prims.unit t_Error with
                                  | Core_models.Result.Result_Ok _ ->
                                    let hax_temp_output:Core_models.Result.t_Result Prims.unit
                                      t_Error =
                                      Core_models.Result.Result_Ok (() <: Prims.unit)
                                      <:
                                      Core_models.Result.t_Result Prims.unit t_Error
                                    in
                                    self, hax_temp_output
                                    <:
                                    (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                  | Core_models.Result.Result_Err err ->
                                    self,
                                    (Core_models.Result.Result_Err err
                                      <:
                                      Core_models.Result.t_Result Prims.unit t_Error)
                                    <:
                                    (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
                              | Core_models.Result.Result_Err err ->
                                self,
                                (Core_models.Result.Result_Err err
                                  <:
                                  Core_models.Result.t_Result Prims.unit t_Error)
                                <:
                                (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
                      | Core_models.Result.Result_Err err ->
                        self,
                        (Core_models.Result.Result_Err err
                          <:
                          Core_models.Result.t_Result Prims.unit t_Error)
                        <:
                        (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
                | Core_models.Option.Option_None  ->
                  if
                    ~.(match node.f_side <: t_Side with
                      | Side_Right  -> true
                      | _ -> false)
                  then
                    self,
                    (Core_models.Result.Result_Err (Error_Internal <: t_Error)
                      <:
                      Core_models.Result.t_Result Prims.unit t_Error)
                    <:
                    (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                  else
                    let siblings:Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global =
                      Core_models.Clone.f_clone #(Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
                        #FStar.Tactics.Typeclasses.solve
                        self.f_root_right
                    in
                    let at:usize =
                      Alloc.Vec.impl_1__len #t_BirthId #Alloc.Alloc.t_Global siblings
                    in
                    match
                      impl_Tree__rank (Alloc.Vec.impl_1__as_slice whole <: t_Slice t_BirthId)
                        node.f_right_origin
                      <:
                      Core_models.Result.t_Result usize t_Error
                    with
                    | Core_models.Result.Result_Ok rank ->
                      (match
                          Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
                            (Alloc.Vec.impl_1__len #t_BirthId #Alloc.Alloc.t_Global siblings
                              <:
                              usize)
                            (fun at temp_1_ ->
                                let at:usize = at in
                                let _:usize = temp_1_ in
                                true)
                            at
                            (fun at i ->
                                let at:usize = at in
                                let i:usize = i in
                                match
                                  impl_Tree__node self (siblings.[ i ] <: t_BirthId)
                                  <:
                                  Core_models.Result.t_Result t_Node t_Error
                                with
                                | Core_models.Result.Result_Ok old ->
                                  if
                                    match node.f_side <: t_Side with
                                    | Side_Right  -> true
                                    | _ -> false
                                  then
                                    match
                                      impl_Tree__rank (Alloc.Vec.impl_1__as_slice whole
                                          <:
                                          t_Slice t_BirthId)
                                        old.f_right_origin
                                      <:
                                      Core_models.Result.t_Result usize t_Error
                                    with
                                    | Core_models.Result.Result_Ok hoist23 ->
                                      let before:bool =
                                        rank >. hoist23 ||
                                        node.f_right_origin =. old.f_right_origin &&
                                        birth_lt node.f_id old.f_id
                                      in
                                      if before
                                      then
                                        let at:usize = i in
                                        Core_models.Ops.Control_flow.ControlFlow_Break
                                        (Core_models.Ops.Control_flow.ControlFlow_Continue
                                          ((), at <: (Prims.unit & usize))
                                          <:
                                          Core_models.Ops.Control_flow.t_ControlFlow
                                            (t_Tree & Core_models.Result.t_Result Prims.unit t_Error
                                            ) (Prims.unit & usize))
                                        <:
                                        Core_models.Ops.Control_flow.t_ControlFlow
                                          (Core_models.Ops.Control_flow.t_ControlFlow
                                              (t_Tree &
                                                Core_models.Result.t_Result Prims.unit t_Error)
                                              (Prims.unit & usize)) usize
                                      else
                                        Core_models.Ops.Control_flow.ControlFlow_Continue at
                                        <:
                                        Core_models.Ops.Control_flow.t_ControlFlow
                                          (Core_models.Ops.Control_flow.t_ControlFlow
                                              (t_Tree &
                                                Core_models.Result.t_Result Prims.unit t_Error)
                                              (Prims.unit & usize)) usize
                                    | Core_models.Result.Result_Err err ->
                                      Core_models.Ops.Control_flow.ControlFlow_Break
                                      (Core_models.Ops.Control_flow.ControlFlow_Break
                                        (self,
                                          (Core_models.Result.Result_Err err
                                            <:
                                            Core_models.Result.t_Result Prims.unit t_Error)
                                          <:
                                          (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
                                        <:
                                        Core_models.Ops.Control_flow.t_ControlFlow
                                          (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                          (Prims.unit & usize))
                                      <:
                                      Core_models.Ops.Control_flow.t_ControlFlow
                                        (Core_models.Ops.Control_flow.t_ControlFlow
                                            (t_Tree & Core_models.Result.t_Result Prims.unit t_Error
                                            ) (Prims.unit & usize)) usize
                                  else
                                    let before:bool = birth_lt node.f_id old.f_id in
                                    if before
                                    then
                                      let at:usize = i in
                                      Core_models.Ops.Control_flow.ControlFlow_Break
                                      (Core_models.Ops.Control_flow.ControlFlow_Continue
                                        ((), at <: (Prims.unit & usize))
                                        <:
                                        Core_models.Ops.Control_flow.t_ControlFlow
                                          (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                          (Prims.unit & usize))
                                      <:
                                      Core_models.Ops.Control_flow.t_ControlFlow
                                        (Core_models.Ops.Control_flow.t_ControlFlow
                                            (t_Tree & Core_models.Result.t_Result Prims.unit t_Error
                                            ) (Prims.unit & usize)) usize
                                    else
                                      Core_models.Ops.Control_flow.ControlFlow_Continue at
                                      <:
                                      Core_models.Ops.Control_flow.t_ControlFlow
                                        (Core_models.Ops.Control_flow.t_ControlFlow
                                            (t_Tree & Core_models.Result.t_Result Prims.unit t_Error
                                            ) (Prims.unit & usize)) usize
                                | Core_models.Result.Result_Err err ->
                                  Core_models.Ops.Control_flow.ControlFlow_Break
                                  (Core_models.Ops.Control_flow.ControlFlow_Break
                                    (self,
                                      (Core_models.Result.Result_Err err
                                        <:
                                        Core_models.Result.t_Result Prims.unit t_Error)
                                      <:
                                      (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
                                    <:
                                    Core_models.Ops.Control_flow.t_ControlFlow
                                      (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                      (Prims.unit & usize))
                                  <:
                                  Core_models.Ops.Control_flow.t_ControlFlow
                                    (Core_models.Ops.Control_flow.t_ControlFlow
                                        (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                        (Prims.unit & usize)) usize)
                          <:
                          Core_models.Ops.Control_flow.t_ControlFlow
                            (t_Tree & Core_models.Result.t_Result Prims.unit t_Error) usize
                        with
                        | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
                        | Core_models.Ops.Control_flow.ControlFlow_Continue at ->
                          match parent <: Core_models.Option.t_Option usize with
                          | Core_models.Option.Option_Some p ->
                            if
                              p >=.
                              (Alloc.Vec.impl_1__len #t_Node #Alloc.Alloc.t_Global self.f_nodes
                                <:
                                usize)
                            then
                              self,
                              (Core_models.Result.Result_Err (Error_Internal <: t_Error)
                                <:
                                Core_models.Result.t_Result Prims.unit t_Error)
                              <:
                              (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                            else
                              (match node.f_side <: t_Side with
                                | Side_Left  ->
                                  let
                                  (tmp0: Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global),
                                  (out: Core_models.Result.t_Result Prims.unit t_Error) =
                                    insert #t_BirthId
                                      (self.f_nodes.[ p ] <: t_Node).f_left
                                      at
                                      node.f_id
                                  in
                                  let self:t_Tree =
                                    {
                                      self with
                                      f_nodes
                                      =
                                      Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                                            (Alloc.Vec.impl_1__as_slice self.f_nodes
                                              <:
                                              t_Slice t_Node)
                                            p
                                            ({ (self.f_nodes.[ p ] <: t_Node) with f_left = tmp0 }
                                              <:
                                              t_Node)
                                          <:
                                          t_Slice t_Node)
                                    }
                                    <:
                                    t_Tree
                                  in
                                  (match out <: Core_models.Result.t_Result Prims.unit t_Error with
                                    | Core_models.Result.Result_Ok ok ->
                                      let node:t_Node =
                                        { node with f_left = Alloc.Vec.impl__new #t_BirthId () }
                                        <:
                                        t_Node
                                      in
                                      let node:t_Node =
                                        { node with f_right = Alloc.Vec.impl__new #t_BirthId () }
                                        <:
                                        t_Node
                                      in
                                      let
                                      (tmp0: Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global),
                                      (out: Core_models.Result.t_Result Prims.unit t_Error) =
                                        push #t_Node self.f_nodes node
                                      in
                                      let self:t_Tree = { self with f_nodes = tmp0 } <: t_Tree in
                                      (match
                                          out <: Core_models.Result.t_Result Prims.unit t_Error
                                        with
                                        | Core_models.Result.Result_Ok _ ->
                                          let hax_temp_output:Core_models.Result.t_Result Prims.unit
                                            t_Error =
                                            Core_models.Result.Result_Ok (() <: Prims.unit)
                                            <:
                                            Core_models.Result.t_Result Prims.unit t_Error
                                          in
                                          self, hax_temp_output
                                          <:
                                          (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                        | Core_models.Result.Result_Err err ->
                                          self,
                                          (Core_models.Result.Result_Err err
                                            <:
                                            Core_models.Result.t_Result Prims.unit t_Error)
                                          <:
                                          (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
                                    | Core_models.Result.Result_Err err ->
                                      self,
                                      (Core_models.Result.Result_Err err
                                        <:
                                        Core_models.Result.t_Result Prims.unit t_Error)
                                      <:
                                      (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
                                | Side_Right  ->
                                  let
                                  (tmp0: Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global),
                                  (out: Core_models.Result.t_Result Prims.unit t_Error) =
                                    insert #t_BirthId
                                      (self.f_nodes.[ p ] <: t_Node).f_right
                                      at
                                      node.f_id
                                  in
                                  let self:t_Tree =
                                    {
                                      self with
                                      f_nodes
                                      =
                                      Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                                            (Alloc.Vec.impl_1__as_slice self.f_nodes
                                              <:
                                              t_Slice t_Node)
                                            p
                                            ({ (self.f_nodes.[ p ] <: t_Node) with f_right = tmp0 }
                                              <:
                                              t_Node)
                                          <:
                                          t_Slice t_Node)
                                    }
                                    <:
                                    t_Tree
                                  in
                                  match out <: Core_models.Result.t_Result Prims.unit t_Error with
                                  | Core_models.Result.Result_Ok ok ->
                                    let node:t_Node =
                                      { node with f_left = Alloc.Vec.impl__new #t_BirthId () }
                                      <:
                                      t_Node
                                    in
                                    let node:t_Node =
                                      { node with f_right = Alloc.Vec.impl__new #t_BirthId () }
                                      <:
                                      t_Node
                                    in
                                    let
                                    (tmp0: Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global),
                                    (out: Core_models.Result.t_Result Prims.unit t_Error) =
                                      push #t_Node self.f_nodes node
                                    in
                                    let self:t_Tree = { self with f_nodes = tmp0 } <: t_Tree in
                                    (match
                                        out <: Core_models.Result.t_Result Prims.unit t_Error
                                      with
                                      | Core_models.Result.Result_Ok _ ->
                                        let hax_temp_output:Core_models.Result.t_Result Prims.unit
                                          t_Error =
                                          Core_models.Result.Result_Ok (() <: Prims.unit)
                                          <:
                                          Core_models.Result.t_Result Prims.unit t_Error
                                        in
                                        self, hax_temp_output
                                        <:
                                        (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                      | Core_models.Result.Result_Err err ->
                                        self,
                                        (Core_models.Result.Result_Err err
                                          <:
                                          Core_models.Result.t_Result Prims.unit t_Error)
                                        <:
                                        (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
                                  | Core_models.Result.Result_Err err ->
                                    self,
                                    (Core_models.Result.Result_Err err
                                      <:
                                      Core_models.Result.t_Result Prims.unit t_Error)
                                    <:
                                    (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
                          | Core_models.Option.Option_None  ->
                            let
                            (tmp0: Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global),
                            (out: Core_models.Result.t_Result Prims.unit t_Error) =
                              insert #t_BirthId self.f_root_right at node.f_id
                            in
                            let self:t_Tree = { self with f_root_right = tmp0 } <: t_Tree in
                            match out <: Core_models.Result.t_Result Prims.unit t_Error with
                            | Core_models.Result.Result_Ok ok ->
                              let node:t_Node =
                                { node with f_left = Alloc.Vec.impl__new #t_BirthId () } <: t_Node
                              in
                              let node:t_Node =
                                { node with f_right = Alloc.Vec.impl__new #t_BirthId () } <: t_Node
                              in
                              let
                              (tmp0: Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global),
                              (out: Core_models.Result.t_Result Prims.unit t_Error) =
                                push #t_Node self.f_nodes node
                              in
                              let self:t_Tree = { self with f_nodes = tmp0 } <: t_Tree in
                              (match out <: Core_models.Result.t_Result Prims.unit t_Error with
                                | Core_models.Result.Result_Ok _ ->
                                  let hax_temp_output:Core_models.Result.t_Result Prims.unit t_Error
                                  =
                                    Core_models.Result.Result_Ok (() <: Prims.unit)
                                    <:
                                    Core_models.Result.t_Result Prims.unit t_Error
                                  in
                                  self, hax_temp_output
                                  <:
                                  (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                | Core_models.Result.Result_Err err ->
                                  self,
                                  (Core_models.Result.Result_Err err
                                    <:
                                    Core_models.Result.t_Result Prims.unit t_Error)
                                  <:
                                  (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
                            | Core_models.Result.Result_Err err ->
                              self,
                              (Core_models.Result.Result_Err err
                                <:
                                Core_models.Result.t_Result Prims.unit t_Error)
                              <:
                              (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
                    | Core_models.Result.Result_Err err ->
                      self,
                      (Core_models.Result.Result_Err err
                        <:
                        Core_models.Result.t_Result Prims.unit t_Error)
                      <:
                      (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
            | Core_models.Result.Result_Err err ->
              self,
              (Core_models.Result.Result_Err err <: Core_models.Result.t_Result Prims.unit t_Error)
              <:
              (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
        | Core_models.Option.Option_None  ->
          let parent:Core_models.Option.t_Option usize =
            Core_models.Option.Option_None <: Core_models.Option.t_Option usize
          in
          match parent <: Core_models.Option.t_Option usize with
          | Core_models.Option.Option_Some p ->
            if p >=. (Alloc.Vec.impl_1__len #t_Node #Alloc.Alloc.t_Global self.f_nodes <: usize)
            then
              self,
              (Core_models.Result.Result_Err (Error_Internal <: t_Error)
                <:
                Core_models.Result.t_Result Prims.unit t_Error)
              <:
              (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
            else
              let siblings:Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global =
                match node.f_side <: t_Side with
                | Side_Left  ->
                  Core_models.Clone.f_clone #(Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
                    #FStar.Tactics.Typeclasses.solve
                    (self.f_nodes.[ p ] <: t_Node).f_left
                | Side_Right  ->
                  Core_models.Clone.f_clone #(Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
                    #FStar.Tactics.Typeclasses.solve
                    (self.f_nodes.[ p ] <: t_Node).f_right
              in
              let at:usize = Alloc.Vec.impl_1__len #t_BirthId #Alloc.Alloc.t_Global siblings in
              (match
                  impl_Tree__rank (Alloc.Vec.impl_1__as_slice whole <: t_Slice t_BirthId)
                    node.f_right_origin
                  <:
                  Core_models.Result.t_Result usize t_Error
                with
                | Core_models.Result.Result_Ok rank ->
                  (match
                      Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
                        (Alloc.Vec.impl_1__len #t_BirthId #Alloc.Alloc.t_Global siblings <: usize)
                        (fun at temp_1_ ->
                            let at:usize = at in
                            let _:usize = temp_1_ in
                            true)
                        at
                        (fun at i ->
                            let at:usize = at in
                            let i:usize = i in
                            match
                              impl_Tree__node self (siblings.[ i ] <: t_BirthId)
                              <:
                              Core_models.Result.t_Result t_Node t_Error
                            with
                            | Core_models.Result.Result_Ok old ->
                              if
                                match node.f_side <: t_Side with
                                | Side_Right  -> true
                                | _ -> false
                              then
                                match
                                  impl_Tree__rank (Alloc.Vec.impl_1__as_slice whole
                                      <:
                                      t_Slice t_BirthId)
                                    old.f_right_origin
                                  <:
                                  Core_models.Result.t_Result usize t_Error
                                with
                                | Core_models.Result.Result_Ok hoist23 ->
                                  let before:bool =
                                    rank >. hoist23 ||
                                    node.f_right_origin =. old.f_right_origin &&
                                    birth_lt node.f_id old.f_id
                                  in
                                  if before
                                  then
                                    let at:usize = i in
                                    Core_models.Ops.Control_flow.ControlFlow_Break
                                    (Core_models.Ops.Control_flow.ControlFlow_Continue
                                      ((), at <: (Prims.unit & usize))
                                      <:
                                      Core_models.Ops.Control_flow.t_ControlFlow
                                        (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                        (Prims.unit & usize))
                                    <:
                                    Core_models.Ops.Control_flow.t_ControlFlow
                                      (Core_models.Ops.Control_flow.t_ControlFlow
                                          (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                          (Prims.unit & usize)) usize
                                  else
                                    Core_models.Ops.Control_flow.ControlFlow_Continue at
                                    <:
                                    Core_models.Ops.Control_flow.t_ControlFlow
                                      (Core_models.Ops.Control_flow.t_ControlFlow
                                          (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                          (Prims.unit & usize)) usize
                                | Core_models.Result.Result_Err err ->
                                  Core_models.Ops.Control_flow.ControlFlow_Break
                                  (Core_models.Ops.Control_flow.ControlFlow_Break
                                    (self,
                                      (Core_models.Result.Result_Err err
                                        <:
                                        Core_models.Result.t_Result Prims.unit t_Error)
                                      <:
                                      (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
                                    <:
                                    Core_models.Ops.Control_flow.t_ControlFlow
                                      (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                      (Prims.unit & usize))
                                  <:
                                  Core_models.Ops.Control_flow.t_ControlFlow
                                    (Core_models.Ops.Control_flow.t_ControlFlow
                                        (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                        (Prims.unit & usize)) usize
                              else
                                let before:bool = birth_lt node.f_id old.f_id in
                                if before
                                then
                                  let at:usize = i in
                                  Core_models.Ops.Control_flow.ControlFlow_Break
                                  (Core_models.Ops.Control_flow.ControlFlow_Continue
                                    ((), at <: (Prims.unit & usize))
                                    <:
                                    Core_models.Ops.Control_flow.t_ControlFlow
                                      (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                      (Prims.unit & usize))
                                  <:
                                  Core_models.Ops.Control_flow.t_ControlFlow
                                    (Core_models.Ops.Control_flow.t_ControlFlow
                                        (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                        (Prims.unit & usize)) usize
                                else
                                  Core_models.Ops.Control_flow.ControlFlow_Continue at
                                  <:
                                  Core_models.Ops.Control_flow.t_ControlFlow
                                    (Core_models.Ops.Control_flow.t_ControlFlow
                                        (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                        (Prims.unit & usize)) usize
                            | Core_models.Result.Result_Err err ->
                              Core_models.Ops.Control_flow.ControlFlow_Break
                              (Core_models.Ops.Control_flow.ControlFlow_Break
                                (self,
                                  (Core_models.Result.Result_Err err
                                    <:
                                    Core_models.Result.t_Result Prims.unit t_Error)
                                  <:
                                  (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
                                <:
                                Core_models.Ops.Control_flow.t_ControlFlow
                                  (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                  (Prims.unit & usize))
                              <:
                              Core_models.Ops.Control_flow.t_ControlFlow
                                (Core_models.Ops.Control_flow.t_ControlFlow
                                    (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                    (Prims.unit & usize)) usize)
                      <:
                      Core_models.Ops.Control_flow.t_ControlFlow
                        (t_Tree & Core_models.Result.t_Result Prims.unit t_Error) usize
                    with
                    | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
                    | Core_models.Ops.Control_flow.ControlFlow_Continue at ->
                      match parent <: Core_models.Option.t_Option usize with
                      | Core_models.Option.Option_Some p ->
                        if
                          p >=.
                          (Alloc.Vec.impl_1__len #t_Node #Alloc.Alloc.t_Global self.f_nodes <: usize
                          )
                        then
                          self,
                          (Core_models.Result.Result_Err (Error_Internal <: t_Error)
                            <:
                            Core_models.Result.t_Result Prims.unit t_Error)
                          <:
                          (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                        else
                          (match node.f_side <: t_Side with
                            | Side_Left  ->
                              let
                              (tmp0: Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global),
                              (out: Core_models.Result.t_Result Prims.unit t_Error) =
                                insert #t_BirthId (self.f_nodes.[ p ] <: t_Node).f_left at node.f_id
                              in
                              let self:t_Tree =
                                {
                                  self with
                                  f_nodes
                                  =
                                  Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                                        (Alloc.Vec.impl_1__as_slice self.f_nodes <: t_Slice t_Node)
                                        p
                                        ({ (self.f_nodes.[ p ] <: t_Node) with f_left = tmp0 }
                                          <:
                                          t_Node)
                                      <:
                                      t_Slice t_Node)
                                }
                                <:
                                t_Tree
                              in
                              (match out <: Core_models.Result.t_Result Prims.unit t_Error with
                                | Core_models.Result.Result_Ok ok ->
                                  let node:t_Node =
                                    { node with f_left = Alloc.Vec.impl__new #t_BirthId () }
                                    <:
                                    t_Node
                                  in
                                  let node:t_Node =
                                    { node with f_right = Alloc.Vec.impl__new #t_BirthId () }
                                    <:
                                    t_Node
                                  in
                                  let
                                  (tmp0: Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global),
                                  (out: Core_models.Result.t_Result Prims.unit t_Error) =
                                    push #t_Node self.f_nodes node
                                  in
                                  let self:t_Tree = { self with f_nodes = tmp0 } <: t_Tree in
                                  (match out <: Core_models.Result.t_Result Prims.unit t_Error with
                                    | Core_models.Result.Result_Ok _ ->
                                      let hax_temp_output:Core_models.Result.t_Result Prims.unit
                                        t_Error =
                                        Core_models.Result.Result_Ok (() <: Prims.unit)
                                        <:
                                        Core_models.Result.t_Result Prims.unit t_Error
                                      in
                                      self, hax_temp_output
                                      <:
                                      (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                    | Core_models.Result.Result_Err err ->
                                      self,
                                      (Core_models.Result.Result_Err err
                                        <:
                                        Core_models.Result.t_Result Prims.unit t_Error)
                                      <:
                                      (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
                                | Core_models.Result.Result_Err err ->
                                  self,
                                  (Core_models.Result.Result_Err err
                                    <:
                                    Core_models.Result.t_Result Prims.unit t_Error)
                                  <:
                                  (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
                            | Side_Right  ->
                              let
                              (tmp0: Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global),
                              (out: Core_models.Result.t_Result Prims.unit t_Error) =
                                insert #t_BirthId
                                  (self.f_nodes.[ p ] <: t_Node).f_right
                                  at
                                  node.f_id
                              in
                              let self:t_Tree =
                                {
                                  self with
                                  f_nodes
                                  =
                                  Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                                        (Alloc.Vec.impl_1__as_slice self.f_nodes <: t_Slice t_Node)
                                        p
                                        ({ (self.f_nodes.[ p ] <: t_Node) with f_right = tmp0 }
                                          <:
                                          t_Node)
                                      <:
                                      t_Slice t_Node)
                                }
                                <:
                                t_Tree
                              in
                              match out <: Core_models.Result.t_Result Prims.unit t_Error with
                              | Core_models.Result.Result_Ok ok ->
                                let node:t_Node =
                                  { node with f_left = Alloc.Vec.impl__new #t_BirthId () } <: t_Node
                                in
                                let node:t_Node =
                                  { node with f_right = Alloc.Vec.impl__new #t_BirthId () }
                                  <:
                                  t_Node
                                in
                                let
                                (tmp0: Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global),
                                (out: Core_models.Result.t_Result Prims.unit t_Error) =
                                  push #t_Node self.f_nodes node
                                in
                                let self:t_Tree = { self with f_nodes = tmp0 } <: t_Tree in
                                (match out <: Core_models.Result.t_Result Prims.unit t_Error with
                                  | Core_models.Result.Result_Ok _ ->
                                    let hax_temp_output:Core_models.Result.t_Result Prims.unit
                                      t_Error =
                                      Core_models.Result.Result_Ok (() <: Prims.unit)
                                      <:
                                      Core_models.Result.t_Result Prims.unit t_Error
                                    in
                                    self, hax_temp_output
                                    <:
                                    (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                  | Core_models.Result.Result_Err err ->
                                    self,
                                    (Core_models.Result.Result_Err err
                                      <:
                                      Core_models.Result.t_Result Prims.unit t_Error)
                                    <:
                                    (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
                              | Core_models.Result.Result_Err err ->
                                self,
                                (Core_models.Result.Result_Err err
                                  <:
                                  Core_models.Result.t_Result Prims.unit t_Error)
                                <:
                                (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
                      | Core_models.Option.Option_None  ->
                        let
                        (tmp0: Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global),
                        (out: Core_models.Result.t_Result Prims.unit t_Error) =
                          insert #t_BirthId self.f_root_right at node.f_id
                        in
                        let self:t_Tree = { self with f_root_right = tmp0 } <: t_Tree in
                        match out <: Core_models.Result.t_Result Prims.unit t_Error with
                        | Core_models.Result.Result_Ok ok ->
                          let node:t_Node =
                            { node with f_left = Alloc.Vec.impl__new #t_BirthId () } <: t_Node
                          in
                          let node:t_Node =
                            { node with f_right = Alloc.Vec.impl__new #t_BirthId () } <: t_Node
                          in
                          let
                          (tmp0: Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global),
                          (out: Core_models.Result.t_Result Prims.unit t_Error) =
                            push #t_Node self.f_nodes node
                          in
                          let self:t_Tree = { self with f_nodes = tmp0 } <: t_Tree in
                          (match out <: Core_models.Result.t_Result Prims.unit t_Error with
                            | Core_models.Result.Result_Ok _ ->
                              let hax_temp_output:Core_models.Result.t_Result Prims.unit t_Error =
                                Core_models.Result.Result_Ok (() <: Prims.unit)
                                <:
                                Core_models.Result.t_Result Prims.unit t_Error
                              in
                              self, hax_temp_output
                              <:
                              (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                            | Core_models.Result.Result_Err err ->
                              self,
                              (Core_models.Result.Result_Err err
                                <:
                                Core_models.Result.t_Result Prims.unit t_Error)
                              <:
                              (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
                        | Core_models.Result.Result_Err err ->
                          self,
                          (Core_models.Result.Result_Err err
                            <:
                            Core_models.Result.t_Result Prims.unit t_Error)
                          <:
                          (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
                | Core_models.Result.Result_Err err ->
                  self,
                  (Core_models.Result.Result_Err err
                    <:
                    Core_models.Result.t_Result Prims.unit t_Error)
                  <:
                  (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
          | Core_models.Option.Option_None  ->
            if
              ~.(match node.f_side <: t_Side with
                | Side_Right  -> true
                | _ -> false)
            then
              self,
              (Core_models.Result.Result_Err (Error_Internal <: t_Error)
                <:
                Core_models.Result.t_Result Prims.unit t_Error)
              <:
              (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
            else
              let siblings:Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global =
                Core_models.Clone.f_clone #(Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
                  #FStar.Tactics.Typeclasses.solve
                  self.f_root_right
              in
              let at:usize = Alloc.Vec.impl_1__len #t_BirthId #Alloc.Alloc.t_Global siblings in
              match
                impl_Tree__rank (Alloc.Vec.impl_1__as_slice whole <: t_Slice t_BirthId)
                  node.f_right_origin
                <:
                Core_models.Result.t_Result usize t_Error
              with
              | Core_models.Result.Result_Ok rank ->
                (match
                    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
                      (Alloc.Vec.impl_1__len #t_BirthId #Alloc.Alloc.t_Global siblings <: usize)
                      (fun at temp_1_ ->
                          let at:usize = at in
                          let _:usize = temp_1_ in
                          true)
                      at
                      (fun at i ->
                          let at:usize = at in
                          let i:usize = i in
                          match
                            impl_Tree__node self (siblings.[ i ] <: t_BirthId)
                            <:
                            Core_models.Result.t_Result t_Node t_Error
                          with
                          | Core_models.Result.Result_Ok old ->
                            if
                              match node.f_side <: t_Side with
                              | Side_Right  -> true
                              | _ -> false
                            then
                              match
                                impl_Tree__rank (Alloc.Vec.impl_1__as_slice whole
                                    <:
                                    t_Slice t_BirthId)
                                  old.f_right_origin
                                <:
                                Core_models.Result.t_Result usize t_Error
                              with
                              | Core_models.Result.Result_Ok hoist23 ->
                                let before:bool =
                                  rank >. hoist23 ||
                                  node.f_right_origin =. old.f_right_origin &&
                                  birth_lt node.f_id old.f_id
                                in
                                if before
                                then
                                  let at:usize = i in
                                  Core_models.Ops.Control_flow.ControlFlow_Break
                                  (Core_models.Ops.Control_flow.ControlFlow_Continue
                                    ((), at <: (Prims.unit & usize))
                                    <:
                                    Core_models.Ops.Control_flow.t_ControlFlow
                                      (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                      (Prims.unit & usize))
                                  <:
                                  Core_models.Ops.Control_flow.t_ControlFlow
                                    (Core_models.Ops.Control_flow.t_ControlFlow
                                        (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                        (Prims.unit & usize)) usize
                                else
                                  Core_models.Ops.Control_flow.ControlFlow_Continue at
                                  <:
                                  Core_models.Ops.Control_flow.t_ControlFlow
                                    (Core_models.Ops.Control_flow.t_ControlFlow
                                        (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                        (Prims.unit & usize)) usize
                              | Core_models.Result.Result_Err err ->
                                Core_models.Ops.Control_flow.ControlFlow_Break
                                (Core_models.Ops.Control_flow.ControlFlow_Break
                                  (self,
                                    (Core_models.Result.Result_Err err
                                      <:
                                      Core_models.Result.t_Result Prims.unit t_Error)
                                    <:
                                    (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
                                  <:
                                  Core_models.Ops.Control_flow.t_ControlFlow
                                    (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                    (Prims.unit & usize))
                                <:
                                Core_models.Ops.Control_flow.t_ControlFlow
                                  (Core_models.Ops.Control_flow.t_ControlFlow
                                      (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                      (Prims.unit & usize)) usize
                            else
                              let before:bool = birth_lt node.f_id old.f_id in
                              if before
                              then
                                let at:usize = i in
                                Core_models.Ops.Control_flow.ControlFlow_Break
                                (Core_models.Ops.Control_flow.ControlFlow_Continue
                                  ((), at <: (Prims.unit & usize))
                                  <:
                                  Core_models.Ops.Control_flow.t_ControlFlow
                                    (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                    (Prims.unit & usize))
                                <:
                                Core_models.Ops.Control_flow.t_ControlFlow
                                  (Core_models.Ops.Control_flow.t_ControlFlow
                                      (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                      (Prims.unit & usize)) usize
                              else
                                Core_models.Ops.Control_flow.ControlFlow_Continue at
                                <:
                                Core_models.Ops.Control_flow.t_ControlFlow
                                  (Core_models.Ops.Control_flow.t_ControlFlow
                                      (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                      (Prims.unit & usize)) usize
                          | Core_models.Result.Result_Err err ->
                            Core_models.Ops.Control_flow.ControlFlow_Break
                            (Core_models.Ops.Control_flow.ControlFlow_Break
                              (self,
                                (Core_models.Result.Result_Err err
                                  <:
                                  Core_models.Result.t_Result Prims.unit t_Error)
                                <:
                                (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
                              <:
                              Core_models.Ops.Control_flow.t_ControlFlow
                                (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                (Prims.unit & usize))
                            <:
                            Core_models.Ops.Control_flow.t_ControlFlow
                              (Core_models.Ops.Control_flow.t_ControlFlow
                                  (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                  (Prims.unit & usize)) usize)
                    <:
                    Core_models.Ops.Control_flow.t_ControlFlow
                      (t_Tree & Core_models.Result.t_Result Prims.unit t_Error) usize
                  with
                  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
                  | Core_models.Ops.Control_flow.ControlFlow_Continue at ->
                    match parent <: Core_models.Option.t_Option usize with
                    | Core_models.Option.Option_Some p ->
                      if
                        p >=.
                        (Alloc.Vec.impl_1__len #t_Node #Alloc.Alloc.t_Global self.f_nodes <: usize)
                      then
                        self,
                        (Core_models.Result.Result_Err (Error_Internal <: t_Error)
                          <:
                          Core_models.Result.t_Result Prims.unit t_Error)
                        <:
                        (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                      else
                        (match node.f_side <: t_Side with
                          | Side_Left  ->
                            let
                            (tmp0: Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global),
                            (out: Core_models.Result.t_Result Prims.unit t_Error) =
                              insert #t_BirthId (self.f_nodes.[ p ] <: t_Node).f_left at node.f_id
                            in
                            let self:t_Tree =
                              {
                                self with
                                f_nodes
                                =
                                Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                                      (Alloc.Vec.impl_1__as_slice self.f_nodes <: t_Slice t_Node)
                                      p
                                      ({ (self.f_nodes.[ p ] <: t_Node) with f_left = tmp0 }
                                        <:
                                        t_Node)
                                    <:
                                    t_Slice t_Node)
                              }
                              <:
                              t_Tree
                            in
                            (match out <: Core_models.Result.t_Result Prims.unit t_Error with
                              | Core_models.Result.Result_Ok ok ->
                                let node:t_Node =
                                  { node with f_left = Alloc.Vec.impl__new #t_BirthId () } <: t_Node
                                in
                                let node:t_Node =
                                  { node with f_right = Alloc.Vec.impl__new #t_BirthId () }
                                  <:
                                  t_Node
                                in
                                let
                                (tmp0: Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global),
                                (out: Core_models.Result.t_Result Prims.unit t_Error) =
                                  push #t_Node self.f_nodes node
                                in
                                let self:t_Tree = { self with f_nodes = tmp0 } <: t_Tree in
                                (match out <: Core_models.Result.t_Result Prims.unit t_Error with
                                  | Core_models.Result.Result_Ok _ ->
                                    let hax_temp_output:Core_models.Result.t_Result Prims.unit
                                      t_Error =
                                      Core_models.Result.Result_Ok (() <: Prims.unit)
                                      <:
                                      Core_models.Result.t_Result Prims.unit t_Error
                                    in
                                    self, hax_temp_output
                                    <:
                                    (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                  | Core_models.Result.Result_Err err ->
                                    self,
                                    (Core_models.Result.Result_Err err
                                      <:
                                      Core_models.Result.t_Result Prims.unit t_Error)
                                    <:
                                    (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
                              | Core_models.Result.Result_Err err ->
                                self,
                                (Core_models.Result.Result_Err err
                                  <:
                                  Core_models.Result.t_Result Prims.unit t_Error)
                                <:
                                (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
                          | Side_Right  ->
                            let
                            (tmp0: Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global),
                            (out: Core_models.Result.t_Result Prims.unit t_Error) =
                              insert #t_BirthId (self.f_nodes.[ p ] <: t_Node).f_right at node.f_id
                            in
                            let self:t_Tree =
                              {
                                self with
                                f_nodes
                                =
                                Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                                      (Alloc.Vec.impl_1__as_slice self.f_nodes <: t_Slice t_Node)
                                      p
                                      ({ (self.f_nodes.[ p ] <: t_Node) with f_right = tmp0 }
                                        <:
                                        t_Node)
                                    <:
                                    t_Slice t_Node)
                              }
                              <:
                              t_Tree
                            in
                            match out <: Core_models.Result.t_Result Prims.unit t_Error with
                            | Core_models.Result.Result_Ok ok ->
                              let node:t_Node =
                                { node with f_left = Alloc.Vec.impl__new #t_BirthId () } <: t_Node
                              in
                              let node:t_Node =
                                { node with f_right = Alloc.Vec.impl__new #t_BirthId () } <: t_Node
                              in
                              let
                              (tmp0: Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global),
                              (out: Core_models.Result.t_Result Prims.unit t_Error) =
                                push #t_Node self.f_nodes node
                              in
                              let self:t_Tree = { self with f_nodes = tmp0 } <: t_Tree in
                              (match out <: Core_models.Result.t_Result Prims.unit t_Error with
                                | Core_models.Result.Result_Ok _ ->
                                  let hax_temp_output:Core_models.Result.t_Result Prims.unit t_Error
                                  =
                                    Core_models.Result.Result_Ok (() <: Prims.unit)
                                    <:
                                    Core_models.Result.t_Result Prims.unit t_Error
                                  in
                                  self, hax_temp_output
                                  <:
                                  (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                                | Core_models.Result.Result_Err err ->
                                  self,
                                  (Core_models.Result.Result_Err err
                                    <:
                                    Core_models.Result.t_Result Prims.unit t_Error)
                                  <:
                                  (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
                            | Core_models.Result.Result_Err err ->
                              self,
                              (Core_models.Result.Result_Err err
                                <:
                                Core_models.Result.t_Result Prims.unit t_Error)
                              <:
                              (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
                    | Core_models.Option.Option_None  ->
                      let
                      (tmp0: Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global),
                      (out: Core_models.Result.t_Result Prims.unit t_Error) =
                        insert #t_BirthId self.f_root_right at node.f_id
                      in
                      let self:t_Tree = { self with f_root_right = tmp0 } <: t_Tree in
                      match out <: Core_models.Result.t_Result Prims.unit t_Error with
                      | Core_models.Result.Result_Ok ok ->
                        let node:t_Node =
                          { node with f_left = Alloc.Vec.impl__new #t_BirthId () } <: t_Node
                        in
                        let node:t_Node =
                          { node with f_right = Alloc.Vec.impl__new #t_BirthId () } <: t_Node
                        in
                        let
                        (tmp0: Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global),
                        (out: Core_models.Result.t_Result Prims.unit t_Error) =
                          push #t_Node self.f_nodes node
                        in
                        let self:t_Tree = { self with f_nodes = tmp0 } <: t_Tree in
                        (match out <: Core_models.Result.t_Result Prims.unit t_Error with
                          | Core_models.Result.Result_Ok _ ->
                            let hax_temp_output:Core_models.Result.t_Result Prims.unit t_Error =
                              Core_models.Result.Result_Ok (() <: Prims.unit)
                              <:
                              Core_models.Result.t_Result Prims.unit t_Error
                            in
                            self, hax_temp_output
                            <:
                            (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)
                          | Core_models.Result.Result_Err err ->
                            self,
                            (Core_models.Result.Result_Err err
                              <:
                              Core_models.Result.t_Result Prims.unit t_Error)
                            <:
                            (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
                      | Core_models.Result.Result_Err err ->
                        self,
                        (Core_models.Result.Result_Err err
                          <:
                          Core_models.Result.t_Result Prims.unit t_Error)
                        <:
                        (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
              | Core_models.Result.Result_Err err ->
                self,
                (Core_models.Result.Result_Err err <: Core_models.Result.t_Result Prims.unit t_Error
                )
                <:
                (t_Tree & Core_models.Result.t_Result Prims.unit t_Error))
    | Core_models.Result.Result_Err err ->
      self, (Core_models.Result.Result_Err err <: Core_models.Result.t_Result Prims.unit t_Error)
      <:
      (t_Tree & Core_models.Result.t_Result Prims.unit t_Error)

let next_counter_after (counter: u64) : Core_models.Result.t_Result u64 t_Error =
  if counter >. v_MAX_COUNTER
  then
    Core_models.Result.Result_Err (Error_Capacity (Capacity_Counter <: t_Capacity) <: t_Error)
    <:
    Core_models.Result.t_Result u64 t_Error
  else Core_models.Result.Result_Ok (counter +! mk_u64 1) <: Core_models.Result.t_Result u64 t_Error

let has_event (ids: t_Slice t_EventId) (id: t_EventId) : bool =
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
      (Core_models.Slice.impl__len #t_EventId ids <: usize)
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:usize = temp_1_ in
          true)
      ()
      (fun temp_0_ i ->
          let _:Prims.unit = temp_0_ in
          let i:usize = i in
          if (ids.[ i ] <: t_EventId) =. id <: bool
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

let has_birth (ids: t_Slice t_BirthId) (id: t_BirthId) : bool =
  match
    Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter #(t_Slice
            t_BirthId)
          #FStar.Tactics.Typeclasses.solve
          ids
        <:
        Core_models.Slice.Iter.t_Iter t_BirthId)
      ()
      (fun temp_0_ old ->
          let _:Prims.unit = temp_0_ in
          let old:t_BirthId = old in
          if old =. id <: bool
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

let impl_Tree__insert
      (self: t_Tree)
      (id: t_BirthId)
      (scalar: u32)
      (visible: t_Slice t_BirthId)
      (gap: usize)
    : (t_Tree & Core_models.Result.t_Result t_Node t_Error) =
  match
    impl_Tree__whole self
    <:
    Core_models.Result.t_Result (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error
  with
  | Core_models.Result.Result_Ok all ->
    let view:Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global = Alloc.Vec.impl__new #t_BirthId () in
    (match
        Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter #(Core_models.Slice.Iter.t_Iter
                t_BirthId)
              #FStar.Tactics.Typeclasses.solve
              (Core_models.Slice.impl__iter #t_BirthId
                  (Alloc.Vec.impl_1__as_slice all <: t_Slice t_BirthId)
                <:
                Core_models.Slice.Iter.t_Iter t_BirthId)
            <:
            Core_models.Slice.Iter.t_Iter t_BirthId)
          view
          (fun view id ->
              let view:Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global = view in
              let id:t_BirthId = id in
              if has_birth visible id <: bool
              then
                let
                (tmp0: Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global),
                (out: Core_models.Result.t_Result Prims.unit t_Error) =
                  push #t_BirthId view id
                in
                let view:Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global = tmp0 in
                match out <: Core_models.Result.t_Result Prims.unit t_Error with
                | Core_models.Result.Result_Ok _ ->
                  Core_models.Ops.Control_flow.ControlFlow_Continue view
                  <:
                  Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Ops.Control_flow.t_ControlFlow
                        (t_Tree & Core_models.Result.t_Result t_Node t_Error)
                        (Prims.unit & Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global))
                    (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
                | Core_models.Result.Result_Err err ->
                  Core_models.Ops.Control_flow.ControlFlow_Break
                  (Core_models.Ops.Control_flow.ControlFlow_Break
                    (self,
                      (Core_models.Result.Result_Err err
                        <:
                        Core_models.Result.t_Result t_Node t_Error)
                      <:
                      (t_Tree & Core_models.Result.t_Result t_Node t_Error))
                    <:
                    Core_models.Ops.Control_flow.t_ControlFlow
                      (t_Tree & Core_models.Result.t_Result t_Node t_Error)
                      (Prims.unit & Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global))
                  <:
                  Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Ops.Control_flow.t_ControlFlow
                        (t_Tree & Core_models.Result.t_Result t_Node t_Error)
                        (Prims.unit & Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global))
                    (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
              else
                Core_models.Ops.Control_flow.ControlFlow_Continue view
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Ops.Control_flow.t_ControlFlow
                      (t_Tree & Core_models.Result.t_Result t_Node t_Error)
                      (Prims.unit & Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global))
                  (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global))
        <:
        Core_models.Ops.Control_flow.t_ControlFlow
          (t_Tree & Core_models.Result.t_Result t_Node t_Error)
          (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
      with
      | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
      | Core_models.Ops.Control_flow.ControlFlow_Continue view ->
        if
          (Alloc.Vec.impl_1__len #t_BirthId #Alloc.Alloc.t_Global view <: usize) <>.
          (Core_models.Slice.impl__len #t_BirthId visible <: usize) ||
          gap >. (Alloc.Vec.impl_1__len #t_BirthId #Alloc.Alloc.t_Global view <: usize)
        then
          self,
          (Core_models.Result.Result_Err (Error_Internal <: t_Error)
            <:
            Core_models.Result.t_Result t_Node t_Error)
          <:
          (t_Tree & Core_models.Result.t_Result t_Node t_Error)
        else
          let left:Core_models.Option.t_Option t_BirthId =
            if gap =. mk_usize 0
            then Core_models.Option.Option_None <: Core_models.Option.t_Option t_BirthId
            else
              Core_models.Option.Option_Some view.[ gap -! mk_usize 1 <: usize ]
              <:
              Core_models.Option.t_Option t_BirthId
          in
          match left <: Core_models.Option.t_Option t_BirthId with
          | Core_models.Option.Option_None  ->
            let next:usize = mk_usize 0 in
            let right:Core_models.Option.t_Option t_BirthId =
              if next <. (Alloc.Vec.impl_1__len #t_BirthId #Alloc.Alloc.t_Global all <: usize)
              then
                Core_models.Option.Option_Some all.[ next ] <: Core_models.Option.t_Option t_BirthId
              else Core_models.Option.Option_None <: Core_models.Option.t_Option t_BirthId
            in
            (match left <: Core_models.Option.t_Option t_BirthId with
              | Core_models.Option.Option_None  ->
                let has_right:bool =
                  ~.(Alloc.Vec.impl_1__is_empty #t_BirthId #Alloc.Alloc.t_Global self.f_root_right
                    <:
                    bool)
                in
                let side:t_Side = if has_right then Side_Left <: t_Side else Side_Right <: t_Side in
                let parent:Core_models.Option.t_Option t_BirthId =
                  if
                    match side <: t_Side with
                    | Side_Right  -> true
                    | _ -> false
                  then left
                  else right
                in
                if
                  (match side <: t_Side with
                    | Side_Left  -> true
                    | _ -> false) &&
                  Core_models.Option.impl__is_none #t_BirthId parent
                then
                  self,
                  (Core_models.Result.Result_Err (Error_Internal <: t_Error)
                    <:
                    Core_models.Result.t_Result t_Node t_Error)
                  <:
                  (t_Tree & Core_models.Result.t_Result t_Node t_Error)
                else
                  let node:t_Node =
                    {
                      f_id = id;
                      f_scalar = scalar;
                      f_left_origin = left;
                      f_right_origin = right;
                      f_parent = parent;
                      f_side = side;
                      f_left = Alloc.Vec.impl__new #t_BirthId ();
                      f_right = Alloc.Vec.impl__new #t_BirthId ()
                    }
                    <:
                    t_Node
                  in
                  let (tmp0: t_Tree), (out: Core_models.Result.t_Result Prims.unit t_Error) =
                    impl_Tree__add self
                      (Core_models.Clone.f_clone #t_Node #FStar.Tactics.Typeclasses.solve node
                        <:
                        t_Node)
                  in
                  let self:t_Tree = tmp0 in
                  (match out <: Core_models.Result.t_Result Prims.unit t_Error with
                    | Core_models.Result.Result_Ok _ ->
                      let hax_temp_output:Core_models.Result.t_Result t_Node t_Error =
                        Core_models.Result.Result_Ok node
                        <:
                        Core_models.Result.t_Result t_Node t_Error
                      in
                      self, hax_temp_output <: (t_Tree & Core_models.Result.t_Result t_Node t_Error)
                    | Core_models.Result.Result_Err err ->
                      self,
                      (Core_models.Result.Result_Err err
                        <:
                        Core_models.Result.t_Result t_Node t_Error)
                      <:
                      (t_Tree & Core_models.Result.t_Result t_Node t_Error))
              | Core_models.Option.Option_Some x ->
                match impl_Tree__node self x <: Core_models.Result.t_Result t_Node t_Error with
                | Core_models.Result.Result_Ok hoist34 ->
                  let has_right:bool =
                    ~.(Alloc.Vec.impl_1__is_empty #t_BirthId #Alloc.Alloc.t_Global hoist34.f_right
                      <:
                      bool)
                  in
                  let side:t_Side =
                    if has_right then Side_Left <: t_Side else Side_Right <: t_Side
                  in
                  let parent:Core_models.Option.t_Option t_BirthId =
                    if
                      match side <: t_Side with
                      | Side_Right  -> true
                      | _ -> false
                    then left
                    else right
                  in
                  if
                    (match side <: t_Side with
                      | Side_Left  -> true
                      | _ -> false) &&
                    Core_models.Option.impl__is_none #t_BirthId parent
                  then
                    self,
                    (Core_models.Result.Result_Err (Error_Internal <: t_Error)
                      <:
                      Core_models.Result.t_Result t_Node t_Error)
                    <:
                    (t_Tree & Core_models.Result.t_Result t_Node t_Error)
                  else
                    let node:t_Node =
                      {
                        f_id = id;
                        f_scalar = scalar;
                        f_left_origin = left;
                        f_right_origin = right;
                        f_parent = parent;
                        f_side = side;
                        f_left = Alloc.Vec.impl__new #t_BirthId ();
                        f_right = Alloc.Vec.impl__new #t_BirthId ()
                      }
                      <:
                      t_Node
                    in
                    let (tmp0: t_Tree), (out: Core_models.Result.t_Result Prims.unit t_Error) =
                      impl_Tree__add self
                        (Core_models.Clone.f_clone #t_Node #FStar.Tactics.Typeclasses.solve node
                          <:
                          t_Node)
                    in
                    let self:t_Tree = tmp0 in
                    (match out <: Core_models.Result.t_Result Prims.unit t_Error with
                      | Core_models.Result.Result_Ok _ ->
                        let hax_temp_output:Core_models.Result.t_Result t_Node t_Error =
                          Core_models.Result.Result_Ok node
                          <:
                          Core_models.Result.t_Result t_Node t_Error
                        in
                        self, hax_temp_output
                        <:
                        (t_Tree & Core_models.Result.t_Result t_Node t_Error)
                      | Core_models.Result.Result_Err err ->
                        self,
                        (Core_models.Result.Result_Err err
                          <:
                          Core_models.Result.t_Result t_Node t_Error)
                        <:
                        (t_Tree & Core_models.Result.t_Result t_Node t_Error))
                | Core_models.Result.Result_Err err ->
                  self,
                  (Core_models.Result.Result_Err err <: Core_models.Result.t_Result t_Node t_Error)
                  <:
                  (t_Tree & Core_models.Result.t_Result t_Node t_Error))
          | Core_models.Option.Option_Some x ->
            match
              impl_Tree__rank (Alloc.Vec.impl_1__as_slice all <: t_Slice t_BirthId)
                (Core_models.Option.Option_Some x <: Core_models.Option.t_Option t_BirthId)
              <:
              Core_models.Result.t_Result usize t_Error
            with
            | Core_models.Result.Result_Ok p ->
              if p =. Core_models.Num.impl_usize__MAX
              then
                self,
                (Core_models.Result.Result_Err (Error_Internal <: t_Error)
                  <:
                  Core_models.Result.t_Result t_Node t_Error)
                <:
                (t_Tree & Core_models.Result.t_Result t_Node t_Error)
              else
                let next:usize = p +! mk_usize 1 in
                let right:Core_models.Option.t_Option t_BirthId =
                  if next <. (Alloc.Vec.impl_1__len #t_BirthId #Alloc.Alloc.t_Global all <: usize)
                  then
                    Core_models.Option.Option_Some all.[ next ]
                    <:
                    Core_models.Option.t_Option t_BirthId
                  else Core_models.Option.Option_None <: Core_models.Option.t_Option t_BirthId
                in
                (match left <: Core_models.Option.t_Option t_BirthId with
                  | Core_models.Option.Option_None  ->
                    let has_right:bool =
                      ~.(Alloc.Vec.impl_1__is_empty #t_BirthId
                          #Alloc.Alloc.t_Global
                          self.f_root_right
                        <:
                        bool)
                    in
                    let side:t_Side =
                      if has_right then Side_Left <: t_Side else Side_Right <: t_Side
                    in
                    let parent:Core_models.Option.t_Option t_BirthId =
                      if
                        match side <: t_Side with
                        | Side_Right  -> true
                        | _ -> false
                      then left
                      else right
                    in
                    if
                      (match side <: t_Side with
                        | Side_Left  -> true
                        | _ -> false) &&
                      Core_models.Option.impl__is_none #t_BirthId parent
                    then
                      self,
                      (Core_models.Result.Result_Err (Error_Internal <: t_Error)
                        <:
                        Core_models.Result.t_Result t_Node t_Error)
                      <:
                      (t_Tree & Core_models.Result.t_Result t_Node t_Error)
                    else
                      let node:t_Node =
                        {
                          f_id = id;
                          f_scalar = scalar;
                          f_left_origin = left;
                          f_right_origin = right;
                          f_parent = parent;
                          f_side = side;
                          f_left = Alloc.Vec.impl__new #t_BirthId ();
                          f_right = Alloc.Vec.impl__new #t_BirthId ()
                        }
                        <:
                        t_Node
                      in
                      let (tmp0: t_Tree), (out: Core_models.Result.t_Result Prims.unit t_Error) =
                        impl_Tree__add self
                          (Core_models.Clone.f_clone #t_Node #FStar.Tactics.Typeclasses.solve node
                            <:
                            t_Node)
                      in
                      let self:t_Tree = tmp0 in
                      (match out <: Core_models.Result.t_Result Prims.unit t_Error with
                        | Core_models.Result.Result_Ok _ ->
                          let hax_temp_output:Core_models.Result.t_Result t_Node t_Error =
                            Core_models.Result.Result_Ok node
                            <:
                            Core_models.Result.t_Result t_Node t_Error
                          in
                          self, hax_temp_output
                          <:
                          (t_Tree & Core_models.Result.t_Result t_Node t_Error)
                        | Core_models.Result.Result_Err err ->
                          self,
                          (Core_models.Result.Result_Err err
                            <:
                            Core_models.Result.t_Result t_Node t_Error)
                          <:
                          (t_Tree & Core_models.Result.t_Result t_Node t_Error))
                  | Core_models.Option.Option_Some x ->
                    match impl_Tree__node self x <: Core_models.Result.t_Result t_Node t_Error with
                    | Core_models.Result.Result_Ok hoist34 ->
                      let has_right:bool =
                        ~.(Alloc.Vec.impl_1__is_empty #t_BirthId
                            #Alloc.Alloc.t_Global
                            hoist34.f_right
                          <:
                          bool)
                      in
                      let side:t_Side =
                        if has_right then Side_Left <: t_Side else Side_Right <: t_Side
                      in
                      let parent:Core_models.Option.t_Option t_BirthId =
                        if
                          match side <: t_Side with
                          | Side_Right  -> true
                          | _ -> false
                        then left
                        else right
                      in
                      if
                        (match side <: t_Side with
                          | Side_Left  -> true
                          | _ -> false) &&
                        Core_models.Option.impl__is_none #t_BirthId parent
                      then
                        self,
                        (Core_models.Result.Result_Err (Error_Internal <: t_Error)
                          <:
                          Core_models.Result.t_Result t_Node t_Error)
                        <:
                        (t_Tree & Core_models.Result.t_Result t_Node t_Error)
                      else
                        let node:t_Node =
                          {
                            f_id = id;
                            f_scalar = scalar;
                            f_left_origin = left;
                            f_right_origin = right;
                            f_parent = parent;
                            f_side = side;
                            f_left = Alloc.Vec.impl__new #t_BirthId ();
                            f_right = Alloc.Vec.impl__new #t_BirthId ()
                          }
                          <:
                          t_Node
                        in
                        let (tmp0: t_Tree), (out: Core_models.Result.t_Result Prims.unit t_Error) =
                          impl_Tree__add self
                            (Core_models.Clone.f_clone #t_Node #FStar.Tactics.Typeclasses.solve node
                              <:
                              t_Node)
                        in
                        let self:t_Tree = tmp0 in
                        (match out <: Core_models.Result.t_Result Prims.unit t_Error with
                          | Core_models.Result.Result_Ok _ ->
                            let hax_temp_output:Core_models.Result.t_Result t_Node t_Error =
                              Core_models.Result.Result_Ok node
                              <:
                              Core_models.Result.t_Result t_Node t_Error
                            in
                            self, hax_temp_output
                            <:
                            (t_Tree & Core_models.Result.t_Result t_Node t_Error)
                          | Core_models.Result.Result_Err err ->
                            self,
                            (Core_models.Result.Result_Err err
                              <:
                              Core_models.Result.t_Result t_Node t_Error)
                            <:
                            (t_Tree & Core_models.Result.t_Result t_Node t_Error))
                    | Core_models.Result.Result_Err err ->
                      self,
                      (Core_models.Result.Result_Err err
                        <:
                        Core_models.Result.t_Result t_Node t_Error)
                      <:
                      (t_Tree & Core_models.Result.t_Result t_Node t_Error))
            | Core_models.Result.Result_Err err ->
              self,
              (Core_models.Result.Result_Err err <: Core_models.Result.t_Result t_Node t_Error)
              <:
              (t_Tree & Core_models.Result.t_Result t_Node t_Error))
  | Core_models.Result.Result_Err err ->
    self, (Core_models.Result.Result_Err err <: Core_models.Result.t_Result t_Node t_Error)
    <:
    (t_Tree & Core_models.Result.t_Result t_Node t_Error)

let has_fact (facts: t_Slice t_Fact) (id: t_EventId) : bool =
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
      (Core_models.Slice.impl__len #t_Fact facts <: usize)
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:usize = temp_1_ in
          true)
      ()
      (fun temp_0_ i ->
          let _:Prims.unit = temp_0_ in
          let i:usize = i in
          if (facts.[ i ] <: t_Fact).f_id =. id <: bool
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

let choose_unseen (facts out: t_Slice t_Fact)
    : Core_models.Result.t_Result (Core_models.Option.t_Option usize) t_Error =
  let chosen:Core_models.Option.t_Option usize =
    Core_models.Option.Option_None <: Core_models.Option.t_Option usize
  in
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
      (Core_models.Slice.impl__len #t_Fact facts <: usize)
      (fun chosen temp_1_ ->
          let chosen:Core_models.Option.t_Option usize = chosen in
          let _:usize = temp_1_ in
          true)
      chosen
      (fun chosen j ->
          let chosen:Core_models.Option.t_Option usize = chosen in
          let j:usize = j in
          if ~.(has_fact out (facts.[ j ] <: t_Fact).f_id <: bool) <: bool
          then
            match chosen <: Core_models.Option.t_Option usize with
            | Core_models.Option.Option_None  ->
              Core_models.Ops.Control_flow.ControlFlow_Continue
              (Core_models.Option.Option_Some j <: Core_models.Option.t_Option usize)
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result (Core_models.Option.t_Option usize) t_Error)
                    (Prims.unit & Core_models.Option.t_Option usize))
                (Core_models.Option.t_Option usize)
            | Core_models.Option.Option_Some k ->
              if k >=. (Core_models.Slice.impl__len #t_Fact facts <: usize) <: bool
              then
                Core_models.Ops.Control_flow.ControlFlow_Break
                (Core_models.Ops.Control_flow.ControlFlow_Break
                  (Core_models.Result.Result_Err (Error_Internal <: t_Error)
                    <:
                    Core_models.Result.t_Result (Core_models.Option.t_Option usize) t_Error)
                  <:
                  Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result (Core_models.Option.t_Option usize) t_Error)
                    (Prims.unit & Core_models.Option.t_Option usize))
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Result.t_Result (Core_models.Option.t_Option usize) t_Error)
                      (Prims.unit & Core_models.Option.t_Option usize))
                  (Core_models.Option.t_Option usize)
              else
                if event_lt (facts.[ j ] <: t_Fact).f_id (facts.[ k ] <: t_Fact).f_id <: bool
                then
                  let chosen:Core_models.Option.t_Option usize =
                    Core_models.Option.Option_Some j <: Core_models.Option.t_Option usize
                  in
                  Core_models.Ops.Control_flow.ControlFlow_Continue chosen
                  <:
                  Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Ops.Control_flow.t_ControlFlow
                        (Core_models.Result.t_Result (Core_models.Option.t_Option usize) t_Error)
                        (Prims.unit & Core_models.Option.t_Option usize))
                    (Core_models.Option.t_Option usize)
                else
                  Core_models.Ops.Control_flow.ControlFlow_Continue chosen
                  <:
                  Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Ops.Control_flow.t_ControlFlow
                        (Core_models.Result.t_Result (Core_models.Option.t_Option usize) t_Error)
                        (Prims.unit & Core_models.Option.t_Option usize))
                    (Core_models.Option.t_Option usize)
          else
            Core_models.Ops.Control_flow.ControlFlow_Continue chosen
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result (Core_models.Option.t_Option usize) t_Error)
                  (Prims.unit & Core_models.Option.t_Option usize))
              (Core_models.Option.t_Option usize))
    <:
    Core_models.Ops.Control_flow.t_ControlFlow
      (Core_models.Result.t_Result (Core_models.Option.t_Option usize) t_Error)
      (Core_models.Option.t_Option usize)
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue chosen ->
    Core_models.Result.Result_Ok chosen
    <:
    Core_models.Result.t_Result (Core_models.Option.t_Option usize) t_Error

let clone_selected_fact (fact: t_Fact) : t_Fact =
  Core_models.Clone.f_clone #t_Fact #FStar.Tactics.Typeclasses.solve fact

let canonical_step (facts: t_Slice t_Fact) (out: Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global)
    : Core_models.Result.t_Result (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global) t_Error =
  match
    choose_unseen facts (Alloc.Vec.impl_1__as_slice out <: t_Slice t_Fact)
    <:
    Core_models.Result.t_Result (Core_models.Option.t_Option usize) t_Error
  with
  | Core_models.Result.Result_Ok chosen ->
    (match
        Core_models.Option.impl__ok_or #usize #t_Error chosen (Error_Internal <: t_Error)
        <:
        Core_models.Result.t_Result usize t_Error
      with
      | Core_models.Result.Result_Ok i ->
        if i >=. (Core_models.Slice.impl__len #t_Fact facts <: usize)
        then
          Core_models.Result.Result_Err (Error_Internal <: t_Error)
          <:
          Core_models.Result.t_Result (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global) t_Error
        else
          let
          (tmp0: Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global),
          (out1: Core_models.Result.t_Result Prims.unit t_Error) =
            push #t_Fact out (clone_selected_fact (facts.[ i ] <: t_Fact) <: t_Fact)
          in
          let out:Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global = tmp0 in
          (match out1 <: Core_models.Result.t_Result Prims.unit t_Error with
            | Core_models.Result.Result_Ok _ ->
              Core_models.Result.Result_Ok out
              <:
              Core_models.Result.t_Result (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global) t_Error
            | Core_models.Result.Result_Err err ->
              Core_models.Result.Result_Err err
              <:
              Core_models.Result.t_Result (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global) t_Error)
      | Core_models.Result.Result_Err err ->
        Core_models.Result.Result_Err err
        <:
        Core_models.Result.t_Result (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global) t_Error)
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err
    <:
    Core_models.Result.t_Result (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global) t_Error

let canonical (facts: t_Slice t_Fact)
    : Core_models.Result.t_Result (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global) t_Error =
  let out:Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global = Alloc.Vec.impl__new #t_Fact () in
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
      (Core_models.Slice.impl__len #t_Fact facts <: usize)
      (fun out temp_1_ ->
          let out:Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global = out in
          let _:usize = temp_1_ in
          true)
      out
      (fun out temp_1_ ->
          let out:Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global = out in
          let _:usize = temp_1_ in
          match
            canonical_step facts out
            <:
            Core_models.Result.t_Result (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global) t_Error
          with
          | Core_models.Result.Result_Ok hoist45 ->
            Core_models.Ops.Control_flow.ControlFlow_Continue hoist45
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global) t_Error
                  ) (Prims.unit & Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global))
              (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global)
          | Core_models.Result.Result_Err err ->
            Core_models.Ops.Control_flow.ControlFlow_Break
            (Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Result.Result_Err err
                <:
                Core_models.Result.t_Result (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global) t_Error)
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global) t_Error)
                (Prims.unit & Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global))
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global) t_Error
                  ) (Prims.unit & Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global))
              (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global))
    <:
    Core_models.Ops.Control_flow.t_ControlFlow
      (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global) t_Error)
      (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global)
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue out ->
    Core_models.Result.Result_Ok out
    <:
    Core_models.Result.t_Result (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global) t_Error

let deletes (facts: t_Slice t_Fact) (id: t_BirthId) : bool =
  match
    Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter #(t_Slice
            t_Fact)
          #FStar.Tactics.Typeclasses.solve
          facts
        <:
        Core_models.Slice.Iter.t_Iter t_Fact)
      ()
      (fun temp_0_ f ->
          let _:Prims.unit = temp_0_ in
          let f:t_Fact = f in
          if has_birth (Alloc.Vec.impl_1__as_slice f.f_delete <: t_Slice t_BirthId) id <: bool
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

let ready (after done: t_Slice t_EventId) : bool =
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
      (Core_models.Slice.impl__len #t_EventId after <: usize)
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:usize = temp_1_ in
          true)
      ()
      (fun temp_0_ i ->
          let _:Prims.unit = temp_0_ in
          let i:usize = i in
          if has_event done (after.[ i ] <: t_EventId) <: bool
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

let choose_ready (facts: t_Slice t_Fact) (done: t_Slice t_EventId)
    : Core_models.Option.t_Option usize =
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
      (Core_models.Slice.impl__len #t_Fact facts <: usize)
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:usize = temp_1_ in
          true)
      ()
      (fun temp_0_ i ->
          let _:Prims.unit = temp_0_ in
          let i:usize = i in
          if has_event done (facts.[ i ] <: t_Fact).f_id <: bool
          then
            Core_models.Ops.Control_flow.ControlFlow_Continue ()
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow (Core_models.Option.t_Option usize)
                  (Prims.unit & Prims.unit)) Prims.unit
          else
            if
              ready (Alloc.Vec.impl_1__as_slice (facts.[ i ] <: t_Fact).f_after <: t_Slice t_EventId
                )
                done
              <:
              bool
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

let frontier (facts: t_Slice t_Fact)
    : Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error =
  let out:Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global = Alloc.Vec.impl__new #t_EventId () in
  match
    Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter #(t_Slice
            t_Fact)
          #FStar.Tactics.Typeclasses.solve
          facts
        <:
        Core_models.Slice.Iter.t_Iter t_Fact)
      out
      (fun out f ->
          let out:Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global = out in
          let f:t_Fact = f in
          let child:bool = false in
          let child:bool =
            Core_models.Iter.Traits.Iterator.f_fold (Core_models.Iter.Traits.Collect.f_into_iter #(t_Slice
                    t_Fact)
                  #FStar.Tactics.Typeclasses.solve
                  facts
                <:
                Core_models.Slice.Iter.t_Iter t_Fact)
              child
              (fun child e ->
                  let child:bool = child in
                  let e:t_Fact = e in
                  if
                    has_event (Alloc.Vec.impl_1__as_slice e.f_after <: t_Slice t_EventId) f.f_id
                    <:
                    bool
                  then
                    let child:bool = true in
                    child
                  else child)
          in
          if ~.child
          then
            let
            (tmp0: Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global),
            (out1: Core_models.Result.t_Result Prims.unit t_Error) =
              push #t_EventId out f.f_id
            in
            let out:Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global = tmp0 in
            match out1 <: Core_models.Result.t_Result Prims.unit t_Error with
            | Core_models.Result.Result_Ok _ ->
              Core_models.Ops.Control_flow.ControlFlow_Continue out
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
                        t_Error) (Prims.unit & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global))
                (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
            | Core_models.Result.Result_Err err ->
              Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Ops.Control_flow.ControlFlow_Break
                (Core_models.Result.Result_Err err
                  <:
                  Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
                    t_Error)
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
                      t_Error) (Prims.unit & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global))
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
                        t_Error) (Prims.unit & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global))
                (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
          else
            Core_models.Ops.Control_flow.ControlFlow_Continue out
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
                      t_Error) (Prims.unit & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global))
              (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global))
    <:
    Core_models.Ops.Control_flow.t_ControlFlow
      (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error)
      (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue out ->
    Core_models.Result.Result_Ok out
    <:
    Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error

let validate_after (facts: t_Slice t_Fact) (after: t_Slice t_EventId)
    : Core_models.Result.t_Result Prims.unit t_Error =
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
      (Core_models.Slice.impl__len #t_EventId after <: usize)
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:usize = temp_1_ in
          true)
      ()
      (fun temp_0_ i ->
          let _:Prims.unit = temp_0_ in
          let i:usize = i in
          if ~.(has_fact facts (after.[ i ] <: t_EventId) <: bool) <: bool
          then
            Core_models.Ops.Control_flow.ControlFlow_Break
            (Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Result.Result_Err (Error_Missing <: t_Error)
                <:
                Core_models.Result.t_Result Prims.unit t_Error)
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Result.t_Result Prims.unit t_Error) (Prims.unit & Prims.unit))
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result Prims.unit t_Error) (Prims.unit & Prims.unit))
              Prims.unit
          else
            Core_models.Ops.Control_flow.ControlFlow_Continue ()
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result Prims.unit t_Error) (Prims.unit & Prims.unit))
              Prims.unit)
    <:
    Core_models.Ops.Control_flow.t_ControlFlow (Core_models.Result.t_Result Prims.unit t_Error)
      Prims.unit
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue _ ->
    Core_models.Result.Result_Ok (() <: Prims.unit)
    <:
    Core_models.Result.t_Result Prims.unit t_Error

let extend_past (fact: t_Fact) (selected: Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
    : Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error =
  if has_event (Alloc.Vec.impl_1__as_slice selected <: t_Slice t_EventId) fact.f_id
  then
    match
      Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
        (Alloc.Vec.impl_1__len #t_EventId #Alloc.Alloc.t_Global fact.f_after <: usize)
        (fun selected temp_1_ ->
            let selected:Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global = selected in
            let _:usize = temp_1_ in
            true)
        selected
        (fun selected i ->
            let selected:Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global = selected in
            let i:usize = i in
            let id:t_EventId = fact.f_after.[ i ] in
            if ~.(has_event (Alloc.Vec.impl_1__as_slice selected <: t_Slice t_EventId) id <: bool)
            then
              let
              (tmp0: Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global),
              (out: Core_models.Result.t_Result Prims.unit t_Error) =
                push #t_EventId selected id
              in
              let selected:Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global = tmp0 in
              match out <: Core_models.Result.t_Result Prims.unit t_Error with
              | Core_models.Result.Result_Ok _ ->
                Core_models.Ops.Control_flow.ControlFlow_Continue selected
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
                          t_Error) (Prims.unit & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global))
                  (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
              | Core_models.Result.Result_Err err ->
                Core_models.Ops.Control_flow.ControlFlow_Break
                (Core_models.Ops.Control_flow.ControlFlow_Break
                  (Core_models.Result.Result_Err err
                    <:
                    Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
                      t_Error)
                  <:
                  Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
                        t_Error) (Prims.unit & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global))
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
                          t_Error) (Prims.unit & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global))
                  (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
            else
              Core_models.Ops.Control_flow.ControlFlow_Continue selected
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
                        t_Error) (Prims.unit & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global))
                (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global))
      <:
      Core_models.Ops.Control_flow.t_ControlFlow
        (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error)
        (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
    with
    | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
    | Core_models.Ops.Control_flow.ControlFlow_Continue selected ->
      Core_models.Result.Result_Ok selected
      <:
      Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error
  else
    Core_models.Result.Result_Ok selected
    <:
    Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error

let past_pass (facts: t_Slice t_Fact) (selected: Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
    : Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error =
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
      (Core_models.Slice.impl__len #t_Fact facts <: usize)
      (fun selected temp_1_ ->
          let selected:Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global = selected in
          let _:usize = temp_1_ in
          true)
      selected
      (fun selected i ->
          let selected:Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global = selected in
          let i:usize = i in
          match
            extend_past (facts.[ i ] <: t_Fact) selected
            <:
            Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error
          with
          | Core_models.Result.Result_Ok hoist52 ->
            Core_models.Ops.Control_flow.ControlFlow_Continue hoist52
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
                      t_Error) (Prims.unit & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global))
              (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
          | Core_models.Result.Result_Err err ->
            Core_models.Ops.Control_flow.ControlFlow_Break
            (Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Result.Result_Err err
                <:
                Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error
              )
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
                    t_Error) (Prims.unit & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global))
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
                      t_Error) (Prims.unit & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global))
              (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global))
    <:
    Core_models.Ops.Control_flow.t_ControlFlow
      (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error)
      (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue selected ->
    Core_models.Result.Result_Ok selected
    <:
    Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error

let past (facts: t_Slice t_Fact) (after: t_Slice t_EventId)
    : Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error =
  let selected:Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global =
    Alloc.Slice.impl__to_vec #t_EventId after
  in
  match validate_after facts after <: Core_models.Result.t_Result Prims.unit t_Error with
  | Core_models.Result.Result_Ok _ ->
    (match
        Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
          (Core_models.Slice.impl__len #t_Fact facts <: usize)
          (fun selected temp_1_ ->
              let selected:Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global = selected in
              let _:usize = temp_1_ in
              true)
          selected
          (fun selected temp_1_ ->
              let selected:Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global = selected in
              let _:usize = temp_1_ in
              match
                past_pass facts selected
                <:
                Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error
              with
              | Core_models.Result.Result_Ok hoist53 ->
                Core_models.Ops.Control_flow.ControlFlow_Continue hoist53
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
                          t_Error) (Prims.unit & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global))
                  (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
              | Core_models.Result.Result_Err err ->
                Core_models.Ops.Control_flow.ControlFlow_Break
                (Core_models.Ops.Control_flow.ControlFlow_Break
                  (Core_models.Result.Result_Err err
                    <:
                    Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
                      t_Error)
                  <:
                  Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
                        t_Error) (Prims.unit & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global))
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
                          t_Error) (Prims.unit & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global))
                  (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global))
        <:
        Core_models.Ops.Control_flow.t_ControlFlow
          (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error)
          (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
      with
      | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
      | Core_models.Ops.Control_flow.ControlFlow_Continue selected ->
        Core_models.Result.Result_Ok selected
        <:
        Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error)
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err
    <:
    Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error

let visible (facts: t_Slice t_Fact)
    : Core_models.Result.t_Result (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error =
  let ids:Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global = Alloc.Vec.impl__new #t_BirthId () in
  match
    Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter #(t_Slice
            t_Fact)
          #FStar.Tactics.Typeclasses.solve
          facts
        <:
        Core_models.Slice.Iter.t_Iter t_Fact)
      ids
      (fun ids fact ->
          let ids:Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global = ids in
          let fact:t_Fact = fact in
          match
            Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
              (Alloc.Vec.impl_1__len #u32 #Alloc.Alloc.t_Global fact.f_insert <: usize)
              (fun ids temp_1_ ->
                  let ids:Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global = ids in
                  let _:usize = temp_1_ in
                  true)
              ids
              (fun ids index ->
                  let ids:Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global = ids in
                  let index:usize = index in
                  let id:t_BirthId = { f_event = fact.f_id; f_index = index } <: t_BirthId in
                  if ~.(deletes facts id <: bool)
                  then
                    let
                    (tmp0: Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global),
                    (out: Core_models.Result.t_Result Prims.unit t_Error) =
                      push #t_BirthId ids id
                    in
                    let ids:Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global = tmp0 in
                    match out <: Core_models.Result.t_Result Prims.unit t_Error with
                    | Core_models.Result.Result_Ok _ ->
                      Core_models.Ops.Control_flow.ControlFlow_Continue ids
                      <:
                      Core_models.Ops.Control_flow.t_ControlFlow
                        (Core_models.Ops.Control_flow.t_ControlFlow
                            (Core_models.Result.t_Result
                                (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error)
                            (Prims.unit & Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global))
                        (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
                    | Core_models.Result.Result_Err err ->
                      Core_models.Ops.Control_flow.ControlFlow_Break
                      (Core_models.Ops.Control_flow.ControlFlow_Break
                        (Core_models.Result.Result_Err err
                          <:
                          Core_models.Result.t_Result
                            (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error)
                        <:
                        Core_models.Ops.Control_flow.t_ControlFlow
                          (Core_models.Result.t_Result
                              (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error)
                          (Prims.unit & Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global))
                      <:
                      Core_models.Ops.Control_flow.t_ControlFlow
                        (Core_models.Ops.Control_flow.t_ControlFlow
                            (Core_models.Result.t_Result
                                (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error)
                            (Prims.unit & Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global))
                        (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
                  else
                    Core_models.Ops.Control_flow.ControlFlow_Continue ids
                    <:
                    Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Ops.Control_flow.t_ControlFlow
                          (Core_models.Result.t_Result
                              (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error)
                          (Prims.unit & Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global))
                      (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global))
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error)
              (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
          with
          | Core_models.Ops.Control_flow.ControlFlow_Break ret ->
            Core_models.Ops.Control_flow.ControlFlow_Break
            (Core_models.Ops.Control_flow.ControlFlow_Break ret
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
                    t_Error) (Prims.unit & Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global))
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
                      t_Error) (Prims.unit & Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global))
              (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
          | Core_models.Ops.Control_flow.ControlFlow_Continue loop_res ->
            Core_models.Ops.Control_flow.ControlFlow_Continue loop_res
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
                      t_Error) (Prims.unit & Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global))
              (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global))
    <:
    Core_models.Ops.Control_flow.t_ControlFlow
      (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error)
      (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue ids ->
    Core_models.Result.Result_Ok ids
    <:
    Core_models.Result.t_Result (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error

let select_basis (facts: t_Slice t_Fact) (selected: t_Slice t_EventId)
    : Core_models.Result.t_Result (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global) t_Error =
  let basis:Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global = Alloc.Vec.impl__new #t_Fact () in
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
      (Core_models.Slice.impl__len #t_Fact facts <: usize)
      (fun basis temp_1_ ->
          let basis:Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global = basis in
          let _:usize = temp_1_ in
          true)
      basis
      (fun basis i ->
          let basis:Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global = basis in
          let i:usize = i in
          let fact:t_Fact = facts.[ i ] in
          if has_event selected fact.f_id
          then
            let
            (tmp0: Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global),
            (out: Core_models.Result.t_Result Prims.unit t_Error) =
              push #t_Fact basis (clone_selected_fact fact <: t_Fact)
            in
            let basis:Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global = tmp0 in
            match out <: Core_models.Result.t_Result Prims.unit t_Error with
            | Core_models.Result.Result_Ok _ ->
              Core_models.Ops.Control_flow.ControlFlow_Continue basis
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global)
                        t_Error) (Prims.unit & Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global))
                (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global)
            | Core_models.Result.Result_Err err ->
              Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Ops.Control_flow.ControlFlow_Break
                (Core_models.Result.Result_Err err
                  <:
                  Core_models.Result.t_Result (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global) t_Error)
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global) t_Error
                  ) (Prims.unit & Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global))
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global)
                        t_Error) (Prims.unit & Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global))
                (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global)
          else
            Core_models.Ops.Control_flow.ControlFlow_Continue basis
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global) t_Error
                  ) (Prims.unit & Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global))
              (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global))
    <:
    Core_models.Ops.Control_flow.t_ControlFlow
      (Core_models.Result.t_Result (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global) t_Error)
      (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global)
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue basis ->
    Core_models.Result.Result_Ok basis
    <:
    Core_models.Result.t_Result (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global) t_Error

let event_basis (facts: t_Slice t_Fact) (event: t_Fact)
    : Core_models.Result.t_Result
      (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global & Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global)
      t_Error =
  match
    past facts (Alloc.Vec.impl_1__as_slice event.f_after <: t_Slice t_EventId)
    <:
    Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error
  with
  | Core_models.Result.Result_Ok selected ->
    (match
        select_basis facts (Alloc.Vec.impl_1__as_slice selected <: t_Slice t_EventId)
        <:
        Core_models.Result.t_Result (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global) t_Error
      with
      | Core_models.Result.Result_Ok basis ->
        Core_models.Result.Result_Ok
        (selected, basis
          <:
          (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global &
            Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global))
        <:
        Core_models.Result.t_Result
          (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global &
            Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global) t_Error
      | Core_models.Result.Result_Err err ->
        Core_models.Result.Result_Err err
        <:
        Core_models.Result.t_Result
          (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global &
            Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global) t_Error)
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err
    <:
    Core_models.Result.t_Result
      (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global & Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global)
      t_Error

let replay_nodes (tree: t_Tree) (nodes: t_Slice t_Node) : Core_models.Result.t_Result t_Tree t_Error =
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
      (Core_models.Slice.impl__len #t_Node nodes <: usize)
      (fun tree temp_1_ ->
          let tree:t_Tree = tree in
          let _:usize = temp_1_ in
          true)
      tree
      (fun tree i ->
          let tree:t_Tree = tree in
          let i:usize = i in
          let (tmp0: t_Tree), (out: Core_models.Result.t_Result Prims.unit t_Error) =
            impl_Tree__add tree
              (Core_models.Clone.f_clone #t_Node
                  #FStar.Tactics.Typeclasses.solve
                  (nodes.[ i ] <: t_Node)
                <:
                t_Node)
          in
          let tree:t_Tree = tmp0 in
          match out <: Core_models.Result.t_Result Prims.unit t_Error with
          | Core_models.Result.Result_Ok ok ->
            Core_models.Ops.Control_flow.ControlFlow_Continue tree
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result t_Tree t_Error) (Prims.unit & t_Tree)) t_Tree
          | Core_models.Result.Result_Err err ->
            Core_models.Ops.Control_flow.ControlFlow_Break
            (Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Result.Result_Err err <: Core_models.Result.t_Result t_Tree t_Error)
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Result.t_Result t_Tree t_Error) (Prims.unit & t_Tree))
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result t_Tree t_Error) (Prims.unit & t_Tree)) t_Tree)
    <:
    Core_models.Ops.Control_flow.t_ControlFlow (Core_models.Result.t_Result t_Tree t_Error) t_Tree
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue tree ->
    Core_models.Result.Result_Ok tree <: Core_models.Result.t_Result t_Tree t_Error

let replay_author
      (operations: t_Slice (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global))
      (selected: t_Slice t_EventId)
    : Core_models.Result.t_Result t_Tree t_Error =
  let author:t_Tree = Core_models.Default.f_default #t_Tree #FStar.Tactics.Typeclasses.solve () in
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
      (Core_models.Slice.impl__len #(t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
          operations
        <:
        usize)
      (fun author temp_1_ ->
          let author:t_Tree = author in
          let _:usize = temp_1_ in
          true)
      author
      (fun author i ->
          let author:t_Tree = author in
          let i:usize = i in
          let (id: t_EventId), (ops: Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global) =
            Core_models.Clone.f_clone #(t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
              #FStar.Tactics.Typeclasses.solve
              (operations.[ i ] <: (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global))
          in
          if has_event selected id
          then
            match
              replay_nodes author (Alloc.Vec.impl_1__as_slice ops <: t_Slice t_Node)
              <:
              Core_models.Result.t_Result t_Tree t_Error
            with
            | Core_models.Result.Result_Ok hoist57 ->
              let author:t_Tree = hoist57 in
              Core_models.Ops.Control_flow.ControlFlow_Continue author
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result t_Tree t_Error) (Prims.unit & t_Tree)) t_Tree
            | Core_models.Result.Result_Err err ->
              Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Ops.Control_flow.ControlFlow_Break
                (Core_models.Result.Result_Err err <: Core_models.Result.t_Result t_Tree t_Error)
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result t_Tree t_Error) (Prims.unit & t_Tree))
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result t_Tree t_Error) (Prims.unit & t_Tree)) t_Tree
          else
            Core_models.Ops.Control_flow.ControlFlow_Continue author
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result t_Tree t_Error) (Prims.unit & t_Tree)) t_Tree)
    <:
    Core_models.Ops.Control_flow.t_ControlFlow (Core_models.Result.t_Result t_Tree t_Error) t_Tree
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue author ->
    Core_models.Result.Result_Ok author <: Core_models.Result.t_Result t_Tree t_Error

let author_context
      (facts: t_Slice t_Fact)
      (event: t_Fact)
      (operations: t_Slice (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global))
    : Core_models.Result.t_Result (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global & t_Tree) t_Error =
  match
    event_basis facts event
    <:
    Core_models.Result.t_Result
      (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global & Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global)
      t_Error
  with
  | Core_models.Result.Result_Ok (selected, basis) ->
    (match
        replay_author operations (Alloc.Vec.impl_1__as_slice selected <: t_Slice t_EventId)
        <:
        Core_models.Result.t_Result t_Tree t_Error
      with
      | Core_models.Result.Result_Ok author ->
        Core_models.Result.Result_Ok
        (basis, author <: (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global & t_Tree))
        <:
        Core_models.Result.t_Result (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global & t_Tree) t_Error
      | Core_models.Result.Result_Err err ->
        Core_models.Result.Result_Err err
        <:
        Core_models.Result.t_Result (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global & t_Tree) t_Error)
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err
    <:
    Core_models.Result.t_Result (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global & t_Tree) t_Error

let interpret_event
      (facts: t_Slice t_Fact)
      (event: t_Fact)
      (operations: t_Slice (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global))
      (result: t_Tree)
    : Core_models.Result.t_Result (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global) t_Error =
  match
    author_context facts event operations
    <:
    Core_models.Result.t_Result (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global & t_Tree) t_Error
  with
  | Core_models.Result.Result_Ok (basis, author) ->
    (match
        visible (Alloc.Vec.impl_1__as_slice basis <: t_Slice t_Fact)
        <:
        Core_models.Result.t_Result (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error
      with
      | Core_models.Result.Result_Ok seen ->
        let ops:Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global = Alloc.Vec.impl__new #t_Node () in
        if ~.(Alloc.Vec.impl_1__is_empty #u32 #Alloc.Alloc.t_Global event.f_insert <: bool)
        then
          match
            Core_models.Option.impl__ok_or #usize #t_Error event.f_gap (Error_Internal <: t_Error)
            <:
            Core_models.Result.t_Result usize t_Error
          with
          | Core_models.Result.Result_Ok gap ->
            (match
                Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
                  (Alloc.Vec.impl_1__len #u32 #Alloc.Alloc.t_Global event.f_insert <: usize)
                  (fun temp_0_ temp_1_ ->
                      let
                      (author: t_Tree),
                      (ops: Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global),
                      (seen: Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) =
                        temp_0_
                      in
                      let _:usize = temp_1_ in
                      true)
                  (author, ops, seen
                    <:
                    (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global &
                      Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global))
                  (fun temp_0_ index ->
                      let
                      (author: t_Tree),
                      (ops: Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global),
                      (seen: Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) =
                        temp_0_
                      in
                      let index:usize = index in
                      let id:t_BirthId = { f_event = event.f_id; f_index = index } <: t_BirthId in
                      match add gap index <: Core_models.Result.t_Result usize t_Error with
                      | Core_models.Result.Result_Ok hoist58 ->
                        let (tmp0: t_Tree), (out: Core_models.Result.t_Result t_Node t_Error) =
                          impl_Tree__insert author
                            id
                            (event.f_insert.[ index ] <: u32)
                            (Alloc.Vec.impl_1__as_slice seen <: t_Slice t_BirthId)
                            hoist58
                        in
                        let author:t_Tree = tmp0 in
                        (match out <: Core_models.Result.t_Result t_Node t_Error with
                          | Core_models.Result.Result_Ok op ->
                            let
                            (tmp0: Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global),
                            (out: Core_models.Result.t_Result Prims.unit t_Error) =
                              push #t_Node ops op
                            in
                            let ops:Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global = tmp0 in
                            (match out <: Core_models.Result.t_Result Prims.unit t_Error with
                              | Core_models.Result.Result_Ok _ ->
                                let
                                (tmp0: Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global),
                                (out: Core_models.Result.t_Result Prims.unit t_Error) =
                                  push #t_BirthId seen id
                                in
                                let seen:Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global = tmp0 in
                                (match out <: Core_models.Result.t_Result Prims.unit t_Error with
                                  | Core_models.Result.Result_Ok _ ->
                                    Core_models.Ops.Control_flow.ControlFlow_Continue
                                    (author, ops, seen
                                      <:
                                      (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global &
                                        Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global))
                                    <:
                                    Core_models.Ops.Control_flow.t_ControlFlow
                                      (Core_models.Ops.Control_flow.t_ControlFlow
                                          (Core_models.Result.t_Result
                                              (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                                              t_Error)
                                          (Prims.unit &
                                            (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global &
                                              Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)))
                                      (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global &
                                        Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
                                  | Core_models.Result.Result_Err err ->
                                    Core_models.Ops.Control_flow.ControlFlow_Break
                                    (Core_models.Ops.Control_flow.ControlFlow_Break
                                      (Core_models.Result.Result_Err err
                                        <:
                                        Core_models.Result.t_Result
                                          (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                                          t_Error)
                                      <:
                                      Core_models.Ops.Control_flow.t_ControlFlow
                                        (Core_models.Result.t_Result
                                            (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                                            t_Error)
                                        (Prims.unit &
                                          (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global &
                                            Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)))
                                    <:
                                    Core_models.Ops.Control_flow.t_ControlFlow
                                      (Core_models.Ops.Control_flow.t_ControlFlow
                                          (Core_models.Result.t_Result
                                              (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                                              t_Error)
                                          (Prims.unit &
                                            (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global &
                                              Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)))
                                      (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global &
                                        Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global))
                              | Core_models.Result.Result_Err err ->
                                Core_models.Ops.Control_flow.ControlFlow_Break
                                (Core_models.Ops.Control_flow.ControlFlow_Break
                                  (Core_models.Result.Result_Err err
                                    <:
                                    Core_models.Result.t_Result
                                      (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global) t_Error
                                  )
                                  <:
                                  Core_models.Ops.Control_flow.t_ControlFlow
                                    (Core_models.Result.t_Result
                                        (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                                        t_Error)
                                    (Prims.unit &
                                      (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global &
                                        Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)))
                                <:
                                Core_models.Ops.Control_flow.t_ControlFlow
                                  (Core_models.Ops.Control_flow.t_ControlFlow
                                      (Core_models.Result.t_Result
                                          (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                                          t_Error)
                                      (Prims.unit &
                                        (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global &
                                          Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)))
                                  (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global &
                                    Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global))
                          | Core_models.Result.Result_Err err ->
                            Core_models.Ops.Control_flow.ControlFlow_Break
                            (Core_models.Ops.Control_flow.ControlFlow_Break
                              (Core_models.Result.Result_Err err
                                <:
                                Core_models.Result.t_Result
                                  (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global) t_Error)
                              <:
                              Core_models.Ops.Control_flow.t_ControlFlow
                                (Core_models.Result.t_Result
                                    (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global) t_Error)
                                (Prims.unit &
                                  (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global &
                                    Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)))
                            <:
                            Core_models.Ops.Control_flow.t_ControlFlow
                              (Core_models.Ops.Control_flow.t_ControlFlow
                                  (Core_models.Result.t_Result
                                      (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global) t_Error
                                  )
                                  (Prims.unit &
                                    (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global &
                                      Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)))
                              (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global &
                                Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global))
                      | Core_models.Result.Result_Err err ->
                        Core_models.Ops.Control_flow.ControlFlow_Break
                        (Core_models.Ops.Control_flow.ControlFlow_Break
                          (Core_models.Result.Result_Err err
                            <:
                            Core_models.Result.t_Result
                              (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global) t_Error)
                          <:
                          Core_models.Ops.Control_flow.t_ControlFlow
                            (Core_models.Result.t_Result
                                (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global) t_Error)
                            (Prims.unit &
                              (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global &
                                Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)))
                        <:
                        Core_models.Ops.Control_flow.t_ControlFlow
                          (Core_models.Ops.Control_flow.t_ControlFlow
                              (Core_models.Result.t_Result
                                  (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global) t_Error)
                              (Prims.unit &
                                (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global &
                                  Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)))
                          (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global &
                            Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global))
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result
                      (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global) t_Error)
                  (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global &
                    Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
              with
              | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
              | Core_models.Ops.Control_flow.ControlFlow_Continue (author, ops, seen) ->
                match
                  Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
                    (Alloc.Vec.impl_1__len #t_Node #Alloc.Alloc.t_Global ops <: usize)
                    (fun result temp_1_ ->
                        let result:t_Tree = result in
                        let _:usize = temp_1_ in
                        true)
                    result
                    (fun result i ->
                        let result:t_Tree = result in
                        let i:usize = i in
                        let (tmp0: t_Tree), (out: Core_models.Result.t_Result Prims.unit t_Error) =
                          impl_Tree__add result
                            (Core_models.Clone.f_clone #t_Node
                                #FStar.Tactics.Typeclasses.solve
                                (ops.[ i ] <: t_Node)
                              <:
                              t_Node)
                        in
                        let result:t_Tree = tmp0 in
                        match out <: Core_models.Result.t_Result Prims.unit t_Error with
                        | Core_models.Result.Result_Ok ok ->
                          Core_models.Ops.Control_flow.ControlFlow_Continue result
                          <:
                          Core_models.Ops.Control_flow.t_ControlFlow
                            (Core_models.Ops.Control_flow.t_ControlFlow
                                (Core_models.Result.t_Result
                                    (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global) t_Error)
                                (Prims.unit & t_Tree)) t_Tree
                        | Core_models.Result.Result_Err err ->
                          Core_models.Ops.Control_flow.ControlFlow_Break
                          (Core_models.Ops.Control_flow.ControlFlow_Break
                            (Core_models.Result.Result_Err err
                              <:
                              Core_models.Result.t_Result
                                (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global) t_Error)
                            <:
                            Core_models.Ops.Control_flow.t_ControlFlow
                              (Core_models.Result.t_Result
                                  (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global) t_Error)
                              (Prims.unit & t_Tree))
                          <:
                          Core_models.Ops.Control_flow.t_ControlFlow
                            (Core_models.Ops.Control_flow.t_ControlFlow
                                (Core_models.Result.t_Result
                                    (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global) t_Error)
                                (Prims.unit & t_Tree)) t_Tree)
                  <:
                  Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result
                        (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global) t_Error) t_Tree
                with
                | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
                | Core_models.Ops.Control_flow.ControlFlow_Continue result ->
                  Core_models.Result.Result_Ok
                  (result, ops <: (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global))
                  <:
                  Core_models.Result.t_Result (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                    t_Error)
          | Core_models.Result.Result_Err err ->
            Core_models.Result.Result_Err err
            <:
            Core_models.Result.t_Result (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
              t_Error
        else
          let
          (author: t_Tree),
          (ops: Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global),
          (seen: Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) =
            author, ops, seen
            <:
            (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global &
              Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
          in
          (match
              Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
                (Alloc.Vec.impl_1__len #t_Node #Alloc.Alloc.t_Global ops <: usize)
                (fun result temp_1_ ->
                    let result:t_Tree = result in
                    let _:usize = temp_1_ in
                    true)
                result
                (fun result i ->
                    let result:t_Tree = result in
                    let i:usize = i in
                    let (tmp0: t_Tree), (out: Core_models.Result.t_Result Prims.unit t_Error) =
                      impl_Tree__add result
                        (Core_models.Clone.f_clone #t_Node
                            #FStar.Tactics.Typeclasses.solve
                            (ops.[ i ] <: t_Node)
                          <:
                          t_Node)
                    in
                    let result:t_Tree = tmp0 in
                    match out <: Core_models.Result.t_Result Prims.unit t_Error with
                    | Core_models.Result.Result_Ok ok ->
                      Core_models.Ops.Control_flow.ControlFlow_Continue result
                      <:
                      Core_models.Ops.Control_flow.t_ControlFlow
                        (Core_models.Ops.Control_flow.t_ControlFlow
                            (Core_models.Result.t_Result
                                (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global) t_Error)
                            (Prims.unit & t_Tree)) t_Tree
                    | Core_models.Result.Result_Err err ->
                      Core_models.Ops.Control_flow.ControlFlow_Break
                      (Core_models.Ops.Control_flow.ControlFlow_Break
                        (Core_models.Result.Result_Err err
                          <:
                          Core_models.Result.t_Result
                            (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global) t_Error)
                        <:
                        Core_models.Ops.Control_flow.t_ControlFlow
                          (Core_models.Result.t_Result
                              (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global) t_Error)
                          (Prims.unit & t_Tree))
                      <:
                      Core_models.Ops.Control_flow.t_ControlFlow
                        (Core_models.Ops.Control_flow.t_ControlFlow
                            (Core_models.Result.t_Result
                                (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global) t_Error)
                            (Prims.unit & t_Tree)) t_Tree)
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Result.t_Result (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                    t_Error) t_Tree
            with
            | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
            | Core_models.Ops.Control_flow.ControlFlow_Continue result ->
              Core_models.Result.Result_Ok
              (result, ops <: (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global))
              <:
              Core_models.Result.t_Result (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                t_Error)
      | Core_models.Result.Result_Err err ->
        Core_models.Result.Result_Err err
        <:
        Core_models.Result.t_Result (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global) t_Error)
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err
    <:
    Core_models.Result.t_Result (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global) t_Error

let interpret_scheduled (facts: t_Slice t_Fact)
    : Core_models.Result.t_Result (t_Tree & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error =
  let result:t_Tree = Core_models.Default.f_default #t_Tree #FStar.Tactics.Typeclasses.solve () in
  let (done: Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global):Alloc.Vec.t_Vec t_EventId
    Alloc.Alloc.t_Global =
    Alloc.Vec.impl__new #t_EventId ()
  in
  let
  (operations:
    Alloc.Vec.t_Vec (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global) Alloc.Alloc.t_Global):Alloc.Vec.t_Vec
    (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global) Alloc.Alloc.t_Global =
    Alloc.Vec.impl__new #(t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global) ()
  in
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
      (Core_models.Slice.impl__len #t_Fact facts <: usize)
      (fun temp_0_ temp_1_ ->
          let
          (done: Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global),
          (operations:
            Alloc.Vec.t_Vec (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
              Alloc.Alloc.t_Global),
          (result: t_Tree) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (done, operations, result
        <:
        (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global &
          Alloc.Vec.t_Vec (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
            Alloc.Alloc.t_Global &
          t_Tree))
      (fun temp_0_ temp_1_ ->
          let
          (done: Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global),
          (operations:
            Alloc.Vec.t_Vec (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
              Alloc.Alloc.t_Global),
          (result: t_Tree) =
            temp_0_
          in
          let _:usize = temp_1_ in
          match
            Core_models.Option.impl__ok_or #usize
              #t_Error
              (choose_ready facts (Alloc.Vec.impl_1__as_slice done <: t_Slice t_EventId)
                <:
                Core_models.Option.t_Option usize)
              (Error_Internal <: t_Error)
            <:
            Core_models.Result.t_Result usize t_Error
          with
          | Core_models.Result.Result_Ok index ->
            if index >=. (Core_models.Slice.impl__len #t_Fact facts <: usize) <: bool
            then
              Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Ops.Control_flow.ControlFlow_Break
                (Core_models.Result.Result_Err (Error_Internal <: t_Error)
                  <:
                  Core_models.Result.t_Result
                    (t_Tree & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error)
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result
                      (t_Tree & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error)
                  (Prims.unit &
                    (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global &
                      Alloc.Vec.t_Vec (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                        Alloc.Alloc.t_Global &
                      t_Tree)))
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result
                        (t_Tree & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error)
                    (Prims.unit &
                      (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global &
                        Alloc.Vec.t_Vec (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                          Alloc.Alloc.t_Global &
                        t_Tree)))
                (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global &
                  Alloc.Vec.t_Vec (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                    Alloc.Alloc.t_Global &
                  t_Tree)
            else
              let event:t_Fact = facts.[ index ] in
              (match
                  interpret_event facts
                    event
                    (Alloc.Vec.impl_1__as_slice operations
                      <:
                      t_Slice (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global))
                    result
                  <:
                  Core_models.Result.t_Result (t_Tree & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                    t_Error
                with
                | Core_models.Result.Result_Ok pair ->
                  let (next: t_Tree), (ops: Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global) = pair in
                  let result:t_Tree = next in
                  let
                  (tmp0: Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global),
                  (out: Core_models.Result.t_Result Prims.unit t_Error) =
                    push #t_EventId done event.f_id
                  in
                  let done:Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global = tmp0 in
                  (match out <: Core_models.Result.t_Result Prims.unit t_Error with
                    | Core_models.Result.Result_Ok _ ->
                      let
                      (tmp0:
                        Alloc.Vec.t_Vec (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                          Alloc.Alloc.t_Global),
                      (out: Core_models.Result.t_Result Prims.unit t_Error) =
                        push #(t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                          operations
                          (event.f_id, ops
                            <:
                            (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global))
                      in
                      let operations:Alloc.Vec.t_Vec
                        (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                        Alloc.Alloc.t_Global =
                        tmp0
                      in
                      (match out <: Core_models.Result.t_Result Prims.unit t_Error with
                        | Core_models.Result.Result_Ok _ ->
                          Core_models.Ops.Control_flow.ControlFlow_Continue
                          (done, operations, result
                            <:
                            (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global &
                              Alloc.Vec.t_Vec
                                (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                                Alloc.Alloc.t_Global &
                              t_Tree))
                          <:
                          Core_models.Ops.Control_flow.t_ControlFlow
                            (Core_models.Ops.Control_flow.t_ControlFlow
                                (Core_models.Result.t_Result
                                    (t_Tree & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
                                    t_Error)
                                (Prims.unit &
                                  (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global &
                                    Alloc.Vec.t_Vec
                                      (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                                      Alloc.Alloc.t_Global &
                                    t_Tree)))
                            (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global &
                              Alloc.Vec.t_Vec
                                (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                                Alloc.Alloc.t_Global &
                              t_Tree)
                        | Core_models.Result.Result_Err err ->
                          Core_models.Ops.Control_flow.ControlFlow_Break
                          (Core_models.Ops.Control_flow.ControlFlow_Break
                            (Core_models.Result.Result_Err err
                              <:
                              Core_models.Result.t_Result
                                (t_Tree & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error)
                            <:
                            Core_models.Ops.Control_flow.t_ControlFlow
                              (Core_models.Result.t_Result
                                  (t_Tree & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error)
                              (Prims.unit &
                                (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global &
                                  Alloc.Vec.t_Vec
                                    (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                                    Alloc.Alloc.t_Global &
                                  t_Tree)))
                          <:
                          Core_models.Ops.Control_flow.t_ControlFlow
                            (Core_models.Ops.Control_flow.t_ControlFlow
                                (Core_models.Result.t_Result
                                    (t_Tree & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global)
                                    t_Error)
                                (Prims.unit &
                                  (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global &
                                    Alloc.Vec.t_Vec
                                      (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                                      Alloc.Alloc.t_Global &
                                    t_Tree)))
                            (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global &
                              Alloc.Vec.t_Vec
                                (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                                Alloc.Alloc.t_Global &
                              t_Tree))
                    | Core_models.Result.Result_Err err ->
                      Core_models.Ops.Control_flow.ControlFlow_Break
                      (Core_models.Ops.Control_flow.ControlFlow_Break
                        (Core_models.Result.Result_Err err
                          <:
                          Core_models.Result.t_Result
                            (t_Tree & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error)
                        <:
                        Core_models.Ops.Control_flow.t_ControlFlow
                          (Core_models.Result.t_Result
                              (t_Tree & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error)
                          (Prims.unit &
                            (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global &
                              Alloc.Vec.t_Vec
                                (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                                Alloc.Alloc.t_Global &
                              t_Tree)))
                      <:
                      Core_models.Ops.Control_flow.t_ControlFlow
                        (Core_models.Ops.Control_flow.t_ControlFlow
                            (Core_models.Result.t_Result
                                (t_Tree & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error)
                            (Prims.unit &
                              (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global &
                                Alloc.Vec.t_Vec
                                  (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                                  Alloc.Alloc.t_Global &
                                t_Tree)))
                        (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global &
                          Alloc.Vec.t_Vec (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                            Alloc.Alloc.t_Global &
                          t_Tree))
                | Core_models.Result.Result_Err err ->
                  Core_models.Ops.Control_flow.ControlFlow_Break
                  (Core_models.Ops.Control_flow.ControlFlow_Break
                    (Core_models.Result.Result_Err err
                      <:
                      Core_models.Result.t_Result
                        (t_Tree & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error)
                    <:
                    Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Result.t_Result
                          (t_Tree & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error)
                      (Prims.unit &
                        (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global &
                          Alloc.Vec.t_Vec (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                            Alloc.Alloc.t_Global &
                          t_Tree)))
                  <:
                  Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Ops.Control_flow.t_ControlFlow
                        (Core_models.Result.t_Result
                            (t_Tree & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error)
                        (Prims.unit &
                          (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global &
                            Alloc.Vec.t_Vec
                              (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                              Alloc.Alloc.t_Global &
                            t_Tree)))
                    (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global &
                      Alloc.Vec.t_Vec (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                        Alloc.Alloc.t_Global &
                      t_Tree))
          | Core_models.Result.Result_Err err ->
            Core_models.Ops.Control_flow.ControlFlow_Break
            (Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Result.Result_Err err
                <:
                Core_models.Result.t_Result
                  (t_Tree & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error)
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Result.t_Result
                    (t_Tree & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error)
                (Prims.unit &
                  (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global &
                    Alloc.Vec.t_Vec (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                      Alloc.Alloc.t_Global &
                    t_Tree)))
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result
                      (t_Tree & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error)
                  (Prims.unit &
                    (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global &
                      Alloc.Vec.t_Vec (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                        Alloc.Alloc.t_Global &
                      t_Tree)))
              (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global &
                Alloc.Vec.t_Vec (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
                  Alloc.Alloc.t_Global &
                t_Tree))
    <:
    Core_models.Ops.Control_flow.t_ControlFlow
      (Core_models.Result.t_Result (t_Tree & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error
      )
      (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global &
        Alloc.Vec.t_Vec (t_EventId & Alloc.Vec.t_Vec t_Node Alloc.Alloc.t_Global)
          Alloc.Alloc.t_Global &
        t_Tree)
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue (done, operations, result) ->
    Core_models.Result.Result_Ok
    (result, done <: (t_Tree & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global))
    <:
    Core_models.Result.t_Result (t_Tree & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error

let interpret (facts: t_Slice t_Fact) : Core_models.Result.t_Result t_Tree t_Error =
  match
    interpret_scheduled facts
    <:
    Core_models.Result.t_Result (t_Tree & Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error
  with
  | Core_models.Result.Result_Ok pair ->
    let (tree: t_Tree), (_: Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) = pair in
    Core_models.Result.Result_Ok tree <: Core_models.Result.t_Result t_Tree t_Error
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err <: Core_models.Result.t_Result t_Tree t_Error

type t_Replica = {
  f_writer:Core_models.Option.t_Option t_Writer;
  f_next_counter:u64;
  f_limits:t_Limits;
  f_facts:Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global;
  f_tree:t_Tree
}

let impl_82: Core_models.Clone.t_Clone t_Replica =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

let impl_Replica__new (writer: Core_models.Option.t_Option t_Writer) (limits: t_Limits)
    : Core_models.Result.t_Result t_Replica t_Error =
  if
    limits.f_events >. mk_usize 128 || limits.f_births >. mk_usize 512 ||
    limits.f_scalars >. mk_usize 64 ||
    limits.f_dependencies >. mk_usize 64 ||
    limits.f_ordering_links >. mk_usize 1536
  then
    Core_models.Result.Result_Err (invalid (Invalid_Profile <: t_Invalid))
    <:
    Core_models.Result.t_Result t_Replica t_Error
  else
    Core_models.Result.Result_Ok
    ({
        f_writer = writer;
        f_next_counter = mk_u64 1;
        f_limits = limits;
        f_facts = Alloc.Vec.impl__new #t_Fact ();
        f_tree = Core_models.Default.f_default #t_Tree #FStar.Tactics.Typeclasses.solve ()
      }
      <:
      t_Replica)
    <:
    Core_models.Result.t_Result t_Replica t_Error

let impl_Replica__duplicate (facts: t_Slice t_Fact) (fact: t_Fact)
    : Core_models.Result.t_Result bool t_Error =
  if fact.f_id.f_counter =. mk_u64 0 || fact.f_id.f_counter >. v_MAX_COUNTER
  then
    Core_models.Result.Result_Err (invalid (Invalid_Counter <: t_Invalid))
    <:
    Core_models.Result.t_Result bool t_Error
  else
    match
      Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
        (Core_models.Slice.impl__len #t_Fact facts <: usize)
        (fun temp_0_ temp_1_ ->
            let _:Prims.unit = temp_0_ in
            let _:usize = temp_1_ in
            true)
        ()
        (fun temp_0_ i ->
            let _:Prims.unit = temp_0_ in
            let i:usize = i in
            let old:t_Fact = facts.[ i ] in
            if old.f_id =. fact.f_id
            then
              Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Ops.Control_flow.ControlFlow_Break
                (if fact_equal old fact
                  then Core_models.Result.Result_Ok true <: Core_models.Result.t_Result bool t_Error
                  else
                    Core_models.Result.Result_Err (invalid (Invalid_Conflict <: t_Invalid))
                    <:
                    Core_models.Result.t_Result bool t_Error)
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result bool t_Error) (Prims.unit & Prims.unit))
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result bool t_Error) (Prims.unit & Prims.unit)) Prims.unit
            else
              Core_models.Ops.Control_flow.ControlFlow_Continue ()
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Ops.Control_flow.t_ControlFlow
                    (Core_models.Result.t_Result bool t_Error) (Prims.unit & Prims.unit)) Prims.unit
        )
      <:
      Core_models.Ops.Control_flow.t_ControlFlow (Core_models.Result.t_Result bool t_Error)
        Prims.unit
    with
    | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
    | Core_models.Ops.Control_flow.ControlFlow_Continue _ ->
      Core_models.Result.Result_Ok false <: Core_models.Result.t_Result bool t_Error

let impl_Replica__validate_new (facts: t_Slice t_Fact) (limits: t_Limits) (fact: t_Fact)
    : Core_models.Result.t_Result Prims.unit t_Error =
  if (Core_models.Slice.impl__len #t_Fact facts <: usize) >=. limits.f_events
  then
    Core_models.Result.Result_Err (Error_Capacity (Capacity_Events <: t_Capacity) <: t_Error)
    <:
    Core_models.Result.t_Result Prims.unit t_Error
  else
    if
      (Alloc.Vec.impl_1__len #t_EventId #Alloc.Alloc.t_Global fact.f_after <: usize) >.
      limits.f_dependencies
    then
      Core_models.Result.Result_Err
      (Error_Capacity (Capacity_Dependencies <: t_Capacity) <: t_Error)
      <:
      Core_models.Result.t_Result Prims.unit t_Error
    else
      if duplicate_events (Alloc.Vec.impl_1__as_slice fact.f_after <: t_Slice t_EventId)
      then
        Core_models.Result.Result_Err (invalid (Invalid_DependencyDuplicate <: t_Invalid))
        <:
        Core_models.Result.t_Result Prims.unit t_Error
      else
        match
          past facts (Alloc.Vec.impl_1__as_slice fact.f_after <: t_Slice t_EventId)
          <:
          Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error
        with
        | Core_models.Result.Result_Ok selected ->
          if
            fact.f_id.f_counter >. mk_u64 1 &&
            ~.(has_event (Alloc.Vec.impl_1__as_slice selected <: t_Slice t_EventId)
                ({
                    f_writer = fact.f_id.f_writer;
                    f_counter = fact.f_id.f_counter -! mk_u64 1 <: u64
                  }
                  <:
                  t_EventId)
              <:
              bool)
          then
            Core_models.Result.Result_Err (invalid (Invalid_Predecessor <: t_Invalid))
            <:
            Core_models.Result.t_Result Prims.unit t_Error
          else
            (match
                Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
                  (Core_models.Slice.impl__len #t_Fact facts <: usize)
                  (fun temp_0_ temp_1_ ->
                      let _:Prims.unit = temp_0_ in
                      let _:usize = temp_1_ in
                      true)
                  ()
                  (fun temp_0_ i ->
                      let _:Prims.unit = temp_0_ in
                      let i:usize = i in
                      let e:t_Fact = facts.[ i ] in
                      if
                        has_event (Alloc.Vec.impl_1__as_slice selected <: t_Slice t_EventId) e.f_id &&
                        e.f_id.f_writer =. fact.f_id.f_writer &&
                        e.f_id.f_counter >=. fact.f_id.f_counter
                      then
                        Core_models.Ops.Control_flow.ControlFlow_Break
                        (Core_models.Ops.Control_flow.ControlFlow_Break
                          (Core_models.Result.Result_Err
                            (invalid (Invalid_Predecessor <: t_Invalid))
                            <:
                            Core_models.Result.t_Result Prims.unit t_Error)
                          <:
                          Core_models.Ops.Control_flow.t_ControlFlow
                            (Core_models.Result.t_Result Prims.unit t_Error)
                            (Prims.unit & Prims.unit))
                        <:
                        Core_models.Ops.Control_flow.t_ControlFlow
                          (Core_models.Ops.Control_flow.t_ControlFlow
                              (Core_models.Result.t_Result Prims.unit t_Error)
                              (Prims.unit & Prims.unit)) Prims.unit
                      else
                        Core_models.Ops.Control_flow.ControlFlow_Continue ()
                        <:
                        Core_models.Ops.Control_flow.t_ControlFlow
                          (Core_models.Ops.Control_flow.t_ControlFlow
                              (Core_models.Result.t_Result Prims.unit t_Error)
                              (Prims.unit & Prims.unit)) Prims.unit)
                <:
                Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result Prims.unit t_Error) Prims.unit
              with
              | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
              | Core_models.Ops.Control_flow.ControlFlow_Continue _ ->
                if
                  (Alloc.Vec.impl_1__len #u32 #Alloc.Alloc.t_Global fact.f_insert <: usize) >.
                  limits.f_scalars
                then
                  Core_models.Result.Result_Err
                  (Error_Capacity (Capacity_Scalars <: t_Capacity) <: t_Error)
                  <:
                  Core_models.Result.t_Result Prims.unit t_Error
                else
                  let births:usize = mk_usize 0 in
                  match
                    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
                      (Core_models.Slice.impl__len #t_Fact facts <: usize)
                      (fun births temp_1_ ->
                          let births:usize = births in
                          let _:usize = temp_1_ in
                          true)
                      births
                      (fun births i ->
                          let births:usize = births in
                          let i:usize = i in
                          match
                            add births
                              (Alloc.Vec.impl_1__len #u32
                                  #Alloc.Alloc.t_Global
                                  (facts.[ i ] <: t_Fact).f_insert
                                <:
                                usize)
                            <:
                            Core_models.Result.t_Result usize t_Error
                          with
                          | Core_models.Result.Result_Ok hoist75 ->
                            Core_models.Ops.Control_flow.ControlFlow_Continue hoist75
                            <:
                            Core_models.Ops.Control_flow.t_ControlFlow
                              (Core_models.Ops.Control_flow.t_ControlFlow
                                  (Core_models.Result.t_Result Prims.unit t_Error)
                                  (Prims.unit & usize)) usize
                          | Core_models.Result.Result_Err err ->
                            Core_models.Ops.Control_flow.ControlFlow_Break
                            (Core_models.Ops.Control_flow.ControlFlow_Break
                              (Core_models.Result.Result_Err err
                                <:
                                Core_models.Result.t_Result Prims.unit t_Error)
                              <:
                              Core_models.Ops.Control_flow.t_ControlFlow
                                (Core_models.Result.t_Result Prims.unit t_Error)
                                (Prims.unit & usize))
                            <:
                            Core_models.Ops.Control_flow.t_ControlFlow
                              (Core_models.Ops.Control_flow.t_ControlFlow
                                  (Core_models.Result.t_Result Prims.unit t_Error)
                                  (Prims.unit & usize)) usize)
                    <:
                    Core_models.Ops.Control_flow.t_ControlFlow
                      (Core_models.Result.t_Result Prims.unit t_Error) usize
                  with
                  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
                  | Core_models.Ops.Control_flow.ControlFlow_Continue births ->
                    match
                      add births
                        (Alloc.Vec.impl_1__len #u32 #Alloc.Alloc.t_Global fact.f_insert <: usize)
                      <:
                      Core_models.Result.t_Result usize t_Error
                    with
                    | Core_models.Result.Result_Ok hoist76 ->
                      if hoist76 >. limits.f_births
                      then
                        Core_models.Result.Result_Err
                        (Error_Capacity (Capacity_Births <: t_Capacity) <: t_Error)
                        <:
                        Core_models.Result.t_Result Prims.unit t_Error
                      else
                        if
                          (Alloc.Vec.impl_1__len #t_BirthId #Alloc.Alloc.t_Global fact.f_delete
                            <:
                            usize) >.
                          mk_usize 512
                        then
                          Core_models.Result.Result_Err
                          (Error_Capacity (Capacity_DeleteTargets <: t_Capacity) <: t_Error)
                          <:
                          Core_models.Result.t_Result Prims.unit t_Error
                        else
                          (match
                              validate_scalars (Alloc.Vec.impl_1__as_slice fact.f_insert
                                  <:
                                  t_Slice u32)
                              <:
                              Core_models.Result.t_Result Prims.unit t_Error
                            with
                            | Core_models.Result.Result_Ok _ ->
                              let basis:Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global =
                                Alloc.Vec.impl__new #t_Fact ()
                              in
                              (match
                                  Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter
                                        #(Core_models.Slice.Iter.t_Iter t_Fact)
                                        #FStar.Tactics.Typeclasses.solve
                                        (Core_models.Slice.impl__iter #t_Fact facts
                                          <:
                                          Core_models.Slice.Iter.t_Iter t_Fact)
                                      <:
                                      Core_models.Slice.Iter.t_Iter t_Fact)
                                    basis
                                    (fun basis f ->
                                        let basis:Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global =
                                          basis
                                        in
                                        let f:t_Fact = f in
                                        if
                                          has_event (Alloc.Vec.impl_1__as_slice selected
                                              <:
                                              t_Slice t_EventId)
                                            f.f_id
                                          <:
                                          bool
                                        then
                                          let
                                          (tmp0: Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global),
                                          (out: Core_models.Result.t_Result Prims.unit t_Error) =
                                            push #t_Fact
                                              basis
                                              (Core_models.Clone.f_clone #t_Fact
                                                  #FStar.Tactics.Typeclasses.solve
                                                  f
                                                <:
                                                t_Fact)
                                          in
                                          let basis:Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global =
                                            tmp0
                                          in
                                          match
                                            out <: Core_models.Result.t_Result Prims.unit t_Error
                                          with
                                          | Core_models.Result.Result_Ok _ ->
                                            Core_models.Ops.Control_flow.ControlFlow_Continue basis
                                            <:
                                            Core_models.Ops.Control_flow.t_ControlFlow
                                              (Core_models.Ops.Control_flow.t_ControlFlow
                                                  (Core_models.Result.t_Result Prims.unit t_Error)
                                                  (Prims.unit &
                                                    Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global))
                                              (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global)
                                          | Core_models.Result.Result_Err err ->
                                            Core_models.Ops.Control_flow.ControlFlow_Break
                                            (Core_models.Ops.Control_flow.ControlFlow_Break
                                              (Core_models.Result.Result_Err err
                                                <:
                                                Core_models.Result.t_Result Prims.unit t_Error)
                                              <:
                                              Core_models.Ops.Control_flow.t_ControlFlow
                                                (Core_models.Result.t_Result Prims.unit t_Error)
                                                (Prims.unit &
                                                  Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global))
                                            <:
                                            Core_models.Ops.Control_flow.t_ControlFlow
                                              (Core_models.Ops.Control_flow.t_ControlFlow
                                                  (Core_models.Result.t_Result Prims.unit t_Error)
                                                  (Prims.unit &
                                                    Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global))
                                              (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global)
                                        else
                                          Core_models.Ops.Control_flow.ControlFlow_Continue basis
                                          <:
                                          Core_models.Ops.Control_flow.t_ControlFlow
                                            (Core_models.Ops.Control_flow.t_ControlFlow
                                                (Core_models.Result.t_Result Prims.unit t_Error)
                                                (Prims.unit &
                                                  Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global))
                                            (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global))
                                  <:
                                  Core_models.Ops.Control_flow.t_ControlFlow
                                    (Core_models.Result.t_Result Prims.unit t_Error)
                                    (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global)
                                with
                                | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
                                | Core_models.Ops.Control_flow.ControlFlow_Continue basis ->
                                  match
                                    visible (Alloc.Vec.impl_1__as_slice basis <: t_Slice t_Fact)
                                    <:
                                    Core_models.Result.t_Result
                                      (Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global) t_Error
                                  with
                                  | Core_models.Result.Result_Ok seen ->
                                    (match
                                        Rust_primitives.Hax.Folds.fold_return (Core_models.Iter.Traits.Collect.f_into_iter
                                              #(Core_models.Slice.Iter.t_Iter t_BirthId)
                                              #FStar.Tactics.Typeclasses.solve
                                              (Core_models.Slice.impl__iter #t_BirthId
                                                  (Alloc.Vec.impl_1__as_slice fact.f_delete
                                                    <:
                                                    t_Slice t_BirthId)
                                                <:
                                                Core_models.Slice.Iter.t_Iter t_BirthId)
                                            <:
                                            Core_models.Slice.Iter.t_Iter t_BirthId)
                                          ()
                                          (fun temp_0_ id ->
                                              let _:Prims.unit = temp_0_ in
                                              let id:t_BirthId = id in
                                              if
                                                ~.(has_birth (Alloc.Vec.impl_1__as_slice seen
                                                      <:
                                                      t_Slice t_BirthId)
                                                    id
                                                  <:
                                                  bool)
                                                <:
                                                bool
                                              then
                                                Core_models.Ops.Control_flow.ControlFlow_Break
                                                (Core_models.Ops.Control_flow.ControlFlow_Break
                                                  (Core_models.Result.Result_Err
                                                    (invalid (Invalid_DeleteNotVisible <: t_Invalid)
                                                      <:
                                                      t_Error)
                                                    <:
                                                    Core_models.Result.t_Result Prims.unit t_Error)
                                                  <:
                                                  Core_models.Ops.Control_flow.t_ControlFlow
                                                    (Core_models.Result.t_Result Prims.unit t_Error)
                                                    (Prims.unit & Prims.unit))
                                                <:
                                                Core_models.Ops.Control_flow.t_ControlFlow
                                                  (Core_models.Ops.Control_flow.t_ControlFlow
                                                      (Core_models.Result.t_Result Prims.unit
                                                          t_Error) (Prims.unit & Prims.unit))
                                                  Prims.unit
                                              else
                                                Core_models.Ops.Control_flow.ControlFlow_Continue ()
                                                <:
                                                Core_models.Ops.Control_flow.t_ControlFlow
                                                  (Core_models.Ops.Control_flow.t_ControlFlow
                                                      (Core_models.Result.t_Result Prims.unit
                                                          t_Error) (Prims.unit & Prims.unit))
                                                  Prims.unit)
                                        <:
                                        Core_models.Ops.Control_flow.t_ControlFlow
                                          (Core_models.Result.t_Result Prims.unit t_Error)
                                          Prims.unit
                                      with
                                      | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
                                      | Core_models.Ops.Control_flow.ControlFlow_Continue _ ->
                                        if
                                          duplicate_births (Alloc.Vec.impl_1__as_slice fact.f_delete
                                              <:
                                              t_Slice t_BirthId)
                                        then
                                          Core_models.Result.Result_Err
                                          (invalid (Invalid_DeleteDuplicate <: t_Invalid))
                                          <:
                                          Core_models.Result.t_Result Prims.unit t_Error
                                        else
                                          if
                                            Alloc.Vec.impl_1__is_empty #u32
                                              #Alloc.Alloc.t_Global
                                              fact.f_insert
                                          then
                                            if Core_models.Option.impl__is_some #usize fact.f_gap
                                            then
                                              Core_models.Result.Result_Err
                                              (invalid (Invalid_PlacementWithoutBirth <: t_Invalid))
                                              <:
                                              Core_models.Result.t_Result Prims.unit t_Error
                                            else
                                              Core_models.Result.Result_Ok (() <: Prims.unit)
                                              <:
                                              Core_models.Result.t_Result Prims.unit t_Error
                                          else
                                            if
                                              ~.(match
                                                  (match
                                                      fact.f_gap
                                                      <:
                                                      Core_models.Option.t_Option usize
                                                    with
                                                    | Core_models.Option.Option_Some gap ->
                                                      (match
                                                          gap <=.
                                                          (Alloc.Vec.impl_1__len #t_BirthId
                                                              #Alloc.Alloc.t_Global
                                                              seen
                                                            <:
                                                            usize)
                                                          <:
                                                          bool
                                                        with
                                                        | true ->
                                                          Core_models.Option.Option_Some true
                                                          <:
                                                          Core_models.Option.t_Option bool
                                                        | _ ->
                                                          Core_models.Option.Option_None
                                                          <:
                                                          Core_models.Option.t_Option bool)
                                                    | _ ->
                                                      Core_models.Option.Option_None
                                                      <:
                                                      Core_models.Option.t_Option bool)
                                                  <:
                                                  Core_models.Option.t_Option bool
                                                with
                                                | Core_models.Option.Option_Some x -> x
                                                | Core_models.Option.Option_None  -> false)
                                            then
                                              Core_models.Result.Result_Err
                                              (invalid (Invalid_Gap <: t_Invalid))
                                              <:
                                              Core_models.Result.t_Result Prims.unit t_Error
                                            else
                                              Core_models.Result.Result_Ok (() <: Prims.unit)
                                              <:
                                              Core_models.Result.t_Result Prims.unit t_Error)
                                  | Core_models.Result.Result_Err err ->
                                    Core_models.Result.Result_Err err
                                    <:
                                    Core_models.Result.t_Result Prims.unit t_Error)
                            | Core_models.Result.Result_Err err ->
                              Core_models.Result.Result_Err err
                              <:
                              Core_models.Result.t_Result Prims.unit t_Error)
                    | Core_models.Result.Result_Err err ->
                      Core_models.Result.Result_Err err
                      <:
                      Core_models.Result.t_Result Prims.unit t_Error)
        | Core_models.Result.Result_Err err ->
          Core_models.Result.Result_Err err <: Core_models.Result.t_Result Prims.unit t_Error

let impl_Replica__with_tree (self: t_Replica) (tree: t_Tree) : t_Replica =
  let self:t_Replica = { self with f_tree = tree } <: t_Replica in
  self

let impl_Replica__with_counter (self: t_Replica) (counter: u64) : t_Replica =
  let self:t_Replica = { self with f_next_counter = counter } <: t_Replica in
  self

let impl_Replica__plan (self: t_Replica) (fact: t_Fact)
    : Core_models.Result.t_Result (Core_models.Option.t_Option t_Replica) t_Error =
  match
    impl_Replica__duplicate (Alloc.Vec.impl_1__as_slice self.f_facts <: t_Slice t_Fact) fact
    <:
    Core_models.Result.t_Result bool t_Error
  with
  | Core_models.Result.Result_Ok hoist85 ->
    if hoist85
    then
      Core_models.Result.Result_Ok
      (Core_models.Option.Option_None <: Core_models.Option.t_Option t_Replica)
      <:
      Core_models.Result.t_Result (Core_models.Option.t_Option t_Replica) t_Error
    else
      (match
          impl_Replica__validate_new (Alloc.Vec.impl_1__as_slice self.f_facts <: t_Slice t_Fact)
            self.f_limits
            fact
          <:
          Core_models.Result.t_Result Prims.unit t_Error
        with
        | Core_models.Result.Result_Ok _ ->
          let next:t_Replica =
            Core_models.Clone.f_clone #t_Replica #FStar.Tactics.Typeclasses.solve self
          in
          let
          (tmp0: Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global),
          (out: Core_models.Result.t_Result Prims.unit t_Error) =
            push #t_Fact
              next.f_facts
              (Core_models.Clone.f_clone #t_Fact #FStar.Tactics.Typeclasses.solve fact <: t_Fact)
          in
          let next:t_Replica = { next with f_facts = tmp0 } <: t_Replica in
          (match out <: Core_models.Result.t_Result Prims.unit t_Error with
            | Core_models.Result.Result_Ok _ ->
              (match
                  canonical (Alloc.Vec.impl_1__as_slice next.f_facts <: t_Slice t_Fact)
                  <:
                  Core_models.Result.t_Result (Alloc.Vec.t_Vec t_Fact Alloc.Alloc.t_Global) t_Error
                with
                | Core_models.Result.Result_Ok hoist88 ->
                  let next:t_Replica = { next with f_facts = hoist88 } <: t_Replica in
                  (match
                      interpret (Alloc.Vec.impl_1__as_slice next.f_facts <: t_Slice t_Fact)
                      <:
                      Core_models.Result.t_Result t_Tree t_Error
                    with
                    | Core_models.Result.Result_Ok tree ->
                      if
                        (Alloc.Vec.impl_1__len #t_Node #Alloc.Alloc.t_Global tree.f_nodes <: usize) >.
                        (Core_models.Num.impl_usize__MAX /! mk_usize 3 <: usize)
                      then
                        Core_models.Result.Result_Err (Error_Internal <: t_Error)
                        <:
                        Core_models.Result.t_Result (Core_models.Option.t_Option t_Replica) t_Error
                      else
                        if
                          ((Alloc.Vec.impl_1__len #t_Node #Alloc.Alloc.t_Global tree.f_nodes
                              <:
                              usize) *!
                            mk_usize 3
                            <:
                            usize) >.
                          self.f_limits.f_ordering_links
                        then
                          Core_models.Result.Result_Err
                          (Error_Capacity (Capacity_OrderingLinks <: t_Capacity) <: t_Error)
                          <:
                          Core_models.Result.t_Result (Core_models.Option.t_Option t_Replica)
                            t_Error
                        else
                          Core_models.Result.Result_Ok
                          (Core_models.Option.Option_Some (impl_Replica__with_tree next tree)
                            <:
                            Core_models.Option.t_Option t_Replica)
                          <:
                          Core_models.Result.t_Result (Core_models.Option.t_Option t_Replica)
                            t_Error
                    | Core_models.Result.Result_Err err ->
                      Core_models.Result.Result_Err err
                      <:
                      Core_models.Result.t_Result (Core_models.Option.t_Option t_Replica) t_Error)
                | Core_models.Result.Result_Err err ->
                  Core_models.Result.Result_Err err
                  <:
                  Core_models.Result.t_Result (Core_models.Option.t_Option t_Replica) t_Error)
            | Core_models.Result.Result_Err err ->
              Core_models.Result.Result_Err err
              <:
              Core_models.Result.t_Result (Core_models.Option.t_Option t_Replica) t_Error)
        | Core_models.Result.Result_Err err ->
          Core_models.Result.Result_Err err
          <:
          Core_models.Result.t_Result (Core_models.Option.t_Option t_Replica) t_Error)
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err
    <:
    Core_models.Result.t_Result (Core_models.Option.t_Option t_Replica) t_Error

/// Consumes and returns the complete instance even on error. The borrowed
/// input remains the caller's responsibility until Added/Duplicate succeeds.
let impl_Replica__receive (self: t_Replica) (fact: t_Fact)
    : (t_Replica & Core_models.Result.t_Result t_Admission t_Error) =
  match
    impl_Replica__plan self fact
    <:
    Core_models.Result.t_Result (Core_models.Option.t_Option t_Replica) t_Error
  with
  | Core_models.Result.Result_Err error ->
    self, (Core_models.Result.Result_Err error <: Core_models.Result.t_Result t_Admission t_Error)
    <:
    (t_Replica & Core_models.Result.t_Result t_Admission t_Error)
  | Core_models.Result.Result_Ok (Core_models.Option.Option_None ) ->
    self,
    (Core_models.Result.Result_Ok (Admission_Duplicate <: t_Admission)
      <:
      Core_models.Result.t_Result t_Admission t_Error)
    <:
    (t_Replica & Core_models.Result.t_Result t_Admission t_Error)
  | Core_models.Result.Result_Ok (Core_models.Option.Option_Some next) ->
    next,
    (Core_models.Result.Result_Ok (Admission_Added <: t_Admission)
      <:
      Core_models.Result.t_Result t_Admission t_Error)
    <:
    (t_Replica & Core_models.Result.t_Result t_Admission t_Error)

/// One call is one primary edit. Gap is in the pre-edit author's view,
/// including when this same fact deletes its predecessor or successor.
let impl_Replica__edit
      (self: t_Replica)
      (gap: usize)
      (insert: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global)
      (delete: Alloc.Vec.t_Vec t_BirthId Alloc.Alloc.t_Global)
    : (t_Replica & Core_models.Result.t_Result t_Local t_Error) =
  match self.f_writer <: Core_models.Option.t_Option t_Writer with
  | Core_models.Option.Option_Some w ->
    let writer:t_Writer = w in
    if
      Alloc.Vec.impl_1__is_empty #u32 #Alloc.Alloc.t_Global insert &&
      Alloc.Vec.impl_1__is_empty #t_BirthId #Alloc.Alloc.t_Global delete
    then
      self,
      (Core_models.Result.Result_Ok (Local_Empty <: t_Local)
        <:
        Core_models.Result.t_Result t_Local t_Error)
      <:
      (t_Replica & Core_models.Result.t_Result t_Local t_Error)
    else
      (match next_counter_after self.f_next_counter <: Core_models.Result.t_Result u64 t_Error with
        | Core_models.Result.Result_Ok counter ->
          let next_counter:u64 = counter in
          (match
              frontier (Alloc.Vec.impl_1__as_slice self.f_facts <: t_Slice t_Fact)
              <:
              Core_models.Result.t_Result (Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global) t_Error
            with
            | Core_models.Result.Result_Ok ids ->
              let after:Alloc.Vec.t_Vec t_EventId Alloc.Alloc.t_Global = ids in
              let fact:t_Fact =
                {
                  f_id = { f_writer = writer; f_counter = self.f_next_counter } <: t_EventId;
                  f_after = after;
                  f_gap
                  =
                  if Alloc.Vec.impl_1__is_empty #u32 #Alloc.Alloc.t_Global insert
                  then Core_models.Option.Option_None <: Core_models.Option.t_Option usize
                  else Core_models.Option.Option_Some gap <: Core_models.Option.t_Option usize;
                  f_insert = insert;
                  f_delete = delete
                }
                <:
                t_Fact
              in
              (match
                  impl_Replica__plan self fact
                  <:
                  Core_models.Result.t_Result (Core_models.Option.t_Option t_Replica) t_Error
                with
                | Core_models.Result.Result_Err error ->
                  self,
                  (Core_models.Result.Result_Err error
                    <:
                    Core_models.Result.t_Result t_Local t_Error)
                  <:
                  (t_Replica & Core_models.Result.t_Result t_Local t_Error)
                | Core_models.Result.Result_Ok (Core_models.Option.Option_None ) ->
                  self,
                  (Core_models.Result.Result_Err (invalid (Invalid_Conflict <: t_Invalid))
                    <:
                    Core_models.Result.t_Result t_Local t_Error)
                  <:
                  (t_Replica & Core_models.Result.t_Result t_Local t_Error)
                | Core_models.Result.Result_Ok (Core_models.Option.Option_Some next) ->
                  let next:t_Replica = impl_Replica__with_counter next next_counter in
                  next,
                  (Core_models.Result.Result_Ok (Local_Authored fact <: t_Local)
                    <:
                    Core_models.Result.t_Result t_Local t_Error)
                  <:
                  (t_Replica & Core_models.Result.t_Result t_Local t_Error))
            | Core_models.Result.Result_Err error ->
              self,
              (Core_models.Result.Result_Err error <: Core_models.Result.t_Result t_Local t_Error)
              <:
              (t_Replica & Core_models.Result.t_Result t_Local t_Error))
        | Core_models.Result.Result_Err error ->
          self, (Core_models.Result.Result_Err error <: Core_models.Result.t_Result t_Local t_Error)
          <:
          (t_Replica & Core_models.Result.t_Result t_Local t_Error))
  | Core_models.Option.Option_None  ->
    self,
    (Core_models.Result.Result_Err (invalid (Invalid_NoWriter <: t_Invalid))
      <:
      Core_models.Result.t_Result t_Local t_Error)
    <:
    (t_Replica & Core_models.Result.t_Result t_Local t_Error)
