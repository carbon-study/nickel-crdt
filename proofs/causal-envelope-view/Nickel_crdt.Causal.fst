module Nickel_crdt.Causal
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_Id = {
  f_peer:u64;
  f_counter:u64
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core_models.Cmp.t_PartialEq t_Id t_Id =
  {
    f_eq_pre = (fun (self: t_Id) (other: t_Id) -> true);
    f_eq_post = (fun (self: t_Id) (other: t_Id) (out: bool) -> true);
    f_eq
    =
    fun (self: t_Id) (other: t_Id) ->
      self.f_peer =. other.f_peer && self.f_counter =. other.f_counter
  }

type t_Event (v_P: Type0) {| i0: Core_models.Clone.t_Clone v_P |} = {
  f_id:t_Id;
  f_after:Alloc.Vec.t_Vec t_Id Alloc.Alloc.t_Global;
  f_payload:v_P
}

let ids_eq (left right: t_Slice t_Id) : bool =
  if
    (Core_models.Slice.impl__len #t_Id left <: usize) <>.
    (Core_models.Slice.impl__len #t_Id right <: usize)
  then false
  else
    match
      Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
        (Core_models.Slice.impl__len #t_Id left <: usize)
        (fun temp_0_ temp_1_ ->
            let _:Prims.unit = temp_0_ in
            let _:usize = temp_1_ in
            true)
        ()
        (fun temp_0_ i ->
            let _:Prims.unit = temp_0_ in
            let i:usize = i in
            if (left.[ i ] <: t_Id) <>. (right.[ i ] <: t_Id) <: bool
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

let event_equal
      (#v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_P)
      (left right: t_Event v_P)
      (eq: (v_P -> v_P -> bool))
    : bool =
  left.f_id =. right.f_id &&
  ids_eq (Alloc.Vec.impl_1__as_slice left.f_after <: t_Slice t_Id)
    (Alloc.Vec.impl_1__as_slice right.f_after <: t_Slice t_Id) &&
  eq left.f_payload right.f_payload

/// None means a new identity; Some(true) is duplicate relative to the supplied
/// payload predicate. Exact whole-event equality requires exact client equality.
let classify
      (#v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_P)
      (facts: t_Slice (t_Event v_P))
      (fact: t_Event v_P)
      (eq: (v_P -> v_P -> bool))
    : Core_models.Option.t_Option bool =
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
      (Core_models.Slice.impl__len #(t_Event v_P) facts <: usize)
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:usize = temp_1_ in
          true)
      ()
      (fun temp_0_ i ->
          let _:Prims.unit = temp_0_ in
          let i:usize = i in
          if (facts.[ i ] <: t_Event v_P).f_id =. fact.f_id <: bool
          then
            Core_models.Ops.Control_flow.ControlFlow_Break
            (Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Option.Option_Some
                (event_equal #v_P (facts.[ i ] <: t_Event v_P) fact eq <: bool)
                <:
                Core_models.Option.t_Option bool)
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
