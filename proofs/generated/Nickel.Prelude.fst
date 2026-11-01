(* Latte generated F* view *)
module Nickel.Prelude

open Rust_primitives

type bytes = Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global

type units = Rust_primitives.t_Slice u16

unfold let (==?) (#a: eqtype) (left: a) (right: a) : bool =
  Prims.op_Equality left right