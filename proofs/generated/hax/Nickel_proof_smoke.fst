module Nickel_proof_smoke
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let flip (n: usize) (value: bool) : bool =
  let value:bool =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      n
      (fun value temp_1_ ->
          let value:bool = value in
          let _:usize = temp_1_ in
          true)
      value
      (fun value temp_1_ ->
          let value:bool = value in
          let _:usize = temp_1_ in
          ~.value <: bool)
  in
  value
