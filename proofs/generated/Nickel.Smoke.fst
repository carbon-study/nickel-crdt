(* Latte generated F* view *)
module Nickel.Smoke

open Nickel.Prelude

open Rust_primitives

open Core_models

module Option = Core_models.Option

open FStar.Pervasives

open Nickel.LoopUtil

open Nickel_proof_smoke

let flip_next (n: usize) : Nickel.LoopUtil.transition bool n =
  fun value _ -> Option.Option_Some (not value)

let keep (value: bool) (at: usize) : bool =
  value

let identity (value: bool) : bool =
  value

let flip_run (n: usize) (at: usize{v at <= v n}) (value: bool) : bool =
  Nickel.LoopUtil.option_run n at value (flip_next n) keep identity

let flip_bridge (n: usize) (value: bool) : Lemma (ensures Nickel_proof_smoke.flip n value == flip_run n (mk_usize 0) value) =
  Nickel.LoopUtil.plain_interpret_any (mk_usize 0) n (flip_next n) keep identity

let rec odd (n: nat) : Tot bool (decreases n) =
  if Prims.op_Equality n 0 then
    begin false end
  else
    begin not (odd (n - 1)) end

let parity (value: bool) (n: nat) : bool =
  if odd n then
    begin not value end
  else
    begin value end

let rec flip_run_exact (n: usize) (at: usize{v at <= v n}) (value: bool) : Lemma (ensures flip_run n at value == parity value (v n - v at)) (decreases v n - v at) =
  if v at < v n then
    begin Nickel.LoopUtil.option_run_step n at value (flip_next n) keep identity;
    flip_run_exact n (at +! mk_int 1) (not value) end
  else
    begin Nickel.LoopUtil.option_run_end n at value (flip_next n) keep identity end

let flip_exact (n: usize) (value: bool) : Lemma (ensures Nickel_proof_smoke.flip n value == parity value (v n)) =
  Nickel.LoopUtil.plain_preserve_any (mk_usize 0) n (fun at s -> parity s (v n - at) == parity value (v n)) (fun s -> s == parity value (v n))

let flip_involution (n: usize) (value: bool) : Lemma (ensures Nickel_proof_smoke.flip n (Nickel_proof_smoke.flip n value) == value) =
  flip_exact n value;
  flip_exact n (Nickel_proof_smoke.flip n value)