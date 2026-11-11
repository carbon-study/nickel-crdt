(* Latte generated F* view *)
module Nickel.EventShell

open Nickel.Prelude

open Rust_primitives

open Core_models

open FStar.Pervasives

module Native = Nickel_crdt.Event_shell

module Result = Core_models.Result

module Option = Core_models.Option

module Tactics = FStar.Tactics.V2

let planned (#r: Type0) (#f: Type0) (#c: Type0) (#e: Type0) (before: r) (fact: f) (context: c) (duplicate: c -> r -> f -> Result.t_Result bool e) (validate: c -> r -> f -> Result.t_Result unit e) (prepare: c -> r -> f -> Result.t_Result r e) (execute: c -> r -> Result.t_Result r e) : Result.t_Result (Option.t_Option r) e =
  match duplicate context before fact with | Result.Result_Err error -> begin Result.Result_Err error end | Result.Result_Ok true -> begin Result.Result_Ok Option.Option_None end | Result.Result_Ok false -> begin match validate context before fact with | Result.Result_Err error -> begin Result.Result_Err error end | Result.Result_Ok _ -> begin match prepare context before fact with | Result.Result_Err error -> begin Result.Result_Err error end | Result.Result_Ok next -> begin match execute context next with | Result.Result_Err error -> begin Result.Result_Err error end | Result.Result_Ok next -> begin Result.Result_Ok (Option.Option_Some next) end end end end

let planning_is_exact (#r: Type0) (#f: Type0) (#c: Type0) (#e: Type0) {| i0 : Core_models.Clone.t_Clone r |} (before: r) (fact: f) (context: c) (duplicate: c -> r -> f -> Result.t_Result bool e) (validate: c -> r -> f -> Result.t_Result unit e) (prepare: c -> r -> f -> Result.t_Result r e) (execute: c -> r -> Result.t_Result r e) : Lemma (ensures Native.plan before fact context duplicate validate prepare execute == planned before fact context duplicate validate prepare execute) [SMTPat (Native.plan before fact context duplicate validate prepare execute)] =
  ()

let received (#r: Type0) (#e: Type0) (#a: Type0) (before: r) (result: Result.t_Result (Option.t_Option r) e) (added: a) (duplicate: a) : r & Result.t_Result a e =
  match result with | Result.Result_Err error -> begin (before, Result.Result_Err error) end | Result.Result_Ok Option.Option_None -> begin (before, Result.Result_Ok duplicate) end | Result.Result_Ok (Option.Option_Some next) -> begin (next, Result.Result_Ok added) end

let borrowed_publication_is_exact (#r: Type0) (#f: Type0) (#e: Type0) (#a: Type0) (#c: Type0) (before: r) (fact: f) (context: c) (plan: c -> r -> f -> Result.t_Result (Option.t_Option r) e) (added: a) (duplicate: a) : Lemma (ensures Native.receive_into before fact context plan added duplicate == received before (plan context before fact) added duplicate) [SMTPat (Native.receive_into before fact context plan added duplicate)] =
  ()

let publication_is_exact (#r: Type0) (#f: Type0) (#e: Type0) (#a: Type0) (#c: Type0) (before: r) (fact: f) (context: c) (plan: c -> r -> f -> Result.t_Result (Option.t_Option r) e) (added: a) (duplicate: a) : Lemma (ensures Native.receive before fact context plan added duplicate == received before (plan context before fact) added duplicate) [SMTPat (Native.receive before fact context plan added duplicate)] =
  assert (Native.receive before fact context plan added duplicate == received before (plan context before fact) added duplicate) by (
    Tactics.prune "Nickel_crdt.Event_shell.receive_into";
    Tactics.smt_sync' 1 1
  )