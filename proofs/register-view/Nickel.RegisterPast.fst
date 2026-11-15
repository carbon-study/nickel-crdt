(* Latte generated F* view *)
module Nickel.RegisterPast

open Nickel.Prelude

open Rust_primitives

open Core_models

open FStar.Pervasives

open Nickel.EventGraph

module Native = Nickel_crdt.Register

module Envelope = Nickel_crdt.Causal

unfold type fact = Envelope.t_Event Native.t_Write

unfold type rid = Envelope.t_Id

unfold type rops = Nickel.EventGraph.graph_ops fact Envelope.t_Id Native.t_Error

unfold type ids_vec = Alloc.Vec.t_Vec Envelope.t_Id Alloc.Alloc.t_Global

unfold type facts_vec = Alloc.Vec.t_Vec fact Alloc.Alloc.t_Global

unfold type reops = Nickel.EventGraph.event_ops fact Envelope.t_Id Native.t_Error