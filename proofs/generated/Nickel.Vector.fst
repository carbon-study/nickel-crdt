(* Latte generated F* view *)
module Nickel.Vector

open Nickel.Prelude

open Rust_primitives

open Rust_primitives.Slice

open Core_models

open FStar.Pervasives

module Seq = FStar.Seq

let vector_contents (#item: Type0) (items: Rust_primitives.Sequence.t_Seq item) (allocator: Core_models.Marker.t_PhantomData Alloc.Alloc.t_Global) : Lemma (ensures Alloc.Vec.impl_1__as_slice (Alloc.Vec.Vec items allocator) == items) [SMTPat (Alloc.Vec.impl_1__as_slice (Alloc.Vec.Vec items allocator))] =
  ()

let vector_length (#item: Type0) (items: Alloc.Vec.t_Vec item Alloc.Alloc.t_Global) : Lemma (ensures v (Alloc.Vec.impl_1__len items) == Seq.length (Alloc.Vec.impl_1__as_slice items)) [SMTPat (Alloc.Vec.impl_1__len items)] =
  ()

let slice_length (#item: Type0) (items: t_Slice item) : Lemma (ensures v (Core_models.Slice.impl__len items) == Seq.length items) [SMTPat (Core_models.Slice.impl__len items)] =
  ()

let slice_index (#item: Type0) (items: t_Slice item) (at: usize{v at < Seq.length items}) : Lemma (ensures Rust_primitives.Slice.slice_index items at == Seq.index items (v at)) [SMTPat (Rust_primitives.Slice.slice_index items at)] =
  ()