(* Latte generated F* view *)
module Nickel.Canonical

open Nickel.Prelude

open Rust_primitives

open Core_models

open FStar.Pervasives

open Nickel.EventGraph

open Nickel.LoopUtil

open Nickel.Vector

module Native = Nickel_crdt.Event_layer

module Seq = FStar.Seq

module Option = Core_models.Option

module Result = Core_models.Result

module Tactics = FStar.Tactics.V2

open FStar.Fin

open FStar.Classical

type vector (f: Type0) = Alloc.Vec.t_Vec f Alloc.Alloc.t_Global

let exact_values (#f: Type0) (#i: Type0) (#e: Type0) (ops: Nickel.EventGraph.graph_ops f i e) : Type0 =
  Prims.l_and (Prims.l_and (forall(a: i) (b: i). ops._1._3 a b == true <==> a == b) (forall(a: f). ops._1._5 a == a)) (forall(a: f) (b: f). ops._1._6 a b == true <==> a == b)

let present (#f: Type0) (input: t_Slice f) (item: f) : Type0 =
  exists(j: nat). Prims.l_and (j < Seq.length input) (Seq.index input j == item)

let unique (#f: Type0) (#i: Type0) (items: t_Slice f) (id: f -> i) : Type0 =
  forall(a: nat) (b: nat). Prims.l_and (Prims.l_and (a < Seq.length items) (b < Seq.length items)) (id (Seq.index items a) == id (Seq.index items b)) ==> a == b

let content_prefix (#f: Type0) (#i: Type0) (input: t_Slice f) (at: nat) (out: vector f) (id: f -> i) : Type0 =
  Prims.l_and (Prims.l_and (Seq.length (Alloc.Vec.impl_1__as_slice out) == at) (forall(j: nat). j < Seq.length (Alloc.Vec.impl_1__as_slice out) ==> present input (Seq.index (Alloc.Vec.impl_1__as_slice out) j))) (unique (Alloc.Vec.impl_1__as_slice out) id)

let push_outcome (#f: Type0) (#e: Type0) (before: vector f) (item: f) (internal: unit -> e) : vector f & Result.t_Result unit e =
  if v (Alloc.Vec.impl_1__len before) ==? max_usize then
    begin (before, Result.Result_Err (internal ())) end
  else
    begin (Alloc.Vec.from_seq (Seq.append (Alloc.Vec.impl_1__as_slice before) (Seq.create 1 item)), Result.Result_Ok ()) end

let push_is_exact (#f: Type0) (#e: Type0) (before: vector f) (item: f) (internal: unit -> e) : Lemma (ensures Native.push before item internal == push_outcome before item internal) [SMTPat (Native.push before item internal)] =
  ()

let fresh_prefix (#f: Type0) (#i: Type0) (#e: Type0) (input: t_Slice f) (out: t_Slice f) (ops: Nickel.EventGraph.graph_ops f i e) (at: nat) (choice: Option.t_Option usize) : Type0 =
  match choice with | Option.Option_None -> begin Prims.l_True end | Option.Option_Some k -> begin Prims.l_and (Prims.l_and (v k < at) (v k < Seq.length input)) (Prims.l_not (Native.has_fact out (ops._1._1 (Rust_primitives.Slice.slice_index input k)) ops == true)) end

let fresh_choice (#f: Type0) (#i: Type0) (#e: Type0) (input: t_Slice f) (out: t_Slice f) (ops: Nickel.EventGraph.graph_ops f i e) (choice: Option.t_Option usize) : Type0 =
  fresh_prefix input out ops (Seq.length input) choice

let choose_is_fresh (#f: Type0) (#i: Type0) (#e: Type0) (input: t_Slice f) (out: t_Slice f) (ops: Nickel.EventGraph.graph_ops f i e) : Lemma (ensures Nickel.LoopUtil.result_safe (fresh_choice input out ops) (fun (_: e) -> Prims.l_True) (Native.choose_unseen input out ops)) [SMTPat (Native.choose_unseen input out ops)] =
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len input) (fun (at: nat) (choice: Option.t_Option usize) -> fresh_prefix input out ops at choice) (fun (choice: Option.t_Option usize) -> choice) (fresh_choice input out ops) (fun (_: e) -> Prims.l_True);
  assert (Nickel.LoopUtil.result_safe (fresh_choice input out ops) (fun (_: e) -> Prims.l_True) (Native.choose_unseen input out ops)) by (
    Tactics.prune "Nickel_crdt.Event_layer.has_fact";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.smt_sync' 1 1
  )

let strict_lt (#f: Type0) (#i: Type0) (#e: Type0) (ops: Nickel.EventGraph.graph_ops f i e) : Type0 =
  Prims.l_and (forall(a: i). Prims.l_not (ops._1._4 a a == true)) (forall(a: i) (b: i) (c: i). Prims.l_and (ops._1._4 a b == true) (ops._1._4 b c == true) ==> ops._1._4 a c == true)

let unseen (#f: Type0) (#i: Type0) (#e: Type0) (input: t_Slice f) (out: t_Slice f) (ops: Nickel.EventGraph.graph_ops f i e) (j: usize{v j < Seq.length input}) : Type0 =
  Prims.l_not (Native.has_fact out (ops._1._1 (Rust_primitives.Slice.slice_index input j)) ops == true)

let least_prefix (#f: Type0) (#i: Type0) (#e: Type0) (input: t_Slice f) (out: t_Slice f) (ops: Nickel.EventGraph.graph_ops f i e) (at: nat) (choice: Option.t_Option usize) : Type0 =
  match choice with | Option.Option_None -> begin forall(j: usize{v j < Seq.length input}). v j < at ==> Prims.l_not (unseen input out ops j) end | Option.Option_Some k -> begin Prims.l_and (Prims.l_and (Prims.l_and (v k < at) (v k < Seq.length input)) (unseen input out ops k)) (forall(j: usize{v j < Seq.length input}). Prims.l_and (v j < at) (unseen input out ops j) ==> Prims.l_not (ops._1._4 (ops._1._1 (Rust_primitives.Slice.slice_index input j)) (ops._1._1 (Rust_primitives.Slice.slice_index input k)) == true)) end

let least_choice (#f: Type0) (#i: Type0) (#e: Type0) (input: t_Slice f) (out: t_Slice f) (ops: Nickel.EventGraph.graph_ops f i e) (choice: Option.t_Option usize) : Type0 =
  least_prefix input out ops (Seq.length input) choice

let least_next (#f: Type0) (#i: Type0) (#e: Type0) (input: t_Slice f) (out: t_Slice f) (ops: Nickel.EventGraph.graph_ops f i e) (j: usize{v j < Seq.length input}) (choice: Option.t_Option usize) : Option.t_Option usize =
  if Native.has_fact out (ops._1._1 (Rust_primitives.Slice.slice_index input j)) ops then
    begin choice end
  else
    begin match choice with | Option.Option_None -> begin Option.Option_Some j end | Option.Option_Some k -> begin if v k < v (Core_models.Slice.impl__len input) && ops._1._4 (ops._1._1 (Rust_primitives.Slice.slice_index input j)) (ops._1._1 (Rust_primitives.Slice.slice_index input k)) then
      begin Option.Option_Some j end
    else
      begin choice end end end

let least_extends (#f: Type0) (#i: Type0) (#e: Type0) (input: t_Slice f) (out: t_Slice f) (ops: Nickel.EventGraph.graph_ops f i e) : Lemma (requires strict_lt ops) (ensures forall(j: Nickel.LoopUtil.position (mk_usize 0) (Core_models.Slice.impl__len input)) (choice: Option.t_Option usize). least_prefix input out ops (v j) choice ==> least_prefix input out ops (v j + 1) (least_next input out ops j choice)) =
  let each (j: Nickel.LoopUtil.position (mk_usize 0) (Core_models.Slice.impl__len input)) (choice: Option.t_Option usize) : Lemma (ensures least_prefix input out ops (v j) choice ==> least_prefix input out ops (v j + 1) (least_next input out ops j choice)) = if Native.has_fact out (ops._1._1 (Rust_primitives.Slice.slice_index input j)) ops then
    begin () end
  else
    begin match choice with | Option.Option_None -> begin () end | Option.Option_Some k -> begin if v k < v (Core_models.Slice.impl__len input) && ops._1._4 (ops._1._1 (Rust_primitives.Slice.slice_index input j)) (ops._1._1 (Rust_primitives.Slice.slice_index input k)) then
      begin () end
    else
      begin () end end end in
  FStar.Classical.forall_intro_2 each

let appended_content (#f: Type0) (#i: Type0) (#e: Type0) (input: t_Slice f) (out: vector f) (ops: Nickel.EventGraph.graph_ops f i e) (result: vector f & Result.t_Result unit e) : Type0 =
  match result with | (next, Result.Result_Ok _) -> begin content_prefix input (Seq.length (Alloc.Vec.impl_1__as_slice out) + 1) next ops._1._1 end | _ -> begin Prims.l_True end

let append_preserves_content (#f: Type0) (#i: Type0) (#e: Type0) (input: t_Slice f) (out: vector f) (item: f) (ops: Nickel.EventGraph.graph_ops f i e) : Lemma (requires (exact_values ops /\ content_prefix input (Seq.length (Alloc.Vec.impl_1__as_slice out)) out ops._1._1 /\ present input item /\ Prims.l_not (Native.has_fact (Alloc.Vec.impl_1__as_slice out) (ops._1._1 item) ops == true))) (ensures appended_content input out ops (Native.push out item ops._2._1)) =
  Nickel.EventGraph.fact_membership_is_exact (Alloc.Vec.impl_1__as_slice out) (ops._1._1 item) ops;
  let each_absent (j: nat{j < Seq.length (Alloc.Vec.impl_1__as_slice out)}) : Lemma (ensures ops._1._1 (Seq.index (Alloc.Vec.impl_1__as_slice out) j) =!= ops._1._1 item) =
    assert (v (mk_usize j) == j);
    assert (ops._1._3 (ops._1._1 (Seq.index (Alloc.Vec.impl_1__as_slice out) (v (mk_usize j)))) (ops._1._1 item) == false) by (
      Tactics.prune "Nickel_crdt.Event_layer.has_fact";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro each_absent;
  push_is_exact out item ops._2._1;
  Nickel.Vector.vector_length out;
  if v (Alloc.Vec.impl_1__len out) ==? max_usize then
    begin () end
  else
    begin Nickel.Vector.vector_from_seq_value (Seq.append (Alloc.Vec.impl_1__as_slice out) (Seq.create 1 item)) end;
  assert (appended_content input out ops (Native.push out item ops._2._1)) by (
    Tactics.prune "Nickel_crdt.Event_layer.has_fact";
    Tactics.prune "Nickel_crdt.Event_layer.push";
    Tactics.smt_sync' 1 1
  )

let copy_selected_is_exact (#f: Type0) (item: f) (copy: f -> f) : Lemma (requires copy item == item) (ensures Native.clone_selected_fact item copy == item) [SMTPat (Native.clone_selected_fact item copy)] =
  ()

let step_result (#f: Type0) (#i: Type0) (#e: Type0) (input: t_Slice f) (out: vector f) (ops: Nickel.EventGraph.graph_ops f i e) : Result.t_Result (vector f) e =
  match Native.choose_unseen input (Alloc.Vec.impl_1__as_slice out) ops with | Result.Result_Err err -> begin Result.Result_Err err end | Result.Result_Ok Option.Option_None -> begin Result.Result_Err (ops._2._1 ()) end | Result.Result_Ok (Option.Option_Some k) -> begin if v k < Seq.length input then
    begin match Native.push out (Native.clone_selected_fact (Rust_primitives.Slice.slice_index input k) ops._1._5) ops._2._1 with | (next, Result.Result_Ok _) -> begin Result.Result_Ok next end | (_, Result.Result_Err err) -> begin Result.Result_Err err end end
  else
    begin Result.Result_Err (ops._2._1 ()) end end

let step_uses_selected_fact (#f: Type0) (#i: Type0) (#e: Type0) (input: t_Slice f) (out: vector f) (ops: Nickel.EventGraph.graph_ops f i e) : Lemma (ensures Native.canonical_step input out ops == step_result input out ops) =
  assert (Native.canonical_step input out ops == step_result input out ops) by (
    Tactics.prune "Nickel_crdt.Event_layer.choose_unseen";
    Tactics.prune "Nickel_crdt.Event_layer.clone_selected_fact";
    Tactics.prune "Nickel_crdt.Event_layer.push";
    Tactics.smt_sync' 1 1
  )

let step_preserves_content (#f: Type0) (#i: Type0) (#e: Type0) (input: t_Slice f) (out: vector f) (at: nat) (ops: Nickel.EventGraph.graph_ops f i e) : Lemma (requires (exact_values ops /\ content_prefix input at out ops._1._1)) (ensures Nickel.LoopUtil.result_safe (fun (next: vector f) -> content_prefix input (at + 1) next ops._1._1) (fun (_: e) -> Prims.l_True) (Native.canonical_step input out ops)) =
  step_uses_selected_fact input out ops;
  choose_is_fresh input (Alloc.Vec.impl_1__as_slice out) ops;
  assert (Nickel.LoopUtil.result_safe (fresh_choice input (Alloc.Vec.impl_1__as_slice out) ops) (fun (_: e) -> Prims.l_True) (Native.choose_unseen input (Alloc.Vec.impl_1__as_slice out) ops)) by (
    Tactics.prune "Nickel_crdt.Event_layer.choose_unseen";
    Tactics.smt_sync' 1 1
  );
  match Native.choose_unseen input (Alloc.Vec.impl_1__as_slice out) ops with | Result.Result_Err _ -> begin assert (Nickel.LoopUtil.result_safe (fun (next: vector f) -> content_prefix input (at + 1) next ops._1._1) (fun (_: e) -> Prims.l_True) (Native.canonical_step input out ops)) by (
    Tactics.prune "Nickel_crdt.Event_layer.choose_unseen";
    Tactics.prune "Nickel_crdt.Event_layer.canonical_step";
    Tactics.prune "Nickel_crdt.Event_layer.clone_selected_fact";
    Tactics.prune "Nickel_crdt.Event_layer.push";
    Tactics.prune "Nickel.Canonical.push_is_exact";
    Tactics.smt_sync' 1 1
  ) end | Result.Result_Ok Option.Option_None -> begin assert (Nickel.LoopUtil.result_safe (fun (next: vector f) -> content_prefix input (at + 1) next ops._1._1) (fun (_: e) -> Prims.l_True) (Native.canonical_step input out ops)) by (
    Tactics.prune "Nickel_crdt.Event_layer.choose_unseen";
    Tactics.prune "Nickel_crdt.Event_layer.canonical_step";
    Tactics.prune "Nickel_crdt.Event_layer.clone_selected_fact";
    Tactics.prune "Nickel_crdt.Event_layer.push";
    Tactics.prune "Nickel.Canonical.push_is_exact";
    Tactics.smt_sync' 1 1
  ) end | Result.Result_Ok (Option.Option_Some k) -> begin if v k < Seq.length input then
    begin copy_selected_is_exact (Rust_primitives.Slice.slice_index input k) ops._1._5;
    assert (present input (Rust_primitives.Slice.slice_index input k));
    append_preserves_content input out (Rust_primitives.Slice.slice_index input k) ops;
    assert (Nickel.LoopUtil.result_safe (fun (next: vector f) -> content_prefix input (at + 1) next ops._1._1) (fun (_: e) -> Prims.l_True) (Native.canonical_step input out ops)) by (
      Tactics.prune "Nickel_crdt.Event_layer.choose_unseen";
      Tactics.prune "Nickel_crdt.Event_layer.canonical_step";
      Tactics.prune "Nickel_crdt.Event_layer.clone_selected_fact";
      Tactics.prune "Nickel_crdt.Event_layer.push";
      Tactics.prune "Nickel.Canonical.push_is_exact";
      Tactics.smt_sync' 1 1
    ) end
  else
    begin assert (Nickel.LoopUtil.result_safe (fun (next: vector f) -> content_prefix input (at + 1) next ops._1._1) (fun (_: e) -> Prims.l_True) (Native.canonical_step input out ops)) by (
      Tactics.prune "Nickel_crdt.Event_layer.choose_unseen";
      Tactics.prune "Nickel_crdt.Event_layer.canonical_step";
      Tactics.prune "Nickel_crdt.Event_layer.clone_selected_fact";
      Tactics.prune "Nickel_crdt.Event_layer.push";
      Tactics.prune "Nickel.Canonical.push_is_exact";
      Tactics.smt_sync' 1 1
    ) end end

let canonical_selects_whole_facts (#f: Type0) (#i: Type0) (#e: Type0) (input: t_Slice f) (ops: Nickel.EventGraph.graph_ops f i e) : Lemma (requires exact_values ops) (ensures Nickel.LoopUtil.result_safe (fun (out: vector f) -> content_prefix input (Seq.length input) out ops._1._1) (fun (_: e) -> Prims.l_True) (Native.canonical input ops)) =
  Nickel.Vector.empty_vector_value #f ();
  let each_step (out: vector f) : Lemma (requires content_prefix input (Seq.length (Alloc.Vec.impl_1__as_slice out)) out ops._1._1) (ensures Nickel.LoopUtil.result_safe (fun (next: vector f) -> content_prefix input (Seq.length (Alloc.Vec.impl_1__as_slice out) + 1) next ops._1._1) (fun (_: e) -> Prims.l_True) (Native.canonical_step input out ops)) [SMTPat (Native.canonical_step input out ops)] =
    step_preserves_content input out (Seq.length (Alloc.Vec.impl_1__as_slice out)) ops;
    assert (Nickel.LoopUtil.result_safe (fun (next: vector f) -> content_prefix input (Seq.length (Alloc.Vec.impl_1__as_slice out) + 1) next ops._1._1) (fun (_: e) -> Prims.l_True) (Native.canonical_step input out ops)) by (
      Tactics.prune "Nickel_crdt.Event_layer.canonical_step";
      Tactics.smt_sync' 1 1
    ) in
  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len input) (fun (at: nat) (out: vector f) -> content_prefix input at out ops._1._1) (fun (out: vector f) -> out) (fun (out: vector f) -> content_prefix input (Seq.length input) out ops._1._1) (fun (_: e) -> Prims.l_True);
  assert (Nickel.LoopUtil.result_safe (fun (out: vector f) -> content_prefix input (Seq.length input) out ops._1._1) (fun (_: e) -> Prims.l_True) (Native.canonical input ops)) by (
    Tactics.prune "Nickel_crdt.Event_layer.canonical_step";
    Tactics.prune "Alloc.Vec.impl__new";
    Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
    Tactics.smt_sync' 1 1
  )

let position (#f: Type0) (#i: Type0) (#e: Type0) (input: t_Slice f) (item: f{present input item}) (ops: Nickel.EventGraph.graph_ops f i e{exact_values ops}) : at: nat{Prims.l_and (at < Seq.length input) (Seq.index input at == item)} =
  match FStar.Fin.find input (fun (old: f) -> ops._1._6 old item) 0 with | Some at -> begin at end | None -> begin 0 end

let squeezed (#f: Type0) (#i: Type0) (#e: Type0) (input: t_Slice f{Seq.length input > 1}) (ops: Nickel.EventGraph.graph_ops f i e{exact_values ops}) (out: vector f{content_prefix input (Seq.length input) out ops._1._1}) (missing: nat{Prims.l_and (missing < Seq.length input) (Prims.l_not (present (Alloc.Vec.impl_1__as_slice out) (Seq.index input missing)))}) (at: nat{at < Seq.length (Alloc.Vec.impl_1__as_slice out)}) : FStar.Fin.under (Seq.length input - 1) =
  let pos = position input (Seq.index (Alloc.Vec.impl_1__as_slice out) at) ops in
  if pos < missing then
    begin pos end
  else
    begin pos - 1 end

let squeeze_collision (#f: Type0) (#i: Type0) (#e: Type0) (input: t_Slice f{Seq.length input > 1}) (ops: Nickel.EventGraph.graph_ops f i e{exact_values ops}) (out: vector f{content_prefix input (Seq.length input) out ops._1._1}) (missing: nat{Prims.l_and (missing < Seq.length input) (Prims.l_not (present (Alloc.Vec.impl_1__as_slice out) (Seq.index input missing)))}) (a: nat{a < Seq.length (Alloc.Vec.impl_1__as_slice out)}) (b: nat{b < Seq.length (Alloc.Vec.impl_1__as_slice out)}) : Lemma (requires squeezed input ops out missing a == squeezed input ops out missing b) (ensures a == b) =
  ()

let whole_selection_covers (#f: Type0) (#i: Type0) (#e: Type0) (input: t_Slice f) (out: vector f) (ops: Nickel.EventGraph.graph_ops f i e) : Lemma (requires (exact_values ops /\ content_prefix input (Seq.length input) out ops._1._1)) (ensures forall(item: f). present input item <==> present (Alloc.Vec.impl_1__as_slice out) item) =
  let no_missing (at: nat{at < Seq.length input}) : Lemma (requires Prims.l_not (present (Alloc.Vec.impl_1__as_slice out) (Seq.index input at))) (ensures Prims.l_False) = if Seq.length input > 1 then
    begin let positions = Seq.init (Seq.length input) (squeezed input ops out at) in
    Seq.lemma_init_len (Seq.length input) (squeezed input ops out at);
    Seq.init_index (Seq.length input) (squeezed input ops out at);
    match FStar.Fin.pigeonhole positions with | (a, b) -> begin assert (a < b);
    assert (squeezed input ops out at a == squeezed input ops out at b);
    squeeze_collision input ops out at a b end end
  else
    begin assert (Seq.length input == 1);
    assert (present input (Seq.index (Alloc.Vec.impl_1__as_slice out) 0));
    assert (Seq.index (Alloc.Vec.impl_1__as_slice out) 0 == Seq.index input at);
    assert (present (Alloc.Vec.impl_1__as_slice out) (Seq.index input at)) end in
  FStar.Classical.forall_intro (FStar.Classical.move_requires no_missing);
  ()

let exact_contents (#f: Type0) (input: t_Slice f) (out: vector f) : Type0 =
  Prims.l_and (Seq.length (Alloc.Vec.impl_1__as_slice out) == Seq.length input) (forall(item: f). present input item <==> present (Alloc.Vec.impl_1__as_slice out) item)

let canonical_preserves_exact_contents (#f: Type0) (#i: Type0) (#e: Type0) (input: t_Slice f) (ops: Nickel.EventGraph.graph_ops f i e) : Lemma (requires exact_values ops) (ensures Nickel.LoopUtil.result_safe (exact_contents input) (fun (_: e) -> Prims.l_True) (Native.canonical input ops)) =
  canonical_selects_whole_facts input ops;
  match Native.canonical input ops with | Result.Result_Ok out -> begin whole_selection_covers input out ops;
  assert (Nickel.LoopUtil.result_safe (exact_contents input) (fun (_: e) -> Prims.l_True) (Native.canonical input ops)) by (
    Tactics.prune "Nickel_crdt.Event_layer.canonical";
    Tactics.smt_sync' 1 1
  ) end | Result.Result_Err _ -> begin assert (Nickel.LoopUtil.result_safe (exact_contents input) (fun (_: e) -> Prims.l_True) (Native.canonical input ops)) by (
    Tactics.prune "Nickel_crdt.Event_layer.canonical";
    Tactics.smt_sync' 1 1
  ) end