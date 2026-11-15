(* Latte generated F* view *)
module Nickel.RegisterFrontier

open Nickel.Prelude

open Rust_primitives

open Core_models

open FStar.Pervasives

open Nickel.LoopUtil

module Native = Nickel_crdt.Register

module Graph = Nickel_crdt.Event_layer

module Envelope = Nickel_crdt.Causal

module Seq = FStar.Seq

module List = FStar.List.Tot.Base

module Tactics = FStar.Tactics.V2

open Nickel.Register

open Nickel.RegisterPast

open Nickel.RegisterHistory

open Nickel.RegisterValid

open Nickel.RegisterPublic

open Nickel.Canonical

let terminal (h: Seq.seq Nickel.Register.fact) (f: Nickel.Register.fact) : Type0 =
  Prims.l_not (exists(child: Nickel.Register.fact). Prims.l_and (stored h child) (Nickel.RegisterPast.member (Alloc.Vec.impl_1__as_slice child.f_after) f.f_id))

let terminal_cover (h: Seq.seq Nickel.Register.fact) (f: Nickel.Register.fact) : Type0 =
  exists(root: Nickel.Register.fact) (steps: Prims.list Envelope.t_Id). Prims.l_and (Prims.l_and (stored h root) (terminal h root)) (id_path h root.f_id steps f.f_id)

let rec append_id_edge (h: Seq.seq Nickel.Register.fact) (root: Envelope.t_Id) (steps: Prims.list Envelope.t_Id) (parent: Envelope.t_Id) (child: Envelope.t_Id) : Lemma (requires Prims.l_and (id_path h root steps parent) (id_edge h parent child)) (ensures id_path h root (List.append steps (Prims.Cons child Prims.Nil)) child) (decreases steps) =
  match steps with | Prims.Nil -> begin () end | Prims.Cons next rest -> begin append_id_edge h next rest parent child end

let rec terminal_above (h: Seq.seq Nickel.Register.fact) (f: Nickel.Register.fact) (fuel: nat) : Lemma (requires (Prims.l_and (stored h f) (id_clocks_increase h) /\ v f.f_payload.f_lamport + fuel >= Rust_primitives.Integers.maxint Rust_primitives.Integers.U64)) (ensures terminal_cover h f) (decreases fuel) =
  let via (child: Nickel.Register.fact) : Lemma (requires Prims.l_and (stored h child) (Nickel.RegisterPast.member (Alloc.Vec.impl_1__as_slice child.f_after) f.f_id)) (ensures terminal_cover h f) =
    assert (v f.f_payload.f_lamport < v child.f_payload.f_lamport);
    assert (fuel > 0);
    terminal_above h child (fuel - 1);
    assert (id_edge h child.f_id f.f_id);
    let extend (root: Nickel.Register.fact) (steps: Prims.list Envelope.t_Id) : Lemma (requires Prims.l_and (Prims.l_and (stored h root) (terminal h root)) (id_path h root.f_id steps child.f_id)) (ensures terminal_cover h f) =
      append_id_edge h root.f_id steps child.f_id f.f_id;
      assert (terminal_cover h f) in
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 extend) in
  FStar.Classical.forall_intro (FStar.Classical.move_requires via);
  assert (id_path h f.f_id Prims.Nil f.f_id);
  assert (terminal h f ==> terminal_cover h f);
  assert (terminal_cover h f)

let every_stored_fact_has_a_terminal_ancestor_root (h: Seq.seq Nickel.Register.fact) (f: Nickel.Register.fact) : Lemma (requires Prims.l_and (stored h f) (id_clocks_increase h)) (ensures terminal_cover h f) =
  terminal_above h f (Rust_primitives.Integers.maxint Rust_primitives.Integers.U64 - v f.f_payload.f_lamport)

let rec nonparent_position_is_kept_induct (#f: Type0) (#i: Type0) (#e: Type0) (input: t_Slice f) (ops: Nickel.EventGraph.graph_ops f i e) (at: nat{at <= Seq.length input}) (out: Seq.seq i) (j: nat{j < at}) : Lemma (requires (Nickel.Canonical.frontier_prefix input ops at out /\ Prims.l_not (Nickel.Canonical.mentioned_before input (ops._1._1 (Seq.index input j)) ops (Seq.length input)))) (ensures exists(k: nat). Prims.l_and (k < Seq.length out) (Seq.index out k == ops._1._1 (Seq.index input j))) (decreases at) =
  let wanted = ops._1._1 (Seq.index input j) in
  let last = ops._1._1 (Seq.index input (at - 1)) in
  Nickel.Canonical.frontier_prefix_step input ops at out;
  assert (Prims.l_or (Prims.l_and (Nickel.Canonical.mentioned_before input last ops (Seq.length input)) (Nickel.Canonical.frontier_prefix input ops (at - 1) out)) (Prims.l_and (Prims.l_not (Nickel.Canonical.mentioned_before input last ops (Seq.length input))) (exists(previous: Seq.seq i). Prims.l_and (Nickel.Canonical.frontier_prefix input ops (at - 1) previous) (out == Seq.append previous (Seq.create 1 last)))));
  if j ==? at - 1 then
    begin let last_position (previous: Seq.seq i) : Lemma (requires out == Seq.append previous (Seq.create 1 last)) (ensures exists(k: nat). Prims.l_and (k < Seq.length out) (Seq.index out k == wanted)) = assert (Seq.index out (Seq.length previous) == wanted) in
    FStar.Classical.forall_intro (FStar.Classical.move_requires last_position) end
  else
    begin let previous_position (previous: Seq.seq i) : Lemma (requires (Nickel.Canonical.frontier_prefix input ops (at - 1) previous /\ Prims.l_or (out == previous) (out == Seq.append previous (Seq.create 1 last)))) (ensures exists(k: nat). Prims.l_and (k < Seq.length out) (Seq.index out k == wanted)) =
      nonparent_position_is_kept_induct input ops (at - 1) previous j;
      let carry (k: nat) : Lemma (requires Prims.l_and (k < Seq.length previous) (Seq.index previous k == wanted)) (ensures exists(k: nat). Prims.l_and (k < Seq.length out) (Seq.index out k == wanted)) = assert (Seq.index out k == wanted) in
      FStar.Classical.forall_intro (FStar.Classical.move_requires carry) in
    FStar.Classical.forall_intro (FStar.Classical.move_requires previous_position) end

let nonparent_position_is_kept (#f: Type0) (#i: Type0) (#e: Type0) (input: t_Slice f) (ops: Nickel.EventGraph.graph_ops f i e) (at: nat{at <= Seq.length input}) (out: Seq.seq i) (j: nat{j < at}) : Lemma (requires (Nickel.Canonical.frontier_prefix input ops at out /\ Prims.l_not (Nickel.Canonical.mentioned_before input (ops._1._1 (Seq.index input j)) ops (Seq.length input)))) (ensures exists(k: nat). Prims.l_and (k < Seq.length out) (Seq.index out k == ops._1._1 (Seq.index input j))) =
  nonparent_position_is_kept_induct input ops at out j

let exact_comparison_membership (ids: t_Slice Envelope.t_Id) (id: Envelope.t_Id) (ops: Nickel.RegisterPast.rops) : Lemma (requires Nickel.RegisterPast.ids_exact ops) (ensures Nickel.EventGraph.member ids id ops._1._3 <==> Nickel.RegisterPast.member ids id) =
  let each (at: usize{v at < Seq.length ids}) : Lemma (ensures ops._1._3 (Seq.index ids (v at)) id == false <==> Seq.index ids (v at) =!= id) = () in
  FStar.Classical.forall_intro each

let register_member_matches_generic (ids: t_Slice Envelope.t_Id) (id: Envelope.t_Id) : Lemma (ensures Nickel.EventGraph.member ids id Native.v_OPS._1._1._3 <==> Nickel.RegisterPast.member ids id) =
  register_ops_are_exact ();
  assert (Nickel.RegisterPast.ids_exact Native.v_OPS._1) by (
    Tactics.prune "Nickel_crdt.Register.v_OPS";
    Tactics.prune "Nickel_crdt.Register.same_id";
    Tactics.prune "Nickel.RegisterHistory.register_ops_are_exact";
    Tactics.smt_sync' 1 1
  );
  exact_comparison_membership ids id Native.v_OPS._1

let terminal_is_not_mentioned (h: t_Slice Nickel.Register.fact) (f: Nickel.Register.fact) : Lemma (requires terminal h f) (ensures Prims.l_not (Nickel.Canonical.mentioned_before h f.f_id Native.v_OPS._1 (Seq.length h))) =
  register_ops_are_exact ();
  let each (j: nat{j < Seq.length h}) : Lemma (ensures Prims.l_not (Nickel.EventGraph.member (Native.v_OPS._1._1._2 (Seq.index h j)) f.f_id Native.v_OPS._1._1._3)) =
    let child = Seq.index h j in
    assert (stored h child);
    assert (Native.v_OPS._1._1._2 child == Alloc.Vec.impl_1__as_slice child.f_after) by (
      Tactics.prune "Nickel_crdt.Register.v_OPS";
      Tactics.prune "Nickel_crdt.Register.parents";
      Tactics.prune "Nickel.RegisterHistory.register_ops_are_exact";
      Tactics.smt_sync' 1 1
    );
    register_member_matches_generic (Alloc.Vec.impl_1__as_slice child.f_after) f.f_id in
  FStar.Classical.forall_intro each

let terminal_occurs_in_filter (h: t_Slice Nickel.Register.fact) (out: Alloc.Vec.t_Vec Envelope.t_Id Alloc.Alloc.t_Global) (f: Nickel.Register.fact) : Lemma (requires (Prims.l_and (stored h f) (terminal h f) /\ Nickel.Canonical.frontier_state h Native.v_OPS._1 (Seq.length h) out)) (ensures Nickel.RegisterPast.member (Alloc.Vec.impl_1__as_slice out) f.f_id) =
  register_ops_are_exact ();
  terminal_is_not_mentioned h f;
  let at (j: nat) : Lemma (requires Prims.l_and (j < Seq.length h) (Seq.index h j == f)) (ensures Nickel.RegisterPast.member (Alloc.Vec.impl_1__as_slice out) f.f_id) =
    assert (Native.v_OPS._1._1._1 (Seq.index h j) == f.f_id) by (
      Tactics.prune "Nickel_crdt.Register.v_OPS";
      Tactics.prune "Nickel_crdt.Register.identity";
      Tactics.prune "Nickel.RegisterHistory.register_ops_are_exact";
      Tactics.smt_sync' 1 1
    );
    nonparent_position_is_kept h Native.v_OPS._1 (Seq.length h) (Alloc.Vec.impl_1__as_slice out) j;
    let found (k: nat{k < Seq.length (Alloc.Vec.impl_1__as_slice out)}) : Lemma (requires Seq.index (Alloc.Vec.impl_1__as_slice out) k == f.f_id) (ensures Nickel.RegisterPast.member (Alloc.Vec.impl_1__as_slice out) f.f_id) =
      let index = mk_usize k in
      assert (v index == k);
      assert (Prims.l_not (Nickel.RegisterPast.absent_prefix (Alloc.Vec.impl_1__as_slice out) f.f_id (Seq.length (Alloc.Vec.impl_1__as_slice out)))) in
    FStar.Classical.forall_intro (FStar.Classical.move_requires found) in
  FStar.Classical.forall_intro (FStar.Classical.move_requires at)

let roots_cover (h: t_Slice Nickel.Register.fact) (roots: t_Slice Envelope.t_Id) : Type0 =
  forall(f: Nickel.Register.fact). stored h f ==> Nickel.RegisterPast.ancestor Native.v_OPS._1 h roots f.f_id

let filter_covers_history (h: t_Slice Nickel.Register.fact) (out: Alloc.Vec.t_Vec Envelope.t_Id Alloc.Alloc.t_Global) : Lemma (requires (id_clocks_increase h /\ Nickel.Canonical.frontier_state h Native.v_OPS._1 (Seq.length h) out)) (ensures roots_cover h (Alloc.Vec.impl_1__as_slice out)) =
  let each (f: Nickel.Register.fact) : Lemma (requires stored h f) (ensures Nickel.RegisterPast.ancestor Native.v_OPS._1 h (Alloc.Vec.impl_1__as_slice out) f.f_id) =
    every_stored_fact_has_a_terminal_ancestor_root h f;
    let root_at (root: Nickel.Register.fact) (steps: Prims.list Envelope.t_Id) : Lemma (requires Prims.l_and (Prims.l_and (stored h root) (terminal h root)) (id_path h root.f_id steps f.f_id)) (ensures Nickel.RegisterPast.ancestor Native.v_OPS._1 h (Alloc.Vec.impl_1__as_slice out) f.f_id) =
      terminal_occurs_in_filter h out root;
      register_path_is_id_path h root.f_id steps f.f_id in
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 root_at) in
  FStar.Classical.forall_intro (FStar.Classical.move_requires each)

let actual_frontier_covers_history (h: t_Slice Nickel.Register.fact) : Lemma (requires id_clocks_increase h) (ensures exists(out: Alloc.Vec.t_Vec Envelope.t_Id Alloc.Alloc.t_Global). Prims.l_and (Graph.frontier h Native.v_OPS._1 == Core_models.Result.Result_Ok out) (roots_cover h (Alloc.Vec.impl_1__as_slice out))) =
  Nickel.Canonical.frontier_is_nonparent_filter h Native.v_OPS._1;
  FStar.Classical.forall_intro (FStar.Classical.move_requires (filter_covers_history h));
  assert (exists(out: Alloc.Vec.t_Vec Envelope.t_Id Alloc.Alloc.t_Global). Prims.l_and (Graph.frontier h Native.v_OPS._1 == Core_models.Result.Result_Ok out) (roots_cover h (Alloc.Vec.impl_1__as_slice out))) by (
    Tactics.prune "Nickel_crdt.Event_layer.frontier";
    Tactics.prune "Nickel.Canonical.frontier_is_nonparent_filter";
    Tactics.prune "Nickel.Canonical.frontier_state";
    Tactics.prune "Nickel.RegisterFrontier.roots_cover";
    Tactics.smt_sync' 1 1
  )

let counted_installation_frontier (before: Native.t_Replica) (key: u64) (value: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) (next: Native.t_Replica) (authored: Nickel.Register.fact) : Lemma (requires Nickel.Register.write_installation before key value (next, Core_models.Result.Result_Ok (Core_models.Option.Option_Some authored))) (ensures Graph.frontier (Alloc.Vec.impl_1__as_slice before.f_facts) Native.v_OPS._1 == Core_models.Result.Result_Ok authored.f_after) =
  ()

let counted_write_roots_cover_at (before: Native.t_Replica) (key: u64) (value: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) (next: Native.t_Replica) (authored: Nickel.Register.fact) : Lemma (requires (public_history before /\ Native.impl_Replica__write before key value == (next, Core_models.Result.Result_Ok (Core_models.Option.Option_Some authored)))) (ensures roots_cover (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice authored.f_after)) =
  actual_frontier_covers_history (Alloc.Vec.impl_1__as_slice before.f_facts);
  Nickel.Register.write_installs_successful_candidate before key value;
  assert (Nickel.Register.write_installation before key value (next, Core_models.Result.Result_Ok (Core_models.Option.Option_Some authored))) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__write";
    Tactics.prune "Nickel.Register.write_installs_successful_candidate";
    Tactics.prune "Nickel.Register.write_installation";
    Tactics.smt_sync' 1 1
  );
  counted_installation_frontier before key value next authored;
  assert (roots_cover (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice authored.f_after)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__write";
    Tactics.prune "Nickel_crdt.Event_layer.frontier";
    Tactics.prune "Nickel.RegisterFrontier.roots_cover";
    Tactics.smt_sync' 1 1
  )

let counted_write_roots_cover_history (before: Native.t_Replica) (key: u64) (value: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) : Lemma (requires public_history before) (ensures forall(next: Native.t_Replica) (authored: Nickel.Register.fact). Native.impl_Replica__write before key value == (next, Core_models.Result.Result_Ok (Core_models.Option.Option_Some authored)) ==> roots_cover (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice authored.f_after)) =
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (counted_write_roots_cover_at before key value))

let covered_basis_is_whole_history (h: t_Slice Nickel.Register.fact) (roots: t_Slice Envelope.t_Id) (selected: t_Slice Envelope.t_Id) (basis: Seq.seq Nickel.Register.fact) : Lemma (requires (roots_cover h roots /\ (forall(id: Envelope.t_Id). Nickel.RegisterPast.member selected id <==> Nickel.RegisterPast.ancestor Native.v_OPS._1 h roots id) /\ Nickel.RegisterPast.selected_prefix Native.v_OPS._1 h selected (Seq.length h) basis)) (ensures basis == h) =
  register_ops_are_exact ();
  let each (j: nat{j < Seq.length h}) : Lemma (ensures Nickel.RegisterPast.member selected (Native.v_OPS._1._1._1 (Seq.index h j))) =
    assert (stored h (Seq.index h j));
    assert (Native.v_OPS._1._1._1 (Seq.index h j) == (Seq.index h j).f_id) by (
      Tactics.prune "Nickel_crdt.Register.v_OPS";
      Tactics.prune "Nickel_crdt.Register.identity";
      Tactics.prune "Nickel.RegisterHistory.register_ops_are_exact";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro each;
  Nickel.RegisterPast.all_selected_prefix_is_input Native.v_OPS._1 h selected (Seq.length h) basis

let whole_basis (before: Native.t_Replica) (authored: Nickel.Register.fact) : Type0 =
  exists(selected: Alloc.Vec.t_Vec Envelope.t_Id Alloc.Alloc.t_Global) (basis: Alloc.Vec.t_Vec Nickel.Register.fact Alloc.Alloc.t_Global). Prims.l_and (Prims.l_and (Graph.validate_event (Alloc.Vec.impl_1__as_slice before.f_facts) authored before.f_limits.f_events before.f_limits.f_dependencies Native.v_OPS == Core_models.Result.Result_Ok selected) (Graph.select_basis (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice selected) Native.v_OPS._1 == Core_models.Result.Result_Ok basis)) (Alloc.Vec.impl_1__as_slice basis == Alloc.Vec.impl_1__as_slice before.f_facts)

let exact_basis_is_whole (before: Native.t_Replica) (authored: Nickel.Register.fact) : Lemma (requires Prims.l_and (roots_cover (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice authored.f_after)) (exact_selected_basis before authored)) (ensures whole_basis before authored) =
  let exact (selected: Alloc.Vec.t_Vec Envelope.t_Id Alloc.Alloc.t_Global) (basis: Alloc.Vec.t_Vec Nickel.Register.fact Alloc.Alloc.t_Global) : Lemma (requires (Graph.validate_event (Alloc.Vec.impl_1__as_slice before.f_facts) authored before.f_limits.f_events before.f_limits.f_dependencies Native.v_OPS == Core_models.Result.Result_Ok selected /\ Graph.select_basis (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice selected) Native.v_OPS._1 == Core_models.Result.Result_Ok basis /\ (forall(id: Envelope.t_Id). Nickel.RegisterPast.member (Alloc.Vec.impl_1__as_slice selected) id <==> Nickel.RegisterPast.ancestor Native.v_OPS._1 (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice authored.f_after) id) /\ Nickel.RegisterPast.selected_prefix Native.v_OPS._1 (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice selected) (Seq.length (Alloc.Vec.impl_1__as_slice before.f_facts)) (Alloc.Vec.impl_1__as_slice basis))) (ensures Alloc.Vec.impl_1__as_slice basis == Alloc.Vec.impl_1__as_slice before.f_facts) = covered_basis_is_whole_history (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice authored.f_after) (Alloc.Vec.impl_1__as_slice selected) (Alloc.Vec.impl_1__as_slice basis) in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 exact);
  assert (whole_basis before authored) by (
    Tactics.prune "Nickel_crdt.Event_layer.validate_event";
    Tactics.prune "Nickel_crdt.Event_layer.select_basis";
    Tactics.smt_sync' 1 1
  )

let added_basis_at (before: Native.t_Replica) (authored: Nickel.Register.fact) (received: Native.t_Replica) : Lemma (requires Native.impl_Replica__receive before authored == (received, Core_models.Result.Result_Ok Native.Admission_Added)) (ensures exact_selected_basis before authored) =
  receive_added_basis_is_exact_ancestry before authored;
  assert (exact_selected_basis before authored) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel.RegisterHistory.receive_added_basis_is_exact_ancestry";
    Tactics.prune "Nickel.RegisterHistory.exact_selected_basis";
    Tactics.smt_sync' 1 1
  )

let counted_write_basis_is_whole_history_at (before: Native.t_Replica) (key: u64) (value: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) (next: Native.t_Replica) (authored: Nickel.Register.fact) : Lemma (requires (public_history before /\ Native.impl_Replica__write before key value == (next, Core_models.Result.Result_Ok (Core_models.Option.Option_Some authored)))) (ensures whole_basis before authored) =
  counted_write_roots_cover_at before key value next authored;
  assert (roots_cover (Alloc.Vec.impl_1__as_slice before.f_facts) (Alloc.Vec.impl_1__as_slice authored.f_after)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__write";
    Tactics.prune "Nickel_crdt.Event_layer.frontier";
    Tactics.prune "Nickel.RegisterFrontier.counted_write_roots_cover_at";
    Tactics.prune "Nickel.RegisterFrontier.roots_cover";
    Tactics.smt_sync' 1 1
  );
  write_counted_is_added_receive before key value next authored;
  assert (Native.impl_Replica__receive before authored == ((Native.impl_Replica__receive before authored)._1, Core_models.Result.Result_Ok Native.Admission_Added)) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__write";
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel_crdt.Register.planned";
    Tactics.prune "Nickel.RegisterPublic.write_counted_is_added_receive";
    Tactics.prune "Nickel.Register.write_installs_successful_candidate";
    Tactics.prune "Nickel.Register.planned_checks_payload";
    Tactics.prune "Nickel.Register.planned_adds_exact_fact";
    Tactics.smt_sync' 1 1
  );
  added_basis_at before authored (Native.impl_Replica__receive before authored)._1;
  assert (exact_selected_basis before authored) by (
    Tactics.prune "Nickel_crdt.Register.impl_Replica__write";
    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";
    Tactics.prune "Nickel.RegisterHistory.exact_selected_basis";
    Tactics.prune "Nickel.RegisterFrontier.added_basis_at";
    Tactics.smt_sync' 1 1
  );
  exact_basis_is_whole before authored;
  assert (whole_basis before authored) by (
    Tactics.prune "Nickel.RegisterFrontier.whole_basis";
    Tactics.prune "Nickel.RegisterFrontier.exact_basis_is_whole";
    Tactics.smt_sync' 1 1
  )

let counted_write_basis_is_whole_history (before: Native.t_Replica) (key: u64) (value: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) : Lemma (requires public_history before) (ensures forall(next: Native.t_Replica) (authored: Nickel.Register.fact). Native.impl_Replica__write before key value == (next, Core_models.Result.Result_Ok (Core_models.Option.Option_Some authored)) ==> whole_basis before authored) =
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (counted_write_basis_is_whole_history_at before key value))