(* Latte generated F* view *)
module Nickel.LoopUtil

open Nickel.Prelude

open Rust_primitives

open Core_models.Ops.Control_flow

open Rust_primitives.Hax.Folds

open FStar.Pervasives

open FStar.Classical

module Tactics = FStar.Tactics.V2

type output (state: Type0) (result: Type0) = t_ControlFlow result state

type iter_output (state: Type0) (result: Type0) = t_ControlFlow (t_ControlFlow result (unit & state)) state

type position (start: usize) (finish: usize) = i: usize{Prims.l_and (v i <= v finish) (fold_range_wf_index start finish true (v i))}

type inv_position (start: usize) (finish: usize) = i: usize{fold_range_wf_index start finish false (v i)}

type invariant (state: Type0) (start: usize) (finish: usize) = state -> inv_position start finish -> Type0

type callback (state: Type0) (result: Type0) (start: usize) (finish: usize) = state -> position start finish -> iter_output state result

let unroll (#state: Type0) (#result: Type0) (start: usize) (finish: usize{v start < v finish}) (inv: invariant state start finish) (value: state) (f: callback state result start finish) : Lemma (ensures fold_range_return start finish inv value f == ((match f value start with | ControlFlow_Break (ControlFlow_Break ret) -> begin ControlFlow_Break ret end | ControlFlow_Break (ControlFlow_Continue (_, next)) -> begin ControlFlow_Continue next end | ControlFlow_Continue next -> begin fold_range_return (start +! mk_int 1) finish inv next f end) <: output state result)) =
  ()

let empty (#state: Type0) (#result: Type0) (start: usize) (finish: usize{v start == v finish}) (inv: invariant state start finish) (value: state) (f: callback state result start finish) : Lemma (ensures fold_range_return start finish inv value f == ControlFlow_Continue value) =
  ()

let output_safe (#state: Type0) (#result: Type0) (post: state -> Type0) (returned: result -> Type0) (out: output state result) : Type0 =
  match out with | ControlFlow_Break ret -> begin returned ret end | ControlFlow_Continue next -> begin post next end

let step_safe (#state: Type0) (#result: Type0) (p: nat -> state -> Type0) (post: state -> Type0) (returned: result -> Type0) (at: nat) (out: iter_output state result) : Type0 =
  match out with | ControlFlow_Break (ControlFlow_Break ret) -> begin returned ret end | ControlFlow_Break (ControlFlow_Continue (_, next)) -> begin post next end | ControlFlow_Continue next -> begin p (at + 1) next end

let rec preserve (#state: Type0) (#result: Type0) (start: usize) (finish: usize{v start <= v finish}) (inv: invariant state start finish) (value: state) (f: callback state result start finish) (p: nat -> state -> Type0) (post: state -> Type0) (returned: result -> Type0) : Lemma (requires (p (v start) value /\ (forall(s: state) (i: position start finish). p (v i) s ==> step_safe p post returned (v i) (f s i)) /\ (forall(s: state). p (v finish) s ==> post s))) (ensures output_safe post returned (fold_range_return start finish inv value f)) (decreases v finish - v start) =
  if v start < v finish then
    begin unroll start finish inv value f;
    assert (step_safe p post returned (v start) (f value start));
    match f value start with | ControlFlow_Break _ -> begin () end | ControlFlow_Continue next -> begin preserve (start +! mk_int 1) finish inv next f p post returned end;
    assert (output_safe post returned (fold_range_return start finish inv value f)) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.smt_sync' 1 1
    ) end
  else
    begin empty start finish inv value f;
    assert (output_safe post returned (fold_range_return start finish inv value f)) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.smt_sync' 1 1
    ) end

module Option = Core_models.Option

type transition (state: Type0) (finish: usize) = state -> (i: usize{v i < v finish}) -> Option.t_Option state

let option_finish (#state: Type0) (#result: Type0) (done: state -> result) (out: output state result) : result =
  match out with | ControlFlow_Break ret -> begin ret end | ControlFlow_Continue next -> begin done next end

let rec option_run (#state: Type0) (#result: Type0) (finish: usize) (at: usize{v at <= v finish}) (value: state) (next: transition state finish) (stop: state -> (i: usize{v i < v finish}) -> result) (done: state -> result) : Tot result (decreases v finish - v at) =
  if v at < v finish then
    begin match next value at with | Option.Option_None -> begin stop value at end | Option.Option_Some value -> begin option_run finish (at +! mk_int 1) value next stop done end end
  else
    begin done value end

let option_run_end (#state: Type0) (#result: Type0) (finish: usize) (at: usize{v at == v finish}) (value: state) (next: transition state finish) (stop: state -> (i: usize{v i < v finish}) -> result) (done: state -> result) : Lemma (ensures option_run finish at value next stop done == done value) =
  ()

let option_run_step (#state: Type0) (#result: Type0) (finish: usize) (at: usize{v at < v finish}) (value: state) (next: transition state finish) (stop: state -> (i: usize{v i < v finish}) -> result) (done: state -> result) : Lemma (ensures option_run finish at value next stop done == ((match next value at with | Option.Option_None -> begin stop value at end | Option.Option_Some value -> begin option_run finish (at +! mk_int 1) value next stop done end) <: result)) =
  ()

let option_agrees (#state: Type0) (#result: Type0) (start: usize) (finish: usize) (f: callback state result start finish) (next: transition state finish) (stop: state -> (i: usize{v i < v finish}) -> result) (done: state -> result) : Type0 =
  forall(value: state) (i: position start finish). ((match f value i with | ControlFlow_Break (ControlFlow_Break ret) -> begin Prims.l_and (next value i == Option.Option_None) (stop value i == ret) end | ControlFlow_Break (ControlFlow_Continue (_, out)) -> begin Prims.l_and (next value i == Option.Option_None) (stop value i == done out) end | ControlFlow_Continue out -> begin next value i == Option.Option_Some out end) <: Type0)

let rec option_interpret (#state: Type0) (#result: Type0) (start: usize) (finish: usize{v start <= v finish}) (inv: invariant state start finish) (value: state) (f: callback state result start finish) (next: transition state finish) (stop: state -> (i: usize{v i < v finish}) -> result) (done: state -> result) : Lemma (requires option_agrees start finish f next stop done) (ensures option_finish done (fold_range_return start finish inv value f) == option_run finish start value next stop done) (decreases v finish - v start) =
  if v start < v finish then
    begin unroll start finish inv value f;
    option_run_step finish start value next stop done;
    match f value start with | ControlFlow_Break (ControlFlow_Break ret) -> begin assert (next value start == Option.Option_None);
    assert (stop value start == ret);
    assert (option_finish done (fold_range_return start finish inv value f) == option_run finish start value next stop done) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.prune "Nickel.LoopUtil.option_run";
      Tactics.smt_sync' 1 1
    ) end | ControlFlow_Break (ControlFlow_Continue (_, out)) -> begin assert (next value start == Option.Option_None);
    assert (stop value start == done out);
    assert (option_finish done (fold_range_return start finish inv value f) == option_run finish start value next stop done) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.prune "Nickel.LoopUtil.option_run";
      Tactics.smt_sync' 1 1
    ) end | ControlFlow_Continue out -> begin assert (next value start == Option.Option_Some out);
    option_interpret (start +! mk_int 1) finish inv out f next stop done;
    assert (option_finish done (fold_range_return start finish inv value f) == option_run finish start value next stop done) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.prune "Nickel.LoopUtil.option_run";
      Tactics.smt_sync' 1 1
    ) end end
  else
    begin empty start finish inv value f;
    option_run_end finish start value next stop done;
    assert (option_finish done (fold_range_return start finish inv value f) == option_run finish start value next stop done) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.prune "Nickel.LoopUtil.option_run";
      Tactics.smt_sync' 1 1
    ) end

let option_interpret_any (#state: Type0) (#result: Type0) (start: usize) (finish: usize{v start <= v finish}) (next: transition state finish) (stop: state -> (i: usize{v i < v finish}) -> result) (done: state -> result) : Lemma (ensures forall(inv: invariant state start finish) (value: state) (f: callback state result start finish). option_agrees start finish f next stop done ==> option_finish done (fold_range_return start finish inv value f) == option_run finish start value next stop done) =
  let each (inv: invariant state start finish) (value: state) (f: callback state result start finish) : Lemma (requires option_agrees start finish f next stop done) (ensures option_finish done (fold_range_return start finish inv value f) == option_run finish start value next stop done) =
    option_interpret start finish inv value f next stop done;
    assert (option_finish done (fold_range_return start finish inv value f) == option_run finish start value next stop done) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.prune "Nickel.LoopUtil.option_run";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 each)

type total_invariant (state: Type0) (start: usize) (finish: usize) = inv: invariant state start finish{forall(value: state) (at: inv_position start finish). inv value at}

type plain_callback (state: Type0) (start: usize) (finish: usize) = state -> position start finish -> state

type break_callback (state: Type0) (start: usize) (finish: usize) = state -> position start finish -> t_ControlFlow (unit & state) state

let plain_agrees (#state: Type0) (start: usize) (finish: usize) (f: plain_callback state start finish) (next: transition state finish) : Type0 =
  forall(value: state) (at: position start finish). next value at == Option.Option_Some (f value at)

let plain_step (#state: Type0) (start: usize) (finish: usize{v start < v finish}) (inv: total_invariant state start finish) (value: state) (f: plain_callback state start finish) : Lemma (ensures fold_range start finish inv value f == fold_range (start +! mk_int 1) finish inv (f value start) f) =
  ()

let plain_end (#state: Type0) (start: usize) (finish: usize{v start == v finish}) (inv: total_invariant state start finish) (value: state) (f: plain_callback state start finish) : Lemma (ensures fold_range start finish inv value f == value) =
  ()

let rec plain_interpret (#state: Type0) (#result: Type0) (start: usize) (finish: usize{v start <= v finish}) (inv: total_invariant state start finish) (value: state) (f: plain_callback state start finish) (next: transition state finish) (stop: state -> (i: usize{v i < v finish}) -> result) (done: state -> result) : Lemma (requires plain_agrees start finish f next) (ensures done (fold_range start finish inv value f) == option_run finish start value next stop done) (decreases v finish - v start) =
  if v start < v finish then
    begin plain_step start finish inv value f;
    option_run_step finish start value next stop done;
    assert (next value start == Option.Option_Some (f value start));
    plain_interpret (start +! mk_int 1) finish inv (f value start) f next stop done;
    assert (done (fold_range start finish inv value f) == option_run finish start value next stop done) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range";
      Tactics.prune "Nickel.LoopUtil.option_run";
      Tactics.smt_sync' 1 1
    ) end
  else
    begin plain_end start finish inv value f;
    option_run_end finish start value next stop done;
    assert (done (fold_range start finish inv value f) == option_run finish start value next stop done) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range";
      Tactics.prune "Nickel.LoopUtil.option_run";
      Tactics.smt_sync' 1 1
    ) end

let plain_interpret_any (#state: Type0) (#result: Type0) (start: usize) (finish: usize{v start <= v finish}) (next: transition state finish) (stop: state -> (i: usize{v i < v finish}) -> result) (done: state -> result) : Lemma (ensures forall(inv: total_invariant state start finish) (value: state) (f: plain_callback state start finish). plain_agrees start finish f next ==> done (fold_range start finish inv value f) == option_run finish start value next stop done) =
  let each (inv: total_invariant state start finish) (value: state) (f: plain_callback state start finish) : Lemma (requires plain_agrees start finish f next) (ensures done (fold_range start finish inv value f) == option_run finish start value next stop done) =
    plain_interpret start finish inv value f next stop done;
    assert (done (fold_range start finish inv value f) == option_run finish start value next stop done) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 each)

let break_agrees (#state: Type0) (#result: Type0) (start: usize) (finish: usize) (f: break_callback state start finish) (next: transition state finish) (stop: state -> (i: usize{v i < v finish}) -> result) (done: state -> result) : Type0 =
  forall(value: state) (at: position start finish). ((match f value at with | ControlFlow_Break (_, out) -> begin Prims.l_and (next value at == Option.Option_None) (stop value at == done out) end | ControlFlow_Continue out -> begin next value at == Option.Option_Some out end) <: Type0)

let break_step (#state: Type0) (start: usize) (finish: usize{v start < v finish}) (inv: total_invariant state start finish) (value: state) (f: break_callback state start finish) : Lemma (ensures fold_range_cf start finish inv value f == ((match f value start with | ControlFlow_Break (_, out) -> begin out end | ControlFlow_Continue out -> begin fold_range_cf (start +! mk_int 1) finish inv out f end) <: state)) =
  ()

let break_end (#state: Type0) (start: usize) (finish: usize{v start == v finish}) (inv: total_invariant state start finish) (value: state) (f: break_callback state start finish) : Lemma (ensures fold_range_cf start finish inv value f == value) =
  ()

let rec break_interpret (#state: Type0) (#result: Type0) (start: usize) (finish: usize{v start <= v finish}) (inv: total_invariant state start finish) (value: state) (f: break_callback state start finish) (next: transition state finish) (stop: state -> (i: usize{v i < v finish}) -> result) (done: state -> result) : Lemma (requires break_agrees start finish f next stop done) (ensures done (fold_range_cf start finish inv value f) == option_run finish start value next stop done) (decreases v finish - v start) =
  if v start < v finish then
    begin break_step start finish inv value f;
    option_run_step finish start value next stop done;
    match f value start with | ControlFlow_Break (_, out) -> begin assert (next value start == Option.Option_None);
    assert (stop value start == done out);
    assert (done (fold_range_cf start finish inv value f) == option_run finish start value next stop done) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_cf";
      Tactics.prune "Nickel.LoopUtil.option_run";
      Tactics.smt_sync' 1 1
    ) end | ControlFlow_Continue out -> begin assert (next value start == Option.Option_Some out);
    break_interpret (start +! mk_int 1) finish inv out f next stop done;
    assert (done (fold_range_cf start finish inv value f) == option_run finish start value next stop done) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_cf";
      Tactics.prune "Nickel.LoopUtil.option_run";
      Tactics.smt_sync' 1 1
    ) end end
  else
    begin break_end start finish inv value f;
    option_run_end finish start value next stop done;
    assert (done (fold_range_cf start finish inv value f) == option_run finish start value next stop done) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_cf";
      Tactics.prune "Nickel.LoopUtil.option_run";
      Tactics.smt_sync' 1 1
    ) end

let break_interpret_any (#state: Type0) (#result: Type0) (start: usize) (finish: usize{v start <= v finish}) (next: transition state finish) (stop: state -> (i: usize{v i < v finish}) -> result) (done: state -> result) : Lemma (ensures forall(inv: total_invariant state start finish) (value: state) (f: break_callback state start finish). break_agrees start finish f next stop done ==> done (fold_range_cf start finish inv value f) == option_run finish start value next stop done) =
  let each (inv: total_invariant state start finish) (value: state) (f: break_callback state start finish) : Lemma (requires break_agrees start finish f next stop done) (ensures done (fold_range_cf start finish inv value f) == option_run finish start value next stop done) =
    break_interpret start finish inv value f next stop done;
    assert (done (fold_range_cf start finish inv value f) == option_run finish start value next stop done) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_cf";
      Tactics.prune "Nickel.LoopUtil.option_run";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 each)

let preserve_any (#state: Type0) (#result: Type0) (start: usize) (finish: usize{v start <= v finish}) (p: nat -> state -> Type0) (post: state -> Type0) (returned: result -> Type0) : Lemma (ensures forall(inv: invariant state start finish) (value: state) (f: callback state result start finish). Prims.l_and (Prims.l_and (p (v start) value) (forall(s: state) (i: position start finish). p (v i) s ==> step_safe p post returned (v i) (f s i))) (forall(s: state). p (v finish) s ==> post s) ==> output_safe post returned (fold_range_return start finish inv value f)) =
  let each (inv: invariant state start finish) (value: state) (f: callback state result start finish) : Lemma (requires (p (v start) value /\ (forall(s: state) (i: position start finish). p (v i) s ==> step_safe p post returned (v i) (f s i)) /\ (forall(s: state). p (v finish) s ==> post s))) (ensures output_safe post returned (fold_range_return start finish inv value f)) =
    preserve start finish inv value f p post returned;
    assert (output_safe post returned (fold_range_return start finish inv value f)) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 each)

let return_step (#state: Type0) (#result: Type0) (p: nat -> state -> Type0) (returned: result -> Type0) (at: nat) (out: iter_output state result) : Type0 =
  match out with | ControlFlow_Continue next -> begin p (at + 1) next end | ControlFlow_Break (ControlFlow_Break ret) -> begin returned ret end | ControlFlow_Break (ControlFlow_Continue _) -> begin Prims.l_True end

let early_returns_only (#state: Type0) (#result: Type0) (returned: result -> Type0) (out: output state result) : Type0 =
  match out with | ControlFlow_Break ret -> begin returned ret end | ControlFlow_Continue _ -> begin Prims.l_True end

let early_return_preserve_any (#state: Type0) (#result: Type0) (start: usize) (finish: usize{v start <= v finish}) (p: nat -> state -> Type0) (returned: result -> Type0) : Lemma (ensures forall(inv: invariant state start finish) (value: state) (f: callback state result start finish). Prims.l_and (p (v start) value) (forall(s: state) (i: position start finish). p (v i) s ==> return_step p returned (v i) (f s i)) ==> early_returns_only returned (fold_range_return start finish inv value f)) =
  let each (inv: invariant state start finish) (value: state) (f: callback state result start finish) : Lemma (requires (p (v start) value /\ (forall(s: state) (i: position start finish). p (v i) s ==> return_step p returned (v i) (f s i)))) (ensures early_returns_only returned (fold_range_return start finish inv value f)) =
    preserve_any start finish p (fun (_: state) -> Prims.l_True) returned;
    assert (early_returns_only returned (fold_range_return start finish inv value f)) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 each)

type for_invariant (state: Type0) (finish: usize) = (at: nat{at <= v finish}) -> state -> Type0

let rec plain_preserve (#state: Type0) (start: usize) (finish: usize{v start <= v finish}) (inv: total_invariant state start finish) (value: state) (f: plain_callback state start finish) (p: for_invariant state finish) (post: state -> Type0) : Lemma (requires (p (v start) value /\ (forall(s: state) (i: position start finish{v i < v finish}). p (v i) s ==> p (v i + 1) (f s i)) /\ (forall(s: state). p (v finish) s ==> post s))) (ensures post (fold_range start finish inv value f)) (decreases v finish - v start) =
  if v start < v finish then
    begin plain_step start finish inv value f;
    plain_preserve (start +! mk_int 1) finish inv (f value start) f p post;
    assert (post (fold_range start finish inv value f)) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range";
      Tactics.smt_sync' 1 1
    ) end
  else
    begin plain_end start finish inv value f;
    assert (post (fold_range start finish inv value f)) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range";
      Tactics.smt_sync' 1 1
    ) end

let plain_preserve_any (#state: Type0) (start: usize) (finish: usize{v start <= v finish}) (p: for_invariant state finish) (post: state -> Type0) : Lemma (ensures forall(inv: total_invariant state start finish) (value: state) (f: plain_callback state start finish). Prims.l_and (Prims.l_and (p (v start) value) (forall(s: state) (i: position start finish{v i < v finish}). p (v i) s ==> p (v i + 1) (f s i))) (forall(s: state). p (v finish) s ==> post s) ==> post (fold_range start finish inv value f)) =
  let each (inv: total_invariant state start finish) (value: state) (f: plain_callback state start finish) : Lemma (requires (p (v start) value /\ (forall(s: state) (i: position start finish{v i < v finish}). p (v i) s ==> p (v i + 1) (f s i)) /\ (forall(s: state). p (v finish) s ==> post s))) (ensures post (fold_range start finish inv value f)) =
    plain_preserve start finish inv value f p post;
    assert (post (fold_range start finish inv value f)) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 each)

module Result = Core_models.Result

let result_safe (#value: Type0) (#error: Type0) (successful: value -> Type0) (failed: error -> Type0) (out: Result.t_Result value error) : Type0 =
  match out with | Result.Result_Ok value -> begin successful value end | Result.Result_Err error -> begin failed error end

let result_finish (#state: Type0) (#value: Type0) (#error: Type0) (done: state -> value) (out: output state (Result.t_Result value error)) : Result.t_Result value error =
  match out with | ControlFlow_Break ret -> begin ret end | ControlFlow_Continue next -> begin Result.Result_Ok (done next) end

let result_step (#state: Type0) (#value: Type0) (#error: Type0) (p: nat -> state -> Type0) (done: state -> value) (successful: value -> Type0) (failed: error -> Type0) (at: nat) (out: iter_output state (Result.t_Result value error)) : Type0 =
  match out with | ControlFlow_Continue next -> begin p (at + 1) next end | ControlFlow_Break (ControlFlow_Break ret) -> begin result_safe successful failed ret end | ControlFlow_Break (ControlFlow_Continue (_, next)) -> begin successful (done next) end

let result_preserve_any (#state: Type0) (#value: Type0) (#error: Type0) (start: usize) (finish: usize{v start <= v finish}) (p: nat -> state -> Type0) (done: state -> value) (successful: value -> Type0) (failed: error -> Type0) : Lemma (ensures forall(inv: invariant state start finish) (initial: state) (f: callback state (Result.t_Result value error) start finish). Prims.l_and (Prims.l_and (p (v start) initial) (forall(s: state) (i: position start finish). p (v i) s ==> result_step p done successful failed (v i) (f s i))) (forall(s: state). p (v finish) s ==> successful (done s)) ==> result_safe successful failed (result_finish done (fold_range_return start finish inv initial f))) =
  let each (inv: invariant state start finish) (initial: state) (f: callback state (Result.t_Result value error) start finish) : Lemma (requires (p (v start) initial /\ (forall(s: state) (i: position start finish). p (v i) s ==> result_step p done successful failed (v i) (f s i)) /\ (forall(s: state). p (v finish) s ==> successful (done s)))) (ensures result_safe successful failed (result_finish done (fold_range_return start finish inv initial f))) =
    preserve_any start finish p (fun (s: state) -> successful (done s)) (result_safe successful failed);
    assert (result_safe successful failed (result_finish done (fold_range_return start finish inv initial f))) by (
      Tactics.prune "Rust_primitives.Hax.Folds.fold_range_return";
      Tactics.smt_sync' 1 1
    ) in
  FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 each)