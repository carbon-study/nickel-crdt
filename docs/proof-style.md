# proof style guide

write a proof so a reader can follow the operation, its contract and the few
facts connecting them. the reader should not have to reconstruct the extracted
program or guess which definitions the solver happened to use.

this is the style for new and migrated nickel proofs. it also supplies the
readability checklist for the [whole-codebase reform](edit-admit-continuation.md#0-reform-contracts-patterns-and-for-loop-proofs-first).
legacy proofs are migration work, not examples that grant exceptions. a shorter
file or fewer tactic names does not by itself establish a better proof.

## start with the claim

- name the operation and observable property: `push_result_is_exact`,
  `receive_rejection_unchanged`, `scalar_validation_is_sound`. avoid names like
  `helper2`, `do_proof` or `fixed`.
- say what happens on every relevant result branch. distinguish a success-only
  property from an all-return property. include errors, empty work and duplicates
  when the claim is about transactional behavior.
- make semantic premises visible in `takes` clauses or clearly named parameters.
  ordinary index bounds can stay in parameter refinements. do not hide a major
  premise such as equal shared state in a long parameter type on a public surface.
- use a named predicate when it explains a concept or removes a substantial
  repeated expression. its definition must be nearby or easy to find. a name
  that merely abbreviates the entire goal once usually adds another lookup.
- state the exact domain. fact storage order is not text order; four preserved
  invariant components are not complete semantic well-formedness. do not call a
  structural rebuild theorem semantic refinement.

when refactoring an existing theorem, keep its logical strength and premises.
compare the old and new statements, including parameter refinements and pattern
metadata. if the old statement is wrong or needs a different domain, report the
change as a separate claim decision; do not disguise it as style cleanup.

## prove contracts at the actual boundary

prove laws about the actual extracted function call. an independently rewritten
algorithm is not its contract until the implementation connection is checked.
use exact-result laws where callers need constructors, unchanged fields or full
contents; an underspecified predicate can leave callers depending on hidden
implementation facts.

one function may need several small laws. choose them from actual caller needs,
then keep the relevant bodies unavailable in those caller queries. do not split
a contract into dozens of forwarding lemmas just to make each proof one line.
a new helper earns its place by removing repeated reasoning, naming a useful
semantic step or establishing a real boundary.

keep implementation knowledge in its owning boundary proof. a caller may inspect
its own control flow, but should compose contracts for its callees. document
exactly which functions are withheld; “the implementation is hidden” is too broad
if other native or model bodies remain available.

### an existing caller

this excerpt is `append_fresh_preserves_unique` at merged `d7e999f` in
[`EditAccepted.lt`](https://github.com/carbon-study/nickel-crdt/blob/d7e999fe04a2f1f8e99b9ec22f71ba6b6d44fddf/proofs/EditAccepted.lt). the existing definitions and
imports in that file are required; this is not a standalone example.

```text
proof append_fresh_preserves_unique(facts: facts_vec, fact: Native.t_Fact): unit
  takes ids_unique(facts)
  takes Native.has_fact(Alloc.Vec.impl_1__as_slice(facts), fact.f_id) == false
  gives push_result_unique(Native.push(facts, fact))
{
  membership_absent(Alloc.Vec.impl_1__as_slice(facts), fact.f_id);
  assert(push_result_unique(Native.push(facts, fact))) by {
    Tactics.prune("Nickel_crdt.Edit.push");
    Tactics.smt_sync'(1, 1)
  }
}
```

the body supplies a membership fact and uses the exact push contract with the
native helper withheld. that contract's pattern makes it available at the call.
this excerpt demonstrates a native-function boundary only: imported vector/slice
models remain visible here. extending their boundary is separate work.

## keep the reasoning in order

prefer a few direct lemma calls, a meaningful case split or a recursive induction
step. put intermediate assertions where they expose a missing mathematical step,
not after every expression as solver encouragement. use descriptive local names
such as `before`, `next`, `fact` and `index`.

keep one-off reasoning local. extract a repeated result match or quantifier
argument when it gives callers a simpler interface. preserve captures and joint
premises when factoring it. do not scatter essentially identical `each`,
`each_imp` and `move_requires` scaffolds across every caller. existing repetitions
are still reform work; another wrapper around each repetition is not a solution.

comments should explain a non-obvious premise, boundary or choice of invariant.
remove comments that merely repeat the next lemma's name. comments are not proof
steps and must not claim more opacity or correctness than the checked query has.

## use loop rules at the caller's level

for a basic bounded loop, expose the initial state, invariant, preservation step
and completion condition. use the derived plain-loop interface over the actual
pinned interpreter. callers should not manipulate the fold model or rebuild
`ControlFlow`, `step_safe` and `output_safe` obligations.

for fallible loops, state what continuing preserves and what early `Ok` or `Err`
returns establish. use the result-level rule where it fits. use a separate rule
for a genuinely different exit shape; do not add impossible-case hypotheses just
to force a loop into a convenient adapter. keep bounds and empty ranges in scope.

[`Smoke.flip_exact`](../proofs/Smoke.lt) and the two scalar-boundary proofs in
[`EditWellFormed.lt`](../proofs/EditWellFormed.lt) show the current caller
interfaces. they are starting points, not instructions to copy their internal
adapter scaffolding. recursive proofs need an explicit decreasing measure.

## keep automation deliberate and local

- use a deliberate `hint` on a term the caller actually produces. every required
  quantified variable must be covered by the pattern; avoid self-generating
  trigger loops. prefer an explicit contract call if it reads more clearly.
- put visibility changes beside the goal they affect. `prune` withholds named
  definitions from that goal's smt query; it does not discharge the goal. broad
  namespace pruning needs an explained scope, especially in dependency controls.
- the current reformed queries use `Tactics.smt_sync'(1, 1)` for shallow automatic
  unfolding. the numbers are fuel settings, not a bound on theorem inputs. do not
  scatter solver tuning through callers in place of finding the missing law.
- explicit authored normalization, including `norm_spec`, `norm`, `delta_only`,
  `iota` and `zeta` scripts or aliases hiding them, is prohibited in reformed
  code. no source-boundary exception is approved. do not move a reduction list
  into a helper and call that an abstraction.
- `prune`/smt assertion blocks still carry boilerplate. keep it small and explicit;
  do not advertise current syntax as a final ergonomic interface. improving it
  must preserve the checked visibility boundary and the pinned toolchain policy.

if a proof becomes unpredictable, first identify the missing premise, contract
or induction step. retain unsuccessful attempts in local evidence notes. do not
respond by enlarging compiler/query limits, changing trusted models, adding an
admission or silently narrowing the theorem.

## show that the abstraction does work

check two different boundaries:

1. **implementation sensitivity:** a real wrong Rust body or wrong actual call
   argument must fail native checks and the intended source-linked law after
   fresh extraction, where that kind of control applies.
2. **contract dependence:** with the helper bodies withheld, remove the needed
   pattern or contract use and require an ordinary failure at the caller.

pattern deletion may stop at the first caller. use separate caller-scoped
withholding checks when claiming that several callers use the boundary. a
pattern that changes nothing is not evidence of modularity. model-law dependency
controls are proof checks, not native bug witnesses.

require an ordinary named failure whose semantic error belongs to that theorem's
source declaration. timeout, solver exhaustion, parser/type errors and failures
in an earlier unrelated lemma do not count. a positive pass alone is insufficient:
removing several individually redundant steps can change control attribution.

## finish a migration, not just a proof edit

- compare old statements, source bindings and any moved theorem-owner mapping.
- regenerate the affected authored views, compare them freshly, update receipts
  and provenance, and include new files in the actual verification gate.
- extend the source fence to the migrated scope and test an actual forbidden
  injection. the fence catches prohibited forms; it does not judge readability.
- run the relevant positive and dependency/semantic controls. proof-only changes
  may reuse hash-recorded fresh native extractions with normal proof-cache
  invalidation. run native/extraction checks when their boundary changes.
- keep local checks focused. the complete matrix belongs in ci; docs-only edits
  do not justify rerunning proof builds or browsers. preserve each running head
  until its acceptance finishes, then require exact-head arm acceptance for a
  proof change and a scoped collected review before merge.

review a representative caller by reading its statement and body together:
can you identify the claim, premises, contracts and induction without opening
the callee implementations? does each new abstraction remove work for that
reader and for the next author? if not, the readability gate is still open.

## the public theorem surface

`Spec.lt` is proposed, not implemented. its job is to present checked public
predicates, explicit premises and short compositions of implementation-linked
laws. it must not be a parallel set of copied claims or a new unproved model.
name partial invariant bundles precisely and surface the hypotheses of
cross-replica laws. keep the missing semantic/refinement/progress results visible.
