# proof scope

Author new and migrated proofs using the [proof style guide](../docs/proof-style.md).
It includes the readability and boundary-review checklist; the existing legacy
proofs are not exceptions to that standard.

`Smoke.lt` retains the extracted Rust `flip`/reference-interpreter bridge and also proves parity directly through the plain-loop invariant rule, then derives involution from that parity contract. `LoopUtil.lt` supplies reusable range-loop interpretation and induction lemmas. Its invariant parameter follows the pinned hax representation: it is an annotation, not an independently enforced loop invariant.

The check freshly extracts Rust in isolated positive and mutation workspaces. Both use the same authored theorem statements. Replacing the loop's toggle with identity must fail `Nickel.Smoke.flip_bridge` as a proof obligation; a timeout or extraction error is not an accepted control result. The native test must also detect the mutation.

The locked public flake checks committed F* views directly. It checks source/view receipts for accidental drift, but a hash receipt does not prove compiler correctness or that a view was emitted from its source. Latte is currently a private, unlicensed regeneration dependency; its compiler is not bundled or fetched by this public flake. See the exact local regeneration provenance in ../PROVENANCE.md. Until that dependency can be published, anonymous users can reproduce F* verification and Rust extraction, not Latte emission.

Trusted dependencies include Rust compilation, hax translation, Latte emission, F*, its solver and external Rust models. The external models are checked once in an immutable Nix output; each proof workspace uses that exact cache. No own admissions, hint replay or stale hash bypass is used. Project modules retain a 60-second per-compiler limit. Cold imported-model
bootstrap allows 180 seconds per compiler under a 600-second make-driver guard;
dependency discovery has its own 60-second guard. These are distinct command
budgets, not a claim about termination of every detached descendant. Solver
settings and proof obligations are unchanged. Successful model outputs retain
`bootstrap.log` and `bootstrap.stats.json`, including per-module F* wall times.
`check-proof-timeouts.mjs` exercises the actual make/timeout wiring using an
explicitly simulated compiler; those fixtures never enter the real model cache.

The project make driver has a separate graph-derived bound:
`N * (moduleSeconds + 2) + 10` seconds, where `N` is the number of distinct
project compiler targets reachable from the requested roots in F*'s actual
dependency graph. Interfaces and implementations count separately. Unrelated
workspace files, extraction targets and immutable imported models do not count;
checked project targets still count on warm runs. The serial sum is not divided
by make's job count. The two seconds per target cover compiler timeout kill
grace; ten seconds cover make overhead. For the current nine-module edit chain
this is 568 seconds, while every F* process remains capped at 60 seconds and
every solver query at rlimit100. Dependency discovery remains independently
capped at 60 seconds; model bootstrap keeps its explicit 600-second driver.
Project callers cannot enlarge the derived bound through an explicit override.
The selected target list, policy and bounds are printed and retained in
`last-check.stats.json`. The simulated-compiler gate tests a serial chain,
separate compiler/aggregate timeouts, SIGTERM-resistant compiler kill grace,
and normal rejection; none is a proof-success substitute.

The smoke fixture establishes no CRDT convergence, ordering, undo, codec, Wasm or browser property.

The [prospective API/verification contract](../docs/api-verification.md) lists the proposed V1–V9 obligations. None is currently discharged. The [undo analysis](../docs/undo-semantics.md) records the semantic/algorithmic stop gate; the loop proof does not bypass it.

## running the edit gate

With no arguments, `scripts/check-edit-proofs.mjs` (and therefore `.#proofs` and
CI) runs everything: the positive chain, every contract-dependency family and
every actual-Rust mutation mode. For development, pass any of:

- `positive-only`: the positive chain alone;
- `contracts:<family>` (`counter`, `push`, `vector`, `scalar`, `identity`,
  `writer`, `plan`, `containment`, `accepted`, `spec`, `private`, `shared`, `commit`, `remaining`): the positive chain, then that family's dependency controls;
- `positive`: the positive chain and all families (the previous meaning);
- `cache-safety`: the positive chain, then the cache-reuse self-test;
- mutation mode names, which run after the positive chain when it is selected.

Each family edits its own copy of the verified positive workspace, so probes
neither leave the positive cache in a failed state nor see each other's edits.
A fresh mutation workspace starts as a copy of the verified positive workspace;
fresh hax output then replaces `Nickel_crdt.Edit.fst`, and the digest check plus
F*'s own dependency check force that module and every dependent proof to
recheck. Only modules independent of the extraction (Prelude, LoopUtil, Vector)
are reused. Acceptance still requires the complete no-argument gate.

Reuse is checked, not assumed:

- Every selected mutation must have an owning theorem, an anchored edit and a
  resolvable scope before any native test, extraction or compiler starts.
- Each hax run writes into a staging directory and is installed as an inventory:
  project sources that are neither authored views nor part of the fresh extraction
  are removed before verification.
- Every mutation run must compile both `Nickel_crdt.Edit.fst` and its owning proof
  module in that run, so a cache cannot stand in for checking the changed program.
- The `cache-safety` self-test (part of the no-argument gate) copies the verified
  positive workspace and requires the following:
  - an unchanged copy compiles nothing;
  - a changed extraction recompiles it and its dependents, but reuses Prelude and LoopUtil;
  - a changed LoopUtil recompiles it and EditIdentity, but reuses the extraction,
    EditAtomic and EditCommit;
  - a changed recorded option recompiles everything.

## actual edit/admit return paths

`EditAtomic.lt` proves complete-instance neutrality on admission errors/duplicates
and local errors/empty results, plus the successful local counter step, against
freshly extracted `src/edit.rs`. Three wrong native bodies must fail their
unchanged lemmas and native tests. `scripts/check-edit-proofs.mjs` runs inside
the existing `.#proofs` gate, using the same immutable models and limits. These
are universal return-path results, not local/admission semantic refinement,
FugueMax representation, freshness or convergence. See the
[candidate contract](../docs/rust-edit-admit.md) for the precise domain and
remaining joint exit. No full V1–V9 obligation is thereby closed.

## positive author/admit coherence

`EditCommit.lt` binds an authored fact to its request, proves replay into the
author's before-state matches its complete facts/tree commit, and proves remote
admission preserves and is independent of private writer/allocator state. Their
composition covers an actual second receiver with the same shared before-state
and limits but different private state. Five additional wrong Rust bodies test
returned-fact binding, stale-tree publication, receiver allocator preservation,
request-gap binding and private-state independence. All run in the existing
proof gate; optional explicit mode names support focused local checks, while
the default keeps all controls. This is joint commit coherence, not successful
refinement to the independent reference, WF preservation, ordering or convergence.

## identity classification

`EditIdentity.lt` proves the actual range scan equals a recursive first-ID
lookup, and carries it through public `receive` and successful local `edit`:
known IDs classify by exact fact equality; invalid counters reject; Added and
Authored event IDs are absent from the before-facts. Known-member classification
requires unique before-IDs; freshness does not. This is not full WF preservation,
whole refinement, global writer fencing or ordering.

The pinned backend structurally lowers `PartialEq` operator calls. An ordinary
`fact_equal` call plus its exactness lemma preserves source sensitivity at the
identity guard; separate lemmas check handwritten ID equality. Eight native and
F* mutation controls cover these laws. The candidate contract records the
reproduced erased-comparison blind spot and the remaining trust boundary.

## accepted event IDs

`EditAccepted.lt` proves the actual native membership/selection/append/
canonicalization chain, then constructor establishment and all-return-path
preservation of accepted event-ID uniqueness by public receive/edit. Successful
admission gets unique IDs from the real canonicalizer; errors, duplicates and
empty local work use the already checked whole-instance neutrality laws. This
discharges the unique-ID premise of indexed known-member classification for
publicly constructed/preserved states. It is one WF component, not causal/scalar/
ordering refinement or a verified engine. The LoopUtil preservation adapter
requires explicitly proved semantic premises rather than hax annotations.
Three additional wrong Rust bodies must reject their unchanged named lemmas,
including a duplicate injected into the actual joint publication.

## exact successful fact publication

`EditAccepted.lt` also proves that successful `receive` adds exactly the offered
whole fact while retaining every old whole fact, and that successful `edit`
does the same for its returned authored fact. It proves this through the actual
push, selection step, canonical loop and final publication, not a replacement
sorting algorithm. The native test helpers check the same public fact contents.

The canonical proof establishes whole-input selection and equal length, then
uses accepted-ID uniqueness and F*'s checked finite pigeonhole lemma to establish
coverage of every input fact. This is exact fact-content preservation; it is
not a sorting-order theorem, causal WF, interpretation/FugueMax refinement,
fitting-input progress or convergence. The existing all-return neutrality laws
still cover errors, duplicates and empty edits. Two further wrong Rust bodies
must fail native tests and their unchanged named content lemmas: altering a
selected fact's gap and omitting the canonical iterations.

## native push contract

`EditAccepted.push_result_is_exact` gives an exact generic contract for the
translated Rust `push<T>`: an unchanged vector and `Internal` at the modeled
length ceiling, or the original sequence followed by exactly the offered item
and `Ok`. Four append/content/membership proofs withhold the native helper and
use this contract. Removing its pattern, or withholding its contract in each
caller, must reject ordinarily. Two actual Rust controls discard the value or
prepend it and must fail native tests and the exact contract.

Other imported vector/slice model definitions remain available; the next section
describes the selected model-function contracts. The native helper contract
isolates one source function in four queries; it does not finish model opacity
or the Accepted family. The contract concerns the hax translation under those trusted models,
not physical allocation failure or a proved Rust-to-F* semantic equivalence.

## vector/slice model contracts

`Vector.lt` proves five equations over the pinned hax models: a constructed
global-allocator vector and `from_seq` expose their original sequence; vector
and slice lengths agree with sequence length; slice indexing agrees with
sequence indexing.
The equations are generic in the element type, have deliberate SMT patterns,
and use no explicit normalization or new assumptions.

The same four push callers withhold `Alloc.Vec.impl_1__as_slice`,
`Alloc.Vec.from_seq`, `Alloc.Vec.impl_1__len`, `Core_models.Slice.impl__len` and
`Rust_primitives.Slice.slice_index`, as well as native `push`. This uniform block
is a deliberate visibility boundary, not a claim that each equation is needed
in every caller.
Five global pattern removals must reject at their named dependent proof. The
slice-length removal now reaches the earlier isolated Identity duplicate boundary;
the others still reach the first Accepted push caller. Each equation is also
withheld only within that Accepted caller's query, requiring its own rejection
without disrupting upstream proofs. Separately withholding all Vector contracts,
or just the `vector_from_seq` equation, in each of the four callers must reject
at that caller. These are proof-dependency controls, not native bugs.
Existing actual-Rust controls remain separate.

This gives those four queries an explicit model-function boundary. Other model
definitions and sequence reasoning remain available, and the rest of Accepted
still needs reform. The upstream model trust boundary is unchanged.

## counter-control isolation

The counter guard and successor calculation are a pure native helper; no
instance counter is changed until the existing successful commit. Its lemma
checks the returned successor and the exact over-limit error. The public
`authored_edit_advances_once` statement is unchanged and remains part of the
full positive proof chain.

The reused-counter mutation changes that actual helper's successful result from
`counter + 1` to `counter`. It must still fail native public tests and now reject
`counter_result_advances_once` ordinarily. These counter negative checks stop at their
owning `EditAtomic` module; positive verification checks the `Spec` and `EditCausal` roots.
The separate `edit-commit-ignores-counter` control changes the actual counter
installation inside `with_counter` to retain the old value. It must fail native
public tests and `counter_installation_is_exact`, which checks both the installed
counter and preservation of every other instance field. Public `edit` uses
that function after successful planning, and its unchanged counter theorem
now composes the calculation and setter contracts at the actual call. This controls the installation body, not its argument
wiring inside `edit`.

The separate `edit-call-passes-old-counter` control mutates that actual call to
`next.with_counter(self.next_counter)`. It must fail native tests and the
unchanged public `authored_edit_advances_once` theorem ordinarily. Calculation,
setter-body and call-site controls therefore exercise distinct source boundaries.
Earlier resource-only wiring attempts are retained as failed experiments, not
counted as proof detections.

The request binding, same-commit and private-state proofs still explicitly
normalize their actual native call boundaries, then run the standard F*
synchronous SMT tactic with fuel/ifuel 1/1. Those families await the reform below.
The counter proof now composes the checked calculation and setter contracts,
with the same shallow final SMT request and no explicit normalization. The
legacy private-state proofs expose the existing native clone and tree setter. This limits automatic unfolding into replay while preserving the exact
universal theorem statements. Default module settings, rlimit100 and all wall
time limits are unchanged; these query-local unfolding depths are lower, not
larger proof budgets. Positive and mutated programs use identical proof views
and settings.

The wrong-returned-gap control now names the existing public
`authored_fact_binds_request` theorem, placed before same-commit coherence.
The same-commit theorem remains required in the full positive chain and is
exercised separately by `local-stale-tree` (committed tree mismatch) and
`local-return-after` (returned fact mismatch). The latter empties only the
returned fact’s `after` list, leaving the committed fact intact; request binding
does not constrain that field. It must fail `authored_fact_replays_same_commit`. The negative classifier
still requires clean extraction, native failure, ordinary proof failure and a
named non-resource query below its rlimit; no failure class was broadened.
Neither timeouts nor solely resource-exhausted failures count as detection.

The pinned hax translations are also committed under
[`proofs/generated/hax`](generated/hax/README.md). Its README gives the exact extraction scope and refresh commands.
The existing fresh-extraction proof gate requires byte-identical positive output;
mutant extractions still use their unchanged semantic proof obligations.
This makes translation changes reviewable, without proving Rust/F* semantic
equivalence or removing hax from the trusted boundary.

## canonical fact-order component

`EditAccepted` now relates the actual `event_lt` to a mathematical event key:
Alice counters precede Bo counters, and counters order each writer's events.
This is accepted-fact storage order, not causal scheduling or Fugue text order.
The actual selection scan chooses a least unseen key; the checked append/loop
argument proves nondecreasing keys in every successful canonical result. Actual
`receive`/`edit` publish that result, and constructor establishment plus neutrality
on other returns give all-return preservation from an ordered before-state.
Accepted-ID uniqueness remains a separate established component.

The native public-state checks require strict event-ID order. The two focused
controls reverse only the selection comparison, or compute canonicalization but
discard its result at publication. They target the least-selection theorem and
the actual canonical-publication theorem respectively. That existing publication
theorem retains its exact statement and now uses explicit normalization followed
by synchronous SMT with fuel/ifuel1/1, preserving rlimit100 and wall budgets.
As elsewhere, extraction
errors, timeouts and resource-only proof failures are not accepted detection.
The order component alone does not prove successful canonicalization or unique
canonical output. The separate agreement/success components below address those
storage obligations, not causal replay equivalence, text order, full
representation validity or whole-engine convergence.

`event_key_identifies_event` proves injectivity of the arithmetic key, including
its writer component. `ordered_unique_is_strict` therefore turns the separately
checked uniqueness and nondecreasing-order components into strict native
`event_lt` order; `canonical_facts_are_strictly_ordered` applies it to the actual
successful canonical result. The default `order-key-ignores-writer` control
changes the real comparator body to counter-only comparison and must fail the
independent key-order bridge. This supplies the strict-order premise for the
separate vector-agreement argument below.

## conditional canonical and public shared-state agreement

`ordered_contents_determine_vector` proves exact vector equality, using a finite
prefix argument, unique IDs and strict key order. `canonical_is_permutation_independent`
applies it to actual canonicalization when both calls succeed. Its input premise
is equal whole-fact support and equal length, not an asserted multiset-count
characterization for arbitrary malformed inputs.

`plan_publishes_interpretation` binds actual successful publication to the result
of the existing native `interpret`. `receive_added_shared_state_agrees` then
compares two actual public receives: if their candidate fact inputs meet that
premise and both return Added, committed facts and trees are equal. It does not
compare error dispositions or establish successful admission. This is structural
rebuild agreement, not independent semantic refinement of the interpreter.

Two default controls independently keep the old tree in the setter, or pass the
old tree to the correct setter in the actual plan. Both must fail native tests
and `plan_publishes_interpretation`; a helper-only control is insufficient. The
finite native witness uses all three causal schedules of a two-event Alice run
and concurrent Bo event, checks a nonempty result, and compares public facts,
whole birth IDs and observations. Existing trust and failure-classification
boundaries are unchanged.

## non-vacuous canonical storage success

`canonical_succeeds_for_unique_ids` proves that actual native canonicalization
returns `Ok` for every unique-event-ID input slice. The proof connects totality
of the actual choice scan, finite cardinality of input/output IDs, successful
append below the vector-length guard, exact step length and the actual
LoopUtil-linked outer loop. It does not assume the result is successful.

`unique_inputs_canonicalize_identically` combines this with exact-content and
strict-order agreement: equal whole-fact support/length and unique input IDs
imply two successful equal canonical vectors. Neither theorem states that the
validator or interpreter succeeds. Full valid-fitting public admission progress
and independent causal/Fugue refinement remain open.

The default `canonical-step-refuses` and `canonical-refuses` modes change only
the respective native successful return into `Err(Internal)`. They require a
native failure and an ordinary rejection at `canonical_step_succeeds` and
`canonical_succeeds_for_unique_ids`, respectively. Extraction failures,
timeouts and solely resource-exhausted queries do not count. Query-local shallow
SMT for the final step/loop assertions preserves the existing rlimit and wall
budgets; no driver-policy change is made here.

## accepted Unicode scalar domain

The independent `unicode_scalar` predicate excludes surrogate code points and
words above `0x10ffff`. `scalar_validation_is_sound` follows the actual indexed
native helper; `valid_scalar_input_succeeds` separately proves that valid input
passes that helper. `successful_validation_has_valid_scalars` checks its actual
call in `validate_new`, including the error-only early returns of the two prior
range loops. `receive_added_fact_has_valid_scalars` and
`edit_authors_only_valid_scalars` connect the result to successful public calls.
Constructor establishment plus exact-content publication and neutral returns
prove all-return preservation of `facts_scalars_valid` for both public calls.

The scalar loop is factored into a helper and the two preceding iterator loops
become indexed loops because the pinned generic `fold_return` supplies no
semantic body/postcondition for the needed early-return law. The existing
LoopUtil range theorem proves it without a project axiom. The updated committed
native hax snapshot must match fresh extraction as usual.

Default `scalar-accepts-invalid`, `scalar-call-passes-empty` and
`scalar-refuses-valid` controls target helper soundness, actual call-site
validation soundness, and helper completeness, respectively. Native failures,
fresh extraction and ordinary named proof rejections are all required. No
resource-only failure counts. `scalar-count-loop-bypasses-check` additionally
returns success early from the preceding counting loop; it must fail actual
validator soundness, witnessing the range-loop control-flow obligation.
This component does not establish node/scalar
correspondence, complete tree validity, independent replay refinement or public
valid-fitting-input success.

## attributing negative proof evidence

Both native proof gates require exit2, a final failed query for the named theorem
below its resource limit without a timeout/resource reason, and an actual
semantic error whose source range overlaps that query inside the theorem's
unchanged generated declaration. A warning, a type/extraction failure, another
declaration's error, or a preliminary failure followed by a successful retry
cannot supply the evidence. The classifier accepts ordinary proof-condition
errors and failed synchronous SMT tactics; it does not treat arbitrary tactic
exceptions as semantic rejection. The small classifier regression gate runs
inside the existing edit-proof command, without invoking another proof run.

The default `plan-interprets-uncanonical` control derives the tree before
canonicalizing the fact vector. It must fail native tests and the same actual
interpretation-publication law as the old-tree controls. This witnesses the
publication's input ordering, not independent causal/Fugue refinement.

## direct causal-reference closure

`EditWellFormed` connects the direct predecessor guard to actual `past`,
validation and public admission. `Added` implies that the offered direct
predecessor IDs existed in the before facts. Exact whole-fact publication and
membership monotonicity then give constructor establishment and all-return
closure preservation for public receive/edit. The local proof composes the
existing same-commit theorem. Guard completeness is proved separately.

The guard is factored into an executable indexed range, retaining its checks
and errors; its hax snapshot is refreshed. Four default controls cover both
helper semantics and the actual argument wiring at `past` and validation.
This WF component does not establish acyclicity, exact transitive-past
computation, scheduler progress/independence, Fugue refinement or full WF.

## compiler boundary for WF components

The accepted-fact/storage proofs remain in `EditAccepted`. Scalar-domain and
direct causal-reference contracts live in `EditWellFormed`, which imports
those checked publication laws. The positive gate now verifies the full chain
through `Spec` and `EditCausal`; non-counter mutation controls retain the `EditWellFormed` root
and their owning theorems (relocated where appropriate). The three counter
controls still stop at `EditAtomic`.

This separates cumulative compiler work into semantic modules; it does not
increase the 60-second compiler cap or solver rlimit100. The split produced eight compiler targets. With the Vector model contracts,
the earlier edit chain had nine targets (568s). The current Spec/Causal
positive union has eleven targets (692s), using that same formula.
Every moved definition, universal statement and proof body is unchanged modulo
the owned module namespace. Rust and the hax snapshots are unchanged by the
split. Fresh extraction, byte-matching, native-failure requirements and the
source-bound ordinary-rejection classifier remain in force.

## proof reform: first migrated family

`EditAtomic` proves the five pre-existing universal laws without explicit
normalization, including the source-linking calculator/setter and public
neutral-return boundaries. Their parameters and conclusions are unchanged.
The public counter proof now calls a complete calculator-value contract; its
setter law has a deliberate pattern on `with_counter(state, counter)`.

At that edit boundary, two explicit `Tactics.prune` calls withhold the callee
facts for `next_counter_after` and `with_counter`. The proof can still inspect
edit's own wiring, including plan/frontier bodies. This is isolation of the
two counter helpers, not an all-callee abstraction. The calculator/setter implementation bodies remain available
only when establishing their contracts, not when composing them in this
counter proof. Pruning also withholds implicit SMT typing facts, so the value
contract specifies the full Ok/Error result, not just an arithmetic predicate
inside a match. The original weaker calculator law remains unchanged.

The default positive gate additionally checks two proof-dependency controls:
removing the setter pattern or the complete calculator-contract call must give
an ordinary source-bound failure of the unchanged public counter theorem.
These change proof machinery only; they are separate from the three actual-Rust
counter controls for arithmetic, setter implementation and the real argument.
Both public neutral-return Rust controls remain too. No timeout/exhaustion counts
as rejection. No Rust/hax/model change, axiom, compiler/query cap or graph-budget
change accompanies this refactor.

The token fence prohibits normalization operators/imports and tactic references
except the canonical direct shallow SMT call and these two named visibility
operations. Aliasing approved methods is refused too. Default fixture controls
and real-entry probes exercise normalization, import and alias bypasses. This
is a source-style fence, not an isolation boundary against arbitrary imported
code. Other proof families and loop-interface work remain; the whole reform is
not complete.


## ordinary for-loop invariant rule

For the supported plain range (`start <= finish`, total body/annotation),
supply the invariant before the first iteration, show
that the body preserves it at each executed index, and use it at the end.
`plain_preserve` proves this rule for the actual pinned hax `fold_range`.
`plain_preserve_any` exposes the same rule as an ordinary universal contract
over the anonymous callback emitted by hax. A caller need not copy that callback
or encode it as an Option/ControlFlow interpreter. Its semantic invariant has a
bounded index (zero through the final index); preservation is required only
for indices where the body executes. Hax's own annotation remains separate
and is not treated as a proof of preservation.

The actual parity caller in Smoke is:

```text
plain_preserve_any(0, n,
  (at, s) => parity(s, n - at) == parity(value, n),
  (s) => s == parity(value, n))
```

Here the invariant says that the remaining toggles finish at the desired
answer. The elementary one-toggle preservation condition checks automatically;
the rule handles loop induction. No auxiliary parity-step wrapper is needed. The source uses the native usize constructors/projections at that
boundary. This is applied to the actual extracted Rust loop, not a second
implementation accepted in its place.

All existing LoopUtil/Smoke logical statements remain intact, including the
legacy reference-interpreter bridge and its wrong-native-body control. Their
proof bodies now use ordinary induction, contracts and automatic checking
without explicit normalization. The shared entry fence covers Atomic,
LoopUtil and Smoke in both proof gates; it catches known normalization forms,
not arbitrary aliases. Existing fallible/break adapters remain available with
their exact statements, but a simpler fallible invariant interface and migration
of the remaining application proof families are still separate reform work.


### contract isolation on the plain path

The step/end equations are the source boundaries for the pinned model. Plain
interpretation and induction then compose those contracts with the fold facts
withheld; interpretation also withholds its reference interpreter's facts.
Both actual Rust smoke boundaries withhold the fold facts too. Their own Rust
function remains available for checking its wiring. The downstream involution
proof withholds that Rust function and uses its parity contract instead. The caller's invariant and
final condition are unchanged; the final assertions make the callee-opacity
check explicit. The same shallow SMT query and existing limits remain in use.

The two plain universal adapters use ordinary quantified contracts introduced
through standard-library lemmas. Their old explicit recursive-function pattern
was encoded with a fuel-instrumented symbol, while the actual Rust call used
the ordinary symbol. It therefore depended on facts that opacity removes.
Removing that pattern and using explicit universal introduction preserves the
logical statement and lets the contract work without the model body.

Thirteen default proof-dependency controls remove step/end/induction, adapter or
actual-source contract calls. Each must ordinarily fail its unchanged named
lemma. These are proof-machinery controls, not native bugs. The original wrong
Rust loop still fails the old bridge; an additional check omits that bridge and
requires the direct parity theorem to reject the same actual extraction too.
The direct positive also passes with the old bridge absent. Neither changes
the original semantic control or its target.

Controls reuse the checked workspace and normal source-hash invalidation; they
restore changed generated views in finally blocks. Changed views must actually
produce source-bound failed queries, so cached successes cannot count as
detection. Evidence for each result is saved separately.

This isolates the plain path. The other fallible/break adapters and remaining
application proof families still need the corresponding isolation work; zero
explicit normalization alone does not establish their abstraction boundary.

### fallible range loops: the scalar validator

`preserve_any` covers hax's return-capable range loop. The caller gives an
index/state invariant, a condition for normal completion and a condition for
an early returned result. The rule's step premise checks all three cases:
continue at the next index, break with a final state, or return a result.
Neither the hax annotation nor an early exit supplies preservation by itself.

The inductive rule now composes `unroll`/`empty` and its recursive contract with
`fold_range_return` facts withheld. Its universal adapter uses explicit standard
quantifier introduction and ordinary trigger inference, as on the plain path.
The original logical statement is unchanged; pattern metadata changes.

The first native callers use a Result-oriented specialization,
`result_preserve_any`. They supply the index/state invariant, a value produced
on normal completion, and separate conditions for successful results and errors.
Continue preserves the next invariant; break satisfies the completion condition;
early return satisfies the appropriate Ok/Err condition. The specialization
proves that rule from the old general preservation contract; it does not copy
the native callback or add a second loop implementation.

The three-way step obligation is defined once as `result_step` and reused by
the public contract and its introduction adapters. It separates continuing
with the next invariant, returning an Ok/Err result, and breaking with a final
state. This is transparent specification factoring, not another loop algorithm.
The specialization's contract does not mention `step_safe` or `output_safe`.
The actual scalar soundness and valid-input-success proofs withhold both of
those definitions, as well as the model fold, in their final assertions. They
check their own Rust validator wiring; its body and the scalar-domain predicates
remain visible at that source boundary. Normal completion of the unit-state
scalar scan produces `Ok(())`; soundness allows any error, while valid-input
success rules out errors. The old public theorem statements remain unchanged.

The general ControlFlow encoding still belongs to LoopUtil's compatibility
rule. Its Result specialization exposes the case obligations directly and
quantifies over the actual anonymous callback; the application proof never
names or copies that callback. This does not migrate all of EditWellFormed or
establish all-callee opacity. Only the two migrated scalar declarations have
the new entry fence.

Four default dependency controls remove return-loop step/end, induction and
adapter calls. Another removes the general rule from its Result specialization.
Two edit-gate controls remove the Result rule from the actual scalar proofs.
All must fail ordinarily in their unchanged named declarations. Existing native
invalid-scalar, false-refusal, wrong-argument and early-success controls retain
their original targets. The separate `fold_range_cf` break interpreter and
other application families still await migration. Repeated visibility and
quantifier-introduction scaffolds remain a readability issue in the library;
this specialization does not close the whole reform gate.

## identity equality contract and lookup cleanup

`EditIdentity.fact_equality_exact` checks the actual named native `fact_equal`
call against structural whole-fact equality and supplies a pattern for that call.
`duplicate_matches_lookup` withholds that helper and composes its contract with
lookup reasoning. It no longer needs a local quantified equality scaffold.
Removing the pattern or withholding the contract must reject ordinarily at the
actual duplicate boundary. The eight identity Rust controls separately test the
handwritten equalities, scan key, conflict classification, scan coverage and
counter guard through fresh extraction.

The three handwritten writer/event/birth equality boundary proofs also need no
explicit normalization. Their source controls remain important: the pinned hax
backend structurally lowers ordinary equality operators, so those boundary laws
must continue to check the named handwritten implementations separately.

Five explicit `first_id` reductions are removed from the recursive lookup proofs
and their two Accepted consumers; their recursive arguments and universal claims
are unchanged. This does not hide the lookup spec or vector/slice models.
The duplicate loop model remains visible, as do the unconverted public
receive/edit identity boundaries. This is a specific native equality boundary
and lookup cleanup, not completion of the identity family or whole-codebase reform.

## shared writer-code contract

`writer_index_is_exact` checks the actual native helper against the two-case
inline writer-code mapping (Alice → 0, Bo → 1). Both `writer_equality_exact` and
`event_order_is_key_order` withhold the native helper; neither may reconstruct
that mapping by opening its body. The helper contract has a deliberate pattern.
Three default dependency controls remove that pattern at the first caller or
withhold the contract independently in each caller. A separate actual Rust
`writer-index-collides` control maps Bo to zero and must fail native checks plus
the exact helper theorem.

This closes those two writer-index dependencies, without hiding the writer
`PartialEq` implementation or `event_lt` from their owning proofs. The public
identity freshness proofs also lose two redundant spec-only reductions. Their
receive/edit/plan reasoning is not isolated by this deletion; the broader public
boundary and duplicate loop-model migrations remain open. Every prior public
Identity/Accepted theorem signature and pattern is unchanged in this slice.

## redundant WellFormed reductions

The first cleanup removed fifteen redundant reductions from EditWellFormed's
scalar-validity, causal-closure, membership and dependency-validation laws.
Ten opened only project spec definitions. Five named a native function
(`new`, `validate_after`, `past`) inside its own owning boundary proof.
That cleanup added no new contract isolation. The subsequent deletion cut below
removed four `Tactics.norm` steps, and the containment-contract migration removes
the last five reductions. The whole file is now fenced; implicit model/callee
reads outside the named contract boundaries still need migration.

## invalid-result constructor contract

`invalid_is_exact` checks that the actual native `invalid(reason)` helper returns
`Error_Invalid(reason)`, keeping the supplied reason. The duplicate-classification
proof withholds this helper alongside `fact_equal`. Each contract's pattern and
its availability are tested separately; removing the error-constructor pattern
or contract must reject ordinarily at `duplicate_matches_lookup`.

The actual Rust `invalid-forgets-reason` control replaces the supplied reason
with `Counter`. It must fail native checks and the new exact helper theorem.
This is a source control, distinct from the proof-dependency controls. No public
classification theorem is weakened or retargeted. The duplicate loop model and
other public `plan` dependencies remain open; these two hidden callees do not establish
whole-function opacity or close the proof reform.

## planner prefix contracts

The counter proof needs to distinguish the possible results of `plan`; the
identity proofs need to know what happens before validation. Two checked laws in
`EditAtomic` expose just those facts:

- `plan_has_result_shape` supplies the `Err` / `Ok(None)` / `Ok(Some(next))`
  alternatives when the planner's implementation facts are withheld. This is
  constructor information, not admission progress.
- `plan_preserves_duplicate_result` says a classifier error is returned unchanged,
  and a known duplicate returns `Ok(None)`. It deliberately promises nothing
  about the `Ok(false)` branch. Its proof withholds the classifier body and
  treats that result symbolically.

`authored_edit_advances_once` withholds `plan` alongside its two counter helpers.
The three public identity queries (`receive_known_identity`,
`receive_invalid_counter`, `receive_added_has_fresh_event_id`) withhold both
`plan` and `duplicate`, composing the prefix law with the checked classifier law.
The default gate removes each planner pattern and withholds each required
contract at its actual consumer. These must give ordinary named rejections.
Separate native controls ignore a duplicate, swallow a classifier error, and
rewrite the fact passed from `receive` into `plan`.

`EditIdentity` now has no explicit normalization and its whole authored file is
fenced. Its duplicate-loop model remains visible: this is not whole-family
implementation isolation. At that prefix-contract cut, other planner callers still reopened the planner.
The private/shared/receive compositions below now migrate the Commit callers;
Accepted publication boundaries and other implicit model/loop reads remain open.
Neither these prefix laws nor their caller compositions prove successful
admission, causal replay, or delivery convergence.

## redundant EditAccepted and WellFormed reductions

Thirty-three explicit `norm_spec` reductions in EditAccepted and four
`Tactics.norm` steps in EditWellFormed were removed because they were redundant.
The proofs verify without them, and every control still rejects at its usual
owner. No statement, pattern, control owner or budget changes.

What the removed EditAccepted lists named:

- **18 named a native function.** In the opacity map measured on a tree with these
  deletions, every such function is read only by its own owning proofs: `receive`
  (`receive_added_*`), `choose_unseen`, `canonical_step`, `canonical`,
  `clone_selected_fact`, `with_tree`, `has_fact`, `new` and `plan`
  (`successful_plan_pushed_fact`). The `impl_26`/`impl_82` (`Clone`) mentions follow from the
  hax typeclass refinement `x == r`, not from reading a body. That map shows these
  as owner reads; it does not prove isolation.
- **15 named only vector/slice model functions.** Those proofs now read the model
  bodies implicitly. Contracts for them, beyond the existing push-caller `Vector`
  boundary, are still open.

The four WellFormed steps opened `validate_new`, `receive` and `plan` inside the
scalar-validity and direct-dependency laws for those operations. Their deletion
does not establish callee isolation; those implicit reads remain open work.

Kept, with their reductions still needed:

- `append_least_preserves_frontier` (6). The two containment lemmas' five sites
  were retained at that deletion cut, then removed through the contracts below.
- `canonical_orders_facts` (2): without them its peak rises from 0.66% to about 34%.
- The four EditAccepted `Tactics.norm` publication/planner boundaries
  (`plan_publishes_canonical_facts`, `plan_publishes_interpretation`,
  `canonical_step_succeeds`, `canonical_succeeds_for_unique_ids`), which are left
  for the planner migration.
- `selected_id_is_least`: without its reduction its peak rises from 15.6% to about
  34% when combined with this slice, so it is kept by the same cost rule.

The fence now also covers the 26 migrated EditAccepted declarations and the 4
WellFormed declarations that are free of normalization.


## containment through whole-fact witnesses

The last five explicit WellFormed reductions are gone. In
`absence_on_whole_facts`, a selected whole fact is related to its sequence
position by the existing checked slice-index and slice-length contracts. The
model index/length implementations and those contracts' global facts are
withheld; the two explicit calls supply local facts. Native `has_fact` is also
withheld in that query.

`presence_survives_containment` chooses one before-fact with the required ID.
Containment gives the same whole fact in the next slice; the checked absence
law then rules out absence. There is no second position search, reverse lookup
or hand-expanded prefix predicate. That caller withholds the prefix predicate
and native `has_fact`. The absence law has no automatic pattern; its explicit
call supplies the usable contract.

All21 prior WellFormed theorem signatures, premises and patterns remain exact.
Three default `contracts:containment` controls remove the two vector calls and
the absence-law call independently; each must reject ordinarily at its caller.
The whole WellFormed file is fenced against normalization, and its extra
visibility prefixes are not allowed in other families. This does not make all
remaining validators/loop models opaque or close the reform: prior implicit
callee/model reads outside these two boundaries remain open.

## readable public-contract entry point

[`Spec.lt`](Spec.lt) presents the 33 established public behavior laws through ten
checked headlines. Each calls the existing laws explicitly and withholds the
native operation bodies. The original proofs and their premises stay unchanged.
Implementation-only boundaries such as `receive_uses_plan` remain in their owning
families; this is a public behavior surface, not a second implementation layer.

| headline | explicit premise | constituent laws |
| --- | --- | --- |
| `new_establishes_valid_facts` | none; conclusion is conditional on successful construction | four storage invariants |
| `receive_preserves_valid_facts` | valid stored facts before | four invariant preservations, every return |
| `edit_preserves_valid_facts` | valid stored facts before | four invariant preservations, every return |
| `receive_obeys_contract` | none | neutrality/private state, exact contents, fresh ID, unique/ordered storage, new-fact scalars and direct dependencies (eight laws) |
| `edit_obeys_contract` | none | neutrality, counter, request, same-commit replay, exact contents, fresh ID, storage order and new-fact scalars (eight laws) |
| `known_identity_is_classified` | in-bounds member, unique before-IDs, matching ID and valid counter | duplicate/conflict classification |
| `invalid_counter_is_rejected` | zero or over-domain counter | exact invalid-counter return |
| `equal_shared_history_gives_same_admission` | equal facts/tree/limits | same admission despite different private writer/counter |
| `authored_fact_admits_on_equal_shared_history` | equal facts/tree/limits | conditional authored-fact delivery and receiver-private-state preservation |
| `equal_candidate_contents_give_same_rebuild` | equal candidate whole-fact support and length | identical facts/tree when both receives are Added |

The four storage invariants are unique IDs, nondecreasing event-key storage
order, inserted Unicode scalars and direct causal-reference closure. This is
not full representation WF, causal acyclicity or a text-order semantics theorem.
The outcome bundles apply with no before-invariant premise; their success-only
clauses say nothing about a call that errors or returns no authored fact. Their
neutrality clauses cover those other returns explicitly.

Both same-history premises are visible `takes` lines. Equal candidate contents
allows permutations and is distinct from equal starting shared state. None of
these conditional laws proves delivery convergence, admission progress or
refinement against an independent CRDT semantics. Those remain open.

`contracts:spec` removes each of the 33 public-law calls independently and
requires ordinary rejection at its headline. Patternless lemmas supply their
posts by these explicit calls; there are no decorative lemma-name prunes.
The default positive chain checks Spec and Causal, while native mutation roots
and owners stay unchanged. Spec visibility permissions remain module-scoped;
other families have their own explicit permissions.

## private state through tree publication

`tree_publication_keeps_private` checks that the actual `with_tree` call keeps
its input writer, next counter and limits. `plan_preserves_private_state` uses
that contract with `with_tree` withheld: any `Ok(Some(next))` preserves those
fields; errors and duplicate/no-new-state results make no publication claim.
The existing public `receive_preserves_private_state` then uses this planner law
with `plan` withheld. Its universal conclusion is unchanged.

`same_private` names the three-field relation once. The existing result predicate
`private_unchanged` simply applies it to the returned instance; its equivalence
to the original inline predicate is checked during this migration. Neither law
constrains the resulting facts/tree or proves acceptance, private-state
independence, or semantic refinement.

Both helper patterns and both contracts have default dependency-removal controls
at their actual caller. The private family's probes run in a separate copy so
they do not modify the positive workspace. Two actual Rust mutations clear the
private counter in the tree setter or in `plan` before publication; they must
fail native tests and their corresponding checked contract. The existing
receive-success-counter mutation still tests the real public receive boundary.

This private-state path alone does not establish shared-state independence;
that separate contract migration is described below. The later receive/commit
boundary migration removes the remaining three Commit normalization sites and
extends the fence to the whole file. Remaining Accepted/WellFormed boundaries,
model isolation and loop families are still open.

## same-history admission without private planner details

`tree_publication_respects_shared` compares two setter calls with the same tree
and equal shared inputs (facts, tree and limits). Its paired trigger exposes
that relational law to `plan_ignores_private_state`, whose two input replicas
have the same shared fields but may differ in writer/counter. Planning returns
matching error/duplicate/success cases; successful results have equal shared
fields. The existing public `admission_ignores_private_state` composes that law
with `plan` withheld, preserving its exact same-history premise and conclusion.
The planner boundary itself withholds `with_tree`.

The setter law is deliberately relational: it does not claim the supplied tree
was installed. A setter that ignored that tree identically on both replicas
would still respect shared equality; existing interpretation/publication controls
must continue to catch that separate error. Neither these laws nor the public
composition prove general delivery convergence or admission progress.

Four new default dependency controls remove the paired patterns or withhold
these contracts at their actual callers. A new native setter mutation makes
publication depend on the private writer. The existing `receive-private-gate`
mutation keeps its source/anchor but now rejects earlier at
`plan_ignores_private_state`, the new checked callee boundary, rather than the
public composition. This is the sole control-owner migration in this slice;
the public theorem and its premise are unchanged. The private-state family’s
four controls still run, scoped to their own declarations despite the additional
visibility blocks. The following migration closes the remaining three explicit
Commit normalization sites.


## exact receive boundary and commit composition

`received_plan` gives the three-case public receive result for an arbitrary
planner result: the same error with unchanged state, duplicate with unchanged
state, or Added with the planned state. `receive_uses_plan` checks that equation
against actual receive with plan withheld. It is called explicitly, so it needs
no new automatic trigger.

The same-commit proof composes this receive equation, the existing exact counter
calculation/installation contracts, and the public counter-step law. Plan,
receive, counter helpers, frontier and invalid's native bodies are withheld in
its source-boundary query. The exact calculator and receive equation are called
explicitly; neither has an automatic pattern. Deleting each call rejects the
public proof. Request binding likewise needs none of those callee bodies. Their own edit boundary and model definitions remain
visible; this is not whole-model opacity.

The private and shared receive compositions now call the receive equation too,
with receive's body withheld. The final same-history delivery composition uses
its three public laws with both native edit and receive withheld. All prior
universal conclusions, premises and patterns remain exact. The whole Commit file
is fenced against explicit normalization. Nine new default dependency controls
exercise the receive/counter/setter dependencies and final public composition;
the preceding eight private/shared controls remain required.

Two existing controls move to the new source boundary: `receive-plan-rewrites-counter`
and `receive-success-counter` now reject at `receive_uses_plan`, which is the
checked declaration reading receive's body. Their actual Rust mutations and tests
are unchanged. The old public same-commit/private-state laws remain unchanged and
are connected to that equation by the new dependency controls. The earlier
`receive-private-gate` move to the relational planner law remains as documented.
No other owner moves, no native or hax snapshot changes, and no convergence or
extra-concurrent-history claim follows from this reform.

## further redundant EditAccepted reductions

Four more explicit reductions are removed:
- three of the six in `append_least_preserves_frontier`: the order-frontier opening, the `push`/vector-model opening (now carried by the push and Vector contracts) and the final ordered-push opening;
- one of the two in `canonical_orders_facts`.

They were chosen by adding sites one at a time, keeping each only if the positive chain and the cost rule still held. Removing all six frontier sites, or both `canonical_orders_facts` sites (about 34%), does not hold.

`selected_id_is_least`'s reduction can be removed on its own (peak 15.6% to about 22%). Combined with this slice its peak reaches about 34%, so it is kept by the cost rule, as in the previous slice.

The frontier lemma keeps three reductions and `canonical_orders_facts` keeps one, so neither declaration is fenced yet. No statement, pattern or control owner changes. The deleted lists that named `push` or vector models leave implicit model reads; that is cleanup, not callee isolation.
## remaining-family reform candidate

The remaining-family candidate preserves the established universal claims,
including the held `EditCausal` rank component. It adds no transitive-past,
scheduling, semantic-refinement, admission-progress or convergence claim.

Loop clients provide semantic invariants and completion/return conditions.
`early_return_preserve_any` covers validators whose prefix loops can fail before
the final check. The identity scan uses `option_interpret_any`; the break
adapter has checked step/end equations. Universal adapters share
`Classical.forall_intro_3 (Classical.move_requires_3 each)` rather than copying
another quantified proposition. The option/break adapters deliberately remove
their old fuel-sensitive quantifier triggers; their logical types are unchanged.

The actual constructor's empty-fact contract uses the explicit, patternless
`Vector.empty_vector_contents` equation. Scalar, closure and rank establishment
compose that contract with `new` withheld. A successful-plan prefix contract
states that actual validation succeeded; it promises no planning progress.

Selected caller queries withhold native callees, fold encodings and vector/slice
model operations. These are query-local visibility boundaries, not globally
opaque modules. Contract-call removals test the recorded compositions;
patterned membership facts have separate per-caller withholding controls.
`contracts:remaining` selects these checks, and no-argument CI includes them.
Existing native source-control owners are retained.

The positive gate checks both `Spec` and `EditCausal`; mutation roots retain
their owning Atomic or WellFormed chain. Eleven reachable project compiler
targets yield a 692s aggregate allowance under the unchanged graph policy.
Each compiler still has 60s and the solver rlimit remains 100.

`EditCausal` carries a ghost rank, absent from Rust storage: each direct
predecessor ranks below its event, and accepted ranks stay below a bound.
Added/Authored extend this certificate at a fresh ID; neutral calls preserve it.
A separately defined edge and finite path connect the certificate to exclusion
of nonempty causal cycles. This covers finite public-call continuations from
`new`, under the existing translation/model trust. Arbitrary closed abstract
states need not admit such a certificate. Derived Clone preserves the existing
certificate through hax's identity-refined Clone signature; it grants no writer
lease. Ghost-only rank/edge controls are separate from native mutations.


## EditAccepted without normalization

The last nine explicit reductions in EditAccepted are gone, and the whole module
is fenced. It no longer imports `FStar.NormSteps`. Each affected proof now states
its conclusion in an assertion that withholds the callee bodies with
`Tactics.prune`, so it can only pass through the callee contracts. The
`contracts:accepted` family withholds each of those contracts in turn and
requires the owner to reject.

| proof | callee bodies withheld | contract it composes |
| --- | --- | --- |
| `selected_id_is_least` (owns `choose_unseen`) | `has_fact`, `event_lt`, `fold_range_return` | `least_extends_all` (the quantified loop step in spec terms), `event_order_is_key_order` |
| `canonical_orders_facts` (owns `canonical`) | `canonical_step`, `choose_unseen`, `push`, `fold_range_return` | `canonical_step_preserves_order` (hinted) |
| `canonical_succeeds_for_unique_ids` (owns `canonical`) | the same four | `canonical_step_succeeds` + `canonical_step_selects_whole_facts` (hinted) |
| `canonical_step_succeeds` (owns `canonical_step`) | `choose_unseen`, `push`, `clone_selected_fact`, `has_fact` | `choice_always_returns`, `selected_id_is_least`, an explicit `push_result_is_exact` instance |
| `append_least_preserves_frontier` (caller of `push`) | `push`; the vector models in its one slice equation | `push_membership`, `push_result_is_exact`, Vector, `frontier_bounds_unseen` |
| `plan_publishes_canonical_facts` (owns `plan`) | `with_tree`, `canonical`, `interpret`, `duplicate`, `push` | `tree_installation_preserves_facts` (local hint), `canonical`/`interpret` result shapes |
| `plan_publishes_interpretation` (owns `plan`) | the same five | `tree_installation_preserves_facts` and the new setter contract `tree_installation_installs_tree` (local hints), the result shapes |

New declarations: `least_next`, `least_extends_all`,
`tree_installation_installs_tree`, `result_shape` and the hinted
`canonical_has_result_shape` / `interpret_has_result_shape`.

**Why the result shapes exist.** `Tactics.prune` withholds a function's typing
facts along with its body. Without "`canonical x` is a `Result`", the solver
cannot rebuild `canonical x == Ok v` from the planner's match, so withholding
`canonical` failed even though the conclusion only needs congruence. The two
shape lemmas state only the declared result type, following
`plan_has_result_shape`. Each is load-bearing: removing its pattern makes
`plan_publishes_canonical_facts` reject. An equivalent `duplicate` shape turned
out unnecessary and is not included.

**Owner move:** `plan-keeps-old-tree` now rejects first at the setter contract
`tree_installation_installs_tree`, which reads `with_tree`'s body, instead of
at `plan_publishes_interpretation`. The pattern-removal control
`accepted-interpretation-without-tree-contract` ties the public theorem to that
contract. With its callee bodies withheld,
`canonical_orders_facts` needs no base-case lemma (peak 1.35%). With them
visible and no reduction, it peaked at about 34% (82% in the earlier sweep). No old statement or
pattern changes; that migration records the setter control-owner change.

**Note.**
- Each prune in `canonical_step_succeeds` passes alone. Withholding `push` and
  `clone_selected_fact` together needs the explicit `push_result_is_exact`
  instance.

## Result-level Accepted loop callers

Accepted's seven loop owners now supply an invariant, an identity finish map,
and separate `Ok`/`Err` conditions to `LoopUtil.result_preserve_any`. Their final
source-linked queries withhold the fold, `step_safe` and `output_safe`; callers
no longer need the interpreter's internal safety predicates to recover their
public result property.

| owner | `Ok` condition | `Err` condition |
| --- | --- | --- |
| `selected_id_is_unseen` | the choice is absent from the output | unconstrained |
| `canonical_has_unique_ids` | unique IDs | unconstrained |
| `canonical_selects_whole_facts` | exact-length whole-fact selection invariant | unconstrained |
| `selected_id_is_least` | least unseen choice | unconstrained |
| `canonical_orders_facts` | ordered facts and frontier | unconstrained |
| `choice_always_returns` | unconstrained | false |
| `canonical_succeeds_for_unique_ids` | unconstrained | false |

Preservation laws still allow errors; the existing totality laws exclude them.
Every old theorem type, premise and pattern is unchanged. Each owner has a
separate default call-removal control requiring an ordinary rejection at that
owner when its Result-rule call is removed, in addition to the ten existing
Accepted dependency cases. Four further call-removal checks tie the canonical
owners to their source frame. These checks extend `contracts:accepted`; the CI
entry is unchanged.

This closes these loop-interface dependencies, not every callee/model dependency
in the family. Source-boundary proofs still inspect the function they establish;
no single-boundary-per-function policy or new semantic claim is introduced.

The canonical owners compose one checked source-frame equation:
`canonical` starts empty, runs its actual fallible step over the complete
`0..input.len()` range, then publishes the resulting `Result`. The frame
equation withholds `canonical_step`; the four public callers withhold
`canonical` as well as the fold and the two internal predicates. The frame
is ordinary authored code checked against the fresh native translation, not
an assumed equation. Its callback remains in this one boundary definition.

Two existing native mutations now reject at
`EditAccepted.canonical_uses_complete_range`: `content-omits-facts`
changes the range to `0..0`, and `canonical-refuses` changes the final
return to an error. Their native patches are unchanged. The first patch also
changes hax's inferred index type to i32; without the frame it causes an
unrelated failure at the uniqueness theorem, despite the empty output being
unique. That failure is not counted. The frame checks the actual range/return
wiring directly, and its four dependency checks preserve each public theorem's
connection to that wiring. These are explicit control-owner migrations, with
no weakened universal theorem or broader admission/convergence claim.

## Lookup and empty-state boundaries

The final Accepted lookup bridge composes `option_interpret_any` with
`member_lookup`, withholding both the fold and `option_run`. Its induction
uses checked step/end equations with `option_run` withheld in each branch.
The absence IFF proves its reverse implication first, then closes the two
boolean cases with the membership implementation hidden. No caller needs to
recover that implication by expanding the native lookup.
The final assertions stay inside their branches, where the step/induction facts
are available; appending one after the conditional was insufficient.

`empty_has_unique_ids` composes the checked empty-vector equation instead of
reading the constructor model. `new_establishes_fact_order` composes the checked
`new_has_empty_facts` contract with the native constructor hidden. These two
contracts come from the remaining-family migration in PR37; this addition is
for the combined36/37 tree, not a standalone advance of the PR36 base.

Nineteen additional default Accepted controls remove the lookup interpreter,
lookup induction, its step/end/recursive calls, both directions of the absence
IFF the Boolean-range hint, both constructor-value equations, two local step calls,
four canonical initializer calls and the two empty-state contracts
one at a time. Each requires its own ordinary named rejection. No old theorem
header, native mutation, native control owner or imported model changes in this
addition. `contracts:accepted` retains every prior case; the optional selector
is for focused local checks and defaults to all cases.

Checked Vector value equations describe from_seq and empty construction, beside the existing slice equations. Four loop callers use the empty-value equation with the constructor model hidden. The push boundary uses from_seq_value only after splitting the existing capacity guard: its precondition is invalid on the full-capacity branch. Both unique/content local adapters compose step laws with the native step hidden. The membership Boolean-range hint restores only the declared return type lost by pruning, not membership semantics.

## Independent canonical-frame controls

The Accepted family's default path also tests two ghost-only frame faults:
`accepted-frame-refuses` must reject at `canonical_succeeds_for_unique_ids`,
and `accepted-frame-drops-facts` at `canonical_selects_whole_facts`.
These leave Rust and its extracted translation unchanged. They test the public
laws independently of the source-to-frame transcription check, which already
owns the actual malformed-native-loop controls.

Only inside the family's disposable proof copy, the harness replaces the exact
transcription lemma with a test-only assumed declaration. A healthy frame must
first verify under that same trust cut. Each fault then changes only the ghost
`canonical_loop_result` body, preserving all consumer headers and proofs.
Ordinary named rejection is mandatory; parser/type errors, unrelated failures
and resource exhaustion are not credited. The original view is restored in
`finally`, including on compiler failure, and the native source must stay exact.

The assumed declaration is deliberate fault injection, never a production lemma,
a positive proof result, a new model axiom or certification of the transcription
boundary. The production source/view/receipts remain unchanged. Existing native
controls and their source-frame owners are retained; these two tests supplement
them with independent public progress/content discrimination.

The push boundary additionally composes a local checked length-value equation:
its vector length equals the usize constructor of its slice cardinality. Both
final guard branches withhold all six designated vector/slice model operations.
Removing that explicit contract must reject at push_result_is_exact. A numeric
length equation alone was insufficient when pruning also removed the result's
constructor/type facts; the exact typed value restores those facts without
reopening the model in the caller. The default family therefore retains all21
prior dependency cases, adds19 (40 in total), then runs the healthy ghost-frame
fixture and the two independent public progress/content fault cases.

The global `vector_contents` pattern-removal control is owned by
`push_result_is_exact`: the final length/model-opacity repair makes that
boundary the first dependent consumer. Its scoped equation-removal counterpart
still rejects at `append_fresh_preserves_unique`, and the remaining per-caller
controls remain unchanged. This is a proof-dependency control-owner migration,
not a native mutation-owner change or a weakened rejection criterion.

## compiler-workaround cleanup candidate

The recorded private emitter revision fixes binary control-expression grouping.
The writer-code law now uses its two-case match directly, and break_step no
longer needs a state ascription solely to preserve match parentheses. The Vector
constructor laws use the already-supported positional native implicit arguments
instead of result ascriptions to select the allocator. The allocator remains
explicit: removing that information would change the SMT-pattern boundary.
The re-emitted containment law gains grouping around its quantified right side.
No normalization, admitted axiom, native/model change or proof-budget change is
introduced. The loop frame uses facts_vec again with an explicit transparent alias. The
reduced failure reproduces in raw F*, and opt-in native alias transparency
repairs it at unchanged limits. This is an interop capability, not a claim that
Latte previously emitted the alias incorrectly; ordinary alias behavior stays
unchanged.

## causal past: seed retention and no spurious ancestors

`EditPast.lt` connects the actual extracted `past` call to the independently
stated finite `EditCausal.causal_path` relation. On **every successful return**:

- every root supplied in `after` remains selected;
- every selected ID has a finite predecessor path from some supplied root
  (the root itself is the zero-edge case).

The source boundary proves the stronger reusable invariant: if a predicate on
IDs contains the roots and is closed under the stored facts' direct edges,
every successful selected vector stays in that predicate and retains the roots.
It then instantiates that invariant with finite-path ancestry. These are set-membership claims, not multiplicity or output-order claims. No acyclicity or
unique-ID premise is needed for these soundness/retention laws. They do not
promise that `past` returns Ok, or that it selects **all** ancestors.

The native membership scan and the two expansion layers use indexed loops.
`extend_past` expands one selected fact; `past_pass` scans stored facts;
`past` repeats the scan in the original order. Their source-linked proofs use
LoopUtil and checked callee contracts. Native membership/push, expansion and
pass bodies are withheld at their callers; the final ancestry composition
withholds `past`. Vector/slice models remain visible at these boundaries. No
iterator semantics, axiom, model or budget is added. This is not a formal
old/new Rust equivalence proof; the native acceptance fixture supplies bounded
source-change evidence. Fresh hax extraction is committed and checked exactly.

The positive gate includes EditPast. Focused development commands:

```sh
node scripts/check-edit-proofs.mjs /tmp/past-proof contracts:past \
  past-drops-roots past-invents-id past-membership-always-false \
  past-skips-predecessors past-skips-passes
node scripts/check-causal-basis-native.mjs /tmp/past-native
```

The Rust controls erase the roots, invent an unrelated ID, make membership
always false, skip predecessor expansion, or skip the outer passes. Each must
fail the native fixture and ordinarily reject at its registered owner (the
outer-pass frame attribution is qualified below). The `past` contract family
checks the membership, soundness, bounded-coverage and exact-closure caller
connections. A resource failure or unrelated error is not detection.

The separate four-control native command above is manual evidence, not part of
CI; only its positive native fixture is discovered by the workspace gate. Its
continued mutation sensitivity is not certified by CI.

This soundness law alone does not establish closure completeness. The following
coverage and finite-graph components establish exact membership on success.
Successful computation (no `Err` in the stated domain) and the scheduler's
once-only/order/progress and subset-schedule projection laws remain open in #42.

### bounded predecessor-path coverage

`past_contains_short_paths` adds the converse direction for every independently
stated `EditCausal.causal_path` with at most `facts.len()` edges: **if actual
`past` returns `Ok`, the path's endpoint is selected**. Its root must belong to
the offered roots. No uniqueness or acyclicity premise is needed for this law.

The proof follows the actual nested loops: expansion covers every predecessor
of a selected fact, one pass covers edges from its initial selection, and each
outer pass increases the covered path depth by one. Checked callee contracts
are used with their native bodies withheld. A checked Boolean-range lemma keeps
membership's declared type available under that withholding; it is not a new
membership axiom. The path bridge uses the independent finite-list relation.

The `past` contract family also removes the pass contract at the outer caller
and the depth contract at the finite-path caller. New default Rust controls
skip predecessor expansion and skip all outer passes. They must fail the
native fixture and ordinarily reject at their registered owners. Skipping
predecessors reaches the new expansion-coverage law. Skipping outer passes
reaches the pre-existing `past_stays_in_closed_set` loop frame first: that is
structural frame detection, not a semantic counterexample to soundness and not
credited as an independent coverage-law rejection.

This bounded-path law alone does not establish unbounded closure completeness;
the finite-graph bridge below supplies that step. Successful computation
(absence of `Err` on valid fitting inputs), scheduler progress/order and #42
remain open.
There is no Rust, hax snapshot, model, compiler pin or budget change in this
coverage extension.

### exact causal ID closure on success

`successful_past_is_exact_closure` proves, for arbitrary stored facts and roots:
if actual `past` returns `Ok(selected)`, then for every event ID,

```text
member(selected, id) iff
  some root belongs to roots and has a finite causal_path to id
```

There is **no path-length, uniqueness or acyclicity premise**. This is exact
set membership, not vector order or multiplicity, and not a guarantee of `Ok`.

The finite-graph bridge is constructive. Every edge's parent has a stored fact.
In a walk with more than `facts.len()` edges, map its first `facts.len()+1`
parents to stored-fact positions. The checked finite pigeonhole principle finds
two equal positions, hence equal IDs. Cutting out the intervening loop preserves
the endpoint and strictly shortens the walk. Recursion produces a path of at
most `facts.len()` edges. The endpoint itself need not have a stored fact;
only the edge-bearing parents are counted. Duplicate fact IDs and cycles do
not invalidate the argument.

`past_contains_every_causal_path` composes that bridge with bounded coverage.
The final exactness theorem composes it with the earlier no-spurious-ancestor
law, withholding actual `past` at the composition boundary. Two additional
`past` controls remove the shortening and unbounded-path contract calls and
require ordinary rejection at their callers. Prior theorem statements and
source/view prefixes are retained; no native source, hax snapshot, axiom,
compiler/model pin or limit changes.
