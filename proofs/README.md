# proof scope

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
grace; ten seconds cover make overhead. For the current eight-module edit chain
this is 506 seconds, while every F* process remains capped at 60 seconds and
every solver query at rlimit100. Dependency discovery remains independently
capped at 60 seconds; model bootstrap keeps its explicit 600-second driver.
Project callers cannot enlarge the derived bound through an explicit override.
The selected target list, policy and bounds are printed and retained in
`last-check.stats.json`. The simulated-compiler gate tests a serial chain,
separate compiler/aggregate timeouts, SIGTERM-resistant compiler kill grace,
and normal rejection; none is a proof-success substitute.

The smoke fixture establishes no CRDT convergence, ordering, undo, codec, Wasm or browser property.

The [prospective API/verification contract](../docs/api-verification.md) lists the proposed V1–V9 obligations. None is currently discharged. The [undo analysis](../docs/undo-semantics.md) records the semantic/algorithmic stop gate; the loop proof does not bypass it.

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

## counter-control isolation

The counter guard and successor calculation are a pure native helper; no
instance counter is changed until the existing successful commit. Its lemma
checks the returned successor and the exact over-limit error. The public
`authored_edit_advances_once` statement is unchanged and remains part of the
full positive proof chain.

The reused-counter mutation changes that actual helper's successful result from
`counter + 1` to `counter`. It must still fail native public tests and now reject
`counter_result_advances_once` ordinarily. These counter negative checks stop at their
owning `EditAtomic` module; positive verification reaches `EditWellFormed`.
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
those checked publication laws. The positive gate verifies the full chain
through `EditWellFormed`; every non-counter control uses that same root,
with its original owning theorem (relocated where appropriate). The three
counter controls still stop at `EditAtomic`.

This separates cumulative compiler work into semantic modules; it does not
increase the 60-second compiler cap or solver rlimit100. The actual graph now
has eight compiler targets, so the unchanged aggregate formula yields506s.
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
