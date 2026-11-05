# after the experimental edit/admit merge

PR18 merged the experimental Rust candidate at `f86cc7f`, retaining reviewed
head `4e0f55d` unchanged. That head passed the complete native/proofs,
reference and questionnaire checks on ARM. This is a development baseline,
not the verified edit-only exit, the history milestone or a release.

**Priority changed by Ren:** reform the existing proof codebase around proved
function contracts, deliberate patterns and a simple for-loop interface before
any further semantic work. This supersedes the earlier “eventual cleanup; do not
block proofs on style” sequencing. Sections 1–5 below are the continuation after
that gate, not work to advance alongside it. The causal-rank candidate in PR20
is held unchanged; it is not an exception to the new gate.

After the reform, connect **what an admitted edit means** to the actual Rust
transition and prove supported valid inputs can be admitted. Keep replay while
closing those obligations; incremental performance work remains later.

## what the merge supplies

The [native contract](rust-edit-admit.md) and [proof scope](../proofs/README.md)
are authoritative for the implemented domain and exact theorem premises.
The merged chain supplies transactional ordinary returns, counter and request
binding, same-history commit coherence, identity classification, exact fact
publication, unique accepted IDs, canonical fact storage order and totality,
conditional structural rebuild agreement, scalar-valid facts and direct causal
reference closure. These are proofs about the hax translation of actual source;
hax and its imported models remain trusted. Committed extraction snapshots
make translation changes reviewable, not proved equivalent to Rust.

Three distinctions determine the remaining work:

- Equal accepted whole-fact sets can yield identical canonical vectors and
  rebuilt trees without proving those trees implement the independent ordering
  specification. Structural agreement is not yet semantic refinement.
- The same *offered* facts can produce different accepted subsets at capacity.
  Keep the native counterexamples. Neither this merge nor the plan adopts a
  new budget policy or promises over-capacity synchronization.
- Same-ID facts with different content also retain whichever arrives first.
  The joint exit requires an **identity-consistent offered history**: every
  event ID denotes exactly one whole fact, including any fact already accepted
  in the initial state. See the [cloned-writer witness](rust-edit-admit.md#domain-and-representation).
  Conflicting histories remain an explicit exclusion, not a proposed conflict
  resolution rule. External producer fencing is a caller obligation; neither
  `Clone` nor the local allocator enforces it.

## 0. reform contracts, patterns and for-loop proofs first

**Requested outcome:** proofs compose semantic laws instead of repeatedly
negotiating which Rust definitions, matches and local bindings to unfold.
Putting the same reduction lists behind a renamed tactic does not meet this
request. This is a mandatory first deliverable, not a cleanup suggestion.

**Scope:** all project-authored proof code: Prelude, LoopUtil, Smoke, EditAtomic,
EditCommit, EditIdentity, EditAccepted and EditWellFormed, plus the held
EditCausal candidate before that candidate advances. Generated authored F* views,
receipts and verification roots follow those changes. Imported F*/hax models and
the private Latte compiler are not a codebase to rewrite or new trust to add.
Unproved Rust behavior does not become proved merely by giving it a contract.

**Boundary decision still required:** Ren has requested eliminating the fiddly
normalization approach throughout the codebase. No exception has been approved
for source-linking lemmas. Clarify whether zero explicit normalization is required
even there, or whether a small, explicitly approved boundary may retain it while
all callers use contracts. Until that answer, do not declare retained boundary
normalizers compliant or mark the reform complete. The downstream target is
unambiguous: no hand-maintained implementation unfolding lists in callers.

### 0a. map and prove useful function contracts

Inspect the existing proof families and record which implementation detail each
caller currently opens, which semantic law it actually needs, and the source
boundary that must prove that law. Keep this as a small reviewable coverage
table, not a new framework. Cover helper wiring as well as helper bodies.

For each needed Rust function, prove a pre/post or exact-result law about its
actual extracted call. State independent result predicates where appropriate:
unchanged full state, exact publication, freshness, validation success/error,
ordering or interpretation installation. Several laws per function can be more
useful than one monolithic contract. These are proved lemmas, not assumed hax
annotations or axioms.

Use deliberate Latte `hint` patterns on the actual function-call terms where
automatic instantiation helps. Check that a caller produces the matching term,
that needed premises are available, and that the trigger does not generate a
self-sustaining matching loop. Use explicit calls where they make the dependency
clearer. Pattern syntax alone is not the abstraction: downstream proofs must be
able to use the law without reopening its implementation.

**First acceptance slice:** the existing counter calculation → installation →
actual public call wiring. Preserve its universal conclusions and the three
existing arithmetic/setter/wrong-argument controls. A theorem about the setter
alone is not an exit; the wrong argument at the real call must still reject
ordinarily at its public or call-boundary law. Use this complete slice to check
the contract/pattern mechanism before migrating the larger proof families.

### 0b. expose ordinary for loops through a simple invariant rule

Build a derived interface over the **actual pinned hax loop interpreter** already
connected by LoopUtil. An ordinary no-break bounded loop should expose:

- an initial accumulator and a body step;
- an invariant at the initial index;
- one preservation obligation from index i/state to the next index/state;
- an invariant/postcondition at normal completion.

The caller should not reconstruct nested ControlFlow encodings, hax's annotation
argument or `step_safe`/`output_safe` bookkeeping for every basic loop. Prove the
adapter once; do not replace the Rust loop by a separate convenient algorithm
and treat agreement as an assumption. Preserve range endpoints, empty-range and
index/representation behavior explicitly. Generalizing beyond the first basic
range shape must not silently add a precondition absent from Rust.

Provide separately named derived rules for early error/return or break shapes
needed by existing callers. Normal completion, error return and break cannot be
collapsed into one success case. Keep the general interpreter behind those
rules rather than weakening the existing early-return controls to fit a simpler
interface. Inventory supported loop shapes; leave unsupported/unproved Rust loops
explicitly unsupported, rather than claiming they were verified by this reform.

**Acceptance:** migrate the actual Boolean-loop smoke proof through the basic
rule, preserving parity/involution and its wrong-body control. Then migrate an
actual fallible validation loop and its public caller, retaining success,
early-error and wrong-argument/refusal controls. This checks that the interface
works at both the loop and real public boundary, not just on an authored example.

### 0c. migrate the whole authored proof codebase

Carry the proven interfaces through identity/membership, exact publication and
canonicalization, scalar/direct-reference validation, commit/neutral returns,
and the held causal-rank component. Pure recursive lemmas also get usable
semantic equations/contracts instead of repeated manual reduction scripts.

For each family, compare the before/after theorem statements and their source
bindings, then run the affected positive and semantic controls. Keep a named
mapping for moved/renamed laws. Preserve all-return claims, not only successful
cases. Do not erase a required premise, reduce the quantifier domain, bless an
unrelated error or count timeout/resource exhaustion as a successful control.
Revalidate source/view receipts and actual gate discovery after moves.

**Whole-reform exit:** every authored proof family is accounted for; downstream
callers use proved contracts and loop rules without manual implementation
unfolding; any remaining boundary machinery meets Ren's explicitly chosen
policy. Add a focused recurrence guard for prohibited authored normalization
forms once that policy is settled, with a failing control. A wrapper or alias
that merely hides the old reduction lists does not satisfy the gate. Existing
public conclusions and semantic controls remain intact; fresh extraction/view
binding, scoped review and exact-head ARM acceptance pass. Keep compiler60s and
query rlimit100 unchanged; the aggregate graph policy remains separate.

Do not resume sections 1–5, cache adoption, new engine features or other queued
implementation/review work before this reform gate is closed. This is a change
of sequencing, not permission to remove unfinished semantic/release obligations.

## 1. close reachable causal well-formedness

**Deliverable:** source-linked acyclicity for accepted facts, composed through
construction and every public receive/edit return. Direct-reference closure
alone admits cyclic abstract states; the new claim must distinguish reachable
states from arbitrary closed inputs.

Use freshness, exact old-plus-new publication and the requirement that an
incoming fact's direct predecessors already exist. A ghost admission rank is
one candidate witness: preserve old ranks and assign the new fact a rank above
its predecessors. It must be established and preserved, not postulated. Rust
fact-storage ID order is not a causal rank. Account for cloned replicas and
external writer fencing explicitly; cloning supplies no fresh writer lease.

**Acceptance:** the public composition establishes a finite DAG without a
caller-supplied acyclicity assumption on each successful call. Preserve the
existing neutral-return laws. Retain a cyclic closed abstract-state separator,
and source mutations at the prerequisite/freshness/publication boundaries that
violate the claimed invariant and reject at the corresponding unchanged law.
Reuse existing controls where they already cross that boundary.

## 2. prove the actual causal basis and scheduler

**Deliverable:** `past` computes exactly the transitive predecessor set, and the
actual replay scheduler processes each accepted event once after its causal
past on finite well-formed inputs. Prove termination/progress of that scheduler
inside the supported representation domain; canonical storage totality does
not establish it.

Relate selected membership, the actual done sequence and readiness. Then prove
the projection needed by author reconstruction: replaying the full history and
restricting to `past(e)` gives the same schedule as replaying that predecessor-
closed subset alone. ID tie-breaking chooses among ready events; it does not
replace causal readiness. State any uniqueness, closure and representability
premises in the theorem rather than importing them from an example.

**Acceptance:** two receivers with different extra concurrent history derive
the same author basis for the same event. Exercise actual Rust calls under
multiple causal schedules, with exact basis/node observations, and connect the
universal law to the extracted loops. Missing references, cycles outside the
reachable domain, skipped closure expansion and wrong readiness/author-basis
mutations remain discriminators. An executed corpus supports this law but
cannot replace it.

### fit/domain preflight before semantic refinement

After slice 2, define slice 4's valid-input/fit predicate and probe the actual
native fallible paths **before** investing in slice 3's full refinement proof.
Include intermediate structures and prefix resources, and retain any valid
fitting refusal as a blocker. This can expose a necessary representation repair
while there is less refinement work to redo. The native probes do not close
public progress. Slice 4's scheduler dependency is on slice 2; its full proof
and slice 3's semantic proof must meet at the joint exit, rather than treating
3 → 4 as a strict logical dependency. Keep one active deliverable at a time.

## 3. connect authoring and retained-node interpretation to meaning

**Deliverable:** an explicit abstraction from native facts/tree to the chosen
edit-only sequence semantics, independent of the Rust replay algorithm. Use the
[FugueMax account](fugue-ordering.md) to state the ordering obligations and the
[Rust transition cut](rust-transition-cut.md) for the whole-instance boundary.
Name any algorithmic assumption still trusted rather than calling the result
fully verified.

Connect actual birth identities/scalars, gap and deletion targets, derived
origins, retained-node integration, traversal and visible projection. Establish
that local authoring targets its visible pre-edit basis and that admission
reconstructs that author's basis despite extra concurrent receiver facts.
Scalar-valid facts alone do not prove node payload correspondence. Extend the
existing same-history commit result to this semantic boundary, with its exact
premises visible.

**Acceptance:** local edits and remote admission refine the independent
transition on success and preserve the prior abstraction on neutral returns.
Directed replacement, hidden-endpoint, prepend-run and Unicode cases plus a
bounded two-writer schedule generator compare complete relevant abstract state,
not only final strings. Wrong origins, receiver-contaminated author bases,
changed scalar/target and traversal mutations must reach their intended
semantic assertions and owning proofs. Do not weaken an existing public claim
to fit a representation change.

## 4. close valid-fitting admission progress

**Deliverable:** a public progress theorem for a precisely named valid-input
and capacity domain, plus `Internal` unreachability there. Trace each fallible
step from validation through causal replay, tree construction and final
publication. Storage totality and helper completeness cover only parts of it.

Define the fit predicate before claiming progress: include relevant prefixes,
intermediate author/reconstruction structures, numeric bounds and every counted
resource. A final set fitting an aggregate count is not automatically enough.
Separate missing prerequisites, invalid/conflicting facts, caller-owned resource
deferral and an unreachable internal failure. Show disposition agreement only
under premises that really imply it; never extrapolate it to the over-capacity
witnesses.

**Acceptance:** valid supported facts with available prerequisites and the
proved fit conditions return Added (or Duplicate where appropriate), while
invalid/deferred calls retain the existing full-instance neutrality. Native
refusal controls and unchanged public theorems must detect arbitrary refusal
and internal-error injection. If an actual valid fitting history fails, retain
it as a blocker; do not shrink the domain silently or switch resource policy.

**Joint exit of slices 2–4:** start from the same shared state and limits,
and one fixed finite valid, identity-consistent fact set extending that state.
Prove that all legal causal delivery schedules whose prefixes meet the stated
fit conditions admit that same set and yield the same shared interpretation.
Compose exact publication/canonical rebuild agreement with semantic refinement
and public progress; include the independent semantics' schedule-independence
law wherever that derivation needs it. This concerns delivery of already
authored facts, not changing an author's knowledge before authoring. It excludes
both the retained over-capacity different-subset cases and same-ID conflicting
histories. Bounded schedule tests do not discharge this universal obligation.

Extend the exit to finite receive traces with neutral attempts by proving a
stuttering reduction: deleting calls returning Missing, Duplicate, invalidity
or another unchanged-state result leaves the same final instance. The remaining
Added subsequence is a legal causal extension of the initial accepted state.
Agreement with the fixed target set additionally requires coverage: every target
fact not already held must eventually be offered/retried when its prerequisites
are available and the fit conditions hold. Unrelated offers are allowed here
only when they return neutrally; an extra Added fact changes the target set.
Infinite Missing retries need not progress. The library supplies no transport,
automatic retry or fairness guarantee, and a neutral Conflict does not erase
the effect of having accepted its conflicting alternative first.

These four slices, including that joint exit, close the edit-only argument.
They do **not** close the roadmap milestone that includes Undo/Redo/Restore,
or constitute a versioned release by themselves.

## 5. make the established cut usable

After the semantic/progress boundary, evaluate an incremental representation
against that boundary. The [derived-node cache experiment](derived-node-cache.md)
supplies evidence and explicit adoption gates, not enabled library code. Prove
causal locality, exact cache validity from construction, preservation, assembly
and **all-return** refinement. A reachable-state/cache-valid theorem is a new
claim with a changed domain; it cannot silently replace the current theorem
over arbitrary private states. Account for added memory and the public fact
view before selecting a storage layout.

**Acceptance:** an external native caller uses the crate without private model
internals, authors and exchanges varied histories, and sees the same results
and projected states on success, duplicate, empty and error paths. Differential
checks remain paired with implementation-linked refinement. Measure public-call
latency and retained memory at declared workload sizes, including deletion and
cold reconstruction. The experiment's roughly 25 ms observations are neither a
promised bound nor acceptance for this new implementation. Do not rerun the
old storage-sort experiment as a substitute: replay dominated its measurements.

## history and eventual release

The larger [roadmap](../ROADMAP.md) remains in force. Rust history work needs its
own jointly transactional edit/Undo/Redo/Restore cut and implementation-linked
argument. Retain skipped actions and frozen observed masks are approved.
New-work redo and exact public IDs remain decisions; register behavior,
grouping/children and general anchor behavior must not be inferred from those
approvals. Resolve only the choices the next history slice actually needs.
No transport, codec, checkpoint, Carbon integration or parked Dark/Loro work is
opened by this plan. Merging PR18 does not remove those eventual requirements.

## how to carry each slice

Lynn owns construction and implementation-linked proofs; Ren owns behavior and
scope choices. Keep one reviewable semantic slice at a time, with a public
contract delta, actual Rust/extraction binding, positive proof, relevant native
and semantic controls, scoped review and exact-head ARM acceptance. Consult the
whole candidate's limits as well as the local delta. Report a usable result or
a retained counterexample, not just another helper lemma.

Section 0 is now the prerequisite reform. Preserve theorem strength throughout
it and the later semantic slices. Keep compiler
60 s and query rlimit 100 unchanged; the graph-derived aggregate driver is a
separate guard. Split a genuinely overgrown compilation unit before publishing
another timed-out head, and never count resource exhaustion as detection.
No complete matrix or browser rerun is needed for this documentation plan.

**Immediate next action:** section 0: settle the boundary-normalization policy,
map current caller needs, and carry the counter contract/pattern slice through
its actual public wiring and controls. No further causal/scheduler work first.
