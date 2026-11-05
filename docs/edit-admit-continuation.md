# after the experimental edit/admit merge

PR18 merged the experimental Rust candidate at `f86cc7f`, retaining reviewed
head `4e0f55d` unchanged. That head passed the complete native/proofs,
reference and questionnaire checks on ARM. This is a development baseline,
not the verified edit-only exit, the history milestone or a release.

The next goal is to connect **what an admitted edit means** to the actual Rust
transition, and show that valid inputs in the supported domain can be admitted.
Keep the replay implementation while closing those obligations. Performance
work should then preserve an established meaning, rather than define it by
agreement with an unproved implementation.

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

Build source-function contracts and reuse loop invariant rules where they
remove repeated implementation reasoning. Prefer explicit lemma composition
or deliberate triggers over reopening every implementation downstream. Proof
style must not block correctness work or change theorem strength. Keep compiler
60 s and query rlimit 100 unchanged; the graph-derived aggregate driver is a
separate guard. Split a genuinely overgrown compilation unit before publishing
another timed-out head, and never count resource exhaustion as detection.
No complete matrix or browser rerun is needed for this documentation plan.

**Immediate next action:** slice 1, reachable causal acyclicity, beginning with
the exact invariant and its constructor/receive/edit composition. If its
representation reveals a counterexample, resolve that before using a DAG as a
premise for slice 2.
