# toward a usable Nickel library

**Status: proposed execution plan.** The destination is a Rust crate a caller can
edit, replicate and resume, with proofs about its actual transitions. The Python
experiment helps choose that behavior; extending it is not the release goal.
This roadmap does not approve an ordering algorithm or start implementation.

## the first usable release

The proposed v0.1 profile is one plain-text sequence per document, independent
of Carbon, Dark, workers, storage and transport. A native caller should be able
to:

- insert, delete and replace exact Unicode scalars in atomic multi-edit batches;
- keep stable identities and resolve anchors through edits and restored text;
- group its own actions explicitly, including specified derived-child edits;
- Undo/Redo its own actions and explicitly Restore a selected foreign deletion,
  with inspectable effects and defined blocked/invisible results;
- exchange bounded encoded updates with another replica, admit duplicates
  idempotently and reject invalid/incomplete inputs without partial publication;
- load shared document meaning with a new session, or resume a fenced writer's
  explicit private checkpoint and continue its history;
- update a consumer view from revision-bound change receipts, under documented
  size/history/update budgets and an explicit response when those limits are hit.

A small native consumer must demonstrate those calls using the published crate,
not reach into a test model's internals. Carbon and a possible future Dark
adapter are separate acceptance work. Neither integration, a browser demo nor a
zero-change Loro swap is required to pretend the core works. A Wasm binding is
optional; if shipped, its actual boundary and checked UTF-16 conversions must
also pass. Native support alone must not be described as JavaScript acceptance.

Registers and keyed collections come later. Their semantics can be researched
in parallel, but they must not postpone the first sequence release. Rich text,
general remote selective undo, permissions, distributed identity allocation,
automatic history GC and server/storage/UI implementations are outside this cut.
This does not reopen Dark or the Loro fork.

### an earlier experimental delivery

The first externally usable artifact need not wait for every v0.1 requirement.
Milestone 2 should publish an experimental native crate with a narrow supported
profile, an unstable API and a small external caller. Its supported operations
must compose beyond a canned trace; missing features and incomplete guarantees
must be listed. There is no production-readiness or whole-CRDT verification
claim. The full profile above remains the eventual verified v0.1 target; this
earlier delivery does not quietly remove anchors, children or recovery from it.

## where we are

| available now | what it does not establish |
| --- | --- |
| locked Rust → hax → F* scaffold, authored Latte proofs and wrong-body control | only Boolean-loop properties; no CRDT property |
| restricted identity-set edit/Undo/Restore sessions with frozen masks, creator withdrawal and private checkpoints | no text order, anchors, general session algorithm or public Rust API |
| in-process Restore inspection/confirmation bound to issued selection and full document/private basis | no wire proposal format; restart requires fresh inspection; unrelated changes expire a preview |
| named-author cancellation/reactivation/withdrawal admission checks and semantic mutation tests | consistency of supplied tags, not authentication or complete hostile-input admission |
| anchor explainer and Ren's Xab/Xab clarification | one placement witness, not a general run or replacement rule |

The [private-session profile](docs/private-session-profile.md) and
[preview contract](docs/restore-preview.md) own the running experiment.
[API verification](docs/api-verification.md) and parts of the
[consumer contract](docs/carbon-contract.md) retain older proposed shapes;
they are not an implemented interface. All V1–V9 are still unfulfilled.

## 1. finish the first profile's behavioral contract

**Next deliverable:** a short decision sheet for skipped Undo history, followed
by an ordered reference interpretation and the corresponding API reconciliation.
The source of each expected result must be a stated decision or argument, not
whatever today's implementation happens to return.

Close these dependencies before committing the corresponding engine behavior:

1. **History continuation.** Compare consume/retain when a suppressed deletion
   becomes active again, including its interaction with redo and new work.
   Keep-redo stacking is provisional. Distinguish an empty Undo, an invisible
   applied Undo, a blocked Redo and a rejected call. No automatic selective redo
   follows from retaining skipped items.
2. **Restoration effects.** State whether frozen observed masks remain the
   first profile's rule, including the different outcomes when a concurrent
   deletion arrives before/after the press. Unseen concurrent deletion behavior
   is unapproved. Include peers' undo/redo and later causal deletions. Do not
   quietly turn frozen masks into predicates over future arrivals.
3. **Ordered construction and anchors.** Supply a complete finite-history
   interpretation of gap integration, concurrent runs, ties, hidden endpoints,
   affinity and restoration. Ren wants Xab in both q30/q31 histories, keeping
   restored a beside b. Longer runs and Friday/Monday replacement order are
   still open. Retaining gap information does not force the old placement rule.
4. **Atomic membership.** Specify primary continuation, derived children,
   closure, inactive-trigger rejection and cancellation/redo of outstanding
   derived work. The engine has no clock or job scheduler. Do not silently drop
   the multi-edit/child requirements just to get an easier first engine.
5. **Boundary and budgets.** Choose the first API/profile, rejection results,
   encoding/dependency rules and numeric supported workloads. Distinguish
   document facts from device-local history and writer fencing. Use both the
   Carbon many-document and prospective Dark sustained-editor workloads as
   motivations, not integrated product requirements.

**Exit:** one internally consistent contract for the selected profile, an
executable ordered reference, and a constructive algorithm/correctness argument
covering arbitrary valid histories within its declared domain. Directed traces
and bounded exploration must preserve their failures and limits; passing them
is not that general argument. Reconcile the older API/activity text with the
chosen profile before treating it as an implementation specification.

This is not a demand to settle every future feature first. A Rust slice may
start when its own behavior, errors, abstraction and dependencies are specified
and reviewed. A choice it depends on cannot be hidden as an implementation
detail; independent unresolved features stay outside that slice's claim.

## 2. cross the first real Rust replication boundary

Build the smallest **ordered** two-writer vertical slice of the agreed profile.
Use actual Rust state and operations for creation, editing, delivery and the
selected Undo/Restore continuation. Include independent peer text, duplicate
imports and invisible effects from the start, rather than finishing an engine
whose Undo is deferred as an unspecified extension.

Define the slice's reference state and an explicit Rust-to-reference abstraction
before using a differential check as evidence. For each transition, add its hax
extraction and Latte/F* refinement, well-formedness, targeting and rejection
obligations alongside the code. Name any supporting lemma still missing; don't
label the slice verified by assuming its central reference law. A semantic
mutation must fail the unchanged relevant observation/theorem.

The minimum acceptance harness must include a bounded **history generator**,
not just the chosen vertical trace. Generate both writers' supported edits and
Undo/Restore continuations, delayed/duplicate deliveries and multiple legal
partitions/interleavings. Compare the Rust/reference transition results and
abstract states at each step, including private history/allocator observations
and unchanged-state rejection where those are in scope, rather than only final
strings. Distinguish changing author knowledge before a press from permuting
delivery of one already authored event set. Declare the operation vocabulary,
depth, replica/data bounds and schedule coverage; retain counterexamples.
Generated agreement does not supply a general refinement or convergence proof.

**Exit:** two real Rust instances cross the declared boundaries; the generator
and directed cases pass; source-linked obligations are discharged for the
specified slice; remaining V1–V9 coverage is listed explicitly. An external
native caller uses that supported crate API without test-model internals, and
can exercise histories within the declared subset rather than invoke a
hardcoded replay. Publish the experimental artifact and its limitations at
this point. Full portable codecs, checkpoint recovery and other features may
still be unavailable as explicitly declared; a structured-operation harness
must not be described as encoded-wire or persistence acceptance.

## 3. complete the profile, continuation and recovery

Extend that same implementation to the rest of the selected scope: atomic
multi-edits, explicit grouping/children, own history and Restore inspection,
anchor resolution, receipts, limits and portable encoding/admission. Define the
Rust preview lifetime/revalidation contract; the Python issuance registry is
reference machinery, not a production wire design to copy blindly.

Cross these boundaries with actual calls:

- two peers receive encoded operations in different legal partitions/orders;
- a fresh document loads shared meaning, while a separately fenced session
  resumes its checkpoint and runs the same future commands as the warm session;
- rejected batches/imports leave the document, allocator, history and published
  outputs unchanged; duplicate delivery introduces nothing twice;
- receipt splices reconstruct the actual after-view from the declared before-
  revision, including unchanged text with changed semantic facts;
- limits and malformed/conflicting inputs exercise the actual error paths.

**Exit:** the whole chosen native profile has its implementation-linked
V1–V8 obligations closed, with codecs/parsers, resource claims and external
models explicitly covered or excluded from each theorem. Closure is relative
to the documented profile and named trust base, not all possible CRDTs. Binding
V9 is additionally required if the JavaScript/Wasm interface ships.

## 4. close full-profile usability and cut verified v0.1

Extend the experimental external native consumer through editing, replication,
Undo/Restore, anchors and restart, using only the crate's supported boundary.
Publish the runnable example, API/error documentation, format compatibility
policy and measurements against the declared workload budgets. Include Unicode,
long inactive history, cold import, update growth and incremental-view costs.
Safety proofs do not imply interactive latency or bounded memory by themselves.

**Exit:** that consumer is usable within the stated budgets, the release scope
and proof coverage agree, the locked checks reproduce the shipped sources, and
known unsupported cases reject or are explicitly outside the API. Only then
call this v0.1. Consumer integration and later registers/collections get their
own milestones rather than being smuggled into this exit.

## how we choose the next task

Every research task must either settle a named blocking decision, supply a
missing construction/argument, or refute a candidate. Every implementation task
must close a runnable acceptance slice and its stated proof obligations. An
extra helper, test count or citation is not itself a milestone exit.

If a gate fails, retain the counterexample and say which decision or argument
is missing. Change the plan openly; do not weaken an oracle to keep a date.
There is no defensible release date yet. The next update should name the closed
edge and the remaining path to a usable crate, not just report more experiments.
