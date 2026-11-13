# Shared causal events before a second CRDT kind (proposal)

**Status: docs-only proposal, not an implementation plan or adopted API.**
Inventory baseline: main `65e35df` (including the writer-identity and
representation-boundary proposals). PR88's reviewed operation-provenance
continuation is separate from this baseline. No Rust, proofs, generated views,
pins, gates or limits change here. Registers/collections remain contract work;
this document does not declare their construction adopted or complete.

## 1. The operation we need to express

Carbon's concrete motivating action is “create a card with prompt and answer.”
It should publish one document change containing entry creation and both field
writes, or publish none of them. The same document may eventually hold a text
field as well. This is about **document-local atomic commits**, not transactions
between referenced documents, plugin ownership, transport delivery or durable
storage. Carbon's stable document identity and replacement-plugin requirements
remain application contracts, not peer or CRDT identity formats.

The candidate is a shared event envelope and admission boundary, with each
CRDT supplying its operation meaning. Text is the first client, not the model
that defines every payload. A register changes one value; a collection manages
entry identity/lifetime; text determines scalar identities and placements.
Lists require their own selected contract: replacing Unicode scalars with
values alone does not decide mutable entries or move semantics.

**Recommendation for discussion:** specify this boundary before implementing a
second native kind. Do not copy the present text-specific `Replica` into a
register engine and later assert the two envelopes are equivalent. Also do not
hold every semantic result hostage to a large generic rewrite: preserve today's
checked text implementation and bridge each new interface back to it.

## 2. Inventory: what could generalize, and what is proved today

“Shared candidate” below means an inspected dependency on IDs/edges or storage,
not an already checked theorem over arbitrary payloads. All current native
families still quantify the concrete `Nickel_crdt.Edit` types. Transparent
`Fact`, the two-constructor `Writer`, imports and extracted bodies remain in
scope even where authored code never examines text fields. A name fence or
keyword count does not establish parametricity.

### Rust surface (`src/edit.rs`)

| current items | proposed responsibility | work at the boundary |
|---|---|---|
| `Writer`, `writer_index`, `EventId`, `event_lt` | shared producer/event identity and deterministic storage ordering | discharge [writer identity](writer-identity.md) laws and allocation assumptions; ID order is not causal order |
| `Fact`, `fact_equal`, `clone_selected_fact` | split envelope from payload; preserve whole offered event | equality must compare ID, dependencies **and the entire payload**, not only an envelope hash or visible effect |
| `has_event`, `has_fact`, `duplicate_events`, `frontier`, `validate_after`, `extend_past`, `past_pass`, `past` | shared membership, causal edges, past and roots | parameterize fact access; retain closed/present/unique-root premises and ordinary failures |
| `choose_unseen`, `canonical_step`, `canonical` | shared canonical whole-event storage | exact payload clone, ordering, uniqueness, totality and permutation agreement must all transfer |
| `ready`, `choose_ready` | shared causal scheduling | only IDs/edges are inspected; retain least eligible storage index and progress premises |
| `interpret_scheduled` | mixed driver | choice/done bookkeeping is shared; `Tree`, node groups and `interpret_event` are text-specific state/effects |
| `Replica::duplicate` | shared duplicate/conflict classification | equal ID with different payload remains conflict, including an operation targeting a different container |
| `Replica::validate_new` | **mixed**, not a generic validator today | dependency duplicates/presence and producer predecessor rules separate from scalar/delete/gap checks; artificial resource ceilings have moved to caller harnesses |
| `Replica::plan`, `receive`, `edit`, `with_counter`, `next_counter_after` | mixed transactional publication and producer shell | current `plan` calls text validation/rebuild; current `edit` binds a text request. Preserve all-return state/counter laws through a new payload adapter |
| `push<T>`, checked arithmetic | reusable implementation support | mathematical and native overflow/capacity contracts still required |
| `BirthId`, `Side`, `Node`, `Tree` methods, `birth_lt` | text client | derive scalar occurrence identity, retained traversal and FugueMax placement; do not put a text tree in the shared log |
| `validate_scalars`, `duplicate_births`, `has_birth`, `deletes`, `visible` | text client | scalar validity, text target/visibility rules |
| `select_basis`, `event_basis` | shared-candidate whole-event selection plus client composition | selecting whole facts by chosen IDs is generic in substance; author text reconstruction is not |
| `replay_nodes`, `replay_author`, `author_context`, `interpret_event`, `interpret` | text client and its driver adapter | actual `Tree.add` replay is not independent text meaning; keep author-basis discipline and receiver-extra-history obligations |
| `Invalid`, `Capacity`, `Error`, `Admission`, `Local`, `Replica` | split shared shell from client results/state | preserve semantic outcomes through adapters; Limits and artificial policy errors were explicitly removed by the policy-budget migration, while identity/integer bounds remain |

### Proof families

Links name actual source families and representative contracts, not promised
verbatim reuse. The inventory deliberately splits mixed modules rather than
assigning a whole file to “generic.”

| family | present guarantee / representative names | candidate transfer |
|---|---|---|
| [LoopUtil](../proofs/LoopUtil.lt), [Vector](../proofs/Vector.lt) | type-parameterized loop/Result rules, exact vector/slice equations | already generic infrastructure; instantiation and new native callers still need checks |
| [Prelude](../proofs/Prelude.lt), [Smoke](../proofs/Smoke.lt) | aliases and separate Boolean extraction fixture | infrastructure, not CRDT semantics |
| [EditIdentity](../proofs/EditIdentity.lt) | `fact_equality_exact`, `duplicate_matches_lookup`, known-ID classification | shared after payload equality is exact and peer laws replace two-writer dependence; birth equality stays text-local |
| [EditAtomic](../proofs/EditAtomic.lt) | `receive_rejection_unchanged`, `edit_rejection_or_empty_unchanged`, counter calculation/publication | transactional shell pattern transfers only with exact generic planner/authoring equations; text Empty policy stays the adapter's contract |
| [EditAccepted](../proofs/EditAccepted.lt) | unique IDs, exact whole-fact extension, canonical ordering/permutation/totality | substantial storage candidate; `event_key` needs peer-order repair. `plan_publishes_interpretation` and exact tree agreement remain current-backend laws, not generic semantics |
| [EditWellFormed](../proofs/EditWellFormed.lt) | scalar validity **and** direct-dependency presence/closure/whole-fact containment | split scalar rules from `dependency_validation_is_sound`, `exact_extension_preserves_causal_closure` and their public compositions |
| [EditCausal](../proofs/EditCausal.lt) | ghost `causal_rank`, rank extension and public preservation | graph candidate after abstract envelope access and checked admission composition; rank is not replicated metadata or event-ID order |
| [EditPast](../proofs/EditPast.lt) | membership, sound closure and exact ancestry work | graph candidate with actual scan contracts retained at R; no inference about payload interpretation |
| [EditPastTotal](../proofs/EditPastTotal.lt) | `scanned_roots_compute_exact_past`, `two_closed_receivers_select_same_past` | total/exact selection over closed histories with present distinct roots; two receivers select equal IDs, not equal client states |
| [EditBasis](../proofs/EditBasis.lt) | `actual_basis_is_exact_filter`, `closed_event_basis_is_exact` | whole-event selection candidate; preserve selected occurrence order/content, not merely membership of IDs |
| [EditSchedule](../proofs/EditSchedule.lt) | `scheduler_choice_is_exact`, `ranked_incomplete_scan_progress`, successful once-only causal trace, exact-past cut | graph/driver split. Progress of ready choice does not prove payload success. `event_work_prefix` and error-origin replay mention actual text state and node groups |
| [EditReplay](../proofs/EditReplay.lt) | `actual_nodes_replay_in_order`, `actual_author_replays_selected_groups`, `closed_author_context_is_exact` | text backend-local proofs through actual `Tree.add`; not a generic operation interpreter or independent placement semantics |
| [EditCommit](../proofs/EditCommit.lt) | private-state preservation, `authored_fact_binds_request`, same-history author/admit composition | shell laws can be generalized; request equality and setter/rebuild links require the text adapter |
| [Spec](../proofs/Spec.lt) | composed existing public guarantees | retain the current text surface; add a shared surface and client refinement rather than rename `edit(gap, insert, delete)` to an unconstrained callback |

Reproducible size context: `wc -l proofs/*.lt` at the baseline is **5,999 lines
in 16 files**, including comments, infrastructure and Smoke. That is not a proof
reuse percentage or effort estimate. The proposed “4,000 generic lines” does not
account for mixed modules, transparent concrete types or new client obligations.
In particular, much of EditSchedule is graph reasoning despite its text driver.

## 3. Candidate shape: one event, an ordered operation batch

Illustrative types, **not code accepted by the current extractor**:

```text
Event<P> = { id: EventId, after: sequence<EventId>, payload: P }
DocumentBatch = sequence<TargetedOperation>
TargetedOperation = { target: ContainerId, operation: KindOperation }
```

The log is parameterized over `P`; a mixed document uses `P = DocumentBatch`.
Container identity must be stable and distinct from plugin identity. Operations
are an ordered batch, not a set: repetitions and intra-batch order may matter.
Event equality includes that order. Validation and interpretation must consume
that same stored order: neither may sort or regroup operations by kind. The
batch shares one causal basis, one
producer allocation and one externally visible commit. This is not permission
to collapse separate user actions or group their future Undo histories.

Candidate local semantics: start from the event's causal-basis document state,
then evaluate its operations in order on a private working state. Thus an
`InsertRecord` may produce an entry that subsequent `SetField` operations in
that batch target. Define references to those newly created IDs, and whether
later operations see earlier ones, before implementation. A possible stable
sub-operation identity is `(event ID, ordinal)`; this is an **open representation
choice**, not a change to current `BirthId { event, index }`.

The compatibility adapter for today's API is explicitly restricted to **at most
one text operation per event**, encoded as one payload operation. Only in that
restricted adapter does today's `BirthId { event, index }` retain its meaning
unchanged. Keep its pre-edit gap/delete semantics and birth IDs under an
explicit embedding.

A general batch with two text operations cannot independently number both from
index zero: even distinct containers would produce two births `{event, 0}`.
Before supporting that case, choose a collision-free identity/targeting scheme:
container-qualified occurrences (which must also distinguish repeated operations
on the same container), batch-global birth numbering, or an operation ordinal
such as `(event, ordinal, scalar-index)`. Every text delete/anchor target must
resolve an unambiguous occurrence in its intended container. Prove how old
single-text histories embed and how new occurrences remain distinct, including
two text operations on the **same** container. No scheme is selected here.
Flattening insert scalars into generic operations without that mapping would
silently change targeting and grouping.

A document interpreter dispatches each target operation to its kind. It owes
cross-kind noninterference/composition laws as well as per-kind laws; two
operations touching the same entry cannot be assumed independent. Register
and collection contracts are not replaced by a universal “apply” callback.
The operation set and container creation/type rules remain decisions. In
particular, shallow records do not remove creation/removal/recreation races.

## 4. Atomicity: validate, compute and publish the complete batch

Candidate admission pipeline:

1. Classify duplicate/conflicting **whole events** and validate the envelope,
   including causal references and producer constraints.
2. Obtain the exact author basis and validate the entire payload, including
   references created earlier in the batch and all relevant resource bounds.
3. Compute the complete candidate log and derived document state privately.
   Interpret affected history using checked client semantics, not merely the
   receiver's concurrent display.
4. Publish the candidate log and all derived state together only on success.
   On error retain the entire before-state, including counters and all fields.
   A local no-op allocates no event according to a specified client policy.

One event containing several operations is **not** itself an atomicity proof.
A failed third operation must not leave the first two installed. A reader or
subscription must see the before or after snapshot, not a half-created card.
The engine's in-memory publication proof does not establish browser persistence,
crash durability or cross-document atomicity. Carbon's adapter must compose
its persistence and notification boundary separately.

Application/transport workload budgets may bound envelope and batch encodings,
objects, intermediate author states or derived storage. These budgets are outside
the engine; births and ordering_links are no longer engine policy checks. Actual
integer/identity bounds and independent semantic fitting, termination and client
refinement obligations remain. Shared publication alone supplies none of those
arguments; see [policy budgets](policy-budgets.md).

### Unsupported data formats are not unknown engine operations

Carbon's newer **value-format** case can still be a known register operation:
in this candidate, Nickel stores an atomic tagged byte value and computes the register winner
without interpreting the application's format family/version. Carbon preserves
the raw value and locks its incompatible editor; other supported fields can
remain editable. This requires an opaque **register value**, not necessarily
an unknown CRDT operation or an uninterpreted event. The stored tag must identify
the format family as well as its version, independently of the handler plugin.

An actually unknown **operation kind** is different: the engine may not know
its targets, effects, invariants or effect on later validation. Rejecting or
deferring event counter `c` also prevents admission of `c+1` under the current
producer-chain rule, and blocks other peers' causal descendants. This is a
transitive causal stall, not an isolated locked field. Such rejection cannot be
advertised as Carbon's “newer field locked, other fields editable” behavior.

If mixed engine versions must accept such events and continue their graph
history, the design needs separate envelope retention/structural admission and
semantic application states (with explicit frontiers/status), plus a proof of
which later operations and observations remain safe. Storing an unknown event
does not certify its payload validity or application, and receiving a descendant
does not make that descendant interpretable. Do not partially apply the known
operations of one atomic batch or expose guessed/default state for its unknown
effects. This can lock dependent state until interpretation becomes available.

Two policies remain to decide: restrict participating engine versions to a
supported operation vocabulary and expose transitive deferral on mismatch; or
build that separate opaque-event/application protocol. They are **not equally
compatible with uninterrupted mixed-engine-version editing**. Neither protocol
exists today. Offered-input ownership, retry and storage bounds must be explicit;
no existing `Added` result is silently redefined as “stored but unapplied.”

## 5. Proof boundary over arbitrary payloads

The proposed shared specification quantifies a payload type `P` with exact
equality, an event projection `(id, after)`, and a full-event storage relation.
No Unicode, gap, `Tree`, `Node` or plugin names occur in its graph theorems.
The shared mathematical interface should expose:

- unique event identities and exact payload/dependency preservation;
- duplicate vs same-ID/different-content conflict classification;
- dependency closure, acyclicity/rank and exact transitive past;
- canonical whole-event storage independent of input permutation, under the
  existing corresponding uniqueness/content premises;
- once-only causal schedule and conditional graph scan progress;
- transactional state/counter publication and private-state preservation,
  composed with explicit client planner obligations.

These are **conditional universal contracts**, not new trusted axioms. Prove
them parametrically where possible, prove each concrete instance, and prove the
actual Rust/extraction bridge. If the current Rust/hax/F* path cannot express
one parametric native implementation, alternatives are a generic specification
with separately proved concrete adapters or a closed operation enum with a
checked projection. The latter is not a proof over arbitrary payloads merely
because its code avoids matching enum constructors. Toolchain feasibility and
implicit context isolation must be demonstrated before selecting a path.

Each client supplies checked obligations for: payload validity in the named
basis; exact local request encoding; deterministic interpretation, including
errors; invariant establishment/preservation; all-return refinement to its own
independent meaning; fitting-domain progress; and the composition/locality or
schedule-independence facts its convergence argument needs. A shared graph
order does **not** prove client convergence. Receiver-independent validity,
subset replay equality and text placement remain substantive missing work;
they cannot be assumed in order to advertise a generic completed CRDT.

Follow [the representation boundary](representation-boundary.md): abstract
client state includes hidden data and future-targeting information. Its bridge
may mention concrete states. A text event-work proof tied to actual `Tree.add`
is a useful backend law, not that independent meaning.

### Which statements should survive a new loop or backend?

Keep implementation-local scan/push/fold equations as R proofs. Add semantic
interface statements for exact closure, full-event publication, causal trace
and client state transitions. For example:

- preserve `ranked_incomplete_scan_progress` as the present `choose_ready`
  bridge; expose eligible-event existence from rank/closure/uniqueness without
  making a particular scan part of the shared graph specification;
- preserve `plan_publishes_interpretation` exactly for today's backend; expose
  transactional publication plus client refinement separately, not a weaker
  replacement for the accepted equality;
- abstract successful scheduler trace from `schedule_state`'s concrete
  `(done, operations, Tree)` tuple, while retaining exact current replay/error
  witnesses and their initialization/choice/helper-output correlation;
- retain the exact filter's whole-event content/order obligation in the basis
  interface. Equal selected ID sets alone are insufficient.

Do not replace all-return theorems over arbitrary current states with only
reachable-state results without an explicit domain decision and preserved old
adapter theorem. Do not weaken a failed statement to make generic extraction
pass. No new admissions, pin changes or raised proof limits are proposed.

## 6. Relation to PR90: one boundary design, separate implementation cuts

PR90 was a **merged proposal**, not a landed arbitrary-peer implementation.
It leaves representation, allocation/recovery and abstract peer-law choices
open. This proposal shares its EventId/equality/order surface.

Recommendation: agree the peer/envelope laws together, but do **not** combine
peer representation, payload generalization, batching and client semantics in
one implementation PR. First establish the chosen peer-law interface and port
its concrete producer representation with the explicit Alice/Bo embedding;
then generalize the envelope against that interface. An alternative order is
acceptable if the first cut keeps a checked adapter to current IDs and does
not proliferate new two-writer case splits. Allocation/restart/fork non-reuse
is separate from either type refactor.

Separate cuts make solver/extraction changes and semantic faults attributable.
Changing Writer affects comparisons and mathematical keys; changing Fact
changes whole-event equality, validator composition and many extracted callers.
A single large diff saves an intermediate mechanical port but combines both
failure surfaces. Do not promise unchanged placement merely because both are
called identity refactors. Preserve writer-first ordering under PR90's explicit
embedding, and preserve per-text-birth identities under the payload embedding.

## 7. Work and cost: no reuse percentage or calendar promise

The inspected baseline identifies the following work packages:

| package | expected relative work | concrete exit / reason |
|---|---|---|
| envelope/peer specification and adapter equations | bounded design, high leverage | exact duplicate/content and old-text-ID embeddings; decisions below settled |
| pure graph/store parametric laws | medium, many statements but limited payload semantics | actual exact-past, uniqueness, canonical and scheduling instances rechecked, not just mathematical rewrites |
| split public validation/commit composition | high integration risk | current universal public laws retained, payload validators and whole-state publication linked |
| native extraction and control migration | cross-cutting, unavoidable | fresh pinned hax/view/receipt identity, every affected mutation resolves in its intended function and rejects at its stated owner |
| mixed-document atomicity and client composition | new proof work, not a restatement | multi-field success/error and same-key lifetime traces through real API |
| independent text/register/collection meaning and progress | substantive remaining semantic work | client-specific refinement/convergence/fit gates, not credited to generic graph lemmas |

These are qualitative estimates from the dependency inventory, not measurements
of an implemented generic prototype. Even the mostly graph modules import
concrete types; arithmetic keys, native signatures, clone/equality calls and
proof triggers may change. Existing extraction snapshots and mutation anchors
must be revalidated, with ordinary named owning failures and unchanged limits.
Preserve retained failed experiments rather than counting a resource timeout as
successful fault detection. No local full matrix is useful for this docs PR.

**Why consider it now?** There is one native client and an existing source-bound
contract suite to preserve. If registers copy its shell first, later separation
must reconcile at least two implementations, public APIs and control suites.
That is an avoidable multiplication of interfaces, not proof that total effort
must be lower now: premature genericity can cost more if the second client's
requirements are guessed. Before selecting the implementation, use the
create-card mixed-batch scenario and a register-only client to test the proposed
boundary. These are future acceptance slices, not permission to implement now.

## 8. Proposed acceptance and decisions

Future acceptance should include:

1. Current text histories ported through the adapter, preserving exact offered
   facts/IDs, public outcomes and all existing theorem strength.
2. A non-text payload whose graph operations cannot inspect text data. Same-ID
   unequal payload and different target/container controls must reject.
3. One document batch creating a record and two fields. Failure of the final
   operation, unsupported kind and capacity exhaustion leave everything
   unchanged; deleting the rollback/publication barrier must fail controls.
4. Two receivers with extra concurrent history, operation-order/repetition
   witnesses and same-key creation/remove/field-edit continuations. Each result
   needs its own independent oracle; agreement of two wrong receivers is not
   sufficient.
5. Arbitrary-peer obligations and three-plus/sparse/high-ID cases from PR90;
   scalar/birth targeting compatibility from the restricted text embedding; fresh
   extraction plus affected semantic/dependency controls before landing.
6. Two text operations in one event, including on the same container: the
   selected identity scheme must distinguish their births and delete targets;
   the restricted compatibility adapter must refuse an unsupported second text
   operation rather than alias it.
7. A known register write with an unknown application format must retain its
   exact bytes without freezing unrelated supported fields. Separately test an
   unknown engine operation followed by the same producer's next event and a
   different peer's descendant: expose the causal stall or selected
   stored/unapplied statuses, never pretend it is only a field-format lock.

Decisions still needed, **not adopted by this proposal**:

- Generic Rust payloads vs generic mathematical interface with concrete
  adapters; how to demonstrate extraction/verification isolation.
- Which operations/containers the first mixed document supports; same-key and
  record-lifetime policy; intra-batch references and ordering.
- Common vs per-kind error/resource budgets; unknown-kind storage/defer policy;
  local no-op detection and public event/sub-operation identities, including
  multi-text birth identity and unambiguous container targeting.
- Peer representation and producer recovery choice under PR90; exact ordering
  of those implementation cuts; no automatic allocation policy follows here.
- Where this work sits in the revised Nickel milestones. Text-first release
  priority is under revision; this document does not rewrite ROADMAP or issues.

Carbon remains responsible for format/command contracts, handler reassignment,
local storage/sync and replacement-plugin acceptance. A generic event envelope
solves none of those by itself. Runs and incremental text representation remain
post-v0.1; no Dark/Loro work, history implementation or transport is reopened.
