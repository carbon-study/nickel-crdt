# prospective API and verification contract

**revision direction:** [the response-led PR plan](response-plan.md) now takes priority over the earlier writer-exclusive activity recommendation. Ren requests restoration of another writer’s deletion and corresponding undo-history adjustment. That behavior still needs a complete trace semantics; the older candidate below is retained for comparison, not adopted.

**Status: unimplemented proposal for review.** This is the library boundary that was missing from the overview. None of the CRDT obligations below is currently verified. The only checked implementation is the separate Boolean loop fixture described in [proofs/README.md](../proofs/README.md).

The [undo analysis](undo-semantics.md) identifies unresolved semantics. In particular, the current activity proposal is not an established implementation of general local undo. The API must not be frozen on that premise.

## 1. the objects a caller manipulates

A `Replica` holds a replicated document and one local history session. The document determines shared text, identities, ordering and activity. The session determines which local item an undo selects, the redo stack and outstanding local grouping tokens. Imports add no foreign items to those stacks.

- `DocumentId` names a replication unit. `WriterId` names one operation allocator, not an account.
- `OperationId`, `CommandId` and `ElementId` are distinct opaque identities. Equal payload does not imply equal identity.
- `Version` summarizes admitted causal operations, including invisible activity events.
- `ViewRevision` identifies a particular local admitted basis. It is not a cross-replica version vector, a UI selection epoch or a durable acknowledgement.
- `ScalarPos` and `ScalarRange` are checked coordinates. JavaScript UTF-16 conversion is a separate checked binding operation.
- `Gap` and `Anchor` retain historical identity/order and affinity. `Selection` identifies a specific set of elements, rather than a range that can expand after replication.
- `Snapshot` encodes replicated semantics. `Checkpoint` additionally encodes the specified local session and allocator continuation. Neither object writes itself to disk.

The first profile has one plain-text sequence per document. No public representation or wire layout for these types has been chosen. Domain checks, range checks and format/profile checks are part of admission, not obligations discharged merely by giving a host value an opaque type name.

## 2. proposed operation shapes

The following is typed pseudocode, **not a compilable or implemented Rust module**. All fallible mutations return `Result`; errors have the neutrality contract in §3. Names replace the overview's earlier illustrative list if this proposal is accepted.

```text
Replica.create(DocumentId, fresh WriterId, Limits) -> Replica
Replica.load(Snapshot, fresh WriterId, Limits) -> Result<Replica, LoadError>
Replica.resume(Checkpoint, Limits) -> Result<Replica, LoadError>

view(&Replica) -> View { revision: ViewRevision, text: Scalars }
version(&Replica) -> Version
anchor(&Replica, ViewRevision, ScalarPos, Affinity) -> Result<Anchor, QueryError>
gap(&Replica, ViewRevision, ScalarPos, Affinity) -> Result<Gap, QueryError>
resolve(&Replica, Anchor) -> Result<ScalarPos, QueryError>

prepare(&Replica, ViewRevision, BatchSteps) -> Result<PreparedBatch, EditError>
apply(&mut Replica, PreparedBatch, Grouping) -> Result<ApplyResult, EditError>
close_primary(&mut Replica, ItemToken) -> Result<(), TokenError>
close_children(&mut Replica, TriggerToken) -> Result<(), TokenError>
undo(&mut Replica) -> Result<HistoryResult, HistoryError>
redo(&mut Replica) -> Result<HistoryResult, HistoryError>
clear_history(&mut Replica) -> Result<(), HistoryError>

export_since(&Replica, Version, ExportBudget) -> Result<ExportPage, ExportError>
import_complete(&mut Replica, EncodedBatch) -> Result<Imported, ImportError>
snapshot(&Replica) -> Result<Snapshot, EncodeError>
checkpoint(&Replica) -> Result<Checkpoint, EncodeError>
```

`BatchSteps` describes a finite sequence of inserts, removals and replacements. Positional steps address successive scratch views. An explicit stable-gap insertion retains the supplied gap's historical meaning instead of converting it to a nearest visible neighbor. Preparation resolves each deletion's exact element targets and reserves only tentative identities. A prepared value is scoped to the document, writer/session and original revision; applying it after another semantic commit rejects. Successful admission, not preparation, advances the published allocator. The precise temporary-ID representation remains an implementation choice.

Preparation is optimistic, with no progress guarantee across intervening commits. The caller should serialize a bounded prepare/apply pair with imports on the same replica: finish admission before processing the next queued import. This is an ownership/scheduling obligation, not a Nickel worker or event-loop requirement. If the caller releases that ownership between calls, it must handle stale-basis rejection; continuously retrying under remote traffic may starve. No automatic rebase is proposed. A future combined operation could remove this gap, but is not part of this API. V2/V3 describe safety, not starvation freedom.

`Grouping` is proposed as `NewPrimary`, `ContinuePrimary(ItemToken)` or `ChildOf(TriggerToken)`. Continuing a primary requires the most recent active local item whose primary continuation is still open. It cannot annex an intervening primary item. Children can join an earlier active retained item whose child admission is open. Closing primary continuation need not close its asynchronous children. This is the missing operation-level distinction between coalescing primary work and explicit derived membership. No timer runs inside Nickel. Whether imports cause a caller to close continuation is caller policy.

An empty batch is `NoChange`, not a new history item. Any admitted primary edit, including a continued primary, clears redo. An admitted child does not. A stale/foreign/closed/inactive token rejects before changing anything. `clear_history` closes local tokens and empties local stacks without changing replicated activity.

`ApplyResult` is `NoChange` or `Applied`; `NoChange` leaves the complete published state unchanged. `Applied`/`Imported` expose the resulting semantic version, an exportable update if one was created, and a `ChangeReceipt`. A new primary also returns its local item/trigger tokens. `HistoryResult` is `Empty` or `Applied { item, visible_changed, update, receipt }`. The proposed invisible undo returns the latter with `visible_changed=false`; its redo remains selectable. This is an unapproved semantic policy, not just an error-handling convention.

For that proposal, an applied history result should also expose a bounded diagnostic: `VisibilityEffect = Changed | Unchanged { explanation: NotClassified | Evidence(...) }`. Evidence must describe facts established by this transition, such as identities still hidden by an active remover; it must not guess another writer's intent. Multiple causes may coexist. `NotClassified` is valid and preferable to a false single-cause explanation. The item identity, consumed-item result, version/update and visible-change flag remain authoritative even when no more specific diagnosis is available. Exact evidence fields and their proof obligations remain open. The host can always say “undid this item; the visible text did not change,” and may add a specific explanation only when supported.

An `ExportPage` has explicit dependency/completeness information and a continuation. It cannot split an atomic command in a way that allows the receiver to publish a prefix as a complete transaction. Export budget exhaustion is an explicit result; it does not silently omit required activity or identity facts. Missing import dependencies return `NeedDependencies` without retaining a hidden pending queue.

`load` creates a new local session with empty stacks; `resume` restores the encoded one. The caller must ensure a resumed writer has no other live copy. Structural conflict detection cannot authenticate writers or prevent two unfenced copies from generating conflicting IDs.

## 3. preconditions and outcomes

For a live replica, let `S` include the complete logical document, allocator, local stacks, token state and returned/publication-visible outputs. Its implementation may have derived caches, but those cannot be additional semantic input.

| call | admitted precondition | successful postcondition | ordinary error |
| --- | --- | --- | --- |
| queries/preparation | well-formed S; supplied basis/domain/ranges checked | no published state change; returned identity/coordinate has its declared meaning | S unchanged |
| apply | prepared basis still current; grouping admission and limits valid | one atomic semantic transition with exact prepared targets/membership; corresponding stack and receipt transition | S unchanged, no counter/token consumption or update publication |
| undo/redo | valid local session and a selectable top item, or empty stack | exactly one selected item toggled under the eventual agreed semantics; no skipping invisible items | S unchanged; Empty also leaves S unchanged |
| import | compatible, bounded, causally complete operations; consistent identities and activity authority | all valid new operations admitted atomically; duplicate facts idempotent; no foreign stack entry or redo clearing | entire call rejected; no prefix publication |
| encode/decode | representable compatible profile and budget | faithful encoded state / validated reconstructed state | no partial live document or session returned |

These are intended postconditions for normal return. They do not cover process death, abort/OOM, arbitrary unsafe memory corruption or a Rust/Wasm trap. A caller cannot infer persistence or delivery from an in-memory success. The design must return notification data after commit rather than execute arbitrary callbacks inside mutation.

Resource limits are inputs to admission. Tests must compare rejection against *the entire logical S*, including allocator/stacks/tokens, not just the visible text. Whether the implementation uses staging, rollback or persistent data structures must be justified by proofs of its actual return paths.

## 4. prospective verifier obligations

Here `WF` is a fully defined well-formedness predicate, `step` the extracted implementation transition, `Ref` the agreed abstract transition, `abs` the implementation-to-reference abstraction, and `view` the visible sequence. These definitions are **not yet present**. A theorem cannot hide the engine's hard part in an assumed `Ref` law.

| ID | intended statement | current status |
| --- | --- | --- |
| V1 — transition refinement | for every WF admitted input and successful actual transition, `abs(step(S,x)) = Ref(abs(S),x)` and WF is preserved | no implementation or theorem |
| V2 — rejection neutrality | every ordinary Err path preserves S, including history/allocator/tokens and publication outputs | no implementation or theorem |
| V3 — identity and targeting | successful allocation is fresh under the single-writer premise; removals target exactly prepared IDs; grouping never absorbs an unrelated command | no implementation or theorem |
| V4 — delivery independence | any two legal causal schedules for the same valid operation set yield equivalent semantic documents and all future observations; delivery partition and derived caches do not change meaning | reference ordering/activity semantics missing |
| V5 — history selection/effect | undo/redo selects exactly one eligible local item and implements its agreed abstract effect, including invisible cases, children and redo continuation | semantic choice and general sequence algorithm missing |
| V6 — anchors/order | gap creation, integration, resolution and restoration refine a complete ordering/affinity specification, including hidden endpoints | complete specification missing |
| V7 — receipt correspondence | folding a successful receipt's declared splices over its before-view equals its actual after-view; wrong-basis application rejects | no implementation or theorem |
| V8 — encoding/recovery | decoding an encoded snapshot preserves the semantic abstraction; checkpoint recovery also preserves local continuation; validated imports cannot create malformed internal state | codec/profile missing |
| V9 — checked coordinate conversion | valid scalar/UTF-16 endpoints round-trip as declared; invalid endpoints reject before mutation | binding missing |

V4 does not require identical local stacks on replicas with different local sessions. It requires identical document semantics, and corresponding future results for the *same* restored local session and commands. It assumes legitimate unique-writer histories with the selected profile and complete dependencies. Merely rejecting conflicting copies of an ID does not provide Byzantine convergence when peers first see different equivocating histories.

For undo/redo neutrality, define the observed state and permitted intervening events. A matched cycle with no new edits/imports/children should restore text and logical ordering/anchor observations; it need not restore the operation log or Version. That target is not unrestricted cancellation against every future operation. See the conditional reasoning and gaps in [the undo analysis](undo-semantics.md).

### what “verified” would mean here

Rust entry points must be extracted from the shipped core and connected to the exact theorem statements above. Helper proofs over a rewritten algorithm, external engine assumptions or a predicate that already asserts the desired result would not establish V1–V9. Failure and unsupported-input branches belong in the extracted proof scope.

F* checking is conditional on its trusted core/solver and the external Rust models. Rust compilation and hax translation remain trust boundaries. Latte is currently a private regeneration dependency; public checks verify committed F* views. Bindings, codecs and their parsers need explicit coverage; leaving them outside extraction must be declared, not silently included in an engine theorem. Own admissions are forbidden. None of this establishes physical UI behavior, disk durability, authentication, wall-clock latency or a memory bound absent a separate argument.

## 5. existing evidence and the stop gate

The current `flip_bridge`, `flip_exact` and `flip_involution` statements check one extracted Boolean loop with LoopUtil. The wrong-loop mutation fails its unchanged bridge theorem. Those results demonstrate the proof pipeline, not any V1–V9 property. No theorem in the current tree mentions sequence state, undo, anchors, import or checkpoints.

Before treating undo as an adopted API, I need a reviewed reference semantics and a complete finite-history algorithm with a source-linked correctness argument. It must distinguish local selection from effect semantics, handle ordering through inactive history, and replay the agreed two-writer/late-child/cold-recovery continuations. Finite witnesses can refute an algorithm; passing them does not substitute for the general argument. Until those exist, this document is a proposed verification contract and the core has no advertised verified undo implementation.
