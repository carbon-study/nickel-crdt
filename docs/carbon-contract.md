# proposed Carbon contract

**Review draft, not an adopted API.** This describes the behavior I want Nickel to provide and the order I would build it in. It proposes choices that Dark never settled, especially redo after invisible undo. No engine implements this document yet.

## 1. what Carbon would do with it

A reader has several kinds of changing data. They should not all become editable strings.

| Carbon action | data primitive | proposed priority |
| --- | --- | --- |
| type a note, including edits from another tab or device | plain Unicode sequence with local undo | first engine slice |
| keep a highlight attached while that note changes | stable sequence anchors | first release |
| save a reading location or a font setting | scalar register, with an explicit concurrent-write policy | next primitive |
| add/remove highlights, bookmarks or note records independently | keyed collection with observed removal | after registers |
| store EPUB/PDF bytes and installed plugin artifacts | ordinary blob storage | outside Nickel |
| render pages, interpret EPUB locations or PDF rectangles | format plugin | outside Nickel |

An EPUB locator is not a Nickel text offset. A highlight in an immutable PDF can store the book revision and rectangles as application data; Nickel does not infer those coordinates. A note's text anchors refer to Nickel's own sequence. If a plugin replaces the underlying book revision, it must migrate or invalidate its book locators explicitly.

The first useful client would be a **plain-text note plugin**: edit on the phone, edit offline elsewhere, reconnect, reload, and undo local commands without erasing the other device's contribution. That exercises identity, persistence and sync together. It does not by itself complete Carbon's M3 reading-position/highlight milestone.

Carbon's merged [roadmap](https://github.com/carbon-study/carbon/blob/4195cb1092ecc46b883c4cda8a5ddd5f6639fe26/ROADMAP.md) supplies the product context: plugins own the app; the worker owns shared data; local persistence and server sync are missing. This proposal does not freeze unrelated platform development or choose Carbon's plugin trust model.

## 2. ownership and the boundary to plugins

I propose a pure Rust state machine, a small Wasm binding, and a Carbon worker library plugin. Each browser worker instance owns its replica; frames send typed edit requests through Carbon's eventual frame/worker API. Nickel does not implement that RPC mechanism.

One mutable document has one writer at a time. A command is a finite list of declarative edits, not a callback that can re-enter the engine. A frame includes the view revision it edited; a stale positional request rejects. It can then refresh or deliberately submit an edit using stable anchors. The worker must not silently reinterpret an old index in a newer document.

A replica ID identifies a single operation writer. A restarted writer needs its persisted next counter, or a new replica ID. Two offline devices must not share one counter allocator. A user's account ID is therefore not a replica ID. Carbon owns allocation, durable identity and admission of devices; Nickel checks structural identity conflicts.

Each note is a separate Nickel document initially. Creating, listing and authorizing notes belongs to Carbon. Cross-document atomic edits, nesting documents inside elements, rich-text marks and arbitrary JSON trees are outside the first release.

## 3. elements, gaps and deletion

Text is a sequence of Unicode scalar values. Positions count scalars; the Wasm wrapper offers checked UTF-16 conversion for JavaScript. A UTF-16 endpoint inside a surrogate pair rejects before mutation. Byte, scalar, UTF-16 and grapheme coordinates must have different types. Grapheme-aware movement belongs to the editor.

Each inserted scalar has a stable logical `ElementId`. Editing equal text creates different elements. Undo/redo changes whether the original contribution is active; it does not manufacture a new logical character. Storage can pack runs, but packing must preserve every scalar's identity and target set.

An insertion names a historical gap, not just an integer. A deletion names the elements selected in the author's current view. It must not later expand to delete concurrent insertions that were absent from that selection. Replacing a range combines those two actions in one command. Empty edits create no command.

A gap contains enough retained ordering information to remain meaningful when its visible neighbors disappear. Anchors have explicit affinity: does an insertion exactly at the boundary stay before or after that boundary? Both directions must work. For a range, the start and end have independent affinity, so a plugin can choose whether typing at either edge enlarges the highlight. Hidden anchors remain valid while history is retained; if the sequence becomes empty they resolve to its only visible gap, while retaining their historical identity.

Required ordering behavior:

- all admitted replicas derive the same total order from the same causal operation set, regardless of delivery partition or arrival order;
- insertion into a visible gap appears in that gap in the author's resulting view;
- a command's inserted run preserves its internal order; concurrent runs at the identical gap have a deterministic tie-break and do not alternate their scalars;
- hiding an element does not discard the ordering evidence needed to place later edits or restore it;
- reactivating an insertion restores its original identities and ordering relations, not a nearest-visible-neighbor approximation.

**An ordering algorithm is still a blocking choice.** These laws and examples do not uniquely define every concurrent placement. Before the first sequence implementation is accepted, we need a complete reference interpretation of gap integration, sibling ties and affinity, including three-way concurrent/causal cases. I would compare candidate policies against the witnesses below, then write that interpretation alongside the implementation-linked proof statements. I am not claiming that a pair of neighbor IDs or these English laws alone supplies it.

## 4. command activity, undo and redo

I propose explicit replicated command activity from the beginning. For an element `e`:

```
visible(e) = active(creator(e))
             and no active deletion contribution targets e
```

This separates creation from the deletions targeting it. Logoot-Undo derives a related visibility equation from enabled insertion/deletion patches ([Weiss et al., §6.2, eq. 1](#references)); its §§5.3–5.4 retain overlapping deletions even when they no longer change the display. We borrow that distinction, not its line-identifier allocation or multi-author patch-degree protocol.

Inactive insertions and deletions remain in history as ordering and targeting evidence. This equation defines visibility, not the ordering algorithm. Activity belongs to commands, and undo removes only the selected command's contributions. Causal dependence alone never makes another command part of it.

Commands begin active. Each insertion or deletion contribution belongs to exactly one command; accepted child edits belong to their trigger's command. Only the originating writer changes a command's activity. Its activity changes form a causally chained, monotonically numbered sequence; the latest admitted change for that command wins. Conflicting identities or a forked activity chain reject rather than being resolved by arrival order. An undo and redo are new semantic events with new operation IDs, causal dependencies and sync-visible versions. Duplicate delivery does nothing. A foreign writer cannot structurally toggle someone else's command. Authentication of the writer is Carbon's job, not a property of a numeric ID.

**Proposed no-op policy:** undo consumes exactly one history item, even if no visible character changes. It still publishes the activity change and creates a redo item. Redo likewise consumes exactly one item. Return a result such as `Applied { command, visible_changed, update }`; never collapse semantic success into a Boolean meaning "text changed". An empty stack returns `Empty` and publishes nothing. This deliberately differs from the old Loro no-visible-effect retirement policy. It needs approval, not a compatibility disguise.

Remote imports never enter the local undo stack. They do not clear redo. A successful new primary local command clears local redo; an edit rejection does not. Undo/redo metadata identifies local history items, while replicated activity determines the document's meaning. Clearing a local history list must not reactivate previously undone work.

### which undo semantics this chooses

**Here, undo means origin-selective contribution deactivation.** That is a deliberate policy, not an agreed meaning of “local undo” throughout the literature.

- **Independent peer insertions:** [Yu, André and Ignat, §§3–6](#references) retain operation descriptors across string splitting, but their default transitive ground-dependency policy can hide insertions built on an undone insertion. Nickel instead requires the independent X in witness 1 to survive; only explicit children join a trigger. Their §6 explicitly leaves formal proof outside the paper. The relationship bookkeeping is useful precedent; the default dependency semantics are not our specification.
- **Who may undo:** [Yu, Elvinger and Ignat, §5](#references) distinguish concurrent equivalent undos from causally later redo through equivalence classes and undo lengths; Lemma 6 merges same-origin lengths with max. Nickel's single-writer activity chain avoids concurrent foreign toggles of one command. It does not solve that paper's broader selective-undo problem. Supporting foreign undo later requires a new semantic decision, not just removing an ownership check.
- **Register undo differs:** [Stewen and Kleppmann, §2 and Fig. 1(d)](#references) choose restoration semantics: black → A:red → B:green → A:undo yields black; redo yields green. Merely deactivating A's contribution while preserving B's gives green instead. Their §§4–5 implement restoration with history-referencing RestoreOps, not a Boolean toggle. Nickel must not call its proposed sequence policy their “local undo,” or assume it determines register behavior. Their §7 makes precisely this distinction from counter-based activity approaches.

For the next register primitive, review that black/red/green example explicitly. Preserving a later peer write and restoring the state before one's own write are different product choices. The register row in §1 remains open between them. The papers supply alternatives and separating examples, not evidence that our proposed choice is universally what users want.

An invisible toggle's replicated event and redo entry are Nickel requirements motivated by witnesses 3–5. The cited work establishes useful activity/history representations; none is being cited as a proof of our child protocol, exact stack policy or cold-recovery implementation.

### explicit children and editor grouping

A primary command may acquire explicit derived edits: an auto-pair close, renumbering or composition normalization. A child names its trigger through an opaque token. It never starts an independent undo item, regardless of when it completes. A different edit that merely observed the trigger stays independent.

For the first release, a late child may join only an active, retained, locally owned command with an open child token. If the command was undone, evicted or its token was closed, admission rejects **before** changing anything. The app can cancel the job or request a new primary command; it cannot silently revive an inactive trigger. Accepted child contributions thereafter follow the trigger's activity, including across imports and cold recovery.

The engine has explicit item boundaries. Carbon's editor adapter implements its grouping policy: 500 ms, single-selection primary edits only; Enter, direction changes and multiple selections split. A peer import closes primary coalescing. Explicit children still join their trigger across that boundary. Composition previews/final commits and multi-selection restoration need adapter-level tests; a low-level grouping token is not physical IME acceptance.

The first thin note plugin may send one primary item per committed edit. It must describe that UI honestly; it does not pass the grouped-editor acceptance slice until the grouping adapter is tested.

## 5. proposed functions

Names are illustrative Rust shapes; the semantic distinctions are the contract. Bounds and identifiers are checked opaque types, not freely interchangeable integers.

| operation | result / obligation |
| --- | --- |
| `Document::create(doc_id, replica_id, limits)` | empty document, explicit format/profile and resource limits |
| `Document::load(snapshot, replica_id, limits)` | validate a complete snapshot before publishing a document |
| `text.view()` | text plus an opaque revision for positional requests |
| `text.gap(revision, scalar_pos, affinity)` | stable gap; reject stale revision/out-of-range position |
| `text.anchor(revision, scalar_pos, affinity)` / `resolve(anchor)` | checked historical coordinate / current scalar position; reject wrong document or container |
| `apply_primary(revision, edits)` | atomic command, fresh trigger token and update; positions interpreted sequentially within the batch |
| `append_child(token, revision, edits)` | atomic addition to that trigger, no independent undo item |
| `close_children(token)` | prevent further asynchronous children; existing contributions remain |
| `undo()` / `redo()` | one item or `Empty`; distinguish semantic change from visible change |
| `history.clear()` | discard local undo/redo access and close its tokens, preserve replicated history/activity |
| `version()` / `export_since(version, budget)` | version summary / bounded, dependency-described update chunks or an explicit incompatible/too-old result |
| `import_complete(batch)` | validate/dependency-check whole batch, then atomic semantic admission; duplicates idempotent |
| `snapshot()` | self-contained semantic state, including hidden elements, activity and required causal history |
| `checkpoint()` / `resume(checkpoint)` | snapshot plus local history session, counters, stacks and retained trigger identities |

An edit list contains inserts at checked gaps and removals of checked selections. It cannot supply an invented creation identity, arbitrary restoration relation or a forged child membership declaration. The public decoder validates those declarations against the selected protocol.

There is no general checkout/fork-at-history API in the first release. A clone for a new writer gets a new replica identity and an empty local history session. Resuming the same writer is a different operation: Carbon must fence out its previous instance. Persisted counters alone do not prevent two resumed copies from writing concurrently.

## 6. sync, storage and failures

The engine admits only causally complete batches initially. Missing dependencies return `NeedDependencies`; it retains no hidden unbounded pending queue. An invalid suffix rejects the entire call, not just that suffix. A duplicate operation ID with different content rejects, including when the ID is already known. A complete transaction may be transported in several packets, but the receiver assembles it within an explicit byte budget before calling admission.

Updates carry document ID, format/order profile, operation IDs, dependency/version information, command membership and activity. A cold receiver must reconstruct the same behavior from those bytes without a private sender-side restoration map. Different compatible batching is semantically irrelevant. Incompatible profiles reject; first release has no migration promise.

Version summaries must include activity events even when the text is unchanged. A per-replica prefix vector is a proposed representation, subject to the actual protocol. The server may store opaque encrypted payloads and use an agreed exposed envelope for backfill. Nickel does not implement encryption, signatures, authorization or prove that an envelope describes its ciphertext honestly. Renee's old Loro envelope is prior art, not our wire format.

A successful core call means an in-memory semantic commit, **not** a disk write or peer acknowledgement. Returned receipts include the update/version needed for storage. Carbon should stage changes on a candidate document/session, persist the candidate checkpoint plus an outbox record atomically, then publish it to frames and send the outbox. A crash after persistence but before a reply can yield an already committed command on reload; request IDs in the worker's durable ledger prevent a blind retry from issuing it twice. Local write failure publishes no candidate. This orchestration and IndexedDB/OPFS transaction choice need their own integration check.

Within the core, an ordinary rejected call leaves text, identities, versions, stacks, tokens and outgoing events unchanged. Notifications are returned data emitted after commit; no user callback runs inside mutation. The implementation should compute/validate a candidate transition and publish only at the commit point. We must prove its actual failure paths rather than assume an arbitrary Rust mutation rolls back. Traps, process death, abort-on-allocation failure and damaged storage are outside that in-memory return contract; durable recovery is checked separately.

Undo here also does not restore the complete internal state: it appends history and advances versions. [Dolan, §2](#references) proves the counter characterization under a stronger undoability axiom that returns the abstract state itself. We are not claiming that inverse for the retained history; Stewen and Kleppmann explicitly discuss this internal/external distinction in §7. Our proof obligations must name the observed projection and allowed continuations, rather than asserting unrestricted cancellation.

**Retention proposal:** keep full semantic history for v0.1. No tombstone GC, history truncation or bounded-memory claim. A local undo limit may evict stack entries and tokens, but cannot erase replicated facts. Explicit byte/operation/input limits reject growth before admission; reaching them requires export/recovery or an application decision, not silent data deletion. This is a usable finite first release only if the agreed note-size/offline-history workloads fit on a phone. Measure those workloads before choosing numeric defaults; do not deploy an unlimited-history claim as phone readiness.

## 7. acceptance witnesses

These are required tests to implement, not results of the current scaffold. Run them with both replica-ID orderings, repeated undo/redo, batch/sliced delivery, duplicate updates and reconstruction on a third cold replica. Compare identity-sensitive ordering as well as text. For checkpoints, also resume the selected writer and continue its history.

1. **peer insertion survives:** A inserts `ab`; B inserts `X` between them. Undo A leaves `X`. Redo A returns `aXb`, using the original identities of `a` and `b`.
2. **overlapping deletion:** from one element `b`, A and B independently delete it. Undo A leaves it hidden; undo B reveals it. Equal spelling inserted anew is not that element.
3. **invisible undo crosses sync:** A inserts `a`; B imports it and inserts `B`; A imports B and, as a child of A's command, replaces B with `x`. B imports that edit and undoes B's own now-hidden insertion. Its version/update must change despite unchanged text. After A imports the activity and undoes A, the result is empty. Without B's undo, that continuation reveals `B`. A cold reader must distinguish those histories.
4. **late retirement:** deliver the previous activity event only after A has already undone A. Import must hide the revealed B and converge with the peer that knew the event earlier. No permanent "restoration already happened" exception.
5. **redo an invisible item:** redo B after the previous empty result reveals B; redo A restores `ax` and hides B again. No command may disappear from history because its first toggle was invisible.
6. **late child:** one writer issues primary `(`, an independent primary command inserts B after it, then an explicit child `)` inserted after B. Undo B gives `()`; undo the trigger gives empty; redo trigger gives `()`; redo B gives `(B)`. A child submitted while its trigger is inactive rejects without effect.
7. **historical side:** create `ab`, hide a, insert X once at an anchor before a and once in a separate history after a. Reactivate a: results are `Xab` and `aXb`, even though both insertions originally displayed `Xb`. Visible text alone cannot select the restoration side.
8. **admission and crash:** missing dependencies, conflicting known IDs, malformed activity and oversized batches publish nothing. Replaying a durably recorded update after a lost response does not duplicate characters or history membership. A persisted undo stays undone after cold load.
9. **real coordinates:** non-BMP scalars, combining sequences, empty text, both affinities, forward/backward ranges and multiple selections cross the actual Rust/Wasm/Carbon boundary. Invalid UTF-16 endpoints reject before edits. Book locators remain outside this coordinate test.

## 8. construction and proof order

1. **Settle the reference semantics.** Specify complete ordering, activity authority, child membership and version/admission rules. Turn the witnesses into a small executable specification. Agree the counterfactual redo examples, not just the function list.
2. **Build the pure sequence/activity slice and its proofs together.** Prove identifier uniqueness under the writer contract, deterministic interpretation, delivery/idempotence laws, visibility/activity laws and implementation-linked transition preservation. Cross the original two-peer and cold-reader witnesses with actual encoded operations. A model's convergence theorem does not automatically prove the Rust receiver.
3. **Close admission and local history.** Prove rejection neutrality and one-item stack transitions; test fault/limit paths, conflicting duplicates and checkpoint continuation. Extraction and bindings remain named trust boundaries.
4. **Ship the Wasm/Carbon note slice.** Add checked coordinate bindings, typed worker calls, local durable checkpoint/outbox and real reconnect/reload acceptance. Measure quota-sized Unicode edits, long inactive history, cold import, memory and update growth on the chosen phone test target. Set explicit supported budgets.
5. **Then add reader data primitives.** Specify registers before implementation: does a concurrent location choose one deterministic winner, or expose alternatives? A font setting and reading location need not have the same product policy. For keyed highlights, observed removal should not erase a concurrently added independent record; editing an already removed record needs an explicit policy. Reuse the engine's causal/activity machinery only after these meanings are fixed.

**Proposed v0.1 exit:** a real Carbon plain-note plugin uses Nickel through the Wasm/worker boundary; two offline writers and a cold reload preserve the listed sequence/undo laws; the shipped Rust transitions have source-linked proofs with explicit external assumptions; admission/storage failure tests and measured phone budgets pass. Rich text, general containers, arbitrary selective remote undo, permissions, GC and the full reader remain later work.

## review decisions

I recommend approving these directions, but each remains a proposal:

- sequence + undo + anchors first; registers/collections follow rather than being silently encoded as text;
- invisible undo is a replicated event **with redo**, unlike the retired no-op policy;
- single-origin command activity; foreign selective undo deferred;
- explicit late children, rejected while inactive; editor grouping outside the pure engine;
- full semantic retention with admission budgets for v0.1;
- first release tested by a Carbon note client, without promising all of M3 or a zero-change Loro swap.

The ordering interpretation and numeric workloads/budgets are still open requirements. Approval of this draft should authorize refining those requirements, not imply they have already been solved.

## references

1. **Stéphane Weiss, Pascal Urso and Pascal Molli.** “Logoot-Undo: Distributed Collaborative Editing System on P2P Networks.” *IEEE TPDS* 21(8), 1162–1174, 2010. [DOI](https://doi.org/10.1109/TPDS.2009.173), [author-uploaded full text](https://www.researchgate.net/publication/47441669_Logoot-Undo_Distributed_Collaborative_Editing_System_on_P2P_Networks). Relevant: §§4.4–6.2; unique ordered identities, patch activity, overlapping-deletion visibility. Its exactly-once delivery assumption is not a network guarantee we inherit; §6 of this contract requires duplicate admission to be idempotent.
2. **Weihai Yu, Luc André and Claudia-Lavinia Ignat.** “A CRDT Supporting Selective Undo for Collaborative Text Editing.” *DAIS 2015*, LNCS 9038, 193–206. [DOI](https://doi.org/10.1007/978-3-319-19129-4_16), [author-hosted paper](https://members.loria.fr/CIgnat/files/pdf/YuDAIS15.pdf). Relevant: §§3–6; operation relationships and their effect on selective undo.
3. **Weihai Yu, Victorien Elvinger and Claudia-Lavinia Ignat.** “A Generic Undo Support for State-Based CRDTs.” *OPODIS 2019*, LIPIcs 153, 14:1–14:17. [DOI](https://doi.org/10.4230/LIPIcs.OPODIS.2019.14), [open paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol153-opodis2019/LIPIcs.OPODIS.2019.14/LIPIcs.OPODIS.2019.14.pdf). Relevant: §5, concurrent undo/redo; its generic state-based construction is not an adopted Nickel backend.
4. **Leo Stewen and Martin Kleppmann.** “Undo and Redo Support for Replicated Registers.” *PaPoC 2024*, 1–7. [DOI](https://doi.org/10.1145/3642976.3653029), [open manuscript](https://arxiv.org/pdf/2404.11308), [author publication page](https://martin.kleppmann.com/2024/04/22/undo-replicated-register.html). Relevant: §§2, 4–7; register restoration, local stacks and comparison with activity approaches.
5. **Stephen Dolan.** “The Only Undoable CRDTs Are Counters.” 2020. [Open manuscript](https://arxiv.org/pdf/2006.10494); conference brief announcement in *PODC 2020*, 57–58, [DOI](https://doi.org/10.1145/3382734.3405749). Relevant: §§1–3, especially the abstract-state undoability axiom in §2.

Reading scope: Logoot-Undo §§4.4–6.2; Yu/André/Ignat full text, especially §§3–6; Yu/Elvinger/Ignat §5; Stewen/Kleppmann §§2–7; Dolan §§1–3. No implementation, application survey or benchmark from these papers was reproduced. These references inform semantic choices; they do not settle the still-open sequence ordering, prove Nickel's implementation or establish its phone budgets. The 500 ms grouping rule, explicit-child admission policy and worker durability boundary are product/API proposals, not conclusions attributed to these papers.
