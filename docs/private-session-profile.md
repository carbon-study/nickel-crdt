# private hybrid undo sessions: a restricted reference profile

The [restoration candidate](hybrid-continuation.md) can calculate visibility after authored events. This slice adds actual `edit`, `undo`, `redo`, `receive`, `clear_history`, `checkpoint` and `resume` calls that **select and generate** those events. The runnable implementation is [sessions.py](../experiments/hybrid-restoration/sessions.py); [session_check.py](../experiments/hybrid-restoration/session_check.py) drives two independent documents/sessions. This remains an unapproved reference profile, not Nickel's Rust API or a complete text CRDT.

## 1. the skipped-item choice

**Candidate policy: an externally reversed deletion is bypassed, not permanently removed from its writer's private history.** If a peer's redo makes that deletion effective again, it becomes selectable again unless this session has itself undone or cleared that item. This avoids changing a private cursor merely because a remote restoration arrived. It can make an older, previously bypassed item reappear; that consequence needs review.

Let Bo first create z, Alice create b, and Bo delete b. Both receive the edits. The following table is produced by actual session calls; the visible sets do not specify text order.

| action, received by both | visible IDs | Alice's next undo | Bo's next undo | waiting redo |
| --- | --- | --- | --- | --- |
| initial synced deletion | z | restore Bo's deletion | Bo's deletion | none |
| Alice undo | b,z | Alice's insertion of b | Bo's older insertion z | Alice's restoration |
| Bo undo | b | Alice's insertion of b | empty | Alice's restoration; Bo's undo of z |
| Bo resumes a saved private session plus shared facts | b | unchanged | empty | unchanged |
| Alice redo | empty | restore Bo's now-effective deletion | Bo's reactivated deletion | Bo's undo of z |
| Bo undo | b | Alice's insertion of b | empty | Bo can redo the deletion restoration, then his undo of z |

[session-trace.json](../experiments/hybrid-restoration/session-trace.json) records the actual IDs, next actions and each separate redo list. Run it again with:

```sh
cd experiments/hybrid-restoration
nix run .#sessions -- trace
```

The alternative that consumes a skipped item fails the chosen profile's reactivation assertion. That is a policy contrast, not a proof that permanent skipping is universally wrong or that Ren already selected this behavior.

## 2. state and selection rules

Each session has one trusted writer tag, a next synthetic event counter, its ordered own-item list, a set of locally undone own items, and a private redo list. Shared events gain a writer tag so the profile can identify whose creations were deleted. This tag is not authentication, an account, a user grant or an adopted Nickel wire format. Imports change the document and therefore future eligibility, but never append a foreign item to the private list or clear redo.

The candidate selects as follows:

1. An own item is eligible unless locally undone, if any of its creation effects is not withdrawn or any of its ordinary deletion atoms remains effective. An ordinary deletion can remain semantically relevant even while its target's creation is withdrawn; invisible history actions are not eliminated.
2. A foreign deletion is a victim-restoration candidate if an effective atom targets this writer's creation and that creation has not been withdrawn. Selecting it restores the deletion's **full original scope**, which may include text from several creators, while leaving its insertion effects alone. This agrees with q11's requested restoration of a/B while preserving x; it does not settle general per-hunk/subset selection.
3. Prefer causally later eligible source actions. Among concurrent maximal candidates, prefer an own item, then the model's string ID order. This tie policy is a concrete arbitrary profile choice, not a new ordered-ID primitive or sequence-placement decision.

A locally selected source belongs in the private redo/history record when needed. The replicated event carries its author and frozen effect mask, not a redundant selected-source-ID field. Receivers apply it without calling their own selector.

## 3. transitions implemented in this profile

| call | document effect | private effect |
| --- | --- | --- |
| nonempty edit | one event creates fresh supplied IDs and/or deletes currently visible IDs | append one own item; explicit pending-redo policy below |
| undo own item | one event restores its deletion effect under the observed-concurrent law and withdraws its creations | mark that item locally undone; append its opposite to redo |
| undo victim deletion | one restoration event, no withdrawal of the foreign creation effects | append a private redo entry; do not alter the foreign writer's private list |
| redo | one event cancels the selected undo token and all its facets | pop the top redo; reactivate an own item locally if applicable |
| receive | ordinary model-event validation/publication | no list/counter mutation; subsequent selection is derived again |
| empty undo/redo | no event | no change |
| clear history | no event; semantic facts stay intact | clear own items and redo; forget currently known victim candidates |

Clear-history also suppresses later reselection of those same forgotten victim-source IDs, even if a peer later redoes them; a newly issued foreign deletion is a different candidate. This is a specified profile choice, not garbage collection. Full event history remains retained.

Ordinary input edit IDs must be fresh; deletions must target the current visible identity set. Each edit is one item/event. Multi-step scratch edits, timed grouping, asynchronous children, registers, anchors, spans and positions are **not** implemented by this profile.

### redo after new primary work remains an explicit choice

Ren was unsure in q04, prioritizing data recovery. The reference method therefore refuses a nonempty new edit with waiting redo unless the caller explicitly chooses `keep` or `clear`. `keep` preserves the old redo list; `clear` drops local access without erasing replicated facts. Both are exercised. This is not a selected Nickel default, a full undo tree or a claim that reintroduced text has the desired placement. The identity-set model has no text positions.

## 4. two peers, action timing and checkpoints

The directed checks generate events through session calls for:

- the skipped-item cycle above, including resuming Bo before and after Alice's redo;
- Bo undoing his deletion before seeing Alice's restoration versus pressing afterwards, legitimately selecting his older z. Once emitted, his message never turns into a different selection on receipt;
- q07's synced concurrent deletes, including empty Bo undo while his deletion is externally reversed and reactivation after Alice redo;
- q11's whole replacement and victim restoration, preserving the completed author undo through victim redo;
- the reviewed creator-withdrawal case, then creator redo and peer deletion redo;
- pending redo surviving remote edits, both explicit new-edit policies, and clearing history without reactivating text.

Three action-generated event sets also cross causal-delivery replay, duplicate handling and shared-log reconstruction at every prefix. **Private sessions** in those directed checks are resumed at selected continuation cuts, not exhaustively at every prefix. A fresh reader receives shared facts but no private items; its undo is empty. The private checkpoint serializes source/token references, phases and the synthetic allocator. Shared document state is supplied separately.

Checkpoint decoding is a small trusted-shape reference codec with reference checks, not general hostile-input admission or a selected production format. The caller must stop/fence the original writer before resuming it; no disk transaction, split-brain recovery or exactly-once user-command protocol is implemented. A stale next-ID continuation is rejected when it already occurs in the document. Memory errors, arbitrary interrupts, reentrant callbacks and concurrent method calls are outside these model checks. No general Python transaction-safety guarantee is being made.

### bounded generated cold continuations

A separate [bounded explorer](../experiments/hybrid-restoration/README.md#bounded-cold-session-continuation-check) now tests all outgoing actions from238 generated prefixes at depths zero through two under its explicit four seeds and action grammar. It compares uninterrupted operation with JSON reconstruction of either or both peers, then executes the same actual next operation. Its3,419 edges give10,257 warm/cold comparisons. This is separate from the directed trace's selected checkpoint cuts; it does not extend them to arbitrary histories or test outgoing actions from the depth-three leaves.

The comparison checks operation results, shared facts, visible identities and next undo selection, using the same session/effect code on both sides. It does not independently judge whether the profile is the undo behavior users want. Three deliberately damaged reloads produce retained executable witnesses for lost redo, forgotten clear-history exclusions and allocator collision. No session/effect transition or proposed policy changed to make this check pass.

## 5. what this closes and leaves open

This slice replaces hand-authored undo targets with running private-session transitions for the stated restricted profile. It makes “the other writer's history adjusts” mean derived eligibility without replicated private lists, and chooses reversible skipping as an explicit candidate. It does not establish that the policy is the desired one in every questionnaire scenario.

General command membership/children, account or permission scope, concurrent victim-choice policy, registers, text order/placement, cost/admission budgets and implementation-linked Rust proofs remain open. V1–V9 remain unfulfilled. The next contract work is to reconcile this profile with those missing cases before adopting a core API; do not silently rename it a complete local-undo algorithm.
