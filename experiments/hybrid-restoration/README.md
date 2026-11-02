# observed-concurrent restoration: directed reference candidate

The event-set portion is a research model for the [hybrid continuation](../../docs/hybrid-continuation.md), not Nickel's core, a selected undo protocol, a general session algorithm or a CRDT text-order implementation. It is separate from the Rust/hax proof scaffold. No parked Dark/Loro code is executed or changed.

## run

```sh
nix flake check -L .
nix run .
```

The nested flake pins the same nixpkgs revision as the project, with Python as its only runtime dependency. It neither extends the core's dependency graph nor deploys anything. Run from this directory to select its development shell. `nix run . -- target-only` and `nix run . -- all-known` intentionally fail the unchanged expected observations.

## exact candidate

A deletion has separately addressable atoms `(deletion-event ID, element ID)`. A restoration's author selects a deletion effect D, takes its original target set T, and captures a mask from its current causal view:

- include D's atoms;
- include atoms on T from other **observed concurrent** deletions;
- exclude unobserved deletions and any causally earlier/later deletion.

The mask is frozen into the restoration event. There is no separate selected-target-ID field: two local selections can produce identical masks and identical replicated events. A private checkpoint may retain the selected item if its UI/history contract needs it; the shared projection does not need that additional field in these cases. A receiver unions masks from uncancelled restoration events; it never reselects their targets. A fresh personal-redo event cancels the named restoration token; another writer's token remains. A later undo creates a fresh token rather than un-cancelling an old one. This explores the simpler personal-redo alternative permitted by Ren; it does not demonstrate that this is the simplest complete design.

Restoring a deletion effect of a replacement preserves that replacement's creation effects. Author undo of the whole replacement is one event carrying both the restoration mask and creator withdrawal for its inserted identities. Ordinary deletion restorations do not cancel creator withdrawals. Creator redo cancels that combined undo token; a peer's deletion redo can still hide the reactivated creation. This distinction repairs the review's replacement/deletion/undo counterexample. The fixture assumes the caller withdraws only its own creation; permission/admission is not implemented. The dictionary publishes that combined event in one `put`, so no prefix exposes only one facet of this authored undo. This does not establish general core transaction atomicity or admit arbitrary multi-event packets atomically. The event-set evaluator has only the narrow trusted-author reactivation guard, not general permission admission, transaction grouping, insertion order or a selection/redo stack; the private-session layer below adds a restricted selector and redo state.

## checks and their boundary

Twelve directed fixtures replay28 legal causal schedules, plus a check that two local targets can produce the same wire event. At each prefix they check an immediate duplicate, a JSON full-log reconstruction through `put`, equality of live removal atoms and creator-withdrawal tokens, and continuation to the expected final visible ID set. Late reverse-order duplicates are also checked. These are crafted event sets, not generated histories or a user model. The causal scheduler and the evaluator are ordinary Python, not extracted/proved code.

The five policy negative controls fail at their intended unchanged assertions:

- target-only restoration fails **q07 observed concurrent deletes**;
- cancelling every known deletion fails **later deletion remains through author undo**;
- using an ordinary delete to hide an undone creation fails **creator withdrawal survives peer deletion undo**;
- dropping the target-set filter fails **overlap restoration stays in selected scope**;
- splitting the compound undo into two events fails the **half-published compound undo** prefix assertion, even though its final p-only result is correct.

Passing the first check on the observed-concurrent law shows compatibility with this q07 fixture, not acceptance of its behavior for unseen concurrent deletions. The retained unseen-concurrent fixture instead leaves b hidden. That is a proposed boundary, not an answer Ren has supplied.

The log decoder assumes this model's JSON structure. `put` uses explicit `ModelError` exceptions for missing prerequisites, conflicting duplicates, non-ancestral/invalid deletion releases, unknown/non-ancestral/non-token cancellations and unknown/non-ancestral creator withdrawals. All these checks precede publication. Fourteen invalid-reference cases check unchanged event dictionaries, including under `python -O`; optimization does not disable these guards. This is still not full semantic admission: no general malformed-shape input suite, authority proof, parser/resource bound, independent reference oracle, compact checkpoint or disk failure acceptance is claimed. The fixed-event-set calculation is delivery independent by construction; the schedule count is a regression receipt, not the main argument for a general CRDT.

`model.py` and `check.py` are authored for this candidate. The earlier model supplied by Ren remains unmodified in the local evidence store; its40 schedules and q07 disagreement are recorded in [hybrid-traces.md](../../docs/hybrid-traces.md). We did not replace its expected result and relabel it passing.

## retained review failure

`review-before-repair.txt` records the old law revealing both p and x in all three review schedules, and the scope-spill control restoring unrelated c. The repaired p-only assertion was not weakened. Creator withdrawal is now a separate fact class; ordinary deletion/restore fixtures retain their earlier required text outcomes. An initial edit command used Node inside this Python-only nested shell and did not apply; the resulting missing-field TypeError is not counted as a semantic failure or passing check. The patch was then applied using the declared Python environment.

## collected audit follow-through

The peer audit read the pre-repair afc8eae source. Its creator-withdrawal finding was already addressed by the first repair; the remaining gaps led to the combined undo event, prefix oracle and explicit causal-reference guards described above. The earlier source and outputs remain in Git history. The positive schedule count drops when two effect facets become one event; the original p-only oracle is unchanged. Validation under optimization is tested separately from the ordinary assertion-based regression oracles.

## private-session continuation slice

[sessions.py](sessions.py) implements the restricted
[own-action Undo / explicit Restore profile](../../docs/private-session-profile.md).
Ren approved this split after the appendix scenario. Ordinary Undo never selects
another writer's deletion. Explicit Restore appends an own item; Undo retracts
its token, and Redo uses a fresh token with its original frozen masks.

```sh
nix run .#sessions
nix run .#sessions -- trace
nix run .#selection-review
```

`selection-review.json` and `session-review-trace.json` are generated directed
observations; `session-trace.json` shows explicit Restore and consumed bypass
through actual calls. The locked check regenerates and compares each receipt.
The old implicit-victim selector/receipts remain at `c475d6d`. Passing those older
checks was not a complete undo contract; changed outcomes here are policy
revisions, not relabeled old failures.

Ordinary edits accept scalars and mint occurrence IDs. Version-3 checkpoints bind
exact known event content and retain Restore-token identity. Missing/changed
basis or later same-writer work rejects; remote extensions are permitted.
Versions 1/2 reject without migration. The codec remains trusted-shape, not a
production format or disk durability guarantee.

Creator suggestions use the highest *current* affected creator position,
including redo priority. They organize `restoration_choices()`, not Undo.
The directed scenarios cover both before/after-redo and before/after-press
arrivals, warm and reloaded; immediate Undo after Redo; replacement and full
scope; equal-looking occurrences; and clear-history/compatible saves.

### selected own reactivation

Explicit Restore can re-enable its author's withdrawn occurrences **inside the
selected deletion's scope**. This makes the approved Friday scenario usable even
after Alice already undid Friday. Restoring p from her undone paste pq does not
revive q. The event carries frozen `reactivates` pairs in addition to its frozen
ordinary-deletion mask. Peers cannot override her withdrawal. Undo Restore
retracts both masks; Redo copies both into a fresh token. The model checks the
withdrawal event's author under trusted metadata and applies the same author
restriction to cancellation of restoration/withdrawal tokens; this is not authentication or
a general authority proof. Causal/atom/author failures reject before publication,
including under Python optimization.

### no-op and history behavior

Empty Undo leaves all history unchanged. An eligible but invisible own Undo
still records that action. Actual bypasses before a selected eligible action are
consumed; inspection/import and unvisited older items are not consumed.

Empty Redo returns `None`. An ineffective top Redo returns a `Blocked` result
with `unchanged-visible-identities`, without consuming that entry or selecting an
older one. Restore with no identity effect is also blocked. A redo switching
between distinct visible x identities counts as effective. Explicit `keep` or
`clear` is required for effective new work with pending redo; keep-redo stacking
is provisional. No selective-redo or exact-global-inverse promise is made.

## bounded cold-session continuation check

```sh
nix run .#continuations
# deliberate broken reloads, each exits 1 with a JSON witness:
nix run .#continuations -- drop-redo
nix run .#continuations -- drop-ignored
nix run .#continuations -- reset-counter
nix run .#continuations -- drop-restore-tokens
```

The explorer starts from **five** pairs: empty; synced victim deletion with an
older Bo item; partitioned independent deletions; synced replacement; and an
undone explicit Restore. It explores at most **three additional actions** and
at most **two creation-bearing events per writer**, including seed events.
The action vocabulary is either writer's Undo/Redo/clear, each offered explicit
Restore, a fresh x insertion, a singleton visible deletion or whole-visible-set
replacement by x (with explicit keep/clear policies), causally ready delivery,
and duplicate foreign delivery.

The current receipt visits **2,292** per-seed states. At **345** prefixes of
additional depth 0–2 it checks **5,283** outgoing actions, each warm and after
JSON reload of A, B or both: **15,849** comparisons. It compares returned events,
Blocked results or rejection, full shared facts, visible IDs, next own Undo and
Restore suggestions. The state key includes private checkpoints. Every visited
state, including depth-three leaves, completes synchronization and checks equal
facts/visibility and unchanged private history. The **10,000-state budget fails**
rather than silently truncating. Four broken-reload reports are retained under
[continuation-controls](continuation-controls/); the check regenerates their
first breadth-first counterexample and byte-compares it.

This compares the same implementation with itself after reload, not an
independent intended-undo oracle. Leaves have no outgoing restart test. Longer
histories, arbitrary edit subsets, text positions/order, grouping/children,
registers, hostile checkpoints, disk failures and split-brain writers remain
outside it. None of V1–V9 is discharged.

## rejecting session controls

In addition to the five unchanged raw-effect controls above, the locked check
requires these variants to fail at their named assertions:

| mode (`nix run .#sessions -- MODE`) | deliberately wrong behavior |
| --- | --- |
| retain | bypassed deletion returns after peer retracts Restore |
| unbound-save | cleared history bypasses saved basis |
| presence-only-basis | same IDs conceal changed scalar content |
| caller-ids | equal values alias occurrence IDs |
| old-redo-order | erase successful redo priority |
| eager-consume | discard an older item that was not visited |
| empty-consumes | empty Undo consumes inspected items |
| ineffective-redo-advances | publish/consume an identity-ineffective redo |
| receipt-ranking | insert foreign deletion into ordinary Undo |
| refreeze-restore-redo | expand Restore redo's mask to a late deletion |
| drop-restore-reactivation | selected own withdrawn p cannot be restored |
| peer-reactivation | another author overrides creator withdrawal |
| scope-reactivation-spill | Restore p revives unrelated grouped q |
| skip-blocked-redo | automatically select an older effective redo |

The scope, creator-withdrawal, later-deletion and q07 oracles remain intact. The
new selected-author reactivation is explicit and separately controlled; it does
not reinterpret peer restoration as permission to revive another author’s text.

## cancellation-authority review repair

The review of `8b0bc38` found that a peer could bypass the reactivation guard by
cancelling an entire foreign withdrawal. The model now checks the token author
in the `cancels` loop too. Two **named-session** fixtures reject Bo cancelling
Alice's withdrawal and her Restore token, without changing the document, and
check that Alice's corresponding cancellation still works. They run under normal
and optimized Python; anonymous legacy fixtures cannot establish this property.

`nix run . -- peer-cancel` removes that guard;
`nix run . -- peer-cancel-restore` keeps it for withdrawals but admits foreign
Restore cancellation. Each must fail at its matching peer-cancellation oracle.
The committed session and continuation receipts remain unchanged. This enforces
consistency of trusted author metadata, not authentication or complete admission.

## revision-bound Restore previews

`nix run .#restore-preview` runs the actual inspection/confirmation cases and
prints [restore-preview-output.json](restore-preview-output.json). The locked
check regenerates that receipt, checks guards under Python optimization, and
rejects five preview mutations:

```sh
nix run .#restore-preview -- reselect-on-confirm
nix run .#restore-preview -- accept-altered-preview
nix run .#restore-preview -- reserve-on-inspect
nix run .#restore-preview -- preview-target-list
nix run .#restore-preview -- recomputed-validity
```

The [contract](../../docs/restore-preview.md) explains the returned visible
occurrences, exact proposed event and full document/private binding. A hidden
remote change invalidates the proposal even if the screen looks identical. A
matching reload preserves it, while successful publication makes it stale.
These are directed held-proposal cases; the existing bounded explorer still
uses immediate Restore, not arbitrary pending proposals. Its receipts and the
old session/selection receipts remain unchanged. No text order, preview UI,
wire capability, concurrent-call atomicity or CRDT proof is claimed.

The source-substitution repair binds each proposal to a process-local issuance
record, not merely a newly recomputed valid effect. Bo/Cam previews with identical
effects cannot be interchanged by changing only source. Matching resume tests
hold the original handle in the same interpreter; process restart discards it.
The weak-key registry releases records when the last proposal copy drops its
handle. This is not a serialized capability or authentication against arbitrary
in-process code. Full-basis invalidation remains conservative: the five-unrelated-
keystroke scenario is retained, not a material-change reconfirmation policy.
