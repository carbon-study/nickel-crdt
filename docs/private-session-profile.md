# private undo sessions and explicit Restore

This is the restricted Python reference experiment in
[sessions.py](../experiments/hybrid-restoration/sessions.py). Ren approved the
split after the appendix example: **ordinary Undo selects your own actions;
restoring another writer's deletion requires an explicit Restore action.**
Restore becomes an action in the restorer's own history. It is not a foreign
item slipped into that history by message receipt. This revises the earlier
q03/q18/q23 victim-undo interpretation. The old implicit-victim profile and its
receipts remain in Git at `c475d6d`; their passing checks did not settle this UX.

The experiment manipulates visible occurrence sets, not ordered text or an
editor. No Rust CRDT engine or general local-undo argument is supplied. All
V1–V9 remain unfulfilled.

## 1. occurrences and edits

`edit(creates=('x',))` accepts Unicode scalar values and allocates occurrence
IDs from a trusted writer tag, local counter and index. Equal values remain
different occurrences, including within one edit. Deletions name returned IDs,
not matching spellings. Redo preserves those occurrence identities. Surrogates
and conflicting births reject before publication.

A nonempty edit appends one own item. With pending redo, new work requires an
explicit `keep` or `clear` choice. Restore has the same requirement when it
actually creates an action. No q04 default is selected; keep-redo branch
stacking remains provisional. Groups, child edits and positions are not modeled.

## 2. ordinary Undo

`next_undo()` inspects only own items. Later own edits and successful redos take
priority. An own creation is eligible while it has an unwithdrawn occurrence,
even if another writer deleted that occurrence: undoing it may be invisible.
An ordinary deletion is eligible while it has a live removal atom. Undo of a
replacement restores its deletion effects and withdraws its creations in one
event. Frozen observed-concurrent restoration masks still give q07 its b result.
Selecting an own action does not imply author-exclusive effects.

An actual undo permanently consumes ineffective own items it bypassed before
the selected action. Inspection, import, and **empty undo consume nothing**.
An older item below the selected item was not bypassed. No skipped item gains a
redo entry. This preserves the earlier consumed-bypass choice, while ordinary
Undo no longer selects a foreign deletion.

A successful Undo returns the event, including its effect facets. Empty Undo
returns `None`. An invisible eligible Undo still emits an event and advances
history; it is not an empty press. UI explanation remains consumer work.

## 3. explicit Restore and its opposite

`restoration_choices()` offers known foreign deletions touching this writer's
created occurrences. It returns `(deletion, creator)` display suggestions,
ordered by the **highest current creator position**, including successful redo
priority, not original creation time. One deletion has one suggestion even when
it spans several creation items. String event-ID order breaks same-slot ties.
These suggestions never participate in ordinary Undo selection.

`restore(deletion, redo_policy=...)` freezes the selected deletion's full scope
and its observed-concurrent removal mask. It leaves that edit's insertion
portion alone. A replacement Friday→Monday can therefore explicitly restore
Friday while retaining Monday. The full deletion scope may include another
writer's text; this is the retained whole-deletion rule, not a general permission
or subset-selection model.

There is a necessary author-only facet. If Alice already undid her original
Friday insertion, suppressing Bo's deletion alone cannot reveal Friday: Alice's
own creation withdrawal also hides it. Explicit Restore therefore captures the
**live own withdrawal atoms for Alice's occurrences within that deletion's
scope**. These `reactivates` pairs are frozen alongside the deletion mask. With
an undone paste pq and Bo deleting p, Restore p re-enables p, not q. Bo cannot
reactivate Alice's withdrawal. Session restricts this to its own births; the
model additionally rejects a reactivation whose event author differs from the
withdrawal event's author. Writer metadata remains trusted, not authenticated.

The Restore event is appended as a new own history item. Its Undo cancels that
Restore's current token, retracting both masks, even if another restoration
makes that Undo invisible. Its Redo creates a **fresh token with the original
frozen masks**; it does not cancel a cancellation or expand to newly received
deletions. The next Undo targets that fresh token. The ordinary item previously
undone stays undone in private history: Restore is a new choice, not an implicit
redo of an entire old paste.

## 4. blocked Redo is different from empty Redo

Redo selects only the top private redo entry. It previews that entry against
the current document. If the visible **identity set** is unchanged, it returns
`Blocked(operation='redo', reason='unchanged-visible-identities', source, token)`.
It publishes no event and changes no counter, item, redo entry, stamp or mask.
An empty redo returns `None`. A new explicit Restore with no visible identity
effect likewise returns `Blocked(operation='restore', ...)` without an action.
Unknown or unavailable Restore choices reject with `ModelError`.

This reason reports the observed predicate, not an invented unique cause such
as “Alice blocked it.” Switching between two different visible x occurrences
counts as effective even when their scalar text looks identical. Arbitrary
older redo selection and automatic skipping are not implemented. A blocked top
entry can make an older useful redo unreachable; selective redo needs its own
contract. It is not silently adopted to work around that limitation.

The preview copies the full document. This is a reference operation, not a
performance or fatal-failure atomicity claim. Undo/Redo are not promised to
restore a global past state or be exact inverses amid remote changes.

## 5. imports, clear and matched saves

Imports publish shared facts without changing private items, counters, redo,
restore-token tracking or selection stamps. Clear-history forgets own history
and known foreign Restore sources; it does not erase shared effects. A newly
received deletion may still be offered using retained creation facts.

A checkpoint binds exact encodings of every known event, including after
clear-history. Resume requires those same contents, rejects later same-writer
activity, and allows remote extensions. Equal IDs with changed scalar content
are incompatible. Version **hybrid-private-session-3** also retains each explicit
Restore item's current token, its undone state and redo priority. Versions 1/2
reject; no migration is claimed. `private_state()` excludes the growing shared
basis, so import preserves it even though the next checkpoint records more facts.

This full-log trusted-shape codec is not a compact production format. The caller
must fence the writer before resume. Authentication, malicious checkpoint
admission, disk atomicity, arbitrary interrupts and concurrent calls remain
outside the experiment.

## 6. runnable evidence and remaining boundary

The [experiment README](../experiments/hybrid-restoration/README.md) owns commands,
finite exploration bounds, generated receipts and rejecting controls. Directed
calls cover the appendix press-time arrivals warm/cold, immediate Undo after
Redo, highest-current creator display slots, full-scope Restore, selected own
reactivation, peer reactivation rejection, fresh-token restore redo, unchanged
masks after late concurrent deletion, equal-looking occurrences, empty presses,
consumed bypasses, and compatible reload.

The bounded explorer compares uninterrupted and reloaded executions of the same
candidate. It is not an independent intended-undo oracle or an unbounded proof.
The split removes implicit victim selection; own eligibility can still depend
on received facts, and own deletion undo can suppress shared concurrent atoms.
It does not establish universal delivery-timing independence, positions,
permissions, registers, grouping/children, text order or a deployable engine.
