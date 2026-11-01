# private hybrid undo sessions: restricted reference profile

This profile runs `edit`, `undo`, `redo`, `receive`, `clear_history`, `checkpoint`
and `resume` over two independent documents. It follows Ren's collected PR4
review: compatible saves, library-owned occurrences, permanent bypass and redo
priority. The implementation is [sessions.py](../experiments/hybrid-restoration/sessions.py).
It is still a reference experiment, not Nickel's Rust API, a text-order engine
or a complete local-undo correctness argument. V1–V9 remain unfulfilled.

## 1. occurrences belong to the library

`edit(creates=('x',))` supplies a Unicode scalar value, not an identity. The
session allocates each occurrence from its trusted writer tag, event counter and
index within the edit. The model encodes that triple as a JSON string. Even two
`x` values in one edit get different identities. Two offline writers inserting
`x` therefore produce two occurrences; after sync, Alice's undo withdraws only
hers. Redo reactivates that same occurrence, not a newly allocated spelling.

An event carries its created IDs and `(ID, scalar)` payload pairs. Deletions
name the returned IDs, never a search for matching characters. The document
rejects conflicting births before publication. Values are validated as single
Unicode scalars; surrogates are rejected. This is exact-value preservation in
an identity-set model, not a chosen production encoding or insertion order.
Distinct writer tags and a fenced single continuation of each writer are still
trusted preconditions; this is not account authentication or a distributed
writer-registration protocol. Hand-authored lower-level event fixtures remain
separate from this library-allocated session path.

## 2. a bypassed item does not come back

Bo inserts z, Alice inserts b, then Bo deletes b. Alice restores the deletion.
Bo's next undo bypasses his already-reversed deletion and withdraws z. That
press **consumes** the bypassed own item permanently from Bo's private history.
When Alice redoes her restoration and b becomes hidden again, Bo's next undo is
empty. Bo gets no redo entry for an action he skipped; his actual undo of z can
still be redone.

This replaces the previous reversible-skip candidate. Ren explicitly rejected
that continuation in PR4. The old behavior is retained in Git at `15d06cf` and
in [session-review-before-repair.txt](../experiments/hybrid-restoration/session-review-before-repair.txt).
The `retain` control now fails the required consumed-bypass observation. The old
reactivation assertion is not still presented as a required oracle.

Only ineffective own items encountered before the selected eligible action are
consumed. An older item below a selected newer item has not been bypassed.
Consumption occurs when undo is pressed, not merely when a remote message
arrives or `next_undo` is inspected. An empty undo may consume ineffective own
items without emitting an event. Imports never append foreign items to the
private stack or consume local items on their own.

## 3. selection, full-scope restoration and redo priority

An own item is eligible unless locally undone, if it has an unwithdrawn creation
or an effective ordinary deletion atom. An ordinary deletion can matter even
when its target's creation is withdrawn; this does not eliminate invisible undo.

A foreign deletion is eligible for victim restoration when an effective atom
removes this writer's unwithdrawn creation. Selecting it restores the deletion's
**full original scope**, including other writers' characters in that deletion,
while leaving its insertion effects alone. Alice can therefore reverse Cam's
delete of both Alice's a and Bo's b. She cannot thereby restore unrelated
identities outside that selected scope. Frozen observed-concurrent masks and
separate creator withdrawal are unchanged from [the effect model](hybrid-continuation.md).

Causally later eligible actions take precedence. Concurrent ties prefer victim
restoration, then the model's string-ID order. This implements Ren's preferred
`a` restoration while leaving concurrent z in place. In the q07 fixture it also
selects Bo's deletion rather than Alice's concurrent own deletion; the frozen
mask still covers both and the required visible b is unchanged. This is a
private selection choice, not a new ordering primitive for text.

**A redo is a new local selection occurrence.** Its private selection stamp is
the emitted redo event, rather than the old source event. Type a, undo it, type
x with `keep`, then redo a: both are visible, and the next undo withdraws a,
leaving x. A later primary edit takes precedence over that redo. These stamps
are private checkpoint data; receivers do not recompute the author's chosen
source or import its private stack. Victim redo gets the same priority treatment
when the source becomes eligible again.

## 4. transitions and private state

Each session keeps its writer tag/counter, own items, locally undone own items,
redo entries, forgotten victim-source IDs and local redo selection stamps.

| call | replicated effect | private effect |
| --- | --- | --- |
| nonempty edit | one event allocates occurrences and/or deletes visible IDs | append own item; explicit pending-redo choice |
| own undo | one event restores deletion effects and withdraws own creations | consume bypassed items, mark selected item undone, append redo |
| victim undo | one frozen restoration event, no foreign creator withdrawal | consume bypassed own items, append private redo |
| redo | cancel the selected undo token and all its facets | pop redo, reactivate own item if applicable, update local selection stamp |
| receive | validate/publish a shared event | history lists/counter/stamps unchanged |
| empty undo | no event | consume any bypassed ineffective own items |
| empty redo | no event | unchanged |
| clear history | no event | clear lists/stamps; forget known victim sources |

Clear-history exclusions stay forgotten even if a peer later redoes the same
source; a newly issued deletion is a new candidate. It is not garbage collection:
shared semantic facts remain intact. Imports do not clear pending redo.

Pending redo plus new nonempty work still requires an explicit `keep` or `clear`.
Ren was unsure in q04; no default is silently selected. Retaining access does not
settle placement in an ordered document. Grouping, derived children, registers,
anchors, spans and positions remain outside this profile.

## 5. compatible document/history saves

A checkpoint includes an exact basis of every event encoding known when it was
saved, including when clear-history has emptied the private stack. Resume checks
that the supplied document contains all those same events, with identical
content. A document with later events authored by that same writer is also
rejected: the private save does not describe that writer's continuation.
Additional **remote** events are permitted and can change current eligibility.

Thus Alice cannot combine the empty document saved after undo with her later
history saved after redo. Clearing history after that redo does not evade the
basis check. Same event IDs with changed content are incompatible too. The
reference stores full canonical event encodings, not a compact checkpoint or a
cryptographic authentication mechanism. It intentionally spends space to make
the compatibility check explicit. The checkpoint format is now
`hybrid-private-session-2`; old version-1 saves are rejected, not silently
reinterpreted.

`private_state()` describes history independent of this basis. Receiving a new
remote event leaves that private history unchanged, but a subsequently saved
checkpoint records the larger shared basis. The earlier claim that checkpoint
bytes never change on import would be wrong for this format.

The caller must still fence the original writer before resume. Matched saves do
not provide disk atomicity, split-brain recovery or exactly-once user commands.
The codec remains trusted-shape, not general hostile-input admission. Arbitrary
interrupts, memory errors, callbacks and concurrent calls are not covered.

## 6. runnable evidence and remaining gate

The directed suite checks all review outcomes, whole-replacement/creator-
withdrawal continuations, q07, full-scope victim restoration, duplicate imports,
private reload, explicit new-edit policies and remote redo preservation.
[session-review-trace.json](../experiments/hybrid-restoration/session-review-trace.json)
shows the six review cases through actual calls;
[session-trace.json](../experiments/hybrid-restoration/session-trace.json) is
regenerated by actual calls; it shows occurrence IDs and scalar values separately.

The [bounded explorer](../experiments/hybrid-restoration/README.md#bounded-cold-session-continuation-check)
compares the same next operation after uninterrupted execution and JSON reload
of either or both peers. Its explicit four-seed/depth/action bounds remain in
its README and receipt. It is a codec/continuation regression against the same
candidate, not an independent intended-undo oracle or an unbounded proof.

No Rust transition/proof, general text order, permission/account model,
admission/storage budget, grouping/children or register continuation is supplied
by these repairs. Review behavior and implementation remain separate from the
complete reference-contract gate and eventual implementation-linked proofs.
