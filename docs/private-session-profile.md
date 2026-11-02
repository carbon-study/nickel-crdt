# private hybrid undo sessions: restricted reference profile

Ren's follow-up selects **creator-slot placement**. The earlier overlapping-
delete answer is retracted: the first undo restores a,b, not b,c. Empty undo
preserves history; visibly ineffective redo emits nothing and preserves history.
Keep-redo branch stacking remains provisional.

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
arrives or `next_undo` is inspected. An empty undo consumes nothing, including ineffective own items it inspected. Imports never append foreign items to the
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

A foreign deletion's restoration sits immediately above the newest local
**creation item** containing any occurrence that deletion targeted. One deletion
gets one choice, even when its scope spans several creation items. Newer own
items stay above that slot. Foreign receipt time and its relation to a local
redo's causal ancestry do not set priority. Same-slot victims use string event-ID
order, independent of receipt order. A forgotten creation still supplies a slot
for a newly received deletion; clear-history suppresses only already known victims.

For p older than a, with a undone and redone, Bo's offline deletion of p gives
three undos: remove a, restore p, remove p. This holds whether the deletion
arrives before or after redo and after compatible reload. With p,a in one item,
restore p precedes withdrawing that whole item. A deletion spanning p and q sits
once above q, the newer affected creation.

For one creation abc followed by Alice deleting a,b and Bo deleting b,c offline,
Alice's own deletion lies above Bo's creation-anchored choice. The first undo
restores **a,b**. This is the outcome Ren accepted on retracting the inconsistent
b,c answer; the frozen-mask effect rule is unchanged. q07 similarly selects
Alice's own deletion and still restores b. The previous concurrent victim-first
preference is superseded. This ranks private actions, not characters in text.

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
| effective redo | cancel the selected undo token and all its facets | pop redo, reactivate own item if applicable, update local selection stamp |
| receive | validate/publish a shared event | history lists/counter/stamps unchanged |
| empty undo | no event | unchanged, including inspected ineffective items |
| empty or visibly ineffective redo | no event | unchanged, including the pending redo entry and counter |
| clear history | no event | clear lists/stamps; forget known victim sources |

Redo first previews cancellation on a document copy. If the visible **identity
set** is unchanged, it returns no event and changes neither shared facts nor
private state. Equal-looking scalar values do not substitute for identity. A
later retry can succeed after another action changes the document. This is a
reference evaluator, not a performance claim or a fatal-failure atomicity proof.

This rule has consequences beyond the motivating causal-delete example. Two
independent restorations that both keep b visible can each make the other's
redo ineffective: neither redo is consumed or published, so b stays visible.
For the replacement continuation, Bo's ineffective redo waits while Alice's
undo also restores the same deletion; after Alice redoes, Bo can retry and
successfully hide the restored originals. These are changed session
continuations required by the no-advance rule. The raw effect model still allows
explicit cancellation events; it does not impose this session-level gate.
Invisible **undo of an eligible item** remains allowed; an empty undo means no
eligible item was selected, not merely that the screen did not change.

Clear-history exclusions stay forgotten even if a peer later redoes the same
source; a newly issued deletion is a new candidate. It is not garbage collection:
shared semantic facts remain intact. Imports do not clear pending redo.

Pending redo plus new nonempty work still requires an explicit `keep` or `clear`.
Ren was unsure in q04; no default is silently selected. Keep-redo branch stacking
is provisional, not a settled policy for arbitrary histories. Retaining access does not
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

The directed suite checks the implemented review continuations, whole-replacement/creator-
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
