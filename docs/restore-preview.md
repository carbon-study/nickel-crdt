# inspect Restore, then confirm exactly that proposal

Suppose Bo replaced Alice's Friday and Carol's sentence with Monday in one
edit. Restore covers that deletion's whole scope. The consumer needs to know
that **Friday and Carol's sentence will return, while Monday remains** before
it offers confirmation. Looking only at the deletion's original targets is not
enough: Carol may since have withdrawn her own sentence, so it would stay hidden.

The reference session now exposes this two-step operation:

```python
proposal = alice.inspect_restore(deletion.id)
proposal.restored     # occurrences that would become visible
proposal.retained     # visible occurrences that would remain visible
proposal.still_hidden # selected deletion targets still hidden after this proposal
result = alice.confirm_restore(proposal, redo_policy='keep')
```

This is the Python identity-set experiment, **not** an adopted Nickel Rust API,
ordered text, Carbon UI or a complete undo contract. The approved own-action
Undo / explicit Restore [semantics](private-session-profile.md) are unchanged.
Recent-changes lists and on-demand inline markers remain consumer work.

## what inspection supplies

`RestorePreview` contains the selected deletion ID, writer, a full binding basis,
and the exact predicted event: identity, author, causal prerequisites, frozen
deletion releases and selected own creator-reactivation pairs. It also carries
before/after visible occurrences, the actual restored/retained subsets, and the
selected targets that remain hidden. Each occurrence records its identity,
scalar and birth author's trusted tag. The collections are sorted by identity;
**they are not a text order or strings to concatenate into prose**.

The current full-view lists make the reference calculation inspectable, not
compact. Hand-authored legacy births without scalar payloads are reported with
`scalar=None`, never an invented value. A future ordered engine/consumer must
provide text reconstruction, location, human author names and presentation.

Inspection publishes nothing and changes neither history nor the allocator.
Its predicted event ID is not a reservation or an admitted history fact. The
consumer must not treat that ID as committed before confirmation succeeds.
Repeated inspection on the same basis yields the same immutable proposal.

## what confirmation binds

The binding is the exact canonical private checkpoint, including every known
shared event's contents, the writer/counter, own items, redo entries, current
Restore tokens, clear-history exclusions and priority stamps. It is a
reference **full-content comparison**, not a compact revision ID, cross-replica
clock, hash proof or authenticated capability. The proposal includes private
history in its basis and is not a replicated document event.

Confirmation first rejects another writer or a changed binding. A new shared
fact invalidates the proposal even when it leaves the screen unchanged, has no
restoration effect, or changes an unrelated part of the document. A changed
private continuation, such as clear-history, also invalidates it. This is
conservative: the caller must obtain and display a fresh proposal rather than
silently reselecting the old deletion against the new state.

On an unchanged basis, the session recomputes the expected proposal for
validation and rejects altered display fields, source or event masks. It then
publishes **the inspected event**, not a newly chosen action. Under the
single-threaded profile, successful confirmation returns an event equal to
`proposal.event`; the resulting visible identities equal `proposal.after`.
That publication changes the binding, so confirming the same old proposal again
rejects. Rejected confirmation changes neither document nor private history.

An exact duplicate import or a no-op call that changes no state does not
invalidate a proposal. A matching resume can confirm the same in-process
proposal after reconstructing the identical document/private checkpoint; the
caller must first fence the original writer. Proposals have no public wire or
save format, and the existing version-3 session checkpoint format is unchanged.

## blocked results and history policy

If the inspected event changes no visible identities, confirmation returns the
existing `Blocked('restore', 'unchanged-visible-identities', source)` result
without publication or history change. Such a proposal may be confirmed again
while its basis is unchanged and yields the same blocked result.

For an effective Restore, a pending redo still requires explicit `keep` or
`clear` at confirmation. This private-history choice is separate from the frozen
document effect. A missing/invalid policy rejects unchanged and does not consume
a valid proposal. `restore(source, redo_policy=...)` remains the immediate
convenience call: inspect and confirm without an intervening consumer decision.
It produces the same events and histories as the earlier direct Restore.

## executable boundary

From `experiments/hybrid-restoration`:

```sh
nix run .#restore-preview
nix flake check -L
```

The generated receipt covers full mixed-author scope, retained replacement
text, Carol's later invisible withdrawal, unrelated and semantic-no-op remote
facts, altered/foreign/untyped proposals, private clear-history, repeated
confirmation, selected own reactivation, explicit policy, blocked proposals and
matching warm/cold continuations. Four wrong implementations fail: reselecting
at confirmation, accepting altered preview fields, reserving an identity during
inspection, and reporting all deleted targets as visibly restored.

The older session/selection/continuation receipts remain unchanged. The bounded
continuation explorer still exercises immediate Restore; it does **not** explore
every schedule with a held proposal. The new held-proposal cases are directed
regressions, not an independent semantics oracle or general concurrency proof.
No guarantee covers asynchronous mutation during a call, fatal interruption,
hostile proposal deserialization, writer split-brain, storage or resource bounds.
No Rust transition, implementation-linked CRDT proof, ordering/anchor law,
editor or deployment is supplied. All V1–V9 remain unfulfilled.
