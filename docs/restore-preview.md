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
Each inspection also issues an opaque process-local handle and retains a frozen
record of the proposal under that handle. The handle reserves no event identity
and changes no document or private checkpoint. Repeated inspection yields equal
public data with distinct valid handles. A weak-key registry drops the issuance
record when no proposal/copy retains its handle; it does not retain discarded
proposals indefinitely.

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

On an unchanged basis, confirmation compares every field with the frozen record
associated with the issued handle. It rejects an unknown handle or changed
source, display fields or event masks. Recomputing a valid proposal is **not**
sufficient: Bo and Cam can independently delete the same x, giving identical
restoration masks and predicted events for two different valid choices. Changing
only a Bo preview's source to Cam must still reject. A separately issued Cam
proposal remains a valid choice; the API binds the submitted issuance, not proof
that a human looked at it. Confirmation then publishes **the inspected event**,
not a newly chosen action. Under the single-threaded profile, successful
confirmation returns an event equal to
`proposal.event`; the resulting visible identities equal `proposal.after`.
That publication changes the binding, so confirming the same old proposal again
rejects. Rejected confirmation changes neither document nor private history.

An exact duplicate import or a no-op call that changes no state does not
invalidate a proposal. A matching resume **in the same interpreter** can confirm
a held proposal after reconstructing the identical document/private checkpoint; the caller must first
fence the original writer. In-process copies retain the same immutable handle.
An interpreter restart loses the issuance registry: inspect again rather than
reconstructing a proposal from public fields. Proposals have no public wire or
save format; the registry is not persisted in the version-3 session checkpoint.
This is not a network capability or an authentication boundary against arbitrary
Python code that can modify the module's private memory.

### reference invalidation versus editor reconfirmation

The reference retains conservative full-basis rejection. Five successive
unrelated introduction edits each invalidate an appendix preview, even though
the same occurrences would return. The directed receipt demonstrates that case;
it is not silently relaxed to visible-string equality.

An editor may eventually distinguish revalidation from asking for another
click, but that needs a separate material-change contract. Selected deletion
identity, masks and actual occurrence effects matter; identical strings alone
cannot define equivalence. This draft does not implement that editor policy.
`retained` covers the whole currently visible view. To label “Monday will remain”,
intersect it with the **selected original edit's** `creates`, not the Restore
event's empty `creates`. Unrelated introduction text can remain outside that
label even though it is included in the full reference view.

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

The generated receipt covers equivalent-effect Bo/Cam source substitution live
and after matching in-process resume, issued-handle lifetime, five unrelated
edits, full mixed-author scope, retained replacement text, Carol's later invisible withdrawal, unrelated and semantic-no-op remote
facts, altered/foreign/untyped proposals, private clear-history, repeated
confirmation, selected own reactivation, explicit policy, blocked proposals and
matching warm/cold continuations. Five wrong implementations fail: replacing
issuance checking with semantic recomputation, reselecting at confirmation,
accepting altered preview fields, reserving an identity during
inspection, and reporting all deleted targets as visibly restored.

The older session/selection/continuation receipts remain unchanged. The bounded
continuation explorer still exercises immediate Restore; it does **not** explore
every schedule with a held proposal. The new held-proposal cases are directed
regressions, not an independent semantics oracle or general concurrency proof.
No guarantee covers asynchronous mutation during a call, fatal interruption,
hostile proposal deserialization, writer split-brain, storage or resource bounds.
No Rust transition, implementation-linked CRDT proof, ordering/anchor law,
editor or deployment is supplied. All V1–V9 remain unfulfilled.
