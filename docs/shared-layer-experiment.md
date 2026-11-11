# one-pass shared causal layer experiment

This branch adds a payload-generic event store and two clients. An event has a
peer/counter identity, ordered causal dependencies and an arbitrary payload. The
store classifies exact duplicates and conflicts, selects an author's causal
basis, schedules a proposed history, asks the client to validate and rebuild
privately, and publishes the history and client state together only on success.

This is an **experimental parallel API**, not a migration of `edit::Replica` or
a verified CRDT release. The accepted text implementation and its proof sources,
generated views, receipts and hax snapshots remain unchanged. Their existing
statements are not automatically theorems about the new store or adapters.

## clients

`shared_text` carries one text operation per event through the shared store. It
embeds Alice as peer 1 and Bo as peer 2 and retains the existing two-writer text
backend. It rebuilds through that backend's public admission interface; this
also repeats some validation inside the backend. It is a real client of the new
store, not yet an extraction of every shared responsibility from the old API.
Its structured experimental error envelope need not reproduce the old API's
error priority. Multiple text operations in one event remain unsupported: there
is no new birth/target identity scheme here.

`atomic_map` is a small non-text client with ordered record-creation and
field-write batches, including opaque application-format tags and bytes. Its
example policy is deterministic canonical replay with last write in that replay
winning. Source events remain retained. This is not the proposed complete
register/collection API: there is no remove, Restore, Undo, retirement, garbage
collection or general mixed-version engine-operation protocol. In particular,
this example policy does not settle the register history contracts.

Both clients use the same native generic store. Application value-format bytes
may remain opaque in known writes. Unknown engine operation kinds are not
silently stored as applied, nor is a partially understood batch published.

## identity and resource boundary

The experimental peer representation is `u64` and order is peer-first, then
counter. This is an experimental choice, not adoption of all the writer-identity
proposal. A producer must have an exclusive peer and must not reuse counters
across crash, rollback, cloning or concurrent sessions. There is no persistence,
peer allocation or producer-counter recovery protocol here. Randomness is not a
uniqueness proof. The text backend still restricts peers to its explicit
Alice/Bo embedding; non-text examples exercise more peers.

Store event/dependency limits and client-specific bounds are explicit. Publication
is one store-owned history/state assignment boundary. The generic interface also
requires client equality, validation and replay to leave their borrowed inputs
and previously published reachable state unchanged. `Clone` alone does not
guarantee this: `Rc<Cell<_>>` can share mutable payloads across clones, allowing a
rejecting callback to alter retained content. Callbacks must be observationally
pure with respect to published data; mutable working data must be detached.
External callback effects are not rolled back. The supplied clients use owned
values and pure equality/validation/replay code, but no generic purity theorem is
claimed. Under those client obligations, rejection leaves published data unchanged. No over-capacity synchronization policy or
larger accepted text profile is introduced. Allocation/process failure and Rust,
hax, F* and model correctness remain trust boundaries.

## acceptance and proof scope

Run `cargo test --locked --workspace` for native acceptance. The original text
suite remains in that run. The new tests exercise causal graphs, exact content,
transactional rejection, text compatibility fixtures and ordered multi-field
creation. Finite tests are not universal refinement or convergence proofs.

Run `nix build --no-link .#shared-proofs` for the isolated
[generic envelope proof](../proofs/causal-envelope-view/README.md). It checks the
actual new source, not the earlier supplied toy probe: identity equality, exact
first-ID classification (even for duplicate-ID stores), ordered dependency
sequence equality, and whole-event equality under an explicit exact client
payload-equality premise. Fresh per-mode hax output must match its independent
extraction; the healthy native output also matches the tracked snapshot. Six
wrong-Rust controls and three callee/range-contract removals must fail ordinarily
at named owners, with no timeout/type-failure credit. This is a focused extraction
of classifier/equality roots, not extraction or proof of the entire generic
store.

The full new Latte document was inspected and emitted through the registered MCP
and compared byte-for-byte with the immutable producer. The portable gate checks
tracked source/view/native receipts; optional local re-emission is documented in
the proof README. The existing global native manifest was not repinned.

These theorems do not prove graph closure, scheduling totality, publication,
counters, client refinement or convergence. Client-supplied payload equality
still needs its own exactness proof; the logical premise does not certify an
arbitrary Rust callback. Those missing universal boundaries are required before
this becomes a replacement for the checked text shell.

No old theorem is weakened and no old mutant is reclassified by this experiment.
Before adopting this as the library's shared layer, the remaining universal
proofs, adapter bridges and exact-head acceptance require their own closure.
