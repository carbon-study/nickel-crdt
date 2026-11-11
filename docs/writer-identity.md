# Writer identity beyond two writers (draft proposal)

Status: **draft for Lynn (owner) and Ren.** Nothing here is decided. It proposes
how Nickel replaces its two-constructor `Writer` with Loro-style opaque peer
IDs, and how to keep every proof from depending on there being two writers.
Facts about this repository were checked against `main` at `79ea964`. Facts
about Loro are from memory and marked as such.

## 1. Where the two-writer assumption lives today

The runtime already treats writers generically almost everywhere. The
assumption is concentrated in the representation and two proof sites.

**Representation (src/edit.rs).**
- `pub enum Writer { Alice, Bo }`, with `writer_index(w) -> u8` mapping Alice → 0
  and Bo → 1.
- `impl PartialEq for Writer` compares `writer_index` values.
- `event_lt` orders events by `writer_index`, then counter. `birth_lt` builds on
  it.

**Already writer-generic (no change in meaning).**
- `EventId { writer, counter }` and `BirthId { event, index }` as identities.
- Admission's per-writer chain in `validate_new`: counter `c > 1` needs
  `(writer, c - 1)` in the fact's past, and no same-writer event with a counter
  at least `c` may be in that past.
- `Replica { writer: Option<Writer>, next_counter }`: one writer per replica.
  `None` cannot author (`Invalid::NoWriter`).
- The contract text already speaks of replica IDs. `docs/carbon-contract.md`
  says "A replica ID identifies a single operation writer… The caller supplies
  that identity and prevents simultaneous reuse; Nickel checks structural
  identity conflicts". `docs/collection-contract.md` notes that "public IDs stay
  held".

**Proofs that case-split on the two constructors.**
- `EditIdentity.writer_index_is_exact`: `writer_index(w)` equals
  `match w { Alice => 0, Bo => 1 }`. `writer_equality_exact` builds on it.
- `EditAccepted.event_key`: `rank = match id.f_writer { Alice => 0, Bo => 2^64 }`,
  then `rank + counter`. `event_order_is_key_order` proves `event_lt` agrees
  with that key.
- Every other proof that mentions writers takes `Option<Writer>` or a writer
  value as an opaque parameter. Examples are the `new_establishes_*` laws in
  EditAccepted, EditAtomic, EditCausal, EditWellFormed and Spec.

**Mutation modes tied to the enum (scripts/check-edit-proofs.mjs).**
- `writer-index-collides` edits `Writer::Bo => 1` to `=> 0`.
- `identity-writer-equality` makes equality compare `self` with itself.
- `order-key-ignores-writer` drops the writer component of `event_lt`.
- `scheduler-records-wrong-id` and `past-invents-id` construct
  `Writer::Alice` IDs as wrong values.

**Fixtures and oracles.**
- Native tests construct `Writer::Alice`/`Writer::Bo` in `tests/edit_admit.rs`
  (24), `src/edit/causal_basis_tests.rs` (8), `author_replay_tests.rs` (5),
  `basis_filter_tests.rs` (1) and `tests/capacity_boundary.rs` (2).
- `scripts/check-rust-edit-reference.py` maps `writers=['Alice','Bo']`, and
  `scripts/compare-edit-storage.mjs` alternates the two.
- The Python oracle `experiments/combined-admission/admission.py` already has a
  third writer: `WRITERS = {'Alice': 0, 'Bo': 1, 'Cam': 2}`.
- The design docs (`first-cut-decisions.md`, `hybrid-*.md` and others) use Alice
  and Bo as narrative names. They need no change.

So the proofs are not currently *about* two writers except at two definitional
sites. But nothing prevents a future proof from case-splitting on the enum, and
the native fixtures only ever exercise two writers.

## 2. Proposal: an opaque peer ID with a fixed total order

### 2.1 Representation
- `pub struct Writer(pub u64)`: an opaque peer ID, as in Loro. From memory,
  Loro uses a random `u64` `PeerID` per session and identifies operations by
  `(peer, counter)`.
- `EventId { writer: Writer, counter: u64 }` and `BirthId` are unchanged in
  shape.
- Equality is `self.0 == other.0`. Order is numeric on `.0`, then counter.
  `writer_index` disappears.
- `MAX_COUNTER` (2^53 − 1, JavaScript-safe) is unchanged. Peer IDs are full
  `u64`. A JavaScript binding would therefore carry peers as `bigint` or a
  string. That is a binding decision (§4).

### 2.2 What the order is for
The writer order is only a deterministic tie-break, used in canonical fact order
(`event_lt`) and in FugueMax sibling/tie decisions through `birth_lt`. Any fixed
total order on peer IDs preserves convergence, because every replica uses the
same order. Numeric order on `u64` is the simplest.

The visible consequence is that **which concurrent insertion goes first is
decided by peer-ID order**, as with Lamport-style tie-breaks. With random peer
IDs that is effectively arbitrary but consistent. Ren should confirm this is
acceptable for text placement. Today the same role is played by "Alice before
Bo". Which recorded placement decisions (q30/q31 and the others) depend on that
tie-break has not been checked for this draft.

### 2.3 Fencing and allocation
These stay caller responsibilities, as the Carbon contract already states.
- One producer per peer ID.
- A restarted writer needs its persisted next counter, or a new peer ID.
- Two independent writers must not share a counter allocator.

Nickel keeps checking structural conflicts. The same `(peer, counter)` with
different contents is rejected as today, via `duplicate`/`fact_equal`, with
`EditIdentity.duplicate_matches_lookup` and the `identity-accepts-conflict`
mode.

Suggested allocation (not Nickel's job, recorded for Carbon): a fresh random
`u64` per session or per device install, persisted with the next counter. The
collision probability among k peers is about k²/2^65.

### 2.4 Encoding
Peer IDs become 8 bytes per event ID. A per-update peer table (index into a
list of peers) is a later size optimisation. It is not needed for correctness
and is not proposed for v0.1.

## 3. The proof rule ren asked for: no two-writer dependence

**Rule.** No proof may case-split on, or enumerate, writer values. Writers may
appear only through:
- equality (`w1 == w2`), and
- the fixed total order on `EventId` / `BirthId`.

Every theorem that mentions writers must therefore hold for arbitrary peer
sets, including one writer and many writers.

**How to make that mechanical, not a convention.**
1. **Fence:** `proof-reform.mjs` rejects writer-constructor patterns and
   numeric writer literals in `.lt` sources, for example `Writer_`, `match …
   f_writer {` with literal arms, or `mk_u64(<literal>)` applied as a writer.
   Fixtures prove the fence refuses them.
2. **Re-prove the two definitional sites generically.**
   - `writer_index_is_exact` and `writer_equality_exact` are replaced by
     `writer_equality_is_value_equality`, a single statement over all `u64`.
   - `event_key` becomes `v(id.f_writer.0) * 2^64 + v(id.f_counter)`, with no
     match. `event_order_is_key_order` is re-proved over all peers. The same
     order lemma then serves canonical order and FugueMax tie-breaks.
3. **Mutation modes** keep their fault meaning, with new anchors:
   - `writer-index-collides` becomes "equality ignores the high bits", e.g.
     `self.0 == other.0` changed to `(self.0 & 1) == (other.0 & 1)`. This is a
     collision that only a many-writer fixture can expose.
   - `identity-writer-equality` and `order-key-ignores-writer` keep their
     meaning.
   - `scheduler-records-wrong-id` and `past-invents-id` use `Writer(0)` as the
     invented ID.
4. **Native fixtures with at least three writers**, including the extremes `0`
   and `u64::MAX`, and a peer order that differs from creation order. A fixture
   that only ever uses two adjacent IDs could hide a parity- or low-bit
   comparison.
5. **No proof premise may bound the number of writers.** The existing limits
   (`events`, `births`, …) bound history size. A writer count is not a limit
   and should not become one.

## 4. Migration order (proposed)

1. **Fence first** (small PR). Add the no-case-split rule with refusal
   fixtures. It must exclude the two current definitional sites by name, so
   every *other* proof is already compliant and future slices cannot regress.
2. **Representation** (one PR, runtime plus the two proofs):
   - change `Writer` to the `u64` newtype;
   - rewrite equality and `event_lt`;
   - re-prove the identity and key-order lemmas generically;
   - re-anchor the five writer-related mutation modes;
   - remove the fence exclusion;
   - regenerate hax and receipts.
   Its acceptance is the whole gate, since every module's extraction changes.
3. **Fixtures** (same or following PR): map `Alice → Writer(1)` and
   `Bo → Writer(2)` mechanically, then add many-writer native fixtures (§3.4).
   Also update the Python oracle and the storage comparison to accept arbitrary
   peer IDs; the oracle already takes a third name.
4. **Contracts and docs:** state the peer-ID order as the tie-break in
   `fugue-ordering.md` and the contract docs. Keep the narrative names.

Step 2 changes the extraction of `Nickel_crdt.Edit` everywhere. Per today's
solver-margin survey, queries near their budget (one at 76%) should be
re-measured on that PR rather than assumed stable.

## 5. Open decisions

- **Peer ID width:** `u64` as in Loro (memory), or `u128`, or opaque bytes.
  `u64` keeps the order lemma arithmetic simple and the encoding small.
- **Tie-break order:** numeric peer order (proposed), or a hash of the peer.
  Both are deterministic; numeric is simpler to prove.
- **Reserved values:** whether `Writer(0)` or `u64::MAX` is reserved. Proposed:
  none, and fixtures exercise both.
- **JavaScript representation** of peers in the Wasm binding (`bigint` or
  string).
- **Scope of "Loro-like":** this draft covers identity only. Loro's other
  features (from memory: Lamport timestamps per op, a peer-ID-compressed
  encoding, movable trees and lists) are out of scope here. Nickel's causal
  basis uses explicit `after` dependencies, so a Lamport clock is not needed
  for admission or replay. If Ren meant more than identity, that needs its own
  proposal.

## 6. What this does not claim

- It doesn't claim the current proofs are wrong. They mention writers only
  through the two definitional sites.
- It doesn't claim a re-proof effort estimate; the solver behaviour after an
  extraction-wide change has to be measured.
- The Loro details are not checked against Loro's current source.
