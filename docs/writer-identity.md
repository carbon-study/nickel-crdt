# Writer identity beyond two writers (draft proposal)

Status: **draft, docs only.** Lynn owns Nickel and reviews this; Ren decides
product choices. It separates three questions and exposes the remaining
choices without adopting them:

1. how a peer identifier is represented;
2. how a producer obtains a fresh identity and avoids reusing counters;
3. which equality and order laws the proofs actually need, and how proofs over
   an arbitrary ordered peer domain reach the concrete Rust type.

Repository facts were checked on `main` at `79ea964`. Loro facts are cited in
§8. Nothing here reopens Loro/Dark decisions or proposes an implementation slice.

**A peer is not a person.** A peer identifier names one operation producer: an
editor session, a device install, or a server process. A person or account may
use many peers, and Nickel has no account concept (`docs/carbon-contract.md`:
"Accounts and devices are not concepts in the library"). Attribution to people
is application data.

## 1. Where the two-writer assumption lives today

**Representation (`src/edit.rs`).**
- `pub enum Writer { Alice, Bo }`; `writer_index` maps Alice → 0 and Bo → 1.
- `impl PartialEq for Writer` compares `writer_index`.
- `event_lt(a, b)` is `writer_index(a.writer) < writer_index(b.writer) ||
  (same writer && a.counter < b.counter)`. `birth_lt` refines it by birth index.

**Where order decides behaviour.**
- Canonical fact order: `choose_unseen` uses `event_lt` (`src/edit.rs:441`).
- FugueMax sibling placement: `birth_lt` breaks ties between concurrent siblings
  (`src/edit.rs:312`, `:314`).
- So *the writer order is visible in text placement*.

**Already generic over the writer value.**
- `EventId { writer, counter }` / `BirthId { event, index }` as identities.
- The per-writer chain in `validate_new`: counter `c > 1` needs `(writer, c-1)`
  in the past, and no same-writer event with counter ≥ `c` may be in the past.
- `Replica { writer: Option<Writer>, next_counter }`: one writer per replica.
- Structural conflict checks (`duplicate`/`fact_equal`,
  `EditIdentity.duplicate_matches_lookup`).

**Proofs that split on the two constructors.**
- `EditIdentity.writer_index_is_exact`: `match writer { Alice => 0, Bo => 1 }`.
  `writer_equality_exact` builds on it.
- `EditAccepted.event_key`: `rank = match f_writer { Alice => 0, Bo => 2^64 }`,
  then `rank + counter`. `event_order_is_key_order` relates `event_lt` to it.
- Other proofs take `Writer`/`Option<Writer>` as an opaque parameter. Example:
  the `new_establishes_*` laws in EditAccepted, EditAtomic, EditCausal,
  EditWellFormed and Spec. But because the type has exactly two inhabitants,
  "for all writers" in every theorem currently means "for Alice and Bo". **No
  arbitrary-peer statement has been proved yet.**

**Mutation modes tied to the enum (`scripts/check-edit-proofs.mjs`).**
- `writer-index-collides`, `identity-writer-equality`, `order-key-ignores-writer`.
- `scheduler-records-wrong-id` and `past-invents-id` build `Writer::Alice` IDs.

**Fixtures and oracles.**
- Native tests use `Writer::Alice`/`Writer::Bo`: `tests/edit_admit.rs` (24),
  `src/edit/causal_basis_tests.rs` (8), `author_replay_tests.rs` (5),
  `basis_filter_tests.rs` (1), `tests/capacity_boundary.rs` (2).
- `scripts/check-rust-edit-reference.py` maps `['Alice','Bo']`;
  `scripts/compare-edit-storage.mjs` alternates them.
- The Python oracle `experiments/combined-admission/admission.py` already
  accepts a third writer (`WRITERS = {'Alice': 0, 'Bo': 1, 'Cam': 2}`).
- Design docs use Alice/Bo as narrative names; they need no change.

## 2. Question A: the peer identifier's representation

Options, none adopted:

| option | sketch | notes |
|---|---|---|
| A1 `Writer(u64)` | opaque 64-bit peer ID | Loro's width (§8); 8 bytes per ID; random allocation is plausible (§3) |
| A2 `Writer(u128)` | 128-bit | collision risk under random allocation negligible for any realistic peer count; 16 bytes |
| A3 opaque bytes | variable-length | most flexible; order and encoding need a defined byte order; heavier proofs and encoding |
| A4 interned index | `u32` into a per-document peer table | compact, but the table is document state and must itself be replicated and ordered; more proof surface |

**Finite width is not a two-producer restriction.**
- Any finite width bounds the *space* of identifiers: 2^64 or 2^128 values. It
  doesn't bound how many producers a history may contain. That number is
  bounded only by the existing history limits (`events`, …).
- Today's enum is a two-producer restriction: the type has two values.
- The proofs must not assume any bound on the number of distinct writers (§4).

**JavaScript.** A1 and A2 exceed JavaScript's safe-integer range, so a Wasm
binding needs `bigint` or a string for peers. `MAX_COUNTER` (2^53 − 1) already
keeps counters JavaScript-safe.

## 3. Question B: fresh identity and counter freshness

Nickel can't make identities unique. It can only detect a structural conflict
when two facts with the same `(peer, counter)` and different contents meet. The
following are **assumptions on the caller**, stated as assumptions and not as
proved properties:

- **B1 single producer:** at any time, at most one producer authors with a given
  peer ID. Carbon's contract already says this: "A replica ID identifies a
  single operation writer… The caller supplies that identity and prevents
  simultaneous reuse".
- **B2 counter continuity across restart:** a restarted producer either resumes
  from its persisted next counter, or takes a new peer ID. Reusing a peer ID
  with a reset counter re-issues `(peer, counter)` pairs. That is exactly the
  conflict Nickel can only detect after the fact.
- **B3 fork/clone:** a cloned replica, or a restored backup, must not continue
  authoring under the original peer ID while the original also does. Either the
  clone takes a fresh peer ID before authoring, or it stays read-only
  (`writer: None`). The continuation doc already notes "cloning supplies no
  fresh writer lease".

Allocation choices, none adopted:

| option | how fresh | assumption it rests on |
|---|---|---|
| C1 random per session | draw a fresh ID whenever a producer starts | probability: about k²/2^(w+1) collisions among k peers for width w; this is a probabilistic assumption, **not** a uniqueness proof |
| C2 random, persisted with the next counter | reuse ID + counter across restarts | B2 holds only if persistence is atomic with authoring; fork/restore hazards (B3) |
| C3 coordinated | an authority issues IDs (server or account service) | availability of the authority; still needs B2/B3 |

A probabilistic collision under C1 is not a safety violation Nickel can prove
absent. If it happens, the outcome is the same as a B1 violation: a detected
conflict when the facts meet, or nothing if they never meet. The contract should
say that explicitly.

## 4. Question C: the laws the proofs need

Every theorem should hold for an arbitrary set of peers. The proofs need only
these properties of writers:

- **L1 equality:** `Writer` equality is decidable and is value equality
  (reflexive, symmetric, transitive). This replaces `writer_index_is_exact` /
  `writer_equality_exact`.
- **L2 strict total order on writers:** irreflexive, transitive and total on
  distinct values.
- **L3 event order:** `event_lt` is the lexicographic order on
  (writer order, counter), hence a strict total order on `EventId` consistent
  with equality.
- **L4 birth order:** `birth_lt` is lexicographic on (`event_lt`, index).
- **L5 order key** (used by EditAccepted): some injective, order-preserving map
  of `EventId` into `nat`. For example `key(w, c) = rank(w) · 2^64 + c` with
  `rank` an order embedding of writers into `nat`. It replaces the two-armed
  `event_key`.

**From an arbitrary ordered peer domain to the Rust type.**
- hax extracts the concrete `Writer`, so theorems are stated over
  `Native.t_Writer`. Making them peer-generic needs two things:
  - **(i)** the concrete type must have more than two inhabitants (any of
    A1–A4);
  - **(ii)** the proofs must use writers *only* through L1–L5.
- Then every theorem holds for any subset of peers that occurs in a history. The
  proof never inspects which peers exist or how many there are.
- To make (ii) mechanical rather than a convention, the proof-reform fence
  refuses writer-constructor patterns and literal writer values in `.lt`
  sources. A small set of named representation lemmas proves L1–L5 once,
  against the concrete type. They are the only declarations allowed to unfold
  the representation.
- An alternative, not proposed for the first step, is an explicit abstract
  interface: an F* type with axiomatised L1–L5, proved generically and then
  instantiated by the concrete type through those representation lemmas.
  Choice (ii) gets the same guarantee with less machinery, provided the fence
  holds.

## 5. Compatibility: the order is observable

`event_lt` orders writer first, then counter, and FugueMax uses it for sibling
ties (§1). So changing the order changes text placement for concurrent
insertions. It is not an ID-format refactor.

Choices, none adopted:

- **O1 preserve the order under an explicit embedding.** Map `Alice ↦ p_A` and
  `Bo ↦ p_B` with `p_A < p_B` in the new peer order, and keep `event_lt`
  lexicographic on (peer, counter). Every existing two-writer history keeps its
  canonical order and placements, and existing fixtures can be ported
  mechanically. Placements between new peers follow peer-ID order. Under random
  allocation that is deterministic but arbitrary.
- **O2 adopt a different tie-break**, such as Lamport time before peer. §8
  explains why this is not attributed to Loro. This **changes placements** relative to today and needs
  Ren's explicit approval, plus re-derivation of any recorded placement
  decisions that depend on the tie-break. Which recorded decisions depend on it
  (q30/q31 and others) has not been checked for this draft.

## 6. Acceptance (for an eventual implementation slice)

- **Proof fence:** refusal fixtures for constructor matches and literal writer
  values. The only permitted unfoldings are the named representation lemmas.
- **Re-proofs:** L1–L5 against the concrete type, plus the existing theorems
  re-checked over it, with no premise bounding the number of distinct writers.
- **Native fixtures with at least three peers.** They must include:
  - sparse and high IDs, for example `0`, `1`, `2^32`, `2^63`, `u64::MAX - 1`
    and `u64::MAX` under A1;
  - a peer order different from creation order;
  - concurrent sibling insertions by three peers, with the expected placement
    stated from the chosen order (O1 or O2).
- **Mutation modes** keep their fault meanings with new anchors, and gain one
  only sparse IDs can catch: for example, equality or order comparing only the
  low bits.
- **O1 only:** a ported-fixture check that every existing two-writer fixture
  yields identical canonical order and placements under the embedding.
- **Solver margins:** the representation change alters extraction everywhere.
  Queries near their budget (one is at 76% today) are re-measured on that change,
  not assumed stable.

## 7. Possible order of work (not a plan)

1. The fence, with the two current definitional sites excluded by name. Every
   other proof is then already compliant, and later slices cannot regress.
2. The representation (A*), L1–L5 representation lemmas, re-anchored modes,
   removal of the exclusions, regenerated hax and receipts.
3. Fixture port (O1 embedding, or O2 re-derivation) and many-peer fixtures.
4. Contract and documentation text: the peer order as the stated tie-break, and
   the B1–B3 caller assumptions.

## 8. Prior art: Loro

The mechanism used as prior art is Loro's **(peer, counter) operation ID with a
random per-session 64-bit PeerID and explicit single-writer pitfalls**. Sources
are docs.rs for `loro` 1.17.1 and the Loro repository; loro.dev itself refused
automated fetching, so its pages were not read.

- `pub type PeerID = u64;`, documented as "Unique id for each peer. It's a
  random u64 by default."
  ([docs.rs PeerID](https://docs.rs/loro/latest/loro/type.PeerID.html))
- `pub struct ID { pub peer: u64, pub counter: i32 }`, documented as "the unique
  ID of an Op represented by PeerID and Counter."
  ([docs.rs ID](https://docs.rs/loro/latest/loro/struct.ID.html))
- From the `LoroDoc::set_peer_id` pitfalls: "Never reuse the same PeerID across
  concurrent writers (multiple tabs/devices). Duplicate PeerIDs can produce
  conflicting OpIDs and corrupt the document." Also: "Do not assign a fixed
  PeerID to a user or device without strict single-ownership locking. Prefer the
  default random PeerID per process/session."
  ([docs.rs LoroDoc](https://docs.rs/loro/latest/loro/struct.LoroDoc.html))
- `LoroDoc::fork`: "Duplicate the document with a different PeerID". This is the
  same hazard as B3, answered by forcing a fresh identity on fork (same page).
- A repository design note records the consequence of shared peer IDs. Before a
  fix, an import "either panicked … or it returned `Ok` with scrambled text";
  detected cases now fail with `LoroError::UsedOpID`
  ([context/import-peer-id-reuse.md](https://github.com/loro-dev/loro/blob/main/context/import-peer-id-reuse.md)).
  This is internal design material, not user documentation.

This supports §3's framing: random allocation is a convention with stated
pitfalls, not a uniqueness guarantee. Reuse is detectable at best after the fact.

**Not established from the sources read:**
- how Loro tie-breaks concurrent text/list insertions. Loro also has Lamport
  timestamps (`pub type Lamport = u32`), but the pages read don't say they
  decide placement;
- any guidance on persisting a peer ID across restarts.

So O2 (§5) is a generic alternative, not a description of Loro's rule.

## 9. What this draft does not claim

- That any arbitrary-peer theorem holds today; none has been proved.
- That random identifiers are unique; §3 states that as an assumption.
- An effort estimate for the re-proofs.
- Anything about Loro beyond the cited mechanism; no Loro/Dark decision is
  reopened.
