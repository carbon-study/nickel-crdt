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

**A peer is not a person.** A peer identifier names one operation producer, such
as one editor session or one server process. It is not a device, since one
device can run several sessions at once (§3.3). A person or account may use
many peers, and Nickel has no account concept (`docs/carbon-contract.md`:
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
- No other *authored* match or writer literal was found. That doesn't make the
  other proofs independent of the two-element type. Every statement quantifies
  over `Native.t_Writer`, whose hax definition is the two-constructor datatype.
  The SMT context can exploit that finite domain (for example by case analysis
  on an inductive) without any authored match. So "for all writers" currently
  means "for Alice and Bo", and **no arbitrary-peer statement has been proved**.
  Only re-verifying the theorems against an enlarged representation would
  establish one (§4).

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
| A1 `Writer(u64)` | opaque 64-bit peer ID | Loro's width (§8); 8 bytes is the raw field width, not a wire-encoding promise (no codec is proposed); random allocation is plausible (§3) |
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

### 3.1 What the current API supplies

- `Replica::new(writer, limits)` always starts with `next_counter: 1` and no
  facts. `next_counter()` is a getter; there is no operation that restores a
  replica's counter or facts.
- So **a same-peer restart is not possible through today's API.** A caller who
  persists the counter externally cannot hand it back. Calling `new` with the
  same peer ID would re-issue `(peer, 1)`, `(peer, 2)`, … as different
  operations.
- Nickel's counters start at 1 and are capped at `MAX_COUNTER`. Loro's start
  at 0 (§8). The difference matters only for porting fixtures or encodings.

### 3.2 The boundary: two choices, none adopted

- **R1 fresh peer per replica construction** (for a first profile): every
  `Replica::new` that may author is given a peer ID never used before in that
  document's namespace. Restart, reload, crash recovery, fork and opening a
  second tab all mean a new peer. Nothing in Nickel needs to change for this.
- **R2 recovery as a prerequisite:** a checked restoration API, restoring facts
  and the next counter together with a no-reuse argument, is listed as work that
  must exist *before* same-peer restart is offered. It is not designed here.

### 3.3 The no-reuse invariant (a caller obligation, not a proved property)

Within one document's namespace, a `(peer, counter)` pair names at most one
operation, ever. This must survive:
- **crash** between authoring and persisting: under R1 the next start is a new
  peer anyway;
- **rollback to an old backup or snapshot:** the restored state may be behind
  operations that already escaped to other replicas. Reusing its peer, even with
  its saved counter, can re-issue escaped IDs;
- **concurrent tabs, processes or devices** opening the same document;
- **fork or clone of producer state:** a copy is not a second independent
  producer with that identity. It must take a fresh peer before authoring, or
  stay read-only (`writer: None`). The continuation doc already notes "cloning
  supplies no fresh writer lease".

Uniqueness is scoped to the document (or session) namespace. It is not about
people, devices or accounts: a person uses many peers, and a device can run many
sessions.

### 3.4 Allocation and its assumptions

| option | how fresh | what it assumes |
|---|---|---|
| C1 random per construction | draw a fresh ID for each authoring replica | the collision assumption below; this is not a proof of freshness |
| C2 coordinated | an authority issues IDs | the authority never re-issues; it is available when a replica starts |
| C3 reused from a locked cache | as in Loro's guidance (§8) | needs R2 plus exclusive ownership; not available with today's API |

**Collision assumption under C1:** with k independently and uniformly drawn
w-bit IDs, the probability that any two collide is about k²/2^(w+1). That
estimate holds only in the low-collision regime k ≪ 2^(w/2), and only if the
draws really are independent and uniform; a weak or cloned RNG state breaks
both. Under that assumption a collision is a probabilistic risk, not something
Nickel can prove absent.

**What Nickel's structural checks are not.** `duplicate`/`fact_equal` reject
two facts with the same ID and different contents *when they meet in one
replica*. That is detection after the fact. It is not an allocator, not
authentication, and not a recovery mechanism for a collision or a reuse.

## 4. Question C: the laws the proofs need

The goal is that every theorem holds for an arbitrary set of peers. The
proposal is that proofs use writers only through these properties:

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

Removing the two-writer dependence is a re-verification result, not a syntax
property. The exit is: the relevant universal theorem families are re-verified
against an enlarged representation, through a checked equality/order bridge
(L1–L5). Their substantive statements are unchanged, and discriminating controls
show the bridge matters. Two targets are possible, and they are not the same:

- **T1 all concrete peers.** Re-verify every theorem over the concrete extracted
  type, for example all `u64` peers under A1. This removes the two-writer
  restriction, but it stays representation-specific: the theorems are about
  `u64` peers.
- **T2 a representation-independent ordered-peer interface.** State L1–L5 as an
  explicit interface (an ordered peer type with equality and order laws). Prove
  the theorem families against the interface, then discharge checked
  instantiation obligations for the concrete type. A `u64` field and three-peer
  fixtures do not by themselves establish T2.

Neither target may introduce new trusted project axioms, or assume its own
conclusion. Under T2, the interface laws are obligations the concrete instance
must prove, not postulates.

**What the fence does and doesn't do.** A proof-reform rule that refuses
writer-constructor patterns and literal writer values in `.lt` sources is an
*authored-syntax regression guard*. It stops new explicit case-splits, and it
can confine representation unfolding to the named L1–L5 lemmas. It cannot stop
the SMT context from exploiting a finite inductive domain. That is why the exit
above is re-verification over the enlarged type, not the fence.

## 5. Compatibility: the order is observable

`event_lt` orders writer first, then counter, and FugueMax uses it for sibling
ties (§1). The order therefore reaches text placement for concurrent
insertions.

**The compatibility embedding (proposed, preserves current behaviour).**
- Map `Alice ↦ Writer(1)` and `Bo ↦ Writer(2)`. Counters and birth indices are
  unchanged.
- Keep `event_lt` lexicographic on (numeric peer order, counter), and keep
  `birth_lt` lexicographic on (`event_lt`, index).
- Because `1 < 2` matches today's `Alice < Bo`, this keeps the existing
  writer-first tie policy. It is not a new placement decision, and it does not
  need re-approval.
- Its obligations: the embedding preserves equality, `event_lt` and `birth_lt`,
  and every existing two-writer fixture yields the same canonical order and
  placements under the ID renaming.
- Among new peers, ties follow numeric peer order. Under random allocation that
  is deterministic but arbitrary.

**A changed order is a separate behaviour proposal.** For example, Lamport time
before peer would change placements relative to today. It would need its own
proposal and Ren's approval, plus re-derivation of any recorded placement
decision that depends on the tie-break. Nothing here proposes one. §8 explains
why no such rule is attributed to Loro.

**Convergence is not established by a shared order.** A common, deterministic
tie order is necessary for replicas to make the same tie decisions. It is not
sufficient for Nickel's open convergence and placement obligations. "Replicas
with the same facts produce the same document, for any number of peers" remains
a proposed theorem obligation. Its premises (history well-formedness, the
no-reuse invariant of §3.3, and the refinement from Rust to the reference
semantics) must be stated in the theorem.

## 6. Acceptance (for an eventual implementation slice)

- **Re-verification:** the relevant universal theorem families are re-checked
  against the enlarged type, for the chosen target (T1 or T2). Their statements
  are unchanged, and no premise bounds the number of distinct writers. Under T2,
  the concrete instantiation obligations are discharged, and nothing is
  postulated.
- **Fence**, as a regression guard: refusal fixtures for constructor matches and
  literal writer values, with the named L1–L5 lemmas as the only permitted
  unfoldings.
- **Native fixtures with at least three peers.** They must include:
  - sparse and high IDs, for example `0`, `1`, `2`, `2^32`, `2^63`,
    `u64::MAX - 1` and `u64::MAX` under A1;
  - a peer order different from creation order;
  - concurrent sibling insertions by three peers, with the expected placement
    stated from numeric peer order.
- **Mutation modes:**
  - each keeps its fault meaning under new anchors, and must fail for its
    intended reason (native and owner theorem) through the existing gate;
  - a low-bit comparison fault is added. Two suitably sparse peers such as `0`
    and `2` expose it; three peers alone are not a semantic oracle.
- **Compatibility:** under the `Alice ↦ 1, Bo ↦ 2` embedding, every existing
  two-writer fixture yields the same canonical order and placements.
- **Solver margins:** the representation change alters extraction everywhere.
  Queries near their budget (one is at 76% today) are re-measured on that change,
  not assumed stable.

## 7. Possible order of work (not a plan)

1. The fence as a syntax regression guard, with the two current definitional
   sites excluded by name. This blocks new explicit case-splits. It does not
   establish independence (§4).
2. Choose T1 or T2, and the restart boundary (R1 or R2 as a prerequisite).
3. The representation, L1–L5, re-anchored modes, removal of the exclusions,
   regenerated hax and receipts, and re-verification.
4. The fixture port under the embedding, and many-peer and sparse-ID fixtures.
5. Contract text: numeric peer order as the stated tie-break (preserving today's
   writer-first order), and the §3.3 no-reuse obligation.

## 8. Prior art: Loro

The mechanism used as prior art is Loro's **per-instance random 64-bit PeerID
with `(peerId, counter)` operation IDs, plus controlled reuse that requires
persisted state and exclusive ownership.** It is cited only as prior art; no
Loro work is proposed.

Sources:
- the loro.dev pages *PeerID Management* and *Tips and Tricks*, read from the
  site's source repository `loro-dev/loro-docs` at `fed8589`
  (`pages/docs/concepts/peerid_management.mdx`, `pages/docs/tutorial/tips.mdx`),
  because loro.dev refuses automated fetches;
- docs.rs for the Rust aliases.

**Identity and counters** (*PeerID Management*):
- "**Peer ID**: A 64-bit unique identifier for each client/session".
- "**Operation ID**: Combination of `(peerId, counter)` that uniquely identifies
  each operation".
- "**Counter**: Monotonically increasing number starting at 0 for each peer",
  described as "Monotonic, continuous, per-peer, persistent". Nickel's counters
  start at 1 (§3.1).
- In JavaScript the peer is a string, "because 64bit integers are not supported
  in JS". This bears on §2's JavaScript note.

**Fresh by default** (*PeerID Management*):
- "New peer ID generated for each `LoroDoc` instance, even when loading same
  document."
- *Tips and Tricks* repeats this: "`LoroDoc` will be initialized with a new
  random PeerID each time". This is the R1/C1 shape of §3.

**Controlled reuse** (*PeerID Management*):
- "If you intentionally reuse a Peer ID, persist the document's local data
  (snapshot, updates, or durable cache) alongside that ID and load it before
  fetching or applying any remote updates."
- "Skipping this step risks generating a new operation that reuses an existing
  operation ID, which leads to inconsistent replicas."

**Exclusive ownership and why** (*Tips and Tricks*):
- "you must avoid having two parallel peers use the same PeerId".
- Reuse needs "a local PeerId cache with proper locking mechanisms" so that "only
  one tab [can] 'take' a specific PeerId". This is the C3 shape of §3.4.
- Do not tie a peer to a user ("one user might use multiple devices") or to a
  device ("multiple tabs might open the same document simultaneously").
- The reason: Loro "determines whether an operation has already been included by
  checking its operation ID", so duplicate IDs can make it "incorrectly assume
  certain operations have already been processed".

**Rust types** (docs.rs, `loro` 1.17.1):
- `pub type PeerID = u64;` ("It's a random u64 by default").
- `pub struct ID { pub peer: u64, pub counter: i32 }`.
- `LoroDoc::fork` duplicates "the document with a different PeerID". This is the
  fork rule of §3.3.

**Not taken from Loro:**
- Loro's rule for ordering concurrent text/list insertions. The pages read don't
  state it, so no tie-break here is attributed to Loro. Nickel keeps its own
  writer-first order (§5).
- Any numeric collision analysis. The pages read give none; §3.4's estimate and
  its assumptions are this draft's own.

## 9. What this draft does not claim

- That any arbitrary-peer theorem holds today; none has been proved.
- That the fence establishes independence from the writer count; it is a
  syntax guard (§4).
- That a shared tie order implies convergence; that remains a theorem obligation
  (§5).
- That a same-peer restart works through today’s API; it does not (§3.1).
- That random identifiers are unique; §3 states that as an assumption.
- An effort estimate for the re-proofs.
- Anything about Loro beyond the cited mechanism; no Loro/Dark decision is
  reopened.
