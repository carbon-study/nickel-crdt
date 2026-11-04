# experimental Rust edit/admit candidate

Two separately owned `Replica`s can author one insertion, deletion or replacement
and pass the returned immutable `Fact` to each other. The receiver rebuilds the
FugueMax retained-node order from each fact's causal author basis. No Python,
Node or network call runs inside the Rust library.

This implements the first edit-only boundary of the
[Rust transition cut](rust-transition-cut.md), following Ren's implementation
go-ahead. It is **not the verified slice's exit**: semantic refinement,
representation and delivery-independence theorems are still missing. The return-path and commit-coherence lemmas below do not prove those properties. This also
does not complete the roadmap's experimental milestone, which includes history.

## using the boundary

```rust
use nickel_crdt::edit::*;
let alice = Replica::new(Some(Writer::Alice), Limits::default()).unwrap();
let bo = Replica::new(Some(Writer::Bo), Limits::default()).unwrap();
let (alice, result) = alice.edit(0, vec!['a' as u32, 'b' as u32], vec![]);
let Local::Authored(fact) = result.unwrap() else { unreachable!() };
let (bo, result) = bo.receive(&fact);
assert_eq!(result, Ok(Admission::Added));
assert_eq!(alice.observe(), bo.observe());
```

Each call consumes and returns the complete instance, including on failure.
The caller replaces its old handle with the returned one. Successful local
work returns the fact **after** trial admission and final capacity checks;
there is no callback before commit. A replacement names the IDs it deletes,
its inserted scalar values, and a gap in the author's **pre-edit** visible
sequence. One call is one primary edit; grouping and child edits are absent.

`receive(&fact)` borrows a caller-owned structured fact. Exact duplicates return
`Duplicate`; a changed field under an accepted ID returns `Invalid(Conflict)`.
Equality includes dependency/target list order and the original gap; it is not
semantic equivalence of two differently packaged facts. `Missing`, `Capacity`
and `Internal` return the unchanged instance. The caller must retain the fact
for retry or diagnosis: **Internal is not evidence that a fact is invalid**.
There is no inbox, acknowledgement, transport or automatic retry in this crate.
Allocation failure/process death is outside these ordinary return-path claims.

`whole()` returns retained birth IDs, including deleted text; `observe()` returns
the visible ordered `(BirthId, u32)` pairs. Unicode scalar values are preserved
exactly, including CR, LF, NUL, BOM and supplementary-plane values. This is not
UTF-16 indexing or a normalization interface.

## domain and representation

The closed writer set is Alice and Bo. `None` creates an observer that cannot
author. Each writer must have **one externally fenced producer for the entire
document lifetime**, whose allocator is never reset. Starting another producer
and importing its old facts is not supported recovery. Admission does not
advance its local allocator; importing old own-writer facts into a fresh
producer can therefore cause an ID conflict on its next edit. Writer tags are
consistency inputs, not authenticated identities or a Byzantine protocol.

An event ID is `(writer, counter)`, with counters in `1..=2^53-1`. A birth ID
adds its scalar's index within the event. Insertions derive their IDs from that
index; callers cannot pair a different birth ID with a scalar. The same-writer
predecessor must be in the fact's causal closure. A fact's deletion targets must
be visible in that closure, independently of additional receiver facts.

Default experimental ceilings: 128 accepted events, 512 retained births,
64 scalars per fact, 64 direct dependencies per fact, 512 deletion targets per
fact, and 1536 logical ordering links. `Replica::new` allows smaller ceilings,
not increases beyond this profile. Ordering links count three parent/origin
slots per retained birth, including sentinels. **They do not bound heap usage,
child arrays, temporary clones, replay time or input allocation.** Deletions do
not reclaim retained births. Full reconstruction and repeated author snapshots
are deliberately expensive; no incremental index or useful-scale claim is made.
The [native latency diagnostic](#native-latency-diagnostic) below makes that
limitation concrete; the profile ceilings are not interactive-latency budgets.

### capacity is an admission boundary, not a synchronization policy

At an aggregate ceiling, the same **offered** facts can leave different
**accepted** subsets. This is an executable limitation of the current candidate:
two observers accept root `x`, then receive concurrent append facts `y` and `z`
in opposite orders. With room for only one of them, their texts remain `xy` and
`xz`. This happens independently at the event, retained-birth and ordering-link
ceilings. Both producers can author their branches under that same small
profile: local fit does not ensure that their concurrent union fits. The
second addition returns `Capacity` without changing either
instance. Repeating the rejected offer against that unchanged full instance
still returns `Capacity`; retaining a fact is not a progress guarantee.

Run the retained negative boundary witnesses and fitting-history controls with:

```sh
cargo test --offline --locked -p nickel-crdt --test capacity_boundary -- --nocapture
```

These tests deliberately demonstrate the limitation; their passing does **not**
close a convergence obligation. They also reconstruct fresh read-only observers
from all caller-retained offers under a larger fitting profile and check exact
agreement. This is a finite control, not an implemented promotion/inbox API,
producer/allocator recovery, or a solution beyond the hard experimental ceiling.
Reconstruction from only one observer's accepted facts would omit the other
branch's failed offer. Deletion does not reclaim these retained resource counts.

The [fixed-fact/prefix-budget obligation](rust-transition-cut.md) already
requires a valid fitting final fact set and eventual admission; it explicitly
excludes differing accepted subsets at capacity. For such a fitting set,
prefix-monotone aggregate measures can support an admission/progress argument.
That argument, valid-input admissibility and internal-error unreachability still
need implementation-linked proofs. Equality for the same accepted fact set is
distinct from convergence after the same offers, including over-budget offers.

No over-capacity synchronization policy is selected. Changing the checks to use
only a fact's causal past would permit concurrent facts to exceed the present
aggregate ceiling. Per-writer reservations, coordinated budgets or a different
retention/retry protocol would each change the resource contract and need their
own agreement/progress/boundedness account. Merely documenting caller retention
or proving rejection neutrality does not supply that account.

The Rust profile is an edit-only projection of the two-writer Python/Node
reference. Its `Fact` is already typed, and its derived birth IDs replace the
reference's independently supplied birth/payload fields. It has no JSON-byte
ceiling because there is no selected portable encoding. Comparison fixtures
are restricted to facts fitting both profiles; they do not prove equal admission
for arbitrary Python packets or over-budget inputs. No release budget or public
wire format is selected by these experimental ceilings.

## checks and what they establish

```sh
cargo test --offline --locked -p nickel-crdt --test edit_admit
nix build --no-link .#edit-reference
nix build --no-link .#proofs
```

The native tests use the public crate API for two-instance replacement,
exact duplicates/changed-gap conflicts, concurrent deletion at the author's last
gap, separate-event prepend runs, scalar validity, missing prerequisites and
final ordering-budget rejection. Failed calls compare the **whole instance**,
including facts, tree, limits and private counter, not just the displayed text.

The separate native consumer `examples/edit-reference.rs` authors fixtures using
only public calls, and admits every legal causal delivery order. It supplies
150 histories / 882 schedules: six directed cases and all 144 combinations of
two insertion gaps per offline writer on `ab`. Python then compares them with
actual `Combined(Oracle('fugue'))`: retained ID order, visible IDs and exact
scalar text. The JSON is an internal test artifact, not a serialization API.
Within Rust, equality across arrival permutations is **structural replay agreement**:
`canonical` sorts accepted facts and `interpret` picks one deterministic ready-fact
order. These tests do not vary that internal choice or prove arbitrary topological
replay equivalence. Fixed expected strings discriminate selected placements; the
separate Python/Node comparison supplies an independent finite ordering oracle.
This is finite agreement with a reference, not a convergence or refinement proof.

`proofs/EditAtomic.lt` checks the **actual freshly extracted Rust entry points**:

- every admission error and exact duplicate returns the entire original instance;
- every local error or empty result returns the entire original instance;
- an authored edit advances the counter exactly once, and its returned fact uses
  the before-counter.

These quantify over all well-typed extracted input states and arguments, not
only generated histories. `proofs/EditCommit.lt` adds a positive joint boundary:

- a returned authored fact carries the requested scalar list, deletion targets,
  gap (absent for deletion-only work) and local writer;
- receiving that exact fact into the same before-instance returns `Added` with
  exactly the local commit's complete accepted facts and retained tree;
- admission preserves the receiver's writer, allocator and limits on every
  disposition, including success;
- two states with the same complete facts, tree and limits have identical
  admission dispositions and next shared state, independently of their private
  writer/allocator values;
- therefore, if a local edit authors a fact, a second instance starting with that
  same shared state admits it as `Added` and reaches the same complete shared
  state, while retaining its own writer and counter.

The last theorem is about **two actual Rust calls**, not a rewritten replay
algorithm. Its premise requires the same accepted history/tree/limits before the
edit; it does not cover a receiver with extra concurrent facts. It is conditional
on authoring succeeding, not a theorem that every valid fitting request succeeds.
Eight native tests include successful insert/replace/delete continuation with a
separate receiver whose writer and allocator differ, alongside replay into a
copy of the author's before-state. These make the exercised success branches
non-vacuous; finite examples do not establish general admissibility.

The private-state proof is kept structural by making new-fact validation return
only `Result<(), Error>`, with accepted facts and limits as explicit inputs.
Duplicate classification similarly returns only a disposition. Trial assembly
still owns the whole publication; no validator can return a replacement instance.
The checks and their order are unchanged by this Rust refactor.

### identity classification and event-ID freshness

`proofs/EditIdentity.lt` relates the actual Rust identity scan to an independent,
recursive first-ID lookup using structural fact equality. It then connects that
lookup to the public calls:

- an existing ID in a state with unique accepted IDs returns `Duplicate` for
  exactly equal facts, and `Invalid(Conflict)` for any different fact; either
  returns the entire before-instance, without invoking new-fact validation;
- an out-of-range counter returns `Invalid(Counter)`, even before lookup;
- every `Added` result has an event ID absent from all before-facts;
- every successfully authored local fact likewise has a fresh event ID, by the
  same-commit theorem and actual receiving call.

The lookup theorem itself permits arbitrary duplicate IDs and specifies the
first matching entry. The indexed-member theorem requires unique IDs. The accepted-ID invariant below
now establishes that premise for states built through the public constructor
and retained through public calls. Freshness here means
absence from this instance's accepted event IDs. It does not prove global
producer fencing, allocator progress, birth/scalar correspondence, or that a
valid request succeeds. The freshness theorems need no well-formedness premise.

The scan now uses a range loop so its early returns are interpreted through the
checked LoopUtil bridge. The previous generic-iterator fold is opaque at the
pinned model boundary. This is a representation change, with the same scan order.

A source-trust pitfall was reproduced while making this connection: the pinned
F* backend lowers Rust `PartialEq::eq` operator calls to structural equality,
without following a custom comparison body. Removing the gap comparison from
`Fact::eq` changed the native conflict result but left the old extracted scan
unchanged. The identity-critical comparison is now an ordinary `fact_equal`
call, whose extracted body is checked against structural equality. Separate
lemmas check the handwritten writer/event/birth equality bodies; the gate also
requires the ordinary fact call to remain present in the extraction. This
repairs that proof blind spot; it is not an audit of all hax translations.

Independently extracted wrong Rust bodies must fail native tests and the
unchanged relevant lemma. Three corrupt/reuse the counter on earlier return
paths. Six challenge the positive boundary: alter the returned fact's gap or its
`after` list, commit a stale tree, change the receiver's counter on success, ignore the caller's
gap before validation, or gate admission on the receiver's private writer.
Eight identity controls ignore the gap, accept conflicts, skip the scan, ignore
the counter range, compare only counters in the scan key, or corrupt custom
event/birth/writer equality (erase the counter, erase the index, or compare the
writer with itself). Each is
required to fail its own named theorem, not merely another module.
The check rejects timeouts/extraction errors as control results. Extracted project
code and authored views contain no own admissions. Trust remains with Rust,
hax, the external Rust models, private Latte emission, F* and its solver.

### accepted event-ID invariant

`proofs/EditAccepted.lt` closes one component of well-formedness through the
actual constructor, canonicalizer and public calls:

- the native membership scan agrees with the independent recursive first-ID
  lookup, so a negative result really means absence at every bounded index;
- the actual selection scan chooses only an in-range input fact whose ID is
  absent from its output accumulator;
- appending that fact preserves unique IDs, and the actual canonicalization
  loop therefore returns unique IDs whenever it succeeds, for any input slice;
- successful trial publication retains exactly the canonicalizer's accepted facts;
  the final tree-installation function cannot replace them;
- every public `receive` that returns `Added` has unique accepted IDs;
- `Replica::new` establishes unique IDs; both `receive` and `edit` preserve
  them on **all ordinary return paths**, assuming them before the call.

The all-path theorems combine the positive canonicalization result with the
existing full-instance error/duplicate/empty neutrality lemmas. The local case
uses the actual author/receive same-commit theorem. This supplies the unique-ID
premise required by known-member classification without trusting a caller's
claim about the rebuilt tree. It is an event-ID invariant, **not full edit WF**:
causal closure, canonical ordering, scalar/birth/tree
correspondence, allocator progress and semantic refinement remain open. It does
not establish that a valid fitting request succeeds, or justify an Internal
result as invalidity.

To expose the checked loops, the membership helper now scans an indexed range,
and the unchanged canonicalization selection and append bodies are factored
into private functions. Final tree installation is also factored so its
fact-set preservation is a separate source-linked obligation. No guard,
comparator or successful publication rule
was added or removed. These implementation refactors retain the byte-identical
finite reference output; that comparison is not a general equivalence proof
between the old and factored programs. LoopUtil's generic preservation adapter
requires actual semantic preservation premises, separately discharged here;
hax's default loop annotation is not treated as proof of the invariant.

Three additional controls break this boundary: allow a previously selected ID,
append input element zero instead of the selected element, or duplicate a fact during
final tree installation before joint publication. Each must
fail native tests and its unchanged named selection/append/tree-installation theorem.
The last control tests the real public commit, not just a standalone helper.

### exact successful fact contents

The same source-linked module now checks the successful publication's content:
old whole facts remain unchanged, the offered fact (or returned authored fact)
is present unchanged, no other whole fact is introduced, and accepted length
increases by exactly one. The actual canonicalizer selects whole input facts;
its successful result has input length and unique IDs. A finite pigeonhole
argument, using the pinned F* standard library, establishes coverage of every
input position. The proof then follows the actual plan/publication and public
receive/edit calls. It requires no extra before-WF premise for this conditional
successful-return statement; it does not establish that valid fitting input
will successfully return.

This does not identify canonical order with the intended order, validate causal
closure/scalars, relate the tree to semantic interpretation, prove convergence
or repair the capacity boundary. Those remain separate exit obligations.
Changing a selected fact's gap or omitting the canonical loop must fail native
public-state checks and the corresponding unchanged named content theorem.

## native latency diagnostic

Build the manual public-API diagnostic separately from its timed runs:

```sh
cargo build --release --offline --locked --example edit-profile
for shape in append prepend frontloaded-delete; do
  timeout --kill-after=2s 45s target/release/examples/edit-profile "$shape" > "$shape.jsonl"
  echo "$shape exit=$?"
done
```

Each line is emitted only after both authoring and receiving succeed and both
instances' exact visible IDs/scalars and retained IDs match a separately
maintained sequential-list expectation. Append/prepend insert four scalars per
event. Frontloaded-delete inserts eight 64-scalar batches, then deletes one
occurrence per event, retaining all 512 births. Completed runs also check that
event 129 rejects without changing the author. This is a diagnostic, not a
routine CI timing assertion; every process has a 45-second external cap.

One optimized local run at `5545111` on 2026-11-04, x86_64 Intel i9-12900KF
(before the proof-oriented helper factoring above):

| shape | last checked events / retained births | last author / receive | sum of checked author + receive calls | outcome |
|---|---|---|---|---|
| append | 128 / 512 | 483 / 482 ms | 28.19 s | completed |
| prepend | 128 / 512 | 506 / 519 ms | 30.37 s | completed |
| frontloaded-delete | 63 / 512 | 700 / 694 ms | 43.85 s | external timeout (124), incomplete |

Observation/assertion and build time are excluded from call timers; author time
includes copying the request vectors. The sums exclude any interrupted call.
This shared machine was not CPU-isolated, and focused proof checks overlapped
part of the run. These are observations, not stable benchmark estimates, maxima
over valid histories, or ARM/phone predictions. No memory measurement is supplied.
In particular, the third row does **not** establish latency at 128 events.

The candidate is already too slow for interactive editing on these modest
histories: one author/admit call can take about half a second at the ceiling,
and keeping births after deletion can be worse before reaching that ceiling.
The ceilings bound selected counts, not useful latency. A usable implementation
needs to avoid reconstructing every author's tree on every admission; this
measurement does not select an incremental representation or verify one. The
current reconstruction remains the experimental reference path while its
semantic/WF obligations are discharged. It is not a performance-ready engine.

The subsequent [source-bound storage comparison](edit-storage-comparison.md)
tests maintained ID-sorted insertion in isolated crate copies, with separate
validation/storage/replay timings. It matches the finite native/reference
fixtures but does not adopt or prove a new library path. On those measured
histories, replay consumes over 99.8% of the measured plan-phase time; cheaper
fact storage does not repair interactive latency. The comparison owns commands,
input hashes, capped failures and the next representation/proof boundary.

The subsequent [derived-node cache experiment](derived-node-cache.md) gives a
conditional source argument for causal-past locality and tests a per-instance
cache in isolated copies. Its correctness path compares complete trees to full
replay; its timing path omits that guard and completes the three bounded shapes.
The general locality/cache invariant remains unproved, and the ordinary library
continues to use full replay. The experiment also identifies the explicit
representation-domain issue for the existing shared-history theorem.

## remaining exit

Extend the accepted-ID component to the edit-only whole-instance abstraction
and full well-formedness predicate,
then prove local/admission semantic refinement and preservation, including every
error category. Prove the frozen-origin FugueMax representation relation,
ID/scalar correspondence, causal schedule independence and prefix-budget
progress for this profile. The tested internal-error branch must be shown
unreachable for valid fitting facts, rather than being called a rejection oracle.
Until these hold together, this remains an executable candidate with checked
transactional return paths, **not a verified edit/admit slice**.

Undo/Redo/Restore, private history/checkpoints, inspection capabilities, grouping,
anchors, registers, incremental receipts, byte codecs, persistence, authentication,
bindings and consumer UI are absent. Pending new-work redo and exact returning-ID
choices remain open; implementing this cut does not silently settle them.

## counter-control gate follow-through

The ARM gate at `bf611c8` failed because the reused-counter negative check did
not finish within the verifier driver's 60-second budget. That was correctly
rejected, not accepted as mutation detection. It is not evidence that the
positive content theorem is false.

The existing guard/successor calculation is now a pure native helper, with a
source-linked result/error lemma. The instance still installs the calculated
counter only after plan success. The public whole-edit counter theorem is
unchanged. The reused-counter control checks the actual helper through
`EditAtomic`; the full positive still checks all the public proofs through
`EditAccepted`. Budgets and proof-integrity requirements are unchanged. This
primitive counter calculation is not global writer fencing or a proof of valid
fitting edit/admission progress.
