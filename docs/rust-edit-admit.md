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
first matching entry. The indexed-member theorem requires unique IDs; their
preservation by canonicalization is **not yet proved**. Freshness here means
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

Thirteen independently extracted wrong Rust bodies must fail native tests and the
unchanged relevant lemma. Three corrupt/reuse the counter on earlier return
paths. Five challenge the positive boundary: alter the returned fact's gap,
commit a stale tree, change the receiver's counter on success, ignore the caller's
gap before validation, or gate admission on the receiver's private writer.
Five identity controls ignore the gap, accept conflicts, skip the scan, ignore
the counter range, or erase the event counter from custom equality. Each is
required to fail its own named theorem, not merely another module.
The check rejects timeouts/extraction errors as control results. Extracted project
code and authored views contain no own admissions. Trust remains with Rust,
hax, the external Rust models, private Latte emission, F* and its solver.

## remaining exit

Define the edit-only whole-instance abstraction and well-formedness predicate,
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
