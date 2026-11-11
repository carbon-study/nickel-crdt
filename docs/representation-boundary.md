# Representation boundary: runs and the incremental tree (draft proposal)

Status: **draft, docs only.** Lynn owns Nickel and reviews this; Ren decides
scope and priority. Repository facts were checked on `main` at `30a8435`.

Ren's requirement: *the proofs must not depend on things we plan to change.*
Two representation changes are planned or proposed:

- **storage runs:** store several consecutive births as one tree entry, instead
  of one node per character (proposed; not yet on the roadmap). These are
  distinct from authored runs (§1);
- **the incremental tree:** maintain the tree across admissions instead of
  rebuilding it from all facts. The continuation plan's §5 places this after the
  semantic and progress boundary
  ([edit-admit-continuation.md](edit-admit-continuation.md)), as a post-v0.1
  item.

This draft proposes a two-layer rule, inventories which current proofs sit in
which layer, and states the obligation each future representation would
discharge. It adopts no representation and starts no implementation.

## 1. What two implementations must preserve

Take two implementations of the same API, for example today's rebuilt
per-character tree and a future packed or incremental one. Started from
corresponding states, and given the same call (`edit` or `receive`), they must
agree on:

1. **scalar identities and content:** the same `BirthId { event, index }`
   exists, with the same scalar, in both. No identity is merged, renumbered or
   lost by storage. Every `BirthId` stays individually addressable for later
   targeting: deletion targets (`Fact.delete`), insertion gaps and future
   anchors.
2. **retained order:** `Replica::whole()`, the sequence of every birth,
   including hidden ones, is equal.
3. **visible order and content:** `Replica::observe()`, the visible
   `(BirthId, scalar)` sequence, is equal.
4. **author-basis placements:** for each event, its placement is computed against
   the author's basis, as in #86/#87, and gives the same position in the whole
   order. That holds even when the receiver holds extra concurrent facts.
5. **public outcomes:** the same result on every path:
   - `edit` returns `Local::Empty`, or `Local::Authored(fact)` with an equal
     fact (identity, `after`, `insert`, `delete`, `gap`);
   - `receive` returns `Admission::Added` or `Admission::Duplicate`;
   - the same `Invalid` / `Capacity` / `Internal` error;
   - the same state on neutral returns (an error leaves the replica unchanged).

**Status of other observations:**
- **Anchors and undo/redo/restore are not implemented in the Rust crate.**
  `src/edit.rs` has no anchor or history API. They exist as contracts and
  decisions (`carbon-contract.md`, `undo-semantics.md`, `first-cut-decisions.md`).
- They join this list as observations only when they are implemented and
  contracted. Until then the boundary doesn't claim to preserve them, and items
  1–4 are what they will be built on.

**Authored runs are not storage runs.**
- An *authored run* is one event's insertion: `Fact.insert: Vec<u32>`, whose
  births are `index 0..n` of that event. It is document data, part of
  identity, and grouping-relevant.
- A *storage run* would be a packing choice inside a tree representation: one
  stored entry for several consecutive births. Splitting or coalescing storage
  runs is invisible by definition. It must preserve every individual `BirthId`
  and its later targeting, not only today's text.
- A storage run need not coincide with an authored run. It may be split by later
  edits, and whether it may span authored runs is a representation choice.

## 2. The rule: two layers

**Layer S (semantic, must stay stable).** Theorems that state what the document
*means* or what callers *observe*:
- convergence;
- placement and FugueMax ordering;
- visibility and deletion;
- public transition results;
- undo/redo/restore effects and anchors, once implemented (§1: not in the Rust
  crate today).

These must be stated only over:
- facts and identities: `Fact`, `EventId`, `BirthId`;
- the public observations `Replica::whole()` (whole sequence of births) and
  `Replica::observe()` (visible births with scalars);
- public return values (the §1 list);
- an independent mathematical sequence semantics: the per-character FugueMax
  account in [fugue-ordering.md](fugue-ordering.md), which "keep[s] every birth
  as a tree node" as a *mathematical* tree.

They must not mention the Rust representation: `Native.t_Tree`, `Native.t_Node`,
their fields, `Tree.add`, or the rebuild algorithm (`interpret`,
`interpret_scheduled`, `interpret_event`, `replay_*`).

**Layer R (implementation refinement, expected to be redone).** Theorems that
show *this* implementation computes Layer S's meaning:
- the scheduler;
- event-work replay;
- author reconstruction;
- node installation;
- the refinement from the Rust tree to the mathematical tree.

They may mention the representation freely. When the representation changes,
Layer R is re-proved for the new one, and Layer S theorems carry over unchanged,
provided their premises and observations are preserved.

This is the boundary the continuation plan already asks for. Continuation §3's
deliverable is
"an explicit abstraction from native facts/tree to the chosen edit-only sequence
semantics, independent of the Rust replay algorithm". Continuation §5 says an
incremental
representation is evaluated "against that boundary". This draft adds runs as a
second representation under the same rule, and makes the layer assignment
explicit so that new M1 theorems can be checked against it.

**Distinction from today's per-character tree.** The *mathematical* per-birth
tree is Layer S. The Rust `Node` / `Tree` struct is Layer R. A storage-run tree
changes only the latter. Fact identities are already per character
(`BirthId { event, index }`), and facts carry *authored* runs
(`Fact.insert: Vec<u32>`). Storage runs are a different thing (§1), so neither
identities nor the update shape change.

## 3. Inventory: where the current proofs sit

Grep of `proofs/*.lt` on `main` for tree-representation names (`t_Tree`,
`t_Node`, `impl_Tree__*`, node fields, `interpret*`, `replay_*`):

| module | references | layer | note |
|---|---|---|---|
| EditReplay | 47 | R | `node_prefix` replays nodes through the actual `Native.impl_Tree__add`; its own comment says "it does not independently refine add". So #87's ordered author replay is not yet the independent meaning. |
| EditSchedule | 42 | R | causal schedule and `event_work_prefix` describe the rebuild-per-event algorithm (`choose_ready`, `interpret_event` outputs) |
| EditAccepted | 8 | R | `tree_installation_*` only say `with_tree` stores the given value; they hold for any `Tree` type. But the publication law (around line 1059) states the published tree **equals** `Native.interpret(facts)`, the rebuild. An incremental tree would satisfy only observation-equality with `interpret`, so this law is one to restate. |
| EditCommit | 2 | R, opaque | `tree_publication_*` say `with_tree` keeps private state; opaque in the tree value |
| EditBasis | 1 | R | fact-selection stage of the current interpreter |
| the other 11 modules | 0 | — | no tree-representation reference |

Observations:
- **No Layer S theorem about document meaning exists yet.** No proof mentions
  `whole()` or `observe()`. Convergence, placement and visible-sequence
  correctness are all still open (#42 and continuation §3).
- So today **nothing semantic depends on the representation**, simply because
  the semantic theorems don't exist yet. The risk ren describes is about the next
  slices. If continuation §3's abstraction were stated over `Native.t_Tree` or node structure,
  rather than over `whole()`/`observe()` and the mathematical tree, every
  semantic theorem would have to be redone for runs or the incremental tree.
- The Layer R modules (EditReplay, EditSchedule's event-work, EditBasis) are
  legitimately algorithm-specific. They are what a new representation re-proves.
  Their cost of change should be counted against the representation change, and
  it does not spread to Layer S.

## 4. What each future representation must discharge

For a new representation `T'` (a storage-run tree, an incremental tree, or both),
the semantic theorems transfer through a sufficient refinement boundary:

> For every history the public API admits, `T'` agrees with the mathematical
> per-birth tree on every §1 item: identities and content, `whole()`,
> `observe()`, author-basis placements, and every public outcome, on success,
> `Duplicate`, empty and error paths.

Given that, Layer S theorems carry over without being re-proved. **That is not
the whole cost of a new backend.** It still owes:
- its own representation invariants, established and preserved;
- progress and capacity arguments for its own structures (the fit predicate of
  continuation §4 covers today's intermediate structures, not a new backend's);
- cache validity, for an incremental tree;
- all-return refinement, not only success.

**Storage runs, specifically:**
- **Splitting:** an insertion into the middle of a stored run, or a deletion of
  part of one, splits it (and so would a later partial restore, once restore
  exists). Splitting never changes any §1 item. Every `BirthId` stays
  individually addressable, and stays targetable by later deletions and gaps.
- **Origins:** within a run, each character's left origin is its predecessor in
  the run. A run representation may store this implicitly, but the refinement
  must reproduce the per-character origins FugueMax uses (`left_origin`,
  `right_origin`, `parent`, `side`). In particular, sibling tie-breaks use
  `birth_lt` on individual births.
- **Coalescing** adjacent stored runs is optional, and is equally invisible to
  every §1 item.

**Incremental tree, specifically:** §5's obligations: causal locality, cache
validity from construction, preservation and all-return refinement. A
reachable-state theorem is a changed domain, not a silent replacement of the
current theorem over arbitrary states.

**Both together:** one refinement from the combined representation to the
mathematical tree, rather than two stacked refinements. Whether one or two steps
is cheaper is an open choice (§6).

## 5. Checking the rule as slices land

Proposed as review criteria, not as new machinery:
- **New theorem statements:** a review checks which layer each new statement
  belongs to. A Layer S statement that mentions a Layer R name is a finding.
- **The §3 abstraction:** its statement names `whole()`/`observe()` (or an
  equivalent observation function) and the mathematical tree. `Native.t_Tree`
  appears only inside its refinement proof.
- **Controls** for Layer S theorems should include at least one
  representation-preserving perturbation of the implementation that is
  observation-neutral and must not break the theorem. For example, a reordering
  of the `nodes` vector that keeps traversal unchanged. That shows the theorem
  doesn't depend on layout.
- **A syntactic fence** like #90's is possible, refusing Layer R names inside
  Layer S modules. Like #90's fence, it would be a syntax guard only. It cannot
  stop SMT from using facts about the extracted representation, so the real
  evidence is the refinement structure and the perturbation controls.

## 6. Open choices

- **Priority and timing:** whether runs join v0.1 (only if the v0.1 profile's
  limits grow well beyond today's 512-birth cap in `Replica::new`), or follow v0.1
  with the incremental tree.
- **Representation order:** runs first, the incremental tree first, or one
  combined representation with a single refinement.
- **Mathematical tree:** whether Layer S uses the mathematical per-birth tree
  directly, or a simpler sequence semantics with FugueMax proved as a separate
  lemma.
- **Observation surface:** whether `whole()`/`observe()` is the complete
  observation for refinement, or anchors and undo need more observations.
- **Prior art:** run-length tree representations in other sequence CRDTs are
  not reviewed for this draft. They can be added with citations if useful.

## 7. What this draft does not claim

- That any limit increase, storage-run implementation or incremental-tree
  implementation is adopted. None is.
- That the current Layer R proofs are wrong or wasted. They are the current
  implementation's refinement, and the obligation is to re-prove them for a new
  representation.
- That Layer S theorems exist. None about document meaning has been proved yet.
- Any cost estimate for a run or incremental refinement.
- That FugueMax admits a run representation without subtleties; §4's
  obligations are where those would surface.
