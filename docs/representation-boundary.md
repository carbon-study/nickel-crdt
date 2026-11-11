# Representation boundary: runs and the incremental tree (draft proposal)

Status: **draft, docs only.** Lynn owns Nickel and reviews this; Ren decides
scope and priority. Repository facts were checked on `main` at `30a8435`.

Ren's requirement: *the proofs must not depend on things we plan to change.*
Two representation changes are planned or proposed:

- **runs:** store consecutive characters of one insertion as a single tree
  entry, instead of one node per character (proposed; not yet on the roadmap);
- **the incremental tree:** maintain the tree across admissions instead of
  rebuilding it from all facts. The continuation plan's §5 places this after the
  semantic and progress boundary
  ([edit-admit-continuation.md](edit-admit-continuation.md)), as a post-v0.1
  item.

This draft proposes a two-layer rule, inventories which current proofs sit in
which layer, and states the obligation each future representation would
discharge. It adopts no representation and starts no implementation.

## 1. The rule: two layers

**Layer S (semantic, must stay stable).** Theorems that state what the document
*means* or what callers *observe*:
- convergence;
- placement and FugueMax ordering;
- visibility and deletion;
- undo, redo and restore effects;
- anchors;
- public transition results.

These must be stated only over:
- facts and identities: `Fact`, `EventId`, `BirthId`;
- the public observations `Replica::whole()` (whole sequence of births) and
  `Replica::observe()` (visible births with scalars);
- public return values;
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

This is the boundary the continuation plan already asks for. §3's deliverable is
"an explicit abstraction from native facts/tree to the chosen edit-only sequence
semantics, independent of the Rust replay algorithm". §5 says an incremental
representation is evaluated "against that boundary". This draft adds runs as a
second representation under the same rule, and makes the layer assignment
explicit so that new M1 theorems can be checked against it.

**Distinction from today's per-character tree.** The *mathematical* per-birth
tree is Layer S. The Rust `Node` / `Tree` struct is Layer R. A run tree changes
only the latter. Fact identities are already per character (`BirthId { event,
index }`), and facts already carry runs (`Fact.insert: Vec<u32>`), so neither
identities nor the update shape change.

## 2. Inventory: where the current proofs sit

Grep of `proofs/*.lt` on `main` for tree-representation names (`t_Tree`,
`t_Node`, `impl_Tree__*`, node fields, `interpret*`, `replay_*`):

| module | references | layer | note |
|---|---|---|---|
| EditReplay | 47 | R | `node_prefix` replays nodes through `Native.impl_Tree__add`; its own comment says "it does not independently refine add" |
| EditSchedule | 42 | R | causal schedule and `event_work_prefix` describe the rebuild-per-event algorithm (`choose_ready`, `interpret_event` outputs) |
| EditAccepted | 8 | R | `tree_installation_*` only say `with_tree` stores the given value; they hold for any `Tree` type. But the publication law (around line 1059) states the published tree **equals** `Native.interpret(facts)`, the rebuild. An incremental tree would satisfy only observation-equality with `interpret`, so this law is one to restate. |
| EditCommit | 2 | R, opaque | `tree_publication_*` say `with_tree` keeps private state; opaque in the tree value |
| EditBasis | 1 | R | fact-selection stage of the current interpreter |
| the other 11 modules | 0 | — | no tree-representation reference |

Observations:
- **No Layer S theorem about document meaning exists yet.** No proof mentions
  `whole()` or `observe()`. Convergence, placement and visible-sequence
  correctness are all still open (#42 and §3).
- So today **nothing semantic depends on the representation**, simply because
  the semantic theorems don't exist yet. The risk ren describes is about the next
  slices. If §3's abstraction were stated over `Native.t_Tree` or node structure,
  rather than over `whole()`/`observe()` and the mathematical tree, every
  semantic theorem would have to be redone for runs or the incremental tree.
- The Layer R modules (EditReplay, EditSchedule's event-work, EditBasis) are
  legitimately algorithm-specific. They are what a new representation re-proves.
  Their cost of change should be counted against the representation change, and
  it does not spread to Layer S.

## 3. What each future representation must discharge

For a new representation `T'` (a run tree, an incremental tree, or both), Layer R
is replaced by one refinement obligation:

> For every history the public API admits, the observations of `T'` equal those
> of the mathematical per-birth tree. That covers `whole()`, `observe()` and every
> public return value, on success, `Duplicate`, empty and error paths.

Layer S theorems then hold for `T'` unchanged.

**Runs, specifically:**
- **Splitting:** an insertion into the middle of a run, and a deletion or
  restore of part of one, split it. The obligation includes that splitting never
  changes `whole()`/`observe()`, and that every `BirthId` stays addressable after
  any split.
- **Origins:** within a run, each character's left origin is its predecessor in
  the run. A run representation may store this implicitly, but the refinement
  must reproduce the per-character origins FugueMax uses (`left_origin`,
  `right_origin`, `parent`, `side`). In particular, sibling tie-breaks use
  `birth_lt` on individual births.
- **Merging** of adjacent runs is optional, and is equally observation-neutral.

**Incremental tree, specifically:** §5's obligations: causal locality, cache
validity from construction, preservation and all-return refinement. A
reachable-state theorem is a changed domain, not a silent replacement of the
current theorem over arbitrary states.

**Both together:** one refinement from the combined representation to the
mathematical tree, rather than two stacked refinements. Whether one or two steps
is cheaper is an open choice (§5 of this draft).

## 4. Checking the rule as slices land

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

## 5. Open choices

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

## 6. What this draft does not claim

- That the current Layer R proofs are wrong or wasted. They are the current
  implementation's refinement, and the obligation is to re-prove them for a new
  representation.
- That Layer S theorems exist. None about document meaning has been proved yet.
- Any cost estimate for a run or incremental refinement.
- That FugueMax admits a run representation without subtleties; §3's
  obligations are where those would surface.
