# Representation boundary: runs and the incremental tree (draft proposal)

Status: **draft, docs only.** Lynn owns Nickel and reviews this; Ren decides
scope and priority. Repository facts were checked on `main` at `30a8435`.

Ren's requirement: *the proofs must not depend on things we plan to change.*
Two representation changes are planned:

- **storage runs (packing):** store several consecutive births as one stored
  entry instead of one node per character;
- **the incremental tree:** maintain the tree across admissions instead of
  rebuilding it from all facts. The continuation plan's §5
  ([edit-admit-continuation.md](edit-admit-continuation.md)) places this after
  the semantic and progress boundary.

**Both stay post-v0.1, with no change to v0.1's limits.** The urgent work is the
proof boundary: v0.1's semantic statements must not depend on either layout.
This draft proposes the boundary, maps the current proofs onto it, and lists
what a future backend owes. It adopts no representation and requests no
implementation.

## 1. The abstract state and its transitions

Matching outputs such as `whole()` and `observe()` at one point is not enough.
`whole()` returns retained IDs only, and `observe()` returns scalars only for
visible births. Hidden content and placement information would be unconstrained,
and those decide what later reveals, insertions and authoring produce. So the
boundary is a relation on complete states, preserved by every transition.

**Abstract state `A`** (what any backend must be able to reproduce):
- **births:** every `BirthId { event, index }` with its scalar, **including
  hidden births**, and its visibility. No identity is merged, renumbered or
  dropped by storage.
- **retained and visible order:** the whole order over all births, and the
  visible subsequence.
- **placement structure:** whatever the mathematical FugueMax account in
  [fugue-ordering.md](fugue-ordering.md) needs to place future insertions and
  resolve future targets. That is the per-birth parent, side and origins, and
  the author-basis placement of each event (#86/#87).
- **public facts and producer surface:** the retained facts (`Replica::facts()`),
  the writer, `next_counter()` and limits.

**Relation and obligations.** For a backend `B`, a relation `≈` between `B`'s
states and `A` must satisfy:
1. **construction:** `Replica::new(writer, limits)` yields a state related to the
   initial abstract state (the same success/error result);
2. **transitions:** for related states and the same inputs, each public
   transition (`edit`, `receive`) gives the same return and related successor
   states. That covers `Local::Empty` / `Local::Authored(fact)` with an equal
   fact, `Admission::Added` / `Duplicate`, and the same `Invalid` / `Capacity` /
   `Internal` error;
3. **neutral paths:** on every specified neutral return (errors, `Empty`,
   `Duplicate` where it is neutral), the returned state is related to the
   *unchanged* abstract state;
4. **observations:** `facts()`, `next_counter()`, `whole()` and `observe()` are
   functions of `A`, so related states give equal observations.

By induction from 1–3, the relation holds after **any sequence of successive
calls**, not only at one corresponding point. Every later call, including the
reveals, insertions and authoring that hidden content affects, starts from
related states.

These obligations do **not** discharge, and a backend separately owes:
- its own representation invariants, established and preserved;
- fit, prefix and intermediate-capacity conditions, and progress, for its own
  structures (continuation §4's fit predicate covers today's structures, not a
  new backend's);
- cache validity, for an incremental tree (continuation §5);
- the all-return coverage above, not only success.

**Not yet part of `A`:** anchors and undo/redo/restore. They exist as contracts
and decisions (`carbon-contract.md`, `undo-semantics.md`,
`first-cut-decisions.md`), but the Rust crate has no anchor or history API. They
join `A` when they are implemented and contracted. The births, order and
placement structure above are what they will be built on.

## 2. The rule: two layers

**Layer S (semantic, stable).** Statements about meaning and the public
contract: convergence, placement and FugueMax ordering, visibility and deletion,
public transition results, and later undo and anchors. These are **stated** over
`A`, its transitions, facts, identities and public returns. Their statements do
not mention the Rust representation: `Native.t_Tree`, `Native.t_Node` and their
fields, `Tree.add`, `interpret*`, `replay_*`.

**Layer R (backend-local).** Everything about a particular implementation:
- the scheduler and event-work replay;
- author reconstruction and node installation;
- the current exact publication law;
- **the bridge itself**: the relation `≈` and its preservation (§1).

The bridge's statement necessarily mentions both the concrete and the abstract
state, and that is fine: it belongs to Layer R. Mentioning a concrete type
doesn't make semantic proofs depend on it. The checked interface does the
separating: Layer S theorems are proved over `A`, and a backend's bridge
instantiates them.

This is the boundary the continuation plan already asks for. Continuation §3's
deliverable is "an explicit abstraction from native facts/tree to the chosen
edit-only sequence semantics, independent of the Rust replay algorithm", and
continuation §5 evaluates an incremental representation "against that boundary".
This draft adds storage runs under the same rule and makes the layer assignment
explicit.

## 3. Inventory: where the current proofs sit

Grep of `proofs/*.lt` on `main` for tree-representation names (`t_Tree`,
`t_Node`, `impl_Tree__*`, node fields, `interpret*`, `replay_*`):

| module | references | layer | note |
|---|---|---|---|
| EditReplay | 47 | R | `node_prefix` replays nodes through the actual `Native.impl_Tree__add` ("it does not independently refine add"). #87's ordered author replay is an ingredient for the bridge, not yet the independent meaning. |
| EditSchedule | 42 | R | causal schedule and `event_work_prefix` describe the rebuild-per-event algorithm |
| EditAccepted | 8 | R | `tree_installation_*` only say `with_tree` stores the value. `plan_publishes_interpretation` states the published tree **equals** `Native.interpret(facts)`. This stays as the current backend's exact law, and is not weakened; a new backend proves its own bridge alongside. |
| EditCommit | 2 | R | `tree_publication_*`: `with_tree` keeps private state |
| EditBasis | 1 | R | the current interpreter's fact-selection stage |
| the other 11 modules | 0 | — | no tree-representation reference |

Observations:
- **No Layer S theorem about document meaning exists yet**, and no bridge to an
  independent `A` exists. No proof mentions `whole()` or `observe()`.
  Convergence, placement and visible-sequence correctness are open (#42,
  continuation §3).
- So today nothing semantic depends on the representation, because those
  theorems don't exist yet. The risk is in how continuation §3 gets stated. If
  its semantic statements were over `Native.t_Tree` instead of `A`, they would
  have to be redone for each backend.
- The current Layer R proofs stay valid for the current backend and are
  ingredients for its bridge. A new backend re-proves its own Layer R.

## 4. Storage runs: what packing must preserve

- **Packing is not authored grouping.** An authored run is one event's insertion
  (`Fact.insert: Vec<u32>`, births `index 0..n`). It is document data and may
  matter for grouping and non-interleaving. A storage run is a physical packing
  of consecutive births. It may split an authored run, and whether it may span
  several is a representation choice. No grouping or UX meaning may be inferred
  from physical adjacency.
- **Split and coalesce are neutral.** Splitting or coalescing storage changes no
  component of `A`. Each birth keeps its content, origins, visibility and future
  targetability. The *edit* that prompts a split (an insertion inside a stored
  run, a deletion of part of one) is an ordinary transition and may change `A`.
  The split itself must not.
- **Splitting on deletion (or on a future Restore) is one possible technique**,
  as opposed to keeping per-birth visibility inside a packed entry. Neither is
  adopted. The obligation is only the §1 relation.
- **Per-birth placement:** each birth's actual origins (left and right), parent
  and side are preserved exactly as FugueMax computed them. Within one authored
  insertion a birth's left origin is usually its predecessor in that run, but
  that describes an authored scalar chain, not storage packing. A packed entry
  may hold births from several events, so physical adjacency must never
  determine an origin. The sibling tie-breaks (`birth_lt` on individual births)
  are preserved the same way.

**Incremental tree:** continuation §5's obligations: causal locality, cache
validity from construction, preservation and all-return refinement. A
reachable-state theorem is a changed domain, not a silent replacement of the
current theorem over arbitrary states.

## 5. Checking the rule as slices land

Review criteria, not new machinery:
- **New theorem statements:** classify each as S or R. A Layer S statement that
  mentions a Layer R name is a finding. A bridge statement mentioning both is
  expected.
- **The continuation §3 abstraction** should be stated as the §1 relation over
  `A`, covering construction, both transitions and neutral paths. Matching
  observations of the final state is not enough.
- **Layout perturbations,** for example reordering the `nodes` vector without
  changing traversal, are useful **regression tests**. They do not prove that
  no implicit layout fact was used. Independence comes from Layer S theorems
  proved over `A` and an instantiated bridge.
- **A syntactic fence** refusing Layer R names inside Layer S statements would
  be a syntax guard only (as in #90). It cannot stop SMT from using facts about
  the extracted representation.

## 6. Open choices

- **Order of post-v0.1 work:** packing first, incrementality first, or one
  combined backend with a single bridge.
- **The form of `A`:** the mathematical per-birth FugueMax tree directly, or a
  simpler sequence state with the FugueMax placement facts proved as a separate
  layer.
- **Extending `A`** when anchors and history are implemented.
- **Prior art:** packed-run sequence CRDT representations are not reviewed for
  this draft.

## 7. What this draft does not claim

- That any limit increase, packing implementation or incremental-tree
  implementation is adopted. None is.
- That Layer S theorems or a bridge exist. Neither does yet.
- That the current exact theorems should be weakened. They remain the current
  backend's laws.
- That FugueMax admits packing without subtleties; the §1 relation is where they
  would surface.
- Any cost estimate.
