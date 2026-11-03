# stronger ordering candidate: FugueMax

**Research candidate, not adopted ordering or a Rust engine.** Ren rejected
`a2413b` as the merge of independently authored `a21b` and `a43b`: the two
multi-event runs should stay contiguous, in either order. The earlier
[dense-key construction](ordering-construction.md) fails that witness and remains
unchanged as comparison evidence.

This candidate is an authored interpretation of Weidner and Kleppmann,
[*The Art of the Fugue*, arXiv v3](https://arxiv.org/abs/2305.00583v3),
Algorithm 1 and §5.3. It is not a copy or certification of an upstream engine.
The full paper, including appendix proofs, was read before making this fit claim.

## the operation and its retained information

Keep every birth as a tree node, including currently hidden births. To insert
one scalar at a visible gap in the author's known insertion history:

1. Choose `L`, the visible predecessor, or the root at the beginning.
2. Choose `R`, the immediate successor of `L` in the whole tree traversal,
   including hidden nodes, or the end sentinel.
3. If `L` has no right children, insert a right child of `L`. Otherwise insert
   a left child of `R`.
4. Retain the parent, side and origins. Traverse left subtrees, the node, then
   right subtrees. The root has no displayed value.

Left siblings are ordered by increasing occurrence ID. Right siblings are
ordered by **decreasing whole-order position of their right origins**, with
increasing occurrence ID breaking ties. End is after every node. This last
comparison is FugueMax's change to plain Fugue, whose siblings use ID order.
The paper's ordering stability result justifies comparing already-known right
origins; testing a comparator does not re-prove that result for our source.

For a multi-scalar insertion event, perform these scalar insertions successively
in the author tree, with the previous new scalar visible. This supplies a causal
scalar chain inside the atomic event. IDs are the existing numeric
`writer:counter/scalar-index` tuples, compared numerically. No string ordering
or payload-based identity is used.

The implementation accepts the existing `author()` records: full insertion-event
basis, visible birth set, visible gap and scalar text. It reconstructs each
author basis separately, derives scalar operations there, then integrates those
operations into the receiver tree. It never picks origins from the receiver's
concurrent display. This is the same **author-basis discipline**, not the same
allocation representation, as the old candidate.

The returned order records expose ID, scalar, event, parent, side, left origin
and right origin. Child arrays are not returned. The abstraction to displayed
text is whole-tree traversal filtered by a separately supplied visible-ID set.
Tree rebuilding, full causal bases, recursive traversal and JavaScript safe
integers are experimental bounds/choices, not a release resource profile.

## what it fixes, and what it does not promise

Both plain Fugue and FugueMax yield `a2143b` for the rejected prepend witness;
exchanging writer IDs can yield `a4321b`. Max is worth considering for the
stronger property, not because plain Fugue fails this specific example. Figure 7
of the paper distinguishes the variants: the reference gets `AXYBC` with Max
and `AYXBC` with plain Fugue for the chosen IDs.

Algorithm 1 already chooses the whole-order successor, so hiding `a` in `ab`,
typing `X` at the start, then revealing `a` gives **Xab**. No changed cursor API
or remembered historical side is needed for this particular witness. It does
not decide general anchors, range membership or replacement UX.

The paper's maximal non-interleaving is Definition 4, with the exceptions of
Lemma 5, proved for FugueMax in Theorem 9. It is not an unconditional promise
about everything an editor groups as one run. For example, a later writer may
explicitly insert inside a previous run. Figure 6 exhibits a conflict between
unconditional forward/backward adjacency and stable earlier order. These
qualifications do not excuse the old two-run `a2413b` failure.

## retained-node hide/reveal: conditional transfer argument

The paper's list model has permanent deletion, not Nickel's Undo/Restore.
Here is our proposed bridge, **not a machine-checked or peer-reviewed result**.

Take a finite causally closed insertion history with unique occurrence IDs.
Suppose visibility never removes a node or changes its order metadata, and each
insertion derives its origins in its fixed author basis using the rule above.
Construct a deletion-free execution with the same insertion knowledge and IDs:
for each scalar insertion, insert immediately after `L` in the whole visible
list of the corresponding deletion-free author replica. Its successor is `R`,
so the parent/side choice, origins and sibling comparisons are the same. Induct
on causal insertion events and on scalar indices inside each event. The
insertion trees therefore coincide at corresponding causally closed bases.

This supplies a route to applying the paper's **whole-order insertion** laws
to trees authored under changing visibility. Revealing nodes filters the same
retained order rather than moving them. Filtering cannot separate two nodes
that are already adjacent in the whole order when both are visible.

The conclusion is deliberately origin-relative: it does not say a UI's arbitrary
multi-event group is contiguous, or that partial visibility of a group restores
it as one block. Nor does it prove Nickel effect semantics, authority checks,
preview binding, admission, causal delivery, reclamation, anchors or undo UX.
Removing order metadata, re-deciding origins at receivers, or changing the gap
rule would invalidate these premises. A source-linked Rust refinement proof
would still be required even if this argument and candidate were adopted.

## checked boundaries

The [ordering experiment](../experiments/ordered-gap-reference/README.md)
contains `fugue.mjs` beside the unchanged dense-key/tree baseline. Its focused
check covers the prepend witness, Xab, Figure 7, exact scalars, deliberate
interior insertion, duplicates/cold input, and a finite common-gap run family:

- 96 histories of two or three independent writers;
- append/prepend combinations, exchanged writer IDs and four gap/visibility
  profiles (three ordinary gaps and a hidden middle);
- separate-event runs of length three for two writers or two for three writers;
- 6,400 causal event-delivery schedules and 672 author whole-gap checks.

Each run is required to be contiguous and retain its own order. The family
excludes seeing a peer's run while continuing, arbitrary edits at different
gaps, arbitrary visibility changes during the run and general history grouping.
These finite checks do not establish Definition 4 for all histories.
They also do not distinguish the Max comparator from plain/reversed variants;
the separate oracle below addresses that specific review finding.

The [actual Session bridge](../experiments/order-effect-bridge/README.md) also
runs this interpreter without changing the Python effect transitions. Its eight
histories/46 views check unchanged expected text, identity/payload linkage,
effect filtering, cold continuation and 52 causal insertion deliveries.
Friday/Monday remains an experimental expected output, not a policy inferred
from Ren's single-character answer. The new order is not integrated into the
combined-admission or inbox interpreter, whose old key-digit limits would need
a new representation-specific contract. No byte decoder or hostile wire input
is handled here. All CRDT verification obligations remain unfulfilled.

### independent finite Max oracle

`fugue-max-oracle.mjs` enumerates candidate total orders, without constructing
a Fugue tree or using its sibling comparator to choose an expected order. The
generated histories have two or three concurrent root insertions and two
independent singleton insertions, each knowing all but one root. Every possible
known-root omission and gap is chosen for each insertion, with exchanged
insertion IDs. Origins come directly from those independently specified author
sequences. All generated histories are deletion-free.

For each history, it considers every total order and every causally closed
subset. A surviving order must preserve each author insertion sequence and
satisfy Definition 4's forward adjacency, backward adjacency with the explicit
Lemma 5 exception, and equal-origin ID ordering in every subset. Descendance
is computed in the **left-origin tree**, not the candidate's physical tree.
Start/end are sentinels, not additional list elements for adjacency clauses.
This is a finite strong-list/projection check and the three order constraints,
not a general mechanization of the paper.

There are 194 histories, 20,208 candidate total orders, 2,464 causally closed
subsets counted across histories, and 3,032 causal delivery schedules. Exactly
one total order survives per history; the implementation must match it on
every schedule. Plain Fugue disagrees on four histories. Removing the forward, backward
or tie clause makes the specification underdetermine an order and fails the
uniqueness check. Reversing right-origin rank, reversing right ID ties, replacing
Max with plain, or reversing left ID ties fails the generated oracle alone.
No directed strings or the common-gap run family participate in those controls.

### hidden nodes inside a run: empirical evidence only

`fugue-hidden-runs.mjs` supplies eight additional visibility histories. A
helper inserts h between a and Alice's first 1; Alice hides h, then prepends 2
while knowing h. Carol independently prepends 3 then 4, optionally inserting
and hiding k between them. Both hidden-node options and exchanged writer IDs
are checked, across 92 causal schedules and cold reconstruction. Six histories
have a hidden interruption in the whole order. An example is retained order
**a2h14k3b**, visible **a2143b**; exchanging the run writers gives
**a4k32h1b**, visible **a4321b**.

The deletion-free simulation places 2 before h, not immediately before 1.
Consequently that simulation does **not** make the visible 21 sequence a
backward-origin run, and the paper's corresponding run guarantee is not
transferred to it. These tests are expressly empirical, with supplied visibility
rather than real effect transitions, and supply no general visible-run theorem.
