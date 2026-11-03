# ordered-gap reference experiment

Run from the Nickel dev shell (Node 22, locked in the repository flake):

```sh
node experiments/ordered-gap-reference/check.mjs
```

Or `nix develop -c node experiments/ordered-gap-reference/check.mjs` from the
repository root. No service, browser, external package or unpinned tool is used.
The only new local check is this script; do not rebuild unrelated proof caches.

`order.mjs` is an authored pure reference interpretation. Events contain a
fresh writer/counter name, text, the complete insertion-event basis, the supplied
visible occurrence set and a visible gap offset. Reconstruction derives keys
from each event's own basis, never the receiver's current state. It accepts
exact duplicate insertion records and rejects missing/cyclic dependencies,
conflicting names, unknown visible IDs, malformed scalar strings and invalid
intervals. These checks are not a public hostile-input protocol or writer
fencing implementation. The inputs must satisfy the domain in the accompanying
[construction note](../../docs/ordering-construction.md).

The reference's visible set is **an input**, not computed Undo/Restore meaning.
No history selection, deletion event, mask, anchor, replacement transaction,
checkpoint or encoded sync implementation is supplied. Cold checks serialize
these insertion records, not Nickel's private-session save format.

`check.mjs` checks twelve named outputs, both writer orderings and four legal
causal delivery orders in its small concurrent-run fixtures, exact duplicates,
cold reconstruction, and 1,960 insertion/visibility snapshots through three
extension levels. All first-level masks/gaps are explored; later levels keep
the documented deterministic frontier in source. This is not exhaustive over
all histories, and supplying arbitrary visibility sets is not an undo oracle.

Those 1,960 snapshots are single-writer. They now check the stronger whole-order
gap property in `properties.mjs`: each new insertion immediately follows its
visible predecessor, before any known hidden successors. The visible-right-only
variant fails that property on 399 snapshots. The original visible-text-only
assertion did not distinguish it; that earlier coverage gap is preserved here.

`concurrent.mjs` separately enumerates 144 finite histories: two active writers
above an initial writer's ab, each selecting one of three initial gaps and then
append, prepend, hide-own-first-run or see-peer-first-run. All 792 legal causal
schedules check convergence, tree expansion, duplicates and cold reconstruction.
There are 720 whole-order author-gap checks and a per-insertion-event cohesion
check for every history. This small family is not arbitrary concurrency coverage.

Cohesion means one insertion event's text, not a multi-event typing sequence or
Undo item. The retained backwards-typing limitation is a21b and a43b merging
to a2413b. This is not silently accepted as satisfying a broader typing contract.

Negative variants preserve evidence of two concrete failures:

- selecting only the visible right bound misplaces Y relative to hidden X;
- choosing bounds from the receiver's current set reverses concurrent runs
  according to arrival order.

An intentionally interleaved aXPYQb record ordering also fails the unchanged
per-event cohesion assertion for concurrent XY and PQ. That checks the oracle;
it is not an additional allocation algorithm or a general proof.

Finally the append control preserves the baseline's bad expanded-key growth:
total digit count is triangular (528 at 32 characters). `tree.mjs` supplies a
prefix-sharing representation, storing a parent ID and one digit per occurrence.
Its independently traversed tree is checked against the full-key interpretation
on every directed/generated snapshot, every legal delivery schedule and their
duplicate/cold continuations. At 32 appends it stores 32 digits and 32 parent
fields. The expansion function is a test diagnostic, not stored engine state.
This does not make the whole reference linear-memory: author bases and visibility
snapshots still copy history, fields have numeric widths, and traversals are
rebuilt. No resource-budget, efficient-update or useful-scale claim. Output is
committed as `receipt.json` for inspection; regenerate with the command above.
The written finite-history argument is not a machine proof. This is research,
not adoption of the candidate, a public Rust API or a verified CRDT engine.

## stronger FugueMax candidate

Ren has rejected the baseline's multi-event prepend interleaving. It remains
unchanged above; `fugue.mjs` supplies the stronger, unadopted candidate beside it.
Read [the operation, abstraction and hide/reveal premises](../../docs/fugue-ordering.md).
It derives origins in each author's causal insertion basis, using a whole-order
successor including hidden births. It accepts the same trusted research event
shape, not a new public packet format. Parent/side/origin records replace dense
keys; the old tree-to-key abstraction and digit bounds do not apply to it.

Run only its focused check:

```sh
node experiments/ordered-gap-reference/fugue-check.mjs
```

The committed `fugue-receipt.json` records 96 common-gap run histories, 6,400
causal schedules and 672 author-gap checks. All runs use separate events; both
append/prepend directions, two/three writers and exchanged IDs are included.
The hidden-middle profile retains the hidden births in the tree. Same-history
exact duplicate/cold input checks preserve all exposed metadata. Directed
controls distinguish visible-right authoring, plain sibling ordering (paper
Figure 7), and receiver-basis authoring. Invalid gaps, dependencies, scalar
strings, visible sets and conflicting retries reject. These are not hostile
input validation or exhaustive non-interleaving proofs. A later explicit edit
inside a run is allowed and checked.

The real Python Session bridge can also use this candidate, without a new Undo
model: `bash experiments/order-effect-bridge/check.sh --fugue`.

### comparator oracle and hidden-inside-run recheck

The original common-gap family does **not** distinguish plain/reversed Max
comparators once directed strings are removed. The repair adds two independent
checks to `fugue-check.mjs` and its receipt:

- `fugue-max-oracle.mjs`: enumerate total orders and all causally closed states
  in 194 small histories; require the finite author-sequence constraints and
  Definition 4 order conditions to select exactly one order, then compare all
  3,032 causal schedules. No physical tree traversal defines that expected order.
- `fugue-hidden-runs.mjs`: eight empirical supplied-visibility histories and
  92 schedules, with hidden nodes interrupting whole-order runs. The resulting
  visible contiguity is not a consequence of the insertion-only argument.

Run the generated oracle alone, or its seven actual source-mutation controls:

```sh
node experiments/ordered-gap-reference/fugue-max-oracle.mjs
node experiments/ordered-gap-reference/fugue-oracle-controls.mjs
```

`fugue-oracle-controls.json` records rejection at the intended assertions. The
controls run the standalone oracle in temporary copies; no directed witness or
common-gap run check is imported. Timeouts and spawn failures are not accepted
as successful controls. See [the detailed scope](../../docs/fugue-ordering.md).
