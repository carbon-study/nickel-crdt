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

Negative variants preserve evidence of two concrete failures:

- selecting only the visible right bound misplaces Y relative to hidden X;
- choosing bounds from the receiver's current set reverses concurrent runs
  according to arrival order.

Finally the append control exposes the candidate's bad key growth: total digit
count is triangular (528 at 32 characters), before counting event bases and
visibility snapshots. No resource-budget or useful-scale claim. Output is
committed as `receipt.json` for inspection; regenerate with the command above.
The written finite-history argument is not a machine proof. This is research,
not adoption of the candidate, a public Rust API or a verified CRDT engine.
