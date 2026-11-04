# derived event nodes: locality and a cache experiment

**An isolated native experiment and conditional source argument, not a
machine-checked cache law or an enabled library backend.** The ordinary Rust
library and its implementation-linked proofs remain unchanged. The preceding
[fact-storage comparison](edit-storage-comparison.md) identified repeated
`interpret` work, rather than sorting, as the measured latency bottleneck.

## the object being retained

The actual `interpret` in `src/edit.rs` already constructs a temporary
`operations: Vec<(EventId, Vec<Node>)>`. Each entry records the fresh scalar
nodes derived when that event is interpreted in its author's causal basis.
These are the records returned by `Tree::insert`, before integration into the
receiver's result tree. They are not snapshots of a mutable tree node's child
arrays, a current visible set, or an author's whole tree.

The experimental copy retains that per-event vector in each owned Replica.
On its next admission, the existing canonical causal scheduler still runs:
old entries reuse their saved nodes, while a new event reconstructs its author
basis and derives its own nodes. The result tree is still rebuilt by applying
all entries in the same canonical causal order. It therefore does **not**
require an unproved change of integration order or an incremental tree index.
Every new trial also clones the cache; no global cache is shared by instances.

Deletion-only events have an empty node entry. Their facts still participate
in the causal-basis visibility calculation for later insertions, and `observe`
still computes visibility from all accepted facts. Caching insertion metadata
does not cache or freeze document visibility. Undo/Restore remains outside this
edit-only experiment.

## conditional source argument

The proposed locality claim is: for a fixed event and the exact facts in its
transitive causal past, its freshly derived node vector is unchanged by facts
outside that past. This includes concurrent facts and later descendants.
It is stronger than agreement of rendered text.

Required premises, **not yet established together by the native proofs**:

1. Facts have unique IDs and a closed acyclic dependency graph. Existing fact
   bodies are immutable; the same accepted ID cannot acquire different content.
2. `canonical` returns precisely those facts in strict `event_lt` order, and
   the actual `past` loop computes their exact transitive causal closure.
3. We reason about ordinary successful executions within the selected scalar,
   node and arithmetic bounds. A future resource policy must not be silently
   substituted into this claim.

Here is the source-level argument to machine-check:

- **Causal scheduling projects.** `interpret` repeatedly chooses the first
  not-yet-done ready fact in canonical ID order. Let S be a causally closed
  subset. Steps outside S cannot change readiness of any member of S: every
  dependency of a member is already in S. Whenever a member of S is chosen,
  it is the least-ID ready member of S. Deleting the outside steps therefore
  leaves exactly the schedule obtained on S alone. This is a restriction of
  the *causal scheduler*, not a claim that ID order itself is causal order.
  For the author reconstruction, take S to be `past(e)`. Transitive readiness
  puts every member of this past in `done` before e is chosen. The actual
  `operations` vector is in done order, and its `selected` filter therefore
  replays exactly this projected schedule when rebuilding e's author tree.
- **The basis is fixed.** Filtering the strictly ID-ordered facts to an exact
  causal closure gives the same ordered fact list in every extension. `visible`
  reads precisely that list, so the author's pre-edit visible-ID vector is
  fixed, including the effects of causal deletion facts.
- **Induct over causal events.** Previously derived entries for that basis
  agree by induction. Their filtered application order agrees by the schedule
  projection above. Thus rebuilding `author` performs identical `Tree::add`
  calls and produces an identical author tree. The event's gap, scalars and IDs
  are fixed. Each scalar call to `Tree::insert`, followed by adding its new ID
  to `seen`, is then identical. So every field of every freshly derived node
  agrees. This argument uses deterministic identical calls; it does not assume
  a general permutation/commutativity law for `Tree::add`.
- **Substitute valid cached entries.** If every existing cache entry equals
  this derivation for its exact accepted fact, replacing reconstruction by that
  entry leaves the canonical result-tree call sequence unchanged. Cache misses
  derive the same new entry. Establishing and preserving this cache invariant
  is a separate implementation obligation, not a consequence of choosing an ID
  as the lookup key.

The current implementation-linked accepted-ID law alone supplies neither exact
canonical content/order nor exact closure nor the cache invariant. This is not
a completed refinement/convergence proof. The argument deliberately exposes
those dependencies instead of treating cached nodes as automatically immutable.

## executable boundary checks

```sh
# Locked default dev shell; normal focused command, no timing runs.
node scripts/check-edit-cache.mjs .cache/edit-cache
# Manual public-call diagnostic; each shape has its own 45-second cap.
node scripts/check-edit-cache.mjs .cache/edit-cache-profile --profiles
```

The script binds the original Rust, itself, manifests, tests and example inputs
by SHA256. It changes only generated crate copies. Unique exact source anchors
extract/reuse the actual interpreter and its actual author-node builder rather
than maintaining a separate handwritten ordering algorithm.

The reference trace records the event, its exact ordered basis facts and its
fresh node vector. Equal event/basis keys must yield equal complete nodes even
when the surrounding full history changes. In the recorded 150-history corpus,
14,942 observations cover 39 distinct event/basis keys; 37 keys see more than
one full history. These are repeated finite observations, not 14,942 independent
histories or a universal quantifier.

The cached correctness copy compares its **entire Tree**, including retained
metadata/child arrays and vector ordering, to actual full replay at every plan
that reaches successful tree construction, before publication. Native public
error/duplicate/empty/commit tests also run. Its complete 150-history /
882-causal-schedule export must equal the traced reference export byte for byte.
The existing independent Python/Node reference separately checks that common
artifact; agreement with the Rust replay path alone is not that independent
semantic check.

Two deliberately wrong copies must fail normally at the intended boundary:

- Let all already-derived receiver operations into the author tree rather than
  only causal-past operations. The locality assertion catches changed origins:
  an observed Bo:1 node's right origin changes from Alice:1/1 to Alice:3/0 under
  changed surrounding history, despite the same event and causal facts.
- Corrupt a reused cached node's scalar. The exact cached/full replay assertion
  catches it. This also demonstrates that cache hits are exercised.

The timing copy differs from the cached correctness copy only by removing the
full-replay comparison. It still runs the public example's independent
sequential-list checks after every completed pair. Timed calls therefore do not
carry the exhaustive replay guard, and their finite checks do not establish the
unproved general cache law.

## observation and adoption gate

The [measurement receipt](measurements/edit-cache.json) retains aggregate public
call observations. These are optimized single-run observations on the shared,
non-isolated x86_64 Intel i9-12900KF host, not maxima, stable speed estimates,
ARM/phone measurements or a whole-memory bound. The earlier reference timings
are not a simultaneous or counterbalanced baseline.
The cache adds retained metadata; the existing `ordering_links` check still
counts the result tree and does not account for that extra cache storage.

| cached timing shape | checked events / retained births | last author / receive | sum of checked public calls | outcome |
|---|---|---|---|---|
| append | 128 / 512 | 24.2 / 24.2 ms | 1.84 s | complete |
| prepend | 128 / 512 | 25.6 / 25.5 ms | 1.90 s | complete |
| frontloaded-delete | 128 / 512 | 25.6 / 26.2 ms | 6.20 s | complete |

Every completed timing run also checks event 129's atomic capacity rejection.
The prior full-replay append/prepend calls were roughly 0.5 seconds at the same
ceiling; its frontloaded-delete run timed out before that ceiling. The cache
experiment supplies concrete evidence that avoiding repeated derivation is
worth the proof work. These observations do not make it a verified backend,
a stable latency budget, or an editor-ready release.

There is an important proof-domain issue before adoption. Current
`EditCommit.same_shared` compares facts/tree/limits without a cache. An arbitrary
poisoned cache can change future behavior despite equality of those fields;
the corruption control exhibits the danger. Adding cache equality or a new
validity premise would change the claim. It must not be smuggled into a recheck
as an unchanged theorem. A representation-refinement account must establish
cache validity from construction, preserve it on all public returns, and lift
the existing observable contracts, with any changed domain/premise explicit.

A proposed new reachable-state theorem would require a semantic `CacheValid`:
exactly one entry per accepted fact, no extras, exact derived node contents,
and the specified canonical causal entry order. Merely matching IDs/counts is
insufficient. Refinement must compare the returned result and projected state
on **all** returns, including rejection, capacity failure, duplicate and empty
calls; it cannot introduce extra errors and prove only successful-tree equality.
Pairing nodes with their fact could rule out orphan/missing entries structurally,
but would still require the semantic-content law. It would also need an explicit
account of the current `facts() -> &[Fact]` view before changing storage layout.

Next machine-checked obligations are the exact canonical-content/closure and
causal-schedule projection needed by the locality argument, node-derivation
locality, cache establishment/preservation, and assembly agreement with the
retained replay path. The experiment does not replace those obligations with
differential tests. It introduces neither version vectors nor a new ordering,
undo, transport, persistence or resource policy. The ordinary replay candidate
and its existing proofs remain the library implementation until that boundary
is closed.

The collected scoped design/argument review of `f7def59` supports the conditional
schedule-projection reasoning and the explicit theorem-domain concern. The
source connection to `past(e)`/done order and the all-return refinement obligation
above make its requested clarifications explicit. That review did not assess
lemma or control strength and does not close the machine-checked adoption gate.
