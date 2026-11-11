# shared graph policies

A client constructs the graph callbacks once and passes that value to the shared
scans. Text uses `TEXT_OPS`; the batch example uses `BATCH_OPS`. Changing this
packaging does not change event identity, operation order, admission/error order,
publication, capacity, or any client's interpretation.

`event_layer::GraphOps<F, I, E>` has two groups:

- projections/comparisons: identity, dependencies, identity equality, identity
  order, whole-fact copy, whole-fact equality;
- graph errors: internal, missing dependency.

`EventOps<F, I, E>` adds predecessor/forbidden callbacks and four admission errors:
 event capacity, dependency capacity, duplicate dependency, producer predecessor.
The text client supplies this complete policy. The batch example retains its own
admission rules and supplies the graph group only. Ordinary push/copy helpers and
`event_shell`'s application callbacks remain separate boundaries in this cut.

## construction and proofs

Use the generic `const fn graph_ops` and `event_ops` constructors. The tuple slots
are positional: Rust cannot distinguish equality from ordering by their types.
The constructor contracts in `EventGraph.lt` preserve every slot, including the
error constructors. The concrete text policy is separately equated to its exact
expected construction in `EventGraphText.lt`. Callers compose those contracts
with the constant and constructor bodies withheld at the relevant assertions.

The generic constructor shape also matters to the pinned extraction. A concrete
tuple literal or concrete constructor failed the native cross-module classifier
check with an incomplete-pattern error, despite passing Rust tests. The generic
constructor passes with the original exhaustive match and unmodified extraction.
This is a checked source-shape requirement for this toolchain, not permission to
patch generated F*, increase checking options, or generalize from a toy probe.

Generic scan laws quantify the same arbitrary callbacks through the tuple; their
mathematical predicates remain comparison-relative. Concrete text statements and
predicates retain their domains and meanings. Exact shared-call specialization
statements now name the bundled policy. No arbitrary-client convergence,
register/collection semantics, writer migration or wrapper retirement follows.

## deliberate-bug coverage

`check-edit-proofs.mjs` includes actual Rust construction-site and constructor-body
controls:

- `text-policy-swaps-eq-lt`: swap the text constructor's two comparison arguments;
- `graph-policy-swaps-eq-lt`: swap those slots in the generic constructor;
- `admission-policy-swaps-errors`: exchange two admission-error constructors.

Each must freshly extract and fail ordinarily at its named policy/constructor
law. Existing algorithm and actual-call controls remain, retargeted to the bundled
call shape. Contract-dependency controls additionally remove the required policy
contracts while their implementation bodies remain hidden.

The batch example's construction-site swap is a **native** control in
`check-shared-native.mjs`. Its test calls the actual batch scheduling callback
with a completed event. This detects incorrect equality wiring but is not a
machine-checked batch-client refinement or convergence proof.

From the locked proof environment, run focused checks with:

```sh
node scripts/check-edit-proofs.mjs /tmp/nickel-policy-check gatepreflight
node scripts/check-edit-proofs.mjs /tmp/nickel-policy-check positive-only \
  text-policy-swaps-eq-lt graph-policy-swaps-eq-lt admission-policy-swaps-errors
node scripts/check-shared-native.mjs /tmp/nickel-batch-policy-check
```

The complete mutation/dependency matrix belongs in CI. Source staging and passing
selected controls alone do not establish acceptance of the entire port.
