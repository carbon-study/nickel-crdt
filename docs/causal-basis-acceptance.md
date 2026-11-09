# native causal-basis acceptance

This is the native evidence for [continuation §2](edit-admit-continuation.md#2-prove-the-actual-causal-basis-and-scheduler).
It does not close the universal exact-past, scheduler progress or subset-schedule
projection obligations in [#42](https://github.com/carbon-study/nickel-crdt/issues/42).

Run the actual unit tests:

```sh
cargo test --offline --locked --lib causal_basis_tests
```

They are also discovered by the existing native workspace test gate. To run the
focused positive and four isolated Rust mutation controls, retaining logs:

```sh
node scripts/check-causal-basis-native.mjs /tmp/nickel-causal-basis
```

That control command is a developer check, not a new CI lane. It requires each
mutation to compile and fail at its intended native assertion; a timeout or
compilation failure is not detection. It does not modify the checkout.

## what is checked

- `past` is compared with an independent worklist/set closure on all DAGs with
  0–4 fixed topological labels, every storage permutation and every root subset.
  Event-ID order differs from topological-label order. This is bounded graph
  coverage, not all writer assignments or a proof for arbitrary finite inputs.
- `ready` is compared with direct set inclusion on four IDs.
- Actual public `edit` constructs a six-event replacement/concurrent-insertion
  history. Every legal causal delivery order and each intermediate receiver
  state preserve each event's exact node placement: birth ID, scalar, origins,
  parent and side. Expected placement is replay on an independently selected
  ancestor basis. This tests native reconstruction locality, not an independent
  FugueMax semantics or equality of observed scheduler traces.
- Domain separators retain duplicate roots, directly missing roots, a missing
  transitive reference in a non-closed stored graph, and a closed cycle. In
  particular, `past` does not validate all transitive references on arbitrary
  malformed stored inputs. Closure and acyclicity must remain explicit premises;
  public admission establishes its own invariants separately.

Controls remove closure expansion, skip direct-root validation, ignore a missing
readiness predecessor, and let receiver operations contaminate author replay.
The last must change an origin/parent in the actual public-admission fixture.
An append-only version of that fixture let the control survive; concurrent
insertion at the same leading gap supplies the distinguishing observation.

All tests are `cfg(test)` only. No runtime behavior, public API, theorem or trust
boundary is changed. The source-linked universal laws still need to be proved.
