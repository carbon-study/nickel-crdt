# workload budgets outside the engine — migration candidate

The engine does not choose how many events, parents, retained births, scalar
values, delete targets, ordering links or value bytes a caller may use. Those
artificial workload ceilings have been removed, including the hidden 512-node
tree check. No larger constant or maximum-sized sentinel replaces them.

Text construction is now `edit::Replica::new(writer)`; register construction
is `register::Replica::new(writer, initial)`. Both retain their Result return
shape. The batch example takes only its producer ID. The shared admission policy
now supplies only duplicate-dependency and producer-predecessor errors, not
capacity error constructors.

## run the actual boundary

```sh
cargo run --locked --example policy-boundary
cargo test --locked --test capacity_boundary
cargo test --locked --test register_checkpoint
```

The external example relays a text insertion and deletion with 513 births/targets,
then authors a register write after synchronizing 65 concurrent heads. It also
relays a 4097-byte value and retains 130 register facts. These are finite test
workloads, not new promised bounds. `tests/support` owns the old workload budgets;
the capacity tests retain the old order-dependent policy witnesses through an
explicit caller guard while the underlying engine admits the complete history. The guard checks all
budgets before semantic admission; it intentionally does not preserve the old
engine error precedence. A missing dependency plus an oversized insertion can
therefore return Budget from the harness while the engine returns Missing.

The batch fixture no longer caps operation count, nonempty name length or value
bytes. Empty batches/names and missing records remain invalid. No collection,
Undo or wire-format semantics are otherwise adopted.

## finite representation and safety remain

Text's existing MAX_COUNTER identity domain is unchanged. Register counters and
logical clocks still reject overflow. Vec-push/add guards remain. Tree traversal
computes two visits per retained node, so it now checks the actual usize
multiplication boundary rather than relying on 512 as an accidental proof.
The obsolete multiplication guard for the removed ordering-link budget is gone.

Removing a policy refusal does not prove allocation success, termination,
fitting admission, independent client refinement or SEC. Rust allocation,
translation/models and external delivery remain explicit boundaries.

## proof and control migration

Constructor/validator arguments and frames naming the deleted Limits field are
ported to the new API. Non-policy state equality, neutrality, returned identities,
counter advancement, exact installation, retained content and semantic predicates
remain. Equal-value neutrality no longer needs a value-byte-bound premise.
The payload-validation equivalence drops the two removed byte-policy conjuncts;
its observation, counted-change, clock and actual selected-basis checks remain.

Derived hax instance names changed when Limits was removed. Bridges explicitly
follow the same Writer/EventId/BirthId equality, Tree default and Replica Clone
instances; this is not a new abstract equality or clone axiom.

The old birth-count-loop mutant cannot exist once that policy computation is
deleted. Its replacement skips scalar validation on nonempty histories, with the
same scalar-validity owner. The admission error-swap control now swaps the two
remaining error constructors. The native premature-write-publication control
uses a writer-conflict failure instead of an artificial capacity failure.
No preparation/type error is counted as semantic rejection.

This remains a migration candidate pending focused controls, source-linked review
and complete exact-head CI. It does not accept the native register checkpoint,
activate a new compiler or close the remaining text-side sequencing audit.

Removing the ordering-link policy also removes the native text test's reachable
post-prepare failure. The replacement test checks successful replacement. There
is currently no retained end-to-end native text witness of failure after prepare;
that transactional case remains covered by the implementation-linked proof
controls, not a claimed native late-failure test. No production fault hook was
added to manufacture one.
