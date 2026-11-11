# shared causal layer migration experiment

The existing `edit::Replica` now uses the shared layer directly. Its production
call graph goes through `event_layer` for identity lookup, duplicate scans,
causal admission guards, exact-past expansion, whole-event canonicalization and
basis selection. `event_shell` owns planning order, scheduled replay and the
publication decision. The text client supplies projections, identity policy,
text validation and tree interpretation. This replaces the first version of
this branch, which only added a parallel prototype and did not fulfill the
migration request.

`Fact`, `EventId`, `BirthId`, public text calls, error categories and bounded text
profile remain the compatibility surface. Thin native wrappers keep the old
proof-facing names and specialize the generic functions at the actual text
callbacks. They do not contain a second graph algorithm. Some are retained
explicitly as proof bridges even when a generic inner call no longer calls the
wrapper itself. Source mutation controls must target the actual shared body or
executed client callback, not such an unused forwarding wrapper.

## generic core and clients

`event_layer` is generic over the complete event value and identity type. Plain
function parameters project identity/dependencies and supply comparison, ordering,
cloning and error construction; the module does not import the text types or
assume two identity constructors. `event_shell` is generic over candidate state,
event, interpretation state, operation results, context and errors. Its client
callbacks are explicit arguments, including the actual arguments used during
planning and replay.

The public text client retains Alice and Bo and the existing writer-first order.
This migration does not implement the separate peer-representation/recovery
proposal or enlarge the accepted text profile. The generic layer's comparison-
relative statements must not be confused with proving a client's equality,
ordering, allocation or interpretation obligations.

`atomic_map::BatchReplica` exercises the same shared graph/planning/publication
code with arbitrary `u64` peers and ordered record/field batches. Application
format tags and bytes are opaque. Its example policy is last write in canonical
replay order, with source events retained. It does not adopt the proposed full
register/collection/history contracts: there is no remove, Restore, Undo,
retirement, compaction or general unknown-engine-operation protocol.

`shared_text::SharedText` remains a compatibility example, but it is no longer
the only way text reaches the layer: ordinary `edit::Replica::edit/receive`
execute it directly. One fact remains one text operation. Multi-text occurrence
identity is still open.

## proof transfer

The pre-existing text theorem statements retain their original input domains,
premises, refinements and pattern metadata. Their proof bodies now compose the
actual generic operations and exact text-specialization bridges. Shared callee
bodies are withheld where the corresponding old callee bodies were withheld;
contract-removal controls check that the new contracts actually do work.
`LoopEquality` proves the needed pointwise range-fold congruence by induction
from existing checked loop equations, without adding an extensionality axiom.

`EventClassifier`, `EventGraph` and `EventShell` supply generic classifier,
membership, readiness/first-choice and planning/publication laws. The stronger
existing exact-past, rank/progress, causal-trace, basis and labelled tree-replay
claims are rechecked at the text specialization of the actual shared code.
This is not a claim that every existing semantic statement has become a theorem
for every arbitrary client. A new client still owes its validity, comparison,
interpretation, refinement, composition and fitting/progress obligations.
Neither the old nor the new checked components establish general CRDT convergence
or text-tree totality.

The gate records explicit mutation-owner migrations when the owning algorithm
moves to a generic theorem. It retains the original modes and adds concrete
caller/wiring controls; a failure at an arbitrary earlier theorem is not credited.
Fresh extraction has a strict three-module edit inventory (`Edit`, `Event_layer`,
`Event_shell`), separately from the existing smoke module. Changed sources,
views, receipts, affected owners and controls must agree at the accepted head.
The existing pins, models, resource limits and ordinary-rejection classifier are
unchanged.

## transaction and trust boundary

Owned and in-place receive APIs share one publication match. A duplicate or error
does not publish a candidate or replace the original state. In-place receive must
not clone the original and unconditionally assign that clone back: even a pure,
owned Rust `Clone` implementation can change values. A retained regression tests
that case and the actual wrong implementation.

Clients must leave borrowed inputs and published reachable data unchanged;
mutable working data must be detached. `Clone` alone does not guarantee this:
`Rc<Cell<_>>` can share mutable payloads across clones. External callback effects,
panics and allocation/process failure are not rolled back. The pinned hax Clone
model promises value-preserving cloning; fidelity of each concrete Rust client
and of the extraction/models/checker remains an explicit trust boundary, not an
enforced generic Rust purity type.

## run

```
cargo test --locked --workspace
cargo run --locked --example shared-causal
nix build --no-link .#native .#shared-native .#shared-proofs
```

The main proof gate (`.#proofs` and its CI shards) now includes the transferred
text proofs and generic foundations. `.#shared-proofs` additionally preserves the
[first experimental envelope classifier/equality checks](../proofs/causal-envelope-view/README.md);
that focused component is not a substitute for the migration gate. Full matrices
belong in CI; local development uses the affected positive roots and scoped
controls. This experimental branch remains unmerged until its exact-head checks
and scoped reviews close; no revised roadmap or production interface is adopted
by the experiment alone.
