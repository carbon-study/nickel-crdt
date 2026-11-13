# nickel-crdt

An application-independent CRDT library, intended for Carbon and potentially Dark, with proofs tied to its Rust implementation through hax and Latte. Lynn owns and maintains it.

This repository contains an [experimental Rust edit/admit candidate](docs/rust-edit-admit.md), the toolchain scaffold and restricted executable references. Two Rust producers can exchange insert/delete/replace facts using FugueMax ordering. Transactional return paths, same-history two-instance commit coherence, accepted event-ID uniqueness and exact successful fact publication have implementation-linked proofs; general semantic refinement, convergence and ordering proofs remain open. **There is no verified CRDT release or stable public API.**

Artificial workload budgets now live in the caller/test harness, not engine
configuration. The [policy-budget migration](docs/policy-budgets.md) records the
API/proof changes and retained overflow boundaries. This removes one source of
order-dependent refusal; it does not establish admission progress or SEC.

## Keyed-register checkpoint candidate

The [native checkpoint](docs/register-checkpoint.md) adds single-write keyed
write/read/replication through the actual shared graph and publication shell.
Run `cargo run --locked --example register-checkpoint`. The read-selection,
equality, no-edit and publication proofs are bounded components; full register
validity/refinement and convergence remain open. This is not acceptance of the
complete [register-first cut](docs/register-first-cut.md), atomic multi-write
registers or Undo/Redo.

## Shared-layer experiment

The [shared-layer migration](docs/shared-layer-experiment.md) routes the existing
text engine's admission, graph scans, scheduling and publication through generic
native code. The atomic record/field-batch example uses that same layer. Try
`cargo run --locked --example shared-causal`; the main proof gate checks the
transferred text statements and generic foundations. This remains experimental,
with client obligations and the unproved semantic boundaries listed in the scope.

## Next native delivery

The [register-first slice](docs/register-first-cut.md) is the next approved
delivery: keyed write/read/replication with implementation-linked obligations.
It is not implemented yet. Text remains a preserved track, with an explicit
return point after that slice and a goal of sharing the convergence argument
where the actual client laws support it. No strong eventual consistency claim
is delivered by this plan.

## Ordering research candidates

[FugueMax candidate](docs/fugue-ordering.md) is the current stronger-ordering
experiment: separate-event common-gap runs, retained-node hide/reveal fit and
the existing actual Session bridge. It is selected for the experimental Rust edit-only cut, not a release or a machine-verified ordering algorithm.
The earlier [historical-gap ordering construction](docs/ordering-construction.md) supplies
one authored order-only interpretation, directed restoration/concurrent-run
witnesses and its explicit quadratic key-growth limit. It is not adopted
semantics, an integrated undo algorithm or a Rust implementation. The
[reference command](experiments/ordered-gap-reference/README.md) runs separately
from the existing proof/toolchain checks.

[Order/effect bridge](experiments/order-effect-bridge/README.md) renders actual
Python session Undo/Restore transitions through that candidate order, with warm
and cold continuations. This is a finite research integration, not combined
wire admission or a verified engine.

## Undo questionnaire

[40 scenarios, local progress and JSON answer export](https://nickel-undo.shit.yachts/) support the design discussion. The standalone [questionnaire](questionnaire/README.md) has its own locked flake and is not a CRDT implementation or verifier.

## Run the checks

On x86_64 or aarch64 Linux with Nix:

```sh
nix flake check -L
nix build --no-link .#native .#proofs
nix develop
cargo test --workspace --offline --locked
```

The `references` shell runs the executable research gates without realizing
the native/proof toolchain:

```sh
nix develop .#references --command bash experiments/order-effect-bridge/check.sh --fugue
```

It contains locked Node, jq and shell utilities. Python remains owned by the
hybrid reference's nested flake. This changes no gate's semantics, receipts or
proof dependencies; CI must still run the native/proof check separately.

The workspace has the experimental `edit` module and a separate `proof-smoke` crate. Its `flip` function toggles a Boolean in a Rust range loop. The proof check extracts that actual function with the locked hax compiler, connects it to the imported `LoopUtil` interpreter, and proves parity and involution for every representable loop bound. It also changes the Rust loop to leave the Boolean unchanged and requires the unchanged bridge theorem to reject it.

The Boolean fixture is toolchain evidence. The same proof gate also checks the actual edit/admit error/empty return paths, local counter step, same-history author/admit coherence, accepted-ID uniqueness and exact successful fact publication; it does not prove the full edit semantics or convergence. See [proof scope](proofs/README.md) and [provenance](PROVENANCE.md).

## Layout

- `src/`: experimental two-writer Rust edit/admit candidate.
- `tests/`, `examples/`: public-API native cases and external fixture consumer.
- `proof-smoke/`: independent Rust extraction fixture.
- `proofs/`: authored Latte sources and committed F* views.
- `scripts/`: extraction, proof checks and immutable external-model bootstrap.

## API and verification proposal

- [Prospective API and verifier obligations](docs/api-verification.md): operation shapes, preconditions, return/error contracts and the status of each intended theorem.
- [Shared causal-event layer](docs/causal-event-layer.md) (proposal): source-linked inventory, mixed-document atomic commits, payload/client proof boundary and writer-ID sequencing. No implementation or roadmap change is adopted.
- [Register contract](docs/register-contract.md) (#67, proposed): one value per caller key, with Ren's register undo outcomes (q13–q17 and five follow-ups) fixed as rules; executable evidence in [experiments/register-candidates](experiments/register-candidates/README.md).
- [Keyed collection contract](docs/collection-contract.md) (#68, proposed): put/insert, removal that deletes only what it saw, restore, and Ren's collection answers; executable evidence in [experiments/collection-candidates](experiments/collection-candidates/README.md).
- [Local-undo analysis](docs/undo-semantics.md): selection versus effect semantics, literature alternatives, worked continuations and the unresolved sequence algorithm.
- [Consumer motivation and required witnesses](docs/carbon-contract.md): Carbon and potential Dark uses, separate from the library contract.

No sequence/undo verifier obligation is currently discharged. The proved Boolean loop is toolchain evidence only.

## Current reference candidate

[Own-action Undo and explicit Restore](docs/private-session-profile.md): running edit/restore/undo/redo selection over two independent identity-set documents, with private checkpoint continuations. This is a restricted research model, not the Rust core or an adopted complete undo API. The [Restore preview follow-up](docs/restore-preview.md) adds inspect/confirm calls bound to the exact document/private basis.

## Roadmap and next decision

[The implementation roadmap](ROADMAP.md) proposes the first usable native
release, an earlier experimental crate, and Rust/proof/consumer acceptance gates. The first Rust edit/admit cut is now being implemented with its proofs; the
complete experimental milestone is not delivered. The
[four decision scenarios](docs/first-cut-decisions.md) collect the pending
history/effect/identity choices before ordered-reference/API reconciliation;
the roadmap alone adopts no ordering algorithm; the edit-only implementation uses FugueMax.

The [response-led plan](docs/response-plan.md) preserves why Ren's questionnaire
answers displaced the earlier writer-exclusive activity recommendation.
The [consumer contract](docs/carbon-contract.md) retains motivation and witnesses,
not an adopted complete API. Carbon and possible Dark adapters remain separate.

The scaffold does not reopen the parked Dark or Loro projects. Copying their reusable loop reasoning is a scoped extraction.

The [Rust transition/proof cut](docs/rust-transition-cut.md) states the remaining joint proof/consumer exit. See the [candidate contract](docs/rust-edit-admit.md) for the implemented domain and current evidence.
