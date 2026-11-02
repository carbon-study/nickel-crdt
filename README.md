# nickel-crdt

An application-independent sequence CRDT library, intended for Carbon and potentially Dark, with proofs tied to its Rust implementation through hax and Latte. Lynn owns and maintains it.

This repository currently contains the toolchain scaffold and restricted executable reference experiments. It has **no CRDT implementation or public API yet**. Sequence ordering, identity, undo, replication and the first release boundary still need an agreed contract.

## Undo questionnaire

[40 scenarios, local progress and JSON answer export](https://nickel-undo.shit.yachts/) support the design discussion. The standalone [questionnaire](questionnaire/README.md) has its own locked flake and is not a CRDT implementation or verifier.

## Run the checks

On x86_64 Linux with Nix:

```sh
nix flake check -L
nix build --no-link .#native .#proofs
nix develop
cargo test --workspace --offline --locked
```

The workspace has an empty library and a separate `proof-smoke` crate. Its `flip` function toggles a Boolean in a Rust range loop. The proof check extracts that actual function with the locked hax compiler, connects it to the imported `LoopUtil` interpreter, and proves parity and involution for every representable loop bound. It also changes the Rust loop to leave the Boolean unchanged and requires the unchanged bridge theorem to reject it.

These are toolchain checks, not CRDT correctness results. See [proof scope](proofs/README.md) and [provenance](PROVENANCE.md).

## Layout

- `src/`: future library; currently documentation only.
- `proof-smoke/`: independent Rust extraction fixture.
- `proofs/`: authored Latte sources and committed F* views.
- `scripts/`: extraction, proof checks and immutable external-model bootstrap.

## API and verification proposal

- [Prospective API and verifier obligations](docs/api-verification.md): operation shapes, preconditions, return/error contracts and the status of each intended theorem.
- [Local-undo analysis](docs/undo-semantics.md): selection versus effect semantics, literature alternatives, worked continuations and the unresolved sequence algorithm.
- [Consumer motivation and required witnesses](docs/carbon-contract.md): Carbon and potential Dark uses, separate from the library contract.

No sequence/undo verifier obligation is currently discharged. The proved Boolean loop is toolchain evidence only.

## Current reference candidate

[Own-action Undo and explicit Restore](docs/private-session-profile.md): running edit/restore/undo/redo selection over two independent identity-set documents, with private checkpoint continuations. This is a restricted research model, not the Rust core or an adopted complete undo API. The [Restore preview follow-up](docs/restore-preview.md) adds inspect/confirm calls bound to the exact document/private basis.

## Roadmap and next decision

[The implementation roadmap](ROADMAP.md) proposes the first usable native
release, an earlier experimental crate, and Rust/proof/consumer acceptance gates. We are
still closing the reference profile, not implementing a CRDT engine. Next is
the skipped-history decision sheet and ordered-reference/API reconciliation;
no ordering algorithm is adopted by the roadmap.

The [response-led plan](docs/response-plan.md) preserves why Ren's questionnaire
answers displaced the earlier writer-exclusive activity recommendation.
The [consumer contract](docs/carbon-contract.md) retains motivation and witnesses,
not an adopted complete API. Carbon and possible Dark adapters remain separate.

The scaffold does not reopen the parked Dark or Loro projects. Copying their reusable loop reasoning is a scoped extraction.
