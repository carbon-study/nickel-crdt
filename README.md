# nickel-crdt

A sequence CRDT library being built for Carbon, with proofs tied to its Rust implementation through hax and Latte. Lynn owns and maintains it.

This repository currently contains the toolchain scaffold. It has **no CRDT implementation or public API yet**. Sequence ordering, identity, undo, replication and the first release boundary still need an agreed contract.

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

## Next decision

Write the sequence/undo contract with concrete two-peer and cold-recovery examples before implementing the engine. In particular, decide what an invisible undo publishes, how independent peer edits survive, and which identities and ordering survive restoration. A matching method signature alone does not establish backend substitutability.

The scaffold does not reopen the parked Dark or Loro projects. Copying their reusable loop reasoning is a scoped extraction.
