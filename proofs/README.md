# proof scope

`Smoke.lt` proves the extracted Rust `flip` function equals a simple range interpreter, then proves its parity result and that applying it twice returns the input. `LoopUtil.lt` supplies reusable range-loop interpretation and induction lemmas. Its invariant parameter follows the pinned hax representation: it is an annotation, not an independently enforced loop invariant.

The check freshly extracts Rust in isolated positive and mutation workspaces. Both use the same authored theorem statements. Replacing the loop's toggle with identity must fail `Nickel.Smoke.flip_bridge` as a proof obligation; a timeout or extraction error is not an accepted control result. The native test must also detect the mutation.

The locked public flake checks committed F* views directly. It checks source/view receipts for accidental drift, but a hash receipt does not prove compiler correctness or that a view was emitted from its source. Latte is currently a private, unlicensed regeneration dependency; its compiler is not bundled or fetched by this public flake. See the exact local regeneration provenance in ../PROVENANCE.md. Until that dependency can be published, anonymous users can reproduce F* verification and Rust extraction, not Latte emission.

Trusted dependencies include Rust compilation, hax translation, Latte emission, F*, its solver and external Rust models. The external models are checked once in an immutable Nix output; each proof workspace uses that exact cache. No own admissions, hint replay or stale hash bypass is used. Project modules retain a 60-second per-compiler limit. Cold imported-model
bootstrap allows 180 seconds per compiler under a 600-second make-driver guard;
dependency discovery has its own 60-second guard. These are distinct command
budgets, not a claim about termination of every detached descendant. Solver
settings and proof obligations are unchanged. Successful model outputs retain
`bootstrap.log` and `bootstrap.stats.json`, including per-module F* wall times.
`check-proof-timeouts.mjs` exercises the actual make/timeout wiring using an
explicitly simulated compiler; those fixtures never enter the real model cache.

The smoke fixture establishes no CRDT convergence, ordering, undo, codec, Wasm or browser property.

The [prospective API/verification contract](../docs/api-verification.md) lists the proposed V1–V9 obligations. None is currently discharged. The [undo analysis](../docs/undo-semantics.md) records the semantic/algorithmic stop gate; the loop proof does not bypass it.
