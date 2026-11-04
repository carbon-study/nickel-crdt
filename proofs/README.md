# proof scope

`Smoke.lt` proves the extracted Rust `flip` function equals a simple range interpreter, then proves its parity result and that applying it twice returns the input. `LoopUtil.lt` supplies reusable range-loop interpretation and induction lemmas. Its invariant parameter follows the pinned hax representation: it is an annotation, not an independently enforced loop invariant.

The check freshly extracts Rust in isolated positive and mutation workspaces. Both use the same authored theorem statements. Replacing the loop's toggle with identity must fail `Nickel.Smoke.flip_bridge` as a proof obligation; a timeout or extraction error is not an accepted control result. The native test must also detect the mutation.

The locked public flake checks committed F* views directly. It checks source/view receipts for accidental drift, but a hash receipt does not prove compiler correctness or that a view was emitted from its source. Latte is currently a private, unlicensed regeneration dependency; its compiler is not bundled or fetched by this public flake. See the exact local regeneration provenance in ../PROVENANCE.md. Until that dependency can be published, anonymous users can reproduce F* verification and Rust extraction, not Latte emission.

Trusted dependencies include Rust compilation, hax translation, Latte emission, F*, its solver and external Rust models. The external models are checked once in an immutable Nix output; each proof workspace uses that exact cache. No own admissions, hint replay or stale hash bypass is used. Ordinary proof commands have a 60-second wall limit; external-model bootstrap has a separate 180-second allowance.

The smoke fixture establishes no CRDT convergence, ordering, undo, codec, Wasm or browser property.

The [prospective API/verification contract](../docs/api-verification.md) lists the proposed V1–V9 obligations. None is currently discharged. The [undo analysis](../docs/undo-semantics.md) records the semantic/algorithmic stop gate; the loop proof does not bypass it.

## actual edit/admit return paths

`EditAtomic.lt` proves complete-instance neutrality on admission errors/duplicates
and local errors/empty results, plus the successful local counter step, against
freshly extracted `src/edit.rs`. Three wrong native bodies must fail their
unchanged lemmas and native tests. `scripts/check-edit-proofs.mjs` runs inside
the existing `.#proofs` gate, using the same immutable models and limits. These
are universal return-path results, not local/admission semantic refinement,
FugueMax representation, freshness or convergence. See the
[candidate contract](../docs/rust-edit-admit.md) for the precise domain and
remaining joint exit. No full V1–V9 obligation is thereby closed.

## positive author/admit coherence

`EditCommit.lt` binds an authored fact to its request, proves replay into the
author's before-state matches its complete facts/tree commit, and proves remote
admission preserves and is independent of private writer/allocator state. Their
composition covers an actual second receiver with the same shared before-state
and limits but different private state. Five additional wrong Rust bodies test
returned-fact binding, stale-tree publication, receiver allocator preservation,
request-gap binding and private-state independence. All run in the existing
proof gate; optional explicit mode names support focused local checks, while
the default keeps all controls. This is joint commit coherence, not successful
refinement to the independent reference, WF preservation, ordering or convergence.

## identity classification

`EditIdentity.lt` proves the actual range scan equals a recursive first-ID
lookup, and carries it through public `receive` and successful local `edit`:
known IDs classify by exact fact equality; invalid counters reject; Added and
Authored event IDs are absent from the before-facts. Known-member classification
requires unique before-IDs; freshness does not. This is not WF preservation,
whole refinement, global writer fencing or ordering.

The pinned backend structurally lowers `PartialEq` operator calls. An ordinary
`fact_equal` call plus its exactness lemma preserves source sensitivity at the
identity guard; separate lemmas check handwritten ID equality. Five native and
F* mutation controls cover these laws. The candidate contract records the
reproduced erased-comparison blind spot and the remaining trust boundary.
