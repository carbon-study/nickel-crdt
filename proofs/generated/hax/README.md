# reviewable Rust translations

`Nickel_crdt.Edit.fst` is the pinned hax extraction reachable from native
`Replica::new`, `receive` and `edit`. `Nickel_proof_smoke.fst` is the separate
Boolean-loop fixture. These are hax output, not Latte-authored proof views.
They do not cover all Rust in the repository.

The existing proof gate freshly extracts both positive programs and requires
exact byte equality with these files before verification. It still verifies
fresh output, not a substituted committed copy. Mutated Rust is also freshly
extracted and checked against the unchanged authored lemmas; it is deliberately
not required to match the positive snapshots. No path, whitespace or identifier
normalization is used.

To refresh after an intentional Rust/toolchain change, use the locked proof
shell and an empty temporary output directory:

```sh
nix develop --command bash
out=$(mktemp -d)
export NICKEL_HAX_BIN=$(command -v cargo-hax)
```

The complete extraction commands (the semicolon is one literal argument) are:

```sh
"$NICKEL_HAX_BIN" -C --offline --locked -p nickel-crdt ';' into \
  --output-dir "$out/edit" \
  -i '-** +nickel_crdt::edit::**::receive +nickel_crdt::edit::**::edit +nickel_crdt::edit::**::new' fstar
"$NICKEL_HAX_BIN" -C --offline --locked -p nickel-proof-smoke ';' into \
  --output-dir "$out/smoke" -i '-** +!nickel_proof_smoke::flip' fstar
diff -u proofs/generated/hax/Nickel_crdt.Edit.fst "$out/edit/Nickel_crdt.Edit.fst"
diff -u proofs/generated/hax/Nickel_proof_smoke.fst "$out/smoke/Nickel_proof_smoke.fst"
# after inspecting the differences:
cp "$out/edit/Nickel_crdt.Edit.fst" proofs/generated/hax/
cp "$out/smoke/Nickel_proof_smoke.fst" proofs/generated/hax/
nix build --no-link .#proofs
```

Commit the Rust, translation and any corresponding proof changes together.
A matching snapshot is an inspectable translation and a reproducibility/drift
check, not a proof that Rust and F* have equivalent semantics. hax's lowering,
external models and the rest of the compiler/solver chain remain trusted; in
particular, the pinned backend structurally lowers `PartialEq` operators.
