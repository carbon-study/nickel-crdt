# reviewable Rust translations

`Nickel_crdt.Edit.fst`, `Nickel_crdt.Event_layer.fst` and
`Nickel_crdt.Event_shell.fst` form the pinned edit extraction: production
`Replica::new`, `receive` and `edit`, plus the explicitly retained thin text
proof-bridge functions. `Nickel_proof_smoke.fst` is the separate
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

The complete extraction commands (the semicolon is one literal argument) are
below. `validate_new` is an explicit proof-facing root: a mutant that removes
its runtime call must still check the theorem referring to its result, rather
than fail because extraction omitted its declaration.

```sh
"$NICKEL_HAX_BIN" -C --offline --locked -p nickel-crdt ';' into \
  --output-dir "$out/edit" \
  -i '-** +nickel_crdt::edit::**::receive +nickel_crdt::edit::**::edit +nickel_crdt::edit::**::new +nickel_crdt::edit::**::validate_new +nickel_crdt::edit::fact_equal +nickel_crdt::edit::push +nickel_crdt::edit::duplicate_events +nickel_crdt::edit::has_event +nickel_crdt::edit::has_fact +nickel_crdt::edit::choose_unseen +nickel_crdt::edit::clone_selected_fact +nickel_crdt::edit::canonical_step +nickel_crdt::edit::canonical +nickel_crdt::edit::ready +nickel_crdt::edit::choose_ready +nickel_crdt::edit::frontier +nickel_crdt::edit::validate_after +nickel_crdt::edit::extend_past +nickel_crdt::edit::past_pass +nickel_crdt::edit::past +nickel_crdt::edit::select_basis +nickel_crdt::edit::event_basis +nickel_crdt::edit::interpret_scheduled' fstar
"$NICKEL_HAX_BIN" -C --offline --locked -p nickel-proof-smoke ';' into \
  --output-dir "$out/smoke" -i '-** +!nickel_proof_smoke::flip' fstar
for name in Edit Event_layer Event_shell; do
  diff -u "proofs/generated/hax/Nickel_crdt.$name.fst" "$out/edit/Nickel_crdt.$name.fst"
done
diff -u proofs/generated/hax/Nickel_proof_smoke.fst "$out/smoke/Nickel_proof_smoke.fst"
# after inspecting the differences:
cp "$out/edit/"*.fst proofs/generated/hax/
cp "$out/smoke/Nickel_proof_smoke.fst" proofs/generated/hax/
nix build --no-link .#proofs
```

Commit the Rust, translation and any corresponding proof changes together.
A matching snapshot is an inspectable translation and a reproducibility/drift
check, not a proof that Rust and F* have equivalent semantics. hax's lowering,
external models and the rest of the compiler/solver chain remain trusted; in
particular, the pinned backend structurally lowers `PartialEq` operators.
