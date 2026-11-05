# provenance

The generic loop library and prelude were extracted, with Ren's explicit authorization, from Lynn's Dark work. Dark itself was read only and remains parked.

- Dark source revision inspected: `ed19a76a8ca66a05518803f5411d4975e08b71da`.
- Last source revision touching `Light/LoopUtil.lt`: `30c0c85eab3d72c5a645a2f895b3aae50305e633`.
- Original `Light/LoopUtil.lt` SHA256: `589f8dddbc293c057fcafcfcc6e1367cab709b411aaa0ba63c257b05fbb47e00`.
- Original generated `Light.LoopUtil.fst` SHA256: `6b73a71b7ab740207cccefde9dbc277a6815377e19a538eccab45a7a87583350`.

The loop source was renamed from `Light` to `Nickel`. The proof-cache/bootstrap helpers and smoke proof also adapt Lynn's existing harness and loop-shape work. This extraction does not redistribute the Dark application or the Latte compiler. The scaffold's authored code is offered under MIT; upstream toolchains retain their own licenses.

The committed Prelude, LoopUtil, Smoke, EditAtomic, EditCommit, EditIdentity and
EditAccepted views were re-emitted and compared byte-for-byte using local
`carbon-study/latte-nursery` revision
`0729bf34e2a7d9538604d951edc44d376d1b8ced` and its locked `.#cli` package. The
clean local checkout's CLI output matches the installed emitter used for that
comparison. An authorized local checkout can repeat the emission check with:

```sh
emitter=$(nix build --no-link --print-out-paths /path/to/latte-nursery#cli)
temporary=$(mktemp -d)
for name in Prelude LoopUtil Smoke EditAtomic EditCommit EditIdentity EditAccepted; do
  "$emitter/bin/latte" emit-fstar "$PWD/proofs/$name.lt" > "$temporary/Nickel.$name.fst"
  cmp "$temporary/Nickel.$name.fst" "proofs/generated/Nickel.$name.fst" || exit 1
done
rm -r "$temporary"
```

Run from the Nickel repository with that private checkout pinned to the named
revision. This confirms reproducibility with the recorded emitter, not compiler
correctness. That repository is private and has no selected license. Ren
directed Latte to remain private; publishing or vendoring its compiler is outside
the current cut. Public verification of generated F* is unchanged.

Public verification uses hax revision `f33e5c844497c057450ebf56828cbb191223e93a` and its pinned F* (2025.10.06), not normal Latte's newer F*. `flake.lock` records the complete public dependency graph. `proofs/generated/*.sha256` binds each local source/view pair; it is a drift check, not a compiler certificate.

The exact-content extension in `EditAccepted` uses the pinned F* standard
library's `FStar.Fin.pigeonhole` for finite coverage. It adds no project axiom or
admission; the ordinary upstream F*/model trust boundary remains in force.
Its updated view is emitted by the same private CLI revision recorded above.

The pinned hax translations are also committed under
[`proofs/generated/hax`](proofs/generated/hax/README.md). Its README gives the exact extraction scope and refresh commands.
The existing fresh-extraction proof gate requires byte-identical positive output;
mutant extractions still use their unchanged semantic proof obligations.
This makes translation changes reviewable, without proving Rust/F* semantic
equivalence or removing hax from the trusted boundary.

The canonical fact-order extension remains in `EditAccepted`, emitted by the
same pinned private CLI above. Its logical precondition conversion uses the
pinned standard `FStar.Classical.move_requires`/`move_requires_2` and
`forall_intro_2`; no project axiom is added.
The native Rust/hax snapshots are unchanged by this proof extension.

The conditional canonical/publication agreement extension also remains in
`EditAccepted`, emitted by the same pinned private CLI. It uses the pinned
standard `FStar.Seq` extensional-equality lemmas to pass from pointwise sequence
agreement to equality of the native fact vectors. The interpretation-publication
law targets the existing native interpreter, not an independently specified one.

The canonical storage-success extension is also emitted by the same private CLI
into `EditAccepted`. Its cardinality argument uses the already-pinned standard
`FStar.Fin.pigeonhole` and `FStar.Classical.move_requires`; it introduces no
project axiom or admission. It changes neither native Rust nor the committed
hax snapshot. The result concerns the extracted storage algorithm, not runtime
allocation guarantees or independent semantic refinement.
