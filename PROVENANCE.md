# provenance

The generic loop library and prelude were extracted, with Ren's explicit authorization, from Lynn's Dark work. Dark itself was read only and remains parked.

- Dark source revision inspected: `ed19a76a8ca66a05518803f5411d4975e08b71da`.
- Last source revision touching `Light/LoopUtil.lt`: `30c0c85eab3d72c5a645a2f895b3aae50305e633`.
- Original `Light/LoopUtil.lt` SHA256: `589f8dddbc293c057fcafcfcc6e1367cab709b411aaa0ba63c257b05fbb47e00`.
- Original generated `Light.LoopUtil.fst` SHA256: `6b73a71b7ab740207cccefde9dbc277a6815377e19a538eccab45a7a87583350`.

The loop source was renamed from `Light` to `Nickel`. The proof-cache/bootstrap helpers and smoke proof also adapt Lynn's existing harness and loop-shape work. This extraction does not redistribute the Dark application or the Latte compiler. The scaffold's authored code is offered under MIT; upstream toolchains retain their own licenses.

The committed Prelude, LoopUtil, Vector, Smoke, EditAtomic, EditCommit, EditIdentity,
EditAccepted and EditWellFormed views were re-emitted and compared byte-for-byte using local
`carbon-study/latte-nursery` revision
`0729bf34e2a7d9538604d951edc44d376d1b8ced` and its locked `.#cli` package. The
clean local checkout's CLI output matches the installed emitter used for that
comparison. An authorized local checkout can repeat the emission check with:

```sh
emitter=$(nix build --no-link --print-out-paths /path/to/latte-nursery#cli)
temporary=$(mktemp -d)
for name in Prelude LoopUtil Vector Smoke EditAtomic EditCommit EditIdentity EditAccepted EditWellFormed; do
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

The scalar-domain extension, now in `EditWellFormed`, uses the same pinned emitter and existing LoopUtil
range semantics. The native scalar helper and two preceding validator loops
now extract as executable `fold_range_return` rather than the pinned opaque
generic iterator `fold_return`. No semantics is invented for that opaque value;
no model axiom or budget is changed. The committed native hax snapshot is
refreshed and checked against fresh extraction. Other native function snapshot
changes are generated hoist-variable alpha-renaming; the validator body and
new scalar helper carry the substantive translation changes. This does not
prove old/new Rust equivalence or eliminate the hax trust boundary.

The direct causal-reference extension is in `EditWellFormed`, emitted by the
same private CLI revision above. Its indexed `validate_after` helper factors the
existing `past` existence guard; the reviewed translation snapshot changes only
that helper and its `past` caller. These source-bound results retain hax and the
external models as trusted translation boundaries.

The WF-module split mechanically moves the scalar and direct-reference contracts
from EditAccepted to EditWellFormed, including their statements and proof bodies,
with only owned namespace changes. Both regenerated views use that same emitter;
no Rust, native hax extraction or external model changes accompany the split.

The EditAtomic contract/pattern reform uses the same private emitter revision
above. All five universally quantified lemma statements and parameters are
unchanged, with setter pattern metadata added. Automatic checking replaces the
manual normalization bodies; the actual public counter call retains its prior
shallow SMT request. Rust and the committed hax translation remain unchanged.

The Atomic contract-isolation repair uses the same private emitter. It adds a
complete calculator-value contract while retaining all five existing universal
statements. The actual edit-boundary proof prunes the two callee fact namespaces
when composing their contracts. Two default proof-dependency controls remove
the setter pattern and calculator-contract call separately; both require an
ordinary named public-counter rejection against the same actual extraction.
They are not native semantic mutants. All earlier native controls, hax snapshot
binding, model trust, classifier and proof limits remain unchanged.

The LoopUtil/Smoke proof reform uses the same pinned private emitter. Every
existing universal lemma signature is unchanged. All explicit normalization is
removed from those two authored modules, including the interpreter boundary
laws. The new plain-for invariant rule is derived recursively over the pinned
`Rust_primitives.Hax.Folds.fold_range`; its caller supplies initialization,
step preservation and the final condition. It does not trust hax's annotation
as an invariant. Smoke's existing exact-parity theorem now uses that rule on
the actual extracted Rust loop. No native source, hax snapshot, imported model,
axiom, compiler/query limit or driver-budget formula changes accompany this cut.

The plain-loop isolation continuation retains the same emitter and models.
The plain interpretation/induction callers and both actual Rust smoke boundaries
withhold the `fold_range` facts; the interpretation proof also withholds its
`option_run` model facts. Their step/end/induction contracts are tested by
removal controls. The two plain `_any` adapters now use the pinned standard
`FStar.Classical.move_requires_3`/`forall_intro_3` introduction functions, with
ordinary universal conclusions instead of an explicit recursive-function
trigger. Only pattern metadata changes in those conclusions; their logical
premises, quantification and postconditions are unchanged. No Rust/hax snapshot,
axiom, tool pin or proof-budget change accompanies the continuation.

The smoke involution consumer additionally prunes the actual Rust function
facts and composes its two parity-contract calls. Separate default removals of
each call make that dependency observable.

The return-capable loop preservation continuation also composes its model
step/end contracts with `fold_range_return` facts withheld. Standard Classical
introduction replaces the universal adapter's explicit recursive trigger,
without changing its logical type. The native scalar soundness and valid-input
success boundaries use that rule without normalization; their own validator
body remains visible. No model, extraction, compiler or budget change is made.

The Result-oriented return-loop specialization composes the preserved general
rule and exposes successful/error conditions. Its actual scalar callers
withhold step_safe/output_safe as well as the fold model. This changes neither
prior theorem types nor the native extraction. Its universal-introduction
scaffold uses the same pinned standard-library lemmas; no axiom is added.

The Result step's three repeated matches are factored into the transparent
`result_step` predicate. Its contents are unchanged. Focused verification also
checks the current implementation against the exact previous inline universal
contract, not just the refactored signature; existing actual caller and native
controls remain. The remaining-family candidate factors universal introduction through the existing
Classical move-requires/forall-introduction functions. It changes the option and
break adapters' trigger metadata, without changing their logical statements.

`Vector` contains checked equations over the already-pinned hax models
(vector contents/length and slice length/index). It is emitted by the same
private CLI revision above. It adds no assumed equation and changes no imported
model. Four Accepted callers withhold those model functions and use the proved
contracts; other imported model definitions remain available.

The remaining-family candidate ports the previously held EditCausal rank/path
proofs without strengthening their claims. It reuses the same native/hax
translations and imported model trust, including identity-refined derived Clone.
The additional empty-vector equation and constructor/validation-prefix contracts
are proved in the project; they are not new imported assumptions.
