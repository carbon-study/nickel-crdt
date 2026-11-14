# Gate-specific script inputs

The text proof gate and causal-envelope proof gate used to include every file
under `scripts/`. A change to the separately run Latte capture helper therefore
changed both proof derivations even though neither gate reads that helper.

`nix/gate-scripts.json` now supplies their script filesets, plus the existing
model-builder, shared-native, register-native and register-proof script inventories. Each list is the exact
transitive module-import closure of its entry points. The Rust, tests, authored
proofs, retained views and receipts in each gate's source set are unchanged.
Text cores/shards still share one script closure: this does not partition
individual contract-family inputs or narrow native Rust dependencies.

## Check the actual packages

```
nix build --no-link .#gate-inputs
node --experimental-vm-modules scripts/check-gate-inputs.mjs
node scripts/check-gate-derivations.mjs /absolute/new/evidence-directory
```

The Nix check inspects the **actual packaged script directories**, including the
model builder, and compares every script byte with the source. Node's module
parser supplies static import/export dependencies without running gate bodies.
Literal dynamic imports are included; other dynamic-import forms refuse. That
recognizer is deliberately conservative and can refuse apparent imports in
comments/strings. It is not a general JavaScript dependency analyzer.

The check also exercises missing/extra dependencies, a new dynamic dependency,
unsupported imports and syntax errors. It runs in the existing native CI job;
there is no extra runner or change to the proof jobs, modes or timeout budgets.

The derivation check copies tracked working bytes into a temporary flake, edits
one input at a time, and evaluates real derivation identities on both declared
architectures. It never edits the checkout or builds the proof matrix. Its output
directory must be new. It checks these invalidation boundaries:

| changed input | affected existing derivations |
|---|---|
| Latte setup helper / unrelated comparison script | none |
| text contract checker | all text proof cores/shards/full gate |
| causal-envelope checker | shared proofs |
| shared-native checker | shared native |
| register-native checker | register native |
| register-proof checker / authored Register or Canonical proof | register proofs |
| mutation scope helper | text proofs, shared proofs, shared native and both register gates |
| proof runtime/cache helper | model cache and every consuming gate |
| model builder / model budget checker | model cache and consuming proof gates |
| authored text proof | text proofs |
| text Rust implementation | native, edit reference, shared native, text proofs and both register gates |

All script edits also invalidate the cheap `gate-inputs` check. These are
**derivation dependencies**, not measured end-to-end CI speedups. Workflow jobs
still launch; Nix can reuse unchanged derivations only if their outputs are
available. This PR does not supply a binary cache or change cache policy.

## Changing a gate

When adding/removing an imported script, update its sorted list in
`nix/gate-scripts.json` and run the checks above. Missing imports fail the audit
rather than silently disappearing from the package. Filesystem asset reads,
subprocess programs and newly introduced entry points still need an explicit
source/packaging review; an import closure alone cannot infer those dependencies.
The existing non-script source sets remain conservative.

New independent gates need their own reviewed entry points, manifest list and
actual packaged-directory argument in the check. Both register inventories are included even while the register checkpoint remains
a draft; packaging coverage is not semantic checkpoint acceptance.
