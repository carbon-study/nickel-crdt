# collection candidates

The executable evidence behind [docs/collection-contract.md](../../docs/collection-contract.md) (#68, phase 1). It is a research model, not the Rust core, and is not wired into CI. The adopted traces belong in the eventual implementation gate.

```sh
node model.mjs 4    # 6 variants vs the constraint traces, then a search of all histories up to 4 commands (~1 s)
node verify-k.mjs   # asserts the K1/K2 stories under every option, plus the restore continuation
node adopted.mjs    # asserts that exactly the adopted variant matches the constraints and Ren's answers
```

`verify-k.mjs` and `adopted.mjs` assert, and exit nonzero on a failure. `model.mjs` only reports. Importing `model.mjs` runs nothing.

- **Model:** one entry key, one field, writers A–C. The commands are put (create-or-write), remove, undo, and restore. A command that does nothing stays local. Decisions are frozen against the author's captured past. Redo is not modelled.
- **Variant names:** `removeMode/undoCreate` (see the header of `model.mjs`).
- **Coverage:**
  - The search compares each axis's first two options only. `undoCreate=removes` was added later and is checked on the asserted stories only.
  - The bounded search is evidence, not a completeness proof.
