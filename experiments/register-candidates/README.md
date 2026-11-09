# register candidates

The executable evidence behind [docs/register-contract.md](../../docs/register-contract.md) (#67, phase 1). It is a research model, not the Rust core. It is not wired into CI. The adopted traces belong in the eventual implementation gate.

```sh
node model.mjs 4      # 48 variants vs Ren's q13–q17, then a search of all histories up to 4 commands (~3 s)
node model.mjs 5      # the same up to 5 commands: 1,474,110 histories (~2.5 min)
node verify-q.mjs     # asserts the five follow-up stories: per-step values and command reports for both options
node adopted.mjs      # asserts the adopted variant against q13–q17 and the follow-up answers
```

All three scripts exit nonzero on a failed assertion.

- **Model:** a history lists commands in creation order. Each command records its author and what it has seen. Replicated facts are writes, and undo/redo commands that take effect. A do-nothing undo/redo stays local. Decisions are frozen against the author's captured past.
- **Variant names:** `family/blocked/redo/noEdit/clear`. See the header of `model.mjs`.
- **Coverage:** the search covers only these variants within the stated bound (three independently named writers, two values). It is evidence, not a completeness proof.
