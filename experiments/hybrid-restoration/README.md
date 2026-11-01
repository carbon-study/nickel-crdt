# observed-concurrent restoration: directed reference candidate

This is a research model for the [hybrid continuation](../../docs/hybrid-continuation.md), not Nickel's core, a selected undo protocol, a general session algorithm or a CRDT text-order implementation. It is separate from the Rust/hax proof scaffold. No parked Dark/Loro code is executed or changed.

## run

```sh
nix flake check -L .
nix run .
```

The nested flake pins the same nixpkgs revision as the project, with Python as its only runtime dependency. It neither extends the core's dependency graph nor deploys anything. Run from this directory to select its development shell. `nix run . -- target-only` and `nix run . -- all-known` intentionally fail the unchanged expected observations.

## exact candidate

A deletion has separately addressable atoms `(deletion-event ID, element ID)`. A restoration's author selects a deletion effect D, takes its original target set T, and captures a mask from its current causal view:

- include D's atoms;
- include atoms on T from other **observed concurrent** deletions;
- exclude unobserved deletions and any causally earlier/later deletion.

The mask is frozen into the restoration event. A receiver unions masks from uncancelled restoration events; it never reselects their targets. A fresh personal-redo event cancels the named restoration token; another writer's token remains. A later undo creates a fresh token rather than un-cancelling an old one. This explores the simpler personal-redo alternative permitted by Ren; it does not demonstrate that this is the simplest complete design.

Restoring a deletion effect of a replacement preserves that replacement's creation effects. Author undo of the whole replacement is decomposed into a restoration event plus a removal of its inserted identities. The fixture assumes these share one eventual atomic user action; **this model does not implement atomic multi-event publication**. The model contains no permission checks, transaction grouping, insertion-order algorithm or selection/redo stack.

## checks and their boundary

Eight directed fixtures replay20 legal causal schedules. At each prefix they check an immediate duplicate, a JSON full-log reconstruction through `put`, equality of live removal atoms, and continuation to the expected final visible ID set. Late reverse-order duplicates are also checked. These are crafted event sets, not generated histories or a user model. The causal scheduler and the evaluator are ordinary Python, not extracted/proved code.

The two policy negative controls fail at their intended unchanged assertions:

- target-only restoration fails **q07 observed concurrent deletes**;
- cancelling every known deletion fails **later deletion remains through author undo**.

Passing the first check on the observed-concurrent law shows compatibility with this q07 fixture, not acceptance of its behavior for unseen concurrent deletions. The retained unseen-concurrent fixture instead leaves b hidden. That is a proposed boundary, not an answer Ren has supplied.

The log decoder assumes this model's JSON structure. `put` checks explicit prerequisites and duplicate-event equality only. It is not full semantic admission: no malformed-input suite, authority proof, parser/resource bound, independent reference oracle, compact checkpoint or disk failure acceptance is claimed. The fixed-event-set calculation is delivery independent by construction; the schedule count is a regression receipt, not the main argument for a general CRDT.

`model.py` and `check.py` are authored for this candidate. The earlier model supplied by Ren remains unmodified in the local evidence store; its40 schedules and q07 disagreement are recorded in [hybrid-traces.md](../../docs/hybrid-traces.md). We did not replace its expected result and relabel it passing.
