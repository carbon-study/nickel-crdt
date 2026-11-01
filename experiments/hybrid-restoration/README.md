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

The mask is frozen into the restoration event. There is no separate selected-target-ID field: two local selections can produce identical masks and identical replicated events. A private checkpoint may retain the selected item if its UI/history contract needs it; the shared projection does not need that additional field in these cases. A receiver unions masks from uncancelled restoration events; it never reselects their targets. A fresh personal-redo event cancels the named restoration token; another writer's token remains. A later undo creates a fresh token rather than un-cancelling an old one. This explores the simpler personal-redo alternative permitted by Ren; it does not demonstrate that this is the simplest complete design.

Restoring a deletion effect of a replacement preserves that replacement's creation effects. Author undo of the whole replacement is one event carrying both the restoration mask and creator withdrawal for its inserted identities. Ordinary deletion restorations do not cancel creator withdrawals. Creator redo cancels that combined undo token; a peer's deletion redo can still hide the reactivated creation. This distinction repairs the review's replacement/deletion/undo counterexample. The fixture assumes the caller withdraws only its own creation; permission/admission is not implemented. The dictionary publishes that combined event in one `put`, so no prefix exposes only one facet of this authored undo. This does not establish general core transaction atomicity or admit arbitrary multi-event packets atomically. The model contains no permission checks, transaction grouping, insertion-order algorithm or selection/redo stack.

## checks and their boundary

Twelve directed fixtures replay28 legal causal schedules, plus a check that two local targets can produce the same wire event. At each prefix they check an immediate duplicate, a JSON full-log reconstruction through `put`, equality of live removal atoms and creator-withdrawal tokens, and continuation to the expected final visible ID set. Late reverse-order duplicates are also checked. These are crafted event sets, not generated histories or a user model. The causal scheduler and the evaluator are ordinary Python, not extracted/proved code.

The five policy negative controls fail at their intended unchanged assertions:

- target-only restoration fails **q07 observed concurrent deletes**;
- cancelling every known deletion fails **later deletion remains through author undo**;
- using an ordinary delete to hide an undone creation fails **creator withdrawal survives peer deletion undo**;
- dropping the target-set filter fails **overlap restoration stays in selected scope**;
- splitting the compound undo into two events fails the **half-published compound undo** prefix assertion, even though its final p-only result is correct.

Passing the first check on the observed-concurrent law shows compatibility with this q07 fixture, not acceptance of its behavior for unseen concurrent deletions. The retained unseen-concurrent fixture instead leaves b hidden. That is a proposed boundary, not an answer Ren has supplied.

The log decoder assumes this model's JSON structure. `put` uses explicit `ModelError` exceptions for missing prerequisites, conflicting duplicates, non-ancestral/invalid deletion releases, unknown/non-ancestral/non-token cancellations and unknown/non-ancestral creator withdrawals. All these checks precede publication. Ten invalid-reference cases check unchanged event dictionaries, including under `python -O`; optimization does not disable these guards. This is still not full semantic admission: no general malformed-shape input suite, authority proof, parser/resource bound, independent reference oracle, compact checkpoint or disk failure acceptance is claimed. The fixed-event-set calculation is delivery independent by construction; the schedule count is a regression receipt, not the main argument for a general CRDT.

`model.py` and `check.py` are authored for this candidate. The earlier model supplied by Ren remains unmodified in the local evidence store; its40 schedules and q07 disagreement are recorded in [hybrid-traces.md](../../docs/hybrid-traces.md). We did not replace its expected result and relabel it passing.

## retained review failure

`review-before-repair.txt` records the old law revealing both p and x in all three review schedules, and the scope-spill control restoring unrelated c. The repaired p-only assertion was not weakened. Creator withdrawal is now a separate fact class; ordinary deletion/restore fixtures retain their earlier required text outcomes. An initial edit command used Node inside this Python-only nested shell and did not apply; the resulting missing-field TypeError is not counted as a semantic failure or passing check. The patch was then applied using the declared Python environment.

## collected audit follow-through

The peer audit read the pre-repair afc8eae source. Its creator-withdrawal finding was already addressed by the first repair; the remaining gaps led to the combined undo event, prefix oracle and explicit causal-reference guards described above. The earlier source and outputs remain in Git history. The positive schedule count drops when two effect facets become one event; the original p-only oracle is unchanged. Validation under optimization is tested separately from the ordinary assertion-based regression oracles.
