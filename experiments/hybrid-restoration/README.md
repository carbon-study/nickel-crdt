# observed-concurrent restoration: directed reference candidate

The event-set portion is a research model for the [hybrid continuation](../../docs/hybrid-continuation.md), not Nickel's core, a selected undo protocol, a general session algorithm or a CRDT text-order implementation. It is separate from the Rust/hax proof scaffold. No parked Dark/Loro code is executed or changed.

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

Restoring a deletion effect of a replacement preserves that replacement's creation effects. Author undo of the whole replacement is one event carrying both the restoration mask and creator withdrawal for its inserted identities. Ordinary deletion restorations do not cancel creator withdrawals. Creator redo cancels that combined undo token; a peer's deletion redo can still hide the reactivated creation. This distinction repairs the review's replacement/deletion/undo counterexample. The fixture assumes the caller withdraws only its own creation; permission/admission is not implemented. The dictionary publishes that combined event in one `put`, so no prefix exposes only one facet of this authored undo. This does not establish general core transaction atomicity or admit arbitrary multi-event packets atomically. The event-set evaluator alone contains no permission checks, transaction grouping, insertion-order algorithm or selection/redo stack; the private-session layer below adds a restricted selector and redo state.

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

## private-session continuation slice

[sessions.py](sessions.py) adds the restricted writer/session profile specified in [private-session-profile.md](../../docs/private-session-profile.md). `session_check.py` generates actions through actual edit/undo/redo calls on two independent documents, then replays selected action-generated histories. It is no longer necessary to supply those undo masks by hand. The lower-level `check.py` remains useful for policy and malformed-reference fixtures. Existing event fixtures retain their meaning; the new writer tag is trusted metadata, not authentication.

```sh
nix run .#sessions
nix run .#sessions -- trace
# intentional contrasting policy, fails the consumed-bypass assertion:
nix run .#sessions -- retain
```

Ren rejected the reversible-skip candidate. The repaired profile consumes bypassed own items on an undo press; the retained-skip control rejects at `bypassed deletion must stay consumed after peer redo`. The locked check also verifies that the committed session trace matches freshly generated output. The session checks cover selection, own/victim undo, redo, imports, chosen checkpoint cuts, explicit keep/clear redo policy and clear-history facts. No text order, grouping/children, register behavior or full input/authority/resource admission is implemented. The version-2 checkpoint binds a private history to exact known shared facts, rejects missing/changed basis or later same-writer activity, and permits remote extensions. It is not a hostile-input codec or disk durability guarantee. Ordinary edits accept scalar values and allocate occurrence IDs internally. Redo updates private selection priority so the redone item, rather than an older-interleaved primary item, is undone next.

An initial nested-flake edit defined its dynamic apps attribute twice; evaluation rejected it before any check ran. The app definitions were grouped and the full locked check then ran. That evaluation failure is not counted as a test pass.

## bounded cold-session continuation check

```sh
nix run .#continuations
# deliberate broken reloads, each exits 1 with a replayable JSON counterexample:
nix run .#continuations -- drop-redo
nix run .#continuations -- drop-ignored
nix run .#continuations -- reset-counter
```

`continuation_check.py` enumerates a **fixed finite action vocabulary**, without
changing the proposed session policy. Its four starting pairs are empty, a synced
victim deletion with an older Bo item, partitioned independent deletes, and a
synced replacement. From each seed it explores at most three additional actions.
Each writer may have at most two creation-bearing events, counting the seed.
At each nonterminal prefix the choices are:

- either writer's undo, redo or clear-history;
- one fresh occurrence carrying scalar x, a singleton visible deletion, or a replacement
  of the whole current visible set by one fresh identity;
- both explicit `keep` and `clear` new-edit policies when redo is pending;
- delivery of any available event whose causal predecessors the receiver has,
  or a duplicate of any already-known foreign event.

The breadth-first search merges equal per-seed document/private states. It visits
1,526 per-seed states through depth three. At the 238 prefixes of depth zero,
one or two it tests every outgoing generated action: 3,419 edges. Each edge is
run uninterrupted and after JSON reconstruction of A, B, or both, giving 10,257
warm/cold comparisons. It compares the returned event or rejection, complete
shared event facts, visible identity sets and the next selected undo. The state
key includes private checkpoints so different future histories are not merged.
The comparator does **not** merely compare checkpoint bytes.

Every visited state also completes causal synchronization to both peers and
checks equal facts/visibility and unchanged private history (the next save may record a larger shared basis). This tests the
transport harness and import behavior; convergence of the event-set projection
is already built into this model. A 10,000-state budget fails the command rather
than turning unfinished exploration into a passing result.

[continuation-output.json](continuation-output.json) is the deterministic receipt.
The three [control witnesses](continuation-controls/) retain actual operation
failures: losing redo makes a redo return no event; forgetting cleared victim
sources makes undo restore a deliberately forgotten deletion; resetting the
allocator makes the next undo collide with an existing event ID. Each report
names its seed, action prefix, selected restart and warm/cold observations. It is
the first breadth-first counterexample in the first failing seed, not a globally
minimal counterexample across all possible histories. The locked check regenerates
both the receipt and all three reports and compares their bytes.

This is a **bounded codec/continuation regression**, using the same session and
effect implementation on both sides. It is not an independent intended-undo
oracle, an implementation-linked proof or a proof about arbitrary future traces.
The depth-three leaf states are synchronized but have no outgoing restart test.
Other multi-edit subsets, longer histories, grouping/children, registers, text
order, hostile checkpoints, real disk failure and split-brain writers remain
outside it. No policy choice becomes approved merely because its warm and cold
executions agree.

## collected PR4 review repair

[The profile](../../docs/private-session-profile.md) maps the repairs to the review:
compatible shared/private saves, library-owned equal-looking occurrences,
permanently consumed bypasses, preserved whole-deletion victim restoration,
redo-priority stamps. The follow-up below supersedes the earlier victim-first tie. The actual old failures
are in [session-review-before-repair.txt](session-review-before-repair.txt).
The old source remains at `15d06cf`; there was no history rewrite.

The locked check also requires these deliberately broken variants to fail:

```sh
nix run .#sessions -- unbound-save
nix run .#sessions -- caller-ids
nix run .#sessions -- old-redo-order
nix run .#sessions -- eager-consume
```

They respectively bypass saved-basis binding, derive occurrence IDs from values,
erase redo selection priority, or consume an older item the undo press never
bypassed. Existing effect-model negative controls are
unchanged. Session fixtures now assert generated occurrence IDs and scalar
values separately; passing equal-looking text alone cannot conceal lost identity.
The q07 visible-b oracle is unchanged; its internal selection now follows the
accepted creator-slot rule.

For the six review cases as actual generated observations, run
`nix run .#sessions -- review-trace`; the locked check compares its output with
[session-review-trace.json](session-review-trace.json). These values are shown
without claiming a text order.

## follow-up selection review: creator slots and no-op history

`nix run .#selection-review` now checks the **actual Session selector**, and exits
success only when its directed assertions hold. [selection-review.json](selection-review.json)
is regenerated and byte-compared by the locked check. The old failing comparison
is preserved at `490bb09`; Ren retracted its b,c overlap answer and accepted a,b.
The newest-touch alternative was not adopted.

A peer deletion is placed above the newest local creation item it targets, once
for its whole scope. Receipt timing does not rank it against local actions.
The checks exercise both deletion-before/after-redo arrivals, warm and reloaded;
grouped creations; one deletion spanning two creation items; the a,b overlap;
replacement chains; equal-value occurrences; clear before/after receipt; and
same-slot event-ID ties. Successful local redo still supplies a private priority
stamp, including a redone victim action. These slots use this profile's trusted
writer-local event counters; they are not text order or a general clock protocol.

Empty undo leaves both facts and private state unchanged. It does not consume
an ineffective item unless a later eligible action is actually selected in that
press. Visibly ineffective redo similarly leaves the pending entry, counter,
selection stamps and facts untouched. Warm/cold tests compare Bo waiting versus
pressing empty Undo, and a redo hidden by a later causal deletion. Extra controls:

```sh
nix run .#sessions -- empty-consumes
nix run .#sessions -- ineffective-redo-advances
nix run .#sessions -- receipt-ranking
```

Each deliberately broken variant must fail its named observation. See
[the profile](../../docs/private-session-profile.md) for the changed independent-
restoration and replacement continuations implied by ineffective-redo gating.
Keep-redo branch stacking remains provisional. The isolated checkpoint-content
fixture retains every saved event ID and changes only x to y; its presence-only-
basis control still fails independently of missing-event rejection.

No general intended-undo oracle, Rust transition, text-order engine or CRDT proof
is supplied by these finite checks. The admission and effect-model controls
remain unchanged; all V1–V9 obligations remain unfulfilled.
