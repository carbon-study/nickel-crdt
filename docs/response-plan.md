# PR1 plan based on ren's responses

This is the revision plan for [PR1](https://github.com/carbon-study/nickel-crdt/pull/1), based on Ren's completed questionnaire edition2026-11-01.1. It replaces “approve the current contribution-deactivation proposal” as the next decision. Ren's desired behavior is the design target to investigate; Rotbot's answers provide comparisons, not a vote against it. The exported answers remain unchanged and are not republished here.

## 1. put the hybrid undo behavior first

The first question is now: **when another writer deletes my text, can my undo restore it, and what does their next undo/redo do?**

Ren requests this in q03, q18, q19, q23 and q40. It conflicts with the draft's restriction that an undo selects only its own writer's item and that only that writer changes its activity. Calling the action local does not remove this conflict. The current single-origin activity proposal is suspended as a release recommendation until this behavior is specified. Registers cannot silently inherit sequence semantics: q13–q15 require a different continuation from simply deactivating hidden writes.

Do not assume a shared stack or put a foreign command on a local stack yet. Those are possible representations, not the requested behavior itself. First specify eligible actions and their visible and history effects.

### first reviewable trace

Use these named actions, keeping identities distinct from spelling:

| step | event | required observation / question |
| --- | --- | --- |
| 1 | Alice inserts b; both receive it | both display b |
| 2 | Bo deletes that b; both receive it | both display empty text |
| 3 | Alice presses undo | Ren wants b restored by undoing Bo's deletion, rather than withdrawing Alice's insertion |
| 4 | Bo presses undo | Ren wants the already-undone deletion skipped; define what happens if no older eligible action exists, and repeat with an older action present |
| 5 | redo on each writer | define whose redo can delete b again, which action it selects and how the other writer's next selection changes |

For every step show the selected semantic action, text, each session's next undo/redo action, returned result and new replicated information. The proposed trace must then cover:

- Bo's undo concurrent with Alice's restoration, followed by delayed delivery in both orders;
- two independent deleters, linking q07 to this rule;
- one delete spanning text from several creators: can a victim restore only their part, or the entire delete? How does this interact with atomic items?
- replacement where restoration should keep the replacement's inserted x, as in q11/q19;
- repeated undo/redo, duplicate updates and a fresh reader receiving the saved document;
- a peer with an old private undo session reconnecting after someone else has already undone its deletion.

These are the next requested specifications, not filled-in outcomes or an implemented protocol. Do not silently assume last-writer-wins activity, message-count toggles or remote stack mutation.

## 2. organize the remaining responses by consequence

| area | response IDs | planned contract change |
| --- | --- | --- |
| ordinary selection | q01–q02 | retain own-device/session selection as the baseline, with explicit victim-restoration exceptions |
| independent text | q05–q06, q08–q10, q12, q29 | retain independent insertions and equal-spelling distinctions; require whole concurrent runs rather than arbitrary character interleaving |
| deletion conflicts | q07, q11, q18–q23 | replace the draft's blanket active-remover rule with a complete account of restoration, overlapping deletes and cross-writer continuation |
| registers | q13–q17 | specify an ineffective undo after overwrite, its stack result and later Bo undo revealing red; decide why an equal-valued write behaves differently from a distinct text insertion |
| redo after new work | q04 | compare retaining a recoverable branch with linear discard; retaining data does not require automatically inserting it |
| grouping and children | q24–q29 | keep editor-owned time/grouping; use monotonic time in adapters; examine cancellation plus rerunning a derived job on redo; avoid engine clocks |
| hidden gaps and selection | q30–q34 | explain before/after and inside/outside at equal displayed positions; clarify the questions Ren did not understand before adopting an identity or restoration law |
| persistence and limits | q35–q39 | expose stack save/restore; distinguish private undo stacks from replicated identity/activity facts; explain resource limits with an actual offline-peer example |
| failure and rejected input | q38 | retain atomic rejection and make the rejected edit recoverable by the UI through an explicit return/ownership contract |
| implementation latitude | q22, q25, q27, q40 | prefer the simpler design where Ren allowed alternatives, but check it against all mandatory continuations rather than treating convenience as a blanket exemption |

The same option in q20/q21 does not imply the same trace: Ren assumes two undo presses where the questionnaire stipulated one. Preserve that changed premise. “Unsure” in q33/q34/q37 records an explanation failure, not rejection of those mechanisms. No additional40-question round is needed; use a few small worked examples.

## 3. research the behavior before selecting its representation

Map each proposed trace against the relevant paper's actual premises and criteria. Prakash/Knister informs selection, dependency conflicts, transposition/cancellation and historical gaps. Yu/Elvinger/Ignat is relevant to concurrent undo equivalence and supersession, but supplies neither victim eligibility nor cross-writer session bookkeeping. Stewen/Kleppmann provides a concrete register-restoration comparison, not a selected sequence policy. Read the outstanding OT/selective-undo leads where they address these traces; record gaps instead of claiming coverage from titles.

The deliverable is a complete finite-history reference semantics and a constructive algorithm/argument for the selected scope. A contradiction among desired observations is a decision to bring back to Ren. A failing candidate is retained evidence, not a reason to quietly narrow the requested behavior.

## 4. rewrite the API and proof contract to match

Once the trace semantics is agreed, revise all three companions together:

- `carbon-contract.md`: replace writer-exclusive undo recommendations and old witnesses that assume them; keep the library independent of Carbon/Dark adapters.
- `undo-semantics.md`: define eligibility, effect, concurrent resolution and continuation for the hybrid behavior, including an ineffective register undo. Name any deliberately unsupported case.
- `api-verification.md`: revise session selection, history results, authority/admission and checkpoint contracts. Specify what evidence lets a session skip or reinterpret an item after a peer's undo. Do not promise a globally identical private stack.
- `observation-catalogue.md`: link every accepted outcome to its full trace and pending theorem/test, retaining qualified alternatives. Accepted choices must work together; they are not independent lookup answers.

Keep V1–V9, strengthening their definitions as needed. In particular, V3 must cover authorized cross-writer restoration targets, V4 delayed activity and all future observations, V5 both writers' history continuation, and V8 cold reconstruction plus restored local sessions. The current Boolean proofs establish none of these.

## 5. implementation gate and PR scope

PR1 remains documentation/research planning. No engine or bindings are started by this plan. Any later authorized core slice must develop actual Rust transitions and their hax/Latte proofs together, using the agreed traces as witnesses and preserving failure evidence. Source-linked proofs and the broader algorithm argument remain required; a passing scenario list alone is not verification.

Keep sequence/undo/anchors first, exact scalar preservation, atomic multi-edit batches and checked receipts. Registers can be specified now without expanding the first engine slice. Numeric workloads, general ordering and resource bounds remain explicit decisions. Dark and the Loro fork remain parked; no integration or deployment follows from this plan.

**Next PR1 delivery:** the hybrid trace suite with both sessions' undo/redo continuations, a short clarification of the misunderstood questions, and a consistent revised semantic contract—or an exact conflict that needs a choice. Not another implementation of the earlier local-only activity model.
