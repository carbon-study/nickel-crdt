# register contract (#67, phase 1)

**Status: proposed contract for review. Nothing is implemented.** It fixes the register behaviour that #67's phase 2 will implement and prove.
- **Answered by Ren:** the outcomes in §4's table: the undo questionnaire's q13–q17, plus follow-ups f1–f7 answered on 2026-11-08. The `own` trace is a consequence of those answers, not one of them.
- **Proposed:** a do-nothing redo uses up its entry (rule 5).
- **Held:** one choice, for the sequence undo stack (§5). Executable evidence: [experiments/register-candidates](../experiments/register-candidates/README.md).

## 1. what a register is

A register holds one value per key. Carbon's uses are:
- reading positions, keyed by (book, device)
- runtime settings, keyed by (plugin, setting)
- whole-list orderings
- record fields

Keys are caller data. A key is not a writer, and nickel never infers one from the other. Different keys are independent registers. Writes to one key can still be concurrent, for example from two tabs or a restart, and follow the rules below.

## 2. replicated facts and local commands

- **Replicated facts:**
  - every **write(v)**. It has ID `(writer, counter)` as for edit events, records its causal past, and records its **observed value**: the visible value in that past.
  - every **undo or redo that takes effect**, naming its target write
- **Local only:** an undo or redo that does nothing. Peers never see it.
- **Frozen decisions:** a write's observed value, and whether an undo or redo takes effect, are decided against the author's captured past. That is the author's own local history plus the replicated facts it has seen. Facts received later never revise them.
- **Stacks:** undo and redo are per-writer stack commands over that writer's own items, as in the own-action sequence profile.

## 3. the rules

1. **Only edits count.** A write whose value equals its observed value is no edit. It never counts for the visible value or for blocking. It pushes no undo item and leaves the redo stack alone (Ren: q17, follow-up 4).
2. **Activity.** A counted write is active until its author's undo deactivates it; a redo reactivates it. Only the author toggles it, so activity is a single-writer chain.
3. **Visible value.** Take the causal maxima among active counted writes. If there are none, the value is the initial one. Otherwise it is the deterministic winner: highest Lamport time, then writer order. A write's Lamport time is 1 + the highest Lamport time among the **replicated facts** in its causal past. It is carried with the write, so every peer computes the same order. Do-nothing commands are local and never advance it (`lamport` trace). Losing concurrent writes stay in the state, so undoing the winner reveals them (q16).
4. **Undo** targets the author's latest own item. It does nothing if a later counted write has that item in its causal past, whatever its value, and that write is either still active or by **another user**, even if he has since undone it (q13, q15, follow-ups 5–6; see the [producer-to-user ownership obligation](checkpoint-representation-decisions.md#producer-identity-does-not-settle-undo-ownership)). The author's own later writes block only while active, so consecutive own undos work. Otherwise it deactivates the target. A do-nothing undo reports that someone else edited, and **uses up its item**: a later undo does not retry it and reports no item (follow-up 3).
5. **Redo** reactivates the latest undone item. It does nothing under the same blocking condition, applied to counted writes made after that undo (q14, follow-ups 2 and 7). A do-nothing redo also uses up its entry. That part is **proposed**, by analogy with f3, which Ren answered for undo only. The model does not vary it.

**Principle (Ren, 2026-11-08): undos are not composed across users.** A user's undo or redo is decided once, against that user's own captured past. Another user's later undo never revives, re-enables or re-targets it. Rule 4's "another user, even if since undone", rule 5 and the frozen decisions of §2 are this principle. f2, f3 and f5–f7 are its witnesses.

Every rule depends only on the merged causal history and on decisions frozen at creation. So replicas that admit the same facts expose the same value.

## 4. the outcomes these rules must reproduce

All of these are asserted by `adopted.mjs`. f1–f5 are also asserted by `verify-q.mjs` against their alternatives, with per-step values and command reports. That script uses the X-based variants the questions were asked against. f6, f7, `own` and `lamport` are asserted only by `adopted.mjs`, against the adopted Y variants. Start black.

| | history | outcome |
|---|---|---|
| q13 | A red; B sees it, green; A undoes | A's undo does nothing; green |
| q14 | then A redoes | nothing; green |
| q15 | A undoes (nothing); sync; B undoes green | red |
| q16 | A red ∥ B blue | one deterministic winner; the loser is retained, and either can undo |
| q17 | A red; B sees it, red again; sync; A undoes | black |
| f1 | A red; B sees it, red again; A undoes without seeing B's red | black |
| f2 | A red; A undoes; B, seeing that, red; A redoes; B undoes | A's redo does nothing; black |
| f3 | A red; B green; A undoes (nothing); B undoes; A undoes again | A's first undo was used up, so the second finds no item; red |
| f4 | A red; A red again; A undoes | black |
| f5 | A red; B green; C, seeing green, red; B undoes without seeing C's red; sync; A undoes | A's undo does nothing |
| f6 | A red; B, seeing it, green; B undoes his green; A undoes | A's undo does nothing; red |
| f7 | A red; A undoes; B, seeing that, red; B undoes his red; A redoes | A's redo does nothing; black |
| own | A red; A green; A undoes; A undoes | both work; black |
| lamport | A red; A undoes; A undoes again (nothing, local); A green; B, seeing A's red and first undo, blue | blue: B's blue ties A's green on Lamport time, and writer order picks B |

f1–f5 are Ren's follow-up answers. f6 and f7 are his answer that an undone edit by another user still blocks ("this is the composing, right? I would assume nothing happens"). `own` is the consequence of keeping that rule to other users.

**Variants ruled out.** The model's 64 variants come from five families:
- **P:** every write counts. It fails q17.
- **E:** every write counts, but undo retires later equal-valued "echoes". It reproduces q13–q17 but fails f1.
- **X2:** only a later *different*-valued write blocks. It fails f5.
- **X:** only an *active* later edit blocks. It fails f6 and f7.
- **Y:** the one adopted here.

f2, f3 (by its report) and f4 rule out the other Y stack variants. `adopted.mjs` asserts that exactly the expected Y variants match, so another matching variant fails it. Removing f6 and f7 lets X match, and the script then fails.

**Coverage:**
- **Full search:** all 1,474,110 histories of up to 5 commands, with three independently named writers and two values. It ran over the first 48 variants, before Y was added.
- **Plus:** the 6-command f5 history.
- **Y:** added after Ren's f6/f7 answer and checked on the listed traces only. It has not been re-swept.

Within the swept variants, f1–f5 were the only value-changing differences found. That is evidence, not a completeness proof.

## 5. held: redo clearing

Whether a new own counted write clears the redo stack is the pending sequence undo decision, and it should be decided there. Both register variants (clear or keep) match every answer above. A note for that decision: under these rules a redo never makes a write visible over a newer own write, because the newer write dominates causally. So keeping the redo stack only shows when a later undo exposes the redone write.

**Retention of do-nothing commands.** Under rule 4, another user's blocking edit never stops blocking. So in f3 a retained undo would also do nothing: the colour matches, but the report differs ("nothing" instead of "no item"). Ren's answer was that it is used up, so the contract keeps consume, and `adopted.mjs` asserts the "no item" report. For redo, using up the entry is a proposal (rule 5). The model has no retained-redo variant, so no equivalence is claimed.

## 6. phase 2 obligations (#67)

- the event and state types in Rust: the visible-value function and frozen undo/redo admission
- implementation-linked proofs:
  - **convergence:** replicas admitting the same facts expose the same value
  - **single-writer activity:** no foreign toggles
- the q13–q17, f1–f7 and `own` traces as tests against the implementation, through the consumer boundary
- controls that break each rule and fail at its owner
- the register calls on the supported consumer boundary
- bounded history (#69): the losing writes (q16) and the restore targets (q15) are what retention must keep
