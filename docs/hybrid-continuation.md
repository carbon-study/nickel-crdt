# a candidate for overlapping deletions and hybrid continuation

This follows the merged [response-led plan](response-plan.md). It proposes one visibility rule matching Ren's q07 and the requested restoration of a replacement's deletion portion. It also exposes a session-continuation decision the earlier examples did not settle. **This is a candidate, not the complete reference contract or an implemented undo API.**

## 1. distinguish concurrent removals from a later deletion

Let D name one deletion effect and T its exact original element targets. A restoration of D could suppress D **and the observed concurrent deletions of those same identities**, while leaving causally later deletions effective. The author selects a deletion and records the exact `(deletion, element)` pairs to suppress. These fixtures need no additional selected-target-ID field in the replicated event. A private checkpoint may retain which local item was selected if that is a promised history/UI observation. Receivers apply that fixed action; they do not select again from their own current view.

This is a proposed extension to the supplied model. Restoring only D fails q07: Bo's independent deletion keeps b hidden. Restoring every known deletion indiscriminately is too broad: it can erase a newer, deliberate deletion when undoing an older replacement. The observed-concurrent rule distinguishes those two cases. Whether the same rule is desirable for all selective undo remains open.

Ren permits either redo outcome after concurrent restoration. This candidate uses **personal cancellation**: redo cancels only the caller's restoration token. Undoing again creates a new token. This is a concrete hypothesis for review, not another request for the same preference.

## 2. two independent deletions: both sessions

`I` creates b; `DA` and `DB` independently delete that same b. Both peers receive both deletions before the restoration. Each session has its own local items. Let Alice's local list be `[DA,I]` and Bo's be `[DB]`, newest first. A list here names retained items, not a proposed shared stack encoding.

| step | selected action / new shared fact | visible IDs | Alice continuation | Bo continuation |
| --- | --- | --- | --- | --- |
| both deletes received | none | empty | can select DA | can select DB |
| Alice undo | RA suppresses `(DA,b)` and `(DB,b)` | b | redo can cancel RA; I remains her older own item | DB has no remaining removal effect; skip it on the next selection |
| Bo had independently selected DB before receiving RA | RB records the same two atoms from Bo's own observed basis | b | redo RA remains available | redo RB becomes available |
| both restores received, Alice redo | XA cancels RA only | b | fresh undo/restoration action must be specified by the session rule | RB still justifies restoration; Bo can redo RB |
| Bo redo | XB cancels RB | empty | both original deletions are effective again | both original deletions are effective again |
| a new selected restoration of DA | a fresh RA2 suppresses both original atoms | b | new token has its own opposite | peer import does not create a private redo item |

The visibility rows are executed by the directed model. The session columns identify required bookkeeping and the remaining open selection rule; they are **not** claims that the model generates these session actions. In particular, whether a skipped deletion becomes selectable again after another writer's redo is not determined just by the atom calculation.

### an important knowledge boundary

If Alice issues RA before receiving DB, its mask contains only `(DA,b)`. Receiving the previously unseen DB subsequently hides b. All delivery schedules still agree because RA's mask is immutable. The candidate therefore satisfies q07 under its stated “then sync, then undo” premise, but makes a distinct, unapproved choice for the unseen-concurrent case. Do not expand q07 into a rule about unseen deletion effects without checking that new premise.

## 3. replacement restoration and a durable author undo

Use the q11 prefix: A creates a, Bo creates B, then A replaces aB with x as a new item C. C atomically consists of creation x and deletion of a/B. The proposed victim action addresses **C's deletion effect**, not all of C.

| step | action | visible IDs | local-history consequence to specify |
| --- | --- | --- | --- |
| after replacement C | C removes a/B and creates x | x | C is A's latest own item; B is hidden |
| Bo restores C's deletion | RV suppresses C's a/B removal atoms | a, B, x | B's creation has not been undone; Bo has a redo for RV |
| A undoes whole C | UC independently suppresses C's deletion atoms; UX withdraws C's x creation | a, B | this is one requested atomic item, represented by a restoration plus a distinct creator-withdrawal token only in this experiment |
| Bo redoes his restoration | cancel RV | a, B | UC must still preserve A's completed undo; it cannot depend solely on Bo's RV |

The independent UC matters even though C's deletion was already visibly reversed. If A's undo merely withdraws x and emits no own cancellation of C's deletion, Bo's later redo can make a/B disappear again. The directed fixture pins the durable cancellation in this limited event interpretation. This is another reason to distinguish a whole-command action from an externally restored subset of its effects.

Now let Bo delete B again **after seeing RV**. A later undo of C should not cancel that causally newer deletion under this candidate. The resulting visible set is `{a}`, with x withdrawn and B still hidden. The negative control that cancels all known removal atoms incorrectly restores B here.

These are identity sets, not proofs of aBx/aB ordering. The candidate restores the full deletion effect T, potentially including another creator's text. The supplied model's mixed-author example instead restored only the victim's part; that was a hypothesis, not a settled answer. General per-hunk/subset selection and authority remain to specify.

### review counterexample: undo of a creation is not an ordinary deletion

Alice replaces p with x. Bo deletes x while Alice independently undoes her replacement. Everyone syncs and sees p. Bo then undoes his deletion. The original candidate restored **both p and x** in all three schedules because it represented Alice's withdrawal of x as an ordinary concurrent deletion. The review's required outcome is p alone.

The repaired candidate records Alice's creator withdrawal separately from ordinary removal atoms. Bo's restoration can cancel ordinary deletions of x, but cannot reactivate its withdrawn creation. If Alice later redoes her replacement, her creator-withdrawal token is cancelled; with Bo's deletion still restored, x becomes visible and p is hidden again. Bo can then redo his deletion and hide x. All three continuations are directed fixtures. Authorization for creation withdrawal and atomic publication of the compound undo remain outside this model.

### review scope control

Alice deletes a,b; Bo concurrently deletes b,c; both sync. Alice restores her selected deletion's target set a,b. The required visible IDs are a,b, with c still hidden by Bo's deletion. A version that omits the target-set restriction also suppresses the removal of c; the new fixture rejects it. Shared overlap at b does not authorize restoring unrelated identities.

## 4. fixed-action delivery argument and its limits

For a finite compatible event set S with unique IDs, all causal schedules deliver the same event dictionary. Active restoration tokens are S's restoration events minus tokens named by cancellation events in S. Suppressed removal atoms are the union of those active tokens' frozen masks. Active creator-withdrawal tokens are likewise withdrawal events minus cancelled tokens. Visible IDs are all created IDs minus IDs with either an unsuppressed ordinary removal atom or an active creator withdrawal. Each expression depends only on S, so this **set projection** is schedule independent. This is a written observation about the supplied representation, not a mechanized theorem or a proof that all authored histories are valid.

The [nested reference experiment](../experiments/hybrid-restoration/README.md) replays twelve directed fixtures with duplicate delivery and prefix recovery, including four semantic negative controls. It implements neither text order nor session selection, grouping, resource admission, binding or durable storage. The original supplied model and its failing-to-match-q07 policy are retained separately. None of V1–V9 is discharged.

## 5. concrete remaining session edge

Take Bo's private item list `[D,Z]`: D deletes Alice's b, and Z is Bo's older insertion z. Alice restores D; Bo learns this and presses undo, skipping the ineffective D and undoing Z. Alice then redoes her restoration, making D effective again.

Two continuations satisfy the earlier examples:

- skipping D consumed its local position permanently; Bo's next undo is empty;
- skipping D only bypassed an externally reversed effect; when D becomes effective again, Bo can select D on a subsequent undo.

They require different local session state and checkpoint continuation. Neither a frozen restoration mask nor the current questionnaire decides between them. A proposed session specification must choose and replay this case, rather than treating “adjust the stack” as an algorithm. If choosing the simpler policy under Ren's implementation latitude, name the resulting user-visible behavior explicitly.

The next gate remains a complete selection/effect/replication/continuation contract, including this case, new primary work/redo, compound items, register no-ops and historical text ordering. This artifact narrows the gap by giving q07 a concrete candidate law and pinning later-deletion/whole-replacement continuations; it does not relabel the gap closed.
