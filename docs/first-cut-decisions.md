# four choices before the first Rust cut

**Decision record and remaining proposals for Ren.** Items 1–2 are approved; items
3–4 remain pending. These close the history/effect/identity choices in the
[roadmap](../ROADMAP.md). They do not choose a text-ordering
algorithm, approve the cut's budgets or authorize engine implementation.

The examples below concern which occurrences are visible and which action is
selected. They do not promise where newly visible text is placed. Own-action
Undo and explicit foreign Restore remain the approved split.

## 1. keep access to an action Undo skipped

Alice writes **b**. Bo writes **z**, then deletes Alice's b. Alice explicitly
Restores b. Bo presses Undo: his deletion currently has no remaining effect,
so Undo skips it and removes his older z. Alice then undoes her Restore; b
disappears again.

**Recommendation: retain.** Bo's next Undo may now select his own deletion,
bringing b back. Skipping an action should not permanently discard access to
it. The superseded default consumed that skipped item, leaving Bo no ordinary
Undo for it. The running default now retains it; explicit consume remains
historical comparison evidence.

Cost: an old skipped action can become eligible after a remote change. This
does not make Undo independent of delivery timing. It also does not authorize
skipping a blocked Redo or selecting another writer's action.

If Bo redoes z before revisiting the deletion, his next Undo removes z first.
Retaining the deletion does not put it above a just-redone action. Explicitly
clearing private history still removes local access without erasing shared facts.

**Decision: retain, approved by Ren in Discord.** Skipped actions stay available;
the running experiment and continuation assertions now select retain by
default. Saved sessions preserve their recorded policy; no old private history
is reconstructed or migrated. This does not authorize selective Redo.

## 2. Undo only the concurrent deletions the author had received

Alice and Bo independently delete the same b. Alice then undoes her deletion.

- If she received Bo's deletion before pressing, her Undo records both deletion
  atoms and b returns.
- If she had not received it, her Undo records only her own deletion atom.
  A later arrival of Bo's deletion hides b.

**Recommendation: frozen observed masks for this cut.** These are the candidate's
existing outcomes. Replicas receiving the same authored facts agree; changing
Alice's knowledge before her press can change the action she authors. The latter
is not a delivery-order convergence failure for one fixed event set.

A later deletion made after seeing the restoration remains effective. Redo of
an explicit Restore uses its original masks in a fresh token; it does not grow
them to include deletions received since inspection.

**Response received:** Ren said “I think yes, but have rotbot confirm” in
Discord message 1567021321953742910. Rotbot's confirmation in
message 1567022067889475617 reproduced the observed-before, unseen-after and
later-causal deletion cases.

**Decision: frozen observed masks approved for the first cut.** Ren ratified
these outcomes in Discord message 1567303368131608637. An unseen concurrent
deletion can hide the text when it later arrives; a later causal deletion stays
effective. Neither Undo nor Restore reaches forward to cancel unseen deletion
atoms. This approves these effect outcomes, not a general placement rule or
engine implementation.

## 3. keep/clear is explicit; keeping redo is a stack, not a branch browser

Alice types b, undoes it, then types x. Her q04 note preferred correcting a
malformed result over losing access to old work, but did not choose a rule.

**Recommendation: keep the caller's explicit keep/clear choice.** Without that
choice, effective new work with pending redo rejects unchanged. No silent
default is added to the library.

- With **keep**, the redo of b remains. Alice may redo b while x remains visible.
  This statement promises both identities, not an `abx` placement rule.
- If she first undoes x, redo offers x first, then b. Redoing the newest undone
  item does not discard the older pending one.
- With **clear**, the old redo of b is discarded. Undoing x later does not
  recover that discarded redo. This clears redo access, not b's shared facts.

Explicit Restore is new work too and needs the same choice when redo is pending.
A blocked top Redo stays blocked; keep does not give access to an older entry
under it. Choosing arbitrary older entries or a branch needs another contract.

**Decision:** accept these continuation outcomes with explicit keep/clear, or
restrict the first cut to one of them? Keeping both is not a UI requirement.

## 4. a returning occurrence keeps its ID

Alice inserts a. A caller remembers that occurrence's ID. Alice undoes the
insertion and redoes it. The caller later deletes using the remembered ID.

**Recommendation: the same public ID denotes the returning a.** The caller's
delete addresses it; another occurrence merely spelled a is not substituted.
Likewise, Restore reveals the selected original occurrences rather than making
fresh copies. The experiment already reuses these IDs.

This selects the exact-ID contract proposed for the cut. It does not require
the same memory address or internal representation, and does not promise a
working anchor API: the first cut excludes general anchor resolution. A future
anchor contract still has to specify hidden targets and fallback behavior.

**Decision:** accept stable public IDs across these returns, or require a fresh-ID
or observational-equivalence contract instead? The latter needs its own precise
future-observation rule before implementation.

## what approval would change

An answer can be as short as “retain; observed masks; explicit keep/clear;
same IDs,” with any exception named. No new questionnaire is needed.

After approval, Lynn must revise the profile and affected policy assertions
openly, preserve the superseded failures, and reconcile the API. Existing
[session behavior](private-session-profile.md) and
[mask argument](hybrid-continuation.md) are the comparison, not an independent
oracle for what people should want. Passing finite continuations does not
establish a general local-undo algorithm or ordering construction.
