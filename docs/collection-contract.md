# keyed collection contract (#68, phase 1)

**Status: proposed contract for review. Nothing is implemented.** It fixes the collection behaviour that #68's phase 2 will implement and prove.
- **Answered by Ren (2026-11-08):** the two outcomes in §4: an unseen change survives a removal, and an undo of your creation does nothing after another user edited it.
- **Proposed design (§1–§3):** the put/insert shape, unified removal semantics, the restore field policy, and the key representation.
- **Built on:** [the register contract](register-contract.md) for field edits.

Executable evidence: [experiments/collection-candidates](../experiments/collection-candidates/README.md).

## 1. shape (proposed)

- **Caller keys:** `put(key, v)` and `remove(key)`. Used for reading position per (book, device), settings, and installed plugins.
  - A `put` **creates** the entry if it is absent in the author's view.
  - Otherwise it is a **register write** to the entry's field.
  - An equal-valued put on a present entry is no edit (register rule 1).
- **Fresh records:** `insert(v) → key`. Used for highlights, bookmarks and notes. Edits to the record are puts to that key.
  - The API does not allow create-by-put on insert-kind keys, so a fresh record comes back only through restore.
  - Building the key from the creating event's `(writer, counter)` is a representation proposal while public IDs stay held. Writer fencing is unchanged.
- **Fields:** entry fields are registers (#67). Conformance is scoped to counted writes and undo blocking; redo is not modelled here.

## 2. rules (proposed; one of them answered)

1. **Removal sees only what it saw.** A remove deletes exactly the puts in its causal past. Any **counted** put it did not see keeps the entry, whether it creates the entry or writes a field (answered, K1). An unseen equal-valued put is no edit (§1) and does **not** keep a removed entry (proposed, by analogy with Ren's register f1, where a concurrent same-value tap didn't count; `equalUnseen` trace).
   - One rule covers both fresh records and caller keys. That coupling is proposed design, from the unified put.
   - Sequence analogy: q09, where a deletion doesn't remove a character it didn't see.
2. **Undo of your own put or remove** follows the register undo rule. It does nothing if another user's later counted command on the entry exists, even if since undone. The author's own later commands block only while active.
   - This includes the undo of your **creating** put (answered, K2). Alice can still remove the entry explicitly. That is an ordinary remove, and others can restore it.
3. **Restore** brings an entry back after removals by **other** users.
   - It masks every removal effect by another user in the restorer's view, including observed-concurrent removals.
   - It is an action in the restorer's own history, so the restorer can undo it. It doesn't alter the remover's stack.
   - Basis: q40 and the [sequence profile](private-session-profile.md).
4. **Restore discards no field write (proposed).** After a restore, the field is the register over every counted put. That includes a write made concurrently with a removal.
   - Immutable sequence content doesn't settle mutable fields.
   - The alternative, restoring the fields as of the removal, is not modelled.

Every rule depends only on the merged causal history and on decisions frozen at creation.

## 3. outcomes the rules must reproduce

All of these, plus a `lamport` trace (Lamport time counts replicated facts only, as in the register contract), are asserted by `adopted.mjs`. The answered stories are also asserted under every option by `verify-k.mjs`.

| | history | outcome |
|---|---|---|
| restore | A puts red; B removes; A restores | red |
| restoreUndo | then A undoes her restore | absent |
| restore3 | A puts red; B and C remove concurrently; A, seeing both, restores | red |
| restoreHidden | A puts red; B removes; C, seeing only the put, writes green; A restores | green |
| q13 | A puts red, then blue; B writes green; A undoes | A's undo does nothing; green |
| equalPut | A puts red; B puts red again; A undoes | absent: B's equal put is no edit |
| K1 | A red → A green; B, having seen only red, removes | green |
| K1′ | A puts; B removes; A, unaware, puts again | the entry stays (A's new value) |
| equalUnseen | A puts red; B removes; C, having seen only A's put, puts red | absent: C's equal put is no edit (proposed) |
| K2 | A adds red; B writes green; A undoes | A's undo does nothing; green |
| K2+ | then B undoes his write | red |

## 4. Ren's answers (2026-11-08)

Ren: "both your guesses seem right to me".
- **K1:** the highlight is back, green. Bo never saw Alice's change. The same applies to caller keys.
- **K2:** green now, then red when Bo undoes. Alice's undo did nothing, because Bo edited after her.

**Variants ruled out.** The model has 6 variants:
- `removeMode`: `observed` or `removeWins`
- `undoCreate`: `blocked`, `allowed` or `removes`

K1 rules out `removeWins`, and K2/K2+ rule out `allowed` and `removes`. `adopted.mjs` asserts that exactly `observed/blocked` matches. Removing both K1 and K1′ lets `removeWins/blocked` match too, and the script then fails. Removing either one alone doesn't, because the other still excludes it.

## 5. phase 2 obligations (#68)

- **Rust:** the entry, removal and restore facts, presence and field functions, and frozen undo/restore admission.
- **Implementation-linked proofs:**
  - convergence
  - observed removal
  - restore masking
  - single-writer activity
- **Tests and controls:** the §3 traces as tests through the consumer boundary, plus controls that break each rule.
- **Bounded history (#69):** removed entries and their field writes are what restore needs retained.
