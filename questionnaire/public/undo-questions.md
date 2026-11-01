# undo decisions — 2026-11-01.1

The same 40 questions as the web edition, without a browser.

Fill in undo-answers-template.json: set respondent, then each answer.choiceId to the quoted choice ID and answer.note to your explanation. Leave choiceId null when unanswered; q40 uses only note. Do not edit question snapshots. choiceLabel and status are derived metadata: the browser regenerates them on export. Import the completed file into the web quiz to review it or export a normalized copy. Partial answers are welcome.

- Each question is independent. Quoted letters are text; Alice and Bo are writers.
- Each listed edit is its own item unless explicit grouping or child membership is stated.
- Concurrent means neither writer saw the other operation when issuing its own.
- Some questions stipulate an observed intermediate result; that is not an endorsement of your earlier answer.
- There is no answer key, score, adopted Nickel policy or CRDT simulation behind this questionnaire.

## q01: whose last edit?

1 · choosing an item

1. Start with empty text. Alice inserts “a”. Bo receives it and appends “b”. Alice receives Bo’s edit; both see “ab”.
2. Alice presses undo.

which edit should Alice’s undo select?

- `1`: Alice’s insertion of “a”
- `2`: Bo’s more recent insertion of “b”
- `3`: neither; Bo’s edit blocks Alice’s undo
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q02: one account, two devices

1 · choosing an item

1. You edit one document on your phone, then edit it again on your laptop. The devices have synced.
2. You press undo on the phone.

which history should that button use?

- `1`: the phone’s own edit history
- `2`: your account’s combined history, including the laptop edit
- `3`: the currently focused editing session only, even if it excludes earlier phone edits
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q03: the top item is invisible

1 · choosing an item

1. Alice inserts “a”, then makes a separate insertion of “b”. Bo deletes “b”; Alice receives the deletion. The screen shows “a”.
2. Alice presses undo once. Her newest item is the insertion of the now-hidden “b”.

what should this single press do?

- `1`: consume the “b” item, with no immediate text change
- `2`: skip invisible “b” and undo “a” too
- `3`: do nothing and keep “b” at the top
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q04: typing after undo

1 · choosing an item

1. In a single-user document, you insert “a”, insert “b”, then undo the insertion of “b”. The text is “a”.
2. You now type “x”, producing “ax”.

what happens to the old redo of “b”?

- `1`: discard it when “x” is committed
- `2`: keep it as the next redo
- `3`: keep both branches and let the user choose
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q05: a peer edits while redo waits

1 · choosing an item

1. Alice inserts “a”, then undoes it. Her redo is waiting.
2. Bo inserts “B” into the empty document. Alice receives it and sees “B”.

what should happen to Alice’s redo?

- `1`: keep the redo of her “a”
- `2`: clear redo because a remote edit arrived
- `3`: keep it but ask for confirmation before applying it
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q06: a peer inside my insertion

2 · sequence effects

1. Alice inserts “ab” as one item. Bo receives it and inserts “X” between the two characters. Everyone sees “aXb”.
2. Alice undoes her insertion.

what text should remain?

- `1`: “X”
- `2`: empty text
- `3`: “aXb” — the peer edit prevents undoing the surrounding insertion
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q07: two deletions of one character

2 · sequence effects

1. Start with the same original “b” on both peers. Alice and Bo independently delete it before seeing each other’s deletion. They then sync.
2. Alice undoes only her deletion. Bo has not undone his.

what should be visible?

- `1`: empty text — Bo’s deletion still applies
- `2`: “b” — undo restores what Alice deleted
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q08: does dependence imply membership?

2 · sequence effects

1. Alice inserts “this is hard”. Bo receives it and independently inserts “not ” inside it, giving “this is not hard”.
2. No derived-edit membership was declared. Alice undoes her original insertion.

what should remain?

- `1`: “not ”
- `2`: empty text — the later insertion loses its ground
- `3`: ask whether to keep Bo’s text, with a specified rule for peers that receive the answer late
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q09: a deletion did not see the new character

2 · sequence effects

1. Both peers see “ab”. Alice deletes both original characters. Concurrently, Bo inserts “X” between them without seeing Alice’s deletion.
2. They sync.

should Alice’s deletion remove Bo’s unseen X?

- `1`: no; show “X”
- `2`: yes; show empty text because X lies inside the deleted region
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q10: same spelling, different insertion

2 · sequence effects

1. Both peers see one original “b”. Alice deletes it. Bo receives that deletion and independently types a new “b”.
2. Alice receives Bo’s new character, then undoes her deletion of the original.

how many characters should appear?

- `1`: two “b” characters — the original and Bo’s new one
- `2`: one “b” — equal spelling should be combined
- `3`: one “b” — the newer insertion should block restoration of the original
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q11: hidden creation under a replacement

2 · sequence effects

1. Alice inserts “a”. Bo receives it and appends “B”. Alice receives that, then replaces all of “aB” with “x” as a new, separate item.
2. Bo receives the replacement and undoes his now-hidden insertion of B. Alice receives that undo, then undoes only her replacement item.

what should Alice see?

- `1`: “a” — B’s creation remains undone
- `2`: “aB” — restore the text before Alice’s replacement
- `3`: empty text
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q12: concurrent runs in one gap

2 · sequence effects

1. Both peers start with empty text. Alice inserts “ab” in one operation. Concurrently, Bo inserts “XY” in one operation.
2. There are no other edits. They sync.

which outputs should the library permit?

- `1`: “abXY” or “XYab”, with a deterministic rule; no interleaving
- `2`: interleavings such as “aXbY” are acceptable if everyone agrees
- `3`: the library should expose a conflict instead of choosing an order
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q13: overwriting someone else’s overwrite

3 · register effects

1. A shared color register starts black. Alice sets red. Bo sees red and sets green. Alice receives green.
2. Alice presses undo on her own red-setting item.

what color should appear?

- `1`: green — preserve Bo’s later contribution
- `2`: black — restore the state before Alice’s own write
- `3`: red — undo the most recent global change
- `4`: undo should be unavailable here
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q14: redo after that register undo

3 · register effects

1. Independently of the previous question: black → Alice sets red → Bo sees it and sets green → Alice undoes her own red write.
2. With no intervening edit, Alice now presses redo.

what should the color be after redo?

- `1`: green — the state immediately before Alice’s undo
- `2`: red — reapply Alice’s selected write as her choice
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q15: both authors undo their register writes

3 · register effects

1. Start black. Alice sets red. Bo receives red and sets green. Everyone syncs.
2. Alice undoes her own write and everyone syncs. Bo then undoes his own green write. There are no other edits.

what should be visible after both undos?

- `1`: black — both original writes are inactive
- `2`: red — restore the state before Bo’s green write
- `3`: green
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q16: two concurrent colors

3 · register effects

1. Alice and Bo both start from black. Without seeing the other’s write, Alice chooses red and Bo chooses blue.
2. They sync.

what should a register expose?

- `1`: both alternatives, so the caller can resolve them
- `2`: one deterministic winner, while retaining the other write for future undo
- `3`: one deterministic winner; the losing value may be forgotten
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q17: an equal-valued overwrite

3 · register effects

1. Start black. Alice sets red. Bo sees that and independently sets red again. Everyone syncs.
2. Alice undoes only her own red-setting item.

does Bo’s equal-valued write matter?

- `1`: yes; the register stays red
- `2`: no; the register returns to black
- `3`: equal-valued writes should not create separate history items
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q18: must an invisible undo travel?

4 · invisible actions

1. Alice’s inserted character is currently hidden by a peer’s deletion. Alice undoes that insertion. Her text does not change.
2. Another peer may later undo the deletion.

what must Alice publish now?

- `1`: an undo/activity event, even though text is unchanged
- `2`: nothing until the character would become visible
- `3`: nothing; undo with no visible effect should not be recorded
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q19: a late child and an invisible peer undo

4 · invisible actions

1. Alice’s item C inserts “a”. Bo inserts “B” after it. Alice adds an explicitly declared child to C: delete B and insert “x”. Everyone sees “ax”.
2. Bo undoes his hidden insertion of B. Alice receives that undo, then undoes all of C, including its child.

what should remain?

- `1`: empty text
- `2`: “B” — restoring the child’s deletion reveals it
- `3`: “x”
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q20: the same undo arrives late

4 · invisible actions

1. Use the same history: C creates a and its child replaces Bo’s B with x. Bo has undone his hidden B, but that event is delayed.
2. Alice first undoes C and temporarily sees “B”. She then receives Bo’s earlier undo.

what should happen on receipt?

- `1`: B disappears; the final state becomes empty
- `2`: B stays because it was restored before the event arrived
- `3`: report a conflict for the application to resolve
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q21: redoing the invisible item

4 · invisible actions

1. Again C creates a and its child replaces Bo’s B with x. Bo undoes B; Alice receives that, then undoes C. Everyone now sees empty text.
2. Bo presses redo on his previously invisible undo.

what should appear?

- `1`: “B”
- `2`: nothing — the invisible item should not have a redo entry
- `3`: “ax”
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q22: redoing the parent afterwards

4 · invisible actions

1. Continue the previous history: C and B were both undone, then Bo redid B, so the text is “B”.
2. Alice now redoes C, including its previously admitted child.

what should appear?

- `1`: “ax” — C’s child again hides B
- `2`: “aB” — redo should not repeat the child’s deletion
- `3`: “aBx” — preserve B and also reinsert x
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q23: a consumed invisible item

4 · invisible actions

1. Alice inserts a character; Bo deletes it. Alice presses undo on that now-hidden creation.
2. Assume the operation is recorded and synchronizes.

what should Alice’s next redo be allowed to select?

- `1`: that same item, despite its undo having no visible effect
- `2`: only an older item whose undo visibly changed text
- `3`: nothing; this kind of item has no opposite
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q24: ordinary typing

5 · groups and derived edits

1. In one focused text field with one cursor, you type “a”, then “b” 200 ms later. There is no movement, import or other edit.
2. You press undo once.

what grouping would you prefer?

- `1`: remove “ab” together
- `2`: remove only “b”
- `3`: let the editor choose; the library should only support explicit boundaries
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q25: Enter between two edits

5 · groups and derived edits

1. You type “a”, press Enter, then type “b”, all within half a second. There is one cursor.
2. You press undo once.

what should the editor undo?

- `1`: only the final “b”
- `2`: Enter and “b” together
- `3`: the whole “a”, Enter, “b” sequence
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q26: remote import between typing

5 · groups and derived edits

1. You type “a”. A remote edit is imported elsewhere in the same document. You then type “b” at your cursor, within 200 ms.
2. The two local insertions would otherwise coalesce.

should that import split the local undo group?

- `1`: yes
- `2`: no
- `3`: only if the remote edit touches the local editing region
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q27: delayed auto-pair close

5 · groups and derived edits

1. One writer inserts “(” as item C. It makes a separate primary item inserting “B” after it.
2. A delayed job explicitly tagged as C’s child inserts “)” after B. The text is “(B)”. The newest primary item is B.

what should one undo remove?

- `1`: only B, leaving “()”
- `2`: the delayed “)” first, leaving “(B”
- `3`: all of “(B)” as one group
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q28: a child completes while its trigger is undone

5 · groups and derived edits

1. You type “(” and start an auto-pair job tagged as its child. Before the job completes, you undo “(”.
2. The delayed result now wants to add “)”.

what should happen?

- `1`: reject/cancel that child with no document effect
- `2`: record it as an inactive child, so it appears if the trigger is redone
- `3`: commit it as a new independent item
- `4`: reactivate the trigger and attach it
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q29: later does not necessarily mean derived

5 · groups and derived edits

1. Alice inserts “a”. Later, after other activity, she independently inserts “b”; she declares no child relationship.
2. She undoes only the first item using a hypothetical explicit item-selection command.

should b disappear because it happened after a?

- `1`: no; keep b
- `2`: yes; later local edits should be undone with their causal predecessor
- `3`: only when b was inserted inside a region created by the first item
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q30: before a hidden character

6 · identity and anchors

1. Create “ab”. Keep a stable gap immediately before a, then delete a. The visible text is “b”.
2. Insert X at that historical gap, then undo the deletion of a.

what should be visible?

- `1`: “Xab”
- `2`: “aXb”
- `3`: the two histories may be indistinguishable once a is hidden
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q31: after a hidden character

6 · identity and anchors

1. Create “ab”. This time keep a stable gap immediately after a, then delete a. The visible text is “b”.
2. Insert X at that historical gap, then undo the deletion of a.

what should be visible?

- `1`: “aXb”
- `2`: “Xab”
- `3`: the two histories may be indistinguishable once a is hidden
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q32: typing at a range boundary

6 · identity and anchors

1. A saved annotation covers “word”. Someone inserts X exactly at the annotation’s start boundary.
2. There is no other edit.

what should the anchor API allow?

- `1`: the caller chooses whether X belongs inside or outside via explicit affinity
- `2`: always include X
- `3`: always exclude X
- `4`: leave it to the library’s insertion-order tie-break
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q33: cursor positions after a cycle

6 · identity and anchors

1. You edit with two selections and later move both cursors. You undo the edit, then move the cursors again before redo.
2. The library supplies anchors; an editor adapter chooses selection restoration.

after redo, which selection should the editor prefer?

- `1`: the selection saved when the original edit finished
- `2`: the selection in effect when undo was invoked
- `3`: the selection in effect immediately before redo
- `4`: leave selections where they are, transformed through the change
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q34: is restored text the same element?

6 · identity and anchors

1. Alice inserts a. Bo saves an anchor attached to that character. Alice undoes and then redoes her insertion.
2. The character again displays as a.

what should the anchor treat it as?

- `1`: the same logical element as before
- `2`: a fresh element; the old anchor follows a documented fallback
- `3`: either representation is fine only if every future anchor/edit observation is equivalent
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q35: undo after a reload

7 · recovery and limits

1. You edit a document, persist it, close the app and reopen it. No remote edit occurs.

what history behavior should the API support?

- `1`: resume the exact local undo/redo session from an explicit checkpoint
- `2`: restore document meaning but start a fresh local history
- `3`: support either as two clearly different loading operations
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q36: clear the local history

7 · recovery and limits

1. You undo an insertion, leaving it inactive. Then you choose “clear undo history”.
2. Later a peer undoes a deletion that also hid that insertion.

what should clearing history have changed?

- `1`: only local access to undo/redo; the insertion stays inactive
- `2`: forgetting the undo allows the insertion to become active again
- `3`: clearing should be forbidden until every peer acknowledges it
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q37: when retained history gets too large

7 · recovery and limits

1. A phone reaches the configured history/storage budget. Some hidden identities and activity may still matter to an offline peer.

what is an acceptable first-release response?

- `1`: refuse further growth and offer export/recovery; do not silently change meaning
- `2`: discard local undo access, but keep all replicated semantic facts until there is room
- `3`: garbage-collect old facts only after an explicit protocol proves it safe
- `4`: make a new document and require every device to adopt that reset
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q38: an error halfway through a batch

7 · recovery and limits

1. One requested item replaces two separate ranges. The first replacement can be applied, but validating the second finds an invalid endpoint.
2. The operation returns an ordinary error, not a process crash.

what should callers observe?

- `1`: no document, history, ID-allocation or event changes
- `2`: the first replacement remains committed, with a partial-success receipt
- `3`: the library may keep the first replacement if the UI can recover
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q39: a cold peer receives equal text

7 · recovery and limits

1. Two histories display identical text but disagree about whether an invisible creation is active. A later undo can reveal the difference.
2. A third peer opens a saved document without access to the original writer’s in-memory tables.

what should the snapshot preserve?

- `1`: enough identity/history/activity to reproduce those future differences
- `2`: only current visible text; history is private to the editing device
- `3`: text plus application-supplied restoration metadata outside the CRDT
- `other`: another outcome — explain below
- `unsure`: depends / unsure — explain if you can

## q40: what would change your mind?

7 · recovery and limits


describe a missing undo/redo scenario, a requirement you would not compromise on, or a case where your answers depend on the application. “nothing to add” is fine.


