export const revision = '2026-11-01.1';
export const title = 'Nickel / undo decisions';
const q = (id, section, name, events, prompt, labels) => ({ id, section, title:name, events, prompt,
  choices:labels.map((label,i)=>({id:String(i+1),label})).concat([{id:'other',label:'another outcome — explain below'},{id:'unsure',label:'depends / unsure — explain if you can'}]) });
export const questions = [
q('q01','1 · choosing an item','whose last edit?',[
'Start with empty text. Alice inserts “a”. Bo receives it and appends “b”. Alice receives Bo’s edit; both see “ab”.','Alice presses undo.'],
'which edit should Alice’s undo select?', ['Alice’s insertion of “a”','Bo’s more recent insertion of “b”','neither; Bo’s edit blocks Alice’s undo']),
q('q02','1 · choosing an item','one account, two devices',[
'You edit one document on your phone, then edit it again on your laptop. The devices have synced.','You press undo on the phone.'],
'which history should that button use?', ['the phone’s own edit history','your account’s combined history, including the laptop edit','the currently focused editing session only, even if it excludes earlier phone edits']),
q('q03','1 · choosing an item','the top item is invisible',[
'Alice inserts “a”, then makes a separate insertion of “b”. Bo deletes “b”; Alice receives the deletion. The screen shows “a”.','Alice presses undo once. Her newest item is the insertion of the now-hidden “b”.'],
'what should this single press do?', ['consume the “b” item, with no immediate text change','skip invisible “b” and undo “a” too','do nothing and keep “b” at the top']),
q('q04','1 · choosing an item','typing after undo',[
'In a single-user document, you insert “a”, insert “b”, then undo the insertion of “b”. The text is “a”.','You now type “x”, producing “ax”.'],
'what happens to the old redo of “b”?', ['discard it when “x” is committed','keep it as the next redo','keep both branches and let the user choose']),
q('q05','1 · choosing an item','a peer edits while redo waits',[
'Alice inserts “a”, then undoes it. Her redo is waiting.','Bo inserts “B” into the empty document. Alice receives it and sees “B”.'],
'what should happen to Alice’s redo?', ['keep the redo of her “a”','clear redo because a remote edit arrived','keep it but ask for confirmation before applying it']),
q('q06','2 · sequence effects','a peer inside my insertion',[
'Alice inserts “ab” as one item. Bo receives it and inserts “X” between the two characters. Everyone sees “aXb”.','Alice undoes her insertion.'],
'what text should remain?', ['“X”','empty text','“aXb” — the peer edit prevents undoing the surrounding insertion']),
q('q07','2 · sequence effects','two deletions of one character',[
'Start with the same original “b” on both peers. Alice and Bo independently delete it before seeing each other’s deletion. They then sync.','Alice undoes only her deletion. Bo has not undone his.'],
'what should be visible?', ['empty text — Bo’s deletion still applies','“b” — undo restores what Alice deleted']),
q('q08','2 · sequence effects','does dependence imply membership?',[
'Alice inserts “this is hard”. Bo receives it and independently inserts “not ” inside it, giving “this is not hard”.','No derived-edit membership was declared. Alice undoes her original insertion.'],
'what should remain?', ['“not ”','empty text — the later insertion loses its ground','ask whether to keep Bo’s text, with a specified rule for peers that receive the answer late']),
q('q09','2 · sequence effects','a deletion did not see the new character',[
'Both peers see “ab”. Alice deletes both original characters. Concurrently, Bo inserts “X” between them without seeing Alice’s deletion.','They sync.'],
'should Alice’s deletion remove Bo’s unseen X?', ['no; show “X”','yes; show empty text because X lies inside the deleted region']),
q('q10','2 · sequence effects','same spelling, different insertion',[
'Both peers see one original “b”. Alice deletes it. Bo receives that deletion and independently types a new “b”.','Alice receives Bo’s new character, then undoes her deletion of the original.'],
'how many characters should appear?', ['two “b” characters — the original and Bo’s new one','one “b” — equal spelling should be combined','one “b” — the newer insertion should block restoration of the original']),
q('q11','2 · sequence effects','hidden creation under a replacement',[
'Alice inserts “a”. Bo receives it and appends “B”. Alice receives that, then replaces all of “aB” with “x” as a new, separate item.','Bo receives the replacement and undoes his now-hidden insertion of B. Alice receives that undo, then undoes only her replacement item.'],
'what should Alice see?', ['“a” — B’s creation remains undone','“aB” — restore the text before Alice’s replacement','empty text']),
q('q12','2 · sequence effects','concurrent runs in one gap',[
'Both peers start with empty text. Alice inserts “ab” in one operation. Concurrently, Bo inserts “XY” in one operation.','There are no other edits. They sync.'],
'which outputs should the library permit?', ['“abXY” or “XYab”, with a deterministic rule; no interleaving','interleavings such as “aXbY” are acceptable if everyone agrees','the library should expose a conflict instead of choosing an order']),
q('q13','3 · register effects','overwriting someone else’s overwrite',[
'A shared color register starts black. Alice sets red. Bo sees red and sets green. Alice receives green.','Alice presses undo on her own red-setting item.'],
'what color should appear?', ['green — preserve Bo’s later contribution','black — restore the state before Alice’s own write','red — undo the most recent global change','undo should be unavailable here']),
q('q14','3 · register effects','redo after that register undo',[
'Independently of the previous question: black → Alice sets red → Bo sees it and sets green → Alice undoes her own red write.','With no intervening edit, Alice now presses redo.'],
'what should the color be after redo?', ['green — the state immediately before Alice’s undo','red — reapply Alice’s selected write as her choice']),
q('q15','3 · register effects','both authors undo their register writes',[
'Start black. Alice sets red. Bo receives red and sets green. Everyone syncs.','Alice undoes her own write and everyone syncs. Bo then undoes his own green write. There are no other edits.'],
'what should be visible after both undos?', ['black — both original writes are inactive','red — restore the state before Bo’s green write','green']),
q('q16','3 · register effects','two concurrent colors',[
'Alice and Bo both start from black. Without seeing the other’s write, Alice chooses red and Bo chooses blue.','They sync.'],
'what should a register expose?', ['both alternatives, so the caller can resolve them','one deterministic winner, while retaining the other write for future undo','one deterministic winner; the losing value may be forgotten']),
q('q17','3 · register effects','an equal-valued overwrite',[
'Start black. Alice sets red. Bo sees that and independently sets red again. Everyone syncs.','Alice undoes only her own red-setting item.'],
'does Bo’s equal-valued write matter?', ['yes; the register stays red','no; the register returns to black','equal-valued writes should not create separate history items']),
q('q18','4 · invisible actions','must an invisible undo travel?',[
'Alice’s inserted character is currently hidden by a peer’s deletion. Alice undoes that insertion. Her text does not change.','Another peer may later undo the deletion.'],
'what must Alice publish now?', ['an undo/activity event, even though text is unchanged','nothing until the character would become visible','nothing; undo with no visible effect should not be recorded']),
q('q19','4 · invisible actions','a late child and an invisible peer undo',[
'Alice’s item C inserts “a”. Bo inserts “B” after it. Alice adds an explicitly declared child to C: delete B and insert “x”. Everyone sees “ax”.','Bo undoes his hidden insertion of B. Alice receives that undo, then undoes all of C, including its child.'],
'what should remain?', ['empty text','“B” — restoring the child’s deletion reveals it','“x”']),
q('q20','4 · invisible actions','the same undo arrives late',[
'Use the same history: C creates a and its child replaces Bo’s B with x. Bo has undone his hidden B, but that event is delayed.','Alice first undoes C and temporarily sees “B”. She then receives Bo’s earlier undo.'],
'what should happen on receipt?', ['B disappears; the final state becomes empty','B stays because it was restored before the event arrived','report a conflict for the application to resolve']),
q('q21','4 · invisible actions','redoing the invisible item',[
'Again C creates a and its child replaces Bo’s B with x. Bo undoes B; Alice receives that, then undoes C. Everyone now sees empty text.','Bo presses redo on his previously invisible undo.'],
'what should appear?', ['“B”','nothing — the invisible item should not have a redo entry','“ax”']),
q('q22','4 · invisible actions','redoing the parent afterwards',[
'Continue the previous history: C and B were both undone, then Bo redid B, so the text is “B”.','Alice now redoes C, including its previously admitted child.'],
'what should appear?', ['“ax” — C’s child again hides B','“aB” — redo should not repeat the child’s deletion','“aBx” — preserve B and also reinsert x']),
q('q23','4 · invisible actions','a consumed invisible item',[
'Alice inserts a character; Bo deletes it. Alice presses undo on that now-hidden creation.','Assume the operation is recorded and synchronizes.'],
'what should Alice’s next redo be allowed to select?', ['that same item, despite its undo having no visible effect','only an older item whose undo visibly changed text','nothing; this kind of item has no opposite']),
q('q24','5 · groups and derived edits','ordinary typing',[
'In one focused text field with one cursor, you type “a”, then “b” 200 ms later. There is no movement, import or other edit.','You press undo once.'],
'what grouping would you prefer?', ['remove “ab” together','remove only “b”','let the editor choose; the library should only support explicit boundaries']),
q('q25','5 · groups and derived edits','Enter between two edits',[
'You type “a”, press Enter, then type “b”, all within half a second. There is one cursor.','You press undo once.'],
'what should the editor undo?', ['only the final “b”','Enter and “b” together','the whole “a”, Enter, “b” sequence']),
q('q26','5 · groups and derived edits','remote import between typing',[
'You type “a”. A remote edit is imported elsewhere in the same document. You then type “b” at your cursor, within 200 ms.','The two local insertions would otherwise coalesce.'],
'should that import split the local undo group?', ['yes','no','only if the remote edit touches the local editing region']),
q('q27','5 · groups and derived edits','delayed auto-pair close',[
'One writer inserts “(” as item C. It makes a separate primary item inserting “B” after it.','A delayed job explicitly tagged as C’s child inserts “)” after B. The text is “(B)”. The newest primary item is B.'],
'what should one undo remove?', ['only B, leaving “()”','the delayed “)” first, leaving “(B”','all of “(B)” as one group']),
q('q28','5 · groups and derived edits','a child completes while its trigger is undone',[
'You type “(” and start an auto-pair job tagged as its child. Before the job completes, you undo “(”.','The delayed result now wants to add “)”.'],
'what should happen?', ['reject/cancel that child with no document effect','record it as an inactive child, so it appears if the trigger is redone','commit it as a new independent item','reactivate the trigger and attach it']),
q('q29','5 · groups and derived edits','later does not necessarily mean derived',[
'Alice inserts “a”. Later, after other activity, she independently inserts “b”; she declares no child relationship.','She undoes only the first item using a hypothetical explicit item-selection command.'],
'should b disappear because it happened after a?', ['no; keep b','yes; later local edits should be undone with their causal predecessor','only when b was inserted inside a region created by the first item']),
q('q30','6 · identity and anchors','before a hidden character',[
'Create “ab”. Keep a stable gap immediately before a, then delete a. The visible text is “b”.','Insert X at that historical gap, then undo the deletion of a.'],
'what should be visible?', ['“Xab”','“aXb”','the two histories may be indistinguishable once a is hidden']),
q('q31','6 · identity and anchors','after a hidden character',[
'Create “ab”. This time keep a stable gap immediately after a, then delete a. The visible text is “b”.','Insert X at that historical gap, then undo the deletion of a.'],
'what should be visible?', ['“aXb”','“Xab”','the two histories may be indistinguishable once a is hidden']),
q('q32','6 · identity and anchors','typing at a range boundary',[
'A saved annotation covers “word”. Someone inserts X exactly at the annotation’s start boundary.','There is no other edit.'],
'what should the anchor API allow?', ['the caller chooses whether X belongs inside or outside via explicit affinity','always include X','always exclude X','leave it to the library’s insertion-order tie-break']),
q('q33','6 · identity and anchors','cursor positions after a cycle',[
'You edit with two selections and later move both cursors. You undo the edit, then move the cursors again before redo.','The library supplies anchors; an editor adapter chooses selection restoration.'],
'after redo, which selection should the editor prefer?', ['the selection saved when the original edit finished','the selection in effect when undo was invoked','the selection in effect immediately before redo','leave selections where they are, transformed through the change']),
q('q34','6 · identity and anchors','is restored text the same element?',[
'Alice inserts a. Bo saves an anchor attached to that character. Alice undoes and then redoes her insertion.','The character again displays as a.'],
'what should the anchor treat it as?', ['the same logical element as before','a fresh element; the old anchor follows a documented fallback','either representation is fine only if every future anchor/edit observation is equivalent']),
q('q35','7 · recovery and limits','undo after a reload',[
'You edit a document, persist it, close the app and reopen it. No remote edit occurs.'],
'what history behavior should the API support?', ['resume the exact local undo/redo session from an explicit checkpoint','restore document meaning but start a fresh local history','support either as two clearly different loading operations']),
q('q36','7 · recovery and limits','clear the local history',[
'You undo an insertion, leaving it inactive. Then you choose “clear undo history”.','Later a peer undoes a deletion that also hid that insertion.'],
'what should clearing history have changed?', ['only local access to undo/redo; the insertion stays inactive','forgetting the undo allows the insertion to become active again','clearing should be forbidden until every peer acknowledges it']),
q('q37','7 · recovery and limits','when retained history gets too large',[
'A phone reaches the configured history/storage budget. Some hidden identities and activity may still matter to an offline peer.'],
'what is an acceptable first-release response?', ['refuse further growth and offer export/recovery; do not silently change meaning','discard local undo access, but keep all replicated semantic facts until there is room','garbage-collect old facts only after an explicit protocol proves it safe','make a new document and require every device to adopt that reset']),
q('q38','7 · recovery and limits','an error halfway through a batch',[
'One requested item replaces two separate ranges. The first replacement can be applied, but validating the second finds an invalid endpoint.','The operation returns an ordinary error, not a process crash.'],
'what should callers observe?', ['no document, history, ID-allocation or event changes','the first replacement remains committed, with a partial-success receipt','the library may keep the first replacement if the UI can recover']),
q('q39','7 · recovery and limits','a cold peer receives equal text',[
'Two histories display identical text but disagree about whether an invisible creation is active. A later undo can reveal the difference.','A third peer opens a saved document without access to the original writer’s in-memory tables.'],
'what should the snapshot preserve?', ['enough identity/history/activity to reproduce those future differences','only current visible text; history is private to the editing device','text plus application-supplied restoration metadata outside the CRDT']),
{ id:'q40',section:'7 · recovery and limits',title:'what would change your mind?',events:[],prompt:'describe a missing undo/redo scenario, a requirement you would not compromise on, or a case where your answers depend on the application. “nothing to add” is fine.',choices:[],free:true }
];
