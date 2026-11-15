// A bounded checkpoint gate, not full register validity/refinement or SEC.
// Exact tracked views + fresh actual source extraction + named ordinary controls.
import fs from 'node:fs/promises';
import path from 'node:path';
import assert from 'node:assert/strict';
import {fileURLToPath} from 'node:url';
import {verify,holdLock,runAsync,digest,put} from './proof-cache.mjs';
import {scopedAnchor,codeMask} from './mutation-scope.mjs';
import {hasOrdinaryTheoremRejection} from './negative-proof-evidence.mjs';
import {assertReformedSource} from './proof-reform.mjs';
const root=fileURLToPath(new URL('..',import.meta.url));
const output=path.resolve(process.argv[2]??path.join(root,'.cache/register-proofs'));
const selected=process.argv.slice(3);
await fs.mkdir(output,{recursive:true});
assert(holdLock(path.join(output,'register-proofs.lock')),'register proof output is owned by another invocation');
const env=process.env;
for(const k of ['NICKEL_HAX_BIN','NICKEL_PROOF_FSTAR','NICKEL_HAX_SOURCE','NICKEL_FSTAR_MODEL_CACHE'])assert(env[k],k);
const views=path.join(root,'proofs/register-view');
const receipt=JSON.parse(await fs.readFile(path.join(views,'receipt.json'),'utf8'));
const required=['Cargo.toml','Cargo.lock','src/lib.rs','src/register.rs','src/causal.rs','src/event_layer.rs','src/event_shell.rs','proofs/Register.lt','proofs/RegisterPast.lt','proofs/RegisterHistory.lt','proofs/RegisterValid.lt','proofs/RegisterPublic.lt','proofs/Canonical.lt','proofs/Vector.lt','proofs/EventGraph.lt','proofs/EventClassifier.lt',
 'proofs/Prelude.lt','proofs/LoopUtil.lt','proofs/EventShell.lt','proofs/CausalEnvelope.lt',
 'proofs/generated/Nickel.Vector.fst','proofs/generated/Nickel.EventGraph.fst','proofs/generated/Nickel.EventClassifier.fst','proofs/generated/Nickel.Prelude.fst','proofs/generated/Nickel.LoopUtil.fst','proofs/generated/Nickel.EventShell.fst',
 'proofs/causal-envelope-view/Nickel.CausalEnvelope.fst',
 'proofs/register-view/Nickel.Canonical.fst','proofs/register-view/Nickel.RegisterPast.fst','proofs/register-view/Nickel.RegisterHistory.fst','proofs/register-view/Nickel.RegisterValid.fst','proofs/register-view/Nickel.RegisterPublic.fst',
 ...['Register','Nickel_crdt.Register','Nickel_crdt.Causal','Nickel_crdt.Event_layer','Nickel_crdt.Event_shell'].map(n=>'proofs/register-view/'+(n==='Register'?'Nickel.Register':n)+'.fst')];
assert.equal(receipt.schemaVersion,1);assert.deepEqual(Object.keys(receipt.files).sort(),required.sort(),'complete checkpoint receipt required');
for(const [f,h]of Object.entries(receipt.files))assert.equal(digest(await fs.readFile(path.join(root,f))),h,'stale checkpoint receipt: '+f);
assertReformedSource('LoopUtil',await fs.readFile(path.join(root,'proofs/LoopUtil.lt'),'utf8'));
assertReformedSource('Canonical',await fs.readFile(path.join(root,'proofs/Canonical.lt'),'utf8'));
assertReformedSource('Register',await fs.readFile(path.join(root,'proofs/Register.lt'),'utf8'));
assertReformedSource('RegisterPast',await fs.readFile(path.join(root,'proofs/RegisterPast.lt'),'utf8'));
assert.throws(()=>assertReformedSource('RegisterPast','Tactics.prune("Nickel_crdt.Event_layer");'),'no broad shared namespace exception for exact past');
assert.throws(()=>assertReformedSource('RegisterPast','Tactics.prune("Nickel_crdt.Register.v_OPS");'),'exact past stays generic over ops');
assertReformedSource('RegisterHistory',await fs.readFile(path.join(root,'proofs/RegisterHistory.lt'),'utf8'));
assertReformedSource('RegisterValid',await fs.readFile(path.join(root,'proofs/RegisterValid.lt'),'utf8'));
assertReformedSource('RegisterPublic',await fs.readFile(path.join(root,'proofs/RegisterPublic.lt'),'utf8'));
assert.throws(()=>assertReformedSource('RegisterHistory','Tactics.prune("Nickel_crdt.Register");'),'no broad native namespace exception for history meaning');
assert.throws(()=>assertReformedSource('RegisterHistory','Tactics.prune("Nickel.RegisterPast.ancestor");'),'history meaning keeps exact-past ancestry visible');
assert.throws(()=>assertReformedSource('EditAccepted','Tactics.prune("Nickel_crdt.Register.bytes_equal");'),'new native visibility stays Register-scoped');
assert.throws(()=>assertReformedSource('EventGraph','Tactics.prune("Nickel.Register.planned_preserves_private");'),'write caller contract isolation stays Register-scoped');
assert.throws(()=>assertReformedSource('EventGraph','Tactics.prune("Nickel_crdt.Register.read_history");'),'payload callee visibility stays Register-scoped');
assert.throws(()=>assertReformedSource('EventGraph','Tactics.prune("Nickel.Register.planned_checks_payload");'),'clock payload alternate stays Register-scoped');
assert.throws(()=>assertReformedSource('EventGraph','Tactics.prune("Nickel.Register.planned_adds_exact_fact");'),'counted-write ordering isolation stays Register-scoped');
assert.throws(()=>assertReformedSource('Register','Tactics.norm([]);'),'no normalization exception');
assert.throws(()=>assertReformedSource('EventGraph','Tactics.prune("Nickel.Register.fact_ids_unique");'),'unique-outcome predicate opacity stays Register-scoped');
assert.throws(()=>assertReformedSource('Register','Tactics.prune("Nickel_crdt.Register");'),'no broad native namespace exception');
assert.throws(()=>assertReformedSource('EventGraph','Tactics.prune("Alloc.Vec.impl__new");'),'new vector visibility stays Canonical-scoped');
assert.throws(()=>assertReformedSource('Canonical','Tactics.prune("Nickel_crdt.Register");'),'no broad client visibility');
assert.throws(()=>assertReformedSource('EventGraph','Tactics.prune("Nickel.Canonical.push_is_exact");'),'lower append-contract visibility stays Canonical-scoped');
assert.throws(()=>assertReformedSource('Register','Tactics.prune("Nickel_crdt.Event_layer");'),'no broad shared namespace exception');
const loopView=await fs.readFile(path.join(root,'proofs/generated/Nickel.LoopUtil.fst'),'utf8');
const canonicalView=await fs.readFile(path.join(views,'Nickel.Canonical.fst'),'utf8');
const view=await fs.readFile(path.join(views,'Nickel.Register.fst'),'utf8');
const pastView=await fs.readFile(path.join(views,'Nickel.RegisterPast.fst'),'utf8');
const historyView=await fs.readFile(path.join(views,'Nickel.RegisterHistory.fst'),'utf8');
const validView=await fs.readFile(path.join(views,'Nickel.RegisterValid.fst'),'utf8');
const publicView=await fs.readFile(path.join(views,'Nickel.RegisterPublic.fst'),'utf8');
for(const checkedView of [view,canonicalView,pastView,historyView,validView,publicView])assert(!/\b(?:admit|assume|lax|admit_smt_queries)\b/.test(checkedView));
if(env.NICKEL_LATTE_BIN){
 const l=await runAsync('loop producer',env.NICKEL_LATTE_BIN,['emit-fstar',path.join(root,'proofs/LoopUtil.lt')],root,{env});assert.equal(l.status,0);assert.equal(l.stdout,loopView,'complete loop producer/view parity');
 const c=await runAsync('canonical producer',env.NICKEL_LATTE_BIN,['emit-fstar',path.join(root,'proofs/Canonical.lt')],root,{env});assert.equal(c.status,0);assert.equal(c.stdout,canonicalView,'complete generic producer/view parity');
 const rh=await runAsync('history producer',env.NICKEL_LATTE_BIN,['emit-fstar',path.join(root,'proofs/RegisterHistory.lt')],root,{env});assert.equal(rh.status,0);assert.equal(rh.stdout,historyView,'complete history producer/view parity');
 const rv=await runAsync('valid-history producer',env.NICKEL_LATTE_BIN,['emit-fstar',path.join(root,'proofs/RegisterValid.lt')],root,{env});assert.equal(rv.status,0);assert.equal(rv.stdout,validView,'complete valid-history producer/view parity');
 const rpub=await runAsync('public producer',env.NICKEL_LATTE_BIN,['emit-fstar',path.join(root,'proofs/RegisterPublic.lt')],root,{env});assert.equal(rpub.status,0);assert.equal(rpub.stdout,publicView,'complete public producer/view parity');
 const rp=await runAsync('exact past producer',env.NICKEL_LATTE_BIN,['emit-fstar',path.join(root,'proofs/RegisterPast.lt')],root,{env});assert.equal(rp.status,0);assert.equal(rp.stdout,pastView,'complete exact past producer/view parity');
 const p=await runAsync('checkpoint producer',env.NICKEL_LATTE_BIN,['emit-fstar',path.join(root,'proofs/Register.lt')],root,{env});
 await fs.writeFile(path.join(output,'producer.log'),p.log);assert.equal(p.status,0);assert.equal(p.stdout,view,'full producer/view parity');
}
const source=await fs.readFile(path.join(root,'src/register.rs'),'utf8');
const graphSource=await fs.readFile(path.join(root,'src/event_layer.rs'),'utf8');
const graphModes=new Set(['past-skips-parent-check','past-extend-never-pushes','past-extend-unselected','canonical-push-drops-value','canonical-copies-wrong-fact','canonical-discards-output','canonical-chooses-largest','canonical-choice-always-errors']);
const bodyModes=[
 ['new-repeats-fact','pub fn new(',"facts: Vec::new()","facts: { let f = Fact { id: Id { peer: writer, counter: 1 }, after: Vec::new(), payload: Write { key: 0, value: Vec::new(), observed: Vec::new(), lamport: 1 } }; let mut facts = Vec::new(); facts.push(f.clone()); facts.push(f); facts }",'new_has_unique_ids'],
 ['canonical-choice-always-errors','fn choose_unseen<','Ok(chosen)','Err(internal())','Canonical.choose_finishes_scan'],
 ['execute-always-errors','fn execute(','Ok(next)','Err(invalid())','execute_succeeds_for_unique_ids'],
 // Writer streams: the native previous/forbidden policy is what makes an Added offer's stream clause true.
 ['stream-previous-skips','fn previous(','counter: id.counter - 1','counter: id.counter - 2','RegisterValid.offered_stream_from_checks'],
 ['stream-forbidden-strict','fn forbidden(','ancestor.counter >= offered.counter','ancestor.counter > offered.counter','RegisterValid.offered_stream_from_checks'],
 // Fresh-replica base case: one stored fact whose value equals its observation breaks values_changed only (one fact, so #117's positional uniqueness still holds).
 // Receive meaning: a duplicate callback that reports a conflicting retained id as Duplicate.
 ['duplicate-conflict-as-duplicate','fn duplicate(','Some(false) => Err(Error::Conflict),','Some(false) => Ok(true),','RegisterPublic.duplicate_by_classify'],
 // Producer bookkeeping base case: a constructor starting the private counter at 0.
 ['producer-new-counter-zero','pub fn new(','next_counter: 1,','next_counter: 0,','RegisterPublic.new_public_producer'],
 ['history-new-unchanged-value','pub fn new(',"facts: Vec::new()","facts: { let mut facts = Vec::new(); facts.push(Fact { id: Id { peer: writer, counter: 1 }, after: Vec::new(), payload: Write { key: 0, value: Vec::new(), observed: Vec::new(), lamport: 1 } }); facts }",'RegisterValid.new_establishes_history'],
 // History invariant (receive half): an Added offer's parents are stored only because past checks them.
 ['past-skips-parent-check','fn past<','    validate_after(facts, after_ids, ops)?;\n','','RegisterHistory.past_checked_parents'],
 // Exact past directions (#97 obligation 1): each native fault breaks only its own direction.
 ['past-extend-never-pushes','fn extend_past<','if !has_id(&selected, &predecessor, ops) {','if false && !has_id(&selected, &predecessor, ops) {','RegisterPast.extend_past_covers_predecessors'],
 ['past-extend-unselected','fn extend_past<','if has_id(&selected, &id(fact), ops) {','if true {','RegisterPast.extend_past_preserves'],
 ['canonical-chooses-largest','fn choose_unseen<','id_lt(&id(&facts[j]), &id(&facts[k]))','id_lt(&id(&facts[k]), &id(&facts[j]))','Canonical.choose_is_least'],
 ['register-wrong-order-policy','const OPS:','graph::graph_ops(identity, parents, same_id, less_id,','graph::graph_ops(identity, parents, same_id, same_id,','register_order_policy_is_exact'],
 ['register-orders-counter-first','fn less_id(','a.peer < b.peer || (a.peer == b.peer && a.counter < b.counter)','a.counter < b.counter || (a.counter == b.counter && a.peer < b.peer)','less_id_is_lexicographic'],
 ['canonical-push-drops-value','fn push<','xs.push(value);','let _ = value;','Canonical.push_is_exact'],
 ['canonical-copies-wrong-fact','fn canonical_step<','clone_selected_fact(&facts[i], clone_fact)','clone_selected_fact(&facts[0], clone_fact)','Canonical.step_uses_selected_fact'],
 ['canonical-discards-output','fn canonical<','Ok(out)','Ok(Vec::new())','Canonical.canonical_selects_whole_facts'],
 ['prepare-appends-wrong-fact','fn prepare(','graph::push(&mut next.facts, fact.clone(), invalid)?;','graph::push(&mut next.facts, { let mut wrong = fact.clone(); wrong.payload.key = 0; wrong }, invalid)?;','prepare_appends_exact_fact'],
 ['execute-canonicalizes-wrong-input','fn execute(','graph::canonical(&next.facts, &OPS.0)','graph::canonical(&Vec::new(), &OPS.0)','execute_preserves_exact_fact_contents'],

 ['clock-forgets-maximum','pub fn next_lamport(','if fact.payload.lamport > highest','if false && fact.payload.lamport > highest','next_lamport_is_maximum_successor'],
 ['clock-invents-maximum','pub fn next_lamport(','let mut highest = 0;','let mut highest = 1;','next_lamport_is_maximum_successor'],
 ['clock-ignores-overflow','pub fn next_lamport(','highest.checked_add(1).ok_or(Error::ClockExhausted)','Ok(0)','next_lamport_is_maximum_successor'],
 ['validate-skips-clock','fn validate(','if fact.payload.lamport != next_lamport(&basis)?','if false && fact.payload.lamport != next_lamport(&basis)?','validation_is_exact_basis_checks'],
 ['validate-skips-observed','fn validate(','if !bytes_equal(&fact.payload.observed,','if false && !bytes_equal(&fact.payload.observed,','validation_is_exact_basis_checks'],
 ['validate-allows-noedit','fn validate(','|| bytes_equal(&fact.payload.value, &fact.payload.observed)','|| false','validation_is_exact_basis_checks'],
 ['validate-always-refuses','fn validate(','    Ok(())\n}','    Err(Error::Invalid)\n}','validation_is_exact_basis_checks'],
 ['validate-wrong-basis-argument','fn validate(','graph::select_basis(&before.facts, &selected, &OPS.0)','graph::select_basis(&before.facts, &fact.after, &OPS.0)','validation_is_exact_basis_checks'],
 ['write-authors-wrong-key','pub fn write(','payload: Write { key, value, observed,','payload: Write { key: 0, value, observed,','write_installs_successful_candidate'],
 ['write-skips-installation','pub fn write(','*self = candidate;','self.next_counter = next;','write_installs_successful_candidate'],
 ['write-installs-wrong-facts','pub fn write(','*self = candidate;','candidate.facts = Vec::new(); *self = candidate;','write_installs_successful_candidate'],
 ['write-receives-wrong-key','pub fn write(','candidate.receive(fact.clone())','candidate.receive({ let mut offered = fact.clone(); offered.payload.key = 0; offered })','write_installs_successful_candidate'],
 ['prepare-corrupts-counter','fn prepare(','graph::push(&mut next.facts, fact.clone(), invalid)?;','graph::push(&mut next.facts, fact.clone(), invalid)?; next.next_counter = 0;','prepare_preserves_private'],
 ['execute-corrupts-writer','fn execute(','next.facts = graph::canonical(&next.facts, &OPS.0)?;','next.facts = graph::canonical(&next.facts, &OPS.0)?; next.writer = 0;','execute_preserves_private'],
 ['plan-wrong-prepare-policy','fn planned(','duplicate, validate, prepare, execute','duplicate, validate, |context, next, fact| { let mut n = prepare(context, next, fact)?; n.writer = 0; Ok(n) }, execute','planned_preserves_private'],
 ['write-advances-before-admission','pub fn write(','let mut candidate = self.clone();','self.next_counter = next; let mut candidate = self.clone();','write_publication_on_every_return'],
 ['write-publishes-wrong-counter','pub fn write(','candidate.next_counter = next;','candidate.next_counter = 0;','write_publication_on_every_return'],
 ['write-returns-wrong-identity','pub fn write(','Ok(Some(fact))','{ let mut returned = fact; returned.id.counter = 0; Ok(Some(returned)) }','write_publication_on_every_return'],
 ['winner-forgets-result','pub fn winner(','    found\n}','    None\n}','winner_is_priority_maximum'],
 ['read-discards-selected-value','pub fn read_history(','facts[i].payload.value.clone()','initial.to_vec()','read_history_selects_maximum'],
 ['fact-equality-wrong-argument','fn fact_equal(','crate::causal::event_equal(a, b, write_equal)','crate::causal::event_equal(a, a, write_equal)','fact_equal_is_complete'],
 ['copy-changes-key','fn copy_fact(','f.clone()','{ let mut copy = f.clone(); copy.payload.key = 0; copy }','copy_fact_is_exact'],
 ['bytes-accept-mismatch','pub fn bytes_equal(','if a[i] != b[i] { return false; }','if a[i] != b[i] { return true; }','bytes_equal_exact'],
 ['priority-reverses-clock','pub fn later(','a.payload.lamport > b.payload.lamport','a.payload.lamport < b.payload.lamport','later_is_priority'],
 ['noedit-counted','pub fn write(','if bytes_equal(&value, &observed)','if false','equal_value_write_is_neutral'],
 ['receive-error-corrupts-counter','pub fn receive(','shell::receive_into(self, &fact, &(), planned, Admission::Added, Admission::Duplicate)','let result = shell::receive_into(self, &fact, &(), planned, Admission::Added, Admission::Duplicate); if result.is_err() { self.next_counter = 0; } result','receive_publication_is_exact'],
 ['read-wrong-key','pub fn read(','read_history(&self.facts, &self.initial, key)','read_history(&self.facts, &self.initial, 0)','public_read_is_history'],
 ['payload-ignores-observed','fn write_equal(','&& bytes_equal(&a.observed, &b.observed)','&& true','write_equal_is_exact'],
];
assert(selected.every(n=>n==='positive'||["without-plan-publication-contract","without-duplicate-planning-contract","without-stored-classification-contract","without-added-publication-plan","without-write-added-installation","without-added-meaning-at","without-write-meaning-receive","without-write-meaning-read","without-write-meaning-added","without-meaning-single-hit","without-meaning-classifier-law","without-meaning-some-hit","without-meaning-publication","without-meaning-plan","without-meaning-classify","without-meaning-stored","without-added-meaning-fresh","without-added-meaning-parents","without-added-meaning-observation","without-added-meaning-clock","without-added-meaning-stream","without-added-meaning-extension","without-added-meaning-public","without-read-public-method","without-producer-new-history","without-producer-receive-history","without-producer-receive-frame","without-producer-write-history","without-producer-write-outcome","without-producer-write-installation","without-wrap-outcome","without-stream-step-path","without-public-clock-bridge","without-read-clock-premise","without-read-history-bridge","without-read-single-value-premises","without-read-steps-law","without-positional-premise","without-public-receive-history","without-public-receive-unique","without-public-write-history","without-public-write-unique","without-public-new-history","without-public-new-unique","without-stream-extension","without-stream-preservation","without-stream-native-checks","without-receive-stream-witness","without-read-filter","without-history-receive-publication","without-history-receive-added","without-history-write-installation","without-history-write-counted","without-added-clock-basis","without-clock-extension","without-plan-receive-history","without-write-plan-history","without-freeze-maximum-read","without-fresh-classification","without-dominator-clock","without-extension-walk","without-unreferenced-walk","without-fresh-lookup","without-presence-loop","without-basis-filter","without-read-maximum-contract","without-past-soundness-closure","without-past-completeness-paths","without-admission-exact-selection","without-admission-whole-basis","without-frozen-payload-checks","without-ancestor-clock-step","without-order-unique-premise","without-added-id-order","without-counted-id-order","without-receive-id-publication","without-receive-added-unique","without-write-id-neutrality","without-write-counted-unique","without-receive-execute-unique","without-write-execute-unique","without-receive-result-execute","without-write-result-execute"].includes(n)||bodyModes.some(m=>m[0]===n)||["without-execute-success-id-policy","without-choice-scan-contract","without-shorter-output-missing","without-step-membership-contract","without-step-success-contract","without-canonical-success-loop","without-execute-success-contract","without-agreement-order","without-agreement-contents","without-agreement-vector-equality","without-execute-agreement-contract","without-minimum-order-contract","without-canonical-order-contract","without-write-order-plan","without-receive-order-plan","without-generic-append-contract","without-canonical-selection-contract","without-canonical-coverage-contract","without-loop-unroll","without-loop-recursion","without-loop-empty","without-generic-step-equation","without-generic-push-contract","without-generic-membership-contract","without-generic-choice-loop","without-generic-canonical-loop","without-generic-choice-contract","without-generic-step-contract","without-register-canonical-policy","without-register-canonical-content","without-prepare-content","without-plan-prepared-content","without-receive-retention-plan","without-write-retention-installation","without-clock-loop-contract","without-added-clock-contract","without-added-clock-payload","without-validation-byte-contract","without-payload-validation-contract","without-payload-planning-contract","without-receive-payload-contract","without-added-publication-contract","without-write-receive-publication","without-write-receive-frame","without-winner-loop","without-read-winner","without-publication-contract","without-noedit-byte-contract","without-shared-planning-contract","without-prepare-frame","without-execute-frame","without-receive-publication-frame","without-plan-private-frame"].includes(n)),'unknown selected mode');
// The actual const policy has no brace body; bind this one construction-site
// control to its complete exact code item, never a later function's body.
function registerPolicyAnchor(source,anchor){
 const item='const OPS: graph::EventOps<Fact, Id, Error> = graph::event_ops(\n    graph::graph_ops(identity, parents, same_id, less_id, copy_fact, fact_equal, invalid, missing),\n    previous, forbidden, capacity, capacity, invalid, invalid,\n);';
 assert.equal(source.split(item).length,2,'one exact register policy item');
 const at=source.indexOf(item);assert.equal(codeMask(source).slice(at,at+item.length),item,'policy item is code');
 assert.equal(item.split(anchor).length,2,'one policy slot');return at+item.indexOf(anchor);
}
assert.throws(()=>registerPolicyAnchor(source+source,'graph::graph_ops(identity, parents, same_id, less_id,'),'duplicate const policy refuses');
assert.throws(()=>registerPolicyAnchor(source.replace('const OPS:','// const OPS:'),'graph::graph_ops(identity, parents, same_id, less_id,'),'commented const policy refuses');
assert.throws(()=>registerPolicyAnchor(source.replace('const OPS:','const OTHER_OPS:'),'graph::graph_ops(identity, parents, same_id, less_id,'),'missing const policy never borrows a later item');
const haxArgs=out=>['-C','--offline','--locked','-p','nickel-crdt',';','into','--output-dir',out,'-i','-** +nickel_crdt::register::**::new +nickel_crdt::register::**::write +nickel_crdt::register::**::receive +nickel_crdt::register::**::read +nickel_crdt::register::winner +nickel_crdt::register::later +nickel_crdt::register::bytes_equal +nickel_crdt::register::next_lamport +nickel_crdt::register::less_id +nickel_crdt::event_shell::receive +nickel_crdt::causal::classify +nickel_crdt::event_layer::**','fstar'];
const inventory=['Nickel_crdt.Causal.fst','Nickel_crdt.Event_layer.fst','Nickel_crdt.Event_shell.fst','Nickel_crdt.Register.fst'];
const proofFiles=['Nickel.Prelude.fst','Nickel.LoopUtil.fst','Nickel.EventShell.fst','Nickel.Vector.fst','Nickel.EventGraph.fst','Nickel.EventClassifier.fst'];
async function support(dir){
 await fs.mkdir(dir,{recursive:true});
 for(const f of proofFiles)await put(path.join(dir,f),await fs.readFile(path.join(root,'proofs/generated',f)));
 await put(path.join(dir,'Nickel.Canonical.fst'),canonicalView);
 await put(path.join(dir,'Nickel.RegisterPast.fst'),pastView);
 await put(path.join(dir,'Nickel.CausalEnvelope.fst'),await fs.readFile(path.join(root,'proofs/causal-envelope-view/Nickel.CausalEnvelope.fst')));
}
async function check(dir,roots,log){
 const r=await verify({dir,roots:roots.map(f=>path.join(dir,f)),fstar:env.NICKEL_PROOF_FSTAR,models:env.NICKEL_HAX_SOURCE,modelCache:env.NICKEL_FSTAR_MODEL_CACHE});
 await fs.writeFile(log,r.log);return r;
}
// Register no longer imports RegisterPast; RegisterHistory imports both. Verify the owner's module
// (positive: everything) so a RegisterPast or RegisterHistory owner is actually checked.
const rootsFor=owner=>!owner?['Nickel.Register.fst','Nickel.RegisterPublic.fst']:owner.startsWith('RegisterPublic.')?['Nickel.RegisterPublic.fst']:owner.startsWith('RegisterValid.')?['Nickel.RegisterValid.fst']:owner.startsWith('RegisterHistory.')?['Nickel.RegisterHistory.fst']:owner.startsWith('RegisterPast.')?['Nickel.RegisterPast.fst']:['Nickel.Register.fst'];
const results=[];
for(const [name,header,anchor,replacement,owner] of [['positive',null,null,null,null],...bodyModes]){
 if(selected.length&&!selected.includes(name)&&name!=='positive')continue;
 const mode=path.join(output,name),crate=path.join(mode,'crate'),extract=path.join(mode,'extract'),dir=path.join(mode,'proof');
 await fs.mkdir(crate,{recursive:true});await fs.cp(path.join(root,'src'),path.join(crate,'src'),{recursive:true,force:true});
 for(const f of ['Cargo.toml','Cargo.lock'])await fs.copyFile(path.join(root,f),path.join(crate,f));
 await fs.cp(path.join(root,'proof-smoke'),path.join(crate,'proof-smoke'),{recursive:true,force:true});
 const sourceFile=graphModes.has(name)?'src/event_layer.rs':'src/register.rs',original=graphModes.has(name)?graphSource:source;
 let changed=original;if(header){const at=header==='const OPS:'?registerPolicyAnchor(original,anchor):scopedAnchor(original,header,anchor,name);changed=original.slice(0,at)+replacement+original.slice(at+anchor.length);await fs.writeFile(path.join(crate,sourceFile),changed);}
 await fs.rm(extract,{recursive:true,force:true});await fs.mkdir(extract,{recursive:true});
 const r=await runAsync(name+' extraction',env.NICKEL_HAX_BIN,haxArgs(extract),crate,{env:{...env,CARGO_TARGET_DIR:path.join(mode,'target')}});
 await fs.writeFile(path.join(mode,'extraction.log'),r.log);assert.equal(r.status,0,name+': extraction failed');
 assert.deepEqual((await fs.readdir(extract)).filter(f=>/\.fsti?$/.test(f)).sort(),inventory);
 await support(dir);
 for(const f of inventory){const b=await fs.readFile(path.join(extract,f));assert(!/assume\s+val/.test(b.toString()),name+': assumed native body');if(!header)assert(b.equals(await fs.readFile(path.join(views,f))),'fresh production native identity: '+f);await put(path.join(dir,f),b);}
 const native=await check(dir,['Nickel_crdt.Register.fst'],path.join(mode,'native-typecheck.log'));assert.equal(native.status,0,name+': native type error is not owner rejection');
 const file=path.join(dir,'Nickel.Register.fst');await put(file,view);await put(path.join(dir,'Nickel.RegisterHistory.fst'),historyView);await put(path.join(dir,'Nickel.RegisterValid.fst'),validView);await put(path.join(dir,'Nickel.RegisterPublic.fst'),publicView);
 const checked=await check(dir,rootsFor(owner),path.join(mode,'proof.log'));
 const ordinary=owner?hasOrdinaryTheoremRejection({status:checked.status,log:checked.log,theorem:/^(Canonical|RegisterPast|RegisterHistory|RegisterValid|RegisterPublic)\./.test(owner)?'Nickel.'+owner:'Nickel.Register.'+owner,view:owner.startsWith('Canonical.')?canonicalView:owner.startsWith('RegisterPast.')?pastView:owner.startsWith('RegisterHistory.')?historyView:owner.startsWith('RegisterValid.')?validView:owner.startsWith('RegisterPublic.')?publicView:view}):null;
 if(owner)assert(ordinary,name+': ordinary named owner rejection required');else assert.equal(checked.status,0,'checkpoint positive failed');
 results.push({name,owner,status:checked.status,ordinary,sourceFile,source:digest(changed),log:digest(checked.log)});
 console.log('PASS '+name);
}
const positive=path.join(output,'positive/proof'),file=path.join(positive,'Nickel.Register.fst');
function replaceInDeclaration(name,needle,replacement,sourceView=view){
 const start=sourceView.indexOf('let '+name+' ');assert(start>=0);
 const next=/\nlet (?:rec )?\w+ /.exec(sourceView.slice(start+4)),end=next?start+4+next.index:sourceView.length;
 const decl=sourceView.slice(start,end);assert.equal(decl.split(needle).length,2,name+': unique control anchor');
 return sourceView.slice(0,start)+decl.replace(needle,replacement)+sourceView.slice(end);
}
function withholdReceivePublication(sourceView=view){
 const name='receive_preserves_private',start=sourceView.indexOf('let '+name+' ');assert(start>=0);
 const next=/\nlet (?:rec )?\w+ /.exec(sourceView.slice(start+4)),end=next?start+4+next.index:sourceView.length;
 let decl=sourceView.slice(start,end);const needle='    Tactics.prune "Nickel_crdt.Register.impl_Replica__receive";';
 assert.equal(decl.split(needle).length,4,'three receive frame query boundaries');
 decl=decl.replaceAll(needle,needle+'\n    Tactics.prune "Nickel.Register.receive_publication_is_exact";');
 assert.equal(decl.split('  receive_publication_is_exact before offered;').length,2);
 decl=decl.replace('  receive_publication_is_exact before offered;','  ();');
 return sourceView.slice(0,start)+decl+sourceView.slice(end);
}
function withholdWriteContract(law,sourceView=view){
 const name='write_installs_successful_candidate',start=sourceView.indexOf('let '+name+' ');assert(start>=0);
 const next=/\nlet (?:rec )?\w+ /.exec(sourceView.slice(start+4)),end=next?start+4+next.index:sourceView.length;
 let decl=sourceView.slice(start,end);const needle='Tactics.prune "Nickel_crdt.Register.planned";';
 assert.equal(decl.split(needle).length,7,'six write-installation query boundaries');
 decl=decl.replaceAll(needle,needle+'\n    Tactics.prune "Nickel.Register.'+law+'";');
 const call='  '+law+' before authored;';assert.equal(decl.split(call).length,2,'one explicit write contract use');
 decl=decl.replace(call,'  ();');
 return sourceView.slice(0,start)+decl+sourceView.slice(end);
}
// Suppress automatic contracts only at this caller's counted query boundaries.
function withholdPayloadContract(name,boundary,count,laws,calls,sourceView=view){
 const start=sourceView.indexOf('let '+name+' ');assert(start>=0);
 const next=/\nlet (?:rec )?\w+ /.exec(sourceView.slice(start+4)),end=next?start+4+next.index:sourceView.length;
 let decl=sourceView.slice(start,end);const needle='Tactics.prune "'+boundary+'";';
 assert.equal(decl.split(needle).length,count+1,name+': exact query boundary count');
 decl=decl.replaceAll(needle,needle+laws.map(l=>'\n    Tactics.prune "'+l+'";').join(''));
 for(const call of calls){assert.equal(decl.split(call).length,2,name+': one explicit contract use');decl=decl.replace(call,'  ();');}
 return sourceView.slice(0,start)+decl+sourceView.slice(end);
}
const loopLine=view.split('\n').find(l=>l.startsWith('  Nickel.LoopUtil.plain_preserve_any #(Option.t_Option usize)'));
assert(loopLine,'actual winner loop contract');
const clockLoopLine=view.split('\n').find(l=>l.startsWith('  Nickel.LoopUtil.plain_preserve_any #u64 '));
assert(clockLoopLine,'actual clock loop contract');
const canonicalChoiceLoop=canonicalView.split('\n').find(l=>l.startsWith('  Nickel.LoopUtil.result_preserve_any')&&l.includes('fresh_prefix'));
const canonicalWholeLoop=canonicalView.split('\n').find(l=>l.startsWith('  Nickel.LoopUtil.result_preserve_any')&&l.includes('content_prefix'));
assert(canonicalChoiceLoop&&canonicalWholeLoop,'actual generic loop interfaces');
// Branch-local queries make the formerly uncredited append probe a registered
// control. The earlier nonterminal attempt remains retained.
const presenceLoop=historyView.split('\n').find(l=>l.startsWith('  Nickel.LoopUtil.result_preserve_any (mk_usize 0) (Core_models.Slice.impl__len after)'));
assert(presenceLoop,'actual validate_after loop contract');
const depModes=[
 // History invariant (receive half), one owner per new law.
 // Exact clocks / value change and the write path.
 // All-return callers and the public Added clock/value bridge (Lynn's coverage review).
 ['without-history-receive-publication',withholdPayloadContract('receive_preserves_history','Nickel_crdt.Register.impl_Replica__receive',3,['Nickel.Register.receive_publication_is_exact'],['  Nickel.Register.receive_publication_is_exact before offered;'],validView),'RegisterValid.receive_preserves_history'],
 ['without-history-receive-added',withholdPayloadContract('receive_preserves_history','Nickel_crdt.Register.impl_Replica__receive',3,['Nickel.RegisterHistory.receive_added_preserves_history'],['  receive_added_preserves_history before offered;'],validView),'RegisterValid.receive_preserves_history'],
 ['without-history-write-installation',withholdPayloadContract('write_preserves_history','Nickel_crdt.Register.impl_Replica__write',3,['Nickel.Register.write_installs_successful_candidate'],['  Nickel.Register.write_installs_successful_candidate before key value;'],validView),'RegisterValid.write_preserves_history'],
 ['without-history-write-counted',withholdPayloadContract('write_preserves_history','Nickel_crdt.Register.impl_Replica__write',3,['Nickel.RegisterHistory.write_counted_preserves_history'],['  write_counted_preserves_history before key value;'],validView),'RegisterValid.write_preserves_history'],
 ['without-added-clock-basis',withholdPayloadContract('receive_added_preserves_history','Nickel_crdt.Register.impl_Replica__receive',1,['Nickel.RegisterHistory.receive_added_basis_is_exact_ancestry'],['  receive_added_basis_is_exact_ancestry before offered;'],validView),'RegisterValid.receive_added_preserves_history'],
 // clock_exact_from_basis is definitional (its proof is ()), so withholding it still verifies: not a dependency control.
 // Public callers: #117's positional uniqueness alongside the history invariant.
 // Per-caller native-contract links (explicit call removed; its hinted law is hidden at the consuming queries).
 ['without-plan-publication-contract',replaceInDeclaration('receive_by_plan',"  Nickel.Register.receive_publication_is_exact before offered;",'  ();',publicView),'RegisterPublic.receive_by_plan'],
 ['without-duplicate-planning-contract',replaceInDeclaration('plan_by_duplicate',"  Nickel.EventShell.planning_is_exact before offered () Native.duplicate Native.validate Native.prepare Native.execute;",'  ();',publicView),'RegisterPublic.plan_by_duplicate'],
 ['without-stored-classification-contract',replaceInDeclaration('duplicate_classification_is_stored',"  Nickel.EventClassifier.classification_is_exact h offered Native.v_OPS._1;",'  ();',publicView),'RegisterPublic.duplicate_classification_is_stored'],
 // Receive meaning: every non-Added return (Duplicate/Conflict/errors) and Added as a valid fresh extension.
 ['without-meaning-single-hit',replaceInDeclaration('stored_id_classifies',"  lookup_single_hit h offered Native.v_OPS._1._1._1 Native.v_OPS._1._1._3 Native.v_OPS._1._1._6 (mk_usize 0) j;",'  ();',publicView),'RegisterPublic.stored_id_classifies'],
 ['without-meaning-classifier-law',replaceInDeclaration('stored_id_classifies',"  Nickel.EventClassifier.classification_is_exact h offered Native.v_OPS._1;",'  ();',publicView),'RegisterPublic.stored_id_classifies'],
 ['without-meaning-some-hit',replaceInDeclaration('duplicate_classification_is_stored',"  lookup_some_hits h offered Native.v_OPS._1._1._1 Native.v_OPS._1._1._3 Native.v_OPS._1._1._6 (mk_usize 0) true;",'  ();',publicView),'RegisterPublic.duplicate_classification_is_stored'],
 ['without-meaning-publication',replaceInDeclaration('receive_duplicate_meaning',"  receive_by_plan before offered;",'  ();',publicView),'RegisterPublic.receive_duplicate_meaning'],
 ['without-meaning-plan',replaceInDeclaration('receive_duplicate_meaning',"  plan_by_duplicate before offered;",'  ();',publicView),'RegisterPublic.receive_duplicate_meaning'],
 ['without-meaning-classify',replaceInDeclaration('receive_duplicate_meaning',"  duplicate_by_classify before offered;",'  ();',publicView),'RegisterPublic.receive_duplicate_meaning'],
 ['without-meaning-stored',replaceInDeclaration('receive_duplicate_meaning',"  FStar.Classical.move_requires (duplicate_classification_is_stored h) offered;",'  ();',publicView),'RegisterPublic.receive_duplicate_meaning'],
 ['without-added-meaning-fresh',replaceInDeclaration('receive_added_meaning',"  receive_added_offer_is_fresh before offered;",'  ();',publicView),'RegisterPublic.receive_added_meaning'],
 ['without-added-meaning-parents',replaceInDeclaration('receive_added_meaning',"  receive_added_parents_stored before offered;",'  ();',publicView),'RegisterPublic.receive_added_meaning'],
 ['without-added-meaning-observation',replaceInDeclaration('receive_added_meaning',"  FStar.Classical.move_requires (id_frozen_gives_observation before) offered;",'  ();',publicView),'RegisterPublic.receive_added_meaning'],
 ['without-added-meaning-clock',replaceInDeclaration('receive_added_meaning',"  FStar.Classical.move_requires (exact_basis_gives_clock_and_value before) offered;",'  ();',publicView),'RegisterPublic.receive_added_meaning'],
 ['without-added-meaning-stream',replaceInDeclaration('receive_added_meaning',"  receive_added_offer_stream before offered;",'  ();',publicView),'RegisterPublic.receive_added_meaning'],
 ['without-added-meaning-extension',replaceInDeclaration('receive_added_meaning',"  Nickel.Register.receive_added_retains_exact_facts before offered;",'  ();',publicView),'RegisterPublic.receive_added_meaning'],
 ['without-added-meaning-public',replaceInDeclaration('receive_added_meaning',"  receive_preserves_public_history before offered;",'  ();',publicView),'RegisterPublic.receive_added_meaning'],
 // Write meaning: a counted write's authored fact is a fresh valid offer through its installed Added candidate.
 ['without-added-publication-plan',replaceInDeclaration('planned_some_is_added',"  Nickel.Register.receive_publication_is_exact before offered;",'  ();',publicView),'RegisterPublic.planned_some_is_added'],
 ['without-write-added-installation',replaceInDeclaration('write_counted_is_added_receive',"  Nickel.Register.write_installs_successful_candidate before key value;",'  ();',publicView),'RegisterPublic.write_counted_is_added_receive'],
 ['without-write-meaning-receive',replaceInDeclaration('write_counted_meaning',"    write_counted_is_added_receive before key value next authored;",'  ();',publicView),'RegisterPublic.write_counted_meaning'],
 ['without-write-meaning-read',replaceInDeclaration('write_counted_meaning',"  public_read_is_the_causal_read before key (Alloc.Vec.impl_1__as_slice (Native.impl_Replica__read before key));",'  ();',publicView),'RegisterPublic.write_counted_meaning'],
 ['without-write-meaning-added',replaceInDeclaration('write_counted_meaning',"    receive_added_meaning_at before authored (Native.impl_Replica__receive before authored)._1;",'  ();',publicView),'RegisterPublic.write_counted_meaning'],
 ['without-added-meaning-at',replaceInDeclaration('receive_added_meaning_at',"  receive_added_meaning before offered;",'  ();',publicView),'RegisterPublic.receive_added_meaning_at'],
 // Public producer bookkeeping (local meaning, not ID allocation/recovery).
 ['without-producer-new-history',replaceInDeclaration('new_public_producer',"  new_establishes_public_history writer initial limits;",'  ();',publicView),'RegisterPublic.new_public_producer'],
 ['without-producer-receive-history',replaceInDeclaration('receive_public_producer',"  receive_preserves_public_history before offered;",'  ();',publicView),'RegisterPublic.receive_public_producer'],
 ['without-producer-receive-frame',replaceInDeclaration('receive_public_producer',"  Nickel.Register.receive_preserves_private before offered;",'  ();',publicView),'RegisterPublic.receive_public_producer'],
 ['without-producer-write-history',replaceInDeclaration('write_public_producer',"  write_preserves_public_history before key value;",'  ();',publicView),'RegisterPublic.write_public_producer'],
 ['without-producer-write-outcome',replaceInDeclaration('write_public_producer',"  Nickel.Register.write_publication_on_every_return before key value;",'  ();',publicView),'RegisterPublic.write_public_producer'],
 ['without-producer-write-installation',replaceInDeclaration('write_public_producer',"  Nickel.Register.write_installs_successful_candidate before key value;",'  ();',publicView),'RegisterPublic.write_public_producer'],
 ['without-wrap-outcome',replaceInDeclaration('counted_write_does_not_wrap',"  Nickel.Register.write_publication_on_every_return before key value;",'  ();',publicView),'RegisterPublic.counted_write_does_not_wrap'],
 // Public read: single-valued causal read of a public replica.
 // Caller-level public-method equation (its hint is hidden at the final query; the lower native read-wrong-key owner stays).
 ['without-read-public-method',replaceInDeclaration('public_read_is_the_causal_read',"  Nickel.Register.public_read_is_history r key;",'  ();',publicView),'RegisterPublic.public_read_is_the_causal_read'],
 ['without-stream-step-path',replaceInDeclaration('stream_step_at',"    id_path_clock_decreases h f root steps g;",'    ();',publicView),'RegisterPublic.stream_step_at'],
 ['without-public-clock-bridge',replaceInDeclaration('public_clocks_increase',"  positional_clocks_from_ids (Alloc.Vec.impl_1__as_slice r.f_facts);",'  ();',publicView),'RegisterPublic.public_clocks_increase'],
 ['without-read-clock-premise',replaceInDeclaration('public_read_is_the_causal_read',"  public_clocks_increase r;",'  ();',publicView),'RegisterPublic.public_read_is_the_causal_read'],
 ['without-read-history-bridge',replaceInDeclaration('public_read_is_the_causal_read',"  read_history_is_causal_read h init key;",'  ();',publicView),'RegisterPublic.public_read_is_the_causal_read'],
 ['without-read-single-value-premises',replaceInDeclaration('public_read_is_the_causal_read',"  public_single_value_premises r;",'  ();',publicView),'RegisterPublic.public_read_is_the_causal_read'],
 ['without-read-steps-law',replaceInDeclaration('public_read_is_the_causal_read',"  FStar.Classical.move_requires (causal_read_is_single_valued_by_steps h key init (Alloc.Vec.impl_1__as_slice (Native.impl_Replica__read r key))) x;",'  ();',publicView),'RegisterPublic.public_read_is_the_causal_read'],
 ['without-positional-premise',replaceInDeclaration('positional_ids_are_stored_unique','(requires Nickel.Register.fact_ids_unique facts)','',publicView),'RegisterPublic.positional_ids_are_stored_unique'],
 ['without-public-receive-history',replaceInDeclaration('receive_preserves_public_history','  receive_preserves_history before offered;','  ();',publicView),'RegisterPublic.receive_preserves_public_history'],
 ['without-public-receive-unique',replaceInDeclaration('receive_preserves_public_history','  Nickel.Register.receive_preserves_unique_ids before offered;','  ();',publicView),'RegisterPublic.receive_preserves_public_history'],
 ['without-public-write-history',replaceInDeclaration('write_preserves_public_history','  write_preserves_history before key value;','  ();',publicView),'RegisterPublic.write_preserves_public_history'],
 ['without-public-write-unique',replaceInDeclaration('write_preserves_public_history','  Nickel.Register.write_preserves_unique_ids before key value;','  ();',publicView),'RegisterPublic.write_preserves_public_history'],
 ['without-public-new-history',replaceInDeclaration('new_establishes_public_history','  new_establishes_history writer initial limits;','  ();',publicView),'RegisterPublic.new_establishes_public_history'],
 ['without-public-new-unique',replaceInDeclaration('new_establishes_public_history','  Nickel.Register.new_has_unique_ids writer initial limits;','  ();',publicView),'RegisterPublic.new_establishes_public_history'],
 ['without-stream-extension',replaceInDeclaration('stream_kept','  ancestry_unchanged_by_extension h h2 fnew (Alloc.Vec.impl_1__as_slice g.f_after);','  ();',validView),'RegisterValid.stream_kept'],
 ['without-stream-preservation',replaceInDeclaration('history_from_parts','  FStar.Classical.move_requires (streams_preserved h h2) offered','  ()',validView),'RegisterValid.history_from_parts'],
 ['without-stream-native-checks',replaceInDeclaration('stream_witness','  validated_stream_checks (Alloc.Vec.impl_1__as_slice before.f_facts) offered before.f_limits.f_events before.f_limits.f_dependencies Native.v_OPS;','  ();',validView),'RegisterValid.stream_witness'],
 ['without-receive-stream-witness',replaceInDeclaration('receive_added_offer_stream','  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (stream_witness before offered));','  ();',validView),'RegisterValid.receive_added_offer_stream'],
 ['without-clock-extension',replaceInDeclaration('clock_kept','  ancestry_unchanged_by_extension h h2 fnew (Alloc.Vec.impl_1__as_slice g.f_after);','  ();',validView),'RegisterValid.clock_kept'],
 ['without-plan-receive-history',withholdPayloadContract('planned_preserves_history','Nickel_crdt.Register.impl_Replica__receive',1,['Nickel.RegisterHistory.receive_added_preserves_history'],['  receive_added_preserves_history before offered;'],validView),'RegisterValid.planned_preserves_history'],
 ['without-write-plan-history',withholdPayloadContract('write_counted_preserves_history','Nickel_crdt.Register.impl_Replica__write',1,['Nickel.RegisterHistory.planned_preserves_history'],['  FStar.Classical.forall_intro (planned_preserves_history before);'],validView),'RegisterValid.write_counted_preserves_history'],
 // Contract-only consumers (Lynn's finding): each removal withholds the explicit call and suppresses the law at the boundary.
 ['without-freeze-maximum-read',withholdPayloadContract('basis_freezes_id_read','Nickel_crdt.Register.read_history',1,['Nickel.Register.read_history_selects_maximum'],['  Nickel.Register.read_history_selects_maximum b (Alloc.Vec.impl_1__as_slice before.f_initial) offered.f_payload.f_key;'],historyView),'RegisterHistory.basis_freezes_id_read'],
 ['without-fresh-classification',withholdPayloadContract('not_duplicate_is_fresh','Nickel_crdt.Event_layer.classify',2,['Nickel.EventClassifier.classification_is_exact'],['  Nickel.EventClassifier.classification_is_exact facts offered Native.v_OPS._1;'],historyView),'RegisterHistory.not_duplicate_is_fresh'],
 // filter_has_selected_facts is a pure spec induction; withholding its step is a search, so its dependence is owned at its users.
 ['without-read-filter',replaceInDeclaration('basis_freezes_id_read','filter_has_selected_facts Native.v_OPS._1 facts (Alloc.Vec.impl_1__as_slice selected) (Seq.length facts) b;','();',historyView),'RegisterHistory.basis_freezes_id_read'],
 ['without-dominator-clock',replaceInDeclaration('maximum_is_maximal_in','id_path_clock_decreases facts g next rest f','()',historyView),'RegisterHistory.maximum_is_maximal_in'],
 ['without-extension-walk',replaceInDeclaration('rec id_path_extend','id_path_extend h h2 f next rest finish','()',historyView),'RegisterHistory.id_path_extend'],
 ['without-unreferenced-walk',replaceInDeclaration('rec never_reaches_new','never_reaches_new h2 x next rest','()',historyView),'RegisterHistory.never_reaches_new'],
 // lookup_none_misses' own step: split retries succeed after the failing query, so it is owned at its user.
 ['without-fresh-lookup',replaceInDeclaration('not_duplicate_is_fresh','lookup_none_misses facts offered Native.v_OPS._1._1._1 Native.v_OPS._1._1._3 Native.v_OPS._1._1._6 (mk_usize 0)','()',historyView),'RegisterHistory.not_duplicate_is_fresh'],
 ['without-presence-loop',replaceInDeclaration('validate_after_checks_presence',presenceLoop,'  ();',historyView),'RegisterHistory.validate_after_checks_presence'],
 ['without-basis-filter',replaceInDeclaration('basis_bounds_parent_clocks','filter_has_selected_facts Native.v_OPS._1 facts (Alloc.Vec.impl_1__as_slice selected) (Seq.length facts) (Alloc.Vec.impl_1__as_slice basis);','();',validView),'RegisterValid.basis_bounds_parent_clocks'],
 // Withholding freshness at receive_added_preserves_invariant is a search (20 s, 100% rlimit): that composition
 // dependence is uncontrolled; freshness itself is owned at not_duplicate_is_fresh.
 // Exact past and history meaning (#97 obligation 1): soundness and completeness are separate owners.
 ['without-past-soundness-closure',replaceInDeclaration('past_has_only_ancestors_and_keeps_roots','  past_stays_in_closed_set ops facts roots (ancestor ops facts roots)','  ()',pastView),'RegisterPast.past_has_only_ancestors_and_keeps_roots'],
 ['without-past-completeness-paths',replaceInDeclaration('successful_past_is_exact_closure','      past_contains_every_causal_path ops facts roots root steps id;','      ();',pastView),'RegisterPast.successful_past_is_exact_closure'],
 ['without-admission-exact-selection',replaceInDeclaration('selected_basis_is_exact','  Nickel.RegisterPast.validated_selection_is_exact facts offered before.f_limits.f_events before.f_limits.f_dependencies Native.v_OPS;','  ();',historyView),'RegisterHistory.selected_basis_is_exact'],
 ['without-admission-whole-basis',replaceInDeclaration('selected_basis_is_exact','  Nickel.RegisterPast.actual_basis_is_exact_filter Native.v_OPS._1 facts (Alloc.Vec.impl_1__as_slice selected);','  ();',historyView),'RegisterHistory.selected_basis_is_exact'],
 // The read bridge consumes the maximum-read contract with the native read/winner bodies hidden.
 ['without-read-maximum-contract',withholdPayloadContract('read_history_is_causal_read','Nickel_crdt.Register.read_history',1,['Nickel.Register.read_history_selects_maximum'],['  Nickel.Register.read_history_selects_maximum facts initial key;'],historyView),'RegisterHistory.read_history_is_causal_read'],
 ['without-frozen-payload-checks',replaceInDeclaration('receive_added_freezes_causal_observation','  Nickel.Register.receive_added_checks_payload before offered;','  ();',historyView),'RegisterHistory.receive_added_freezes_causal_observation'],
 // Withholding the clock lemma at its use in priority_maximum_is_causal_maximum leaves a long search
 // (10.6 s, 58% rlimit locally) that crosses the 60 s module cap on CI; own the induction step instead.
 ['without-ancestor-clock-step',replaceInDeclaration('rec ancestor_clock_is_smaller','begin ancestor_clock_is_smaller facts next rest older end','begin () end',historyView),'RegisterHistory.ancestor_clock_is_smaller'],
 // Positional ID uniqueness and actual all-return public caller composition.
 ['without-order-unique-premise',replaceInDeclaration('facts_order_implies_unique','(requires facts_in_id_order facts)',''),'facts_order_implies_unique'],
 ['without-added-id-order',withholdPayloadContract('receive_added_has_unique_ids','Nickel_crdt.Register.impl_Replica__receive',1,['Nickel.Register.receive_added_orders_fact_history'],['  receive_added_orders_fact_history before offered;']),'receive_added_has_unique_ids'],
 ['without-counted-id-order',withholdPayloadContract('write_counted_has_unique_ids','Nickel_crdt.Register.impl_Replica__write',1,['Nickel.Register.write_counted_orders_fact_history'],['  write_counted_orders_fact_history before key value;']),'write_counted_has_unique_ids'],
 ['without-receive-id-publication',withholdPayloadContract('receive_preserves_unique_ids','Nickel_crdt.Register.impl_Replica__receive',3,['Nickel.Register.receive_publication_is_exact'],['  receive_publication_is_exact before offered;']),'receive_preserves_unique_ids'],
 ['without-receive-added-unique',withholdPayloadContract('receive_preserves_unique_ids','Nickel_crdt.Register.impl_Replica__receive',3,['Nickel.Register.receive_added_has_unique_ids'],['  receive_added_has_unique_ids before offered;']),'receive_preserves_unique_ids'],
 ['without-write-id-neutrality',withholdPayloadContract('write_preserves_unique_ids','Nickel_crdt.Register.impl_Replica__write',3,['Nickel.Register.write_publication_on_every_return'],['  write_publication_on_every_return before key value;']),'write_preserves_unique_ids'],
 ['without-write-counted-unique',withholdPayloadContract('write_preserves_unique_ids','Nickel_crdt.Register.impl_Replica__write',3,['Nickel.Register.write_counted_has_unique_ids'],['  write_counted_has_unique_ids before key value;']),'write_preserves_unique_ids'],
 ['without-receive-execute-unique',withholdPayloadContract('receive_result_can_execute','Nickel_crdt.Register.impl_Replica__receive',2,['Nickel.Register.receive_preserves_unique_ids'],['  receive_preserves_unique_ids before offered;']),'receive_result_can_execute'],
 ['without-write-execute-unique',withholdPayloadContract('write_result_can_execute','Nickel_crdt.Register.impl_Replica__write',2,['Nickel.Register.write_preserves_unique_ids'],['  write_preserves_unique_ids before key value;']),'write_result_can_execute'],
 ['without-receive-result-execute',withholdPayloadContract('receive_result_can_execute','Nickel_crdt.Register.execute',1,['Nickel.Register.execute_succeeds_for_unique_ids'],['  execute_succeeds_for_unique_ids after;']),'receive_result_can_execute'],
 ['without-write-result-execute',withholdPayloadContract('write_result_can_execute','Nickel_crdt.Register.execute',1,['Nickel.Register.execute_succeeds_for_unique_ids'],['  execute_succeeds_for_unique_ids after;']),'write_result_can_execute'],
 ['without-execute-success-id-policy',withholdPayloadContract('execute_succeeds_for_unique_ids','Nickel_crdt.Register.v_OPS',2,['Nickel.Register.register_order_policy_is_exact'],['  register_order_policy_is_exact ();']),'execute_succeeds_for_unique_ids'],
 ['without-choice-scan-contract',withholdPayloadContract('canonical_step_succeeds','Nickel_crdt.Event_layer.choose_unseen',7,['Nickel.Canonical.choose_finishes_scan'],['  choose_finishes_scan input old ops;'],canonicalView),'Canonical.canonical_step_succeeds'],
 ['without-shorter-output-missing',replaceInDeclaration('canonical_step_succeeds','  shorter_output_misses_id input old ops;','  ();',canonicalView),'Canonical.canonical_step_succeeds'],
 ['without-step-membership-contract',withholdPayloadContract('canonical_step_succeeds','Nickel_crdt.Event_layer.has_fact',3,['Nickel.EventGraph.fact_membership_is_exact'],['    Nickel.EventGraph.fact_membership_is_exact old (ops._1._1 (Seq.index input j)) ops;'],canonicalView),'Canonical.canonical_step_succeeds'],
 ['without-step-success-contract',withholdPayloadContract('canonical_succeeds_for_unique_ids','Nickel_crdt.Event_layer.canonical_step',2,['Nickel.Canonical.canonical_step_succeeds'],['    canonical_step_succeeds input out ops;'],canonicalView),'Canonical.canonical_succeeds_for_unique_ids'],
 ['without-canonical-success-loop',replaceInDeclaration('canonical_succeeds_for_unique_ids',canonicalView.split('\n').find(l=>l.startsWith('  Nickel.LoopUtil.result_preserve_any')&&l.includes('(fun (_: vector f) -> Prims.l_True)')),'  ();',canonicalView),'Canonical.canonical_succeeds_for_unique_ids'],
 ['without-execute-success-contract',withholdPayloadContract('execute_succeeds_for_unique_ids','Nickel_crdt.Event_layer.canonical',1,['Nickel.Canonical.canonical_succeeds_for_unique_ids'],['  Nickel.Canonical.canonical_succeeds_for_unique_ids (Alloc.Vec.impl_1__as_slice before.f_facts) Native.v_OPS._1;']),'execute_succeeds_for_unique_ids'],
 ['without-agreement-order',withholdPayloadContract('canonical_is_permutation_independent','Nickel_crdt.Event_layer.canonical',3,['Nickel.Canonical.canonical_outputs_strict_id_order'],['  canonical_outputs_strict_id_order left ops;','  canonical_outputs_strict_id_order right ops;'],canonicalView),'Canonical.canonical_is_permutation_independent'],
 ['without-agreement-contents',withholdPayloadContract('canonical_is_permutation_independent','Nickel_crdt.Event_layer.canonical',3,['Nickel.Canonical.canonical_preserves_exact_contents'],['  canonical_preserves_exact_contents left ops;','  canonical_preserves_exact_contents right ops;'],canonicalView),'Canonical.canonical_is_permutation_independent'],
 ['without-agreement-vector-equality',replaceInDeclaration('canonical_is_permutation_independent','  ordered_contents_determine_vector a b ops;','  ();',canonicalView),'Canonical.canonical_is_permutation_independent'],
 ['without-execute-agreement-contract',withholdPayloadContract('execute_agrees_on_same_fact_contents','Nickel_crdt.Event_layer.canonical',1,['Nickel.Canonical.canonical_is_permutation_independent'],['  Nickel.Canonical.canonical_is_permutation_independent (Alloc.Vec.impl_1__as_slice left.f_facts) (Alloc.Vec.impl_1__as_slice right.f_facts) Native.v_OPS._1;']),'execute_agrees_on_same_fact_contents'],
 ['without-minimum-order-contract',withholdPayloadContract('step_preserves_order','Nickel_crdt.Event_layer.choose_unseen',3,['Nickel.Canonical.choose_is_least'],['  choose_is_least input (Alloc.Vec.impl_1__as_slice out) ops;'],canonicalView),'Canonical.step_preserves_order'],
 ['without-canonical-order-contract',withholdPayloadContract('execute_orders_fact_history','Nickel_crdt.Event_layer.canonical',3,['Nickel.Canonical.canonical_outputs_strict_id_order'],['  Nickel.Canonical.canonical_outputs_strict_id_order (Alloc.Vec.impl_1__as_slice before.f_facts) Native.v_OPS._1;']),'execute_orders_fact_history'],
 ['without-write-order-plan',withholdPayloadContract('write_counted_orders_fact_history','Nickel_crdt.Register.planned',1,['Nickel.Register.planned_orders_fact_history'],['  FStar.Classical.forall_intro (planned_orders_fact_history before);']),'write_counted_orders_fact_history'],
 ['without-receive-order-plan',withholdPayloadContract('receive_added_orders_fact_history','Nickel_crdt.Register.planned',3,['Nickel.Register.planned_orders_fact_history'],['  planned_orders_fact_history before offered;']),'receive_added_orders_fact_history'],
 ['without-generic-append-contract',withholdPayloadContract('step_preserves_content','Nickel_crdt.Event_layer.push',4,['Nickel.Canonical.append_preserves_content'],['append_preserves_content input out (Rust_primitives.Slice.slice_index input k) ops;'],canonicalView),'Canonical.step_preserves_content'],
 ['without-canonical-selection-contract',withholdPayloadContract('canonical_preserves_exact_contents','Nickel_crdt.Event_layer.canonical',2,['Nickel.Canonical.canonical_selects_whole_facts'],['  canonical_selects_whole_facts input ops;'],canonicalView),'Canonical.canonical_preserves_exact_contents'],
 ['without-canonical-coverage-contract',withholdPayloadContract('canonical_preserves_exact_contents','Nickel_crdt.Event_layer.canonical',2,['Nickel.Canonical.whole_selection_covers'],['whole_selection_covers input out ops;'],canonicalView),'Canonical.canonical_preserves_exact_contents'],
 ['without-loop-unroll',withholdPayloadContract('rec preserve','Rust_primitives.Hax.Folds.fold_range_return',4,['Nickel.LoopUtil.unroll'],['unroll start finish inv value f;'],loopView),'LoopUtil.preserve'],
 ['without-loop-recursion',replaceInDeclaration('rec preserve','preserve (start +! mk_int 1) finish inv next f p post returned;','();',loopView),'LoopUtil.preserve'],
 ['without-loop-empty',withholdPayloadContract('rec preserve','Rust_primitives.Hax.Folds.fold_range_return',4,['Nickel.LoopUtil.empty'],['empty start finish inv value f;'],loopView),'LoopUtil.preserve'],

 ['without-generic-step-equation',withholdPayloadContract('step_preserves_content','Nickel_crdt.Event_layer.canonical_step',4,['Nickel.Canonical.step_uses_selected_fact'],['  step_uses_selected_fact input out ops;'],canonicalView),'Canonical.step_preserves_content'],
 ['without-generic-push-contract',withholdPayloadContract('append_preserves_content','Nickel_crdt.Event_layer.push',1,['Nickel.Canonical.push_is_exact'],['  push_is_exact out item ops._2._1;'],canonicalView),'Canonical.append_preserves_content'],
 ['without-generic-membership-contract',withholdPayloadContract('append_preserves_content','Nickel_crdt.Event_layer.has_fact',2,['Nickel.EventGraph.fact_membership_is_exact'],['  Nickel.EventGraph.fact_membership_is_exact (Alloc.Vec.impl_1__as_slice out) (ops._1._1 item) ops;'],canonicalView),'Canonical.append_preserves_content'],
 ['without-generic-choice-loop',replaceInDeclaration('choose_is_fresh',canonicalChoiceLoop,'  ();',canonicalView),'Canonical.choose_is_fresh'],
 ['without-generic-canonical-loop',replaceInDeclaration('canonical_selects_whole_facts',canonicalWholeLoop,'  ();',canonicalView),'Canonical.canonical_selects_whole_facts'],
 ['without-generic-choice-contract',withholdPayloadContract('step_preserves_content','Nickel_crdt.Event_layer.choose_unseen',5,['Nickel.Canonical.choose_is_fresh'],['  choose_is_fresh input (Alloc.Vec.impl_1__as_slice out) ops;'],canonicalView),'Canonical.step_preserves_content'],
 ['without-generic-step-contract',withholdPayloadContract('canonical_selects_whole_facts','Nickel_crdt.Event_layer.canonical_step',2,['Nickel.Canonical.step_preserves_content'],['    step_preserves_content input out (Seq.length (Alloc.Vec.impl_1__as_slice out)) ops;'],canonicalView),'Canonical.canonical_selects_whole_facts'],
 ['without-register-canonical-policy',withholdPayloadContract('execute_preserves_exact_fact_contents','Nickel_crdt.Register.v_OPS',2,['Nickel.Register.register_canonical_values_are_exact'],['  register_canonical_values_are_exact ();']),'execute_preserves_exact_fact_contents'],
 ['without-register-canonical-content',withholdPayloadContract('execute_preserves_exact_fact_contents','Nickel_crdt.Event_layer.canonical',1,['Nickel.Canonical.canonical_preserves_exact_contents'],['  Nickel.Canonical.canonical_preserves_exact_contents (Alloc.Vec.impl_1__as_slice before.f_facts) Native.v_OPS._1;']),'execute_preserves_exact_fact_contents'],
 ['without-prepare-content',withholdPayloadContract('prepare_appends_exact_fact','Nickel_crdt.Event_layer.push',1,['Nickel.Canonical.push_is_exact'],['  Nickel.Canonical.push_is_exact before.f_facts offered Native.invalid;']),'prepare_appends_exact_fact'],
 ['without-plan-prepared-content',withholdPayloadContract('planned_adds_exact_fact','Nickel_crdt.Register.prepare',1,['Nickel.Register.prepare_appends_exact_fact'],['  prepare_appends_exact_fact before offered;']),'planned_adds_exact_fact'],
 ['without-receive-retention-plan',withholdPayloadContract('receive_added_retains_exact_facts','Nickel_crdt.Register.planned',3,['Nickel.Register.planned_adds_exact_fact'],['  planned_adds_exact_fact before offered;']),'receive_added_retains_exact_facts'],
 ['without-write-retention-installation',withholdPayloadContract('write_counted_retains_exact_facts','Nickel_crdt.Register.impl_Replica__write',1,['Nickel.Register.write_installs_successful_candidate'],['  write_installs_successful_candidate before key value;']),'write_counted_retains_exact_facts'],
 ['without-clock-loop-contract',replaceInDeclaration('next_lamport_is_maximum_successor',clockLoopLine,'  ();'),'next_lamport_is_maximum_successor'],
 ['without-added-clock-contract',withholdPayloadContract('receive_added_clock_is_maximum_successor','Nickel_crdt.Register.next_lamport',2,['Nickel.Register.next_lamport_is_maximum_successor'],['next_lamport_is_maximum_successor (Alloc.Vec.impl_1__as_slice basis);']),'receive_added_clock_is_maximum_successor'],
 ['without-added-clock-payload',withholdPayloadContract('receive_added_clock_is_maximum_successor','Nickel_crdt.Register.impl_Replica__receive',1,['Nickel.Register.receive_added_checks_payload'],['  receive_added_checks_payload before offered;']),'receive_added_clock_is_maximum_successor'],
 ['without-validation-byte-contract',withholdPayloadContract('validation_is_exact_basis_checks','Nickel_crdt.Register.bytes_equal',5,['Nickel.Register.bytes_equal_exact'],[
 'bytes_equal_exact (Alloc.Vec.impl_1__as_slice offered.f_payload.f_observed) (Alloc.Vec.impl_1__as_slice (Native.read_history (Alloc.Vec.impl_1__as_slice basis) (Alloc.Vec.impl_1__as_slice before.f_initial) offered.f_payload.f_key));',
 'bytes_equal_exact (Alloc.Vec.impl_1__as_slice offered.f_payload.f_value) (Alloc.Vec.impl_1__as_slice offered.f_payload.f_observed);']),'validation_is_exact_basis_checks'],
 ['without-payload-validation-contract',withholdPayloadContract('planned_checks_payload','Nickel_crdt.Register.validate',1,['Nickel.Register.validation_is_exact_basis_checks'],['  validation_is_exact_basis_checks before offered;']),'planned_checks_payload'],
 ['without-payload-planning-contract',withholdPayloadContract('planned_checks_payload','Nickel_crdt.Event_shell.plan',1,['Nickel.EventShell.planning_is_exact','Nickel.Register.shared_success_stages'],['  shared_success_stages before offered () Native.duplicate Native.validate Native.prepare Native.execute;']),'planned_checks_payload'],
 ['without-receive-payload-contract',withholdPayloadContract('receive_added_checks_payload','Nickel_crdt.Register.planned',3,['Nickel.Register.planned_checks_payload'],['  planned_checks_payload before offered;']),'receive_added_checks_payload'],
 ['without-added-publication-contract',withholdPayloadContract('receive_added_checks_payload','Nickel_crdt.Register.impl_Replica__receive',3,['Nickel.Register.receive_publication_is_exact'],['  receive_publication_is_exact before offered;']),'receive_added_checks_payload'],
 ['without-write-receive-publication',withholdWriteContract('receive_publication_is_exact'),'write_installs_successful_candidate'],
 ['without-write-receive-frame',withholdWriteContract('receive_preserves_private'),'write_installs_successful_candidate'],
 ['without-shared-planning-contract',replaceInDeclaration('shared_success_stages','    Tactics.prune "Nickel_crdt.Event_shell.plan";','    Tactics.prune "Nickel_crdt.Event_shell.plan";\n    Tactics.prune "Nickel.EventShell.planning_is_exact";',replaceInDeclaration('shared_success_stages','  Nickel.EventShell.planning_is_exact before offered context duplicate validate prepare execute;','  ();')),'shared_success_stages'],
 ['without-prepare-frame',replaceInDeclaration('prepare_preserves_private',' [SMTPat (Native.prepare () before offered)]','',replaceInDeclaration('planned_preserves_private','  prepare_preserves_private before offered;','  ();')),'planned_preserves_private'],
 ['without-execute-frame',replaceInDeclaration('execute_preserves_private',' [SMTPat (Native.execute () before)]',''),'planned_preserves_private'],
 ['without-receive-publication-frame',withholdReceivePublication(),'receive_preserves_private'],
 ['without-plan-private-frame',replaceInDeclaration('planned_preserves_private',' [SMTPat (Native.planned () before offered)]','',replaceInDeclaration('receive_preserves_private','  planned_preserves_private before offered;','  ();')),'receive_preserves_private'],
 ['without-winner-loop',replaceInDeclaration('winner_is_priority_maximum',loopLine,'  ();'),'winner_is_priority_maximum'],
 ['without-read-winner',replaceInDeclaration('read_history_selects_maximum','  winner_is_priority_maximum facts key;','  ();'),'read_history_selects_maximum'],
 ['without-publication-contract',replaceInDeclaration('receive_publication_is_exact','  Nickel.EventShell.borrowed_publication_is_exact before offered () Native.planned Native.Admission_Added Native.Admission_Duplicate;','  ();'),'receive_publication_is_exact'],
 ['without-noedit-byte-contract',replaceInDeclaration('equal_value_write_is_neutral','    Tactics.prune "Nickel_crdt.Register.bytes_equal";','    Tactics.prune "Nickel_crdt.Register.bytes_equal";\n    Tactics.prune "Nickel.Register.bytes_equal_exact";',replaceInDeclaration('equal_value_write_is_neutral','  bytes_equal_exact (Alloc.Vec.impl_1__as_slice value) (Alloc.Vec.impl_1__as_slice (Native.impl_Replica__read before key));','  ();')),'equal_value_write_is_neutral'],
];
for(const [name,changed,owner]of depModes){
 if(selected.length&&!selected.includes(name))continue;
 const generic=owner.startsWith('Canonical.')||owner.startsWith('LoopUtil.')||owner.startsWith('RegisterPast.')||owner.startsWith('RegisterHistory.')||owner.startsWith('RegisterValid.')||owner.startsWith('RegisterPublic.'),baseView=owner.startsWith('LoopUtil.')?loopView:owner.startsWith('Canonical.')?canonicalView:owner.startsWith('RegisterPast.')?pastView:owner.startsWith('RegisterHistory.')?historyView:owner.startsWith('RegisterValid.')?validView:owner.startsWith('RegisterPublic.')?publicView:view,ownerFile=generic?path.join(positive,'Nickel.'+owner.split('.')[0]+'.fst'):file;
 await fs.writeFile(path.join(output,name+'.fst'),changed);
 try{await put(ownerFile,changed);const r=await check(positive,rootsFor(owner),path.join(output,name+'.log'));const ordinary=hasOrdinaryTheoremRejection({status:r.status,log:r.log,theorem:generic?'Nickel.'+owner:'Nickel.Register.'+owner,view:changed});assert(ordinary,name+': checked callee dependence required');results.push({name,owner,status:r.status,ordinary,view:digest(changed),log:digest(r.log)});console.log('PASS '+name);}
 finally{await put(ownerFile,baseView);}
}
await fs.writeFile(path.join(output,'results.json'),JSON.stringify(results,null,2)+'\n');
console.log('checkpoint claims only; full register refinement/validity and SEC remain open');
