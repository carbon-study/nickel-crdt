// Actual edit/admit extraction: return paths, commit coherence and identity laws.
// This gate does not prove valid-fact acceptance, convergence or FugueMax.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {digest,run,verify,put} from './proof-cache.mjs';
import {hasOrdinaryTheoremRejection} from './negative-proof-evidence.mjs';
import {checkProofReform} from './proof-reform.mjs';
import {checkRemainingContracts} from './check-remaining-contracts.mjs';
import {checkPushContracts} from './check-push-contracts.mjs';
import {checkVectorContracts} from './check-vector-contracts.mjs';
import {checkIdentityContracts} from './check-identity-contracts.mjs';
import {checkContainmentContracts} from './check-containment-contracts.mjs';
import {checkAcceptedContracts} from './check-accepted-contracts.mjs';
import {checkSpecContracts} from './check-spec-contracts.mjs';
import {checkPrivateContracts} from './check-private-contracts.mjs';
import {checkSharedContracts} from './check-shared-contracts.mjs';
import {checkCommitContracts} from './check-commit-contracts.mjs';
import {checkPlanContracts} from './check-plan-contracts.mjs';
import {checkWriterContracts} from './check-writer-contracts.mjs';
import {checkNegativeProofEvidence} from './check-negative-proof-evidence.mjs';
import {checkScalarContracts} from './check-loop-contracts.mjs';
import {checkPastContracts} from './check-past-contracts.mjs';
import {checkCounterContracts} from './check-counter-contracts.mjs';
import {checkCacheSafety} from './check-cache-safety.mjs';
import './check-proof-reform.mjs';
checkNegativeProofEvidence();
const root=fileURLToPath(new URL('..',import.meta.url));
await checkProofReform(root);
const {NICKEL_HAX_BIN:hax,NICKEL_PROOF_FSTAR:fstar,NICKEL_HAX_SOURCE:models,NICKEL_FSTAR_MODEL_CACHE:modelCache}=process.env;
assert(hax&&fstar&&models&&modelCache,'use the locked .#proofs environment');
const output=process.argv[2];assert(output,'output directory required');
await fs.mkdir(output,{recursive:true});
const identity=JSON.parse(await fs.readFile(path.join(modelCache,'identity.json'),'utf8'));
assert.equal(identity.models,models);assert.equal(identity.fstar,fstar);
const views=new Map();
for(const name of ['Prelude','LoopUtil','Vector','EditAtomic','EditCommit','EditIdentity','EditAccepted','EditWellFormed','Spec','EditCausal','EditPast','EditPastTotal']) {
  const source=`proofs/${name}.lt`,view=`proofs/generated/Nickel.${name}.fst`;
  const code=await fs.readFile(path.join(root,view),'utf8');
  const receipt=(await fs.readFile(path.join(root,`proofs/generated/${name}.sha256`),'utf8')).trim().split('\n');
  assert.deepEqual(receipt,[digest(await fs.readFile(path.join(root,source)))+'  '+source,digest(code)+'  '+view]);
  assert(!/\b(?:admit|admit_smt_queries|assume|lax)\b/.test(code),'no authored admissions');
  views.set(`Nickel.${name}.fst`,code);
}
const original=await fs.readFile(path.join(root,'src/edit.rs'),'utf8');
const modes=['plan-skips-validation',"tree-publication-uses-private-writer","tree-publication-clears-private-counter","plan-clears-private-counter",'positive','plan-ignores-duplicate','plan-swallows-classifier-error','receive-plan-rewrites-counter','invalid-forgets-reason','writer-index-collides','native-push-discards-value','native-push-prepends','causal-validator-passes-empty','causal-accepts-missing','causal-call-passes-empty','causal-refuses-present','plan-interprets-uncanonical','scalar-count-loop-bypasses-check','scalar-accepts-invalid','scalar-call-passes-empty','scalar-refuses-valid','canonical-step-refuses','canonical-refuses','plan-keeps-old-tree','plan-passes-old-tree','order-key-ignores-writer','order-chooses-largest','order-discards-canonical','local-return-after','edit-call-passes-old-counter','edit-commit-ignores-counter','receive-error-corrupts-counter','edit-error-corrupts-counter','edit-success-reuses-counter',
  'local-return-gap','local-stale-tree','receive-success-counter','author-forgets-gap','receive-private-gate',
  'identity-forgets-gap','identity-accepts-conflict','identity-skips-later','identity-counter-range','identity-event-equality',
  'identity-scan-key','identity-birth-equality','identity-writer-equality',
  'accepted-reuses-member','accepted-wrong-canonical-push','accepted-publication-duplicates',
  'content-changes-whole-fact','content-omits-facts','past-drops-roots','past-invents-id','past-membership-always-false','past-skips-predecessors','past-skips-passes','past-refuses-closure'];
// Contract-dependency families run after the positive chain verifies. With no
// arguments (CI) every mode and every family runs. Development runs may select
// `positive-only`, `contracts:<family>` (implies the positive chain) and any
// mutation modes; `positive` keeps its meaning of positive plus all families.
// `shard:<i>/<n>` selects every mutation mode whose index k has k mod n == i
// (after the positive chain), so n shards together cover every mode exactly once.
// `contracts-except:<a>,<b>` runs every family not listed, so a CI job using it
// also picks up any family added later.
const families={past:checkPastContracts,remaining:checkRemainingContracts,counter:checkCounterContracts,push:checkPushContracts,vector:checkVectorContracts,
  scalar:checkScalarContracts,identity:checkIdentityContracts,writer:checkWriterContracts,plan:checkPlanContracts,containment:checkContainmentContracts,accepted:checkAcceptedContracts,spec:checkSpecContracts,private:checkPrivateContracts,shared:checkSharedContracts,commit:checkCommitContracts};
const args=process.argv.slice(3),familyRuns=new Set();let wantPositive=args.length===0,cacheSafety=args.length===0;
const mutations=[];
for(const arg of args) {
  if(arg==='positive'){wantPositive=true;for(const name of Object.keys(families))familyRuns.add(name);}
  else if(arg==='positive-only')wantPositive=true;
  else if(arg==='cache-safety'){wantPositive=true;cacheSafety=true;}
  else if(/^shard:\d+\/\d+$/.test(arg)){
    const [i,n]=arg.slice(6).split('/').map(Number);assert(n>0&&i<n,'shard index out of range '+arg);
    wantPositive=true;mutations.push(...modes.filter(mode=>mode!=='positive').filter((_,k)=>k%n===i));
  }
  else if(arg.startsWith('contracts-except:')){
    const skip=arg.slice(17).split(',');for(const name of skip)assert(Object.hasOwn(families,name),'unknown contract family '+name);
    wantPositive=true;for(const name of Object.keys(families))if(!skip.includes(name))familyRuns.add(name);
  }
  else if(arg.startsWith('contracts:')){const name=arg.slice(10);assert(Object.hasOwn(families,name),'unknown contract family '+name);wantPositive=true;familyRuns.add(name);}
  else {assert(modes.includes(arg),'unknown mode '+arg);mutations.push(arg);}
}
if(args.length===0){for(const name of Object.keys(families))familyRuns.add(name);mutations.push(...modes.filter(mode=>mode!=='positive'));}
// A fresh mutation workspace starts from the verified positive workspace: same
// views and caches, then fresh hax output replaces Nickel_crdt.Edit.fst. Its
// digest change (and F*'s own dependency check) forces the extracted module and
// every dependent proof to recheck; only modules independent of it are reused.
// Each mutation edits exactly one anchored site of the actual Rust source.
function prepareMutation(mode) {
  const scopes={
'past-refuses-closure':'fn past(', 'past-skips-passes':'fn past(', 'past-skips-predecessors':'fn extend_past(', 'past-drops-roots':'fn past(', 'past-invents-id':'fn extend_past(', 'past-membership-always-false':'fn has_event(',
'plan-skips-validation':'fn plan(',
"tree-publication-uses-private-writer":"fn with_tree(",
"tree-publication-clears-private-counter":"fn with_tree(",
"plan-clears-private-counter":"fn plan(",
'plan-ignores-duplicate':'fn plan(', 'plan-swallows-classifier-error':'fn plan(', 'receive-plan-rewrites-counter':'pub fn receive(', 'invalid-forgets-reason':'fn invalid(', 'writer-index-collides':'fn writer_index(', 'native-push-discards-value':'fn push<T>','native-push-prepends':'fn push<T>','causal-validator-passes-empty':'fn validate_new(','causal-accepts-missing':'fn validate_after(', 'causal-call-passes-empty':'fn past(', 'causal-refuses-present':'fn validate_after(','plan-interprets-uncanonical':'fn plan(','scalar-count-loop-bypasses-check':'fn validate_new(','scalar-accepts-invalid':'fn validate_scalars(', 'scalar-refuses-valid':'fn validate_scalars(', 'scalar-call-passes-empty':'fn validate_new(','canonical-step-refuses':'fn canonical_step(', 'canonical-refuses':'fn canonical(','plan-keeps-old-tree':'fn with_tree(', 'plan-passes-old-tree':'fn plan(','order-key-ignores-writer':'fn event_lt(','order-chooses-largest':'fn choose_unseen(', 'order-discards-canonical':'fn plan(','edit-commit-ignores-counter':'fn with_counter(', 'edit-success-reuses-counter':'fn next_counter_after(', 'content-changes-whole-fact':'fn clone_selected_fact(', 'content-omits-facts':'fn canonical(', 'accepted-reuses-member':'fn choose_unseen(', 'accepted-wrong-canonical-push':'fn canonical_step(', 'accepted-publication-duplicates':'fn with_tree('};
  const start=original.indexOf(scopes[mode]??(mode==='identity-writer-equality'?'impl PartialEq for Writer':mode==='identity-birth-equality'?'impl PartialEq for BirthId':mode==='identity-event-equality'?'impl PartialEq for EventId':mode==='identity-forgets-gap'?'fn fact_equal(':mode.startsWith('identity-')?'fn duplicate(':mode==='receive-private-gate'?'fn plan(':mode.startsWith('receive')?'pub fn receive(':'pub fn edit('));assert(start>=0);
  const edits={
'plan-skips-validation':['Self::validate_new(&self.facts, self.limits, fact)?;', 'let _ = Self::validate_new(&self.facts, self.limits, fact);'],
"tree-publication-uses-private-writer":["self.tree = tree;","if self.writer.is_some() { self.tree = tree; }"],
"tree-publication-clears-private-counter":["self.tree = tree;","self.tree = tree; self.next_counter = 0;"],
"plan-clears-private-counter":["let mut next = self.clone();","let mut next = self.clone(); next.next_counter = 0;"],

    'plan-ignores-duplicate':['if Self::duplicate(&self.facts, fact)? {','if Self::duplicate(&self.facts, fact)? && false {'],
    'plan-swallows-classifier-error':['if Self::duplicate(&self.facts, fact)? {','if match Self::duplicate(&self.facts, fact) { Ok(found) => found, Err(_) => false } {'],
    'receive-plan-rewrites-counter':['match self.plan(fact) {','let mut offered = (*fact).clone(); offered.id.counter = 1; match self.plan(&offered) {'],
    'native-push-discards-value':['xs.push(value);','let _ = value;'],
    'native-push-prepends':['xs.push(value);','xs.insert(0, value);'],
    'past-refuses-closure':['Ok(selected)', 'Err(Error::Internal)'],
    'past-skips-passes':['for _ in 0..facts.len() {', 'for _ in 0..0 {'],
    'past-skips-predecessors':['if has_event(&selected, fact.id) {', 'if false {'],
    'past-drops-roots':['let mut selected = after.to_vec();','let mut selected = Vec::new();'],
    'past-invents-id':['push(&mut selected, id)?;', 'push(&mut selected, EventId { writer: Writer::Alice, counter: 0 })?;'],
    'past-membership-always-false':['if ids[i] == id {','if false {'],
    'causal-validator-passes-empty':['let selected = past(&facts, &fact.after)?;', 'let selected = past(&facts, &[])?;'],
    'causal-accepts-missing':['if !has_fact(facts, after[i]) {','if false {'],
    'causal-call-passes-empty':['validate_after(facts, after)?;', 'validate_after(facts, &[])?;'],
    'causal-refuses-present':['Ok(())','Err(Error::Missing)'],
    'scalar-count-loop-bypasses-check':['births = add(births, facts[i].insert.len())?;', 'births = add(births, facts[i].insert.len())?; if births > 0 { return Ok(()); }'],
    'scalar-accepts-invalid':['if scalar > 0x10ffff || (scalar >= 0xd800 && scalar <= 0xdfff) {', 'if false {'],
    'scalar-call-passes-empty':['validate_scalars(&fact.insert)?;', 'validate_scalars(&[])?;'],
    'scalar-refuses-valid':['Ok(())', 'Err(invalid(Invalid::Scalar))'],
    'canonical-step-refuses':['Ok(out)', 'Err(Error::Internal)'],
    'canonical-refuses':['Ok(out)', 'Err(Error::Internal)'],
    'plan-keeps-old-tree':['self.tree = tree;', 'let _ = tree;'],
    'plan-passes-old-tree':['Ok(Some(next.with_tree(tree)))', 'Ok(Some(next.with_tree(self.tree.clone())))'],
    'plan-interprets-uncanonical':['next.facts = canonical(&next.facts)?;\n        let tree = interpret(&next.facts)?;', 'let tree = interpret(&next.facts)?;\n        next.facts = canonical(&next.facts)?;'],
    'order-chooses-largest':['if event_lt(facts[j].id, facts[k].id) {', 'if event_lt(facts[k].id, facts[j].id) {'],
    'order-key-ignores-writer':['writer_index(a.writer) < writer_index(b.writer)\n        || (a.writer == b.writer && a.counter < b.counter)', 'a.counter < b.counter'],
    'order-discards-canonical':['next.facts = canonical(&next.facts)?;', 'let _ = canonical(&next.facts)?;'],
    'edit-call-passes-old-counter':['next = next.with_counter(next_counter);', 'next = next.with_counter(self.next_counter);'],
    'local-return-after':['(next, Ok(Local::Authored(fact)))','{ let mut changed = fact; changed.after = Vec::new(); (next, Ok(Local::Authored(changed))) }'],
    'edit-commit-ignores-counter':['self.next_counter = counter;', 'self.next_counter = self.next_counter;'],
    'content-changes-whole-fact':['fact.clone()', 'let mut changed = fact.clone(); changed.gap = None; changed'],
    'content-omits-facts':['for _ in 0..facts.len() {', 'for _ in 0..0 {'],
    'accepted-reuses-member':['if !has_fact(out, facts[j].id) {','if true {'],
    'accepted-wrong-canonical-push':['push(&mut out, clone_selected_fact(&facts[i]))?;','push(&mut out, clone_selected_fact(&facts[0]))?;'],
    'accepted-publication-duplicates':['self.tree = tree;','self.tree = tree; if !self.facts.is_empty() && self.facts.len() < usize::MAX { let copy = self.facts[0].clone(); self.facts.push(copy); }'],
    'invalid-forgets-reason':['Error::Invalid(reason)','Error::Invalid(Invalid::Counter)'],
    'writer-index-collides':['Writer::Bo => 1','Writer::Bo => 0'],
    'identity-writer-equality':['writer_index(*self) == writer_index(*other)','writer_index(*self) == writer_index(*self)'],
    'identity-birth-equality':['self.event == other.event && self.index == other.index','self.event == other.event'],
    'identity-scan-key':['if old.id == fact.id {','if old.id.counter == fact.id.counter {'],
    'identity-event-equality':['self.writer == other.writer && self.counter == other.counter','self.writer == other.writer'],
    'identity-forgets-gap':['&& left.gap == right.gap','&& true'],
    'identity-accepts-conflict':['return if fact_equal(old, fact) {','return if fact_equal(old, fact) || old.id == fact.id {'],
    'identity-skips-later':['for i in 0..facts.len() {','for i in 0..0 {'],
    'identity-counter-range':['if fact.id.counter == 0 || fact.id.counter > MAX_COUNTER {','if false {'],
    'receive-error-corrupts-counter':['Err(error) => (self, Err(error)),','Err(error) => { let mut damaged = self; damaged.next_counter = 0; (damaged, Err(error)) },'],
    'edit-error-corrupts-counter':['Err(error) => (self, Err(error)),','Err(error) => { let mut damaged = self; damaged.next_counter = 0; (damaged, Err(error)) },'],
    'edit-success-reuses-counter':['Ok(counter + 1)','Ok(counter)'],
    'local-return-gap':['(next, Ok(Local::Authored(fact)))','{ let mut changed = fact; changed.gap = Some(0); (next, Ok(Local::Authored(changed))) }'],
    'local-stale-tree':['next = next.with_counter(next_counter);','next = next.with_counter(next_counter); next.tree = self.tree.clone();'],
    'receive-success-counter':['Ok(Some(next)) => (next, Ok(Admission::Added)),','Ok(Some(mut next)) => { next.next_counter = 0; (next, Ok(Admission::Added)) },'],
    'author-forgets-gap':['Some(gap)','Some(0)'],
    'receive-private-gate':['Self::validate_new(&self.facts, self.limits, fact)?;', 'Self::validate_new(&self.facts, self.limits, fact)?; if self.writer.is_none() { return Err(Error::Missing); }'],
  };
  assert(start>=0,'mutation scope not found: '+mode);
  assert(Object.hasOwn(edits,mode),'mutation without a registered edit: '+mode);
  const [needle,replacement]=edits[mode];const at=original.indexOf(needle,start);assert(at>=start,'mutation anchor not found in scope: '+mode);
  if(mode.startsWith('native-push-')) { const end=original.indexOf('\n}',start)+2;assert(end>start&&at<end);assert.equal(original.slice(start,end).split(needle).length,2,'one actual push-body anchor'); }
  if(['plan-skips-validation','tree-publication-uses-private-writer','tree-publication-clears-private-counter','plan-clears-private-counter','plan-ignores-duplicate','plan-swallows-classifier-error','receive-plan-rewrites-counter'].includes(mode)) {
    const next=/\n    (?:pub )?fn /.exec(original.slice(start));
    const end=next?start+next.index:original.length;
    assert(at<end);assert.equal(original.slice(start,end).split(needle).length,2,'one actual planner/caller anchor');
  }
  const mutant=original.slice(0,at)+original.slice(at).replace(needle,replacement);
  assert.notEqual(mutant,original);
  return mutant;
}
const theorems={
'plan-skips-validation':'EditAtomic.successful_plan_requires_validation',
"tree-publication-uses-private-writer":"EditCommit.tree_publication_respects_shared",
"tree-publication-clears-private-counter":"EditCommit.tree_publication_keeps_private",
"plan-clears-private-counter":"EditCommit.plan_preserves_private_state",

  'plan-ignores-duplicate':'EditAtomic.plan_preserves_duplicate_result',
  'plan-swallows-classifier-error':'EditAtomic.plan_preserves_duplicate_result',
  "receive-plan-rewrites-counter":"EditCommit.receive_uses_plan",
  'native-push-discards-value':'EditAccepted.push_result_is_exact',
  'native-push-prepends':'EditAccepted.push_result_is_exact',
  'causal-validator-passes-empty':'EditWellFormed.successful_validation_has_direct_dependencies',
  'causal-accepts-missing':'EditWellFormed.dependency_validation_is_sound',
  'past-refuses-closure':'EditPastTotal.fitting_closed_history_computes_past',
  'past-skips-passes':'EditPast.past_stays_in_closed_set',
  'past-skips-predecessors':'EditPast.extend_past_covers_predecessors',
  'past-drops-roots':'EditPast.past_stays_in_closed_set',
  'past-invents-id':'EditPast.extend_past_preserves',
  'past-membership-always-false':'EditPast.event_membership_is_exact',
  'causal-call-passes-empty':'EditWellFormed.successful_past_has_direct_dependencies',
  'causal-refuses-present':'EditWellFormed.present_dependencies_pass_guard',
  'scalar-count-loop-bypasses-check':'EditWellFormed.successful_validation_has_valid_scalars',
  'scalar-accepts-invalid':'EditWellFormed.scalar_validation_is_sound',
  'scalar-call-passes-empty':'EditWellFormed.successful_validation_has_valid_scalars',
  'scalar-refuses-valid':'EditWellFormed.valid_scalar_input_succeeds',
  'canonical-step-refuses':'EditAccepted.canonical_step_succeeds',
  'canonical-refuses':'EditAccepted.canonical_uses_complete_range',
  'plan-keeps-old-tree':'EditAccepted.tree_installation_installs_tree',
  'plan-passes-old-tree':'EditAccepted.plan_publishes_interpretation',
  'plan-interprets-uncanonical':'EditAccepted.plan_publishes_interpretation',
  'order-chooses-largest':'EditAccepted.selected_id_is_least',
  'order-key-ignores-writer':'EditAccepted.event_order_is_key_order',
  'order-discards-canonical':'EditAccepted.plan_publishes_canonical_facts',
  'edit-call-passes-old-counter':'EditAtomic.authored_edit_advances_once',
  'local-return-after':'EditCommit.authored_fact_replays_same_commit',
  'edit-commit-ignores-counter':'EditAtomic.counter_installation_is_exact',
  'content-changes-whole-fact':'EditAccepted.selected_fact_is_exact',
  'content-omits-facts':'EditAccepted.canonical_uses_complete_range',
  'accepted-reuses-member':'EditAccepted.selected_id_is_unseen',
  'accepted-wrong-canonical-push':'EditAccepted.canonical_step_preserves_unique',
  'accepted-publication-duplicates':'EditAccepted.tree_installation_preserves_facts',
  'invalid-forgets-reason':'EditIdentity.invalid_is_exact',
  'writer-index-collides':'EditIdentity.writer_index_is_exact',
  'identity-writer-equality':'EditIdentity.writer_equality_exact',
  'identity-birth-equality':'EditIdentity.birth_equality_exact',
  'identity-scan-key':'EditIdentity.duplicate_matches_lookup',
  'identity-event-equality':'EditIdentity.event_equality_exact',
  'identity-forgets-gap':'EditIdentity.fact_equality_exact',
  'identity-accepts-conflict':'EditIdentity.duplicate_matches_lookup',
  'identity-skips-later':'EditIdentity.duplicate_matches_lookup',
  'identity-counter-range':'EditIdentity.duplicate_matches_lookup',
  'receive-error-corrupts-counter':'EditAtomic.receive_rejection_unchanged',
  'edit-error-corrupts-counter':'EditAtomic.edit_rejection_or_empty_unchanged',
  'edit-success-reuses-counter':'EditAtomic.counter_result_advances_once',
  'local-return-gap':'EditCommit.authored_fact_binds_request',
  'local-stale-tree':'EditCommit.authored_fact_replays_same_commit',
  "receive-success-counter":"EditCommit.receive_uses_plan",
  'author-forgets-gap':'EditCommit.authored_fact_binds_request',
  "receive-private-gate":"EditCommit.plan_ignores_private_state",
};
// Registration consistency: every selected mutation must have an anchored edit and a
// named owning theorem before any native test, extraction or compiler starts.
const prepared=new Map();
for(const mode of mutations) {
  assert(Object.hasOwn(theorems,mode),'mutation without an owning theorem: '+mode);
  assert(views.has('Nickel.'+theorems[mode].split('.')[0]+'.fst'),'owning theorem outside the checked views: '+mode);
  prepared.set(mode,prepareMutation(mode));
}
const fresh=async proof=>{try{await fs.access(path.join(proof,'sources.json'));return false;}catch{return true;}};
let positive,positiveProof;
for(const mode of [...(wantPositive?['positive']:[]),...mutations]) {
  const work=path.join(root,'.cache','edit-proofs',mode),crate=path.join(work,'crate'),proof=path.join(work,'proof');
  await fs.mkdir(crate,{recursive:true});
  if(positiveProof&&await fresh(proof))await fs.cp(positiveProof,proof,{recursive:true,preserveTimestamps:true});
  await fs.mkdir(proof,{recursive:true});
  for(const name of ['Cargo.toml','Cargo.lock','src','tests','proof-smoke'])await fs.cp(path.join(root,name),path.join(crate,name),{recursive:true});
  if(mode!=='positive') {
    await fs.writeFile(path.join(crate,'src/edit.rs'),prepared.get(mode));
  }
  const env={...process.env,CARGO_TARGET_DIR:path.join(root,'target','edit-proof-check')};
  const nativeArgs=['test','--offline','--locked','-p','nickel-crdt',...(mode.startsWith('past-')?['--lib','causal_basis_tests']:['--test','edit_admit'])];
  const native=run('edit native '+mode,'cargo',nativeArgs,crate,{env});
  await fs.writeFile(path.join(output,mode+'.native.log'),native.log);
  if(mode==='positive')assert.equal(native.status,0,native.log);
  else {assert.equal(native.status,101,native.log);assert.match(native.log,/test result: FAILED/);}
  const extract=path.join(work,'extract');await fs.rm(extract,{recursive:true,force:true});await fs.mkdir(extract,{recursive:true});
  const extracted=run('edit hax '+mode,hax,['-C','--offline','--locked','-p','nickel-crdt',';','into','--output-dir',extract,'-i','-** +nickel_crdt::edit::**::receive +nickel_crdt::edit::**::edit +nickel_crdt::edit::**::new','fstar'],crate,{env});
  await fs.writeFile(path.join(output,mode+'.hax.log'),extracted.log);
  assert.equal(extracted.status,0,extracted.log);
  // Install the fresh extraction inventory: remove project sources that are neither
  // authored views nor produced by this extraction (e.g. left by a seeded copy).
  const inventory=(await fs.readdir(extract)).filter(name=>/\.fsti?$/.test(name));
  assert(inventory.includes('Nickel_crdt.Edit.fst'),'extraction did not produce Nickel_crdt.Edit.fst');
  for(const name of await fs.readdir(proof))if(/\.fsti?$/.test(name)&&!views.has(name)&&!inventory.includes(name))await fs.rm(path.join(proof,name));
  for(const name of inventory)await put(path.join(proof,name),await fs.readFile(path.join(extract,name),'utf8'));
  const code=await fs.readFile(path.join(proof,'Nickel_crdt.Edit.fst'),'utf8');
  assert.match(code,/let impl_Replica__receive /);assert.match(code,/let impl_Replica__edit/);assert.match(code,/let impl_Replica__new/);
  // Preserve an ordinary call at the identity boundary: PartialEq operators
  // are structurally lowered by the pinned backend, ignoring custom bodies.
  const scan=code.slice(code.indexOf('let impl_Replica__duplicate '),code.indexOf('let impl_Replica__validate_new '));
  assert.match(scan,/fact_equal old fact/);
  assert(!/\b(?:admit|assume|admit_smt_queries)\b/.test(code),'no assumptions in extracted project code');
  if(mode==='positive') {
    const committed=await fs.readFile(path.join(root,'proofs/generated/hax/Nickel_crdt.Edit.fst'),'utf8');
    assert(code===committed,'fresh hax edit extraction differs from proofs/generated/hax/Nickel_crdt.Edit.fst; review and refresh the committed translation');
    positive=code;
  } else assert.notEqual(code,positive);
  for(const [name,code] of views)await put(path.join(proof,name),code);
  // What this workspace last recorded for the extraction decides whether it must be
  // recompiled now: changed (seeded, fresh or edited) must recompile; unchanged may be reused.
  let recorded={};try{recorded=JSON.parse(await fs.readFile(path.join(proof,'sources.json'),'utf8'));}catch(e){if(e.code!=='ENOENT')throw e;}
  const extractionChanged=recorded['Nickel_crdt.Edit.fst']!==digest(code);
  // Counter calculation/installation/wiring controls need only their owning module. The positive path still
  // checks both the public Spec surface and the existing ghost causal-rank family.
  const proofRoot=mode==='positive'?'Nickel.Spec.fst':mode==='past-refuses-closure'?'Nickel.EditPastTotal.fst':mode.startsWith('past-')?'Nickel.EditPast.fst':['edit-success-reuses-counter','edit-commit-ignores-counter','edit-call-passes-old-counter'].includes(mode)?'Nickel.EditAtomic.fst':'Nickel.EditWellFormed.fst';
  const checked=await verify({dir:proof,roots:(mode==='positive'?['Nickel.Spec.fst','Nickel.EditCausal.fst','Nickel.EditPastTotal.fst']:[proofRoot]).map(name=>path.join(proof,name)),fstar,models,modelCache});
  await fs.writeFile(path.join(output,mode+'.proof.log'),checked.log);
  if(mode==='positive') {
    assert.equal(checked.status,0,checked.log);
    positiveProof=proof;
    // Each family edits its own copy of the verified positive workspace, so the
    // positive cache stays clean and families cannot see each other's probes.
    for(const [name,check] of Object.entries(families))if(familyRuns.has(name)) {
      const copy=path.join(root,'.cache','edit-proofs','contracts-'+name,'proof');
      await fs.rm(copy,{recursive:true,force:true});
      await fs.cp(proof,copy,{recursive:true,preserveTimestamps:true});
      await check({proof:copy,output,fstar,models,modelCache});
    }
    if(cacheSafety)await checkCacheSafety({positiveProof:proof,workRoot:path.join(root,'.cache','edit-proofs'),output,fstar,models,modelCache});
    await fs.copyFile(path.join(proof,'Nickel_crdt.Edit.fst'),path.join(output,'Nickel_crdt.Edit.fst'));
  } else {
    assert.equal(checked.status,2,'require ordinary proof rejection, not extraction failure/timeout');
    const theorem='Nickel.'+theorems[mode],file='Nickel.'+theorems[mode].split('.')[0]+'.fst';
    // A reused cache must never stand in for checking the changed program. The owning
    // proof module always compiles here (a rejected module leaves no checked result);
    // the extraction must compile whenever it differs from this workspace's last record.
    // An unchanged extraction in a warm rerun of the same mode may be legitimately reused.
    for(const changed of [...(extractionChanged?['Nickel_crdt.Edit.fst']:[]),file])
      assert(checked.modules.includes(changed),changed+' was not compiled for '+mode+': '+(checked.modules.join(',')||'nothing'));
    assert(hasOrdinaryTheoremRejection({status:checked.status,log:checked.log,theorem,view:views.get(file)}),
      'require a final ordinary named query rejection and a semantic error in its source declaration: '+checked.log);
  }
  console.log(`PASS ${mode}: native and unchanged actual-Rust theorem ${mode==='positive'?'verified':'reject the mutation'}`);
}
