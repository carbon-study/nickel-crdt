import {checkEventContracts} from './check-event-contracts.mjs';
import {checkOperationContracts} from './check-operation-contracts.mjs';
import {checkReplayContracts} from './check-replay-contracts.mjs';
import {itemSpan,scopedAnchor,checkMutationScopeControls} from './mutation-scope.mjs';
import {checkBasisContracts} from './check-basis-contracts.mjs';
// Actual edit/admit extraction: return paths, commit coherence and identity laws.
// This gate does not prove valid-fact acceptance, convergence or FugueMax.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {mkdirSync} from 'node:fs';
import {digest,holdLock,runAsync,verify,put} from './proof-cache.mjs';
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
import {checkScheduleContracts} from './check-schedule-contracts.mjs';
import {checkPastContracts} from './check-past-contracts.mjs';
import {checkCounterContracts} from './check-counter-contracts.mjs';
import {checkCacheSafety} from './check-cache-safety.mjs';
const root=fileURLToPath(new URL('..',import.meta.url));
// One invocation per checkout. Mode workspaces (.cache/edit-proofs), Cargo targets
// (target/edit-proof-check) and the positive seed are shared mutable state, so an
// overlapping invocation is rejected before it writes any of them. This process
// takes the lock itself and every command it starts inherits it (holdLock), so a
// killed runner's surviving writers keep the checkout locked until they exit.
// Never delete the lock file: its inode is the lock.
const lock=path.join(root,'.cache','edit-proofs.lock');
mkdirSync(path.dirname(lock),{recursive:true});
if(!holdLock(lock)) {
  console.error('another check-edit-proofs invocation holds '+lock+'; overlapping runs would share workspaces and extractions');
  process.exit(75);
}
// Self-checks run once the lock is held.
await import('./check-proof-reform.mjs');
checkNegativeProofEvidence();
await checkProofReform(root);
const sourceFiles=['src/edit.rs','src/event_layer.rs','src/event_shell.rs'];
const original=Object.fromEntries(await Promise.all(sourceFiles.map(async name=>[name,await fs.readFile(path.join(root,name),'utf8')])));
const modes=['plan-skips-validation',"tree-publication-uses-private-writer","tree-publication-clears-private-counter","plan-clears-private-counter",'positive','plan-ignores-duplicate','plan-swallows-classifier-error','receive-plan-rewrites-counter','invalid-forgets-reason','writer-index-collides','native-push-discards-value','native-push-prepends','causal-validator-passes-empty','causal-accepts-missing','causal-call-passes-empty','causal-refuses-present','plan-interprets-uncanonical','scalar-validation-bypasses-on-history','scalar-accepts-invalid','scalar-call-passes-empty','scalar-refuses-valid','canonical-step-refuses','canonical-refuses','plan-keeps-old-tree','plan-passes-old-tree','order-key-ignores-writer','order-chooses-largest','order-discards-canonical','local-return-after','edit-call-passes-old-counter','edit-commit-ignores-counter','receive-error-corrupts-counter','edit-error-corrupts-counter','edit-success-reuses-counter',
  'local-return-gap','local-stale-tree','receive-success-counter','author-forgets-gap','receive-private-gate',
  'identity-forgets-gap','identity-accepts-conflict','identity-skips-later','identity-counter-range','identity-event-equality',
  'identity-scan-key','identity-birth-equality','identity-writer-equality',
  'accepted-reuses-member','accepted-wrong-canonical-push','accepted-publication-duplicates',
  'content-changes-whole-fact','content-omits-facts','past-drops-roots','past-invents-id','past-membership-always-false','past-skips-predecessors','past-skips-passes','past-refuses-closure','duplicate-scan-skips-pairs','scheduler-ready-skips-dependency','scheduler-reselects-done','scheduler-refuses-ready','scheduler-checks-empty-after','scheduler-records-wrong-id','scheduler-stops-early','scheduler-erases-wrong-trace','scheduler-invents-bookkeeping-error','basis-includes-unselected','basis-omits-selected','basis-event-ignores-roots','replay-nodes-skip-first','replay-nodes-reverse','replay-groups-include-all','replay-groups-skip-all','replay-context-passes-empty','replay-context-invents-error','replay-context-contaminates-basis','scheduler-forgets-completed-tree'];
modes.push('plan-interprets-uncanonical-call', ...["shared-plan-skips-validation","shared-plan-ignores-duplicate","shared-plan-swallows-classifier-error","identity-call-passes-empty","identity-call-ignores-payload","past-membership-call-passes-empty","scheduler-readiness-call-passes-empty","scheduler-choice-call-passes-empty"]);
modes.push('text-policy-swaps-eq-lt','graph-policy-swaps-eq-lt','admission-policy-swaps-errors');
// Contract-dependency families run after the positive chain verifies. With no
// arguments (CI) every mode and every family runs. Development runs may select
// `positive-only`, `contracts:<family>` (implies the positive chain) and any
// mutation modes; `positive` keeps its meaning of positive plus all families.
// `shard:<i>/<n>` selects every mutation mode whose index k has k mod n == i
// (after the positive chain), so n shards together cover every mode exactly once.
// `contracts-except:<a>,<b>` runs every family not listed, so a CI job using it
// also picks up any family added later. `jobs:<n>` (default 1) checks up to n
// selected mutation modes concurrently, after the positive chain and its
// families; it selects nothing by itself.
const families={event:checkEventContracts,operation:checkOperationContracts,replay:checkReplayContracts,basis:checkBasisContracts,schedule:checkScheduleContracts,past:checkPastContracts,remaining:checkRemainingContracts,counter:checkCounterContracts,push:checkPushContracts,vector:checkVectorContracts,
  scalar:checkScalarContracts,identity:checkIdentityContracts,writer:checkWriterContracts,plan:checkPlanContracts,containment:checkContainmentContracts,accepted:checkAcceptedContracts,spec:checkSpecContracts,private:checkPrivateContracts,shared:checkSharedContracts,commit:checkCommitContracts};
const jobArgs=process.argv.slice(3).filter(arg=>arg.startsWith('jobs:')),args=process.argv.slice(3).filter(arg=>!arg.startsWith('jobs:'));
assert(jobArgs.length<=1&&jobArgs.every(arg=>/^jobs:[1-9]\d*$/.test(arg)),'use at most one jobs:<n> with n >= 1');
const jobs=jobArgs.length?Number(jobArgs[0].slice(5)):1;
const familyRuns=new Set();let wantPositive=args.length===0,cacheSafety=args.length===0;
const mutations=[];
for(const arg of args) {
  if(arg==='gatepreflight'){}
  else if(arg==='positive'){wantPositive=true;for(const name of Object.keys(families))familyRuns.add(name);}
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
  else {assert(modes.includes(arg),'unknown mode '+arg);if(arg.startsWith('basis-')||arg.startsWith('replay-')||arg==='scheduler-forgets-completed-tree')wantPositive=true;mutations.push(arg);}
}
assert(!args.includes('gatepreflight')||args.length===1,'gatepreflight is an exclusive preparation-only mode');
if(args.length===0){for(const name of Object.keys(families))familyRuns.add(name);mutations.push(...modes.filter(mode=>mode!=='positive'));}
// A fresh mutation workspace starts from the verified positive workspace: same
// views and caches, then fresh hax output replaces Nickel_crdt.Edit.fst. Its
// digest change (and F*'s own dependency check) forces the extracted module and
// every dependent proof to recheck; only modules independent of it are reused.
// Each mutation edits exactly one anchored site of the actual Rust source.
// Each row is [mode, source owner, item header, anchor, replacement]. This is
// the sole mutation definition table; the lookup below is only its index.
const mutationDefinitions=[
  ["plan-skips-validation","src/edit.rs","fn plan_validate(","Replica::validate_new(&before.facts, fact)","Ok(())"],
  ["tree-publication-uses-private-writer","src/edit.rs","fn with_tree(","self.tree = tree;","if self.writer.is_some() { self.tree = tree; }"],
  ["tree-publication-clears-private-counter","src/edit.rs","fn with_tree(","self.tree = tree;","self.tree = tree; self.next_counter = 0;"],
  ["plan-clears-private-counter","src/edit.rs","fn plan_prepare(","push(&mut next.facts, fact.clone())?;","next.next_counter = 0; push(&mut next.facts, fact.clone())?;"],
  ["plan-ignores-duplicate","src/edit.rs","fn plan_duplicate(","Replica::duplicate(&before.facts, fact)","let _ = Replica::duplicate(&before.facts, fact)?; Ok(false)"],
  ["plan-swallows-classifier-error","src/edit.rs","fn plan_duplicate(","Replica::duplicate(&before.facts, fact)","match Replica::duplicate(&before.facts, fact) { Ok(found) => Ok(found), Err(_) => Ok(false) }"],
  ["receive-plan-rewrites-counter","src/edit.rs","fn receive_plan(","before.plan(fact)","let mut offered = fact.clone(); offered.id.counter = 1; before.plan(&offered)"],
  ["invalid-forgets-reason","src/edit.rs","fn invalid(","Error::Invalid(reason)","Error::Invalid(Invalid::Counter)"],
  ["writer-index-collides","src/edit.rs","fn writer_index(","w.0","0"],
  ["native-push-discards-value","src/event_layer.rs","fn push<","xs.push(value);","let _ = value;"],
  ["native-push-prepends","src/event_layer.rs","fn push<","xs.push(value);","xs.insert(0, value);"],
  ["causal-validator-passes-empty","src/edit.rs","fn validate_new(","&TEXT_OPS)","&crate::event_layer::event_ops(crate::event_layer::graph_ops(fact_id, |_| &[], same_event_id, earlier_event_id, clone_selected_fact, fact_equal, internal_error, missing_error), required_predecessor, forbidden_ancestor, duplicate_dependency_error, predecessor_error))"],
  ["causal-accepts-missing","src/event_layer.rs","fn validate_after<","if !has_fact(facts, &after[i], ops) {","if false {"],
  ["causal-call-passes-empty","src/event_layer.rs","fn past<","validate_after(facts, after_ids, ops)?;","validate_after(facts, &[], ops)?;"],
  ["causal-refuses-present","src/event_layer.rs","fn validate_after<","Ok(())","Err(missing())"],
  ["plan-interprets-uncanonical","src/event_shell.rs","fn plan<","let next = prepare(context, next, fact)?;\n    let next = execute(context, next)?;","let next = execute(context, next)?;\n    let next = prepare(context, next, fact)?;"],
  ["scalar-validation-bypasses-on-history","src/edit.rs","fn validate_new(","validate_scalars(&fact.insert)?;","if facts.is_empty() { validate_scalars(&fact.insert)?; }"],
  ["scalar-accepts-invalid","src/edit.rs","fn validate_scalars(","if scalar > 0x10ffff || (scalar >= 0xd800 && scalar <= 0xdfff) {","if false {"],
  ["scalar-call-passes-empty","src/edit.rs","fn validate_new(","validate_scalars(&fact.insert)?;","validate_scalars(&[])?;"],
  ["scalar-refuses-valid","src/edit.rs","fn validate_scalars(","Ok(())","Err(invalid(Invalid::Scalar))"],
  ["canonical-step-refuses","src/event_layer.rs","fn canonical_step<","Ok(out)","Err(internal())"],
  ["canonical-refuses","src/event_layer.rs","fn canonical<","Ok(out)","Err((ops.1.0)())"],
  ["plan-keeps-old-tree","src/edit.rs","fn with_tree(","self.tree = tree;","let _ = tree;"],
  ["plan-passes-old-tree","src/edit.rs","fn plan_execute(","Ok(next.with_tree(tree))","Ok(next.clone().with_tree(next.tree.clone()))"],
  ["order-key-ignores-writer","src/edit.rs","fn event_lt(","writer_index(a.writer) < writer_index(b.writer)\n        || (a.writer == b.writer && a.counter < b.counter)","a.counter < b.counter"],
  ["order-chooses-largest","src/event_layer.rs","fn choose_unseen<","if id_lt(&id(&facts[j]), &id(&facts[k])) {","if id_lt(&id(&facts[k]), &id(&facts[j])) {"],
  ["order-discards-canonical","src/edit.rs","fn plan_prepare(","next.facts = canonical(&next.facts)?;","let _ = canonical(&next.facts)?;"],
  ["local-return-after","src/edit.rs","pub fn edit(","(next, Ok(Local::Authored(fact)))","{ let mut changed = fact; changed.after = Vec::new(); (next, Ok(Local::Authored(changed))) }"],
  ["edit-call-passes-old-counter","src/edit.rs","pub fn edit(","next = next.with_counter(next_counter);","next = next.with_counter(self.next_counter);"],
  ["edit-commit-ignores-counter","src/edit.rs","fn with_counter(","self.next_counter = counter;","self.next_counter = self.next_counter;"],
  ["receive-error-corrupts-counter","src/edit.rs","fn receive(","crate::event_shell::receive(\n            self,\n            fact,\n            &(),\n            receive_plan,\n            Admission::Added,\n            Admission::Duplicate,\n        )","{ let (mut next, result) = crate::event_shell::receive(\n            self,\n            fact,\n            &(),\n            receive_plan,\n            Admission::Added,\n            Admission::Duplicate,\n        ); if matches!(result, Err(_)) { next.next_counter = 0; } (next, result) }"],
  ["edit-error-corrupts-counter","src/edit.rs","pub fn edit(","Err(error) => (self, Err(error)),","Err(error) => { let mut damaged = self; damaged.next_counter = 0; (damaged, Err(error)) },"],
  ["edit-success-reuses-counter","src/edit.rs","fn next_counter_after(","Ok(counter + 1)","Ok(counter)"],
  ["local-return-gap","src/edit.rs","pub fn edit(","(next, Ok(Local::Authored(fact)))","{ let mut changed = fact; changed.gap = Some(0); (next, Ok(Local::Authored(changed))) }"],
  ["local-stale-tree","src/edit.rs","pub fn edit(","next = next.with_counter(next_counter);","next = next.with_counter(next_counter); next.tree = self.tree.clone();"],
  ["receive-success-counter","src/edit.rs","fn receive(","crate::event_shell::receive(\n            self,\n            fact,\n            &(),\n            receive_plan,\n            Admission::Added,\n            Admission::Duplicate,\n        )","{ let (mut next, result) = crate::event_shell::receive(\n            self,\n            fact,\n            &(),\n            receive_plan,\n            Admission::Added,\n            Admission::Duplicate,\n        ); if matches!(result, Ok(Admission::Added)) { next.next_counter = 0; } (next, result) }"],
  ["author-forgets-gap","src/edit.rs","pub fn edit(","Some(gap)","Some(0)"],
  ["receive-private-gate","src/edit.rs","fn plan_validate(","Replica::validate_new(&before.facts, fact)","Replica::validate_new(&before.facts, fact)?; if before.writer.is_none() { return Err(Error::Missing); } Ok(())"],
  ["identity-forgets-gap","src/edit.rs","fn fact_equal(","&& left.gap == right.gap","&& true"],
  ["identity-accepts-conflict","src/event_layer.rs","fn classify<","return Some(fact_eq(old, fact));","return Some(fact_eq(old, fact) || id_eq(&id(old), &id(fact)));"],
  ["identity-skips-later","src/event_layer.rs","fn classify<","for i in 0..facts.len() {","for i in 0..0 {"],
  ["identity-counter-range","src/edit.rs","fn duplicate(","if fact.id.counter == 0 || fact.id.counter > MAX_COUNTER {","if false {"],
  ["identity-event-equality","src/edit.rs","impl PartialEq for EventId","self.writer == other.writer && self.counter == other.counter","self.writer == other.writer"],
  ["identity-scan-key","src/edit.rs","fn duplicate(","crate::event_layer::classify(facts, fact, &TEXT_OPS.0)","crate::event_layer::classify(facts, fact, &crate::event_layer::graph_ops(|f| EventId { writer: Writer(1), counter: f.id.counter }, fact_after, same_event_id, earlier_event_id, clone_selected_fact, fact_equal, internal_error, missing_error))"],
  ["identity-birth-equality","src/edit.rs","impl PartialEq for BirthId","self.event == other.event && self.index == other.index","self.event == other.event"],
  ["identity-writer-equality","src/edit.rs","impl PartialEq for Writer","writer_index(*self) == writer_index(*other)","writer_index(*self) == writer_index(*self)"],
  ["accepted-reuses-member","src/event_layer.rs","fn choose_unseen<","if !has_fact(out, &id(&facts[j]), ops) {","if true {"],
  ["accepted-wrong-canonical-push","src/event_layer.rs","fn canonical_step<","push(&mut out, clone_selected_fact(&facts[i], clone_fact), internal)?;","push(&mut out, clone_selected_fact(&facts[0], clone_fact), internal)?;"],
  ["accepted-publication-duplicates","src/edit.rs","fn with_tree(","self.tree = tree;","self.tree = tree; if !self.facts.is_empty() && self.facts.len() < usize::MAX { let copy = self.facts[0].clone(); self.facts.push(copy); }"],
  ["content-changes-whole-fact","src/edit.rs","fn clone_selected_fact(","fact.clone()","let mut changed = fact.clone(); changed.gap = None; changed"],
  ["content-omits-facts","src/event_layer.rs","fn canonical<","for _ in 0..facts.len() {","for _ in 0..0 {"],
  ["past-drops-roots","src/event_layer.rs","fn past<","let mut selected = after_ids.to_vec();","let mut selected = Vec::new();"],
  ["past-invents-id","src/event_layer.rs","fn extend_past<","if has_id(&selected, &id(fact), ops) {","if true {"],
  ["past-membership-always-false","src/event_layer.rs","fn has_id<","if id_eq(&ids[i], wanted) {","if false {"],
  ["past-skips-predecessors","src/event_layer.rs","fn extend_past<","if has_id(&selected, &id(fact), ops) {","if false {"],
  ["past-skips-passes","src/event_layer.rs","fn past<","for _ in 0..facts.len() {","for _ in 0..0 {"],
  ["past-refuses-closure","src/event_layer.rs","fn past<","Ok(selected)","Err((ops.1.0)())"],
  ["duplicate-scan-skips-pairs","src/event_layer.rs","fn duplicate_ids<","if id_eq(&xs[i], &xs[j]) {","if false {"],
  ["scheduler-ready-skips-dependency","src/event_layer.rs","fn ready<","if has_id(done, &after[i], ops) {","if true {"],
  ["scheduler-reselects-done","src/event_layer.rs","fn choose_ready<","if has_id(done, &id(&facts[i]), ops) {","if false {"],
  ["scheduler-refuses-ready","src/event_layer.rs","fn choose_ready<","return Some(i);","return None;"],
  ["scheduler-checks-empty-after","src/event_layer.rs","fn choose_ready<","ready(after(&facts[i]), done, ops)","ready(&[], done, ops)"],
  ["scheduler-records-wrong-id","src/edit.rs","fn interpret_scheduled(","fact_id,","|_| EventId { writer: Writer(1), counter: 0 },"],
  ["scheduler-stops-early","src/event_shell.rs","fn scheduled<","for _ in 0..facts.len() {","for _ in 0..0 {"],
  ["scheduler-erases-wrong-trace","src/edit.rs","fn interpret(","let pair = interpret_scheduled(facts)?;","let pair = interpret_scheduled(&[])?;"],
  ["scheduler-invents-bookkeeping-error","src/event_shell.rs","fn scheduled<","let event_id = id(event);","if operations.len() == 0 { return Err(internal()); } let event_id = id(event);"],
  ["basis-includes-unselected","src/event_layer.rs","fn select_basis<","if has_id(selected, &id(fact), ops) {","if true {"],
  ["basis-omits-selected","src/event_layer.rs","fn select_basis<","if has_id(selected, &id(fact), ops) {","if false {"],
  ["basis-event-ignores-roots","src/event_layer.rs","fn event_basis<","past(facts, after(event), ops)?","past(facts, &[], ops)?"],
  ["replay-nodes-skip-first","src/edit.rs","fn replay_nodes(","for i in 0..nodes.len() {","for i in 1..nodes.len() {"],
  ["replay-nodes-reverse","src/edit.rs","fn replay_nodes(","tree.add(nodes[i].clone())?;","tree.add(nodes[nodes.len() - 1 - i].clone())?;"],
  ["replay-groups-include-all","src/edit.rs","fn replay_author(","if has_event(selected, id) {","if !has_event(&[], id) {"],
  ["replay-groups-skip-all","src/edit.rs","fn replay_author(","if has_event(selected, id) {","if has_event(&[], id) {"],
  ["replay-context-passes-empty","src/edit.rs","fn author_context(","replay_author(operations, &selected)?","replay_author(&[], &selected)?"],
  ["replay-context-invents-error","src/edit.rs","fn author_context(","let author = replay_author(operations, &selected)?;","let author = replay_author(operations, &selected)?; if operations.is_empty() { return Err(Error::Internal); }"],
  ["replay-context-contaminates-basis","src/edit.rs","fn author_context(","let (selected, basis) = event_basis(facts, event)?;","let (selected, mut basis) = event_basis(facts, event)?; if !event.after.is_empty() && facts.len() > 2 { push(&mut basis, facts[1].clone())?; }"],
  ["scheduler-forgets-completed-tree","src/edit.rs","fn interpret_scheduled(","crate::event_shell::scheduled(\n        facts,\n        Tree::default(),\n        &(),\n        fact_id,\n        scheduled_choose,\n        scheduled_apply,\n        internal_error,\n    )","crate::event_shell::scheduled(\n        facts,\n        Tree::default(),\n        &(),\n        fact_id,\n        scheduled_choose,\n        scheduled_apply,\n        internal_error,\n    ).map(|(_, done)| (Tree::default(), done))"],
  ["plan-interprets-uncanonical-call","src/edit.rs","fn plan(","plan_prepare,","|_, next, fact| { let mut prepared = next; push(&mut prepared.facts, fact.clone())?; Ok(prepared) },"],
  ["shared-plan-skips-validation","src/event_shell.rs","fn plan<","validate(context, before, fact)?;","let _ = validate(context, before, fact);"],
  ["shared-plan-ignores-duplicate","src/event_shell.rs","fn plan<","if duplicate(context, before, fact)? {","if duplicate(context, before, fact)? && false {"],
  ["shared-plan-swallows-classifier-error","src/event_shell.rs","fn plan<","if duplicate(context, before, fact)? {","if match duplicate(context, before, fact) { Ok(found) => found, Err(_) => false } {"],
  ["identity-call-passes-empty","src/edit.rs","fn duplicate(","crate::event_layer::classify(facts, fact, &TEXT_OPS.0)","crate::event_layer::classify(&[], fact, &TEXT_OPS.0)"],
  ["identity-call-ignores-payload","src/edit.rs","fn duplicate(","crate::event_layer::classify(facts, fact, &TEXT_OPS.0)","crate::event_layer::classify(facts, fact, &crate::event_layer::graph_ops(fact_id, fact_after, same_event_id, earlier_event_id, clone_selected_fact, |left, right| left.id == right.id, internal_error, missing_error))"],
  ["past-membership-call-passes-empty","src/edit.rs","fn has_event(","crate::event_layer::has_id(ids, &id, &TEXT_OPS.0)","crate::event_layer::has_id(&[], &id, &TEXT_OPS.0)"],
  ["scheduler-readiness-call-passes-empty","src/edit.rs","fn ready(","crate::event_layer::ready(after, done, &TEXT_OPS.0)","crate::event_layer::ready(&[], done, &TEXT_OPS.0)"],
  ["scheduler-choice-call-passes-empty","src/edit.rs","fn choose_ready(","crate::event_layer::choose_ready(facts, done, &TEXT_OPS.0)","crate::event_layer::choose_ready(&[], done, &TEXT_OPS.0)"],
  ["text-policy-swaps-eq-lt","src/edit.rs","const TEXT_OPS:","same_event_id, earlier_event_id,","earlier_event_id, same_event_id,"],
  ["graph-policy-swaps-eq-lt","src/event_layer.rs","const fn graph_ops<","(id, after, id_eq, id_lt, clone_fact, fact_eq)","(id, after, id_lt, id_eq, clone_fact, fact_eq)"],
  ["admission-policy-swaps-errors","src/event_layer.rs","const fn event_ops<","(duplicate_error, predecessor_error)","(predecessor_error, duplicate_error)"]
];
const definitionByMode=new Map(mutationDefinitions.map(([mode,...definition])=>[mode,definition]));
const registeredMutations=modes.filter(mode=>mode!=='positive');
assert.equal(new Set(registeredMutations).size,registeredMutations.length,'duplicate registered mutation mode');
assert.equal(definitionByMode.size,mutationDefinitions.length,'duplicate mutation definition');
assert.deepEqual([...definitionByMode.keys()].sort(),[...registeredMutations].sort(),'mutation definitions must exactly cover registered modes');
for(const [mode,owner,header,needle,replacement] of mutationDefinitions) {
  assert.equal(definitionByMode.get(mode).length,4,'mutation definition must have four fields: '+mode);
  assert(sourceFiles.includes(owner),'unknown mutation source owner: '+mode);
  assert([header,needle,replacement].every(value=>typeof value==='string'&&value.length>0),'mutation fields must be nonempty strings: '+mode);
}
function prepareMutation(mode,sources=original) {
  const definition=definitionByMode.get(mode);
  assert(definition,'mutation without a registered definition: '+mode);
  const [owner,header,needle,replacement]=definition;
  const source=typeof sources==='string'?sources:sources[owner];
  const at=scopedAnchor(source,header,needle,mode);
  const mutant=source.slice(0,at)+source.slice(at).replace(needle,replacement);
  assert.notEqual(mutant,source);
  return typeof sources==='string'?mutant:{...sources,[owner]:mutant};
}
const theorems={
  'scheduler-forgets-completed-tree':'EditSchedule.successful_schedule_has_complete_event_work',
  'replay-nodes-skip-first':'EditReplay.actual_nodes_replay_in_order',
  'replay-nodes-reverse':'EditReplay.actual_nodes_replay_in_order',
  'replay-groups-include-all':'EditReplay.actual_author_replays_selected_groups',
  'replay-groups-skip-all':'EditReplay.actual_author_replays_selected_groups',
  'replay-context-passes-empty':'EditReplay.closed_author_context_is_exact',
  'replay-context-invents-error':'EditReplay.closed_author_context_is_exact',
  'replay-context-contaminates-basis':'EditReplay.closed_author_context_is_exact',
  'basis-includes-unselected':'EditBasis.actual_basis_is_exact_filter',
  'basis-omits-selected':'EditBasis.actual_basis_is_exact_filter',
  'basis-event-ignores-roots':'EditBasis.closed_event_basis_is_exact',
  'scheduler-ready-skips-dependency':'EditSchedule.readiness_is_exact',
  'scheduler-reselects-done':'EditSchedule.scheduler_choice_is_exact',
  'scheduler-refuses-ready':'EditSchedule.scheduler_choice_is_exact',
  'scheduler-checks-empty-after':'EditSchedule.scheduler_choice_is_exact',
  'scheduler-records-wrong-id':'EditSchedule.successful_schedule_is_once_only_and_causal',
  'scheduler-stops-early':'EditSchedule.successful_schedule_is_once_only_and_causal',
  'scheduler-erases-wrong-trace':'EditSchedule.interpret_erases_only_schedule',
  'scheduler-invents-bookkeeping-error':'EditSchedule.ranked_outer_errors_come_from_tree_work',
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
  'duplicate-scan-skips-pairs':'EditPastTotal.duplicate_scan_is_exact',
  'past-skips-passes':'EditPast.past_stays_in_closed_set',
  'past-skips-predecessors':'EditPast.extend_past_covers_predecessors',
  'past-drops-roots':'EditPast.past_stays_in_closed_set',
  'past-invents-id':'EditPast.extend_past_preserves',
  'past-membership-always-false':'EditPast.event_membership_is_exact',
  'causal-call-passes-empty':'EditWellFormed.successful_past_has_direct_dependencies',
  'causal-refuses-present':'EditWellFormed.present_dependencies_pass_guard',
  'scalar-validation-bypasses-on-history':'EditWellFormed.successful_validation_has_valid_scalars',
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

// Explicit semantic ownership transfers. The old statements and their domains
// remain checked; additional concrete callback/call-argument controls above keep
// caller composition sensitive. Only the exact named new owner may reject a
// moved-body control; an arbitrary earlier dependency failure is never credited.
theorems['plan-interprets-uncanonical-call']='EditAccepted.plan_publishes_interpretation';
theorems['text-policy-swaps-eq-lt']='EventGraphText.text_policy_is_exact';
theorems['graph-policy-swaps-eq-lt']='EventGraph.graph_ops_preserve_callbacks';
theorems['admission-policy-swaps-errors']='EventGraph.event_ops_preserve_callbacks';
const priorOwners={...theorems};
const ownerMigrations={
  "plan-interprets-uncanonical-call":["EditAccepted.plan_publishes_canonical_facts","added wrong-prepare callback omits canonicalization; exact canonical fact publication owns this fault, while interpretation of the returned facts can still agree"],
  "plan-interprets-uncanonical":["EventShell.planning_is_exact","callback ordering moved from concrete plan to generic plan"],
  "past-membership-always-false": [
    "EventGraph.membership_is_exact",
    "membership loop moved unchanged to comparison-relative has_id"
  ],
  "scheduler-ready-skips-dependency": [
    "EventGraph.readiness_is_exact",
    "dependency scan moved unchanged to comparison-relative ready"
  ],
  "scheduler-reselects-done": [
    "EventGraph.scheduler_choice_is_exact",
    "actual first-ready scan moved to generic choose_ready"
  ],
  "scheduler-refuses-ready": [
    "EventGraph.scheduler_choice_is_exact",
    "actual first-ready scan moved to generic choose_ready"
  ],
  "scheduler-checks-empty-after": [
    "EventGraph.scheduler_choice_is_exact",
    "actual dependency argument belongs to generic choose_ready"
  ],
  "identity-accepts-conflict": [
    "EventClassifier.classification_is_exact",
    "actual first matching identity classification moved to generic classify"
  ],
  "identity-skips-later": [
    "EventClassifier.classification_is_exact",
    "indexed first-match scan moved to generic classify"
  ]
};
Object.assign(theorems,{
  "shared-plan-skips-validation": "EventShell.planning_is_exact",
  "shared-plan-ignores-duplicate": "EventShell.planning_is_exact",
  "shared-plan-swallows-classifier-error": "EventShell.planning_is_exact",
  "identity-call-passes-empty": "EditIdentity.duplicate_matches_lookup",
  "identity-call-ignores-payload": "EditIdentity.duplicate_matches_lookup",
  "past-membership-call-passes-empty": "EditPast.event_membership_is_exact",
  "scheduler-readiness-call-passes-empty": "EditSchedule.readiness_is_exact",
  "scheduler-choice-call-passes-empty": "EditSchedule.scheduler_choice_is_exact"
});
for(const [mode,[owner]] of Object.entries(ownerMigrations))theorems[mode]=owner;
const mutationOwners=Object.fromEntries(modes.filter(mode=>mode!=='positive').map(mode=>[mode,{owner:theorems[mode],priorOwner:priorOwners[mode]??null,reason:ownerMigrations[mode]?.[1]??(priorOwners[mode]?'owning concrete statement retained':'additional generic-body or concrete-caller control'),source:definitionByMode.get(mode)[0]}]));

// Registration consistency: every selected mutation must have an anchored edit and a
// named owning theorem before any native test, extraction or compiler starts.
// Every registered mode, not only the selected ones, must resolve to exactly one
// anchor inside its named item; the scope controls exercise the same path.
for(const mode of modes.filter(mode=>mode!=='positive')){assert(Object.hasOwn(theorems,mode),'mutation without an owning theorem '+mode);prepareMutation(mode);}
// Owner dispatch itself is part of the fail-closed preparation boundary. A moved
// anchor in another source file must never rescue the selected owner's missing
// anchor. Existing exhaustive literal/lexer controls still run below.
for(const mode of ['native-push-discards-value','plan-skips-validation']) {
  const [owner,header,needle]=definitionByMode.get(mode);
  const source=original[owner], [start,end]=itemSpan(source,header,mode);
  const body=source.slice(start,end);
  const variant=body=>({...original,[owner]:source.slice(0,start)+body+source.slice(end)});
  const prepared=prepareMutation(mode);
  assert.deepEqual(sourceFiles.filter(file=>prepared[file]!==original[file]),[owner],'mutation must change only its actual owner '+mode);
  assert.throws(()=>prepareMutation(mode,variant(body.replace(needle,'/* moved '+needle+' */'))),/anchor is not code/);
  assert.throws(()=>prepareMutation(mode,variant(body.replace(needle,''))),/anchor not found in its scope/);
  assert.throws(()=>prepareMutation(mode,variant(body.replace('{','{ '+needle+';'))),/anchor is ambiguous/);
  const other=sourceFiles.find(file=>file!==owner);
  assert.throws(()=>prepareMutation(mode,{...variant(body.replace(needle,'')),[other]:original[other]+'\n'+body}),/anchor not found in its scope/,'another file cannot rescue a moved anchor');
  const renamed=source.replace(header,header.replace('fn ','fn moved_'));
  assert.throws(()=>prepareMutation(mode,{...original,[owner]:'// '+header+'\n'+renamed}),/scope not found/);
}

checkMutationScopeControls(prepareMutation,original['src/edit.rs'],'scalar-refuses-valid','fn validate_scalars(','Ok(())','fn validate_new(');
console.log('PASS mutation scopes: every registered mode resolves to one in-scope anchor; moved/duplicate/comment-only anchor, missing/comment/string/duplicated header, literal braces, C raw strings across items and unsupported-lexeme controls');
if(args.length===1&&args[0]==='gatepreflight')process.exit(0);
const {NICKEL_HAX_BIN:hax,NICKEL_PROOF_FSTAR:fstar,NICKEL_HAX_SOURCE:models,NICKEL_FSTAR_MODEL_CACHE:modelCache}=process.env;
assert(hax&&fstar&&models&&modelCache,'use the locked .#proofs environment');
const output=process.argv[2];assert(output,'output directory required');
await fs.mkdir(output,{recursive:true});
await fs.writeFile(path.join(output,'mutation-owners.json'),JSON.stringify(mutationOwners,null,2)+'\n');
const identity=JSON.parse(await fs.readFile(path.join(modelCache,'identity.json'),'utf8'));
assert.equal(identity.models,models);assert.equal(identity.fstar,fstar);
const views=new Map();
for(const name of ['Prelude','LoopUtil','LoopEquality','EventGraph','EventGraphText','EventShell','EventClassifier','Vector','EditAtomic','EditCommit','EditIdentity','EditAccepted','EditWellFormed','Spec','EditCausal','EditPast','EditPastTotal','EditSchedule','EditBasis','EditReplay']) {
  const source=`proofs/${name}.lt`,view=`proofs/generated/Nickel.${name}.fst`;
  const code=await fs.readFile(path.join(root,view),'utf8');
  const receipt=(await fs.readFile(path.join(root,`proofs/generated/${name}.sha256`),'utf8')).trim().split('\n');
  assert.deepEqual(receipt,[digest(await fs.readFile(path.join(root,source)))+'  '+source,digest(code)+'  '+view]);
  assert(!/\b(?:admit|admit_smt_queries|assume|lax)\b/.test(code),'no authored admissions');
  views.set(`Nickel.${name}.fst`,code);
}

const prepared=new Map();
for(const mode of mutations) {
  assert(Object.hasOwn(theorems,mode),'mutation without an owning theorem: '+mode);
  assert(views.has('Nickel.'+theorems[mode].split('.')[0]+'.fst'),'owning theorem outside the checked views: '+mode);
  prepared.set(mode,prepareMutation(mode));
}
const haxArgs=out=>['-C','--offline','--locked','-p','nickel-crdt',';','into','--output-dir',out,'-i',"-** +nickel_crdt::edit::**::receive +nickel_crdt::edit::**::edit +nickel_crdt::edit::**::new +nickel_crdt::edit::**::validate_new +nickel_crdt::edit::fact_equal +nickel_crdt::edit::push +nickel_crdt::edit::duplicate_events +nickel_crdt::edit::has_event +nickel_crdt::edit::has_fact +nickel_crdt::edit::choose_unseen +nickel_crdt::edit::clone_selected_fact +nickel_crdt::edit::canonical_step +nickel_crdt::edit::canonical +nickel_crdt::edit::ready +nickel_crdt::edit::choose_ready +nickel_crdt::edit::frontier +nickel_crdt::edit::validate_after +nickel_crdt::edit::extend_past +nickel_crdt::edit::past_pass +nickel_crdt::edit::past +nickel_crdt::edit::select_basis +nickel_crdt::edit::event_basis +nickel_crdt::edit::interpret_scheduled",'fstar'];
const copyCrate=async(crate,source)=>{
  await fs.mkdir(crate,{recursive:true});
  for(const name of ['Cargo.toml','Cargo.lock','src','tests','proof-smoke'])await fs.cp(path.join(root,name),path.join(crate,name),{recursive:true});
  if(source!==undefined)for(const [name,code] of Object.entries(source))await fs.writeFile(path.join(crate,name),code);
};
const inventory=async dir=>JSON.stringify(await Promise.all((await fs.readdir(dir)).filter(name=>/\.fsti?$/.test(name)).sort()
  .map(async name=>[name,digest(await fs.readFile(path.join(dir,name)))])));
// Extraction identity, independent of any theorem: a second extraction of the same
// crate, in a fresh private Cargo target, must give the same generated inventory
// byte for byte. A shared or stale target that hands one crate another crate's
// extraction fails here, even when the owner would also reject the wrong mutant.
async function sameExtraction(label,crate,extract,scratch) {
  await fs.rm(scratch,{recursive:true,force:true});await fs.mkdir(path.join(scratch,'extract'),{recursive:true});
  const reference=await runAsync('edit hax reference '+label,hax,haxArgs(path.join(scratch,'extract')),crate,{env:{...process.env,CARGO_TARGET_DIR:path.join(scratch,'target')}});
  assert.equal(reference.status,0,reference.log);
  const same=await inventory(extract)===await inventory(path.join(scratch,'extract'));
  await fs.rm(scratch,{recursive:true,force:true});
  return same;
}
const fresh=async proof=>{try{await fs.access(path.join(proof,'sources.json'));return false;}catch{return true;}};
let positive,positiveProof;
async function check(mode) {
  const work=path.join(root,'.cache','edit-proofs',mode),crate=path.join(work,'crate'),proof=path.join(work,'proof');
  if(positiveProof&&await fresh(proof))await fs.cp(positiveProof,proof,{recursive:true,preserveTimestamps:true});
  await fs.mkdir(proof,{recursive:true});
  await copyCrate(crate,mode==='positive'?undefined:prepared.get(mode));
  // Each mode has its own Cargo target: hax names its metadata by package, not by
  // source tree, so crate copies sharing a target read each other's extraction.
  const env={...process.env,CARGO_TARGET_DIR:path.join(root,'target','edit-proof-check','modes',mode)};
  const nativeArgs=['test','--offline','--locked','-p','nickel-crdt',...(mode==='scheduler-forgets-completed-tree'?['--lib','operation_provenance_tests']:mode.startsWith('replay-')?['--lib','author_replay_tests']:mode.startsWith('basis-')?['--lib','basis_filter_tests']:((mode.startsWith('past-')||mode.startsWith('scheduler-'))?['--lib','causal_basis_tests']:['--test','edit_admit']))];
  const native=await runAsync('edit native '+mode,'cargo',nativeArgs,crate,{env});
  await fs.writeFile(path.join(output,mode+'.native.log'),native.log);
  if(mode==='positive') {
    assert.equal(native.status,0,native.log);
    const basisNative=await runAsync('edit basis native baseline','cargo',['test','--offline','--locked','-p','nickel-crdt','--lib','basis_filter_tests'],crate,{env});
    await fs.writeFile(path.join(output,'positive.basis-native.log'),basisNative.log);
    assert.equal(basisNative.status,0,basisNative.log);
    assert.match(basisNative.log,/test result: ok\. [1-9]\d* passed;/,'basis native baseline must discover and pass tests: '+basisNative.log);
    const operationNative=await runAsync('edit operation native baseline','cargo',['test','--offline','--locked','-p','nickel-crdt','--lib','operation_provenance_tests'],crate,{env});
    await fs.writeFile(path.join(output,'positive.operation-native.log'),operationNative.log);
    assert.equal(operationNative.status,0,operationNative.log);
    assert.match(operationNative.log,/test result: ok\. [1-9]\d* passed;/,'operation native baseline must discover and pass tests: '+operationNative.log);
    const replayNative=await runAsync('edit replay native baseline','cargo',['test','--offline','--locked','-p','nickel-crdt','--lib','author_replay_tests'],crate,{env});
    await fs.writeFile(path.join(output,'positive.replay-native.log'),replayNative.log);
    assert.equal(replayNative.status,0,replayNative.log);
    assert.match(replayNative.log,/test result: ok\. [1-9]\d* passed;/,'replay native baseline must discover and pass tests: '+replayNative.log);
  }
  else {assert.equal(native.status,101,native.log);assert.match(native.log,/test result: FAILED/);}
  const extract=path.join(work,'extract');await fs.rm(extract,{recursive:true,force:true});await fs.mkdir(extract,{recursive:true});
  const extracted=await runAsync('edit hax '+mode,hax,haxArgs(extract),crate,{env});
  await fs.writeFile(path.join(output,mode+'.hax.log'),extracted.log);
  assert.equal(extracted.status,0,extracted.log);
  assert(await sameExtraction(mode,crate,extract,path.join(work,'reference')),'extraction identity: '+mode+"'s extraction differs from a private-target extraction of its own crate");
  // Install the fresh extraction inventory: remove project sources that are neither
  // authored views nor produced by this extraction (e.g. left by a seeded copy).
  const inventory=(await fs.readdir(extract)).filter(name=>/\.fsti?$/.test(name)).sort();
  const expectedExtraction=['Nickel_crdt.Edit.fst','Nickel_crdt.Event_layer.fst','Nickel_crdt.Event_shell.fst'];
  assert.deepEqual(inventory,expectedExtraction,'unexpected actual edit extraction inventory');
  assert(inventory.includes('Nickel_crdt.Edit.fst'),'extraction did not produce Nickel_crdt.Edit.fst');
  for(const name of await fs.readdir(proof))if(/\.fsti?$/.test(name)&&!views.has(name)&&!inventory.includes(name))await fs.rm(path.join(proof,name));
  for(const name of inventory)await put(path.join(proof,name),await fs.readFile(path.join(extract,name),'utf8'));
  const code=await fs.readFile(path.join(proof,'Nickel_crdt.Edit.fst'),'utf8');
  assert.match(code,/let impl_Replica__receive /);assert.match(code,/let impl_Replica__edit/);assert.match(code,/let impl_Replica__new/);
  // Preserve an ordinary call at the identity boundary: PartialEq operators
  // are structurally lowered by the pinned backend, ignoring custom bodies.
  const nativeDeclaration=name=>{
    const found=[...code.matchAll(new RegExp('^let '+name+'(?=[: \t])','gm'))];
    assert.equal(found.length,1,'exact native declaration '+name);
    const start=found[0].index,next=code.indexOf('\nlet ',start+4);
    return code.slice(start,next<0?code.length:next);
  };
  const scan=nativeDeclaration('impl_Replica__duplicate');
  assert.match(scan,/Nickel_crdt\.Event_layer\.classify/);
  if(mode==='identity-call-ignores-payload') {
    assert.match(scan,/Nickel_crdt\.Event_layer\.graph_ops/,'wrong per-call policy must be extracted');
    assert(!/fact_equal/.test(scan),'wrong callback must replace the full-fact comparison');
  } else if(mode!=='identity-scan-key') {
    assert.match(scan,/v_TEXT_OPS/,'classifier must consume the actual client policy');
    const policy=nativeDeclaration('v_TEXT_OPS');
    assert.match(policy,/fact_equal/,'client policy must retain whole-fact equality');
  }
  for(const name of inventory)assert(!/\b(?:admit|assume|admit_smt_queries)\b/.test(await fs.readFile(path.join(proof,name),'utf8')),'no assumptions in extracted project code '+name);
  const extractionIdentity=await Promise.all(inventory.map(async name=>[name,digest(await fs.readFile(path.join(extract,name)))]));
  if(mode==='positive') {
    const retained=(await fs.readdir(path.join(root,'proofs/generated/hax'))).filter(name=>/\.fsti?$/.test(name)).sort();
    // This directory also retains the independent smoke gate's sole module.
    assert.deepEqual(retained,[...expectedExtraction,'Nickel_proof_smoke.fst'].sort(),'unexpected retained hax inventory (edit owners plus independent smoke owner)');
    for(const name of inventory)assert.equal(await fs.readFile(path.join(extract,name),'utf8'),await fs.readFile(path.join(root,'proofs/generated/hax',name),'utf8'),'fresh extraction differs from retained '+name);
    positive=JSON.stringify(extractionIdentity);
  } else assert.notEqual(JSON.stringify(extractionIdentity),positive,'mutation must change the actual extracted inventory');
  for(const [name,code] of views)await put(path.join(proof,name),code);
  // What this workspace last recorded for the extraction decides whether it must be
  // recompiled now: changed (seeded, fresh or edited) must recompile; unchanged may be reused.
  let recorded={};try{recorded=JSON.parse(await fs.readFile(path.join(proof,'sources.json'),'utf8'));}catch(e){if(e.code!=='ENOENT')throw e;}
  const extractionChanged=extractionIdentity.filter(([name,hash])=>recorded[name]!==hash).map(([name])=>name);
  // Counter calculation/installation/wiring controls need only their owning module. The positive path still
  // checks both the public Spec surface and the existing ghost causal-rank family.
  const proofRoot=/^(EventGraph|EventGraphText|EventShell|EventClassifier)\./.test(theorems[mode]??'')?'Nickel.'+theorems[mode].split('.')[0]+'.fst':mode==='positive'?'Nickel.Spec.fst':mode.startsWith('replay-')?'Nickel.EditReplay.fst':mode.startsWith('basis-')?'Nickel.EditBasis.fst':mode.startsWith('scheduler-')?'Nickel.EditSchedule.fst':['past-refuses-closure','duplicate-scan-skips-pairs'].includes(mode)?'Nickel.EditPastTotal.fst':mode.startsWith('past-')?'Nickel.EditPast.fst':['edit-success-reuses-counter','edit-commit-ignores-counter','edit-call-passes-old-counter'].includes(mode)?'Nickel.EditAtomic.fst':'Nickel.EditWellFormed.fst';
  const checked=await verify({label:mode,dir:proof,roots:(mode==='positive'?['Nickel.EventGraph.fst','Nickel.EventGraphText.fst','Nickel.EventShell.fst','Nickel.EventClassifier.fst','Nickel.Spec.fst','Nickel.EditCausal.fst','Nickel.EditPastTotal.fst','Nickel.EditSchedule.fst','Nickel.EditBasis.fst','Nickel.EditReplay.fst']:['Nickel_crdt.Edit.fst',proofRoot]).map(name=>path.join(proof,name)),fstar,models,modelCache});
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
    for(const name of inventory)await fs.copyFile(path.join(proof,name),path.join(output,name));
  } else {
    assert.equal(checked.status,2,'require ordinary proof rejection, not extraction failure/timeout');
    const theorem='Nickel.'+theorems[mode],file='Nickel.'+theorems[mode].split('.')[0]+'.fst';
    // A reused cache must never stand in for checking the changed program. The owning
    // proof module always compiles here (a rejected module leaves no checked result);
    // the extraction must compile whenever it differs from this workspace's last record.
    // An unchanged extraction in a warm rerun of the same mode may be legitimately reused.
    for(const changed of [...extractionChanged,file])
      assert(checked.modules.includes(changed),changed+' was not compiled for '+mode+': '+(checked.modules.join(',')||'nothing'));
    assert(hasOrdinaryTheoremRejection({status:checked.status,log:checked.log,theorem,view:views.get(file)}),
      'require a final ordinary named query rejection and a semantic error in its source declaration: '+checked.log);
  }
  console.log(`PASS ${mode}: native and unchanged actual-Rust theorem ${mode==='positive'?'verified':'reject the mutation'}`);
}
// The positive chain (and its families) completes first: it seeds every fresh
// mutation workspace and is only read afterwards. After the first failure no
// further mode starts; running modes finish before the failure is reported.
if(wantPositive)await check('positive');
// Identity control: two mutants of one function (one owner theorem rejects both).
// A's crate with B's extraction must fail the identity check; B's own must pass.
if(mutations.length) {
  const control=path.join(root,'.cache','edit-proofs','identity-control'),[a,b]=['scheduler-reselects-done','scheduler-refuses-ready'];
  await fs.rm(control,{recursive:true,force:true});
  await copyCrate(path.join(control,'a'),prepareMutation(a));await copyCrate(path.join(control,'b'),prepareMutation(b));
  await fs.mkdir(path.join(control,'extract'),{recursive:true});
  const extracted=await runAsync('edit hax identity control',hax,haxArgs(path.join(control,'extract')),path.join(control,'b'),{env:{...process.env,CARGO_TARGET_DIR:path.join(control,'target')}});
  assert.equal(extracted.status,0,extracted.log);
  assert(!await sameExtraction('control wrong mutant',path.join(control,'a'),path.join(control,'extract'),path.join(control,'reference')),'identity control: another mutant\'s extraction passed the identity check');
  assert(await sameExtraction('control own mutant',path.join(control,'b'),path.join(control,'extract'),path.join(control,'reference')),'identity control: a mutant\'s own extraction failed the identity check');
  await fs.rm(control,{recursive:true,force:true});
  console.log('PASS extraction identity control: a wrong mutant\'s extraction fails identity; its own passes');
}
// A mode selected twice (for example by a shard and by name) runs once: two
// concurrent checks of one mode would share its workspace.
const queue=[...new Set(mutations)];
let next=0,failure;
await Promise.all(Array.from({length:Math.min(jobs,queue.length)},async()=>{
  while(!failure&&next<queue.length) {const mode=queue[next++];try{await check(mode);}catch(error){failure??={mode,error};}}
}));
if(failure)throw failure.error;
