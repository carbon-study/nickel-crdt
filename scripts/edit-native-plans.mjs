// Shared enumeration of the text gate's native mutation modes and its positive chain (#197).
// check-edit-proofs.mjs executes exactly these units, and `export-plans` exports them; neither path
// re-derives a mode, owner, root, mutation or cargo argument on its own. Pure: no I/O, no solver.
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {scopedAnchor} from './mutation-scope.mjs';
export const sourceFiles=['src/edit.rs','src/event_layer.rs','src/event_shell.rs'];
export const modes=["stream-admission-skips-predecessor","stream-admission-skips-forbidden","stream-admission-swaps-forbidden-args","stream-text-omits-predecessor-policy",'plan-skips-validation',"tree-publication-uses-private-writer","tree-publication-clears-private-counter","plan-clears-private-counter",'positive','plan-ignores-duplicate','plan-swallows-classifier-error','receive-plan-rewrites-counter','invalid-forgets-reason','writer-index-collides','native-push-discards-value','native-push-prepends','causal-validator-passes-empty','causal-accepts-missing','causal-call-passes-empty','causal-refuses-present','plan-interprets-uncanonical','scalar-validation-bypasses-on-history','scalar-accepts-invalid','scalar-call-passes-empty','scalar-refuses-valid','canonical-step-refuses','canonical-refuses','plan-keeps-old-tree','plan-passes-old-tree','order-key-ignores-writer','order-chooses-largest','order-discards-canonical','local-return-after','edit-call-passes-old-counter','edit-commit-ignores-counter','receive-error-corrupts-counter','edit-error-corrupts-counter','edit-success-reuses-counter',
  'local-return-gap','local-stale-tree','receive-success-counter','author-forgets-gap','receive-private-gate',
  'identity-forgets-gap','identity-accepts-conflict','identity-skips-later','identity-counter-range','identity-event-equality',
  'identity-scan-key','identity-birth-equality','identity-writer-equality',
  'accepted-reuses-member','accepted-wrong-canonical-push','accepted-publication-duplicates',
  'content-changes-whole-fact','content-omits-facts','past-drops-roots','past-invents-id','past-membership-always-false','past-skips-predecessors','past-skips-passes','past-refuses-closure','duplicate-scan-skips-pairs','scheduler-ready-skips-dependency','scheduler-reselects-done','scheduler-refuses-ready','scheduler-checks-empty-after','scheduler-records-wrong-id','scheduler-stops-early','scheduler-erases-wrong-trace','scheduler-invents-bookkeeping-error','basis-includes-unselected','basis-omits-selected','basis-event-ignores-roots','replay-nodes-skip-first','replay-nodes-reverse','replay-groups-include-all','replay-groups-skip-all','replay-context-passes-empty','replay-context-invents-error','replay-context-contaminates-basis','scheduler-forgets-completed-tree'];
modes.push('plan-interprets-uncanonical-call', ...["shared-plan-skips-validation","shared-plan-ignores-duplicate","shared-plan-swallows-classifier-error","identity-call-passes-empty","identity-call-ignores-payload","past-membership-call-passes-empty","scheduler-readiness-call-passes-empty","scheduler-choice-call-passes-empty"]);
modes.push('past-guard-refuses-present','past-extension-refuses-selection');
modes.push("past-extend-call-clears-selection","past-pass-call-skips-facts","past-call-clears-roots");
// #107: past stops at its fixpoint and each pass scans newest-first.
modes.push("past-closes-after-one-pass","past-pass-rescans-last");
modes.push('text-policy-swaps-eq-lt','graph-policy-swaps-eq-lt','admission-policy-swaps-errors');
// A fresh mutation workspace starts from the verified positive workspace: same
// views and caches, then fresh hax output replaces Nickel_crdt.Edit.fst. Its
// digest change (and F*'s own dependency check) forces the extracted module and
// every dependent proof to recheck; only modules independent of it are reused.
// Each mutation edits exactly one anchored site of the actual Rust source.
// Each row is [mode, source owner, item header, anchor, replacement]. This is
// the sole mutation definition table; the lookup below is only its index.
const mutationDefinitions=[
  ["stream-admission-skips-predecessor","src/event_layer.rs","fn validate_event<","if !has_id(&selected, &previous, ops) {","if false {"],
  ["stream-admission-skips-forbidden","src/event_layer.rs","fn validate_event<","&& forbidden(&id(e), &id(fact))","&& false"],
  ["stream-admission-swaps-forbidden-args","src/event_layer.rs","fn validate_event<","forbidden(&id(e), &id(fact))","forbidden(&id(fact), &id(e))"],
  ["stream-text-omits-predecessor-policy","src/edit.rs","fn validate_new(","&TEXT_OPS)","&crate::event_layer::event_ops(TEXT_OPS.0, |_| None, forbidden_ancestor, duplicate_dependency_error, predecessor_error))"],
  ["plan-skips-validation","src/edit.rs","fn plan_validate(","Replica::validate_new(&before.facts, fact)","Ok(())"],
  ["tree-publication-uses-private-writer","src/edit.rs","fn with_tree(","self.tree = tree;","if self.writer.is_some() { self.tree = tree; }"],
  ["tree-publication-clears-private-counter","src/edit.rs","fn with_tree(","self.tree = tree;","self.tree = tree; self.next_counter = 0;"],
  ["plan-clears-private-counter","src/edit.rs","fn plan_prepare(","push(&mut next.facts, fact.clone())?;","next.next_counter = 0; push(&mut next.facts, fact.clone())?;"],
  ["plan-ignores-duplicate","src/edit.rs","fn plan_duplicate(","Replica::duplicate(&before.facts, fact)","let _ = Replica::duplicate(&before.facts, fact)?; Ok(false)"],
  ["plan-swallows-classifier-error","src/edit.rs","fn plan_duplicate(","Replica::duplicate(&before.facts, fact)","match Replica::duplicate(&before.facts, fact) { Ok(found) => Ok(found), Err(_) => Ok(false) }"],
  ["receive-plan-rewrites-counter","src/edit.rs","fn receive_plan(","before.plan(fact)","let mut offered = fact.clone(); offered.id.counter = 1; before.plan(&offered)"],
  ["invalid-forgets-reason","src/edit.rs","fn invalid(","Error::Invalid(reason)","Error::Invalid(Invalid::Counter)"],
  ["writer-index-collides","src/edit.rs","fn writer_index(","Writer::Bo => 1","Writer::Bo => 0"],
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
  ["identity-scan-key","src/edit.rs","fn duplicate(","crate::event_layer::classify(facts, fact, &TEXT_OPS.0)","crate::event_layer::classify(facts, fact, &crate::event_layer::graph_ops(|f| EventId { writer: Writer::Alice, counter: f.id.counter }, fact_after, same_event_id, earlier_event_id, clone_selected_fact, fact_equal, internal_error, missing_error))"],
  ["identity-birth-equality","src/edit.rs","impl PartialEq for BirthId","self.event == other.event && self.index == other.index","self.event == other.event"],
  ["identity-writer-equality","src/edit.rs","impl PartialEq for Writer","writer_index(*self) == writer_index(*other)","writer_index(*self) == writer_index(*self)"],
  ["accepted-reuses-member","src/event_layer.rs","fn choose_unseen<","if !has_fact(out, &id(&facts[j]), ops) {","if true {"],
  ["accepted-wrong-canonical-push","src/event_layer.rs","fn canonical_step<","push(&mut out, clone_selected_fact(&facts[i], clone_fact), internal)?;","push(&mut out, clone_selected_fact(&facts[0], clone_fact), internal)?;"],
  ["accepted-publication-duplicates","src/edit.rs","fn with_tree(","self.tree = tree;","self.tree = tree; if !self.facts.is_empty() && self.facts.len() < usize::MAX { let copy = self.facts[0].clone(); self.facts.push(copy); }"],
  ["content-changes-whole-fact","src/edit.rs","fn clone_selected_fact(","fact.clone()","let mut changed = fact.clone(); changed.gap = None; changed"],
  ["content-omits-facts","src/event_layer.rs","fn canonical<","for _ in 0..facts.len() {","for _ in 0..0usize {"],
  ["past-extend-call-clears-selection","src/edit.rs","fn extend_past(","crate::event_layer::extend_past(fact, selected, &TEXT_OPS.0)","crate::event_layer::extend_past(fact, Vec::new(), &TEXT_OPS.0)"],
  ["past-pass-call-skips-facts","src/edit.rs","fn past_pass(","crate::event_layer::past_pass(facts, selected, &TEXT_OPS.0)","crate::event_layer::past_pass(&[], selected, &TEXT_OPS.0)"],
  ["past-call-clears-roots","src/edit.rs","fn past(","crate::event_layer::past(facts, after, &TEXT_OPS.0)","crate::event_layer::past(facts, &[], &TEXT_OPS.0)"],
  ["past-drops-roots","src/event_layer.rs","fn past<","let mut selected = after_ids.to_vec();","let mut selected = Vec::new();"],
  ["past-invents-id","src/event_layer.rs","fn extend_past<","if has_id(&selected, &id(fact), ops) {","if true {"],
  ["past-membership-always-false","src/event_layer.rs","fn has_id<","if id_eq(&ids[i], wanted) {","if false {"],
  ["past-skips-predecessors","src/event_layer.rs","fn extend_past<","if has_id(&selected, &id(fact), ops) {","if false {"],
  ["past-skips-passes","src/event_layer.rs","fn past<","for _ in 0..facts.len() {","for _ in 0..0usize {"],
  ["past-closes-after-one-pass","src/event_layer.rs","fn past<","closed = selected.len() == before;","closed = true;"],
  ["past-pass-rescans-last","src/event_layer.rs","fn past_pass<","let i = facts.len() - 1 - offset;","let i = facts.len() - 1;"],
  ["past-guard-refuses-present","src/event_layer.rs","fn validate_after<","if !has_fact(facts, &after[i], ops)","if has_fact(facts, &after[i], ops)"],
  ["past-extension-refuses-selection","src/event_layer.rs","fn extend_past<","Ok(selected)","Err(internal())"],
  ["past-refuses-closure","src/event_layer.rs","fn past<","Ok(selected)","Err((ops.1.0)())"],
  ["duplicate-scan-skips-pairs","src/event_layer.rs","fn duplicate_ids<","if id_eq(&xs[i], &xs[j]) {","if false {"],
  ["scheduler-ready-skips-dependency","src/event_layer.rs","fn ready<","if has_id(done, &after[i], ops) {","if true {"],
  ["scheduler-reselects-done","src/event_layer.rs","fn choose_ready<","if has_id(done, &id(&facts[i]), ops) {","if false {"],
  ["scheduler-refuses-ready","src/event_layer.rs","fn choose_ready<","return Some(i);","return None;"],
  ["scheduler-checks-empty-after","src/event_layer.rs","fn choose_ready<","ready(after(&facts[i]), done, ops)","ready(&[], done, ops)"],
  ["scheduler-records-wrong-id","src/edit.rs","fn interpret_scheduled(","fact_id,","|_| EventId { writer: Writer::Alice, counter: 0 },"],
  ["scheduler-stops-early","src/event_shell.rs","fn scheduled<","for _ in 0..facts.len() {","for _ in 0..0usize {"],
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
export function prepareMutation(mode,sources) {
  assert(sources&&(typeof sources==='string'||typeof sources==='object'),'prepareMutation needs the actual sources');
  const definition=definitionByMode.get(mode);
  assert(definition,'mutation without a registered definition: '+mode);
  const [owner,header,needle,replacement]=definition;
  const source=typeof sources==='string'?sources:sources[owner];
  const at=scopedAnchor(source,header,needle,mode);
  const mutant=source.slice(0,at)+source.slice(at).replace(needle,replacement);
  assert.notEqual(mutant,source);
  return typeof sources==='string'?mutant:{...sources,[owner]:mutant};
}
export const theorems={
"stream-admission-skips-predecessor":"EventGraph.validated_stream_checks",
"stream-admission-skips-forbidden":"EventGraph.validated_stream_checks",
"stream-admission-swaps-forbidden-args":"EventGraph.validated_stream_checks",
"stream-text-omits-predecessor-policy":"EditWellFormed.successful_validation_has_stream_checks",
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
  'causal-validator-passes-empty':'EditWellFormed.successful_validation_has_stream_checks',
  'causal-accepts-missing':'EditWellFormed.dependency_validation_is_sound',
  'past-guard-refuses-present':'PastExact.present_dependencies_pass_guard',
  'past-extension-refuses-selection':'PastExact.extend_stored_selection_succeeds',
  'past-refuses-closure':'PastExact.fitting_closed_history_computes_past',
  'past-closes-after-one-pass':'PastExact.past_covers_bounded_predecessor_paths',
  'past-pass-rescans-last':'PastExact.past_pass_covers_edges',
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
theorems['past-extend-call-clears-selection']='EventGraphText.extend_past_is_text_call';
theorems['past-pass-call-skips-facts']='EventGraphText.past_pass_is_text_call';
theorems['past-call-clears-roots']='EventGraphText.past_is_text_call';
theorems['text-policy-swaps-eq-lt']='EventGraphText.text_policy_is_exact';
theorems['graph-policy-swaps-eq-lt']='EventGraph.graph_ops_preserve_callbacks';
theorems['admission-policy-swaps-errors']='EventGraph.event_ops_preserve_callbacks';
export const priorOwners={...theorems};
export const ownerMigrations={
  'past-skips-predecessors':['PastExact.extend_past_covers_predecessors','direct-predecessor coverage of the actual generic loop is shared; old concrete text statement remains'],
  'past-drops-roots':['PastExact.past_stays_in_closed_set','root-retention induction is shared; preserve the old concrete text law as a thin composition'],
  'past-invents-id':['PastExact.extend_past_preserves','the actual extend body is checked in the shared closed-set owner'],
  'past-skips-passes':['PastExact.past_covers_bounded_predecessor_paths','zero passes preserve closed-set soundness but violate completeness; keep the Rust range usize and require ordinary rejection in the depth owner, not an earlier true soundness law'],
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
export const mutationOwners=Object.fromEntries(modes.filter(mode=>mode!=='positive').map(mode=>[mode,{owner:theorems[mode],priorOwner:priorOwners[mode]??null,reason:ownerMigrations[mode]?.[1]??(priorOwners[mode]?'owning concrete statement retained':'additional generic-body or concrete-caller control'),source:definitionByMode.get(mode)[0]}]));

// The positive chain: its native baselines (after `cargo test --test edit_admit`) and its verification roots.
export const positiveRoots=['Nickel.EditDeleteComplete.fst','Nickel.EventGraph.fst','Nickel.EventGraphText.fst','Nickel.EventShell.fst','Nickel.EventClassifier.fst','Nickel.Spec.fst','Nickel.EditCausal.fst','Nickel.EditPastTotal.fst','Nickel.EditSchedule.fst','Nickel.EditBasis.fst','Nickel.EditReplay.fst'];
export const positiveBaselines=[
  {name:'basis',test:'basis_filter_tests'},
  {name:'operation',test:'operation_provenance_tests'},
  {name:'replay',test:'author_replay_tests'}];
export const cargoBase=['test','--offline','--locked','-p','nickel-crdt'];
// The native cargo arguments of a mode (the positive uses the default `--test edit_admit`).
export function nativeArgs(mode){return ['test','--offline','--locked','-p','nickel-crdt',...(mode.startsWith('stream-')?[]:(mode==='scheduler-forgets-completed-tree'?['--lib','operation_provenance_tests']:mode.startsWith('replay-')?['--lib','author_replay_tests']:mode.startsWith('basis-')?['--lib','basis_filter_tests']:((mode.startsWith('past-')||mode.startsWith('scheduler-'))?['--lib','causal_basis_tests']:['--test','edit_admit'])))];}
// The non-extraction verification root of a mutation mode (the positive verifies positiveRoots).
export function proofRoot(mode){return /^(PastExact|EventGraph|EventGraphText|EventShell|EventClassifier)\./.test(theorems[mode]??'')?'Nickel.'+theorems[mode].split('.')[0]+'.fst':mode==='positive'?'Nickel.Spec.fst':mode.startsWith('replay-')?'Nickel.EditReplay.fst':mode.startsWith('basis-')?'Nickel.EditBasis.fst':mode.startsWith('scheduler-')?'Nickel.EditSchedule.fst':['past-refuses-closure','duplicate-scan-skips-pairs'].includes(mode)?'Nickel.EditPastTotal.fst':mode.startsWith('past-')?'Nickel.EditPast.fst':['edit-success-reuses-counter','edit-commit-ignores-counter','edit-call-passes-old-counter'].includes(mode)?'Nickel.EditAtomic.fst':'Nickel.EditWellFormed.fst';}
export const verifyRoots=mode=>mode==='positive'?[...positiveRoots]:['Nickel_crdt.Edit.fst',proofRoot(mode)];
const sha=s=>createHash('sha256').update(s).digest('hex');
// Plan tuples. A mutation mode: owner theorem, expected ordinary rejection, exact roots, the mutated source
// file and its digest, cargo arguments and extraction. The positive: expected success, its roots, its cargo
// arguments and baselines. These are exactly what check-edit-proofs.mjs executes (it audits each run).
export function positivePlan(){
  return {id:'positive',kind:'positive',owner:null,expect:'verify',roots:verifyRoots('positive'),mutation:null,
    native:{cargoArgs:nativeArgs('positive'),baselines:positiveBaselines.map(b=>[...cargoBase,'--lib',b.test]),extraction:true}};
}
// The files a text plan export is built from (its source identity). Execution code itself (check-edit-proofs.mjs and
// its static imports) is handled by the selector's code-input rule, not by plan equality.
export const TEXT_PLAN_INPUTS=['scripts/edit-native-plans.mjs','scripts/mutation-scope.mjs','src/edit.rs','src/event_layer.rs','src/event_shell.rs'];
// The extraction identity control runs in every invocation that runs a mutation mode.
export const identityControlPlan=()=>({id:'extraction-identity-control',kind:'identity-control',modes:['scheduler-reselects-done','scheduler-refuses-ready']});
export function nativeModePlans(sources){
  return modes.filter(mode=>mode!=='positive').map((mode,index)=>{
    const [file]=definitionByMode.get(mode);
    return {id:mode,kind:'native-mode',index,owner:theorems[mode],expect:'reject',roots:verifyRoots(mode),
      mutation:[{file,sha256:sha(prepareMutation(mode,sources)[file])}],native:{cargoArgs:nativeArgs(mode),baselines:[],extraction:true}};
  });
}
export {mutationDefinitions,definitionByMode};

/** Exact-tuple audit: every executed unit has a plan, every plan was executed, and each executed unit equals its plan
 *  field for field (ids, kinds, expectations, roots, mutations, cargo arguments, baselines, owners). */
export function auditUnits(planned,executed){
  const byId=new Map();for(const plan of planned){assert(!byId.has(plan.id),'planned unit listed twice: '+plan.id);byId.set(plan.id,plan);}
  const ran=executed instanceof Map?executed:new Map(executed.map(unit=>[unit.id,unit]));
  for(const id of ran.keys())assert(byId.has(id),'hidden unit executed without a plan: '+id);
  for(const plan of planned)assert(ran.has(plan.id),'planned unit not executed: '+plan.id);
  for(const plan of planned)assert.deepEqual(ran.get(plan.id),plan,'executed unit differs from its plan: '+plan.id);
  return planned.length;
}
// Controls for the audit itself, on real plan tuples: a hidden unit, an unexecuted plan, changed roots under the
// same id, a wrong expectation, a different mutation digest and different cargo arguments must each be refused.
export function checkAuditControls(sources){
  const plans=[positivePlan(),...nativeModePlans(sources).slice(0,2)];
  const copy=x=>structuredClone(x);
  assert.equal(auditUnits(plans,plans.map(copy)),3);
  const hidden=[...plans.map(copy),copy(nativeModePlans(sources)[2])];
  assert.throws(()=>auditUnits(plans,hidden),/hidden unit executed without a plan/);
  assert.throws(()=>auditUnits(plans,plans.slice(1).map(copy)),/planned unit not executed: positive/);
  const tweak=(i,f)=>{const ran=plans.map(copy);f(ran[i]);return ran;};
  for(const [what,i,f] of [['changed roots',1,u=>{u.roots=[u.roots[0],'Nickel.EditAtomic.fst'];}],['wrong expectation',1,u=>{u.expect='verify';}],
    ['positive expectation',0,u=>{u.expect='reject';}],['mutation digest',2,u=>{u.mutation[0].sha256='0'.repeat(64);}],
    ['cargo arguments',1,u=>{u.native.cargoArgs=[...u.native.cargoArgs,'--release'];}],['baselines',0,u=>{u.native.baselines.pop();}],['owner',2,u=>{u.owner='EditAtomic.other';}]])
    assert.throws(()=>auditUnits(plans,tweak(i,f)),/executed unit differs from its plan/,what);
}
