// Actual edit/admit extraction: return paths, commit coherence and identity laws.
// This gate does not prove valid-fact acceptance, convergence or FugueMax.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {digest,run,verify,put} from './proof-cache.mjs';
const root=fileURLToPath(new URL('..',import.meta.url));
const {NICKEL_HAX_BIN:hax,NICKEL_PROOF_FSTAR:fstar,NICKEL_HAX_SOURCE:models,NICKEL_FSTAR_MODEL_CACHE:modelCache}=process.env;
assert(hax&&fstar&&models&&modelCache,'use the locked .#proofs environment');
const output=process.argv[2];assert(output,'output directory required');
await fs.mkdir(output,{recursive:true});
const identity=JSON.parse(await fs.readFile(path.join(modelCache,'identity.json'),'utf8'));
assert.equal(identity.models,models);assert.equal(identity.fstar,fstar);
const views=new Map();
for(const name of ['Prelude','LoopUtil','EditAtomic','EditCommit','EditIdentity','EditAccepted']) {
  const source=`proofs/${name}.lt`,view=`proofs/generated/Nickel.${name}.fst`;
  const code=await fs.readFile(path.join(root,view),'utf8');
  const receipt=(await fs.readFile(path.join(root,`proofs/generated/${name}.sha256`),'utf8')).trim().split('\n');
  assert.deepEqual(receipt,[digest(await fs.readFile(path.join(root,source)))+'  '+source,digest(code)+'  '+view]);
  assert(!/\b(?:admit|admit_smt_queries|assume|lax)\b/.test(code),'no authored admissions');
  views.set(`Nickel.${name}.fst`,code);
}
const original=await fs.readFile(path.join(root,'src/edit.rs'),'utf8');
const modes=['positive','local-return-after','edit-call-passes-old-counter','edit-commit-ignores-counter','receive-error-corrupts-counter','edit-error-corrupts-counter','edit-success-reuses-counter',
  'local-return-gap','local-stale-tree','receive-success-counter','author-forgets-gap','receive-private-gate',
  'identity-forgets-gap','identity-accepts-conflict','identity-skips-later','identity-counter-range','identity-event-equality',
  'identity-scan-key','identity-birth-equality','identity-writer-equality',
  'accepted-reuses-member','accepted-wrong-canonical-push','accepted-publication-duplicates',
  'content-changes-whole-fact','content-omits-facts'];
const selected=process.argv.slice(3);for(const mode of selected)assert(modes.includes(mode),'unknown mode '+mode);
let positive;
for(const mode of selected.length?selected:modes) {
  const work=path.join(root,'.cache','edit-proofs',mode),crate=path.join(work,'crate'),proof=path.join(work,'proof');
  await fs.mkdir(crate,{recursive:true});await fs.mkdir(proof,{recursive:true});
  for(const name of ['Cargo.toml','Cargo.lock','src','tests','proof-smoke'])await fs.cp(path.join(root,name),path.join(crate,name),{recursive:true});
  if(mode!=='positive') {
    const scopes={'edit-commit-ignores-counter':'fn with_counter(', 'edit-success-reuses-counter':'fn next_counter_after(', 'content-changes-whole-fact':'fn clone_selected_fact(', 'content-omits-facts':'fn canonical(', 'accepted-reuses-member':'fn choose_unseen(', 'accepted-wrong-canonical-push':'fn canonical_step(', 'accepted-publication-duplicates':'fn with_tree('};
    const start=original.indexOf(scopes[mode]??(mode==='identity-writer-equality'?'impl PartialEq for Writer':mode==='identity-birth-equality'?'impl PartialEq for BirthId':mode==='identity-event-equality'?'impl PartialEq for EventId':mode==='identity-forgets-gap'?'fn fact_equal(':mode.startsWith('identity-')?'fn duplicate(':mode==='receive-private-gate'?'fn plan(':mode.startsWith('receive')?'pub fn receive(':'pub fn edit('));assert(start>=0);
    const edits={
      'edit-call-passes-old-counter':['next = next.with_counter(next_counter);', 'next = next.with_counter(self.next_counter);'],
      'local-return-after':['(next, Ok(Local::Authored(fact)))','{ let mut changed = fact; changed.after = Vec::new(); (next, Ok(Local::Authored(changed))) }'],
      'edit-commit-ignores-counter':['self.next_counter = counter;', 'self.next_counter = self.next_counter;'],
      'content-changes-whole-fact':['fact.clone()', 'let mut changed = fact.clone(); changed.gap = None; changed'],
      'content-omits-facts':['for _ in 0..facts.len() {', 'for _ in 0..0 {'],
      'accepted-reuses-member':['if !has_fact(out, facts[j].id) {','if true {'],
      'accepted-wrong-canonical-push':['push(&mut out, clone_selected_fact(&facts[i]))?;','push(&mut out, clone_selected_fact(&facts[0]))?;'],
      'accepted-publication-duplicates':['self.tree = tree;','self.tree = tree; if !self.facts.is_empty() && self.facts.len() < usize::MAX { let copy = self.facts[0].clone(); self.facts.push(copy); }'],
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
    const [needle,replacement]=edits[mode];const at=original.indexOf(needle,start);assert(at>=start);
    const mutant=original.slice(0,at)+original.slice(at).replace(needle,replacement);
    await fs.writeFile(path.join(crate,'src/edit.rs'),mutant);
  }
  const env={...process.env,CARGO_TARGET_DIR:path.join(root,'target','edit-proof-check')};
  const native=run('edit native '+mode,'cargo',['test','--offline','--locked','-p','nickel-crdt','--test','edit_admit'],crate,{env});
  await fs.writeFile(path.join(output,mode+'.native.log'),native.log);
  if(mode==='positive')assert.equal(native.status,0,native.log);
  else {assert.equal(native.status,101,native.log);assert.match(native.log,/test result: FAILED/);}
  const extracted=run('edit hax '+mode,hax,['-C','--offline','--locked','-p','nickel-crdt',';','into','--output-dir',proof,'-i','-** +nickel_crdt::edit::**::receive +nickel_crdt::edit::**::edit +nickel_crdt::edit::**::new','fstar'],crate,{env});
  await fs.writeFile(path.join(output,mode+'.hax.log'),extracted.log);
  assert.equal(extracted.status,0,extracted.log);
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
  // Counter calculation/installation/wiring controls need only their owning module. The positive path still
  // checks the complete public proof chain through EditAccepted.
  const proofRoot=['edit-success-reuses-counter','edit-commit-ignores-counter','edit-call-passes-old-counter'].includes(mode)?'Nickel.EditAtomic.fst':'Nickel.EditAccepted.fst';
  const checked=await verify({dir:proof,roots:[path.join(proof,proofRoot)],fstar,models,modelCache});
  await fs.writeFile(path.join(output,mode+'.proof.log'),checked.log);
  if(mode==='positive') {
    assert.equal(checked.status,0,checked.log);
    await fs.copyFile(path.join(proof,'Nickel_crdt.Edit.fst'),path.join(output,'Nickel_crdt.Edit.fst'));
  } else {
    assert.equal(checked.status,2,'require ordinary proof rejection, not extraction failure/timeout');
    const theorems={
      'edit-call-passes-old-counter':'EditAtomic.authored_edit_advances_once',
      'local-return-after':'EditCommit.authored_fact_replays_same_commit',
      'edit-commit-ignores-counter':'EditAtomic.counter_installation_is_exact',
      'content-changes-whole-fact':'EditAccepted.selected_fact_is_exact',
      'content-omits-facts':'EditAccepted.canonical_selects_whole_facts',
      'accepted-reuses-member':'EditAccepted.selected_id_is_unseen',
      'accepted-wrong-canonical-push':'EditAccepted.canonical_step_preserves_unique',
      'accepted-publication-duplicates':'EditAccepted.tree_installation_preserves_facts',
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
      'receive-success-counter':'EditCommit.receive_preserves_private_state',
      'author-forgets-gap':'EditCommit.authored_fact_binds_request',
      'receive-private-gate':'EditCommit.admission_ignores_private_state',
    };
    assert(checked.log.split('\n').some(line=>{
      if(!line.includes('Query-stats (Nickel.'+theorems[mode]+',')||!line.includes('failed'))return false;
      if(/reason-unknown=[^}]*?(?:canceled|resource limits reached|timeout)/i.test(line))return false;
      const budget=line.match(/and rlimit (\d+) \(used rlimit ([\d.]+)\)/);
      return budget&&Number(budget[2])<Number(budget[1]);
    }),'require a named non-resource proof rejection, not solely solver exhaustion: '+checked.log);
    assert.match(checked.log,/Could not prove post-condition|Assertion failed/);
  }
  console.log(`PASS ${mode}: native and unchanged actual-Rust theorem ${mode==='positive'?'verified':'reject the mutation'}`);
}
