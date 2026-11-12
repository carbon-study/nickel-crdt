// A bounded checkpoint gate, not full register validity/refinement or SEC.
// Exact tracked views + fresh actual source extraction + named ordinary controls.
import fs from 'node:fs/promises';
import path from 'node:path';
import assert from 'node:assert/strict';
import {fileURLToPath} from 'node:url';
import {verify,holdLock,runAsync,digest,put} from './proof-cache.mjs';
import {scopedAnchor} from './mutation-scope.mjs';
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
const required=['Cargo.toml','Cargo.lock','src/lib.rs','src/register.rs','src/causal.rs','src/event_layer.rs','src/event_shell.rs','proofs/Register.lt',
 'proofs/Prelude.lt','proofs/LoopUtil.lt','proofs/EventShell.lt','proofs/CausalEnvelope.lt',
 'proofs/generated/Nickel.Prelude.fst','proofs/generated/Nickel.LoopUtil.fst','proofs/generated/Nickel.EventShell.fst',
 'proofs/causal-envelope-view/Nickel.CausalEnvelope.fst',
 ...['Register','Nickel_crdt.Register','Nickel_crdt.Causal','Nickel_crdt.Event_layer','Nickel_crdt.Event_shell'].map(n=>'proofs/register-view/'+(n==='Register'?'Nickel.Register':n)+'.fst')];
assert.equal(receipt.schemaVersion,1);assert.deepEqual(Object.keys(receipt.files).sort(),required.sort(),'complete checkpoint receipt required');
for(const [f,h]of Object.entries(receipt.files))assert.equal(digest(await fs.readFile(path.join(root,f))),h,'stale checkpoint receipt: '+f);
assertReformedSource('Register',await fs.readFile(path.join(root,'proofs/Register.lt'),'utf8'));
assert.throws(()=>assertReformedSource('EditAccepted','Tactics.prune("Nickel_crdt.Register.bytes_equal");'),'new native visibility stays Register-scoped');
assert.throws(()=>assertReformedSource('EventGraph','Tactics.prune("Nickel.Register.planned_preserves_private");'),'write caller contract isolation stays Register-scoped');
assert.throws(()=>assertReformedSource('EventGraph','Tactics.prune("Nickel_crdt.Register.read_history");'),'payload callee visibility stays Register-scoped');
assert.throws(()=>assertReformedSource('Register','Tactics.norm([]);'),'no normalization exception');
assert.throws(()=>assertReformedSource('Register','Tactics.prune("Nickel_crdt.Register");'),'no broad native namespace exception');
const view=await fs.readFile(path.join(views,'Nickel.Register.fst'),'utf8');
assert(!/\b(?:admit|assume|lax|admit_smt_queries)\b/.test(view));
if(env.NICKEL_LATTE_BIN){
 const p=await runAsync('checkpoint producer',env.NICKEL_LATTE_BIN,['emit-fstar',path.join(root,'proofs/Register.lt')],root,{env});
 await fs.writeFile(path.join(output,'producer.log'),p.log);assert.equal(p.status,0);assert.equal(p.stdout,view,'full producer/view parity');
}
const source=await fs.readFile(path.join(root,'src/register.rs'),'utf8');
const bodyModes=[
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
assert(selected.every(n=>n==='positive'||bodyModes.some(m=>m[0]===n)||["without-validation-byte-contract","without-payload-validation-contract","without-payload-planning-contract","without-receive-payload-contract","without-added-publication-contract","without-write-receive-publication","without-write-receive-frame","without-winner-loop","without-read-winner","without-publication-contract","without-noedit-byte-contract","without-shared-planning-contract","without-prepare-frame","without-execute-frame","without-receive-publication-frame","without-plan-private-frame"].includes(n)),'unknown selected mode');
const haxArgs=out=>['-C','--offline','--locked','-p','nickel-crdt',';','into','--output-dir',out,'-i','-** +nickel_crdt::register::**::new +nickel_crdt::register::**::write +nickel_crdt::register::**::receive +nickel_crdt::register::**::read +nickel_crdt::register::winner +nickel_crdt::register::later +nickel_crdt::register::bytes_equal +nickel_crdt::register::next_lamport +nickel_crdt::event_shell::receive +nickel_crdt::causal::classify','fstar'];
const inventory=['Nickel_crdt.Causal.fst','Nickel_crdt.Event_layer.fst','Nickel_crdt.Event_shell.fst','Nickel_crdt.Register.fst'];
const proofFiles=['Nickel.Prelude.fst','Nickel.LoopUtil.fst','Nickel.EventShell.fst'];
async function support(dir){
 await fs.mkdir(dir,{recursive:true});
 for(const f of proofFiles)await put(path.join(dir,f),await fs.readFile(path.join(root,'proofs/generated',f)));
 await put(path.join(dir,'Nickel.CausalEnvelope.fst'),await fs.readFile(path.join(root,'proofs/causal-envelope-view/Nickel.CausalEnvelope.fst')));
}
async function check(dir,roots,log){
 const r=await verify({dir,roots:roots.map(f=>path.join(dir,f)),fstar:env.NICKEL_PROOF_FSTAR,models:env.NICKEL_HAX_SOURCE,modelCache:env.NICKEL_FSTAR_MODEL_CACHE});
 await fs.writeFile(log,r.log);return r;
}
const results=[];
for(const [name,header,anchor,replacement,owner] of [['positive',null,null,null,null],...bodyModes]){
 if(selected.length&&!selected.includes(name)&&name!=='positive')continue;
 const mode=path.join(output,name),crate=path.join(mode,'crate'),extract=path.join(mode,'extract'),dir=path.join(mode,'proof');
 await fs.mkdir(crate,{recursive:true});await fs.cp(path.join(root,'src'),path.join(crate,'src'),{recursive:true,force:true});
 for(const f of ['Cargo.toml','Cargo.lock'])await fs.copyFile(path.join(root,f),path.join(crate,f));
 await fs.cp(path.join(root,'proof-smoke'),path.join(crate,'proof-smoke'),{recursive:true,force:true});
 let changed=source;if(header){const at=scopedAnchor(source,header,anchor,name);changed=source.slice(0,at)+replacement+source.slice(at+anchor.length);await fs.writeFile(path.join(crate,'src/register.rs'),changed);}
 await fs.rm(extract,{recursive:true,force:true});await fs.mkdir(extract,{recursive:true});
 const r=await runAsync(name+' extraction',env.NICKEL_HAX_BIN,haxArgs(extract),crate,{env:{...env,CARGO_TARGET_DIR:path.join(mode,'target')}});
 await fs.writeFile(path.join(mode,'extraction.log'),r.log);assert.equal(r.status,0,name+': extraction failed');
 assert.deepEqual((await fs.readdir(extract)).filter(f=>/\.fsti?$/.test(f)).sort(),inventory);
 await support(dir);
 for(const f of inventory){const b=await fs.readFile(path.join(extract,f));assert(!/assume\s+val/.test(b.toString()),name+': assumed native body');if(!header)assert(b.equals(await fs.readFile(path.join(views,f))),'fresh production native identity: '+f);await put(path.join(dir,f),b);}
 const native=await check(dir,['Nickel_crdt.Register.fst'],path.join(mode,'native-typecheck.log'));assert.equal(native.status,0,name+': native type error is not owner rejection');
 const file=path.join(dir,'Nickel.Register.fst');await put(file,view);
 const checked=await check(dir,['Nickel.Register.fst'],path.join(mode,'proof.log'));
 const ordinary=owner?hasOrdinaryTheoremRejection({status:checked.status,log:checked.log,theorem:'Nickel.Register.'+owner,view}):null;
 if(owner)assert(ordinary,name+': ordinary named owner rejection required');else assert.equal(checked.status,0,'checkpoint positive failed');
 results.push({name,owner,status:checked.status,ordinary,source:digest(changed),log:digest(checked.log)});
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
const depModes=[
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
 try{await put(file,changed);const r=await check(positive,['Nickel.Register.fst'],path.join(output,name+'.log'));const ordinary=hasOrdinaryTheoremRejection({status:r.status,log:r.log,theorem:'Nickel.Register.'+owner,view:changed});assert(ordinary,name+': checked callee dependence required');results.push({name,owner,status:r.status,ordinary,view:digest(changed),log:digest(r.log)});console.log('PASS '+name);}
 finally{await put(file,view);}
}
await fs.writeFile(path.join(output,'results.json'),JSON.stringify(results,null,2)+'\n');
console.log('checkpoint claims only; full register refinement/validity and SEC remain open');
