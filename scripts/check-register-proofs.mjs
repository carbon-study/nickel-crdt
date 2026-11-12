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
 ['copy-changes-key','fn copy_fact(','f.clone()','{ let mut copy = f.clone(); copy.payload.key = 0; copy }','copy_fact_is_exact'],
 ['bytes-accept-mismatch','pub fn bytes_equal(','if a[i] != b[i] { return false; }','if a[i] != b[i] { return true; }','bytes_equal_exact'],
 ['priority-reverses-clock','pub fn later(','a.payload.lamport > b.payload.lamport','a.payload.lamport < b.payload.lamport','later_is_priority'],
 ['noedit-counted','pub fn write(','if bytes_equal(&value, &observed)','if false','equal_value_write_is_neutral'],
 ['receive-error-corrupts-counter','pub fn receive(','shell::receive_into(self, &fact, &(), planned, Admission::Added, Admission::Duplicate)','let result = shell::receive_into(self, &fact, &(), planned, Admission::Added, Admission::Duplicate); if result.is_err() { self.next_counter = 0; } result','receive_publication_is_exact'],
 ['read-wrong-key','pub fn read(','read_history(&self.facts, &self.initial, key)','read_history(&self.facts, &self.initial, 0)','public_read_is_history'],
 ['payload-ignores-observed','fn write_equal(','&& bytes_equal(&a.observed, &b.observed)','&& true','write_equal_is_exact'],
];
assert(selected.every(n=>n==='positive'||bodyModes.some(m=>m[0]===n)||['without-winner-loop','without-read-winner','without-publication-contract','without-noedit-byte-contract'].includes(n)),'unknown selected mode');
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
const loopLine=view.split('\n').find(l=>l.startsWith('  Nickel.LoopUtil.plain_preserve_any #(Option.t_Option usize)'));
assert(loopLine,'actual winner loop contract');
const depModes=[
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
