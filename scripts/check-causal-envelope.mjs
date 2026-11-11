// Isolated actual-source extraction and one bounded generic classifier law.
// No old proof views, global manifests, pins, flags or classifiers are changed.
import fs from 'node:fs/promises';
import path from 'node:path';
import {createHash} from 'node:crypto';
import assert from 'node:assert/strict';
import {verify,holdLock,runAsync} from './proof-cache.mjs';
import {scopedAnchor} from './mutation-scope.mjs';
import {hasOrdinaryTheoremRejection} from './negative-proof-evidence.mjs';
const root=path.resolve(import.meta.dirname,'..');
const output=path.resolve(process.argv[2]??path.join(root,'.cache','causal-envelope'));
const latte=process.env.NICKEL_LATTE_BIN;
const env=process.env;
for(const k of ['NICKEL_HAX_BIN','NICKEL_PROOF_FSTAR','NICKEL_HAX_SOURCE','NICKEL_FSTAR_MODEL_CACHE'])assert(env[k],k);
await fs.mkdir(output,{recursive:true});
assert(holdLock(path.join(output,'causal-envelope.lock')),'another causal proof runner holds the permanent lock');
async function run(command,args,cwd,log,extra={}) {
 const r=await runAsync(path.basename(log),command,args,cwd,{env:{...env,...extra}});
 await fs.writeFile(log,r.log);assert.equal(r.status,0,command+' failed: '+log);
 return {...r,elapsedMs:r.seconds*1000};
}
function mutate(header,needle,replacement) {
 const at=scopedAnchor(source,header,needle,'causal envelope mutation');
 return source.slice(0,at)+replacement+source.slice(at+needle.length);
}
const digest=bytes=>createHash('sha256').update(bytes).digest('hex');
const support=path.join(output,'proof-support');await fs.mkdir(support,{recursive:true});
for(const f of ['Prelude.lt','LoopUtil.lt','CausalEnvelope.lt'])await fs.copyFile(path.join(root,'proofs',f),path.join(support,f));
await fs.writeFile(path.join(support,'latte.modules.json'),JSON.stringify({schemaVersion:1,module:'Nickel',modules:['*.lt'],prelude:'Nickel.Prelude'}));
const viewRoot=path.join(root,'proofs/causal-envelope-view');
const receipt=JSON.parse(await fs.readFile(path.join(viewRoot,'receipt.json'),'utf8'));
const requiredFiles=['proofs/CausalEnvelope.lt','proofs/causal-envelope-view/Nickel.CausalEnvelope.fst','proofs/causal-envelope-view/Nickel_crdt.Causal.fst','src/causal.rs','proofs/Prelude.lt','proofs/LoopUtil.lt','proofs/generated/Nickel.Prelude.fst','proofs/generated/Nickel.LoopUtil.fst'];
assert.equal(receipt.schemaVersion,1);assert.deepEqual(Object.keys(receipt.files).sort(),requiredFiles.sort(),'incomplete source/view receipt');
for(const [file,hash] of Object.entries(receipt.files))assert.equal(digest(await fs.readFile(path.join(root,file))),hash,'stale source/view receipt: '+file);
const emitted=await fs.readFile(path.join(viewRoot,'Nickel.CausalEnvelope.fst'),'utf8');
assert(!/\b(?:admit|assume|lax|admit_smt_queries)\b/.test(emitted),'authored admission in new view');
assert(!/\b(?:norm_spec|norm|delta_only|iota|zeta)\b/.test(await fs.readFile(path.join(root,'proofs/CausalEnvelope.lt'),'utf8')),'authored normalization in new source');
if(latte) {
 const actual=(await run(latte,['emit-fstar',path.join(support,'CausalEnvelope.lt')],root,path.join(output,'latte-emission.log'))).stdout;
 assert.equal(actual,emitted,'full MCP/producer accepted view differs from current producer');
}
await fs.writeFile(path.join(output,'producer-check.json'),JSON.stringify({mode:latte?'actual-full-reemission':'tracked-source-view-receipt',producer:latte??null},null,2));
const source=await fs.readFile(path.join(root,'src/causal.rs'),'utf8');
const modes=[['positive',source,null],
 ['payload-ignored',mutate('fn event_equal<P: Clone>','&& eq(&left.payload, &right.payload)','&& true'),'event_equal_exact'],
 ['dependencies-ignored',mutate('fn event_equal<P: Clone>','ids_eq(&left.after, &right.after)','true'),'event_equal_exact'],
 ['id-peer-ignored',mutate('fn eq(&self, other: &Self)','self.peer == other.peer && self.counter == other.counter','self.counter == other.counter'),'id_equal_exact'],
 ['ids-mismatch-accepted',mutate('fn ids_eq(', 'if left[i] != right[i] {\n            return false;', 'if left[i] != right[i] {\n            return true;'),'ids_eq_exact'],
 ['classifier-wrong-call',mutate('fn classify<P: Clone>','event_equal(&facts[i], fact, eq)','event_equal(fact, fact, eq)'),'classify_first_match'],
 ['none-on-match',mutate('fn classify<P: Clone>','return Some(event_equal(&facts[i], fact, eq));','return None;'),'classify_first_match']];
const results=[];
for(const [name,changed,owner] of modes) {
 if(name!=='positive')assert.notEqual(source,changed,'mutation absent: '+name);
 const mode=path.join(output,name),crate=path.join(mode,'crate'),dir=path.join(mode,'out'),extractDir=path.join(mode,'native-extract');
 await fs.mkdir(path.join(crate,'src'),{recursive:true});await fs.mkdir(dir,{recursive:true});
 await fs.rm(extractDir,{recursive:true,force:true});await fs.mkdir(extractDir,{recursive:true});
 await fs.writeFile(path.join(crate,'Cargo.toml'),'[package]\nname="nickel-crdt"\nversion="0.0.0"\nedition="2021"\n[workspace]\n');
 await fs.writeFile(path.join(crate,'src/lib.rs'),'pub mod causal;\n');await fs.writeFile(path.join(crate,'src/causal.rs'),changed);
 await run('cargo',['generate-lockfile','--offline'],crate,path.join(mode,'lock.log'));
 const extraction=await run(env.NICKEL_HAX_BIN,['-C','--offline','--locked',';','into','--output-dir',extractDir,'-i','-** +nickel_crdt::causal::classify +nickel_crdt::causal::event_equal +nickel_crdt::causal::ids_eq +nickel_crdt::causal::**::eq','fstar'],crate,path.join(mode,'extract.log'),{CARGO_TARGET_DIR:path.join(mode,'target-proof-hax')});
 const inventory=(await fs.readdir(extractDir)).filter(f=>/\.fsti?$/.test(f)).sort();
 assert.deepEqual(inventory,['Nickel_crdt.Causal.fst'],'unexpected native extraction inventory');
 const native=await fs.readFile(path.join(extractDir,inventory[0]),'utf8');
 assert(native.startsWith('module Nickel_crdt.Causal\n'));
 assert(!/assume\s+val/.test(native),'focused extraction contains assumed bodies');
 if(name==='positive')assert.equal(native,await fs.readFile(path.join(viewRoot,'Nickel_crdt.Causal.fst'),'utf8'),'actual extraction differs from retained focused native snapshot');
 await fs.rm(path.join(mode,'identity-target'),{recursive:true,force:true});
 const scratch=path.join(mode,'identity-extraction');await fs.rm(scratch,{recursive:true,force:true});await fs.mkdir(scratch,{recursive:true});
 await run(env.NICKEL_HAX_BIN,['-C','--offline','--locked',';','into','--output-dir',scratch,'-i','-** +nickel_crdt::causal::classify +nickel_crdt::causal::event_equal +nickel_crdt::causal::ids_eq +nickel_crdt::causal::**::eq','fstar'],crate,path.join(mode,'identity-extract.log'),{CARGO_TARGET_DIR:path.join(mode,'identity-target')});
 assert.deepEqual((await fs.readdir(scratch)).filter(f=>/\.fsti?$/.test(f)).sort(),inventory);
 assert.equal(await fs.readFile(path.join(scratch,inventory[0]),'utf8'),native,'independent fresh extraction differs');
 await fs.writeFile(path.join(mode,'extraction-receipt.json'),JSON.stringify({source:digest(changed),native:digest(native),inventory},null,2));
 await fs.copyFile(path.join(extractDir,inventory[0]),path.join(dir,inventory[0]));
 for(const f of ['Nickel.Prelude.fst','Nickel.LoopUtil.fst'])await fs.copyFile(path.join(root,'proofs/generated',f),path.join(dir,f));
 const proof=path.join(dir,'Nickel.CausalEnvelope.fst');await fs.writeFile(proof,emitted);
 const started=performance.now(),r=await verify({dir,roots:[proof],fstar:env.NICKEL_PROOF_FSTAR,models:env.NICKEL_HAX_SOURCE,modelCache:env.NICKEL_FSTAR_MODEL_CACHE});
 await fs.writeFile(path.join(mode,'verify.log'),r.log);
 const ordinary=owner?hasOrdinaryTheoremRejection({status:r.status,log:r.log,theorem:'Nickel.CausalEnvelope.'+owner,view:emitted}):null;
 const result={name,status:r.status,ordinary,extractionMs:extraction.elapsedMs,proofMs:performance.now()-started};results.push(result);
 await fs.writeFile(path.join(output,'proof-results.json'),JSON.stringify(results,null,2));console.log(JSON.stringify(result));
 if(!owner)assert.equal(r.status,0,'positive proof failed');else assert(ordinary,'require ordinary named owner rejection');
}

// Callee contract dependence is distinct from wrong-body sensitivity.
function once(view,needle,replacement) {
 assert.equal(view.split(needle).length,2,'ambiguous proof control anchor');
 return view.replace(needle,replacement);
}
const contractless=once(once(emitted,
 '  ids_eq_exact (Alloc.Vec.impl_1__as_slice left.f_after) (Alloc.Vec.impl_1__as_slice right.f_after);','  ();'),
 '    Tactics.prune "Nickel_crdt.Causal.ids_eq";',
 '    Tactics.prune "Nickel_crdt.Causal.ids_eq";\n    Tactics.prune "Nickel.CausalEnvelope.ids_eq_exact";');
const rangeLine=emitted.split('\n').find(line=>line.startsWith('  Nickel.LoopUtil.preserve_any #unit #(Option.t_Option bool)'));
assert(rangeLine,'missing exact classifier range-contract call');
const rangeless=once(emitted,rangeLine,'  ();');
const idsRangeLine=emitted.split('\n').find(line=>line.includes('Nickel.LoopUtil.preserve_any #unit #bool '));
assert(idsRangeLine,'missing exact dependency equality range-contract call');
const idsRangeless=once(emitted,idsRangeLine,'    begin ();');
for(const [name,view,owner] of [['without-ids-contract',contractless,'event_equal_exact'],['without-range-contract',rangeless,'classify_first_match'],['without-ids-range-contract',idsRangeless,'ids_eq_exact']]) {
 const dir=path.join(output,name);await fs.mkdir(dir,{recursive:true});
 for(const f of ['Nickel_crdt.Causal.fst','Nickel.Prelude.fst','Nickel.LoopUtil.fst'])await fs.copyFile(path.join(output,'positive','out',f),path.join(dir,f));
 const file=path.join(dir,'Nickel.CausalEnvelope.fst');await fs.writeFile(file,view);
 const started=performance.now(),r=await verify({dir,roots:[file],fstar:env.NICKEL_PROOF_FSTAR,models:env.NICKEL_HAX_SOURCE,modelCache:env.NICKEL_FSTAR_MODEL_CACHE});
 await fs.writeFile(path.join(dir,'verify.log'),r.log);
 const ordinary=hasOrdinaryTheoremRejection({status:r.status,log:r.log,theorem:'Nickel.CausalEnvelope.'+owner,view});
 const row={name,status:r.status,ordinary,proofMs:performance.now()-started};results.push(row);
 await fs.writeFile(path.join(output,'proof-results.json'),JSON.stringify(results,null,2));console.log(JSON.stringify(row));assert(ordinary,'require ordinary callee-contract removal owner rejection');
}
