// A bounded checkpoint gate, not full register validity/refinement or SEC.
// Exact tracked views + fresh actual source extraction + named ordinary controls.
import fs from 'node:fs/promises';
import path from 'node:path';
import assert from 'node:assert/strict';
import {fileURLToPath} from 'node:url';
import {verify,holdLock,runAsync,digest,put} from './proof-cache.mjs';
import {hasOrdinaryTheoremRejection} from './negative-proof-evidence.mjs';
import {assertReformedSource} from './proof-reform.mjs';
import {registerControlPlans} from './register-control-plans.mjs';
const root=fileURLToPath(new URL('..',import.meta.url));
const output=path.resolve(process.argv[2]??path.join(root,'.cache/register-proofs'));
const selected=process.argv.slice(3);
// `shard:<i>/<n>` (the text gate's convention) selects every negative mode whose index k in the
// combined list [...bodyModes, ...depModes] has k mod n == i; the positive always runs first, so
// n shards together run every negative exactly once, each after its own positive. Named modes may
// be added to a shard. `shard-coverage:<n>` builds both mode tables, checks that partition and
// proves nothing.
const shardArgs=selected.filter(a=>a.startsWith('shard'));
assert(shardArgs.length<=1,'use at most one shard selector');
let shard=null,coverageOnly=null;
if(shardArgs.length){
 const s=shardArgs[0],m=/^shard:(\d+)\/(\d+)$/.exec(s),c=/^shard-coverage:(\d+)$/.exec(s);
 assert(m||c,'malformed shard selector '+s);
 if(m){const i=Number(m[1]),n=Number(m[2]);assert(Number.isSafeInteger(i)&&Number.isSafeInteger(n)&&n>0&&i<n,'shard index out of range '+s);shard={i,n};}
 else{coverageOnly=Number(c[1]);assert(Number.isSafeInteger(coverageOnly)&&coverageOnly>0,'shard count out of range '+s);assert.equal(selected.length,1,'shard-coverage is exclusive');}
}
// `export-plans` (exclusive) writes <out>/plans.json from the exact plans the runner executes, then
// exits before any extraction or proof.
const exportPlans=selected.includes('export-plans');
assert(!exportPlans||selected.length===1,'export-plans is exclusive');
// `selection:<file>` runs what a selector record (scripts/select-affected.mjs) chose, optionally split by a
// shard. Before any extraction the record must match this tree's own plan export exactly; see below.
const selectionArgs=selected.filter(a=>a.startsWith('selection:'));
assert(selectionArgs.length<=1,'use at most one selection');
const selectionFile=selectionArgs.length?selectionArgs[0].slice('selection:'.length):null;
const named=selected.filter(a=>!a.startsWith('shard')&&!a.startsWith('selection:')&&a!=='export-plans');
assert(!selectionFile||(selectionFile.length>0&&named.length===0&&!exportPlans&&coverageOnly===null),'selection combines only with a shard');
let wanted=(name,k)=>name==='positive'||!selected.length||named.includes(name)||(shard!==null&&k%shard.n===shard.i);
function shardPartition(names,n){
 assert.equal(new Set(names).size,names.length,'negative mode names are unique');
 const parts=Array.from({length:n},(_,i)=>names.filter((_,k)=>k%n===i));
 for(const [i,p] of parts.entries())assert(p.length>0,'shard '+i+'/'+n+' selects no negative mode');
 const union=parts.flat();assert.equal(union.length,names.length,'shards cover each negative exactly once');
 assert.deepEqual([...union].sort(),[...names].sort(),'shards cover every negative');
 return parts;
}
let ranNegatives=0;
// The CI matrix must list exactly register-proofs-shard-0..n-1, each once.
function checkCiShards(workflow,n){
 const line=workflow.split('\n').find(l=>/^\s*target:\s*\[/.test(l));assert(line,'ci matrix target list');
 // YAML inline-list entries may be bare or wrapped in one matching pair of quotes; any other
 // quote character (unmatched or embedded) refuses, so quoting cannot hide an entry.
 const targets=line.slice(line.indexOf('[')+1,line.lastIndexOf(']')).split(',').map(s=>s.trim().replace(/^(['"])(.*)\1$/,'$2'));
 for(const t of targets)assert(!/['"]/.test(t),'unsupported quoting in ci matrix entry '+t);
 const shards=targets.filter(t=>/^register-proofs-shard-/.test(t));
 for(const t of shards)assert(/^register-proofs-shard-(0|[1-9]\d*)$/.test(t),'malformed ci register shard '+t);
 assert.equal(new Set(shards).size,shards.length,'ci lists a register shard twice');
 assert.deepEqual([...shards].sort(),Array.from({length:n},(_,i)=>'register-proofs-shard-'+i).sort(),'ci must list exactly register-proofs-shard-0..'+(n-1));
 assert(!targets.includes('register-proofs'),'ci must not also run the unsharded register gate');
}
await fs.mkdir(output,{recursive:true});
assert(holdLock(path.join(output,'register-proofs.lock')),'register proof output is owned by another invocation');
const env=process.env;
for(const k of ['NICKEL_HAX_BIN','NICKEL_PROOF_FSTAR','NICKEL_HAX_SOURCE','NICKEL_FSTAR_MODEL_CACHE'])assert(env[k],k);
const views=path.join(root,'proofs/register-view');
const receipt=JSON.parse(await fs.readFile(path.join(views,'receipt.json'),'utf8'));
const required=['Cargo.toml','Cargo.lock','src/lib.rs','src/register.rs','src/causal.rs','src/event_layer.rs','src/event_shell.rs','proofs/Register.lt','proofs/RegisterPast.lt','proofs/RegisterHistory.lt','proofs/RegisterValid.lt','proofs/RegisterPublic.lt','proofs/RegisterFrontier.lt','proofs/Canonical.lt','proofs/Vector.lt','proofs/EventGraph.lt','proofs/EventClassifier.lt',
 'proofs/Prelude.lt','proofs/LoopUtil.lt','proofs/EventShell.lt','proofs/CausalEnvelope.lt',
 'proofs/generated/Nickel.Vector.fst','proofs/generated/Nickel.EventGraph.fst','proofs/generated/Nickel.EventClassifier.fst','proofs/generated/Nickel.Prelude.fst','proofs/generated/Nickel.LoopUtil.fst','proofs/generated/Nickel.EventShell.fst',
 'proofs/causal-envelope-view/Nickel.CausalEnvelope.fst',
 'proofs/register-view/Nickel.Canonical.fst','proofs/register-view/Nickel.RegisterPast.fst','proofs/register-view/Nickel.RegisterHistory.fst','proofs/register-view/Nickel.RegisterValid.fst','proofs/register-view/Nickel.RegisterPublic.fst','proofs/register-view/Nickel.RegisterFrontier.fst',
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
assertReformedSource('RegisterFrontier',await fs.readFile(path.join(root,'proofs/RegisterFrontier.lt'),'utf8'));
assert.throws(()=>assertReformedSource('RegisterFrontier','Tactics.prune("Nickel_crdt.Register");'),'no broad frontier native namespace');
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
const frontierView=await fs.readFile(path.join(views,'Nickel.RegisterFrontier.fst'),'utf8');
for(const checkedView of [view,canonicalView,pastView,historyView,validView,publicView,frontierView])assert(!/\b(?:admit|assume|lax|admit_smt_queries)\b/.test(checkedView));
if(env.NICKEL_LATTE_BIN){
 const rf=await runAsync('frontier meaning producer',env.NICKEL_LATTE_BIN,['emit-fstar',path.join(root,'proofs/RegisterFrontier.lt')],root,{env});assert.equal(rf.status,0);assert.equal(rf.stdout,frontierView,'complete register frontier producer/view parity');
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
const plans=registerControlPlans({source,graphSource,view,loopView,canonicalView,pastView,historyView,validView,publicView,frontierView});
const bodyModes=plans.body,depModes=plans.dep;
const viewByModule={'Nickel.Register':view,'Nickel.LoopUtil':loopView,'Nickel.Canonical':canonicalView,'Nickel.RegisterPast':pastView,'Nickel.RegisterHistory':historyView,'Nickel.RegisterValid':validView,'Nickel.RegisterPublic':publicView,'Nickel.RegisterFrontier':frontierView};
// Focused modes are validated against the constructed plans themselves, so a new plan is selectable.
const planNames=new Set([...bodyModes,...depModes].map(p=>p.name));
assert(named.every(n=>n==='positive'||planNames.has(n)),'unknown selected mode');
const haxArgs=out=>['-C','--offline','--locked','-p','nickel-crdt',';','into','--output-dir',out,'-i','-** +nickel_crdt::register::**::new +nickel_crdt::register::**::write +nickel_crdt::register::**::receive +nickel_crdt::register::**::read +nickel_crdt::register::winner +nickel_crdt::register::later +nickel_crdt::register::bytes_equal +nickel_crdt::register::next_lamport +nickel_crdt::register::less_id +nickel_crdt::event_shell::receive +nickel_crdt::causal::classify +nickel_crdt::event_layer::**','fstar'];
const inventory=['Nickel_crdt.Causal.fst','Nickel_crdt.Event_layer.fst','Nickel_crdt.Event_shell.fst','Nickel_crdt.Register.fst'];
const proofFiles=['Nickel.Prelude.fst','Nickel.LoopUtil.fst','Nickel.EventShell.fst','Nickel.Vector.fst','Nickel.EventGraph.fst','Nickel.EventClassifier.fst'];
async function support(dir){
 await fs.mkdir(dir,{recursive:true});
 for(const f of proofFiles)await put(path.join(dir,f),await fs.readFile(path.join(root,'proofs/generated',f)));
 await put(path.join(dir,'Nickel.Canonical.fst'),canonicalView);
 await put(path.join(dir,'Nickel.RegisterFrontier.fst'),frontierView);
 await put(path.join(dir,'Nickel.RegisterPast.fst'),pastView);
 await put(path.join(dir,'Nickel.CausalEnvelope.fst'),await fs.readFile(path.join(root,'proofs/causal-envelope-view/Nickel.CausalEnvelope.fst')));
}
async function check(dir,roots,log){
 const r=await verify({dir,roots:roots.map(f=>path.join(dir,f)),fstar:env.NICKEL_PROOF_FSTAR,models:env.NICKEL_HAX_SOURCE,modelCache:env.NICKEL_FSTAR_MODEL_CACHE});
 await fs.writeFile(log,r.log);return r;
}
const positive=path.join(output,'positive/proof'),file=path.join(positive,'Nickel.Register.fst');
// Plan and validate the complete partition (and, for coverage, the CI matrix) before any
// extraction or proof runs.
const negativeNames=[...bodyModes.map(p=>p.name),...depModes.map(p=>p.name)];
async function exportText(){
 const describe=p=>({name:p.name,kind:p.kind,owner:p.owner,theorem:p.theorem,roots:p.roots,...(p.sourceFile?{sourceFile:p.sourceFile}:{}),...(p.module?{module:p.module}:{}),...(p.classifierModule?{classifierModule:p.classifierModule}:{}),mutated:p.mutated===null?null:digest(p.mutated)});
 // Source identity: the digest of every file the plans are built from, plus the code that builds and
 // exports them, so a selector can check an export against the commit it claims to describe.
 const planInputs=['scripts/check-register-proofs.mjs','scripts/register-control-plans.mjs','scripts/mutation-scope.mjs',
  'src/register.rs','src/event_layer.rs','proofs/generated/Nickel.LoopUtil.fst',
  ...['Canonical','Register','RegisterPast','RegisterHistory','RegisterValid','RegisterPublic','RegisterFrontier'].map(m=>'proofs/register-view/Nickel.'+m+'.fst')];
 const sources={};for(const f of planInputs)sources[f]=digest(await fs.readFile(path.join(root,f)));
 return JSON.stringify({schema:1,gate:'register',sources,plans:[plans.positive,...bodyModes,...depModes].map(describe)},null,1)+'\n';
}
if(exportPlans){
 await fs.writeFile(path.join(output,'plans.json'),await exportText());
 console.log('exported '+(bodyModes.length+depModes.length)+' negative plans and the positive to '+path.join(output,'plans.json'));
 process.exit(0);
}
if(coverageOnly){
 const parts=shardPartition(negativeNames,coverageOnly);
 if(env.NICKEL_CI_WORKFLOW)checkCiShards(await fs.readFile(env.NICKEL_CI_WORKFLOW,'utf8'),coverageOnly);
 console.log('shard coverage: '+negativeNames.length+' negatives over '+coverageOnly+' shards: '+parts.map(p=>p.length).join('/'));
 process.exit(0);
}
// Selection consumer. The record is refused unless it was made from exactly this tree's plans (its
// headPlans digest equals this runner's own export), is not diagnostic, and names only known modes
// with a known run value. full runs as if unselected; none runs nothing; selected runs the named
// negatives (split by shard index like unselected runs) and the positive in every shard that runs
// one (dependency controls reuse the positive's workspace), or in shard 0 for a positive-only record.
let selection=null;
if(selectionFile){
 let rec;try{rec=JSON.parse(await fs.readFile(selectionFile,'utf8'));}catch(e){assert.fail('selection record unreadable: '+e.message);}
 const keys=['schema','base','head','diagnosticOnly','basePlans','headPlans','full','reasons','affected','register','text','shared'];
 assert(rec&&typeof rec==='object'&&!Array.isArray(rec)&&Object.keys(rec).length===keys.length&&keys.every(k=>Object.hasOwn(rec,k)),'selection record has an unrecognised shape');
 assert.equal(rec.schema,1,'selection record schema');
 assert.equal(rec.diagnosticOnly,false,'a diagnostic selection record cannot be consumed');
 assert.equal(rec.headPlans,digest(await exportText()),'selection record was not made for this tree (head plan export differs)');
 const reg=rec.register;assert(reg&&typeof reg==='object'&&!Array.isArray(reg),'selection record register entry');
 assert(rec.full===true||rec.full===false,'selection record full flag');
 if(rec.full||reg.run==='full'){assert.deepEqual(Object.keys(reg),['run'],'a full register selection carries only run');assert.equal(reg.run,'full','a full record selects the full register gate');selection={run:'full'};}
 else{
  const rkeys=['run','positive','modes','why','removed','total'];
  assert(Object.keys(reg).length===rkeys.length&&rkeys.every(k=>Object.hasOwn(reg,k)),'selection record register entry has an unrecognised shape');
  assert(Array.isArray(reg.modes)&&reg.modes.every(m=>typeof m==='string'),'selection modes');
  assert.equal(new Set(reg.modes).size,reg.modes.length,'selection names a mode twice');
  for(const m of reg.modes)assert(planNames.has(m),'selection names unknown mode '+m);
  assert.equal(reg.total,negativeNames.length,'selection record counts a different plan total');
  if(reg.run==='none'){assert(reg.positive===null&&reg.modes.length===0,'a none selection runs nothing');selection={run:'none',modes:new Set()};}
  else if(reg.run==='selected'){assert(typeof reg.positive==='string'&&reg.positive.length>0,'a selected record runs the positive');selection={run:'selected',modes:new Set(reg.modes)};}
  else assert.fail('unknown selection run '+String(reg.run));
 }
 if(selection.run==='full')wanted=(name,k)=>name==='positive'||shard===null||k%shard.n===shard.i;
 else{
  const inShard=k=>shard===null||k%shard.n===shard.i;
  const mine=new Set(negativeNames.filter((n,k)=>selection.modes.has(n)&&inShard(k)));
  const runPositive=mine.size>0||(selection.run==='selected'&&selection.modes.size===0&&(shard===null||shard.i===0));
  wanted=(name,k)=>name==='positive'?runPositive:mine.has(name);
  console.log('selection '+selection.run+': '+mine.size+' of '+selection.modes.size+' selected negatives here'+(runPositive?' plus the positive':''));
  if(!runPositive){await fs.writeFile(path.join(output,'results.json'),'[]\n');console.log('selection runs nothing in this job');process.exit(0);}
 }
}
// A shard may be combined with named modes: it runs the union, each negative once.
const planned=new Set(negativeNames.filter((n,k)=>wanted(n,k)));
console.log('planned '+planned.size+' negatives'+(wanted('positive',-1)?' after the positive':''));
if(shard){const parts=shardPartition(negativeNames,shard.n);console.log('shard '+shard.i+'/'+shard.n+': '+parts[shard.i].length+' of '+negativeNames.length+' negatives'+(named.length?' plus '+named.filter(n=>n!=='positive').length+' named':''));}
const results=[];
for(const plan of [plans.positive,...bodyModes]){
 const {name,owner}=plan,header=plan.kind==='body';
 if(!wanted(name,bodyModes.findIndex(p=>p.name===name)))continue;
 if(name!=='positive')ranNegatives++;
 const mode=path.join(output,name),crate=path.join(mode,'crate'),extract=path.join(mode,'extract'),dir=path.join(mode,'proof');
 await fs.mkdir(crate,{recursive:true});await fs.cp(path.join(root,'src'),path.join(crate,'src'),{recursive:true,force:true});
 for(const f of ['Cargo.toml','Cargo.lock'])await fs.copyFile(path.join(root,f),path.join(crate,f));
 await fs.cp(path.join(root,'proof-smoke'),path.join(crate,'proof-smoke'),{recursive:true,force:true});
 const sourceFile=plan.sourceFile,changed=header?plan.mutated:source;if(header)await fs.writeFile(path.join(crate,sourceFile),changed);
 await fs.rm(extract,{recursive:true,force:true});await fs.mkdir(extract,{recursive:true});
 const r=await runAsync(name+' extraction',env.NICKEL_HAX_BIN,haxArgs(extract),crate,{env:{...env,CARGO_TARGET_DIR:path.join(mode,'target')}});
 await fs.writeFile(path.join(mode,'extraction.log'),r.log);assert.equal(r.status,0,name+': extraction failed');
 assert.deepEqual((await fs.readdir(extract)).filter(f=>/\.fsti?$/.test(f)).sort(),inventory);
 await support(dir);
 for(const f of inventory){const b=await fs.readFile(path.join(extract,f));assert(!/assume\s+val/.test(b.toString()),name+': assumed native body');if(!header)assert(b.equals(await fs.readFile(path.join(views,f))),'fresh production native identity: '+f);await put(path.join(dir,f),b);}
 const native=await check(dir,['Nickel_crdt.Register.fst'],path.join(mode,'native-typecheck.log'));assert.equal(native.status,0,name+': native type error is not owner rejection');
 const file=path.join(dir,'Nickel.Register.fst');await put(file,view);await put(path.join(dir,'Nickel.RegisterHistory.fst'),historyView);await put(path.join(dir,'Nickel.RegisterValid.fst'),validView);await put(path.join(dir,'Nickel.RegisterPublic.fst'),publicView);
 const checked=await check(dir,plan.roots,path.join(mode,'proof.log'));
 const ordinary=owner?hasOrdinaryTheoremRejection({status:checked.status,log:checked.log,theorem:plan.theorem,view:viewByModule[plan.classifierModule]}):null;
 if(owner)assert(ordinary,name+': ordinary named owner rejection required');else assert.equal(checked.status,0,'checkpoint positive failed');
 results.push({name,owner,status:checked.status,ordinary,sourceFile,source:digest(changed),log:digest(checked.log)});
 console.log('PASS '+name);
}
for(const plan of depModes){
 const {name,owner}=plan,changed=plan.mutated;
 if(!wanted(name,bodyModes.length+depModes.findIndex(p=>p.name===name)))continue;
 ranNegatives++;
 const baseView=viewByModule[plan.module],ownerFile=path.join(positive,plan.module+'.fst');
 await fs.writeFile(path.join(output,name+'.fst'),changed);
 try{await put(ownerFile,changed);const r=await check(positive,plan.roots,path.join(output,name+'.log'));const ordinary=hasOrdinaryTheoremRejection({status:r.status,log:r.log,theorem:plan.theorem,view:changed});assert(ordinary,name+': checked callee dependence required');results.push({name,owner,status:r.status,ordinary,view:digest(changed),log:digest(r.log)});console.log('PASS '+name);}
 finally{await put(ownerFile,baseView);}
}
if(shard||selection)assert.equal(ranNegatives,planned.size,'job ran exactly its planned negatives');
await fs.writeFile(path.join(output,'results.json'),JSON.stringify(results,null,2)+'\n');
console.log('checkpoint claims only; full register refinement/validity and SEC remain open');
