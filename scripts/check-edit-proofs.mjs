import {checkFstarMutationScope} from './check-fstar-mutation-scope.mjs';
import {checkDeletePreparation,editProofHaxArgs} from './check-delete-contracts.mjs';
import {itemSpan,scopedAnchor,checkMutationScopeControls} from './mutation-scope.mjs';
// Actual edit/admit extraction: return paths, commit coherence and identity laws.
// This gate does not prove valid-fact acceptance, convergence or FugueMax.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {mkdirSync,appendFileSync,readFileSync,existsSync,writeFileSync} from 'node:fs';
import {register} from 'node:module';
import {spawnSync} from 'node:child_process';
import {tmpdir} from 'node:os';
import {mkdtempSync,rmSync} from 'node:fs';
import {digest,holdLock,runAsync,verify,put} from './proof-cache.mjs';
import {hasOrdinaryTheoremRejection} from './negative-proof-evidence.mjs';
import {sourceFiles,modes,mutationDefinitions,definitionByMode,prepareMutation as prepareMutationIn,theorems,mutationOwners,positiveBaselines,cargoBase,nativeArgs as nativeArgsOf,proofRoot,verifyRoots,positivePlan,nativeModePlans,identityControlPlan,auditUnits,checkAuditControls,TEXT_PLAN_INPUTS} from './edit-native-plans.mjs';
import {checkProofReform} from './proof-reform.mjs';
import {nativeCodeClosure,checkNativeCodeRecord,checkNativeCodeControls,checkHeadInputs,checkHeadInputControls} from './text-native-code.mjs';
import {checkNegativeProofEvidence} from './check-negative-proof-evidence.mjs';
const root=fileURLToPath(new URL('..',import.meta.url));
// Runtime load audit (#197). A selected shard run records every module it loads after this point (the static imports
// above are native code inputs by construction); the consumer refuses the run if any loaded gate script lies outside
// the selector's recorded native-code set, so "family modules are not native inputs" is checked, not assumed.
const selectionArg=process.argv.slice(3).find(arg=>arg.startsWith('selection:'));
const loadLog=selectionArg&&process.argv[2]?path.join(process.argv[2],'loaded-modules.log'):null;
// One invocation per checkout. Mode workspaces (.cache/edit-proofs), Cargo targets
// (target/edit-proof-check) and the positive seed are shared mutable state, so an
// overlapping invocation is rejected before it writes any of them. This process
// takes the lock itself and every command it starts inherits it (holdLock), so a
// killed runner's surviving writers keep the checkout locked until they exit.
// Never delete the lock file: its inode is the lock.
// A plan export (`<out> export-plans`, exclusive) writes only its output directory and runs on read-only trees
// (the selection boundary exports base and head from the Nix store), so it takes no checkout lock.
const exportOnly=process.argv.length===4&&process.argv[3]==='export-plans';
const lock=path.join(root,'.cache','edit-proofs.lock');
if(!exportOnly){
mkdirSync(path.dirname(lock),{recursive:true});
if(!holdLock(lock)) {
  console.error('another check-edit-proofs invocation holds '+lock+'; overlapping runs would share workspaces and extractions');
  process.exit(75);
}
}
// Selected-run output and the load hook are set up only once this invocation owns the checkout lock, so a refused
// overlapping invocation (exit 75 above) never truncates an active run's evidence.
if(loadLog){
  mkdirSync(process.argv[2],{recursive:true});writeFileSync(loadLog,'');
  const hooks='import {appendFileSync} from "node:fs";let log;export function initialize(d){log=d.log;}'+
    'export async function resolve(s,c,n){const r=await n(s,c);if(r.url.startsWith("file:"))appendFileSync(log,r.url+"\\n");return r;}';
  register('data:text/javascript,'+encodeURIComponent(hooks),{parentURL:import.meta.url,data:{log:loadLog}});
}

// Self-checks run once the lock is held.
await import('./check-proof-reform.mjs');
checkNegativeProofEvidence();
await checkProofReform(root);
const prepareMutation=(mode,sources=original)=>prepareMutationIn(mode,sources);
const original=Object.fromEntries(await Promise.all(sourceFiles.map(async name=>[name,await fs.readFile(path.join(root,name),'utf8')])));
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
// Family names in execution order; the modules themselves live in text-families.mjs, loaded only when needed.
const FAMILY_NAMES=["delete","event","operation","replay","basis","schedule","past","remaining","counter","push","vector","scalar","identity","writer","plan","containment","accepted","spec","private","shared","commit"];
let familyModule=null;
const familiesModule=async()=>familyModule??=await import('./text-families.mjs');
const jobArgs=process.argv.slice(3).filter(arg=>arg.startsWith('jobs:')),args=process.argv.slice(3).filter(arg=>!arg.startsWith('jobs:'));
assert(jobArgs.length<=1&&jobArgs.every(arg=>/^jobs:[1-9]\d*$/.test(arg)),'use at most one jobs:<n> with n >= 1');
const jobs=jobArgs.length?Number(jobArgs[0].slice(5)):1;
const familyRuns=new Set();let wantPositive=args.length===0,cacheSafety=args.length===0;
const mutations=[];
// `export-plans` (exclusive) writes <out>/plans.json from the exact units this runner executes (the shared
// enumeration in edit-native-plans.mjs), after the pure self-checks and before any toolchain is required.
const exportPlans=args.includes('export-plans');
assert(!exportPlans||args.length===1,'export-plans is exclusive');
for(const arg of args) {
  if(arg==='gatepreflight'||arg==='export-plans'||arg.startsWith('selection:')){}
  else if(arg==='positive'){wantPositive=true;for(const name of FAMILY_NAMES)familyRuns.add(name);}
  else if(arg==='positive-only')wantPositive=true;
  else if(arg==='cache-safety'){wantPositive=true;cacheSafety=true;}
  else if(/^shard:\d+\/\d+$/.test(arg)){
    const [i,n]=arg.slice(6).split('/').map(Number);assert(n>0&&i<n,'shard index out of range '+arg);
    wantPositive=true;mutations.push(...modes.filter(mode=>mode!=='positive').filter((_,k)=>k%n===i));
  }
  else if(arg.startsWith('contracts-except:')){
    const skip=arg.slice(17).split(',');for(const name of skip)assert(FAMILY_NAMES.includes(name),'unknown contract family '+name);
    wantPositive=true;for(const name of FAMILY_NAMES)if(!skip.includes(name))familyRuns.add(name);
  }
  else if(arg.startsWith('contracts:')){const name=arg.slice(10);assert(FAMILY_NAMES.includes(name),'unknown contract family '+name);wantPositive=true;familyRuns.add(name);}
  else {assert(modes.includes(arg),'unknown mode '+arg);if(arg.startsWith('basis-')||arg.startsWith('replay-')||arg==='scheduler-forgets-completed-tree')wantPositive=true;mutations.push(arg);}
}
assert(!args.includes('gatepreflight')||args.length===1,'gatepreflight is an exclusive preparation-only mode');
if(args.length===0){for(const name of FAMILY_NAMES)familyRuns.add(name);mutations.push(...modes.filter(mode=>mode!=='positive'));}

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

await checkDeletePreparation(root);
checkMutationScopeControls(prepareMutation,original['src/edit.rs'],'scalar-refuses-valid','fn validate_scalars(','Ok(())','fn validate_new(');
checkFstarMutationScope();
// The Remaining locator controls belong to the Remaining family: they run with it, and in gatepreflight.
if(familyRuns.has('remaining')||args.includes('gatepreflight')){(await familiesModule()).checkRemainingCallLocator();
console.log('PASS remaining call locator: calls only in code (line/nested comments, strings), code-only occurrence indexing, inline fallback unhidden, comment/string-only callee refused, mixed call lines refused');}
checkAuditControls(original);
checkNativeCodeControls();
checkHeadInputControls();
console.log('PASS head input controls: added, changed, deleted declared (file and directory member) and declaration-hidden deletion refused; undeclared absence counted');
// Lock order control: while this invocation owns the checkout lock, an overlapping selected invocation must be refused
// (75) before it touches its output, so an existing load log (an active run's evidence) survives byte for byte.
if(!exportOnly){
  const tmp=mkdtempSync(path.join(tmpdir(),'edit-lock-order-')),out=path.join(tmp,'out'),sentinel=path.join(out,'loaded-modules.log');
  try{
    mkdirSync(out,{recursive:true});writeFileSync(sentinel,'sentinel: an active run\'s load log\n');
    const r=spawnSync(process.execPath,[fileURLToPath(import.meta.url),out,'selection:'+path.join(tmp,'absent.json'),'shard:0/3'],{encoding:'utf8',env:process.env});
    assert.equal(r.status,75,'an overlapping selected invocation must be refused by the checkout lock: '+(r.stderr||'').slice(-300));
    assert.equal(readFileSync(sentinel,'utf8'),'sentinel: an active run\'s load log\n','a refused invocation must not touch an existing load log');
    console.log('PASS lock order: an overlapping selected invocation is refused (75) before touching an existing load log');
  }finally{rmSync(tmp,{recursive:true,force:true});}
}
console.log('PASS native code record controls: complete set accepted; omitted static helper, extra entry, wrong digest and runner-only set refused');
console.log('PASS exact-tuple audit controls: hidden unit, unexecuted plan, changed roots, wrong expectation (both kinds), mutation digest, cargo arguments, baselines and owner each refused');
console.log('PASS mutation scopes: every registered mode resolves to one in-scope anchor; moved/duplicate/comment-only anchor, missing/comment/string/duplicated header, literal braces, C raw strings across items and unsupported-lexeme controls');
if(args.length===1&&args[0]==='gatepreflight')process.exit(0);
// Source identity: the files the native and positive units are built from, so a selector can check an export
// against the commit it claims to describe, and a consumer can check a record against its own tree.
async function exportText(){
  const sources={};for(const f of TEXT_PLAN_INPUTS)sources[f]=digest(await fs.readFile(path.join(root,f)));
  return JSON.stringify({schema:1,gate:'text',sources,plans:[positivePlan(),...nativeModePlans(original),identityControlPlan()]},null,1)+'\n';
}
if(exportPlans){
  const out=process.argv[2];assert(out,'output directory required');
  await fs.mkdir(out,{recursive:true});
  await fs.writeFile(path.join(out,'plans.json'),await exportText());
  console.log('exported '+(modes.length-1)+' native-mode plans, the positive and the identity control to '+path.join(out,'plans.json'));
  process.exit(0);
}
// Selection consumer (#197). `selection:<file> shard:<i>/<n>` runs what a selector record chose for this shard. The
// record is refused unless it was made from exactly this tree's text plans (its headPlans digest equals this
// runner's own export) and is not diagnostic. full runs the plain shard; none runs nothing; selected runs this
// shard's share of the selected native modes plus this job's own positive seed (only when it runs a mode).
let textSelection=null;
if(selectionArg){
  const file=selectionArg.slice('selection:'.length);assert(file.length>0,'selection needs a record path');
  const shardArgs=args.filter(arg=>arg.startsWith('shard:'));
  assert(shardArgs.length===1&&args.length===2,'selection combines only with exactly one shard');
  const [i,n]=shardArgs[0].slice(6).split('/').map(Number);
  let rec;try{rec=JSON.parse(await fs.readFile(file,'utf8'));}catch(e){assert.fail('selection record unreadable: '+e.message);}
  const keys=['schema','base','head','diagnosticOnly','basePlans','headPlans','full','reasons','affected','register','text','shared'];
  assert(rec&&typeof rec==='object'&&!Array.isArray(rec)&&Object.keys(rec).length===keys.length&&keys.every(k=>Object.hasOwn(rec,k)),'selection record has an unrecognised shape');
  assert.equal(rec.schema,1,'selection record schema');
  assert.equal(rec.diagnosticOnly,false,'a diagnostic selection record cannot be consumed');
  const t=rec.text;assert(t&&typeof t==='object'&&!Array.isArray(t),'selection record text entry');
  if(rec.full===true||t.run==='full'){assert.deepEqual(Object.keys(t),['run'],'a full text selection carries only run');assert.equal(t.run,'full');textSelection={run:'full'};}
  else{
    const tkeys=['run','positive','modes','why','removed','total','headPlans','basePlans','nativeCode','headInputs'];
    assert(Object.keys(t).length===tkeys.length&&tkeys.every(k=>Object.hasOwn(t,k)),'selection record text entry has an unrecognised shape');
    assert.equal(t.headPlans,digest(await exportText()),'selection record was not made for this tree (head text plan export differs)');
    const natives=modes.filter(mode=>mode!=='positive');
    assert(Array.isArray(t.modes)&&t.modes.every(m=>natives.includes(m)),'selection names unknown native modes');
    assert.equal(new Set(t.modes).size,t.modes.length,'selection names a mode twice');
    assert.equal(t.total,natives.length,'selection record counts a different plan total');
    // Bind the record to this tree's native code: its entries must be exactly this tree's own closure (computed here,
    // so an omitted input cannot pass), each with this tree's digest. Checked before the no-work exit.
    const closure=await nativeCodeClosure(async f=>{try{return await fs.readFile(path.join(root,'scripts',f),'utf8');}catch{return null;}});
    checkNativeCodeRecord(t.nativeCode,closure,f=>digest(readFileSync(path.join(root,f))));
    // Bind the decision to this tree's selection-relevant content: every file this tree holds under those roots must be
    // recorded with this digest (a changed or added proof, crate or script file refuses). Recorded files this
    // packaged tree does not hold cannot be read by any unit run here; they are counted, not checked.
    {
      assert(t.headInputs&&typeof t.headInputs==='object'&&!Array.isArray(t.headInputs),'selection record head inputs');
      const present=[];const walk=async rel=>{let st;try{st=await fs.lstat(path.join(root,rel));}catch{return;}
        if(st.isDirectory()){for(const e of (await fs.readdir(path.join(root,rel))).sort())await walk(rel+'/'+e);}else if(st.isFile())present.push(rel);};
      for(const r of ['proofs','src','tests','proof-smoke','scripts','Cargo.toml','Cargo.lock','nix/text-inputs.json','nix/gate-scripts.json'])await walk(r);
      const decl=JSON.parse(readFileSync(path.join(root,'nix/text-inputs.json'),'utf8')),gates=JSON.parse(readFileSync(path.join(root,'nix/gate-scripts.json'),'utf8'));
      assert(Array.isArray(decl.paths)&&decl.paths.every(p=>typeof p==='string')&&Array.isArray(gates.text),'packaged input declarations');
      // The declarations themselves are bound (they are present inputs), so a deletion cannot be hidden by editing them.
      const undeclared=checkHeadInputs(t.headInputs,present,f=>digest(readFileSync(path.join(root,f))),[...decl.paths,...gates.text.map(n=>'scripts/'+n)]);
      console.log('selection inputs: '+present.length+' files of this tree bound to the record; '+undeclared+' recorded files outside the declared packaged inputs');
    }
    assert(t.run==='selected'?t.modes.length>0:t.run==='none'&&t.modes.length===0,'selection run and modes agree');
    const mine=natives.filter((mode,k)=>k%n===i&&t.modes.includes(mode));
    textSelection={run:t.run,mine,nativeCode:new Set(Object.keys(t.nativeCode))};
    // This job runs exactly its share: no families, no cache-safety, its own positive seed iff it runs a mode.
    mutations.length=0;mutations.push(...mine);wantPositive=mine.length>0;cacheSafety=false;familyRuns.clear();
    console.log('selection '+t.run+': '+mine.length+' of '+t.modes.length+' selected native modes in shard '+i+'/'+n+(wantPositive?' plus this job\'s positive seed':''));
    if(!mine.length){
      const out=process.argv[2];await fs.mkdir(out,{recursive:true});
      await fs.writeFile(path.join(out,'planned.json'),'[]\n');await fs.writeFile(path.join(out,'results.json'),'[]\n');
      console.log('selection runs nothing in this job: not affected (no build of these units ran; no result is claimed)');
      process.exit(0);
    }
  }
}
const {NICKEL_HAX_BIN:hax,NICKEL_PROOF_FSTAR:fstar,NICKEL_HAX_SOURCE:models,NICKEL_FSTAR_MODEL_CACHE:modelCache}=process.env;
assert(hax&&fstar&&models&&modelCache,'use the locked .#proofs environment');
const output=process.argv[2];assert(output,'output directory required');
await fs.mkdir(output,{recursive:true});
await fs.writeFile(path.join(output,'mutation-owners.json'),JSON.stringify(mutationOwners,null,2)+'\n');
const identity=JSON.parse(await fs.readFile(path.join(modelCache,'identity.json'),'utf8'));
assert.equal(identity.models,models);assert.equal(identity.fstar,fstar);
const views=new Map();
for(const name of ['EditDeletePermutation','EditDeleteAnswer','EditDeleteHeap','EditDeleteComplete','PastExact','Canonical','Prelude','LoopUtil','LoopEquality','EventGraph','EventGraphText','EventShell','EventClassifier','Vector','EditAtomic','EditCommit','EditIdentity','EditAccepted','EditWellFormed','Spec','EditCausal','EditPast','EditPastTotal','EditSchedule','EditBasis','EditReplay']) {
  const source=`proofs/${name}.lt`,view=name==='Canonical'?'proofs/register-view/Nickel.Canonical.fst':`proofs/generated/Nickel.${name}.fst`;
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
const haxArgs=editProofHaxArgs;
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
// Exact-tuple audit (#197): every executed unit records what it actually ran (roots passed to the
// verifier, cargo arguments and baselines, the mutated file it wrote, the owner it judged and the
// expected outcome it asserted). At the end these must equal the planned tuples field for field.
const executed=new Map();
const nativeIndex=new Map(modes.filter(mode=>mode!=='positive').map((mode,index)=>[mode,index]));
async function check(mode) {
  const work=path.join(root,'.cache','edit-proofs',mode),crate=path.join(work,'crate'),proof=path.join(work,'proof');
  const ran={id:mode,kind:mode==='positive'?'positive':'native-mode',...(mode==='positive'?{}:{index:nativeIndex.get(mode)}),owner:null,expect:null,roots:null,mutation:null,native:{cargoArgs:null,baselines:[],extraction:false}};
  if(positiveProof&&await fresh(proof))await fs.cp(positiveProof,proof,{recursive:true,preserveTimestamps:true});
  await fs.mkdir(proof,{recursive:true});
  await copyCrate(crate,mode==='positive'?undefined:prepared.get(mode));
  if(mode!=='positive'){const [file]=definitionByMode.get(mode);ran.mutation=[{file,sha256:digest(await fs.readFile(path.join(crate,file)))}];}
  // Each mode has its own Cargo target: hax names its metadata by package, not by
  // source tree, so crate copies sharing a target read each other's extraction.
  const env={...process.env,CARGO_TARGET_DIR:path.join(root,'target','edit-proof-check','modes',mode)};
  const nativeArgs=nativeArgsOf(mode);ran.native.cargoArgs=[...nativeArgs];
  const native=await runAsync('edit native '+mode,'cargo',nativeArgs,crate,{env});
  await fs.writeFile(path.join(output,mode+'.native.log'),native.log);
  if(mode==='positive') {
    assert.equal(native.status,0,native.log);
    for(const {name,test} of positiveBaselines){
      const baseline=await runAsync('edit '+name+' native baseline','cargo',[...cargoBase,'--lib',test],crate,{env});
      await fs.writeFile(path.join(output,'positive.'+name+'-native.log'),baseline.log);
      assert.equal(baseline.status,0,baseline.log);
      assert.match(baseline.log,/test result: ok\. [1-9]\d* passed;/,name+' native baseline must discover and pass tests: '+baseline.log);
      ran.native.baselines.push([...cargoBase,'--lib',test]);
    }
  }
  else {assert.equal(native.status,101,native.log);assert.match(native.log,/test result: FAILED/);}
  const extract=path.join(work,'extract');await fs.rm(extract,{recursive:true,force:true});await fs.mkdir(extract,{recursive:true});
  const extracted=await runAsync('edit hax '+mode,hax,haxArgs(extract),crate,{env});ran.native.extraction=true;
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
  const roots=verifyRoots(mode);ran.roots=[...roots];
  const checked=await verify({label:mode,dir:proof,roots:roots.map(name=>path.join(proof,name)),fstar,models,modelCache});
  await fs.writeFile(path.join(output,mode+'.proof.log'),checked.log);
  if(mode==='positive') {
    assert.equal(checked.status,0,checked.log);ran.expect='verify';
    positiveProof=proof;
    // Each family edits its own copy of the verified positive workspace, so the
    // positive cache stays clean and families cannot see each other's probes.
    // The family module loads only when a family runs (native-only runs never load it; selected runs audit that).
    const {families}=familyRuns.size?await familiesModule():{families:{}};
    if(familyRuns.size)assert.deepEqual(Object.keys(families),FAMILY_NAMES,'family table and names agree');
    for(const [name,check] of Object.entries(families))if(familyRuns.has(name)) {
      const copy=path.join(root,'.cache','edit-proofs','contracts-'+name,'proof');
      await fs.rm(copy,{recursive:true,force:true});
      await fs.cp(proof,copy,{recursive:true,preserveTimestamps:true});
      await check({proof:copy,output,fstar,models,modelCache});
    }
    if(cacheSafety)await (await familiesModule()).checkCacheSafety({positiveProof:proof,workRoot:path.join(root,'.cache','edit-proofs'),output,fstar,models,modelCache});
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
    ran.expect='reject';ran.owner=theorems[mode];
  }
  assert(!executed.has(mode),'unit executed twice: '+mode);executed.set(mode,ran);
  console.log(`PASS ${mode}: native and unchanged actual-Rust theorem ${mode==='positive'?'verified':'reject the mutation'}`);
}
// The positive chain (and its families) completes first: it seeds every fresh
// mutation workspace and is only read afterwards. After the first failure no
// further mode starts; running modes finish before the failure is reported.
if(wantPositive)await check('positive');
// Identity control: two mutants of one function (one owner theorem rejects both).
// A's crate with B's extraction must fail the identity check; B's own must pass.
if(mutations.length) {
  const control=path.join(root,'.cache','edit-proofs','identity-control'),[a,b]=identityControlPlan().modes;
  await fs.rm(control,{recursive:true,force:true});
  await copyCrate(path.join(control,'a'),prepareMutation(a));await copyCrate(path.join(control,'b'),prepareMutation(b));
  await fs.mkdir(path.join(control,'extract'),{recursive:true});
  const extracted=await runAsync('edit hax identity control',hax,haxArgs(path.join(control,'extract')),path.join(control,'b'),{env:{...process.env,CARGO_TARGET_DIR:path.join(control,'target')}});
  assert.equal(extracted.status,0,extracted.log);
  assert(!await sameExtraction('control wrong mutant',path.join(control,'a'),path.join(control,'extract'),path.join(control,'reference')),'identity control: another mutant\'s extraction passed the identity check');
  assert(await sameExtraction('control own mutant',path.join(control,'b'),path.join(control,'extract'),path.join(control,'reference')),'identity control: a mutant\'s own extraction failed the identity check');
  await fs.rm(control,{recursive:true,force:true});
  executed.set('extraction-identity-control',{id:'extraction-identity-control',kind:'identity-control',modes:[a,b]});
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
// Planned units for this invocation, from the shared enumeration; executed units must equal them exactly.
{
  const native=nativeModePlans(original).filter(plan=>queue.includes(plan.id));
  const planned=[...(wantPositive?[positivePlan()]:[]),...native,...(queue.length?[identityControlPlan()]:[])];
  await fs.writeFile(path.join(output,'planned.json'),JSON.stringify(planned,null,1)+'\n');
  const ran=[...executed.values()];
  await fs.writeFile(path.join(output,'results.json'),JSON.stringify(ran,null,1)+'\n');
  auditUnits(planned,executed);
  console.log('PASS exact-tuple audit: '+planned.length+' planned units executed exactly as planned (ids, expectations, roots, mutations, cargo arguments, baselines, owners)');
}
if(textSelection&&textSelection.run!=='full'){
  const loaded=[...new Set(readFileSync(loadLog,'utf8').split('\n').filter(Boolean).map(url=>fileURLToPath(url)))]
    .filter(f=>f.startsWith(path.join(root,'scripts')+path.sep)).map(f=>'scripts/'+path.relative(path.join(root,'scripts'),f)).sort();
  await fs.writeFile(path.join(output,'loaded-modules.json'),JSON.stringify(loaded,null,1)+'\n');
  const outside=loaded.filter(f=>!textSelection.nativeCode.has(f));
  assert.deepEqual(outside,[],'a selected shard loaded gate scripts outside the recorded native code set: '+outside.join(', '));
  console.log('PASS load audit: '+loaded.length+' gate scripts loaded after startup, all inside the recorded native code set');
}
