// Affected-set selection for pull requests (draft; not yet wired into CI).
// usage: node scripts/select-affected.mjs <base-ref> <head-ref> [--repo <dir>]
//          [--base-plans <plans.json> --head-plans <plans.json>] [--test-ignore-full-paths]
// Plans are produced at each ref by `node scripts/check-register-proofs.mjs <out> export-plans`.
//
// Prints a selection record: exact base/head commits, whether each gate must run in full and why,
// the affected proof modules, and for the register gate the controls to run plus the controls the
// head removed. Conservative by construction:
// - Register controls come only from plans exported by the gate itself (check-register-proofs.mjs
//   export-plans, built by scripts/register-control-plans.mjs), never from parsing gate source.
//   Missing, malformed or unrecognised plan exports select the full register gate.
// - A head plan runs if it is new, differs from the base plan of the same name (owner, theorem,
//   roots, source/module or mutated-text digest), or its theorem module or a verification root is
//   in the affected set, or it is a native body fault whose source file changed. Removed plans are
//   reported, never silently dropped from coverage accounting.
// - Changed paths must map to proof modules, the declared register plan module, or a known no-proof
//   category. Any other gate script, the gate script declarations, flake, CI, Cargo or nix input
//   selects the full suite. Gate script ownership is read from nix/gate-scripts.json at both refs.
// - Module dependencies are read statically from the committed F* files at BOTH base and head; the
//   affected set is the reverse closure over the union of both graphs.
// - Text: native modes (#197) and core-b's contract families (#199) are selected from each ref's own text plan and
//   family plan exports (below); core-a's families are not selected (#198). Shared gates always run in full.
// --test-ignore-full-paths is a diagnostic aid only: it reports module-level selection with the
// full-forcing paths ignored; its record carries diagnosticOnly:true and a consumer must reject it.
import {execFileSync} from 'node:child_process';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import assert from 'node:assert/strict';

const args=process.argv.slice(2);
const opt=name=>{const i=args.indexOf(name);return i>=0?args[i+1]:null;};
const repo=opt('--repo')??process.cwd();
const valued=new Set(['--repo','--base-plans','--head-plans','--text-base-plans','--text-head-plans','--text-base-family-plans','--text-head-family-plans']);
const positional=args.filter((a,i)=>!a.startsWith('--')&&!valued.has(args[i-1]));
const [baseRef,headRef]=positional;
assert(baseRef&&headRef&&positional.length===2,'usage: select-affected.mjs <base-ref> <head-ref> [--repo dir] [--base-plans f --head-plans f]');
const ignoreFull=args.includes('--test-ignore-full-paths');
const git=(...a)=>execFileSync('git',['-C',repo,...a],{encoding:'utf8',maxBuffer:1<<28});
const show=(ref,path)=>{try{return git('show',ref+':'+path);}catch{return null;}};
const base=git('rev-parse',baseRef+'^{commit}').trim(),head=git('rev-parse',headRef+'^{commit}').trim();

const reasons=[];let full=false,registerFull=false,textFull=false;
const forceFull=(why,path)=>{if(ignoreFull){reasons.push({ignoredForTest:'would force full: '+why,why:path});return;}full=true;reasons.push({full:why,why:path});};

// ---------------------------------------------------------------- module graph (base and head)
const PROOF_DIRS=['proofs/generated','proofs/generated/hax','proofs/register-view','proofs/causal-envelope-view'];
const moduleOfFile=p=>{const m=/(?:^|\/)((?:Nickel|Nickel_crdt|Nickel_proof_smoke)(?:\.[A-Za-z_0-9]+)*)\.fsti?$/.exec(p);return m?m[1]:null;};
const projectModule=name=>/^(Nickel|Nickel_crdt)\.[A-Za-z_0-9]+$/.test(name)||name==='Nickel_proof_smoke';
function depsOf(text){
  const deps=new Set();
  for(const m of text.matchAll(/^\s*(?:open|include|friend)\s+([A-Za-z_0-9.]+)/gm))deps.add(m[1]);
  for(const m of text.matchAll(/^\s*module\s+[A-Za-z_0-9]+\s*=\s*([A-Za-z_0-9.]+)/gm))deps.add(m[1]);
  for(const m of text.matchAll(/\b((?:Nickel|Nickel_crdt)\.[A-Z][A-Za-z_0-9]*)\./g))deps.add(m[1]);
  return [...deps].filter(projectModule);
}
// Modules verified by the text gate: everything defined under proofs/generated at base or head.
const textModules=new Set(),causalModules=new Set(),registerViewModules=new Set();
function graphAt(ref){
  const files=git('ls-tree','-r','--name-only',ref,'--',...PROOF_DIRS).split('\n').filter(f=>/\.fsti?$/.test(f));
  const graph=new Map();
  // Several files can define one module (for example the text and register extractions of
  // Nickel_crdt.Event_shell); their dependencies are united.
  for(const f of files){const mod=moduleOfFile(f);if(!mod)continue;if(/^proofs\/generated\//.test(f))textModules.add(mod);if(/^proofs\/causal-envelope-view\//.test(f))causalModules.add(mod);if(/^proofs\/register-view\//.test(f))registerViewModules.add(mod);const text=show(ref,f);if(text===null){forceFull("unreadable enumerated proof file",ref+":"+f);continue;}
    const d=graph.get(mod)??new Set();for(const x of depsOf(text))if(x!==mod)d.add(x);graph.set(mod,d);}
  return graph;
}
const graphs=[graphAt(base),graphAt(head)];
const reverse=new Map();
for(const g of graphs)for(const [mod,deps] of g)for(const d of deps){if(!reverse.has(d))reverse.set(d,new Set());reverse.get(d).add(mod);}
const known=new Set(graphs.flatMap(g=>[...g.keys()]));

// ---------------------------------------------------------------- gate script ownership (base and head)
const PLAN_MODULE='register-control-plans.mjs';
function gateScriptsAt(ref){
  const text=show(ref,'nix/gate-scripts.json');if(text===null)return null;
  try{const j=JSON.parse(text);for(const [k,v] of Object.entries(j))assert(Array.isArray(v)&&v.every(s=>typeof s==='string'),k);return j;}catch{return null;}
}
const gateScripts=[gateScriptsAt(base),gateScriptsAt(head)];
const scriptGates=new Map();
for(const j of gateScripts)if(j)for(const [gate,files] of Object.entries(j))for(const f of files){if(!scriptGates.has(f))scriptGates.set(f,new Set());scriptGates.get(f).add(gate);}
if(gateScripts.some(j=>j===null))forceFull('unreadable nix/gate-scripts.json at base or head','nix/gate-scripts.json');

// ---------------------------------------------------------------- text native path code inputs (base and head)
// The native mutation path's code is check-edit-proofs.mjs plus everything it loads by a literal import
// (static `from '…'` or `import('…')`), transitively, at either ref. Family modules load by name only when
// their family runs: the runner imports scripts/text-families.mjs only for families, cache-safety or gatepreflight,
// so that one named module (and what only it reaches) is not a native code input. Selected shard runs audit the
// modules they actually load against this set. Shared machinery and the runner itself force full.
const TEXT_RUNNER='scripts/check-edit-proofs.mjs',TEXT_FAMILIES='scripts/text-families.mjs';
const TEXT_SHARED=new Set([TEXT_RUNNER,'scripts/proof-cache.mjs','scripts/negative-proof-evidence.mjs','scripts/mutation-scope.mjs',
  'scripts/fstar-mutation-scope.mjs','scripts/proof-reform.mjs','scripts/text-family-run.mjs','nix/gate-scripts.json','flake.nix']);
// The closure itself is text-native-code.mjs (shared with the consumer; check-gate-inputs' parser, which needs node
// --experimental-vm-modules). Change detection uses the union of base and head; the record carries the head closure.
let nativeCodeClosure=null;try{({nativeCodeClosure}=await import('./text-native-code.mjs'));}catch{}
const nativeCode=new Set();let nativeCodeError=nativeCodeClosure?null:'native code closure unavailable (run the selector with node --experimental-vm-modules)';
let headNativeCode=[];
for(const ref of [base,head]){if(nativeCodeError)break;
  try{const names=await nativeCodeClosure(async f=>show(ref,'scripts/'+f));for(const n of names)nativeCode.add('scripts/'+n);if(ref===head)headNativeCode=names.map(n=>'scripts/'+n);}
  catch(e){nativeCodeError=ref+': '+String(e?.message??e).slice(0,200);}}

// ---------------------------------------------------------------- changed paths
const NATIVE={'src/register.rs':'Nickel_crdt.Register','src/event_layer.rs':'Nickel_crdt.Event_layer','src/edit.rs':'Nickel_crdt.Edit',
  'src/causal.rs':'Nickel_crdt.Causal','src/event_shell.rs':'Nickel_crdt.Event_shell'};
const changes=git('diff','--name-only','--no-renames',base,head).split('\n').filter(Boolean);
const seeds=new Set(),changedNative=new Set();let receiptChanged=false,textNativeAll=false;
if(nativeCodeError){textFull=true;reasons.push({textFull:'native-path code inputs unreadable',why:nativeCodeError});}
// Crate, test and native inputs of the native mutation path: any change runs every native tuple.
const CRATE=/^(src\/|tests\/|proof-smoke\/|Cargo\.(toml|lock)$)/;
const seed=(mod,why)=>{seeds.add(mod);reasons.push({module:mod,why});};
for(const path of changes){
  let m;
  if(CRATE.test(path)){textNativeAll=true;reasons.push({textNative:'crate/test/native input changed: every native tuple runs',why:path});}
  if(path==='flake.nix'||path==='flake.lock'){textFull=true;reasons.push({textFull:'toolchain or flake changed',why:path});}
  if((m=/^proofs\/([A-Za-z]+)\.lt$/.exec(path)))seed('Nickel.'+m[1],path);
  else if(moduleOfFile(path)&&path.startsWith('proofs/'))seed(moduleOfFile(path),path);
  else if((m=/^proofs\/generated\/([A-Za-z]+)\.sha256$/.exec(path)))seed('Nickel.'+m[1],path);
  else if(path==='proofs/register-view/receipt.json'||path==='proofs/causal-envelope-view/receipt.json'){receiptChanged=true;reasons.push({gate:'view receipt (register positive; shared gates always full)',why:path});}
  else if(Object.hasOwn(NATIVE,path)){seed(NATIVE[path],path);changedNative.add(path);}
  else if(path==='scripts/'+PLAN_MODULE)reasons.push({register:'plan module changed: plans are compared',why:path});
  else if((m=/^scripts\/([A-Za-z0-9_.-]+)$/.exec(path))&&scriptGates.has(m[1])){
    const gates=scriptGates.get(m[1]);
    if(gates.has('register')&&ignoreFull)reasons.push({ignoredForTest:'would force register full',why:path});else if(gates.has('register')){registerFull=true;reasons.push({registerFull:'register execution infrastructure changed',why:path});}
    if(gates.has('text')&&ignoreFull)reasons.push({ignoredForTest:'would force text full',why:path});
    else if(gates.has('text')){
      if(TEXT_SHARED.has(path)){textFull=true;reasons.push({textFull:'text runner or shared text machinery changed',why:path});}
      else if(nativeCode.has(path)){textNativeAll=true;reasons.push({textNative:'native-path code input changed: every native tuple runs',why:path});}
      else reasons.push({textFamily:'text family/core script changed; no native tuple reads it (families are selected by their code closures; core-a runs per its own route)',why:path});
    }
    const other=[...gates].filter(g=>g!=='register'&&g!=='text');
    if(other.length)reasons.push({shared:'shared/model/native gate script changed ('+other.join(',')+'); those gates always run in full',why:path});
  }
  else if(/^src\/edit\/[a-z_]+_tests\.rs$/.test(path)||/^tests\/(?!register_checkpoint\.rs$)/.test(path)||/^examples\//.test(path))reasons.push({native:'tests only (native jobs always run)',why:path});
  else if(/^(docs\/|experiments\/|questionnaire\/)|\.md$|^LICENSE$/.test(path))reasons.push({none:'documentation/reference',why:path});
  else forceFull('no proof-module or gate mapping',path);
}
const affected=new Set(seeds);const queue=[...seeds];
while(queue.length){const x=queue.pop();for(const c of reverse.get(x)??[])if(!affected.has(c)){affected.add(c);queue.push(c);}}
// A changed module that neither graph defines is verified by no gate this selector knows: run everything.
for(const mod of seeds)if(!known.has(mod))forceFull('seed module absent from both graphs',mod);

// ---------------------------------------------------------------- register plans
const HEX=/^[0-9a-f]{64}$/,NAME=/^[a-z0-9]+(?:-[a-z0-9]+)*$/;
// The export's source identity (plan inputs, register gate scripts, view receipt); every export must carry exactly these digests, and each
// must equal the file at the ref the export claims to describe.
const PLAN_INPUTS=['scripts/check-register-proofs.mjs','scripts/register-control-plans.mjs','scripts/mutation-scope.mjs',
  'scripts/negative-proof-evidence.mjs','scripts/proof-cache.mjs','scripts/proof-reform.mjs','proofs/register-view/receipt.json',
  'src/register.rs','src/event_layer.rs','proofs/generated/Nickel.LoopUtil.fst',
  ...['Canonical','Register','RegisterPast','RegisterHistory','RegisterValid','RegisterPublic','RegisterFrontier'].map(m=>'proofs/register-view/Nickel.'+m+'.fst')];
const sha=b=>createHash('sha256').update(b).digest('hex');
const blob=(ref,path)=>{try{return execFileSync('git',['-C',repo,'show',ref+':'+path],{maxBuffer:1<<28});}catch{return null;}};
function readPlans(file,label,ref){
  if(!file)return {error:label+' plan export not supplied'};
  let bytes,j;try{bytes=readFileSync(file);j=JSON.parse(bytes.toString('utf8'));}catch(e){return {error:label+' plan export unreadable: '+e.message};}
  const bad=why=>({error:label+' plan export '+why});
  if(!j||typeof j!=='object'||Object.keys(j).some(k=>!['schema','gate','sources','plans'].includes(k)))return bad('has unrecognised top-level fields');
  if(j.schema!==1||j.gate!=='register'||!Array.isArray(j.plans))return bad('has an unrecognised shape');
  if(!j.sources||typeof j.sources!=='object'||Object.keys(j.sources).sort().join()!==[...PLAN_INPUTS].sort().join())return bad('does not carry exactly the plan input digests');
  for(const f of PLAN_INPUTS){const b=blob(ref,f);if(b===null)return bad('names '+f+', absent at '+ref.slice(0,12));
    if(j.sources[f]!==sha(b))return bad('was not built from '+ref.slice(0,12)+' ('+f+' differs)');}
  const keys=new Set(['name','kind','owner','theorem','roots','sourceFile','module','classifierModule','mutated']);
  const byName=new Map();let positives=0;
  for(const p of j.plans){
    if(!p||typeof p!=='object'||Object.keys(p).some(k=>!keys.has(k)))return bad('has a plan with unrecognised fields');
    if(typeof p.name!=='string'||!NAME.test(p.name))return bad('has a malformed plan name');
    if(byName.has(p.name))return bad('lists '+p.name+' twice');
    if(!Array.isArray(p.roots)||!p.roots.length||!p.roots.every(r=>typeof r==='string'&&/^(Nickel|Nickel_crdt)\.[A-Za-z_0-9]+\.fst$/.test(r)))return bad('has malformed roots for '+p.name);
    if(p.kind==='positive'){positives++;if(p.mutated!==null||p.owner!==null||p.theorem!==null)return bad('has a malformed positive');}
    else if(p.kind==='body'){if(!HEX.test(p.mutated??'')||!Object.hasOwn(NATIVE,p.sourceFile??'')||typeof p.theorem!=='string'||typeof p.owner!=='string')return bad('has a malformed body plan '+p.name);}
    else if(p.kind==='dep'){if(!HEX.test(p.mutated??'')||!/^Nickel\.[A-Za-z]+$/.test(p.module??'')||typeof p.theorem!=='string'||typeof p.owner!=='string')return bad('has a malformed dependency plan '+p.name);}
    else return bad('has unknown plan kind '+String(p.kind));
    if(p.kind!=='positive'&&!/^(Nickel|Nickel_crdt)\.[A-Za-z_0-9]+\.[A-Za-z_0-9']+$/.test(p.theorem))return bad('has a malformed theorem for '+p.name);
    byName.set(p.name,p);
  }
  if(positives!==1)return bad('must contain exactly one positive');
  return {plans:j.plans,byName,digest:sha(bytes)};
}
const basePlans=readPlans(opt('--base-plans'),'base',base),headPlans=readPlans(opt('--head-plans'),'head',head);
for(const r of [basePlans,headPlans])if(r.error){registerFull=true;reasons.push({registerFull:r.error});}
const theoremModule=t=>t.split('.').slice(0,2).join('.');
const rootModule=r=>r.replace(/\.fst$/,'');
// Every changed module must be verified by some gate: a text module, a causal-envelope module, or a
// module the register positive's roots reach at base or head (any register-view module when the
// register gate runs in full anyway). A changed module no gate reaches selects everything.
{const reach=new Set(),stack=[];
 for(const r of [basePlans,headPlans])if(!r.error)for(const root of r.plans.find(p=>p.kind==='positive').roots)stack.push(root.replace(/\.fst$/,''));
 while(stack.length){const m=stack.pop();if(reach.has(m))continue;reach.add(m);for(const g of graphs)for(const d of g.get(m)??[])stack.push(d);}
 for(const mod of seeds)if(!textModules.has(mod)&&!causalModules.has(mod)&&!reach.has(mod)&&!(registerFull&&registerViewModules.has(mod)))
  forceFull('changed module reached by no gate root',mod);}
let registerSelected=[],registerRemoved=[],registerTotal=null,positiveWhy=null;
if(!registerFull){
  for(const p of headPlans.plans){if(p.kind==='positive')continue;
    const b=basePlans.byName.get(p.name);
    if(!b)registerSelected.push([p.name,'new control']);
    else if(JSON.stringify(b)!==JSON.stringify(p))registerSelected.push([p.name,'control plan changed']);
    else if(affected.has(theoremModule(p.theorem)))registerSelected.push([p.name,'owner module affected']);
    else if(p.roots.some(r=>affected.has(rootModule(r))))registerSelected.push([p.name,'verification root affected']);
    else if(p.kind==='body'&&changedNative.has(p.sourceFile))registerSelected.push([p.name,'mutated native source changed']);
  }
  registerRemoved=basePlans.plans.filter(p=>p.kind!=='positive'&&!headPlans.byName.has(p.name)).map(p=>p.name);
  registerTotal=headPlans.plans.length-1;
  // The positive verifies every register root; it runs whenever any control runs, a root module is
  // affected, the positive plan changed, or a receipt changed, even if no control owns the change.
  const hp=headPlans.plans.find(p=>p.kind==='positive'),bp=basePlans.plans.find(p=>p.kind==='positive');
  if(registerSelected.length)positiveWhy='selected controls';
  else if(JSON.stringify(hp)!==JSON.stringify(bp))positiveWhy='positive plan changed';
  else if(hp.roots.some(r=>affected.has(rootModule(r))))positiveWhy='register root affected';
  else if(receiptChanged)positiveWhy='receipt changed';
}

// ---------------------------------------------------------------- text native plans (#197)
// Roots of the files a text decision depends on (and the text consumer's packaged tree is drawn from).
const TEXT_INPUT_ROOTS=['proofs','src','tests','proof-smoke','scripts','Cargo.toml','Cargo.lock','nix/text-inputs.json','nix/gate-scripts.json'];
const TEXT_PLAN_INPUTS=['scripts/edit-native-plans.mjs','scripts/mutation-scope.mjs','src/edit.rs','src/event_layer.rs','src/event_shell.rs'];
const MODFILE=/^(Nickel|Nickel_crdt)\.[A-Za-z_0-9]+\.fst$/;
function readTextPlans(file,label,ref){
  if(!file)return {error:label+' text plan export not supplied'};
  let bytes,j;try{bytes=readFileSync(file);j=JSON.parse(bytes.toString('utf8'));}catch(e){return {error:label+' text plan export unreadable: '+e.message};}
  const bad=why=>({error:label+' text plan export '+why});
  if(!j||typeof j!=='object'||Object.keys(j).sort().join()!=='gate,plans,schema,sources')return bad('has unrecognised top-level fields');
  if(j.schema!==1||j.gate!=='text'||!Array.isArray(j.plans))return bad('has an unrecognised shape');
  if(!j.sources||typeof j.sources!=='object'||Object.keys(j.sources).sort().join()!==[...TEXT_PLAN_INPUTS].sort().join())return bad('does not carry exactly the text plan input digests');
  for(const f of TEXT_PLAN_INPUTS){const b=blob(ref,f);if(b===null)return bad('names '+f+', absent at '+ref.slice(0,12));if(j.sources[f]!==sha(b))return bad('was not built from '+ref.slice(0,12)+' ('+f+' differs)');}
  const byId=new Map();let positives=0,identity=0;
  const strings=a=>Array.isArray(a)&&a.every(x=>typeof x==='string');
  for(const p of j.plans){
    if(!p||typeof p!=='object'||typeof p.id!=='string'||byId.has(p.id))return bad('has a malformed or repeated plan id');
    if(p.kind==='positive'){positives++;if(Object.keys(p).sort().join()!=='expect,id,kind,mutation,native,owner,roots'||p.expect!=='verify'||p.owner!==null||p.mutation!==null||!strings(p.roots)||!p.roots.every(r=>MODFILE.test(r))||!p.native||!strings(p.native.cargoArgs)||!Array.isArray(p.native.baselines)||p.native.extraction!==true)return bad('has a malformed positive');}
    else if(p.kind==='identity-control'){identity++;if(Object.keys(p).sort().join()!=='id,kind,modes'||!strings(p.modes)||p.modes.length!==2)return bad('has a malformed identity control');}
    else if(p.kind==='native-mode'){
      if(Object.keys(p).sort().join()!=='expect,id,index,kind,mutation,native,owner,roots'||p.expect!=='reject'||!Number.isSafeInteger(p.index)||typeof p.owner!=='string'||!/^[A-Za-z]+\.[A-Za-z_0-9']+$/.test(p.owner))return bad('has a malformed native mode '+p.id);
      if(!strings(p.roots)||p.roots.length!==2||p.roots[0]!=='Nickel_crdt.Edit.fst'||!MODFILE.test(p.roots[1]))return bad('has malformed roots for '+p.id);
      if(!Array.isArray(p.mutation)||p.mutation.length!==1||!TEXT_PLAN_INPUTS.includes(p.mutation[0].file)||!HEX.test(p.mutation[0].sha256??''))return bad('has a malformed mutation for '+p.id);
      if(!p.native||!strings(p.native.cargoArgs)||!Array.isArray(p.native.baselines)||p.native.baselines.length!==0||p.native.extraction!==true)return bad('has malformed native inputs for '+p.id);
    } else return bad('has unknown plan kind '+String(p.kind));
    byId.set(p.id,p);
  }
  if(positives!==1||identity!==1)return bad('must contain exactly one positive and one identity control');
  const natives=j.plans.filter(p=>p.kind==='native-mode');
  if(natives.some((p,k)=>p.index!==k))return bad('has native indices out of order');
  return {plans:j.plans,byId,natives,digest:sha(bytes)};
}
// ---------------------------------------------------------------- text family plans (#199)
// Family control tuples come from each ref's own family export (check-edit-proofs.mjs export-plans, family-plans.json),
// built by the same per-family enumeration execution consumes. Families are selected whole: one selected tuple
// schedules the family's complete inventory. A family is selected when any of its tuples is new, changed or removed;
// a changed module lies in the dependency closure of a tuple's roots or its owner's module; a crate or test input
// changed and the family has native tuples; its code (its module's literal import closure, at either ref) changed; or
// the family index changed. Unreadable or malformed family exports, or an owner outside its roots' closure, select
// every family job in full. Shared machinery and the runner already select all text work in full.
const FAMILY_KEYS='expect,family,id,kind,mutation,native,owner,roots';
function readFamilyPlans(file,label,ref){
  if(!file)return {error:label+' family plan export not supplied'};
  let bytes,j;try{bytes=readFileSync(file);j=JSON.parse(bytes.toString('utf8'));}catch(e){return {error:label+' family plan export unreadable: '+e.message};}
  const bad=why=>({error:label+' family plan export '+why});
  if(!j||typeof j!=='object'||Object.keys(j).sort().join()!=='gate,modules,order,plans,schema,sources,unconverted')return bad('has unrecognised top-level fields');
  if(j.schema!==1||j.gate!=='text-families'||!Array.isArray(j.plans)||!Array.isArray(j.order)||!Array.isArray(j.unconverted))return bad('has an unrecognised shape');
  if(!j.order.every(n=>typeof n==='string'&&NAME.test(n))||new Set(j.order).size!==j.order.length||!j.unconverted.every(n=>j.order.includes(n)))return bad('has a malformed family order');
  if(!j.modules||typeof j.modules!=='object'||Object.keys(j.modules).sort().join()!==[...j.order].sort().join()||!Object.values(j.modules).every(m=>typeof m==='string'&&/^[a-z0-9-]+\.mjs$/.test(m)))return bad('has malformed family modules');
  if(!j.sources||typeof j.sources!=='object'||!Object.keys(j.sources).length)return bad('names no sources');
  for(const [f,d] of Object.entries(j.sources)){const b=blob(ref,f);if(b===null)return bad('names '+f+', absent at '+ref.slice(0,12));if(d!==sha(b))return bad('was not built from '+ref.slice(0,12)+' ('+f+' differs)');}
  const converted=j.order.filter(n=>!j.unconverted.includes(n)),byId=new Map(),byFamily=new Map(converted.map(n=>[n,[]]));
  const strings=a=>Array.isArray(a)&&a.every(x=>typeof x==='string');
  for(const p of j.plans){
    if(!p||typeof p!=='object'||Object.keys(p).sort().join()!==FAMILY_KEYS||p.kind!=='family-control')return bad('has a malformed family tuple');
    if(!byFamily.has(p.family)||typeof p.id!=='string'||!p.id.startsWith(p.family+':')||byId.has(p.id))return bad('has a malformed, repeated or unconverted-family id '+String(p.id));
    if(!(p.expect==='reject'&&typeof p.owner==='string'&&/^(Nickel|Nickel_crdt)\.[A-Za-z_0-9]+\.[A-Za-z_0-9']+$/.test(p.owner))&&!(p.expect==='verify'&&p.owner===null))return bad('has a malformed expectation or owner for '+p.id);
    if(!strings(p.roots)||!p.roots.length||!p.roots.every(r=>MODFILE.test(r)))return bad('has malformed roots for '+p.id);
    if(!Array.isArray(p.mutation)||!p.mutation.length||!p.mutation.every(m=>m&&Object.keys(m).sort().join()==='file,sha256'&&typeof m.file==='string'&&HEX.test(m.sha256)))return bad('has a malformed mutation for '+p.id);
    if(p.native!==null&&(!p.native||Object.keys(p.native).sort().join()!=='baselines,cargoArgs,extraction'||!strings(p.native.cargoArgs)||!Array.isArray(p.native.baselines)||p.native.baselines.length!==0||p.native.extraction!==true))return bad('has malformed native inputs for '+p.id);
    byId.set(p.id,p);byFamily.get(p.family).push(p);
  }
  for(const [n,ps] of byFamily)if(!ps.length)return bad('has no tuples for converted family '+n);
  return {j,converted,byId,byFamily,digest:sha(bytes)};
}
let familyCodeClosure=null;try{({familyCodeClosure}=await import('./text-native-code.mjs'));}catch{}
async function selectFamilies(){
  const fb=readFamilyPlans(opt('--text-base-family-plans'),'base',base),fh=readFamilyPlans(opt('--text-head-family-plans'),'head',head);
  const err=[fb,fh].find(r=>r.error);if(err){reasons.push({textFamiliesFull:err.error});return {run:'full'};}
  if(!familyCodeClosure){reasons.push({textFamiliesFull:'family code closure unavailable (run the selector with node --experimental-vm-modules)'});return {run:'full'};}
  // Family code at both refs, from each ref's own module table.
  const code={base:{},head:{}};
  try{for(const [side,ref,r] of [['base',base,fb],['head',head,fh]])for(const n of r.converted)code[side][n]=(await familyCodeClosure(async f=>show(ref,'scripts/'+f),r.j.modules[n])).map(f=>'scripts/'+f);}
  catch(e){reasons.push({textFamiliesFull:'family code inputs unreadable',why:String(e?.message??e).slice(0,200)});return {run:'full'};}
  const depsClosure=mods=>{const seen=new Set(),stack=[...mods];while(stack.length){const m=stack.pop();if(seen.has(m))continue;seen.add(m);for(const d of graphs[1].get(m)??[])stack.push(d);}return seen;};
  const outside=[...fh.byId.values()].filter(p=>p.owner!==null&&!depsClosure(p.roots.map(rootModule)).has(theoremModule(p.owner))).map(p=>p.id);
  if(outside.length){reasons.push({textFamiliesFull:'family owner module outside its roots\' dependency closure (graph incomplete)',why:outside.slice(0,5).join(',')});return {run:'full'};}
  const changed=new Set(changes),crate=changes.some(p=>CRATE.test(p)),index=changed.has(TEXT_FAMILIES);
  const why={};
  for(const n of fh.converted){
    const hp=fh.byFamily.get(n),bp=fb.byFamily.get(n);
    const codeHit=[...new Set([...(code.base[n]??[]),...code.head[n]])].filter(f=>changed.has(f));
    let r=null;
    if(!bp)r='new or newly converted family';
    else if(JSON.stringify(bp)!==JSON.stringify(hp))r='family tuples changed (new, changed or removed controls)';
    else if(index)r='family index changed ('+TEXT_FAMILIES+')';
    else if(codeHit.length)r='family code changed: '+codeHit.join(',');
    else if(crate&&hp.some(p=>p.native!==null))r='crate or test input changed and the family has native tuples';
    else{const p=hp.find(p=>p.roots.some(x=>affected.has(rootModule(x)))||(p.owner!==null&&affected.has(theoremModule(p.owner))));
      if(p)r=(p.roots.some(x=>affected.has(rootModule(x)))?'verification root affected':'owner module affected')+' ('+p.id+')';}
    if(r)why[n]=r;
  }
  const selected=fh.converted.filter(n=>Object.hasOwn(why,n));
  const removed=[...fb.byId.keys()].filter(id=>!fh.byId.has(id));
  return {run:selected.length?'selected':'none',selected,why,removed,total:fh.byId.size,headPlans:fh.digest,basePlans:fb.digest,
    digests:Object.fromEntries(fh.converted.map(n=>[n,sha(JSON.stringify(fh.byFamily.get(n)))])),
    familyCode:Object.fromEntries(fh.converted.map(n=>[n,Object.fromEntries(code.head[n].map(f=>[f,sha(blob(head,f))]))]))};
}
let text={run:'none'};
{
  const tb=readTextPlans(opt('--text-base-plans'),'base',base),th=readTextPlans(opt('--text-head-plans'),'head',head);
  const err=[tb,th].find(r=>r.error);
  if(full||textFull)text={run:'full'};
  else if(err){reasons.push({textFull:err.error});text={run:'full'};}
  else {
    const semantic=p=>{const {index,...rest}=p;return JSON.stringify(rest);};
    // An owner theorem is only judged if F* checks its module, i.e. if that module is in the dependency closure
    // of the tuple's roots. Check it on the head graph: a violation means this selector's graph is missing an edge,
    // so text runs full. (Given it, the owner rule below is implied by the root rule; it stays as defence in depth.)
    const depsClosure=mods=>{const seen=new Set(),stack=[...mods];while(stack.length){const m=stack.pop();if(seen.has(m))continue;seen.add(m);for(const d of graphs[1].get(m)??[])stack.push(d);}return seen;};
    const outside=th.natives.filter(p=>!depsClosure(p.roots.map(rootModule)).has(theoremModule('Nickel.'+p.owner))).map(p=>p.id);
    const sel=[];
    for(const p of th.natives){
      const b=tb.byId.get(p.id);
      if(!b)sel.push([p.id,'new native tuple']);
      else if(semantic(b)!==semantic(p))sel.push([p.id,'native tuple changed']);
      else if(textNativeAll)sel.push([p.id,'crate, test or native-path code input changed']);
      else if(affected.has(theoremModule('Nickel.'+p.owner)))sel.push([p.id,'owner module affected']);
      else if(p.roots.some(r=>affected.has(rootModule(r))))sel.push([p.id,'verification root affected']);
    }
    const removed=tb.natives.filter(p=>!th.byId.has(p.id)).map(p=>p.id);
    const hp=th.byId.get('positive'),bp=tb.byId.get('positive');
    const positive=textNativeAll?'crate, test or native-path code input changed':semantic(hp)!==semantic(bp)?'positive tuple changed':hp.roots.some(r=>affected.has(rootModule(r)))?'positive root affected':null;
    if(outside.length){reasons.push({textFull:'owner module outside its roots\' dependency closure (graph incomplete)',why:outside.slice(0,5).join(',')});text={run:'full'};}
    else text={run:sel.length?'selected':'none',positive,modes:sel.map(([n])=>n),why:Object.fromEntries(sel),removed,total:th.natives.length,headPlans:th.digest,basePlans:tb.digest,nativeCode:Object.fromEntries(headNativeCode.map(f=>[f,sha(blob(head,f))])),
      // Every head file under the selection-relevant roots, so a consumer refuses a record made for other proof, crate
      // or script content (a stale record replayed on a changed tree), not only other plans or native code.
      headInputs:Object.fromEntries(git('ls-tree','-r','--name-only',head,'--',...TEXT_INPUT_ROOTS).split('\n').filter(Boolean).sort().map(f=>[f,sha(blob(head,f))])),
      families:await selectFamilies()};
  }
}

// ---------------------------------------------------------------- text and shared gates

// basePlans/headPlans: digests of the export files used. A consumer must recompute its own head export
// and refuse unless it matches headPlans exactly.
const record={schema:1,base,head,diagnosticOnly:ignoreFull,basePlans:basePlans.digest??null,headPlans:headPlans.digest??null,full,reasons,affected:[...affected].sort(),
  register:full||registerFull?{run:'full'}:{run:registerSelected.length||positiveWhy?'selected':'none',positive:positiveWhy,
    modes:registerSelected.map(([n])=>n),why:Object.fromEntries(registerSelected),removed:registerRemoved,total:registerTotal},
  text,
  shared:{run:'full'}};
console.log(JSON.stringify(record,null,1));
