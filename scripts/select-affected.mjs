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
// - The text gate and the shared gates are not plan-exported yet: text runs in full whenever a
//   text-gate module is affected or a text gate script changed; shared gates always run in full.
// --test-ignore-full-paths is a diagnostic aid only: it reports module-level selection with the
// full-forcing paths ignored; its record carries diagnosticOnly:true and a consumer must reject it.
import {execFileSync} from 'node:child_process';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import assert from 'node:assert/strict';

const args=process.argv.slice(2);
const opt=name=>{const i=args.indexOf(name);return i>=0?args[i+1]:null;};
const repo=opt('--repo')??process.cwd();
const valued=new Set(['--repo','--base-plans','--head-plans']);
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
  for(const f of files){const mod=moduleOfFile(f);if(!mod)continue;if(/^proofs\/generated\//.test(f))textModules.add(mod);if(/^proofs\/causal-envelope-view\//.test(f))causalModules.add(mod);if(/^proofs\/register-view\//.test(f))registerViewModules.add(mod);const text=show(ref,f);if(text===null)continue;
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

// ---------------------------------------------------------------- changed paths
const NATIVE={'src/register.rs':'Nickel_crdt.Register','src/event_layer.rs':'Nickel_crdt.Event_layer','src/edit.rs':'Nickel_crdt.Edit',
  'src/causal.rs':'Nickel_crdt.Causal','src/event_shell.rs':'Nickel_crdt.Event_shell'};
const changes=git('diff','--name-only','--no-renames',base,head).split('\n').filter(Boolean);
const seeds=new Set(),changedNative=new Set();let receiptChanged=false;
const seed=(mod,why)=>{seeds.add(mod);reasons.push({module:mod,why});};
for(const path of changes){
  let m;
  if((m=/^proofs\/([A-Za-z]+)\.lt$/.exec(path)))seed('Nickel.'+m[1],path);
  else if(moduleOfFile(path)&&path.startsWith('proofs/'))seed(moduleOfFile(path),path);
  else if((m=/^proofs\/generated\/([A-Za-z]+)\.sha256$/.exec(path)))seed('Nickel.'+m[1],path);
  else if(path==='proofs/register-view/receipt.json'||path==='proofs/causal-envelope-view/receipt.json'){receiptChanged=true;reasons.push({gate:'view receipt (register positive; shared gates always full)',why:path});}
  else if(Object.hasOwn(NATIVE,path)){seed(NATIVE[path],path);changedNative.add(path);}
  else if(path==='scripts/'+PLAN_MODULE)reasons.push({register:'plan module changed: plans are compared',why:path});
  else if((m=/^scripts\/([A-Za-z0-9_.-]+)$/.exec(path))&&scriptGates.has(m[1])){
    const gates=scriptGates.get(m[1]);
    if(gates.has('register')&&ignoreFull)reasons.push({ignoredForTest:'would force register full',why:path});else if(gates.has('register')){registerFull=true;reasons.push({registerFull:'register execution infrastructure changed',why:path});}
    if(gates.has('text')&&ignoreFull)reasons.push({ignoredForTest:'would force text full',why:path});else if(gates.has('text')){textFull=true;reasons.push({textFull:'text gate script changed',why:path});}
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

// ---------------------------------------------------------------- text and shared gates
const textGateModule=m=>textModules.has(m);
const textAffected=[...affected].some(textGateModule);

// basePlans/headPlans: digests of the export files used. A consumer must recompute its own head export
// and refuse unless it matches headPlans exactly.
const record={schema:1,base,head,diagnosticOnly:ignoreFull,basePlans:basePlans.digest??null,headPlans:headPlans.digest??null,full,reasons,affected:[...affected].sort(),
  register:full||registerFull?{run:'full'}:{run:registerSelected.length||positiveWhy?'selected':'none',positive:positiveWhy,
    modes:registerSelected.map(([n])=>n),why:Object.fromEntries(registerSelected),removed:registerRemoved,total:registerTotal},
  text:{run:full||textFull||textAffected?'full':'none'},
  shared:{run:'full'}};
console.log(JSON.stringify(record,null,1));
