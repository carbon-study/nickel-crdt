// Affected-set selection for pull requests (draft; not yet wired into CI).
// usage: node scripts/select-affected.mjs <base-ref> <head-ref> [--repo <dir>]
//
// Prints JSON: whether the full suite is required, why, the affected proof modules, and the
// register / text controls to run. It is deliberately conservative:
// - every changed path must map to known proof modules, a known no-proof category, or `full`;
//   an unknown path selects the full suite;
// - module dependencies are read statically from the committed F* files at BOTH base and head
//   (open / module X = / include / friend and qualified Nickel.* / Nickel_crdt.* references), and
//   the affected set is the reverse closure over the union of both graphs, so deletions and
//   renames keep their consumers;
// - register controls are selected by owner module, and native body faults also by the source
//   file they edit; text mutation modes by owner module and source file; text contract families
//   are not mapped per owner yet, so any affected text-gate module selects every family.
// The positive chain of a gate always runs when any of its controls is selected.
import {execFileSync} from 'node:child_process';
import assert from 'node:assert/strict';

const args=process.argv.slice(2);
const repoAt=args.indexOf('--repo');const repo=repoAt>=0?args[repoAt+1]:process.cwd();
const [base,head]=args.filter((a,i)=>!a.startsWith('--')&&args[i-1]!=='--repo');
// TEST ONLY: report what module-level selection alone picks when paths that would force the full
// suite (gate scripts, flake, CI) are ignored. Never used for an actual selection.
const ignoreFull=args.includes('--test-ignore-full-paths');
assert(base&&head,'usage: select-affected.mjs <base-ref> <head-ref> [--repo dir]');
const git=(...a)=>execFileSync('git',['-C',repo,...a],{encoding:'utf8',maxBuffer:1<<28});
const show=(ref,path)=>{try{return git('show',ref+':'+path);}catch{return null;}};

// ---------------------------------------------------------------- module graph
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
function graphAt(ref){
  const files=git('ls-tree','-r','--name-only',ref,'--',...PROOF_DIRS).split('\n').filter(f=>/\.fsti?$/.test(f));
  const graph=new Map();
  for(const f of files){const mod=moduleOfFile(f);if(!mod)continue;const text=show(ref,f);if(text===null)continue;
    const d=graph.get(mod)??new Set();for(const x of depsOf(text))if(x!==mod)d.add(x);graph.set(mod,d);}
  return graph;
}
const graphs=[graphAt(base),graphAt(head)];
const reverse=new Map();
for(const g of graphs)for(const [mod,deps] of g)for(const d of deps){if(!reverse.has(d))reverse.set(d,new Set());reverse.get(d).add(mod);}
const known=new Set(graphs.flatMap(g=>[...g.keys()]));

// ---------------------------------------------------------------- changed paths
const NATIVE={'src/register.rs':'Nickel_crdt.Register','src/event_layer.rs':'Nickel_crdt.Event_layer','src/edit.rs':'Nickel_crdt.Edit',
  'src/causal.rs':'Nickel_crdt.Causal','src/event_shell.rs':'Nickel_crdt.Event_shell'};
const changes=git('diff','--name-status','--no-renames',base,head).split('\n').filter(Boolean).map(l=>{const [s,...p]=l.split('\t');return {status:s,path:p[p.length-1]};});
const seeds=new Set(),reasons=[],changedNative=new Set();let full=false;
const seed=(mod,why)=>{seeds.add(mod);reasons.push({module:mod,why});};
for(const {path} of changes){
  let m;
  if((m=/^proofs\/([A-Za-z]+)\.lt$/.exec(path)))seed('Nickel.'+m[1],path);
  else if(moduleOfFile(path)&&path.startsWith('proofs/'))seed(moduleOfFile(path),path);
  else if((m=/^proofs\/generated\/([A-Za-z]+)\.sha256$/.exec(path)))seed('Nickel.'+m[1],path);
  else if(path==='proofs/register-view/receipt.json'||path==='proofs/causal-envelope-view/receipt.json')reasons.push({gate:'receipt',why:path});
  else if(Object.hasOwn(NATIVE,path)){seed(NATIVE[path],path);changedNative.add(path);}
  else if(/^src\/edit\/[a-z_]+_tests\.rs$/.test(path)||/^tests\/(?!register_checkpoint\.rs$)/.test(path)||/^examples\//.test(path))reasons.push({native:'tests only',why:path});
  else if(/^(docs\/|experiments\/|questionnaire\/)|\.md$|^LICENSE$/.test(path))reasons.push({none:'documentation/reference',why:path});
  else if(ignoreFull)reasons.push({ignoredForTest:'would force full',why:path});
  else{full=true;reasons.push({full:'no proof-module mapping',why:path});}
}
// Reverse closure over both graphs.
const affected=new Set(seeds);const queue=[...seeds];
while(queue.length){const x=queue.pop();for(const c of reverse.get(x)??[])if(!affected.has(c)){affected.add(c);queue.push(c);}}
for(const mod of seeds)if(!known.has(mod)&&!/^Nickel\.[A-Za-z]+$/.test(mod)){full=true;reasons.push({full:'seed module absent from both graphs',why:mod});}

// ---------------------------------------------------------------- register controls
const regGate=show(head,'scripts/check-register-proofs.mjs');assert(regGate,'register gate missing at head');
function registerRows(src){
  // A row starts at ` ['name',` / ` ["name",` and may continue over several lines; its owner is
  // the last string literal before the row's closing `]`.
  const rows=[];let section=null,cur=null;
  const finish=()=>{if(!cur)return;const owner=/(['"])([A-Za-z_0-9.]+)\1\]\s*,?\s*$/.exec(cur.text.trimEnd());
    assert(owner,'register row owner unparsed: '+cur.name);rows.push({name:cur.name,kind:cur.kind,owner:owner[2]});cur=null;};
  for(const line of src.split('\n')){
    if(/^const bodyModes=\[/.test(line)){section='body';continue;}
    if(/^const depModes=\[/.test(line)){section='dep';continue;}
    if(section&&/^\];/.test(line)){finish();section=null;continue;}
    if(!section)continue;
    const m=/^ \[(['"])([a-z0-9-]+)\1,/.exec(line);
    if(m){finish();cur={name:m[2],kind:section,text:line};}
    else if(cur&&!/^\s*\/\//.test(line))cur.text+='\n'+line;
  }
  finish();
  return rows;
}
const graphModes=new Set([...(/const graphModes=new Set\(\[([^\]]*)\]/.exec(regGate)?.[1]??'').matchAll(/'([a-z0-9-]+)'/g)].map(m=>m[1]));
const regRows=registerRows(regGate);
const regModule=owner=>/^(Canonical|PastExact|RegisterPast|RegisterHistory|RegisterValid|RegisterPublic|RegisterFrontier|LoopUtil)\./.test(owner)?'Nickel.'+owner.split('.')[0]:'Nickel.Register';
const registerSelected=regRows.filter(r=>affected.has(regModule(r.owner))||
  (r.kind==='body'&&changedNative.has(graphModes.has(r.name)?'src/event_layer.rs':'src/register.rs'))).map(r=>r.name);

// ---------------------------------------------------------------- text controls
const textGate=show(head,'scripts/check-edit-proofs.mjs');assert(textGate,'text gate missing at head');
const theorems=Object.fromEntries([...(/const theorems=\{([\s\S]*?)\n\};/.exec(textGate)?.[1]??'').matchAll(/'([a-z0-9-]+)':\s*'([A-Za-z_0-9.]+)'/g)].map(m=>[m[1],m[2]]));
const textSource=Object.fromEntries([...textGate.matchAll(/^\s*\["([a-z0-9-]+)","(src\/[a-z_]+\.rs)",/gm)].map(m=>[m[1],m[2]]));
const textModes=Object.keys(textSource);
const textModule=owner=>'Nickel.'+owner.split('.')[0];
const textGateModules=new Set([...known].filter(m=>/^Nickel\.(Edit|Event|Loop|Prelude|Spec|Smoke|Vector)/.test(m)||m==='Nickel_crdt.Edit'||m==='Nickel_crdt.Event_layer'||m==='Nickel_crdt.Event_shell'));
const textAffected=[...affected].some(m=>textGateModules.has(m));
const textSelected=textModes.filter(n=>(theorems[n]?affected.has(textModule(theorems[n])):textAffected)||changedNative.has(textSource[n]));
const textFamilies=textAffected?'all':'none';

console.log(JSON.stringify({base,head,testIgnoreFullPaths:ignoreFull,full,reasons,affected:[...affected].sort(),
  register:{positive:full||registerSelected.length>0,modes:full?'all':registerSelected,total:regRows.length},
  text:{positive:full||textSelected.length>0||textFamilies==='all',modes:full?'all':textSelected,families:full?'all':textFamilies,total:textModes.length,unownedModes:textModes.filter(n=>!theorems[n]).length}},null,1));
