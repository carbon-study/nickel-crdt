// Declared-nix selection boundary for the register gate, and with --gate=text for the text gate's native
// mutation shards (#197) and its core-b contract families (#199).
// usage: node selection-boundary.mjs <out> <head-tree> <base-tree> <head-rev> <base-rev> [--gate=text]
// Writes <out>/mode ("full" or "selected"), <out>/identity.json and, when selected,
// <out>/selection.json for check-register-proofs.mjs selection:<file>. Every doubt selects full:
// the default base (nix/selection-base-none), a missing head or base revision (no selection-head
// override matching this tree, or an unpinned base),
// a toolchain difference (flake.lock or flake.nix), a base or head export that
// fails, a selector that fails, or a record that is full or diagnostic. Base and head plans are
// exported by each tree's own runner; the record comes from the head tree's selector over a
// two-commit repository holding exactly the base tree and then exactly the head tree.
import {spawnSync} from 'node:child_process';
import {createHash} from 'node:crypto';
import fs from 'node:fs';import path from 'node:path';
const [out,head,base,headRev,baseRev,gateArg]=process.argv.slice(2);
if(!out||!head||!base||headRev===undefined||baseRev===undefined||process.argv.length>8||(gateArg!==undefined&&gateArg!=='--gate=text')){console.error('usage: selection-boundary.mjs <out> <head-tree> <base-tree> <head-rev> <base-rev> [--gate=text]');process.exit(2);}
const gate=gateArg?'text':'register';
fs.mkdirSync(out,{recursive:true});
const sha=b=>createHash('sha256').update(b).digest('hex');
const fileSha=f=>fs.existsSync(f)?sha(fs.readFileSync(f)):null;
const rev=/^[0-9a-f]{40}$/;
const identity={schema:1,gate,head:headRev||null,base:baseRev||null,
  toolchain:{headFlakeLock:fileSha(path.join(head,'flake.lock')),baseFlakeLock:fileSha(path.join(base,'flake.lock')),
   headFlake:fileSha(path.join(head,'flake.nix')),baseFlake:fileSha(path.join(base,'flake.nix'))},
  mode:null,reasons:[],selection:null};
const finish=(mode,why)=>{identity.mode=mode;if(why)identity.reasons.push(why);
  fs.writeFileSync(path.join(out,'identity.json'),JSON.stringify(identity,null,1)+'\n');fs.writeFileSync(path.join(out,'mode'),mode+'\n');
  console.log('selection boundary: '+mode+(why?' ('+why+')':''));process.exit(0);};
const run=(label,cmd,args,opts={})=>{const r=spawnSync(cmd,args,{encoding:'utf8',maxBuffer:1<<28,...opts});
  fs.writeFileSync(path.join(out,label+'.log'),(r.stdout??'')+(r.stderr??''));return r;};

// A relative path input reports the parent flake's revision as its own, so the sentinel's rev is not a base.
if(fs.existsSync(path.join(base,'nickel-selection-base-none'))){identity.base=null;finish('full','no base revision supplied (default selection-base)');}
if(!rev.test(headRev))finish('full','head has no exact revision (no selection-head override whose tree is this tree)');
if(!rev.test(baseRev))finish('full','base has no exact revision');
const t=identity.toolchain;
if(!t.headFlakeLock||t.headFlakeLock!==t.baseFlakeLock||t.headFlake!==t.baseFlake)finish('full','toolchain differs between base and head (flake.lock or flake.nix)');

// each tree exports its own plans with its own runner
const exp={};
for(const [side,tree] of [['base',base],['head',head]]){
  const dir=path.join(out,side+'-export');const r=run(side+'-export','node',[path.join(tree,gate==='text'?'scripts/check-edit-proofs.mjs':'scripts/check-register-proofs.mjs'),dir,'export-plans']);
  if(r.status!==0||!fs.existsSync(path.join(dir,'plans.json')))finish('full',side+' plan export failed');
  exp[side]=path.join(dir,'plans.json');
}
// a two-commit repository: exactly the base tree, then exactly the head tree
const repo=path.join(process.env.TMPDIR??'/tmp','selection-repo');fs.rmSync(repo,{recursive:true,force:true});fs.mkdirSync(repo,{recursive:true});
const genv={...process.env,GIT_AUTHOR_NAME:'selection',GIT_AUTHOR_EMAIL:'selection@localhost',GIT_COMMITTER_NAME:'selection',GIT_COMMITTER_EMAIL:'selection@localhost',
  GIT_AUTHOR_DATE:'2000-01-01T00:00:00Z',GIT_COMMITTER_DATE:'2000-01-01T00:00:00Z',GIT_CONFIG_NOSYSTEM:'1',HOME:process.env.HOME??repo};
const git=(...a)=>{const r=spawnSync('git',['-C',repo,...a],{encoding:'utf8',env:genv,maxBuffer:1<<28});if(r.status!==0)finish('full','git '+a[0]+' failed: '+(r.stderr??'').trim().slice(0,200));return r.stdout.trim();};
git('init','-q');
const load=(tree,msg)=>{for(const e of fs.readdirSync(repo))if(e!=='.git')fs.rmSync(path.join(repo,e),{recursive:true,force:true});
  fs.cpSync(tree,repo,{recursive:true});spawnSync('chmod',['-R','u+w',repo]);git('add','-A');git('commit','-q','--allow-empty','-m',msg);return git('rev-parse','HEAD');};
const b=load(base,'base '+baseRev),h=load(head,'head '+headRev);
// The selector parses gate imports with node's module parser, which needs --experimental-vm-modules.
const sel=run('selector','node',['--experimental-vm-modules','--no-warnings',path.join(head,'scripts/select-affected.mjs'),b,h,'--repo',repo,
  // The text gate also passes each tree's family export (#199); a tree without one (a base before #199) makes the
  // selector route the family jobs full, which it records.
  ...(gate==='text'?['--text-base-plans',exp.base,'--text-head-plans',exp.head,
    '--text-base-family-plans',path.join(path.dirname(exp.base),'family-plans.json'),'--text-head-family-plans',path.join(path.dirname(exp.head),'family-plans.json')]
   :['--base-plans',exp.base,'--head-plans',exp.head])]);
if(sel.status!==0)finish('full','selector failed');
let record;try{record=JSON.parse(sel.stdout);}catch{finish('full','selector output unreadable');}
if(record.diagnosticOnly!==false)finish('full','diagnostic record');
if(gate==='register'&&(record.full===true||record.register?.run==='full'))finish('full','selector chose the full register gate');
if(gate==='text'&&(record.full===true||record.text?.run==='full'))finish('full','selector chose the full text shards');
fs.writeFileSync(path.join(out,'selection.json'),sel.stdout);
identity.selection=gate==='text'?{digest:sha(sel.stdout),run:record.text.run,modes:record.text.modes.length,removed:record.text.removed,headPlans:record.text.headPlans,
   families:record.text.families.run==='full'?{run:'full'}:{run:record.text.families.run,selected:record.text.families.selected,removed:record.text.families.removed,headPlans:record.text.families.headPlans}}
  :{digest:sha(sel.stdout),run:record.register.run,modes:record.register.modes.length,removed:record.register.removed,headPlans:record.headPlans};
finish('selected');
