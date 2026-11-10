import {spawn,spawnSync} from 'node:child_process';
import {createHash} from 'node:crypto';
import {openSync} from 'node:fs';
import {mkdir,readFile,writeFile,rename,readdir,rm,cp} from 'node:fs/promises';
import {join,basename} from 'node:path';
import {fileURLToPath} from 'node:url';

export const proofFlags=['--cmi','--warn_error','-331','--split_queries','on_failure','--fuel','4','--ifuel','4','--z3rlimit','100','--timing','--query_stats'];
export const compilerKillGraceSeconds=2;
export const makeMarginSeconds=10;
// Count the reachable compiler targets, not unrelated workspace files, imported
// immutable models, or extraction targets also emitted by F*'s --dep full.
export function projectCompilerTargets(graph,dir,sources,roots) {
  const rules=new Map(),prefix=join(dir,'checked')+'/';
  for(const line of graph.replace(/\\\r?\n/g,' ').split('\n')) {
    if(!line.trim()||line.trimStart().startsWith('#'))continue;
    const colon=line.indexOf(':');if(colon<0)continue;
    const dependencies=line.slice(colon+1).trim().split(/\s+/).filter(Boolean);
    for(const target of line.slice(0,colon).trim().split(/\s+/))
      rules.set(target,[...(rules.get(target)??[]),...dependencies]);
  }
  const visited=new Set(),targets=new Set(),known=new Set(sources);
  function visit(target) {
    if(visited.has(target))return;visited.add(target);
    if(target.startsWith(prefix)&&target.endsWith('.checked')) {
      const source=target.slice(prefix.length,-'.checked'.length);
      if(!known.has(source))throw Error('unexpected local compiler target: '+target);
      if(!rules.has(target))throw Error('missing compiler dependency rule: '+target);
      targets.add(target);
    }
    for(const dependency of rules.get(target)??[])visit(dependency);
  }
  for(const root of roots) {
    if(!root.startsWith(prefix)||!known.has(root.slice(prefix.length,-'.checked'.length))||!root.endsWith('.checked'))
      throw Error('aggregate budget requires project compiler roots: '+root);
    visit(root);
  }
  return [...targets].sort();
}
export function aggregateProofSeconds(count,moduleSeconds) {
  const seconds=count*(moduleSeconds+compilerKillGraceSeconds)+makeMarginSeconds;
  if(!Number.isSafeInteger(count)||count<1||!Number.isInteger(moduleSeconds)||moduleSeconds<1||!Number.isSafeInteger(seconds))
    throw Error('invalid aggregate proof budget');
  return seconds;
}
export function projectRlimit() {
  const value=Number(process.env.NICKEL_PROOF_RLIMIT??100);
  if(!Number.isInteger(value)||value<1||value>100)throw Error('NICKEL_PROOF_RLIMIT must be an integer from 1 to 100');
  return value;
}
function flagsAt(rlimit) {
  if(!Number.isInteger(rlimit)||rlimit<1||rlimit>100)throw Error('invalid proof rlimit');
  const flags=[...proofFlags];flags[flags.indexOf('--z3rlimit')+1]=String(rlimit);return flags;
}
// Declaration wall time and every solver attempt, including failed split queries.
export function proofStats(log) {
  const rows=new Map();
  const row=name=>{if(!rows.has(name))rows.set(name,{name,declarationMs:null,queries:[]});return rows.get(name);};
  for(const m of log.matchAll(/Query-stats \(([^,]+), (\d+)\)\s+(succeeded|failed).*? in (\d+) milliseconds[^\n]*? and rlimit (\d+) \(used rlimit ([\d.]+)\)/g))
    row(m[1]).queries.push({id:Number(m[2]),status:m[3],ms:Number(m[4]),limit:Number(m[5]),used:Number(m[6])});
  for(const m of log.matchAll(/^(\S+), profiled [^\n]*process_one_decl:\s+(\d+) ms$/gm))row(m[1]).declarationMs=Number(m[2]);
  return [...rows.values()];
}
export const modelIncludes=models=>['hax-lib/proofs/fstar/extraction','proof-libs/fstar/rust_primitives','proof-libs/fstar/core','proof-libs/fstar/hax_lib'].map(p=>join(models,p));
export const digest=data=>createHash('sha256').update(data).digest('hex');
export async function put(path,data) {
  try { if((await readFile(path)).equals(Buffer.from(data)))return false; } catch(e) {if(e.code!=='ENOENT')throw e;}
  await writeFile(path+'.tmp',data);await rename(path+'.tmp',path);return true;
}
// Exclusive flock(2) on file for this process and every command run/runAsync
// start. The lock belongs to the open file description: this process keeps it
// open and passes it to each command as fd 3, so descendants that outlive this
// process (timeout, make, F*, cargo, hax) hold the lock until the last exits.
// Returns false if another holder has it. The file is opened for append and
// never truncated or unlinked: its inode is the lock.
let lockFd;
export function holdLock(file) {
  if(lockFd!==undefined)throw Error('lock already held');
  const fd=openSync(file,'a');
  const r=spawnSync('flock',['--nonblock','--conflict-exit-code','75','3'],{stdio:['ignore','inherit','inherit',fd]});
  if(r.error)throw r.error.code==='ENOENT'?Error('the edit proof runner needs flock(1) (util-linux) on PATH'):r.error;
  if(r.status===75)return false;
  if(r.status!==0)throw Error('flock '+file+' exited '+(r.status??r.signal));
  lockFd=fd;return true;
}
const stdio=()=>lockFd===undefined?'pipe':['pipe','pipe','pipe',lockFd];
export function run(label,bin,args,cwd,{env=process.env,seconds=60}={}) {
  const start=performance.now();
  const r=spawnSync('timeout',['--kill-after=2s',`${seconds}s`,bin,...args],{cwd,env,stdio:stdio(),encoding:'utf8',maxBuffer:32*1024*1024});
  const elapsed=(performance.now()-start)/1000;
  console.log(`[time] ${label}: ${elapsed.toFixed(3)}s (exit ${r.status ?? r.signal})`);
  if(r.error)throw r.error;
  return {status:r.status,stdout:r.stdout??'',log:(r.stdout??'')+(r.stderr??''),seconds:elapsed};
}
// The same command, timeout and result as run, without blocking the event loop,
// so independent proof workspaces can be checked concurrently in one process.
// Like spawnSync's maxBuffer, more than 32 MiB on either stream kills the command
// and throws.
export function runAsync(label,bin,args,cwd,{env=process.env,seconds=60}={}) {
  const start=performance.now(),limit=32*1024*1024;
  return new Promise((resolve,reject)=>{
    const child=spawn('timeout',['--kill-after=2s',`${seconds}s`,bin,...args],{cwd,env,stdio:stdio()});
    const out={stdout:'',stderr:''},bytes={stdout:0,stderr:0};let overflow=false,settled=false;
    const finish=(status,signal)=>{
      if(settled)return;settled=true;
      const elapsed=(performance.now()-start)/1000;
      console.log(`[time] ${label}: ${elapsed.toFixed(3)}s (exit ${status ?? signal})`);
      if(overflow)return reject(Error(label+': output exceeded '+limit+' bytes'));
      resolve({status,stdout:out.stdout,log:out.stdout+out.stderr,seconds:elapsed});
    };
    // Overflow: TERM timeout, which forwards it to its process group. timeout
    // leads that group (no --foreground), so after the same 2 s grace KILL the
    // whole group: a descendant that ignores TERM can outlive timeout itself.
    // Then settle without waiting for pipes such a survivor might hold open.
    const stop=()=>{
      child.kill('SIGTERM');
      setTimeout(()=>{
        try{process.kill(-child.pid,'SIGKILL');}catch(e){if(e.code!=='ESRCH')throw e;}
        child.stdout.destroy();child.stderr.destroy();
        finish(null,'SIGKILL');
      },2000);
    };
    for(const name of ['stdout','stderr']) {
      child[name].setEncoding('utf8');
      child[name].on('data',chunk=>{
        if(overflow)return; // stop collecting once the command has been told to stop
        out[name]+=chunk;bytes[name]+=Buffer.byteLength(chunk);
        if(bytes[name]>limit){overflow=true;stop();}
      });
    }
    child.stdin.end();
    child.on('error',error=>{if(!settled){settled=true;reject(error);}});
    child.on('close',finish);
  });
}
// Workspace source hashes, not source mtimes, invalidate direct cache entries.
// Make/F* then propagate invalidation through the actual dependency graph.
// label (optional) names the workspace in every console line, for concurrent checks.
export async function verify({dir,roots,fstar,models,modelCache,seconds,moduleSeconds=60,rlimit=100,label}) {
  const tag=label===undefined?'':' '+label,say=line=>console.log(label===undefined?line:`[${label}] ${line}`);
  if(!Number.isInteger(moduleSeconds)||moduleSeconds<1||moduleSeconds>180)throw Error('moduleSeconds must be an integer from 1 to 180');
  if(modelCache&&moduleSeconds>60)throw Error('project module budget cannot exceed 60 seconds');
  if(seconds!==undefined&&(!Number.isSafeInteger(seconds)||seconds<1))throw Error('invalid aggregate seconds');
  await mkdir(join(dir,'checked'),{recursive:true});
  const options=JSON.stringify({fstar,models,modelCache,moduleSeconds,flags:flagsAt(rlimit)});
  let oldOptions;try {oldOptions=await readFile(join(dir,'options.json'),'utf8');}catch(e){if(e.code!=='ENOENT')throw e;}
  if(options!==oldOptions)for(const name of await readdir(join(dir,'checked')))
    if(name.endsWith('.checked')||name.endsWith('.checked.lax'))await rm(join(dir,'checked',name));
  await put(join(dir,'options.json'),options);
  let previous={};try {previous=JSON.parse(await readFile(join(dir,'sources.json'),'utf8'));}catch(e){if(e.code!=='ENOENT')throw e;}
  const current={};for(const name of await readdir(dir))if(/\.fsti?$/.test(name))current[name]=digest(await readFile(join(dir,name)));
  for(const name of new Set([...Object.keys(previous),...Object.keys(current)]))if(previous[name]!==current[name]) {
    await rm(join(dir,'checked',name+'.checked'),{force:true});
    await rm(join(dir,'checked',name+'.checked.lax'),{force:true});
  }
  await put(join(dir,'sources.json'),JSON.stringify(current,null,2)+'\n');
  const flags=[...flagsAt(rlimit),'--cache_checked_modules','--cache_dir',join(dir,'checked'),'--already_cached','+Prims+FStar+LowStar+C+Spec.Loops+TestLib'];
  for(const include of [...modelIncludes(models),...(modelCache?[modelCache]:[]),dir])flags.push('--include',include);
  const dep=await runAsync('F* dependency graph'+tag,fstar,[...flags,'--dep','full',...roots],dir);
  if(dep.status!==0)return dep;
  // Project runs may write only project caches, even if a prior run left a
  // model cache here. Missing immutable models are a packaging error.
  if(modelCache) {
    const prefix=join(dir,'checked')+'/';
    const missing=dep.stdout.split('\n').filter(line=>line.startsWith(prefix)&&line.includes(':'))
      .map(line=>line.slice(prefix.length,line.indexOf(':')))
      .filter(name=>name.endsWith('.checked')&&!Object.hasOwn(current,name.slice(0,-'.checked'.length)));
    if(missing.length)throw Error('incomplete immutable proof-models cache; rebuild/update .#proof-models: '+[...new Set(missing)].join(', '));
  }
  await put(join(dir,'depend.mk'),dep.stdout);
  const quote=s=>`'${s.replaceAll("'",`'\\''`)}'`;
  const command=['timeout',`--kill-after=${compilerKillGraceSeconds}s`,`${moduleSeconds}s`,fstar,...flags].map(quote).join(' ');
  const targets=roots.map(p=>join(dir,'checked',basename(p)+'.checked'));
  // Paths with make metacharacters would need a different escaping protocol.
  for(const p of [dir,...roots])if(/[\s#$:%\\]/.test(p))throw Error('unsupported proof workspace path: '+p);
  const compilerTargets=seconds===undefined||modelCache?projectCompilerTargets(dep.stdout,dir,Object.keys(current),targets):null;
  const derivedSeconds=compilerTargets?aggregateProofSeconds(compilerTargets.length,moduleSeconds):undefined;
  if(modelCache&&seconds!==undefined&&seconds>derivedSeconds)throw Error('project aggregate override exceeds graph-derived bound');
  const aggregateSeconds=seconds??derivedSeconds;
  const budget={policy:seconds===undefined?'graph-derived':'explicit',seconds:aggregateSeconds,moduleSeconds,
    compilerKillGraceSeconds,makeMarginSeconds,compilerTargets};
  say(`[budget] make ${aggregateSeconds}s (${budget.policy}); compiler ${moduleSeconds}s + ${compilerKillGraceSeconds}s kill grace; ${compilerTargets?.length??'uncounted'} project targets`);
  const makefile=`.DEFAULT_GOAL := verify\n.DELETE_ON_ERROR:\ninclude depend.mk\n${dir}/checked/%.checked:\n\t@echo '[CHECK] $*'\n\t@${command} "$<"\n\t@test -f "$@" && touch "$@"\n.PHONY: verify\nverify: ${targets.join(' ')}\n`;
  await put(join(dir,'Makefile'),makefile);
  const result=await runAsync('F* module checks'+tag,'make',['--jobs=2','--no-print-directory','-f','Makefile','verify'],dir,{seconds:aggregateSeconds});
  result.budget=budget;
  result.modules=[...result.log.matchAll(/^\[CHECK\] (.+)$/gm)].map(m=>m[1]);
  await put(join(dir,'last-check.log'),result.log);
  result.stats=proofStats(result.log);
  await put(join(dir,'last-check.stats.json'),JSON.stringify({rlimit,moduleSeconds,seconds:aggregateSeconds,budget,status:result.status,modules:result.modules,declarations:result.stats},null,2)+'\n');
  for(const row of result.stats)if(/^(Nickel\.)/.test(row.name)) {
    if(!row.queries.length) {say(`[theorem] ${row.name}: declaration ${row.declarationMs??'unmeasured'}ms; no SMT query`);continue;}
    const peak=row.queries.reduce((a,q)=>q.used/q.limit>a.used/a.limit?q:a);
    say(`[theorem] ${row.name}: declaration ${row.declarationMs??'unmeasured'}ms; queries ${row.queries.reduce((n,q)=>n+q.ms,0)}ms; peak ${peak.used}/${peak.limit} (${(100*peak.used/peak.limit).toFixed(2)}%); ${row.queries.some(q=>q.status==='failed')?'failed attempt':'passed'}`);
  }
  if(!result.stats.length)say('[theorem] no fresh measurements (checked results reused)');
  say(`[proof] ${result.modules.length} module checks; ${result.status===0?'verified or reused':'failed (see '+join(dir,'last-check.log')+')'}`);
  return result;
}
export async function seedChecked(from,to) {
  await mkdir(to,{recursive:true});
  for(const name of await readdir(from))if(name.endsWith('.checked'))await cp(join(from,name),join(to,name),{preserveTimestamps:true});
}
export async function toolKey({fstar,hax,models,modelCache,rlimit=100}) {
  const compiler=run('Rust compiler identity','rustc',['-vV'],process.cwd());
  if(compiler.status!==0)throw Error(compiler.log);
  return digest(JSON.stringify({fstar,hax,models,modelCache,flags:flagsAt(rlimit),rust:compiler.log,
    implementation:digest(await readFile(fileURLToPath(import.meta.url)))})).slice(0,24);
}
