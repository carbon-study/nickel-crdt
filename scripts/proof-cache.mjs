import {spawnSync} from 'node:child_process';
import {createHash} from 'node:crypto';
import {mkdir,readFile,writeFile,rename,readdir,rm,cp} from 'node:fs/promises';
import {join,basename} from 'node:path';
import {fileURLToPath} from 'node:url';

export const proofFlags=['--cmi','--warn_error','-331','--split_queries','on_failure','--fuel','4','--ifuel','4','--z3rlimit','100','--timing','--query_stats'];
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
export function run(label,bin,args,cwd,{env=process.env,seconds=60}={}) {
  const start=performance.now();
  const r=spawnSync('timeout',['--kill-after=2s',`${seconds}s`,bin,...args],{cwd,env,encoding:'utf8',maxBuffer:32*1024*1024});
  const elapsed=(performance.now()-start)/1000;
  console.log(`[time] ${label}: ${elapsed.toFixed(3)}s (exit ${r.status ?? r.signal})`);
  if(r.error)throw r.error;
  return {status:r.status,stdout:r.stdout??'',log:(r.stdout??'')+(r.stderr??''),seconds:elapsed};
}
// Workspace source hashes, not source mtimes, invalidate direct cache entries.
// Make/F* then propagate invalidation through the actual dependency graph.
export async function verify({dir,roots,fstar,models,modelCache,seconds=60,moduleSeconds=60,rlimit=100}) {
  if(!Number.isInteger(moduleSeconds)||moduleSeconds<1||moduleSeconds>180)throw Error('moduleSeconds must be an integer from 1 to 180');
  if(modelCache&&moduleSeconds>60)throw Error('project module budget cannot exceed 60 seconds');
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
  const dep=run('F* dependency graph',fstar,[...flags,'--dep','full',...roots],dir);
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
  const command=['timeout','--kill-after=2s',`${moduleSeconds}s`,fstar,...flags].map(quote).join(' ');
  const targets=roots.map(p=>join(dir,'checked',basename(p)+'.checked'));
  // Paths with make metacharacters would need a different escaping protocol.
  for(const p of [dir,...roots])if(/[\s#$:%\\]/.test(p))throw Error('unsupported proof workspace path: '+p);
  const makefile=`.DEFAULT_GOAL := verify\n.DELETE_ON_ERROR:\ninclude depend.mk\n${dir}/checked/%.checked:\n\t@echo '[CHECK] $*'\n\t@${command} "$<"\n\t@test -f "$@" && touch "$@"\n.PHONY: verify\nverify: ${targets.join(' ')}\n`;
  await put(join(dir,'Makefile'),makefile);
  const result=run('F* module checks','make',['--jobs=2','--no-print-directory','-f','Makefile','verify'],dir,{seconds});
  result.modules=[...result.log.matchAll(/^\[CHECK\] (.+)$/gm)].map(m=>m[1]);
  await put(join(dir,'last-check.log'),result.log);
  result.stats=proofStats(result.log);
  await put(join(dir,'last-check.stats.json'),JSON.stringify({rlimit,moduleSeconds,seconds,status:result.status,modules:result.modules,declarations:result.stats},null,2)+'\n');
  for(const row of result.stats)if(/^(Nickel\.)/.test(row.name)) {
    if(!row.queries.length) {console.log(`[theorem] ${row.name}: declaration ${row.declarationMs??'unmeasured'}ms; no SMT query`);continue;}
    const peak=row.queries.reduce((a,q)=>q.used/q.limit>a.used/a.limit?q:a);
    console.log(`[theorem] ${row.name}: declaration ${row.declarationMs??'unmeasured'}ms; queries ${row.queries.reduce((n,q)=>n+q.ms,0)}ms; peak ${peak.used}/${peak.limit} (${(100*peak.used/peak.limit).toFixed(2)}%); ${row.queries.some(q=>q.status==='failed')?'failed attempt':'passed'}`);
  }
  if(!result.stats.length)console.log('[theorem] no fresh measurements (checked results reused)');
  console.log(`[proof] ${result.modules.length} module checks; ${result.status===0?'verified or reused':'failed (see '+join(dir,'last-check.log')+')'}`);
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
