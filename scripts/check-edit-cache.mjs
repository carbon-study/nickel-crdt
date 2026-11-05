// Isolated derived-node cache experiment. No enabled library/proof path changes.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import {spawnSync} from 'node:child_process';
const root=fileURLToPath(new URL('..',import.meta.url));
const output=path.resolve(process.argv[2]??'.cache/edit-cache');
await fs.mkdir(output,{recursive:true});
const original=await fs.readFile(path.join(root,'src/edit.rs'),'utf8');
const digest=x=>createHash('sha256').update(x).digest('hex');
const change=(s,a,b)=>{assert.equal(s.split(a).length,2,'exact unique boundary: '+a);return s.replace(a,b);};
const start=original.indexOf('fn interpret(facts:');
const end=original.indexOf('\n#[derive(Clone, Debug, PartialEq, Eq)]\npub struct Replica',start);
assert(start>=0&&end>start);
const interpreter=original.slice(start,end);
const builderStart=interpreter.indexOf('        let selected = past(');
const builderEnd=interpreter.indexOf('        for i in 0..ops.len() {\n            result.add',builderStart);
assert(builderStart>0&&builderEnd>builderStart);
const builder=interpreter.slice(builderStart,builderEnd);
const trace=`
mod causal_trace {
    use super::*;
    use std::collections::{BTreeMap,BTreeSet};
    use std::sync::{Mutex,OnceLock};
    #[derive(Default)]
    struct State { rows:BTreeMap<String,(Vec<Node>,BTreeSet<String>)>, observations:usize }
    static STATE:OnceLock<Mutex<State>>=OnceLock::new();
    pub fn record(facts:&[Fact],event:&Fact,basis:&[Fact],ops:&[Node]) {
        let key=format!("{:?}|{:?}",event,basis);
        let context=format!("{:?}",facts);
        let mut state=STATE.get_or_init(||Mutex::new(State::default())).lock().unwrap();
        state.observations+=1;
        if let Some((old,contexts))=state.rows.get_mut(&key) {
            assert_eq!(old,ops,"derived nodes changed with the same event and causal facts");
            contexts.insert(context);
        } else { state.rows.insert(key,(ops.to_vec(),BTreeSet::from([context]))); }
    }
    pub fn summary() {
        let state=STATE.get_or_init(||Mutex::new(State::default())).lock().unwrap();
        let varied=state.rows.values().filter(|(_,contexts)|contexts.len()>1).count();
        assert!(varied>0,"locality witness must include changed full histories");
        eprintln!("CAUSAL_TRACE observations={} keys={} varied_context_keys={}",state.observations,state.rows.len(),varied);
    }
}
// Exported only in this generated diagnostic crate, not in the library API.
pub fn cache_trace_summary() { causal_trace::summary(); }
`;
let traced=change(original,'        for i in 0..ops.len() {\n            result.add',
 '        causal_trace::record(facts,event,&basis,&ops);\n        for i in 0..ops.len() {\n            result.add')+trace;
let cachedInterpreter=interpreter.replace('fn interpret(facts: &[Fact]) -> Result<Tree, Error> {',
 'fn interpret_cached(facts: &[Fact], cache: &[(EventId,Vec<Node>)]) -> Result<(Tree,Vec<(EventId,Vec<Node>)>), Error> {');
cachedInterpreter=cachedInterpreter.slice(0,cachedInterpreter.indexOf(builder))+`        let cached = cache.iter().find(|(id,_)| *id == event.id);
        let ops = if let Some((_,nodes)) = cached { nodes.clone() } else {
${builder}
            ops
        };
`+cachedInterpreter.slice(cachedInterpreter.indexOf(builder)+builder.length);
cachedInterpreter=change(cachedInterpreter,'    Ok(result)','    Ok((result,operations))');
let cached=change(original,'    tree: Tree,\n}', '    tree: Tree,\n    cache: Vec<(EventId,Vec<Node>)>,\n}');
cached=change(cached,'            tree: Tree::default(),','            tree: Tree::default(),\n            cache: Vec::new(),');
cached=change(cached,'        let tree = interpret(&next.facts)?;',`        let (tree,cache) = interpret_cached(&next.facts,&self.cache)?;
        // Full replay is the correctness witness, removed only in timing copies.
        assert_eq!(tree,interpret(&next.facts)?,"cached replay disagrees with full replay");
        next.cache = cache;`)+ '\n'+cachedInterpreter;
const fixtures=await fs.readFile(path.join(root,'examples/edit-reference.rs'),'utf8');
const records=[];
async function run(label,cmd,args,cwd,seconds=60) {
 const then=Date.now();
 const r=spawnSync('timeout',['--kill-after=2s',seconds+'s',cmd,...args],{cwd,encoding:'utf8',maxBuffer:64*1024*1024,
  env:{...process.env,CARGO_TARGET_DIR:path.join(root,'target','edit-cache-diagnostic')}});
 await fs.writeFile(path.join(output,label+'.stdout'),r.stdout??'');await fs.writeFile(path.join(output,label+'.stderr'),r.stderr??'');
 records.push({label,status:r.status,signal:r.signal,elapsed_ms:Date.now()-then});assert(!r.error,String(r.error));return r;
}
let reference;
for(const mode of ['trace','cached','receiver-basis-control','cache-corruption-control']) {
 const crate=path.join(output,mode);await fs.mkdir(crate,{recursive:true});
 for(const name of ['Cargo.toml','Cargo.lock','src','tests','proof-smoke','examples'])await fs.cp(path.join(root,name),path.join(crate,name),{recursive:true});
 let code=mode==='trace'?traced:cached;
 if(mode==='receiver-basis-control') {
  // A tempting but wrong shortcut: let unrelated receiver facts shape authors.
  code=change(traced,'            if has_event(&selected, id) {','            if true {');
 }
 if(mode==='cache-corruption-control') {
  code=change(cached,'if let Some((_,nodes)) = cached { nodes.clone() }',
   'if let Some((_,nodes)) = cached { let mut changed=nodes.clone(); if !changed.is_empty() { changed[0].scalar=0; } changed }');
 }
 await fs.writeFile(path.join(crate,'src/edit.rs'),code);
 await fs.writeFile(path.join(output,mode+'-correctness.rs'),code);
 const native=await run(mode+'-native','cargo',['test','--offline','--locked','-p','nickel-crdt','--test','edit_admit'],crate);
 if(mode.endsWith('control')) {
  assert.equal(native.status,101,native.stderr);assert.match(native.stdout,/test result: FAILED/);
  assert.match(native.stdout,mode==='receiver-basis-control'?/derived nodes changed with the same event and causal facts/:/cached replay disagrees with full replay/);continue;
 }
 assert.equal(native.status,0,native.stderr);
 await fs.writeFile(path.join(crate,'examples/edit-reference.rs'),mode==='trace'?change(fixtures,'    println!("[{}]", cases.join(","));',
  '    nickel_crdt::edit::cache_trace_summary();\n    println!("[{}]", cases.join(","));'):fixtures);
 const result=await run(mode+'-fixtures','cargo',['run','--release','--offline','--locked','--example','edit-reference'],crate);
 assert.equal(result.status,0,result.stderr);
 const cases=JSON.parse(result.stdout);assert.equal(cases.length,150);assert.equal(cases.reduce((n,c)=>n+c.orders,0),882);
 if(mode==='trace') {
  assert.match(result.stderr,/CAUSAL_TRACE observations=\d+ keys=\d+ varied_context_keys=[1-9]\d*/);
  const match=result.stderr.match(/CAUSAL_TRACE observations=(\d+) keys=(\d+) varied_context_keys=(\d+)/);
  records.push({trace_observations:Number(match[1]),event_basis_keys:Number(match[2]),varied_context_keys:Number(match[3])});
  reference=result.stdout;
 } else assert.equal(result.stdout,reference,'same full finite export');
 if(mode==='cached'&&process.argv.includes('--profiles')) {
  const timed=change(code,'        assert_eq!(tree,interpret(&next.facts)?,"cached replay disagrees with full replay");','        // Timing only: replay assertion omitted. Not a verified cache path.');
  await fs.writeFile(path.join(crate,'src/edit.rs'),timed);
  await fs.writeFile(path.join(output,'cached-timing.rs'),timed);
  const build=await run('cached-profile-build','cargo',['build','--release','--offline','--locked','--example','edit-profile'],crate);assert.equal(build.status,0,build.stderr);
  for(const shape of ['append','prepend','frontloaded-delete']) {
   const r=await run('cached-'+shape,path.join(root,'target/edit-cache-diagnostic/release/examples/edit-profile'),[shape],crate,45);
   assert(r.status===0||r.status===124,r.stderr);
   const rows=r.stdout.trim().split('\n').filter(Boolean).map(JSON.parse);
   const complete=rows.at(-1)?.complete===true;assert.equal(complete,r.status===0);
   if(complete)assert.equal(rows.filter(x=>'events'in x).length,128);
   records.push({shape,complete,checked_pairs:rows.filter(x=>'events'in x).length,last_checked:rows.filter(x=>'events'in x).at(-1),summary:complete?rows.at(-1):null});
  }
 }
}
const input_hashes={};for(const file of ['Cargo.toml','Cargo.lock','tests/edit_admit.rs','examples/edit-reference.rs','examples/edit-profile.rs'])input_hashes[file]=digest(await fs.readFile(path.join(root,file)));
await fs.writeFile(path.join(output,'receipt.json'),JSON.stringify({input_hashes,source_sha256:digest(original),script_sha256:digest(await fs.readFile(fileURLToPath(import.meta.url))),records},null,2)+'\n');
console.log(JSON.stringify({source_sha256:digest(original),histories:150,schedules:882,exact_cached_tree_comparison:'every plan reaching tree construction in correctness copies',controls:'both rejected; see logs',output}));
