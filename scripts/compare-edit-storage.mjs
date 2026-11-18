// Manual source-bound diagnostic, not a replacement library or a proof gate.
// Only copied crates change; the ordinary library/extraction path is untouched.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import {spawnSync} from 'node:child_process';
const root=fileURLToPath(new URL('..',import.meta.url));
const output=path.resolve(process.argv[2]??'.cache/edit-storage-comparison');
const profiles=process.argv.includes('--profiles');
await fs.mkdir(output,{recursive:true});
const source=await fs.readFile(path.join(root,'src/edit.rs'),'utf8');
const digest=s=>createHash('sha256').update(s).digest('hex');
const replace=(s,a,b)=>{assert.equal(s.split(a).length,2,'unique source boundary: '+a);return s.replace(a,b);};
const insertion=`
// Diagnostic alternative: requires strictly ID-sorted input and a fresh ID.
// Public duplicate/validation checks still run before this function.
fn insert_sorted(facts: &[Fact], fact: &Fact) -> Result<Vec<Fact>, Error> {
    let mut out = Vec::new();
    let mut inserted = false;
    for old in facts {
        if !inserted && event_lt(fact.id, old.id) {
            push(&mut out, fact.clone())?;
            inserted = true;
        }
        push(&mut out, old.clone())?;
    }
    if !inserted { push(&mut out, fact.clone())?; }
    Ok(out)
}
#[cfg(test)]
mod storage_comparison {
    use super::*;
    fn permutations(prefix: Vec<Fact>, rest: Vec<Fact>) {
        if rest.is_empty() {
            let mut stored = Vec::new();
            for incoming in &prefix {
                let before = stored.clone();
                stored = insert_sorted(&stored, incoming).unwrap();
                assert_eq!(stored.len(), before.len()+1);
                for pair in stored.windows(2) { assert!(event_lt(pair[0].id,pair[1].id)); }
                for old in &before { assert_eq!(stored.iter().filter(|f| fact_equal(f,old)).count(),1); }
                assert_eq!(stored.iter().filter(|f| fact_equal(f,incoming)).count(),1);
                let mut appended = before; appended.push(incoming.clone());
                let expected = canonical(&appended).unwrap();
                assert!(stored.iter().zip(&expected).all(|(a,b)| fact_equal(a,b)));
            }
        } else {
            for i in 0..rest.len() {
                let mut next=prefix.clone(); next.push(rest[i].clone());
                let mut todo=rest.clone(); todo.remove(i); permutations(next,todo);
            }
        }
    }
    #[test]
    fn exact_sorted_content_matches_retained_canonicalizer() {
        // Both writers, unequal counters, distinct payload/delete/gap fields.
        // These are storage-level facts, not all admissible causal histories.
        let facts=(0..6).map(|i| Fact {
            id:EventId{writer:if i%2==0 {Writer(1)} else {Writer(2)},counter:i+1},
            after:vec![],insert:vec![65+i as u32],delete:vec![],gap:Some(i as usize),
        }).collect();
        permutations(vec![],facts);
    }
}
`;
const instrument=s=>{
 s=replace(s,'        if Self::duplicate(&self.facts, fact)? {','        let profile_start = std::time::Instant::now();\n        if Self::duplicate(&self.facts, fact)? {');
 s=replace(s,'        Self::validate_new(&self.facts, self.limits, fact)?;',`        let profile_identity = profile_start.elapsed().as_nanos();
        Self::validate_new(&self.facts, self.limits, fact)?;
        let profile_validation = profile_start.elapsed().as_nanos();`);
 s=replace(s,'        let mut next = self.clone();',`        let mut next = self.clone();
        let profile_clone = profile_start.elapsed().as_nanos();`);
 s=replace(s,'        let tree = interpret(&next.facts)?;',`        let profile_storage = profile_start.elapsed().as_nanos();
        let tree = interpret(&next.facts)?;
        let profile_replay = profile_start.elapsed().as_nanos();`);
 return replace(s,'        Ok(Some(next.with_tree(tree)))',`        eprintln!("{{\\\"events\\\":{},\\\"identity_ns\\\":{},\\\"validation_ns\\\":{},\\\"clone_ns\\\":{},\\\"storage_ns\\\":{},\\\"replay_ns\\\":{}}}",
            next.facts.len(), profile_identity, profile_validation-profile_identity,
            profile_clone-profile_validation, profile_storage-profile_clone, profile_replay-profile_storage);
        Ok(Some(next.with_tree(tree)))`);
};
const records=[];
function run(label,cmd,args,cwd,timeout=60_000) {
 const start=Date.now();
 const r=spawnSync(cmd,args,{cwd,timeout,killSignal:'SIGKILL',encoding:'utf8',maxBuffer:64*1024*1024,
   env:{...process.env,CARGO_TARGET_DIR:path.join(root,'target','edit-storage-comparison')}});
 return fs.writeFile(path.join(output,label+'.stdout'),r.stdout??'').then(()=>fs.writeFile(path.join(output,label+'.stderr'),r.stderr??'')).then(()=>{
  records.push({label,status:r.status,signal:r.signal,error:r.error?.code,elapsed_ms:Date.now()-start});return r;
 });
}
let reference;
for(const mode of ['reference','sorted','drop-control']) {
 const crate=path.join(output,mode); await fs.mkdir(crate,{recursive:true});
 for(const name of ['Cargo.toml','Cargo.lock','src','tests','proof-smoke','examples'])
  await fs.cp(path.join(root,name),path.join(crate,name),{recursive:true});
 let code=source;
 if(mode!=='reference') {
  code=replace(code,'        push(&mut next.facts, fact.clone())?;\n        next.facts = canonical(&next.facts)?;',
    '        next.facts = insert_sorted(&self.facts, fact)?;');
  code+=insertion;
  if(mode==='drop-control') code=replace(code,'        push(&mut out, old.clone())?;','        // Deliberately drop old facts.');
 }
 // Correctness checks use the untimed alternative; profile adds timers later.
 await fs.writeFile(path.join(crate,'src/edit.rs'),code);
 const tested=await run(mode+'-native','cargo',['test','--offline','--locked','-p','nickel-crdt'],crate);
 if(mode==='drop-control') {
  assert.equal(tested.status,101,tested.stderr);assert.match(tested.stdout,/test result: FAILED/);continue;
 }
 assert.equal(tested.status,0,tested.stderr);
 const fixtures=await run(mode+'-fixtures','cargo',['run','--release','--offline','--locked','--example','edit-reference'],crate);
 assert.equal(fixtures.status,0,fixtures.stderr);
 const parsed=JSON.parse(fixtures.stdout); assert.equal(parsed.length,150);
 assert.equal(parsed.reduce((n,c)=>n+c.orders,0),882);
 if(mode==='reference')reference=fixtures.stdout;else assert.equal(fixtures.stdout,reference,'exact finite fixture equality');
 if(profiles) {
  await fs.writeFile(path.join(crate,'src/edit.rs'),instrument(code));
  const built=await run(mode+'-profile-build','cargo',['build','--release','--offline','--locked','--example','edit-profile'],crate);
  assert.equal(built.status,0,built.stderr);
  for(const shape of ['append','prepend','frontloaded-delete']) {
   const r=await run(mode+'-'+shape,path.join(root,'target/edit-storage-comparison/release/examples/edit-profile'),[shape],crate,45_000);
   // A capped run is retained as incomplete; never counts as a passing profile.
   assert(r.status===0||r.error?.code==='ETIMEDOUT',r.stderr);
   const checked=r.stdout.trim().split('\n').filter(Boolean).map(JSON.parse);
   const stages=r.stderr.trim().split('\n').filter(Boolean).map(JSON.parse);
   const complete=checked.at(-1)?.complete===true;
   assert.equal(complete,r.status===0);
   if(complete)assert.equal(stages.length,256);
   const sums=Object.fromEntries(['identity_ns','validation_ns','clone_ns','storage_ns','replay_ns'].map(k=>[k,stages.reduce((n,row)=>n+row[k],0)]));
   records.push({mode,shape,complete,checked_pairs:checked.filter(x=>'events'in x).length,completed_plans:stages.length,stage_sums_ns:sums,last_plan:stages.at(-1)});
  }
 }
}
await fs.writeFile(path.join(output,'receipt.json'),JSON.stringify({source_sha256:digest(source),script_sha256:digest(await fs.readFile(fileURLToPath(import.meta.url))),profiles,records},null,2)+'\n');
console.log(JSON.stringify({output,source_sha256:digest(source),profiles,finite_fixtures:'150 histories / 882 schedules match exactly',drop_control:'rejected by native tests'}));
