// Native implementation controls for the single-write checkpoint only.
// They do not certify F* rejection, graph validity, full refinement or SEC.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {holdLock, runAsync, digest} from './proof-cache.mjs';
import {scopedAnchor} from './mutation-scope.mjs';
const root=fileURLToPath(new URL('..',import.meta.url));
const output=path.resolve(process.argv[2]??path.join(root,'.cache/register-native'));
await fs.mkdir(output,{recursive:true});
assert(holdLock(path.join(output,'register-native.lock')),'register native output is owned by another invocation');
const source=await fs.readFile(path.join(root,'src/register.rs'),'utf8');
const modes=[
 ['write-advances-before-admission','pub fn write(','let mut candidate = self.clone();','self.next_counter = next; let mut candidate = self.clone();','limits_counter_and_opaque_bytes'],
 ['winner-reverses-clock','pub fn later(', 'a.payload.lamport > b.payload.lamport', 'a.payload.lamport < b.payload.lamport','concurrent_winners_losers_noedit_and_independent_keys'],
 ['winner-reverses-writer','pub fn later(', 'a.id.peer > b.id.peer', 'a.id.peer < b.id.peer','concurrent_winners_losers_noedit_and_independent_keys'],
 ['noedit-counted','pub fn write(', 'if bytes_equal(&value, &observed)', 'if false','concurrent_winners_losers_noedit_and_independent_keys'],
 ['receiver-contamination','fn validate(', '&read_history(&basis, &before.initial, fact.payload.key)', '&read_history(&before.facts, &before.initial, fact.payload.key)','author_basis_not_receiver_contamination'],
 ['loser-discarded','fn prepare(', 'graph::push(&mut next.facts, fact.clone(), invalid)?;', 'next.facts.clear(); graph::push(&mut next.facts, fact.clone(), invalid)?;','concurrent_winners_losers_noedit_and_independent_keys'],
 ['receive-publishes-error','pub fn receive(', 'shell::receive_into(self, &fact, &(), planned, Admission::Added, Admission::Duplicate)', 'let result = shell::receive_into(self, &fact, &(), planned, Admission::Added, Admission::Duplicate); if result.is_err() { self.facts.push(fact); } result','rejection_and_duplicate_preserve_full_snapshot'],
 ['clock-ignores-past','pub fn next_lamport(', 'if fact.payload.lamport > highest', 'if false','concurrent_winners_losers_noedit_and_independent_keys'],
 ['producer-chain-skipped','fn previous(', 'if id.counter > 1', 'if false','rejection_and_duplicate_preserve_full_snapshot'],
 ['policy-swaps-equality-order','const OPS:', 'same_id, less_id,', 'less_id, same_id,','rejection_and_duplicate_preserve_full_snapshot'],
];
const results=[];
for(const [name,header,anchor,replacement,test] of [['positive',null,null,null,null],...modes]){
 const dir=path.join(output,name);await fs.mkdir(dir,{recursive:true});
 await fs.cp(path.join(root,'src'),path.join(dir,'src'),{recursive:true,force:true});
 await fs.mkdir(path.join(dir,'tests'),{recursive:true});
 await fs.mkdir(path.join(dir,'examples'),{recursive:true});
 await fs.copyFile(path.join(root,'examples/register-checkpoint.rs'),path.join(dir,'examples/register-checkpoint.rs'));
 await fs.copyFile(path.join(root,'tests/register_checkpoint.rs'),path.join(dir,'tests/register_checkpoint.rs'));
 for(const f of ['Cargo.toml','Cargo.lock'])await fs.copyFile(path.join(root,f),path.join(dir,f));
 await fs.cp(path.join(root,'proof-smoke'),path.join(dir,'proof-smoke'),{recursive:true,force:true});
 let changed=source;
 if(header){let at;
 if(header==='const OPS:'){
   assert.equal(source.split(header).length,2,'unique policy declaration');
   const start=source.indexOf(header),end=source.indexOf(';',start);
   assert(end>start,'complete policy declaration');
   const declaration=source.slice(start,end);
   assert.equal(declaration.split(anchor).length,2,'unique construction anchor');
   at=start+declaration.indexOf(anchor);
 } else { at=scopedAnchor(source,header,anchor,name); }
 assert(Number.isInteger(at));changed=source.slice(0,at)+replacement+source.slice(at+anchor.length);await fs.writeFile(path.join(dir,'src/register.rs'),changed);}
 const result=await runAsync(name,'cargo',['test','--offline','--locked','-p','nickel-crdt',...(test?['--test','register_checkpoint',test]:[])],dir,{seconds:60,env:{...process.env,CARGO_TARGET_DIR:path.join(output,'target'),CARGO_PROFILE_DEV_DEBUG:'0',CARGO_PROFILE_TEST_DEBUG:'0'}});
 await fs.writeFile(path.join(dir,'native.log'),result.log);
 if(!header){
  assert.equal(result.status,0,result.log);
  const caller=await runAsync('external register caller','cargo',['run','--offline','--locked','-p','nickel-crdt','--example','register-checkpoint'],dir,{seconds:60,env:{...process.env,CARGO_TARGET_DIR:path.join(output,'target')}});
  await fs.writeFile(path.join(dir,'caller.log'),caller.log);assert.equal(caller.status,0,caller.log);
 }
 else {assert.equal(result.status,101,name+': ordinary test failure required');assert(result.log.includes(test+' ... FAILED'),name+': owning external test did not fail');assert(!result.log.includes('could not compile'),name+': compile failure is not semantic evidence');}
 results.push({name,status:result.status,seconds:result.seconds,source:digest(changed),log:digest(result.log)});
}
await fs.writeFile(path.join(output,'receipt.json'),JSON.stringify({source:digest(source),results},null,2)+'\n');
console.log('PASS: register native positive and '+modes.length+' actual-source controls; no proof/SEC claim');
