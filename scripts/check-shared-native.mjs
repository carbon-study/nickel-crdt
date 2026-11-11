// Isolated native implementation-sensitivity checks for the experimental API.
// No mutation touches the checkout or accepted edit/proof runner.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import {mkdirSync} from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {digest,holdLock,runAsync} from './proof-cache.mjs';
import {scopedAnchor} from './mutation-scope.mjs';
const root=fileURLToPath(new URL('..',import.meta.url));
const output=path.resolve(process.argv[2] ?? path.join(root,'.cache/shared-native'));
mkdirSync(output,{recursive:true});
// Lock the actual workspace location, including across distinct checkouts.
assert(holdLock(path.join(output,'.shared-native.lock')),'another shared-native invocation holds this output workspace');
const modes=[
  [
    "payload-equality",
    "causal.rs",
    "fn event_equal<",
    "eq(&left.payload, &right.payload)",
    "true",
    "atomic_map::tests::duplicates_conflicts_and_capacity_leave_everything_unchanged"
  ],
  [
    "dependency-equality",
    "causal.rs",
    "fn event_equal<",
    "ids_eq(&left.after, &right.after)",
    "true",
    "atomic_map::tests::ordered_dependencies_are_part_of_duplicate_identity"
  ],
  [
    "early-publication",
    "atomic_map.rs",
    "pub fn receive(",
    "crate::event_shell::receive_into(\n            self,\n            &event,\n            &(),\n            plan_incoming,\n            Admission::Added,\n            Admission::Duplicate,\n        )",
    "let result = crate::event_shell::receive_into(\n            self,\n            &event,\n            &(),\n            plan_incoming,\n            Admission::Added,\n            Admission::Duplicate,\n        ); if result.is_err() { self.events.push(event); } result",
    "atomic_map::tests::received_final_failure_and_payload_bounds_are_transactional"
  ],
  [
    "empty-author-basis",
    "atomic_map.rs",
    "fn validate_incoming(",
    "validate(&basis, event)",
    "validate(&[], event)",
    "atomic_map::tests::basis_is_exact_and_stored_order"
  ],
  [
    "skip-ready-dependency",
    "event_layer.rs",
    "fn ready<",
    "if has_id(done, &after[i], id_eq) {",
    "if true {",
    "atomic_map::tests::independent_closure_and_schedule_oracles_all_small_dags"
  ],
  [
    "reverse-operation-order",
    "atomic_map.rs",
    "fn apply(",
    "for op in batch {",
    "for op in batch.iter().rev() {",
    "stored_batch_order_is_preserved_after_record_creation"
  ]
];
const sources=new Map(await Promise.all(['causal.rs','atomic_map.rs','event_layer.rs','event_shell.rs'].map(async name=>[name,await fs.readFile(path.join(root,'src',name),'utf8')])));
const receipts=[];
for(const [mode,file,header,anchor,replacement,test] of [['positive',null,null,null,null,null,null],...modes]) {
  const dir=path.join(output,mode);
  await fs.mkdir(dir,{recursive:true});
  await fs.cp(path.join(root,'src'),path.join(dir,'src'),{recursive:true,force:true});
  await fs.cp(path.join(root,'tests/shared_layer.rs'),path.join(dir,'shared_layer.rs'));
  await fs.mkdir(path.join(dir,'tests'),{recursive:true});
  await fs.copyFile(path.join(dir,'shared_layer.rs'),path.join(dir,'tests/shared_layer.rs'));
  await fs.writeFile(path.join(dir,'Cargo.toml'),'[package]\nname="nickel-crdt"\nversion="0.0.0"\nedition="2021"\n[workspace]\n');
  if(file) {
    const source=sources.get(file), span=scopedAnchor(source,header,anchor,mode);
    const at=typeof span==='number'?span:span.at;
    assert(Number.isInteger(at),'scopedAnchor return shape');
    await fs.writeFile(path.join(dir,'src',file),source.slice(0,at)+replacement+source.slice(at+anchor.length));
  }
  const result=await runAsync(mode,'cargo',['test','--offline',...(test?[test]:[])],dir,{seconds:60,env:{...process.env,CARGO_PROFILE_DEV_DEBUG:'0',CARGO_PROFILE_TEST_DEBUG:'0',CARGO_TARGET_DIR:path.join(dir,'target')}});
  await fs.writeFile(path.join(dir,'native.log'),result.log);
  if(mode==='positive')assert.equal(result.status,0,result.log);
  else {
    assert.equal(result.status,101,mode+': must fail a native assertion, not timeout or preparation');
    assert(result.log.includes('assertion `left == right` failed'),mode+': expected actual comparison assertion');
    assert(result.log.includes(test.split('::').at(-1)+' ... FAILED'),mode+': owning test did not fail');
    assert(!result.log.includes('could not compile'),mode+': compilation is not a semantic control');
  }
  receipts.push({mode,status:result.status,seconds:result.seconds,source:file?digest(await fs.readFile(path.join(dir,'src',file))):null,log:digest(result.log)});
}
await fs.writeFile(path.join(output,'receipt.json'),JSON.stringify({sources:Object.fromEntries([...sources].map(([name,source])=>[name,digest(source)])),receipts},null,2)+'\n');
console.log('shared-native: positive and '+modes.length+' actual-source controls passed');
