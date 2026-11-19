// Actual duplicate-check contracts and retained weaker-root scope witnesses.
// Called inside the text gate's inherited permanent lock. No private compiler.
import assert from 'node:assert/strict';
import {replaceUniqueInFstarDeclaration} from './fstar-mutation-scope.mjs';
import fs from 'node:fs/promises';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {digest,put,verify,runAsync} from './proof-cache.mjs';
import {itemSpan} from './mutation-scope.mjs';
import {hasOrdinaryTheoremRejection} from './negative-proof-evidence.mjs';
import {deleteControlFixtures} from './delete-control-fixtures.mjs';
export const deleteExtractionIncludes = '+nickel_crdt::edit::sift_births +nickel_crdt::edit::heap_births +nickel_crdt::edit::drain_births +nickel_crdt::edit::ordered_births +nickel_crdt::edit::duplicate_births';
export const editProofHaxArgs=out=>['-C','--offline','--locked','-p','nickel-crdt',';','into','--output-dir',out,'-i',`-** ${deleteExtractionIncludes} +nickel_crdt::edit::**::receive +nickel_crdt::edit::**::edit +nickel_crdt::edit::**::new +nickel_crdt::edit::**::validate_new +nickel_crdt::edit::fact_equal +nickel_crdt::edit::push +nickel_crdt::edit::duplicate_events +nickel_crdt::edit::has_event +nickel_crdt::edit::has_fact +nickel_crdt::edit::choose_unseen +nickel_crdt::edit::clone_selected_fact +nickel_crdt::edit::canonical_step +nickel_crdt::edit::canonical +nickel_crdt::edit::ready +nickel_crdt::edit::choose_ready +nickel_crdt::edit::frontier +nickel_crdt::edit::validate_after +nickel_crdt::edit::extend_past +nickel_crdt::edit::past_pass +nickel_crdt::edit::past +nickel_crdt::edit::select_basis +nickel_crdt::edit::event_basis +nickel_crdt::edit::interpret_scheduled`,'fstar'];
const root=fileURLToPath(new URL('..',import.meta.url));
export function prepareDeleteMutation(c,source) {
  const patch=c.rust??c.view;
  assert.equal(digest(source),patch.hash,'delete control source drift: '+c.name);
  assert(patch.before.length>0&&patch.before!==patch.after,'nonempty changed anchor required');
  let at;
  if(c.rust){const[a,b]=itemSpan(source,patch.scope,c.name);assert.equal(source.slice(a,b),patch.before,'exact Rust item required');at=a;}
  else return replaceUniqueInFstarDeclaration(source,patch.scope,patch.before,patch.after,c.name);
  return source.slice(0,at)+patch.after+source.slice(at+patch.before.length);
}
export async function checkDeletePreparation(tree=root) {
  assert.equal(deleteControlFixtures.length,48);assert.equal(new Set(deleteControlFixtures.map(c=>c.name)).size,48);
  assert.equal(deleteControlFixtures.filter(c=>!c.positive).length,44);
  for(const c of deleteControlFixtures){assert(Boolean(c.rust)!==Boolean(c.view),'exactly one mutation kind');assert(c.positive?c.owner===null:typeof c.owner==='string','explicit semantic owner');const file=c.rust?'src/edit.rs':'proofs/generated/'+c.view.file,source=await fs.readFile(path.join(tree,file),'utf8');
    assert.notEqual(prepareDeleteMutation(c,source),source);
    assert.throws(()=>prepareDeleteMutation(c,source+'\n'),/source drift/);
    const patch=c.rust??c.view;
    const missing={...c,[c.rust?'rust':'view']:{...patch,scope:c.rust?'fn absent_delete_scope(':'absent_delete_scope'}};
    assert.throws(()=>prepareDeleteMutation(missing,source),/scope not found|declaration required/);
    const wrong={...c,[c.rust?'rust':'view']:{...patch,before:'__absent_delete_anchor__'}};
    assert.throws(()=>prepareDeleteMutation(wrong,source),/anchor/);
  }
  console.log('PASS delete preparation: 48 scoped cases, source drift/missing scope/missing anchor refuse');
}
// Called under check-edit-proofs' inherited permanent-file lock.
export async function checkDeleteContracts({proof,output,fstar,models,modelCache,selected}) {
  const cases=selected?selected.map(n=>{const c=deleteControlFixtures.find(c=>c.name===n);assert(c,'unknown delete control '+n);return c;}):deleteControlFixtures;
  assert.equal(new Set(cases.map(c=>c.name)).size,cases.length,'duplicate selected delete controls');
  const work=path.dirname(proof),rows=[];
  await fs.mkdir(output,{recursive:true});
  await fs.writeFile(path.join(output,'delete-planned.json'),JSON.stringify(cases.map(c=>({name:c.name,positive:c.positive,owner:c.owner})),null,2));
  await fs.writeFile(path.join(output,'delete-results.json'),'[]');
  console.log('DELETE-PLAN '+JSON.stringify(cases.map(c=>({name:c.name,positive:c.positive,owner:c.owner}))));
  for(const c of cases){const out=path.join(output,c.name),dir=path.join(work,c.name),p=path.join(dir,'proof');await fs.mkdir(out,{recursive:true});await fs.cp(proof,p,{recursive:true,preserveTimestamps:true});
    if(c.rust){const crate=path.join(dir,'crate');await fs.mkdir(crate,{recursive:true});for(const n of ['Cargo.toml','Cargo.lock','src','tests','proof-smoke'])await fs.cp(path.join(root,n),path.join(crate,n),{recursive:true});
      const source=await fs.readFile(path.join(root,'src/edit.rs'),'utf8');await fs.writeFile(path.join(crate,'src/edit.rs'),prepareDeleteMutation(c,source));
      // A private target per source is essential: hax metadata is package-named.
      const env={...process.env,CARGO_TARGET_DIR:path.join(dir,'target')};
      const test=await runAsync(c.name+' native','cargo',c.tests,crate,{env});await fs.writeFile(path.join(out,'native.log'),test.log);assert.equal(test.status,101,test.log);assert.match(test.log,/test result: FAILED/,'require test failure, not compilation failure');assert.match(test.log,/assertion [^\n]*failed/,'require actual native assertion failure');
      const extract=path.join(dir,'extract'),hax=process.env.NICKEL_HAX_BIN;assert(hax,'locked hax required');
      const ex=await runAsync(c.name+' hax',hax,editProofHaxArgs(extract),crate,{env});await fs.writeFile(path.join(out,'hax.log'),ex.log);assert.equal(ex.status,0,ex.log);
      const names=(await fs.readdir(extract)).filter(n=>/\.fsti?$/.test(n)).sort();assert.deepEqual(names,['Nickel_crdt.Edit.fst','Nickel_crdt.Event_layer.fst','Nickel_crdt.Event_shell.fst']);
      let changed=false;const inventory=[];for(const n of names){const bytes=await fs.readFile(path.join(extract,n));assert(!/\b(?:admit|assume|admit_smt_queries)\b/.test(bytes.toString()),'no extracted admissions');if(digest(bytes)!==digest(await fs.readFile(path.join(proof,n))))changed=true;await put(path.join(p,n),bytes);inventory.push([n,digest(bytes)]);}
      assert(changed,'native fault must change fresh extraction');await fs.writeFile(path.join(out,'extraction.json'),JSON.stringify(inventory,null,2));console.log('DELETE-EXTRACTION '+JSON.stringify({name:c.name,inventory}));
    }else{const source=await fs.readFile(path.join(proof,c.view.file),'utf8');await put(path.join(p,c.view.file),prepareDeleteMutation(c,source));}
    // Positive witnesses deliberately query weaker components. Other cases must
    // fail in their exact named owner; an earlier unrelated failure never counts.
    const ownerFile=c.owner?c.owner.slice(0,c.owner.lastIndexOf('.'))+'.fst':'Nickel.'+c.root+'.fst';
    const result=await verify({label:c.name,dir:p,roots:[path.join(p,ownerFile)],fstar,models,modelCache});await fs.writeFile(path.join(out,'proof.log'),result.log);await fs.writeFile(path.join(out,'result.json'),JSON.stringify(result,null,2));
    assert(result.modules.includes(ownerFile),'must actually check owner, not reuse it');if(c.rust)assert(result.modules.includes('Nickel_crdt.Edit.fst'),'changed Native must be rechecked');
    if(c.positive)assert.equal(result.status,0,result.log);else assert(hasOrdinaryTheoremRejection({status:result.status,log:result.log,theorem:c.owner,view:await fs.readFile(path.join(p,ownerFile),'utf8')}),result.log);
    rows.push({name:c.name,owner:c.owner,positive:c.positive,status:result.status,root:ownerFile});await fs.writeFile(path.join(output,'delete-results.json'),JSON.stringify(rows,null,2));console.log('PASS '+c.name+(c.positive?' (weaker-root scope witness)':''));
  }
  assert.deepEqual(rows.map(r=>r.name),cases.map(c=>c.name),'planned and executed delete inventory');
  console.log('DELETE-RESULTS '+JSON.stringify(rows));
}
