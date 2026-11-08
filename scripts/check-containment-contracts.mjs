// Containment composes the whole-fact absence law; its boundary uses checked
// vector/slice equations with the native/model implementation facts withheld.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import {put,verify} from './proof-cache.mjs';
import {hasOrdinaryTheoremRejection} from './negative-proof-evidence.mjs';
export async function checkContainmentContracts({proof,output,fstar,models,modelCache}) {
  const file=path.join(proof,'Nickel.EditWellFormed.fst'),original=await fs.readFile(file,'utf8');
  for(const[name,needle,theorem]of[
    ['containment-without-index','Nickel.Vector.slice_index facts (mk_usize i);','absence_on_whole_facts'],
    ['containment-without-length','Nickel.Vector.slice_length facts;','absence_on_whole_facts'],
    ['containment-without-absence','absence_on_whole_facts next id;','presence_survives_containment'],
  ]) {
    assert.equal(original.split(needle).length,2);
    const view=original.replace(needle,'();');
    try {await put(file,view);const result=await verify({dir:proof,roots:[file],fstar,models,modelCache});
      await fs.writeFile(path.join(output,name+'.proof.log'),result.log);
      assert(hasOrdinaryTheoremRejection({status:result.status,log:result.log,theorem:'Nickel.EditWellFormed.'+theorem,view}),'require ordinary containment dependency rejection: '+result.log);
      console.log('PASS '+name+': caller needs its checked contract');
    }finally{await put(file,original);}
  }
}
