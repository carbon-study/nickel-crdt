// Actual-Rust body mutants are separate; these remove the contract interface.
import assert from 'node:assert/strict';import fs from 'node:fs/promises';import path from 'node:path';
import {put,verify} from './proof-cache.mjs';
import {hasOrdinaryTheoremRejection} from './negative-proof-evidence.mjs';
export async function checkPushContracts({proof,output,fstar,models,modelCache}) {
 const file=path.join(proof,'Nickel.EditAccepted.fst'),original=await fs.readFile(file,'utf8');
 const pattern=' [SMTPat (Native.push before fact)]';assert.equal(original.split(pattern).length,2);
 const cases=[['push-without-pattern','append_fresh_preserves_unique',original.replace(pattern,'')]];
 for(const name of ['append_fresh_preserves_unique','append_whole_fact','push_has_exact_contents','push_membership']) {
  const start=new RegExp('^let '+name+' ','m').exec(original)?.index;assert(start!==undefined);
  const next=/\nlet (?:rec )?\w+ /.exec(original.slice(start+4));const end=next?start+4+next.index:original.length;
  const body=original.slice(start,end),needle='Tactics.prune "Nickel_crdt.Edit.push";';assert.equal(body.split(needle).length,2);
  const replacement=needle+'\n    Tactics.prune "Nickel.EditAccepted.push_result_is_exact";';
  cases.push(['push-without-contract-'+name,name,original.slice(0,start)+body.replace(needle,replacement)+original.slice(end)]);
 }
 for(const [name,lemma,view] of cases) {
  try {
   await put(file,view);const result=await verify({dir:proof,roots:[file],fstar,models,modelCache});
   await fs.writeFile(path.join(output,name+'.proof.log'),result.log);
   assert(hasOrdinaryTheoremRejection({status:result.status,log:result.log,theorem:'Nickel.EditAccepted.'+lemma,view}), 'require ordinary push-contract dependency rejection: '+result.log);
   console.log('PASS '+name+': actual caller requires the push contract');
  } finally { await put(file,original); }
 }
}
