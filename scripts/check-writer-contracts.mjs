// The shared writer-code contract must serve both actual native callers.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import {put,verify} from './proof-cache.mjs';
import {hasOrdinaryTheoremRejection} from './negative-proof-evidence.mjs';
export async function checkWriterContracts({proof,output,fstar,models,modelCache}) {
  const identityFile=path.join(proof,'Nickel.EditIdentity.fst');
  const acceptedFile=path.join(proof,'Nickel.EditAccepted.fst');
  const identity=await fs.readFile(identityFile,'utf8');
  const accepted=await fs.readFile(acceptedFile,'utf8');
  const pattern=' [SMTPat (Native.writer_index writer)]';
  assert.equal(identity.split(pattern).length,2);
  const needle='Tactics.prune "Nickel_crdt.Edit.writer_index";';
  assert.equal(identity.split(needle).length,2);
  assert.equal(accepted.split(needle).length,2);
  const without=needle+'\n    Tactics.prune "Nickel.EditIdentity.writer_index_is_exact";';
  const cases=[
    ['writer-without-pattern',identityFile,identity.replace(pattern,''),'Nickel.EditIdentity.writer_equality_exact'],
    ['writer-without-equality-contract',identityFile,identity.replace(needle,without),'Nickel.EditIdentity.writer_equality_exact'],
    ['writer-without-order-contract',acceptedFile,accepted.replace(needle,without),'Nickel.EditAccepted.event_order_is_key_order'],
  ];
  for(const [name,file,view,theorem]of cases) {
    try {
      await put(file,view);
      const result=await verify({dir:proof,roots:[file],fstar,models,modelCache});
      await fs.writeFile(path.join(output,name+'.proof.log'),result.log);
      assert(hasOrdinaryTheoremRejection({status:result.status,log:result.log,theorem,view}),
        'require ordinary writer-contract dependency rejection: '+result.log);
      console.log('PASS '+name+': actual caller requires the writer-code contract');
    }finally{await put(identityFile,identity);await put(acceptedFile,accepted);}
  }
}
