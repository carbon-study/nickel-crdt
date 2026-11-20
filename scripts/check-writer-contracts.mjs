// The shared writer-code contract must serve both actual native callers.
import assert from 'node:assert/strict';
import {viewUnits} from './text-family-run.mjs';
export function writerUnits(read) {
  const identityFile='Nickel.EditIdentity.fst';
  const acceptedFile='Nickel.EditAccepted.fst';
  const identity=read(identityFile);
  const accepted=read(acceptedFile);
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
  return viewUnits('writer',cases.map(([name,file,view,theorem])=>({name,files:{[file]:view},roots:[file],theorem,inPlace:true,
    log:name+'.proof.log',pass:name+': actual caller requires the writer-code contract',failure:'require ordinary writer-contract dependency rejection'})),read);
}
