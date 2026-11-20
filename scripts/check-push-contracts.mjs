// Actual-Rust body mutants are separate; these remove the contract interface.
import assert from 'node:assert/strict';
import {viewUnits} from './text-family-run.mjs';
export function pushUnits(read) {
 const file='Nickel.EditAccepted.fst',original=read(file);
 const pattern=' [SMTPat (Native.push before fact)]';assert.equal(original.split(pattern).length,2);
 const cases=[['push-without-pattern','append_fresh_preserves_unique',original.replace(pattern,'')]];
 for(const name of ['append_fresh_preserves_unique','append_whole_fact','push_has_exact_contents','push_membership']) {
  const start=new RegExp('^let '+name+' ','m').exec(original)?.index;assert(start!==undefined);
  const next=/\nlet (?:rec )?\w+ /.exec(original.slice(start+4));const end=next?start+4+next.index:original.length;
  const body=original.slice(start,end),needle='Tactics.prune "Nickel_crdt.Edit.push";';assert.equal(body.split(needle).length,2);
  const replacement=needle+'\n    Tactics.prune "Nickel.EditAccepted.push_result_is_exact";';
  cases.push(['push-without-contract-'+name,name,original.slice(0,start)+body.replace(needle,replacement)+original.slice(end)]);
 }
 return viewUnits('push',cases.map(([name,lemma,view])=>({name,files:{[file]:view},roots:[file],theorem:'Nickel.EditAccepted.'+lemma,inPlace:true,
  log:name+'.proof.log',pass:name+': actual caller requires the push contract',failure:'require ordinary push-contract dependency rejection'})),read);
}
