// Dependency controls for the named equality contract, not native bug witnesses.
import assert from 'node:assert/strict';
import {viewUnits} from './text-family-run.mjs';
export function identityUnits(read) {
  const file='Nickel.EditIdentity.fst';
  const original=read(file);
  const pattern=' [SMTPat (Native.fact_equal a b)]';
  assert.equal(original.split(pattern).length,2);
  const needle='Tactics.prune "Nickel_crdt.Edit.fact_equal";';
  // Migration: the actual fact_equal callback is consumed inside the concrete
  // shared lookup bridge, before duplicate_matches_lookup consumes its result.
  // Scope this removal there; the later duplicate assertion still hides the
  // same native body but no longer needs the equality contract independently.
  const bridgeStart=original.indexOf('let rec shared_lookup_agrees ');
  const bridgeEnd=original.indexOf('\nlet ',bridgeStart+4);
  assert(bridgeStart>=0 && bridgeEnd>bridgeStart,'shared lookup declaration');
  const bridge=original.slice(bridgeStart,bridgeEnd);
  assert.equal(bridge.split(needle).length,2,'one actual equality callback boundary');
  const withoutEqualityContract=original.slice(0,bridgeStart)+bridge.replace(needle,
    needle+'\n        Tactics.prune "Nickel.EditIdentity.fact_equality_exact";')+original.slice(bridgeEnd);
  const invalidPattern=' [SMTPat (Native.invalid reason)]';
  const invalidNeedle='Tactics.prune "Nickel_crdt.Edit.invalid";';
  assert.equal(original.split(invalidPattern).length,2);
  assert.equal(original.split(invalidNeedle).length,2);
  const cases=[
    ['identity-without-invalid-pattern',original.replace(invalidPattern,''),'duplicate_matches_lookup'],
    ['identity-without-invalid-contract',original.replace(invalidNeedle,invalidNeedle+'\n    Tactics.prune "Nickel.EditIdentity.invalid_is_exact";'),'duplicate_matches_lookup'],
    ['identity-without-equality-pattern',original.replace(pattern,''),'shared_lookup_agrees'],
    ['identity-without-equality-contract',withoutEqualityContract,'shared_lookup_agrees'],
  ];
  return viewUnits('identity',cases.map(([name,view,owner])=>({name,files:{[file]:view},roots:[file],theorem:'Nickel.EditIdentity.'+owner,inPlace:true,
    log:name+'.proof.log',pass:name+': actual '+owner+' boundary requires its selected callee contract',failure:'require ordinary identity-callee contract dependency rejection'})),read);
}
