// Proof-dependency controls, distinct from actual-Rust semantic mutants.
import assert from 'node:assert/strict';
import {viewUnits} from './text-family-run.mjs';
export function counterUnits(read) {
  const original=read('Nickel.EditAtomic.fst');
  const controls=[
    ['counter-without-setter-pattern',' [SMTPat (Native.impl_Replica__with_counter state counter)]'],
    ['counter-without-calculator-contract','  counter_result_is_exact before.f_next_counter;\n'],
  ];
  const units=[];
  for(const [name,needle] of controls) {
    assert.equal(original.split(needle).length,2,'contract-control anchor must occur exactly once');
    const view=original.replace(needle,'');
    units.push({name,files:{'Nickel.EditAtomic.fst':view},roots:['Nickel.EditAtomic.fst'],theorem:'Nickel.EditAtomic.authored_edit_advances_once',inPlace:false,
      log:name+'.proof.log',pass:name+': unchanged public theorem requires its callee contract',failure:'require ordinary public-counter rejection after removing its contract dependency'});
  }
  return viewUnits('counter',units,read);
}
