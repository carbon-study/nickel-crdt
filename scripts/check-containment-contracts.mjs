// Containment composes the whole-fact absence law; its boundary uses checked
// vector/slice equations with the native/model implementation facts withheld.
import assert from 'node:assert/strict';
import {viewUnits} from './text-family-run.mjs';
export function containmentUnits(read) {
  const file='Nickel.EditWellFormed.fst',original=read(file);
  const units=[];
  for(const[name,needle,theorem]of[
    ['containment-without-index','Nickel.Vector.slice_index facts (mk_usize i);','absence_on_whole_facts'],
    ['containment-without-length','Nickel.Vector.slice_length facts;','absence_on_whole_facts'],
    ['containment-without-absence','absence_on_whole_facts next id;','presence_survives_containment'],
  ]) {
    assert.equal(original.split(needle).length,2);
    const view=original.replace(needle,'();');
    units.push({name,files:{[file]:view},roots:[file],theorem:'Nickel.EditWellFormed.'+theorem,inPlace:true,
      log:name+'.proof.log',pass:name+': caller needs its checked contract',failure:'require ordinary containment dependency rejection'});
  }
  return viewUnits('containment',units,read);
}
