// Actual basis selection composes checked loops, whole-fact cloning and exact past.
import assert from 'node:assert/strict';
import {viewUnits} from './text-family-run.mjs';
export function basisUnits(read) {
  const name='Nickel.EditBasis.fst', original=read(name);
  const controls=[
    ['basis-filter-without-loop',/  Nickel\.LoopUtil\.result_preserve_any [^\n]+;\n/,'actual_basis_is_exact_filter','actual_basis_is_exact_filter'],
    ['basis-filter-without-clone',/    selected_fact_is_exact fact;\n/,'actual_basis_is_exact_filter','actual_basis_is_exact_filter'],
    ['basis-event-without-past',/  scanned_roots_compute_exact_past facts roots;\n/,'closed_event_basis_is_exact','closed_event_basis_is_exact'],
    ['basis-event-without-filter',/actual_basis_is_exact_filter input \(Alloc\.Vec\.impl_1__as_slice selected\)/,'closed_event_basis_is_exact','closed_event_basis_is_exact','()'],
  ];
  const units=[];
  for(const [control,pattern,owner,scope,replacement=''] of controls) {
    let start=0,end=original.length;
    if(scope) {
      const declaration=new RegExp('^let (?:rec )?'+scope+' ','m').exec(original);assert(declaration,control+' declaration');
      start=declaration.index;
      const next=/\nlet (?:rec )?\w+ /.exec(original.slice(start+declaration[0].length));
      end=next?start+declaration[0].length+next.index:original.length;
    }
    const body=original.slice(start,end);
    assert.equal([...body.matchAll(new RegExp(pattern.source,'g'))].length,1,control+' anchor');
    const view=original.slice(0,start)+body.replace(pattern,replacement)+original.slice(end);
    units.push({name:control,files:{[name]:view},roots:[name],theorem:'Nickel.EditBasis.'+owner,inPlace:false,
      log:control+'.proof.log',pass:control+': ordinary owning rejection',failure:control});
  }
  return viewUnits('basis',units,read);
}
