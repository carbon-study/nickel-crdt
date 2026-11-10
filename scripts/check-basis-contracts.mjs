// Actual basis selection composes checked loops, whole-fact cloning and exact past.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import {put,verify} from './proof-cache.mjs';
import {hasOrdinaryTheoremRejection} from './negative-proof-evidence.mjs';
export async function checkBasisContracts({proof,output,fstar,models,modelCache}) {
  const name='Nickel.EditBasis.fst', original=await fs.readFile(path.join(proof,name),'utf8');
  const controls=[
    ['basis-filter-without-loop',/  Nickel\.LoopUtil\.result_preserve_any [^\n]+;\n/,'actual_basis_is_exact_filter','actual_basis_is_exact_filter'],
    ['basis-filter-without-clone',/    selected_fact_is_exact fact;\n/,'actual_basis_is_exact_filter','actual_basis_is_exact_filter'],
    ['basis-event-without-past',/  scanned_roots_compute_exact_past facts roots;\n/,'closed_event_basis_is_exact','closed_event_basis_is_exact'],
    ['basis-event-without-filter',/actual_basis_is_exact_filter input \(Alloc\.Vec\.impl_1__as_slice selected\)/,'closed_event_basis_is_exact','closed_event_basis_is_exact','()'],
  ];
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
    const dir=path.join(path.dirname(proof),control);await fs.rm(dir,{recursive:true,force:true});
    await fs.cp(proof,dir,{recursive:true,preserveTimestamps:true});
    const view=original.slice(0,start)+body.replace(pattern,replacement)+original.slice(end);await put(path.join(dir,name),view);
    const r=await verify({dir,roots:[path.join(dir,name)],fstar,models,modelCache});
    await fs.writeFile(path.join(output,control+'.proof.log'),r.log);
    assert(hasOrdinaryTheoremRejection({status:r.status,log:r.log,theorem:'Nickel.EditBasis.'+owner,view}),control+': '+r.log);
    console.log('PASS '+control+': ordinary owning rejection');
  }
}
