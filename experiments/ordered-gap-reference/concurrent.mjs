import assert from 'node:assert/strict';
import {author,ids,keys,interpret,eventId} from './order.mjs';
import {treeInterpret,expandTree} from './tree.mjs';
import {wholeGap,eventCohesion} from './properties.mjs';
function* permutations(xs){if(!xs.length){yield [];return;}for(let i=0;i<xs.length;i++)for(const tail of permutations(xs.filter((_,j)=>i!==j)))yield[xs[i],...tail];}
function legal(xs){const seen=new Set();for(const e of xs){if(!e.basis.every(id=>seen.has(id)))return false;seen.add(eventId(e));}return true;}
export function concurrentFamily() {
  const receipt={histories:0,legalSchedules:0,authorGapChecks:0,modes:['append','prepend','hide-own-first-run','see-peer-first-run']};
  for(let leftGap=0;leftGap<=2;leftGap++)for(let rightGap=0;rightGap<=2;rightGap++)
  for(const leftMode of receipt.modes)for(const rightMode of receipt.modes) {
    const root=author([],0,1,'ab',[],0),base=ids([root]);
    const p=author([root],1,1,'XY',base,leftGap),q=author([root],2,1,'PQ',base,rightGap);
    function continuation(own,peer,mode,originalGap){
      const basis=mode==='see-peer-first-run'?[root,own,peer]:[root,own];
      const all=interpret(basis),ownIds=all.filter(r=>r.event===eventId(own)).map(r=>r.id);
      const visible=mode==='hide-own-first-run'?base:all.map(r=>r.id);
      const gap=mode==='hide-own-first-run'?originalGap:mode==='prepend'?visible.indexOf(ownIds[0]):visible.indexOf(ownIds.at(-1))+1;
      return author(basis,own.writer,2,own.writer===1?'u':'v',visible,gap);
    }
    const history=[root,p,q,continuation(p,q,leftMode,leftGap),continuation(q,p,rightMode,rightGap)];
    const canonical=keys(history);eventCohesion(history);
    for(const e of history){const basis=history.filter(x=>e.basis.includes(eventId(x)));wholeGap(basis,e);receipt.authorGapChecks++;}
    for(const order of permutations(history))if(legal(order)) {
      assert.deepEqual(keys(order),canonical,'concurrent family convergence');
      assert.deepEqual(expandTree(treeInterpret(order)),canonical,'concurrent family tree abstraction');
      assert.deepEqual(keys([...order,order[1]]),canonical,'concurrent family duplicate');
      const cold=JSON.parse(JSON.stringify(order));
      assert.deepEqual(expandTree(treeInterpret(cold)),canonical,'concurrent family cold tree');
      receipt.legalSchedules++;
    }
    receipt.histories++;
  }
  return receipt;
}
