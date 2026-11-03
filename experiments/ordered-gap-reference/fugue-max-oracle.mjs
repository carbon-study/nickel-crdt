// Tiny finite Definition 4 constraint oracle, independent of Fugue tree layout.
// It enumerates total orders, not alternative implementations of the comparator.
import assert from 'node:assert/strict';
import {pathToFileURL} from 'node:url';
import {author,eventId} from './order.mjs';
import {fugueInterpret,causalSchedules,ROOT} from './fugue.mjs';
const permutations=function*(xs){if(!xs.length){yield [];return;}for(let i=0;i<xs.length;i++)for(const tail of permutations(xs.filter((_,j)=>j!==i)))yield[xs[i],...tail];};
function idLess(a,b) {
  const aa=a.split(/[:/]/).map(Number),bb=b.split(/[:/]/).map(Number);
  for(let i=0;i<3;i++)if(aa[i]!==bb[i])return aa[i]<bb[i];return false;
}
function closedStates(model) {
  const states=[];
  for(let mask=0;mask<2**model.length;mask++) {
    const state=model.filter((_,i)=>mask&(2**i)),present=new Set(state.map(e=>e.id));
    if(state.every(e=>e.basis.every(id=>present.has(id))))states.push(state);
  }
  return states;
}
function constraints(model,states,order) {
  const byId=new Map(model.map(e=>[e.id,e]));
  const descendant=(child,ancestor)=>{
    while(child!==ROOT){child=byId.get(child).leftOrigin;if(child===ancestor)return true;}
    return false;
  };
  // One global order witnesses every author insertion state. All generated
  // states are deletion-free single-scalar histories with independently known
  // author sequences; this is only the finite strong-list obligation here.
  for(const e of model) {
    const set=new Set([...e.basis,e.id]);
    if(order.filter(id=>set.has(id)).join('|')!==e.authorSequence.join('|'))return false;
  }
  for(const state of states) {
    const present=new Set(state.map(e=>e.id)),list=order.filter(id=>present.has(id));
    const pos=new Map(list.map((id,i)=>[id,i]));pos.set(ROOT,-1);
    for(const B of state) {
      // Definition 4(1): first element having an actual element as left origin.
      // start/end are sentinels, not extra list elements in clauses (1)/(2).
      const A=B.leftOrigin;
      if(A!==ROOT&&!state.some(C=>C.leftOrigin===A&&pos.get(C.id)<pos.get(B.id)))
        if(pos.get(B.id)!==pos.get(A)+1)return false;
    }
    for(const A of state) {
      const B=A.rightOrigin;
      if(B===null||state.some(C=>C.rightOrigin===B&&pos.get(C.id)>pos.get(A.id)))continue;
      // Definition 4(2), with exactly the exception stated in Lemma 5.
      const exception=A.leftOrigin!==byId.get(B).leftOrigin&&state.some(C=>
        pos.get(A.leftOrigin)<pos.get(C.id)&&pos.get(C.id)<pos.get(B)&&!descendant(C.id,A.leftOrigin));
      if(!exception&&pos.get(B)!==pos.get(A.id)+1)return false;
    }
    for(const A of state)for(const B of state)
      if(A.leftOrigin===B.leftOrigin&&A.rightOrigin===B.rightOrigin&&idLess(A.id,B.id))
        if(pos.get(A.id)>=pos.get(B.id))return false;
  }
  return true;
}
export function maxOracleFamily() {
  const receipt={histories:0,totalOrders:0,causalStates:0,causalSchedules:0,plainDisagreements:0,
    limits:'2 or 3 concurrent roots; two independent singleton insertions observing all but one root; all gaps; exchanged insert IDs'};
  for(const n of [2,3])for(const swap of [false,true]) {
    const roots=Array.from({length:n},(_,writer)=>author([],writer,1,String.fromCharCode(65+writer),[],0));
    const rootIds=roots.map(e=>`${eventId(e)}/0`);
    const choices=[];
    for(let omitted=0;omitted<n;omitted++)for(let gap=0;gap<n;gap++)choices.push({omitted,gap});
    for(const x of choices)for(const y of choices) {
      const model=roots.map((e,i)=>({id:rootIds[i],leftOrigin:ROOT,rightOrigin:null,basis:[],authorSequence:[rootIds[i]]}));
      const events=[...roots];
      for(const [j,choice]of [x,y].entries()) {
        const known=roots.filter((_,i)=>i!==choice.omitted),visible=rootIds.filter((_,i)=>i!==choice.omitted);
        const e=author(known,swap?n+1-j:n+j,1,j?'Y':'X',visible,choice.gap),id=`${eventId(e)}/0`;
        const sequence=[...visible];sequence.splice(choice.gap,0,id);
        model.push({id,leftOrigin:choice.gap?visible[choice.gap-1]:ROOT,rightOrigin:visible[choice.gap]??null,
          basis:[...visible],authorSequence:sequence});events.push(e);
      }
      const states=closedStates(model),allowed=[];
      for(const order of permutations(model.map(e=>e.id))) {
        receipt.totalOrders++;if(constraints(model,states,order))allowed.push(order);
      }
      assert.equal(allowed.length,1,'finite specification must determine one order');
      const expected=allowed[0];
      for(const schedule of causalSchedules(events)) {
        const actual=fugueInterpret(schedule);assert.deepEqual(actual.map(e=>e.id),expected,'generated Definition 4 order');
        for(const row of actual) {
          const authored=model.find(e=>e.id===row.id);
          assert.equal(row.leftOrigin,authored.leftOrigin,'independent left-origin derivation');
          assert.equal(row.rightOrigin,authored.rightOrigin,'independent right-origin derivation');
        }
        receipt.causalSchedules++;
      }
      if(fugueInterpret(events,{plain:true}).map(e=>e.id).join('|')!==expected.join('|'))receipt.plainDisagreements++;
      receipt.histories++;receipt.causalStates+=states.length;
    }
  }
  assert(receipt.plainDisagreements>0,'generated family must distinguish Max from plain');
  return receipt;
}
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)console.log(JSON.stringify(maxOracleFamily(),null,2));
