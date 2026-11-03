import assert from 'node:assert/strict';
import {author,eventId,render as oldRender,ids as oldIds} from './order.mjs';
import {fugueInterpret as interpret,fugueIds as ids,fugueRender as render,ROOT,causalSchedules} from './fugue.mjs';
import {maxOracleFamily} from './fugue-max-oracle.mjs';
import {hiddenInsideRuns} from './fugue-hidden-runs.mjs';
const receipt={witnesses:{},runFamily:{histories:0,causalSchedules:0,authorGapChecks:0},controls:{}};
function wholeGap(history,e) {
  const basis=history.filter(x=>e.basis.includes(eventId(x))),before=interpret(basis);
  const visible=new Set(e.visible),view=before.filter(n=>visible.has(n.id));
  const left=e.gap?view[e.gap-1].id:ROOT,after=interpret([...basis,e]);
  const at=left===ROOT?-1:after.findIndex(n=>n.id===left);
  assert.deepEqual(after.slice(at+1,at+1+[...e.text].length).map(n=>n.id),[...e.text].map((_,i)=>`${eventId(e)}/${i}`),'whole-order author gap');
}
function contiguousRuns(history,runs,order=ids(history)) {
  for(const run of runs) {
    const positions=run.map(id=>order.indexOf(id));assert(positions.every(i=>i>=0));
    assert.equal(Math.max(...positions)-Math.min(...positions)+1,positions.length,'multi-event run interleaved');
  }
}
const root=author([],0,1,'ab',[],0),base=ids([root]);
const one=author([root],1,1,'1',base,1),two=author([root,one],1,2,'2',ids([root,one]),1);
const three=author([root],2,1,'3',base,1),four=author([root,three],2,2,'4',ids([root,three]),1);
const prepends=[root,one,two,three,four];
assert.equal(oldRender(prepends),'a2413b');assert.equal(render(prepends),'a2143b');
receipt.witnesses.prepend={old:'a2413b',candidate:'a2143b'};
assert.throws(()=>contiguousRuns(prepends,[['1:2/0','1:1/0'],['2:2/0','2:1/0']],oldIds(prepends)),/multi-event run interleaved/);
receipt.controls.oldAllocation='run oracle rejects retained a2413b baseline';
const x=author([root],1,1,'X',[base[1]],0);
assert.equal(render([root,x]),'Xab');receipt.witnesses.hiddenReturn='Xab';
assert.notEqual(render([root,x],null,{visibleRight:true}),'Xab');receipt.controls.visibleRight='caught by hidden return';
// The paper's Figure 7 distinguishes plain Fugue from FugueMax.
const A=author([],0,1,'A',[],0),B=author([],1,1,'B',[],0),C=author([],2,1,'C',[],0);
const X=author([A,C],2,2,'X',ids([A,C]),1),Y=author([A,B],1,2,'Y',ids([A,B]),1),fig7=[A,B,C,X,Y];
assert.equal(render(fig7),'AXYBC');assert.equal(render(fig7,null,{plain:true}),'AYXBC');
let fig7Schedules=0;for(const schedule of causalSchedules(fig7)){assert.equal(render(schedule),'AXYBC');fig7Schedules++;}
receipt.witnesses.figure7={max:'AXYBC',plain:'AYXBC',causalSchedules:fig7Schedules};
receipt.controls.plainComparator='caught by Figure 7';
assert.notEqual(render([root,one,three],null,{receiverBasis:true}),render([root,three,one],null,{receiverBasis:true}));
receipt.controls.receiverBasis='caught by arrival-order disagreement';
// Common-gap independent runs, each using separate events. No writer sees a
// peer's run. Explicit later insertion into a run is deliberately outside this
// contiguity property. Full births remain even in the hidden-middle profile.
for(const writers of [2,3])for(const swap of [false,true])
for(const profile of ['gap0','gap1','gap2','hidden-middle'])for(let modes=0;modes<2**writers;modes++) {
  const hidden=profile==='hidden-middle',r=author([],0,1,hidden?'abcd':'ab',[],0),allBase=ids([r]);
  const visibleBase=hidden?[allBase[0],allBase[3]]:allBase,gap=hidden?1:Number(profile.at(-1));
  const history=[r],runs=[];
  for(let w=0;w<writers;w++) {
    const site=swap?writers-w:w+1,prepend=Boolean(modes&(1<<w));let own=[r],run=[];
    const length=writers===2?3:2;
    for(let n=1;n<=length;n++) {
      const total=interpret(own),visible=total.filter(o=>visibleBase.includes(o.id)||run.includes(o.id)).map(o=>o.id);
      const at=n===1?gap:prepend?visible.indexOf(run[0]):visible.indexOf(run.at(-1))+1;
      const e=author(own,site,n,String.fromCharCode(65+w*3+n-1),visible,at),id=`${eventId(e)}/0`;
      own.push(e);history.push(e);if(prepend)run.unshift(id);else run.push(id);
    }
    runs.push(run);
  }
  const canonical=interpret(history);contiguousRuns(history,runs);
  for(const run of runs)assert.deepEqual(canonical.filter(n=>run.includes(n.id)).map(n=>n.id),run,'local run order');
  for(const e of history){wholeGap(history,e);receipt.runFamily.authorGapChecks++;}
  for(const schedule of causalSchedules(history)) {
    assert.deepEqual(interpret(schedule),canonical,'causal delivery agreement');receipt.runFamily.causalSchedules++;
  }
  assert.deepEqual(interpret([...history,history[1]]),canonical,'exact retry');
  assert.deepEqual(interpret(JSON.parse(JSON.stringify(history)).reverse()),canonical,'cold input reconstruction');
  receipt.runFamily.histories++;
}
// Real scalar preservation and an intentional later edit inside an earlier run.
const pq=author([root],1,1,'P🦊é',base,1),z=author([root,pq],2,1,'Z',ids([root,pq]),2);
assert.equal(render([root,pq,z]),'aPZ🦊éb');receipt.witnesses.explicitInteriorEdit='aPZ🦊éb';
for(const bad of [
  {...one,gap:99},{...one,visible:['missing']},{...one,text:'\ud800'},
  {...one,basis:['missing']},{...one,basis:['0:1','0:1']},
])assert.throws(()=>interpret([root,bad]));
assert.throws(()=>interpret([root,one,{...one,text:'different'}]),/conflicting duplicate/);
assert.throws(()=>interpret([root,one,{...two,basis:['1:1']}]),/downward closed/);
assert.throws(()=>interpret([{...one,basis:['1:1']}]),/missing dependency or cycle/);
receipt.controls.inputRejections=8;
receipt.maxOracle=maxOracleFamily();
receipt.hiddenInsideRuns=hiddenInsideRuns();
console.log(JSON.stringify(receipt,null,2));
