import assert from 'node:assert/strict';
import {fileURLToPath} from 'node:url';
import {hasOrdinaryTheoremRejection as accepts} from './negative-proof-evidence.mjs';
export function checkNegativeProofEvidence() {
  const view='module Nickel.Test\nlet target () : Lemma True =\n  ()\nlet other () : Lemma False =\n  ()\n';
  const query=(name='target',status='failed',used=5,reason='unknown because (incomplete quantifiers)',line=3)=>
    `(Nickel.Test.fst(${line},2-${line},4)) Query-stats (Nickel.Test.${name}, 1) ${status} {reason-unknown=${reason}} in 5 milliseconds with fuel 1 and ifuel 1 and rlimit 100 (used rlimit ${used})`;
  const error=(line=3,code=19,message='Could not prove post-condition')=>`* Error ${code} at Nickel.Test.fst(${line},2-${line},4):\n  - ${message}\n\n`;
  const check=log=>accepts({status:2,log,theorem:'Nickel.Test.target',view});
  assert(check(query()+'\n'+error()));
  assert(check(query()+'\n'+error(3,228,"Tactic failed\n  - 't_smt_sync' failed\n  - SMT did not solve this goal")));
  // The former any-failed-line + any-error policy accepts this stream, even
  // though target recovered after splitting and only other has a final error.
  const recovered=query()+'\n'+query('target','succeeded')+'\n'+error(5);
  assert(recovered.split('\n').some(line=>line.includes('Query-stats (Nickel.Test.target,')&&line.includes('failed')));
  assert.match(recovered,/Could not prove post-condition/);
  assert(!check(recovered));
  assert(!check(query()+'\n'+error(5)));
  assert(!check(query()+'\n'+error().replace('(3,2-3,4)','(3,20-3,24)')));
  assert(!check(query()+'\n* Warning 252 at Nickel.Test.fst(3,2-3,4):\n  - Assertion failed\n'));
  assert(!check(query()+'\n'+error(3,12,'Expected type Prims.bool')));
  assert(!check(query()+'\n'+error(3,228,'Tactic failed\n  - unrelated tactic exception')));
  assert(!check(query('other','failed',5,'unknown',5)+'\n'+error(5)));
  assert(!check(query('target','failed',100)+'\n'+error()));
  assert(!check(query('target','failed',2,'timeout')+'\n'+error()));
  assert(!check(query()+'\n'+query('target','failed',100,'resource limits reached')+'\n'+error()));
  assert(!check(query()+'\n'+query('target','succeeded')+'\n'+error()));
  assert(!accepts({status:124,log:query()+'\n'+error(),theorem:'Nickel.Test.target',view}));
  assert(!accepts({status:2,log:query()+'\n'+error(),theorem:'Nickel.Test.missing',view}));
  console.log('PASS negative proof evidence: final named query, source-bound semantic error, resource/type/warning/recovered-split controls');
}
if(process.argv[1]===fileURLToPath(import.meta.url))checkNegativeProofEvidence();
