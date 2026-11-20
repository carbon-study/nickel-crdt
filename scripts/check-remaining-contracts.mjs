// Source-family call-removal controls for the remaining reform. Each case
// edits one declaration and requires its own ordinary semantic rejection.
import assert from 'node:assert/strict';
import {declarationCode,fstarDeclaration,replaceUniqueInFstarDeclaration} from './fstar-mutation-scope.mjs';
import {viewUnits} from './text-family-run.mjs';
const cases=[];
function calls(module,owner,callees) {
  for(const callee of callees)cases.push({module,owner,callee});
}
for(const owner of ['plain_interpret_any','preserve_any','plain_preserve_any','result_preserve_any','option_interpret_any','break_interpret_any','early_return_preserve_any'])
  calls('LoopUtil',owner,['FStar.Classical.forall_intro_3']);
calls('LoopUtil','early_return_preserve_any',['preserve_any']);
calls('LoopUtil','option_interpret_any',['option_interpret']);
calls('LoopUtil','option_interpret',['unroll','option_run_step','empty','option_interpret']);
calls('LoopUtil','break_interpret_any',['break_interpret']);
calls('LoopUtil','break_interpret',['break_step','break_end','option_run_step','break_interpret']);
calls('EditIdentity','scan_lookup',['Nickel.LoopUtil.option_run_step','Nickel.LoopUtil.option_run_end','scan_lookup']);
// Migration: duplicate_matches_lookup's old option-interpreter/scan_lookup
// dependence moved to EventClassifier.classification_is_exact. Keep both
// generic obligations, then separately test the concrete callback/lookup bridge.
calls('EventClassifier','classification_is_exact',['Nickel.LoopUtil.option_interpret_any','scan_matches_lookup']);
calls('EditIdentity','duplicate_matches_lookup',['Nickel.EventClassifier.classification_is_exact','shared_lookup_agrees']);
// Bundling does not expose constructor/constant bodies at client consumption.
// These patternless contracts must be called; each removal has an exact owner.
calls('EventGraphText','text_graph_callbacks_are_exact',['Nickel.EventGraph.graph_ops_preserve_callbacks']);
calls('EventGraphText','text_graph_policy_is_exact',['text_policy_is_exact','Nickel.EventGraph.event_ops_preserve_callbacks']);
calls('EditIdentity','duplicate_matches_lookup',['Nickel.EventGraphText.text_graph_policy_is_exact','Nickel.EventGraphText.text_graph_callbacks_are_exact']);
calls('EditAccepted','selected_id_is_unseen',['Nickel.EventGraphText.text_graph_policy_is_exact','Nickel.EventGraphText.text_graph_callbacks_are_exact']);
calls('EditPast','event_membership_is_exact',['Nickel.EventGraphText.text_graph_policy_is_exact','Nickel.EventGraphText.text_graph_callbacks_are_exact']);
calls('EditSchedule','readiness_is_exact',['Nickel.EventGraphText.text_graph_policy_is_exact','Nickel.EventGraphText.text_graph_callbacks_are_exact']);
calls('EditAtomic','authored_edit_advances_once',['result_has_constructor']);
calls('EditAtomic','new_has_empty_facts',['Nickel.Vector.empty_vector_contents']);
for(const owner of ['new_establishes_scalar_validity','new_establishes_causal_closure'])
  calls('EditWellFormed',owner,['Nickel.EditAtomic.new_has_empty_facts']);
// Migration: the old unit-state pre-scalar loop moved into validate_event's
// Result<Vec<EventId>, Error> phase. Its redundant unit proof call was retired;
// The remaining usize birth-count loop was then deleted with policy ceilings.
// Its early-return rule is no longer consumed here; retain scalar-contract
// dependence and the actual wrong-body/wrong-argument scalar controls.
calls('EditWellFormed','successful_validation_has_valid_scalars',['scalar_validation_is_sound']);
for(const owner of ['dependency_validation_is_sound','present_dependencies_pass_guard'])
  calls('EditWellFormed',owner,['Nickel.LoopUtil.result_preserve_any']);
calls('EditWellFormed','membership_result_is_exact',['event_membership_is_presence']);
calls('EditWellFormed','successful_past_has_direct_dependencies',['dependency_validation_is_sound']);
calls('EditWellFormed','successful_validation_has_direct_dependencies',['successful_past_has_direct_dependencies']);
for(const owner of ['receive_added_fact_has_valid_scalars','receive_added_has_direct_dependencies'])
  calls('EditWellFormed',owner,['Nickel.EditAtomic.successful_plan_requires_validation','Nickel.EditCommit.receive_uses_plan']);
calls('EditWellFormed','receive_preserves_scalar_validity',['Nickel.EditAtomic.receive_rejection_unchanged','receive_added_has_exact_contents','receive_added_fact_has_valid_scalars']);
calls('EditWellFormed','edit_preserves_scalar_validity',['Nickel.EditAtomic.edit_rejection_or_empty_unchanged','edit_authored_has_exact_contents','edit_authors_only_valid_scalars']);
calls('EditCausal','present_fact_has_id',['absence_on_whole_facts']);
calls('EditCausal','new_establishes_causal_rank',['Nickel.EditAtomic.new_has_empty_facts']);
calls('EditCausal','receive_preserves_causal_rank',['Nickel.EditAtomic.receive_rejection_unchanged','receive_added_has_exact_contents','Nickel.EditIdentity.receive_added_has_fresh_event_id','receive_added_has_direct_dependencies','exact_extension_extends_rank']);
calls('EditCausal','edit_preserves_causal_rank',['Nickel.EditAtomic.edit_rejection_or_empty_unchanged','edit_authored_has_exact_contents','Nickel.EditIdentity.authored_event_id_is_fresh','Nickel.EditCommit.authored_fact_replays_same_commit','receive_added_has_direct_dependencies','exact_extension_extends_rank']);
// One case per call of callee in owner's declaration, in source order (the
// index is the occurrence among the calls found). Calls are found in code
// only: F* comments (line and nested block) and strings are blanked first, so
// their text never becomes a case or hides the inline fallback. A found call
// whose text shares its line with a comment or string is refused rather than
// edited or dropped. Declaration discovery is fstarDeclaration's, unchanged.
export function remainingCallSites(source,module,owner,callee) {
  const {start:a,end:b}=fstarDeclaration(source,owner);
  const body=source.slice(a,b),code=declarationCode(source).slice(a,b),escaped=callee.replace(/[.*+?^${}()|[\]\\]/g,'\\$&');
  // Only complete statement calls; a recursive call in the conclusion is
  // never an anchor. A separate case is made for every repeated call.
  const re=new RegExp('^([ \\t]+(?:begin )?)'+escaped+' [^\\n]+;?$', 'gm');
  let anchors=[...code.matchAll(re)].filter(m=>! /\bend\b|\bin\b/.test(m[0]));
  const inline=anchors.length===0;
  if(inline)anchors=[...code.matchAll(new RegExp(escaped+' [^\\n;]+?(?=;| end(?: |;|$))','g'))];
  assert(anchors.length,'no statement call '+module+'.'+owner+' -> '+callee);
  return anchors.map((m,i)=>{
    const name=[module,owner,callee,i].join('-').replaceAll('.','_');
    assert.equal(body.slice(m.index,m.index+m[0].length),m[0],name+': unsupported call syntax: a comment or string shares the call\'s text');
    return {name,index:m.index,length:m[0].length,replacement:inline?'()':m[1]+(m[0].trimEnd().endsWith(';')?'();':'()')};
  });
}

export function remainingUnits(read) {
  const originals=new Map(),units=[];
  for(const {module}of cases)if(!originals.has(module))originals.set(module,read('Nickel.'+module+'.fst'));
  for(const c of cases) {
    const {module,owner,callee}=c,original=originals.get(module),{start:a,end:b}=fstarDeclaration(original,owner);
    const body=original.slice(a,b);
    for(const {name,index,length,replacement} of remainingCallSites(original,module,owner,callee)){
      let changed=body.slice(0,index)+replacement+body.slice(index+length);
      if(module==='EditIdentity' && owner==='duplicate_matches_lookup' && callee==='Nickel.EventClassifier.classification_is_exact') {
        // This callee also has a global pattern; remove the automatic route
        // at the same concrete assertion, with classify/fold bodies hidden.
        const anchor='    Tactics.prune "Nickel_crdt.Event_layer.classify";';
        assert.equal(changed.split(anchor).length,2,'classification callee-prune anchor');
        changed=changed.replace(anchor,anchor+'\n    Tactics.prune "Nickel.EventClassifier.classification_is_exact";');
      }
      const view=original.slice(0,a)+changed+original.slice(b),file='Nickel.'+module+'.fst';
      units.push({name,files:{[file]:view},roots:[file],theorem:'Nickel.'+module+'.'+owner,inPlace:true,
        log:name+'.proof.log',pass:name,failure:name+': require ordinary named rejection (see retained log)'});
    }
  }

  // This lemma has a real SMT pattern: withhold its global facts at each
  // dependency-loop caller, independently of the other caller.
  for(const [module,owner] of [['EditWellFormed','dependency_validation_is_sound'],['EditWellFormed','present_dependencies_pass_guard'],['EditCausal','present_id_rank_bound']]){
    const original=originals.get(module),needle='Tactics.prune "Nickel_crdt.Edit.has_fact";';
    const view=replaceUniqueInFstarDeclaration(original,owner,needle,needle+'\n    Tactics.prune "Nickel.EditWellFormed.membership_result_is_exact";');
    const file='Nickel.'+module+'.fst';
    units.push({name:owner,files:{[file]:view},roots:[file],theorem:'Nickel.'+module+'.'+owner,inPlace:true,
      log:owner+'-without-membership.proof.log',pass:owner+': constructor-complete membership contract required',failure:'ordinary membership contract dependency required'});
  }
  const causal=originals.get('EditCausal');
  for(const [name,from,to,owner]of[
    ['causal-zero-new-rank','    begin bound end','    begin 0 end','exact_extension_extends_rank'],
    ['causal-erased-edges',/let causal_edge ([\s\S]*?): Type0 =\n  [^\n]+/,'let causal_edge $1: Type0 =\n  Prims.l_False','actual_reference_is_edge']
  ]){
    const view=causal.replace(from,to);assert.notEqual(view,causal);
    const file='Nickel.EditCausal.fst';
    units.push({name,files:{[file]:view},roots:[file],theorem:'Nickel.EditCausal.'+owner,inPlace:true,
      log:name+'.proof.log',pass:name+': ghost-only control, no native mutation claimed',failure:'ordinary ghost-law rejection required'});
  }
  return viewUnits('remaining',units,read);
}

// Pure locator controls (#158): calls count only in code, occurrence indexing
// follows source order, and unsupported mixed lines are refused, not dropped.
export function checkRemainingCallLocator() {
  const source=lines=>'module M\nlet owner () =\n'+lines.join('\n')+'\nlet later () = ()\n';
  const sites=lines=>{
    const s=source(lines),{start}=fstarDeclaration(s,'owner');
    return remainingCallSites(s,'M','owner','c').map(x=>({name:x.name,text:s.slice(start+x.index,start+x.index+x.length),replacement:x.replacement}));
  };
  const one=(lines,text,replacement)=>assert.deepEqual(sites(lines),[{name:'M-owner-c-0',text,replacement}]);
  // A line comment, a nested block comment and a multi-line string each
  // contain the callee's statement text; only the real call is a case.
  one(['  // c x;','  c y;'],'  c y;','  ();');
  one(['  (* outer (* inner *)','  c x;','  *)','  c y;'],'  c y;','  ();');
  one(['  let s = "','  c x;','" in','  c y;'],'  c y;','  ();');
  // Indexing counts code calls only: a commented call between two real calls
  // does not take an index.
  assert.deepEqual(sites(['  c a;','  (* c b; *)','  c d;']).map(x=>[x.name,x.text]),[['M-owner-c-0','  c a;'],['M-owner-c-1','  c d;']]);
  // A commented statement no longer hides the inline fallback, and a string
  // holding the callee's text is not an inline call.
  one(['  (*','  c x;','  *)','  begin c y end'],'c y','()');
  one(['  begin f "c z" end;','  begin c y end'],'c y','()');
  // Control: a callee present only in a comment or string produces no case.
  assert.throws(()=>sites(['  (*','  c x;','  *)','  ()']),/no statement call M\.owner -> c/);
  assert.throws(()=>sites(['  f "c x";','  ()']),/no statement call M\.owner -> c/);
  // A real call sharing its text with a comment or string is refused, never
  // silently edited or dropped.
  assert.throws(()=>sites(['  c x; (* why *)']),/M-owner-c-0: unsupported call syntax/);
  assert.throws(()=>sites(['  c "x";']),/M-owner-c-0: unsupported call syntax/);
  assert.throws(()=>sites(['  (* note *) c x;']),/M-owner-c-0: unsupported call syntax/);
}
