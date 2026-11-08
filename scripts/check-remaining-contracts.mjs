// Source-family call-removal controls for the remaining reform. Each case
// edits one declaration and requires its own ordinary semantic rejection.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import {put,verify} from './proof-cache.mjs';
import {hasOrdinaryTheoremRejection} from './negative-proof-evidence.mjs';
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
calls('EditIdentity','duplicate_matches_lookup',['Nickel.LoopUtil.option_interpret_any','scan_lookup']);
calls('EditAtomic','authored_edit_advances_once',['result_has_constructor']);
calls('EditAtomic','new_has_empty_facts',['Nickel.Vector.empty_vector_contents']);
for(const owner of ['new_establishes_scalar_validity','new_establishes_causal_closure'])
  calls('EditWellFormed',owner,['Nickel.EditAtomic.new_has_empty_facts']);
calls('EditWellFormed','successful_validation_has_valid_scalars',['Nickel.LoopUtil.early_return_preserve_any','scalar_validation_is_sound']);
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
function declaration(view,name) {
  const match=new RegExp('^let (?:rec )?'+name+' ','m').exec(view);assert(match,'missing '+name);
  const tail=view.slice(match.index+match[0].length),next=/\nlet (?:rec )?\w+ /.exec(tail);
  return [match.index,next?match.index+match[0].length+next.index:view.length];
}
export async function checkRemainingContracts({proof,output,fstar,models,modelCache,select=()=>true}) {
  const originals=new Map();
  for(const {module}of cases)if(!originals.has(module))originals.set(module,await fs.readFile(path.join(proof,'Nickel.'+module+'.fst'),'utf8'));
  for(const c of cases.filter(select)) {
    const {module,owner,callee}=c,original=originals.get(module),[a,b]=declaration(original,owner);
    const body=original.slice(a,b),escaped=callee.replace(/[.*+?^${}()|[\]\\]/g,'\\$&');
    // Only complete statement calls; a recursive call in the conclusion is
    // never an anchor. A separate case is made for every repeated call.
    const re=new RegExp('^([ \\t]+(?:begin )?)'+escaped+' [^\\n]+;?$', 'gm');
    let anchors=[...body.matchAll(re)].filter(m=>! /\bend\b|\bin\b/.test(m[0]));
    const inline=anchors.length===0;
    if(inline)anchors=[...body.matchAll(new RegExp(escaped+' [^\\n;]+?(?=;| end(?: |;|$))','g'))];
    assert(anchors.length,'no statement call '+module+'.'+owner+' -> '+callee);
    for(let i=0;i<anchors.length;i++){
      const m=anchors[i],name=[module,owner,callee,i].join('-').replaceAll('.','_');
      const replacement=inline?'()':m[1]+(m[0].trimEnd().endsWith(';')?'();':'()');
      const changed=body.slice(0,m.index)+replacement+body.slice(m.index+m[0].length);
      const view=original.slice(0,a)+changed+original.slice(b),file=path.join(proof,'Nickel.'+module+'.fst');
      try {
        await put(file,view);
        const r=await verify({dir:proof,roots:[file],fstar,models,modelCache});
        await fs.writeFile(path.join(output,name+'.proof.log'),r.log);
        assert(hasOrdinaryTheoremRejection({status:r.status,log:r.log,theorem:'Nickel.'+module+'.'+owner,view}),
          name+': require ordinary named rejection (see retained log)');
        console.log('PASS '+name);
      }finally{await put(file,original);}
    }
  }

  // This lemma has a real SMT pattern: withhold its global facts at each
  // dependency-loop caller, independently of the other caller.
  for(const [module,owner] of [['EditWellFormed','dependency_validation_is_sound'],['EditWellFormed','present_dependencies_pass_guard'],['EditCausal','present_id_rank_bound']]){
    const original=originals.get(module),[a,b]=declaration(original,owner);
    const body=original.slice(a,b),needle='Tactics.prune "Nickel_crdt.Edit.has_fact";';
    assert.equal(body.split(needle).length,2);
    const view=original.slice(0,a)+body.replace(needle,needle+'\n    Tactics.prune "Nickel.EditWellFormed.membership_result_is_exact";')+original.slice(b);
    const file=path.join(proof,'Nickel.'+module+'.fst');
    try{await put(file,view);const r=await verify({dir:proof,roots:[file],fstar,models,modelCache});
      await fs.writeFile(path.join(output,owner+'-without-membership.proof.log'),r.log);
      assert(hasOrdinaryTheoremRejection({status:r.status,log:r.log,theorem:'Nickel.'+module+'.'+owner,view}),'ordinary membership contract dependency required');
      console.log('PASS '+owner+': constructor-complete membership contract required');
    }finally{await put(file,original);}
  }
  const causal=originals.get('EditCausal');
  for(const [name,from,to,owner]of[
    ['causal-zero-new-rank','    begin bound end','    begin 0 end','exact_extension_extends_rank'],
    ['causal-erased-edges',/let causal_edge ([\s\S]*?): Type0 =\n  [^\n]+/,'let causal_edge $1: Type0 =\n  Prims.l_False','actual_reference_is_edge']
  ]){
    const view=causal.replace(from,to);assert.notEqual(view,causal);
    const file=path.join(proof,'Nickel.EditCausal.fst');
    try{await put(file,view);const r=await verify({dir:proof,roots:[file],fstar,models,modelCache});
      await fs.writeFile(path.join(output,name+'.proof.log'),r.log);
      assert(hasOrdinaryTheoremRejection({status:r.status,log:r.log,theorem:'Nickel.EditCausal.'+owner,view}),'ordinary ghost-law rejection required');
      console.log('PASS '+name+': ghost-only control, no native mutation claimed');
    }finally{await put(file,causal);}
  }
}
