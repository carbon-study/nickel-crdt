// Actual text callers must require the generic algorithm contract with that
// algorithm's body withheld. These are dependency controls, not Rust mutants.
import assert from 'node:assert/strict';
import {viewUnits} from './text-family-run.mjs';
export function eventUnits(read) {
  const units=[];
  const cases=[
    ['duplicate','EditAtomic','plan_preserves_duplicate_result','Nickel.EventShell.planning_is_exact'],
    ['validation','EditAtomic','successful_plan_requires_validation','Nickel.EventShell.planning_is_exact'],
    ['neutral','EditAtomic','receive_rejection_unchanged','Nickel.EventShell.publication_is_exact'],
    ['receive','EditCommit','receive_uses_plan','Nickel.EventShell.publication_is_exact'],
    ['private','EditCommit','plan_preserves_private_state','Nickel.EventShell.planning_is_exact'],
    ['shared','EditCommit','plan_ignores_private_state','Nickel.EventShell.planning_is_exact'],
    ['classifier','EditIdentity','duplicate_matches_lookup','Nickel.EventClassifier.classification_is_exact'],
  ];
  for(const [label,module,owner,contract] of cases) {
    const name='event-without-'+label,file='Nickel.'+module+'.fst';
    const original=read(file);
    const declaration=new RegExp('^let '+owner+' ','m').exec(original);assert(declaration,name+' owner declaration');
    const start=declaration.index,next=/\nlet (?:rec )?\w+ /.exec(original.slice(start+declaration[0].length));
    const end=next?start+declaration[0].length+next.index:original.length;
    let body=original.slice(start,end);
    const needle="    Tactics.smt_sync' 1 1";assert.equal(body.split(needle).length,2,name+' unique owning query');
    body=body.replace(needle,'    Tactics.prune "'+contract+'";\n'+needle);
    if(label==='classifier') {
      const use='  Nickel.EventClassifier.classification_is_exact facts fact (Nickel.EventGraphText.text_graph_ops ());\n';
      assert.equal(body.split(use).length,2,name+' explicit contract use');body=body.replace(use,'');
    }
    const view=original.slice(0,start)+body+original.slice(end);
    units.push({name,files:{[file]:view},roots:[file],theorem:'Nickel.'+module+'.'+owner,inPlace:false,
      log:name+'.proof.log',pass:name+': concrete caller requires '+contract,failure:name+': require the exact ordinary caller rejection'});
  }
  // These consumers already withhold the native/generic callee at every final
  // query. Delete the explicit use, preserving all existing statement domains.
  for(const [name,module,owner,use] of [
    ['stream-text-without-shared-checks','EventGraphText','text_admission_checks_streams','  Nickel.EventGraph.validated_stream_checks facts offered (text_event_ops ());'],
    ['stream-validation-without-text-checks','EditWellFormed','successful_validation_has_stream_checks','  Nickel.EventGraphText.text_admission_checks_streams facts fact;'],
    ['stream-shared-without-loop-contract','EventGraph','validated_stream_checks',null],
    ['stream-public-without-validation-checks','EditWellFormed','receive_added_checks_stream','successful_validation_has_stream_checks (Alloc.Vec.impl_1__as_slice before.f_facts) fact;'],
    ['stream-public-without-plan-validation','EditWellFormed','receive_added_checks_stream','  Nickel.EditAtomic.successful_plan_requires_validation before fact;'],
    ['stream-public-without-receive-plan','EditWellFormed','receive_added_checks_stream','  Nickel.EditCommit.receive_uses_plan before fact;'],
  ]) {
    const file='Nickel.'+module+'.fst',original=read(file);
    const start=original.indexOf('let '+owner+' ');assert(start>=0);
    const next=/\nlet (?:rec )?\w+ /.exec(original.slice(start+4));const end=next?start+4+next.index:original.length;
    let decl=original.slice(start,end);
    if(use){assert.equal(decl.split(use).length,2,name+' one explicit use');decl=decl.replace(use,'  ();');}
    else {const from=decl.indexOf('Nickel.LoopUtil.result_preserve_any '),to=decl.indexOf(';',from);assert(from>=0&&to>from);decl=decl.slice(0,from)+'()'+decl.slice(to);}
    const view=original.slice(0,start)+decl+original.slice(end);
    units.push({name,files:{[file]:view},roots:[file],theorem:'Nickel.'+module+'.'+owner,inPlace:true,
      log:name+'.proof.log',pass:name+': checked stream contract is load-bearing',failure:name+': ordinary named rejection required'});
  }
  return viewUnits('event',units,read);
}
