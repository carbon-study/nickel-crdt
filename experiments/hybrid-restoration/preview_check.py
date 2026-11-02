"""Actual inspect/confirm calls: identity effects, stale rejection and reload."""
from dataclasses import asdict, replace
from copy import deepcopy
import json, sys
from model import ModelError
from sessions import Session, Blocked
from session_check import deliver, shown
from continuation_check import synced


def state(s):
    return s.checkpoint(), dict(s.doc.events)


def inspect(s, source):
    before=state(s)
    p=s.inspect_restore(source)
    if state(s)!=before:
        raise AssertionError('inspection must not change document or private history')
    if p.event.id!=f'{s.writer}:{s.counter}':
        raise AssertionError('inspection must predict without reserving the next identity')
    return p


def rejects(s, preview, message):
    before=state(s)
    try: s.confirm_restore(preview,redo_policy='keep')
    except ModelError: pass
    else: raise AssertionError(message)
    if state(s)!=before:
        raise AssertionError('rejected preview changed document or private history')


def mixed():
    a,b,c=Session('A'),Session('B'),Session('C')
    friday=a.edit(creates=('F',)); carol=c.edit(creates=('c',)); synced(a,b,c)
    monday=b.edit(creates=('M',),deletes=friday.creates+carol.creates); synced(a,b,c)
    return a,b,c,friday,carol,monday


def identities(rows): return {r.identity for r in rows}


def delta(s,p):
    before=s.doc.visible()
    trial=s.doc.copy(); trial.put(p.event)
    after=trial.visible()
    if (identities(p.before)!=before or identities(p.after)!=after or
        identities(p.restored)!=after-before or identities(p.retained)!=before&after):
        raise AssertionError('preview must report actual visible delta')


def whole_scope_and_reload():
    a,b,c,f,cc,m=mixed()
    p=inspect(a,m.id); delta(a,p)
    assert {(o.scalar,o.creator) for o in p.restored}=={('F','A'),('c','C')}
    assert [(o.scalar,o.creator) for o in p.retained]==[('M','B')]
    assert not p.still_hidden
    assert inspect(a,m.id)==p
    # Duplicate delivery and pure queries do not invalidate the same basis.
    a.receive(m); a.next_undo(); a.restoration_choices(); assert a.redo() is None
    warm=deepcopy(a)
    cold=Session.resume(a.checkpoint(),a.doc.copy())
    ew=warm.confirm_restore(p); ec=cold.confirm_restore(p)
    assert ew==ec==p.event and warm.checkpoint()==cold.checkpoint()
    assert warm.doc.visible()==identities(p.after)
    # Confirmation is not repeatable after the first successful publication.
    rejects(warm,p,'replayed preview must reject after successful confirmation')
    deliver(ec,b,c)
    assert shown(cold)==shown(b)==shown(c)==['F','M','c']
    cold.undo(); assert shown(cold)==['M']
    cold.redo(); assert shown(cold)==['F','M','c']
    return dict(restored=[asdict(o) for o in p.restored],retained=[asdict(o) for o in p.retained],
                predicted_and_published=ew.id,warm_cold_equal=True)


def stale_and_hidden_effects():
    a,b,c,f,cc,m=mixed()
    p=inspect(a,m.id)
    # Carol withdraws her own already-deleted occurrence: same screen, new facts.
    before_visible=a.doc.visible(); deliver(c.undo(),a,b)
    assert a.doc.visible()==before_visible
    rejects(a,p,'changed basis must reject confirmation')
    current=inspect(a,m.id); delta(a,current)
    assert [o.scalar for o in current.restored]==['F']
    assert [o.scalar for o in current.still_hidden]==['c']
    result=a.confirm_restore(current)
    assert result==current.event and shown(a)==['F','M']
    # A fresh unrelated remote edit invalidates too, even if Restore's masks agree.
    a,b,c,f,cc,m=mixed(); p=inspect(a,m.id)
    deliver(c.edit(creates=('x',)),a,b)
    rejects(a,p,'changed basis must reject confirmation')
    # An extra shared fact with no visible or restoration effect also invalidates.
    a,b,c,f,cc,m=mixed(); p=inspect(a,m.id)
    from model import Event
    harmless=Event('C:notice',after=tuple(a.doc.events),author='C')
    a.receive(harmless)
    rejects(a,p,'changed basis must reject confirmation')
    return dict(hidden_fact_rejected=True,new_restored=['F'],still_hidden=['c'],
                unrelated_edit_rejected=True,semantic_noop_fact_rejected=True)


def private_binding_and_tamper():
    a,b,c,f,cc,m=mixed(); p=inspect(a,m.id)
    rejects(b,p,'foreign writer preview must reject')
    rejects(a,replace(p,restored=()),'altered preview must reject before publication')
    rejects(a,replace(p,event=replace(p.event,releases=())),
            'altered preview must reject before publication')
    rejects(a,replace(p,source='missing'),'altered preview must reject before publication')
    rejects(a,asdict(p),'untyped preview must reject')
    # Same document, different private continuation is not the same confirmation.
    doc=dict(a.doc.events); a.clear_history(); assert a.doc.events==doc
    rejects(a,p,'changed private history must reject confirmation')
    return dict(foreign_writer=True,display_tamper=True,event_tamper=True,source_tamper=True,
                untyped_value=True,clear_history=True)


def scoped_reactivation_and_policy():
    a,b=Session('A'),Session('B')
    paste=a.edit(creates=('p','q')); deliver(paste,b)
    withdrawal=a.undo(); deletion=b.edit(deletes=(paste.creates[0],))
    deliver(deletion,a); deliver(withdrawal,b)
    p=inspect(a,deletion.id); delta(a,p)
    assert [o.scalar for o in p.restored]==['p']
    assert p.event.reactivates==((withdrawal.id,paste.creates[0]),)
    before=state(a)
    try: a.confirm_restore(p)
    except ModelError: pass
    else: raise AssertionError('pending redo must still require explicit policy')
    assert state(a)==before  # A rejected missing policy does not consume the preview.
    event=a.confirm_restore(p,redo_policy='keep'); assert event==p.event and shown(a)==['p']
    a.undo(); assert shown(a)==[]
    a.redo(); assert shown(a)==['p']
    return dict(restored=['p'],grouped_q_retained_hidden=True,policy_rejection_unchanged=True)


def blocked_confirmation():
    a,b,c=Session('A'),Session('B'),Session('C')
    birth=a.edit(creates=('x',)); synced(a,b,c)
    deletion=b.edit(deletes=birth.creates); synced(a,b,c)
    a.restore(deletion.id); synced(a,b,c)
    later=c.edit(deletes=birth.creates); deliver(later,a,b)
    a.undo()  # Undo Restore while the later deletion already hides x.
    p=inspect(a,deletion.id); delta(a,p)
    assert p.before==p.after and not p.restored and p.still_hidden
    before=state(a); result=a.confirm_restore(p)
    assert isinstance(result,Blocked) and state(a)==before
    assert a.confirm_restore(p)==result and state(a)==before
    return dict(reason=result.reason,still_hidden=[o.scalar for o in p.still_hidden],unchanged=True)


def report():
    return dict(scope='in-process full-checkpoint-bound Restore proposals; identity sets, no text ordering',
        whole_scope=whole_scope_and_reload(),stale=stale_and_hidden_effects(),
        rejected=private_binding_and_tamper(),own_scope=scoped_reactivation_and_policy(),
        blocked=blocked_confirmation())


if __name__=='__main__':
    mode=sys.argv[1] if len(sys.argv)>1 else 'check'
    if mode=='reselect-on-confirm':
        original=Session.confirm_restore
        Session.confirm_restore=lambda self,p,redo_policy=None: original(self,self.inspect_restore(p.source),redo_policy)
        stale_and_hidden_effects()
    elif mode=='accept-altered-preview':
        import inspect as introspect,textwrap
        from sessions import RestorePreview
        source=textwrap.dedent(introspect.getsource(Session.confirm_restore)).replace(
            'if preview != self.inspect_restore(preview.source):','if False:')
        namespace=dict(RestorePreview=RestorePreview,ModelError=ModelError,Blocked=Blocked)
        exec(source,namespace); Session.confirm_restore=namespace['confirm_restore']
        private_binding_and_tamper()
    elif mode=='reserve-on-inspect':
        original=Session.inspect_restore
        def reserve(self,source):
            p=original(self,source); self.counter+=1; return p
        Session.inspect_restore=reserve
        whole_scope_and_reload()
    elif mode=='preview-target-list':
        original=Session.inspect_restore
        def target_list(self,source):
            p=original(self,source)
            return replace(p,restored=self._occurrences(set(self.doc.events[source].deletes)))
        Session.inspect_restore=target_list
        stale_and_hidden_effects()
    elif mode=='check': print(json.dumps(report(),indent=2))
    else: raise SystemExit('unknown preview-check mode')
