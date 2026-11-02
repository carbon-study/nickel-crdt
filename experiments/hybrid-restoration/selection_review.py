"""Accepted own-action Undo / explicit Restore regression scenarios."""
import json
from sessions import Session, Blocked
from session_check import deliver, shown, same_after_resume
from continuation_check import synced


def appendix(before, cold):
    a, b = Session('A'), Session('B')
    friday = a.edit(creates=('F',)); deliver(friday, b)
    a.edit(creates=('i',))
    monday = b.edit(creates=('M',), deletes=friday.creates)
    a.undo()
    if before: deliver(monday, a)
    if cold: a = same_after_resume(a)
    assert a.next_undo() == ('own', friday.id), 'foreign deletion must not enter undo selection'
    a.undo()
    if not before: deliver(monday, a)
    synced(a,b)
    assert shown(a) == shown(b) == ['M'], 'appendix Undo must not restore Friday implicitly'
    # Explicit author Restore can re-enable the SELECTED own occurrences even
    # after ordinary Undo withdrew them; peers cannot override that withdrawal.
    restored = a.restore(monday.id, redo_policy='keep')
    assert shown(a)==['F','M'] and restored.reactivates
    a=same_after_resume(a)
    a.undo(); assert shown(a)==['M']
    return dict(before=before,cold=cold,after_ordinary_undo=['M'],
                after_explicit_restore=['F','M'],after_undo_restore=shown(a))


def redo_arrival(before, cold):
    a,b=Session('A'),Session('B')
    p=a.edit(creates=('p',)); deliver(p,b)
    aa=a.edit(creates=('a',)); a.undo()
    deletion=b.edit(deletes=p.creates)
    if before: deliver(deletion,a)
    a.redo()
    if not before: deliver(deletion,a)
    if cold: a=same_after_resume(a)
    assert a.next_undo()==('own',aa.id), 'redo must remain next own undo'
    a.undo(); assert shown(a)==[]
    restoration=a.restore(deletion.id,redo_policy='keep')
    assert shown(a)==['p'] and a.next_undo()==('restore',restoration.id)
    a.undo(); assert shown(a)==[]
    return dict(before=before,cold=cold,steps=[[],['p'],[]])


def current_creator(cold):
    a,b=Session('A'),Session('B')
    p=a.edit(creates=('p',)); a.undo()
    q=a.edit(creates=('q',),redo_policy='keep'); a.redo(); synced(a,b)
    deletion=b.edit(deletes=p.creates+q.creates); deliver(deletion,a)
    if cold: a=same_after_resume(a)
    assert a.restoration_choices()==[(deletion.id,p.id)], 'display slot must use highest current creator position'
    assert a.next_undo()==('own',p.id), 'foreign deletion must not enter undo selection'
    restoration=a.restore(deletion.id)
    assert shown(a)==['p','q']
    a.undo(); assert shown(a)==[]
    return dict(cold=cold,choice=(deletion.id,p.id),restore=restoration.id,after_restore=['p','q'])


def immediate(cold):
    a,b=Session('A'),Session('B')
    paste=a.edit(creates=('p','q')); deliver(paste,b)
    ua=a.undo(); db=b.edit(deletes=(paste.creates[0],))
    deliver(ua,b); deliver(db,a)
    if cold: a=same_after_resume(a)
    a.redo(); assert shown(a)==['q']
    a.undo(); assert shown(a)==[], 'immediate undo must target the redone own paste'
    return dict(cold=cold,after_redo=['q'],after_undo=[])


def frozen_restore(cold):
    a,b,c=Session('A'),Session('B'),Session('C')
    paste=a.edit(creates=('p','q')); deliver(paste,b,c)
    db=b.edit(deletes=paste.creates); deliver(db,a)
    rp=a.restore(db.id); a.undo()
    dc=c.edit(deletes=(paste.creates[0],)); deliver(dc,a)
    if cold: a=same_after_resume(a)
    redo=a.redo()
    assert redo.releases==rp.releases and shown(a)==['q'], 'Restore redo must preserve original frozen mask'
    assert redo.id!=rp.id and a.restore_tokens[rp.id]==redo.id
    a.undo(); assert shown(a)==[], 'Undo Restore must retract the current fresh token'
    return dict(cold=cold,original=rp.id,redo=redo.id,releases=redo.releases,values_after_redo=['q'])


def same_value():
    a=Session('A'); old=a.edit(creates=('x',)); new=a.edit(creates=('x',),deletes=old.creates)
    a.undo(); before=a.doc.visible(); redone=a.redo()
    assert not isinstance(redone,Blocked) and before!=a.doc.visible() and shown(a)==['x']
    return dict(before=sorted(before),after=sorted(a.doc.visible()),values=shown(a))


def scoped_author_reactivation():
    from model import Event, ModelError
    a,b=Session('A'),Session('B')
    paste=a.edit(creates=('p','q')); deliver(paste,b)
    withdrawal=a.undo(); deletion=b.edit(deletes=(paste.creates[0],))
    deliver(deletion,a); deliver(withdrawal,b)
    explicit=a.restore(deletion.id,redo_policy='keep')
    assert shown(a)==['p'], 'explicit author Restore must recover only selected p'
    assert explicit.reactivates==((withdrawal.id,paste.creates[0]),)
    a=same_after_resume(a); a.undo(); assert shown(a)==[]
    a.redo(); assert shown(a)==['p']
    forged=Event('B:forged',after=tuple(b.doc.events),author='B',
                 reactivates=((withdrawal.id,paste.creates[0]),))
    before=dict(b.doc.events)
    try: b.doc.put(forged)
    except ModelError: pass
    else: raise AssertionError('peer must not reactivate another author withdrawal')
    assert b.doc.events==before
    return dict(restored=['p'],grouped_q_stays_withdrawn=True,peer_reactivation='rejected')


def blocked_older_redo():
    from model import Event
    a,b,c=Session('A'),Session('B'),Session('C')
    z=a.edit(creates=('z',)); a.undo()
    birth=a.edit(creates=('b',),redo_policy='keep'); synced(a,b,c)
    deletion=b.edit(deletes=birth.creates); deliver(deletion,a,c)
    restoration=a.restore(deletion.id,redo_policy='keep'); synced(a,b,c)
    later=c.edit(deletes=birth.creates)
    deliver(a.undo(),b,c); deliver(later,a,b)
    a=same_after_resume(a)
    assert [e.source for e in a.redos]==[z.id,restoration.id]
    before=a.checkpoint(); result=a.redo()
    assert (isinstance(result,Blocked) and result.operation=='redo' and
            result.source==restoration.id and a.checkpoint()==before), 'blocked top redo must not skip to older item'
    assert a._preview_changes(Event('',cancels=(a.redos[0].event,)))
    return dict(blocked_source=result.source,older_effective_source=z.id,
                reason=result.reason,history_unchanged=True)


def report():
    return dict(status='own-action undo and explicit Restore directed regressions pass',
        boundary='actual restricted identity-set Session calls; no editor or text-order claim',
        appendix=[appendix(before,cold) for before in (False,True) for cold in (False,True)],
        redo_arrival=[redo_arrival(before,cold) for before in (False,True) for cold in (False,True)],
        creator_display=[current_creator(cold) for cold in (False,True)],
        immediate=[immediate(cold) for cold in (False,True)],
        frozen_restore=[frozen_restore(cold) for cold in (False,True)],same_value=same_value(),scoped_author_reactivation=scoped_author_reactivation(),blocked_older_redo=blocked_older_redo())


if __name__=='__main__': print(json.dumps(report(),indent=2))
