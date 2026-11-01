from model import Doc, ModelError, replay
from sessions import Session


def deliver(event, *sessions):
    for s in sessions:
        before = s.checkpoint()
        s.receive(event)
        s.receive(event)
        assert s.checkpoint() == before, 'import changed private history'


def pair(skip='retain'):
    a, b = Session('A'), Session('B', skip_policy=skip)
    z = b.edit(creates=('z',)); deliver(z, a)
    birth = a.edit(creates=('b',)); deliver(birth, b)
    deletion = b.edit(deletes=('b',)); deliver(deletion, a)
    return a, b, z, birth, deletion


def same_after_resume(s):
    resumed = Session.resume(s.checkpoint(), s.doc.copy())
    assert resumed.checkpoint() == s.checkpoint()
    assert resumed.next_undo() == s.next_undo()
    assert resumed.doc.visible() == s.doc.visible()
    return resumed


def skipped_reactivation(skip):
    a, b, z, birth, d = pair(skip)
    assert a.next_undo() == ('victim', d.id)
    restore = a.undo(); deliver(restore, b)
    assert b.next_undo() == ('own', z.id)
    remove_z = b.undo(); deliver(remove_z, a)
    assert b.doc.visible() == {'b'}
    assert b.next_undo() is None
    b = same_after_resume(b)
    redelete = a.redo(); deliver(redelete, b)
    assert b.next_undo() == ('own', d.id), 'skipped deletion must reactivate after peer redo'
    assert b.doc.visible() == set()
    b = same_after_resume(b)
    restore_again = b.undo(); deliver(restore_again, a)
    assert b.doc.visible() == a.doc.visible() == {'b'}
    # Two actual redo calls reverse Bo's last two actual undo calls.
    deliver(b.redo(), a)
    assert a.doc.visible() == set()
    deliver(b.redo(), a)
    assert a.doc.visible() == {'z'}
    return len(b.doc.events)


def frozen_vs_observed():
    a, b, z, birth, d = pair()
    ra = a.undo()
    # Bo has NOT received RA: his actual selector still chooses D, not Z.
    assert b.next_undo() == ('own', d.id)
    rb = b.undo()
    deliver(ra, b); deliver(rb, a)
    assert a.doc.visible() == b.doc.visible() == {'z', 'b'}
    # The events came from Session.undo, not hand-authored fixture effects.
    count = replay([z, birth, d, ra, rb], {'z', 'b'}, set())
    snapshot = b.doc.copy()
    fresh = Session('C', snapshot)
    assert fresh.undo() is None  # No private history was shared.
    deliver(a.redo(), b)
    assert b.doc.visible() == {'z', 'b'}  # Bo's restoration still stands.
    deliver(b.redo(), a)
    assert a.doc.visible() == b.doc.visible() == {'z'}
    # The same user pressing after receiving RA legitimately selects older Z.
    aa, bb, zz, _, dd = pair()
    deliver(aa.undo(), bb)
    assert bb.next_undo() == ('own', zz.id)
    assert bb.undo().withdraws == ('z',)
    return count


def q07():
    a, b = Session('A'), Session('B')
    i = a.edit(creates=('b',)); deliver(i, b)
    da = a.edit(deletes=('b',))
    db = b.edit(deletes=('b',))
    deliver(da, b); deliver(db, a)
    assert a.next_undo() == ('own', da.id)
    assert b.next_undo() == ('own', db.id)
    ra = a.undo(); deliver(ra, b)
    assert a.doc.visible() == b.doc.visible() == {'b'}
    before = b.checkpoint(), dict(b.doc.events)
    assert b.undo() is None
    assert (b.checkpoint(), b.doc.events) == before
    deliver(a.redo(), b)
    assert b.next_undo() == ('own', db.id)
    return replay([i, da, db, ra], {'b'}, set())


def replacement():
    a, b = Session('A'), Session('B')
    i = a.edit(creates=('a',)); deliver(i, b)
    j = b.edit(creates=('B',)); deliver(j, a)
    c = a.edit(creates=('x',), deletes=('a', 'B')); deliver(c, b)
    assert b.next_undo() == ('victim', c.id)
    rv = b.undo(); deliver(rv, a)
    assert rv.withdraws == () and a.doc.visible() == {'a', 'B', 'x'}
    assert a.next_undo() == ('own', c.id)
    uc = a.undo(); deliver(uc, b)
    assert uc.withdraws == ('x',) and uc.releases
    assert b.doc.visible() == {'a', 'B'}
    deliver(b.redo(), a)
    assert a.doc.visible() == {'a', 'B'}
    a = same_after_resume(a)
    deliver(a.redo(), b)
    assert b.doc.visible() == {'x'}


def creator_withdrawal():
    a, b = Session('A'), Session('B')
    i = a.edit(creates=('p',)); deliver(i, b)
    c = a.edit(creates=('x',), deletes=('p',)); deliver(c, b)
    ua = a.undo()  # Alice does not know Bo will delete x.
    db = b.edit(deletes=('x',))  # Bo does not know Alice withdrew x.
    deliver(db, a); deliver(ua, b)
    assert a.doc.visible() == b.doc.visible() == {'p'}
    ub = b.undo(); deliver(ub, a)
    assert a.doc.visible() == {'p'}
    count = replay([i, c, ua, db, ub], {'p'}, set(), {(ua.id, 'x')},
                   {frozenset({'p', 'x'})})
    deliver(a.redo(), b)
    assert b.doc.visible() == {'x'}
    deliver(b.redo(), a)
    assert a.doc.visible() == set()
    return count


def redo_policy_and_clear():
    for policy, expected in [('keep', {'b', 'x'}), ('clear', {'x'})]:
        s = Session('A')
        s.edit(creates=('b',)); s.undo()
        prior = s.checkpoint(), dict(s.doc.events)
        try:
            s.edit(creates=('x',))
        except ModelError:
            pass
        else:
            raise AssertionError('unresolved redo policy was silently chosen')
        assert (s.checkpoint(), s.doc.events) == prior
        s.edit(creates=('x',), redo_policy=policy)
        s.redo()
        assert s.doc.visible() == expected
    s = Session('A'); s.edit(creates=('b',)); s.undo()
    facts = dict(s.doc.events)
    s.clear_history()
    assert s.doc.events == facts and s.doc.visible() == set()
    assert s.undo() is None and s.redo() is None
    same_after_resume(s)


def remote_edit_keeps_redo():
    a, b = Session('A'), Session('B')
    i = a.edit(creates=('a',)); deliver(i, b)
    u = a.undo(); deliver(u, b)
    foreign = b.edit(creates=('B',)); deliver(foreign, a)
    assert len(a.redos) == 1
    a = same_after_resume(a)
    deliver(a.redo(), b)
    assert a.doc.visible() == b.doc.visible() == {'a', 'B'}


def trace():
    a, b, z, birth, deletion = pair()
    rows = []
    def row(label):
        rows.append(dict(step=label, visibleA=sorted(a.doc.visible()),
                         visibleB=sorted(b.doc.visible()),
                         nextA=a.next_undo(), nextB=b.next_undo(),
                         redoA=[e.source for e in a.redos],
                         redoB=[e.source for e in b.redos]))
    row('both know the deletion')
    deliver(a.undo(), b)
    row('Alice restores; Bo skips his deletion')
    deliver(b.undo(), a)
    row('Bo undoes older z')
    b = same_after_resume(b)
    row('Bo reloads private checkpoint plus shared facts')
    deliver(a.redo(), b)
    row('Alice redo reactivates Bo deletion')
    deliver(b.undo(), a)
    row('Bo selects the reactivated deletion')
    return dict(profile='candidate reversible skip; identity sets only', rows=rows)


def main(skip='retain'):
    n = skipped_reactivation(skip)
    print(f'skipped-item reactivation: generated {n} events; resumed both before/after peer redo')
    total = frozen_vs_observed() + q07() + creator_withdrawal()
    replacement()
    redo_policy_and_clear()
    remote_edit_keeps_redo()
    print(f'generated-action delivery replay: {total} legal schedules across 3 event sets')
    print('PASS private session selection/effect/redo/import/checkpoint directed cases')


if __name__ == '__main__':
    import sys
    mode = sys.argv[1] if len(sys.argv) > 1 else 'retain'
    if mode == 'trace':
        import json
        print(json.dumps(trace(), indent=2))
    elif mode in ('retain', 'consume'):
        main(mode)
    else:
        raise SystemExit('expected retain, consume or trace')
