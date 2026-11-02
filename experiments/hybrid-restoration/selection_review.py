"""Accepted creator-slot regressions using the actual Session transitions."""
import json
from sessions import Session
from session_check import deliver, shown


def redo_arrival(cls, before_redo, cold=False):
    a, b = cls('A'), cls('B')
    p = a.edit(creates=('p',)); deliver(p, b)
    original_a = a.edit(creates=('a',)); a.undo()
    deletion = b.edit(deletes=p.creates)
    if before_redo:
        deliver(deletion, a)
    redone = a.redo()
    if not before_redo:
        deliver(deletion, a)
    if cold:
        a = cls.resume(a.checkpoint(), a.doc.copy())
    start = shown(a)
    sequence = []
    for _ in range(3):
        selected = a.next_undo()
        event = a.undo()
        sequence.append(dict(selected=selected, emitted=event.id if event else None, values=shown(a)))
    return dict(deletion_received='before redo' if before_redo else 'after redo',
        cold=cold, initial=start, redone_source=original_a.id, redo_after=redone.after,
        undo_sequence=sequence)


def overlap(cls):
    a, b = cls('A'), cls('B')
    birth = a.edit(creates=tuple('abc')); deliver(birth, b)
    aa, bb, cc = birth.creates
    own_delete = a.edit(deletes=(aa, bb))
    peer_delete = b.edit(deletes=(bb, cc))
    deliver(own_delete, b); deliver(peer_delete, a)
    selected = a.next_undo(); restored = a.undo()
    return dict(creation_item=birth.id, own_delete=own_delete.id, peer_delete=peer_delete.id,
        selected=selected, released_atoms=restored.releases, actual=shown(a), requested=list('ab'))


def grouped_and_spanning():
    cases = {}
    for cold in (False, True):
        a, b = Session('A'), Session('B')
        group = a.edit(creates=('p', 'a')); deliver(group, b)
        deletion = b.edit(deletes=(group.creates[0],)); deliver(deletion, a)
        if cold: a = Session.resume(a.checkpoint(), a.doc.copy())
        a.undo(); first = shown(a)
        a.undo(); second = shown(a)
        assert (first, second) == (['a', 'p'], []), 'group creator placement'
        cases[f'group-cold-{cold}'] = [first, second]
        a, b = Session('A'), Session('B')
        p = a.edit(creates=('p',)); middle = a.edit(creates=('a',)); q = a.edit(creates=('q',))
        for e in (p, middle, q): deliver(e, b)
        deletion = b.edit(deletes=p.creates+q.creates); deliver(deletion, a)
        if cold: a = Session.resume(a.checkpoint(), a.doc.copy())
        assert a.next_undo() == ('victim', deletion.id), 'newest affected creation anchors one victim'
        a.undo(); sequence = [shown(a)]
        for _ in range(3):
            a.undo(); sequence.append(shown(a))
        assert sequence == [['a', 'p', 'q'], ['a', 'p'], ['p'], []], 'spanning deletion has one slot'
        cases[f'spanning-cold-{cold}'] = sequence
    return cases


def retained_review_cases():
    results = {}
    # A's replacement is reached only after restoring the peer's deletion of a.
    a, b = Session('A'), Session('B')
    p = a.edit(creates=('p',)); deliver(p, b)
    aa = a.edit(creates=('a',), deletes=p.creates); deliver(aa, b)
    bb = b.edit(creates=('b',), deletes=aa.creates); deliver(bb, a)
    a.undo(); first = shown(a); a.undo(); second = shown(a)
    assert (first, second) == (['a', 'b'], ['b', 'p'])
    results['replacement_chain'] = [first, second]
    # Matching scalar values remain distinct when victim restoration brings back x.
    a, b = Session('A'), Session('B')
    x = a.edit(creates=('x',)); deliver(x, b)
    xx = b.edit(creates=('x',), deletes=x.creates); deliver(xx, a)
    a.undo(); assert shown(a) == ['x', 'x']
    results['equal_replacement'] = shown(a)
    # Clear forgets known victims, without erasing the birth used by new victims.
    for before in (True, False):
        a, b = Session('A'), Session('B')
        x = a.edit(creates=('x',)); deliver(x, b)
        deletion = b.edit(deletes=x.creates)
        if before: a.clear_history()
        deliver(deletion, a)
        if not before: a.clear_history()
        a = Session.resume(a.checkpoint(), a.doc.copy())
        assert (a.next_undo() is not None) == before
        results[f'clear-before-receipt-{before}'] = a.next_undo()
    # Same-slot candidates use stable event IDs, independent of receipt order.
    selected = []
    for reverse in (False, True):
        a, b, c = Session('A'), Session('B'), Session('C')
        birth = a.edit(creates=('a', 'b')); deliver(birth, b, c)
        db = b.edit(deletes=(birth.creates[0],)); dc = c.edit(deletes=(birth.creates[1],))
        for e in ([dc, db] if reverse else [db, dc]): deliver(e, a)
        selected.append(a.next_undo())
    assert selected == [('victim', db.id)] * 2
    results['same-slot-order'] = selected
    return results


def report():
    arrivals = [redo_arrival(Session, before, cold) for before in (True, False) for cold in (False, True)]
    assert all([step['values'] for step in r['undo_sequence']] == [[], ['p'], []]
               for r in arrivals), 'creator-slot arrival independence'
    overlapping = overlap(Session)
    assert overlapping['actual'] == overlapping['requested'] == list('ab'), 'accepted overlap restores a,b'
    return dict(status='accepted creator-slot regressions pass',
        boundary='actual restricted Session calls; identity sets, not text ordering',
        redo_arrival=arrivals, overlap=overlapping, grouped_and_spanning=grouped_and_spanning(), retained_review_cases=retained_review_cases())


if __name__ == '__main__':
    print(json.dumps(report(), indent=2))
