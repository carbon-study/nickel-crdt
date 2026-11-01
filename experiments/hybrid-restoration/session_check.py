from model import Doc, ModelError, replay
from sessions import Session


def deliver(event, *sessions):
    for s in sessions:
        before = s.private_state()
        s.receive(event); s.receive(event)
        assert s.private_state() == before, 'import changed private history'


def shown(s):
    values = {k: value for event in s.doc.events.values() for k, value in event.payloads}
    return sorted(values[k] for k in s.doc.visible())


def pair(skip='consume'):
    a, b = Session('A'), Session('B', skip_policy=skip)
    z = b.edit(creates=('z',)); deliver(z, a)
    birth = a.edit(creates=('b',)); deliver(birth, b)
    deletion = b.edit(deletes=birth.creates); deliver(deletion, a)
    return a, b, z, birth, deletion


def same_after_resume(s):
    resumed = Session.resume(s.checkpoint(), s.doc.copy())
    assert resumed.checkpoint() == s.checkpoint()
    assert resumed.next_undo() == s.next_undo()
    assert resumed.doc.visible() == s.doc.visible()
    return resumed


def consumed_skip(skip):
    a, b, z, birth, d = pair(skip)
    assert a.next_undo() == ('victim', d.id)
    deliver(a.undo(), b)
    assert b.next_undo() == ('own', z.id)
    deliver(b.undo(), a)
    assert shown(b) == ['b'] and b.next_undo() is None
    b = same_after_resume(b)
    deliver(a.redo(), b)
    assert b.next_undo() is None, 'bypassed deletion must stay consumed after peer redo'
    before = dict(b.doc.events)
    assert b.undo() is None and b.doc.events == before
    assert shown(a) == shown(b) == []
    # The skipped deletion gained no redo entry; only Bo's actual undo of z did.
    assert [e.source for e in b.redos] == [z.id]
    deliver(b.redo(), a)
    assert shown(a) == ['z']
    return len(b.doc.events)


def frozen_vs_observed():
    a, b, z, birth, d = pair()
    ra = a.undo()
    assert b.next_undo() == ('own', d.id)
    rb = b.undo()
    deliver(ra, b); deliver(rb, a)
    assert shown(a) == shown(b) == ['b', 'z']
    count = replay([z, birth, d, ra, rb], set(z.creates + birth.creates), set())
    fresh = Session('C', b.doc.copy())
    assert fresh.undo() is None
    deliver(a.redo(), b)
    assert shown(b) == ['b', 'z']
    deliver(b.redo(), a)
    assert shown(a) == shown(b) == ['z']
    aa, bb, zz, _, _ = pair()
    deliver(aa.undo(), bb)
    assert bb.next_undo() == ('own', zz.id)
    assert bb.undo().withdraws == zz.creates
    return count


def q07():
    a, b = Session('A'), Session('B')
    i = a.edit(creates=('b',)); deliver(i, b)
    da = a.edit(deletes=i.creates); db = b.edit(deletes=i.creates)
    deliver(da, b); deliver(db, a)
    # Victim-first concurrent tie selects the other deletion; the frozen mask
    # still covers both observed concurrent removals, preserving q07's b result.
    assert a.next_undo() == ('victim', db.id)
    assert b.next_undo() == ('own', db.id)
    ra = a.undo(); deliver(ra, b)
    assert shown(a) == shown(b) == ['b']
    assert b.undo() is None  # This press consumes the bypassed item, with no event.
    deliver(a.redo(), b)
    assert b.next_undo() is None
    return replay([i, da, db, ra], set(i.creates), set())


def replacement():
    a, b = Session('A'), Session('B')
    i = a.edit(creates=('a',)); deliver(i, b)
    j = b.edit(creates=('B',)); deliver(j, a)
    c = a.edit(creates=('x',), deletes=i.creates+j.creates); deliver(c, b)
    assert b.next_undo() == ('victim', c.id)
    rv = b.undo(); deliver(rv, a)
    assert rv.withdraws == () and shown(a) == ['B', 'a', 'x']
    assert a.next_undo() == ('own', c.id)
    uc = a.undo(); deliver(uc, b)
    assert uc.withdraws == c.creates and uc.releases
    assert shown(b) == ['B', 'a']
    deliver(b.redo(), a)
    assert shown(a) == ['B', 'a']
    a = same_after_resume(a)
    deliver(a.redo(), b)
    assert shown(b) == ['x']


def creator_withdrawal():
    a, b = Session('A'), Session('B')
    i = a.edit(creates=('p',)); deliver(i, b)
    c = a.edit(creates=('x',), deletes=i.creates); deliver(c, b)
    ua = a.undo(); db = b.edit(deletes=c.creates)
    deliver(db, a); deliver(ua, b)
    assert shown(a) == shown(b) == ['p']
    ub = b.undo(); deliver(ub, a)
    assert shown(a) == ['p']
    count = replay([i, c, ua, db, ub], set(i.creates), set(), {(ua.id, c.creates[0])},
                   {frozenset(i.creates+c.creates)})
    deliver(a.redo(), b); assert shown(b) == ['x']
    deliver(b.redo(), a); assert shown(a) == []
    return count


def redo_policy_and_clear():
    for policy, expected in [('keep', ['b', 'x']), ('clear', ['x'])]:
        s = Session('A')
        birth = s.edit(creates=('b',)); s.undo()
        prior = s.checkpoint(), dict(s.doc.events)
        try:
            s.edit(creates=('x',))
        except ModelError:
            pass
        else:
            raise AssertionError('unresolved redo policy was silently chosen')
        assert (s.checkpoint(), s.doc.events) == prior
        x = s.edit(creates=('x',), redo_policy=policy)
        s.redo(); assert shown(s) == expected
        if policy == 'keep':
            assert s.next_undo() == ('own', birth.id), 'redone item must be next undo'
            s = same_after_resume(s)
            s.undo(); assert shown(s) == ['x'], 'undo after redo must retain newer x'
            s.redo(); s.edit(creates=('y',), redo_policy='keep')
            assert shown(s) == ['b', 'x', 'y']
            s.undo(); assert shown(s) == ['b', 'x']  # A later primary edit takes priority.
    s = Session('A'); s.edit(creates=('b',)); s.undo()
    facts = dict(s.doc.events); s.clear_history()
    assert s.doc.events == facts and shown(s) == []
    assert s.undo() is None and s.redo() is None
    same_after_resume(s)


def remote_edit_keeps_redo():
    a, b = Session('A'), Session('B')
    i = a.edit(creates=('a',)); deliver(i, b)
    deliver(a.undo(), b)
    deliver(b.edit(creates=('B',)), a)
    assert len(a.redos) == 1
    a = same_after_resume(a); deliver(a.redo(), b)
    assert shown(a) == shown(b) == ['B', 'a']


def compatible_saves():
    s = Session('A'); s.edit(creates=('x',)); s.undo()
    earlier = s.doc.copy(); s.redo(); later_history = s.checkpoint()
    try:
        Session.resume(later_history, earlier)
    except ModelError:
        pass
    else:
        raise AssertionError('incompatible document/history save must reject')
    s.clear_history()
    try:
        Session.resume(s.checkpoint(), earlier)
    except ModelError:
        pass
    else:
        raise AssertionError('cleared history must still bind shared basis')
    # Remote extension is compatible, but a same-writer future is not.
    saved = s.checkpoint(); later = s.doc.copy()
    peer = Session('B', later); event = peer.edit(creates=('z',))
    resumed = Session.resume(saved, later)
    assert shown(resumed) == ['x', 'z']
    original_x = next(e.creates[0] for e in later.events.values() if e.author == 'A' and e.creates)
    removed = peer.edit(deletes=(original_x,))
    resumed = Session.resume(saved, later.copy())
    assert resumed.next_undo() == ('victim', removed.id)
    resumed.undo(); assert shown(resumed) == ['x', 'z']
    s.edit(creates=('y',))
    try:
        Session.resume(saved, s.doc.copy())
    except ModelError:
        pass
    else:
        raise AssertionError('later same-writer facts need a matching history save')
    # Same IDs with different content are not a compatible basis either.
    from dataclasses import replace
    bad = earlier.copy(); first = next(iter(bad.events))
    bad.events[first] = replace(bad.events[first], author='changed')
    try:
        Session.resume(Session.resume(saved, later).checkpoint(), bad)
    except ModelError:
        pass
    else:
        raise AssertionError('changed saved facts must reject')


def equal_occurrences_and_victim_scope():
    a, b = Session('A'), Session('B')
    aa = a.edit(creates=('x',)); bb = b.edit(creates=('x',))
    assert aa.creates != bb.creates, 'equal values need different occurrence identities'
    deliver(aa, b); deliver(bb, a)
    assert shown(a) == shown(b) == ['x', 'x'] and len(a.doc.visible()) == 2
    deliver(a.undo(), b)
    assert a.doc.visible() == b.doc.visible() == set(bb.creates)
    assert shown(a) == ['x']
    # Equal values within one edit also get distinct occurrences.
    c = Session('C'); cc = c.edit(creates=('x', 'x'))
    assert len(set(cc.creates)) == 2 and shown(c) == ['x', 'x']
    c.undo(); assert shown(c) == []
    c.redo(); assert c.doc.visible() == set(cc.creates) and shown(c) == ['x', 'x']
    for bad in [('xx',), ('\ud800',)]:
        before = c.checkpoint()
        try:
            c.edit(creates=bad, redo_policy='keep')
        except ModelError:
            pass
        else:
            raise AssertionError('invalid scalar edit must reject')
        assert c.checkpoint() == before
    a, b, c = Session('A'), Session('B'), Session('C')
    aa = a.edit(creates=('a',)); bb = b.edit(creates=('b',))
    deliver(aa, b, c); deliver(bb, a, c)
    deletion = c.edit(deletes=aa.creates+bb.creates); deliver(deletion, a, b)
    deliver(a.undo(), b, c)
    assert shown(a) == shown(b) == shown(c) == ['a', 'b'], 'victim restores full deletion scope'
    # Ren prefers restoration over an independent concurrent own edit.
    a, b = Session('A'), Session('B')
    birth = a.edit(creates=('a',)); deliver(birth, b)
    deletion = b.edit(deletes=birth.creates); z = a.edit(creates=('z',))
    deliver(deletion, a); deliver(z, b)
    assert a.next_undo() == ('victim', deletion.id)
    deliver(a.undo(), b); assert shown(a) == ['a', 'z']


def bypass_boundaries():
    # Inspection and receipt do not consume an item; pressing undo does.
    a, b, z, birth, d = pair()
    deliver(a.undo(), b)
    private = b.private_state()
    assert b.next_undo() == ('own', z.id) and b.private_state() == private
    deliver(a.redo(), b)
    assert b.next_undo() == ('own', d.id)
    # An ineffective item BELOW the selected newer item was not bypassed.
    a, b = Session('A'), Session('B')
    birth = a.edit(creates=('b',)); deliver(birth, b)
    d = b.edit(deletes=birth.creates); deliver(d, a)
    z = b.edit(creates=('z',)); deliver(z, a)
    deliver(a.undo(), b)
    assert b.next_undo() == ('own', z.id)
    deliver(b.undo(), a)
    deliver(a.redo(), b)
    assert b.next_undo() == ('own', d.id), 'unvisited older item must not be consumed'
    # A redone victim restoration also gets a new private priority stamp.
    a, b, _, _, d = pair()
    deliver(a.undo(), b)
    deliver(a.edit(creates=('x',), redo_policy='keep'), b)
    deliver(a.redo(), b)
    a = same_after_resume(a)
    assert a.next_undo() == ('victim', d.id)
    deliver(a.undo(), b); assert shown(a) == ['b', 'x', 'z']


def trace():
    a, b, z, birth, deletion = pair()
    rows = []
    def row(label):
        rows.append(dict(step=label, visibleA=sorted(a.doc.visible()), visibleB=sorted(b.doc.visible()),
            valuesA=shown(a), valuesB=shown(b), nextA=a.next_undo(), nextB=b.next_undo(),
            redoA=[e.source for e in a.redos], redoB=[e.source for e in b.redos]))
    row('both know the deletion')
    deliver(a.undo(), b); row('Alice restores; Bo can bypass his deletion')
    deliver(b.undo(), a); row('Bo consumes bypassed deletion and undoes older z')
    b = same_after_resume(b); row('Bo reloads compatible private checkpoint and shared facts')
    deliver(a.redo(), b); row('Alice redo hides b; consumed Bo item does not return')
    assert b.undo() is None; row('Bo undo emits nothing')
    return dict(profile='consumed skip; library occurrence identities; identity sets only', rows=rows)


def review_trace():
    cases = {}
    a = Session('A'); a.edit(creates=('x',)); a.undo()
    earlier = a.doc.copy(); a.redo()
    try:
        Session.resume(a.checkpoint(), earlier)
        result = 'accepted'
    except ModelError as error:
        result = str(error)
    cases['incompatible_save'] = dict(result=result, earlier_visible=sorted(earlier.visible()))
    a, b = Session('A'), Session('B')
    aa = a.edit(creates=('x',)); bb = b.edit(creates=('x',))
    deliver(aa, b); deliver(bb, a)
    both = shown(a); removed = a.undo(); deliver(removed, b)
    cases['equal_occurrences'] = dict(alice_ids=aa.creates, bo_ids=bb.creates,
        before=both, withdrawn=removed.withdraws, after=shown(a), remaining=sorted(a.doc.visible()))
    cases['consumed_bypass'] = trace()['rows']
    a, b, c = Session('A'), Session('B'), Session('C')
    aa = a.edit(creates=('a',)); bb = b.edit(creates=('b',))
    deliver(aa, b, c); deliver(bb, a, c)
    deletion = c.edit(deletes=aa.creates+bb.creates); deliver(deletion, a, b)
    restored = a.undo(); deliver(restored, b, c)
    cases['whole_victim_scope'] = dict(selected=deletion.id,
        restored_atoms=restored.releases, values=shown(a))
    a = Session('A'); birth = a.edit(creates=('a',)); a.undo()
    x = a.edit(creates=('x',), redo_policy='keep'); a.redo()
    selected = a.next_undo(); a.undo()
    cases['redo_priority'] = dict(redone_source=birth.id, newer_primary=x.id,
        selected=selected, after_undo=shown(a))
    a, b = Session('A'), Session('B')
    birth = a.edit(creates=('a',)); deliver(birth, b)
    deletion = b.edit(deletes=birth.creates); z = a.edit(creates=('z',))
    deliver(deletion, a); deliver(z, b)
    selected = a.next_undo(); deliver(a.undo(), b)
    cases['concurrent_victim_first'] = dict(selected=selected, after_undo=shown(a))
    return dict(scope='actual restricted reference calls; visible values are not text order', cases=cases)


def main(skip='consume'):
    n = consumed_skip(skip)
    print(f'consumed bypass: generated {n} events; cold resume preserves consumed history')
    total = frozen_vs_observed() + q07() + creator_withdrawal()
    replacement(); redo_policy_and_clear(); remote_edit_keeps_redo()
    compatible_saves(); equal_occurrences_and_victim_scope(); bypass_boundaries()
    print(f'generated-action delivery replay: {total} legal schedules across 3 event sets')
    print('PASS private session review repairs and directed continuations')


if __name__ == '__main__':
    import sys
    mode = sys.argv[1] if len(sys.argv) > 1 else 'consume'
    if mode == 'trace':
        import json
        print(json.dumps(trace(), indent=2))
    elif mode == 'review-trace':
        import json
        print(json.dumps(review_trace(), indent=2))
    elif mode == 'eager-consume':
        original = Session.undo
        def eager(self):
            self.items = [k for k in self.items if k in self.undone or self._own_eligible(k)]
            return original(self)
        Session.undo = eager
        bypass_boundaries()
    elif mode == 'unbound-save':
        import json
        original = Session.resume.__func__
        def unbound(cls, raw, document):
            x = json.loads(raw)
            x['basis'] = {k: cls._event_encoding(e) for k, e in document.events.items()}
            return original(cls, json.dumps(x), document)
        Session.resume = classmethod(unbound)
        compatible_saves()
    elif mode == 'caller-ids':
        Session._created_identity = lambda self, index, value: value
        equal_occurrences_and_victim_scope()
    elif mode == 'old-redo-order':
        original = Session.redo
        def old_redo(self):
            event = original(self)
            self.selection_stamps.clear()
            return event
        Session.redo = old_redo
        redo_policy_and_clear()
    elif mode in ('retain', 'consume'):
        main(mode)
    else:
        raise SystemExit('expected retain, consume or trace')
