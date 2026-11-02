from model import Doc, ModelError, replay
from sessions import Session, Blocked


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
    assert a.next_undo() == ('own', birth.id)
    deliver(a.restore(d.id), b)
    assert b.next_undo() == ('own', z.id)
    deliver(b.undo(), a)
    assert shown(b) == ['b'] and b.next_undo() is None
    b = same_after_resume(b)
    deliver(a.undo(), b)
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
    ra = a.restore(d.id)
    assert b.next_undo() == ('own', d.id)
    rb = b.undo()
    deliver(ra, b); deliver(rb, a)
    assert shown(a) == shown(b) == ['b', 'z']
    count = replay([z, birth, d, ra, rb], set(z.creates + birth.creates), set())
    fresh = Session('C', b.doc.copy())
    assert fresh.undo() is None
    deliver(a.undo(), b)
    assert shown(b) == ['b', 'z']
    deliver(b.redo(), a)
    assert shown(a) == shown(b) == ['z']
    aa, bb, zz, _, dd = pair()
    deliver(aa.restore(dd.id), bb)
    assert bb.next_undo() == ('own', zz.id)
    assert bb.undo().withdraws == zz.creates
    return count


def q07():
    a, b = Session('A'), Session('B')
    i = a.edit(creates=('b',)); deliver(i, b)
    da = a.edit(deletes=i.creates); db = b.edit(deletes=i.creates)
    deliver(da, b); deliver(db, a)
    # Own deletion is newer than the victim's creation slot; its frozen mask
    # still covers both observed concurrent removals, preserving q07's b result.
    assert a.next_undo() == ('own', da.id)
    assert b.next_undo() == ('own', db.id)
    ra = a.undo(); deliver(ra, b)
    assert shown(a) == shown(b) == ['b']
    before = b.checkpoint()
    assert b.undo() is None and b.checkpoint() == before, 'empty undo must preserve history'
    deliver(a.redo(), b)
    assert b.next_undo() == ('own', db.id)
    return replay([i, da, db, ra], set(i.creates), set())


def replacement():
    a, b = Session('A'), Session('B')
    i = a.edit(creates=('a',)); deliver(i, b)
    j = b.edit(creates=('B',)); deliver(j, a)
    c = a.edit(creates=('x',), deletes=i.creates+j.creates); deliver(c, b)
    assert b.next_undo() == ('own', j.id), 'foreign deletion must not enter undo selection'
    rv = b.restore(c.id); deliver(rv, a)
    assert rv.withdraws == () and shown(a) == ['B', 'a', 'x']
    uc = a.undo(); deliver(uc, b)
    assert uc.withdraws == c.creates and uc.releases and shown(b) == ['B', 'a']
    # Undoing Bo's own Restore may be invisible; it still retracts his token.
    assert b.next_undo() == ('restore', rv.id)
    ur = b.undo(); deliver(ur, a)
    assert ur.cancels == (rv.id,) and shown(a) == ['B', 'a']
    a = same_after_resume(a)
    deliver(a.redo(), b); assert shown(b) == ['x']
    deliver(b.redo(), a); assert shown(a) == shown(b) == ['B', 'a', 'x']


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
    import json
    empty = Session('A'); old = json.loads(empty.checkpoint()); old['format']='hybrid-private-session-2'
    try: Session.resume(json.dumps(old), empty.doc.copy())
    except ModelError: pass
    else: raise AssertionError('version-2 checkpoint must not silently migrate')
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
    assert resumed.next_undo() is None
    resumed.restore(removed.id); assert shown(resumed) == ['x', 'z']
    s.edit(creates=('y',))
    try:
        Session.resume(saved, s.doc.copy())
    except ModelError:
        pass
    else:
        raise AssertionError('later same-writer facts need a matching history save')
    # Isolate content: every saved ID is present; only x's scalar becomes y.
    only = Session('D'); born = only.edit(creates=('x',))
    saved_only = only.checkpoint(); bad = only.doc.copy()
    from dataclasses import replace
    bad.events[born.id] = replace(born, payloads=((born.creates[0], 'y'),))
    assert set(bad.events) == set(only.doc.events)
    try:
        Session.resume(saved_only, bad)
    except ModelError:
        pass
    else:
        raise AssertionError('same-ID changed-content basis must reject')


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
    deliver(a.restore(deletion.id), b, c)
    assert shown(a) == shown(b) == shown(c) == ['a', 'b'], 'victim restores full deletion scope'
    # Creator placement supersedes the earlier concurrent victim-first preference.
    a, b = Session('A'), Session('B')
    birth = a.edit(creates=('a',)); deliver(birth, b)
    deletion = b.edit(deletes=birth.creates); z = a.edit(creates=('z',))
    deliver(deletion, a); deliver(z, b)
    assert a.next_undo() == ('own', z.id)
    deliver(a.undo(), b); assert shown(a) == []
    deliver(a.restore(deletion.id, redo_policy='keep'), b); assert shown(a) == ['a']


def bypass_boundaries():
    # Inspection and receipt do not consume an item; pressing undo does.
    a, b, z, birth, d = pair()
    deliver(a.restore(d.id), b)
    private = b.private_state()
    assert b.next_undo() == ('own', z.id) and b.private_state() == private
    deliver(a.undo(), b)
    assert b.next_undo() == ('own', d.id)
    # An ineffective item BELOW the selected newer item was not bypassed.
    a, b = Session('A'), Session('B')
    birth = a.edit(creates=('b',)); deliver(birth, b)
    d = b.edit(deletes=birth.creates); deliver(d, a)
    z = b.edit(creates=('z',)); deliver(z, a)
    deliver(a.restore(d.id), b)
    assert b.next_undo() == ('own', z.id)
    deliver(b.undo(), a)
    deliver(a.undo(), b)
    assert b.next_undo() == ('own', d.id), 'unvisited older item must not be consumed'
    # Explicit Restore is a new own action; its redo gets private priority.
    a, b, _, _, d = pair()
    restoration = a.restore(d.id); deliver(restoration, b)
    deliver(a.undo(), b)
    deliver(a.edit(creates=('x',), redo_policy='keep'), b)
    deliver(a.redo(), b)
    a = same_after_resume(a)
    assert a.next_undo() == ('restore', restoration.id)
    deliver(a.undo(), b); assert shown(a) == ['x', 'z']


def no_op_history():
    for cold in (False, True):
        results = []
        for empty_press in (False, True):
            a, b = Session('A'), Session('B')
            birth = a.edit(creates=('b',)); deliver(birth, b)
            deletion = b.edit(deletes=birth.creates); deliver(deletion, a)
            deliver(a.restore(deletion.id), b)
            if cold: b = same_after_resume(b)
            before = b.checkpoint()
            if empty_press:
                assert b.undo() is None
                assert b.checkpoint() == before, 'empty undo must preserve history'
            deliver(a.undo(), b)
            event = b.undo()
            assert event is not None, 'empty undo must not forget a future eligible item'
            results.append((shown(b), event.releases))
        assert results[0] == results[1]
        # A later causal deletion makes this redo ineffective. No event, ID,
        # counter, selection stamp or redo entry may change, warm or cold.
        a, b, c = Session('A'), Session('B'), Session('C')
        birth = a.edit(creates=('x',)); deliver(birth, b, c)
        deletion = b.edit(deletes=birth.creates); deliver(deletion, a, c)
        restoration = a.restore(deletion.id); deliver(restoration, b, c)
        retraction = a.undo(); deliver(retraction, b, c)
        # Restore once more before Cam deletes; undo it before trying redo.
        rerestored = a.redo(); deliver(rerestored, b, c)
        later = c.edit(deletes=birth.creates); deliver(later, a, b)
        deliver(a.undo(), b, c)
        if cold: a = same_after_resume(a)
        before = a.checkpoint()
        assert isinstance(a.redo(), Blocked) and a.checkpoint() == before, 'ineffective redo must preserve history'


def trace():
    a, b, z, birth, deletion = pair()
    rows = []
    def row(label):
        rows.append(dict(step=label, valuesA=shown(a), valuesB=shown(b),
            nextA=a.next_undo(), nextB=b.next_undo(),
            redoA=[e.source for e in a.redos], redoB=[e.source for e in b.redos]))
    row('ordinary undo targets own creation, not foreign deletion')
    deliver(a.restore(deletion.id), b); row('Alice explicitly restores; Restore becomes own item')
    deliver(b.undo(), a); row('Bo consumes bypassed deletion and undoes older z')
    b = same_after_resume(b); row('Bo reloads matched private/shared checkpoint')
    deliver(a.undo(), b); row('Alice undoes her Restore; b hides; Bo item stays consumed')
    assert b.undo() is None; row('Bo empty undo changes nothing')
    deliver(a.redo(), b); row('Alice redoes Restore with fresh original-mask token')
    return dict(profile='explicit Restore; own-action undo; identity sets only', rows=rows)


def review_trace():
    from selection_review import report
    return report()


def main(skip='consume'):
    n = consumed_skip(skip)
    print(f'consumed bypass: generated {n} events; cold resume preserves consumed history')
    total = frozen_vs_observed() + q07() + creator_withdrawal()
    replacement(); redo_policy_and_clear(); remote_edit_keeps_redo()
    compatible_saves(); equal_occurrences_and_victim_scope(); bypass_boundaries(); no_op_history()
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
            self.items = [k for k in self.items if k in self.undone or k in self.restore_tokens or self._own_eligible(k)]
            return original(self)
        Session.undo = eager
        bypass_boundaries()
    elif mode == 'empty-consumes':
        original = Session.undo
        def empty_consumes(self):
            chosen, skipped = self._selection()
            if chosen is None:
                self.items = [k for k in self.items if k not in skipped]
            return original(self)
        Session.undo = empty_consumes
        no_op_history()
    elif mode == 'ineffective-redo-advances':
        Session._preview_changes = lambda self, effect: True
        no_op_history()
    elif mode == 'skip-blocked-redo':
        original = Session.redo
        def skipping(self):
            result = original(self)
            if isinstance(result, Blocked):
                held = self.redos.pop()
                try: return original(self)
                finally: self.redos.append(held)
            return result
        Session.redo = skipping
        from selection_review import blocked_older_redo
        blocked_older_redo()
    elif mode == 'refreeze-restore-redo':
        import inspect, textwrap
        source = textwrap.dedent(inspect.getsource(Session.redo)).replace(
            'releases=self.doc.events[entry.source].releases,',
            "releases=self.doc.restore('', self.doc.events[entry.source].releases[0][0]).releases,")
        from model import Event
        namespace = dict(Event=Event, Blocked=Blocked)
        exec(source, namespace)
        Session.redo = namespace['redo']
        from selection_review import frozen_restore
        frozen_restore(False)
    elif mode in ('peer-reactivation', 'scope-reactivation-spill'):
        import inspect, textwrap
        from model import Event, ModelError, Doc
        if mode == 'peer-reactivation':
            source = textwrap.dedent(inspect.getsource(Doc.put)).replace(
                'if event.author != self.events[token].author:', 'if False:')
            namespace = dict(ModelError=ModelError)
            exec(source, namespace)
            Doc.put = namespace['put']
        else:
            source = textwrap.dedent(inspect.getsource(Session.restore)).replace(
                'if elem in scope & mine and', 'if elem in mine and')
            from dataclasses import replace
            namespace = dict(Blocked=Blocked,ModelError=ModelError,replace=replace)
            exec(source, namespace)
            Session.restore = namespace['restore']
        from selection_review import scoped_author_reactivation
        scoped_author_reactivation()
    elif mode == 'drop-restore-reactivation':
        original = Session.restore
        def broken(self, source, redo_policy=None):
            out = original(self, source, redo_policy)
            if not isinstance(out, Blocked):
                from dataclasses import replace
                out = replace(out, reactivates=())
                self.doc.events[out.id] = out
            return out
        Session.restore = broken
        from selection_review import scoped_author_reactivation
        scoped_author_reactivation()
    elif mode == 'receipt-ranking':
        original = Session._selection
        def receipt(self):
            chosen, skipped = original(self)
            if chosen and chosen[0] == 'own':
                victims = [k for k, e in self.doc.events.items() if e.author != self.writer and e.deletes
                           and not self.doc.before(k, self.selection_stamps.get(chosen, chosen[1]))]
                if victims: return ('victim', min(victims)), skipped
            return chosen, skipped
        Session._selection = receipt
        from selection_review import report
        report()
    elif mode == 'presence-only-basis':
        Session._event_encoding = staticmethod(lambda event: event.id)
        compatible_saves()
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
