from dataclasses import replace
from model import Event, ModelError, doc, replay


def withdraw_in(event, elements, mode):
    # The user's compound undo is one event with both effect facets.
    if mode == 'legacy-hide':
        return replace(event, deletes=elements)
    return replace(event, withdraws=elements)


def cases(mode='parallel'):
    # Review repro: Bo's undo must not resurrect a creation withdrawn by Alice.
    p = Event('I', creates=('p',))
    replace = Event('C', ('I',), creates=('x',), deletes=('p',))
    bo_delete = Event('DB', ('C',), deletes=('x',))
    inverse = withdraw_in(doc(p, replace).restore('UC', 'C', mode), ('x',), mode)
    prefix = [p, replace, bo_delete, inverse]
    withdrawal_token = 'UC'
    if mode == 'split-undo':
        prefix = [p, replace, bo_delete, Event('UC', inverse.after, releases=inverse.releases),
                  Event('UX', ('UC',), withdraws=('x',))]
        withdrawal_token = 'UX'
    restore_bo = doc(*prefix).restore('RB', 'DB', mode)
    both = prefix + [restore_bo]
    yield 'creator withdrawal survives peer deletion undo', both, {'p'}, set(), {(withdrawal_token, 'x')}
    if mode == 'split-undo':
        return
    redo_a = Event('XA', ('RB',), cancels=('UC',))
    yield 'creator redo restores its creation', both + [redo_a], {'x'}, {('C', 'p')}, set()
    redo_b = Event('XB', ('XA',), cancels=('RB',))
    yield 'peer deletion redo after creator redo', both + [redo_a, redo_b], set(), {('C', 'p'), ('DB', 'x')}, set()

    birth = Event('I', creates=('b',))
    a = Event('DA', ('I',), deletes=('b',))
    b = Event('DB', ('I',), deletes=('b',))
    prefix = [birth, a, b]
    r = doc(*prefix).restore('RA', 'DA', mode)
    yield 'q07 observed concurrent deletes', prefix + [r], {'b'}, set(), set()
    early = doc(birth, a).restore('RA', 'DA', mode)
    yield 'unseen concurrent delete', prefix + [early], set(), {('DB', 'b')}, set()
    rb = doc(*prefix).restore('RB', 'DB', mode)
    both = prefix + [r, rb]
    xa = Event('XA', ('RA', 'RB'), cancels=('RA',))
    yield 'personal redo after two restores', both + [xa], {'b'}, set(), set()
    xb = Event('XB', ('XA',), cancels=('RB',))
    yield 'both personal redos', both + [xa, xb], set(), {('DA', 'b'), ('DB', 'b')}, set()
    again = doc(*(both + [xa, xb])).restore('RA2', 'DA', mode)
    yield 'restore again after both redos', both + [xa, xb, again], {'b'}, set(), set()

    old = Event('A', creates=('a',))
    peer = Event('B', ('A',), creates=('B',))
    replacement = Event('C', ('B',), creates=('x',), deletes=('a', 'B'))
    base = [old, peer, replacement]
    victim = doc(*base).restore('RV', 'C', mode)
    yield 'q11 restore deletion portion of replacement', base + [victim], {'a', 'B', 'x'}, set(), set()
    inverse = withdraw_in(doc(*(base + [victim])).restore('UC', 'C', mode), ('x',), mode)
    cancel_victim = Event('XV', ('UC',), cancels=('RV',))
    yield 'author undo survives victim redo', base + [victim, inverse, cancel_victim], {'a', 'B'}, set(), {('UC', 'x')}
    new_delete = Event('D2', ('RV',), deletes=('B',))
    later_inverse = withdraw_in(doc(*(base + [victim, new_delete])).restore('UC', 'C', mode), ('x',), mode)
    yield 'later deletion remains through author undo', base + [victim, new_delete, later_inverse], {'a'}, {('D2', 'B')}, {('UC', 'x')}

    # Review scope control: shared b does not authorize restoring unrelated c.
    abc = Event('I', creates=('a', 'b', 'c'))
    da = Event('DA', ('I',), deletes=('a', 'b'))
    db = Event('DB', ('I',), deletes=('b', 'c'))
    restore = doc(abc, da, db).restore('R', 'DA', mode)
    yield 'overlap restoration stays in selected scope', [abc, da, db, restore], {'a', 'b'}, {('DB', 'c')}, set()


def admission_checks():
    i = Event('I', creates=('a',), author='A')
    d = Event('D', ('I',), deletes=('a',))
    r = doc(i, d).restore('R', 'D')
    withdrawal = Event('W', ('I',), withdraws=('a',), author='A')
    view = doc(i, d, r, withdrawal)
    invalid = [
        Event('missing', ('ghost',)),
        Event('I', creates=('different',)),
        Event('unseen', releases=(('D', 'a'),)),
        Event('unknown-release', releases=(('ghost', 'a'),)),
        Event('wrong-atom', ('D',), releases=(('D', 'other'),)),
        Event('unknown-cancel', cancels=('ghost',)),
        Event('unseen-cancel', cancels=('R',)),
        Event('cancel-nontoken', ('D',), cancels=('D',)),
        Event('unknown-creation', ('I',), withdraws=('ghost',)),
        Event('unseen-creation', withdraws=('a',)),
        Event('unseen-reactivation', author='A', reactivates=(('W','a'),)),
        Event('unknown-reactivation', ('W',), author='A', reactivates=(('ghost','a'),)),
        Event('wrong-reactivation-atom', ('W',), author='A', reactivates=(('W','other'),)),
        Event('peer-reactivation', ('W',), author='B', reactivates=(('W','a'),)),
    ]
    before = dict(view.events)
    for event in invalid:
        try:
            view.put(event)
        except ModelError:
            pass
        else:
            raise RuntimeError('invalid model reference was accepted: ' + event.id)
        if view.events != before:
            raise RuntimeError('rejection changed event dictionary')
    print(f'{len(invalid)} invalid-reference cases reject without publication')


def withdrawal_authority_checks():
    # Named authors and both mixed-target orders: legacy author="" cannot expose this.
    from sessions import Session
    a,b=Session('A'),Session('B')
    paste=a.edit(creates=('p','q')); b.receive(paste)
    own=b.edit(creates=('b',)); a.receive(own)
    p,q=paste.creates; bb=own.creates[0]
    cases=[('foreign', (p,)), ('mixed-own-first', (bb,p)),
           ('mixed-foreign-first', (p,bb))]
    for cold in (False,True):
        for label, targets in cases:
            view=b.doc.copy() if cold else b.doc
            before=dict(view.events); visible=view.visible()
            forged=Event('B:forged-'+label, after=tuple(view.events),
                         author='B', withdraws=targets)
            try: view.put(forged)
            except ModelError: pass
            else: raise AssertionError('peer withdrawal of '+label+' must reject')
            if view.events != before or view.visible() != visible:
                raise AssertionError('rejected peer withdrawal changed document')
            restored=view.copy()
            if restored.events != before or restored.visible() != visible:
                raise AssertionError('rejected peer withdrawal changed cold reconstruction')
    # Same targets, genuine creator: partial withdrawal and owner cancellation
    # remain valid and reconstruct through the same admission path.
    view=b.doc.copy()
    withdrawal=Event('A:scoped', after=tuple(view.events), author='A', withdraws=(p,))
    view.put(withdrawal); view.put(withdrawal)
    if view.visible() != {q,bb} or view.copy().visible() != {q,bb}:
        raise AssertionError('creator scoped withdrawal must work')
    cancel=Event('A:cancel', after=tuple(view.events), author='A', cancels=(withdrawal.id,))
    view.put(cancel)
    if view.visible() != {p,q,bb} or view.copy().visible() != {p,q,bb}:
        raise AssertionError('creator withdrawal cancellation must work')
    owner=b.undo(); a.receive(owner)
    if owner.withdraws != own.creates or a.doc.visible() != set(paste.creates):
        raise AssertionError('session owner withdrawal must work')
    redo=b.redo(); a.receive(redo)
    if a.doc.visible() != b.doc.visible() or b.doc.visible() != {p,q,bb}:
        raise AssertionError('session owner redo must work')
    print('6 named-author foreign/mixed withdrawals reject unchanged; creator scope/cancel/session paths succeed')


def cancel_authority_checks():
    # Actual named sessions: empty-author legacy fixtures cannot test this guard.
    from sessions import Session
    a,b=Session('A'),Session('B')
    paste=a.edit(creates=('p','q')); b.receive(paste)
    withdrawal=a.undo(); b.receive(withdrawal)
    def reject_peer(view, token, label):
        before=dict(view.events)
        forged=Event('B:forged-'+label, after=tuple(view.events),
                     author='B', cancels=(token,))
        try: view.put(forged)
        except ModelError: pass
        else: raise AssertionError('peer cancellation of '+label+' must reject')
        if view.events != before:
            raise AssertionError('rejected peer cancel changed document')
    reject_peer(b.doc,withdrawal.id,'withdrawal')
    # The owner's ordinary redo still cancels her own withdrawal.
    redone=a.redo(); b.receive(redone)
    if a.doc.visible()!=set(paste.creates) or b.doc.visible()!=a.doc.visible():
        raise AssertionError('same-author withdrawal cancellation must work')
    a,b=Session('A'),Session('B')
    paste=a.edit(creates=('p','q')); b.receive(paste)
    deletion=b.edit(deletes=(paste.creates[0],)); a.receive(deletion)
    withdrawal=a.undo(); b.receive(withdrawal)
    restoration=a.restore(deletion.id,redo_policy='keep'); b.receive(restoration)
    reject_peer(b.doc,restoration.id,'Restore')
    # Restore includes both release and reactivation facets; own Undo retracts both.
    retracted=a.undo(); b.receive(retracted)
    if retracted.cancels!=(restoration.id,) or a.doc.visible() or b.doc.visible():
        raise AssertionError('same-author Restore cancellation must work')
    print('2 named-session peer cancellations reject unchanged; both owner cancellations succeed')


def run(mode):
    assert mode in ('parallel', 'target-only', 'all-known', 'legacy-hide', 'spill', 'split-undo')
    # Same frozen mask can arise from either local target; no extra wire target ID.
    i = Event('I', creates=('b',))
    a = Event('DA', ('I',), deletes=('b',))
    b = Event('DB', ('I',), deletes=('b',))
    view = doc(i, a, b)
    assert view.restore('R', 'DA') == view.restore('R', 'DB')
    admission_checks()
    cancel_authority_checks()
    withdrawal_authority_checks()
    total = 0
    count = 0
    for name, events, visible, active, withdrawals in cases(mode):
        try:
            forbidden = {frozenset({'p', 'x'})} if name.startswith(('creator ', 'peer deletion redo')) else frozenset()
            n = replay(events, visible, active, withdrawals, forbidden)
        except AssertionError as error:
            raise AssertionError(name) from error
        print(f'{name}: {n} schedules; visible={sorted(visible)}; live deletion atoms={sorted(active)}; withdrawals={sorted(withdrawals)}')
        total += n
        count += 1
    print(f'{total} legal schedules across {count} directed fixtures')


if __name__ == '__main__':
    import sys
    mode=sys.argv[1] if len(sys.argv)>1 else 'parallel'
    if mode in ('peer-withdrawal','first-withdrawal-only'):
        import inspect, textwrap
        from model import Doc
        source=textwrap.dedent(inspect.getsource(Doc.put))
        needle='if any(event.author != births[elem] for elem in event.withdraws):'
        if needle not in source:
            raise RuntimeError('withdrawal authority mutation site missing')
        wrong=('if False:' if mode=='peer-withdrawal' else
               'if any(event.author != births[elem] for elem in event.withdraws[:1]):')
        namespace=dict(ModelError=ModelError)
        exec(source.replace(needle,wrong),namespace)
        Doc.put=namespace['put']
        withdrawal_authority_checks()
    elif mode in ('peer-cancel','peer-cancel-restore'):
        import inspect, textwrap
        from model import Doc
        wrong = ('if False:' if mode=='peer-cancel' else
                 'if event.author != source.author and not source.releases:')
        source=textwrap.dedent(inspect.getsource(Doc.put)).replace(
            'if event.author != source.author:', wrong)
        namespace=dict(ModelError=ModelError)
        exec(source,namespace)
        Doc.put=namespace['put']
        cancel_authority_checks()
    else:
        run(mode)
