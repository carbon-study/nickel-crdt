from model import Event, doc, replay


def withdrawal(name, after, elements, mode):
    if mode == 'legacy-hide':
        return Event(name, after, deletes=elements)
    return Event(name, after, withdraws=elements)


def cases(mode='parallel'):
    # Review repro: Bo's undo must not resurrect a creation withdrawn by Alice.
    p = Event('I', creates=('p',))
    replace = Event('C', ('I',), creates=('x',), deletes=('p',))
    bo_delete = Event('DB', ('C',), deletes=('x',))
    inverse = doc(p, replace).restore('UC', 'C', mode)
    hide = withdrawal('UX', ('UC',), ('x',), mode)
    prefix = [p, replace, bo_delete, inverse, hide]
    restore_bo = doc(*prefix).restore('RB', 'DB', mode)
    both = prefix + [restore_bo]
    yield 'creator withdrawal survives peer deletion undo', both, {'p'}, set(), {('UX', 'x')}
    redo_a = Event('XA', ('RB',), cancels=('UC', 'UX'))
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
    inverse = doc(*(base + [victim])).restore('UC', 'C', mode)
    remove_x = withdrawal('UX', ('UC',), ('x',), mode)
    cancel_victim = Event('XV', ('UX',), cancels=('RV',))
    yield 'author undo survives victim redo', base + [victim, inverse, remove_x, cancel_victim], {'a', 'B'}, set(), {('UX', 'x')}
    new_delete = Event('D2', ('RV',), deletes=('B',))
    later_inverse = doc(*(base + [victim, new_delete])).restore('UC', 'C', mode)
    later_x = withdrawal('UX', ('UC',), ('x',), mode)
    yield 'later deletion remains through author undo', base + [victim, new_delete, later_inverse, later_x], {'a'}, {('D2', 'B')}, {('UX', 'x')}

    # Review scope control: shared b does not authorize restoring unrelated c.
    abc = Event('I', creates=('a', 'b', 'c'))
    da = Event('DA', ('I',), deletes=('a', 'b'))
    db = Event('DB', ('I',), deletes=('b', 'c'))
    restore = doc(abc, da, db).restore('R', 'DA', mode)
    yield 'overlap restoration stays in selected scope', [abc, da, db, restore], {'a', 'b'}, {('DB', 'c')}, set()


def run(mode):
    assert mode in ('parallel', 'target-only', 'all-known', 'legacy-hide', 'spill')
    # Same frozen mask can arise from either local target; no extra wire target ID.
    i = Event('I', creates=('b',))
    a = Event('DA', ('I',), deletes=('b',))
    b = Event('DB', ('I',), deletes=('b',))
    view = doc(i, a, b)
    assert view.restore('R', 'DA') == view.restore('R', 'DB')
    total = 0
    count = 0
    for name, events, visible, active, withdrawals in cases(mode):
        try:
            n = replay(events, visible, active, withdrawals)
        except AssertionError as error:
            raise AssertionError(name) from error
        print(f'{name}: {n} schedules; visible={sorted(visible)}; live deletion atoms={sorted(active)}; withdrawals={sorted(withdrawals)}')
        total += n
        count += 1
    print(f'{total} legal schedules across {count} directed fixtures')


if __name__ == '__main__':
    import sys
    run(sys.argv[1] if len(sys.argv) > 1 else 'parallel')
