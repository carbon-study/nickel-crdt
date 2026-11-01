from model import Event, doc, replay


def cases(mode='parallel'):
    birth = Event('I', creates=('b',))
    a = Event('DA', ('I',), deletes=('b',))
    b = Event('DB', ('I',), deletes=('b',))
    prefix = [birth, a, b]
    r = doc(*prefix).restore('RA', 'DA', mode)
    yield 'q07 observed concurrent deletes', prefix + [r], {'b'}, set()
    # A restoration cannot include an operation its author has not received.
    early = doc(birth, a).restore('RA', 'DA', mode)
    yield 'unseen concurrent delete', prefix + [early], set(), {('DB', 'b')}
    rb = doc(*prefix).restore('RB', 'DB', mode)
    both = prefix + [r, rb]
    xa = Event('XA', ('RA', 'RB'), cancels=('RA',))
    yield 'personal redo after two restores', both + [xa], {'b'}, set()
    xb = Event('XB', ('XA',), cancels=('RB',))
    yield 'both personal redos', both + [xa, xb], set(), {('DA', 'b'), ('DB', 'b')}
    # New restoration token permits repeated cycles without reviving cancelled tokens.
    again = doc(*(both + [xa, xb])).restore('RA2', 'DA', mode)
    yield 'restore again after both redos', both + [xa, xb, again], {'b'}, set()

    old = Event('A', creates=('a',))
    peer = Event('B', ('A',), creates=('B',))
    replacement = Event('C', ('B',), creates=('x',), deletes=('a', 'B'))
    base = [old, peer, replacement]
    victim = doc(*base).restore('RV', 'C', mode)
    yield 'q11 restore deletion portion of replacement', base + [victim], {'a', 'B', 'x'}, set()
    # Undo C reverses its deletion even if already released, plus removes x.
    # This targets C only; it does not undo B's creation.
    inverse = doc(*(base + [victim])).restore('UC', 'C', mode)
    remove_x = Event('UX', ('UC',), deletes=('x',))
    cancel_victim = Event('XV', ('UX',), cancels=('RV',))
    yield 'author undo survives victim redo', base + [victim, inverse, remove_x, cancel_victim], {'a', 'B'}, {('UX', 'x')}
    # Distinguish concurrent deletes from a later deliberate deletion.
    new_delete = Event('D2', ('RV',), deletes=('B',))
    later_inverse = doc(*(base + [victim, new_delete])).restore('UC', 'C', mode)
    later_x = Event('UX', ('UC',), deletes=('x',))
    yield 'later deletion remains through author undo', base + [victim, new_delete, later_inverse, later_x], {'a'}, {('D2', 'B'), ('UX', 'x')}


def run(mode):
    assert mode in ('parallel', 'target-only', 'all-known')
    total = 0
    for name, events, visible, active in cases(mode):
        try:
            n = replay(events, visible, active)
        except AssertionError as error:
            raise AssertionError(name) from error
        print(f'{name}: {n} schedules; visible={sorted(visible)}; live deletion atoms={sorted(active)}')
        total += n
    print(f'{total} legal schedules across 8 directed fixtures')


if __name__ == '__main__':
    import sys
    run(sys.argv[1] if len(sys.argv) > 1 else 'parallel')
