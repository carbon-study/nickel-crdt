"""Bounded warm/cold transition comparison, not an independent undo oracle."""
from collections import deque
from copy import deepcopy
from dataclasses import asdict
import json
import sys
from model import ModelError
from sessions import Session


def synced(*sessions):
    events = {k: e for s in sessions for k, e in s.doc.events.items()}
    for s in sessions:
        while len(s.doc.events) < len(events):
            ready = sorted(k for k, e in events.items()
                           if k not in s.doc.events and set(e.after) <= s.doc.events.keys())
            if not ready:
                raise RuntimeError('generated transport has no causal continuation')
            for k in ready:
                s.receive(events[k])


def seeds():
    yield 'empty', [Session('A'), Session('B')]
    a, b = Session('A'), Session('B')
    a.edit(creates=('b',)); b.edit(creates=('z',)); synced(a, b)
    b.edit(deletes=('b',)); synced(a, b)
    yield 'synced-victim-and-older-item', [a, b]
    a, b = Session('A'), Session('B')
    a.edit(creates=('b',)); synced(a, b)
    a.edit(deletes=('b',)); b.edit(deletes=('b',))
    yield 'partitioned-independent-deletes', [a, b]
    a, b = Session('A'), Session('B')
    a.edit(creates=('a',)); b.edit(creates=('B',)); synced(a, b)
    a.edit(creates=('x',), deletes=('a', 'B')); synced(a, b)
    yield 'synced-replacement', [a, b]


def facts(s):
    return [asdict(s.doc.events[k]) for k in sorted(s.doc.events)]


def observation(peers):
    return [dict(facts=facts(s), visible=sorted(s.doc.visible()), next_undo=s.next_undo())
            for s in peers]


def key(peers):
    return json.dumps(dict(observed=observation(peers), private=[json.loads(s.checkpoint())
        for s in peers]), sort_keys=True)


def actions(peers):
    union = {k: e for s in peers for k, e in s.doc.events.items()}
    for i, s in enumerate(peers):
        for op in ('undo', 'redo', 'clear'):
            yield dict(peer=i, op=op)
        # At most two creation-bearing events per writer, including seed events.
        births = sum(bool(e.creates) for e in s.doc.events.values() if e.author == s.writer)
        policies = ('keep', 'clear') if s.redos else ('keep',)
        visible = sorted(s.doc.visible())
        if births < 2:
            for policy in policies:
                yield dict(peer=i, op='edit', creates=[f'{s.writer}-elem-{s.counter}'],
                           deletes=[], policy=policy)
                if visible:
                    yield dict(peer=i, op='edit', creates=[f'{s.writer}-elem-{s.counter}'],
                               deletes=visible, policy=policy)
        for elem in visible:
            for policy in policies:
                yield dict(peer=i, op='edit', creates=[], deletes=[elem], policy=policy)
        for k in sorted(union):
            if k not in s.doc.events and set(union[k].after) <= s.doc.events.keys():
                yield dict(peer=i, op='receive', event=k)
            elif k in s.doc.events and union[k].author != s.writer:
                yield dict(peer=i, op='duplicate', event=k)


def apply(peers, action):
    s = peers[action['peer']]
    op = action['op']
    if op in ('receive', 'duplicate'):
        event = next(p.doc.events[action['event']] for p in peers if action['event'] in p.doc.events)
        private = s.checkpoint()
        s.receive(event)
        if s.checkpoint() != private:
            raise AssertionError('receive changed private session')
        return None
    if op == 'clear':
        before = facts(s)
        s.clear_history()
        if facts(s) != before:
            raise AssertionError('clear changed replicated facts')
        return None
    if op == 'edit':
        result = s.edit(action['creates'], action['deletes'], action['policy'])
    else:
        result = getattr(s, op)()
    return asdict(result) if result else None


def cold(peers, subset, mutation):
    result = deepcopy(peers)  # Warm comparator does not use the codec under test.
    for i in subset:
        original = peers[i]
        result[i] = Session.resume(original.checkpoint(), original.doc.copy())
        if mutation == 'drop-redo':
            result[i].redos.clear()
        elif mutation == 'drop-ignored':
            result[i].ignored_victims.clear()
        elif mutation == 'reset-counter':
            result[i].counter = 1
    return result


def outcome(peers, action):
    try:
        returned = apply(peers, action)
        return dict(status='completed', returned=returned, after=observation(peers))
    except ModelError as e:
        return dict(status='rejected', reason=str(e), after=observation(peers))


class Mismatch(Exception):
    def __init__(self, report):
        self.report = report


def explore(depth=3, mutation=None):
    counts = dict(states=0, edges=0, cold_comparisons=0, sync_checks=0, restart_prefixes=0)
    by_seed = {}
    covered = set()
    for name, initial in seeds():
        queue = deque([(initial, [])])
        seen = {key(initial)}
        local_states = local_edges = 0
        while queue:
            peers, prefix = queue.popleft()
            counts['states'] += 1; local_states += 1
            if counts['states'] > 10000:
                raise RuntimeError('state budget exceeded; this is not a passing bounded run')
            # Both peers see the same completed event union, with private lists untouched.
            joined = deepcopy(peers)
            private = [s.checkpoint() for s in joined]
            synced(*joined)
            if facts(joined[0]) != facts(joined[1]) or joined[0].doc.visible() != joined[1].doc.visible():
                raise AssertionError('generated causal sync did not converge')
            if private != [s.checkpoint() for s in joined]:
                raise AssertionError('sync changed private history')
            counts['sync_checks'] += 1
            if len(prefix) == depth:
                continue
            counts['restart_prefixes'] += 1
            for action in actions(peers):
                warm = deepcopy(peers)
                expected = outcome(warm, action)
                if expected['status'] != 'completed':
                    raise RuntimeError('generator emitted an invalid warm action: '+str(action))
                counts['edges'] += 1; local_edges += 1
                covered.add(action['op'])
                for subset in ((0,), (1,), (0, 1)):
                    resumed = cold(peers, subset, mutation)
                    actual = outcome(resumed, action)
                    counts['cold_comparisons'] += 1
                    if expected != actual:
                        raise Mismatch(dict(status='cold continuation mismatch', seed=name,
                            mutation=mutation, prefix=prefix, action=action, resumed=list(subset),
                            expected=expected, actual=actual))
                k = key(warm)
                if k not in seen:
                    seen.add(k); queue.append((warm, prefix+[action]))
        by_seed[name] = dict(states=local_states, edges=local_edges)
    if covered != {'undo', 'redo', 'clear', 'edit', 'receive', 'duplicate'}:
        raise AssertionError('action vocabulary not covered')
    return dict(status='bounded comparisons passed', depth=depth, seeds=by_seed,
        creation_events_per_writer=2, state_budget=10000,
        restart_prefix_depth_max=depth-1, transport_sync_depth_max=depth, **counts,
        boundary='one-step warm/cold observable comparisons at generated reachable prefixes; not an independent undo oracle')


if __name__ == '__main__':
    mutation = sys.argv[1] if len(sys.argv) > 1 else None
    if mutation not in (None, 'drop-redo', 'drop-ignored', 'reset-counter'):
        raise SystemExit('unknown mutation')
    try:
        report = explore(mutation=mutation)
    except Mismatch as e:
        print(json.dumps(e.report, sort_keys=True, indent=2))
        raise SystemExit(1)
    print(json.dumps(report, sort_keys=True, indent=2))
