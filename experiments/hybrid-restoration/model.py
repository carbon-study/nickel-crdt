"""Directed reference candidate, not the Nickel engine or session algorithm."""
from dataclasses import dataclass, asdict
import json


class ModelError(ValueError):
    """Invalid reference in the trusted-shape model event vocabulary."""


@dataclass(frozen=True)
class Event:
    id: str
    after: tuple = ()
    creates: tuple = ()
    deletes: tuple = ()
    withdraws: tuple = ()  # Creator-undo effects, distinct from ordinary deletions.
    releases: tuple = ()
    cancels: tuple = ()
    payloads: tuple = ()  # (library occurrence ID, scalar value); directed legacy fixtures omit it.
    author: str = ""  # Trusted writer tag for the restricted session profile.


class Doc:
    def __init__(self):
        self.events = {}

    def ancestors(self, roots):
        todo = list(roots)
        seen = set()
        while todo:
            key = todo.pop()
            if key not in seen:
                seen.add(key)
                todo.extend(self.events[key].after)
        return seen

    def put(self, event):
        # All checks precede the one event-dictionary publication.
        if event.id in self.events:
            if self.events[event.id] != event:
                raise ModelError('conflicting event ID')
            return
        if not set(event.after) <= self.events.keys():
            raise ModelError('missing prerequisite')
        past = self.ancestors(event.after)
        existing = {elem for old in self.events.values() for elem in old.creates}
        if len(set(event.creates)) != len(event.creates) or set(event.creates) & existing:
            raise ModelError('conflicting occurrence birth')
        if event.payloads and (tuple(k for k, _ in event.payloads) != event.creates or
            any(not isinstance(v, str) or len(v) != 1 or 0xD800 <= ord(v) <= 0xDFFF
                for _, v in event.payloads)):
            raise ModelError('invalid scalar payloads')
        for deletion, elem in event.releases:
            if deletion not in past or elem not in self.events[deletion].deletes:
                raise ModelError('release must name an ancestral deletion atom')
        for token in event.cancels:
            if token not in past:
                raise ModelError('cancellation must name an ancestral token')
            source = self.events[token]
            if not (source.releases or source.withdraws):
                raise ModelError('only restoration/withdrawal tokens can be cancelled')
        births = {elem for key in past for elem in self.events[key].creates}
        if not set(event.withdraws) <= births:
            raise ModelError('withdrawal must name an ancestral creation')
        self.events[event.id] = event

    def before(self, a, b):
        return a in self.ancestors(self.events[b].after)

    def atoms(self):
        return {(event.id, elem) for event in self.events.values() for elem in event.deletes}

    def live_atoms(self):
        cancelled = {r for event in self.events.values() for r in event.cancels}
        released = {pair for event in self.events.values() if event.id not in cancelled
                    for pair in event.releases}
        return self.atoms() - released

    def live_withdrawals(self):
        cancelled = {r for event in self.events.values() for r in event.cancels}
        return {(event.id, elem) for event in self.events.values()
                if event.id not in cancelled for elem in event.withdraws}

    def visible(self):
        created = {e for event in self.events.values() for e in event.creates}
        return created - {e for _, e in self.live_atoms() | self.live_withdrawals()}

    def restore(self, name, target, mode='parallel'):
        """Author freezes mask from its supplied view. No receiver recomputation.

        Scope = full deletion effect of target (not its insertion effects).
        Cancel target + observed concurrent removal atoms on that scope.
        Other scope policies and authorization remain unselected.
        """
        scope = set(self.events[target].deletes)
        def included(other):
            if mode == 'target-only':
                return other == target
            if mode == 'all-known':
                return True
            return other == target or not (self.before(other, target) or self.before(target, other))
        mask = tuple(sorted((d, e) for d, e in self.atoms() if (e in scope or mode == 'spill') and included(d)))
        return Event(name, tuple(sorted(self.events)), releases=mask)

    def copy(self):
        # Experimental full-log codec. Reconstruction uses ordinary put in causal order.
        raw = json.dumps([asdict(e) for e in self.events.values()], sort_keys=True)
        events = []
        for row in json.loads(raw):
            row['releases'] = tuple(tuple(p) for p in row['releases'])
            row['payloads'] = tuple(tuple(p) for p in row['payloads'])
            for k in ('after', 'creates', 'deletes', 'withdraws', 'cancels'):
                row[k] = tuple(row[k])
            events.append(Event(**row))
        result = Doc()
        pending = list(reversed(events))
        while pending:
            ready = next((e for e in pending if set(e.after) <= result.events.keys()), None)
            assert ready is not None
            result.put(ready)
            pending.remove(ready)
        return result


def doc(*events):
    d = Doc()
    for e in events:
        d.put(e)
    return d


def schedules(events, known=frozenset()):
    if not events:
        yield ()
    for e in events:
        if set(e.after) <= known:
            for tail in schedules(tuple(x for x in events if x != e), known | {e.id}):
                yield (e,) + tail


def replay(events, expected, expected_live, expected_withdrawals=frozenset(), forbidden_visible=frozenset()):
    count = 0
    for order in schedules(tuple(events)):
        d = Doc()
        for i, e in enumerate(order):
            d.put(e)
            assert frozenset(d.visible()) not in forbidden_visible, 'half-published compound undo'
            d.put(e)
            cold = d.copy()
            assert cold.events == d.events
            assert cold.visible() == d.visible()
            assert frozenset(cold.visible()) not in forbidden_visible, 'half-published compound undo'
            assert cold.live_atoms() == d.live_atoms()
            assert cold.live_withdrawals() == d.live_withdrawals()
            for later in order[i + 1:]:
                cold.put(later)
            assert cold.visible() == expected
            assert cold.live_atoms() == expected_live
            assert cold.live_withdrawals() == expected_withdrawals
        for e in reversed(order):
            d.put(e)
        assert d.visible() == expected
        assert d.live_atoms() == expected_live
        assert d.live_withdrawals() == expected_withdrawals
        count += 1
    assert count
    return count
