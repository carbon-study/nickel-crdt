"""Candidate private-session transitions over the identity-set reference model.

One event per ordinary item; no clocks, accounts, grouping, positions or registers.
Writer tags are trusted metadata, not authentication. This is not Nickel's API.
"""
from dataclasses import asdict, dataclass, replace
import json
from model import Doc, Event, ModelError


@dataclass(frozen=True)
class Undo:
    kind: str
    source: str
    event: str


class Session:
    def __init__(self, writer, document=None, skip_policy='retain'):
        if skip_policy not in ('retain', 'consume'):
            raise ModelError('unknown skip policy')
        self.doc = document if document is not None else Doc()
        if not writer or any(e.author == writer for e in self.doc.events.values()):
            raise ModelError('new session needs a fresh writer; use resume for a saved one')
        self.writer = writer
        self.counter = 1
        self.items = []
        self.undone = set()
        self.redos = []
        self.ignored_victims = set()
        self.skip_policy = skip_policy

    def _publish(self, event):
        out = replace(event, id=f'{self.writer}:{self.counter}', author=self.writer,
                      after=tuple(sorted(self.doc.events)))
        self.doc.put(out)
        self.counter += 1
        return out

    def edit(self, creates=(), deletes=(), redo_policy=None):
        creates, deletes = tuple(creates), tuple(deletes)
        if not creates and not deletes:
            return None
        if redo_policy not in (None, 'keep', 'clear'):
            raise ModelError('unknown redo policy')
        if self.redos and redo_policy is None:
            raise ModelError('new work with pending redo requires keep or clear')
        births = {e for event in self.doc.events.values() for e in event.creates}
        if len(set(creates)) != len(creates) or set(creates) & births:
            raise ModelError('creation IDs must be fresh')
        if not set(deletes) <= self.doc.visible():
            raise ModelError('ordinary edits delete only visible identities in this profile')
        event = self._publish(Event('', creates=creates, deletes=deletes))
        self.items.append(event.id)
        if redo_policy == 'clear':
            self.redos.clear()
        return event

    def _own_eligible(self, source):
        if source in self.undone:
            return False
        event = self.doc.events[source]
        withdrawn = {e for _, e in self.doc.live_withdrawals()}
        return bool(set(event.creates) - withdrawn or
                    {(source, e) for e in event.deletes} & self.doc.live_atoms())

    def next_undo(self):
        candidates = [('own', key) for key in self.items if self._own_eligible(key)]
        mine = {e for event in self.doc.events.values() if event.author == self.writer
                for e in event.creates}
        withdrawn = {e for _, e in self.doc.live_withdrawals()}
        for key, event in self.doc.events.items():
            if event.author == self.writer or key in self.ignored_victims:
                continue
            if any(e in mine - withdrawn and (key, e) in self.doc.live_atoms()
                   for e in event.deletes):
                candidates.append(('victim', key))
        # Causal descendants take precedence. Concurrent ties favor own items,
        # then the model's string IDs. This is not a text-order primitive.
        maximal = [c for c in candidates
                   if not any(self.doc.before(c[1], other[1]) for other in candidates)]
        return min(maximal, key=lambda c: (c[0] != 'own', c[1])) if maximal else None

    def undo(self):
        if self.skip_policy == 'consume':  # Negative-control alternative only.
            self.items = [key for key in self.items
                          if key in self.undone or self._own_eligible(key)]
        chosen = self.next_undo()
        if chosen is None:
            return None
        kind, source = chosen
        original = self.doc.events[source]
        effect = self.doc.restore('', source) if original.deletes else Event('')
        if kind == 'own':
            effect = replace(effect, withdraws=original.creates)
        out = self._publish(effect)
        if kind == 'own':
            self.undone.add(source)
        self.redos.append(Undo(kind, source, out.id))
        return out

    def redo(self):
        if not self.redos:
            return None
        entry = self.redos[-1]
        out = self._publish(Event('', cancels=(entry.event,)))
        self.redos.pop()
        if entry.kind == 'own':
            self.undone.remove(entry.source)
        return out

    def receive(self, event):
        # No imported item enters the private lists; no receiving-side selection.
        self.doc.put(event)

    def clear_history(self):
        self.items.clear()
        self.undone.clear()
        self.redos.clear()
        self.ignored_victims = set(self.doc.events)

    def checkpoint(self):
        return json.dumps(dict(format='hybrid-private-session-1', writer=self.writer,
            counter=self.counter, items=self.items, undone=sorted(self.undone),
            redos=[asdict(e) for e in self.redos], ignored=sorted(self.ignored_victims),
            skip_policy=self.skip_policy), sort_keys=True)

    @classmethod
    def resume(cls, raw, document):
        # A small trusted-shape checkpoint codec, not hostile-input admission.
        x = json.loads(raw)
        if x['format'] != 'hybrid-private-session-1' or x['counter'] < 1:
            raise ModelError('unsupported checkpoint')
        items, undone = list(x['items']), set(x['undone'])
        redos = [Undo(**e) for e in x['redos']]
        if len(set(items)) != len(items) or not undone <= set(items):
            raise ModelError('invalid private item state')
        for key in items:
            if key not in document.events or document.events[key].author != x['writer']:
                raise ModelError('missing/foreign private item')
        for e in redos:
            if e.kind not in ('own', 'victim') or e.source not in document.events:
                raise ModelError('invalid redo source')
            if e.event not in document.events or document.events[e.event].author != x['writer']:
                raise ModelError('missing/foreign undo event')
            if e.kind == 'own' and e.source not in undone:
                raise ModelError('redo of a non-undone own item')
        if f"{x['writer']}:{x['counter']}" in document.events:
            raise ModelError('stale writer continuation')
        result = object.__new__(cls)
        result.doc, result.writer, result.counter = document, x['writer'], x['counter']
        result.items, result.undone, result.redos = items, undone, redos
        result.ignored_victims, result.skip_policy = set(x['ignored']), x['skip_policy']
        return result
