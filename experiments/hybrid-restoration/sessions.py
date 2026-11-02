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
    def __init__(self, writer, document=None, skip_policy='consume'):
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
        self.selection_stamps = {}

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
        if any(type(v) is not str or len(v) != 1 or 0xD800 <= ord(v) <= 0xDFFF for v in creates):
            raise ModelError('insertions must be Unicode scalars')
        identities = tuple(self._created_identity(i, value) for i, value in enumerate(creates))
        if not set(deletes) <= self.doc.visible():
            raise ModelError('ordinary edits delete only visible identities in this profile')
        event = self._publish(Event('', creates=identities, deletes=deletes,
                                    payloads=tuple(zip(identities, creates))))
        self.items.append(event.id)
        if redo_policy == 'clear':
            self.redos.clear()
        return event

    def _created_identity(self, index, value):
        # Values never determine identity; the caller supplies no occurrence ID.
        return json.dumps([self.writer, self.counter, index], separators=(',', ':'))

    def _own_eligible(self, source):
        if source in self.undone:
            return False
        event = self.doc.events[source]
        withdrawn = {e for _, e in self.doc.live_withdrawals()}
        return bool(set(event.creates) - withdrawn or
                    {(source, e) for e in event.deletes} & self.doc.live_atoms())

    def _selection(self):
        candidates = [('own', key) for key in self.items if key not in self.undone]
        mine = {e for event in self.doc.events.values() if event.author == self.writer
                for e in event.creates}
        withdrawn = {e for _, e in self.doc.live_withdrawals()}
        for key, event in self.doc.events.items():
            if event.author == self.writer or key in self.ignored_victims:
                continue
            if any(e in mine - withdrawn and (key, e) in self.doc.live_atoms()
                   for e in event.deletes):
                candidates.append(('victim', key))
        # Foreign receipt never establishes recency. Anchor a deletion above
        # the newest local creation it touches, including forgotten creations.
        # A successful local redo is an explicit new selection occurrence.
        def local_rank(key):
            return int(key.rsplit(':', 1)[1])
        def priority(candidate):
            kind, source = candidate
            stamp = self.selection_stamps.get(candidate)
            if stamp is not None:
                return local_rank(stamp), 1 if kind == 'victim' else 0
            if kind == 'own':
                return local_rank(source), 0
            targets = set(self.doc.events[source].deletes)
            anchors = [e.id for e in self.doc.events.values()
                       if e.author == self.writer and targets.intersection(e.creates)]
            newest = max(anchors, key=local_rank)
            anchor_stamp = self.selection_stamps.get(('own', newest), newest)
            return local_rank(anchor_stamp), 1
        skipped = []
        while candidates:
            top = max(map(priority, candidates))
            chosen = min(c for c in candidates if priority(c) == top)
            if chosen[0] == 'victim' or self._own_eligible(chosen[1]):
                return chosen, skipped
            skipped.append(chosen[1])
            candidates.remove(chosen)
        return None, skipped

    def next_undo(self):
        return self._selection()[0]

    def undo(self):
        chosen, skipped = self._selection()
        if chosen is None:
            return None
        if self.skip_policy == 'consume':
            self.items = [key for key in self.items if key not in skipped]
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
        effect = Event('', cancels=(entry.event,))
        trial = self.doc.copy()
        trial.put(replace(effect, id=f'{self.writer}:{self.counter}', author=self.writer,
                          after=tuple(sorted(self.doc.events))))
        if trial.visible() == self.doc.visible():
            return None
        out = self._publish(effect)
        self.redos.pop()
        self.selection_stamps[(entry.kind, entry.source)] = out.id
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
        self.selection_stamps.clear()
        self.ignored_victims = set(self.doc.events)

    def private_state(self):
        return dict(writer=self.writer, counter=self.counter, items=list(self.items),
            undone=sorted(self.undone), redos=[asdict(e) for e in self.redos],
            ignored=sorted(self.ignored_victims), skip_policy=self.skip_policy,
            selection_stamps=[[*key, value] for key, value in sorted(self.selection_stamps.items())])

    @staticmethod
    def _event_encoding(event):
        return json.dumps(asdict(event), sort_keys=True, separators=(',', ':'))

    def checkpoint(self):
        # Exact event encodings are a reference basis, not a compact production codec.
        return json.dumps(dict(format='hybrid-private-session-2', **self.private_state(),
            basis={k: self._event_encoding(e) for k, e in self.doc.events.items()}), sort_keys=True)

    @classmethod
    def resume(cls, raw, document):
        # A small trusted-shape checkpoint codec, not hostile-input admission.
        x = json.loads(raw)
        if x['format'] != 'hybrid-private-session-2' or x['counter'] < 1:
            raise ModelError('unsupported checkpoint')
        for key, encoded in x['basis'].items():
            if key not in document.events or cls._event_encoding(document.events[key]) != encoded:
                raise ModelError('incompatible document/history basis')
        if any(e.author == x['writer'] and key not in x['basis'] for key, e in document.events.items()):
            raise ModelError('document has later same-writer activity')
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
        result.selection_stamps = {(kind, source): stamp for kind, source, stamp in x['selection_stamps']}
        for (kind, source), stamp in result.selection_stamps.items():
            if kind not in ('own', 'victim') or source not in document.events or stamp not in document.events:
                raise ModelError('invalid selection stamp')
            if document.events[stamp].author != result.writer:
                raise ModelError('foreign selection stamp')
        return result
