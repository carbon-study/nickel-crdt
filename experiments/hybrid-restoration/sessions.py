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


@dataclass(frozen=True)
class Blocked:
    operation: str
    reason: str
    source: str
    token: str = ''


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
        self.restore_tokens = {}

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

    @staticmethod
    def _local_rank(key):
        return int(key.rsplit(':', 1)[1])

    def _item_rank(self, source):
        kind = 'restore' if source in self.restore_tokens else 'own'
        return self._local_rank(self.selection_stamps.get((kind, source), source))

    def restoration_choices(self):
        # Display suggestions only: never part of ordinary undo selection.
        births = [e for e in self.doc.events.values() if e.author == self.writer and e.creates]
        choices = []
        for source, event in self.doc.events.items():
            if event.author == self.writer or source in self.ignored_victims:
                continue
            anchors = [e.id for e in births if set(e.creates).intersection(event.deletes)]
            if anchors and any((source, elem) in self.doc.live_atoms() for elem in event.deletes):
                anchor = max(anchors, key=self._item_rank)
                choices.append((source, anchor))
        return sorted(choices, key=lambda pair: (-self._item_rank(pair[1]), pair[0]))

    def _preview_changes(self, effect):
        trial = self.doc.copy()
        trial.put(replace(effect, id=f'{self.writer}:{self.counter}', author=self.writer,
                          after=tuple(sorted(self.doc.events))))
        return trial.visible() != self.doc.visible()

    def restore(self, source, redo_policy=None):
        if redo_policy not in (None, 'keep', 'clear'):
            raise ModelError('unknown redo policy')
        if source not in {key for key, _ in self.restoration_choices()}:
            raise ModelError('restore needs a known offered foreign deletion')
        effect = self.doc.restore('', source)
        # Explicit Restore may re-enable ONLY this author's own occurrences in
        # the selected deletion's scope, not the rest of a withdrawn paste.
        scope = set(self.doc.events[source].deletes)
        mine = {elem for event in self.doc.events.values() if event.author == self.writer
                for elem in event.creates}
        reactivates = tuple(sorted((token, elem) for token, elem in self.doc.live_withdrawals()
                                   if elem in scope & mine and self.doc.events[token].author == self.writer))
        effect = replace(effect, reactivates=reactivates)
        if not self._preview_changes(effect):
            return Blocked('restore', 'unchanged-visible-identities', source)
        if self.redos and redo_policy is None:
            raise ModelError('new work with pending redo requires keep or clear')
        out = self._publish(effect)
        self.items.append(out.id)
        self.restore_tokens[out.id] = out.id
        if redo_policy == 'clear':
            self.redos.clear()
        return out

    def _selection(self):
        candidates = [key for key in self.items if key not in self.undone]
        skipped = []
        while candidates:
            source = max(candidates, key=self._item_rank)
            kind = 'restore' if source in self.restore_tokens else 'own'
            if kind == 'restore' or self._own_eligible(source):
                return (kind, source), skipped
            skipped.append(source)
            candidates.remove(source)
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
        if kind == 'restore':
            effect = Event('', cancels=(self.restore_tokens[source],))
        else:
            effect = self.doc.restore('', source) if original.deletes else Event('')
            effect = replace(effect, withdraws=original.creates)
        out = self._publish(effect)
        self.undone.add(source)
        self.redos.append(Undo(kind, source, out.id))
        return out

    def redo(self):
        if not self.redos:
            return None
        entry = self.redos[-1]
        # Restore redo creates a fresh token with the ORIGINAL frozen mask.
        # It cannot cancel a cancellation, or re-evaluate against new deletions.
        if entry.kind == 'restore':
            effect = Event('', releases=self.doc.events[entry.source].releases,
                           reactivates=self.doc.events[entry.source].reactivates)
        else:
            effect = Event('', cancels=(entry.event,))
        if not self._preview_changes(effect):
            return Blocked('redo', 'unchanged-visible-identities', entry.source, entry.event)
        out = self._publish(effect)
        self.redos.pop()
        self.selection_stamps[(entry.kind, entry.source)] = out.id
        if entry.kind == 'restore':
            self.restore_tokens[entry.source] = out.id
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
        self.restore_tokens.clear()
        self.ignored_victims = set(self.doc.events)

    def private_state(self):
        return dict(writer=self.writer, counter=self.counter, items=list(self.items),
            undone=sorted(self.undone), redos=[asdict(e) for e in self.redos],
            restore_tokens=dict(sorted(self.restore_tokens.items())),
            ignored=sorted(self.ignored_victims), skip_policy=self.skip_policy,
            selection_stamps=[[*key, value] for key, value in sorted(self.selection_stamps.items())])

    @staticmethod
    def _event_encoding(event):
        return json.dumps(asdict(event), sort_keys=True, separators=(',', ':'))

    def checkpoint(self):
        # Exact event encodings are a reference basis, not a compact production codec.
        return json.dumps(dict(format='hybrid-private-session-3', **self.private_state(),
            basis={k: self._event_encoding(e) for k, e in self.doc.events.items()}), sort_keys=True)

    @classmethod
    def resume(cls, raw, document):
        # A small trusted-shape checkpoint codec, not hostile-input admission.
        x = json.loads(raw)
        if x['format'] != 'hybrid-private-session-3' or x['counter'] < 1:
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
            if e.kind not in ('own', 'restore') or e.source not in document.events:
                raise ModelError('invalid redo source')
            if e.event not in document.events or document.events[e.event].author != x['writer']:
                raise ModelError('missing/foreign undo event')
            if e.source not in undone:
                raise ModelError('redo of a non-undone own item')
        if f"{x['writer']}:{x['counter']}" in document.events:
            raise ModelError('stale writer continuation')
        result = object.__new__(cls)
        result.doc, result.writer, result.counter = document, x['writer'], x['counter']
        result.items, result.undone, result.redos = items, undone, redos
        result.ignored_victims, result.skip_policy = set(x['ignored']), x['skip_policy']
        result.restore_tokens = dict(x['restore_tokens'])
        expected_restores = {key for key in items if document.events[key].releases}
        if set(result.restore_tokens) != expected_restores:
            raise ModelError('missing/extra private Restore token tracking')
        for source, token in result.restore_tokens.items():
            if source not in items or token not in document.events:
                raise ModelError('missing restore source/token')
            initial, active = document.events[source], document.events[token]
            if (not initial.releases or initial.releases != active.releases or
                initial.reactivates != active.reactivates or active.author != result.writer):
                raise ModelError('invalid restore token')
        for entry in redos:
            if (entry.kind == 'restore') != (entry.source in result.restore_tokens):
                raise ModelError('redo kind does not match source')
        result.selection_stamps = {(kind, source): stamp for kind, source, stamp in x['selection_stamps']}
        for (kind, source), stamp in result.selection_stamps.items():
            if kind not in ('own', 'restore') or source not in document.events or stamp not in document.events:
                raise ModelError('invalid selection stamp')
            if document.events[stamp].author != result.writer:
                raise ModelError('foreign selection stamp')
        return result
