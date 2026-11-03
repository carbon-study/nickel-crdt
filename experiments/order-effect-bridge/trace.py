"""Exercise the existing Session; export its actual birth/effect facts, not a second undo model."""
import json
import os
import sys
from dataclasses import asdict
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'hybrid-restoration'))
from sessions import Session

WRITERS = {'Alice': 0, 'Bo': 1, 'Cam': 2}

class Sessions(dict):
    def __getitem__(self, writer):
        session = super().__getitem__(writer)
        if os.environ.get('BRIDGE_COLD') == '1':
            session = Session.resume(session.checkpoint(), session.doc.copy())
            self[writer] = session
        return session

class Trace:
    def __init__(self, name):
        self.name = name
        # Explicit research profile, not a change to Session's consume default.
        self.sessions = Sessions({w: Session(w, skip_policy='retain') for w in WRITERS})
        self.insertions = {}
        self.steps = []

    def sync(self):
        facts = {k: e for s in self.sessions.values() for k, e in s.doc.events.items()}
        for s in self.sessions.values():
            pending = [e for k, e in facts.items() if k not in s.doc.events]
            while pending:
                e = next(e for e in pending if set(e.after) <= s.doc.events.keys())
                s.receive(e)
                pending.remove(e)

    def edit(self, writer, text='', deletes=(), gap=0, redo_policy=None):
        s = self.sessions[writer]
        before = sorted(s.doc.visible())
        event = s.edit(tuple(text), deletes, redo_policy)
        if event.creates:
            self.insertions[event.id] = dict(event=event.id, writer=WRITERS[writer],
                counter=int(event.id.rsplit(':', 1)[1]), text=text,
                basis=sorted(k for k in s.doc.ancestors(event.after)
                             if s.doc.events[k].creates),
                visible=before, gap=gap, creates=list(event.creates))
        return event

    def step(self, label, expected):
        views = {}
        for writer, text in expected.items():
            s = self.sessions[writer]
            # Real JSON cold reconstruction plus the actual private resume validator.
            cold = Session.resume(s.checkpoint(), s.doc.copy())
            assert cold.checkpoint() == s.checkpoint(), 'private cold mismatch'
            assert cold.doc.visible() == s.doc.visible(), 'effect cold mismatch'
            views[writer] = dict(facts=[asdict(e) for _, e in sorted(s.doc.events.items())],
                visible=sorted(s.doc.visible()), expected=text)
        self.steps.append(dict(label=label, views=views))

    def out(self):
        return dict(name=self.name, insertions=list(self.insertions.values()), steps=self.steps)

traces = []
# Hidden a remains an ordered birth when Restore makes it visible again.
t = Trace('Xab with real explicit Restore')
ab = t.edit('Alice', 'ab'); t.sync()
t.edit('Bo', deletes=(ab.creates[0],)); t.sync()
t.edit('Alice', 'X', gap=0); t.sync(); t.step('hidden a', {'Alice': 'Xb', 'Bo': 'Xb'})
preview = t.sessions['Alice'].inspect_restore('Bo:1')
assert {o.identity for o in preview.restored} == {ab.creates[0]}
t.sessions['Alice'].confirm_restore(preview); t.sync(); t.step('confirm Restore', {'Alice': 'Xab', 'Bo': 'Xab'})
t.sessions['Alice'].undo(); t.sync(); t.step('Undo Restore', {'Alice': 'Xb', 'Bo': 'Xb'})
t.sessions['Alice'].redo(); t.sync(); t.step('fresh-token Redo Restore', {'Alice': 'Xab', 'Bo': 'Xab'})
traces.append(t.out())

# A real withdrawal, rather than a hand-supplied hidden set, forces whole-gap placement.
t = Trace('hidden X through creator Undo and Redo')
t.edit('Bo', 'ab'); t.sync()
x = t.edit('Alice', 'X', gap=1); t.sync()
t.sessions['Alice'].undo(); t.sync(); t.step('withdraw X', {'Alice': 'ab', 'Bo': 'ab'})
t.edit('Bo', 'Y', gap=1); t.sync(); t.step('Y before hidden X', {'Alice': 'aYb', 'Bo': 'aYb'})
t.sessions['Alice'].redo(); t.sync(); t.step('reactivate original X', {'Alice': 'aYXb', 'Bo': 'aYXb'})
traces.append(t.out())

# One real edit publishes creation and deletion together; Restore does not undo its creation.
t = Trace('replacement and frozen Restore continuation')
f = t.edit('Alice', 'Friday!'); t.sync()
m = t.edit('Bo', 'Monday', deletes=f.creates[:-1], gap=0); t.sync()
t.step('compound replacement', {'Alice': 'Monday!', 'Bo': 'Monday!'})
t.sessions['Alice'].restore(m.id); t.sync()
t.step('Restore leaves replacement', {'Alice': 'MondayFriday!', 'Bo': 'MondayFriday!'})
t.sessions['Alice'].undo(); t.sync(); t.step('Undo Restore', {'Alice': 'Monday!', 'Bo': 'Monday!'})
t.sessions['Alice'].redo(); t.sync(); t.step('Redo Restore', {'Alice': 'MondayFriday!', 'Bo': 'MondayFriday!'})
traces.append(t.out())

# Independent text keeps its birth position while both neighbours are withdrawn.
t = Trace('peer insertion survives creator withdrawal')
t.edit('Alice', 'ab'); t.sync(); t.edit('Bo', 'X', gap=1); t.sync()
t.sessions['Alice'].undo(); t.sync(); t.step('withdraw neighbours', {'Alice': 'X', 'Bo': 'X'})
t.sessions['Alice'].redo(); t.sync(); t.step('same neighbours return', {'Alice': 'aXb', 'Bo': 'aXb'})
traces.append(t.out())

# Concurrent insertion runs use actual effect histories and author-visible bases.
t = Trace('concurrent scalar runs and personal withdrawal')
t.edit('Cam', 'ab'); t.sync()
t.edit('Alice', 'X🦊', gap=1)
t.edit('Bo', 'Pe\u0301', gap=1)
t.sync(); t.step('both concurrent runs', {'Alice': 'aX🦊Pe\u0301b', 'Bo': 'aX🦊Pe\u0301b'})
t.sessions['Alice'].undo(); t.sync(); t.step('only Alice withdraws', {'Alice': 'aPe\u0301b', 'Bo': 'aPe\u0301b'})
t.sessions['Alice'].redo(); t.sync(); t.step('exact scalar identities return', {'Alice': 'aX🦊Pe\u0301b', 'Bo': 'aX🦊Pe\u0301b'})
traces.append(t.out())

# Same named Undo, but different observed deletion masks. No receiver re-selection.
for observed in (False, True):
    t = Trace('concurrent deletion, peer ' + ('observed' if observed else 'unseen'))
    b = t.edit('Alice', 'b'); t.sync()
    t.edit('Alice', deletes=b.creates)
    t.edit('Bo', deletes=b.creates)
    if observed: t.sync()
    t.sessions['Alice'].undo()
    t.step('author press', {'Alice': 'b'})
    t.sync()
    result = 'b' if observed else ''
    t.step('both facts delivered', {'Alice': result, 'Bo': result})
    if not observed:
        t.sessions['Alice'].restore('Bo:1', redo_policy='keep'); t.sync()
        t.step('explicit Restore after unseen arrival', {'Alice': 'b', 'Bo': 'b'})
    traces.append(t.out())

# The approved retain witness, explicitly opted in without rewriting the old oracle.
t = Trace('retained skipped deletion becomes eligible again')
b = t.edit('Alice', 'b'); t.sync()
t.edit('Bo', 'z', gap=1); t.edit('Bo', deletes=b.creates); t.sync()
t.sessions['Alice'].restore('Bo:2'); t.sync()
t.sessions['Bo'].undo(); t.sync(); t.step('skip deletion and undo z', {'Alice': 'b', 'Bo': 'b'})
t.sessions['Alice'].undo(); t.sync(); t.step('Undo Restore', {'Alice': '', 'Bo': ''})
assert t.sessions['Bo'].next_undo() == ('own', 'Bo:2')
t.sessions['Bo'].undo(); t.sync(); t.step('retained deletion Undo', {'Alice': 'b', 'Bo': 'b'})
traces.append(t.out())
print(json.dumps(dict(format='order-effect-bridge-1', traces=traces), indent=2, sort_keys=True))
