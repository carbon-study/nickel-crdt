"""Directed comparison for the new creator-slot rule; not the adopted selector."""
import json
from sessions import Session
from session_check import deliver, shown


class CreationSlots(Session):
    touch_anchor = False

    def _selection(self):
        # This probe covers the supplied uncleared histories, not arbitrary sessions.
        if self.ignored_victims or any(kind == 'victim' for kind, _ in self.selection_stamps):
            raise ValueError('probe does not define cleared histories or redone victim slots')
        own = {k: e for k, e in self.doc.events.items() if e.author == self.writer}
        def rank(source):
            stamp = self.selection_stamps.get(('own', source), source)
            return int(stamp.rsplit(':', 1)[1])
        candidates = [(('own', k), (rank(k), 0)) for k in self.items if k not in self.undone]
        mine = {elem for e in own.values() for elem in e.creates}
        withdrawn = {elem for _, elem in self.doc.live_withdrawals()}
        for source, event in self.doc.events.items():
            if event.author == self.writer:
                continue
            if not any(elem in mine-withdrawn and (source, elem) in self.doc.live_atoms()
                       for elem in event.deletes):
                continue
            targets = set(event.deletes)
            anchors = [k for k, e in own.items()
                       if targets & (set(e.creates) | (set(e.deletes) if self.touch_anchor else set()))]
            candidates.append((('victim', source), (max(map(rank, anchors)), 1)))
        skipped = []
        while candidates:
            top = max(priority for _, priority in candidates)
            selected = min(c for c, priority in candidates if priority == top)
            if selected[0] == 'victim' or self._own_eligible(selected[1]):
                return selected, skipped
            skipped.append(selected[1])
            candidates = [(c, p) for c, p in candidates if c != selected]
        return None, skipped


class LatestTouchSlots(CreationSlots):
    # A possible revision to the rule, not an authorized default.
    touch_anchor = True


def redo_arrival(cls, before_redo, cold=False):
    a, b = cls('A'), cls('B')
    p = a.edit(creates=('p',)); deliver(p, b)
    original_a = a.edit(creates=('a',)); a.undo()
    deletion = b.edit(deletes=p.creates)
    if before_redo:
        deliver(deletion, a)
    redone = a.redo()
    if not before_redo:
        deliver(deletion, a)
    if cold:
        a = cls.resume(a.checkpoint(), a.doc.copy())
    start = shown(a)
    sequence = []
    for _ in range(3):
        selected = a.next_undo()
        event = a.undo()
        sequence.append(dict(selected=selected, emitted=event.id if event else None, values=shown(a)))
    return dict(deletion_received='before redo' if before_redo else 'after redo',
        cold=cold, initial=start, redone_source=original_a.id, redo_after=redone.after,
        undo_sequence=sequence)


def overlap(cls):
    a, b = cls('A'), cls('B')
    birth = a.edit(creates=tuple('abc')); deliver(birth, b)
    aa, bb, cc = birth.creates
    own_delete = a.edit(deletes=(aa, bb))
    peer_delete = b.edit(deletes=(bb, cc))
    deliver(own_delete, b); deliver(peer_delete, a)
    selected = a.next_undo(); restored = a.undo()
    return dict(creation_item=birth.id, own_delete=own_delete.id, peer_delete=peer_delete.id,
        selected=selected, released_atoms=restored.releases, actual=shown(a), requested=list('bc'))


def report():
    profiles = {}
    for cls in (Session, CreationSlots, LatestTouchSlots):
        profiles[cls.__name__] = dict(
            redo_arrival=[redo_arrival(cls, before, cold) for before in (True, False) for cold in (False, True)],
            overlap=overlap(cls))
    strict = profiles['CreationSlots']
    assert all([step['values'] for step in r['undo_sequence']] == [[], ['p'], []]
               for r in strict['redo_arrival'])
    assert strict['overlap']['actual'] == list('ab')
    assert strict['overlap']['actual'] != strict['overlap']['requested']
    assert profiles['LatestTouchSlots']['overlap']['actual'] == list('bc')
    return dict(status='decision required: strict creator placement conflicts with accepted overlap outcome',
        boundary='directed selector comparisons only; default Session unchanged', profiles=profiles)


if __name__ == '__main__':
    print(json.dumps(report(), indent=2))
    raise SystemExit(2)
