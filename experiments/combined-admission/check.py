import copy
import json
import sys
from dataclasses import asdict
from admission import Combined, Limits as DenseLimits, FugueLimits, Oracle, Rejected, Deferred, WRITERS
from sessions import Session

backend = 'fugue' if '--fugue' in sys.argv[2:] else 'dense'
Limits = FugueLimits if backend == 'fugue' else DenseLimits
traces=json.load(open(sys.argv[1]))['traces']

def packet(event, gaps):
    return dict(event=event,gap=gaps[event['id']] if event['creates'] else None)

def replay(oracle, events, gaps, reverse=False):
    store=Combined(oracle)
    pending=list(reversed(events)) if reverse else list(events)
    while pending:
        doc=store.state[0]
        event=next(e for e in pending if set(e['after']) <= doc.events.keys())
        p=packet(event,gaps)
        store.put(p)
        before=store.snapshot()
        assert store.put(p) is False
        assert before==store.snapshot(), 'duplicate changed state'
        pending.remove(event)
    return store

rejections=[]
def reject(store, p, reason, kind=None):
    before=store.snapshot()
    try:
        store.put(p)
    except Rejected as error:
        assert reason in str(error), (reason,str(error))
        if kind is not None:
            assert isinstance(error,Deferred) and error.kind==kind,'oracle fault misclassified as invalid'
        assert store.snapshot()==before, 'rejection partially published'
        rejections.append(reason)
    else:
        raise AssertionError('invalid packet accepted: '+reason)

with Oracle(backend) as oracle:
    finals=[]
    for trace in traces:
        gaps={i['event']:i['gap'] for i in trace['insertions']}
        # End-to-end every recorded view; actual Session facts are the source.
        for step in trace['steps']:
            for writer,view in step['views'].items():
                store=replay(oracle,view['facts'],gaps)
                assert store.text()==view['expected'], (trace['name'],step['label'],writer)
                cold=replay(oracle,json.loads(json.dumps(view['facts'])),gaps,True)
                assert cold.text()==view['expected']
                assert cold.snapshot()==store.snapshot(), 'cold combined state mismatch'
        finals.append(dict(name=trace['name'],text=store.text()))

    # Alice chooses her last visible gap before seeing Bo's concurrent deletion.
    # Cam must admit it even if that deletion has already reduced Cam's view.
    alice,bo=Session('Alice'),Session('Bo')
    ab=alice.edit(tuple('ab')); bo.receive(ab)
    x=alice.edit(('X',))
    remove_b=bo.edit(deletes=(ab.creates[1],))
    gap_packets={ab.id:dict(event=asdict(ab),gap=0),
        x.id:dict(event=asdict(x),gap=2),
        remove_b.id:dict(event=asdict(remove_b),gap=None)}
    receivers=[]
    for schedule in [(ab,x,remove_b),(ab,remove_b,x)]:
        cam=Combined(oracle)
        for event in schedule:
            cam.put(gap_packets[event.id])
        assert cam.text()=='aX','receiver last-gap render mismatch'
        receivers.append(cam)
    assert receivers[0].snapshot()==receivers[1].snapshot(),'receiver gap arrival dependence'
    last_gap_text=receivers[0].text()

    prepend_receipts=[]
    if backend == 'fugue':
        # Actual two-writer Session facts, not caller-supplied visibility/bases.
        from itertools import permutations
        for swapped in (False, True):
            alice,bo=Session('Alice'),Session('Bo')
            root_event=alice.edit(tuple('ab'));bo.receive(root_event)
            left,right=(bo,alice) if swapped else (alice,bo)
            one=left.edit(('1',));two=left.edit(('2',))
            three=right.edit(('3',));four=right.edit(('4',))
            events=[asdict(e) for e in (root_event,one,two,three,four)]
            pgaps={e['id']:0 if e['id']==root_event.id else 1 for e in events}
            expected='a4321b' if swapped else 'a2143b'
            snapshots=[]
            for schedule in permutations(events):
                seen=set()
                for e in schedule:
                    if not set(e['after']) <= seen:break
                    seen.add(e['id'])
                else:
                    receiver=replay(oracle,schedule,pgaps)
                    assert receiver.text()==expected,'joint prepend order'
                    snapshots.append(receiver.snapshot())
            assert len(snapshots)==6 and len(set(snapshots))==1,'joint prepend delivery dependence'
            cold=replay(oracle,json.loads(json.dumps(events)),pgaps,True)
            assert cold.snapshot()==snapshots[0],'cold joint prepend state'
            prepend_receipts.append(dict(text=expected,orders=len(snapshots),same_state=True))

        # Actual three-writer Figure 7 facts distinguish Max from plain at the
        # joint boundary too; this is outside the proposed two-writer Rust cut.
        a,b,c=Session('Alice'),Session('Bo'),Session('Cam')
        A=a.edit(('A',));B=b.edit(('B',));C=c.edit(('C',))
        b.receive(A);c.receive(A)
        X=c.edit(('X',));Y=b.edit(('Y',))
        max_events=[asdict(e) for e in (A,B,C,X,Y)]
        max_gaps={e.id:0 if e in (A,B,C) else 1 for e in (A,B,C,X,Y)}
        max_snapshots=[]
        for schedule in permutations(max_events):
            seen=set()
            for e in schedule:
                if not set(e['after']) <= seen:break
                seen.add(e['id'])
            else:
                receiver=replay(oracle,schedule,max_gaps)
                assert receiver.text()=='AXYBC','joint Max discriminator'
                max_snapshots.append(receiver.snapshot())
        assert len(max_snapshots)==16 and len(set(max_snapshots))==1,'joint Max arrival dependence'

        # Final metric rejection cannot publish either half of a replacement.
        replacement=traces[2]
        rgaps={i['event']:i['gap'] for i in replacement['insertions']}
        rfacts=replacement['steps'][0]['views']['Alice']['facts']
        original=next(e for e in rfacts if e['creates'] and not e['deletes'])
        compound=next(e for e in rfacts if e['creates'] and e['deletes'])
        original_packet=packet(original,rgaps);compound_packet=packet(compound,rgaps)
        limited=Combined(oracle,FugueLimits(ordering_links=3*len(original['creates'])))
        limited.put(original_packet);saved=limited.snapshot();retained=copy.deepcopy(compound_packet)
        try:
            limited.put(compound_packet)
        except Deferred as error:
            assert error.kind=='resource' and str(error)=='ordering link budget'
        else:
            raise AssertionError('compound metric overflow accepted')
        assert limited.snapshot()==saved and compound_packet==retained,'rejection partially published'
        assert limited.text()=='Friday!','failed replacement deletion escaped'

        class WrongBackend:
            backend=backend
            def ask(self,*args):
                result=oracle.ask(*args);result['backend']='dense';return result
        reject(Combined(WrongBackend()),original_packet,'order backend mismatch','oracle')
        class WrongBirthCount:
            backend=backend
            def ask(self,*args):
                result=oracle.ask(*args);result['ids']=result['ids'][:-1];return result
        reject(Combined(WrongBirthCount()),original_packet,'order/effect birth count mismatch','oracle')

    # Same cardinality is not the same birth multiset, in either backend.
    identity_event=Session('Alice').edit(tuple('ab'))
    identity_packet=dict(event=asdict(identity_event),gap=0)
    for fault in ('duplicate', 'foreign'):
        class WrongBirthIdentity:
            backend=backend
            def ask(self,*args):
                result=oracle.ask(*args)
                result['ids'][-1]=result['ids'][0] if fault=='duplicate' else '999:1/0'
                return result
        store=Combined(WrongBirthIdentity());before=store.snapshot()
        try:
            store.put(identity_packet)
        except Deferred as error:
            assert error.kind=='oracle' and str(error)=='order/effect birth identity mismatch'
            assert store.snapshot()==before,'rejection partially published'
        else:
            raise AssertionError('same-count wrong identity accepted')

    first=traces[0]
    gaps={i['event']:i['gap'] for i in first['insertions']}
    facts=first['steps'][-1]['views']['Alice']['facts']
    root=next(e for e in facts if e['id']=='Alice:1')
    deletion=next(e for e in facts if e['id']=='Bo:1')
    insertion=next(e for e in facts if e['id']=='Alice:2')
    base=Combined(oracle); base.put(packet(root,gaps))
    p=copy.deepcopy(packet(deletion,gaps)); p['event']['deletes']=[deletion['deletes'][0]]*2
    reject(base,p,'duplicate deletion target')
    p=packet(insertion,gaps); reject(base,p,'missing prerequisite')
    p=copy.deepcopy(packet(deletion,gaps)); p['event']['after']=[]; reject(base,p,'delete outside author-visible births')
    p=packet(deletion,gaps); p['gap']=0; reject(base,p,'placement without birth')
    p=copy.deepcopy(packet(deletion,gaps)); p['event']['deletes']=['unknown']; reject(base,p,'delete outside author-visible births')
    p=copy.deepcopy(packet(deletion,gaps)); p['event']['author']='Cam'; reject(base,p,'event ID/writer mismatch')
    base.put(packet(deletion,gaps))
    for change,reason in [
        (lambda p:p['event'].__setitem__('creates',['wrong']), 'birth/payload identity mismatch'),
        (lambda p:p['event'].__setitem__('after',[]), 'missing writer predecessor'),
        (lambda p:p.__setitem__('gap',99), 'author gap'),
        (lambda p:p.__setitem__('gap',True), 'author gap'),
    ]:
        p=copy.deepcopy(packet(insertion,gaps)); change(p); reject(base,p,reason)
    # A compound packet cannot publish its valid birth before a bad authority effect.
    from admission import Event
    birth=json.dumps(['Bo',2,0],separators=(',',':'))
    foreign=Event('Bo:2',author='Bo',after=('Alice:1','Bo:1'),
        creates=(birth,),payloads=((birth,'Z'),),withdraws=(root['creates'][0],))
    reject(base,dict(event=asdict(foreign),gap=0),'only the creator can withdraw')
    p=copy.deepcopy(packet(insertion,gaps)); p['event']['releases']=[['Bo:1']]; reject(base,p,'event pair shape')
    p=copy.deepcopy(packet(insertion,gaps)); p['visible']=[]; reject(base,p,'packet fields')
    base.put(packet(insertion,gaps))
    p=copy.deepcopy(packet(insertion,gaps)); p['gap']=1; reject(base,p,'conflicting combined duplicate')

    # Limits are supplied experiment parameters, not adopted release budgets.
    for limits,reason in [
        (Limits(events=1),'event budget'),
        (Limits(packet_bytes=1),'packet byte budget'),
        (Limits(births=1),'birth budget'),
        (Limits(scalars_per_edit=1),'scalar budget'),
        (Limits(dependencies=0),'dependency budget'),
        ((Limits(ordering_links=1),'ordering link budget') if backend == 'fugue' else (Limits(expanded_digits=1),'expanded digit budget')),
    ]:
        limited=Combined(oracle,limits)
        if reason in ('event budget','dependency budget'):
            limited.put(packet(root,gaps))
            before=limited.snapshot()
            assert limited.put(packet(root,gaps)) is False
            assert limited.snapshot()==before
            reject(limited,packet(deletion,gaps),reason)
        else:
            reject(limited,packet(root,gaps),reason)

    # An explicit representation-specific profile cannot be silently reused.
    if backend == 'fugue':
        try:
            Combined(oracle,DenseLimits())
        except Rejected as error:
            assert str(error) == 'ordering/profile mismatch'
        else:
            raise AssertionError('legacy digit profile accepted as Fugue profile')

    if backend == 'fugue':
        from pathlib import Path
        sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'pending-recovery'))
        from inbox import Inbox
        try:
            Inbox(oracle,FugueLimits())
        except Rejected as error:
            assert str(error)=='pending checkpoint profile supports dense ordering only'
        else:
            raise AssertionError('unversioned Fugue inbox profile accepted')

    # Publication happens after the external ordering boundary too.
    class BrokenOracle:
        backend = backend
        def ask(self,*args): raise Rejected('injected order failure')
    broken=Combined(BrokenOracle())
    reject(broken,packet(root,gaps),'injected order failure')
    with Oracle(backend) as stopped:
        stopped.process.kill()
        stopped.process.wait()
        reject(Combined(stopped),packet(root,gaps),'order oracle stopped')

extra = {}
if backend == 'fugue':
    extra = dict(ordering='FugueMax',ordering_metric='three derived node link slots per retained birth',
        profile_mismatch_rejected=True,unversioned_inbox_rejected=True,prepends=prepend_receipts,
        max_discriminator=dict(text='AXYBC',orders=len(max_snapshots),same_state=True,authors=3),
        compound_deferral=dict(original='Friday!',retained_exact_packet=True,unchanged_joint_state=True))
print(json.dumps(dict(**extra,histories=len(traces),views=sum(len(s['views']) for t in traces for s in t['steps']),
    rejections=rejections,finals=finals,
    receiver_last_gap=dict(orders=len(receivers),text=last_gap_text,same_state=True)),indent=2,sort_keys=True))
