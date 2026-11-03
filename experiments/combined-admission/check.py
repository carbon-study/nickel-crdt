import copy
import json
import sys
from dataclasses import asdict
from admission import Combined, Limits, Oracle, Rejected
from sessions import Session

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
def reject(store, p, reason):
    before=store.snapshot()
    try:
        store.put(p)
    except Rejected as error:
        assert reason in str(error), (reason,str(error))
        assert store.snapshot()==before, 'rejection partially published'
        rejections.append(reason)
    else:
        raise AssertionError('invalid packet accepted: '+reason)

with Oracle() as oracle:
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
        (Limits(expanded_digits=1),'expanded digit budget'),
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

    # Publication happens after the external ordering boundary too.
    class BrokenOracle:
        def ask(self,*args): raise Rejected('injected order failure')
    broken=Combined(BrokenOracle())
    reject(broken,packet(root,gaps),'injected order failure')
    with Oracle() as stopped:
        stopped.process.kill()
        stopped.process.wait()
        reject(Combined(stopped),packet(root,gaps),'order oracle stopped')

print(json.dumps(dict(histories=len(traces),views=sum(len(s['views']) for t in traces for s in t['steps']),
    rejections=rejections,finals=finals,
    receiver_last_gap=dict(orders=len(receivers),text=last_gap_text,same_state=True)),indent=2,sort_keys=True))
