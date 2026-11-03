import copy
import json
import sys
from dataclasses import asdict
from inbox import Inbox, Backpressure
from admission import Oracle, Limits, Rejected, Event, encode

traces=json.load(open(sys.argv[1]))['traces']
counts=dict(views=0,checkpoints=0)

def packet(event,gaps):
    return dict(event=event,gap=gaps[event['id']] if event['creates'] else None)

def roundtrip(inbox,oracle):
    cold=Inbox.resume(inbox.checkpoint(),oracle)
    assert cold.snapshot()==inbox.snapshot(),'pending cold mismatch'
    counts['checkpoints']+=1
    return cold

def raises_unchanged(inbox,action,kind):
    before=inbox.snapshot()
    try: action()
    except kind: assert inbox.snapshot()==before,'failed offer changed state'
    else: raise AssertionError('expected '+kind.__name__)

with Oracle() as oracle:
    for trace in traces:
        gaps={i['event']:i['gap'] for i in trace['insertions']}
        for step in trace['steps']:
            for view in step['views'].values():
                inbox=Inbox(oracle,Limits(events=1))
                for event in reversed(view['facts']):
                    inbox.offer(packet(event,gaps))
                    inbox=roundtrip(inbox,oracle)
                all_ids={e['id'] for e in view['facts']}
                assert set(inbox.held)|set(inbox.store.state[2])==all_ids,'retained facts missing'
                inbox.promote(Limits())
                assert not inbox.held, 'ready facts stranded'
                assert inbox.store.text()==view['expected'],'resumed render mismatch'
                counts['views']+=1

    def birth(writer,scalar):
        identity=json.dumps([writer,1,0],separators=(',',':'))
        return dict(event=asdict(Event(writer+':1',author=writer,creates=(identity,),payloads=((identity,scalar),))),gap=0)
    a,b=birth('Alice','a'),birth('Bo','b')
    replicas=[Inbox(oracle,Limits(events=1)),Inbox(oracle,Limits(events=1))]
    for inbox,first,second in [(replicas[0],a,b),(replicas[1],b,a)]:
        assert inbox.offer(first)=='accepted'
        assert inbox.offer(second)=='pending'
        assert len(inbox.held)==1,'retained facts missing'
    initial=[i.store.text() for i in replicas]
    assert initial==['a','b'],'capacity disagreement witness lost'
    for n,inbox in enumerate(replicas):
        inbox=roundtrip(inbox,oracle)
        inbox.promote(Limits())
        assert not inbox.held
        assert inbox.store.text()=='ab'
        before=inbox.snapshot()
        assert inbox.offer(a)=='accepted-duplicate'
        assert inbox.snapshot()==before
        replicas[n]=inbox

    # Bounded retention returns upstream responsibility, not success or invalidity.
    for cap in [dict(slots=0),dict(staged_bytes=0)]:
        inbox=Inbox(oracle,Limits(events=1),**cap)
        inbox.offer(a)
        raises_unchanged(inbox,lambda:inbox.offer(b),Backpressure)
        inbox.promote(Limits())
        assert inbox.offer(b)=='accepted'
        assert inbox.store.text()=='ab'

    # An actual stopped order subprocess is recoverable without re-authoring facts.
    with Oracle() as stopped:
        stopped.process.kill(); stopped.process.wait()
        inbox=Inbox(stopped)
        assert inbox.offer(a)=='pending'
        assert inbox.held['Alice:1']['kind']=='oracle'
        inbox=roundtrip(inbox,oracle)
        inbox.drain()
        assert inbox.store.text()=='a' and not inbox.held

    # Defer is not a validity verdict: a missing ancestor can reveal an invalid effect.
    bad=dict(event=asdict(Event('Bo:1',author='Bo',after=('Alice:1',),deletes=('unknown',))),gap=None)
    inbox=Inbox(oracle)
    assert inbox.offer(bad)=='pending'
    assert inbox.held['Bo:1']['kind']=='missing'
    changed=copy.deepcopy(bad); changed['gap']=0
    raises_unchanged(inbox,lambda:inbox.offer(changed),Rejected)
    inbox=roundtrip(inbox,oracle)
    inbox.offer(a)
    assert inbox.held['Bo:1']['kind']=='invalid'
    assert inbox.store.text()=='a'
    inbox=roundtrip(inbox,oracle)
    assert encode(inbox.acknowledge_invalid('Bo:1'))==encode(bad)
    assert not inbox.held

    # A pending Undo retains its original unseen-deletion mask across retry.
    unseen=next(t for t in traces if t['name']=='concurrent deletion, peer unseen')
    gaps={i['event']:i['gap'] for i in unseen['insertions']}
    facts=next(s for s in unseen['steps'] if s['label']=='both facts delivered')['views']['Alice']['facts']
    by_id={e['id']:packet(e,gaps) for e in facts}
    inbox=Inbox(oracle,Limits(events=2))
    inbox.offer(by_id['Alice:1']); inbox.offer(by_id['Alice:2'])
    inbox.offer(by_id['Bo:1']); inbox.offer(by_id['Alice:3'])
    held_undo=copy.deepcopy(inbox.held['Alice:3']['packet'])
    inbox=roundtrip(inbox,oracle)
    inbox.promote(Limits())
    assert inbox.store.state[2]['Alice:3']==held_undo,'pending mask changed on retry'
    assert inbox.store.text()==''
    raises_unchanged(inbox,lambda:inbox.promote(Limits(events=1)),Rejected)

print(json.dumps(dict(**counts,capacity_before=initial,capacity_after=['ab','ab'],
    backpressure='caller retains; later re-offer accepted',
    invalid_deferred='retained until explicit acknowledgement',
    unseen_mask='unchanged after checkpoint and capacity promotion',
    stopped_oracle='retained then admitted through fresh oracle'),indent=2,sort_keys=True))
