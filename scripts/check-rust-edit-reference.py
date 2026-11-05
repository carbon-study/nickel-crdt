"""Compare Rust-authored structured fixtures with the reviewed Python/Node oracle.
The input is an internal test artifact, not Nickel's wire or persistence codec.
"""
import json,os,sys,itertools
from pathlib import Path
from dataclasses import asdict
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'experiments/combined-admission'))
from admission import Combined,Oracle,Event
writers=['Alice','Bo']
def eid(pair):return writers[pair[0]]+':'+str(pair[1])
def bid(parts):return json.dumps([writers[parts[0]],parts[1],parts[2]],separators=(',',':'))
def oid(parts):return f'{parts[0]}:{parts[1]}/{parts[2]}'
cases=json.load(open(sys.argv[1]));orders=0
with Oracle('fugue') as oracle:
 for case in cases:
  facts=[]
  for f in case['facts']:
   births=tuple(bid([f['writer'],f['counter'],i]) for i in range(len(f['insert'])))
   e=Event(eid([f['writer'],f['counter']]),author=writers[f['writer']],after=tuple(map(eid,f['after'])),creates=births,payloads=tuple(zip(births,map(chr,f['insert']))),deletes=tuple(map(bid,f['delete'])))
   facts.append(dict(event=asdict(e),gap=f['gap']))
  count=0
  for schedule in itertools.permutations(facts):
   seen=set()
   for p in schedule:
    if not set(p['event']['after'])<=seen:break
    seen.add(p['event']['id'])
   else:
    store=Combined(oracle)
    for p in schedule:store.put(p)
    doc,records,_=store.state
    answer=oracle.ask(list(records.values()),sorted(oid([writers.index(json.loads(x)[0]),*json.loads(x)[1:]]) for x in doc.visible()))
    assert answer['ids']==[oid(x) for x in case['whole']],(case['name'],'whole order')
    assert store.text()==''.join(map(lambda x:chr(x[3]),case['visible'])),(case['name'],'scalars')
    assert set(doc.visible())=={bid(x[:3]) for x in case['visible']},(case['name'],'visible IDs')
    count+=1
  assert count==case['orders'],case['name']
  orders+=count
print(json.dumps(dict(cases=len(cases),causal_orders=orders,reference='actual Combined/Doc + FugueMax',native_authored=True),sort_keys=True))
