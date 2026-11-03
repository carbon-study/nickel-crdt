"""Restricted combined admission research; trusted writer tags, no byte decoder/auth."""
import json
import os
import subprocess
import selectors
import time
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'hybrid-restoration'))
from model import Doc, Event, ModelError

class Rejected(ValueError):
    pass

@dataclass(frozen=True)
class Limits:
    events: int = 128
    births: int = 512
    packet_bytes: int = 8192
    scalars_per_edit: int = 64
    dependencies: int = 64
    expanded_digits: int = 4096

class Oracle:
    def __enter__(self):
        self.process = subprocess.Popen([os.environ['NODE'], str(Path(__file__).with_name('oracle.mjs'))],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE)
        return self

    def ask(self, events, visible):
        try:
            self.process.stdin.write((json.dumps(dict(events=events, visible=visible))+'\n').encode())
            self.process.stdin.flush()
        except BrokenPipeError as error:
            raise Rejected('order oracle stopped') from error
        deadline=time.monotonic()+5
        line=b''
        with selectors.DefaultSelector() as ready:
            ready.register(self.process.stdout, selectors.EVENT_READ)
            while not line.endswith(b'\n'):
                if not ready.select(timeout=max(0,deadline-time.monotonic())):
                    self.process.kill()
                    self.process.wait()
                    raise Rejected('order oracle deadline')
                chunk=os.read(self.process.stdout.fileno(),4096)
                if not chunk:
                    raise Rejected('order oracle stopped')
                line+=chunk
                if len(line)>65536:
                    self.process.kill()
                    self.process.wait()
                    raise Rejected('order oracle response budget')
        result = json.loads(line)
        if not result['ok']:
            raise Rejected('order: '+result['error'])
        return result

    def __exit__(self, *args):
        try:
            self.process.stdin.close()
        except BrokenPipeError:
            pass
        try:
            self.process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            self.process.kill()
            self.process.wait()
        self.process.stdout.close()

WRITERS = {'Alice': 0, 'Bo': 1, 'Cam': 2}

def encode(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True)

def unpack(raw):
    # The input here is parsed trusted-shape data, not arbitrary bytes.
    expected = set(Event.__dataclass_fields__)
    if type(raw) is not dict or set(raw) != expected:
        raise Rejected('event fields')
    fields = dict(raw)
    for k in expected-{'id', 'author'}:
        if type(fields[k]) not in (list, tuple):
            raise Rejected('event sequence')
        fields[k] = tuple(tuple(x) if type(x) in (list,tuple) else x for x in fields[k])
    for k in ('after','creates','deletes','withdraws','cancels'):
        if any(type(x) is not str for x in fields[k]):
            raise Rejected('event reference shape')
    for k in ('payloads','releases','reactivates'):
        if any(type(x) is not tuple or len(x)!=2 or any(type(v) is not str for v in x) for x in fields[k]):
            raise Rejected('event pair shape')
    return Event(**fields)

class Combined:
    def __init__(self, oracle, limits=Limits()):
        self.oracle, self.limits = oracle, limits
        # One state pointer: neither plane is published before every check passes.
        self.state = (Doc(), {}, {})  # effect document, placement records, exact packets

    def snapshot(self):
        doc, order, packets = self.state
        return encode(dict(events={k:asdict(v) for k,v in doc.events.items()},order=order,packets=packets))

    def put(self, packet):
        if type(packet) is not dict or set(packet) != {'event','gap'}:
            raise Rejected('packet fields')
        if len(encode(packet).encode()) > self.limits.packet_bytes:
            raise Rejected('packet byte budget')
        event = unpack(packet['event'])
        doc, order, packets = self.state
        if type(event.id) is not str or type(event.author) is not str or event.author not in WRITERS:
            raise Rejected('named writer required')
        prefix = event.author+':'
        suffix = event.id[len(prefix):] if event.id.startswith(prefix) else ''
        if not suffix.isascii() or not suffix.isdecimal() or suffix.startswith('0'):
            raise Rejected('event ID/writer mismatch')
        if len(suffix) > 16:
            raise Rejected('counter bound')
        counter = int(suffix)
        if not 0 < counter <= 2**53-1:
            raise Rejected('counter bound')
        if event.id in packets:
            if encode(packet) != encode(packets[event.id]):
                raise Rejected('conflicting combined duplicate')
            return False
        if len(doc.events) >= self.limits.events:
            raise Rejected('event budget')
        if len(event.after) > self.limits.dependencies or len(set(event.after)) != len(event.after):
            raise Rejected('dependency budget/duplicate')
        if not set(event.after) <= doc.events.keys():
            raise Rejected('missing prerequisite')
        past = doc.ancestors(event.after)
        if counter > 1 and f'{event.author}:{counter-1}' not in past:
            raise Rejected('missing writer predecessor')
        if any(e.author == event.author and int(e.id.rsplit(':',1)[1]) >= counter for e in (doc.events[k] for k in past)):
            raise Rejected('writer counter order')
        if len(event.creates) > self.limits.scalars_per_edit:
            raise Rejected('scalar budget')
        if sum(len(e.creates) for e in doc.events.values())+len(event.creates) > self.limits.births:
            raise Rejected('birth budget')
        canonical = tuple(json.dumps([event.author,counter,i],separators=(',',':')) for i in range(len(event.creates)))
        if event.creates != canonical or tuple(k for k,_ in event.payloads) != canonical:
            raise Rejected('birth/payload identity mismatch')
        # Reconstruct the author's causal effect view, NEVER receiver-current visibility.
        basis = Doc()
        for k,e in doc.events.items():
            if k in past:
                basis.put(e)
        if not set(event.deletes) <= basis.visible():
            raise Rejected('delete outside author-visible births')
        if len(set(event.deletes)) != len(event.deletes):
            raise Rejected('duplicate deletion target')
        trial = doc.copy()
        try:
            trial.put(event)
        except ModelError as error:
            raise Rejected(str(error)) from error
        candidate = dict(order)
        if event.creates:
            if type(packet['gap']) is not int or not 0 <= packet['gap'] <= len(basis.visible()):
                raise Rejected('author gap')
            def occurrence_id(identity):
                writer,n,index = json.loads(identity)
                return f'{WRITERS[writer]}:{n}/{index}'
            candidate[event.id] = dict(writer=WRITERS[event.author], counter=counter,
                text=''.join(value for _,value in event.payloads),
                basis=sorted(f'{WRITERS[doc.events[k].author]}:{int(k.rsplit(":",1)[1])}' for k in past if doc.events[k].creates),
                visible=sorted(occurrence_id(x) for x in basis.visible()), gap=packet['gap'])
        elif packet['gap'] is not None:
            raise Rejected('placement without birth')
        visible=[]
        for identity in trial.visible():
            writer,n,index=json.loads(identity)
            visible.append(f'{WRITERS[writer]}:{n}/{index}')
        result=self.oracle.ask(list(candidate.values()), sorted(visible))
        if result['digits'] > self.limits.expanded_digits:
            raise Rejected('expanded digit budget')
        new_packets=dict(packets)
        new_packets[event.id]=json.loads(encode(packet))
        self.state=(trial,candidate,new_packets)
        return True

    def text(self):
        doc,order,_=self.state
        visible=[]
        for identity in doc.visible():
            writer,n,index=json.loads(identity)
            visible.append(f'{WRITERS[writer]}:{n}/{index}')
        return self.oracle.ask(list(order.values()),visible)['text']
