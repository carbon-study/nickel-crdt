"""Bounded in-memory retention for deferred parsed facts; not a wire/storage layer."""
import json
import sys
from dataclasses import asdict
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'combined-admission'))
from admission import Combined, Deferred, Rejected, Limits, encode

class Backpressure(Rejected):
    """This inbox did not retain the offered value; the caller must keep it."""

class Inbox:
    def __init__(self, oracle, limits=Limits(), slots=16, staged_bytes=65536):
        if getattr(oracle, 'backend', 'dense') != 'dense':
            raise Rejected('pending checkpoint profile supports dense ordering only')
        self.store=Combined(oracle,limits)
        self.slots,self.staged_bytes=slots,staged_bytes
        self.held={}

    @staticmethod
    def key(packet):
        if type(packet) is not dict or type(packet.get('event')) is not dict or type(packet['event'].get('id')) is not str:
            raise Rejected('packet needs an event ID for retention')
        return packet['event']['id']

    def checkpoint(self):
        return encode(dict(format='pending-reference-1',limits=asdict(self.store.limits),
            slots=self.slots,staged_bytes=self.staged_bytes,
            accepted=list(self.store.state[2].values()),held=self.held))

    def snapshot(self):
        return encode(dict(checkpoint=self.checkpoint(),accepted=self.store.snapshot()))

    def offer(self, packet):
        key=self.key(packet)
        if key in self.held:
            if encode(packet)!=encode(self.held[key]['packet']):
                raise Rejected('conflicting held event ID')
            return 'held-duplicate'
        # The admission reference mutates nothing on Deferred.
        try:
            accepted=self.store.put(packet)
        except Deferred as error:
            entry=dict(packet=json.loads(encode(packet)),kind=error.kind,reason=str(error))
            size=sum(len(encode(e['packet']).encode()) for e in self.held.values())+len(encode(packet).encode())
            if len(self.held)>=self.slots or size>self.staged_bytes:
                raise Backpressure('inbox full; caller retains packet')
            self.held[key]=entry
            return 'pending'
        self.drain()
        return 'accepted' if accepted else 'accepted-duplicate'

    def drain(self):
        # A pass either accepts at least one retained event or stops. Invalid
        # entries stay inspectable until explicitly acknowledged.
        while True:
            progressed=False
            for key,entry in list(self.held.items()):
                if entry['kind']=='invalid':
                    continue
                try:
                    self.store.put(entry['packet'])
                except Deferred as error:
                    entry['kind'],entry['reason']=error.kind,str(error)
                except Rejected as error:
                    entry['kind'],entry['reason']='invalid',str(error)
                else:
                    del self.held[key]
                    progressed=True
            if not progressed:
                return

    def acknowledge_invalid(self,key):
        if key not in self.held or self.held[key]['kind']!='invalid':
            raise Rejected('only an invalid entry may be acknowledged')
        return self.held.pop(key)['packet']

    def promote(self, limits):
        old=asdict(self.store.limits)
        if any(value<old[key] for key,value in asdict(limits).items()):
            raise Rejected('reference promotion cannot lower a limit')
        self.store.limits=limits
        self.drain()

    @classmethod
    def resume(cls, raw, oracle):
        # Trusted checkpoint shape, not hostile checkpoint decoding.
        saved=json.loads(raw)
        if saved['format']!='pending-reference-1':
            raise Rejected('unsupported inbox checkpoint')
        out=cls(oracle,Limits(**saved['limits']),saved['slots'],saved['staged_bytes'])
        for packet in saved['accepted']:
            out.store.put(packet)
        out.held=saved['held']
        if len(out.held)>out.slots or sum(len(encode(e['packet']).encode()) for e in out.held.values())>out.staged_bytes:
            raise Rejected('checkpoint retention bound')
        return out
