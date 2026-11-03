"""Two separate Python processes, with a temporary checkpoint between them."""
import json
import sys
from dataclasses import asdict
from pathlib import Path
from inbox import Inbox
from admission import Oracle, Limits
from sessions import Session

with Oracle() as oracle:
    if sys.argv[1]=='save':
        inbox=Inbox(oracle,Limits(events=1))
        for writer,scalar in [('Alice','a'),('Bo','b')]:
            event=Session(writer).edit((scalar,))
            inbox.offer(dict(event=asdict(event),gap=0))
        assert inbox.store.text()=='a' and set(inbox.held)=={'Bo:1'}
        Path(sys.argv[2]).write_text(inbox.checkpoint())
    elif sys.argv[1]=='resume':
        inbox=Inbox.resume(Path(sys.argv[2]).read_text(),oracle)
        before=inbox.store.text(); pending=sorted(inbox.held)
        assert before=='a' and pending==['Bo:1']
        inbox.promote(Limits())
        assert inbox.store.text()=='ab' and not inbox.held
        assert set(inbox.store.state[2])=={'Alice:1','Bo:1'}
        print(json.dumps(dict(before=before,pending=pending,after=inbox.store.text()),sort_keys=True))
    else:
        raise ValueError('expected save or resume')
