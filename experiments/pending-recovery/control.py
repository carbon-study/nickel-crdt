import contextlib
import io
import runpy
import sys
import types
from pathlib import Path
path=Path(__file__).with_name('inbox.py')
text=path.read_text()
mode=sys.argv[2] if len(sys.argv)>2 else 'drop-pending'
if mode=='drop-pending':
    text=text.replace('self.held[key]=entry', "pass # wrong: falsely report pending without retaining the fact")
    expected='retained facts missing'
elif mode=='ack-pending':
    text=text.replace("if key not in self.held or self.held[key]['kind']!='invalid':", 'if key not in self.held:')
    expected='pending acknowledgement accepted'
elif mode=='promote-profile':
    text=text.replace('if type(limits) is not Limits:', 'if False:')
    expected='non-dense promotion accepted'
elif mode=='resume-bound':
    text=text.replace("if len(out.held)>out.slots or sum(len(encode(e['packet']).encode()) for e in out.held.values())>out.staged_bytes:", 'if False:')
    expected='over-bound resume accepted'
else:
    raise ValueError(mode)
module=types.ModuleType('inbox');module.__file__=str(path);sys.modules['inbox']=module
exec(compile(text,str(path),'exec'),module.__dict__)
try:
    with contextlib.redirect_stdout(io.StringIO()):
        runpy.run_path(str(path.with_name('check.py')),run_name='__main__')
except AssertionError as error:
    if str(error)!=expected: raise
    print(mode+' mutation rejected: '+expected)
else:
    raise AssertionError(mode+' mutation unexpectedly passed')
