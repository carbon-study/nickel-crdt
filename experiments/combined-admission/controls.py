"""Scratch source mutations; no variant flag enters the admission implementation."""
import contextlib
import io
import runpy
import sys
import types
from pathlib import Path
source=Path(__file__).with_name('admission.py')
mode=sys.argv[2]
text=source.read_text()
if mode=='receiver-visible-delete':
    text=text.replace('if not set(event.deletes) <= basis.visible():', 'if not set(event.deletes) <= doc.visible():')
    expected='delete outside author-visible births'
elif mode=='early-publish':
    text=text.replace('result=self.oracle.ask(list(candidate.values()), sorted(visible))',
        'self.state=(trial,candidate,packets)\n        result=self.oracle.ask(list(candidate.values()), sorted(visible))')
    expected='rejection partially published'
elif mode=='receiver-visible-gap':
    text=text.replace("packet['gap'] <= len(basis.visible())", "packet['gap'] <= len(doc.visible())")
    expected='author gap'
elif mode=='duplicate-delete-target':
    text=text.replace('if len(set(event.deletes)) != len(event.deletes):', 'if False:')
    expected='invalid packet accepted: duplicate deletion target'
elif mode=='fugue-link-budget':
    text=text.replace("elif result['links'] > self.limits.ordering_links:", 'elif False:')
    expected='compound metric overflow accepted'
elif mode=='order-backend':
    text=text.replace("if result.get('backend') != self.backend:", 'if False:')
    expected='invalid packet accepted: order backend mismatch'
elif mode=='order-birth-count':
    text=text.replace("if len(result['ids']) != sum(len(e.creates) for e in trial.events.values()):", 'if False:')
    expected='invalid packet accepted: order/effect birth count mismatch'
else:
    raise ValueError(mode)
module=types.ModuleType('admission'); module.__file__=str(source)
sys.modules['admission']=module
exec(compile(text,str(source),'exec'),module.__dict__)
sys.argv = [str(source.with_name('check.py')), sys.argv[1]] + (['--fugue'] if '--fugue' in sys.argv[3:] else [])
try:
    with contextlib.redirect_stdout(io.StringIO()):
        runpy.run_path(str(source.with_name('check.py')),run_name='__main__')
except (AssertionError,module.Rejected) as error:
    if expected not in str(error): raise
    print(mode+': rejected by unchanged check: '+expected)
else:
    raise AssertionError('mutation unexpectedly passed')
