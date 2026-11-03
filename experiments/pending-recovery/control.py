import contextlib
import io
import runpy
import sys
import types
from pathlib import Path
path=Path(__file__).with_name('inbox.py')
text=path.read_text().replace('self.held[key]=entry', "pass # wrong: falsely report pending without retaining the fact")
module=types.ModuleType('inbox');module.__file__=str(path);sys.modules['inbox']=module
exec(compile(text,str(path),'exec'),module.__dict__)
try:
    with contextlib.redirect_stdout(io.StringIO()):
        runpy.run_path(str(path.with_name('check.py')),run_name='__main__')
except AssertionError as error:
    if str(error)!='retained facts missing': raise
    print('drop-pending mutation rejected: retained facts missing')
else:
    raise AssertionError('drop-pending mutation unexpectedly passed')
