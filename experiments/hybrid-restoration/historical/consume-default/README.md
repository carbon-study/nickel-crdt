# superseded consume-default evidence

These are the previously published session trace/output and the failing retain
control from the consume-default profile. They are historical evidence, not
expected outputs for today's selected retain default. The failure's assertion
that a bypassed deletion must stay consumed was deliberately superseded by
Ren's retain decision; it was not repaired by changing the interpreter to satisfy
that old assertion.

`session_check.py legacy-consume` still exercises the explicit consume profile,
including checkpoint continuation and its original seven-event outcome. Saved
format-3 checkpoints carry their own `skip_policy`; resume does not reinterpret
an old consume session as retain. No checkpoint migration is supplied. New
sessions default to retain, and `session_check.py consume` now fails the new
retained-access assertion. The ordinary blocked-Redo controls are unchanged.
