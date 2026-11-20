// Pull-request job skipping by derivation identity (#194). A job may skip its builds only when every
// derivation it builds is identical at the exact PR base and the exact merge head. Identical derivation
// paths mean identical declared recipes under Nix's input-addressing contract
// (https://nix.dev/manual/nix/2.34/store/derivation/outputs/input-address.html); that is the whole claim.
// It is not a proof run and not a claim of identical outcomes: a skipped job reports "not affected",
// never "passed". Every doubt runs the job. This module is pure; skip-plan-run.mjs does the I/O.

export const SYSTEM = 'aarch64-linux';
const P = (t) => `packages.${SYSTEM}.${t}`;
const C = (t) => `checks.${SYSTEM}.${t}`;

// Everything each scaffold job builds (ci.yml). skip-plan.test.mjs checks this against the workflow,
// so a build added there without its bundle member fails the self-test.
export const BUNDLES = Object.freeze({
  native: [C('native'), C('edit-reference'), C('gate-inputs')],
  'shared-native': [P('shared-native')],
  'shared-proofs': [P('shared-proofs')],
  'register-native': [P('register-native')],
  'register-proofs-shard-0': [P('register-proofs-shard-0')],
  'register-proofs-shard-1': [P('register-proofs-shard-1')],
  'register-proofs-shard-2': [P('register-proofs-shard-2')],
  'register-proofs-shard-3': [P('register-proofs-shard-3')],
  'proofs-core-a': [P('proofs-core-a'), P('register-proofs-shard-coverage')],
  'proofs-core-b': [P('proofs-core-b')],
  'proofs-shard-0': [P('proofs-shard-0')],
  'proofs-shard-1': [P('proofs-shard-1')],
  'proofs-shard-2': [P('proofs-shard-2')],
});

// A pull-request register or text shard runs the head tree's selector through a selection boundary. Those
// inputs are outside the full shard's derivation, so a change to any of them must run the boundary.
// check-gate-inputs.mjs is the selector's import parser; edit-native-plans.mjs is the text plan export.
export const SELECTION_PATHS = Object.freeze(['scripts/select-affected.mjs', 'scripts/selection-boundary.mjs',
  'scripts/register-control-plans.mjs', 'scripts/check-gate-inputs.mjs', 'scripts/gate-imports.mjs', 'scripts/text-native-code.mjs', 'scripts/edit-native-plans.mjs', 'flake.nix', 'nix/gate-scripts.json']);

// The exact resolution, recorded verbatim. stdout and stderr are kept apart. `nix path-info --derivation`
// resolves the flake output as an installable, the way `nix build` does, so an output that is not a
// buildable derivation (e.g. a bare set carrying a drvPath field) is refused here as it would be there;
// reading `.drvPath` would only look up a field (Lynn, #195 review).
export const RESOLVE_ARGS = Object.freeze(['path-info', '--derivation', '--no-write-lock-file']);
const SHA = /^[0-9a-f]{40}$/;
const DRV = /^\/nix\/store\/[0-9a-z]{32}-[^/\s]+\.drv$/;

/** One resolution result {status, stdout, stderr} -> a drv path, or why it does not count. stdout must be
 *  exactly one store path ending in .drv, optionally followed by one newline. */
export function checkEval(r) {
  if (!r || r.status !== 0) return { ok: false, why: `exit ${r ? r.status : 'none'}`, stderr: tail(r?.stderr) };
  const out = typeof r.stdout === 'string' && r.stdout.endsWith('\n') ? r.stdout.slice(0, -1) : r.stdout;
  if (typeof out !== 'string' || !DRV.test(out)) return { ok: false, why: 'stdout is not exactly one .drv store path', stdout: tail(r.stdout), stderr: tail(r.stderr) };
  return { ok: true, drv: out };
}
const tail = (s) => (typeof s === 'string' ? s.slice(-600) : null);

export const flakeRef = (repo, rev) => `git+file://${repo}?rev=${rev}&shallow=1`;

/**
 * The decision and its record. `changedPaths` is the list of paths changed between base and head
 * (both sides of a rename or deletion), or null if it could not be read. `evaluate(rev, attr)` resolves the installable and returns
 * {status, stdout, stderr}. Nothing here throws on bad input: every doubt is a "run" with its reason.
 */
export function decide({ job, event, baseSha, headSha, checkedHead, changedPaths, evaluate, repo = '.', nixVersion = null }) {
  const record = { schema: 1, job, event, base: baseSha ?? null, head: headSha ?? null, checkedHead: checkedHead ?? null,
    system: SYSTEM, nixVersion, evalCommand: ['nix', ...RESOLVE_ARGS, `${flakeRef(repo, '<rev>')}#<attr>`],
    targets: [], decision: 'run', reasons: [] };
  const run = (why) => { record.decision = 'run'; record.reasons.push(why); return record; };
  const bundle = BUNDLES[job];
  if (!bundle) return run(`unknown job ${JSON.stringify(job)}: no bundle`);
  if (event !== 'pull_request') return run(`event ${JSON.stringify(event)} is not pull_request: always full`);
  if (typeof baseSha !== 'string' || !SHA.test(baseSha)) return run('base sha missing or malformed');
  if (typeof headSha !== 'string' || !SHA.test(headSha)) return run('merge head sha missing or malformed');
  if (checkedHead !== headSha) return run('checked-out HEAD is not the merge head');
  if (!Array.isArray(changedPaths)) return run('changed paths unreadable');
  record.changedPaths = changedPaths.length;
  const github = changedPaths.filter((p) => p.startsWith('.github/'));
  if (github.length) return run(`workflow/skip machinery changed (${github.slice(0, 5).join(', ')}): always full`);
  if (job.startsWith('register-proofs-shard-') || job.startsWith('proofs-shard-')) {
    const sel = changedPaths.filter((p) => SELECTION_PATHS.includes(p));
    if (sel.length) return run(`selection machinery changed (${sel.join(', ')}): the boundary must run`);
  }
  // Every member is evaluated (no early exit), so the record shows the whole bundle.
  const differs = [];
  for (const attr of bundle) {
    let b, h;
    try { b = checkEval(evaluate(baseSha, attr)); } catch (e) { b = { ok: false, why: `evaluation threw: ${String(e).slice(0, 200)}` }; }
    try { h = checkEval(evaluate(headSha, attr)); } catch (e) { h = { ok: false, why: `evaluation threw: ${String(e).slice(0, 200)}` }; }
    record.targets.push({ attr, base: b, head: h });
    // Two failures never compare equal: only two valid drv paths can.
    if (!b.ok || !h.ok) differs.push(`${attr}: ${[!b.ok && `base ${b.why}`, !h.ok && `head ${h.why}`].filter(Boolean).join(', ')}`);
    else if (b.drv !== h.drv) differs.push(`${attr}: derivation changed`);
  }
  if (differs.length) return run(differs.join('; '));
  record.decision = 'skip';
  record.reasons.push(`not affected: all ${bundle.length} derivation(s) identical at base and merge head (identical declared recipes; no build ran, no result is claimed)`);
  return record;
}
