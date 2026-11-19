// Controls for skip-plan.mjs (#194). Runs in well under a second; CI runs it in every scaffold job
// before the plan. Every doubt must run the job; only a complete bundle of identical, valid drv paths skips.
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { BUNDLES, SELECTION_PATHS, SYSTEM, checkEval, decide } from './skip-plan.mjs';

const B = 'b'.repeat(40), H = 'c'.repeat(40);
const drv = (n) => `/nix/store/${n.padEnd(32, '0').slice(0, 32)}-x.drv`;
const ok = (stdout) => ({ status: 0, stdout, stderr: '' });
// Same valid drv at both revisions unless overridden per revision and attribute.
const evaluator = (over = {}) => (rev, attr) => over[`${rev === B ? 'base' : 'head'}:${attr}`] ?? ok(drv(attr.replace(/[^a-z0-9]/g, '')));
const pr = (o = {}) => decide({ job: 'native', event: 'pull_request', baseSha: B, headSha: H, checkedHead: H, changedPaths: ['src/lib.rs'], evaluate: evaluator(), ...o });
const runs = (r, re) => { assert.equal(r.decision, 'run', JSON.stringify(r.reasons)); if (re) assert.match(r.reasons.join(' | '), re); };
let n = 0; const t = (name, f) => { f(); n++; };

t('identical complete bundle skips, with every member recorded', () => {
  for (const job of Object.keys(BUNDLES)) {
    const r = pr({ job });
    assert.equal(r.decision, 'skip', job); assert.equal(r.targets.length, BUNDLES[job].length);
    assert.match(r.reasons[0], /not affected/); assert.doesNotMatch(r.reasons[0], /passed/);
  }
});
t("Lynn's missed-check: native.drv identical but edit-reference changed -> native runs", () => {
  const r = pr({ evaluate: evaluator({ [`head:checks.${SYSTEM}.edit-reference`]: ok(drv('changed')) }) });
  runs(r, /edit-reference: derivation changed/);
  assert.equal(r.targets.length, 3, 'every bundle member is evaluated and recorded');
  assert.equal(r.targets[0].base.drv, r.targets[0].head.drv, 'native itself identical');
});
t('core-a: a changed coverage derivation runs the job', () => {
  runs(pr({ job: 'proofs-core-a', evaluate: evaluator({ [`base:packages.${SYSTEM}.register-proofs-shard-coverage`]: ok(drv('old')) }) }), /register-proofs-shard-coverage: derivation changed/);
});
t('two failed evaluations never compare equal, even with identical stderr', () => {
  const fail = { status: 1, stdout: '', stderr: 'error: same message' };
  runs(pr({ evaluate: () => fail }), /base exit 1, head exit 1/);
});
t('base failure, head failure, thrown evaluation', () => {
  runs(pr({ evaluate: evaluator({ [`base:checks.${SYSTEM}.native`]: { status: 1, stdout: drv('x'), stderr: '' } }) }), /base exit 1/);
  runs(pr({ evaluate: evaluator({ [`head:checks.${SYSTEM}.native`]: { status: 1, stdout: drv('x'), stderr: '' } }) }), /head exit 1/);
  runs(pr({ evaluate: () => { throw new Error('spawn'); } }), /evaluation threw/);
});
t('malformed stdout is never a drv path', () => {
  for (const s of [drv('x') + '\n', `${drv('x')}\n${drv('y')}`, '/nix/store/short-x.drv', `${drv('x')}.extra`, '', 'warning: x', '/tmp/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa-x.drv']) {
    assert.equal(checkEval(ok(s)).ok, false, JSON.stringify(s));
    runs(pr({ evaluate: () => ok(s) }), /not exactly one .drv store path/);
  }
  assert.equal(checkEval(ok(drv('x'))).ok, true);
});
t('identity of the run: event, shas, checked-out head, changed paths', () => {
  runs(pr({ event: 'push' }), /always full/);
  for (const baseSha of [undefined, '', 'B'.repeat(40), 'b'.repeat(39), 'b'.repeat(41)]) runs(pr({ baseSha }), /base sha missing or malformed/);
  runs(pr({ headSha: 'xyz' }), /merge head sha missing or malformed/);
  runs(pr({ checkedHead: B }), /checked-out HEAD is not the merge head/);
  runs(pr({ checkedHead: null }), /checked-out HEAD/);
  runs(pr({ changedPaths: null }), /changed paths unreadable/);
});
t('.github changes always run, before any evaluation', () => {
  let evaluated = 0;
  runs(pr({ changedPaths: ['src/lib.rs', '.github/scripts/skip-plan.mjs'], evaluate: () => { evaluated++; return ok(drv('x')); } }), /workflow\/skip machinery changed/);
  assert.equal(evaluated, 0);
});
t('selection machinery runs register shards only, even with identical full shard drvs', () => {
  for (const p of SELECTION_PATHS) {
    runs(pr({ job: 'register-proofs-shard-2', changedPaths: [p] }), /selection machinery changed/);
    assert.equal(pr({ job: 'shared-native', changedPaths: [p] }).decision, 'skip', `${p} alone does not force shared-native`);
  }
});
t('unknown job runs', () => { runs(pr({ job: 'nope' }), /unknown job/); });

// The bundles must be exactly what ci.yml builds.
const ci = readFileSync(new URL('../workflows/ci.yml', import.meta.url), 'utf8');
t('bundles cover every scaffold build in ci.yml', () => {
  const matrix = ci.match(/^\s+target: \[([^\]]+)\]/m)[1].split(',').map((s) => s.trim());
  assert.deepEqual([...matrix].sort(), Object.keys(BUNDLES).sort(), 'matrix targets == bundle jobs');
  const step = (name) => { const i = ci.indexOf(`- name: ${name}`); assert.ok(i >= 0, name); const j = ci.indexOf('\n      - name:', i + 1); return ci.slice(i, j < 0 ? undefined : j); };
  const tokens = (s) => [...s.matchAll(/\.#((?:packages|checks)\.aarch64-linux\.(?:\$\{\{ [^}]+ \}\}|[\w$.\-]+))/g)].map((m) => m[1]);
  const build = step('build ${{ matrix.target }}');
  const nativeLine = build.split('\n').find((l) => l.includes('check.sh native'));
  assert.deepEqual(tokens(nativeLine), BUNDLES.native, 'native builds exactly its bundle');
  assert.ok(build.includes('.#packages.aarch64-linux.${{ matrix.target }}'), 'other targets build packages.<target>');
  for (const [job, b] of Object.entries(BUNDLES)) if (job !== 'native') assert.equal(b[0], `packages.${SYSTEM}.${job}`, job);
  assert.deepEqual(tokens(step('register shard coverage')), [BUNDLES['proofs-core-a'][1]], 'core-a coverage step builds its bundle member');
  // Every other installable in the workflow is either a bundle member or the register PR route, which
  // the plan never compares (selected wrappers and the boundary).
  const allowed = new Set([...Object.values(BUNDLES).flat(), 'packages.aarch64-linux.${{ matrix.target }}',
    'packages.aarch64-linux.register-selection', 'packages.aarch64-linux.register-proofs-selected-shard-$i']);
  for (const tok of tokens(ci)) assert.ok(allowed.has(tok), `unaccounted build in ci.yml: ${tok}`);
  for (const s of ['shard coverage', 'build ${{ matrix.target }}']) assert.ok(step(s).length > 0);
  assert.match(step('register shard coverage'), /steps\.plan\.outputs\.decision != 'skip'/);
  assert.match(build, /if: steps\.plan\.outputs\.decision != 'skip'/);
});
console.log(`PASS skip plan: ${n} control groups (identical bundles skip; changed member, failed/thrown/malformed evaluation, non-PR, bad shas, head mismatch, unreadable diff, .github and selection-machinery changes run; bundles match ci.yml)`);
