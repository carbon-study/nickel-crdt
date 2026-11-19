// Controls for skip-plan.mjs (#194). Runs in well under a second; CI runs it in every scaffold job
// before the plan. Every doubt must run the job; only a complete bundle of identical, valid drv paths skips.
import assert from 'node:assert/strict';
import { mkdtempSync, readFileSync, writeFileSync, rmSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { resolveDrv } from './skip-plan-nix.mjs';
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
  for (const s of [drv('x') + '\n\n', `${drv('x')}\n${drv('y')}`, `${drv('x')}\n${drv('y')}\n`, ' ' + drv('x'), '/nix/store/short-x.drv', `${drv('x')}.extra`, '', 'warning: x', '/tmp/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa-x.drv']) {
    assert.equal(checkEval(ok(s)).ok, false, JSON.stringify(s));
    runs(pr({ evaluate: () => ok(s) }), /not exactly one .drv store path/);
  }
  assert.equal(checkEval(ok(drv('x'))).ok, true);
  assert.deepEqual(checkEval(ok(drv('x') + '\n')), { ok: true, drv: drv('x') }, 'one trailing newline (path-info) is accepted and stripped');
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

// Lynn's witness (#195 review): a flake output that is a bare set carrying a drvPath field. Reading
// .drvPath would return a valid-looking path; resolving the installable must refuse it, as nix build does.
t('installable resolution refuses a non-derivation output (real nix)', () => {
  const dir = mkdtempSync(join(tmpdir(), 'skip-plan-witness-'));
  try {
    writeFileSync(join(dir, 'flake.nix'), `{ outputs = { self }: let real = derivation { name = "real"; system = "${SYSTEM}"; builder = "/bin/sh"; args = [ "-c" "echo > $out" ]; }; in {
      packages.${SYSTEM}.real = real;
      packages.${SYSTEM}.fake = { drvPath = real.drvPath; };
    }; }\n`);
    const git = (...a) => { const r = spawnSync('git', ['-C', dir, ...a], { encoding: 'utf8' }); assert.equal(r.status, 0, r.stderr); return r.stdout.trim(); };
    git('init', '-q'); git('add', 'flake.nix'); git('-c', 'user.name=t', '-c', 'user.email=t@t', 'commit', '-qm', 'witness');
    const rev = git('rev-parse', 'HEAD');
    const real = checkEval(resolveDrv(dir, rev, `packages.${SYSTEM}.real`));
    assert.ok(real.ok, JSON.stringify(real));
    const fake = checkEval(resolveDrv(dir, rev, `packages.${SYSTEM}.fake`));
    assert.equal(fake.ok, false, 'a bare set with a drvPath field must not resolve');
    // Through the planner: identical "drvPath" at both revisions must still run.
    const r = decide({ job: 'shared-native', event: 'pull_request', baseSha: B, headSha: H, checkedHead: H, changedPaths: ['x'],
      evaluate: () => resolveDrv(dir, rev, `packages.${SYSTEM}.fake`) });
    runs(r, /base exit 1, head exit 1/);
  } finally { rmSync(dir, { recursive: true, force: true }); }
});

// The bundles must be exactly what each job builds in ci.yml, per job: every command that builds
// something matches exactly one rule with an exact target list, and each job's bundle is derived from
// the rules that apply to it (Lynn, #195 review: a global allow-list let core-b build shared-proofs).
const ci = readFileSync(new URL('../workflows/ci.yml', import.meta.url), 'utf8');
t('bundles are exactly what each job builds in ci.yml', () => {
  const matrix = ci.match(/^\s+target: \[([^\]]+)\]/m)[1].split(',').map((x) => x.trim());
  assert.deepEqual([...matrix].sort(), Object.keys(BUNDLES).sort(), 'matrix targets == bundle jobs');
  const tokens = (x) => [...x.matchAll(/\.#((?:packages|checks)\.aarch64-linux\.(?:\$\{\{ [^}]+ \}\}|[\w$.\-]+))/g)].map((m) => m[1]);
  const stepOf = (pos) => { const k = ci.lastIndexOf('- name: ', pos); return ci.slice(k + 8, ci.indexOf('\n', k)).trim(); };
  // Physical lines joined across shell continuations, each with the step it belongs to.
  const lines = []; let at = 0;
  for (const raw of ci.split(/(?<!\\)\n/)) { lines.push({ text: raw.replace(/\\\n\s*/g, ' '), step: stepOf(at) }); at += raw.length + 1; }
  const P = (x) => `packages.${SYSTEM}.${x}`, GENERIC = 'packages.aarch64-linux.${{ matrix.target }}';
  const BUILD = 'build ${{ matrix.target }}', COVER = 'register shard coverage';
  const rules = [
    { name: 'native', step: BUILD, when: (l) => l.includes('check.sh native'), want: BUNDLES.native },
    { name: 'generic', step: BUILD, when: (l) => l.includes('check.sh ${{ matrix.target }}'), want: [GENERIC] },
    { name: 'register boundary (PR route, never compared)', step: BUILD, when: (l) => l.includes('"$TARGET-selection"'), want: [P('register-selection')] },
    { name: 'register selected (PR route, never compared)', step: BUILD, when: (l) => l.includes('check.sh "$TARGET" 9000'), want: [P('register-proofs-selected-shard-$i')] },
    { name: 'core-a coverage', step: COVER, when: () => true, want: [BUNDLES['proofs-core-a'][1]] },
  ];
  const hits = new Map(rules.map((r) => [r.name, 0]));
  for (const { text, step } of lines) {
    const tk = tokens(text); if (!tk.length) continue;
    const match = rules.filter((r) => r.step === step && r.when(text));
    assert.equal(match.length, 1, `build command in step "${step}" matches ${match.length} rules: ${text.trim()}`);
    assert.deepEqual(tk, match[0].want, `${match[0].name}: builds exactly ${match[0].want.join(' ')}`);
    hits.set(match[0].name, hits.get(match[0].name) + 1);
  }
  for (const [name, k] of hits) assert.equal(k, 1, `rule "${name}" matched ${k} commands`);
  // Per job: native builds only its own branch; core-a the generic package plus coverage; every
  // other job only the generic package (register shards' PR route is the boundary, compared as the full shard).
  for (const job of Object.keys(BUNDLES)) {
    const want = job === 'native' ? BUNDLES.native : job === 'proofs-core-a' ? [P(job), BUNDLES['proofs-core-a'][1]] : [P(job)];
    assert.deepEqual(BUNDLES[job], want, `${job}: bundle == what the job builds`);
  }
  assert.match(ci.slice(ci.indexOf(`- name: ${COVER}`)), /^\s+if: matrix\.target == 'proofs-core-a' && steps\.plan\.outputs\.decision != 'skip'/m);
  assert.match(ci.slice(ci.indexOf(`- name: ${BUILD}`)), /^\s+if: steps\.plan\.outputs\.decision != 'skip'/m);
});
console.log(`PASS skip plan: ${n} control groups (identical bundles skip; changed member, failed/thrown/malformed evaluation, non-PR, bad shas, head mismatch, unreadable diff, .github and selection-machinery changes run; non-derivation outputs refused by real nix; bundles match each job's builds in ci.yml)`);
