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
t('selection machinery runs register shards, text shards, core-b and core-a only, even with identical full drvs', () => {
  for (const p of SELECTION_PATHS) {
    runs(pr({ job: 'register-proofs-shard-2', changedPaths: [p] }), /selection machinery changed/);
    runs(pr({ job: 'proofs-shard-1', changedPaths: [p] }), /selection machinery changed/);
    runs(pr({ job: 'proofs-core-b', changedPaths: [p] }), /selection machinery changed/);
    assert.equal(pr({ job: 'shared-native', changedPaths: [p] }).decision, 'skip', `${p} alone does not force shared-native`);
    runs(pr({ job: 'proofs-core-a', changedPaths: [p] }), /selection machinery changed/);
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

// The bundles must be exactly what each job builds in ci.yml (Lynn, #195 review r2). Recognizing some
// target spellings is not enough: an unrecognized argument would silently mean "builds nothing". So the
// scaffold job is accounted for line by line: every run command (continuations joined), uses, env and
// with entry must be one of the reviewed lines below, unknown step or job keys are refused, and every
// argument of every nix command must be a known flag, the overrides array, or a .#(packages|checks)
// installable. Bundles are then derived from the parsed build targets of each job's branch.
export function scaffoldAccount(text) {
  const start = text.indexOf('\n  scaffold:\n'); assert.ok(start >= 0, 'scaffold job');
  const body = text.slice(start + 1); const end = body.slice(1).search(/\n {2}[A-Za-z][\w-]*:/);
  const lines = (end < 0 ? body : body.slice(0, end + 1)).split('\n');
  const jobKeys = new Set(), stepKeys = new Set(), items = [], steps = [];
  let step = null;
  for (let k = 1; k < lines.length; k++) {
    const l = lines[k]; if (!l.trim() || l.trim().startsWith('#')) continue;
    const ind = l.search(/\S/);
    if (ind === 4) { jobKeys.add(l.trim().split(':')[0]); continue; }
    if (ind === 6 && !l.trim().startsWith('- ')) continue; // strategy contents (matrix checked separately)
    if (ind === 8 && !lines.slice(0, k).some((x) => x.startsWith('    steps:'))) continue; // matrix entries
    let m = l.match(/^ {6}- ([\w-]+):\s?(.*)$/) ?? l.match(/^ {8}([\w-]+):\s?(.*)$/);
    if (l.startsWith('      - ')) { step = { name: null, if: null, items: [] }; steps.push(step); }
    assert.ok(m && step, `unparsed scaffold line: ${l}`);
    const [, key, val] = m; stepKeys.add(key);
    if (key === 'name') step.name = val.trim(); else if (key === 'if') step.if = val.trim(); else if (key === 'id') step.id = val.trim();
    else if (key === 'uses') { items.push(`uses: ${val.trim()}`); step.items.push(`uses: ${val.trim()}`); }
    else if (key === 'env' || key === 'with') {
      assert.equal(val.trim(), '', `${key} must be a block`);
      for (k++; k < lines.length && (lines[k].trim() === '' || lines[k].search(/\S/) >= 10); k++) {
        if (!lines[k].trim() || lines[k].trim().startsWith('#')) continue;
        const e = `${key}.${lines[k].trim().replace(/\s+/g, ' ')}`; items.push(e); step.items.push(e);
      }
      k--;
    } else if (key === 'run') {
      const cmds = [];
      if (val.trim() !== '|') cmds.push(val.trim());
      else {
        const blk = []; for (k++; k < lines.length && (lines[k].trim() === '' || lines[k].search(/\S/) >= 10); k++) blk.push(lines[k]); k--;
        for (const c of blk.join('\n').replace(/\\\n\s*/g, ' ').split('\n')) { const t = c.trim().replace(/\s+/g, ' '); if (t && !t.startsWith('#')) cmds.push(t); }
      }
      for (const c of cmds) { items.push(`run: ${c}`); step.items.push(`run: ${c}`); }
    } else assert.fail(`unsupported step key "${key}" in scaffold step ${step.name}`);
  }
  return { jobKeys, stepKeys, items, steps };
}
// Shell words of one nix command after its subcommand; every word must be understood.
export function nixTargets(cmd) {
  const at = cmd.search(/(?:^|\s)nix\s/); if (at < 0) return null;
  // The workflow expression is one word to the shell (expanded before it runs); keep it whole.
  const MT = '\u0000MATRIX_TARGET\u0000';
  const words = cmd.slice(at).trim().replaceAll('${{ matrix.target }}', MT).match(/"[^"]*"|'[^']*'|\S+/g).map((x) => x.replaceAll(MT, '${{ matrix.target }}'));
  assert.equal(words[0], 'nix');
  const sub = words[1], targets = [];
  const FLAGS = new Set(['-L', '--no-link', '--no-write-lock-file', '--json']);
  for (let w = 2; w < words.length; w++) {
    const word = words[w];
    if (FLAGS.has(word)) continue;
    if (word === '--out-link' || word === '--apply') { w++; continue; }
    if (word === '"${overrides[@]}"') continue;
    const m = word.replace(/^"(.*)"$/, '$1').match(/^\.#((?:packages|checks)\.aarch64-linux(?:\.(?:\$\{\{ matrix\.target \}\}|[\w$-]+))?)$/);
    assert.ok(m, `unsupported nix argument ${JSON.stringify(word)} in: ${cmd}`);
    targets.push(m[1]);
  }
  return { sub, targets };
}
// The reviewed scaffold lines. Any workflow change to the scaffold job must update this list, which
// makes every new command or argument an explicit, reviewed accounting decision.
const SCAFFOLD = [
  "uses: actions/checkout@v6",
  "with.persist-credentials: false",
  "uses: nixbuild/nix-quick-install-action@v35",
  "run: echo \"prefix=nix-scaffold-$RUNNER_OS-$RUNNER_ARCH-${{ hashFiles('**/*.nix', '**/flake.lock') }}\" >> \"$GITHUB_OUTPUT\"",
  "uses: nix-community/cache-nix-action/restore@v7",
  "with.primary-key: ${{ steps.key.outputs.prefix }}-${{ github.run_id }}-${{ github.run_attempt }}",
  "with.restore-prefixes-first-match: |",
  "with.${{ steps.key.outputs.prefix }}-",
  "with.nix-scaffold-${{ runner.os }}-${{ runner.arch }}-",
  "run: .github/scripts/check.test.sh",
  "run: node .github/scripts/skip-plan.test.mjs",
  "env.EVENT: ${{ github.event_name }}",
  "env.TARGET: ${{ matrix.target }}",
  "env.BASE_SHA: ${{ github.event.pull_request.base.sha }}",
  "env.HEAD_SHA: ${{ github.sha }}",
  "run: if [ \"$EVENT\" = pull_request ] && [[ \"$BASE_SHA\" =~ ^[0-9a-f]{40}$ ]]; then",
  "run: git fetch --no-tags --depth=1 origin \"$BASE_SHA\" || echo \"base fetch failed: the job runs in full\"",
  "run: fi",
  "run: node .github/scripts/skip-plan-run.mjs decide \"$TARGET\" skip-plan/record.json",
  "uses: actions/upload-artifact@v4",
  "with.name: skip-plan-${{ matrix.target }}",
  "with.path: skip-plan/",
  "with.if-no-files-found: warn",
  "run: shards=$(nix eval --json .#packages.aarch64-linux --apply 'p: builtins.length (builtins.filter (n: builtins.match \"proofs-shard-[0-9]+\" n != null) (builtins.attrNames p))')",
  "run: test \"$shards\" = 3 || { echo \"flake exposes $shards proof shards; ci.yml lists 3\"; exit 1; }",
  "run: nix build -L --no-link .#packages.aarch64-linux.register-proofs-shard-coverage",
  "env.EVENT: ${{ github.event_name }}",
  "env.TARGET: ${{ matrix.target }}",
  "env.BASE_SHA: ${{ github.event.pull_request.base.sha }}",
  "run: if [ \"${{ matrix.target }}\" = native ]; then",
  "run: .github/scripts/check.sh native 9000 nix build -L --no-link .#checks.aarch64-linux.native .#checks.aarch64-linux.edit-reference .#checks.aarch64-linux.gate-inputs",
  "run: elif [ \"$EVENT\" = pull_request ] && [[ \"$TARGET\" =~ ^register-proofs-shard-([0-9]+)$ ]]; then",
  "run: i=\"${BASH_REMATCH[1]}\"",
  "run: [[ \"$BASE_SHA\" =~ ^[0-9a-f]{40}$ ]] || { echo \"pull_request base sha missing or malformed: $BASE_SHA\"; exit 1; }",
  "run: [ \"$(git rev-parse HEAD)\" = \"$GITHUB_SHA\" ] || { echo \"checkout HEAD is not GITHUB_SHA\"; exit 1; }",
  "run: overrides=(--override-input selection-head \"git+file://$PWD?rev=$GITHUB_SHA&shallow=1\"",
  "run: --override-input selection-base \"github:carbon-study/nickel-crdt/$BASE_SHA\")",
  "run: mkdir -p selection-evidence",
  "run: .github/scripts/check.sh \"$TARGET-selection\" 1800 nix build -L --no-write-lock-file --out-link selection-result .#packages.aarch64-linux.register-selection \"${overrides[@]}\"",
  "run: cp selection-result/identity.json selection-result/mode selection-evidence/",
  "run: if [ -e selection-result/selection.json ]; then cp selection-result/selection.json selection-evidence/; fi",
  "run: .github/scripts/check.sh \"$TARGET\" 9000 nix build -L --no-write-lock-file --out-link selected-result \".#packages.aarch64-linux.register-proofs-selected-shard-$i\" \"${overrides[@]}\"",
  "run: elif [ \"$EVENT\" = pull_request ] && [[ \"$TARGET\" =~ ^proofs-(shard-[0-9]+|core-b|core-a)$ ]]; then",
  "run: job=\"${BASH_REMATCH[1]}\"",
  "run: [[ \"$BASE_SHA\" =~ ^[0-9a-f]{40}$ ]] || { echo \"pull_request base sha missing or malformed: $BASE_SHA\"; exit 1; }",
  "run: [ \"$(git rev-parse HEAD)\" = \"$GITHUB_SHA\" ] || { echo \"checkout HEAD is not GITHUB_SHA\"; exit 1; }",
  "run: overrides=(--override-input selection-head \"git+file://$PWD?rev=$GITHUB_SHA&shallow=1\"",
  "run: --override-input selection-base \"github:carbon-study/nickel-crdt/$BASE_SHA\")",
  "run: mkdir -p text-selection-evidence",
  "run: .github/scripts/check.sh \"$TARGET-selection\" 1800 nix build -L --no-write-lock-file --out-link text-selection-result .#packages.aarch64-linux.text-selection \"${overrides[@]}\"",
  "run: cp text-selection-result/identity.json text-selection-result/mode text-selection-evidence/",
  "run: if [ -e text-selection-result/selection.json ]; then cp text-selection-result/selection.json text-selection-evidence/; fi",
  "run: .github/scripts/check.sh \"$TARGET\" 9000 nix build -L --no-write-lock-file --out-link text-selected-result \".#packages.aarch64-linux.proofs-selected-$job\" \"${overrides[@]}\"",
  "run: else",
  "run: .github/scripts/check.sh ${{ matrix.target }} 9000 nix build -L --no-link .#packages.aarch64-linux.${{ matrix.target }}",
  "run: fi",
  "env.TARGET: ${{ matrix.target }}",
  "run: mkdir -p selection-evidence",
  "run: for f in \"/tmp/$TARGET-selection.log\" \"/tmp/$TARGET.log\"; do if [ -e \"$f\" ]; then cp \"$f\" selection-evidence/; fi; done",
  "run: for f in selection-identity.json planned.json results.json; do if [ -e \"selected-result/$f\" ]; then cp \"selected-result/$f\" selection-evidence/; fi; done",
  "run: ls -la selection-evidence",
  "uses: actions/upload-artifact@v4",
  "with.name: register-selection-${{ matrix.target }}",
  "with.path: selection-evidence/",
  "with.if-no-files-found: warn",
  "env.TARGET: ${{ matrix.target }}",
  "run: mkdir -p text-selection-evidence",
  "run: for f in \"/tmp/$TARGET-selection.log\" \"/tmp/$TARGET.log\"; do if [ -e \"$f\" ]; then cp \"$f\" text-selection-evidence/; fi; done",
  "run: for f in selection-identity.json edit/planned.json edit/results.json edit/loaded-modules.json smoke-planned.json smoke-results.json; do if [ -e \"text-selected-result/$f\" ]; then cp \"text-selected-result/$f\" text-selection-evidence/; fi; done",
  "run: ls -la text-selection-evidence",
  "uses: actions/upload-artifact@v4",
  "with.name: text-selection-${{ matrix.target }}",
  "with.path: text-selection-evidence/",
  "with.if-no-files-found: warn",
  "uses: nix-community/cache-nix-action/save@v7",
  "with.primary-key: ${{ steps.key.outputs.prefix }}-${{ github.run_id }}-${{ github.run_attempt }}",
];
const ci = readFileSync(new URL('../workflows/ci.yml', import.meta.url), 'utf8');
t('scaffold job is accounted for line by line; bundles are exactly what each job builds', () => {
  const matrix = ci.match(/^\s+target: \[([^\]]+)\]/m)[1].split(',').map((x) => x.trim());
  assert.deepEqual([...matrix].sort(), Object.keys(BUNDLES).sort(), 'matrix targets == bundle jobs');
  const acc = scaffoldAccount(ci);
  assert.deepEqual([...acc.jobKeys].sort(), ['name', 'runs-on', 'steps', 'strategy', 'timeout-minutes'], 'scaffold job keys');
  for (const k of acc.stepKeys) assert.ok(['name', 'id', 'if', 'run', 'uses', 'with', 'env'].includes(k), `step key ${k}`);
  assert.deepEqual(acc.items, SCAFFOLD, 'every scaffold command, action, env and with entry is a reviewed line');
  // Every nix command, parsed word by word; only builds contribute targets.
  const P = (x) => `packages.${SYSTEM}.${x}`, GENERIC = 'packages.aarch64-linux.${{ matrix.target }}';
  const builds = [];
  for (const st of acc.steps) for (const it of st.items) {
    if (!it.startsWith('run: ')) continue;
    const parsed = nixTargets(it.slice(5)); if (!parsed) continue;
    if (parsed.sub === 'build') builds.push({ step: st, cmd: it, targets: parsed.targets });
    else assert.deepEqual([parsed.sub, parsed.targets], ['eval', ['packages.aarch64-linux']], `only the shard-count eval may be a non-build nix command: ${it}`);
  }
  const by = (pred) => { const b = builds.filter(pred); assert.equal(b.length, 1, 'exactly one matching build command'); return b[0]; };
  const build = acc.steps.find((x) => x.name === 'build ${{ matrix.target }}'), cover = acc.steps.find((x) => x.name === 'register shard coverage');
  assert.equal(builds.length, 7, 'seven build commands');
  assert.deepEqual(by((b) => b.cmd.includes('check.sh native')).targets, BUNDLES.native);
  assert.deepEqual(by((b) => b.cmd.includes('check.sh ${{ matrix.target }}')).targets, [GENERIC]);
  assert.deepEqual(by((b) => b.step === cover).targets, [BUNDLES['proofs-core-a'][1]]);
  assert.deepEqual(by((b) => b.cmd.includes('--out-link selection-result')).targets, [P('register-selection')]);
  assert.deepEqual(by((b) => b.cmd.includes('check.sh "$TARGET" 9000') && b.cmd.includes('--out-link selected-result')).targets, [P('register-proofs-selected-shard-$i')]);
  assert.deepEqual(by((b) => b.cmd.includes('--out-link text-selection-result')).targets, [P('text-selection')]);
  assert.deepEqual(by((b) => b.cmd.includes('--out-link text-selected-result')).targets, [P('proofs-selected-$job')]);
  for (const b of builds) assert.ok(b.step === build || b.step === cover, `build outside the guarded steps: ${b.cmd}`);
  for (const job of Object.keys(BUNDLES)) {
    const want = job === 'native' ? BUNDLES.native : job === 'proofs-core-a' ? [P(job), BUNDLES['proofs-core-a'][1]] : [P(job)];
    assert.deepEqual(BUNDLES[job], want, `${job}: bundle == what the job builds`);
  }
  assert.equal(cover.if, "matrix.target == 'proofs-core-a' && steps.plan.outputs.decision != 'skip'");
  assert.equal(build.if, "steps.plan.outputs.decision != 'skip'");
});
t('nixTargets refuses every unsupported argument shape', () => {
  for (const w of ['./#packages.aarch64-linux.shared-proofs', 'path:.#packages.aarch64-linux.x', '.#packages.x86_64-linux.x', 'github:o/r#packages.aarch64-linux.x', '--file', 'nixpkgs#hello', '.'])
    assert.throws(() => nixTargets(`nix build -L --no-link .#packages.aarch64-linux.ok ${w}`), /unsupported nix argument/, w);
  assert.deepEqual(nixTargets('nix build -L --no-link .#packages.aarch64-linux.a ".#checks.aarch64-linux.b"').targets, ['packages.aarch64-linux.a', 'checks.aarch64-linux.b']);
});
console.log(`PASS skip plan: ${n} control groups (identical bundles skip; changed member, failed/thrown/malformed evaluation, non-PR, bad shas, head mismatch, unreadable diff, .github and selection-machinery changes run; non-derivation outputs refused by real nix; scaffold job accounted line by line, unsupported nix arguments refused, bundles == each job's builds)`);
