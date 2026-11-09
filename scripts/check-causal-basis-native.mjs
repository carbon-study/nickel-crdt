// Focused native acceptance and semantic controls for continuation §2.
// This is neither an F* proof nor a replacement for the independent sequence oracle.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
const root = fileURLToPath(new URL('..', import.meta.url));
assert(process.argv[2], 'usage: node scripts/check-causal-basis-native.mjs OUTPUT_DIRECTORY');
const output = path.resolve(process.argv[2]);
await fs.mkdir(output, {recursive: true});
const original = await fs.readFile(path.join(root, 'src/edit.rs'), 'utf8');
const cases = [
  ['past-no-expansion', 'for _ in 0..facts.len() {\n        selected = past_pass', 'for _ in 0..0 {\n        selected = past_pass', 'exact_past_on_all_four_vertex_dags_and_storage_permutations', 'assertion `left == right` failed'],
  ['past-skips-root-check', '    validate_after(facts, after)?;', '    // skipped direct validation', 'past_roots_missing_and_transitive_domain_boundary', 'assertion `left == right` failed'],
  ['ready-ignores-missing', 'if !has_event(done, *id) {', 'if false {', 'readiness_is_exact_direct_inclusion', 'assertion `left == right` failed'],
  ['receiver-contaminates-author', 'if has_event(&selected, id) {', 'if true {', 'receiver_extras_preserve_exact_author_placements_through_public_admission', 'author basis changed with receiver extras'],
];
function run(cwd, test, target) {
  return spawnSync('cargo', ['test', '--offline', '--locked', '--lib', test, '--', '--nocapture'], {
    cwd, encoding: 'utf8', timeout: 60000,
    env: {...process.env, CARGO_TARGET_DIR: target},
  });
}
const positive = run(root, 'causal_basis_tests', path.join(output, 'positive-target'));
await fs.writeFile(path.join(output, 'positive.log'), positive.stdout + positive.stderr);
assert.equal(positive.status, 0, 'positive native acceptance failed (see positive.log)');
for (const [name, from, to, test, marker] of cases) {
  assert.equal(original.split(from).length, 2, name + ': mutation anchor must be unique');
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'nickel-past-control-'));
  try {
    for (const p of ['Cargo.toml', 'Cargo.lock', 'src', 'proof-smoke']) {
      await fs.cp(path.join(root, p), path.join(dir, p), {recursive: true});
    }
    await fs.writeFile(path.join(dir, 'src/edit.rs'), original.replace(from, to));
    await fs.writeFile(path.join(output, name + '.mutation.json'), JSON.stringify({from, to, test}, null, 2) + '\n');
    const result = run(dir, test, path.join(output, 'control-target'));
    const log = result.stdout + result.stderr;
    await fs.writeFile(path.join(output, name + '.log'), log);
    assert.equal(result.status, 101, name + ': must fail as a native test, not timeout/signal');
    assert(log.includes('running 1 test') && log.includes('test result: FAILED') && log.includes(marker),
      name + ': must reach the intended runtime assertion, not a compile failure');
    console.log(name + ': intended native assertion rejected');
  } finally {
    await fs.rm(dir, {recursive: true});
  }
}
