// CLI for skip-plan.mjs (#194).
//   node skip-plan-run.mjs bundle JOB          -> the job's installables, one per line (unknown job: exit 2)
//   node skip-plan-run.mjs decide JOB OUT.json -> writes the record, prints the decision, and appends
//        decision=skip|run to $GITHUB_OUTPUT. Env: EVENT, BASE_SHA, HEAD_SHA (the merge head).
// `decide` never fails on a doubt: any error becomes decision=run with its reason in the record.
import { spawnSync } from 'node:child_process';
import { appendFileSync, mkdirSync, writeFileSync } from 'node:fs';
import { dirname } from 'node:path';
import { BUNDLES, decide } from './skip-plan.mjs';
import { resolveDrv } from './skip-plan-nix.mjs';

const [mode, job, out] = process.argv.slice(2);
if (mode === 'bundle') {
  const b = BUNDLES[job];
  if (!b) { console.error(`unknown job ${JSON.stringify(job)}`); process.exit(2); }
  for (const a of b) console.log(`.#${a}`);
  process.exit(0);
}
if (mode !== 'decide' || !job || !out) { console.error('usage: skip-plan-run.mjs bundle JOB | decide JOB OUT.json'); process.exit(2); }

const repo = process.cwd();
const sh = (cmd, args) => spawnSync(cmd, args, { cwd: repo, encoding: 'utf8', maxBuffer: 1 << 26 });
let record;
try {
  const { EVENT: event, BASE_SHA: baseSha, HEAD_SHA: headSha } = process.env;
  const head = sh('git', ['rev-parse', 'HEAD']);
  const checkedHead = head.status === 0 ? head.stdout.trim() : null;
  // --no-renames lists both sides of a rename; deletions are listed too.
  const diff = baseSha && headSha ? sh('git', ['diff', '--name-only', '--no-renames', '-z', baseSha, headSha]) : null;
  const changedPaths = diff && diff.status === 0 ? diff.stdout.split('\0').filter(Boolean) : null;
  const nix = sh('nix', ['--version']);
  record = decide({ job, event, baseSha, headSha, checkedHead, changedPaths, repo,
    nixVersion: nix.status === 0 ? nix.stdout.trim() : null,
    evaluate: (rev, attr) => resolveDrv(repo, rev, attr) });
} catch (e) {
  record = { schema: 1, job, decision: 'run', reasons: [`planner error: ${String(e?.stack ?? e).slice(0, 500)}`] };
}
mkdirSync(dirname(out), { recursive: true });
writeFileSync(out, JSON.stringify(record, null, 2) + '\n');
console.log(`${job}: ${record.decision}: ${record.reasons.join(' | ')}`);
if (process.env.GITHUB_OUTPUT) appendFileSync(process.env.GITHUB_OUTPUT, `decision=${record.decision}\n`);
