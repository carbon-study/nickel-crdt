// The one real Nix call of the skip plan: resolve a flake output as an installable to its .drv path.
import { spawnSync } from 'node:child_process';
import { RESOLVE_ARGS, flakeRef } from './skip-plan.mjs';

export function resolveDrv(repo, rev, attr) {
  return spawnSync('nix', [...RESOLVE_ARGS, `${flakeRef(repo, rev)}#${attr}`], { cwd: repo, encoding: 'utf8', maxBuffer: 1 << 26 });
}
