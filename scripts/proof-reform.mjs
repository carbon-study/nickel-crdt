// Recurrence fence for migrated authored families; not a proof against aliases.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
export async function checkProofReform(root) {
  for(const name of ['EditAtomic','LoopUtil','Smoke']) {
    const source=await fs.readFile(path.join(root,'proofs',name+'.lt'),'utf8');
    assert(!/\b(?:norm_spec|delta_only|delta_once|iota|zeta_full)\b|\.norm\s*\(/.test(source),
      name+' reform: explicit normalization is prohibited; compose the proved contracts');
  }
}
