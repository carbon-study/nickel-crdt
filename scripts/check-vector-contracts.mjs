// These are proof-dependency controls, separate from actual-Rust mutations.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import {put, verify} from './proof-cache.mjs';
import {hasOrdinaryTheoremRejection} from './negative-proof-evidence.mjs';

export async function checkVectorContracts({proof, output, fstar, models, modelCache}) {
  const vectorFile = path.join(proof, 'Nickel.Vector.fst');
  const acceptedFile = path.join(proof, 'Nickel.EditAccepted.fst');
  const vector = await fs.readFile(vectorFile, 'utf8');
  const accepted = await fs.readFile(acceptedFile, 'utf8');
  const cases = [];
  for (const name of ['vector_contents', 'vector_from_seq', 'vector_length', 'slice_length', 'slice_index']) {
    const start = vector.indexOf('let ' + name + ' ');
    assert(start >= 0, 'missing vector contract ' + name);
    const at = vector.indexOf(' [SMTPat ', start);
    const end = vector.indexOf('] =', at) + 1;
    assert(at > start && end > at && !vector.slice(start, at).includes('\n\n'));
    cases.push({name: 'vector-without-pattern-' + name, file: vectorFile,
      source: vector.slice(0, at) + vector.slice(end),
      theorem: 'append_fresh_preserves_unique', view: accepted});
  }
  for (const name of ['append_fresh_preserves_unique', 'append_whole_fact', 'push_has_exact_contents', 'push_membership']) {
    const start = accepted.indexOf('let ' + name + ' ');
    assert(start >= 0, 'missing vector caller ' + name);
    const next = /\nlet (?:rec )?\w+ /.exec(accepted.slice(start + 4));
    const end = next ? start + 4 + next.index : accepted.length;
    const body = accepted.slice(start, end);
    const needle = 'Tactics.prune "Alloc.Vec.impl_1__as_slice";';
    assert.equal(body.split(needle).length, 2, 'one caller visibility anchor');
    const source = accepted.slice(0, start) + body.replace(needle,
      needle + '\n    Tactics.prune "Nickel.Vector";') + accepted.slice(end);
    cases.push({name: 'vector-without-contracts-' + name, file: acceptedFile,
      source, theorem: name, view: source});
    const withoutFromSeq = accepted.slice(0, start) + body.replace(needle,
      needle + '\n    Tactics.prune "Nickel.Vector.vector_from_seq";') + accepted.slice(end);
    cases.push({name: 'vector-without-from-seq-' + name, file: acceptedFile,
      source: withoutFromSeq, theorem: name, view: withoutFromSeq});
  }
  for (const test of cases) {
    try {
      await put(test.file, test.source);
      const result = await verify({dir: proof, roots: [acceptedFile], fstar, models, modelCache});
      await fs.writeFile(path.join(output, test.name + '.proof.log'), result.log);
      assert(hasOrdinaryTheoremRejection({status: result.status, log: result.log,
        theorem: 'Nickel.EditAccepted.' + test.theorem, view: test.view}),
        'require ordinary vector-contract dependency rejection: ' + result.log);
      console.log('PASS ' + test.name + ': actual caller requires the model contract');
    } finally {
      await put(vectorFile, vector);
      await put(acceptedFile, accepted);
    }
  }
}
