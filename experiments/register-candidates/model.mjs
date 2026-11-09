// Register-contract candidates vs Ren's undo-questionnaire answers (q13-q17),
// and a bounded search for histories where surviving candidates show
// different values. v2: repairs from Lynn's review of v1 (2026-11-08):
// writer names are enumerated independently (tie-breaking uses them, so no
// symmetry reduction); same-value-write stack handling and redo clearing are
// explicit choices; peers see only replicated facts; every decision is frozen
// against the author's own captured past.
//
// Model. A history lists commands in creation order. Each command names its
// author and the commands it has seen (causally closed, including the author's
// own earlier commands). Replicated facts are writes and the undo/redo
// commands that take effect; a do-nothing undo/redo stays in its author's
// local history only, so peers never see it. Undo/redo are stack commands per
// author. The final state merges every replicated fact.
//
// usage: node model.mjs [maxOps]

const INITIAL = "black";

// Choices:
// family   X : a write equal to the value its author saw is no edit (it never
//              counts); an undo does nothing if a later active counted write
//              exists.
//          X2: as X, but only a later counted write with a different value
//              blocks.
//          E : every write counts; a later active write with a different
//              value blocks; an undo also retires later equal-valued writes
//              whose author saw this write's value.
//          P : every write counts; any later active write blocks.
// blocked  consume | retain : a do-nothing undo uses up its stack item, or
//              leaves it for a later attempt.
// redo     free | guarded   : a redo always reactivates, or does nothing if a
//              counted write was made after the undo.
// noEdit   push | skip      : (X, X2) a no-edit write pushes an undo item and
//              clears redo like any write, or touches neither stack.
// clear    clear | keep     : a new own (stack-touching) write clears the redo
//              stack, or keeps it.
const families = {
  X: { idempotent: true, block: "laterCounted", cascade: false },
  X2: { idempotent: true, block: "laterDifferent", cascade: false },
  E: { idempotent: false, block: "laterDifferent", cascade: true },
  P: { idempotent: false, block: "laterCounted", cascade: false },
};
const AXES = ["family", "blocked", "redo", "noEdit", "clear"];
const candidates = [];
for (const [family, f] of Object.entries(families)) for (const blocked of ["consume", "retain"]) for (const redo of ["free", "guarded"])
  for (const noEdit of f.idempotent ? ["push", "skip"] : ["push"]) for (const clear of ["clear", "keep"])
    candidates.push({ name: [family, blocked, redo, noEdit, clear].join("/"), family, ...f, blocked, redo, noEdit, clear });

const W = (author, value, seen, label) => ({ kind: "write", author, value, seen, label });
const U = (author, seen, label) => ({ kind: "undo", author, seen, label });
const R = (author, seen, label) => ({ kind: "redo", author, seen, label });

function evaluate(history, cand) {
  const ops = history.map((op, i) => ({ ...op, i }));
  const order = (a, b) => (ops[a].lamport - ops[b].lamport) || (ops[a].author < ops[b].author ? -1 : ops[a].author > ops[b].author ? 1 : a - b);
  const outcome = {};
  const stacks = {};
  const replicated = j => ops[j].kind === "write" || ops[j].targets != null;
  for (const op of ops) {
    // The author's captured past: its own local commands plus the replicated
    // facts it has seen. Do-nothing commands of other authors are invisible.
    const S = op.seen.filter(j => ops[j].author === op.author || replicated(j));
    op.view = S;
    op.lamport = 1 + Math.max(0, ...S.map(j => ops[j].lamport));
    const before = (a, b) => ops[b].view.includes(a);
    const active = (w, within) => {
      let last;
      for (const j of within) if (ops[j].targets?.includes(w) && (last === undefined || order(j, last) > 0)) last = j;
      return last === undefined || ops[last].kind === "redo";
    };
    const counts = (w, within) => ops[w].kind === "write" && active(w, within) && (!cand.idempotent || ops[w].effective);
    const visible = within => {
      const live = within.filter(w => counts(w, within));
      const maxima = live.filter(w => !live.some(e => e !== w && before(w, e)));
      return maxima.length ? ops[maxima.sort(order).at(-1)].value : INITIAL;
    };
    op.visibleIn = visible; op.beforeFn = before; op.countsFn = counts;
    const st = stacks[op.author] ??= { undo: [], redo: [] };
    const say = v => { outcome[op.label ?? op.i] = v; };
    if (op.kind === "write") {
      op.observed = visible(S);
      op.effective = op.value !== op.observed;
      if (cand.idempotent && !op.effective && cand.noEdit === "skip") continue;
      st.undo.push(op.i);
      if (cand.clear === "clear") st.redo = [];
      continue;
    }
    if (op.kind === "undo") {
      const w = st.undo.at(-1);
      if (w === undefined) { op.targets = null; say("unavailable"); continue; }
      const later = S.filter(e => ops[e].kind === "write" && e !== w && before(w, e) && active(e, S));
      const blocking = later.filter(e => cand.block === "laterDifferent"
        ? ops[e].value !== ops[w].value && (!cand.idempotent || ops[e].effective)
        : counts(e, S));
      if (blocking.length) {
        op.targets = null; say("nothing");
        if (cand.blocked === "consume") st.undo.pop();
        continue;
      }
      const echoes = cand.cascade ? later.filter(e => ops[e].value === ops[w].value && ops[e].observed === ops[w].value) : [];
      op.targets = [w, ...echoes];
      st.undo.pop(); st.redo.push(op.i);
      say("undone");
    } else {
      const u = st.redo.at(-1);
      if (u === undefined) { op.targets = null; say("nothing"); continue; }
      if (cand.redo === "guarded" && S.some(e => before(u, e) && counts(e, S))) { op.targets = null; say("nothing"); st.redo.pop(); continue; }
      op.targets = ops[u].targets;
      st.redo.pop(); st.undo.push(ops[u].targets[0]);
      say("redone");
    }
  }
  // merged final state: every replicated fact
  const all = ops.filter(o => o.kind === "write" || o.targets != null).map(o => o.i);
  const before = (a, b) => ops[b].view.includes(a);
  const active = w => { let last; for (const j of all) if (ops[j].targets?.includes(w) && (last === undefined || order(j, last) > 0)) last = j; return last === undefined || ops[last].kind === "redo"; };
  const live = all.filter(w => ops[w].kind === "write" && active(w) && (!cand.idempotent || ops[w].effective));
  const maxima = live.filter(w => !live.some(e => e !== w && before(w, e)));
  outcome.final = maxima.length ? ops[maxima.sort(order).at(-1)].value : INITIAL;
  return outcome;
}

// ---- Ren's answers (incoming/nickel-undo-quiz/ren/ren.json) --------------
const quiz = {
  q13: { history: [W("A", "red", []), W("B", "green", [0]), U("A", [0, 1], "aliceUndo")],
         expect: { aliceUndo: "nothing", final: "green" } },
  q14: { history: [W("A", "red", []), W("B", "green", [0]), U("A", [0, 1], "aliceUndo"), R("A", [0, 1, 2], "aliceRedo")],
         expect: { aliceRedo: "nothing", final: "green" } },
  q15: { history: [W("A", "red", []), W("B", "green", [0]), U("A", [0, 1], "aliceUndo"), U("B", [0, 1, 2], "boUndo")],
         expect: { aliceUndo: "nothing", boUndo: "undone", final: "red" } },
  q16: { history: [W("A", "red", []), W("B", "blue", []), U("B", [0, 1], "boUndo")],
         expect: { boUndo: "undone", final: "red" } },
  q16b: { history: [W("A", "red", []), W("B", "blue", []), U("A", [0, 1], "aliceUndo")],
          expect: { aliceUndo: "undone" } },
  q17: { history: [W("A", "red", []), W("B", "red", [0]), U("A", [0, 1], "aliceUndo")],
         expect: { final: "black" } },
};

const survivors = [], failed = [];
for (const cand of candidates) {
  const fails = [];
  for (const [q, { history, expect }] of Object.entries(quiz)) {
    const got = evaluate(history, cand);
    for (const [k, v] of Object.entries(expect)) if (got[k] !== v) fails.push(`${q}.${k}=${got[k]}`);
  }
  (fails.length ? failed : survivors).push([cand, fails]);
}
console.log(`${candidates.length} candidates; ${survivors.length} reproduce q13-q17`);
const failedFamilies = new Map();
for (const [c, f] of failed) failedFamilies.set(c.family, (failedFamilies.get(c.family) ?? new Set()).add(f.join(";")));
for (const [fam, s] of failedFamilies) console.log(`  ${fam}: ${[...s].length === 1 ? "all variants fail " + [...s][0] : "some variants fail: " + [...s].join(" | ")}`);
const surv = survivors.map(([c]) => c);
console.log("  surviving families: " + [...new Set(surv.map(c => c.family))].join(", "));

// ---- targeted 6-command history from Lynn's review ------------------------
// alice red -> bo green -> cara red; bo undoes without seeing cara; everyone
// syncs; alice undoes; cara undoes.
const lynn6 = [W("A", "red", []), W("B", "green", [0]), W("C", "red", [0, 1]), U("B", [0, 1]), U("A", [0, 1, 2, 3]), U("C", [0, 1, 2, 3, 4])];

// ---- bounded search: all writer labelings, <= maxOps commands --------------
const maxOps = process.env.MODEL_NO_SEARCH ? 0 : Number(process.argv[2] ?? 4);
const authors = ["A", "B", "C"], values = ["red", "green"];
function closedSubsets(history, author) {
  const n = history.length, out = [];
  for (let mask = 0; mask < 1 << n; mask++) {
    const set = []; for (let i = 0; i < n; i++) if (mask >> i & 1) set.push(i);
    if (history.some((op, i) => op.author === author && !set.includes(i))) continue;
    if (!set.every(i => history[i].seen.every(j => set.includes(j)))) continue;
    out.push(set);
  }
  return out;
}
function* extend(history) {
  if (history.length) yield history;
  if (history.length >= maxOps) return;
  for (const author of authors) for (const seen of closedSubsets(history, author)) {
    for (const value of values) yield* extend([...history, W(author, value, seen)]);
    if (history.some(op => op.author === author)) { yield* extend([...history, U(author, seen)]); yield* extend([...history, R(author, seen)]); }
  }
}
const show = h => h.map((op, i) => `${i}:${op.author} ${op.kind === "write" ? op.value : op.kind} [${op.seen}]`).join("  ");
// For each axis, the shortest history where two survivors differing ONLY on
// that axis show different final values.
const byAxis = new Map();
let count = 0;
const index = new Map(surv.map(c => [c.name, c]));
const partner = (c, axis, v) => index.get(AXES.map(a => a === axis ? v : c[a]).join("/"));
const axisValues = { family: Object.keys(families), blocked: ["consume", "retain"], redo: ["free", "guarded"], noEdit: ["push", "skip"], clear: ["clear", "keep"] };
for (const history of extend([])) {
  count++;
  const finals = new Map(surv.map(c => [c.name, evaluate(history, c).final]));
  for (const c of surv) for (const axis of AXES) for (const v of axisValues[axis]) {
    if (v <= c[axis]) continue;
    const d = partner(c, axis, v);
    if (!d || finals.get(c.name) === finals.get(d.name)) continue;
    const key = `${axis}: ${c[axis]} vs ${v}`;
    const score = history.length * 10 + new Set(history.map(o => o.author)).size;
    if (!byAxis.has(key) || byAxis.get(key).score > score) byAxis.set(key, { score, history, a: `${c.name}=${finals.get(c.name)}`, b: `${d.name}=${finals.get(d.name)}` });
  }
}
console.log(`\nsearched ${count} histories (<= ${maxOps} commands, writers A-C enumerated independently, values red/green, initial ${INITIAL})`);
console.log("single-choice value separations (shortest each):");
for (const [key, v] of [...byAxis].sort((x, y) => x[1].score - y[1].score)) console.log(`\n[${key}]\n  ${show(v.history)}\n  ${v.a}   ${v.b}`);
const none = AXES.flatMap(a => axisValues[a].flatMap(x => axisValues[a].filter(y => y > x).map(y => `${a}: ${x} vs ${y}`))).filter(k => { const [axis, rest] = k.split(": "); const [x, y] = rest.split(" vs "); return !byAxis.has(k) && surv.some(c => c[axis] === x && partner(c, axis, y)); });
console.log(`\nno value separation within this bound: ${none.join("; ") || "(none)"}`);
console.log("\nLynn's 6-command history: " + show(lynn6));
for (const name of ["X/consume/free/push/clear", "X2/consume/free/push/clear"]) console.log(`  ${name}: ${JSON.stringify(evaluate(lynn6, index.get(name)))}`);
export { evaluate, candidates, W, U, R };
