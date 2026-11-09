// Keyed-collection candidates (nickel #68 prep), v3 after Lynn's review of v2.
// One entry key, one field, writers A/B/C.
//
// Commands:
//   put(v)   create the entry if absent in the author's view; otherwise a
//            register write to its field. An equal-valued put on a present
//            entry is no edit (register rule 1). Fresh-record insertion is a
//            put on an absent key whose key nobody else can name (§1 of the
//            packet), so it needs no separate command here.
//   remove   delete the entry (only if present in the author's view).
//   undo     the author's latest own item (put or remove or restore). Blocking
//            follows the register contract's undo rule (Y): another user's later
//            counted command on the entry blocks it, even if since undone; the
//            author's own later commands only while active. Redo is NOT
//            modelled.
//   restore  bring back the entry after removals by OTHER users: it masks
//            every effective removal by another user in the restorer's view
//            (observed-concurrent removals included). It is an action in the
//            restorer's own history (undoable by her).
//
// Fields: the visible field is the register over every counted put (causal
// maxima, deterministic winner). Restore discards nothing: a field write made
// while the entry was removed still takes part.
//
// Axes:
//   removeMode  observed | removeWins : a remove deletes only the puts it
//               observed (an unseen create OR field write keeps the entry), or
//               it also deletes concurrent unseen puts.                 (K1)
//   undoCreate  blocked | allowed | removes : is the undo of your creating put
//               blocked by another user's later edit (blocked); or does it go
//               ahead and withdraw only your put, so another user's field write
//               can keep the entry (allowed); or does it remove the entry, as a
//               remove observing the undoer's view (removes)?              (K2)
//
// usage: node model.mjs [maxOps]

import { pathToFileURL } from "node:url";
// Importing this module runs no report or search; only `node model.mjs` does.
const isMain = !!process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href;
const log = isMain ? console.log : () => {};
const AXES = { removeMode: ["observed", "removeWins"], undoCreate: ["blocked", "allowed", "removes"] };
const candidates = [];
for (const removeMode of AXES.removeMode) for (const undoCreate of AXES.undoCreate)
  candidates.push({ name: `${removeMode}/${undoCreate}`, removeMode, undoCreate });

const P = (author, value, seen, label) => ({ kind: "put", author, value, seen, label });
const X = (author, seen, label) => ({ kind: "remove", author, seen, label });
const U = (author, seen, label) => ({ kind: "undo", author, seen, label });
const T = (author, seen, label) => ({ kind: "restore", author, seen, label });
const ABSENT = "absent";

function evaluate(history, cand) {
  const ops = history.map((op, i) => ({ ...op, i }));
  const order = (a, b) => (ops[a].lamport - ops[b].lamport) || (ops[a].author < ops[b].author ? -1 : ops[a].author > ops[b].author ? 1 : a - b);
  const outcome = {}, stacks = {};
  const before = (a, b) => ops[b].view.includes(a);
  const active = (j, within) => !within.some(u => ops[u].kind === "undo" && !ops[u].noop && ops[u].target === j);
  const live = (within, kind) => within.filter(j => ops[j].kind === kind && !ops[j].noop && active(j, within));
  function state(within) {
    const restores = live(within, "restore");
    const removes = [...live(within, "remove"), ...within.filter(j => ops[j].kind === "undo" && ops[j].asRemove && !ops[j].noop)]
      .filter(r => !restores.some(t => ops[t].masks.includes(r)));
    const puts = live(within, "put").filter(p => ops[p].counted);
    const killed = p => removes.some(r => cand.removeMode === "observed" ? before(p, r) : (before(p, r) || !before(r, p)));
    if (!puts.some(p => !killed(p))) return ABSENT;
    const maxima = puts.filter(w => !puts.some(e => e !== w && before(w, e)));
    return ops[maxima.sort(order).at(-1)].value;
  }
  for (const op of ops) {
    op.view = op.seen.filter(j => ops[j].author === op.author || !ops[j].noop);
    // Lamport time from replicated facts only (own do-nothing commands are local)
    op.lamport = 1 + Math.max(0, ...op.view.filter(j => !ops[j].noop).map(j => ops[j].lamport));
    const st = stacks[op.author] ??= [];
    const say = v => { outcome[op.label ?? op.i] = v; };
    const now = state(op.view);
    if (op.kind === "put") {
      op.created = now === ABSENT;
      op.counted = op.created || op.value !== now; // equal-valued put on a present entry is no edit
      if (op.counted) st.push(op.i);
      continue;
    }
    if (op.kind === "remove") {
      if (now === ABSENT) { op.noop = true; say("nothing"); continue; }
      st.push(op.i); continue;
    }
    if (op.kind === "restore") {
      // every removal effect by another user: explicit removes and creator
      // withdrawals that act as removals (undoCreate = removes)
      const removalEffects = [...live(op.view, "remove"), ...op.view.filter(j => ops[j].kind === "undo" && ops[j].asRemove && !ops[j].noop)];
      op.masks = removalEffects.filter(r => ops[r].author !== op.author);
      if (now !== ABSENT || !op.masks.length) { op.noop = true; say("nothing"); continue; }
      st.push(op.i); say("restored"); continue;
    }
    // undo
    const w = st.at(-1);
    if (w === undefined) { op.noop = true; say("unavailable"); continue; }
    st.pop();
    const later = op.view.filter(e => e !== w && before(w, e) && !ops[e].noop && ops[e].kind !== "undo" && (ops[e].kind !== "put" || ops[e].counted));
    const blocking = later.filter(e => ops[e].author !== op.author || active(e, op.view));
    const creating = ops[w].kind === "put" && ops[w].created;
    const exempt = creating && cand.undoCreate !== "blocked";
    if (blocking.length && !exempt) { op.noop = true; say("nothing"); continue; }
    op.target = w; say("undone");
    if (creating && cand.undoCreate === "removes" && blocking.length) op.asRemove = true;
  }
  outcome.final = state(ops.filter(o => !o.noop).map(o => o.i));
  return outcome;
}

// ---- constraints (targeted traces) ----------------------------------------
const constraints = {
  // q40 + sequence profile: the victim restores another user's removal; the
  // entry comes back; the restore is her own action and she can undo it.
  restore: { history: [P("A", "red", []), X("B", [0]), T("A", [0, 1], "r")], expect: { r: "restored", final: "red" } },
  restoreUndo: { history: [P("A", "red", []), X("B", [0]), T("A", [0, 1]), U("A", [0, 1, 2], "u")], expect: { u: "undone", final: ABSENT } },
  // Lynn's three-writer trace: B and C remove concurrently; A sees both and
  // restores. Both observed removals are masked.
  restore3: { history: [P("A", "red", []), X("B", [0]), X("C", [0]), T("A", [0, 1, 2], "r")], expect: { r: "restored", final: "red" } },
  // Restore discards no field write: C changes the field to green while
  // concurrent with B's removal (C saw only the entry); A, seeing everything,
  // restores. Under removeWins C's write was hidden; it is not discarded.
  restoreHidden: { history: [P("A", "red", []), X("B", [0]), P("C", "green", [0]), T("A", [0, 1, 2], "r")], expect: { final: "green" } },
  // register rule (Y) for field writes: another user's later edit blocks an
  // undo of your field write (q13).
  q13: { history: [P("A", "red", []), P("A", "blue", [0]), P("B", "green", [0, 1]), U("A", [0, 1, 2], "u")], expect: { u: "nothing", final: "green" } },
  // an equal-valued put on a present entry is no edit (register rule 1, q17):
  // it doesn't block A's undo of her creation.
  equalPut: { history: [P("A", "red", []), P("B", "red", [0]), U("A", [0, 1], "u")], expect: { u: "undone", final: ABSENT } },
};
const survivors = [];
for (const cand of candidates) {
  const fails = [];
  for (const [q, { history, expect }] of Object.entries(constraints)) {
    const got = evaluate(history, cand);
    for (const [k, v] of Object.entries(expect)) if (got[k] !== v) fails.push(`${q}.${k}=${got[k]}`);
  }
  log(`${cand.name.padEnd(22)} ${fails.length ? "FAILS " + fails.join("; ") : "ok"}`);
  if (!fails.length) survivors.push(cand);
}

// ---- bounded search ---------------------------------------------------------
const maxOps = isMain ? Number(process.argv[2] ?? 4) : 0;
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
    for (const v of values) yield* extend([...history, P(author, v, seen)]);
    if (history.length) { yield* extend([...history, X(author, seen)]); yield* extend([...history, T(author, seen)]); }
    if (history.some(op => op.author === author)) yield* extend([...history, U(author, seen)]);
  }
}
const show = h => h.map((op, i) => `${i}:${op.author} ${op.kind}${op.value ? " " + op.value : ""} [${op.seen}]`).join("  ");
if (maxOps) {
  const index = new Map(survivors.map(c => [c.name, c]));
  const byAxis = new Map(); let count = 0;
  for (const history of extend([])) {
    count++;
    const finals = new Map(survivors.map(c => [c.name, evaluate(history, c).final]));
    for (const c of survivors) for (const axis of Object.keys(AXES)) {
      const [x, y] = AXES[axis];
      if (c[axis] !== x) continue;
      const d = index.get(Object.keys(AXES).map(a => a === axis ? y : c[a]).join("/"));
      if (!d || finals.get(c.name) === finals.get(d.name)) continue;
      const score = history.length * 10 + new Set(history.map(o => o.author)).size;
      if (!byAxis.has(axis) || byAxis.get(axis).score > score) byAxis.set(axis, { score, history, a: `${c.name}=${finals.get(c.name)}`, b: `${d.name}=${finals.get(d.name)}` });
    }
  }
  log(`\nsearched ${count} histories (<= ${maxOps} commands, writers A-C, values red/green)`);
  for (const axis of Object.keys(AXES)) { const v = byAxis.get(axis); log(v ? `\n[${axis}]\n  ${show(v.history)}\n  ${v.a}   ${v.b}` : `\n[${axis}] no value separation within the bound`); }
}
export { evaluate, candidates, P, X, U, T, ABSENT };
