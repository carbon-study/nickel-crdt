// Asserts each user-facing story in docs/register-contract.md (f1–f5) against model.mjs:
// the merged value after every step and every command report, for both
// options. Exits nonzero on any mismatch. Base = the proposed defaults
// (X, guarded redo, no-edit writes skip the stacks, clear) with "consume"
// for f3's still-open choice.
const { evaluate, candidates, W, U, R } = await import("./model.mjs");
const base = { family: "X", blocked: "consume", redo: "guarded", noEdit: "skip", clear: "clear" };
const variant = (axis, v) => {
  const o = { ...base, [axis]: v };
  if (o.family === "E" || o.family === "P") o.noEdit = "push";
  const name = Object.values(o).join("/");
  const c = candidates.find(x => x.name === name);
  if (!c) throw Error("no candidate " + name);
  return c;
};
let failures = 0;
function story(q, axis, h, options) {
  for (const [v, want] of Object.entries(options)) {
    const c = variant(axis, v);
    const values = h.map((_, i) => evaluate(h.slice(0, i + 1), c).final);
    const { final, ...reports } = evaluate(h, c);
    const got = { values, reports };
    const ok = JSON.stringify(got) === JSON.stringify(want);
    if (!ok) failures++;
    console.log(`${ok ? "ok  " : "FAIL"} ${q} ${axis}=${v}: ${JSON.stringify(got)}${ok ? "" : "  want " + JSON.stringify(want)}`);
  }
  const finals = Object.values(options).map(o => o.values.at(-1));
  if (new Set(finals).size < 2) { failures++; console.log(`FAIL ${q}: the options don't separate`); }
}
// f1 Alice red; Bo sees red, taps red; before seeing Bo's tap, Alice undoes.
story("f1", "family", [W("A", "red", []), W("B", "red", [0]), U("A", [0])], {
  X: { values: ["red", "red", "black"], reports: { 2: "undone" } },
  E: { values: ["red", "red", "red"], reports: { 2: "undone" } },
});
// f2 Alice red, undoes; Bo (seeing the undo) sets red; Alice redoes; Bo undoes.
story("f2", "redo", [W("A", "red", []), U("A", [0]), W("B", "red", [0, 1]), R("A", [0, 1, 2]), U("B", [0, 1, 2, 3])], {
  guarded: { values: ["red", "black", "red", "red", "black"], reports: { 1: "undone", 3: "nothing", 4: "undone" } },
  free: { values: ["red", "black", "red", "red", "red"], reports: { 1: "undone", 3: "redone", 4: "undone" } },
});
// f3 Alice red; Bo green; Alice undo (nothing); Bo undoes; Alice undoes again.
story("f3", "blocked", [W("A", "red", []), W("B", "green", [0]), U("A", [0, 1]), U("B", [0, 1]), U("A", [0, 1, 2, 3])], {
  consume: { values: ["red", "green", "green", "red", "red"], reports: { 2: "nothing", 3: "undone", 4: "unavailable" } },
  retain: { values: ["red", "green", "green", "red", "black"], reports: { 2: "nothing", 3: "undone", 4: "undone" } },
});
// f4 Alice taps red twice, then undoes once.
story("f4", "noEdit", [W("A", "red", []), W("A", "red", [0]), U("A", [0, 1])], {
  skip: { values: ["red", "red", "black"], reports: { 2: "undone" } },
  push: { values: ["red", "red", "red"], reports: { 2: "undone" } },
});
// f5 Alice red; Bo green; Cara (seeing green) red; Bo undoes without seeing
// Cara; everyone syncs; Alice undoes; Cara undoes.
story("f5", "family", [W("A", "red", []), W("B", "green", [0]), W("C", "red", [0, 1]), U("B", [0, 1]), U("A", [0, 1, 2, 3]), U("C", [0, 1, 2, 3, 4])], {
  X: { values: ["red", "green", "red", "red", "red", "red"], reports: { 3: "undone", 4: "nothing", 5: "undone" } },
  X2: { values: ["red", "green", "red", "red", "red", "black"], reports: { 3: "undone", 4: "undone", 5: "undone" } },
});
console.log(failures ? `${failures} FAILED` : "all stories hold");
process.exit(failures ? 1 : 0);
