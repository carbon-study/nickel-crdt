// Asserts that exactly the variant adopted in docs/collection-contract.md
// matches the constraints and Ren's K1/K2 answers (2026-11-08).
const { evaluate, candidates, P, X, U, T, ABSENT } = await import("./model.mjs");
const traces = {
  // constraints (also in model.mjs)
  restore: [[P("A","red",[]), X("B",[0]), T("A",[0,1])], { 2: "restored", final: "red" }],
  restoreUndo: [[P("A","red",[]), X("B",[0]), T("A",[0,1]), U("A",[0,1,2])], { 3: "undone", final: ABSENT }],
  restore3: [[P("A","red",[]), X("B",[0]), X("C",[0]), T("A",[0,1,2])], { 3: "restored", final: "red" }],
  restoreHidden: [[P("A","red",[]), X("B",[0]), P("C","green",[0]), T("A",[0,1,2])], { final: "green" }],
  q13: [[P("A","red",[]), P("A","blue",[0]), P("B","green",[0,1]), U("A",[0,1,2])], { 3: "nothing", final: "green" }],
  equalPut: [[P("A","red",[]), P("B","red",[0]), U("A",[0,1])], { 2: "undone", final: ABSENT }],
  // proposed: an unseen equal-valued put is no edit, so it doesn't keep a
  // removed entry (by analogy with register f1; CodeRabbit #72).
  equalUnseen: [[P("A","red",[]), X("B",[0]), P("C","red",[0])], { final: ABSENT }],
  // Lamport time counts replicated facts only: A's do-nothing undo must not
  // advance her later put past B's concurrent one.
  lamport: [[P("A","red",[]), U("A",[0]), U("A",[0,1]), P("A","green",[0,1,2]), P("B","blue",[0,1])], { 2: "unavailable", final: "blue" }],
  // Ren's answers
  K1: [[P("A","red",[]), P("A","green",[0]), X("B",[0])], { final: "green" }],
  "K1'": [[P("A","red",[]), X("B",[0]), P("A","green",[0])], { final: "green" }],
  K2: [[P("A","red",[]), P("B","green",[0]), U("A",[0,1])], { 2: "nothing", final: "green" }],
  "K2+": [[P("A","red",[]), P("B","green",[0]), U("A",[0,1]), U("B",[0,1,2])], { final: "red" }],
};
let bad = 0;
const matching = candidates.filter(c => Object.values(traces).every(([h, want]) => { const g = evaluate(h, c); return Object.entries(want).every(([k, v]) => g[k] === v); }));
console.log("matching: " + matching.map(c => c.name).join(", "));
if (JSON.stringify(matching.map(c => c.name)) !== JSON.stringify(["observed/blocked"])) { bad++; console.log("FAIL expected exactly observed/blocked"); }
process.exit(bad ? 1 : 0);
