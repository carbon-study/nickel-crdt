// The variant adopted in docs/register-contract.md from Ren's 2026-11-08 follow-up answers: re-checks it
// against q13-q17 and every follow-up story's chosen option.
const { evaluate, candidates, W, U, R } = await import("./model.mjs");
const quiz = {
  q13: [[W("A","red",[]), W("B","green",[0]), U("A",[0,1])], { 2: "nothing", final: "green" }],
  q14: [[W("A","red",[]), W("B","green",[0]), U("A",[0,1]), R("A",[0,1,2])], { 3: "nothing", final: "green" }],
  q15: [[W("A","red",[]), W("B","green",[0]), U("A",[0,1]), U("B",[0,1,2])], { 2: "nothing", 3: "undone", final: "red" }],
  q16: [[W("A","red",[]), W("B","blue",[]), U("B",[0,1])], { 2: "undone", final: "red" }],
  q16b: [[W("A","red",[]), W("B","blue",[]), U("A",[0,1])], { 2: "undone" }],
  q17: [[W("A","red",[]), W("B","red",[0]), U("A",[0,1])], { final: "black" }],
  f1: [[W("A","red",[]), W("B","red",[0]), U("A",[0])], { final: "black" }],
  f2: [[W("A","red",[]), U("A",[0]), W("B","red",[0,1]), R("A",[0,1,2]), U("B",[0,1,2,3])], { 3: "nothing", final: "black" }],
  // f3: "red (it was used up)": the retry finds no item.
  f3: [[W("A","red",[]), W("B","green",[0]), U("A",[0,1]), U("B",[0,1]), U("A",[0,1,2,3])], { 4: "unavailable", final: "red" }],
  f4: [[W("A","red",[]), W("A","red",[0]), U("A",[0,1])], { final: "black" }],
  f5: [[W("A","red",[]), W("B","green",[0]), W("C","red",[0,1]), U("B",[0,1]), U("A",[0,1,2,3])], { 4: "nothing" }],
};
// Ren, 2026-11-08 ("this is the composing, right? I would assume nothing
// happens"): another user's later edit still blocks after he undoes it, for
// undo and redo alike. p3 (a blocked redo is used up) remains a proposal.
const proposed = {
  f6: [[W("A","red",[]), W("B","green",[0]), U("B",[0,1]), U("A",[0,1,2])], { 3: "nothing", final: "red" }],
  f7: [[W("A","red",[]), U("A",[0]), W("B","red",[0,1]), U("B",[0,1,2]), R("A",[0,1,2,3])], { 4: "nothing", final: "black" }],
  // Lamport time counts replicated facts only: A's do-nothing undo (local)
  // must not advance her later write past B's concurrent one (CodeRabbit #71).
  lamport: [[W("A","red",[]), U("A",[0]), U("A",[0,1]), W("A","green",[0,1,2]), W("B","blue",[0,1])], { 2: "unavailable", final: "blue" }],
  // own later edits block only while active: two own undos in a row work.
  own: [[W("A","red",[]), W("A","green",[0]), U("A",[0,1]), U("A",[0,1,2])], { 2: "undone", 3: "undone", final: "black" }],
  // p3: a blocked redo uses up its entry; retrying after Bo's undo does nothing.
  p3: [[W("A","red",[]), U("A",[0]), W("B","red",[0,1]), R("A",[0,1,2]), U("B",[0,1,2]), R("A",[0,1,2,3,4])], { 3: "nothing", 5: "nothing", final: "black" }],
};
Object.assign(quiz, proposed);
let bad = 0;
for (const name of ["Y/consume/guarded/skip/clear", "Y/consume/guarded/skip/keep"]) {
  const c = candidates.find(x => x.name === name);
  for (const [q, [h, want]] of Object.entries(quiz)) {
    const got = evaluate(h, c);
    for (const [k, v] of Object.entries(want)) if (got[k] !== v) { bad++; console.log(`FAIL ${name} ${q}.${k}=${got[k]} want ${v}`); }
  }
  console.log(`${name}: checked ${Object.keys(quiz).length} histories`);
}
// which survivors match ALL answers?
const all = candidates.filter(c => Object.values(quiz).every(([h, want]) => { const g = evaluate(h, c); return Object.entries(want).every(([k, v]) => g[k] === v); }));
console.log("candidates matching every answer: " + all.map(c => c.name).join(", "));
// f3's report (used up -> no item) excludes retain; clear/keep is held.
const expected = ["Y/consume/guarded/skip/clear", "Y/consume/guarded/skip/keep"];
if (JSON.stringify(all.map(c => c.name).sort()) !== JSON.stringify(expected)) { bad++; console.log("FAIL matching set differs from " + expected.join(", ")); }
process.exit(bad ? 1 : 0);
