// Checks two claims in docs/register-contract.md: (a) f2 and f4 rule out the
// other Y stack variants; (b) under Y, consume/retain doesn't change the f3
// retry or its redo twin.
process.env.MODEL_NO_SEARCH = "1";
const { evaluate, candidates, W, U, R } = await import("./model.mjs");
const c = n => candidates.find(x => x.name === n);
let bad = 0; const check = (ok, msg) => { if (!ok) bad++; console.log(`${ok ? "ok  " : "FAIL"} ${msg}`); };
const f2 = [W("A","red",[]), U("A",[0]), W("B","red",[0,1]), R("A",[0,1,2]), U("B",[0,1,2,3])];
const f4 = [W("A","red",[]), W("A","red",[0]), U("A",[0,1])];
check(evaluate(f2, c("Y/consume/free/skip/clear")).final === "red", "free redo fails f2 (red, not black)");
check(evaluate(f4, c("Y/consume/guarded/push/clear")).final === "red", "noEdit push fails f4 (red, not black)");
const f3 = [W("A","red",[]), W("B","green",[0]), U("A",[0,1]), U("B",[0,1]), U("A",[0,1,2,3])];
const twin = [W("A","red",[]), U("A",[0]), W("B","red",[0,1]), R("A",[0,1,2]), U("B",[0,1,2]), R("A",[0,1,2,3,4])];
for (const [name, h] of [["f3", f3], ["redo twin", twin]]) {
  const a = evaluate(h, c("Y/consume/guarded/skip/clear")), b = evaluate(h, c("Y/retain/guarded/skip/clear"));
  check(a.final === b.final, `${name}: consume ${a.final} = retain ${b.final} (reports ${JSON.stringify(a)} / ${JSON.stringify(b)})`);
}
process.exit(bad ? 1 : 0);
