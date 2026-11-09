// Checks claims in docs/register-contract.md: f2 and f4 rule out the other Y
// stack variants, and f3's consume/retain difference is in the report only.
// Blocked-redo retention is not a model variant, so no claim is made about it.
process.env.MODEL_NO_SEARCH = "1";
const { evaluate, candidates, W, U, R } = await import("./model.mjs");
const c = n => candidates.find(x => x.name === n);
let bad = 0; const check = (ok, msg) => { if (!ok) bad++; console.log(`${ok ? "ok  " : "FAIL"} ${msg}`); };
const f2 = [W("A","red",[]), U("A",[0]), W("B","red",[0,1]), R("A",[0,1,2]), U("B",[0,1,2,3])];
const f4 = [W("A","red",[]), W("A","red",[0]), U("A",[0,1])];
check(evaluate(f2, c("Y/consume/free/skip/clear")).final === "red", "free redo fails f2 (red, not black)");
check(evaluate(f4, c("Y/consume/guarded/push/clear")).final === "red", "noEdit push fails f4 (red, not black)");
// f3 under Y: same colour for consume and retain, but different reports; the
// answered "used up" is consume (no item on retry).
const f3 = [W("A","red",[]), W("B","green",[0]), U("A",[0,1]), U("B",[0,1]), U("A",[0,1,2,3])];
const a = evaluate(f3, c("Y/consume/guarded/skip/clear")), b = evaluate(f3, c("Y/retain/guarded/skip/clear"));
check(a.final === "red" && b.final === "red" && a[4] === "unavailable" && b[4] === "nothing", `f3: both red; consume reports ${a[4]}, retain ${b[4]}`);
process.exit(bad ? 1 : 0);
