// Asserts the collection stories in docs/collection-contract.md under every option.
const { evaluate, candidates, P, X, U, T, ABSENT } = await import("./model.mjs");
const base = { removeMode: "observed", undoCreate: "blocked" };
const variant = (axis, v) => candidates.find(c => c.name === Object.values({ ...base, [axis]: v }).join("/"));
let bad = 0;
function story(q, axis, h, want) {
  const got = {};
  for (const v of Object.keys(want)) got[v] = evaluate(h, variant(axis, v));
  const finals = Object.fromEntries(Object.entries(got).map(([k, o]) => [k, o.final]));
  const ok = JSON.stringify(finals) === JSON.stringify(want);
  if (!ok) bad++;
  console.log(`${ok ? "ok  " : "FAIL"} ${q} ${axis}: ${JSON.stringify(got)}${ok ? "" : " want " + JSON.stringify(want)}`);
}
// K1 (fresh record) Alice's highlight is red; she changes it to green; Bo,
// having seen only red, removes it.
story("K1", "removeMode", [P("A", "red", []), P("A", "green", [0]), X("B", [0])], { observed: "green", removeWins: ABSENT });
// K1 (caller key, same axis) Bo removes Alice's reading-position key while
// Alice, unaware, saves a new position.
story("K1'", "removeMode", [P("A", "red", []), X("B", [0]), P("A", "green", [0])], { observed: "green", removeWins: ABSENT });
// K2 Alice adds a highlight; Bo changes its colour; Alice undoes her add.
story("K2", "undoCreate", [P("A", "red", []), P("B", "green", [0]), U("A", [0, 1])], { blocked: "green", allowed: "green", removes: ABSENT });
// K2 continued: then Bo undoes his colour change (separates blocked from allowed).
story("K2+", "undoCreate", [P("A", "red", []), P("B", "green", [0]), U("A", [0, 1]), U("B", [0, 1, 2])], { blocked: "red", allowed: ABSENT, removes: ABSENT });
// K2 then Bo restores: under removes, Alice's withdrawal is a removal Bo can
// restore (Lynn's #68 v3 review), giving his green back.
story("K2r", "undoCreate", [P("A", "red", []), P("B", "green", [0]), U("A", [0, 1]), T("B", [0, 1, 2])], { blocked: "green", allowed: "green", removes: "green" });
{ const o = evaluate([P("A", "red", []), P("B", "green", [0]), U("A", [0, 1]), T("B", [0, 1, 2], "r")], variant("undoCreate", "removes"));
  const ok = o.r === "restored"; if (!ok) bad++; console.log(`${ok ? "ok  " : "FAIL"} K2r removes: Bo's restore reports ${o.r}`); }
console.log(bad ? `${bad} FAILED` : "all collection stories hold");
process.exit(bad ? 1 : 0);
