// The text gate's unit-group table (#198): names and modules only, no imports, so a module that needs the table
// (the smoke consumer, the record binding) does not take the family loaders' import closure as its own code.
// The remaining families were converted in #198; UNCONVERTED stays as the explicit conservative list (now empty).
// Execution order.
export const FAMILY_ORDER=['delete','event','operation','replay','basis','schedule','past','remaining','counter','push','vector','scalar','identity','writer','plan','containment','accepted','spec','private','shared','commit'];
export const UNCONVERTED=[];
// Unit groups (#198): every family plus core-a's cache-safety and the smoke gate. Each group is selected whole. FAMILY_ORDER
// alone is what contract-family arguments (contracts:, contracts-except:) range over.
export const UNIT_GROUPS=[...FAMILY_ORDER,'cache-safety','smoke'];
// Each family's module (its code input is that module's import closure) and its loader.
// smoke's code is its runner check-proofs.mjs (whose closure includes smoke-units.mjs and the loop controls).
export const FAMILY_MODULES={delete:'check-delete-contracts.mjs',event:'check-event-contracts.mjs',operation:'check-operation-contracts.mjs',replay:'check-replay-contracts.mjs',basis:'check-basis-contracts.mjs',schedule:'check-schedule-contracts.mjs',past:'check-past-contracts.mjs',remaining:'check-remaining-contracts.mjs',counter:'check-counter-contracts.mjs',push:'check-push-contracts.mjs',vector:'check-vector-contracts.mjs',scalar:'check-loop-contracts.mjs',identity:'check-identity-contracts.mjs',writer:'check-writer-contracts.mjs',plan:'check-plan-contracts.mjs',containment:'check-containment-contracts.mjs',accepted:'check-accepted-contracts.mjs',spec:'check-spec-contracts.mjs',private:'check-private-contracts.mjs',shared:'check-shared-contracts.mjs',commit:'check-commit-contracts.mjs'};
export const UNIT_MODULES={...FAMILY_MODULES,'cache-safety':'check-cache-safety.mjs',smoke:'check-proofs.mjs'};
