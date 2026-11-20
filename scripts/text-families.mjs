// The text gate's contract families, their Remaining locator controls and the cache-safety control (#197).
// check-edit-proofs.mjs loads this module (by a literal import) only when a family or cache-safety runs, or in
// gatepreflight, so native mutation runs never load these modules; selected shard runs audit that at runtime.
import {checkDeleteContracts} from './check-delete-contracts.mjs';
import {checkEventContracts} from './check-event-contracts.mjs';
import {checkOperationContracts} from './check-operation-contracts.mjs';
import {checkReplayContracts} from './check-replay-contracts.mjs';
import {checkBasisContracts} from './check-basis-contracts.mjs';
import {checkScheduleContracts} from './check-schedule-contracts.mjs';
import {checkPastContracts} from './check-past-contracts.mjs';
import {checkRemainingContracts,checkRemainingCallLocator} from './check-remaining-contracts.mjs';
import {checkCounterContracts} from './check-counter-contracts.mjs';
import {checkPushContracts} from './check-push-contracts.mjs';
import {checkVectorContracts} from './check-vector-contracts.mjs';
import {checkScalarContracts} from './check-loop-contracts.mjs';
import {checkIdentityContracts} from './check-identity-contracts.mjs';
import {checkWriterContracts} from './check-writer-contracts.mjs';
import {checkPlanContracts} from './check-plan-contracts.mjs';
import {checkContainmentContracts} from './check-containment-contracts.mjs';
import {checkAcceptedContracts} from './check-accepted-contracts.mjs';
import {checkSpecContracts} from './check-spec-contracts.mjs';
import {checkPrivateContracts} from './check-private-contracts.mjs';
import {checkSharedContracts} from './check-shared-contracts.mjs';
import {checkCommitContracts} from './check-commit-contracts.mjs';
import {checkCacheSafety} from './check-cache-safety.mjs';
export {checkRemainingCallLocator,checkCacheSafety};
// Execution order is this object's key order.
export const families={delete:checkDeleteContracts,event:checkEventContracts,operation:checkOperationContracts,replay:checkReplayContracts,basis:checkBasisContracts,schedule:checkScheduleContracts,past:checkPastContracts,remaining:checkRemainingContracts,counter:checkCounterContracts,push:checkPushContracts,vector:checkVectorContracts,scalar:checkScalarContracts,identity:checkIdentityContracts,writer:checkWriterContracts,plan:checkPlanContracts,containment:checkContainmentContracts,accepted:checkAcceptedContracts,spec:checkSpecContracts,private:checkPrivateContracts,shared:checkSharedContracts,commit:checkCommitContracts};
