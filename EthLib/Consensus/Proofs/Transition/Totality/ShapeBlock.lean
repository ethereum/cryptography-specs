module

public import EthLib.Consensus.Proofs.Transition.Totality.Shape
import EthLib.Consensus.Proofs.Mutators
import EthLib.Consensus.Proofs.PayloadTimeliness
import EthLib.Consensus.Proofs.Transition.Block
import EthLib.Consensus.Proofs.Transition.BuilderRequests
import EthLib.Consensus.Proofs.Transition.EpochPending
import EthLib.Consensus.Proofs.Transition.Execution
import EthLib.Consensus.Proofs.Transition.ForkBoundary
import EthLib.Consensus.Proofs.Transition.Invariants
import EthLib.Consensus.Proofs.Transition.Operations
import EthLib.Consensus.Proofs.Transition.ParentPayload
import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
import EthLib.Consensus.Proofs.Transition.Requests
import EthLib.Consensus.Proofs.Transition.StateTransition
import EthLib.Consensus.Proofs.Transition.TargetFlags
import EthLib.Consensus.Proofs.Transition.Totality.PendingDeposits
import EthLib.Consensus.Proofs.Transition.ValidatorCaps
import EthLib.Consensus.Proofs.Transition.Withdrawals

/-!
# Proofs: a block keeps the shape of the state

A new validator appends one entry to each list indexed by the registry, and starts within its cap.

No other step of a block changes those lengths or an existing effective balance.

A change of credentials never lowers a cap, and a queued consolidation stays in the registry.

So a block keeps the shape, and so does a block applied across the forks.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

section Steps

variable {fork : Fork} {engine : ExecutionEngine preset fork} {s t : BeaconState preset fork}

/-- The facts of the shape on the flags, the scores and the queue of consolidations. -/
private def Listed (s : BeaconState preset fork) : Prop :=
  ParticipationMatches s ∧ InactivityScoresMatch s ∧ ConsolidationsInside s

/-- A step keeps the size of the registry and leaves the flags, scores and queue unchanged. -/
private def Kept (s t : BeaconState preset fork) : Prop :=
  t.validators.data.size = s.validators.data.size ∧
    t.previousEpochParticipation = s.previousEpochParticipation ∧
    t.currentEpochParticipation = s.currentEpochParticipation ∧
    t.inactivityScores = s.inactivityScores ∧ t.pendingConsolidations = s.pendingConsolidations

private theorem Kept.refl (s : BeaconState preset fork) : Kept s s := ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem Kept.trans {u : BeaconState preset fork} (one : Kept s t) (two : Kept t u) :
    Kept s u :=
  ⟨two.1.trans one.1, two.2.1.trans one.2.1, two.2.2.1.trans one.2.2.1,
    two.2.2.2.1.trans one.2.2.2.1, two.2.2.2.2.trans one.2.2.2.2⟩

private theorem Kept.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (kept : ∀ a x b, step a x = .ok b → Kept a b) {items : List α}
    (computed : items.foldlM step s = .ok t) : Kept s t :=
  foldlM_ok_invariant (Kept s) (fun _ _ _ before ok => before.trans (kept _ _ _ ok))
    (Kept.refl s) computed

/-- A step that keeps the registry size and the lists keeps the facts. -/
private theorem Kept.listed (kept : Kept s t) (listed : Listed s) : Listed t := by
  obtain ⟨size, previous, current, scores, queue⟩ := kept
  obtain ⟨flags, scored, inside⟩ := listed
  refine ⟨fun altair => ?_, fun altair => ?_, fun electra => ?_⟩
  · rw [previous, current, size]
    exact flags altair
  · rw [scores, size]
    exact scored altair
  · rw [queue, size]
    exact inside electra

/-- A fold whose every step keeps the facts keeps them. -/
private theorem listed_foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (each : ∀ a x b, step a x = .ok b → Listed a → Listed b) {items : List α}
    (computed : items.foldlM step s = .ok t) (listed : Listed s) : Listed t :=
  foldlM_ok_invariant Listed (fun _ _ _ held ok => each _ _ _ ok held) listed computed

/-! ### Steps that keep the registry size and the lists -/

private theorem Kept.setValidatorAt {i : Nat} {v : Validator}
    (ok : s.setValidatorAt i v = .ok t) : Kept s t := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok ok
  exact ⟨(sameSizes_putValidator _ _ _).1, rfl, rfl, rfl, rfl⟩

private theorem Kept.setValidator {i : ValidatorIndex} {v : Validator}
    (ok : s.setValidator i v = .ok t) : Kept s t :=
  Kept.setValidatorAt (by rwa [← setValidator_eq_setValidatorAt])

private theorem Kept.setBalance {i : ValidatorIndex} {b : Gwei}
    (ok : s.setBalance i b = .ok t) : Kept s t := by
  obtain ⟨_, rfl⟩ := setBalance_ok ok
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem Kept.increase {i : ValidatorIndex} {amount : Gwei}
    (ok : increaseBalance s i amount = .ok t) : Kept s t := by
  obtain ⟨_, set⟩ := increaseBalance_ok ok
  exact Kept.setBalance set

private theorem Kept.decrease {i : ValidatorIndex} {amount : Gwei}
    (ok : decreaseBalance s i amount = .ok t) : Kept s t := by
  obtain ⟨_, set⟩ := decreaseBalance_ok ok
  exact Kept.setBalance set

private theorem Kept.exit {i : ValidatorIndex} (ok : initiateValidatorExit config s i = .ok t) :
    Kept s t := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok ok
  · exact Kept.refl _
  · obtain ⟨_, _, rfl⟩ := exitQueue_eq queue
    have kept := Kept.setValidator set
    exact kept

private theorem Kept.slash {i : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config s i whistleblower = .ok t) : Kept s t := by
  obtain ⟨_, _, _, marked, _, _, slashings, _, _, _, _, last, exited, _, _, set,
    _, _, _, lowered, _, _, raised, paid, rfl⟩ := slashValidator_ok ok
  have first := (Kept.exit exited).trans (Kept.setValidator set)
  have second : Kept marked last :=
    (show Kept marked { marked with slashings } from ⟨rfl, rfl, rfl, rfl, rfl⟩).trans
      ((Kept.decrease lowered).trans ((Kept.increase raised).trans (Kept.increase paid)))
  refine (first.trans second).trans ?_
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem Kept.proposerSlashing {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks s slashing = .ok t) : Kept s t := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact Kept.slash slashed

private theorem Kept.attesterSlashing {slashing : AttesterSlashing preset fork}
    (ok : processAttesterSlashing config checks s slashing = .ok t) : Kept s t := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  refine foldlM_ok_invariant (fun step : BeaconState preset fork × Bool => Kept s step.1)
    (fun step _ _ before ok => ?_) (Kept.refl s) folded
  obtain ⟨middle, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, slashed, rfl⟩ := ok
    exact before.trans (Kept.slash slashed)
  · cases ok
    exact before

private theorem Kept.exitChurn {electra : .pectra ≤ fork} {balance : Gwei} {epoch : Epoch}
    (ok : computeExitEpochAndUpdateChurn config s electra balance = .ok (t, epoch)) :
    Kept s t := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, ok⟩ := ok
  cases ok
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem Kept.consolidationChurn {electra : .pectra ≤ fork} {balance : Gwei}
    {epoch : Epoch}
    (ok : computeConsolidationEpochAndUpdateChurn config s electra balance = .ok (t, epoch)) :
    Kept s t := by
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, ok⟩ := ok
  cases ok
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem Kept.partialWithdrawal {electra : .pectra ≤ fork} {index : ValidatorIndex}
    {validator : Validator} {amount owed : Gwei}
    (ok : requestPartialWithdrawal config s electra index validator amount owed = .ok t) :
    Kept s t := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at ok
  obtain ⟨_, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at ok
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := ok
    exact (Kept.exitChurn churned).trans ⟨rfl, rfl, rfl, rfl, rfl⟩
  · cases ok
    exact Kept.refl _

private theorem Kept.withdrawalRequest {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t) : Kept s t := by
  rcases withdrawalRequest_cases ok with rfl | ⟨_, exited⟩ | ⟨_, _, _, withdrawn⟩
  · exact Kept.refl _
  · exact Kept.exit exited
  · exact Kept.partialWithdrawal withdrawn

private theorem Kept.depositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (ok : processDepositRequest s electra request = .ok t) : Kept s t := by
  obtain ⟨start, recorded⟩ := recordDepositRequestsStart_eq (state := s) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit,
    bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, rfl⟩ := ok
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem Kept.excess {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : queueExcessActiveBalance s electra index = .ok t) : Kept s t := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, set, rfl⟩ := ok
    exact (Kept.setBalance set).trans ⟨rfl, rfl, rfl, rfl, rfl⟩
  · cases ok
    exact Kept.refl _

private theorem Kept.compounding {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : switchToCompoundingValidator s electra index = .ok t) : Kept s t := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨_, _, _, set, queued⟩ := ok
  exact (Kept.setValidator set).trans (Kept.excess queued)

private theorem Kept.withdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (ok : processWithdrawals s capella payload = .ok t) : Kept s t := by
  have expected {a b : BeaconState preset fork} {expected : ExpectedWithdrawals}
      (applied : applyExpectedWithdrawals a capella expected = .ok b) : Kept a b := by
    apply applyExpectedWithdrawals_of_setters Kept Kept.refl (fun one two => one.trans two)
      (fun withdrawn => by rw [applyWithdrawal_eq withdrawn]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
      _ _ _ _ _ _ applied
    all_goals exact fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
  unfold processWithdrawals at ok
  split at ok
  · split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, applied⟩ := ok
      exact expected applied
    · cases ok
      exact Kept.refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, applied⟩ := ok
    exact expected applied

private theorem Kept.blockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (ok : processBlockExecution config checks engine s body bellatrix = .ok t) : Kept s t := by
  have payload {a b : BeaconState preset fork}
      {execution : .bellatrix ≤ fork ∧ fork < .glamsterdam}
      (paid : processExecutionPayload config engine a body execution = .ok b) : Kept a b := by
    obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok paid
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  unfold processBlockExecution at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, withdrawn, bid⟩ := ok
    obtain ⟨_, rfl⟩ := processExecutionPayloadBid_eq bid
    exact (Kept.withdrawals withdrawn).trans ⟨rfl, rfl, rfl, rfl, rfl⟩
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, withdrawn, paid⟩ := ok
    exact (Kept.withdrawals withdrawn).trans (payload paid)
  · dsimp only at ok
    split at ok
    · exact payload ok
    · cases ok
      exact Kept.refl _

/-! ### Steps that grow the registry, set flags or queue a consolidation -/

/-- A new validator keeps the facts. -/
private theorem listed_add {key : Cryptography.Bls.BLSPubkey} {credentials : Bytes32}
    {amount : Gwei} (ok : addValidatorToRegistry s key credentials amount = .ok t)
    (listed : Listed s) : Listed t := by
  obtain ⟨flags, scored, inside⟩ := listed
  obtain ⟨flags', scored'⟩ := addValidatorToRegistry_matches ok flags scored
  refine ⟨flags', scored', fun electra c member => ?_⟩
  rw [addValidatorToRegistry_pendingConsolidations ok] at member
  -- The registry grows by one validator.
  have grows : s.validators.data.size ≤ t.validators.data.size := by
    rw [addValidatorToRegistry_validators_eq_push ok, Array.size_push]
    exact Nat.le_succ _
  have held := inside electra c member
  exact ⟨Nat.lt_of_lt_of_le held.1 grows, Nat.lt_of_lt_of_le held.2 grows⟩

/-- A deposit keeps the facts. -/
private theorem listed_deposit {before : fork < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks before s deposit = .ok t) (listed : Listed s) :
    Listed t := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok ok
  have start : Listed { s with eth1DepositIndex := fun _ => next } := listed
  rcases applyDeposit_cases applied with rfl | ⟨_, _, _, rfl | added, rfl⟩ | ⟨_, pending⟩
  · exact start
  · exact start
  · have grown := listed_add added start
    exact grown
  · rcases applyPendingDeposit_cases pending with rfl | ⟨_, raised⟩ | ⟨_, added⟩
    · exact start
    · exact (Kept.increase raised).listed start
    · exact listed_add added start

/-- An attestation keeps the facts.

From Altair it sets flags in place, and before Altair it records a pending attestation. -/
private theorem listed_attestation {attestation : Attestation preset fork} {parentSlot : Slot}
    (ok : processAttestation config checks s parentSlot attestation = .ok t)
    (listed : Listed s) : Listed t := by
  by_cases altair : Fork.altair ≤ fork
  · simp only [processAttestation, altair, ↓reduceDIte] at ok
    unfold processAttestationAltair at ok
    simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      ⟨updated, _⟩, folded, _, _, _, raisedOk, final⟩ := ok
    have sized := (foldlM_addAttesterFlags_target folded).1
    obtain ⟨flags, scored, inside⟩ := listed
    -- The new flags have the length of the flags that they replace.
    have flagged : Listed (setEpochParticipation s
        (attestation.data.target.epoch == getCurrentEpoch s) updated) := by
      cases current : (attestation.data.target.epoch == getCurrentEpoch s) <;>
        simp only [current, setEpochParticipation, Bool.false_eq_true, ↓reduceIte] at sized ⊢
      · exact ⟨fun altair => ⟨sized.trans (flags altair).1, (flags altair).2⟩, scored, inside⟩
      · exact ⟨fun altair => ⟨(flags altair).1, sized.trans (flags altair).2⟩, scored, inside⟩
    have raised := (Kept.increase raisedOk).listed flagged
    split at final
    · rw [recordPaymentWeight_eq final]
      exact raised
    · cases final
      exact raised
  · obtain ⟨_, _, _, _, _, recorded, _⟩ := processAttestation_records (Nat.lt_of_not_le altair) ok
    have kept := recordPendingAttestation_ok recorded
    split at kept
    all_goals
      obtain ⟨_, rest⟩ := kept
      rw [← rest] at listed
      exact listed

/-- A queued consolidation of two validators of the registry keeps the facts. -/
private theorem listed_queueConsolidation {electra : .pectra ≤ fork}
    {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (sourceInside : sourceIndex.toNat < s.validators.data.size)
    (targetInside : targetIndex.toNat < s.validators.data.size)
    (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t)
    (listed : Listed s) : Listed t := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff, Base.Uint64.addChecked_ok_iff, pure, Except.pure] at ok
  obtain ⟨⟨churned, epoch⟩, churn, _, _, marked, set, pending, appended, ok⟩ := ok
  simp only [Except.ok.injEq] at ok
  subst ok
  have kept := (Kept.consolidationChurn churn).trans (Kept.setValidator set)
  obtain ⟨flags, scored, -⟩ := kept.listed listed
  refine ⟨flags, scored, fun electra' c member => ?_⟩
  rw [kept.1]
  have pushed := appendWithinLimit_data appended
  simp only at member
  rw [pushed, Array.mem_push] at member
  rcases member with old | rfl
  · rw [kept.2.2.2.2] at old
    exact listed.2.2 electra' c old
  · exact ⟨sourceInside, targetInside⟩

/-- A consolidation request keeps the facts. -/
private theorem listed_consolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (ok : processConsolidationRequest config s electra request = .ok t) (listed : Listed s) :
    Listed t := by
  have inside {i : ValidatorIndex} {v : Validator} (found : s.validators.data[i.toNat]? = some v) :
      i.toNat < s.validators.data.size :=
    (Array.getElem?_eq_some_iff.mp found).1
  unfold processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact listed)
    | exact (Kept.compounding (liftAccessor_ok.mp ok)).listed listed
    | exact listed_queueConsolidation
        (inside (getElem?_toNat_of_ofNatChecked (by assumption)))
        (inside (getElem?_toNat_of_ofNatChecked (by assumption))) ok listed

/-- The requests of the execution layer keep the facts. -/
private theorem listed_executionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (ok : processExecutionRequests config s body electra = .ok t) (listed : Listed s) :
    Listed t := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, deposits, _, withdrawals, consolidations⟩ := ok
  exact listed_foldlM (fun _ _ _ ok => listed_consolidationRequest ok) consolidations <|
    (Kept.foldlM (fun _ _ _ => Kept.withdrawalRequest) withdrawals).listed <|
    (Kept.foldlM (fun _ _ _ => Kept.depositRequest) deposits).listed listed

/-- From Gloas, the payload of the parent keeps the facts. -/
private theorem listed_parentPayload {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (ok : processParentExecutionPayload config checks s gloas body = .ok t)
    (listed : Listed s) : Listed t := by
  rcases processParentExecutionPayload_ok ok with ⟨-, -, rfl⟩ |
    ⟨-, settled, _, _, _, _, _, _, settledOk, depositsOk, withdrawalsOk, consolidationsOk,
      buildersOk, exitsOk, -, rfl⟩
  · exact listed
  have settled : Kept s settled := by
    rw [settleParentPayment_eq settledOk]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have requested := listed_foldlM (fun _ _ _ ok => listed_consolidationRequest ok)
    consolidationsOk <|
    (Kept.foldlM (fun _ _ _ => Kept.withdrawalRequest) withdrawalsOk).listed <|
    (Kept.foldlM (fun _ _ _ => Kept.depositRequest) depositsOk).listed (settled.listed listed)
  have builders := Kept.foldlM (fun _ _ _ ok => by
    obtain ⟨_, rfl⟩ := processBuilderDepositRequest_eq ok
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩) buildersOk
  have exits := Kept.foldlM (fun _ _ _ ok => by
    obtain ⟨_, rfl⟩ := processBuilderExitRequest_eq ok
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩) exitsOk
  exact (show Kept _ _ from (builders.trans exits).trans ⟨rfl, rfl, rfl, rfl, rfl⟩).listed
    requested

/-- A block keeps the facts on the flags, the scores and the queue. -/
private theorem processBlock_listed {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine s block = .ok t) (listed : Listed s) :
    Listed t := by
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput computed
  have head : Listed input := started.step_of (fun a b => Listed a → Listed b) (fun _ => id)
    (fun one two => two ∘ one) (fun _ paid => listed_parentPayload paid)
    (fun headed => by
      obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headed
      exact id)
    (fun _ executed => (Kept.blockExecution executed).listed)
    (fun revealed => by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealed
      exact id)
    (fun _ voted held => by
      obtain ⟨_, _, rest⟩ := processEth1Data_eq voted
      rw [← rest] at held
      exact held)
    listed
  obtain ⟨_, _, _, proposersOk, slashingsOk, attestedOk, rest⟩ :=
    processOperations_folds_of (fun a b => Listed a → Listed b) (fun _ => id)
      (fun one two => two ∘ one) (fun deposited => listed_deposit deposited)
      (fun exited => (Kept.exit (processVoluntaryExit_initiates exited)).listed)
      (fun changed => by
        obtain ⟨_, _, _, _, _, set⟩ := processBlsToExecutionChange_ok changed
        exact (Kept.setValidator set).listed)
      (fun requested => listed_executionRequests requested)
      (fun attested => by rw [processPayloadAttestation_eq attested]; exact id) operated
  have operatedListed := rest <|
    listed_foldlM (fun _ _ _ ok => listed_attestation ok) attestedOk <|
    (Kept.foldlM (fun _ _ _ => Kept.attesterSlashing) slashingsOk).listed <|
    (Kept.foldlM (fun _ _ _ => Kept.proposerSlashing) proposersOk).listed head
  split at synced
  · obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
    exact operatedListed
  · cases synced
    exact operatedListed

end Steps

/-- A block keeps the shape of the state.

The activation balance must be at most the cap of compounding credentials.

Then a switch to compounding credentials never lowers a cap. -/
theorem processBlock_shaped {fork : Fork} {engine : ExecutionEngine preset fork}
    {state after : BeaconState preset fork} {block : BeaconBlock preset fork}
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (computed : processBlock config checks engine state block = .ok after)
    (shaped : Shaped state) : Shaped after := by
  have listed := processBlock_listed computed
    ⟨shaped.participationMatches, shaped.inactivityScoresMatch, shaped.inside⟩
  exact ⟨(frame_processBlock computed).balancesMatch shaped.balancesMatch, listed.1, listed.2.1,
    processBlock_capped compounding computed shaped.capped, listed.2.2⟩

/-- A run of slots across the forks keeps the shape, with the upgrades on the way. -/
private theorem advanceSlotsAcross_shaped
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA) :
    ∀ {count : Nat} {forked after : ForkedBeaconState preset},
      advanceSlotsAcross config checks count forked = .ok after → Shaped forked.state →
        Shaped after.state
  | 0, forked, after, computed, shaped => by
    simp only [advanceSlotsAcross, pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ shaped
  | count + 1, forked, after, computed, shaped => by
    simp only [advanceSlotsAcross, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp nextOk
    exact advanceSlotsAcross_shaped activation compounding rest
      (processUpgrades_shaped activation compounding upgraded
        (advanceSlot_shaped advancedOk shaped))

/-- A block that the transition accepts keeps the shape, from a state of an earlier fork or not.

The state advances to the slot of the block, with the upgrades on the way.

The cap before Electra must be at most the activation balance.

The activation balance must be at most the cap of compounding credentials. -/
theorem stateTransitionAcross_shaped {fork : Fork} {engine : ExecutionEngine preset fork}
    {forked : ForkedBeaconState preset} {signed : SignedBeaconBlock preset fork}
    {validateResult : Bool} {after : BeaconState preset fork}
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (computed :
      stateTransitionAcross config checks engine forked signed validateResult = .ok after)
    (shaped : Shaped forked.state) : Shaped after := by
  obtain ⟨advanced, slotsOk, applied⟩ := stateTransitionAcross_ok computed
  simp only [processSlotsAcross, bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨_, _, advancedOk⟩ := slotsOk
  exact processBlock_shaped compounding (applySignedBlock_ok applied).2.1
    (advanceSlotsAcross_shaped activation compounding advancedOk shaped)

end EthLib.Consensus
