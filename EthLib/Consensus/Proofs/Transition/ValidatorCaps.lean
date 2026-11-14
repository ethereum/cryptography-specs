module

public import EthLib.Consensus.Proofs.Transition.Totality.Genesis
public import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
public import EthLib.Consensus.Proofs.Transition.Committees

/-!
# Validator effective-balance caps

Each validator's effective balance is at most the cap of its withdrawal credentials.

Genesis gives it, and every step keeps it before Gloas.

An epoch and a slot keep it at every fork.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- At genesis, each validator's effective balance is at most the cap of its credentials. -/
theorem Genesis.effectiveBalance_capped {g : ForkedBeaconState preset}
    (genesis : Genesis (config := config) (checks := checks) g) :
    ∀ validator ∈ g.state.validators.data,
      validator.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset g.fork validator := by
  obtain ⟨hash, time, deposits, initialized⟩ := genesis
  exact (initializeBeaconStateFromEth1_withinBudget 0 (Nat.le_refl _) initialized).capped

/-- Ordered preset caps and retained compounding credentials make a validator's cap monotone. -/
private theorem withdrawalMaxEffectiveBalance_mono {f h : Fork} {v w : Validator}
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (forks : f ≤ h)
    (credentials : hasCompoundingWithdrawalCredential v = true →
      hasCompoundingWithdrawalCredential w = true) :
    withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset h w := by
  unfold withdrawalMaxEffectiveBalance getMaxEffectiveBalance
  split <;> rename_i before
  · have later : Fork.pectra ≤ h := Nat.le_trans before forks
    rw [ite_eq_left later]
    split <;> rename_i compound
    · rw [ite_eq_left (credentials compound)]
      exact UInt64.le_refl _
    · split
      · exact compounding
      · exact UInt64.le_refl _
  · split
    · split
      · exact UInt64.le_trans activation compounding
      · exact activation
    · exact UInt64.le_refl _

private theorem capped_setValidatorAt {f : Fork} {s t : BeaconState preset f}
    {i : Nat} {v : Validator}
    (capped : ∀ w ∈ s.validators.data,
      w.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f w)
    (bound : v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f v)
    (ok : s.setValidatorAt i v = .ok t) :
    ∀ w ∈ t.validators.data,
      w.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f w := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok ok
  intro w member
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set] at member
  rcases Array.mem_or_eq_of_mem_set (w := inside) member with old | rfl
  · exact capped w old
  · exact bound

private structure CapStep {f h : Fork} (s : BeaconState preset f)
    (t : BeaconState preset h) : Prop where
  capped : (∀ v ∈ s.validators.data,
      v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f v) →
    ∀ v ∈ t.validators.data,
      v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset h v
  monotone : ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
    ∃ w, t.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset h w

private theorem CapStep.refl {f : Fork} (s : BeaconState preset f) : CapStep s s :=
  ⟨id, fun _ v found => ⟨v, found, UInt64.le_refl _⟩⟩

private theorem CapStep.trans {f h k : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} {u : BeaconState preset k}
    (one : CapStep s t) (two : CapStep t u) : CapStep s u where
  capped := two.capped ∘ one.capped
  monotone i v found := by
    obtain ⟨w, read, first⟩ := one.monotone i v found
    obtain ⟨z, read', second⟩ := two.monotone i w read
    exact ⟨z, read', UInt64.le_trans first second⟩

private theorem CapStep.data {f : Fork} {s t : BeaconState preset f}
    (same : t.validators.data = s.validators.data := by rfl) : CapStep s t := by
  constructor
  · simpa only [same] using (id : (∀ v ∈ s.validators.data,
      v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f v) → _)
  · intro i v found
    exact ⟨v, same ▸ found, UInt64.le_refl _⟩

private theorem CapStep.fold {f : Fork} {s t : BeaconState preset f} {α ε : Type}
    {step : BeaconState preset f → α → Except ε (BeaconState preset f)} {xs : List α}
    (kept : ∀ s a t, step s a = .ok t → CapStep s t)
    (ok : xs.foldlM step s = .ok t) : CapStep s t :=
  foldlM_ok_invariant (CapStep s)
    (fun _ _ _ previous computed => previous.trans (kept _ _ _ computed)) (.refl s) ok

private theorem CapStep.setValidatorAt {f : Fork} {s t : BeaconState preset f}
    {i : Nat} {v w : Validator} (found : getValidatorAt s i = .ok v)
    (monotone : withdrawalMaxEffectiveBalance preset f v ≤
      withdrawalMaxEffectiveBalance preset f w)
    (bound : v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f v →
      w.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f w)
    (ok : s.setValidatorAt i w = .ok t) : CapStep s t := by
  constructor
  · intro capped
    exact capped_setValidatorAt capped (bound (capped v (mem_of_getValidatorAt found))) ok
  · obtain ⟨inside, rfl⟩ := setValidatorAt_ok ok
    have read := getValidatorAt_eq_ok_iff.mp found
    intro j old located
    by_cases eq : j = i
    · subst j
      rw [read, Option.some.injEq] at located
      subst old
      exact ⟨w, by simp [BeaconState.putValidator,
        Serialization.Ssz.RootedForkList.data_set], monotone⟩
    · refine ⟨old, ?_, UInt64.le_refl _⟩
      simpa [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
        Ne.symm eq] using located

private theorem CapStep.setValidator {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} {v w : Validator} (found : getValidator s i = .ok v)
    (monotone : withdrawalMaxEffectiveBalance preset f v ≤
      withdrawalMaxEffectiveBalance preset f w)
    (bound : v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f v →
      w.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f w)
    (ok : s.setValidator i w = .ok t) : CapStep s t :=
  CapStep.setValidatorAt (by rwa [← getValidator_eq_getValidatorAt]) monotone bound
    (by rwa [← setValidator_eq_setValidatorAt])

private theorem CapStep.increase {f : Fork} {s t : BeaconState preset f}
    {i amount : UInt64} (ok : increaseBalance s i amount = .ok t) : CapStep s t :=
  CapStep.data (congrArg (·.data) (increaseBalance_validators ok))

private theorem CapStep.decrease {f : Fork} {s t : BeaconState preset f}
    {i amount : UInt64} (ok : decreaseBalance s i amount = .ok t) : CapStep s t :=
  CapStep.data (congrArg (·.data) (decreaseBalance_validators ok))

private theorem CapStep.exit {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} (ok : initiateValidatorExit config s i = .ok t) : CapStep s t := by
  obtain ⟨v, found, unchanged | ⟨_, queued, epoch, withdrawal, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok ok
  · rw [unchanged.2]; exact CapStep.refl _
  · have same := (exitQueue_validators queue).1
    exact (CapStep.data (congrArg (·.data) same)).trans
      (CapStep.setValidator (v := v)
        (by rw [getValidator_of_validators_eq same]; exact found)
        (by exact UInt64.le_refl _) (by exact id) set)

private theorem CapStep.slash {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config s i whistleblower = .ok t) : CapStep s t := by
  obtain ⟨_, _, _, marked, _, _, slashings, _, _, _, _, last, exited, found, _, set,
    _, _, _, lowered, _, _, raised, paid, rfl⟩ := slashValidator_ok ok
  have first := (CapStep.exit exited).trans
    (CapStep.setValidator found (by exact UInt64.le_refl _) (by exact id) set)
  have second := (CapStep.decrease lowered).trans
    ((CapStep.increase raised).trans (CapStep.increase paid))
  have total := first.trans ((CapStep.data (s := marked)
    (t := { marked with slashings })).trans second)
  split
  · exact total.trans (CapStep.data rfl)
  · exact total

private theorem CapStep.add {f : Fork} {s t : BeaconState preset f}
    {key : Cryptography.Bls.BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    (ok : addValidatorToRegistry s key credentials amount = .ok t) : CapStep s t := by
  have data := addValidatorToRegistry_validators_eq_push ok
  constructor
  · intro capped v member
    rw [data, Array.mem_push] at member
    rcases member with old | rfl
    · exact capped v old
    · unfold getValidatorFromDeposit
      exact UInt64.le_iff_toNat_le.mpr (by rw [Base.Uint64.toNat_min]; exact Nat.min_le_right _ _)
  · intro i v found
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    refine ⟨v, ?_, UInt64.le_refl _⟩
    simpa [data, Array.getElem?_push, Nat.ne_of_lt inside] using found

private theorem CapStep.deposit {f : Fork} {s t : BeaconState preset f}
    {deposit : PendingDeposit}
    (ok : applyPendingDeposit config checks s deposit = .ok t) : CapStep s t := by
  rcases applyPendingDeposit_cases ok with rfl | ⟨_, raised⟩ | ⟨_, added⟩
  · exact CapStep.refl _
  · exact CapStep.increase raised
  · exact CapStep.add added

private theorem CapStep.applyDeposit {f : Fork} {s t : BeaconState preset f}
    {key : Cryptography.Bls.BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    {signature : Cryptography.Bls.BLSSignature}
    (ok : Consensus.applyDeposit config checks s key credentials amount signature = .ok t) :
    CapStep s t := by
  unfold Consensus.applyDeposit at ok
  split at ok
  · unfold applyDepositElectra at ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨middle, added, queued⟩ := ok
        obtain ⟨_, rfl⟩ := addPendingDeposit_eq queued
        exact (CapStep.add added).trans (CapStep.data rfl)
      · cases ok; exact CapStep.refl _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp ok)
      exact CapStep.data rfl
  · exact CapStep.deposit ok

private theorem CapStep.processDeposit {f : Fork} {s t : BeaconState preset f}
    {before : f < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks before s deposit = .ok t) : CapStep s t := by
  obtain ⟨_, _, next, _, credited⟩ := processDeposit_ok ok
  exact (CapStep.data (s := s)
    (t := { s with eth1DepositIndex := fun _ => next })).trans (CapStep.applyDeposit credited)

private theorem CapStep.registryEntry {f : Fork} {s t : BeaconState preset f}
    {i : Nat} (ok : updateRegistryEntry config s i = .ok t) : CapStep s t := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, queued, queue, marked, set, ok⟩ := ok
  have same : queued.effectiveBalance = v.effectiveBalance ∧
      queued.withdrawalCredentials = v.withdrawalCredentials := by
    unfold queueForActivation at queue
    split at queue
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queue
      obtain ⟨_, _, rfl⟩ := queue
      exact ⟨rfl, rfl⟩
    · cases queue; exact ⟨rfl, rfl⟩
  have cap : withdrawalMaxEffectiveBalance preset f queued =
      withdrawalMaxEffectiveBalance preset f v := by
    simp only [withdrawalMaxEffectiveBalance, getMaxEffectiveBalance,
      hasCompoundingWithdrawalCredential, same.2]
    rfl
  have first := CapStep.setValidatorAt found
    (by rw [cap]; exact UInt64.le_refl _) (by simp only [same.1, cap]; exact id) set
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, exited⟩ := ok
    exact first.trans (CapStep.exit exited)
  · cases ok; exact first

private theorem CapStep.activate {f : Fork} {s t : BeaconState preset f}
    {i : ValidatorIndex} (ok : activateValidator s i = .ok t) : CapStep s t := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, _, _, set⟩ := ok
  exact CapStep.setValidator found (by exact UInt64.le_refl _) (by exact id) set

private theorem CapStep.registryElectra {f : Fork} {s t : BeaconState preset f}
    {epoch : Epoch} {i : Nat}
    (ok : updateRegistryEntryElectra config epoch s i = .ok t) : CapStep s t := by
  simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, set⟩ := ok
    exact CapStep.setValidatorAt found (by exact UInt64.le_refl _) (by exact id) set
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, exited⟩ := ok
    exact CapStep.exit exited
  split at ok
  · exact CapStep.setValidatorAt found (by exact UInt64.le_refl _) (by exact id)
      (liftAccessor_ok.mp ok)
  · cases ok; exact CapStep.refl _

private theorem CapStep.registry {f : Fork} {s t : BeaconState preset f}
    (ok : processRegistryUpdates config s = .ok t) : CapStep s t := by
  unfold processRegistryUpdates at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    exact CapStep.fold (fun _ _ _ => CapStep.registryElectra) ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, updated, activated⟩ := ok
    exact (CapStep.fold (fun _ _ _ => CapStep.registryEntry) updated).trans
      (CapStep.fold (fun _ _ _ => CapStep.activate) activated)

private theorem CapStep.excess {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {i : ValidatorIndex}
    (ok : queueExcessActiveBalance s electra i = .ok t) : CapStep s t := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, set, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact CapStep.data rfl
  · cases ok; exact CapStep.refl _

private theorem CapStep.compounding {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {i : ValidatorIndex}
    (order : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : switchToCompoundingValidator s electra i = .ok t) : CapStep s t := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨v, found, _, set, queued⟩ := ok
  apply CapStep.trans (CapStep.setValidator found ?_ ?_ set) (CapStep.excess queued)
  · simp only [withdrawalMaxEffectiveBalance, electra, ↓reduceIte,
      getMaxEffectiveBalance, hasCompoundingWithdrawalCredential,
      isCompoundingWithdrawalCredential]
    simp only [Vector.getElem_set_self, beq_self_eq_true, ↓reduceIte]
    by_cases h : (v.withdrawalCredentials[0] == COMPOUNDING_WITHDRAWAL_PREFIX[0]) = true
    · simp only [h]; exact UInt64.le_refl _
    · simp only [h]; exact order
  · intro bound
    apply UInt64.le_trans bound
    simp only [withdrawalMaxEffectiveBalance, electra, ↓reduceIte,
      getMaxEffectiveBalance, hasCompoundingWithdrawalCredential,
      isCompoundingWithdrawalCredential]
    simp only [Vector.getElem_set_self, beq_self_eq_true, ↓reduceIte]
    by_cases h : (v.withdrawalCredentials[0] == COMPOUNDING_WITHDRAWAL_PREFIX[0]) = true
    · simp only [h]; exact UInt64.le_refl _
    · simp only [h]; exact order

private theorem CapStep.blsChange {f : Fork} {s t : BeaconState preset f}
    {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks s signed = .ok t) : CapStep s t := by
  obtain ⟨v, found, bls, _, _, set⟩ := processBlsToExecutionChange_ok ok
  have before : hasCompoundingWithdrawalCredential v = false := by
    simp [hasCompoundingWithdrawalCredential, isCompoundingWithdrawalCredential, bls,
      BLS_WITHDRAWAL_PREFIX, COMPOUNDING_WITHDRAWAL_PREFIX]
  have after : hasCompoundingWithdrawalCredential
      { v with withdrawalCredentials := executionCredentials signed.message.toExecutionAddress } =
      false := by
    simp [hasCompoundingWithdrawalCredential, isCompoundingWithdrawalCredential,
      executionCredentials_prefix, ETH1_ADDRESS_WITHDRAWAL_PREFIX, COMPOUNDING_WITHDRAWAL_PREFIX]
  apply CapStep.setValidator found ?_ ?_ set
  · simp only [withdrawalMaxEffectiveBalance, getMaxEffectiveBalance, before, after,
      Bool.false_eq_true, ↓reduceIte]
    exact UInt64.le_refl _
  · simp only [withdrawalMaxEffectiveBalance, getMaxEffectiveBalance, before, after,
      Bool.false_eq_true, ↓reduceIte]
    exact id

private theorem CapStep.consolidate {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (found : s.validators.data[sourceIndex.toNat]? = some source)
    (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
    CapStep s t := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff, Base.Uint64.addChecked_ok_iff, pure, Except.pure] at ok
  obtain ⟨⟨churned, epoch⟩, churn, withdrawal, _, marked, set, _, _, ok⟩ := ok
  simp only [Except.ok.injEq] at ok
  subst ok
  have validators := (computeConsolidationEpochAndUpdateChurn_earliest churn).2.1
  have read : getValidator churned sourceIndex = .ok source := by
    rw [getValidator, validators, found]
  exact (CapStep.data (by rw [validators])).trans
    ((CapStep.setValidator read (by exact UInt64.le_refl _) (by exact id) set).trans
      (CapStep.data rfl))

private theorem CapStep.consolidationRequest {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {request : ConsolidationRequest}
    (order : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : processConsolidationRequest config s electra request = .ok t) : CapStep s t := by
  unfold processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact CapStep.refl _)
    | exact CapStep.compounding order (liftAccessor_ok.mp ok)
    | exact CapStep.consolidate (getElem?_toNat_of_ofNatChecked (by assumption)) ok

private theorem CapStep.partialWithdrawal {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {i : ValidatorIndex} {v : Validator} {amount owed : Gwei}
    (ok : requestPartialWithdrawal config s electra i v amount owed = .ok t) : CapStep s t := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at ok
  obtain ⟨_, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at ok
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := ok
    exact CapStep.data (by rw [(computeExitEpochAndUpdateChurn_earliest churned).2.1])
  · cases ok; exact CapStep.refl _

private theorem CapStep.withdrawalRequest {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t) : CapStep s t := by
  unfold processWithdrawalRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact CapStep.refl _)
    | exact CapStep.exit (liftAccessor_ok.mp ok)
    | exact CapStep.partialWithdrawal ok

private theorem CapStep.depositRequest {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {request : DepositRequest}
    (ok : processDepositRequest s electra request = .ok t) : CapStep s t := by
  obtain ⟨start, recorded⟩ := recordDepositRequestsStart_eq (state := s) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit,
    bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, rfl⟩ := ok
  exact CapStep.data rfl

private theorem CapStep.requests {f : Fork} {s t : BeaconState preset f}
    {body : BeaconBlockBody preset f} {electra : .pectra ≤ f ∧ f < .glamsterdam}
    (order : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : processExecutionRequests config s body electra = .ok t) : CapStep s t := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨deposited, deposits, withdrawn, withdrawals, consolidations⟩ := ok
  exact (CapStep.fold (fun _ _ _ => CapStep.depositRequest) deposits).trans
    ((CapStep.fold (fun _ _ _ => CapStep.withdrawalRequest) withdrawals).trans
      (CapStep.fold (fun _ _ _ => CapStep.consolidationRequest order) consolidations))

private theorem CapStep.proposerSlashing {f : Fork} {s t : BeaconState preset f}
    {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks s slashing = .ok t) : CapStep s t := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact CapStep.slash slashed

private theorem CapStep.attesterSlashing {f : Fork} {s t : BeaconState preset f}
    {slashing : AttesterSlashing preset f}
    (ok : processAttesterSlashing config checks s slashing = .ok t) : CapStep s t := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  refine foldlM_ok_invariant (fun step => CapStep s step.1) ?_ (CapStep.refl s) folded
  intro step i next previous ok
  obtain ⟨middle, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, slashed, rfl⟩ := ok
    exact previous.trans (CapStep.slash slashed)
  · cases ok; exact previous

private theorem CapStep.block {f : Fork} {s t : BeaconState preset f}
    {engine : ExecutionEngine preset f} {block : BeaconBlock preset f}
    (order : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : processBlock config checks engine s block = .ok t) : CapStep s t := by
  have same {a b : BeaconState preset f} (validators : b.validators = a.validators) :
      CapStep a b :=
    CapStep.data (congrArg (·.data) validators)
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput ok
  -- From Gloas, a block first applies the payload of the parent, which runs the validator requests.
  have head : CapStep s input :=
    started.step_of CapStep CapStep.refl (fun one two => one.trans two)
      (fun _ paid => processParentExecutionPayload_step_of CapStep CapStep.refl
        (fun one two => one.trans two) (fun _ validators => same validators)
        CapStep.withdrawalRequest (CapStep.consolidationRequest order) paid)
      (fun headed => same (by obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headed; rfl))
      (fun _ executed => same (processBlockExecution_validators executed))
      (fun revealed => same (by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealed
        rfl))
      (fun _ voted => same (by
        obtain ⟨_, _, rest⟩ := processEth1Data_eq voted
        rw [← rest]))
  obtain ⟨_, _, _, proposersOk, slashingsOk, attestedOk, rest⟩ :=
    processOperations_folds_of CapStep CapStep.refl (fun one two => one.trans two)
      CapStep.processDeposit (fun exited => CapStep.exit (processVoluntaryExit_initiates exited))
      CapStep.blsChange (CapStep.requests order)
      (fun attested => same (by rw [processPayloadAttestation_eq attested])) operated
  have tail : CapStep last t := by
    split at synced
    · obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
      exact same rfl
    · cases synced
      exact CapStep.refl _
  exact head.trans <|
    (CapStep.fold (fun _ _ _ => CapStep.proposerSlashing) proposersOk).trans <|
    (CapStep.fold (fun _ _ _ => CapStep.attesterSlashing) slashingsOk).trans <|
    (CapStep.fold (fun _ _ _ attested => same (processAttestation_registry attested).1)
      attestedOk).trans (rest.trans tail)

private theorem CapStep.pending {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} (ok : processPendingDeposits config checks s electra = .ok t) :
    CapStep s t := by
  have pass {stop : PendingDeposit → Bool} {nextEpoch : Epoch} {available : Gwei} :
      ∀ {deposits : List PendingDeposit} {state : BeaconState preset f} {processed : Gwei}
        {count : Nat} {postponed : Array PendingDeposit} {result},
        passPendingDeposits config checks stop nextEpoch available state processed count
          postponed deposits = .ok result → CapStep state result.1.state :=
    fun ok => passPendingDeposits_of CapStep CapStep.refl (fun one two => one.trans two)
      (fun credited => CapStep.deposit credited) ok
  unfold processPendingDeposits at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' (split at ok <;> try cases ok)
  all_goals exact (pass ‹_›).trans (CapStep.data rfl)

private theorem CapStep.effective {f : Fork} {s t : BeaconState preset f}
    (ok : processEffectiveBalanceUpdates s = .ok t) : CapStep s t := by
  unfold processEffectiveBalanceUpdates at ok
  refine CapStep.fold (fun _ _ _ ok => ?_) ok
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, balance, read, next, changed, set⟩ := ok
  refine CapStep.setValidatorAt found ?_ ?_ set
  · exact UInt64.le_refl _
  · intro bound
    exact updatedEffectiveBalance_le_largest bound changed

/-- An epoch keeps the caps; only three of its stages change the validators. -/
private theorem CapStep.epoch {f : Fork} {s t : BeaconState preset f}
    (ok : processEpoch config checks s = .ok t) : CapStep s t := by
  apply (processEpoch_trace ok).transport CapStep CapStep.refl (fun a b => a.trans b)
  intro k _ a b computed
  have edge := EpochStage.action_cases.mp computed
  cases k
  case registry => exact CapStep.registry edge
  case pendingDeposits =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · exact CapStep.pending edge
    · exact edge ▸ CapStep.refl _
  case effectiveBalances => exact CapStep.effective edge
  all_goals exact CapStep.data (congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩))

private theorem CapStep.slot {f : Fork} {s t : BeaconState preset f}
    (ok : advanceSlot config checks s = .ok t) : CapStep s t := by
  simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨next, _, cached, cache, advanced, advance, rfl⟩ := ok
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cache
  unfold epochIfLast at advance
  split at advance
  · have step := CapStep.epoch advance
    exact ⟨step.capped, step.monotone⟩
  · cases advance
    exact CapStep.data rfl

private theorem CapStep.carry {f h : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} (same : t.validators.data = s.validators.data)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (forks : f ≤ h) : CapStep s t where
  capped capped v member := UInt64.le_trans (capped v (same ▸ member))
    (withdrawalMaxEffectiveBalance_mono activation compounding forks id)
  monotone _i v found := ⟨v, same ▸ found,
    withdrawalMaxEffectiveBalance_mono activation compounding forks id⟩

private theorem CapStep.preActivation {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {i : ValidatorIndex}
    (ok : queuePreActivation s electra i = .ok t) : CapStep s t := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨v, found, _, _, _, _, _, balance, _, validator, rfl⟩ := ok
  obtain ⟨_, rfl⟩ := setBalance_ok balance
  have changed := CapStep.setValidator (v := v)
    (by simpa only [getValidator, BeaconState.putBalance] using found)
    (by exact UInt64.le_refl _) (by intro _; exact UInt64.zero_le) validator
  exact ⟨changed.capped, changed.monotone⟩

private theorem CapStep.upgrade {s : ForkedBeaconState preset}
    {t : {t : ForkedBeaconState preset // s.fork < t.fork}}
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : upgradeNext config checks s = .ok t) : CapStep s.state t.val.state := by
  obtain ⟨fork, state⟩ := s
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at ok
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact CapStep.carry (upgradeToAltair_spec upgraded).1
      activation compounding (by change Fork.phase0 ≤ .altair; decide)
  · subst ok
    exact CapStep.carry rfl activation compounding (by change Fork.altair ≤ .bellatrix; decide)
  · subst ok
    exact CapStep.carry rfl activation compounding (by change Fork.bellatrix ≤ .shapella; decide)
  · subst ok
    exact CapStep.carry rfl activation compounding (by change Fork.shapella ≤ .dencun; decide)
  · obtain ⟨_, upgraded, rfl⟩ := ok
    simp only [upgradeToElectra, bind_ok_iff] at upgraded
    obtain ⟨_, _, _, _, _, _, _, _, middle, queued, compounded⟩ := upgraded
    have queuedStep := CapStep.fold (fun _ _ _ => CapStep.preActivation) queued
    have one := (CapStep.carry (s := state) (h := .pectra) (t := _) (by rfl)
      activation compounding (by decide)).trans queuedStep
    apply one.trans
    refine CapStep.fold (fun a index b ok => ?_) compounded
    unfold queueCompoundingExcess at ok
    split at ok
    · split at ok
      · exact CapStep.excess (liftAccessor_ok.mp ok)
      · cases ok; exact CapStep.refl _
    · cases ok; exact CapStep.refl _
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact CapStep.carry (upgradeToFulu_spec upgraded).1
      activation compounding (by change Fork.pectra ≤ .fusaka; decide)
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact CapStep.carry (upgradeToGloas_spec upgraded).1
      activation compounding (by change Fork.fusaka ≤ .glamsterdam; decide)
  · obtain ⟨_, upgraded, rfl⟩ := ok
    obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    exact CapStep.carry (upgradeHezeFields_lists state).1
      activation compounding (by change Fork.glamsterdam ≤ .hegota; decide)

private theorem CapStep.upgrades {s t : ForkedBeaconState preset}
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : processUpgrades config checks s = .ok t) : CapStep s.state t.state := by
  fun_induction processUpgrades config checks s generalizing t with
  | case1 s due ih =>
    obtain ⟨next, nextOk, rest⟩ := bind_ok_iff.mp ok
    exact (CapStep.upgrade activation compounding nextOk).trans (ih next rest)
  | case2 s notDue => cases ok; exact CapStep.refl _

private theorem CapStep.step {s t : ForkedBeaconState preset}
    (step : Step config checks s t)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (early : t.fork < .glamsterdam) : CapStep s.state t.state := by
  cases step with
  | block engine signed due ok =>
    exact CapStep.block compounding (applySignedBlock_ok ok).2.1
  | slot ok =>
    obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
    exact (CapStep.slot slotOk).trans
      (CapStep.upgrades activation compounding upgrades)

private theorem CapStep.run {s t : ForkedBeaconState preset}
    (run : Run config checks s t)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (early : t.fork < .glamsterdam) : CapStep s.state t.state := by
  induction run with
  | nil => exact CapStep.refl _
  | snoc pre step ih =>
    exact (ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early)).trans
      (CapStep.step step activation compounding early)

/-- Before Gloas, each validator reached from genesis has an effective balance at most its cap.

The preset caps are assumed in order.

`MAX_EFFECTIVE_BALANCE` is at most `MIN_ACTIVATION_BALANCE`.

`MIN_ACTIVATION_BALANCE` is at most `MAX_EFFECTIVE_BALANCE_ELECTRA`.
-/
theorem Run.effectiveBalance_capped {g x : ForkedBeaconState preset}
    (run : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (early : x.fork < .glamsterdam) :
    ∀ v ∈ x.state.validators.data,
      v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset x.fork v :=
  (CapStep.run run activation compounding early).capped genesis.effectiveBalance_capped

/-- An existing validator's cap cannot decrease along a pre-Gloas run. -/
theorem Run.validatorCap_mono {x y : ForkedBeaconState preset}
    (run : Run config checks x y)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (early : y.fork < .glamsterdam) (i : Nat) (v : Validator)
    (found : x.state.validators.data[i]? = some v) :
    ∃ w, y.state.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset x.fork v ≤
        withdrawalMaxEffectiveBalance preset y.fork w :=
  (CapStep.run run activation compounding early).monotone i v found

/-- The cap at an existing index cannot decrease during an epoch. -/
theorem processEpoch_validatorCap_mono {f : Fork} {s t : BeaconState preset f}
    (ok : processEpoch config checks s = .ok t)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v) :
    ∃ w, t.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset f w :=
  (CapStep.epoch ok).monotone i v found

/-- One epoch keeps each effective balance at most the largest one of its validator. -/
theorem processEpoch_capped {f : Fork} {s t : BeaconState preset f}
    (ok : processEpoch config checks s = .ok t) (capped : EffectiveBalancesCapped s) :
    EffectiveBalancesCapped t :=
  (CapStep.epoch ok).capped capped

/-- One slot keeps each effective balance at most the largest one of its validator. -/
theorem advanceSlot_capped {f : Fork} {s t : BeaconState preset f}
    (ok : advanceSlot config checks s = .ok t) (capped : EffectiveBalancesCapped s) :
    EffectiveBalancesCapped t :=
  (CapStep.slot ok).capped capped

/-- A block keeps each effective balance at most the largest one of its validator, at every fork.

The activation balance must be at most the cap of compounding credentials.

Then a switch to compounding credentials never lowers a cap. -/
theorem processBlock_capped {f : Fork} {s t : BeaconState preset f}
    {engine : ExecutionEngine preset f} {block : BeaconBlock preset f}
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : processBlock config checks engine s block = .ok t) (capped : EffectiveBalancesCapped s) :
    EffectiveBalancesCapped t :=
  (CapStep.block compounding ok).capped capped

/-- The upgrade to the next fork keeps each effective balance at most the cap of its validator.

The caps of the preset are assumed in order.

The largest balance before Electra must be at most the least one from Electra.

That one must be at most the largest one for compounding credentials. -/
theorem upgradeNext_capped {s : ForkedBeaconState preset}
    {t : {t : ForkedBeaconState preset // s.fork < t.fork}}
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : upgradeNext config checks s = .ok t) (capped : EffectiveBalancesCapped s.state) :
    EffectiveBalancesCapped t.val.state :=
  (CapStep.upgrade activation compounding ok).capped capped

end EthLib.Consensus
