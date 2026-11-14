module

public import EthLib.Consensus.Proofs.Containers.Misc
public import EthLib.Consensus.Proofs.Transition.EpochPending
public import EthLib.Consensus.Proofs.Transition.Totality.Consolidations
public import EthLib.Consensus.Proofs.Transition.Totality.RegistryLoad

/-!
# Proofs: the pending deposits of an epoch succeed under bounds

From Electra the epoch step reads the queue of pending deposits from its front.

A deposit to a known key adds its amount to a balance.

A deposit to a new key with a valid signature adds a validator.

Every amount it credits comes from the queue, and leaves it.

So the sum of the balances plus the amounts in the queue below `2^64` leaves room for each credit.

The same bound keeps the running total of the amounts that the pass reads below `2^64`.

Each new validator takes the place of a deposit that leaves the queue.

So the validators plus the pending deposits within the limit of the registry leave room for it.

The churn is at most a cap of the configuration, which Gloas changes.

So the carried churn plus that cap must fit in 64 bits.

The step after it, the pending consolidations, then succeeds too.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork}

/-- The check of a deposit signature always succeeds, whatever its verdict. -/
theorem isValidDepositSignature_exists_ok (config : Config) (checks : SignatureChecks)
    (pubkey : Cryptography.Bls.BLSPubkey) (credentials : Bytes32) (amount : Gwei)
    (signature : Cryptography.Bls.BLSSignature) :
    ∃ valid, isValidDepositSignature config checks pubkey credentials amount signature =
      .ok valid := by
  obtain ⟨domain, domainOk⟩ := computeDomain_total config DOMAIN_DEPOSIT
    config.GENESIS_FORK_VERSION (Vector.replicate 32 0)
  obtain ⟨root, rootOk⟩ := computeSigningRoot_total
    (DepositMessage.mk pubkey credentials amount) domain
  simp [isValidDepositSignature, isValidDepositMessageSignature, domainOk, rootOk, liftSsz, bind,
    Except.bind, pure, Except.pure, Except.mapError]

/-- An entry added at the end of a list with room succeeds. -/
private theorem setOrAppendList_exists_ok {switch : Base.Fork} {α : Type} {limit : Nat}
    (list : ForkList switch fork α limit) {index : UInt64} (value : α)
    (atEnd : index.toNat = list.data.size) (room : list.data.size + 1 ≤ limit) :
    ∃ next, setOrAppendList list index value = .ok next := by
  simp [setOrAppendList, atEnd, appendWithinLimit, room]

/-- A new validator succeeds in a registry with room, with one entry per validator in each list. -/
private theorem addValidatorToRegistry_exists_ok {state : BeaconState preset fork}
    (matched : BalancesMatch state) (sized : ParticipationMatches state)
    (scored : InactivityScoresMatch state)
    (room : state.validators.data.size < preset.VALIDATOR_REGISTRY_LIMIT.toNat)
    (pubkey : Cryptography.Bls.BLSPubkey) (credentials : Bytes32) (amount : Gwei) :
    ∃ after, addValidatorToRegistry state pubkey credentials amount = .ok after := by
  have small : state.validators.data.size < 2 ^ 64 :=
    Nat.lt_trans room preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt
  unfold addValidatorToRegistry
  split
  · rename_i altair
    have index : getIndexForNewValidator state = .ok state.validators.data.size.toUInt64 := by
      simp [getIndexForNewValidator, ofNatChecked_of_lt small, liftArith, Except.mapError]
    have atEnd : state.validators.data.size.toUInt64.toNat = state.validators.data.size := by
      simpa using small
    obtain ⟨validators, validatorsOk⟩ : ∃ validators, setOrAppendRooted state.validators
        state.validators.data.size.toUInt64
        (getValidatorFromDeposit preset fork pubkey credentials amount) = .ok validators := by
      simp [setOrAppendRooted, atEnd, Nat.succ_le_of_lt room]
    obtain ⟨balances, balancesOk⟩ := setOrAppendList_exists_ok state.balances amount
      (atEnd.trans matched.symm) (by unfold BalancesMatch at matched; omega)
    obtain ⟨previous, previousOk⟩ := setOrAppendList_exists_ok
      (state.previousEpochParticipation altair) 0 (atEnd.trans (sized altair).1.symm)
      (by have := (sized altair).1; omega)
    obtain ⟨current, currentOk⟩ := setOrAppendList_exists_ok
      (state.currentEpochParticipation altair) 0 (atEnd.trans (sized altair).2.symm)
      (by have := (sized altair).2; omega)
    obtain ⟨scores, scoresOk⟩ := setOrAppendList_exists_ok
      (state.inactivityScores altair) 0 (atEnd.trans (scored altair).symm)
      (by have := scored altair; omega)
    simp [addValidatorToRegistryAltair, index, validatorsOk, balancesOk, previousOk, currentOk,
      scoresOk, liftAccessor, bind, Except.bind, pure, Except.pure, Except.mapError]
  · unfold BalancesMatch at matched
    simp [room, matched]

/-- A pending deposit succeeds in a registry with room.

The sum of the balances plus its amount must be below `2^64`.

Each list of the registry must have one entry for each validator. -/
private theorem applyPendingDeposit_exists_ok (config : Config) (checks : SignatureChecks)
    {state : BeaconState preset fork} (deposit : PendingDeposit)
    (matched : BalancesMatch state) (sized : ParticipationMatches state)
    (scored : InactivityScoresMatch state)
    (room : state.validators.data.size < preset.VALIDATOR_REGISTRY_LIMIT.toNat)
    (funded : balanceSum state + deposit.amount.toNat < 2 ^ 64) :
    ∃ after, applyPendingDeposit config checks state deposit = .ok after := by
  have small : state.validators.data.size < 2 ^ 64 :=
    Nat.lt_trans room preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt
  unfold applyPendingDeposit
  split
  · split
    · exact ⟨_, rfl⟩
    obtain ⟨valid, validOk⟩ := isValidDepositSignature_exists_ok config checks deposit.pubkey
      deposit.withdrawalCredentials deposit.amount deposit.signature
    simp only [validOk, bind, Except.bind]
    cases valid
    · exact ⟨_, rfl⟩
    · exact addValidatorToRegistry_exists_ok matched sized scored room _ _ _
  · rename_i position found
    obtain ⟨inside, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp found
    have converted := ofNatChecked_of_lt (Nat.lt_trans inside small)
    have toNat : position.toUInt64.toNat = position := by
      simpa using Nat.lt_trans inside small
    unfold BalancesMatch at matched
    have insideBalances : position.toUInt64.toNat < state.balances.data.size := by omega
    have le := balance_le_balanceSum state insideBalances
    have raised : increaseBalance state position.toUInt64 deposit.amount = .ok _ :=
      increaseBalance_eq_ok_iff.mpr ⟨insideBalances, by omega, rfl⟩
    simp only [liftAccessor, liftArith, converted, Except.mapError, bind, Except.bind, raised]
    exact ⟨_, rfl⟩

/-- A new validator keeps one entry for each validator in the flags and the scores.

From Altair, it appends one entry to each list, and before Altair there are no such lists. -/
theorem addValidatorToRegistry_matches {state after : BeaconState preset fork}
    {pubkey : Cryptography.Bls.BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey credentials amount = .ok after)
    (sized : ParticipationMatches state) (scored : InactivityScoresMatch state) :
    ParticipationMatches after ∧ InactivityScoresMatch after := by
  unfold addValidatorToRegistry at computed
  split at computed
  · rename_i altair
    simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨index, indexOk, _, validatorsOk, _, _, _, previousOk, _, currentOk, _, scoresOk,
      rfl⟩ := computed
    have atEnd := (getIndexForNewValidator_ok_iff.mp indexOk).2
    have validators := setOrAppendRooted_size validatorsOk
    have previous := setOrAppendList_size previousOk
    have current := setOrAppendList_size currentOk
    have scores := setOrAppendList_size scoresOk
    have one := (sized altair).1
    have two := (sized altair).2
    have three := scored altair
    refine ⟨fun _ => ⟨?_, ?_⟩, fun _ => ?_⟩ <;>
      simp only at validators previous current scores ⊢ <;>
      split at validators <;> split at previous <;> split at current <;>
      split at scores <;> omega
  · split at computed
    · cases computed
      exact ⟨fun altair => absurd altair ‹_›, fun altair => absurd altair ‹_›⟩
    · cases computed

/-- A pending deposit keeps one entry for each validator in the flags and the scores. -/
private theorem applyPendingDeposit_matches {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after)
    (sized : ParticipationMatches state) (scored : InactivityScoresMatch state) :
    ParticipationMatches after ∧ InactivityScoresMatch after := by
  rcases applyPendingDeposit_cases computed with rfl | ⟨_, raised⟩ | ⟨_, added⟩
  · exact ⟨sized, scored⟩
  · obtain ⟨_, _, rfl⟩ := increaseBalance_eq_ok_iff.mp raised
    exact ⟨sized, scored⟩
  · exact addValidatorToRegistry_matches added sized scored

/-- The pending deposits of an epoch keep one entry for each validator in the flags and scores. -/
theorem processPendingDeposits_matches {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after)
    (sized : ParticipationMatches state) (scored : InactivityScoresMatch state) :
    ParticipationMatches after ∧ InactivityScoresMatch after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, applies, rfl⟩ :=
    processPendingDeposits_applied computed
  have flags := foldlM_ok_invariant
    (fun s : BeaconState preset fork => ParticipationMatches s ∧ InactivityScoresMatch s)
    (fun _ _ _ before step => applyPendingDeposit_matches step before.1 before.2) ⟨sized, scored⟩
    applies
  exact flags

/-- A pass over the pending deposits succeeds under bounds on what it may still read.

The validators plus the deposits left must be within the limit of the registry.

The balances plus the amounts left must be below `2^64`, and so must the churn used plus them.

Each list of the registry must have one entry for each validator. -/
private theorem passPendingDeposits_exists_ok (config : Config) (checks : SignatureChecks)
    (stop : PendingDeposit → Bool) (nextEpoch : Epoch) (available : Gwei) :
    ∀ (deposits : List PendingDeposit) (state : BeaconState preset fork) (processed : Gwei)
      (count : Nat) (postponed : Array PendingDeposit),
      BalancesMatch state → ParticipationMatches state → InactivityScoresMatch state →
      state.validators.data.size + deposits.length ≤ preset.VALIDATOR_REGISTRY_LIMIT.toNat →
      balanceSum state + pendingAmount deposits < 2 ^ 64 →
      processed.toNat + pendingAmount deposits < 2 ^ 64 →
      ∃ pass, passPendingDeposits config checks stop nextEpoch available state processed count
        postponed deposits = .ok pass
  | [], _, _, _, _, _, _, _, _, _, _ => ⟨_, rfl⟩
  | deposit :: rest, state, processed, count, postponed, matched, sized, scored, room, funded,
      used => by
    have limit := preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt
    have small : state.validators.data.size < 2 ^ 64 := by
      simp only [List.length_cons] at room
      omega
    have split : pendingAmount (deposit :: rest) = deposit.amount.toNat + pendingAmount rest := by
      simp [pendingAmount]
    rw [split] at funded used
    simp only [List.length_cons] at room
    unfold passPendingDeposits
    simp only [bind, Except.bind, pure, Except.pure]
    split
    · exact ⟨_, rfl⟩
    have status : liftAccessor (depositTargetStatus state nextEpoch deposit.pubkey) =
        .ok (match state.validators.data.find? (·.pubkey == deposit.pubkey) with
          | some validator => (decide (validator.exitEpoch.toNat < 2 ^ 64 - 1),
              decide (validator.withdrawableEpoch.toNat < nextEpoch.toNat))
          | none => (false, false)) := by
      rw [depositTargetStatus_eq small]
      rfl
    rw [status]
    generalize (match state.validators.data.find? (·.pubkey == deposit.pubkey) with
          | some validator => (decide (validator.exitEpoch.toNat < 2 ^ 64 - 1),
              decide (validator.withdrawableEpoch.toNat < nextEpoch.toNat))
          | none => (false, false)) = tests
    obtain ⟨exited, withdrawn⟩ := tests
    -- A deposit that the pass credits keeps the bounds for the deposits after it.
    have credit : ∀ processed' : Gwei, processed'.toNat + pendingAmount rest < 2 ^ 64 →
        ∃ next, applyPendingDeposit config checks state deposit = .ok next ∧
          ∃ pass, passPendingDeposits config checks stop nextEpoch available next processed'
            (count + 1) postponed rest = .ok pass := by
      intro processed' fits
      obtain ⟨next, nextOk⟩ := applyPendingDeposit_exists_ok config checks deposit matched sized
        scored (by omega) (by omega)
      have grown := (applyPendingDeposit_validators_size_le_and_mem nextOk).1
      have raised := balanceSum_applyPendingDeposit_le nextOk
      have kept := applyPendingDeposit_matches nextOk sized scored
      exact ⟨next, nextOk, passPendingDeposits_exists_ok config checks stop nextEpoch available
        rest next processed' (count + 1) postponed ((applyPendingDeposit_kept nextOk).1 matched)
        kept.1 kept.2 (by omega) (by omega) fits⟩
    cases withdrawn
    · cases exited
      · have summed : liftAccessor (liftArith (addChecked processed deposit.amount)) =
            .ok (processed + deposit.amount) := by
          simp [addChecked_of_lt (by omega : processed.toNat + deposit.amount.toNat < 2 ^ 64),
            liftAccessor, liftArith, Except.mapError]
        have value : (processed + deposit.amount).toNat = processed.toNat + deposit.amount.toNat :=
          toNat_add_of_lt (by omega)
        simp only [Bool.false_eq_true, ↓reduceIte, summed]
        split
        · exact ⟨_, rfl⟩
        · obtain ⟨next, nextOk, pass, passOk⟩ := credit (processed + deposit.amount) (by omega)
          simp only [nextOk, passOk]
          exact ⟨_, rfl⟩
      · obtain ⟨pass, passOk⟩ := passPendingDeposits_exists_ok config checks stop nextEpoch
          available rest state processed (count + 1) (postponed.push deposit) matched sized scored
          (by omega) (by omega) (by omega)
        simp only [Bool.false_eq_true, ↓reduceIte, passOk]
        exact ⟨_, rfl⟩
    · obtain ⟨next, nextOk, pass, passOk⟩ := credit processed (by omega)
      simp only [↓reduceIte, nextOk, passOk]
      exact ⟨_, rfl⟩

/-- From Electra, the cap on the churn of pending deposits, which Gloas changes. -/
def depositChurnCap (config : Config) (fork : Base.Fork) : Nat :=
  if .glamsterdam ≤ fork then config.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS.toNat
  else config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat

/-- When the churn of deposits succeeds, it is at most the cap of its fork. -/
theorem depositChurnLimit_le_cap {config : Config} {state : BeaconState preset fork}
    {churn : Gwei} (computed : depositChurnLimit config state = .ok churn) :
    churn.toNat ≤ depositChurnCap config fork := by
  unfold depositChurnLimit at computed
  unfold depositChurnCap
  split at computed
  · simp only [getActivationChurnLimit, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    rw [UInt64.min_def]
    split <;> rename_i chosen <;> simp only [UInt64.le_iff_toNat_le] at chosen <;> omega
  · simp only [getActivationExitChurnLimit, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    rw [UInt64.min_def]
    split <;> rename_i chosen <;> simp only [UInt64.le_iff_toNat_le] at chosen <;> omega

/-- The churn of deposits succeeds when the effective balances sum below `2^64`.

The registry must stay within its limit.

The churn is then at most the cap of its fork. -/
theorem depositChurnLimit_exists_ok (config : Config) {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit) (summed : effectiveBalanceSum state < 2 ^ 64) :
    ∃ churn, depositChurnLimit config state = .ok churn ∧
      churn.toNat ≤ depositChurnCap config fork := by
  obtain ⟨total, totalOk, -⟩ := getTotalActiveBalance_exists_ok within summed
  suffices exists_ok : ∃ churn, depositChurnLimit config state = .ok churn by
    obtain ⟨churn, churnOk⟩ := exists_ok
    exact ⟨churn, churnOk, depositChurnLimit_le_cap churnOk⟩
  unfold depositChurnLimit
  split
  · exact ⟨_, by simp [getActivationChurnLimit, getExitChurnLimit, totalOk, bind, Except.bind,
      pure, Except.pure]; rfl⟩
  · exact ⟨_, by simp [getActivationExitChurnLimit, getBalanceChurnLimit, totalOk, bind,
      Except.bind, pure, Except.pure]; rfl⟩

/-- From Electra, the pending deposits carry at most the churn carried before plus a cap.

The cap is that of the churn of deposits of its fork. -/
theorem processPendingDeposits_depositBalanceToConsume_le {config : Config}
    {checks : SignatureChecks} {state after : BeaconState preset fork} {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    (after.depositBalanceToConsume electra).toNat ≤
      (state.depositBalanceToConsume electra).toNat + depositChurnCap config fork := by
  obtain ⟨_, _, _, _, _, _, churnOk, availableOk, _, _, _, _, _, carriedEq⟩ :=
    processPendingDeposits_pass computed
  have capped := depositChurnLimit_le_cap churnOk
  have value := (addChecked_ok_iff.mp (mapError_ok_iff.mp availableOk)).2
  rw [carriedEq]
  split <;> omega

/-- A pass over the pending consolidations changes only the balances. -/
private theorem passPendingConsolidations_fields {nextEpoch : Epoch} :
    ∀ {consolidations : List PendingConsolidation} {state : BeaconState preset fork}
      {result : BeaconState preset fork × Nat},
      passPendingConsolidations nextEpoch state consolidations = .ok result →
      result.1.validators = state.validators ∧
        result.1.previousEpochParticipation = state.previousEpochParticipation ∧
        result.1.currentEpochParticipation = state.currentEpochParticipation ∧
        result.1.inactivityScores = state.inactivityScores ∧
        result.1.pendingDeposits = state.pendingDeposits ∧
        result.1.depositBalanceToConsume = state.depositBalanceToConsume ∧
        result.1.historicalSummaries = state.historicalSummaries ∧
        result.1.slashings = state.slashings ∧ result.1.historicalRoots = state.historicalRoots
  | [], _, _, computed => by
    simp only [passPendingConsolidations, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | consolidation :: rest, state, result, computed => by
    unfold passPendingConsolidations at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
    split at computed
    · split at computed
      · cases computed
      rename_i recur
      cases computed
      exact (passPendingConsolidations_fields (consolidations := rest) recur :)
    split at computed
    · cases computed
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    split at computed
    · cases computed
    split at computed
    · cases computed
    rename_i lowered loweredOk
    split at computed
    · cases computed
    rename_i raised raisedOk
    split at computed
    · cases computed
    rename_i recur
    cases computed
    obtain ⟨_, lowerSet⟩ := decreaseBalance_ok (liftAccessor_ok.mp loweredOk)
    obtain ⟨_, rfl⟩ := setBalance_ok lowerSet
    obtain ⟨_, _, rfl⟩ := increaseBalance_eq_ok_iff.mp (liftAccessor_ok.mp raisedOk)
    exact (passPendingConsolidations_fields (consolidations := rest) recur :)

/-- The pending consolidations change only the balances and their own queue. -/
theorem processPendingConsolidations_fields {electra : .pectra ≤ fork}
    {state after : BeaconState preset fork}
    (computed : processPendingConsolidations state electra = .ok after) :
    after.validators = state.validators ∧
      after.previousEpochParticipation = state.previousEpochParticipation ∧
      after.currentEpochParticipation = state.currentEpochParticipation ∧
      after.inactivityScores = state.inactivityScores ∧
      after.pendingDeposits = state.pendingDeposits ∧
      after.depositBalanceToConsume = state.depositBalanceToConsume ∧
      after.historicalSummaries = state.historicalSummaries ∧
      after.slashings = state.slashings ∧ after.historicalRoots = state.historicalRoots := by
  simp only [processPendingConsolidations, bind, Except.bind, pure, Except.pure] at computed
  split at computed
  · cases computed
  split at computed
  · cases computed
  rename_i passed
  cases computed
  exact passPendingConsolidations_fields passed

/-- A validator from a deposit has an effective balance at most its largest one.

Its largest one reads only its credentials, which it shares with the record it starts from. -/
private theorem getValidatorFromDeposit_capped (pubkey : Cryptography.Bls.BLSPubkey)
    (credentials : Bytes32) (amount : Gwei) :
    (getValidatorFromDeposit preset fork pubkey credentials amount).effectiveBalance ≤
      withdrawalMaxEffectiveBalance preset fork
        (getValidatorFromDeposit preset fork pubkey credentials amount) := by
  simp only [getValidatorFromDeposit, withdrawalMaxEffectiveBalance, getMaxEffectiveBalance,
    hasCompoundingWithdrawalCredential]
  exact Std.min_le_right

/-- A validator from a deposit has an effective balance at most the amount of the deposit. -/
theorem getValidatorFromDeposit_effectiveBalance_le (pubkey : Cryptography.Bls.BLSPubkey)
    (credentials : Bytes32) (amount : Gwei) :
    (getValidatorFromDeposit preset fork pubkey credentials amount).effectiveBalance ≤ amount := by
  have mod : amount % preset.EFFECTIVE_BALANCE_INCREMENT ≤ amount := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]
    exact Nat.mod_le _ _
  exact UInt64.le_trans Std.min_le_left (UInt64.sub_le mod)

/-- A pending deposit keeps each effective balance at most the largest one of its validator. -/
private theorem applyPendingDeposit_capped {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after)
    (capped : ∀ validator ∈ state.validators.data,
      validator.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork validator) :
    ∀ validator ∈ after.validators.data,
      validator.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork validator := by
  rcases applyPendingDeposit_cases computed with rfl | ⟨_, raised⟩ | ⟨_, added⟩
  · exact capped
  · rw [increaseBalance_validators raised]
    exact capped
  · rw [addValidatorToRegistry_validators_eq_push added]
    intro validator member
    rcases Array.mem_push.mp member with old | rfl
    · exact capped validator old
    · exact getValidatorFromDeposit_capped _ _ _

/-- From Electra, the pending deposits succeed under bounds on the registry and the amounts.

The validators plus the pending deposits must be within the limit of the registry.

The registry has one balance for each validator, and each effective balance is within its cap.

From Altair, each list of scores and of participation flags has one entry for each validator.

The sum of the balances plus the amounts in the queue must be below `2^64`.

So must the sum of the effective balances, which the churn reads.

The churn carried from the last epoch plus the cap on the churn of deposits must fit too.

The current epoch plus one, and the first slot of the finalized epoch, must fit in 64 bits.

Afterwards the validators plus the pending deposits stay within the limit of the registry.

There is still one balance for each validator.

The sum of the balances plus the amounts in the queue does not grow.

The registry does not shrink, and the pending consolidations and the current epoch stay.

From Altair each list of scores and of flags still has one entry for each validator.

The churn carried to the next epoch is at most the churn carried before plus the cap.

Each effective balance stays at most the largest one of its validator. -/
theorem processPendingDeposits_total (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (electra : .pectra ≤ fork)
    (loaded : registryLoad state ≤ preset.VALIDATOR_REGISTRY_LIMIT.toNat)
    (matched : BalancesMatch state) (sized : ParticipationMatches state)
    (scored : InactivityScoresMatch state)
    (capped : ∀ validator ∈ state.validators.data,
      validator.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork validator)
    (funded : balanceSum state + pendingDepositSum state < 2 ^ 64)
    (summed : effectiveBalanceSum state < 2 ^ 64)
    (churned : (state.depositBalanceToConsume electra).toNat + depositChurnCap config fork < 2 ^ 64)
    (fits : (getCurrentEpoch state).toNat + 1 < 2 ^ 64)
    (finalized : state.finalizedCheckpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64) :
    ∃ after, processPendingDeposits config checks state electra = .ok after ∧
      registryLoad after ≤ preset.VALIDATOR_REGISTRY_LIMIT.toNat ∧
      BalancesMatch after ∧
      balanceSum after + pendingDepositSum after ≤ balanceSum state + pendingDepositSum state ∧
      state.validators.data.size ≤ after.validators.data.size ∧
      after.pendingConsolidations electra = state.pendingConsolidations electra ∧
      getCurrentEpoch after = getCurrentEpoch state ∧
      ParticipationMatches after ∧ InactivityScoresMatch after ∧
      (after.depositBalanceToConsume electra).toNat ≤
        (state.depositBalanceToConsume electra).toNat + depositChurnCap config fork ∧
      ∀ validator ∈ after.validators.data,
        validator.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork validator := by
  have limit := preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt
  have load := loaded
  unfold registryLoad at load
  simp only [electra, ↓reduceDIte] at load
  have within : state.RegistryWithinLimit := by
    unfold BeaconState.RegistryWithinLimit
    omega
  have sums := funded
  unfold pendingDepositSum at sums
  simp only [electra, ↓reduceDIte] at sums
  obtain ⟨churn, churnOk, churnLe⟩ := depositChurnLimit_exists_ok config within summed
  have nextOk : liftAccessor (liftArith (addChecked (getCurrentEpoch state) 1)) =
      .ok (getCurrentEpoch state + 1) := by
    have added : addChecked (getCurrentEpoch state) 1 = .ok (getCurrentEpoch state + 1) :=
      addChecked_of_lt (by simpa using fits)
    simp [added, liftAccessor, liftArith, Except.mapError]
  have churnOk' : liftAccessor (depositChurnLimit config state) = .ok churn := by
    simp [churnOk, liftAccessor, Except.mapError]
  have availableOk : liftAccessor (liftArith (addChecked (state.depositBalanceToConsume electra)
      churn)) = .ok (state.depositBalanceToConsume electra + churn) := by
    have added : addChecked (state.depositBalanceToConsume electra) churn =
        .ok (state.depositBalanceToConsume electra + churn) := addChecked_of_lt (by omega)
    simp [added, liftAccessor, liftArith, Except.mapError]
  have slotOk : liftAccessor (liftArith (computeStartSlotAtEpoch preset
      state.finalizedCheckpoint.epoch)) =
      .ok (state.finalizedCheckpoint.epoch * preset.SLOTS_PER_EPOCH) := by
    simp [computeStartSlotAtEpoch, mulChecked_of_lt finalized, liftAccessor, liftArith,
      Except.mapError]
  obtain ⟨pass, passOk⟩ := passPendingDeposits_exists_ok config checks
    (depositWaits state (state.finalizedCheckpoint.epoch * preset.SLOTS_PER_EPOCH))
    (getCurrentEpoch state + 1) (state.depositBalanceToConsume electra + churn)
    (state.pendingDeposits electra).data.toList state 0 0 #[] matched sized scored
    (by simpa using load) (by omega) (by simpa using Nat.lt_of_le_of_lt (Nat.le_add_left _ _) sums)
  have used := passPendingDeposits_processed_le passOk (UInt64.zero_le)
  obtain ⟨after, computed⟩ : ∃ after, processPendingDeposits config checks state electra =
      .ok after := by
    unfold processPendingDeposits
    simp only [nextOk, churnOk', availableOk, slotOk, bind, Except.bind, passOk, pure,
      Except.pure]
    have subtracted : subChecked (state.depositBalanceToConsume electra + churn) pass.1.processed =
        .ok (state.depositBalanceToConsume electra + churn - pass.1.processed) :=
      subChecked_ok_iff.mpr ⟨UInt64.le_iff_toNat_le.mp used,
        UInt64.toNat_sub_of_le _ _ used⟩
    split
    · simp only [subtracted, liftAccessor, liftArith, Except.mapError]
      exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  have frame := frame_processPendingDeposits computed
  obtain ⟨_, _, applied, _, next, _, _, _, _, _, _, _, _, applies, rest⟩ :=
    processPendingDeposits_applied computed
  have flags := processPendingDeposits_matches computed sized scored
  have bounded := foldlM_ok_invariant
    (fun s : BeaconState preset fork => ∀ validator ∈ s.validators.data,
      validator.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork validator)
    (fun _ _ _ before step => applyPendingDeposit_capped step before) capped applies
  refine ⟨after, computed, (processPendingDeposits_registryLoad_le computed).trans loaded,
    balancesMatch_processPendingDeposits computed matched, ?_, frame.registryGrows, ?_, ?_,
    ?_, ?_, processPendingDeposits_depositBalanceToConsume_le computed, ?_⟩
  · have total := processPendingDeposits_total_le computed
    unfold pendingDepositSum
    simpa only [electra, ↓reduceDIte] using total
  · exact congrFun (processPendingDeposits_pendingConsolidations computed) electra
  · simp only [getCurrentEpoch, frame.slot]
  · exact flags.1
  · exact flags.2
  · subst rest
    exact bounded

/-- From Electra, the pending deposits and then the pending consolidations succeed under bounds.

The bounds are those of the pending deposits.

Both indices of every queued consolidation must also be in the registry.

Before Electra the step returns the state unchanged.

The state after it keeps the registry within its limit and one balance for each validator.

From Altair each list of scores and of flags keeps one entry for each validator.

The sum of the balances plus the amounts in the queue does not grow.

The churn carried to the next epoch is at most the churn carried before plus the cap.

Each effective balance stays at most the largest one of its validator. -/
theorem processPendingBalances_total (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork)
    (loaded : registryLoad state ≤ preset.VALIDATOR_REGISTRY_LIMIT.toNat)
    (matched : BalancesMatch state) (sized : ParticipationMatches state)
    (scored : InactivityScoresMatch state)
    (capped : ∀ validator ∈ state.validators.data,
      validator.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork validator)
    (funded : balanceSum state + pendingDepositSum state < 2 ^ 64)
    (summed : effectiveBalanceSum state < 2 ^ 64)
    (churned : ∀ electra : .pectra ≤ fork,
      (state.depositBalanceToConsume electra).toNat + depositChurnCap config fork < 2 ^ 64)
    (inside : ∀ electra : .pectra ≤ fork,
      ∀ consolidation ∈ (state.pendingConsolidations electra).data,
      consolidation.sourceIndex.toNat < state.validators.data.size ∧
        consolidation.targetIndex.toNat < state.validators.data.size)
    (fits : (getCurrentEpoch state).toNat + 1 < 2 ^ 64)
    (finalized : state.finalizedCheckpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64) :
    ∃ after, processPendingBalances config checks state = .ok after ∧
      registryLoad after ≤ preset.VALIDATOR_REGISTRY_LIMIT.toNat ∧ BalancesMatch after ∧
      ParticipationMatches after ∧ InactivityScoresMatch after ∧
      balanceSum after + pendingDepositSum after ≤ balanceSum state + pendingDepositSum state ∧
      (∀ electra : .pectra ≤ fork, (after.depositBalanceToConsume electra).toNat ≤
        (state.depositBalanceToConsume electra).toNat + depositChurnCap config fork) ∧
      ∀ validator ∈ after.validators.data,
        validator.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork validator := by
  unfold processPendingBalances
  split
  · rename_i electra
    obtain ⟨deposited, depositedOk, loaded', matched', sums, grown, consolidations, epoch,
      sized', scored', carried, bounded⟩ :=
      processPendingDeposits_total config checks state electra loaded matched sized scored capped
        funded summed (churned electra) fits finalized
    obtain ⟨after, afterOk⟩ := processPendingConsolidations_total deposited electra matched'
      (by omega) (by
        rw [consolidations]
        intro consolidation member
        have := inside electra consolidation member
        omega) (by rw [epoch]; exact fits)
    obtain ⟨validators, previous, current, scores, pending, churn, -⟩ :=
      processPendingConsolidations_fields afterOk
    have summedAfter := (processPendingConsolidations_kept afterOk).2
    refine ⟨after, by simp only [depositedOk, afterOk, bind, Except.bind], ?_,
      (frame_processPendingConsolidations afterOk).balancesMatch matched', ?_, ?_, ?_, ?_, ?_⟩
    · unfold registryLoad at loaded' ⊢
      rw [validators, pending]
      exact loaded'
    · intro altair
      rw [previous, current, validators]
      exact sized' altair
    · intro altair
      rw [scores, validators]
      exact scored' altair
    · unfold pendingDepositSum at sums ⊢
      rw [summedAfter, pending]
      exact sums
    · intro _
      rw [churn]
      exact carried
    · rw [validators]
      exact bounded
  · rename_i before
    exact ⟨state, rfl, loaded, matched, sized, scored, Nat.le_refl _,
      fun electra => absurd electra before, capped⟩

end EthLib.Consensus
