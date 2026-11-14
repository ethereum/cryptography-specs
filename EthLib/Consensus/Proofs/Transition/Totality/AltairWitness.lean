module

public import EthLib.Consensus.Proofs.Transition.Totality.Run
public import EthLib.Consensus.Proofs.Transition.Totality.RunFromAltair
public import EthLib.Cryptography.Proofs.Bls.SignaturesCorrect

/-!
# Proofs: a mainnet state at Altair whose run of slots succeeds up to Electra

The state is at the Altair fork epoch and holds one validator, with no vote and no finality.

Its key is the generator of `G1`, and its effective balance is 32 ETH.

Its balance is `10^5` ETH, more than the leak takes before the Electra fork epoch.

It meets the facts of a run that starts at its epoch, under the mainnet bounds.

So every slot advance up to the last slot before Electra succeeds.

The run makes 1131 sync committee draws, and each one finds the validator.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls

/-- The key of the witness: the generator of `G1`, compressed. -/
def witnessKey : BLSPubkey := Signatures.pointToPubkey (G1.mul G1.generator 1)

/-- The one validator of the witness.

It is active from genesis with no exit set, and its effective balance is 32 ETH. -/
def witnessValidator : Validator where
  pubkey := witnessKey
  withdrawalCredentials := Vector.replicate 32 0
  effectiveBalance := 32 * 10 ^ 9
  slashed := false
  activationEligibilityEpoch := GENESIS_EPOCH
  activationEpoch := GENESIS_EPOCH
  exitEpoch := FAR_FUTURE_EPOCH
  withdrawableEpoch := FAR_FUTURE_EPOCH

/-- The sync committee of the witness: its one key, at every seat.

Its aggregate key is the generator times the 512 seats. -/
def witnessCommittee : SyncCommittee Preset.mainnet where
  pubkeys := Vector.replicate _ witnessKey
  aggregatePubkey := Signatures.pointToPubkey (G1.mul G1.generator 512)

/-- A mainnet state at the first slot of the Altair fork epoch, with one validator.

The validator holds `10^5` ETH, and no one has voted.

Every checkpoint is at genesis, so the chain is in the leak.

Both sync committees hold its key at every seat.

The deposit data counts one deposit, and every other field is zero or empty. -/
def altairWitnessState : BeaconState Preset.mainnet .altair where
  genesisTime := 0
  genesisValidatorsRoot := Vector.replicate 32 0
  slot := 74240 * 32
  forkVersions :=
    ⟨Config.mainnet.GENESIS_FORK_VERSION, Config.mainnet.ALTAIR_FORK_VERSION, 74240⟩
  latestBlockHeader := ⟨0, 0, Vector.replicate 32 0, Vector.replicate 32 0, Vector.replicate 32 0⟩
  blockRoots := .ofVector (Vector.replicate _ (Vector.replicate 32 0))
  stateRoots := .ofVector (Vector.replicate _ (Vector.replicate 32 0))
  historicalRoots := ⟨#[], by simp⟩
  eth1Data := fun _ => ⟨Vector.replicate 32 0, 1, Vector.replicate 32 0⟩
  eth1DataVotes := fun _ => ⟨#[], by simp⟩
  eth1DepositIndex := fun _ => 1
  validators := .ofData #[witnessValidator] fun _ => by decide
  balances := ⟨#[10 ^ 14], fun _ => by decide⟩
  randaoMixes := .ofVector (Vector.replicate _ (Vector.replicate 32 0))
  slashings := .ofVector (Vector.replicate _ 0)
  previousEpochAttestations := fun before => absurd before (by decide)
  currentEpochAttestations := fun before => absurd before (by decide)
  previousEpochParticipation := fun _ => ⟨#[0], fun _ => by decide⟩
  currentEpochParticipation := fun _ => ⟨#[0], fun _ => by decide⟩
  justificationBits := ⟨Vector.replicate _ false⟩
  previousJustifiedCheckpoint := ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩
  currentJustifiedCheckpoint := ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩
  finalizedCheckpoint := ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩
  inactivityScores := fun _ => ⟨#[0], fun _ => by decide⟩
  currentSyncCommittee := fun _ => .of witnessCommittee
  nextSyncCommittee := fun _ => .of witnessCommittee
  latestExecutionPayloadHeader := fun during => absurd during.1 (by decide)
  latestBlockHash := fun since => absurd since (by decide)
  nextWithdrawalIndex := fun since => absurd since (by decide)
  nextWithdrawalValidatorIndex := fun since => absurd since (by decide)
  historicalSummaries := fun since => absurd since (by decide)
  depositRequestsStartIndex := fun during => absurd during.1 (by decide)
  depositBalanceToConsume := fun since => absurd since (by decide)
  exitBalanceToConsume := fun since => absurd since (by decide)
  earliestExitEpoch := fun since => absurd since (by decide)
  consolidationBalanceToConsume := fun since => absurd since (by decide)
  earliestConsolidationEpoch := fun since => absurd since (by decide)
  pendingDeposits := fun since => absurd since (by decide)
  pendingPartialWithdrawals := fun since => absurd since (by decide)
  pendingConsolidations := fun since => absurd since (by decide)
  proposerLookahead := fun since => absurd since (by decide)
  builders := fun since => absurd since (by decide)
  nextWithdrawalBuilderIndex := fun since => absurd since (by decide)
  executionPayloadAvailability := fun since => absurd since (by decide)
  builderPendingPayments := fun since => absurd since (by decide)
  builderPendingWithdrawals := fun since => absurd since (by decide)
  latestExecutionPayloadBid := fun since => absurd since (by decide)
  payloadExpectedWithdrawals := fun since => absurd since (by decide)
  ptcWindow := fun since => absurd since (by decide)

/-- The key of the witness passes validation. -/
theorem witnessKey_valid :
    ∃ point, G1.keyValidatePoint (packBytes witnessKey) = .ok point := by
  open scoped Fr in
  obtain ⟨point, valid, -⟩ := G1.keyValidatePoint_compress_mul (a := 1) one_ne_zero
  exact ⟨point, by rw [witnessKey, Signatures.packBytes_pointToPubkey]; exact valid⟩

/-! ## The fields of the witness -/

/-- The witness is at the first slot of the Altair fork epoch. -/
private theorem witness_slot : altairWitnessState.slot = 74240 * 32 := rfl

/-- The witness is at the Altair fork epoch. -/
private theorem witness_epoch : (getCurrentEpoch altairWitnessState).toNat = 74240 := by
  rw [getCurrentEpoch, computeEpochAtSlot, witness_slot]
  rfl

/-- The registry of the witness holds its one validator. -/
private theorem witness_validators : altairWitnessState.validators.data = #[witnessValidator] :=
  rfl

/-- The one balance of the witness is `10^5` ETH. -/
private theorem witness_balances : altairWitnessState.balances.data = #[10 ^ 14] := rfl

/-- No balance of the witness has been slashed. -/
private theorem witness_slashings :
    altairWitnessState.slashings.elements = Vector.replicate _ 0 := rfl

/-- No one has signed in the witness. -/
private theorem witness_quiet : Quiet altairWitnessState := by
  have never : Fork.altair < .altair → False := by decide
  refine ⟨⟨fun before => (never before).elim, fun _ flags member => ?_⟩,
    fun before => (never before).elim, fun _ flags member => ?_⟩
  all_goals
    change flags ∈ #[(0 : ParticipationFlags)] at member
    rw [Array.mem_singleton] at member
    exact member

/-- The witness meets the facts of a run that starts at its epoch, under the mainnet bounds.

The budget of effective balances is `2^57` Gwei. -/
theorem runHolds_altairWitnessState :
    RunHolds Config.mainnet (RunStart.mainnet 74240) (2 ^ 57) 74240 altairWitnessState := by
  have altair : Fork.altair < .altair → False := by decide
  have notElectra : ¬ Fork.pectra ≤ .altair := by decide
  have notCapella : ¬ Fork.shapella ≤ .altair := by decide
  refine
    { started := by rw [witness_epoch]
      invariant := ?_
      shaped := ?_
      wellFormed := fun before => (altair before).elim
      resolved := fun before => (altair before).elim
      early := ?_
      voted := fun before => (altair before).elim
      bounded := ?_
      quietCurrent := fun _ => ?_
      quiet := fun _ => ?_ }
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · unfold BalancesMatch
      rw [witness_balances, witness_validators]
      rfl
    · intro validator member
      rw [witness_validators, Array.mem_singleton] at member
      subst member
      exact UInt64.le_refl _
    · exact ⟨UInt64.le_refl _, UInt64.le_refl _⟩
    · exact UInt64.zero_le
    · intro _ validator member
      rw [witness_validators, Array.mem_singleton] at member
      subst member
      decide
  · refine ⟨?_, fun _ => ⟨rfl, rfl⟩, fun _ => rfl, ?_, fun electra => (notElectra electra).elim⟩
    · unfold BalancesMatch
      rw [witness_balances, witness_validators]
      rfl
    · intro validator member
      rw [witness_validators, Array.mem_singleton] at member
      subst member
      decide
  · intro first
    have := UInt64.le_iff_toNat_le.mp first
    rw [witness_epoch] at this
    exact absurd this (by decide)
  · rw [witness_epoch, Nat.sub_self]
    refine ⟨?_, Or.inl ?_, ?_, fun _ score member => ?_, fun validator member => ?_,
      fun electra => (notElectra electra).elim, ?_, fun capella => (notCapella capella).elim,
      fun electra => (notElectra electra).elim, fun electra => (notElectra electra).elim, ?_⟩
    · rw [balanceSum, pendingDepositSum, dite_eq_right_of_eq_false (eq_false notElectra),
        witness_balances, Nat.zero_mul, Nat.add_zero]
      decide
    · rw [effectiveBalanceSum, witness_validators]
      decide
    · rw [registryLoad, dite_eq_right_of_eq_false (eq_false notElectra), witness_validators]
      decide
    · change score ∈ #[(0 : UInt64)] at member
      rw [Array.mem_singleton] at member
      subst member
      decide
    · rw [witness_validators, Array.mem_singleton] at member
      subst member
      exact fun set => absurd rfl set
    · exact Nat.zero_le _
    · rw [slashedBalanceSum, witness_slashings]
      simp
  · exact witness_quiet.1
  · exact witness_quiet

/-- The balance of the witness covers the cap and the drain of the epochs before Electra. -/
private theorem witness_funded {epochs : Nat} (within : epochs ≤ 289791) :
    Preset.mainnet.MAX_EFFECTIVE_BALANCE.toNat + Preset.mainnet.capDrain Config.mainnet 0 epochs ≤
      (10 ^ 14 : Gwei).toNat := by
  have root : Preset.mainnet.EFFECTIVE_BALANCE_INCREMENT.toNat.sqrt = 31622 :=
    (Nat.eq_sqrt.mpr ⟨by decide, by decide⟩).symm
  have drain := (Preset.capDrain_mono Preset.mainnet Config.mainnet 0 within).trans
    (Preset.capDrain_le Preset.mainnet Config.mainnet 0 289791)
  rw [root] at drain
  refine (Nat.add_le_add_left drain _).trans ?_
  decide

/-- On mainnet, every slot advance from the witness up to the last slot before Electra succeeds.

The run starts at the Altair fork epoch and crosses at most 289791 epoch boundaries.

The state that the advance returns keeps the facts of the run. -/
theorem processSlotsAcross_exists_ok_altairWitnessState {checks : SignatureChecks} {slot : Slot}
    (later : 74240 * 32 < slot.toNat) (beforeElectra : slot.toNat / 32 < 364032) :
    ∃ after, processSlotsAcross Config.mainnet checks ⟨.altair, altairWitnessState⟩ slot =
        .ok after ∧
      RunHolds Config.mainnet (RunStart.mainnet 74240) (2 ^ 57) 74240 after.state := by
  have slot0 : altairWitnessState.slot.toNat = 74240 * 32 := by rw [witness_slot]; rfl
  have count : altairWitnessState.slot.toNat + (slot.toNat - 74240 * 32) = slot.toNat := by
    omega
  have epochs : slot.toNat / 32 - 74240 ≤ 289791 := by omega
  -- The one key of the registry passes validation.
  have keys : ∀ validator ∈ altairWitnessState.validators.data,
      ∃ point, Cryptography.Bls.G1.keyValidatePoint (packBytes validator.pubkey) = .ok point := by
    intro validator member
    rw [witness_validators, Array.mem_singleton] at member
    subst member
    exact witnessKey_valid
  -- Every inactivity score is zero.
  have scored : ∀ score ∈ (altairWitnessState.inactivityScores (by decide)).data,
      score.toNat ≤ 0 := by
    intro score member
    change score ∈ #[(0 : UInt64)] at member
    rw [Array.mem_singleton] at member
    subst member
    exact Nat.zero_le _
  obtain ⟨signers, draws, limit⟩ := runHypotheses_of_quiet_altair (config := Config.mainnet)
    (checks := checks) (forked := ⟨.altair, altairWitnessState⟩)
    (count := slot.toNat - 74240 * 32) (by decide) (by decide)
    maxEffectiveBalancesAligned_mainnet (by decide) (by decide) witness_quiet keys
    (index := 0) (validator := witnessValidator) (balance := 10 ^ 14) (scoreStart := 0)
    (by rw [witness_validators]; rfl) ⟨rfl, by decide, UInt64.zero_le, rfl, rfl⟩ rfl scored
    (by rw [count]; exact beforeElectra)
    (by rw [count]; exact witness_funded epochs)
  obtain ⟨after, computed, holds⟩ := processSlotsAcross_exists_ok_mainnet (checks := checks)
    (forked := ⟨.altair, altairWitnessState⟩) (slot := slot)
    (by rw [witness_epoch]; decide) (by rw [witness_epoch]; exact runHolds_altairWitnessState)
    (UInt64.lt_iff_toNat_lt.mpr (by rw [slot0]; exact later))
    (by rw [witness_epoch]; change slot.toNat / 32 ≤ 74240 + 2250000; omega)
    signers draws limit
  rw [witness_epoch] at holds
  exact ⟨after, computed, holds⟩

end EthLib.Consensus
