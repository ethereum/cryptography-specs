module

public import EthLib.Consensus.Proofs.Transition.Totality.EpochElectra
public import EthLib.Consensus.Proofs.Transition.Totality.Rewards
import EthLib.Consensus.Proofs.Transition.RegistryLifecycle

/-!
# Proofs: a validator at the cap stays there through an epoch before Electra

Before Electra an epoch adds no validator and changes no key.

From Altair, a validator at the cap loses at most one base reward and its inactivity penalty.

If it starts at least that much above the cap, its record is the same after the epoch.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 EpochStage EpochTrace

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state ready after : BeaconState preset fork}

/-- From Altair, a bound on what an epoch's rewards take from a validator at the cap.

The score is a bound on its inactivity score after the update.

The missed source and target cost at most one base reward, at a total of one increment.

The inactivity penalty adds the cap times the score, over the bias times the smaller quotient.

The two quotients are those of Altair and Bellatrix. -/
def Preset.capPenalty (preset : Preset) (config : Config) (score : Nat) : Nat :=
  preset.MAX_EFFECTIVE_BALANCE.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      (preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat /
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat.sqrt) +
    preset.MAX_EFFECTIVE_BALANCE.toNat * score /
      (config.INACTIVITY_SCORE_BIAS.toNat * min preset.INACTIVITY_PENALTY_QUOTIENT_ALTAIR.toNat
        preset.INACTIVITY_PENALTY_QUOTIENT_BELLATRIX.toNat)

/-- A validator at the cap before Electra, active at an epoch and every epoch after it.

It is unslashed, has joined the activation queue, and is active from that epoch.

It has no exit set, so it stays active, and its effective balance is the cap before Electra. -/
structure AtCap (preset : Preset) (epoch : Epoch) (validator : Validator) : Prop where
  /-- The validator is not slashed. -/
  unslashed : validator.slashed = false
  /-- The validator has joined the activation queue. -/
  queued : validator.activationEligibilityEpoch ≠ FAR_FUTURE_EPOCH
  /-- The validator is activated at that epoch or before. -/
  active : validator.activationEpoch ≤ epoch
  /-- The validator has no exit set. -/
  staying : validator.exitEpoch = FAR_FUTURE_EPOCH
  /-- The effective balance is the cap before Electra. -/
  capped : validator.effectiveBalance = preset.MAX_EFFECTIVE_BALANCE

/-! ## The keys -/

/-- Before Electra, one stage of an epoch keeps the keys as a prefix and adds no validator. -/
private theorem keys_action (before : fork < .pectra) {stage : EpochStage}
    {s t : BeaconState preset fork} (computed : action config checks stage s = .ok t) :
    validatorKeys s <+: validatorKeys t ∧ t.validators.data.size ≤ s.validators.data.size := by
  by_cases ordinary : stage ≠ .justification ∧ stage ≠ .payments ∧ stage ≠ .participation ∧
      stage ≠ .pendingDeposits
  · exact ⟨(mutatorEpochFrameLaws.toEpochStepLaws.epochEdge ordinary computed).pubkeysPrefix,
      Nat.le_of_eq (loadKeptLaws.epochEdge ordinary computed).1⟩
  have notElectra : ¬ Fork.pectra ≤ fork := Nat.not_le_of_lt before
  have notGloas : ¬ Fork.glamsterdam ≤ fork := fun h => notElectra (Nat.le_trans (by decide) h)
  have edge := action_cases.mp computed
  have same (kept : t.validators = s.validators) :
      validatorKeys s <+: validatorKeys t ∧ t.validators.data.size ≤ s.validators.data.size := by
    rw [validatorKeys, validatorKeys, kept]
    exact ⟨List.prefix_refl _, Nat.le_refl _⟩
  cases stage <;> simp only [ne_eq, not_and, Decidable.not_not, reduceCtorEq,
    imp_false, not_true_eq_false] at ordinary <;> simp only [Edge] at edge
  case justification => exact same (processJustificationAndFinalization_keeps edge).2.2.2.2.2.1
  case pendingDeposits =>
    simp only [notElectra, ↓reduceDIte] at edge
    exact same (by rw [edge])
  case payments =>
    simp only [notGloas, ↓reduceDIte] at edge
    exact same (by rw [edge])
  case participation =>
    split at edge
    · exact same (by rw [← edge]; rfl)
    · exact ⟨(mutatorEpochFrameLaws.toEpochStepLaws.processParticipationRecordUpdates
        edge).pubkeysPrefix,
        Nat.le_of_eq (loadKeptLaws.processParticipationRecordUpdates edge).1⟩

/-- Before Electra, the stages before the sync committee update keep the keys of the registry. -/
theorem run_readyStages_validatorKeys (before : fork < .pectra)
    (computed : run (action config checks) readyStages state = .ok ready) :
    validatorKeys ready = validatorKeys state := by
  have kept := (run_ok_iff.mp computed).transport
    (fun s t => validatorKeys s <+: validatorKeys t ∧
      t.validators.data.size ≤ s.validators.data.size)
    (fun _ => ⟨List.prefix_refl _, Nat.le_refl _⟩)
    (fun one two => ⟨one.1.trans two.1, Nat.le_trans two.2 one.2⟩)
    (fun _ _ _ _ ok => keys_action before ok)
  exact (kept.1.eq_of_length_le (by simpa [validatorKeys] using kept.2)).symm

/-- Before Electra, the epoch transition keeps the keys of the registry. -/
theorem processEpoch_validatorKeys (before : fork < .pectra)
    (computed : processEpoch config checks state = .ok after) :
    validatorKeys after = validatorKeys state := by
  obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame computed
  have same : validatorKeys justified = validatorKeys state := by
    unfold validatorKeys
    rw [(processJustificationAndFinalization_keeps justifiedOk).2.2.2.2.2.1]
  have kept := frame.pubkeysPrefix
  rw [same] at kept
  -- Before Electra the load is the size of the registry, which the epoch never raises.
  have load := processEpoch_registryLoad_le computed
  have notElectra : ¬ Fork.pectra ≤ fork := Nat.not_le_of_lt before
  simp only [registryLoad, notElectra, ↓reduceDIte, Nat.add_zero] at load
  exact (kept.eq_of_length_le (by simpa [validatorKeys] using load)).symm

/-! ## The validator at the cap -/

/-- Two states with the same registry, the same balances and the same slot. -/
private def Same (s t : BeaconState preset fork) : Prop :=
  t.validators = s.validators ∧ t.balances = s.balances ∧ t.slot = s.slot

/-- From Altair before Electra, eleven stages keep the registry, the balances and the slot. -/
private theorem same_action (altair : .altair ≤ fork) (before : fork < .pectra)
    {stage : EpochStage} (member : stage ∈ [.eth1Reset, .pendingDeposits,
      .pendingConsolidations, .payments, .slashingsReset, .randaoReset, .history, .participation,
      .syncCommittees, .proposerLookahead, .ptcWindow])
    {s t : BeaconState preset fork} (computed : action config checks stage s = .ok t) :
    Same s t := by
  have notElectra : ¬ Fork.pectra ≤ fork := Nat.not_le_of_lt before
  have notGloas : ¬ Fork.glamsterdam ≤ fork := fun h => notElectra (Nat.le_trans (by decide) h)
  have edge := action_cases.mp computed
  cases stage <;> simp only [Edge] at edge <;> try (simp at member; done)
  case eth1Reset =>
    split at edge
    · rw [processEth1DataReset_frame edge]
      exact ⟨rfl, rfl, rfl⟩
    · subst edge
      exact ⟨rfl, rfl, rfl⟩
  case pendingDeposits | pendingConsolidations | payments =>
    simp only [notElectra, notGloas, ↓reduceDIte] at edge
    subst edge
    exact ⟨rfl, rfl, rfl⟩
  case slashingsReset =>
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq edge
    exact ⟨rfl, rfl, rfl⟩
  case randaoReset =>
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq edge
    exact ⟨rfl, rfl, rfl⟩
  case history =>
    split at edge
    · unfold processHistoricalSummariesUpdate at edge
      simp only [bind, Except.bind, pure, Except.pure] at edge
      repeat' (split at edge <;> try cases edge)
      all_goals exact ⟨rfl, rfl, rfl⟩
    · unfold processHistoricalRootsUpdate at edge
      simp only [bind, Except.bind, pure, Except.pure] at edge
      repeat' (split at edge <;> try cases edge)
      all_goals exact ⟨rfl, rfl, rfl⟩
  case participation =>
    simp only [altair, ↓reduceDIte] at edge
    subst edge
    exact ⟨rfl, rfl, rfl⟩
  case syncCommittees =>
    simp only [altair, ↓reduceDIte] at edge
    unfold processSyncCommitteeUpdates at edge
    simp only [bind, Except.bind, pure, Except.pure] at edge
    repeat' (split at edge <;> try cases edge)
    all_goals exact ⟨rfl, rfl, rfl⟩
  case proposerLookahead =>
    split at edge
    · simp only [processProposerLookahead, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at edge
      obtain ⟨_, _, _, _, rfl⟩ := edge
      exact ⟨rfl, rfl, rfl⟩
    · subst edge
      exact ⟨rfl, rfl, rfl⟩
  case ptcWindow =>
    simp only [notGloas, ↓reduceDIte] at edge
    subst edge
    exact ⟨rfl, rfl, rfl⟩

/-- A fold of the balance through some deltas loses at most the sum of the penalties. -/
private theorem foldlM_penalties_le {i : Nat} :
    ∀ (deltas : List (Array Gwei × Array Gwei)) (start result : Gwei),
      deltas.foldlM (fun balance delta => (addChecked balance (delta.1.getD i 0)).map
          fun raised => saturatingSub raised (delta.2.getD i 0)) start = .ok result →
        start.toNat ≤ result.toNat + (deltas.map fun delta => (delta.2.getD i 0).toNat).sum := by
  intro deltas
  induction deltas with
  | nil =>
    intro start result computed
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    simp
  | cons delta rest ih =>
    intro start result computed
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, first, folded⟩ := computed
    cases added : addChecked start (delta.1.getD i 0) with
    | error => simp only [added, Except.map, reduceCtorEq] at first
    | ok raised =>
      simp only [added, Except.map, Except.ok.injEq] at first
      subst first
      have sum := (addChecked_ok_iff.mp added).2
      have later := ih _ _ folded
      rw [toNat_saturatingSub] at later
      simp only [List.map_cons, List.sum_cons]
      omega

/-- From Altair, the base reward of a validator at the cap is at most its value at one increment.

The total active balance is at least one increment, and a larger total gives a smaller reward. -/
private theorem baseReward_le (altair : .altair ≤ fork) {s : BeaconState preset fork}
    {total base : Gwei} (totalOk : getTotalActiveBalance s = .ok total) {i : Nat}
    {validator : Validator} (found : s.validators.data[i]? = some validator)
    (within : s.RegistryWithinLimit)
    (capped : validator.effectiveBalance = preset.MAX_EFFECTIVE_BALANCE)
    (baseOk : getBaseReward s total i.toUInt64 = .ok base) :
    base.toNat ≤ preset.MAX_EFFECTIVE_BALANCE.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      (preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat /
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat.sqrt) := by
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have read := getValidator_toUInt64 within inside
  rw [Array.getElem?_eq_getElem inside, Option.some.injEq] at found
  rw [found] at read
  simp only [getBaseReward, bind_ok_iff, read, altair, ↓reduceIte, liftArith, mapError_ok_iff,
    Except.ok.injEq, exists_eq_left'] at baseOk
  obtain ⟨per, perOk, multiplied⟩ := baseOk
  simp only [getBaseRewardPerIncrement, liftArith, mapError_ok_iff, bind_ok_iff] at perOk
  obtain ⟨product, productOk, divided⟩ := perOk
  have low := UInt64.le_iff_toNat_le.mp
    (le_getTotalBalance (getTotalActiveBalance_ok totalOk))
  rw [(mulChecked_ok_iff.mp multiplied).2, UInt64.toNat_div, capped]
  rw [divChecked_ok_iff, toNat_integerSquareroot] at divided
  rw [(mulChecked_ok_iff.mp productOk).2] at divided
  rw [divided.2]
  -- A total of at least one increment has a root of at least that of one increment.
  rcases Nat.eq_zero_or_pos preset.EFFECTIVE_BALANCE_INCREMENT.toNat with zero | positive
  · simp [zero]
  · exact Nat.mul_le_mul_left _
      (Nat.div_le_div_left (Nat.sqrt_le_sqrt low) (Nat.sqrt_pos.mpr positive))

/-- From Altair, a flag takes from a validator at the cap at most its weight of a base reward.

That base reward is its value at a total of one increment. -/
private theorem flagPenalty_le (altair : .altair ≤ fork) {s : BeaconState preset fork}
    (within : s.RegistryWithinLimit) {flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length}
    {rewards penalties : Array Gwei}
    (computed : getFlagIndexDeltas s altair flagIndex = .ok (rewards, penalties)) {i : Nat}
    {validator : Validator} (found : s.validators.data[i]? = some validator)
    (capped : validator.effectiveBalance = preset.MAX_EFFECTIVE_BALANCE) :
    (penalties.getD i 0).toNat ≤
      preset.MAX_EFFECTIVE_BALANCE.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        (preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat.sqrt) *
        PARTICIPATION_FLAG_WEIGHTS[flagIndex].toNat / WEIGHT_DENOMINATOR.toNat := by
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  obtain ⟨participating, _, total, _, _, totalOk, each⟩ := getFlagIndexDeltas_getD within computed
  obtain ⟨eligible, -, absent, present⟩ := each i inside
  cases eligible
  · rw [(absent rfl).2]
    exact Nat.zero_le _
  obtain ⟨base, baseOk, set, unset⟩ := present rfl
  have bounded := baseReward_le altair totalOk found within capped baseOk
  by_cases member : i.toUInt64 ∈ participating
  · obtain ⟨_, _, _, zero⟩ := set member
    rw [zero]
    exact Nat.zero_le _
  · rw [(unset member).2]
    split
    · exact Nat.zero_le _
    · exact Nat.div_le_div_right (Nat.mul_le_mul_right _ bounded)

/-- From Altair, the inactivity penalty of a validator at the cap is at most that of a bound.

The bound must be at least every inactivity score. -/
private theorem inactivityPenalty_le (altair : .altair ≤ fork) {s : BeaconState preset fork}
    (within : s.RegistryWithinLimit)
    (quotients : 0 < min preset.INACTIVITY_PENALTY_QUOTIENT_ALTAIR.toNat
      preset.INACTIVITY_PENALTY_QUOTIENT_BELLATRIX.toNat)
    {rewards penalties : Array Gwei}
    (computed : getInactivityPenaltyDeltas config s = .ok (rewards, penalties)) {i : Nat}
    {validator : Validator} (found : s.validators.data[i]? = some validator)
    (capped : validator.effectiveBalance = preset.MAX_EFFECTIVE_BALANCE) {bound : Nat}
    (scored : ∀ score ∈ (s.inactivityScores altair).data, score.toNat ≤ bound) :
    (penalties.getD i 0).toNat ≤ preset.MAX_EFFECTIVE_BALANCE.toNat * bound /
      (config.INACTIVITY_SCORE_BIAS.toNat * min preset.INACTIVITY_PENALTY_QUOTIENT_ALTAIR.toNat
        preset.INACTIVITY_PENALTY_QUOTIENT_BELLATRIX.toNat) := by
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  obtain ⟨matching, _, each⟩ := getInactivityPenaltyDeltas_getD_of_altair altair within computed
  obtain ⟨eligible, _, _, exempt, pays⟩ := each i inside
  by_cases owed : eligible = true ∧ i.toUInt64 ∉ matching
  · obtain ⟨score, scoreOk, penalty⟩ := pays owed.1 owed.2
    rw [penalty]
    rw [Array.getElem?_eq_getElem inside, Option.some.injEq] at found
    rw [found, capped]
    have low := scored score (Array.mem_of_getElem? scoreOk)
    -- From Altair the quotient of the fork is one of the two, so at least the least of them.
    have least : min preset.INACTIVITY_PENALTY_QUOTIENT_ALTAIR.toNat
        preset.INACTIVITY_PENALTY_QUOTIENT_BELLATRIX.toNat ≤
        (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat := by
      simp only [parameters, ge_iff_le]
      split
      · exact Nat.min_le_right _ _
      · exact Nat.min_le_left _ _
    rcases Nat.eq_zero_or_pos config.INACTIVITY_SCORE_BIAS.toNat with zero | biased
    · simp [zero]
    · exact Nat.div_le_div (Nat.mul_le_mul_left _ low) (Nat.mul_le_mul_left _ least)
        (Nat.ne_of_gt (Nat.mul_pos biased quotients))
  · rw [exempt (by cases eligible <;> simp_all)]
    exact Nat.zero_le _

/-- From Altair before Electra, the rewards take at most one penalty from a validator at the cap.

The penalty is computed at a bound on every inactivity score. -/
private theorem rewards_atCap (altair : .altair ≤ fork) (before : fork < .pectra)
    (quotients : 0 < min preset.INACTIVITY_PENALTY_QUOTIENT_ALTAIR.toNat
      preset.INACTIVITY_PENALTY_QUOTIENT_BELLATRIX.toNat)
    {s t : BeaconState preset fork} (computed : processRewardsAndPenalties config s = .ok t)
    {i : Nat} {validator : Validator} {balance : Gwei} {bound : Nat}
    (found : s.validators.data[i]? = some validator)
    (capped : validator.effectiveBalance = preset.MAX_EFFECTIVE_BALANCE)
    (held : s.balances.data[i]? = some balance)
    (scored : ∀ score ∈ (s.inactivityScores altair).data, score.toNat ≤ bound) :
    ∃ left, t.balances.data[i]? = some left ∧
      balance.toNat ≤ left.toNat + preset.capPenalty config bound := by
  by_cases genesis : getCurrentEpoch s = GENESIS_EPOCH
  · rw [processRewardsAndPenalties_genesis config genesis, Except.ok.injEq] at computed
    subst computed
    exact ⟨balance, held, Nat.le_add_right _ _⟩
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have within : s.RegistryWithinLimit := s.validators.bound (Nat.lt_trans before (by decide))
  obtain ⟨flagDeltas, ⟨rewards, penalties⟩, flagged, penalized, applied⟩ :=
    processRewardsAndPenalties_balances_of_altair altair genesis computed
  obtain ⟨atIndex, chained, -⟩ := applied i
  refine ⟨_, by rw [atIndex inside, held]; rfl, ?_⟩
  have lower := foldlM_penalties_le _ _ _ (chained inside balance held)
  have whole : List.finRange PARTICIPATION_FLAG_WEIGHTS.length =
      [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩] := by decide
  rw [whole] at flagged
  simp only [List.mapM_cons, List.mapM_nil, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at flagged
  obtain ⟨⟨_, p0⟩, d0, _, ⟨⟨_, p1⟩, d1, _, ⟨⟨_, p2⟩, d2, _, rfl, rfl⟩, rfl⟩, rfl⟩ := flagged
  have bounded0 := flagPenalty_le altair within d0 found capped
  have bounded1 := flagPenalty_le altair within d1 found capped
  have bounded2 := flagPenalty_le altair within d2 found capped
  have inactive := inactivityPenalty_le altair within quotients penalized found capped scored
  have weight0 : PARTICIPATION_FLAG_WEIGHTS[(⟨0, by decide⟩ :
      Fin PARTICIPATION_FLAG_WEIGHTS.length)].toNat = 14 := rfl
  have weight1 : PARTICIPATION_FLAG_WEIGHTS[(⟨1, by decide⟩ :
      Fin PARTICIPATION_FLAG_WEIGHTS.length)].toNat = 26 := rfl
  have weight2 : PARTICIPATION_FLAG_WEIGHTS[(⟨2, by decide⟩ :
      Fin PARTICIPATION_FLAG_WEIGHTS.length)].toNat = 14 := rfl
  have denominator : WEIGHT_DENOMINATOR.toNat = 64 := by decide
  rw [weight0, denominator] at bounded0
  rw [weight1, denominator] at bounded1
  rw [weight2, denominator] at bounded2
  simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil] at lower ⊢
  -- The three flags take at most 54 of 64 parts of one base reward.
  unfold Preset.capPenalty
  generalize preset.MAX_EFFECTIVE_BALANCE.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
    (preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat /
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat.sqrt) = base at *
  omega

/-- Before Electra, the registry updates keep the record of a validator at the cap.

The ejection balance must be below the cap, and the current epoch below the last one. -/
private theorem registry_atCap (before : fork < .pectra)
    (ejection : config.EJECTION_BALANCE < preset.MAX_EFFECTIVE_BALANCE)
    {s t : BeaconState preset fork} (computed : processRegistryUpdates config s = .ok t)
    {i : Nat} {validator : Validator} (found : s.validators.data[i]? = some validator)
    (atCap : AtCap preset (getCurrentEpoch s) validator)
    (small : (getCurrentEpoch s).toNat + 1 < 2 ^ 64) :
    t.validators.data[i]? = some validator := by
  have notElectra : ¬ Fork.pectra ≤ fork := Nat.not_le_of_lt before
  have notGloas : fork < .glamsterdam := Nat.lt_trans before (by decide)
  -- A write at another position keeps the validator at this one.
  have other {b : BeaconState preset fork} {j : Nat} (inside : j < b.validators.data.size)
      (v : Validator) (different : j ≠ i) :
      (b.putValidator j inside v).validators.data[i]? = b.validators.data[i]? := by
    simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set]
    exact Array.getElem?_set_ne inside different
  unfold processRegistryUpdates at computed
  simp only [notElectra, ↓reduceIte, bind_ok_iff] at computed
  obtain ⟨updated, updatedOk, activated⟩ := computed
  -- The first pass neither queues nor ejects the validator, and leaves it as it is.
  have first : updated.validators.data[i]? = some validator := by
    refine foldlM_ok_invariant (fun b : BeaconState preset fork =>
      b.validators.data[i]? = some validator) (fun b j b' kept ok => ?_) found updatedOk
    simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨read, readOk, queued, queuedOk, marked, markedOk, ok⟩ := ok
    obtain ⟨inside, rfl⟩ := setValidatorAt_ok markedOk
    by_cases same : j = i
    · subst same
      simp only [getValidatorAt, kept, Except.ok.injEq] at readOk
      subst readOk
      have notQueued : isEligibleForActivationQueue preset fork validator = false := by
        simp [isEligibleForActivationQueue, atCap.queued]
      simp only [queueForActivation, notQueued, Bool.false_eq_true, ↓reduceIte, pure,
        Except.pure, Except.ok.injEq] at queuedOk
      subst queuedOk
      have notLow : ¬ validator.effectiveBalance ≤ config.EJECTION_BALANCE := by
        rw [atCap.capped]
        exact UInt64.not_le.mpr ejection
      simp only [notLow, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte, pure,
        Except.pure, Except.ok.injEq] at ok
      subst ok
      simp [BeaconState.putValidator]
    · split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨position, positionOk, exited⟩ := ok
        have named := (ofNatChecked_ok_iff.mp (mapError_ok_iff.mp positionOk)).2
        obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok exited
        · rw [other inside _ same]
          exact kept
        · obtain ⟨_, _, rfl⟩ := exitQueue_eq queue
          obtain ⟨inside', rfl⟩ := setValidator_ok set
          rw [other inside' _ (named ▸ same)]
          change (b.putValidator j inside queued).validators.data[i]? = _
          rw [other inside _ same]
          exact kept
      · simp only [pure, Except.pure, Except.ok.injEq] at ok
        subst ok
        rw [other inside _ same]
        exact kept
  -- The validator was activated by the current epoch, so it is not in the activation queue.
  refine foldlM_ok_invariant_of_mem (fun b : BeaconState preset fork =>
    b.validators.data[i]? = some validator) (fun b index b' member kept ok => ?_) first activated
  obtain ⟨position, queued, named, located, eligible⟩ :=
    mem_activationQueue (List.mem_of_mem_take member)
  have apart : position ≠ i := by
    rintro rfl
    rw [first, Option.some.injEq] at located
    subst located
    have far := activationEpoch_of_isEligibleForActivation eligible
    have active := UInt64.le_iff_toNat_le.mp atCap.active
    rw [far] at active
    have last : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    omega
  have small : index.toNat = position := by
    rw [← named]
    exact toNat_toUInt64_of_lt (updated.registryWithinLimit_of_lt notGloas)
      (Array.getElem?_eq_some_iff.mp located).1
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, set⟩ := ok
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  rw [other inside _ (small ▸ apart)]
  exact kept

/-- Before Electra, the slashings keep the balance of an unslashed validator. -/
private theorem slashings_atCap (before : fork < .pectra) {s t : BeaconState preset fork}
    (computed : processSlashings s = .ok t) {i : Nat} {validator : Validator}
    (found : s.validators.data[i]? = some validator) (unslashed : validator.slashed = false) :
    t.balances.data[i]? = s.balances.data[i]? := by
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  obtain ⟨_, _, _, _, each⟩ := processSlashings_balances_of_lt_electra before computed
  obtain ⟨other, otherFound, lowered⟩ := (each i).1 inside
  rw [found, Option.some.injEq] at otherFound
  subst otherFound
  rw [lowered]
  have notDue : ¬ SlashingPenaltyDue preset (getCurrentEpoch s) validator := by
    simp [SlashingPenaltyDue, unslashed]
  simp only [notDue, ↓reduceIte]
  cases s.balances.data[i]? <;> rfl

/-- Before Electra, the effective balance updates keep the record of a validator at the cap.

The balance must be at least the cap, and the cap a whole number of increments. -/
private theorem effective_atCap (before : fork < .pectra)
    (aligned : MaxEffectiveBalancesAligned preset)
    {s t : BeaconState preset fork} (computed : processEffectiveBalanceUpdates s = .ok t)
    {i : Nat} {validator : Validator} {balance : Gwei}
    (found : s.validators.data[i]? = some validator)
    (capped : validator.effectiveBalance = preset.MAX_EFFECTIVE_BALANCE)
    (held : s.balances.data[i]? = some balance)
    (high : preset.MAX_EFFECTIVE_BALANCE.toNat ≤ balance.toNat) :
    t.validators.data[i]? = some validator := by
  have notElectra : ¬ Fork.pectra ≤ fork := Nat.not_le_of_lt before
  obtain ⟨effectiveBalance, updated, scalar⟩ :=
    processEffectiveBalanceUpdates_effectiveBalance_eq computed found held
  simp only [withdrawalMaxEffectiveBalance, notElectra, ↓reduceIte, updatedEffectiveBalance,
    bind_ok_iff, pure, Except.pure, Except.ok.injEq] at scalar
  obtain ⟨_, _, _, _, leaves, _, rfl⟩ := scalar
  rw [updated]
  -- A balance at least the cap rounds down to at least the cap, since the cap is aligned.
  have whole :
      preset.MAX_EFFECTIVE_BALANCE.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
    have := congrArg UInt64.toNat aligned.1
    rwa [UInt64.toNat_mod] at this
  have below : balance % preset.EFFECTIVE_BALANCE_INCREMENT ≤ balance := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]
    exact Nat.mod_le _ _
  have rounded : preset.MAX_EFFECTIVE_BALANCE ≤
      balance - balance % preset.EFFECTIVE_BALANCE_INCREMENT := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ below, UInt64.toNat_mod]
    have split := Nat.mod_add_div balance.toNat preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    have cap := Nat.mod_add_div preset.MAX_EFFECTIVE_BALANCE.toNat
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    have more := Nat.mul_le_mul_left preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      (Nat.div_le_div_right (c := preset.EFFECTIVE_BALANCE_INCREMENT.toNat) high)
    omega
  have same : (if leaves = true then
      (balance - balance % preset.EFFECTIVE_BALANCE_INCREMENT) ⊓ preset.MAX_EFFECTIVE_BALANCE
      else validator.effectiveBalance) = validator.effectiveBalance := by
    split
    · rw [capped]
      apply UInt64.toNat_inj.mp
      rw [toNat_min]
      exact Nat.min_eq_right (UInt64.le_iff_toNat_le.mp rounded)
    · rfl
  rw [same]

/-- From Altair before Electra, a validator at the cap keeps its record before the sync update.

Every score must be at most a bound, and the balance at least the cap plus one penalty.

The penalty is at that bound plus the score bias.

The balance then loses at most that penalty.

The cap must be a whole number of increments, and above the ejection balance.

The inactivity penalty quotients of Altair and Bellatrix must be positive. -/
theorem run_readyStages_atCap (altair : .altair ≤ fork) (before : fork < .pectra)
    (aligned : MaxEffectiveBalancesAligned preset)
    (ejection : config.EJECTION_BALANCE < preset.MAX_EFFECTIVE_BALANCE)
    (quotients : 0 < min preset.INACTIVITY_PENALTY_QUOTIENT_ALTAIR.toNat
      preset.INACTIVITY_PENALTY_QUOTIENT_BELLATRIX.toNat)
    (computed : run (action config checks) readyStages state = .ok ready)
    {index : Nat} {validator : Validator} {balance : Gwei} {bound : Nat}
    (found : state.validators.data[index]? = some validator)
    (atCap : AtCap preset (getCurrentEpoch state) validator)
    (held : state.balances.data[index]? = some balance)
    (scored : ∀ score ∈ (state.inactivityScores altair).data, score.toNat ≤ bound)
    (funded : preset.MAX_EFFECTIVE_BALANCE.toNat +
      preset.capPenalty config (bound + config.INACTIVITY_SCORE_BIAS.toNat) ≤ balance.toNat) :
    ready.validators.data[index]? = some validator ∧
      ∃ left, ready.balances.data[index]? = some left ∧
        balance.toNat ≤
          left.toNat + preset.capPenalty config (bound + config.INACTIVITY_SCORE_BIAS.toNat) := by
  have notElectra : ¬ Fork.pectra ≤ fork := Nat.not_le_of_lt before
  have notGloas : ¬ Fork.glamsterdam ≤ fork := fun h => notElectra (Nat.le_trans (by decide) h)
  have trace := run_ok_iff.mp computed
  change EpochTrace _ [.justification, .inactivity, .rewards, .registry, .slashings, .eth1Reset,
    .pendingDeposits, .pendingConsolidations, .payments, .effectiveBalances, .slashingsReset,
    .randaoReset, .history, .participation] _ _ at trace
  cases trace; rename_i s1 e1 trace
  cases trace; rename_i s2 e2 trace
  cases trace; rename_i s3 e3 trace
  cases trace; rename_i s4 e4 trace
  cases trace; rename_i s5 e5 trace
  cases trace; rename_i s6 e6 trace
  cases trace; rename_i s7 e7 trace
  cases trace; rename_i s8 e8 trace
  cases trace; rename_i s9 e9 trace
  cases trace; rename_i s10 e10 trace
  cases trace; rename_i s11 e11 trace
  cases trace; rename_i s12 e12 trace
  cases trace; rename_i s13 e13 trace
  cases trace; rename_i e14 trace
  cases trace
  -- Justification and the scores keep the registry, the balances and the slot.
  have j1 := processJustificationAndFinalization_eq (action_cases.mp e1)
  have v1 : s1.validators = state.validators := by rw [j1]
  have b1 : s1.balances = state.balances := by rw [j1]
  have t1 : s1.slot = state.slot := by rw [j1]
  have scores1 : s1.inactivityScores = state.inactivityScores := by rw [j1]
  have i2 : processInactivityUpdates config s1 altair = .ok s2 := by
    simpa only [Edge, altair, ↓reduceDIte] using action_cases.mp e2
  have f2 := processInactivityUpdates_frame i2
  have v2 : s2.validators = s1.validators := by rw [f2]
  have b2 : s2.balances = s1.balances := by rw [f2]
  have t2 : s2.slot = s1.slot := by rw [f2]
  have scored2 := processInactivityUpdates_scoreBound i2 (by rw [scores1]; exact scored)
  -- The rewards take at most one penalty.
  have r3 : processRewardsAndPenalties config s2 = .ok s3 := action_cases.mp e3
  have f3 := processRewardsAndPenalties_frame r3
  have v3 : s3.validators = s2.validators := by rw [f3]
  have t3 : s3.slot = s2.slot := by rw [f3]
  have found2 : s2.validators.data[index]? = some validator := by rw [v2, v1]; exact found
  have held2 : s2.balances.data[index]? = some balance := by rw [b2, b1]; exact held
  obtain ⟨left, held3, lost⟩ :=
    rewards_atCap altair before quotients r3 found2 atCap.capped held2 scored2
  have found3 : s3.validators.data[index]? = some validator := by rw [v3]; exact found2
  -- The later stages keep the slot, so the epoch is below the last one.
  have r4 : processRegistryUpdates config s3 = .ok s4 := action_cases.mp e4
  obtain ⟨t4, b4, -⟩ := processRegistryUpdates_registryKept before r4
  have r5 : processSlashings s4 = .ok s5 := action_cases.mp e5
  have f5 := processSlashings_frame r5
  have v5 : s5.validators = s4.validators := by rw [f5]
  have t5 : s5.slot = s4.slot := by rw [f5]
  have same6 := same_action altair before (by simp) e6
  have same7 := same_action altair before (by simp) e7
  have same8 := same_action altair before (by simp) e8
  have same9 := same_action altair before (by simp) e9
  have r10 : processEffectiveBalanceUpdates s9 = .ok s10 := action_cases.mp e10
  have f10 := processEffectiveBalanceUpdates_frame r10
  have b10 : s10.balances = s9.balances := by rw [f10]
  have t10 : s10.slot = s9.slot := by rw [f10]
  obtain ⟨next, -, nextEq, -, -⟩ := processSlashingsReset_eq (action_cases.mp e11)
  have epoch3 : getCurrentEpoch s3 = getCurrentEpoch state := by
    unfold getCurrentEpoch
    rw [t3, t2, t1]
  have epoch10 : getCurrentEpoch s10 = getCurrentEpoch s3 := by
    unfold getCurrentEpoch
    rw [t10, same9.2.2, same8.2.2, same7.2.2, same6.2.2, t5, t4]
  have small : (getCurrentEpoch s3).toNat + 1 < 2 ^ 64 := by
    rw [← epoch10, ← nextEq]
    exact next.toNat_lt
  -- The registry, the slashings and the effective balances keep the validator.
  have found4 := registry_atCap before ejection r4 found3 (epoch3 ▸ atCap) small
  have held5 : s5.balances.data[index]? = some left := by
    rw [slashings_atCap before r5 found4 atCap.unslashed, b4]
    exact held3
  have found9 : s9.validators.data[index]? = some validator := by
    rw [same9.1, same8.1, same7.1, same6.1, v5]
    exact found4
  have held9 : s9.balances.data[index]? = some left := by
    rw [same9.2.1, same8.2.1, same7.2.1, same6.2.1]
    exact held5
  have high : preset.MAX_EFFECTIVE_BALANCE.toNat ≤ left.toNat := by omega
  have found10 := effective_atCap before aligned r10 found9 atCap.capped held9 high
  have same11 := same_action altair before (by simp) e11
  have same12 := same_action altair before (by simp) e12
  have same13 := same_action altair before (by simp) e13
  have same14 := same_action altair before (by simp) e14
  refine ⟨?_, left, ?_, lost⟩
  · rw [same14.1, same13.1, same12.1, same11.1]
    exact found10
  · rw [same14.2.1, same13.2.1, same12.2.1, same11.2.1, b10]
    exact held9

/-- From Altair before Electra, a validator at the cap keeps its record through the epoch.

Every score must be at most a bound, and the balance at least the cap plus one penalty.

The penalty is at that bound plus the score bias.

The balance then loses at most that penalty.

The cap must be a whole number of increments, and above the ejection balance.

The inactivity penalty quotients of Altair and Bellatrix must be positive. -/
theorem processEpoch_atCap (altair : .altair ≤ fork) (before : fork < .pectra)
    (aligned : MaxEffectiveBalancesAligned preset)
    (ejection : config.EJECTION_BALANCE < preset.MAX_EFFECTIVE_BALANCE)
    (quotients : 0 < min preset.INACTIVITY_PENALTY_QUOTIENT_ALTAIR.toNat
      preset.INACTIVITY_PENALTY_QUOTIENT_BELLATRIX.toNat)
    (computed : processEpoch config checks state = .ok after)
    {index : Nat} {validator : Validator} {balance : Gwei} {bound : Nat}
    (found : state.validators.data[index]? = some validator)
    (atCap : AtCap preset (getCurrentEpoch state) validator)
    (held : state.balances.data[index]? = some balance)
    (scored : ∀ score ∈ (state.inactivityScores altair).data, score.toNat ≤ bound)
    (funded : preset.MAX_EFFECTIVE_BALANCE.toNat +
      preset.capPenalty config (bound + config.INACTIVITY_SCORE_BIAS.toNat) ≤ balance.toNat) :
    after.validators.data[index]? = some validator ∧
      ∃ left, after.balances.data[index]? = some left ∧
        balance.toNat ≤
          left.toNat + preset.capPenalty config (bound + config.INACTIVITY_SCORE_BIAS.toNat) := by
  have whole : epochStages = readyStages ++ [.syncCommittees, .proposerLookahead, .ptcWindow] :=
    rfl
  rw [processEpoch_eq_run, whole] at computed
  obtain ⟨ready, head, tail⟩ := append_iff.mp (run_ok_iff.mp computed)
  obtain ⟨kept, left, held, lost⟩ := run_readyStages_atCap altair before aligned ejection
    quotients (run_ok_iff.mpr head) found atCap held scored funded
  -- The committee stages keep the registry and the balances.
  cases tail; rename_i synced e1 tail
  cases tail; rename_i moved e2 tail
  cases tail; rename_i e3 tail
  cases tail
  have same1 := same_action altair before (by simp) e1
  have same2 := same_action altair before (by simp) e2
  have same3 := same_action altair before (by simp) e3
  refine ⟨?_, left, ?_, lost⟩
  · rw [same3.1, same2.1, same1.1]
    exact kept
  · rw [same3.2.1, same2.2.1, same1.2.1]
    exact held

end EthLib.Consensus
