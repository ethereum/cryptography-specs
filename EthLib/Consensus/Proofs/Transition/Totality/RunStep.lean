module

public import EthLib.Consensus.Proofs.Transition.TargetPending
public import EthLib.Consensus.Proofs.Transition.Totality.Horizon
public import EthLib.Consensus.Proofs.Transition.Totality.Pending
public import EthLib.Consensus.Proofs.Transition.Totality.RunBounds
public import EthLib.Consensus.Proofs.Transition.Totality.RunHypotheses
public import EthLib.Consensus.Proofs.Transition.Totality.Shape

/-!
# Proofs: each epoch and each upgrade of a bounded run of slots succeeds

A run of slots keeps bounds whose parameters grow with each epoch.

Fixed conditions on the preset, the configuration and those parameters hold for the whole run.

Under them, each epoch and each upgrade succeeds.

The epoch transition succeeds at every fork, from a state within the bounds of its epoch count.

It also needs the draws at the cap and the signers of that epoch, which the run assumes.

Each upgrade succeeds too, under the draws of that upgrade.

The conditions are global: they read the start of the run and its last epoch, not each state.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}

/-- The conditions on a run of slots that make each of its epochs and upgrades succeed.

The run starts within some bounds, crosses at most some number of epochs, and ends by an epoch.

The budget bounds the sum of the effective balances at every epoch of the run.

The conditions on the preset and the configuration hold on mainnet. -/
structure RunConditions (preset : Preset) (config : Config) (start : RunStart)
    (budget epochs lastEpoch : Nat) : Prop where
  /-- The divisors of the preset are positive. -/
  positive : preset.DivisorsPositive
  /-- The divisors of the configuration are positive. -/
  configPositive : config.DivisorsPositive
  /-- The buffer of block roots reaches the epoch before, and an epoch has at least two slots. -/
  roots : preset.RootsReachPreviousEpoch
  /-- The hysteresis bands are below `2^63`. -/
  bands : preset.HysteresisBandsBelow
  /-- The downward hysteresis multiplier is below the quotient. -/
  hysteresis : preset.HYSTERESIS_DOWNWARD_MULTIPLIER.toNat < preset.HYSTERESIS_QUOTIENT.toNat
  /-- The products of each draw fit in 64 bits. -/
  draws : ∀ fork, DrawFits preset fork
  /-- The shortest seed lookahead is shorter than the history of mixes. -/
  lookahead : preset.MIN_SEED_LOOKAHEAD.toNat < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat
  /-- A sync committee has members. -/
  members : preset.SYNC_COMMITTEE_SIZE ≠ 0
  /-- The largest effective balances are whole numbers of increments. -/
  aligned : MaxEffectiveBalancesAligned preset
  /-- The least balance to activate is at most the cap of a compounding validator. -/
  compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA
  /-- The least churn is at least one increment. -/
  minimum : preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
  /-- The largest activation and exit churn is at least one increment. -/
  maximum :
    preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT
  /-- An epoch has at least six slots, which the payload committees need from Gloas. -/
  slots : 6 ≤ preset.SLOTS_PER_EPOCH.toNat
  /-- The budget covers one increment and the effective balances at the start. -/
  effectiveStart :
    max preset.EFFECTIVE_BALANCE_INCREMENT.toNat start.effective ≤ budget
  /-- The bound on the supply at the last epoch, in the ratio of the hysteresis, fits the budget. -/
  supplyRatio : (start.supply + epochs * preset.epochIssuanceBeforeAltair budget) *
      preset.HYSTERESIS_QUOTIENT.toNat ≤
    budget * (preset.HYSTERESIS_QUOTIENT.toNat - preset.HYSTERESIS_DOWNWARD_MULTIPLIER.toNat)
  /-- The supply at the last epoch plus the issuance of one more epoch is below `2^63`. -/
  supplyRoom : start.supply + epochs * preset.epochIssuanceBeforeAltair budget +
    preset.epochIssuance budget < 2 ^ 63
  /-- Three times one increment plus the budget fits in 64 bits. -/
  tripled : 3 * (preset.EFFECTIVE_BALANCE_INCREMENT.toNat + budget) < 2 ^ 64
  /-- Before Electra, the cap in increments, times the budget, fits in 64 bits. -/
  product :
    preset.MAX_EFFECTIVE_BALANCE.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * budget < 2 ^ 64
  /-- From Altair, the rewards fit for the budget, at the bound on the scores at the start. -/
  fit : RewardsFit preset config budget start.scores
  /-- The run crosses at most as many epochs as the horizon of its scores. -/
  horizon : epochs ≤ preset.horizon config start.scores
  /-- From Altair, the ceiling on the balances after the rewards is below `2^63`. -/
  half : preset.rewardsCeiling budget < 2 ^ 63
  /-- Before Altair, the rewards fit for the budget up to the epoch limit. -/
  fitBefore : RewardsFitBeforeAltair preset budget preset.epochLimitBeforeAltair
  /-- Before Altair, the ceiling on the balances after the rewards is below `2^63`. -/
  halfBefore : preset.rewardsCeilingBeforeAltair budget < 2 ^ 63
  /-- The exit ceiling at the start covers the first epoch, plus one and the longest seed lookahead.

  The first epoch of the run is the last epoch less the number of epochs. -/
  firstStart : lastEpoch - epochs + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ start.ceiling
  /-- The exit ceiling at the last epoch, plus one step, the delay and one, is below `2^64 - 1`. -/
  exitRoom : start.ceilingAt preset budget epochs + start.exitStep preset budget +
    config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat + 1 < 2 ^ 64 - 1
  /-- The carried exit churn plus three churns fits in 64 bits. -/
  churnRoom : max start.exitChurn (exitChurnBound preset config budget) +
    3 * exitChurnBound preset config budget < 2 ^ 64
  /-- The carried deposit churn at the last epoch plus one churn fits in 64 bits. -/
  depositRoom : start.depositChurn + (epochs + 1) * depositChurnBound config < 2 ^ 64
  /-- The slashed balances, times the multiplier of any fork, fit in 64 bits. -/
  slashed : ∀ fork,
    start.slashed * ((parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER.toNat + 1) < 2 ^ 64
  /-- The history has room for one entry in each epoch of the run.

  The bound is generous, since the history gains an entry only once per period of roots. -/
  history : start.history + epochs < preset.HISTORICAL_ROOTS_LIMIT.toNat
  /-- The registry load is within the registry limit, the deposit queue limit and `2^40`. -/
  load : start.load ≤ preset.VALIDATOR_REGISTRY_LIMIT.toNat ∧
    start.load ≤ preset.PENDING_DEPOSITS_LIMIT.toNat ∧ start.load ≤ 2 ^ 40
  /-- The draws of committees fit in 64 bits for the registry load. -/
  loadRoom : preset.SYNC_COMMITTEE_SIZE.toNat * start.load < 2 ^ 64 ∧
    preset.PTC_SIZE.toNat * start.load < 2 ^ 64 ∧
    start.load * (preset.MAX_COMMITTEES_PER_SLOT.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat <
      2 ^ 64
  /-- The slots up to the last epoch, with the lookahead and the buffer of roots, fit in 64 bits. -/
  slotRoom : (lastEpoch + preset.MIN_SEED_LOOKAHEAD.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat +
    preset.SLOTS_PER_HISTORICAL_ROOT.toNat < 2 ^ 64
  /-- The last epoch plus the lookahead and the buffers of mixes and slashings fits in 64 bits. -/
  epochRoom : lastEpoch + preset.MIN_SEED_LOOKAHEAD.toNat + 1 +
    preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat < 2 ^ 64

/-! ## The facts that the conditions and the bounds give on a state of the run -/

section Facts

variable {start : RunStart} {budget epochs lastEpoch elapsed : Nat}
  {state : BeaconState preset fork}

/-- The registry load is at most the bound on the load. -/
private theorem RunBounded.registryLoad_le (holds : RunBounded config start budget elapsed state) :
    registryLoad state ≤ start.load :=
  (Nat.le_mul_of_pos_left _ (one_le_registryLoadFactor fork)).trans holds.load

/-- The registry size is at most the bound on the load. -/
private theorem RunBounded.size_le (holds : RunBounded config start budget elapsed state) :
    state.validators.data.size ≤ start.load := by
  have := holds.registryLoad_le
  unfold registryLoad at this
  omega

/-- The bound on the supply at the last epoch is at most the budget. -/
private theorem RunConditions.supply_le_budget
    (conditions : RunConditions preset config start budget epochs lastEpoch) :
    start.supply + epochs * preset.epochIssuanceBeforeAltair budget ≤ budget := by
  have quotient : 0 < preset.HYSTERESIS_QUOTIENT.toNat := by
    have := conditions.hysteresis
    omega
  refine Nat.le_of_mul_le_mul_right ?_ quotient
  exact conditions.supplyRatio.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))

/-- The budget is below `2^63`. -/
private theorem RunConditions.budget_lt
    (conditions : RunConditions preset config start budget epochs lastEpoch) :
    budget < 2 ^ 63 :=
  Nat.lt_of_le_of_lt (Nat.le_add_right _ _) conditions.half

/-- Up to the last epoch, the balances plus the pending deposits are within the bound at its end. -/
private theorem RunBounded.supply_le_of_le (holds : RunBounded config start budget elapsed state)
    (le : elapsed ≤ epochs) : balanceSum state + pendingDepositSum state ≤
      start.supply + epochs * preset.epochIssuanceBeforeAltair budget :=
  holds.supply.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ le) _)

/-- Up to the last epoch, the sum of the effective balances is at most the budget. -/
private theorem RunBounded.effective_le (holds : RunBounded config start budget elapsed state)
    (conditions : RunConditions preset config start budget epochs lastEpoch)
    (le : elapsed ≤ epochs) : effectiveBalanceSum state ≤ budget := by
  rcases holds.effective with low | ratio
  · exact low.trans ((le_max_right _ _).trans conditions.effectiveStart)
  · have gap : 0 < preset.HYSTERESIS_QUOTIENT.toNat -
        preset.HYSTERESIS_DOWNWARD_MULTIPLIER.toNat := by
      have := conditions.hysteresis
      omega
    refine Nat.le_of_mul_le_mul_right ?_ gap
    refine ratio.trans (le_trans ?_ conditions.supplyRatio)
    exact Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.mul_le_mul_right _ le) _)

/-- Up to the last epoch, each balance is at most the budget. -/
private theorem RunBounded.funded (holds : RunBounded config start budget elapsed state)
    (conditions : RunConditions preset config start budget epochs lastEpoch)
    (le : elapsed ≤ epochs) : ∀ balance ∈ state.balances.data, balance.toNat ≤ budget := by
  intro balance member
  have single : balance.toNat ≤ balanceSum state :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _
      (List.mem_map.mpr ⟨balance, Array.mem_toList_iff.mpr member, rfl⟩)
  have := holds.supply_le_of_le le
  have := conditions.supply_le_budget
  omega

/-- Each effective balance of a shaped state is at most the largest cap. -/
private theorem Shaped.le_largest (shaped : Shaped state) :
    ∀ validator ∈ state.validators.data,
      validator.effectiveBalance.toNat ≤ preset.largestEffectiveBalance := fun validator member =>
  (UInt64.le_iff_toNat_le.mp (shaped.capped validator member)).trans
    (withdrawalMaxEffectiveBalance_le_largestEffectiveBalance preset fork validator)

/-- Before Electra, each effective balance of a shaped state is at most the cap of the draw. -/
private theorem Shaped.le_drawCap_of_lt_electra (shaped : Shaped state) (before : fork < .pectra) :
    ∀ validator ∈ state.validators.data,
      validator.effectiveBalance.toNat ≤ drawCap preset fork := by
  intro validator member
  have := UInt64.le_iff_toNat_le.mp (shaped.capped validator member)
  have electra : ¬ Fork.pectra ≤ fork := Nat.not_le_of_lt before
  simpa only [withdrawalMaxEffectiveBalance, drawCap, electra, ↓reduceIte] using this

/-- Before Electra, each effective balance in increments, times their sum, fits in 64 bits. -/
private theorem RunBounded.product (holds : RunBounded config start budget elapsed state)
    (conditions : RunConditions preset config start budget epochs lastEpoch)
    (shaped : Shaped state) (before : fork < .pectra) (le : elapsed ≤ epochs) :
    ∀ validator ∈ state.validators.data,
      (validator.effectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT).toNat *
        effectiveBalanceSum state < 2 ^ 64 := by
  intro validator member
  have capped := shaped.le_drawCap_of_lt_electra before validator member
  have electra : ¬ Fork.pectra ≤ fork := Nat.not_le_of_lt before
  simp only [drawCap, electra, ↓reduceIte] at capped
  rw [UInt64.toNat_div]
  refine Nat.lt_of_le_of_lt (Nat.mul_le_mul ?_ (holds.effective_le conditions le))
    conditions.product
  exact Nat.div_le_div_right capped

/-- The slashed balances fit, and so does their product with the multiplier of the fork. -/
private theorem RunBounded.slashed_fits (holds : RunBounded config start budget elapsed state)
    (conditions : RunConditions preset config start budget epochs lastEpoch) :
    slashedBalanceSum state < 2 ^ 64 ∧ slashedBalanceSum state *
      (parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER.toNat < 2 ^ 64 := by
  have room := conditions.slashed fork
  have product := Nat.mul_le_mul holds.slashed
    (Nat.le_add_right (parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER.toNat 1)
  have single : start.slashed ≤ start.slashed *
      ((parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER.toNat + 1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have := holds.slashed
  constructor <;> omega

/-- The exit ceiling one epoch on is at most the exit ceiling at the last epoch. -/
private theorem RunStart.ceilingAt_succ_le (start : RunStart) (le : elapsed < epochs) :
    start.ceilingAt preset budget elapsed + start.exitStep preset budget ≤
      start.ceilingAt preset budget epochs := by
  unfold RunStart.ceilingAt
  have := Nat.mul_le_mul_right (start.exitStep preset budget) (Nat.succ_le_of_lt le)
  rw [Nat.succ_mul] at this
  omega

/-- Within the horizon, the scores one epoch on still fit in 64 bits. -/
private theorem scores_lt_of_lt_horizon {scoreStart : Nat}
    (within : elapsed < preset.horizon config scoreStart) :
    scoreStart + config.INACTIVITY_SCORE_BIAS.toNat * elapsed +
      config.INACTIVITY_SCORE_BIAS.toNat < 2 ^ 64 := by
  unfold Preset.horizon at within
  have bias : 0 < config.INACTIVITY_SCORE_BIAS.toNat := by
    rcases Nat.eq_zero_or_pos config.INACTIVITY_SCORE_BIAS.toNat with zero | positive
    · rw [zero, Nat.div_zero] at within
      omega
    · exact positive
  have grown := (Nat.le_div_iff_mul_le bias).mp (Nat.succ_le_of_lt within)
  rw [Nat.succ_mul] at grown
  have := Nat.div_le_self (2 ^ 64 - 1) preset.largestEffectiveBalance
  rw [Nat.mul_comm] at grown
  omega

/-- A slot is before the first slot of the epoch after its own. -/
private theorem slot_lt_of_epoch (positive : preset.DivisorsPositive) :
    state.slot.toNat < ((getCurrentEpoch state).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat := by
  have spe : 0 < preset.SLOTS_PER_EPOCH.toNat := by
    have := positive.slotsPerEpoch
    have := UInt64.toNat_inj.not.mpr this
    simp only [UInt64.toNat_zero] at this
    omega
  rw [getCurrentEpoch_toNat, Nat.succ_mul]
  exact Nat.lt_div_mul_add spe

/-- From Electra, each effective balance of a shaped state is at most the cap of the draw.

The activation balance must be at most the cap of a compounding validator. -/
private theorem Shaped.le_drawCap_of_electra (shaped : Shaped state) (electra : .pectra ≤ fork)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA) :
    ∀ validator ∈ state.validators.data,
      validator.effectiveBalance.toNat ≤ drawCap preset fork := by
  intro validator member
  have := UInt64.le_iff_toNat_le.mp (shaped.capped validator member)
  have ordered := UInt64.le_iff_toNat_le.mp compounding
  simp only [withdrawalMaxEffectiveBalance, getMaxEffectiveBalance, electra, ↓reduceIte] at this
  simp only [drawCap, electra, ↓reduceIte]
  split at this <;> omega

/-- The increment is positive. -/
private theorem increment_pos (positive : preset.DivisorsPositive) :
    0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  have := UInt64.toNat_inj.not.mpr positive.increment
  simp only [UInt64.toNat_zero] at this
  omega

end Facts

/-- The epoch transition of a bounded run succeeds at every fork.

The state is at the end of an epoch of the run, some epochs after its start, before the last one.

It keeps the invariant of the state transition, the shape, and the facts on pending attestations.

The current epoch plus one plus the longest seed lookahead is at most the exit ceiling.

The signers of the epoch hold at most the active balance, and the draws meet a validator at the cap.

Before Altair, the epoch is within the epoch limit. -/
theorem processEpoch_exists_ok_of_run [NeZero preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat]
    [NeZero preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat]
    {start : RunStart} {budget epochs lastEpoch elapsed : Nat}
    {state : BeaconState preset fork}
    (conditions : RunConditions preset config start budget epochs lastEpoch)
    (holds : RunBounded config start budget elapsed state) (invariant : Invariant state)
    (shaped : Shaped state) (wellFormed : PendingWellFormed state)
    (resolved : PendingResolved state)
    (counted : elapsed < epochs)
    (ended : (getCurrentEpoch state).toNat < lastEpoch)
    (last : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0)
    (first : (getCurrentEpoch state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤
      start.ceilingAt preset budget elapsed)
    (signers : SignersWithinActive state) (draws : EpochDraws config checks state)
    (limit : fork < .altair → (getCurrentEpoch state).toNat ≤ preset.epochLimitBeforeAltair) :
    ∃ after, processEpoch config checks state = .ok after := by
  have le := Nat.le_of_lt counted
  have summedLe := holds.effective_le conditions le
  have budgetLt := conditions.budget_lt
  have funded := holds.funded conditions le
  obtain ⟨slashedFits, slashedProduct⟩ := holds.slashed_fits conditions
  have sizeLe := holds.size_le
  have load := conditions.load
  have tripled : 3 * (preset.EFFECTIVE_BALANCE_INCREMENT.toNat + effectiveBalanceSum state) <
      2 ^ 64 := by
    have := conditions.tripled
    omega
  have within : state.RegistryWithinLimit := sizeLe.trans load.1
  -- The slot and the epoch are before the end of the last epoch, so their sums fit.
  have slotLt := slot_lt_of_epoch (state := state) conditions.positive
  have slotRoomC := conditions.slotRoom
  have epochRoomC := conditions.epochRoom
  have slotMul : ((getCurrentEpoch state).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat ≤
      (lastEpoch + preset.MIN_SEED_LOOKAHEAD.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat :=
    Nat.mul_le_mul_right _ (by omega)
  have room : state.slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat < 2 ^ 64 := by omega
  have halfway : (getCurrentEpoch state).toNat + (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat <
      2 ^ 64 := by
    have : (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat ≤
        preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat := by
      rw [UInt64.toNat_div]
      exact Nat.div_le_self _ _
    omega
  -- The exit ceiling one epoch on is within the room at the last epoch.
  have stepLe := start.ceilingAt_succ_le (preset := preset) (budget := budget) counted
  have exitRoomC := conditions.exitRoom
  have stepSize : state.validators.data.size + 1 ≤ start.exitStep preset budget :=
    Nat.add_le_add_right (sizeLe.trans (Nat.le_add_left _ _)) 1
  have historyC := conditions.history
  have rootsLe := holds.roots
  by_cases altair : Fork.altair ≤ fork
  · -- From Altair, the rewards fit at the bound on the scores one epoch on.
    have short := Nat.lt_of_lt_of_le counted conditions.horizon
    have fitted := RewardsFit.of_lt_horizon conditions.fit conditions.fit.scorePenalty short
    have scoreRoom := scores_lt_of_lt_horizon short
    by_cases electra : Fork.pectra ≤ fork
    · have capella : Fork.shapella ≤ fork := Nat.le_trans (by decide) electra
      have incLe : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ budget :=
        (le_max_left _ _).trans conditions.effectiveStart
      -- The total active balance and the balance of each flag read, within the active balance.
      obtain ⟨total, active, _, totalLe⟩ := getTotalActiveBalance_exists_ok within (by omega)
      have totalBudget : total.toNat ≤ budget := by
        rcases totalLe with rfl | totalLe <;> omega
      choose indices listed inside using fun flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length =>
        getUnslashedParticipatingIndices_exists_ok within altair flagIndex.val.toUInt64
          (Or.inl rfl) shaped.participationMatches
      choose participatingBalance weighed _ using fun flagIndex =>
        getTotalBalance_exists_ok (inside flagIndex) (by omega)
      have supply : balanceSum state + pendingDepositSum state +
          preset.epochIssuance total.toNat < 2 ^ 63 := by
        have := holds.supply_le_of_le le
        have := preset.epochIssuance_mono totalBudget
        have := conditions.supplyRoom
        omega
      -- The exits not yet started cost at most one step of the ceiling.
      have costLe : exitCost preset state + 1 ≤ start.exitStep preset budget := by
        have := exitCost_le state
        have := Nat.div_le_div_right (c := preset.EFFECTIVE_BALANCE_INCREMENT.toNat) summedLe
        unfold RunStart.exitStep
        omega
      have exitCarried : (state.exitBalanceToConsume electra).toNat +
          3 * exitChurnCeiling config state < 2 ^ 64 := by
        have churnLe : exitChurnCeiling config state ≤ exitChurnBound preset config budget := by
          unfold exitChurnCeiling exitChurnBound
          omega
        have := holds.exitChurn electra
        have := conditions.churnRoom
        omega
      have depositCarried : (state.depositBalanceToConsume electra).toNat +
          depositChurnCap config fork < 2 ^ 64 := by
        have capLe : depositChurnCap config fork ≤ depositChurnBound config := by
          unfold depositChurnCap depositChurnBound
          split
          · exact le_max_left _ _
          · exact le_max_right _ _
        have grown := Nat.mul_le_mul_right (depositChurnBound config) (Nat.succ_le_of_lt counted)
        rw [Nat.succ_mul] at grown
        have := holds.depositChurn electra
        have depositRoom := conditions.depositRoom
        rw [Nat.succ_mul] at depositRoom
        omega
      have loadLe := holds.registryLoad_le
      have seedMul : ((getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 2) *
          preset.SLOTS_PER_EPOCH.toNat ≤
          (lastEpoch + preset.MIN_SEED_LOOKAHEAD.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat :=
        Nat.mul_le_mul_right _ (by omega)
      have loadRoom := conditions.loadRoom
      exact processEpoch_total_of_electra electra conditions.positive conditions.configPositive
        conditions.roots conditions.bands fitted conditions.half (conditions.draws fork)
        conditions.lookahead conditions.members last room (by omega) (by omega)
        (loadLe.trans load.1) shaped.balancesMatch shaped.participationMatches
        shaped.inactivityScoresMatch shaped.capped summedLe tripled funded (holds.scores _)
        scoreRoom active (fun flagIndex => ⟨indices flagIndex, listed flagIndex, weighed flagIndex⟩)
        (fun flagIndex => (signers total active).2 altair flagIndex _ _ (listed flagIndex)
          (weighed flagIndex))
        supply invariant.ordered invariant.settled
        (ceiling := start.ceilingAt preset budget elapsed + 1) (by omega) (holds.queue electra)
        (fun validator member set => (holds.exits validator member set).trans (Nat.le_succ _))
        (by omega) conditions.minimum conditions.maximum exitCarried depositCarried
        (shaped.inside electra) slashedFits slashedProduct halfway
        (by have := holds.summaries capella; omega) (fun _ => conditions.slots)
        conditions.compounding (loadLe.trans load.2.2)
        (Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ loadLe) loadRoom.1)
        (fun _ => ⟨Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ loadLe) loadRoom.2.1,
          Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ loadLe))
            loadRoom.2.2⟩)
        (draws.keys altair) (draws.sync altair) draws.proposers draws.ptc
    · -- Before Electra, the cap of the draw is the cap of every validator.
      have before : fork < .pectra := Nat.lt_of_not_le electra
      have drawCapped := shaped.le_drawCap_of_lt_electra before
      have product := holds.product conditions shaped before le
      have loadRoom := conditions.loadRoom
      exact processEpoch_total_of_altair_of_lt_electra altair before conditions.positive
        conditions.configPositive conditions.roots conditions.bands fitted conditions.half
        (conditions.draws fork) conditions.lookahead conditions.members last room (by omega)
        within shaped.balancesMatch shaped.participationMatches shaped.inactivityScoresMatch
        drawCapped summedLe tripled funded (holds.scores altair) scoreRoom invariant.ordered
        invariant.settled (ceiling := start.ceilingAt preset budget elapsed) first holds.exits
        (by omega) slashedFits slashedProduct halfway product (fun _ => by omega)
        (fun capella => by have := holds.summaries capella; omega) (draws.keys altair)
        (fun _ => sizeLe.trans load.2.2)
        (fun _ => Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ sizeLe) loadRoom.1)
        (draws.sync altair)
  · have before : fork < .altair := Nat.lt_of_not_le altair
    have product := holds.product conditions shaped (Nat.lt_trans before (by decide)) le
    exact processEpoch_total_of_lt_altair (epochBound := preset.epochLimitBeforeAltair)
      (ceiling := start.ceilingAt preset budget elapsed) before conditions.positive
      conditions.roots conditions.bands conditions.fitBefore conditions.halfBefore last room
      (limit before) within shaped.balancesMatch shaped.le_largest summedLe tripled funded
      invariant.ordered invariant.settled resolved wellFormed first holds.exits (by omega)
      slashedFits slashedProduct halfway product (by omega)

/-- The epoch transition of a bounded run keeps its bounds, one epoch further on.

The conditions are those under which the epoch succeeds. -/
theorem RunBounded.of_processEpoch_of_run {start : RunStart}
    {budget epochs lastEpoch elapsed : Nat} {state after : BeaconState preset fork}
    (conditions : RunConditions preset config start budget epochs lastEpoch)
    (holds : RunBounded config start budget elapsed state) (invariant : Invariant state)
    (shaped : Shaped state) (resolved : PendingResolved state)
    (counted : elapsed < epochs)
    (first : (getCurrentEpoch state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤
      start.ceilingAt preset budget elapsed)
    (signers : SignersWithinActive state)
    (computed : processEpoch config checks state = .ok after) :
    RunBounded config start budget (elapsed + 1) after := by
  have summedLe := holds.effective_le conditions (Nat.le_of_lt counted)
  have budgetLt := conditions.budget_lt
  have stepLe := start.ceilingAt_succ_le (preset := preset) (budget := budget) counted
  have exitRoom := conditions.exitRoom
  exact holds.of_processEpoch invariant conditions.aligned
    (holds.size_le.trans conditions.load.1) (increment_pos conditions.positive)
    conditions.fit.perIncrement (by omega)
    (max_le ((le_max_left _ _).trans conditions.effectiveStart) summedLe)
    shaped.participationMatches resolved signers first conditions.minimum conditions.maximum
    (by omega) conditions.churnRoom computed

/-- Before Altair, the flags of each pending attestation of the previous epoch are computed.

Each must target the previous epoch, have its slot in it, and have the previous justified source.

The state must be past its first epoch.

Its slot plus the length of the buffer of block roots must fit in 64 bits.

An epoch must have two slots at least, and the buffer of block roots must reach the epoch before.

The parent slot can be any slot. -/
theorem getAttestationParticipationFlagIndices_exists_ok_of_voted
    {votes : Set (ValidatorIndex × AttestationData)} {state : BeaconState preset fork}
    (before : fork < .altair) (roots : preset.RootsReachPreviousEpoch)
    (voted : PendingVoted votes state) (started : 0 < (getCurrentEpoch state).toNat)
    (room : state.slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat < 2 ^ 64)
    {attestation : PendingAttestation preset}
    (member : attestation ∈ (state.previousEpochAttestations before).data) (parentSlot : Slot) :
    ∃ flags, getAttestationParticipationFlagIndices state attestation.data
      attestation.inclusionDelay parentSlot = .ok flags := by
  obtain ⟨target, slotEpoch, source, -⟩ := voted before false attestation member
  simp only [Bool.false_eq_true, ↓reduceIte] at target source
  have twoSlots := roots.twoSlots
  have reach := roots.reach
  have current := getCurrentEpoch_toNat state
  have previous := getPreviousEpoch_toNat state
  have slotEpochNat : attestation.data.slot.toNat / preset.SLOTS_PER_EPOCH.toNat =
      (getCurrentEpoch state).toNat - 1 := by
    rw [← previous, ← target, ← slotEpoch]
    simp [computeEpochAtSlot, UInt64.toNat_div]
  have targetNat : attestation.data.target.epoch.toNat = (getCurrentEpoch state).toNat - 1 := by
    rw [target, previous]
  -- The slot of the state is in the current epoch, and the attestation slot in the previous one.
  have stateSplit := Nat.div_add_mod state.slot.toNat preset.SLOTS_PER_EPOCH.toNat
  have stateMod := Nat.mod_lt state.slot.toNat (by omega : 0 < preset.SLOTS_PER_EPOCH.toNat)
  have slotSplit := Nat.div_add_mod attestation.data.slot.toNat preset.SLOTS_PER_EPOCH.toNat
  have slotMod := Nat.mod_lt attestation.data.slot.toNat
    (by omega : 0 < preset.SLOTS_PER_EPOCH.toNat)
  rw [← current] at stateSplit
  rw [slotEpochNat] at slotSplit
  have back : preset.SLOTS_PER_EPOCH.toNat * (getCurrentEpoch state).toNat =
      preset.SLOTS_PER_EPOCH.toNat * ((getCurrentEpoch state).toNat - 1) +
        preset.SLOTS_PER_EPOCH.toNat := by
    rw [Nat.mul_sub, Nat.mul_one]
    have := Nat.le_mul_of_pos_right preset.SLOTS_PER_EPOCH.toNat started
    omega
  have epochStart : attestation.data.target.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat =
      preset.SLOTS_PER_EPOCH.toNat * ((getCurrentEpoch state).toNat - 1) := by
    rw [targetNat, Nat.mul_comm]
  obtain ⟨targetRoot, targetOk⟩ := getBlockRoot_exists (state := state)
    (epoch := attestation.data.target.epoch) (by omega) (by omega) (by omega)
  obtain ⟨slotRoot, slotOk⟩ := getBlockRootAtSlot_exists (state := state)
    (slot := attestation.data.slot) (by omega) (by omega) (by omega) (by omega)
  have older : attestation.data.target.epoch ≠ getCurrentEpoch state := fun same => by
    rw [same] at targetNat
    omega
  have notGloas : ¬ Fork.glamsterdam ≤ fork := fun gloas =>
    absurd (Nat.lt_of_le_of_lt gloas before) (by decide)
  unfold getAttestationParticipationFlagIndices
  simp only [targetOk, slotOk, older, ↓reduceIte, source, notGloas, ↓reduceDIte]
  exact ⟨_, rfl⟩

/-- The upgrade from the fork of a bounded state to the next fork succeeds.

The upgrade must be due, so the fork has a next fork.

The state keeps the shape and, before Altair, the pending attestations resolve.

Before Altair, each pending attestation must have the target, slot and source its block checked.

Before Altair, the slot of the state must not be zero.

Its epoch is at most the last one, and the draws of the upgrade meet a validator at the cap. -/
theorem UpgradeReady.of_run {start : RunStart} {budget epochs lastEpoch elapsed : Nat}
    {forked : ForkedBeaconState preset}
    (conditions : RunConditions preset config start budget epochs lastEpoch)
    (holds : RunBounded config start budget elapsed forked.state)
    (shaped : Shaped forked.state) (resolved : PendingResolved forked.state)
    (counted : elapsed ≤ epochs)
    (ended : (getCurrentEpoch forked.state).toNat ≤ lastEpoch)
    (draws : UpgradeDraws forked) (due : upgradeDue config forked = true)
    {votes : Set (ValidatorIndex × AttestationData)} (voted : PendingVoted votes forked.state)
    (started : forked.fork < .altair → forked.state.slot ≠ 0) :
    UpgradeReady forked := by
  have summedLe := holds.effective_le conditions counted
  have budgetLt := conditions.budget_lt
  have sizeLe := holds.size_le
  have load := conditions.load
  have loadRoom := conditions.loadRoom
  have epochRoomC := conditions.epochRoom
  have slotRoomC := conditions.slotRoom
  have slotMul : ((getCurrentEpoch forked.state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1) *
      preset.SLOTS_PER_EPOCH.toNat ≤
      (lastEpoch + preset.MIN_SEED_LOOKAHEAD.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat :=
    Nat.mul_le_mul_right _ (by omega)
  -- The exit ceiling at the last epoch is past the last epoch and the longest lookahead.
  have maxRoom : (getCurrentEpoch forked.state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat + 1 <
      2 ^ 64 := by
    have first := conditions.firstStart
    have exitRoom := conditions.exitRoom
    have step : 1 ≤ start.exitStep preset budget := Nat.le_add_left _ _
    have grown : start.ceiling + epochs ≤ start.ceilingAt preset budget epochs := by
      unfold RunStart.ceilingAt
      have := Nat.le_mul_of_pos_right epochs step
      omega
    omega
  have supplyLe := holds.supply_le_of_le counted
  have supplyBudget := conditions.supply_le_budget
  obtain ⟨fork, pre⟩ := forked
  dsimp only at *
  cases fork with
  | phase0 =>
    obtain ⟨keys, validator, member, active, atCap⟩ := draws
    refine ⟨conditions.draws .altair, by omega, conditions.lookahead, conditions.members,
      ⟨keys, shaped.le_drawCap_of_lt_electra (by decide), ⟨validator, member, active, atCap⟩,
        sizeLe.trans load.2.2, Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ sizeLe) loadRoom.1⟩,
      fun attestation member => ?_⟩
    have listed := Array.mem_toList_iff.mp member
    have twoSlots := conditions.roots.twoSlots
    have current := getCurrentEpoch_toNat pre
    have split := Nat.div_add_mod pre.slot.toNat preset.SLOTS_PER_EPOCH.toNat
    have below := Nat.mod_lt pre.slot.toNat (by omega : 0 < preset.SLOTS_PER_EPOCH.toNat)
    rw [← current] at split
    -- The slot is in the current epoch, so it lies below the end of the lookahead.
    have within : preset.SLOTS_PER_EPOCH.toNat * ((getCurrentEpoch pre).toNat + 1) ≤
        ((getCurrentEpoch pre).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1) *
          preset.SLOTS_PER_EPOCH.toNat := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_right _ (by omega)
    rw [Nat.mul_add, Nat.mul_one] at within
    -- The upgrade is due at the first slot of an epoch, and that slot is not zero.
    have first : pre.slot.toNat % preset.SLOTS_PER_EPOCH.toNat = 0 := by
      simp only [upgradeDue, Bool.and_eq_true, beq_iff_eq] at due
      have := congrArg UInt64.toNat due.1
      simpa [UInt64.toNat_mod] using this
    have nonzero : pre.slot.toNat ≠ 0 := fun zero =>
      started (by decide) (UInt64.toNat_inj.mp (by simpa))
    have positive : 0 < (getCurrentEpoch pre).toNat := by
      rcases Nat.eq_zero_or_pos (getCurrentEpoch pre).toNat with zero | pos
      · rw [zero, Nat.mul_zero] at split
        omega
      · exact pos
    exact ⟨getAttestationParticipationFlagIndices_exists_ok_of_voted (by decide) conditions.roots
      voted positive (by omega) listed _, resolved (by decide) attestation (.inl listed)⟩
  | altair => trivial
  | bellatrix => trivial
  | shapella => trivial
  | dencun =>
    -- Before Electra the load counts the registry twice.
    have doubled : 2 * registryLoad pre ≤ start.load := holds.load
    have := holds.size_le
    unfold registryLoad at doubled
    exact ⟨shaped.balancesMatch, by omega, maxRoom, by omega⟩
  | pectra =>
    refine ⟨conditions.draws .fusaka, by omega, conditions.lookahead, by omega,
      fun offset within => ⟨shaped.le_drawCap_of_electra (by decide) conditions.compounding,
        ?_, sizeLe.trans load.2.2⟩⟩
    obtain ⟨validator, member, active, atCap⟩ := draws offset within
    exact ⟨validator, member, active, fun gloas => absurd gloas (by decide), atCap⟩
  | fusaka =>
    have pending : pendingDepositSum pre =
        pendingAmount (pre.pendingDeposits (by decide)).data.toList := by
      simp only [pendingDepositSum, (by decide : Fork.pectra ≤ .fusaka), ↓reduceDIte]
    refine ⟨conditions.draws .glamsterdam, by omega, conditions.lookahead, by omega,
      conditions.positive.slotsPerEpoch,
      fun offset within => ⟨shaped.le_drawCap_of_electra (by decide) conditions.compounding,
        draws offset within, sizeLe.trans load.2.2,
        Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ sizeLe) loadRoom.2.1,
        Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ sizeLe))
          loadRoom.2.2⟩, by omega⟩
  | glamsterdam => exact draws
  | _ => simp [upgradeDue, Config.nextFork] at due

/-- On mainnet the conditions hold for a supply of 36 million ETH and a budget of `2^57` Gwei.

The run crosses `2.25 * 10^6` epochs, from epoch `4 * 10^5`. -/
theorem runConditions_mainnet :
    RunConditions Preset.mainnet Config.mainnet
      { supply := 36 * 10 ^ 15, effective := 36 * 10 ^ 15, load := 2 ^ 22, scores := 0,
        ceiling := 400005, history := 2 ^ 20, depositChurn := 0, exitChurn := 0, slashed := 0 }
      (2 ^ 57) 2250000 2650000 := by
  have root : Nat.sqrt (2 ^ 57) = 379625062 := (Nat.eq_sqrt.mpr ⟨by decide, by decide⟩).symm
  have fitBefore := rewardsFitBeforeAltair_mainnet
  exact {
    positive := Preset.divisorsPositive_mainnet
    configPositive := Config.divisorsPositive_mainnet
    roots := Preset.rootsReachPreviousEpoch_mainnet
    bands := Preset.hysteresisBandsBelow_mainnet
    hysteresis := by decide
    draws := fun fork => (drawFits_presets fork).1
    lookahead := seedLookahead_lt_presets.1
    members := syncCommitteeSize_ne_zero_presets.1
    aligned := maxEffectiveBalancesAligned_mainnet
    compounding := by decide
    minimum := by decide
    maximum := by decide
    slots := by decide
    effectiveStart := by decide
    supplyRatio := by
      simp only [Preset.epochIssuanceBeforeAltair, root]
      decide
    supplyRoom := by
      simp only [Preset.epochIssuanceBeforeAltair, Preset.epochIssuance, root]
      decide
    tripled := by decide
    product := by decide
    fit := rewardsFit_mainnet.of_scoreBound (by decide)
    horizon := Preset.horizon_mainnet
    half := rewardsCeiling_mainnet
    fitBefore := ⟨fitBefore.product, fitBefore.rewards,
      Preset.penalties_lt_of_le_epochLimitBeforeAltair le_rfl
        (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) fitBefore.penalties)⟩
    halfBefore := rewardsCeilingBeforeAltair_mainnet
    firstStart := by decide
    exitRoom := by decide
    churnRoom := by decide
    depositRoom := by decide
    slashed := fun _ => by simp
    history := by decide
    load := by decide
    loadRoom := by decide
    slotRoom := by decide
    epochRoom := by decide }

end EthLib.Consensus
