module

public import EthLib.Consensus.Proofs.Transition.Totality.EpochBounds
public import EthLib.Consensus.Proofs.Transition.Totality.EpochExits
public import EthLib.Consensus.Proofs.Transition.Totality.RegistryLoadChain
public import EthLib.Consensus.Proofs.Transition.Totality.Signers

/-!
# Proofs: the bounds of a run of slots, with parameters that grow per epoch

A run of slots needs bounds on each state it reaches, so that each epoch succeeds.

Fixed bounds cannot hold, since the rewards, the scores and the exit queue grow in each epoch.

So the bounds start from given values, and each epoch raises some of them by a fixed step.

One epoch keeps these bounds, one epoch further on, under conditions on the state before it.

A slot keeps them unchanged, since none of them reads the slot or the roots it caches.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {state after : BeaconState preset fork}

/-- The bounds at the start of a run of slots. -/
structure RunStart where
  /-- A bound on the balances plus the pending deposits. -/
  supply : Nat
  /-- A bound on the sum of the effective balances. -/
  effective : Nat
  /-- A bound on the registry load, counted twice before Electra. -/
  load : Nat
  /-- A bound on the inactivity scores. -/
  scores : Nat
  /-- A bound on the end of the exit queue and on each exit epoch that is set. -/
  ceiling : Nat
  /-- A bound on the number of historical roots, and of historical summaries. -/
  history : Nat
  /-- A bound on the deposit churn carried to the next epoch. -/
  depositChurn : Nat
  /-- A bound on the exit churn carried to the next epoch. -/
  exitChurn : Nat
  /-- A bound on the sum of the slashed balances. -/
  slashed : Nat

/-- The rise of the exit ceiling in one epoch.

It bounds the cost of the exits not yet started, plus one epoch.

That cost is at most the budget in increments plus the registry load.

Before Electra the rise is at most the registry size, which the load bounds too. -/
def RunStart.exitStep (preset : Preset) (start : RunStart) (budget : Nat) : Nat :=
  budget / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + start.load + 1

/-- The exit ceiling after some epochs of the run. -/
def RunStart.ceilingAt (preset : Preset) (start : RunStart) (budget elapsed : Nat) : Nat :=
  start.ceiling + elapsed * start.exitStep preset budget

/-- A bound on one exit churn, for a sum of the effective balances at most the budget. -/
def exitChurnBound (preset : Preset) (config : Config) (budget : Nat) : Nat :=
  config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat + budget + preset.EFFECTIVE_BALANCE_INCREMENT.toNat

/-- A bound on one deposit churn, at every fork. -/
def depositChurnBound (config : Config) : Nat :=
  max config.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS.toNat
    config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat

/-- The bounds that a state of a run keeps, some epochs after its start.

Most bounds start from given values and rise by a fixed step in each epoch.

The budget bounds the sum of the effective balances, and sets the issuance of an epoch. -/
structure RunBounded (config : Config) (start : RunStart) (budget elapsed : Nat)
    (state : BeaconState preset fork) : Prop where
  /-- The balances plus the pending deposits grow by at most the issuance of each epoch. -/
  supply : balanceSum state + pendingDepositSum state ≤
    start.supply + elapsed * preset.epochIssuanceBeforeAltair budget
  /-- The effective balances stay within their start or a fixed ratio of the bound on the supply.

  The ratio comes from the hysteresis constants, and it is 4/3 on mainnet.

  The bound says nothing when the downward multiplier is at least the quotient.

  An epoch sets them within that ratio of the balances, and a slot does not change them.

  It reads the bound on the supply, not the supply.

  The upgrade to Gloas can lower the supply. -/
  effective : effectiveBalanceSum state ≤ start.effective ∨
    effectiveBalanceSum state *
        (preset.HYSTERESIS_QUOTIENT.toNat - preset.HYSTERESIS_DOWNWARD_MULTIPLIER.toNat) ≤
      (start.supply + elapsed * preset.epochIssuanceBeforeAltair budget) *
        preset.HYSTERESIS_QUOTIENT.toNat
  /-- The registry load, counted twice before Electra, does not grow. -/
  load : registryLoadFactor fork * registryLoad state ≤ start.load
  /-- Each inactivity score grows by at most the score bias in each epoch. -/
  scores : ∀ altair : .altair ≤ fork, ∀ score ∈ (state.inactivityScores altair).data,
    score.toNat ≤ start.scores + config.INACTIVITY_SCORE_BIAS.toNat * elapsed
  /-- Each exit epoch that is set is at most the exit ceiling. -/
  exits : ∀ validator ∈ state.validators.data, validator.exitEpoch ≠ FAR_FUTURE_EPOCH →
    validator.exitEpoch.toNat ≤ start.ceilingAt preset budget elapsed
  /-- From Electra, the end of the exit queue is at most one past the exit ceiling. -/
  queue : ∀ electra : .pectra ≤ fork,
    (state.earliestExitEpoch electra).toNat ≤ start.ceilingAt preset budget elapsed + 1
  /-- The historical roots gain at most one entry in each epoch, and none from Capella. -/
  roots : state.historicalRoots.data.size ≤ start.history + elapsed
  /-- From Capella, the historical summaries gain at most one entry in each epoch. -/
  summaries : ∀ capella : .shapella ≤ fork,
    (state.historicalSummaries capella).data.size ≤ start.history + elapsed
  /-- From Electra, the carried deposit churn grows by at most one churn in each epoch. -/
  depositChurn : ∀ electra : .pectra ≤ fork,
    (state.depositBalanceToConsume electra).toNat ≤
      start.depositChurn + elapsed * depositChurnBound config
  /-- From Electra, the carried exit churn is at most the larger of its start and one churn. -/
  exitChurn : ∀ electra : .pectra ≤ fork,
    (state.exitBalanceToConsume electra).toNat ≤
      max start.exitChurn (exitChurnBound preset config budget)
  /-- The sum of the slashed balances does not grow. -/
  slashed : slashedBalanceSum state ≤ start.slashed

/-- The caching of a slot keeps the bounds of a run, with no more epochs. -/
theorem RunBounded.of_processSlot {config : Config} {start : RunStart} {budget elapsed : Nat}
    (holds : RunBounded config start budget elapsed state)
    (computed : processSlot state = .ok after) : RunBounded config start budget elapsed after := by
  -- The caching writes only the roots, the header and the availability bits.
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok computed
  exact ⟨holds.supply, holds.effective, holds.load, holds.scores, holds.exits, holds.queue,
    holds.roots, holds.summaries, holds.depositChurn, holds.exitChurn, holds.slashed⟩

/-- A new slot number keeps the bounds of a run, since none of them reads the slot. -/
theorem RunBounded.withSlot {config : Config} {start : RunStart} {budget elapsed : Nat}
    (holds : RunBounded config start budget elapsed state) (slot : Slot) :
    RunBounded config start budget elapsed { state with slot := slot } := by
  exact ⟨holds.supply, holds.effective, holds.load, holds.scores, holds.exits, holds.queue,
    holds.roots, holds.summaries, holds.depositChurn, holds.exitChurn, holds.slashed⟩

/-- One epoch keeps the bounds of a run, one epoch further on.

The state before it must keep the invariant of the state transition.

The largest effective balances of the preset must be whole numbers of increments.

The conditions of the bound on the supply must hold on that state.

The budget must cover one increment and the sum of the effective balances.

The signers of the previous epoch must hold at most the total active balance.

No theorem derives that condition, which a run takes as an assumption.

The current epoch plus one plus the seed lookahead must be at most the exit ceiling.

The least churn and the largest activation and exit churn must each be at least one increment.

The exit ceiling plus its step and the withdrawal delay must be below `2^64 - 1`.

The bound on the carried exit churn plus three exit churns must be below `2^64`. -/
theorem RunBounded.of_processEpoch {config : Config} {checks : SignatureChecks}
    {start : RunStart} {budget elapsed : Nat}
    (holds : RunBounded config start budget elapsed state)
    (invariant : Invariant state) (aligned : MaxEffectiveBalancesAligned preset)
    (within : state.RegistryWithinLimit)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (perIncrement :
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat < 2 ^ 64)
    (summed : effectiveBalanceSum state < 2 ^ 64)
    (budgeted : max preset.EFFECTIVE_BALANCE_INCREMENT.toNat (effectiveBalanceSum state) ≤ budget)
    (sized : ParticipationMatches state) (resolved : PendingResolved state)
    (signers : SignersWithinActive state)
    (first : (getCurrentEpoch state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤
      start.ceilingAt preset budget elapsed)
    (minimum : preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA)
    (maximum :
      preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT)
    (exitRoom : start.ceilingAt preset budget elapsed + start.exitStep preset budget +
      config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat < 2 ^ 64 - 1)
    (churnRoom : max start.exitChurn (exitChurnBound preset config budget) +
      3 * exitChurnBound preset config budget < 2 ^ 64)
    (computed : processEpoch config checks state = .ok after) :
    RunBounded config start budget (elapsed + 1) after := by
  have loadLe := processEpoch_registryLoad_le computed
  have effectiveLe := processEpoch_effectiveBalanceSum_le invariant aligned computed
  have supplyLe := processEpoch_supply_le_of_signers within increment perIncrement summed budgeted
    sized resolved signers computed
  have rootsLe := processEpoch_historicalRoots_size_le computed
  have slashedLe := processEpoch_slashedBalanceSum_le computed
  -- The weight of the registry load is at least one, so the registry size is within the bound.
  have sizeLe : state.validators.data.size ≤ start.load :=
    (Nat.le_add_right _ _).trans
      ((Nat.le_mul_of_pos_left _ (one_le_registryLoadFactor fork)).trans holds.load)
  have budgetLe : effectiveBalanceSum state ≤ budget := (le_max_right _ _).trans budgeted
  -- The supply grows by at most the issuance of the budget.
  have supplyAfter : balanceSum after + pendingDepositSum after ≤
      start.supply + (elapsed + 1) * preset.epochIssuanceBeforeAltair budget := by
    have := holds.supply
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have ceilingStep : start.ceilingAt preset budget (elapsed + 1) =
      start.ceilingAt preset budget elapsed + start.exitStep preset budget := by
    simp only [RunStart.ceilingAt, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
  have exitStepLe : state.validators.data.size + 1 ≤ start.exitStep preset budget := by
    exact Nat.add_le_add_right (sizeLe.trans (Nat.le_add_left _ _)) 1
  -- The exits of the epoch: from Electra through the exit queue, before it through the registry.
  have exits : (∀ electra : .pectra ≤ fork, ExitsAtMost electra
        (start.ceilingAt preset budget (elapsed + 1) + 1) after ∧
        (after.exitBalanceToConsume electra).toNat ≤
          max start.exitChurn (exitChurnBound preset config budget)) ∧
      ∀ validator ∈ after.validators.data, validator.exitEpoch ≠ FAR_FUTURE_EPOCH →
        validator.exitEpoch.toNat ≤ start.ceilingAt preset budget (elapsed + 1) := by
    by_cases electra : Fork.pectra ≤ fork
    · -- The cost of the exits is at most the budget in increments plus the registry load.
      have costLe : exitCost preset state + 1 ≤ start.exitStep preset budget :=
        calc exitCost preset state + 1
            ≤ effectiveBalanceSum state / preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
                state.validators.data.size + 1 := Nat.add_le_add_right (exitCost_le state) 1
          _ ≤ start.exitStep preset budget := by
            have := Nat.div_le_div_right (c := preset.EFFECTIVE_BALANCE_INCREMENT.toNat) budgetLe
            unfold RunStart.exitStep
            omega
      have churnLe : exitChurnCeiling config state ≤ exitChurnBound preset config budget := by
        unfold exitChurnCeiling exitChurnBound
        omega
      have carriedLe := holds.exitChurn electra
      obtain ⟨bounded, churned⟩ := processEpoch_exits_of_electra electra computed within summed
        increment minimum maximum (ceiling := start.ceilingAt preset budget elapsed + 1)
        (by omega)
        ⟨holds.queue electra, fun validator member set => (holds.exits validator member set).trans
          (Nat.le_succ _)⟩ (by omega) (by omega)
      -- The queue may sit one past the ceiling, which the slack of one epoch in the step absorbs.
      have narrowed := bounded.mono (high := start.ceilingAt preset budget (elapsed + 1))
        (by omega)
      refine ⟨fun _ => ⟨narrowed.mono (Nat.le_succ _), ?_⟩, narrowed.2⟩
      exact churned.trans (max_le carriedLe (churnLe.trans (le_max_right _ _)))
    · have widened := processEpoch_exits_of_lt_electra (Nat.lt_of_not_le electra) computed first
        holds.exits (by omega)
      exact ⟨fun electra' => absurd electra' electra, fun validator member set =>
        (widened validator member set).trans (by omega)⟩
  refine ⟨?_, ?_, ?_, ?_, exits.2, fun electra => (exits.1 electra).1.1, ?_, ?_, ?_,
    fun electra => (exits.1 electra).2, slashedLe.trans holds.slashed⟩
  · exact supplyAfter
  · -- The effective balances follow the balances, which the bound on the supply covers.
    exact .inr (effectiveLe.trans (Nat.mul_le_mul_right _
      ((Nat.le_add_right _ _).trans supplyAfter)))
  · exact (Nat.mul_le_mul_left _ loadLe).trans holds.load
  · intro altair score member
    have := processEpoch_scoreBound altair (holds.scores altair) computed score member
    rw [Nat.mul_add, Nat.mul_one]
    omega
  · have := holds.roots
    omega
  · intro capella
    have := processEpoch_historicalSummaries_size_le capella computed
    have := holds.summaries capella
    omega
  · -- The cap of each fork is one of the two churns that the bound takes the larger of.
    intro electra
    have capLe : depositChurnCap config fork ≤ depositChurnBound config := by
      unfold depositChurnCap depositChurnBound
      split
      · exact le_max_left _ _
      · exact le_max_right _ _
    have := processEpoch_depositBalanceToConsume_le electra computed
    have := holds.depositChurn electra
    rw [Nat.add_mul, Nat.one_mul]
    omega

end EthLib.Consensus
