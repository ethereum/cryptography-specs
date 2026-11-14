module

public import EthLib.Consensus.Proofs.Transition.Totality.AtCap
public import EthLib.Consensus.Proofs.Transition.Totality.RunHypotheses
import EthLib.Consensus.Proofs.Transition.Totality.EpochBounds

/-!
# Proofs: a run from Altair before Electra meets its hypotheses

A run of slots from Altair applies no block, so a quiet state stays quiet.

The signers then hold at most the total active balance.

A validator at the cap with a large balance keeps its record while the leak drains it.

So it meets every draw of a sync committee, as long as its balance stays above the cap.

Before Electra the keys never change, and the upgrades on the way draw nothing.

The bound for runs before Altair holds trivially, since the run starts at Altair.
-/

@[expose] public section

namespace EthLib.Consensus

open Base EpochStage EpochTrace

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- From Altair, the most that a number of epochs take from a validator at the cap.

The scores start at most at a bound, and rise by at most the bias in each epoch.

So epoch `k` of the run, counted from one, reads scores at most the bound plus `k` times the bias.
-/
def Preset.capDrain (preset : Preset) (config : Config) (scoreStart : Nat) : Nat → Nat
  | 0 => 0
  | epochs + 1 => preset.capDrain config scoreStart epochs +
      preset.capPenalty config (scoreStart + config.INACTIVITY_SCORE_BIAS.toNat * (epochs + 1))

/-- The drain of a number of epochs is at most its terms summed before rounding down.

The flags cost one base reward in each epoch.

The scores sum to the epochs times the start, plus the bias times 1 + 2 + ... + the epochs. -/
theorem Preset.capDrain_le (preset : Preset) (config : Config) (scoreStart epochs : Nat) :
    preset.capDrain config scoreStart epochs ≤
      epochs * (preset.MAX_EFFECTIVE_BALANCE.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        (preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat.sqrt)) +
      preset.MAX_EFFECTIVE_BALANCE.toNat * (epochs * scoreStart +
          config.INACTIVITY_SCORE_BIAS.toNat * (epochs * (epochs + 1) / 2)) /
        (config.INACTIVITY_SCORE_BIAS.toNat *
          min preset.INACTIVITY_PENALTY_QUOTIENT_ALTAIR.toNat
            preset.INACTIVITY_PENALTY_QUOTIENT_BELLATRIX.toNat) := by
  induction epochs with
  | zero => simp [Preset.capDrain]
  | succ epochs previous =>
    simp only [Preset.capDrain, Preset.capPenalty]
    generalize config.INACTIVITY_SCORE_BIAS.toNat *
      min preset.INACTIVITY_PENALTY_QUOTIENT_ALTAIR.toNat
        preset.INACTIVITY_PENALTY_QUOTIENT_BELLATRIX.toNat = divisor at previous ⊢
    -- The sum of the steps up to one more is the old sum plus that step.
    have steps :
        (epochs + 1) * (epochs + 1 + 1) / 2 = epochs * (epochs + 1) / 2 + (epochs + 1) := by
      have double :
          (epochs + 1) * (epochs + 1 + 1) = epochs * (epochs + 1) + (epochs + 1) * 2 := by
        rw [Nat.mul_comm, Nat.succ_mul, Nat.succ_mul]
        omega
      rw [double, Nat.add_mul_div_right _ _ (by omega)]
    have split : preset.MAX_EFFECTIVE_BALANCE.toNat * (epochs * scoreStart +
          config.INACTIVITY_SCORE_BIAS.toNat * (epochs * (epochs + 1) / 2)) / divisor +
        preset.MAX_EFFECTIVE_BALANCE.toNat *
          (scoreStart + config.INACTIVITY_SCORE_BIAS.toNat * (epochs + 1)) / divisor ≤
        (preset.MAX_EFFECTIVE_BALANCE.toNat * (epochs * scoreStart +
          config.INACTIVITY_SCORE_BIAS.toNat * (epochs * (epochs + 1) / 2)) +
        preset.MAX_EFFECTIVE_BALANCE.toNat *
          (scoreStart + config.INACTIVITY_SCORE_BIAS.toNat * (epochs + 1))) / divisor :=
      Nat.div_add_div_le_add_div
    rw [← Nat.mul_add] at split
    have regroup : (epochs + 1) * scoreStart + config.INACTIVITY_SCORE_BIAS.toNat *
        (epochs * (epochs + 1) / 2 + (epochs + 1)) = epochs * scoreStart +
          config.INACTIVITY_SCORE_BIAS.toNat * (epochs * (epochs + 1) / 2) +
          (scoreStart + config.INACTIVITY_SCORE_BIAS.toNat * (epochs + 1)) := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
      omega
    rw [steps, regroup, Nat.succ_mul]
    omega

/-! ## The facts that a run from Altair keeps -/

/-- The drain grows with the number of epochs. -/
theorem Preset.capDrain_mono (preset : Preset) (config : Config) (scoreStart : Nat)
    {fewer more : Nat} (le : fewer ≤ more) :
    preset.capDrain config scoreStart fewer ≤ preset.capDrain config scoreStart more := by
  induction more with
  | zero => rw [Nat.le_zero.mp le]
  | succ more previous =>
    rcases Nat.lt_or_eq_of_le le with lt | rfl
    · exact (previous (by omega)).trans (Nat.le_add_right _ _)
    · exact Nat.le_refl _

/-- A balance funded for more epochs pays the penalty of the next epoch above the cap. -/
private theorem funded_next {scoreStart epochs total balance left : Nat}
    (more : epochs + 1 ≤ total)
    (funded : preset.MAX_EFFECTIVE_BALANCE.toNat + preset.capDrain config scoreStart total ≤
      balance)
    (held : balance ≤ left + preset.capDrain config scoreStart epochs) :
    preset.MAX_EFFECTIVE_BALANCE.toNat + preset.capPenalty config
        (scoreStart + config.INACTIVITY_SCORE_BIAS.toNat * epochs +
          config.INACTIVITY_SCORE_BIAS.toNat) ≤ left := by
  have grown := preset.capDrain_mono config scoreStart more
  simp only [Preset.capDrain, Nat.mul_succ, ← Nat.add_assoc] at grown
  omega

/-- A slot whose successor starts an epoch moves to the next epoch, within the run. -/
private theorem crossing {slot limit epochLength : Nat} (within : slot + 1 ≤ limit)
    (last : (slot + 1) % epochLength = 0) :
    (slot + 1) / epochLength = slot / epochLength + 1 ∧
      (slot + 1) / epochLength ≤ limit / epochLength := by
  rcases Nat.eq_zero_or_pos epochLength with zero | _
  · rw [zero, Nat.mod_zero] at last
    omega
  · exact ⟨Nat.succ_div_of_dvd (Nat.dvd_of_mod_eq_zero last), Nat.div_le_div_right within⟩

/-- Every key of the registry passes validation. -/
private def KeysValid {fork : Fork} (state : BeaconState preset fork) : Prop :=
  ∀ validator ∈ state.validators.data,
    ∃ point, Cryptography.Bls.G1.keyValidatePoint (packBytes validator.pubkey) = .ok point

/-- A state with the same keys keeps their validity. -/
private theorem KeysValid.of_keys {fork fork' : Fork} {state : BeaconState preset fork}
    {after : BeaconState preset fork'} (same : validatorKeys after = validatorKeys state)
    (valid : KeysValid state) : KeysValid after := by
  intro validator member
  have key : validator.pubkey ∈ validatorKeys after :=
    List.mem_map_of_mem (Array.mem_toList_iff.mpr member)
  rw [same] at key
  obtain ⟨other, otherMember, otherKey⟩ := List.mem_map.mp key
  rw [← otherKey]
  exact valid other (Array.mem_toList_iff.mp otherMember)

/-- A validator at the cap from an epoch stays so from any later epoch. -/
private theorem AtCap.mono {epoch later : Epoch} {validator : Validator}
    (atCap : AtCap preset epoch validator) (le : epoch.toNat ≤ later.toNat) :
    AtCap preset later validator :=
  ⟨atCap.unslashed, atCap.queued,
    UInt64.le_iff_toNat_le.mpr (Nat.le_trans (UInt64.le_iff_toNat_le.mp atCap.active) le),
    atCap.staying, atCap.capped⟩

/-- From Altair before Electra, an upgrade due before the Electra fork epoch carries the state.

It keeps the slot, the registry, the balances and the inactivity scores. -/
private theorem upgradeNext_early {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (altair : .altair ≤ pre.fork) (before : pre.fork < .pectra)
    (early : pre.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat <
      config.ELECTRA_FORK_EPOCH.toNat)
    (due : upgradeDue config pre = true)
    (computed : upgradeNext config checks pre = .ok post) :
    ∃ altair' : .altair ≤ post.val.fork, post.val.fork < .pectra ∧
      post.val.state.slot = pre.state.slot ∧
      post.val.state.validators.data = pre.state.validators.data ∧
      post.val.state.balances.data = pre.state.balances.data ∧
      (post.val.state.inactivityScores altair').data =
        (pre.state.inactivityScores altair).data := by
  obtain ⟨fork, state⟩ := pre
  cases fork
  case altair | bellatrix | shapella =>
    simp only [upgradeNext, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨by dsimp only; decide, by dsimp only; decide, rfl, rfl, rfl, rfl⟩
  case dencun =>
    -- The upgrade to Electra is due only at its fork epoch, which the run does not reach.
    exfalso
    simp only [upgradeDue, Config.nextFork, Option.any_some, Bool.and_eq_true,
      beq_iff_eq] at due
    have epoch : (computeEpochAtSlot preset state.slot).toNat =
        state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
      simp [computeEpochAtSlot, UInt64.toNat_div]
    rw [due.2] at epoch
    dsimp only at early
    omega
  all_goals dsimp only at altair before
  all_goals first
    | exact absurd altair (by decide)
    | exact absurd before (by decide)
    | (simp only [upgradeNext] at computed; cases computed)

/-- From Altair before Electra, the upgrades due before the Electra fork epoch carry the state.

They keep the slot, the registry, the balances and the inactivity scores. -/
private theorem processUpgrades_early {forked after : ForkedBeaconState preset}
    (altair : .altair ≤ forked.fork) (before : forked.fork < .pectra)
    (early : forked.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat <
      config.ELECTRA_FORK_EPOCH.toNat)
    (computed : processUpgrades config checks forked = .ok after) :
    ∃ altair' : .altair ≤ after.fork, after.fork < .pectra ∧
      after.state.slot = forked.state.slot ∧
      after.state.validators.data = forked.state.validators.data ∧
      after.state.balances.data = forked.state.balances.data ∧
      (after.state.inactivityScores altair').data = (forked.state.inactivityScores altair).data :=
  processUpgrades_induction_due (property := fun reached =>
      ∃ altair' : .altair ≤ reached.fork, reached.fork < .pectra ∧
        reached.state.slot = forked.state.slot ∧
        reached.state.validators.data = forked.state.validators.data ∧
        reached.state.balances.data = forked.state.balances.data ∧
        (reached.state.inactivityScores altair').data =
          (forked.state.inactivityScores altair).data)
    (fun due ⟨stepAltair, stepBefore, slot, validators, balances, scores⟩ stepOk => by
      obtain ⟨nextAltair, nextBefore, nextSlot, nextValidators, nextBalances, nextScores⟩ :=
        upgradeNext_early stepAltair stepBefore (by rw [slot]; exact early) due stepOk
      exact ⟨nextAltair, nextBefore, nextSlot.trans slot, nextValidators.trans validators,
        nextBalances.trans balances, nextScores.trans scores⟩)
    ⟨altair, before, rfl, rfl, rfl, rfl⟩ computed

/-- From Altair before Electra, the upgrades before the Electra fork epoch stay before Electra.

So each state they pass through draws nothing. -/
private theorem UpgradesPass.early {forked reached : ForkedBeaconState preset}
    (passes : UpgradesPass config checks forked reached)
    (altair : .altair ≤ forked.fork) (before : forked.fork < .pectra)
    (early : forked.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat <
      config.ELECTRA_FORK_EPOCH.toNat) :
    UpgradeDraws reached := by
  induction passes with
  | refl forked =>
    obtain ⟨fork, state⟩ := forked
    dsimp only at altair before
    cases fork <;> first
      | exact absurd altair (by decide)
      | exact absurd before (by decide)
      | exact True.intro
  | step due computed _ rest =>
    obtain ⟨nextAltair, nextBefore, nextSlot, -⟩ :=
      upgradeNext_early altair before early due computed
    exact rest nextAltair nextBefore (by rw [nextSlot]; exact early)

/-- The facts that a run from Altair keeps, for one validator at the cap.

The epochs count from an origin, and the drain and the scores grow with them. -/
private structure Tracked (config : Config) (origin index : Nat) (validator : Validator)
    (balance : Gwei) (scoreStart : Nat) (reached : ForkedBeaconState preset) : Prop where
  /-- The fork is at least Altair. -/
  altair : .altair ≤ reached.fork
  /-- The fork is before Electra. -/
  before : reached.fork < .pectra
  /-- No validator has signed. -/
  quiet : Quiet reached.state
  /-- Every key passes validation. -/
  keys : KeysValid reached.state
  /-- The validator keeps its record. -/
  found : reached.state.validators.data[index]? = some validator
  /-- The validator is at the cap from the current epoch. -/
  atCap : AtCap preset (getCurrentEpoch reached.state) validator
  /-- The current epoch is at least the origin. -/
  later : origin ≤ (getCurrentEpoch reached.state).toNat
  /-- The balance lost at most the drain of the epochs since the origin. -/
  held : ∃ left, reached.state.balances.data[index]? = some left ∧
    balance.toNat ≤ left.toNat + preset.capDrain config scoreStart
      ((getCurrentEpoch reached.state).toNat - origin)
  /-- Every score rose by at most the bias in each epoch since the origin. -/
  scored : ∀ score ∈ (reached.state.inactivityScores altair).data, score.toNat ≤
    scoreStart + config.INACTIVITY_SCORE_BIAS.toNat *
      ((getCurrentEpoch reached.state).toNat - origin)

/-- One slot keeps the tracked facts, within a run funded up to a last slot. -/
private theorem Tracked.of_advanceSlot {fork : Fork} {state advanced : BeaconState preset fork}
    {origin index : Nat} {validator : Validator} {balance : Gwei} {scoreStart limit : Nat}
    (aligned : MaxEffectiveBalancesAligned preset)
    (ejection : config.EJECTION_BALANCE < preset.MAX_EFFECTIVE_BALANCE)
    (quotients : 0 < min preset.INACTIVITY_PENALTY_QUOTIENT_ALTAIR.toNat
      preset.INACTIVITY_PENALTY_QUOTIENT_BELLATRIX.toNat)
    (funded : preset.MAX_EFFECTIVE_BALANCE.toNat + preset.capDrain config scoreStart
      (limit / preset.SLOTS_PER_EPOCH.toNat - origin) ≤ balance.toNat)
    (within : state.slot.toNat + 1 ≤ limit)
    (holds : Tracked config origin index validator balance scoreStart ⟨fork, state⟩)
    (computed : advanceSlot config checks state = .ok advanced) :
    Tracked config origin index validator balance scoreStart ⟨fork, advanced⟩ := by
  have quiet := holds.quiet.of_advanceSlot computed
  have epochNow := getCurrentEpoch_toNat state
  have epochNext := getCurrentEpoch_toNat advanced
  rw [advanceSlot_slot computed] at epochNext
  obtain ⟨altair, before, -, keys, found, atCap, later, held, scored⟩ := holds
  dsimp only at altair before keys found atCap later held scored
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, advancedEq⟩ := advanceSlot_ok computed
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
  have validators : advanced.validators = epoched.validators := by rw [advancedEq]
  have balances : advanced.balances = epoched.balances := by rw [advancedEq]
  have scores : ∀ altair, (advanced.inactivityScores altair).data =
      (epoched.inactivityScores altair).data := by
    subst advancedEq
    exact fun _ => rfl
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i last
    -- The slot ends its epoch, so the epoch transition runs and the epoch moves on by one.
    have lastNat : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 := by
      have := congrArg UInt64.toNat last
      simpa [UInt64.toNat_mod, sum] using this
    obtain ⟨succ, bounded⟩ := crossing within lastNat
    obtain ⟨left, leftHeld, leftBound⟩ := held
    have fundedStep := funded_next (preset := preset) (config := config)
      (total := limit / preset.SLOTS_PER_EPOCH.toNat - origin) (by omega) funded leftBound
    obtain ⟨found', after, afterHeld, drop⟩ := processEpoch_atCap altair before
      aligned ejection quotients epochedOk found atCap leftHeld scored fundedStep
    have keysEpoched : KeysValid epoched :=
      KeysValid.of_keys (processEpoch_validatorKeys before epochedOk) keys
    have moved : (getCurrentEpoch advanced).toNat - origin =
        (getCurrentEpoch state).toNat - origin + 1 := by
      omega
    refine ⟨altair, before, quiet, ?_, ?_, atCap.mono (by dsimp only; omega),
      by dsimp only; omega, ⟨after, ?_, ?_⟩, ?_⟩ <;> dsimp only
    · rw [KeysValid, validators]
      exact keysEpoched
    · rw [validators]
      exact found'
    · rw [balances]
      exact afterHeld
    · rw [moved]
      simp only [Preset.capDrain, Nat.mul_succ, ← Nat.add_assoc]
      omega
    · intro score member
      rw [moved, Nat.mul_succ, ← Nat.add_assoc]
      have bound := processEpoch_scoreBound altair (by exact scored) epochedOk
      rw [scores altair] at member
      exact bound score member
  · rename_i inside
    -- The slot stays inside its epoch, so the state keeps its epoch.
    simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    have kept := nextSlot_epoch_of_inside sum inside
    rw [sum] at kept
    have same : getCurrentEpoch advanced = getCurrentEpoch state :=
      UInt64.toNat_inj.mp (epochNext.trans (kept.trans epochNow.symm))
    refine ⟨altair, before, quiet, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;> try rw [same]
    · rw [KeysValid, validators]
      exact keys
    · rw [validators]
      exact found
    · exact atCap
    · exact later
    · rw [balances]
      exact held
    · intro score member
      rw [scores] at member
      exact scored score member

/-- One slot across fork boundaries keeps the tracked facts, before the Electra fork epoch. -/
private theorem Tracked.of_advanceSlotAcross {reached next : ForkedBeaconState preset}
    {origin index : Nat} {validator : Validator} {balance : Gwei} {scoreStart limit : Nat}
    (aligned : MaxEffectiveBalancesAligned preset)
    (ejection : config.EJECTION_BALANCE < preset.MAX_EFFECTIVE_BALANCE)
    (quotients : 0 < min preset.INACTIVITY_PENALTY_QUOTIENT_ALTAIR.toNat
      preset.INACTIVITY_PENALTY_QUOTIENT_BELLATRIX.toNat)
    (funded : preset.MAX_EFFECTIVE_BALANCE.toNat + preset.capDrain config scoreStart
      (limit / preset.SLOTS_PER_EPOCH.toNat - origin) ≤ balance.toNat)
    (electra : limit / preset.SLOTS_PER_EPOCH.toNat < config.ELECTRA_FORK_EPOCH.toNat)
    (within : reached.state.slot.toNat + 1 ≤ limit)
    (holds : Tracked config origin index validator balance scoreStart reached)
    (computed : advanceSlotAcross config checks reached = .ok next) :
    Tracked config origin index validator balance scoreStart next ∧
      next.state.slot.toNat = reached.state.slot.toNat + 1 := by
  obtain ⟨fork, state⟩ := reached
  obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
  have slot := advanceSlot_slot advancedOk
  obtain ⟨altair, before, quiet, keys, found, atCap, later, held, scored⟩ :=
    Tracked.of_advanceSlot aligned ejection quotients funded within holds advancedOk
  dsimp only at altair before quiet keys found atCap later held scored within slot
  -- The upgrades on the way stay before Electra, and carry the state.
  obtain ⟨altair', before', slotEq, validators, balances, scores⟩ :=
    processUpgrades_early altair before
      (Nat.lt_of_le_of_lt (Nat.div_le_div_right (by dsimp only; omega)) electra) upgraded
  dsimp only at slotEq validators balances scores
  have same : getCurrentEpoch next.state = getCurrentEpoch advanced := by
    unfold getCurrentEpoch
    rw [slotEq]
  refine ⟨⟨altair', before', Quiet.of_processUpgrades quiet upgraded, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_⟩
  · intro member contained
    rw [validators] at contained
    exact keys member contained
  · rw [validators]
    exact found
  · rw [same]
    exact atCap
  · rw [same]
    exact later
  · rw [balances, same]
    exact held
  · intro score member
    rw [scores] at member
    rw [same]
    exact scored score member
  · rw [slotEq]
    exact slot

/-- A run of slots keeps the tracked facts, before the Electra fork epoch. -/
private theorem Tracked.of_advanceSlotsAcross {origin index : Nat} {validator : Validator}
    {balance : Gwei} {scoreStart limit : Nat}
    (aligned : MaxEffectiveBalancesAligned preset)
    (ejection : config.EJECTION_BALANCE < preset.MAX_EFFECTIVE_BALANCE)
    (quotients : 0 < min preset.INACTIVITY_PENALTY_QUOTIENT_ALTAIR.toNat
      preset.INACTIVITY_PENALTY_QUOTIENT_BELLATRIX.toNat)
    (funded : preset.MAX_EFFECTIVE_BALANCE.toNat + preset.capDrain config scoreStart
      (limit / preset.SLOTS_PER_EPOCH.toNat - origin) ≤ balance.toNat)
    (electra : limit / preset.SLOTS_PER_EPOCH.toNat < config.ELECTRA_FORK_EPOCH.toNat) :
    ∀ (steps : Nat) {start reached : ForkedBeaconState preset},
      Tracked config origin index validator balance scoreStart start →
      start.state.slot.toNat + steps ≤ limit →
      advanceSlotsAcross config checks steps start = .ok reached →
      Tracked config origin index validator balance scoreStart reached ∧
        reached.state.slot.toNat = start.state.slot.toNat + steps
  | 0, start, reached, holds, _, computed => by
    simp only [advanceSlotsAcross, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨holds, rfl⟩
  | steps + 1, start, reached, holds, within, computed => by
    simp only [advanceSlotsAcross, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    obtain ⟨nextHolds, nextSlot⟩ := Tracked.of_advanceSlotAcross aligned ejection quotients
      funded electra (by omega) holds nextOk
    obtain ⟨reachedHolds, reachedSlot⟩ := Tracked.of_advanceSlotsAcross aligned ejection
      quotients funded electra steps nextHolds (by omega) rest
    exact ⟨reachedHolds, by omega⟩

/-- A run from Altair that ends before Electra meets its three hypotheses.

The state is quiet, and every key of its registry passes validation.

One validator is at the cap, and every inactivity score is at most a bound.

Its balance is at least the cap plus the drain of the epochs that the run crosses.

The caps before and from Electra and the activation balance are whole numbers of increments.

The cap is above the ejection balance.

The inactivity penalty quotients of Altair and Bellatrix are positive. -/
theorem runHypotheses_of_quiet_altair {forked : ForkedBeaconState preset} {count : Nat}
    (altair : .altair ≤ forked.fork) (before : forked.fork < .pectra)
    (aligned : MaxEffectiveBalancesAligned preset)
    (ejection : config.EJECTION_BALANCE < preset.MAX_EFFECTIVE_BALANCE)
    (quotients : 0 < min preset.INACTIVITY_PENALTY_QUOTIENT_ALTAIR.toNat
      preset.INACTIVITY_PENALTY_QUOTIENT_BELLATRIX.toNat)
    (quiet : Quiet forked.state)
    (keys : ∀ validator ∈ forked.state.validators.data,
      ∃ point, Cryptography.Bls.G1.keyValidatePoint (packBytes validator.pubkey) = .ok point)
    {index : Nat} {validator : Validator} {balance : Gwei} {scoreStart : Nat}
    (found : forked.state.validators.data[index]? = some validator)
    (atCap : AtCap preset (getCurrentEpoch forked.state) validator)
    (held : forked.state.balances.data[index]? = some balance)
    (scored : ∀ score ∈ (forked.state.inactivityScores altair).data, score.toNat ≤ scoreStart)
    (beforeElectra : (forked.state.slot.toNat + count) / preset.SLOTS_PER_EPOCH.toNat <
      config.ELECTRA_FORK_EPOCH.toNat)
    (funded : preset.MAX_EFFECTIVE_BALANCE.toNat + preset.capDrain config scoreStart
      ((forked.state.slot.toNat + count) / preset.SLOTS_PER_EPOCH.toNat -
        (getCurrentEpoch forked.state).toNat) ≤ balance.toNat) :
    SignersEarly config checks forked count ∧ DrawsAtCap config checks forked count ∧
      EpochLimitBeforeAltair forked count := by
  -- The tracked facts hold at the start, with no epoch passed.
  have start : Tracked config (getCurrentEpoch forked.state).toNat index validator balance
      scoreStart forked :=
    ⟨altair, before, quiet, keys, found, atCap, Nat.le_refl _,
      ⟨balance, held, by rw [Nat.sub_self]; exact Nat.le_add_right _ _⟩,
      by rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero]; exact scored⟩
  have run : ∀ steps < count, ∀ reached,
      advanceSlotsAcross config checks steps forked = .ok reached →
      Tracked config (getCurrentEpoch forked.state).toNat index validator balance scoreStart
        reached ∧ reached.state.slot.toNat = forked.state.slot.toNat + steps :=
    fun steps short _ computed => Tracked.of_advanceSlotsAcross aligned ejection quotients
      funded beforeElectra steps start (by omega) computed
  refine ⟨?_, ?_, fun early => absurd (Nat.lt_of_le_of_lt altair early) (by decide)⟩
  · intro steps short reached computed _ _ cached cachedOk
    obtain ⟨holds, -⟩ := run steps short reached computed
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact holds.quiet.signers
  · intro steps short reached computed
    obtain ⟨holds, slot⟩ := run steps short reached computed
    refine ⟨fun last cached cachedOk => ?_, fun advanced advancedOk upgrading passes _ =>
      passes.early holds.altair holds.before (Nat.lt_of_le_of_lt (Nat.div_le_div_right
        (by dsimp only; rw [advanceSlot_slot advancedOk]; omega)) beforeElectra)⟩
    -- The caching of the slot keeps the registry, the balances, the scores and the slot.
    obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
    have validators : cached.validators = reached.state.validators := by rw [cachedEq]
    have balances : cached.balances = reached.state.balances := by rw [cachedEq]
    have scores : ∀ altair, (cached.inactivityScores altair).data =
        (reached.state.inactivityScores altair).data := by
      subst cachedEq
      exact fun _ => rfl
    have epoch : getCurrentEpoch cached = getCurrentEpoch reached.state := by
      rw [cachedEq]
      rfl
    -- The slot ends its epoch, and the next epoch is within the run.
    obtain ⟨succ, bounded⟩ := crossing (limit := forked.state.slot.toNat + count)
      (by omega) last
    have epochNow := getCurrentEpoch_toNat reached.state
    have later := holds.later
    have bound := UInt64.toNat_lt config.ELECTRA_FORK_EPOCH
    obtain ⟨left, leftHeld, leftBound⟩ := holds.held
    have fundedStep := funded_next (preset := preset) (config := config)
      (total := (forked.state.slot.toNat + count) / preset.SLOTS_PER_EPOCH.toNat -
        (getCurrentEpoch forked.state).toNat) (by omega) funded leftBound
    refine ⟨fun _ _ ready readyOk => ?_, fun _ _ ready readyOk => ?_,
      fun fulu => absurd (Nat.lt_of_le_of_lt fulu holds.before) (by decide),
      fun gloas => absurd (Nat.lt_of_le_of_lt gloas holds.before) (by decide)⟩
    · refine KeysValid.of_keys (run_readyStages_validatorKeys holds.before readyOk) ?_
      intro member contained
      rw [validators] at contained
      exact holds.keys member contained
    · obtain ⟨readyFound, -⟩ := run_readyStages_atCap holds.altair holds.before aligned
        ejection quotients readyOk (by rw [validators]; exact holds.found)
        (by rw [epoch]; exact holds.atCap) (by rw [balances]; exact leftHeld)
        (fun score member => holds.scored score (by rw [← scores]; exact member)) fundedStep
      refine ⟨validator, Array.mem_of_getElem? readyFound, ?_, ?_⟩
      · -- The next epoch is after the activation and before the far future epoch.
        have next : (getCurrentEpoch reached.state + 1).toNat =
            (getCurrentEpoch reached.state).toNat + 1 := by
          rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt]
          omega
        have active := UInt64.le_iff_toNat_le.mp holds.atCap.active
        simp only [isActiveValidator, holds.atCap.staying, Bool.and_eq_true, decide_eq_true_eq,
          UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, epoch, next]
        refine ⟨by omega, ?_⟩
        rw [show FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 from rfl]
        omega
      · rw [holds.atCap.capped]
        simp only [drawCap, show ¬Fork.pectra ≤ reached.fork from Nat.not_le_of_lt holds.before,
          ↓reduceIte]

end EthLib.Consensus
