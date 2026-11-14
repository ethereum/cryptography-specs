module

public import EthLib.Consensus.Proofs.Transition.TargetUpgrades
public import EthLib.Consensus.Proofs.Transition.Totality.RunStep
public import EthLib.Consensus.Proofs.Transition.Totality.RunUpgrades
public import EthLib.Consensus.Proofs.Transition.Totality.Slot

/-!
# Proofs: every slot advance within the horizon succeeds on a bounded state

A run of slots advances a state one slot at a time, with the upgrades due on the way.

Each state that it reaches keeps the invariant, the shape of the state and the bounds of the run.

So every slot advance within the horizon succeeds, under three hypotheses on the states reached.

From Electra, a run of empty slots leaks.

The hypothesis on the draws then fails within about `7.7 * 10^5` epochs.

On mainnet the bounds alone hold for `2.25 * 10^6` epochs, about 27 years.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The facts that each state of a bounded run of slots keeps.

The run starts at a given epoch, and the bounds count the epochs since then.

Before Altair, the pending attestations are as block processing stored and checked them. -/
structure RunHolds (config : Config) (start : RunStart) (budget startEpoch : Nat) {fork : Fork}
    (state : BeaconState preset fork) : Prop where
  /-- The state is at the first epoch of the run or later. -/
  started : startEpoch ≤ (getCurrentEpoch state).toNat
  /-- The state keeps the invariant of the state transition. -/
  invariant : Invariant state
  /-- The state keeps its shape. -/
  shaped : Shaped state
  /-- Each pending attestation has its slot in its epoch, a nonzero delay, and a known proposer. -/
  wellFormed : PendingWellFormed state
  /-- The committee and the signers of each pending attestation succeed. -/
  resolved : PendingResolved state
  /-- In the first two epochs of the chain, the two justified checkpoints are equal. -/
  early : JustifiedEarly state
  /-- Each pending attestation has the target and the source that its block checked. -/
  voted : PendingVoted Set.univ state
  /-- The bounds of the run hold, after as many epochs as the state is past the first one. -/
  bounded : RunBounded config start budget ((getCurrentEpoch state).toNat - startEpoch) state
  /-- From the second epoch of the run, no one has signed in the current epoch. -/
  quietCurrent : startEpoch < (getCurrentEpoch state).toNat → QuietCurrent state
  /-- From the third epoch of the run, no one has signed. -/
  quiet : startEpoch + 2 ≤ (getCurrentEpoch state).toNat → Quiet state

/-! ## One slot -/

/-- From Altair, the votes of the pending attestations hold for any set, since none are kept. -/
private theorem PendingVoted.of_altair_le {fork : Fork}
    {votes : Set (ValidatorIndex × AttestationData)} (altair : .altair ≤ fork)
    (state : BeaconState preset fork) : PendingVoted votes state :=
  fun before => absurd before (Nat.not_lt_of_le altair)

/-- The upgrades due at a slot keep the pending attestations well formed. -/
private theorem PendingWellFormed.of_processUpgrades {forked after : ForkedBeaconState preset}
    (holds : PendingWellFormed forked.state)
    (computed : processUpgrades config checks forked = .ok after) :
    PendingWellFormed after.state :=
  processUpgrades_induction (property := fun state => PendingWellFormed state.state)
    (fun _ stepOk => PendingWellFormed.of_altair (upgradeNext_altair stepOk).1 _) holds computed

/-- The upgrades due at a slot keep the pending attestations resolved. -/
private theorem PendingResolved.of_processUpgrades {forked after : ForkedBeaconState preset}
    (holds : PendingResolved forked.state)
    (computed : processUpgrades config checks forked = .ok after) :
    PendingResolved after.state :=
  processUpgrades_induction (property := fun state => PendingResolved state.state)
    (fun _ stepOk => PendingResolved.of_altair (upgradeNext_altair stepOk).1 _) holds computed

/-- The caching of a slot keeps the pending attestations resolved. -/
private theorem PendingResolved.of_processSlot {fork : Fork}
    {state cached : BeaconState preset fork}
    (resolved : PendingResolved state) (computed : processSlot state = .ok cached) :
    PendingResolved cached := by
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok computed
  intro before attestation member
  rw [cachedEq] at member
  obtain ⟨signers, ok⟩ := resolved before attestation member
  refine ⟨signers, ?_⟩
  unfold getPendingAttestingIndices at ok ⊢
  rw [CommitteesKept.of_eq (state := state) (other := cached) (by rw [cachedEq])
    (by rw [cachedEq]) (computeEpochAtSlot preset attestation.data.slot) attestation.data.slot
    attestation.data.index rfl]
  exact ok

/-- The caching of a slot keeps the facts of a run. -/
private theorem RunHolds.of_processSlot {start : RunStart} {budget startEpoch : Nat}
    {fork : Fork} {state cached : BeaconState preset fork}
    (holds : RunHolds config start budget startEpoch state)
    (computed : processSlot state = .ok cached) :
    RunHolds config start budget startEpoch cached := by
  have frame := frame_processSlot computed
  have resolved := holds.resolved.of_processSlot computed
  have voted := holds.voted.of_processSlot computed
  have bounded := holds.bounded.of_processSlot computed
  have invariant := frame.invariant holds.invariant
  have early := holds.early.of_frame frame
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok computed
  have shaped := holds.shaped
  exact ⟨holds.started, invariant, ⟨shaped.balancesMatch, shaped.participationMatches,
    shaped.inactivityScoresMatch, shaped.capped, shaped.inside⟩, holds.wellFormed, resolved,
    early, voted, bounded, holds.quietCurrent, holds.quiet⟩

/-- An epoch of the run, plus one and the longest lookahead, is at most the exit ceiling there. -/
private theorem first_le {start : RunStart} {budget epochs lastEpoch startEpoch epoch : Nat}
    (conditions : RunConditions preset config start budget epochs lastEpoch)
    (fits : startEpoch + epochs ≤ lastEpoch) (started : startEpoch ≤ epoch) :
    epoch + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤
      start.ceilingAt preset budget (epoch - startEpoch) := by
  have firstStart := conditions.firstStart
  have step : epoch - startEpoch ≤ (epoch - startEpoch) * start.exitStep preset budget :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  unfold RunStart.ceilingAt
  omega

/-- A chain of upgrades extends by one more due upgrade. -/
private theorem UpgradesPass.snoc {first reached : ForkedBeaconState preset}
    {next : {post : ForkedBeaconState preset // reached.fork < post.fork}}
    (pass : UpgradesPass config checks first reached) (due : upgradeDue config reached = true)
    (computed : upgradeNext config checks reached = .ok next) :
    UpgradesPass config checks first next.val := by
  induction pass with
  | refl forked => exact .step due computed (.refl _)
  | step stepDue stepOk rest ih => exact .step stepDue stepOk (ih due computed)

/-- One slot keeps the facts of a run, before the upgrades of the slot it reaches. -/
private theorem RunHolds.of_advanceSlot {start : RunStart}
    {budget epochs lastEpoch startEpoch : Nat} {fork : Fork}
    {state advanced : BeaconState preset fork}
    (conditions : RunConditions preset config start budget epochs lastEpoch)
    (fits : startEpoch + epochs ≤ lastEpoch)
    (holds : RunHolds config start budget startEpoch state)
    (within : (state.slot.toNat + 1) / preset.SLOTS_PER_EPOCH.toNat ≤ startEpoch + epochs)
    (signers : (getCurrentEpoch state).toNat < startEpoch + 2 →
      (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 →
      ∀ cached, processSlot state = .ok cached → SignersWithinActive cached)
    (computed : advanceSlot config checks state = .ok advanced) :
    RunHolds config start budget startEpoch advanced := by
  have stateEpoch := getCurrentEpoch_toNat state
  have advancedEpoch := getCurrentEpoch_toNat advanced
  have slot := advanceSlot_slot computed
  have invariant := (advanceSlot_invariant holds.invariant computed).1
  have shaped := advanceSlot_shaped computed holds.shaped
  have wellFormed := holds.wellFormed.of_advanceSlot computed
  have resolved := holds.resolved.of_advanceSlot conditions.apart holds.wellFormed computed
  have early := holds.early.of_advanceSlot computed
  have voted : PendingVoted Set.univ advanced := by
    by_cases before : fork < .altair
    · exact holds.voted.of_advanceSlot before conditions.apart holds.early computed
    · exact PendingVoted.of_altair_le (Nat.le_of_not_lt before) advanced
  -- The epoch moves on by at most one.
  have moves : (getCurrentEpoch advanced).toNat = (getCurrentEpoch state).toNat ∨
      (getCurrentEpoch advanced).toNat = (getCurrentEpoch state).toNat + 1 := by
    rw [advancedEpoch, stateEpoch, slot, Nat.succ_div]
    split <;> simp
  have started : startEpoch ≤ (getCurrentEpoch advanced).toNat := by
    have := holds.started
    omega
  have quietCurrent : startEpoch < (getCurrentEpoch advanced).toNat → QuietCurrent advanced := by
    intro late
    rcases moves with same | crossed
    · exact (holds.quietCurrent (by omega)).of_advanceSlot computed
    · exact advanceSlot_quietCurrent_of_lt computed (by omega)
  have quiet : startEpoch + 2 ≤ (getCurrentEpoch advanced).toNat → Quiet advanced := by
    intro late
    rcases moves with same | crossed
    · exact (holds.quiet (by omega)).of_advanceSlot computed
    · exact (holds.quietCurrent (by omega)).quiet_of_advanceSlot_of_lt computed (by omega)
  refine ⟨started, invariant, shaped, wellFormed, resolved, early, voted, ?_, quietCurrent, quiet⟩
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  have cachedHolds := holds.of_processSlot cachedOk
  have cachedEpoch : (getCurrentEpoch cached).toNat = (getCurrentEpoch state).toNat := by
    rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, processSlot_slot cachedOk]
  have nextEpoch : (getCurrentEpoch { epoched with slot := next }).toNat =
      next.toNat / preset.SLOTS_PER_EPOCH.toNat := getCurrentEpoch_toNat _
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    have crossed := nextSlot_epoch_of_boundary sum boundary
    have nextIs : (state.slot.toNat + 1) / preset.SLOTS_PER_EPOCH.toNat =
        (getCurrentEpoch state).toNat + 1 := by
      rw [← sum, crossed, stateEpoch]
    have started := holds.started
    have boundaryNat : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 := by
      have := congrArg UInt64.toNat boundary
      rwa [UInt64.toNat_mod, sum] at this
    have cachedSigners : SignersWithinActive cached := by
      by_cases early : (getCurrentEpoch state).toNat < startEpoch + 2
      · exact signers early boundaryNat cached cachedOk
      · exact (cachedHolds.quiet (by omega)).signers
    have bounded := RunBounded.of_processEpoch_of_run conditions cachedHolds.bounded
      cachedHolds.invariant cachedHolds.shaped cachedHolds.resolved
      (by rw [cachedEpoch]; omega)
      (first_le conditions fits cachedHolds.started) cachedSigners epochedOk
    have elapsed : (getCurrentEpoch { epoched with slot := next }).toNat - startEpoch =
        (getCurrentEpoch cached).toNat - startEpoch + 1 := by
      have := holds.started
      omega
    rw [elapsed]
    exact bounded.withSlot next
  · rename_i inside
    simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    have same := nextSlot_epoch_of_inside sum inside
    have elapsed : (getCurrentEpoch { cached with slot := next }).toNat - startEpoch =
        (getCurrentEpoch cached).toNat - startEpoch := by
      omega
    rw [elapsed]
    exact cachedHolds.bounded.withSlot next

/-- The upgrades due at a slot keep the facts of a run, while the epoch is within the run. -/
private theorem RunHolds.of_processUpgrades {start : RunStart}
    {budget epochs lastEpoch startEpoch : Nat} {forked after : ForkedBeaconState preset}
    (conditions : RunConditions preset config start budget epochs lastEpoch)
    (fits : startEpoch + epochs ≤ lastEpoch)
    (counted : (getCurrentEpoch forked.state).toNat ≤ startEpoch + epochs)
    (holds : RunHolds config start budget startEpoch forked.state)
    (computed : processUpgrades config checks forked = .ok after) :
    RunHolds config start budget startEpoch after.state := by
  have epochEq : getCurrentEpoch after.state = getCurrentEpoch forked.state := by
    unfold getCurrentEpoch
    rw [processUpgrades_slot computed]
  have bounded := holds.bounded.of_processUpgrades
    (holds.bounded.effective_le conditions (by omega))
    (first_le conditions fits holds.started) computed
  refine ⟨?_, (processUpgrades_invariant holds.invariant computed).1,
    processUpgrades_shaped conditions.activation conditions.compounding computed holds.shaped,
    holds.wellFormed.of_processUpgrades computed, holds.resolved.of_processUpgrades computed,
    holds.early.of_processUpgrades computed, holds.voted.of_processUpgrades computed, ?_,
    fun late => (holds.quietCurrent (epochEq ▸ late)).of_processUpgrades computed,
    fun late => (holds.quiet (epochEq ▸ late)).of_processUpgrades computed⟩
  · rw [epochEq]
    exact holds.started
  · rw [epochEq]
    exact bounded

/-- One slot of a bounded run succeeds, with the upgrades due at the slot it reaches.

The epoch of the next slot is at most the first epoch of the run plus the number of epochs.

The run then ends by the last epoch of the conditions.

At the end of an epoch, the draws meet a validator at the cap.

In the first two epochs of the run, the signers hold at most the active balance.

The draws of the upgrades due at the next slot meet a validator at the cap.

Before Altair, the epoch is within the limit before Altair. -/
theorem RunHolds.advanceSlotAcross_exists_ok
    [∀ fork, Serialization.Ssz.LawfulSszType (BeaconState preset fork)]
    [NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat]
    [NeZero preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat]
    [NeZero preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat]
    {start : RunStart} {budget epochs lastEpoch startEpoch : Nat}
    {forked : ForkedBeaconState preset}
    (conditions : RunConditions preset config start budget epochs lastEpoch)
    (fits : startEpoch + epochs ≤ lastEpoch)
    (holds : RunHolds config start budget startEpoch forked.state)
    (within : (forked.state.slot.toNat + 1) / preset.SLOTS_PER_EPOCH.toNat ≤ startEpoch + epochs)
    (signers : (getCurrentEpoch forked.state).toNat < startEpoch + 2 →
      (forked.state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 →
      ∀ cached, processSlot forked.state = .ok cached → SignersWithinActive cached)
    (draws : (forked.state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 →
      ∀ cached, processSlot forked.state = .ok cached → EpochDraws config checks cached)
    (upgradeDraws : ∀ advanced, advanceSlot config checks forked.state = .ok advanced →
      ∀ upgrading, UpgradesPass config checks ⟨forked.fork, advanced⟩ upgrading →
        upgradeDue config upgrading = true → UpgradeDraws upgrading)
    (limit : forked.fork < .altair →
      (getCurrentEpoch forked.state).toNat ≤ preset.epochLimitBeforeAltair) :
    ∃ next, advanceSlotAcross config checks forked = .ok next := by
  have started := holds.started
  have stateEpoch := getCurrentEpoch_toNat forked.state
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by
    have := conditions.slots
    omega
  -- The next slot is before the end of the last epoch, so it fits in 64 bits.
  have slotFits : forked.state.slot.toNat + 1 < 2 ^ 64 := by
    have room := conditions.slotRoom
    have below := Nat.lt_div_mul_add (a := forked.state.slot.toNat + 1) positive
    have scaled : (forked.state.slot.toNat + 1) / preset.SLOTS_PER_EPOCH.toNat *
        preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_EPOCH.toNat ≤
        (lastEpoch + preset.MIN_SEED_LOOKAHEAD.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ (by omega)
    omega
  obtain ⟨advanced, advancedOk⟩ := advanceSlot_exists_ok (config := config) (checks := checks)
    slotFits fun boundary cached cachedOk => by
      have cachedHolds := holds.of_processSlot cachedOk
      have cachedEpoch : (getCurrentEpoch cached).toNat = (getCurrentEpoch forked.state).toNat := by
        rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, processSlot_slot cachedOk]
      have nextIs : (forked.state.slot.toNat + 1) / preset.SLOTS_PER_EPOCH.toNat =
          (getCurrentEpoch forked.state).toNat + 1 := by
        rw [stateEpoch]
        exact Nat.succ_div_of_dvd (Nat.dvd_of_mod_eq_zero boundary)
      have cachedSigners : SignersWithinActive cached := by
        by_cases early : (getCurrentEpoch forked.state).toNat < startEpoch + 2
        · exact signers early boundary cached cachedOk
        · exact (cachedHolds.quiet (by omega)).signers
      exact processEpoch_exists_ok_of_run conditions cachedHolds.bounded cachedHolds.invariant
        cachedHolds.shaped cachedHolds.wellFormed cachedHolds.resolved
        (by rw [cachedEpoch]; omega) (by omega) (by rwa [processSlot_slot cachedOk])
        (first_le conditions fits cachedHolds.started) cachedSigners
        (draws boundary cached cachedOk) (fun before => cachedEpoch ▸ limit before)
  have advancedHolds := RunHolds.of_advanceSlot conditions fits holds within signers advancedOk
  have advancedEpoch : (getCurrentEpoch advanced).toNat ≤ startEpoch + epochs := by
    rw [getCurrentEpoch_toNat, advanceSlot_slot advancedOk]
    exact within
  have advancedSlot := advanceSlot_slot advancedOk
  -- Each due upgrade succeeds from a state that the upgrades pass through.
  obtain ⟨after, afterOk, -⟩ := processUpgrades_exists_ok (config := config) (checks := checks)
    (property := fun upgrading =>
      UpgradesPass config checks ⟨forked.fork, advanced⟩ upgrading ∧
        upgrading.state.slot = advanced.slot ∧
        RunBounded config start budget ((getCurrentEpoch advanced).toNat - startEpoch)
          upgrading.state ∧
        Shaped upgrading.state ∧ PendingResolved upgrading.state ∧
        PendingVoted Set.univ upgrading.state)
    ⟨.refl _, rfl, advancedHolds.bounded, advancedHolds.shaped, advancedHolds.resolved,
      advancedHolds.voted⟩
    (fun reached ⟨passes, slotEq, bounded, shaped, resolved, voted⟩ due => by
      have epochEq : getCurrentEpoch reached.state = getCurrentEpoch advanced := by
        unfold getCurrentEpoch
        rw [slotEq]
      have nonzero : reached.state.slot ≠ 0 := by
        intro zero
        have := congrArg UInt64.toNat (slotEq.symm.trans zero)
        simp only [UInt64.toNat_zero] at this
        omega
      have ready := UpgradeReady.of_run conditions bounded shaped resolved (by omega)
        (by rw [epochEq]; omega) (upgradeDraws advanced advancedOk reached passes due) due voted
        fun _ => nonzero
      obtain ⟨next, nextOk⟩ := upgradeNext_exists_ok (config := config) (checks := checks) ready
      have altair := (upgradeNext_altair nextOk).1
      refine ⟨next, nextOk, passes.snoc due nextOk,
        (upgradeFrame_upgradeNext nextOk).slot.trans slotEq,
        bounded.of_upgradeNext (bounded.effective_le conditions (by omega))
          (by rw [epochEq]; exact first_le conditions fits advancedHolds.started) nextOk,
        upgradeNext_shaped conditions.activation conditions.compounding nextOk shaped,
        PendingResolved.of_altair altair _, PendingVoted.of_altair_le altair _⟩)
  exact ⟨after, by simp only [advanceSlotAcross, advancedOk, bind, Except.bind]; exact afterOk⟩

/-- One slot of a bounded run keeps the facts of the run, with the upgrades on the way.

The epoch of the next slot is at most the first epoch of the run plus the number of epochs.

The run then ends by the last epoch of the conditions.

In the first two epochs of the run, the signers hold at most the active balance. -/
theorem RunHolds.of_advanceSlotAcross {start : RunStart}
    {budget epochs lastEpoch startEpoch : Nat} {forked next : ForkedBeaconState preset}
    (conditions : RunConditions preset config start budget epochs lastEpoch)
    (fits : startEpoch + epochs ≤ lastEpoch)
    (holds : RunHolds config start budget startEpoch forked.state)
    (within : (forked.state.slot.toNat + 1) / preset.SLOTS_PER_EPOCH.toNat ≤ startEpoch + epochs)
    (signers : (getCurrentEpoch forked.state).toNat < startEpoch + 2 →
      (forked.state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 →
      ∀ cached, processSlot forked.state = .ok cached → SignersWithinActive cached)
    (computed : advanceSlotAcross config checks forked = .ok next) :
    RunHolds config start budget startEpoch next.state := by
  obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
  have advancedEpoch : (getCurrentEpoch advanced).toNat ≤ startEpoch + epochs := by
    rw [getCurrentEpoch_toNat, advanceSlot_slot advancedOk]
    exact within
  exact RunHolds.of_processUpgrades (forked := ⟨forked.fork, advanced⟩) conditions fits
    advancedEpoch (RunHolds.of_advanceSlot conditions fits holds within signers advancedOk)
    upgraded

/-- A run of slots from a state of a run succeeds and keeps the facts of the run.

The hypotheses on the states it reaches read the first epoch of the run. -/
private theorem advanceSlotsAcross_run
    [∀ fork, Serialization.Ssz.LawfulSszType (BeaconState preset fork)]
    [NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat]
    [NeZero preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat]
    [NeZero preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat]
    {start : RunStart} {budget epochs lastEpoch startEpoch : Nat}
    (conditions : RunConditions preset config start budget epochs lastEpoch)
    (fits : startEpoch + epochs ≤ lastEpoch) :
    ∀ (count : Nat) {forked : ForkedBeaconState preset},
      RunHolds config start budget startEpoch forked.state →
      (forked.state.slot.toNat + count) / preset.SLOTS_PER_EPOCH.toNat ≤ startEpoch + epochs →
      (∀ steps < count, ∀ reached, advanceSlotsAcross config checks steps forked = .ok reached →
        (getCurrentEpoch reached.state).toNat < startEpoch + 2 →
        (reached.state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 →
        ∀ cached, processSlot reached.state = .ok cached → SignersWithinActive cached) →
      DrawsAtCap config checks forked count → EpochLimitBeforeAltair forked count →
      ∃ after, advanceSlotsAcross config checks count forked = .ok after ∧
        RunHolds config start budget startEpoch after.state
  | 0, forked, holds, _, _, _, _ => ⟨forked, rfl, holds⟩
  | count + 1, forked, holds, within, signers, draws, limit => by
    have stepWithin : (forked.state.slot.toNat + 1) / preset.SLOTS_PER_EPOCH.toNat ≤
        startEpoch + epochs :=
      (Nat.div_le_div_right (by omega)).trans within
    have stepSigners := signers 0 (Nat.succ_pos _) forked rfl
    obtain ⟨stepDraws, stepUpgradeDraws⟩ := draws 0 (Nat.succ_pos _) forked rfl
    have stepLimit : forked.fork < .altair →
        (getCurrentEpoch forked.state).toNat ≤ preset.epochLimitBeforeAltair := fun before => by
      rw [getCurrentEpoch_toNat]
      exact (Nat.div_le_div_right (by omega)).trans (limit before)
    obtain ⟨next, nextOk⟩ := RunHolds.advanceSlotAcross_exists_ok conditions fits holds
      stepWithin stepSigners stepDraws stepUpgradeDraws stepLimit
    have nextHolds := RunHolds.of_advanceSlotAcross conditions fits holds stepWithin
      stepSigners nextOk
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp nextOk
    have nextSlot : next.state.slot.toNat = forked.state.slot.toNat + 1 := by
      rw [processUpgrades_slot upgraded]
      exact advanceSlot_slot advancedOk
    have nextFork : forked.fork ≤ next.fork :=
      processUpgrades_fork_le (forked := ⟨forked.fork, advanced⟩) upgraded
    -- The rest of the run starts from the next state, one step later.
    have shifted : ∀ {steps reached}, advanceSlotsAcross config checks steps next = .ok reached →
        advanceSlotsAcross config checks (steps + 1) forked = .ok reached := fun reachedOk => by
      simp only [advanceSlotsAcross, nextOk, bind, Except.bind]
      exact reachedOk
    obtain ⟨after, afterOk, afterHolds⟩ := advanceSlotsAcross_run conditions fits count
      (forked := next) nextHolds (by rwa [nextSlot, Nat.add_right_comm, Nat.add_assoc])
      (fun steps below reached reachedOk =>
        signers (steps + 1) (by omega) reached (shifted reachedOk))
      (fun steps below reached reachedOk =>
        draws (steps + 1) (by omega) reached (shifted reachedOk))
      (fun before => by
        rw [nextSlot, Nat.add_right_comm, Nat.add_assoc]
        exact limit (Nat.lt_of_le_of_lt nextFork before))
    exact ⟨after, by simp only [advanceSlotsAcross, nextOk, bind, Except.bind]; exact afterOk,
      afterHolds⟩

/-! ## The run -/

/-- A run of slots from a bounded state succeeds and keeps the facts of the run.

The run starts at the epoch of the state, and its last slot is at most that many epochs later.

The run takes its three hypotheses on the states it reaches. -/
theorem advanceSlotsAcross_exists_ok_of_run
    [∀ fork, Serialization.Ssz.LawfulSszType (BeaconState preset fork)]
    [NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat]
    [NeZero preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat]
    [NeZero preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat]
    {start : RunStart} {budget epochs lastEpoch count : Nat}
    {forked : ForkedBeaconState preset}
    (conditions : RunConditions preset config start budget epochs lastEpoch)
    (fits : (getCurrentEpoch forked.state).toNat + epochs ≤ lastEpoch)
    (holds : RunHolds config start budget (getCurrentEpoch forked.state).toNat forked.state)
    (within : (forked.state.slot.toNat + count) / preset.SLOTS_PER_EPOCH.toNat ≤
      (getCurrentEpoch forked.state).toNat + epochs)
    (signers : SignersEarly config checks forked count)
    (draws : DrawsAtCap config checks forked count)
    (limit : EpochLimitBeforeAltair forked count) :
    ∃ after, advanceSlotsAcross config checks count forked = .ok after ∧
      RunHolds config start budget (getCurrentEpoch forked.state).toNat after.state :=
  advanceSlotsAcross_run conditions fits count holds within signers draws limit

/-- Every slot advance within the horizon succeeds from a bounded state.

The state keeps the facts of a run that starts at its own epoch.

The conditions hold for some number of epochs, which is within the horizon of the scores.

Their last epoch is at least that number of epochs past the epoch of the state.

The later slot is in an epoch at most that number of epochs past the epoch of the state.

The run takes three hypotheses on the states it reaches.

In its first two epochs, the signers hold at most the active balance.

The draws meet a validator at the cap, and before Altair the run ends within the epoch limit.

The state that the advance returns keeps the facts of the run. -/
theorem processSlotsAcross_exists_ok_of_run
    [∀ fork, Serialization.Ssz.LawfulSszType (BeaconState preset fork)]
    [NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat]
    [NeZero preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat]
    [NeZero preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat]
    {start : RunStart} {budget epochs lastEpoch : Nat}
    {forked : ForkedBeaconState preset} {slot : Slot}
    (conditions : RunConditions preset config start budget epochs lastEpoch)
    (fits : (getCurrentEpoch forked.state).toNat + epochs ≤ lastEpoch)
    (holds : RunHolds config start budget (getCurrentEpoch forked.state).toNat forked.state)
    (later : forked.state.slot < slot)
    (within : slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤
      (getCurrentEpoch forked.state).toNat + epochs)
    (signers : SignersEarly config checks forked (slot.toNat - forked.state.slot.toNat))
    (draws : DrawsAtCap config checks forked (slot.toNat - forked.state.slot.toNat))
    (limit : EpochLimitBeforeAltair forked (slot.toNat - forked.state.slot.toNat)) :
    ∃ after, processSlotsAcross config checks forked slot = .ok after ∧
      RunHolds config start budget (getCurrentEpoch forked.state).toNat after.state := by
  have ahead := UInt64.lt_iff_toNat_lt.mp later
  obtain ⟨after, afterOk, afterHolds⟩ := advanceSlotsAcross_exists_ok_of_run conditions fits
    holds (by rwa [Nat.add_sub_cancel' ahead.le]) signers draws limit
  refine ⟨after, ?_, afterHolds⟩
  have ensured : ensure (forked.state.slot < slot)
      (TransitionError.slotNotAfter slot forked.state.slot) = .ok () := ensure_ok_iff.mpr later
  simp only [processSlotsAcross, ensured, bind, Except.bind]
  exact afterOk

/-- On mainnet, every slot advance within `2.25 * 10^6` epochs succeeds from a bounded state.

The epoch of the state is at most `2^40`.

The state keeps the facts of a run from its epoch, with the mainnet bounds at the start.

The budget of effective balances is `2^57` Gwei.

The run takes the three hypotheses on the states it reaches.

From Electra, the leak takes every validator off the cap of 2048 ETH.

It does so within about `7.7 * 10^5` epochs.

From a balance at the cap, it takes 68 epochs. -/
theorem processSlotsAcross_exists_ok_mainnet {forked : ForkedBeaconState Preset.mainnet}
    {slot : Slot} (early : (getCurrentEpoch forked.state).toNat ≤ 2 ^ 40)
    (holds : RunHolds Config.mainnet (RunStart.mainnet (getCurrentEpoch forked.state).toNat)
      (2 ^ 57) (getCurrentEpoch forked.state).toNat forked.state)
    (later : forked.state.slot < slot)
    (within : slot.toNat / Preset.mainnet.SLOTS_PER_EPOCH.toNat ≤
      (getCurrentEpoch forked.state).toNat + 2250000)
    (signers : SignersEarly Config.mainnet checks forked (slot.toNat - forked.state.slot.toNat))
    (draws : DrawsAtCap Config.mainnet checks forked (slot.toNat - forked.state.slot.toNat))
    (limit : EpochLimitBeforeAltair forked (slot.toNat - forked.state.slot.toNat)) :
    ∃ after, processSlotsAcross Config.mainnet checks forked slot = .ok after ∧
      RunHolds Config.mainnet (RunStart.mainnet (getCurrentEpoch forked.state).toNat) (2 ^ 57)
        (getCurrentEpoch forked.state).toNat after.state :=
  processSlotsAcross_exists_ok_of_run (runConditions_mainnet early) (Nat.le_refl _) holds later
    within signers draws limit

/-! ## A start that meets the facts -/

/-- The empty state at genesis, before any deposit, keeps the facts of a run from its epoch.

It meets any bounds at the start and any budget, since it has no validator and no balance. -/
theorem runHolds_emptyGenesisState {fork : Fork} (before : fork < .altair) (start : RunStart)
    (budget : Nat) (genesisTime : UInt64) (eth1BlockHash : Hash32) (depositCount : UInt64)
    (bodyRoot : Root) :
    RunHolds config start budget 0 (emptyGenesisState (preset := preset) config before
      genesisTime eth1BlockHash depositCount bodyRoot) := by
  have never : ∀ {later : Fork}, .altair ≤ later → ¬ later ≤ fork := fun altair atLeast =>
    absurd (Nat.lt_of_lt_of_le before (Nat.le_trans altair atLeast)) (by simp)
  have quiet := emptyGenesisState_quiet (preset := preset) (config := config) before genesisTime
    eth1BlockHash depositCount bodyRoot
  have notAltair : ¬ .altair ≤ fork := fun altair => never altair (Nat.le_refl _)
  have notElectra : ¬ .pectra ≤ fork := never (by decide)
  refine
    { started := Nat.zero_le _
      invariant := emptyGenesisState_invariant before _ _ _ _
      shaped := ?_
      wellFormed := ?_
      resolved := ?_
      early := fun _ => rfl
      voted := ?_
      bounded := ?_
      quietCurrent := fun _ => quiet.1
      quiet := fun _ => quiet }
  · exact ⟨rfl, fun altair => (notAltair altair).elim, fun altair => (notAltair altair).elim,
      fun _ member => by simp [emptyGenesisState] at member,
      fun electra => (notElectra electra).elim⟩
  · exact fun _ => ⟨fun _ member => by simp [emptyGenesisState] at member,
      fun _ member => by simp [emptyGenesisState] at member⟩
  · intro _ _ member
    simp [emptyGenesisState] at member
  · intro _ current _ member
    cases current <;> simp [recentPending, emptyGenesisState] at member
  refine ⟨?_, Or.inl ?_, ?_, fun altair => (notAltair altair).elim,
    fun _ member => by simp [emptyGenesisState] at member,
    fun electra => (notElectra electra).elim, ?_, fun capella => (never (by decide) capella).elim,
    fun electra => (notElectra electra).elim, fun electra => (notElectra electra).elim, ?_⟩
  all_goals simp [balanceSum, pendingDepositSum, effectiveBalanceSum, registryLoad,
    slashedBalanceSum, emptyGenesisState, notElectra]

/-- On mainnet, from the empty state at genesis, every slot advance before Altair succeeds.

So the hypotheses of the mainnet theorem can hold together, with an empty registry before Altair.
-/
theorem processSlotsAcross_exists_ok_emptyGenesisState {slot : Slot} (later : 0 < slot.toNat)
    (beforeAltair : slot.toNat / 32 < 74240) (genesisTime : UInt64) (eth1BlockHash : Hash32)
    (depositCount : UInt64) (bodyRoot : Root) :
    ∃ after, processSlotsAcross Config.mainnet checks
      ⟨.phase0, emptyGenesisState (preset := Preset.mainnet) Config.mainnet (by decide)
        genesisTime eth1BlockHash depositCount bodyRoot⟩ slot = .ok after := by
  have before : Fork.phase0 < .altair := by decide
  have slot0 : (emptyGenesisState (preset := Preset.mainnet) Config.mainnet before genesisTime
      eth1BlockHash depositCount bodyRoot).slot.toNat = 0 := rfl
  have epoch : (getCurrentEpoch (emptyGenesisState (preset := Preset.mainnet) Config.mainnet
      before genesisTime eth1BlockHash depositCount bodyRoot)).toNat = 0 := by
    simp [getCurrentEpoch, computeEpochAtSlot, emptyGenesisState, GENESIS_SLOT]
  obtain ⟨signers, draws, limit⟩ := runHypotheses_mainnet (checks := checks)
    (count := slot.toNat) (emptyGenesisState_quiet before genesisTime eth1BlockHash depositCount
      bodyRoot) (by rw [slot0, Nat.zero_add]; exact beforeAltair)
  have holds := runHolds_emptyGenesisState (preset := Preset.mainnet) (config := Config.mainnet)
    before (RunStart.mainnet 0) (2 ^ 57) genesisTime eth1BlockHash depositCount bodyRoot
  obtain ⟨after, computed, -⟩ := processSlotsAcross_exists_ok_mainnet (checks := checks)
    (forked := ⟨.phase0, emptyGenesisState Config.mainnet before genesisTime eth1BlockHash
      depositCount bodyRoot⟩) (slot := slot)
    (by rw [epoch]; exact Nat.zero_le _) (by rw [epoch]; exact holds)
    (UInt64.lt_iff_toNat_lt.mpr (by rw [slot0]; exact later))
    (by rw [epoch]; change slot.toNat / 32 ≤ 0 + 2250000; omega)
    (by rw [slot0, Nat.sub_zero]; exact signers) (by rw [slot0, Nat.sub_zero]; exact draws)
    (by rw [slot0, Nat.sub_zero]; exact limit)
  exact ⟨after, computed⟩

end EthLib.Consensus
