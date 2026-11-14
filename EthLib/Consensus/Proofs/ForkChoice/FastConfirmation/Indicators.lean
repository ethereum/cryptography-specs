module

public import EthLib.Base.Proofs.FilterM
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Basic
public import EthLib.Consensus.Proofs.Models.ForkChoice.HonestSupport
public import EthLib.Consensus.Proofs.Transition.FfgStake
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Proofs: the indicators that the fast confirmation rule computes

The rule confirms a block when its support from the store exceeds its safety threshold.

That check is Definition 4 of the fast confirmation paper, [arXiv 2405.00549v4][fcr].

The paper writes it, in its equation (5), as `S > Φ / 2 + β W - I`.

Here `S` is the support of the block, and `I` the stake of the known equivocators.

`W` is the weight of the committees from the slot of the block to the last slot.

`Φ` is the largest weight that could still vote for a sibling, plus the boost, less a discount.

The store computes each term in Gwei, with its own roundings.

It weighs the committees of a range exactly, from the effective balances of their active members.

A range with a whole epoch weighs the total active balance instead, which is no smaller.

Its `Φ` is the committee weight since the parent, plus the boost.

A discount is then taken off.

It comes from the votes for the parent from the committees of the empty slots before the block.

A discount above the committee weight since the parent is an error of the store.

For a block at or before the current slot, those empty slots lie in that range.

Their votes then weigh no more than the range, so that error never occurs.

The effective balance that the store reads for a validator is its weight as a stake.

The votes of a range for some nodes are the stake of the voters that the store counts.

The store's share of the adversary is the committee weight of `W`, divided by 100 and rounded down.

That share is then multiplied by the threshold in percent, and the equivocators are taken off.

So the weight covers the stake of `W`, and the share covers β of it for balances in 100 Gwei.

An average weight per slot in place of the exact one would not cover it.

With that cover, Lemmas 4 and 3 of the paper give the honest support of a confirmed block.

Twice that support, plus the discount, exceeds the committee weight and the boost.

The range of slots of the adversary starts at the block, or at its epoch when its parent is older.

The file also states the two FFG tests of the rule on the target of the current epoch.

[fcr]: https://arxiv.org/abs/2405.00549v4
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models Models.ForkChoice

variable {preset : Preset} {fork : Fork}

/-- The effective balance that the store reads for a validator is its weight as a stake.

This is the effective-balance assignment of arXiv 2405.00549v4, Section 2.1. -/
theorem toNat_eq_balanceAt_of_effectiveBalance {state : BeaconState preset fork}
    {index : ValidatorIndex} {value : Gwei}
    (valueOk : (do return (← validatorAt state index).effectiveBalance :
      Except ForkChoiceError Gwei) = .ok value) :
    value.toNat = balanceAt state index.toNat := by
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at valueOk
  obtain ⟨validator, found, rfl⟩ := valueOk
  simp [balanceAt, validatorAt_ok_iff.mp found]

namespace Store

variable {config : Config} {store : Store preset fork}

/-- The store's adversary for a range of slots, step by step.

It is the share of the committee weight, less the known equivocators of the committees. -/
theorem computeAdversarialWeight_steps {head : Root} {balanceSource : BeaconState preset fork}
    {startSlot endSlot : Slot} {adversary : Gwei}
    (result : store.computeAdversarialWeight config head balanceSource startSlot endSlot =
      .ok adversary) :
    ∃ weight share equivocation,
      store.computeCommitteeWeightBetweenSlots head balanceSource startSlot endSlot =
        .ok weight ∧
      mulChecked (weight / 100) config.CONFIRMATION_BYZANTINE_THRESHOLD = .ok share ∧
      store.getEquivocationScore head balanceSource startSlot endSlot = .ok equivocation ∧
      adversary = saturatingSub share equivocation := by
  simp only [computeAdversarialWeight, bind_ok_iff, mapError_ok_iff] at result
  obtain ⟨⟨weight, members⟩, pairOk, share, shareOk, rest⟩ := result
  -- The members come from the weight, or are read again when the weight did not need them.
  obtain ⟨participants, found, rest⟩ :
      ∃ participants, store.getCommitteesBetweenSlots head startSlot endSlot = .ok participants ∧
        ∃ equivocation,
          store.getEquivocationScoreOf balanceSource participants = .ok equivocation ∧
            adversary = saturatingSub share equivocation := by
    cases members with
    | none =>
      simp only [bind_ok_iff] at rest
      obtain ⟨participants, found, equivocation, equivocationOk, final⟩ := rest
      simp only [pure, Except.pure, Except.ok.injEq] at final
      exact ⟨participants, found, equivocation, equivocationOk, final.symm⟩
    | some members =>
      simp only [pure, Except.pure, bind, Except.bind] at rest
      split at rest
      · cases rest
      · rename_i equivocation equivocationOk
        simp only [Except.ok.injEq] at rest
        exact ⟨members, getCommitteesBetweenSlots_of_computeCommitteeWeightAndMembers pairOk,
          equivocation, equivocationOk, rest.symm⟩
  obtain ⟨equivocation, equivocationOk, final⟩ := rest
  refine ⟨weight, share, equivocation, ?_, shareOk, ?_, final⟩
  · simp [computeCommitteeWeightBetweenSlots, pairOk, bind, Except.bind, pure, Except.pure]
  · simp [getEquivocationScore, found, equivocationOk, bind, Except.bind]

/-- The store's adversary for a range of slots: its share of the weight, less the equivocators.

The share is the weight of the committees divided by 100, rounded down, times the threshold.

The share is then at most the adversary plus the stake of the equivocators. -/
theorem computeAdversarialWeight_share {head : Root} {balanceSource : BeaconState preset fork}
    {startSlot endSlot : Slot} {weight equivocation adversary : Gwei}
    (weightOk : store.computeCommitteeWeightBetweenSlots head balanceSource startSlot endSlot =
      .ok weight)
    (equivocationOk :
      store.getEquivocationScore head balanceSource startSlot endSlot = .ok equivocation)
    (result : store.computeAdversarialWeight config head balanceSource startSlot endSlot =
      .ok adversary) :
    weight.toNat / 100 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤
      adversary.toNat + equivocation.toNat := by
  obtain ⟨e, share, q, eOk, shareOk, qOk, rfl⟩ := computeAdversarialWeight_steps result
  rw [weightOk, Except.ok.injEq] at eOk
  subst eOk
  rw [equivocationOk, Except.ok.injEq] at qOk
  subst qOk
  rw [mulChecked_ok_iff] at shareOk
  rw [toNat_saturatingSub, shareOk.2, UInt64.toNat_div]
  have hundred : UInt64.toNat 100 = 100 := rfl
  rw [hundred]
  omega

/-- The adversary of a block in a later epoch than its parent counts from the start of its epoch.

The range of slots ends at the last slot before the current one. -/
theorem getAdversarialWeight_of_lt {head root : Root} {balanceSource : BeaconState preset fork}
    {currentSlot startSlot lastSlot : Slot} {block : BeaconBlock preset fork}
    {epoch parentEpoch : Epoch}
    (slotOk : store.getCurrentSlot config = .ok currentSlot)
    (blockOk : store.block root = .ok block)
    (epochOk : store.getBlockEpoch root = .ok epoch)
    (parentEpochOk : store.getBlockEpoch block.parentRoot = .ok parentEpoch)
    (later : parentEpoch < epoch)
    (startOk : computeStartSlotAtEpoch preset epoch = .ok startSlot)
    (lastOk : subChecked currentSlot 1 = .ok lastSlot) :
    store.getAdversarialWeight config head balanceSource root =
      store.computeAdversarialWeight config head balanceSource startSlot lastSlot := by
  simp [getAdversarialWeight, slotOk, blockOk, epochOk, parentEpochOk, later, startOk, lastOk,
    bind, Except.bind, Except.mapError]

/-- The adversary of a block in the epoch of its parent counts from the slot of the block.

The range of slots ends at the last slot before the current one. -/
theorem getAdversarialWeight_of_not_lt {head root : Root} {balanceSource : BeaconState preset fork}
    {currentSlot lastSlot : Slot} {block : BeaconBlock preset fork} {epoch parentEpoch : Epoch}
    (slotOk : store.getCurrentSlot config = .ok currentSlot)
    (blockOk : store.block root = .ok block)
    (epochOk : store.getBlockEpoch root = .ok epoch)
    (parentEpochOk : store.getBlockEpoch block.parentRoot = .ok parentEpoch)
    (notLater : ¬parentEpoch < epoch)
    (lastOk : subChecked currentSlot 1 = .ok lastSlot) :
    store.getAdversarialWeight config head balanceSource root =
      store.computeAdversarialWeight config head balanceSource block.slot lastSlot := by
  simp [getAdversarialWeight, slotOk, blockOk, epochOk, parentEpochOk, notLater, lastOk,
    bind, Except.bind, pure, Except.pure, Except.mapError]

/-- The store's safety threshold from its terms, each from its own step.

A discount above the committee weight since the parent is an error.

Otherwise the threshold adds the weight, the boost and twice the adversary, less the discount.

It then halves that sum, rounding down.

Each addition and the doubling can still fail, by leaving 64 bits. -/
theorem computeSafetyThreshold_of_steps {head root : Root}
    {balanceSource : BeaconState preset fork} {currentSlot firstSlot lastSlot : Slot}
    {block parentBlock : BeaconBlock preset fork}
    {proposerScore maximumSupport discount adversary : Gwei}
    (slotOk : store.getCurrentSlot config = .ok currentSlot)
    (blockOk : store.block root = .ok block)
    (parentOk : store.block block.parentRoot = .ok parentBlock)
    (boostOk : computeProposerScore config balanceSource = .ok proposerScore)
    (firstOk : addChecked parentBlock.slot 1 = .ok firstSlot)
    (lastOk : subChecked currentSlot 1 = .ok lastSlot)
    (weightOk : store.computeCommitteeWeightBetweenSlots head balanceSource firstSlot lastSlot =
      .ok maximumSupport)
    (discountOk :
      store.computeEmptySlotSupportDiscount config head balanceSource root = .ok discount)
    (adversaryOk : store.getAdversarialWeight config head balanceSource root = .ok adversary) :
    store.computeSafetyThreshold config head root balanceSource =
      if discount > maximumSupport then .error (.supportDiscountAboveMaximum root) else do
        let withBoost ← (addChecked maximumSupport proposerScore).mapError .arith
        let doubled ← (mulChecked 2 adversary).mapError .arith
        let bound ← (addChecked withBoost doubled).mapError .arith
        return (bound - discount) / 2 := by
  simp only [computeSafetyThreshold, slotOk, blockOk, parentOk, boostOk, firstOk, lastOk,
    weightOk, discountOk, adversaryOk, Except.mapError, bind, Except.bind]
  split <;> rfl

/-- A safety threshold that the store computes has a discount at most the weight since the parent.
-/
theorem discount_le_of_computeSafetyThreshold {head root : Root}
    {balanceSource : BeaconState preset fork} {currentSlot firstSlot lastSlot : Slot}
    {block parentBlock : BeaconBlock preset fork}
    {proposerScore maximumSupport discount adversary threshold : Gwei}
    (slotOk : store.getCurrentSlot config = .ok currentSlot)
    (blockOk : store.block root = .ok block)
    (parentOk : store.block block.parentRoot = .ok parentBlock)
    (boostOk : computeProposerScore config balanceSource = .ok proposerScore)
    (firstOk : addChecked parentBlock.slot 1 = .ok firstSlot)
    (lastOk : subChecked currentSlot 1 = .ok lastSlot)
    (weightOk : store.computeCommitteeWeightBetweenSlots head balanceSource firstSlot lastSlot =
      .ok maximumSupport)
    (discountOk :
      store.computeEmptySlotSupportDiscount config head balanceSource root = .ok discount)
    (adversaryOk : store.getAdversarialWeight config head balanceSource root = .ok adversary)
    (result : store.computeSafetyThreshold config head root balanceSource = .ok threshold) :
    discount ≤ maximumSupport := by
  rw [computeSafetyThreshold_of_steps slotOk blockOk parentOk boostOk firstOk lastOk weightOk
    discountOk adversaryOk] at result
  split at result
  · cases result
  · rename_i notAbove
    exact UInt64.not_lt.mp notAbove

/-- The store's safety threshold, doubled, covers its terms, up to the discount and one Gwei.

The terms are the committee weight since the parent, the boost and twice the adversary.

The halving of the threshold rounds down, which loses at most one Gwei. -/
theorem computeSafetyThreshold_bound {head root : Root} {balanceSource : BeaconState preset fork}
    {currentSlot firstSlot lastSlot : Slot} {block parentBlock : BeaconBlock preset fork}
    {proposerScore maximumSupport discount adversary threshold : Gwei}
    (slotOk : store.getCurrentSlot config = .ok currentSlot)
    (blockOk : store.block root = .ok block)
    (parentOk : store.block block.parentRoot = .ok parentBlock)
    (boostOk : computeProposerScore config balanceSource = .ok proposerScore)
    (firstOk : addChecked parentBlock.slot 1 = .ok firstSlot)
    (lastOk : subChecked currentSlot 1 = .ok lastSlot)
    (weightOk : store.computeCommitteeWeightBetweenSlots head balanceSource firstSlot lastSlot =
      .ok maximumSupport)
    (discountOk :
      store.computeEmptySlotSupportDiscount config head balanceSource root = .ok discount)
    (adversaryOk : store.getAdversarialWeight config head balanceSource root = .ok adversary)
    (result : store.computeSafetyThreshold config head root balanceSource = .ok threshold) :
    maximumSupport.toNat + proposerScore.toNat + 2 * adversary.toNat ≤
      2 * threshold.toNat + discount.toNat + 1 := by
  rw [computeSafetyThreshold_of_steps slotOk blockOk parentOk boostOk firstOk lastOk weightOk
    discountOk adversaryOk] at result
  split at result
  · cases result
  rename_i notAbove
  simp only [bind_ok_iff, mapError_ok_iff, pure, Except.pure, Except.ok.injEq] at result
  obtain ⟨withBoost, withBoostOk, doubled, doubledOk, bound, boundOk, rfl⟩ := result
  rw [addChecked_ok_iff] at withBoostOk boundOk
  rw [mulChecked_ok_iff] at doubledOk
  have two : UInt64.toNat 2 = 2 := rfl
  rw [two] at doubledOk
  rw [gt_iff_lt, UInt64.lt_iff_toNat_lt] at notAbove
  have le : discount ≤ bound := by
    rw [UInt64.le_iff_toNat_le]
    omega
  rw [UInt64.toNat_div, UInt64.toNat_sub_of_le _ _ le, two]
  omega

/-- The terms of a safety threshold that the store computes, each from its own step.

They are the current slot, the block and its parent, and the boost.

They are also the first and last slots of the range since the parent, and its committee weight.

They are also the discount and the adversary of the block. -/
theorem computeSafetyThreshold_eq_ok {head root : Root} {balanceSource : BeaconState preset fork}
    {threshold : Gwei}
    (result : store.computeSafetyThreshold config head root balanceSource = .ok threshold) :
    ∃ currentSlot block parentBlock proposerScore firstSlot lastSlot maximumSupport
      discount adversary,
      store.getCurrentSlot config = .ok currentSlot ∧ store.block root = .ok block ∧
      store.block block.parentRoot = .ok parentBlock ∧
      computeProposerScore config balanceSource = .ok proposerScore ∧
      addChecked parentBlock.slot 1 = .ok firstSlot ∧ subChecked currentSlot 1 = .ok lastSlot ∧
      store.computeCommitteeWeightBetweenSlots head balanceSource firstSlot lastSlot =
        .ok maximumSupport ∧
      store.computeEmptySlotSupportDiscount config head balanceSource root = .ok discount ∧
      store.getAdversarialWeight config head balanceSource root = .ok adversary := by
  have steps := result
  simp only [computeSafetyThreshold, bind_ok_iff, mapError_ok_iff] at steps
  obtain ⟨c, cOk, b, bOk, pb, pbOk, ps, psOk, f, fOk, l, lOk, m, mOk, d, dOk, a, aOk,
    -⟩ := steps
  exact ⟨c, b, pb, ps, f, l, m, d, a, cOk, bOk, pbOk, psOk, fOk, lOk, mOk, dOk, aOk⟩

/-- The range of slots of the adversary of a block, and the adversary over it.

The range ends at the last slot before the current one.

It starts at the slot of the block, or at the start of the epoch of the block. -/
theorem getAdversarialWeight_eq_ok {head root : Root} {balanceSource : BeaconState preset fork}
    {adversary : Gwei}
    (result : store.getAdversarialWeight config head balanceSource root = .ok adversary) :
    ∃ currentSlot block startSlot lastSlot,
      store.getCurrentSlot config = .ok currentSlot ∧ store.block root = .ok block ∧
      subChecked currentSlot 1 = .ok lastSlot ∧
      (startSlot = block.slot ∨
        computeStartSlotAtEpoch preset (computeEpochAtSlot preset block.slot) = .ok startSlot) ∧
      store.computeAdversarialWeight config head balanceSource startSlot lastSlot =
        .ok adversary := by
  have steps := result
  simp only [getAdversarialWeight, bind_ok_iff] at steps
  obtain ⟨c, cOk, b, bOk, e, eOk, pe, -, range⟩ := steps
  have epoch : computeEpochAtSlot preset b.slot = e := by
    simpa [getBlockEpoch, bOk, bind, Except.bind, pure, Except.pure] using eOk
  split_ifs at range
  · simp only [bind_ok_iff, mapError_ok_iff] at range
    obtain ⟨start, startOk, l, lOk, done⟩ := range
    exact ⟨c, b, start, l, cOk, bOk, lOk, .inr (epoch ▸ startOk), done⟩
  · simp only [bind_ok_iff, mapError_ok_iff, pure, Except.pure, Except.ok.injEq] at range
    obtain ⟨start, startOk, l, lOk, done⟩ := range
    exact ⟨c, b, start, l, cOk, bOk, lOk, .inl startOk.symm, done⟩

/-- The terms of the store's adversary over a range of slots, each from its own step.

They are the weight of the committees of the range, and the known equivocators. -/
theorem computeAdversarialWeight_eq_ok {head : Root} {balanceSource : BeaconState preset fork}
    {startSlot endSlot : Slot} {adversary : Gwei}
    (result : store.computeAdversarialWeight config head balanceSource startSlot endSlot =
      .ok adversary) :
    ∃ weight equivocation,
      store.computeCommitteeWeightBetweenSlots head balanceSource startSlot endSlot =
        .ok weight ∧
      store.getEquivocationScore head balanceSource startSlot endSlot = .ok equivocation := by
  obtain ⟨weight, -, equivocation, weightOk, -, equivocationOk, -⟩ :=
    computeAdversarialWeight_steps result
  exact ⟨weight, equivocation, weightOk, equivocationOk⟩

/-- A block is confirmed when its support and its threshold are computed, the first above. -/
theorem isOneConfirmed_eq_ok_true_iff {head root : Root}
    {balanceSource : BeaconState preset fork} {tally : VoteTally} :
    store.isOneConfirmed config head balanceSource tally root = .ok true ↔
      ∃ support threshold, store.scoreFromTally tally ⟨root, .pending⟩ = .ok support ∧
        store.computeSafetyThreshold config head root balanceSource = .ok threshold ∧
        threshold < support := by
  simp [isOneConfirmed, bind_ok_iff, pure, Except.pure]

/-- A confirmed block has support above its safety threshold. -/
theorem threshold_lt_of_isOneConfirmed {head root : Root} {balanceSource : BeaconState preset fork}
    {tally : VoteTally} {support threshold : Gwei}
    (supportOk : store.scoreFromTally tally ⟨root, .pending⟩ = .ok support)
    (thresholdOk : store.computeSafetyThreshold config head root balanceSource = .ok threshold)
    (confirmed : store.isOneConfirmed config head balanceSource tally root = .ok true) :
    threshold.toNat < support.toNat := by
  simp only [isOneConfirmed, supportOk, thresholdOk, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq, decide_eq_true_eq] at confirmed
  exact UInt64.lt_iff_toNat_lt.mp confirmed

/-- A total balance of some indices covers the stake of a set among them. -/
theorem stake_le_of_getTotalBalance {balanceSource : BeaconState preset fork}
    {indices : List ValidatorIndex} {total : Gwei} {W : Finset ValidatorIndex}
    (totalOk : getTotalBalance balanceSource indices = .ok total) (among : ∀ v ∈ W, v ∈ indices) :
    stake (fun v => balanceAt balanceSource v.toNat) W ≤ total.toNat := by
  obtain ⟨-, -, total⟩ := getTotalBalance_ok_iff_stake.mp totalOk
  rw [total]
  exact le_max_of_le_right (stake_mono fun v member => List.mem_toFinset.mpr (among v member))

/-- A range with a whole epoch weighs at least the total stake of the active validators.

A validator weighs its effective balance in the source of balances.

It is active when it is active in the current epoch of that source. -/
theorem stake_le_computeCommitteeWeightBetweenSlots_of_covered {head : Root}
    {balanceSource : BeaconState preset fork} {startSlot endSlot : Slot} {weight : Gwei}
    (covered : isFullValidatorSetCovered preset startSlot endSlot = .ok true)
    (weightOk : store.computeCommitteeWeightBetweenSlots head balanceSource startSlot endSlot =
      .ok weight) :
    stake (fun v => balanceAt balanceSource v.toNat)
        (getActiveValidatorIndices balanceSource (getCurrentEpoch balanceSource)).toFinset ≤
      weight.toNat := by
  rw [computeCommitteeWeightBetweenSlots_of_covered covered, mapError_ok_iff] at weightOk
  exact stake_le_of_getTotalBalance (getTotalActiveBalance_ok weightOk)
    fun v member => List.mem_toFinset.mp member

/-- The store's weight of the committees of a range covers the stake of active members.

A member weighs its effective balance in the source of balances.

It is active when that source holds it, active in the epoch of that source.

Each member of the set must be in every set of members that the store reads for the range. -/
theorem stake_le_computeCommitteeWeightBetweenSlots_of_reads {head : Root}
    {balanceSource : BeaconState preset fork} {startSlot endSlot : Slot} {weight : Gwei}
    {W : Finset ValidatorIndex}
    (weightOk : store.computeCommitteeWeightBetweenSlots head balanceSource startSlot endSlot =
      .ok weight)
    (inside : ∀ v ∈ W, (∀ participants,
      store.getCommitteesBetweenSlots head startSlot endSlot = .ok participants →
        v ∈ participants) ∧ ∃ validator,
      balanceSource.validators.data[v.toNat]? = some validator ∧
        isActiveValidator validator (getCurrentEpoch balanceSource) = true) :
    stake (fun v => balanceAt balanceSource v.toNat) W ≤ weight.toNat := by
  by_cases empty : endSlot < startSlot
  · have : W = ∅ := Finset.eq_empty_of_forall_notMem fun v member => by
      have := (inside v member).1 ∅ (getCommitteesBetweenSlots_of_gt empty)
      simp at this
    simp [this, stake_empty]
  -- A whole epoch weighs the total active balance, which counts every active validator.
  by_cases whole : isFullValidatorSetCovered preset startSlot endSlot = .ok true
  · refine (stake_mono fun v member => List.mem_toFinset.mpr ?_).trans
      (stake_le_computeCommitteeWeightBetweenSlots_of_covered whole weightOk)
    obtain ⟨-, validator, atIndex, isActive⟩ := inside v member
    exact mem_getActiveValidatorIndices_of_isActiveAt
      (isActiveAt_eq_true_iff.mpr ⟨validator, atIndex, isActive⟩)
  have notGt : ¬startSlot > endSlot := empty
  simp only [computeCommitteeWeightBetweenSlots, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at weightOk
  obtain ⟨⟨_, members⟩, weightOk, rfl⟩ := weightOk
  simp only [computeCommitteeWeightAndMembers, notGt, ↓reduceIte, bind_ok_iff] at weightOk
  obtain ⟨covered, coveredOk, weightOk⟩ := weightOk
  cases covered
  · -- The members of the committees count once each, when active.
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok_iff, mapError_ok_iff] at weightOk
    obtain ⟨found, foundOk, active, activeOk, total, totalOk, final⟩ := weightOk
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at final
    obtain ⟨rfl, -⟩ := final
    refine stake_le_of_getTotalBalance totalOk fun v member => ?_
    obtain ⟨inParticipants, validator, atIndex, isActive⟩ := inside v member
    refine mem_filterM_ok_of_test activeOk
      (Std.TreeSet.mem_toList.mpr (inParticipants found foundOk)) ?_
    simp [validatorAt, atIndex, isActive, bind, Except.bind, pure, Except.pure]
  · exact absurd coveredOk whole

/-- The store's weight of the committees of a range covers the stake of their active members.

A member weighs its effective balance in the source of balances.

It is active when that source holds it, active in the epoch of that source. -/
theorem stake_le_computeCommitteeWeightBetweenSlots {head : Root}
    {balanceSource : BeaconState preset fork} {startSlot endSlot : Slot}
    {participants : Std.TreeSet ValidatorIndex} {weight : Gwei} {W : Finset ValidatorIndex}
    (participantsOk : store.getCommitteesBetweenSlots head startSlot endSlot = .ok participants)
    (weightOk : store.computeCommitteeWeightBetweenSlots head balanceSource startSlot endSlot =
      .ok weight)
    (inside : ∀ v ∈ W, v ∈ participants ∧ ∃ validator,
      balanceSource.validators.data[v.toNat]? = some validator ∧
        isActiveValidator validator (getCurrentEpoch balanceSource) = true) :
    stake (fun v => balanceAt balanceSource v.toNat) W ≤ weight.toNat := by
  refine stake_le_computeCommitteeWeightBetweenSlots_of_reads weightOk fun v member => ?_
  refine ⟨fun read readOk => ?_, (inside v member).2⟩
  rw [participantsOk, Except.ok.injEq] at readOk
  exact readOk ▸ (inside v member).1

/-- The store's votes for any of a list of nodes from the committees of a range are a stake.

It is the stake of the voters: the members of those committees whose votes the store counts.

The source of balances holds a voter, not slashed and active in the epoch of that source.

The store does not know a voter to equivocate.

The latest message of a voter supports one of the nodes, not a descendant of one.

A validator weighs its effective balance in the source of balances.

With the nodes of the parent, this is the observed weight of arXiv 2405.00549v4, Definition 5. -/
theorem exists_stake_of_getNodeSupportBetweenSlots {head : Root}
    {balanceSource : BeaconState preset fork} {nodes : List ForkChoiceNode}
    {startSlot endSlot : Slot} {support : Gwei}
    (supportOk :
      store.getNodeSupportBetweenSlots head balanceSource nodes startSlot endSlot = .ok support) :
    ∃ (participants : Std.TreeSet ValidatorIndex) (voters : Finset ValidatorIndex),
      store.getCommitteesBetweenSlots head startSlot endSlot = .ok participants ∧
      (∀ v, v ∈ voters ↔ v ∈ participants ∧
        (∃ validator, balanceSource.validators.data[v.toNat]? = some validator ∧
          validator.slashed = false ∧
          isActiveValidator validator (getCurrentEpoch balanceSource) = true) ∧
        v ∉ store.equivocatingIndices ∧
        ∃ message supported, store.latestMessages[v]? = some message ∧
          store.getSupportedNode message = .ok supported ∧ supported ∈ nodes) ∧
      stake (fun v => balanceAt balanceSource v.toNat) voters = support.toNat := by
  classical
  simp only [getNodeSupportBetweenSlots, bind_ok_iff] at supportOk
  obtain ⟨participants, participantsOk, counted, countedOk, summed⟩ := supportOk
  -- The filter keeps the members of the committees that the source holds, not slashed and active.
  have kept : ∀ v, v ∈ counted ↔ v ∈ participants ∧
      ∃ validator, balanceSource.validators.data[v.toNat]? = some validator ∧
        validator.slashed = false ∧
        isActiveValidator validator (getCurrentEpoch balanceSource) = true := by
    intro v
    constructor
    · intro member
      have passes := passes_of_mem_filterM_ok countedOk member
      simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Bool.and_eq_true,
        Bool.not_eq_true'] at passes
      obtain ⟨validator, found, unslashed, isActive⟩ := passes
      exact ⟨Std.TreeSet.mem_toList.mp (mem_of_filterM_ok countedOk member), validator,
        validatorAt_ok_iff.mp found, unslashed, isActive⟩
    · rintro ⟨inside, validator, found, unslashed, isActive⟩
      refine mem_filterM_ok_of_test countedOk (Std.TreeSet.mem_toList.mpr inside) ?_
      simp [validatorAt, found, unslashed, isActive, bind, Except.bind, pure, Except.pure]
  have distinct : counted.Nodup :=
    (sublist_of_filterM_ok countedOk).nodup
      (Std.TreeSet.distinct_toList.imp Std.ReflCmp.ne_of_cmp_ne_eq)
  -- The vote of a validator counts when it is no known equivocator and supports one of the nodes.
  refine ⟨participants, counted.toFinset.filter fun v => v ∉ store.equivocatingIndices ∧
    ∃ message supported, store.latestMessages[v]? = some message ∧
      store.getSupportedNode message = .ok supported ∧ supported ∈ nodes, participantsOk,
    fun v => by simp only [Finset.mem_filter, List.mem_toFinset, kept, and_assoc], ?_⟩
  -- The sum adds the effective balance of each validator whose vote counts, and nothing else.
  rw [stake, Finset.sum_filter, List.sum_toFinset _ distinct]
  -- A vote that the store does not count adds nothing.
  have nothing : ∀ {value : Gwei} {counts : Prop} [Decidable counts] {balance : ℕ},
      (pure 0 : Except ForkChoiceError Gwei) = .ok value → ¬counts →
        value.toNat = if counts then balance else 0 := by
    intro value counts _ balance valueOk fails
    simp only [pure, Except.pure, Except.ok.injEq] at valueOk
    rw [ite_eq_right fails, ← valueOk]
    rfl
  refine (toNat_eq_of_sumGwei summed fun v _ value valueOk => ?_).symm
  split at valueOk
  · rename_i latest
    refine nothing valueOk ?_
    rintro ⟨-, other, -, otherLatest, -⟩
    simp [latest] at otherLatest
  · rename_i message latest
    simp only [bind_ok_iff] at valueOk
    obtain ⟨supported, supportedOk, valueOk⟩ := valueOk
    split at valueOk
    · rename_i passes
      rw [ite_eq_left ⟨passes.2, message, supported, latest, supportedOk, passes.1⟩]
      exact toNat_eq_balanceAt_of_effectiveBalance valueOk
    · rename_i fails
      refine nothing valueOk ?_
      rintro ⟨notKnown, other, node, otherLatest, nodeOk, among⟩
      rw [latest, Option.some.injEq] at otherLatest
      subst otherLatest
      rw [supportedOk, Except.ok.injEq] at nodeOk
      subst nodeOk
      exact fails ⟨among, notKnown⟩

/-- The store's votes for any of a list of nodes from the committees of a range weigh at most them.

The weight may be that of a range from the same slot that ends later. -/
theorem getNodeSupportBetweenSlots_le {head : Root} {balanceSource : BeaconState preset fork}
    {nodes : List ForkChoiceNode} {startSlot shortEnd endSlot : Slot} {support weight : Gwei}
    (supportOk :
      store.getNodeSupportBetweenSlots head balanceSource nodes startSlot shortEnd = .ok support)
    (weightOk : store.computeCommitteeWeightBetweenSlots head balanceSource startSlot endSlot =
      .ok weight)
    (le : shortEnd ≤ endSlot) : support.toNat ≤ weight.toNat := by
  -- The votes are the stake of voters that are active members of the committees.
  obtain ⟨short, voters, shortOk, members, staked⟩ :=
    exists_stake_of_getNodeSupportBetweenSlots supportOk
  rw [← staked]
  refine stake_le_computeCommitteeWeightBetweenSlots_of_reads weightOk fun v member => ?_
  obtain ⟨inside, ⟨validator, found, -, isActive⟩, -⟩ := (members v).mp member
  exact ⟨fun long longOk => mem_getCommitteesBetweenSlots_of_le shortOk longOk le inside,
    validator, found, isActive⟩

/-- The steps of a discount that the store computes, given the block and its parent.

When the block is at the slot after its parent, the discount is zero.

Otherwise the store makes a list of nodes.

From Gloas the list holds the pending node and the ancestor of the block at the parent's slot.

Before Gloas it holds the pending node only.

The discount is then the votes for those nodes, less the adversarial weight.

It is zero when the adversary is larger.

Both are over the slots from the one after the parent to the one before the block.

This is the store's form of the discount of arXiv 2405.00549v4, Definition 5. -/
theorem computeEmptySlotSupportDiscount_steps {head root : Root}
    {balanceSource : BeaconState preset fork} {firstSlot : Slot}
    {block parentBlock : BeaconBlock preset fork} {discount : Gwei}
    (blockOk : store.block root = .ok block)
    (parentOk : store.block block.parentRoot = .ok parentBlock)
    (firstOk : addChecked parentBlock.slot 1 = .ok firstSlot)
    (discountOk :
      store.computeEmptySlotSupportDiscount config head balanceSource root = .ok discount) :
    (firstSlot = block.slot ∧ discount = 0) ∨
      ∃ parentNodes lastSlot parentSupport adversary,
        (.glamsterdam ≤ fork → ∃ parentNode,
          store.getAncestor ⟨root, .pending⟩ parentBlock.slot = .ok parentNode ∧
            parentNodes = [⟨block.parentRoot, .pending⟩, parentNode]) ∧
        (¬.glamsterdam ≤ fork → parentNodes = [⟨block.parentRoot, .pending⟩]) ∧
        subChecked block.slot 1 = .ok lastSlot ∧
        store.getNodeSupportBetweenSlots head balanceSource parentNodes firstSlot lastSlot =
          .ok parentSupport ∧
        store.computeAdversarialWeight config head balanceSource firstSlot lastSlot =
          .ok adversary ∧
        discount = saturatingSub parentSupport adversary := by
  simp only [computeEmptySlotSupportDiscount, bind_ok_iff, mapError_ok_iff] at discountOk
  obtain ⟨b, bOk, pb, pbOk, f, fOk, discountOk⟩ := discountOk
  rw [blockOk, Except.ok.injEq] at bOk
  subst bOk
  rw [parentOk, Except.ok.injEq] at pbOk
  subst pbOk
  rw [firstOk, Except.ok.injEq] at fOk
  subst fOk
  split at discountOk
  · rename_i same
    simp only [pure, Except.pure, Except.ok.injEq] at discountOk
    exact .inl ⟨same, discountOk.symm⟩
  simp only [bind_ok_iff, mapError_ok_iff] at discountOk
  obtain ⟨parentNodes, nodesOk, lastEmpty, lastEmptyOk, parentSupport, supportOk, adversary,
    adversaryOk, final⟩ := discountOk
  simp only [pure, Except.pure, Except.ok.injEq] at final
  refine .inr ⟨parentNodes, lastEmpty, parentSupport, adversary, ?_, ?_, lastEmptyOk, supportOk,
    adversaryOk, final.symm⟩
  · intro gloas
    simp only [gloas, ↓reduceIte, bind_ok_iff] at nodesOk
    obtain ⟨parentNode, walk, listed⟩ := nodesOk
    simp only [pure, Except.pure, Except.ok.injEq] at listed
    exact ⟨parentNode, walk, listed.symm⟩
  · intro before
    simp only [before, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at nodesOk
    exact nodesOk.symm

/-- The store's discount of a block is at most the weight of the committees since its parent.

That needs the block at or before the current slot.

The discount counts the votes for the parent from the committees of the empty slots before it.

Those slots then lie in the range since the parent, which ends at the slot before the current one.
-/
theorem computeEmptySlotSupportDiscount_le {head root : Root}
    {balanceSource : BeaconState preset fork} {currentSlot firstSlot lastSlot : Slot}
    {block parentBlock : BeaconBlock preset fork} {maximumSupport discount : Gwei}
    (blockOk : store.block root = .ok block)
    (parentOk : store.block block.parentRoot = .ok parentBlock)
    (firstOk : addChecked parentBlock.slot 1 = .ok firstSlot)
    (lastOk : subChecked currentSlot 1 = .ok lastSlot)
    (maximumOk : store.computeCommitteeWeightBetweenSlots head balanceSource firstSlot lastSlot =
      .ok maximumSupport)
    (discountOk :
      store.computeEmptySlotSupportDiscount config head balanceSource root = .ok discount)
    (notFuture : block.slot ≤ currentSlot) : discount ≤ maximumSupport := by
  obtain ⟨-, zero⟩ | ⟨parentNodes, lastEmpty, parentSupport, adversary, -, -, lastEmptyOk,
    supportOk, -, final⟩ :=
      computeEmptySlotSupportDiscount_steps blockOk parentOk firstOk discountOk
  · subst zero
    exact UInt64.zero_le
  subst final
  rw [subChecked_ok_iff] at lastEmptyOk lastOk
  have le : lastEmpty ≤ lastSlot := by
    rw [UInt64.le_iff_toNat_le] at notFuture ⊢
    omega
  have bounded := getNodeSupportBetweenSlots_le supportOk maximumOk le
  rw [UInt64.le_iff_toNat_le, toNat_saturatingSub]
  omega

/-- The store's check on the discount of a block passes when the block is not in the future.

The block must be at or before the current slot, as the handler of blocks requires.

The threshold then adds the weight since the parent, the boost and twice the adversary.

It takes off the discount and halves the result, rounding down.

Only an addition or the doubling can still fail, by leaving 64 bits. -/
theorem computeSafetyThreshold_of_le_currentSlot {head root : Root}
    {balanceSource : BeaconState preset fork} {currentSlot firstSlot lastSlot : Slot}
    {block parentBlock : BeaconBlock preset fork}
    {proposerScore maximumSupport discount adversary : Gwei}
    (slotOk : store.getCurrentSlot config = .ok currentSlot)
    (blockOk : store.block root = .ok block)
    (parentOk : store.block block.parentRoot = .ok parentBlock)
    (boostOk : computeProposerScore config balanceSource = .ok proposerScore)
    (firstOk : addChecked parentBlock.slot 1 = .ok firstSlot)
    (lastOk : subChecked currentSlot 1 = .ok lastSlot)
    (weightOk : store.computeCommitteeWeightBetweenSlots head balanceSource firstSlot lastSlot =
      .ok maximumSupport)
    (discountOk :
      store.computeEmptySlotSupportDiscount config head balanceSource root = .ok discount)
    (adversaryOk : store.getAdversarialWeight config head balanceSource root = .ok adversary)
    (notFuture : block.slot ≤ currentSlot) :
    store.computeSafetyThreshold config head root balanceSource = (do
      let withBoost ← (addChecked maximumSupport proposerScore).mapError .arith
      let doubled ← (mulChecked 2 adversary).mapError .arith
      let bound ← (addChecked withBoost doubled).mapError .arith
      return (bound - discount) / 2) := by
  have le := computeEmptySlotSupportDiscount_le blockOk parentOk firstOk lastOk weightOk
    discountOk notFuture
  rw [computeSafetyThreshold_of_steps slotOk blockOk parentOk boostOk firstOk lastOk weightOk
    discountOk adversaryOk]
  simp only [gt_iff_lt, UInt64.not_lt.mpr le, ↓reduceIte]

/-- The Byzantine share of a set of validators is at most the store's adversary and equivocators.

The store's weight of a range of slots must cover the stake of the set.

The adversary and the equivocation score are those of that range.

Here the share is β of the stake, with β the threshold of the configuration, in percent.

Each effective balance in the set must be a whole number of 100 Gwei.

The store rounds the weight down to 100 Gwei for its adversary.

The rounded weight then still covers the stake of the set.

This supplies the Byzantine share in arXiv 2405.00549v4, Assumption 2 and Definition 5. -/
theorem threshold_mul_stake_le_of_computeAdversarialWeight {W : Finset ValidatorIndex}
    {head : Root} {balanceSource : BeaconState preset fork} {startSlot endSlot : Slot}
    {weight equivocation adversary : Gwei}
    (weightOk : store.computeCommitteeWeightBetweenSlots head balanceSource startSlot endSlot =
      .ok weight)
    (equivocationOk :
      store.getEquivocationScore head balanceSource startSlot endSlot = .ok equivocation)
    (rangeOk : store.computeAdversarialWeight config head balanceSource startSlot endSlot =
      .ok adversary)
    (weighed : stake (fun v => balanceAt balanceSource v.toNat) W ≤ weight.toNat)
    (aligned : ∀ v ∈ W, balanceAt balanceSource v.toNat % 100 = 0) :
    config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat *
        stake (fun v => balanceAt balanceSource v.toNat) W ≤
      100 * (adversary.toNat + equivocation.toNat) := by
  set w := fun v : ValidatorIndex => balanceAt balanceSource v.toNat
  have share := computeAdversarialWeight_share weightOk equivocationOk rangeOk
  -- The weight covers the stake of `W`, and that stake is a whole number of 100 Gwei.
  have whole : 100 ∣ stake w W := Finset.dvd_sum fun v member => Nat.dvd_of_mod_eq_zero
    (aligned v member)
  have cover : stake w W ≤ weight.toNat / 100 * 100 := by
    obtain ⟨k, hk⟩ := whole
    rw [hk] at weighed ⊢
    rw [Nat.mul_comm 100 k]
    exact Nat.mul_le_mul_right 100 ((Nat.le_div_iff_mul_le (by norm_num)).mpr
      (by rw [Nat.mul_comm]; exact weighed))
  -- The cover of the stake gives the cover of its Byzantine share.
  calc config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat * stake w W
      ≤ config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat * (weight.toNat / 100 * 100) :=
        Nat.mul_le_mul_left _ cover
    _ = 100 * (weight.toNat / 100 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat) := by ring
    _ ≤ 100 * (adversary.toNat + equivocation.toNat) := Nat.mul_le_mul_left _ share

/-- Lemmas 4 and 3 for a block that the store confirms: honest support above half of `Φ`.

Here `Φ` is the store's: the committee weight since the parent, plus the boost.

The discount is taken off it, and is added to the other side so that nothing truncates.

A validator weighs its effective balance in the source of balances.

The supporters are validators whose stake is the support of the block in the store.

The equivocators are validators whose stake is that of the known equivocators in the store.

Both lie in a set `W` of validators, whose stake the store's weight of a range of slots covers.

The supporters and the equivocators are apart.

The store's adversary over that range must be its adversary for the block.

The range that the store uses for the block is one such range.

Assume that the Byzantine validators hold at most β of the stake of `W`.

That is Assumption 2 when `W` is the set of active members of the committees of the range.

A range with a whole epoch may take as `W` every validator active in the source of balances.

Here β is the threshold of the configuration, in percent, and no equivocator is honest.

Assume also that each effective balance in `W` is a whole number of 100 Gwei.

The store rounds the weight down to 100 Gwei for its adversary, and this keeps β of `W` below it.

Effective balances are whole increments, and an increment is 10^9 Gwei in the presets.

The discount is at most the committee weight, since the store checks it. -/
theorem lt_two_mul_honest_support_of_isOneConfirmed {J : Set ValidatorIndex}
    [DecidablePred (· ∈ J)] {W supporters equivocators : Finset ValidatorIndex} {head root : Root}
    {balanceSource : BeaconState preset fork} {tally : VoteTally}
    {currentSlot firstSlot lastSlot startSlot : Slot} {block parentBlock : BeaconBlock preset fork}
    {proposerScore maximumSupport discount adversary threshold support weight equivocation : Gwei}
    (slotOk : store.getCurrentSlot config = .ok currentSlot)
    (blockOk : store.block root = .ok block)
    (parentOk : store.block block.parentRoot = .ok parentBlock)
    (boostOk : computeProposerScore config balanceSource = .ok proposerScore)
    (firstOk : addChecked parentBlock.slot 1 = .ok firstSlot)
    (lastOk : subChecked currentSlot 1 = .ok lastSlot)
    (maximumOk : store.computeCommitteeWeightBetweenSlots head balanceSource firstSlot lastSlot =
      .ok maximumSupport)
    (discountOk :
      store.computeEmptySlotSupportDiscount config head balanceSource root = .ok discount)
    (adversaryOk : store.getAdversarialWeight config head balanceSource root = .ok adversary)
    (rangeOk : store.computeAdversarialWeight config head balanceSource startSlot lastSlot =
      .ok adversary)
    (weightOk : store.computeCommitteeWeightBetweenSlots head balanceSource startSlot lastSlot =
      .ok weight)
    (equivocationOk :
      store.getEquivocationScore head balanceSource startSlot lastSlot = .ok equivocation)
    (thresholdOk : store.computeSafetyThreshold config head root balanceSource = .ok threshold)
    (supportOk : store.scoreFromTally tally ⟨root, .pending⟩ = .ok support)
    (confirmed : store.isOneConfirmed config head balanceSource tally root = .ok true)
    (supportStake : stake (fun v => balanceAt balanceSource v.toNat) supporters = support.toNat)
    (equivocationStake :
      stake (fun v => balanceAt balanceSource v.toNat) equivocators = equivocation.toNat)
    (supportersIn : supporters ⊆ W) (equivocatorsIn : equivocators ⊆ W)
    (weighed : stake (fun v => balanceAt balanceSource v.toNat) W ≤ weight.toNat)
    (aligned : ∀ v ∈ W, balanceAt balanceSource v.toNat % 100 = 0)
    (apart : Disjoint supporters equivocators) (dishonest : ∀ v ∈ equivocators, v ∉ J)
    (byzantine : ByzantineStakeAtMost (fun v => balanceAt balanceSource v.toNat) W J
      config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100) :
    maximumSupport.toNat + proposerScore.toNat <
      discount.toNat + 2 * stake (fun v => balanceAt balanceSource v.toNat)
        {v ∈ supporters | v ∈ J} := by
  set w := fun v : ValidatorIndex => balanceAt balanceSource v.toNat
  have bound := computeSafetyThreshold_bound slotOk blockOk parentOk boostOk firstOk lastOk
    maximumOk discountOk adversaryOk thresholdOk
  have above := threshold_lt_of_isOneConfirmed supportOk thresholdOk confirmed
  -- The store's adversary and equivocators cover the Byzantine share of `W`.
  have cover := threshold_mul_stake_le_of_computeAdversarialWeight weightOk equivocationOk rangeOk
    weighed aligned
  -- The discount is at most the committee weight, so nothing truncates.
  have small := UInt64.le_iff_toNat_le.mp (discount_le_of_computeSafetyThreshold slotOk blockOk
    parentOk boostOk firstOk lastOk maximumOk discountOk adversaryOk thresholdOk)
  have phi := Nat.sub_add_cancel (show discount.toNat ≤
    maximumSupport.toNat + proposerScore.toNat by omega)
  suffices maximumSupport.toNat + proposerScore.toNat - discount.toNat <
      2 * stake w {v ∈ supporters | v ∈ J} by omega
  generalize maximumSupport.toNat + proposerScore.toNat - discount.toNat = Φ at phi ⊢
  refine lt_two_mul_honest_support byzantine supportersIn equivocatorsIn apart dishonest ?_
  rw [supportStake, equivocationStake, Nat.mul_assoc 2]
  generalize config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat * stake w W = byzantineShare at cover ⊢
  omega

/-! ## The FFG indicators of the current target

The theorems above state the LMD-GHOST indicator of the rule, Definition 4 of the paper.

The rule also has two FFG indicators, which weigh the honest support against the active balance.

One stands for no checkpoint in conflict with the current target becoming justified.

It asks for more than a third of the balance.

It accepts at once when the target is the unrealized justified checkpoint of the store.

The other stands for the current target becoming justified, and asks for two thirds of it.

Here both are only tests of the support against the balance.

So reaching two thirds implies the weaker test, for a nonzero balance increment.
-/

/-- The checkpoint of an epoch in a chain carries that epoch and its checkpoint block. -/
private theorem getCheckpointForBlock_eq_ok_iff {root : Root} {epoch : Epoch}
    {checkpoint : Checkpoint} :
    store.getCheckpointForBlock root epoch = .ok checkpoint ↔
      ∃ block, store.getCheckpointBlock root epoch = .ok block ∧
        checkpoint = ⟨epoch, block⟩ := by
  simp only [getCheckpointForBlock, bind_ok_iff, pure, Except.pure, Except.ok.injEq]
  exact exists_congr fun _ => and_congr_right fun _ => eq_comm

/-- The current target is the checkpoint of the store's epoch in the chain of the head. -/
theorem getCurrentTarget_eq_ok_iff {head : Root} {checkpoint : Checkpoint} :
    store.getCurrentTarget config head = .ok checkpoint ↔
      ∃ epoch block, store.getCurrentStoreEpoch config = .ok epoch ∧
        store.getCheckpointBlock head epoch = .ok block ∧ checkpoint = ⟨epoch, block⟩ := by
  unfold getCurrentTarget
  rw [bind_ok_iff]
  simp only [getCheckpointForBlock_eq_ok_iff]
  constructor
  · rintro ⟨epoch, epochOk, block, blockOk, rfl⟩
    exact ⟨epoch, block, epochOk, blockOk, rfl⟩
  · rintro ⟨epoch, block, epochOk, blockOk, rfl⟩
    exact ⟨epoch, epochOk, block, blockOk, rfl⟩

/-- The current target carries the current epoch of the store. -/
theorem epoch_eq_of_getCurrentTarget {head : Root} {epoch : Epoch} {checkpoint : Checkpoint}
    (epochOk : store.getCurrentStoreEpoch config = .ok epoch)
    (targetOk : store.getCurrentTarget config head = .ok checkpoint) :
    checkpoint.epoch = epoch := by
  obtain ⟨epoch', block, epochOk', -, rfl⟩ := getCurrentTarget_eq_ok_iff.mp targetOk
  rw [epochOk] at epochOk'
  exact (Except.ok.inj epochOk').symm

/-- The two-thirds test accepts exactly when three times the support reaches twice the balance.

Both products must fit in 64 bits.

The balance is the total active balance of the state of the head, pulled up to the current epoch.
-/
theorem willCurrentTargetBeJustified_eq_ok_true_iff {head : Root} :
    store.willCurrentTargetBeJustified config head = .ok true ↔
      ∃ state total support twice thrice,
        store.getPulledUpHeadState config head = .ok state ∧
        getTotalActiveBalance state = .ok total ∧
        store.computeHonestFfgSupportForCurrentTarget config head = .ok support ∧
        mulChecked 2 total = .ok twice ∧ mulChecked 3 support = .ok thrice ∧
        twice ≤ thrice := by
  simp [willCurrentTargetBeJustified, bind_ok_iff, mapError_ok_iff, pure, Except.pure]

/-- When the two-thirds test accepts, three times the support reaches twice the balance. -/
theorem two_mul_le_three_mul_of_willCurrentTargetBeJustified {head : Root}
    {state : BeaconState preset fork} {total support : Gwei}
    (stateOk : store.getPulledUpHeadState config head = .ok state)
    (totalOk : getTotalActiveBalance state = .ok total)
    (supportOk : store.computeHonestFfgSupportForCurrentTarget config head = .ok support)
    (justified : store.willCurrentTargetBeJustified config head = .ok true) :
    2 * total.toNat ≤ 3 * support.toNat := by
  obtain ⟨state', total', support', twice, thrice, stateOk', totalOk', supportOk', twiceOk,
    thriceOk, le⟩ := willCurrentTargetBeJustified_eq_ok_true_iff.mp justified
  obtain rfl : state' = state := by rw [stateOk] at stateOk'; exact (Except.ok.inj stateOk').symm
  obtain rfl : total' = total := by rw [totalOk] at totalOk'; exact (Except.ok.inj totalOk').symm
  obtain rfl : support' = support := by
    rw [supportOk] at supportOk'
    exact (Except.ok.inj supportOk').symm
  obtain ⟨-, twiceVal⟩ := mulChecked_ok_iff.mp twiceOk
  obtain ⟨-, thriceVal⟩ := mulChecked_ok_iff.mp thriceOk
  have two : (2 : Gwei).toNat = 2 := rfl
  have three : (3 : Gwei).toNat = 3 := rfl
  have above := UInt64.le_iff_toNat_le.mp le
  rw [twiceVal, thriceVal, two, three] at above
  exact above

/-- The one-third test accepts exactly in two cases.

The current target is the unrealized justified checkpoint.

Or three times the support exceeds the balance, and that product fits in 64 bits.
-/
theorem willNoConflictingCheckpointBeJustified_eq_ok_true_iff {head : Root} {target : Checkpoint}
    (targetOk : store.getCurrentTarget config head = .ok target) :
    store.willNoConflictingCheckpointBeJustified config head = .ok true ↔
      target = store.unrealizedJustifiedCheckpoint ∨
        ∃ state total support thrice,
          store.getPulledUpHeadState config head = .ok state ∧
          getTotalActiveBalance state = .ok total ∧
          store.computeHonestFfgSupportForCurrentTarget config head = .ok support ∧
          mulChecked 3 support = .ok thrice ∧ total < thrice := by
  by_cases unrealized : target = store.unrealizedJustifiedCheckpoint
  · simp [willNoConflictingCheckpointBeJustified, targetOk, unrealized, bind, Except.bind, pure,
      Except.pure]
  · simp [willNoConflictingCheckpointBeJustified, targetOk, unrealized, bind_ok_iff,
      mapError_ok_iff, pure, Except.pure]

/-- The support of the current target is computed only once that target is. -/
private theorem exists_getCurrentTarget_of_support {head : Root} {support : Gwei}
    (supportOk : store.computeHonestFfgSupportForCurrentTarget config head = .ok support) :
    ∃ target, store.getCurrentTarget config head = .ok target := by
  simp only [computeHonestFfgSupportForCurrentTarget, getCurrentTargetScore, bind_ok_iff]
    at supportOk
  obtain ⟨-, -, -, -, -, -, -, ⟨target, targetOk, -⟩, -⟩ := supportOk
  exact ⟨target, targetOk⟩

/-- When the two-thirds test accepts, the one-third test accepts too.

The balance increment is assumed nonzero.

The total active balance is at least one increment, so it is nonzero too.

Two thirds of a nonzero balance is above a third of it.
-/
theorem willNoConflictingCheckpointBeJustified_of_willCurrentTargetBeJustified {head : Root}
    (positive : preset.EFFECTIVE_BALANCE_INCREMENT ≠ 0)
    (justified : store.willCurrentTargetBeJustified config head = .ok true) :
    store.willNoConflictingCheckpointBeJustified config head = .ok true := by
  obtain ⟨state, total, support, -, thrice, stateOk, totalOk, supportOk, -, thriceOk, -⟩ :=
    willCurrentTargetBeJustified_eq_ok_true_iff.mp justified
  obtain ⟨target, targetOk⟩ := exists_getCurrentTarget_of_support supportOk
  refine (willNoConflictingCheckpointBeJustified_eq_ok_true_iff targetOk).mpr
    (.inr ⟨state, total, support, thrice, stateOk, totalOk, supportOk, thriceOk, ?_⟩)
  have above := two_mul_le_three_mul_of_willCurrentTargetBeJustified stateOk totalOk supportOk
    justified
  have least := UInt64.le_iff_toNat_le.mp (le_getTotalBalance (getTotalActiveBalance_ok totalOk))
  have nonzero : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    Nat.pos_of_ne_zero fun h => positive (UInt64.toNat_inj.mp (by simpa using h))
  obtain ⟨-, thriceVal⟩ := mulChecked_ok_iff.mp thriceOk
  have three : (3 : Gwei).toNat = 3 := rfl
  refine UInt64.lt_iff_toNat_lt.mpr ?_
  rw [thriceVal, three]
  omega

end Store

end EthLib.Consensus
