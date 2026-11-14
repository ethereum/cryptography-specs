module

public import EthLib.Consensus.Proofs.ForkChoice.CommitteeAgreement
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Sets
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Supporters

/-!
# Proofs: each supporter of a tested block is in the committees that the rule reads

Lemmas 4 and 3 of [arXiv 2405.00549v4][fcr] need each supporter of the block in a set `W`.

For a range of the adversary with part of an epoch, `W` is the active members of its committees.

The rule reads those committees in the state of the head.

The store checks each vote against the committees in the state of its target.

A range without a whole epoch ends at most one epoch after its start.

So the vote of each supporter is at most one epoch after the block.

The head state is at or before the current slot, so at most one epoch after the vote.

When the head descends from the block, the two states then agree on the committees of the vote.

So each supporter is a member of the committees that the rule reads, with no assumption.

[fcr]: https://arxiv.org/abs/2405.00549v4
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models Models.ForkChoice

variable {preset : Preset} {fork : Fork} {config : Config}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {store : Store preset fork}

/-- In a range of slots without a whole epoch, each slot is at most one epoch after the start.

So is the slot after the end. -/
theorem epochAtSlot_le_of_not_isFullValidatorSetCovered {startSlot endSlot slot : Slot}
    (partialRange : isFullValidatorSetCovered preset startSlot endSlot = .ok false)
    (le : slot.toNat ≤ endSlot.toNat + 1) :
    (computeEpochAtSlot preset slot).toNat ≤ (computeEpochAtSlot preset startSlot).toNat + 1 := by
  simp only [isFullValidatorSetCovered, bind_ok_iff, mapError_ok_iff] at partialRange
  obtain ⟨afterFirst, first, lastOfFirst, last, afterEnd, after, notLater⟩ := partialRange
  have one : (1 : UInt64).toNat = 1 := rfl
  rw [Uint64.addChecked_ok_iff] at first after
  rw [Uint64.subChecked_ok_iff] at last
  rw [one] at last after
  have notLater : (afterEnd / preset.SLOTS_PER_EPOCH).toNat ≤
      (lastOfFirst / preset.SLOTS_PER_EPOCH).toNat := by
    simpa [pure, Except.pure, computeEpochAtSlot, UInt64.lt_iff_toNat_lt] using notLater
  rw [UInt64.toNat_div, UInt64.toNat_div] at notLater
  simp only [computeEpochAtSlot, UInt64.toNat_div]
  rcases Nat.eq_zero_or_pos preset.SLOTS_PER_EPOCH.toNat with zero | positive
  · simp [zero]
  calc slot.toNat / preset.SLOTS_PER_EPOCH.toNat
      ≤ afterEnd.toNat / preset.SLOTS_PER_EPOCH.toNat := Nat.div_le_div_right (by omega)
    _ ≤ lastOfFirst.toNat / preset.SLOTS_PER_EPOCH.toNat := notLater
    _ ≤ (startSlot.toNat + preset.SLOTS_PER_EPOCH.toNat) / preset.SLOTS_PER_EPOCH.toNat :=
      Nat.div_le_div_right (by omega)
    _ = startSlot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1 := Nat.add_div_right _ positive

/-- Each supporter of a block is a member of the committees that the rule reads for a range.

The range starts at or before the slot of the block.

It ends at the last slot before the current one, and holds no whole epoch.

The rule reads the committees in the state of the head, which descends from the block.

The store is built with one setting of the checks, and the anchor block is not after its state.

Both lookaheads of the seed are at least one epoch.

The ring of mixes is longer than the minimum lookahead plus two epochs. -/
theorem Store.ForwardReachableWith.supportersOf_mem_committees {checks : SignatureChecks}
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {head root : Root} {block : BeaconBlock preset fork} {balanceSource : BeaconState preset fork}
    {currentSlot startSlot lastSlot : Slot} {participants : Std.TreeSet ValidatorIndex}
    (slotOk : store.getCurrentSlot config = .ok currentSlot)
    (blockOk : store.block root = .ok block) (startLe : startSlot ≤ block.slot)
    (lastOk : subChecked currentSlot 1 = .ok lastSlot)
    (descends : store.isAncestor ⟨head, .pending⟩ ⟨root, .pending⟩ = .ok true)
    (partialRange : isFullValidatorSetCovered preset startSlot lastSlot = .ok false)
    (participantsOk : store.getCommitteesBetweenSlots head startSlot lastSlot = .ok participants) :
    ∀ v ∈ store.supportersOf balanceSource ⟨root, .pending⟩, v ∈ participants := by
  intro v supporter
  have found : store.blocks[root]? = some block := Store.block_ok_iff.mp blockOk
  -- The vote of the supporter comes from an attestation of a slot of the range.
  obtain ⟨attestation, latest, origin, low, high⟩ :=
    reached.forwardReachable.votesHaveOrigins.slot_mem_range_of_mem_supportersOf blockOk startLe
      slotOk lastOk supporter
  -- It votes for a node that descends from the block.
  obtain ⟨message, voted, latest', -, supported, voteDescends⟩ :=
    store.exists_of_voteCountsFor (store.voteCountsFor_of_mem_supportersOf supporter)
  rw [latest, Option.some.injEq] at latest'
  subst latest'
  have votedRoot : voted.root = attestation.data.beaconBlockRoot :=
    Store.getSupportedNode_root supported
  -- The head has a state, at or before the current slot.
  obtain ⟨headBlock, headBlockFound, -⟩ := Store.slot_le_of_isAncestor found descends
  obtain ⟨headState, headFound, -, -⟩ := reached.reachable.blockStatesFromParents headBlockFound
  have headLe := reached.forwardReachable.slot_le_of_blockState_of_getCurrentSlot headFound
    slotOk
  -- The vote is at most one epoch after the block, and the head state one epoch after the vote.
  obtain ⟨lastLe, lastValue⟩ := subChecked_ok_iff.mp lastOk
  have one : (1 : UInt64).toNat = 1 := rfl
  rw [one] at lastLe lastValue
  rw [UInt64.le_iff_toNat_le] at low high startLe headLe
  have voteNear := epochAtSlot_le_of_not_isFullValidatorSetCovered partialRange
    (slot := attestation.data.slot) (by omega)
  have currentNear := epochAtSlot_le_of_not_isFullValidatorSetCovered partialRange
    (slot := currentSlot) (by omega)
  have startBlock : (computeEpochAtSlot preset startSlot).toNat ≤
      (computeEpochAtSlot preset block.slot).toNat := by
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_le_div_right startLe
  have startVote : (computeEpochAtSlot preset startSlot).toNat ≤
      (computeEpochAtSlot preset attestation.data.slot).toNat := by
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_le_div_right low
  have headCurrent : (getCurrentEpoch headState).toNat ≤
      (computeEpochAtSlot preset currentSlot).toNat := by
    rw [getCurrentEpoch_toNat]
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_le_div_right headLe
  -- The target state and the head state agree on the committees of the vote.
  obtain ⟨targetState, index, committee, targetFound, below, committeeOk, member⟩ :=
    origin.exists_mem_committee
  obtain ⟨kept, count⟩ := reached.committeesKept_of_voteOrigin anchorSlot minLookahead
    maxLookahead (by omega) found descends origin votedRoot voteDescends (by omega) targetFound
    headFound (by omega)
  rw [← UInt64.le_iff_toNat_le] at low high
  exact Store.mem_getCommitteesBetweenSlots participantsOk low high
    (Store.blockState_ok_iff.mpr headFound) (count ▸ below)
    ((kept _ _ rfl).trans committeeOk) member

/-- Lemmas 4 and 3 for a confirmed block whose range of the adversary holds part of an epoch.

Here `W` is the active members of the committees of the range, as in Section 2.1 of the paper.

The head descends from the block.

Each supporter is then a member of those committees, which the theorem proves, not assumes.

A validator weighs its effective balance in the source of balances, and is active there.

The supporters are the validators that the tally of that source counts for the block.

The range starts at or before the slot of the block, and ends at the slot before the current one.

Its adversary must be the adversary of the block.

The range that the rule uses for the block is one such range.

Assume that the Byzantine validators hold at most β of the stake of `W`, Assumption 2.

Here β is the threshold of the configuration, in percent.

Assume that no known equivocator is honest.

Assume also that each effective balance of the source is a whole number of increments.

An increment must be a whole number of 100 Gwei, as 10^9 Gwei in the presets is.

The registry of the source of balances must stay within the limit of the preset.

The store must be built with one setting of the checks, and the anchor block not after its state.

Both lookaheads of the seed must be at least one epoch.

The ring of mixes must be longer than the minimum lookahead plus two epochs. -/
theorem Store.ForwardReachableWith.lt_two_mul_honest_supportersOf_of_partialRange
    {checks : SignatureChecks} {J : Set ValidatorIndex} [DecidablePred (· ∈ J)]
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {head root : Root} {balanceSource : BeaconState preset fork}
    {currentSlot firstSlot lastSlot startSlot : Slot} {block parentBlock : BeaconBlock preset fork}
    {participants : Std.TreeSet ValidatorIndex}
    {proposerScore maximumSupport discount adversary : Gwei}
    (within : balanceSource.RegistryWithinLimit)
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
    (startLe : startSlot ≤ block.slot)
    (rangeOk : store.computeAdversarialWeight config head balanceSource startSlot lastSlot =
      .ok adversary)
    (partialRange : isFullValidatorSetCovered preset startSlot lastSlot = .ok false)
    (participantsOk : store.getCommitteesBetweenSlots head startSlot lastSlot = .ok participants)
    (descends : store.isAncestor ⟨head, .pending⟩ ⟨root, .pending⟩ = .ok true)
    (confirmed : store.isOneConfirmed config head balanceSource (store.tallyVotes balanceSource)
      root = .ok true)
    (aligned : EffectiveBalancesAligned balanceSource)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (dishonest : ∀ v ∈ store.equivocatingIndices, v ∉ J)
    (byzantine : ByzantineStakeAtMost (fun v => balanceAt balanceSource v.toNat)
      (Store.activeMembers balanceSource participants) J
      config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100) :
    maximumSupport.toNat + proposerScore.toNat <
      discount.toNat + 2 * stake (fun v => balanceAt balanceSource v.toNat)
        {v ∈ store.supportersOf balanceSource ⟨root, .pending⟩ | v ∈ J} :=
  Store.lt_two_mul_honest_supportersOf_of_isOneConfirmed within slotOk blockOk parentOk boostOk
    firstOk lastOk maximumOk discountOk adversaryOk rangeOk participantsOk confirmed
    (reached.supportersOf_mem_committees anchorSlot minLookahead maxLookahead ring slotOk
      blockOk startLe lastOk descends partialRange participantsOk)
    aligned increment dishonest byzantine

end EthLib.Consensus
