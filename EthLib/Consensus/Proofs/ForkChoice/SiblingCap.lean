module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Committees
public import EthLib.Consensus.Proofs.ForkChoice.Ghost

/-!
# Proofs: two sibling blocks weigh at most what the fast confirmation rule counts

The proof of Lemma 2 of [arXiv 2405.00549v4][fcr], Appendix A.1, bounds two sibling blocks together.

Take a block `c` with parent `p`, and another child `c'` of `p`.

Their supporters voted at or after the slot of `c` or `c'`, so after `p`, and before now.

The rule counts the committees of the slots from the one after `p` to the one before now.

A range with a whole epoch counts every active validator.

A range without a whole epoch counts the members of its committees, read in the state of the head.

Each supporter of `c` or `c'` is one of them, since the head descends from `p`.

That holds for a sibling off the chain of the head too.

The supporters of `c` and `c'` are disjoint, and the boost counts once for both.

So both weigh at most that count plus the score of the boost.

The votes for `p` from the empty slots before `c` support neither block.

So they come off the count, and they bound the discount of the rule.

All of this is before Gloas, with the weights of the model of the store.

[fcr]: https://arxiv.org/abs/2405.00549v4
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models Models.ForkChoice

variable {preset : Preset} {fork : Fork} {config : Config}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {store : Store preset fork}

/-- A slot of a range without a whole epoch is at most one epoch after the slot before the range.

So is the slot after the end. -/
theorem epochAtSlot_le_of_not_isFullValidatorSetCovered_of_addChecked
    {before startSlot endSlot slot : Slot} (startOk : addChecked before 1 = .ok startSlot)
    (partialRange : isFullValidatorSetCovered preset startSlot endSlot = .ok false)
    (le : slot.toNat ≤ endSlot.toNat + 1) :
    (computeEpochAtSlot preset slot).toNat ≤ (computeEpochAtSlot preset before).toNat + 1 := by
  simp only [isFullValidatorSetCovered, bind_ok_iff, mapError_ok_iff] at partialRange
  obtain ⟨afterFirst, first, lastOfFirst, last, afterEnd, after, notLater⟩ := partialRange
  have one : (1 : UInt64).toNat = 1 := rfl
  rw [Uint64.addChecked_ok_iff] at first after startOk
  rw [Uint64.subChecked_ok_iff] at last
  rw [one] at last after startOk
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
    _ ≤ (before.toNat + preset.SLOTS_PER_EPOCH.toNat) / preset.SLOTS_PER_EPOCH.toNat :=
      Nat.div_le_div_right (by omega)
    _ = before.toNat / preset.SLOTS_PER_EPOCH.toNat + 1 := Nat.add_div_right _ positive

namespace Store

variable {lower : store.ParentsBelow}

/-- Before Gloas, a known block that descends from another in the tree descends in the store.

The other block must be known too. -/
theorem isAncestor_of_blockTree_ancestor (before : fork < .glamsterdam) {root ancestor : Root}
    {block ancestorBlock : BeaconBlock preset fork} (found : store.blocks[root]? = some block)
    (ancestorFound : store.blocks[ancestor]? = some ancestorBlock)
    (above : (blockTree lower).Ancestor (some ancestor) (some root)) :
    store.isAncestor ⟨root, .pending⟩ ⟨ancestor, .pending⟩ = .ok true := by
  obtain ⟨n, chain⟩ := above
  induction n generalizing root block with
  | zero =>
    cases chain
    have later : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
    simp only [isAncestor, later, ↓reduceIte, bind, Except.bind, block_ok_iff.mpr ancestorFound,
      getAncestor_of_le (node := ⟨ancestor, .pending⟩) ancestorFound (UInt64.le_refl _), pure,
      Except.pure, beq_self_eq_true]
  | succ n ih =>
    rw [Function.iterate_succ_apply, blockTree_parent_of found] at chain
    cases parentFound : store.blocks[block.parentRoot]? with
    | none =>
      have := (show (blockTree lower).Ancestor (some ancestor) (some block.parentRoot) from
        ⟨n, chain⟩).height_le
      rw [blockTree_height_of ancestorFound] at this
      simp [blockTree, treeHeight, parentFound] at this
    | some parent =>
      exact isAncestor_of_parent before found parentFound (lower _ block parent found parentFound)
        (ih parentFound chain)

end Store

/-- On a range that is not empty, the store's check of a whole epoch returns false unless true.

That holds when the store computes the weight of the committees of the range. -/
private theorem isFullValidatorSetCovered_eq_false {head : Root} {state : BeaconState preset fork}
    {startSlot endSlot : Slot} {weight : Gwei}
    (weightOk : store.computeCommitteeWeightBetweenSlots head state startSlot endSlot = .ok weight)
    (notEmpty : startSlot ≤ endSlot)
    (whole : ¬ isFullValidatorSetCovered preset startSlot endSlot = .ok true) :
    isFullValidatorSetCovered preset startSlot endSlot = .ok false := by
  have notGt : ¬startSlot > endSlot := UInt64.not_lt.mpr notEmpty
  simp only [Store.computeCommitteeWeightBetweenSlots, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at weightOk
  obtain ⟨⟨_, members⟩, weightOk, rfl⟩ := weightOk
  simp only [Store.computeCommitteeWeightAndMembers, notGt, ↓reduceIte, bind_ok_iff] at weightOk
  obtain ⟨covered, coveredOk, -⟩ := weightOk
  cases covered
  · exact coveredOk
  · exact absurd coveredOk whole

/-- The store's weight of the committees of a range covers the stake of a set of validators.

Each member of the set must be active in the source of balances.

When the range holds no whole epoch, each must be in every set of members read for the range. -/
private theorem stake_le_of_active_of_reads {head : Root} {state : BeaconState preset fork}
    {startSlot endSlot : Slot} {weight : Gwei} {W : Finset ValidatorIndex}
    (weightOk : store.computeCommitteeWeightBetweenSlots head state startSlot endSlot = .ok weight)
    (active : ∀ v ∈ W, ∃ validator, state.validators.data[v.toNat]? = some validator ∧
      isActiveValidator validator (getCurrentEpoch state) = true)
    (reads : ¬ isFullValidatorSetCovered preset startSlot endSlot = .ok true → ∀ v ∈ W,
      ∀ participants, store.getCommitteesBetweenSlots head startSlot endSlot = .ok participants →
        v ∈ participants) :
    stake (fun v => balanceAt state v.toNat) W ≤ weight.toNat := by
  by_cases whole : isFullValidatorSetCovered preset startSlot endSlot = .ok true
  · refine (stake_mono fun v member => List.mem_toFinset.mpr ?_).trans
      (Store.stake_le_computeCommitteeWeightBetweenSlots_of_covered whole weightOk)
    obtain ⟨validator, atIndex, isActive⟩ := active v member
    exact mem_getActiveValidatorIndices_of_isActiveAt
      (isActiveAt_eq_true_iff.mpr ⟨validator, atIndex, isActive⟩)
  · exact Store.stake_le_computeCommitteeWeightBetweenSlots_of_reads weightOk
      fun v member => ⟨reads whole v member, active v member⟩

/-- A vote in the subtree of a child of a known parent is from a slot after the parent, before now.

Those are the slots from the one after the parent to the one before the current slot. -/
private theorem slot_mem_range_of_voteOrigin (lower : store.ParentsBelow)
    {child parentRoot : Root} {childBlock parentBlock : BeaconBlock preset fork}
    {currentSlot firstSlot lastSlot : Slot} {v : ValidatorIndex}
    {attestation : Attestation preset fork}
    (parentFound : store.blocks[parentRoot]? = some parentBlock)
    (childFound : store.blocks[child]? = some childBlock)
    (childParent : childBlock.parentRoot = parentRoot)
    (slotOk : store.getCurrentSlot config = .ok currentSlot)
    (firstOk : addChecked parentBlock.slot 1 = .ok firstSlot)
    (lastOk : subChecked currentSlot 1 = .ok lastSlot)
    (origin : store.VoteOrigin config v attestation)
    (above : (Store.blockTree lower).Ancestor (some child)
      (some attestation.data.beaconBlockRoot)) :
    firstSlot ≤ attestation.data.slot ∧ attestation.data.slot ≤ lastSlot := by
  obtain ⟨voted, votedFound, votedLe⟩ := origin.voted
  have heights := above.height_le
  rw [Store.blockTree_height_of childFound, Store.blockTree_height_of votedFound] at heights
  have parentLower := lower _ childBlock parentBlock childFound
    (by rw [childParent]; exact parentFound)
  obtain ⟨current, currentOk, past⟩ := origin.past
  rw [slotOk] at currentOk
  cases currentOk
  rw [Uint64.addChecked_ok_iff] at firstOk
  obtain ⟨le, eq⟩ := subChecked_ok_iff.mp lastOk
  rw [UInt64.le_iff_toNat_le, UInt64.le_iff_toNat_le]
  have := UInt64.lt_iff_toNat_lt.mp past
  have := UInt64.lt_iff_toNat_lt.mp parentLower
  have := UInt64.le_iff_toNat_le.mp votedLe
  simp only [UInt64.toNat_one] at le eq firstOk
  omega

/-- A vote in the subtree of a child of a known block is from a member of the committees read.

The range starts after that block, ends before the current slot and holds no whole epoch.

The rule reads its committees in the state of the head, which descends from that block.

The store must be built with one setting of the checks, and the anchor block not after its state.

Both lookaheads of the seed must be at least one epoch.

The ring of mixes must be longer than the minimum lookahead plus two epochs. -/
private theorem mem_committees_of_voteOrigin {checks : SignatureChecks}
    (before : fork < .glamsterdam) (lower : store.ParentsBelow)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {head child parentRoot : Root} {childBlock parentBlock : BeaconBlock preset fork}
    {currentSlot firstSlot lastSlot : Slot} {participants : Std.TreeSet ValidatorIndex}
    {v : ValidatorIndex} {attestation : Attestation preset fork}
    (parentFound : store.blocks[parentRoot]? = some parentBlock)
    (childFound : store.blocks[child]? = some childBlock)
    (childParent : childBlock.parentRoot = parentRoot)
    (descends : store.isAncestor ⟨head, .pending⟩ ⟨parentRoot, .pending⟩ = .ok true)
    (slotOk : store.getCurrentSlot config = .ok currentSlot)
    (firstOk : addChecked parentBlock.slot 1 = .ok firstSlot)
    (lastOk : subChecked currentSlot 1 = .ok lastSlot)
    (partialRange : isFullValidatorSetCovered preset firstSlot lastSlot = .ok false)
    (participantsOk : store.getCommitteesBetweenSlots head firstSlot lastSlot = .ok participants)
    (origin : store.VoteOrigin config v attestation)
    (above : (Store.blockTree lower).Ancestor (some child)
      (some attestation.data.beaconBlockRoot)) :
    v ∈ participants := by
  obtain ⟨low, high⟩ := slot_mem_range_of_voteOrigin lower parentFound childFound childParent
    slotOk firstOk lastOk origin above
  obtain ⟨voted, votedFound, -⟩ := origin.voted
  have isChild : (Store.blockTree lower).IsChild (some child) (some parentRoot) :=
    Store.blockTree_isChild_iff.mpr ⟨childBlock, childFound, childParent⟩
  have voteDescends := Store.isAncestor_of_blockTree_ancestor (lower := lower) before votedFound
    parentFound (isChild.ancestor.trans above)
  -- The head has a state, at or before the current slot.
  obtain ⟨headBlock, headBlockFound, -⟩ := Store.slot_le_of_isAncestor parentFound descends
  obtain ⟨headState, headFound, -, -⟩ := reached.reachable.blockStatesFromParents headBlockFound
  have headLe := reached.forwardReachable.slot_le_of_blockState_of_getCurrentSlot headFound
    slotOk
  -- The vote and the head state are each at most one epoch after the parent.
  have firstOk' := firstOk
  rw [Uint64.addChecked_ok_iff] at firstOk'
  obtain ⟨lastLe, lastValue⟩ := subChecked_ok_iff.mp lastOk
  have one : (1 : UInt64).toNat = 1 := rfl
  rw [one] at lastLe lastValue firstOk'
  rw [UInt64.le_iff_toNat_le] at low high headLe
  have voteNear := epochAtSlot_le_of_not_isFullValidatorSetCovered_of_addChecked firstOk
    partialRange (slot := attestation.data.slot) (by omega)
  have currentNear := epochAtSlot_le_of_not_isFullValidatorSetCovered_of_addChecked firstOk
    partialRange (slot := currentSlot) (by omega)
  have parentVote : (computeEpochAtSlot preset parentBlock.slot).toNat ≤
      (computeEpochAtSlot preset attestation.data.slot).toNat := by
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_le_div_right (by omega)
  have headCurrent : (getCurrentEpoch headState).toNat ≤
      (computeEpochAtSlot preset currentSlot).toNat := by
    rw [getCurrentEpoch_toNat]
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_le_div_right headLe
  -- The target state and the head state agree on the committees of the vote.
  obtain ⟨targetState, index, committee, targetFound, below, committeeOk, member⟩ :=
    origin.exists_mem_committee
  obtain ⟨kept, count⟩ := reached.committeesKept_of_voteOrigin anchorSlot minLookahead
    maxLookahead (by omega) parentFound descends origin
    (voted := ⟨attestation.data.beaconBlockRoot, .pending⟩) rfl voteDescends voteNear targetFound
    headFound (by omega)
  rw [← UInt64.le_iff_toNat_le] at low high
  exact Store.mem_getCommitteesBetweenSlots participantsOk low high
    (Store.blockState_ok_iff.mpr headFound) (count ▸ below)
    ((kept _ _ rfl).trans committeeOk) member

/-- A supporter of a child of a root voted with an attestation that the store checked.

Its vote is in the subtree of the child, which is a known block with that parent root. -/
private theorem exists_voteOrigin_of_mem_supporters {checks : SignatureChecks}
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    {lower : store.ParentsBelow} {state : BeaconState preset fork} {nodes : List ForkChoiceNode}
    {c : Option Root} {parentRoot : Root} {i : ℕ}
    (isChild : (Store.blockTree lower).IsChild c (some parentRoot))
    (supporter : i ∈ supporters (Store.voters state) (Store.view lower nodes) c) :
    ∃ child childBlock attestation, c = some child ∧
      store.blocks[child]? = some childBlock ∧ childBlock.parentRoot = parentRoot ∧
      store.VoteOrigin config i.toUInt64 attestation ∧
      (Store.blockTree lower).Ancestor (some child) (some attestation.data.beaconBlockRoot) := by
  classical
  simp only [supporters, Finset.mem_filter] at supporter
  obtain ⟨-, m, latest, above⟩ := supporter
  change store.latestVote i.toUInt64 = some m at latest
  unfold Store.latestVote at latest
  split at latest
  · exact absurd latest (by simp)
  cases messageFound : store.latestMessages[i.toUInt64]? with
  | none => simp [messageFound] at latest
  | some message =>
    simp only [messageFound, Option.map_some, Option.some.injEq] at latest
    subst latest
    obtain ⟨attestation, rfl, origin⟩ := reached.forwardReachable.votesHaveOrigins messageFound
    rcases c with _ | child
    · exact absurd rfl isChild.1
    obtain ⟨childBlock, childFound, childParent⟩ := Store.blockTree_isChild_iff.mp isChild
    exact ⟨child, childBlock, attestation, rfl, childFound, childParent, origin, above⟩

/-- A validator whose latest vote is for a block supports no child of that block.

It must not be a known equivocator. -/
private theorem not_mem_supporters_of_latest {lower : store.ParentsBelow}
    {state : BeaconState preset fork} {nodes : List ForkChoiceNode} {c : Option Root}
    {parentRoot : Root} {v : ValidatorIndex} {message : LatestMessage fork}
    (isChild : (Store.blockTree lower).IsChild c (some parentRoot))
    (honest : v ∉ store.equivocatingIndices)
    (latest : store.latestMessages[v]? = some message) (voteRoot : message.root = parentRoot) :
    v.toNat ∉ supporters (Store.voters state) (Store.view lower nodes) c := by
  classical
  intro supporter
  simp only [supporters, Finset.mem_filter] at supporter
  obtain ⟨-, m, vote, above⟩ := supporter
  change store.latestVote v.toNat.toUInt64 = some m at vote
  have contains : store.equivocatingIndices.contains v = false := by simpa using honest
  simp only [Store.latestVote, UInt64.ofNat_toNat, contains, latest, Bool.false_eq_true,
    ↓reduceIte, Option.map_some, Option.some.injEq] at vote
  subst vote
  rw [voteRoot] at above
  exact absurd isChild.height_lt (Nat.not_lt.mpr above.height_le)

/-- Two children of a block weigh together at most the rule's count, plus the score of the boost.

The count is the weight of the committees from the slot after the parent to the slot before now.

The rule reads them in the state of the head, which descends from the parent.

A validator counts in the given state, active and not slashed there, with its effective balance.

That state is also the source of balances of the count.

A set of validators that support neither child adds its stake to the left side.

Each of them must count in that range: active in the source, and a member of its committees.

The weights are those of the model of the store with the boost, for any boosted block and score.

Every latest vote must come from an attestation that the store checked.

The store must be built with one setting of the checks, and the anchor block not after its state.

Both lookaheads of the seed must be at least one epoch.

The ring of mixes must be longer than the minimum lookahead plus two epochs.

The registry of the state must hold at most the validators that the preset allows. -/
theorem Store.ForwardReachableWith.weight_add_weight_add_stake_le_withBoost
    {checks : SignatureChecks} (before : fork < .glamsterdam) (lower : store.ParentsBelow)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {state : BeaconState preset fork} (within : state.RegistryWithinLimit)
    (nodes : List ForkChoiceNode) (boosted : Option (Option Root)) (score : ℕ)
    {head root : Root} {sibling : Option Root} {block parentBlock : BeaconBlock preset fork}
    {currentSlot firstSlot lastSlot : Slot} {maximumSupport : Gwei}
    (found : store.blocks[root]? = some block)
    (parentFound : store.blocks[block.parentRoot]? = some parentBlock)
    (siblingChild : sibling ∈ children (view lower nodes) (some block.parentRoot))
    (distinct : sibling ≠ some root)
    (descends : store.isAncestor ⟨head, .pending⟩ ⟨block.parentRoot, .pending⟩ = .ok true)
    (slotOk : store.getCurrentSlot config = .ok currentSlot)
    (firstOk : addChecked parentBlock.slot 1 = .ok firstSlot)
    (lastOk : subChecked currentSlot 1 = .ok lastSlot)
    (maximumOk : store.computeCommitteeWeightBetweenSlots head state firstSlot lastSlot =
      .ok maximumSupport)
    {N : Finset ValidatorIndex}
    (inside : ∀ v ∈ N, (∀ participants,
      store.getCommitteesBetweenSlots head firstSlot lastSlot = .ok participants →
        v ∈ participants) ∧ ∃ validator,
      state.validators.data[v.toNat]? = some validator ∧
        isActiveValidator validator (getCurrentEpoch state) = true)
    (neither : ∀ v ∈ N, v.toNat ∉ supporters (voters state) (view lower nodes) (some root) ∧
      v.toNat ∉ supporters (voters state) (view lower nodes) sibling) :
    weight (voters state).insertNone (boostStake (balanceAt state) score)
        ((view lower nodes).withBoost boosted) (some root) +
      weight (voters state).insertNone (boostStake (balanceAt state) score)
        ((view lower nodes).withBoost boosted) sibling +
      stake (fun v => balanceAt state v.toNat) N ≤
    maximumSupport.toNat + score := by
  classical
  have isChild : (Store.blockTree lower).IsChild (some root) (some block.parentRoot) :=
    Store.blockTree_isChild_iff.mpr ⟨block, found, rfl⟩
  have siblingIsChild := (mem_children.mp siblingChild).2
  refine (Nat.add_le_add_right (weight_withBoost_add_le isChild siblingIsChild (Ne.symm distinct)
    boosted score) _).trans ?_
  suffices key :
      weight (Store.voters state) (balanceAt state) (Store.view lower nodes) (some root) +
      weight (Store.voters state) (balanceAt state) (Store.view lower nodes) sibling +
      stake (fun v => balanceAt state v.toNat) N ≤ maximumSupport.toNat by omega
  set S := supporters (Store.voters state) (Store.view lower nodes) (some root) with hS
  set S' := supporters (Store.voters state) (Store.view lower nodes) sibling with hS'
  -- Each supporter counts in the state: it is in the registry and active there.
  have voter : ∀ i ∈ S ∪ S', i < state.validators.data.size ∧ ∃ validator,
      state.validators.data[i]? = some validator ∧
        isActiveValidator validator (getCurrentEpoch state) = true := by
    intro i member
    have member : i ∈ Store.voters state := by
      rcases Finset.mem_union.mp member with h | h <;> exact Finset.mem_of_mem_filter _ h
    simp only [Store.voters, Finset.mem_filter, Finset.mem_range] at member
    obtain ⟨lt, countsOk⟩ := member
    unfold Store.counts at countsOk
    cases atIndex : state.validators.data[i]? with
    | none => simp [atIndex] at countsOk
    | some validator =>
      simp only [atIndex, Bool.and_eq_true] at countsOk
      exact ⟨lt, validator, rfl, countsOk.1⟩
  have back : ∀ i ∈ S ∪ S', i.toUInt64.toNat = i := fun i member =>
    toNat_toUInt64_of_lt within (voter i member).1
  -- The supporters of the two children and the set are pairwise disjoint.
  have apart : Disjoint S S' := by
    refine Finset.disjoint_left.mpr fun v hv hv' => ?_
    simp only [hS, hS', supporters, Finset.mem_filter] at hv hv'
    obtain ⟨-, m, hm, hcm⟩ := hv
    obtain ⟨-, m', hm', hcm'⟩ := hv'
    rw [hm, Option.some_inj] at hm'
    subst hm'
    exact isChild.disjoint siblingIsChild (Ne.symm distinct) hcm hcm'
  have apartN : Disjoint ((S ∪ S').image Nat.toUInt64) N := by
    refine Finset.disjoint_left.mpr fun v hv hN => ?_
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨n, n'⟩ := neither _ hN
    rw [back i hi] at n n'
    rcases Finset.mem_union.mp hi with h | h
    exacts [n h, n' h]
  have injective : Set.InjOn Nat.toUInt64 ↑(S ∪ S') := fun i hi j hj same => by
    have := congrArg UInt64.toNat same
    rwa [back i hi, back j hj] at this
  have split : weight (Store.voters state) (balanceAt state) (Store.view lower nodes) (some root) +
      weight (Store.voters state) (balanceAt state) (Store.view lower nodes) sibling +
      stake (fun v => balanceAt state v.toNat) N =
      stake (fun v => balanceAt state v.toNat) ((S ∪ S').image Nat.toUInt64 ∪ N) := by
    simp only [weight, stake]
    rw [Finset.sum_union apartN, Finset.sum_image injective, ← hS, ← hS',
      ← Finset.sum_union apart]
    congr 1
    exact Finset.sum_congr rfl fun i hi => by rw [back i hi]
  rw [split]
  refine stake_le_of_active_of_reads maximumOk (fun v member => ?_) (fun whole v member => ?_)
  · rcases Finset.mem_union.mp member with image | hN
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp image
      rw [back i hi]
      exact (voter i hi).2
    · exact (inside v hN).2
  rcases Finset.mem_union.mp member with image | hN
  swap
  · exact (inside v hN).1
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp image
  intro participants participantsOk
  -- The supporter voted with a checked attestation in the subtree of one of the children.
  obtain ⟨c, cIsChild, supporter⟩ : ∃ c, (Store.blockTree lower).IsChild c
      (some block.parentRoot) ∧ i ∈ supporters (Store.voters state) (Store.view lower nodes) c := by
    rcases Finset.mem_union.mp hi with h | h
    exacts [⟨_, isChild, h⟩, ⟨_, siblingIsChild, h⟩]
  obtain ⟨child, childBlock, attestation, -, childFound, childParent, origin, above⟩ :=
    exists_voteOrigin_of_mem_supporters reached cIsChild supporter
  obtain ⟨low, high⟩ := slot_mem_range_of_voteOrigin lower parentFound childFound childParent
    slotOk firstOk lastOk origin above
  exact mem_committees_of_voteOrigin before lower anchorSlot reached minLookahead maxLookahead
    ring parentFound childFound childParent descends slotOk firstOk lastOk
    (isFullValidatorSetCovered_eq_false maximumOk (UInt64.le_trans low high) whole)
    participantsOk origin above

/-- Two children of a block and the rule's discount weigh at most its count, plus a boost score.

So the discount never exceeds the count plus the score.

The count is the weight of the committees from the slot after the parent to the slot before now.

The discount is the rule's discount of the first child, for the empty slots before it.

Both read the state of the head, which descends from the parent.

A validator counts in the given state, active and not slashed there, with its effective balance.

That state is also the source of balances of the rule.

The weights are those of the model of the store with the boost, for any boosted block and score.

Every latest vote must come from an attestation that the store checked.

The store must be built with one setting of the checks, and the anchor block not after its state.

Both lookaheads of the seed must be at least one epoch.

The ring of mixes must be longer than the minimum lookahead plus two epochs.

The registry of the state must hold at most the validators that the preset allows. -/
theorem Store.ForwardReachableWith.weight_add_weight_le_withBoost
    {checks : SignatureChecks} (before : fork < .glamsterdam) (lower : store.ParentsBelow)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {state : BeaconState preset fork} (within : state.RegistryWithinLimit)
    (nodes : List ForkChoiceNode) (boosted : Option (Option Root)) (score : ℕ)
    {head root : Root} {sibling : Option Root} {block parentBlock : BeaconBlock preset fork}
    {currentSlot firstSlot lastSlot : Slot} {maximumSupport discount : Gwei}
    (found : store.blocks[root]? = some block)
    (parentFound : store.blocks[block.parentRoot]? = some parentBlock)
    (siblingChild : sibling ∈ children (view lower nodes) (some block.parentRoot))
    (distinct : sibling ≠ some root)
    (descends : store.isAncestor ⟨head, .pending⟩ ⟨block.parentRoot, .pending⟩ = .ok true)
    (slotOk : store.getCurrentSlot config = .ok currentSlot)
    (firstOk : addChecked parentBlock.slot 1 = .ok firstSlot)
    (lastOk : subChecked currentSlot 1 = .ok lastSlot)
    (maximumOk : store.computeCommitteeWeightBetweenSlots head state firstSlot lastSlot =
      .ok maximumSupport)
    (discountOk : store.computeEmptySlotSupportDiscount config head state root = .ok discount) :
    weight (voters state).insertNone (boostStake (balanceAt state) score)
        ((view lower nodes).withBoost boosted) (some root) +
      weight (voters state).insertNone (boostStake (balanceAt state) score)
        ((view lower nodes).withBoost boosted) sibling + discount.toNat ≤
    maximumSupport.toNat + score := by
  obtain ⟨shortLast, participants, adversary, shortOk, participantsOk, -, discountValue, -⟩ :=
    Store.exists_stake_parentVotersOf_of_computeEmptySlotSupportDiscount
      (Store.block_ok_iff.mpr found) (Store.block_ok_iff.mpr parentFound) firstOk discountOk
  -- The block is at or before the current slot, so the range of the discount ends in the count.
  obtain ⟨blockState, blockStateFound, -, -⟩ := reached.reachable.blockStatesFromParents found
  have blockLe := Store.Reachable.slot_le_of_blockState anchorSlot reached.reachable found
    blockStateFound
  have stateLe := reached.forwardReachable.slot_le_of_blockState_of_getCurrentSlot
    blockStateFound slotOk
  have shortLe : shortLast ≤ lastSlot := by
    obtain ⟨-, shortValue⟩ := subChecked_ok_iff.mp shortOk
    obtain ⟨-, lastValue⟩ := subChecked_ok_iff.mp lastOk
    rw [UInt64.le_iff_toNat_le] at blockLe stateLe ⊢
    omega
  have bound := reached.weight_add_weight_add_stake_le_withBoost before lower anchorSlot
    minLookahead maxLookahead ring within nodes boosted score found parentFound siblingChild
    distinct descends slotOk firstOk lastOk maximumOk
    (N := store.parentVotersOf state participants block parentBlock)
    (fun v member => by
      obtain ⟨inShort, ⟨validator, atIndex, -, isActive⟩, -⟩ := Store.mem_parentVotersOf.mp member
      exact ⟨fun read readOk =>
        Store.mem_getCommitteesBetweenSlots_of_le participantsOk readOk shortLe inShort,
        validator, atIndex, isActive⟩)
    (fun v member => by
      obtain ⟨-, -, honest, message, supported, latest, supportedOk, isParent⟩ :=
        Store.mem_parentVotersOf.mp member
      have voteRoot : message.root = block.parentRoot := by
        rw [← Store.getSupportedNode_root supportedOk]
        rcases isParent with rfl | rfl <;> rfl
      exact ⟨not_mem_supporters_of_latest
          (Store.blockTree_isChild_iff.mpr ⟨block, found, rfl⟩) honest latest voteRoot,
        not_mem_supporters_of_latest (mem_children.mp siblingChild).2 honest latest voteRoot⟩)
  omega

end EthLib.Consensus
