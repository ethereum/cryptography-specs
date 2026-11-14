module

public import EthLib.Consensus.Proofs.Transition.Genesis
public import EthLib.Consensus.Proofs.Transition.TargetPending
public import EthLib.Consensus.Proofs.Transition.TargetSlots
public import EthLib.Consensus.Proofs.Transition.ForkBoundary
public import EthLib.Consensus.Transition.ForkBoundary

/-!
# Proofs: the target flags across the fork upgrades

From Altair each target flag of the state comes from a vote of a set for the link of its epoch.

Each upgrade from Altair on keeps that.

It carries the slot, the justified checkpoints, the block roots and the flags of both epochs.

So a vote for the link of a flag stays a vote for that link.

The upgrade from Phase 0 builds the flags of the previous epoch from the pending attestations.

When each of their attesters cast a vote of the set for the link of that epoch, each flag has one.

Gasper §4.4, Definitions 4.5 and 4.6, justify a checkpoint by a supermajority link.

The paper is [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {config : Config} {checks : SignatureChecks}
  {votes : Set (ValidatorIndex × AttestationData)}

/-! ## What an upgrade keeps -/

/-- A vote for a link is one in a state of another fork with the same slot, roots and checkpoints.

That is the case after an upgrade. -/
theorem LinkVote.of_upgradeFrame {fork post : Fork} {pre : BeaconState preset fork}
    {after : BeaconState preset post} {current : Bool} {position : Nat}
    {vote : ValidatorIndex × AttestationData} (frame : UpgradeFrame config pre after)
    (link : LinkVote pre current position vote) : LinkVote after current position vote := by
  simpa only [LinkVote, getCurrentEpoch, getPreviousEpoch, getBlockRoot, getBlockRootAtSlot,
    frame.slot, frame.blockRoots, frame.previousJustified, frame.currentJustified] using link

/-- An upgrade keeps the two justified checkpoints equal in the first two epochs. -/
theorem JustifiedEarly.of_upgradeFrame {fork post : Fork} {pre : BeaconState preset fork}
    {after : BeaconState preset post} (frame : UpgradeFrame config pre after)
    (early : JustifiedEarly pre) : JustifiedEarly after := by
  unfold JustifiedEarly getCurrentEpoch at early ⊢
  rw [frame.slot, frame.previousJustified, frame.currentJustified]
  exact early

/-- An upgrade keeps the previous justified epoch below the previous epoch. -/
theorem JustifiedSeparated.of_upgradeFrame {fork post : Fork} {pre : BeaconState preset fork}
    {after : BeaconState preset post} (frame : UpgradeFrame config pre after)
    (separated : JustifiedSeparated pre) : JustifiedSeparated after := by
  unfold JustifiedSeparated getPreviousEpoch getCurrentEpoch at separated ⊢
  rw [frame.slot, frame.previousJustified]
  exact separated

/-- An upgrade from Altair on keeps each target flag backed by a vote of the set for its link. -/
theorem TargetFlagsVoted.of_upgradeFrame {fork post : Fork} {pre : BeaconState preset fork}
    {after : BeaconState preset post}
    (frame : UpgradeFrame config pre after) (altair : .altair ≤ fork)
    (holds : TargetFlagsVoted votes pre) : TargetFlagsVoted votes after := by
  intro _ current position flagged
  obtain ⟨vote, voted, link⟩ := holds altair current position (frame.flags altair current
    position flagged)
  exact ⟨vote, voted, link.of_upgradeFrame frame⟩

/-! ## The upgrade from Phase 0 -/

/-- One translated pending attestation sets a target flag only for one of its attesters.

Its target root is then the root of the block at the first slot of its target epoch. -/
private theorem translateAttestation_target {fork : Fork} {state after : BeaconState preset fork}
    {altair : .altair ≤ fork} {pending : PendingAttestation preset}
    (computed : translateAttestation state altair pending = .ok after) (position : Nat)
    (flagged : TargetFlagAt (after.previousEpochParticipation altair) position) :
    TargetFlagAt (state.previousEpochParticipation altair) position ∨
      getBlockRoot state pending.data.target.epoch = .ok pending.data.target.root ∧
        ∃ attesters, getPendingAttestingIndices state pending = .ok attesters ∧
          ∃ attester ∈ attesters, attester.toNat = position := by
  simp only [translateAttestation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨flags, flagsOk, attesters, attestersOk, participation, folded, rfl⟩ := computed
  have kinds := (getAttestationParticipationFlagIndices_spec flagsOk).2
  -- Each attester in turn gets the earned flags at its own position.
  rcases foldlM_targetFlag (earned := TIMELY_TARGET_FLAG_INDEX ∈ flags) (flagsOf := id)
      (fun list index updated ok place ⟨value, found, set⟩ => by
        split at ok
        · rename_i inside
          simp only [Except.ok.injEq] at ok
          subst ok
          dsimp only [id] at found ⊢
          rw [Array.getElem?_set] at found
          split at found
          · rename_i same
            cases found
            rcases hasFlag_foldl_addFlag_target flags _ kinds set with before | chosen
            · exact .inl ⟨_, by rw [← same]; exact Array.getElem?_eq_getElem inside, before⟩
            · exact .inr ⟨chosen, same⟩
          · exact .inl ⟨value, found, set⟩
        · cases ok)
      attesters _ participation folded position flagged with
    old | ⟨chosen, attester, member, place⟩
  · exact .inl old
  · exact .inr ⟨getAttestationParticipationFlagIndices_targetRoot flagsOk chosen, attesters,
      attestersOk, attester, member, place⟩

/-- The upgrade to Altair builds each target flag from a vote of the set for the link of its epoch.

Each pending attestation of Phase 0 must be a vote of the set for the link of its epoch.

The flags of the current epoch start empty. -/
theorem TargetFlagsVoted.of_upgradeToAltair {pre : BeaconState preset .phase0}
    {after : BeaconState preset .altair}
    (holds : PendingVoted votes pre) (computed : upgradeToAltair config pre = .ok after) :
    TargetFlagsVoted votes after := by
  have frame := upgradeFrame_upgradeToAltair computed
  obtain ⟨_, folded, _, rfl⟩ := upgradeToAltair_ok computed
  obtain ⟨previousZero, currentZero, -⟩ := carryFields_of_lt_altair (config := config)
    (post := .altair) pre (by decide) (by decide) (by decide) (by decide)
  -- A flag of the previous epoch in a state of the fold comes from a vote of the set.
  let Claim : BeaconState preset .altair → Prop := fun state =>
    state.validators.data = pre.validators.data ∧
      state.randaoMixes.elements = pre.randaoMixes.elements ∧
      state.slot = pre.slot ∧ state.blockRoots = pre.blockRoots ∧
      (∀ position, ¬TargetFlagAt (state.currentEpochParticipation (by decide)) position) ∧
      ∀ position, TargetFlagAt (state.previousEpochParticipation (by decide)) position →
        ∃ vote ∈ votes, LinkVote pre false position vote
  have walk : ∀ (list : List (PendingAttestation preset)),
      (∀ pending ∈ list, pending ∈ recentPending pre (by decide) false) →
      ∀ (state final : BeaconState preset .altair), Claim state →
        list.foldlM (fun state attestation => translateAttestation state (by decide) attestation)
          state = .ok final → Claim final := by
    intro list
    induction list with
    | nil =>
      intro _ state final holdsState computed
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ holdsState
    | cons first rest more =>
      intro listed state final holdsState computed
      rw [List.foldlM_cons, bind_ok_iff] at computed
      obtain ⟨middle, middleOk, computed⟩ := computed
      refine more (fun pending member => listed pending (List.mem_cons_of_mem first member))
        middle final ?_ computed
      obtain ⟨validators, mixes, slot, roots, none, flags⟩ := holdsState
      have translated := translateAttestation_target middleOk
      obtain ⟨participation, rfl, -⟩ := translateAttestation_spec middleOk
      refine ⟨validators, mixes, slot, roots, none, fun position flagged => ?_⟩
      rcases translated position flagged with old | ⟨root, attesters, attestersOk, attester,
        member, place⟩
      · exact flags position old
      obtain ⟨epoch, slotEpoch, source, voted⟩ :=
        holds (by decide) false first (listed first List.mem_cons_self)
      have committees : CommitteesKept first.data.target.epoch pre state :=
        CommitteesKept.of_eq validators mixes _
      have attestersPre : getPendingAttestingIndices pre first = .ok attesters := by
        unfold getPendingAttestingIndices at attestersOk ⊢
        rw [← committees _ _ slotEpoch]
        exact attestersOk
      refine ⟨(attester, first.data), voted attesters attestersPre attester member,
        place, epoch, source, ?_⟩
      have same : getBlockRoot state first.data.target.epoch =
          getBlockRoot pre first.data.target.epoch := by
        simp only [getBlockRoot, getBlockRootAtSlot, slot, roots]
      exact same ▸ root
  have empty : ∀ {list : EpochParticipation preset .altair},
      list.data = Array.replicate pre.validators.data.size 0 → ∀ position,
        ¬TargetFlagAt list position := fun zero position ⟨value, found, set⟩ => by
    rw [zero, Array.getElem?_replicate] at found
    split at found
    · cases found
      exact absurd set (by decide)
    · cases found
  have start : Claim (carryFields config .altair pre (by decide) (by decide)) :=
    ⟨rfl, rfl, rfl, rfl, empty currentZero, fun position flagged =>
      absurd flagged (empty previousZero position)⟩
  obtain ⟨-, -, -, -, currentNone, previousFlags⟩ :=
    walk _ (fun pending member => by simpa [recentPending] using member) _ _ start folded
  intro altair current position flagged
  cases current
  · obtain ⟨vote, voted, link⟩ := previousFlags position flagged
    exact ⟨vote, voted, link.of_upgradeFrame frame⟩
  · exact absurd flagged (currentNone position)

/-! ## The upgrades due at a slot -/

/-- The upgrades due at a slot never shrink the registry. -/
theorem processUpgrades_registryGrows {forked after : ForkedBeaconState preset}
    (computed : processUpgrades config checks forked = .ok after) :
    forked.state.validators.data.size ≤ after.state.validators.data.size :=
  processUpgrades_induction
    (property := fun state => forked.state.validators.data.size ≤ state.state.validators.data.size)
    (fun le stepOk => Nat.le_trans le (upgradeFrame_upgradeNext stepOk).registryGrows)
    (Nat.le_refl _) computed

/-- The upgrades due at a slot keep the two justified checkpoints equal in the first two epochs.
-/
theorem JustifiedEarly.of_processUpgrades {forked after : ForkedBeaconState preset}
    (early : JustifiedEarly forked.state)
    (computed : processUpgrades config checks forked = .ok after) :
    JustifiedEarly after.state :=
  processUpgrades_induction (property := fun state => JustifiedEarly state.state)
    (fun early stepOk => early.of_upgradeFrame (upgradeFrame_upgradeNext stepOk)) early computed

/-- The upgrades due at a slot keep the previous justified epoch below the previous epoch. -/
theorem JustifiedSeparated.of_processUpgrades {forked after : ForkedBeaconState preset}
    (separated : JustifiedSeparated forked.state)
    (computed : processUpgrades config checks forked = .ok after) :
    JustifiedSeparated after.state :=
  processUpgrades_induction (property := fun state => JustifiedSeparated state.state)
    (fun separated stepOk => separated.of_upgradeFrame (upgradeFrame_upgradeNext stepOk))
    separated computed

/-- The upgrades due at a slot keep both justified checkpoints. -/
theorem processUpgrades_justified {forked after : ForkedBeaconState preset}
    (computed : processUpgrades config checks forked = .ok after) :
    after.state.previousJustifiedCheckpoint = forked.state.previousJustifiedCheckpoint ∧
      after.state.currentJustifiedCheckpoint = forked.state.currentJustifiedCheckpoint :=
  processUpgrades_induction
    (property := fun state =>
      state.state.previousJustifiedCheckpoint = forked.state.previousJustifiedCheckpoint ∧
        state.state.currentJustifiedCheckpoint = forked.state.currentJustifiedCheckpoint)
    (fun ⟨previous, current⟩ stepOk =>
      ⟨(upgradeFrame_upgradeNext stepOk).previousJustified.trans previous,
        (upgradeFrame_upgradeNext stepOk).currentJustified.trans current⟩)
    ⟨rfl, rfl⟩ computed

/-- The upgrades due at a slot keep the bits of justification. -/
theorem processUpgrades_justificationBits {forked after : ForkedBeaconState preset}
    (computed : processUpgrades config checks forked = .ok after) :
    after.state.justificationBits = forked.state.justificationBits :=
  processUpgrades_induction
    (property := fun state => state.state.justificationBits = forked.state.justificationBits)
    (fun same stepOk => (upgradeFrame_upgradeNext stepOk).justificationBits.trans same) rfl
    computed

/-- The upgrades due at a slot keep the buffer of block roots. -/
theorem processUpgrades_blockRoots {forked after : ForkedBeaconState preset}
    (computed : processUpgrades config checks forked = .ok after) :
    after.state.blockRoots = forked.state.blockRoots :=
  processUpgrades_induction
    (property := fun state => state.state.blockRoots = forked.state.blockRoots)
    (fun same stepOk => (upgradeFrame_upgradeNext stepOk).blockRoots.trans same) rfl computed

/-- An upgrade reaches Altair or a later fork.

Before Altair, only a state of Phase 0 upgrades. -/
theorem upgradeNext_altair {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post) :
    .altair ≤ post.val.fork ∧ (pre.fork < .altair → pre.fork = .phase0) := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at computed <;>
    first
      | (obtain ⟨_, -, rfl⟩ := computed; dsimp only; decide)

/-- The upgrades due at a slot keep each pending attestation a vote of the set for its link.

An upgrade moves the state to Altair or later, where no pending attestation remains. -/
theorem PendingVoted.of_processUpgrades {forked after : ForkedBeaconState preset}
    (holds : PendingVoted votes forked.state)
    (computed : processUpgrades config checks forked = .ok after) :
    PendingVoted votes after.state :=
  processUpgrades_induction (property := fun state => PendingVoted votes state.state)
    (fun _ stepOk before => absurd (upgradeNext_altair stepOk).1 (Nat.not_le_of_lt before))
    holds computed

/-- The upgrades due at a slot, from Altair on, keep each target flag backed by a vote of the set.

That vote is for the link of the epoch of the flag. -/
theorem TargetFlagsVoted.of_processUpgrades {forked after : ForkedBeaconState preset}
    (altair : .altair ≤ forked.fork) (holds : TargetFlagsVoted votes forked.state)
    (computed : processUpgrades config checks forked = .ok after) :
    TargetFlagsVoted votes after.state := by
  fun_induction processUpgrades config checks forked generalizing after with
  | case1 forked _ more =>
    obtain ⟨step, stepOk, rest⟩ := bind_ok_iff.mp computed
    exact more step (Nat.le_trans altair (Nat.le_of_lt step.property))
      (holds.of_upgradeFrame (upgradeFrame_upgradeNext stepOk) altair) rest
  | case2 forked _ =>
    cases computed
    exact holds

/-- The upgrades due at a slot, from Phase 0, give each target flag a vote of the set.

That vote is for the link of the epoch of the flag.

Each pending attestation of Phase 0 must be a vote of the set for the link of its epoch. -/
theorem TargetFlagsVoted.of_processUpgrades_of_phase0 {forked after : ForkedBeaconState preset}
    (phase0 : forked.fork = .phase0) (holds : PendingVoted votes forked.state)
    (computed : processUpgrades config checks forked = .ok after) :
    TargetFlagsVoted votes after.state := by
  obtain ⟨fork, state⟩ := forked
  simp only at phase0 holds
  subst phase0
  unfold processUpgrades at computed
  split at computed
  · obtain ⟨step, stepOk, rest⟩ := bind_ok_iff.mp computed
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at stepOk
    obtain ⟨_, upgraded, rfl⟩ := stepOk
    exact TargetFlagsVoted.of_processUpgrades (show Fork.altair ≤ Fork.altair by decide)
      (TargetFlagsVoted.of_upgradeToAltair holds upgraded) rest
  · cases computed
    intro altair
    exact absurd altair (by decide : ¬Fork.altair ≤ Fork.phase0)

/-- The upgrades due at a slot, before Altair, give each target flag a vote of the set.

That vote is for the link of the epoch of the flag.

Each pending attestation must be a vote of the set for the link of its epoch. -/
theorem TargetFlagsVoted.of_processUpgrades_of_lt_altair
    {forked after : ForkedBeaconState preset} (before : forked.fork < .altair)
    (holds : PendingVoted votes forked.state)
    (computed : processUpgrades config checks forked = .ok after) :
    TargetFlagsVoted votes after.state := by
  by_cases phase0 : forked.fork = .phase0
  · exact TargetFlagsVoted.of_processUpgrades_of_phase0 phase0 holds computed
  unfold processUpgrades at computed
  split at computed
  · obtain ⟨step, stepOk, -⟩ := bind_ok_iff.mp computed
    exact absurd ((upgradeNext_altair stepOk).2 before) phase0
  · cases computed
    intro altair
    exact absurd altair (Nat.not_le_of_lt before)

/-! ## Genesis -/

/-- The genesis state built from deposits has equal justified checkpoints in the first two epochs.
-/
theorem JustifiedEarly.of_initializeBeaconStateFromEth1 {fork : Fork}
    {after : BeaconState preset fork} {eth1BlockHash : Hash32} {eth1Timestamp : UInt64}
    {deposits : Array Deposit}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok after) :
    JustifiedEarly after := by
  obtain ⟨_, _, _, activated, _, frame, rfl⟩ := initializeBeaconStateFromEth1_frame computed
  intro _
  show activated.previousJustifiedCheckpoint = activated.currentJustifiedCheckpoint
  rw [frame.previousJustified, frame.currentJustified]
  rfl

/-- The genesis state has its previous justified epoch below the previous epoch once it counts.

It is at the genesis epoch, so the separation asks nothing of it. -/
theorem JustifiedSeparated.of_initializeBeaconStateFromEth1 {fork : Fork}
    {after : BeaconState preset fork} {eth1BlockHash : Hash32} {eth1Timestamp : UInt64}
    {deposits : Array Deposit}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok after) :
    JustifiedSeparated after := by
  intro later
  have slot := (initializeBeaconStateFromEth1_checkpoints computed).1
  simp [getCurrentEpoch, slot, GENESIS_SLOT, GENESIS_EPOCH, computeEpochAtSlot,
    UInt64.lt_iff_toNat_lt] at later

/-- Before Altair, the genesis state built from deposits has no pending attestations. -/
theorem initializeBeaconStateFromEth1_pending {fork : Fork} {after : BeaconState preset fork}
    {eth1BlockHash : Hash32} {eth1Timestamp : UInt64} {deposits : Array Deposit}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok after) (before : fork < .altair) (current : Bool) :
    recentPending after before current = #[] := by
  obtain ⟨_, _, _, deposited, activated, _, depositedOk, activatedOk, rfl⟩ :=
    initializeBeaconStateFromEth1_ok computed
  let Empty : BeaconState preset fork → Prop := fun state =>
    (state.previousEpochAttestations before).data = #[] ∧
      (state.currentEpochAttestations before).data = #[]
  have afterDeposits : Empty deposited := by
    refine foldlM_ok_invariant Empty (fun state entry next empty ok => ?_) ⟨rfl, rfl⟩ depositedOk
    simp only [genesisDeposit, bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    have frame := pendingFrame_processDeposit before ok
    exact ⟨by rw [funext frame.previousPending]; exact empty.1,
      by rw [funext frame.currentPending]; exact empty.2⟩
  have afterActivation : Empty activated := by
    refine foldlM_ok_invariant Empty (fun state index next empty ok => ?_) afterDeposits
      activatedOk
    simp only [activateAtGenesis, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, set⟩ := ok
    obtain ⟨_, rfl⟩ := setValidatorAt_ok set
    exact empty
  cases current
  · exact afterActivation.1
  · exact afterActivation.2

end EthLib.Consensus
