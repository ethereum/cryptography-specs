module

public import EthLib.Consensus.BeaconApi.Duties
public import EthLib.Consensus.Proofs.HonestValidator
public import EthLib.Consensus.Proofs.Transition.StateTransition

/-!
# Proofs: the duty answers of the Beacon API

Each attester duty names a committee of its slot, and the validator's place in it.

A requested validator in a committee of the epoch has exactly one duty.

A request for an epoch after the next one is refused.

An attester, sync or PTC request with no index is refused.

So is an attester epoch whose seed is gone.

An attester epoch whose dependent root has left the block roots is refused as well.

That refusal needs each requested index to name a validator whose committee assignment succeeds.

From Gloas, a PTC request is refused outside the previous epoch to the next one.

It is also refused before the Gloas fork epoch.

An attester, sync or PTC index that names no validator is refused.

That refusal needs an epoch the answer serves, and the duty lookup of each earlier index to succeed.

A sync epoch outside the current and next periods is refused.

So is a proposer epoch that the state cannot answer for.

A sync request before Altair is refused, and so is a PTC request before Gloas.

In the current epoch, each proposer duty from the slot of the state on names its proposer.

Each seat of a sync duty holds the key of the validator.

Each refusal of the sync answer is one of four errors, all with code 400.

Under bounds on the slots, the dependent root fails only with the error of an invalid epoch.

Before Fulu, both proposer answers give code 500 to a current epoch with no active validator.

From Fulu, under the same bounds, a proposer answer gets code 500 exactly at a lookahead entry.

That entry lies at a slot of the requested epoch, and names no validator.

Under those bounds, if each lookahead entry names a validator, the answer fails only with code 400.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base Cryptography.Bls

variable {preset : Preset} {fork : Fork}

/-- An attester duty comes from the committee assignment of its validator. -/
private theorem attesterDuty_some {state : BeaconState preset fork} {epoch : Epoch}
    {index : ValidatorIndex} {duty : AttesterDuty}
    (computed : attesterDuty state epoch index = .ok (some duty)) :
    ∃ committee, getCommitteeAssignment state epoch index =
        .ok (some (committee, duty.committeeIndex, duty.slot)) ∧
      duty.validatorIndex = index ∧ duty.committeeLength = committee.size.toUInt64 ∧
      duty.validatorCommitteeIndex = (committee.idxOf index).toUInt64 ∧
      duty.committeesAtSlot = getCommitteeCountPerSlot state epoch := by
  unfold attesterDuty at computed
  obtain ⟨validator, -, computed⟩ := bind_ok_iff.mp computed
  obtain ⟨assignment, assigned, computed⟩ := bind_ok_iff.mp computed
  rw [mapError_ok_iff] at assigned
  match assignment, computed with
  | some (committee, committeeIndex, slot), computed =>
    simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at computed
    subst computed
    exact ⟨committee, assigned, rfl, rfl, rfl, rfl⟩

/-- Attester duties pass the epoch check and keep the duties of the requested validators. -/
private theorem attesterDuties_ok {state : BeaconState preset fork} {epoch : Epoch}
    {indices : List ValidatorIndex} {duties : List AttesterDuty}
    (computed : attesterDuties state epoch indices = .ok duties) :
    checkDutyEpoch state epoch = .ok () ∧ ∃ found,
      indices.mapM (attesterDuty state epoch) = .ok found ∧ duties = found.filterMap id := by
  unfold attesterDuties at computed
  by_cases empty : indices.isEmpty
  · simp [empty, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at computed
  · simp only [empty, Bool.false_eq_true, ↓reduceIte] at computed
    obtain ⟨_, checked, computed⟩ := bind_ok_iff.mp computed
    obtain ⟨found, mapped, computed⟩ := bind_ok_iff.mp computed
    simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact ⟨checked, found, mapped, computed.symm⟩

/-- Each attester duty comes from a requested validator. -/
private theorem attesterDuties_mem {state : BeaconState preset fork} {epoch : Epoch}
    {indices : List ValidatorIndex} {duties : List AttesterDuty}
    (computed : attesterDuties state epoch indices = .ok duties) {duty : AttesterDuty}
    (mem : duty ∈ duties) :
    ∃ index ∈ indices, attesterDuty state epoch index = .ok (some duty) := by
  obtain ⟨-, found, mapped, rfl⟩ := attesterDuties_ok computed
  obtain ⟨_, member, rfl⟩ := List.mem_filterMap.mp mem
  exact mapM_ok_mem mapped _ member

/-- Each attester duty names a committee of its slot that holds the validator.

The committee has the length of the duty, and the validator at the position of the duty. -/
theorem attesterDuties_committee {state : BeaconState preset fork} {epoch : Epoch}
    {indices : List ValidatorIndex} {duties : List AttesterDuty}
    (computed : attesterDuties state epoch indices = .ok duties) {duty : AttesterDuty}
    (mem : duty ∈ duties) :
    ∃ (committee : Array ValidatorIndex) (position : Nat),
      getBeaconCommittee state duty.slot duty.committeeIndex = .ok committee ∧
      duty.committeeLength = committee.size.toUInt64 ∧
      duty.validatorCommitteeIndex = position.toUInt64 ∧
      committee[position]? = some duty.validatorIndex := by
  obtain ⟨index, -, made⟩ := attesterDuties_mem computed mem
  obtain ⟨committee, assigned, named, length, position, -⟩ := attesterDuty_some made
  obtain ⟨-, -, read, member⟩ := getCommitteeAssignment_sound assigned
  refine ⟨committee, committee.idxOf index, read, length, position, ?_⟩
  rw [named]
  rcases committee with ⟨members⟩
  simp only [List.idxOf_toArray, List.getElem?_toArray]
  exact List.getElem?_idxOf (List.mem_toArray.mp member)

/-- A requested validator in a committee of the epoch has exactly one duty.

The request must not repeat an index. -/
theorem attesterDuties_complete {state : BeaconState preset fork} {epoch : Epoch}
    {indices : List ValidatorIndex} {duties : List AttesterDuty}
    (computed : attesterDuties state epoch indices = .ok duties) (distinct : indices.Nodup)
    {index : ValidatorIndex} (requested : index ∈ indices) {committee : Array ValidatorIndex}
    {committeeIndex : CommitteeIndex} {slot : Slot}
    (assigned :
      getCommitteeAssignment state epoch index = .ok (some (committee, committeeIndex, slot))) :
    (duties.filter (·.validatorIndex = index)).length = 1 := by
  obtain ⟨-, found, mapped, rfl⟩ := attesterDuties_ok computed
  clear computed
  induction indices generalizing found with
  | nil => simp at requested
  | cons first rest ih =>
    obtain ⟨head, tail, headOk, tailOk, rfl⟩ := mapM_cons_ok.mp mapped
    obtain ⟨absent, distinct⟩ := List.nodup_cons.mp distinct
    by_cases same : first = index
    · subst same
      -- The requested validator has a duty, and no later index names it.
      obtain ⟨validator, validatorOk, headOk⟩ := bind_ok_iff.mp headOk
      rw [assigned] at headOk
      simp only [Except.mapError, bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at headOk
      subst headOk
      have none : (tail.filterMap id).filter (·.validatorIndex = first) = [] := by
        refine List.filter_eq_nil_iff.mpr fun duty member named => ?_
        obtain ⟨_, member, rfl⟩ := List.mem_filterMap.mp member
        obtain ⟨other, otherMem, made⟩ := mapM_ok_mem tailOk _ member
        obtain ⟨_, -, otherNamed, -⟩ := attesterDuty_some made
        have named := of_decide_eq_true named
        exact absent (by rw [← named, otherNamed]; exact otherMem)
      rw [List.filterMap_cons_some (f := id) rfl, List.filter_cons_of_pos (by simp), none]
      rfl
    · have later : index ∈ rest := (List.mem_cons.mp requested).resolve_left (Ne.symm same)
      rw [← ih distinct later tail tailOk]
      cases head with
      | none => simp
      | some duty =>
        obtain ⟨_, -, named, -⟩ := attesterDuty_some headOk
        simp [named, same]

/-- The epoch check refuses an epoch after the next one. -/
private theorem checkDutyEpoch_far {state : BeaconState preset fork} {epoch : Epoch}
    (far : (getCurrentEpoch state).toNat + 1 < epoch.toNat) :
    checkDutyEpoch state epoch = .error (invalidEpoch epoch) := by
  simp [checkDutyEpoch, Nat.not_le.mpr far, throw, throwThe, MonadExceptOf.throw, bind,
    Except.bind]

/-- The epoch check refuses an epoch too old for the mixes of the state to hold its seed. -/
private theorem checkDutyEpoch_seed_gone {state : BeaconState preset fork} {epoch : Epoch}
    (gone : epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat ≤
      (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1) :
    checkDutyEpoch state epoch = .error (invalidEpoch epoch) := by
  by_cases far : (getCurrentEpoch state).toNat + 1 < epoch.toNat
  · exact checkDutyEpoch_far far
  · simp [checkDutyEpoch, Nat.not_lt.mp far, Nat.not_lt.mpr gone, throw, throwThe,
      MonadExceptOf.throw]

/-- The epoch check passes an epoch at most the next one, whose seed the mixes still hold. -/
private theorem checkDutyEpoch_ok {state : BeaconState preset fork} {epoch : Epoch}
    (near : epoch.toNat ≤ (getCurrentEpoch state).toNat + 1)
    (seeded : (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1 <
      epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat) :
    checkDutyEpoch state epoch = .ok () := by
  simp [checkDutyEpoch, near, seeded, pure, Except.pure]

/-- The epoch check passes, or gives the error of an invalid epoch. -/
private theorem checkDutyEpoch_cases (state : BeaconState preset fork) (epoch : Epoch) :
    checkDutyEpoch state epoch = .ok () ∨
      checkDutyEpoch state epoch = .error (invalidEpoch epoch) := by
  by_cases far : (getCurrentEpoch state).toNat + 1 < epoch.toNat
  · exact .inr (checkDutyEpoch_far far)
  by_cases gone : epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat ≤
      (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1
  · exact .inr (checkDutyEpoch_seed_gone gone)
  · exact .inl (checkDutyEpoch_ok (Nat.not_lt.mp far) (Nat.lt_of_not_le gone))

/-- A request for an epoch after the next one gets the error of an invalid epoch, code 400. -/
theorem attesterDuties_epoch_bound {state : BeaconState preset fork} {epoch : Epoch}
    {index : ValidatorIndex} {rest : List ValidatorIndex}
    (far : (getCurrentEpoch state).toNat + 1 < epoch.toNat) :
    attesterDuties state epoch (index :: rest) = .error (invalidEpoch epoch) := by
  simp [attesterDuties, checkDutyEpoch_far far, bind, Except.bind]

/-- An attester request with no index gets the error of an empty request, code 400. -/
theorem attesterDuties_nil {state : BeaconState preset fork} {epoch : Epoch} :
    attesterDuties state epoch [] = .error emptyIndices := by
  simp [attesterDuties, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- An attester epoch whose seed is gone gets the error of an invalid epoch, code 400.

It needs at least one index, and an epoch too old for the mixes of the state to hold its seed. -/
theorem attesterDuties_seed_gone {state : BeaconState preset fork} {epoch : Epoch}
    {index : ValidatorIndex} {rest : List ValidatorIndex}
    (gone : epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat ≤
      (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1) :
    attesterDuties state epoch (index :: rest) = .error (invalidEpoch epoch) := by
  simp [attesterDuties, checkDutyEpoch_seed_gone gone, bind, Except.bind]

/-- From Gloas, a PTC request for an epoch after the next one gets the error of an invalid epoch.
-/
theorem ptcDuties_epoch_bound {config : Config} {state : BeaconState preset fork}
    {gloas : .glamsterdam ≤ fork} {epoch : Epoch} {index : ValidatorIndex}
    {rest : List ValidatorIndex} (far : (getCurrentEpoch state).toNat + 1 < epoch.toNat) :
    ptcDuties config state gloas epoch (index :: rest) = .error (invalidEpoch epoch) := by
  simp [ptcDuties, checkDutyEpoch_far far, bind, Except.bind]

/-- From Gloas, the PTC duties of a request, against the current epoch of the state.

An empty request gets the error of an empty request, code 400.

The epoch must be from the previous epoch to the next one, and not before the Gloas fork epoch.

The mixes of the state must also still hold the seed of the epoch.

In that window it holds whenever the mixes outlast the seed lookahead by more than two epochs.

Any other epoch gets the error of an invalid epoch, code 400.

For an epoch in that range, a repeated index gets code 400 too.

Else the answer runs the duty of each requested validator in turn, in request order.

It keeps the validators in the PTC; the first index that fails ends the answer. -/
theorem ptcDuties_eq {config : Config} {state : BeaconState preset fork}
    {gloas : .glamsterdam ≤ fork} {epoch : Epoch} {indices : List ValidatorIndex} :
    ptcDuties config state gloas epoch indices =
      if indices = [] then .error emptyIndices
      else if (getCurrentEpoch state).toNat ≤ epoch.toNat + 1 ∧
          epoch.toNat ≤ (getCurrentEpoch state).toNat + 1 ∧
          config.GLOAS_FORK_EPOCH.toNat ≤ epoch.toNat ∧
          (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1 <
            epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat then
        if indices.Nodup then
          (·.filterMap id) <$> indices.mapM (ptcDuty config state gloas epoch)
        else .error { code := 400, message := "Repeated validator index" }
      else .error (invalidEpoch epoch) := by
  unfold ptcDuties checkDutyEpoch
  by_cases empty : indices = []
  · simp [empty, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  have notEmpty : indices.isEmpty = false := List.isEmpty_eq_false_iff.mpr empty
  simp only [empty, notEmpty, Bool.false_eq_true, ↓reduceIte, UInt64.lt_iff_toNat_lt]
  by_cases ahead : epoch.toNat ≤ (getCurrentEpoch state).toNat + 1 <;>
  by_cases seeded : (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1 <
      epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat <;>
  by_cases behind : epoch.toNat + 1 < (getCurrentEpoch state).toNat <;>
  by_cases early : epoch.toNat < config.GLOAS_FORK_EPOCH.toNat <;>
  by_cases distinct : indices.Nodup <;>
  simp [ahead, seeded, behind, early, distinct, throw, throwThe, MonadExceptOf.throw, bind,
    Except.bind, pure, Except.pure, Functor.map, Except.map]

/-- Each attester duty is in the requested epoch, at a committee index below the count it gives.

That count is the number of committees per slot of the epoch. -/
theorem attesterDuties_epoch {state : BeaconState preset fork} {epoch : Epoch}
    {indices : List ValidatorIndex} {duties : List AttesterDuty}
    (computed : attesterDuties state epoch indices = .ok duties) {duty : AttesterDuty}
    (mem : duty ∈ duties) :
    computeEpochAtSlot preset duty.slot = epoch ∧
      duty.committeesAtSlot = getCommitteeCountPerSlot state epoch ∧
      duty.committeeIndex < duty.committeesAtSlot := by
  obtain ⟨index, -, made⟩ := attesterDuties_mem computed mem
  obtain ⟨committee, assigned, -, -, -, count⟩ := attesterDuty_some made
  obtain ⟨slotEpoch, below, -, -⟩ := getCommitteeAssignment_sound assigned
  exact ⟨slotEpoch, count, count ▸ below⟩

/-- Each proposer duty names the proposer at its offset, at that offset from the first slot. -/
private theorem proposerDuties_mem {state : BeaconState preset fork} {epoch : Epoch}
    {duties : List ProposerDuty} (computed : proposerDuties state epoch = .ok duties)
    {duty : ProposerDuty} (mem : duty ∈ duties) :
    ∃ (proposers : List ValidatorIndex) (start : Slot) (offset : Nat),
      epochProposers state epoch = .ok proposers ∧
      computeStartSlotAtEpoch preset epoch = .ok start ∧
      proposers[offset]? = some duty.validatorIndex ∧
      Uint64.addChecked start offset.toUInt64 = .ok duty.slot := by
  unfold proposerDuties at computed
  obtain ⟨proposers, proposersOk, computed⟩ := bind_ok_iff.mp computed
  obtain ⟨start, startOk, computed⟩ := bind_ok_iff.mp computed
  rw [mapError_ok_iff] at startOk
  obtain ⟨⟨proposer, offset⟩, member, made⟩ := mapM_ok_mem computed _ mem
  obtain ⟨inside, entry⟩ := List.mem_zipIdx' member
  obtain ⟨slot, slotOk, made⟩ := bind_ok_iff.mp made
  rw [mapError_ok_iff] at slotOk
  obtain ⟨validator, -, made⟩ := bind_ok_iff.mp made
  simp only [pure, Except.pure, Except.ok.injEq] at made
  subst made
  refine ⟨proposers, start, offset, proposersOk, startOk, ?_, slotOk⟩
  rw [List.getElem?_eq_getElem inside, ← entry]

/-- Slot steps that reach no epoch start keep the registry, the RANDAO mixes and the lookahead. -/
private theorem advanceSlots_kept {config : Config} {checks : SignatureChecks} :
    ∀ (count : Nat) {state after : BeaconState preset fork},
      advanceSlots config checks count state = .ok after →
      (∀ step, 1 ≤ step → step ≤ count →
        (state.slot.toNat + step) % preset.SLOTS_PER_EPOCH.toNat ≠ 0) →
      after.validators = state.validators ∧ after.randaoMixes = state.randaoMixes ∧
        after.proposerLookahead = state.proposerLookahead
  | 0, _, _, computed, _ => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨rfl, rfl, rfl⟩
  | count + 1, state, _, computed, inside => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨middle, first, rest⟩ := computed
    obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, middleEq⟩ := advanceSlot_ok first
    -- The next slot starts no epoch, so the step only caches the slot.
    have noEpoch : ¬next % preset.SLOTS_PER_EPOCH = 0 := by
      intro zero
      have natural := congrArg UInt64.toNat zero
      rw [UInt64.toNat_mod, sum] at natural
      exact inside 1 le_rfl (by omega) natural
    simp only [epochIfLast, noEpoch, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
    have middleSlot : middle.slot.toNat = state.slot.toNat + 1 := by
      rw [middleEq]
      exact sum
    have kept := advanceSlots_kept (state := middle) count rest fun step low high => by
      have shifted := inside (step + 1) (by omega) (by omega)
      rwa [middleSlot, show state.slot.toNat + 1 + step = state.slot.toNat + (step + 1) by omega]
    refine ⟨kept.1.trans ?_, kept.2.1.trans ?_, kept.2.2.trans ?_⟩ <;> rw [middleEq, cachedEq]

/-- A current proposer duty is in the epoch, and a state at its slot with that data names it. -/
private theorem proposerDuties_current {state : BeaconState preset fork}
    {duties : List ProposerDuty}
    (computed : proposerDuties state (getCurrentEpoch state) = .ok duties)
    {duty : ProposerDuty} (mem : duty ∈ duties) :
    duty.slot.toNat / preset.SLOTS_PER_EPOCH.toNat = (getCurrentEpoch state).toNat ∧
      ∀ other : BeaconState preset fork, other.slot = duty.slot →
        other.validators = state.validators → other.randaoMixes = state.randaoMixes →
        other.proposerLookahead = state.proposerLookahead →
        getBeaconProposerIndex other = .ok duty.validatorIndex := by
  obtain ⟨proposers, start, offset, proposersOk, startOk, entry, slotOk⟩ :=
    proposerDuties_mem computed mem
  obtain ⟨-, startNat⟩ := computeStartSlotAtEpoch_ok_iff.mp startOk
  unfold epochProposers at proposersOk
  -- The proposers of the current epoch are one per slot of the epoch, at most.
  have lt : offset < preset.SLOTS_PER_EPOCH.toNat := by
    by_cases fulu : .fusaka ≤ fork
    · simp [fulu, pure, Except.pure] at proposersOk
      subst proposersOk
      rw [List.getElem?_take] at entry
      split at entry
      · assumption
      · simp at entry
    · simp only [fulu, ↓reduceDIte, ↓reduceIte, bind_ok_iff, mapError_ok_iff, pure,
        Except.pure, Except.ok.injEq] at proposersOk
      obtain ⟨drawn, -, rfl⟩ := proposersOk
      simpa using (List.getElem?_eq_some_iff.mp entry).1
  have slotNat : duty.slot.toNat = start.toNat + offset := by
    obtain ⟨-, sum⟩ := Uint64.addChecked_ok_iff.mp slotOk
    have := preset.SLOTS_PER_EPOCH.toNat_lt
    rw [sum, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by omega
  have slotDiv :
      duty.slot.toNat / preset.SLOTS_PER_EPOCH.toNat = (getCurrentEpoch state).toNat := by
    rw [slotNat, startNat, Nat.mul_comm, Nat.mul_add_div positive, Nat.div_eq_of_lt lt]
    rfl
  have slotMod : duty.slot.toNat % preset.SLOTS_PER_EPOCH.toNat = offset := by
    rw [slotNat, startNat, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt lt]
  refine ⟨slotDiv, fun other otherSlot validators mixes lookahead => ?_⟩
  by_cases fulu : .fusaka ≤ fork
  · simp [fulu, pure, Except.pure] at proposersOk
    subst proposersOk
    have nonzero : preset.SLOTS_PER_EPOCH ≠ 0 := fun zero => by simp [zero] at positive
    have index : (other.slot % preset.SLOTS_PER_EPOCH).toNat = offset := by
      rw [UInt64.toNat_mod, otherSlot, slotMod]
    rw [List.getElem?_take_of_lt lt, Vector.getElem?_toList] at entry
    unfold getBeaconProposerIndex
    simp only [fulu, nonzero, ↓reduceDIte]
    simp only [lookahead, index, pure, Except.pure, Except.ok.injEq]
    exact (Vector.getElem?_eq_some_iff.mp entry).2
  · simp only [fulu, ↓reduceDIte, ↓reduceIte, bind_ok_iff, mapError_ok_iff, pure,
      Except.pure, Except.ok.injEq] at proposersOk
    obtain ⟨drawn, drawnOk, rfl⟩ := proposersOk
    have named : drawn[offset] = duty.validatorIndex := by
      simpa using (List.getElem?_eq_some_iff.mp entry).2
    have notGloas : ¬.glamsterdam ≤ fork := fun gloas =>
      fulu (Nat.le_trans (show Fork.fusaka.ctorIdx ≤ Fork.glamsterdam.ctorIdx by decide) gloas)
    -- The proposer at the offset is drawn from the active validators, with the seed of the slot.
    unfold getBeaconProposerIndices at drawnOk
    obtain ⟨active, activeOk, drawnOk⟩ := bind_ok_iff.mp drawnOk
    obtain ⟨seed, seedOk, drawnOk⟩ := bind_ok_iff.mp drawnOk
    unfold computeProposerIndices at drawnOk
    obtain ⟨start', startOk', drawnOk⟩ := bind_ok_iff.mp drawnOk
    rw [liftArith, mapError_ok_iff, startOk, Except.ok.injEq] at startOk'
    subst startOk'
    have drawnAt := vector_mapM_ok_getElem drawnOk offset lt
    simp only [Vector.getElem_range, liftArith, slotOk, Except.mapError, bind, Except.bind,
      computeSlotProposer, notGloas, ↓reduceIte, proposerCandidates, named] at drawnAt
    -- The other state reads the same epoch, seed, active validators and balances.
    have epoch : getCurrentEpoch other = getCurrentEpoch state := by
      rw [← UInt64.toNat_inj, getCurrentEpoch_toNat, otherSlot]
      exact slotDiv
    have seedOther : getSeed other (getCurrentEpoch state) DOMAIN_BEACON_PROPOSER =
        .ok seed := by
      rw [← seedOk]
      simp only [getSeed, getRandaoMix, mixes]
    have activeOther : getActiveValidatorIndicesChecked other (getCurrentEpoch state) =
        .ok active := by
      rw [← activeOk]
      simp only [getActiveValidatorIndicesChecked, validators]
    have drawOther : computeProposerIndex other active.toArray (proposerSlotSeed seed duty.slot) =
        .ok duty.validatorIndex := by
      rw [← drawnAt]
      simp only [computeProposerIndex, validators]
    unfold getBeaconProposerIndex
    simp only [fulu, ↓reduceDIte]
    simp only [epoch, seedOther, activeOther, bind, Except.bind]
    rw [← drawOther, otherSlot]
    rfl

/-- In the current epoch, each proposer duty after the slot of the state names its proposer.

The proposer is that of the state advanced to the slot of the duty. -/
theorem proposerDuties_beaconProposer {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {duties : List ProposerDuty}
    (computed : proposerDuties state (getCurrentEpoch state) = .ok duties)
    {duty : ProposerDuty} (mem : duty ∈ duties)
    (advanced : processSlots config checks state duty.slot = .ok after) :
    getBeaconProposerIndex after = .ok duty.validatorIndex := by
  obtain ⟨sameEpoch, named⟩ := proposerDuties_current computed mem
  obtain ⟨later, reached⟩ := processSlots_slot advanced
  have later := UInt64.lt_iff_toNat_lt.mp later
  have current := getCurrentEpoch_toNat state
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at advanced
  obtain ⟨_, _, advanced⟩ := advanced
  -- Every slot passed lies strictly inside the epoch of the duty, so no epoch step runs.
  obtain ⟨validators, mixes, lookahead⟩ := advanceSlots_kept _ advanced fun step low high => by
    intro zero
    have split := Nat.div_add_mod (state.slot.toNat + step) preset.SLOTS_PER_EPOCH.toNat
    have below := Nat.div_add_mod state.slot.toNat preset.SLOTS_PER_EPOCH.toNat
    have quotient : (state.slot.toNat + step) / preset.SLOTS_PER_EPOCH.toNat =
        (getCurrentEpoch state).toNat := by
      refine Nat.le_antisymm ?_ ?_
      · rw [← sameEpoch]
        exact Nat.div_le_div_right (by omega)
      · rw [current]
        exact Nat.div_le_div_right (by omega)
    rw [quotient, zero] at split
    rw [← current] at below
    omega
  exact named after reached validators mixes lookahead

/-- The proposer duty at the slot of the state names the proposer of the state. -/
theorem proposerDuties_current_slot {state : BeaconState preset fork}
    {duties : List ProposerDuty}
    (computed : proposerDuties state (getCurrentEpoch state) = .ok duties)
    {duty : ProposerDuty} (mem : duty ∈ duties) (now : duty.slot = state.slot) :
    getBeaconProposerIndex state = .ok duty.validatorIndex :=
  (proposerDuties_current computed mem).2 state now.symm rfl rfl rfl

/-- Each seat of a sync duty holds the key of the validator, in the committee of the period.

A sync duty has at least one seat. -/
theorem syncDuties_seats {state : BeaconState preset fork} {altair : .altair ≤ fork}
    {epoch : Epoch} {indices : List ValidatorIndex} {duties : List SyncDuty}
    (computed : syncDuties state altair epoch indices = .ok duties) {duty : SyncDuty}
    (mem : duty ∈ duties) :
    ∃ committee validator, syncCommitteeOf state altair epoch = .ok committee ∧
      getValidator state duty.validatorIndex = .ok validator ∧
      duty.pubkey = validator.pubkey ∧ duty.validatorSyncCommitteeIndices ≠ [] ∧
      ∀ seat ∈ duty.validatorSyncCommitteeIndices,
        committee.pubkeys.toList[seat.toNat]? = some validator.pubkey := by
  unfold syncDuties at computed
  by_cases empty : indices.isEmpty
  · simp [empty, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at computed
  simp only [empty, Bool.false_eq_true, ↓reduceIte] at computed
  obtain ⟨committee, committeeOk, computed⟩ := bind_ok_iff.mp computed
  obtain ⟨found, mapped, computed⟩ := bind_ok_iff.mp computed
  simp only [pure, Except.pure, Except.ok.injEq] at computed
  subst computed
  obtain ⟨_, member, rfl⟩ := List.mem_filterMap.mp mem
  obtain ⟨index, -, made⟩ := mapM_ok_mem mapped _ member
  unfold syncDuty at made
  obtain ⟨validator, validatorOk, made⟩ := bind_ok_iff.mp made
  unfold requestedValidator at validatorOk
  rw [mapError_ok_iff] at validatorOk
  refine ⟨committee, validator, committeeOk, ?_⟩
  -- The seats are those of the key in the committee, and there is at least one.
  have seated : duty.pubkey = validator.pubkey ∧ duty.validatorIndex = index ∧
      duty.validatorSyncCommitteeIndices = syncSeats committee validator.pubkey ∧
      syncSeats committee validator.pubkey ≠ [] := by
    split at made
    · simp [pure, Except.pure] at made
    · rename_i seats nonempty
      simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at made
      subst made
      exact ⟨rfl, rfl, rfl, nonempty⟩
  obtain ⟨key, named, seats, nonempty⟩ := seated
  refine ⟨named ▸ validatorOk, key, seats ▸ nonempty, fun seat inside => ?_⟩
  rw [seats] at inside
  simp only [syncSeats, List.mem_map, List.mem_filter, beq_iff_eq] at inside
  obtain ⟨⟨pubkey, position⟩, ⟨within, same⟩, rfl⟩ := inside
  obtain ⟨inside, entry⟩ := List.mem_zipIdx' within
  have small : position < 2 ^ 64 := by
    have := preset.SYNC_COMMITTEE_SIZE.toNat_lt
    simp only [Vector.length_toList] at inside
    omega
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt small]
  rw [List.getElem?_eq_getElem inside, ← entry]
  exact congrArg some same

/-- From Altair, a sync request with no index gets the error of an empty request, code 400. -/
theorem syncDuties_nil {state : BeaconState preset fork} {altair : .altair ≤ fork}
    {epoch : Epoch} :
    syncDuties state altair epoch [] = .error emptyIndices := by
  simp [syncDuties, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- In the first two epochs, the dependent root of a lag of one is the genesis root. -/
theorem dependentRoot_genesis {state : BeaconState preset fork} {epoch : Epoch}
    {genesisRoot : Root} (early : epoch.toNat ≤ 1) :
    dependentRoot state 1 epoch genesisRoot = .ok genesisRoot := by
  by_cases zero : epoch.toNat < 1
  · simp [dependentRoot, zero, pure, Except.pure]
  · have one : epoch = 1 := UInt64.toNat_inj.mp (by simp; omega)
    subst one
    have start : computeStartSlotAtEpoch preset 0 = .ok 0 :=
      computeStartSlotAtEpoch_ok_iff.mpr ⟨by simp, by simp⟩
    simp [dependentRoot, start, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- In the first epoch, the dependent root without a lag is the genesis root. -/
theorem dependentRoot_genesis_zero {state : BeaconState preset fork} {genesisRoot : Root} :
    dependentRoot state 0 0 genesisRoot = .ok genesisRoot := by
  have start : computeStartSlotAtEpoch preset 0 = .ok 0 :=
    computeStartSlotAtEpoch_ok_iff.mpr ⟨by simp, by simp⟩
  simp [dependentRoot, start, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- Past the underflow, the dependent root is the block root at the slot before the start.

The start is that of the epoch a lag before the given one, and must not be slot 0. -/
theorem dependentRoot_eq {state : BeaconState preset fork} {lag : Nat} {epoch : Epoch}
    {genesisRoot : Root} {start : Slot} (late : lag ≤ epoch.toNat)
    (started : computeStartSlotAtEpoch preset (epoch - lag.toUInt64) = .ok start)
    (positive : start ≠ 0) :
    dependentRoot state lag epoch genesisRoot =
      (getBlockRootAtSlot state (start - 1)).mapError (rootError epoch) := by
  simp [dependentRoot, Nat.not_lt.mpr late, started, positive, Except.mapError, bind,
    Except.bind]

/-- The first slot of the epoch a lag before the given one is that epoch times the epoch length.

It needs a lag of at most the given epoch, and that product to fit in 64 bits. -/
private theorem dependentRoot_start_exists {lag : Nat} {epoch : Epoch} (late : lag ≤ epoch.toNat)
    (fits : (epoch.toNat - lag) * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64) :
    ∃ start, computeStartSlotAtEpoch preset (epoch - lag.toUInt64) = .ok start ∧
      start.toNat = (epoch.toNat - lag) * preset.SLOTS_PER_EPOCH.toNat := by
  have epochSmall := epoch.toNat_lt
  have lagNat : lag.toUInt64.toNat = lag := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have difference : (epoch - lag.toUInt64).toNat = epoch.toNat - lag := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), lagNat]
  obtain ⟨start, startNat⟩ := Uint64.exists_toNat_eq fits
  exact ⟨start, computeStartSlotAtEpoch_ok_iff.mpr
    ⟨by rw [difference]; exact fits, by rw [difference, startNat]⟩, startNat⟩

/-- A dependent root whose slot has left the block roots gives the error of an invalid epoch.

The error has code 400.

Its slot is the one before the start of the epoch a lag before the given one.

It needs that start to be after slot 0.

It needs the slot of the state to be at least that start plus the length of the buffer of roots. -/
theorem dependentRoot_too_old {state : BeaconState preset fork} {lag : Nat} {epoch : Epoch}
    {genesisRoot : Root} (started : 0 < (epoch.toNat - lag) * preset.SLOTS_PER_EPOCH.toNat)
    (old : (epoch.toNat - lag) * preset.SLOTS_PER_EPOCH.toNat +
      preset.SLOTS_PER_HISTORICAL_ROOT.toNat ≤ state.slot.toNat) :
    dependentRoot state lag epoch genesisRoot = .error (invalidEpoch epoch) := by
  have late : lag < epoch.toNat := by
    refine Nat.lt_of_not_le fun early => ?_
    simp [Nat.sub_eq_zero_of_le early] at started
  have slotSmall := state.slot.toNat_lt
  obtain ⟨start, startOk, startNat⟩ :=
    dependentRoot_start_exists (preset := preset) late.le (by omega)
  have nonzero : start.toNat ≠ 0 := by omega
  have positive : start ≠ 0 := fun zero => nonzero (by rw [zero, UInt64.toNat_zero])
  -- The slot before the start is before the slot of the state, by more than the buffer.
  have one : (1 : UInt64) ≤ start := by
    rw [UInt64.le_iff_toNat_le]
    show 1 ≤ _
    omega
  have previous : (start - 1).toNat = start.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ one]
    rfl
  have before : start - 1 < state.slot := UInt64.lt_iff_toNat_lt.mpr (by omega)
  have bound : Uint64.addChecked (start - 1) preset.SLOTS_PER_HISTORICAL_ROOT =
      .ok (start - 1 + preset.SLOTS_PER_HISTORICAL_ROOT) :=
    Uint64.addChecked_ok_iff.mpr
      ⟨by omega, by rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]⟩
  have beyond : ¬state.slot ≤ start - 1 + preset.SLOTS_PER_HISTORICAL_ROOT := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [dependentRoot_eq late.le startOk positive]
  simp [getBlockRootAtSlot, before, liftArith, bound, beyond, Except.mapError, rootError,
    throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- The dependent root fails only with the error of an invalid epoch, code 400.

It needs the epoch a lag before the given one to start at a slot that fits in 64 bits.

It needs the slot of the state plus the length of the buffer of roots to be at most `2^64`. -/
theorem dependentRoot_error {state : BeaconState preset fork} {lag : Nat} {epoch : Epoch}
    {genesisRoot : Root} {error : ErrorMessage}
    (fits : (epoch.toNat - lag) * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64)
    (room : state.slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat ≤ 2 ^ 64)
    (failed : dependentRoot state lag epoch genesisRoot = .error error) :
    error = invalidEpoch epoch := by
  by_cases early : epoch.toNat < lag
  · simp [dependentRoot, early, pure, Except.pure] at failed
  have late : lag ≤ epoch.toNat := Nat.le_of_not_lt early
  obtain ⟨start, startOk, -⟩ := dependentRoot_start_exists late fits
  by_cases zero : start = 0
  · simp [dependentRoot, early, startOk, zero, Except.mapError, bind, Except.bind, pure,
      Except.pure] at failed
  rw [dependentRoot_eq late startOk zero] at failed
  obtain ⟨fault, read, rfl⟩ := mapError_eq_error failed
  rw [getBlockRootAtSlot_error room read]
  rfl

/-- Before Altair, the sync answer is the error with code 400 that names Altair.

A request with no index gets that error too, not the error of an empty request. -/
theorem dutiesResponse_sync_of_lt_altair {config : Config} {state : BeaconState preset fork}
    {epoch : Epoch} {indices : List ValidatorIndex} {genesisRoot : Root}
    (early : fork < .altair) :
    dutiesResponse config state .sync epoch indices genesisRoot =
      .error (beforeFork "sync duties" .altair) := by
  have notAltair : ¬.altair ≤ fork := Nat.not_le.2 early
  simp [dutiesResponse, notAltair]

/-- Before Gloas, the PTC answer is the error with code 400 that names Gloas.

A request with no index gets that error too, not the error of an empty request. -/
theorem dutiesResponse_ptc_of_lt_gloas {config : Config} {state : BeaconState preset fork}
    {epoch : Epoch} {indices : List ValidatorIndex} {genesisRoot : Root}
    (early : fork < .glamsterdam) :
    dutiesResponse config state .ptc epoch indices genesisRoot =
      .error (beforeFork "PTC duties" .glamsterdam) := by
  have notGloas : ¬.glamsterdam ≤ fork := Nat.not_le.2 early
  simp [dutiesResponse, notGloas]

/-- An attester, sync or PTC request with no index gets an error with code 400. -/
theorem dutiesResponse_nil {config : Config} {state : BeaconState preset fork}
    {kind : DutyKind} {epoch : Epoch} {genesisRoot : Root}
    (indexed : kind = .attester ∨ kind = .sync ∨ kind = .ptc) :
    ∃ error, dutiesResponse config state kind epoch [] genesisRoot = .error error ∧
      error.code = 400 := by
  rcases indexed with rfl | rfl | rfl
  · exact ⟨emptyIndices, by simp [dutiesResponse, attesterDuties_nil, bind, Except.bind], rfl⟩
  · by_cases altair : .altair ≤ fork
    · exact ⟨emptyIndices, by simp [dutiesResponse, altair, syncDuties_nil, bind, Except.bind],
        rfl⟩
    · exact ⟨_, dutiesResponse_sync_of_lt_altair (Nat.lt_of_not_le altair), rfl⟩
  · by_cases gloas : .glamsterdam ≤ fork
    · exact ⟨emptyIndices, by simp [dutiesResponse, gloas, ptcDuties_eq, bind, Except.bind],
        rfl⟩
    · exact ⟨_, dutiesResponse_ptc_of_lt_gloas (Nat.lt_of_not_le gloas), rfl⟩

/-- The duty lookup of a validator of the state succeeds when its committee assignment does. -/
private theorem attesterDuty_exists {state : BeaconState preset fork} {epoch : Epoch}
    {index : ValidatorIndex} (known : ∃ validator, getValidator state index = .ok validator)
    (assigned : ∃ assignment, getCommitteeAssignment state epoch index = .ok assignment) :
    ∃ duty, attesterDuty state epoch index = .ok duty := by
  obtain ⟨validator, validatorOk⟩ := known
  obtain ⟨assignment, assignedOk⟩ := assigned
  rcases assignment with _ | ⟨committee, committeeIndex, slot⟩ <;>
    simp [attesterDuty, requestedValidator, validatorOk, assignedOk, Except.mapError, bind,
      Except.bind, pure, Except.pure]

/-- An attester epoch whose dependent root has left the block roots gets an invalid epoch error.

The error has code 400.

It needs at least one index, each naming a validator of the state.

It needs the committee assignment of each requested validator to succeed.

It needs the epoch before the requested one to start after slot 0.

It needs the slot of the state to be at least that start plus the length of the buffer of roots. -/
theorem dutiesResponse_attester_too_old {config : Config} {state : BeaconState preset fork}
    {epoch : Epoch} {index : ValidatorIndex} {rest : List ValidatorIndex} {genesisRoot : Root}
    (known : ∀ member ∈ index :: rest, ∃ validator, getValidator state member = .ok validator)
    (assigned : ∀ member ∈ index :: rest, ∃ assignment,
      getCommitteeAssignment state epoch member = .ok assignment)
    (started : 0 < (epoch.toNat - 1) * preset.SLOTS_PER_EPOCH.toNat)
    (old : (epoch.toNat - 1) * preset.SLOTS_PER_EPOCH.toNat +
      preset.SLOTS_PER_HISTORICAL_ROOT.toNat ≤ state.slot.toNat) :
    dutiesResponse config state .attester epoch (index :: rest) genesisRoot =
      .error (invalidEpoch epoch) := by
  rcases checkDutyEpoch_cases state epoch with checked | refused
  · obtain ⟨found, mapped⟩ := mapM_exists_ok (f := attesterDuty state epoch)
      fun member inside => attesterDuty_exists (known member inside) (assigned member inside)
    simp [dutiesResponse, attesterDuties, checked, mapped, dependentRoot_too_old started old,
      bind, Except.bind, pure, Except.pure]
  · simp [dutiesResponse, attesterDuties, refused, bind, Except.bind]

/-- The lookup of an index that names no validator gets the error of an invalid index. -/
private theorem requestedValidator_unknown {state : BeaconState preset fork}
    {index : ValidatorIndex} (unknown : state.validators.data.size ≤ index.toNat) :
    requestedValidator state index = .error (invalidIndex index) := by
  simp [requestedValidator, getValidator, Array.getElem?_eq_none unknown, Except.mapError]

/-- An attester index that names no validator gets the error of an invalid index, code 400.

It needs the epoch to be at most the next one, with its seed still in the mixes of the state.

It needs each earlier index to name a validator whose committee assignment succeeds. -/
theorem dutiesResponse_attester_unknown {config : Config} {state : BeaconState preset fork}
    {epoch : Epoch} {before after : List ValidatorIndex} {index : ValidatorIndex}
    {genesisRoot : Root} (near : epoch.toNat ≤ (getCurrentEpoch state).toNat + 1)
    (seeded : (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1 <
      epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (known : ∀ member ∈ before, ∃ validator, getValidator state member = .ok validator)
    (assigned : ∀ member ∈ before, ∃ assignment,
      getCommitteeAssignment state epoch member = .ok assignment)
    (unknown : state.validators.data.size ≤ index.toNat) :
    dutiesResponse config state .attester epoch (before ++ index :: after) genesisRoot =
      .error (invalidIndex index) := by
  obtain ⟨found, mapped⟩ := mapM_exists_ok (f := attesterDuty state epoch)
    fun member inside => attesterDuty_exists (known member inside) (assigned member inside)
  have failed : attesterDuty state epoch index = .error (invalidIndex index) := by
    simp [attesterDuty, requestedValidator_unknown unknown, bind, Except.bind]
  simp [dutiesResponse, attesterDuties, checkDutyEpoch_ok near seeded, mapped, failed, bind,
    Except.bind]

/-- The sync committee of the current or the next period of the state is found. -/
private theorem syncCommitteeOf_exists {state : BeaconState preset fork}
    (altair : .altair ≤ fork) {epoch : Epoch}
    (period : (computeSyncCommitteePeriod preset (getCurrentEpoch state)).toNat ≤
        (computeSyncCommitteePeriod preset epoch).toNat ∧
      (computeSyncCommitteePeriod preset epoch).toNat ≤
        (computeSyncCommitteePeriod preset (getCurrentEpoch state)).toNat + 1) :
    ∃ committee, syncCommitteeOf state altair epoch = .ok committee := by
  unfold syncCommitteeOf
  by_cases same : computeSyncCommitteePeriod preset epoch =
      computeSyncCommitteePeriod preset (getCurrentEpoch state)
  · simp [same]
  · have next : (computeSyncCommitteePeriod preset epoch).toNat =
        (computeSyncCommitteePeriod preset (getCurrentEpoch state)).toNat + 1 := by
      have := mt UInt64.toNat_inj.mp same
      omega
    simp [same, next]

/-- The sync duty lookup of a validator of the state succeeds. -/
private theorem syncDuty_exists {state : BeaconState preset fork}
    {committee : SyncCommittee preset} {index : ValidatorIndex}
    (known : ∃ validator, getValidator state index = .ok validator) :
    ∃ duty, syncDuty state committee index = .ok duty := by
  obtain ⟨validator, validatorOk⟩ := known
  simp only [syncDuty, requestedValidator, validatorOk, Except.mapError, bind, Except.bind]
  split <;> exact ⟨_, rfl⟩

/-- A sync index that names no validator gets the error of an invalid index, code 400.

It needs a fork from Altair, and an epoch in the current or the next period of the state.

It needs each earlier index to name a validator. -/
theorem dutiesResponse_sync_unknown {config : Config} {state : BeaconState preset fork}
    {epoch : Epoch} {before after : List ValidatorIndex} {index : ValidatorIndex}
    {genesisRoot : Root} (altair : .altair ≤ fork)
    (period : (computeSyncCommitteePeriod preset (getCurrentEpoch state)).toNat ≤
        (computeSyncCommitteePeriod preset epoch).toNat ∧
      (computeSyncCommitteePeriod preset epoch).toNat ≤
        (computeSyncCommitteePeriod preset (getCurrentEpoch state)).toNat + 1)
    (known : ∀ member ∈ before, ∃ validator, getValidator state member = .ok validator)
    (unknown : state.validators.data.size ≤ index.toNat) :
    dutiesResponse config state .sync epoch (before ++ index :: after) genesisRoot =
      .error (invalidIndex index) := by
  obtain ⟨committee, committeeOk⟩ := syncCommitteeOf_exists altair period
  obtain ⟨found, mapped⟩ := mapM_exists_ok (f := syncDuty state committee)
    fun member inside => syncDuty_exists (known member inside)
  have failed : syncDuty state committee index = .error (invalidIndex index) := by
    simp [syncDuty, requestedValidator_unknown unknown, bind, Except.bind]
  simp [dutiesResponse, altair, syncDuties, committeeOk, mapped, failed, bind, Except.bind]

/-- A sync epoch outside the current and next periods of the state gets the error with code 400.

The error says that the epoch is outside the sync committee period of the state.

It needs a fork from Altair, and at least one index. -/
theorem dutiesResponse_sync_outside {config : Config} {state : BeaconState preset fork}
    {epoch : Epoch} {index : ValidatorIndex} {rest : List ValidatorIndex} {genesisRoot : Root}
    (altair : .altair ≤ fork)
    (outside : (computeSyncCommitteePeriod preset epoch).toNat <
        (computeSyncCommitteePeriod preset (getCurrentEpoch state)).toNat ∨
      (computeSyncCommitteePeriod preset (getCurrentEpoch state)).toNat + 1 <
        (computeSyncCommitteePeriod preset epoch).toNat) :
    dutiesResponse config state .sync epoch (index :: rest) genesisRoot = .error
      { code := 400, message := "Epoch is outside the sync committee period of the state" } := by
  have other : computeSyncCommitteePeriod preset epoch ≠
      computeSyncCommitteePeriod preset (getCurrentEpoch state) := fun same => by
    rw [same] at outside
    omega
  have notNext : (computeSyncCommitteePeriod preset epoch).toNat ≠
      (computeSyncCommitteePeriod preset (getCurrentEpoch state)).toNat + 1 := by
    omega
  simp [dutiesResponse, altair, syncDuties, syncCommitteeOf, other, notNext, bind, Except.bind]

/-- Each refusal of the sync answer is one of four errors.

Two are the errors of a state before Altair and of an empty request.

The third is the error of an epoch outside the current and next periods of the state.

The fourth is the error of a requested index that names no validator of the state. -/
theorem dutiesResponse_sync_error {config : Config} {state : BeaconState preset fork}
    {epoch : Epoch} {indices : List ValidatorIndex} {genesisRoot : Root} {error : ErrorMessage}
    (failed : dutiesResponse config state .sync epoch indices genesisRoot = .error error) :
    error = beforeFork "sync duties" .altair ∨ error = emptyIndices ∨
      error = { code := 400,
                message := "Epoch is outside the sync committee period of the state" } ∨
      ∃ index ∈ indices, error = invalidIndex index := by
  by_cases altair : .altair ≤ fork
  case neg =>
    rw [dutiesResponse_sync_of_lt_altair (Nat.lt_of_not_le altair)] at failed
    cases failed
    exact .inl rfl
  simp only [dutiesResponse, altair, ↓reduceDIte] at failed
  rcases bind_eq_error failed with refused | ⟨_, -, failed⟩
  case inr => cases failed
  unfold syncDuties at refused
  by_cases empty : indices.isEmpty
  · simp [empty, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at refused
    exact .inr (.inl refused.symm)
  simp only [empty, Bool.false_eq_true, ↓reduceIte] at refused
  rcases bind_eq_error refused with outside | ⟨committee, -, refused⟩
  · -- The committee of a period fails only outside the current and next periods.
    by_cases same : computeSyncCommitteePeriod preset epoch =
        computeSyncCommitteePeriod preset (getCurrentEpoch state)
    · simp [syncCommitteeOf, same] at outside
    by_cases next : (computeSyncCommitteePeriod preset epoch).toNat =
        (computeSyncCommitteePeriod preset (getCurrentEpoch state)).toNat + 1
    · simp [syncCommitteeOf, same, next] at outside
    simp [syncCommitteeOf, same, next] at outside
    exact .inr (.inr (.inl outside.symm))
  rcases bind_eq_error refused with unknown | ⟨_, -, refused⟩
  · -- Each duty fails only by an index that names no validator.
    obtain ⟨index, member, step⟩ := exists_mem_of_mapM_error unknown
    unfold syncDuty at step
    rcases bind_eq_error step with named | ⟨_, -, step⟩
    · obtain ⟨_, -, rfl⟩ := mapError_eq_error named
      exact .inr (.inr (.inr ⟨index, member, rfl⟩))
    · split at step <;> cases step
  · cases refused

/-- The sync answer fails only with code 400. -/
theorem dutiesResponse_sync_error_code {config : Config} {state : BeaconState preset fork}
    {epoch : Epoch} {indices : List ValidatorIndex} {genesisRoot : Root} {error : ErrorMessage}
    (failed : dutiesResponse config state .sync epoch indices genesisRoot = .error error) :
    error.code = 400 := by
  rcases dutiesResponse_sync_error failed with rfl | rfl | rfl | ⟨_, -, rfl⟩ <;> rfl

/-- The PTC duty lookup of a validator of the state succeeds when its PTC assignment does. -/
private theorem ptcDuty_exists {config : Config} {state : BeaconState preset fork}
    {gloas : .glamsterdam ≤ fork} {epoch : Epoch} {index : ValidatorIndex}
    (known : ∃ validator, getValidator state index = .ok validator)
    (assigned : ∃ slot, getPtcAssignment config state gloas epoch index = .ok slot) :
    ∃ duty, ptcDuty config state gloas epoch index = .ok duty := by
  obtain ⟨validator, validatorOk⟩ := known
  obtain ⟨slot, slotOk⟩ := assigned
  rcases slot with _ | slot <;>
    simp [ptcDuty, requestedValidator, validatorOk, slotOk, Except.mapError, bind, Except.bind,
      pure, Except.pure]

/-- A PTC index that names no validator gets the error of an invalid index, code 400.

It needs a fork from Gloas, and no repeated index.

The epoch must lie from the previous one to the next, and not before the Gloas fork epoch.

The mixes of the state must still hold its seed.

It needs each earlier index to name a validator whose PTC assignment succeeds. -/
theorem dutiesResponse_ptc_unknown {config : Config} {state : BeaconState preset fork}
    {epoch : Epoch} {before after : List ValidatorIndex} {index : ValidatorIndex}
    {genesisRoot : Root} (gloas : .glamsterdam ≤ fork)
    (window : (getCurrentEpoch state).toNat ≤ epoch.toNat + 1 ∧
      epoch.toNat ≤ (getCurrentEpoch state).toNat + 1 ∧
      config.GLOAS_FORK_EPOCH.toNat ≤ epoch.toNat ∧
      (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1 <
        epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (distinct : (before ++ index :: after).Nodup)
    (known : ∀ member ∈ before, ∃ validator, getValidator state member = .ok validator)
    (assigned : ∀ member ∈ before, ∃ slot,
      getPtcAssignment config state gloas epoch member = .ok slot)
    (unknown : state.validators.data.size ≤ index.toNat) :
    dutiesResponse config state .ptc epoch (before ++ index :: after) genesisRoot =
      .error (invalidIndex index) := by
  obtain ⟨found, mapped⟩ := mapM_exists_ok (f := ptcDuty config state gloas epoch)
    fun member inside => ptcDuty_exists (known member inside) (assigned member inside)
  have failed : ptcDuty config state gloas epoch index = .error (invalidIndex index) := by
    simp [ptcDuty, requestedValidator_unknown unknown, bind, Except.bind]
  have mappedAll : (before ++ index :: after).mapM (ptcDuty config state gloas epoch) =
      .error (invalidIndex index) := by
    simp [mapped, failed, bind, Except.bind]
  have nonempty : before ++ index :: after ≠ [] := by simp
  have refused : ptcDuties config state gloas epoch (before ++ index :: after) =
      .error (invalidIndex index) := by
    rw [ptcDuties_eq, ite_eq_right nonempty, ite_eq_left window, ite_eq_left distinct, mappedAll]
    rfl
  simp [dutiesResponse, gloas, refused, bind, Except.bind]

/-- A proposer epoch other than the current one gets the error of an invalid epoch, code 400.

It needs the first proposer answer, or the second on a fork before Fulu.

The first answer refuses the next epoch even from Fulu, where the lookahead holds its proposers. -/
theorem dutiesResponse_proposer_not_current {config : Config} {state : BeaconState preset fork}
    {kind : DutyKind} {epoch : Epoch} {indices : List ValidatorIndex} {genesisRoot : Root}
    (version : kind = .proposerV1 ∨ (kind = .proposerV2 ∧ fork < .fusaka))
    (other : epoch ≠ getCurrentEpoch state) :
    dutiesResponse config state kind epoch indices genesisRoot = .error (invalidEpoch epoch) := by
  rcases version with rfl | ⟨rfl, early⟩
  · simp [dutiesResponse, other, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  · have notFulu : ¬.fusaka ≤ fork := Nat.not_le.2 early
    simp [dutiesResponse, proposerDuties, epochProposers, notFulu, other, throw, throwThe,
      MonadExceptOf.throw, bind, Except.bind]

/-- The second proposer answer refuses an epoch before the current one or past the seed lookahead.

The error is that of an invalid epoch, code 400.

It holds on every fork, as before Fulu that answer serves the current epoch alone. -/
theorem dutiesResponse_proposer_outside {config : Config} {state : BeaconState preset fork}
    {epoch : Epoch} {indices : List ValidatorIndex} {genesisRoot : Root}
    (outside : epoch.toNat < (getCurrentEpoch state).toNat ∨
      (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat < epoch.toNat) :
    dutiesResponse config state .proposerV2 epoch indices genesisRoot =
      .error (invalidEpoch epoch) := by
  by_cases fulu : .fusaka ≤ fork
  · rcases outside with behind | ahead
    · have notAfter : ¬getCurrentEpoch state ≤ epoch := by
        rw [UInt64.le_iff_toNat_le]
        omega
      simp [dutiesResponse, proposerDuties, epochProposers, fulu, notAfter, throw, throwThe,
        MonadExceptOf.throw, bind, Except.bind]
    · have far :
          ¬epoch.toNat ≤ (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat :=
        Nat.not_le.2 ahead
      simp [dutiesResponse, proposerDuties, epochProposers, fulu, far, throw, throwThe,
        MonadExceptOf.throw, bind, Except.bind]
  · have other : epoch ≠ getCurrentEpoch state := fun same => by
      rw [same] at outside
      omega
    exact dutiesResponse_proposer_not_current (.inr ⟨rfl, Nat.lt_of_not_le fulu⟩) other

/-- Both proposer answers give code 500 to a current epoch with no active validator.

The draw of its first slot has no candidate, so that epoch gets code 500, not code 400.

It needs a fork before Fulu, where the answers draw the proposers.

It needs an epoch of at least one slot. -/
theorem dutiesResponse_proposer_no_active {config : Config} {state : BeaconState preset fork}
    {kind : DutyKind} {indices : List ValidatorIndex} {genesisRoot : Root}
    (version : kind = .proposerV1 ∨ kind = .proposerV2) (early : fork < .fusaka)
    (positive : preset.SLOTS_PER_EPOCH ≠ 0)
    (idle : getActiveValidatorIndices state (getCurrentEpoch state) = []) :
    ∃ error, dutiesResponse config state kind (getCurrentEpoch state) indices genesisRoot =
      .error error ∧ error.code = 500 := by
  have notFulu : ¬.fusaka ≤ fork := Nat.not_le.2 early
  have notGloas : ¬.glamsterdam ≤ fork := fun gloas => notFulu (Nat.le_trans (by decide) gloas)
  -- The draw of the first slot has no candidate, so the proposers of the epoch fail.
  obtain ⟨fault, drawFailed⟩ :
      ∃ fault, getBeaconProposerIndices state (getCurrentEpoch state) = .error fault := by
    cases drawn : getBeaconProposerIndices state (getCurrentEpoch state) with
    | error fault => exact ⟨fault, rfl⟩
    | ok proposers =>
      unfold getBeaconProposerIndices computeProposerIndices at drawn
      obtain ⟨active, activeOk, drawn⟩ := bind_ok_iff.mp drawn
      obtain ⟨_, -, drawn⟩ := bind_ok_iff.mp drawn
      obtain ⟨_, -, drawn⟩ := bind_ok_iff.mp drawn
      have first := vector_mapM_ok_getElem drawn 0
        (Nat.pos_of_ne_zero fun zero => positive (UInt64.toNat_inj.mp (by simpa using zero)))
      obtain ⟨_, -, first⟩ := bind_ok_iff.mp first
      rw [getActiveValidatorIndicesChecked_ok activeOk, idle] at first
      simp [computeSlotProposer, notGloas, proposerCandidates, computeProposerIndex, throw,
        throwThe, MonadExceptOf.throw, bind, Except.bind] at first
  refine ⟨internalError (reprStr fault), ?_, rfl⟩
  rcases version with rfl | rfl <;>
    simp [dutiesResponse, proposerDuties, epochProposers, notFulu, drawFailed, Except.mapError,
      bind, Except.bind]

/-- The proposers of an epoch are the entries of the lookahead at the slots of that epoch.

It needs a fork from Fulu, and an epoch from the current one to the end of the seed lookahead. -/
private theorem epochProposers_lookahead {state : BeaconState preset fork}
    (fulu : .fusaka ≤ fork) {epoch : Epoch}
    (served : (getCurrentEpoch state).toNat ≤ epoch.toNat ∧
      epoch.toNat ≤ (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat) :
    epochProposers state epoch = .ok (((state.proposerLookahead fulu).toList.drop
      ((epoch.toNat - (getCurrentEpoch state).toNat) * preset.SLOTS_PER_EPOCH.toNat)).take
      preset.SLOTS_PER_EPOCH.toNat) := by
  have after : getCurrentEpoch state ≤ epoch := UInt64.le_iff_toNat_le.mpr served.1
  simp [epochProposers, fulu, after, served.2, pure, Except.pure]

/-- Once the proposers of an epoch are read, the proposer duties fail only with code 500. -/
private theorem proposerDuties_error_code {state : BeaconState preset fork} {epoch : Epoch}
    {proposers : List ValidatorIndex} {error : ErrorMessage}
    (read : epochProposers state epoch = .ok proposers)
    (failed : proposerDuties state epoch = .error error) : error.code = 500 := by
  unfold proposerDuties at failed
  rcases bind_eq_error failed with refused | ⟨_, -, failed⟩
  · rw [read] at refused
    cases refused
  rcases bind_eq_error failed with refused | ⟨_, -, failed⟩
  · obtain ⟨_, -, rfl⟩ := mapError_eq_error refused
    rfl
  -- Each duty fails at its slot or at its validator, both with code 500.
  obtain ⟨⟨proposer, offset⟩, -, step⟩ := exists_mem_of_mapM_error failed
  dsimp only at step
  rcases bind_eq_error step with refused | ⟨_, -, step⟩
  · obtain ⟨_, -, rfl⟩ := mapError_eq_error refused
    rfl
  rcases bind_eq_error step with refused | ⟨_, -, step⟩
  · obtain ⟨_, -, rfl⟩ := mapError_eq_error refused
    rfl
  · cases step

/-- A proposer answer reads the duties of its epoch, then a dependent root.

The duties read the lookahead at the slots of that epoch, whose start fits in 64 bits.

It needs a fork from Fulu, where the answers read the proposers from the lookahead.

It needs the first answer at the current epoch, or the second at an epoch of the lookahead.

It needs the slots of the epoch to fit in 64 bits. -/
private theorem dutiesResponse_proposer_lag_exists {config : Config}
    {state : BeaconState preset fork} {kind : DutyKind} {epoch : Epoch}
    {indices : List ValidatorIndex} {genesisRoot : Root} (fulu : .fusaka ≤ fork)
    (served : kind = .proposerV1 ∧ epoch = getCurrentEpoch state ∨
      kind = .proposerV2 ∧ (getCurrentEpoch state).toNat ≤ epoch.toNat ∧
        epoch.toNat ≤ (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat)
    (slotsFit : (epoch.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat ≤ 2 ^ 64) :
    ∃ lag, dutiesResponse config state kind epoch indices genesisRoot =
        (do
          let duties ← proposerDuties state epoch
          return { dependentRoot := some (← dependentRoot state lag epoch genesisRoot),
                   data := .arr (duties.map ProposerDuty.toJson).toArray }) ∧
      epochProposers state epoch = .ok (((state.proposerLookahead fulu).toList.drop
        ((epoch.toNat - (getCurrentEpoch state).toNat) * preset.SLOTS_PER_EPOCH.toNat)).take
        preset.SLOTS_PER_EPOCH.toNat) ∧
      epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 := by
  have window : (getCurrentEpoch state).toNat ≤ epoch.toNat ∧
      epoch.toNat ≤ (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat := by
    rcases served with ⟨-, rfl⟩ | ⟨-, window⟩
    · omega
    · exact window
  have startFits : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 := by
    rw [Nat.succ_mul] at slotsFit
    rcases Nat.eq_zero_or_pos preset.SLOTS_PER_EPOCH.toNat with zero | positive
    · rw [zero, Nat.mul_zero]
      exact Nat.two_pow_pos 64
    · omega
  rcases served with ⟨rfl, rfl⟩ | ⟨rfl, -⟩
  · exact ⟨0, by simp [dutiesResponse], epochProposers_lookahead fulu window, startFits⟩
  · exact ⟨1, rfl, epochProposers_lookahead fulu window, startFits⟩

/-- A proposer answer gets code 500 exactly when the lookahead names an index past the registry.

That index is the entry of the lookahead at a slot of the requested epoch.

It needs a fork from Fulu, where the answers read the proposers from the lookahead.

It needs the first answer at the current epoch, or the second at an epoch of the lookahead.

It needs the slots of the epoch to fit in 64 bits.

It needs the slot of the state plus the length of the buffer of roots to be at most `2^64`. -/
theorem dutiesResponse_proposer_internal_iff {config : Config} {state : BeaconState preset fork}
    {kind : DutyKind} {epoch : Epoch} {indices : List ValidatorIndex} {genesisRoot : Root}
    (fulu : .fusaka ≤ fork)
    (served : kind = .proposerV1 ∧ epoch = getCurrentEpoch state ∨
      kind = .proposerV2 ∧ (getCurrentEpoch state).toNat ≤ epoch.toNat ∧
        epoch.toNat ≤ (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat)
    (slotsFit : (epoch.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat ≤ 2 ^ 64)
    (room : state.slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat ≤ 2 ^ 64) :
    (∃ error, dutiesResponse config state kind epoch indices genesisRoot = .error error ∧
        error.code = 500) ↔
      ∃ offset < preset.SLOTS_PER_EPOCH.toNat, ∃ proposer,
        (state.proposerLookahead fulu)[(epoch.toNat - (getCurrentEpoch state).toNat) *
          preset.SLOTS_PER_EPOCH.toNat + offset]? = some proposer ∧
        state.validators.data.size ≤ proposer.toNat := by
  -- Both answers read the proposer duties, then a dependent root.
  obtain ⟨lag, answer, read, startFits⟩ := dutiesResponse_proposer_lag_exists (config := config)
    (indices := indices) (genesisRoot := genesisRoot) fulu served slotsFit
  rw [Nat.succ_mul] at slotsFit
  obtain ⟨start, startNat⟩ := Uint64.exists_toNat_eq startFits
  have startOk : computeStartSlotAtEpoch preset epoch = .ok start :=
    computeStartSlotAtEpoch_ok_iff.mpr ⟨startFits, startNat⟩
  -- The slot of each proposer of the epoch fits, and the root fails only with code 400.
  have slotOk : ∀ offset < preset.SLOTS_PER_EPOCH.toNat,
      Uint64.addChecked start offset.toUInt64 = .ok (start + offset.toUInt64) := by
    intro offset offsetLt
    have small : offset < 2 ^ 64 := Nat.lt_trans offsetLt preset.SLOTS_PER_EPOCH.toNat_lt
    refine Uint64.addChecked_of_lt ?_
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt small, startNat]
    omega
  have rootCode : ∀ error, dependentRoot state lag epoch genesisRoot = .error error →
      error.code = 400 := fun error failed => by
    rw [dependentRoot_error (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
      startFits) room failed]
    rfl
  have entryOf : ∀ proposer offset, (proposer, offset) ∈
      (((state.proposerLookahead fulu).toList.drop
        ((epoch.toNat - (getCurrentEpoch state).toNat) * preset.SLOTS_PER_EPOCH.toNat)).take
        preset.SLOTS_PER_EPOCH.toNat).zipIdx ↔
      offset < preset.SLOTS_PER_EPOCH.toNat ∧
        (state.proposerLookahead fulu)[(epoch.toNat - (getCurrentEpoch state).toNat) *
          preset.SLOTS_PER_EPOCH.toNat + offset]? = some proposer := by
    intro proposer offset
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_take, List.getElem?_drop,
      Vector.getElem?_toList]
    by_cases lt : offset < preset.SLOTS_PER_EPOCH.toNat <;> simp [lt]
  constructor
  · rintro ⟨error, failed, code⟩
    rw [answer] at failed
    rcases bind_eq_error failed with refused | ⟨_, -, failed⟩
    · -- The duties fail at a slot whose proposer names no validator.
      unfold proposerDuties at refused
      rcases bind_eq_error refused with bad | ⟨proposers, readOk, refused⟩
      · rw [read] at bad
        cases bad
      rw [read] at readOk
      obtain rfl := Except.ok.inj readOk
      rcases bind_eq_error refused with bad | ⟨started, startedOk, refused⟩
      · rw [startOk] at bad
        cases bad
      rw [mapError_ok_iff, startOk] at startedOk
      obtain rfl := Except.ok.inj startedOk
      obtain ⟨⟨proposer, offset⟩, member, step⟩ := exists_mem_of_mapM_error refused
      obtain ⟨offsetLt, entry⟩ := (entryOf proposer offset).mp member
      dsimp only at step
      rcases bind_eq_error step with bad | ⟨_, -, step⟩
      · rw [slotOk offset offsetLt] at bad
        cases bad
      rcases bind_eq_error step with bad | ⟨_, -, step⟩
      · obtain ⟨_, named, -⟩ := mapError_eq_error bad
        refine ⟨offset, offsetLt, proposer, entry, Nat.le_of_not_lt fun inside => ?_⟩
        rw [getValidator_eq_ok_iff.mpr (Array.getElem?_eq_getElem inside)] at named
        cases named
      · cases step
    · -- With the duties, only the dependent root can fail, and it does with code 400.
      rcases bind_eq_error failed with refused | ⟨_, -, failed⟩
      · have := rootCode _ refused
        omega
      · cases failed
  · rintro ⟨offset, offsetLt, proposer, entry, past⟩
    cases dutiesOk : proposerDuties state epoch with
    | error error =>
      refine ⟨error, ?_, proposerDuties_error_code read dutiesOk⟩
      rw [answer, dutiesOk]
      rfl
    | ok duties =>
      -- The duty at the offset reads the validator of the proposer, which fails.
      unfold proposerDuties at dutiesOk
      obtain ⟨proposers, readOk, dutiesOk⟩ := bind_ok_iff.mp dutiesOk
      rw [read] at readOk
      obtain rfl := Except.ok.inj readOk
      obtain ⟨_, -, dutiesOk⟩ := bind_ok_iff.mp dutiesOk
      obtain ⟨_, step⟩ := mapM_ok_of_mem dutiesOk (proposer, offset)
        ((entryOf proposer offset).mpr ⟨offsetLt, entry⟩)
      dsimp only at step
      obtain ⟨_, -, step⟩ := bind_ok_iff.mp step
      obtain ⟨_, named, -⟩ := bind_ok_iff.mp step
      rw [mapError_ok_iff, getValidator_eq_ok_iff, Array.getElem?_eq_none past] at named
      cases named

/-- A proposer answer fails only with the error of an invalid epoch, code 400.

It needs a fork from Fulu, where the answers read the proposers from the lookahead.

It needs one of the two proposer answers.

It needs the slots of the epoch to fit in 64 bits.

It needs the slot of the state plus the length of the buffer of roots to be at most `2^64`.

It needs the lookahead to name only validators of the state.

It holds even with no active validator, unlike an answer before Fulu. -/
theorem dutiesResponse_proposer_error {config : Config}
    {state : BeaconState preset fork} {kind : DutyKind} {epoch : Epoch}
    {indices : List ValidatorIndex} {genesisRoot : Root} {error : ErrorMessage}
    (fulu : .fusaka ≤ fork) (version : kind = .proposerV1 ∨ kind = .proposerV2)
    (slotsFit : (epoch.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat ≤ 2 ^ 64)
    (room : state.slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat ≤ 2 ^ 64)
    (known : ∀ proposer ∈ state.proposerLookahead fulu,
      proposer.toNat < state.validators.data.size)
    (failed : dutiesResponse config state kind epoch indices genesisRoot = .error error) :
    error = invalidEpoch epoch := by
  by_cases served : kind = .proposerV1 ∧ epoch = getCurrentEpoch state ∨
      kind = .proposerV2 ∧ (getCurrentEpoch state).toNat ≤ epoch.toNat ∧
        epoch.toNat ≤ (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat
  · obtain ⟨lag, answer, read, startFits⟩ := dutiesResponse_proposer_lag_exists (config := config)
      (indices := indices) (genesisRoot := genesisRoot) fulu served slotsFit
    rw [answer] at failed
    rcases bind_eq_error failed with refused | ⟨_, -, failed⟩
    · -- The duties fail only with code 500, which a lookahead of validators of the state excludes.
      obtain ⟨_, -, proposer, entry, past⟩ := (dutiesResponse_proposer_internal_iff
        (config := config) (indices := indices) (genesisRoot := genesisRoot) fulu served slotsFit
        room).mp ⟨error, by rw [answer, refused]; rfl, proposerDuties_error_code read refused⟩
      have inside := known proposer (Vector.mem_of_getElem? entry)
      omega
    -- With the duties, only the dependent root can fail, with the error of an invalid epoch.
    rcases bind_eq_error failed with refused | ⟨_, -, failed⟩
    · exact dependentRoot_error (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
        startFits) room refused
    · cases failed
  -- The answer refuses any other epoch with the error of an invalid epoch.
  rcases version with rfl | rfl
  · have other : epoch ≠ getCurrentEpoch state := fun same => served (.inl ⟨rfl, same⟩)
    rw [dutiesResponse_proposer_not_current (.inl rfl) other] at failed
    cases failed
    rfl
  · have outside : epoch.toNat < (getCurrentEpoch state).toNat ∨
        (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat < epoch.toNat := by
      by_cases low : epoch.toNat < (getCurrentEpoch state).toNat
      · exact .inl low
      · exact .inr (Nat.lt_of_not_le fun high => served (.inr ⟨rfl, Nat.le_of_not_lt low, high⟩))
    rw [dutiesResponse_proposer_outside outside] at failed
    cases failed
    rfl

/-- A proposer answer fails only with code 400.

It needs a fork from Fulu, where the answers read the proposers from the lookahead.

It needs one of the two proposer answers.

It needs the slots of the epoch to fit in 64 bits.

It needs the slot of the state plus the length of the buffer of roots to be at most `2^64`.

It needs the lookahead to name only validators of the state. -/
theorem dutiesResponse_proposer_error_code {config : Config}
    {state : BeaconState preset fork} {kind : DutyKind} {epoch : Epoch}
    {indices : List ValidatorIndex} {genesisRoot : Root} {error : ErrorMessage}
    (fulu : .fusaka ≤ fork) (version : kind = .proposerV1 ∨ kind = .proposerV2)
    (slotsFit : (epoch.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat ≤ 2 ^ 64)
    (room : state.slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat ≤ 2 ^ 64)
    (known : ∀ proposer ∈ state.proposerLookahead fulu,
      proposer.toNat < state.validators.data.size)
    (failed : dutiesResponse config state kind epoch indices genesisRoot = .error error) :
    error.code = 400 := by
  rw [dutiesResponse_proposer_error fulu version slotsFit room known failed]
  rfl

end EthLib.Consensus.BeaconApi
