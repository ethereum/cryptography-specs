module

public import EthLib.Consensus.Proofs.Accessors
public import EthLib.Consensus.Proofs.Accessors.Draw
public import EthLib.Consensus.Proofs.Shuffle
public import EthLib.Consensus.Proofs.ShufflePermutation
public import EthLib.Consensus.Proofs.SyncCommittee
public import EthLib.Consensus.Transition.EpochParticipation

/-!
# Proofs: the sync committee update of an epoch succeeds under bounds

From Altair the epoch step draws a new sync committee at the start of each period.

The draw reads the candidates in a fixed order and accepts each with a chance set by its balance.

A candidate at the largest effective balance of the draw is always accepted.

The order visits every candidate once in each pass over them.

So each pass accepts at least one candidate, and the draw ends within as many passes as members.

With a candidate at the cap, the draw fails only when it runs out of 64-bit draw numbers first.

So a registry with a candidate at that balance, and a bound on the passes, makes the draw succeed.

The committee then aggregates the keys of its members, which must all be valid.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork}

/-- The largest effective balance that the draw of a fork compares against.

From Electra it is the cap of a compounding validator. -/
def drawCap (preset : Preset) (fork : Base.Fork) : Nat :=
  if .pectra ≤ fork then preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
  else preset.MAX_EFFECTIVE_BALANCE.toNat

/-- The products of the draw fit in 64 bits.

The draw compares the cap times a random value with a balance times the largest such value.

The value takes two bytes from Electra, and one before. -/
def DrawFits (preset : Preset) (fork : Base.Fork) : Prop :=
  if .pectra ≤ fork then preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat * (2 ^ 16 - 1) < 2 ^ 64
  else preset.MAX_EFFECTIVE_BALANCE.toNat * (2 ^ 8 - 1) < 2 ^ 64

/-- The products of the draw fit in 64 bits for the mainnet and minimal presets, at every fork. -/
theorem drawFits_presets (fork : Base.Fork) :
    DrawFits Preset.mainnet fork ∧ DrawFits Preset.minimal fork := by
  unfold DrawFits
  constructor <;> split <;> decide

/-- The seed lookahead is shorter than the history of mixes for the mainnet and minimal presets. -/
theorem seedLookahead_lt_presets :
    Preset.mainnet.MIN_SEED_LOOKAHEAD.toNat < Preset.mainnet.EPOCHS_PER_HISTORICAL_VECTOR.toNat ∧
      Preset.minimal.MIN_SEED_LOOKAHEAD.toNat <
        Preset.minimal.EPOCHS_PER_HISTORICAL_VECTOR.toNat := by
  decide

/-- The sync committee is not empty for the mainnet and minimal presets. -/
theorem syncCommitteeSize_ne_zero_presets :
    Preset.mainnet.SYNC_COMMITTEE_SIZE ≠ 0 ∧ Preset.minimal.SYNC_COMMITTEE_SIZE ≠ 0 := by
  decide

/-- A draw of a balance at most the cap succeeds, and accepts a balance at the cap. -/
theorem drawAccepts_ok_of_le (fits : DrawFits preset fork) (random : Bytes32) (i : Nat)
    {e : Gwei} (capped : e.toNat ≤ drawCap preset fork) :
    ∃ accepted, drawAccepts preset fork random i e = .ok accepted ∧
      (e.toNat = drawCap preset fork → accepted = true) := by
  unfold DrawFits at fits
  unfold drawCap at capped
  by_cases electra : .pectra ≤ fork
  · rw [ite_eq_left electra] at fits capped
    refine ⟨_, drawAccepts_eq_of_pectra preset fork electra random i e fits capped, ?_⟩
    intro atCap
    rw [atCap, drawCap, ite_eq_left electra]
    have small : i % 16 * 2 + 1 < 32 := by have := Nat.mod_lt i (by decide : 0 < 16); omega
    have low := (random[i % 16 * 2]'(by omega)).toNat_lt
    have high := random[i % 16 * 2 + 1].toNat_lt
    exact decide_eq_true (Nat.mul_le_mul_left _ (by omega))
  · rw [ite_eq_right electra] at fits capped
    refine ⟨_, drawAccepts_eq_of_before_pectra preset fork electra random i e fits capped, ?_⟩
    intro atCap
    rw [atCap, drawCap, ite_eq_right electra]
    have byte := (random[i % 32]'(Nat.mod_lt i (by decide))).toNat_lt
    exact decide_eq_true (Nat.mul_le_mul_left _ (by omega))

/-- The search succeeds while this draw or a later one reads the capped position in time.

That draw must leave one pass of draw numbers for each member still to draw after it. -/
private theorem balanceWeightedSearch_ok_of_next {indices : Array ValidatorIndex}
    {balances : Array Gwei} {order : Nat → Nat} {seed : Bytes32} {size : Nat}
    (fits : DrawFits preset fork)
    (capped : ∀ j < indices.size, (balances.getD (order j) 0).toNat ≤ drawCap preset fork)
    {j : Nat} (jLt : j < indices.size)
    (atCap : (balances.getD (order j) 0).toNat = drawCap preset fork) :
    ∀ left, ∀ {selected : Array ValidatorIndex} {bound : selected.size ≤ size} {i : Nat}
      {random : { random // random = drawHash fork seed i }}, left = 2 ^ 64 - i →
      (selected.size = size ∨ ∃ m, (i + m) % indices.size = j ∧
        i + m + 1 + (size - selected.size - 1) * indices.size < 2 ^ 64) →
      ∃ out, balanceWeightedSearch preset fork indices balances order seed size selected bound i
        random = .ok out := by
  intro left
  induction left using Nat.strongRecOn with
  | _ left ih =>
  intro selected bound i random leftEq next
  rw [balanceWeightedSearch]
  by_cases full : selected.size = size
  · rw [dite_eq_left full]
    exact ⟨_, rfl⟩
  rw [dite_eq_right full]
  obtain ⟨m, reaches, room⟩ := next.resolve_left full
  have nonempty : 0 < indices.size := by omega
  obtain ⟨accepted, draw, top⟩ :=
    drawAccepts_ok_of_le fits random.1 i (capped _ (Nat.mod_lt i nonempty))
  have iLt : i + 1 < 2 ^ 64 := by omega
  simp only [bind, Except.bind, draw, iLt, ↓reduceIte]
  refine ih (2 ^ 64 - (i + 1)) (leftEq ▸ Nat.sub_lt_sub_left (by omega) (Nat.lt_succ_self i))
    rfl ?_
  rcases m with _ | m
  · -- This draw reads the capped position, so it accepts.
    rw [Nat.add_zero] at reaches
    rw [top (reaches ▸ atCap)]
    simp only [↓reduceIte, Array.size_push]
    by_cases last : selected.size + 1 = size
    · exact .inl last
    refine .inr ⟨indices.size - 1, ?_, ?_⟩
    · rw [show i + 1 + (indices.size - 1) = i + indices.size by omega, Nat.add_mod_right]
      exact reaches
    · have split : size - selected.size - 1 = (size - (selected.size + 1) - 1) + 1 := by omega
      rw [split, Nat.succ_mul] at room
      omega
  · -- A later draw reads the capped position.
    have mono : (size - (selected.size + 1) - 1) * indices.size ≤
        (size - selected.size - 1) * indices.size :=
      Nat.mul_le_mul_right _ (by omega)
    cases accepted
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact .inr ⟨m, by rw [← reaches]; congr 1; omega, by omega⟩
    · simp only [↓reduceIte, Array.size_push]
      by_cases last : selected.size + 1 = size
      · exact .inl last
      exact .inr ⟨m, by rw [← reaches]; congr 1; omega, by omega⟩

/-- The search succeeds when one position of the order holds a candidate at the cap.

Each read balance must be at most the cap, so that no draw fails.

Each pass over the candidates then accepts at least one.

The draw numbers left must cover one pass for each member still to draw. -/
theorem balanceWeightedSearch_ok {indices : Array ValidatorIndex} {balances : Array Gwei}
    {order : Nat → Nat} {seed : Bytes32} {size : Nat} {selected : Array ValidatorIndex}
    {bound : selected.size ≤ size} {i : Nat} {random : { random // random = drawHash fork seed i }}
    (fits : DrawFits preset fork)
    (capped : ∀ j < indices.size, (balances.getD (order j) 0).toNat ≤ drawCap preset fork)
    {j : Nat} (jLt : j < indices.size)
    (atCap : (balances.getD (order j) 0).toNat = drawCap preset fork)
    (room : i + (size - selected.size) * indices.size < 2 ^ 64) :
    ∃ out, balanceWeightedSearch preset fork indices balances order seed size selected bound i
      random = .ok out := by
  refine balanceWeightedSearch_ok_of_next fits capped jLt atCap _ rfl ?_
  by_cases full : selected.size = size
  · exact .inl full
  -- The capped position comes back within one pass, before the last pass ends.
  refine .inr ⟨(j + indices.size - i % indices.size) % indices.size, ?_, ?_⟩
  · have whole := Nat.mod_add_div i indices.size
    have below := Nat.mod_lt i (show 0 < indices.size by omega)
    rw [Nat.add_mod_mod, show i + (j + indices.size - i % indices.size) =
        j + indices.size + indices.size * (i / indices.size) by omega,
      Nat.add_mul_mod_self_left, Nat.add_mod_right, Nat.mod_eq_of_lt jLt]
  · have within := Nat.mod_lt (j + indices.size - i % indices.size) (show 0 < indices.size by omega)
    have split : size - selected.size = (size - selected.size - 1) + 1 := by omega
    rw [split, Nat.succ_mul] at room
    omega

/-- A weighted selection succeeds when a candidate is at the cap and the draws suffice.

Each candidate must name a validator whose effective balance is at most the cap.

At most `2^40` candidates keep the shuffle in range; the bound is asked without a shuffle too.

The members times the candidates must stay below `2^64`, one pass for each member. -/
theorem computeBalanceWeightedSelection_ok {state : BeaconState preset fork}
    {indices : Array ValidatorIndex} {seed : Bytes32} {size : UInt64} {shuffleIndices : Bool}
    (fits : DrawFits preset fork)
    (known : ∀ index ∈ indices, ∃ validator, getValidator state index = .ok validator ∧
      validator.effectiveBalance.toNat ≤ drawCap preset fork)
    (full : ∃ index ∈ indices, ∃ validator, getValidator state index = .ok validator ∧
      validator.effectiveBalance.toNat = drawCap preset fork)
    (few : indices.size ≤ 2 ^ 40)
    (room : size.toNat * indices.size < 2 ^ 64) :
    ∃ out, computeBalanceWeightedSelection state indices seed size shuffleIndices = .ok out := by
  obtain ⟨index, member, validator, found, atCap⟩ := full
  have nonempty : indices.size ≠ 0 := by
    have := Array.size_pos_of_mem member
    omega
  have small : indices.size < 2 ^ 64 := by omega
  unfold computeBalanceWeightedSelection
  simp only [nonempty, small, ↓reduceIte, bind, Except.bind]
  split
  · next err mapped =>
    refine absurd mapped (array_mapM_ne_error fun x mem => ?_)
    obtain ⟨v, read, _⟩ := known x mem
    exact ⟨_, by rw [read]; rfl⟩
  rename_i balances mapped
  obtain ⟨sizeEq, each⟩ := array_mapM_ok mapped
  -- The balance at each position is the effective balance of the validator there.
  have balanceAt : ∀ k (lt : k < indices.size) v, getValidator state indices[k] = .ok v →
      balances.getD k 0 = v.effectiveBalance := by
    intro k lt v read
    have step := each k lt (sizeEq ▸ lt)
    rw [read] at step
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (sizeEq ▸ lt), Option.getD_some]
    exact (Except.ok.inj step).symm
  have notLarge : ¬(shuffleIndices = true ∧ size ≠ 0 ∧ 2 ^ 40 < indices.size) := by omega
  simp only [notLarge, ↓reduceIte]
  obtain ⟨p, pLt, pEq⟩ := Array.getElem_of_mem member
  -- Any order that permutes the positions reaches the validator at the cap.
  have search : ∀ order : Nat → Nat, (∀ k < indices.size, order k < indices.size) →
      (∃ j < indices.size, order j = p) →
      ∃ out, balanceWeightedSearch preset fork indices balances order seed size.toNat #[]
        (Nat.zero_le _) 0 ⟨drawHash fork seed 0, rfl⟩ = .ok out := by
    intro order inside ⟨j, jLt, reachesP⟩
    refine balanceWeightedSearch_ok fits (fun k kLt => ?_) jLt ?_ (by simpa using room)
    · obtain ⟨v, read, le⟩ := known _ (Array.getElem_mem (inside k kLt))
      rw [balanceAt _ (inside k kLt) v read]
      exact le
    · rw [reachesP, balanceAt p pLt validator (pEq ▸ found)]
      exact atCap
  cases shuffleIndices
  · exact search id (fun _ lt => lt) ⟨p, pLt, rfl⟩
  · exact search _ (fun _ lt => Shuffle.shuffledIndex_lt lt)
      ⟨_, Shuffle.unshuffledIndex_lt pLt, Shuffle.shuffledIndex_unshuffledIndex pLt⟩

/-- The seed of an epoch exists when the epoch plus the length of the history of mixes fits.

The seed lookahead must also be shorter than that history. -/
theorem getSeed_ok {state : BeaconState preset fork} {epoch : Epoch}
    (domain : DomainType)
    (epochRoom : epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat < 2 ^ 64)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat) :
    ∃ seed, getSeed state epoch domain = .ok seed := by
  have subOk : ∀ a b : UInt64, b.toNat ≤ a.toNat → Uint64.subChecked a b = .ok (a - b) :=
    fun a b le => by simp [Uint64.subChecked, UInt64.le_iff_toNat_le, le]
  have sum := Uint64.toNat_add_of_lt epochRoom
  have first := subOk (epoch + preset.EPOCHS_PER_HISTORICAL_VECTOR) preset.MIN_SEED_LOOKAHEAD
    (by omega)
  have second := subOk (epoch + preset.EPOCHS_PER_HISTORICAL_VECTOR - preset.MIN_SEED_LOOKAHEAD) 1
    (by rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))]; simp; omega)
  have nonzero : preset.EPOCHS_PER_HISTORICAL_VECTOR ≠ 0 := by
    intro zero
    rw [zero] at lookahead
    simp at lookahead
  simp only [getSeed, getRandaoMix, readCircular, liftArith, Uint64.addChecked_of_lt epochRoom,
    first, second, nonzero, bind, Except.bind, Except.mapError, pure, Except.pure, dite_false]
  exact ⟨_, rfl⟩

/-- No more validators are active in an epoch than the registry holds. -/
theorem length_getActiveValidatorIndices_le (state : BeaconState preset fork)
    (epoch : Epoch) :
    (getActiveValidatorIndices state epoch).length ≤ state.validators.data.size := by
  unfold getActiveValidatorIndices
  refine Nat.le_trans (List.length_filterMap_le _ _) ?_
  simp only [List.length_zipIdx, Array.length_toList, Nat.le_refl]

/-- The indices of the next sync committee are drawn under the bounds of the update. -/
private theorem getNextSyncCommitteeIndices_ok {state : BeaconState preset fork}
    (fits : DrawFits preset fork)
    (epochRoom : (getCurrentEpoch state).toNat + 1 + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat <
      2 ^ 64)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (capped : ∀ validator ∈ state.validators.data,
      validator.effectiveBalance.toNat ≤ drawCap preset fork)
    (full : ∃ validator ∈ state.validators.data,
      isActiveValidator validator (getCurrentEpoch state + 1) ∧
        validator.effectiveBalance.toNat = drawCap preset fork)
    (few : state.validators.data.size ≤ 2 ^ 40)
    (room : preset.SYNC_COMMITTEE_SIZE.toNat * state.validators.data.size < 2 ^ 64) :
    ∃ indices, getNextSyncCommitteeIndices state = .ok indices := by
  have oneNat : (1 : UInt64).toNat = 1 := rfl
  have sumFits : (getCurrentEpoch state).toNat + (1 : UInt64).toNat < 2 ^ 64 := by
    rw [oneNat]; omega
  have epochNat := Uint64.toNat_add_of_lt sumFits
  rw [oneNat] at epochNat
  obtain ⟨seed, seedOk⟩ := getSeed_ok (state := state) (epoch := getCurrentEpoch state + 1)
    DOMAIN_SYNC_COMMITTEE (by rw [epochNat]; omega) lookahead
  have checked := getActiveValidatorIndicesChecked_of_size_le (state := state) (by omega)
    (getCurrentEpoch state + 1)
  have lengthLe := length_getActiveValidatorIndices_le state (getCurrentEpoch state + 1)
  obtain ⟨out, selected⟩ := computeBalanceWeightedSelection_ok (state := state)
    (indices := (getActiveValidatorIndices state (getCurrentEpoch state + 1)).toArray)
    (seed := seed) (size := preset.SYNC_COMMITTEE_SIZE) (shuffleIndices := true) fits
    (fun index member => by
      obtain ⟨validator, read, _⟩ :=
        (mem_iff_of_getActiveValidatorIndicesChecked_ok checked).mp (List.mem_toArray.mp member)
      exact ⟨validator, by unfold getValidator; rw [read],
        capped validator (Array.mem_of_getElem? read)⟩)
    (by
      obtain ⟨validator, member, active, atCap⟩ := full
      obtain ⟨position, inside, rfl⟩ := Array.getElem_of_mem member
      have positionNat : (UInt64.ofNat position).toNat = position :=
        UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
      have read : state.validators.data[(UInt64.ofNat position).toNat]? =
          some state.validators.data[position] := by
        rw [positionNat, Array.getElem?_eq_getElem inside]
      exact ⟨UInt64.ofNat position, List.mem_toArray.mpr
        ((mem_iff_of_getActiveValidatorIndicesChecked_ok checked).mpr ⟨_, read, active⟩),
        _, by unfold getValidator; rw [read], atCap⟩)
    (by simp only [List.size_toArray]; omega)
    (by
      simp only [List.size_toArray]
      exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ lengthLe) room)
  refine ⟨out, ?_⟩
  simp only [getNextSyncCommitteeIndices, liftArith, Uint64.addChecked_of_lt sumFits, seedOk,
    checked, selected, bind, Except.bind, Except.mapError]

/-- The aggregate of a nonempty list of valid keys exists. -/
private theorem aggregatePubkeys_ok {pubkeys : Array Cryptography.Bls.BLSPubkey}
    (nonempty : pubkeys.size ≠ 0)
    (valid : ∀ pubkey ∈ pubkeys,
      ∃ point, Cryptography.Bls.G1.keyValidatePoint (packBytes pubkey) = .ok point) :
    ∃ aggregate, aggregatePubkeys pubkeys = .ok aggregate := by
  obtain ⟨sum, folded⟩ : ∃ sum, pubkeys.zipIdx.foldlM Cryptography.Bls.Signatures.addPubkeyPoint
      Cryptography.Bls.G1.zero = .ok sum := by
    rw [← Array.foldlM_toList]
    refine foldlM_exists_ok_of_invariant (fun _ => True) (fun acc entry member _ => ?_) _ trivial
    have read := Array.mem_zipIdx_iff_getElem?.mp (Array.mem_toList_iff.mp member)
    obtain ⟨point, checked⟩ := valid entry.1 (Array.mem_of_getElem? read)
    exact ⟨acc.add point, by
      simp [Cryptography.Bls.Signatures.addPubkeyPoint, checked, pure, Except.pure], trivial⟩
  have notEmpty : pubkeys.isEmpty = false := by simpa using nonempty
  refine ⟨Cryptography.Bls.Signatures.pointToPubkey sum, ?_⟩
  simp only [aggregatePubkeys, Cryptography.Bls.Signatures.ethAggregatePubkeys,
    Cryptography.Bls.Signatures.aggregatePubkeyPoint, notEmpty, folded, Bool.false_eq_true,
    ↓reduceIte, bind, Except.bind, pure, Except.pure, Except.mapError]

/-- The next sync committee is drawn and aggregated under the bounds of the draw.

It also needs valid keys, no balance above the cap and an active validator at it.

Those are assumptions on the registry, not bounds. -/
theorem getNextSyncCommittee_ok {state : BeaconState preset fork}
    (fits : DrawFits preset fork)
    (epochRoom : (getCurrentEpoch state).toNat + 1 + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat <
      2 ^ 64)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (keys : ∀ validator ∈ state.validators.data,
      ∃ point, Cryptography.Bls.G1.keyValidatePoint (packBytes validator.pubkey) = .ok point)
    (capped : ∀ validator ∈ state.validators.data,
      validator.effectiveBalance.toNat ≤ drawCap preset fork)
    (full : ∃ validator ∈ state.validators.data,
      isActiveValidator validator (getCurrentEpoch state + 1) ∧
        validator.effectiveBalance.toNat = drawCap preset fork)
    (few : state.validators.data.size ≤ 2 ^ 40)
    (room : preset.SYNC_COMMITTEE_SIZE.toNat * state.validators.data.size < 2 ^ 64)
    (members : preset.SYNC_COMMITTEE_SIZE ≠ 0) :
    ∃ committee, getNextSyncCommittee state = .ok committee := by
  obtain ⟨indices, drawn⟩ :=
    getNextSyncCommitteeIndices_ok fits epochRoom lookahead capped full few room
  have checked := getActiveValidatorIndicesChecked_of_size_le (state := state) (by omega)
    (getCurrentEpoch state + 1)
  -- Each drawn member is active next epoch, so it names a validator of the registry.
  have each : ∀ i : Fin preset.SYNC_COMMITTEE_SIZE.toNat, ∃ validator,
      state.validators.data[indices[i].toNat]? = some validator := by
    intro i
    have active := mem_getNextSyncCommitteeIndices drawn indices[i]
      (Vector.mem_toList_iff.mpr (Vector.getElem_mem i.isLt))
    obtain ⟨validator, read, _⟩ :=
      (mem_iff_of_getActiveValidatorIndicesChecked_ok checked).mp active
    exact ⟨validator, read⟩
  let chosen := fun i => Classical.choose (each i)
  have chosenRead : ∀ i, state.validators.data[indices[i].toNat]? = some (chosen i) :=
    fun i => Classical.choose_spec (each i)
  let pubkeys : Vector Cryptography.Bls.BLSPubkey preset.SYNC_COMMITTEE_SIZE.toNat :=
    Vector.ofFn fun i => (chosen i).pubkey
  obtain ⟨aggregate, aggregated⟩ := aggregatePubkeys_ok (pubkeys := pubkeys.toArray)
    (by
      have nonzero : preset.SYNC_COMMITTEE_SIZE.toNat ≠ 0 := fun zero =>
        members (UInt64.toNat_inj.mp (by rw [zero]; rfl))
      simpa using nonzero)
    (by
      intro pubkey member
      obtain ⟨i, rfl⟩ := Array.mem_ofFn.mp (by simpa [pubkeys] using member)
      exact keys (chosen i) (Array.mem_of_getElem? (chosenRead i)))
  refine ⟨⟨pubkeys, aggregate⟩, getNextSyncCommittee_eq_ok_iff.mpr
    ⟨indices, drawn, fun i => ⟨chosen i, ?_, by simp [pubkeys]⟩, aggregated⟩⟩
  unfold getValidator
  rw [chosenRead i]

/-- The assumptions under which the sync committee of the next period can be drawn from a state.

Every key of the registry passes key validation, as each deposit checked.

No effective balance is above the cap of the draw.

One validator active in the next epoch is at that cap: an assumption on the registry, not a bound.

The registry holds at most `2^40` validators.

Their number times the committee size is below `2^64`. -/
structure SyncDrawable (state : BeaconState preset fork) : Prop where
  /-- Every key of the registry passes key validation. -/
  keys : ∀ validator ∈ state.validators.data,
    ∃ point, Cryptography.Bls.G1.keyValidatePoint (packBytes validator.pubkey) = .ok point
  /-- No effective balance is above the cap of the draw. -/
  capped : ∀ validator ∈ state.validators.data,
    validator.effectiveBalance.toNat ≤ drawCap preset fork
  /-- One validator active in the next epoch is at the cap of the draw. -/
  full : ∃ validator ∈ state.validators.data,
    isActiveValidator validator (getCurrentEpoch state + 1) ∧
      validator.effectiveBalance.toNat = drawCap preset fork
  /-- The registry holds at most `2^40` validators. -/
  few : state.validators.data.size ≤ 2 ^ 40
  /-- The committee size times the number of validators is below `2^64`. -/
  room : preset.SYNC_COMMITTEE_SIZE.toNat * state.validators.data.size < 2 ^ 64

/-- From Altair, the sync committee update succeeds under bounds on the state.

The epoch after the current one, plus the length of the history of mixes, stays below `2^64`.

That room is asked at every epoch, though only a draw reads the history.

The seed lookahead is shorter than that history.

The products of the draw fit in 64 bits.

The committee is not empty, since the keys of an empty one have no aggregate.

The state must allow the draw only when the next epoch starts a period, the only time it draws. -/
theorem processSyncCommitteeUpdates_ok (altair : .altair ≤ fork) {state : BeaconState preset fork}
    (fits : DrawFits preset fork)
    (epochRoom : (getCurrentEpoch state).toNat + 1 + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat <
      2 ^ 64)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (members : preset.SYNC_COMMITTEE_SIZE ≠ 0)
    (drawable : (getCurrentEpoch state + 1) % preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD = 0 →
      SyncDrawable state) :
    ∃ after, processSyncCommitteeUpdates state altair = .ok after := by
  have sumFits : (getCurrentEpoch state).toNat + (1 : UInt64).toNat < 2 ^ 64 := by
    change _ + 1 < _
    omega
  unfold processSyncCommitteeUpdates
  simp only [liftAccessor, liftArith, Uint64.addChecked_of_lt sumFits, bind, Except.bind,
    Except.mapError, pure, Except.pure]
  split
  · next boundary =>
    obtain ⟨keys, capped, full, few, room⟩ := drawable boundary
    -- The committee is drawn from a state that differs only in its current committee.
    obtain ⟨committee, drawn⟩ := getNextSyncCommittee_ok
      (state := { state with currentSyncCommittee := fun _ => state.nextSyncCommittee altair })
      fits epochRoom lookahead keys capped full few room members
    simp only [drawn]
    exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

end EthLib.Consensus
