module

public import EthLib.Base.Proofs.List
public import EthLib.Base.Proofs.Uint64
public import EthLib.Consensus.Accessors
public import EthLib.Consensus.Credentials
public import EthLib.Consensus.Proofs.ShufflePermutation
public import EthLib.Consensus.Proofs.Signing

/-!
# Proofs: state accessors

The active indices are exactly the indices of the active validators, in increasing order.

That needs the registry to stay within the limit of the preset, which its type says before Gloas.

From Gloas the registry is a progressive list, so these theorems take the bound as a hypothesis.

A position of the registry is active in an epoch when the validator there is.

The effective balances are aligned when each is a whole number of increments.

When the largest values of the preset are aligned, so is the largest of each validator.

A marked sum of effective balances is their sum over the marked positions.

A total balance reads its indices as a set: their order and their repeats do not matter.

A total balance is at least one effective balance increment.

The total active balance rejects an active position or a balance sum of `2^64` or more.

From Electra, the pending balance of a validator is the sum of its pending partial withdrawals.

A sum of `2^64` or more fails, and the balance is zero exactly when each of those amounts is.

The previous epoch is the current one minus one, or the genesis epoch at genesis.

On natural numbers, the current epoch is the slot over the epoch length, less one for the previous.

Each slot has from one committee up to the most committees of the preset.

Each member of a committee, and each validator that an attestation shows, is active in its epoch.

Every active validator is in a committee of its epoch, and no validator is in two of them.

A committee is cut from the shuffle of the epoch of its slot.

The members of the committees of a slot, cut from one shuffle, are those of each committee in turn.

A validator is among those members exactly when one of the committees holds it.

From Electra, the attesters of some committees, cut from one shuffle, are those of each in turn.

The signers of an attestation are those cut from the shuffle of the epoch of its slot.

This holds when that shuffle has a value.

The indices of an attestation increase strictly, as the check of an indexed attestation asks.

An attestation has at most as many signers as bits, so its indexed form never exceeds its limit.

A proposer draw that shuffles only the positions it reads returns what the full shuffle gives.

Before Fulu, the proposer is active in the epoch of the state.

A signature domain always has a value.

A write to a circular buffer is read back at its position, and leaves every other entry unchanged.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork}

/-- Whether the validator at a position of the registry is active in an epoch.

A position outside the registry is not active. -/
def isActiveAt (state : BeaconState preset fork) (epoch : Epoch) (position : Nat) : Bool :=
  (state.validators.data[position]?.map (isActiveValidator · epoch)).getD false

/-- A position is active in an epoch exactly when it holds a validator active in that epoch. -/
theorem isActiveAt_eq_true_iff {state : BeaconState preset fork} {epoch : Epoch}
    {position : Nat} :
    isActiveAt state epoch position = true ↔ ∃ validator,
      state.validators.data[position]? = some validator ∧
        isActiveValidator validator epoch = true := by
  cases found : state.validators.data[position]? <;> simp [isActiveAt, found]

/-- Every effective balance of the registry is a whole number of increments. -/
def EffectiveBalancesAligned (state : BeaconState preset fork) : Prop :=
  ∀ validator ∈ state.validators.data,
    validator.effectiveBalance % preset.EFFECTIVE_BALANCE_INCREMENT = 0

/-- Each largest effective balance of the preset is a whole number of increments.

These are the largest before Electra, the activation balance and the largest from Electra. -/
def MaxEffectiveBalancesAligned (preset : Preset) : Prop :=
  preset.MAX_EFFECTIVE_BALANCE % preset.EFFECTIVE_BALANCE_INCREMENT = 0 ∧
    preset.MIN_ACTIVATION_BALANCE % preset.EFFECTIVE_BALANCE_INCREMENT = 0 ∧
    preset.MAX_EFFECTIVE_BALANCE_ELECTRA % preset.EFFECTIVE_BALANCE_INCREMENT = 0

/-- The mainnet preset has aligned largest values. -/
theorem maxEffectiveBalancesAligned_mainnet : MaxEffectiveBalancesAligned Preset.mainnet := by
  unfold MaxEffectiveBalancesAligned
  decide

/-- The minimal preset has aligned largest values. -/
theorem maxEffectiveBalancesAligned_minimal : MaxEffectiveBalancesAligned Preset.minimal := by
  unfold MaxEffectiveBalancesAligned
  decide

/-- With aligned largest values in the preset, the largest of each validator is aligned. -/
theorem withdrawalMaxEffectiveBalance_aligned (maxAligned : MaxEffectiveBalancesAligned preset)
    (validator : Validator) :
    withdrawalMaxEffectiveBalance preset fork validator % preset.EFFECTIVE_BALANCE_INCREMENT =
      0 := by
  unfold withdrawalMaxEffectiveBalance getMaxEffectiveBalance
  split
  · split
    · exact maxAligned.2.2
    · exact maxAligned.2.1
  · exact maxAligned.1

/-- A position of the validator registry, as a validator index, keeps its value.

The registry must stay within the limit of the preset, which its type says before Gloas. -/
theorem toNat_toUInt64_of_lt {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit) {i : Nat} (lt : i < state.validators.data.size) :
    i.toUInt64.toNat = i := by
  have bound : state.validators.data.size ≤ _ := within
  have limit := preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

/-- An index whose position holds a validator active in an epoch is active in that epoch. -/
theorem mem_getActiveValidatorIndices_of_isActiveAt {state : BeaconState preset fork}
    {epoch : Epoch} {index : ValidatorIndex} (active : isActiveAt state epoch index.toNat = true) :
    index ∈ getActiveValidatorIndices state epoch := by
  obtain ⟨validator, found, isActive⟩ := isActiveAt_eq_true_iff.mp active
  simp only [getActiveValidatorIndices, List.mem_filterMap, Option.ite_none_right_eq_some,
    Option.some.injEq, List.mem_zipIdx_iff_getElem?, Prod.exists]
  exact ⟨validator, index.toNat, by simpa using found, isActive, by simp⟩

/-- The active positions of a registry, converted without a check, are the active indices. -/
private theorem map_activePositions (state : BeaconState preset fork) (epoch : Epoch) :
    (state.validators.data.toList.zipIdx.filterMap fun (validator, position) =>
        if isActiveValidator validator epoch then some position else none).map Nat.toUInt64 =
      getActiveValidatorIndices state epoch := by
  rw [getActiveValidatorIndices, List.map_filterMap]
  congr
  funext ⟨validator, position⟩
  dsimp only
  split <;> rfl

/-- A position is an active position exactly when the validator there is active. -/
private theorem mem_activePositions {state : BeaconState preset fork} {epoch : Epoch}
    {position : Nat} :
    position ∈ (state.validators.data.toList.zipIdx.filterMap fun (validator, position) =>
        if isActiveValidator validator epoch then some position else none) ↔
      ∃ inside : position < state.validators.data.size,
        isActiveValidator state.validators.data[position] epoch = true := by
  simp only [List.mem_filterMap, Option.ite_none_right_eq_some, Option.some.injEq,
    List.mem_zipIdx_iff_getElem?, Prod.exists]
  constructor
  · rintro ⟨validator, _, found, active, rfl⟩
    obtain ⟨inside, read⟩ := Array.getElem?_eq_some_iff.mp (by simpa using found)
    exact ⟨inside, read ▸ active⟩
  · rintro ⟨inside, active⟩
    exact ⟨_, position, by simp [inside], active, rfl⟩

/-- The checked read gives the active indices exactly when each active position is below `2^64`.

The specification builds each active index with that check, so it fails otherwise.

Otherwise the pure list wraps some active position modulo `2^64`. -/
theorem getActiveValidatorIndicesChecked_eq_ok_iff {state : BeaconState preset fork}
    {epoch : Epoch} :
    getActiveValidatorIndicesChecked state epoch = .ok (getActiveValidatorIndices state epoch) ↔
    ∀ position (inside : position < state.validators.data.size),
      isActiveValidator state.validators.data[position] epoch = true → position < 2 ^ 64 := by
  rw [getActiveValidatorIndicesChecked, liftArith, mapError_ok_iff, mapM_ofNatChecked_eq_ok_iff,
    map_activePositions]
  simp only [and_true]
  constructor
  · intro below position inside active
    exact below position (mem_activePositions.mpr ⟨inside, active⟩)
  · intro below position member
    obtain ⟨inside, active⟩ := mem_activePositions.mp member
    exact below position inside active

/-- A successful checked read agrees with the pure list of active indices. -/
theorem getActiveValidatorIndicesChecked_ok {state : BeaconState preset fork} {epoch : Epoch}
    {indices : List ValidatorIndex}
    (computed : getActiveValidatorIndicesChecked state epoch = .ok indices) :
    indices = getActiveValidatorIndices state epoch := by
  rw [getActiveValidatorIndicesChecked, liftArith, mapError_ok_iff,
    mapM_ofNatChecked_eq_ok_iff, map_activePositions] at computed
  exact computed.2

/-- The checked read fails only by an overflow. -/
theorem getActiveValidatorIndicesChecked_error {state : BeaconState preset fork} {epoch : Epoch}
    {error : AccessorError}
    (computed : getActiveValidatorIndicesChecked state epoch = .error error) :
    error = .arith .overflow := by
  rw [getActiveValidatorIndicesChecked, liftArith] at computed
  cases converted : (state.validators.data.toList.zipIdx.filterMap fun (validator, position) =>
      if isActiveValidator validator epoch then some position else none).mapM ofNatChecked with
  | ok => simp [converted, Except.mapError] at computed
  | error arith =>
    simp only [converted, Except.mapError, Except.error.injEq] at computed
    rw [← computed, mapM_ofNatChecked_error converted]

/-- An active position of `2^64` or more makes the checked read fail by an overflow. -/
theorem getActiveValidatorIndicesChecked_eq_error {state : BeaconState preset fork}
    {epoch : Epoch}
    (large : ¬ ∀ position (inside : position < state.validators.data.size),
      isActiveValidator state.validators.data[position] epoch = true → position < 2 ^ 64) :
    getActiveValidatorIndicesChecked state epoch = .error (.arith .overflow) := by
  cases computed : getActiveValidatorIndicesChecked state epoch with
  | ok indices =>
    rw [getActiveValidatorIndicesChecked_ok computed] at computed
    exact absurd (getActiveValidatorIndicesChecked_eq_ok_iff.mp computed) large
  | error error => rw [getActiveValidatorIndicesChecked_error computed]

/-- A successful checked read leaves every active position below `2^64`. -/
theorem lt_of_getActiveValidatorIndicesChecked_ok {state : BeaconState preset fork}
    {epoch : Epoch} {indices : List ValidatorIndex} {position : Nat} {validator : Validator}
    (computed : getActiveValidatorIndicesChecked state epoch = .ok indices)
    (found : state.validators.data[position]? = some validator)
    (active : isActiveValidator validator epoch = true) : position < 2 ^ 64 := by
  obtain ⟨inside, rfl⟩ := Array.getElem?_eq_some_iff.mp found
  rw [getActiveValidatorIndicesChecked_ok computed] at computed
  exact getActiveValidatorIndicesChecked_eq_ok_iff.mp computed position inside active

/-- The checked read succeeds when every position of the registry fits in 64 bits. -/
theorem getActiveValidatorIndicesChecked_of_size_le {state : BeaconState preset fork}
    (small : state.validators.data.size ≤ 2 ^ 64) (epoch : Epoch) :
    getActiveValidatorIndicesChecked state epoch = .ok (getActiveValidatorIndices state epoch) :=
  getActiveValidatorIndicesChecked_eq_ok_iff.mpr fun _ inside _ => Nat.lt_of_lt_of_le inside small

/-- A registry within its preset limit has the same checked and pure active indices. -/
theorem getActiveValidatorIndicesChecked_of_within {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit) (epoch : Epoch) :
    getActiveValidatorIndicesChecked state epoch = .ok (getActiveValidatorIndices state epoch) :=
  getActiveValidatorIndicesChecked_of_size_le
    (Nat.le_trans within (Nat.le_of_lt preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt)) epoch

/-- A successful checked read lists exactly the indices that name an active validator. -/
theorem mem_iff_of_getActiveValidatorIndicesChecked_ok {state : BeaconState preset fork}
    {epoch : Epoch} {indices : List ValidatorIndex}
    (computed : getActiveValidatorIndicesChecked state epoch = .ok indices)
    {index : ValidatorIndex} :
    index ∈ indices ↔
      ∃ validator, state.validators.data[index.toNat]? = some validator ∧
        isActiveValidator validator epoch = true := by
  rw [getActiveValidatorIndicesChecked_ok computed]
  refine ⟨fun member => ?_, fun found =>
    mem_getActiveValidatorIndices_of_isActiveAt (isActiveAt_eq_true_iff.mpr found)⟩
  rw [getActiveValidatorIndicesChecked, liftArith, mapError_ok_iff,
    mapM_ofNatChecked_eq_ok_iff] at computed
  obtain ⟨small, same⟩ := computed
  rw [← map_activePositions, List.mem_map] at member
  obtain ⟨position, listed, rfl⟩ := member
  obtain ⟨inside, active⟩ := mem_activePositions.mp listed
  have fits : position.toUInt64.toNat = position := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (small position listed)]
  rw [fits]
  exact ⟨_, by simp [inside], active⟩

/-- An index is active exactly when it names a validator that is active in the epoch. -/
theorem mem_getActiveValidatorIndices {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit) {epoch : Epoch} {index : ValidatorIndex} :
    index ∈ getActiveValidatorIndices state epoch ↔
      ∃ validator, state.validators.data[index.toNat]? = some validator ∧
        isActiveValidator validator epoch = true :=
  mem_iff_of_getActiveValidatorIndicesChecked_ok
    (getActiveValidatorIndicesChecked_of_within within epoch)

/-- The positions of the validators that pass a test increase strictly, as 64-bit indices.

That needs each position that passes to be below `2^64`. -/
theorem validatorPositions_sorted_of_fits {state : BeaconState preset fork}
    (test : Validator → Bool)
    (fits : ∀ entry ∈ state.validators.data.toList.zipIdx, test entry.1 = true →
      entry.2 < 2 ^ 64) :
    (state.validators.data.toList.zipIdx.filterMap fun (validator, index) =>
      if test validator then some index.toUInt64 else none).Pairwise (· < ·) := by
  have base : state.validators.data.toList.zipIdx.Pairwise (fun a b => a.2 < b.2) := by
    have := List.pairwise_lt_range' (s := 0) (n := state.validators.data.toList.length)
    rw [← List.zipIdx_map_snd 0] at this
    exact List.pairwise_map.mp this
  refine List.Pairwise.filterMap _ ?_ (List.Pairwise.and_mem.mp base)
  rintro ⟨v, i⟩ ⟨w, j⟩ ⟨mi, mj, lt⟩ a ha b hb
  simp only [Option.ite_none_right_eq_some, Option.some.injEq] at ha hb
  obtain ⟨vi, rfl⟩ := ha
  obtain ⟨wj, rfl⟩ := hb
  rw [UInt64.lt_iff_toNat_lt, Nat.toUInt64_eq, Nat.toUInt64_eq,
    UInt64.toNat_ofNat_of_lt' (fits _ mi vi), UInt64.toNat_ofNat_of_lt' (fits _ mj wj)]
  exact lt

/-- The positions of the validators that pass a test increase strictly, as 64-bit indices.

That needs a registry within its limit. -/
theorem validatorPositions_sorted {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit) (test : Validator → Bool) :
    (state.validators.data.toList.zipIdx.filterMap fun (validator, index) =>
      if test validator then some index.toUInt64 else none).Pairwise (· < ·) :=
  validatorPositions_sorted_of_fits test fun entry member _ => by
    have inside : entry.2 < state.validators.data.size := by
      simpa using (List.mem_zipIdx' member).1
    have limit := preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt
    have bound : state.validators.data.size ≤ _ := within
    omega

/-- After a successful checked read, the active indices increase strictly. -/
theorem sorted_of_getActiveValidatorIndicesChecked_ok {state : BeaconState preset fork}
    {epoch : Epoch} {indices : List ValidatorIndex}
    (computed : getActiveValidatorIndicesChecked state epoch = .ok indices) :
    indices.Pairwise (· < ·) := by
  obtain rfl := getActiveValidatorIndicesChecked_ok computed
  refine validatorPositions_sorted_of_fits (isActiveValidator · epoch) fun entry member active => ?_
  obtain ⟨inside, read⟩ := Array.getElem?_eq_some_iff.mp
    (by simpa using List.mem_zipIdx_iff_getElem?.mp member)
  exact getActiveValidatorIndicesChecked_eq_ok_iff.mp computed entry.2 inside (read ▸ active)

/-- The active indices increase strictly. -/
theorem getActiveValidatorIndices_sorted {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit) (epoch : Epoch) :
    (getActiveValidatorIndices state epoch).Pairwise (· < ·) :=
  sorted_of_getActiveValidatorIndicesChecked_ok
    (getActiveValidatorIndicesChecked_of_within within epoch)

/-- Marking indices one after the other sets exactly the entries that some index names. -/
theorem getElem?_foldl_mark (indices : List ValidatorIndex) (init : Array Bool) (j : Nat) :
    (indices.foldl (fun marked index => marked.setIfInBounds index.toNat true) init)[j]? =
      init[j]?.map (· || indices.any (·.toNat == j)) := by
  induction indices generalizing init with
  | nil =>
    simp only [List.foldl_nil, List.any_nil, Bool.or_false]
    cases init[j]? <;> rfl
  | cons index rest ih =>
    rw [List.foldl_cons, ih, Array.getElem?_setIfInBounds]
    by_cases same : index.toNat = j
    · subst same
      by_cases inside : index.toNat < init.size
      · simp [inside]
      · simp [inside]
    · have differ : (index.toNat == j) = false := by simpa using same
      cases init[j]? <;> simp [same, differ]

/-- The mark of a validator is set exactly when some index names it. -/
theorem getElem?_markIndices (size : Nat) (indices : List ValidatorIndex) (j : Nat) :
    (markIndices size indices)[j]? =
      if j < size then some (indices.any (·.toNat == j)) else none := by
  rw [markIndices, getElem?_foldl_mark]
  by_cases lt : j < size <;> simp [lt]

/-- Two lists with the same members mark the same validators. -/
theorem markIndices_congr {size : Nat} {first second : List ValidatorIndex}
    (same : ∀ index, index ∈ first ↔ index ∈ second) :
    markIndices size first = markIndices size second := by
  refine Array.ext_getElem? fun j => ?_
  rw [getElem?_markIndices, getElem?_markIndices]
  have : first.any (·.toNat == j) = second.any (·.toNat == j) := by
    rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
    exact ⟨fun ⟨x, m, e⟩ => ⟨x, (same x).mp m, e⟩, fun ⟨x, m, e⟩ => ⟨x, (same x).mpr m, e⟩⟩
  rw [this]

/-- A fold that adds the effective balance of each marked validator sums them by position. -/
private theorem foldl_zip_marks :
    ∀ (validators : List Validator) (marks : List Bool) (sum : Nat),
      (validators.zip marks).foldl (fun sum pair =>
          if pair.2 then sum + pair.1.effectiveBalance.toNat else sum) sum =
        sum + ((List.range validators.length).map fun j =>
          if marks.getD j false then
            ((validators[j]?).map (·.effectiveBalance.toNat)).getD 0
          else 0).sum
  | [], _, sum => by simp
  | _ :: _, [], sum => by
    simp only [List.zip_nil_right, List.foldl_nil, List.getD_nil, Bool.false_eq_true,
      ↓reduceIte, List.map_const', List.sum_replicate_nat, Nat.mul_zero, Nat.add_zero]
  | validator :: validators, mark :: marks, sum => by
    rw [List.zip_cons_cons, List.foldl_cons, foldl_zip_marks validators marks,
      List.length_cons, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.sum_cons, Function.comp_def,
      List.getD_cons_zero, List.getD_cons_succ, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.map_some, Option.getD_some]
    cases mark <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- The marked sum of the effective balances is their sum over the marked positions. -/
theorem sumMarked_eq_sum (validators : Array Validator) (marks : Array Bool) :
    sumMarked validators marks = ((List.range validators.size).map fun j =>
      if (marks[j]?).getD false then ((validators[j]?).map (·.effectiveBalance.toNat)).getD 0
      else 0).sum := by
  unfold sumMarked
  rw [← Array.foldl_toList, Array.toList_zip]
  change List.foldl (fun (sum : Nat) (pair : Validator × Bool) =>
      if pair.2 then sum + pair.1.effectiveBalance.toNat else sum) 0 _ = _
  rw [foldl_zip_marks, Nat.zero_add, Array.length_toList]
  simp only [List.getD_eq_getElem?_getD, Array.getElem?_toList]

/-- A total balance exists exactly when two conditions hold.

Every index names a validator, and the sum of the marked effective balances is below 2^64.

It is then that sum, or one increment if the sum is smaller. -/
theorem getTotalBalance_ok_iff {state : BeaconState preset fork}
    {indices : List ValidatorIndex} {total : Gwei} :
    getTotalBalance state indices = .ok total ↔
      (∀ index ∈ indices, index.toNat < state.validators.data.size) ∧
        sumMarked state.validators.data
          (markIndices state.validators.data.size indices) < 2 ^ 64 ∧
        total = max preset.EFFECTIVE_BALANCE_INCREMENT
          (sumMarked state.validators.data
            (markIndices state.validators.data.size indices)).toUInt64 := by
  unfold getTotalBalance
  cases found : indices.find? (state.validators.data.size ≤ ·.toNat) with
  | some index =>
    obtain ⟨outside, member⟩ := List.find?_eq_some_iff_append.mp found |>.imp_right
      fun ⟨as, bs, eq, _⟩ => eq ▸ List.mem_append_right as (List.mem_cons_self ..)
    have notAll : ¬ ∀ i ∈ indices, i.toNat < state.validators.data.size := fun inside => by
      have := inside index member
      simp at outside
      omega
    simp only [found]
    constructor
    · intro h
      simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    · intro h
      exact absurd h.1 notAll
  | none =>
    have inside : ∀ index ∈ indices, index.toNat < state.validators.data.size := by
      intro index member
      have := List.find?_eq_none.mp found index member
      simp at this
      exact this
    simp only [found]
    by_cases big : 2 ^ 64 ≤ sumMarked state.validators.data
        (markIndices state.validators.data.size indices)
    · constructor
      · intro h
        simp [big, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
      · rintro ⟨-, lt, -⟩
        omega
    · have lt : sumMarked state.validators.data
          (markIndices state.validators.data.size indices) < 2 ^ 64 := by omega
      simp only [big, ite_false, pure, Except.pure, Except.ok.injEq]
      constructor
      · rintro rfl
        exact ⟨inside, lt, rfl⟩
      · rintro ⟨-, -, rfl⟩
        rfl

/-- A total balance is at least one effective balance increment. -/
theorem le_getTotalBalance {state : BeaconState preset fork} {indices : List ValidatorIndex}
    {total : Gwei} (ok : getTotalBalance state indices = .ok total) :
    preset.EFFECTIVE_BALANCE_INCREMENT ≤ total := by
  obtain ⟨-, -, rfl⟩ := getTotalBalance_ok_iff.mp ok
  rw [UInt64.max_def]
  split
  · assumption
  · exact UInt64.le_refl _

/-- A total balance depends on its indices only as a set: their order and repeats do not matter. -/
theorem getTotalBalance_congr {state : BeaconState preset fork}
    {first second : List ValidatorIndex} (same : ∀ index, index ∈ first ↔ index ∈ second)
    {total : Gwei} :
    getTotalBalance state first = .ok total ↔ getTotalBalance state second = .ok total := by
  rw [getTotalBalance_ok_iff, getTotalBalance_ok_iff, markIndices_congr same]
  exact ⟨fun ⟨inside, rest⟩ => ⟨fun i m => inside i ((same i).mpr m), rest⟩,
    fun ⟨inside, rest⟩ => ⟨fun i m => inside i ((same i).mp m), rest⟩⟩

/-- A successful active-balance read is the total balance of the checked active indices. -/
theorem getTotalActiveBalance_ok {state : BeaconState preset fork} {total : Gwei}
    (computed : getTotalActiveBalance state = .ok total) :
    getTotalBalance state (getActiveValidatorIndices state (getCurrentEpoch state)) =
      .ok total := by
  obtain ⟨indices, checked, computed⟩ := bind_ok_iff.mp computed
  rw [getActiveValidatorIndicesChecked_ok checked] at computed
  exact computed

/-- The total active balance never fails on an index: every active index names a validator. -/
theorem getTotalActiveBalance_ne_indexOutOfRange {state : BeaconState preset fork}
    (index : ValidatorIndex) :
    getTotalActiveBalance state ≠ .error (.indexOutOfRange index) := by
  unfold getTotalActiveBalance
  cases checked : getActiveValidatorIndicesChecked state (getCurrentEpoch state) with
  | error error =>
    rw [getActiveValidatorIndicesChecked_error checked]
    simp [bind, Except.bind]
  | ok indices =>
    have none : indices.find? (state.validators.data.size ≤ ·.toNat) = none := by
      rw [List.find?_eq_none]
      intro i member
      obtain ⟨_, found, -⟩ := (mem_iff_of_getActiveValidatorIndicesChecked_ok checked).mp member
      have := (Array.getElem?_eq_some_iff.mp found).1
      simp
      omega
    simp only [bind, Except.bind]
    unfold getTotalBalance
    simp only [none]
    by_cases big : 2 ^ 64 ≤ sumMarked state.validators.data
        (markIndices state.validators.data.size indices)
    · simp [big, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
    · simp [big, pure, Except.pure]

/-- From Electra, the pending balance of a validator succeeds exactly when its sum is below `2^64`.

The sum runs over the amounts of the pending partial withdrawals of that validator alone.

The result is then that sum. -/
theorem getPendingBalanceToWithdraw_ok_iff {state : BeaconState preset fork}
    {electra : .pectra ≤ fork} {index : ValidatorIndex} {amount : Gwei} :
    getPendingBalanceToWithdraw state electra index = .ok amount ↔
      (((state.pendingPartialWithdrawals electra).data.toList.filter
          (·.validatorIndex = index)).map (·.amount.toNat)).sum < 2 ^ 64 ∧
        amount.toNat = (((state.pendingPartialWithdrawals electra).data.toList.filter
          (·.validatorIndex = index)).map (·.amount.toNat)).sum := by
  unfold getPendingBalanceToWithdraw
  simp only [EthLib.Base.sum_map_ite_eq_sum_filter
    fun withdrawal : PendingPartialWithdrawal => withdrawal.validatorIndex = index]
  split
  · rename_i small
    simp only [Except.ok.injEq, small, true_and]
    constructor
    · rintro rfl
      simp [Nat.mod_eq_of_lt small]
    · intro sum
      apply UInt64.toNat_inj.mp
      simp [sum, Nat.mod_eq_of_lt small]
  · simp only [reduceCtorEq, false_iff, not_and]
    omega

/-- From Electra, the pending balance of a validator fails exactly when its sum reaches `2^64`.

It then fails with a balance overflow. -/
theorem getPendingBalanceToWithdraw_eq_error_iff {state : BeaconState preset fork}
    {electra : .pectra ≤ fork} {index : ValidatorIndex} {error : AccessorError} :
    getPendingBalanceToWithdraw state electra index = .error error ↔
      2 ^ 64 ≤ (((state.pendingPartialWithdrawals electra).data.toList.filter
          (·.validatorIndex = index)).map (·.amount.toNat)).sum ∧
        error = .balanceOverflow := by
  unfold getPendingBalanceToWithdraw
  simp only [EthLib.Base.sum_map_ite_eq_sum_filter
    fun withdrawal : PendingPartialWithdrawal => withdrawal.validatorIndex = index]
  split
  · simp only [reduceCtorEq, false_iff, not_and]
    omega
  · simp only [Except.error.injEq]
    constructor
    · rintro rfl
      exact ⟨by omega, rfl⟩
    · rintro ⟨-, rfl⟩
      rfl

/-- From Electra, the pending balance of a validator is zero exactly when each of its amounts is.

The amounts are those of its pending partial withdrawals. -/
theorem getPendingBalanceToWithdraw_eq_ok_zero_iff {state : BeaconState preset fork}
    {electra : .pectra ≤ fork} {index : ValidatorIndex} :
    getPendingBalanceToWithdraw state electra index = .ok 0 ↔
      ∀ withdrawal ∈ (state.pendingPartialWithdrawals electra).data.toList,
        withdrawal.validatorIndex = index → withdrawal.amount = 0 := by
  rw [getPendingBalanceToWithdraw_ok_iff, UInt64.toNat_zero, eq_comm (a := 0),
    List.sum_eq_zero_iff_forall_eq_nat]
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨-, vanish⟩ withdrawal member owned
    exact UInt64.toNat_inj.mp (vanish _ ⟨withdrawal, ⟨member, owned⟩, rfl⟩)
  · intro vanish
    have each : ∀ amount, (∃ withdrawal, (withdrawal ∈ (state.pendingPartialWithdrawals
        electra).data.toList ∧ withdrawal.validatorIndex = index) ∧
          withdrawal.amount.toNat = amount) → amount = 0 := by
      rintro amount ⟨withdrawal, ⟨member, owned⟩, rfl⟩
      simp [vanish withdrawal member owned]
    refine ⟨?_, each⟩
    rw [List.sum_eq_zero_iff_forall_eq_nat.mpr (by simpa using each)]
    omega


/--
The previous epoch on natural numbers is the current epoch less one, and zero in the genesis epoch.
-/
theorem getPreviousEpoch_toNat (state : BeaconState preset fork) :
    (getPreviousEpoch state).toNat = (getCurrentEpoch state).toNat - 1 := by
  unfold getPreviousEpoch saturatingSub
  split
  · rename_i lt
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt lt)]
    rfl
  · rename_i notLt
    rw [UInt64.lt_iff_toNat_lt] at notLt
    simp only [UInt64.toNat_one] at notLt
    simp only [UInt64.toNat_zero]
    omega

/-- The current epoch on natural numbers is the slot divided by the length of an epoch. -/
theorem getCurrentEpoch_toNat (state : BeaconState preset fork) :
    (getCurrentEpoch state).toNat = state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
  simp [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div]

/-- With at least two slots in an epoch, the current epoch is never the far future one. -/
theorem getCurrentEpoch_ne_farFuture (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (state : BeaconState preset fork) : getCurrentEpoch state ≠ FAR_FUTURE_EPOCH := by
  intro far
  have epoch := congrArg UInt64.toNat far
  rw [getCurrentEpoch_toNat] at epoch
  have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  have half := Nat.div_le_div_left (a := state.slot.toNat) twoSlots (by decide)
  have := state.slot.toNat_lt_size
  simp only [UInt64.size] at this
  omega

/-- The current epoch is at most the slot, at every length of an epoch. -/
theorem getCurrentEpoch_toNat_le_slot (state : BeaconState preset fork) :
    (getCurrentEpoch state).toNat ≤ state.slot.toNat := by
  rw [getCurrentEpoch_toNat]
  exact Nat.div_le_self _ _

/-- The epoch after the current one exists when a next slot exists.

A next epoch alone would be enough for a caller that needs only that epoch. -/
theorem addChecked_getCurrentEpoch_one_total (state : BeaconState preset fork)
    (fits : state.slot.toNat + 1 < 2 ^ 64) :
    ∃ next, addChecked (getCurrentEpoch state) 1 = .ok next := by
  have le := getCurrentEpoch_toNat_le_slot state
  exact ⟨_, addChecked_of_lt (by simp; omega)⟩

/-- The previous epoch is at most the current epoch. -/
theorem getPreviousEpoch_le (state : BeaconState preset fork) :
    getPreviousEpoch state ≤ getCurrentEpoch state := by
  unfold getPreviousEpoch saturatingSub
  split
  · rename_i lt
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt lt)]
    omega
  · exact UInt64.zero_le

/-- After genesis, the previous epoch is the epoch just before the current one. -/
theorem getPreviousEpoch_add_one {state : BeaconState preset fork}
    (positive : getCurrentEpoch state ≠ 0) :
    getPreviousEpoch state + 1 = getCurrentEpoch state := by
  unfold getPreviousEpoch saturatingSub
  have nonzero : (getCurrentEpoch state).toNat ≠ 0 :=
    fun zero => positive (UInt64.toNat_inj.mp (by simpa using zero))
  split
  · rename_i lt
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt lt)]
    have := (getCurrentEpoch state).toNat_lt
    simp
    omega
  · rename_i notLt
    rw [UInt64.lt_iff_toNat_lt] at notLt
    have one : (getCurrentEpoch state).toNat = 1 := by simp at notLt; omega
    apply UInt64.toNat_inj.mp
    simp [one]

/-- The number of active validators fits in 64 bits, when the registry stays within its limit. -/
theorem length_getActiveValidatorIndices_lt {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit) (epoch : Epoch) :
    (getActiveValidatorIndices state epoch).length < 2 ^ 64 := by
  unfold getActiveValidatorIndices
  refine Nat.lt_of_le_of_lt (List.length_filterMap_le _ _) ?_
  have bound : state.validators.data.size ≤ _ := within
  have limit := preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt
  simp only [List.length_zipIdx, Array.length_toList]
  omega

/-- The number of active validators, as a 64-bit integer, keeps its value. -/
theorem toNat_length_getActiveValidatorIndices {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit) (epoch : Epoch) :
    (getActiveValidatorIndices state epoch).length.toUInt64.toNat =
      (getActiveValidatorIndices state epoch).length := by
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt (length_getActiveValidatorIndices_lt within epoch)]

/-- Each slot has at least one committee. -/
theorem one_le_getCommitteeCountPerSlot (state : BeaconState preset fork) (epoch : Epoch) :
    1 ≤ getCommitteeCountPerSlot state epoch := by
  simp only [getCommitteeCountPerSlot, committeeCountOf, max, min]
  repeat' split
  all_goals simp_all [UInt64.le_iff_toNat_le]
  all_goals omega

/-- A slot has at most the most committees of the preset, or one if that is zero. -/
theorem getCommitteeCountPerSlot_le (state : BeaconState preset fork) (epoch : Epoch) :
    getCommitteeCountPerSlot state epoch ≤ max 1 preset.MAX_COMMITTEES_PER_SLOT := by
  simp only [getCommitteeCountPerSlot, committeeCountOf, max, min]
  repeat' split
  all_goals simp_all [UInt64.le_iff_toNat_le]
  all_goals omega

/-- A committee that has a value comes from a positive count. -/
theorem count_ne_zero_of_computeCommittee {indices : Array ValidatorIndex} {seed : Bytes32}
    {index count : UInt64} {committee : Array ValidatorIndex}
    (computed : computeCommittee preset indices seed index count = .ok committee) : count ≠ 0 := by
  intro zero
  cases shuffle : computeShuffledPermutation preset (UInt64.ofNat indices.size) seed <;>
    simp [computeCommittee, shuffledCommittee, shuffle, zero, bind, Except.bind, throw, throwThe,
      MonadExcept.throw, MonadExceptOf.throw] at computed

/-- A successful shuffle uses the checked active indices, and then shuffles their positions. -/
theorem attesterShuffle_ok {state : BeaconState preset fork} {epoch : Epoch}
    {active : Array ValidatorIndex} {shuffled : Array UInt64}
    (computed : attesterShuffle state epoch = .ok (active, shuffled)) :
    ∃ seed, getSeed state epoch DOMAIN_BEACON_ATTESTER = .ok seed ∧
      computeShuffledPermutation preset
        (UInt64.ofNat (getActiveValidatorIndices state epoch).toArray.size) seed = .ok shuffled ∧
      active = (getActiveValidatorIndices state epoch).toArray := by
  simp only [attesterShuffle, bind_ok_iff] at computed
  obtain ⟨seed, seedOk, indices, indicesOk, rest⟩ := computed
  have same := getActiveValidatorIndicesChecked_ok indicesOk
  subst indices
  simp only [liftArith, mapError_ok_iff, pure, Except.pure, Except.ok.injEq,
    Prod.mk.injEq] at rest
  obtain ⟨count, countOk, _, shuffleOk, activeEq, rfl⟩ := rest
  obtain ⟨-, value⟩ := ofNatChecked_ok_iff.mp countOk
  have same : count = UInt64.ofNat (getActiveValidatorIndices state epoch).toArray.size := by
    rw [← value, UInt64.ofNat_toNat]
  subst same
  exact ⟨seed, seedOk, shuffleOk, activeEq.symm⟩

/-- A successful shuffle has checked every active registry position. -/
theorem getActiveValidatorIndicesChecked_of_attesterShuffle
    {state : BeaconState preset fork} {epoch : Epoch}
    {active : Array ValidatorIndex} {shuffled : Array UInt64}
    (computed : attesterShuffle state epoch = .ok (active, shuffled)) :
    getActiveValidatorIndicesChecked state epoch = .ok (getActiveValidatorIndices state epoch) := by
  simp only [attesterShuffle, bind_ok_iff] at computed
  obtain ⟨_, _, indices, checked, _⟩ := computed
  rw [getActiveValidatorIndicesChecked_ok checked] at checked
  exact checked

/-- A registry within its preset limit has the same checked and pure committee count. -/
theorem getCommitteeCountPerSlotChecked_of_within {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit) (epoch : Epoch) :
    getCommitteeCountPerSlotChecked state epoch = .ok (getCommitteeCountPerSlot state epoch) := by
  simp [getCommitteeCountPerSlotChecked, getCommitteeCountPerSlot,
    getActiveValidatorIndicesChecked_of_within within, liftArith,
    ofNatChecked_of_lt (length_getActiveValidatorIndices_lt within epoch), Except.mapError, bind,
    Except.bind, pure, Except.pure]

/-- A successful checked count agrees with the pure committee count. -/
theorem getCommitteeCountPerSlotChecked_ok {state : BeaconState preset fork} {epoch : Epoch}
    {count : UInt64} (computed : getCommitteeCountPerSlotChecked state epoch = .ok count) :
    count = getCommitteeCountPerSlot state epoch := by
  simp only [getCommitteeCountPerSlotChecked, bind_ok_iff, liftArith, mapError_ok_iff, pure,
    Except.pure, Except.ok.injEq] at computed
  obtain ⟨active, checked, converted, convertedOk, rfl⟩ := computed
  obtain rfl := getActiveValidatorIndicesChecked_ok checked
  obtain ⟨-, value⟩ := ofNatChecked_ok_iff.mp convertedOk
  rw [getCommitteeCountPerSlot, ← value, Nat.toUInt64_eq, UInt64.ofNat_toNat]

/-- A beacon committee that has a value is one committee cut from the active indices.

Its position counts the committees of the earlier slots of the epoch, then its index.

The count is the number of committees in the whole epoch. -/
theorem getBeaconCommittee_ok {state : BeaconState preset fork} {slot : Slot}
    {index : CommitteeIndex} {committee : Array ValidatorIndex}
    (computed : getBeaconCommittee state slot index = .ok committee) :
    ∃ seed position count,
      getSeed state (computeEpochAtSlot preset slot) DOMAIN_BEACON_ATTESTER = .ok seed ∧
      position.toNat = (slot % preset.SLOTS_PER_EPOCH).toNat *
        (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat + index.toNat ∧
      count.toNat = (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat *
        preset.SLOTS_PER_EPOCH.toNat ∧
      computeCommittee preset
        (getActiveValidatorIndices state (computeEpochAtSlot preset slot)).toArray seed position
        count = .ok committee := by
  simp only [getBeaconCommittee, bind_ok_iff] at computed
  obtain ⟨⟨active, shuffled⟩, shuffledOk, rest⟩ := computed
  obtain ⟨seed, seedOk, shuffleOk, rfl⟩ := attesterShuffle_ok shuffledOk
  simp only [beaconCommitteeOf, bind_ok_iff, liftArith, mapError_ok_iff,
    Base.Uint64.mulChecked_ok_iff, Base.Uint64.addChecked_ok_iff] at rest
  obtain ⟨position, ⟨product, ⟨_, productEq⟩, _, positionEq⟩,
    count, ⟨_, countEq⟩, committeeOk⟩ := rest
  refine ⟨seed, position, count, seedOk, by rw [positionEq, productEq], countEq, ?_⟩
  rw [computeCommittee, shuffleOk]
  exact committeeOk

/-- Each member of a committee is active in the epoch of its slot. -/
theorem mem_getActiveValidatorIndices_of_getBeaconCommittee {state : BeaconState preset fork}
    {slot : Slot} {index : CommitteeIndex} {committee : Array ValidatorIndex}
    (computed : getBeaconCommittee state slot index = .ok committee)
    {member : ValidatorIndex} (mem : member ∈ committee) :
    member ∈ getActiveValidatorIndices state (computeEpochAtSlot preset slot) := by
  obtain ⟨_, _, _, _, _, _, committeeOk⟩ := getBeaconCommittee_ok computed
  simpa using mem_of_computeCommittee committeeOk mem

/-- No validator is in two committees of one epoch.

Take two committees of slots of one epoch, each with an index below the committees of a slot.

If both hold one validator, their slots are equal and their indices are equal.

The registry must stay within its limit.

The number of active validators times the number of committees of the epoch must fit in 64 bits.
-/
theorem eq_of_mem_getBeaconCommittee {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit) {firstSlot secondSlot : Slot}
    {firstIndex secondIndex : CommitteeIndex}
    (sameEpoch : computeEpochAtSlot preset firstSlot = computeEpochAtSlot preset secondSlot)
    (firstLt : firstIndex < getCommitteeCountPerSlot state (computeEpochAtSlot preset firstSlot))
    (secondLt :
      secondIndex < getCommitteeCountPerSlot state (computeEpochAtSlot preset secondSlot))
    (fits : (getActiveValidatorIndices state (computeEpochAtSlot preset firstSlot)).length *
      ((getCommitteeCountPerSlot state (computeEpochAtSlot preset firstSlot)).toNat *
        preset.SLOTS_PER_EPOCH.toNat) < 2 ^ 64)
    {firstCommittee secondCommittee : Array ValidatorIndex}
    (first : getBeaconCommittee state firstSlot firstIndex = .ok firstCommittee)
    (second : getBeaconCommittee state secondSlot secondIndex = .ok secondCommittee)
    {member : ValidatorIndex} (firstMem : member ∈ firstCommittee)
    (secondMem : member ∈ secondCommittee) :
    firstSlot = secondSlot ∧ firstIndex = secondIndex := by
  obtain ⟨firstSeed, firstPosition, firstCount, firstSeedOk, firstPositionEq, firstCountEq,
    firstOk⟩ := getBeaconCommittee_ok first
  obtain ⟨secondSeed, secondPosition, secondCount, secondSeedOk, secondPositionEq,
    secondCountEq, secondOk⟩ := getBeaconCommittee_ok second
  rw [← sameEpoch] at secondSeedOk secondPositionEq secondCountEq secondOk secondLt
  rw [firstSeedOk, Except.ok.injEq] at secondSeedOk
  subst secondSeedOk
  have sameCount : firstCount = secondCount :=
    UInt64.toNat_inj.mp (firstCountEq.trans secondCountEq.symm)
  subst sameCount
  -- The names of the epoch's numbers, on natural numbers.
  generalize perSlotEq : (getCommitteeCountPerSlot state
    (computeEpochAtSlot preset firstSlot)).toNat = perSlot at *
  generalize epochLength : preset.SLOTS_PER_EPOCH.toNat = length at *
  have firstIndexLt : firstIndex.toNat < perSlot := perSlotEq ▸ UInt64.lt_iff_toNat_lt.mp firstLt
  have secondIndexLt : secondIndex.toNat < perSlot :=
    perSlotEq ▸ UInt64.lt_iff_toNat_lt.mp secondLt
  have lengthPos : 0 < length := by
    have nonzero := count_ne_zero_of_computeCommittee firstOk
    refine Nat.pos_of_ne_zero fun zero => nonzero (UInt64.toNat_inj.mp ?_)
    rw [firstCountEq, zero, Nat.mul_zero]
    rfl
  have firstModLt : (firstSlot % preset.SLOTS_PER_EPOCH).toNat < length := by
    rw [UInt64.toNat_mod, epochLength]
    exact Nat.mod_lt _ lengthPos
  have secondModLt : (secondSlot % preset.SLOTS_PER_EPOCH).toNat < length := by
    rw [UInt64.toNat_mod, epochLength]
    exact Nat.mod_lt _ lengthPos
  -- A position below the count: the earlier slots, then the index, stay below the epoch.
  have positionLt : ∀ slotPart indexPart, slotPart < length → indexPart < perSlot →
      slotPart * perSlot + indexPart < perSlot * length := by
    intro slotPart indexPart slotLt indexLt
    calc slotPart * perSlot + indexPart < slotPart * perSlot + perSlot := by omega
      _ = (slotPart + 1) * perSlot := (Nat.succ_mul _ _).symm
      _ ≤ length * perSlot := Nat.mul_le_mul_right _ slotLt
      _ = perSlot * length := Nat.mul_comm _ _
  have nodup : (getActiveValidatorIndices state
      (computeEpochAtSlot preset firstSlot)).toArray.toList.Nodup := by
    simpa [List.Nodup] using (getActiveValidatorIndices_sorted within _).imp UInt64.ne_of_lt
  have samePosition := eq_of_mem_computeCommittee (count := firstCount) nodup
    (by simpa [firstCountEq] using fits)
    (first := firstPosition.toNat) (second := secondPosition.toNat)
    (by rw [firstPositionEq, firstCountEq]; exact positionLt _ _ firstModLt firstIndexLt)
    (by rw [secondPositionEq, firstCountEq]; exact positionLt _ _ secondModLt secondIndexLt)
    (by simpa using firstOk) (by simpa using secondOk) firstMem secondMem
  rw [firstPositionEq, secondPositionEq] at samePosition
  -- The slot part and the index part of one position are equal.
  have perSlotPos : 0 < perSlot := Nat.zero_lt_of_lt firstIndexLt
  have split : ∀ a b c d, b < perSlot → d < perSlot → a * perSlot + b = c * perSlot + d →
      a = c ∧ b = d := by
    intro a b c d bLt dLt equal
    have divided := congrArg (· / perSlot) equal
    have reduced := congrArg (· % perSlot) equal
    simp only [Nat.mul_comm _ perSlot, Nat.mul_add_div perSlotPos, Nat.div_eq_of_lt bLt,
      Nat.div_eq_of_lt dLt, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt bLt,
      Nat.mod_eq_of_lt dLt] at divided reduced
    exact ⟨divided, reduced⟩
  obtain ⟨sameMod, sameIndex⟩ := split _ _ _ _ firstIndexLt secondIndexLt samePosition
  refine ⟨?_, UInt64.toNat_inj.mp sameIndex⟩
  -- A slot is its epoch times the length of an epoch, plus its place in the epoch.
  have epochNat := congrArg UInt64.toNat sameEpoch
  simp only [computeEpochAtSlot, UInt64.toNat_div, epochLength] at epochNat
  rw [UInt64.toNat_mod, UInt64.toNat_mod, epochLength] at sameMod
  apply UInt64.toNat_inj.mp
  rw [← Nat.div_add_mod firstSlot.toNat length, ← Nat.div_add_mod secondSlot.toNat length,
    epochNat, sameMod]

/-- Every active validator is in a committee of its epoch.

The committee has a slot of the epoch and an index below the committees of a slot.

The checked read of the active indices of the epoch must succeed.

The seed of the epoch must have a value, and an epoch must have at least one slot.

The slots of the epoch must fit in 64 bits.

There must be at most `2^40` active validators.

Their number times the number of committees of the epoch must fit in 64 bits. -/
theorem exists_mem_getBeaconCommittee {state : BeaconState preset fork} {epoch : Epoch}
    (indicesFit : getActiveValidatorIndicesChecked state epoch =
      .ok (getActiveValidatorIndices state epoch))
    {seed : Bytes32} (seedOk : getSeed state epoch DOMAIN_BEACON_ATTESTER = .ok seed)
    (positive : preset.SLOTS_PER_EPOCH ≠ 0)
    (slotsFit : (epoch.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat ≤ 2 ^ 64)
    (small : (getActiveValidatorIndices state epoch).length ≤ 2 ^ 40)
    (fits : (getActiveValidatorIndices state epoch).length *
      ((getCommitteeCountPerSlot state epoch).toNat * preset.SLOTS_PER_EPOCH.toNat) < 2 ^ 64)
    {member : ValidatorIndex} (active : member ∈ getActiveValidatorIndices state epoch) :
    ∃ slot index committee, computeEpochAtSlot preset slot = epoch ∧
      index < getCommitteeCountPerSlot state epoch ∧
      getBeaconCommittee state slot index = .ok committee ∧ member ∈ committee := by
  have lengthPos : 0 < preset.SLOTS_PER_EPOCH.toNat :=
    Nat.pos_of_ne_zero fun zero => positive (UInt64.toNat_inj.mp (by simpa using zero))
  have perPos : 0 < (getCommitteeCountPerSlot state epoch).toNat :=
    UInt64.le_iff_toNat_le.mp (one_le_getCommitteeCountPerSlot state epoch)
  have countFits : (getCommitteeCountPerSlot state epoch).toNat * preset.SLOTS_PER_EPOCH.toNat <
      2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (List.length_pos_of_mem active)) fits
  have countEq : (getCommitteeCountPerSlot state epoch * preset.SLOTS_PER_EPOCH).toNat =
      (getCommitteeCountPerSlot state epoch).toNat * preset.SLOTS_PER_EPOCH.toNat := by
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt countFits]
  have countPos : 0 < getCommitteeCountPerSlot state epoch * preset.SLOTS_PER_EPOCH :=
    UInt64.lt_iff_toNat_lt.mpr (by rw [countEq]; exact Nat.mul_pos perPos lengthPos)
  -- The validator is in committee `position` of the epoch.
  obtain ⟨position, positionLt, committee, computed, mem⟩ :=
    exists_mem_computeCommittee (preset := preset) (seed := seed)
      (indices := (getActiveValidatorIndices state epoch).toArray)
      (by simpa using small) (by simpa [countEq] using fits) countPos (by simpa using active)
  rw [countEq] at positionLt
  have perSmall := (getCommitteeCountPerSlot state epoch).toNat_lt
  generalize perEq : (getCommitteeCountPerSlot state epoch).toNat = perSlot at *
  generalize lengthEq : preset.SLOTS_PER_EPOCH.toNat = length at *
  -- That committee is committee `place mod perSlot` of the slot at `place` in the epoch.
  have placeLt : position / perSlot < length := Nat.div_lt_of_lt_mul positionLt
  have indexLt : position % perSlot < perSlot := Nat.mod_lt _ perPos
  have slotLt : epoch.toNat * length + position / perSlot < 2 ^ 64 := by
    have : epoch.toNat * length + position / perSlot < (epoch.toNat + 1) * length := by
      rw [Nat.succ_mul]
      omega
    omega
  have slotNat : (UInt64.ofNat (epoch.toNat * length + position / perSlot)).toNat =
      epoch.toNat * length + position / perSlot := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt slotLt]
  have indexNat : (UInt64.ofNat (position % perSlot)).toNat = position % perSlot := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have epochEq :
      computeEpochAtSlot preset (UInt64.ofNat (epoch.toNat * length + position / perSlot)) =
        epoch := by
    apply UInt64.toNat_inj.mp
    rw [computeEpochAtSlot, UInt64.toNat_div, slotNat, lengthEq, Nat.mul_comm,
      Nat.mul_add_div lengthPos, Nat.div_eq_of_lt placeLt, Nat.add_zero]
  have placeNat :
      (UInt64.ofNat (epoch.toNat * length + position / perSlot) % preset.SLOTS_PER_EPOCH).toNat =
        position / perSlot := by
    rw [UInt64.toNat_mod, slotNat, lengthEq, Nat.mul_comm, Nat.mul_add_mod,
      Nat.mod_eq_of_lt placeLt]
  refine ⟨UInt64.ofNat (epoch.toNat * length + position / perSlot),
    UInt64.ofNat (position % perSlot), committee, epochEq, ?_, ?_, mem⟩
  · exact UInt64.lt_iff_toNat_lt.mpr (by rw [indexNat, perEq]; exact indexLt)
  -- The checked products and sum of the position all fit, and give `position` back.
  have split : position / perSlot * perSlot + position % perSlot = position := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod _ _
  have productSmall : position / perSlot * perSlot < 2 ^ 64 := by omega
  have productOk := mulChecked_of_lt (a := UInt64.ofNat (epoch.toNat * length + position / perSlot)
    % preset.SLOTS_PER_EPOCH) (b := getCommitteeCountPerSlot state epoch)
    (by rw [placeNat, perEq]; exact productSmall)
  have productNat :
      (UInt64.ofNat (epoch.toNat * length + position / perSlot) % preset.SLOTS_PER_EPOCH *
        getCommitteeCountPerSlot state epoch).toNat = position / perSlot * perSlot := by
    rw [UInt64.toNat_mul, placeNat, perEq, Nat.mod_eq_of_lt productSmall]
  have sumOk := addChecked_of_lt
    (a := UInt64.ofNat (epoch.toNat * length + position / perSlot) % preset.SLOTS_PER_EPOCH *
      getCommitteeCountPerSlot state epoch) (b := UInt64.ofNat (position % perSlot))
    (by rw [productNat, indexNat, split]; omega)
  have countOk := mulChecked_of_lt (a := getCommitteeCountPerSlot state epoch)
    (b := preset.SLOTS_PER_EPOCH) (by rw [perEq, lengthEq]; exact countFits)
  have positionEq :
      UInt64.ofNat (epoch.toNat * length + position / perSlot) % preset.SLOTS_PER_EPOCH *
          getCommitteeCountPerSlot state epoch + UInt64.ofNat (position % perSlot) =
        UInt64.ofNat position := by
    apply UInt64.toNat_inj.mp
    rw [Base.Uint64.toNat_add_of_lt (by rw [productNat, indexNat, split]; omega), productNat,
      indexNat, split, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have activeSize : (UInt64.ofNat (getActiveValidatorIndices state epoch).toArray.size).toNat =
      (getActiveValidatorIndices state epoch).toArray.size :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by simpa using small) (by decide))
  have shuffleOk := computeShuffledPermutation_eq (preset := preset) (seed := seed)
    (count := UInt64.ofNat (getActiveValidatorIndices state epoch).toArray.size)
    (by rw [activeSize]; simpa using small)
  rw [computeCommittee_of_le (by simpa using small)] at computed
  have lengthOk : ofNatChecked (getActiveValidatorIndices state epoch).toArray.size =
      .ok (UInt64.ofNat (getActiveValidatorIndices state epoch).toArray.size) := by
    rw [ofNatChecked_of_lt (Nat.lt_of_le_of_lt (by simpa using small) (by decide)),
      Nat.toUInt64_eq]
  simp only [getBeaconCommittee, attesterShuffle, beaconCommitteeOf, epochEq, seedOk, indicesFit,
    lengthOk, shuffleOk, activeSize, liftArith, productOk, sumOk, countOk, bind, Except.bind,
    Except.mapError, pure, Except.pure, positionEq]
  rw [computed]

/-- A beacon committee is cut from the shuffle of the epoch of its slot.

The two sides fail with the same error too. -/
theorem getBeaconCommittee_eq (state : BeaconState preset fork) (slot : Slot)
    (index : CommitteeIndex) :
    getBeaconCommittee state slot index = (do
      let (active, shuffled) ← attesterShuffle state (computeEpochAtSlot preset slot)
      beaconCommitteeOf preset slot index
        (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)) active shuffled) :=
  rfl

/-- The members of the committees of a slot are those of each committee, one after the other.

The committees of the slot share one shuffle, and each committee alone gives the same members. -/
theorem slotCommitteeMembers_eq (state : BeaconState preset fork) (slot : Slot) :
    slotCommitteeMembers state slot =
      (List.range (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat).foldlM
        (fun members index => return members ++ (← getBeaconCommittee state slot index.toUInt64))
        #[] := by
  unfold slotCommitteeMembers slotCommitteeMembersOf
  have perPos : 0 < (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat :=
    UInt64.le_iff_toNat_le.mp (one_le_getCommitteeCountPerSlot _ _)
  obtain ⟨n, count⟩ : ∃ n,
      (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat = n + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos perPos).symm⟩
  cases shuffledOk : attesterShuffle state (computeEpochAtSlot preset slot) with
  | error e =>
    rw [count, List.range_succ_eq_map, List.foldlM_cons]
    simp [getBeaconCommittee, shuffledOk, bind, Except.bind]
  | ok pair =>
    simp only [shuffledOk, bind, Except.bind]
    congr 1
    funext members index
    simp [getBeaconCommittee, shuffledOk, bind, Except.bind, pure, Except.pure]

/-- A validator is among the members of a slot exactly when a beacon committee of it holds it. -/
theorem mem_slotCommitteeMembers {state : BeaconState preset fork} {slot : Slot}
    {members : Array ValidatorIndex} (found : slotCommitteeMembers state slot = .ok members)
    {validator : ValidatorIndex} :
    validator ∈ members ↔
      ∃ i < (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat,
        ∃ committee, getBeaconCommittee state slot i.toUInt64 = .ok committee ∧
          validator ∈ committee := by
  rw [slotCommitteeMembers_eq, foldlM_append_eq_flatten_mapM] at found
  simp only [bind, Except.bind] at found
  split at found
  · cases found
  rename_i committees mapped
  simp only [pure, Except.pure, Except.ok.injEq] at found
  subst found
  simp only [Array.empty_append, Array.mem_flatten, List.mem_toArray]
  constructor
  · rintro ⟨committee, member, holds⟩
    obtain ⟨i, inRange, made⟩ := mapM_ok_mem mapped committee member
    exact ⟨i, List.mem_range.mp inRange, committee, made, holds⟩
  · rintro ⟨i, inRange, committee, made, holds⟩
    have bound : i < (List.range
        (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat).length := by
      simpa using inRange
    have atIndex := mapM_ok_getElem mapped i bound
    rw [List.getElem_range, made] at atIndex
    cases atIndex
    exact ⟨_, List.getElem_mem _, holds⟩

/-- One step of the pass that drops repeats keeps its list decreasing, below the rest. -/
theorem keepNew_step {kept rest : List ValidatorIndex} {first : ValidatorIndex}
    (decreasing : kept.Pairwise (· > ·)) (keptLe : ∀ last ∈ kept, last ≤ first)
    (firstLe : ∀ index ∈ rest, first ≤ index) :
    (keepNew kept first).Pairwise (· > ·) ∧
      (∀ last ∈ keepNew kept first, ∀ index ∈ rest, last ≤ index) ∧
      ∀ index, index ∈ keepNew kept first ↔ index ∈ kept ∨ index = first := by
  have trans : ∀ a b c : UInt64, a ≤ b → b ≤ c → a ≤ c := fun a b c ab bc => by
    rw [UInt64.le_iff_toNat_le] at *; omega
  match kept with
  | [] => simpa [keepNew] using firstLe
  | last :: older =>
    by_cases same : last = first
    · subst same
      refine ⟨by simpa [keepNew] using decreasing, ?_, ?_⟩
      · intro other mem index inRest
        simp only [keepNew, ite_true] at mem
        exact trans _ _ _ (keptLe other mem) (firstLe index inRest)
      · intro index
        simp only [keepNew, ite_true, List.mem_cons]
        constructor
        · exact Or.inl
        · rintro (inKept | rfl)
          · exact inKept
          · exact Or.inl rfl
    · simp only [keepNew, same, ite_false]
      refine ⟨?_, ?_, ?_⟩
      · refine List.pairwise_cons.mpr ⟨fun other mem => ?_, decreasing⟩
        have otherLe := keptLe other mem
        have lastLe := keptLe last (by simp)
        rw [List.mem_cons] at mem
        rcases mem with rfl | inOlder
        · rw [UInt64.le_iff_toNat_le] at otherLe
          have : other.toNat ≠ first.toNat := fun eq => same (UInt64.toNat_inj.mp eq)
          show other < first
          rw [UInt64.lt_iff_toNat_lt]
          omega
        · have below := (List.pairwise_cons.mp decreasing).1 other inOlder
          show other < first
          rw [UInt64.lt_iff_toNat_lt]
          rw [UInt64.le_iff_toNat_le] at lastLe
          rw [gt_iff_lt, UInt64.lt_iff_toNat_lt] at below
          omega
      · intro other mem index inRest
        rw [List.mem_cons] at mem
        rcases mem with rfl | inKept
        · exact firstLe index inRest
        · exact trans _ _ _ (keptLe other inKept) (firstLe index inRest)
      · intro index
        simp only [List.mem_cons]
        constructor
        · rintro (rfl | inKept)
          · exact Or.inr rfl
          · exact Or.inl inKept
        · rintro (inKept | rfl)
          · exact Or.inr inKept
          · exact Or.inl rfl

/-- The pass that drops repeats, on a sorted list, onto a list kept in decreasing order. -/
theorem foldl_keepNew {indices kept : List ValidatorIndex}
    (sorted : indices.Pairwise (· ≤ ·)) (decreasing : kept.Pairwise (· > ·))
    (below : ∀ last ∈ kept, ∀ index ∈ indices, last ≤ index) :
    (indices.foldl keepNew kept).Pairwise (· > ·) ∧
      ∀ index, index ∈ indices.foldl keepNew kept ↔ index ∈ kept ∨ index ∈ indices := by
  induction indices generalizing kept with
  | nil => simpa using decreasing
  | cons first rest ih =>
    rw [List.pairwise_cons] at sorted
    obtain ⟨stepDecreasing, stepBelow, stepMem⟩ := keepNew_step (rest := rest) decreasing
      (fun last mem => below last mem first (by simp)) sorted.1
    obtain ⟨resultDecreasing, resultMem⟩ := ih sorted.2 stepDecreasing stepBelow
    refine ⟨resultDecreasing, fun index => ?_⟩
    rw [List.foldl_cons, resultMem, stepMem, List.mem_cons, or_assoc]

/-- The sort of a list of indices is in increasing order. -/
theorem mergeSort_sorted (indices : List ValidatorIndex) :
    (indices.mergeSort (· ≤ ·)).Pairwise (· ≤ ·) := by
  have sorted := List.pairwise_mergeSort (le := fun a b : UInt64 => decide (a ≤ b))
    (fun a b c ab bc => by simp only [decide_eq_true_eq, UInt64.le_iff_toNat_le] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq, UInt64.le_iff_toNat_le]; omega)
    indices
  simpa using sorted

/-- The pass over the sorted list gives a decreasing list with the same members. -/
theorem sortedSet_spec (indices : List ValidatorIndex) :
    ((indices.mergeSort (· ≤ ·)).foldl keepNew []).Pairwise (· > ·) ∧
      ∀ index, index ∈ (indices.mergeSort (· ≤ ·)).foldl keepNew [] ↔
        index ∈ [] ∨ index ∈ indices.mergeSort (· ≤ ·) :=
  foldl_keepNew (mergeSort_sorted indices) List.Pairwise.nil (by simp)

/-- The set of a list has the same members as the list. -/
theorem mem_sortedSet {indices : List ValidatorIndex} {index : ValidatorIndex} :
    index ∈ sortedSet indices ↔ index ∈ indices := by
  rw [sortedSet, List.mem_reverse, (sortedSet_spec indices).2, List.mem_mergeSort]
  simp

/-- The set of a list increases strictly, so it holds each index once. -/
theorem sortedSet_sorted (indices : List ValidatorIndex) :
    (sortedSet indices).Pairwise (· < ·) := by
  rw [sortedSet, List.pairwise_reverse]
  exact (sortedSet_spec indices).1

/-- Each attester of a committee is a member of it. -/
theorem mem_of_committeeAttesters {bits : Array Bool} {offset : Nat}
    {committee : Array ValidatorIndex} {attesters : List ValidatorIndex}
    (computed : committeeAttesters bits offset committee = .ok attesters)
    {attester : ValidatorIndex} (mem : attester ∈ attesters) : attester ∈ committee := by
  unfold committeeAttesters at computed
  split at computed
  · cases computed
  cases computed
  simp only [List.mem_filterMap, Option.ite_none_right_eq_some, Option.some.injEq,
    List.mem_zipIdx_iff_getElem?, Prod.exists] at mem
  obtain ⟨member, position, found, -, rfl⟩ := mem
  exact Array.mem_toList_iff.mp (List.mem_of_getElem? found)

/-- From Electra: with a shuffle that has a value, each committee of a list is read from the state.

The shuffle is that of the epoch of the slot, with its count of committees per slot.

The attesters of the list are those of the first committee, then those of the rest. -/
theorem committeesAttestersOf_cons_of_attesterShuffle {state : BeaconState preset fork}
    {slot : Slot} {active : Array ValidatorIndex} {shuffled : Array UInt64}
    (shuffleOk : attesterShuffle state (computeEpochAtSlot preset slot) = .ok (active, shuffled))
    (bits : Array Bool) (index : CommitteeIndex) (rest : List CommitteeIndex) (offset : Nat) :
    committeesAttestersOf preset slot bits
        (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)) active shuffled
        (index :: rest) offset = (do
      let committee ← getBeaconCommittee state slot index
      let here ← committeeAttesters bits offset committee
      return here ++ (← committeesAttestersOf preset slot bits
        (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)) active shuffled rest
        (offset + committee.size))) := by
  simp only [committeesAttestersOf, getBeaconCommittee_eq, shuffleOk, bind, Except.bind]

/-- A committee that has a value comes from a shuffle of the epoch of its slot that has one. -/
theorem attesterShuffle_ok_of_getBeaconCommittee {state : BeaconState preset fork}
    {slot : Slot} {index : CommitteeIndex} {committee : Array ValidatorIndex}
    (computed : getBeaconCommittee state slot index = .ok committee) :
    ∃ active shuffled,
      attesterShuffle state (computeEpochAtSlot preset slot) = .ok (active, shuffled) := by
  rw [getBeaconCommittee_eq] at computed
  cases shuffleOk : attesterShuffle state (computeEpochAtSlot preset slot) with
  | error e => simp only [shuffleOk, bind, Except.bind] at computed; cases computed
  | ok pair => exact ⟨pair.1, pair.2, rfl⟩

/-- With a shuffle that has a value, an attestation shows the signers cut from that shuffle.

The shuffle is that of the epoch of its slot, with its count of committees per slot. -/
theorem getAttestingIndices_of_attesterShuffle {state : BeaconState preset fork}
    {attestation : Attestation preset fork} {active : Array ValidatorIndex}
    {shuffled : Array UInt64}
    (shuffleOk : attesterShuffle state (computeEpochAtSlot preset attestation.data.slot) =
      .ok (active, shuffled)) :
    getAttestingIndices state attestation =
      attestingIndicesOf attestation
        (getCommitteeCountPerSlot state (computeEpochAtSlot preset attestation.data.slot)) active
        shuffled := by
  unfold getAttestingIndices
  split
  · rename_i unnamed
    obtain ⟨electra, empty⟩ := unnamed
    simp [attestingIndicesOf, electra, empty, committeesAttestersOf, sortedSet, Functor.map,
      Except.map]
  · simp only [shuffleOk, bind, Except.bind]

/-- Before Electra, the signers of an attestation are those of its one committee, as a set.

The committee is read from the state. -/
theorem getAttestingIndices_of_lt_electra (before : fork < .pectra)
    (state : BeaconState preset fork) (attestation : Attestation preset fork) :
    getAttestingIndices state attestation = (do
      let committee ← getBeaconCommittee state attestation.data.slot attestation.data.index
      return sortedSet (← committeeAttesters attestation.aggregationBits.bits 0 committee)) := by
  have notElectra : ¬.pectra ≤ fork := Nat.not_le_of_lt before
  unfold getAttestingIndices attestingIndicesOf
  split
  · rename_i unnamed
    exact absurd unnamed.1 notElectra
  rw [getBeaconCommittee_eq]
  cases shuffleOk : attesterShuffle state (computeEpochAtSlot preset attestation.data.slot) with
  | error e => simp only [shuffleOk, bind, Except.bind]
  | ok pair => simp only [shuffleOk, bind, Except.bind]

/-- The signers of an attestation are none, or are cut from a shuffle of its epoch with a value.

The shuffle is that of the epoch of its slot, with its count of committees per slot. -/
theorem getAttestingIndices_ok {state : BeaconState preset fork}
    {attestation : Attestation preset fork} {attesters : List ValidatorIndex}
    (computed : getAttestingIndices state attestation = .ok attesters) :
    attesters = [] ∨ ∃ active shuffled,
      attesterShuffle state (computeEpochAtSlot preset attestation.data.slot) =
        .ok (active, shuffled) ∧
      attestingIndicesOf attestation
        (getCommitteeCountPerSlot state (computeEpochAtSlot preset attestation.data.slot)) active
        shuffled = .ok attesters := by
  cases shuffleOk : attesterShuffle state (computeEpochAtSlot preset attestation.data.slot) with
  | ok pair =>
    exact .inr ⟨pair.1, pair.2, rfl, by rw [← getAttestingIndices_of_attesterShuffle shuffleOk,
      computed]⟩
  | error e =>
    unfold getAttestingIndices at computed
    split at computed
    · cases computed
      exact .inl rfl
    · simp only [shuffleOk, bind, Except.bind] at computed
      cases computed

/-- Each signer of an attestation sits in one of the committees that the attestation names.

Before Electra that committee has the index of the attestation.

From Electra its index is one of the committee bits, as [EIP-7549] specifies.

[EIP-7549]: https://eips.ethereum.org/EIPS/eip-7549#consensus-layer
-/
theorem exists_mem_getBeaconCommittee_of_getAttestingIndices {state : BeaconState preset fork}
    {attestation : Attestation preset fork} {attesters : List ValidatorIndex}
    (computed : getAttestingIndices state attestation = .ok attesters)
    {attester : ValidatorIndex} (mem : attester ∈ attesters) :
    ∃ index committee,
      (if electra : .pectra ≤ fork then
        index ∈ getCommitteeIndices (attestation.committeeBits electra)
      else index = attestation.data.index) ∧
      getBeaconCommittee state attestation.data.slot index = .ok committee ∧
      attester ∈ committee := by
  rcases getAttestingIndices_ok computed with rfl | ⟨active, shuffled, shuffleOk, computed⟩
  · simp at mem
  unfold attestingIndicesOf at computed
  split at computed
  · rename_i electra
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
    rename_i listed listedOk
    cases computed
    -- Each attester of the walk sits in a committee of the list that the walk reads.
    have walk : ∀ {committees : List CommitteeIndex} {offset : Nat} {listed : List ValidatorIndex},
        committeesAttestersOf preset attestation.data.slot attestation.aggregationBits.bits
          (getCommitteeCountPerSlot state (computeEpochAtSlot preset attestation.data.slot))
          active shuffled committees offset = .ok listed →
        attester ∈ listed → ∃ index ∈ committees, ∃ committee,
          getBeaconCommittee state attestation.data.slot index = .ok committee ∧
          attester ∈ committee := by
      intro committees
      induction committees with
      | nil =>
        intro offset listed computed mem
        cases computed
        simp at mem
      | cons index rest ih =>
        intro offset listed computed mem
        simp only [committeesAttestersOf_cons_of_attesterShuffle shuffleOk, bind, Except.bind,
          pure, Except.pure] at computed
        split at computed
        · cases computed
        rename_i committee committeeOk
        split at computed
        · cases computed
        rename_i here hereOk
        split at computed
        · cases computed
        rename_i later laterOk
        cases computed
        rcases List.mem_append.mp mem with inHere | inLater
        · exact ⟨index, List.mem_cons_self, committee, committeeOk,
            mem_of_committeeAttesters hereOk inHere⟩
        · obtain ⟨other, named, committee, committeeOk, inCommittee⟩ := ih laterOk inLater
          exact ⟨other, List.mem_cons_of_mem _ named, committee, committeeOk, inCommittee⟩
    obtain ⟨index, named, committee, committeeOk, inCommittee⟩ :=
      walk listedOk (mem_sortedSet.mp mem)
    exact ⟨index, committee, by simpa [electra] using named, committeeOk, inCommittee⟩
  · rename_i electra
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
    rename_i committee committeeOk
    split at computed
    · cases computed
    rename_i listed listedOk
    cases computed
    have readOk : getBeaconCommittee state attestation.data.slot attestation.data.index =
        .ok committee := by
      simp only [getBeaconCommittee_eq, shuffleOk, bind, Except.bind, committeeOk]
    exact ⟨_, committee, by simp [electra], readOk,
      mem_of_committeeAttesters listedOk (mem_sortedSet.mp mem)⟩

/-- Each validator that an attestation shows as a signer is active in the epoch of its slot. -/
theorem mem_getActiveValidatorIndices_of_getAttestingIndices {state : BeaconState preset fork}
    {attestation : Attestation preset fork} {attesters : List ValidatorIndex}
    (computed : getAttestingIndices state attestation = .ok attesters)
    {attester : ValidatorIndex} (mem : attester ∈ attesters) :
    attester ∈
      getActiveValidatorIndices state (computeEpochAtSlot preset attestation.data.slot) := by
  obtain ⟨_, _, -, committeeOk, inCommittee⟩ :=
    exists_mem_getBeaconCommittee_of_getAttestingIndices computed mem
  exact mem_getActiveValidatorIndices_of_getBeaconCommittee committeeOk inCommittee

/-- The validators that an attestation shows as signers increase strictly. -/
theorem getAttestingIndices_sorted {state : BeaconState preset fork}
    {attestation : Attestation preset fork} {attesters : List ValidatorIndex}
    (computed : getAttestingIndices state attestation = .ok attesters) :
    attesters.Pairwise (· < ·) := by
  rcases getAttestingIndices_ok computed with rfl | ⟨_, _, _, computed⟩
  · exact List.Pairwise.nil
  unfold attestingIndicesOf at computed
  split at computed <;>
  · simp only [bind, Except.bind, pure, Except.pure] at computed
    repeat' (split at computed; · cases computed)
    cases computed
    exact sortedSet_sorted _

/-- The pass that drops repeats adds at most one index for each index it reads. -/
theorem length_foldl_keepNew_le (indices kept : List ValidatorIndex) :
    (indices.foldl keepNew kept).length ≤ kept.length + indices.length := by
  induction indices generalizing kept with
  | nil => simp
  | cons first rest ih =>
    have step : (keepNew kept first).length ≤ kept.length + 1 := by
      unfold keepNew
      split
      · split <;> simp
      · simp
    have := ih (keepNew kept first)
    simp only [List.foldl_cons, List.length_cons]
    omega

/-- The set of a list has at most as many indices as the list. -/
theorem length_sortedSet_le (indices : List ValidatorIndex) :
    (sortedSet indices).length ≤ indices.length := by
  have := length_foldl_keepNew_le (indices.mergeSort (· ≤ ·)) []
  simpa [sortedSet, List.length_mergeSort] using this

/-- The attesters of a committee read one bit each, from an offset.

So they end before the last bit, and an empty committee has none, wherever its bits start. -/
theorem length_committeeAttesters {bits : Array Bool} {offset : Nat}
    {committee : Array ValidatorIndex} {attesters : List ValidatorIndex}
    (computed : committeeAttesters bits offset committee = .ok attesters) :
    attesters.length ≤ committee.size ∧
      (0 < committee.size → offset + committee.size ≤ bits.size) := by
  unfold committeeAttesters at computed
  split at computed
  · cases computed
  rename_i inRange
  cases computed
  refine ⟨Nat.le_trans (List.length_filterMap_le _ _) (by simp), fun nonempty => ?_⟩
  omega

/-- From Electra: the attesters of a list of committees end before the last bit. -/
theorem length_committeesAttestersOf {slot : Slot} {bits : Array Bool} {perSlot : UInt64}
    {active : Array ValidatorIndex} {shuffled : Array UInt64}
    {committees : List CommitteeIndex} {offset : Nat} {attesters : List ValidatorIndex}
    (computed : committeesAttestersOf preset slot bits perSlot active shuffled committees offset =
      .ok attesters) :
    offset + attesters.length ≤ max offset bits.size := by
  induction committees generalizing offset attesters with
  | nil =>
    cases computed
    simp only [List.length_nil, Nat.add_zero]
    omega
  | cons index rest ih =>
    simp only [committeesAttestersOf, bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
    rename_i committee _
    split at computed
    · cases computed
    rename_i here hereOk
    split at computed
    · cases computed
    rename_i later laterOk
    cases computed
    obtain ⟨hereLe, reach⟩ := length_committeeAttesters hereOk
    have second := ih laterOk
    simp only [List.length_append]
    -- An empty committee moves no offset; a nonempty one ends before the last bit.
    by_cases empty : committee.size = 0
    · simp only [empty, Nat.add_zero] at second
      omega
    · have := reach (Nat.pos_of_ne_zero empty)
      omega

/-- The validators that an attestation shows as signers are at most its bits. -/
theorem length_getAttestingIndices_le {state : BeaconState preset fork}
    {attestation : Attestation preset fork} {attesters : List ValidatorIndex}
    (computed : getAttestingIndices state attestation = .ok attesters) :
    attesters.length ≤ attestation.aggregationBits.bits.size := by
  rcases getAttestingIndices_ok computed with rfl | ⟨_, _, _, computed⟩
  · exact Nat.zero_le _
  unfold attestingIndicesOf at computed
  split at computed
  · simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
    rename_i listed listedOk
    cases computed
    have := length_committeesAttestersOf listedOk
    have := length_sortedSet_le listed
    omega
  · simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
    split at computed
    · cases computed
    rename_i committee _ _ listed listedOk
    cases computed
    obtain ⟨short, reach⟩ := length_committeeAttesters listedOk
    have := length_sortedSet_le listed
    by_cases empty : committee.size = 0
    · omega
    · have := reach (Nat.pos_of_ne_zero empty)
      omega

/-- The check of the limit on an indexed attestation never fails.

Before Gloas the signers are at most the bits, and the bits are at most the limit.

From Gloas the list has no limit.

So the indexed form fails exactly when the signers do, with the same error. -/
theorem getIndexedAttestation_eq_error_iff {state : BeaconState preset fork}
    {attestation : Attestation preset fork} {error : AccessorError} :
    getIndexedAttestation state attestation = .error error ↔
      getAttestingIndices state attestation = .error error := by
  simp only [getIndexedAttestation, indexedAttestationOf, bind, Except.bind]
  split
  · rename_i failure
    simp [failure]
  · rename_i attesters attestersOk
    simp only [attestersOk, reduceCtorEq, iff_false]
    split
    · simp [pure, Except.pure]
    · rename_i over
      exact absurd (fun before => Nat.le_trans (length_getAttestingIndices_le attestersOk)
        (attestation.aggregationBits.bound before)) over

/-- The signers of an indexed attestation that has a value are the signers of the attestation. -/
theorem getAttestingIndices_of_getIndexedAttestation {state : BeaconState preset fork}
    {attestation : Attestation preset fork} {indexed : IndexedAttestation preset fork}
    (computed : getIndexedAttestation state attestation = .ok indexed) :
    ∃ attesters, getAttestingIndices state attestation = .ok attesters ∧
      indexed.attestingIndices.data = attesters.toArray := by
  simp only [getIndexedAttestation, indexedAttestationOf, bind, Except.bind] at computed
  split at computed
  · cases computed
  rename_i attesters attestersOk
  split at computed
  · cases computed
    exact ⟨attesters, attestersOk, rfl⟩
  · cases computed

/-- The indices of an indexed attestation increase strictly, as its validity check asks. -/
theorem getIndexedAttestation_sorted {state : BeaconState preset fork}
    {attestation : Attestation preset fork} {indexed : IndexedAttestation preset fork}
    (computed : getIndexedAttestation state attestation = .ok indexed) :
    indexed.attestingIndices.data.toList.Pairwise (· < ·) := by
  obtain ⟨attesters, attestersOk, data⟩ := getAttestingIndices_of_getIndexedAttestation computed
  rw [data]
  exact getAttestingIndices_sorted attestersOk

/-- When the signers of an attestation have a value, its indexed form lists them in order. -/
theorem getIndexedAttestation_of_getAttestingIndices {state : BeaconState preset fork}
    {attestation : Attestation preset fork} {attesters : List ValidatorIndex}
    (computed : getAttestingIndices state attestation = .ok attesters) :
    ∃ indexed, getIndexedAttestation state attestation = .ok indexed ∧
      indexed.attestingIndices.data = attesters.toArray ∧ indexed.data = attestation.data ∧
      indexed.signature = attestation.signature := by
  simp only [getIndexedAttestation, indexedAttestationOf, bind, Except.bind, computed]
  split
  · exact ⟨_, rfl, rfl, rfl, rfl⟩
  · rename_i over
    exact absurd (fun before => Nat.le_trans (length_getAttestingIndices_le computed)
      (attestation.aggregationBits.bound before)) over

/-- The proposer search returns one of the indices, when each position of the order is in range. -/
theorem mem_of_proposerSearch {preset : Preset} {fork : Base.Fork}
    {validators : Array Validator} {indices : Array ValidatorIndex} {order : Nat → Nat}
    {seed : Bytes32} (nonempty : 0 < indices.size)
    (positions : ∀ place < indices.size, order place < indices.size)
    {i : Nat} {proposer : ValidatorIndex}
    (found : proposerSearch preset fork validators indices order seed i = .ok proposer) :
    proposer ∈ indices := by
  -- The candidate of every step is one of the indices.
  have candidateMem : ∀ j, indices.getD (order (j % indices.size)) 0 ∈ indices := by
    intro j
    have lt := positions _ (Nat.mod_lt j nonempty)
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem lt, Option.getD_some]
    exact Array.getElem_mem lt
  -- Each step either returns its candidate or moves closer to the end of the counter.
  obtain ⟨left, leftEq⟩ : ∃ left, left = 2 ^ 64 - i := ⟨_, rfl⟩
  induction left using Nat.strongRecOn generalizing i with
  | _ left ih =>
    unfold proposerSearch at found
    simp only [bind, Except.bind, pure, Except.pure] at found
    split at found
    · split at found
      · cases found
      split at found
      · cases found
        exact candidateMem i
      split at found
      · exact ih (2 ^ 64 - (i + 1)) (by omega) found rfl
      · simp [throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at found
    · simp [throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at found

/-- A proposer is one of the indices it is drawn from. -/
theorem mem_of_computeProposerIndex {state : BeaconState preset fork}
    {indices : Array ValidatorIndex} {seed : Bytes32} {proposer : ValidatorIndex}
    (computed : computeProposerIndex state indices seed = .ok proposer) :
    proposer ∈ indices := by
  unfold computeProposerIndex at computed
  by_cases empty : indices.size = 0
  · simp [empty, bind, Except.bind, throw, throwThe, MonadExcept.throw,
      MonadExceptOf.throw] at computed
  by_cases fits : indices.size < 2 ^ 64
  · by_cases large : 2 ^ 40 < indices.size
    · simp [empty, fits, large, bind, Except.bind, throw, throwThe, MonadExcept.throw,
        MonadExceptOf.throw] at computed
    simp only [empty, fits, large, ↓reduceIte] at computed
    exact mem_of_proposerSearch (Nat.pos_of_ne_zero empty)
      (fun place lt => Shuffle.shuffledIndex_lt lt) computed
  · simp [empty, fits, bind, Except.bind, throw, throwThe, MonadExcept.throw,
      MonadExceptOf.throw] at computed

/-- Two orders that agree on the positions below the number of indices give one proposer search.

The search reads the order only at a candidate number modulo that number. -/
theorem proposerSearch_congr {preset : Preset} {fork : Base.Fork}
    {validators : Array Validator} {indices : Array ValidatorIndex} {first second : Nat → Nat}
    {seed : Bytes32} (nonempty : 0 < indices.size)
    (agree : ∀ place < indices.size, first place = second place) :
    ∀ {i : Nat}, proposerSearch preset fork validators indices first seed i =
      proposerSearch preset fork validators indices second seed i := by
  intro i
  obtain ⟨left, leftEq⟩ : ∃ left, left = 2 ^ 64 - i := ⟨_, rfl⟩
  induction left using Nat.strongRecOn generalizing i with
  | _ left ih =>
    unfold proposerSearch
    simp only [agree _ (Nat.mod_lt i nonempty), bind, Except.bind]
    repeat' split
    all_goals first
      | rfl
      | exact ih _ (by omega) rfl

/-- The proposer draw returns what a walk over the full shuffle of its indices returns.

Each position it shuffles alone lands where the full shuffle puts it, and the errors agree. -/
theorem computeProposerIndex_eq (state : BeaconState preset fork) (indices : Array ValidatorIndex)
    (seed : Bytes32) :
    computeProposerIndex state indices seed = (do
      if indices.size = 0 then throw .noCandidates
      unless indices.size < 2 ^ 64 do throw (.arith .overflow)
      let shuffled ←
        (computeShuffledPermutation preset indices.size.toUInt64 seed).mapError .shuffle
      proposerSearch preset fork state.validators.data indices
        (fun place => (shuffled.getD place 0).toNat) seed 0) := by
  unfold computeProposerIndex
  by_cases empty : indices.size = 0
  · simp [empty, bind, Except.bind, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]
  by_cases fits : indices.size < 2 ^ 64
  · have sizeEq : indices.size.toUInt64.toNat = indices.size := by
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt fits]
    by_cases large : 2 ^ 40 < indices.size
    · rw [computeShuffledPermutation_countTooLarge (by rw [sizeEq]; exact large)]
      simp [empty, fits, large, Except.mapError, bind, Except.bind, throw, throwThe,
        MonadExcept.throw, MonadExceptOf.throw]
    simp only [empty, fits, large, ↓reduceIte,
      computeShuffledPermutation_eq (by rw [sizeEq]; exact Nat.le_of_not_lt large), sizeEq,
      Except.mapError, bind, Except.bind]
    -- Both read the shuffled position of each candidate.
    refine proposerSearch_congr (Nat.pos_of_ne_zero empty) fun place lt => ?_
    change Shuffle.shuffledIndex preset.SHUFFLE_ROUND_COUNT.toNat seed indices.size place = _
    rw [Array.getD_eq_getD_getElem?, Shuffle.shuffledPositions_getElem lt, Option.getD_some,
      UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_trans (Shuffle.shuffledIndex_lt lt) fits)]
  · simp [empty, fits, bind, Except.bind, throw, throwThe, MonadExcept.throw,
      MonadExceptOf.throw]

/-- Before Fulu, the proposer of a slot is active in the epoch of the state. -/
theorem mem_getActiveValidatorIndices_of_getBeaconProposerIndex
    {state : BeaconState preset fork} (beforeFulu : ¬.fusaka ≤ fork)
    {proposer : ValidatorIndex} (computed : getBeaconProposerIndex state = .ok proposer) :
    proposer ∈ getActiveValidatorIndices state (getCurrentEpoch state) := by
  simp only [getBeaconProposerIndex, beforeFulu, ↓reduceDIte, bind, Except.bind] at computed
  split at computed
  · cases computed
  split at computed
  · cases computed
  have same := getActiveValidatorIndicesChecked_ok (show
    getActiveValidatorIndicesChecked state (getCurrentEpoch state) = .ok _ from by assumption)
  subst same
  simpa using mem_of_computeProposerIndex computed

/-- A domain always has a value. -/
theorem getDomain_total (config : Config) (state : BeaconState preset fork)
    (domainType : DomainType) (epoch : Option Epoch) :
    ∃ domain, getDomain config state domainType epoch = .ok domain := by
  unfold getDomain
  obtain ⟨domain, computed⟩ := computeDomain_total config domainType
    (if epoch.getD (getCurrentEpoch state) < state.forkVersions.epoch then
      state.forkVersions.previousVersion else state.forkVersions.currentVersion)
    state.genesisValidatorsRoot
  exact ⟨domain, by simp only [computed]; rfl⟩

/-- A write to a circular buffer of nonzero length replaces the entry at position `i mod n`. -/
theorem writeCircular_of_ne_zero {α : Type} {n : UInt64} (buffer : Vector α n.toNat)
    (i : UInt64) (value : α) (nonzero : n ≠ 0) :
    writeCircular buffer i value =
      .ok (buffer.set (i % n).toNat value (toNat_mod_lt nonzero)) := by
  simp [writeCircular, nonzero]

/-- A write to a circular buffer of length zero is a division-by-zero error. -/
theorem writeCircular_zero {α : Type} (buffer : Vector α (0 : UInt64).toNat) (i : UInt64)
    (value : α) : writeCircular buffer i value = .error (.arith .divisionByZero) := by
  simp [writeCircular]

/-- A write to a circular buffer holds its value at position `i mod n`. -/
theorem getElem?_writeCircular {α : Type} {n : UInt64} {buffer written : Vector α n.toNat}
    {i : UInt64} {value : α} (computed : writeCircular buffer i value = .ok written) :
    written[(i % n).toNat]? = some value := by
  unfold writeCircular at computed
  split at computed
  · cases computed
  · cases computed
    simp

/-- A write to a circular buffer is read back at the position it wrote. -/
theorem readCircular_writeCircular {α : Type} {n : UInt64} {buffer written : Vector α n.toNat}
    {i : UInt64} {value : α} (computed : writeCircular buffer i value = .ok written) :
    readCircular written i = .ok value := by
  unfold writeCircular at computed
  split at computed
  · cases computed
  · next nonzero =>
    cases computed
    simp [readCircular, nonzero]

/-- Two numbers that differ by less than a length lie at different positions modulo it. -/
theorem _root_.Nat.mod_ne_of_sub_lt {low high length : Nat} (lt : low < high)
    (close : high - low < length) : high % length ≠ low % length := by
  intro same
  have zero := Nat.sub_mod_eq_zero_of_mod_eq same
  rw [Nat.mod_eq_of_lt close] at zero
  omega

/-- A write to a circular buffer leaves the entry at every other position unchanged. -/
theorem readCircular_writeCircular_of_ne {α : Type} {n : UInt64}
    {buffer written : Vector α n.toNat} {i j : UInt64} {value : α}
    (computed : writeCircular buffer i value = .ok written) (other : i % n ≠ j % n) :
    readCircular written j = readCircular buffer j := by
  unfold writeCircular at computed
  split at computed
  · cases computed
  · next nonzero =>
    cases computed
    have differ : i.toNat % n.toNat ≠ j.toNat % n.toNat := by
      rw [← UInt64.toNat_mod, ← UInt64.toNat_mod]
      exact fun same => other (UInt64.toNat_inj.mp same)
    simp [readCircular, nonzero, differ]

/-- A write to a circular buffer that keeps its tree writes its elements as a plain buffer. -/
theorem writeCircularRooted_elements {α : Type} [SszType α] {n : UInt64}
    (buffer : RootedVector α n.toNat) (i : UInt64) (value : α) :
    RootedVector.elements <$> writeCircularRooted buffer i value
      = writeCircular buffer.elements i value := by
  unfold writeCircularRooted writeCircular
  split <;> rfl

/-- A read of a circular buffer of positive length succeeds. -/
theorem readCircular_total {α : Type} {n : UInt64} [NeZero n.toNat] (buffer : Vector α n.toNat)
    (i : UInt64) : ∃ value, readCircular buffer i = .ok value :=
  ⟨_, by rw [readCircular, dite_eq_right ne_zero_of_neZero_toNat]⟩

/-- A write to a circular buffer of positive length succeeds. -/
theorem writeCircular_total {α : Type} {n : UInt64} [NeZero n.toNat] (buffer : Vector α n.toNat)
    (i : UInt64) (value : α) : ∃ written, writeCircular buffer i value = .ok written :=
  ⟨_, writeCircular_of_ne_zero buffer i value ne_zero_of_neZero_toNat⟩

/-- A write to a circular buffer of positive length that keeps its tree succeeds. -/
theorem writeCircularRooted_total {α : Type} [SszType α] {n : UInt64} [NeZero n.toNat]
    (buffer : RootedVector α n.toNat) (i : UInt64) (value : α) :
    ∃ written, writeCircularRooted buffer i value = .ok written := by
  simp [writeCircularRooted, ne_zero_of_neZero_toNat (n := n)]

/-- A read of a block root is before the slot of the state, and reads the buffer of roots. -/
theorem getBlockRootAtSlot_read {state : BeaconState preset fork} {slot : Slot} {root : Root}
    (computed : getBlockRootAtSlot state slot = .ok root) :
    slot < state.slot ∧ readCircular state.blockRoots.elements slot = .ok root := by
  unfold getBlockRootAtSlot at computed
  by_cases lt : slot < state.slot
  · simp only [lt, ↓reduceIte, bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact ⟨lt, computed⟩
    · cases computed
  · simp only [lt, ↓reduceIte, bind_ok_iff] at computed
    obtain ⟨_, thrown, _⟩ := computed
    cases thrown

/-- A read of the root of an epoch is a read of the root at the first slot of the epoch. -/
theorem getBlockRoot_ok_iff {state : BeaconState preset fork} {epoch : Epoch} {root : Root} :
    getBlockRoot state epoch = .ok root ↔ ∃ start,
      computeStartSlotAtEpoch preset epoch = .ok start ∧
        getBlockRootAtSlot state start = .ok root := by
  unfold getBlockRoot
  simp only [bind_ok_iff, liftArith, mapError_ok_iff]

/-- A read of the root of an epoch reads a slot before the slot of the state. -/
theorem getBlockRoot_start_lt {state : BeaconState preset fork} {epoch : Epoch} {root : Root}
    (computed : getBlockRoot state epoch = .ok root) :
    epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < state.slot.toNat := by
  obtain ⟨start, startOk, read⟩ := getBlockRoot_ok_iff.mp computed
  rw [← (mulChecked_ok_iff.mp startOk).2]
  exact UInt64.lt_iff_toNat_lt.mp (getBlockRootAtSlot_read read).1

/-- A read of a recorded root succeeds exactly when the slot is recent and its bound fits.

The read of the buffer must then succeed too. -/
theorem getBlockRootAtSlot_ok_iff {state : BeaconState preset fork}
    {slot : Slot} {root : Root} :
    getBlockRootAtSlot state slot = .ok root ↔ slot.toNat < state.slot.toNat ∧
      slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat < 2 ^ 64 ∧
      state.slot.toNat ≤ slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat ∧
      readCircular state.blockRoots.elements slot = .ok root := by
  unfold getBlockRootAtSlot
  by_cases lt : slot < state.slot
  · simp only [lt, ↓reduceIte, bind_ok_iff, liftArith, mapError_ok_iff, addChecked_ok_iff]
    have lt' := UInt64.lt_iff_toNat_lt.mp lt
    constructor
    · rintro ⟨bound, ⟨fits, boundEq⟩, rest⟩
      by_cases within : state.slot ≤ bound
      · simp only [within, ↓reduceIte] at rest
        exact ⟨lt', fits, boundEq ▸ UInt64.le_iff_toNat_le.mp within, rest⟩
      · simp only [within, ↓reduceIte, bind_ok_iff] at rest
        obtain ⟨_, thrown, _⟩ := rest
        cases thrown
    · rintro ⟨-, fits, within, rest⟩
      have sum : (slot + preset.SLOTS_PER_HISTORICAL_ROOT).toNat =
          slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
        rw [UInt64.toNat_add, Nat.mod_eq_of_lt fits]
      refine ⟨slot + preset.SLOTS_PER_HISTORICAL_ROOT, ⟨fits, sum⟩, ?_⟩
      simp only [UInt64.le_iff_toNat_le.mpr (sum ▸ within), ↓reduceIte]
      exact rest
  · have lt' : ¬slot.toNat < state.slot.toNat := fun lt' => lt (UInt64.lt_iff_toNat_lt.mpr lt')
    simp only [lt, lt', ↓reduceIte, false_and, iff_false]
    intro computed
    rw [bind_ok_iff] at computed
    obtain ⟨_, thrown, _⟩ := computed
    cases thrown

/-- A read of a recorded root fails only for a slot out of range.

It needs the slot of the state plus the length of the buffer of roots to be at most `2^64`. -/
theorem getBlockRootAtSlot_error {state : BeaconState preset fork} {slot : Slot}
    {fault : AccessorError}
    (room : state.slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat ≤ 2 ^ 64)
    (failed : getBlockRootAtSlot state slot = .error fault) :
    fault = .slotOutOfRange slot state.slot := by
  unfold getBlockRootAtSlot at failed
  by_cases before : slot < state.slot
  · -- The bound of a slot before the state fits, so only the range checks can fail.
    have bound : Uint64.addChecked slot preset.SLOTS_PER_HISTORICAL_ROOT =
        .ok (slot + preset.SLOTS_PER_HISTORICAL_ROOT) :=
      Uint64.addChecked_of_lt (by have := UInt64.lt_iff_toNat_lt.mp before; omega)
    by_cases within : state.slot ≤ slot + preset.SLOTS_PER_HISTORICAL_ROOT
    · have nonzero : preset.SLOTS_PER_HISTORICAL_ROOT ≠ 0 := by
        intro zero
        rw [zero, UInt64.add_zero] at within
        exact absurd before (UInt64.not_lt.mpr within)
      simp [before, liftArith, bound, within, readCircular, nonzero, Except.mapError, bind,
        Except.bind] at failed
    · simp [before, liftArith, bound, within, throw, throwThe, MonadExceptOf.throw,
        Except.mapError, bind, Except.bind] at failed
      exact failed.symm
  · simp [before, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at failed
    exact failed.symm

/-- A read of a recorded root succeeds when the slot is recent and its bound does not overflow.

The buffer of roots must not be empty. -/
theorem getBlockRootAtSlot_exists {state : BeaconState preset fork}
    {slot : Slot} (before : slot.toNat < state.slot.toNat)
    (fits : slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat < 2 ^ 64)
    (within : state.slot.toNat ≤ slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (nonempty : 0 < preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    ∃ root, getBlockRootAtSlot state slot = .ok root := by
  have : NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat := ⟨Nat.pos_iff_ne_zero.mp nonempty⟩
  obtain ⟨root, read⟩ := readCircular_total state.blockRoots.elements slot
  exact ⟨root, getBlockRootAtSlot_ok_iff.mpr ⟨before, fits, within, read⟩⟩

/-- A read of the root of an epoch succeeds when the first slot of the epoch is recent.

The bound of that slot must not overflow. -/
theorem getBlockRoot_exists {state : BeaconState preset fork} {epoch : Epoch}
    (before : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < state.slot.toNat)
    (fits : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat <
      2 ^ 64)
    (within : state.slot.toNat ≤
      epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    ∃ root, getBlockRoot state epoch = .ok root := by
  obtain ⟨start, startEq⟩ := exists_toNat_eq
    (n := epoch.toNat * preset.SLOTS_PER_EPOCH.toNat) (by omega)
  have startOk : computeStartSlotAtEpoch preset epoch = .ok start :=
    mulChecked_ok_iff.mpr ⟨by omega, startEq⟩
  obtain ⟨root, read⟩ := getBlockRootAtSlot_exists (state := state) (slot := start)
    (by omega) (by omega) (by omega) (by omega)
  exact ⟨root, getBlockRoot_ok_iff.mpr ⟨start, startOk, read⟩⟩

/-- A read of a recorded root succeeds at each slot between two slots where it succeeds. -/
theorem getBlockRootAtSlot_between {state : BeaconState preset fork}
    {low middle high : Slot} {lowRoot highRoot : Root}
    (lowRead : getBlockRootAtSlot state low = .ok lowRoot)
    (highRead : getBlockRootAtSlot state high = .ok highRoot)
    (above : low.toNat ≤ middle.toNat) (below : middle.toNat ≤ high.toNat) :
    ∃ root, getBlockRootAtSlot state middle = .ok root := by
  obtain ⟨-, -, lowWithin, -⟩ := getBlockRootAtSlot_ok_iff.mp lowRead
  obtain ⟨highLt, highFits, -, highBuffer⟩ := getBlockRootAtSlot_ok_iff.mp highRead
  unfold readCircular at highBuffer
  split at highBuffer
  · cases highBuffer
  rename_i nonzero
  exact getBlockRootAtSlot_exists (by omega) (by omega) (by omega)
    (Nat.pos_of_ne_zero fun zero => nonzero (UInt64.toNat_inj.mp (by simpa using zero)))

/-- Two states with the same slot and buffer of roots read the same root at each slot. -/
theorem getBlockRootAtSlot_congr {post : Fork} {state : BeaconState preset fork}
    {other : BeaconState preset post} (slot : other.slot = state.slot)
    (roots : other.blockRoots = state.blockRoots) (index : Slot) :
    getBlockRootAtSlot other index = getBlockRootAtSlot state index := by
  simp only [getBlockRootAtSlot, slot, roots]

end EthLib.Consensus
