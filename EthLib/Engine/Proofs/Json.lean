module

public import EthLib.Engine.Json
public import EthLib.Serialization.Proofs.JsonRpc
public import EthLib.Execution.Proofs.Rpc.Json
public import EthLib.Base.Except
public import EthLib.Base.Proofs.Fork
-- Showing that a payload field is not `null` unfolds the null test of Lean's JSON.
import all Lean.Data.Json.Basic

/-!
# Proofs: the JSON decoders of the Engine API

A shared reader, run as an Engine decoding, returns what the reader returns.

A reader that rejects its input becomes an invalid parameter, for the same reason.

A decoded payload has version 1, 2 or 3 of the structure.

It holds the withdrawals exactly from version 2.

It holds the two blob gas fields exactly in version 3.

A payload of version 4 decodes only when its object holds exactly the fields of that version.

Its access list and its slot must then decode.

The rest must decode as a payload of an earlier version.

A field from a fork decodes exactly when it is present from that fork on and absent before.

A field decodes from an option exactly when reading the field back gives that option.

The decoders read back the payloads that the writers write.

The extra data must then hold at most 32 bytes.

A JSON value reads as a payload status exactly when it is an object of this form.

Its members that are not `null` are `status`, `latestValidHash` and `validationError` alone.

The status is one of the five names, the hash 32 bytes in lowercase hex, and the error a string.

The hash and the error may be absent.
-/

public section

namespace EthLib.Engine.Json

open EthLib.Base
open EthLib.Serialization.JsonRpc
open EthLib.Execution.Blocks (MAX_EXTRA_DATA_BYTES)

/-- A failure with an invalid parameter is that error, never a value. -/
@[simp] theorem invalid_eq {α : Type} (reason : String) :
    (invalid reason : Decode α) = .error (.invalidParams reason) := rfl

/-- A shared reader returns a value as a decoding exactly when it returns it alone. -/
@[simp] theorem liftM_eq_ok_iff {α : Type} {r : Read α} {a : α} :
    (liftM r : Decode α) = .ok a ↔ r = .ok a := by
  cases r <;> simp [liftM, monadLift, MonadLift.monadLift, lift, Except.mapError]

/-- A shared reader that rejects its input fails as a decoding with an invalid parameter. -/
@[simp] theorem liftM_error {α : Type} (reason : String) :
    (liftM (.error reason : Read α) : Decode α) = .error (.invalidParams reason) := rfl

/-- A value that a shared reader returns is what the decoding returns. -/
@[simp] theorem liftM_ok {α : Type} (a : α) : (liftM (.ok a : Read α) : Decode α) = .ok a :=
  rfl

/-- A decoded payload has version 1, 2 or 3, and its optional fields match that version. -/
theorem shape_of_anyPayload {j : Lean.Json} {p : AnyPayload} (h : anyPayload j = .ok p) :
    (p.version = 1 ∨ p.version = 2 ∨ p.version = 3) ∧ (p.withdrawals.isSome ↔ 2 ≤ p.version) ∧
      (p.blobGasUsed.isSome ↔ 3 ≤ p.version) ∧ (p.excessBlobGas.isSome ↔ 3 ≤ p.version) := by
  unfold anyPayload at h
  -- Inline the steps that the decoder shares between its branches.
  dsimp only at h
  -- Split each step of the decoder: a failing step contradicts the success, and a read value stays.
  repeat' (first
    | (simp only [invalid_eq] at h; cases h; done)
    | (obtain ⟨_, step, h⟩ := bind_ok_iff.mp h
       first | cases step | obtain ⟨_, -, rfl⟩ := map_ok_iff.mp step | skip)
    | split at h)
  -- Each success fixes the version and the fields.
  all_goals (cases h; simp)

/-- A decoded payload has version 1, 2 or 3. -/
theorem version_of_anyPayload {j : Lean.Json} {p : AnyPayload} (h : anyPayload j = .ok p) :
    p.version = 1 ∨ p.version = 2 ∨ p.version = 3 :=
  (shape_of_anyPayload h).1

/-- A decoded payload holds the withdrawals exactly from version 2. -/
theorem withdrawals_isSome_iff_of_anyPayload {j : Lean.Json} {p : AnyPayload}
    (h : anyPayload j = .ok p) : p.withdrawals.isSome ↔ 2 ≤ p.version :=
  (shape_of_anyPayload h).2.1

/-- A decoded payload holds the blob gas used exactly in version 3. -/
theorem blobGasUsed_isSome_iff_of_anyPayload {j : Lean.Json} {p : AnyPayload}
    (h : anyPayload j = .ok p) : p.blobGasUsed.isSome ↔ 3 ≤ p.version :=
  (shape_of_anyPayload h).2.2.1

/-- A decoded payload holds the excess blob gas exactly in version 3. -/
theorem excessBlobGas_isSome_iff_of_anyPayload {j : Lean.Json} {p : AnyPayload}
    (h : anyPayload j = .ok p) : p.excessBlobGas.isSome ↔ 3 ≤ p.version :=
  (shape_of_anyPayload h).2.2.2

/-- A payload of version 4 decodes exactly when it has the fields of version 4 and each decodes.

Fields whose value is null count as absent.

The object without the access list and the slot must decode as a payload of version 1, 2 or 3.

The access list must decode as a byte string, and the slot as a 64-bit number. -/
theorem payloadV4_eq_ok_iff {j : Lean.Json} {p : AnyPayload} {blockAccessList : ByteArray}
    {slotNumber : UInt64} :
    payloadV4 j = .ok (p, blockAccessList, slotNumber) ↔
      ∃ fs, fields "payload" j = .ok fs ∧ hasExactly fs payloadFieldsV4 = true ∧
        anyPayload (Lean.Json.mkObj
          (fs.filter fun (name, _) => !amsterdamFields.contains name)) = .ok p ∧
        ∃ list slot, fs.lookup "blockAccessList" = some list ∧ fs.lookup "slotNumber" = some slot ∧
          bytes "blockAccessList" list = .ok blockAccessList ∧
          uint64 "slotNumber" slot = .ok slotNumber := by
  unfold payloadV4
  simp only [bind_ok_iff, liftM_eq_ok_iff]
  constructor
  · rintro ⟨fs, hfs, h⟩
    by_cases hc : hasExactly fs payloadFieldsV4 = true
    · rw [ite_eq_left hc] at h
      simp only [bind_ok_iff, liftM_eq_ok_iff, field_eq_ok_iff] at h
      obtain ⟨a, ha, l, hl, b, hb, s, hs, n, hn, hr⟩ := h
      cases hr
      exact ⟨fs, hfs, hc, ha, l, s, hl, hs, hb, hn⟩
    -- An object with other fields fails with an invalid parameter, never with a payload.
    · rw [ite_eq_right hc, bind_ok_iff] at h
      obtain ⟨_, hInvalid, -⟩ := h
      cases hInvalid
  · rintro ⟨fs, hfs, hc, ha, l, s, hl, hs, hb, hn⟩
    refine ⟨fs, hfs, ?_⟩
    rw [ite_eq_left hc]
    simp only [bind_ok_iff, liftM_eq_ok_iff, field_eq_ok_iff]
    exact ⟨p, ha, l, hl, _, hb, s, hs, _, hn, rfl⟩

/-! ## A field from a fork -/

section Since

variable {fork : Fork}

/-- A field from fork `f` decodes exactly when its presence agrees with `f ≤ fork`. -/
theorem exists_since_iff {α : Type} {f : Fork} {what : String} {o : Option α} :
    (∃ x : Since f fork α, since what o = .ok x) ↔ (o.isSome ↔ f ≤ fork) := by
  -- Each of the four cases either succeeds or fails with an invalid parameter.
  cases o <;> unfold since <;> by_cases h : f ≤ fork <;> simp [h, pure, Except.pure] <;>
    exact ⟨_, rfl⟩

/-- Reading back a decoded field from a fork gives the option it was decoded from. -/
theorem sinceValue_of_since {α : Type} {f : Fork} {what : String} {o : Option α}
    {x : Since f fork α} (h : since what o = .ok x) : sinceValue x = o := by
  -- The two cases that fail cannot give the field, and the other two give back the option.
  cases o <;> unfold since at h <;> by_cases hf : f ≤ fork <;> simp [hf, pure, Except.pure] at h
  · simp [sinceValue, hf]
  · cases h
    simp [sinceValue, hf]

/-- Decoding the value of a field from a fork gives back the field. -/
theorem since_sinceValue {α : Type} {f : Fork} {what : String} (x : Since f fork α) :
    since what (sinceValue x) = .ok x := by
  unfold sinceValue since
  by_cases hf : f ≤ fork
  · simp only [hf, dite_true, ite_true]
    exact congrArg Except.ok (Since.eq_const hf x).symm
  · simp only [hf, dite_false]
    exact congrArg Except.ok (Since.eq_of_not_le hf _ _)

/-- A field from a fork decodes from an option exactly when reading it back gives that option. -/
theorem since_eq_ok_iff {α : Type} {f : Fork} {what : String} {o : Option α}
    {x : Since f fork α} : since what o = .ok x ↔ sinceValue x = o :=
  ⟨sinceValue_of_since, fun h => h ▸ since_sinceValue x⟩

end Since

/-! ## The writers of payloads -/

/-- The fields of a payload have distinct names. -/
private theorem names_distinct {fork : Fork} (p : ExecutionPayload fork) :
    (executionPayloadFields p).Pairwise fun a b => a.1 ≠ b.1 := by
  unfold executionPayloadFields
  by_cases h1 : Fork.shapella ≤ fork <;> by_cases h2 : Fork.dencun ≤ fork <;> simp [h1, h2]

/-- No field of a payload is `null`. -/
private theorem fields_present {fork : Fork} (p : ExecutionPayload fork) :
    ∀ x ∈ executionPayloadFields p, x.2.isNull = false := by
  unfold executionPayloadFields
  by_cases h1 : Fork.shapella ≤ fork <;> by_cases h2 : Fork.dencun ≤ fork <;>
    simp [h1, h2, dataJson, quantityJson, listJson, isNull_str, isNull_arr]

/-- A computation that has succeeded passes its value on. -/
private theorem ok_bind {α β : Type} (a : α) (f : α → Decode β) :
    (Except.ok a >>= f : Decode β) = f a := rfl

/-- Mapping a function over a computation that has succeeded maps its value. -/
private theorem map_ok {α β : Type} (f : α → β) (a : α) :
    (f <$> (Except.ok a : Decode α) : Decode β) = .ok (f a) := rfl

/-- The common part of a payload: the fields that every fork has, as the payload of Paris. -/
private abbrev commonOf {fork : Fork} (p : ExecutionPayload fork) : ExecutionPayload .paris where
  parentHash := p.parentHash
  feeRecipient := p.feeRecipient
  stateRoot := p.stateRoot
  receiptsRoot := p.receiptsRoot
  logsBloom := p.logsBloom
  prevRandao := p.prevRandao
  blockNumber := p.blockNumber
  gasLimit := p.gasLimit
  gasUsed := p.gasUsed
  timestamp := p.timestamp
  extraData := p.extraData
  baseFeePerGas := p.baseFeePerGas
  blockHash := p.blockHash
  transactions := p.transactions
  withdrawals := fun h => absurd h (by decide)
  blobGasUsed := fun h => absurd h (by decide)
  excessBlobGas := fun h => absurd h (by decide)

/-- The decoder of numbers of 256 bits reads back a number of 256 bits written as a quantity. -/
private theorem quantity_baseFee (what : String) (x : BitVec 256) :
    quantity what 256 (quantityJson x.toNat) = .ok x.toNat :=
  quantity_toDigits what x.isLt

/-- The decoder of byte strings of a limit reads back a byte string that fits the limit. -/
private theorem bytesMax_dataJson (what : String) (n : Nat) (b : ByteArray) (h : b.size ≤ n) :
    bytesMax what n (dataJson b.data.toList) = .ok b :=
  bytesMax_eq_ok_iff.mpr ⟨bytes_dataJson what b, h⟩

/-- Fields that are those of a payload decode as a payload that reads back at its fork. -/
private theorem anyPayload_of_perm {fork : Fork} (p : ExecutionPayload fork)
    (extra : p.extraData.size ≤ MAX_EXTRA_DATA_BYTES) {j : Lean.Json}
    {fs : List (String × Lean.Json)}
    (hfs : fields "payload" j = .ok fs) (hp : fs.Perm (executionPayloadFields p)) :
    ∃ any, anyPayload j = .ok any ∧ any.atFork fork = .ok p := by
  have hd := names_distinct p
  have rd : ∀ k v, (k, v) ∈ executionPayloadFields p → field "payload" fs k = .ok v :=
    fun k v hm => field_of_perm hp hd hm
  have hex := hasExactly_of_perm hp
  have hlen := hp.length_eq
  -- Each of the fields of version 1 reads as the value that its JSON holds.
  have r1 := rd "parentHash" (dataJson p.parentHash.toList)
    (by simp [executionPayloadFields])
  have r2 := rd "feeRecipient" (dataJson p.feeRecipient.toList)
    (by simp [executionPayloadFields])
  have r3 := rd "stateRoot" (dataJson p.stateRoot.toList)
    (by simp [executionPayloadFields])
  have r4 := rd "receiptsRoot" (dataJson p.receiptsRoot.toList)
    (by simp [executionPayloadFields])
  have r5 := rd "logsBloom" (dataJson p.logsBloom.toList)
    (by simp [executionPayloadFields])
  have r6 := rd "prevRandao" (dataJson p.prevRandao.toList)
    (by simp [executionPayloadFields])
  have r7 := rd "blockNumber" (quantityJson p.blockNumber.toNat)
    (by simp [executionPayloadFields])
  have r8 := rd "gasLimit" (quantityJson p.gasLimit.toNat)
    (by simp [executionPayloadFields])
  have r9 := rd "gasUsed" (quantityJson p.gasUsed.toNat)
    (by simp [executionPayloadFields])
  have r10 := rd "timestamp" (quantityJson p.timestamp.toNat)
    (by simp [executionPayloadFields])
  have r11 := rd "extraData" (dataJson p.extraData.data.toList)
    (by simp [executionPayloadFields])
  have r12 := rd "baseFeePerGas" (quantityJson p.baseFeePerGas.toNat)
    (by simp [executionPayloadFields])
  have r13 := rd "blockHash" (dataJson p.blockHash.toList)
    (by simp [executionPayloadFields])
  have r14 := rd "transactions" (listJson (dataJson ·.data.toList) p.transactions)
    (by simp [executionPayloadFields])
  have hbase : BitVec.ofNat 256 p.baseFeePerGas.toNat = p.baseFeePerGas := by simp
  have key : ∃ v, anyPayload j = .ok ⟨v, commonOf p, sinceValue p.withdrawals,
      sinceValue p.blobGasUsed, sinceValue p.excessBlobGas⟩ := by
    by_cases h1 : Fork.shapella ≤ fork <;> by_cases h2 : Fork.dencun ≤ fork
    · -- Version 3.
      have hn : (executionPayloadFields p).map Prod.fst = payloadFieldsV3 := by
        simp [executionPayloadFields, h1, h2, payloadFieldsV3, payloadFieldsV2, payloadFieldsV1]
      have hl : fs.length = payloadFieldsV3.length := by rw [hlen, ← hn, List.length_map]
      rw [hn] at hex
      have ne1 : ¬ hasExactly fs payloadFieldsV1 = true := by
        simp [hasExactly, hl, payloadFieldsV3, payloadFieldsV2, payloadFieldsV1]
      have ne2 : ¬ hasExactly fs payloadFieldsV2 = true := by
        simp [hasExactly, hl, payloadFieldsV3, payloadFieldsV2, payloadFieldsV1]
      have r15 := rd "withdrawals" (listJson Execution.Rpc.withdrawalJson (p.withdrawals h1))
        (by simp [executionPayloadFields, h1, h2])
      have r16 := rd "blobGasUsed" (quantityJson (p.blobGasUsed h2).toNat)
        (by simp [executionPayloadFields, h1, h2])
      have r17 := rd "excessBlobGas" (quantityJson (p.excessBlobGas h2).toNat)
        (by simp [executionPayloadFields, h1, h2])
      refine ⟨3, ?_⟩
      unfold anyPayload
      simp only [hfs, liftM_ok, ok_bind, pure_bind]
      rw [ite_eq_right ne1, ite_eq_right ne2, ite_eq_left hex]
      simp only [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17,
        liftM_ok, ok_bind, fixed_dataJson, address_dataJson, uint64_toDigits, quantity_baseFee,
        bytesMax_dataJson _ _ _ extra, array_bytes_listJson, ge_iff_le, Nat.reduceLeDiff,
        reduceIte, map_ok, Execution.Rpc.array_withdrawal_listJson, hbase, sinceValue, h1, h2,
        dite_true]
      rfl
    · -- Version 2.
      have hn : (executionPayloadFields p).map Prod.fst = payloadFieldsV2 := by
        simp [executionPayloadFields, h1, h2, payloadFieldsV2, payloadFieldsV1]
      have hl : fs.length = payloadFieldsV2.length := by rw [hlen, ← hn, List.length_map]
      rw [hn] at hex
      have ne1 : ¬ hasExactly fs payloadFieldsV1 = true := by
        simp [hasExactly, hl, payloadFieldsV2, payloadFieldsV1]
      have r15 := rd "withdrawals" (listJson Execution.Rpc.withdrawalJson (p.withdrawals h1))
        (by simp [executionPayloadFields, h1, h2])
      refine ⟨2, ?_⟩
      unfold anyPayload
      simp only [hfs, liftM_ok, ok_bind, pure_bind]
      rw [ite_eq_right ne1, ite_eq_left hex]
      simp only [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15,
        liftM_ok, ok_bind, fixed_dataJson, address_dataJson, uint64_toDigits, quantity_baseFee,
        bytesMax_dataJson _ _ _ extra, array_bytes_listJson, ge_iff_le, Nat.reduceLeDiff,
        reduceIte, map_ok, Execution.Rpc.array_withdrawal_listJson, hbase, sinceValue, h1, h2,
        dite_true, dite_false]
      rfl
    · -- The fork has no Dencun before Shapella.
      exact absurd (Std.le_trans (by decide) h2) h1
    · -- Version 1.
      have hn : (executionPayloadFields p).map Prod.fst = payloadFieldsV1 := by
        simp [executionPayloadFields, h1, h2, payloadFieldsV1]
      rw [hn] at hex
      refine ⟨1, ?_⟩
      unfold anyPayload
      simp only [hfs, liftM_ok, ok_bind, pure_bind]
      rw [ite_eq_left hex]
      simp only [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14,
        liftM_ok, ok_bind, fixed_dataJson, address_dataJson, uint64_toDigits, quantity_baseFee,
        bytesMax_dataJson _ _ _ extra, array_bytes_listJson, ge_iff_le, Nat.reduceLeDiff,
        reduceIte, hbase, sinceValue, h1, h2, dite_false]
      rfl
  obtain ⟨v, hv⟩ := key
  refine ⟨_, hv, ?_⟩
  -- Each optional field reads back from the value that the payload gives for its fork.
  simp only [AnyPayload.atFork, since_sinceValue, ok_bind]
  rfl

/-- The decoder of payloads of versions 1 to 3 reads back the JSON of a payload, at its fork.

The extra data must hold at most 32 bytes, the bound of its type in the Engine API. -/
theorem anyPayload_executionPayloadJson {fork : Fork} (p : ExecutionPayload fork)
    (extra : p.extraData.size ≤ MAX_EXTRA_DATA_BYTES) :
    ∃ any, anyPayload (executionPayloadJson p) = .ok any ∧ any.atFork fork = .ok p := by
  obtain ⟨fs, hfs, hp⟩ := fields_mkObj "payload" (names_distinct p) (fields_present p)
  exact anyPayload_of_perm p extra hfs hp

/-- The object of a payload of version 4 from Dencun on, and that object without its two new fields.

The first holds the pairs of the payload, then the access list and the slot.

The second holds the pairs of the payload alone. -/
private theorem fields_executionPayloadV4Json {fork : Fork} (p : ExecutionPayload fork)
    (blockAccessList : ByteArray) (slotNumber : UInt64) (dencun : .dencun ≤ fork) :
    ∃ fs, fields "payload" (executionPayloadV4Json p blockAccessList slotNumber) = .ok fs ∧
      fs.Perm (executionPayloadFields p ++ [("blockAccessList",
        dataJson blockAccessList.data.toList), ("slotNumber", quantityJson slotNumber.toNat)]) ∧
      (executionPayloadFields p ++ [("blockAccessList", dataJson blockAccessList.data.toList),
        ("slotNumber", quantityJson slotNumber.toNat)]).Pairwise (fun a b => a.1 ≠ b.1) ∧
      ∃ fs', fields "payload" (Lean.Json.mkObj
          (fs.filter fun (name, _) => !amsterdamFields.contains name)) = .ok fs' ∧
        fs'.Perm (executionPayloadFields p) := by
  have h1 : Fork.shapella ≤ fork := Std.le_trans (by decide) dencun
  have hn : (executionPayloadFields p).map Prod.fst = payloadFieldsV3 := by
    simp [executionPayloadFields, h1, dencun, payloadFieldsV3, payloadFieldsV2, payloadFieldsV1]
  have hd := names_distinct p
  -- The pairs that the object holds: those of the payload, then the access list and the slot.
  have hdist : (executionPayloadFields p ++ [("blockAccessList",
      dataJson blockAccessList.data.toList), ("slotNumber", quantityJson slotNumber.toNat)]
      ).Pairwise fun a b => a.1 ≠ b.1 := by
    rw [List.pairwise_append]
    refine ⟨hd, by simp, fun a ha b hb => ?_⟩
    have ha' : a.1 ∈ payloadFieldsV3 := hn ▸ List.mem_map_of_mem ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;>
      simp [payloadFieldsV3, payloadFieldsV2, payloadFieldsV1] at ha' ⊢ <;>
      intro e <;> rw [e] at ha' <;> simp at ha'
  have hpres : ∀ x ∈ executionPayloadFields p ++ [("blockAccessList",
      dataJson blockAccessList.data.toList), ("slotNumber", quantityJson slotNumber.toNat)],
      x.2.isNull = false := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact fields_present p x hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> exact isNull_str _
  obtain ⟨fs, hfs, hp⟩ := fields_mkObj "payload" hdist hpres
  have hfsd := (hp.pairwise_iff fun hab => Ne.symm hab).mpr hdist
  -- The pairs of version 3 are those that keep their name when the two new names are dropped.
  have hflt : (executionPayloadFields p ++ [("blockAccessList",
      dataJson blockAccessList.data.toList), ("slotNumber", quantityJson slotNumber.toNat)]).filter
        (fun (name, _) => !amsterdamFields.contains name) = executionPayloadFields p := by
    rw [List.filter_append, List.filter_eq_self.mpr]
    · simp [amsterdamFields]
    · intro x hx
      have : x.1 ∈ payloadFieldsV3 := hn ▸ List.mem_map_of_mem hx
      simp only [amsterdamFields, List.contains_cons, List.contains_nil,
        Bool.or_false, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne]
      refine ⟨fun h => ?_, fun h => ?_⟩ <;> rw [h] at this <;>
        simp [payloadFieldsV3, payloadFieldsV2, payloadFieldsV1] at this
  obtain ⟨fs', hfs', hp'⟩ := fields_mkObj "payload"
    (hfsd.sublist (List.filter_sublist ..))
    (fun x hx => hpres x (hp.mem_iff.mp (List.mem_filter.mp hx).1))
  exact ⟨fs, hfs, hp, hdist, fs', hfs', hp'.trans (hflt ▸ hp.filter _)⟩

/-- The decoder of payloads of version 4 reads back the JSON of a payload from Dencun on.

It reads the payload at its fork, the block access list and the slot number.

The extra data must hold at most 32 bytes, the bound of its type in the Engine API. -/
theorem payloadV4_executionPayloadV4Json {fork : Fork} (p : ExecutionPayload fork)
    (blockAccessList : ByteArray) (slotNumber : UInt64) (dencun : .dencun ≤ fork)
    (extra : p.extraData.size ≤ MAX_EXTRA_DATA_BYTES) :
    ∃ any, payloadV4 (executionPayloadV4Json p blockAccessList slotNumber) =
      .ok (any, blockAccessList, slotNumber) ∧ any.atFork fork = .ok p := by
  have h1 : Fork.shapella ≤ fork := Std.le_trans (by decide) dencun
  have hn : (executionPayloadFields p).map Prod.fst = payloadFieldsV3 := by
    simp [executionPayloadFields, h1, dencun, payloadFieldsV3, payloadFieldsV2, payloadFieldsV1]
  obtain ⟨fs, hfs, hp, hdist, fs', hfs', hp'⟩ :=
    fields_executionPayloadV4Json p blockAccessList slotNumber dencun
  have hfsd := (hp.pairwise_iff fun hab => Ne.symm hab).mpr hdist
  have hex := hasExactly_of_perm hp
  rw [List.map_append, hn] at hex
  obtain ⟨any, hany, hat⟩ := anyPayload_of_perm p extra hfs' hp'
  refine ⟨any, payloadV4_eq_ok_iff.mpr ⟨fs, hfs, ?_, hany,
    dataJson blockAccessList.data.toList, quantityJson slotNumber.toNat, ?_, ?_, ?_, ?_⟩, hat⟩
  · simpa [payloadFieldsV4, amsterdamFields] using hex
  · exact lookup_of_mem hfsd (hp.mem_iff.mpr (by simp))
  · exact lookup_of_mem hfsd (hp.mem_iff.mpr (by simp))
  · exact bytes_dataJson _ _
  · exact uint64_toDigits _ _

/-- A decoded payload holds the extra data that its field decodes to, within 32 bytes. -/
private theorem extraData_of_anyPayload {j : Lean.Json} {any : AnyPayload}
    (h : anyPayload j = .ok any) :
    ∃ fs, fields "payload" j = .ok fs ∧ ∃ v, field "payload" fs "extraData" = .ok v ∧
      bytesMax "extraData" MAX_EXTRA_DATA_BYTES v = .ok any.common.extraData := by
  unfold anyPayload at h
  dsimp only at h
  repeat' (first
    | (simp only [invalid_eq] at h; cases h; done)
    | (obtain ⟨_, step, h⟩ := bind_ok_iff.mp h
       first | cases step | obtain ⟨_, -, rfl⟩ := map_ok_iff.mp step | skip)
    | split at h)
  -- The extra data of the result is the value that its field decoded to.
  all_goals
    cases h
    exact ⟨_, liftM_eq_ok_iff.mp ‹liftM (fields _ _) = _›, _,
      liftM_eq_ok_iff.mp ‹liftM (field _ _ "extraData") = _›,
      liftM_eq_ok_iff.mp ‹liftM (bytesMax _ _ _) = _›⟩

/-- Fields that are those of a payload decode only when its extra data holds at most 32 bytes. -/
private theorem extraData_le_of_perm {fork : Fork} (p : ExecutionPayload fork) {j : Lean.Json}
    {fs : List (String × Lean.Json)} (hfs : fields "payload" j = .ok fs)
    (hp : fs.Perm (executionPayloadFields p)) {any : AnyPayload} (h : anyPayload j = .ok any) :
    p.extraData.size ≤ MAX_EXTRA_DATA_BYTES := by
  obtain ⟨fs', hfs', v, hv, hb⟩ := extraData_of_anyPayload h
  obtain rfl := Except.ok.inj (hfs.symm.trans hfs')
  rw [field_of_perm hp (names_distinct p)
    (by simp [executionPayloadFields] :
      ("extraData", dataJson p.extraData.data.toList) ∈ executionPayloadFields p)] at hv
  obtain rfl := Except.ok.inj hv
  obtain ⟨hb, hs⟩ := bytesMax_eq_ok_iff.mp hb
  rw [bytes_dataJson] at hb
  rwa [Except.ok.inj hb]

/-- The decoder of payloads of versions 1 to 3 reads the JSON of a payload only when it fits.

Its extra data must hold at most 32 bytes. -/
theorem extraData_le_of_anyPayload_executionPayloadJson {fork : Fork} {p : ExecutionPayload fork}
    {any : AnyPayload} (h : anyPayload (executionPayloadJson p) = .ok any) :
    p.extraData.size ≤ MAX_EXTRA_DATA_BYTES := by
  obtain ⟨fs, hfs, hp⟩ := fields_mkObj "payload" (names_distinct p) (fields_present p)
  exact extraData_le_of_perm p hfs hp h

/-- The decoder of version 4 reads the JSON of a payload from Dencun on only when it fits.

Its extra data must hold at most 32 bytes. -/
theorem extraData_le_of_payloadV4_executionPayloadV4Json {fork : Fork} {p : ExecutionPayload fork}
    {blockAccessList : ByteArray} {slotNumber : UInt64} (dencun : .dencun ≤ fork)
    {x : AnyPayload × ByteArray × UInt64}
    (h : payloadV4 (executionPayloadV4Json p blockAccessList slotNumber) = .ok x) :
    p.extraData.size ≤ MAX_EXTRA_DATA_BYTES := by
  obtain ⟨any, list, slot⟩ := x
  obtain ⟨fs, hfs, -, -, fs', hfs', hp'⟩ :=
    fields_executionPayloadV4Json p blockAccessList slotNumber dencun
  obtain ⟨fs₀, hfs₀, -, hany, -⟩ := payloadV4_eq_ok_iff.mp h
  obtain rfl := Except.ok.inj (hfs.symm.trans hfs₀)
  exact extraData_le_of_perm p hfs' hp' hany

/-- The name of every status reads back as that status. -/
theorem statusOfName_name (s : Status) : statusOfName s.name = some s := by
  cases s <;> rfl

/-- The decoder of a payload status reads back the JSON of every status and validation error. -/
theorem payloadStatusOfJson_json (s : PayloadStatus) (e : Option String) :
    payloadStatusOfJson (payloadStatusJson s e) = .ok (s, e) := by
  have hd : [("status", Lean.Json.str s.status.name),
      ("latestValidHash", optionJson (dataJson ·.toList) s.latestValidHash),
      ("validationError", optionJson .str e)].Pairwise fun a b => a.1 ≠ b.1 := by simp
  obtain ⟨fs, hfs, hp⟩ := fields_mkObj_filter "payloadStatus" hd
  have look := lookup_of_perm_filter hp hd
  have k1 : ∀ a b c : Lean.Json,
      [("status", a), ("latestValidHash", b), ("validationError", c)].lookup "status" = some a :=
    fun _ _ _ => rfl
  have k2 : ∀ a b c : Lean.Json,
      [("status", a), ("latestValidHash", b), ("validationError", c)].lookup "latestValidHash" =
        some b := fun _ _ _ => rfl
  have k3 : ∀ a b c : Lean.Json,
      [("status", a), ("latestValidHash", b), ("validationError", c)].lookup "validationError" =
        some c := fun _ _ _ => rfl
  have l1 : fs.lookup "status" = some (.str s.status.name) := by
    rw [look, k1]; rfl
  have l2 : fs.lookup "latestValidHash" = s.latestValidHash.map (dataJson ·.toList) := by
    rw [look, k2]; cases s.latestValidHash <;> rfl
  have l3 : fs.lookup "validationError" = e.map .str := by
    rw [look, k3]; cases e <;> rfl
  have hall : (fs.all (payloadStatusFields.contains ·.1)) = true := by
    rw [List.all_eq_true]
    intro p hm
    obtain ⟨hm, -⟩ := List.mem_filter.mp (hp.mem_iff.mp hm)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp [payloadStatusFields]
  unfold payloadStatusOfJson payloadStatusJson
  have hf : field "payloadStatus" fs "status" = .ok (.str s.status.name) := by
    simp [field, l1]; rfl
  have hs : string "status" (.str s.status.name) = .ok s.status.name := rfl
  simp only [hfs, liftM_ok, ok_bind, hall, ite_true, hf, l2, l3, hs, statusOfName_name]
  obtain ⟨st, lvh⟩ := s
  cases lvh <;> cases e <;> simp [lift, fixed_dataJson, string, Option.mapM]
  all_goals rfl

/-- A name reads as a status exactly when it is the name that the Engine API writes for it. -/
theorem statusOfName_eq_some_iff {name : String} {s : Status} :
    statusOfName name = some s ↔ name = s.name := by
  constructor
  · intro h
    unfold statusOfName at h
    have found := List.find?_some h
    exact (beq_iff_eq.mp found).symm
  · rintro rfl
    exact statusOfName_name s

/-- An optional byte string of a fixed size decodes exactly from the encoding of its bytes.

That encoding is `0x` and two lowercase hex digits per byte.

An absent value decodes as absent. -/
theorem lift_mapM_fixed_eq_ok_iff {what : String} {n : Nat} {o : Option Lean.Json}
    {r : Option (Vector UInt8 n)} :
    lift (o.mapM (fixed what n)) = .ok r ↔ o = r.map fun v => .str (hexString v.toList) := by
  cases o with
  | none => cases r <;> simp [lift, Option.mapM, Except.mapError, pure, Except.pure]
  | some x =>
    have e : lift (Option.mapM (fixed what n) (some x)) =
        (some <$> fixed what n x : Read _).mapError .invalidParams := rfl
    rw [e]
    cases h : fixed what n x <;> cases r <;>
      simp [Functor.map, Except.map, Except.mapError, ← fixed_false_eq_ok_iff (what := what), h]

/-- An optional string decodes exactly from its JSON string, and an absent value as absent. -/
theorem lift_mapM_string_eq_ok_iff {what : String} {o : Option Lean.Json}
    {r : Option String} :
    lift (o.mapM (string what)) = .ok r ↔ o = r.map .str := by
  cases o with
  | none => cases r <;> simp [lift, Option.mapM, Except.mapError, pure, Except.pure]
  | some x =>
    have e : lift (Option.mapM (string what) (some x)) =
        (some <$> string what x : Read _).mapError .invalidParams := rfl
    rw [e]
    cases h : string what x <;> cases r <;>
      simp [Functor.map, Except.map, Except.mapError, ← string_eq_ok_iff (what := what), h]

/-- A JSON value reads as a payload status exactly when it is an object of the form below.

A member whose value is `null` counts as absent.

Its other members are `status`, `latestValidHash` and `validationError` alone.

The value of `status` is the name of the status.

The latest valid hash is `0x` and 64 lowercase hex digits, or absent.

The validation error is a string, or absent. -/
theorem payloadStatusOfJson_eq_ok_iff {j : Lean.Json} {s : PayloadStatus} {e : Option String} :
    payloadStatusOfJson j = .ok (s, e) ↔
      ∃ fs, fields "payloadStatus" j = .ok fs ∧
        (∀ f ∈ fs, f.1 = "status" ∨ f.1 = "latestValidHash" ∨ f.1 = "validationError") ∧
        fs.lookup "status" = some (.str s.status.name) ∧
        fs.lookup "latestValidHash" = s.latestValidHash.map (fun h => .str (hexString h.toList)) ∧
        fs.lookup "validationError" = e.map .str := by
  obtain ⟨st, lvh⟩ := s
  unfold payloadStatusOfJson
  simp only [bind_ok_iff, liftM_eq_ok_iff]
  refine exists_congr fun fs => and_congr_right fun _ => ?_
  have allIff : fs.all (payloadStatusFields.contains ·.1) = true ↔
      ∀ f ∈ fs, f.1 = "status" ∨ f.1 = "latestValidHash" ∨ f.1 = "validationError" := by
    simp [List.all_eq_true, payloadStatusFields]
  by_cases hall : fs.all (payloadStatusFields.contains ·.1) = true
  · rw [and_iff_right (allIff.mp hall)]
    simp only [hall, ite_true, bind_ok_iff, liftM_eq_ok_iff, field_eq_ok_iff, string_eq_ok_iff]
    constructor
    · rintro ⟨_, hs, name, rfl, h⟩
      cases hn : statusOfName name with
      | none =>
        rw [hn] at h
        cases h
      | some st' =>
        rw [hn] at h
        simp only [bind_ok_iff, lift_mapM_fixed_eq_ok_iff, lift_mapM_string_eq_ok_iff] at h
        obtain ⟨l, hl, v, hv, h⟩ := h
        cases h
        obtain rfl := statusOfName_eq_some_iff.mp hn
        exact ⟨hs, hl, hv⟩
    · rintro ⟨hs, hl, he⟩
      refine ⟨_, hs, st.name, rfl, ?_⟩
      rw [statusOfName_name]
      simp only [bind_ok_iff, lift_mapM_fixed_eq_ok_iff, lift_mapM_string_eq_ok_iff]
      exact ⟨lvh, hl, e, he, rfl⟩
  -- A member of another name fails with an invalid parameter, never with a status.
  · constructor
    · intro h
      simp only [bind, Except.bind] at h
      split at h
      · contradiction
      · cases h
    · rintro ⟨members, -⟩
      exact absurd (allIff.mpr members) hall

end EthLib.Engine.Json

namespace EthLib.Engine

/-- A request passes the size check exactly when it asks for at most as many items as allowed. -/
theorem checkRequestSize_eq_ok_iff (maxRequest count : Nat) :
    checkRequestSize maxRequest count = .ok () ↔ count ≤ maxRequest := by
  unfold checkRequestSize
  by_cases h : maxRequest < count
  · simp [h, throw, throwThe, MonadExceptOf.throw]
  · simp [h, pure, Except.pure]; omega

/-- A request is too large exactly when it asks for more items than the node takes. -/
theorem checkRequestSize_eq_error_iff (maxRequest count : Nat) (e : EngineError) :
    checkRequestSize maxRequest count = .error e ↔ maxRequest < count ∧ e = .tooLargeRequest := by
  unfold checkRequestSize
  by_cases h : maxRequest < count
  · simp [h, throw, throwThe, MonadExceptOf.throw, eq_comm]
  · simp [h, pure, Except.pure]

end EthLib.Engine
