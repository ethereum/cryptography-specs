module

public import EthLib.Serialization.Der
public import EthLib.Base.Except
public import EthLib.Base.Proofs.BigEndian

/-!
# DER reader checks

A successful typed read has the requested tag and a complete read consumes its input.

The reader is stated against X.690 itself, in terms of octets and numbers.

- A read is exactly a low-number tag octet other than 0, the shortest length, the content, the rest.
- So a tag and a content have a single encoding.
- An INTEGER reads as `i` exactly when its content is `i` in two's complement on the fewest octets.
- So an integer has a single content.
- A nonnegative one is its big-endian octets, at least one, after a zero if the top bit is set.
- A BOOLEAN is one octet, FF for TRUE and 00 for FALSE.
- The BIT STRING reader accepts only an octet-aligned value: the octet 0, then its octets.
- BIT STRING contents count at most 7 unused bits, all zero, and none when no octet follows.
- BMPString and UniversalString pass when they write Unicode scalar values, two or four octets each.
- An OBJECT IDENTIFIER is one or more subidentifiers, each on the fewest base-128 octets.
- A SEQUENCE passes validation when each value it holds passes, and a SET OF also needs them sorted.
-/

@[expose] public section

namespace EthLib.Serialization.Proofs.Der

open EthLib.Serialization.Der
open EthLib.Base

/-- A typed read succeeds only with the requested tag and the underlying reader's result. -/
theorem readTag_ok_iff {tag : UInt8} {input rest : ByteArray} {value : Value} :
    readTag tag input = .ok (value, rest) ↔
      read input = .ok (value, rest) ∧ value.tag = tag := by
  simp only [readTag, bind_ok_iff]
  constructor
  · rintro ⟨⟨v, r⟩, parsed, checked⟩
    split at checked
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at checked
      obtain ⟨rfl, rfl⟩ := checked
      exact ⟨parsed, ‹v.tag = tag›⟩
    · simp at checked
  · rintro ⟨parsed, same⟩
    exact ⟨(value, rest), parsed, by simp [same, pure, Except.pure]⟩

/-- An exact read succeeds only when no trailing bytes remain. -/
theorem exact_ok_iff {tag : UInt8} {input : ByteArray} {value : Value} :
    exact tag input = .ok value ↔
      ∃ rest, readTag tag input = .ok (value, rest) ∧ rest.isEmpty = true := by
  simp only [exact, bind_ok_iff]
  constructor
  · rintro ⟨⟨v, r⟩, parsed, checked⟩
    split at checked
    · simp only [pure, Except.pure, Except.ok.injEq] at checked
      subst v
      exact ⟨r, parsed, ‹r.isEmpty = true›⟩
    · simp at checked
  · rintro ⟨rest, parsed, empty⟩
    exact ⟨(value, rest), parsed, by simp [empty, pure, Except.pure]⟩

/-- An INTEGER whose zero sign byte is redundant is rejected for every remaining byte. -/
theorem integer_redundant_zero (next : UInt8) (rest : List UInt8)
    (small : next.toNat < 128) (encoded : ByteArray) :
    integer ⟨2, ⟨(0 :: next :: rest).toArray⟩, encoded⟩ = .error .value := by
  simp [integer, small, throw, throwThe, MonadExceptOf.throw,
    Functor.map, Except.map]

/-! ## The length octets -/

/-- A list of bytes in a byte array is the array. -/
private theorem byteArray_eq_of_toList {a b : ByteArray} (h : a.data.toList = b.data.toList) :
    a = b := ByteArray.ext (Array.toList_inj.mp h)

/-- The bytes of a slice are the bytes after its start, up to its end. -/
private theorem toList_extract (b : ByteArray) (x y : Nat) :
    (b.extract x y).data.toList = (b.data.toList.drop x).take (y - x) := by
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]

/-- A read gives `value` and `rest` exactly when the input is the encoding of `value`, then `rest`.

The identifier is one octet whose five low bits are not all set (X.690 §8.1.2).

It is not zero, the identifier of the end-of-contents octets (X.690 §8.1.5).

The length is definite and on the fewest octets (X.690 §§8.1.3, 10.1).

A content of fewer than 128 octets has its length in one octet.

A longer content has an octet `129 + k`, then its length on `k + 1` big-endian octets.

Its length lies in `[256 ^ k, 256 ^ (k + 1))`, so the first of those octets is not zero.

`k` is below 126, because the initial octet 255 is reserved. -/
theorem read_ok_iff {input rest : ByteArray} {value : Value} :
    read input = .ok (value, rest) ↔
      value.tag.toNat % 32 ≠ 31 ∧ value.tag ≠ 0 ∧
      input.data.toList = value.encoded.data.toList ++ rest.data.toList ∧
      ((value.content.size < 128 ∧ value.encoded.data.toList =
          value.tag :: UInt8.ofNat value.content.size :: value.content.data.toList) ∨
        ∃ k, 256 ^ k ≤ value.content.size ∧ value.content.size < 256 ^ (k + 1) ∧ k < 126 ∧
          128 ≤ value.content.size ∧ value.encoded.data.toList =
            value.tag :: UInt8.ofNat (129 + k) ::
              (natToBytes (k + 1) value.content.size ++ value.content.data.toList)) := by
  constructor
  · intro h
    have hsz : input.size = input.data.toList.length := by rw [Array.length_toList]; rfl
    unfold EthLib.Serialization.Der.read at h
    generalize hL : input.data.toList = L at h hsz
    rcases L with _ | ⟨tag, _ | ⟨first, more⟩⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    simp only at h
    by_cases ht : tag.toNat % 32 = 31 ∨ tag = 0
    · simp [ht, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    have hsize : ∀ x y, (input.extract x y).size = min y input.size - x := fun x y =>
      ByteArray.size_extract
    -- The short form gives the length in the second octet, the long form in the octets after it.
    by_cases hs : first.toNat < 128
    · simp [ht, hs, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure,
        Except.pure] at h
      split at h
      · cases h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [List.length_cons] at hsz
      simp only [toList_extract, hL, hsize, hsz]
      have hm : min (2 + first.toNat) (more.length + 1 + 1) - 2 = first.toNat := by omega
      have e : 2 + first.toNat = first.toNat + 1 + 1 := by omega
      rw [hm, e]
      simp only [Nat.sub_zero, List.drop_zero, List.take_succ_cons, List.drop_succ_cons,
        UInt8.ofNat_toNat]
      refine ⟨by omega, fun h => ht (.inr h), ?_, .inl ⟨hs, rfl⟩⟩
      rw [List.take_of_length_le (l := List.drop first.toNat more)
        (by simp only [List.length_drop]; omega)]
      simp
    · simp [ht, hs, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure,
        Except.pure] at h
      have hf : first.toNat < 256 := first.toNat_lt
      split at h
      · cases h
      split at h
      · cases h
      rename_i hc hmore
      rcases htake : List.take (first.toNat - 128) more with _ | ⟨head, tail⟩
      · simp only [htake] at h
        cases h
      simp only [htake] at h
      split at h
      · cases h
      rename_i hhead
      split at h
      · cases h
      rename_i hn
      split at h
      · cases h
      rename_i hin
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [List.length_cons] at hsz
      simp only [toList_extract, hL, hsize, hsz]
      -- The length octets: `c` bytes, the first nonzero, worth `n`.
      have hlen : (head :: tail).length = first.toNat - 128 := by
        rw [← htake, List.length_take]; omega
      have hlo := bytesToNat_cons head tail
      have hhi := bytesToNat_lt (head :: tail)
      have hh : 1 ≤ head.toNat := by
        have : head.toNat ≠ 0 := fun h => hhead (UInt8.toNat_inj.mp h)
        omega
      have hpow : 256 ^ tail.length ≤ head.toNat * 256 ^ tail.length :=
        Nat.le_mul_of_pos_left _ hh
      generalize hnb : bytesToNat (head :: tail) = n at *
      obtain ⟨k, hk⟩ : ∃ k, first.toNat - 128 = k + 1 := ⟨first.toNat - 129, by omega⟩
      rw [hk] at hlen htake hin ⊢
      have hm : min (2 + (k + 1) + n) (more.length + 1 + 1) - (2 + (k + 1)) = n := by omega
      have e3 : 2 + (k + 1) + n - (2 + (k + 1)) = n := by omega
      have e : 2 + (k + 1) + n = (k + 1 + n) + 1 + 1 := by omega
      have e2 : 2 + (k + 1) = (k + 1) + 1 + 1 := by omega
      rw [hm, e3, e, e2]
      simp only [Nat.sub_zero, List.drop_zero, List.take_succ_cons, List.drop_succ_cons]
      have htl : tail.length = k := by simp at hlen; omega
      have hfirst : UInt8.ofNat (129 + k) = first := by
        apply UInt8.toNat_inj.mp
        simp only [UInt8.toNat_ofNat']
        omega
      have hbytes : natToBytes (k + 1) n = List.take (k + 1) more := by
        rw [htake, ← hnb, ← hlen, natToBytes_bytesToNat]
      refine ⟨fun h => ht (.inl h), fun h => ht (.inr h), ?_,
        .inr ⟨k, ?_, ?_, ?_, by omega, ?_⟩⟩
      · rw [List.take_of_length_le (l := List.drop (k + 1 + n) more) (by
          simp only [List.length_drop]; omega)]
        simp
      · rw [← htl]; omega
      · simpa [hlen] using hhi
      · omega
      · rw [hfirst, hbytes, List.take_add]
  · rintro ⟨ht1, ht0, hin, hcases⟩
    obtain ⟨tag, content, encoded⟩ := value
    simp only at *
    have hsz : input.size = input.data.toList.length := by rw [Array.length_toList]; rfl
    have hcs : content.size = content.data.toList.length := by rw [Array.length_toList]; rfl
    generalize hC : content.data.toList = C at *
    generalize hR : rest.data.toList = R at *
    have hext : ∀ x y,
        (input.extract x y).data.toList = (input.data.toList.drop x).take (y - x) :=
      fun x y => toList_extract input x y
    -- Run the reader on the encoding, in the short form and then in the long form.
    rcases hcases with ⟨hs, he⟩ | ⟨k, hlo, hhi, hk, h128, he⟩
    · rw [he] at hin
      have hfirst : (UInt8.ofNat content.size).toNat = content.size := by
        simp only [UInt8.toNat_ofNat']; omega
      unfold EthLib.Serialization.Der.read
      rw [hin]
      simp only [List.cons_append]
      simp [ht1, ht0, hfirst, hs, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure,
        Except.pure]
      have hnot : ¬ input.size < 2 + content.size := by rw [hsz, hin]; simp; omega
      have e : 2 + C.length = C.length + 1 + 1 := by omega
      simp only [hnot, ite_false, Except.ok.injEq, Prod.mk.injEq, Value.mk.injEq, true_and]
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> apply byteArray_eq_of_toList <;>
        simp [hin, hC, hR, he, hcs, hsz, e]
    · rw [he] at hin
      have hfirst : (UInt8.ofNat (129 + k)).toNat = 129 + k := by
        simp only [UInt8.toNat_ofNat']; omega
      -- The length octets: the first is the quotient by `256 ^ k`, which is not zero.
      have hpos : 0 < 256 ^ k := Nat.pow_pos (by decide)
      have hq1 : 1 ≤ content.size / 256 ^ k := (Nat.le_div_iff_mul_le hpos).mpr (by omega)
      have hq2 : content.size / 256 ^ k < 256 :=
        (Nat.div_lt_iff_lt_mul hpos).mpr (by rw [Nat.pow_succ] at hhi; omega)
      have hsplit : natToBytes (k + 1) content.size =
          UInt8.ofNat (content.size / 256 ^ k) :: natToBytes k content.size := by
        rw [Nat.add_comm, natToBytes_add, natToBytes_succ, natToBytes_zero, List.nil_append,
          Nat.mod_eq_of_lt hq2]
        rfl
      have hhead : UInt8.ofNat (content.size / 256 ^ k) ≠ 0 := by
        intro h
        have := congrArg UInt8.toNat h
        simp only [UInt8.toNat_ofNat'] at this
        simp at this
        omega
      have hval : bytesToNat (natToBytes (k + 1) content.size) = content.size :=
        bytesToNat_natToBytes_of_lt hhi
      rw [hsplit] at hin he hval
      have hnot : ¬ input.size < 2 + (k + 1) + content.size := by
        rw [hsz, hin]
        simp [natToBytes_length, ← hcs]
        omega
      unfold EthLib.Serialization.Der.read
      rw [hin]
      simp only [List.cons_append]
      simp [ht1, ht0, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure,
        Except.pure]
      have htk : List.take (k + 1) (UInt8.ofNat (content.size / 256 ^ k) ::
          (natToBytes k content.size ++ (C ++ R))) =
          UInt8.ofNat (content.size / 256 ^ k) :: natToBytes k content.size := by
        rw [List.take_succ_cons, List.take_left' (natToBytes_length k _)]
      simp only [show (129 + k) % 256 = 129 + k by omega, show 129 + k - 128 = k + 1 by omega,
        htk, hhead, hval, hnot]
      have a3 : ¬ (natToBytes k content.size).length + (C.length + R.length) + 1 < k + 1 := by
        rw [natToBytes_length]; omega
      simp only [show ¬ 129 + k < 128 by omega, show ¬ (k + 1 = 0 ∨ k + 1 = 127) by omega, a3,
        show ¬ content.size < 128 by omega, ite_false]
      simp only [Except.ok.injEq, Prod.mk.injEq, Value.mk.injEq, true_and]
      have e : 2 + (k + 1) = k + 1 + 1 + 1 := by omega
      rw [e]
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> apply byteArray_eq_of_toList <;> rw [hext, hin]
      · simp [hC, hcs, List.drop_left' (natToBytes_length k _)]
      · have e2 : k + 1 + 1 + 1 + content.size = k + content.size + 1 + 1 + 1 := by omega
        have hl : (natToBytes k content.size ++ C).length = k + content.size := by
          simp [natToBytes_length, hcs]
        simp only [Nat.sub_zero, List.drop_zero, he, e2, List.take_succ_cons, List.cons_append,
          ← hl, List.take_left']
      · have e2 : k + 1 + 1 + 1 + content.size = k + content.size + 1 + 1 + 1 := by omega
        have hl : (natToBytes k content.size ++ C).length = k + content.size := by
          simp [natToBytes_length, hcs]
        rw [hR, hsz, hin, e2]
        simp only [List.drop_succ_cons, List.cons_append, ← hl,
          List.drop_left']
        exact List.take_of_length_le (by simp; omega)

/-- Two reads of one tag and one content have one encoding, so each value has a single header. -/
theorem encoded_eq_of_read_ok {a b rest rest' : ByteArray} {v w : Value}
    (ha : read a = .ok (v, rest)) (hb : read b = .ok (w, rest')) (tag : v.tag = w.tag)
    (content : v.content = w.content) : v.encoded = w.encoded := by
  obtain ⟨-, -, -, hv⟩ := read_ok_iff.mp ha
  obtain ⟨-, -, -, hw⟩ := read_ok_iff.mp hb
  rw [tag, content] at hv
  apply byteArray_eq_of_toList
  rcases hv with ⟨hs, hv⟩ | ⟨k, lo, hi, -, h128, hv⟩ <;>
    rcases hw with ⟨hs', hw⟩ | ⟨l, lo', hi', -, h128', hw⟩
  · rw [hv, hw]
  · omega
  · omega
  · -- The length lies in `[256 ^ k, 256 ^ (k + 1))` for one `k` only.
    have hkl : k = l := by
      rcases Nat.lt_trichotomy k l with h | h | h
      · have := Nat.pow_le_pow_right (show 0 < 256 by decide) h
        omega
      · exact h
      · have := Nat.pow_le_pow_right (show 0 < 256 by decide) h
        omega
    rw [hv, hw, hkl]

/-! ## INTEGER -/

/-- A power of 256 in the integers is the cast of the natural power. -/
private theorem natCast_pow_256 (n : Nat) : (256 : Int) ^ n = ((256 ^ n : Nat) : Int) := by
  rw [Int.natCast_pow]; rfl

/-- Modulo `M`, an integer in `[-M/2, M/2)` is itself, or `M` above itself if negative. -/
private theorem emod_cases {i M : Int} (lo : -M ≤ 2 * i) (hi : 2 * i < M) :
    (0 ≤ i ∧ i % M = i) ∨ (i < 0 ∧ i % M = i + M) := by
  by_cases h : 0 ≤ i
  · exact .inl ⟨h, Int.emod_eq_of_lt h (by omega)⟩
  · refine .inr ⟨by omega, ?_⟩
    rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]

/-- Bytes with no redundant sign octet read as `i` exactly when they hold `i` on the fewest octets.
-/
private theorem twos_complement_iff (first : UInt8) (rest : List UInt8) (i : Int) :
    ((∀ next tail, rest = next :: tail →
        ¬ ((first = 0 ∧ next.toNat < 128) ∨ (first = 255 ∧ 128 ≤ next.toNat))) ∧
      i = if first.toNat < 128 then (bytesToNat (first :: rest) : Int)
        else bytesToNat (first :: rest) - 256 ^ (rest.length + 1)) ↔
    ∃ k : Nat, -(128 * 256 ^ k : Int) ≤ i ∧ i < 128 * 256 ^ k ∧
      (∀ j < k, i < -(128 * 256 ^ j : Int) ∨ 128 * 256 ^ j ≤ i) ∧
      first :: rest = natToBytes (k + 1) (i % 256 ^ (k + 1)).toNat := by
  have hN := bytesToNat_cons first rest
  have hR := bytesToNat_lt rest
  have hf : first.toNat < 256 := first.toNat_lt
  have mulQ : ∀ a b, a ≤ b → a * 256 ^ rest.length ≤ b * 256 ^ rest.length :=
    fun a b h => Nat.mul_le_mul_right _ h
  -- The second byte, when there is one, is worth `256 ^ (k - 1)` per unit.
  have hsecond : ∀ next tail, rest = next :: tail →
      bytesToNat rest = next.toNat * 256 ^ tail.length + bytesToNat tail ∧
      bytesToNat tail < 256 ^ tail.length ∧ 256 ^ rest.length = 256 * 256 ^ tail.length ∧
      (∀ a b, a ≤ b → a * 256 ^ tail.length ≤ b * 256 ^ tail.length) := by
    rintro next tail rfl
    exact ⟨bytesToNat_cons next tail, bytesToNat_lt tail, by
      rw [List.length_cons, Nat.pow_succ, Nat.mul_comm], fun a b h => Nat.mul_le_mul_right _ h⟩
  have hsmall : ∀ j < rest.length, ∀ tail : List UInt8, rest.length = tail.length + 1 →
      256 ^ j ≤ 256 ^ tail.length := fun j hj tail ht =>
    Nat.pow_le_pow_right (by decide) (by omega)
  simp only [natCast_pow_256, Nat.pow_succ]
  constructor
  · rintro ⟨nr, hi⟩
    refine ⟨rest.length, ?_⟩
    have hrange : -(128 * ((256 ^ rest.length : Nat) : Int)) ≤ i ∧
        i < 128 * ((256 ^ rest.length : Nat) : Int) := by
      split at hi
      · have := mulQ first.toNat 127 (by omega)
        omega
      · have := mulQ 128 first.toNat (by omega)
        have := mulQ first.toNat 255 (by omega)
        omega
    have hmod : (i % ((256 ^ rest.length * 256 : Nat) : Int)).toNat =
        bytesToNat (first :: rest) := by
      have := mulQ first.toNat 255 (by omega)
      rcases emod_cases (i := i) (M := ((256 ^ rest.length * 256 : Nat) : Int))
        (by omega) (by omega) with ⟨h0, h⟩ | ⟨h0, h⟩ <;> rw [h] <;> split at hi <;> omega
    refine ⟨hrange.1, hrange.2, ?_, ?_⟩
    · intro j hj
      rcases rest with _ | ⟨next, tail⟩
      · simp at hj
      · obtain ⟨hr, ht, hq, mulP⟩ := hsecond next tail rfl
        have hjP := hsmall j hj tail rfl
        have hnr := nr next tail rfl
        suffices i < -(128 * ((256 ^ tail.length : Nat) : Int)) ∨
            128 * ((256 ^ tail.length : Nat) : Int) ≤ i by omega
        split at hi
        · by_cases h0 : first = 0
          · subst h0
            have : 128 ≤ next.toNat := by simp at hnr; omega
            have := mulP 128 next.toNat this
            omega
          · have : first.toNat ≠ 0 := fun h => h0 (UInt8.toNat_inj.mp h)
            have := mulQ 1 first.toNat (by omega)
            omega
        · by_cases h255 : first = 255
          · subst h255
            have : next.toNat < 128 := by simp at hnr; omega
            have := mulP next.toNat 127 (by omega)
            have := mulQ 255 255 (by omega)
            simp at hN
            omega
          · have : first.toNat ≠ 255 := fun h => h255 (UInt8.toNat_inj.mp h)
            have := mulQ first.toNat 254 (by omega)
            omega
    · rw [hmod]
      exact (natToBytes_bytesToNat (first :: rest)).symm
  · rintro ⟨k, lo, hi, hmin, hc⟩
    have hk : k = rest.length := by
      have := congrArg List.length hc
      rw [natToBytes_length, List.length_cons] at this
      omega
    subst hk
    -- The bytes hold `i` modulo `256 ^ (k + 1)`, which is `i` or `i + 256 ^ (k + 1)`.
    have hval :
        bytesToNat (first :: rest) = (i % ((256 ^ rest.length * 256 : Nat) : Int)).toNat := by
      rw [hc, bytesToNat_natToBytes_of_lt]
      rcases emod_cases (i := i) (M := ((256 ^ rest.length * 256 : Nat) : Int))
        (by omega) (by omega) with ⟨h0, h⟩ | ⟨h0, h⟩ <;> rw [h, Nat.pow_succ] <;> omega
    have hcase := emod_cases (i := i) (M := ((256 ^ rest.length * 256 : Nat) : Int))
      (by omega) (by omega)
    refine ⟨?_, ?_⟩
    · rintro next tail rfl hred
      obtain ⟨hr, ht, hq, mulP⟩ := hsecond next tail rfl
      have := hmin tail.length (by simp)
      rcases hred with ⟨rfl, hn⟩ | ⟨rfl, hn⟩
      · have := mulP next.toNat 127 (by omega)
        simp at hN
        rcases hcase with ⟨h0, h⟩ | ⟨h0, h⟩ <;> rw [h] at hval <;> omega
      · have := mulP 128 next.toNat hn
        simp at hN
        rcases hcase with ⟨h0, h⟩ | ⟨h0, h⟩ <;> rw [h] at hval <;> omega
    · split
      · have := mulQ first.toNat 127 (by omega)
        rcases hcase with ⟨h0, h⟩ | ⟨h0, h⟩ <;> rw [h] at hval <;> omega
      · have := mulQ 128 first.toNat (by omega)
        rcases hcase with ⟨h0, h⟩ | ⟨h0, h⟩ <;> rw [h] at hval <;> omega

/-- An INTEGER reads as `i` exactly when its tag is 2 and its content is `i` on the fewest octets.

The octets are two's complement (X.690 §8.3.3).

The content is `i` modulo `256 ^ (k + 1)` on `k + 1` big-endian octets.

`i` lies in `[-(128 * 256 ^ k), 128 * 256 ^ k)`, the range of `k + 1` octets.

No shorter content holds `i`, so a first octet 0 or 255 is never redundant (X.690 §8.3.2). -/
theorem integer_ok_iff {value : Value} {i : Int} :
    integer value = .ok i ↔ value.tag = 2 ∧ ∃ k : Nat,
      -(128 * 256 ^ k : Int) ≤ i ∧ i < 128 * 256 ^ k ∧
      (∀ j < k, i < -(128 * 256 ^ j : Int) ∨ 128 * 256 ^ j ≤ i) ∧
      value.content.data.toList = natToBytes (k + 1) (i % 256 ^ (k + 1)).toNat := by
  unfold integer
  generalize hc : value.content.data.toList = c
  have hsize : value.content.size = c.length := by
    rw [← hc, Array.length_toList]
    rfl
  rw [hsize]
  by_cases ht : value.tag = 2
  · simp only [ht, bne_self_eq_false, Bool.false_eq_true, ite_false, true_and]
    rcases c with _ | ⟨first, rest⟩
    · simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq, false_iff, not_exists,
        not_and]
      intro k _ _ _ h
      have := congrArg List.length h
      simp [natToBytes_length] at this
    rw [← twos_complement_iff]
    rcases rest with _ | ⟨next, tail⟩
    · simp [pure, Except.pure, eq_comm]
    · by_cases hr : (first = 0 ∧ next.toNat < 128) ∨ (first = 255 ∧ 128 ≤ next.toNat)
      · simp only [hr, ite_true, throw, throwThe, MonadExceptOf.throw, bind, Except.bind,
          reduceCtorEq, false_iff, not_and]
        intro h
        exact absurd hr (h next tail rfl)
      · have hnr : ∀ n t, next :: tail = n :: t →
            ¬ ((first = 0 ∧ n.toNat < 128) ∨ (first = 255 ∧ 128 ≤ n.toNat)) := by
          intro n t h
          cases h
          exact hr
        rw [and_iff_right hnr]
        simp [hr, pure, Except.pure, eq_comm]
  · simp [ht, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- Two INTEGERs that read as one value have one content. -/
theorem content_eq_of_integer_ok {v w : Value} {i : Int} (hv : integer v = .ok i)
    (hw : integer w = .ok i) : v.content = w.content := by
  obtain ⟨-, k, lo, hi, hmin, hc⟩ := integer_ok_iff.mp hv
  obtain ⟨-, l, lo', hi', hmin', hc'⟩ := integer_ok_iff.mp hw
  -- The fewest octets that hold `i` are one count, so both contents have it.
  have hkl : k = l := by
    rcases Nat.lt_trichotomy k l with h | h | h
    · rcases hmin' k h with h' | h' <;> omega
    · exact h
    · rcases hmin l h with h' | h' <;> omega
  subst hkl
  exact byteArray_eq_of_toList (hc.trans hc'.symm)

/-- A nonnegative INTEGER reads as `n` exactly when its tag is 2 and its content is `n` big-endian.

The content has the fewest octets that leave the top bit of the first clear (X.690 §§8.3.2, 8.3.3).

The content has `k + 1` octets, and `n` is below `128 * 256 ^ k`.

No shorter content holds `n`. -/
theorem natural_ok_iff {value : Value} {n : Nat} :
    natural value = .ok n ↔ value.tag = 2 ∧ ∃ k : Nat, n < 128 * 256 ^ k ∧
      (∀ j < k, 128 * 256 ^ j ≤ n) ∧ value.content.data.toList = natToBytes (k + 1) n := by
  have hnat : natural value = .ok n ↔ integer value = .ok (n : Int) := by
    unfold natural
    cases h : integer value with
    | error e => simp [bind, Except.bind]
    | ok i =>
      by_cases hi : i < 0
      · simp only [bind, Except.bind, hi, ite_true, throw, throwThe, MonadExceptOf.throw,
          reduceCtorEq, false_iff, Except.ok.injEq]
        omega
      · simp only [bind, Except.bind, hi, ite_false, pure, Except.pure, Except.ok.injEq]
        omega
  rw [hnat, integer_ok_iff]
  simp only [natCast_pow_256]
  refine and_congr_right fun _ => exists_congr fun k => ?_
  -- A nonnegative value below `256 ^ (k + 1)` is its own residue.
  have hpow : 0 < 256 ^ k := Nat.pow_pos (by decide)
  constructor
  · rintro ⟨-, hi, hmin, hc⟩
    refine ⟨by omega, fun j hj => ?_, ?_⟩
    · have := hmin j hj
      omega
    · rw [hc, Int.emod_eq_of_lt (by omega) (by rw [Nat.pow_succ]; omega)]
      rfl
  · rintro ⟨hi, hmin, hc⟩
    refine ⟨by omega, by omega, fun j hj => .inr (by have := hmin j hj; omega), ?_⟩
    rw [hc, Int.emod_eq_of_lt (by omega) (by rw [Nat.pow_succ]; omega)]
    rfl

/-! ## BOOLEAN and BIT STRING -/

/-- A BOOLEAN reads as `b` exactly when its tag is 1 and its content is the one octet of `b`.

TRUE is the octet FF and FALSE the octet 00, so every other content is rejected.

That is X.690 §§8.2.1 and 8.2.2, with the DER rule for TRUE of §11.1. -/
theorem boolean_ok_iff {value : Value} {b : Bool} :
    boolean value = .ok b ↔
      value.tag = 1 ∧ value.content.data.toList = [if b then 0xFF else 0x00] := by
  unfold boolean
  generalize value.content.data.toList = c
  by_cases ht : value.tag = 1
  · simp only [ht, bne_self_eq_false, Bool.false_eq_true, ite_false, true_and]
    rcases c with _ | ⟨x, _ | ⟨y, rest⟩⟩
    · simp [throw, throwThe, MonadExceptOf.throw]
    · by_cases h0 : x = 0
      · subst h0
        cases b <;> simp [pure, Except.pure]
      · by_cases h1 : x = 255
        · subst h1
          cases b <;> simp [pure, Except.pure]
        · cases b <;> simp [h0, h1, throw, throwThe, MonadExceptOf.throw]
    · simp [throw, throwThe, MonadExceptOf.throw]
  · simp [ht, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- A BIT STRING reads as `bytes` exactly when its tag is 3 and its content is 0, then `bytes`.

The initial octet 0 says that no bit of the final octet is unused (X.690 §8.6.2.2). -/
theorem bitString_ok_iff {value : Value} {bytes : ByteArray} :
    bitString value = .ok bytes ↔
      value.tag = 3 ∧ value.content.data.toList = 0 :: bytes.data.toList := by
  unfold bitString
  generalize value.content.data.toList = c
  by_cases ht : value.tag = 3
  · simp only [ht, bne_self_eq_false, Bool.false_eq_true, ite_false, true_and]
    rcases c with _ | ⟨x, rest⟩
    · simp [throw, throwThe, MonadExceptOf.throw]
    · by_cases h0 : x = 0
      · subst h0
        simp only [pure, Except.pure, Except.ok.injEq, List.cons.injEq, true_and]
        constructor
        · rintro rfl
          rfl
        · intro h
          apply byteArray_eq_of_toList
          simp [h]
      · simp [h0, throw, throwThe, MonadExceptOf.throw]
  · simp [ht, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- The low `u` bits of `n` are zero exactly when `2 ^ u` divides it with no remainder. -/
private theorem mod_two_pow_eq_zero_iff (n u : Nat) :
    n % 2 ^ u = 0 ↔ ∀ i < u, n.testBit i = false := by
  constructor
  · intro h i hi
    have := Nat.testBit_mod_two_pow n u i
    rw [h, Nat.zero_testBit] at this
    simpa [hi] using this.symm
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
    by_cases hi : i < u
    · simp [hi, h i hi]
    · simp [hi]

/-- BIT STRING contents pass exactly when the initial octet counts at most 7 unused bits, all zero.

The initial octet is 0 when no octet follows it (X.690 §8.6.2.3).

Otherwise the unused bits are the low bits of the final octet (X.690 §§8.6.2.1, 8.6.2.2).

Each of them is zero (X.690 §11.2.1).

The reader does not know the type, so it does not drop the trailing zero bits of §11.2.2. -/
theorem validBits_ok_iff {content : ByteArray} :
    validBits content = .ok () ↔ content.data.toList = [0] ∨
      ∃ unused init last, content.data.toList = unused :: (init ++ [last]) ∧
        unused.toNat ≤ 7 ∧ ∀ i < unused.toNat, last.toNat.testBit i = false := by
  unfold validBits
  generalize content.data.toList = c
  rcases c with _ | ⟨unused, bytes⟩
  · simp [throw, throwThe, MonadExceptOf.throw]
  rcases List.eq_nil_or_concat bytes with rfl | ⟨init, last, rfl⟩
  · by_cases h0 : unused = 0
    · subst h0
      simp [pure, Except.pure]
    · have : unused.toNat ≠ 0 := fun h => h0 (UInt8.toNat_inj.mp h)
      simp [h0, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  · simp only [List.concat_eq_append, List.getLast?_append, List.getLast?_singleton,
      Option.some_or]
    have hr : (unused :: (init ++ [last]) = [0] ∨ ∃ u i l, unused :: (init ++ [last]) =
        u :: (i ++ [l]) ∧ u.toNat ≤ 7 ∧ ∀ j < u.toNat, l.toNat.testBit j = false) ↔
        unused.toNat ≤ 7 ∧ last.toNat % 2 ^ unused.toNat = 0 := by
      constructor
      · rintro (h | ⟨u, i, l, h, h7, hb⟩)
        · simp at h
        · simp only [List.cons.injEq] at h
          obtain ⟨rfl, h⟩ := h
          obtain ⟨-, hl⟩ := List.append_inj' h rfl
          simp only [List.cons.injEq, and_true] at hl
          subst hl
          exact ⟨h7, (mod_two_pow_eq_zero_iff _ _).mpr hb⟩
      · rintro ⟨h7, hb⟩
        exact .inr ⟨unused, init, last, rfl, h7, (mod_two_pow_eq_zero_iff _ _).mp hb⟩
    rw [hr]
    by_cases h7 : 7 < unused.toNat
    · simp [h7, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
      omega
    · by_cases hm : last.toNat % 2 ^ unused.toNat = 0
      · simp [h7, hm, pure, Except.pure]
        omega
      · simp [h7, hm, throw, throwThe, MonadExceptOf.throw]

/-! ## BMPString and UniversalString -/

/-- One step of the code-unit reader: the octets of the current unit, their value, the verdict. -/
private def step (width : Nat) (state : Nat × Nat × Bool) (byte : UInt8) : Nat × Nat × Bool :=
  let n := state.2.1 * 256 + byte.toNat
  if state.1 + 1 = width then (0, 0, state.2.2 && unicodeScalar n)
  else (state.1 + 1, n, state.2.2)

/-- The verdict at the end: no partial code unit, and every code unit a scalar. -/
private def finish (state : Nat × Nat × Bool) : Bool := state.1 == 0 && state.2.2

/-- The code-unit reader is the fold of one step. -/
private theorem fixedString_eq (width : Nat) (bytes : List UInt8) :
    fixedString width bytes = finish (bytes.foldl (step width) (0, 0, true)) := rfl

/-- Octets that do not complete a code unit are counted and read big-endian. -/
private theorem foldl_step_partial {width : Nat} (bytes : List UInt8) (i acc : Nat) (ok : Bool)
    (h : i + bytes.length < width) :
    bytes.foldl (step width) (i, acc, ok) =
      (i + bytes.length, acc * 256 ^ bytes.length + bytesToNat bytes, ok) := by
  induction bytes generalizing i acc with
  | nil => simp [bytesToNat]
  | cons x xs ih =>
    simp only [List.length_cons] at h
    have hne : ¬ i + 1 = width := by omega
    simp only [List.foldl_cons, step, hne, ite_false]
    rw [ih (i + 1) (acc * 256 + x.toNat) (by omega), bytesToNat_cons]
    simp only [List.length_cons, Prod.mk.injEq, and_true]
    refine ⟨by omega, ?_⟩
    rw [Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 256, Nat.add_assoc]

/-- A complete code unit resets the count and adds its scalar check to the verdict. -/
private theorem foldl_step_chunk {width : Nat} (chunk : List UInt8) (ok : Bool)
    (pos : 0 < width) (h : chunk.length = width) :
    chunk.foldl (step width) (0, 0, ok) = (0, 0, ok && unicodeScalar (bytesToNat chunk)) := by
  rcases List.eq_nil_or_concat chunk with rfl | ⟨init, last, rfl⟩
  · simp at h
    omega
  · simp only [List.concat_eq_append, List.length_append, List.length_singleton] at h ⊢
    rw [List.foldl_append, foldl_step_partial init 0 0 ok (by omega)]
    simp [step, h, bytesToNat]

/-- A Unicode scalar value is at most 10FFFF and is not a surrogate, D800 to DFFF. -/
private theorem unicodeScalar_iff (n : Nat) :
    unicodeScalar n = true ↔ n ≤ 0x10FFFF ∧ (n < 0xD800 ∨ 0xDFFF < n) := by
  simp only [unicodeScalar, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
    Bool.not_true, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  omega

/-- The fold accepts from a verdict `ok` exactly when `ok` holds and the octets write scalars.

Each scalar takes `width` octets, big-endian. -/
private theorem finish_foldl_iff {width : Nat} (pos : 0 < width) (bytes : List UInt8)
    (ok : Bool) :
    finish (bytes.foldl (step width) (0, 0, ok)) = true ↔ ok = true ∧ ∃ chars : List Nat,
      (∀ c ∈ chars, c < 256 ^ width ∧ c ≤ 0x10FFFF ∧ (c < 0xD800 ∨ 0xDFFF < c)) ∧
      bytes = chars.flatMap (natToBytes width) := by
  induction h : bytes.length using Nat.strongRecOn generalizing bytes ok with
  | _ n ih =>
    by_cases hw : width ≤ bytes.length
    · -- The first code unit is the first `width` octets.
      rw [← List.take_append_drop width bytes, List.foldl_append,
        foldl_step_chunk _ ok pos (by simp; omega),
        ih (bytes.drop width).length (by simp; omega) _ _ rfl]
      constructor
      · rintro ⟨hok, chars, hc, he⟩
        rw [Bool.and_eq_true, unicodeScalar_iff] at hok
        refine ⟨hok.1, bytesToNat (bytes.take width) :: chars, ?_, ?_⟩
        · intro c hc'
          rcases List.mem_cons.mp hc' with rfl | hc'
          · refine ⟨?_, hok.2⟩
            have := bytesToNat_lt (bytes.take width)
            simpa [Nat.min_eq_left hw] using this
          · exact hc c hc'
        · have hl : (bytes.take width).length = width := by simp; omega
          rw [List.flatMap_cons, ← he]
          conv => lhs; rw [← natToBytes_bytesToNat (bytes.take width)]
          rw [hl]
      · rintro ⟨hok, chars, hc, he⟩
        rcases chars with _ | ⟨c, chars⟩
        · simp only [List.flatMap_nil, List.take_append_drop] at he
          rw [he] at hw
          simp at hw
          omega
        · rw [List.take_append_drop, List.flatMap_cons] at he
          have hc0 := hc c (by simp)
          have ht : bytes.take width = natToBytes width c := by
            rw [he, List.take_left' (natToBytes_length width c)]
          have hd : bytes.drop width = chars.flatMap (natToBytes width) := by
            rw [he, List.drop_left' (natToBytes_length width c)]
          rw [Bool.and_eq_true, unicodeScalar_iff, ht, bytesToNat_natToBytes_of_lt hc0.1]
          exact ⟨⟨hok, hc0.2⟩, chars, fun c' h' => hc c' (by simp [h']), hd⟩
    · -- Fewer than `width` octets pass only when there are none.
      rw [foldl_step_partial bytes 0 0 ok (by omega)]
      rcases bytes with _ | ⟨x, xs⟩
      · simp only [finish]
        simp
        intro _
        exact ⟨[], by simp, by simp⟩
      · have hz : (0 + (x :: xs).length == 0) = false := by simp
        simp only [finish, hz, Bool.false_and, Bool.false_eq_true, false_iff, not_and,
          not_exists]
        intro _ chars _ he
        rcases chars with _ | ⟨c, chars⟩
        · simp at he
        · have := congrArg List.length he
          simp [natToBytes_length] at this
          simp at hw
          omega

/-- Code units of `width` octets pass exactly when they write a list of Unicode scalar values.

The reader takes a scalar value to be at most 10FFFF and outside the surrogates D800 to DFFF.

Each is written big-endian on `width` octets, so it is below `256 ^ width`.

A UniversalString has four octets per character and a BMPString two (X.690 §§8.23.7, 8.23.8). -/
theorem fixedString_eq_true_iff {width : Nat} (pos : 0 < width) {bytes : List UInt8} :
    fixedString width bytes = true ↔ ∃ chars : List Nat,
      (∀ c ∈ chars, c < 256 ^ width ∧ c ≤ 0x10FFFF ∧ (c < 0xD800 ∨ 0xDFFF < c)) ∧
      bytes = chars.flatMap (natToBytes width) := by
  rw [fixedString_eq, finish_foldl_iff pos]
  simp

/-! ## OBJECT IDENTIFIER -/

/-- One step of the subidentifier check: reject a leading 80, then note whether one ends here. -/
private def oidStep (atStart : Bool) (byte : UInt8) : Except Error Bool := do
  if atStart ∧ byte = 128 then throw .value
  return byte.toNat < 128

/-- The check of a content is the fold of one step from the start of a subidentifier. -/
private theorem oid_eq (value : Value) : oid value = (do
    if value.tag != 6 then throw .tag
    if value.content.isEmpty then throw .value
    let atStart ← value.content.data.toList.foldlM oidStep true
    if atStart then return value.content else throw .value) := rfl

/-- Octets that end a subidentifier: bit 8 set on each but the last, clear on the last. -/
private def Tail (p : List UInt8) : Prop :=
  ∃ init last, p = init ++ [last] ∧ (∀ b ∈ init, 0x80 ≤ b.toNat) ∧ last.toNat < 0x80

/-- A subidentifier also has a first octet other than 80, so it is on the fewest octets. -/
private def Sub (p : List UInt8) : Prop := p.head? ≠ some 0x80 ∧ Tail p

/-- The octets that end a subidentifier are never empty. -/
private theorem tail_ne_nil {p : List UInt8} (h : Tail p) : p ≠ [] := by
  obtain ⟨init, last, rfl, -, -⟩ := h
  simp

/-- An octet that ends a subidentifier has bit 8 clear, and any other has it set. -/
private theorem tail_cons_iff (x : UInt8) (r : List UInt8) :
    Tail (x :: r) ↔ (r = [] ∧ x.toNat < 0x80) ∨ (0x80 ≤ x.toNat ∧ Tail r) := by
  constructor
  · rintro ⟨init, last, h, hi, hl⟩
    rcases init with _ | ⟨y, init⟩
    · simp only [List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .inl ⟨rfl, hl⟩
    · simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .inr ⟨hi _ (by simp), init, last, rfl, fun b hb => hi b (by simp [hb]), hl⟩
  · rintro (⟨rfl, hx⟩ | ⟨hx, init, last, rfl, hi, hl⟩)
    · exact ⟨[], x, rfl, by simp, hx⟩
    · refine ⟨x :: init, last, rfl, ?_, hl⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hx
      · exact hi b hb

/-- A split whose first piece is nonempty starts that piece with the first octet. -/
private theorem cons_eq_append_iff {Q : List UInt8 → Prop} (hQ : ∀ t, Q t → t ≠ [])
    (R : List (List UInt8) → Prop) (x : UInt8) (xs : List UInt8) :
    (∃ (t : List UInt8) (parts : List (List UInt8)),
        x :: xs = t ++ parts.flatten ∧ Q t ∧ R parts) ↔
      ∃ (r : List UInt8) (parts : List (List UInt8)),
        xs = r ++ parts.flatten ∧ Q (x :: r) ∧ R parts := by
  constructor
  · rintro ⟨t, parts, h, hq, hr⟩
    rcases t with _ | ⟨y, r⟩
    · exact absurd rfl (hQ _ hq)
    · simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨r, parts, rfl, hq, hr⟩
  · rintro ⟨r, parts, rfl, hq, hr⟩
    exact ⟨x :: r, parts, rfl, hq, hr⟩

/-- Nonempty octets split into subidentifiers exactly when a first one comes before the rest. -/
private theorem cons_eq_flatten_iff (x : UInt8) (xs : List UInt8) :
    (∃ parts : List (List UInt8), x :: xs = parts.flatten ∧ ∀ q ∈ parts, Sub q) ↔
      ∃ (t : List UInt8) (parts : List (List UInt8)),
        x :: xs = t ++ parts.flatten ∧ Sub t ∧ ∀ q ∈ parts, Sub q := by
  constructor
  · rintro ⟨_ | ⟨t, parts⟩, h, hp⟩
    · simp at h
    · exact ⟨t, parts, h, hp t (by simp), fun q hq => hp q (by simp [hq])⟩
  · rintro ⟨t, parts, h, ht, hp⟩
    refine ⟨t :: parts, h, ?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ht
    · exact hp q hq

/-- From the start of a subidentifier the fold ends at a start exactly on whole subidentifiers.

From inside one, it ends at a start exactly when the octets end that one first. -/
private theorem foldlM_oidStep (c : List UInt8) :
    (c.foldlM oidStep true = .ok true ↔
      ∃ parts : List (List UInt8), c = parts.flatten ∧ ∀ q ∈ parts, Sub q) ∧
    (c.foldlM oidStep false = .ok true ↔
      ∃ (t : List UInt8) (parts : List (List UInt8)),
        c = t ++ parts.flatten ∧ Tail t ∧ ∀ q ∈ parts, Sub q) := by
  induction c with
  | nil =>
    refine ⟨?_, ?_⟩
    · simp only [List.foldlM_nil, pure, Except.pure, true_iff]
      exact ⟨[], rfl, by simp⟩
    · simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, Bool.false_eq_true,
        false_iff, not_exists, not_and]
      intro t parts h ht
      have := tail_ne_nil ht
      simp_all
  | cons x xs ih =>
    have hS : ∀ t, Sub t → t ≠ [] := fun t h => tail_ne_nil h.2
    rw [cons_eq_flatten_iff, cons_eq_append_iff hS, cons_eq_append_iff (fun t h => tail_ne_nil h)]
    have hsub : ∀ r, Sub (x :: r) ↔ x ≠ 0x80 ∧ Tail (x :: r) := fun r => by simp [Sub]
    simp only [hsub, tail_cons_iff]
    have hnil : ∀ P : List (List UInt8) → Prop,
        (∃ parts : List (List UInt8), xs = parts.flatten ∧ P parts) ↔
          ∃ (r : List UInt8) (parts : List (List UInt8)),
            xs = r ++ parts.flatten ∧ r = [] ∧ P parts := by
      intro P
      constructor
      · rintro ⟨parts, h, hp⟩
        exact ⟨[], parts, h, rfl, hp⟩
      · rintro ⟨r, parts, h, rfl, hp⟩
        exact ⟨parts, h, hp⟩
    by_cases h128 : x = 0x80
    · subst h128
      simp [List.foldlM_cons, oidStep, throw, throwThe, MonadExceptOf.throw, bind,
        Except.bind, pure, Except.pure, ih.2]
    · by_cases hx : x.toNat < 0x80
      · have hx' : ¬ 0x80 ≤ x.toNat := by omega
        simp only [List.foldlM_cons, oidStep, h128, hx, hx', and_false, ite_false, pure,
          Except.pure, bind, Except.bind, decide_true, ih.1, false_and, or_false, true_and,
          ne_eq, not_false_eq_true, and_true]
        exact ⟨hnil _, hnil _⟩
      · have hx' : 0x80 ≤ x.toNat := by omega
        simp only [List.foldlM_cons, oidStep, h128, hx, hx', and_false, ite_false, pure,
          Except.pure, bind, Except.bind, decide_false, ih.2, false_or, true_and,
          ne_eq, not_false_eq_true]

/-- An OBJECT IDENTIFIER reads as `bytes` exactly when its tag is 6 and `bytes` is its content.

The content must be one or more subidentifiers (X.690 §8.19.2).

Bit 8 is set on each octet of a subidentifier but the last, and clear on the last.

The first octet of a subidentifier is not 80, so that it takes the fewest octets.

The first subidentifier combines two arcs, and any value of it names a valid pair (§8.19.4). -/
theorem oid_ok_iff {value : Value} {bytes : ByteArray} :
    oid value = .ok bytes ↔ value.tag = 6 ∧ bytes = value.content ∧
      ∃ parts : List (List UInt8), parts ≠ [] ∧ value.content.data.toList = parts.flatten ∧
        ∀ p ∈ parts, p.head? ≠ some 0x80 ∧ ∃ init last, p = init ++ [last] ∧
          (∀ b ∈ init, 0x80 ≤ b.toNat) ∧ last.toNat < 0x80 := by
  rw [oid_eq]
  change _ ↔ _ ∧ _ ∧ ∃ parts : List (List UInt8), parts ≠ [] ∧
    value.content.data.toList = parts.flatten ∧ ∀ p ∈ parts, Sub p
  have hempty : value.content.isEmpty = true ↔ value.content.data.toList = [] := by
    have hsize : value.content.size = value.content.data.toList.length := by
      rw [Array.length_toList]
      rfl
    simp only [ByteArray.isEmpty, hsize, beq_iff_eq, List.length_eq_zero_iff]
  by_cases ht : value.tag = 6
  · simp only [ht, bne_self_eq_false, Bool.false_eq_true, ite_false, true_and]
    revert hempty
    generalize value.content.data.toList = c
    intro hempty
    rcases c with _ | ⟨x, xs⟩
    · simp only [hempty, ite_true, throw, throwThe, MonadExceptOf.throw, bind, Except.bind,
        reduceCtorEq, false_iff, not_and, not_exists]
      intro _ parts hne h hp
      rcases parts with _ | ⟨p, parts⟩
      · exact hne rfl
      · have := tail_ne_nil (hp p (by simp)).2
        simp_all
    · have hne : ¬ value.content.isEmpty = true := by simp [hempty]
      have key := (foldlM_oidStep (x :: xs)).1
      cases h : (x :: xs).foldlM oidStep true with
      | error e =>
        simp only [hne, ↓reduceIte, bind, Except.bind, reduceCtorEq, false_iff, not_and,
          not_exists]
        intro _ parts _ hc hp
        rw [key.mpr ⟨parts, hc, hp⟩] at h
        cases h
      | ok a =>
        cases a
        · simp only [hne, ↓reduceIte, bind, Except.bind, Bool.false_eq_true, throw, throwThe,
            MonadExceptOf.throw, reduceCtorEq, false_iff, not_and, not_exists]
          intro _ parts _ hc hp
          rw [key.mpr ⟨parts, hc, hp⟩] at h
          cases h
        · obtain ⟨parts, hc, hp⟩ := key.mp h
          simp only [hne, ↓reduceIte, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
            Bool.false_eq_true]
          constructor
          · rintro rfl
            refine ⟨rfl, parts, ?_, hc, hp⟩
            rintro rfl
            simp at hc
          · rintro ⟨rfl, -⟩
            rfl
  · simp [ht, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-! ## The certificate subset -/

/-- With positive fuel, a value of tag 1 passes validation exactly when its content is 00 or FF. -/
theorem validate_go_boolean_ok_iff {value : Value} (fuel : Nat) (tag : value.tag = 1) :
    validate.go (fuel + 1) value = .ok () ↔
      value.content.data.toList = [0x00] ∨ value.content.data.toList = [0xFF] := by
  have hb : (∃ b, boolean value = .ok b) ↔
      value.content.data.toList = [0x00] ∨ value.content.data.toList = [0xFF] := by
    simp only [boolean_ok_iff, tag, true_and]
    constructor
    · rintro ⟨b, h⟩
      cases b <;> simp_all
    · rintro (h | h)
      · exact ⟨false, by simp [h]⟩
      · exact ⟨true, by simp [h]⟩
  rw [← hb, validate.go, tag]
  cases boolean value <;> simp [bind, Except.bind, pure, Except.pure]

/-- With positive fuel, a value of tag 3 passes validation exactly when its contents do. -/
theorem validate_go_bitString {value : Value} (fuel : Nat) (tag : value.tag = 3) :
    validate.go (fuel + 1) value = validBits value.content := by
  rw [validate.go, tag]
  rfl

/-- With positive fuel, a value of tag 30 passes validation exactly when it writes scalar values.

Each takes two octets. -/
theorem validate_go_bmpString_ok_iff {value : Value} (fuel : Nat) (tag : value.tag = 30) :
    validate.go (fuel + 1) value = .ok () ↔ ∃ chars : List Nat,
      (∀ c ∈ chars, c < 256 ^ 2 ∧ c ≤ 0x10FFFF ∧ (c < 0xD800 ∨ 0xDFFF < c)) ∧
      value.content.data.toList = chars.flatMap (natToBytes 2) := by
  rw [← fixedString_eq_true_iff (by decide), validate.go, tag]
  dsimp only
  split <;> simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-- With positive fuel, a value of tag 28 passes validation exactly when it writes scalar values.

Each takes four octets. -/
theorem validate_go_universalString_ok_iff {value : Value} (fuel : Nat) (tag : value.tag = 28) :
    validate.go (fuel + 1) value = .ok () ↔ ∃ chars : List Nat,
      (∀ c ∈ chars, c < 256 ^ 4 ∧ c ≤ 0x10FFFF ∧ (c < 0xD800 ∨ 0xDFFF < c)) ∧
      value.content.data.toList = chars.flatMap (natToBytes 4) := by
  rw [← fixedString_eq_true_iff (by decide), validate.go, tag]
  dsimp only
  split <;> simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-- A value of tag 1 passes validation exactly when its content is the octet 00 or the octet FF. -/
theorem validate_boolean_ok_iff {value : Value} (tag : value.tag = 1) :
    validate value = .ok () ↔
      value.content.data.toList = [0x00] ∨ value.content.data.toList = [0xFF] :=
  validate_go_boolean_ok_iff _ tag

/-- A value of tag 3 passes validation exactly when its contents are those of a BIT STRING. -/
theorem validate_bitString {value : Value} (tag : value.tag = 3) :
    validate value = validBits value.content :=
  validate_go_bitString _ tag

/-- A BMPString passes validation exactly when it writes Unicode scalar values, two octets each. -/
theorem validate_bmpString_ok_iff {value : Value} (tag : value.tag = 30) :
    validate value = .ok () ↔ ∃ chars : List Nat,
      (∀ c ∈ chars, c < 256 ^ 2 ∧ c ≤ 0x10FFFF ∧ (c < 0xD800 ∨ 0xDFFF < c)) ∧
      value.content.data.toList = chars.flatMap (natToBytes 2) :=
  validate_go_bmpString_ok_iff _ tag

/-- A UniversalString passes validation exactly when it writes scalar values, four octets each. -/
theorem validate_universalString_ok_iff {value : Value} (tag : value.tag = 28) :
    validate value = .ok () ↔ ∃ chars : List Nat,
      (∀ c ∈ chars, c < 256 ^ 4 ∧ c ≤ 0x10FFFF ∧ (c < 0xD800 ∨ 0xDFFF < c)) ∧
      value.content.data.toList = chars.flatMap (natToBytes 4) :=
  validate_go_universalString_ok_iff _ tag

/-- With positive fuel, a value of tag 6 passes validation exactly when it is subidentifiers.

Each has bit 8 set on all its octets but the last, and a first octet other than 80. -/
private theorem validate_go_oid_ok_iff {value : Value} (fuel : Nat) (tag : value.tag = 6) :
    validate.go (fuel + 1) value = .ok () ↔
      ∃ parts : List (List UInt8), parts ≠ [] ∧ value.content.data.toList = parts.flatten ∧
        ∀ p ∈ parts, p.head? ≠ some 0x80 ∧ ∃ init last, p = init ++ [last] ∧
          (∀ b ∈ init, 0x80 ≤ b.toNat) ∧ last.toNat < 0x80 := by
  have ho : (∃ b, oid value = .ok b) ↔ ∃ parts : List (List UInt8), parts ≠ [] ∧
      value.content.data.toList = parts.flatten ∧ ∀ p ∈ parts, p.head? ≠ some 0x80 ∧
        ∃ init last, p = init ++ [last] ∧ (∀ b ∈ init, 0x80 ≤ b.toNat) ∧
          last.toNat < 0x80 := by
    simp only [oid_ok_iff, tag, true_and, exists_eq_left]
  rw [← ho, validate.go, tag]
  cases oid value <;> simp [bind, Except.bind, pure, Except.pure]

/-- With positive fuel, a value of tag 5 passes validation exactly when its content is empty.

That is the NULL of X.690 §8.8.2. -/
private theorem validate_go_null_ok_iff {value : Value} (fuel : Nat) (tag : value.tag = 5) :
    validate.go (fuel + 1) value = .ok () ↔ value.content.data.toList = [] := by
  have hsize : value.content.size = value.content.data.toList.length := by
    rw [Array.length_toList]
    rfl
  rw [validate.go, tag]
  simp only [ByteArray.isEmpty, hsize, beq_iff_eq, List.length_eq_zero_iff]
  split <;> simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-- With positive fuel, a value of tag 12 passes validation exactly when it is UTF-8 characters.

That is the UTF8String of X.690 §8.23.10. -/
private theorem validate_go_utf8String_ok_iff {value : Value} (fuel : Nat) (tag : value.tag = 12) :
    validate.go (fuel + 1) value = .ok () ↔
      ∃ chars : List Char, value.content = chars.utf8Encode := by
  have hv : (String.fromUTF8? value.content).isSome = true ↔
      ∃ chars : List Char, value.content = chars.utf8Encode := by
    by_cases h : value.content.IsValidUTF8
    · simp only [String.fromUTF8?, h, dite_true, Option.isSome_some, true_iff]
      obtain ⟨chars, hc⟩ := h
      exact ⟨chars, hc⟩
    · simp only [String.fromUTF8?, h, dite_false, Option.isSome_none, Bool.false_eq_true,
        false_iff, not_exists]
      exact fun chars hc => h ⟨chars, hc⟩
  rw [← hv, validate.go, tag]
  split <;> simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-- The marks of PrintableString besides the letters and digits (X.680 §41.4). -/
private def printableMarks : List Char :=
  [' ', '\'', '(', ')', '+', ',', '-', '.', '/', ':', '=', '?']

/-- An octet is a PrintableString character: a Latin letter, a digit, or one of 12 marks. -/
private theorem printable_iff (b : UInt8) :
    ((48 ≤ b.toNat && b.toNat ≤ 57) || (65 ≤ b.toNat && b.toNat ≤ 90) ||
      (97 ≤ b.toNat && b.toNat ≤ 122) ||
      ([32, 39, 40, 41, 43, 44, 45, 46, 47, 58, 61, 63] : List UInt8).contains b) = true ↔
      (Char.ofNat b.toNat).isAlphanum ∨ Char.ofNat b.toNat ∈ printableMarks := by
  have key : ∀ n < 256,
      ((48 ≤ n && n ≤ 57) || (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122) ||
        ([32, 39, 40, 41, 43, 44, 45, 46, 47, 58, 61, 63] : List UInt8).contains
          (UInt8.ofNat n)) = true ↔
        (Char.ofNat n).isAlphanum ∨ Char.ofNat n ∈ printableMarks := by
    decide +kernel
  have := key b.toNat b.toNat_lt
  rwa [UInt8.ofNat_toNat] at this

/-- With positive fuel, a value of tag 19 passes validation exactly when it is PrintableString.

Each octet is then a Latin letter, a digit, a space or one of `'()+,-./:=?` (X.680 §41.4). -/
private theorem validate_go_printableString_ok_iff {value : Value} (fuel : Nat)
    (tag : value.tag = 19) :
    validate.go (fuel + 1) value = .ok () ↔ ∀ b ∈ value.content.data.toList,
      (Char.ofNat b.toNat).isAlphanum ∨
        Char.ofNat b.toNat ∈ [' ', '\'', '(', ')', '+', ',', '-', '.', '/', ':', '=', '?'] := by
  simp only [show [' ', '\'', '(', ')', '+', ',', '-', '.', '/', ':', '=', '?'] = printableMarks
    from rfl, ← printable_iff]
  rw [← List.all_eq_true, validate.go, tag]
  split <;> simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-- With positive fuel, a value of any tag outside the certificate subset is rejected by its tag.

The subset is BOOLEAN, INTEGER, BIT STRING, OCTET STRING, NULL and OBJECT IDENTIFIER.

It also holds the UTF8String, PrintableString, IA5String, UniversalString and BMPString.

The constructed SEQUENCE and SET have identifier octets 48 and 49. -/
private theorem validate_go_eq_error_tag {value : Value} (fuel : Nat)
    (tag : value.tag.toNat ∉ [1, 2, 3, 4, 5, 6, 12, 19, 22, 28, 30, 48, 49]) :
    validate.go (fuel + 1) value = .error .tag := by
  rw [validate.go]
  split <;> simp_all <;> rfl

/-- A value of tag 6 passes validation exactly when its content is one or more subidentifiers.

Each has bit 8 set on all its octets but the last, and a first octet other than 80. -/
theorem validate_oid_ok_iff {value : Value} (tag : value.tag = 6) :
    validate value = .ok () ↔
      ∃ parts : List (List UInt8), parts ≠ [] ∧ value.content.data.toList = parts.flatten ∧
        ∀ p ∈ parts, p.head? ≠ some 0x80 ∧ ∃ init last, p = init ++ [last] ∧
          (∀ b ∈ init, 0x80 ≤ b.toNat) ∧ last.toNat < 0x80 :=
  validate_go_oid_ok_iff _ tag

/-- A NULL passes validation exactly when its content is empty (X.690 §8.8.2). -/
theorem validate_null_ok_iff {value : Value} (tag : value.tag = 5) :
    validate value = .ok () ↔ value.content.data.toList = [] :=
  validate_go_null_ok_iff _ tag

/-- A UTF8String passes validation exactly when it is the UTF-8 encoding of some characters. -/
theorem validate_utf8String_ok_iff {value : Value} (tag : value.tag = 12) :
    validate value = .ok () ↔ ∃ chars : List Char, value.content = chars.utf8Encode :=
  validate_go_utf8String_ok_iff _ tag

/-- A PrintableString passes validation exactly when each octet is one of its characters.

Those are the Latin letters, the digits, the space and `'()+,-./:=?` (X.680 §41.4). -/
theorem validate_printableString_ok_iff {value : Value} (tag : value.tag = 19) :
    validate value = .ok () ↔ ∀ b ∈ value.content.data.toList,
      (Char.ofNat b.toNat).isAlphanum ∨
        Char.ofNat b.toNat ∈ [' ', '\'', '(', ')', '+', ',', '-', '.', '/', ':', '=', '?'] :=
  validate_go_printableString_ok_iff _ tag

/-- A value of a tag outside the certificate subset fails validation with a tag error. -/
theorem validate_eq_error_tag {value : Value}
    (tag : value.tag.toNat ∉ [1, 2, 3, 4, 5, 6, 12, 19, 22, 28, 30, 48, 49]) :
    validate value = .error .tag :=
  validate_go_eq_error_tag _ tag

/-! ## SEQUENCE and SET OF -/

/-- The size of a byte array is the length of its octet list. -/
private theorem size_eq_length (b : ByteArray) : b.size = b.data.toList.length := by
  rw [Array.length_toList]
  rfl

/-- A value that the reader returns has an encoding longer than its content, by its header. -/
private theorem size_lt_of_read_ok {input rest : ByteArray} {v : Value}
    (h : read input = .ok (v, rest)) :
    v.content.size < v.encoded.size ∧ v.encoded.size + rest.size = input.size := by
  obtain ⟨-, -, hin, hv⟩ := read_ok_iff.mp h
  refine ⟨?_, by rw [size_eq_length, size_eq_length, size_eq_length, hin, List.length_append]⟩
  rw [size_eq_length, size_eq_length]
  rcases hv with ⟨-, hv⟩ | ⟨k, -, -, -, -, hv⟩ <;> rw [hv] <;> simp <;> omega

/-- Each value that a read of siblings returns is a read value at most as long as the input. -/
private theorem children_go_sizes : ∀ (fuel : Nat) (input : ByteArray) (vs : List Value),
    children.go fuel input = .ok vs →
      ∀ v ∈ vs, v.content.size < v.encoded.size ∧ v.encoded.size ≤ input.size := by
  intro fuel
  induction fuel with
  | zero =>
    intro input vs h v hv
    simp only [children.go] at h
    split at h
    · cases h
      simp at hv
    · cases h
  | succ fuel ih =>
    intro input vs h v hv
    simp only [children.go] at h
    by_cases he : input.isEmpty = true
    · simp only [he, ite_true, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h
      subst h
      simp at hv
    · cases hr : read input with
      | error e => simp [he, hr, bind, Except.bind] at h
      | ok p =>
        obtain ⟨w, rest⟩ := p
        obtain ⟨hw, hsize⟩ := size_lt_of_read_ok hr
        cases hg : children.go fuel rest with
        | error e => simp [he, hr, hg, bind, Except.bind] at h
        | ok ws =>
          simp only [he, hr, hg, Bool.false_eq_true, ite_false, bind, Except.bind, pure,
            Except.pure, Except.ok.injEq] at h
          subst h
          rcases List.mem_cons.mp hv with rfl | hv
          · exact ⟨hw, by omega⟩
          · have := ih rest ws hg v hv
            omega

/-- Two checks that agree on each value agree on the list. -/
private theorem forM_congr {F G : Value → Except Error Unit} :
    ∀ vs : List Value, (∀ v ∈ vs, F v = G v) → vs.forM F = vs.forM G
  | [], _ => rfl
  | v :: vs, h => by
    show (F v >>= fun _ => vs.forM F) = (G v >>= fun _ => vs.forM G)
    rw [h v (by simp), forM_congr vs (fun w hw => h w (by simp [hw]))]

/-- Validation of a read value gives one verdict for every fuel above its encoded size. -/
private theorem go_fuel : ∀ (f g : Nat) (w : Value), w.content.size < w.encoded.size →
    w.encoded.size < f → w.encoded.size < g → validate.go f w = validate.go g w := by
  intro f
  induction f with
  | zero => intros; omega
  | succ f ih =>
    intro g w hw hf hg
    cases g with
    | zero => omega
    | succ g =>
      rw [validate.go, validate.go]
      split <;> try rfl
      all_goals
        cases hc : children w.content with
        | error e => rfl
        | ok vs =>
          have hvs : vs.forM (validate.go f) = vs.forM (validate.go g) := by
            apply forM_congr
            intro v hv
            have := children_go_sizes _ _ _ hc v hv
            exact ih g v this.1 (by omega) (by omega)
          simp only [bind, Except.bind, hvs]

/-- A check passes on a list exactly when it passes on each value. -/
private theorem forM_ok_iff {F : Value → Except Error Unit} :
    ∀ vs : List Value, vs.forM F = .ok () ↔ ∀ v ∈ vs, F v = .ok ()
  | [] => by simp [List.forM, pure, Except.pure]
  | v :: vs => by
    show (F v >>= fun _ => vs.forM F) = .ok () ↔ _
    rw [List.forall_mem_cons, ← forM_ok_iff vs]
    cases F v <;> simp [bind, Except.bind]

/-- A constructed value passes validation exactly when its content reads as values that pass.

A SET OF also needs the encodings of those values in ascending order. -/
private theorem validate_constructed_ok_iff {value : Value}
    (tag : value.tag.toNat = 48 ∨ value.tag.toNat = 49)
    (header : value.content.size < value.encoded.size) :
    validate value = .ok () ↔ ∃ values, children value.content = .ok values ∧
      (value.tag = 49 → (values.map (·.encoded.data.toList)).Pairwise (· ≤ ·)) ∧
        ∀ v ∈ values, validate v = .ok () := by
  have hforM : ∀ vs, children value.content = .ok vs →
      (vs.forM (validate.go value.encoded.size) = .ok () ↔
        ∀ v ∈ vs, validate v = .ok ()) := by
    intro vs hc
    rw [forM_ok_iff]
    have hgo : ∀ v ∈ vs, validate.go value.encoded.size v = validate v := by
      intro v hv
      have := children_go_sizes _ _ _ hc v hv
      exact go_fuel _ _ v this.1 (by omega) (by omega)
    constructor
    · intro h v hv
      rw [← hgo v hv]
      exact h v hv
    · intro h v hv
      rw [hgo v hv]
      exact h v hv
  rw [validate, validate.go]
  rcases tag with h | h <;> simp only [h] <;>
    cases hc : children value.content with
    | error e => simp [bind, Except.bind]
    | ok vs =>
      simp only [bind, Except.bind, Except.ok.injEq, exists_eq_left', ← hforM vs hc]
      by_cases h49 : value.tag = 49
      · by_cases hp : (vs.map (·.encoded.data.toList)).Pairwise (· ≤ ·)
        · simp [h49, hp]
        · simp [h49, hp, throw, throwThe, MonadExceptOf.throw]
      · simp [h49]

/-- A SEQUENCE passes validation exactly when its content reads as values that each pass.

Every value that the reader returns has a header, so its encoding is longer than its content. -/
theorem validate_sequence_ok_iff {value : Value} (tag : value.tag = 48)
    (header : value.content.size < value.encoded.size) :
    validate value = .ok () ↔ ∃ values, children value.content = .ok values ∧
      ∀ v ∈ values, validate v = .ok () := by
  rw [validate_constructed_ok_iff (.inl (by rw [tag]; rfl)) header]
  simp [tag]

/-- A SET OF passes validation exactly when its content reads as values that each pass.

Their encodings must also come in ascending order, compared octet by octet (X.690 §11.6).

Every value that the reader returns has a header, so its encoding is longer than its content. -/
theorem validate_set_ok_iff {value : Value} (tag : value.tag = 49)
    (header : value.content.size < value.encoded.size) :
    validate value = .ok () ↔ ∃ values, children value.content = .ok values ∧
      (values.map (·.encoded.data.toList)).Pairwise (· ≤ ·) ∧
        ∀ v ∈ values, validate v = .ok () := by
  rw [validate_constructed_ok_iff (.inr (by rw [tag]; rfl)) header]
  simp [tag]

end EthLib.Serialization.Proofs.Der
