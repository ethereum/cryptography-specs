import EthCryptographySpecs.Kzg.Polynomials
import EthCryptographySpecs.Proofs.Bls.Fr
import EthCryptographySpecs.Proofs.Kzg.BitReversal

/-!
# Proofs: `Polynomials`

Properties of the polynomial helpers: byte <-> field element
conversions round-trip, `computePowers` really returns powers,
`blobToPolynomial` is characterized on its success and failure paths,
and evaluation at a domain point is a table lookup.
-/

namespace EthCryptographySpecs.Kzg

open EthCryptographySpecs.Bls (Fr)
open EthCryptographySpecs.Kzg.Constants
open EthCryptographySpecs.Kzg.BitReversal

/-- `bytesBEToNatAux` coincides with `Fr.fromBytesBEAux` (they implement
the same fold). -/
private theorem bytesBEToNatAux_eq_fromBytesBEAux (acc : Nat)
    (l : List UInt8) :
    bytesBEToNatAux acc l = Bls.Fr.fromBytesBEAux acc l := by
  induction l generalizing acc with
  | nil => rfl
  | cons u rest ih =>
    simp only [bytesBEToNatAux, Bls.Fr.fromBytesBEAux]
    exact ih _

/-- Shifting left by a byte and or-ing in a byte is base-256 arithmetic. -/
private theorem shiftLeft_eight_or (a u : Nat) (hu : u < 256) :
    (a <<< 8) ||| u = a * 256 + u := by
  have h28 : (2 : Nat) ^ 8 = 256 := by decide
  have h1 : ((a <<< 8) ||| u) % 2 ^ 8 = u := by
    rw [Nat.or_mod_two_pow, Nat.shiftLeft_eq, Nat.mul_mod_left,
      Nat.mod_eq_of_lt (h28 ▸ hu), Nat.zero_or]
  have h2 : ((a <<< 8) ||| u) / 2 ^ 8 = a := by
    rw [Nat.or_div_two_pow, Nat.shiftLeft_eq,
      Nat.mul_div_cancel a (Nat.two_pow_pos 8),
      Nat.div_eq_of_lt (h28 ▸ hu), Nat.or_zero]
  have h3 := Nat.div_add_mod ((a <<< 8) ||| u) (2 ^ 8)
  rw [h1, h2, h28] at h3
  omega

/-- The accumulator contributes linearly: `acc` is worth
`acc * 256 ^ length`. -/
private theorem bytesBEToNatAux_linear (acc : Nat) (l : List UInt8) :
    bytesBEToNatAux acc l = acc * 256 ^ l.length + bytesBEToNatAux 0 l := by
  induction l generalizing acc with
  | nil => simp [bytesBEToNatAux]
  | cons u rest ih =>
    rw [bytesBEToNatAux, ih, shiftLeft_eight_or acc u.toNat u.toNat_lt_size,
      bytesBEToNatAux, Nat.zero_shiftLeft, Nat.zero_or, ih u.toNat,
      List.length_cons, Nat.pow_succ]
    generalize (256 : Nat) ^ rest.length = P
    rw [Nat.add_mul, Nat.mul_comm P 256, ← Nat.mul_assoc, Nat.add_assoc]

/-- A big-endian decoding fits in `8 * size` bits. -/
theorem bytesBEToNat_lt (b : ByteArray) : bytesBEToNat b < 256 ^ b.size := by
  have haux : ∀ l : List UInt8, bytesBEToNatAux 0 l < 256 ^ l.length := by
    intro l
    induction l with
    | nil => simp [bytesBEToNatAux]
    | cons u rest ih =>
      rw [bytesBEToNatAux, Nat.zero_shiftLeft, Nat.zero_or,
        bytesBEToNatAux_linear, List.length_cons, Nat.pow_succ]
      have h1 : u.toNat * 256 ^ rest.length + 256 ^ rest.length
          ≤ 256 * 256 ^ rest.length := by
        rw [← Nat.succ_mul]
        exact Nat.mul_le_mul_right _ u.toNat_lt_size
      omega
  have := haux b.data.toList
  simpa [bytesBEToNat] using this

/-- Decoding the encoding of `n` over `len` bytes recovers `n` modulo
`256 ^ len`. -/
theorem bytesBEToNat_intToBytesBE (n len : Nat) :
    bytesBEToNat (intToBytesBE n len) = n % 256 ^ len := by
  induction len with
  | zero => simp [bytesBEToNat, intToBytesBE, bytesBEToNatAux, Nat.mod_one]
  | succ len ih =>
    have hdecomp : (intToBytesBE n (len + 1)).data.toList
        = UInt8.ofNat ((n >>> (len * 8)) &&& 0xff) ::
          (intToBytesBE n len).data.toList := by
      have h0 : len + 1 - 1 - 0 = len := by omega
      have hs : ∀ i : Fin len, len + 1 - 1 - (i.val + 1) = len - 1 - i.val :=
        fun i => by omega
      simp only [intToBytesBE, Array.toList_ofFn, List.ofFn_succ,
        Fin.val_zero, Fin.val_succ, h0, hs]
    have hlen : (intToBytesBE n len).data.toList.length = len := by
      simp [intToBytesBE]
    have hbyte : (UInt8.ofNat ((n >>> (len * 8)) &&& 0xff)).toNat
        = n / 256 ^ len % 256 := by
      rw [UInt8.toNat_ofNat', show (0xff : Nat) = 2 ^ 8 - 1 by decide,
        Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod,
        Nat.shiftRight_eq_div_pow, Nat.pow_mul',
        show (2 : Nat) ^ 8 = 256 by decide]
    rw [bytesBEToNat, hdecomp, bytesBEToNatAux, Nat.zero_shiftLeft,
      Nat.zero_or, bytesBEToNatAux_linear, hlen, hbyte]
    rw [bytesBEToNat] at ih
    rw [ih, Nat.pow_succ, Nat.mod_mul, Nat.mul_comm (n / 256 ^ len % 256)]
    exact Nat.add_comm _ _

/-- Decoding inverts encoding for values that fit in `len` bytes. -/
theorem bytesBEToNat_intToBytesBE_of_lt {n len : Nat}
    (h : n < 256 ^ len) :
    bytesBEToNat (intToBytesBE n len) = n := by
  rw [bytesBEToNat_intToBytesBE, Nat.mod_eq_of_lt h]

/-- A successful `bytesToBlsField` implies: the input was 32 bytes, the
value is the big-endian decoding, and the value is canonical. -/
theorem bytesToBlsField_ok {b : Bytes32} {f : Fr}
    (h : bytesToBlsField b = .ok f) :
    b.size = BYTES_PER_FIELD_ELEMENT ∧ f.val = bytesBEToNat b ∧
      f.val < Fr.modulus := by
  rw [bytesToBlsField] at h
  split at h
  · cases h
  · split at h
    · rename_i g hg
      cases h
      obtain ⟨hsz, hval, hlt⟩ := Bls.Fr.fromBytesBE_ok hg
      refine ⟨hsz, ?_, hlt⟩
      rw [hval, bytesBEToNat, bytesBEToNatAux_eq_fromBytesBEAux]
    · cases h

@[simp] theorem length_computePowersAux (x current : Fr) (n : Nat) :
    (computePowersAux x current n).length = n := by
  induction n generalizing current with
  | zero => rfl
  | succ n ih => simp [computePowersAux, ih]

@[simp] theorem size_computePowers (x : Fr) (n : Nat) :
    (computePowers x n).size = n := by
  simp [computePowers]

/-- Element `i` of `computePowersAux x current n` is `current * x ^ i`
(stated with an `if` so that it also holds for non-canonical `current`,
which is returned unchanged at index `0`). -/
theorem getElem_computePowersAux (x current : Fr) (n i : Nat)
    (h : i < (computePowersAux x current n).length) :
    (computePowersAux x current n)[i] =
      if i = 0 then current else current * Fr.powNat x i := by
  induction n generalizing current i with
  | zero => exact absurd h (by simp)
  | succ n ih =>
    cases i with
    | zero => simp [computePowersAux]
    | succ i =>
      simp only [computePowersAux, List.getElem_cons_succ]
      rw [ih]
      cases i with
      | zero =>
        rw [if_pos rfl, if_neg (Nat.succ_ne_zero 0), Fr.powNat_succ,
          Fr.powNat_zero, Fr.mul_mul_one]
      | succ i =>
        rw [if_neg (Nat.succ_ne_zero i), if_neg (Nat.succ_ne_zero (i + 1)),
          Fr.powNat_succ x (i + 1), ← Fr.mul_assoc]

/-- `computePowers x n` is `[x^0, x^1, ..., x^(n-1)]`, as its docstring
claims. -/
theorem getElem_computePowers (x : Fr) (n i : Nat)
    (h : i < (computePowers x n).size) :
    (computePowers x n)[i] = Fr.powNat x i := by
  have hl : i < (computePowersAux x Fr.one n).length := by
    simpa [computePowers] using h
  show (computePowersAux x Fr.one n).toArray[i] = _
  rw [List.getElem_toArray, getElem_computePowersAux x Fr.one n i hl]
  cases i with
  | zero => rw [if_pos rfl, Fr.powNat_zero]
  | succ i =>
    rw [if_neg (Nat.succ_ne_zero i), Fr.powNat_succ, Fr.one_mul_mul,
      ← Fr.powNat_succ]

@[simp] theorem size_computeRootsOfUnity (order : Nat) :
    (computeRootsOfUnity order).size = order := by
  simp [computeRootsOfUnity]

/-- A successful `blobToPolynomialAux` returns exactly `count` elements. -/
theorem length_blobToPolynomialAux (blob : Blob) (i count : Nat)
    (l : List Fr) (h : blobToPolynomialAux blob i count = .ok l) :
    l.length = count := by
  induction count generalizing i l with
  | zero =>
    rw [blobToPolynomialAux] at h
    cases h
    rfl
  | succ count ih =>
    rw [blobToPolynomialAux] at h
    split at h
    · rename_i f hf
      cases hrec : blobToPolynomialAux blob (i + 1) count with
      | ok rest =>
        rw [hrec] at h
        cases h
        simp [ih (i + 1) rest hrec]
      | error e =>
        rw [hrec] at h
        cases h
    · cases h

/-- Element `j` of a successful `blobToPolynomialAux` decode is the
decoding of chunk `start + j`. -/
theorem getElem_blobToPolynomialAux (blob : Blob) (start count : Nat)
    (l : List Fr) (h : blobToPolynomialAux blob start count = .ok l)
    (j : Nat) (hj : j < l.length) :
    bytesToBlsField (blob.extract ((start + j) * BYTES_PER_FIELD_ELEMENT)
      ((start + j + 1) * BYTES_PER_FIELD_ELEMENT)) = .ok l[j] := by
  induction count generalizing start l j with
  | zero =>
    rw [blobToPolynomialAux] at h
    cases h
    exact absurd hj (by simp)
  | succ count ih =>
    rw [blobToPolynomialAux] at h
    split at h
    · rename_i f hf
      cases hrec : blobToPolynomialAux blob (start + 1) count with
      | ok rest =>
        rw [hrec] at h
        cases h
        cases j with
        | zero => simpa using hf
        | succ j =>
          have := ih (start + 1) rest hrec j (by simpa using hj)
          simpa [show start + 1 + j = start + (j + 1) by omega] using this
      | error e =>
        rw [hrec] at h
        cases h
    · cases h

/-- `blobToPolynomialAux` fails exactly with the index of the *first*
invalid chunk: that chunk does not decode, and every chunk before it
does. -/
theorem blobToPolynomialAux_error (blob : Blob) (start count : Nat)
    (e : KzgError) (h : blobToPolynomialAux blob start count = .error e) :
    ∃ j, start ≤ j ∧ j < start + count ∧
      e = .invalidFieldElement (some j) ∧
      (∀ f, bytesToBlsField (blob.extract (j * BYTES_PER_FIELD_ELEMENT)
        ((j + 1) * BYTES_PER_FIELD_ELEMENT)) ≠ .ok f) ∧
      (∀ k, start ≤ k → k < j →
        ∃ f, bytesToBlsField (blob.extract (k * BYTES_PER_FIELD_ELEMENT)
          ((k + 1) * BYTES_PER_FIELD_ELEMENT)) = .ok f) := by
  induction count generalizing start e with
  | zero =>
    rw [blobToPolynomialAux] at h
    cases h
  | succ count ih =>
    rw [blobToPolynomialAux] at h
    split at h
    · rename_i f hf
      cases hrec : blobToPolynomialAux blob (start + 1) count with
      | ok rest =>
        rw [hrec] at h
        cases h
      | error e' =>
        rw [hrec] at h
        cases h
        obtain ⟨j, hj1, hj2, hj3, hj4, hj5⟩ := ih (start + 1) e hrec
        refine ⟨j, by omega, by omega, hj3, hj4, fun k hk1 hk2 => ?_⟩
        rcases Nat.eq_or_lt_of_le hk1 with rfl | hk
        · exact ⟨f, hf⟩
        · exact hj5 k hk hk2
    · rename_i herr
      cases h
      refine ⟨start, Nat.le_refl _, by omega, rfl, fun f hf => ?_,
        fun k hk1 hk2 => absurd (Nat.lt_of_le_of_lt hk1 hk2)
          (Nat.lt_irrefl _)⟩
      rw [herr] at hf
      cases hf

/-- A successful `blobToPolynomial` returns exactly
`FIELD_ELEMENTS_PER_BLOB` field elements. -/
theorem size_blobToPolynomial (blob : Blob) (poly : Polynomial)
    (h : blobToPolynomial blob = .ok poly) :
    poly.size = FIELD_ELEMENTS_PER_BLOB := by
  rw [blobToPolynomial] at h
  split at h
  · cases h
  · generalize FIELD_ELEMENTS_PER_BLOB = N at h ⊢
    cases hrec : blobToPolynomialAux blob 0 N with
    | ok l =>
      rw [hrec] at h
      cases h
      simpa using length_blobToPolynomialAux blob 0 N l hrec
    | error e =>
      rw [hrec] at h
      cases h

/-- Element `i` of a successful `blobToPolynomial` is the decoding of
the `i`-th 32-byte chunk of the blob. -/
theorem getElem_blobToPolynomial (blob : Blob) (poly : Polynomial)
    (h : blobToPolynomial blob = .ok poly) (i : Nat) (hi : i < poly.size) :
    bytesToBlsField (blob.extract (i * BYTES_PER_FIELD_ELEMENT)
      ((i + 1) * BYTES_PER_FIELD_ELEMENT)) = .ok poly[i] := by
  rw [blobToPolynomial] at h
  split at h
  · cases h
  · generalize FIELD_ELEMENTS_PER_BLOB = N at h
    cases hrec : blobToPolynomialAux blob 0 N with
    | ok l =>
      rw [hrec] at h
      cases h
      have hj : i < l.length := by simpa using hi
      have := getElem_blobToPolynomialAux blob 0 N l hrec i hj
      simpa using this
    | error e =>
      rw [hrec] at h
      cases h

/-- A `blobToPolynomial` failure with `invalidFieldElement (some j)`
means: the blob size was right, `j` is in range, chunk `j` does not
decode, and all chunks before `j` do. -/
theorem blobToPolynomial_error_invalidFieldElement (blob : Blob) (j : Nat)
    (h : blobToPolynomial blob = .error (.invalidFieldElement (some j))) :
    blob.size = BYTES_PER_BLOB ∧ j < FIELD_ELEMENTS_PER_BLOB ∧
      (∀ f, bytesToBlsField (blob.extract (j * BYTES_PER_FIELD_ELEMENT)
        ((j + 1) * BYTES_PER_FIELD_ELEMENT)) ≠ .ok f) ∧
      (∀ k, k < j →
        ∃ f, bytesToBlsField (blob.extract (k * BYTES_PER_FIELD_ELEMENT)
          ((k + 1) * BYTES_PER_FIELD_ELEMENT)) = .ok f) := by
  rw [blobToPolynomial] at h
  split at h
  · rename_i hsz
    cases h
  · rename_i hsz
    refine ⟨by omega, ?_⟩
    generalize hN : FIELD_ELEMENTS_PER_BLOB = N at h ⊢
    cases hrec : blobToPolynomialAux blob 0 N with
    | ok l =>
      rw [hrec] at h
      cases h
    | error e =>
      rw [hrec] at h
      cases h
      obtain ⟨j', _, hj2, hj3, hj4, hj5⟩ :=
        blobToPolynomialAux_error blob 0 N _ hrec
      cases hj3
      exact ⟨by omega, hj4, fun k hk => hj5 k (Nat.zero_le k) hk⟩

/-- `blobToPolynomial` fails with `badBlobSize` exactly when the blob has
the wrong size (and reports that size). -/
theorem blobToPolynomial_error_badBlobSize (blob : Blob) (n : Nat) :
    blobToPolynomial blob = .error (.badBlobSize n) ↔
      blob.size ≠ BYTES_PER_BLOB ∧ n = blob.size := by
  rw [blobToPolynomial]
  split
  · rename_i hsz
    constructor
    · intro h
      cases h
      exact ⟨hsz, rfl⟩
    · rintro ⟨_, rfl⟩
      rfl
  · rename_i hsz
    constructor
    · intro h
      generalize FIELD_ELEMENTS_PER_BLOB = N at h
      cases hrec : blobToPolynomialAux blob 0 N with
      | ok l =>
        rw [hrec] at h
        cases h
      | error e =>
        rw [hrec] at h
        cases h
        obtain ⟨j, _, _, hj3, _, _⟩ :=
          blobToPolynomialAux_error blob 0 N _ hrec
        cases hj3
    · rintro ⟨hcontra, _⟩
      exact absurd hcontra hsz

@[simp] theorem size_rootsOfUnityBrp (size : Nat) :
    (rootsOfUnityBrp size).size = size := by
  simp [rootsOfUnityBrp, size_bitReversalPermutation]

/-- When `z` is the `i`-th element of `domain`, evaluation is a table
lookup. -/
theorem evaluatePolynomialInEvaluationFormAux_fastPath
    (polynomial domain : Array Fr) (z : Fr) (i : Nat)
    (h : domain.idxOf? z = some i) :
    evaluatePolynomialInEvaluationFormAux polynomial domain z
      = polynomial[i]! := by
  rw [evaluatePolynomialInEvaluationFormAux]
  simp only [h]

/-- When `z` is the `i`-th element of the evaluation domain, evaluating
the polynomial at `z` is a table lookup. -/
theorem evaluatePolynomialInEvaluationForm_fastPath
    (polynomial : Polynomial) (z : Fr) (i : Nat)
    (h : (rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB).idxOf? z = some i) :
    evaluatePolynomialInEvaluationForm polynomial z = polynomial[i]! :=
  evaluatePolynomialInEvaluationFormAux_fastPath polynomial _ z i h

end EthCryptographySpecs.Kzg
