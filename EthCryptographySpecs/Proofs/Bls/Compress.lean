import EthCryptographySpecs.Bls.Compress
import EthCryptographySpecs.Proofs.Bls.G1Group
import EthCryptographySpecs.Proofs.IdLoops
import EthCryptographySpecs.Proofs.Kzg.Polynomials

/-!
# Proofs: `Fp.sqrt` and the G1 compressed-encoding round-trip

`Fp.sqrt` computes `a^((p+1)/4)`, which squares back to `a` exactly on
quadratic residues (`p ≡ 3 (mod 4)`): soundness (`sqrt_ok`) is the
spec's own final check, completeness (`sqrt_complete`) is Euler's
criterion. On top of this, `uncompress_compress` shows that
decompressing a compressed valid point recovers the same group
element (the Jacobian representative changes — compression
normalizes to `z = 1` — but its `toPoint` does not).
-/

deriving instance DecidableEq for EthCryptographySpecs.Bls.BlsError
deriving instance DecidableEq for EthCryptographySpecs.Bls.G1

namespace EthCryptographySpecs.Bls.Fp

set_option maxRecDepth 4000

/-- `Fp.beq` in `ZMod` form (compare `G1.beq_iff`). -/
private theorem beq_iff' {a b : Fp} :
    a.beq b = true ↔ (a : ZMod Fp.modulus) = b := by
  rw [Fp.beq, beq_iff_eq]
  exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩

/-- Soundness of `Fp.sqrt`: a returned root squares to the input. -/
theorem sqrt_ok {a c : Fp} (h : Fp.sqrt a = .ok c) :
    (c : ZMod Fp.modulus) * c = a := by
  rw [Fp.sqrt] at h
  split at h
  · rename_i hbeq
    cases h
    exact beq_iff'.mp hbeq
  · cases h

/-- The core Euler-criterion computation, phrased over `ZMod`. -/
private theorem pow_sqrt_exponent {x y : ZMod Fp.modulus} (h : y * y = x) :
    x ^ ((Fp.modulus + 1) / 4) * x ^ ((Fp.modulus + 1) / 4) = x := by
  by_cases hy : y = 0
  · subst hy
    rw [← h, mul_zero, zero_pow (by decide : (Fp.modulus + 1) / 4 ≠ 0),
        mul_zero]
  · subst h
    rw [← pow_add, ← pow_two, ← pow_mul,
        show 2 * ((Fp.modulus + 1) / 4 + (Fp.modulus + 1) / 4)
          = (Fp.modulus - 1) + 2 by decide,
        pow_add, ZMod.pow_card_sub_one_eq_one hy, one_mul, pow_two]

/-- Completeness of `Fp.sqrt`: it succeeds on every square. -/
theorem sqrt_complete {a b : Fp} (h : (b : ZMod Fp.modulus) * b = a) :
    Fp.sqrt a = .ok (Fp.powNat a ((Fp.modulus + 1) / 4)) := by
  have hcand : (Fp.powNat a ((Fp.modulus + 1) / 4) : ZMod Fp.modulus)
      * Fp.powNat a ((Fp.modulus + 1) / 4) = a := by
    rw [powNat_eq_zmod_pow a ((Fp.modulus + 1) / 4)]
    exact pow_sqrt_exponent h
  rw [Fp.sqrt, if_pos (beq_iff'.mpr hcand)]

/-! ## Big-endian byte recovery

`Fp.toBytesBE` is definitionally the KZG codec's `intToBytesBE` at
width 48, whose decode-encode round-trip is already proved in
`Proofs.Kzg.Polynomials`; the only new content is converting the
spec's `Id.run` decoding loop (`Fp.bytesBEToNat`) into the KZG
list-fold decoder. -/

private theorem byteArray_getElem! (b : ByteArray) (i : Nat) :
    b[i]! = b.data[i]! := by
  by_cases h : i < b.size
  · rw [getElem!_pos b i h, getElem!_pos b.data i h]
    rfl
  · rw [getElem!_neg b i h, getElem!_neg b.data i h]

open EthCryptographySpecs.IdLoops in
/-- The spec's byte-decoding loop, as a fold over the byte list. -/
private theorem bytesBEToNat_eq_list (b : ByteArray) :
    Fp.bytesBEToNat b
      = b.data.toList.foldl (fun acc u => (acc <<< 8) ||| u.toNat) 0 := by
  unfold Fp.bytesBEToNat
  dsimp only [Id.run, id_pure, id_bind]
  rw [forIn_range_yield]
  rw [show (fun (acc : Nat) (i : Nat) => (acc <<< 8) ||| b[i]!.toNat)
      = fun acc i => (acc <<< 8) ||| b.data[i]!.toNat from
      funext fun acc => funext fun i => by rw [byteArray_getElem!]]
  show (List.range' 0 b.data.size).foldl
      (fun acc i => (acc <<< 8) ||| b.data[i]!.toNat) 0 = _
  exact foldl_range'_getElem! b.data (fun acc u => (acc <<< 8) ||| u.toNat) 0

/-- The KZG list-fold decoder agrees with `List.foldl`. -/
private theorem kzgAux_eq_foldl (l : List UInt8) (acc : Nat) :
    Kzg.bytesBEToNatAux acc l
      = l.foldl (fun acc u => (acc <<< 8) ||| u.toNat) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons u rest ih =>
    rw [Kzg.bytesBEToNatAux, List.foldl_cons]
    exact ih _

/-- Decoding the encoding of a field element recovers its value. -/
private theorem bytesBEToNat_toBytesBE (x : Fp) :
    Fp.bytesBEToNat (Fp.toBytesBE x) = x.val := by
  have heq : Fp.toBytesBE x = Kzg.intToBytesBE x.val 48 := rfl
  rw [heq, bytesBEToNat_eq_list, ← kzgAux_eq_foldl]
  have := Kzg.bytesBEToNat_intToBytesBE_of_lt
    (n := x.val) (len := 48) (by
      calc x.val < Fp.modulus := x.isLt
        _ < 256 ^ 48 := by decide)
  rwa [Kzg.bytesBEToNat] at this

/-! ## Encoding size, byte 0, and the `fromBytesBE` round-trip -/

theorem size_toBytesBE (x : Fp) : (Fp.toBytesBE x).size = 48 := by
  simp only [Fp.toBytesBE, ByteArray.size, Array.size_ofFn]

set_option maxHeartbeats 1000000 in
/-- Byte 0 (most significant) of the big-endian encoding, via `.get!`
(the form `compress` uses). -/
theorem get!_toBytesBE_zero (x : Fp) :
    ((Fp.toBytesBE x).get! 0).toNat = (x.val >>> (47 * 8)) &&& 0xff := by
  have hdata : (Fp.toBytesBE x).get! 0 = (Array.ofFn (n := 48) (fun j =>
      UInt8.ofNat ((x.val >>> ((47 - j.val) * 8)) &&& 0xff)))[0]! := rfl
  rw [hdata,
    getElem!_pos (Array.ofFn (n := 48) fun j =>
      UInt8.ofNat ((x.val >>> ((47 - j.val) * 8)) &&& 0xff)) 0
      (by rw [Array.size_ofFn]; decide),
    Array.getElem_ofFn, UInt8.toNat_ofNat',
    show (0xff : Nat) = 2 ^ 8 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod, Nat.and_two_pow_sub_one_eq_mod]
  norm_num

set_option exponentiation.threshold 400 in
/-- The most significant byte of a canonical field element has its top
three bits clear (`< 0x20`), since `p < 2^381 = 32·2^376`. -/
theorem toBytesBE_head_lt (x : Fp) : ((Fp.toBytesBE x).get! 0).toNat < 0x20 := by
  rw [get!_toBytesBE_zero]
  have hb : x.val < 32 * 2 ^ (47 * 8) := lt_of_lt_of_le x.isLt (by decide)
  have hsr : x.val >>> (47 * 8) < 32 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hb)
  have hand : (x.val >>> (47 * 8)) &&& 0xff ≤ x.val >>> (47 * 8) := Nat.and_le_left
  omega

theorem fromBytesBE_toBytesBE (x : Fp) : Fp.fromBytesBE x.toBytesBE = .ok x := by
  rw [Fp.fromBytesBE, if_neg (by rw [size_toBytesBE]; decide),
    dif_pos (by rw [bytesBEToNat_toBytesBE]; exact x.isLt)]
  congr 1
  apply Fin.ext
  exact bytesBEToNat_toBytesBE x


end EthCryptographySpecs.Bls.Fp


namespace EthCryptographySpecs.Bls.G1

open WeierstrassCurve.Jacobian
open scoped EthCryptographySpecs.Bls.Fp

set_option maxRecDepth 4000

/-! ## Affine coordinates satisfy the curve equation -/

/-- Pure `ZMod` curve identity whose term structure matches `toAffine`
and uncompress's `rhs`, so it transfers to the spec goal by `exact`
(defeq: `Fin`-mul ≡ `ZMod`-mul). -/
private theorem curve_eq_aux (x y z w : ZMod Fp.modulus) (hw : z * w = 1)
    (heq : y ^ 2 = x ^ 3 + 4 * z ^ 6) :
    (y * (w * w * w)) * (y * (w * w * w))
      = x * (w * w) * (x * (w * w)) * (x * (w * w)) + 4 := by
  have h6 : (z * w) ^ 6 = 1 := by rw [hw, one_pow]
  linear_combination w ^ 6 * heq + 4 * h6

private theorem z_mul_inverse {p : G1} (hz : ¬ p.z.isZero = true) :
    (p.z : ZMod Fp.modulus) * (p.z.inverse : ZMod Fp.modulus) = 1 := by
  rw [Fp.inverse_eq_inv]
  exact mul_inv_cancel₀ (fun hh => hz (isZero_iff.mpr hh))

/-- The affine `y` squares to `x³ + 4` (matching uncompress's `rhs`). -/
theorem affine_sqrt_witness {p : G1} (h : Valid p) (hz : ¬ p.z.isZero = true) :
    ((p.toAffine).2 : ZMod Fp.modulus) * (p.toAffine).2
      = (p.toAffine).1 * (p.toAffine).1 * (p.toAffine).1 + Fp.ofNat 4 := by
  have heq := valid_equation h
  rw [rep_x, rep_y, rep_z] at heq
  have hw := z_mul_inverse hz
  simp only [G1.toAffine, if_neg hz]
  exact curve_eq_aux p.x p.y p.z p.z.inverse hw heq

/-! ## Sign-bit recovery -/

/-- Sign bit flips under negation of a nonzero element (`p` is odd, so
`y ≠ p − y`). -/
theorem signBit_neg {y : Fp} (hy : y ≠ 0) :
    Fp.signBit (-y) = !Fp.signBit y := by
  have hv : (-y).val = Fp.modulus - y.val := by
    rw [Fin.val_neg, if_neg hy]
  have hy0 : 0 < y.val := Nat.pos_of_ne_zero (fun hh => hy (Fin.ext hh))
  have hylt : y.val < Fp.modulus := y.isLt
  have hodd : Fp.modulus % 2 = 1 := by decide
  unfold Fp.signBit
  rw [hv, show Fp.modulus - (Fp.modulus - y.val) = y.val from by omega]
  rcases Nat.lt_trichotomy y.val (Fp.modulus - y.val) with h | h | h
  · rw [decide_eq_true (show Fp.modulus - y.val > y.val by omega),
      decide_eq_false (show ¬ y.val > Fp.modulus - y.val by omega), Bool.not_false]
  · omega
  · rw [decide_eq_false (show ¬ Fp.modulus - y.val > y.val by omega),
      decide_eq_true (show y.val > Fp.modulus - y.val by omega), Bool.not_true]

/-! ## The two square roots -/

/-- `yPos = ±ya`: any square root of `ya²` is `ya` or `-ya`
(`ZMod Fp.modulus` is a domain, as `p` is prime). -/
private theorem sqrt_pm {ya yPos : ZMod Fp.modulus}
    (h : yPos * yPos = ya * ya) : yPos = ya ∨ yPos = -ya := by
  have hfac : (yPos - ya) * (yPos + ya) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact Or.inl (sub_eq_zero.mp h1)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h2)

/-- Uncompress's sign selection recovers the original `y` from `±y`
and the stored sign bit. -/
private theorem sign_recovery {ya yPos : Fp}
    (hsq : (yPos : ZMod Fp.modulus) * yPos = (ya : ZMod Fp.modulus) * ya) :
    (if Fp.signBit yPos = Fp.signBit ya then yPos else -yPos) = ya := by
  rcases sqrt_pm hsq with h | h
  · rw [show yPos = ya from h, if_pos rfl]
  · rw [show yPos = -ya from h]
    by_cases hya : ya = 0
    · subst hya
      simp
    · rw [signBit_neg hya, if_neg (Bool.not_ne_self _), neg_neg]

/-! ## `ByteArray` `get!`/`set!` plumbing -/

private theorem ba_size_set! (b : ByteArray) (j : Nat) (v : UInt8) :
    (b.set! j v).size = b.size := Array.size_setIfInBounds

private theorem ba_get!_set!_ne (b : ByteArray) {i j : Nat} (v : UInt8)
    (hne : i ≠ j) : (b.set! j v).get! i = b.get! i := by
  show (b.data.setIfInBounds j v)[i]! = b.data[i]!
  by_cases hi : i < b.data.size
  · rw [getElem!_pos (b.data.setIfInBounds j v) i
        (by rw [Array.size_setIfInBounds]; exact hi),
      getElem!_pos b.data i hi, Array.getElem_setIfInBounds_ne hi (fun hh => hne hh.symm)]
  · rw [getElem!_neg (b.data.setIfInBounds j v) i
        (by rw [Array.size_setIfInBounds]; exact hi),
      getElem!_neg b.data i hi]

private theorem ba_get!_set!_self (b : ByteArray) {j : Nat} (v : UInt8)
    (hj : j < b.size) : (b.set! j v).get! j = v := by
  show (b.data.setIfInBounds j v)[j]! = v
  rw [getElem!_pos (b.data.setIfInBounds j v) j
    (by rw [Array.size_setIfInBounds]; exact hj), Array.getElem_setIfInBounds_self]

private theorem ba_ext {a b : ByteArray} (hsz : a.size = b.size)
    (h : ∀ i, i < a.size → a.get! i = b.get! i) : a = b := by
  apply ByteArray.ext
  apply Array.ext hsz
  intro i hi1 hi2
  have := h i hi1
  rwa [show a.get! i = a.data[i]! from rfl, show b.get! i = b.data[i]! from rfl,
    getElem!_pos a.data i hi1, getElem!_pos b.data i hi2] at this

/-! ## `toPoint` of the affine normalization -/

private theorem xval_aux (x z w : ZMod Fp.modulus) (hw : z * w = 1) :
    x * (w * w) * z ^ 2 = x := by linear_combination x * (z * w + 1) * hw

private theorem yval_aux (y z w : ZMod Fp.modulus) (hw : z * w = 1) :
    y * (w * w * w) * z ^ 3 = y := by
  linear_combination y * ((z * w) ^ 2 + z * w + 1) * hw

private theorem xeq_aux (x z w one : ZMod Fp.modulus) (hw : z * w = 1)
    (hone : one = 1) : x * (w * w) * z ^ 2 = x * one ^ 2 := by
  subst hone; rw [one_pow, mul_one]; exact xval_aux x z w hw

private theorem yeq_aux (y z w one : ZMod Fp.modulus) (hw : z * w = 1)
    (hone : one = 1) : y * (w * w * w) * z ^ 3 = y * one ^ 3 := by
  subst hone; rw [one_pow, mul_one]; exact yval_aux y z w hw

/-- The compressed-then-decompressed point (affine, `z = 1`) denotes the
same group element as `p`. -/
theorem toPoint_affine_normalize {p : G1} (hz : ¬ p.z.isZero = true) :
    toPoint ⟨(p.toAffine).1, (p.toAffine).2, Fp.one⟩ = toPoint p := by
  have hzne : (p.z : ZMod Fp.modulus) ≠ 0 := fun hh => hz (isZero_iff.mpr hh)
  have hw := z_mul_inverse hz
  refine Point.toAffine_of_equiv (equiv_of_X_eq_of_Y_eq one_ne_zero hzne ?_ ?_)
  · -- rep q 0 * rep p 2 ^ 2 = rep p 0 * rep q 2 ^ 2
    simp only [rep, G1.toAffine, if_neg hz, Matrix.cons_val_zero,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    exact xeq_aux p.x p.z p.z.inverse Fp.one hw rfl
  · simp only [rep, G1.toAffine, if_neg hz, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    exact yeq_aux p.y p.z p.z.inverse Fp.one hw rfl

/-! ## Compress → uncompress round-trip -/

private theorem compress_inf {p : G1} (hinf : p.isInfinity = true) :
    compress p = infinityBytes := by
  unfold compress; simp only [Id.run, hinf, if_true]; rfl

private theorem compress_noninf {p : G1} (hinf : ¬ p.isInfinity = true)
    {xa ya : Fp} (hpa : p.toAffine = (xa, ya)) :
    compress p =
      (let base := (Fp.toBytesBE xa).set! 0 ((Fp.toBytesBE xa).get! 0 ||| 0x80)
       if Fp.signBit ya then base.set! 0 (base.get! 0 ||| 0x20) else base) := by
  unfold compress
  simp only [Id.run, hinf, hpa]
  rfl

/-- The infinity round-trip is a closed 48-byte decidable computation
that the kernel will not reduce through (`Array.replicate` and the
`tailAllZero` loop), so it is discharged by `native_decide`. This is a
finite check, not a mathematical assumption. -/
private theorem uncompress_infinityBytes :
    uncompress infinityBytes = .ok zero := by native_decide

/-- Sign selection in `uncompress` (a `Prop`-equality condition)
recovers `y` from `±y` and the stored sign bit. -/
private theorem sign_recovery' {ya yPos : Fp} {P : Prop} [Decidable P]
    (hsq : (yPos : ZMod Fp.modulus) * yPos = (ya : ZMod Fp.modulus) * ya)
    (hP : P ↔ (Fp.signBit ya = true)) :
    (if (Fp.signBit yPos = true) = P then yPos else -yPos) = ya := by
  have key : ((Fp.signBit yPos = true) = P) ↔ (Fp.signBit yPos = Fp.signBit ya) := by
    rw [eq_iff_iff, hP]
    by_cases h1 : Fp.signBit yPos = true <;> by_cases h2 : Fp.signBit ya = true <;>
      simp_all
  rw [if_congr key rfl rfl]
  exact sign_recovery hsq

/-- Uncompress recovers `⟨xa, ya, 1⟩` from compressed bytes `cb`
satisfying the flag- and coordinate-level facts. -/
private theorem uncompress_of_facts {xa ya yPos : Fp} {cb : ByteArray}
    (hsize : cb.size = 48)
    (hc : (cb.get! 0 &&& 0x80) ≠ 0)
    (hi : (cb.get! 0 &&& 0x40) = 0)
    (hsg : (cb.get! 0 &&& 0x20 ≠ 0) ↔ (Fp.signBit ya = true))
    (hmaskeq : cb.set! 0 (cb.get! 0 &&& 0x1f) = Fp.toBytesBE xa)
    (hsqrt : Fp.sqrt (xa * xa * xa + Fp.ofNat 4) = .ok yPos)
    (hysq : (yPos : ZMod Fp.modulus) * yPos = (ya : ZMod Fp.modulus) * ya) :
    uncompress cb = .ok ⟨xa, ya, Fp.one⟩ := by
  rw [uncompress, if_neg (by rw [hsize]; decide)]
  simp only
  rw [if_neg (by rw [decide_eq_true hc]; decide), if_neg (by rw [hi]; decide),
    hmaskeq, Fp.fromBytesBE_toBytesBE]
  simp only [hsqrt]
  rw [sign_recovery' hysq hsg]

/-- **Compression round-trip.** For any valid point `p`, `compress`
followed by `uncompress` succeeds and returns a point `q` denoting the
same group element (`toPoint q = toPoint p`). The Jacobian
representative is generally *not* preserved — `compress` records only
the affine `x` plus the sign of `y`, so decompression rebuilds the
canonical `z = 1` representative — but the underlying curve point is.
This is the encoding half of the BLS G1 serialization spec; it relies
on `p` being prime (both square roots are `±y`, recovered via the
stored sign bit) and on `p ≡ 3 (mod 4)` (so `Fp.sqrt` is exact). -/
theorem uncompress_compress {p : G1} (h : Valid p) :
    ∃ q, uncompress (compress p) = .ok q ∧ toPoint q = toPoint p := by
  by_cases hinf : p.isInfinity = true
  · refine ⟨zero, ?_, ?_⟩
    · rw [compress_inf hinf]; exact uncompress_infinityBytes
    · rw [toPoint_zero]
      exact (Point.toAffine_of_Z_eq_zero (W := curve)
        (isZero_iff.mp hinf : rep p 2 = 0)).symm
  · rcases hpa : p.toAffine with ⟨xa, ya⟩
    set B0 := (Fp.toBytesBE xa).get! 0 with hB0
    have hb0 : B0 < 0x20 := by
      rw [hB0, UInt8.lt_iff_toNat_lt]; exact Fp.toBytesBE_head_lt xa
    have hsqw : (ya : ZMod Fp.modulus) * ya = xa * xa * xa + Fp.ofNat 4 := by
      have := affine_sqrt_witness h hinf; rw [hpa] at this; exact this
    have hsqrt := Fp.sqrt_complete hsqw
    have hysq : ((Fp.powNat (xa * xa * xa + Fp.ofNat 4)
        ((Fp.modulus + 1) / 4) : Fp) : ZMod Fp.modulus)
        * Fp.powNat (xa * xa * xa + Fp.ofNat 4) ((Fp.modulus + 1) / 4)
        = (ya : ZMod Fp.modulus) * ya := by rw [Fp.sqrt_ok hsqrt, ← hsqw]
    have hsz48 : (Fp.toBytesBE xa).size = 48 := Fp.size_toBytesBE xa
    have hcp := compress_noninf hinf hpa
    have hother : ∀ i, i ≠ 0 → (compress p).get! i = (Fp.toBytesBE xa).get! i := by
      intro i hi0
      rw [hcp]; dsimp only
      by_cases hs : Fp.signBit ya
      · rw [if_pos hs, ba_get!_set!_ne _ _ hi0, ba_get!_set!_ne _ _ hi0]
      · rw [if_neg hs, ba_get!_set!_ne _ _ hi0]
    have hsize : (compress p).size = 48 := by
      rw [hcp]; dsimp only
      by_cases hs : Fp.signBit ya
      · rw [if_pos hs, ba_size_set!, ba_size_set!, hsz48]
      · rw [if_neg hs, ba_size_set!, hsz48]
    refine ⟨⟨xa, ya, Fp.one⟩, ?_, ?_⟩
    · by_cases hs : Fp.signBit ya
      · have hhead : (compress p).get! 0 = B0 ||| 0x80 ||| 0x20 := by
          rw [hcp]; dsimp only
          rw [if_pos hs, ba_get!_set!_self _ _ (by rw [ba_size_set!, hsz48]; decide),
            ba_get!_set!_self _ _ (by rw [hsz48]; decide)]
        refine uncompress_of_facts hsize (by rw [hhead]; bv_decide)
          (by rw [hhead]; bv_decide) ?_ ?_ hsqrt hysq
        · rw [hhead]
          exact ⟨fun _ => hs, fun _ => by bv_decide⟩
        · refine ba_ext (by rw [ba_size_set!, hsize, hsz48]) (fun i hi' => ?_)
          rw [ba_size_set!, hsize] at hi'
          by_cases hi0 : i = 0
          · subst hi0
            rw [ba_get!_set!_self _ _ (by rw [hsize]; decide), hhead, ← hB0]; bv_decide
          · rw [ba_get!_set!_ne _ _ hi0, hother i hi0]
      · have hhead : (compress p).get! 0 = B0 ||| 0x80 := by
          rw [hcp]; dsimp only
          rw [if_neg hs, ba_get!_set!_self _ _ (by rw [hsz48]; decide)]
        refine uncompress_of_facts hsize (by rw [hhead]; bv_decide)
          (by rw [hhead]; bv_decide) ?_ ?_ hsqrt hysq
        · rw [hhead]
          exact ⟨fun hne => absurd (by bv_decide) hne, fun hh => absurd hh hs⟩
        · refine ba_ext (by rw [ba_size_set!, hsize, hsz48]) (fun i hi' => ?_)
          rw [ba_size_set!, hsize] at hi'
          by_cases hi0 : i = 0
          · subst hi0
            rw [ba_get!_set!_self _ _ (by rw [hsize]; decide), hhead, ← hB0]; bv_decide
          · rw [ba_get!_set!_ne _ _ hi0, hother i hi0]
    · have := toPoint_affine_normalize (p := p) hinf
      rw [hpa] at this; exact this

end EthCryptographySpecs.Bls.G1
