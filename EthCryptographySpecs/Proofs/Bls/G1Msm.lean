import EthCryptographySpecs.Proofs.Bls.G1Order
import EthCryptographySpecs.Proofs.IdLoops

/-!
# Proofs: the spec's Pippenger MSM computes `Σ [sᵢ]Pᵢ`

Two layers:

1. **Mechanical**: `G1.msm` (an `Id.run do` program with counted
   `for` loops and mutable state) equals a pure `List.foldl` model
   (`msmModel`), by converting each loop with
   `Std.Legacy.Range.forIn_eq_forIn_range'` and an `Id`-specialized
   fold lemma. No group theory here.
2. **Mathematical**: the model computes
   `Σ i ∈ range n, [scalars[i]]points[i]` in the curve group, via the
   bucket-partition and running-sum identities and the base-`2^w`
   window recomposition of the scalars.

The headline result is `toPoint_msm`.
-/

namespace EthCryptographySpecs.Bls.G1

open EthCryptographySpecs.IdLoops

set_option maxRecDepth 4000

/-! ## The pure model of `msm` -/

/-- Window `k` of a scalar: bits `[8k, 8k + 8)` of its value. -/
def windowVal (s : Fr) (k : Nat) : Nat := (s.val >>> (k * 8)) &&& (1 <<< 8 - 1)

/-- The `maxBits` fold: maximal bit length among the first `n`
scalars. -/
def msmMaxBits (scalars : Array Fr) (n : Nat) : Nat :=
  (List.range' 0 n).foldl (fun m j =>
    if scalars[j]!.val ≠ 0 then
      if scalars[j]!.val.log2 + 1 > m then scalars[j]!.val.log2 + 1 else m
    else m) 0

/-- The bucket-accumulation fold for window `k`. -/
def msmBuckets (points : Array G1) (scalars : Array Fr) (n k : Nat) :
    Array G1 :=
  (List.range' 0 n).foldl (fun bs j =>
    if windowVal scalars[j]! k ≠ 0 then
      bs.set! (windowVal scalars[j]! k)
        (add bs[windowVal scalars[j]! k]! points[j]!)
    else bs) (Array.replicate (1 <<< 8) zero)

/-- The running-sum fold, walking `v` from `255` down to `1`. The
state is `⟨partialSum, running⟩` — the `do`-elaborator packs the two
mutable variables in *reverse* declaration order — so the first
component accumulates `Σ_{v>0} v·b_v` and the second `Σ_{v>0} b_v`. -/
def msmRunning (bs : Array G1) : MProd G1 G1 :=
  (List.range' 0 (1 <<< 8 - 1)).foldl (fun rp vv =>
    ⟨add rp.1 (add rp.2 bs[1 <<< 8 - 1 - vv]!),
     add rp.2 bs[1 <<< 8 - 1 - vv]!⟩) ⟨zero, zero⟩

/-- One window iteration of the Pippenger loop. The conditional
doubling is distributed over the final addition exactly as in the
`do`-notation desugaring of `msm`, so the mechanical equality below is
definitional at this node. -/
def msmWindowStep (points : Array G1) (scalars : Array Fr) (n nW : Nat)
    (acc : G1) (kk : Nat) : G1 :=
  if nW - 1 - kk + 1 < nW then
    add ((List.range' 0 8).foldl (fun a _ => double a) acc)
      (msmRunning (msmBuckets points scalars n (nW - 1 - kk))).1
  else
    add acc (msmRunning (msmBuckets points scalars n (nW - 1 - kk))).1

/-- The pure model of `G1.msm`. -/
def msmModel (points : Array G1) (scalars : Array Fr) : G1 :=
  let n := if points.size ≤ scalars.size then points.size else scalars.size
  if n = 0 then zero
  else if msmMaxBits scalars n = 0 then zero
  else
    (List.range' 0 ((msmMaxBits scalars n + 8 - 1) / 8)).foldl
      (msmWindowStep points scalars n ((msmMaxBits scalars n + 8 - 1) / 8))
      zero

/-! ## `msm` equals its model (mechanical layer) -/

/-- The `maxBits` loop, converted and folded into `msmMaxBits` in one
step, so the (large) fold expression never gets duplicated into later
goals. -/
private theorem maxBits_forIn_eq (scalars : Array Fr) (N : Nat) :
    (forIn (m := Id) [:N] 0 (fun j m =>
        if scalars[j]!.val ≠ 0 then
          if scalars[j]!.val.log2 + 1 > m then
            ForInStep.yield (scalars[j]!.val.log2 + 1)
          else ForInStep.yield m
        else ForInStep.yield m))
      = msmMaxBits scalars N :=
  (forIn_range_yield_ite₂ N 0 _ _ _).trans rfl

set_option maxHeartbeats 1600000 in
private theorem foldl_congr_fun {α β : Type} {f g : β → α → β}
    (h : f = g) (init : β) (l : List α) :
    l.foldl f init = l.foldl g init := by rw [h]

theorem msm_eq_msmModel (points : Array G1) (scalars : Array Fr) :
    msm points scalars = msmModel points scalars := by
  unfold msm msmModel
  dsimp only [Id.run, id_pure, id_bind]
  by_cases h0 : (if points.size ≤ scalars.size then points.size
    else scalars.size) = 0
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0, maxBits_forIn_eq]
    by_cases h1 : msmMaxBits scalars (if points.size ≤ scalars.size
      then points.size else scalars.size) = 0
    · rw [if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1, forIn_range_yield_ite]
      refine foldl_congr_fun ?_ _ _
      funext acc kk
      unfold msmWindowStep msmBuckets msmRunning windowVal
      rw [forIn_range_yield, forIn_range_yield_ite, forIn_range_yield]

/-! ## The math layer: `msmModel` computes `Σ [sᵢ]Pᵢ` -/

open Finset

/-- The `maxBits` fold function, named for the induction proofs. -/
private def maxBitsF (scalars : Array Fr) (m j : Nat) : Nat :=
  if scalars[j]!.val ≠ 0 then
    if scalars[j]!.val.log2 + 1 > m then scalars[j]!.val.log2 + 1 else m
  else m

private theorem msmMaxBits_eq_foldl (scalars : Array Fr) (n : Nat) :
    msmMaxBits scalars n = (List.range' 0 n).foldl (maxBitsF scalars) 0 := rfl

private theorem maxBitsF_le (scalars : Array Fr) (l : List Nat) :
    ∀ init, init ≤ l.foldl (maxBitsF scalars) init := by
  induction l with
  | nil => exact fun _ => Nat.le_refl _
  | cons a l ih =>
    intro init
    refine Nat.le_trans ?_ (ih (maxBitsF scalars init a))
    rw [maxBitsF]
    split
    · split
      · exact Nat.le_of_lt (by assumption)
      · exact Nat.le_refl _
    · exact Nat.le_refl _

private theorem maxBitsF_bound (scalars : Array Fr) (l : List Nat) :
    ∀ init j, j ∈ l →
      scalars[j]!.val < 2 ^ (l.foldl (maxBitsF scalars) init) := by
  induction l with
  | nil => exact fun _ j hj => absurd hj (List.not_mem_nil)
  | cons a l ih =>
    intro init j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · -- the head: the fold is at least `log2 + 1` (or the value is 0)
      by_cases h0 : scalars[j]!.val = 0
      · rw [h0]
        exact Nat.two_pow_pos _
      · have hstep : scalars[j]!.val.log2 + 1 ≤ maxBitsF scalars init j := by
          rw [maxBitsF, if_pos h0]
          split
          · exact Nat.le_refl _
          · omega
        have hle := Nat.le_trans hstep (maxBitsF_le scalars l _)
        calc scalars[j]!.val < 2 ^ (scalars[j]!.val.log2 + 1) :=
              Nat.lt_log2_self
          _ ≤ 2 ^ (List.foldl (maxBitsF scalars) (maxBitsF scalars init j) l) :=
              Nat.pow_le_pow_right (by omega) hle
    · exact ih (maxBitsF scalars init a) j hj

/-- Every scalar among the first `n` is below `2 ^ msmMaxBits`. -/
private theorem msmMaxBits_bound (scalars : Array Fr) (n : Nat) :
    ∀ j, j < n → scalars[j]!.val < 2 ^ msmMaxBits scalars n := by
  intro j hj
  rw [msmMaxBits_eq_foldl]
  exact maxBitsF_bound scalars (List.range' 0 n) 0 j
    (List.mem_range'_1.mpr ⟨Nat.zero_le j, by omega⟩)

/-- The base-`2⁸` digit decomposition that drives the window
recomposition: shifting eight fewer bits is `256·(shift) + window`. -/
private theorem shift_window (s a : Nat) :
    s >>> a = (1 <<< 8) * (s >>> (a + 8)) + ((s >>> a) &&& (1 <<< 8 - 1)) := by
  rw [Nat.shiftRight_add, show ((1 : Nat) <<< 8 - 1) = 2 ^ 8 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow (s >>> a) 8,
      show ((1 : Nat) <<< 8) = 2 ^ 8 from rfl]
  omega

/-- Iterated doubling is multiplication by `2^m` in the group. -/
private theorem doubleFold_spec {a : G1} (h : Valid a) (m : Nat) :
    Valid ((List.range' 0 m).foldl (fun x _ => double x) a)
    ∧ toPoint ((List.range' 0 m).foldl (fun x _ => double x) a)
        = 2 ^ m • toPoint a := by
  induction m with
  | zero => exact ⟨h, by rw [pow_zero, one_nsmul]; rfl⟩
  | succ m ih =>
    rw [List.range'_1_concat, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
    refine ⟨valid_double ih.1, ?_⟩
    rw [toPoint_double ih.1, ih.2, ← two_nsmul, ← mul_nsmul', ← pow_succ']

/-- The bucket fold: sizes, validity, and the partition sums.
Bucket `0` is never written and stays `zero`; bucket `v > 0` collects
exactly the points whose window value is `v`. -/
private theorem msmBuckets_spec (points : Array G1) (scalars : Array Fr)
    (n k : Nat) (hval : ∀ j, j < n → Valid points[j]!) :
    (msmBuckets points scalars n k).size = 1 <<< 8
    ∧ (∀ v, v < 1 <<< 8 → Valid (msmBuckets points scalars n k)[v]!)
    ∧ ∀ v, v < 1 <<< 8 →
        toPoint (msmBuckets points scalars n k)[v]!
          = if v = 0 then 0
            else ∑ j ∈ (range n).filter (fun j => windowVal scalars[j]! k = v),
              toPoint points[j]! := by
  induction n with
  | zero =>
    have hsz : ∀ v, v < 1 <<< 8 →
        v < (Array.replicate (1 <<< 8) (zero : G1)).size := by
      intro v hv
      simpa using hv
    have hget : ∀ v, (hv : v < 1 <<< 8) →
        (msmBuckets points scalars 0 k)[v]! = zero := by
      intro v hv
      rw [show msmBuckets points scalars 0 k
          = Array.replicate (1 <<< 8) zero from rfl,
        getElem!_pos (Array.replicate (1 <<< 8) (zero : G1)) v (hsz v hv),
        Array.getElem_replicate]
    refine ⟨by simp [msmBuckets], fun v hv => ?_, fun v hv => ?_⟩
    · rw [hget v hv]
      exact valid_zero
    · rw [hget v hv]
      split
      · exact toPoint_zero
      · rw [show range 0 = (∅ : Finset Nat) from rfl, Finset.filter_empty,
          Finset.sum_empty]
        exact toPoint_zero
  | succ n ih =>
    have ihn := ih (fun j hj => hval j (by omega))
    have hstep : msmBuckets points scalars (n + 1) k
        = if windowVal scalars[n]! k ≠ 0 then
            (msmBuckets points scalars n k).setIfInBounds
              (windowVal scalars[n]! k)
              (add (msmBuckets points scalars n k)[windowVal scalars[n]! k]!
                points[n]!)
          else msmBuckets points scalars n k := by
      rw [msmBuckets, msmBuckets, List.range'_1_concat, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      simp only [Nat.zero_add]
      rfl
    have hwlt : windowVal scalars[n]! k < 1 <<< 8 := by
      have := Nat.and_le_right (n := scalars[n]!.val >>> (k * 8))
        (m := 1 <<< 8 - 1)
      rw [windowVal]
      omega
    by_cases hw : windowVal scalars[n]! k ≠ 0
    · rw [hstep, if_pos hw]
      set bs := msmBuckets points scalars n k with hbs
      set w := windowVal scalars[n]! k with hwdef
      have hsz : (bs.setIfInBounds w (add bs[w]! points[n]!)).size
          = 1 <<< 8 := by
        rw [Array.size_setIfInBounds]
        exact ihn.1
      have hwbs : w < bs.size := by omega
      refine ⟨hsz, fun v hv => ?_, fun v hv => ?_⟩
      · have hv' : v < (bs.setIfInBounds w (add bs[w]! points[n]!)).size := by
          omega
        rw [getElem!_pos (bs.setIfInBounds w (add bs[w]! points[n]!)) v hv']
        by_cases hveq : w = v
        · subst hveq
          rw [Array.getElem_setIfInBounds_self]
          exact valid_add (ihn.2.1 w hwlt) (hval n (by omega))
        · rw [Array.getElem_setIfInBounds_ne (by omega : v < bs.size) hveq]
          rw [show bs[v] = bs[v]! from (getElem!_pos bs v (by omega)).symm]
          exact ihn.2.1 v hv
      · have hv' : v < (bs.setIfInBounds w (add bs[w]! points[n]!)).size := by
          omega
        rw [getElem!_pos (bs.setIfInBounds w (add bs[w]! points[n]!)) v hv']
        by_cases hv0 : v = 0
        · subst hv0
          rw [if_pos rfl, Array.getElem_setIfInBounds_ne
            (by omega : (0 : Nat) < bs.size) hw,
            show bs[(0 : Nat)] = bs[(0 : Nat)]! from
              (getElem!_pos bs 0 (by omega)).symm]
          have := ihn.2.2 0 (by omega)
          rw [if_pos rfl] at this
          exact this
        · rw [if_neg hv0, Finset.range_add_one, Finset.filter_insert]
          by_cases hveq : w = v
          · subst hveq
            rw [Array.getElem_setIfInBounds_self, if_pos rfl,
              Finset.sum_insert (by simp),
              toPoint_add (ihn.2.1 w hwlt) (hval n (by omega))]
            have hprev := ihn.2.2 w hwlt
            rw [if_neg hw] at hprev
            rw [hprev]
            exact add_comm _ _
          · rw [Array.getElem_setIfInBounds_ne (by omega : v < bs.size) hveq, if_neg hveq,
              show bs[v] = bs[v]! from (getElem!_pos bs v (by omega)).symm]
            have := ihn.2.2 v hv
            rw [if_neg hv0] at this
            exact this
    · rw [hstep, if_neg hw]
      replace hw : windowVal scalars[n]! k = 0 := not_ne_iff.mp hw
      refine ⟨ihn.1, ihn.2.1, fun v hv => ?_⟩
      by_cases hv0 : v = 0
      · subst hv0
        rw [if_pos rfl]
        have := ihn.2.2 0 hv
        rw [if_pos rfl] at this
        exact this
      · rw [if_neg hv0, Finset.range_add_one, Finset.filter_insert,
          if_neg (fun h => hv0 (by rw [← h, hw]))]
        have := ihn.2.2 v hv
        rw [if_neg hv0] at this
        exact this

/-- Prefix of the running-sum fold, for the suffix-sum induction. -/
private def msmRunningT (bs : Array G1) (t : Nat) : MProd G1 G1 :=
  (List.range' 0 t).foldl (fun rp vv =>
    ⟨add rp.1 (add rp.2 bs[1 <<< 8 - 1 - vv]!),
     add rp.2 bs[1 <<< 8 - 1 - vv]!⟩) ⟨zero, zero⟩

private theorem msmRunning_eq_T (bs : Array G1) :
    msmRunning bs = msmRunningT bs (1 <<< 8 - 1) := rfl

/-- The running-sum invariant: after `t` iterations the second
component is the plain suffix sum and the first the weighted one. -/
private theorem msmRunningT_spec (bs : Array G1)
    (hval : ∀ v, v < 1 <<< 8 → Valid bs[v]!) :
    ∀ t, t ≤ 1 <<< 8 - 1 →
      Valid (msmRunningT bs t).1 ∧ Valid (msmRunningT bs t).2
      ∧ toPoint (msmRunningT bs t).2
          = ∑ v ∈ Ico (1 <<< 8 - t) (1 <<< 8), toPoint bs[v]!
      ∧ toPoint (msmRunningT bs t).1
          = ∑ v ∈ Ico (1 <<< 8 - t) (1 <<< 8),
              (v - (1 <<< 8 - 1 - t)) • toPoint bs[v]! := by
  intro t
  induction t with
  | zero =>
    intro _
    have hico : Ico (1 <<< 8 - 0) (1 <<< 8) = ∅ := by
      rw [Nat.sub_zero]
      exact Finset.Ico_self _
    rw [show msmRunningT bs 0 = ⟨zero, zero⟩ from rfl]
    refine ⟨valid_zero, valid_zero, ?_, ?_⟩ <;>
      rw [hico, Finset.sum_empty] <;> exact toPoint_zero
  | succ t ih =>
    intro ht
    obtain ⟨ihv1, ihv2, ihr, ihp⟩ := ih (by omega)
    have hstep : msmRunningT bs (t + 1)
        = ⟨add (msmRunningT bs t).1
            (add (msmRunningT bs t).2 bs[1 <<< 8 - 1 - t]!),
           add (msmRunningT bs t).2 bs[1 <<< 8 - 1 - t]!⟩ := by
      rw [msmRunningT, msmRunningT, List.range'_1_concat, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      simp only [Nat.zero_add]
    have hvb : Valid bs[1 <<< 8 - 1 - t]! := hval _ (by omega)
    have hvr : Valid (add (msmRunningT bs t).2 bs[1 <<< 8 - 1 - t]!) :=
      valid_add ihv2 hvb
    -- the new suffix sum (second component)
    have hr' : toPoint (add (msmRunningT bs t).2 bs[1 <<< 8 - 1 - t]!)
        = ∑ v ∈ Ico (1 <<< 8 - (t + 1)) (1 <<< 8), toPoint bs[v]! := by
      rw [toPoint_add ihv2 hvb, ihr,
        Finset.sum_eq_sum_Ico_succ_bot
          (by omega : 1 <<< 8 - (t + 1) < 1 <<< 8)
          (fun v => toPoint bs[v]!),
        show 1 <<< 8 - (t + 1) + 1 = 1 <<< 8 - t by omega,
        show (1 : Nat) <<< 8 - (t + 1) = 1 <<< 8 - 1 - t from by omega]
      apply add_comm
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hstep]
      exact valid_add ihv1 hvr
    · rw [hstep]
      exact hvr
    · rw [hstep]
      exact hr'
    · rw [hstep]
      show toPoint (add (msmRunningT bs t).1 _) = _
      rw [toPoint_add ihv1 hvr, ihp, hr']
      -- Σ (v − c)•b + Σ b = Σ (v − (c−1))•b over the extended interval
      rw [Finset.sum_eq_sum_Ico_succ_bot
          (by omega : 1 <<< 8 - (t + 1) < 1 <<< 8)
          (fun v => (v - (1 <<< 8 - 1 - (t + 1))) • toPoint bs[v]!),
        show 1 <<< 8 - (t + 1) + 1 = 1 <<< 8 - t by omega,
        show 1 <<< 8 - (t + 1) - (1 <<< 8 - 1 - (t + 1)) = 1 by omega,
        one_nsmul]
      have hcongr : ∀ v ∈ Ico (1 <<< 8 - t) (1 <<< 8),
          (v - (1 <<< 8 - 1 - (t + 1))) • toPoint bs[v]!
            = (v - (1 <<< 8 - 1 - t)) • toPoint bs[v]! + toPoint bs[v]! := by
        intro v hv
        have hv' := Finset.mem_Ico.mp hv
        rw [show v - (1 <<< 8 - 1 - (t + 1)) = (v - (1 <<< 8 - 1 - t)) + 1
          by omega, add_nsmul, one_nsmul]
      rw [show ∑ k ∈ Ico (1 <<< 8 - t) (1 <<< 8),
            (k - (1 <<< 8 - 1 - (t + 1))) • toPoint bs[k]!
          = ∑ v ∈ Ico (1 <<< 8 - t) (1 <<< 8),
              ((v - (1 <<< 8 - 1 - t)) • toPoint bs[v]! + toPoint bs[v]!)
          from Finset.sum_congr rfl hcongr,
        Finset.sum_add_distrib,
        Finset.sum_eq_sum_Ico_succ_bot
          (by omega : 1 <<< 8 - (t + 1) < 1 <<< 8) (fun v => toPoint bs[v]!),
        show 1 <<< 8 - (t + 1) + 1 = 1 <<< 8 - t by omega]
      apply add_left_comm

/-- The running-sum fold computes `Σ_v v·b_v` (first component). -/
private theorem msmRunning_spec (bs : Array G1)
    (hval : ∀ v, v < 1 <<< 8 → Valid bs[v]!) :
    Valid (msmRunning bs).1
    ∧ toPoint (msmRunning bs).1
        = ∑ v ∈ range (1 <<< 8), v • toPoint bs[v]! := by
  obtain ⟨hv1, _, _, hp⟩ :=
    msmRunningT_spec bs hval (1 <<< 8 - 1) (Nat.le_refl _)
  refine ⟨by rw [msmRunning_eq_T]; exact hv1, ?_⟩
  rw [msmRunning_eq_T, hp,
    show (1 : Nat) <<< 8 - (1 <<< 8 - 1) = 1 from by omega,
    show (1 : Nat) <<< 8 - 1 - (1 <<< 8 - 1) = 0 from by omega,
    Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (by omega : (0 : Nat) < 1 <<< 8)
      (fun v => v • toPoint bs[v]!),
    zero_nsmul, zero_add]
  exact Finset.sum_congr rfl fun v hv => by rw [Nat.sub_zero]

private theorem windowVal_lt (s : Fr) (k : Nat) : windowVal s k < 1 <<< 8 := by
  have := Nat.and_le_right (n := s.val >>> (k * 8)) (m := 1 <<< 8 - 1)
  rw [windowVal]
  omega

/-- Buckets + running sums compute the window-weighted point sum. -/
private theorem window_sum (points : Array G1) (scalars : Array Fr)
    (n k : Nat) (hval : ∀ j, j < n → Valid points[j]!) :
    Valid (msmRunning (msmBuckets points scalars n k)).1
    ∧ toPoint (msmRunning (msmBuckets points scalars n k)).1
        = ∑ j ∈ range n, windowVal scalars[j]! k • toPoint points[j]! := by
  obtain ⟨hbsz, hbval, hbsum⟩ := msmBuckets_spec points scalars n k hval
  obtain ⟨hrv, hrsum⟩ := msmRunning_spec _ hbval
  refine ⟨hrv, ?_⟩
  rw [hrsum]
  have h1 : ∀ v ∈ range (1 <<< 8),
      v • toPoint (msmBuckets points scalars n k)[v]!
        = ∑ j ∈ (range n).filter (fun j => windowVal scalars[j]! k = v),
            windowVal scalars[j]! k • toPoint points[j]! := by
    intro v hv
    rw [hbsum v (Finset.mem_range.mp hv)]
    by_cases hv0 : v = 0
    · subst hv0
      rw [if_pos rfl, zero_nsmul]
      exact (Finset.sum_eq_zero fun j hj => by
        rw [(Finset.mem_filter.mp hj).2, zero_nsmul]).symm
    · rw [if_neg hv0, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j hj => by
        rw [(Finset.mem_filter.mp hj).2]
  have h2 := Finset.sum_congr rfl h1
  rw [h2]
  exact Finset.sum_fiberwise_of_maps_to
    (fun j _ => Finset.mem_range.mpr (windowVal_lt scalars[j]! k)) _

/-- Prefix of the outer window fold. -/
private def msmAcc (points : Array G1) (scalars : Array Fr)
    (n nW t : Nat) : G1 :=
  (List.range' 0 t).foldl (msmWindowStep points scalars n nW) zero

/-- The window-recomposition invariant: after `t` windows, the
accumulator holds `Σ_j (sⱼ >>> ((nW − t)·8)) · Pⱼ`. -/
private theorem msmAcc_spec (points : Array G1) (scalars : Array Fr)
    (n nW : Nat) (hval : ∀ j, j < n → Valid points[j]!)
    (hbound : ∀ j, j < n → scalars[j]!.val < 2 ^ (nW * 8)) :
    ∀ t, t ≤ nW →
      Valid (msmAcc points scalars n nW t)
      ∧ toPoint (msmAcc points scalars n nW t)
          = ∑ j ∈ range n,
              (scalars[j]!.val >>> ((nW - t) * 8)) • toPoint points[j]! := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨valid_zero, ?_⟩
    rw [show toPoint (msmAcc points scalars n nW 0) = 0 from toPoint_zero,
      Nat.sub_zero]
    exact (Finset.sum_eq_zero fun j hj => by
      rw [Nat.shiftRight_eq_zero _ _ (hbound j (Finset.mem_range.mp hj)),
        zero_nsmul]).symm
  | succ t ih =>
    intro ht
    obtain ⟨ihv, ihsum⟩ := ih (by omega)
    have hstep : msmAcc points scalars n nW (t + 1)
        = msmWindowStep points scalars n nW (msmAcc points scalars n nW t)
            t := by
      rw [msmAcc, msmAcc, List.range'_1_concat, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      simp only [Nat.zero_add]
    obtain ⟨hwv, hwsum⟩ := window_sum points scalars n (nW - 1 - t) hval
    -- merging one window into the accumulated shifts
    have hmerge : (2 ^ 8)
          • (∑ j ∈ range n,
              (scalars[j]!.val >>> ((nW - t) * 8)) • toPoint points[j]!)
        + ∑ j ∈ range n,
            windowVal scalars[j]! (nW - 1 - t) • toPoint points[j]!
        = ∑ j ∈ range n,
            (scalars[j]!.val >>> ((nW - (t + 1)) * 8)) • toPoint points[j]!
        := by
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [← mul_nsmul', ← add_nsmul]
      congr 1
      have hsw := shift_window scalars[j]!.val ((nW - 1 - t) * 8)
      rw [show ((nW - 1 - t) * 8 + 8) = (nW - t) * 8 from by omega] at hsw
      rw [windowVal, show (nW - (t + 1)) * 8 = (nW - 1 - t) * 8 from by omega]
      omega
    rw [hstep, msmWindowStep]
    by_cases hd : nW - 1 - t + 1 < nW
    · rw [if_pos hd]
      obtain ⟨hdv, hdsum⟩ := doubleFold_spec ihv 8
      refine ⟨valid_add hdv hwv, ?_⟩
      rw [toPoint_add hdv hwv, hdsum, ihsum, hwsum]
      exact hmerge
    · rw [if_neg hd]
      have ht0 : t = 0 := by omega
      subst ht0
      refine ⟨valid_add ihv hwv, ?_⟩
      rw [toPoint_add ihv hwv, ihsum, hwsum]
      have hzero : ∑ j ∈ range n,
          (scalars[j]!.val >>> ((nW - 0) * 8)) • toPoint points[j]! = 0 :=
        Finset.sum_eq_zero fun j hj => by
          rw [Nat.shiftRight_eq_zero _ _ (by
            rw [Nat.sub_zero]
            exact hbound j (Finset.mem_range.mp hj)), zero_nsmul]
      rw [hzero, zero_add]
      refine Finset.sum_congr rfl fun j hj => ?_
      congr 1
      have hsw := shift_window scalars[j]!.val ((nW - 1 - 0) * 8)
      have h0 : scalars[j]!.val >>> ((nW - 1 - 0) * 8 + 8) = 0 := by
        rw [show (nW - 1 - 0) * 8 + 8 = nW * 8 from by omega]
        exact Nat.shiftRight_eq_zero _ _ (hbound j (Finset.mem_range.mp hj))
      rw [windowVal, show (nW - (0 + 1)) * 8 = (nW - 1 - 0) * 8 from by omega]
      omega

/-- **Correctness of the spec's Pippenger MSM**: for valid points,
`msm` computes `Σ_j [scalars[j]] points[j]` in the curve group. -/
theorem toPoint_msm (points : Array G1) (scalars : Array Fr)
    (hval : ∀ j, j < (if points.size ≤ scalars.size then points.size
      else scalars.size) → Valid points[j]!) :
    Valid (msm points scalars)
    ∧ toPoint (msm points scalars)
        = ∑ j ∈ range (if points.size ≤ scalars.size then points.size
            else scalars.size),
            (scalars[j]!).val • toPoint points[j]! := by
  rw [msm_eq_msmModel]
  unfold msmModel
  by_cases h0 : (if points.size ≤ scalars.size then points.size
      else scalars.size) = 0
  · rw [if_pos h0, h0]
    exact ⟨valid_zero, by rw [toPoint_zero, Finset.range_zero,
      Finset.sum_empty]⟩
  · rw [if_neg h0]
    by_cases h1 : msmMaxBits scalars (if points.size ≤ scalars.size
        then points.size else scalars.size) = 0
    · rw [if_pos h1]
      refine ⟨valid_zero, ?_⟩
      rw [toPoint_zero]
      refine (Finset.sum_eq_zero fun j hj => ?_).symm
      have hb := msmMaxBits_bound scalars _ j (Finset.mem_range.mp hj)
      rw [h1, pow_zero] at hb
      rw [show (scalars[j]!).val = 0 from by omega, zero_nsmul]
    · rw [if_neg h1]
      have hbound : ∀ j, j < (if points.size ≤ scalars.size
          then points.size else scalars.size) →
          scalars[j]!.val < 2 ^ (((msmMaxBits scalars
            (if points.size ≤ scalars.size then points.size
              else scalars.size) + 8 - 1) / 8) * 8) := by
        intro j hj
        refine Nat.lt_of_lt_of_le (msmMaxBits_bound scalars _ j hj) ?_
        exact Nat.pow_le_pow_right (by omega) (by omega)
      obtain ⟨hv, hsum⟩ := msmAcc_spec points scalars _ _ hval hbound _
        (Nat.le_refl _)
      refine ⟨hv, ?_⟩
      rw [show toPoint ((List.range' 0 ((msmMaxBits scalars
          (if points.size ≤ scalars.size then points.size
            else scalars.size) + 8 - 1) / 8)).foldl
          (msmWindowStep points scalars _ _) zero) = toPoint (msmAcc points
            scalars _ ((msmMaxBits scalars (if points.size ≤ scalars.size
              then points.size else scalars.size) + 8 - 1) / 8) _)
        from rfl, hsum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Nat.sub_self, Nat.zero_mul, Nat.shiftRight_zero]

end EthCryptographySpecs.Bls.G1
