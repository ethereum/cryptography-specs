module

public import EthLib.Consensus.Proofs.Accessors.DrawRandomOracle
public import EthLib.Consensus.Proofs.Transition.Totality.SyncCommittee

/-!
# Proofs: a balance-weighted search ends with high probability in the random oracle model

The search of a balance-weighted selection draws candidates until it has its members.

Its draw counter has 64 bits, so it fails when it runs out of draw numbers first.

A validator at the cap is always accepted, so with one the search ends within a pass per member.

Without one, whether the search ends depends on the hash of its draws.

Here a random oracle answers that hash, and the cache holds no draw input of the seed.

A draw then accepts any balance at most the cap with probability at least `2^-b`.

Here `b` is the number of random bits that a draw reads: 8 before Electra, 16 from Electra.

So for `n` members, the search fails with probability at most `n * (1 - 2^-b)^⌊(2^64 - 1) / n⌋`.

For at most `2^32` members, that is at most `2^-128`.

The bounds hold for the oracle only; no theorem bounds the search when SHA-256 answers.

The seed, the candidates, their balances and their order are fixed before the draws are answered.

The bound holds for every order, so the shuffle that gives it is not modelled.
-/

@[expose] public section

namespace EthLib.Consensus

open Base OracleComp OracleSpec ENNReal

/-- The number of random bits that one draw reads: 16 from Electra, 8 before. -/
def drawBits (fork : Base.Fork) : Nat :=
  if .pectra ≤ fork then 16 else 8

/-- The search of a balance-weighted selection, with the verdict of each draw given.

Draw `i` reads the candidate at position `order (i mod n)`, among `n` candidates.

A verdict that is an error stops the search with that error.

The draw counter is a 64-bit integer, so the search fails when it would reach `2^64`. -/
def searchOfVerdicts (verdict : Nat → Except AccessorError Bool) (indices : Array ValidatorIndex)
    (order : Nat → Nat) (size : Nat) (selected : Array ValidatorIndex)
    (bound : selected.size ≤ size) (i : Nat) :
    Except AccessorError (Vector ValidatorIndex size) :=
  if full : selected.size = size then .ok ⟨selected, full⟩
  else do
    let position := order (i % indices.size)
    let accepted ← verdict i
    let next : { next : Array ValidatorIndex // next.size ≤ size } :=
      if accepted then ⟨selected.push (indices.getD position 0), by simp; omega⟩
      else ⟨selected, bound⟩
    if i + 1 < 2 ^ 64 then searchOfVerdicts verdict indices order size next.1 next.2 (i + 1)
    else throw (.arith .overflow)
termination_by 2 ^ 64 - i

/-- The search of a balance-weighted selection is the search on the verdicts of its draws.

Draw `i` weighs the balance at position `order (i mod n)`, among `n` candidates. -/
theorem balanceWeightedSearch_eq_searchOfVerdicts (preset : Preset) (fork : Base.Fork)
    (indices : Array ValidatorIndex) (balances : Array Gwei) (order : Nat → Nat)
    (seed : Bytes32) (size : Nat) (selected : Array ValidatorIndex) (bound : selected.size ≤ size)
    (i : Nat) (random : { random // random = drawHash fork seed i }) :
    balanceWeightedSearch preset fork indices balances order seed size selected bound i random =
      searchOfVerdicts (fun j => proposerDraw preset fork seed j
        (balances.getD (order (j % indices.size)) 0)) indices order size selected bound i := by
  suffices key : ∀ left, ∀ {selected : Array ValidatorIndex} {bound : selected.size ≤ size}
      {i : Nat} {random : { random // random = drawHash fork seed i }}, left = 2 ^ 64 - i →
      balanceWeightedSearch preset fork indices balances order seed size selected bound i random =
        searchOfVerdicts (fun j => proposerDraw preset fork seed j
          (balances.getD (order (j % indices.size)) 0)) indices order size selected bound i from
    key _ rfl
  intro left
  induction left using Nat.strongRecOn with
  | _ left ih =>
  intro selected bound i random leftEq
  rw [balanceWeightedSearch, searchOfVerdicts]
  by_cases full : selected.size = size
  · rw [dite_eq_left full, dite_eq_left full]
  rw [dite_eq_right full, dite_eq_right full]
  obtain ⟨random, rfl⟩ := random
  simp only [proposerDraw]
  cases drawAccepts preset fork (drawHash fork seed i) i
    (balances.getD (order (i % indices.size)) 0) with
  | error e => rfl
  | ok accepted =>
    simp only [bind, Except.bind]
    by_cases iLt : i + 1 < 2 ^ 64
    · simp only [iLt, ↓reduceIte]
      exact ih _ (leftEq ▸ Nat.sub_lt_sub_left (by omega) (Nat.lt_succ_self i)) rfl
    · simp only [iLt, ↓reduceIte]

/-- The search of a balance-weighted selection, with its hash calls exposed to a shared oracle.

It makes the `2^64` draws of the seed up front, then searches on their verdicts.

The search reads only the draws it needs, so its outcome does not depend on the others.

The cache afterwards holds them all.

Draw `i` weighs the balance at position `order (i mod n)`, among `n` candidates. -/
def querySearch (preset : Preset) (fork : Base.Fork) (indices : Array ValidatorIndex)
    (balances : Array Gwei) (order : Nat → Nat) (seed : Bytes32) (size : Nat) :
    OracleComp (ByteArray →ₒ Bytes32) (Except AccessorError (Vector ValidatorIndex size)) :=
  (fun draws => searchOfVerdicts (fun i => draws.getD i (.ok false)) indices order size #[]
      (Nat.zero_le _) 0) <$>
    queryDraws preset fork seed (fun i => balances.getD (order (i % indices.size)) 0) (2 ^ 64)

/-- The search reads only the verdicts from its current draw number up to `2^64`. -/
private theorem searchOfVerdicts_congr {verdict other : Nat → Except AccessorError Bool}
    {indices : Array ValidatorIndex} {order : Nat → Nat} {size : Nat} :
    ∀ left, ∀ {selected : Array ValidatorIndex} {bound : selected.size ≤ size} {i : Nat},
      left = 2 ^ 64 - i → i < 2 ^ 64 → (∀ j, i ≤ j → j < 2 ^ 64 → verdict j = other j) →
      searchOfVerdicts verdict indices order size selected bound i =
        searchOfVerdicts other indices order size selected bound i := by
  intro left
  induction left using Nat.strongRecOn with
  | _ left ih =>
  intro selected bound i leftEq small same
  rw [searchOfVerdicts, searchOfVerdicts]
  by_cases full : selected.size = size
  · rw [dite_eq_left full, dite_eq_left full]
  rw [dite_eq_right full, dite_eq_right full, same i le_rfl small]
  cases other i with
  | error e => rfl
  | ok accepted =>
    simp only [bind, Except.bind]
    by_cases iLt : i + 1 < 2 ^ 64
    · simp only [iLt, ↓reduceIte]
      exact ih _ (leftEq ▸ Nat.sub_lt_sub_left (by omega) (Nat.lt_succ_self i)) rfl iLt
        fun j low high => same j (by omega) high
    · simp only [iLt, ↓reduceIte]

/-- Entry `j` of the mapped range of length `n` is the image of `j`, for `j < n`. -/
private theorem getD_map_range {α : Type} (f : Nat → α) (d : α) {n j : Nat} (small : j < n) :
    ((List.range n).map f).getD j d = f j := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range small]

/-- Answering the exposed hash calls with SHA-256 gives the specified search. -/
theorem evalWithAnswerFn_querySearch (preset : Preset) (fork : Base.Fork)
    (indices : Array ValidatorIndex) (balances : Array Gwei) (order : Nat → Nat)
    (seed : Bytes32) (size : Nat) :
    evalWithAnswerFn (QueryImpl.ofFn Cryptography.Hash.Sha256.hash32)
      (querySearch preset fork indices balances order seed size) =
      balanceWeightedSearch preset fork indices balances order seed size #[] (Nat.zero_le _) 0
        ⟨drawHash fork seed 0, rfl⟩ := by
  rw [balanceWeightedSearch_eq_searchOfVerdicts, querySearch, map_eq_bind_pure_comp,
    evalWithAnswerFn_bind, evalWithAnswerFn_queryDraws]
  simp only [Function.comp_apply, evalWithAnswerFn_pure]
  exact searchOfVerdicts_congr _ rfl (Nat.two_pow_pos 64) fun j _ small => getD_map_range _ _ small

/-- The search succeeds when each window not yet filled accepts a draw at or after the current one.

Window `w` holds the draw numbers from `w * width` up to `(w + 1) * width`, excluded, below `2^64`.

Every verdict below `2^64` must be given rather than fail. -/
private theorem searchOfVerdicts_isOk_of_windows {verdict : Nat → Except AccessorError Bool}
    {indices : Array ValidatorIndex} {order : Nat → Nat} {size width : Nat}
    (room : size * width < 2 ^ 64) (given : ∀ j < 2 ^ 64, ∃ b, verdict j = .ok b) :
    ∀ left, ∀ {selected : Array ValidatorIndex} {bound : selected.size ≤ size} {i : Nat},
      left = 2 ^ 64 - i →
      (∀ w, selected.size ≤ w → w < size →
        ∃ j, i ≤ j ∧ w * width ≤ j ∧ j < (w + 1) * width ∧ verdict j = .ok true) →
      (searchOfVerdicts verdict indices order size selected bound i).isOk = true := by
  intro left
  induction left using Nat.strongRecOn with
  | _ left ih =>
  intro selected bound i leftEq windows
  rw [searchOfVerdicts]
  by_cases full : selected.size = size
  · rw [dite_eq_left full]
    rfl
  rw [dite_eq_right full]
  -- The last window has an acceptance ahead, so the counter does not run out at this draw.
  obtain ⟨last, iLast, -, lastLt, -⟩ := windows (size - 1) (by omega) (by omega)
  rw [Nat.sub_add_cancel (by omega)] at lastLt
  have iLt : i + 1 < 2 ^ 64 := by omega
  obtain ⟨b, verdictI⟩ := given i (by omega)
  rw [verdictI]
  simp only [bind, Except.bind, iLt, ↓reduceIte]
  refine ih _ (leftEq ▸ Nat.sub_lt_sub_left (by omega) (Nat.lt_succ_self i)) rfl ?_
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    intro w low high
    obtain ⟨j, ij, wl, wh, accepts⟩ := windows w low high
    have apart : j ≠ i := by
      rintro rfl
      rw [verdictI] at accepts
      cases accepts
    exact ⟨j, by omega, wl, wh, accepts⟩
  · simp only [↓reduceIte, Array.size_push]
    intro w low high
    obtain ⟨j, ij, wl, wh, accepts⟩ := windows w (by omega) high
    obtain ⟨k, ik, -, kh, -⟩ := windows selected.size le_rfl (by omega)
    have later := Nat.mul_le_mul_right width low
    rw [Nat.succ_mul] at later kh
    exact ⟨j, by omega, wl, wh, accepts⟩

/-- A list of length `n` relates to the range of `n` when each entry relates to its index. -/
private theorem forall₂_range_iff {γ : Type} (P : Nat → γ → Prop) (d : γ) {n : Nat}
    {z : List γ} (length : z.length = n) :
    List.Forall₂ P (List.range n) z ↔ ∀ j < n, P j (z.getD j d) := by
  subst length
  rw [List.forall₂_iff_get]
  simp only [List.length_range, List.get_eq_getElem, List.getElem_range, true_and]
  constructor
  · intro h j small
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem small] using h j small small
  · intro h j small _
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem small] using h j small

/-- A draw on a uniform digest accepts a balance at most the cap with chance at least `2^-b`. -/
private theorem le_prEvent_drawAccepts {preset : Preset} {fork : Base.Fork}
    (fits : DrawFits preset fork) (positive : 0 < drawCap preset fork) (i : Nat) {e : Gwei}
    (capped : e.toNat ≤ drawCap preset fork) :
    (2 ^ drawBits fork : ℝ≥0∞)⁻¹ ≤
      Pr{let random ← $ᵗ Bytes32}[drawAccepts preset fork random i e = .ok true] := by
  unfold DrawFits at fits
  unfold drawCap at capped positive
  unfold drawBits
  by_cases electra : .pectra ≤ fork
  · rw [ite_eq_left electra] at fits capped positive ⊢
    rw [prEvent_drawAccepts_uniform_of_pectra preset fork electra i e positive capped fits,
      ← one_div]
    gcongr
    exact_mod_cast Nat.succ_pos _
  · rw [ite_eq_right electra] at fits capped positive ⊢
    rw [prEvent_drawAccepts_uniform_of_before_pectra preset fork electra i e positive capped fits,
      ← one_div]
    gcongr
    exact_mod_cast Nat.succ_pos _

/-- The search fails with probability at most `n * (1 - 2^-b)^⌊(2^64 - 1) / n⌋` for `n` members.

Here `b` is the number of random bits that a draw reads.

The last draw number cannot complete the search, so `2^64 - 1` draws count.

Split them into `n` windows of `⌊(2^64 - 1) / n⌋` draws.

Each draw accepts with probability at least `2^-b`, whatever the balance up to the cap.

The search ends when each window accepts once.

It needs a positive cap and at least one candidate.

Every balance read must be at most the cap, and the products of a draw must fit in 64 bits.

It also needs the cache to hold no draw input of the seed. -/
theorem prEvent_querySearch_fails_le (preset : Preset) (fork : Base.Fork)
    (fits : DrawFits preset fork) (positive : 0 < drawCap preset fork)
    (indices : Array ValidatorIndex) (balances : Array Gwei) (order : Nat → Nat)
    (seed : Bytes32) (size : Nat) (cache : (ByteArray →ₒ Bytes32).QueryCache)
    (nonempty : 0 < indices.size)
    (capped : ∀ j < indices.size, (balances.getD (order j) 0).toNat ≤ drawCap preset fork)
    (fresh : ∀ i < 2 ^ 64, cache (drawInput seed (i / drawsPerHash fork)) = none) :
    Pr{let z ← (simulateQ (ByteArray →ₒ Bytes32).randomOracle
      (querySearch preset fork indices balances order seed size)).run' cache}[z.isOk = false] ≤
      size * (1 - (2 ^ drawBits fork : ℝ≥0∞)⁻¹) ^ ((2 ^ 64 - 1) / size) := by
  rw [querySearch, simulateQ_map, StateT.run'_map', prEvent_map,
    (run_queryDraws_evalDistEq preset fork seed _ (2 ^ 64) cache le_rfl fresh).prEvent_eq]
  have bounded : ∀ i, (balances.getD (order (i % indices.size)) 0).toNat ≤ drawCap preset fork :=
    fun i => capped _ (Nat.mod_lt i nonempty)
  have room : size * ((2 ^ 64 - 1) / size) < 2 ^ 64 :=
    lt_of_le_of_lt (Nat.mul_div_le _ _) (Nat.sub_lt (Nat.two_pow_pos 64) Nat.one_pos)
  -- A failed search either meets a failed draw or a window of draws that all reject.
  refine le_trans (prEvent_mono _ _ (fun z =>
    ¬ List.Forall₂ (fun _ y => ∃ b, y = Except.ok b) (List.range (2 ^ 64)) z ∨
      ∃ w ∈ Finset.range size, List.Forall₂ (fun j (y : Except AccessorError Bool) =>
        w * ((2 ^ 64 - 1) / size) ≤ j → j < (w + 1) * ((2 ^ 64 - 1) / size) → y ≠ .ok true)
        (List.range (2 ^ 64)) z) ?_) ?_
  · intro z fails
    by_cases given : List.Forall₂ (fun _ y => ∃ b, y = Except.ok b) (List.range (2 ^ 64)) z
    · right
      have length : z.length = 2 ^ 64 := by simpa using given.length_eq.symm
      rw [forall₂_range_iff _ (.ok false) length] at given
      by_contra none
      push Not at none
      have succeeds := searchOfVerdicts_isOk_of_windows (indices := indices) (order := order)
        room given _ (selected := #[]) (bound := Nat.zero_le _) (i := 0) rfl (by
          intro w _ high
          have notAll := none w (Finset.mem_range.mpr high)
          rw [forall₂_range_iff _ (.ok false) length] at notAll
          push Not at notAll
          obtain ⟨j, -, low, up, accepts⟩ := notAll
          exact ⟨j, Nat.zero_le _, low, up, accepts⟩)
      rw [succeeds] at fails
      exact Bool.noConfusion fails
    · exact .inl given
  refine le_trans (prEvent_or_le _ _ _) ?_
  rw [prEvent_not_eq_one_sub, prEvent_mapM_forall₂, List.prod_eq_one, tsub_self, zero_add]
  · refine le_trans (prEvent_exists_finset_le _ _ _) ?_
    calc _ ≤ ∑ w ∈ Finset.range size,
          (1 - (2 ^ drawBits fork : ℝ≥0∞)⁻¹) ^ ((2 ^ 64 - 1) / size) :=
          Finset.sum_le_sum fun w small => ?_
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    -- Inside its window a draw rejects with chance at most `1 - 2^-b`, elsewhere at most one.
    rw [prEvent_mapM_forall₂, ← List.prod_toFinset _ List.nodup_range, List.toFinset_range]
    refine le_trans (Finset.prod_le_prod (g := fun j =>
      if j ∈ Finset.Ico (w * ((2 ^ 64 - 1) / size)) ((w + 1) * ((2 ^ 64 - 1) / size)) then
        1 - (2 ^ drawBits fork : ℝ≥0∞)⁻¹ else 1) fun j _ => ?_) ?_
    · split_ifs with inside
      · rw [Finset.mem_Ico] at inside
        rw [prEvent_map, prEvent_congr _ _ (fun random => ¬ drawAccepts preset fork random j
          (balances.getD (order (j % indices.size)) 0) = .ok true)
          (fun random => ⟨fun h => h inside.1 inside.2, fun h _ _ => h⟩), prEvent_not_eq_one_sub]
        exact tsub_le_tsub_left (le_prEvent_drawAccepts fits positive j (bounded j)) 1
      · exact prEvent_le_one _
    · have high : (w + 1) * ((2 ^ 64 - 1) / size) ≤ size * ((2 ^ 64 - 1) / size) :=
        Nat.mul_le_mul_right _ (Finset.mem_range.mp small)
      rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr ?_, Finset.prod_const, Nat.card_Ico,
        Nat.succ_mul, Nat.add_sub_cancel_left]
      intro j inside
      rw [Finset.mem_Ico] at inside
      rw [Finset.mem_range]
      omega
  · intro x mem
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp mem
    rw [prEvent_map]
    exact prEvent_eq_one_of_forall_mem_support _ _ fun random _ =>
      (drawAccepts_ok_of_le fits random j (bounded j)).imp fun _ h => h.1

/-- The bound for `n` members is at most `2^-128` for at most `2^32` members.

It needs windows of at least `2^24` draws, and at most 16 random bits per draw. -/
private theorem search_bound_le {size width b : Nat} (few : 2 ^ 24 ≤ width)
    (small : size ≤ 2 ^ 32) (bits : b ≤ 16) :
    (size : ℝ≥0∞) * (1 - (2 ^ b : ℝ≥0∞)⁻¹) ^ width ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  have twoPos : (0 : ℝ) < 2 ^ b := by positivity
  have reject : 0 ≤ 1 - ((2 : ℝ) ^ b)⁻¹ :=
    sub_nonneg.mpr (inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two))
  -- Both sides are images of real numbers.
  have left : (size : ℝ≥0∞) * (1 - (2 ^ b : ℝ≥0∞)⁻¹) ^ width =
      ENNReal.ofReal (size * (1 - ((2 : ℝ) ^ b)⁻¹) ^ width) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow reject, ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_inv_of_pos twoPos, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  have right : (2 ^ 128 : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((2 ^ 128 : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat]
  rw [left, right]
  refine ENNReal.ofReal_le_ofReal ?_
  -- A draw of at most 16 bits rejects at most as often as a draw of 16 bits.
  have fewer : 1 - ((2 : ℝ) ^ b)⁻¹ ≤ 1 - ((2 : ℝ) ^ 16)⁻¹ := by
    gcongr
    exact one_le_two
  have below : 1 - ((2 : ℝ) ^ 16)⁻¹ ≤ 1 := by
    have : (0 : ℝ) ≤ ((2 : ℝ) ^ 16)⁻¹ := by positivity
    linarith
  -- `2^16` draws of 16 bits all reject with chance at most `e^-1`, below `1/2`.
  have half : (1 - ((2 : ℝ) ^ 16)⁻¹) ^ 2 ^ 16 ≤ 1 / 2 := by
    have bound := Real.one_sub_div_pow_le_exp_neg (n := 2 ^ 16) (t := 1) (by norm_num)
    have grows := Real.add_one_le_exp 1
    rw [Real.exp_neg] at bound
    calc (1 - ((2 : ℝ) ^ 16)⁻¹) ^ 2 ^ 16 = (1 - 1 / ((2 ^ 16 : ℕ) : ℝ)) ^ 2 ^ 16 := by
          norm_num
      _ ≤ (Real.exp 1)⁻¹ := bound
      _ ≤ 1 / 2 := by
          rw [inv_eq_one_div]
          gcongr
          linarith
  have windows : (1 - ((2 : ℝ) ^ b)⁻¹) ^ width ≤ (1 / 2) ^ 2 ^ 8 :=
    calc (1 - ((2 : ℝ) ^ b)⁻¹) ^ width ≤ (1 - ((2 : ℝ) ^ 16)⁻¹) ^ width :=
          pow_le_pow_left₀ reject fewer _
      _ ≤ (1 - ((2 : ℝ) ^ 16)⁻¹) ^ (2 ^ 16 * 2 ^ 8) :=
          pow_le_pow_of_le_one (reject.trans fewer) below (by omega)
      _ = ((1 - ((2 : ℝ) ^ 16)⁻¹) ^ 2 ^ 16) ^ 2 ^ 8 := pow_mul _ _ _
      _ ≤ (1 / 2) ^ 2 ^ 8 := pow_le_pow_left₀ (pow_nonneg (reject.trans fewer) _) half _
  calc (size : ℝ) * (1 - ((2 : ℝ) ^ b)⁻¹) ^ width ≤ 2 ^ 32 * (1 / 2) ^ 2 ^ 8 :=
        mul_le_mul (by exact_mod_cast small) windows (pow_nonneg reject _) (by positivity)
    _ ≤ (2 ^ 128)⁻¹ := by norm_num

/-- A search of at most `2^32` members fails with probability at most `2^-128`.

The sync committee and the payload timeliness committee have 512 members on mainnet.

It needs the hypotheses of the bound for `n` members. -/
theorem prEvent_querySearch_fails_le_of_size_le (preset : Preset) (fork : Base.Fork)
    (fits : DrawFits preset fork) (positive : 0 < drawCap preset fork)
    (indices : Array ValidatorIndex) (balances : Array Gwei) (order : Nat → Nat)
    (seed : Bytes32) (size : Nat) (cache : (ByteArray →ₒ Bytes32).QueryCache)
    (nonempty : 0 < indices.size)
    (capped : ∀ j < indices.size, (balances.getD (order j) 0).toNat ≤ drawCap preset fork)
    (fresh : ∀ i < 2 ^ 64, cache (drawInput seed (i / drawsPerHash fork)) = none)
    (small : size ≤ 2 ^ 32) :
    Pr{let z ← (simulateQ (ByteArray →ₒ Bytes32).randomOracle
      (querySearch preset fork indices balances order seed size)).run' cache}[z.isOk = false] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  refine le_trans (prEvent_querySearch_fails_le preset fork fits positive indices balances order
    seed size cache nonempty capped fresh) ?_
  rcases Nat.eq_zero_or_pos size with empty | some
  · simp [empty]
  have few : 2 ^ 24 ≤ (2 ^ 64 - 1) / size := (Nat.le_div_iff_mul_le some).mpr (by omega)
  have bits : drawBits fork ≤ 16 := by unfold drawBits; split <;> omega
  exact search_bound_le few small bits

end EthLib.Consensus
