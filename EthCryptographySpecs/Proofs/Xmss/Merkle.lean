import EthCryptographySpecs.Xmss.Merkle

/-!
# Proofs: `Xmss.Merkle`

Correctness of the authentication path.
-/

namespace EthCryptographySpecs.Xmss

open EthCryptographySpecs.Xmss.Constants

variable {tp : TreeParams} {leaves : Nat → Digest} {level index l : Nat}

/-! ## Unfolding a node -/

/-- Outside the epoch range a node is a filler, whatever its level. -/
theorem node_of_not_covers (h : tp.covers level index = false) :
    tp.node leaves level index
      = fillerNode tp.publicParam tp.seed level index := by
  rw [TreeParams.node.eq_def, h]
  rfl

/-- The leaves are the nodes on level 0. -/
theorem node_zero (h : tp.covers 0 index = true) :
    tp.node leaves 0 index = leaves index := by
  rw [TreeParams.node.eq_def, h]
  rfl

/-- Every node above level 0 is the hash of its two children. -/
theorem node_succ (h : tp.covers (l + 1) index = true) :
    tp.node leaves (l + 1) index = merkleNode tp.publicParam (l + 1) index
      (tp.node leaves l (2 * index)) (tp.node leaves l (2 * index + 1)) := by
  rw [TreeParams.node.eq_def, h]
  rfl

/-! ## Indices -/

/-- Flipping the bottom bit, written as arithmetic. -/
private theorem xor_one (n : Nat) : n ^^^ 1 = 2 * (n / 2) + (1 - n % 2) := by
  -- The bits above the bottom one are untouched.
  have hd : (n ^^^ 1) / 2 = n / 2 := by rw [Nat.xor_div_two]; simp
  -- The bottom one is swapped.
  have hm : (n ^^^ 1) % 2 = 1 ↔ n % 2 = 0 := by simp
  have h1 := Nat.mod_two_eq_zero_or_one n
  have h2 := Nat.mod_two_eq_zero_or_one (n ^^^ 1)
  omega

/-- Sibling indices fit the tweak's 32-bit index field. -/
theorem siblingIndex_lt_size (epoch : Epoch) (level : Nat) :
    siblingIndex epoch.toNat level < UInt32.size := by
  -- Shifting only shrinks, so the path node is an epoch at most.
  have hs : epoch.toNat >>> level ≤ epoch.toNat := by
    simp only [Nat.shiftRight_eq_div_pow]
    exact Nat.div_le_self _ _
  have hlt := epoch.toNat_lt_size
  have := Nat.mod_two_eq_zero_or_one (epoch.toNat >>> level)
  simp only [siblingIndex, xor_one, UInt32.size] at hlt ⊢
  omega

/-- Shifting one bit further stays inside the range the key covers. -/
theorem covers_shiftRight (tp : TreeParams) (epoch : Epoch) (level : Nat)
    (h₁ : tp.epochStart.toNat ≤ epoch.toNat)
    (h₂ : epoch.toNat ≤ tp.epochEnd.toNat) :
    tp.covers level (epoch.toNat >>> level) = true := by
  -- Shifting is division, and division keeps the order of the three epochs.
  simp only [TreeParams.covers, Nat.shiftRight_eq_div_pow, Bool.and_eq_true,
    decide_eq_true_eq]
  exact ⟨Nat.div_le_div_right h₁, Nat.div_le_div_right h₂⟩

/-! ## The path reaches the root -/

/-- The verifier's node at `levels` is the signer's, all the way up. -/
theorem climbUpto_eq_node (tp : TreeParams) (leaves : Nat → Digest)
    (epoch : Epoch)
    (h₁ : tp.epochStart.toNat ≤ epoch.toNat)
    (h₂ : epoch.toNat ≤ tp.epochEnd.toNat) :
    ∀ (levels : Nat) (hl : levels ≤ LOG_LIFETIME),
      Internal.climbUpto tp.publicParam epoch.toNat (tp.authPath leaves epoch)
          levels hl (leaves epoch.toNat)
        = tp.node leaves levels (epoch.toNat >>> levels) := by
  intro levels
  induction levels with
  | zero =>
    intro _
    -- The verifier starts on the very leaf the signer's path starts on.
    rw [node_zero (covers_shiftRight tp epoch 0 h₁ h₂)]
    rfl
  | succ l ih =>
    intro hl
    -- Below the last step the two sides agree by the induction hypothesis.
    simp only [Internal.climbUpto, ih (by omega)]
    simp only [TreeParams.authPath, Vector.getElem_ofFn, Internal.climbStep,
      node_succ (covers_shiftRight tp epoch (l + 1) h₁ h₂)]
    have hhalf : epoch.toNat >>> (l + 1) = (epoch.toNat >>> l) / 2 :=
      Nat.shiftRight_succ _ _
    rcases Nat.mod_two_eq_zero_or_one (epoch.toNat >>> l) with hr | hr
    · -- Bit `l` is zero, so the path node is the left child.
      have hb : 2 * (epoch.toNat >>> (l + 1)) + 1
          = siblingIndex epoch.toNat l := by
        rw [hhalf]
        simp only [siblingIndex, xor_one]
        omega
      have ha : 2 * (epoch.toNat >>> (l + 1)) = epoch.toNat >>> l := by
        rw [hhalf]; omega
      rw [hb, ha]
      simp [hr]
    · -- Bit `l` is one, so the sibling is the left child.
      have hb : 2 * (epoch.toNat >>> (l + 1)) + 1 = epoch.toNat >>> l := by
        rw [hhalf]; omega
      have ha : 2 * (epoch.toNat >>> (l + 1))
          = siblingIndex epoch.toNat l := by
        rw [hhalf]
        simp only [siblingIndex, xor_one]
        omega
      rw [hb, ha]
      simp [hr]

/-- An honest authentication path leads from its leaf to the root. -/
theorem computeRoot_authPath (tp : TreeParams) (leaves : Nat → Digest)
    (epoch : Epoch)
    (h₁ : tp.epochStart.toNat ≤ epoch.toNat)
    (h₂ : epoch.toNat ≤ tp.epochEnd.toNat) :
    computeRoot tp.publicParam epoch (tp.authPath leaves epoch)
        (leaves epoch.toNat)
      = tp.root leaves := by
  rw [computeRoot, climbUpto_eq_node tp leaves epoch h₁ h₂, TreeParams.root]
  -- An epoch is 32 bits, so shifting all 32 away leaves the root's index 0.
  congr 1
  simp only [Nat.shiftRight_eq_div_pow, LOG_LIFETIME]
  exact Nat.div_eq_of_lt epoch.toNat_lt_size

/-! ## Known answer -/

/-- A key covering the three epochs 6 to 8. -/
private def exampleParams : TreeParams where
  publicParam := Vector.ofFn fun i => UInt8.ofNat i.val
  seed := Vector.ofFn fun i => UInt8.ofNat i.val
  epochStart := 6
  epochEnd := 8
  epochStart_le_epochEnd := by decide

/-- Leaves that repeat their own epoch, standing in for the one-time keys. -/
private def exampleLeaves (epoch : Nat) : Digest :=
  Vector.replicate DIGEST_LEN (UInt8.ofNat epoch)

/-- Pins the parent's call site and the order of its two children. -/
theorem merkleNode_known_answer :
    (merkleNode (Vector.ofFn fun i => UInt8.ofNat i.val) 5 9
      (Vector.replicate 16 0xaa) (Vector.replicate 16 0xbb)).toArray =
        #[0x6d, 0xa8, 0x11, 0x86, 0xf2, 0x04, 0x64, 0x73,
          0xea, 0x6a, 0x1d, 0x01, 0xe9, 0x12, 0xdb, 0xa4] := by
  decide +kernel

/-- Pins the filler's call site, decided by the seed alone. -/
theorem fillerNode_known_answer :
    (fillerNode (Vector.ofFn fun i => UInt8.ofNat i.val)
      (Vector.ofFn fun i => UInt8.ofNat i.val) 7 3).toArray =
        #[0x26, 0xc6, 0x14, 0xa6, 0x77, 0x45, 0x0a, 0x9f,
          0x05, 0x3b, 0x01, 0x1d, 0xc9, 0x29, 0x6a, 0xb5] := by
  decide +kernel

/-- Pins a subtree spanning epochs 4 to 7, of which the key covers 6 and 7.

The node under it spanning 4 and 5 is a filler, the two leaves below are not. -/
theorem node_known_answer :
    (exampleParams.node exampleLeaves 2 1).toArray =
        #[0xec, 0xa7, 0x59, 0x1f, 0xd7, 0x1a, 0x50, 0x4a,
          0xe8, 0xf1, 0x9d, 0x5a, 0x89, 0x3c, 0x5f, 0xd4] := by
  decide +kernel

end EthCryptographySpecs.Xmss
