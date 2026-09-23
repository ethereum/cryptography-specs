import EthCryptographySpecs.Xmss.TweakHash
import EthCryptographySpecs.Proofs.Xmss.Blake2s

/-!
# Proofs: `Xmss.TweakHash`

Properties of the tweak encoding.
-/

namespace EthCryptographySpecs.Xmss

open EthCryptographySpecs.Xmss.Constants

/-! ## Domain separation -/

/-- Distinct call sites are assigned distinct bytes. -/
theorem toByte_injective : Function.Injective TweakType.toByte := by
  -- Sixty-four pairs, each settled by comparing two literals.
  intro a b h
  cases a <;> cases b <;> simp_all [TweakType.toByte]

/-- No two distinct call sites, sub-positions or indices share a tweak.

Sharing one would put two call sites back into a single hash function. -/
theorem makeTweak_injective {t₁ t₂ : TweakType} {p₁ p₂ j₁ j₂ : UInt32}
    (h : makeTweak t₁ p₁ j₁ = makeTweak t₂ p₂ j₂) :
    t₁ = t₂ ∧ p₁ = p₂ ∧ j₁ = j₂ := by
  -- Fixed widths, so the four pieces peel apart from the outside in.
  obtain ⟨hInner, hIndex⟩ := Vector.append_inj h
  obtain ⟨hOuter, _⟩ := Vector.append_inj hInner
  obtain ⟨hHead, hSub⟩ := Vector.append_inj hOuter
  refine ⟨?_, Blake2s.wordBytes_injective hSub,
    Blake2s.wordBytes_injective hIndex⟩
  -- Byte one of the head is the call site.
  have hByte := congrArg (fun v : Vector UInt8 4 => v[1]) hHead
  simp only at hByte
  exact toByte_injective hByte

/-- Distinct call sites give distinct tweaks, whatever their positions. -/
theorem makeTweak_ne_of_type_ne {t₁ t₂ : TweakType} {p₁ p₂ j₁ j₂ : UInt32}
    (h : t₁ ≠ t₂) : makeTweak t₁ p₁ j₁ ≠ makeTweak t₂ p₂ j₂ :=
  fun heq => h (makeTweak_injective heq).left

/-! ## Chain positions

The chain call site packs two numbers into one tweak field.

Separating chain steps therefore needs the packing to be injective as well. -/

/-- Positions stay inside the tweak's 32-bit field, so none is truncated. -/
theorem chainPosition_no_overflow (chain : Fin V) (step : Fin CHAIN_LENGTH) :
    CHAIN_LENGTH * chain.val + step.val < 2 ^ 32 := by
  -- The largest position is 8 * 41 + 7, far below the field's range.
  have hc := chain.isLt
  have hs := step.isLt
  simp only [V, CHAIN_LENGTH, W] at hc hs ⊢
  omega

/-- Distinct chain steps take distinct positions. -/
theorem chainPosition_injective {c₁ c₂ : Fin V} {s₁ s₂ : Fin CHAIN_LENGTH}
    (h : chainPosition c₁ s₁ = chainPosition c₂ s₂) : c₁ = c₂ ∧ s₁ = s₂ := by
  -- Compare the underlying numbers, which the conversion leaves untouched.
  have hnat := congrArg UInt32.toNat h
  simp only [chainPosition, UInt32.toNat_ofNat'] at hnat
  have hc₁ := c₁.isLt; have hc₂ := c₂.isLt
  have hs₁ := s₁.isLt; have hs₂ := s₂.isLt
  simp only [V, CHAIN_LENGTH, W] at hc₁ hc₂ hs₁ hs₂ hnat
  -- A step below 8 cannot carry into the chain's block.
  refine ⟨Fin.val_inj.mp ?_, Fin.val_inj.mp ?_⟩ <;> omega

/-- Two different chain steps never share a tweak. -/
theorem makeTweak_chain_injective {c₁ c₂ : Fin V} {s₁ s₂ : Fin CHAIN_LENGTH}
    {ep₁ ep₂ : UInt32}
    (h : makeTweak .chain (chainPosition c₁ s₁) ep₁
      = makeTweak .chain (chainPosition c₂ s₂) ep₂) :
    c₁ = c₂ ∧ s₁ = s₂ ∧ ep₁ = ep₂ := by
  -- The tweak separates the fields, and the packing separates the two numbers.
  obtain ⟨_, hpos, hep⟩ := makeTweak_injective h
  obtain ⟨hc, hs⟩ := chainPosition_injective hpos
  exact ⟨hc, hs, hep⟩

/-! ## Byte layout

These fail if a field moves, changes width, or changes endianness. -/

/-- A chain-step tweak lays out as the specification prescribes. -/
theorem makeTweak_chain_3_5 :
    (makeTweak .chain 3 5).toArray =
      #[0, 1, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0] := by
  decide +kernel

/-- The public-parameter tweak is its call-site byte and nothing else. -/
theorem makeTweak_parameter :
    (makeTweak .parameter 0 0).toArray =
      #[0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

end EthCryptographySpecs.Xmss
