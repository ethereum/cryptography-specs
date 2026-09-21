import EthCryptographySpecs.Xmss.Tweak
import EthCryptographySpecs.Proofs.Xmss.Blake2s

/-!
# Proofs: `Xmss.Tweak`

Properties of the tweak encoding.
-/

namespace EthCryptographySpecs.Xmss

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
      #[0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

end EthCryptographySpecs.Xmss
