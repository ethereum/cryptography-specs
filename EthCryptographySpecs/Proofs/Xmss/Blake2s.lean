import EthCryptographySpecs.Xmss.Blake2s
import Mathlib.Tactic
import Std.Tactic.BVDecide

/-!
# Proofs: `Xmss.Blake2s`

Machine-checked known answers for the BLAKE2s-256 specification.
-/

namespace EthCryptographySpecs.Xmss.Blake2s

/-! ## Structural properties -/

/-- Block processing always has at least one iteration.

This includes the empty message required by RFC 7693 Section 3.3.
-/
theorem blockCount_pos (length : Nat) : 0 < Internal.blockCount length := by
  -- The explicit lower bound makes the result positive for every length.
  simp only [Internal.blockCount]
  omega

/-- The final block's counter equals the complete message length. -/
theorem finalBlock_counter (length : Nat) :
    Internal.blockCounter length (Internal.blockCount length - 1) = length := by
  -- Expand ceiling division, the final offset, and the remaining-byte count.
  simp only [Internal.blockCounter, Internal.bytesInBlock, Internal.blockOffset,
    Internal.blockCount]
  -- Linear arithmetic with division by 64 closes both empty and nonempty cases.
  omega

/-- Every non-final block ends on its next 64-byte boundary. -/
theorem nonfinalBlock_counter (length block : Nat)
    (h : block + 1 < Internal.blockCount length) :
    Internal.blockCounter length block = (block + 1) * 64 := by
  -- A later block exists, so the current block must contain all 64 bytes.
  simp only [Internal.blockCounter, Internal.bytesInBlock, Internal.blockOffset,
    Internal.blockCount] at *
  omega

/-- A standard-domain final counter converts to 64 bits without truncation. -/
theorem finalBlock_counter_toNat (length : Nat) (h : length < 2 ^ 64) :
    (UInt64.ofNat
      (Internal.blockCounter length (Internal.blockCount length - 1))).toNat = length := by
  -- Block accounting first reduces the encoded counter to the message length.
  rw [finalBlock_counter]
  -- Conversion preserves every value inside the RFC's input-length domain.
  simp [UInt64.ofNat, UInt64.toNat, BitVec.toNat_ofNat]
  norm_num at h ⊢
  exact h

/-- Splitting and recombining a byte counter preserves all 64 bits. -/
theorem counter_words_recombine (counter : UInt64) :
    (Internal.counterLow counter).toUInt64
      ||| ((Internal.counterHigh counter).toUInt64 <<< 32) = counter := by
  -- Expose the two bit-vector slices to the decision procedure.
  simp only [Internal.counterLow, Internal.counterHigh]
  bv_decide

/-- Little-endian serialization followed by parsing returns the original word. -/
theorem little32_wordBytes (word : UInt32) :
    Internal.little32 ⟨(Internal.wordBytes word).toArray⟩ 0 = word := by
  -- Reduce the four in-bounds array reads to their corresponding byte slices.
  simp [Internal.little32, Internal.wordBytes, Array.getD]
  -- The four disjoint eight-bit slices cover the complete 32-bit word.
  bv_decide

/-- A word is recoverable from its little-endian bytes. -/
theorem wordBytes_injective : Function.Injective Internal.wordBytes := by
  intro a b hab
  -- Read the four bytes off both sides.
  have h0 := congrArg (fun v : Vector UInt8 4 => v[0]) hab
  have h1 := congrArg (fun v : Vector UInt8 4 => v[1]) hab
  have h2 := congrArg (fun v : Vector UInt8 4 => v[2]) hab
  have h3 := congrArg (fun v : Vector UInt8 4 => v[3]) hab
  simp [Internal.wordBytes] at h0 h1 h2 h3
  -- Each byte equation becomes one base-256 digit equation.
  have n0 := congrArg UInt8.toNat h0
  have n1 := congrArg UInt8.toNat h1
  have n2 := congrArg UInt8.toNat h2
  have n3 := congrArg UInt8.toNat h3
  simp [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight] at n0 n1 n2 n3
  refine UInt32.toNat_inj.mp ?_
  simp only [Nat.shiftRight_eq_div_pow] at n0 n1 n2 n3
  -- Four base-256 digits plus the 32-bit range leave one value.
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  omega

/-- Every message schedule row contains each index from 0 through 15 once. -/
theorem sigma_row_permutation (round : Fin 10) :
    (Internal.sigma[round.val]!).toList.Perm (List.range 16) := by
  -- Ten finite cases check the literal rows without trusting array indexing.
  fin_cases round <;> native_decide

/-! ## Known answers -/

/-- Hashing the empty byte string matches the standard digest. -/
theorem hash_empty : (hash ⟨#[]⟩).toArray = #[
    0x69, 0x21, 0x7a, 0x30, 0x79, 0x90, 0x80, 0x94,
    0xe1, 0x11, 0x21, 0xd0, 0x42, 0x35, 0x4a, 0x7c,
    0x1f, 0x55, 0xb6, 0x48, 0x2c, 0xa1, 0xa5, 0x1e,
    0x1b, 0x25, 0x0d, 0xfd, 0x1e, 0xd0, 0xee, 0xf9
  ] := by
  -- The native evaluator checks the closed computation.
  native_decide

/-- Hashing the RFC 7693 Appendix B message matches its standard digest. -/
theorem hash_abc : (hash ⟨#[0x61, 0x62, 0x63]⟩).toArray = #[
    0x50, 0x8c, 0x5e, 0x8c, 0x32, 0x7c, 0x14, 0xe2,
    0xe1, 0xa7, 0x2b, 0xa3, 0x4e, 0xeb, 0x45, 0x2f,
    0x37, 0x45, 0x8b, 0x20, 0x9e, 0xd6, 0x3a, 0x29,
    0x4d, 0x99, 0x9b, 0x4c, 0x86, 0x67, 0x59, 0x82
  ] := by
  -- The native evaluator checks the closed computation.
  native_decide

/-- Hashing one full block marks that data block as final. -/
theorem hash_one_full_block : (hash ⟨Array.replicate 64 0x61⟩).toArray = #[
    0x65, 0x1d, 0x2f, 0x5f, 0x20, 0x95, 0x2e, 0xac,
    0xae, 0xa2, 0xfb, 0xa2, 0xf2, 0xaf, 0x2b, 0xcd,
    0x63, 0x3e, 0x51, 0x1e, 0xa2, 0xd2, 0xe4, 0xc9,
    0xae, 0x2a, 0xc0, 0xd9, 0xff, 0xb7, 0xb2, 0x52
  ] := by
  -- The native evaluator checks the closed computation.
  native_decide

/-- Hashing one block plus one byte uses two compressions. -/
theorem hash_block_and_tail : (hash ⟨Array.replicate 65 0x61⟩).toArray = #[
    0x04, 0x5f, 0x8a, 0xe1, 0x89, 0x32, 0x11, 0x9b,
    0xd0, 0x51, 0xac, 0x7b, 0xa5, 0xc7, 0x3d, 0xb5,
    0x98, 0x92, 0x05, 0x5f, 0xad, 0x5c, 0x32, 0xf8,
    0x2d, 0x79, 0xa6, 0x54, 0x3d, 0x92, 0xa4, 0x97
  ] := by
  -- The native evaluator checks the closed computation.
  native_decide

/-- Generate the deterministic pseudorandom input used by RFC 7693 Appendix E. -/
private def selfTestInput (length seed : Nat) : ByteArray := Id.run do
  -- The seed selects the first 32-bit Fibonacci state word.
  let mut previous := 0xDEAD4BAD * UInt32.ofNat seed
  -- The second state word starts at one for every test case.
  let mut current : UInt32 := 1
  -- Allocate the exact message length before filling it.
  let mut output := ByteArray.mk (Array.replicate length 0)
  for position in [:length] do
    -- Addition wraps modulo `2^32` as required by the C self-test module.
    let next := previous + current
    -- Advance the two-word Fibonacci state.
    previous := current
    current := next
    -- The most significant byte becomes the next message byte.
    output := output.set! position (next >>> 24).toUInt8
  return output

/-- The 255-byte Appendix E input matches an independent BLAKE2s-256 digest. -/
theorem hash_selfTest_255 : (hash (selfTestInput 255 255)).toArray = #[
    0xad, 0x42, 0x86, 0xd0, 0xcb, 0x75, 0x44, 0xfe,
    0x3b, 0x1c, 0x1a, 0xff, 0x31, 0xb8, 0xa9, 0xaa,
    0x3b, 0x60, 0x76, 0xd9, 0xa2, 0xc6, 0xb4, 0xbb,
    0xdb, 0x79, 0x75, 0xba, 0x7f, 0x74, 0x08, 0xa1
  ] := by
  -- Native evaluation covers four blocks and a 63-byte final tail.
  native_decide

/-- The 1024-byte Appendix E input matches an independent BLAKE2s-256 digest. -/
theorem hash_selfTest_1024 : (hash (selfTestInput 1024 1024)).toArray = #[
    0xc7, 0x95, 0xe9, 0xac, 0x66, 0xad, 0x49, 0x54,
    0x0e, 0x9c, 0xe4, 0x3e, 0xfc, 0xc6, 0xda, 0x14,
    0x2c, 0x61, 0xc1, 0xe6, 0x05, 0x1f, 0x06, 0x08,
    0xbb, 0x10, 0x9c, 0x14, 0xd2, 0x4e, 0x4e, 0xbb
  ] := by
  -- Native evaluation covers sixteen full blocks with the final flag on block 16.
  native_decide

end EthCryptographySpecs.Xmss.Blake2s
