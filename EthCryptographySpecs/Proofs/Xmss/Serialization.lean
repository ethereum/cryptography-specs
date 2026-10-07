import EthCryptographySpecs.Xmss.Serialization
import EthCryptographySpecs.Proofs.Xmss.Types

/-!
# Proofs: `Xmss.Serialization`

The encodings are bijections between objects and byte strings of the declared length.
-/

namespace EthCryptographySpecs.Xmss

open Constants

set_option maxRecDepth 2048

/-- Cutting a field into digests and joining them back gives the field. -/
@[simp] theorem flatten_splitDigests {n : Nat} (bytes : Vector UInt8 (n * DIGEST_LEN)) :
    (splitDigests bytes).flatten = bytes := by
  apply Vector.ext
  intro i inside
  simp only [Vector.getElem_flatten, splitDigests, Vector.getElem_ofFn]
  -- Position p is byte p mod 16 of digest p / 16.
  congr 1
  simp only [DIGEST_LEN] at *
  omega

/-- Joining digests into a field and cutting it back gives the digests. -/
@[simp] theorem splitDigests_flatten {n : Nat} (digests : Vector Digest n) :
    splitDigests digests.flatten = digests := by
  apply Vector.ext
  intro i inside
  apply Vector.ext
  intro j within
  simp only [splitDigests, Vector.getElem_ofFn, Vector.getElem_flatten]
  -- Position 16 i + j is byte j of digest i.
  have quotient : (i * DIGEST_LEN + j) / DIGEST_LEN = i := by
    simp only [DIGEST_LEN] at *
    omega
  have remainder : (i * DIGEST_LEN + j) % DIGEST_LEN = j := by
    simp only [DIGEST_LEN] at *
    omega
  simp [quotient, remainder]

/-- A public key encodes as its root, then its public parameter. -/
theorem encodePublicKey_eq (pk : PublicKey) :
    encodePublicKey pk = packBytes pk.merkleRoot ++ packBytes pk.publicParam := by
  simp [encodePublicKey, publicKeySsz, publicKeySszValue, Ssz.serialize,
    Ssz.serializeStruct, Ssz.serializeFields, Ssz.assemble,
    Ssz.Desc.isFixed, Ssz.Desc.fixedSize, Ssz.headWidth, Ssz.bodyWidth,
    Ssz.headOf, Ssz.bodiesOf, Ssz.bytesPerOffset, Bind.bind, Except.bind,
    pure, Except.pure, DIGEST_LEN, PUBLIC_PARAM_LEN, packBytes]
  apply ByteArray.ext
  simp only [ByteArray.data_append]

/-- A signature encodes as its chain values, then its randomizer, then its siblings. -/
theorem encodeSignature_eq (sig : Signature) :
    encodeSignature sig = packBytes sig.chainElements.flatten ++
      (packBytes sig.randomness ++ packBytes sig.merklePath.flatten) := by
  simp [encodeSignature, signatureSsz, signatureSszValue, Ssz.serialize,
    Ssz.serializeStruct, Ssz.serializeFields, Ssz.assemble,
    Ssz.Desc.isFixed, Ssz.Desc.fixedSize, Ssz.headWidth, Ssz.bodyWidth,
    Ssz.headOf, Ssz.bodiesOf, Ssz.bytesPerOffset, Bind.bind, Except.bind,
    pure, Except.pure, V, LOG_LIFETIME, DIGEST_LEN, RANDOMNESS_LEN,
    packBytes]
  apply ByteArray.ext
  simp only [ByteArray.data_append]

/-- A public key encodes to 32 bytes. -/
@[simp] theorem size_encodePublicKey (pk : PublicKey) :
    (encodePublicKey pk).size = PUB_KEY_SIZE := by
  simp [encodePublicKey_eq, PUB_KEY_SIZE]

/-- A signature encodes to 1208 bytes. -/
@[simp] theorem size_encodeSignature (sig : Signature) :
    (encodeSignature sig).size = SIG_SIZE := by
  simp [encodeSignature_eq, SIG_SIZE, WOTS_SIG_SIZE, Nat.add_assoc]

/-- Converting a public key to a codec value and back returns it. -/
@[simp] theorem publicKeyFromSsz?_value (pk : PublicKey) :
    publicKeyFromSsz? (publicKeySszValue pk) = some pk := by
  simp [publicKeySszValue, publicKeyFromSsz?]

/-- Converting a signature to a codec value and back returns it. -/
@[simp] theorem signatureFromSsz?_value (sig : Signature) :
    signatureFromSsz? (signatureSszValue sig) = some sig := by
  simp [signatureSszValue, signatureFromSsz?]

private theorem deserialize_publicKey_value (pk : PublicKey) :
    Ssz.deserialize publicKeySsz (encodePublicKey pk).data = .ok (publicKeySszValue pk) := by
  -- The codec checks the 32-byte length, then cuts out the two 16-byte fields.
  rw [encodePublicKey_eq]
  simp [publicKeySsz, publicKeySszValue, packBytes, ByteArray.data_append,
    Ssz.deserialize, Ssz.structSlices, Ssz.structBudget,
    Ssz.readSlots, Ssz.bodyStarts, Ssz.Slot.held, Ssz.deserializeFields,
    Ssz.Desc.fieldsFixedSize, Ssz.Desc.fixedSize, Ssz.bytesPerOffset,
    Bind.bind, Except.bind, pure, Except.pure, DIGEST_LEN, PUBLIC_PARAM_LEN]
  -- Slicing a concatenation at its seams returns the original pieces.
  simp [Array.extract_empty_of_stop_le_start]

private theorem deserialize_signature_value (sig : Signature) :
    Ssz.deserialize signatureSsz (encodeSignature sig).data = .ok (signatureSszValue sig) := by
  -- The codec checks the 1208-byte length, then cuts out 672, 24 and 512 bytes.
  rw [encodeSignature_eq]
  simp [signatureSsz, signatureSszValue, packBytes, ByteArray.data_append,
    Ssz.deserialize, Ssz.structSlices, Ssz.structBudget,
    Ssz.readSlots, Ssz.bodyStarts, Ssz.Slot.held, Ssz.deserializeFields,
    Ssz.Desc.fieldsFixedSize, Ssz.Desc.fixedSize, Ssz.bytesPerOffset,
    Bind.bind, Except.bind, pure, Except.pure, V, LOG_LIFETIME, DIGEST_LEN, RANDOMNESS_LEN]
  -- Slicing a concatenation at its seams returns the original pieces.
  simp [Array.extract_empty_of_stop_le_start]

/-- Decoding an encoded public key returns it. -/
@[simp] theorem decodePublicKey_encodePublicKey (pk : PublicKey) :
    decodePublicKey (encodePublicKey pk) = .ok pk := by
  simp [decodePublicKey, deserialize_publicKey_value]

/-- Decoding an encoded signature returns it. -/
@[simp] theorem decodeSignature_encodeSignature (sig : Signature) :
    decodeSignature (encodeSignature sig) = .ok sig := by
  simp [decodeSignature, deserialize_signature_value]

/-- Every 32-byte string is the encoding of a public key. -/
theorem encodePublicKey_surjective {bytes : ByteArray} (sized : bytes.size = PUB_KEY_SIZE) :
    ∃ pk, encodePublicKey pk = bytes := by
  have size : bytes.data.size = 32 := sized.trans pub_key_size_eq
  -- Bytes 0..15 are the root and bytes 16..31 the public parameter.
  refine ⟨⟨⟨bytes.data.extract 0 16, by simp [size, DIGEST_LEN]⟩,
    ⟨bytes.data.extract 16 32, by simp [size, PUBLIC_PARAM_LEN]⟩⟩, ?_⟩
  -- Re-joining the two adjacent slices gives the whole string.
  rw [encodePublicKey_eq]
  apply ByteArray.ext
  simp [packBytes, Array.extract_append_extract, ← size]
  omega

/-- Every 1208-byte string is the encoding of a signature. -/
theorem encodeSignature_surjective {bytes : ByteArray} (sized : bytes.size = SIG_SIZE) :
    ∃ sig, encodeSignature sig = bytes := by
  have size : bytes.data.size = 1208 := sized.trans sig_size_eq
  -- Cut at the field seams:
  --
  --     [ 0, 672) chain values
  --     [672, 696) randomizer
  --     [696, 1208) siblings
  refine ⟨⟨splitDigests ⟨bytes.data.extract 0 672, by simp [size, V, DIGEST_LEN]⟩,
    ⟨bytes.data.extract 672 696, by simp [size, RANDOMNESS_LEN]⟩,
    splitDigests ⟨bytes.data.extract 696 1208, by simp [size, LOG_LIFETIME, DIGEST_LEN]⟩⟩, ?_⟩
  -- Re-joining the three adjacent slices gives the whole string.
  rw [encodeSignature_eq]
  apply ByteArray.ext
  simp [packBytes, Array.extract_append_extract, ← size]
  omega

/-- Decoding then re-encoding a 32-byte string returns it. -/
theorem encodePublicKey_decodePublicKey {bytes : ByteArray} (sized : bytes.size = PUB_KEY_SIZE) :
    (decodePublicKey bytes).map encodePublicKey = .ok bytes := by
  obtain ⟨pk, rfl⟩ := encodePublicKey_surjective sized
  simp [Except.map]

/-- Decoding then re-encoding a 1208-byte string returns it. -/
theorem encodeSignature_decodeSignature {bytes : ByteArray} (sized : bytes.size = SIG_SIZE) :
    (decodeSignature bytes).map encodeSignature = .ok bytes := by
  obtain ⟨sig, rfl⟩ := encodeSignature_surjective sized
  simp [Except.map]

/-- Distinct public keys have distinct encodings. -/
theorem encodePublicKey_injective : Function.Injective encodePublicKey := by
  intro left right same
  simpa using congrArg decodePublicKey same

/-- Distinct signatures have distinct encodings. -/
theorem encodeSignature_injective : Function.Injective encodeSignature := by
  intro left right same
  simpa using congrArg decodeSignature same

/-- A public key string of any other length than 32 bytes is rejected. -/
theorem decodePublicKey_badSize {bytes : ByteArray} (wrong : bytes.size ≠ PUB_KEY_SIZE) :
    decodePublicKey bytes = .error (.badPublicKeySize bytes.size) := by
  rw [pub_key_size_eq] at wrong
  -- The codec rejects strings of 2^32 bytes or more before it checks the exact length.
  by_cases large : 2 ^ 32 ≤ bytes.size <;>
    simp [decodePublicKey, publicKeySsz, Ssz.deserialize, Ssz.structSlices,
      Ssz.structBudget, Ssz.Desc.fieldsFixedSize, Ssz.Desc.fixedSize,
      Ssz.bytesPerOffset, DIGEST_LEN, PUBLIC_PARAM_LEN, wrong, large,
      Bind.bind, Except.bind, pure, Except.pure]

/-- A signature string of any other length than 1208 bytes is rejected. -/
theorem decodeSignature_badSize {bytes : ByteArray} (wrong : bytes.size ≠ SIG_SIZE) :
    decodeSignature bytes = .error (.badSignatureSize bytes.size) := by
  rw [sig_size_eq] at wrong
  -- The codec rejects strings of 2^32 bytes or more before it checks the exact length.
  by_cases large : 2 ^ 32 ≤ bytes.size <;>
    simp [decodeSignature, signatureSsz, Ssz.deserialize, Ssz.structSlices,
      Ssz.structBudget, Ssz.Desc.fieldsFixedSize, Ssz.Desc.fixedSize,
      Ssz.bytesPerOffset, V, LOG_LIFETIME, DIGEST_LEN, RANDOMNESS_LEN, wrong, large,
      Bind.bind, Except.bind, pure, Except.pure]

/-- Public key decoding succeeds exactly on 32-byte strings. -/
theorem decodePublicKey_success_iff (bytes : ByteArray) :
    (∃ pk, decodePublicKey bytes = .ok pk) ↔ bytes.size = PUB_KEY_SIZE := by
  constructor
  · rintro ⟨pk, read⟩
    exact Decidable.byContradiction fun wrong => by simp [decodePublicKey_badSize wrong] at read
  · intro sized
    obtain ⟨pk, rfl⟩ := encodePublicKey_surjective sized
    exact ⟨pk, by simp⟩

/-- Signature decoding succeeds exactly on 1208-byte strings. -/
theorem decodeSignature_success_iff (bytes : ByteArray) :
    (∃ sig, decodeSignature bytes = .ok sig) ↔ bytes.size = SIG_SIZE := by
  constructor
  · rintro ⟨sig, read⟩
    exact Decidable.byContradiction fun wrong => by simp [decodeSignature_badSize wrong] at read
  · intro sized
    obtain ⟨sig, rfl⟩ := encodeSignature_surjective sized
    exact ⟨sig, by simp⟩

end EthCryptographySpecs.Xmss
