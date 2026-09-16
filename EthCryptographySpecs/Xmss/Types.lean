import EthCryptographySpecs.Xmss.Constants

/-!
# `Xmss.Types`

Fixed-size byte objects, with the length carried in the type.

- Indexing is total, so reading a field needs no bounds proof and cannot panic.
- Sizes stop being side conditions dragged through proofs.
- These are abbreviations, so equal-length objects stay interchangeable.

Untyped bytes survive at two edges only: serialization and the C ABI.
-/

namespace EthCryptographySpecs.Xmss

open EthCryptographySpecs.Xmss.Constants

/-! ## Objects -/

/-- A hash value of `n` bits.

Chain values, Merkle nodes and leaves are all digests. -/
abbrev Digest := Vector UInt8 DIGEST_LEN

/-- The call-site label hashed in front of every input.

It is what keeps a chain step, a Merkle node and a leaf from sharing a hash. -/
abbrev Tweak := Vector UInt8 TWEAK_LEN

/-- The public parameter `P`, hashed into every call.

It makes one key's hash functions independent of another's. -/
abbrev PublicParam := Vector UInt8 PUBLIC_PARAM_LEN

/-- The randomizer `rho`, ground by the signer until the encoding is valid.

It is part of the signature. -/
abbrev Randomness := Vector UInt8 RANDOMNESS_LEN

/-- The message to sign: a 256-bit digest, not a document. -/
abbrev Message := Vector UInt8 MESSAGE_LEN

/-- The master secret `S`, from which every other secret is derived. -/
abbrev Seed := Vector UInt8 SEED_LEN

/-- When a signature was made.

Each epoch in a key's range carries one one-time key.

Signing is stateless and takes the epoch explicitly.

Tracking which epochs are spent belongs to the caller. -/
abbrev Epoch := UInt32

/-! ## Crossing to and from untyped bytes -/

/-- The bytes of a fixed-size object, in order.

Examples:
* `(packBytes #v[10, 20]).data = #[10, 20]`
* `(packBytes #v[10, 20]).size = 2`
-/
def packBytes {n : Nat} (v : Vector UInt8 n) : ByteArray :=
  -- The length invariant is discarded, not checked: every object has one.
  ⟨v.toArray⟩

/-- Read a fixed-size object out of a buffer at an offset.

Returns nothing when the buffer has no room for the object.

Never pads and never truncates.

Examples, with `b = ByteArray.mk #[10, 20, 30, 40]`:
* `unpackBytes? 4 b = some #v[10, 20, 30, 40]`
* `unpackBytes? 2 b 1 = some #v[20, 30]`
* `unpackBytes? 2 b 3 = none`
-/
def unpackBytes? (n : Nat) (b : ByteArray) (offset : Nat := 0) :
    Option (Vector UInt8 n) :=
  -- The guard is the whole validation: a buffer without room is rejected.
  if h : offset + n ≤ b.size then
    -- Invariant: every index below the object's length lands inside the buffer.
    -- So reading is total and needs no fallback byte.
    some (Vector.ofFn fun i => b.data[offset + i.val]'(by
      simp only [ByteArray.size] at h
      omega))
  else
    none

end EthCryptographySpecs.Xmss
