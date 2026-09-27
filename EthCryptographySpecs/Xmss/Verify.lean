import EthCryptographySpecs.Xmss.Encoding
import EthCryptographySpecs.Xmss.Merkle

/-!
# `Xmss.Verify`

Signature verification.

# Cost

A constant 133 hash calls, or 144 BLAKE2s compressions of 64-byte blocks:

- Encoding: 1 call, 2 compressions.
  - Message and randomizer are hashed once into the digest the digits come from.
  - Input: 16 + 16 + 64 = 96 bytes, so two blocks.
- Chains: 99 calls, 1 compression each.
  - Chain `i` walks `7 - x_i` steps, and the 42 digits always sum to 195.
  - So the steps total 42 * 7 - 195 = 99, whatever the message.
  - Input per step: 16 + 16 + 16 = 48 bytes, within one block.
- Leaf: 1 call, 11 compressions.
  - The 42 recovered public values are hashed together.
  - Input: 16 + 16 + 42 * 16 = 704 bytes, so eleven blocks.
- Climb: 32 calls, 1 compression each.
  - One parent per level, from the leaf up to the root.
  - Input per parent: 16 + 16 + 2 * 16 = 64 bytes, exactly one block.

A fixed count is what keeps the aggregation circuit a fixed size.

Nothing here needs to be constant time: every value it reads is public.
-/

namespace EthCryptographySpecs.Xmss

open EthCryptographySpecs.Xmss.Constants

/-! ## Keys and signatures -/

/-- What a verifier knows about a signer. -/
structure PublicKey where
  /-- The root of the Merkle tree over the signer's one-time keys. -/
  merkleRoot : Digest
  /-- The call site every hash of this key is made under. -/
  publicParam : PublicParam
  deriving DecidableEq

/-- A one-time signature, plus the path from its leaf to the root. -/
structure Signature where
  /-- Each chain revealed at the height its digit names. -/
  chainTips : Vector Digest V
  /-- The randomizer under which the message encodes. -/
  randomness : Randomness
  /-- The siblings from the leaf upward, one per level. -/
  merklePath : Vector Digest LOG_LIFETIME
  deriving DecidableEq

/-! ## Verification -/

/-- Whether a signature signs a message at an epoch under a public key.

A yes or a no, never a reason.

Which step rejected a well-formed signature carries no consensus meaning. -/
def verify (pk : PublicKey) (msg : Message) (sig : Signature) (epoch : Epoch) :
    Bool :=
  let pp := pk.publicParam
  -- Step 1: recompute the digits.
  -- An inadmissible digest has no digits, so nothing below can accept.
  match wotsEncode pp msg sig.randomness epoch with
  | none => false
  | some x =>
    -- Step 2: walk chain `i` for `7 - x_i` steps, to its claimed public value.
    let tips := otsRecover pp epoch sig.chainTips x
    -- Step 3: hash the 42 claimed public values into the claimed leaf.
    let leaf := otsLeaf pp epoch tips
    -- Step 4: climb the 32 levels, the epoch's bits choosing left or right.
    -- Step 5: the claimed leaf must reach the committed root.
    decide (computeRoot pp epoch sig.merklePath leaf = pk.merkleRoot)

end EthCryptographySpecs.Xmss
