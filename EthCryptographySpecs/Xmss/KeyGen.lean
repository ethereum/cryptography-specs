import EthCryptographySpecs.Xmss.Errors
import EthCryptographySpecs.Xmss.Verify

/-!
# `Xmss.KeyGen`

Key generation.

The seed and the epoch range regenerate the whole key pair.

The secret key stores no chain value and no tree node.

Each one is recomputed when needed, which gives the same key as storing them.
-/

namespace EthCryptographySpecs.Xmss

open EthCryptographySpecs.Xmss.Constants

/-! ## Derivations from the seed -/

/-- The public parameter of the key grown from a seed.

It is hashed under an all-zero parameter, since its own does not exist yet. -/
def genPublicParam (seed : Seed) : PublicParam :=
  tweakHash (Vector.replicate PUBLIC_PARAM_LEN 0) .parameter 0 0
    (packBytes seed)

/-- The starting value of every chain of one epoch's one-time key. -/
def otsSecretKey (pp : PublicParam) (seed : Seed) (epoch : Epoch) :
    Vector Digest V :=
  -- The chain number and the epoch place each value at its own call site.
  Vector.ofFn fun i =>
    tweakHash pp .prf (UInt32.ofNat i.val) epoch (packBytes seed)

/-! ## Keys -/

/-- A secret key: the seed, the public parameter and the epoch range.

It must never sign two different messages at one epoch.

Signing is stateless, so tracking spent epochs is the caller's job. -/
abbrev SecretKey := TreeParams

/-- The Merkle leaf of each epoch: its one-time public key, hashed. -/
def SecretKey.leaves (sk : SecretKey) (epoch : Nat) : Digest :=
  -- Leaf indices are epochs, so the conversion never wraps.
  let ep := UInt32.ofNat epoch
  otsLeaf sk.publicParam ep
    (otsPublicKey sk.publicParam ep (otsSecretKey sk.publicParam sk.seed ep))

/-- The public key: the root over the key's leaves, with its parameter. -/
def SecretKey.publicKey (sk : SecretKey) : PublicKey where
  merkleRoot := sk.root sk.leaves
  publicParam := sk.publicParam

/-- The key pair grown from a seed, signing at the epochs of a range.

Rejects an empty range. -/
def keyGen (seed : Seed) (epochStart epochEnd : Epoch) :
    Except XmssError (SecretKey × PublicKey) :=
  if h : epochStart ≤ epochEnd then
    let sk : SecretKey := {
      publicParam := genPublicParam seed
      seed
      epochStart
      epochEnd
      epochStart_le_epochEnd := h }
    .ok (sk, sk.publicKey)
  else
    .error (.invalidEpochRange epochStart epochEnd)

end EthCryptographySpecs.Xmss
