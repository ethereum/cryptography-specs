import EthCryptographySpecs.Xmss.TweakHash

/-!
# `Xmss.Wots`

The one-time signature: 42 hash chains, one per encoding digit.

Revealing a chain at height `k` lets anyone reach the heights above `k`.

It reveals nothing about the heights below.
-/

namespace EthCryptographySpecs.Xmss

open EthCryptographySpecs.Xmss.Constants

/-! ## Chains -/

instance : NeZero CHAIN_LENGTH := ⟨by decide⟩

/-- One step along a chain, from position `step` to the next. -/
def chainStep (pp : PublicParam) (epoch : Epoch) (index : Fin V) (step : Nat)
    (value : Digest) : Digest :=
  -- A walk never leaves the chain, so the conversion never wraps.
  tweakHash pp .chain (chainPosition index (Fin.ofNat CHAIN_LENGTH step)) epoch
    (packBytes value)

/-- Walk chain `index` for `steps` steps, starting at position `start`. -/
def chain (pp : PublicParam) (epoch : Epoch) (index : Fin V)
    (start steps : Nat) (value : Digest) : Digest :=
  match steps with
  | 0 => value
  -- The last step leaves position `start + s`, having walked `s` before it.
  | s + 1 => chainStep pp epoch index (start + s)
      (chain pp epoch index start s value)

/-! ## The one-time key -/

/-- The public value of every chain, each walked to its last position. -/
def wotsPublicKey (pp : PublicParam) (epoch : Epoch) (sk : Vector Digest V) :
    Vector Digest V :=
  Vector.ofFn fun i => chain pp epoch i 0 (CHAIN_LENGTH - 1) sk[i]

/-- Reveal each chain at the height its digit names. -/
def wotsSign (pp : PublicParam) (epoch : Epoch) (sk : Vector Digest V)
    (x : Vector (Fin CHAIN_LENGTH) V) : Vector Digest V :=
  Vector.ofFn fun i => chain pp epoch i 0 (x[i] : Nat) sk[i]

/-- Walk each revealed value the rest of the way to its public value. -/
def wotsRecover (pp : PublicParam) (epoch : Epoch) (tips : Vector Digest V)
    (x : Vector (Fin CHAIN_LENGTH) V) : Vector Digest V :=
  Vector.ofFn fun i =>
    chain pp epoch i (x[i] : Nat) (CHAIN_LENGTH - 1 - (x[i] : Nat)) tips[i]

/-- The Merkle leaf: the 42 public values hashed together. -/
def wotsLeaf (pp : PublicParam) (epoch : Epoch) (pk : Vector Digest V) :
    Digest :=
  -- - payload: V tips of DIGEST_LEN bytes = 42 * 16 = 672
  -- - hash input: TWEAK_LEN + PUBLIC_PARAM_LEN + payload = 16 + 16 + 672 = 704
  tweakHash pp .leaf 0 epoch
    (pk.toList.foldl (fun acc d => acc ++ packBytes d) ByteArray.empty)

end EthCryptographySpecs.Xmss
