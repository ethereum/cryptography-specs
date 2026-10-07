import EthCryptographySpecs.Xmss.KeyGen
import EthCryptographySpecs.Xmss.Sign
import EthCryptographySpecs.Xmss.Serialization

/-!
# `Xmss.Exports`

C-ABI exports for the Python bindings.

The hash and encoding layers are exported too, to locate a diverging layer.
-/

namespace EthCryptographySpecs.Xmss.Exports

open EthCryptographySpecs.Xmss
open EthCryptographySpecs.Xmss.Constants

/-- Read a fixed-size input, rejecting any other length with the given error. -/
private def readExact (n : Nat) (bytes : ByteArray) (bad : Nat → XmssError) :
    Except XmssError (Vector UInt8 n) :=
  -- Too short or too long is refused: no padding, no truncation.
  if h : bytes.size = n then .ok ⟨bytes.data, h⟩ else .error (bad bytes.size)

/-- The public key grown from a seed, for the epochs `[epochStart, epochEnd]`. -/
@[export eth_xmss_key_gen]
def keyGenExport (seed : ByteArray) (epochStart epochEnd : Epoch) :
    IO ByteArray :=
  runXmss do
    let seed ← readExact SEED_LEN seed .badSeedSize
    -- The secret half is dropped: the seed and the range regrow it.
    let (_, pk) ← keyGen seed epochStart epochEnd
    return encodePublicKey pk

/-- Sign a message at an epoch with the key grown from a seed. -/
@[export eth_xmss_sign]
def signExport (seed : ByteArray) (epochStart epochEnd epoch : Epoch)
    (msg : ByteArray) : IO ByteArray :=
  runXmss do
    let seed ← readExact SEED_LEN seed .badSeedSize
    let msg ← readExact MESSAGE_LEN msg .badMessageSize
    -- An empty range fails here, an epoch outside the range fails at signing.
    let (sk, _) ← keyGen seed epochStart epochEnd
    let sig ← sign sk msg epoch
    return encodeSignature sig

/-- Whether a signature signs a message at an epoch under a public key, as 1 or 0. -/
@[export eth_xmss_verify]
def verifyExport (pk : ByteArray) (epoch : Epoch) (msg : ByteArray)
    (sig : ByteArray) : IO UInt8 :=
  runXmss do
    -- Only the lengths are checked: every correctly sized string decodes.
    let pk ← decodePublicKey pk
    let msg ← readExact MESSAGE_LEN msg .badMessageSize
    let sig ← decodeSignature sig
    return if verify pk msg sig epoch then 1 else 0

/-- The message's 42 chain digits, one byte each, or nothing when inadmissible. -/
@[export eth_xmss_wots_encode]
def wotsEncodeExport (pp : ByteArray) (msg : ByteArray)
    (rnd : ByteArray) (epoch : Epoch) : IO ByteArray :=
  runXmss do
    let pp ← readExact PUBLIC_PARAM_LEN pp .badPublicParamSize
    let msg ← readExact MESSAGE_LEN msg .badMessageSize
    let rnd ← readExact RANDOMNESS_LEN rnd .badRandomnessSize
    -- Inadmissible is an ordinary outcome when grinding, not an error.
    match wotsEncode pp msg rnd epoch with
    -- Each digit is below 8, so it fits one byte.
    | some x => return ⟨x.toArray.map fun d => UInt8.ofNat d.val⟩
    | none => return .empty

/-- The tweakable hash of a payload at one call site, as 16 bytes. -/
@[export eth_xmss_tweak_hash]
def tweakHashExport (pp : ByteArray) (tweakType : UInt8)
    (subPosition index : UInt32) (payload : ByteArray) : IO ByteArray :=
  runXmss do
    let pp ← readExact PUBLIC_PARAM_LEN pp .badPublicParamSize
    -- Bytes 0 to 7 name the eight call sites.
    let some t := TweakType.ofByte? tweakType
      | throw (.unknownTweakType tweakType)
    -- The payload has no fixed length, so it is hashed as given.
    return packBytes (tweakHash pp t subPosition index payload)

/-- The BLAKE2s-256 digest of a byte string, as 32 bytes. -/
@[export eth_xmss_blake2s]
def blake2sExport (input : ByteArray) : IO ByteArray :=
  -- Hashing cannot fail, so there is no error to run.
  return packBytes (Blake2s.hash input)

end EthCryptographySpecs.Xmss.Exports
