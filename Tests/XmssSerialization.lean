import EthCryptographySpecs.Xmss.Serialization
import Ssz.Codec.Json

/-! Byte-level XMSS wire fixtures and exact-length regression tests. -/

open EthCryptographySpecs.Xmss
open EthCryptographySpecs.Xmss.Constants

private def check (accepted : Bool) (label : String) : IO Unit := do
  -- A failing regression names the wire property that changed.
  unless accepted do throw (IO.userError label)

private def fixtureBytes (hex : String) : IO ByteArray := do
  -- The shared library reads the literal fixture, independently of XMSS serialization.
  match Ssz.ofHex hex with
  | .ok bytes => return ⟨bytes⟩
  | .error _ => throw (IO.userError "malformed hex fixture")

private def testPublicKeyWire : IO Unit := do
  -- Fixture state: 16 increasing root bytes followed by 16 distinct parameter bytes.
  let pk : PublicKey := {
    -- Different bytes within each field expose reversal as well as field swaps.
    merkleRoot := Vector.ofFn fun i => UInt8.ofNat i.val
    publicParam := Vector.ofFn fun i => UInt8.ofNat (0x80 + i.val) }
  -- Expected wire order is fixed independently of the encoder.
  let expected ← fixtureBytes "0x000102030405060708090a0b0c0d0e0f808182838485868788898a8b8c8d8e8f"
  -- The full literal pins length, field order, and byte order.
  check (encodePublicKey pk == expected) "public key wire fixture"
  -- Decoding the external bytes must recover the expected typed fields.
  match decodePublicKey expected with
  | .ok actual => check (decide (actual = pk)) "public key fixture decode"
  | .error _ => throw (IO.userError "public key fixture rejected")

private def testSignatureWire : IO Unit := do
  -- Fixture state: each chain and sibling has a distinct repeated tag.
  let sig : Signature := {
    -- Tags 1 through 42 expose digest permutations and missing entries.
    chainElements := Vector.ofFn fun i => Vector.replicate DIGEST_LEN (UInt8.ofNat (i.val + 1))
    -- Increasing high bytes distinguish the randomizer from every digest field.
    randomness := Vector.ofFn fun i => UInt8.ofNat (0xe0 + i.val)
    -- Tags 128 through 159 distinguish every level of the authentication path.
    merklePath := Vector.ofFn fun i => Vector.replicate DIGEST_LEN (UInt8.ofNat (0x80 + i.val)) }
  -- Expected wire bytes, written out independently of the encoder.
  let expected ← fixtureBytes <| "0x" ++
    -- 42 chains: 16 bytes each, in chain order.
    "01010101010101010101010101010101020202020202020202020202020202020303030303030303030303030303030304040404040404040404040404040404" ++
    "05050505050505050505050505050505060606060606060606060606060606060707070707070707070707070707070708080808080808080808080808080808" ++
    "090909090909090909090909090909090a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c" ++
    "0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f10101010101010101010101010101010" ++
    "11111111111111111111111111111111121212121212121212121212121212121313131313131313131313131313131314141414141414141414141414141414" ++
    "15151515151515151515151515151515161616161616161616161616161616161717171717171717171717171717171718181818181818181818181818181818" ++
    "191919191919191919191919191919191a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1b1b1b1b1b1b1b1b1b1b1b1b1b1b1b1b1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c" ++
    "1d1d1d1d1d1d1d1d1d1d1d1d1d1d1d1d1e1e1e1e1e1e1e1e1e1e1e1e1e1e1e1e1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f20202020202020202020202020202020" ++
    "21212121212121212121212121212121222222222222222222222222222222222323232323232323232323232323232324242424242424242424242424242424" ++
    "25252525252525252525252525252525262626262626262626262626262626262727272727272727272727272727272728282828282828282828282828282828" ++
    "292929292929292929292929292929292a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a" ++
    -- 24 randomizer bytes, after the chains.
    "e0e1e2e3e4e5e6e7e8e9eaebecedeeeff0f1f2f3f4f5f6f7" ++
    -- 32 siblings: 16 bytes each, from leaf to root.
    "80808080808080808080808080808080818181818181818181818181818181818282828282828282828282828282828283838383838383838383838383838383" ++
    "84848484848484848484848484848484858585858585858585858585858585858686868686868686868686868686868687878787878787878787878787878787" ++
    "88888888888888888888888888888888898989898989898989898989898989898a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8b8b8b8b8b8b8b8b8b8b8b8b8b8b8b8b" ++
    "8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8d8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f" ++
    "90909090909090909090909090909090919191919191919191919191919191919292929292929292929292929292929293939393939393939393939393939393" ++
    "94949494949494949494949494949494959595959595959595959595959595959696969696969696969696969696969697979797979797979797979797979797" ++
    "98989898989898989898989898989898999999999999999999999999999999999a9a9a9a9a9a9a9a9a9a9a9a9a9a9a9a9b9b9b9b9b9b9b9b9b9b9b9b9b9b9b9b" ++
    "9c9c9c9c9c9c9c9c9c9c9c9c9c9c9c9c9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9e9e9e9e9e9e9e9e9e9e9e9e9e9e9e9e9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f"
  -- The whole 1208-byte literal pins all three fields and every collection entry.
  check (encodeSignature sig == expected) "signature wire fixture"
  -- Parsing these bytes must recover the typed collections in the same order.
  match decodeSignature expected with
  | .ok actual => check (decide (actual = sig)) "signature fixture decode"
  | .error _ => throw (IO.userError "signature fixture rejected")

private def testLengths : IO Unit := do
  -- Mutation: empty, truncated, and extended public key buffers must all fail.
  for n in [0, 1, 15, 16, 31, 33, 64, 1208] do
    -- Content is immaterial: the only validation for opaque bytes is exact length.
    let bytes := ByteArray.mk (Array.replicate n 0xff)
    -- The error must retain the actual input length for the caller.
    match decodePublicKey bytes with
    | .error (.badPublicKeySize actual) => check (actual == n) "public key size error payload"
    | _ => throw (IO.userError s!"accepted bad public key length {n}")
  -- Mutation: exercise field boundaries and both adjacent invalid signature lengths.
  for n in [0, 1, 32, 672, 695, 696, 1207, 1209, 2416] do
    -- No prefix of a signature, nor an encoding with trailing bytes, is accepted.
    let bytes := ByteArray.mk (Array.replicate n 0)
    -- Reject the complete container rather than silently padding or truncating it.
    match decodeSignature bytes with
    | .error (.badSignatureSize actual) => check (actual == n) "signature size error payload"
    | _ => throw (IO.userError s!"accepted bad signature length {n}")

private def testOpaqueBytes : IO Unit := do
  -- Fixture state: all-zero, all-high, and mixed bytes need no canonical-form check.
  for salt in [0, 1, 127, 255] do
    -- A mixed fixture exercises every byte position in the 32-byte public key.
    let pkBytes := ByteArray.mk (Array.ofFn (n := 32) fun i => UInt8.ofNat (i.val * salt))
    -- Re-encoding an arbitrary accepted key preserves its original bytes.
    match decodePublicKey pkBytes with
    | .ok pk => check (encodePublicKey pk == pkBytes) "arbitrary public key buffer"
    | .error _ => throw (IO.userError "rejected correctly sized public key")
    -- A different pattern crosses both signature field boundaries and wraps past 255.
    let sigBytes := ByteArray.mk (Array.ofFn (n := 1208) fun i => UInt8.ofNat (i.val * salt + salt))
    -- Acceptance and exact recovery apply even when these bytes are not a valid signature.
    match decodeSignature sigBytes with
    | .ok sig => check (encodeSignature sig == sigBytes) "arbitrary signature buffer"
    | .error _ => throw (IO.userError "rejected correctly sized signature")
  -- A uniform high-byte signature separately covers opaque contents with every bit set.
  let highBytes := ByteArray.mk (Array.replicate 1208 0xff)
  -- Cryptographic verification is separate from decoding the wire representation.
  match decodeSignature highBytes with
  | .ok sig => check (encodeSignature sig == highBytes) "all-high signature buffer"
  | .error _ => throw (IO.userError "rejected all-high signature")

def main : IO Unit := do
  -- Pin consensus field order with independent literal buffers in both directions.
  testPublicKeyWire
  -- Pin every digest position and the randomizer's position within the signature.
  testSignatureWire
  -- Protect exact-length rejection at the container and field boundaries.
  testLengths
  -- Protect the absence of byte-content restrictions on parsing.
  testOpaqueBytes
  -- Report success only after every fixture and refusal case has passed.
  IO.println "XMSS SSZ serialization regressions passed"
