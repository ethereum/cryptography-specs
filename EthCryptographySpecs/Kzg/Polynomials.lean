import EthCryptographySpecs.Bls
import EthCryptographySpecs.Kzg.Constants
import EthCryptographySpecs.Kzg.BitReversal
import EthCryptographySpecs.Kzg.Errors

/-!
# `Polynomials`

Polynomial helpers used by the blob-commitment surface of KZG. These
are field-element manipulations independent of the trusted setup.

`Polynomial` is a fixed-length sequence of `Fr`s
(conceptually `Vector[Fr, FIELD_ELEMENTS_PER_BLOB]`). We
represent it as `Array Fr` and rely on length checks at
the boundaries.

`PolynomialCoeff` is the same shape but for coefficient form, used by
the cell-proof surface. Function names are picked to avoid collision
(`evaluatePolynomialcoeff` vs `evaluatePolynomialInEvaluationForm`).
-/

namespace EthCryptographySpecs.Kzg

open EthCryptographySpecs.Bls (Fr)

open EthCryptographySpecs.Kzg.Constants
open EthCryptographySpecs.Kzg.BitReversal

/-! ## Type aliases -/

abbrev Polynomial      := Array Fr
abbrev PolynomialCoeff := Array Fr
abbrev Blob            := ByteArray
abbrev Bytes32         := ByteArray
abbrev Bytes48         := ByteArray

/-! ## Bytes <-> field element helpers -/

/-- SHA-256 over the input bytes. -/
@[inline] def hash (data : ByteArray) : ByteArray := Bls.sha256 data

/-- Encode `n` as `len` big-endian bytes. -/
def intToBytesBE (n : Nat) (len : Nat) : ByteArray :=
  ByteArray.mk <| Array.ofFn (n := len) fun i =>
    UInt8.ofNat ((n >>> ((len - 1 - i.val) * 8)) &&& 0xff)

/-- Big-endian accumulation of `bytes` onto `acc`. -/
def bytesBEToNatAux (acc : Nat) : List UInt8 → Nat
  | [] => acc
  | b :: rest => bytesBEToNatAux ((acc <<< 8) ||| b.toNat) rest

/-- Decode big-endian bytes as a `Nat`. -/
def bytesBEToNat (b : ByteArray) : Nat :=
  bytesBEToNatAux 0 b.data.toList

/-- Hash `data` and reduce the SHA-256 output modulo the BLS modulus
into an `Fr`. The output is not uniform over the field. -/
def hashToBlsField (data : ByteArray) : Fr :=
  let h := hash data
  -- Reduce the 256-bit hash modulo BLS_MODULUS, then construct the field element.
  Fr.ofNat (bytesBEToNat h)

/-- Decode a 32-byte big-endian integer as an `Fr`. Throws if the input
has the wrong size or the integer is `≥ BLS_MODULUS`. -/
def bytesToBlsField (b : Bytes32) : Except KzgError Fr :=
  if b.size ≠ BYTES_PER_FIELD_ELEMENT then
    .error (.badFieldElementSize b.size)
  else match Fr.fromBytesBE b with
  | .ok f    => .ok f
  | .error _ => .error (.invalidFieldElement none)

/-- Encode `x` as 32 big-endian bytes. -/
@[inline] def blsFieldToBytes (x : Fr) : Bytes32 := x.toBytesBE

/-- `[current, current * x, ..., current * x^(n-1)]`. -/
def computePowersAux (x current : Fr) : Nat → List Fr
  | 0 => []
  | n + 1 => current :: computePowersAux x (current * x) n

/-- Return `[x^0, x^1, ..., x^(n-1)]`. -/
def computePowers (x : Fr) (n : Nat) : Array Fr :=
  (computePowersAux x Fr.one n).toArray

/-- Return the `order`-th roots of unity in `Fr`. Requires `order` to
divide `BLS_MODULUS - 1`. -/
def computeRootsOfUnity (order : Nat) : Array Fr :=
  let exponent := (BLS_MODULUS - 1) / order
  let root :=
    (Fr.ofNat PRIMITIVE_ROOT_OF_UNITY) ^ (Fr.ofNat exponent)
  computePowers root order

/-! ## Blob <-> Polynomial -/

/-- Decode `count` 32-byte chunks of `blob`, starting at chunk index `i`.
Throws (with the chunk index) on the first invalid field element. -/
def blobToPolynomialAux (blob : Blob) : Nat → Nat → Except KzgError (List Fr)
  | _, 0 => .ok []
  | i, count + 1 =>
    let start := i * BYTES_PER_FIELD_ELEMENT
    let stop  := (i + 1) * BYTES_PER_FIELD_ELEMENT
    match bytesToBlsField (blob.extract start stop) with
    | .ok f    => do return f :: (← blobToPolynomialAux blob (i + 1) count)
    | .error _ => throw (.invalidFieldElement (some i))

/-- Convert a blob to a sequence of `Fr` field elements. Throws if the
blob is the wrong size or any 32-byte chunk represents a value
`≥ BLS_MODULUS`. -/
def blobToPolynomial (blob : Blob) : Except KzgError Polynomial := do
  if blob.size ≠ BYTES_PER_BLOB then
    throw (.badBlobSize blob.size)
  return (← blobToPolynomialAux blob 0 FIELD_ELEMENTS_PER_BLOB).toArray

/-! ## Evaluating a polynomial in evaluation form -/

/-- The bit-reversed `size`-th roots of unity. Recomputed on every call. -/
def rootsOfUnityBrp (size : Nat) : Array Fr :=
  bitReversalPermutation (computeRootsOfUnity size)

/-- Barycentric sum `Σ_j p[i+j] * D[i+j] / (z - D[i+j])` over `count`
terms, accumulated left-to-right onto `acc`. -/
def barycentricSumAux (polynomial domain : Array Fr) (z : Fr) :
    Fr → Nat → Nat → Fr
  | acc, _, 0 => acc
  | acc, i, count + 1 =>
    let a := polynomial[i]! * domain[i]!
    let b := z - domain[i]!
    barycentricSumAux polynomial domain z (acc + a / b) (i + 1) count

/-- `evaluatePolynomialInEvaluationForm` over an explicit evaluation
domain. -/
def evaluatePolynomialInEvaluationFormAux
    (polynomial domain : Array Fr) (z : Fr) : Fr :=
  let width := polynomial.size
  let inverseWidth := (Fr.ofNat width).inverse
  match domain.idxOf? z with
  -- Fast path: z is in the domain.
  | some i => polynomial[i]!
  | none =>
    -- Barycentric formula.
    let acc := barycentricSumAux polynomial domain z Fr.zero 0 width
    let r := z ^ (Fr.ofNat width) - Fr.one
    acc * r * inverseWidth

/-- Evaluate an evaluation-form polynomial at `z`. Indexes directly when
`z` is in the domain; otherwise uses the barycentric formula
`f(z) = (z^WIDTH − 1) / WIDTH · Σ_i (f(D[i]) · D[i]) / (z − D[i])`. -/
def evaluatePolynomialInEvaluationForm
    (polynomial : Polynomial) (z : Fr) : Fr :=
  -- Caller must pass `polynomial.size == FIELD_ELEMENTS_PER_BLOB`; the
  -- public entry points enforce this, so we don't re-check here.
  evaluatePolynomialInEvaluationFormAux polynomial
    (rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB) z

end EthCryptographySpecs.Kzg
