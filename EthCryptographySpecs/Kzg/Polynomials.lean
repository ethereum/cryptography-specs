import EthCryptographySpecs.Bls
import EthCryptographySpecs.Kzg.Constants
import EthCryptographySpecs.Kzg.BitReversal
import EthCryptographySpecs.Kzg.Errors
import EthCryptographySpecs.Kzg.Fft

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

/-- Convert untrusted bytes to a trusted and validated BLS scalar field
element. This function does not accept inputs greater than the BLS modulus.
Throws if the input has the wrong size or the integer is `≥ BLS_MODULUS`. -/
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

/-! ## Polynomials in coefficient form -/

/-- Sum the coefficient-form polynomials `a` and `b`. -/
def addPolynomialcoeff (a b : PolynomialCoeff) : PolynomialCoeff :=
  let (a, b) := if a.size ≥ b.size then (a, b) else (b, a)
  Array.ofFn (n := a.size) fun i =>
    let bi := if i.val < b.size then b[i.val]! else Fr.zero
    a[i.val]! + bi

/-- Multiply the coefficient-form polynomials `a` and `b`. Throws if the
product would exceed `FIELD_ELEMENTS_PER_EXT_BLOB` coefficients. -/
def multiplyPolynomialcoeff (a b : PolynomialCoeff) :
    Except KzgError PolynomialCoeff := do
  if a.size + b.size > FIELD_ELEMENTS_PER_EXT_BLOB then
    throw (.polynomialProductTooLong a.size b.size)
  return (Array.range a.size).foldl (init := #[Fr.zero]) fun r power =>
    let coef := a[power]!
    let summand : PolynomialCoeff :=
      Array.replicate power Fr.zero ++ b.map (· * coef)
    addPolynomialcoeff r summand

/-- Long polynomial division for two coefficient-form polynomials.
Each step eliminates the current leading coefficient of `a` (at index
`apos`, descending) and prepends the quotient coefficient to `o`.
Throws on an empty divisor, and on a divisor with a zero leading
coefficient whenever the division loop would run. -/
def dividePolynomialcoeff (a b : PolynomialCoeff) :
    Except KzgError PolynomialCoeff := do
  -- An empty divisor is invalid.
  if b.size = 0 then
    throw .zeroDivisorPolynomial
  -- A zero leading coefficient would make every quotient step below a
  -- division by zero, silently yielding 0 (see the `Div Fr` docstring)
  -- instead of failing. Only reachable when the loop runs at least once.
  if a.size ≥ b.size ∧ b[b.size - 1]!.isZero then
    throw .zeroDivisorPolynomial
  let bpos := b.size - 1
  -- The divisor's leading coefficient is loop-invariant; precompute its
  -- inverse once instead of paying for a full Fermat exponentiation
  -- (~570 Fp muls) on every outer iteration.
  let bLeadInv := b[bpos]!.inverse
  -- One quotient coefficient per step, while `apos - t ≥ bpos`.
  let steps := a.size + 1 - max b.size 1
  let (_, o) := (Array.range steps).foldl
    (init := (a, (Array.empty : PolynomialCoeff)))
    fun (a, o) t =>
      let apos := a.size - 1 - t
      let diff := apos - bpos
      let quot := a[apos]! * bLeadInv
      let a := (Array.range b.size).foldl
        (fun a i => a.set! (diff + i) (a[diff + i]! - b[i]! * quot)) a
      (a, #[quot] ++ o)
  return o

/-- Lagrange interpolation: Finds the lowest degree polynomial that takes
the value `ys[i]` at `xs[i]` for all i. Outputs a coefficient form
polynomial. Leading coefficients may be zero.

The entries of `xs` must be pairwise distinct: the weights invert
`xs[i] - xs[j]`, and `Fr` inversion silently maps 0 to 0. -/
def interpolatePolynomialcoeff
    (xs ys : Array Fr) : Except KzgError PolynomialCoeff :=
  (Array.range xs.size).foldlM (init := #[Fr.zero]) fun r i => do
    let summand ← (Array.range ys.size).foldlM (init := #[ys[i]!])
      fun summand j =>
        if j ≠ i then
          let weightAdj := (xs[i]! - xs[j]!).inverse
          multiplyPolynomialcoeff summand #[(-weightAdj) * xs[j]!, weightAdj]
        else
          pure summand
    return addPolynomialcoeff r summand

/-- Compute the vanishing polynomial on `xs` (coefficient form). -/
def vanishingPolynomialcoeff (xs : Array Fr) : Except KzgError PolynomialCoeff :=
  xs.foldlM (init := #[Fr.one]) fun p x =>
    multiplyPolynomialcoeff p #[-x, Fr.one]

/-- Evaluate a coefficient-form polynomial at `z` using Horner's schema. -/
def evaluatePolynomialcoeff
    (polynomialCoeff : PolynomialCoeff) (z : Fr) : Fr :=
  let n := polynomialCoeff.size
  (Array.range n).foldl (init := Fr.zero) fun y i =>
    y * z + polynomialCoeff[n - 1 - i]!

/-- Convert evaluation form to coefficient form via inverse FFT. -/
def polynomialEvalToCoeff (polynomial : Polynomial) : PolynomialCoeff :=
  let roots := computeRootsOfUnity FIELD_ELEMENTS_PER_BLOB
  fftField (bitReversalPermutation polynomial) roots (inv := true)


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
terms, accumulated left-to-right onto `acc`. The caller must ensure `z` is
distinct from every visited `domain` entry — a zero denominator would
silently contribute `0` (see the `Div Fr` docstring). -/
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
    -- Barycentric formula. On this path `z ∉ domain`, and the domain (roots
    -- of unity) has no duplicates, so every `z - domain[i]` inside the sum is
    -- nonzero — otherwise the division would silently contribute 0.
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
