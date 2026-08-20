import EthCryptographySpecs.Bls
import EthCryptographySpecs.Kzg.Constants
import EthCryptographySpecs.Kzg.BitReversal
import EthCryptographySpecs.Kzg.Polynomials
import EthCryptographySpecs.Kzg.TrustedSetup
import EthCryptographySpecs.Kzg.Errors

/-!
# `Kzg.Core`

The blob-commitment surface of KZG. Public methods live in `KzgM`
(`ExceptT KzgError IO`) because they read the loaded trusted setup and
report typed domain errors; internal helpers that only manipulate field
elements remain pure.
-/

namespace EthCryptographySpecs.Kzg

open EthCryptographySpecs.Kzg.Constants
open EthCryptographySpecs.Kzg.BitReversal
open EthCryptographySpecs.Bls (G1 G2 Fr)

/-! ## Type aliases

`KZGCommitment` and `KZGProof` are `Bytes48` aliases, kept as
`ByteArray` for direct interop with public method signatures. -/

abbrev G1Point       := ByteArray
abbrev G2Point       := ByteArray
abbrev KZGCommitment := ByteArray
abbrev KZGProof      := ByteArray

/-! ## Validation -/

/-- BLS validation, allowing the point at infinity. -/
def validateKzgG1 (b : Bytes48) : Bool :=
  if b == G1_POINT_AT_INFINITY then true
  else (Bls.G1.keyValidate b).isOk

/-- Validate untrusted bytes as a `KZGCommitment`. -/
def bytesToKzgCommitment (b : Bytes48) : Except KzgError KZGCommitment :=
  if validateKzgG1 b then .ok b else .error (.invalidCommitment none)

/-- Validate untrusted bytes as a `KZGProof`. -/
def bytesToKzgProof (b : Bytes48) : Except KzgError KZGProof :=
  if validateKzgG1 b then .ok b else .error (.invalidProof none)

/-- Fiat-Shamir challenge for a (blob, commitment) pair. -/
def computeChallenge (blob : Blob) (commitment : KZGCommitment) : Fr :=
  let degreePoly := intToBytesBE FIELD_ELEMENTS_PER_BLOB 16
  let data := FIAT_SHAMIR_PROTOCOL_DOMAIN ++ degreePoly ++ blob ++ commitment
  Fr.hashToBlsField data

/-- BLS multi-scalar multiplication in G1, on compressed-point inputs. -/
def g1Lincomb
    (points : Array KZGCommitment) (scalars : Array Fr) : KzgM KZGCommitment := do
  if points.size ≠ scalars.size then
    throw (.lincombLengthMismatch points.size scalars.size)
  if points.size = 0 then
    return Bls.G1.compress Bls.G1.zero
  let pointsG1 := points.map (fun p => (Bls.G1.uncompress p).toOption.get!)
  return Bls.G1.compress (Bls.G1.msm pointsG1 scalars)

/-- Given `y == p(z)`, compute `q(z)` for the KZG quotient polynomial,
handling the special case where `z` is in the roots of unity. -/
private def computeQuotientEvalWithinDomain
    (z : Fr) (polynomial : Polynomial) (y : Fr)
    : Fr :=
  let domain := rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB
  (Array.range domain.size).foldl (init := Fr.zero) fun result i =>
    let omega_i := domain[i]!
    if omega_i == z then
      result
    else
      let f_i := polynomial[i]! - y
      let numerator := f_i * omega_i
      let denominator := z * (z - omega_i)
      result + (numerator / denominator)

/-- Returns the KZG proof at `z` and the evaluation `y = p(z)`. -/
private def computeKzgProofImpl
    (polynomial : Polynomial) (z : Fr) : KzgM (KZGProof × Fr) := do
  let setup ← TrustedSetup.get!
  let g1LagrangeBrp := bitReversalPermutation setup.g1LagrangeBytes
  let domain := rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB

  -- For all x_i, compute p(x_i) - p(z).
  let y := evaluatePolynomialInEvaluationForm polynomial z
  let polynomialShifted := polynomial.map (· - y)

  -- For all x_i, compute (x_i - z).
  let denominatorPoly := domain.map (· - z)

  -- Quotient polynomial directly in evaluation form.
  let quotient : Array Fr := Array.ofFn (n := FIELD_ELEMENTS_PER_BLOB) fun i =>
    let a := polynomialShifted[i.val]!
    let b := denominatorPoly[i.val]!
    if b.isZero then
      -- z lands on a root of unity; use the special-case formula.
      computeQuotientEvalWithinDomain domain[i.val]! polynomial y
    else
      a / b

  let proof ← g1Lincomb g1LagrangeBrp quotient
  return (proof, y)

/-- Compute a KZG proof at `z` for the polynomial represented by `blob`.
Returns `(proof, y_bytes)`, where `y_bytes` is the 32-byte big-endian
encoding of `p(z)`. -/
def computeKzgProof (blob : Blob) (zBytes : Bytes32) : KzgM (KZGProof × Bytes32) := do
  if blob.size ≠ BYTES_PER_BLOB then
    throw (.badBlobSize blob.size)
  if zBytes.size ≠ BYTES_PER_FIELD_ELEMENT then
    throw (.badFieldElementSize zBytes.size)
  let polynomial ← blobToPolynomial blob
  let z ← bytesToBlsField zBytes
  let (proof, y) ← computeKzgProofImpl polynomial z
  return (proof, blsFieldToBytes y)

/-- Verify a KZG proof that `p(z) == y`, where `p(x)` is the polynomial
committed to in `commitment`. Checks the pairing equation
`e(P - [y], -[1]) * e(proof, [s] - [z]) == 1`. -/
private def verifyKzgProofImpl
    (commitment : KZGCommitment) (z y : Fr) (proof : KZGProof)
    : KzgM Bool := do
  let setup ← TrustedSetup.get!
  let s := setup.g2Monomial[1]!
  let X_minus_z : G2 := Bls.G2.add s (Bls.G2.mul Bls.G2.generator (-z))
  let P_minus_y : G1 := Bls.G1.add ((Bls.G1.uncompress commitment).toOption.get!)
                                   (Bls.G1.mul Bls.G1.generator (-y))
  let pairs : Array (G1 × G2) := #[
    (P_minus_y, Bls.G2.neg Bls.G2.generator),
    ((Bls.G1.uncompress proof).toOption.get!, X_minus_z)
  ]
  return Bls.pairingCheck pairs

/-- Verify a KZG proof, taking inputs as raw bytes. -/
def verifyKzgProof
    (commitmentBytes : Bytes48) (zBytes yBytes : Bytes32) (proofBytes : Bytes48)
    : KzgM Bool := do
  if commitmentBytes.size ≠ BYTES_PER_COMMITMENT then
    throw (.badCommitmentSize commitmentBytes.size)
  if zBytes.size ≠ BYTES_PER_FIELD_ELEMENT then
    throw (.badFieldElementSize zBytes.size)
  if yBytes.size ≠ BYTES_PER_FIELD_ELEMENT then
    throw (.badFieldElementSize yBytes.size)
  if proofBytes.size ≠ BYTES_PER_PROOF then
    throw (.badProofSize proofBytes.size)
  let commitment ← bytesToKzgCommitment commitmentBytes
  let proof ← bytesToKzgProof proofBytes
  let z ← bytesToBlsField zBytes
  let y ← bytesToBlsField yBytes
  verifyKzgProofImpl commitment z y proof

/-- Verify multiple KZG proofs efficiently using a random linear combination. -/
private def verifyKzgProofBatch
    (commitments : Array KZGCommitment)
    (zs ys : Array Fr)
    (proofs : Array KZGProof) : KzgM Bool := do
  if zs.size ≠ commitments.size then
    throw (.inputLengthMismatch "zs" commitments.size zs.size)
  if ys.size ≠ commitments.size then
    throw (.inputLengthMismatch "ys" commitments.size ys.size)
  if proofs.size ≠ commitments.size then
    throw (.inputLengthMismatch "proofs" commitments.size proofs.size)
  let setup ← TrustedSetup.get!

  -- Random challenge: deterministic via Fiat-Shamir.
  let degreePoly := intToBytesBE FIELD_ELEMENTS_PER_BLOB 8
  let numCommitments := intToBytesBE commitments.size 8
  let data := (Array.range commitments.size).foldl
    (init := RANDOM_CHALLENGE_KZG_BATCH_DOMAIN ++ degreePoly ++ numCommitments)
    fun data i => data
        ++ commitments[i]!
        ++ blsFieldToBytes zs[i]!
        ++ blsFieldToBytes ys[i]!
        ++ proofs[i]!
  let r := Fr.hashToBlsField data
  let rPowers := computePowers r commitments.size

  -- proof_lincomb = Σ_i r^i · proof_i
  let proofLincomb ← g1Lincomb proofs rPowers
  -- proof_z_lincomb = Σ_i (z_i · r^i) · proof_i
  let zRPowers := Array.ofFn (n := zs.size) fun i => zs[i.val]! * rPowers[i.val]!
  let proofZLincomb ← g1Lincomb proofs zRPowers

  -- C_minus_ys[i] = commitment_i - [y_i]
  let cMinusYs : Array G1 := Array.ofFn (n := commitments.size) fun i =>
    Bls.G1.add ((Bls.G1.uncompress commitments[i.val]!).toOption.get!)
               (Bls.G1.mul Bls.G1.generator (-ys[i.val]!))
  let cMinusYBytes := cMinusYs.map Bls.G1.compress
  let cMinusYLincomb ← g1Lincomb cMinusYBytes rPowers

  let s := setup.g2Monomial[1]!
  let pairs : Array (G1 × G2) := #[
    ( (Bls.G1.uncompress proofLincomb).toOption.get!, Bls.G2.neg s ),
    ( Bls.G1.add ((Bls.G1.uncompress cMinusYLincomb).toOption.get!)
                 ((Bls.G1.uncompress proofZLincomb).toOption.get!)
    , Bls.G2.generator )
  ]
  return Bls.pairingCheck pairs

/-- Compute a KZG commitment from a blob. -/
def blobToKzgCommitment (blob : Blob) : KzgM KZGCommitment := do
  if blob.size ≠ BYTES_PER_BLOB then
    throw (.badBlobSize blob.size)
  let setup ← TrustedSetup.get!
  let polynomial ← blobToPolynomial blob
  let lagrangeBrp := bitReversalPermutation setup.g1LagrangeBytes
  g1Lincomb lagrangeBrp polynomial

/-- Compute the KZG proof verifying `blob` against `commitment`. Does
not check that `commitment` is correct for `blob`. -/
def computeBlobKzgProof (blob : Blob) (commitmentBytes : Bytes48) : KzgM KZGProof := do
  if blob.size ≠ BYTES_PER_BLOB then
    throw (.badBlobSize blob.size)
  if commitmentBytes.size ≠ BYTES_PER_COMMITMENT then
    throw (.badCommitmentSize commitmentBytes.size)
  let commitment ← bytesToKzgCommitment commitmentBytes
  let polynomial ← blobToPolynomial blob
  let evaluationChallenge := computeChallenge blob commitment
  let (proof, _) ← computeKzgProofImpl polynomial evaluationChallenge
  return proof

/-- Verify that `blob` corresponds to `commitment` via `proof`. -/
def verifyBlobKzgProof
    (blob : Blob) (commitmentBytes : Bytes48) (proofBytes : Bytes48)
    : KzgM Bool := do
  if blob.size ≠ BYTES_PER_BLOB then
    throw (.badBlobSize blob.size)
  if commitmentBytes.size ≠ BYTES_PER_COMMITMENT then
    throw (.badCommitmentSize commitmentBytes.size)
  if proofBytes.size ≠ BYTES_PER_PROOF then
    throw (.badProofSize proofBytes.size)
  let commitment ← bytesToKzgCommitment commitmentBytes
  let polynomial ← blobToPolynomial blob
  let evaluationChallenge := computeChallenge blob commitment
  let y := evaluatePolynomialInEvaluationForm polynomial evaluationChallenge
  let proof ← bytesToKzgProof proofBytes
  verifyKzgProofImpl commitment evaluationChallenge y proof

/-- Verify a batch of (blob, commitment, proof) triples. Returns `true`
for the empty input. -/
def verifyBlobKzgProofBatch
    (blobs : Array Blob)
    (commitmentsBytes : Array Bytes48)
    (proofsBytes : Array Bytes48) : KzgM Bool := do
  if commitmentsBytes.size ≠ blobs.size then
    throw (.inputLengthMismatch "commitmentsBytes" blobs.size commitmentsBytes.size)
  if proofsBytes.size ≠ blobs.size then
    throw (.inputLengthMismatch "proofsBytes" blobs.size proofsBytes.size)

  let (commitments, challenges, ys, proofs) ←
    (Array.range blobs.size).foldlM
      (init := ((#[] : Array KZGCommitment), (#[] : Array Fr),
                (#[] : Array Fr), (#[] : Array KZGProof)))
      fun (commitments, challenges, ys, proofs) i => do
        let blob := blobs[i]!
        let cb := commitmentsBytes[i]!
        let pb := proofsBytes[i]!
        if blob.size ≠ BYTES_PER_BLOB then
          throw (.badBlobSize blob.size)
        if cb.size ≠ BYTES_PER_COMMITMENT then
          throw (.badCommitmentSize cb.size)
        if pb.size ≠ BYTES_PER_PROOF then
          throw (.badProofSize pb.size)

        let commitment ← match bytesToKzgCommitment cb with
                         | .ok c    => pure c
                         | .error _ => throw (.invalidCommitment (some i))
        let proof ← match bytesToKzgProof pb with
                    | .ok p    => pure p
                    | .error _ => throw (.invalidProof (some i))

        let polynomial ← blobToPolynomial blob
        let challenge := computeChallenge blob commitment
        let y := evaluatePolynomialInEvaluationForm polynomial challenge

        pure (commitments.push commitment, challenges.push challenge,
              ys.push y, proofs.push proof)

  verifyKzgProofBatch commitments challenges ys proofs

end EthCryptographySpecs.Kzg
