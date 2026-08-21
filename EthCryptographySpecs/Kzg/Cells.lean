import EthCryptographySpecs.Bls
import EthCryptographySpecs.Kzg.Constants
import EthCryptographySpecs.Kzg.BitReversal
import EthCryptographySpecs.Kzg.Polynomials
import EthCryptographySpecs.Kzg.Fft
import EthCryptographySpecs.Kzg.Core
import EthCryptographySpecs.Kzg.TrustedSetup
import EthCryptographySpecs.Kzg.Errors

/-!
# `Cells`

Cell proofs over a Reed-Solomon-extended blob. The extended
polynomial is split into `CELLS_PER_EXT_BLOB` cosets of
`FIELD_ELEMENTS_PER_CELL` evaluations each; each cell carries an
independent KZG multi-evaluation proof, so verifiers can sample any
subset of cells without downloading the full blob.
-/

namespace EthCryptographySpecs.Kzg

open EthCryptographySpecs.Kzg.Constants
open EthCryptographySpecs.Kzg.BitReversal
open EthCryptographySpecs.Bls (G1 G2 Fr)

/-! ## Type aliases -/

abbrev Cell             := ByteArray
abbrev CellIndex        := Nat
abbrev CommitmentIndex  := Nat
abbrev Coset            := Array Fr
abbrev CosetEvals       := Array Fr

/-- Convert an untrusted `Cell` into a trusted `CosetEvals`. -/
def cellToCosetEvals (cell : Cell) : Except KzgError CosetEvals := do
  if cell.size ≠ BYTES_PER_CELL then
    throw (.badCellSize cell.size)
  (Array.range FIELD_ELEMENTS_PER_CELL).mapM fun i =>
    let s := i * BYTES_PER_FIELD_ELEMENT
    let e := (i + 1) * BYTES_PER_FIELD_ELEMENT
    match bytesToBlsField (cell.extract s e) with
    | .ok f    => pure f
    | .error _ => throw (.invalidFieldElement (some i))

/-- Convert a trusted `CosetEvals` back into an untrusted `Cell`. -/
def cosetEvalsToCell (cosetEvals : CosetEvals) : Cell :=
  (Array.range FIELD_ELEMENTS_PER_CELL).foldl
    (init := ByteArray.empty)
    fun bytes i => bytes ++ blsFieldToBytes cosetEvals[i]!

/-! ## Cell cosets -/

/-- Get the shift that determines the coset for a given `cellIndex`.
Precisely, consider the group of roots of unity of order
`FIELD_ELEMENTS_PER_CELL * CELLS_PER_EXT_BLOB`.
Let `G = {1, g, g^2, ...}` denote its subgroup of order `FIELD_ELEMENTS_PER_CELL`.
Then, the coset is defined as `h * G = {h, hg, hg^2, ...}` for an element `h`.
This function returns `h`. -/
private def cosetShiftForCell (cellIndex : CellIndex) : Except KzgError Fr := do
  if cellIndex ≥ CELLS_PER_EXT_BLOB then
    throw .cellIndexOutOfBounds
  let domain := rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB
  return domain[FIELD_ELEMENTS_PER_CELL * cellIndex]!

/-- Get the coset for a given `cellIndex`.
Precisely, consider the group of roots of unity of order
`FIELD_ELEMENTS_PER_CELL * CELLS_PER_EXT_BLOB`.
Let `G = {1, g, g^2, ...}` denote its subgroup of order `FIELD_ELEMENTS_PER_CELL`.
Then, the coset is defined as `h * G = {h, hg, hg^2, ...}`.
This function, returns the coset. -/
def cosetForCell (cellIndex : CellIndex) : Except KzgError Coset := do
  if cellIndex ≥ CELLS_PER_EXT_BLOB then
    throw .cellIndexOutOfBounds
  let domain := rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB
  let start := FIELD_ELEMENTS_PER_CELL * cellIndex
  return Array.ofFn (n := FIELD_ELEMENTS_PER_CELL) fun i => domain[start + i.val]!

/-- Compute a KZG multi-evaluation proof for a set of `k` points.

This is done by committing to the following quotient polynomial:
`Q(X) = f(X) - I(X) / Z(X)`
Where:
- `I(X)` is the degree `k-1` polynomial that agrees with `f(x)` at all `k` points
- `Z(X)` is the degree `k` polynomial that evaluates to zero on all `k` points

We further note that since the degree of `I(X)` is less than the degree of
`Z(X)`, the computation can be simplified in monomial form to
`Q(X) = f(X) / Z(X)`. -/
private def computeKzgProofMultiImpl
    (polynomialCoeff : PolynomialCoeff) (zs : Coset) : KzgM (KZGProof × CosetEvals) := do
  let setup ← TrustedSetup.get!
  -- For all points, compute the evaluation of those points.
  let ys : CosetEvals := zs.map (evaluatePolynomialcoeff polynomialCoeff)
  -- Compute Z(X).
  let denominator ← vanishingPolynomialcoeff zs
  -- Compute the quotient polynomial directly in monomial form.
  let quotient ← dividePolynomialcoeff polynomialCoeff denominator
  let monomial := setup.g1MonomialBytes
  let proof ← g1Lincomb (monomial.extract 0 quotient.size) quotient
  return (proof, ys)

/-- Reed-Solomon-extend `blob` and return its cells. -/
def computeCells (blob : Blob) : KzgM (Array Cell) := do
  if blob.size ≠ BYTES_PER_BLOB then
    throw (.badBlobSize blob.size)
  let polynomial ← blobToPolynomial blob
  let polynomialCoeff := polynomialEvalToCoeff polynomial
  (Array.range CELLS_PER_EXT_BLOB).mapM fun i => do
    let coset ← cosetForCell i
    pure (cosetEvalsToCell (coset.map (evaluatePolynomialcoeff polynomialCoeff)))

/-- Compute cells and proofs for a polynomial in coefficient form. -/
def computeCellsAndKzgProofsPolynomialcoeff
    (polynomialCoeff : PolynomialCoeff) : KzgM (Array Cell × Array KZGProof) := do
  let pairs ← (Array.range CELLS_PER_EXT_BLOB).mapM fun i => do
    let (proof, ys) ← computeKzgProofMultiImpl polynomialCoeff (← cosetForCell i)
    pure (cosetEvalsToCell ys, proof)
  return (pairs.map (·.1), pairs.map (·.2))

/-- Compute all cell proofs for an extended blob. Naive O(n²);
optimal implementations use FK20. -/
def computeCellsAndKzgProofs
    (blob : Blob) : KzgM (Array Cell × Array KZGProof) := do
  if blob.size ≠ BYTES_PER_BLOB then
    throw (.badBlobSize blob.size)
  let polynomial ← blobToPolynomial blob
  let polynomialCoeff := polynomialEvalToCoeff polynomial
  computeCellsAndKzgProofsPolynomialcoeff polynomialCoeff

/-- Random challenge `r` used in the universal verification equation. -/
def computeVerifyCellKzgProofBatchChallenge
    (commitments : Array KZGCommitment)
    (commitmentIndices : Array CommitmentIndex)
    (cellIndices : Array CellIndex)
    (cosetsEvals : Array CosetEvals)
    (proofs : Array KZGProof) : Fr :=
  let h := RANDOM_CHALLENGE_KZG_CELL_BATCH_DOMAIN
    ++ intToBytesBE FIELD_ELEMENTS_PER_BLOB 8
    ++ intToBytesBE FIELD_ELEMENTS_PER_CELL 8
    ++ intToBytesBE commitments.size 8
    ++ intToBytesBE cellIndices.size 8
  let h := commitments.foldl (init := h) fun h c => h ++ c
  let h := (Array.range cosetsEvals.size).foldl (init := h) fun h k =>
    let h := h ++ intToBytesBE commitmentIndices[k]! 8
    let h := h ++ intToBytesBE cellIndices[k]! 8
    let h := cosetsEvals[k]!.foldl (init := h) fun h ce =>
      h ++ blsFieldToBytes ce
    h ++ proofs[k]!
  Fr.hashToBlsField h

/-- Helper: Verify that a set of cells belong to their corresponding commitment.

Given a list of `commitments` (which contains no duplicates) and four lists
representing tuples of (`commitmentIndex`, `cellIndex`, `evals`, `proof`), the
function verifies `proof` which shows that `evals` are the evaluations of the
polynomial associated with `commitments[commitmentIndex]`, evaluated over the
domain specified by `cellIndex`.

This function is the internal implementation of `verifyCellKzgProofBatch`. -/
def verifyCellKzgProofBatchImpl
    (commitments : Array KZGCommitment)
    (commitmentIndices : Array CommitmentIndex)
    (cellIndices : Array CellIndex)
    (cosetsEvals : Array CosetEvals)
    (proofs : Array KZGProof) : KzgM Bool := do
  -- Length and bounds checks.
  if cellIndices.size ≠ commitmentIndices.size then
    throw (.inputLengthMismatch "cellIndices" commitmentIndices.size cellIndices.size)
  if cosetsEvals.size ≠ commitmentIndices.size then
    throw (.inputLengthMismatch "cosetsEvals" commitmentIndices.size cosetsEvals.size)
  if proofs.size ≠ commitmentIndices.size then
    throw (.inputLengthMismatch "proofs" commitmentIndices.size proofs.size)
  if commitmentIndices.any (· ≥ commitments.size) then
    throw .commitmentIndexOutOfBounds
  -- The commitments list must contain no duplicates
  if (Array.range commitments.size).any
      (fun i => commitments.idxOf? commitments[i]! ≠ some i) then
    throw .duplicateCommitments

  -- The verification equation that we will check is pairing (LL, LR) = pairing (RL, [1]), where
  -- LL = sum_k r^k proofs[k],
  -- LR = [s^n]
  -- RL = RLC - RLI + RLP, where
  --   RLC = sum_i weights[i] commitments[i]
  --   RLI = [sum_k r^k interpolation_poly_k(s)]
  --   RLP = sum_k (r^k * h_k^n) proofs[k]
  --
  -- Here, the variables have the following meaning:
  -- - k < cellIndices.size is an index iterating over all cells in the input
  -- - r is a random coefficient, derived from hashing all data provided by the prover
  -- - s is the secret embedded in the KZG setup
  -- - n = FIELD_ELEMENTS_PER_CELL is the size of the evaluation domain
  -- - i ranges over all provided commitments
  -- - weights[i] is a weight computed for commitment i
  --   - It depends on r and on which cells are associated with commitment i
  -- - interpolation_poly_k is the interpolation polynomial for the kth cell
  -- - h_k is the coset shift specifying the evaluation domain of the kth cell

  let setup ← TrustedSetup.get!
  let numCells := cellIndices.size
  let n := FIELD_ELEMENTS_PER_CELL
  let numCommitments := commitments.size

  -- Step 1: r and r^0..r^(num_cells-1).
  let r := computeVerifyCellKzgProofBatchChallenge
            commitments commitmentIndices cellIndices cosetsEvals proofs
  let rPowers := computePowers r numCells

  -- Step 2: LL = Σ_k r^k proofs[k].
  let ll : G1 := (Bls.G1.uncompress (← g1Lincomb proofs rPowers)).toOption.get!

  -- Step 3: LR = [s^n].
  let lr : G2 := setup.g2Monomial[n]!

  -- Step 4.1: weights[i] = Σ_{k : commitmentIndices[k] = i} r^k.
  -- Note: we do that by iterating over all k and updating the correct
  -- weights[i] accordingly.
  let weights : Array Fr := (Array.range numCells).foldl
    (init := Array.replicate numCommitments Fr.zero)
    fun weights k =>
      let i := commitmentIndices[k]!
      weights.set! i (weights[i]! + rPowers[k]!)

  -- Step 4.1b: RLC = Σ_i weights[i] commitments[i].
  let rlc : G1 := (Bls.G1.uncompress (← g1Lincomb commitments weights)).toOption.get!

  -- Step 4.2: RLI = [Σ_k r^k I_k(s)].
  -- Note: an efficient implementation would use the IDFT based method
  -- explained in the blog post linked in `verifyCellKzgProofBatch`.
  let sumInterp : PolynomialCoeff ← (Array.range numCells).foldlM
    (init := Array.replicate n Fr.zero)
    fun sumInterp k => do
      let interp ← interpolatePolynomialcoeff
        (← cosetForCell cellIndices[k]!) cosetsEvals[k]!
      let scaled ← multiplyPolynomialcoeff #[rPowers[k]!] interp
      pure (addPolynomialcoeff sumInterp scaled)
  let rli : G1 := (Bls.G1.uncompress
                  (← g1Lincomb (setup.g1MonomialBytes.extract 0 n) sumInterp)).toOption.get!

  -- Step 4.3: RLP = Σ_k (r^k * h_k^n) proofs[k].
  let weightedRPowers : Array Fr ← (Array.range numCells).mapM fun k => do
    let h_k ← cosetShiftForCell cellIndices[k]!
    pure (rPowers[k]! * (h_k ^ (Fr.ofNat n)))
  let rlp : G1 := (Bls.G1.uncompress (← g1Lincomb proofs weightedRPowers)).toOption.get!

  -- Step 4.4: RL = RLC - RLI + RLP.
  let rl : G1 := Bls.G1.add (Bls.G1.add rlc (Bls.G1.neg rli)) rlp

  -- Step 5: pairing(LL, LR) = pairing(RL, [1]).
  return Bls.pairingCheck #[
    (ll, lr),
    (rl, Bls.G2.neg setup.g2Monomial[0]!)
  ]

/-- Verify that a set of cells belong to their corresponding commitments.

Given four lists representing tuples of (`commitment`, `cellIndex`, `cell`,
`proof`), the function verifies `proof` which shows that `cell` are the
evaluations of the polynomial associated with `commitment`, evaluated over the
domain specified by `cellIndex`.

This function implements the universal verification equation that has been
introduced here:
https://ethresear.ch/t/a-universal-verification-equation-for-data-availability-sampling/13240

Deduplicates `commitmentsBytes` and forwards into
`verifyCellKzgProofBatchImpl`. -/
def verifyCellKzgProofBatch
    (commitmentsBytes : Array Bytes48)
    (cellIndices : Array CellIndex)
    (cells : Array Cell)
    (proofsBytes : Array Bytes48) : KzgM Bool := do

  if cells.size ≠ commitmentsBytes.size then
    throw (.inputLengthMismatch "cells" commitmentsBytes.size cells.size)
  if proofsBytes.size ≠ commitmentsBytes.size then
    throw (.inputLengthMismatch "proofsBytes" commitmentsBytes.size proofsBytes.size)
  if cellIndices.size ≠ commitmentsBytes.size then
    throw (.inputLengthMismatch "cellIndices" commitmentsBytes.size cellIndices.size)

  if let some cb := commitmentsBytes.find? (fun cb => cb.size != BYTES_PER_COMMITMENT) then
    throw (.badCommitmentSize cb.size)
  if cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) then
    throw .cellIndexOutOfBounds
  if let some c := cells.find? (fun c => c.size != BYTES_PER_CELL) then
    throw (.badCellSize c.size)
  if let some pb := proofsBytes.find? (fun pb => pb.size != BYTES_PER_PROOF) then
    throw (.badProofSize pb.size)

  -- Deduplicate commitments while preserving the index of first occurrence.
  -- We use a simple linear scan (`idxOf?`); the input list of commitments
  -- tends to be short relative to the cell list.
  let (deduped, commitmentIndices) ←
    (Array.range commitmentsBytes.size).foldlM
      (init := ((#[] : Array KZGCommitment), (#[] : Array CommitmentIndex)))
      fun (deduped, commitmentIndices) i => do
        let cb := commitmentsBytes[i]!
        -- Validate (also acts as `bytes_to_kzg_commitment`).
        let _ ← match bytesToKzgCommitment cb with
                | .ok c    => pure c
                | .error _ => throw (.invalidCommitment (some i))
        -- Find or append.
        match deduped.idxOf? cb with
        | some j => pure (deduped, commitmentIndices.push j)
        | none   => pure (deduped.push cb, commitmentIndices.push deduped.size)

  -- Convert cells to coset evaluations.
  let cosetsEvals : Array CosetEvals ← cells.mapM fun c =>
    cellToCosetEvals c

  -- Validate proofs.
  let proofs : Array KZGProof ← (Array.range proofsBytes.size).mapM fun i =>
    match bytesToKzgProof proofsBytes[i]! with
    | .ok p    => pure p
    | .error _ => throw (.invalidProof (some i))

  verifyCellKzgProofBatchImpl deduped commitmentIndices cellIndices cosetsEvals proofs

end EthCryptographySpecs.Kzg
