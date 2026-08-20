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

/-- Shift `h` such that cell `cellIndex` is evaluated on the coset `h·G`,
where `G` is the order-`FIELD_ELEMENTS_PER_CELL` subgroup. -/
private def cosetShiftForCell (cellIndex : CellIndex) : Fr :=
  let domain := rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB
  domain[FIELD_ELEMENTS_PER_CELL * cellIndex]!

/-- The full evaluation coset for cell `cellIndex`. -/
def cosetForCell (cellIndex : CellIndex) : Coset :=
  let domain := rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB
  let start := FIELD_ELEMENTS_PER_CELL * cellIndex
  Array.ofFn (n := FIELD_ELEMENTS_PER_CELL) fun i => domain[start + i.val]!

/-- Compute a KZG multi-evaluation proof for a set of `k` points.
For `Z(X)` the vanishing polynomial on `zs`, division gives
`f(X) = Q(X) * Z(X) + I(X)`, where the remainder `I(X)` is the
degree-`< k` interpolation polynomial through the evaluations at `zs`.
The proof commits to the quotient `Q(X)`. -/
private def computeKzgProofMultiImpl
    (polynomialCoeff : PolynomialCoeff) (zs : Coset) : KzgM (KZGProof × CosetEvals) := do
  let setup ← TrustedSetup.get!
  let ys : CosetEvals := zs.map (evaluatePolynomialcoeff polynomialCoeff)
  let denominator := vanishingPolynomialcoeff zs
  let quotient := dividePolynomialcoeff polynomialCoeff denominator
  let monomial := setup.g1MonomialBytes
  let proof ← g1Lincomb (monomial.extract 0 quotient.size) quotient
  return (proof, ys)

/-- Reed-Solomon-extend `blob` and return its cells. -/
def computeCells (blob : Blob) : KzgM (Array Cell) := do
  if blob.size ≠ BYTES_PER_BLOB then
    throw (.badBlobSize blob.size)
  let polynomial ← blobToPolynomial blob
  let polynomialCoeff := polynomialEvalToCoeff polynomial
  return Array.ofFn (n := CELLS_PER_EXT_BLOB) fun i =>
    let coset := cosetForCell i.val
    cosetEvalsToCell (coset.map (evaluatePolynomialcoeff polynomialCoeff))

/-- Compute cells and proofs for a polynomial in coefficient form. -/
def computeCellsAndKzgProofsPolynomialcoeff
    (polynomialCoeff : PolynomialCoeff) : KzgM (Array Cell × Array KZGProof) := do
  let pairs ← (Array.range CELLS_PER_EXT_BLOB).mapM fun i => do
    let (proof, ys) ← computeKzgProofMultiImpl polynomialCoeff (cosetForCell i)
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

/-- Verify that a set of cells belong to their corresponding commitment.
The pairing equation has six accumulator terms, named LL, LR, RL, RLC,
RLI, RLP in the comments below. -/
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
  let weights : Array Fr := (Array.range numCells).foldl
    (init := Array.replicate numCommitments Fr.zero)
    fun weights k =>
      let i := commitmentIndices[k]!
      weights.set! i (weights[i]! + rPowers[k]!)

  -- Step 4.1b: RLC = Σ_i weights[i] commitments[i].
  let rlc : G1 := (Bls.G1.uncompress (← g1Lincomb commitments weights)).toOption.get!

  -- Step 4.2: RLI = [Σ_k r^k I_k(s)].
  let sumInterp : PolynomialCoeff := (Array.range numCells).foldl
    (init := Array.replicate n Fr.zero)
    fun sumInterp k =>
      let interp := interpolatePolynomialcoeff
        (cosetForCell cellIndices[k]!) cosetsEvals[k]!
      let scaled := multiplyPolynomialcoeff #[rPowers[k]!] interp
      addPolynomialcoeff sumInterp scaled
  let rli : G1 := (Bls.G1.uncompress
                  (← g1Lincomb (setup.g1MonomialBytes.extract 0 n) sumInterp)).toOption.get!

  -- Step 4.3: RLP = Σ_k (r^k * h_k^n) proofs[k].
  let weightedRPowers : Array Fr := Array.ofFn (n := numCells) fun k =>
    let h_k := cosetShiftForCell cellIndices[k.val]!
    rPowers[k.val]! * (h_k ^ (Fr.ofNat n))
  let rlp : G1 := (Bls.G1.uncompress (← g1Lincomb proofs weightedRPowers)).toOption.get!

  -- Step 4.4: RL = RLC - RLI + RLP.
  let rl : G1 := Bls.G1.add (Bls.G1.add rlc (Bls.G1.neg rli)) rlp

  -- Step 5: pairing(LL, LR) = pairing(RL, [1]).
  return Bls.pairingCheck #[
    (ll, lr),
    (rl, Bls.G2.neg setup.g2Monomial[0]!)
  ]

/-- Verify that a set of cells belong to their corresponding commitments.
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
