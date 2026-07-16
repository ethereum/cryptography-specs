import EthCryptographySpecs.Kzg.Cells
import EthCryptographySpecs.Proofs.Kzg.Polynomials

/-!
# Proofs: `Cells`

Shape properties of the coefficient-form helpers (`addPolynomialcoeff`
spans the longer input, `cosetForCell` yields a full cell of points),
canonicity of the batch challenge, and the validation surface of the
cell-proof entry points: each malformed input is rejected with exactly
the documented error before any real work.
-/

namespace EthCryptographySpecs.Kzg

open EthCryptographySpecs.Bls (Fr)
open EthCryptographySpecs.Kzg.Constants


/-- A cell's coset has exactly `FIELD_ELEMENTS_PER_CELL` points. -/
@[simp] theorem size_cosetForCell (cellIndex : CellIndex) :
    (cosetForCell cellIndex).size = FIELD_ELEMENTS_PER_CELL := by
  simp [cosetForCell]

/-- The cell-batch challenge is a canonical field element. -/
theorem val_computeVerifyCellKzgProofBatchChallenge_lt
    (commitments : Array KZGCommitment)
    (commitmentIndices : Array CommitmentIndex)
    (cellIndices : Array CellIndex)
    (cosetsEvals : Array CosetEvals)
    (proofs : Array KZGProof) :
    (computeVerifyCellKzgProofBatchChallenge commitments commitmentIndices
      cellIndices cosetsEvals proofs).val < Fr.modulus := by
  rw [computeVerifyCellKzgProofBatchChallenge]
  exact val_hashToBlsField_lt _

/-- `cellToCosetEvals` rejects a wrongly-sized cell. -/
theorem cellToCosetEvals_badCellSize {cell : Cell}
    (h : cell.size ≠ BYTES_PER_CELL) :
    cellToCosetEvals cell = throw (.badCellSize cell.size) := by
  simp [cellToCosetEvals, h]
  rfl

/-- `computeCells` rejects a wrongly-sized blob. -/
theorem computeCells_badBlobSize {blob : Blob}
    (h : blob.size ≠ BYTES_PER_BLOB) :
    computeCells blob = throw (.badBlobSize blob.size) := by
  simp [computeCells, h]
  rfl

/-- `computeCellsAndKzgProofs` rejects a wrongly-sized blob. -/
theorem computeCellsAndKzgProofs_badBlobSize {blob : Blob}
    (h : blob.size ≠ BYTES_PER_BLOB) :
    computeCellsAndKzgProofs blob = throw (.badBlobSize blob.size) := by
  simp [computeCellsAndKzgProofs, h]
  rfl

/-! ## `verifyCellKzgProofBatchImpl` validation -/

/-- Rejects a `cellIndices` array whose length does not match
`commitmentIndices`. -/
theorem verifyCellKzgProofBatchImpl_cellIndices_mismatch
    {commitments : Array KZGCommitment}
    {commitmentIndices : Array CommitmentIndex} {cellIndices : Array CellIndex}
    {cosetsEvals : Array CosetEvals} {proofs : Array KZGProof}
    (h : cellIndices.size ≠ commitmentIndices.size) :
    verifyCellKzgProofBatchImpl commitments commitmentIndices cellIndices
        cosetsEvals proofs
      = throw (.inputLengthMismatch "cellIndices" commitmentIndices.size
          cellIndices.size) := by
  simp [verifyCellKzgProofBatchImpl, h]
  rfl

/-- Rejects a `cosetsEvals` array whose length does not match
`commitmentIndices`. -/
theorem verifyCellKzgProofBatchImpl_cosetsEvals_mismatch
    {commitments : Array KZGCommitment}
    {commitmentIndices : Array CommitmentIndex} {cellIndices : Array CellIndex}
    {cosetsEvals : Array CosetEvals} {proofs : Array KZGProof}
    (hcell : cellIndices.size = commitmentIndices.size)
    (h : cosetsEvals.size ≠ commitmentIndices.size) :
    verifyCellKzgProofBatchImpl commitments commitmentIndices cellIndices
        cosetsEvals proofs
      = throw (.inputLengthMismatch "cosetsEvals" commitmentIndices.size
          cosetsEvals.size) := by
  simp [verifyCellKzgProofBatchImpl, hcell, h]
  rfl

/-- Rejects a `proofs` array whose length does not match
`commitmentIndices`. -/
theorem verifyCellKzgProofBatchImpl_proofs_mismatch
    {commitments : Array KZGCommitment}
    {commitmentIndices : Array CommitmentIndex} {cellIndices : Array CellIndex}
    {cosetsEvals : Array CosetEvals} {proofs : Array KZGProof}
    (hcell : cellIndices.size = commitmentIndices.size)
    (hcoset : cosetsEvals.size = commitmentIndices.size)
    (h : proofs.size ≠ commitmentIndices.size) :
    verifyCellKzgProofBatchImpl commitments commitmentIndices cellIndices
        cosetsEvals proofs
      = throw (.inputLengthMismatch "proofs" commitmentIndices.size
          proofs.size) := by
  simp [verifyCellKzgProofBatchImpl, hcell, hcoset, h]
  rfl

/-- Rejects a commitment index that is out of bounds. -/
theorem verifyCellKzgProofBatchImpl_commitmentIndexOutOfBounds
    {commitments : Array KZGCommitment}
    {commitmentIndices : Array CommitmentIndex} {cellIndices : Array CellIndex}
    {cosetsEvals : Array CosetEvals} {proofs : Array KZGProof}
    (hcell : cellIndices.size = commitmentIndices.size)
    (hcoset : cosetsEvals.size = commitmentIndices.size)
    (hproof : proofs.size = commitmentIndices.size)
    (h : commitmentIndices.any (· ≥ commitments.size) = true) :
    verifyCellKzgProofBatchImpl commitments commitmentIndices cellIndices
        cosetsEvals proofs
      = throw .commitmentIndexOutOfBounds := by
  simp [verifyCellKzgProofBatchImpl, hcell, hcoset, hproof, h]
  rfl

/-! ## `verifyCellKzgProofBatch` validation -/

/-- Rejects a `cells` array whose length does not match
`commitmentsBytes`. -/
theorem verifyCellKzgProofBatch_cells_mismatch
    {commitmentsBytes : Array Bytes48} {cellIndices : Array CellIndex}
    {cells : Array Cell} {proofsBytes : Array Bytes48}
    (h : cells.size ≠ commitmentsBytes.size) :
    verifyCellKzgProofBatch commitmentsBytes cellIndices cells proofsBytes
      = throw (.inputLengthMismatch "cells" commitmentsBytes.size
          cells.size) := by
  simp [verifyCellKzgProofBatch, h]
  rfl

/-- Rejects a `proofsBytes` array whose length does not match
`commitmentsBytes`. -/
theorem verifyCellKzgProofBatch_proofsBytes_mismatch
    {commitmentsBytes : Array Bytes48} {cellIndices : Array CellIndex}
    {cells : Array Cell} {proofsBytes : Array Bytes48}
    (hcells : cells.size = commitmentsBytes.size)
    (h : proofsBytes.size ≠ commitmentsBytes.size) :
    verifyCellKzgProofBatch commitmentsBytes cellIndices cells proofsBytes
      = throw (.inputLengthMismatch "proofsBytes" commitmentsBytes.size
          proofsBytes.size) := by
  simp [verifyCellKzgProofBatch, hcells, h]
  rfl

/-- Rejects a `cellIndices` array whose length does not match
`commitmentsBytes`. -/
theorem verifyCellKzgProofBatch_cellIndices_mismatch
    {commitmentsBytes : Array Bytes48} {cellIndices : Array CellIndex}
    {cells : Array Cell} {proofsBytes : Array Bytes48}
    (hcells : cells.size = commitmentsBytes.size)
    (hproofs : proofsBytes.size = commitmentsBytes.size)
    (h : cellIndices.size ≠ commitmentsBytes.size) :
    verifyCellKzgProofBatch commitmentsBytes cellIndices cells proofsBytes
      = throw (.inputLengthMismatch "cellIndices" commitmentsBytes.size
          cellIndices.size) := by
  simp [verifyCellKzgProofBatch, hcells, hproofs, h]
  rfl

/-- Rejects a wrongly-sized commitment, reporting the first offender. -/
theorem verifyCellKzgProofBatch_badCommitmentSize
    {commitmentsBytes : Array Bytes48} {cellIndices : Array CellIndex}
    {cells : Array Cell} {proofsBytes : Array Bytes48} {cb : Bytes48}
    (hcells : cells.size = commitmentsBytes.size)
    (hproofs : proofsBytes.size = commitmentsBytes.size)
    (hcidx : cellIndices.size = commitmentsBytes.size)
    (h : commitmentsBytes.find? (fun cb => cb.size != BYTES_PER_COMMITMENT)
      = some cb) :
    verifyCellKzgProofBatch commitmentsBytes cellIndices cells proofsBytes
      = throw (.badCommitmentSize cb.size) := by
  simp [verifyCellKzgProofBatch, hcells, hproofs, hcidx, h]
  rfl

end EthCryptographySpecs.Kzg
