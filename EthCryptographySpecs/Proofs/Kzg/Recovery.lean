import EthCryptographySpecs.Kzg.Recovery
import EthCryptographySpecs.Proofs.Kzg.Fft

/-!
# Proofs: `Recovery`

Shape properties of the recovery pipeline (the recovered polynomial has
exactly `FIELD_ELEMENTS_PER_BLOB` coefficients) and the validation
surface of `recoverCellsAndKzgProofs`: each malformed input is rejected
with exactly the documented error.
-/

namespace EthCryptographySpecs.Kzg

open EthCryptographySpecs.Bls (Fr)
open EthCryptographySpecs.Kzg.Constants

/-- A `foldl` whose step preserves array size preserves array size. -/
private theorem size_foldl_of_size_step {α β : Type _} (xs : Array β)
    (init : Array α) (f : Array α → β → Array α)
    (hf : ∀ acc b, (f acc b).size = acc.size) :
    (xs.foldl f init).size = init.size :=
  Array.foldl_induction (motive := fun _ acc => acc.size = init.size) rfl
    (fun i acc h => (hf acc xs[i]).trans h)

/-- The extended vanishing polynomial spans the full extended domain. -/
theorem size_constructVanishingPolynomial
    {missingCellIndices : Array CellIndex} {p : PolynomialCoeff}
    (h : constructVanishingPolynomial missingCellIndices = .ok p) :
    p.size = FIELD_ELEMENTS_PER_EXT_BLOB := by
  simp only [constructVanishingPolynomial, bind, Except.bind] at h
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [size_foldl_of_size_step]
    · simp
    · exact fun acc b => Array.size_setIfInBounds

/-- On success, the recovered polynomial has exactly
`FIELD_ELEMENTS_PER_BLOB` coefficients, whatever the inputs. -/
theorem size_recoverPolynomialcoeff
    {cellIndices : Array CellIndex} {cosetsEvals : Array CosetEvals}
    {p : PolynomialCoeff}
    (h : recoverPolynomialcoeff cellIndices cosetsEvals = .ok p) :
    p.size = FIELD_ELEMENTS_PER_BLOB := by
  simp only [recoverPolynomialcoeff, bind, Except.bind] at h
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [FIELD_ELEMENTS_PER_EXT_BLOB]
    omega

/-- `recoverCellsAndKzgProofs` rejects a cells array whose length does
not match the indices array. -/
theorem recoverCellsAndKzgProofs_length_mismatch
    {cellIndices : Array CellIndex} {cells : Array Cell}
    (h : cells.size ≠ cellIndices.size) :
    recoverCellsAndKzgProofs cellIndices cells
      = throw (.inputLengthMismatch "cells" cellIndices.size cells.size) := by
  simp [recoverCellsAndKzgProofs, h]
  rfl

/-- `recoverCellsAndKzgProofs` rejects fewer than 50% of the cells. -/
theorem recoverCellsAndKzgProofs_notEnoughCells
    {cellIndices : Array CellIndex} {cells : Array Cell}
    (hlen : cells.size = cellIndices.size)
    (h : cellIndices.size < CELLS_PER_EXT_BLOB / 2) :
    recoverCellsAndKzgProofs cellIndices cells = throw .notEnoughCells := by
  simp [recoverCellsAndKzgProofs, hlen, h]
  rfl

/-- `recoverCellsAndKzgProofs` rejects more cells than exist. -/
theorem recoverCellsAndKzgProofs_tooManyCells
    {cellIndices : Array CellIndex} {cells : Array Cell}
    (hlen : cells.size = cellIndices.size)
    (hmin : ¬cellIndices.size < CELLS_PER_EXT_BLOB / 2)
    (h : cellIndices.size > CELLS_PER_EXT_BLOB) :
    recoverCellsAndKzgProofs cellIndices cells = throw .tooManyCells := by
  simp [recoverCellsAndKzgProofs, hlen, hmin, h]
  rfl

/-- `recoverCellsAndKzgProofs` rejects an out-of-bounds cell index. -/
theorem recoverCellsAndKzgProofs_cellIndexOutOfBounds
    {cellIndices : Array CellIndex} {cells : Array Cell}
    (hlen : cells.size = cellIndices.size)
    (hmin : ¬cellIndices.size < CELLS_PER_EXT_BLOB / 2)
    (hmax : ¬cellIndices.size > CELLS_PER_EXT_BLOB)
    (h : cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) = true) :
    recoverCellsAndKzgProofs cellIndices cells
      = throw .cellIndexOutOfBounds := by
  simp [recoverCellsAndKzgProofs, hlen, hmin, hmax, h]
  rfl

/-- `recoverCellsAndKzgProofs` rejects cell indices that are not
strictly ascending. -/
theorem recoverCellsAndKzgProofs_indicesNotAscending
    {cellIndices : Array CellIndex} {cells : Array Cell}
    (hlen : cells.size = cellIndices.size)
    (hmin : ¬cellIndices.size < CELLS_PER_EXT_BLOB / 2)
    (hmax : ¬cellIndices.size > CELLS_PER_EXT_BLOB)
    (hbound : cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) = false)
    (h : (Array.range (cellIndices.size - 1)).any
      (fun i => cellIndices[i + 1]! ≤ cellIndices[i]!) = true) :
    recoverCellsAndKzgProofs cellIndices cells
      = throw .indicesNotAscending := by
  simp only [Array.size_range] at h
  simp [recoverCellsAndKzgProofs, hlen, hmin, hmax, hbound, h]
  rfl

/-- `recoverCellsAndKzgProofs` rejects a wrongly-sized cell, reporting
the first offender's size. -/
theorem recoverCellsAndKzgProofs_badCellSize
    {cellIndices : Array CellIndex} {cells : Array Cell} {c : Cell}
    (hlen : cells.size = cellIndices.size)
    (hmin : ¬cellIndices.size < CELLS_PER_EXT_BLOB / 2)
    (hmax : ¬cellIndices.size > CELLS_PER_EXT_BLOB)
    (hbound : cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) = false)
    (hasc : (Array.range (cellIndices.size - 1)).any
      (fun i => cellIndices[i + 1]! ≤ cellIndices[i]!) = false)
    (h : cells.find? (fun c => c.size != BYTES_PER_CELL) = some c) :
    recoverCellsAndKzgProofs cellIndices cells
      = throw (.badCellSize c.size) := by
  simp only [Array.size_range] at hasc
  simp [recoverCellsAndKzgProofs, hlen, hmin, hmax, hbound, hasc, h]
  rfl

end EthCryptographySpecs.Kzg
