import EthCryptographySpecs.Bls
import EthCryptographySpecs.Kzg.Constants
import EthCryptographySpecs.Kzg.BitReversal
import EthCryptographySpecs.Kzg.Polynomials
import EthCryptographySpecs.Kzg.Fft
import EthCryptographySpecs.Kzg.Cells
import EthCryptographySpecs.Kzg.TrustedSetup
import EthCryptographySpecs.Kzg.Errors

/-!
# `Recovery`

The Reed-Solomon recovery routine for cell proofs.
-/

namespace EthCryptographySpecs.Kzg

open EthCryptographySpecs.Bls (Fr)

open EthCryptographySpecs.Kzg.Constants
open EthCryptographySpecs.Kzg.BitReversal

/-- Given the cells indices that are missing from the data, compute the
polynomial that vanishes at every point that corresponds to a missing field
element.

This method assumes that all of the cells cannot be missing. In this case the
vanishing polynomial could be computed as `Z(x) = x^n - 1`, where `n` is
`FIELD_ELEMENTS_PER_EXT_BLOB`.

We never encounter this case however because this method is used solely for
recovery and recovery only works if at least half of the cells are available. -/
def constructVanishingPolynomial
    (missingCellIndices : Array CellIndex) : Except KzgError PolynomialCoeff := do
  -- Small domain: roots of unity of order CELLS_PER_EXT_BLOB.
  let rouReduced := computeRootsOfUnity CELLS_PER_EXT_BLOB

  -- Vanishing polynomial over the small domain (roots in BRP order).
  let xs : Array Fr := missingCellIndices.map fun mci =>
    rouReduced[reverseBits mci CELLS_PER_EXT_BLOB]!
  let shortZeroPoly ← vanishingPolynomialcoeff xs

  -- Extend to the full domain using the closed form of the vanishing
  -- polynomial over a coset.
  return (Array.range shortZeroPoly.size).foldl
    (init := Array.replicate FIELD_ELEMENTS_PER_EXT_BLOB Fr.zero)
    fun zeroPoly i =>
      zeroPoly.set! (i * FIELD_ELEMENTS_PER_CELL) shortZeroPoly[i]!

/-- Recover the polynomial in coefficient form that when evaluated at the
roots of unity will give the extended blob. -/
def recoverPolynomialcoeff
    (cellIndices : Array CellIndex) (cosetsEvals : Array CosetEvals)
    : Except KzgError PolynomialCoeff := do
  -- Get the extended domain. This will be referred to as the FFT domain.
  let rouExt := computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB

  -- Flatten the cosets evaluations.
  -- If a cell is missing, then its evaluation is zero.
  -- We let E(x) be a polynomial of degree FIELD_ELEMENTS_PER_EXT_BLOB - 1
  -- that interpolates the evaluations including the zeros for missing ones.
  let extendedRbo : Array Fr := (Array.range cellIndices.size).foldl
    (init := Array.replicate FIELD_ELEMENTS_PER_EXT_BLOB Fr.zero)
    fun acc k =>
      let cell := cosetsEvals[k]!
      let start := cellIndices[k]! * FIELD_ELEMENTS_PER_CELL
      (Array.range FIELD_ELEMENTS_PER_CELL).foldl
        (fun acc j => acc.set! (start + j) cell[j]!) acc

  let extended := bitReversalPermutation extendedRbo

  -- Compute the vanishing polynomial Z(x) in coefficient form.
  -- Z(x) is the polynomial which vanishes on all of the evaluations which are missing.
  -- CELLS_PER_EXT_BLOB = 128; an Array.contains lookup is plenty fast.
  let missing : Array CellIndex :=
    (Array.range CELLS_PER_EXT_BLOB).filter fun ci => !cellIndices.contains ci
  let zeroPolyCoeff ← constructVanishingPolynomial missing

  -- Convert Z(x) to evaluation form over the FFT domain.
  let zeroPolyEval := fftField zeroPolyCoeff rouExt

  -- Compute (E*Z)(x) = E(x) * Z(x) in evaluation form over the FFT domain.
  -- Note: over the FFT domain, the polynomials (E*Z)(x) and (P*Z)(x) agree, where
  -- P(x) is the polynomial we want to reconstruct (degree FIELD_ELEMENTS_PER_BLOB - 1).
  let extTimesZero : Array Fr :=
    Array.ofFn (n := FIELD_ELEMENTS_PER_EXT_BLOB) fun i =>
      zeroPolyEval[i.val]! * extended[i.val]!

  -- We know that (E*Z)(x) and (P*Z)(x) agree over the FFT domain,
  -- and we know that (P*Z)(x) has degree at most FIELD_ELEMENTS_PER_EXT_BLOB - 1.
  -- Thus, an inverse FFT of the evaluations of (E*Z)(x) (= evaluations of (P*Z)(x))
  -- yields the coefficient form of (P*Z)(x).
  let extTimesZeroCoeffs := fftField extTimesZero rouExt (inv := true)

  -- Next step is to divide the polynomial (P*Z)(x) by polynomial Z(x) to get P(x).
  -- We do this in evaluation form over a coset of the FFT domain to avoid division by 0,
  -- i.e. because Z(x) vanishes on (part of) the FFT domain itself. If Z(x) were zero
  -- anywhere on the coset too, the division below would silently produce 0 instead of
  -- failing (see the `Div Fr` docstring), masking a broken vanishing polynomial.

  -- Convert (P*Z)(x) to evaluation form over a coset of the FFT domain.
  let pzOverCoset := cosetFftField extTimesZeroCoeffs rouExt
  -- Convert Z(x) to evaluation form over a coset of the FFT domain.
  let zOverCoset  := cosetFftField zeroPolyCoeff       rouExt
  -- Compute P(x) = (P*Z)(x) / Z(x) in evaluation form over a coset of the FFT domain.
  let pOverCoset : Array Fr :=
    Array.ofFn (n := FIELD_ELEMENTS_PER_EXT_BLOB) fun i =>
      pzOverCoset[i.val]! / zOverCoset[i.val]!
  -- Convert P(x) to coefficient form.
  let pCoeff := cosetFftField pOverCoset rouExt (inv := true)

  return pCoeff.extract 0 FIELD_ELEMENTS_PER_BLOB

/-- Given at least 50% of cells for a blob, recover all the cells/proofs.
This algorithm uses FFTs to recover cells faster than using Lagrange
implementation, as can be seen here:
https://ethresear.ch/t/reed-solomon-erasure-code-recovery-in-n-log-2-n-time-with-ffts/3039

A faster version thanks to Qi Zhou can be found here:
https://github.com/ethereum/research/blob/51b530a53bd4147d123ab3e390a9d08605c2cdb8/polynomial_reconstruction/polynomial_reconstruction_danksharding.py -/
def recoverCellsAndKzgProofs
    (cellIndices : Array CellIndex) (cells : Array Cell)
    : KzgM (Array Cell × Array KZGProof) := do

  -- There must be an equal number of cells and indices.
  if cells.size ≠ cellIndices.size then
    throw (.inputLengthMismatch "cells" cellIndices.size cells.size)

  -- At least 50% of cells must be provided.
  if cellIndices.size < CELLS_PER_EXT_BLOB / 2 then
    throw .notEnoughCells

  -- There must not be more cells than can exist in a single blob.
  if cellIndices.size > CELLS_PER_EXT_BLOB then
    throw .tooManyCells

  -- Cell indices must be within bounds.
  if cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) then
    throw .cellIndexOutOfBounds

  -- Cell indices must be strictly ascending. This enforces two requirements
  -- at once: no duplicates, and ascending order.
  if (Array.range (cellIndices.size - 1)).any
      (fun i => cellIndices[i + 1]! ≤ cellIndices[i]!) then
    throw .indicesNotAscending

  -- Cells must be the correct size.
  if let some c := cells.find? (fun c => c.size != BYTES_PER_CELL) then
    throw (.badCellSize c.size)

  -- Convert cells to coset evaluations.
  let cosetsEvals : Array CosetEvals ← cells.mapM fun c =>
    cellToCosetEvals c

  let polyCoeff ← recoverPolynomialcoeff cellIndices cosetsEvals
  computeCellsAndKzgProofsPolynomialcoeff polyCoeff

end EthCryptographySpecs.Kzg
