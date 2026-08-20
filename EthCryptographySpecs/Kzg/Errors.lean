/-!
# `Kzg.Errors`

Typed errors for the KZG surface.

The implementation functions are written in `KzgM` (`ExceptT KzgError IO`):
they can still perform the I/O they need (reading the loaded trusted
setup) while reporting domain failures as structured `KzgError` values
rather than stringly-typed `IO.userError`s. Pure helpers that cannot do
I/O return `Except KzgError` and lift transparently into `KzgM`.

The C-ABI layer in `Exports` runs a `KzgM` action back down to `IO` with
`runKzg`, translating any `KzgError` into the `IO.userError` that the
Python bindings expect.
-/

namespace EthCryptographySpecs.Kzg

/-- Every way a KZG operation can reject its input. -/
inductive KzgError where
  /-- A blob was not `BYTES_PER_BLOB` bytes long. -/
  | badBlobSize (actual : Nat)
  /-- A commitment was not `BYTES_PER_COMMITMENT` bytes long. -/
  | badCommitmentSize (actual : Nat)
  /-- A proof was not `BYTES_PER_PROOF` bytes long. -/
  | badProofSize (actual : Nat)
  /-- A cell was not `BYTES_PER_CELL` bytes long. -/
  | badCellSize (actual : Nat)
  /-- A field element (`z` or `y`) was not `BYTES_PER_FIELD_ELEMENT` bytes long. -/
  | badFieldElementSize (actual : Nat)
  /-- Commitment bytes failed group validation. -/
  | invalidCommitment (index : Option Nat)
  /-- Proof bytes failed group validation. -/
  | invalidProof (index : Option Nat)
  /-- A field element was not canonical. -/
  | invalidFieldElement (index : Option Nat)
  /-- An input array (`input`, named after the parameter) did not have
  the same length as the input array it must match. -/
  | inputLengthMismatch (input : String) (expected actual : Nat)
  /-- A G1 linear combination got different point and scalar counts. -/
  | lincombLengthMismatch (points scalars : Nat)
  /-- A commitment index referenced a commitment that does not exist. -/
  | commitmentIndexOutOfBounds
  /-- A cell index was `≥ CELLS_PER_EXT_BLOB`. -/
  | cellIndexOutOfBounds
  /-- Cell indices were not strictly ascending. -/
  | indicesNotAscending
  /-- Fewer than 50% of a blob's cells were provided. -/
  | notEnoughCells
  /-- More cells than exist in an extended blob were provided. -/
  | tooManyCells
  /-- Polynomial division by an empty polynomial or one whose leading
  coefficient is zero (`Fr` division alone would silently produce a
  wrong polynomial). -/
  | zeroDivisorPolynomial
  /-- A coefficient-form product would exceed `FIELD_ELEMENTS_PER_EXT_BLOB`
  coefficients. -/
  | polynomialProductTooLong (lenA lenB : Nat)
  /-- An evaluation-form polynomial did not have `FIELD_ELEMENTS_PER_BLOB`
  elements. -/
  | badPolynomialSize (actual : Nat)
  /-- The deduplicated commitments list passed to
  `verifyCellKzgProofBatchImpl` contained duplicates. -/
  | duplicateCommitments
  /-- 48-byte input failed to decompress to a G1 point. -/
  | invalidG1Point
  /-- Every cell of the extended blob was reported missing; the vanishing
  polynomial for that case is not representable here (and recovery
  requires at least half the cells anyway). -/
  | tooManyMissingCells

/-- Human-readable description, used at the C-ABI boundary. -/
def KzgError.message : KzgError → String
  | .badBlobSize actual         => s!"bad blob size: {actual}"
  | .badCommitmentSize actual   => s!"bad commitment size: {actual}"
  | .badProofSize actual        => s!"bad proof size: {actual}"
  | .badCellSize actual         => s!"bad cell size: {actual}"
  | .badFieldElementSize actual => s!"bad field element size: {actual}"
  | .invalidCommitment (some index) => s!"invalid commitment at index {index}"
  | .invalidCommitment none         => "invalid commitment"
  | .invalidProof (some index)      => s!"invalid proof at index {index}"
  | .invalidProof none              => "invalid proof"
  | .invalidFieldElement (some index) => s!"invalid field element at index {index}"
  | .invalidFieldElement none         => "invalid field element"
  | .inputLengthMismatch input expected actual =>
      s!"input length mismatch: {input} has length {actual}, expected {expected}"
  | .lincombLengthMismatch points scalars =>
      s!"linear combination length mismatch: {points} points, {scalars} scalars"
  | .commitmentIndexOutOfBounds => "out-of-bounds commitment index"
  | .cellIndexOutOfBounds       => "cell index out of bounds"
  | .indicesNotAscending        => "indices not strictly ascending"
  | .notEnoughCells             => "not enough cells provided"
  | .tooManyCells               => "too many cells provided"
  | .zeroDivisorPolynomial      => "division by zero polynomial"
  | .polynomialProductTooLong lenA lenB =>
      s!"polynomial product too long: {lenA} + {lenB} coefficients"
  | .badPolynomialSize actual   => s!"bad polynomial size: {actual}"
  | .duplicateCommitments       => "duplicate commitments"
  | .invalidG1Point             => "invalid G1 point"
  | .tooManyMissingCells        => "too many missing cells"

/-- The KZG implementation monad: `IO` (for the trusted setup) with
typed `KzgError` domain failures. -/
abbrev KzgM := ExceptT KzgError IO

/-- Run a `KzgM` action down to `IO`, turning a `KzgError` into the
`IO.userError` the C-ABI layer surfaces to callers. -/
def runKzg {α : Type} (act : KzgM α) : IO α := do
  match ← act.run with
  | .ok a    => pure a
  | .error e => throw (IO.userError e.message)

end EthCryptographySpecs.Kzg
