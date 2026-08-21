/-!
# `Bls.Errors`

Typed errors for the BLS surface.

The BLS spec functions do no I/O, so the fallible ones return
`Except BlsError` and report structured failures rather than
stringly-typed `IO.userError`s. The C-ABI layer in `Exports` runs such a
computation down to `IO` with `runBls`, translating any `BlsError` into
the `IO.userError` the Python bindings expect.
-/

namespace EthCryptographySpecs.Bls

/-- Every way a BLS operation can reject its input. -/
inductive BlsError where
  /-- The pubkey list was empty. -/
  | emptyPubkeyList
  /-- A pubkey was not `BYTES_PER_PUBKEY` bytes long. -/
  | badPubkeySize (actual : Nat)
  /-- Pubkey bytes failed `KeyValidate` (bad encoding, off-curve, wrong
  subgroup, or the point at infinity). When it came from an array,
  `index` is its position. -/
  | invalidPubkey (index : Option Nat)
  /-- G1 point bytes could not be decompressed. -/
  | invalidG1Point
  /-- G2 point bytes could not be decompressed. -/
  | invalidG2Point
  /-- `KeyValidate` rejected the point at infinity. -/
  | pointAtInfinity
  /-- A point was not in the prime-order subgroup. -/
  | notInSubgroup
  /-- Bytes did not represent a canonical field element (value ≥ modulus). -/
  | nonCanonicalFieldElement
  /-- A field element had no square root (not a quadratic residue). -/
  | notASquare
  /-- `expand_message_xmd` was asked for more than 65535 bytes. -/
  | expandMessageOutputTooLong (len : Nat)
  /-- `expand_message_xmd` would need more than 255 hash blocks. -/
  | expandMessageTooManyBlocks (ell : Nat)

/-- Human-readable description, used at the C-ABI boundary. -/
def BlsError.message : BlsError → String
  | .emptyPubkeyList            => "empty pubkey list"
  | .badPubkeySize actual       => s!"bad pubkey size: {actual}"
  | .invalidPubkey (some index) => s!"invalid pubkey at index {index}"
  | .invalidPubkey none         => "invalid pubkey"
  | .invalidG1Point             => "invalid G1 point"
  | .invalidG2Point             => "invalid G2 point"
  | .pointAtInfinity            => "point at infinity"
  | .notInSubgroup              => "point not in subgroup"
  | .nonCanonicalFieldElement   => "non-canonical field element"
  | .notASquare                 => "not a square"
  | .expandMessageOutputTooLong len =>
      s!"expand_message_xmd output too long: {len}"
  | .expandMessageTooManyBlocks ell =>
      s!"expand_message_xmd too many blocks: {ell}"

/-- Run a fallible BLS computation down to `IO`, turning a `BlsError`
into the `IO.userError` the C-ABI layer surfaces to callers. -/
def runBls {α : Type} (act : Except BlsError α) : IO α :=
  match act with
  | .ok a    => pure a
  | .error e => throw (IO.userError e.message)

end EthCryptographySpecs.Bls

namespace EthCryptographySpecs

/-- `panic!` with an explicit fallback value: logically equal to `fallback`
(so theorems about the surrounding definition are unaffected), but at
runtime prints an error message — and aborts when the process runs with
`LEAN_ABORT_ON_PANIC=1` — when reached. Used to transcribe spec-level
runtime assertions into proof-covered pure code. -/
@[inline] def panicWith {α : Type _} (fallback : α) (msg : String) : α :=
  @panic α ⟨fallback⟩ msg

@[simp] theorem panicWith_eq {α : Type _} (fallback : α) (msg : String) :
    panicWith fallback msg = fallback := rfl

end EthCryptographySpecs
