import EthCryptographySpecs.Xmss.Types

/-!
# `Xmss.Errors`

Typed failures for the XMSS surface.

Fallible operations should return a result rather than throwing.

Verification is not here.

Bytes that do not parse are a caller error and fail here.

A well-formed signature that does not verify is an ordinary `false`.
-/

namespace EthCryptographySpecs.Xmss

open EthCryptographySpecs.Xmss.Constants

/-- Every way an XMSS operation can reject its input. -/
inductive XmssError where
  /-- Key generation was given an empty epoch range. -/
  | invalidEpochRange (epochStart epochEnd : Epoch)
  /-- Signing was given an epoch the key does not cover. -/
  | epochOutOfRange (epoch epochStart epochEnd : Epoch)
  /-- Signing exhausted every randomizer without landing in the code.

  Under a random oracle this reports a broken hash, not bad luck. -/
  | noAdmissibleEncoding (epoch : Epoch)
  /-- Public key bytes were not the public key length. -/
  | badPublicKeySize (actual : Nat)
  /-- Signature bytes were not the signature length. -/
  | badSignatureSize (actual : Nat)
  /-- Message bytes were not the message length.

  XMSS signs a 256-bit digest, so the caller hashes first. -/
  | badMessageSize (actual : Nat)
  /-- Seed bytes were not the seed length. -/
  | badSeedSize (actual : Nat)

/-- Human-readable description, used at the C-ABI boundary. -/
def XmssError.message : XmssError → String
  -- One line per rejection, phrased for someone reading a Python traceback.
  | .invalidEpochRange epochStart epochEnd =>
      s!"invalid epoch range: {epochStart} is past {epochEnd}"
  | .epochOutOfRange epoch epochStart epochEnd =>
      s!"epoch {epoch} is outside the key's range [{epochStart}, {epochEnd}]"
  | .noAdmissibleEncoding epoch =>
      s!"no admissible encoding at epoch {epoch} within the trial limit"
  -- The expected length is fixed by the parameter set.
  -- So it is read from there rather than carried in the error.
  | .badPublicKeySize actual =>
      s!"bad public key size: {actual}, expected {PUB_KEY_SIZE}"
  | .badSignatureSize actual =>
      s!"bad signature size: {actual}, expected {SIG_SIZE}"
  | .badMessageSize actual =>
      s!"bad message size: {actual}, expected {MESSAGE_LEN}"
  | .badSeedSize actual =>
      s!"bad seed size: {actual}, expected {SEED_LEN}"

/-- Run a fallible XMSS computation down to `IO`.

The C-ABI layer surfaces failures to Python as exceptions. -/
def runXmss {α : Type} (act : Except XmssError α) : IO α :=
  match act with
  -- Success passes straight through.
  | .ok a    => pure a
  -- Failure becomes the user error the Python bindings expect.
  | .error e => throw (IO.userError e.message)

end EthCryptographySpecs.Xmss
