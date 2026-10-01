import EthCryptographySpecs.Xmss.KeyGen

/-!
# `Xmss.Sign`

Signing.

Signing is deterministic: same key, message and epoch, same signature.

A key must never sign two different messages at one epoch.

Signing is stateless, so tracking spent epochs is the caller's job.
-/

namespace EthCryptographySpecs.Xmss

open EthCryptographySpecs.Xmss.Constants

/-! ## Grinding the randomizer -/

/-- The randomizer of one attempt.

The seed is in the hash input, so the randomizer stays secret until signed. -/
def randomizer (pp : PublicParam) (seed : Seed) (msg : Message) (epoch : Epoch)
    (trial : Nat) : Randomness :=
  -- Same layout as every other hash: tweak, then parameter, then payload.
  let input := packBytes (makeTweak .randomizer (UInt32.ofNat trial) epoch)
    ++ packBytes pp ++ packBytes seed ++ packBytes msg
  -- The randomizer keeps more of the digest than a node does.
  (Blake2s.hash input).take RANDOMNESS_LEN

namespace Internal

/-- Try the attempts from `trial` onward, at most `fuel` of them.

Returns the first admissible randomizer with its digits. -/
def findRandomness (pp : PublicParam) (seed : Seed) (msg : Message)
    (epoch : Epoch) (trial fuel : Nat) :
    Option (Randomness × Vector (Fin CHAIN_LENGTH) V) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    let rnd := randomizer pp seed msg epoch trial
    match wotsEncode pp msg rnd epoch with
    -- The first admissible attempt wins.
    | some x => some (rnd, x)
    -- Otherwise move on to the next attempt.
    | none => findRandomness pp seed msg epoch (trial + 1) fuel

end Internal

/-! ## Signing -/

/-- Sign a message at an epoch of the key's range.

Rejects an epoch outside the range, and a message no attempt encodes.

The second has probability below `2^-256` per signature. -/
def sign (sk : SecretKey) (msg : Message) (epoch : Epoch) :
    Except XmssError Signature :=
  let pp := sk.publicParam
  if epoch < sk.epochStart || sk.epochEnd < epoch then
    .error (.epochOutOfRange epoch sk.epochStart sk.epochEnd)
  else
    -- Step 1: grind the randomizer until the message encodes.
    let found :=
      Internal.findRandomness pp sk.seed msg epoch 0 MAX_RANDOMIZER_TRIALS
    match found with
    | none => .error (.noAdmissibleEncoding epoch)
    | some (rnd, x) => .ok {
        -- Step 2: reveal each chain at the height its digit names.
        chainElements := otsReveal pp epoch (otsSecretKey pp sk.seed epoch) x
        randomness := rnd
        -- Step 3: the co-path of the epoch's leaf.
        merklePath := sk.authPath sk.leaves epoch }

end EthCryptographySpecs.Xmss
