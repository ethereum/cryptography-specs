/-!
# `Xmss.Constants`

The XMSS parameter set.
-/

namespace EthCryptographySpecs.Xmss.Constants

/-! ## Hash and object sizes -/

/-- `n`, the hash value and Merkle node length in bytes.

128 bits, following SLH-DSA at NIST level 1.

Digests this short move the security argument into the random oracle model.

That is the price of a signature under the minimum IPv6 MTU. -/
def DIGEST_LEN : Nat := 16

/-- `l_p`, the public parameter length in bytes.

Hashed into every call, which separates one key's hashes from another's. -/
def PUBLIC_PARAM_LEN : Nat := 16

/-- `l_t`, the tweak length in bytes.

The tweak separates call sites within one key.

A chain step, a Merkle node and a leaf never share a hash input. -/
def TWEAK_LEN : Nat := 16

/-- `l_msg`, the message length in bytes.

XMSS signs a 256-bit digest, so the caller hashes the real message first. -/
def MESSAGE_LEN : Nat := 32

/-- `l_rnd`, the randomizer length in bytes.

The signer grinds this value until the message encodes into the code.

192 bits rather than 128, so a repeat within one signature is negligible. -/
def RANDOMNESS_LEN : Nat := 24

/-- Length of the master secret `S` in bytes.

Every other secret the key holds is derived from it. -/
def SEED_LEN : Nat := 32

/-! ## Winternitz one-time signature -/

/-- `w`, the chunk size in bits.

One encoding digit selects a position along a hash chain. -/
def W : Nat := 3

/-- `v`, the code length: the number of hash chains in one one-time key. -/
def V : Nat := 42

/-- `2^w`, the number of values a hash chain takes.

Position `0` holds the secret key, position `2^w - 1` the public key. -/
def CHAIN_LENGTH : Nat := 2 ^ W

/-- `T`, the sum a valid encoding's digits must hit.

Fixing the sum removes the checksum chains: the signer grinds instead.

`195` sits above the mean of `147`, so the verifier walks fewer steps.

The cost is about 15 bits of grinding per signature. -/
def TARGET_SUM : Nat := 195

/-- Chain steps a verifier walks, summed over all chains.

Constant because the digit sum is fixed.

That is what makes verification a fixed-size circuit. -/
def NUM_CHAIN_HASHES : Nat := 99

/-- `A_max`, the randomizer trials allowed per signature.

A trial succeeds with probability `alpha = 2^-14.85`, so `2^15` are expected.

Exhausting all of them has probability below `2^-(2^17)`. -/
def MAX_RANDOMIZER_TRIALS : Nat := 2 ^ 32

/-! ## Merkle tree -/

/-- `h`, the Merkle tree height. -/
def LOG_LIFETIME : Nat := 32

/-- `L = 2^h`, the number of epochs one key covers.

Each epoch is a one-time key.

Signing two different messages at one epoch breaks the scheme. -/
def LIFETIME : Nat := 2 ^ LOG_LIFETIME

/-! ## Serialized sizes -/

/-- Bytes in a serialized public key: root, then public parameter. -/
def PUB_KEY_SIZE : Nat := DIGEST_LEN + PUBLIC_PARAM_LEN

/-- Bytes in the one-time part of a signature: chain values, then randomizer. -/
def WOTS_SIG_SIZE : Nat := V * DIGEST_LEN + RANDOMNESS_LEN

/-- Bytes in a serialized signature: one-time part, then authentication path. -/
def SIG_SIZE : Nat := WOTS_SIG_SIZE + LOG_LIFETIME * DIGEST_LEN

/-! ## Identities the parameter set must satisfy -/

/-- The encoding consumes `v*w = 126` of the digest's 128 bits.

The signer grinds the two leftover bits to zero.

That is what makes the digest decompose into digits with no slack term. -/
theorem encoding_fills_digest : V * W + 2 = DIGEST_LEN * 8 := by decide

/-- Each 64-bit digest half carries `v/2 = 21` digits in its low 63 bits.

Bit 63 is the padding bit ground to zero. -/
theorem digits_fill_word : W * (V / 2) + 1 = 64 := by decide

/-- The code length is even, so digits split evenly across the two halves. -/
theorem code_length_even : 2 * (V / 2) = V := by decide

/-- The target sum is reachable: it does not exceed the maximum digit sum. -/
theorem target_sum_le_max : TARGET_SUM ≤ V * (CHAIN_LENGTH - 1) := by decide

/-- The verifier's step count is what the target sum leaves unwalked. -/
theorem num_chain_hashes_eq :
    V * (CHAIN_LENGTH - 1) - TARGET_SUM = NUM_CHAIN_HASHES := by decide

/-- The advertised public key size. -/
theorem pub_key_size_eq : PUB_KEY_SIZE = 32 := by decide

/-- The advertised signature size. -/
theorem sig_size_eq : SIG_SIZE = 1208 := by decide

/-! ## C-callable size accessors

The Python C extension reads every size through these at module-init time,
so the wrapper hardcodes no constant of its own.

Each takes a `Unit` to keep the C-ABI signature predictable. -/

@[export eth_xmss_const_digest_len]
def constDigestLen (_ : Unit) : UInt64 :=
  UInt64.ofNat DIGEST_LEN

@[export eth_xmss_const_public_param_len]
def constPublicParamLen (_ : Unit) : UInt64 :=
  UInt64.ofNat PUBLIC_PARAM_LEN

@[export eth_xmss_const_message_len]
def constMessageLen (_ : Unit) : UInt64 :=
  UInt64.ofNat MESSAGE_LEN

@[export eth_xmss_const_randomness_len]
def constRandomnessLen (_ : Unit) : UInt64 :=
  UInt64.ofNat RANDOMNESS_LEN

@[export eth_xmss_const_seed_len]
def constSeedLen (_ : Unit) : UInt64 :=
  UInt64.ofNat SEED_LEN

@[export eth_xmss_const_code_length]
def constCodeLength (_ : Unit) : UInt64 :=
  UInt64.ofNat V

@[export eth_xmss_const_log_lifetime]
def constLogLifetime (_ : Unit) : UInt64 :=
  UInt64.ofNat LOG_LIFETIME

@[export eth_xmss_const_pub_key_size]
def constPubKeySize (_ : Unit) : UInt64 :=
  UInt64.ofNat PUB_KEY_SIZE

@[export eth_xmss_const_sig_size]
def constSigSize (_ : Unit) : UInt64 :=
  UInt64.ofNat SIG_SIZE

end EthCryptographySpecs.Xmss.Constants
