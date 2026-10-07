"""Inputs and encoding helpers shared by the XMSS test-vector generators."""

import itertools

from eth_cryptography_specs import xmss


# Keys and messages

# Distinct readable bytes, so a swapped or reversed field is easy to spot.
SEED = bytes(range(32))

MESSAGE = b"\x11" * 32
OTHER_MESSAGE = b"\x22" * 32

PUBLIC_PARAM = b"\x5a" * 16
OTHER_PUBLIC_PARAM = b"\xa5" * 16


# Epoch ranges

MAX_EPOCH = 2**32 - 1

# Each range holds a handful of epochs, so key generation stays fast.
#
#     low    : [0, 3]                  touches the first epoch
#     middle : [2^31 - 2, 2^31 + 2]    straddles the root's two subtrees
#     high   : [2^32 - 4, 2^32 - 1]    touches the last epoch
RANGE_LOW = (0, 3)
RANGE_MIDDLE = (2**31 - 2, 2**31 + 2)
RANGE_HIGH = (MAX_EPOCH - 3, MAX_EPOCH)


# Signature layout

# A signature is three fields back to back:
#
#     [ 42 chain values: 672 | randomizer: 24 | 32 siblings: 512 ]
#       ^ 0                    ^ 672            ^ 696
CHAIN_VALUES_OFFSET = 0
RANDOMIZER_OFFSET = xmss.CODE_LENGTH * xmss.DIGEST_LEN
SIBLINGS_OFFSET = RANDOMIZER_OFFSET + xmss.RANDOMNESS_LEN

# The three fields fill the signature exactly.
assert SIBLINGS_OFFSET + xmss.LOG_LIFETIME * xmss.DIGEST_LEN == xmss.SIG_SIZE


def flip_byte(data: bytes, offset: int) -> bytes:
    # Flip the lowest bit: the smallest change a verifier must still catch.
    return data[:offset] + bytes([data[offset] ^ 0x01]) + data[offset + 1:]


# Message encoding
#
# Recomputed here from the digest, so a case can be built for each way the encoding fails.

ENCODING_TWEAK_TYPE = 4
TARGET_SUM = 195
DIGIT_BITS = 3


def encoding_digest(pp: bytes, msg: bytes, rnd: bytes, epoch: int) -> bytes:
    # The encoding hashes 64 bytes: message, randomizer, and 8 zero bytes of padding.
    return xmss.tweak_hash(pp, ENCODING_TWEAK_TYPE, 0, epoch, msg + rnd + bytes(8))


def decode_digest(digest: bytes) -> tuple[list[int], bool]:
    # The 16-byte digest splits into two little-endian 64-bit halves.
    halves = [int.from_bytes(digest[:8], "little"), int.from_bytes(digest[8:], "little")]

    # Each half carries 21 three-bit digits in bits 0 to 62:
    #
    #     bit:   63      62 .. 60   ...   5 .. 3    2 .. 0
    #           spare    digit 20   ...   digit 1   digit 0
    digits = [
        (half >> (DIGIT_BITS * r)) % 2**DIGIT_BITS
        for half in halves
        for r in range(xmss.CODE_LENGTH // 2)
    ]

    # Bit 63 of each half is spare and must be zero.
    padded = all(half >> 63 == 0 for half in halves)

    return digits, padded


def find_randomness(pp: bytes, msg: bytes, epoch: int,
                    *, padded: bool, on_target: bool) -> bytes:
    # Accept a randomizer when both checks come out as requested.
    #
    #     padded, on_target  -> admissible
    #     not padded         -> rejected by the spare bit
    #     not on_target      -> rejected by the digit sum
    def matches(rnd: bytes) -> bool:
        digits, is_padded = decode_digest(encoding_digest(pp, msg, rnd, epoch))
        return is_padded == padded and (sum(digits) == TARGET_SUM) == on_target

    # Counting up from zero makes the search, and so the vectors, reproducible.
    counters = (c.to_bytes(xmss.RANDOMNESS_LEN, "little") for c in itertools.count())
    return next(filter(matches, counters))
