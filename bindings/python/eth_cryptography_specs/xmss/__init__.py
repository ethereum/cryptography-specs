"""XMSS signatures, with the encoding and hash layers exposed for vector tracing.

- Malformed arguments raise TypeError, ValueError or OverflowError.
- Inputs the spec rejects raise RuntimeError.
"""

from .._native import (
    xmss_blake2s,
    xmss_key_gen,
    xmss_sign,
    xmss_tweak_hash,
    xmss_verify,
    xmss_wots_encode,
    XMSS_CODE_LENGTH as CODE_LENGTH,
    XMSS_DIGEST_LEN as DIGEST_LEN,
    XMSS_LOG_LIFETIME as LOG_LIFETIME,
    XMSS_MESSAGE_LEN as MESSAGE_LEN,
    XMSS_PUB_KEY_SIZE as PUB_KEY_SIZE,
    XMSS_PUBLIC_PARAM_LEN as PUBLIC_PARAM_LEN,
    XMSS_RANDOMNESS_LEN as RANDOMNESS_LEN,
    XMSS_SEED_LEN as SEED_LEN,
    XMSS_SIG_SIZE as SIG_SIZE,
)


def key_gen(seed: bytes, epoch_start: int, epoch_end: int) -> bytes:
    """The public key grown from a seed, for epochs start to end inclusive."""
    return xmss_key_gen(seed, epoch_start, epoch_end)


def sign(seed: bytes, epoch_start: int, epoch_end: int, epoch: int, message: bytes) -> bytes:
    """Sign a message at an epoch with the key grown from a seed and epoch range."""
    return xmss_sign(seed, epoch_start, epoch_end, epoch, message)


def verify(public_key: bytes, epoch: int, message: bytes, signature: bytes) -> bool:
    """Whether a signature signs a message at an epoch under a public key."""
    return xmss_verify(public_key, epoch, message, signature)


def wots_encode(
    public_param: bytes, message: bytes, randomness: bytes, epoch: int
) -> bytes | None:
    """The message's chain digits, one byte each, or None for an inadmissible randomizer."""
    return xmss_wots_encode(public_param, message, randomness, epoch)


def tweak_hash(
    public_param: bytes, tweak_type: int, sub_position: int, index: int, payload: bytes
) -> bytes:
    """The tweakable hash of a payload at one call site.

    - tweak_type: the spec's tweak-type byte, from 0 to 7.
    """
    return xmss_tweak_hash(public_param, tweak_type, sub_position, index, payload)


def blake2s(data: bytes) -> bytes:
    """The BLAKE2s-256 digest of a byte string."""
    return xmss_blake2s(data)


__all__ = [
    "key_gen",
    "sign",
    "verify",
    "wots_encode",
    "tweak_hash",
    "blake2s",
    "CODE_LENGTH",
    "DIGEST_LEN",
    "LOG_LIFETIME",
    "MESSAGE_LEN",
    "PUB_KEY_SIZE",
    "PUBLIC_PARAM_LEN",
    "RANDOMNESS_LEN",
    "SEED_LEN",
    "SIG_SIZE",
]
