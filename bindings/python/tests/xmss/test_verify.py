"""Test-vector generator: verification."""

import pytest

from eth_cryptography_specs import xmss

from . import fixtures as F
from dumper import hex_str, write_case


HANDLER = "verify"

# Fixture state: one honest signature at epoch 2, under a key covering [0, 3].
START, END = F.RANGE_LOW
EPOCH = 2
PUBLIC_KEY = xmss.key_gen(F.SEED, START, END)
SIGNATURE = xmss.sign(F.SEED, START, END, EPOCH, F.MESSAGE)


def _input(public_key: bytes, epoch: int, message: bytes, signature: bytes) -> dict:
    return {
        "public_key": hex_str(public_key),
        "epoch":      epoch,
        "message":    hex_str(message),
        "signature":  hex_str(signature),
    }


def _emit(case: str, public_key: bytes, epoch: int, message: bytes, signature: bytes,
          *, expected: bool) -> None:
    result = xmss.verify(public_key, epoch, message, signature)
    assert result == expected

    write_case("xmss", HANDLER, case, {
        "input":  _input(public_key, epoch, message, signature),
        "output": result,
    })


def _emit_invalid(case: str, public_key: bytes, signature: bytes) -> None:
    # Bytes of the wrong length are not a signature or a key at all: an error, not a false.
    with pytest.raises(ValueError):
        xmss.verify(public_key, EPOCH, F.MESSAGE, signature)

    write_case("xmss", HANDLER, case, {
        "input":  _input(public_key, EPOCH, F.MESSAGE, signature),
        "output": None,
    })


def test_valid() -> None:
    _emit(f"{HANDLER}_valid", PUBLIC_KEY, EPOCH, F.MESSAGE, SIGNATURE, expected=True)


# Mutation: flip one bit in each field of the signature in turn.
#
#     [ chain values | randomizer | siblings ]
#       ^ byte 0       ^ byte 672   ^ byte 696
#
# A verifier that skips any one field accepts the matching case.

def test_tampered_chain_value() -> None:
    tampered = F.flip_byte(SIGNATURE, F.CHAIN_VALUES_OFFSET)
    _emit(f"{HANDLER}_tampered_chain_value",
          PUBLIC_KEY, EPOCH, F.MESSAGE, tampered, expected=False)


def test_tampered_randomizer() -> None:
    tampered = F.flip_byte(SIGNATURE, F.RANDOMIZER_OFFSET)
    _emit(f"{HANDLER}_tampered_randomizer",
          PUBLIC_KEY, EPOCH, F.MESSAGE, tampered, expected=False)


def test_tampered_sibling() -> None:
    tampered = F.flip_byte(SIGNATURE, F.SIBLINGS_OFFSET)
    _emit(f"{HANDLER}_tampered_sibling",
          PUBLIC_KEY, EPOCH, F.MESSAGE, tampered, expected=False)


def test_wrong_epoch() -> None:
    # Epoch 3 is also in the key's range, so only the epoch binding can reject it.
    _emit(f"{HANDLER}_wrong_epoch",
          PUBLIC_KEY, EPOCH + 1, F.MESSAGE, SIGNATURE, expected=False)


def test_wrong_message() -> None:
    _emit(f"{HANDLER}_wrong_message",
          PUBLIC_KEY, EPOCH, F.OTHER_MESSAGE, SIGNATURE, expected=False)


# Mutation: drop the last byte, 32 -> 31 for the key and 1208 -> 1207 for the signature.

def test_wrong_length_public_key() -> None:
    _emit_invalid(f"{HANDLER}_wrong_length_public_key", PUBLIC_KEY[:-1], SIGNATURE)


def test_wrong_length_signature() -> None:
    _emit_invalid(f"{HANDLER}_wrong_length_signature", PUBLIC_KEY, SIGNATURE[:-1])
