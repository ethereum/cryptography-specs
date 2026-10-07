"""Test-vector generator: the tweakable hash."""

import hashlib

import pytest

from eth_cryptography_specs import xmss

from . import fixtures as F
from dumper import hex_str, write_case


HANDLER = "tweak_hash"

# Every case changes one input of this base call.
BASE_TYPE = 1
BASE_SUB_POSITION = 3
BASE_INDEX = 5
PAYLOAD = b"\x33" * 32

# Tweak types run from 0 to 7, so 8 names none.
UNKNOWN_TYPE = 8


def _input(pp: bytes, tweak_type: int, sub_position: int, index: int) -> dict:
    return {
        "public_param": hex_str(pp),
        "tweak_type":   tweak_type,
        "sub_position": sub_position,
        "index":        index,
        "payload":      hex_str(PAYLOAD),
    }


def _emit_valid(case: str, pp: bytes, tweak_type: int, sub_position: int,
                index: int) -> bytes:
    out = xmss.tweak_hash(pp, tweak_type, sub_position, index, PAYLOAD)

    # Rebuild the hash input by hand, to pin the 16-byte tweak layout:
    #
    #     byte:  0          1      2..3   4..7           8..11   12..15
    #            domain 0   type   zero   sub-position   zero    index
    tweak = (bytes([0, tweak_type, 0, 0]) + sub_position.to_bytes(4, "little")
             + bytes(4) + index.to_bytes(4, "little"))

    # The output is the first 16 bytes of BLAKE2s over tweak, parameter, payload.
    assert out == hashlib.blake2s(tweak + pp + PAYLOAD).digest()[:xmss.DIGEST_LEN]

    write_case("xmss", HANDLER, case, {
        "input":  _input(pp, tweak_type, sub_position, index),
        "output": hex_str(out),
    })
    return out


def _base() -> bytes:
    return xmss.tweak_hash(F.PUBLIC_PARAM, BASE_TYPE, BASE_SUB_POSITION, BASE_INDEX, PAYLOAD)


@pytest.mark.parametrize("tweak_type", range(8))
def test_tweak_type(tweak_type: int) -> None:
    out = _emit_valid(f"{HANDLER}_type_{tweak_type}",
                      F.PUBLIC_PARAM, tweak_type, BASE_SUB_POSITION, BASE_INDEX)

    # Each call site is its own hash function: only the base type reproduces the base output.
    assert (out == _base()) == (tweak_type == BASE_TYPE)


# Adding 2^24 changes only the top byte of a 4-byte field.
# An encoding that keeps just the low byte would miss it.

def test_changed_sub_position() -> None:
    out = _emit_valid(f"{HANDLER}_changed_sub_position",
                      F.PUBLIC_PARAM, BASE_TYPE, BASE_SUB_POSITION + 2**24, BASE_INDEX)

    assert out != _base()


def test_changed_index() -> None:
    out = _emit_valid(f"{HANDLER}_changed_index",
                      F.PUBLIC_PARAM, BASE_TYPE, BASE_SUB_POSITION, BASE_INDEX + 2**24)

    assert out != _base()


def test_changed_public_param() -> None:
    # Each key has its own parameter, so two keys never share a hash function.
    out = _emit_valid(f"{HANDLER}_changed_public_param",
                      F.OTHER_PUBLIC_PARAM, BASE_TYPE, BASE_SUB_POSITION, BASE_INDEX)

    assert out != _base()


def test_unknown_tweak_type() -> None:
    # A byte that names no call site is rejected, not hashed.
    with pytest.raises(RuntimeError):
        xmss.tweak_hash(F.PUBLIC_PARAM, UNKNOWN_TYPE, BASE_SUB_POSITION, BASE_INDEX, PAYLOAD)

    write_case("xmss", HANDLER, f"{HANDLER}_unknown_tweak_type", {
        "input":  _input(F.PUBLIC_PARAM, UNKNOWN_TYPE, BASE_SUB_POSITION, BASE_INDEX),
        "output": None,
    })
