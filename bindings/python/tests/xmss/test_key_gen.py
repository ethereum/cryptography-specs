"""Test-vector generator: key generation."""

import pytest

from eth_cryptography_specs import xmss

from . import fixtures as F
from dumper import hex_str, write_case


HANDLER = "key_gen"


def _input(epoch_start: int, epoch_end: int) -> dict:
    return {
        "seed":        hex_str(F.SEED),
        "epoch_start": epoch_start,
        "epoch_end":   epoch_end,
    }


def _emit_valid(case: str, epoch_start: int, epoch_end: int) -> bytes:
    out = xmss.key_gen(F.SEED, epoch_start, epoch_end)

    # The seed alone determines the key, so a second run gives the same bytes.
    assert out == xmss.key_gen(F.SEED, epoch_start, epoch_end)

    write_case("xmss", HANDLER, case, {
        "input":  _input(epoch_start, epoch_end),
        "output": hex_str(out),
    })
    return out


def test_epoch_zero() -> None:
    _emit_valid(f"{HANDLER}_epoch_zero", *F.RANGE_LOW)


def test_middle_epochs() -> None:
    _emit_valid(f"{HANDLER}_middle_epochs", *F.RANGE_MIDDLE)


def test_max_epoch() -> None:
    _emit_valid(f"{HANDLER}_max_epoch", *F.RANGE_HIGH)


def test_single_epoch() -> None:
    # The smallest range: one leaf, every other node a filler.
    _emit_valid(f"{HANDLER}_single_epoch", 7, 7)


def test_extended_range() -> None:
    # Fixture state: the same seed over [0, 3] and over [0, 4].
    start, end = F.RANGE_LOW
    out = _emit_valid(f"{HANDLER}_extended_range", start, end + 1)
    base = xmss.key_gen(F.SEED, start, end)

    # A public key is the root, then the public parameter:
    #
    #     [0, 3]:  [ root A | param P ]
    #     [0, 4]:  [ root B | param P ]
    #
    # The extra leaf changes the root, and the seed alone fixes the parameter.
    assert out[:xmss.DIGEST_LEN] != base[:xmss.DIGEST_LEN]
    assert out[xmss.DIGEST_LEN:] == base[xmss.DIGEST_LEN:]


def test_empty_range() -> None:
    # The start is one past the end, so the range holds no epoch.
    with pytest.raises(RuntimeError):
        xmss.key_gen(F.SEED, 4, 3)

    write_case("xmss", HANDLER, f"{HANDLER}_empty_range", {
        "input":  _input(4, 3),
        "output": None,
    })
