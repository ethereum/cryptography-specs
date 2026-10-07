"""Test-vector generator: signing."""

import pytest

from eth_cryptography_specs import xmss

from . import fixtures as F
from dumper import hex_str, write_case


HANDLER = "sign"

# The key covers [2^31 - 2, 2^31 + 2].
START, END = F.RANGE_MIDDLE


def _input(epoch: int) -> dict:
    return {
        "seed":        hex_str(F.SEED),
        "epoch_start": START,
        "epoch_end":   END,
        "epoch":       epoch,
        "message":     hex_str(F.MESSAGE),
    }


def _emit_valid(case: str, epoch: int) -> None:
    out = xmss.sign(F.SEED, START, END, epoch, F.MESSAGE)

    # Signing is deterministic: same key, message and epoch give the same signature.
    assert out == xmss.sign(F.SEED, START, END, epoch, F.MESSAGE)

    # Every emitted signature verifies under the key it was made with.
    assert xmss.verify(xmss.key_gen(F.SEED, START, END), epoch, F.MESSAGE, out)

    write_case("xmss", HANDLER, case, {
        "input":  _input(epoch),
        "output": hex_str(out),
    })


def _emit_invalid(case: str, epoch: int) -> None:
    # The key has no one-time key at this epoch, so signing is refused.
    with pytest.raises(RuntimeError):
        xmss.sign(F.SEED, START, END, epoch, F.MESSAGE)

    write_case("xmss", HANDLER, case, {
        "input":  _input(epoch),
        "output": None,
    })


# Both ends and the middle of the range:
#
#     epoch:  START-1 | START   ...   middle   ...   END | END+1
#             refused | signed        signed         signed | refused

def test_range_start() -> None:
    _emit_valid(f"{HANDLER}_range_start", START)


def test_range_middle() -> None:
    _emit_valid(f"{HANDLER}_range_middle", (START + END) // 2)


def test_range_end() -> None:
    _emit_valid(f"{HANDLER}_range_end", END)


def test_epoch_before_range() -> None:
    _emit_invalid(f"{HANDLER}_epoch_before_range", START - 1)


def test_epoch_after_range() -> None:
    _emit_invalid(f"{HANDLER}_epoch_after_range", END + 1)
