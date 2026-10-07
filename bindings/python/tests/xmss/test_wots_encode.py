"""Test-vector generator: the message encoding."""

from eth_cryptography_specs import xmss

from . import fixtures as F
from dumper import hex_str, write_case


HANDLER = "wots_encode"

EPOCH = 7


def _emit(case: str, rnd: bytes) -> None:
    out = xmss.wots_encode(F.PUBLIC_PARAM, F.MESSAGE, rnd, EPOCH)

    # Recompute the verdict from the digest, independently of the binding.
    digits, padded = F.decode_digest(F.encoding_digest(F.PUBLIC_PARAM, F.MESSAGE, rnd, EPOCH))
    admissible = padded and sum(digits) == F.TARGET_SUM

    # Admissible gives the 42 digits, anything else gives nothing.
    assert out == (bytes(digits) if admissible else None)

    write_case("xmss", HANDLER, case, {
        "input": {
            "public_param": hex_str(F.PUBLIC_PARAM),
            "message":      hex_str(F.MESSAGE),
            "randomness":   hex_str(rnd),
            "epoch":        EPOCH,
        },
        "output": None if out is None else list(out),
    })


# An encoding is admissible when both checks pass.
# Each rejection below fails exactly one, so it pins that check alone.
#
#     case            spare bits   digit sum
#     admissible      zero         195
#     spare_bit_set   set          195
#     off_target      zero         not 195

def test_admissible() -> None:
    rnd = F.find_randomness(F.PUBLIC_PARAM, F.MESSAGE, EPOCH, padded=True, on_target=True)
    _emit(f"{HANDLER}_admissible", rnd)


def test_spare_bit_set() -> None:
    # Without this check, two digests differing in a spare bit share one codeword.
    rnd = F.find_randomness(F.PUBLIC_PARAM, F.MESSAGE, EPOCH, padded=False, on_target=True)
    _emit(f"{HANDLER}_spare_bit_set", rnd)


def test_off_target() -> None:
    rnd = F.find_randomness(F.PUBLIC_PARAM, F.MESSAGE, EPOCH, padded=True, on_target=False)
    _emit(f"{HANDLER}_off_target", rnd)
