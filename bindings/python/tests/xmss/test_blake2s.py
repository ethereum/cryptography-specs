"""Test-vector generator: the BLAKE2s-256 hash."""

import hashlib

from eth_cryptography_specs import xmss

from dumper import hex_str, write_case


HANDLER = "blake2s"


def _emit(case: str, data: bytes) -> None:
    out = xmss.blake2s(data)

    # Every output must match the standard library's BLAKE2s.
    assert out == hashlib.blake2s(data).digest()

    write_case("xmss", HANDLER, case, {
        "input":  hex_str(data),
        "output": hex_str(out),
    })


def test_rfc7693_abc() -> None:
    # The worked example of RFC 7693, Appendix B.
    out = xmss.blake2s(b"abc")
    assert out.hex() == "508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982"

    _emit(f"{HANDLER}_rfc7693_abc", b"abc")


def test_empty() -> None:
    # No data still compresses one all-zero block.
    _emit(f"{HANDLER}_empty", b"")


# BLAKE2s compresses 64-byte blocks, and the last one is flagged as final.
#
#     63 bytes -> 1 block, padded with one zero
#     64 bytes -> 1 block, exactly full
#     65 bytes -> 2 blocks, the second holding a single byte

def test_63_bytes() -> None:
    _emit(f"{HANDLER}_63_bytes", bytes(range(63)))


def test_64_bytes() -> None:
    _emit(f"{HANDLER}_64_bytes", bytes(range(64)))


def test_65_bytes() -> None:
    _emit(f"{HANDLER}_65_bytes", bytes(range(65)))
