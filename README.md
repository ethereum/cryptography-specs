# cryptography-specs

Specifications for cryptography in Ethereum, written in Lean.

## Specs

- `EthCryptographySpecs/Bls/`, BLS12-381 curve arithmetic, hash-to-curve, and signatures.
- `EthCryptographySpecs/Kzg/`, KZG polynomial commitments.
- `EthCryptographySpecs/Xmss/`, XMSS signatures and SSZ encodings of public keys and signatures.

## Proofs

Formal proofs of properties of the specs exist in
`EthCryptographySpecs/Proofs/`, mirroring the layout above.

## Prerequisites

- [`elan`](https://github.com/leanprover/elan), for `lean` and `lake`.

## Building

```bash
lake exe cache get
lake build
```

Note: `lake exe cache get` is only needed after
the initial clone or after `lake update`; otherwise, `lake build is sufficient`.

XMSS serialization uses the pinned Lean codec from [ethereum/ssz-specs](https://github.com/ethereum/ssz-specs).
The codec builds with this project's Lean 4.29.1 toolchain.
When refreshing dependencies, use `lake --keep-toolchain update` to retain the toolchain matching Mathlib.


## Tests

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -e '.[test]'
pytest
```

*Note*: Pre-generated reference tests are written to `tests/` at the project
root. These tests are intended for use across implementations and may be pinned
by downstream consumers.
