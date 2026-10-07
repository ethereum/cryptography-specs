# Test format: XMSS key generation

Grow the public key from a seed, for the epochs from `epoch_start` to
`epoch_end` inclusive.

## Test case format

The test data is declared in a `data.yaml` file:

```yaml
input:
  seed: Bytes32 -- the master secret
  epoch_start: uint32 -- the first epoch the key covers
  epoch_end: uint32 -- the last epoch the key covers
output: XMSS Public Key -- the public key, or `null`
```

- `XMSS Public Key` here is encoded as a string: hexadecimal encoding of 32
  bytes, the Merkle root then the public parameter, prefixed with `0x`.

All byte(s) fields are encoded as strings, hexadecimal encoding, prefixed with
`0x`.

## Condition

The `key_gen` handler should generate the public key from the `input`, and the
result should match the expected `output`. If the range is empty
(`epoch_start > epoch_end`), it should error, i.e. the output should be `null`.
