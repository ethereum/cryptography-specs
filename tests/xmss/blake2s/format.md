# Test format: XMSS BLAKE2s

Hash a byte string with BLAKE2s-256, the hash every XMSS operation is built on.

## Test case format

The test data is declared in a `data.yaml` file:

```yaml
input: bytes -- the data to hash
output: Bytes32 -- the BLAKE2s-256 digest
```

All byte(s) fields are encoded as strings, hexadecimal encoding, prefixed with
`0x`.

## Condition

The `blake2s` handler should hash the `input`, and the result should match the
expected `output`.
