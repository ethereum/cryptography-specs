# Test format: XMSS tweakable hash

Hash a payload under one call site of one key: the first 16 bytes of the
BLAKE2s-256 digest of tweak, public parameter and payload.

## Test case format

The test data is declared in a `data.yaml` file:

```yaml
input:
  public_param: Bytes16 -- the key's public parameter
  tweak_type: uint8 -- the call site, from 0 to 7
  sub_position: uint32 -- the tweak's sub-position
  index: uint32 -- the tweak's index
  payload: bytes -- the data to hash
output: Bytes16 -- the digest, or `null`
```

All byte(s) fields are encoded as strings, hexadecimal encoding, prefixed with
`0x`.

## Condition

The `tweak_hash` handler should hash the `payload` under the tweak and public
parameter in the `input`, and the result should match the expected `output`. If
`tweak_type` names no call site, it should error, i.e. the output should be
`null`.
