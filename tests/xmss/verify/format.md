# Test format: XMSS verify

Verify a signature against a public key, an epoch and a message.

## Test case format

The test data is declared in a `data.yaml` file:

```yaml
input:
  public_key: XMSS Public Key -- the public key
  epoch: uint32 -- the epoch
  message: Bytes32 -- the message
  signature: XMSS Signature -- the signature to verify
output: bool -- true (VALID), false (INVALID), or `null`
```

- `XMSS Public Key` here is encoded as a string: hexadecimal encoding of 32
  bytes, prefixed with `0x`.
- `XMSS Signature` here is encoded as a string: hexadecimal encoding of 1208
  bytes, prefixed with `0x`.

All byte(s) fields are encoded as strings, hexadecimal encoding, prefixed with
`0x`.

## Condition

The `verify` handler should verify the `signature` with the public key, epoch
and message in the `input`, and the result should match the expected `output`.
If the public key or the signature has the wrong length, it should error, i.e.
the output should be `null`.
