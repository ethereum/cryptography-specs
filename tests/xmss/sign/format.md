# Test format: XMSS sign

Sign a message at an epoch with the key grown from a seed and epoch range.

## Test case format

The test data is declared in a `data.yaml` file:

```yaml
input:
  seed: Bytes32 -- the master secret
  epoch_start: uint32 -- the first epoch the key covers
  epoch_end: uint32 -- the last epoch the key covers
  epoch: uint32 -- the epoch to sign at
  message: Bytes32 -- the message
output: XMSS Signature -- the signature, or `null`
```

- `XMSS Signature` here is encoded as a string: hexadecimal encoding of 1208
  bytes, prefixed with `0x`. It is the 42 chain values (672 bytes), then the
  randomizer (24 bytes), then the 32 Merkle siblings from the leaf up (512
  bytes).

All byte(s) fields are encoded as strings, hexadecimal encoding, prefixed with
`0x`.

## Condition

The `sign` handler should sign the `message` at `epoch`, and the result should
match the expected `output`. Signing is deterministic. If `epoch` is outside the
key's range, it should error, i.e. the output should be `null`.
