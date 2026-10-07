# Test format: XMSS target-sum encoding

Encode a message into 42 chain digits under one randomizer.

## Test case format

The test data is declared in a `data.yaml` file:

```yaml
input:
  public_param: Bytes16 -- the key's public parameter
  message: Bytes32 -- the message
  randomness: Bytes24 -- the randomizer
  epoch: uint32 -- the epoch
output: List[uint8, 42] -- the digits, each from 0 to 7, or `null`
```

All byte(s) fields are encoded as strings, hexadecimal encoding, prefixed with
`0x`.

## Condition

The `wots_encode` handler should encode the `message` under the `randomness`,
and the result should match the expected `output`. The output is `null` when the
encoding is inadmissible: a spare bit of the digest is set, or the digits do not
sum to 195. This is an ordinary outcome, not an error.
