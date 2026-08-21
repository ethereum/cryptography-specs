/-!
# `BitReversal`

`bitReversalPermutation` and friends. Operate on any `Array α`.
-/

namespace EthCryptographySpecs.Kzg.BitReversal

/-- Reverse the lower `bits` bits of `x`, shifting the reversed bits into
the accumulator `r` (pass `0` initially). -/
def reverseBitsAux (x r : Nat) : Nat → Nat
  | 0 => r
  | bits + 1 => reverseBitsAux (x >>> 1) ((r <<< 1) ||| (x &&& 1)) bits

/-- Reverse the bit order of `n` over `log2 order` bits. Requires
`order` to be a positive power of two. -/
def reverseBits (n order : Nat) : Nat :=
  reverseBitsAux n 0 order.log2

/-- Bit-reversed permutation of `seq`: `out[i] = seq[reverseBits i (size seq)]`.
The permutation is an involution. -/
def bitReversalPermutation {α : Type _} [Inhabited α]
    (seq : Array α) : Array α :=
  Array.ofFn (n := seq.size) fun i =>
    seq[reverseBits i.val seq.size]!

end EthCryptographySpecs.Kzg.BitReversal
