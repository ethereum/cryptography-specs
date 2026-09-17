import EthCryptographySpecs.Xmss.Types

/-!
# Proofs: `Xmss.Types`

Properties of the fixed-size byte objects.
-/

namespace EthCryptographySpecs.Xmss

/-- A fixed-size object serializes to exactly its own length. -/
@[simp] theorem size_packBytes {n : Nat} (v : Vector UInt8 n) :
    (packBytes v).size = n := v.size_toArray

/-- Reading succeeds exactly when the buffer has room for the object.

Nothing weaker is accepted, so a caller cannot slip a short buffer through. -/
@[simp] theorem isSome_unpackBytes? {n : Nat} (b : ByteArray) (offset : Nat) :
    (unpackBytes? n b offset).isSome ↔ offset + n ≤ b.size := by
  -- Acceptance is the guard itself, so both branches close by case analysis.
  rw [unpackBytes?]
  split <;> simp_all

/-- Writing an object and reading it back returns the same object. -/
@[simp] theorem unpackBytes?_packBytes {n : Nat} (v : Vector UInt8 n) :
    unpackBytes? n (packBytes v) = some v := by
  -- A buffer holding exactly one object has room for it, so the guard passes.
  rw [unpackBytes?, dif_pos (by simp : 0 + n ≤ (packBytes v).size)]
  -- Reading back index `i` gives entry `i`, which rebuilds the object.
  simp [packBytes]

/-- Reading a full-length buffer and writing it back returns it unchanged.

So no buffer is unreachable, and no object has two encodings. -/
theorem packBytes_unpackBytes? {n : Nat} {b : ByteArray} (hb : b.size = n) :
    (unpackBytes? n b).map packBytes = some b := by
  -- A buffer of exactly the right length has room, so the guard passes.
  rw [unpackBytes?, dif_pos (by omega : 0 + n ≤ b.size)]
  simp only [Option.map_some, packBytes, Vector.toArray_ofFn, Nat.zero_add]
  -- The object's length is the buffer's, so the read indices cover it exactly.
  have hdata : b.data.size = n := hb
  subst hdata
  -- Tabulating every entry of an array rebuilds that array.
  refine congrArg some ?_
  exact congrArg ByteArray.mk Array.ofFn_getElem

end EthCryptographySpecs.Xmss
