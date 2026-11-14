module

public import EthLib.Serialization.JsonRpc
public import EthLib.Base.Hex
public import EthLib.Base.Except
public import EthLib.Base.Proofs.MapM
public import EthLib.Base.Proofs.Bytes
public import Std.Data.TreeMap.Raw.WF
public import Std.Data.TreeMap.Raw.Lemmas
-- The fields of an encoded object unfold Lean's `Json.mkObj`.
import all Lean.Data.Json.Basic
-- The digits of `Nat.toDigits` must unfold for `decide` to read them.
import all Init.Data.Repr

/-!
# Proofs: the JSON form of the base types

The readers read the value of a hex digit from its ASCII byte.

They read back each digit that the hex encoder writes.

Those digits are lowercase, so this holds whether or not the readers accept uppercase.

The byte string readers read back the bytes of their hex encoding.

That holds for byte strings of any length and of a given size.

Whether the reader accepts uppercase digits does not matter there.

The proofs rest on two facts about the encoding.

Its characters are ASCII.

It writes two digits for each byte.

A number that the reader checks against `2^bits` is below `2^bits`.

So the 64-bit reader returns the decoded number itself, without wrapping.

A byte string decoded with a limit on its size has at most that many bytes.

A field of an object decodes to the value that the object holds under its name.

A list decodes exactly when the value is an array whose items each decode, in order.

A byte string of a fixed size, such as an address, decodes exactly to the vector of its bytes.

A number below the bound, written in lowercase hex without leading zeros, decodes to itself.

No other text decodes to a number.

The encoder of numbers writes exactly that text, so two numbers never share an encoding.

The encoder of lists writes what the list reader reads back, item by item.

A byte string without uppercase digits decodes exactly from `0x` and two lowercase digits per byte.

An address, whose digits may be uppercase, decodes exactly from `0x` and two digits per byte.

Each of those digits is in either case, and their lowercase forms are the hex encoding.

The 64-bit reader returns a number exactly when the reader with the bound `2^64` returns it.

The bounded byte reader succeeds exactly when the byte reader succeeds within the limit.

An object built from pairs with distinct names holds exactly those pairs.

A number reads as an integer exactly when its value is a whole number.

A value reads as an error object exactly when its only members are a code, a message and data.

The data may be missing.
-/

public section

namespace EthLib.Serialization.JsonRpc

open EthLib.Base

/-- A rejection is that failure, never a value. -/
@[simp] theorem reject_eq {α : Type} (reason : String) : (reject reason : Read α) = .error reason :=
  rfl

/-- The decoders read the value of each digit that the hex encoder writes. -/
theorem hexValue_hexDigitChar (upper : Bool) (n : Fin 16) :
    hexValue upper (hexDigitChar n).toUInt8 = some n.val.toUInt8 := by
  decide +revert

/-- A decoded number is below the bound that the decoder checks. -/
theorem lt_of_quantity {what : String} {bits : Nat} {j : Lean.Json} {value : Nat}
    (h : quantity what bits j = .ok value) : value < 2 ^ bits := by
  unfold quantity at h
  obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
  -- The last step compares the number with the bound.
  split at h
  · cases h
    assumption
  · cases h

/-- A decoded 64-bit number is the number read with the bound `2^64`, so it does not wrap. -/
theorem quantity_of_uint64 {what : String} {j : Lean.Json} {x : UInt64}
    (h : uint64 what j = .ok x) : quantity what 64 j = .ok x.toNat := by
  unfold uint64 at h
  obtain ⟨value, hq, hx⟩ := bind_ok_iff.mp h
  cases hx
  -- The value is below `2^64`, so its conversion keeps it.
  rw [hq, Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (lt_of_quantity hq)]

/-- A byte string decoded with a limit has at most that many bytes. -/
theorem size_le_of_bytesMax {what : String} {n : Nat} {j : Lean.Json} {b : ByteArray}
    (h : bytesMax what n j = .ok b) : b.size ≤ n := by
  unfold bytesMax at h
  obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
  split at h
  · cases h
    assumption
  · cases h

/-- A 64-bit number decodes to `x` exactly when the number read with the bound `2^64` is `x`. -/
theorem uint64_eq_ok_iff {what : String} {j : Lean.Json} {x : UInt64} :
    uint64 what j = .ok x ↔ quantity what 64 j = .ok x.toNat := by
  refine ⟨quantity_of_uint64, fun h => ?_⟩
  unfold uint64
  rw [h]
  simp [bind, Except.bind, pure, Except.pure]

/-- A byte string decodes within a limit exactly when it decodes and fits the limit. -/
theorem bytesMax_eq_ok_iff {what : String} {n : Nat} {j : Lean.Json} {b : ByteArray} :
    bytesMax what n j = .ok b ↔ bytes what j = .ok b ∧ b.size ≤ n := by
  unfold bytesMax
  constructor
  · intro h
    obtain ⟨c, hc, h⟩ := bind_ok_iff.mp h
    split at h
    · cases h
      exact ⟨hc, by assumption⟩
    · cases h
  · rintro ⟨h, hn⟩
    rw [h]
    simp [bind, Except.bind, hn, pure, Except.pure]

/-- ASCII characters encode to their own bytes. -/
theorem ascii_utf8Encode (l : List Char) (h : ∀ c ∈ l, c.val ≤ 0x7F) :
    l.utf8Encode = (l.map fun c => c.val.toUInt8).toByteArray := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    have hc : c.utf8Size = 1 := by simp [Char.utf8Size, h c (by simp)]
    rw [List.utf8Encode_cons, List.utf8Encode_singleton, ih (fun d hd => h d (by simp [hd])),
      String.utf8EncodeChar_eq_singleton hc, List.map_cons]
    exact (List.toByteArray_append (l := [c.val.toUInt8])).symm

/-- Entry `2 * i` and `2 * i + 1` of a list that holds two entries per element. -/
private theorem flatMap_pair_getElem? {α β : Type} (x y : α → β) (l : List α) (i : Nat) :
    (l.flatMap fun a => [x a, y a])[2 * i]? = l[i]?.map x ∧
    (l.flatMap fun a => [x a, y a])[2 * i + 1]? = l[i]?.map y := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    cases i with
    | zero => simp
    | succ i =>
      have := ih i
      simp only [List.flatMap_cons, List.cons_append]
      constructor
      · rw [show 2 * (i + 1) = 2 * i + 1 + 1 by omega]; simpa using this.1
      · rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 by omega]; simpa using this.2

/-- A loop that pushes one byte per index returns the bytes it pushed. -/
private theorem forIn_range'_push {s k : Nat}
    {f : Nat → ByteArray → Except String (ForInStep ByteArray)}
    (g : Nat → UInt8) (h : ∀ i out, i ∈ List.range' s k → f i out = .ok (.yield (out.push (g i))))
    (out : ByteArray) :
    forIn (List.range' s k) out f = .ok (out ++ ((List.range' s k).map g).toByteArray) := by
  induction k generalizing s out with
  | zero => simp [List.range'_zero]; rfl
  | succ k ih =>
    rw [List.range'_succ, List.forIn_cons, h s out (by simp [List.range'_succ])]
    simp only [bind, Except.bind]
    rw [ih (fun i o hi => h i o (by simp [List.range'_succ, hi]))]
    congr 1
    apply ByteArray.ext
    simp [List.map_cons]

/-- The hex digits are ASCII. -/
private theorem hexDigitChar_ascii (n : Fin 16) : (hexDigitChar n).val ≤ 0x7F := by
  revert n; decide +revert

/-- The digits after the marker `0x` of an ASCII text are the codes of its characters. -/
theorem hexDigits_ascii (what : String) (l : List Char) (h : ∀ c ∈ l, c.val ≤ 0x7F) :
    hexDigits what (.str ("0x" ++ String.ofList l)) =
      .ok (l.map fun c => c.val.toUInt8).toByteArray := by
  unfold hexDigits
  have hascii : ∀ c ∈ '0' :: 'x' :: l, c.val ≤ 0x7F := by
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | rfl | hc
    · decide
    · decide
    · exact h c hc
  have hs : ("0x" ++ String.ofList l).toUTF8 =
      ('0'.val.toUInt8 :: 'x'.val.toUInt8 :: l.map fun c => c.val.toUInt8).toByteArray := by
    have : ("0x" ++ String.ofList l) = String.ofList ('0' :: 'x' :: l) := by
      apply String.ext; simp
    rw [this, String.toUTF8_eq_toByteArray, String.toByteArray_ofList, ascii_utf8Encode _ hascii]
    rfl
  simp only [hs]
  generalize l.map (fun c => c.val.toUInt8) = ds
  have h0 : '0'.val.toUInt8 = 48 := by decide
  have hx : 'x'.val.toUInt8 = 120 := by decide
  rw [h0, hx]
  have h1 : (48 :: 120 :: ds).toByteArray[0]? = some 48 := by simp
  have h2 : (48 :: 120 :: ds).toByteArray[1]? = some 120 := by simp
  simp only [h1, h2, and_self, ↓reduceIte]
  congr 1
  apply ByteArray.ext
  simp [ByteArray.data_extract]

/-- The digits after the marker `0x` of a hex encoding are the ASCII codes of its characters. -/
theorem hexDigits_hexString (what : String) (data : List UInt8) :
    hexDigits what (.str (hexString data)) =
      .ok ((data.flatMap byteHexDigits).map fun c => c.val.toUInt8).toByteArray := by
  have htext : hexString data = "0x" ++ String.ofList (data.flatMap byteHexDigits) := by
    apply String.ext
    simp [toList_hexString]
  rw [htext]
  refine hexDigits_ascii what _ fun c hc => ?_
  simp only [List.mem_flatMap, byteHexDigits, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with ⟨b, -, rfl | rfl⟩ <;> exact hexDigitChar_ascii _

/-- A byte is sixteen times its high digit plus its low digit. -/
private theorem byte_split (b : UInt8) :
    16 * (b.toNat / 16).toUInt8 + (b.toNat % 16).toUInt8 = b := by
  have h := b.toNat_lt
  apply UInt8.toNat_inj.mp
  simp only [UInt8.toNat_add, UInt8.toNat_mul, Nat.toUInt8_eq, UInt8.toNat_ofNat,
    UInt8.toNat_ofNat']
  omega

/-- The sum of a list of twos is twice its length. -/
private theorem sum_two (l : List UInt8) : (l.map fun _ => 2).sum = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; omega

/-- The high digit of a byte. -/
private def highDigit (b : UInt8) : Fin 16 := ⟨b.toNat / 16, by have := b.toNat_lt; omega⟩

/-- The low digit of a byte. -/
private def lowDigit (b : UInt8) : Fin 16 := ⟨b.toNat % 16, by omega⟩

/-- The two digits of each byte of a list, at positions `2 * i` and `2 * i + 1` of its encoding. -/
private theorem flatMap_byteHexDigits_getElem? (data : List UInt8) (i : Nat) :
    (data.flatMap byteHexDigits)[2 * i]? = data[i]?.map (fun b => hexDigitChar (highDigit b)) ∧
    (data.flatMap byteHexDigits)[2 * i + 1]? = data[i]?.map (fun b => hexDigitChar (lowDigit b)) :=
  flatMap_pair_getElem? (fun b => hexDigitChar (highDigit b)) (fun b => hexDigitChar (lowDigit b))
    data i

/-- The hex encoding writes two digits for each byte. -/
private theorem length_flatMap_byteHexDigits (data : List UInt8) :
    (data.flatMap byteHexDigits).length = 2 * data.length := by
  rw [List.length_flatMap]
  simp only [byteHexDigits, List.length_cons, List.length_nil]
  exact sum_two data

/-- The decoder returns the bytes whose two digits it reads at positions `2 * i` and `2 * i + 1`.

This holds when the text after `0x` has exactly two digit codes for each byte. -/
private theorem bytesOf_of_hexDigits {what : String} {upper : Bool} {j : Lean.Json}
    {ds data : List UInt8} (hj : hexDigits what j = .ok ds.toByteArray)
    (hlen : ds.length = 2 * data.length)
    (hidx : ∀ (i : Nat) (hi : i < data.length),
      ds[2 * i]?.bind (hexValue upper) = some (highDigit data[i]).val.toUInt8 ∧
        ds[2 * i + 1]?.bind (hexValue upper) = some (lowDigit data[i]).val.toUInt8) :
    bytesOf what upper j = .ok data.toByteArray := by
  unfold bytesOf
  rw [hj]
  simp only [bind, Except.bind, pure, Except.pure]
  have hsz : ds.toByteArray.size = 2 * data.length := by simpa using hlen
  have hne : ¬ (ds.toByteArray.size % 2 ≠ 0) := by omega
  simp only [hne, ↓reduceIte]
  rw [show ds.toByteArray.size / 2 = data.length by omega]
  have hr : List.range' [:data.length].start [:data.length].size [:data.length].step =
      List.range' 0 data.length 1 := by
    rw [show [:data.length].size = data.length by simp [Std.Legacy.Range.size]]
  rw [Std.Legacy.Range.forIn_eq_forIn_range', hr,
    forIn_range'_push (fun i => data.getD i 0) ?_]
  · show Except.ok _ = Except.ok _
    congr 1
    apply ByteArray.ext
    simp only [ByteArray.data_append, List.data_toByteArray]
    have hm : (List.range' 0 data.length).map (fun i => data.getD i 0) = data := by
      apply List.ext_getElem (by simp)
      intro n h1 h2
      simp [List.getD_eq_getElem?_getD, h2]
    rw [hm]
    simp [ByteArray.emptyWithCapacity]
    rfl
  · intro i out hi
    rw [List.mem_range'_1] at hi
    have hi' : i < data.length := by omega
    have e : ∀ j : Nat, ds.toByteArray[j]? = ds[j]? := by
      intro j
      rw [getElem?_def, getElem?_def]
      simp
    obtain ⟨h0, h1⟩ := hidx i hi'
    obtain ⟨c, hc, hv1⟩ := Option.bind_eq_some_iff.mp h0
    obtain ⟨d, hd, hv2⟩ := Option.bind_eq_some_iff.mp h1
    rw [e, e, hc, hd]
    simp only
    rw [hv1, hv2, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
    exact congrArg (fun x => Except.ok (ForInStep.yield (out.push x))) (byte_split data[i])

/-- The decoder reads back the bytes of their hex encoding.

This holds whether or not it accepts uppercase digits. -/
theorem bytesOf_hexString (what : String) (upper : Bool) (data : List UInt8) :
    bytesOf what upper (.str (hexString data)) = .ok data.toByteArray := by
  refine bytesOf_of_hexDigits (hexDigits_hexString what data)
    (by rw [List.length_map, length_flatMap_byteHexDigits]) fun i hi => ?_
  obtain ⟨h0, h1⟩ := flatMap_byteHexDigits_getElem? data i
  rw [List.getElem?_map, List.getElem?_map, h0, h1, List.getElem?_eq_getElem hi]
  have hv1 := hexValue_hexDigitChar upper (highDigit data[i])
  have hv2 := hexValue_hexDigitChar upper (lowDigit data[i])
  simp only [Char.toUInt8] at hv1 hv2
  exact ⟨hv1, hv2⟩

/-- The decoder of byte strings reads back the bytes of their hex encoding. -/
theorem bytes_hexString (what : String) (data : List UInt8) :
    bytes what (.str (hexString data)) = .ok data.toByteArray :=
  bytesOf_hexString what false data

/-- The decoder of byte strings of a size reads back the bytes of their hex encoding. -/
theorem fixed_hexString (what : String) (n : Nat) (v : Vector UInt8 n) (upper : Bool) :
    fixed what n (.str (hexString v.toList)) upper = .ok v := by
  unfold fixed
  rw [bytesOf_hexString]
  simp only [bind, Except.bind]
  have h : (v.toList.toByteArray).data.size = n := by simp
  simp only [h, ↓reduceDIte]
  simp only [pure, Except.pure]
  congr 1
  exact Vector.toArray_inj.mp (by
    simp only [List.data_toByteArray]
    rw [← Vector.toArray_toList])

/-- A field of an object decodes to a value exactly when the object holds it under that name. -/
theorem field_eq_ok_iff {what name : String} {fs : List (String × Lean.Json)} {v : Lean.Json} :
    field what fs name = .ok v ↔ fs.lookup name = some v := by
  unfold field
  cases h : fs.lookup name <;>
    simp [pure, Except.pure]

/-- A string decodes exactly from its JSON string. -/
theorem string_eq_ok_iff {what : String} {j : Lean.Json} {s : String} :
    string what j = .ok s ↔ j = .str s := by
  cases j <;> simp [string, pure, Except.pure]

/-- A list decodes exactly when the value is an array whose items each decode, in order.

Item `i` of the list is the decoded item `i` of the array. -/
theorem array_eq_ok_iff {α : Type} {what : String} {f : Lean.Json → Read α} {j : Lean.Json}
    {l : List α} :
    array what f j = .ok l ↔
      ∃ items : Array Lean.Json, j = .arr items ∧
        ∃ h : l.length = items.size, ∀ (i : Nat) (hi : i < items.size), f items[i] = .ok l[i] := by
  cases j with
  | arr items =>
    simp only [array, Lean.Json.arr.injEq, exists_eq_left', mapM_eq_ok_iff]
    simp
  -- Any other JSON value is not an array, so the read fails at once.
  | _ => simp [array]

/-- A byte string of a fixed size decodes to a vector exactly when its bytes are the vector's.

The decoder of byte strings must then return exactly those bytes, so their number is the size. -/
theorem fixed_eq_ok_iff {what : String} {n : Nat} {j : Lean.Json} {upper : Bool}
    {v : Vector UInt8 n} :
    fixed what n j upper = .ok v ↔ bytesOf what upper j = .ok ⟨v.toArray⟩ := by
  unfold fixed
  constructor
  · intro h
    obtain ⟨b, hb, h⟩ := bind_ok_iff.mp h
    -- A string of another size fails, so the bytes have the size and form the vector.
    split at h
    · cases h
      rw [hb]
    · cases h
  · intro h
    rw [h]
    simp [bind, Except.bind, pure, Except.pure, v.size_toArray]

/-- An address decodes exactly when its bytes are the address's, with uppercase digits allowed. -/
theorem address_eq_ok_iff {what : String} {j : Lean.Json} {a : Address} :
    address what j = .ok a ↔ bytesOf what true j = .ok ⟨a.toArray⟩ :=
  fixed_eq_ok_iff

/-! ## A number written in hex -/

/-- The value of the code of a hex digit, or zero for any other code. -/
@[expose] def digitValue (c : UInt8) : Nat := ((hexValue false c).getD 0).toNat

/-- The digit that Lean core writes for a value below sixteen is the lowercase hex digit. -/
private theorem digitChar_eq_hexDigitChar : ∀ n (h : n < 16),
    Nat.digitChar n = hexDigitChar ⟨n, h⟩ := by
  decide

/-- Each digit that `Nat.toDigits 16` writes is a lowercase hex digit, read back as its value. -/
theorem hexValue_digitChar (n : Nat) (hn : n < 16) :
    hexValue false (Nat.digitChar n).val.toUInt8 = some n.toUInt8 ∧
      (Nat.digitChar n).val ≤ 0x7F := by
  rw [digitChar_eq_hexDigitChar n hn]
  exact ⟨hexValue_hexDigitChar false ⟨n, hn⟩, hexDigitChar_ascii _⟩

/-- No digit of a positive value below sixteen is the digit `0`. -/
private theorem digitChar_ne_zero : ∀ n, n < 16 → 0 < n → ¬ Nat.digitChar n = '0' := by
  decide

/-- The hex digits of a number are ASCII digits whose values, read from the first, give the number.

A positive number does not start with the digit `0`. -/
theorem toDigits_hex (n : Nat) :
    (∀ c ∈ Nat.toDigits 16 n, ∃ d, d < 16 ∧ c = Nat.digitChar d) ∧
      ((Nat.toDigits 16 n).map fun c => c.val.toUInt8).foldl
        (fun acc c => 16 * acc + digitValue c) 0 = n ∧
      (0 < n → (Nat.toDigits 16 n).head? ≠ some '0') := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [Nat.toDigits_eq_ite (by decide : 1 < 16)]
    split
    · rename_i hn
      refine ⟨?_, ?_, ?_⟩
      · intro c hc
        exact ⟨n, hn, by simpa using hc⟩
      · simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, digitValue]
        rw [(hexValue_digitChar n hn).1]
        simp [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega : n < 256)]
      · intro hpos
        simp only [List.head?_cons, ne_eq, Option.some.injEq]
        exact digitChar_ne_zero n hn hpos
    · rename_i hn
      have hq : n / 16 < n := by omega
      obtain ⟨hall, hval, hhead⟩ := ih (n / 16) hq
      refine ⟨?_, ?_, ?_⟩
      · intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · exact hall c hc
        · exact ⟨n % 16, by omega, by simpa using hc⟩
      · rw [List.map_append, List.foldl_append, hval]
        simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, digitValue]
        rw [(hexValue_digitChar (n % 16) (by omega)).1]
        simp [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega : n % 16 < 256)]
        omega
      · intro _
        have hne := Nat.toDigits_ne_nil (b := 16) (n := n / 16)
        obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
        have := hhead (by omega)
        rw [hx] at this ⊢
        simpa using this

/-- A digit whose code is that of `0` is the digit `0`. -/
private theorem digitChar_code_zero : ∀ n, n < 16 →
    (Nat.digitChar n).val.toUInt8 = 48 → Nat.digitChar n = '0' := by
  decide

/-- A loop whose step multiplies by sixteen and adds the value of a digit computes the fold. -/
private theorem forIn_digits {ds : List UInt8}
    {f : UInt8 → Nat → Except String (ForInStep Nat)}
    (h : ∀ c ∈ ds, ∀ s, f c s = .ok (.yield (16 * s + digitValue c))) (acc : Nat) :
    forIn ds acc f = .ok (ds.foldl (fun a c => 16 * a + digitValue c) acc) := by
  induction ds generalizing acc with
  | nil => rfl
  | cons c ds ih =>
    rw [List.forIn_cons, h c (by simp) acc]
    exact ih (fun c' hc' s => h c' (by simp [hc']) s) _

/-- The decoder of numbers of any size reads back a number, written in lowercase hex.

The text is `0x` and the digits of the number, without leading zeros, and `0x0` for zero.

The converse, that no other text decodes to the number, is proved below. -/
theorem uint_quantityJson (what : String) (v : Nat) : uint what (quantityJson v) = .ok v := by
  unfold quantityJson
  obtain ⟨hall, hval, hhead⟩ := toDigits_hex v
  have hascii : ∀ c ∈ Nat.toDigits 16 v, c.val ≤ 0x7F := by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := hall c hc
    exact (hexValue_digitChar d hd).2
  unfold uint
  rw [hexDigits_ascii _ _ hascii]
  simp only [bind, Except.bind]
  have hne := Nat.toDigits_ne_nil (b := 16) (n := v)
  have hsize : (List.map (fun c => c.val.toUInt8) (Nat.toDigits 16 v)).toByteArray.size =
      (Nat.toDigits 16 v).length := by simp
  -- There is at least one digit.
  rw [ite_eq_right (by rw [hsize]; exact fun h => hne (List.length_eq_zero_iff.mp h))]
  -- The first digit is `0` only for the number 0, which has no other digit.
  rw [ite_eq_right]
  · -- Every digit is read, and the digits give the number.
    rw [forIn_eq_forIn_toList]
    have hdata : (List.map (fun c => c.val.toUInt8) (Nat.toDigits 16 v)).toByteArray.data.toList =
        List.map (fun c => c.val.toUInt8) (Nat.toDigits 16 v) := by simp
    rw [hdata, forIn_digits, hval]
    · rfl
    · intro c hc s
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
      obtain ⟨d, hd, rfl⟩ := hall c' hc'
      simp only [digitValue, (hexValue_digitChar d hd).1, Option.getD_some]
      rfl
  · rintro ⟨hgt, hzero⟩
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
    rw [hx] at hzero hgt
    have hx48 : x.val.toUInt8 = 48 := by simpa using hzero
    obtain ⟨d, hd, rfl⟩ := hall x (by simp [hx])
    have hpos : 0 < v := by
      rcases Nat.eq_zero_or_pos v with rfl | hp
      · simp [Nat.toDigits_zero] at hx
        obtain ⟨rfl, rfl⟩ := hx
        simp at hgt
      · exact hp
    exact hhead hpos (by rw [hx]; simp [digitChar_code_zero d hd hx48])

/-- The decoder of numbers reads back a number below its bound, written in lowercase hex.

The converse also holds: no other text decodes to the number. -/
theorem quantity_toDigits (what : String) {bits v : Nat} (hv : v < 2 ^ bits) :
    quantity what bits (quantityJson v) = .ok v := by
  unfold quantity
  rw [uint_quantityJson]
  simp [hv, bind, Except.bind, pure, Except.pure]

/-- The decoder of 64-bit numbers reads back any 64-bit number, written in lowercase hex. -/
theorem uint64_toDigits (what : String) (x : UInt64) :
    uint64 what (quantityJson x.toNat) = .ok x :=
  uint64_eq_ok_iff.mpr (quantity_toDigits what x.toNat_lt)

/-! ## Only the canonical text decodes -/

/-- The fact below, checked by the kernel on each of the 256 codes. -/
private theorem digitChar_digitValue_lt : ∀ n, n < 256 →
    (hexValue false n.toUInt8).isSome = true →
    digitValue n.toUInt8 < 16 ∧ (Nat.digitChar (digitValue n.toUInt8)).val.toUInt8 = n.toUInt8 ∧
      (n.toUInt8 ≠ 48 → 0 < digitValue n.toUInt8) := by
  decide +kernel

/-- A code that the decoder reads as a hex digit is the code of the digit of its value.

Only the code of `0` has the value zero. -/
private theorem digitChar_digitValue (c : UInt8) (h : (hexValue false c).isSome = true) :
    digitValue c < 16 ∧ (Nat.digitChar (digitValue c)).val.toUInt8 = c ∧
      (c ≠ 48 → 0 < digitValue c) := by
  have := digitChar_digitValue_lt c.toNat c.toNat_lt
  simp only [show c.toNat.toUInt8 = c from UInt8.ofNat_toNat] at this
  exact this h

/-- A loop whose step reads a hex digit and fails on any other code succeeds only on hex digits. -/
private theorem forIn_digits_ok {ds : List UInt8}
    {f : UInt8 → Nat → Except String (ForInStep Nat)}
    (hf : ∀ c s r, f c s = .ok r → (hexValue false c).isSome = true ∧
      r = .yield (16 * s + digitValue c))
    {acc w : Nat} (h : forIn ds acc f = .ok w) :
    (∀ c ∈ ds, (hexValue false c).isSome = true) ∧
      w = ds.foldl (fun a c => 16 * a + digitValue c) acc := by
  induction ds generalizing acc with
  | nil => exact ⟨by simp, by cases h; rfl⟩
  | cons c ds ih =>
    rw [List.forIn_cons] at h
    obtain ⟨r, hr, h⟩ := bind_ok_iff.mp h
    obtain ⟨hc, rfl⟩ := hf c acc r hr
    obtain ⟨hall, hw⟩ := ih h
    exact ⟨fun c' hc' => (List.mem_cons.mp hc').elim (· ▸ hc) (hall c'), hw⟩

/-- Digits read from a positive first digit give a number at least that digit. -/
private theorem foldl_digits_pos {ds : List UInt8} {acc : Nat} (h : 0 < acc) :
    0 < ds.foldl (fun a c => 16 * a + digitValue c) acc := by
  induction ds generalizing acc with
  | nil => exact h
  | cons c ds ih => exact ih (by simp only; omega)

/-- Hex digits without a leading `0` are what `Nat.toDigits 16` writes for their value. -/
private theorem digits_canonical : ∀ (k : Nat) (ds : List UInt8), ds.length = k → ds ≠ [] →
    (∀ c ∈ ds, (hexValue false c).isSome = true) → (1 < ds.length → ds.head? ≠ some 48) →
    ds = (Nat.toDigits 16 (ds.foldl (fun a c => 16 * a + digitValue c) 0)).map
      fun c => c.val.toUInt8 := by
  intro k
  induction k with
  | zero => intro ds hk hne; exact absurd (List.length_eq_zero_iff.mp hk) hne
  | succ k ih =>
    intro ds hk hne hall hlead
    obtain ⟨l, c, rfl⟩ : ∃ l c, ds = l ++ [c] := by
      rcases List.eq_nil_or_concat ds with h | ⟨l, c, h⟩
      · exact absurd h hne
      · exact ⟨l, c, by simpa using h⟩
    have hc := digitChar_digitValue c (hall c (by simp))
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases hl : l = []
    · -- One digit: its value is below sixteen and `Nat.toDigits` writes that digit.
      subst hl
      simp only [List.nil_append, List.foldl_nil, Nat.mul_zero, Nat.zero_add]
      rw [Nat.toDigits_eq_ite (by decide), ite_eq_left hc.1]
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
      exact hc.2.1.symm
    · -- Several digits: the first is not `0`, so the digits before the last give a positive number.
      obtain ⟨y, ys, hy⟩ := List.exists_cons_of_ne_nil hl
      have hy48 : y ≠ 48 := by
        have := hlead (by simp [hy])
        subst hy
        simpa using this
      have hpos : 0 < l.foldl (fun a c => 16 * a + digitValue c) 0 := by
        rw [hy, List.foldl_cons]
        have := (digitChar_digitValue y (hall y (by simp [hy]))).2.2 hy48
        exact foldl_digits_pos (by omega)
      have hih := ih l (by simp at hk; omega) hl (fun c' hc' => hall c' (by simp [hc']))
        (fun _ => by rw [hy]; simpa using hy48)
      generalize l.foldl (fun a c => 16 * a + digitValue c) 0 = n at hpos hih
      have hge : ¬ 16 * n + digitValue c < 16 := by omega
      rw [Nat.toDigits_eq_ite (by decide), ite_eq_right hge,
        show (16 * n + digitValue c) / 16 = n by omega,
        show (16 * n + digitValue c) % 16 = digitValue c by omega, List.map_append]
      congr 1
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
      exact hc.2.1.symm

/-- A text from which the decoder reads digits is `0x` and the codes of those digits. -/
private theorem toUTF8_of_hexDigits {what s : String} {digits : ByteArray}
    (h : hexDigits what (.str s) = .ok digits) :
    s.toUTF8.data.toList = 48 :: 120 :: digits.data.toList := by
  unfold hexDigits at h
  dsimp only at h
  split at h
  · rename_i hm
    cases h
    obtain ⟨h0, h1⟩ := hm
    generalize s.toUTF8 = b at h0 h1 ⊢
    obtain ⟨arr⟩ := b
    obtain ⟨l⟩ := arr
    have hsize : (ByteArray.mk ⟨l⟩).size = l.length := rfl
    have hx : (ByteArray.mk ⟨l⟩).extract 2 (ByteArray.mk ⟨l⟩).size = ByteArray.mk ⟨l.drop 2⟩ := by
      apply ByteArray.ext
      simp only [ByteArray.data_extract, hsize, List.extract_toArray]
      simp [List.take_of_length_le]
    rw [hx]
    -- The first two bytes are those of `0` and `x`.
    match l, h0, h1 with
    | x :: y :: rest, h0, h1 =>
      have e0 : (ByteArray.mk ⟨x :: y :: rest⟩)[0]? = some x := rfl
      have e1 : (ByteArray.mk ⟨x :: y :: rest⟩)[1]? = some y := rfl
      rw [e0] at h0
      rw [e1] at h1
      cases Option.some.inj h0
      cases Option.some.inj h1
      rfl
  · cases h

/-- The decoder of numbers of any size returns a number exactly when the text is its canonical text.

That text is `0x` and the lowercase hex digits of the number, without leading zeros.

So uppercase digits, leading zeros, `0x` alone and any other text are rejected. -/
theorem uint_eq_ok_iff {what : String} {j : Lean.Json} {v : Nat} :
    uint what j = .ok v ↔ j = quantityJson v := by
  unfold quantityJson
  constructor
  · intro h'
    unfold uint at h'
    cases j with
    | str s =>
      obtain ⟨digits, hd, h'⟩ := bind_ok_iff.mp h'
      dsimp only at h'
      -- A text with no digits, or with a leading `0` before other digits, fails.
      split at h'
      · cases h'
      rename_i hsize
      split at h'
      · cases h'
      rename_i hlead
      -- The loop reads every digit, and the value it returns is the number.
      obtain ⟨w, hw, h'⟩ := bind_ok_iff.mp h'
      have hwv : w = v := Except.ok.inj h'
      subst hwv
      rw [forIn_eq_forIn_toList] at hw
      obtain ⟨hall, hval⟩ := forIn_digits_ok (fun c s r hr => by
        cases hc : hexValue false c with
        | none => simp [hc, bind, Except.bind] at hr
        | some d =>
          simp only [hc, pure, Except.pure, Except.ok.injEq] at hr
          exact ⟨rfl, by rw [← hr, digitValue, hc]; rfl⟩) hw
      -- Those digits are the canonical digits of the number.
      have hcanon := digits_canonical _ _ rfl
        (fun hnil => hsize (by simp [ByteArray.size, ← Array.length_toList, hnil]))
        hall
        (fun hlen hzero => hlead ⟨by simpa [ByteArray.size, ← Array.length_toList] using hlen,
          by obtain ⟨arr⟩ := digits; obtain ⟨l⟩ := arr; cases l with
            | nil => simp at hzero
            | cons x xs =>
              have hx : x = 48 := by simpa using hzero
              subst hx
              rfl⟩)
      rw [← hval] at hcanon
      -- So the text has the bytes of the canonical text, and is that text.
      have ht := toUTF8_of_hexDigits (hexDigits_ascii what (Nat.toDigits 16 w) fun c hc => by
        obtain ⟨d, hdl, rfl⟩ := (toDigits_hex w).1 c hc
        exact (hexValue_digitChar d hdl).2)
      have hs := toUTF8_of_hexDigits hd
      rw [List.data_toByteArray, ← hcanon, ← hs] at ht
      congr 1
      apply String.toByteArray_inj.mp
      rw [← String.toUTF8_eq_toByteArray, ← String.toUTF8_eq_toByteArray]
      exact ByteArray.ext (Array.ext' ht.symm)
    -- Any other JSON value is not a string, so the read fails at once.
    | _ =>
      obtain ⟨digits, hd, -⟩ := bind_ok_iff.mp h'
      simp [hexDigits] at hd
  · rintro rfl
    exact uint_quantityJson what v

/-- The decoder of numbers returns a number exactly when the text is the canonical text of it.

That text is `0x` and the lowercase hex digits of the number, without leading zeros.

The number must also be below the bound of the decoder.

So uppercase digits, leading zeros, `0x` alone and any other text are rejected. -/
theorem quantity_eq_ok_iff {what : String} {bits : Nat} {j : Lean.Json} {v : Nat} :
    quantity what bits j = .ok v ↔ v < 2 ^ bits ∧ j = quantityJson v := by
  constructor
  · intro h
    refine ⟨lt_of_quantity h, ?_⟩
    unfold quantity at h
    obtain ⟨w, hw, h⟩ := bind_ok_iff.mp h
    split at h
    · cases h
      exact uint_eq_ok_iff.mp hw
    · cases h
  · rintro ⟨hv, rfl⟩
    exact quantity_toDigits what hv

/-! ## Only the canonical text decodes to bytes -/

/-- A code that the decoder reads as a lowercase hex digit is the code of the digit of its value.

That value is below sixteen. -/
private theorem hexDigitChar_hexValue (c : UInt8) (h : (hexValue false c).isSome = true) :
    (hexDigitChar ⟨digitValue c % 16, Nat.mod_lt _ (by decide)⟩).val.toUInt8 = c ∧
      digitValue c < 16 := by
  obtain ⟨below, code, -⟩ := digitChar_digitValue c h
  have digit : (⟨digitValue c % 16, Nat.mod_lt _ (by decide)⟩ : Fin 16) = ⟨digitValue c, below⟩ :=
    Fin.ext (Nat.mod_eq_of_lt below)
  rw [digit, ← digitChar_eq_hexDigitChar _ below]
  exact ⟨code, below⟩

/-- A loop over indices whose every step pushes one byte returns those bytes, each with its fact. -/
private theorem forIn_range'_ok {Q : Nat → UInt8 → Prop} {s k : Nat}
    {f : Nat → ByteArray → Except String (ForInStep ByteArray)}
    (hf : ∀ i out r, f i out = .ok r → ∃ x, r = .yield (out.push x) ∧ Q i x)
    {out res : ByteArray} (h : forIn (List.range' s k) out f = .ok res) :
    ∃ xs : List UInt8, xs.length = k ∧ res = out ++ xs.toByteArray ∧
      ∀ (j : Nat) (hj : j < xs.length), Q (s + j) xs[j] := by
  induction k generalizing s out with
  | zero =>
    refine ⟨[], rfl, ?_, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    simp only [List.range'_zero, List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h
    rw [← h]
    apply ByteArray.ext
    simp
  | succ k ih =>
    rw [List.range'_succ, List.forIn_cons] at h
    obtain ⟨r, hr, h⟩ := bind_ok_iff.mp h
    obtain ⟨x, rfl, hx⟩ := hf s out r hr
    obtain ⟨xs, hlen, hres, hq⟩ := ih h
    refine ⟨x :: xs, by simp [hlen], ?_, ?_⟩
    · rw [hres]
      apply ByteArray.ext
      simp
    · intro j hj
      cases j with
      | zero => simpa using hx
      | succ j =>
        have := hq j (by simpa using hj)
        rw [show s + 1 + j = s + (j + 1) by omega] at this
        exact this

/-- A byte of a buffer, read with a check, is the entry of the list of its bytes. -/
private theorem getElem?_eq_data_toList (b : ByteArray) (i : Nat) : b[i]? = b.data.toList[i]? := by
  have hs : b.data.toList.length = b.size := Array.length_toList
  by_cases h : i < b.size
  · rw [getElem?_pos b i h, List.getElem?_eq_getElem (by omega)]
    simp only [Array.getElem_toList]
    rfl
  · rw [getElem?_neg b i h, List.getElem?_eq_none (by omega)]

/-- The fact below, checked by the kernel on each of the 256 codes, with and without uppercase. -/
private theorem hexValue_lt_lt : ∀ n, n < 256 → ∀ upper : Bool,
    (hexValue upper n.toUInt8).isSome = true →
      n < 128 ∧ ((hexValue upper n.toUInt8).getD 0).toNat < 16 := by
  decide +kernel

/-- A code that the decoder reads as a hex digit is ASCII, and its value is below sixteen. -/
private theorem hexValue_lt {upper : Bool} {c v : UInt8} (h : hexValue upper c = some v) :
    c.toNat < 128 ∧ v.toNat < 16 := by
  have := hexValue_lt_lt c.toNat c.toNat_lt upper
  simp only [show c.toNat.toUInt8 = c from UInt8.ofNat_toNat, h, Option.isSome_some,
    Option.getD_some, forall_const] at this
  exact this

/-- A byte of two digits below sixteen has those digits as its high and low digit. -/
private theorem highDigit_lowDigit {u v : UInt8} (hu : u.toNat < 16) (hv : v.toNat < 16) :
    (highDigit (16 * u + v)).val.toUInt8 = u ∧ (lowDigit (16 * u + v)).val.toUInt8 = v := by
  have hx : (16 * u + v).toNat = 16 * u.toNat + v.toNat := by
    simp only [UInt8.toNat_add, UInt8.toNat_mul]
    simp
    omega
  constructor
  · apply UInt8.toNat_inj.mp
    simp only [highDigit, hx, Nat.toUInt8_eq, UInt8.toNat_ofNat']
    omega
  · apply UInt8.toNat_inj.mp
    simp only [lowDigit, hx, Nat.toUInt8_eq, UInt8.toNat_ofNat']
    omega

/-- The decoder returns bytes only from text after `0x` with two digit codes for each byte.

The codes at positions `2 * i` and `2 * i + 1` have the values of the two digits of byte `i`. -/
private theorem bytesOf_eq_ok_digits {what : String} {upper : Bool} {j : Lean.Json}
    {b : ByteArray} (h : bytesOf what upper j = .ok b) :
    ∃ s digits, j = .str s ∧ hexDigits what (.str s) = .ok digits ∧
      digits.data.toList.length = 2 * b.data.toList.length ∧
      ∀ (i : Nat) (hi : i < b.data.toList.length),
        digits.data.toList[2 * i]?.bind (hexValue upper) =
            some (highDigit b.data.toList[i]).val.toUInt8 ∧
          digits.data.toList[2 * i + 1]?.bind (hexValue upper) =
            some (lowDigit b.data.toList[i]).val.toUInt8 := by
  unfold bytesOf at h
  cases j with
  | str s =>
    obtain ⟨digits, hd, h⟩ := bind_ok_iff.mp h
    dsimp only at h
    split at h
    · cases h
    rename_i heven
    obtain ⟨res, hloop, hres⟩ := bind_ok_iff.mp h
    have hb : res = b := by cases hres; rfl
    subst hb
    have hr : List.range' [:digits.size / 2].start [:digits.size / 2].size
        [:digits.size / 2].step = List.range' 0 (digits.size / 2) 1 := by
      rw [show [:digits.size / 2].size = digits.size / 2 by simp [Std.Legacy.Range.size]]
    rw [Std.Legacy.Range.forIn_eq_forIn_range', hr] at hloop
    -- Each step reads two digit codes and pushes the byte that they write.
    obtain ⟨xs, hlen, hxs, hq⟩ := forIn_range'_ok
      (Q := fun i x => ∃ c d, digits[2 * i]? = some c ∧ digits[2 * i + 1]? = some d ∧
        hexValue upper c = some (highDigit x).val.toUInt8 ∧
        hexValue upper d = some (lowDigit x).val.toUInt8)
      (fun i out r hr' => by
        split at hr'
        · rename_i c d hc hd'
          split at hr'
          · rename_i high low hh hl
            simp only [pure, Except.pure, Except.ok.injEq] at hr'
            obtain ⟨eh, el⟩ := highDigit_lowDigit (hexValue_lt hh).2 (hexValue_lt hl).2
            exact ⟨_, hr'.symm, c, d, hc, hd', by rw [hh, eh], by rw [hl, el]⟩
          · simp [bind, Except.bind] at hr'
        · simp [bind, Except.bind] at hr')
      hloop
    have hres' : res.data.toList = xs := by
      rw [hxs]; simp [ByteArray.emptyWithCapacity] <;> rfl
    refine ⟨s, digits, rfl, hd, ?_, fun i hi => ?_⟩
    · have : digits.data.toList.length = digits.size := Array.length_toList
      rw [hres']
      omega
    · obtain ⟨c, d, hc, hd2, hcs, hds⟩ := hq i (by rw [← hres']; exact hi)
      simp only [Nat.zero_add] at hc hd2
      rw [getElem?_eq_data_toList] at hc hd2
      rw [hc, hd2, List.getElem_of_eq hres' hi]
      exact ⟨hcs, hds⟩
  | _ =>
    obtain ⟨digits, hd, -⟩ := bind_ok_iff.mp h
    simp [hexDigits] at hd

/-- A code that the decoder reads as a lowercase hex digit of a value is the code of that digit. -/
private theorem eq_of_hexValue_false {c : UInt8} {n : Fin 16}
    (h : hexValue false c = some n.val.toUInt8) : c = (hexDigitChar n).val.toUInt8 := by
  obtain ⟨code, -⟩ := hexDigitChar_hexValue c (by simp [h])
  have digit : (⟨digitValue c % 16, Nat.mod_lt _ (by decide)⟩ : Fin 16) = n := by
    apply Fin.ext
    simp only [digitValue, h, Option.getD_some, Nat.toUInt8_eq, UInt8.toNat_ofNat']
    omega
  rw [digit] at code
  exact code.symm

/-- The byte decoder without uppercase digits returns bytes exactly when the text encodes them.

That encoding is `0x` and two lowercase hex digits for each byte, high digit first.

So uppercase digits, an odd number of digits, a missing `0x` and any other text are rejected. -/
theorem bytesOf_false_eq_ok_iff {what : String} {j : Lean.Json} {b : ByteArray} :
    bytesOf what false j = .ok b ↔ j = .str (hexString b.data.toList) := by
  constructor
  · intro h
    obtain ⟨s, digits, rfl, hd, hdl, hidx⟩ := bytesOf_eq_ok_digits h
    generalize b.data.toList = xs at hdl hidx ⊢
    -- The digit codes are the hex encoding of the bytes, two digits per byte.
    have hdig : digits.data.toList = (xs.flatMap byteHexDigits).map fun c => c.val.toUInt8 := by
      apply List.ext_getElem?
      intro k
      obtain ⟨j, hk⟩ : ∃ j, k = 2 * j ∨ k = 2 * j + 1 := ⟨k / 2, by omega⟩
      obtain ⟨e1, e2⟩ := flatMap_byteHexDigits_getElem? xs j
      by_cases hj : j < xs.length
      · obtain ⟨h0, h1⟩ := hidx j hj
        rw [List.getElem?_eq_getElem hj, Option.map_some] at e1 e2
        rcases hk with rfl | rfl
        · obtain ⟨c, hc, hv⟩ := Option.bind_eq_some_iff.mp h0
          rw [hc, List.getElem?_map, e1, Option.map_some, eq_of_hexValue_false hv]
        · obtain ⟨d, hd2, hv⟩ := Option.bind_eq_some_iff.mp h1
          rw [hd2, List.getElem?_map, e2, Option.map_some, eq_of_hexValue_false hv]
      · -- Past the last byte, neither list has an entry.
        rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by
          rw [List.length_map, length_flatMap_byteHexDigits]; omega)]
    -- So the text has the bytes of the hex encoding, and is that encoding.
    have ht := toUTF8_of_hexDigits (hexDigits_hexString what xs)
    have hs := toUTF8_of_hexDigits hd
    rw [List.data_toByteArray, ← hdig, ← hs] at ht
    congr 1
    apply String.toByteArray_inj.mp
    rw [← String.toUTF8_eq_toByteArray, ← String.toUTF8_eq_toByteArray]
    exact ByteArray.ext (Array.ext' ht.symm)
  · rintro rfl
    rw [bytesOf_hexString]
    congr 1
    apply ByteArray.ext
    simp

/-- A byte string decodes exactly when the text is `0x` and two lowercase hex digits per byte. -/
theorem bytes_eq_ok_iff {what : String} {j : Lean.Json} {b : ByteArray} :
    bytes what j = .ok b ↔ j = .str (hexString b.data.toList) :=
  bytesOf_false_eq_ok_iff

/-- A byte string of a fixed size, without uppercase digits, decodes exactly from its encoding.

It applies to the hashes, roots and the logs bloom, which take lowercase digits only. -/
theorem fixed_false_eq_ok_iff {what : String} {n : Nat} {j : Lean.Json} {v : Vector UInt8 n} :
    fixed what n j false = .ok v ↔ j = .str (hexString v.toList) := by
  rw [fixed_eq_ok_iff, bytesOf_false_eq_ok_iff]
  exact Iff.rfl

/-! ## Uppercase digits -/

/-- The fact below, checked by the kernel on each of the 128 ASCII codes and the 16 digits. -/
private theorem toLower_ofNat_lt : ∀ m, m < 128 → (Char.ofNat m).val.toUInt8 = m.toUInt8 ∧
    ∀ n : Fin 16, ((Char.ofNat m).toLower = hexDigitChar n ↔
      hexValue true m.toUInt8 = some n.val.toUInt8) := by
  decide +kernel

/-- A character whose lowercase form is a hex digit is ASCII, and the decoder reads its value. -/
private theorem hexValue_of_toLower {c : Char} {n : Fin 16} (h : c.toLower = hexDigitChar n) :
    c.val ≤ 0x7F ∧ hexValue true c.val.toUInt8 = some n.val.toUInt8 := by
  by_cases hc : c.val ≤ 0x7F
  · have hm : c.toNat < 128 := by
      have := UInt32.le_iff_toNat_le.mp hc
      simp at this
      omega
    have := ((toLower_ofNat_lt c.toNat hm).2 n).mp (by rw [Char.ofNat_toNat]; exact h)
    exact ⟨hc, this⟩
  · -- Above ASCII, the lowercase form is the character itself, which is not a hex digit.
    exfalso
    have hz : ¬ (c.val ≥ 'A'.val ∧ c.val ≤ 'Z'.val) := by
      intro hz
      apply hc
      have := UInt32.le_iff_toNat_le.mp hz.2
      apply UInt32.le_iff_toNat_le.mpr
      simp at this ⊢
      omega
    have hl : c.toLower = c := by
      unfold Char.toLower
      exact dite_eq_right_of_eq_false (eq_false hz)
    have := hexDigitChar_ascii n
    rw [← h, hl] at this
    exact hc this

/-- A code that the decoder reads as a hex digit, in either case, lowercases to that digit. -/
private theorem toLower_ofNat_of_hexValue {c : UInt8} {n : Fin 16}
    (h : hexValue true c = some n.val.toUInt8) :
    (Char.ofNat c.toNat).toLower = hexDigitChar n ∧ (Char.ofNat c.toNat).val.toUInt8 = c := by
  have hm := toLower_ofNat_lt c.toNat (hexValue_lt h).1
  simp only [show c.toNat.toUInt8 = c from UInt8.ofNat_toNat] at hm
  exact ⟨(hm.2 n).mpr h, hm.1⟩

/-- The byte decoder with uppercase digits returns bytes exactly when the text encodes them.

That text is `0x` and two hex digits for each byte, high digit first, each digit in either case.

So the digits in lowercase are the hex encoding of the bytes.

The marker must still be `0x` with a lowercase `x`. -/
theorem bytesOf_true_eq_ok_iff {what : String} {j : Lean.Json} {b : ByteArray} :
    bytesOf what true j = .ok b ↔ ∃ ds : List Char,
      j = .str ("0x" ++ String.ofList ds) ∧
        ds.map Char.toLower = b.data.toList.flatMap byteHexDigits := by
  constructor
  · intro h
    obtain ⟨s, digits, rfl, hd, hdl, hidx⟩ := bytesOf_eq_ok_digits h
    generalize b.data.toList = xs at hdl hidx ⊢
    -- Each digit code is the code of an ASCII character, whose lowercase form the encoding writes.
    have hpos : ∀ k : Nat,
        ((digits.data.toList.map fun c => Char.ofNat c.toNat).map Char.toLower)[k]? =
          (xs.flatMap byteHexDigits)[k]? ∧
        ((digits.data.toList.map fun c => Char.ofNat c.toNat).map fun c => c.val.toUInt8)[k]? =
          digits.data.toList[k]? := by
      intro k
      simp only [List.map_map, List.getElem?_map]
      obtain ⟨j, hk⟩ : ∃ j, k = 2 * j ∨ k = 2 * j + 1 := ⟨k / 2, by omega⟩
      obtain ⟨e1, e2⟩ := flatMap_byteHexDigits_getElem? xs j
      by_cases hj : j < xs.length
      · obtain ⟨h0, h1⟩ := hidx j hj
        rw [List.getElem?_eq_getElem hj, Option.map_some] at e1 e2
        rcases hk with rfl | rfl
        · obtain ⟨c, hc, hv⟩ := Option.bind_eq_some_iff.mp h0
          obtain ⟨el, ec⟩ := toLower_ofNat_of_hexValue hv
          rw [hc, e1]
          exact ⟨congrArg some el, congrArg some ec⟩
        · obtain ⟨d, hd2, hv⟩ := Option.bind_eq_some_iff.mp h1
          obtain ⟨el, ec⟩ := toLower_ofNat_of_hexValue hv
          rw [hd2, e2]
          exact ⟨congrArg some el, congrArg some ec⟩
      · -- Past the last byte, no list has an entry.
        rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by
          rw [length_flatMap_byteHexDigits]; omega)]
        exact ⟨rfl, rfl⟩
    generalize hds : digits.data.toList.map (fun c => Char.ofNat c.toNat) = ds at hpos
    have hlower : ds.map Char.toLower = xs.flatMap byteHexDigits :=
      List.ext_getElem? fun k => (hpos k).1
    have hcodes : ds.map (fun c => c.val.toUInt8) = digits.data.toList :=
      List.ext_getElem? fun k => (hpos k).2
    refine ⟨ds, ?_, hlower⟩
    -- The characters are ASCII, so the text has the bytes `0x` and the digit codes.
    have hascii : ∀ c ∈ ds, c.val ≤ 0x7F := by
      intro c hc
      have hm : c.toLower ∈ xs.flatMap byteHexDigits := hlower ▸ List.mem_map_of_mem hc
      simp only [List.mem_flatMap, byteHexDigits, List.mem_cons, List.not_mem_nil,
        or_false] at hm
      obtain ⟨x, -, hx | hx⟩ := hm
      · exact (hexValue_of_toLower hx).1
      · exact (hexValue_of_toLower hx).1
    have ht := toUTF8_of_hexDigits (hexDigits_ascii what ds hascii)
    have hs := toUTF8_of_hexDigits hd
    rw [List.data_toByteArray, hcodes, ← hs] at ht
    congr 1
    apply String.toByteArray_inj.mp
    rw [← String.toUTF8_eq_toByteArray, ← String.toUTF8_eq_toByteArray]
    exact ByteArray.ext (Array.ext' ht.symm)
  · rintro ⟨ds, rfl, hlower⟩
    have hascii : ∀ c ∈ ds, c.val ≤ 0x7F := by
      intro c hc
      have hm : c.toLower ∈ b.data.toList.flatMap byteHexDigits :=
        hlower ▸ List.mem_map_of_mem hc
      simp only [List.mem_flatMap, byteHexDigits, List.mem_cons, List.not_mem_nil,
        or_false] at hm
      obtain ⟨x, -, hx | hx⟩ := hm
      · exact (hexValue_of_toLower hx).1
      · exact (hexValue_of_toLower hx).1
    have hlen : ds.length = 2 * b.data.toList.length := by
      rw [← length_flatMap_byteHexDigits, ← hlower, List.length_map]
    have hb := bytesOf_of_hexDigits (upper := true) (data := b.data.toList)
      (hexDigits_ascii what ds hascii) (by rw [List.length_map, hlen]) fun i hi => by
        obtain ⟨e1, e2⟩ := flatMap_byteHexDigits_getElem? b.data.toList i
        rw [List.getElem?_eq_getElem hi, Option.map_some, ← hlower, List.getElem?_map] at e1 e2
        obtain ⟨c, hc, hcl⟩ := Option.map_eq_some_iff.mp e1
        obtain ⟨d, hd, hdl⟩ := Option.map_eq_some_iff.mp e2
        rw [List.getElem?_map, List.getElem?_map, hc, hd]
        exact ⟨(hexValue_of_toLower hcl).2, (hexValue_of_toLower hdl).2⟩
    rw [hb]
    congr 1
    apply ByteArray.ext
    simp

/-- An address decodes exactly when its text encodes its bytes, with digits in either case.

That text is `0x` and two hex digits for each of the 20 bytes, whose lowercase forms encode them. -/
theorem address_eq_ok_iff_map_toLower {what : String} {j : Lean.Json} {a : Address} :
    address what j = .ok a ↔ ∃ ds : List Char,
      j = .str ("0x" ++ String.ofList ds) ∧
        ds.map Char.toLower = a.toList.flatMap byteHexDigits := by
  rw [address_eq_ok_iff, bytesOf_true_eq_ok_iff]
  exact Iff.rfl

/-! ## The encoders

The decoder of numbers takes only the text that the encoder writes, at any bound above the number.

So two numbers never share a text, however large they are.

A list decodes from its encoding exactly as its items decode from theirs, in order.

An object built from pairs with distinct names holds those pairs, and reads each by its name.
-/

/-- Two numbers have the same encoding only when they are equal. -/
theorem quantityJson_inj {m n : Nat} : quantityJson m = quantityJson n ↔ m = n := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  -- Both numbers are below one bound, and the decoder reads each back from the shared text.
  have hm : m < 2 ^ (m + n) := Nat.lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right
    (by decide) (Nat.le_add_right m n))
  have hn : n < 2 ^ (m + n) := Nat.lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right
    (by decide) (Nat.le_add_left n m))
  have h1 := quantity_eq_ok_iff (what := "") (j := quantityJson m) |>.mpr ⟨hm, rfl⟩
  rw [(quantity_eq_ok_iff (what := "")).mpr ⟨hn, h⟩] at h1
  exact (Except.ok.inj h1).symm

/-- A list decodes from its encoding exactly as its items decode from theirs, in order. -/
theorem array_listJson {α β : Type} (what : String) (f : Lean.Json → Read α) (g : β → Lean.Json)
    (items : List β) :
    array what f (listJson g items) = items.mapM fun x => f (g x) := by
  simp only [array, listJson, Array.toList_map]
  induction items with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.mapM_cons, ih]

open Std in
/-- An object built from pairs with distinct names holds exactly those pairs, no two of one name. -/
theorem toList_mkObj {pairs : List (String × Lean.Json)}
    (distinct : pairs.Pairwise fun a b => a.1 ≠ b.1) :
    ∃ kvs, Lean.Json.mkObj pairs = .obj kvs ∧ kvs.toList.length = pairs.length ∧
      (∀ p, p ∈ kvs.toList ↔ p ∈ pairs) ∧ kvs.toList.Pairwise fun a b => a.1 ≠ b.1 := by
  have keys : pairs.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) :=
    distinct.imp fun different equal => different (compare_eq_iff_eq.mp equal)
  have wf : (Std.TreeMap.Raw.ofList pairs (cmp := compare)).WF := Std.TreeMap.Raw.WF.ofList
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [Std.TreeMap.Raw.length_toList wf, Std.TreeMap.Raw.size_ofList keys]
  · rintro ⟨k, v⟩
    rw [Std.TreeMap.Raw.mem_toList_iff_getElem?_eq_some wf]
    refine ⟨fun h => ?_, fun hm => Std.TreeMap.Raw.getElem?_ofList_of_mem compare_self keys hm⟩
    -- A name that no pair carries reads as absent, so the name is that of a pair.
    by_cases hk : (pairs.map Prod.fst).contains k = true
    · obtain ⟨v', hm⟩ : ∃ v', (k, v') ∈ pairs := by simpa using hk
      rw [Std.TreeMap.Raw.getElem?_ofList_of_mem compare_self keys hm] at h
      cases h
      exact hm
    · rw [Std.TreeMap.Raw.getElem?_ofList_of_contains_eq_false (by simpa using hk)] at h
      cases h
  · exact (Std.TreeMap.Raw.distinct_keys_toList wf).imp fun h e => h (compare_eq_iff_eq.mpr e)

/-- A pair of a list with distinct names is what the list holds under its name. -/
theorem lookup_of_mem {fs : List (String × Lean.Json)} {k : String} {v : Lean.Json}
    (distinct : fs.Pairwise fun a b => a.1 ≠ b.1) (h : (k, v) ∈ fs) : fs.lookup k = some v := by
  induction fs with
  | nil => cases h
  | cons p fs ih =>
    obtain ⟨hp, hrest⟩ := List.pairwise_cons.mp distinct
    obtain ⟨k', v'⟩ := p
    rcases List.mem_cons.mp h with h | hm
    · cases h
      simp [List.lookup]
    · -- The name of the first pair is another name, so the lookup reads on.
      have hne : k' ≠ k := hp _ hm
      have hb : (k == k') = false := by simpa using Ne.symm hne
      simp only [List.lookup, hb]
      exact ih hrest hm

/-- An object built from pairs with distinct names, none of them `null`, has those pairs as fields.

They may come in another order. -/
theorem fields_mkObj (what : String) {pairs : List (String × Lean.Json)}
    (distinct : pairs.Pairwise fun a b => a.1 ≠ b.1) (present : ∀ p ∈ pairs, p.2.isNull = false) :
    ∃ fs, fields what (Lean.Json.mkObj pairs) = .ok fs ∧ fs.Perm pairs := by
  obtain ⟨kvs, hobj, -, hmem, hd⟩ := toList_mkObj distinct
  have hkeep : kvs.toList.filter (fun (_, v) => !v.isNull) = kvs.toList := by
    rw [List.filter_eq_self]
    intro p hp
    simp [present p ((hmem p).mp hp)]
  refine ⟨kvs.toList, ?_, ?_⟩
  · rw [hobj]
    simp only [fields, hkeep]
    rfl
  · -- Distinct names make both lists free of repeats, so equal members give a permutation.
    have nodup : ∀ l : List (String × Lean.Json), (l.Pairwise fun a b => a.1 ≠ b.1) → l.Nodup :=
      fun l h => h.imp_of_mem (fun {a b} _ _ hne heq => hne (by rw [heq]))
    exact (List.perm_ext_iff_of_nodup (nodup _ hd) (nodup _ distinct)).mpr hmem

/-- An object built from pairs with distinct names has the pairs that are not `null` as fields.

They may come in another order. -/
theorem fields_mkObj_filter (what : String) {pairs : List (String × Lean.Json)}
    (distinct : pairs.Pairwise fun a b => a.1 ≠ b.1) :
    ∃ fs, fields what (Lean.Json.mkObj pairs) = .ok fs ∧
      fs.Perm (pairs.filter fun p => !p.2.isNull) := by
  obtain ⟨kvs, hobj, -, hmem, hd⟩ := toList_mkObj distinct
  refine ⟨kvs.toList.filter (fun (_, v) => !v.isNull), ?_, ?_⟩
  · rw [hobj]
    rfl
  · have nodup : ∀ l : List (String × Lean.Json), (l.Pairwise fun a b => a.1 ≠ b.1) → l.Nodup :=
      fun l h => h.imp_of_mem (fun {a b} _ _ hne heq => hne (by rw [heq]))
    refine (List.perm_ext_iff_of_nodup ((nodup _ hd).filter _)
      ((nodup _ distinct).filter _)).mpr fun p => ?_
    simp only [List.mem_filter, hmem]

/-- Fields that are some pairs in another order hold exactly the names of those pairs. -/
theorem hasExactly_of_perm {fs pairs : List (String × Lean.Json)} (h : fs.Perm pairs) :
    hasExactly fs (pairs.map Prod.fst) = true := by
  simp only [hasExactly, List.length_map, h.length_eq, beq_self_eq_true, Bool.true_and,
    List.all_eq_true, List.any_eq_true, List.mem_map]
  rintro name ⟨p, hp, rfl⟩
  exact ⟨p, h.mem_iff.mpr hp, by simp⟩

/-- Fields that are pairs with distinct names, in another order, read each pair by its name. -/
theorem field_of_perm {what k : String} {v : Lean.Json} {fs pairs : List (String × Lean.Json)}
    (h : fs.Perm pairs) (distinct : pairs.Pairwise fun a b => a.1 ≠ b.1) (hm : (k, v) ∈ pairs) :
    field what fs k = .ok v := by
  have hd : fs.Pairwise fun a b => a.1 ≠ b.1 :=
    (h.pairwise_iff fun hab => Ne.symm hab).mpr distinct
  simp only [field, lookup_of_mem hd (h.mem_iff.mpr hm)]
  rfl

/-- The JSON of a string is not `null`. -/
theorem isNull_str (s : String) : (Lean.Json.str s).isNull = false := by rfl

/-- The JSON of an array is not `null`. -/
theorem isNull_arr (a : Array Lean.Json) : (Lean.Json.arr a).isNull = false := by rfl

/-- The decoder of byte strings of a size reads back a vector written as data. -/
theorem fixed_dataJson {n : Nat} (what : String) (v : Vector UInt8 n) (upper : Bool) :
    fixed what n (dataJson v.toList) upper = .ok v :=
  fixed_hexString what n v upper

/-- The decoder of addresses reads back an address written as data. -/
theorem address_dataJson (what : String) (v : Vector UInt8 20) :
    address what (dataJson v.toList) = .ok v :=
  fixed_dataJson what v true

/-- Fields that are some pairs in another order, with distinct names, read a name as those do. -/
theorem lookup_of_perm {fs pairs : List (String × Lean.Json)} (h : fs.Perm pairs)
    (distinct : pairs.Pairwise fun a b => a.1 ≠ b.1) (k : String) :
    fs.lookup k = pairs.lookup k := by
  cases hl : pairs.lookup k with
  | none =>
    rw [List.lookup_eq_none_iff] at hl ⊢
    exact fun p hp => hl p (h.mem_iff.mp hp)
  | some v =>
    obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.mp hl
    exact lookup_of_mem ((h.pairwise_iff fun hab => Ne.symm hab).mpr distinct)
      (h.mem_iff.mpr (by simp))

/-- Fields that hold the pairs not `null` of a list with distinct names read each name as the list.

A name whose value is `null` reads as absent. -/
theorem lookup_of_perm_filter {fs pairs : List (String × Lean.Json)}
    (h : fs.Perm (pairs.filter fun p => !p.2.isNull))
    (distinct : pairs.Pairwise fun a b => a.1 ≠ b.1) (k : String) :
    fs.lookup k = (pairs.lookup k).filter fun v => !v.isNull := by
  have hdf : (pairs.filter fun p => !p.2.isNull).Pairwise fun a b => a.1 ≠ b.1 :=
    List.Pairwise.sublist List.filter_sublist distinct
  have hd : fs.Pairwise fun a b => a.1 ≠ b.1 := (h.pairwise_iff fun hab => Ne.symm hab).mpr hdf
  cases hl : pairs.lookup k with
  | none =>
    rw [List.lookup_eq_none_iff] at hl
    rw [Option.filter_none, List.lookup_eq_none_iff]
    intro p hp
    exact hl p (List.mem_filter.mp (h.mem_iff.mp hp)).1
  | some v =>
    have hv : (k, v) ∈ pairs := by
      obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.mp hl
      simp
    by_cases hn : v.isNull = true
    · simp only [Option.filter_some, hn, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [List.lookup_eq_none_iff]
      intro p hp
      obtain ⟨hp, hpn⟩ := List.mem_filter.mp (h.mem_iff.mp hp)
      by_cases hk : p.1 = k
      · have := lookup_of_mem distinct hp
        rw [hk, hl] at this
        cases this
        simp_all
      · simpa using Ne.symm hk
    · simp only [Option.filter_some, hn, Bool.not_false, ↓reduceIte]
      exact lookup_of_mem hd (h.mem_iff.mpr (List.mem_filter.mpr ⟨hv, by simpa using hn⟩))

/-- A list reads back from its encoding when each item reads back from its own. -/
theorem array_listJson_of {α : Type} (what : String) {f : Lean.Json → Read α}
    {g : α → Lean.Json} (h : ∀ x, f (g x) = .ok x) (items : List α) :
    array what f (listJson g items) = .ok items := by
  rw [array_listJson]
  simp only [h]
  induction items with
  | nil => rfl
  | cons x xs ih => simp only [List.mapM_cons, ih]; rfl

/-- The decoder of byte strings reads back a byte string that holds its bytes as data. -/
theorem bytes_dataJson (what : String) (b : ByteArray) :
    bytes what (dataJson b.data.toList) = .ok b := by
  rw [dataJson, bytes_hexString]
  congr 1
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

/-- The decoder of lists of byte strings reads back a list written as data. -/
theorem array_bytes_listJson (what w : String) (l : List ByteArray) :
    array what (bytes w) (listJson (dataJson ·.data.toList) l) = .ok l :=
  array_listJson_of what (bytes_dataJson w) l

/-- The decoder of lists of byte strings of a size reads back a list written as data. -/
theorem array_fixed_listJson {n : Nat} (what w : String) (l : List (Vector UInt8 n)) :
    array what (fixed w n) (listJson (dataJson ·.toList) l) = .ok l :=
  array_listJson_of what (fun v => fixed_dataJson w v false) l

/-- A value or `null` reads back from its encoding, when no value is written as `null`. -/
theorem nullable_optionJson {α : Type} {f : Lean.Json → Read α} {g : α → Lean.Json}
    (h : ∀ x, f (g x) = .ok x) (present : ∀ x, (g x).isNull = false) (o : Option α) :
    nullable f (optionJson g o) = .ok o := by
  cases o with
  | none => rfl
  | some x =>
    have hx := present x
    have hn : nullable f (g x) = some <$> f (g x) := by
      cases hg : g x with
      | null => rw [hg] at hx; cases hx
      | _ => rfl
    simp only [optionJson, hn, h]
    rfl

/-- Fields that are some pairs in another order hold only the names of those pairs. -/
theorem hasOnly_of_perm {fs pairs : List (String × Lean.Json)} {names : List String}
    (h : fs.Perm pairs) (hn : ∀ p ∈ pairs, p.1 ∈ names) : hasOnly fs names = true := by
  simp only [hasOnly, List.all_eq_true]
  intro p hp
  simpa using hn p (h.mem_iff.mp hp)

/-! ## The error object -/

/-- The integer reader reads back the number that an integer writes. -/
theorem integer_fromInt (what : String) (c : Int) :
    integer what (.num (.fromInt c)) = .ok c := by
  simp [integer, Lean.JsonNumber.fromInt]
  rfl

/-- The reader of error objects reads back the error object that the writer writes for any error.

That holds for data of any value, the JSON `null` among them. -/
theorem rpcErrorOfJson_json (e : RpcError) : rpcErrorOfJson (rpcErrorJson e) = .ok e := by
  obtain ⟨c, m, d⟩ := e
  cases d with
  | none =>
    obtain ⟨kvs, hobj, -, hmem, hd⟩ := toList_mkObj (pairs :=
      [("code", .num (.fromInt c)), ("message", .str m)]) (by simp)
    have hc := lookup_of_mem hd ((hmem _).mpr (by simp : ("code", Lean.Json.num (.fromInt c)) ∈
      [("code", Lean.Json.num (.fromInt c)), ("message", Lean.Json.str m)]))
    have hm := lookup_of_mem hd ((hmem _).mpr (by simp : ("message", Lean.Json.str m) ∈
      [("code", Lean.Json.num (.fromInt c)), ("message", Lean.Json.str m)]))
    have hdata : kvs.toList.lookup "data" = none := by
      rw [List.lookup_eq_none_iff]
      intro p hp
      have := (hmem p).mp hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl <;> simp
    have hall : (kvs.toList.all fun (name, _) =>
        name == "code" || name == "message" || name == "data") = true := by
      rw [List.all_eq_true]
      intro p hp
      have := (hmem p).mp hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl <;> simp
    have hobj' : rpcErrorJson ⟨c, m, none⟩ = .obj kvs := hobj
    rw [hobj']
    simp only [rpcErrorOfJson, hall, field, hc, hm, hdata, ite_true, pure_bind, integer_fromInt]
    rfl
  | some v =>
    obtain ⟨kvs, hobj, -, hmem, hd⟩ := toList_mkObj (pairs :=
      [("code", .num (.fromInt c)), ("message", .str m), ("data", v)]) (by simp)
    have hc := lookup_of_mem hd ((hmem _).mpr (by simp : ("code", Lean.Json.num (.fromInt c)) ∈
      [("code", Lean.Json.num (.fromInt c)), ("message", Lean.Json.str m), ("data", v)]))
    have hm := lookup_of_mem hd ((hmem _).mpr (by simp : ("message", Lean.Json.str m) ∈
      [("code", Lean.Json.num (.fromInt c)), ("message", Lean.Json.str m), ("data", v)]))
    have hdata := lookup_of_mem hd ((hmem _).mpr (by simp : ("data", v) ∈
      [("code", Lean.Json.num (.fromInt c)), ("message", Lean.Json.str m), ("data", v)]))
    have hall : (kvs.toList.all fun (name, _) =>
        name == "code" || name == "message" || name == "data") = true := by
      rw [List.all_eq_true]
      intro p hp
      have := (hmem p).mp hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl | rfl <;> simp
    have hobj' : rpcErrorJson ⟨c, m, some v⟩ = .obj kvs := hobj
    rw [hobj']
    simp only [rpcErrorOfJson, hall, field, hc, hm, hdata, ite_true, pure_bind, integer_fromInt]
    rfl

/-- A JSON value reads as an integer exactly when it is a number that equals an integer.

A JSON number in Lean is a mantissa `m` over `10` to the power of an exponent `e`.

It reads as `m / 10 ^ e` when `10 ^ e` divides `m`. -/
theorem integer_eq_ok_iff {what : String} {j : Lean.Json} {i : Int} :
    integer what j = .ok i ↔ ∃ m e, j = .num ⟨m, e⟩ ∧ m % 10 ^ e = 0 ∧ i = m / 10 ^ e := by
  cases j with
  | num n =>
    obtain ⟨m, e⟩ := n
    constructor
    · intro hi
      by_cases h : m % 10 ^ e = 0
      · simp only [integer, h, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hi
        exact ⟨m, e, rfl, h, hi.symm⟩
      · simp [integer, h, reject, throw, throwThe, MonadExceptOf.throw] at hi
    · rintro ⟨m', e', heq, h, rfl⟩
      simp only [Lean.Json.num.injEq, Lean.JsonNumber.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp [integer, h, pure, Except.pure]
  | _ => simp [integer, reject, throw, throwThe, MonadExceptOf.throw]

/-- A JSON value reads as an error object exactly when it is an object with no unknown member.

The known members are `code`, `message` and `data`.

The code is the integer under `code`, and the message the string under `message`.

The data is the value under `data`, `null` included, or none when it is missing. -/
theorem rpcErrorOfJson_eq_ok_iff {j : Lean.Json} {e : RpcError} :
    rpcErrorOfJson j = .ok e ↔ ∃ kvs, j = .obj kvs ∧
      (∀ member ∈ kvs.toList, member.1 = "code" ∨ member.1 = "message" ∨
        member.1 = "data") ∧
      (∃ c, kvs.toList.lookup "code" = some c ∧ integer "code" c = .ok e.code) ∧
      kvs.toList.lookup "message" = some (.str e.message) ∧
      kvs.toList.lookup "data" = e.data := by
  obtain ⟨code, message, data⟩ := e
  cases j with
  | obj kvs =>
    have allIff : (kvs.toList.all fun (name, _) =>
        name == "code" || name == "message" || name == "data") = true ↔
        ∀ member ∈ kvs.toList, member.1 = "code" ∨ member.1 = "message" ∨
          member.1 = "data" := by
      simp [List.all_eq_true, or_assoc]
    simp only [rpcErrorOfJson, Lean.Json.obj.injEq, exists_eq_left']
    by_cases hall : (kvs.toList.all fun (name, _) =>
        name == "code" || name == "message" || name == "data") = true
    · rw [and_iff_right (allIff.mp hall)]
      cases hc : kvs.toList.lookup "code" with
      | none =>
        simp [hall, hc, field, reject, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
      | some cj =>
        cases hi : integer "code" cj with
        | error _ => simp [hall, hc, hi, field, bind, Except.bind, pure, Except.pure]
        | ok c =>
          cases hm : kvs.toList.lookup "message" with
          | none =>
            simp [hall, hc, hi, hm, field, reject, throw, throwThe, MonadExceptOf.throw, bind,
              Except.bind, pure, Except.pure]
          | some mj =>
            cases mj <;> simp [hall, hc, hi, hm, field, string, reject, throw, throwThe,
              MonadExceptOf.throw, bind, Except.bind, pure, Except.pure]
    · constructor
      · intro h
        simp [hall, reject, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
      · rintro ⟨members, -⟩
        exact absurd (allIff.mpr members) hall
  | _ => simp [rpcErrorOfJson, reject, throw, throwThe, MonadExceptOf.throw]

end EthLib.Serialization.JsonRpc
