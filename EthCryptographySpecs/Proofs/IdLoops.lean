import Mathlib.Data.List.Basic
import Mathlib.Tactic.NormNum

/-!
# Proofs: `Id.run do` loops as folds

Conversion lemmas turning `for x in [:n]` loops of the executable
spec's `Id.run do` blocks into `List.foldl` over `List.range' 0 n`,
where ordinary induction applies. The `_ite` variants accommodate
bodies whose branches both yield (the `ite`'s type ascription inside a
`forIn` body differs from a bare one, so the plain lemma cannot match
them). `id_pure`/`id_bind` are `rfl`-lemmas for `dsimp`-normalizing
the monadic plumbing away.
-/

namespace EthCryptographySpecs.IdLoops

theorem id_pure {α : Type} (a : α) : (pure a : Id α) = a := rfl

theorem id_bind {α β : Type} (a : Id α) (f : α → Id β) :
    (a >>= f) = f a := rfl

theorem forIn_list_yield {α β : Type} (l : List α) (init : β)
    (f : α → β → β) :
    (forIn (m := Id) l init (fun a acc => ForInStep.yield (f a acc)))
      = l.foldl (fun acc a => f a acc) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    rw [List.forIn_cons, List.foldl_cons]
    exact ih (f a init)

theorem forIn_range_yield {β : Type} (n : Nat) (init : β)
    (f : Nat → β → β) :
    (forIn (m := Id) [:n] init (fun j acc => ForInStep.yield (f j acc)))
      = (List.range' 0 n).foldl (fun acc j => f j acc) init := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  show (forIn (m := Id) (List.range' 0 ([:n].size) 1) init _) = _
  rw [forIn_list_yield]
  norm_num [Std.Legacy.Range.size]

theorem forIn_range_yield_ite {β : Type} (n : Nat) (init : β)
    (c : Nat → β → Prop) [inst : ∀ j acc, Decidable (c j acc)]
    (f g : Nat → β → β) :
    (forIn (m := Id) [:n] init (fun j acc =>
        if c j acc then ForInStep.yield (f j acc)
        else ForInStep.yield (g j acc)))
      = (List.range' 0 n).foldl
          (fun acc j => if c j acc then f j acc else g j acc) init := by
  have hbody : (fun (j : Nat) (acc : β) =>
      (if c j acc then ForInStep.yield (f j acc)
        else ForInStep.yield (g j acc) : Id (ForInStep β)))
      = fun j acc => ForInStep.yield (if c j acc then f j acc else g j acc) := by
    funext j acc
    split <;> rfl
  rw [hbody, forIn_range_yield]

theorem forIn_range_yield_ite₂ {β : Type} (n : Nat) (init : β)
    (c₁ : Nat → β → Prop) [inst₁ : ∀ j acc, Decidable (c₁ j acc)]
    (c₂ : Nat → β → Prop) [inst₂ : ∀ j acc, Decidable (c₂ j acc)]
    (f : Nat → β → β) :
    (forIn (m := Id) [:n] init (fun j acc =>
        if c₁ j acc then
          if c₂ j acc then ForInStep.yield (f j acc)
          else ForInStep.yield acc
        else ForInStep.yield acc))
      = (List.range' 0 n).foldl
          (fun acc j => if c₁ j acc then
            if c₂ j acc then f j acc else acc
          else acc) init := by
  have hbody : (fun (j : Nat) (acc : β) =>
      (if c₁ j acc then
          if c₂ j acc then ForInStep.yield (f j acc)
          else ForInStep.yield acc
        else ForInStep.yield acc : Id (ForInStep β)))
      = fun j acc => ForInStep.yield
          (if c₁ j acc then if c₂ j acc then f j acc else acc else acc) := by
    funext j acc
    split
    · split <;> rfl
    · rfl
  rw [hbody, forIn_range_yield]

/-- An index-fold over `range' 0 arr.size` reading `arr[i]!` is a fold
over `arr.toList`. -/
theorem foldl_range'_getElem! {α β : Type} [Inhabited α] (arr : Array α)
    (f : β → α → β) (init : β) :
    (List.range' 0 arr.size).foldl (fun acc i => f acc arr[i]!) init
      = arr.toList.foldl f init := by
  suffices h : ∀ t, t ≤ arr.size →
      (List.range' 0 t).foldl (fun acc i => f acc arr[i]!) init
        = (arr.toList.take t).foldl f init by
    have := h arr.size (Nat.le_refl _)
    rwa [show arr.size = arr.toList.length by simp, List.take_length] at this
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    have htl : t < arr.toList.length := by simpa using ht
    rw [List.range'_1_concat, List.foldl_append, List.foldl_cons,
      List.foldl_nil, ih (by omega), List.take_add_one,
      List.getElem?_eq_getElem htl, Option.toList_some, List.foldl_append,
      List.foldl_cons, List.foldl_nil, Nat.zero_add,
      Array.getElem_toList,
      show arr[t] = arr[t]! from (getElem!_pos arr t (by omega)).symm]

end EthCryptographySpecs.IdLoops
