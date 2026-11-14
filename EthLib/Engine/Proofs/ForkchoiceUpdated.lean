module

public import EthLib.Engine.ForkchoiceUpdated
public import EthLib.Base.Except
public import EthLib.Engine.Proofs.Json
-- Showing that a written field is not `null` unfolds the null test of Lean's JSON.
import all Lean.Data.Json.Basic

/-!
# Proofs: the parameters, the head and the payload attributes of `engine_forkchoiceUpdated`

The update is syncing exactly when the execution layer does not hold the head.

A held head whose chain fails the terminal block check is invalid, with the zero hash.

The head then does not change.

A held head of proof of work fails that check exactly when it is not terminal.

A valid head below the known finalized block is valid, and the head does not change.

A valid update that keeps the head is exactly that case.

Any other valid update selects a valid head that the execution layer holds.

Its safe and finalized blocks are then zero, or the head or one of its known ancestors.

They are zero only while the transition block is not finalized.

The update fails in one case only.

The head is valid, and its chain passes the terminal block check.

The head is not below the known finalized block.

Its safe or its finalized block is then zero after the transition, or neither zero nor on its chain.

Otherwise such a head is valid and becomes the head.

A head that the execution layer does not hold gives a syncing update.

An invalid head names as latest valid hash the valid block of its chain nearest the head.

There is none when no block of the chain is valid.

That hash is zero when the block is of proof of work, and else a valid payload of the chain.

Each block of a chain after the first is the parent of the block before it.

The forkchoice state decodes exactly when its object holds exactly its three fields.

Each of them is a hash of 32 bytes.

The parameters decode exactly when they are a JSON array of the state and the attributes.

From version 4 custody columns may follow, and they must then decode.

The state must decode, and the attributes must be `null` or an object.

Custody columns that decode never change the answer.

Without payload attributes, every version gives the same answer.

When the update applies a valid head, attributes that fit no structure of the version give `-38003`.

When it applies none, the attributes are not read.

Attributes that fit give the answer of their checks against the head, which the tree holds.

They pass exactly when the version takes their fork and their structure is that of the fork.

Their timestamp must also be above the head's.

The attributes at that fork keep every field.

A fork that the version does not take, or no fork at all, gives `-38005`.

A version takes the forks from Paris to Glamsterdam whose attribute structure it decodes.

No version takes another fork.

A structure that is not that of the fork, or a timestamp not above the head's, gives `-38003`.

The decoders read back the state, the attributes and the parameters that the writers write.

A JSON value reads as a forkchoice response exactly when it holds a payload status and an ID.

Its members that are not `null` are these two alone.

The status is valid, invalid or syncing, and the ID 8 bytes in lowercase hex or absent.

Attributes sent with a head that the update applies come back at the fork of the next block.
-/

public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Serialization.JsonRpc (field field_eq_ok_iff fields fixed hasExactly paramsArray
  dataJson quantityJson listJson optionJson fields_mkObj hasExactly_of_perm field_of_perm
  lookup_of_mem fixed_hexString uint64 uint64_toDigits address array isNull_str isNull_arr
  fixed_dataJson address_dataJson lookup_of_perm)
open EthLib.Execution.Rpc (withdrawal withdrawalJson)
open EthLib.Engine.Json (liftM_ok exists_since_iff sinceValue_of_since)

variable {transition : TransitionConfiguration} {tree : PayloadTree} {finalized : Option Hash32}
  {state : ForkchoiceState} {config : ChainConfig}

/-- Each hash of the ancestors of a block is held by the tree. -/
theorem lookup_of_mem_ancestors {fuel : Nat} {start h : Hash32}
    (hMem : h ∈ ancestors tree fuel start) : ∃ p, tree.lookup h = some p := by
  induction fuel generalizing start with
  | zero => simp [ancestors] at hMem
  | succ fuel ih =>
    unfold ancestors at hMem
    split at hMem
    · rename_i p hp
      rcases List.mem_cons.mp hMem with rfl | hMem
      · exact ⟨p, hp⟩
      · exact ih hMem
    · simp at hMem

/-- A block that the tree holds is the first block of its chain. -/
theorem chainOf_head {h : Hash32} {p : KnownPayload} (hp : tree.lookup h = some p) :
    (chainOf tree h).head? = some h := by
  have hLen : 0 < tree.length := by
    cases tree with
    | nil => simp at hp
    | cons _ _ => simp
  obtain ⟨n, hn⟩ : ∃ n, tree.length = n + 1 := ⟨tree.length - 1, by omega⟩
  simp [chainOf, hn, ancestors, hp]

/-- The latest valid block of a chain is a valid block of that chain. -/
theorem latestValid_spec {h v : Hash32} (hv : latestValid tree h = some v) :
    v ∈ chainOf tree h ∧ (tree.lookup v).any (·.valid) = true := by
  unfold latestValid at hv
  have hValid := List.find?_some hv
  exact ⟨List.mem_of_find?_eq_some hv, hValid⟩

/-- The latest valid block of a chain is its valid block nearest the head.

Every block between the head and it is invalid. -/
theorem latestValid_eq_some_iff {h v : Hash32} :
    latestValid tree h = some v ↔
      ∃ (i : Nat) (hi : i < (chainOf tree h).length), (chainOf tree h)[i] = v ∧
        (tree.lookup v).any (·.valid) = true ∧
        ∀ (j : Nat) (hj : j < i), (tree.lookup (chainOf tree h)[j]).any (·.valid) = false := by
  unfold latestValid
  rw [List.find?_eq_some_iff_getElem]
  constructor
  · rintro ⟨hv, i, hi, rfl, hj⟩
    exact ⟨i, hi, rfl, hv, fun j hj' => by simpa using hj j hj'⟩
  · rintro ⟨i, hi, rfl, hv, hj⟩
    exact ⟨hv, i, hi, rfl, fun j hj' => by simpa using hj j hj'⟩

/-- A chain has no latest valid block exactly when none of its blocks is valid. -/
theorem latestValid_eq_none_iff {h : Hash32} :
    latestValid tree h = none ↔ ∀ x ∈ chainOf tree h, (tree.lookup x).any (·.valid) = false := by
  unfold latestValid
  simp [List.find?_eq_none]

/-- Each block of the ancestors of a block, after the first, is the parent of the one before. -/
theorem getElem?_succ_ancestors {fuel : Nat} {start b : Hash32} {i : Nat}
    (h : (ancestors tree fuel start)[i + 1]? = some b) :
    ∃ a p, (ancestors tree fuel start)[i]? = some a ∧ tree.lookup a = some p ∧
      b = p.parentHash := by
  induction fuel generalizing start i with
  | zero => simp [ancestors] at h
  | succ fuel ih =>
    cases hp : tree.lookup start with
    | none => simp [ancestors, hp] at h
    | some p =>
      simp only [ancestors, hp, List.getElem?_cons_succ] at h ⊢
      cases i with
      | zero =>
        -- The second block is the first of the ancestors of the parent, so it is the parent.
        refine ⟨start, p, rfl, hp, ?_⟩
        cases hf : fuel with
        | zero => simp [hf, ancestors] at h
        | succ fuel' =>
          rw [hf] at h
          cases hq : tree.lookup p.parentHash with
          | none => simp [ancestors, hq] at h
          | some q => simp [ancestors, hq] at h; exact h.symm
      | succ i =>
        simp only [List.getElem?_cons_succ]
        exact ih h

/-- Each block of the chain of a block, after the first, is the parent of the one before. -/
theorem getElem?_succ_chainOf {h b : Hash32} {i : Nat} (hb : (chainOf tree h)[i + 1]? = some b) :
    ∃ a p, (chainOf tree h)[i]? = some a ∧ tree.lookup a = some p ∧ b = p.parentHash :=
  getElem?_succ_ancestors hb

/-- The latest valid hash of a block is zero, or a valid payload of its chain.

So it is never the hash of a held block of proof of work, unless that hash is zero. -/
theorem latestValidHash_spec {h v : Hash32} (hv : latestValidHash tree h = some v) :
    v = ZERO_HASH ∨
      v ∈ chainOf tree h ∧ ∃ p, tree.lookup v = some p ∧ p.valid = true ∧ p.isPow = false := by
  unfold latestValidHash at hv
  cases hl : latestValid tree h with
  | none => simp [hl] at hv
  | some w =>
    simp only [hl, Option.map_some, Option.some.injEq] at hv
    obtain ⟨hmem, hvalid⟩ := latestValid_spec hl
    cases hk : tree.lookup w with
    | none => simp [hk] at hvalid
    | some p =>
      by_cases hpow : p.isPow = true
      · left
        simp only [hk, hpow, Option.any_some, ↓reduceIte] at hv
        exact hv.symm
      · right
        simp only [hk, hpow, Option.any_some, Bool.false_eq_true, ↓reduceIte] at hv
        subst hv
        exact ⟨hmem, p, hk, by simpa [hk] using hvalid, by simpa using hpow⟩

/-- The latest valid hash is that of the latest valid block, or zero for a block of proof of work.
-/
theorem latestValidHash_eq_some_iff {h v : Hash32} :
    latestValidHash tree h = some v ↔ ∃ w p, latestValid tree h = some w ∧
      tree.lookup w = some p ∧ v = if p.isPow then ZERO_HASH else w := by
  unfold latestValidHash
  cases hl : latestValid tree h with
  | none => simp
  | some w =>
    obtain ⟨-, hvalid⟩ := latestValid_spec hl
    cases hk : tree.lookup w with
    | none => simp [hk] at hvalid
    | some p =>
      simp only [Option.map_some, hk, Option.any_some, Option.some.injEq]
      constructor
      · rintro rfl
        exact ⟨w, p, rfl, hk, rfl⟩
      · rintro ⟨w', p', rfl, hp', rfl⟩
        rw [hk] at hp'
        cases hp'
        rfl

/-- The latest valid hash is zero when the latest valid block is of proof of work. -/
theorem latestValidHash_of_isPow {h v : Hash32} {p : KnownPayload}
    (hv : latestValid tree h = some v) (hp : tree.lookup v = some p) (hPow : p.isPow = true) :
    latestValidHash tree h = some ZERO_HASH := by
  simp [latestValidHash, hv, hp, hPow]

/-- On the chain of a held block of proof of work, the most recent such block is itself. -/
theorem latestPow_of_lookup {h : Hash32} {p : KnownPayload} {totals : Nat × Nat}
    (hp : tree.lookup h = some p) (hPow : p.powTotalDifficulty = some totals) :
    latestPow tree h = some totals := by
  have hc := chainOf_head (tree := tree) hp
  obtain ⟨rest, hrest⟩ : ∃ rest, chainOf tree h = h :: rest := by
    cases hch : chainOf tree h with
    | nil => simp [hch] at hc
    | cons a rest =>
      simp only [hch, List.head?_cons, Option.some.injEq] at hc
      exact ⟨rest, by rw [hc]⟩
  simp [latestPow, hrest, hp, hPow]

/-- A tree that holds two distinct blocks has at least two entries. -/
theorem two_le_length_of_lookup {a b : Hash32} {p q : KnownPayload}
    (ha : tree.lookup a = some p) (hb : tree.lookup b = some q) (hne : a ≠ b) :
    2 ≤ tree.length := by
  induction tree with
  | nil => simp at ha
  | cons e rest ih =>
    obtain ⟨k, v⟩ := e
    cases rest with
    | cons _ _ => simp
    | nil =>
      by_cases hka : a = k
      · by_cases hkb : b = k
        · exact absurd (hka.trans hkb.symm) hne
        · have hbk : (b == k) = false := by simp [hkb]
          simp [List.lookup, hbk] at hb
      · have hak : (a == k) = false := by simp [hka]
        simp [List.lookup, hak] at ha

/-- On the chain of a held payload, the latest totals of proof of work are those of its parent.

The tree must hold the parent, as a block of proof of work. -/
theorem latestPow_of_parent {h : Hash32} {p q : KnownPayload} {totals : Nat × Nat}
    (hp : tree.lookup h = some p) (hPayload : p.powTotalDifficulty = none)
    (hq : tree.lookup p.parentHash = some q) (hPow : q.powTotalDifficulty = some totals) :
    latestPow tree h = some totals := by
  have hne : h ≠ p.parentHash := by
    rintro rfl
    rw [hp] at hq
    cases hq
    simp [hPayload] at hPow
  obtain ⟨n, hn⟩ : ∃ n, tree.length = n + 2 :=
    ⟨tree.length - 2, by have := two_le_length_of_lookup hp hq hne; omega⟩
  simp [latestPow, chainOf, hn, ancestors, hp, hq, hPayload, hPow]

/-- The check on the chain of a held block of proof of work is the check of that block. -/
theorem chainPassesTerminalCheck_of_lookup {h : Hash32} {p : KnownPayload}
    {totalDifficulty parentTotalDifficulty : Nat} (hp : tree.lookup h = some p)
    (hPow : p.powTotalDifficulty = some (totalDifficulty, parentTotalDifficulty)) :
    chainPassesTerminalCheck transition tree h =
      isTerminalPowBlock transition totalDifficulty parentTotalDifficulty := by
  simp [chainPassesTerminalCheck, latestPow_of_lookup hp hPow]

/-- The update is syncing exactly when the tree does not hold the head. -/
theorem forkchoiceUpdated_syncing_iff {result : PayloadStatus × Option Hash32}
    (h : forkchoiceUpdated transition tree finalized state = .ok result) :
    result.1.status = .syncing ↔ tree.lookup state.headBlockHash = none := by
  unfold forkchoiceUpdated at h
  cases hp : tree.lookup state.headBlockHash with
  | none =>
    simp only [hp, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp
  | some p =>
    simp only [reduceCtorEq, iff_false]
    simp only [hp] at h
    repeat' split at h
    all_goals first
      | (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; simp)
      | simp [throw, throwThe, MonadExceptOf.throw] at h

/-- A held head whose chain fails the terminal block check is invalid, with the zero hash.

The head does not change. -/
theorem forkchoiceUpdated_of_not_terminal {p : KnownPayload}
    (hp : tree.lookup state.headBlockHash = some p)
    (hTerminal : chainPassesTerminalCheck transition tree state.headBlockHash = false) :
    forkchoiceUpdated transition tree finalized state =
      .ok (⟨.invalid, some ZERO_HASH⟩, none) := by
  simp [forkchoiceUpdated, hp, hTerminal, pure, Except.pure]

/-- A head of proof of work that is not terminal is invalid, with the zero hash.

The head does not change. -/
theorem forkchoiceUpdated_of_pow_not_terminal {p : KnownPayload}
    {totalDifficulty parentTotalDifficulty : Nat}
    (hp : tree.lookup state.headBlockHash = some p)
    (hPow : p.powTotalDifficulty = some (totalDifficulty, parentTotalDifficulty))
    (hTerminal : isTerminalPowBlock transition totalDifficulty parentTotalDifficulty = false) :
    forkchoiceUpdated transition tree finalized state =
      .ok (⟨.invalid, some ZERO_HASH⟩, none) := by
  exact forkchoiceUpdated_of_not_terminal hp
    (by rw [chainPassesTerminalCheck_of_lookup hp hPow, hTerminal])

/-- A held payload whose parent is a held block of proof of work that is not terminal is invalid.

Its latest valid hash is zero, and the head does not change. -/
theorem forkchoiceUpdated_of_parent_not_terminal {p q : KnownPayload}
    {totalDifficulty parentTotalDifficulty : Nat}
    (hp : tree.lookup state.headBlockHash = some p) (hPayload : p.powTotalDifficulty = none)
    (hq : tree.lookup p.parentHash = some q)
    (hPow : q.powTotalDifficulty = some (totalDifficulty, parentTotalDifficulty))
    (hTerminal : isTerminalPowBlock transition totalDifficulty parentTotalDifficulty = false) :
    forkchoiceUpdated transition tree finalized state =
      .ok (⟨.invalid, some ZERO_HASH⟩, none) :=
  forkchoiceUpdated_of_not_terminal hp
    (by simp [chainPassesTerminalCheck, latestPow_of_parent hp hPayload hq hPow, hTerminal])

/-- A valid update of a head not below the known finalized block selects that head.

The head is valid and known, and its chain passes the terminal block check.

Its safe and finalized blocks are on its chain.

A safe or finalized block of zero bytes stands for no block.

They are not zero once the transition block is finalized. -/
theorem forkchoiceUpdated_valid {result : PayloadStatus × Option Hash32}
    (h : forkchoiceUpdated transition tree finalized state = .ok result)
    (hValid : result.1.status = .valid)
    (hAbove : belowFinalized tree finalized state.headBlockHash = false) :
    (∃ p, tree.lookup state.headBlockHash = some p ∧ p.valid = true) ∧
      chainPassesTerminalCheck transition tree state.headBlockHash = true ∧
      zeroAfterTransition tree finalized state = false ∧
      result = (⟨.valid, some state.headBlockHash⟩, some state.headBlockHash) ∧
      onChain tree state.headBlockHash state.safeBlockHash = true ∧
      onChain tree state.headBlockHash state.finalizedBlockHash = true := by
  unfold forkchoiceUpdated at h
  cases hp : tree.lookup state.headBlockHash with
  | none =>
    simp only [hp, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp at hValid
  | some p =>
    simp only [hp] at h
    by_cases hT : chainPassesTerminalCheck transition tree state.headBlockHash = true
    · by_cases hv : p.valid = true
      · by_cases hz : zeroAfterTransition tree finalized state = true
        · simp [hT, hv, hAbove, hz, throw, throwThe, MonadExceptOf.throw] at h
        · by_cases hc : onChain tree state.headBlockHash state.safeBlockHash = true ∧
              onChain tree state.headBlockHash state.finalizedBlockHash = true
          · simp only [hT, hv, hAbove, hz, hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
              Bool.and_self, pure, Except.pure, Except.ok.injEq] at h
            subst h
            exact ⟨⟨p, rfl, hv⟩, hT, by simpa using hz, rfl, hc.1, hc.2⟩
          · simp [hT, hv, hAbove, hz, hc, throw, throwThe, MonadExceptOf.throw] at h
      · simp only [hT, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
          pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp at hValid
    · simp only [hT, Bool.not_false, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp at hValid

/-- A valid head below the known finalized block is valid, and the head does not change.

Its chain must pass the terminal block check.

Neither the safe nor the finalized block of the request is checked. -/
theorem forkchoiceUpdated_of_belowFinalized {p : KnownPayload}
    (hp : tree.lookup state.headBlockHash = some p) (hValid : p.valid = true)
    (hTerminal : chainPassesTerminalCheck transition tree state.headBlockHash = true)
    (hBelow : belowFinalized tree finalized state.headBlockHash = true) :
    forkchoiceUpdated transition tree finalized state =
      .ok (⟨.valid, some state.headBlockHash⟩, none) := by
  simp [forkchoiceUpdated, hp, hValid, hTerminal, hBelow, pure, Except.pure]

/-- An update is valid with no new head exactly for a valid head below the known finalized block.

The chain of that head passes the terminal block check.

This is the answer of step 2, with the head as the latest valid block. -/
theorem forkchoiceUpdated_valid_none_iff {result : PayloadStatus × Option Hash32} :
    (forkchoiceUpdated transition tree finalized state = .ok result ∧
        result.1.status = .valid ∧ result.2 = none) ↔
      (∃ p, tree.lookup state.headBlockHash = some p ∧ p.valid = true) ∧
        chainPassesTerminalCheck transition tree state.headBlockHash = true ∧
        belowFinalized tree finalized state.headBlockHash = true ∧
        result = (⟨.valid, some state.headBlockHash⟩, none) := by
  unfold forkchoiceUpdated
  cases hp : tree.lookup state.headBlockHash with
  | none =>
    simp [pure, Except.pure]
    rintro rfl
    simp
  | some p =>
    by_cases hT : chainPassesTerminalCheck transition tree state.headBlockHash = true
    · by_cases hv : p.valid = true
      · by_cases hb : belowFinalized tree finalized state.headBlockHash = true
        · simp only [hT, hv, hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure,
            Except.pure, Except.ok.injEq]
          simp only [Option.some.injEq, exists_eq_left', hv, true_and]
          constructor
          · rintro ⟨rfl, -, -⟩
            rfl
          · rintro rfl
            simp
        · by_cases hz : zeroAfterTransition tree finalized state = true
          · simp [hT, hv, hb, hz, throw, throwThe, MonadExceptOf.throw]
          · by_cases hc : onChain tree state.headBlockHash state.safeBlockHash = true ∧
                onChain tree state.headBlockHash state.finalizedBlockHash = true
            · simp [hT, hv, hb, hz, hc, pure, Except.pure]
              rintro rfl
              simp
            · simp [hT, hv, hb, hz, hc, throw, throwThe, MonadExceptOf.throw]
      · simp [hT, hv, pure, Except.pure]
        rintro rfl
        simp
    · simp [hT, pure, Except.pure]
      rintro rfl
      simp

/-- An invalid head that the tree holds is invalid, with the latest valid hash of its chain.

Its chain must pass the terminal block check. -/
theorem forkchoiceUpdated_of_invalid {p : KnownPayload}
    (hp : tree.lookup state.headBlockHash = some p) (hInvalid : p.valid = false)
    (hTerminal : chainPassesTerminalCheck transition tree state.headBlockHash = true) :
    forkchoiceUpdated transition tree finalized state =
      .ok (⟨.invalid, latestValidHash tree state.headBlockHash⟩, none) := by
  simp [forkchoiceUpdated, hp, hInvalid, hTerminal, pure, Except.pure]

/-- An update of a head that the tree does not hold is syncing, and the head does not change. -/
theorem forkchoiceUpdated_of_unknown (hNone : tree.lookup state.headBlockHash = none) :
    forkchoiceUpdated transition tree finalized state = .ok (⟨.syncing, none⟩, none) := by
  simp [forkchoiceUpdated, hNone, pure, Except.pure]

/-- A valid head with its safe and finalized blocks zero or on its chain becomes the head.

The chain of the head must pass the terminal block check.

The head must not be below the known finalized block.

Zero hashes are allowed only until the transition block is finalized. -/
theorem forkchoiceUpdated_of_onChain {p : KnownPayload}
    (hp : tree.lookup state.headBlockHash = some p) (hValid : p.valid = true)
    (hTerminal : chainPassesTerminalCheck transition tree state.headBlockHash = true)
    (hAbove : belowFinalized tree finalized state.headBlockHash = false)
    (hZero : zeroAfterTransition tree finalized state = false)
    (hSafe : onChain tree state.headBlockHash state.safeBlockHash = true)
    (hFinalized : onChain tree state.headBlockHash state.finalizedBlockHash = true) :
    forkchoiceUpdated transition tree finalized state =
      .ok (⟨.valid, some state.headBlockHash⟩, some state.headBlockHash) := by
  simp [forkchoiceUpdated, hp, hValid, hTerminal, hAbove, hZero, hSafe, hFinalized, pure,
    Except.pure]

/-- After the transition, a zero safe or finalized hash is an invalid forkchoice state.

The head is valid, and its chain passes the terminal block check.

The head is not below the known finalized block. -/
theorem forkchoiceUpdated_zero_after_transition {p : KnownPayload}
    (hp : tree.lookup state.headBlockHash = some p) (hValid : p.valid = true)
    (hTerminal : chainPassesTerminalCheck transition tree state.headBlockHash = true)
    (hAbove : belowFinalized tree finalized state.headBlockHash = false)
    (hTransition : transitionFinalized tree finalized = true)
    (hZero : state.safeBlockHash = ZERO_HASH ∨ state.finalizedBlockHash = ZERO_HASH) :
    forkchoiceUpdated transition tree finalized state = .error .invalidForkchoiceState := by
  have hz : zeroAfterTransition tree finalized state = true := by
    rcases hZero with hZero | hZero <;> simp [zeroAfterTransition, hTransition, hZero]
  simp [forkchoiceUpdated, hp, hValid, hTerminal, hAbove, hz, throw, throwThe,
    MonadExceptOf.throw]

/-- An update fails in one case only.

The head is valid, and its chain passes the terminal block check.

The head is not below the known finalized block.

Then its safe or its finalized block is zero after the transition, or neither zero nor on its chain.

The error is then that of an invalid forkchoice state. -/
theorem forkchoiceUpdated_eq_error_iff {e : EngineError} :
    forkchoiceUpdated transition tree finalized state = .error e ↔
      e = .invalidForkchoiceState ∧
        ∃ p, tree.lookup state.headBlockHash = some p ∧ p.valid = true ∧
          chainPassesTerminalCheck transition tree state.headBlockHash = true ∧
          belowFinalized tree finalized state.headBlockHash = false ∧
          (zeroAfterTransition tree finalized state = true ∨
            ¬(onChain tree state.headBlockHash state.safeBlockHash = true ∧
              onChain tree state.headBlockHash state.finalizedBlockHash = true)) := by
  unfold forkchoiceUpdated
  cases hp : tree.lookup state.headBlockHash with
  | none => simp [pure, Except.pure]
  | some p =>
    by_cases hT : chainPassesTerminalCheck transition tree state.headBlockHash = true
    · by_cases hv : p.valid = true
      · by_cases hb : belowFinalized tree finalized state.headBlockHash = true
        · simp [hT, hv, hb, pure, Except.pure]
        · by_cases hz : zeroAfterTransition tree finalized state = true
          · simp [hT, hv, hb, hz, throw, throwThe, MonadExceptOf.throw]
            exact eq_comm
          · by_cases hc : onChain tree state.headBlockHash state.safeBlockHash = true ∧
                onChain tree state.headBlockHash state.finalizedBlockHash = true
            · simp [hT, hv, hb, hz, hc, pure, Except.pure]
            · simp [hT, hv, hb, hz, hc, throw, throwThe, MonadExceptOf.throw]
              exact eq_comm
      · simp [hT, hv, pure, Except.pure]
    · simp [hT, pure, Except.pure]

/-- Without a known finalized block, no head is below it. -/
@[simp] theorem belowFinalized_none (h : Hash32) : belowFinalized tree none h = false := rfl

/-! ## The parameters -/

/-- The forkchoice state decodes exactly when its object holds exactly its three fields.

Each of them must decode as a hash of 32 bytes, which becomes that field of the state. -/
theorem forkchoiceStateOfJson_eq_ok_iff {j : Lean.Json} {s : ForkchoiceState} :
    forkchoiceStateOfJson j = .ok s ↔
      ∃ fs, fields "forkchoiceState" j = .ok fs ∧
        hasExactly fs ["headBlockHash", "safeBlockHash", "finalizedBlockHash"] = true ∧
        ∃ head safe finalized, fs.lookup "headBlockHash" = some head ∧
          fs.lookup "safeBlockHash" = some safe ∧ fs.lookup "finalizedBlockHash" = some finalized ∧
          fixed "headBlockHash" 32 head = .ok s.headBlockHash ∧
          fixed "safeBlockHash" 32 safe = .ok s.safeBlockHash ∧
          fixed "finalizedBlockHash" 32 finalized = .ok s.finalizedBlockHash := by
  unfold forkchoiceStateOfJson
  simp only [bind_ok_iff, Json.liftM_eq_ok_iff]
  constructor
  · rintro ⟨fs, hfs, h⟩
    by_cases hc : hasExactly fs ["headBlockHash", "safeBlockHash", "finalizedBlockHash"] = true
    · rw [ite_eq_left hc] at h
      simp only [bind_ok_iff, Json.liftM_eq_ok_iff, field_eq_ok_iff] at h
      obtain ⟨head, hl1, h1, hf1, safe, hl2, h2, hf2, fin, hl3, h3, hf3, hs⟩ := h
      cases hs
      exact ⟨fs, hfs, hc, head, safe, fin, hl1, hl2, hl3, hf1, hf2, hf3⟩
    -- An object with other fields fails with an invalid parameter, never with a state.
    · rw [ite_eq_right hc, bind_ok_iff] at h
      obtain ⟨_, hInvalid, -⟩ := h
      cases hInvalid
  · rintro ⟨fs, hfs, hc, head, safe, fin, hl1, hl2, hl3, hf1, hf2, hf3⟩
    refine ⟨fs, hfs, ?_⟩
    rw [ite_eq_left hc]
    simp only [bind_ok_iff, Json.liftM_eq_ok_iff, field_eq_ok_iff]
    exact ⟨head, hl1, _, hf1, safe, hl2, _, hf2, fin, hl3, _, hf3, rfl⟩

/-- The parameters decode exactly when they are a JSON array of the state and the attributes.

From version 4 the custody columns may follow them.

The first value must decode as a forkchoice state.

The second value must be `null` or an object.

The custody columns, `null` when absent, must decode.

The result is that state, and the payload attributes when they are an object. -/
theorem forkchoiceUpdatedParams_eq_ok_iff {version : Nat} {params : Lean.Json}
    {r : ForkchoiceState × Option Lean.Json} :
    forkchoiceUpdatedParams version params = .ok r ↔
      ∃ stateJson attributes custody s,
        (params = .arr #[stateJson, attributes] ∧ custody = .null ∨
          4 ≤ version ∧ params = .arr #[stateJson, attributes, custody]) ∧
        forkchoiceStateOfJson stateJson = .ok s ∧
        (∃ columns, custodyColumnsOfJson custody = .ok columns) ∧
        (attributes = .null ∧ r = (s, none) ∨
          ∃ kvs, attributes = .obj kvs ∧ r = (s, some (.obj kvs))) := by
  have hNull : custodyColumnsOfJson .null = .ok none := rfl
  unfold forkchoiceUpdatedParams
  cases params with
  | arr items =>
    obtain ⟨l⟩ := items
    match l with
    | [stateJson, attributes] =>
      cases hs : forkchoiceStateOfJson stateJson <;> cases attributes <;>
        simp [paramsArray, hs, hNull, bind, Except.bind, pure, Except.pure, eq_comm,
          and_assoc]
    | [stateJson, attributes, custody] =>
      by_cases h4 : 4 ≤ version
      · cases hs : forkchoiceStateOfJson stateJson <;> cases hc : custodyColumnsOfJson custody <;>
          cases attributes <;>
          simp [paramsArray, h4, hs, hc, bind, Except.bind, pure, Except.pure, eq_comm,
            and_assoc]
      · simp [paramsArray, h4, bind, Except.bind, pure, Except.pure]
    | [] => simp [paramsArray, bind, Except.bind, pure, Except.pure]
    | [_] => simp [paramsArray, bind, Except.bind, pure, Except.pure]
    | _ :: _ :: _ :: _ :: _ => simp [paramsArray, bind, Except.bind, pure, Except.pure]
  | _ => simp [paramsArray, bind, Except.bind]

/-- Payload attributes that are neither `null` nor an object are an invalid parameter.

That holds for every version and every forkchoice state that decodes.

The error comes before any rule reads the payload tree. -/
theorem forkchoiceUpdatedParams_not_object {version : Nat} {stateJson attributes : Lean.Json}
    {s : ForkchoiceState} (hs : forkchoiceStateOfJson stateJson = .ok s)
    (hNull : attributes ≠ .null) (hObj : ∀ kvs, attributes ≠ .obj kvs) :
    forkchoiceUpdatedParams version (.arr #[stateJson, attributes]) =
      .error (.invalidParams "payloadAttributes: not an object") := by
  unfold forkchoiceUpdatedParams
  cases attributes <;> simp_all [paramsArray, bind, Except.bind, pure, Except.pure]

/-- From version 4, custody columns that decode leave the parameters as they are without them. -/
theorem forkchoiceUpdatedParams_custody {version : Nat} (four : 4 ≤ version)
    {stateJson attributes custody : Lean.Json} {columns : Option (Vector UInt8 16)}
    (decoded : custodyColumnsOfJson custody = .ok columns) :
    forkchoiceUpdatedParams version (.arr #[stateJson, attributes, custody]) =
      forkchoiceUpdatedParams version (.arr #[stateJson, attributes]) := by
  have hNull : custodyColumnsOfJson .null = .ok none := rfl
  cases hs : forkchoiceStateOfJson stateJson <;> cases attributes <;>
    simp [forkchoiceUpdatedParams, paramsArray, four, decoded, hNull, hs, bind, Except.bind,
      pure, Except.pure]

/-- In version 4, custody columns that decode never change the answer of the method.

The answer is the same as without them. -/
theorem forkchoiceUpdatedCall_custody {stateJson attributes custody : Lean.Json}
    {columns : Option (Vector UInt8 16)} (decoded : custodyColumnsOfJson custody = .ok columns) :
    forkchoiceUpdatedCall config transition 4 tree finalized
        (.arr #[stateJson, attributes, custody]) =
      forkchoiceUpdatedCall config transition 4 tree finalized (.arr #[stateJson, attributes]) := by
  simp only [forkchoiceUpdatedCall, forkchoiceUpdatedParams_custody (Nat.le_refl 4) decoded]

/-- Without payload attributes, every version of the method gives the same answer.

So version 4 answers as version 3. -/
theorem forkchoiceUpdatedCall_of_null {version version' : Nat} {stateJson : Lean.Json} :
    forkchoiceUpdatedCall config transition version tree finalized (.arr #[stateJson, .null]) =
      forkchoiceUpdatedCall config transition version' tree finalized
        (.arr #[stateJson, .null]) := by
  cases hs : forkchoiceStateOfJson stateJson <;>
    simp [forkchoiceUpdatedCall, forkchoiceUpdatedParams, paramsArray, custodyColumnsOfJson,
      hs, bind, Except.bind, pure, Except.pure]

/-- Version 4 with custody columns that decode and no attributes answers as version 3. -/
theorem forkchoiceUpdatedCall_four_of_null {stateJson custody : Lean.Json}
    {columns : Option (Vector UInt8 16)} (decoded : custodyColumnsOfJson custody = .ok columns) :
    forkchoiceUpdatedCall config transition 4 tree finalized (.arr #[stateJson, .null, custody]) =
      forkchoiceUpdatedCall config transition 3 tree finalized (.arr #[stateJson, .null]) := by
  rw [forkchoiceUpdatedCall_custody decoded, forkchoiceUpdatedCall_of_null]

/-- Attributes without exactly the fields of a version of their structure do not decode at it. -/
theorem payloadAttributesOfJson_wrong_fields {v : Nat} {j : Lean.Json}
    {fs : List (String × Lean.Json)} (hf : fields "payloadAttributes" j = .ok fs)
    (hx : hasExactly fs (attributesFields v) = false) :
    payloadAttributesOfJson v j = .error (.invalidParams "payloadAttributes: wrong fields") := by
  simp [payloadAttributesOfJson, hf, hx, bind, Except.bind, Json.invalid, throw, throwThe,
    MonadExceptOf.throw]

/-- The attributes of a version of the method fail exactly when no structure that it takes decodes.

The error is then that of invalid payload attributes. -/
theorem payloadAttributesOfVersion_eq_error_iff {version : Nat} {j : Lean.Json}
    {e : EngineError} :
    payloadAttributesOfVersion version j = .error e ↔
      e = .invalidPayloadAttributes ∧
        ∀ v ∈ attributesVersions version, ∃ e', payloadAttributesOfJson v j = .error e' := by
  unfold payloadAttributesOfVersion
  constructor
  · intro h
    split at h
    · cases h
    · next hn =>
      cases h
      refine ⟨rfl, fun v hv => ?_⟩
      have := List.findSome?_eq_none_iff.mp hn v hv
      cases hj : payloadAttributesOfJson v j <;> simp_all [Except.toOption]
  · rintro ⟨rfl, h⟩
    split
    · next a ha =>
      obtain ⟨v, hv, hf⟩ := List.exists_of_findSome?_eq_some ha
      obtain ⟨e', he⟩ := h v hv
      simp [he, Except.toOption] at hf
    · rfl

/-- On an applied valid head, attributes whose fields fit no structure of the version fail.

The answer is then the error of invalid payload attributes, `-38003`, not the status of the head.
-/
theorem forkchoiceUpdatedCall_eq_error_of_attributes {version : Nat}
    {stateJson : Lean.Json} {kvs : Std.TreeMap.Raw String Lean.Json compare}
    {fs : List (String × Lean.Json)} {s : ForkchoiceState} {status : PayloadStatus}
    {head : Hash32} (hs : forkchoiceStateOfJson stateJson = .ok s)
    (hf : forkchoiceUpdated transition tree finalized s = .ok (status, some head))
    (hfs : fields "payloadAttributes" (.obj kvs) = .ok fs)
    (hx : ∀ v ∈ attributesVersions version, hasExactly fs (attributesFields v) = false) :
    forkchoiceUpdatedCall config transition version tree finalized (.arr #[stateJson, .obj kvs]) =
      .error .invalidPayloadAttributes := by
  have hm : payloadAttributesOfVersion version (.obj kvs) = .error .invalidPayloadAttributes :=
    payloadAttributesOfVersion_eq_error_iff.mpr ⟨rfl, fun v hv =>
      ⟨_, payloadAttributesOfJson_wrong_fields hfs (hx v hv)⟩⟩
  simp [forkchoiceUpdatedCall, forkchoiceUpdatedParams, paramsArray, custodyColumnsOfJson,
    hs, hf, hm, bind, Except.bind, pure, Except.pure]

/-- When the update applies no head, the payload attributes are not read.

The answer is that of the update, whatever object the attributes are. -/
theorem forkchoiceUpdatedCall_of_no_head {version : Nat}
    {stateJson : Lean.Json} {kvs : Std.TreeMap.Raw String Lean.Json compare}
    {s : ForkchoiceState} {status : PayloadStatus}
    (hs : forkchoiceStateOfJson stateJson = .ok s)
    (hf : forkchoiceUpdated transition tree finalized s = .ok (status, none)) :
    forkchoiceUpdatedCall config transition version tree finalized (.arr #[stateJson, .obj kvs]) =
      .ok (status, none, none) := by
  simp [forkchoiceUpdatedCall, forkchoiceUpdatedParams, paramsArray, custodyColumnsOfJson,
    hs, hf, bind, Except.bind, pure, Except.pure]

/-- An applied head is a head that the tree holds. -/
theorem exists_lookup_of_forkchoiceUpdated {status : PayloadStatus} {head : Hash32}
    (hf : forkchoiceUpdated transition tree finalized state = .ok (status, some head)) :
    ∃ known, tree.lookup head = some known := by
  unfold forkchoiceUpdated at hf
  split at hf
  · simp [pure, Except.pure] at hf
  · next p hp =>
    repeat' split at hf
    all_goals first
      | simp [pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hf; done
      | (simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hf
         exact ⟨p, hf.2 ▸ hp⟩)

/-- An update applies only the head that it names, with its safe and finalized blocks on its chain.

Each of the two blocks may instead be the zero hash. -/
theorem onChain_of_forkchoiceUpdated {status : PayloadStatus} {head : Hash32}
    (hf : forkchoiceUpdated transition tree finalized state = .ok (status, some head)) :
    head = state.headBlockHash ∧ onChain tree head state.safeBlockHash = true ∧
      onChain tree head state.finalizedBlockHash = true := by
  unfold forkchoiceUpdated at hf
  split at hf
  · simp [pure, Except.pure] at hf
  · repeat' split at hf
    all_goals first
      | simp [pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hf; done
      | (next hc =>
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hf
          rw [← hf.2]
          simpa using hc)

/-- A block that is on the chain of a head and is not the zero hash is a block of that chain. -/
theorem mem_chainOf_of_onChain {head hash : Hash32} (h : onChain tree head hash = true)
    (nonzero : hash ≠ ZERO_HASH) : hash ∈ chainOf tree head := by
  simpa [onChain, nonzero] using h

/-- On an applied valid head, decoded attributes give the answer of their checks against it.

When they pass, the answer is the status, the head, and the attributes at their fork.

When they fail, the answer is the error of the check that fails. -/
theorem forkchoiceUpdatedCall_of_attributes {version : Nat}
    {stateJson : Lean.Json} {kvs : Std.TreeMap.Raw String Lean.Json compare}
    {s : ForkchoiceState} {status : PayloadStatus} {head : Hash32} {known : KnownPayload}
    {decoded : Σ f, PayloadAttributes f}
    (hs : forkchoiceStateOfJson stateJson = .ok s)
    (hf : forkchoiceUpdated transition tree finalized s = .ok (status, some head))
    (hk : tree.lookup head = some known)
    (ha : payloadAttributesOfVersion version (.obj kvs) = .ok decoded) :
    forkchoiceUpdatedCall config transition version tree finalized (.arr #[stateJson, .obj kvs]) =
      (checkAttributes config version known decoded).map
        fun attributes => (status, some head, some attributes) := by
  cases hc : checkAttributes config version known decoded <;>
    simp [forkchoiceUpdatedCall, forkchoiceUpdatedParams, paramsArray, custodyColumnsOfJson,
      hs, hf, hk, ha, hc, bind, Except.bind, pure, Except.pure, Except.map]

/-- Attributes move to a fork exactly when their structure is that of the fork. -/
theorem PayloadAttributes.atFork_isSome_iff {a : Σ f, PayloadAttributes f} {fork : Fork} :
    (PayloadAttributes.atFork a fork).isSome ↔ attributesForkAt fork = a.1 := by
  unfold PayloadAttributes.atFork
  split <;> simp_all

/-- A field read at another fork that has it exactly when the first does keeps its value. -/
theorem sinceValue_congr {f a b : Fork} {α : Type} (h : f ≤ a ↔ f ≤ b) (x : Since f a α) :
    sinceValue (x.congr h) = sinceValue x := by
  by_cases hb : f ≤ b
  · simp [sinceValue, Since.congr, hb, h.mpr hb]
  · simp [sinceValue, hb, mt h.mp hb]

/-- Attributes at a fork keep the timestamp, the RANDAO mix and the fee recipient.

They also keep each field that comes with a fork. -/
theorem PayloadAttributes.atFork_fields {a : Σ f, PayloadAttributes f} {fork : Fork}
    {b : PayloadAttributes fork} (h : PayloadAttributes.atFork a fork = some b) :
    b.timestamp = a.2.timestamp ∧ b.prevRandao = a.2.prevRandao ∧
      b.suggestedFeeRecipient = a.2.suggestedFeeRecipient ∧
      sinceValue b.withdrawals = sinceValue a.2.withdrawals ∧
      sinceValue b.parentBeaconBlockRoot = sinceValue a.2.parentBeaconBlockRoot ∧
      sinceValue b.slotNumber = sinceValue a.2.slotNumber ∧
      sinceValue b.targetGasLimit = sinceValue a.2.targetGasLimit := by
  obtain ⟨f, a⟩ := a
  unfold PayloadAttributes.atFork at h
  split at h
  · next hf =>
    simp only [Option.some.injEq] at h
    subst h
    dsimp only at hf
    subst hf
    simp only [PayloadAttributes.ofStructure, sinceValue_congr, true_and]
  · cases h

/-- Attributes pass their checks exactly when each check holds.

The active fork at the number after the head and at their timestamp is a fork of the version.

Their structure is that of the fork, and their timestamp is above that of the head.

The result is then the attributes at that fork. -/
theorem checkAttributes_eq_ok_iff {version : Nat} {head : KnownPayload}
    {a : Σ f, PayloadAttributes f} {fork : Fork} {b : PayloadAttributes fork} :
    checkAttributes config version head a = .ok ⟨fork, b⟩ ↔
      config.activeFork (head.number.toNat + 1) a.2.timestamp.toNat = some fork ∧
        attributesTakeFork version fork = true ∧ PayloadAttributes.atFork a fork = some b ∧
        head.timestamp < a.2.timestamp := by
  constructor
  · intro h
    cases hF : config.activeFork (head.number.toNat + 1) a.2.timestamp.toNat with
    | none => simp [checkAttributes, hF, throw, throwThe, MonadExceptOf.throw] at h
    | some fork' =>
      cases hT : attributesTakeFork version fork' with
      | false =>
        simp [checkAttributes, hF, hT, bind, Except.bind, throw, throwThe,
          MonadExceptOf.throw] at h
      | true =>
        cases hA : PayloadAttributes.atFork a fork' with
        | none =>
          simp [checkAttributes, hF, hT, hA, throw, throwThe, MonadExceptOf.throw] at h
        | some b' =>
          by_cases hTime : head.timestamp < a.2.timestamp
          · simp only [checkAttributes, hF, hT, hA, hTime, bind, Except.bind, pure, Except.pure,
              reduceIte, Except.ok.injEq, Sigma.mk.injEq] at h
            obtain ⟨rfl, hb⟩ := h
            cases hb
            exact ⟨rfl, hT, hA, hTime⟩
          · simp [checkAttributes, hF, hT, hA, hTime, bind, Except.bind, throw, throwThe,
              MonadExceptOf.throw] at h
  · rintro ⟨hFork, hTake, hAt, hTime⟩
    simp [checkAttributes, hFork, hTake, hAt, hTime, pure, Except.pure]

/-- Attributes of no fork, or of a fork that the version does not take, give `-38005`. -/
theorem checkAttributes_eq_error_of_unsupportedFork {version : Nat} {head : KnownPayload}
    {a : Σ f, PayloadAttributes f}
    (h : ∀ fork, config.activeFork (head.number.toNat + 1) a.2.timestamp.toNat = some fork →
      attributesTakeFork version fork = false) :
    checkAttributes config version head a = .error .unsupportedFork := by
  cases hF : config.activeFork (head.number.toNat + 1) a.2.timestamp.toNat with
  | none => simp [checkAttributes, hF, throw, throwThe, MonadExceptOf.throw]
  | some fork =>
    simp [checkAttributes, hF, h fork hF, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- A version takes exactly the forks from Paris to Glamsterdam whose attributes it decodes.

The structure is that of the payload attributes at the fork.

The source adds a field at Hegotá that these attributes lack, so the bound leaves Hegotá out. -/
theorem attributesTakeFork_eq_true_iff (version : Nat) (fork : Fork) :
    attributesTakeFork version fork = true ↔
      .paris ≤ fork ∧ fork < .hegota ∧
        attributesForkAt fork ∈ (attributesVersions version).map attributesFork := by
  match version with
  | 0 | 1 | 2 | 3 => cases fork <;> decide
  | n + 4 => cases fork <;> simp [attributesTakeFork, attributesVersions, attributesFork] <;> decide

/-- Some version of the method takes a fork exactly when the fork is from Paris to Glamsterdam. -/
theorem exists_attributesTakeFork_iff (fork : Fork) :
    (∃ version, attributesTakeFork version fork = true) ↔ .paris ≤ fork ∧ fork < .hegota := by
  constructor
  · rintro ⟨version, h⟩
    obtain ⟨hLow, hHigh, -⟩ := (attributesTakeFork_eq_true_iff version fork).mp h
    exact ⟨hLow, hHigh⟩
  · intro ⟨hLow, hHigh⟩
    cases fork <;> first
      | exact absurd hLow (by decide)
      | exact absurd hHigh (by decide)
      | exact ⟨1, rfl⟩
      | exact ⟨2, rfl⟩
      | exact ⟨3, rfl⟩
      | exact ⟨4, rfl⟩

/-- A version other than 2 takes only forks whose structure is the one structure that it takes.

So only version 2 can give `-38003` for the structure at the fork. -/
theorem attributesForkAt_of_attributesTakeFork {version : Nat} (hv : version ≠ 2) {fork : Fork}
    (h : attributesTakeFork version fork = true) :
    attributesForkAt fork = attributesFork version := by
  have hmem := ((attributesTakeFork_eq_true_iff version fork).mp h).2.2
  match version, hv with
  | 0, _ | 1, _ | 3, _ | _ + 4, _ => simpa [attributesVersions] using hmem

/-- Attributes of a fork of the version, whose structure is not that of the fork, give `-38003`.

Only version 2 takes two structures, so only it can fail this way. -/
theorem checkAttributes_eq_error_of_wrong_structure {version : Nat} {head : KnownPayload}
    {a : Σ f, PayloadAttributes f} {fork : Fork}
    (hFork : config.activeFork (head.number.toNat + 1) a.2.timestamp.toNat = some fork)
    (hTake : attributesTakeFork version fork = true) (hAt : attributesForkAt fork ≠ a.1) :
    checkAttributes config version head a = .error .invalidPayloadAttributes := by
  have hNone : PayloadAttributes.atFork a fork = none := by
    simpa using mt PayloadAttributes.atFork_isSome_iff.mp hAt
  simp [checkAttributes, hFork, hTake, hNone, throw, throwThe,
    MonadExceptOf.throw]

/-- Attributes that pass the other checks, with a timestamp not above the head's, give `-38003`. -/
theorem checkAttributes_eq_error_of_not_after_head {version : Nat} {head : KnownPayload}
    {a : Σ f, PayloadAttributes f} {fork : Fork} {b : PayloadAttributes fork}
    (hFork : config.activeFork (head.number.toNat + 1) a.2.timestamp.toNat = some fork)
    (hTake : attributesTakeFork version fork = true)
    (hAt : PayloadAttributes.atFork a fork = some b) (hTime : a.2.timestamp ≤ head.timestamp) :
    checkAttributes config version head a = .error .invalidPayloadAttributes := by
  have hNot : ¬ head.timestamp < a.2.timestamp := UInt64.not_lt.mpr hTime
  simp [checkAttributes, hFork, hTake, hAt, hNot, bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw]

/-! ## The writers -/

/-- A computation that has succeeded passes its value on. -/
private theorem ok_bind {α β : Type} (a : α) (f : α → Json.Decode β) :
    (Except.ok a >>= f : Json.Decode β) = f a := rfl

/-- The decoder of the forkchoice state reads back the JSON of every state. -/
theorem forkchoiceStateOfJson_json (state : ForkchoiceState) :
    forkchoiceStateOfJson (forkchoiceStateJson state) = .ok state := by
  have hd : [("headBlockHash", dataJson state.headBlockHash.toList),
      ("safeBlockHash", dataJson state.safeBlockHash.toList),
      ("finalizedBlockHash", dataJson state.finalizedBlockHash.toList)].Pairwise
      fun a b => a.1 ≠ b.1 := by simp
  obtain ⟨fs, hfs, hp⟩ := fields_mkObj "forkchoiceState" hd
    (by simp [dataJson, isNull_str])
  refine forkchoiceStateOfJson_eq_ok_iff.mpr ⟨fs, hfs, hasExactly_of_perm hp,
    dataJson state.headBlockHash.toList, dataJson state.safeBlockHash.toList,
    dataJson state.finalizedBlockHash.toList,
    lookup_of_mem (hp.pairwise_iff (fun h => Ne.symm h) |>.mpr hd) (hp.mem_iff.mpr (by simp)),
    lookup_of_mem (hp.pairwise_iff (fun h => Ne.symm h) |>.mpr hd) (hp.mem_iff.mpr (by simp)),
    lookup_of_mem (hp.pairwise_iff (fun h => Ne.symm h) |>.mpr hd) (hp.mem_iff.mpr (by simp)),
    fixed_dataJson _ _ _, fixed_dataJson _ _ _, fixed_dataJson _ _ _⟩

/-- The pairs of the JSON of payload attributes: those of the fields that their fork has. -/
private def attributePairs {fork : Fork} (a : PayloadAttributes fork) :
    List (String × Lean.Json) :=
  [("timestamp", quantityJson a.timestamp.toNat), ("prevRandao", dataJson a.prevRandao.toList),
      ("suggestedFeeRecipient", dataJson a.suggestedFeeRecipient.toList)] ++
    (if h : .shapella ≤ fork then [("withdrawals", listJson withdrawalJson (a.withdrawals h))]
      else []) ++
    (if h : .dencun ≤ fork then
      [("parentBeaconBlockRoot", dataJson (a.parentBeaconBlockRoot h).toList)] else []) ++
    (if h : .glamsterdam ≤ fork then
      [("slotNumber", quantityJson (a.slotNumber h).toNat),
        ("targetGasLimit", quantityJson (a.targetGasLimit h).toNat)] else [])

/-- The JSON of payload attributes is the object of their pairs. -/
private theorem payloadAttributesJson_eq {fork : Fork} (a : PayloadAttributes fork) :
    payloadAttributesJson a = Lean.Json.mkObj (attributePairs a) := rfl

/-- The pairs of the JSON of payload attributes have distinct names. -/
private theorem attributePairs_distinct {fork : Fork} (a : PayloadAttributes fork) :
    (attributePairs a).Pairwise fun x y => x.1 ≠ y.1 := by
  unfold attributePairs
  by_cases h1 : Fork.shapella ≤ fork <;> by_cases h2 : Fork.dencun ≤ fork <;>
    by_cases h3 : Fork.glamsterdam ≤ fork <;> simp [h1, h2, h3]

/-- No pair of the JSON of payload attributes is `null`. -/
private theorem attributePairs_present {fork : Fork} (a : PayloadAttributes fork) :
    ∀ x ∈ attributePairs a, x.2.isNull = false := by
  unfold attributePairs
  by_cases h1 : Fork.shapella ≤ fork <;> by_cases h2 : Fork.dencun ≤ fork <;>
    by_cases h3 : Fork.glamsterdam ≤ fork <;>
    simp [h1, h2, h3, dataJson, quantityJson, listJson, isNull_str, isNull_arr]

/-- When a version has the fork of the attributes, its fields are the names of the pairs. -/
private theorem attributesFields_eq {fork : Fork} (a : PayloadAttributes fork) {v : Nat}
    (hv : attributesFork v = attributesForkAt fork) :
    attributesFields v = (attributePairs a).map Prod.fst := by
  have h1 := shapella_le_attributesForkAt_iff fork
  have h2 := dencun_le_attributesForkAt_iff fork
  have h3 := glamsterdam_le_attributesForkAt_iff fork
  rw [← hv] at h1 h2 h3
  unfold attributePairs
  rcases v with _ | _ | _ | _ | n <;>
    simp (config := {decide := true}) [attributesFork] at h1 h2 h3 <;>
    simp [attributesFields, attributesFieldsV1, attributesFieldsV2, attributesFieldsV3,
      attributesFieldsV4, h1, h2, h3]

/-- The withdrawals read from the pairs of attributes are the option the attributes give. -/
private theorem attributePairs_lookup_withdrawals {fork : Fork} (a : PayloadAttributes fork) :
    (attributePairs a).lookup "withdrawals" =
      (sinceValue a.withdrawals).map (listJson withdrawalJson) := by
  unfold attributePairs
  by_cases h : Fork.shapella ≤ fork
  · simp [h, sinceValue, List.lookup]
  · simp only [sinceValue, h, dite_false, Option.map_none]
    simp
    rintro k b (⟨rfl, _⟩ | ⟨_, ⟨rfl, _⟩ | ⟨rfl, _⟩⟩) <;> decide

/-- The parent beacon block root read from the pairs of attributes is the option they give. -/
private theorem attributePairs_lookup_beacon {fork : Fork} (a : PayloadAttributes fork) :
    (attributePairs a).lookup "parentBeaconBlockRoot" =
      (sinceValue a.parentBeaconBlockRoot).map (dataJson ·.toList) := by
  by_cases h : Fork.dencun ≤ fork
  · rw [lookup_of_mem (attributePairs_distinct a) (k := "parentBeaconBlockRoot")
      (v := dataJson (a.parentBeaconBlockRoot h).toList) (by simp [attributePairs, h])]
    simp [sinceValue, h]
  · unfold attributePairs
    simp only [sinceValue, h, dite_false, Option.map_none]
    simp
    rintro k b (⟨rfl, _⟩ | ⟨_, ⟨rfl, _⟩ | ⟨rfl, _⟩⟩) <;> decide

/-- The slot number read from the pairs of attributes is the option they give. -/
private theorem attributePairs_lookup_slot {fork : Fork} (a : PayloadAttributes fork) :
    (attributePairs a).lookup "slotNumber" =
      (sinceValue a.slotNumber).map (quantityJson ·.toNat) := by
  by_cases h : Fork.glamsterdam ≤ fork
  · rw [lookup_of_mem (attributePairs_distinct a) (k := "slotNumber")
      (v := quantityJson (a.slotNumber h).toNat) (by simp [attributePairs, h])]
    simp [sinceValue, h]
  · unfold attributePairs
    simp only [sinceValue, h, dite_false, Option.map_none]
    simp
    rintro k b (⟨rfl, _⟩ | ⟨rfl, _⟩) <;> decide

/-- The target gas limit read from the pairs of attributes is the option they give. -/
private theorem attributePairs_lookup_target {fork : Fork} (a : PayloadAttributes fork) :
    (attributePairs a).lookup "targetGasLimit" =
      (sinceValue a.targetGasLimit).map (quantityJson ·.toNat) := by
  by_cases h : Fork.glamsterdam ≤ fork
  · rw [lookup_of_mem (attributePairs_distinct a) (k := "targetGasLimit")
      (v := quantityJson (a.targetGasLimit h).toNat) (by simp [attributePairs, h])]
    simp [sinceValue, h]
  · unfold attributePairs
    simp only [sinceValue, h, dite_false, Option.map_none]
    simp
    rintro k b (⟨rfl, _⟩ | ⟨rfl, _⟩) <;> decide

/-- A field from a fork is present in the option that it gives exactly when the fork has it. -/
private theorem isSome_sinceValue {f fork : Fork} {α : Type} (x : Since f fork α) :
    (sinceValue x).isSome ↔ f ≤ fork := by
  unfold sinceValue
  by_cases h : f ≤ fork <;> simp [h]

/-- The decoder of a version reads back the JSON of attributes at a fork of that version. -/
private theorem payloadAttributesOfJson_json {fork : Fork} (a : PayloadAttributes fork) {v : Nat}
    (hv : attributesFork v = attributesForkAt fork) :
    ∃ c, payloadAttributesOfJson v (payloadAttributesJson a) = .ok c ∧
      c.timestamp = a.timestamp ∧ c.prevRandao = a.prevRandao ∧
      c.suggestedFeeRecipient = a.suggestedFeeRecipient ∧
      sinceValue c.withdrawals = sinceValue a.withdrawals ∧
      sinceValue c.parentBeaconBlockRoot = sinceValue a.parentBeaconBlockRoot ∧
      sinceValue c.slotNumber = sinceValue a.slotNumber ∧
      sinceValue c.targetGasLimit = sinceValue a.targetGasLimit := by
  have hd := attributePairs_distinct a
  obtain ⟨fs, hfs, hp⟩ := fields_mkObj "payloadAttributes" hd (attributePairs_present a)
  have lk := lookup_of_perm hp hd
  have hex : hasExactly fs (attributesFields v) = true := by
    rw [attributesFields_eq a hv]
    exact hasExactly_of_perm hp
  have r1 : field "payloadAttributes" fs "timestamp" = .ok (quantityJson a.timestamp.toNat) :=
    field_of_perm hp hd (by simp [attributePairs])
  have r2 : field "payloadAttributes" fs "prevRandao" = .ok (dataJson a.prevRandao.toList) :=
    field_of_perm hp hd (by simp [attributePairs])
  have r3 : field "payloadAttributes" fs "suggestedFeeRecipient" =
      .ok (dataJson a.suggestedFeeRecipient.toList) :=
    field_of_perm hp hd (by simp [attributePairs])
  have o1 : optionalField fs "withdrawals" (array "withdrawals" withdrawal) =
      Except.ok (sinceValue a.withdrawals) := by
    unfold optionalField
    rw [lk, attributePairs_lookup_withdrawals]
    cases hw : sinceValue a.withdrawals with
    | none => rfl
    | some ws =>
      simp only [Option.map_some]
      rw [Execution.Rpc.array_withdrawal_listJson]
      rfl
  have o2 : optionalField fs "parentBeaconBlockRoot" (fixed "parentBeaconBlockRoot" 32) =
      Except.ok (sinceValue a.parentBeaconBlockRoot) := by
    unfold optionalField
    rw [lk, attributePairs_lookup_beacon]
    cases hw : sinceValue a.parentBeaconBlockRoot with
    | none => rfl
    | some ws =>
      simp only [Option.map_some]
      rw [fixed_dataJson]
      rfl
  have o3 : optionalField fs "slotNumber" (uint64 "slotNumber") =
      Except.ok (sinceValue a.slotNumber) := by
    unfold optionalField
    rw [lk, attributePairs_lookup_slot]
    cases hw : sinceValue a.slotNumber with
    | none => rfl
    | some ws =>
      simp only [Option.map_some]
      rw [uint64_toDigits]
      rfl
  have o4 : optionalField fs "targetGasLimit" (uint64 "targetGasLimit") =
      Except.ok (sinceValue a.targetGasLimit) := by
    unfold optionalField
    rw [lk, attributePairs_lookup_target]
    cases hw : sinceValue a.targetGasLimit with
    | none => rfl
    | some ws =>
      simp only [Option.map_some]
      rw [uint64_toDigits]
      rfl
  have s1 := shapella_le_attributesForkAt_iff fork
  have s2 := dencun_le_attributesForkAt_iff fork
  have s3 := glamsterdam_le_attributesForkAt_iff fork
  rw [← hv] at s1 s2 s3
  obtain ⟨x1, hx1⟩ := exists_since_iff (what := "withdrawals") |>.mpr
    ((isSome_sinceValue a.withdrawals).trans s1.symm)
  obtain ⟨x2, hx2⟩ := exists_since_iff (what := "parentBeaconBlockRoot") |>.mpr
    ((isSome_sinceValue a.parentBeaconBlockRoot).trans s2.symm)
  obtain ⟨x3, hx3⟩ := exists_since_iff (what := "slotNumber") |>.mpr
    ((isSome_sinceValue a.slotNumber).trans s3.symm)
  obtain ⟨x4, hx4⟩ := exists_since_iff (what := "targetGasLimit") |>.mpr
    ((isSome_sinceValue a.targetGasLimit).trans s3.symm)
  unfold payloadAttributesOfJson
  rw [payloadAttributesJson_eq]
  simp only [hfs, liftM_ok, ok_bind]
  rw [ite_eq_left hex]
  simp only [r1, r2, r3, o1, o2, o3, o4, hx1, hx2, hx3, hx4, liftM_ok, ok_bind,
    uint64_toDigits, fixed_dataJson, address_dataJson]
  exact ⟨_, rfl, rfl, rfl, rfl, sinceValue_of_since hx1, sinceValue_of_since hx2,
    sinceValue_of_since hx3, sinceValue_of_since hx4⟩

/-- Two fields from a fork that give the same option are equal. -/
private theorem since_ext {f fork : Fork} {α : Type} {x y : Since f fork α}
    (h : sinceValue x = sinceValue y) : x = y := by
  by_cases hf : f ≤ fork
  · simp only [sinceValue, hf, dite_true, Option.some.injEq] at h
    rw [Since.eq_const hf x, Since.eq_const hf y, h]
  · exact Since.eq_of_not_le hf x y

/-- Attributes of a structure that agree field by field with those of a fork are those at it. -/
private theorem atFork_eq_some {fork : Fork} (a : PayloadAttributes fork)
    (b : Σ f, PayloadAttributes f) (hb : b.1 = attributesForkAt fork)
    (e1 : b.2.timestamp = a.timestamp) (e2 : b.2.prevRandao = a.prevRandao)
    (e3 : b.2.suggestedFeeRecipient = a.suggestedFeeRecipient)
    (e4 : sinceValue b.2.withdrawals = sinceValue a.withdrawals)
    (e5 : sinceValue b.2.parentBeaconBlockRoot = sinceValue a.parentBeaconBlockRoot)
    (e6 : sinceValue b.2.slotNumber = sinceValue a.slotNumber)
    (e7 : sinceValue b.2.targetGasLimit = sinceValue a.targetGasLimit) :
    PayloadAttributes.atFork b fork = some a := by
  obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.mp
    (PayloadAttributes.atFork_isSome_iff.mpr hb.symm)
  rw [hb']
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := PayloadAttributes.atFork_fields hb'
  congr 1
  cases a
  cases b'
  simp only [PayloadAttributes.mk.injEq]
  exact ⟨f1.trans e1, f2.trans e2, f3.trans e3, since_ext (f4.trans e4), since_ext (f5.trans e5),
    since_ext (f6.trans e6), since_ext (f7.trans e7)⟩

/-- A version of the method reads back the JSON of attributes whose structure it takes.

The structure of the fork of the attributes must be one that the version takes.

The attributes read back are those of that structure, and at the fork they are the attributes. -/
theorem payloadAttributesOfVersion_json {fork : Fork} (a : PayloadAttributes fork)
    {version : Nat}
    (takes : ∃ v ∈ attributesVersions version, attributesFork v = attributesForkAt fork) :
    ∃ b, payloadAttributesOfVersion version (payloadAttributesJson a) = .ok b ∧
      PayloadAttributes.atFork b fork = some a := by
  obtain ⟨v, hmem, hv⟩ := takes
  obtain ⟨c, hc, e1, e2, e3, e4, e5, e6, e7⟩ := payloadAttributesOfJson_json a hv
  refine ⟨⟨attributesFork v, c⟩, ?_, atFork_eq_some a ⟨attributesFork v, c⟩ hv e1 e2 e3 e4 e5 e6 e7⟩
  unfold payloadAttributesOfVersion
  by_cases h2 : version = 2
  · subst h2
    simp only [attributesVersions, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · simp [attributesVersions, hc, Except.toOption]
    · -- Version 1 of the structure fails on an object with the four fields of version 2.
      obtain ⟨fs, hfs, hp⟩ := fields_mkObj "payloadAttributes" (attributePairs_distinct a)
        (attributePairs_present a)
      have hex : hasExactly fs (attributesFields 2) = true := by
        rw [attributesFields_eq a hv]
        exact hasExactly_of_perm hp
      have hne : hasExactly fs (attributesFields 1) = false := by
        cases h : hasExactly fs (attributesFields 1)
        · rfl
        · simp only [hasExactly, Bool.and_eq_true, beq_iff_eq] at hex h
          simp [attributesFields, attributesFieldsV1, attributesFieldsV2] at hex h
          omega
      have hfail := payloadAttributesOfJson_wrong_fields (v := 1)
        (j := payloadAttributesJson a) (by rw [payloadAttributesJson_eq]; exact hfs) hne
      simp [attributesVersions, List.findSome?, hfail, hc, Except.toOption]
  · have hl : attributesVersions version = [version] := by
      unfold attributesVersions
      split
      · exact absurd rfl h2
      · rfl
    rw [hl] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    subst hmem
    simp [hl, hc, Except.toOption]

/-- The decoder of the custody columns reads back the columns that the writer writes, or none. -/
theorem custodyColumnsOfJson_json (custody : Option (Vector UInt8 16)) :
    custodyColumnsOfJson (optionJson (dataJson ·.toList) custody) = .ok custody := by
  cases custody with
  | none => rfl
  | some c =>
    simp only [optionJson, custodyColumnsOfJson, dataJson, fixed_hexString, liftM_ok]
    rfl

/-- The decoder of the parameters reads back the state and the JSON of the attributes.

From version 4 this holds whatever custody columns follow. -/
theorem forkchoiceUpdatedParams_json {fork : Fork} (version : Nat) (state : ForkchoiceState)
    (attributes : Option (PayloadAttributes fork)) (custody : Option (Vector UInt8 16)) :
    forkchoiceUpdatedParams version (forkchoiceUpdatedParamsJson version state attributes custody) =
      .ok (state, attributes.map payloadAttributesJson) := by
  -- The attributes are `null` when there are none, and an object otherwise.
  have hlast : optionJson payloadAttributesJson attributes = .null ∧
        (state, attributes.map payloadAttributesJson) = (state, none) ∨
      ∃ kvs, optionJson payloadAttributesJson attributes = .obj kvs ∧
        (state, attributes.map payloadAttributesJson) = (state, some (.obj kvs)) := by
    cases attributes with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some a =>
      obtain ⟨kvs, hk⟩ : ∃ kvs, payloadAttributesJson a = .obj kvs := ⟨_, rfl⟩
      exact Or.inr ⟨kvs, hk, by simp [hk]⟩
  unfold forkchoiceUpdatedParamsJson
  rw [forkchoiceUpdatedParams_eq_ok_iff]
  by_cases h4 : 4 ≤ version
  · refine ⟨forkchoiceStateJson state, optionJson payloadAttributesJson attributes,
      optionJson (dataJson ·.toList) custody, state, Or.inr ⟨h4, by simp [h4]⟩,
      forkchoiceStateOfJson_json state, ⟨custody, custodyColumnsOfJson_json custody⟩, hlast⟩
  · exact ⟨forkchoiceStateJson state, optionJson payloadAttributesJson attributes, .null, state,
      Or.inl ⟨by simp [h4], rfl⟩, forkchoiceStateOfJson_json state, ⟨none, rfl⟩, hlast⟩

/-- The status of every answer of an update is valid, invalid or syncing. -/
private theorem forkchoiceUpdated_status {result : PayloadStatus × Option Hash32}
    (h : forkchoiceUpdated transition tree finalized state = .ok result) :
    result.1.status = .valid ∨ result.1.status = .invalid ∨ result.1.status = .syncing := by
  unfold forkchoiceUpdated at h
  repeat' split at h
  all_goals first
    | (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; simp)
    | simp [throw, throwThe, MonadExceptOf.throw] at h

/-- An answer of a call comes from its update, and names a build only with attributes that pass. -/
private theorem forkchoiceUpdatedCall_ok_cases {version : Nat} {params : Lean.Json}
    {r : PayloadStatus × Option Hash32 × Option (Σ fork, PayloadAttributes fork)}
    (h : forkchoiceUpdatedCall config transition version tree finalized params = .ok r) :
    ∃ state attributes status head,
      forkchoiceUpdatedParams version params = .ok (state, attributes) ∧
      forkchoiceUpdated transition tree finalized state = .ok (status, head) ∧ r.1 = status ∧
      (r.2 = (head, none) ∨
        ∃ j h' known decoded a, attributes = some j ∧ head = some h' ∧
          payloadAttributesOfVersion version j = .ok decoded ∧ tree.lookup h' = some known ∧
          checkAttributes config version known decoded = .ok a ∧
          r = (status, some h', some a)) := by
  unfold forkchoiceUpdatedCall at h
  cases hp : forkchoiceUpdatedParams version params with
  | error e => simp [hp, bind, Except.bind] at h
  | ok pr =>
    obtain ⟨state, attributes⟩ := pr
    cases hf : forkchoiceUpdated transition tree finalized state with
    | error e => simp [hp, hf, bind, Except.bind] at h
    | ok pr2 =>
      obtain ⟨status, head⟩ := pr2
      simp only [hp, hf, bind, Except.bind] at h
      refine ⟨state, attributes, status, head, rfl, hf, ?_⟩
      rcases attributes with _ | j
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp
      rcases head with _ | h'
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp
      cases hd : payloadAttributesOfVersion version j with
      | error e => simp [hd] at h
      | ok v =>
        cases hk : List.lookup h' tree with
        | none =>
          simp only [hd, hk, pure, Except.pure, Except.ok.injEq] at h
          subst h
          simp
        | some known =>
          cases hc : checkAttributes config version known v with
          | error e => simp [hd, hk, hc] at h
          | ok a =>
            simp only [hd, hk, hc, pure, Except.pure, Except.ok.injEq] at h
            subst h
            exact ⟨rfl, Or.inr ⟨j, h', known, v, a, rfl, rfl, hd, hk, hc, rfl⟩⟩

/-- Every answer of a call has a status of the three that step 9 allows. -/
theorem forkchoiceUpdatedCall_status {version : Nat} {params : Lean.Json}
    {r : PayloadStatus × Option Hash32 × Option (Σ fork, PayloadAttributes fork)}
    (h : forkchoiceUpdatedCall config transition version tree finalized params = .ok r) :
    r.1.status = .valid ∨ r.1.status = .invalid ∨ r.1.status = .syncing := by
  obtain ⟨_, _, status, head, -, hf, h1, -⟩ := forkchoiceUpdatedCall_ok_cases h
  rw [h1]
  exact forkchoiceUpdated_status hf

/-- The response of a call names a build exactly when the call starts one.

That is when the update applies a head that the tree holds, and attributes that pass their checks.

The ID is then that of the head and the attributes at their fork. -/
theorem forkchoiceUpdatedResponse_payloadId {version : Nat} {params : Lean.Json}
    {r : PayloadStatus × Option Hash32 × Option (Σ fork, PayloadAttributes fork)}
    {id : PayloadId}
    (h : forkchoiceUpdatedCall config transition version tree finalized params = .ok r) :
    (forkchoiceUpdatedResponse r).2 = some id ↔
      ∃ state j status head known decoded a,
        forkchoiceUpdatedParams version params = .ok (state, some j) ∧
        forkchoiceUpdated transition tree finalized state = .ok (status, some head) ∧
        tree.lookup head = some known ∧
        payloadAttributesOfVersion version j = .ok decoded ∧
        checkAttributes config version known decoded = .ok a ∧
        id = payloadId head a.2 := by
  constructor
  · intro hid
    obtain ⟨state, attributes, status, head, hp, hf, h1, h2 | ⟨j, h', known, decoded, a, rfl, rfl,
      hd, hk, hc, rfl⟩⟩ := forkchoiceUpdatedCall_ok_cases h
    · obtain ⟨r1, r2⟩ := r
      obtain ⟨r2a, r2b⟩ := r2
      simp only [Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      simp [forkchoiceUpdatedResponse] at hid
    · simp only [forkchoiceUpdatedResponse, Option.bind_some, Option.map_some, Option.some.injEq]
        at hid
      exact ⟨state, j, status, h', known, decoded, a, hp, hf, hk, hd, hc, hid.symm⟩
  · rintro ⟨state, j, status, head, known, decoded, a, hp, hf, hk, hd, hc, rfl⟩
    simp only [forkchoiceUpdatedCall, hp, hf, hk, hd, hc, bind, Except.bind, pure,
      Except.pure] at h
    cases h
    rfl

/-- The decoder of a forkchoice response reads back the JSON of every response it allows.

The status must be valid, invalid or syncing. -/
theorem forkchoiceUpdatedResponseOfJson_json (s : PayloadStatus) (e : Option String)
    (id : Option PayloadId) (h : s.status.restricted = true) :
    forkchoiceUpdatedResponseOfJson (forkchoiceUpdatedResponseJson s e id) = .ok (s, e, id) := by
  have hd : [("payloadStatus", Json.payloadStatusJson s e),
      ("payloadId", optionJson (dataJson ·.toList) id)].Pairwise fun a b => a.1 ≠ b.1 := by simp
  obtain ⟨fs, hfs, hp⟩ := EthLib.Serialization.JsonRpc.fields_mkObj_filter
    "forkchoiceUpdatedResponse" hd
  have look := EthLib.Serialization.JsonRpc.lookup_of_perm_filter hp hd
  have k1 : ∀ a b : Lean.Json,
      [("payloadStatus", a), ("payloadId", b)].lookup "payloadStatus" = some a :=
    fun _ _ => rfl
  have k2 : ∀ a b : Lean.Json,
      [("payloadStatus", a), ("payloadId", b)].lookup "payloadId" = some b :=
    fun _ _ => rfl
  have l1 : fs.lookup "payloadStatus" = some (Json.payloadStatusJson s e) := by
    rw [look, k1]; rfl
  have l2 : fs.lookup "payloadId" = id.map (dataJson ·.toList) := by
    rw [look, k2]; cases id <;> rfl
  have hall : (fs.all (["payloadStatus", "payloadId"].contains ·.1)) = true := by
    rw [List.all_eq_true]
    intro p hm
    obtain ⟨hm, -⟩ := List.mem_filter.mp (hp.mem_iff.mp hm)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp
  have hf : field "forkchoiceUpdatedResponse" fs "payloadStatus" =
      .ok (Json.payloadStatusJson s e) := by
    simp [field, l1]; rfl
  unfold forkchoiceUpdatedResponseOfJson forkchoiceUpdatedResponseJson
  simp only [hfs, liftM_ok, ok_bind, hall, ite_true, hf, l2, Json.payloadStatusOfJson_json, h]
  cases id <;> simp [Json.lift, fixed_dataJson, Option.mapM] <;> rfl

/-- A JSON value reads as a forkchoice response exactly when it is an object of the form below.

A member whose value is `null` counts as absent.

Its other members are `payloadStatus` and `payloadId` alone.

The value of `payloadStatus` reads as the payload status and the validation error.

The status is valid, invalid or syncing.

The payload ID is `0x` and 16 lowercase hex digits, or absent. -/
theorem forkchoiceUpdatedResponseOfJson_eq_ok_iff {j : Lean.Json} {s : PayloadStatus}
    {e : Option String} {id : Option PayloadId} :
    forkchoiceUpdatedResponseOfJson j = .ok (s, e, id) ↔
      ∃ fs, fields "forkchoiceUpdatedResponse" j = .ok fs ∧
        (∀ f ∈ fs, f.1 = "payloadStatus" ∨ f.1 = "payloadId") ∧
        (∃ status, fs.lookup "payloadStatus" = some status ∧
          Json.payloadStatusOfJson status = .ok (s, e)) ∧
        (s.status = .valid ∨ s.status = .invalid ∨ s.status = .syncing) ∧
        fs.lookup "payloadId" = id.map fun i => .str (hexString i.toList) := by
  unfold forkchoiceUpdatedResponseOfJson
  simp only [bind_ok_iff, Json.liftM_eq_ok_iff]
  refine exists_congr fun fs => and_congr_right fun _ => ?_
  have allIff : fs.all (["payloadStatus", "payloadId"].contains ·.1) = true ↔
      ∀ f ∈ fs, f.1 = "payloadStatus" ∨ f.1 = "payloadId" := by
    simp [List.all_eq_true]
  have restrictedIff : s.status.restricted = true ↔
      s.status = .valid ∨ s.status = .invalid ∨ s.status = .syncing := by
    cases s.status <;> simp [Status.restricted]
  by_cases hall : fs.all (["payloadStatus", "payloadId"].contains ·.1) = true
  · rw [and_iff_right (allIff.mp hall)]
    simp only [hall, ite_true, bind_ok_iff, Json.liftM_eq_ok_iff, field_eq_ok_iff]
    constructor
    · rintro ⟨status, hs, ⟨s', e'⟩, hp, h⟩
      by_cases hr : s'.status.restricted = true
      · simp only [hr, ite_true, bind_ok_iff, Json.lift_mapM_fixed_eq_ok_iff] at h
        obtain ⟨i, hi, h⟩ := h
        cases h
        exact ⟨⟨status, hs, hp⟩, restrictedIff.mp hr, hi⟩
      -- A status that the method does not answer fails with an invalid parameter.
      · simp only [bind, Except.bind] at h
        split at h
        · contradiction
        · cases h
    · rintro ⟨⟨status, hs, hp⟩, hr, hi⟩
      refine ⟨status, hs, (s, e), hp, ?_⟩
      simp only [restrictedIff.mpr hr, ite_true, bind_ok_iff, Json.lift_mapM_fixed_eq_ok_iff]
      exact ⟨id, hi, rfl⟩
  -- A member of another name fails with an invalid parameter, never with a response.
  · constructor
    · intro h
      simp only [bind, Except.bind] at h
      split at h
      · contradiction
      · cases h
    · rintro ⟨members, -⟩
      exact absurd (allIff.mpr members) hall

/-- The decoder reads back the response of every call, with any validation error. -/
theorem forkchoiceUpdatedResponseOfJson_call {version : Nat} {params : Lean.Json}
    {r : PayloadStatus × Option Hash32 × Option (Σ fork, PayloadAttributes fork)}
    (h : forkchoiceUpdatedCall config transition version tree finalized params = .ok r)
    (e : Option String) :
    forkchoiceUpdatedResponseOfJson (forkchoiceUpdatedResponseJson (forkchoiceUpdatedResponse r).1
      e (forkchoiceUpdatedResponse r).2) =
      .ok ((forkchoiceUpdatedResponse r).1, e, (forkchoiceUpdatedResponse r).2) :=
  forkchoiceUpdatedResponseOfJson_json _ _ _ (by
    rcases forkchoiceUpdatedCall_status h with hs | hs | hs <;>
      simp [forkchoiceUpdatedResponse, hs, Status.restricted])

/-! ## The attributes that the consensus layer sends -/

/-- A fork that a version of the method takes has the structure of a version that it takes. -/
theorem exists_attributesVersions_of_attributesTakeFork {version : Nat} {fork : Fork}
    (h : attributesTakeFork version fork = true) :
    ∃ v ∈ attributesVersions version, attributesFork v = attributesForkAt fork :=
  List.mem_map.mp ((attributesTakeFork_eq_true_iff version fork).mp h).2.2

/-- Attributes sent with a head that the update applies come back at the fork of the next block.

The tree must hold the head.

That fork is the active fork at the number after the head and at the timestamp of the attributes.

The version of the method must take it, and its structure must be that of the attributes.

The timestamp must be above that of the head.

The custody columns, from version 4, do not matter.

The attributes at that fork carry every value of the attributes sent. -/
theorem forkchoiceUpdatedCall_payloadAttributesJson {version : Nat} {fork e : Fork}
    {s : ForkchoiceState} {status : PayloadStatus} {known : KnownPayload}
    (a : PayloadAttributes fork) (custody : Option (Vector UInt8 16))
    (hUpdate : forkchoiceUpdated transition tree finalized s = .ok (status, some s.headBlockHash))
    (hKnown : tree.lookup s.headBlockHash = some known)
    (hTime : known.timestamp < a.timestamp)
    (hFork : config.activeFork (known.number.toNat + 1) a.timestamp.toNat = some e)
    (hTakes : attributesTakeFork version e = true)
    (hShape : attributesForkAt e = attributesForkAt fork) :
    ∃ a' : PayloadAttributes e,
      forkchoiceUpdatedCall config transition version tree finalized
          (forkchoiceUpdatedParamsJson version s (some a) custody) =
        .ok (status, some s.headBlockHash, some ⟨e, a'⟩) ∧
      a'.timestamp = a.timestamp ∧ a'.prevRandao = a.prevRandao ∧
      a'.suggestedFeeRecipient = a.suggestedFeeRecipient ∧
      sinceValue a'.withdrawals = sinceValue a.withdrawals ∧
      sinceValue a'.parentBeaconBlockRoot = sinceValue a.parentBeaconBlockRoot ∧
      sinceValue a'.slotNumber = sinceValue a.slotNumber ∧
      sinceValue a'.targetGasLimit = sinceValue a.targetGasLimit := by
  -- The attributes read back at a structure that the version takes, which is that of their fork.
  have takes := exists_attributesVersions_of_attributesTakeFork hTakes
  rw [hShape] at takes
  obtain ⟨b, hb, hat⟩ := payloadAttributesOfVersion_json a takes
  have hstruct : attributesForkAt fork = b.1 :=
    PayloadAttributes.atFork_isSome_iff.mp (by simp [hat])
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := PayloadAttributes.atFork_fields hat
  -- At the fork of the payload they have the same structure, so they move there.
  obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp
    (PayloadAttributes.atFork_isSome_iff.mpr (hShape.trans hstruct))
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := PayloadAttributes.atFork_fields ha'
  have hcheck : checkAttributes config version known b = .ok ⟨e, a'⟩ :=
    checkAttributes_eq_ok_iff.mpr ⟨t1 ▸ hFork, hTakes, ha', t1 ▸ hTime⟩
  refine ⟨a', ?_, u1.trans t1.symm, u2.trans t2.symm, u3.trans t3.symm, u4.trans t4.symm,
    u5.trans t5.symm, u6.trans t6.symm, u7.trans t7.symm⟩
  unfold forkchoiceUpdatedCall
  rw [forkchoiceUpdatedParams_json]
  simp [hUpdate, hKnown, hb, hcheck, bind, Except.bind, pure, Except.pure]

/-- From Glamsterdam, attributes sent with an applied head come back at Glamsterdam, at version 4.

The tree must hold the head.

The block after the head must be of Glamsterdam, and the timestamp above that of the head.

The attributes at that fork carry every value of the attributes sent. -/
theorem forkchoiceUpdatedCall_payloadAttributesJson_of_gloas {fork : Fork}
    (gloas : .glamsterdam ≤ fork) {s : ForkchoiceState} {status : PayloadStatus}
    {known : KnownPayload} (a : PayloadAttributes fork) (custody : Option (Vector UInt8 16))
    (hUpdate : forkchoiceUpdated transition tree finalized s = .ok (status, some s.headBlockHash))
    (hKnown : tree.lookup s.headBlockHash = some known)
    (hTime : known.timestamp < a.timestamp)
    (hFork : config.activeFork (known.number.toNat + 1) a.timestamp.toNat = some .glamsterdam) :
    ∃ a' : PayloadAttributes .glamsterdam,
      forkchoiceUpdatedCall config transition 4 tree finalized
          (forkchoiceUpdatedParamsJson 4 s (some a) custody) =
        .ok (status, some s.headBlockHash, some ⟨.glamsterdam, a'⟩) ∧
      a'.timestamp = a.timestamp ∧ a'.prevRandao = a.prevRandao ∧
      a'.suggestedFeeRecipient = a.suggestedFeeRecipient ∧
      sinceValue a'.withdrawals = sinceValue a.withdrawals ∧
      sinceValue a'.parentBeaconBlockRoot = sinceValue a.parentBeaconBlockRoot ∧
      sinceValue a'.slotNumber = sinceValue a.slotNumber ∧
      sinceValue a'.targetGasLimit = sinceValue a.targetGasLimit := by
  have hShape : attributesForkAt .glamsterdam = attributesForkAt fork := by
    cases fork <;> first | rfl | exact absurd gloas (by decide)
  exact forkchoiceUpdatedCall_payloadAttributesJson a custody hUpdate hKnown hTime hFork rfl hShape

end EthLib.Engine
