module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.ConfirmedRoot
public import EthLib.Consensus.Proofs.ForkChoice.HonestDuties

/-!
# Proofs: honest validators that run the fast confirmation rule

An honest validator keeps the store of the fork choice and the store of the rule.

It runs the rule at the start of a slot, at most once in each slot.

Its store of the fork choice must then be up to date with its view.

The paper proves safety for the block that the rule stores at the start of a slot.

That is Theorem 2 of Appendix A.2 of [arXiv 2405.00549v4][fcr].

Each execution of this protocol gives an execution of the fork choice alone, with the same views.

Its synchrony carries over, so the duty to vote and the theorems on the fork choice apply to it.

The duty to run the rule takes its set of slots as a parameter.

The duty to vote takes its slots from the assignment in the same way.

[fcr]: https://arxiv.org/abs/2405.00549v4
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- The state of an honest validator that runs the fast confirmation rule. -/
structure ConfirmingState (preset : Preset) (fork : Fork) where
  /-- The store of the fork choice. -/
  store : Store preset fork
  /-- The store of the fast confirmation rule. -/
  fcr : FastConfirmationStore
  /-- The last slot at which the validator ran the rule, if any. -/
  lastSlot : Option Slot

/-- The state of an honest validator before its first run of the rule.

The store of the rule starts from the finalized checkpoint of the store, and no run happened.

The state at the start of an execution is free, so a safety theorem would take this start.

It does not constrain the store of the fork choice, which such a theorem takes reachable. -/
def ConfirmingState.Initial (s : ConfirmingState preset fork) : Prop :=
  s.fcr = getFastConfirmationStore s.store ∧ s.lastSlot = none

/-- A time, in milliseconds, is the start of a slot, for a time of genesis. -/
def IsSlotStart (config : Config) (genesisTimeMs : UInt64) (slot : Slot) (time : ℕ) : Prop :=
  ∃ start, computeTimeAtSlotMs config genesisTimeMs slot = .ok start ∧ time = start.toNat

variable (config : Config) (checks : SignatureChecks) (sources : BlockSources preset fork)
  (genesisTimeMs : UInt64)

/-- The moves of an honest validator that runs the rule, at a time and with a view.

A move of its store of the fork choice keeps the store of the rule.

A run of the rule keeps the store of the fork choice.

A run happens at the start of a slot later than the slot of the last run.

The store of the fork choice then has the time of genesis of the protocol, and is up to date.

Its clock is then in that slot, so the slot it records is the slot of the store.

A later slot than the last run makes the run the only one of its slot. -/
inductive ConfirmingMoves (time : ℕ) (view : Set (Message preset fork))
    (s : ConfirmingState preset fork) : ConfirmingState preset fork → Prop
  /-- A move of the store of the fork choice. -/
  | handles {after : Store preset fork} :
    Handles config checks sources time view s.store after →
      ConfirmingMoves time view s ⟨after, s.fcr, s.lastSlot⟩
  /-- A run of the rule at the start of a slot. -/
  | confirms {slot : Slot} {fcr : FastConfirmationStore} :
    IsSlotStart config genesisTimeMs slot time → (∀ last, s.lastSlot = some last → last < slot) →
      s.store.genesisTimeMs = genesisTimeMs → UpToDate config checks sources time view s.store →
      s.store.getCurrentSlot config = .ok slot →
      s.store.onFastConfirmation config s.fcr = .ok fcr →
      ConfirmingMoves time view s ⟨s.store, fcr, some slot⟩

variable (anchorState : BeaconState preset fork) (anchorBlock : BeaconBlock preset fork)
  (assignment : Assignment preset)

/-- The protocol of honest validators that run the fork choice, vote and run the rule.

The messages and the votes are those of the fork choice alone. -/
abbrev honestConfirming : Protocol ValidatorIndex (Message preset fork)
    (ConfirmingState preset fork) AttestationData where
  signed := statements config checks anchorState anchorBlock
  Sends v time view s :=
    HonestSends config checks sources anchorState anchorBlock assignment genesisTimeMs v time view
      s.store
  Moves _ time view s after := ConfirmingMoves config checks sources genesisTimeMs time view s after

variable {config checks sources genesisTimeMs anchorState anchorBlock assignment}

/-- A move of an honest validator keeps the store of the rule and the slot of its last run.

Or it runs the rule, at the start of a slot later than the last one, and records that slot.

A run has a store of the fork choice that is up to date, with its clock in that slot.

The run is then one fast confirmation, whose confirmed block another proof splits into four cases.
-/
theorem ConfirmingMoves.fcr_eq_or {time : ℕ} {view : Set (Message preset fork)}
    {s after : ConfirmingState preset fork}
    (moved : ConfirmingMoves config checks sources genesisTimeMs time view s after) :
    after.fcr = s.fcr ∧ after.lastSlot = s.lastSlot ∨ ∃ slot,
      IsSlotStart config genesisTimeMs slot time ∧ (∀ last, s.lastSlot = some last → last < slot) ∧
      s.store.genesisTimeMs = genesisTimeMs ∧ UpToDate config checks sources time view s.store ∧
      s.store.getCurrentSlot config = .ok slot ∧ after.store = s.store ∧
      s.store.onFastConfirmation config s.fcr = .ok after.fcr ∧ after.lastSlot = some slot := by
  cases moved with
  | handles _ => exact .inl ⟨rfl, rfl⟩
  | confirms start fresh genesis upToDate current confirmed =>
    exact .inr ⟨_, start, fresh, genesis, upToDate, current, rfl, confirmed, rfl⟩

/-- A property of the state of each honest validator holds along an execution of the protocol.

It holds at the start.

Every move of a store of the fork choice keeps it.

Every run of the rule keeps it, given the conditions of an honest run.

Its case of a run gives the result of the run, which another theorem splits into four cases. -/
theorem Execution.confirmingInduction {J : Set ValidatorIndex}
    (e : Execution (honestConfirming config checks sources genesisTimeMs anchorState anchorBlock
      assignment) J) {I : ValidatorIndex → ConfirmingState preset fork → Prop}
    (start : ∀ v ∈ J, I v (e.start v))
    (handles : ∀ v ∈ J, ∀ time view s after, I v s →
      Handles config checks sources time view s.store after → I v ⟨after, s.fcr, s.lastSlot⟩)
    (confirms : ∀ v ∈ J, ∀ time view s slot fcr, I v s →
      IsSlotStart config genesisTimeMs slot time → (∀ last, s.lastSlot = some last → last < slot) →
      s.store.genesisTimeMs = genesisTimeMs → UpToDate config checks sources time view s.store →
      s.store.getCurrentSlot config = .ok slot →
      s.store.onFastConfirmation config s.fcr = .ok fcr → I v ⟨s.store, fcr, some slot⟩)
    (n : ℕ) : ∀ v ∈ J, I v ((e.world n).state v) :=
  e.state_induction start (fun v honest time view s _ holds moved => by
    cases moved with
    | handles handled => exact handles v honest time view s _ holds handled
    | confirms slotStart fresh genesis upToDate current confirmed =>
      exact confirms v honest time view s _ _ holds slotStart fresh genesis upToDate current
        confirmed) n

/-! ## The execution of the fork choice inside an execution of the rule -/

section Project

variable {ν μ : Type*}

/-- The world of the fork choice inside a world of the rule: each state keeps only its store. -/
def World.stores (w : World ν μ (ConfirmingState preset fork)) : World ν μ (Store preset fork) :=
  ⟨w.time, w.sent, w.view, fun v => (w.state v).store⟩

open Classical in
/-- The event of the fork choice that an event of the rule stands for, in a world.

A move that keeps the store, such as a run of the rule, stands for a wait at the current time. -/
noncomputable def storeEvent (w : World ν μ (ConfirmingState preset fork)) :
    Event ν μ (ConfirmingState preset fork) → Event ν μ (Store preset fork)
  | .wait time => .wait time
  | .send sender message => .send sender message
  | .deliver received => .deliver received
  | .move validator state =>
    if state.store = (w.state validator).store then .wait w.time else .move validator state.store

variable [DecidableEq ν]

/-- The event of the fork choice changes the world inside as the event of the rule does. -/
theorem World.stores_apply (w : World ν μ (ConfirmingState preset fork))
    (event : Event ν μ (ConfirmingState preset fork)) :
    w.stores.apply (storeEvent w event) = (w.apply event).stores := by
  cases event with
  | move validator state =>
    simp only [storeEvent]
    split_ifs with same
    · simp only [World.stores, World.apply, World.mk.injEq, true_and]
      funext u
      by_cases here : u = validator
      · subst here
        simp [same]
      · simp [Function.update_of_ne here]
    · simp only [World.stores, World.apply, World.mk.injEq, true_and]
      funext u
      by_cases here : u = validator
      · subst here
        simp
      · simp [Function.update_of_ne here]
  | _ => rfl

/-- The events of the fork choice give, after each event, the world of the fork choice inside. -/
theorem worldAt_storeEvent (init : World ν μ (ConfirmingState preset fork))
    (events : ℕ → Event ν μ (ConfirmingState preset fork)) (n : ℕ) :
    worldAt init.stores (fun k => storeEvent (worldAt init events k) (events k)) n =
      (worldAt init events n).stores := by
  induction n with
  | zero => rfl
  | succ n ih => rw [worldAt, ih, World.stores_apply, worldAt]

end Project

namespace Execution

variable {J : Set ValidatorIndex}
  (e : Execution (honestConfirming config checks sources genesisTimeMs anchorState anchorBlock
    assignment) J)

/-- The execution of the fork choice inside an execution of the rule.

It has the same times, sent messages and views, and each state keeps only its store. -/
noncomputable def toForkChoice :
    Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J where
  startTime := e.startTime
  start v := (e.start v).store
  events n := storeEvent (e.world n) (e.events n)
  allowed n := by
    have world : worldAt (World.initial e.startTime fun v => (e.start v).store)
        (fun k => storeEvent (e.world k) (e.events k)) n = (e.world n).stores :=
      worldAt_storeEvent (World.initial e.startTime e.start) e.events n
    rw [world]
    have allowed := e.allowed_world n
    generalize e.world n = w at allowed ⊢
    cases event : e.events n with
    | wait time =>
      rw [event] at allowed
      exact allowed
    | send sender message =>
      rw [event] at allowed
      exact allowed
    | deliver received =>
      rw [event] at allowed
      exact allowed
    | move validator state =>
      rw [event] at allowed
      simp only [storeEvent]
      split_ifs with same
      · exact Nat.le_refl _
      · obtain ⟨honest, moved⟩ := allowed
        cases moved with
        | handles handles => exact ⟨honest, handles⟩
        | confirms => exact absurd rfl same

/-- After each event, the world of the fork choice is the one inside the world of the rule. -/
theorem toForkChoice_world (n : ℕ) : e.toForkChoice.world n = (e.world n).stores :=
  worldAt_storeEvent (World.initial e.startTime e.start) e.events n

/-- The execution of the fork choice inside is partially synchronous when the execution is. -/
theorem toForkChoice_partiallySynchronous {GST Δ : ℕ} (sync : e.PartiallySynchronous GST Δ) :
    e.toForkChoice.PartiallySynchronous GST Δ := by
  simpa [Execution.PartiallySynchronous, toForkChoice_world, World.stores] using sync

/-- The execution of the fork choice inside is synchronous when the execution is. -/
theorem toForkChoice_synchronous {Δ : ℕ} (sync : e.Synchronous Δ) :
    e.toForkChoice.Synchronous Δ :=
  e.toForkChoice_partiallySynchronous sync

end Execution

/-! ## The duty to run the rule -/

variable {J : Set ValidatorIndex}

/-- A run of the rule by an honest validator, at the `n`-th event of an execution.

The event is the move of the validator to the store of the rule that the run returns.

It happens at the start of the slot, after the slot of the last run, and records that slot.

The store of the fork choice of the validator then has the time of genesis of the protocol.

That store is up to date, and its clock is in the slot.

The run succeeds from the store of the rule before it. -/
structure ConfirmAt
    (e : Execution (honestConfirming config checks sources genesisTimeMs anchorState anchorBlock
      assignment) J) (v : ValidatorIndex) (slot : Slot) (n : ℕ) (fcr : FastConfirmationStore) :
    Prop where
  moves : e.events n = .move v ⟨((e.world n).state v).store, fcr, some slot⟩
  atTime : IsSlotStart config genesisTimeMs slot (e.world n).time
  fresh : ∀ last, ((e.world n).state v).lastSlot = some last → last < slot
  genesis : ((e.world n).state v).store.genesisTimeMs = genesisTimeMs
  upToDate : UpToDate config checks sources (e.world n).time ((e.world n).view v)
    ((e.world n).state v).store
  current : ((e.world n).state v).store.getCurrentSlot config = .ok slot
  confirmed : ((e.world n).state v).store.onFastConfirmation config ((e.world n).state v).fcr =
    .ok fcr

/-- The duty to run the rule, for a set of slots, from a time `stable` on.

Take an honest validator, a slot of the set, and the start of that slot.

When the execution starts by then, and `stable` is past, the validator runs the rule then.

The duty includes that the run succeeds.

A slot whose start does not fit in 64 bits has no start, so the duty asks nothing there.

A theorem that needs a run at every slot takes a set that holds each slot from `stable` on.

It then covers only executions where the rule never fails at those slots. -/
def Confirms (slots : Set Slot) (stable : ℕ)
    (e : Execution (honestConfirming config checks sources genesisTimeMs anchorState anchorBlock
      assignment) J) : Prop :=
  ∀ v ∈ J, ∀ slot ∈ slots, ∀ time, IsSlotStart config genesisTimeMs slot time →
    e.startTime ≤ time → stable ≤ time → ∃ n fcr, ConfirmAt e v slot n fcr

/-! ## An execution where an honest validator votes and runs the rule -/

/-- A new store holds the unrealized justification of its anchor.

It is the anchor root at the epoch of the anchor state. -/
private theorem getForkchoiceStore_unrealizedJustification
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (made : getForkchoiceStore config anchorState anchorBlock = .ok store)
    {anchorRoot : Root} (hashed : SszType.hashTreeRoot anchorBlock = .ok anchorRoot) :
    store.unrealizedJustification anchorRoot = .ok ⟨getCurrentEpoch anchorState, anchorRoot⟩ := by
  unfold getForkchoiceStore at made
  cases stateRoot : SszType.hashTreeRoot anchorState with
  | error e => simp [stateRoot, bind, Except.bind, Except.mapError] at made
  | ok stateRoot' =>
    simp only [stateRoot, Except.mapError, bind, Except.bind] at made
    split at made
    · simp [throw, throwThe, MonadExceptOf.throw] at made
    · cases blockRoot : SszType.hashTreeRoot anchorBlock with
      | error e => simp [blockRoot] at made
      | ok anchorRoot' =>
        simp only [blockRoot] at made
        cases time : computeTimeAtSlotMs config (secondsToMilliseconds anchorState.genesisTime)
            anchorState.slot with
        | error e => simp [time] at made
        | ok timeMs =>
          simp only [time, pure, Except.pure, Except.ok.injEq] at made
          subst made
          rw [blockRoot, Except.ok.injEq] at hashed
          subst hashed
          simp [Store.unrealizedJustification, pure, Except.pure]

/-- Before Gloas, the rule runs on a store that holds only an anchor block at slot zero.

The store of the rule starts from the finalized checkpoint of the store, the anchor. -/
theorem onFastConfirmation_anchor {store : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok store)
    (stateZero : anchorState.slot = 0) (blockZero : anchorBlock.slot = 0)
    (before : fork < .glamsterdam)
    (parent : ∀ root, SszType.hashTreeRoot anchorBlock = .ok root → anchorBlock.parentRoot ≠ root)
    (slots : 0 < config.SLOT_DURATION_MS) :
    ∃ fcr, store.onFastConfirmation config (getFastConfirmationStore store) = .ok fcr := by
  obtain ⟨anchorRoot, blockRooted, blocks, states⟩ := getForkchoiceStore_maps anchored
  obtain ⟨anchorRoot', blockRooted', -, -, justified, finalized, unrealized, -⟩ :=
    getForkchoiceStore_anchor anchored
  rw [blockRooted, Except.ok.injEq] at blockRooted'
  subst blockRooted'
  have epochZero : getCurrentEpoch anchorState = 0 := by
    simp [getCurrentEpoch, computeEpochAtSlot, stateZero]
  rw [epochZero] at justified finalized unrealized
  have justification := getForkchoiceStore_unrealizedJustification anchored blockRooted
  rw [epochZero] at justification
  have current : store.getCurrentSlot config = .ok 0 :=
    stateZero ▸ getCurrentSlot_getForkchoiceStore slots anchored
  have head : store.getHead config = .ok ⟨anchorRoot, .pending⟩ :=
    getHead_anchor before blocks states (by rw [justified, epochZero])
      (by rw [finalized, epochZero]) current stateZero blockZero (parent _ blockRooted)
  have epoch : store.getCurrentStoreEpoch config = .ok 0 := by
    simp [Store.getCurrentStoreEpoch, current, computeEpochAtSlot, bind, Except.bind, pure,
      Except.pure]
  have found : store.blocks[anchorRoot]? = some anchorBlock := by simp [blocks]
  have blockOk : store.block anchorRoot = .ok anchorBlock := by
    simp [Store.block, found, pure, Except.pure]
  have blockEpoch : store.getBlockEpoch anchorRoot = .ok 0 := by
    simp [Store.getBlockEpoch, blockOk, blockZero, computeEpochAtSlot, bind, Except.bind, pure,
      Except.pure]
  have ancestor : store.getAncestor ⟨anchorRoot, .pending⟩ 0 = .ok ⟨anchorRoot, .pending⟩ :=
    Store.getAncestor_of_le found (by simp [blockZero])
  have isAncestor : store.isAncestor ⟨anchorRoot, .pending⟩ ⟨anchorRoot, .pending⟩ = .ok true := by
    simp [Store.isAncestor, blockOk, blockZero, ancestor, bind, Except.bind, pure, Except.pure]
  have roots : store.getAncestorRoots anchorRoot anchorRoot = .ok [] := by
    rw [Store.getAncestorRoots]
    split <;> simp_all [Store.block, bind, Except.bind, pure, Except.pure]
  have checkpoint : store.getCheckpointForBlock anchorRoot 0 = .ok ⟨0, anchorRoot⟩ := by
    simp [Store.getCheckpointForBlock, Store.getCheckpointBlock, computeStartSlotAtEpoch,
      Uint64.mulChecked, ancestor, bind, Except.bind, pure, Except.pure, Except.mapError]
  have startZero : isStartSlotAtEpoch preset 0 = .ok true := by
    simp [isStartSlotAtEpoch, computeSlotsSinceEpochStart, computeStartSlotAtEpoch,
      computeEpochAtSlot, Uint64.mulChecked, bind, Except.bind, pure, Except.pure, Except.mapError]
  have startOne : ∃ b, isStartSlotAtEpoch preset 1 = .ok b := by
    have small : (1 / preset.SLOTS_PER_EPOCH).toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 := by
      rw [UInt64.toNat_div]
      have := Nat.div_mul_le_self 1 preset.SLOTS_PER_EPOCH.toNat
      simp only [UInt64.toNat_one] at this ⊢
      omega
    have product : Uint64.mulChecked (1 / preset.SLOTS_PER_EPOCH) preset.SLOTS_PER_EPOCH =
        .ok (1 / preset.SLOTS_PER_EPOCH * preset.SLOTS_PER_EPOCH) :=
      Uint64.mulChecked_ok_iff.mpr ⟨small, by
        rw [UInt64.toNat_mul]
        exact Nat.mod_eq_of_lt small⟩
    exact ⟨_, by simp [isStartSlotAtEpoch, computeSlotsSinceEpochStart, computeStartSlotAtEpoch,
      computeEpochAtSlot, product, bind, Except.bind, pure, Except.pure, Except.mapError]; rfl⟩
  have safe : ∀ fcr : FastConfirmationStore,
      fcr.currentEpochObservedJustifiedCheckpoint = ⟨0, anchorRoot⟩ →
      store.isConfirmedChainSafe config fcr anchorRoot anchorRoot = .ok true := by
    intro fcr observed
    simp [Store.isConfirmedChainSafe, observed, checkpoint, epoch, roots, Uint64.addChecked,
      bind, Except.bind, pure, Except.pure, Except.mapError]
  have descendant : ∀ fcr : FastConfirmationStore,
      store.findLatestConfirmedDescendant config fcr anchorRoot anchorRoot = .ok anchorRoot := by
    intro fcr
    simp [Store.findLatestConfirmedDescendant, epoch, current, startZero, blockEpoch, roots,
      Uint64.addChecked, bind, Except.bind, pure, Except.pure, Except.mapError]
  have latest : ∀ fcr : FastConfirmationStore, fcr.confirmedRoot = anchorRoot →
      fcr.currentEpochObservedJustifiedCheckpoint = ⟨0, anchorRoot⟩ →
      store.getLatestConfirmed config fcr anchorRoot = .ok anchorRoot := by
    intro fcr confirmed observed
    simp [Store.getLatestConfirmed, epoch, current, confirmed, observed, blockEpoch, isAncestor,
      startZero, safe fcr observed, blockOk, blockZero, justification, descendant,
      computeEpochAtSlot, Uint64.addChecked, bind, Except.bind, pure, Except.pure,
      Except.mapError]
  obtain ⟨next, nextOk⟩ := startOne
  cases next <;>
    simp [Store.onFastConfirmation, head, Store.updateFastConfirmationVariables, current,
      Uint64.addChecked, nextOk, startZero, getFastConfirmationStore, finalized, unrealized,
      latest, bind, Except.bind, pure, Except.pure, Except.mapError]

section Lift

variable {ν μ : Type*}

/-- A world of the fork choice, with the store of the rule and the slot of each last run. -/
private def liftWorld (extra : ν → FastConfirmationStore × Option Slot)
    (w : World ν μ (Store preset fork)) : World ν μ (ConfirmingState preset fork) :=
  ⟨w.time, w.sent, w.view, fun u => ⟨w.state u, (extra u).1, (extra u).2⟩⟩

/-- An event of the fork choice, where a move keeps the store of the rule and the last run. -/
private def liftEvent (extra : ν → FastConfirmationStore × Option Slot) :
    Event ν μ (Store preset fork) → Event ν μ (ConfirmingState preset fork)
  | .wait time => .wait time
  | .send sender message => .send sender message
  | .deliver received => .deliver received
  | .move validator state => .move validator ⟨state, (extra validator).1, (extra validator).2⟩

/-- A first event, then the events of the fork choice with the extra fields. -/
private def liftEvents (extra : ν → FastConfirmationStore × Option Slot)
    (first : Event ν μ (ConfirmingState preset fork)) (events : ℕ → Event ν μ (Store preset fork)) :
    ℕ → Event ν μ (ConfirmingState preset fork)
  | 0 => first
  | n + 1 => liftEvent extra (events n)

variable [DecidableEq ν]

/-- An event with the extra fields changes the world with them as the event changes the world. -/
private theorem liftWorld_apply (extra : ν → FastConfirmationStore × Option Slot)
    (w : World ν μ (Store preset fork)) (event : Event ν μ (Store preset fork)) :
    (liftWorld extra w).apply (liftEvent extra event) = liftWorld extra (w.apply event) := by
  cases event with
  | move validator state =>
    simp only [liftWorld, liftEvent, World.apply, World.mk.injEq, true_and]
    funext u
    by_cases here : u = validator
    · subst here
      simp
    · simp [Function.update_of_ne here]
  | _ => rfl

/-- After the first event, each world is the world of the fork choice with the extra fields. -/
private theorem worldAt_liftEvents (extra : ν → FastConfirmationStore × Option Slot)
    (init : World ν μ (ConfirmingState preset fork))
    (first : Event ν μ (ConfirmingState preset fork))
    (init₀ : World ν μ (Store preset fork)) (events : ℕ → Event ν μ (Store preset fork))
    (base : init.apply first = liftWorld extra init₀) (n : ℕ) :
    worldAt init (liftEvents extra first events) (n + 1) =
      liftWorld extra (worldAt init₀ events n) := by
  induction n with
  | zero => exact base
  | succ n ih =>
    rw [worldAt, ih]
    exact liftWorld_apply extra _ (events n)

end Lift

/-- An allowed event of the fork choice stays allowed with the extra fields. -/
private theorem allowed_liftEvent {extra : ValidatorIndex → FastConfirmationStore × Option Slot}
    {w : World ValidatorIndex (Message preset fork) (Store preset fork)}
    {event : Event ValidatorIndex (Message preset fork) (Store preset fork)}
    (allowed : Allowed (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J w event) :
    Allowed (honestConfirming config checks sources genesisTimeMs anchorState anchorBlock
      assignment) J (liftWorld extra w) (liftEvent extra event) := by
  cases event with
  | move u state => exact ⟨allowed.1, .handles allowed.2⟩
  | _ => exact allowed

/-- A vote of a duty stays one in another execution, at an event with the same world and event. -/
private theorem VoteAt.transfer
    {e e' : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J} {v : ValidatorIndex} {slot : Slot} {committeeIndex : CommitteeIndex}
    {time n m : ℕ} {attestation : Attestation preset fork}
    {indexed : IndexedAttestation preset fork}
    (vote : VoteAt e v slot committeeIndex time n attestation indexed)
    (world : e'.world m = e.world n) (event : e'.events m = e.events n) :
    VoteAt e' v slot committeeIndex time m attestation indexed := by
  obtain ⟨sends, atTime, genesis, upToDate, honestData, reads, alone⟩ := vote
  refine ⟨event.trans sends, ?_, ?_, ?_, ?_, ?_, alone⟩ <;> rw [world] <;> assumption

/-- Honest validators that vote and run the rule have an execution, with one honest validator.

The hypotheses are those of the execution where the validator only votes.

The validator runs the rule at the start of slot zero, then votes at the deadline of that slot.

Its store of the rule starts from the finalized checkpoint of its store of the fork choice.

The execution is synchronous for every positive delay.

The validator does its duty to vote, and its duty to run the rule for the set of only slot zero.

Its store of the fork choice stays reachable from the anchor. -/
theorem exists_votes_and_confirmations_execution {store : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok store)
    (stateZero : anchorState.slot = 0) (blockZero : anchorBlock.slot = 0)
    (before : fork < .pectra)
    (parent : ∀ root, SszType.hashTreeRoot anchorBlock = .ok root → anchorBlock.parentRoot ≠ root)
    {committee : Array ValidatorIndex}
    (committeeOk : getBeaconCommittee anchorState 0 0 = .ok committee) {v : ValidatorIndex}
    (first : committee[0]? = some v) (small : committee.size ≤ maxAttesters preset fork)
    (slots : 0 < config.SLOT_DURATION_MS) {due : UInt64}
    (dueOk : getAttestationDueMs config fork = .ok due) (inSlot : due < config.SLOT_DURATION_MS)
    (fits : store.genesisTimeMs.toNat + due.toNat < 2 ^ 64) {Δ : ℕ} (positive : 0 < Δ) :
    ∃ e : Execution (honestConfirming config .acceptAll sources store.genesisTimeMs anchorState
        anchorBlock (Assignment.single v 0 0)) {v},
      e.startTime = store.timeMs.toNat ∧
      e.start = (fun _ => ⟨store, getFastConfirmationStore store, none⟩) ∧
      (∀ u, (e.start u).Initial) ∧
      Votes 0 e.toForkChoice ∧ Confirms {0} 0 e ∧ e.Synchronous Δ ∧
      ∀ n, Store.Reachable config anchorState anchorBlock ((e.world n).state v).store := by
  obtain ⟨e₀, startTime₀, start₀, -, votes₀, ⟨-, unbounded₀, deliver₀⟩, reachable₀⟩ :=
    exists_votes_execution (sources := sources) anchored stateZero blockZero before parent
      committeeOk first small slots dueOk inSlot fits positive
  obtain ⟨fcr, confirmed⟩ := onFastConfirmation_anchor anchored stateZero blockZero
    (Nat.lt_trans before (by decide)) parent slots
  -- The anchor sits at slot zero, so the clock of the store starts at genesis.
  have clock : store.timeMs = store.genesisTimeMs := by
    have timeOk := (getForkchoiceStore_timeMs anchored).2
    have bounded := UInt64.toNat_lt store.genesisTimeMs
    simp [stateZero, computeTimeAtSlotMs, Uint64.mulChecked, Uint64.addChecked, bind,
      Except.bind, bounded] at timeOk
    exact timeOk.symm
  have startSlot : store.getCurrentSlot config = .ok 0 :=
    stateZero ▸ getCurrentSlot_getForkchoiceStore slots anchored
  have slotStart : IsSlotStart config store.genesisTimeMs 0 store.timeMs.toNat := by
    refine ⟨store.genesisTimeMs, ?_, by rw [clock]⟩
    have bounded := UInt64.toNat_lt store.genesisTimeMs
    simp [computeTimeAtSlotMs, Uint64.mulChecked, Uint64.addChecked, bind, Except.bind, bounded]
  have upToDate : UpToDate config .acceptAll sources store.timeMs.toNat ∅ store := by
    refine ⟨rfl, fun after handles => ?_⟩
    cases handles with
    | tick _ _ ticks =>
      rw [Nat.toUInt64_eq, UInt64.ofNat_toNat, onTick_timeMs startSlot] at ticks
      exact (Except.ok.inj ticks).symm
    | _ => simp_all
  -- The validator runs the rule first, then follows the execution where it only votes.
  let extra : ValidatorIndex → FastConfirmationStore × Option Slot :=
    fun u => if u = v then (fcr, some 0) else (getFastConfirmationStore store, none)
  let run : Event ValidatorIndex (Message preset fork) (ConfirmingState preset fork) :=
    .move v ⟨store, fcr, some 0⟩
  let init : World ValidatorIndex (Message preset fork) (ConfirmingState preset fork) :=
    World.initial store.timeMs.toNat fun _ => ⟨store, getFastConfirmationStore store, none⟩
  have base : init.apply run = liftWorld extra (e₀.world 0) := by
    rw [Execution.world_zero, startTime₀, start₀]
    simp only [init, run, extra, World.initial, World.apply, liftWorld, World.mk.injEq,
      true_and]
    funext u
    by_cases here : u = v
    · subst here
      simp
    · simp [here]
  have lifted : ∀ n, worldAt init (liftEvents extra run e₀.events) (n + 1) =
      liftWorld extra (e₀.world n) :=
    worldAt_liftEvents extra init run _ e₀.events base
  let e : Execution (honestConfirming config .acceptAll sources store.genesisTimeMs anchorState
      anchorBlock (Assignment.single v 0 0)) {v} :=
    { startTime := store.timeMs.toNat
      start := fun _ => ⟨store, getFastConfirmationStore store, none⟩
      events := liftEvents extra run e₀.events
      allowed := fun n => by
        match n with
        | 0 => exact ⟨Set.mem_singleton v, .confirms slotStart (fun _ none => by cases none) rfl
            upToDate startSlot confirmed⟩
        | n + 1 =>
          rw [lifted n]
          exact allowed_liftEvent (e₀.allowed_world n) }
  have world : ∀ n, e.world (n + 1) = liftWorld extra (e₀.world n) := lifted
  refine ⟨e, rfl, rfl, fun _ => ⟨rfl, rfl⟩, ?_, ?_, ⟨positive, fun T => ?_, ?_⟩, fun n => ?_⟩
  · -- Each vote of the execution where the validator only votes comes one event later.
    intro u honest slot committeeIndex time assigned deadline started stable
    obtain ⟨n, attestation, indexed, vote⟩ := votes₀ u honest slot committeeIndex time assigned
      deadline (by rw [startTime₀]; exact started) stable
    refine ⟨n + 1, attestation, indexed, vote.transfer ?_ ?_⟩
    · rw [Execution.toForkChoice_world, world]
      rfl
    · show storeEvent _ (liftEvent extra (e₀.events n)) = _
      rw [vote.sends]
      rfl
  · -- The only slot is slot zero, and the first event runs the rule at its start.
    rintro u honest slot rfl time - - -
    rw [Set.mem_singleton_iff] at honest
    subst honest
    exact ⟨0, fcr, rfl, slotStart, (fun _ none => by cases none), rfl, upToDate, startSlot,
      confirmed⟩
  · obtain ⟨n, late⟩ := unbounded₀ T
    exact ⟨n + 1, by rw [world]; exact late⟩
  · intro n k le u honest w receiver m member late
    cases n with
    | zero => exact absurd member (Set.notMem_empty m)
    | succ n =>
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [world] at member late ⊢
      exact deliver₀ n k (by omega) u honest w receiver m member late
  · cases n with
    | zero => exact .anchor anchored
    | succ n =>
      rw [world]
      exact reachable₀ n

end EthLib.Consensus.Models.Network
