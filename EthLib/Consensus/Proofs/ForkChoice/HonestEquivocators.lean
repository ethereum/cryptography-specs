module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Sets
public import EthLib.Consensus.Proofs.ForkChoice.HonestDuties

/-!
# Proofs: no honest store knows an honest validator as an equivocator

The model is that of the fast confirmation paper, [arXiv 2405.00549v4][fcr].

Its §3.1 assumes that an honest validator never commits a slashable offence.

The network model of this library derives that from the duty of the honest validator.

A statement of an honest validator in a sent message first came from that validator itself.

So it sits in a message of its own view, which only grows.

Before a new vote, the validator checks it against each vote of its own in that view.

Two votes that it may sign at one time are equal, when slots last a positive time.

So no two votes of an honest validator in sent messages can be slashed together.

A store adds a validator to its equivocators only from an attester slashing that it accepts.

That slashing holds two votes of the validator, which can be slashed together.

It comes as a message or inside a block, and in both cases from the view of the store.

So no honest store lists an honest validator among its equivocators.

The store-level form of Lemmas 4 and 3 assumes as much, and an honest execution discharges it.

[fcr]: https://arxiv.org/abs/2405.00549v4
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Models Models.ForkChoice

variable {preset : Preset} {fork : Fork} {config : Config}

namespace Store

variable {store after : Store preset fork} {checks : SignatureChecks}
  {sources : BlockSources preset fork}

/-! ## The handlers that keep the equivocators -/

/-- Moving the checkpoints keeps the equivocators. -/
private theorem updateCheckpoints_equivocatingIndices (justified finalized : Checkpoint) :
    (store.updateCheckpoints justified finalized).equivocatingIndices =
      store.equivocatingIndices := by
  unfold updateCheckpoints
  by_cases j : store.justifiedCheckpoint.epoch < justified.epoch <;>
    by_cases f : store.finalizedCheckpoint.epoch < finalized.epoch <;> simp [j, f]

/-- Moving the unrealized checkpoints keeps the equivocators. -/
private theorem updateUnrealizedCheckpoints_equivocatingIndices {s : Store preset fork}
    (justified finalized : Checkpoint) :
    (s.updateUnrealizedCheckpoints justified finalized).equivocatingIndices =
      s.equivocatingIndices := by
  unfold updateUnrealizedCheckpoints
  by_cases j : s.unrealizedJustifiedCheckpoint.epoch < justified.epoch <;>
    by_cases f : s.unrealizedFinalizedCheckpoint.epoch < finalized.epoch <;> simp [j, f]

/-- Pulling up the tip keeps the equivocators. -/
private theorem computePulledUpTip_equivocatingIndices {root : Root}
    (pulled : store.computePulledUpTip config root = .ok after) :
    after.equivocatingIndices = store.equivocatingIndices := by
  unfold computePulledUpTip at pulled
  simp only [bind_ok_iff] at pulled
  obtain ⟨state, -, pulledState, -, block, -, epoch, -, pulled⟩ := pulled
  split at pulled <;> simp only [pure, Except.pure, Except.ok.injEq] at pulled <;> subst pulled
  · rw [updateCheckpoints_equivocatingIndices, updateUnrealizedCheckpoints_equivocatingIndices]
  · rw [updateUnrealizedCheckpoints_equivocatingIndices]

/-- A tick within a slot keeps the equivocators. -/
private theorem onTickPerSlot_equivocatingIndices {timeMs : UInt64}
    (ticked : store.onTickPerSlot config timeMs = .ok after) :
    after.equivocatingIndices = store.equivocatingIndices := by
  unfold onTickPerSlot at ticked
  simp only [bind_ok_iff] at ticked
  obtain ⟨previous, -, current, -, ticked⟩ := ticked
  split at ticked <;>
    · obtain ⟨_, _, ticked⟩ := ticked
      split at ticked <;> simp only [pure, Except.pure, Except.ok.injEq] at ticked <;>
        subst ticked <;> simp [updateCheckpoints_equivocatingIndices]

/-- The catch-up loop keeps the equivocators. -/
private theorem catchUp_equivocatingIndices {tickSlot : Slot} {start : Store preset fork}
    (caught : catchUp config start tickSlot = .ok after) :
    after.equivocatingIndices = start.equivocatingIndices := by
  induction start using catchUp.induct config tickSlot with
  | _ start ih =>
    rw [catchUp.eq_1] at caught
    simp only [bind_ok_iff] at caught
    obtain ⟨current, -, caught⟩ := caught
    split at caught
    · simp only [bind_ok_iff] at caught
      obtain ⟨next, -, nextTimeMs, -, ticked, tick, caught⟩ := caught
      split at caught
      · exact (ih ticked ‹_› caught).trans (onTickPerSlot_equivocatingIndices tick)
      · cases caught
    · simp only [pure, Except.pure, Except.ok.injEq] at caught
      subst caught
      rfl

/-- Recording the timeliness of a block keeps the equivocators. -/
private theorem recordBlockTimeliness_equivocatingIndices {s s' : Store preset fork} {root : Root}
    (recorded : s.recordBlockTimeliness config root = .ok s') :
    s'.equivocatingIndices = s.equivocatingIndices := by
  unfold recordBlockTimeliness at recorded
  simp only [bind_ok_iff, pure, Except.pure] at recorded
  obtain ⟨_, _, _, _, _, _, _, _, recorded⟩ := recorded
  split at recorded
  · simp only [bind_ok_iff, Except.ok.injEq] at recorded
    obtain ⟨_, _, rfl⟩ := recorded
    rfl
  · cases recorded
    rfl

/-- Updating the boost keeps the equivocators. -/
private theorem updateProposerBoostRoot_equivocatingIndices {s s' : Store preset fork}
    {head root : Root} (updated : s.updateProposerBoostRoot config head root = .ok s') :
    s'.equivocatingIndices = s.equivocatingIndices := by
  unfold updateProposerBoostRoot at updated
  split at updated
  rotate_left
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at updated
  simp only [bind_ok_iff, pure_bind] at updated
  obtain ⟨_, _, _, _, _, _, updated⟩ := updated
  split at updated <;> simp only [pure, Except.pure, Except.ok.injEq] at updated <;>
    subst updated <;> rfl

/-- Storing the state of a target keeps the equivocators. -/
private theorem storeTargetCheckpointState_equivocatingIndices {s s' : Store preset fork}
    {target : Checkpoint}
    (stored : s.storeTargetCheckpointState config checks target = .ok s') :
    s'.equivocatingIndices = s.equivocatingIndices := by
  unfold storeTargetCheckpointState at stored
  split at stored
  · simp only [pure, Except.pure, Except.ok.injEq] at stored
    subst stored
    rfl
  · simp only [bind_ok_iff] at stored
    obtain ⟨_, _, stored⟩ := stored
    simp only [pure, Except.pure, Except.ok.injEq] at stored
    subst stored
    rfl

/-- A tick keeps the equivocators. -/
theorem onTick_equivocatingIndices {timeMs : UInt64}
    (ticked : store.onTick config timeMs = .ok after) :
    after.equivocatingIndices = store.equivocatingIndices := by
  unfold onTick at ticked
  simp only [bind_ok_iff] at ticked
  obtain ⟨tickSlot, -, caught, caughtUp, ticked⟩ := ticked
  exact (onTickPerSlot_equivocatingIndices ticked).trans (catchUp_equivocatingIndices caughtUp)

/-- A block, without its votes, keeps the equivocators. -/
theorem onBlock_equivocatingIndices {signed : SignedBeaconBlock preset fork}
    (added : store.onBlock config checks sources signed = .ok after) :
    after.equivocatingIndices = store.equivocatingIndices := by
  cases root : SszType.hashTreeRoot signed.message with
  | error e => simp [onBlock, root, bind, Except.bind, Except.mapError] at added
  | ok blockRoot =>
    by_cases known : store.blocks.contains blockRoot
    · rw [onBlock_known root known] at added
      cases added
      rfl
    simp only [onBlock, root, known, bind, Except.bind, Except.mapError, ↓reduceIte,
      Bool.false_eq_true] at added
    unfold addBlock at added
    simp only [bind_ok_iff] at added
    obtain ⟨state, valid, head, -, voted, vote, recorded, record, boosted, boost, added⟩ := added
    obtain ⟨_, _, rfl⟩ := recordBlockPtcVotes_onlyPtcVotes vote
    rw [computePulledUpTip_equivocatingIndices added, updateCheckpoints_equivocatingIndices,
      updateProposerBoostRoot_equivocatingIndices boost,
      recordBlockTimeliness_equivocatingIndices record]

/-- An attestation keeps the equivocators. -/
theorem onAttestation_equivocatingIndices {attestation : Attestation preset fork}
    {isFromBlock : Bool}
    (attested : store.onAttestation config checks attestation isFromBlock = .ok after) :
    after.equivocatingIndices = store.equivocatingIndices := by
  unfold onAttestation at attested
  simp only [bind_ok_iff] at attested
  obtain ⟨_, _, stored, storing, _, _, _, _, _, _, valid, _, attested⟩ := attested
  have first := storeTargetCheckpointState_equivocatingIndices storing
  split at attested
  · simp only [pure, Except.pure, Except.ok.injEq] at attested
    subst attested
    exact first
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at attested

/-- From Gloas, a vote of the payload committee keeps the equivocators. -/
theorem onPayloadAttestationMessage_equivocatingIndices {gloas : .glamsterdam ≤ fork}
    {message : PayloadAttestationMessage} {isFromBlock : Bool}
    (voted : store.onPayloadAttestationMessage config checks gloas message isFromBlock =
      .ok after) :
    after.equivocatingIndices = store.equivocatingIndices := by
  obtain ⟨_, _, rfl⟩ := onPayloadAttestationMessage_onlyPtcVotes voted
  rfl

/-- From Gloas, an envelope keeps the equivocators. -/
theorem onExecutionPayloadEnvelope_equivocatingIndices {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadEnvelope preset fork}
    (accepted : store.onExecutionPayloadEnvelope config checks sources gloas signed = .ok after) :
    after.equivocatingIndices = store.equivocatingIndices := by
  obtain ⟨_, _, _, _, _, record, rfl⟩ := onExecutionPayloadEnvelope_ok accepted
  obtain ⟨_, rfl⟩ := recordEnvelope_frame record
  rfl

/-- From Heze, an inclusion list keeps the equivocators. -/
theorem onInclusionList_equivocatingIndices {heze : .hegota ≤ fork} {signed : SignedInclusionList}
    (accepted : store.onInclusionList config checks heze signed = .ok after) :
    after.equivocatingIndices = store.equivocatingIndices := by
  obtain ⟨_, _, rfl⟩ := onInclusionList_ok heze accepted
  rfl

/-- A block with its votes adds an equivocator only from one of its attester slashings.

That slashing holds the validator in both of its votes, and those votes can be slashed together. -/
theorem mem_equivocatingIndices_of_onBlockWithVotes {signed : SignedBeaconBlock preset fork}
    {i : ValidatorIndex}
    (added : store.onBlockWithVotes config checks sources signed = .ok after)
    (member : i ∈ after.equivocatingIndices) :
    i ∈ store.equivocatingIndices ∨
      ∃ slashing ∈ signed.message.body.attesterSlashings.data,
        isSlashableAttestationData slashing.attestation1.data slashing.attestation2.data = true ∧
        i ∈ slashing.attestation1.attestingIndices.data ∧
        i ∈ slashing.attestation2.attestingIndices.data := by
  unfold onBlockWithVotes at added
  simp only [bind_ok_iff, ← Array.foldlM_toList] at added
  obtain ⟨blocked, blockOk, voted, attested, slashed⟩ := added
  have votes : voted.equivocatingIndices = store.equivocatingIndices :=
    foldlM_ok_invariant (fun s : Store preset fork => s.equivocatingIndices =
      store.equivocatingIndices) (fun _ _ _ held step =>
        (onAttestation_equivocatingIndices step).trans held)
      (onBlock_equivocatingIndices blockOk) attested
  refine foldlM_ok_invariant_of_mem (fun s : Store preset fork => ∀ i ∈ s.equivocatingIndices,
      i ∈ store.equivocatingIndices ∨
      ∃ slashing ∈ signed.message.body.attesterSlashings.data,
        isSlashableAttestationData slashing.attestation1.data slashing.attestation2.data = true ∧
        i ∈ slashing.attestation1.attestingIndices.data ∧
        i ∈ slashing.attestation2.attestingIndices.data)
    (fun s slashing s' mem held step j member' => ?_) (fun j member' => .inl (votes ▸ member'))
    slashed i member
  rcases (mem_equivocatingIndices_of_onAttesterSlashing step).mp member' with old | ⟨one, two⟩
  · exact held j old
  · exact .inr ⟨slashing, Array.mem_toList_iff.mp mem,
      (onAttesterSlashing_eq_ok_iff.mp step).1, one, two⟩

/-- A store built from an anchor knows no equivocator. -/
theorem getForkchoiceStore_equivocatingIndices {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}
    (made : getForkchoiceStore config anchorState anchorBlock = .ok store) :
    store.equivocatingIndices = [] := by
  unfold getForkchoiceStore at made
  cases stateRoot : SszType.hashTreeRoot anchorState with
  | error e => simp [stateRoot, bind, Except.bind, Except.mapError] at made
  | ok stateRoot' =>
    simp only [stateRoot, Except.mapError, bind, Except.bind] at made
    split at made
    · simp [throw, throwThe, MonadExceptOf.throw] at made
    · cases blockRoot : SszType.hashTreeRoot anchorBlock with
      | error e => simp [blockRoot] at made
      | ok anchorRoot =>
        simp only [blockRoot] at made
        cases time : computeTimeAtSlotMs config (secondsToMilliseconds anchorState.genesisTime)
            anchorState.slot with
        | error e => simp [time] at made
        | ok timeMs =>
          simp only [time, pure, Except.pure, Except.ok.injEq] at made
          subst made
          rfl

end Store

namespace Models.Network

variable {checks : SignatureChecks} {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64}

/-- Two slots that start at one time are equal, when slots last a positive time. -/
private theorem slot_eq_of_computeTimeAtSlotMs (slots : 0 < config.SLOT_DURATION_MS)
    {genesis first second : UInt64} {start₁ start₂ : UInt64}
    (firstOk : computeTimeAtSlotMs config genesis first = .ok start₁)
    (secondOk : computeTimeAtSlotMs config genesis second = .ok start₂)
    (same : start₁.toNat = start₂.toNat) : first = second := by
  simp only [computeTimeAtSlotMs, bind_ok_iff] at firstOk secondOk
  obtain ⟨p₁, mul₁, add₁⟩ := firstOk
  obtain ⟨p₂, mul₂, add₂⟩ := secondOk
  obtain ⟨-, mul₁⟩ := mulChecked_ok_iff.mp mul₁
  obtain ⟨-, mul₂⟩ := mulChecked_ok_iff.mp mul₂
  obtain ⟨-, add₁⟩ := addChecked_ok_iff.mp add₁
  obtain ⟨-, add₂⟩ := addChecked_ok_iff.mp add₂
  have positive : 0 < config.SLOT_DURATION_MS.toNat := UInt64.lt_iff_toNat_lt.mp slots
  apply UInt64.toNat_inj.mp
  apply Nat.eq_of_mul_eq_mul_right positive
  omega

/-- The data of an honest vote is unique for a store, a slot and a committee. -/
private theorem HonestVoteData.eq {store : Store preset fork} {slot : Slot}
    {committeeIndex : CommitteeIndex} {first second : AttestationData}
    (isFirst : HonestVoteData config checks store slot committeeIndex first)
    (isSecond : HonestVoteData config checks store slot committeeIndex second) :
    first = second := by
  obtain ⟨head, block, headState, state, headOk, blockOk, headStateOk, stateOk, dataOk⟩ := isFirst
  obtain ⟨head', block', headState', state', headOk', blockOk', headStateOk', stateOk', dataOk'⟩ :=
    isSecond
  rw [headOk] at headOk'
  cases headOk'
  rw [blockOk] at blockOk'
  cases blockOk'
  rw [headStateOk] at headStateOk'
  cases headStateOk'
  rw [stateOk] at stateOk'
  cases stateOk'
  rw [dataOk] at dataOk'
  cases dataOk'
  rfl

/-- An honest validator may sign only one vote at a time, when slots last a positive time.

Each vote has that time as the attestation deadline of its slot, so both votes share a slot.

The assignment then fixes the committee, and the data is the honest vote of the store there. -/
theorem MaySign.eq (slots : 0 < config.SLOT_DURATION_MS) {v : ValidatorIndex} {time : ℕ}
    {view : Set (Message preset fork)} {store : Store preset fork} {first second : AttestationData}
    (signsFirst : MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
      time view store first)
    (signsSecond : MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
      time view store second) :
    first = second := by
  obtain ⟨index₁, assigned₁, ⟨start₁, due₁, startOk₁, dueOk₁, time₁⟩, -, -, data₁, -⟩ := signsFirst
  obtain ⟨index₂, assigned₂, ⟨start₂, due₂, startOk₂, dueOk₂, time₂⟩, -, -, data₂, -⟩ :=
    signsSecond
  rw [dueOk₁] at dueOk₂
  cases dueOk₂
  have slot : first.slot = second.slot :=
    slot_eq_of_computeTimeAtSlotMs slots startOk₁ startOk₂ (by omega)
  rw [slot, assigned₂] at assigned₁
  cases assigned₁
  exact HonestVoteData.eq (slot ▸ data₁) data₂

/-- A move of a store adds an equivocator only from two votes in one message of the view.

Both votes are statements of that message for the validator, and they can be slashed together. -/
theorem Handles.mem_equivocatingIndices {time : ℕ} {view : Set (Message preset fork)}
    {store after : Store preset fork} {i : ValidatorIndex}
    (handles : Handles config checks sources time view store after)
    (member : i ∈ after.equivocatingIndices) :
    i ∈ store.equivocatingIndices ∨
      ∃ m ∈ view, ∃ first second, (i, first) ∈ statements config checks anchorState anchorBlock m ∧
        (i, second) ∈ statements config checks anchorState anchorBlock m ∧
        isSlashableAttestationData first second = true := by
  cases handles with
  | tick _ _ ticked => exact .inl (Store.onTick_equivocatingIndices ticked ▸ member)
  | block mem added =>
    rcases Store.mem_equivocatingIndices_of_onBlockWithVotes added member with old |
      ⟨slashing, carried, slashable, one, two⟩
    · exact .inl old
    · exact .inr ⟨_, mem, slashing.attestation1.data, slashing.attestation2.data,
        .inr ⟨slashing, carried, .inl ⟨one, rfl⟩⟩, .inr ⟨slashing, carried, .inr ⟨two, rfl⟩⟩,
        slashable⟩
  | attestation _ attested =>
    exact .inl (Store.onAttestation_equivocatingIndices attested ▸ member)
  | attesterSlashing mem slashed =>
    rcases (Store.mem_equivocatingIndices_of_onAttesterSlashing slashed).mp member with old |
      ⟨one, two⟩
    · exact .inl old
    · exact .inr ⟨_, mem, _, _, .inl ⟨one, rfl⟩, .inr ⟨two, rfl⟩,
        (Store.onAttesterSlashing_eq_ok_iff.mp slashed).1⟩
  | payloadAttestation _ voted =>
    exact .inl (Store.onPayloadAttestationMessage_equivocatingIndices voted ▸ member)
  | envelope _ accepted =>
    exact .inl (Store.onExecutionPayloadEnvelope_equivocatingIndices accepted ▸ member)
  | inclusionList _ accepted =>
    exact .inl (Store.onInclusionList_equivocatingIndices accepted ▸ member)

variable {J : Set ValidatorIndex}
  (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J)

/-- A newly sent statement of an honest validator was sent before, or the validator may sign it. -/
private theorem Execution.sent_or_maySign (n : ℕ) {v : ValidatorIndex} (honest : v ∈ J)
    {m : Message preset fork} (sent : m ∈ (e.world (n + 1)).sent) {d : AttestationData}
    (signs : (v, d) ∈ statements config checks anchorState anchorBlock m) :
    (∃ m' ∈ (e.world n).sent, (v, d) ∈ statements config checks anchorState anchorBlock m') ∨
      MaySign config checks sources anchorState anchorBlock assignment genesisTimeMs v
        (e.world n).time ((e.world n).view v) ((e.world n).state v) d := by
  have allowed := e.allowed_world n
  rw [Execution.world_succ] at sent
  cases events : e.events n with
  | send sender message =>
    rw [events] at allowed sent
    rcases sent with rfl | before
    · by_cases same : sender = v
      · subst same
        rcases allowed.2 honest (sender, d) signs rfl with ⟨m', member, has⟩ | may
        · exact .inl ⟨m', e.view_subset_sent n sender member, has⟩
        · exact .inr may
      · exact .inl (allowed.1 (v, d) signs honest (Ne.symm same))
    · exact .inl ⟨m, before, signs⟩
  | _ =>
    rw [events] at sent
    exact .inl ⟨m, sent, signs⟩

/-- No two votes of an honest validator in sent messages can be slashed together.

Slots must last a positive time. -/
theorem Execution.isSlashableAttestationData_honest (slots : 0 < config.SLOT_DURATION_MS)
    (n : ℕ) {v : ValidatorIndex} (honest : v ∈ J) {m₁ m₂ : Message preset fork}
    (sent₁ : m₁ ∈ (e.world n).sent) (sent₂ : m₂ ∈ (e.world n).sent) {d₁ d₂ : AttestationData}
    (signs₁ : (v, d₁) ∈ statements config checks anchorState anchorBlock m₁)
    (signs₂ : (v, d₂) ∈ statements config checks anchorState anchorBlock m₂) :
    isSlashableAttestationData d₁ d₂ = false := by
  -- A vote of the validator in a sent message.
  let Sent : ℕ → AttestationData → Prop := fun n d =>
    ∃ m ∈ (e.world n).sent, (v, d) ∈ statements config checks anchorState anchorBlock m
  suffices all : ∀ n d₁ d₂, Sent n d₁ → Sent n d₂ → isSlashableAttestationData d₁ d₂ = false from
    all n d₁ d₂ ⟨m₁, sent₁, signs₁⟩ ⟨m₂, sent₂, signs₂⟩
  intro n
  induction n with
  | zero =>
    rintro d₁ - ⟨m, sent, -⟩ -
    simp [Execution.world_zero, World.initial] at sent
  | succ n ih =>
    rintro d₁ d₂ ⟨m₁, sent₁, signs₁⟩ ⟨m₂, sent₂, signs₂⟩
    -- A vote sent before is in a message of the view of the validator.
    have inView : ∀ d, Sent n d → ∃ m ∈ (e.world n).view v,
        (v, d) ∈ statements config checks anchorState anchorBlock m :=
      fun d ⟨m, sent, signs⟩ => e.signed_mem_view n honest sent signs rfl
    rcases e.sent_or_maySign n honest sent₁ signs₁ with old₁ | new₁ <;>
      rcases e.sent_or_maySign n honest sent₂ signs₂ with old₂ | new₂
    · exact ih d₁ d₂ old₁ old₂
    · obtain ⟨m, member, has⟩ := inView d₁ old₁
      exact (new₂.choose_spec.2.2.2.2.2 m member _ has rfl).1
    · obtain ⟨m, member, has⟩ := inView d₂ old₂
      exact (new₁.choose_spec.2.2.2.2.2 m member _ has rfl).2
    · rw [MaySign.eq slots new₁ new₂]
      exact isSlashableAttestationData_self d₂

/-- No honest store lists an honest validator among its known equivocators.

The honest stores must list no honest equivocator at the start, and slots must last a positive time.
-/
theorem Execution.equivocatingIndices_honest (slots : 0 < config.SLOT_DURATION_MS)
    (start : ∀ u ∈ J, ∀ v ∈ (e.start u).equivocatingIndices, v ∉ J) (n : ℕ) {u : ValidatorIndex}
    (receiver : u ∈ J) : ∀ v ∈ ((e.world n).state u).equivocatingIndices, v ∉ J := by
  induction n with
  | zero => exact start u receiver
  | succ n ih =>
    intro v member honest
    rcases e.state_succ n u with same | ⟨-, moved⟩
    · rw [same] at member
      exact ih v member honest
    · rcases Handles.mem_equivocatingIndices (anchorState := anchorState)
        (anchorBlock := anchorBlock) moved member with
        old | ⟨m, mem, first, second, one, two, slash⟩
      · exact ih v old honest
      · have sent := e.view_subset_sent n u mem
        rw [e.isSlashableAttestationData_honest slots n honest sent sent one two] at slash
        exact Bool.false_ne_true slash

variable [DecidablePred (· ∈ J)]

/-- Lemmas 4 and 3 of the paper for a block that the store of an honest validator confirms.

The store is that of an honest validator in an execution, so no known equivocator is honest.

The honest stores must list no honest equivocator at the start, and slots must last a positive time.

The other hypotheses are those of the store-level form of the lemmas. -/
theorem Execution.lt_two_mul_honest_supportersOf_of_isOneConfirmed
    (slots : 0 < config.SLOT_DURATION_MS)
    (start : ∀ u ∈ J, ∀ v ∈ (e.start u).equivocatingIndices, v ∉ J) (n : ℕ) {u : ValidatorIndex}
    (receiver : u ∈ J) {head root : Root} {balanceSource : BeaconState preset fork}
    {currentSlot firstSlot lastSlot startSlot : Slot} {block parentBlock : BeaconBlock preset fork}
    {participants : Std.TreeSet ValidatorIndex}
    {proposerScore maximumSupport discount adversary : Gwei}
    (within : balanceSource.RegistryWithinLimit)
    (slotOk : ((e.world n).state u).getCurrentSlot config = .ok currentSlot)
    (blockOk : ((e.world n).state u).block root = .ok block)
    (parentOk : ((e.world n).state u).block block.parentRoot = .ok parentBlock)
    (boostOk : computeProposerScore config balanceSource = .ok proposerScore)
    (firstOk : addChecked parentBlock.slot 1 = .ok firstSlot)
    (lastOk : subChecked currentSlot 1 = .ok lastSlot)
    (maximumOk : ((e.world n).state u).computeCommitteeWeightBetweenSlots head balanceSource
      firstSlot lastSlot = .ok maximumSupport)
    (discountOk : ((e.world n).state u).computeEmptySlotSupportDiscount config head balanceSource
      root = .ok discount)
    (adversaryOk : ((e.world n).state u).getAdversarialWeight config head balanceSource root =
      .ok adversary)
    (rangeOk : ((e.world n).state u).computeAdversarialWeight config head balanceSource startSlot
      lastSlot = .ok adversary)
    (participantsOk : ((e.world n).state u).getCommitteesBetweenSlots head startSlot lastSlot =
      .ok participants)
    (confirmed : ((e.world n).state u).isOneConfirmed config head balanceSource
      (((e.world n).state u).tallyVotes balanceSource) root = .ok true)
    (supportersIn : ∀ v ∈ ((e.world n).state u).supportersOf balanceSource ⟨root, .pending⟩,
      v ∈ participants)
    (aligned : EffectiveBalancesAligned balanceSource)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (byzantine : ByzantineStakeAtMost (fun v => balanceAt balanceSource v.toNat)
      (Store.activeMembers balanceSource participants) J
      config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat 100) :
    maximumSupport.toNat + proposerScore.toNat <
      discount.toNat + 2 * stake (fun v => balanceAt balanceSource v.toNat)
        {v ∈ ((e.world n).state u).supportersOf balanceSource ⟨root, .pending⟩ | v ∈ J} :=
  Store.lt_two_mul_honest_supportersOf_of_isOneConfirmed within slotOk blockOk parentOk boostOk
    firstOk lastOk maximumOk discountOk adversaryOk rangeOk participantsOk confirmed supportersIn
    aligned increment (e.equivocatingIndices_honest slots start n receiver) byzantine

end Models.Network

end EthLib.Consensus
