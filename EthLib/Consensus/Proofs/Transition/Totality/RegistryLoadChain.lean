module

public import EthLib.Consensus.Proofs.Transition.Totality.Inactivity
public import EthLib.Consensus.Proofs.Transition.Totality.RegistryLoadBlock
public import EthLib.Consensus.Proofs.Transition.Totality.RegistryLoadUpgrades
public import EthLib.Consensus.Proofs.Transition.Trace

/-!
# Proofs: along a run, the registry grows by at most the bounds of its blocks

The count of a state is its validators plus its pending deposits, which bound its registry.

A slot never raises that count within a fork.

The upgrade to Electra adds at most the size of the registry, which before Electra is the count.

So the count weighted by two before Electra, and by one from Electra, never rises across a slot.

A block adds at most its bound to the count: its deposits, twice from Electra, plus its requests.

So along a run, the weighted count at the end is at most the weighted count at the start.

The bounds of the blocks of the run, each weighted by the factor of its fork, add to it.

When that sum is within the limit of the registry, the registry at the end is within it too.

The limit is weighted by the fork at the end, as the count is.

A run here is checked: each block has its state root checked, and no upgrade is due at it.

The update of the inactivity scores is restated with the count as its hypothesis.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The weight of the count at a fork: two before Electra, and one from Electra.

Before Electra the count can still double, at the upgrade to Electra. -/
def registryLoadFactor (fork : Fork) : Nat :=
  if fork < .pectra then 2 else 1

/-- The weight of the count is at least one. -/
theorem one_le_registryLoadFactor (fork : Fork) : 1 ≤ registryLoadFactor fork := by
  unfold registryLoadFactor
  split <;> omega

/-- One upgrade never raises the weighted count. -/
theorem upgradeNext_weightedRegistryLoad_le {pre : ForkedBeaconState preset}
    {next : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok next) :
    registryLoadFactor next.val.fork * registryLoad next.val.state ≤
      registryLoadFactor pre.fork * registryLoad pre.state := by
  have bound := upgradeNext_registryLoad_le computed
  have ordered : pre.fork.ctorIdx < next.val.fork.ctorIdx := next.property
  have size : pre.state.validators.data.size ≤ registryLoad pre.state := Nat.le_add_right _ _
  unfold registryLoadFactor
  change registryLoad next.val.state ≤ registryLoad pre.state +
    (if pre.fork.ctorIdx < Fork.pectra.ctorIdx ∧ Fork.pectra.ctorIdx ≤ next.val.fork.ctorIdx
      then pre.state.validators.data.size else 0) at bound
  change (if next.val.fork.ctorIdx < Fork.pectra.ctorIdx then 2 else 1) *
      registryLoad next.val.state ≤
    (if pre.fork.ctorIdx < Fork.pectra.ctorIdx then 2 else 1) * registryLoad pre.state
  split_ifs at bound ⊢ <;> omega

/-- A slot with the upgrades due at it never raises the weighted count. -/
theorem advanceSlotAcross_weightedRegistryLoad_le {forked after : ForkedBeaconState preset}
    (computed : advanceSlotAcross config checks forked = .ok after) :
    registryLoadFactor after.fork * registryLoad after.state ≤
      registryLoadFactor forked.fork * registryLoad forked.state := by
  obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp computed
  -- The slot keeps the fork, and each upgrade lowers the weighted count.
  have upgraded := processUpgrades_induction
    (property := fun state => registryLoadFactor state.fork * registryLoad state.state ≤
      registryLoadFactor forked.fork * registryLoad advanced)
    (fun before stepOk => (upgradeNext_weightedRegistryLoad_le stepOk).trans before)
    (Nat.le_refl _) upgrades
  exact upgraded.trans (Nat.mul_le_mul_left _ (advanceSlot_registryLoad_le slotOk))

/-- The bound of a block weighted by its fork, and zero for a slot. -/
def Step.loadBound {before after : ForkedBeaconState preset} :
    Step config checks before after → Nat
  | .slot _ => 0
  | .block (fork := fork) _ signed _ _ =>
    registryLoadFactor fork * blockLoadBound signed.message.body

/-- The sum over the blocks of a run of the bound of each block, weighted by its fork. -/
def Run.loadBound {first : ForkedBeaconState preset} :
    {last : ForkedBeaconState preset} → Run config checks first last → Nat
  | _, .nil => 0
  | _, .snoc pre step => pre.loadBound + step.loadBound

/-- The bounds of two runs one after the other add up. -/
theorem Run.loadBound_append {first middle last : ForkedBeaconState preset}
    (pre : Run config checks first middle) (tail : Run config checks middle last) :
    (pre.append tail).loadBound = pre.loadBound + tail.loadBound := by
  induction tail with
  | nil => rfl
  | snoc tail step ih =>
    simp only [Run.append, Run.loadBound, ih]
    omega

/-- Along a run, the weighted count rises by at most the weighted bounds of its blocks. -/
theorem Run.registryLoad_le {first last : ForkedBeaconState preset}
    (run : Run config checks first last) :
    registryLoadFactor last.fork * registryLoad last.state ≤
      registryLoadFactor first.fork * registryLoad first.state + run.loadBound := by
  induction run with
  | nil => simp [Run.loadBound]
  | snoc pre step ih =>
    cases step with
    | slot computed =>
      have := advanceSlotAcross_weightedRegistryLoad_le computed
      simp only [Run.loadBound, Step.loadBound] at ih ⊢
      omega
    | @block fork before after engine signed due computed =>
      have bound := applySignedBlock_registryLoad_le (config := config) (checks := checks)
        computed
      have := Nat.mul_le_mul_left (registryLoadFactor fork) bound
      simp only [Run.loadBound, Step.loadBound] at ih ⊢
      rw [Nat.mul_add] at this
      omega

/-- At the end of a run, the count is within a limit that the start and the blocks leave room in.

The weighted count at the start plus the weighted bounds of the blocks must be within the limit.

The limit is weighted by the fork at the end. -/
theorem Run.registryLoad_le_limit {first last : ForkedBeaconState preset} {limit : Nat}
    (run : Run config checks first last)
    (room : registryLoadFactor first.fork * registryLoad first.state + run.loadBound ≤
      registryLoadFactor last.fork * limit) :
    registryLoad last.state ≤ limit := by
  exact Nat.le_of_mul_le_mul_left (Nat.le_trans run.registryLoad_le room)
    (one_le_registryLoadFactor last.fork)

/-- At the end of a run, the registry is within its limit, when the start and the blocks leave room.

The weighted count at the start plus the weighted bounds of the blocks must be within the limit.

The limit is weighted by the fork at the end. -/
theorem Run.registryWithinLimit {first last : ForkedBeaconState preset}
    (run : Run config checks first last)
    (room : registryLoadFactor first.fork * registryLoad first.state + run.loadBound ≤
      registryLoadFactor last.fork * preset.VALIDATOR_REGISTRY_LIMIT.toNat) :
    last.state.RegistryWithinLimit := by
  have bound : last.state.validators.data.size ≤ registryLoad last.state := Nat.le_add_right _ _
  exact Nat.le_trans bound (run.registryLoad_le_limit room)

/-- From Altair, the update of the inactivity scores succeeds on a count within the limit.

It takes the validators plus the pending deposits within the limit of the registry.

The other hypotheses are those of the same update when the registry alone is within its limit. -/
theorem processInactivityUpdates_total_of_registryLoad {fork : Fork}
    {state : BeaconState preset fork} (config : Config) (altair : .altair ≤ fork)
    (loaded : registryLoad state ≤ preset.VALIDATOR_REGISTRY_LIMIT.toNat)
    (finalized : FinalizedSettled state) (scored : InactivityScoresMatch state)
    (sized : ParticipationMatches state)
    (fits : ∀ score ∈ (state.inactivityScores altair).data,
      score.toNat + config.INACTIVITY_SCORE_BIAS.toNat < 2 ^ 64) :
    ∃ after, processInactivityUpdates config state altair = .ok after := by
  have size : state.validators.data.size ≤ registryLoad state := Nat.le_add_right _ _
  exact processInactivityUpdates_total config altair (Nat.le_trans size loaded) finalized scored
    sized fits

end EthLib.Consensus
