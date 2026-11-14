module

public import EthLib.Consensus.BeaconApi.LightClient
public import EthLib.Consensus.Proofs.ForkChoice.Reachable
import EthLib.Consensus.Proofs.BeaconApi.LightClientBootstrap
import EthLib.Consensus.Proofs.BeaconApi.StateQueries

/-!
# Proofs: a light client bootstrap served from a store that the handlers reach

A bootstrap that the node serves from such a store starts a light client that trusts its block.

The store holds the block under its own root, and the state after it with the state root it names.

It needs the forks from Capella to Heze in order, a lawful state type and nonzero preset sizes.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork} {config : Config}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {store : Store preset fork}

/-- A bootstrap served from a reachable store starts a light client that trusts its block.

It needs the schedule to put the forks from Capella to Heze in order.

It needs the sizes of the preset that the block and the state hold to be nonzero.

It needs the state type to be lawful. -/
theorem bootstrapFor_valid_of_reachable [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat]
    [NeZero preset.PTC_SIZE.toNat] [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]
    [LawfulSszType (BeaconState preset fork)]
    (reachable : Store.Reachable config anchorState anchorBlock store) {root : Root}
    {bootstrap : LightClientBootstrap preset fork}
    (ordered : config.CAPELLA_FORK_EPOCH ≤ config.DENEB_FORK_EPOCH ∧
      config.DENEB_FORK_EPOCH ≤ config.ELECTRA_FORK_EPOCH ∧
      config.ELECTRA_FORK_EPOCH ≤ config.FULU_FORK_EPOCH ∧
      config.FULU_FORK_EPOCH ≤ config.GLOAS_FORK_EPOCH ∧
      config.GLOAS_FORK_EPOCH ≤ config.HEZE_FORK_EPOCH)
    (served : bootstrapFor config store root = .ok bootstrap) :
    ∃ lightClient, initializeLightClientStore config root bootstrap = .ok lightClient := by
  cases held : store.blocks[root]? with
  | none =>
    rw [bootstrapFor_of_missing (.inl held)] at served
    cases served
  | some block =>
    cases heldState : store.blockStates[root]? with
    | none =>
      rw [bootstrapFor_of_missing (.inr heldState)] at served
      cases served
    | some state =>
      exact bootstrapFor_valid held heldState (reachable.root held)
        (stateRoot_blockStates reachable heldState held) ordered served

end EthLib.Consensus.BeaconApi
