module

public import EthLib.Consensus.Proofs.ForkChoice.Supporters
public import EthLib.Consensus.Proofs.ForkChoice.VoteOrigins

/-!
# Proofs: the supporters of a block that the fast confirmation rule tests

Lemmas 4 and 3 of [arXiv 2405.00549v4][fcr] need each supporter of the block in a set `W`.

For a range with part of an epoch, `W` is the active members of the committees of the range.

This file places the slot of the vote of each supporter in that range.

That is the first step towards placing each supporter in those committees.

Another file shows that the state of the target and the state of the head agree on them.

A supporter of a block votes for a node that descends from it.

That node is a known block, from the slot of the block or later.

In a store where each latest vote has its origin, that vote comes from an attestation.

Its slot is at or after the slot of the voted block, and before the current slot.

So the slot of the vote lies in the range of the adversary of the block.

[fcr]: https://arxiv.org/abs/2405.00549v4
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Fork}

namespace Store

variable {config : Config} {store : Store preset fork}

/-- Each supporter of a known node votes by an attestation from the slot of that node or later.

Each latest vote of the store must come from an attestation, with the facts behind it. -/
theorem VotesHaveOrigins.exists_attestation_of_mem_supportersOf
    (holds : store.VotesHaveOrigins config) {state : BeaconState preset fork}
    {node : ForkChoiceNode} {block : BeaconBlock preset fork} {v : ValidatorIndex}
    (found : store.blocks[node.root]? = some block)
    (supporter : v ∈ store.supportersOf state node) :
    ∃ attestation, store.latestMessages[v]? = some (LatestMessage.ofAttestation attestation) ∧
      store.VoteOrigin config v attestation ∧ block.slot ≤ attestation.data.slot := by
  obtain ⟨message, sn, latest, -, supported, descends⟩ :=
    store.exists_of_voteCountsFor (store.voteCountsFor_of_mem_supportersOf supporter)
  obtain ⟨attestation, rfl, origin⟩ := holds latest
  obtain ⟨snBlock, snFound, slotLe⟩ := slot_le_of_isAncestor found descends
  have root := getSupportedNode_root supported
  obtain ⟨voted, votedFound, votedLe⟩ := origin.voted
  rw [root] at snFound
  have same : snBlock = voted := by
    simp only [LatestMessage.ofAttestation] at snFound
    rw [votedFound] at snFound
    exact (Option.some.inj snFound).symm
  subst same
  exact ⟨attestation, latest, origin, UInt64.le_trans slotLe votedLe⟩

/-- The vote of each supporter of a known block is from a slot of a range of slots.

The range starts at or before the slot of the block.

It ends at the last slot before the current one.

Each latest vote of the store must come from an attestation, with the facts behind it. -/
theorem VotesHaveOrigins.slot_mem_range_of_mem_supportersOf (holds : store.VotesHaveOrigins config)
    {state : BeaconState preset fork} {root : Root} {block : BeaconBlock preset fork}
    {currentSlot startSlot lastSlot : Slot} {v : ValidatorIndex}
    (blockOk : store.block root = .ok block) (startLe : startSlot ≤ block.slot)
    (slotOk : store.getCurrentSlot config = .ok currentSlot)
    (lastOk : subChecked currentSlot 1 = .ok lastSlot)
    (supporter : v ∈ store.supportersOf state ⟨root, .pending⟩) :
    ∃ attestation, store.latestMessages[v]? = some (LatestMessage.ofAttestation attestation) ∧
      store.VoteOrigin config v attestation ∧
      startSlot ≤ attestation.data.slot ∧ attestation.data.slot ≤ lastSlot := by
  have found : store.blocks[root]? = some block := block_ok_iff.mp blockOk
  obtain ⟨attestation, latest, origin, slotLe⟩ :=
    holds.exists_attestation_of_mem_supportersOf (node := ⟨root, .pending⟩) found supporter
  refine ⟨attestation, latest, origin, UInt64.le_trans startLe slotLe, ?_⟩
  obtain ⟨current, currentOk, past⟩ := origin.past
  rw [slotOk] at currentOk
  cases currentOk
  obtain ⟨le, eq⟩ := subChecked_ok_iff.mp lastOk
  rw [UInt64.le_iff_toNat_le]
  have := UInt64.lt_iff_toNat_lt.mp past
  simp only [UInt64.toNat_one] at le eq
  omega

end Store

end EthLib.Consensus
