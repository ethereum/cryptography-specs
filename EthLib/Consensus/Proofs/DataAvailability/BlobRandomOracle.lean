module

public import EthLib.Consensus.DataAvailability.Blob
public import EthLib.Serialization.Proofs.Ssz.BranchRandomOracle

/-!
# Proofs: two blob sidecars of one index and one body root in the random oracle model

An adversary outputs two blob sidecars, for a preset and a fork fixed before the run.

It wins with one index, one body root and different commitments, if both proofs reach that root.

The experiment climbs both proofs as the inclusion check does, with the oracle as the node hash.

A win exposes two different queried messages with one answer, so the birthday bound applies.

A win has probability at most `Q^2 / N`, where `Q` bounds all oracle calls and `N` counts digests.

At the mainnet depth of 17, an adversary of `q` calls gives a bound of `(q + 36)^2 / 2^256`.

Only the forks from Deneb and before Gloas put commitments in the body, where the climbs can run.

With SHA-256 as the node hash, a win is two such sidecars that the inclusion check accepts.

Source: Bellare and Rogaway, "Random Oracles are Practical", CCS 1993, section 2, "Oracles".

<https://cseweb.ucsd.edu/~mihir/papers/ro.pdf>
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz Serialization.Ssz.RandomOracle
open OracleComp OracleSpec ENNReal
open Cryptography.Kzg (KZGCommitment)
open Cryptography.Merkle.RandomOracle (Collision experimentWith experimentWith_queryBound
  prEvent_experimentWith_le)

/-- What the blob experiment reports: the two sidecars, and the climbs of their proofs.

The climbs are absent when the subtree index or a commitment root cannot be read. -/
structure BlobOutcome (preset : Preset) where
  /-- The first sidecar of the adversary. -/
  first : BlobSidecar preset
  /-- The second sidecar of the adversary. -/
  second : BlobSidecar preset
  /-- The index, the commitment roots, the proofs and the roots that the proofs climb to. -/
  climbs : Option BranchOutcome

/-- The extraction for blob sidecars, with a node hash in any monad.

It roots both commitments, then reads the subtree index from the blob index of the first sidecar.

Then it climbs both proofs from their roots, at that index and at the depth of the proof.

The preset fixes that depth, and the fork fixes the place of the commitments in the body.

The experiment runs it with the oracle. -/
def extractBlobSidecars {m : Type → Type} [Monad m] (hash : ByteArray → m ByteArray)
    (preset : Preset) (fork : Fork) (claim : BlobSidecar preset × BlobSidecar preset) :
    m (BlobOutcome preset) := do
  let firstRoot ← (hashTreeRootM (Hasher.ofHash hash) (SszType.desc KZGCommitment)
    (SszType.toValue claim.1.kzgCommitment)).run
  let secondRoot ← (hashTreeRootM (Hasher.ofHash hash) (SszType.desc KZGCommitment)
    (SszType.toValue claim.2.kzgCommitment)).run
  let climbs ← (match blobKzgCommitmentGindex preset fork claim.1.index.toNat >>= getSubtreeIndex,
      firstRoot >>= toChunk, secondRoot >>= toChunk with
    | .ok index, .ok firstLeaf, .ok secondLeaf => do
      let climbs ← extractBranches hash preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat
        ⟨index, firstLeaf, claim.1.kzgCommitmentInclusionProof.toList, secondLeaf,
          claim.2.kzgCommitmentInclusionProof.toList⟩
      pure (some climbs)
    | _, _, _ => pure none)
  return ⟨claim.1, claim.2, climbs⟩

/-- The adversary wins: two sidecars with one index and one body root carry different commitments.

A win also needs both proofs to climb from the roots of their commitments to that body root. -/
def BlobWins {preset : Preset} (outcome : BlobOutcome preset) : Prop :=
  outcome.first.index = outcome.second.index ∧
    outcome.first.signedBlockHeader.message.bodyRoot =
      outcome.second.signedBlockHeader.message.bodyRoot ∧
    outcome.first.kzgCommitment ≠ outcome.second.kzgCommitment ∧
    ∃ climbs, outcome.climbs = some climbs ∧
      climbs.firstRoot = .ok outcome.first.signedBlockHeader.message.bodyRoot ∧
      climbs.secondRoot = .ok outcome.second.signedBlockHeader.message.bodyRoot

/-- A replayed winning blob extraction exposes a collision of the cache.

Two different commitments with one root give two different messages with one answer.

Two different roots that climb to one body root give the collision of the two climbs.

It holds for every preset and fork. -/
theorem collision_of_extractBlobSidecars {preset : Preset} {fork : Fork}
    {cache : HashOracle.QueryCache} {claim : BlobSidecar preset × BlobSidecar preset}
    {outcome : BlobOutcome preset}
    (hrun : simulateQ cache.toPartialImpl (extractBlobSidecars queryHash preset fork claim) =
      some outcome)
    (hwins : BlobWins outcome) : Collision cache := by
  -- A table that extends the cache fixes the value of every replayed computation.
  obtain ⟨f, hf⟩ := cache.exists_agreesWithFn
  simp only [extractBlobSidecars, simulateQ_bind] at hrun
  obtain ⟨firstRoot, hfirst, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨secondRoot, hsecond, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨climbs, hclimbs, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  simp only [simulateQ_pure] at hrun
  cases hrun
  obtain ⟨-, sameRoot, differ, climbed, present, firstClimbed, secondClimbed⟩ := hwins
  dsimp only at sameRoot differ present firstClimbed secondClimbed
  subst present
  obtain ⟨firstCached, rfl⟩ := cached_of_hashTreeRootM_bytes48 hf hfirst
  obtain ⟨secondCached, rfl⟩ := cached_of_hashTreeRootM_bytes48 hf hsecond
  split at hclimbs
  · rename_i index firstLeaf secondLeaf _ hfirstLeaf hsecondLeaf
    simp only [simulateQ_bind, simulateQ_pure] at hclimbs
    obtain ⟨_, hbranches, hclimbs⟩ := Option.bind_eq_some_iff.mp hclimbs
    cases hclimbs
    simp only [bind, Except.bind, toChunk_ok_iff] at hfirstLeaf hsecondLeaf
    -- The root of a commitment is one hash, so no rehash of the general extraction is needed.
    by_cases sameLeaf : firstLeaf = secondLeaf
    · -- One root of two different commitments is one answer to two different messages.
      subst sameLeaf
      refine collision_of_cached (fun same => differ ?_) ?_ firstCached secondCached
      · exact Vector.toArray_inj.mp ((Array.append_left_inj _).mp same)
      · exact congrArg ByteArray.mk (hfirstLeaf.trans hsecondLeaf.symm)
    · -- Two different roots climb to one body root, so the search finds a collision of the climbs.
      have hout := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hbranches
      simp only [extractBranches, evalWithAnswerFn_bind, evalWithAnswerFn_climbBranchM,
        evalWithAnswerFn_pure] at hout
      subst hout
      exact collision_of_extractBranches hbranches ⟨sameLeaf, by simp, by simp, _, firstClimbed,
        sameRoot ▸ secondClimbed⟩
  · simp only [simulateQ_pure] at hclimbs
    cases hclimbs

/-- The extraction makes at most `2 + 2 * depth` oracle calls, with `depth` that of the proofs.

It makes one call per commitment root, and climbs at most `depth` nodes of each proof. -/
theorem extractBlobSidecars_queryBound (preset : Preset) (fork : Fork)
    (claim : BlobSidecar preset × BlobSidecar preset) :
    IsQueryBoundP (extractBlobSidecars queryHash preset fork claim) (fun _ => True)
      (2 + 2 * preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat) := by
  unfold extractBlobSidecars
  refine (isQueryBoundP_bind (hashTreeRootM_bytes48_queryBound _) fun _ _ =>
    isQueryBoundP_bind (hashTreeRootM_bytes48_queryBound _) fun _ _ =>
      isQueryBoundP_bind (n := 2 * preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat) (m := 0) ?_
        fun _ _ => isQueryBoundP_pure _ _ 0).mono (by omega)
  split
  · exact (isQueryBoundP_bind (extractBranches_queryBound _ _) fun _ _ =>
      isQueryBoundP_pure _ _ 0).mono (by omega)
  · exact isQueryBoundP_pure _ _ _

/-- The experiment makes at most `q + 2 + 2 * depth` oracle calls, with `depth` that of the proofs.

It needs the adversary to make at most `q` oracle calls.

The extraction makes one call per commitment root and at most one per climbed node. -/
theorem experimentWith_extractBlobSidecars_queryBound (preset : Preset) (fork : Fork)
    {adversary : OracleComp (unifSpec + HashOracle) (BlobSidecar preset × BlobSidecar preset)}
    {q : Nat} (hq : IsQueryBoundP adversary (fun t => t.isRight = true) q) :
    IsQueryBoundP (experimentWith (extractBlobSidecars queryHash preset fork) adversary)
      (fun t => t.isRight = true)
      (q + 2 + 2 * preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat) :=
  (experimentWith_queryBound hq (extractBlobSidecars_queryBound preset fork)).mono (by omega)

/-- An adversary that outputs two blob sidecars wins with probability at most `Q^2 / N`.

A win is one index, one body root, different commitments, and both proofs climbing to that root.

`Q` bounds the oracle calls of the whole experiment, repeats included, and `N` counts digests.

The oracle cache starts empty, and the adversary's private sampling is not counted. -/
theorem prEvent_blobWins_le [SampleableType Hash32] (preset : Preset) (fork : Fork)
    (adversary : OracleComp (unifSpec + HashOracle) (BlobSidecar preset × BlobSidecar preset))
    {Q : Nat}
    (hQ : IsQueryBoundP (experimentWith (extractBlobSidecars queryHash preset fork) adversary)
      (fun t => t.isRight = true) Q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractBlobSidecars queryHash preset fork) adversary)).run ∅}[
        BlobWins z.1] ≤ Q * ((Q : ℝ≥0∞) / Nat.card Hash32) :=
  prEvent_experimentWith_le (extractBlobSidecars queryHash preset fork) BlobWins
    collision_of_extractBlobSidecars adversary hQ

/-- The same bound for 32 uniform bytes per answer: probability at most `Q^2 / 2^256`. -/
theorem prEvent_blobWins_le_two_pow (preset : Preset) (fork : Fork)
    (adversary : OracleComp (unifSpec + HashOracle) (BlobSidecar preset × BlobSidecar preset))
    {Q : Nat}
    (hQ : IsQueryBoundP (experimentWith (extractBlobSidecars queryHash preset fork) adversary)
      (fun t => t.isRight = true) Q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractBlobSidecars queryHash preset fork) adversary)).run ∅}[
        BlobWins z.1] ≤ Q * ((Q : ℝ≥0∞) / 2 ^ 256) := by
  have bound := prEvent_blobWins_le preset fork adversary hQ
  rw [Cryptography.Merkle.RandomOracle.card_bytes32, Nat.cast_pow, Nat.cast_ofNat] at bound
  exact bound

/-- The same bound with the adversary's oracle calls `q` counted alone.

A win has probability at most `(q + 2 + 2 * depth)^2 / 2^256`, with `depth` that of the proofs. -/
theorem prEvent_blobWins_le_of_adversary (preset : Preset) (fork : Fork)
    (adversary : OracleComp (unifSpec + HashOracle) (BlobSidecar preset × BlobSidecar preset))
    {q : Nat} (hq : IsQueryBoundP adversary (fun t => t.isRight = true) q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractBlobSidecars queryHash preset fork) adversary)).run ∅}[
        BlobWins z.1] ≤
      (q + 2 + 2 * preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat : Nat) *
        (((q + 2 + 2 * preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat : Nat) : ℝ≥0∞) /
          2 ^ 256) :=
  prEvent_blobWins_le_two_pow preset fork adversary
    (experimentWith_extractBlobSidecars_queryBound preset fork hq)

/-- At the mainnet depth of 17, a win has probability at most `(q + 36)^2 / 2^256`.

It needs the adversary to make at most `q` oracle calls, and it holds for every fork. -/
theorem prEvent_blobWins_le_mainnet (fork : Fork)
    (adversary : OracleComp (unifSpec + HashOracle)
      (BlobSidecar .mainnet × BlobSidecar .mainnet))
    {q : Nat} (hq : IsQueryBoundP adversary (fun t => t.isRight = true) q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractBlobSidecars queryHash .mainnet fork) adversary)).run ∅}[
        BlobWins z.1] ≤ (q + 36 : Nat) * (((q + 36 : Nat) : ℝ≥0∞) / 2 ^ 256) :=
  prEvent_blobWins_le_of_adversary .mainnet fork adversary hq

/-- With SHA-256, the extraction roots each commitment and reads the index as the spec does. -/
theorem extractBlobSidecars_sha256 (preset : Preset) (fork : Fork)
    (claim : BlobSidecar preset × BlobSidecar preset) :
    (extractBlobSidecars (m := Id) Cryptography.Hash.Sha256.hash preset fork claim).run =
      ⟨claim.1, claim.2,
        match blobKzgCommitmentGindex preset fork claim.1.index.toNat >>= getSubtreeIndex,
            SszType.hashTreeRoot claim.1.kzgCommitment,
            SszType.hashTreeRoot claim.2.kzgCommitment with
        | .ok index, .ok firstLeaf, .ok secondLeaf =>
          some (extractBranches (m := Id) Cryptography.Hash.Sha256.hash
            preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat
            ⟨index, firstLeaf, claim.1.kzgCommitmentInclusionProof.toList, secondLeaf,
              claim.2.kzgCommitmentInclusionProof.toList⟩).run
        | _, _, _ => none⟩ := by
  simp only [extractBlobSidecars, ofHash_sha256]
  rfl

/-- With SHA-256 as the node hash, a win is two sidecars that the inclusion check accepts.

The two sidecars have one index and one body root, and different commitments.

The roots of the outcome are then computed with SHA-256, not with the oracle.

The step from SHA-256 to the oracle is the idealisation of the model, not a theorem.

It holds for every preset and fork. -/
theorem blobWins_sha256_iff {preset : Preset} {fork : Fork}
    {claim : BlobSidecar preset × BlobSidecar preset} :
    BlobWins (extractBlobSidecars (m := Id) Cryptography.Hash.Sha256.hash preset fork claim).run ↔
      claim.1.index = claim.2.index ∧
        claim.1.signedBlockHeader.message.bodyRoot =
          claim.2.signedBlockHeader.message.bodyRoot ∧
        claim.1.kzgCommitment ≠ claim.2.kzgCommitment ∧
        verifyBlobSidecarInclusionProof preset fork claim.1 = true ∧
        verifyBlobSidecarInclusionProof preset fork claim.2 = true := by
  rw [extractBlobSidecars_sha256]
  simp only [BlobWins]
  refine and_congr_right fun sameIndex => and_congr_right fun sameRoot =>
    and_congr_right fun _ => ?_
  -- Both checks read the subtree index of one blob index, and climb to one body root.
  unfold verifyBlobSidecarInclusionProof
  rw [← sameIndex, ← sameRoot]
  -- A proof of the inclusion depth keeps all its nodes, so the extraction climbs all of them.
  have whole : ∀ (sidecar : BlobSidecar preset),
      sidecar.kzgCommitmentInclusionProof.toList.take
          preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH.toNat =
        sidecar.kzgCommitmentInclusionProof.toList :=
    fun _ => List.take_of_length_le (by simp)
  cases read : blobKzgCommitmentGindex preset fork claim.1.index.toNat with
  | error => simp [bind, Except.bind]
  | ok gindex =>
    cases subtree : getSubtreeIndex gindex <;>
      cases firstRoot : SszType.hashTreeRoot claim.1.kzgCommitment <;>
      cases secondRoot : SszType.hashTreeRoot claim.2.kzgCommitment <;>
      simp [bind, Except.bind, subtree, extractBranches_sha256, whole,
        isValidMerkleBranch_eq_true_iff, toChunk_ok_iff]

end EthLib.Consensus
