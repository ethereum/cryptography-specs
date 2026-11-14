module

public import EthLib.Serialization.Proofs.Ssz.RandomOracle
public import EthLib.Serialization.Proofs.Ssz.Merkle.Branch
public import EthLib.Serialization.Ssz.Typed.Basic

/-!
# Proofs: two branches of one root in the random oracle model

An adversary queries the oracle, then outputs one index and two leaves, each with a branch.

The depth of the branches is fixed before the run.

The adversary wins when the leaves differ, both branches have that depth, and both reach one root.

The experiment climbs both branches as the branch check does, with the oracle as the node hash.

Each win exposes two different queried inputs with one answer, so the birthday bound applies.

The root of 48 bytes, the size of a commitment or a public key, is one call of the oracle.

Source: Bellare and Rogaway, "Random Oracles are Practical", CCS 1993, section 2, "Oracles".

<https://cseweb.ucsd.edu/~mihir/papers/ro.pdf>
-/

@[expose] public section

namespace EthLib.Serialization.Ssz.RandomOracle

open EthLib.Base
open OracleComp OracleSpec ENNReal
open EthLib.Cryptography.Merkle.RandomOracle (Collision experimentWith experimentWith_queryBound
  prEvent_experimentWith_le)

/-- What the adversary outputs: one index, and two leaves with a branch each. -/
structure BranchClaim where
  /-- The index of both leaves among the nodes of their depth. -/
  index : Nat
  /-- The first leaf. -/
  firstLeaf : Vector UInt8 32
  /-- The nodes of the first branch, from the leaf up. -/
  firstBranch : List (Vector UInt8 32)
  /-- The second leaf. -/
  secondLeaf : Vector UInt8 32
  /-- The nodes of the second branch, from the leaf up. -/
  secondBranch : List (Vector UInt8 32)

/-- What the branch experiment reports: the claim and the roots of its two branches. -/
structure BranchOutcome where
  /-- The index, leaves and branches of the adversary. -/
  claim : BranchClaim
  /-- The root that the first branch climbs to, as a node. -/
  firstRoot : Except Err (Vector UInt8 32)
  /-- The root that the second branch climbs to, as a node. -/
  secondRoot : Except Err (Vector UInt8 32)

/-- The extraction for branches, with a node hash in any monad.

It climbs the first `depth` nodes of each branch from its leaf, as the branch check does.

The experiment runs it with the oracle. -/
def extractBranches {m : Type → Type} [Monad m] (hash : ByteArray → m ByteArray) (depth : Nat)
    (claim : BranchClaim) : m BranchOutcome := do
  let firstRoot ← climbBranchM hash claim.index 0 claim.firstLeaf.toArray
    ((claim.firstBranch.take depth).map Vector.toArray)
  let secondRoot ← climbBranchM hash claim.index 0 claim.secondLeaf.toArray
    ((claim.secondBranch.take depth).map Vector.toArray)
  return ⟨claim, toChunk firstRoot, toChunk secondRoot⟩

/-- The adversary wins: two different leaves at one index climb to one root.

A win also needs both branches to have `depth` nodes. -/
def BranchWins (depth : Nat) (outcome : BranchOutcome) : Prop :=
  outcome.claim.firstLeaf ≠ outcome.claim.secondLeaf ∧
    outcome.claim.firstBranch.length = depth ∧ outcome.claim.secondBranch.length = depth ∧
    ∃ root, outcome.firstRoot = .ok root ∧ outcome.secondRoot = .ok root

/-- A climb, run against a full answer table, is the climb with that table. -/
theorem evalWithAnswerFn_climbBranchM (f : QueryImpl HashOracle Id) (index level : Nat)
    (node : Bytes) (branch : List Bytes) :
    evalWithAnswerFn f (climbBranchM queryHash index level node branch) =
      (climbBranchM (m := Id) (tableHash f) index level node branch).run := by
  unfold climbBranchM
  rw [Cryptography.Merkle.climb_map_monad (fun _ _ => combineM queryHash)
    (fun {β} (x : OracleComp HashOracle β) => (evalWithAnswerFn f x : Id β))
    (fun _ => rfl) (fun _ _ => evalWithAnswerFn_bind _ _ _)]
  exact congrArg (fun hash => Cryptography.Merkle.climb hash level (index >>> level) node branch)
    (by funext _ _ left right; exact evalWithAnswerFn_combineM f left right)

/-- A replayed climb caches every message it hashes, with the answer of the table.

It needs the table to agree with the cache. -/
theorem cached_of_climbBranchM {cache : HashOracle.QueryCache} {f : QueryImpl HashOracle Id}
    (hf : cache.AgreesWithFn f) {index level : Nat} {node root : Bytes} {branch : List Bytes}
    (hrun : simulateQ cache.toPartialImpl (climbBranchM queryHash index level node branch) =
      some root) :
    ∀ x ∈ branchMessages index level node branch (tableHash f),
      cache (ByteArray.mk x) = some (f (ByteArray.mk x)) := by
  -- Each level queries its pair, and the levels above climb from the parent of the table.
  have climbed : ∀ (branch : List Bytes) (level j : Nat) (node : Bytes) {root : Bytes},
      simulateQ cache.toPartialImpl
          (Cryptography.Merkle.climb (fun _ _ => combineM queryHash) level j node branch) =
        some root →
      ∀ x ∈ Cryptography.Merkle.climbPairs (fun _ _ => combineM (m := Id) (tableHash f)) level j
          node branch,
        cache (ByteArray.mk (x.1 ++ x.2)) = some (f (ByteArray.mk (x.1 ++ x.2))) := by
    intro branch
    induction branch with
    | nil =>
      intro _ _ _ _ _ x hx
      simp [Cryptography.Merkle.climbPairs] at hx
    | cons sibling rest ih =>
      intro level j node root hrun x hx
      simp only [Cryptography.Merkle.climb, simulateQ_bind] at hrun
      obtain ⟨parent, hparent, hrun⟩ := Option.bind_eq_some_iff.mp hrun
      -- The replayed parent is the parent with the table, which agrees with the cache.
      have heval := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hparent
      rw [evalWithAnswerFn_combineM] at heval
      simp only [Cryptography.Merkle.climbPairs, List.mem_cons] at hx
      rcases hx with rfl | hx
      · -- This level queried its pair, so the cache holds the answer of the table.
        simp only [combineM, simulateQ_bind] at hparent
        obtain ⟨_, hquery, -⟩ := Option.bind_eq_some_iff.mp hparent
        obtain ⟨digest, hdigest⟩ := cached_of_queryHash hquery
        rw [hdigest, hf hdigest]
      · rw [← heval] at hrun
        exact ih (level + 1) (j / 2) _ hrun x hx
  intro x hx
  simp only [branchMessages, List.mem_map] at hx
  obtain ⟨pair, hpair, rfl⟩ := hx
  exact climbed branch level (index >>> level) node hrun pair hpair

/-- A replayed winning branch extraction exposes a collision of the cache.

The search over the two climbs finds it, run with a table that extends the cache. -/
theorem collision_of_extractBranches {depth : Nat} {cache : HashOracle.QueryCache}
    {claim : BranchClaim} {outcome : BranchOutcome}
    (hrun : simulateQ cache.toPartialImpl (extractBranches queryHash depth claim) = some outcome)
    (hwins : BranchWins depth outcome) : Collision cache := by
  -- A table that extends the cache fixes the value of every replayed climb.
  obtain ⟨f, hf⟩ := cache.exists_agreesWithFn
  have hout := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hrun
  simp only [extractBranches, evalWithAnswerFn_bind, evalWithAnswerFn_climbBranchM,
    evalWithAnswerFn_pure] at hout
  subst hout
  obtain ⟨hleaves, hfirst, hsecond, root, hroot₁, hroot₂⟩ := hwins
  dsimp only at hleaves hfirst hsecond hroot₁ hroot₂
  rw [toChunk_ok_iff] at hroot₁ hroot₂
  -- Under the table, the leaves are equal, or the search over the two climbs finds a collision.
  rcases climbBranchM_binding (tableHash f) (by simp [hfirst, hsecond])
      (hroot₁.trans hroot₂.symm) with hsame | hfound
  · exact absurd (Vector.toArray_inj.mp hsame) hleaves
  · obtain ⟨⟨a, b⟩, hab⟩ := Option.isSome_iff_exists.mp hfound
    -- Every leaf and every branch node is a 32-byte vector.
    have widths : ∀ (nodes : List (Vector UInt8 32)),
        ∀ node ∈ nodes.map Vector.toArray, node.size = bytesPerChunk := by
      intro nodes node member
      obtain ⟨vector, -, rfl⟩ := List.mem_map.mp member
      exact vector.size_toArray
    obtain ⟨-, -, hdistinct, hequal⟩ := findBranchCollision_valid_of_width (tableHash f)
      (tableHash_size f) (by simp) (by simp) (widths _) (widths _) hab
    obtain ⟨ha, hb⟩ := findBranchCollision_mem hab
    -- Both climbs were replayed, so the cache gives their messages the answers of the table.
    simp only [extractBranches, simulateQ_bind] at hrun
    obtain ⟨_, hrun₁, hrun⟩ := Option.bind_eq_some_iff.mp hrun
    obtain ⟨_, hrun₂, -⟩ := Option.bind_eq_some_iff.mp hrun
    exact collision_of_cached hdistinct hequal (cached_of_climbBranchM hf hrun₁ a ha)
      (cached_of_climbBranchM hf hrun₂ b hb)

/-- A climb makes at most one oracle call per branch node. -/
private theorem climbBranchM_queryBound (index level : Nat) (node : Bytes) (branch : List Bytes) :
    IsQueryBoundP (climbBranchM queryHash index level node branch) (fun _ => True)
      branch.length := by
  unfold climbBranchM
  generalize index >>> level = j
  induction branch generalizing level j node with
  | nil => trivial
  | cons sibling rest ih =>
    simp only [Cryptography.Merkle.climb]
    refine (isQueryBoundP_bind (n := 1) ?_ fun parent _ => ih (level + 1) parent (j / 2)).mono
      (by simp [Nat.add_comm])
    simp [combineM, queryHash]

/-- The extraction makes at most `2 * depth` oracle calls, one per climbed node.

It climbs at most `depth` nodes of each branch. -/
theorem extractBranches_queryBound (depth : Nat) (claim : BranchClaim) :
    IsQueryBoundP (extractBranches queryHash depth claim) (fun _ => True) (2 * depth) := by
  -- Each climb takes at most `depth` branch nodes, with one call per node.
  have climbs : ∀ (leaf : Vector UInt8 32) (branch : List (Vector UInt8 32)),
      IsQueryBoundP (climbBranchM queryHash claim.index 0 leaf.toArray
        ((branch.take depth).map Vector.toArray)) (fun _ => True) depth := fun _ _ =>
    (climbBranchM_queryBound _ _ _ _).mono (by simp)
  exact (isQueryBoundP_bind (climbs _ _) fun _ _ =>
    isQueryBoundP_bind (climbs _ _) fun _ _ => isQueryBoundP_pure _ _ 0).mono (by omega)

/-- The experiment makes the adversary's oracle calls and at most one call per climbed node.

The extraction climbs at most `depth` nodes of each branch. -/
theorem experimentWith_extractBranches_queryBound (depth : Nat)
    {adversary : OracleComp (unifSpec + HashOracle) BranchClaim} {q : Nat}
    (hq : IsQueryBoundP adversary (fun t => t.isRight = true) q) :
    IsQueryBoundP (experimentWith (extractBranches queryHash depth) adversary)
      (fun t => t.isRight = true) (q + 2 * depth) :=
  experimentWith_queryBound hq (extractBranches_queryBound depth)

/-- Two different leaves at one index with one root, at probability at most `Q^2 / N`.

A win needs both branches to have `depth` nodes, and `N` is the number of digests.

The roots are computed with the oracle as the node hash.

`Q` bounds the oracle calls of the whole experiment, repeats included.

The extraction climbs each branch with one call per node, so it adds at most `2 * depth` calls.

The oracle cache starts empty, and the adversary's private sampling is not counted. -/
theorem prEvent_branchWins_le [SampleableType Hash32] (depth : Nat)
    (adversary : OracleComp (unifSpec + HashOracle) BranchClaim) {Q : Nat}
    (hQ : IsQueryBoundP (experimentWith (extractBranches queryHash depth) adversary)
      (fun t => t.isRight = true) Q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractBranches queryHash depth) adversary)).run ∅}[BranchWins depth z.1] ≤
      Q * ((Q : ℝ≥0∞) / Nat.card Hash32) :=
  prEvent_experimentWith_le (extractBranches queryHash depth) (BranchWins depth)
    collision_of_extractBranches adversary hQ

/-- The same bound for 32 uniform bytes per answer: probability at most `Q^2 / 2^256`. -/
theorem prEvent_branchWins_le_two_pow (depth : Nat)
    (adversary : OracleComp (unifSpec + HashOracle) BranchClaim) {Q : Nat}
    (hQ : IsQueryBoundP (experimentWith (extractBranches queryHash depth) adversary)
      (fun t => t.isRight = true) Q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractBranches queryHash depth) adversary)).run ∅}[BranchWins depth z.1] ≤
      Q * ((Q : ℝ≥0∞) / 2 ^ 256) := by
  have bound := prEvent_branchWins_le depth adversary hQ
  rw [Cryptography.Merkle.RandomOracle.card_bytes32, Nat.cast_pow, Nat.cast_ofNat] at bound
  exact bound

/-- The same bound with the adversary's oracle calls `q` counted alone.

A win has probability at most `(q + 2 * depth)^2 / 2^256`. -/
theorem prEvent_branchWins_le_of_adversary (depth : Nat)
    (adversary : OracleComp (unifSpec + HashOracle) BranchClaim) {q : Nat}
    (hq : IsQueryBoundP adversary (fun t => t.isRight = true) q) :
    Pr{let z ← (simulateQ HashOracle.romImpl
      (experimentWith (extractBranches queryHash depth) adversary)).run ∅}[BranchWins depth z.1] ≤
      (q + 2 * depth : Nat) * (((q + 2 * depth : Nat) : ℝ≥0∞) / 2 ^ 256) :=
  prEvent_branchWins_le_two_pow depth adversary
    (experimentWith_extractBranches_queryBound depth hq)

/-- With SHA-256 in the identity monad, the extraction climbs as the branch check does. -/
theorem extractBranches_sha256 (depth : Nat) (claim : BranchClaim) :
    (extractBranches (m := Id) Cryptography.Hash.Sha256.hash depth claim).run =
      ⟨claim, toChunk (climbBranch claim.index 0 claim.firstLeaf.toArray
          ((claim.firstBranch.take depth).map Vector.toArray)),
        toChunk (climbBranch claim.index 0 claim.secondLeaf.toArray
          ((claim.secondBranch.take depth).map Vector.toArray))⟩ :=
  rfl

/-- With SHA-256 as the node hash, a win is two valid branches of two different leaves.

The two branches have one depth, one index and one root.

The roots of the outcome are then computed with SHA-256, not with the oracle.

The step from SHA-256 to the oracle is the idealisation of the model, not a theorem. -/
theorem branchWins_sha256_iff {depth : Nat} {claim : BranchClaim} :
    BranchWins depth (extractBranches (m := Id) Cryptography.Hash.Sha256.hash depth claim).run ↔
      claim.firstLeaf ≠ claim.secondLeaf ∧ ∃ root,
        isValidMerkleBranch claim.firstLeaf claim.firstBranch depth claim.index root = true ∧
        isValidMerkleBranch claim.secondLeaf claim.secondBranch depth claim.index root = true := by
  rw [extractBranches_sha256]
  simp only [BranchWins, isValidMerkleBranch_eq_true_iff, toChunk_ok_iff]
  -- A branch of `depth` nodes keeps all of them, so the extraction climbs the whole branch.
  constructor
  · rintro ⟨differ, firstCount, secondCount, root, firstClimbed, secondClimbed⟩
    rw [List.take_of_length_le firstCount.le] at firstClimbed
    rw [List.take_of_length_le secondCount.le] at secondClimbed
    exact ⟨differ, root, ⟨firstCount, firstClimbed⟩, secondCount, secondClimbed⟩
  · rintro ⟨differ, root, ⟨firstCount, firstClimbed⟩, secondCount, secondClimbed⟩
    refine ⟨differ, firstCount, secondCount, root, ?_, ?_⟩
    · rw [List.take_of_length_le firstCount.le]
      exact firstClimbed
    · rw [List.take_of_length_le secondCount.le]
      exact secondClimbed

/-- The 48 bytes of a vector and 16 zero bytes form its two packed nodes. -/
private theorem packBytes_bytes48 (bytes : Vector UInt8 48) :
    padded zeroChunk (Serialization.Ssz.packBytes bytes.toArray) 0 ++
        padded zeroChunk (Serialization.Ssz.packBytes bytes.toArray) 1 =
      bytes.toArray ++ Array.replicate 16 0 := by
  have size : bytes.toArray.size = 48 := bytes.size_toArray
  simp [padded, Serialization.Ssz.packBytes, size, bytesPerChunk, ← Array.append_assoc,
    Array.extract_append_extract, Array.extract_eq_self_of_le]

/-- A perfect tree of depth 1 over two nodes is one hash of the two nodes, with any hasher. -/
private theorem subtreeAtM_two {m : Type → Type} [Monad m] [LawfulMonad m] (hasher : Hasher m)
    {chunks : Array Bytes} (count : chunks.size = 2) :
    subtreeAtM hasher chunks 1 0 =
      combineM hasher.hash (padded zeroChunk chunks 0) (padded zeroChunk chunks 1) := by
  simp only [subtreeAtM, count]
  simp

/-- The root of 48 bytes is one hash of those bytes and 16 zero bytes.

It holds for a hasher in any lawful monad. -/
theorem hashTreeRootM_bytes48 {m : Type → Type} [Monad m] [LawfulMonad m]
    (hasher : Hasher m) (bytes : Vector UInt8 48) :
    (hashTreeRootM hasher (SszType.desc (Vector UInt8 48)) (SszType.toValue bytes)).run = (do
      return .ok (← hasher.hash ⟨bytes.toArray ++ Array.replicate 16 0⟩).data) := by
  have size : bytes.toArray.size = 48 := bytes.size_toArray
  have count : (Serialization.Ssz.packBytes bytes.toArray).size = 2 := by
    simp [size, bytesPerChunk]
  show (hashTreeRootAtM hasher 1 (.byteVector 48) (.bytes bytes.toArray)).run = _
  simp only [hashTreeRootAtM, merkleLayout, size, bne_self_eq_false, Bool.false_eq_true,
    ↓reduceIte, liftM_pure, pure_bind]
  simp only [layoutChunksAtM, MerkleLayout.packing, Option.getD_none, Leaves.count,
    Array.extract_size, pure_bind, bind_pure, merkleizeBoundedUncheckedM, Nat.lt_irrefl,
    ↓reduceIte, ExceptT.run_lift]
  rw [count, show depthFor 2 = 1 from depthFor_pow 1, subtreeAtM_two hasher count, combineM,
    packBytes_bytes48]
  simp only [map_bind, map_pure]

/-- The root of 48 bytes makes one oracle call. -/
theorem hashTreeRootM_bytes48_queryBound (bytes : Vector UInt8 48) :
    IsQueryBoundP (hashTreeRootM (Hasher.ofHash queryHash) (SszType.desc (Vector UInt8 48))
      (SszType.toValue bytes)).run (fun _ => True) 1 := by
  rw [hashTreeRootM_bytes48]
  simp [Hasher.ofHash, queryHash]

/-- A replayed root of 48 bytes caches its message, and is the answer of the table to it.

It needs the table to agree with the cache. -/
theorem cached_of_hashTreeRootM_bytes48 {cache : HashOracle.QueryCache}
    {f : QueryImpl HashOracle Id} (hf : cache.AgreesWithFn f) {bytes : Vector UInt8 48}
    {root : Except Err Bytes}
    (hrun : simulateQ cache.toPartialImpl (hashTreeRootM (Hasher.ofHash queryHash)
      (SszType.desc (Vector UInt8 48)) (SszType.toValue bytes)).run = some root) :
    cache ⟨bytes.toArray ++ Array.replicate 16 0⟩ =
        some (f ⟨bytes.toArray ++ Array.replicate 16 0⟩) ∧
      root = .ok (tableHash f ⟨bytes.toArray ++ Array.replicate 16 0⟩).data := by
  have heval := cache.evalWithAnswerFn_eq_of_agreesWithFn hf _ hrun
  rw [hashTreeRootM_bytes48] at hrun heval
  simp only [Hasher.ofHash, evalWithAnswerFn_bind, evalWithAnswerFn_queryHash,
    evalWithAnswerFn_pure] at heval
  simp only [Hasher.ofHash, simulateQ_bind] at hrun
  obtain ⟨_, hquery, -⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨digest, hdigest⟩ := cached_of_queryHash hquery
  exact ⟨by rw [hdigest, hf hdigest], heval.symm⟩

end EthLib.Serialization.Ssz.RandomOracle
