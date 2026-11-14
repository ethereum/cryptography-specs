module

public import EthLib.Cryptography.Proofs.Merkle.Binding
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshAnswer
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.QueryTracking.SubSpec
public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial

/-!
# Classical random-oracle collision bounds

A random oracle is a uniformly random function, chosen once for every party.

Source: Bellare and Rogaway, "Random Oracles are Practical", CCS 1993, section 2, "Oracles".

<https://cseweb.ucsd.edu/~mihir/papers/ro.pdf>

The oracle here samples each new input uniformly and remembers its answer.

Repeated inputs are not collisions, but still count towards the query budget.

The birthday bound here is the loose bound `q^2 / N`, for `N` possible answers.

It exceeds the standard bound `q(q - 1) / (2N)` by the factor `2q / (q - 1)`.

That factor is at most 4 for `q >= 2`, and close to 2 for large `q`.

The proof charges each fresh answer at most `q / N`, and private uniform sampling is not counted.

These are ideal-oracle statements, not claims about the structure of a concrete hash.
-/

@[expose] public section

namespace EthLib.Cryptography.Merkle.RandomOracle

open OracleComp OracleSpec ENNReal

variable {D R α : Type} [DecidableEq D]

/-- Two different queried inputs have the same cached answer. -/
def Collision (c : (D →ₒ R).QueryCache) : Prop :=
  ∃ x y r, x ≠ y ∧ c x = some r ∧ c y = some r

/-- A fresh answer can create a collision only by matching an old answer. -/
theorem collision_cacheQuery {c : (D →ₒ R).QueryCache} {t : D} {u : R}
    (hc : ¬ Collision c) (_ht : c t = none) :
    Collision (c.cacheQuery t u) → u ∈ Sigma.snd '' c.toSet := by
  rintro ⟨x, y, r, hxy, hx, hy⟩
  by_cases hxt : x = t
  · subst x
    have hyr : c y = some r := by
      rwa [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hxy)] at hy
    have hur : u = r := by simpa using hx
    exact ⟨⟨y, r⟩, hyr, hur.symm⟩
  · rw [QueryCache.cacheQuery_of_ne _ _ hxt] at hx
    by_cases hyt : y = t
    · subst y
      have hur : u = r := by simpa using hy
      exact ⟨⟨x, r⟩, hx, hur.symm⟩
    · rw [QueryCache.cacheQuery_of_ne _ _ hyt] at hy
      exact (hc ⟨x, y, r, hxy, hx, hy⟩).elim

/-- The collision probability of an adaptive classical client is at most `q * (q / N)`.

Here `N = Nat.card R`, private uniform sampling is not counted, and the initial cache is empty.
-/
theorem prEvent_collision_le [SampleableType R]
    (oa : OracleComp (unifSpec + (D →ₒ R)) α) {q : Nat}
    (hq : IsQueryBoundP oa (fun t => t.isRight = true) q) :
    Pr{let z ← (simulateQ (D →ₒ R).romImpl oa).run ∅}[Collision z.2] ≤
      q * ((q : ℝ≥0∞) / Nat.card R) := by
  classical
  -- The budget bounds the cache only on reachable runs, so include it in the bad predicate.
  let P := fun c : (D →ₒ R).QueryCache => Collision c ∧ QueryCache.enncard c ≤ q
  have hfresh (t : D) (c : (D →ₒ R).QueryCache) (hc : ¬ P c) (ht : c t = none) :
      Pr{let u ← $ᵗ R}[P (c.cacheQuery t u)] ≤ (q : ℝ≥0∞) / Nat.card R := by
    by_cases hsize : QueryCache.enncard c ≤ q
    · have hnoc : ¬ Collision c := fun h => hc ⟨h, hsize⟩
      calc
        _ ≤ Pr{let u ← $ᵗ R}[u ∈ Sigma.snd '' c.toSet] :=
          prEvent_mono _ _ _ fun _ h => collision_cacheQuery hnoc ht h.1
        _ ≤ _ := by
          let : MeasurableSpace R := ⊤
          rw [prEvent_eq_evalDist_of_discrete]
          apply (SampleableType.evalDist_uniformSample_le_encard_div _).trans
          gcongr
          exact (ENat.toENNReal_le.mpr (Set.encard_image_le _ _)).trans hsize
    -- An oversized cache cannot re-enter the bounded bad predicate after another query.
    · have hfalse : ∀ u : R, ¬ P (c.cacheQuery t u) := by
        intro u h
        exact hsize ((QueryCache.enncard_mono
          (QueryCache.le_cacheQuery c ht)).trans h.2)
      simp only [hfalse, prEvent_false]
      exact zero_le
  have h := prEvent_run_le_of_fresh_bound_of_isQueryBoundP P
    (by simp [P, Collision]) ((q : ℝ≥0∞) / Nat.card R)
    (ENNReal.div_ne_top (by simp) (by exact_mod_cast (Nat.card_pos.ne' : Nat.card R ≠ 0)))
    hfresh oa hq
  -- Every reachable cache respects the budget, so the bounded event loses no collisions.
  exact (prEvent_mono_of_support _ _ _ fun z hz hc =>
    ⟨hc, enncard_le_of_mem_support_run_unifFwdImpl_add_randomOracle hq hz⟩).trans h

/-- An experiment: the adversary outputs a claim, then an extraction runs on it.

The extraction only calls the oracle. -/
def experimentWith {γ β : Type} (extraction : γ → OracleComp (D →ₒ R) β)
    (adversary : OracleComp (unifSpec + (D →ₒ R)) γ) : OracleComp (unifSpec + (D →ₒ R)) β := do
  let claim ← adversary
  liftComp (extraction claim) (unifSpec + (D →ₒ R))

omit [DecidableEq D] in
/-- The experiment makes the adversary's oracle calls and those of the extraction.

It needs the adversary to make at most `q` calls, and the extraction at most `n` on every claim. -/
theorem experimentWith_queryBound {γ β : Type} {extraction : γ → OracleComp (D →ₒ R) β}
    {adversary : OracleComp (unifSpec + (D →ₒ R)) γ} {q n : Nat}
    (hq : IsQueryBoundP adversary (fun t => t.isRight = true) q)
    (hn : ∀ claim, IsQueryBoundP (extraction claim) (fun _ => True) n) :
    IsQueryBoundP (experimentWith extraction adversary) (fun t => t.isRight = true) (q + n) :=
  isQueryBoundP_bind hq fun claim _ => IsQueryBoundP.liftComp_subSpec
    (fun _ => iff_of_true trivial rfl) (hn claim)

/-- A win of an experiment, at probability at most `q * (q / N)`.

Each replay of the extraction that ends in a win must expose a collision of the cache.

Here `N = Nat.card R`, and `q` bounds the oracle calls of the whole experiment, repeats included.

The initial cache is empty, and private uniform sampling is not counted. -/
theorem prEvent_experimentWith_le [SampleableType R] {γ β : Type}
    (extraction : γ → OracleComp (D →ₒ R) β) (wins : β → Prop)
    (collision : ∀ {cache : (D →ₒ R).QueryCache} {claim : γ} {outcome : β},
      simulateQ cache.toPartialImpl (extraction claim) = some outcome → wins outcome →
        Collision cache)
    (adversary : OracleComp (unifSpec + (D →ₒ R)) γ) {q : Nat}
    (hq : IsQueryBoundP (experimentWith extraction adversary) (fun t => t.isRight = true) q) :
    Pr{let z ← (simulateQ (D →ₒ R).romImpl (experimentWith extraction adversary)).run ∅}[
      wins z.1] ≤ q * ((q : ℝ≥0∞) / Nat.card R) := by
  refine (prEvent_mono_of_support _ _ _ ?_).trans
    (prEvent_collision_le (experimentWith extraction adversary) hq)
  intro z hz hwins
  simp only [experimentWith, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨claim, cache⟩, -, hz⟩ := hz
  -- The extraction calls only the oracle, which answers with caching.
  rw [QueryImpl.simulateQ_add_liftComp_right] at hz
  -- The final cache replays the extraction without sampling again.
  exact collision (QueryImpl.simulateQ_toPartialImpl_snd_of_mem_support_run_simulateQ_withCaching
    _ (extraction claim) hz) hwins

/-- The cache contains a query with the fixed target digest. -/
def Hits (r : R) (c : (D →ₒ R).QueryCache) : Prop := ∃ x, c x = some r

/-- A target digest fixed before the run has hit probability at most `q / N` in `q` queries.

Nothing here ties the target to the digest of any input.
-/
theorem prEvent_hits_le [SampleableType R]
    (r : R) (oa : OracleComp (unifSpec + (D →ₒ R)) α) {q : Nat}
    (hq : IsQueryBoundP oa (fun t => t.isRight = true) q) :
    Pr{let z ← (simulateQ (D →ₒ R).romImpl oa).run ∅}[Hits r z.2] ≤
      (q : ℝ≥0∞) / Nat.card R := by
  classical
  have hfresh (t : D) (c : (D →ₒ R).QueryCache) (hc : ¬ Hits r c) (_ht : c t = none) :
      Pr{let u ← $ᵗ R}[Hits r (c.cacheQuery t u)] ≤ 1 / (Nat.card R : ℝ≥0∞) := by
    calc
      _ ≤ Pr{let u ← $ᵗ R}[u = r] := prEvent_mono _ _ _ fun u ⟨x, hx⟩ => by
        by_cases hxt : x = t
        · subst x
          simpa using hx
        · rw [QueryCache.cacheQuery_of_ne _ _ hxt] at hx
          exact (hc ⟨x, hx⟩).elim
      _ = _ := by simp [SampleableType.prEvent_uniformSample_eq_singleton_natCard, one_div]
  have h := prEvent_run_le_of_fresh_bound_of_isQueryBoundP (Hits r)
    (by simp [Hits]) (1 / (Nat.card R : ℝ≥0∞))
    (ENNReal.div_ne_top (by simp) (by exact_mod_cast (Nat.card_pos.ne' : Nat.card R ≠ 0)))
    hfresh oa hq
  simpa [div_eq_mul_inv] using h

/-- An oracle input includes the parent position and its ordered children.

This models a node hash tweaked by its position.

A concrete hash matches it through an injective encoding of this tuple.

Such an encoding exists for levels and positions inside the encodable range.
-/
abbrev NodeInput (R : Type) := Nat × Nat × R × R

/-- Read a complete oracle table as a node hash in the identity monad. -/
def nodeHash (g : NodeInput R → R) (level j : Nat) (a b : R) : Id R :=
  pure (g (level, j, a, b))

/-- The same node hash, with calls exposed rather than answered by a fixed table. -/
def queryNode (level j : Nat) (a b : R) : OracleComp (NodeInput R →ₒ R) R :=
  liftM ((NodeInput R →ₒ R).query (level, j, a, b))

/-- One node-hash call costs one query. -/
theorem queryNode_queryBound (level j : Nat) (a b : R) :
    IsTotalQueryBound (queryNode level j a b) 1 := by
  change IsTotalQueryBound
    (liftM ((NodeInput R →ₒ R).query (level, j, a, b)) >>= pure) 1
  exact isTotalQueryBound_query_bind_iff.mpr ⟨Nat.one_pos, fun _ => trivial⟩

/-- A completed search whose two witness inputs were queried gives a cache collision.

The coverage hypothesis must include the search's queries, not only the adversary's queries.
-/
theorem collision_of_findCollision [DecidableEq R] (g : NodeInput R → R)
    (c : (NodeInput R →ₒ R).QueryCache) (p q : List R) (level j : Nat) (a b : R)
    (hcovered : ∀ w, findCollision (nodeHash g) level j a b p q = some w →
      c (w.level, w.j, w.x.1, w.x.2) = some (g (w.level, w.j, w.x.1, w.x.2)) ∧
      c (w.level, w.j, w.y.1, w.y.2) = some (g (w.level, w.j, w.y.1, w.y.2)))
    (h : (findCollision (nodeHash g) level j a b p q).isSome) : Collision c := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨hne, heq⟩ := (findCollision_valid (nodeHash g) p q level j a b w hw).1
  obtain ⟨hx, hy⟩ := hcovered w hw
  refine ⟨(w.level, w.j, w.x.1, w.x.2), (w.level, w.j, w.y.1, w.y.2),
    g (w.level, w.j, w.x.1, w.x.2), ?_, hx, ?_⟩
  · intro hxy
    exact hne (by simpa using congrArg (fun x : NodeInput R => x.2.2) hxy)
  · simpa [nodeHash] using hy.trans (congrArg some heq.symm)

/-- A second preimage search also gives a collision when both witness inputs were queried.

The honest children and their parent must be computed with the same oracle.
-/
theorem collision_of_findSecondPreimage [DecidableEq R] (g : NodeInput R → R)
    (c : (NodeInput R →ₒ R).QueryCache) (leaves : Nat → Id R)
    (q : List R) (level j : Nat) (b : R)
    (hcovered : ∀ w, findSecondPreimage (nodeHash g) leaves level j b q = some w →
      let x := ((node (nodeHash g) leaves w.level (2 * w.j)).run,
        (node (nodeHash g) leaves w.level (2 * w.j + 1)).run)
      c (w.level + 1, w.j, x.1, x.2) = some (g (w.level + 1, w.j, x.1, x.2)) ∧
      c (w.level + 1, w.j, w.y.1, w.y.2) =
        some (g (w.level + 1, w.j, w.y.1, w.y.2)))
    (h : (findSecondPreimage (nodeHash g) leaves level j b q).isSome) : Collision c := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨hne, heq⟩ := (findSecondPreimage_valid (nodeHash g) leaves q level j b w hw).1
  obtain ⟨hx, hy⟩ := hcovered w hw
  let x := ((node (nodeHash g) leaves w.level (2 * w.j)).run,
    (node (nodeHash g) leaves w.level (2 * w.j + 1)).run)
  refine ⟨(w.level + 1, w.j, w.y.1, w.y.2), (w.level + 1, w.j, x.1, x.2),
    g (w.level + 1, w.j, w.y.1, w.y.2), ?_, hy, ?_⟩
  · intro hxy
    exact hne (by simpa [x] using congrArg (fun z : NodeInput R => z.2.2) hxy)
  · change g (w.level + 1, w.j, w.y.1, w.y.2) =
        g (w.level + 1, w.j, x.1, x.2) at heq
    exact hx.trans (congrArg some heq.symm)

/-- The collision search against the oracle makes two calls per common level.

The bound holds even if the lists have different lengths. -/
theorem findCollision_queryBound [DecidableEq R] :
    ∀ (p q : List R) (level j : Nat) (a b : R),
      IsTotalQueryBound (findCollision queryNode level j a b p q)
        (2 * min p.length q.length) := by
  intro p
  induction p with
  | nil => intros; trivial
  | cons s p ih =>
    intro q level j a b
    cases q with
    | nil => trivial
    | cons t q =>
      simp only [List.length_cons, min_add_add_right,
        findCollision, queryNode, isTotalQueryBound_query_bind_iff]
      refine ⟨by omega, fun x => ⟨by omega, fun y => ?_⟩⟩
      split
      · trivial
      · convert ih q (level + 1) (j / 2) x y using 1
        omega

/-- Replaying a successful search from a cache exposes a collision in that cache. -/
theorem collision_of_partial_findCollision [DecidableEq R]
    (c : (NodeInput R →ₒ R).QueryCache) :
    ∀ (p q : List R) (level j : Nat) (a b : R) (w : Merkle.Collision R),
      simulateQ c.toPartialImpl (findCollision queryNode level j a b p q) = some (some w) →
        Collision c := by
  intro p
  induction p with
  | nil => intro q level j a b w hw; simp [findCollision] at hw
  | cons s p ih =>
    intro q level j a b w hw
    cases q with
    | nil => simp [findCollision] at hw
    | cons t q =>
      simp only [findCollision, queryNode, simulateQ_bind, simulateQ_spec_query,
        QueryCache.toPartialImpl_apply] at hw
      obtain ⟨x, hx, hw⟩ := Option.bind_eq_some_iff.mp hw
      obtain ⟨y, hy, hw⟩ := Option.bind_eq_some_iff.mp hw
      split at hw
      · rename_i h
        refine ⟨(level + 1, j / 2, (ordered j a s).1, (ordered j a s).2),
          (level + 1, j / 2, (ordered j b t).1, (ordered j b t).2), x, ?_, hx, ?_⟩
        · intro heq
          exact h.1 (by simpa using congrArg (fun z : NodeInput R => z.2.2) heq)
        · simpa [h.2] using hy
      · exact ih q _ _ x y w hw

/-- The birthday bound for a client without private sampling. -/
theorem prEvent_collision_le_total [SampleableType R]
    (oa : OracleComp (D →ₒ R) α) {q : Nat} (hq : IsTotalQueryBound oa q) :
    Pr{let z ← (simulateQ (D →ₒ R).randomOracle oa).run ∅}[Collision z.2] ≤
      q * ((q : ℝ≥0∞) / Nat.card R) := by
  have hb : IsQueryBoundP (liftComp oa (unifSpec + (D →ₒ R)))
      (fun t => t.isRight = true) q := by
    induction oa using OracleComp.inductionOn generalizing q with
    | pure x => trivial
    | query_bind t k ih =>
      rw [liftComp_bind, liftComp_query]
      change IsQueryBoundP
        (liftM ((unifSpec + (D →ₒ R)).query (.inr t)) >>= fun u =>
          liftComp (k u) (unifSpec + (D →ₒ R))) _ q
      exact ⟨Or.inr hq.1, fun u => ih u (hq.2 u)⟩
  have h := prEvent_collision_le (liftComp oa (unifSpec + (D →ₒ R))) hb
  simpa only [OracleSpec.romImpl, QueryImpl.simulateQ_add_liftComp_right] using h

/-- The collision search against the oracle succeeds with probability at most `(2h)^2 / N`.

Here `h` is the shorter path length, and the oracle cache starts empty.

The paths and leaves are fixed before the oracle is sampled.

Paths chosen after seeing oracle answers need the bound for covered events.
-/
theorem prEvent_findCollision_queryNode_le [SampleableType R] [DecidableEq R]
    (p q : List R) (level j : Nat) (a b : R) :
    Pr{let z ← (simulateQ (NodeInput R →ₒ R).randomOracle
      (findCollision queryNode level j a b p q)).run ∅}[z.1.isSome] ≤
        (2 * min p.length q.length : Nat) *
          ((2 * min p.length q.length : Nat) / (Nat.card R : ℝ≥0∞)) := by
  refine (prEvent_mono_of_support _ _ _ ?_).trans
    (prEvent_collision_le_total _ (findCollision_queryBound p q level j a b))
  intro z hz hs
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hs
  -- The final cache replays every query of this run without sampling again.
  have hp := QueryImpl.simulateQ_toPartialImpl_snd_of_mem_support_run_simulateQ_withCaching
    uniformSampleImpl (findCollision queryNode level j a b p q) hz
  rw [hw] at hp
  exact collision_of_partial_findCollision z.2 p q level j a b w hp

/-- The probability bound transfers to any event that returns a covered Merkle collision.

The budget covers the whole computation, including extraction and honest-tree construction.
-/
theorem prEvent_findCollision_le [SampleableType R] [DecidableEq R]
    (oa : OracleComp (unifSpec + (NodeInput R →ₒ R)) α) (event : α → Prop) {Q : Nat}
    (hQ : IsQueryBoundP oa (fun t => t.isRight = true) Q)
    (hsearch : ∀ z ∈ support ((simulateQ (NodeInput R →ₒ R).romImpl oa).run ∅),
      event z.1 → ∃ (g : NodeInput R → R) (p q : List R) (level j : Nat) (a b : R),
        (findCollision (nodeHash g) level j a b p q).isSome ∧
        ∀ w, findCollision (nodeHash g) level j a b p q = some w →
          z.2 (w.level, w.j, w.x.1, w.x.2) = some (g (w.level, w.j, w.x.1, w.x.2)) ∧
          z.2 (w.level, w.j, w.y.1, w.y.2) = some (g (w.level, w.j, w.y.1, w.y.2))) :
    Pr{let z ← (simulateQ (NodeInput R →ₒ R).romImpl oa).run ∅}[event z.1] ≤
      Q * ((Q : ℝ≥0∞) / Nat.card R) := by
  refine (prEvent_mono_of_support _ _ _ ?_).trans (prEvent_collision_le oa hQ)
  intro z hz he
  obtain ⟨g, p, q, level, j, a, b, hs, hc⟩ := hsearch z hz he
  exact collision_of_findCollision g z.2 p q level j a b hc hs

/-- A covered second preimage search has the same birthday bound.

Unlike a fixed target, its honest ancestor can depend on previous oracle answers.
-/
theorem prEvent_findSecondPreimage_le [SampleableType R] [DecidableEq R]
    (oa : OracleComp (unifSpec + (NodeInput R →ₒ R)) α) (event : α → Prop) {Q : Nat}
    (hQ : IsQueryBoundP oa (fun t => t.isRight = true) Q)
    (hsearch : ∀ z ∈ support ((simulateQ (NodeInput R →ₒ R).romImpl oa).run ∅),
      event z.1 → ∃ (g : NodeInput R → R) (leaves : Nat → Id R)
        (q : List R) (level j : Nat) (b : R),
        (findSecondPreimage (nodeHash g) leaves level j b q).isSome ∧
        ∀ w, findSecondPreimage (nodeHash g) leaves level j b q = some w →
          let x := ((node (nodeHash g) leaves w.level (2 * w.j)).run,
            (node (nodeHash g) leaves w.level (2 * w.j + 1)).run)
          z.2 (w.level + 1, w.j, x.1, x.2) = some (g (w.level + 1, w.j, x.1, x.2)) ∧
          z.2 (w.level + 1, w.j, w.y.1, w.y.2) =
            some (g (w.level + 1, w.j, w.y.1, w.y.2))) :
    Pr{let z ← (simulateQ (NodeInput R →ₒ R).romImpl oa).run ∅}[event z.1] ≤
      Q * ((Q : ℝ≥0∞) / Nat.card R) := by
  refine (prEvent_mono_of_support _ _ _ ?_).trans (prEvent_collision_le oa hQ)
  intro z hz he
  obtain ⟨g, leaves, q, level, j, b, hs, hc⟩ := hsearch z hz he
  exact collision_of_findSecondPreimage g z.2 leaves q level j b hc hs

/-- Computing an honest node from fixed leaves makes `2^level - 1` hash calls. -/
theorem node_queryBound (leaves : Nat → R) : ∀ level j,
    IsTotalQueryBound (node queryNode (fun j => pure (leaves j)) level j)
      (2 ^ level - 1) := by
  intro level
  induction level with
  | zero => intro j; trivial
  | succ level ih =>
    intro j
    rw [node_succ]
    have h := isTotalQueryBound_bind (ih (2 * j)) fun a =>
      isTotalQueryBound_bind (ih (2 * j + 1)) fun b =>
        queryNode_queryBound (level + 1) j a b
    convert h using 1
    have := Nat.one_le_two_pow (n := level)
    rw [Nat.pow_succ]
    omega

/-- Worst-case calls of the second-preimage search, including honest recomputation.

At each level it hashes the candidate and computes the two honest children and parent.

Repeated honest calls still count, even though the oracle answers them from its cache.

From level `l` over `n` siblings, the budget is `2^(l+n+2) - 2^(l+2) - 2n`.

The search queries at most `2^(l+n) - 1 + n` distinct inputs.

On a path of length at least 1, the budget is one to four times that count.

It nears four only for long paths.
-/
def secondPreimageQueries : Nat → Nat → Nat
  | _, 0 => 0
  | level, n + 1 =>
    1 + 2 * (2 ^ level - 1) + (2 ^ (level + 1) - 1) + secondPreimageQueries (level + 1) n

/-- The second-preimage search against the oracle respects its worst-case budget.

The honest leaves are fixed values, so reading a leaf makes no oracle call. -/
theorem findSecondPreimage_queryBound [DecidableEq R] (leaves : Nat → R) :
    ∀ (q : List R) (level j : Nat) (b : R),
      IsTotalQueryBound (findSecondPreimage queryNode (fun j => pure (leaves j)) level j b q)
        (secondPreimageQueries level q.length) := by
  intro q
  induction q with
  | nil => intros; trivial
  | cons t q ih =>
    intro level j b
    simp only [findSecondPreimage]
    have h := isTotalQueryBound_bind
      (queryNode_queryBound (level + 1) (j / 2) (ordered j b t).1 (ordered j b t).2)
      fun parent => isTotalQueryBound_bind (node_queryBound leaves level (2 * (j / 2)))
      fun left => isTotalQueryBound_bind (node_queryBound leaves level (2 * (j / 2) + 1))
      fun right => isTotalQueryBound_bind (node_queryBound leaves (level + 1) (j / 2))
      fun honest => show IsTotalQueryBound
        (if ordered j b t ≠ (left, right) ∧ parent = honest then
          pure (some ⟨level, j / 2, ordered j b t⟩)
        else findSecondPreimage queryNode (fun j => pure (leaves j)) (level + 1) (j / 2) parent q)
        (secondPreimageQueries (level + 1) q.length) from by
          split
          · trivial
          · exact ih _ _ _
    convert h using 1
    simp only [List.length_cons, secondPreimageQueries]
    omega

/-- Computing a node against a complete table gives the deterministic honest node. -/
theorem evalWithAnswerFn_node (g : NodeInput R → R) (leaves : Nat → R) : ∀ level j,
    evalWithAnswerFn (QueryImpl.ofFn g)
      (node queryNode (fun j => pure (leaves j)) level j) =
        (node (nodeHash g) (fun j => pure (leaves j)) level j).run := by
  intro level
  induction level with
  | zero => intro j; rfl
  | succ level ih =>
    intro j
    simp only [node, evalWithAnswerFn_bind, ih, queryNode,
      evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]
    rfl

/-- A fixed target is hit with probability at most `q / N`, among queried inputs.

The oracle answers only inputs other than one honest input.

The target `r` is fixed before the run.

As a second-preimage bound, `r` is the honest digest, and the other answers stay uniform.

That conditioning is a modelling step, not a proved one: nothing here ties `r` to that input.
-/
theorem prEvent_secondPreimage_le [SampleableType R] (honest : D) (r : R)
    (oa : OracleComp (unifSpec + ({x : D // x ≠ honest} →ₒ R)) α) {q : Nat}
    (hq : IsQueryBoundP oa (fun t => t.isRight = true) q) :
    Pr{let z ← (simulateQ ({x : D // x ≠ honest} →ₒ R).romImpl oa).run ∅}[∃ x,
      z.2 x = some r] ≤ (q : ℝ≥0∞) / Nat.card R :=
  prEvent_hits_le r oa hq

/-- A successful partial node computation caches its final parent call. -/
theorem cached_parent_of_partial_node (g : NodeInput R → R)
    (c : (NodeInput R →ₒ R).QueryCache) (hf : c.AgreesWithFn (QueryImpl.ofFn g))
    (leaves : Nat → R) (level j : Nat) (a : R)
    (ha : simulateQ c.toPartialImpl
      (node queryNode (fun j => pure (leaves j)) (level + 1) j) = some a) :
    c (level + 1, j,
      (node (nodeHash g) (fun j => pure (leaves j)) level (2 * j)).run,
      (node (nodeHash g) (fun j => pure (leaves j)) level (2 * j + 1)).run) = some a := by
  simp only [node_succ, simulateQ_bind] at ha
  obtain ⟨left, hl, ha⟩ := Option.bind_eq_some_iff.mp ha
  obtain ⟨right, hr, ha⟩ := Option.bind_eq_some_iff.mp ha
  have hleft := c.evalWithAnswerFn_eq_of_agreesWithFn hf _ hl
  have hright := c.evalWithAnswerFn_eq_of_agreesWithFn hf _ hr
  rw [evalWithAnswerFn_node] at hleft hright
  simp only [queryNode, simulateQ_spec_query, QueryCache.toPartialImpl_apply] at ha
  rwa [← hleft, ← hright] at ha

/-- A successful partial second-preimage search exposes two distinct cached inputs. -/
theorem collision_of_partial_findSecondPreimage [SampleableType R] [DecidableEq R]
    (c : (NodeInput R →ₒ R).QueryCache) (leaves : Nat → R) :
    ∀ (q : List R) (level j : Nat) (b : R) (w : SecondPreimage R),
      simulateQ c.toPartialImpl
        (findSecondPreimage queryNode (fun j => pure (leaves j)) level j b q) = some (some w) →
        Collision c := by
  -- Complete the cache only to identify the repeated honest-child computations.
  obtain ⟨g, hg⟩ := c.exists_agreesWithFn
  intro q
  induction q with
  | nil => intro level j b w hw; simp [findSecondPreimage] at hw
  | cons t q ih =>
    intro level j b w hw
    simp only [findSecondPreimage, simulateQ_bind] at hw
    obtain ⟨parent, hp, hw⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨left, hl, hw⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨right, hr, hw⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨honest, hh, hw⟩ := Option.bind_eq_some_iff.mp hw
    split at hw
    · rename_i h
      have hg' : c.AgreesWithFn (QueryImpl.ofFn (fun t => g t)) := hg
      have hleft := c.evalWithAnswerFn_eq_of_agreesWithFn hg' _ hl
      have hright := c.evalWithAnswerFn_eq_of_agreesWithFn hg' _ hr
      rw [evalWithAnswerFn_node] at hleft hright
      have hc := cached_parent_of_partial_node (fun t => g t) c hg leaves
        level (j / 2) honest hh
      rw [hleft, hright] at hc
      refine ⟨(level + 1, j / 2, (ordered j b t).1, (ordered j b t).2),
        (level + 1, j / 2, left, right), parent, ?_, ?_, ?_⟩
      · intro heq
        exact h.1 (by simpa using congrArg (fun z : NodeInput R => z.2.2) heq)
      · simpa [queryNode, simulateQ_spec_query, QueryCache.toPartialImpl_apply] using hp
      · simpa [h.2] using hc
    · exact ih _ _ parent w hw

/-- The second-preimage search against the oracle has the birthday bound at its full budget.

The bound includes recomputing honest ancestors, rather than treating them as fixed targets.

The path and leaves are fixed before the oracle is sampled.

A path chosen after seeing oracle answers needs the bound for covered events.
-/
theorem prEvent_findSecondPreimage_queryNode_le [SampleableType R] [DecidableEq R]
    (leaves : Nat → R) (q : List R) (level j : Nat) (b : R) :
    Pr{let z ← (simulateQ (NodeInput R →ₒ R).randomOracle
      (findSecondPreimage queryNode (fun j => pure (leaves j)) level j b q)).run ∅}[z.1.isSome] ≤
        (secondPreimageQueries level q.length : ℝ≥0∞) *
          ((secondPreimageQueries level q.length : ℝ≥0∞) / Nat.card R) := by
  refine (prEvent_mono_of_support _ _ _ ?_).trans
    (prEvent_collision_le_total _ (findSecondPreimage_queryBound leaves q level j b))
  intro z hz hs
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hs
  have hp := QueryImpl.simulateQ_toPartialImpl_snd_of_mem_support_run_simulateQ_withCaching
    uniformSampleImpl (findSecondPreimage queryNode (fun j => pure (leaves j)) level j b q) hz
  rw [hw] at hp
  exact collision_of_partial_findSecondPreimage z.2 leaves q level j b w hp

/-- There are `2^256` digests of 32 bytes. -/
theorem card_bytes32 : Nat.card (Vector UInt8 32) = 2 ^ 256 := by
  rw [Nat.card_congr (arrayVectorEquivFin UInt8 32), Nat.card_fun,
    Nat.card_eq_fintype_card (α := UInt8), ← FinEnum.card_eq_fintypeCard, FinEnum.card_UInt8]
  simp

end EthLib.Cryptography.Merkle.RandomOracle
