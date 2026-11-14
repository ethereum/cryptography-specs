module

public import EthLib.Cryptography.Proofs.EvalDistEq
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic

/-!
# Proofs: lazy random oracles, uniform tables and independent draws

A lazy random oracle samples an answer the first time it sees an input, and caches it.

For a list of queries, its answers are the cached ones, and otherwise reads of one uniform table.

Independent uniform samples are equal in distribution to reads of a uniform table at distinct cells.

A uniform table of vectors, read at distinct (cell, position) pairs, gives a uniform table.

Independent computations give a list of values with the product of their probabilities.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

/-- Reads through a lazy random oracle equal cached answers, else reads of a uniform table.

Two elements must query the same input exactly when they read the same cell. -/
theorem run_mapM_query_evalDistEq {D R α β : Type} [DecidableEq D] [SampleableType R]
    {N : Nat} [SampleableType (Fin N → R)] (q : α → D) (g : α → Fin N) (f : α → R → β)
    (L : List α) (same : ∀ x ∈ L, ∀ y ∈ L, q x = q y ↔ g x = g y)
    (cache : (D →ₒ R).QueryCache) :
    ((simulateQ (D →ₒ R).randomOracle
      (L.mapM fun x => f x <$> liftM ((D →ₒ R).query (q x)))).run' cache) =ᵈ
      ((fun T : Fin N → R => L.map fun x => f x ((cache (q x)).getD (T (g x)))) <$>
        ($ᵗ (Fin N → R))) := by
  induction L generalizing cache with
  | nil =>
    simp only [List.mapM_nil, simulateQ_pure, StateT.run'_pure', List.map_nil]
    exact (EvalDistEq.map_const _ _).symm
  | cons x L ih =>
    have rest := ih fun a ha b hb =>
      same a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb)
    simp only [List.mapM_cons, simulateQ_bind, simulateQ_map, simulateQ_pure, simulateQ_spec_query,
      StateT.run'_eq, StateT.run_bind, StateT.run_map, randomOracle.run_eq]
    cases hc : cache (q x) with
    | some u =>
      refine (EvalDistEq.of_eq ?_).trans
        (((rest cache).map (List.cons (f x u))).trans (EvalDistEq.of_eq ?_))
      · simp [StateT.run'_eq]
      · simp [hc, Functor.map_map]
    | none =>
      -- A fresh answer is the cell of its input in a uniform table, overwritten by the answer.
      have later (u : R) (T : Fin N → R) : (L.map fun y =>
          f y (((cache.cacheQuery (q x) u) (q y)).getD (T (g y)))) =
          L.map fun y => f y ((cache (q y)).getD (Function.update T (g x) u (g y))) := by
        refine List.map_congr_left fun y hy => ?_
        by_cases shared : g y = g x
        · have query : q y = q x :=
            (same y (List.mem_cons_of_mem x hy) x List.mem_cons_self).mpr shared
          rw [shared, Function.update_self]
          generalize q y = t at query ⊢
          subst query
          simp [hc, QueryCache.cacheQuery_self]
        · have query : q y ≠ q x := fun h =>
            shared ((same y (List.mem_cons_of_mem x hy) x List.mem_cons_self).mp h)
          simp [QueryCache.cacheQuery_of_ne _ _ query, Function.update_of_ne shared]
      calc
        _ = ($ᵗ R >>= fun u => List.cons (f x u) <$>
            (simulateQ (D →ₒ R).randomOracle
              (L.mapM fun x => f x <$> liftM ((D →ₒ R).query (q x)))).run'
                (cache.cacheQuery (q x) u)) := by
          simp [StateT.run'_eq]
        _ =ᵈ ($ᵗ R >>= fun u => List.cons (f x u) <$>
            ((fun T : Fin N → R => L.map fun y =>
              f y (((cache.cacheQuery (q x) u) (q y)).getD (T (g y)))) <$> ($ᵗ (Fin N → R)))) :=
          EvalDistEq.bind_right _ fun u => (rest _).map _
        _ = ($ᵗ R >>= fun u => $ᵗ (Fin N → R) >>= fun T =>
            pure ((x :: L).map fun y =>
              f y ((cache (q y)).getD (Function.update T (g x) u (g y))))) := by
          simp [later, hc, map_eq_bind_pure_comp]
        _ =ᵈ ($ᵗ (Fin N → R) >>= fun T =>
            pure ((x :: L).map fun y => f y ((cache (q y)).getD (T (g y))))) :=
          evalDistEq_uniformSample_bind_update (g x)
            (fun T => pure ((x :: L).map fun y => f y ((cache (q y)).getD (T (g y)))))
        _ = _ := by rw [map_eq_bind_pure_comp]; rfl

/-- Independent uniform samples equal reads of a uniform table at distinct cells. -/
theorem mapM_uniformSample_evalDistEq {R α β : Type} [SampleableType R] {N : Nat}
    [SampleableType (Fin N → R)] (g : α → Fin N) (f : α → R → β) (L : List α)
    (distinct : (L.map g).Nodup) :
    (L.mapM fun x => f x <$> ($ᵗ R)) =ᵈ
      ((fun T : Fin N → R => L.map fun x => f x (T (g x))) <$> ($ᵗ (Fin N → R))) := by
  induction L with
  | nil =>
    simp only [List.mapM_nil, List.map_nil]
    exact (EvalDistEq.map_const _ _).symm
  | cons x L ih =>
    rw [List.map_cons, List.nodup_cons] at distinct
    -- The cell of the first sample is read by no later sample.
    have later (u : R) (T : Fin N → R) : (L.map fun y => f y (T (g y))) =
        L.map fun y => f y (Function.update T (g x) u (g y)) := by
      refine List.map_congr_left fun y hy => ?_
      have other : g y ≠ g x := fun h => distinct.1 (h ▸ List.mem_map_of_mem hy)
      rw [Function.update_of_ne other]
    calc
      _ = ($ᵗ R >>= fun u => List.cons (f x u) <$> L.mapM fun x => f x <$> ($ᵗ R)) := by
        simp [map_eq_bind_pure_comp]
      _ =ᵈ ($ᵗ R >>= fun u => List.cons (f x u) <$>
          ((fun T : Fin N → R => L.map fun y => f y (T (g y))) <$> ($ᵗ (Fin N → R)))) :=
        EvalDistEq.bind_right _ fun u => (ih distinct.2).map _
      _ = ($ᵗ R >>= fun u => $ᵗ (Fin N → R) >>= fun T =>
          pure ((x :: L).map fun y => f y (Function.update T (g x) u (g y)))) := by
        simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply,
          List.map_cons, Function.update_self]
        exact bind_congr fun u => bind_congr fun T => by rw [later u T]
      _ =ᵈ ($ᵗ (Fin N → R) >>= fun T => pure ((x :: L).map fun y => f y (T (g y)))) :=
        evalDistEq_uniformSample_bind_update (g x)
          (fun T => pure ((x :: L).map fun y => f y (T (g y))))
      _ = _ := by rw [map_eq_bind_pure_comp]; rfl

/-- Reads of a uniform table of vectors at distinct (cell, position) pairs form a uniform table. -/
theorem evalDistEq_uniformSample_table_reads {R A : Type} [Finite A] [SampleableType R]
    {B m : Nat} [SampleableType (Fin B → Vector R m)] [SampleableType (A → R)]
    {e : A → Fin B × Fin m} (he : Function.Injective e) :
    ((fun T : Fin B → Vector R m => fun a => (T (e a).1)[(e a).2.val]) <$>
      ($ᵗ (Fin B → Vector R m))) =ᵈ ($ᵗ (A → R)) := by
  let flat : (Fin B → Vector R m) ≃ (Fin B × Fin m → R) :=
    (Equiv.arrowCongr (Equiv.refl _) (arrayVectorEquivFin R m)).trans
      (Equiv.curry (Fin B) (Fin m) R).symm
  let : SampleableType (Fin B × Fin m → R) := SampleableType.ofEquiv flat
  calc
    _ =ᵈ ((fun W : Fin B × Fin m → R => W ∘ e) <$> (flat <$> ($ᵗ (Fin B → Vector R m)))) := by
      simp only [Functor.map_map]
      exact EvalDistEq.rfl
    _ =ᵈ ((fun W : Fin B × Fin m → R => W ∘ e) <$> ($ᵗ (Fin B × Fin m → R))) :=
      (SampleableType.map_uniformSample_evalDistEq_of_bijective flat.bijective).map _
    _ =ᵈ ($ᵗ (A → R)) := evalDistEq_uniformSample_map_comp_injective he

/-- Independent computations give a list of values with the product of their probabilities. -/
theorem prEvent_mapM_eq_map {α γ : Type} (m : α → ProbComp γ) (v : α → γ) (L : List α) :
    Pr{let z ← L.mapM m}[z = L.map v] = (L.map fun x => Pr{let y ← m x}[y = v x]).prod := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.mapM_cons, List.map_cons, List.map_cons, List.prod_cons, ← ih]
    simp [List.cons.injEq]

/-- Independent computations meet a pointwise relation with the product of the chances. -/
theorem prEvent_mapM_forall₂ {α γ : Type} (m : α → ProbComp γ) (P : α → γ → Prop)
    (L : List α) :
    Pr{let z ← L.mapM m}[List.Forall₂ P L z] = (L.map fun x => Pr{let y ← m x}[P x y]).prod := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.mapM_cons, List.map_cons, List.prod_cons, ← ih]
    simp [List.forall₂_cons]
