import AsymptoticSubspace.ModelBridgeCore

/-! Convex-hull invariance, nestedness, and validity for averaging executions. -/

noncomputable section

namespace AsymptoticSubspace

open Set ComputationalModel ModelLemmas

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {n : ℕ}

lemma output_succ_mem_poly
    (E : AveragingExecution (V := V) n)
    (t : Round) (i : Proc n) :
    E.outputs (t + 1) i ∈ Poly E t := by
  let f : Proc n → ℝ := fun j => E.weights (t + 1) i j
  let z : Proc n → V := fun j => E.outputs t j
  let ξ : V := Finset.univ.centerMass f z
  have hξ_mem : ξ ∈ Poly E t := by
    have hw0 : ∀ j ∈ (Finset.univ : Finset (Proc n)), 0 ≤ f j := by
      intro j _hj
      exact E.weight_nonneg (t + 1) i j
    have hsum_pos : 0 < Finset.sum (Finset.univ : Finset (Proc n)) (fun j => f j) := by
      have hsum_one : Finset.sum (Finset.univ : Finset (Proc n)) (fun j => f j) = 1 := by
        simpa [f] using E.weights_sum_one (t + 1) i
      linarith
    have hz : ∀ j ∈ (Finset.univ : Finset (Proc n)), z j ∈ Values E t := by
      intro j _hj
      exact ⟨j, rfl⟩
    have hcm :
        ξ ∈ convexHull ℝ (Values E t) := by
      simpa [ξ, f, z, ModelLemmas.Values] using
        (Finset.centerMass_mem_convexHull
          (R := ℝ) (E := V) (t := (Finset.univ : Finset (Proc n)))
          (w := f) hw0 hsum_pos (z := z) hz)
    simpa [ModelLemmas.Poly] using hcm
  have hξ_eq : ξ = E.outputs (t + 1) i := by
    calc
      ξ = (Finset.sum (Finset.univ : Finset (Proc n)) (fun j => f j))⁻¹ •
            Finset.sum (Finset.univ : Finset (Proc n)) (fun j => f j • z j) := rfl
      _ = (1 : ℝ)⁻¹ •
            Finset.sum (Finset.univ : Finset (Proc n)) (fun j => f j • z j) := by
            simp [f, E.weights_sum_one (t + 1) i]
      _ = Finset.sum (Finset.univ : Finset (Proc n)) (fun j => f j • z j) := by simp
      _ = E.outputs (t + 1) i := by
            simpa [f, z] using (E.output_succ_eq_weighted_sum t i).symm
  simpa [hξ_eq] using hξ_mem

namespace ModelLemmas

/--
Validity in set-convergence form for averaging executions:
each trajectory stays in the convex hull of round-0 outputs, hence converges to that set.
-/
theorem averaging_validityAtLimit [NeZero n]
    (E : AveragingExecution (V := V) n) :
    ∀ i : Proc n,
      ConvergesToSet
        (fun t => E.outputs t i)
        (convexHull ℝ (Set.range (E.outputs 0))) := by
  have hmem_all :
      ∀ t : Round, ∀ i : Proc n,
        E.outputs t i ∈ convexHull ℝ (Set.range (E.outputs 0)) := by
    intro t
    induction t with
    | zero =>
        intro i
        exact subset_convexHull ℝ (Set.range (E.outputs 0)) ⟨i, rfl⟩
    | succ t iht =>
        intro i
        have hsucc : E.outputs (t + 1) i ∈ Poly E t :=
          output_succ_mem_poly (E := E) t i
        have hValues_subset : Values E t ⊆ convexHull ℝ (Set.range (E.outputs 0)) := by
          intro x hx
          rcases hx with ⟨j, rfl⟩
          exact iht j
        have hPoly_subset : Poly E t ⊆ convexHull ℝ (Set.range (E.outputs 0)) :=
          convexHull_min hValues_subset (convex_convexHull ℝ (Set.range (E.outputs 0)))
        exact hPoly_subset hsucc
  intro i
  refine ⟨?_, ?_⟩
  · refine ⟨E.outputs 0 i, ?_⟩
    exact hmem_all 0 i
  · intro ε hε
    refine ⟨0, ?_⟩
    intro t _ht
    have hmem : E.outputs t i ∈ convexHull ℝ (Set.range (E.outputs 0)) := hmem_all t i
    have hlt :
        Metric.infDist (E.outputs t i) (convexHull ℝ (Set.range (E.outputs 0))) < ε := by
      refine (Metric.infDist_lt_iff ?_).2 ?_
      · exact ⟨E.outputs 0 i, hmem_all 0 i⟩
      · refine ⟨E.outputs t i, hmem, ?_⟩
        simpa using hε
    exact hlt

lemma output_mem_poly_self [NeZero n]
    (E : AveragingExecution (V := V) n)
    (t : Round) (i : Proc n) :
    E.outputs t i ∈ Poly E t := by
  exact subset_convexHull ℝ (Values E t) ⟨i, rfl⟩

lemma poly_succ_subset [NeZero n]
    (E : AveragingExecution (V := V) n)
    (t : Round) :
    Poly E (t + 1) ⊆ Poly E t := by
  have hValues_subset : Values E (t + 1) ⊆ Poly E t := by
    intro x hx
    rcases hx with ⟨i, rfl⟩
    exact output_succ_mem_poly (E := E) t i
  exact convexHull_min hValues_subset (convex_convexHull ℝ (Values E t))

lemma poly_antitone [NeZero n]
    (E : AveragingExecution (V := V) n) :
    Antitone (fun t => Poly E t) := by
  intro t s hts
  induction hts with
  | refl =>
      intro x hx
      simpa using hx
  | @step s _ ih =>
      exact Set.Subset.trans (poly_succ_subset (E := E) (t := s)) ih

end ModelLemmas

end AsymptoticSubspace
