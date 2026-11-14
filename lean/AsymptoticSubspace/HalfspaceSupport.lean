module

public import AsymptoticSubspace.HalfspaceZoneProofCore
public import AsymptoticSubspace.AveragingHulls

/-! The supporting-level consequence of half-space attraction used in Lemma 10. -/

@[expose] public section

noncomputable section

namespace AsymptoticSubspace.ModelLemmas

open Set ComputationalModel PaperFormalization

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {n : ℕ}

/-- Apply Lemma 5 to the open half-space beyond the supporting level `l b`.
All broadcasting values lie at the common level `l p`. -/
lemma support_bound_of_halfspace_zone
    (E : AveragingExecution (V := V) n) (M : Round → Finset (Proc n))
    (α : ℝ) (t : ℕ) (hα : 0 < α) (hmbw : MinimumBroadcastWeight E M α)
    (l : V →ₗ[ℝ] ℝ) (hl : l ≠ 0) (p b : V)
    (hp : p ∈ PolyOn E t (M (t + 1)))
    (hconst : ∀ x ∈ PolyOn E t (M (t + 1)), l x = l p)
    (hmax : ∀ x ∈ Poly E t, l x ≤ l b) :
    ∀ x ∈ Poly E (t + 1), l x ≤ α * l p + (1 - α) * l b := by
  let v := -(InnerProductSpace.toDual ℝ V).symm l.toContinuousLinearMap
  have hinner (x : V) : inner ℝ (x - b) v = l b - l x := by
    rw [real_inner_comm]
    simp only [v, inner_neg_left, InnerProductSpace.toDual_symm_apply,
      map_sub]
    change -(l x - l b) = l b - l x
    ring
  have hv : v ≠ 0 := by
    intro hv
    apply hl
    ext x
    have h := hinner (x + b)
    simpa [hv] using h
  let H := {x : V | inner ℝ (x - b) v < 0}
  have houtside (x : V) (hx : x ∈ Poly E t) : x ∉ H := by
    change ¬ inner ℝ (x - b) v < 0
    rw [hinner]
    linarith [hmax x hx]
  have hprev : Values E t ∩ H = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    exact fun x hx => houtside x (subset_convexHull ℝ _ hx.1) hx.2
  have hdist (x : V) (hx : x ∈ Poly E t) :
      Metric.infDist x H = (l b - l x) / ‖v‖ := by
    rw [lemma_halfspace_distance_formula hv (houtside x hx), hinner]
  have hsub : PolyOn E t (M (t + 1)) ⊆ Poly E t := by
    apply convexHull_mono
    rintro x ⟨j, _, rfl⟩
    exact ⟨j, rfl⟩
  have hbroadcast : setDistTo (PolyOn E t (M (t + 1))) H = (l b - l p) / ‖v‖ := by
    unfold setDistTo
    have heq : (fun x => Metric.infDist x H) '' PolyOn E t (M (t + 1)) =
        {(l b - l p) / ‖v‖} := by
      apply eq_singleton_iff_unique_mem.mpr
      refine ⟨⟨p, hp, hdist p (hsub hp)⟩, ?_⟩
      rintro y ⟨x, hx, rfl⟩
      change Metric.infDist x H = (l b - l p) / ‖v‖
      rw [hdist x (hsub hx), hconst x hx]
    rw [heq, csInf_singleton]
  have hattract := lemma_halfspace_zone E M α t b v hα hv hmbw hprev
  rw [hbroadcast] at hattract
  apply convexHull_min _ (convex_halfSpace_le l.isLinear (α * l p + (1 - α) * l b))
  rintro x ⟨i, rfl⟩
  have hpoint : setDistTo (Values E (t + 1)) H ≤ Metric.infDist (E.outputs (t + 1) i) H := by
    unfold setDistTo
    refine csInf_le ?_ ⟨E.outputs (t + 1) i, ⟨i, rfl⟩, rfl⟩
    refine ⟨0, ?_⟩
    rintro y ⟨z, _, rfl⟩
    exact Metric.infDist_nonneg
  have hle := hattract.trans hpoint
  rw [hdist _ (output_succ_mem_poly E t i)] at hle
  have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hmul := (div_le_div_iff_of_pos_right hnorm).mp
    (show (α * (l b - l p)) / ‖v‖ ≤ (l b - l (E.outputs (t + 1) i)) / ‖v‖ by
      simpa only [mul_div_assoc] using hle)
  change l (E.outputs (t + 1) i) ≤ α * l p + (1 - α) * l b
  linarith

end AsymptoticSubspace.ModelLemmas
