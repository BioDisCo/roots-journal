-- Internal plumbing module.
-- Reader-facing statement is in `ThmSolving.lean`.
module

public import AsymptoticSubspace.LemDeltaContraction
public import AsymptoticSubspace.NestedHulls

@[expose] public section

noncomputable section

namespace AsymptoticSubspace
namespace ThmSolving

open Set
open ComputationalModel
open ModelLemmas

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {n : Nat}

section ProjectionHelpers

lemma proj_dist_le_thickness_of_mem_poly [NeZero n]
    (Pi : V →L[ℝ] V)
    (E : AveragingExecution (V := V) n)
    (t : Round)
    {x y : V}
    (hx : x ∈ Poly E t)
    (hy : y ∈ Poly E t) :
    dist (Pi x) (Pi y) ≤ thicknessAt Pi E t := by
  classical
  have hXt : (outputSet E t).Nonempty := outputSet_nonempty (E := E) t
  have hbound :
      ‖Pi (x - y)‖ ≤ thicknessOn Pi (outputSet E t) hXt :=
    diffSet_poly_norm_bound (P := Pi) (E := E) (t := t) hXt (x - y)
      ⟨x, hx, y, hy, rfl⟩
  calc
    dist (Pi x) (Pi y) = ‖Pi (x - y)‖ := by
      simp [dist_eq_norm, map_sub]
    _ ≤ thicknessOn Pi (outputSet E t) hXt := hbound
    _ = thicknessAt Pi E t := by
      symm
      exact thicknessAt_eq (P := Pi) (E := E) (t := t) hXt

end ProjectionHelpers

section ProjectedLimit

/-- The diameter of the projected hull is exactly the thickness of the outputs. -/
lemma projected_poly_diam
    (Pi : V →L[ℝ] V) (E : AveragingExecution (V := V) n) (t : Round) :
    Metric.diam (Pi '' Poly E t) = thicknessAt Pi E t := by
  exact thickness_convexHull Pi (Set.range (E.outputs t))

/-- The nonempty nested projected hulls have a singleton intersection when
their diameters tend to zero. The point belongs to every projected hull. -/
lemma projected_poly_inter_eq_singleton [NeZero n]
    (Pi : V →L[ℝ] V) (E : AveragingExecution (V := V) n)
    (hthick : ConvergesTo (fun t => thicknessAt Pi E t) 0) :
    ∃ c : V, (⋂ t, Pi '' Poly E t) = {c} := by
  classical
  have hcompact (t) : IsCompact (Pi '' Poly E t) :=
    (poly_compact E t).image Pi.continuous
  obtain ⟨c, hc⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun t => Pi '' Poly E t)
    (fun t => image_mono (poly_succ_subset E t))
    (fun t => ⟨Pi (E.outputs t 0), mem_image_of_mem Pi (output_mem_poly_self E t 0)⟩)
    (hcompact 0) (fun t => (hcompact t).isClosed)
  refine ⟨c, Set.eq_singleton_iff_unique_mem.mpr ⟨hc, ?_⟩⟩
  intro x hx
  apply dist_eq_zero.mp
  apply le_antisymm ?_ dist_nonneg
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨T, hT⟩ := hthick ε hε
  have hdist := Metric.dist_le_diam_of_mem (hcompact T).isBounded
    (mem_iInter.mp hx T) (mem_iInter.mp hc T)
  rw [projected_poly_diam] at hdist
  have hsmall := hT T le_rfl
  have : thicknessAt Pi E T < ε := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (thicknessAt_nonneg Pi E T)] using hsmall
  simpa using (hdist.trans this.le)

/-- An orthogonal projection's fiber over a point in its image is the translate
of its kernel, and distance to that fiber is the projected distance. -/
lemma projection_fiber_distance [FiniteDimensional ℝ V]
    (K : Submodule ℝ V) (c : V) (hc : K.starProjection c = c) :
    let W := AffineSubspace.mk' c (LinearMap.ker (K.starProjection : V →ₗ[ℝ] V))
    (W : Set V) = {x | K.starProjection x = c} ∧
      ∀ x, Metric.infDist x (W : Set V) = ‖K.starProjection x - c‖ := by
  dsimp only
  let W := AffineSubspace.mk' c (LinearMap.ker (K.starProjection : V →ₗ[ℝ] V))
  have hfiber : (W : Set V) = {x | K.starProjection x = c} := by
    ext x
    change K.starProjection (x - c) = 0 ↔ K.starProjection x = c
    rw [map_sub, hc, sub_eq_zero]
  refine ⟨hfiber, fun x => le_antisymm ?_ ?_⟩
  · let w := x - K.starProjection x + c
    have hw : w ∈ W := by
      change w ∈ (W : Set V)
      rw [hfiber]
      change K.starProjection (x - K.starProjection x + c) = c
      rw [map_add, map_sub, hc, K.starProjection_eq_self_iff.mpr
        (K.starProjection_apply_mem x), sub_self, zero_add]
    calc
      Metric.infDist x (W : Set V) ≤ dist x w := Metric.infDist_le_dist_of_mem hw
      _ = ‖K.starProjection x - c‖ := by
        rw [dist_eq_norm]
        congr 1
        dsimp [w]
        abel
  · apply (Metric.le_infDist ⟨c, by rw [hfiber]; exact hc⟩).mpr
    intro y hy
    have hy' : K.starProjection y = c := by
      change y ∈ (W : Set V) at hy
      rwa [hfiber] at hy
    simpa [dist_eq_norm, map_sub, hy'] using K.norm_starProjection_apply_le (x - y)

end ProjectedLimit

/-- Theorem 13: shrinking projected hulls give convergence to an affine subspace
of dimension at most `k - 1`. The public theorem enlarges it to exact dimension. -/
theorem theorem_solving_core [NeZero n]
    [FiniteDimensional ℝ V]
    (d k : Nat) (_hdk : k ≤ d) (hk : 1 ≤ k)
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (α : ℝ) (hα_pos : 0 < α)
    (hmbw : MinimumBroadcastWeight (V := V) E M α)
    (hcard : ∀ t, (M t).card ≤ k)
    (_hdim : Module.finrank ℝ V = d) :
    ∃ (W : AffineSubspace ℝ V),
      Module.finrank ℝ W.direction ≤ k - 1 ∧
      (∀ i : Proc n, ConvergesToSet (fun t => E.outputs t i) (W : Set V)) ∧
    (∀ i : Proc n,
      ConvergesToSet
        (fun t => E.outputs t i)
        (convexHull ℝ (Set.range (E.outputs 0)))) := by
  classical
  let : DecidableEq V := Classical.decEq V
  rcases lemma_Delta_contraction (V := V) k hk E M α hα_pos hmbw hcard with
    ⟨Pi0, hPiStar0, hkerPi0, hthick0⟩
  rcases (isStarProjection_iff_eq_starProjection.mp hPiStar0) with ⟨K, _hK, hPiEq⟩
  subst Pi0
  let Pi : V →L[ℝ] V := K.starProjection
  have hkerPi : Module.finrank ℝ (LinearMap.ker (Pi : V →ₗ[ℝ] V)) ≤ k - 1 := by
    simpa [Pi] using hkerPi0
  have hthick : ConvergesTo (fun t => thicknessAt Pi E t) 0 := by
    simpa [Pi] using hthick0
  obtain ⟨c, hc⟩ := projected_poly_inter_eq_singleton Pi E hthick
  have hc_mem (t) : c ∈ Pi '' Poly E t := by
    apply mem_iInter.mp (show c ∈ ⋂ t, Pi '' Poly E t from by rw [hc]; simp) t
  have hPc : Pi c = c := by
    obtain ⟨x, _, hx⟩ := hc_mem 0
    rw [← hx]
    exact K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem x)
  let W := AffineSubspace.mk' c (LinearMap.ker (Pi : V →ₗ[ℝ] V))
  obtain ⟨hfiber, hdist⟩ := projection_fiber_distance K c hPc
  refine ⟨W, ?_, ?_, averaging_validityAtLimit E⟩
  · have hWdir : W.direction = LinearMap.ker (Pi : V →ₗ[ℝ] V) := by
      simp [W, AffineSubspace.direction_mk']
    rw [hWdir]
    exact hkerPi
  · intro i
    refine ⟨⟨c, by simp [W]⟩, ?_⟩
    intro ε hε
    obtain ⟨T, hT⟩ := hthick ε hε
    refine ⟨T, fun t ht => ?_⟩
    have hbound : ‖Pi (E.outputs t i) - c‖ ≤ thicknessAt Pi E t := by
      rw [← projected_poly_diam]
      simpa only [dist_eq_norm] using
        Metric.dist_le_diam_of_mem ((poly_compact E t).image Pi.continuous).isBounded
        (mem_image_of_mem Pi (output_mem_poly_self E t i)) (hc_mem t)
    rw [hdist]
    exact hbound.trans_lt (by
      simpa [Real.norm_eq_abs, abs_of_nonneg (thicknessAt_nonneg Pi E t)] using hT t ht)

end ThmSolving
end AsymptoticSubspace
