-- TeX label: lem:continuity
module

public import AsymptoticSubspace.Thickness
public import Mathlib.Analysis.Normed.Operator.Basic

/-! Lemma 18: Lipschitz continuity of thickness. -/

@[expose] public section

noncomputable section

namespace AsymptoticSubspace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Lemma 18: the inverse triangle inequality and operator norm bound,
maximized over the nonempty compact set, give the thickness estimate. -/
theorem lemma_continuity
    (X : Set V) (hX : IsCompact X) (hne : X.Nonempty)
    (P Q : V →L[ℝ] V) :
    |thickness P X - thickness Q X| ≤ ‖P - Q‖ * Metric.diam X := by
  have bound (P Q : V →L[ℝ] V) :
      thickness P X - thickness Q X ≤ ‖P - Q‖ * Metric.diam X := by
    obtain ⟨x, hx, y, hy, hmax⟩ := exists_thickness_eq_norm P hX hne
    have hnorm : ‖P (x - y)‖ - ‖Q (x - y)‖ ≤ ‖(P - Q) (x - y)‖ := by
      simpa using norm_sub_norm_le (P (x - y)) (Q (x - y))
    have hQ := norm_sub_le_thickness Q hX hx hy
    have hop := (P - Q).le_opNorm (x - y)
    have hdiam : ‖x - y‖ ≤ Metric.diam X := by
      simpa [dist_eq_norm] using Metric.dist_le_diam_of_mem hX.isBounded hx hy
    have hmul := mul_le_mul_of_nonneg_left hdiam (norm_nonneg (P - Q))
    rw [hmax]
    linarith
  rw [abs_sub_le_iff]
  exact ⟨bound P Q, by simpa [norm_sub_rev] using bound Q P⟩

/-- The thickness function is Lipschitz, with the diameter as a constant.
This holds for all continuous linear maps, hence for orthogonal projections. -/
theorem thickness_lipschitz
    (X : Set V) (hX : IsCompact X) (hne : X.Nonempty) :
    LipschitzWith (Real.toNNReal (Metric.diam X))
      (fun P : V →L[ℝ] V => thickness P X) := by
  apply LipschitzWith.of_dist_le_mul
  intro P Q
  simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, Real.coe_toNNReal _ Metric.diam_nonneg,
    mul_comm] using lemma_continuity X hX hne P Q

end AsymptoticSubspace
