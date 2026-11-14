module

public import AsymptoticSubspace.PaperFormalizationCore

@[expose] public section

noncomputable section

namespace AsymptoticSubspace.PaperFormalization

open Set MeasureTheory

/-- A nonnegative concave profile on an interval is bounded by twice its midpoint value.
No continuity at the two endpoints is needed. -/
lemma concave_profile_bound {r : ℝ → ℝ} {h : ℝ}
    (hconc : ConcaveOn ℝ (Icc 0 h) r) (hnonneg : ∀ x ∈ Icc 0 h, 0 ≤ r x)
    {x : ℝ} (hx : x ∈ Icc 0 h) : r x ≤ 2 * r (h / 2) := by
  have hy : h - x ∈ Icc 0 h := by constructor <;> linarith [hx.1, hx.2]
  have hmid := hconc.2 hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 + 1 / 2 = 1)
  simp only [smul_eq_mul] at hmid
  have heq : (1 / 2 : ℝ) * x + (1 / 2 : ℝ) * (h - x) = h / 2 := by ring
  rw [heq] at hmid
  linarith [hnonneg (h - x) hy]

/-- The integrability hypotheses in the earlier integral lemma follow from
the paper's measurable, nonnegative, concave-profile assumptions. -/
theorem concave_profile_intervalIntegrable {r : ℝ → ℝ} {h : ℝ} (hh : 0 ≤ h)
    (hmeas : Measurable r) (hconc : ConcaveOn ℝ (Icc 0 h) r)
    (hnonneg : ∀ x ∈ Icc 0 h, 0 ≤ r x) (m : ℕ) :
    IntervalIntegrable (fun x => r x ^ m) volume 0 h := by
  apply IntervalIntegrable.mono_fun'
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (2 * r (h / 2)) ^ m) volume 0 h)
    (hmeas.pow_const m).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
  have hx' : x ∈ Icc 0 h := by
    rw [uIoc_of_le hh] at hx
    exact ⟨hx.1.le, hx.2⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hnonneg x hx') _)]
  exact pow_le_pow_left₀ (hnonneg x hx') (concave_profile_bound hconc hnonneg hx') m

end AsymptoticSubspace.PaperFormalization
