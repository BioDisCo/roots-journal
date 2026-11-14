-- TeX label: lem:volumes
-- Volume bounds for concave radial profiles under zero-line approximation.

module

public import AsymptoticSubspace.ConcaveProfileIntegrability

@[expose] public section

noncomputable section

namespace AsymptoticSubspace

open PaperFormalization

theorem lemma_volumes_paper
    {d : ℕ} (hd : 1 ≤ d)
    {h α : ℝ} (hh : 0 < h) (hα0 : 0 < α) (hα1 : α < 1)
    {r : ℝ → ℝ}
    (hmeas : Measurable r)
    (hconc : ConcaveOn ℝ (Set.Icc 0 h) r)
    (hnonneg : ∀ ξ ∈ Set.Icc 0 h, 0 ≤ r ξ)
    (hIntLeft : IntervalIntegrable (fun ξ => (r ξ) ^ (d - 1)) MeasureTheory.volume 0 ((1 - α) * h))
    (hIntRight :
      IntervalIntegrable (fun ξ => (r ξ) ^ (d - 1)) MeasureTheory.volume ((1 - α) * h) h) :
    let r0 := r ((1 - α) * h)
    let C := C_dMinusOne d
    (∫ ξ in 0..((1 - α) * h), C * (r ξ) ^ (d - 1)
      ≤ C * r0 ^ (d - 1) * h / (α ^ (d - 1) * (d : ℝ)) * (1 - α ^ d)) ∧
    (C * r0 ^ (d - 1) * h / (α ^ (d - 1) * (d : ℝ)) * (α ^ d)
      ≤ ∫ ξ in ((1 - α) * h)..h, C * (r ξ) ^ (d - 1)) :=
  lemma_volumes hd hh hα0 hα1 hmeas hconc hnonneg hIntLeft hIntRight

/-- The integral estimates with exactly the paper's profile hypotheses;
the integrability side conditions are derived. -/
theorem lemma_volumes_of_concave
    {d : ℕ} (hd : 1 ≤ d)
    {h α : ℝ} (hh : 0 < h) (hα0 : 0 < α) (hα1 : α < 1)
    {r : ℝ → ℝ} (hmeas : Measurable r)
    (hconc : ConcaveOn ℝ (Set.Icc 0 h) r)
    (hnonneg : ∀ ξ ∈ Set.Icc 0 h, 0 ≤ r ξ) :
    let r0 := r ((1 - α) * h)
    let C := C_dMinusOne d
    (∫ ξ in 0..((1 - α) * h), C * (r ξ) ^ (d - 1)
      ≤ C * r0 ^ (d - 1) * h / (α ^ (d - 1) * (d : ℝ)) * (1 - α ^ d)) ∧
    (C * r0 ^ (d - 1) * h / (α ^ (d - 1) * (d : ℝ)) * (α ^ d)
      ≤ ∫ ξ in ((1 - α) * h)..h, C * (r ξ) ^ (d - 1)) := by
  have hInt := concave_profile_intervalIntegrable hh.le hmeas hconc hnonneg (d - 1)
  have hb0 : 0 ≤ (1 - α) * h := mul_nonneg (by linarith) hh.le
  have hbh : (1 - α) * h ≤ h := by nlinarith
  apply lemma_volumes_paper hd hh hα0 hα1 hmeas hconc hnonneg
  · apply hInt.mono_set
    rw [Set.uIcc_of_le hb0, Set.uIcc_of_le hh.le]
    exact Set.Icc_subset_Icc le_rfl hbh
  · apply hInt.mono_set
    rw [Set.uIcc_of_le hbh, Set.uIcc_of_le hh.le]
    exact Set.Icc_subset_Icc hb0 le_rfl

end AsymptoticSubspace
