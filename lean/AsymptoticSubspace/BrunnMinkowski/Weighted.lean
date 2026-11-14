module

public import AsymptoticSubspace.BrunnMinkowski.BrunnMinkowski
public import Mathlib

@[expose] public section

noncomputable section

namespace AsymptoticSubspace.BrunnMinkowski

open Set MeasureTheory
open scoped Pointwise

lemma volume_root_smul {m : ℕ} (hm : 0 < m) {a : ℝ} (ha : 0 ≤ a)
    (S : Set (EuclideanSpace ℝ (Fin m))) :
    volume.real (a • S) ^ (m : ℝ)⁻¹ = a * volume.real S ^ (m : ℝ)⁻¹ := by
  simp only [measureReal_def, volume.addHaar_smul_of_nonneg ha S,
    finrank_euclideanSpace, Fintype.card_fin, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg ha m)]
  rw [Real.mul_rpow (pow_nonneg ha m) ENNReal.toReal_nonneg,
    Real.pow_rpow_inv_natCast ha (Nat.ne_of_gt hm)]

/-- The additive Brunn–Minkowski inequality in finite real volumes. -/
theorem brunn_minkowski_real {m : ℕ} (hm : 0 < m)
    {A B : Set (EuclideanSpace ℝ (Fin m))}
    (hA : IsCompact A) (hB : IsCompact B) (hneA : A.Nonempty) (hneB : B.Nonempty) :
    volume.real A ^ (m : ℝ)⁻¹ + volume.real B ^ (m : ℝ)⁻¹ ≤
      volume.real (A + B) ^ (m : ℝ)⁻¹ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have h := brunn_minkowski_euclideanSpace hneA hA.measurableSet hneB hB.measurableSet
    (hA.add hB).measurableSet
  have hfin := ENNReal.rpow_ne_top_of_nonneg (by positivity : 0 ≤ ((d : ℝ) + 1)⁻¹)
    ((hA.add hB).measure_lt_top (μ := volume)).ne
  have h' := ENNReal.toReal_mono hfin h
  rw [ENNReal.toReal_add
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hA.measure_lt_top.ne)
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hB.measure_lt_top.ne)] at h'
  simpa only [measureReal_def, Nat.cast_succ, ← ENNReal.toReal_rpow] using h'

/-- Weighted Brunn–Minkowski, including zero weights and zero-volume bodies. -/
theorem weighted_brunn_minkowski {m : ℕ} (hm : 0 < m)
    {A B : Set (EuclideanSpace ℝ (Fin m))}
    (hA : IsCompact A) (hB : IsCompact B) (hneA : A.Nonempty) (hneB : B.Nonempty)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * volume.real A ^ (m : ℝ)⁻¹ + b * volume.real B ^ (m : ℝ)⁻¹ ≤
      volume.real (a • A + b • B) ^ (m : ℝ)⁻¹ := by
  rw [← volume_root_smul hm ha, ← volume_root_smul hm hb]
  exact brunn_minkowski_real hm (hA.smul a) (hB.smul b)
    (hneA.image (a • ·)) (hneB.image (b • ·))

end AsymptoticSubspace.BrunnMinkowski
