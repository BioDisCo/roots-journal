import Mathlib

noncomputable section

namespace AsymptoticSubspace.VolumeContraction

/-- Iterating a nonnegative one-step contraction. -/
theorem geometric_bound {v : ℕ → ℝ} {q : ℝ} (hq : 0 ≤ q)
    (hstep : ∀ t, v (t + 1) ≤ q * v t) (t : ℕ) :
    v t ≤ q ^ t * v 0 := by
  induction t with
  | zero => simp
  | succ t ih =>
    calc
      v (t + 1) ≤ q * v t := hstep t
      _ ≤ q * (q ^ t * v 0) := mul_le_mul_of_nonneg_left ih hq
      _ = q ^ (t + 1) * v 0 := by rw [pow_succ]; ring

/-- The exponential estimate used to state the paper's logarithmic round bound. -/
theorem geometric_le_exp {δ : ℝ} (hδ : δ ≤ 1) (t : ℕ) :
    (1 - δ) ^ t ≤ Real.exp (-(t : ℝ) * δ) := by
  have hbase : 1 - δ ≤ Real.exp (-δ) := by
    linarith [Real.add_one_le_exp (-δ)]
  calc
    (1 - δ) ^ t ≤ (Real.exp (-δ)) ^ t := pow_le_pow_left₀ (sub_nonneg.mpr hδ) hbase t
    _ = Real.exp (-(t : ℝ) * δ) := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- Explicit round threshold, including an initially zero quantity. -/
theorem geometric_round_bound {v : ℕ → ℝ} {δ ε : ℝ}
    (hv : 0 ≤ v 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε)
    (hstep : ∀ t, v (t + 1) ≤ (1 - δ) * v t)
    (t : ℕ) (ht : δ⁻¹ * Real.log (v 0 / ε) ≤ (t : ℝ)) : v t ≤ ε := by
  have hgeom := geometric_bound (sub_nonneg.mpr hδ1) hstep t
  rcases eq_or_lt_of_le hv with hv0 | hvpos
  · rw [← hv0, mul_zero] at hgeom
    exact hgeom.trans hε.le
  have htime : Real.log (v 0 / ε) ≤ (t : ℝ) * δ := by
    have h := mul_le_mul_of_nonneg_left ht hδ.le
    simpa [← mul_assoc, ne_of_gt hδ, mul_comm] using h
  have hexp : Real.exp (-(t : ℝ) * δ) ≤ ε / v 0 := by
    calc
      Real.exp (-(t : ℝ) * δ) ≤ Real.exp (-Real.log (v 0 / ε)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = ε / v 0 := by rw [Real.exp_neg, Real.exp_log (div_pos hvpos hε), inv_div]
  calc
    v t ≤ (1 - δ) ^ t * v 0 := hgeom
    _ ≤ Real.exp (-(t : ℝ) * δ) * v 0 :=
      mul_le_mul_of_nonneg_right (geometric_le_exp hδ1 t) hv
    _ ≤ ε / v 0 * v 0 := mul_le_mul_of_nonneg_right hexp hv
    _ = ε := div_mul_cancel₀ _ (ne_of_gt hvpos)

end AsymptoticSubspace.VolumeContraction
