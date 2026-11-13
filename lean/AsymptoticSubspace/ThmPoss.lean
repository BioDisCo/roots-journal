-- TeX label: thm:poss
import AsymptoticSubspace.LemContract
import AsymptoticSubspace.VolumeRateCore
import AsymptoticSubspace.NestedHulls
import AsymptoticSubspace.ExactHyperplane

noncomputable section

namespace AsymptoticSubspace

open ComputationalModel ModelLemmas MeasureTheory Filter
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {n : ℕ} [NeZero n]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma minimumBroadcastWeight_le_one
    (E : AveragingExecution (V := V) n) (M : Round → Finset (Proc n))
    {α : ℝ} (hmbw : MinimumBroadcastWeight E M α) : α ≤ 1 := by
  let i : Proc n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  calc
    α ≤ ∑ j ∈ M 0, E.weights 0 i j := hmbw.2 0 i
    _ ≤ ∑ j : Proc n, E.weights 0 i j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => E.weights_nonneg 0 i j)
    _ = 1 := E.weights_row_sum 0 i

/-- The exact geometric estimate preceding the logarithmic bound in the paper. -/
theorem volume_geometric_bound
    (E : AveragingExecution (V := V) n) (M : Round → Finset (Proc n))
    (α : ℝ) (hα : 0 < α) (hmbw : MinimumBroadcastWeight E M α)
    (hcard : ∀ t, (M t).card ≤ Module.finrank ℝ V) (t : ℕ) :
    volume.real (Poly E t) ≤
      (1 - α ^ Module.finrank ℝ V) ^ t * volume.real (Poly E 0) := by
  have hα1 := minimumBroadcastWeight_le_one E M hmbw
  apply VolumeContraction.geometric_bound (sub_nonneg.mpr (pow_le_one₀ hα.le hα1)) _ t
  intro r
  have h := lemma_contract_of_le_one E M α r hα hα1 hmbw (hcard (r + 1))
  have hfin (s : ℕ) : volume (Poly E s) ≠ ⊤ :=
    (Set.finite_range (E.outputs s)).isCompact_convexHull.measure_ne_top
  have hf : 0 ≤ 1 - α ^ Module.finrank ℝ V := sub_nonneg.mpr (pow_le_one₀ hα.le hα1)
  have hreal := (ENNReal.toReal_le_toReal (hfin (r + 1))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin r))).mpr h
  simpa [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hf] using hreal

/-- The current convex hull's volume tends to zero. -/
theorem volume_tendsto_zero
    (E : AveragingExecution (V := V) n) (M : Round → Finset (Proc n))
    (α : ℝ) (hα : 0 < α) (hmbw : MinimumBroadcastWeight E M α)
    (hcard : ∀ t, (M t).card ≤ Module.finrank ℝ V) :
    Tendsto (fun t => volume.real (Poly E t)) atTop (𝓝 0) := by
  have hα1 := minimumBroadcastWeight_le_one E M hmbw
  have hq0 : 0 ≤ 1 - α ^ Module.finrank ℝ V := sub_nonneg.mpr (pow_le_one₀ hα.le hα1)
  have hq1 : 1 - α ^ Module.finrank ℝ V < 1 := by linarith [pow_pos hα (Module.finrank ℝ V)]
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const
    (volume.real (Poly E 0))
  apply squeeze_zero (fun _ => measureReal_nonneg)
    (volume_geometric_bound E M α hα hmbw hcard)
  simpa using hlim

/-- Quantitative part of `thm:poss`, with the necessary positive tolerance explicit. -/
theorem volume_round_bound
    (E : AveragingExecution (V := V) n) (M : Round → Finset (Proc n))
    (α : ℝ) (hα : 0 < α) (hmbw : MinimumBroadcastWeight E M α)
    (hcard : ∀ t, (M t).card ≤ Module.finrank ℝ V)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (ht : (α ^ Module.finrank ℝ V)⁻¹ *
      Real.log (volume.real (Poly E 0) / ε) ≤ (t : ℝ)) :
    volume (Poly E t) ≤ ENNReal.ofReal ε := by
  have hα1 := minimumBroadcastWeight_le_one E M hmbw
  have hreal : volume.real (Poly E t) ≤ ε := by
    apply (volume_geometric_bound E M α hα hmbw hcard t).trans
    apply VolumeContraction.geometric_round_bound
      (v := fun r => (1 - α ^ Module.finrank ℝ V) ^ r * volume.real (Poly E 0))
      (by simp only [pow_zero, one_mul]; exact measureReal_nonneg)
      (pow_pos hα _) (pow_le_one₀ hα.le hα1) hε
    · intro r
      rw [pow_succ]
      exact le_of_eq (by ring)
    · simpa using ht
  apply (ENNReal.toReal_le_toReal
    (Set.finite_range (E.outputs t)).isCompact_convexHull.measure_ne_top ENNReal.ofReal_ne_top).mp
  simpa [measureReal_def, ENNReal.toReal_ofReal hε.le] using hreal

/-- Theorem `thm:poss`: agreement, validity, and the stated volume deadline. -/
theorem theorem_poss
    (hd : 1 ≤ Module.finrank ℝ V)
    (E : AveragingExecution (V := V) n) (M : Round → Finset (Proc n))
    (α : ℝ) (hα : 0 < α) (hmbw : MinimumBroadcastWeight E M α)
    (hcard : ∀ t, (M t).card ≤ Module.finrank ℝ V) :
    (∃ W : AffineSubspace ℝ V,
      Module.finrank ℝ W.direction ≤ Module.finrank ℝ V - 1 ∧
      (∀ i, ConvergesToSet (fun t => E.outputs t i) (W : Set V)) ∧
      (∀ i, ConvergesToSet (fun t => E.outputs t i) (Poly E 0))) ∧
    (∀ (ε : ℝ), 0 < ε → ∀ t : ℕ,
      (α ^ Module.finrank ℝ V)⁻¹ * Real.log (volume.real (Poly E 0) / ε) ≤ (t : ℝ) →
      volume (Poly E t) ≤ ENNReal.ofReal ε) := by
  refine ⟨?_, fun ε hε t ht => volume_round_bound E M α hα hmbw hcard hε t ht⟩
  -- The nested limit hull is convex and has zero volume.
  let Pstar := ⋂ t, Poly E t
  have hfinite : volume Pstar ≠ ⊤ := measure_ne_top_of_subset
    (Set.iInter_subset (fun t => Poly E t) 0) (poly_compact E 0).measure_ne_top
  have hzero : volume Pstar = 0 := by
    have hreal : volume.real Pstar ≤ 0 :=
      ge_of_tendsto (volume_tendsto_zero E M α hα hmbw hcard)
        (Filter.Eventually.of_forall fun t => measureReal_mono
          (Set.iInter_subset (fun t => Poly E t) t) (poly_compact E t).measure_ne_top)
    exact ((ENNReal.toReal_eq_zero_iff _).mp
      (le_antisymm hreal ENNReal.toReal_nonneg)).resolve_right hfinite
  have hconvex : Convex ℝ Pstar := convex_iInter fun t => convex_convexHull ℝ _
  -- Lemma 11 places the limit in a hyperplane; compact nestedness gives agreement.
  obtain ⟨W, _, hdim, hPW⟩ := (lemma_convex_zero_hyperplane_exact hd hconvex).mpr hzero
  refine ⟨W, by omega, ?_, ModelLemmas.averaging_validityAtLimit E⟩
  exact fun i => convergesToSet_mono (outputs_converge_poly_limit E i) hPW

end AsymptoticSubspace
