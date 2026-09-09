import AsymptoticSubspace.VolumeContractionCore
import AsymptoticSubspace.ThmSolvingCore

noncomputable section

namespace AsymptoticSubspace

open ComputationalModel ModelLemmas MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {n : Nat}

/--
TeX label: `lem:contract`.

Volume contraction per round: if `|(M (t+1))| ≤ d = finrank ℝ V`,
then the `d`-dimensional volume contracts by factor `(1 - α^d)`.

The proof uses homothetic copies of the two halves of the old convex hull in the
removed caps. This proves the paper's bound without symmetrization, and includes
the zero-volume case.
-/
theorem lemma_contract_of_le_one
    [NeZero n]
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (α : ℝ)
    (t : Round)
    (hα_pos : 0 < α)
    (hα_le_one : α ≤ 1)
    (hmbw : MinimumBroadcastWeight (V := V) E M α)
    (hcard : (M (t + 1)).card ≤ Module.finrank ℝ V) :
    volume (Poly E (t + 1)) ≤
      ENNReal.ofReal (1 - α ^ Module.finrank ℝ V) * volume (Poly E t) := by
  classical
  let i : Proc n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  obtain ⟨j, hj, _⟩ := hmbw.1 (t + 1) i
  letI : Nonempty (M (t + 1)) := ⟨⟨j, hj⟩⟩
  let xs : M (t + 1) → V := fun j => E.outputs t j.1
  let p := E.outputs t j
  have hspan : vectorSpan ℝ (Set.range xs) < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro h
    have hrank := finrank_vectorSpan_range_add_one_le ℝ xs
    rw [h, finrank_top] at hrank
    simp only [Fintype.card_coe] at hrank
    omega
  obtain ⟨l, hl, hker⟩ := (vectorSpan ℝ (Set.range xs)).exists_le_ker_of_lt_top hspan
  have hconst : ∀ x ∈ PolyOn E t (M (t + 1)), l x = l p := by
    apply convexHull_min _ (convex_hyperplane l.isLinear (l p))
    rintro x ⟨q, hq, rfl⟩
    have hv : E.outputs t q - p ∈ vectorSpan ℝ (Set.range xs) :=
      vsub_mem_vectorSpan (k := ℝ) ⟨⟨q, hq⟩, rfl⟩ ⟨⟨j, hj⟩, rfl⟩
    have hzero := hker hv
    simpa [LinearMap.mem_ker, map_sub, sub_eq_zero] using hzero
  have hPc : IsCompact (Poly E t) := (Set.finite_range (E.outputs t)).isCompact_convexHull
  have hQc : IsCompact (Poly E (t + 1)) :=
    (Set.finite_range (E.outputs (t + 1))).isCompact_convexHull
  have hp : p ∈ Poly E t := subset_convexHull ℝ _ ⟨j, rfl⟩
  obtain ⟨a, ha, hmin⟩ := hPc.exists_isMinOn ⟨p, hp⟩ l.continuous_of_finiteDimensional.continuousOn
  obtain ⟨b, hb, hmax⟩ := hPc.exists_isMaxOn ⟨p, hp⟩ l.continuous_of_finiteDimensional.continuousOn
  apply VolumeContraction.volume_contract_of_support_bounds
    (convex_convexHull ℝ _) hPc hQc (ThmSolving.poly_succ_subset E t)
    l hl α hα_pos hα_le_one ha hb (hmin hp) (hmax hp)
  · apply convexHull_min _ (convex_halfSpace_ge l.isLinear (α * l p + (1 - α) * l a))
    rintro x ⟨q, rfl⟩
    obtain ⟨ξ, hξ, η, hη, hout⟩ := lemma_xi_xip_model E M α t q hα_pos hmbw
    change α * l p + (1 - α) * l a ≤ l (E.outputs (t + 1) q)
    rw [hout, map_add, map_smul, map_smul, hconst ξ hξ]
    simp only [smul_eq_mul]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (show l a ≤ l η from hmin hη)
      (sub_nonneg.mpr hα_le_one))
  · apply convexHull_min _ (convex_halfSpace_le l.isLinear (α * l p + (1 - α) * l b))
    rintro x ⟨q, rfl⟩
    obtain ⟨ξ, hξ, η, hη, hout⟩ := lemma_xi_xip_model E M α t q hα_pos hmbw
    change l (E.outputs (t + 1) q) ≤ α * l p + (1 - α) * l b
    rw [hout, map_add, map_smul, map_smul, hconst ξ hξ]
    simp only [smul_eq_mul]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (show l η ≤ l b from hmax hη)
      (sub_nonneg.mpr hα_le_one))

/-- Original interface for `lem:contract`. -/
theorem lemma_contract [NeZero n]
    (E : AveragingExecution (V := V) n) (M : Round → Finset (Proc n))
    (α : ℝ) (t : Round) (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hmbw : MinimumBroadcastWeight E M α)
    (hcard : (M (t + 1)).card ≤ Module.finrank ℝ V) :
    volume (Poly E (t + 1)) ≤
      ENNReal.ofReal (1 - α ^ Module.finrank ℝ V) * volume (Poly E t) :=
  lemma_contract_of_le_one E M α t hα_pos hα_lt_one.le hmbw hcard

end AsymptoticSubspace
