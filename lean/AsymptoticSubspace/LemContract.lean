module

public import AsymptoticSubspace.VolumeContractionCore
public import AsymptoticSubspace.AveragingHulls
public import AsymptoticSubspace.HalfspaceSupport

@[expose] public section

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

The proof treats zero volume, unit broadcasting weight, and dimension one
first. In higher dimensions it uses the paper's symmetrization, concave-radius
bounds, and the sum of the two open half-space volumes.
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
  let : Nonempty (M (t + 1)) := ⟨⟨j, hj⟩⟩
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
  have hPc : IsCompact (Poly E t) := (Set.finite_range (E.outputs t)).isCompact_convexHull ℝ
  have hQc : IsCompact (Poly E (t + 1)) :=
    (Set.finite_range (E.outputs (t + 1))).isCompact_convexHull ℝ
  have hp : p ∈ Poly E t := subset_convexHull ℝ _ ⟨j, rfl⟩
  obtain ⟨a, ha, hmin⟩ := hPc.exists_isMinOn ⟨p, hp⟩ l.continuous_of_finiteDimensional.continuousOn
  obtain ⟨b, hb, hmax⟩ := hPc.exists_isMaxOn ⟨p, hp⟩ l.continuous_of_finiteDimensional.continuousOn
  -- Degenerate cases precede the symmetrization argument.
  by_cases hzero : volume (Poly E t) = 0
  · rw [hzero, mul_zero]
    exact measure_mono_null (ModelLemmas.poly_succ_subset E t) hzero |>.le
  by_cases hα_one : α = 1
  · subst α
    have hplane : Poly E (t + 1) ⊆ {x | l x = l p} := by
      apply convexHull_min _ (convex_hyperplane l.isLinear (l p))
      rintro x ⟨q, rfl⟩
      obtain ⟨ξ, hξ, η, _, hout⟩ := lemma_xi_xip_model E M 1 t q hα_pos hmbw
      simp only [one_smul, sub_self, zero_smul, add_zero] at hout
      exact hout ▸ hconst ξ hξ
    have hvol := measure_mono_null hplane (VolumeContraction.volume_level_zero l hl p)
    simp [hvol]
  have hα_lt_one : α < 1 := lt_of_le_of_ne hα_le_one hα_one
  have hdpos : 1 ≤ Module.finrank ℝ V :=
    (Finset.one_le_card.mpr ⟨j, hj⟩).trans hcard
  by_cases hd_one : Module.finrank ℝ V = 1
  · have hsingle : ∀ x ∈ PolyOn E t (M (t + 1)), x = p := by
      have hsub : PolyOn E t (M (t + 1)) ⊆ ({p} : Set V) := by
        apply convexHull_min _ (convex_singleton p)
        rintro x ⟨q, hq, rfl⟩
        have hqj := Finset.card_le_one.mp (hcard.trans hd_one.le) q hq j hj
        simp [hqj, p]
      exact fun x hx => Set.mem_singleton_iff.mp (hsub hx)
    -- In dimension one this is the interval with endpoints
    -- α p + (1 - α) a and α p + (1 - α) b.
    have hsub : Poly E (t + 1) ⊆ AffineMap.homothety p (1 - α) '' Poly E t := by
      apply convexHull_min _ ((convex_convexHull ℝ _).affine_image _)
      rintro x ⟨q, rfl⟩
      obtain ⟨ξ, hξ, η, hη, hout⟩ := lemma_xi_xip_model E M α t q hα_pos hmbw
      refine ⟨η, hη, ?_⟩
      rw [hout, hsingle ξ hξ]
      simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_sub,
        sub_smul, one_smul]
      abel
    calc
      volume (Poly E (t + 1)) ≤ volume (AffineMap.homothety p (1 - α) '' Poly E t) :=
        measure_mono hsub
      _ = ENNReal.ofReal (1 - α ^ Module.finrank ℝ V) * volume (Poly E t) := by
        rw [Measure.addHaar_image_homothety]
        simp [hd_one, abs_of_nonneg (sub_nonneg.mpr hα_le_one)]
  -- Rotate the broadcasting hyperplane, symmetrize, and bound each half.
  apply VolumeContraction.volume_contract_of_support_bounds (by omega)
    (convex_convexHull ℝ _) hPc hQc (ModelLemmas.poly_succ_subset E t)
    l hl α hα_pos hα_lt_one hp ha hb hmin hmax
  · have hpOn : p ∈ PolyOn E t (M (t + 1)) := subset_convexHull ℝ _ ⟨j, hj, rfl⟩
    have h := support_bound_of_halfspace_zone E M α t hα_pos hmbw (-l)
      (neg_ne_zero.mpr hl) p a hpOn
      (fun x hx => by simpa using congrArg Neg.neg (hconst x hx))
      (fun x hx => by simpa using hmin hx)
    intro x hx
    have := h x hx
    simp only [LinearMap.neg_apply] at this
    linarith
  · exact support_bound_of_halfspace_zone E M α t hα_pos hmbw l hl p b
      (subset_convexHull ℝ _ ⟨j, hj, rfl⟩) hconst (fun x hx => hmax hx)

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
