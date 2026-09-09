import AsymptoticSubspace.ModelBridgeCore

noncomputable section

namespace AsymptoticSubspace.VolumeContraction

open Set MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- A homothetic copy of a half-body fits in the cap removed by an averaging step.
This gives the volume estimate directly, without a section-radius construction. -/
theorem halfspace_volume_contract
    {P Q : Set V} (hP : Convex ℝ P) (hPc : IsCompact P) (hQc : IsCompact Q)
    (hQP : Q ⊆ P) (l : V →ₗ[ℝ] ℝ) (c α : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) {p : V} (hp : p ∈ P) (hcp : c ≤ l p)
    (hcut : ∀ x ∈ Q, l x ≤ α * c + (1 - α) * l p) :
    volume.real (Q ∩ {x | c < l x}) ≤
      (1 - α ^ Module.finrank ℝ V) * volume.real (P ∩ {x | c < l x}) := by
  let S := P ∩ {x | c < l x}
  let T := Q ∩ {x | c < l x}
  let F := AffineMap.homothety p α '' S
  have hlin (x : V) : l (AffineMap.homothety p α x) = α * l x + (1 - α) * l p := by
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, map_add,
      map_smul, map_sub, smul_eq_mul]
    ring
  have hFP : F ⊆ S := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · have h := hP hx.1 hp hα.le (sub_nonneg.mpr hα1) (by ring : α + (1 - α) = 1)
      convert h using 1
      simp [AffineMap.homothety_apply, smul_sub, sub_smul]
      abel
    · change c < l (AffineMap.homothety p α x)
      rw [hlin]
      have hx' : c < l x := hx.2
      nlinarith [mul_nonneg (sub_nonneg.mpr hα1) (sub_nonneg.mpr hcp)]
  have hTP : T ⊆ S := fun _ hx => ⟨hQP hx.1, hx.2⟩
  have hdis : Disjoint T F := by
    rw [Set.disjoint_left]
    rintro y hy ⟨x, hx, rfl⟩
    have h := hcut _ hy.1
    rw [hlin] at h
    have hx' : c < l x := hx.2
    nlinarith
  have hSf : volume S ≠ ⊤ := measure_ne_top_of_subset inter_subset_left hPc.measure_ne_top
  have hTf : volume T ≠ ⊤ := measure_ne_top_of_subset hTP hSf
  have hFf : volume F ≠ ⊤ := measure_ne_top_of_subset hFP hSf
  have hTm : MeasurableSet T := hQc.measurableSet.inter
    (measurableSet_lt measurable_const l.continuous_of_finiteDimensional.measurable)
  have hvol : volume.real F = α ^ Module.finrank ℝ V * volume.real S := by
    simp [F, measureReal_def, Measure.addHaar_image_homothety,
      abs_of_nonneg (pow_nonneg hα.le _), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hα.le _)]
  have hle := measureReal_mono (Set.union_subset hTP hFP) hSf
  rw [measureReal_union' hdis hTm hTf hFf, hvol] at hle
  change volume.real T ≤ (1 - α ^ Module.finrank ℝ V) * volume.real S
  nlinarith

/-- A proper affine hyperplane has zero ambient volume. -/
lemma volume_level_zero (l : V →ₗ[ℝ] ℝ) (hl : l ≠ 0) (p : V) :
    volume {x | l x = l p} = 0 := by
  let A := AffineSubspace.mk' p l.ker
  have hA : A ≠ ⊤ := by
    intro h
    have hk : l.ker = ⊤ := by
      simpa [A] using congrArg AffineSubspace.direction h
    exact hl (LinearMap.ker_eq_top.mp hk)
  have heq : {x | l x = l p} = (A : Set V) := by
    ext x
    simp [A, AffineSubspace.mem_mk', LinearMap.mem_ker, map_sub, sub_eq_zero]
  rw [heq]
  exact Measure.addHaar_affineSubspace volume A hA

/-- Split a finite-volume set into its two open halves; the separating plane is null. -/
lemma volume_real_split (l : V →ₗ[ℝ] ℝ) (hl : l ≠ 0) (p : V)
    {P : Set V} (hP : volume P ≠ ⊤) :
    volume.real P = volume.real (P ∩ {x | l p < l x}) +
      volume.real (P ∩ {x | l x < l p}) := by
  have hae : ∀ᵐ x ∂volume, l x ≠ l p := by
    rw [ae_iff]
    simpa using volume_level_zero l hl p
  have heq : (P \ {x | l p < l x} : Set V) =ᵐ[volume]
      (P ∩ {x | l x < l p} : Set V) := by
    filter_upwards [hae] with x hx
    change (x ∈ P ∧ ¬l p < l x) = (x ∈ P ∧ l x < l p)
    apply propext
    exact and_congr_right fun _ => ⟨fun h => lt_of_le_of_ne (le_of_not_gt h) hx,
      fun h => not_lt.mpr h.le⟩
  have hsplit := measureReal_inter_add_diff (μ := volume)
    (s := P) (t := {x | l p < l x})
    (measurableSet_lt measurable_const l.continuous_of_finiteDimensional.measurable) hP
  rw [measureReal_congr heq] at hsplit
  exact hsplit.symm

/-- Cutting both sides of a convex body toward a hyperplane contracts its volume.
The hypotheses specify the two supporting levels reached by the cut. -/
theorem volume_contract_of_support_bounds
    {P Q : Set V} (hP : Convex ℝ P) (hPc : IsCompact P) (hQc : IsCompact Q)
    (hQP : Q ⊆ P) (l : V →ₗ[ℝ] ℝ) (hl : l ≠ 0)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {p a b : V} (ha : a ∈ P) (hb : b ∈ P)
    (hmin : l a ≤ l p) (hmax : l p ≤ l b)
    (hlo : ∀ x ∈ Q, α * l p + (1 - α) * l a ≤ l x)
    (hhi : ∀ x ∈ Q, l x ≤ α * l p + (1 - α) * l b) :
    volume Q ≤ ENNReal.ofReal (1 - α ^ Module.finrank ℝ V) * volume P := by
  have hpos := halfspace_volume_contract hP hPc hQc hQP l (l p) α hα hα1 hb hmax hhi
  have hneg := halfspace_volume_contract hP hPc hQc hQP (-l) (-l p) α hα hα1 ha
    (by simpa using hmin) (by
      intro x hx
      change -l x ≤ α * (-l p) + (1 - α) * (-l a)
      linarith [hlo x hx])
  simp only [LinearMap.neg_apply, neg_lt_neg_iff] at hneg
  have hreal : volume.real Q ≤ (1 - α ^ Module.finrank ℝ V) * volume.real P := by
    rw [volume_real_split l hl p hQc.measure_ne_top,
      volume_real_split l hl p hPc.measure_ne_top]
    nlinarith
  have hfactor : 0 ≤ 1 - α ^ Module.finrank ℝ V :=
    sub_nonneg.mpr (pow_le_one₀ hα.le hα1)
  apply (ENNReal.toReal_le_toReal hQc.measure_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hPc.measure_ne_top)).mp
  simpa [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hfactor] using hreal

end AsymptoticSubspace.VolumeContraction
