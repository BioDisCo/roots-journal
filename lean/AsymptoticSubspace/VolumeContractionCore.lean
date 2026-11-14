module

public import AsymptoticSubspace.ModelBridgeCore
public import AsymptoticSubspace.AxialVolumeContraction
public import AsymptoticSubspace.HyperplaneCoordinates

@[expose] public section

noncomputable section

namespace AsymptoticSubspace.VolumeContraction

open Set MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Rotate and translate the broadcasting hyperplane to the first-coordinate
plane, and apply the symmetrization estimate to the positive half. -/
theorem halfspace_volume_contract
    (hd : 2 ≤ Module.finrank ℝ V)
    {P Q : Set V} (hP : Convex ℝ P) (hPc : IsCompact P) (hQc : IsCompact Q)
    (hQP : Q ⊆ P) (l : V →ₗ[ℝ] ℝ) (hl : l ≠ 0) (α : ℝ)
    (hα : 0 < α) (hα1 : α < 1) {p b : V} (hp : p ∈ P) (hb : b ∈ P)
    (hmax : ∀ x ∈ P, l x ≤ l b)
    (hcut : ∀ x ∈ Q, l x ≤ α * l p + (1 - α) * l b) :
    volume.real (Q ∩ {x | l p < l x}) ≤
      (1 - α ^ Module.finrank ℝ V) * volume.real (P ∩ {x | l p < l x}) := by
  let m := Module.finrank ℝ V - 1
  have hm : 0 < m := by omega
  have hdim : Module.finrank ℝ V = m + 1 := by omega
  obtain ⟨F, c, hFc, hFm, hc, hF⟩ :=
    PaperFormalization.exists_hyperplane_coordinates hdim l hl p
  have hhalf (S : Set V) : F '' (S ∩ {x | l p < l x}) =
      F '' S ∩ {z | 0 < z.1} := by
    ext z
    constructor
    · rintro ⟨x, ⟨hx, hxp⟩, rfl⟩
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      change 0 < (F x).1
      rw [hF]
      exact mul_pos hc (sub_pos.mpr hxp)
    · rintro ⟨⟨x, hx, rfl⟩, hxp⟩
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      change 0 < (F x).1 at hxp
      rw [hF] at hxp
      exact sub_pos.mp ((mul_pos_iff_of_pos_left hc).mp hxp)
  have hvol (S : Set V) (hSc : IsCompact S) :
      volume.real (F '' S ∩ {z | 0 < z.1}) = volume.real (S ∩ {x | l p < l x}) := by
    have hmeas : MeasurableSet (F '' S ∩ {z | 0 < z.1}) :=
      (hSc.image hFc).measurableSet.inter (measurableSet_lt measurable_const measurable_fst)
    rw [← hhalf] at hmeas ⊢
    simp only [measureReal_def]
    rw [← hFm.map_eq, Measure.map_apply hFc.measurable hmeas,
      preimage_image_eq _ F.injective]
  have hPF : Convex ℝ (F '' P) := hP.affine_image F.toAffineMap
  have h := axial_halfspace_contract hm hPF
    (hPc.image hFc) (image_mono hQP)
    (show 0 ∈ Prod.fst '' (F '' P) from
      ⟨F p, ⟨p, hp, rfl⟩, by rw [hF]; simp⟩)
    (show F b ∈ F '' P from ⟨b, hb, rfl⟩)
    (by
      rintro z ⟨x, hx, rfl⟩
      simp only [hF]
      exact mul_le_mul_of_nonneg_left (sub_le_sub_right (hmax x hx) _) hc.le)
    hα hα1
    (by
      rintro z ⟨x, hx, rfl⟩
      simp only [hF]
      have hscaled := mul_le_mul_of_nonneg_left (hcut x hx) hc.le
      nlinarith)
  rw [hvol Q hQc, hvol P hPc, ← hdim] at h
  exact h

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
  have hsplit := measureReal_inter_add_sdiff (μ := volume)
    (s := P) (t := {x | l p < l x})
    (measurableSet_lt measurable_const l.continuous_of_finiteDimensional.measurable) hP
  rw [measureReal_congr heq] at hsplit
  exact hsplit.symm

/-- Cutting both sides of a convex body toward a hyperplane contracts its volume.
The hypotheses specify the two supporting levels reached by the cut. -/
theorem volume_contract_of_support_bounds
    (hd : 2 ≤ Module.finrank ℝ V)
    {P Q : Set V} (hP : Convex ℝ P) (hPc : IsCompact P) (hQc : IsCompact Q)
    (hQP : Q ⊆ P) (l : V →ₗ[ℝ] ℝ) (hl : l ≠ 0)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    {p a b : V} (hp : p ∈ P) (ha : a ∈ P) (hb : b ∈ P)
    (hmin : ∀ x ∈ P, l a ≤ l x) (hmax : ∀ x ∈ P, l x ≤ l b)
    (hlo : ∀ x ∈ Q, α * l p + (1 - α) * l a ≤ l x)
    (hhi : ∀ x ∈ Q, l x ≤ α * l p + (1 - α) * l b) :
    volume Q ≤ ENNReal.ofReal (1 - α ^ Module.finrank ℝ V) * volume P := by
  have hpos := halfspace_volume_contract hd hP hPc hQc hQP l hl α hα hα1 hp hb hmax hhi
  have hneg := halfspace_volume_contract hd hP hPc hQc hQP (-l) (neg_ne_zero.mpr hl)
    α hα hα1 hp ha
    (by intro x hx; simpa using hmin x hx) (by
      intro x hx
      change -l x ≤ α * (-l p) + (1 - α) * (-l a)
      linarith [hlo x hx])
  simp only [LinearMap.neg_apply, neg_lt_neg_iff] at hneg
  have hreal : volume.real Q ≤ (1 - α ^ Module.finrank ℝ V) * volume.real P := by
    rw [volume_real_split l hl p hQc.measure_ne_top,
      volume_real_split l hl p hPc.measure_ne_top]
    nlinarith
  have hfactor : 0 ≤ 1 - α ^ Module.finrank ℝ V :=
    sub_nonneg.mpr (pow_le_one₀ hα.le hα1.le)
  apply (ENNReal.toReal_le_toReal hQc.measure_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hPc.measure_ne_top)).mp
  simpa [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hfactor] using hreal

end AsymptoticSubspace.VolumeContraction
