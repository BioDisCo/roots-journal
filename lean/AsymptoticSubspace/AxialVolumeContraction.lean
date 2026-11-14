module

public import AsymptoticSubspace.Symmetrization

/-! The positive-half volume estimate in Lemma 10, in axial coordinates. -/

@[expose] public section

noncomputable section

namespace AsymptoticSubspace.VolumeContraction

open Set MeasureTheory PaperFormalization

variable {m : ℕ}

lemma axial_level_null (c : ℝ) :
    volume {z : ℝ × EuclideanSpace ℝ (Fin m) | z.1 = c} = 0 := by
  have heq : {z : ℝ × EuclideanSpace ℝ (Fin m) | z.1 = c} =
      ({c} : Set ℝ) ×ˢ (univ : Set (EuclideanSpace ℝ (Fin m))) := by ext z; simp
  rw [heq]
  change (volume.prod volume) ({c} ×ˢ univ) = 0
  simp

/-- Cavalieri and the concave-radius estimates of Lemma 9 bound the part
remaining between the broadcasting hyperplane and the contracted support. -/
theorem axial_halfspace_contract (hm : 0 < m)
    {P Q : Set (ℝ × EuclideanSpace ℝ (Fin m))}
    (hP : Convex ℝ P) (hPc : IsCompact P) (hQP : Q ⊆ P)
    (hzero : 0 ∈ Prod.fst '' P) {b : ℝ × EuclideanSpace ℝ (Fin m)} (hb : b ∈ P)
    (hmax : ∀ z ∈ P, z.1 ≤ b.1)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hcut : ∀ z ∈ Q, z.1 ≤ (1 - α) * b.1) :
    volume.real (Q ∩ {z | 0 < z.1}) ≤
      (1 - α ^ (m + 1)) * volume.real (P ∩ {z | 0 < z.1}) := by
  obtain ⟨p, hp, hp0⟩ := hzero
  have hb0 : 0 ≤ b.1 := by simpa [hp0] using hmax p hp
  by_cases hbzero : b.1 = 0
  · have hempty : Q ∩ {z | 0 < z.1} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      have := hcut z hz.1
      simp only [hbzero, mul_zero] at this
      exact (not_lt_of_ge this) hz.2
    rw [hempty, measureReal_empty]
    exact mul_nonneg (sub_nonneg.mpr (pow_le_one₀ hα.le hα1.le)) measureReal_nonneg
  have hbpos : 0 < b.1 := lt_of_le_of_ne hb0 (Ne.symm hbzero)
  let c := (1 - α) * b.1
  let L := P ∩ Prod.fst ⁻¹' Icc 0 c
  let R := P ∩ Prod.fst ⁻¹' Icc c b.1
  let K := C_dMinusOne (m + 1) * sectionRadius P c ^ m * b.1 /
    (α ^ m * ((m + 1 : ℕ) : ℝ))
  have hc0 : 0 ≤ c := mul_nonneg (sub_nonneg.mpr hα1.le) hb0
  have hcb : c ≤ b.1 := by dsimp [c]; nlinarith
  have hproj : Icc 0 b.1 ⊆ Prod.fst '' P :=
    (hP.linear_image (LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin m)))).ordConnected.out
      ⟨p, hp, hp0⟩ ⟨b, hb, rfl⟩
  have hbounds := lemma_volumes_of_convex_body hm hPc hP hbpos hα hα1 hproj
  have hK : 0 ≤ K := by
    dsimp [K]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (section_constant_pos m).le
        (pow_nonneg (sectionRadius_nonneg P c) _)) hb0) (by positivity)
  have hq : 0 ≤ 1 - α ^ (m + 1) := sub_nonneg.mpr (pow_le_one₀ hα.le hα1.le)
  have hLf : volume L ≠ ⊤ := measure_ne_top_of_subset inter_subset_left hPc.measure_ne_top
  have hRf : volume R ≠ ⊤ := measure_ne_top_of_subset inter_subset_left hPc.measure_ne_top
  have hleft : volume.real L ≤ K * (1 - α ^ (m + 1)) := by
    have := (ENNReal.toReal_le_toReal hLf ENNReal.ofReal_ne_top).mpr hbounds.1
    simpa only [L, c, K, measureReal_def, ENNReal.toReal_ofReal (mul_nonneg hK hq)] using this
  have hright : K * α ^ (m + 1) ≤ volume.real R := by
    have := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hRf).mpr hbounds.2
    simpa only [R, c, K, measureReal_def,
      ENNReal.toReal_ofReal (mul_nonneg hK (pow_nonneg hα.le _))] using this
  have hboundary : volume (L ∩ R) = 0 := by
    apply measure_mono_null (t := {z | z.1 = c}) _ (axial_level_null c)
    intro z hz
    exact le_antisymm hz.1.2.2 hz.2.2.1
  have hsum : volume.real L + volume.real R = volume.real (P ∩ {z | 0 < z.1}) := by
    rw [← measureReal_union₀
      (hPc.measurableSet.inter (measurableSet_Icc.preimage measurable_fst)).nullMeasurableSet
      (show AEDisjoint volume L R from hboundary) hLf hRf]
    apply measureReal_congr
    have hae : ∀ᵐ z : ℝ × EuclideanSpace ℝ (Fin m) ∂volume, z.1 ≠ 0 := by
      rw [ae_iff]; simpa using axial_level_null (m := m) 0
    filter_upwards [hae] with z hz
    apply propext
    change (z ∈ L ∨ z ∈ R) ↔ z ∈ P ∧ 0 < z.1
    dsimp [L, R]
    simp only [mem_inter_iff, mem_preimage, mem_Icc]
    constructor
    · rintro (⟨hzP, hz0, _⟩ | ⟨hzP, hzc, _⟩)
      · exact ⟨hzP, lt_of_le_of_ne hz0 (Ne.symm hz)⟩
      · exact ⟨hzP, lt_of_le_of_ne (hc0.trans hzc) (Ne.symm hz)⟩
    · rintro ⟨hzP, hz0⟩
      rcases le_total z.1 c with hzc | hcz
      · exact Or.inl ⟨hzP, hz0.le, hzc⟩
      · exact Or.inr ⟨hzP, hcz, hmax z hzP⟩
  have hQL : volume.real (Q ∩ {z | 0 < z.1}) ≤ volume.real L := by
    apply measureReal_mono _ hLf
    exact fun z hz => ⟨hQP hz.1, hz.2.le, hcut z hz.1⟩
  rw [← hsum]
  have hscaledL := mul_le_mul_of_nonneg_left hleft (pow_nonneg hα.le (m + 1))
  have hscaledR := mul_le_mul_of_nonneg_left hright hq
  nlinarith

end AsymptoticSubspace.VolumeContraction
