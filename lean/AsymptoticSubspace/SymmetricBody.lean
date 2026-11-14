module

public import AsymptoticSubspace.LemVolumes

/-!
# Volumes of rotationally symmetric bodies

Lemma 9 is `lemma_volumes_geometric_paper`: both integral identities and both
inequalities are stated together. Sections have dimension `m`, so the ambient
dimension in the paper is `d = m + 1`. Integrability follows from the profile
hypotheses via `concave_profile_intervalIntegrable`.
-/

@[expose] public section

noncomputable section

namespace AsymptoticSubspace.PaperFormalization

open Set MeasureTheory

/-- A rotational body restricted to an explicit axial interval. Keeping the
interval explicit also makes the definition meaningful in ambient dimension one. -/
def symmetricBodyOn (m : ℕ) (r : ℝ → ℝ) (a b : ℝ) :
    Set (ℝ × EuclideanSpace ℝ (Fin m)) :=
  {z | z.1 ∈ Icc a b ∧ z.2 ∈ Metric.closedBall 0 (r z.1)}

/-- The paper's unrestricted rotational-body definition. -/
def symmetricBody (m : ℕ) (r : ℝ → ℝ) : Set (ℝ × EuclideanSpace ℝ (Fin m)) :=
  {z | z.2 ∈ Metric.closedBall 0 (r z.1)}

/-- For positive-dimensional sections, zeroing the radius outside an interval
changes the interval-restricted body only by a subset of the null rotation axis. -/
theorem volume_symmetricBody_truncated {m : ℕ} (hm : 0 < m) (r : ℝ → ℝ) (a b : ℝ) :
    volume (symmetricBody m (fun x => if x ∈ Icc a b then r x else 0)) =
      volume (symmetricBodyOn m r a b) := by
  classical
  let : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  have hnull : volume {z : ℝ × EuclideanSpace ℝ (Fin m) | z.2 = 0} = 0 := by
    have heq : {z : ℝ × EuclideanSpace ℝ (Fin m) | z.2 = 0} =
        (univ : Set ℝ) ×ˢ ({0} : Set (EuclideanSpace ℝ (Fin m))) := by ext z; simp
    rw [heq]
    change (volume.prod volume) (univ ×ˢ ({0} : Set (EuclideanSpace ℝ (Fin m)))) = 0
    simp
  apply measure_congr
  have hae : ∀ᵐ z : ℝ × EuclideanSpace ℝ (Fin m) ∂volume, z.2 ≠ 0 := by
    rw [ae_iff]
    simpa using hnull
  filter_upwards [hae] with z hz
  change (z.2 ∈ Metric.closedBall 0 (if z.1 ∈ Icc a b then r z.1 else 0)) =
    (z.1 ∈ Icc a b ∧ z.2 ∈ Metric.closedBall 0 (r z.1))
  apply propext
  by_cases hx : z.1 ∈ Icc a b
  · simp [hx]
  · simp [hx, hz]

lemma symmetricBodyOn_measurable {m : ℕ} {r : ℝ → ℝ} (hr : Measurable r) (a b : ℝ) :
    MeasurableSet (symmetricBodyOn m r a b) := by
  apply MeasurableSet.inter (measurableSet_Icc.preimage measurable_fst)
  exact measurableSet_le (measurable_snd.dist measurable_const) (hr.comp measurable_fst)

/-- Cavalieri's formula for the actual measurable rotational body. -/
theorem volume_symmetricBodyOn {m : ℕ} {r : ℝ → ℝ} (hr : Measurable r) (a b : ℝ) :
    volume (symmetricBodyOn m r a b) =
      ∫⁻ x in Icc a b, volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) (r x)) := by
  rw [show (volume : Measure (ℝ × EuclideanSpace ℝ (Fin m))) = volume.prod volume from rfl,
    Measure.prod_apply (symmetricBodyOn_measurable hr a b), ← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ Icc a b
  · simp only [mem_Icc] at hx
    simp [symmetricBodyOn, hx, Set.indicator, Metric.closedBall, dist_eq_norm]
  · simp only [mem_Icc] at hx
    simp [symmetricBodyOn, hx, Set.indicator, Metric.closedBall, dist_eq_norm]

lemma section_ball_volume {m : ℕ} (hm : 0 < m) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) ρ) =
      ENNReal.ofReal (C_dMinusOne (m + 1) * ρ ^ m) := by
  let : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  have hC : 0 ≤ C_dMinusOne (m + 1) := by
    unfold C_dMinusOne
    exact div_nonneg (Real.rpow_nonneg Real.pi_pos.le _)
      (Real.Gamma_pos_of_pos (by positivity)).le
  have hpow : Real.sqrt Real.pi ^ m = Real.rpow Real.pi ((m : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    congr 1
    ring
  rw [EuclideanSpace.volume_closedBall, ENNReal.ofReal_mul hC, ENNReal.ofReal_pow hρ]
  simp [C_dMinusOne, hpow, mul_comm]

/-- Finite volume and the integral identity, in extended nonnegative reals. -/
theorem volume_symmetricBodyOn_eq_integral {m : ℕ} (hm : 0 < m)
    {r : ℝ → ℝ} (hr : Measurable r) {a b : ℝ} (hab : a ≤ b)
    (hr0 : ∀ x ∈ Icc a b, 0 ≤ r x)
    (hInt : IntervalIntegrable (fun x => r x ^ m) volume a b) :
    volume (symmetricBodyOn m r a b) =
      ENNReal.ofReal (∫ x in a..b, C_dMinusOne (m + 1) * r x ^ m) := by
  rw [volume_symmetricBodyOn hr, intervalIntegral.integral_of_le hab,
    ← integral_Icc_eq_integral_Ioc]
  have hi : IntegrableOn (fun x => C_dMinusOne (m + 1) * r x ^ m) (Icc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp (hInt.const_mul _)
  rw [ofReal_integral_eq_lintegral_ofReal hi]
  · apply setLIntegral_congr_fun measurableSet_Icc
    exact fun x hx => section_ball_volume hm (hr0 x hx)
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    apply mul_nonneg _ (pow_nonneg (hr0 x hx) _)
    unfold C_dMinusOne
    exact div_nonneg (Real.rpow_nonneg Real.pi_pos.le _)
      (Real.Gamma_pos_of_pos (by positivity)).le

/-- Finite volume and its real integral representation, with the paper's exact
gamma-function normalization. Integrability is explicit: neither an infinite
volume nor a divergent Bochner integral can silently become real zero here. -/
theorem volume_real_symmetricBodyOn {m : ℕ} (hm : 0 < m)
    {r : ℝ → ℝ} (hr : Measurable r) {a b : ℝ} (hab : a ≤ b)
    (hr0 : ∀ x ∈ Icc a b, 0 ≤ r x)
    (hInt : IntervalIntegrable (fun x => r x ^ m) volume a b) :
    volume (symmetricBodyOn m r a b) < ⊤ ∧
      volume.real (symmetricBodyOn m r a b) =
        ∫ x in a..b, C_dMinusOne (m + 1) * r x ^ m := by
  have hvol := volume_symmetricBodyOn_eq_integral hm hr hab hr0 hInt
  refine ⟨by rw [hvol]; exact ENNReal.ofReal_lt_top, ?_⟩
  have hnonneg : 0 ≤ ∫ x in a..b, C_dMinusOne (m + 1) * r x ^ m := by
    apply intervalIntegral.integral_nonneg hab
    intro x hx
    apply mul_nonneg _ (pow_nonneg (hr0 x hx) _)
    unfold C_dMinusOne
    exact div_nonneg (Real.rpow_nonneg Real.pi_pos.le _)
      (Real.Gamma_pos_of_pos (by positivity)).le
  rw [measureReal_def, hvol, ENNReal.toReal_ofReal hnonneg]

/-- Geometric volume bounds from `lem:volumes` for ambient dimension at least two.
The bodies are measurable subsets of the product Euclidean space, and their
volume finiteness and integral representations are proved rather than assumed. -/
theorem lemma_volumes_geometric {m : ℕ} (hm : 0 < m)
    {h α : ℝ} (hh : 0 < h) (hα0 : 0 < α) (hα1 : α < 1)
    {r : ℝ → ℝ} (hmeas : Measurable r)
    (hconc : ConcaveOn ℝ (Icc 0 h) r)
    (hnonneg : ∀ x ∈ Icc 0 h, 0 ≤ r x) :
    let C := C_dMinusOne (m + 1)
    let r0 := r ((1 - α) * h)
    volume (symmetricBodyOn m r 0 ((1 - α) * h)) ≤
      ENNReal.ofReal (C * r0 ^ m * h / (α ^ m * ((m + 1 : ℕ) : ℝ)) * (1 - α ^ (m + 1))) ∧
    ENNReal.ofReal (C * r0 ^ m * h / (α ^ m * ((m + 1 : ℕ) : ℝ)) * α ^ (m + 1)) ≤
      volume (symmetricBodyOn m r ((1 - α) * h) h) := by
  have hb0 : 0 ≤ (1 - α) * h := mul_nonneg (by linarith) hh.le
  have hbh : (1 - α) * h ≤ h := by nlinarith
  have hInt := concave_profile_intervalIntegrable hh.le hmeas hconc hnonneg m
  have hleft : IntervalIntegrable (fun x => r x ^ m) volume 0 ((1 - α) * h) := by
    apply hInt.mono_set
    rw [uIcc_of_le hb0, uIcc_of_le hh.le]
    exact Icc_subset_Icc le_rfl hbh
  have hright : IntervalIntegrable (fun x => r x ^ m) volume ((1 - α) * h) h := by
    apply hInt.mono_set
    rw [uIcc_of_le hbh, uIcc_of_le hh.le]
    exact Icc_subset_Icc hb0 le_rfl
  have hb := AsymptoticSubspace.lemma_volumes_of_concave (d := m + 1) (by omega)
    hh hα0 hα1 hmeas hconc hnonneg
  dsimp at hb ⊢
  rw [volume_symmetricBodyOn_eq_integral hm hmeas hb0
      (fun x hx => hnonneg x ⟨hx.1, hx.2.trans hbh⟩) hleft,
    volume_symmetricBodyOn_eq_integral hm hmeas hbh
      (fun x hx => hnonneg x ⟨hb0.trans hx.1, hx.2⟩) hright]
  exact ⟨ENNReal.ofReal_le_ofReal hb.1, ENNReal.ofReal_le_ofReal hb.2⟩

/-- Lemma 9: integral representations and upper/lower bounds for the two
restricted symmetric bodies, with ambient dimension `d = m + 1 ≥ 2`. -/
theorem lemma_volumes_geometric_paper {m : ℕ} (hm : 0 < m)
    {h α : ℝ} (hh : 0 < h) (hα0 : 0 < α) (hα1 : α < 1)
    {r : ℝ → ℝ} (hmeas : Measurable r)
    (hconc : ConcaveOn ℝ (Icc 0 h) r)
    (hnonneg : ∀ x ∈ Icc 0 h, 0 ≤ r x) :
    let C := C_dMinusOne (m + 1)
    let r0 := r ((1 - α) * h)
    let left := symmetricBodyOn m r 0 ((1 - α) * h)
    let right := symmetricBodyOn m r ((1 - α) * h) h
    (volume left < ⊤ ∧
      volume.real left = ∫ x in 0..((1 - α) * h), C * r x ^ m ∧
      volume.real left ≤ C * r0 ^ m * h / (α ^ m * ((m + 1 : ℕ) : ℝ)) *
        (1 - α ^ (m + 1))) ∧
    (volume right < ⊤ ∧
      volume.real right = ∫ x in ((1 - α) * h)..h, C * r x ^ m ∧
      C * r0 ^ m * h / (α ^ m * ((m + 1 : ℕ) : ℝ)) * α ^ (m + 1) ≤
        volume.real right) := by
  have hb0 : 0 ≤ (1 - α) * h := mul_nonneg (by linarith) hh.le
  have hbh : (1 - α) * h ≤ h := by nlinarith
  have hInt := concave_profile_intervalIntegrable hh.le hmeas hconc hnonneg m
  have hleft : IntervalIntegrable (fun x => r x ^ m) volume 0 ((1 - α) * h) := by
    apply hInt.mono_set
    rw [uIcc_of_le hb0, uIcc_of_le hh.le]
    exact Icc_subset_Icc le_rfl hbh
  have hright : IntervalIntegrable (fun x => r x ^ m) volume ((1 - α) * h) h := by
    apply hInt.mono_set
    rw [uIcc_of_le hbh, uIcc_of_le hh.le]
    exact Icc_subset_Icc hb0 le_rfl
  obtain ⟨hlfin, hleq⟩ := volume_real_symmetricBodyOn hm hmeas hb0
    (fun x hx => hnonneg x ⟨hx.1, hx.2.trans hbh⟩) hleft
  obtain ⟨hrfin, hreq⟩ := volume_real_symmetricBodyOn hm hmeas hbh
    (fun x hx => hnonneg x ⟨hb0.trans hx.1, hx.2⟩) hright
  have hbounds := AsymptoticSubspace.lemma_volumes_of_concave (d := m + 1) (by omega)
    hh hα0 hα1 hmeas hconc hnonneg
  dsimp at hbounds ⊢
  refine ⟨⟨hlfin, hleq, ?_⟩, ⟨hrfin, hreq, ?_⟩⟩
  · rw [hleq]
    simpa using hbounds.1
  · rw [hreq]
    simpa using hbounds.2

end AsymptoticSubspace.PaperFormalization
