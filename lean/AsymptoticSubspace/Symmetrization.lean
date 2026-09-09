import AsymptoticSubspace.SymmetricBody
import AsymptoticSubspace.BrunnMinkowski.Weighted

noncomputable section

namespace AsymptoticSubspace.PaperFormalization

open Set MeasureTheory
open scoped Pointwise

/-- The section of a body at axial coordinate `x`, in transverse coordinates. -/
def axialSection {m : ℕ} (P : Set (ℝ × EuclideanSpace ℝ (Fin m))) (x : ℝ) :
    Set (EuclideanSpace ℝ (Fin m)) := Prod.mk x ⁻¹' P

lemma axialSection_isCompact {m : ℕ} {P : Set (ℝ × EuclideanSpace ℝ (Fin m))}
    (hP : IsCompact P) (x : ℝ) : IsCompact (axialSection P x) := by
  have hi : Isometry (Prod.mk x : EuclideanSpace ℝ (Fin m) → _) := by
    intro u v
    simp [Prod.edist_eq]
  exact hi.isClosedEmbedding.isCompact_preimage hP

lemma axialSection_convex {m : ℕ} {P : Set (ℝ × EuclideanSpace ℝ (Fin m))}
    (hP : Convex ℝ P) (x : ℝ) : Convex ℝ (axialSection P x) := by
  intro u hu v hv a b ha hb hab
  have h := hP hu hv ha hb hab
  simpa [axialSection, Prod.smul_mk, ← add_mul, hab] using h

lemma section_combination_subset {m : ℕ}
    {P : Set (ℝ × EuclideanSpace ℝ (Fin m))} (hP : Convex ℝ P)
    (x y : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • axialSection P x + b • axialSection P y ⊆ axialSection P (a * x + b * y) := by
  rintro _ ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩
  exact hP hu hv ha hb hab

lemma section_constant_pos (m : ℕ) : 0 < C_dMinusOne (m + 1) := by
  unfold C_dMinusOne
  exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _)
    (Real.Gamma_pos_of_pos (by positivity))

/-- The radius is constructed from the original section volume; no radius,
section-volume identity, or concavity proof is supplied as a hypothesis. -/
def sectionRadius {m : ℕ} (P : Set (ℝ × EuclideanSpace ℝ (Fin m))) (x : ℝ) : ℝ :=
  (volume.real (axialSection P x) / C_dMinusOne (m + 1)) ^ (m : ℝ)⁻¹

lemma sectionRadius_nonneg {m : ℕ} (P : Set (ℝ × EuclideanSpace ℝ (Fin m))) (x : ℝ) :
    0 ≤ sectionRadius P x :=
  Real.rpow_nonneg (div_nonneg ENNReal.toReal_nonneg (section_constant_pos m).le) _

lemma sectionRadius_measurable {m : ℕ} {P : Set (ℝ × EuclideanSpace ℝ (Fin m))}
    (hP : MeasurableSet P) : Measurable (sectionRadius P) := by
  exact ((measurable_measure_prodMk_left hP).ennreal_toReal.div_const _).pow_const _

lemma sectionRadius_pow {m : ℕ} (hm : 0 < m)
    (P : Set (ℝ × EuclideanSpace ℝ (Fin m))) (x : ℝ) :
    C_dMinusOne (m + 1) * sectionRadius P x ^ m = volume.real (axialSection P x) := by
  rw [sectionRadius, Real.rpow_inv_natCast_pow
    (div_nonneg (show 0 ≤ volume.real (axialSection P x) from measureReal_nonneg)
      (section_constant_pos m).le) (Nat.ne_of_gt hm)]
  exact mul_div_cancel₀ _ (section_constant_pos m).ne'

/-- Every transverse section has exactly the original section's volume,
including empty and lower-dimensional sections. -/
theorem symmetrization_section_volume {m : ℕ} (hm : 0 < m)
    {P : Set (ℝ × EuclideanSpace ℝ (Fin m))} (hP : IsCompact P) (x : ℝ) :
    volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) (sectionRadius P x)) =
      volume (axialSection P x) := by
  rw [section_ball_volume hm (sectionRadius_nonneg P x), sectionRadius_pow hm,
    measureReal_def, ENNReal.ofReal_toReal (axialSection_isCompact hP x).measure_lt_top.ne]

/-- The actual symmetrization of `P`, not an independently supplied rotational body. -/
def symmetrization {m : ℕ} (P : Set (ℝ × EuclideanSpace ℝ (Fin m))) :
    Set (ℝ × EuclideanSpace ℝ (Fin m)) := symmetricBody m (sectionRadius P)

lemma symmetrization_measurable {m : ℕ} {P : Set (ℝ × EuclideanSpace ℝ (Fin m))}
    (hP : MeasurableSet P) : MeasurableSet (symmetrization P) :=
  measurableSet_le (measurable_snd.dist measurable_const)
    ((sectionRadius_measurable hP).comp measurable_fst)

/-- Cavalieri gives preservation on every measurable axial region, not only
the total body or a prescribed interval. -/
theorem symmetrization_volume_on {m : ℕ} (hm : 0 < m)
    {P : Set (ℝ × EuclideanSpace ℝ (Fin m))} (hP : IsCompact P)
    {s : Set ℝ} (hs : MeasurableSet s) :
    volume (symmetrization P ∩ Prod.fst ⁻¹' s) = volume (P ∩ Prod.fst ⁻¹' s) := by
  change (volume.prod volume) _ = (volume.prod volume) _
  rw [Measure.prod_apply ((symmetrization_measurable hP.measurableSet).inter
      (hs.preimage measurable_fst)),
    Measure.prod_apply (hP.measurableSet.inter (hs.preimage measurable_fst))]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · have hxs : Prod.mk x ⁻¹' (Prod.fst ⁻¹' s) = (univ : Set (EuclideanSpace ℝ (Fin m))) := by
      ext z
      simp [hx]
    simp only [preimage_inter, hxs, inter_univ]
    simpa [symmetrization, symmetricBody, axialSection, Metric.closedBall, dist_eq_norm] using
      symmetrization_section_volume hm hP x
  · have hxs : Prod.mk x ⁻¹' (Prod.fst ⁻¹' s) = (∅ : Set (EuclideanSpace ℝ (Fin m))) := by
      ext z
      simp [hx]
    simp only [preimage_inter, hxs, inter_empty]

theorem symmetrization_volume {m : ℕ} (hm : 0 < m)
    {P : Set (ℝ × EuclideanSpace ℝ (Fin m))} (hP : IsCompact P) :
    volume (symmetrization P) = volume P := by
  simpa using symmetrization_volume_on hm hP MeasurableSet.univ

lemma sectionRadius_eq_div {m : ℕ}
    (P : Set (ℝ × EuclideanSpace ℝ (Fin m))) (x : ℝ) :
    sectionRadius P x = volume.real (axialSection P x) ^ (m : ℝ)⁻¹ /
      C_dMinusOne (m + 1) ^ (m : ℝ)⁻¹ := by
  exact Real.div_rpow measureReal_nonneg (section_constant_pos m).le _

/-- Brunn–Minkowski proves concavity of the constructed radius on the axial
projection of the original convex body. It is not a theorem hypothesis. -/
theorem sectionRadius_concave {m : ℕ} (hm : 0 < m)
    {P : Set (ℝ × EuclideanSpace ℝ (Fin m))} (hP : IsCompact P) (hconv : Convex ℝ P) :
    ConcaveOn ℝ (Prod.fst '' P) (sectionRadius P) := by
  refine ⟨hconv.linear_image (LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin m))), ?_⟩
  rintro x ⟨⟨x', u⟩, hu, rfl⟩ y ⟨⟨y', v⟩, hv, rfl⟩ a b ha hb hab
  have h := BrunnMinkowski.weighted_brunn_minkowski hm
    (axialSection_isCompact hP x') (axialSection_isCompact hP y') ⟨u, hu⟩ ⟨v, hv⟩ ha hb
  have hmono : volume.real (a • axialSection P x' + b • axialSection P y') ≤
      volume.real (axialSection P (a * x' + b * y')) :=
    measureReal_mono (section_combination_subset hconv x' y' ha hb hab)
      (axialSection_isCompact hP _).measure_lt_top.ne
  have hroot := Real.rpow_le_rpow measureReal_nonneg hmono
    (by positivity : 0 ≤ (m : ℝ)⁻¹)
  have hdiv := div_le_div_of_nonneg_right (h.trans hroot)
    (Real.rpow_nonneg (section_constant_pos m).le (m : ℝ)⁻¹)
  simpa only [sectionRadius_eq_div, smul_eq_mul, add_div, mul_div_assoc] using hdiv

/-- Outside the axial projection, the constructed radius is zero. -/
theorem sectionRadius_zero_off_projection {m : ℕ} (hm : 0 < m)
    (P : Set (ℝ × EuclideanSpace ℝ (Fin m))) {x : ℝ} (hx : x ∉ Prod.fst '' P) :
    sectionRadius P x = 0 := by
  have he : axialSection P x = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    exact fun y hy => hx ⟨(x, y), hy, rfl⟩
  simp [sectionRadius, he, Real.zero_rpow (by positivity : (m : ℝ)⁻¹ ≠ 0)]

/-- The projection is exactly a finite closed interval. Concavity includes
its endpoints, including degenerate bodies and zero-volume sections. -/
theorem symmetrization_profile_interval {m : ℕ} (hm : 0 < m)
    {P : Set (ℝ × EuclideanSpace ℝ (Fin m))}
    (hP : IsCompact P) (hconv : Convex ℝ P) (hne : P.Nonempty) :
    ∃ a b : ℝ, a ≤ b ∧ Prod.fst '' P = Icc a b ∧
      ConcaveOn ℝ (Icc a b) (sectionRadius P) ∧
      (∀ x ∉ Icc a b, sectionRadius P x = 0) := by
  have hc : Convex ℝ (Prod.fst '' P) :=
    hconv.linear_image (LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin m)))
  have hn := hne.image Prod.fst
  have hk := hP.image continuous_fst
  have he := eq_Icc_of_connected_compact (hc.isConnected hn) hk
  refine ⟨sInf (Prod.fst '' P), sSup (Prod.fst '' P), ?_, he, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hn
    rw [he] at hx
    exact hx.1.trans hx.2
  · rw [← he]
    exact sectionRadius_concave hm hP hconv
  · intro x hx
    exact sectionRadius_zero_off_projection hm P (by rwa [he])

/-- Restricting to the true projection removes the extraneous null axis of
the unrestricted definition and also handles ambient dimension one correctly. -/
def supportedSymmetrization {m : ℕ} (P : Set (ℝ × EuclideanSpace ℝ (Fin m))) :
    Set (ℝ × EuclideanSpace ℝ (Fin m)) := symmetrization P ∩ Prod.fst ⁻¹' (Prod.fst '' P)

theorem supportedSymmetrization_convex {m : ℕ} (hm : 0 < m)
    {P : Set (ℝ × EuclideanSpace ℝ (Fin m))} (hP : IsCompact P) (hc : Convex ℝ P) :
    Convex ℝ (supportedSymmetrization P) := by
  have hconc := sectionRadius_concave hm hP hc
  rintro ⟨x, u⟩ ⟨hu, hx⟩ ⟨y, v⟩ ⟨hv, hy⟩ a b ha hb hab
  refine ⟨?_, hconc.1 hx hy ha hb hab⟩
  change dist (a • u + b • v) 0 ≤ sectionRadius P (a * x + b * y)
  rw [dist_zero_right]
  have hu' : ‖u‖ ≤ sectionRadius P x := by simpa [symmetrization, symmetricBody] using hu
  have hv' : ‖v‖ ≤ sectionRadius P y := by simpa [symmetrization, symmetricBody] using hv
  calc
    ‖a • u + b • v‖ ≤ ‖a • u‖ + ‖b • v‖ := norm_add_le _ _
    _ = a * ‖u‖ + b * ‖v‖ := by simp [norm_smul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * sectionRadius P x + b * sectionRadius P y :=
      add_le_add (mul_le_mul_of_nonneg_left hu' ha) (mul_le_mul_of_nonneg_left hv' hb)
    _ ≤ sectionRadius P (a * x + b * y) := hconc.2 hx hy ha hb hab

/-- In dimension one the supported construction is the identity, not a
zero-dimensional ball formula incorrectly interpreted at zero radius. -/
theorem supportedSymmetrization_dim_one (P : Set (ℝ × EuclideanSpace ℝ (Fin 0))) :
    supportedSymmetrization P = P := by
  ext z
  constructor
  · rintro ⟨_, w, hw, he⟩
    have : w = z := Prod.ext he (Subsingleton.elim _ _)
    exact this ▸ hw
  · intro hz
    refine ⟨?_, z, hz, rfl⟩
    simp [symmetrization, symmetricBody, sectionRadius, Subsingleton.elim z.2 0]

/-- Total volume preservation in every ambient dimension at least one. -/
theorem supportedSymmetrization_volume {m : ℕ}
    {P : Set (ℝ × EuclideanSpace ℝ (Fin m))} (hP : IsCompact P) :
    volume (supportedSymmetrization P) = volume P := by
  by_cases hm : m = 0
  · subst m
    rw [supportedSymmetrization_dim_one]
  · rw [supportedSymmetrization, symmetrization_volume_on (Nat.pos_of_ne_zero hm) hP
      (hP.image continuous_fst).measurableSet]
    congr 1
    exact inter_eq_left.mpr (fun z hz => ⟨z, hz, rfl⟩)

theorem volume_symmetricBodyOn_sectionRadius {m : ℕ} (hm : 0 < m)
    {P : Set (ℝ × EuclideanSpace ℝ (Fin m))} (hP : IsCompact P) (a b : ℝ) :
    volume (symmetricBodyOn m (sectionRadius P) a b) = volume (P ∩ Prod.fst ⁻¹' Icc a b) := by
  have he : symmetricBodyOn m (sectionRadius P) a b =
      symmetrization P ∩ Prod.fst ⁻¹' Icc a b := by
    ext z
    exact and_comm
  rw [he]
  exact symmetrization_volume_on hm hP measurableSet_Icc

/-- The paper's geometric volume bounds applied to sections of the original
convex body. Measurability, integrability, and radius concavity are all derived. -/
theorem lemma_volumes_of_convex_body {m : ℕ} (hm : 0 < m)
    {P : Set (ℝ × EuclideanSpace ℝ (Fin m))} (hP : IsCompact P) (hc : Convex ℝ P)
    {h α : ℝ} (hh : 0 < h) (hα0 : 0 < α) (hα1 : α < 1)
    (hproj : Icc 0 h ⊆ Prod.fst '' P) :
    let C := C_dMinusOne (m + 1)
    let r0 := sectionRadius P ((1 - α) * h)
    volume (P ∩ Prod.fst ⁻¹' Icc 0 ((1 - α) * h)) ≤
      ENNReal.ofReal (C * r0 ^ m * h / (α ^ m * ((m + 1 : ℕ) : ℝ)) * (1 - α ^ (m + 1))) ∧
    ENNReal.ofReal (C * r0 ^ m * h / (α ^ m * ((m + 1 : ℕ) : ℝ)) * α ^ (m + 1)) ≤
      volume (P ∩ Prod.fst ⁻¹' Icc ((1 - α) * h) h) := by
  have hbounds := lemma_volumes_geometric hm hh hα0 hα1
    (sectionRadius_measurable hP.measurableSet)
    ((sectionRadius_concave hm hP hc).subset hproj (convex_Icc _ _))
    (fun x _ => sectionRadius_nonneg P x)
  simpa only [volume_symmetricBodyOn_sectionRadius hm hP] using hbounds

end AsymptoticSubspace.PaperFormalization
