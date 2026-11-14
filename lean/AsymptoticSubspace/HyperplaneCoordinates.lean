import AsymptoticSubspace.SymmetrizationCoordinates

/-! Rotation and translation of a specified hyperplane to the first-coordinate plane. -/

noncomputable section

namespace AsymptoticSubspace.PaperFormalization

open Set MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

omit [MeasurableSpace V] [BorelSpace V] in
/-- Choose orthonormal coordinates whose first axis is normal to the given
hyperplane. The positive factor records normalization of its defining functional. -/
lemma exists_axial_isometry {m : ℕ} (hd : Module.finrank ℝ V = m + 1)
    (l : V →ₗ[ℝ] ℝ) (hl : l ≠ 0) :
    ∃ (b : OrthonormalBasis (Fin (m + 1)) ℝ V) (c : ℝ),
      0 < c ∧ ∀ x, b.repr x 0 = c * l x := by
  classical
  let v := (InnerProductSpace.toDual ℝ V).symm l.toContinuousLinearMap
  have hv : v ≠ 0 := by
    intro hv
    apply hl
    ext x
    calc
      l x = inner ℝ v x :=
        (InnerProductSpace.toDual_symm_apply (x := x) (y := l.toContinuousLinearMap)).symm
      _ = 0 := by rw [hv, inner_zero_left]
  let u := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, norm_inv, norm_ne_zero_iff.mpr hv]
  let w : Fin (m + 1) → V := fun _ => u
  have hw : Orthonormal ℝ (({0} : Set (Fin (m + 1))).restrict w) := by
    refine ⟨fun _ => hu, ?_⟩
    intro i j hij
    exact (hij (Subtype.ext (i.property.trans j.property.symm))).elim
  obtain ⟨b, hb⟩ := hw.exists_orthonormalBasis_extension_of_card_eq (by simpa using hd)
  refine ⟨b, ‖v‖⁻¹, inv_pos.mpr (norm_pos_iff.mpr hv), fun x => ?_⟩
  rw [b.repr_apply_apply, hb 0 (by simp)]
  change inner ℝ u x = ‖v‖⁻¹ * l x
  rw [show u = ‖v‖⁻¹ • v from rfl, real_inner_smul_left]
  congr 1
  exact InnerProductSpace.toDual_symm_apply

/-- The coordinate map used in Lemma 10 preserves volume and sends the level
`l x = l p` to `z.1 = 0`. -/
lemma exists_hyperplane_coordinates {m : ℕ} (hd : Module.finrank ℝ V = m + 1)
    (l : V →ₗ[ℝ] ℝ) (hl : l ≠ 0) (p : V) :
    ∃ (F : V ≃ᵃ[ℝ] ℝ × EuclideanSpace ℝ (Fin m)) (c : ℝ),
      Continuous F ∧ MeasurePreserving F ∧ 0 < c ∧
      ∀ x, (F x).1 = c * (l x - l p) := by
  obtain ⟨b, c, hc, hb⟩ := exists_axial_isometry hd l hl
  let e := b.repr.toContinuousLinearEquiv.trans (axialCoordinates m)
  let F : V ≃ᵃ[ℝ] ℝ × EuclideanSpace ℝ (Fin m) :=
    (AffineEquiv.constVAdd ℝ V (-p)).trans e.toAffineEquiv
  have hF (x : V) : F x = axialCoordinates m (b.repr (x - p)) := by
    simp [F, e, sub_eq_add_neg, add_comm]
  refine ⟨F, c, ?_, ?_, hc, ?_⟩
  · have heq : (F : V → ℝ × EuclideanSpace ℝ (Fin m)) = fun x => e (x - p) :=
      funext hF
    rw [heq]
    exact e.continuous.comp (continuous_id.sub continuous_const)
  · have h := (axialCoordinates_measurePreserving m).comp
      (b.measurePreserving_repr.comp (measurePreserving_sub_right volume p))
    convert h using 1
    funext x
    exact hF x
  · intro x
    rw [hF]
    change b.repr (x - p) 0 = c * (l x - l p)
    rw [hb, map_sub]

end AsymptoticSubspace.PaperFormalization
