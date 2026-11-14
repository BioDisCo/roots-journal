module

public import Mathlib

/-! The simplex-volume formula used in Lemma 11. -/

@[expose] public section

noncomputable section

namespace AsymptoticSubspace.SimplexVolume

open Set MeasureTheory
open scoped BigOperators ENNReal

/-- Nonnegative coordinates whose sum is at most `r` (a simplex when `r ≥ 0`). -/
def coordinateSimplex (n : ℕ) (r : ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ r}

lemma coordinateSimplex_closed (n : ℕ) (r : ℝ) : IsClosed (coordinateSimplex n r) := by
  have hnonneg : IsClosed {x : Fin n → ℝ | ∀ i, 0 ≤ x i} := by
    rw [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  exact hnonneg.inter
    (isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)

lemma coordinateSimplex_empty {n : ℕ} {r : ℝ} (hr : r < 0) :
    coordinateSimplex n r = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have : 0 ≤ ∑ i, x i := Finset.sum_nonneg (fun i _ => hx.1 i)
  linarith [hx.2]

lemma coordinateSimplex_cons (n : ℕ) (r x : ℝ) :
    (fun y : Fin n → ℝ => Fin.cons x y) ⁻¹' coordinateSimplex (n + 1) r =
      if 0 ≤ x then coordinateSimplex n (r - x) else ∅ := by
  ext y
  simp only [mem_preimage, coordinateSimplex, mem_ofPred_eq, Fin.forall_fin_succ,
    Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_succ]
  split_ifs <;> simp_all only [mem_ofPred_eq, mem_empty_iff_false, false_and, true_and]
  constructor <;> rintro ⟨h, hsum⟩ <;> exact ⟨h, by linarith⟩

/-- Repeated slicing gives the factor `1 / n!` for the coordinate simplex. -/
theorem volume_coordinateSimplex (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    volume (coordinateSimplex n r) = ENNReal.ofReal (r ^ n / n.factorial) := by
  induction n generalizing r with
  | zero =>
    have hset : coordinateSimplex 0 r = univ := by ext x; simp [coordinateSimplex, hr]
    simp only [hset, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, ENNReal.ofReal_one]
    rw [volume_pi, Measure.pi_univ]
    simp
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
    have hslice (x : ℝ) :
        volume ((fun y : Fin n → ℝ => Fin.cons x y) ⁻¹' coordinateSimplex (n + 1) r) =
        (Icc 0 r).indicator (fun x => ENNReal.ofReal ((r - x) ^ n / n.factorial)) x := by
      rw [coordinateSimplex_cons]
      by_cases hx : 0 ≤ x
      · rw [ite_eq_left hx]
        by_cases hxr : x ≤ r
        · rw [indicator_of_mem (show x ∈ Icc 0 r from ⟨hx, hxr⟩), ih (sub_nonneg.mpr hxr)]
        · rw [coordinateSimplex_empty (by linarith), measure_empty,
            indicator_of_notMem (by simpa [hx] using hxr)]
      · rw [ite_eq_right hx, measure_empty, indicator_of_notMem (by simp [hx])]
    have hmeasure : volume (coordinateSimplex (n + 1) r) =
        ∫⁻ x : ℝ, (Icc 0 r).indicator
          (fun x => ENNReal.ofReal ((r - x) ^ n / n.factorial)) x := by
      rw [← he.measure_preimage
        (coordinateSimplex_closed (n + 1) r).measurableSet.nullMeasurableSet]
      change (volume.prod volume) (e.symm ⁻¹' coordinateSimplex (n + 1) r) = _
      rw [Measure.prod_apply
        ((coordinateSimplex_closed (n + 1) r).measurableSet.preimage e.symm.measurable)]
      apply lintegral_congr
      intro x
      convert hslice x using 2
      ext y
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.consEquiv]
    rw [hmeasure, lintegral_indicator measurableSet_Icc]
    have hcont : Continuous (fun x : ℝ => (r - x) ^ n / (n.factorial : ℝ)) := by fun_prop
    rw [← ofReal_integral_eq_lintegral_ofReal (hcont.continuousOn.integrableOn_Icc)
      (ae_restrict_of_forall_mem measurableSet_Icc (fun x hx =>
        div_nonneg (pow_nonneg (sub_nonneg.mpr hx.2) _) (Nat.cast_nonneg _)))]
    congr 1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr]
    rw [intervalIntegral.integral_div,
      intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ n) r,
      integral_pow]
    simp only [sub_zero, sub_self, zero_pow (Nat.succ_ne_zero n), sub_zero,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    exact div_div _ _ _

lemma coordinateSimplex_eq_convexHull (n : ℕ) :
    coordinateSimplex n 1 =
      convexHull ℝ (insert 0 (range (fun i : Fin n => Pi.single i (1 : ℝ)))) := by
  apply Subset.antisymm
  · intro x hx
    apply mem_convexHull_of_exists_fintype
      (Fin.cons (1 - ∑ i, x i) x) (Fin.cons 0 (fun i : Fin n => Pi.single i (1 : ℝ)))
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact sub_nonneg.mpr hx.2
      · exact hx.1 j
    · simp [Fin.sum_univ_succ]
    · intro i
      refine Fin.cases (by simp) (fun j => ?_) i
      exact mem_insert_of_mem _ (mem_range_self j)
    · ext j
      simp [Fin.sum_univ_succ, Finset.sum_apply, Pi.single_apply, smul_eq_mul]
  · apply convexHull_min
    · rintro x (rfl | ⟨i, rfl⟩)
      · simp [coordinateSimplex]
      · simp [coordinateSimplex, Pi.single_apply, apply_ite (fun x : ℝ => 0 ≤ x)]
    · intro x hx y hy a b ha hb hab
      refine ⟨fun i => add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i)), ?_⟩
      change ∑ i, (a * x i + b * y i) ≤ 1
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      nlinarith [hx.2, hy.2]

section Determinant

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {n : ℕ}

/-- The reference orthonormal simplex has volume `1 / n!`. -/
lemma volume_orthonormal_simplex (o : OrthonormalBasis (Fin n) ℝ V) :
    volume (convexHull ℝ (insert 0 (range o))) = ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
  let e := o.toBasis.equivFunL.symm
  have he : MeasurePreserving e := by
    convert o.measurePreserving_repr_symm.comp (PiLp.volume_preserving_toLp (Fin n)) using 1
    ext x
    rfl
  have hmap (i : Fin n) : e (Pi.single i 1) = o i := by
    change o.toBasis.equivFun.symm (Pi.single i 1) = o i
    simp
  have hset : e '' coordinateSimplex n 1 = convexHull ℝ (insert 0 (range o)) := by
    rw [coordinateSimplex_eq_convexHull]
    change e.toLinearMap '' convexHull ℝ _ = _
    rw [LinearMap.image_convexHull]
    congr 1
    simp [image_insert_eq, ← range_comp, Function.comp_def, hmap]
  have hc : MeasurableSet (e '' coordinateSimplex n 1) :=
    (e.toHomeomorph.isClosedMap _ (coordinateSimplex_closed n 1)).measurableSet
  rw [← hset, ← he.measure_preimage hc.nullMeasurableSet,
    e.injective.preimage_image, volume_coordinateSimplex n zero_le_one, one_pow]

/-- In orthonormal coordinates the simplex volume is the absolute determinant
 of its edge vectors divided by `n!`. -/
theorem volume_simplex (o : OrthonormalBasis (Fin n) ℝ V)
    (v : Fin n → V) (p : V) :
    volume (convexHull ℝ (insert p (range (fun i => p + v i)))) =
      ENNReal.ofReal (|o.toBasis.det v| / (n.factorial : ℝ)) := by
  let f := o.toBasis.constr ℕ v
  have hlinear : f '' convexHull ℝ (insert 0 (range o)) =
      convexHull ℝ (insert 0 (range v)) := by
    rw [LinearMap.image_convexHull]
    congr 1
    simp [image_insert_eq, ← range_comp, Function.comp_def, f]
  have hdet : LinearMap.det f = o.toBasis.det v := by
    rw [← LinearMap.det_toMatrix o.toBasis, ← Module.Basis.toMatrix_eq_toMatrix_constr,
      Module.Basis.det_apply]
  let τ : V →ᵃ[ℝ] V := AffineMap.const ℝ V p + AffineMap.id ℝ V
  have hτ : (τ : V → V) = fun x => p + x := rfl
  have htranslate : (fun x => p + x) '' convexHull ℝ (insert 0 (range v)) =
      convexHull ℝ (insert p (range (fun i => p + v i))) := by
    rw [← hτ, AffineMap.image_convexHull, hτ]
    congr 1
    simp [image_insert_eq, ← range_comp, Function.comp_def]
  rw [← htranslate, image_add_left, measure_preimage_add, ← hlinear,
    Measure.addHaar_image_linearMap, hdet, volume_orthonormal_simplex,
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  ring

end Determinant

end AsymptoticSubspace.SimplexVolume
