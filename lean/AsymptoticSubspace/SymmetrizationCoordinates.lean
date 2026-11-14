module

public import AsymptoticSubspace.Symmetrization

@[expose] public section

noncomputable section

namespace AsymptoticSubspace.PaperFormalization

open MeasureTheory Set

/-- Separate the first coordinate of standard Euclidean space from its
orthogonal transverse coordinates. The product norm is immaterial: the map
is a continuous linear equivalence and preserves the canonical volumes. -/
def axialCoordinates (m : ℕ) :
    EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] ℝ × EuclideanSpace ℝ (Fin m) :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun z => (z 0, WithLp.toLp 2 (fun i => z i.succ))
    invFun := fun p => WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2))
    left_inv := by
      intro z
      apply PiLp.ext
      intro i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    right_inv := by
      intro p
      apply Prod.ext
      · rfl
      · apply PiLp.ext; intro i; simp
    map_add' := by intro z w; rfl
    map_smul' := by intro c z; rfl }

theorem axialCoordinates_measurePreserving (m : ℕ) : MeasurePreserving (axialCoordinates m) := by
  have hsplit := volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
  have hprod := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (PiLp.volume_preserving_toLp (Fin m))
  have h := hprod.comp (hsplit.comp (PiLp.volume_preserving_ofLp (Fin (m + 1))))
  convert h using 1
  ext z
  · rfl
  · simp [axialCoordinates, MeasurableEquiv.piFinSuccAbove, Fin.tail]

/-- The symmetrized body for an arbitrary compact body in standard Euclidean
coordinates, with the true axial support retained. -/
def euclideanSymmetrization {m : ℕ} (P : Set (EuclideanSpace ℝ (Fin (m + 1)))) :
    Set (ℝ × EuclideanSpace ℝ (Fin m)) :=
  supportedSymmetrization (axialCoordinates m '' P)

theorem euclideanSymmetrization_volume {m : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin (m + 1)))} (hP : IsCompact P) :
    volume (euclideanSymmetrization P) = volume P := by
  rw [euclideanSymmetrization,
    supportedSymmetrization_volume (hP.image (axialCoordinates m).continuous)]
  rw [← (axialCoordinates_measurePreserving m).map_eq,
    Measure.map_apply (axialCoordinates m).continuous.measurable
      (hP.image (axialCoordinates m).continuous).measurableSet,
    Set.preimage_image_eq _ (axialCoordinates m).injective]

theorem euclideanSymmetrization_convex {m : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin (m + 1)))} (hP : IsCompact P) (hc : Convex ℝ P) :
    Convex ℝ (euclideanSymmetrization P) := by
  by_cases hm : m = 0
  · subst m
    rw [euclideanSymmetrization, supportedSymmetrization_dim_one]
    exact hc.linear_image (axialCoordinates 0).toLinearMap
  · exact supportedSymmetrization_convex (Nat.pos_of_ne_zero hm)
      (hP.image (axialCoordinates m).continuous) (hc.linear_image (axialCoordinates m).toLinearMap)

end AsymptoticSubspace.PaperFormalization
