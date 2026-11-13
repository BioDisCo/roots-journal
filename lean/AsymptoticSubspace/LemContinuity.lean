-- TeX label: lem:continuity
-- The thickness function is Lipschitz continuous in the projection operator,
-- with Lipschitz constant equal to the pairDiameter of the point set.

import AsymptoticSubspace.ModelBridgeCore

/-! Lemma 18: Lipschitz continuity of thickness. -/

noncomputable section

namespace AsymptoticSubspace

open ModelLemmas

theorem lemma_continuity
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (X : Finset V) (hX : X.Nonempty)
    (P Q : V →L[ℝ] V) :
    |thicknessOn P X hX - thicknessOn Q X hX|
      ≤ ‖P - Q‖ * pairDiameter X hX :=
  lemma_continuity_complete (V := V) X hX P Q

/-- The thickness function is Lipschitz, with the diameter as a constant.
This holds for all continuous linear maps, hence for orthogonal projections. -/
theorem thickness_lipschitz
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (X : Finset V) (hX : X.Nonempty) :
    LipschitzWith (Real.toNNReal (pairDiameter X hX))
      (fun P : V →L[ℝ] V => thicknessOn P X hX) := by
  have hdiam : 0 ≤ pairDiameter X hX := by
    obtain ⟨x, hx⟩ := hX
    have h := Finset.le_sup' (f := fun p : V × V => ‖p.1 - p.2‖)
      (show (x, x) ∈ X.product X by simp [hx])
    simpa [pairDiameter] using h
  apply LipschitzWith.of_dist_le_mul
  intro P Q
  simpa only [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hdiam, mul_comm] using
    lemma_continuity X hX P Q

end AsymptoticSubspace
