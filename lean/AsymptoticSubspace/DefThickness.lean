-- TeX label: def:thickness
-- Definitions of pairDiameter and thicknessOn (projection-based thickness).

import AsymptoticSubspace.LemDeltaContractionCore

/-!
# Definition 16: round projections and thickness

`roundProjection E M t` is the paper's `Π_{t+1}`: it projects orthogonally
onto `dir(X_{M(t+1)}(t))ᗮ`. The equality below identifies its construction
with this description. `thicknessOn` is `Δ_Π(X)`; `pairDiameter` supplies
the Lipschitz constant in Lemma 18.
-/

namespace AsymptoticSubspace

/-- The round projection is the orthogonal projection onto the complement of
the direction space of the broadcasting values before the update. -/
theorem roundProjection_eq_orthogonal_vectorSpan
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ}
    (E : ComputationalModel.AveragingExecution (V := V) n)
    (M : ComputationalModel.Round → Finset (ComputationalModel.Proc n)) (t : ℕ) :
    roundProjection E M t =
      (vectorSpan ℝ (ModelLemmas.ValuesOn E t (M (t + 1))))ᗮ.starProjection := by
  simp only [roundProjection, diffSubmodule_eq_vectorSpan_valuesOn]

def pairDiameter
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (X : Finset V) (hX : X.Nonempty) : ℝ :=
  (X.product X).sup'
    (by
      rcases hX with ⟨x, hx⟩
      exact ⟨(x, x), by simp [hx]⟩)
    (fun p => ‖p.1 - p.2‖)

def thicknessOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (P : V →L[ℝ] V)
    (X : Finset V) (hX : X.Nonempty) : ℝ :=
  (X.product X).sup'
    (by
      rcases hX with ⟨x, hx⟩
      exact ⟨(x, x), by simp [hx]⟩)
    (fun p => ‖P (p.1 - p.2)‖)

section Verification

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Verification anchor: local pair-diameter formula matches the model bridge definition. -/
@[simp] theorem pairDiameter_eq_modelLemmas
    (X : Finset V) (hX : X.Nonempty) :
    pairDiameter X hX = ModelLemmas.pairDiameter X hX :=
  rfl

/-- Verification anchor: local thickness formula matches the model bridge definition. -/
@[simp] theorem thicknessOn_eq_modelLemmas
    (P : V →L[ℝ] V)
    (X : Finset V) (hX : X.Nonempty) :
    thicknessOn P X hX = ModelLemmas.thicknessOn P X hX :=
  rfl

end Verification

end AsymptoticSubspace
