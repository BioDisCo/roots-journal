-- TeX label: lem:convex:zero:hyperplane
-- A convex set has zero volume iff it is contained in a proper affine subspace.

module

public import AsymptoticSubspace.PaperFormalizationCore

@[expose] public section

noncomputable section

namespace AsymptoticSubspace

open PaperFormalization

theorem lemma_convex_zero_hyperplane_paper
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {C : Set V} (hCconv : Convex ℝ C) :
    (∃ E : AffineSubspace ℝ V, E ≠ ⊤ ∧ C ⊆ E) ↔ MeasureTheory.volume C = 0 :=
  lemma_convex_zero_hyperplane hCconv

end AsymptoticSubspace
