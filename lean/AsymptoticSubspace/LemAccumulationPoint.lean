-- TeX label: lem:accumulation_point
-- A sequence of orthogonal projections has a convergent subsequence
-- whose limit is also an orthogonal projection.

module

public import AsymptoticSubspace.LemDeltaContractionCore

/-! Lemma 17: accumulation of orthogonal projections. -/

@[expose] public section

noncomputable section

namespace AsymptoticSubspace

open PaperFormalization

theorem lemma_accumulation_point_paper
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (PiSeq : ℕ → V →L[ℝ] V)
    (hPi : ∀ t, IsStarProjection (PiSeq t)) :
    ∃ P : V →L[ℝ] V, IsStarProjection P ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Filter.Tendsto (PiSeq ∘ φ) Filter.atTop (nhds P) :=
  lemma_accumulation_point PiSeq hPi

/-- Lemma 17 for the projections constructed from the broadcasting values.
The index `t` represents the paper's projection at update round `t + 1`. -/
theorem lemma_roundProjection_accumulation
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {n : ℕ} (E : ComputationalModel.AveragingExecution (V := V) n)
    (M : ComputationalModel.Round → Finset (ComputationalModel.Proc n)) :
    ∃ P : V →L[ℝ] V, IsStarProjection P ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Filter.Tendsto (roundProjection E M ∘ φ) Filter.atTop (nhds P) :=
  lemma_accumulation_point_paper (roundProjection E M) (roundProjection_isStarProjection E M)

end AsymptoticSubspace
