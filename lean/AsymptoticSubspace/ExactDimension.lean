import AsymptoticSubspace.StatefulAlgorithms
import AsymptoticSubspace.AffineDimension

noncomputable section

namespace AsymptoticSubspace

open ComputationalModel

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Exact-dimensional form of the paper's specification. -/
def StatefulSolvesExact {State : Type*} {n : ℕ} (A : StatefulAlgorithm V n State)
    (N : ObliviousMessageAdversary n) (s : ℕ) : Prop :=
  ∀ (G : Round → CommGraph n) (init : Proc n → V), AdmissibleTrace N G →
    ∃ E : AffineSubspace ℝ V, Module.finrank ℝ E.direction = s ∧
      (∀ i, ConvergesToSet (fun t => A.run G init t i) (E : Set V)) ∧
      (∀ i, ConvergesToSet (fun t => A.run G init t i) (convexHull ℝ (Set.range init)))

theorem statefulSolvesExact_iff {State : Type*} {n : ℕ} [NeZero n]
    (A : StatefulAlgorithm V n State) (N : ObliviousMessageAdversary n) (s : ℕ)
    (hs : s ≤ Module.finrank ℝ V) : StatefulSolvesExact A N s ↔ StatefulSolves A N s := by
  constructor
  · intro h G init hG
    obtain ⟨E, hdim, hconv, hvalid⟩ := h G init hG
    exact ⟨E, inferInstance, hdim.le, hconv, hvalid⟩
  · intro h G init hG
    obtain ⟨E, _, hdim, hconv, hvalid⟩ := h G init hG
    obtain ⟨F, hEF, hF⟩ := exists_affine_superspace_finrank E (hconv 0).1 hdim hs
    exact ⟨F, hF, fun i => convergesToSet_mono (hconv i) hEF, hvalid⟩

universe u

/-- Whole-paper characterization: arbitrary internal state and an agreement
subspace of exactly dimension `s`, as opposed to merely at most `s`. -/
theorem corollary_characterization_exact
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {n : ℕ} [NeZero n] (N : ObliviousMessageAdversary n) (s : ℕ)
    (hs : s < Module.finrank ℝ V) :
    (∃ (State : Type u) (A : StatefulAlgorithm V n State), StatefulSolvesExact A N s) ↔
      IsKRootedAdversary N (s + 1) := by
  simp only [statefulSolvesExact_iff _ N s hs.le]
  exact corollary_characterization_stateful N s hs

end AsymptoticSubspace
