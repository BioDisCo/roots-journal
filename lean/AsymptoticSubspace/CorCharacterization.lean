-- Final corollary: Characterization of Asymptotic Subspace Consensus.
import AsymptoticSubspace.ThmRooted
import AsymptoticSubspace.EqualNeighbor
import AsymptoticSubspace.ThmImposs

noncomputable section

namespace AsymptoticSubspace

open ComputationalModel ModelLemmas

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {n : ℕ} [NeZero n]

/-- A concrete local deterministic solver for every rooted oblivious adversary. -/
theorem equalNeighbor_solves
    (N : ObliviousMessageAdversary n) (s : ℕ) (hs : s < Module.finrank ℝ V)
    (hroot : IsKRootedAdversary N (s + 1)) :
    SolvesAsymptoticSubspace (equalNeighborAlgorithm V n) N s := by
  intro G init hG
  have hα : 0 < 1 / (n : ℝ) := by
    have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    positivity
  obtain ⟨W, hdim, hconv, hvalid⟩ := theorem_rooted (s + 1) (by omega) (by omega)
    (equalNeighborExecution G init) (1 / (n : ℝ)) hα (equalNeighbor_safe G init)
    (fun t => hroot (G t) (hG t))
  refine ⟨W, inferInstance, ?_, hconv, hvalid⟩
  simpa using hdim

/-- Complete solvability characterization, with no graph-reduction hypothesis:
the sufficient direction uses the proved polynomial reduction and equal-neighbor
algorithm; the necessary direction uses the existing impossibility proof. -/
theorem corollary_characterization
    (N : ObliviousMessageAdversary n) (s : ℕ) (hs : s < Module.finrank ℝ V) :
    (∃ A : DeterministicAlgorithm V n, SolvesAsymptoticSubspace A N s) ↔
      IsKRootedAdversary N (s + 1) := by
  constructor
  · intro hsolves
    by_contra hnot
    exact lemma_imposs N s hnot hs hsolves
  · intro hroot
    exact ⟨equalNeighborAlgorithm V n, equalNeighbor_solves N s hs hroot⟩

end AsymptoticSubspace
