module

public import AsymptoticSubspace.DefComputationalModel
public import AsymptoticSubspace.ActualRounds

@[expose] public section

noncomputable section

/-!
# Theorem 2 and Corollary 20

The computational model and problem specification are defined in
`DefComputationalModel`. This file gives their impossibility and characterization
results: `impossibility` is Theorem 2, while `characterization` and `safe_averaging`
are the two assertions of Corollary 20.
-/

namespace AsymptoticSubspace.PaperComputationalModel

open ComputationalModel

universe u

/-- Complete characterization using the paper-facing arbitrary-state,
message-local algorithm and exact-dimensional problem specification. -/
theorem characterization
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {n : ℕ} [NeZero n] (N : ComputationalModel.ObliviousMessageAdversary n) (s : ℕ)
    (hs : s < Module.finrank ℝ V) :
    (∃ (State : Type u) (A : Algorithm V n State), Solves A N s) ↔
      ComputationalModel.IsKRootedAdversary N (s + 1) :=
  corollary_characterization_actualRounds N s hs

/-- Theorem 2: impossibility for arbitrary-state local algorithms when the
adversary is not `(s + 1)`-rooted. -/
theorem impossibility
    {V State : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} [NeZero n]
    (N : ComputationalModel.ObliviousMessageAdversary n) (s : ℕ)
    (hs : s < Module.finrank ℝ V)
    (hnot : ¬ ComputationalModel.IsKRootedAdversary N (s + 1)) :
    ¬ ∃ A : Algorithm V n State, Solves A N s := by
  rintro ⟨A, hA⟩
  apply lemma_imposs_stateful N s hnot hs
  refine ⟨A, ?_⟩
  exact (statefulSolvesExact_iff A N s hs.le).mp
    ((statefulSolvesExactActualRounds_iff A N s).mp hA)

/-- Corollary 20, sufficiency for every α-safe averaging execution in a rooted
adversary, with agreement dimension exactly `s` and validity. -/
theorem safe_averaging
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} [NeZero n]
    (N : ComputationalModel.ObliviousMessageAdversary n) (s : ℕ)
    (hs : s < Module.finrank ℝ V)
    (hroot : ComputationalModel.IsKRootedAdversary N (s + 1))
    (E : ComputationalModel.AveragingExecution (V := V) n)
    (hE : AdmissibleActualTrace N E.graphs)
    (α : ℝ) (hα : 0 < α) (hsafe : AlphaSafeActualRounds E α) :
    ∃ W : AffineSubspace ℝ V, Module.finrank ℝ W.direction = s ∧
      (∀ i, ComputationalModel.ConvergesToSet (fun t => E.outputs t i) (W : Set V)) ∧
      (∀ i, ComputationalModel.ConvergesToSet (fun t => E.outputs t i) (ModelLemmas.Poly E 0)) := by
  simpa using theorem_rooted_exact_actualRounds (s + 1) (by omega) (by omega) E α hα hsafe
    (fun t ht => hroot (E.graphs t) (hE t ht))

private def remoteEdgeOff : ComputationalModel.CommGraph 3 where
  edge i j := i = j
  self_loop _ := rfl

private def remoteEdgeOn : ComputationalModel.CommGraph 3 where
  edge i j := i = j ∨ (i = 1 ∧ j = 2)
  self_loop _ := Or.inl rfl

/-- An illegal graph-observation oracle for the locality regression below. -/
def remoteEdgeIndicator (G : ComputationalModel.CommGraph 3) : ℝ := by
  classical
  exact if G.edge 1 2 then 1 else 0

/-- Regression test for cross-graph locality: process `0` cannot inspect the
remote edge `1 → 2`, which does not affect its incoming messages. This protocol
was permitted by the former same-graph-only locality condition. -/
theorem no_remote_edge_spy :
    ¬ ∃ A : Algorithm ℝ 3 ℝ,
      ∀ t G x, A.step t G x 0 = remoteEdgeIndicator G := by
  classical
  rintro ⟨A, hspy⟩
  have hview : ∀ j, remoteEdgeOff.edge j 0 ↔ remoteEdgeOn.edge j 0 := by
    intro j
    simp [remoteEdgeOff, remoteEdgeOn]
  have heq := A.locality 1 remoteEdgeOff remoteEdgeOn (fun _ => 0) (fun _ => 0) 0
    hview (fun _ _ => rfl)
  rw [hspy, hspy] at heq
  norm_num [remoteEdgeIndicator, remoteEdgeOff, remoteEdgeOn] at heq

end AsymptoticSubspace.PaperComputationalModel
