module

public import AsymptoticSubspace.ThmRooted
public import AsymptoticSubspace.EqualNeighbor
public import AsymptoticSubspace.ImpossibilityProofCore

@[expose] public section

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

end AsymptoticSubspace

namespace AsymptoticSubspace.ComputationalModel

namespace StatefulAlgorithm

variable {V State : Type*} {n : ℕ} (A : StatefulAlgorithm V n State)

@[simp] lemma run_zero (G : Round → CommGraph n) (init : Proc n → V) (i : Proc n) :
    A.run G init 0 i = init i := A.output_initial i (init i)

/-- Local indistinguishability does not require vector-valued or bounded state. -/
theorem run_static_eq_on_reachers (G : CommGraph n) (init₁ init₂ : Proc n → V) (i : Proc n)
    (hEq : ∀ j, Reachable G j i → init₁ j = init₂ j) :
    ∀ t, A.run (fun _ => G) init₁ t i = A.run (fun _ => G) init₂ t i := by
  have hAll : ∀ t j, Reachable G j i →
      A.runState (fun _ => G) init₁ t j = A.runState (fun _ => G) init₂ t j := by
    intro t
    induction t with
    | zero => intro j hj; simp only [runState, hEq j hj]
    | succ t ih =>
      intro j hj
      apply A.locality _ G G _ _ j (fun _ => Iff.rfl)
      intro p hpj
      exact ih p (Relation.ReflTransGen.head hpj hj)
  exact fun t => congrArg (A.output t i) (hAll t i Relation.ReflTransGen.refl)

end StatefulAlgorithm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}

/-- Agreement and validity for arbitrary-state local protocols. -/
def StatefulSolves {State : Type*} (A : StatefulAlgorithm V n State)
    (N : ObliviousMessageAdversary n) (s : ℕ) : Prop :=
  ∀ (G : Round → CommGraph n) (init : Proc n → V), AdmissibleTrace N G →
    ∃ E : AffineSubspace ℝ V, FiniteDimensional ℝ E.direction ∧
      Module.finrank ℝ E.direction ≤ s ∧
      (∀ i, ConvergesToSet (fun t => A.run G init t i) (E : Set V)) ∧
      (∀ i, ConvergesToSet (fun t => A.run G init t i) (convexHull ℝ (Set.range init)))

def DeterministicAlgorithm.toStateful (A : DeterministicAlgorithm V n) :
    StatefulAlgorithm V n V where
  initialState _ x := x
  step := A.step
  output _ _ x := x
  output_initial _ _ := rfl
  locality := A.locality

lemma DeterministicAlgorithm.toStateful_run (A : DeterministicAlgorithm V n)
    (G : Round → CommGraph n) (init : Proc n → V) : A.toStateful.run G init = A.run G init := by
  have hs : ∀ t, A.toStateful.runState G init t = A.run G init t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      funext i
      change A.step (t + 1) (G (t + 1)) (A.toStateful.runState G init t) i =
        A.step (t + 1) (G (t + 1)) (A.run G init t) i
      rw [ih]
  funext t i
  exact congrFun (hs t) i

lemma DeterministicAlgorithm.toStateful_solves (A : DeterministicAlgorithm V n)
    (N : ObliviousMessageAdversary n) (s : ℕ) :
    StatefulSolves A.toStateful N s ↔ SolvesAsymptoticSubspace A N s := by
  simp only [StatefulSolves, SolvesAsymptoticSubspace, A.toStateful_run]

end AsymptoticSubspace.ComputationalModel

namespace AsymptoticSubspace

open ComputationalModel ModelLemmas PaperFormalization Set

/-- The impossibility theorem for arbitrary internal state and local initialization,
not only memoryless averaging or protocols whose state equals their output. -/
theorem lemma_imposs_stateful {V State : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : ℕ} (N : ObliviousMessageAdversary n) (s : ℕ)
    (hnotRooted : ¬ IsKRootedAdversary N (s + 1)) (hfin : s < Module.finrank ℝ V) :
    ¬ ∃ A : StatefulAlgorithm V n State, StatefulSolves A N s := by
  rintro ⟨A, hA⟩
  obtain ⟨d⟩ := modelGrounded_of_not_kRootedAdversary (N := N) (s := s) hnotRooted
  obtain ⟨init, hAff, hConst⟩ := exists_init_for_static_data (V := V) N s d hfin
  let G : Round → CommGraph n := fun _ => d.graph
  have hAdm : AdmissibleTrace N G := fun _ => d.graph_in_adversary
  obtain ⟨E, hfdE, hdimE, hToE, _⟩ := hA G init hAdm
  have hclosedE : IsClosed (E : Set V) := by
    let : FiniteDimensional ℝ E.direction := hfdE
    exact (AffineSubspace.isClosed_direction_iff (R := ℝ) (V := V) (P := V) E).mp
      (Submodule.closed_of_finiteDimensional (s := E.direction))
  have hsubset : range (fun p : d.roots => init p) ⊆ (E : Set V) := by
    rintro _ ⟨p, rfl⟩
    let initConst : Proc n → V := fun _ => init p
    have hEq : ∀ t, A.run G init t p = A.run G initConst t p :=
      A.run_static_eq_on_reachers d.graph init initConst p (hConst p p.property)
    obtain ⟨_, _, _, _, hvalid⟩ := hA G initConst hAdm
    have hrange : range initConst = ({init p} : Set V) := by
      ext x
      constructor
      · rintro ⟨q, rfl⟩; rfl
      · intro hx; exact ⟨p, (mem_singleton_iff.mp hx).symm⟩
    have hsingleton : ConvergesToSet (fun t => A.run G initConst t p) ({init p} : Set V) := by
      simpa [hrange, convexHull_singleton] using hvalid p
    have hconv : ConvergesTo (fun t => A.run G init t p) (init p) := by
      have hp := convergesToSet_singleton_iff.mp hsingleton
      simpa only [hEq] using hp
    have hmem := mem_closure_of_convergesTo_and_convergesToSet (hTo := hconv) (hToSet := hToE p)
    simpa [hclosedE.closure_eq] using hmem
  exact (lemma_imposs_complete (xLim := fun p : d.roots => init p)
    (by simpa using d.roots_card) hAff) ⟨E, hfdE, hdimE, hsubset⟩

universe u

/-- The final characterization with arbitrary internal state admitted. -/
theorem corollary_characterization_stateful
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {n : ℕ} [NeZero n] (N : ObliviousMessageAdversary n) (s : ℕ)
    (hs : s < Module.finrank ℝ V) :
    (∃ (State : Type u) (A : StatefulAlgorithm V n State), StatefulSolves A N s) ↔
      IsKRootedAdversary N (s + 1) := by
  constructor
  · rintro ⟨State, A, hA⟩
    by_contra hnot
    exact lemma_imposs_stateful N s hnot hs ⟨A, hA⟩
  · intro hroot
    exact ⟨V, (equalNeighborAlgorithm V n).toStateful,
      ((equalNeighborAlgorithm V n).toStateful_solves N s).mpr (equalNeighbor_solves N s hs hroot)⟩

end AsymptoticSubspace
