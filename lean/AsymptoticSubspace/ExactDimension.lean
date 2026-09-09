import AsymptoticSubspace.StatefulAlgorithms

noncomputable section

namespace AsymptoticSubspace

open ComputationalModel

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

lemma exists_supermodule_add_finrank (S : Submodule ℝ V) (q : ℕ)
    (h : Module.finrank ℝ S + q ≤ Module.finrank ℝ V) :
    ∃ W : Submodule ℝ V, S ≤ W ∧ Module.finrank ℝ W = Module.finrank ℝ S + q := by
  induction q generalizing S with
  | zero => exact ⟨S, le_rfl, by omega⟩
  | succ q ih =>
    obtain ⟨v, hv⟩ := S.exists_of_finrank_lt (by omega)
    have hvS : v ∉ S := by simpa using hv 1 one_ne_zero
    have hv0 : v ≠ 0 := by intro he; exact hvS (he ▸ S.zero_mem)
    let S' := S ⊔ Submodule.span ℝ ({v} : Set V)
    have hdim : Module.finrank ℝ S' = Module.finrank ℝ S + 1 := by
      have hd : Disjoint S (Submodule.span ℝ ({v} : Set V)) :=
        (Submodule.disjoint_span_singleton' hv0).mpr hvS
      have he := S.finrank_sup_add_finrank_inf_eq (Submodule.span ℝ ({v} : Set V))
      have hi : S ⊓ Submodule.span ℝ ({v} : Set V) = ⊥ := hd.eq_bot
      rw [hi, finrank_bot, Nat.add_zero, finrank_span_singleton hv0] at he
      exact he
    obtain ⟨W, hSW, hW⟩ := ih S' (by omega)
    exact ⟨W, le_trans le_sup_left hSW, by omega⟩

/-- Any smaller-dimensional affine subspace is contained in one of exactly
the requested dimension, provided that dimension fits in the ambient space. -/
theorem exists_affine_superspace_finrank (E : AffineSubspace ℝ V)
    (hne : (E : Set V).Nonempty) {s : ℕ}
    (hEs : Module.finrank ℝ E.direction ≤ s) (hsV : s ≤ Module.finrank ℝ V) :
    ∃ F : AffineSubspace ℝ V, E ≤ F ∧ Module.finrank ℝ F.direction = s := by
  obtain ⟨W, hEW, hW⟩ := exists_supermodule_add_finrank E.direction
    (s - Module.finrank ℝ E.direction) (by omega)
  obtain ⟨p, hp⟩ := hne
  refine ⟨AffineSubspace.mk' p W, ?_, ?_⟩
  · intro x hx
    exact AffineSubspace.mem_mk'.mpr (hEW (AffineSubspace.vsub_mem_direction hx hp))
  · rw [AffineSubspace.direction_mk', hW]
    omega

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
lemma convergesToSet_mono {x : Round → V} {S T : Set V}
    (h : ConvergesToSet x S) (hST : S ⊆ T) : ConvergesToSet x T := by
  refine ⟨h.1.mono hST, ?_⟩
  intro ε hε
  obtain ⟨t, ht⟩ := h.2 ε hε
  exact ⟨t, fun u hu => (Metric.infDist_le_infDist_of_subset hST h.1).trans_lt (ht u hu)⟩

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
