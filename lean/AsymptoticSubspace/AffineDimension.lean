import AsymptoticSubspace.ComputationalModelCore

/-! Enlarging an affine subspace to a prescribed dimension and convergence under containment. -/

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

end AsymptoticSubspace
