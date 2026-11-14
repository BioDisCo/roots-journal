module

public import AsymptoticSubspace.LemConvexZeroHyperplane
public import AsymptoticSubspace.AffineDimension

/-! Lemma 11: zero volume and containment in an affine hyperplane. -/

@[expose] public section

noncomputable section

namespace AsymptoticSubspace

open Set MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Exact-codimension-one version of `lem:convex:zero:hyperplane`.
The positive ambient dimension also covers the empty convex set correctly. -/
theorem lemma_convex_zero_hyperplane_exact (hd : 1 ≤ Module.finrank ℝ V)
    {C : Set V} (hCconv : Convex ℝ C) :
    (∃ E : AffineSubspace ℝ V,
      (E : Set V).Nonempty ∧
      Module.finrank ℝ E.direction + 1 = Module.finrank ℝ V ∧ C ⊆ E) ↔ volume C = 0 := by
  constructor
  · rintro ⟨E, _, hdim, hCE⟩
    apply (lemma_convex_zero_hyperplane_paper hCconv).mp
    refine ⟨E, ?_, hCE⟩
    intro hE
    have hdir : E.direction = ⊤ := by
      rw [hE, AffineSubspace.direction_top]
    rw [hdir, finrank_top] at hdim
    omega
  · intro hzero
    obtain ⟨E, hE, hCE⟩ := (lemma_convex_zero_hyperplane_paper hCconv).mpr hzero
    by_cases hne : (E : Set V).Nonempty
    · have hdir : E.direction ≠ ⊤ := by
        intro h
        exact hE ((AffineSubspace.direction_eq_top_iff_of_nonempty hne).mp h)
      have hdim := Submodule.finrank_lt hdir
      obtain ⟨F, hEF, hF⟩ := exists_affine_superspace_finrank E hne
        (s := Module.finrank ℝ V - 1) (by omega) (by omega)
      exact ⟨F, hne.mono hEF, by omega, hCE.trans hEF⟩
    · have hCempty : C = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        exact fun x hx => hne ⟨x, hCE hx⟩
      let E₀ : AffineSubspace ℝ V := AffineSubspace.mk' (0 : V) ⊥
      have hE₀ : (E₀ : Set V).Nonempty := ⟨0, by simp [E₀, AffineSubspace.mem_mk']⟩
      have hdim₀ : Module.finrank ℝ E₀.direction = 0 := by
        simp [E₀]
      obtain ⟨F, hE₀F, hF⟩ := exists_affine_superspace_finrank E₀ hE₀
        (s := Module.finrank ℝ V - 1) (by omega) (by omega)
      exact ⟨F, hE₀.mono hE₀F, by omega, by simp [hCempty]⟩

end AsymptoticSubspace
