import AsymptoticSubspace.AveragingHulls

/-! Compactness and convergence of the nested convex hulls of an averaging execution. -/

noncomputable section

namespace AsymptoticSubspace.ModelLemmas

open ComputationalModel Set Filter
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {n : ℕ} [NeZero n]

omit [NeZero n] in
lemma poly_compact (E : AveragingExecution (V := V) n) (t : ℕ) :
    IsCompact (Poly E t) :=
  (finite_range (E.outputs t)).isCompact_convexHull

/-- The nonempty nested compact hulls have a nonempty intersection. -/
lemma poly_limit_nonempty (E : AveragingExecution (V := V) n) :
    (⋂ t, Poly E t).Nonempty := by
  apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun t => Poly E t) (ModelLemmas.poly_succ_subset E)
  · intro t
    exact ⟨E.outputs t 0, ModelLemmas.output_mem_poly_self E t 0⟩
  · exact poly_compact E 0
  · exact fun t => (poly_compact E t).isClosed

/-- Nestedness and compactness give convergence of the entire hull sequence
in Hausdorff distance, independently of any broadcasting hypothesis. -/
lemma poly_tendsto_limit (E : AveragingExecution (V := V) n) :
    Tendsto (fun t => Metric.hausdorffDist (Poly E t) (⋂ s, Poly E s)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨T, hT⟩ := exists_subset_nhds_of_isCompact'
    (ModelLemmas.poly_antitone E).directed_ge (poly_compact E)
    (fun t => (poly_compact E t).isClosed)
    (U := Metric.thickening (ε / 2) (⋂ s, Poly E s))
    (fun x hx => Metric.isOpen_thickening.mem_nhds
      (Metric.self_subset_thickening hε2 _ hx))
  refine ⟨T, fun t ht => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.hausdorffDist_nonneg]
  calc
    Metric.hausdorffDist (Poly E t) (⋂ s, Poly E s) ≤ ε / 2 := by
      apply Metric.hausdorffDist_le_of_mem_dist hε2.le
      · intro x hx
        obtain ⟨y, hy, hxy⟩ := Metric.mem_thickening_iff.mp
          (hT (ModelLemmas.poly_antitone E ht hx))
        exact ⟨y, hy, hxy.le⟩
      · intro y hy
        exact ⟨y, mem_iInter.mp hy t, by simpa using hε2.le⟩
    _ < ε := half_lt_self hε

/-- Every process approaches the intersection of the nested hulls. -/
lemma outputs_converge_poly_limit (E : AveragingExecution (V := V) n) (i : Proc n) :
    ConvergesToSet (fun t => E.outputs t i) (⋂ s, Poly E s) := by
  refine ⟨poly_limit_nonempty E, ?_⟩
  intro ε hε
  obtain ⟨T, hT⟩ := exists_subset_nhds_of_isCompact'
    (ModelLemmas.poly_antitone E).directed_ge (poly_compact E)
    (fun t => (poly_compact E t).isClosed)
    (U := Metric.thickening ε (⋂ s, Poly E s))
    (fun x hx => Metric.isOpen_thickening.mem_nhds
      (Metric.self_subset_thickening hε _ hx))
  refine ⟨T, fun t ht => ?_⟩
  obtain ⟨y, hy, hxy⟩ := Metric.mem_thickening_iff.mp
    (hT (ModelLemmas.poly_antitone E ht (ModelLemmas.output_mem_poly_self E t i)))
  exact (Metric.infDist_lt_iff (poly_limit_nonempty E)).mpr ⟨y, hy, hxy⟩

end AsymptoticSubspace.ModelLemmas
