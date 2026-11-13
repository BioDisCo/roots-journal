import AsymptoticSubspace.BlockExecution
import AsymptoticSubspace.ThmSolving

noncomputable section

namespace AsymptoticSubspace

open ComputationalModel ModelLemmas Set

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {n : ℕ} [NeZero n]

omit [FiniteDimensional ℝ V] in
/-- Convergence on block boundaries extends to every round because averaging
keeps all intermediate outputs in the preceding convex hull. -/
theorem convergesToSet_of_blocks
    (E : AveragingExecution (V := V) n) {L : ℕ} (hL : 0 < L)
    {W : Set V} (hW : Convex ℝ W)
    (hconv : ∀ i, ConvergesToSet (fun t => E.outputs (t * L) i) W) :
    ∀ i, ConvergesToSet (fun t => E.outputs t i) W := by
  classical
  intro i
  have hWne := (hconv i).1
  refine ⟨hWne, fun ε hε => ?_⟩
  choose T hT using fun j => (hconv j).2 ε hε
  let T0 := Finset.univ.sup T
  refine ⟨T0 * L, fun t ht => ?_⟩
  have hT0 : T0 ≤ t / L := (Nat.le_div_iff_mul_le hL).mpr ht
  have hvalues : Values E ((t / L) * L) ⊆ Metric.thickening ε W := by
    rintro x ⟨j, rfl⟩
    apply (Metric.mem_thickening_iff_infDist_lt hWne).mpr
    exact hT j (t / L) ((Finset.le_sup (Finset.mem_univ j)).trans hT0)
  have hpoly : Poly E ((t / L) * L) ⊆ Metric.thickening ε W :=
    convexHull_min hvalues (hW.thickening ε)
  apply (Metric.mem_thickening_iff_infDist_lt hWne).mp
  apply hpoly
  exact ModelLemmas.poly_antitone E (Nat.div_mul_le_self t L)
    (ModelLemmas.output_mem_poly_self E t i)

/-- An execution-level reduction for any proven finite broadcasting-block bound. -/
theorem theorem_solving_of_broadcastable_blocks
    (k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ Module.finrank ℝ V)
    (E : AveragingExecution (V := V) n) (α : ℝ) (hα : 0 < α) (hsafe : AlphaSafe E α)
    (L : ℕ) (hL : 0 < L)
    (hblocks : ∀ start, IsKBroadcastable (graphProduct E.graphs start L) k) :
    ∃ W : AffineSubspace ℝ V,
      Module.finrank ℝ W.direction ≤ k - 1 ∧
      (∀ i, ConvergesToSet (fun t => E.outputs t i) (W : Set V)) ∧
      (∀ i, ConvergesToSet (fun t => E.outputs t i) (Poly E 0)) := by
  classical
  choose M hcard hbroadcast using fun t => hblocks ((t - 1) * L)
  have hmbw : MinimumBroadcastWeight (blockExecution E L) M (α ^ L) :=
    alphaSafe_implies_minimumBroadcastWeight _ M _ (blockExecution_safe E hα.le hsafe L) hbroadcast
  obtain ⟨W, hdim, hconv, _⟩ := ThmSolving.theorem_solving (Module.finrank ℝ V) k hkd hk
    (blockExecution E L) M (α ^ L) (pow_pos hα _) hmbw hcard rfl
  refine ⟨W, hdim, ?_, ModelLemmas.averaging_validityAtLimit E⟩
  exact convergesToSet_of_blocks E hL W.convex hconv

/-- The rooted-adversary sufficiency result, for ordinary averaging at every round.
It uses the paper's elementary polynomial graph reduction. -/
theorem theorem_rooted
    (k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ Module.finrank ℝ V)
    (E : AveragingExecution (V := V) n) (α : ℝ) (hα : 0 < α) (hsafe : AlphaSafe E α)
    (hroot : ∀ t, IsKRooted (E.graphs t) k) :
    ∃ W : AffineSubspace ℝ V,
      Module.finrank ℝ W.direction ≤ k - 1 ∧
      (∀ i, ConvergesToSet (fun t => E.outputs t i) (W : Set V)) ∧
      (∀ i, ConvergesToSet (fun t => E.outputs t i) (Poly E 0)) := by
  classical
  by_cases hkn : k ≤ n
  · exact theorem_solving_of_broadcastable_blocks k hk hkd E α hα hsafe
      (n ^ (k + 1)) (pow_pos (Nat.pos_of_ne_zero (NeZero.ne n)) _)
      (fun start => graphProduct_broadcastable_polynomial E.graphs start k hk hkn hroot)
  · apply theorem_solving_of_broadcastable_blocks k hk hkd E α hα hsafe 1 (by decide)
    intro start
    refine ⟨Finset.univ, by simpa using (le_of_not_ge hkn), ?_⟩
    intro i
    exact ⟨i, Finset.mem_univ i, (graphProduct E.graphs start 1).self_loop i⟩

end AsymptoticSubspace
