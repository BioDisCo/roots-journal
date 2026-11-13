-- Internal plumbing module.
-- Reader-facing statement is in `LemHalfspaceZone.lean`.
import AsymptoticSubspace.ModelBridgeCore

noncomputable section

namespace AsymptoticSubspace
namespace ModelLemmas

open Set
open ComputationalModel
open PaperFormalization

section HalfspaceZone

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {n : Nat}

/-- Distance from a set to a target set, as the infimum of point-to-set distances. -/
def setDistTo (S T : Set V) : ℝ :=
  sInf ((fun x : V => Metric.infDist x T) '' S)

/--
TeX label: `lem:halfspace:zone` (model-grounded form).

Round-indexed form aligned with the update rule:
if `X(t) ∩ H = ∅` for an open half-space `H`, then
`dist(X(t+1), H) ≥ α * dist(P_{M(t+1)}(t), H)`.
-/
theorem lemma_halfspace_zone
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (α : ℝ) (t : Round)
    (q v : V)
    (hα_pos : 0 < α)
    (hv : v ≠ 0)
    (hmbw : MinimumBroadcastWeight (V := V) E M α)
    (hprev :
      Values E t ∩ {h : V | inner ℝ (h - q) v < 0} = ∅) :
    setDistTo (Values E (t + 1)) {h : V | inner ℝ (h - q) v < 0}
      ≥ α * setDistTo (PolyOn E t (M (t + 1))) {h : V | inner ℝ (h - q) v < 0} := by
  let H : Set V := {h : V | inner ℝ (h - q) v < 0}
  let K : Set V := {h : V | 0 ≤ inner ℝ (h - q) v}
  have hvnorm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hValues_sub_K : Values E t ⊆ K := by
    intro x hx
    have hx_not_H : x ∉ H := by
      intro hxH
      have hxcap : x ∈ Values E t ∩ H := ⟨hx, hxH⟩
      have : x ∈ (∅ : Set V) := by
        rw [← hprev]
        exact hxcap
      exact this.elim
    exact le_of_not_gt (by simpa [H] using hx_not_H)
  have hK_convex : Convex ℝ K := by
    intro x hx y hy a b ha hb hab
    change 0 ≤ inner ℝ ((a • x + b • y) - q) v
    have hsplit :
        (a • x + b • y) - q = a • (x - q) + b • (y - q) := by
      calc
        (a • x + b • y) - q = (a • x + b • y) - (a + b) • q := by simp [hab]
        _ = a • (x - q) + b • (y - q) := by
              simp [sub_eq_add_neg, smul_add, add_smul, add_assoc, add_left_comm, add_comm]
    have hcomb :
        0 ≤ a * inner ℝ (x - q) v + b * inner ℝ (y - q) v := by
      exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
    have hinner :
        inner ℝ ((a • x + b • y) - q) v
          = a * inner ℝ (x - q) v + b * inner ℝ (y - q) v := by
      rw [hsplit, inner_add_left, inner_smul_left, inner_smul_left]
      simp
    simpa [hinner] using hcomb
  have hValuesOn_sub_K : ValuesOn E t (M (t + 1)) ⊆ K := by
    intro x hx
    apply hValues_sub_K
    rcases hx with ⟨j, hj, rfl⟩
    exact ⟨j, rfl⟩
  have hPoly_sub_K : Poly E t ⊆ K := convexHull_min hValues_sub_K hK_convex
  have hPolyOn_sub_K : PolyOn E t (M (t + 1)) ⊆ K := convexHull_min hValuesOn_sub_K hK_convex
  have hpointwise :
      ∀ i : Proc n,
        α * setDistTo (PolyOn E t (M (t + 1))) H
          ≤ Metric.infDist (E.outputs (t + 1) i) H := by
    intro i
    let w : ℝ := ∑ j ∈ M (t + 1), E.weights (t + 1) i j
    let ξ := (M (t + 1)).centerMass (E.weights (t + 1) i) (E.outputs t)
    have hαw : α ≤ w := hmbw.2 (t + 1) i
    have hw : 0 < w := hα_pos.trans_le hαw
    have hξ : ξ ∈ PolyOn E t (M (t + 1)) := by
      exact Finset.centerMass_mem_convexHull (t := M (t + 1))
        (fun j _ => E.weight_nonneg (t + 1) i j) hw
        (fun j hj => ⟨j, hj, rfl⟩)
    have hξ_nonneg : 0 ≤ inner ℝ (ξ - q) v := hPolyOn_sub_K hξ
    have hwξ : w • ξ = ∑ j ∈ M (t + 1), E.weights (t + 1) i j • E.outputs t j := by
      change w • (w⁻¹ • _) = _
      rw [smul_smul, mul_inv_cancel₀ hw.ne', one_smul]
    -- Expand the update, discard nonnegative terms outside M, and use its total weight.
    have hsum : inner ℝ (E.outputs (t + 1) i - q) v =
        ∑ j : Proc n, E.weights (t + 1) i j * inner ℝ (E.outputs t j - q) v := by
      rw [E.output_succ_eq_weighted_sum, inner_sub_left, sum_inner]
      simp_rw [real_inner_smul_left, inner_sub_left, mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, E.weights_sum_one, one_mul]
    have hsumM : w * inner ℝ (ξ - q) v =
        ∑ j ∈ M (t + 1), E.weights (t + 1) i j * inner ℝ (E.outputs t j - q) v := by
      simp_rw [inner_sub_left, mul_sub]
      rw [← real_inner_smul_left, hwξ, sum_inner]
      simp_rw [real_inner_smul_left]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    have hinner_ge : α * inner ℝ (ξ - q) v ≤ inner ℝ (E.outputs (t + 1) i - q) v := by
      calc
        α * inner ℝ (ξ - q) v ≤ w * inner ℝ (ξ - q) v :=
          mul_le_mul_of_nonneg_right hαw hξ_nonneg
        _ = ∑ j ∈ M (t + 1), E.weights (t + 1) i j *
            inner ℝ (E.outputs t j - q) v := hsumM
        _ ≤ ∑ j : Proc n, E.weights (t + 1) i j *
            inner ℝ (E.outputs t j - q) v := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro j _ _
          exact mul_nonneg (E.weight_nonneg (t + 1) i j) (hValues_sub_K ⟨j, rfl⟩)
        _ = inner ℝ (E.outputs (t + 1) i - q) v := hsum.symm
    have hξ_notin : ξ ∉ H := by
      intro hξH
      have : inner ℝ (ξ - q) v < 0 := by simpa [H] using hξH
      exact (not_lt_of_ge hξ_nonneg) this
    have hout_notin : E.outputs (t + 1) i ∉ H := by
      intro houtH
      have hinner_nonneg : 0 ≤ inner ℝ (E.outputs (t + 1) i - q) v := by
        exact le_trans (mul_nonneg hα_pos.le hξ_nonneg) hinner_ge
      have : inner ℝ (E.outputs (t + 1) i - q) v < 0 := by simpa [H] using houtH
      exact (not_lt_of_ge hinner_nonneg) this
    have hdist_out :
        Metric.infDist (E.outputs (t + 1) i) H
          = inner ℝ (E.outputs (t + 1) i - q) v / ‖v‖ := by
      simpa [H] using
        (lemma_halfspace_distance_formula
          (q := q) (v := v) (z := E.outputs (t + 1) i) hv hout_notin)
    have hdist_ξ : Metric.infDist ξ H = inner ℝ (ξ - q) v / ‖v‖ := by
      simpa [H] using
        (lemma_halfspace_distance_formula (q := q) (v := v) (z := ξ) hv hξ_notin)
    have hsInf_le_ξ : setDistTo (PolyOn E t (M (t + 1))) H ≤ Metric.infDist ξ H := by
      refine csInf_le ?_ ?_
      · refine ⟨0, ?_⟩
        rintro y ⟨x, hx, rfl⟩
        exact Metric.infDist_nonneg
      · exact ⟨ξ, hξ, rfl⟩
    calc
      α * setDistTo (PolyOn E t (M (t + 1))) H
          ≤ α * Metric.infDist ξ H := by
            exact mul_le_mul_of_nonneg_left hsInf_le_ξ hα_pos.le
      _ = α * (inner ℝ (ξ - q) v / ‖v‖) := by rw [hdist_ξ]
      _ = (α * inner ℝ (ξ - q) v) / ‖v‖ := by ring
      _ ≤ inner ℝ (E.outputs (t + 1) i - q) v / ‖v‖ := by
            exact div_le_div_of_nonneg_right hinner_ge hvnorm_pos.le
      _ = Metric.infDist (E.outputs (t + 1) i) H := by rw [hdist_out]
  have hmain :
      α * setDistTo (PolyOn E t (M (t + 1))) H
        ≤ setDistTo (Values E (t + 1)) H := by
    by_cases hproc : Nonempty (Proc n)
    · refine le_csInf ?_ ?_
      · rcases hproc with ⟨i0⟩
        refine ⟨Metric.infDist (E.outputs (t + 1) i0) H, ?_⟩
        exact ⟨E.outputs (t + 1) i0, ⟨i0, rfl⟩, rfl⟩
      · intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        rcases hx with ⟨i, rfl⟩
        exact hpointwise i
    · letI : IsEmpty (Proc n) := not_nonempty_iff.mp hproc
      have hMempty : M (t + 1) = ∅ := by
        ext j
        exact False.elim (isEmptyElim j)
      have hValues_empty : Values E (t + 1) = ∅ := by
        ext x
        constructor
        · intro hx
          rcases hx with ⟨i, hi⟩
          exact False.elim (isEmptyElim i)
        · intro hx
          simp at hx
      have hPolyOn_empty : PolyOn E t (M (t + 1)) = ∅ := by
        simp [PolyOn, ValuesOn, hMempty]
      simp [setDistTo, hValues_empty, hPolyOn_empty, Real.sInf_empty]
  simpa [setDistTo, H] using hmain

end HalfspaceZone

end ModelLemmas
end AsymptoticSubspace
