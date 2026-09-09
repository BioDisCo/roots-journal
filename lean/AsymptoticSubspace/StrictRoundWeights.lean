import Mathlib

noncomputable section

namespace AsymptoticSubspace.ComputationalModel

open Finset

/-- Weighted out-degree in the strict-rounds graph, indexed by `s - k - 1`. -/
def strictRoundWeight (j : ℕ) : ℝ :=
  (((j + 2) / 2 : ℕ) : ℝ) * (((j + 3) / 2 : ℕ) : ℝ)

lemma strictRoundWeight_pos (j : ℕ) : 0 < strictRoundWeight j := by
  apply mul_pos <;> exact_mod_cast (show 0 < (_ + 2 : ℕ) / 2 by omega)

lemma strictRoundWeight_mono : Monotone strictRoundWeight := by
  intro i j hij
  apply mul_le_mul
  · exact_mod_cast (show (i + 2) / 2 ≤ (j + 2) / 2 by omega)
  · exact_mod_cast (show (i + 3) / 2 ≤ (j + 3) / 2 by omega)
  · positivity
  · positivity

lemma strictRoundWeight_even (j : ℕ) : strictRoundWeight (2 * j) = ((j : ℝ) + 1) ^ 2 := by
  have h₁ : (2 * j + 2) / 2 = j + 1 := by omega
  have h₂ : (2 * j + 3) / 2 = j + 1 := by omega
  simp [strictRoundWeight, h₁, h₂, pow_two]

lemma strictRoundWeight_odd (j : ℕ) :
    strictRoundWeight (2 * j + 1) = ((j : ℝ) + 1) * ((j : ℝ) + 2) := by
  have h₁ : (2 * j + 1 + 2) / 2 = j + 1 := by omega
  have h₂ : (2 * j + 1 + 3) / 2 = j + 2 := by omega
  simp [strictRoundWeight, h₁, h₂]

/-- Abel's finite summation inequality, proved directly for prefix bounds. -/
lemma sum_mul_le_of_prefix_le {f g w : ℕ → ℝ} (hw : Antitone w)
    (hw0 : ∀ i, 0 ≤ w i) (N : ℕ)
    (hp : ∀ j ≤ N, ∑ i ∈ range j, f i ≤ ∑ i ∈ range j, g i) :
    ∑ i ∈ range N, f i * w i ≤ ∑ i ∈ range N, g i * w i := by
  have haux : ∀ j ≤ N,
      ∑ i ∈ range j, (f i - g i) * w i ≤
        (∑ i ∈ range j, (f i - g i)) * w j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      have hjN : j ≤ N := by omega
      have hi := ih hjN
      have hs : ∑ i ∈ range (j + 1), (f i - g i) ≤ 0 := by
        rw [sum_sub_distrib]
        linarith [hp (j + 1) hj]
      have hm := mul_le_mul_of_nonpos_left (hw (Nat.le_succ j)) hs
      simp only [sum_range_succ, Nat.succ_eq_add_one] at hm ⊢
      nlinarith
  have h := haux N le_rfl
  have hs : ∑ i ∈ range N, (f i - g i) ≤ 0 := by
    rw [sum_sub_distrib]
    linarith [hp N le_rfl]
  have hm := mul_nonpos_of_nonpos_of_nonneg hs (hw0 N)
  simp only [sub_mul, sum_sub_distrib] at h hm
  linarith

lemma strictRoundWeight_prefix_bound (N : ℕ) :
    ∑ j ∈ range N, (strictRoundWeight j)⁻¹ ≤ Real.pi ^ 2 / 6 + 1 := by
  have heven (L : ℕ) :
      ∑ j ∈ range L, (strictRoundWeight (2 * j))⁻¹ ≤ Real.pi ^ 2 / 6 := by
    have h := sum_le_hasSum (range (L + 1)) (fun _ _ => by positivity) hasSum_zeta_two
    have he : ∑ j ∈ range L, (strictRoundWeight (2 * j))⁻¹ =
        ∑ j ∈ range (L + 1), (1 : ℝ) / (j : ℝ) ^ 2 := by
      rw [sum_range_succ']
      simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        div_zero, add_zero]
      apply sum_congr rfl
      intro j _
      simp [strictRoundWeight_even, one_div]
    rw [he]
    exact h
  have hodd (L : ℕ) :
      ∑ j ∈ range L, (strictRoundWeight (2 * j + 1))⁻¹ = 1 - ((L : ℝ) + 1)⁻¹ := by
    induction L with
    | zero => norm_num
    | succ L ih =>
      rw [sum_range_succ, ih, strictRoundWeight_odd]
      push_cast
      field_simp
      ring
  have hsplit : ∑ j ∈ range (2 * N), (strictRoundWeight j)⁻¹ =
      (∑ j ∈ range N, (strictRoundWeight (2 * j))⁻¹) +
        ∑ j ∈ range N, (strictRoundWeight (2 * j + 1))⁻¹ := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [show 2 * (N + 1) = 2 * N + 1 + 1 by omega, sum_range_succ, sum_range_succ, ih,
        sum_range_succ, sum_range_succ]
      ring
  calc
    ∑ j ∈ range N, (strictRoundWeight j)⁻¹ ≤
        ∑ j ∈ range (2 * N), (strictRoundWeight j)⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
      intro i _ _
      exact (inv_pos.mpr (strictRoundWeight_pos i)).le
    _ ≤ Real.pi ^ 2 / 6 + 1 := by
      rw [hsplit, hodd]
      have := heven N
      have : 0 ≤ ((N : ℝ) + 1)⁻¹ := by positivity
      linarith

/-- The numerical strict-round bound (ITCS 2023, Lemma 30). -/
theorem strict_round_numeric_bound {N : ℕ} {δ : ℕ → ℝ} {n : ℝ} (hn : 0 ≤ n)
    (hp : ∀ j ≤ N, ∑ i ∈ range j, δ i * strictRoundWeight i ≤ (j : ℝ) * n) :
    ∑ i ∈ range N, δ i ≤ ((Real.pi ^ 2 + 6) / 6) * n := by
  have hw : Antitone (fun i => (strictRoundWeight i)⁻¹) := by
    intro i j hij
    exact inv_anti₀ (strictRoundWeight_pos i) (strictRoundWeight_mono hij)
  have h := sum_mul_le_of_prefix_le (f := fun i => δ i * strictRoundWeight i)
    (g := fun _ => n) hw (fun i => (inv_pos.mpr (strictRoundWeight_pos i)).le) N
    (fun j hj => by simpa using hp j hj)
  simp only [mul_assoc, mul_inv_cancel₀ (strictRoundWeight_pos _).ne', mul_one,
    ← mul_sum] at h
  have hbound := mul_le_mul_of_nonneg_left (strictRoundWeight_prefix_bound N) hn
  nlinarith

/-- Edge weights with zero-based vertex labels. -/
def strictEdgeWeight (i j : ℕ) : ℝ := if j ≤ i then (2 * j + 1 - i : ℕ) else 0

lemma strictEdgeWeight_nonneg (i j : ℕ) : 0 ≤ strictEdgeWeight i j := by
  unfold strictEdgeWeight
  split <;> positivity

lemma strictRoundWeight_eq_sum (i : ℕ) :
    strictRoundWeight i = ∑ j ∈ range (i + 1), strictEdgeWeight i j := by
  have hoddSum (L : ℕ) : (∑ j ∈ range L, ((2 * j + 1 : ℕ) : ℝ)) = (L : ℝ) ^ 2 := by
    induction L with
    | zero => simp
    | succ L ih => rw [sum_range_succ, ih]; push_cast; ring
  have hevenSum (L : ℕ) : (∑ j ∈ range L, ((2 * j + 2 : ℕ) : ℝ)) =
      (L : ℝ) * ((L : ℝ) + 1) := by
    induction L with
    | zero => simp
    | succ L ih => rw [sum_range_succ, ih]; push_cast; ring
  have he (i j : ℕ) (h : j < i + 1) : strictEdgeWeight i j = (2 * j + 1 - i : ℕ) := by
    simp only [strictEdgeWeight, if_pos (by omega : j ≤ i)]
  have heq : (∑ j ∈ range (i + 1), strictEdgeWeight i j) =
      ∑ j ∈ range (i + 1), ((2 * j + 1 - i : ℕ) : ℝ) :=
    sum_congr rfl (fun j hj => he i j (mem_range.mp hj))
  rw [heq]
  obtain ⟨L, rfl | rfl⟩ : ∃ L, i = 2 * L ∨ i = 2 * L + 1 :=
    ⟨i / 2, by omega⟩
  · rw [strictRoundWeight_even, show 2 * L + 1 = L + (L + 1) by omega, sum_range_add]
    have hz : (∑ j ∈ range L, ((2 * j + 1 - 2 * L : ℕ) : ℝ)) = 0 := by
      apply sum_eq_zero
      intro j hj
      have : 2 * j + 1 - 2 * L = 0 := by have := mem_range.mp hj; omega
      simp [this]
    rw [hz, zero_add]
    have hr : (∑ j ∈ range (L + 1), ((2 * (L + j) + 1 - 2 * L : ℕ) : ℝ)) =
        ∑ j ∈ range (L + 1), ((2 * j + 1 : ℕ) : ℝ) := by
      apply sum_congr rfl
      intro j _
      congr 1
      omega
    rw [hr, hoddSum]
    norm_cast
  · rw [strictRoundWeight_odd, show 2 * L + 1 + 1 = (L + 1) + (L + 1) by omega, sum_range_add]
    have hz : (∑ j ∈ range (L + 1), ((2 * j + 1 - (2 * L + 1) : ℕ) : ℝ)) = 0 := by
      apply sum_eq_zero
      intro j hj
      have : 2 * j + 1 - (2 * L + 1) = 0 := by have := mem_range.mp hj; omega
      simp [this]
    rw [hz, zero_add]
    have hr : (∑ j ∈ range (L + 1), ((2 * (L + 1 + j) + 1 - (2 * L + 1) : ℕ) : ℝ)) =
        ∑ j ∈ range (L + 1), ((2 * j + 2 : ℕ) : ℝ) := by
      apply sum_congr rfl
      intro j _
      congr 1
      omega
    rw [hr, hevenSum]
    push_cast
    ring

lemma strictRoundWeight_eq_sum_of_lt {i N : ℕ} (hi : i < N) :
    strictRoundWeight i = ∑ j ∈ range N, strictEdgeWeight i j := by
  rw [strictRoundWeight_eq_sum]
  apply sum_subset (range_mono (by omega))
  intro j hj hj'
  simp only [mem_range, not_lt] at hj hj'
  simp [strictEdgeWeight, show ¬ j ≤ i by omega]

/-- Summing incoming weights bounds outgoing prefix weights; finite Abel
summation and the reciprocal-weight series give the sharp constant. -/
theorem strict_round_bound_of_rows {N : ℕ} {δ : ℕ → ℝ} {n : ℝ} (hn : 0 ≤ n)
    (hδ : ∀ i, 0 ≤ δ i)
    (hrow : ∀ j < N, ∑ i ∈ range N, δ i * strictEdgeWeight i j ≤ n) :
    ∑ i ∈ range N, δ i ≤ ((Real.pi ^ 2 + 6) / 6) * n := by
  apply strict_round_numeric_bound hn
  intro j hj
  calc
    ∑ i ∈ range j, δ i * strictRoundWeight i =
        ∑ i ∈ range j, ∑ v ∈ range j, δ i * strictEdgeWeight i v := by
      apply sum_congr rfl
      intro i hi
      rw [strictRoundWeight_eq_sum_of_lt (mem_range.mp hi), mul_sum]
    _ = ∑ v ∈ range j, ∑ i ∈ range j, δ i * strictEdgeWeight i v := sum_comm
    _ ≤ ∑ v ∈ range j, ∑ i ∈ range N, δ i * strictEdgeWeight i v := by
      apply sum_le_sum
      intro v _
      apply sum_le_sum_of_subset_of_nonneg (range_mono hj)
      intro i _ _
      exact mul_nonneg (hδ i) (strictEdgeWeight_nonneg i v)
    _ ≤ ∑ _v ∈ range j, n := sum_le_sum fun v hv => hrow v ((mem_range.mp hv).trans_le hj)
    _ = (j : ℝ) * n := by simp

end AsymptoticSubspace.ComputationalModel
