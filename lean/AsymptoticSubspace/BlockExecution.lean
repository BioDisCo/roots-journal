import AsymptoticSubspace.GraphProducts

noncomputable section

namespace AsymptoticSubspace.ComputationalModel

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}

/-- Coefficients of the averaging update over a consecutive block of rounds. -/
def blockWeights (E : AveragingExecution (V := V) n) (start : ℕ) :
    ℕ → Proc n → Proc n → ℝ
  | 0, i, j => if i = j then 1 else 0
  | len + 1, i, j => ∑ m, E.weights (start + len + 1) i m * blockWeights E start len m j

lemma blockWeights_nonneg (E : AveragingExecution (V := V) n) (start len : ℕ) :
    ∀ i j, 0 ≤ blockWeights E start len i j := by
  induction len with
  | zero => intro i j; dsimp [blockWeights]; split <;> norm_num
  | succ len ih =>
    intro i j
    exact Finset.sum_nonneg fun m _ => mul_nonneg (E.weights_nonneg _ _ _) (ih m j)

lemma blockWeights_row_sum (E : AveragingExecution (V := V) n) (start len : ℕ) :
    ∀ i, (∑ j, blockWeights E start len i j) = 1 := by
  induction len with
  | zero => intro i; simp [blockWeights]
  | succ len ih =>
    intro i
    simp only [blockWeights]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, ih, mul_one]
    exact E.weights_row_sum _ i

lemma blockWeights_support (E : AveragingExecution (V := V) n) (start len : ℕ) :
    ∀ i j, ¬(graphProduct E.graphs start len).edge j i → blockWeights E start len i j = 0 := by
  induction len with
  | zero => intro i j h; simp_all [blockWeights, graphProduct, CommGraph.id, eq_comm]
  | succ len ih =>
    intro i j h
    apply Finset.sum_eq_zero
    intro m _
    by_cases hprev : (graphProduct E.graphs start len).edge j m
    · have hlast : ¬(E.graphs (start + len + 1)).edge m i :=
        fun hm => h ⟨m, hprev, hm⟩
      rw [E.weights_support _ i m hlast, zero_mul]
    · rw [ih m j hprev, mul_zero]

lemma blockWeights_safe (E : AveragingExecution (V := V) n) {α : ℝ}
    (hα : 0 ≤ α) (hsafe : AlphaSafe E α) (start len : ℕ) :
    ∀ i j, (graphProduct E.graphs start len).edge j i →
      α ^ len ≤ blockWeights E start len i j := by
  induction len with
  | zero => intro i j h; simp_all [graphProduct, CommGraph.id, blockWeights]
  | succ len ih =>
    intro i j h
    obtain ⟨m, hprev, hlast⟩ := h
    calc
      α ^ (len + 1) = α * α ^ len := by rw [pow_succ, mul_comm]
      _ ≤ E.weights (start + len + 1) i m * blockWeights E start len m j :=
        mul_le_mul (hsafe _ i m hlast) (ih m j hprev) (pow_nonneg hα _)
          (E.weights_nonneg _ i m)
      _ ≤ blockWeights E start (len + 1) i j :=
        Finset.single_le_sum (fun m _ => mul_nonneg (E.weights_nonneg (start + len + 1) i m)
          (blockWeights_nonneg E start len m j)) (Finset.mem_univ m)

lemma block_update (E : AveragingExecution (V := V) n) (start len : ℕ) :
    ∀ i, E.outputs (start + len) i = ∑ j, blockWeights E start len i j • E.outputs start j := by
  induction len with
  | zero => intro i; simp [blockWeights]
  | succ len ih =>
    intro i
    rw [show start + (len + 1) = (start + len) + 1 by omega, E.update_rule]
    simp_rw [ih, Finset.smul_sum, ← mul_smul]
    rw [Finset.sum_comm]
    simp only [blockWeights, Finset.sum_smul]

/-- Sampling an averaging execution every `len` rounds is itself an averaging execution. -/
def blockExecution (E : AveragingExecution (V := V) n) (len : ℕ) :
    AveragingExecution (V := V) n where
  graphs t := graphProduct E.graphs ((t - 1) * len) len
  weights t := blockWeights E ((t - 1) * len) len
  outputs t := E.outputs (t * len)
  weights_nonneg t := blockWeights_nonneg E ((t - 1) * len) len
  weights_support t := blockWeights_support E ((t - 1) * len) len
  weights_row_sum t := blockWeights_row_sum E ((t - 1) * len) len
  update_rule t i := by
    simpa [Nat.add_mul] using block_update E (t * len) len i

theorem blockExecution_safe (E : AveragingExecution (V := V) n) {α : ℝ}
    (hα : 0 ≤ α) (hsafe : AlphaSafe E α) (len : ℕ) :
    AlphaSafe (blockExecution E len) (α ^ len) := by
  intro t i j h
  exact blockWeights_safe E hα hsafe ((t - 1) * len) len i j h

end AsymptoticSubspace.ComputationalModel
