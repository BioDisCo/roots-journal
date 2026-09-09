import AsymptoticSubspace.ComputationalModelCore

noncomputable section

namespace AsymptoticSubspace.ComputationalModel

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}

def inNeighborFinset (G : CommGraph n) (i : Proc n) : Finset (Proc n) := by
  classical
  exact Finset.univ.filter (fun j => G.edge j i)

@[simp] lemma mem_inNeighborFinset (G : CommGraph n) (i j : Proc n) :
    j ∈ inNeighborFinset G i ↔ G.edge j i := by
  classical
  simp [inNeighborFinset]

lemma inNeighborFinset_card_pos (G : CommGraph n) (i : Proc n) :
    0 < (inNeighborFinset G i).card :=
  Finset.card_pos.mpr ⟨i, (mem_inNeighborFinset G i i).mpr (G.self_loop i)⟩

def equalNeighborWeight (G : CommGraph n) (i j : Proc n) : ℝ := by
  classical
  exact if G.edge j i then ((inNeighborFinset G i).card : ℝ)⁻¹ else 0

lemma equalNeighborWeight_nonneg (G : CommGraph n) (i j : Proc n) :
    0 ≤ equalNeighborWeight G i j := by
  classical
  unfold equalNeighborWeight
  split <;> positivity

lemma equalNeighborWeight_sum (G : CommGraph n) (i : Proc n) :
    (∑ j, equalNeighborWeight G i j) = 1 := by
  classical
  have hcard : ((inNeighborFinset G i).card : ℝ) ≠ 0 := by
    exact_mod_cast (inNeighborFinset_card_pos G i).ne'
  simp only [equalNeighborWeight, ← Finset.sum_filter]
  change (∑ _j ∈ inNeighborFinset G i, ((inNeighborFinset G i).card : ℝ)⁻¹) = 1
  simp [hcard]

/-- The equal-neighbor algorithm from Section 4, as a local deterministic algorithm. -/
def equalNeighborAlgorithm (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) : DeterministicAlgorithm V n where
  step _ G x i := ∑ j, equalNeighborWeight G i j • x j
  locality _ G H x y i hgraph h := by
    classical
    have hneighbors : inNeighborFinset G i = inNeighborFinset H i := by
      ext j
      simpa only [mem_inNeighborFinset] using hgraph j
    have hweight : ∀ j, equalNeighborWeight G i j = equalNeighborWeight H i j := by
      intro j
      simp only [equalNeighborWeight, hneighbors, hgraph j]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : G.edge j i
    · rw [hweight j, h j hj]
    · have hjH : ¬ H.edge j i := fun hH => hj ((hgraph j).mpr hH)
      simp [equalNeighborWeight, hj, hjH]

def equalNeighborExecution (G : Round → CommGraph n) (init : Proc n → V) :
    AveragingExecution (V := V) n where
  graphs := G
  weights t := equalNeighborWeight (G t)
  outputs := (equalNeighborAlgorithm V n).run G init
  weights_nonneg t := equalNeighborWeight_nonneg (G t)
  weights_support t i j h := by simp [equalNeighborWeight, h]
  weights_row_sum t := equalNeighborWeight_sum (G t)
  update_rule _ _ := rfl

/-- The equal-neighbor algorithm has the uniform safety bound `1/n`. -/
theorem equalNeighbor_safe [NeZero n] (G : Round → CommGraph n) (init : Proc n → V) :
    AlphaSafe (equalNeighborExecution G init) (1 / (n : ℝ)) := by
  classical
  intro t i j h
  change (G t).edge j i at h
  change 1 / (n : ℝ) ≤ equalNeighborWeight (G t) i j
  rw [equalNeighborWeight, if_pos h, ← one_div]
  apply one_div_le_one_div_of_le
  · exact_mod_cast inNeighborFinset_card_pos (G t) i
  · exact_mod_cast (show (inNeighborFinset (G t) i).card ≤ n from by
      simpa using Finset.card_le_univ (inNeighborFinset (G t) i))

end AsymptoticSubspace.ComputationalModel
