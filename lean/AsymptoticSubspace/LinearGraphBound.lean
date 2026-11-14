module

public import AsymptoticSubspace.StrictRoundCounting

/-! The sharp linear rooted-to-broadcastable bound. The backward-cover and
strict-rounds argument follows El-Hayek, Henzinger, and Schmid, ITCS 2023,
Theorem 32 (CC-BY 4.0): https://doi.org/10.4230/LIPIcs.ITCS.2023.47.
We work directly with rooted directed graphs; no spanning-forest assumption
or unproved graph inequality is needed. -/

@[expose] public section

noncomputable section

namespace AsymptoticSubspace.ComputationalModel

open Finset
variable {n : ℕ}

def backwardDuration (G : Round → CommGraph n) (T k i : ℕ) : ℕ :=
  (backwardFamily G T (k + i + 1)).time - (backwardFamily G T (k + i)).time

lemma backwardDuration_sum (G : Round → CommGraph n) (T k : ℕ) (hk : k ≤ n) :
    (∑ i ∈ range (n - k), backwardDuration G T k i) + (backwardFamily G T k).time = T + 1 := by
  have haux (L : ℕ) : (∑ i ∈ range L, backwardDuration G T k i) +
      (backwardFamily G T k).time = (backwardFamily G T (k + L)).time := by
    induction L with
    | zero => simp
    | succ L ih =>
      rw [sum_range_succ]
      have hsub : backwardDuration G T k L + (backwardFamily G T (k + L)).time =
          (backwardFamily G T (k + L + 1)).time :=
        Nat.sub_add_cancel (backwardFamily_time_mono G T (Nat.le_succ (k + L)))
      rw [show k + (L + 1) = k + L + 1 by omega]
      omega
  have h := haux (n - k)
  simpa [Nat.add_sub_cancel' hk, backwardFamily, backwardRun, initialBackwardState] using h

lemma backwardDuration_row (G : Round → CommGraph n) (T k : ℕ)
    (hroot : ∀ t, IsKRooted (G t) k) {j : ℕ} (hj : j < n - k) :
    ∑ i ∈ range (n - k), (backwardDuration G T k i : ℝ) * strictEdgeWeight i j ≤ (n : ℝ) := by
  have h := backwardFamily_row_bound G T k hroot
    (show 0 < k + j + 1 by omega) (show k + j + 1 ≤ n by omega)
  have he : (∑ i ∈ range (n - k), (backwardDuration G T k i : ℝ) * strictEdgeWeight i j) =
      ((∑ l ∈ range (n + 1 - (k + j + 1)),
        (2 * (k + j + 1) - k - (k + j + 1 + l)) *
          ((backwardFamily G T (k + j + 1 + l)).time -
            (backwardFamily G T (k + j + 1 + l - 1)).time) : ℕ) : ℝ) := by
    rw [show n - k = j + (n - k - j) by omega, sum_range_add]
    have hz : ∑ i ∈ range j, (backwardDuration G T k i : ℝ) * strictEdgeWeight i j = 0 := by
      apply sum_eq_zero
      intro i hi
      simp [strictEdgeWeight, show ¬ j ≤ i by have := mem_range.mp hi; omega]
    rw [hz, zero_add]
    push_cast
    apply sum_congr (by congr 1; omega)
    intro l hl
    have hi₁ : k + (j + l) + 1 = k + j + 1 + l := by omega
    have hi₂ : k + (j + l) = k + j + 1 + l - 1 := by omega
    have hw : 2 * j + 1 - (j + l) = 2 * (k + j + 1) - k - (k + j + 1 + l) := by omega
    simp only [strictEdgeWeight, ite_eq_left (by omega : j ≤ j + l), backwardDuration]
    rw [hi₁, hi₂, hw]
    exact mul_comm _ _
  rw [he]
  exact_mod_cast h

/-- A linear number of rooted rounds always admits a broadcasting set of size
`k`. The proof supplies the cover; there is no external graph-bound premise. -/
theorem graphProduct_broadcastable_of_linear_bound
    (G : Round → CommGraph n) (T k : ℕ)
    (hroot : ∀ t, IsKRooted (G t) k)
    (hT : ((Real.pi ^ 2 + 6) / 6) * (n : ℝ) < (T : ℝ) + 1) :
    IsKBroadcastable (graphProduct G 0 T) k := by
  classical
  by_cases hk : k ≤ n
  · have hnum := strict_round_bound_of_rows (N := n - k)
      (δ := fun i => (backwardDuration G T k i : ℝ)) (by positivity : 0 ≤ (n : ℝ))
      (fun _ => by positivity) (fun j hj => backwardDuration_row G T k hroot hj)
    have hsum : (∑ i ∈ range (n - k), (backwardDuration G T k i : ℝ)) +
        ((backwardFamily G T k).time : ℝ) = (T : ℝ) + 1 := by
      exact_mod_cast backwardDuration_sum G T k hk
    have ht : 0 < (backwardFamily G T k).time := by
      by_contra h
      have he : (backwardFamily G T k).time = 0 := by omega
      rw [he, Nat.cast_zero, add_zero] at hsum
      linarith
    exact ((backwardFamily G T k).cover ht).broadcastable
      (backwardFamily_card G T k hk).le
  · refine ⟨univ, ?_, fun i => ⟨i, mem_univ i, (graphProduct G 0 T).self_loop i⟩⟩
    simp only [card_univ, Fintype.card_fin]
    omega

lemma graphProduct_shift (G : Round → CommGraph n) (start T : ℕ) :
    graphProduct (fun t => G (start + t)) 0 T = graphProduct G start T := by
  induction T with
  | zero => rfl
  | succ T ih => simp only [graphProduct, ih, Nat.zero_add, Nat.add_assoc]

theorem graphProduct_broadcastable_linear
    (G : Round → CommGraph n) (start T k : ℕ)
    (hroot : ∀ t, IsKRooted (G t) k)
    (hT : ((Real.pi ^ 2 + 6) / 6) * (n : ℝ) < (T : ℝ) + 1) :
    IsKBroadcastable (graphProduct G start T) k := by
  have h := graphProduct_broadcastable_of_linear_bound (fun t => G (start + t)) T k
    (fun t => hroot (start + t)) hT
  rwa [graphProduct_shift] at h

end AsymptoticSubspace.ComputationalModel

namespace AsymptoticSubspace

open ComputationalModel

/-- Integer block length corresponding to the cited ITCS 2023 Theorem 32. -/
def linearBroadcastRounds (n : ℕ) : ℕ :=
  ⌈((Real.pi ^ 2 + 6) / 6) * (n : ℝ) + 1⌉₊

lemma linearBroadcastRounds_pos (n : ℕ) : 0 < linearBroadcastRounds n := by
  apply Nat.ceil_pos.mpr
  positivity

/-- The exact cited graph theorem, proved by `sharpRootedBroadcastBound` below. -/
def SharpRootedBroadcastBound (n : ℕ) : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ G : Round → CommGraph n,
    (∀ t, IsKRooted (G t) k) → ∀ start,
      IsKBroadcastable (graphProduct G start (linearBroadcastRounds n)) k

/-- The cited ITCS 2023 Theorem 32, with every graph and counting dependency
discharged in Lean. The integer ceiling is explicit. -/
theorem sharpRootedBroadcastBound (n : ℕ) : SharpRootedBroadcastBound n := by
  intro k _ G hroot start
  apply graphProduct_broadcastable_linear G start _ k hroot
  have hceil := Nat.le_ceil (((Real.pi ^ 2 + 6) / 6) * (n : ℝ) + 1)
  change ((Real.pi ^ 2 + 6) / 6) * (n : ℝ) <
    (⌈((Real.pi ^ 2 + 6) / 6) * (n : ℝ) + 1⌉₊ : ℝ) + 1
  linarith

end AsymptoticSubspace
