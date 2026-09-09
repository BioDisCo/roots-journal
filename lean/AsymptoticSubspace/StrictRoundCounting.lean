import AsymptoticSubspace.BackwardCover
import AsymptoticSubspace.StrictRoundWeights

noncomputable section

namespace AsymptoticSubspace.ComputationalModel

open Finset
variable {n : ℕ}

lemma backwardFamily_difference (G : Round → CommGraph n) (T : ℕ) {s u : ℕ}
    (hsu : s ≤ u) (hun : u ≤ n) :
    ((backwardFamily G T s).nodes \ (backwardFamily G T u).nodes).card ≤ u - s := by
  classical
  induction u, hsu using Nat.le_induction with
  | base => simp
  | succ u hsu ih =>
    have hi := ih (by omega)
    have hstep := (backwardFamily_step G T u (by omega)).2.1
    have hsub : (backwardFamily G T s).nodes \ (backwardFamily G T (u + 1)).nodes ⊆
        ((backwardFamily G T s).nodes \ (backwardFamily G T u).nodes) ∪
        ((backwardFamily G T u).nodes \ (backwardFamily G T (u + 1)).nodes) := by
      intro a ha
      simp only [mem_sdiff, mem_union] at ha ⊢
      tauto
    have hc := (card_le_card hsub).trans (card_union_le _ _)
    omega

lemma backwardFamily_intersection (G : Round → CommGraph n) (T : ℕ) {s u : ℕ}
    (hsu : s ≤ u) (hun : u ≤ n) :
    2 * s ≤ ((backwardFamily G T s).nodes ∩ (backwardFamily G T u).nodes).card + u := by
  have hd := backwardFamily_difference G T hsu hun
  have he := card_sdiff_add_card_inter (backwardFamily G T s).nodes (backwardFamily G T u).nodes
  rw [backwardFamily_card G T s (hsu.trans hun)] at he
  omega

lemma backwardFamily_mass_step (G : Round → CommGraph n) (T k : ℕ)
    (hroot : ∀ t, IsKRooted (G t) k) {s u t : ℕ}
    (hs : 0 < s) (hsu : s ≤ u) (hun : u ≤ n)
    (htlo : (backwardFamily G T (s - 1)).time ≤ t)
    (hthi : t < (backwardFamily G T u).time) :
    ancestorMass G (backwardFamily G T s).nodes (t + 1) + (2 * s - k - u) ≤
      ancestorMass G (backwardFamily G T s).nodes t := by
  classical
  have hstr := (backwardFamily_step G T (s - 1) (by omega)).2.2
  rw [Nat.sub_add_cancel hs] at hstr
  have hstr' := hstr.mono (Subset.refl _) (show (backwardFamily G T (s - 1)).time ≤ t + 1 by omega)
  have hinc := strict_increments hstr' (hroot (t + 1))
  have hsub : (backwardFamily G T s).nodes ∩ (backwardFamily G T u).nodes ⊆
      (backwardFamily G T s).nodes.filter (fun a => t ≤ a.2) := by
    intro a ha
    obtain ⟨has, hau⟩ := mem_inter.mp ha
    have ht := (backwardFamily G T u).timestamp_ge a hau
    exact mem_filter.mpr ⟨has, by omega⟩
  have hcard := card_le_card hsub
  have hi := backwardFamily_intersection G T hsu hun
  have hmono : ancestorMass G (backwardFamily G T s).nodes (t + 1) ≤
      ancestorMass G (backwardFamily G T s).nodes t :=
    ancestorMass_antitone G (backwardFamily G T s).nodes (Nat.le_succ t)
  omega

lemma backwardFamily_mass_block (G : Round → CommGraph n) (T k : ℕ)
    (hroot : ∀ t, IsKRooted (G t) k) {s u : ℕ}
    (hs : 0 < s) (hsu : s ≤ u) (hun : u ≤ n) :
    ancestorMass G (backwardFamily G T s).nodes (backwardFamily G T u).time +
      (2 * s - k - u) * ((backwardFamily G T u).time - (backwardFamily G T (u - 1)).time) ≤
        ancestorMass G (backwardFamily G T s).nodes (backwardFamily G T (u - 1)).time := by
  let lo := (backwardFamily G T (u - 1)).time
  let hi := (backwardFamily G T u).time
  have hlohi : lo ≤ hi := backwardFamily_time_mono G T (by omega)
  have hbase : (backwardFamily G T (s - 1)).time ≤ lo := backwardFamily_time_mono G T (by omega)
  have haux : ∀ j, lo + j ≤ hi →
      ancestorMass G (backwardFamily G T s).nodes (lo + j) + (2 * s - k - u) * j ≤
        ancestorMass G (backwardFamily G T s).nodes lo := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      have hi' := ih (by omega)
      have hstep := backwardFamily_mass_step G T k hroot hs hsu hun
        (show (backwardFamily G T (s - 1)).time ≤ lo + j by omega)
        (show lo + j < (backwardFamily G T u).time by omega)
      simpa only [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Nat.add_le_add_right hstep ((2 * s - k - u) * j)).trans hi'
  simpa only [Nat.add_sub_cancel' hlohi] using haux (hi - lo) (by omega)

/-- Each row of the strict-rounds graph has total weighted duration at most `n`. -/
theorem backwardFamily_row_bound (G : Round → CommGraph n) (T k : ℕ)
    (hroot : ∀ t, IsKRooted (G t) k) {s : ℕ} (hs : 0 < s) (hsn : s ≤ n) :
    ∑ j ∈ range (n + 1 - s),
      (2 * s - k - (s + j)) *
        ((backwardFamily G T (s + j)).time - (backwardFamily G T (s + j - 1)).time) ≤ n := by
  have haux : ∀ L, s + L ≤ n + 1 →
      ancestorMass G (backwardFamily G T s).nodes (backwardFamily G T (s + L - 1)).time +
        (∑ j ∈ range L, (2 * s - k - (s + j)) *
          ((backwardFamily G T (s + j)).time - (backwardFamily G T (s + j - 1)).time)) ≤
      ancestorMass G (backwardFamily G T s).nodes (backwardFamily G T (s - 1)).time := by
    intro L
    induction L with
    | zero => simp
    | succ L ih =>
      intro hL
      have hi := ih (by omega)
      have hb := backwardFamily_mass_block G T k hroot hs
        (show s ≤ s + L by omega) (show s + L ≤ n by omega)
      rw [sum_range_succ]
      rw [show s + (L + 1) - 1 = s + L by omega]
      omega
  have h := haux (n + 1 - s) (by omega)
  have hstr := (backwardFamily_step G T (s - 1) (by omega)).2.2
  rw [Nat.sub_add_cancel hs] at hstr
  have hbound := hstr.mass_le
  omega

end AsymptoticSubspace.ComputationalModel
