module

public import AsymptoticSubspace.TemporalAncestors

@[expose] public section

noncomputable section

namespace AsymptoticSubspace.ComputationalModel

open Finset
variable {n : ℕ}

/-- The ancestor sets of distinct time-stamped processes are disjoint. -/
def StrictAt (G : Round → CommGraph n) (C : Finset (TimedProc n)) (t : ℕ) : Prop :=
  (C : Set (TimedProc n)).PairwiseDisjoint (fun a => ancestors G a t)

lemma StrictAt.mono {G : Round → CommGraph n} {C D : Finset (TimedProc n)} {t u : ℕ}
    (h : StrictAt G C t) (hDC : D ⊆ C) (htu : t ≤ u) : StrictAt G D u := by
  intro a ha b hb hab
  exact (h (hDC ha) (hDC hb) hab).mono
    (ancestors_antitone G a htu) (ancestors_antitone G b htu)

def ancestorMass (G : Round → CommGraph n) (C : Finset (TimedProc n)) (t : ℕ) : ℕ :=
  ∑ a ∈ C, (ancestors G a t).card

lemma ancestorMass_antitone (G : Round → CommGraph n) (C : Finset (TimedProc n)) :
    Antitone (ancestorMass G C) := by
  intro t u htu
  exact sum_le_sum fun a _ => card_le_card (ancestors_antitone G a htu)

lemma StrictAt.mass_le {G : Round → CommGraph n} {C : Finset (TimedProc n)} {t : ℕ}
    (h : StrictAt G C t) : ancestorMass G C t ≤ n := by
  classical
  rw [ancestorMass, ← card_biUnion h]
  exact (card_le_univ _).trans_eq (Fintype.card_fin n)

/-- At most `k` active disjoint ancestor sets can fail to grow backwards in a
`k`-rooted round: each stationary set contains a distinct root. -/
theorem strict_increments {G : Round → CommGraph n} {C : Finset (TimedProc n)} {t k : ℕ}
    (hstrict : StrictAt G C (t + 1)) (hroot : IsKRooted (G (t + 1)) k) :
    ancestorMass G C (t + 1) + (C.filter (fun a => t ≤ a.2)).card ≤
      ancestorMass G C t + k := by
  classical
  obtain ⟨R, hRk, hR⟩ := hroot
  let bad := C.filter (fun a => t ≤ a.2 ∧ ancestors G a t = ancestors G a (t + 1))
  have hbad (a : {a // a ∈ bad}) : ∃ r ∈ R, r ∈ ancestors G a.1 (t + 1) :=
    root_mem_of_ancestors_stationary hR (mem_filter.mp a.2).2.1 (mem_filter.mp a.2).2.2
  choose r hr hm using hbad
  have hcard : bad.card ≤ R.card := by
    apply card_le_card_of_injective (f := fun a => (⟨r a, hr a⟩ : {r // r ∈ R}))
    intro a b hab
    apply Subtype.ext
    by_contra hne
    have hd := hstrict (mem_filter.mp a.2).1 (mem_filter.mp b.2).1 hne
    apply disjoint_left.mp hd (hm a)
    have he : r a = r b := congrArg Subtype.val hab
    exact he ▸ hm b
  have hlocal (a : TimedProc n) (ha : a ∈ C) :
      (ancestors G a (t + 1)).card + (if t ≤ a.2 then 1 else 0) ≤
        (ancestors G a t).card + (if a ∈ bad then 1 else 0) := by
    have hsub := ancestors_antitone G a (Nat.le_succ t)
    by_cases ht : t ≤ a.2
    · by_cases he : ancestors G a t = ancestors G a (t + 1)
      · simp [bad, ha, ht, he]
      · have hlt : (ancestors G a (t + 1)).card < (ancestors G a t).card :=
          card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, Ne.symm he⟩)
        simp only [ht, ↓reduceIte]
        omega
    · simp only [ht, ↓reduceIte, Nat.add_zero]
      exact (card_le_card hsub).trans (Nat.le_add_right _ _)
  have hsum := sum_le_sum hlocal
  simp only [sum_add_distrib, sum_boole] at hsum
  have hb : C.filter (fun a => a ∈ bad) = bad := by
    ext a
    simp [bad]
  rw [hb] at hsum
  exact hsum.trans (Nat.add_le_add_left (hcard.trans hRk) _)

end AsymptoticSubspace.ComputationalModel
