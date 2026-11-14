module

public import AsymptoticSubspace.ComputationalModelCore

@[expose] public section

noncomputable section

namespace AsymptoticSubspace.ComputationalModel

variable {n : ℕ}

def influence (G : CommGraph n) (R : Finset (Proc n)) : Finset (Proc n) := by
  classical
  exact Finset.univ.filter (fun i => ∃ j ∈ R, G.edge j i)

@[simp] lemma mem_influence (G : CommGraph n) (R : Finset (Proc n)) (i : Proc n) :
    i ∈ influence G R ↔ ∃ j ∈ R, G.edge j i := by
  classical
  simp [influence]

lemma subset_influence (G : CommGraph n) (R : Finset (Proc n)) : R ⊆ influence G R :=
  fun i hi => (mem_influence G R i).mpr ⟨i, hi, G.self_loop i⟩

@[simp] lemma influence_id (R : Finset (Proc n)) : influence (CommGraph.id n) R = R := by
  classical
  ext i
  simp [CommGraph.id]

lemma influence_comp (G H : CommGraph n) (R : Finset (Proc n)) :
    influence (G.comp H) R = influence H (influence G R) := by
  classical
  ext i
  simp only [mem_influence, CommGraph.comp]
  aesop

lemma graphProduct_influence_mono (G : Round → CommGraph n) (start : Round)
    (R : Finset (Proc n)) : Monotone (fun t => influence (graphProduct G start t) R) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [graphProduct, influence_comp]
  exact subset_influence _ _

/-- Influence grows in a rooted round unless it already covers every process. -/
lemma root_influence_grows (G : CommGraph n) {R S : Finset (Proc n)}
    (hroot : IsRootSet G R) (hRS : R ⊆ S) (hS : S ≠ Finset.univ) :
    S.card < (influence G S).card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨subset_influence G S, ?_⟩
  intro heq
  apply hS
  apply Finset.eq_univ_of_forall
  intro i
  obtain ⟨j, hj, hji⟩ := hroot i
  have hclosed : ∀ a ∈ S, ∀ b, G.edge a b → b ∈ S := by
    intro a ha b hab
    rw [heq]
    exact (mem_influence G S b).mpr ⟨a, ha, hab⟩
  have hreach : ∀ {a b}, Reachable G a b → a ∈ S → b ∈ S := by
    intro a b hab
    induction hab with
    | refl => exact id
    | @tail b c hab hbc ih => exact fun ha => hclosed b (ih ha) c hbc
  exact hreach hji (hRS hj)

lemma exists_rootSet_card_eq (G : CommGraph n) {k : ℕ}
    (hk : k ≤ n) (hG : IsKRooted G k) :
    ∃ R : Finset (Proc n), R.card = k ∧ IsRootSet G R := by
  classical
  obtain ⟨R, hRk, hR⟩ := hG
  obtain ⟨S, hRS, _, hSk⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ R) hRk (by simpa using hk)
  exact ⟨S, hSk, fun i => by
    obtain ⟨j, hj, hji⟩ := hR i
    exact ⟨j, hRS hj, hji⟩⟩

/-- The pigeonhole argument in the elementary reduction of Section 2.
Choose a root set that occurs in at least `n` rounds. In the product of those
selected rounds, its influence strictly grows until it covers all processes.
Inserting the other rounds can only increase its influence. -/
theorem graphProduct_broadcastable_choose
    (G : Round → CommGraph n) (start k : ℕ) (hk : 0 < k) (hkn : k ≤ n)
    (hroot : ∀ t, IsKRooted (G t) k) :
    IsKBroadcastable (graphProduct G start (n * n.choose k)) k := by
  classical
  let C := {R : Finset (Proc n) // R.card = k}
  let L := n * n.choose k
  choose roots hcard hroots using fun t =>
    exists_rootSet_card_eq (G (start + t + 1)) hkn (hroot _)
  let f (t : ℕ) : C := ⟨roots t, hcard t⟩
  have hC : (Finset.univ : Finset C).Nonempty := ⟨f 0, Finset.mem_univ _⟩
  obtain ⟨R, _, hRfreq⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := Finset.range L) (t := Finset.univ) (f := f)
    (fun _ _ => Finset.mem_univ _) hC
    (show (Finset.univ : Finset C).card * n ≤ (Finset.range L).card by
      simp [C, L, Fintype.card_finset_len, Nat.mul_comm])
  -- Identity rounds pad the selected subsequence without changing its product.
  let H (t : ℕ) : CommGraph n :=
    if f (t - 1) = R then G (start + (t - 1) + 1) else CommGraph.id n
  let S (t : ℕ) := influence (graphProduct H 0 t) R.1
  have hsubset (t : ℕ) : S t ⊆ influence (graphProduct G start t) R.1 := by
    induction t with
    | zero => exact Finset.Subset.refl _
    | succ t ih =>
      intro i hi
      change i ∈ influence ((graphProduct H 0 t).comp (H (0 + t + 1))) R.1 at hi
      rw [influence_comp] at hi
      obtain ⟨j, hj, hji⟩ := (mem_influence _ _ _).mp hi
      have hj' := ih hj
      rw [graphProduct, influence_comp]
      apply (mem_influence _ _ _).mpr
      refine ⟨j, hj', ?_⟩
      by_cases ht : f t = R
      · simpa [H, ht] using hji
      · have : j = i := by simpa [H, ht, CommGraph.id] using hji
        subst i
        exact (G _).self_loop j
  have hfull : S L = Finset.univ := by
    by_contra hbad
    have hnot (t) (ht : t ≤ L) : S t ≠ Finset.univ := by
      intro h
      apply hbad
      exact Finset.eq_univ_of_forall fun i =>
        graphProduct_influence_mono H 0 R.1 ht (by change i ∈ S t; rw [h]; exact Finset.mem_univ i)
    have hgrowth : ∀ t, t ≤ L →
        k + ((Finset.range t).filter (fun j => f j = R)).card ≤ (S t).card := by
      intro t
      induction t with
      | zero => simpa [S, graphProduct] using R.2.ge
      | succ t ih =>
        intro ht
        have hprev := ih (by omega)
        have hmono := Finset.card_le_card (graphProduct_influence_mono H 0 R.1 (Nat.le_succ t))
        by_cases hsel : f t = R
        · have hrootR : IsRootSet (G (start + t + 1)) R.1 := by
            have heq : roots t = R.1 := congrArg Subtype.val hsel
            rw [← heq]
            exact hroots t
          have hstrict := root_influence_grows (G (start + t + 1)) hrootR
            (subset_influence (graphProduct H 0 t) R.1) (hnot t (by omega))
          have hstep : (S t).card < (S (t + 1)).card := by
            simpa [S, graphProduct, influence_comp, H, hsel] using hstrict
          simpa [Finset.range_add_one, Finset.filter_insert, hsel,
            Finset.mem_filter, Finset.mem_range] using (by omega :
              k + (((Finset.range t).filter (fun j => f j = R)).card + 1) ≤ (S (t + 1)).card)
        · simpa [Finset.range_add_one, Finset.filter_insert, hsel] using
            hprev.trans hmono
    have hg := hgrowth L le_rfl
    have hb : (S L).card ≤ n := by simpa using Finset.card_le_univ (S L)
    omega
  refine ⟨R.1, R.2.le, fun i => ?_⟩
  exact (mem_influence _ _ _).mp (hsubset L (by simp [hfull]))

/-- The polynomial bound stated in the paper's elementary reduction. -/
theorem graphProduct_broadcastable_polynomial
    (G : Round → CommGraph n) (start k : ℕ) (hk : 0 < k) (hkn : k ≤ n)
    (hroot : ∀ t, IsKRooted (G t) k) :
    IsKBroadcastable (graphProduct G start (n ^ (k + 1))) k := by
  obtain ⟨R, hRk, hR⟩ := graphProduct_broadcastable_choose G start k hk hkn hroot
  refine ⟨R, hRk, fun i => ?_⟩
  apply (mem_influence _ _ _).mp
  apply graphProduct_influence_mono G start R
    (show n * n.choose k ≤ n ^ (k + 1) from by
      calc
        n * n.choose k ≤ n * n ^ k := Nat.mul_le_mul_left n (Nat.choose_le_pow n k)
        _ = n ^ (k + 1) := by rw [pow_succ, Nat.mul_comm])
  exact (mem_influence _ _ _).mpr (hR i)

end AsymptoticSubspace.ComputationalModel
