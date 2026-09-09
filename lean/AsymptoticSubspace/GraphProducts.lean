import AsymptoticSubspace.ComputationalModelCore

noncomputable section

namespace AsymptoticSubspace.ComputationalModel

variable {n : ℕ}

/-- A communication graph whose edges represent one message-relaying block. -/
def CommGraph.comp (G H : CommGraph n) : CommGraph n where
  edge i j := ∃ m, G.edge i m ∧ H.edge m j
  self_loop i := ⟨i, G.self_loop i, H.self_loop i⟩

def CommGraph.id (n : ℕ) : CommGraph n where
  edge i j := i = j
  self_loop _ := rfl

/-- The product of rounds `start + 1` through `start + len`, in temporal order. -/
def graphProduct (G : Round → CommGraph n) (start : Round) : ℕ → CommGraph n
  | 0 => CommGraph.id n
  | len + 1 => (graphProduct G start len).comp (G (start + len + 1))

def IsKBroadcastable (G : CommGraph n) (k : ℕ) : Prop :=
  ∃ R : Finset (Proc n), R.card ≤ k ∧ IsBroadcastingSet G R

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

/-- The elementary graph reduction in Section 2, with the sharper intermediate
bound `n * choose n k`. A sum of influence-set sizes replaces the pigeonhole
subsequence argument. -/
theorem graphProduct_broadcastable_choose
    (G : Round → CommGraph n) (start k : ℕ) (hk : 0 < k) (hkn : k ≤ n)
    (hroot : ∀ t, IsKRooted (G t) k) :
    IsKBroadcastable (graphProduct G start (n * n.choose k)) k := by
  classical
  let C := {R : Finset (Proc n) // R.card = k}
  let L := n * n.choose k
  let potential (t : ℕ) := ∑ R : C, (influence (graphProduct G start t) R.1).card
  by_contra hbad
  have hnot (t : ℕ) (ht : t ≤ L) (R : C) :
      influence (graphProduct G start t) R.1 ≠ Finset.univ := by
    intro hfull
    apply hbad
    refine ⟨R.1, R.2.le, ?_⟩
    intro i
    apply (mem_influence _ _ _).mp
    apply graphProduct_influence_mono G start R.1 ht
    simp [hfull]
  have hinc (t : ℕ) (ht : t < L) : potential t < potential (t + 1) := by
    obtain ⟨R, hRk, hR⟩ := exists_rootSet_card_eq (G (start + t + 1)) hkn (hroot _)
    apply Finset.sum_lt_sum
    · intro S _
      exact Finset.card_le_card (graphProduct_influence_mono G start S.1 (Nat.le_succ t))
    · refine ⟨⟨R, hRk⟩, Finset.mem_univ _, ?_⟩
      change (influence (graphProduct G start t) R).card <
        (influence (graphProduct G start (t + 1)) R).card
      rw [graphProduct, influence_comp]
      exact root_influence_grows _ hR (subset_influence _ _) (hnot t ht.le ⟨R, hRk⟩)
  have hzero : 0 < potential 0 := by
    obtain ⟨R, hRk, _⟩ := exists_rootSet_card_eq (G 0) hkn (hroot 0)
    have hle := Finset.single_le_sum (s := (Finset.univ : Finset C))
      (f := fun S : C => (influence (graphProduct G start 0) S.1).card)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨R, hRk⟩ : C))
    have : k ≤ potential 0 := by simpa [potential, graphProduct, hRk] using hle
    omega
  have hge : ∀ t, t ≤ L → t < potential t := by
    intro t
    induction t with
    | zero => exact fun _ => hzero
    | succ t ih =>
      intro ht
      have hi := ih (Nat.le_trans (Nat.le_succ t) ht)
      have hs := hinc t (by omega)
      omega
  have hbound : potential L ≤ L := by
    calc
      potential L ≤ ∑ _R : C, n := Finset.sum_le_sum fun R _ => by
        simpa using (Finset.card_le_univ (influence (graphProduct G start L) R.1))
      _ = L := by simp [C, L, Fintype.card_finset_len, Nat.mul_comm]
  exact (hge L le_rfl).not_ge hbound

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
