module

public import AsymptoticSubspace.StrictCoverGrowth

@[expose] public section

noncomputable section

namespace AsymptoticSubspace.ComputationalModel

open Finset
variable {n : ℕ}

/-- Every final process is reached from one of the tagged processes. -/
def TimedCover (G : Round → CommGraph n) (T : ℕ) (C : Finset (TimedProc n)) : Prop :=
  ∀ p, ∃ a ∈ C, TemporalPath G a.2 T a.1 p

lemma TimedCover.broadcastable {G : Round → CommGraph n} {T k : ℕ} {C : Finset (TimedProc n)}
    (h : TimedCover G T C) (hc : C.card ≤ k) :
    IsKBroadcastable (graphProduct G 0 T) k := by
  classical
  refine ⟨C.image Prod.fst, (card_image_le).trans hc, ?_⟩
  intro p
  obtain ⟨a, ha, hp⟩ := h p
  refine ⟨a.1, mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩
  have ht := (TemporalPath.self G (Nat.zero_le a.2) a.1).trans hp
  simpa [TemporalPath] using ht.2

/-- A strict cover together with its earliest permitted time boundary. At time
zero the construction is allowed to discard redundant bookkeeping candidates;
positive-time states always retain an actual cover. -/
structure BackwardState (G : Round → CommGraph n) (T : ℕ) where
  nodes : Finset (TimedProc n)
  time : ℕ
  time_le : time ≤ T + 1
  timestamp_le : ∀ a ∈ nodes, a.2 ≤ T
  timestamp_ge : ∀ a ∈ nodes, time ≤ a.2 + 1
  strict : StrictAt G nodes time
  cover : 0 < time → TimedCover G T nodes

def initialBackwardState (G : Round → CommGraph n) (T : ℕ) : BackwardState G T where
  nodes := univ.image (fun p : Proc n => (p, T))
  time := T + 1
  time_le := le_rfl
  timestamp_le := by simp
  timestamp_ge := by simp
  strict := by
    intro a ha b hb hab
    change a ∈ univ.image (fun p : Proc n => (p, T)) at ha
    change b ∈ univ.image (fun p : Proc n => (p, T)) at hb
    obtain ⟨p, _, rfl⟩ := mem_image.mp ha
    obtain ⟨q, _, rfl⟩ := mem_image.mp hb
    change Disjoint (ancestors G (p, T) (T + 1)) (ancestors G (q, T) (T + 1))
    simp only [ancestors_after G (p, T) (Nat.lt_succ_self T)]
    simp
  cover := by
    intro _ p
    exact ⟨(p, T), mem_image.mpr ⟨p, mem_univ p, rfl⟩, TemporalPath.refl G T p⟩

/-- A single collision merges two tagged processes into a common ancestor. -/
lemma exists_merge_nodes {G : Round → CommGraph n} {T t : ℕ}
    (S : BackwardState G T) (ht : 0 < t) (htS : t ≤ S.time)
    (hstrict : StrictAt G S.nodes t) (hnot : ¬ StrictAt G S.nodes (t - 1)) :
    ∃ C : Finset (TimedProc n), C.card + 1 = S.nodes.card ∧
      (C \ S.nodes).card ≤ 1 ∧
      (∀ a ∈ C, a.2 ≤ T) ∧ (∀ a ∈ C, t ≤ a.2 + 1) ∧
      StrictAt G C t ∧ TimedCover G T C := by
  classical
  have hcollision : ∃ a ∈ S.nodes, ∃ b ∈ S.nodes,
      a ≠ b ∧ ∃ p, p ∈ ancestors G a (t - 1) ∧ p ∈ ancestors G b (t - 1) := by
    simpa only [StrictAt, Set.PairwiseDisjoint, Set.Pairwise, Function.onFun,
      disjoint_left, not_forall, exists_prop, not_not, Finset.mem_coe] using hnot
  obtain ⟨a, ha, b, hb, hab, p, hpa, hpb⟩ := hcollision
  let z : TimedProc n := (p, t - 1)
  have hzT : z.2 ≤ T := by have := S.time_le; dsimp [z]; omega
  have hztime : t ≤ z.2 + 1 := by dsimp [z]; omega
  have hza : TemporalPath G z.2 a.2 z.1 a.1 := (mem_ancestors _ _ _ _).mp hpa
  have hzb : TemporalPath G z.2 b.2 z.1 b.1 := (mem_ancestors _ _ _ _).mp hpb
  have hc := S.cover (lt_of_lt_of_le ht htS)
  have hzempty : ancestors G z t = ∅ := ancestors_after G z (by dsimp [z]; omega)
  by_cases hz : z ∈ S.nodes
  · obtain ⟨w, hw, hwz, hwpath⟩ : ∃ w ∈ S.nodes, w ≠ z ∧ TemporalPath G z.2 w.2 z.1 w.1 := by
      by_cases haz : a = z
      · exact ⟨b, hb, by aesop, hzb⟩
      · exact ⟨a, ha, haz, hza⟩
    refine ⟨S.nodes.erase w, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact card_erase_add_one hw
    · have he : S.nodes.erase w \ S.nodes = ∅ := sdiff_eq_empty_iff_subset.mpr (erase_subset _ _)
      simp [he]
    · exact fun q hq => S.timestamp_le q (mem_of_mem_erase hq)
    · exact fun q hq => htS.trans (S.timestamp_ge q (mem_of_mem_erase hq))
    · exact hstrict.mono (erase_subset _ _) le_rfl
    · intro q
      obtain ⟨v, hv, hvq⟩ := hc q
      by_cases hvw : v = w
      · subst v
        exact ⟨z, mem_erase.mpr ⟨hwz.symm, hz⟩, hwpath.trans hvq⟩
      · exact ⟨v, mem_erase.mpr ⟨hvw, hv⟩, hvq⟩
  · let D := (S.nodes.erase a).erase b
    have hzD : z ∉ D := fun h => hz (mem_of_mem_erase (mem_of_mem_erase h))
    refine ⟨insert z D, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [card_insert_of_notMem hzD]
      have hb' : b ∈ S.nodes.erase a := mem_erase.mpr ⟨hab.symm, hb⟩
      have he₁ := card_erase_add_one ha
      have he₂ := card_erase_add_one hb'
      dsimp [D]
      omega
    · apply (card_le_card (show insert z D \ S.nodes ⊆ {z} from ?_)).trans (by simp)
      intro q hq
      obtain ⟨hq, hqS⟩ := mem_sdiff.mp hq
      rcases mem_insert.mp hq with rfl | hq
      · simp
      · exact (hqS (mem_of_mem_erase (mem_of_mem_erase hq))).elim
    · intro q hq
      rcases mem_insert.mp hq with rfl | hq
      · exact hzT
      · exact S.timestamp_le q (mem_of_mem_erase (mem_of_mem_erase hq))
    · intro q hq
      rcases mem_insert.mp hq with rfl | hq
      · exact hztime
      · exact htS.trans (S.timestamp_ge q (mem_of_mem_erase (mem_of_mem_erase hq)))
    · intro q hq r hr hqr
      change Disjoint (ancestors G q t) (ancestors G r t)
      rcases mem_insert.mp hq with rfl | hq
      · rw [hzempty]; simp
      rcases mem_insert.mp hr with rfl | hr
      · rw [hzempty]; simp
      exact hstrict (mem_of_mem_erase (mem_of_mem_erase hq))
        (mem_of_mem_erase (mem_of_mem_erase hr)) hqr
    · intro q
      obtain ⟨v, hv, hvq⟩ := hc q
      by_cases hva : v = a
      · subst v
        exact ⟨z, mem_insert_self _ _, hza.trans hvq⟩
      by_cases hvb : v = b
      · subst v
        exact ⟨z, mem_insert_self _ _, hzb.trans hvq⟩
      exact ⟨v, mem_insert_of_mem (mem_erase.mpr ⟨hvb, mem_erase.mpr ⟨hva, hv⟩⟩), hvq⟩

lemma exists_backward_step {G : Round → CommGraph n} {T : ℕ}
    (S : BackwardState G T) (hne : S.nodes.Nonempty) :
    ∃ S' : BackwardState G T,
      S'.nodes.card + 1 = S.nodes.card ∧ S'.time ≤ S.time ∧
      (S'.nodes \ S.nodes).card ≤ 1 ∧ StrictAt G S.nodes S'.time := by
  classical
  let B := (range (S.time + 1)).filter (fun t => 0 < t ∧ ¬ StrictAt G S.nodes (t - 1))
  by_cases hB : B.Nonempty
  · let t := B.max' hB
    have htB : t ∈ B := max'_mem B hB
    obtain ⟨htr, ht, hnonstrict⟩ := mem_filter.mp htB
    have htS : t ≤ S.time := by have := mem_range.mp htr; omega
    have hstrict : StrictAt G S.nodes t := by
      by_cases he : t = S.time
      · simpa [he] using S.strict
      by_contra hnot
      have hmem : t + 1 ∈ B := mem_filter.mpr
        ⟨mem_range.mpr (by omega), by simpa using And.intro (Nat.zero_lt_succ t) hnot⟩
      have hle : t + 1 ≤ t := le_max' B (t + 1) hmem
      omega
    obtain ⟨C, hcard, hdiff, hle, hge, hstr, hcov⟩ :=
      exists_merge_nodes S ht htS hstrict hnonstrict
    refine ⟨⟨C, t, htS.trans S.time_le, hle, hge, hstr, fun _ => hcov⟩,
      hcard, htS, hdiff, hstrict⟩
  · have hstrict : StrictAt G S.nodes 0 := by
      by_cases ht : S.time = 0
      · simpa [ht] using S.strict
      by_contra hnot
      apply hB
      exact ⟨1, mem_filter.mpr ⟨mem_range.mpr (by omega), by simpa using hnot⟩⟩
    obtain ⟨a, ha⟩ := hne
    let C := S.nodes.erase a
    refine ⟨⟨C, 0, Nat.zero_le _,
      (fun q hq => S.timestamp_le q (mem_of_mem_erase hq)),
      (fun _ _ => Nat.zero_le _), hstrict.mono (erase_subset _ _) le_rfl,
      (fun h => by omega)⟩, card_erase_add_one ha, Nat.zero_le _, ?_, hstrict⟩
    have he : C \ S.nodes = ∅ := sdiff_eq_empty_iff_subset.mpr (erase_subset _ _)
    simp [he]

def backwardStep {G : Round → CommGraph n} {T : ℕ} (S : BackwardState G T) : BackwardState G T :=
  if h : S.nodes.Nonempty then (exists_backward_step S h).choose else S

lemma backwardStep_spec {G : Round → CommGraph n} {T : ℕ} (S : BackwardState G T)
    (h : S.nodes.Nonempty) :
    (backwardStep S).nodes.card + 1 = S.nodes.card ∧
      (backwardStep S).time ≤ S.time ∧
      ((backwardStep S).nodes \ S.nodes).card ≤ 1 ∧
      StrictAt G S.nodes (backwardStep S).time := by
  simpa only [backwardStep, dite_eq_left h] using (exists_backward_step S h).choose_spec

def backwardRun (G : Round → CommGraph n) (T : ℕ) : ℕ → BackwardState G T
  | 0 => initialBackwardState G T
  | j + 1 => backwardStep (backwardRun G T j)

lemma backwardRun_card (G : Round → CommGraph n) (T j : ℕ) (hj : j ≤ n) :
    (backwardRun G T j).nodes.card = n - j := by
  classical
  induction j with
  | zero =>
    simp only [backwardRun, initialBackwardState, Nat.sub_zero]
    rw [card_image_of_injective _ (fun _ _ h => Prod.mk.inj h |>.1)]
    exact card_fin n
  | succ j ih =>
    have he := ih (by omega)
    have hn : (backwardRun G T j).nodes.Nonempty := card_pos.mp (by omega)
    have hc := (backwardStep_spec _ hn).1
    rw [backwardRun]
    omega

/-- The family indexed by its cardinality rather than its number of merges. -/
def backwardFamily (G : Round → CommGraph n) (T s : ℕ) : BackwardState G T :=
  backwardRun G T (n - s)

lemma backwardFamily_card (G : Round → CommGraph n) (T s : ℕ) (hs : s ≤ n) :
    (backwardFamily G T s).nodes.card = s := by
  rw [backwardFamily, backwardRun_card G T (n - s) (by omega)]
  omega

lemma backwardFamily_step (G : Round → CommGraph n) (T s : ℕ) (hs : s < n) :
    (backwardFamily G T s).time ≤ (backwardFamily G T (s + 1)).time ∧
      ((backwardFamily G T s).nodes \ (backwardFamily G T (s + 1)).nodes).card ≤ 1 ∧
      StrictAt G (backwardFamily G T (s + 1)).nodes (backwardFamily G T s).time := by
  have hn : (backwardFamily G T (s + 1)).nodes.Nonempty := by
    apply card_pos.mp
    rw [backwardFamily_card G T (s + 1) (by omega)]
    omega
  have he : backwardFamily G T s = backwardStep (backwardFamily G T (s + 1)) := by
    unfold backwardFamily
    rw [show n - s = (n - (s + 1)) + 1 by omega, backwardRun]
  rw [he]
  exact (backwardStep_spec _ hn).2

lemma backwardFamily_time_mono (G : Round → CommGraph n) (T : ℕ) :
    Monotone (fun s => (backwardFamily G T s).time) := by
  apply monotone_nat_of_le_succ
  intro s
  by_cases hs : s < n
  · exact (backwardFamily_step G T s hs).1
  · simp [backwardFamily, Nat.sub_eq_zero_of_le (by omega : n ≤ s),
      Nat.sub_eq_zero_of_le (by omega : n ≤ s + 1)]

end AsymptoticSubspace.ComputationalModel
