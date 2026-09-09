import AsymptoticSubspace.GraphProducts

noncomputable section

namespace AsymptoticSubspace.ComputationalModel

variable {n : ℕ}

@[ext] lemma CommGraph.ext {G H : CommGraph n} (h : ∀ i j, G.edge i j ↔ H.edge i j) : G = H := by
  cases G
  cases H
  congr
  funext i j
  exact propext (h i j)

lemma CommGraph.comp_assoc (G H K : CommGraph n) : (G.comp H).comp K = G.comp (H.comp K) := by
  ext i j
  simp only [CommGraph.comp]
  aesop

@[simp] lemma CommGraph.comp_id (G : CommGraph n) : G.comp (CommGraph.id n) = G := by
  ext i j
  simp [CommGraph.comp, CommGraph.id]

@[simp] lemma CommGraph.id_comp (G : CommGraph n) : (CommGraph.id n).comp G = G := by
  ext i j
  simp [CommGraph.comp, CommGraph.id]

lemma graphProduct_succ_left (G : Round → CommGraph n) (start len : ℕ) :
    graphProduct G start (len + 1) =
      (G (start + 1)).comp (graphProduct G (start + 1) len) := by
  induction len with
  | zero => simp [graphProduct]
  | succ len ih =>
    rw [graphProduct, ih, CommGraph.comp_assoc, graphProduct]
    simp only [Nat.add_left_comm, Nat.add_comm]

lemma graphProduct_add (G : Round → CommGraph n) (start a b : ℕ) :
    graphProduct G start (a + b) =
      (graphProduct G start a).comp (graphProduct G (start + a) b) := by
  induction b with
  | zero => simp [graphProduct]
  | succ b ih =>
    rw [Nat.add_succ, graphProduct, ih, CommGraph.comp_assoc, graphProduct]
    simp only [Nat.add_assoc]

/-- A temporal path, with time measured at round boundaries. -/
def TemporalPath (G : Round → CommGraph n) (t u : ℕ) (i j : Proc n) : Prop :=
  t ≤ u ∧ (graphProduct G t (u - t)).edge i j

lemma TemporalPath.refl (G : Round → CommGraph n) (t : ℕ) (i : Proc n) :
    TemporalPath G t t i i := by simp [TemporalPath, graphProduct, CommGraph.id]

lemma TemporalPath.self (G : Round → CommGraph n) {t u : ℕ} (h : t ≤ u) (i : Proc n) :
    TemporalPath G t u i i := ⟨h, (graphProduct G t (u - t)).self_loop i⟩

lemma TemporalPath.trans {G : Round → CommGraph n} {t u v : ℕ} {i j k : Proc n}
    (h : TemporalPath G t u i j) (h' : TemporalPath G u v j k) : TemporalPath G t v i k := by
  refine ⟨h.1.trans h'.1, ?_⟩
  have htu := h.1
  have huv := h'.1
  rw [show v - t = (u - t) + (v - u) by omega, graphProduct_add,
    Nat.add_sub_cancel' h.1]
  exact ⟨j, h.2, h'.2⟩

/-- Time-stamped processes used in the backward cover construction. -/
abbrev TimedProc (n : ℕ) := Proc n × ℕ

/-- Ancestors of a time-stamped process. They are empty after its timestamp. -/
def ancestors (G : Round → CommGraph n) (a : TimedProc n) (t : ℕ) : Finset (Proc n) := by
  classical
  exact Finset.univ.filter (fun p => TemporalPath G t a.2 p a.1)

@[simp] lemma mem_ancestors (G : Round → CommGraph n) (a : TimedProc n) (t : ℕ) (p : Proc n) :
    p ∈ ancestors G a t ↔ TemporalPath G t a.2 p a.1 := by
  classical
  simp [ancestors]

@[simp] lemma ancestors_at (G : Round → CommGraph n) (a : TimedProc n) :
    ancestors G a a.2 = {a.1} := by
  classical
  ext p
  simp [TemporalPath, graphProduct, CommGraph.id]

lemma ancestors_after (G : Round → CommGraph n) (a : TimedProc n) {t : ℕ} (h : a.2 < t) :
    ancestors G a t = ∅ := by
  classical
  ext p
  simp [TemporalPath, Nat.not_le.mpr h]

lemma ancestors_antitone (G : Round → CommGraph n) (a : TimedProc n) :
    Antitone (ancestors G a) := by
  intro t u htu p hp
  exact (mem_ancestors _ _ _ _).mpr ((TemporalPath.self G htu p).trans
    ((mem_ancestors _ _ _ _).mp hp))

/-- One backwards propagation round. -/
lemma ancestors_step {G : Round → CommGraph n} {a : TimedProc n} {t : ℕ} (ht : t < a.2)
    (p : Proc n) :
    p ∈ ancestors G a t ↔ ∃ q ∈ ancestors G a (t + 1), (G (t + 1)).edge p q := by
  simp only [mem_ancestors, TemporalPath]
  rw [show a.2 - t = (a.2 - (t + 1)) + 1 by omega, graphProduct_succ_left]
  simp only [CommGraph.comp]
  constructor
  · rintro ⟨_, q, hpq, hq⟩
    exact ⟨q, ⟨by omega, hq⟩, hpq⟩
  · rintro ⟨q, ⟨_, hq⟩, hpq⟩
    exact ⟨by omega, q, hpq, hq⟩

/-- A stationary nonempty predecessor set contains a root of the current graph. -/
lemma root_mem_of_predecessor_closed {G : CommGraph n} {R S : Finset (Proc n)}
    (hR : IsRootSet G R) (hne : S.Nonempty)
    (hclosed : ∀ p q, G.edge p q → q ∈ S → p ∈ S) :
    ∃ r ∈ R, r ∈ S := by
  obtain ⟨q, hq⟩ := hne
  obtain ⟨r, hr, hreach⟩ := hR q
  refine ⟨r, hr, ?_⟩
  have hback : ∀ {p q}, Reachable G p q → q ∈ S → p ∈ S := by
    intro p q hpq
    induction hpq with
    | refl => exact id
    | @tail q v hpq hqv ih => exact fun hv => ih (hclosed q v hqv hv)
  exact hback hreach hq

/-- If an active ancestor set does not grow, it contains a current root. -/
lemma root_mem_of_ancestors_stationary {G : Round → CommGraph n} {a : TimedProc n}
    {t : ℕ} {R : Finset (Proc n)} (hR : IsRootSet (G (t + 1)) R) (hactive : t ≤ a.2)
    (heq : ancestors G a t = ancestors G a (t + 1)) :
    ∃ r ∈ R, r ∈ ancestors G a (t + 1) := by
  have ht : t < a.2 := by
    by_contra h
    have ht : a.2 = t := by omega
    have hat := ancestors_at G a
    have haf := ancestors_after G a (show a.2 < t + 1 by omega)
    rw [ht] at hat
    rw [hat, haf] at heq
    exact Finset.singleton_ne_empty _ heq
  apply root_mem_of_predecessor_closed hR
  · exact ⟨a.1, (mem_ancestors _ _ _ _).mpr (TemporalPath.self G (by omega) _)⟩
  · intro p q hpq hq
    rw [← heq]
    exact (ancestors_step ht p).mpr ⟨q, hq, hpq⟩

end AsymptoticSubspace.ComputationalModel
