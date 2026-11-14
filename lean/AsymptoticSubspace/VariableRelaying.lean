module

public import AsymptoticSubspace.ThmRooted
public import AsymptoticSubspace.TemporalAncestors

@[expose] public section

noncomputable section

namespace AsymptoticSubspace.ComputationalModel

variable {n : ℕ}

/-- A nonempty product contains its first graph, so it remains `k`-rooted. -/
lemma graphProduct_isKRooted (G : Round → CommGraph n) (start L k : ℕ) (hL : 0 < L)
    (hroot : IsKRooted (G (start + 1)) k) : IsKRooted (graphProduct G start L) k := by
  obtain ⟨R, hcard, hR⟩ := hroot
  refine ⟨R, hcard, fun i => ?_⟩
  obtain ⟨r, hr, hri⟩ := hR i
  refine ⟨r, hr, ?_⟩
  have hedge : ∀ p q, (G (start + 1)).edge p q → (graphProduct G start L).edge p q := by
    intro p q hpq
    rw [show L = (L - 1) + 1 by omega, graphProduct_succ_left]
    exact ⟨q, hpq, (graphProduct G (start + 1) (L - 1)).self_loop q⟩
  exact Relation.ReflTransGen.mono hedge r i hri

/-- Variable block boundaries; strict growth ensures every averaging update
eventually occurs. A uniform bound on block lengths is not needed for convergence. -/
structure RelayingSchedule where
  boundary : ℕ → ℕ
  boundary_zero : boundary 0 = 0
  strictMono : StrictMono boundary

namespace RelayingSchedule

lemma le_boundary (B : RelayingSchedule) (j : ℕ) : j ≤ B.boundary j := by
  have h := B.strictMono.id_le j
  exact h

def clock (B : RelayingSchedule) (t : ℕ) : ℕ :=
  ((Finset.range (t + 1)).filter (fun j => B.boundary j ≤ t)).max'
    ⟨0, by simp [B.boundary_zero]⟩

lemma clock_le (B : RelayingSchedule) (t : ℕ) : B.clock t ≤ t := by
  have hm := Finset.max'_mem
    ((Finset.range (t + 1)).filter (fun j => B.boundary j ≤ t))
    ⟨0, by simp [B.boundary_zero]⟩
  have hr := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
  change B.clock t < t + 1 at hr
  omega

@[simp] lemma clock_zero (B : RelayingSchedule) : B.clock 0 = 0 := by
  exact Nat.eq_zero_of_le_zero (B.clock_le 0)

lemma clock_progress (B : RelayingSchedule) (j t : ℕ) (h : B.boundary j ≤ t) : j ≤ B.clock t := by
  apply Finset.le_max'
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := B.le_boundary j; omega), h⟩

lemma convergence (B : RelayingSchedule) {V : Type*} [NormedAddCommGroup V]
    {x : Round → V} {S : Set V} (h : ConvergesToSet x S) :
    ConvergesToSet (fun t => x (B.clock t)) S := by
  refine ⟨h.1, fun ε hε => ?_⟩
  obtain ⟨j, hj⟩ := h.2 ε hε
  exact ⟨B.boundary j, fun t ht => hj (B.clock t) (B.clock_progress j t ht)⟩

end RelayingSchedule

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- An averaging update at each chosen boundary, on the product of the
communication graphs since the preceding boundary. Outputs are held between updates. -/
structure VariableRelayingExecution (G : Round → CommGraph n) (B : RelayingSchedule) where
  averaging : AveragingExecution (V := V) n
  graphs_eq : ∀ t, averaging.graphs t =
    graphProduct G (B.boundary (t - 1)) (B.boundary (t - 1 + 1) - B.boundary (t - 1))

def VariableRelayingExecution.outputs {G : Round → CommGraph n} {B : RelayingSchedule}
    (R : VariableRelayingExecution (V := V) G B) (t : ℕ) : Proc n → V :=
  R.averaging.outputs (B.clock t)

end AsymptoticSubspace.ComputationalModel

namespace AsymptoticSubspace

open ComputationalModel ModelLemmas

/-- The final corollary's allowance for variable bounded relaying periods.
In fact, any sequence of finite, positive block lengths preserves convergence. -/
theorem theorem_variable_relayed_solving
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {n : ℕ} [NeZero n] (k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ Module.finrank ℝ V)
    (G : Round → CommGraph n) (hroot : ∀ t, IsKRooted (G t) k) (B : RelayingSchedule)
    (R : VariableRelayingExecution (V := V) G B)
    (α : ℝ) (hα : 0 < α) (hsafe : AlphaSafe R.averaging α) :
    ∃ W : AffineSubspace ℝ V,
      Module.finrank ℝ W.direction ≤ k - 1 ∧
      (∀ i, ConvergesToSet (fun t => R.outputs t i) (W : Set V)) ∧
      (∀ i, ConvergesToSet (fun t => R.outputs t i) (convexHull ℝ (Set.range (R.outputs 0)))) := by
  have hmacro : ∀ t, IsKRooted (R.averaging.graphs t) k := by
    intro t
    rw [R.graphs_eq]
    exact graphProduct_isKRooted G _ _ k
      (Nat.sub_pos_of_lt (B.strictMono (Nat.lt_succ_self _))) (hroot _)
  obtain ⟨W, hdim, hconv, hvalid⟩ := theorem_rooted k hk hkd R.averaging α hα hsafe hmacro
  refine ⟨W, hdim, fun i => B.convergence
    (x := fun t => R.averaging.outputs t i) (hconv i), ?_⟩
  intro i
  simpa only [VariableRelayingExecution.outputs, RelayingSchedule.clock_zero]
    using B.convergence (x := fun t => R.averaging.outputs t i) (hvalid i)

end AsymptoticSubspace
