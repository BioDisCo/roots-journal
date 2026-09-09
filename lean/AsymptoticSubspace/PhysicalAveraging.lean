import AsymptoticSubspace.PhysicalRelaying
import AsymptoticSubspace.ActualRounds

noncomputable section

namespace AsymptoticSubspace.ComputationalModel

/-- A local averaging rule reads only the finite origin/value map received in
the current block. Weights may depend on time, receiver, and all received values.
An empty buffer is allowed as an unreachable internal state; stochasticity is
required whenever at least one value is present. -/
structure LocalAveragingRule (V : Type*) (n : ℕ) where
  weights : Round → Proc n → OriginBuffer V n → Proc n → ℝ
  nonneg : ∀ t i b j, 0 ≤ weights t i b j
  support : ∀ t i b j, b j = none → weights t i b j = 0
  row_sum : ∀ t i b, (∃ j v, b j = some v) → (∑ j, weights t i b j) = 1

namespace LocalAveragingRule

variable {V : Type*} {n : ℕ}

/-- Uniform positive safety on actual physical update rounds. -/
def Safe (R : LocalAveragingRule V n) (α : ℝ) : Prop :=
  ∀ t, 0 < t → ∀ i b j v, b j = some v → α ≤ R.weights t i b j

variable [NormedAddCommGroup V] [NormedSpace ℝ V]

def update (R : LocalAveragingRule V n) (t : Round) (i : Proc n)
    (b : OriginBuffer V n) : V := ∑ j, R.weights t i b j • (b j).getD 0

lemma update_floodBuffer (R : LocalAveragingRule V n) (t : Round) (i : Proc n)
    (G : Round → CommGraph n) (start len : ℕ) (x : Proc n → V) :
    R.update t i (floodBuffer G start len x i) =
      ∑ j, R.weights t i (floodBuffer G start len x i) j • x j := by
  classical
  unfold update
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : (graphProduct G start len).edge j i
  · simp only [floodBuffer, if_pos h, Option.getD_some]
  · rw [R.support t i _ j (by simp [floodBuffer, h])]
    simp

/-- Macro outputs are constructed recursively from the local rule and actual
flooded buffers; no macro trajectory or graph realization is assumed. -/
def macroOutputs (R : LocalAveragingRule V n) (B : RelayingSchedule)
    (G : Round → CommGraph n) (init : Proc n → V) : ℕ → Proc n → V
  | 0 => init
  | k + 1 => fun i => R.update (B.boundary (k + 1)) i
      (floodBuffer G (B.boundary k) (B.boundary (k + 1) - B.boundary k)
        (macroOutputs R B G init k) i)

def macroBuffer (R : LocalAveragingRule V n) (B : RelayingSchedule)
    (G : Round → CommGraph n) (init : Proc n → V) (t : ℕ) (i : Proc n) : OriginBuffer V n :=
  floodBuffer G (B.boundary (t - 1)) (B.boundary (t - 1 + 1) - B.boundary (t - 1))
    (R.macroOutputs B G init (t - 1)) i

lemma macroBuffer_self (R : LocalAveragingRule V n) (B : RelayingSchedule)
    (G : Round → CommGraph n) (init : Proc n → V) (t : ℕ) (i : Proc n) :
    R.macroBuffer B G init t i i = some (R.macroOutputs B G init (t - 1) i) := by
  simp only [macroBuffer, floodBuffer, if_pos (CommGraph.self_loop _ i)]

/-- The stochastic macro execution is derived from the physical update rule.
The unused round-zero graph/weight slot duplicates the first block. -/
def macroExecution (R : LocalAveragingRule V n) (B : RelayingSchedule)
    (G : Round → CommGraph n) (init : Proc n → V) : AveragingExecution (V := V) n where
  graphs t := graphProduct G (B.boundary (t - 1))
    (B.boundary (t - 1 + 1) - B.boundary (t - 1))
  weights t i j := R.weights (B.boundary (t - 1 + 1)) i (R.macroBuffer B G init t i) j
  outputs := R.macroOutputs B G init
  weights_nonneg _ _ _ := R.nonneg _ _ _ _
  weights_support t i j h := R.support _ _ _ _ (by simp [macroBuffer, floodBuffer, h])
  weights_row_sum t i := R.row_sum _ _ _ ⟨i, _, R.macroBuffer_self B G init t i⟩
  update_rule t i := by
    simpa only [macroOutputs, macroBuffer, Nat.add_sub_cancel] using
      R.update_floodBuffer (B.boundary (t + 1)) i G (B.boundary t)
        (B.boundary (t + 1) - B.boundary t) (R.macroOutputs B G init t)

def variableExecution (R : LocalAveragingRule V n) (B : RelayingSchedule)
    (G : Round → CommGraph n) (init : Proc n → V) : VariableRelayingExecution (V := V) G B where
  averaging := R.macroExecution B G init
  graphs_eq _ := rfl

theorem macroExecution_safe (R : LocalAveragingRule V n) (B : RelayingSchedule)
    (G : Round → CommGraph n) (init : Proc n → V) {α : ℝ} (hsafe : R.Safe α) :
    AlphaSafe (R.macroExecution B G init) α := by
  intro t i j h
  change (graphProduct G (B.boundary (t - 1))
    (B.boundary (t - 1 + 1) - B.boundary (t - 1))).edge j i at h
  apply hsafe (B.boundary (t - 1 + 1))
    ((Nat.zero_lt_succ (t - 1)).trans_le (B.le_boundary (t - 1 + 1))) i _ j
    (R.macroOutputs B G init (t - 1) j)
  simp only [macroBuffer, floodBuffer, if_pos h]

/-- Safety only for buffers actually received during this execution. In
particular, no lower weight bound is demanded on unreachable input buffers. -/
def SafeExecution (R : LocalAveragingRule V n) (B : RelayingSchedule)
    (G : Round → CommGraph n) (init : Proc n → V) (α : ℝ) : Prop :=
  ∀ k i j v, R.macroBuffer B G init (k + 1) i j = some v →
    α ≤ R.weights (B.boundary (k + 1)) i (R.macroBuffer B G init (k + 1) i) j

/-- Safety for every actual execution in a given message adversary. -/
def SafeForAdversary (R : LocalAveragingRule V n) (B : RelayingSchedule)
    (N : ObliviousMessageAdversary n) (α : ℝ) : Prop :=
  ∀ G init, AdmissibleActualTrace N G → R.SafeExecution B G init α

lemma safeExecution_of_safe (R : LocalAveragingRule V n) (B : RelayingSchedule)
    (G : Round → CommGraph n) (init : Proc n → V) {α : ℝ} (hsafe : R.Safe α) :
    R.SafeExecution B G init α := by
  intro k i j v hv
  exact hsafe (B.boundary (k + 1))
    ((Nat.zero_lt_succ k).trans_le (B.le_boundary (k + 1))) i _ j v hv

theorem macroExecution_safeActualRounds_of_safeExecution
    (R : LocalAveragingRule V n) (B : RelayingSchedule)
    (G : Round → CommGraph n) (init : Proc n → V) {α : ℝ}
    (hsafe : R.SafeExecution B G init α) :
    AlphaSafeActualRounds (R.macroExecution B G init) α := by
  intro t ht i j h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt ht)
  change α ≤ R.weights (B.boundary (k + 1)) i (R.macroBuffer B G init (k + 1) i) j
  apply hsafe k i j (R.macroOutputs B G init k j)
  change (graphProduct G (B.boundary k) (B.boundary (k + 1) - B.boundary k)).edge j i at h
  change floodBuffer G (B.boundary k) (B.boundary (k + 1) - B.boundary k)
    (R.macroOutputs B G init k) i j = some (R.macroOutputs B G init k j)
  simp only [floodBuffer, if_pos h]

/-- The macro execution's slot zero duplicates slot one, so an internal
all-round safety predicate introduces no additional assumption here. -/
theorem macroExecution_safe_of_actualRounds
    (R : LocalAveragingRule V n) (B : RelayingSchedule)
    (G : Round → CommGraph n) (init : Proc n → V) {α : ℝ}
    (hsafe : AlphaSafeActualRounds (R.macroExecution B G init) α) :
    AlphaSafe (R.macroExecution B G init) α := by
  intro t i j hj
  cases t with
  | zero => exact hsafe 1 Nat.zero_lt_one i j hj
  | succ t => exact hsafe (t + 1) (Nat.zero_lt_succ t) i j hj

/-- The concrete, cross-graph-local physical protocol for an arbitrary local
averaging rule; the last communication round performs the averaging update. -/
def physicalAlgorithm (R : LocalAveragingRule V n) (B : RelayingSchedule) :
    StatefulAlgorithm V n (RelayState V n) := physicalRelayAlgorithm B R.update

/-- End-to-end correctness for every local averaging rule. The macro execution,
its averaging law, and the flooding correspondence are all constructed/proved. -/
theorem physical_run (R : LocalAveragingRule V n) (B : RelayingSchedule)
    (G : Round → CommGraph n) (init : Proc n → V) (t : ℕ) (i : Proc n) :
    (R.physicalAlgorithm B).run G init t i = R.macroOutputs B G init (B.clock t) i :=
  physicalRelay_run B R.update G init (R.macroOutputs B G init) rfl (fun _ _ => rfl) t i

end LocalAveragingRule
end AsymptoticSubspace.ComputationalModel

namespace AsymptoticSubspace

open ComputationalModel

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {n : ℕ} [NeZero n]

/-- Every uniformly safe local averaging rule, executed by actual flooding,
converges under any shared schedule of finite positive block lengths. Only
actual positive communication rounds are required to be rooted. -/
theorem physical_averaging_converges_of_safeExecution
    (R : LocalAveragingRule V n) (B : RelayingSchedule)
    (G : Round → CommGraph n) (init : Proc n → V)
    (k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ Module.finrank ℝ V)
    (hroot : ∀ t, 0 < t → IsKRooted (G t) k)
    (α : ℝ) (hα : 0 < α) (hsafe : R.SafeExecution B G init α) :
    ∃ W : AffineSubspace ℝ V, Module.finrank ℝ W.direction ≤ k - 1 ∧
      (∀ i, ConvergesToSet (fun t => (R.physicalAlgorithm B).run G init t i) (W : Set V)) ∧
      (∀ i, ConvergesToSet (fun t => (R.physicalAlgorithm B).run G init t i)
        (convexHull ℝ (Set.range init))) := by
  have hmacro : ∀ t, 0 < t → IsKRooted ((R.macroExecution B G init).graphs t) k := by
    intro t _
    apply graphProduct_isKRooted G _ _ k
      (Nat.sub_pos_of_lt (B.strictMono (Nat.lt_succ_self _)))
    exact hroot _ (Nat.zero_lt_succ _)
  obtain ⟨W, hdim, hconv, hvalid⟩ := theorem_rooted_actualRounds k hk hkd
    (R.macroExecution B G init) α hα
    (R.macroExecution_safeActualRounds_of_safeExecution B G init hsafe) hmacro
  refine ⟨W, hdim, ?_, ?_⟩
  · intro i
    simpa only [LocalAveragingRule.physical_run] using
      B.convergence (x := fun t => R.macroOutputs B G init t i) (hconv i)
  · intro i
    simpa only [LocalAveragingRule.physical_run] using
      B.convergence (x := fun t => R.macroOutputs B G init t i) (hvalid i)

/-- Convenience form for a rule safe on every possible received buffer. -/
theorem physical_averaging_converges (R : LocalAveragingRule V n) (B : RelayingSchedule)
    (G : Round → CommGraph n) (init : Proc n → V)
    (k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ Module.finrank ℝ V)
    (hroot : ∀ t, 0 < t → IsKRooted (G t) k)
    (α : ℝ) (hα : 0 < α) (hsafe : R.Safe α) :
    ∃ W : AffineSubspace ℝ V, Module.finrank ℝ W.direction ≤ k - 1 ∧
      (∀ i, ConvergesToSet (fun t => (R.physicalAlgorithm B).run G init t i) (W : Set V)) ∧
      (∀ i, ConvergesToSet (fun t => (R.physicalAlgorithm B).run G init t i)
        (convexHull ℝ (Set.range init))) :=
  physical_averaging_converges_of_safeExecution R B G init k hk hkd hroot α hα
    (R.safeExecution_of_safe B G init hsafe)

/-- Algorithm-level, exactly-dimensional form of the final paper claim for
every local safe averaging rule, including its actual message-relaying protocol.
There is no assumed macro execution, update correspondence, or flooding premise. -/
theorem physical_averaging_solves_of_safeForAdversary
    (R : LocalAveragingRule V n) (B : RelayingSchedule)
    (N : ObliviousMessageAdversary n) (s : ℕ) (hs : s < Module.finrank ℝ V)
    (hroot : IsKRootedAdversary N (s + 1)) (α : ℝ) (hα : 0 < α)
    (hsafe : R.SafeForAdversary B N α) :
    StatefulSolvesExactActualRounds (R.physicalAlgorithm B) N s := by
  intro G init hG
  obtain ⟨W, hdim, hconv, hvalid⟩ := physical_averaging_converges_of_safeExecution R B G init
    (s + 1) (by omega) (by omega) (fun t ht => hroot (G t) (hG t ht)) α hα (hsafe G init hG)
  obtain ⟨F, hWF, hF⟩ := exists_affine_superspace_finrank W (hconv 0).1
    (show Module.finrank ℝ W.direction ≤ s by simpa using hdim) hs.le
  exact ⟨F, hF, fun i => convergesToSet_mono (hconv i) hWF, hvalid⟩

/-- Globally safe local rules satisfy the same exactly-dimensional solver
specification; adversary-relative safety suffices in the stronger theorem above. -/
theorem physical_averaging_solves (R : LocalAveragingRule V n) (B : RelayingSchedule)
    (N : ObliviousMessageAdversary n) (s : ℕ) (hs : s < Module.finrank ℝ V)
    (hroot : IsKRootedAdversary N (s + 1)) (α : ℝ) (hα : 0 < α) (hsafe : R.Safe α) :
    StatefulSolvesExactActualRounds (R.physicalAlgorithm B) N s :=
  physical_averaging_solves_of_safeForAdversary R B N s hs hroot α hα
    (fun G init _ => R.safeExecution_of_safe B G init hsafe)

end AsymptoticSubspace
