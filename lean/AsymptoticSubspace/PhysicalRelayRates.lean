import AsymptoticSubspace.PhysicalAveraging

noncomputable section

namespace AsymptoticSubspace

open ComputationalModel MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  {n : ℕ} [NeZero n]

/-- The physical local averaging protocol, connected to the fixed-block
execution used in the rate theorem. No graph-product realization is assumed. -/
def ComputationalModel.LocalAveragingRule.fixedExecution (R : LocalAveragingRule V n)
    (G : Round → CommGraph n) (L : ℕ) (hL : 0 < L) (init : Proc n → V) :
    RelayingExecution (V := V) G L where
  averaging := R.macroExecution (fixedRelayingSchedule L hL) G init
  graphs_eq t := by
    dsimp [LocalAveragingRule.macroExecution, fixedRelayingSchedule]
    rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [NeZero n] in
lemma ComputationalModel.LocalAveragingRule.physical_run_fixed (R : LocalAveragingRule V n)
    (G : Round → CommGraph n) (L : ℕ) (hL : 0 < L) (init : Proc n → V) (t : ℕ) (i : Proc n) :
    (R.physicalAlgorithm (fixedRelayingSchedule L hL)).run G init t i =
      (R.fixedExecution G L hL init).outputs t i := by
  rw [LocalAveragingRule.physical_run, fixedRelayingSchedule_clock]
  rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [NeZero n] in
lemma ComputationalModel.LocalAveragingRule.physical_outputs_fixed (R : LocalAveragingRule V n)
    (G : Round → CommGraph n) (L : ℕ) (hL : 0 < L) (init : Proc n → V) (t : ℕ) :
    (R.physicalAlgorithm (fixedRelayingSchedule L hL)).run G init t =
      (R.fixedExecution G L hL init).outputs t :=
  funext (R.physical_run_fixed G L hL init t)

omit [NeZero n] in
/-- The sharp block length works without imposing any graph condition at zero. -/
theorem sharpRootedBroadcastBound_actualRounds (k : ℕ) (hk : 1 ≤ k)
    (G : Round → CommGraph n) (hroot : ∀ t, 0 < t → IsKRooted (G t) k) (start : ℕ) :
    IsKBroadcastable (graphProduct G start (linearBroadcastRounds n)) k := by
  simpa only [graphProduct_normalizeRoundZero] using
    sharpRootedBroadcastBound n k hk (normalizeRoundZero G)
      (normalizeRoundZero_all (f := G) (P := fun H => IsKRooted H k) hroot) start

/-- Geometric rate for actual physical outputs. Safety is required only on the
constructed macro execution, so no safety on unreachable buffers is assumed. -/
theorem physical_averaging_linear_geometric (R : LocalAveragingRule V n)
    (G : Round → CommGraph n) (init : Proc n → V)
    (hd : 1 ≤ Module.finrank ℝ V)
    (hroot : ∀ t, 0 < t → IsKRooted (G t) (Module.finrank ℝ V))
    (α : ℝ) (hα : 0 < α)
    (hsafe : AlphaSafeActualRounds
      (R.macroExecution (fixedRelayingSchedule (linearBroadcastRounds n)
        (linearBroadcastRounds_pos n)) G init) α) (t : ℕ) :
    volume.real (convexHull ℝ (Set.range
      ((R.physicalAlgorithm (fixedRelayingSchedule (linearBroadcastRounds n)
        (linearBroadcastRounds_pos n))).run G init t))) ≤
      (1 - α ^ Module.finrank ℝ V) ^ (t / linearBroadcastRounds n) *
        volume.real (convexHull ℝ (Set.range init)) := by
  rw [LocalAveragingRule.physical_outputs_fixed]
  have h := relayed_volume_geometric_bound G (linearBroadcastRounds n)
    (sharpRootedBroadcastBound_actualRounds _ hd G hroot)
    (R.fixedExecution G _ (linearBroadcastRounds_pos n) init) α hα
      (R.macroExecution_safe_of_actualRounds _ G init hsafe) t
  simpa only [LocalAveragingRule.physical_run_fixed, RelayingExecution.poly,
    RelayingExecution.outputs, LocalAveragingRule.fixedExecution,
    LocalAveragingRule.macroExecution, Nat.zero_div, LocalAveragingRule.macroOutputs] using h

/-- Rounded physical-round deadline, including the final-round update. -/
theorem physical_averaging_linear_deadline (R : LocalAveragingRule V n)
    (G : Round → CommGraph n) (init : Proc n → V)
    (hd : 1 ≤ Module.finrank ℝ V)
    (hroot : ∀ t, 0 < t → IsKRooted (G t) (Module.finrank ℝ V))
    (α : ℝ) (hα : 0 < α)
    (hsafe : AlphaSafeActualRounds
      (R.macroExecution (fixedRelayingSchedule (linearBroadcastRounds n)
        (linearBroadcastRounds_pos n)) G init) α)
    (ε : ℝ) (hε : 0 < ε) (t : ℕ)
    (ht : ⌈(α ^ Module.finrank ℝ V)⁻¹ *
      Real.log (volume.real (convexHull ℝ (Set.range init)) / ε)⌉₊ *
        linearBroadcastRounds n ≤ t) :
    volume (convexHull ℝ (Set.range
      ((R.physicalAlgorithm (fixedRelayingSchedule (linearBroadcastRounds n)
        (linearBroadcastRounds_pos n))).run G init t))) ≤ ENNReal.ofReal ε := by
  rw [LocalAveragingRule.physical_outputs_fixed]
  have h := (corollary_bound hd G (linearBroadcastRounds n) (linearBroadcastRounds_pos n)
    (sharpRootedBroadcastBound_actualRounds _ hd G hroot)
    (R.fixedExecution G _ (linearBroadcastRounds_pos n) init) α hα
      (R.macroExecution_safe_of_actualRounds _ G init hsafe)).2 ε hε t
  simp only [RelayingExecution.poly, RelayingExecution.outputs,
    LocalAveragingRule.fixedExecution, LocalAveragingRule.macroExecution,
    Nat.zero_div, LocalAveragingRule.macroOutputs] at h
  simpa only [RelayingExecution.poly,
    RelayingExecution.outputs, LocalAveragingRule.fixedExecution,
    LocalAveragingRule.macroExecution, Nat.zero_div, LocalAveragingRule.macroOutputs] using h ht

end AsymptoticSubspace
