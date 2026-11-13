import AsymptoticSubspace.PhysicalAveraging

/-!
# Graph products and relayed averaging

`graphProduct_broadcastable_paper` is Theorem 1 for every product length above
the stated bound. `relayed_averaging_linear_convergence` gives the relayed
agreement, validity, and geometric estimate of Corollary 12 for arbitrary
executions. `physical_averaging_linear_convergence` instantiates it for the
local-rule implementation. `ordinary_averaging_linear_convergence` gives
the ordinary-averaging clause by applying the volume theorem to blocks.
-/

noncomputable section

namespace AsymptoticSubspace

open ComputationalModel MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  {n : ℕ} [NeZero n]

/-- Theorem 1: any sufficiently long product of k-rooted graphs is
k-broadcastable, with the paper's real-valued lower bound on its length. -/
theorem graphProduct_broadcastable_paper {n : ℕ}
    (G : Round → CommGraph n) (start T k : ℕ)
    (hroot : ∀ t, 0 < t → IsKRooted (G t) k)
    (hT : ((Real.pi ^ 2 + 6) / 6) * (n : ℝ) + 1 ≤ (T : ℝ)) :
    IsKBroadcastable (graphProduct G start T) k := by
  exact graphProduct_broadcastable_linear_actualRounds G start T k hroot (by linarith)

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

/-- Corollary 12, ordinary averaging. Group `L` rounds, apply the volume
convergence theorem with weight `α^L`, and transfer convergence to every round. -/
theorem ordinary_averaging_linear_convergence
    (hd : 1 ≤ Module.finrank ℝ V) (E : AveragingExecution (V := V) n)
    (α : ℝ) (hα : 0 < α) (hsafe : AlphaSafeActualRounds E α)
    (hroot : ∀ t, 0 < t → IsKRooted (E.graphs t) (Module.finrank ℝ V)) :
    ∃ W : AffineSubspace ℝ V,
      Module.finrank ℝ W.direction = Module.finrank ℝ V - 1 ∧
      (∀ i, ConvergesToSet (fun t => E.outputs t i) (W : Set V)) ∧
      (∀ i, ConvergesToSet (fun t => E.outputs t i) (ModelLemmas.Poly E 0)) := by
  classical
  let L := linearBroadcastRounds n
  let B := blockExecution E.normalizeRoundZero L
  have hblocks : ∀ t, IsKBroadcastable (B.graphs t) (Module.finrank ℝ V) := fun t =>
    sharpRootedBroadcastBound n _ hd E.normalizeRoundZero.graphs
      (normalizeRoundZero_all (f := E.graphs) (P := fun G => IsKRooted G _) hroot)
      ((t - 1) * L)
  choose M hcard hM using hblocks
  have hmbw : MinimumBroadcastWeight B M (α ^ L) :=
    alphaSafe_implies_minimumBroadcastWeight B M _
      (blockExecution_safe E.normalizeRoundZero hα.le (alphaSafe_normalizeRoundZero E hsafe) L) hM
  obtain ⟨⟨W, hdim, hconv, _⟩, _⟩ := theorem_poss hd B M (α ^ L) (pow_pos hα L) hmbw hcard
  obtain ⟨F, hWF, hF⟩ := exists_affine_superspace_finrank W (hconv 0).1 hdim (Nat.sub_le _ _)
  refine ⟨F, hF, ?_, ModelLemmas.averaging_validityAtLimit E⟩
  exact convergesToSet_of_blocks E (linearBroadcastRounds_pos n) F.convex
    (fun i => convergesToSet_mono (hconv i) hWF)

/-- Normalize the unused weight slot of a relayed execution. Both graph slots
zero and one represent the first physical block, so its graph sequence is unchanged. -/
def RelayingExecution.normalizeRoundZero {G : Round → CommGraph n} {L : ℕ}
    (R : RelayingExecution (V := V) G L) : RelayingExecution (V := V) G L where
  averaging := R.averaging.normalizeRoundZero
  graphs_eq t := by
    cases t with
    | zero =>
      change R.averaging.graphs 1 = _
      simpa using R.graphs_eq 1
    | succ t => exact R.graphs_eq (t + 1)

/-- Corollary 12 for arbitrary relayed executions. Weights may depend on the
entire execution history; safety is imposed only at actual block-end updates. -/
theorem relayed_averaging_linear_convergence
    (G : Round → CommGraph n) (hd : 1 ≤ Module.finrank ℝ V)
    (hroot : ∀ t, 0 < t → IsKRooted (G t) (Module.finrank ℝ V))
    (R : RelayingExecution (V := V) G (linearBroadcastRounds n))
    (α : ℝ) (hα : 0 < α) (hsafe : AlphaSafeActualRounds R.averaging α) :
    (∃ W : AffineSubspace ℝ V,
      Module.finrank ℝ W.direction = Module.finrank ℝ V - 1 ∧
      (∀ i, ConvergesToSet (fun t => R.outputs t i) (W : Set V)) ∧
      (∀ i, ConvergesToSet (fun t => R.outputs t i) (R.poly 0))) ∧
    (∀ t, volume.real (R.poly t) ≤
      (1 - α ^ Module.finrank ℝ V) ^ (t / linearBroadcastRounds n) *
        volume.real (R.poly 0)) := by
  have hs := alphaSafe_normalizeRoundZero R.averaging hsafe
  have hblocks := sharpRootedBroadcastBound_actualRounds _ hd G hroot
  obtain ⟨⟨W, hdim, hconv, hvalid⟩, _⟩ := corollary_bound hd G _
    (linearBroadcastRounds_pos n) hblocks R.normalizeRoundZero α hα hs
  obtain ⟨F, hWF, hF⟩ := exists_affine_superspace_finrank W (hconv 0).1 hdim (Nat.sub_le _ _)
  refine ⟨⟨F, hF, fun i => convergesToSet_mono (hconv i) hWF, hvalid⟩, ?_⟩
  exact relayed_volume_geometric_bound G _ hblocks R.normalizeRoundZero α hα hs

/-- The rounded deadline following Corollary 12, for arbitrary relayed executions. -/
theorem relayed_averaging_linear_deadline
    (G : Round → CommGraph n) (hd : 1 ≤ Module.finrank ℝ V)
    (hroot : ∀ t, 0 < t → IsKRooted (G t) (Module.finrank ℝ V))
    (R : RelayingExecution (V := V) G (linearBroadcastRounds n))
    (α : ℝ) (hα : 0 < α) (hsafe : AlphaSafeActualRounds R.averaging α)
    (ε : ℝ) (hε : 0 < ε) (t : ℕ)
    (ht : ⌈(α ^ Module.finrank ℝ V)⁻¹ * Real.log (volume.real (R.poly 0) / ε)⌉₊ *
      linearBroadcastRounds n ≤ t) : volume (R.poly t) ≤ ENNReal.ofReal ε :=
  (corollary_bound hd G _ (linearBroadcastRounds_pos n)
    (sharpRootedBroadcastBound_actualRounds _ hd G hroot) R.normalizeRoundZero α hα
    (alphaSafe_normalizeRoundZero R.averaging hsafe)).2 ε hε t ht

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

/-- Corollary 12, relayed averaging: agreement in an affine subspace of exactly
dimension `d - 1`, validity, and the volume estimate at every physical round. -/
theorem physical_averaging_linear_convergence (R : LocalAveragingRule V n)
    (G : Round → CommGraph n) (init : Proc n → V)
    (hd : 1 ≤ Module.finrank ℝ V)
    (hroot : ∀ t, 0 < t → IsKRooted (G t) (Module.finrank ℝ V))
    (α : ℝ) (hα : 0 < α)
    (hsafe : AlphaSafeActualRounds
      (R.macroExecution (fixedRelayingSchedule (linearBroadcastRounds n)
        (linearBroadcastRounds_pos n)) G init) α) :
    let A := R.physicalAlgorithm (fixedRelayingSchedule (linearBroadcastRounds n)
      (linearBroadcastRounds_pos n))
    (∃ W : AffineSubspace ℝ V,
      Module.finrank ℝ W.direction = Module.finrank ℝ V - 1 ∧
      (∀ i, ConvergesToSet (fun t => A.run G init t i) (W : Set V)) ∧
      (∀ i, ConvergesToSet (fun t => A.run G init t i) (convexHull ℝ (Set.range init)))) ∧
    (∀ t, volume.real (convexHull ℝ (Set.range (A.run G init t))) ≤
      (1 - α ^ Module.finrank ℝ V) ^ (t / linearBroadcastRounds n) *
        volume.real (convexHull ℝ (Set.range init))) := by
  simpa only [LocalAveragingRule.physical_run_fixed, LocalAveragingRule.physical_outputs_fixed,
    RelayingExecution.poly, RelayingExecution.outputs, Nat.zero_div,
    LocalAveragingRule.fixedExecution, LocalAveragingRule.macroExecution,
    LocalAveragingRule.macroOutputs] using relayed_averaging_linear_convergence G hd hroot
      (R.fixedExecution G _ (linearBroadcastRounds_pos n) init) α hα hsafe

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
