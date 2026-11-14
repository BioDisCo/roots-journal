module

public import AsymptoticSubspace.ExternalGraphBound
public import AsymptoticSubspace.ExactDimension

/-! The paper numbers communication/update rounds starting at one. Its initial
round zero has outputs but no communication or averaging weights. These bridges
remove the internal predicates' unused round-zero obligations: copying round one
into that slot changes neither a graph product nor any process trajectory. -/

/-!
# Positive-round hypotheses

An execution has initial outputs at time zero and performs updates at positive
rounds. Normalizing its unused graph and weight slot at zero leaves all outputs
unchanged. This module transfers the internal all-round interfaces to the
paper's convention.

`theorem_solving_exact_actualRounds` is Theorem 13, with an affine agreement
space of exactly dimension `k - 1`. `theorem_rooted_exact_actualRounds` gives
the safe-averaging clause of Corollary 20. Corollary 12 is assembled via the
volume theorem in `PhysicalRelayRates`.
-/

@[expose] public section

noncomputable section

namespace AsymptoticSubspace.ComputationalModel

/-- Fill an unused round-zero slot from round one, leaving actual rounds intact. -/
def normalizeRoundZero {X : Type*} (f : Round → X) : Round → X
  | 0 => f 1
  | t + 1 => f (t + 1)

@[simp] lemma normalizeRoundZero_zero {X : Type*} (f : Round → X) :
    normalizeRoundZero f 0 = f 1 := rfl

@[simp] lemma normalizeRoundZero_succ {X : Type*} (f : Round → X) (t : Round) :
    normalizeRoundZero f (t + 1) = f (t + 1) := rfl

lemma normalizeRoundZero_of_pos {X : Type*} (f : Round → X) {t : Round} (ht : 0 < t) :
    normalizeRoundZero f t = f t := by
  cases t with
  | zero => exact False.elim ((Nat.lt_irrefl 0) ht)
  | succ t => rfl

lemma normalizeRoundZero_all {X : Type*} {f : Round → X} {P : X → Prop}
    (h : ∀ t, 0 < t → P (f t)) : ∀ t, P (normalizeRoundZero f t)
  | 0 => h 1 Nat.zero_lt_one
  | t + 1 => h (t + 1) (Nat.zero_lt_succ t)

variable {n : ℕ}

@[simp] lemma graphProduct_normalizeRoundZero (G : Round → CommGraph n) (start L : ℕ) :
    graphProduct (normalizeRoundZero G) start L = graphProduct G start L := by
  induction L with
  | zero => rfl
  | succ L ih => simp only [graphProduct, ih, normalizeRoundZero_succ]

/-- Only rounds with actual communication must belong to the adversary. -/
def AdmissibleActualTrace (N : ObliviousMessageAdversary n) (G : Round → CommGraph n) : Prop :=
  ∀ t, 0 < t → G t ∈ N.graphs

lemma admissible_normalizeRoundZero {N : ObliviousMessageAdversary n}
    {G : Round → CommGraph n} (h : AdmissibleActualTrace N G) :
    AdmissibleTrace N (normalizeRoundZero G) :=
  normalizeRoundZero_all (f := G) (P := fun H => H ∈ N.graphs) h

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace AveragingExecution

section ActualInput

variable (G : Round → CommGraph n) (weights : Round → Proc n → Proc n → ℝ)
  (outputs : Round → Proc n → V)
  (hnonneg : ∀ t, 0 < t → ∀ i j, 0 ≤ weights t i j)
  (hsupport : ∀ t, 0 < t → ∀ i j, ¬ (G t).edge j i → weights t i j = 0)
  (hrowSum : ∀ t, 0 < t → ∀ i, (∑ j : Proc n, weights t i j) = 1)
  (hupdate : ∀ t i, outputs (t + 1) i = ∑ j : Proc n, weights (t + 1) i j • outputs t j)

/-- Construct the internal execution from the paper's raw data. Nonnegativity,
support, and row sums are required only on actual communication rounds. No
condition whatsoever is imposed on the supplied round-zero weights or their
relationship to the supplied round-zero graph; that unused slot is replaced by
round one. Every supplied output is retained exactly. -/
def ofActualRounds : AveragingExecution (V := V) n where
  graphs := ComputationalModel.normalizeRoundZero G
  weights := ComputationalModel.normalizeRoundZero weights
  outputs := outputs
  weights_nonneg t := by
    cases t with
    | zero => exact hnonneg 1 Nat.zero_lt_one
    | succ t => exact hnonneg (t + 1) (Nat.zero_lt_succ t)
  weights_support t := by
    cases t with
    | zero => exact hsupport 1 Nat.zero_lt_one
    | succ t => exact hsupport (t + 1) (Nat.zero_lt_succ t)
  weights_row_sum t := by
    cases t with
    | zero => exact hrowSum 1 Nat.zero_lt_one
    | succ t => exact hrowSum (t + 1) (Nat.zero_lt_succ t)
  update_rule := hupdate

@[simp] theorem ofActualRounds_outputs :
    (ofActualRounds G weights outputs hnonneg hsupport hrowSum hupdate).outputs = outputs := rfl

theorem ofActualRounds_graphs_pos {t : Round} (ht : 0 < t) :
    (ofActualRounds G weights outputs hnonneg hsupport hrowSum hupdate).graphs t = G t :=
  normalizeRoundZero_of_pos G ht

theorem ofActualRounds_weights_pos {t : Round} (ht : 0 < t) :
    (ofActualRounds G weights outputs hnonneg hsupport hrowSum hupdate).weights t = weights t :=
  normalizeRoundZero_of_pos weights ht

end ActualInput

end AveragingExecution

/-- Normalize bookkeeping data only; every output, including the initial output,
is definitionally unchanged. -/
def AveragingExecution.normalizeRoundZero (E : AveragingExecution (V := V) n) :
    AveragingExecution (V := V) n where
  graphs := ComputationalModel.normalizeRoundZero E.graphs
  weights := ComputationalModel.normalizeRoundZero E.weights
  outputs := E.outputs
  weights_nonneg t := by
    cases t with
    | zero => exact E.weights_nonneg 1
    | succ t => exact E.weights_nonneg (t + 1)
  weights_support t := by
    cases t with
    | zero => exact E.weights_support 1
    | succ t => exact E.weights_support (t + 1)
  weights_row_sum t := by
    cases t with
    | zero => exact E.weights_row_sum 1
    | succ t => exact E.weights_row_sum (t + 1)
  update_rule := E.update_rule

@[simp] lemma AveragingExecution.normalizeRoundZero_outputs
    (E : AveragingExecution (V := V) n) : E.normalizeRoundZero.outputs = E.outputs := rfl

/-- Safety is imposed only where an update actually occurs. -/
def AlphaSafeActualRounds (E : AveragingExecution (V := V) n) (α : ℝ) : Prop :=
  ∀ t, 0 < t → ∀ i j, (E.graphs t).edge j i → α ≤ E.weights t i j

/-- Broadcasting and its weight bound are imposed only on actual update rounds. -/
def MinimumBroadcastWeightActualRounds (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n)) (α : ℝ) : Prop :=
  (∀ t, 0 < t → IsBroadcastingSet (E.graphs t) (M t)) ∧
    (∀ t, 0 < t → ∀ i, α ≤ Finset.sum (M t) (fun j => E.weights t i j))

lemma alphaSafe_normalizeRoundZero (E : AveragingExecution (V := V) n) {α : ℝ}
    (h : AlphaSafeActualRounds E α) : AlphaSafe E.normalizeRoundZero α := by
  intro t
  cases t with
  | zero => exact h 1 Nat.zero_lt_one
  | succ t => exact h (t + 1) (Nat.zero_lt_succ t)

lemma minimumBroadcastWeight_normalizeRoundZero (E : AveragingExecution (V := V) n)
    {M : Round → Finset (Proc n)} {α : ℝ} (h : MinimumBroadcastWeightActualRounds E M α) :
    MinimumBroadcastWeight E.normalizeRoundZero (normalizeRoundZero M) α := by
  constructor
  · intro t
    cases t with
    | zero => exact h.1 1 Nat.zero_lt_one
    | succ t => exact h.1 (t + 1) (Nat.zero_lt_succ t)
  · intro t
    cases t with
    | zero => exact h.2 1 Nat.zero_lt_one
    | succ t => exact h.2 (t + 1) (Nat.zero_lt_succ t)

@[simp] lemma DeterministicAlgorithm.run_normalizeRoundZero
    (A : DeterministicAlgorithm V n) (G : Round → CommGraph n) (init : Proc n → V) :
    A.run (normalizeRoundZero G) init = A.run G init := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih => simp only [DeterministicAlgorithm.run, normalizeRoundZero_succ, ih]

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
@[simp] lemma StatefulAlgorithm.runState_normalizeRoundZero {State : Type*}
    (A : StatefulAlgorithm V n State) (G : Round → CommGraph n) (init : Proc n → V) :
    A.runState (normalizeRoundZero G) init = A.runState G init := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih => simp only [StatefulAlgorithm.runState, normalizeRoundZero_succ, ih]

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
@[simp] lemma StatefulAlgorithm.run_normalizeRoundZero {State : Type*}
    (A : StatefulAlgorithm V n State) (G : Round → CommGraph n) (init : Proc n → V) :
    A.run (normalizeRoundZero G) init = A.run G init := by
  funext t i
  simp only [StatefulAlgorithm.run, StatefulAlgorithm.runState_normalizeRoundZero]

/-- The paper's algorithm specification, without an admissibility condition on
the unused initial graph slot. -/
def SolvesAsymptoticSubspaceActualRounds (A : DeterministicAlgorithm V n)
    (N : ObliviousMessageAdversary n) (s : ℕ) : Prop :=
  ∀ (G : Round → CommGraph n) (init : Proc n → V), AdmissibleActualTrace N G →
    ∃ E : AffineSubspace ℝ V, FiniteDimensional ℝ E.direction ∧
      Module.finrank ℝ E.direction ≤ s ∧
      (∀ i, ConvergesToSet (fun t => A.run G init t i) (E : Set V)) ∧
      (∀ i, ConvergesToSet (fun t => A.run G init t i) (convexHull ℝ (Set.range init)))

theorem solvesAsymptoticSubspaceActualRounds_iff (A : DeterministicAlgorithm V n)
    (N : ObliviousMessageAdversary n) (s : ℕ) :
    SolvesAsymptoticSubspaceActualRounds A N s ↔ SolvesAsymptoticSubspace A N s := by
  constructor
  · intro h G init hG
    exact h G init (fun t _ => hG t)
  · intro h G init hG
    simpa only [A.run_normalizeRoundZero] using
      h (normalizeRoundZero G) init (admissible_normalizeRoundZero hG)

def StatefulSolvesActualRounds {State : Type*} (A : StatefulAlgorithm V n State)
    (N : ObliviousMessageAdversary n) (s : ℕ) : Prop :=
  ∀ (G : Round → CommGraph n) (init : Proc n → V), AdmissibleActualTrace N G →
    ∃ E : AffineSubspace ℝ V, FiniteDimensional ℝ E.direction ∧
      Module.finrank ℝ E.direction ≤ s ∧
      (∀ i, ConvergesToSet (fun t => A.run G init t i) (E : Set V)) ∧
      (∀ i, ConvergesToSet (fun t => A.run G init t i) (convexHull ℝ (Set.range init)))

theorem statefulSolvesActualRounds_iff {State : Type*} (A : StatefulAlgorithm V n State)
    (N : ObliviousMessageAdversary n) (s : ℕ) :
    StatefulSolvesActualRounds A N s ↔ StatefulSolves A N s := by
  constructor
  · intro h G init hG
    exact h G init (fun t _ => hG t)
  · intro h G init hG
    simpa only [A.run_normalizeRoundZero] using
      h (normalizeRoundZero G) init (admissible_normalizeRoundZero hG)

end AsymptoticSubspace.ComputationalModel

namespace AsymptoticSubspace

open ComputationalModel ModelLemmas MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {n : ℕ} [NeZero n]

/-- The geometric rate with hypotheses on communication rounds `t ≥ 1` only. -/
theorem volume_geometric_bound_actualRounds
    (E : AveragingExecution (V := V) n) (M : Round → Finset (Proc n))
    (α : ℝ) (hα : 0 < α) (hmbw : MinimumBroadcastWeightActualRounds E M α)
    (hcard : ∀ t, 0 < t → (M t).card ≤ Module.finrank ℝ V) (t : ℕ) :
    volume.real (Poly E t) ≤
      (1 - α ^ Module.finrank ℝ V) ^ t * volume.real (Poly E 0) :=
  volume_geometric_bound E.normalizeRoundZero (normalizeRoundZero M) α hα
    (minimumBroadcastWeight_normalizeRoundZero E hmbw)
    (normalizeRoundZero_all (f := M) (P := fun R => R.card ≤ Module.finrank ℝ V) hcard) t

theorem volume_round_bound_actualRounds
    (E : AveragingExecution (V := V) n) (M : Round → Finset (Proc n))
    (α : ℝ) (hα : 0 < α) (hmbw : MinimumBroadcastWeightActualRounds E M α)
    (hcard : ∀ t, 0 < t → (M t).card ≤ Module.finrank ℝ V)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (ht : (α ^ Module.finrank ℝ V)⁻¹ *
      Real.log (volume.real (Poly E 0) / ε) ≤ (t : ℝ)) :
    volume (Poly E t) ≤ ENNReal.ofReal ε :=
  volume_round_bound E.normalizeRoundZero (normalizeRoundZero M) α hα
    (minimumBroadcastWeight_normalizeRoundZero E hmbw)
    (normalizeRoundZero_all (f := M) (P := fun R => R.card ≤ Module.finrank ℝ V) hcard) hε t ht

/-- `thm:poss` with no broadcasting, cardinality, or weight condition on the
initial bookkeeping slot. Output round zero remains exactly the given input. -/
theorem theorem_poss_actualRounds
    (hd : 1 ≤ Module.finrank ℝ V)
    (E : AveragingExecution (V := V) n) (M : Round → Finset (Proc n))
    (α : ℝ) (hα : 0 < α) (hmbw : MinimumBroadcastWeightActualRounds E M α)
    (hcard : ∀ t, 0 < t → (M t).card ≤ Module.finrank ℝ V) :
    (∃ W : AffineSubspace ℝ V,
      Module.finrank ℝ W.direction ≤ Module.finrank ℝ V - 1 ∧
      (∀ i, ConvergesToSet (fun t => E.outputs t i) (W : Set V)) ∧
      (∀ i, ConvergesToSet (fun t => E.outputs t i) (Poly E 0))) ∧
    (∀ (ε : ℝ), 0 < ε → ∀ t : ℕ,
      (α ^ Module.finrank ℝ V)⁻¹ * Real.log (volume.real (Poly E 0) / ε) ≤ (t : ℝ) →
      volume (Poly E t) ≤ ENNReal.ofReal ε) :=
  theorem_poss hd E.normalizeRoundZero (normalizeRoundZero M) α hα
    (minimumBroadcastWeight_normalizeRoundZero E hmbw)
    (normalizeRoundZero_all (f := M) (P := fun R => R.card ≤ Module.finrank ℝ V) hcard)

omit [MeasurableSpace V] [BorelSpace V] in
/-- General broadcasting-set sufficiency, constraining actual update rounds only. -/
theorem theorem_solving_actualRounds
    (k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ Module.finrank ℝ V)
    (E : AveragingExecution (V := V) n) (M : Round → Finset (Proc n))
    (α : ℝ) (hα : 0 < α) (hmbw : MinimumBroadcastWeightActualRounds E M α)
    (hcard : ∀ t, 0 < t → (M t).card ≤ k) :
    ∃ W : AffineSubspace ℝ V,
      Module.finrank ℝ W.direction ≤ k - 1 ∧
      (∀ i, ConvergesToSet (fun t => E.outputs t i) (W : Set V)) ∧
      (∀ i, ConvergesToSet (fun t => E.outputs t i) (Poly E 0)) :=
  ThmSolving.theorem_solving (Module.finrank ℝ V) k hkd hk
    E.normalizeRoundZero (normalizeRoundZero M) α hα
    (minimumBroadcastWeight_normalizeRoundZero E hmbw)
    (normalizeRoundZero_all (f := M) (P := fun R => R.card ≤ k) hcard) rfl

omit [MeasurableSpace V] [BorelSpace V] in
/-- The ordinary averaging sufficiency theorem only constrains actual rounds. -/
theorem theorem_rooted_actualRounds
    (k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ Module.finrank ℝ V)
    (E : AveragingExecution (V := V) n) (α : ℝ) (hα : 0 < α)
    (hsafe : AlphaSafeActualRounds E α)
    (hroot : ∀ t, 0 < t → IsKRooted (E.graphs t) k) :
    ∃ W : AffineSubspace ℝ V,
      Module.finrank ℝ W.direction ≤ k - 1 ∧
      (∀ i, ConvergesToSet (fun t => E.outputs t i) (W : Set V)) ∧
      (∀ i, ConvergesToSet (fun t => E.outputs t i) (Poly E 0)) :=
  theorem_rooted k hk hkd E.normalizeRoundZero α hα
    (alphaSafe_normalizeRoundZero E hsafe)
    (normalizeRoundZero_all (f := E.graphs) (P := fun G => IsKRooted G k) hroot)

omit [MeasurableSpace V] [BorelSpace V] in
/-- The paper's exact target dimension, with only actual-round broadcasting
hypotheses. The containing affine subspace can always be enlarged to dimension
exactly `k - 1` without changing any trajectory or validity property. -/
theorem theorem_solving_exact_actualRounds
    (k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ Module.finrank ℝ V)
    (E : AveragingExecution (V := V) n) (M : Round → Finset (Proc n))
    (α : ℝ) (hα : 0 < α) (hmbw : MinimumBroadcastWeightActualRounds E M α)
    (hcard : ∀ t, 0 < t → (M t).card ≤ k) :
    ∃ W : AffineSubspace ℝ V,
      Module.finrank ℝ W.direction = k - 1 ∧
      (∀ i, ConvergesToSet (fun t => E.outputs t i) (W : Set V)) ∧
      (∀ i, ConvergesToSet (fun t => E.outputs t i) (Poly E 0)) := by
  obtain ⟨W, hW, hconv, hvalid⟩ := theorem_solving_actualRounds k hk hkd E M α hα hmbw hcard
  obtain ⟨F, hWF, hF⟩ := exists_affine_superspace_finrank W (hconv 0).1 hW
    ((Nat.sub_le k 1).trans hkd)
  exact ⟨F, hF, fun i => convergesToSet_mono (hconv i) hWF, hvalid⟩

omit [MeasurableSpace V] [BorelSpace V] in
/-- Rooted-adversary sufficiency with exactly the paper's target dimension and
without any round-zero graph or safety obligation. -/
theorem theorem_rooted_exact_actualRounds
    (k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ Module.finrank ℝ V)
    (E : AveragingExecution (V := V) n) (α : ℝ) (hα : 0 < α)
    (hsafe : AlphaSafeActualRounds E α)
    (hroot : ∀ t, 0 < t → IsKRooted (E.graphs t) k) :
    ∃ W : AffineSubspace ℝ V,
      Module.finrank ℝ W.direction = k - 1 ∧
      (∀ i, ConvergesToSet (fun t => E.outputs t i) (W : Set V)) ∧
      (∀ i, ConvergesToSet (fun t => E.outputs t i) (Poly E 0)) := by
  obtain ⟨W, hW, hconv, hvalid⟩ := theorem_rooted_actualRounds k hk hkd E α hα hsafe hroot
  obtain ⟨F, hWF, hF⟩ := exists_affine_superspace_finrank W (hconv 0).1 hW
    ((Nat.sub_le k 1).trans hkd)
  exact ⟨F, hF, fun i => convergesToSet_mono (hconv i) hWF, hvalid⟩

/-- The graph theorem needs rootedness only on communication rounds, not at zero. -/
theorem graphProduct_broadcastable_linear_actualRounds
    {n : ℕ} (G : Round → CommGraph n) (start T k : ℕ)
    (hroot : ∀ t, 0 < t → IsKRooted (G t) k)
    (hT : ((Real.pi ^ 2 + 6) / 6) * (n : ℝ) < (T : ℝ) + 1) :
    IsKBroadcastable (graphProduct G start T) k := by
  simpa only [graphProduct_normalizeRoundZero] using
    graphProduct_broadcastable_linear (normalizeRoundZero G) start T k
      (normalizeRoundZero_all (f := G) (P := fun H => IsKRooted H k) hroot) hT

section Exact

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Exact-dimensional agreement with admissibility required only for `t ≥ 1`. -/
def StatefulSolvesExactActualRounds {State : Type*} {n : ℕ}
    (A : StatefulAlgorithm V n State) (N : ObliviousMessageAdversary n) (s : ℕ) : Prop :=
  ∀ (G : Round → CommGraph n) (init : Proc n → V), AdmissibleActualTrace N G →
    ∃ E : AffineSubspace ℝ V, Module.finrank ℝ E.direction = s ∧
      (∀ i, ConvergesToSet (fun t => A.run G init t i) (E : Set V)) ∧
      (∀ i, ConvergesToSet (fun t => A.run G init t i) (convexHull ℝ (Set.range init)))

theorem statefulSolvesExactActualRounds_iff {State : Type*} {n : ℕ}
    (A : StatefulAlgorithm V n State) (N : ObliviousMessageAdversary n) (s : ℕ) :
    StatefulSolvesExactActualRounds A N s ↔ StatefulSolvesExact A N s := by
  constructor
  · intro h G init hG
    exact h G init (fun t _ => hG t)
  · intro h G init hG
    simpa only [A.run_normalizeRoundZero] using
      h (normalizeRoundZero G) init (admissible_normalizeRoundZero hG)

end Exact

universe u

/-- The final paper characterization, with arbitrary state, exact dimension,
and no admissibility requirement on the initial graph slot. -/
theorem corollary_characterization_actualRounds
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {n : ℕ} [NeZero n] (N : ObliviousMessageAdversary n) (s : ℕ)
    (hs : s < Module.finrank ℝ V) :
    (∃ (State : Type u) (A : StatefulAlgorithm V n State),
      StatefulSolvesExactActualRounds A N s) ↔ IsKRootedAdversary N (s + 1) := by
  simp only [statefulSolvesExactActualRounds_iff]
  exact corollary_characterization_exact N s hs

end AsymptoticSubspace
