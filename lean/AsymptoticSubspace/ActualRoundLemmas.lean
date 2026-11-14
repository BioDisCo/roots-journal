module

public import AsymptoticSubspace.ActualRounds
public import AsymptoticSubspace.LemXiXip
public import AsymptoticSubspace.LemDifferences
public import AsymptoticSubspace.LemHalfspaceZone
public import AsymptoticSubspace.LemContract
public import AsymptoticSubspace.LemDeltaContraction

/-!
# Averaging results on positive communication rounds

The statements in this module are Lemmas 5, 10, 14, 15, 19 and Theorem 6.
The index `t` denotes the pre-update round: the corresponding update in the
paper is round `t + 1`. `Poly E t`, `PolyOn E t S`, and `vectorSpan ℝ (ValuesOn E t S)`
represent `P(t)`, `P_S(t)`, and `dir(X_S(t))`, respectively.

Theorem 6 uses volume contraction, compactness of the nested hulls, and
Lemma 11 to place their intersection in a hyperplane. Lemma 10 uses the
symmetrization and concave-radius estimates of Section 5.2.
-/

@[expose] public section

noncomputable section

namespace AsymptoticSubspace

open ComputationalModel ModelLemmas MeasureTheory

/-- The output decomposition only assumes broadcasting weights on actual update
rounds. The untouched initial outputs are used at `t = 0`. -/
theorem lemma_xi_xip_actualRounds
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}
    (E : AveragingExecution (V := V) n) (M : Round → Finset (Proc n))
    (α : ℝ) (t : Round) (i : Proc n) (hα : 0 < α)
    (hmbw : MinimumBroadcastWeightActualRounds E M α) :
    ∃ ξ ∈ PolyOn E t (M (t + 1)), ∃ ξ' ∈ Poly E t,
      E.outputs (t + 1) i = α • ξ + (1 - α) • ξ' :=
  lemma_xi_xip E.normalizeRoundZero (normalizeRoundZero M) α t i hα
    (minimumBroadcastWeight_normalizeRoundZero E hmbw)

/-- The paper's difference decomposition, derived directly from actual-round
minimum broadcasting weight. The parallel component belongs to the direction
span of the original broadcasting values, not merely to an assumed witness set. -/
theorem lemma_differences_actualRounds
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}
    (E : AveragingExecution (V := V) n) (M : Round → Finset (Proc n))
    (α : ℝ) (t : Round) (i j : Proc n) (hα : 0 < α)
    (hmbw : MinimumBroadcastWeightActualRounds E M α) :
    ∃ uParallel ∈ vectorSpan ℝ (ValuesOn E t (M (t + 1))),
      ∃ uRes ∈ PaperFormalization.diffSet (Poly E t),
        E.outputs (t + 1) i - E.outputs (t + 1) j =
          α • uParallel + (1 - α) • uRes := by
  obtain ⟨u, hu, v, hv, hout⟩ := lemma_differences E M α t i j
    (lemma_xi_xip_actualRounds E M α t i hα hmbw)
    (lemma_xi_xip_actualRounds E M α t j hα hmbw)
  obtain ⟨x, hx, y, hy, rfl⟩ := hu
  refine ⟨x - y, ?_, v, hv, hout⟩
  exact vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
    (convexHull_subset_affineSpan (𝕜 := ℝ) (s := ValuesOn E t (M (t + 1))) hx)
    (convexHull_subset_affineSpan (𝕜 := ℝ) (s := ValuesOn E t (M (t + 1))) hy)

/-- Half-space attraction without a broadcasting or weight obligation at the
unused round-zero graph slot. -/
theorem lemma_halfspace_zone_actualRounds
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
    (E : AveragingExecution (V := V) n) (M : Round → Finset (Proc n))
    (α : ℝ) (t : Round) (q v : V) (hα : 0 < α) (hv : v ≠ 0)
    (hmbw : MinimumBroadcastWeightActualRounds E M α)
    (hprev : Values E t ∩ {h : V | inner ℝ (h - q) v < 0} = ∅) :
    setDistTo (Values E (t + 1)) {h : V | inner ℝ (h - q) v < 0} ≥
      α * setDistTo (PolyOn E t (M (t + 1))) {h : V | inner ℝ (h - q) v < 0} :=
  lemma_halfspace_zone_paper E.normalizeRoundZero (normalizeRoundZero M) α t q v hα hv
    (minimumBroadcastWeight_normalizeRoundZero E hmbw) hprev

/-- The sharp multiplicative contraction statement, including zero initial
volume and `α = 1`. The necessary bound `α ≤ 1` is derived from stochasticity,
not assumed; broadcasting weights are required only on positive rounds. -/
theorem lemma_contract_actualRounds
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {n : ℕ} [NeZero n]
    (E : AveragingExecution (V := V) n) (M : Round → Finset (Proc n))
    (α : ℝ) (t : Round) (hα : 0 < α)
    (hmbw : MinimumBroadcastWeightActualRounds E M α)
    (hcard : (M (t + 1)).card ≤ Module.finrank ℝ V) :
    volume (Poly E (t + 1)) ≤
      ENNReal.ofReal (1 - α ^ Module.finrank ℝ V) * volume (Poly E t) :=
  lemma_contract_of_le_one E.normalizeRoundZero (normalizeRoundZero M) α t hα
    (minimumBroadcastWeight_le_one E.normalizeRoundZero (normalizeRoundZero M)
      (minimumBroadcastWeight_normalizeRoundZero E hmbw))
    (minimumBroadcastWeight_normalizeRoundZero E hmbw) hcard

/-- Thickness contraction with no unused round-zero broadcasting-set,
cardinality, or minimum-weight hypotheses. -/
theorem lemma_Delta_contraction_actualRounds
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} [NeZero n]
    (k : ℕ) (hk : 1 ≤ k)
    (E : AveragingExecution (V := V) n) (M : Round → Finset (Proc n))
    (α : ℝ) (hα : 0 < α) (hmbw : MinimumBroadcastWeightActualRounds E M α)
    (hcard : ∀ t, 0 < t → (M t).card ≤ k) :
    ∃ Pi : V →L[ℝ] V, IsStarProjection Pi ∧
      Module.finrank ℝ (LinearMap.ker (Pi : V →ₗ[ℝ] V)) ≤ k - 1 ∧
      ConvergesTo (fun t => thicknessAt Pi E t) 0 :=
  lemma_Delta_contraction k hk E.normalizeRoundZero (normalizeRoundZero M) α hα
    (minimumBroadcastWeight_normalizeRoundZero E hmbw)
    (normalizeRoundZero_all (f := M) (P := fun R => R.card ≤ k) hcard)

/-- The paper's first main theorem with exactly dimension `d - 1`, the volume
deadline, and hypotheses only on actual positive communication/update rounds. -/
theorem theorem_poss_exact_actualRounds
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {n : ℕ} [NeZero n]
    (hd : 1 ≤ Module.finrank ℝ V)
    (E : AveragingExecution (V := V) n) (M : Round → Finset (Proc n))
    (α : ℝ) (hα : 0 < α) (hmbw : MinimumBroadcastWeightActualRounds E M α)
    (hcard : ∀ t, 0 < t → (M t).card ≤ Module.finrank ℝ V) :
    (∃ W : AffineSubspace ℝ V,
      Module.finrank ℝ W.direction = Module.finrank ℝ V - 1 ∧
      (∀ i, ConvergesToSet (fun t => E.outputs t i) (W : Set V)) ∧
      (∀ i, ConvergesToSet (fun t => E.outputs t i) (Poly E 0))) ∧
    (∀ (ε : ℝ), 0 < ε → ∀ t : ℕ,
      (volume.real (Poly E 0) ≤ ε ∨
        (α ^ Module.finrank ℝ V)⁻¹ * Real.log (volume.real (Poly E 0) / ε) ≤ (t : ℝ)) →
      volume (Poly E t) ≤ ENNReal.ofReal ε) := by
  obtain ⟨⟨W, hdim, hconv, hvalid⟩, hrate⟩ := theorem_poss_actualRounds hd E M α hα hmbw hcard
  obtain ⟨F, hWF, hF⟩ := exists_affine_superspace_finrank W (hconv 0).1 hdim (Nat.sub_le _ _)
  refine ⟨⟨F, hF, fun i => convergesToSet_mono (hconv i) hWF, hvalid⟩, ?_⟩
  intro ε hε t ht
  rcases ht with hsmall | ht
  · have hfinite : volume (Poly E 0) ≠ ⊤ :=
      ((Set.finite_range (E.outputs 0)).isCompact_convexHull ℝ).measure_ne_top
    have hle : volume (Poly E 0) ≤ ENNReal.ofReal ε := by
      apply (ENNReal.toReal_le_toReal hfinite ENNReal.ofReal_ne_top).mp
      simpa [measureReal_def, ENNReal.toReal_ofReal hε.le] using hsmall
    exact (measure_mono (ModelLemmas.poly_antitone E (Nat.zero_le t))).trans hle
  · exact hrate ε hε t ht

end AsymptoticSubspace
