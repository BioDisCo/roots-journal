-- Internal proof infrastructure for `ThmLimitingVertices.lean`.
module

public import AsymptoticSubspace.ActualRoundLemmas
public import AsymptoticSubspace.NestedHulls

/-!
# Theorem 21: the limiting hull has at most k vertices

Notation correspondence:
* `E.outputs t i` is `x_i(t)`, and `Poly E t` is `P(t)`.
* `⋂ t, Poly E t` is `P*`.
* `S` is the recurring broadcasting set `M^∞`.
* `σ r` is the pre-update round `τ_r - 1`; its update is at `σ r + 1`.
* `xStar i` is `x_i*`, `range xStar` is `X*`, and `xStar '' ↑S` is `X*_{M^∞}`.

After the compactness helpers, the proof follows the manuscript's order:
`exists_broadcasting_subsequence`, `inter_eq_convexHull`, `hull_decomposition`,
`limit_decomposition`, `vertex_mem_broadcasting_hull`, and the final assembly
`limiting_vertices_core`. The helpers `poly_limit_nonempty` and
`poly_tendsto_limit` give nonemptiness and Hausdorff convergence of the nested hulls.
-/

@[expose] public section

noncomputable section

namespace AsymptoticSubspace.LimitingVertices

open ComputationalModel ModelLemmas Set Filter
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {n : ℕ} [NeZero n]

/-- Write a point of a finite convex hull with one coefficient per index,
including when distinct indices represent the same point. -/
lemma exists_coefficients {ι : Type*} [Fintype ι] (x : ι → V) {z : V}
    (hz : z ∈ convexHull ℝ (range x)) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
      (∑ i, w i • x i) = z := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at hz
  obtain ⟨s, w, hw, hs, hz⟩ := hz
  refine ⟨fun i => if i ∈ s then w i else 0, ?_, ?_, ?_⟩
  · intro i
    dsimp only
    split_ifs with hi
    · exact hw i hi
    · exact le_rfl
  · simpa using hs
  · simpa [ite_smul, Finset.affineCombination_eq_linear_combination _ _ _ hs] using hz

/-- The coefficient-subsequence argument used for the reverse inclusion in the
limiting-hull proof and for the broadcasting component of a vertex. -/
lemma mem_convexHull_of_tendsto {ι : Type*} [Finite ι]
    (x : ℕ → ι → V) (xStar : ι → V) (z : ℕ → V) (zStar : V)
    (hx : ∀ i, Tendsto (fun r => x r i) atTop (𝓝 (xStar i)))
    (hz : Tendsto z atTop (𝓝 zStar))
    (hmem : ∀ r, z r ∈ convexHull ℝ (range (x r))) :
    zStar ∈ convexHull ℝ (range xStar) := by
  classical
  let := Fintype.ofFinite ι
  choose w hw hs heq using fun r => exists_coefficients (x r) (hmem r)
  have hcompact : IsCompact {w : ι → ℝ | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} := by
    have h := isCompact_range (continuous_pi (fun i : ι =>
      Convexity.StdSimplex.continuous_weights_apply ℝ i))
    simpa only [Convexity.StdSimplex.range_toFun_comp_weights, Set.iInter_ofPred,
      ← Set.ofPred_and] using h
  obtain ⟨wStar, hwStar, φ, hφ, hwlim⟩ :=
    hcompact.tendsto_subseq (fun r => ⟨hw r, hs r⟩)
  have hsum : Tendsto (fun r => ∑ i, w (φ r) i • x (φ r) i) atTop
      (𝓝 (∑ i, wStar i • xStar i)) := by
    apply tendsto_finsetSum
    intro i _
    exact ((tendsto_pi_nhds.mp hwlim) i).smul ((hx i).comp hφ.tendsto_atTop)
  have heqStar : (∑ i, wStar i • xStar i) = zStar :=
    tendsto_nhds_unique (by simpa only [heq, Function.comp_def] using hsum)
      (hz.comp hφ.tendsto_atTop)
  exact mem_convexHull_of_exists_fintype wStar xStar hwStar.1 hwStar.2
    (fun i => mem_range_self i) heqStar

/-- A limit of points in hulls at unbounded rounds belongs to every earlier
hull. This is the closedness argument displayed in the manuscript. -/
lemma mem_inter_of_tendsto (E : AveragingExecution (V := V) n)
    (σ : ℕ → ℕ) (hσ : Tendsto σ atTop atTop)
    (z : ℕ → V) (zStar : V) (hz : Tendsto z atTop (𝓝 zStar))
    (hmem : ∀ r, z r ∈ Poly E (σ r)) :
    zStar ∈ ⋂ t, Poly E t := by
  apply mem_iInter.mpr
  intro t
  apply (poly_compact E t).isClosed.mem_of_tendsto hz
  filter_upwards [hσ.eventually (eventually_ge_atTop t)] with r hr
  exact ModelLemmas.poly_antitone E hr (hmem r)

/-- Choose one recurring broadcasting set and a common convergent subsequence
of the configurations immediately before its rounds. Here `σ r = τ_r - 1`. -/
lemma exists_broadcasting_subsequence (E : AveragingExecution (V := V) n)
    (M : ℕ → Finset (Proc n)) (k : ℕ)
    (hcard : ∀ t, 0 < t → (M t).card ≤ k) :
    ∃ (S : Finset (Proc n)) (σ : ℕ → ℕ) (xStar : Proc n → V),
      S.card ≤ k ∧ StrictMono σ ∧ (∀ r, M (σ r + 1) = S) ∧
      ∀ i, Tendsto (fun r => E.outputs (σ r) i) atTop (𝓝 (xStar i)) := by
  classical
  have hf : ∃ᶠ t in atTop, ∃ S : Finset (Proc n), M (t + 1) = S :=
    (Eventually.of_forall (fun t => ⟨M (t + 1), rfl⟩)).frequently
  obtain ⟨S, hS⟩ := frequently_exists.mp hf
  obtain ⟨ρ, hρ, hM⟩ := extraction_of_frequently_atTop hS
  have hc := isCompact_univ_pi (fun _ : Proc n => poly_compact E 0)
  obtain ⟨xStar, _, φ, hφ, hx⟩ := hc.tendsto_subseq
    (x := fun r => E.outputs (ρ r)) (fun r i _ =>
      ModelLemmas.poly_antitone E (Nat.zero_le _) (ModelLemmas.output_mem_poly_self E _ i))
  refine ⟨S, ρ ∘ φ, xStar, ?_, hρ.comp hφ, fun r => hM (φ r), ?_⟩
  · rw [← hM 0]
    exact hcard _ (Nat.succ_pos _)
  · exact tendsto_pi_nhds.mp hx

/-- The limit hull is generated by the subsequential process limits
(Theorem 21, equation (16)). The inclusions follow the order of the paper. -/
lemma inter_eq_convexHull (E : AveragingExecution (V := V) n)
    (σ : ℕ → ℕ) (hσ : StrictMono σ) (xStar : Proc n → V)
    (hx : ∀ i, Tendsto (fun r => E.outputs (σ r) i) atTop (𝓝 (xStar i))) :
    (⋂ t, Poly E t) = convexHull ℝ (range xStar) := by
  symm -- First the superset inclusion, as in the paper.
  apply Subset.antisymm
  · -- (⊇) Every subsequential process limit lies in every closed hull P(t).
    apply convexHull_min
    · rintro _ ⟨i, rfl⟩
      exact mem_inter_of_tendsto E σ hσ.tendsto_atTop _ _ (hx i)
        (fun r => ModelLemmas.output_mem_poly_self E _ i)
    · exact convex_iInter (fun t => convex_convexHull ℝ (Values E t))
  · -- (⊆) Extract convergent coefficients for a fixed z ∈ P*.
    intro z hz
    exact mem_convexHull_of_tendsto (fun r => E.outputs (σ r)) xStar
      (fun _ => z) z hx tendsto_const_nhds (fun r => mem_iInter.mp hz (σ r))

omit [NeZero n] in
/-- Apply Lemma 14 (decomposition into broadcasting and residual components)
to the outputs in a convex representation of `v`,
then collect their broadcasting and residual components. -/
lemma hull_decomposition (E : AveragingExecution (V := V) n)
    (M : ℕ → Finset (Proc n)) (α : ℝ) (hα : 0 < α)
    (hmbw : MinimumBroadcastWeightActualRounds E M α)
    (t : ℕ) {v : V} (hv : v ∈ Poly E (t + 1)) :
    ∃ ξ ∈ PolyOn E t (M (t + 1)), ∃ ξ' ∈ Poly E t,
      v = α • ξ + (1 - α) • ξ' := by
  classical
  obtain ⟨w, hw, hs, heq⟩ := exists_coefficients (E.outputs (t + 1)) hv
  choose ξ hξ ξ' hξ' hout using fun i =>
    lemma_xi_xip_actualRounds E M α t i hα hmbw
  refine ⟨∑ i, w i • ξ i, ?_, ∑ i, w i • ξ' i, ?_, ?_⟩
  · exact (convex_convexHull ℝ _).sum_mem (fun i _ => hw i) hs (fun i _ => hξ i)
  · exact (convex_convexHull ℝ _).sum_mem (fun i _ => hw i) hs (fun i _ => hξ' i)
  · rw [← heq]
    simp_rw [hout, smul_add, smul_comm (w _) α, smul_comm (w _) (1 - α)]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum]

/-- Pass the broadcasting/residual decomposition to the limit along a common
subsequence, retaining the fixed weight (Theorem 21, equations (18)–(19)). -/
lemma limit_decomposition (E : AveragingExecution (V := V) n)
    (M : ℕ → Finset (Proc n)) (α : ℝ) (hα : 0 < α)
    (hmbw : MinimumBroadcastWeightActualRounds E M α)
    (S : Finset (Proc n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (hM : ∀ r, M (σ r + 1) = S) (xStar : Proc n → V)
    (hx : ∀ i, Tendsto (fun r => E.outputs (σ r) i) atTop (𝓝 (xStar i)))
    {v : V} (hv : v ∈ ⋂ t, Poly E t) :
    ∃ ξ ∈ convexHull ℝ (xStar '' (S : Set (Proc n))),
      ∃ ξ' ∈ ⋂ t, Poly E t, v = α • ξ + (1 - α) • ξ' := by
  classical
  choose ξ hξ ξ' hξ' heq using fun r =>
    hull_decomposition E M α hα hmbw (σ r) (mem_iInter.mp hv _)
  have hξS (r : ℕ) : ξ r ∈ PolyOn E (σ r) S := by
    simpa only [hM r] using hξ r
  have hξP (r : ℕ) : ξ r ∈ Poly E (σ r) :=
    convexHull_mono (image_subset_range _ _) (hξS r)
  obtain ⟨p, _, φ, hφ, hp⟩ := ((poly_compact E 0).prod (poly_compact E 0)).tendsto_subseq
    (x := fun r => (ξ r, ξ' r)) (fun r =>
      ⟨ModelLemmas.poly_antitone E (Nat.zero_le _) (hξP r),
       ModelLemmas.poly_antitone E (Nat.zero_le _) (hξ' r)⟩)
  have hleft : Tendsto (ξ ∘ φ) atTop (𝓝 p.1) := (continuous_fst.tendsto p).comp hp
  have hright : Tendsto (ξ' ∘ φ) atTop (𝓝 p.2) := (continuous_snd.tendsto p).comp hp
  refine ⟨p.1, ?_, p.2, ?_, ?_⟩
  · have hrange (f : Proc n → V) : range (fun i : S => f i) = f '' (S : Set (Proc n)) := by
      ext z
      simp
    rw [← hrange xStar]
    apply mem_convexHull_of_tendsto (fun r (i : S) => E.outputs (σ (φ r)) i)
      (fun i : S => xStar i) (ξ ∘ φ) p.1
      (fun i => (hx i).comp hφ.tendsto_atTop) hleft
    intro r
    rw [hrange]
    exact hξS (φ r)
  · exact mem_inter_of_tendsto E (σ ∘ φ) (hσ.comp hφ).tendsto_atTop
      (ξ' ∘ φ) p.2 hright (fun r => hξ' (φ r))
  · have hlim := (hleft.const_smul α).add (hright.const_smul (1 - α))
    have hlim' : Tendsto (fun _ : ℕ => v) atTop (𝓝 (α • p.1 + (1 - α) • p.2)) := by
      simpa only [Function.comp_apply, ← heq] using hlim
    exact tendsto_nhds_unique tendsto_const_nhds hlim'

/-- A vertex cannot retain a nontrivial residual component. The endpoint
`α = 1` is included; `α ≤ 1` follows from the stochastic weights. -/
lemma vertex_mem_broadcasting_hull (E : AveragingExecution (V := V) n)
    (M : ℕ → Finset (Proc n)) (α : ℝ) (hα : 0 < α)
    (hmbw : MinimumBroadcastWeightActualRounds E M α)
    (S : Finset (Proc n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (hM : ∀ r, M (σ r + 1) = S) (xStar : Proc n → V)
    (hx : ∀ i, Tendsto (fun r => E.outputs (σ r) i) atTop (𝓝 (xStar i)))
    (hHull : (⋂ t, Poly E t) = convexHull ℝ (range xStar)) :
    (⋂ t, Poly E t).extremePoints ℝ ⊆ convexHull ℝ (xStar '' (S : Set (Proc n))) := by
  intro v hv
  obtain ⟨ξ, hξ, ξ', hξ', heq⟩ := limit_decomposition E M α hα hmbw S σ hσ hM xStar hx hv.1
  have hξP : ξ ∈ ⋂ t, Poly E t := by
    rw [hHull]
    exact convexHull_mono (image_subset_range _ _) hξ
  have hα1 : α ≤ 1 := minimumBroadcastWeight_le_one E.normalizeRoundZero
    (normalizeRoundZero M) (minimumBroadcastWeight_normalizeRoundZero E hmbw)
  have hvξ : v = ξ := by
    by_contra hne
    have hαlt : α < 1 := lt_of_le_of_ne hα1 (by
      intro he
      apply hne
      simpa [he] using heq)
    have hsegment : v ∈ openSegment ℝ ξ ξ' :=
      ⟨α, 1 - α, hα, sub_pos.mpr hαlt, by ring, heq.symm⟩
    -- The definition of an extreme point forces the segment endpoint to be v.
    have hendpoint : ξ = v := hv.2 hξP hξ' hsegment
    exact hne hendpoint.symm
  simpa only [hvξ] using hξ

/-- Assemble the finite-hull and vertex arguments in the order of the paper.
The conclusion also explicitly bounds the set of extreme points (vertices). -/
theorem limiting_vertices_core (E : AveragingExecution (V := V) n)
    (M : ℕ → Finset (Proc n)) (k : ℕ) (α : ℝ) (hα : 0 < α)
    (hmbw : MinimumBroadcastWeightActualRounds E M α)
    (hcard : ∀ t, 0 < t → (M t).card ≤ k) :
    ∃ X : Finset V, X.card ≤ k ∧ (⋂ t, Poly E t) = convexHull ℝ (X : Set V) ∧
      ((⋂ t, Poly E t).extremePoints ℝ).ncard ≤ k := by
  classical
  -- Choose M^∞ and the common subsequence of pre-update configurations.
  obtain ⟨S, σ, xStar, hS, hσ, hM, hx⟩ := exists_broadcasting_subsequence E M k hcard
  -- Identify the limit hull: P* = poly(X*).
  have hHull := inter_eq_convexHull E σ hσ xStar hx
  -- Every vertex of P* belongs to poly(X*_{M^∞}).
  have hvertices := vertex_mem_broadcasting_hull E M α hα hmbw S σ hσ hM xStar hx hHull
  have hfinite : ((⋂ t, Poly E t).extremePoints ℝ).Finite := by
    rw [hHull]
    exact (finite_range xStar).subset extremePoints_convexHull_subset
  have hgen : convexHull ℝ ((⋂ t, Poly E t).extremePoints ℝ) = ⋂ t, Poly E t := by
    -- The paper uses that a finite convex hull is generated by its vertices.
    -- Mathlib supplies the compact-convex version with closure (Krein–Milman);
    -- finiteness of the vertices lets us remove that closure here.
    have hc : IsCompact (⋂ t, Poly E t) := by
      rw [hHull]
      exact (finite_range xStar).isCompact_convexHull ℝ
    have hconv : Convex ℝ (⋂ t, Poly E t) :=
      convex_iInter (fun t => convex_convexHull ℝ (Values E t))
    simpa only [(hfinite.isCompact_convexHull ℝ).isClosed.closure_eq] using
      closure_convexHull_extremePoints hc hconv
  have hsmall : (⋂ t, Poly E t) = convexHull ℝ (xStar '' (S : Set (Proc n))) := by
    apply Subset.antisymm
    · rw [← hgen]
      exact convexHull_min hvertices (convex_convexHull ℝ _)
    · rw [hHull]
      exact convexHull_mono (image_subset_range _ _)
  -- X*_{M^∞} has at most |M^∞| ≤ k distinct points, even if limits coincide.
  refine ⟨S.image xStar, (Finset.card_image_le).trans hS, ?_, ?_⟩
  · simpa only [Finset.coe_image] using hsmall
  · rw [hsmall]
    exact (ncard_le_ncard extremePoints_convexHull_subset (S.finite_toSet.image xStar)).trans
      ((ncard_image_le S.finite_toSet).trans (by simpa using hS))

end AsymptoticSubspace.LimitingVertices
