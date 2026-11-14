-- TeX label: cor:bound
module

public import AsymptoticSubspace.ThmPoss
public import AsymptoticSubspace.ThmRooted
public import AsymptoticSubspace.EqualNeighbor

@[expose] public section

noncomputable section

namespace AsymptoticSubspace

open ComputationalModel ModelLemmas MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {n : ℕ} [NeZero n]

/-- Semantics of bounded message relaying followed by an averaging update.
`averaging` updates once per block; its graph is the product of the physical graphs.
The public output is held constant while the next block's messages are relayed. -/
structure RelayingExecution (G : Round → CommGraph n) (L : ℕ) where
  averaging : AveragingExecution (V := V) n
  graphs_eq : ∀ t, averaging.graphs t = graphProduct G ((t - 1) * L) L

namespace RelayingExecution

def outputs {G : Round → CommGraph n} {L : ℕ}
    (R : RelayingExecution (V := V) G L) (t : ℕ) : Proc n → V :=
  R.averaging.outputs (t / L)

def poly {G : Round → CommGraph n} {L : ℕ}
    (R : RelayingExecution (V := V) G L) (t : ℕ) : Set V :=
  convexHull ℝ (Set.range (R.outputs t))

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [NeZero n] in
lemma convergence {G : Round → CommGraph n} {L : ℕ}
    (R : RelayingExecution (V := V) G L) (hL : 0 < L) {S : Set V} {i : Proc n}
    (h : ConvergesToSet (fun t => R.averaging.outputs t i) S) :
    ConvergesToSet (fun t => R.outputs t i) S := by
  refine ⟨h.1, fun ε hε => ?_⟩
  obtain ⟨T, hT⟩ := h.2 ε hε
  exact ⟨T * L, fun t ht => hT (t / L) ((Nat.le_div_iff_mul_le hL).mpr ht)⟩

end RelayingExecution

/-- Relayed equal-neighbor averaging, defined on the actual product graphs. -/
def relayedEqualNeighbor (G : Round → CommGraph n) (L : ℕ) (init : Proc n → V) :
    RelayingExecution (V := V) G L where
  averaging := equalNeighborExecution (fun t => graphProduct G ((t - 1) * L) L) init
  graphs_eq _ := rfl

omit [MeasurableSpace V] [BorelSpace V] in
/-- Relaying preserves the general `k - 1` agreement result, not just the
one-dimension reduction used in the quantitative corollary. -/
theorem theorem_relayed_solving
    (k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ Module.finrank ℝ V)
    (G : Round → CommGraph n) (L : ℕ) (hL : 0 < L)
    (hblocks : ∀ start, IsKBroadcastable (graphProduct G start L) k)
    (R : RelayingExecution (V := V) G L)
    (α : ℝ) (hα : 0 < α) (hsafe : AlphaSafe R.averaging α) :
    ∃ W : AffineSubspace ℝ V,
      Module.finrank ℝ W.direction ≤ k - 1 ∧
      (∀ i, ConvergesToSet (fun t => R.outputs t i) (W : Set V)) ∧
      (∀ i, ConvergesToSet (fun t => R.outputs t i) (R.poly 0)) := by
  classical
  choose M hcard hM using fun t => hblocks ((t - 1) * L)
  have hmbw : MinimumBroadcastWeight R.averaging M α :=
    alphaSafe_implies_minimumBroadcastWeight R.averaging M α hsafe (fun t => by
      rw [R.graphs_eq t]
      exact hM t)
  obtain ⟨W, hdim, hconv, hvalid⟩ := ThmSolving.theorem_solving (Module.finrank ℝ V) k
    hkd hk R.averaging M α hα hmbw hcard rfl
  refine ⟨W, hdim, fun i => R.convergence hL (hconv i), ?_⟩
  intro i
  simpa [RelayingExecution.poly, RelayingExecution.outputs] using R.convergence hL (hvalid i)

/-- The speed-up corollary for any verified broadcasting-block length.
Positivity of `α` and integer rounding of the physical-round deadline are explicit. -/
theorem corollary_bound
    (hd : 1 ≤ Module.finrank ℝ V)
    (G : Round → CommGraph n) (L : ℕ) (hL : 0 < L)
    (hblocks : ∀ start, IsKBroadcastable (graphProduct G start L) (Module.finrank ℝ V))
    (R : RelayingExecution (V := V) G L)
    (α : ℝ) (hα : 0 < α) (hsafe : AlphaSafe R.averaging α) :
    (∃ W : AffineSubspace ℝ V,
      Module.finrank ℝ W.direction ≤ Module.finrank ℝ V - 1 ∧
      (∀ i, ConvergesToSet (fun t => R.outputs t i) (W : Set V)) ∧
      (∀ i, ConvergesToSet (fun t => R.outputs t i) (R.poly 0))) ∧
    (∀ (ε : ℝ), 0 < ε → ∀ t : ℕ,
      ⌈(α ^ Module.finrank ℝ V)⁻¹ * Real.log (volume.real (R.poly 0) / ε)⌉₊ * L ≤ t →
      volume (R.poly t) ≤ ENNReal.ofReal ε) := by
  classical
  choose M hcard hM using fun t => hblocks ((t - 1) * L)
  have hmbw : MinimumBroadcastWeight R.averaging M α :=
    alphaSafe_implies_minimumBroadcastWeight R.averaging M α hsafe (fun t => by
      rw [R.graphs_eq t]
      exact hM t)
  obtain ⟨⟨W, hdim, hconv, hvalid⟩, hrate⟩ := theorem_poss hd R.averaging M α hα hmbw hcard
  refine ⟨⟨W, hdim, fun i => R.convergence hL (hconv i), ?_⟩, ?_⟩
  · intro i
    simpa [RelayingExecution.poly, RelayingExecution.outputs] using R.convergence hL (hvalid i)
  · intro ε hε t ht
    apply hrate ε hε (t / L)
    have hnat := (Nat.le_div_iff_mul_le hL).mpr ht
    simp only [RelayingExecution.poly, RelayingExecution.outputs, Nat.zero_div] at hnat
    exact (Nat.le_ceil _).trans (by exact_mod_cast hnat)

/-- The physical-round geometric estimate: outputs only change after each
complete block, whose final communication round also performs the update. -/
theorem relayed_volume_geometric_bound
    (G : Round → CommGraph n) (L : ℕ)
    (hblocks : ∀ start, IsKBroadcastable (graphProduct G start L) (Module.finrank ℝ V))
    (R : RelayingExecution (V := V) G L)
    (α : ℝ) (hα : 0 < α) (hsafe : AlphaSafe R.averaging α) (t : ℕ) :
    volume.real (R.poly t) ≤
      (1 - α ^ Module.finrank ℝ V) ^ (t / L) * volume.real (R.poly 0) := by
  classical
  choose M hcard hM using fun t => hblocks ((t - 1) * L)
  have hmbw : MinimumBroadcastWeight R.averaging M α :=
    alphaSafe_implies_minimumBroadcastWeight R.averaging M α hsafe (fun t => by
      rw [R.graphs_eq t]
      exact hM t)
  simpa [RelayingExecution.poly, RelayingExecution.outputs] using
    volume_geometric_bound R.averaging M α hα hmbw hcard (t / L)

/-- A fully proved instance of the speed-up result using the elementary
polynomial rooted-to-broadcastable reduction. -/
theorem corollary_bound_polynomial
    (hd : 1 ≤ Module.finrank ℝ V) (hdn : Module.finrank ℝ V ≤ n)
    (G : Round → CommGraph n) (hroot : ∀ t, IsKRooted (G t) (Module.finrank ℝ V))
    (R : RelayingExecution (V := V) G (n ^ (Module.finrank ℝ V + 1)))
    (α : ℝ) (hα : 0 < α) (hsafe : AlphaSafe R.averaging α) :
    ∀ (ε : ℝ), 0 < ε → ∀ t : ℕ,
      ⌈(α ^ Module.finrank ℝ V)⁻¹ * Real.log (volume.real (R.poly 0) / ε)⌉₊ *
        n ^ (Module.finrank ℝ V + 1) ≤ t →
      volume (R.poly t) ≤ ENNReal.ofReal ε := by
  exact (corollary_bound hd G _ (pow_pos (Nat.pos_of_ne_zero (NeZero.ne n)) _)
    (fun start => graphProduct_broadcastable_polynomial G start _ hd hdn hroot)
    R α hα hsafe).2

end AsymptoticSubspace
