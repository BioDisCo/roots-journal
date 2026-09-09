import AsymptoticSubspace.CorBound
import AsymptoticSubspace.LinearGraphBound

noncomputable section

namespace AsymptoticSubspace

open ComputationalModel MeasureTheory

/-- Integer block length corresponding to the cited ITCS 2023 Theorem 32. -/
def linearBroadcastRounds (n : ℕ) : ℕ :=
  ⌈((Real.pi ^ 2 + 6) / 6) * (n : ℝ) + 1⌉₊

lemma linearBroadcastRounds_pos (n : ℕ) : 0 < linearBroadcastRounds n := by
  apply Nat.ceil_pos.mpr
  positivity

/-- The exact cited graph theorem, proved by `sharpRootedBroadcastBound` below. -/
def SharpRootedBroadcastBound (n : ℕ) : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ G : Round → CommGraph n,
    (∀ t, IsKRooted (G t) k) → ∀ start,
      IsKBroadcastable (graphProduct G start (linearBroadcastRounds n)) k

/-- The cited ITCS 2023 Theorem 32, with every graph and counting dependency
discharged in Lean. The integer ceiling is explicit. -/
theorem sharpRootedBroadcastBound (n : ℕ) : SharpRootedBroadcastBound n := by
  intro k _ G hroot start
  apply graphProduct_broadcastable_linear G start _ k hroot
  have hceil := Nat.le_ceil (((Real.pi ^ 2 + 6) / 6) * (n : ℝ) + 1)
  change ((Real.pi ^ 2 + 6) / 6) * (n : ℝ) <
    (⌈((Real.pi ^ 2 + 6) / 6) * (n : ℝ) + 1⌉₊ : ℝ) + 1
  linarith

/-- Compatibility interface accepting an explicit proof of the graph bound.
Use `corollary_bound_linear` for the unconditional paper-facing result. -/
theorem corollary_bound_linear_of_external
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {n : ℕ} [NeZero n] (hsharp : SharpRootedBroadcastBound n)
    (hd : 1 ≤ Module.finrank ℝ V)
    (G : Round → CommGraph n) (hroot : ∀ t, IsKRooted (G t) (Module.finrank ℝ V))
    (R : RelayingExecution (V := V) G (linearBroadcastRounds n))
    (α : ℝ) (hα : 0 < α) (hsafe : AlphaSafe R.averaging α) :
    ∀ (ε : ℝ), 0 < ε → ∀ t : ℕ,
      ⌈(α ^ Module.finrank ℝ V)⁻¹ * Real.log (volume.real (R.poly 0) / ε)⌉₊ *
        linearBroadcastRounds n ≤ t →
      volume (R.poly t) ≤ ENNReal.ofReal ε :=
  (corollary_bound hd G _ (linearBroadcastRounds_pos n)
    (hsharp _ hd G hroot) R α hα hsafe).2

/-- The sharp relaying deadline with no unproved external premise. -/
theorem corollary_bound_linear
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {n : ℕ} [NeZero n]
    (hd : 1 ≤ Module.finrank ℝ V)
    (G : Round → CommGraph n) (hroot : ∀ t, IsKRooted (G t) (Module.finrank ℝ V))
    (R : RelayingExecution (V := V) G (linearBroadcastRounds n))
    (α : ℝ) (hα : 0 < α) (hsafe : AlphaSafe R.averaging α) :
    ∀ (ε : ℝ), 0 < ε → ∀ t : ℕ,
      ⌈(α ^ Module.finrank ℝ V)⁻¹ * Real.log (volume.real (R.poly 0) / ε)⌉₊ *
        linearBroadcastRounds n ≤ t →
      volume (R.poly t) ≤ ENNReal.ofReal ε :=
  corollary_bound_linear_of_external (sharpRootedBroadcastBound n) hd G hroot R α hα hsafe

/-- The manuscript's geometric estimate with a sharp integer block length.
The final round of each block includes the averaging update; no extra round is added. -/
theorem corollary_bound_linear_geometric
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {n : ℕ} [NeZero n]
    (hd : 1 ≤ Module.finrank ℝ V)
    (G : Round → CommGraph n) (hroot : ∀ t, IsKRooted (G t) (Module.finrank ℝ V))
    (R : RelayingExecution (V := V) G (linearBroadcastRounds n))
    (α : ℝ) (hα : 0 < α) (hsafe : AlphaSafe R.averaging α) (t : ℕ) :
    volume.real (R.poly t) ≤
      (1 - α ^ Module.finrank ℝ V) ^ (t / linearBroadcastRounds n) *
        volume.real (R.poly 0) :=
  relayed_volume_geometric_bound G _ (sharpRootedBroadcastBound n _ hd G hroot) R α hα hsafe t

end AsymptoticSubspace
