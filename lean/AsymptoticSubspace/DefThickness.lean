-- TeX label: def:thickness
module

public import AsymptoticSubspace.ComputationalModelCore

/-!
# Definition 16: round projections and thickness

`roundProjection E M t` is the paper's `Π_(t+1)`; its direction space is
spanned by differences of the broadcasting values at time `t`.
`thickness P X` is `Δ_P(X)`. On nonempty compact sets, `thickness_eq_max`
in `Thickness.lean` proves that the projected diameter is exactly the
maximum of `‖P (x - y)‖` used in the paper.
-/

@[expose] public section

noncomputable section

namespace AsymptoticSubspace

open ComputationalModel

section RoundProjection

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {n : ℕ}

/-- Direction space of the broadcasting values before update `t + 1`. -/
def diffSubmodule
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (t : Round) : Submodule ℝ V :=
  Submodule.span ℝ
    (Set.range (fun p : M (t + 1) × M (t + 1) => E.outputs t p.1.1 - E.outputs t p.2.1))

/-- Definition 16: the paper's `Π_(t+1)`, projecting onto the orthogonal
complement of the direction space of the broadcasting values. -/
def roundProjection
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (t : Round) : V →L[ℝ] V :=
  (diffSubmodule E M t)ᗮ.starProjection

end RoundProjection

section Thickness

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The paper's `Δ_P(X)`: the diameter of the image of `X` under `P`. -/
def thickness (P : V →L[ℝ] V) (X : Set V) : ℝ :=
  Metric.diam (P '' X)

end Thickness

end AsymptoticSubspace
