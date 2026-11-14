# Lean formalization

The entry point is [AsymptoticSubspace.lean](AsymptoticSubspace.lean).
The toolchain and Mathlib revision are pinned to v4.27.0. From this directory:

```sh
lake build
lake env lean CheckAxioms.lean
```

The second command checks the axioms of every project theorem and verifies the
main dependencies of the symmetrization and volume-convergence proofs.

## Notation and scope

The ambient space `V` is any finite-dimensional real inner product space;
`Module.finrank ℝ V` is the paper's dimension `d`. In particular, take
`V = EuclideanSpace ℝ (Fin d)` for the paper's Euclidean space. Processes are
indexed by `Fin n`, starting at zero rather than one. `[NeZero n]` requires at
least one process and includes the paper's assumption `n > 1`.

`E.outputs t i`, `ModelLemmas.Values E t`, and `ModelLemmas.Poly E t` are
`x_i(t)`, `X(t)`, and `P(t)`. An `AveragingExecution` consists of arbitrary
communication graphs, stochastic weights, and outputs satisfying the averaging
update. Quantification over these executions covers every averaging algorithm
and every initial configuration. It imposes no convergence of individual values.

The public statements below use hypotheses on positive communication rounds.
`AveragingExecution.ofActualRounds` in [ActualRounds.lean](AsymptoticSubspace/ActualRounds.lean)
constructs the internal execution from precisely those data, filling the unused
round-zero graph and weights without changing any outputs. In statements about
one update, Lean's `t + 1` is the paper's update round, with pre-update values at `t`.

`MinimumBroadcastWeightActualRounds E M α` requires broadcasting sets `M t`
and a lower bound `α` on each process's total weight from that set. It permits
time-varying sets and does not require individual weights to be positive.
`AlphaSafeActualRounds E α` instead bounds the weight of every received message.

`ConvergesToSet` means that the target is nonempty and the distance to it tends
to zero. The agreement statements below give an affine subspace of exactly the
specified dimension. `PaperComputationalModel.Algorithm` permits arbitrary
internal state with message-local updates; its impossibility theorem is not
restricted to averaging algorithms.

`volume` takes values in the extended nonnegative reals, whereas `volume.real`
is real-valued. The hulls are compact, so their volumes are finite. The limiting
hull statements use Hausdorff convergence and `Set.extremePoints` for vertices;
the finite generating set in their conclusions also establishes finiteness of
the vertex set.

## Results

Numbers refer to the manuscript. Declaration names are in the
`AsymptoticSubspace` namespace unless a further namespace is shown.

| Paper | Lean declaration | File |
| --- | --- | --- |
| Theorem 1: rooted graph products | `graphProduct_broadcastable_paper` | [PhysicalRelayRates](AsymptoticSubspace/PhysicalRelayRates.lean) |
| Theorem 2: impossibility | `PaperComputationalModel.impossibility` | [PaperComputationalModel](AsymptoticSubspace/PaperComputationalModel.lean) |
| Definition 3: minimum broadcasting weight | `MinimumBroadcastWeightActualRounds` | [ActualRounds](AsymptoticSubspace/ActualRounds.lean) |
| Lemma 4: distance to a half-space | `lemma_halfspace_dist` | [LemHalfspaceDistFormula](AsymptoticSubspace/LemHalfspaceDistFormula.lean) |
| Lemma 5: half-space attraction | `lemma_halfspace_zone_actualRounds` | [ActualRoundLemmas](AsymptoticSubspace/ActualRoundLemmas.lean) |
| Theorem 6: dimension reduction and volume deadline | `theorem_poss_exact_actualRounds` | [ActualRoundLemmas](AsymptoticSubspace/ActualRoundLemmas.lean) |
| Lemma 7: concave secant bounds | `lemma_concave_line` | [LemConcaveLine](AsymptoticSubspace/LemConcaveLine.lean) |
| Lemma 8: zero-endpoint secant bounds | `lemma_concave_line_zero` | [LemConcaveLineZero](AsymptoticSubspace/LemConcaveLineZero.lean) |
| Lemma 9: symmetric-body volumes | `PaperFormalization.lemma_volumes_geometric_paper` | [SymmetricBody](AsymptoticSubspace/SymmetricBody.lean) |
| Lemma 10: volume contraction | `lemma_contract_actualRounds` | [ActualRoundLemmas](AsymptoticSubspace/ActualRoundLemmas.lean) |
| Lemma 11: zero volume and a containing hyperplane | `lemma_convex_zero_hyperplane_exact` | [ExactHyperplane](AsymptoticSubspace/ExactHyperplane.lean) |
| Corollary 12: ordinary averaging | `ordinary_averaging_linear_convergence` | [PhysicalRelayRates](AsymptoticSubspace/PhysicalRelayRates.lean) |
| Corollary 12: relayed averaging and rate | `relayed_averaging_linear_convergence`, `relayed_averaging_linear_deadline` | [PhysicalRelayRates](AsymptoticSubspace/PhysicalRelayRates.lean) |
| Theorem 13: convergence onto dimension `k - 1` | `theorem_solving_exact_actualRounds` | [ActualRounds](AsymptoticSubspace/ActualRounds.lean) |
| Lemma 14: broadcasting/residual decomposition | `lemma_xi_xip_actualRounds` | [ActualRoundLemmas](AsymptoticSubspace/ActualRoundLemmas.lean) |
| Lemma 15: difference decomposition | `lemma_differences_actualRounds` | [ActualRoundLemmas](AsymptoticSubspace/ActualRoundLemmas.lean) |
| Definition 16: projection and thickness | `roundProjection_eq_orthogonal_vectorSpan`, `thicknessOn` | [DefThickness](AsymptoticSubspace/DefThickness.lean) |
| Lemma 17: accumulation of projections | `lemma_roundProjection_accumulation` | [LemAccumulationPoint](AsymptoticSubspace/LemAccumulationPoint.lean) |
| Lemma 18: continuity of thickness | `lemma_continuity`, `thickness_lipschitz` | [LemContinuity](AsymptoticSubspace/LemContinuity.lean) |
| Lemma 19: contraction of thickness | `lemma_Delta_contraction_actualRounds` | [ActualRoundLemmas](AsymptoticSubspace/ActualRoundLemmas.lean) |
| Corollary 20: characterization and safe averaging | `PaperComputationalModel.characterization`, `PaperComputationalModel.safe_averaging` | [PaperComputationalModel](AsymptoticSubspace/PaperComputationalModel.lean) |
| Theorem 21: limiting vertices under broadcastability | `theorem_limiting_vertices` | [ThmLimitingVertices](AsymptoticSubspace/ThmLimitingVertices.lean) |
| Corollary 22: limiting vertices under rootedness | `corollary_rooted_vertices` | [CorRootedVertices](AsymptoticSubspace/CorRootedVertices.lean) |

## Proof structure

For Lemma 10, [LemContract](AsymptoticSubspace/LemContract.lean) first handles
zero volume, unit broadcasting weight, and dimension one.
[HalfspaceSupport](AsymptoticSubspace/HalfspaceSupport.lean) applies Lemma 5 to
bound the new supporting levels.
[HyperplaneCoordinates](AsymptoticSubspace/HyperplaneCoordinates.lean) supplies
the rotation and translation, and
[AxialVolumeContraction](AsymptoticSubspace/AxialVolumeContraction.lean) combines
the symmetrization and concave-radius bounds. The two half-space estimates are
summed in [VolumeContractionCore](AsymptoticSubspace/VolumeContractionCore.lean).
[ThmPoss](AsymptoticSubspace/ThmPoss.lean) then proves Theorem 6 from the vanishing
volume of the nested hulls and Lemma 11.
[SimplexVolume](AsymptoticSubspace/SimplexVolume.lean) proves the determinant
formula used in Lemma 11: the coordinate simplex has volume `1 / d!`, and
linear change of variables gives the absolute determinant factor.

For Theorem 13, [LemDeltaContractionCore](AsymptoticSubspace/LemDeltaContractionCore.lean)
constructs the round projections and proves contraction towards a limiting
projection. The recurrence samples outputs after each selected update and uses
the paper's projection-change error, followed by the geometric-sum estimate.
[ThmSolvingCore](AsymptoticSubspace/ThmSolvingCore.lean) proves that the projected
hulls have a singleton intersection and identifies the affine fiber and its
exact distance formula. `roundProjection E M t` is the paper's `Π_(t+1)`.

The elementary polynomial reduction in
[GraphProducts](AsymptoticSubspace/GraphProducts.lean) uses the pigeonhole
principle to select a recurring root set. Its influence grows in the selected
rounds; identity graphs pad the omitted rounds when representing that product.

For Theorem 21, [LimitingVerticesCore](AsymptoticSubspace/LimitingVerticesCore.lean)
chooses a recurring broadcasting set and convergent configurations, identifies
the limiting hull, applies Lemma 14, and uses extremality to locate its vertices.
Corollary 22 samples ordinary averaging executions at block boundaries;
the effective weight bound is `α^L`. Corollary 12 treats arbitrary relayed
executions, including history-dependent weights, with weight bound `α` per
block-end update. [PhysicalRelaying](AsymptoticSubspace/PhysicalRelaying.lean)
proves that forwarding origin-labelled values produces exactly the incoming
origins in the product graph. Both Corollary 12 and Corollary 20 use the linear
graph-product bound of Theorem 1.
