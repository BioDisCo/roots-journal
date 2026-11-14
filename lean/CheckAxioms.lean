module

-- Proof bodies are needed to check the dependencies below.
import all AsymptoticSubspace.ActualRoundLemmas
import all AsymptoticSubspace.ActualRounds
import all AsymptoticSubspace.AffineDimension
import all AsymptoticSubspace.AveragingHulls
import all AsymptoticSubspace.AxialVolumeContraction
import all AsymptoticSubspace.BackwardCover
import all AsymptoticSubspace.BlockExecution
import all AsymptoticSubspace.BrunnMinkowski.Basic
import all AsymptoticSubspace.BrunnMinkowski.BrunnMinkowski
import all AsymptoticSubspace.BrunnMinkowski.PrekopaLeindler
import all AsymptoticSubspace.BrunnMinkowski.Weighted
import all AsymptoticSubspace.ComputationalModelCore
import all AsymptoticSubspace.ConcaveProfileIntegrability
import all AsymptoticSubspace.CorBound
import all AsymptoticSubspace.CorCharacterization
import all AsymptoticSubspace.CorRootedVertices
import all AsymptoticSubspace.DefComputationalModel
import all AsymptoticSubspace.DefMinimumBroadcastWeight
import all AsymptoticSubspace.DefThickness
import all AsymptoticSubspace.EqualNeighbor
import all AsymptoticSubspace.ExactDimension
import all AsymptoticSubspace.ExactHyperplane
import all AsymptoticSubspace.ExternalGraphBound
import all AsymptoticSubspace.GraphProducts
import all AsymptoticSubspace.HalfspaceSupport
import all AsymptoticSubspace.HalfspaceZoneProofCore
import all AsymptoticSubspace.HyperplaneCoordinates
import all AsymptoticSubspace.ImpossibilityProofCore
import all AsymptoticSubspace.LemAccumulationPoint
import all AsymptoticSubspace.LemConcaveLine
import all AsymptoticSubspace.LemConcaveLineZero
import all AsymptoticSubspace.LemContinuity
import all AsymptoticSubspace.LemContract
import all AsymptoticSubspace.LemConvexZeroHyperplane
import all AsymptoticSubspace.LemDeltaContraction
import all AsymptoticSubspace.LemDeltaContractionCore
import all AsymptoticSubspace.LemDifferences
import all AsymptoticSubspace.LemHalfspaceDistFormula
import all AsymptoticSubspace.LemHalfspaceZone
import all AsymptoticSubspace.LemVolumes
import all AsymptoticSubspace.LemXiXip
import all AsymptoticSubspace.LimitingVerticesCore
import all AsymptoticSubspace.LinearGraphBound
import all AsymptoticSubspace.ModelBridgeCore
import all AsymptoticSubspace.NestedHulls
import all AsymptoticSubspace.PaperComputationalModel
import all AsymptoticSubspace.PaperFormalizationCore
import all AsymptoticSubspace.PhysicalAveraging
import all AsymptoticSubspace.PhysicalRelayRates
import all AsymptoticSubspace.PhysicalRelaying
import all AsymptoticSubspace.SimplexVolume
import all AsymptoticSubspace.StatefulAlgorithms
import all AsymptoticSubspace.StrictCoverGrowth
import all AsymptoticSubspace.StrictRoundCounting
import all AsymptoticSubspace.StrictRoundWeights
import all AsymptoticSubspace.SymmetricBody
import all AsymptoticSubspace.Symmetrization
import all AsymptoticSubspace.SymmetrizationCoordinates
import all AsymptoticSubspace.TemporalAncestors
import all AsymptoticSubspace.Thickness
import all AsymptoticSubspace.ThmImposs
import all AsymptoticSubspace.ThmLimitingVertices
import all AsymptoticSubspace.ThmPoss
import all AsymptoticSubspace.ThmRooted
import all AsymptoticSubspace.ThmSolving
import all AsymptoticSubspace.ThmSolvingCore
import all AsymptoticSubspace.VariableRelaying
import all AsymptoticSubspace.VolumeContractionCore
import all AsymptoticSubspace.VolumeRateCore
import Lean.Util.CollectAxioms

/-! Check the axioms of all project theorems and the main proof dependencies.
Run with `lake env lean CheckAxioms.lean` after `lake build`. -/

open Lean in
/-- Follow project declarations through their types and proof bodies.
Library declarations are audited by `collectAxioms`, but need not be traversed
when checking the paper's sequence of project lemmas. -/
private partial def projectDependencies (env : Environment) (name : Name) :
    StateM NameSet Unit := do
  if (← get).contains name then return
  modify (·.insert name)
  unless (`AsymptoticSubspace).isPrefixOf (privateToUserName name) do return
  let some info := env.find? name | return
  info.type.getUsedConstants.forM (projectDependencies env)
  if let some value := info.value? (allowOpaque := true) then
    value.getUsedConstants.forM (projectDependencies env)

open Lean in
run_cmd do
  let env ← getEnv
  let names ← env.constants.foldM (init := #[]) fun names name info => do
    pure <| match info with
      | .thmInfo _ =>
        if (`AsymptoticSubspace).isPrefixOf (privateToUserName name) then names.push name else names
      | _ => names
  unless !names.isEmpty do
    throwError "No project theorems were found"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    let unexpected := (← collectAxioms name).filter fun ax => !allowed.contains ax
    unless unexpected.isEmpty do
      throwError "Unexpected axioms in {name}: {unexpected}"
  logInfo m!"Checked {names.size} project theorems: only propext, Classical.choice, and Quot.sound."
  let dependencies := fun name => (projectDependencies env name).run {} |>.2
  unless (dependencies ``AsymptoticSubspace.thickness_eq_max).contains
      ``AsymptoticSubspace.exists_thickness_eq_norm do
    throwError "Definition 16 does not establish attainment on compact sets"
  let thicknessContraction := dependencies
    ``AsymptoticSubspace.lemma_Delta_contraction_actualRounds
  for name in #[``AsymptoticSubspace.thickness,
      ``AsymptoticSubspace.ModelLemmas.thickness_eq_thicknessOn,
      ``AsymptoticSubspace.lemma_continuity] do
    unless thicknessContraction.contains name do
      throwError "Lemma 19 does not use the compact-set thickness development: {name}"
  unless (dependencies ``AsymptoticSubspace.ThmSolving.projected_poly_diam).contains
      ``AsymptoticSubspace.thickness_convexHull do
    throwError "The projected-hull diameter does not use convex-hull invariance"
  logInfo "Checked compact-set thickness, its finite computation, and convex-hull invariance."
  let vertices := dependencies ``AsymptoticSubspace.theorem_limiting_vertices
  for name in #[``AsymptoticSubspace.LimitingVertices.exists_broadcasting_subsequence,
      ``AsymptoticSubspace.LimitingVertices.inter_eq_convexHull,
      ``AsymptoticSubspace.lemma_xi_xip_actualRounds,
      ``AsymptoticSubspace.LimitingVertices.limit_decomposition,
      ``AsymptoticSubspace.LimitingVertices.vertex_mem_broadcasting_hull] do
    unless vertices.contains name do
      throwError "Theorem 21 does not use the manuscript's vertex argument: {name}"
  let rootedVertices := dependencies ``AsymptoticSubspace.corollary_rooted_vertices
  for name in #[``AsymptoticSubspace.theorem_limiting_vertices,
      ``AsymptoticSubspace.ComputationalModel.blockExecution_safe,
      ``AsymptoticSubspace.sharpRootedBroadcastBound] do
    unless rootedVertices.contains name do
      throwError "Corollary 22 does not use the rooted-to-broadcastable reduction: {name}"
  logInfo "Checked the subsequence, decomposition, and vertex arguments of Theorem 21 and Corollary 22."
  let contraction := dependencies ``AsymptoticSubspace.lemma_contract_of_le_one
  for name in #[``AsymptoticSubspace.ModelLemmas.lemma_halfspace_zone,
      ``AsymptoticSubspace.PaperFormalization.sectionRadius_concave,
      ``AsymptoticSubspace.PaperFormalization.lemma_volumes_of_convex_body] do
    unless contraction.contains name do
      throwError "Volume contraction does not use {name}"
  let convergence := dependencies ``AsymptoticSubspace.theorem_poss
  unless convergence.contains ``AsymptoticSubspace.volume_tendsto_zero &&
      convergence.contains ``AsymptoticSubspace.lemma_convex_zero_hyperplane_exact do
    throwError "The first convergence theorem does not use the volume/hyperplane argument"
  for name in #[``AsymptoticSubspace.ThmSolving.theorem_solving,
      ``AsymptoticSubspace.lemma_Delta_contraction] do
    if convergence.contains name then
      throwError "The first convergence theorem depends on the later projection proof: {name}"
  logInfo "Checked the symmetrization and volume-convergence proof dependencies."
  for name in #[``AsymptoticSubspace.ordinary_averaging_linear_convergence,
      ``AsymptoticSubspace.relayed_averaging_linear_convergence] do
    let deps := dependencies name
    unless deps.contains ``AsymptoticSubspace.theorem_poss &&
        deps.contains ``AsymptoticSubspace.sharpRootedBroadcastBound do
      throwError "Corollary 12 does not use the volume theorem and linear graph bound: {name}"
    if deps.contains ``AsymptoticSubspace.lemma_Delta_contraction then
      throwError "Corollary 12 depends on the later projection proof: {name}"
  unless (dependencies ``AsymptoticSubspace.PaperComputationalModel.safe_averaging).contains
      ``AsymptoticSubspace.sharpRootedBroadcastBound do
    throwError "Corollary 20 does not use the linear graph bound"
  logInfo "Checked the proof dependencies of Corollaries 12 and 20."
  let hyperplane := dependencies
    ``AsymptoticSubspace.PaperFormalization.lemma_convex_zero_hyperplane
  unless hyperplane.contains ``AsymptoticSubspace.SimplexVolume.volume_simplex do
    throwError "Lemma 11 does not use the determinant/factorial simplex-volume formula"
  let projection := dependencies ``AsymptoticSubspace.ThmSolving.theorem_solving
  for name in #[``AsymptoticSubspace.ThmSolving.projected_poly_inter_eq_singleton,
      ``AsymptoticSubspace.ThmSolving.projection_fiber_distance,
      ``AsymptoticSubspace.perturbed_geometric_unroll] do
    unless projection.contains name do
      throwError "The projection convergence proof does not use {name}"
  unless (dependencies
      ``AsymptoticSubspace.ComputationalModel.graphProduct_broadcastable_polynomial).contains
      ``Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to do
    throwError "The elementary polynomial graph reduction does not use the pigeonhole argument"
  logInfo "Checked the simplex, nested projected hull, geometric-sum, and pigeonhole dependencies."
