import AsymptoticSubspace
import Lean.Util.CollectAxioms

/-! Check the axioms of all project theorems and the main proof dependencies.
Run with `lake env lean CheckAxioms.lean` after `lake build`. -/

open Lean in
run_cmd do
  let env ← getEnv
  let names ← env.constants.foldM (init := #[]) fun names name info => do
    pure <| match info with
      | .thmInfo _ =>
        if (`AsymptoticSubspace).isPrefixOf (privateToUserName name) then names.push name else names
      | _ => names
  let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := state.axioms.filter fun name => !allowed.contains name
  unless unexpected.isEmpty do
    throwError "Unexpected axioms: {unexpected}"
  logInfo m!"Checked {names.size} project theorems: only propext, Classical.choice, and Quot.sound."
  let dependencies := fun name => (((CollectAxioms.collect name).run env).run {}).2.visited
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
