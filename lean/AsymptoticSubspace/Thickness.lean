module

public import AsymptoticSubspace.DefThickness

/-!
# Thickness of a set under a linear map

The definition in `DefThickness` is the diameter of the projected set. On a nonempty compact set,
`exists_thickness_eq_norm` and `norm_sub_le_thickness` identify it with the
maximum in Definition 16. The definition also applies to finite sets and
their convex hulls, with equality proved in `thickness_convexHull`.
-/

@[expose] public section

noncomputable section

namespace AsymptoticSubspace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma thickness_nonneg (P : V →L[ℝ] V) (X : Set V) :
    0 ≤ thickness P X := Metric.diam_nonneg

lemma norm_sub_le_thickness (P : V →L[ℝ] V) {X : Set V}
    (hX : IsCompact X) {x y : V} (hx : x ∈ X) (hy : y ∈ X) :
    ‖P (x - y)‖ ≤ thickness P X := by
  simpa [thickness, dist_eq_norm, map_sub] using
    Metric.dist_le_diam_of_mem (hX.image P.continuous).isBounded
      (Set.mem_image_of_mem P hx) (Set.mem_image_of_mem P hy)

lemma thickness_le (P : V →L[ℝ] V) {X : Set V} {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ x ∈ X, ∀ y ∈ X, ‖P (x - y)‖ ≤ c) :
    thickness P X ≤ c := by
  apply Metric.diam_le_of_forall_dist_le hc
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  simpa [dist_eq_norm, map_sub] using h x hx y hy

/-- On a nonempty compact set, thickness is attained by a pair of points. -/
lemma exists_thickness_eq_norm (P : V →L[ℝ] V) {X : Set V}
    (hX : IsCompact X) (hne : X.Nonempty) :
    ∃ x ∈ X, ∃ y ∈ X, thickness P X = ‖P (x - y)‖ := by
  have hc : Continuous (fun p : V × V => ‖P (p.1 - p.2)‖) :=
    (P.continuous.comp (continuous_fst.sub continuous_snd)).norm
  obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, hmax⟩ :=
    (hX.prod hX).exists_isMaxOn (hne.prod hne) hc.continuousOn
  refine ⟨x, hx, y, hy, le_antisymm ?_ (norm_sub_le_thickness P hX hx hy)⟩
  exact thickness_le P (norm_nonneg _) fun a ha b hb =>
    (isMaxOn_iff.mp hmax) (a, b) ⟨ha, hb⟩

lemma thickness_mono (P : V →L[ℝ] V) {X Y : Set V}
    (hY : IsCompact Y) (hXY : X ⊆ Y) : thickness P X ≤ thickness P Y := by
  exact thickness_le P (thickness_nonneg P Y) fun _ hx _ hy =>
    norm_sub_le_thickness P hY (hXY hx) (hXY hy)

/-- Taking a convex hull does not change thickness. -/
@[simp] lemma thickness_convexHull (P : V →L[ℝ] V) (X : Set V) :
    thickness P (convexHull ℝ X) = thickness P X := by
  change Metric.diam (P.toLinearMap '' convexHull ℝ X) = Metric.diam (P '' X)
  rw [P.toLinearMap.image_convexHull, convexHull_diam]
  rfl

/-- Definition 16: on a nonempty compact set, thickness is the maximum
of `‖P (x - y)‖`. This holds for all continuous linear maps, hence in
particular for the orthogonal projections in the paper. -/
theorem thickness_eq_max
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (P : V →L[ℝ] V) (X : Set V) (hX : IsCompact X) (hne : X.Nonempty) :
    ∃ x ∈ X, ∃ y ∈ X, thickness P X = ‖P (x - y)‖ ∧
      ∀ a ∈ X, ∀ b ∈ X, ‖P (a - b)‖ ≤ ‖P (x - y)‖ := by
  obtain ⟨x, hx, y, hy, hmax⟩ := exists_thickness_eq_norm P hX hne
  refine ⟨x, hx, y, hy, hmax, ?_⟩
  intro a ha b hb
  rw [← hmax]
  exact norm_sub_le_thickness P hX ha hb


end AsymptoticSubspace
