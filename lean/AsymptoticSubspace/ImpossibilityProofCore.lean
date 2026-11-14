-- Static counterexample construction used by the arbitrary-state impossibility proof.
-- Theorem 2 is stated in `PaperComputationalModel.lean`.
module

public import AsymptoticSubspace.ModelBridgeCore

@[expose] public section

noncomputable section

namespace AsymptoticSubspace
namespace ModelLemmas

open Set
open ComputationalModel
open PaperFormalization

section ImpossibilityModel

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {n : Nat}

variable (N : ObliviousMessageAdversary n)
variable (s : Nat)

/-- Reachability-minimal node: every node that reaches it is also reached by it. -/
def IsReachabilityMinimal (G : CommGraph n) (r : Proc n) : Prop :=
  ∀ j : Proc n, Reachable G j r → Reachable G r j

/-- Finite set of all reachability-minimal nodes in `G`. -/
noncomputable def minimalReachers (G : CommGraph n) : Finset (Proc n) := by
  classical
  exact Finset.univ.filter (fun r => IsReachabilityMinimal (n := n) G r)

theorem mem_minimalReachers_iff (G : CommGraph n) (r : Proc n) :
    r ∈ minimalReachers (n := n) G ↔ IsReachabilityMinimal (n := n) G r := by
  classical
  simp [minimalReachers]

theorem exists_minimal_reacher_to
    (G : CommGraph n) (i : Proc n) :
    ∃ r : Proc n,
      IsReachabilityMinimal (n := n) G r ∧ Reachable G r i := by
  classical
  let S : Set (Proc n) := {j : Proc n | Reachable G j i}
  have hSfin : S.Finite := Set.toFinite S
  have hSne : S.Nonempty := ⟨i, Relation.ReflTransGen.refl⟩
  let : LE (Proc n) := ⟨fun a b => Reachable G a b⟩
  let : IsTrans (Proc n) (· ≤ ·) := ⟨fun _ _ _ => Relation.ReflTransGen.trans⟩
  obtain ⟨r, hrS, hrMin⟩ := hSfin.exists_minimal hSne
  refine ⟨r, ?_, hrS⟩
  intro j hjr
  have hjS : j ∈ S := Relation.ReflTransGen.trans hjr hrS
  exact hrMin hjS hjr

theorem isRootSet_minimalReachers (G : CommGraph n) :
    IsRootSet G (minimalReachers (n := n) G) := by
  intro i
  rcases exists_minimal_reacher_to (n := n) G i with ⟨r, hrMin, hri⟩
  refine ⟨r, ?_, hri⟩
  exact (mem_minimalReachers_iff (n := n) G r).2 hrMin

theorem isKRooted_of_card_minimalReachers_le
    (G : CommGraph n)
    (hcard : (minimalReachers (n := n) G).card ≤ s + 1) :
    IsKRooted G (s + 1) := by
  refine ⟨minimalReachers (n := n) G, hcard, ?_⟩
  exact isRootSet_minimalReachers (n := n) G

theorem lt_card_minimalReachers_of_not_kRooted
    (G : CommGraph n)
    (hnot : ¬ IsKRooted G (s + 1)) :
    s + 1 < (minimalReachers (n := n) G).card := by
  by_contra hle
  exact hnot (isKRooted_of_card_minimalReachers_le (n := n) (s := s) G (Nat.not_lt.mp hle))

/-- Bidirectional reachability (same SCC under reachability equivalence). -/
def MutualReachable (G : CommGraph n) (a b : Proc n) : Prop :=
  Reachable G a b ∧ Reachable G b a

/-- A canonical representative among reachability-minimal nodes of one SCC class. -/
def IsRepMinimal (G : CommGraph n) (r : Proc n) : Prop :=
  IsReachabilityMinimal (n := n) G r ∧
    ∀ r' : Proc n,
      IsReachabilityMinimal (n := n) G r' →
      MutualReachable (n := n) G r r' →
      r ≤ r'

/-- Finite set of canonical representatives of minimal SCC classes. -/
noncomputable def minimalClassReps (G : CommGraph n) : Finset (Proc n) := by
  classical
  exact Finset.univ.filter (fun r => IsRepMinimal (n := n) G r)

theorem mem_minimalClassReps_iff (G : CommGraph n) (r : Proc n) :
    r ∈ minimalClassReps (n := n) G ↔ IsRepMinimal (n := n) G r := by
  classical
  simp [minimalClassReps]

theorem exists_rep_for_minimal
    (G : CommGraph n) (r : Proc n)
    (hrMin : IsReachabilityMinimal (n := n) G r) :
    ∃ rep : Proc n,
      rep ∈ minimalClassReps (n := n) G ∧
      MutualReachable (n := n) G rep r := by
  classical
  let C : Finset (Proc n) :=
    (minimalReachers (n := n) G).filter (fun x => MutualReachable (n := n) G x r)
  have hrC : r ∈ C := by
    refine Finset.mem_filter.mpr ?_
    refine ⟨(mem_minimalReachers_iff (n := n) G r).2 hrMin, ?_⟩
    exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  obtain ⟨rep, hrepC, hmin⟩ := C.exists_minimal ⟨r, hrC⟩
  have hrepMin : IsReachabilityMinimal (n := n) G rep := by
    have : rep ∈ minimalReachers (n := n) G := by
      exact (Finset.mem_filter.mp hrepC).1
    exact (mem_minimalReachers_iff (n := n) G rep).1 this
  have hrepMutR : MutualReachable (n := n) G rep r := by
    exact (Finset.mem_filter.mp hrepC).2
  have hrepLeAll :
      ∀ r' : Proc n,
        IsReachabilityMinimal (n := n) G r' →
        MutualReachable (n := n) G rep r' →
        rep ≤ r' := by
    intro r' hr'Min hmut
    have hr'C : r' ∈ C := by
      have hrr' : Reachable G r r' :=
        Relation.ReflTransGen.trans hrepMutR.2 hmut.1
      have hr'r : Reachable G r' r :=
        Relation.ReflTransGen.trans hmut.2 hrepMutR.1
      refine Finset.mem_filter.mpr ?_
      refine ⟨(mem_minimalReachers_iff (n := n) G r').2 hr'Min, ?_⟩
      exact ⟨hr'r, hrr'⟩
    by_cases hle : r' ≤ rep
    · exact hmin hr'C hle
    · exact le_of_not_ge hle
  have hrepIsRep : IsRepMinimal (n := n) G rep := by
    refine ⟨hrepMin, hrepLeAll⟩
  refine ⟨rep, ?_, hrepMutR⟩
  exact (mem_minimalClassReps_iff (n := n) G rep).2 hrepIsRep

theorem eq_of_rep_mutual
    (G : CommGraph n)
    {i i' : Proc n}
    (hi : i ∈ minimalClassReps (n := n) G)
    (hi' : i' ∈ minimalClassReps (n := n) G)
    (hmut : MutualReachable (n := n) G i i') :
    i = i' := by
  have hRep : IsRepMinimal (n := n) G i :=
    (mem_minimalClassReps_iff (n := n) G i).1 hi
  have hRep' : IsRepMinimal (n := n) G i' :=
    (mem_minimalClassReps_iff (n := n) G i').1 hi'
  have hii' : i ≤ i' := hRep.2 i' hRep'.1 hmut
  have hi'i : i' ≤ i := hRep'.2 i hRep.1 ⟨hmut.2, hmut.1⟩
  exact le_antisymm hii' hi'i

theorem unique_rep_reached
    (G : CommGraph n)
    {j i i' : Proc n}
    (hi : i ∈ minimalClassReps (n := n) G)
    (hi' : i' ∈ minimalClassReps (n := n) G)
    (hji : Reachable G j i)
    (hji' : Reachable G j i') :
    i = i' := by
  have hRep : IsRepMinimal (n := n) G i :=
    (mem_minimalClassReps_iff (n := n) G i).1 hi
  have hRep' : IsRepMinimal (n := n) G i' :=
    (mem_minimalClassReps_iff (n := n) G i').1 hi'
  have hij : Reachable G i j := hRep.1 j hji
  have hi'j : Reachable G i' j := hRep'.1 j hji'
  have hii' : Reachable G i i' := Relation.ReflTransGen.trans hij hji'
  have hi'i : Reachable G i' i := Relation.ReflTransGen.trans hi'j hji
  exact eq_of_rep_mutual (n := n) G hi hi' ⟨hii', hi'i⟩

theorem isRootSet_minimalClassReps (G : CommGraph n) :
    IsRootSet G (minimalClassReps (n := n) G) := by
  intro i
  rcases exists_minimal_reacher_to (n := n) G i with ⟨r, hrMin, hri⟩
  rcases exists_rep_for_minimal (n := n) G r hrMin with ⟨rep, hrep, hmut⟩
  refine ⟨rep, hrep, ?_⟩
  exact Relation.ReflTransGen.trans hmut.1 hri

theorem isKRooted_of_card_minimalClassReps_le
    (G : CommGraph n)
    (hcard : (minimalClassReps (n := n) G).card ≤ s + 1) :
    IsKRooted G (s + 1) := by
  refine ⟨minimalClassReps (n := n) G, hcard, ?_⟩
  exact isRootSet_minimalClassReps (n := n) G

theorem lt_card_minimalClassReps_of_not_kRooted
    (G : CommGraph n)
    (hnot : ¬ IsKRooted G (s + 1)) :
    s + 1 < (minimalClassReps (n := n) G).card := by
  by_contra hle
  exact hnot (isKRooted_of_card_minimalClassReps_le (n := n) (s := s) G (Nat.not_lt.mp hle))

/-- Static graph/roots data used by the lower-bound execution construction. -/
structure StaticImpossibilityData where
  graph : CommGraph n
  graph_in_adversary : graph ∈ N.graphs
  graph_not_k_rooted : ¬ IsKRooted graph (s + 1)
  roots : Finset (Proc n)
  roots_card : roots.card = s + 2
  rootLabel : Proc n → Option (Proc n)
  label_mem_roots : ∀ j r, rootLabel j = some r → r ∈ roots
  label_sound : ∀ j r, rootLabel j = some r → Reachable graph j r
  label_complete :
    ∀ j i, i ∈ roots → Reachable graph j i → rootLabel j = some i

/-- Constant trace that repeats one graph at every round. -/
def staticTrace (G : CommGraph n) : Round → CommGraph n := fun _ => G

theorem admissible_staticTrace
    (d : StaticImpossibilityData N s) :
    AdmissibleTrace N (staticTrace (n := n) d.graph) := by
  intro t
  exact d.graph_in_adversary

theorem exists_staticImpossibilityData_of_badGraph
    (G : CommGraph n)
    (hGin : G ∈ N.graphs)
    (hGnot : ¬ IsKRooted G (s + 1)) :
    Nonempty (StaticImpossibilityData N s) := by
  classical
  have hcardGt :
      s + 1 < (minimalClassReps (n := n) G).card :=
    lt_card_minimalClassReps_of_not_kRooted (n := n) (s := s) G hGnot
  have hsize : s + 2 ≤ (minimalClassReps (n := n) G).card := by
    omega
  rcases Finset.exists_subset_card_eq (s := minimalClassReps (n := n) G) hsize with
    ⟨roots, hrootsSub, hrootsCard⟩
  let rootLabel : Proc n → Option (Proc n) := fun j =>
    if h : ∃ i : Proc n, i ∈ roots ∧ Reachable G j i then
      some (Classical.choose h)
    else
      none
  have hLabelMem : ∀ j r, rootLabel j = some r → r ∈ roots := by
    intro j r hEq
    by_cases h : ∃ i : Proc n, i ∈ roots ∧ Reachable G j i
    · have hChooseMem : Classical.choose h ∈ roots := (Classical.choose_spec h).1
      have hEq' : Classical.choose h = r := by
        simpa [rootLabel, h] using hEq
      simpa [hEq'] using hChooseMem
    · simp [rootLabel, h] at hEq
  have hLabelSound : ∀ j r, rootLabel j = some r → Reachable G j r := by
    intro j r hEq
    by_cases h : ∃ i : Proc n, i ∈ roots ∧ Reachable G j i
    · have hChooseReach : Reachable G j (Classical.choose h) := (Classical.choose_spec h).2
      have hEq' : Classical.choose h = r := by
        simpa [rootLabel, h] using hEq
      simpa [hEq'] using hChooseReach
    · simp [rootLabel, h] at hEq
  have hLabelComplete :
      ∀ j i, i ∈ roots → Reachable G j i → rootLabel j = some i := by
    intro j i hi hji
    let h : ∃ u : Proc n, u ∈ roots ∧ Reachable G j u := ⟨i, hi, hji⟩
    have hChooseMem : Classical.choose h ∈ roots := (Classical.choose_spec h).1
    have hChooseReach : Reachable G j (Classical.choose h) := (Classical.choose_spec h).2
    have hChooseRep : Classical.choose h ∈ minimalClassReps (n := n) G :=
      hrootsSub hChooseMem
    have hiRep : i ∈ minimalClassReps (n := n) G := hrootsSub hi
    have hEqRoot : Classical.choose h = i :=
      unique_rep_reached (n := n) G hChooseRep hiRep hChooseReach hji
    simp [rootLabel, h, hEqRoot]
  refine ⟨{
    graph := G
    graph_in_adversary := hGin
    graph_not_k_rooted := hGnot
    roots := roots
    roots_card := hrootsCard
    rootLabel := rootLabel
    label_mem_roots := hLabelMem
    label_sound := hLabelSound
    label_complete := hLabelComplete
  }⟩

/-- Initial values are constant on every reachability cone of each distinguished root. -/
def InitConstantOnRootReachers
    (d : StaticImpossibilityData N s) (init : Proc n → V) : Prop :=
  ∀ i : Proc n, i ∈ d.roots →
    ∀ j : Proc n, Reachable d.graph j i → init j = init i

/-- Predecessor closure: if `j` reaches `i` and `k → j`, then `k` also reaches `i`. -/
theorem reachable_pred_closed
    (G : CommGraph n) {i j k : Proc n}
    (hji : Reachable G j i) (hkj : G.edge k j) :
    Reachable G k i :=
  Relation.ReflTransGen.head hkj hji

/-- Canonical existence of `s+2` distinct processes when `s+2 ≤ n`. -/
theorem exists_roots_of_two_add_le (hsize : s + 2 ≤ n) :
    ∃ roots : Finset (Proc n), roots.card = s + 2 := by
  refine ⟨(Finset.univ : Finset (Fin (s + 2))).map (Fin.castLEEmb hsize), ?_⟩
  simp

/-- If an adversary is not `(s+1)`-rooted, then necessarily `s+2 ≤ n`. -/
theorem two_add_le_of_not_kRootedAdversary
    (hnotRooted : ¬ IsKRootedAdversary N (s + 1)) :
    s + 2 ≤ n := by
  by_contra hsize
  have hn : n ≤ s + 1 := by omega
  apply hnotRooted
  intro G hG
  refine ⟨Finset.univ, ?_, ?_⟩
  · simpa [Proc] using hn
  · intro i
    refine ⟨i, by simp, ?_⟩
    exact Relation.ReflTransGen.refl

/-- Extract a concrete bad graph from a non-`(s+1)`-rooted adversary. -/
theorem exists_graph_not_kRooted_of_not_kRootedAdversary
    (hnotRooted : ¬ IsKRootedAdversary N (s + 1)) :
    ∃ G : CommGraph n, G ∈ N.graphs ∧ ¬ IsKRooted G (s + 1) := by
  by_contra hno
  apply hnotRooted
  intro G hG
  by_contra hGbad
  exact hno ⟨G, hG, hGbad⟩

/--
If `V` has affine dimension `s+1`, then for any `s+2` processes we can choose initial values
whose restriction to those processes is affinely independent.
-/
theorem exists_init_affineIndependent_of_finrank_eq
    (hfin : Module.finrank ℝ V = s + 1)
    (roots : Finset (Proc n)) (hcard : roots.card = s + 2) :
    ∃ init : Proc n → V, AffineIndependent ℝ (fun p : roots => init p) := by
  have hfin_succ : Module.finrank ℝ V = Nat.succ s := by simpa [Nat.succ_eq_add_one] using hfin
  let : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_eq_succ hfin_succ
  have hcardRoots : Fintype.card roots = Module.finrank ℝ V + 1 := by
    calc
      Fintype.card roots = roots.card := by simp
      _ = s + 2 := hcard
      _ = Module.finrank ℝ V + 1 := by omega
  rcases
      (AffineBasis.exists_affineBasis_of_finiteDimensional
        (k := ℝ) (V := V) (P := V) (ι := roots) hcardRoots) with
    ⟨b⟩
  let init : Proc n → V := fun i =>
    if hi : i ∈ roots then b ⟨i, hi⟩ else 0
  refine ⟨init, ?_⟩
  have hinit : (fun p : roots => init p) = fun p : roots => b p := by
    funext p
    simp [init, p.property]
  simpa [hinit] using b.ind

/--
Generalized version: if `Module.finrank ℝ V > s`, then one can realize `s+2` affinely
independent initial values on any `s+2` distinguished processes.
-/
theorem exists_init_affineIndependent_of_finrank_gt
    (hfin : s < Module.finrank ℝ V)
    (roots : Finset (Proc n)) (hcard : roots.card = s + 2) :
    ∃ init : Proc n → V, AffineIndependent ℝ (fun p : roots => init p) := by
  have hpos : 0 < Module.finrank ℝ V := lt_of_le_of_lt (Nat.zero_le s) hfin
  let : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_pos hpos
  let m : Nat := Module.finrank ℝ V + 1
  have hm : s + 2 ≤ m := by
    dsimp [m]
    omega
  have hcardFin : Fintype.card (Fin m) = Module.finrank ℝ V + 1 := by
    simp [m]
  rcases
      (AffineBasis.exists_affineBasis_of_finiteDimensional
        (k := ℝ) (V := V) (P := V) (ι := Fin m) hcardFin) with
    ⟨b⟩
  let emb : Fin (s + 2) ↪ Fin m := Fin.castLEEmb hm
  let pstd : Fin (s + 2) → V := fun j => b (emb j)
  have hpstd : AffineIndependent ℝ pstd := by
    exact b.ind.comp_embedding emb
  have hcardRoots : Fintype.card roots = s + 2 := by
    simpa using hcard
  have hcardRootsFin : Fintype.card roots = Fintype.card (Fin (s + 2)) := by
    simpa using hcardRoots
  let eRoots : roots ≃ Fin (s + 2) := Fintype.equivOfCardEq hcardRootsFin
  let init : Proc n → V := fun i =>
    if hi : i ∈ roots then pstd (eRoots ⟨i, hi⟩) else 0
  refine ⟨init, ?_⟩
  have hinit : (fun p : roots => init p) = fun p : roots => pstd (eRoots p) := by
    funext p
    simp [init, p.property]
  have hAffOn : AffineIndependent ℝ (fun p : roots => pstd (eRoots p)) := by
    exact (affineIndependent_equiv eRoots).2 hpstd
  simpa [hinit] using hAffOn

/--
From static root-labeling data and `dim(V) > s`, construct an initialization that is both
affinely independent on roots and constant on each root's reachability cone.
-/
theorem exists_init_for_static_data
    (d : StaticImpossibilityData N s)
    (hfin : s < Module.finrank ℝ V) :
    ∃ init : Proc n → V,
      AffineIndependent ℝ (fun p : d.roots => init p) ∧
      InitConstantOnRootReachers (V := V) (n := n) N s d init := by
  rcases exists_init_affineIndependent_of_finrank_gt
      (V := V) (n := n) (s := s) hfin d.roots d.roots_card with
    ⟨initRoot, hAffRoot⟩
  let init : Proc n → V := fun j =>
    match d.rootLabel j with
    | some r => initRoot r
    | none => 0
  have hOnRoots : (fun p : d.roots => init p) = fun p : d.roots => initRoot p := by
    funext p
    have hLbl : d.rootLabel p = some p := d.label_complete p p p.property Relation.ReflTransGen.refl
    simp [init, hLbl]
  have hConst : InitConstantOnRootReachers (V := V) (n := n) N s d init := by
    intro i hi j hj
    have hLbl_j : d.rootLabel j = some i := d.label_complete j i hi hj
    have hLbl_i : d.rootLabel i = some i := d.label_complete i i hi Relation.ReflTransGen.refl
    simp [init, hLbl_j, hLbl_i]
  refine ⟨init, ?_, hConst⟩
  simpa [hOnRoots] using hAffRoot

/-- Existence of the static counterexample data used in the impossibility proof. -/
def ModelGrounded : Prop :=
  Nonempty (StaticImpossibilityData N s)

theorem modelGrounded_of_not_kRootedAdversary
    (hnotRooted : ¬ IsKRootedAdversary N (s + 1)) :
    ModelGrounded (N := N) (s := s) := by
  rcases exists_graph_not_kRooted_of_not_kRootedAdversary (N := N) (s := s) hnotRooted with
    ⟨G, hGin, hGnot⟩
  exact exists_staticImpossibilityData_of_badGraph (n := n) (N := N) (s := s) G hGin hGnot

end ImpossibilityModel

end ModelLemmas
end AsymptoticSubspace
