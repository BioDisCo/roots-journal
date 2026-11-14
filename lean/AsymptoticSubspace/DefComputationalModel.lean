module

public import Mathlib

/-!
# Computational model (Section 2) and problem specification (Section 3)

Processes are indexed by `Fin n`. Time zero contains the initial outputs;
communication starts at time one. An edge `G.edge i j` carries information
from process `i` to process `j`, and every graph has self-loops.

`StatefulAlgorithm` separates arbitrary local state from the vector output.
Its locality condition permits an update to depend only on the received states
and the incoming neighborhood. In particular, it cannot inspect remote edges.
`runState` and `run` give the state and output trajectories from local inputs.

`PaperComputationalModel.Algorithm` and `PaperComputationalModel.Solves` are
used by Theorem 2 and Corollary 20. The specification requires convergence onto
an affine subspace of exactly dimension `s` and onto the initial convex hull.
It does not require individual output sequences to converge to points.
-/

@[expose] public section

noncomputable section

namespace AsymptoticSubspace.ComputationalModel

/-! ## Communication graphs and oblivious message adversaries -/

abbrev Round := Nat
abbrev Proc (n : Nat) := Fin n

/-- Round communication graph on `n` processes with mandatory self-loops. -/
structure CommGraph (n : Nat) where
  edge : Proc n → Proc n → Prop
  self_loop : ∀ i : Proc n, edge i i

/-- Incoming neighbors of process `i` in graph `G`. -/
def InNeighbors {n : Nat} (G : CommGraph n) (i : Proc n) : Set (Proc n) :=
  {j | G.edge j i}

/-- Reachability in a communication graph (directed path, including length-0). -/
def Reachable {n : Nat} (G : CommGraph n) : Proc n → Proc n → Prop :=
  Relation.ReflTransGen G.edge

/-- `R` is a root set of `G` if every node is reachable from some node in `R`. -/
def IsRootSet {n : Nat} (G : CommGraph n) (R : Finset (Proc n)) : Prop :=
  ∀ i : Proc n, ∃ j : Proc n, j ∈ R ∧ Reachable G j i

/-- A graph is `k`-rooted if it has some root set of size at most `k`. -/
def IsKRooted {n : Nat} (G : CommGraph n) (k : Nat) : Prop :=
  ∃ R : Finset (Proc n), R.card ≤ k ∧ IsRootSet G R

/-- Oblivious message adversary as a nonempty set of communication graphs. -/
structure ObliviousMessageAdversary (n : Nat) where
  graphs : Set (CommGraph n)
  nonempty : graphs.Nonempty

/-- An oblivious message adversary is `k`-rooted if each of its graphs is `k`-rooted. -/
def IsKRootedAdversary {n : Nat} (N : ObliviousMessageAdversary n) (k : Nat) : Prop :=
  ∀ G : CommGraph n, G ∈ N.graphs → IsKRooted G k

/-- `M` is a broadcasting set of `G` if every process has an incoming edge from some node in `M`. -/
def IsBroadcastingSet {n : ℕ} (G : CommGraph n) (M : Finset (Proc n)) : Prop :=
  ∀ i : Proc n, ∃ j : Proc n, j ∈ M ∧ G.edge j i

variable {n : ℕ}

/-- A communication graph whose edges represent one message-relaying block. -/
def CommGraph.comp (G H : CommGraph n) : CommGraph n where
  edge i j := ∃ m, G.edge i m ∧ H.edge m j
  self_loop i := ⟨i, G.self_loop i, H.self_loop i⟩

def CommGraph.id (n : ℕ) : CommGraph n where
  edge i j := i = j
  self_loop _ := rfl

/-- The product of rounds `start + 1` through `start + len`, in temporal order. -/
def graphProduct (G : Round → CommGraph n) (start : Round) : ℕ → CommGraph n
  | 0 => CommGraph.id n
  | len + 1 => (graphProduct G start len).comp (G (start + len + 1))

def IsKBroadcastable (G : CommGraph n) (k : ℕ) : Prop :=
  ∃ R : Finset (Proc n), R.card ≤ k ∧ IsBroadcastingSet G R

/-- Every graph of the adversary is `k`-broadcastable. -/
def IsKBroadcastableAdversary (N : ObliviousMessageAdversary n) (k : ℕ) : Prop :=
  ∀ G ∈ N.graphs, IsKBroadcastable G k

/-- Only rounds with actual communication must belong to the adversary. -/
def AdmissibleActualTrace {n : ℕ} (N : ObliviousMessageAdversary n)
    (G : Round → CommGraph n) : Prop :=
  ∀ t, 0 < t → G t ∈ N.graphs

/-! ## Local algorithms and their executions -/

/-- A deterministic local protocol with arbitrary internal state, separately
from its vector output. The state may contain an unbounded message history.
Locality compares different graphs with identical received states and incoming
neighborhoods, excluding access to remote edges. -/
structure StatefulAlgorithm (V : Type*) (n : ℕ) (State : Type*) where
  initialState : Proc n → V → State
  step : Round → CommGraph n → (Proc n → State) → Proc n → State
  output : Round → Proc n → State → V
  output_initial : ∀ i x, output 0 i (initialState i x) = x
  locality : ∀ t G H x y i,
    (∀ j, G.edge j i ↔ H.edge j i) →
    (∀ j, G.edge j i → x j = y j) → step t G x i = step t H y i

namespace StatefulAlgorithm

variable {V State : Type*} {n : ℕ} (A : StatefulAlgorithm V n State)

def runState (G : Round → CommGraph n) (init : Proc n → V) : Round → Proc n → State
  | 0 => fun i => A.initialState i (init i)
  | t + 1 => fun i => A.step (t + 1) (G (t + 1)) (runState G init t) i

def run (G : Round → CommGraph n) (init : Proc n → V) (t : Round) (i : Proc n) : V :=
  A.output t i (A.runState G init t i)

end StatefulAlgorithm

/-! ## Convergence onto a set -/

/-- Asymptotic convergence onto a set (`dist(x(t), S) → 0`). -/
def ConvergesToSet {V : Type*} [NormedAddCommGroup V] (x : Round → V) (S : Set V) : Prop :=
  S.Nonempty ∧
    (∀ ε : ℝ, 0 < ε → ∃ T : Round, ∀ t : Round, T ≤ t → Metric.infDist (x t) S < ε)

end AsymptoticSubspace.ComputationalModel

namespace AsymptoticSubspace

open ComputationalModel

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Exact-dimensional agreement with admissibility required only for `t ≥ 1`. -/
def StatefulSolvesExactActualRounds {State : Type*} {n : ℕ}
    (A : StatefulAlgorithm V n State) (N : ObliviousMessageAdversary n) (s : ℕ) : Prop :=
  ∀ (G : Round → CommGraph n) (init : Proc n → V), AdmissibleActualTrace N G →
    ∃ E : AffineSubspace ℝ V, Module.finrank ℝ E.direction = s ∧
      (∀ i, ConvergesToSet (fun t => A.run G init t i) (E : Set V)) ∧
      (∀ i, ConvergesToSet (fun t => A.run G init t i) (convexHull ℝ (Set.range init)))

namespace PaperComputationalModel

/-- General deterministic message-local protocol, with separately specified
vector output and initialization from each process's own input. -/
abbrev Algorithm (V : Type*) (n : ℕ) (State : Type*) := StatefulAlgorithm V n State

/-- The paper's two requirements: convergence onto one exactly `s`-dimensional
affine subspace, and convergence onto the convex hull of the initial vectors. -/
abbrev Solves {V State : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (A : Algorithm V n State)
    (N : ComputationalModel.ObliviousMessageAdversary n) (s : ℕ) :=
  StatefulSolvesExactActualRounds A N s

end PaperComputationalModel

end AsymptoticSubspace
