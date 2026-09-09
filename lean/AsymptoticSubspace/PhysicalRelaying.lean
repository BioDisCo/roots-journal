import AsymptoticSubspace.StatefulAlgorithms
import AsymptoticSubspace.CorBound
import AsymptoticSubspace.VariableRelaying
import AsymptoticSubspace.ActualRounds

noncomputable section

namespace AsymptoticSubspace.ComputationalModel

variable {V : Type*} {n : ℕ}

/-- One retained value per origin. The domain is the finite process set. -/
abbrev OriginBuffer (V : Type*) (n : ℕ) := Proc n → Option V

def singletonBuffer (i : Proc n) (v : V) : OriginBuffer V n := by
  classical
  exact fun o => if o = i then some v else none

/-- Merge all received buffers, deduplicating by origin. On reachable protocol
states all copies of an origin have the same value (proved below). Conflicting
unreachable inputs are totalized by arbitrary choice; this is not a
conflict-detection or Byzantine-message-validation operation. -/
def mergeBuffers (b : Proc n → OriginBuffer V n) : OriginBuffer V n := by
  classical
  exact fun o => if h : ∃ v, ∃ j, b j o = some v then some h.choose else none

open Classical in
lemma mergeBuffers_mask (P : Proc n → Proc n → Prop) (x : Proc n → V)
    (b : Proc n → OriginBuffer V n)
    (hb : ∀ j o, b j o = if P j o then some (x o) else none) (o : Proc n) :
    mergeBuffers b o = if ∃ j, P j o then some (x o) else none := by
  classical
  by_cases h : ∃ j, P j o
  · obtain ⟨j, hj⟩ := h
    have hex : ∃ v, ∃ j, b j o = some v := ⟨x o, j, by simp [hb, hj]⟩
    have hvalue : hex.choose = x o := by
      obtain ⟨q, hq⟩ := hex.choose_spec
      rw [hb] at hq
      split_ifs at hq with hp
      · exact (Option.some.inj hq).symm
    simp [mergeBuffers, hex, hvalue, show ∃ j, P j o from ⟨j, hj⟩]
  · have hex : ¬ ∃ v, ∃ j, b j o = some v := by
      rintro ⟨v, j, hj⟩
      simp [hb, show ¬ P j o from fun hj => h ⟨j, hj⟩] at hj
    simp [mergeBuffers, hex, h]

def receivedBuffers (G : CommGraph n) (b : Proc n → OriginBuffer V n)
    (i : Proc n) : Proc n → OriginBuffer V n := by
  classical
  exact fun j => if G.edge j i then b j else fun _ => none

def floodBuffer (G : Round → CommGraph n) (start len : ℕ)
    (x : Proc n → V) (i : Proc n) : OriginBuffer V n := by
  classical
  exact fun o => if (graphProduct G start len).edge o i then some (x o) else none

@[simp] lemma floodBuffer_zero (G : Round → CommGraph n) (start : ℕ)
    (x : Proc n → V) (i : Proc n) :
    floodBuffer G start 0 x i = singletonBuffer i (x i) := by
  classical
  funext o
  by_cases h : o = i <;> simp [floodBuffer, graphProduct, CommGraph.id, singletonBuffer, h]

/-- Exact physical flooding invariant: a value is present exactly when its
origin has a temporal path, and its payload is that origin's block-start value. -/
theorem merge_received_floodBuffer (G : Round → CommGraph n) (start len : ℕ)
    (x : Proc n → V) (i : Proc n) :
    mergeBuffers (receivedBuffers (G (start + len + 1))
      (floodBuffer G start len x) i) = floodBuffer G start (len + 1) x i := by
  classical
  funext o
  rw [mergeBuffers_mask
    (fun j o => (G (start + len + 1)).edge j i ∧ (graphProduct G start len).edge o j) x
    _ (by intro j o; by_cases h : (G (start + len + 1)).edge j i <;>
          simp [receivedBuffers, floodBuffer, h])]
  simp only [floodBuffer, graphProduct, CommGraph.comp]
  congr 1
  apply propext
  aesop

namespace RelayingSchedule

lemma boundary_clock_le (B : RelayingSchedule) (t : ℕ) : B.boundary (B.clock t) ≤ t := by
  have hm := Finset.max'_mem
    ((Finset.range (t + 1)).filter (fun j => B.boundary j ≤ t))
    ⟨0, by simp [B.boundary_zero]⟩
  exact (Finset.mem_filter.mp hm).2

lemma lt_next_boundary (B : RelayingSchedule) (t : ℕ) : t < B.boundary (B.clock t + 1) := by
  by_contra h
  have := B.clock_progress (B.clock t + 1) t (by omega)
  omega

lemma clock_eq_of_bounds (B : RelayingSchedule) {k t : ℕ}
    (hl : B.boundary k ≤ t) (hu : t < B.boundary (k + 1)) : B.clock t = k := by
  have hle := B.clock_progress k t hl
  have hbound := B.boundary_clock_le t
  by_contra hne
  have h := B.strictMono.monotone (show k + 1 ≤ B.clock t by omega)
  omega

@[simp] lemma clock_boundary (B : RelayingSchedule) (k : ℕ) : B.clock (B.boundary k) = k :=
  B.clock_eq_of_bounds le_rfl (B.strictMono (Nat.lt_succ_self k))

lemma not_boundary_inside (B : RelayingSchedule) {k t : ℕ}
    (hl : B.boundary k < t) (hu : t < B.boundary (k + 1)) :
    ¬ ∃ j, t = B.boundary (j + 1) := by
  rintro ⟨j, rfl⟩
  have h₁ := B.strictMono.lt_iff_lt.mp hl
  have h₂ := B.strictMono.lt_iff_lt.mp hu
  omega

end RelayingSchedule

structure RelayState (V : Type*) (n : ℕ) where
  value : V
  buffer : OriginBuffer V n

open Classical in
/-- Physical-round protocol. Every round forwards the retained buffers; the
last communication round of a shared block also updates and resets the buffer.
`update` can be any deterministic function of the received origin/value map. -/
def physicalRelayAlgorithm (B : RelayingSchedule)
    (update : Round → Proc n → OriginBuffer V n → V) :
    StatefulAlgorithm V n (RelayState V n) where
  initialState i v := ⟨v, singletonBuffer i v⟩
  step t G s i :=
    let b := mergeBuffers (receivedBuffers G (fun j => (s j).buffer) i)
    if ∃ k, t = B.boundary (k + 1) then
      let v := update t i b
      ⟨v, singletonBuffer i v⟩
    else ⟨(s i).value, b⟩
  output _ _ s := s.value
  output_initial _ _ := rfl
  locality t G H s z i hG hs := by
    have hi := hs i (G.self_loop i)
    have hb : receivedBuffers G (fun j => (s j).buffer) i =
        receivedBuffers H (fun j => (z j).buffer) i := by
      funext j
      by_cases h : G.edge j i
      · simp [receivedBuffers, h, (hG j).mp h, hs j h]
      · simp [receivedBuffers, h, show ¬ H.edge j i from fun h' => h ((hG j).mpr h')]
    simp only [hb, hi]

open Classical in
lemma physicalRelay_step (B : RelayingSchedule)
    (update : Round → Proc n → OriginBuffer V n → V)
    (t : ℕ) (G : CommGraph n) (s : Proc n → RelayState V n) (i : Proc n) :
    (physicalRelayAlgorithm B update).step t G s i =
      if ∃ k, t = B.boundary (k + 1) then
        let v := update t i (mergeBuffers (receivedBuffers G (fun j => (s j).buffer) i))
        ⟨v, singletonBuffer i v⟩
      else ⟨(s i).value, mergeBuffers (receivedBuffers G (fun j => (s j).buffer) i)⟩ := rfl

lemma physicalRelay_runState_inside (B : RelayingSchedule)
    (update : Round → Proc n → OriginBuffer V n → V)
    (G : Round → CommGraph n) (init : Proc n → V) (k : ℕ) (x : Proc n → V)
    (hstart : ∀ i, (physicalRelayAlgorithm B update).runState G init (B.boundary k) i =
      ⟨x i, singletonBuffer i (x i)⟩) :
    ∀ len, len < B.boundary (k + 1) - B.boundary k → ∀ i,
      (physicalRelayAlgorithm B update).runState G init (B.boundary k + len) i =
        ⟨x i, floodBuffer G (B.boundary k) len x i⟩ := by
  intro len
  induction len with
  | zero => intro _ i; simpa using hstart i
  | succ len ih =>
    intro hlen i
    have hprev := ih (by omega)
    have hb := B.not_boundary_inside (k := k) (t := B.boundary k + len + 1)
      (by omega) (by omega)
    rw [show B.boundary k + (len + 1) = (B.boundary k + len) + 1 by omega]
    simp only [StatefulAlgorithm.runState, physicalRelay_step, hb, ↓reduceIte, hprev]
    rw [merge_received_floodBuffer]

lemma physicalRelay_runState_boundary (B : RelayingSchedule)
    (update : Round → Proc n → OriginBuffer V n → V)
    (G : Round → CommGraph n) (init : Proc n → V) (x : ℕ → Proc n → V)
    (hzero : x 0 = init)
    (hupdate : ∀ k i, update (B.boundary (k + 1)) i
      (floodBuffer G (B.boundary k) (B.boundary (k + 1) - B.boundary k) (x k) i) =
        x (k + 1) i) :
    ∀ k i, (physicalRelayAlgorithm B update).runState G init (B.boundary k) i =
      ⟨x k i, singletonBuffer i (x k i)⟩ := by
  intro k
  induction k with
  | zero =>
    intro i
    simp [B.boundary_zero, StatefulAlgorithm.runState, physicalRelayAlgorithm, hzero]
  | succ k ih =>
    intro i
    let len := B.boundary (k + 1) - B.boundary k - 1
    have hlt : B.boundary k < B.boundary (k + 1) := B.strictMono (Nat.lt_succ_self k)
    have hlen : len < B.boundary (k + 1) - B.boundary k := by dsimp [len]; omega
    have ht : B.boundary k + len + 1 = B.boundary (k + 1) := by dsimp [len]; omega
    have hinside := physicalRelay_runState_inside B update G init k (x k) ih len hlen
    rw [← ht]
    simp only [StatefulAlgorithm.runState, physicalRelay_step, hinside]
    rw [if_pos ⟨k, ht⟩, merge_received_floodBuffer, ht,
      show len + 1 = B.boundary (k + 1) - B.boundary k by dsimp [len]; omega,
      hupdate]

/-- End-to-end refinement for any local block update: physical outputs equal
the prescribed macro outputs at the number of completed shared blocks.
The graph-product buffer realization is proved, not assumed. -/
theorem physicalRelay_run (B : RelayingSchedule)
    (update : Round → Proc n → OriginBuffer V n → V)
    (G : Round → CommGraph n) (init : Proc n → V) (x : ℕ → Proc n → V)
    (hzero : x 0 = init)
    (hupdate : ∀ k i, update (B.boundary (k + 1)) i
      (floodBuffer G (B.boundary k) (B.boundary (k + 1) - B.boundary k) (x k) i) =
        x (k + 1) i) (t : ℕ) (i : Proc n) :
    (physicalRelayAlgorithm B update).run G init t i = x (B.clock t) i := by
  have hstart := physicalRelay_runState_boundary B update G init x hzero hupdate (B.clock t)
  have hl := B.boundary_clock_le t
  have hu := B.lt_next_boundary t
  have hi := physicalRelay_runState_inside B update G init (B.clock t) (x (B.clock t)) hstart
    (t - B.boundary (B.clock t)) (by omega) i
  rw [Nat.add_sub_of_le hl] at hi
  exact congrArg RelayState.value hi

section Normed

variable [NormedAddCommGroup V] [NormedSpace ℝ V]

def bufferOrigins (b : OriginBuffer V n) : Finset (Proc n) :=
  Finset.univ.filter (fun o => (b o).isSome)

/-- Arithmetic mean over distinct received origins, never over message copies. -/
def bufferAverage (b : OriginBuffer V n) : V :=
  ∑ o, ((bufferOrigins b).card : ℝ)⁻¹ • (b o).getD 0

lemma bufferAverage_floodBuffer (G : Round → CommGraph n) (start len : ℕ)
    (x : Proc n → V) (i : Proc n) :
    bufferAverage (floodBuffer G start len x i) =
      ∑ o, equalNeighborWeight (graphProduct G start len) i o • x o := by
  have horigins : bufferOrigins (floodBuffer G start len x i) =
      inNeighborFinset (graphProduct G start len) i := by
    ext o
    by_cases h : (graphProduct G start len).edge o i <;>
      simp [bufferOrigins, floodBuffer, h]
  unfold bufferAverage
  rw [horigins]
  apply Finset.sum_congr rfl
  intro o _
  by_cases h : (graphProduct G start len).edge o i <;>
    simp [floodBuffer, equalNeighborWeight, h]

def variableRelayedEqualNeighbor (G : Round → CommGraph n) (B : RelayingSchedule)
    (init : Proc n → V) : VariableRelayingExecution (V := V) G B where
  averaging := equalNeighborExecution
    (fun t => graphProduct G (B.boundary (t - 1))
      (B.boundary (t - 1 + 1) - B.boundary (t - 1))) init
  graphs_eq _ := rfl

/-- Concrete physical protocol with arbitrary positive finite shared blocks. -/
def physicalEqualNeighbor (B : RelayingSchedule) : StatefulAlgorithm V n (RelayState V n) :=
  physicalRelayAlgorithm B (fun _ _ => bufferAverage)

/-- The received-origin update has the uniform `1/n` bound, independently of
any potentially larger safety constant of the unrelayed execution. -/
theorem physicalEqualNeighbor_macro_safe [NeZero n]
    (G : Round → CommGraph n) (B : RelayingSchedule) (init : Proc n → V) :
    AlphaSafe (variableRelayedEqualNeighbor G B init).averaging (1 / (n : ℝ)) :=
  equalNeighbor_safe _ init

/-- No refinement hypothesis remains: the implemented physical-round protocol
is exactly equal-neighbor averaging on the block product graphs. -/
theorem physicalEqualNeighbor_run (G : Round → CommGraph n) (B : RelayingSchedule)
    (init : Proc n → V) (t : ℕ) (i : Proc n) :
    (physicalEqualNeighbor B).run G init t i =
      (variableRelayedEqualNeighbor G B init).outputs t i := by
  apply physicalRelay_run B (fun _ _ => bufferAverage) G init
    (variableRelayedEqualNeighbor G B init).averaging.outputs rfl
  intro k j
  rw [bufferAverage_floodBuffer]
  simpa [variableRelayedEqualNeighbor, equalNeighborExecution] using
    ((variableRelayedEqualNeighbor G B init).averaging.update_rule k j).symm

/-- Shared fixed-length blocks, with no separate update round. -/
def fixedRelayingSchedule (L : ℕ) (hL : 0 < L) : RelayingSchedule where
  boundary k := k * L
  boundary_zero := Nat.zero_mul L
  strictMono := fun _ _ h => Nat.mul_lt_mul_of_pos_right h hL

@[simp] lemma fixedRelayingSchedule_clock (L : ℕ) (hL : 0 < L) (t : ℕ) :
    (fixedRelayingSchedule L hL).clock t = t / L := by
  apply RelayingSchedule.clock_eq_of_bounds
  · exact Nat.div_mul_le_self t L
  · change t < (t / L + 1) * L
    have := Nat.mod_lt t hL
    have := Nat.mod_add_div t L
    nlinarith

end Normed

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma variableRelayedEqualNeighbor_fixed
    (G : Round → CommGraph n) (L : ℕ) (hL : 0 < L)
    (init : Proc n → V) :
    (variableRelayedEqualNeighbor G (fixedRelayingSchedule L hL) init).averaging =
      (AsymptoticSubspace.relayedEqualNeighbor G L init).averaging := by
  have hgraphs : (fun t => graphProduct G ((t - 1) * L) ((t - 1 + 1) * L - (t - 1) * L)) =
      (fun t => graphProduct G ((t - 1) * L) L) := by
    funext t
    congr 1
    rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left]
  exact congrArg (fun H => equalNeighborExecution H init) hgraphs

/-- Fixed-block refinement includes the completed-block count `t / L`. -/
theorem physicalEqualNeighbor_run_fixed
    (G : Round → CommGraph n) (L : ℕ) (hL : 0 < L)
    (init : Proc n → V) (t : ℕ) (i : Proc n) :
    (physicalEqualNeighbor (fixedRelayingSchedule L hL)).run G init t i =
      (AsymptoticSubspace.relayedEqualNeighbor G L init).outputs t i := by
  rw [physicalEqualNeighbor_run]
  simp only [VariableRelayingExecution.outputs, fixedRelayingSchedule_clock,
    AsymptoticSubspace.RelayingExecution.outputs, variableRelayedEqualNeighbor_fixed]

end AsymptoticSubspace.ComputationalModel
