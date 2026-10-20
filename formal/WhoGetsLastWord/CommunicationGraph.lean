/-
  WhoGetsLastWord/CommunicationGraph.lean
  Formalization of finite directed communication topologies, zero-diagonal channel space O,
  incoming/outgoing neighborhoods, recipient update set U(G) (Eq. 1),
  complete directed broadcast G_dense, and incoming-star topology S_in(s).
-/

namespace WhoGetsLastWord

/-- Canonical ascending list of all agent indices `0, 1, ..., N - 1` in `Fin N`. -/
def finRange : (N : Nat) → List (Fin N)
  | 0 => []
  | n + 1 =>
    (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) ::
      (finRange n).map (fun i => ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

/-- The length of `finRange N` is exactly `N`. -/
theorem length_finRange (N : Nat) : (finRange N).length = N := by
  induction N with
  | zero => rfl
  | succ n ih =>
    simp [finRange, ih]

/-- Every agent `i : Fin N` appears in the canonical ascending list `finRange N`. -/
theorem mem_finRange {N : Nat} (i : Fin N) : i ∈ finRange N := by
  induction N with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rcases i with ⟨val, isLt⟩
    cases val with
    | zero =>
      simp [finRange]
    | succ k =>
      simp only [finRange, List.mem_cons, List.mem_map]
      right
      refine ⟨⟨k, Nat.lt_of_succ_lt_succ isLt⟩, ih ⟨k, Nat.lt_of_succ_lt_succ isLt⟩, rfl⟩

/-- A directed communication graph on `N` agents is a zero-diagonal binary relation
    `G ⊆ O = {(i, j) ∈ V × V : i ≠ j}`. -/
structure DirectedGraph (N : Nat) where
  adj : Fin N → Fin N → Bool
  loopless : ∀ i : Fin N, adj i i = false

namespace DirectedGraph

/-- Boolean predicate for whether `i` is an incoming neighbor of `j` in `G` (`(i, j) ∈ G`). -/
def isInNeighbor {N : Nat} (G : DirectedGraph N) (j i : Fin N) : Bool :=
  G.adj i j

/-- Boolean predicate for whether `j` is an outgoing neighbor of `i` in `G` (`(i, j) ∈ G`). -/
def isOutNeighbor {N : Nat} (G : DirectedGraph N) (i j : Fin N) : Bool :=
  G.adj i j

/-- Ordered list of incoming neighbors `N_in(j; G) = {i ∈ V : (i, j) ∈ G}` in ascending agent order. -/
def inNeighbors {N : Nat} (G : DirectedGraph N) (j : Fin N) : List (Fin N) :=
  (finRange N).filter (fun i => G.isInNeighbor j i)

/-- Ordered list of outgoing neighbors `N_out(i; G) = {j ∈ V : (i, j) ∈ G}` in ascending agent order. -/
def outNeighbors {N : Nat} (G : DirectedGraph N) (i : Fin N) : List (Fin N) :=
  (finRange N).filter (fun j => G.isOutNeighbor i j)

/-- Equation (1) (`eq:updated_nodes`): Agent `j` executes a recipient LLM update iff
    there exists a sender `i ∈ V` such that `(i, j) ∈ G`. -/
def isRecipient {N : Nat} (G : DirectedGraph N) (j : Fin N) : Bool :=
  (finRange N).any (fun i => G.isInNeighbor j i)

/-- Ordered list of updated recipient agents `U(G) = {j ∈ V : ∃ i ∈ V, (i, j) ∈ G}`. -/
def recipientSet {N : Nat} (G : DirectedGraph N) : List (Fin N) :=
  (finRange N).filter (fun j => G.isRecipient j)

/-- All ordered pairs of agents `(i, j) ∈ V × V`. -/
def allPairs (N : Nat) : List (Fin N × Fin N) :=
  (finRange N).foldr (fun i acc => (finRange N).map (fun j => (i, j)) ++ acc) []

/-- Off-diagonal channel space `O = {(i, j) ∈ V × V : i ≠ j}`. -/
def offDiagChannels (N : Nat) : List (Fin N × Fin N) :=
  (allPairs N).filter (fun p => !(decide (p.1 = p.2)))

/-- Active directed edges `G ⊆ O` listed in canonical lexicographic order. -/
def edgeList {N : Nat} (G : DirectedGraph N) : List (Fin N × Fin N) :=
  (allPairs N).filter (fun p => G.adj p.1 p.2)

/-- Directed delivery count `|G|`. -/
def deliveryCount {N : Nat} (G : DirectedGraph N) : Nat :=
  (G.edgeList).length

/-- Recipient LLM update count `|U(G)|`. -/
def updateCount {N : Nat} (G : DirectedGraph N) : Nat :=
  (G.recipientSet).length

/-- Characterization of Equation (1): `j ∈ U(G)` iff `isRecipient G j = true`. -/
theorem mem_recipientSet_iff {N : Nat} (G : DirectedGraph N) (j : Fin N) :
    j ∈ G.recipientSet ↔ G.isRecipient j = true := by
  unfold recipientSet
  simp [List.mem_filter, mem_finRange j]

/-- Complete directed broadcast graph `G_dense = O = {(i, j) : i ≠ j}`. -/
def denseGraph (N : Nat) : DirectedGraph N where
  adj := fun i j => !(decide (i = j))
  loopless := by
    intro i
    simp

/-- Incoming-star graph `S_in(s) = {(i, s) : i ≠ s}` targeting designated sink `s`. -/
def inStarGraph (N : Nat) (s : Fin N) : DirectedGraph N where
  adj := fun i j => !(decide (i = s)) && decide (j = s)
  loopless := by
    intro i
    by_cases h : i = s
    · subst h
      simp
    · simp [h]

/-- No-communication empty graph `G_empty = ∅`. -/
def emptyGraph (N : Nat) : DirectedGraph N where
  adj := fun _ _ => false
  loopless := fun _ => rfl

/-- Outgoing-star graph `S_out(r) = {(r, j) : j ≠ r}` from designated root `r`. -/
def outStarGraph (N : Nat) (r : Fin N) : DirectedGraph N where
  adj := fun i j => decide (i = r) && !(decide (j = r))
  loopless := by
    intro i
    by_cases h : i = r
    · subst h
      simp
    · simp [h]

/-- Non-sink agents in `inStarGraph N s` have no incoming neighbors. -/
theorem isInNeighbor_inStar_of_ne_sink {N : Nat} (s j i : Fin N) (hj : j ≠ s) :
    (inStarGraph N s).isInNeighbor j i = false := by
  unfold isInNeighbor inStarGraph
  simp [hj]

/-- Non-sink agents in `inStarGraph N s` do not execute a recipient update (`j ∉ U(S_in(s))`). -/
theorem isRecipient_inStar_of_ne_sink {N : Nat} (s j : Fin N) (hj : j ≠ s) :
    (inStarGraph N s).isRecipient j = false := by
  unfold isRecipient
  have hFalse : (fun i => (inStarGraph N s).isInNeighbor j i) = (fun _ => false) := by
    funext i
    exact isInNeighbor_inStar_of_ne_sink s j i hj
  rw [hFalse]
  induction (finRange N) with
  | nil => rfl
  | cons x xs ih => exact ih

end DirectedGraph
end WhoGetsLastWord
