/-
  WhoGetsLastWord/Protocol.lean
  Formalization of agent state space, normalized answers with abstention (`noanswer`),
  deterministic outgoing payload construction κ, canonical ordered message collection,
  and synchronous 1-round (and multi-round) execution contracts (§3.1).
-/

import WhoGetsLastWord.CommunicationGraph

namespace WhoGetsLastWord

/-- Normalized agent answer type (§3.1, §3.3): either the abstention token `noanswer`
    (including empty/refused normalizations) or a substantive normalized answer `a : α`. -/
inductive Answer (α : Type) where
  | noanswer : Answer α
  | substantive : α → Answer α
  deriving DecidableEq, Repr

namespace Answer

/-- Predicate testing whether an answer is substantive (`y ∉ {∅, noanswer}`). -/
def isSubstantive {α : Type} : Answer α → Bool
  | .noanswer => false
  | .substantive _ => true

/-- Predicate testing whether an answer is the abstention token (`y = noanswer`). -/
def isAbstention {α : Type} : Answer α → Bool
  | .noanswer => true
  | .substantive _ => false

theorem isSubstantive_eq_true_iff {α : Type} (y : Answer α) :
    y.isSubstantive = true ↔ y ≠ .noanswer := by
  cases y with
  | noanswer => simp [isSubstantive]
  | substantive a => simp [isSubstantive]

theorem isAbstention_eq_true_iff {α : Type} (y : Answer α) :
    y.isAbstention = true ↔ y = .noanswer := by
  cases y with
  | noanswer => simp [isAbstention]
  | substantive a => simp [isAbstention]

theorem isSubstantive_not_isAbstention {α : Type} (y : Answer α) :
    y.isSubstantive = !y.isAbstention := by
  cases y <;> rfl

end Answer

/-- Exact-match correctness indicator `Y(y_hat) ∈ {0, 1}` against gold answer `gold`. -/
def exactMatch {α : Type} [DecidableEq α] (gold pred : Answer α) : Nat :=
  if pred = gold then 1 else 0

theorem exactMatch_le_one {α : Type} [DecidableEq α] (gold pred : Answer α) :
    exactMatch gold pred ≤ 1 := by
  unfold exactMatch
  by_cases h : pred = gold <;> simp [h]

theorem exactMatch_eq_one_iff {α : Type} [DecidableEq α] (gold pred : Answer α) :
    exactMatch gold pred = 1 ↔ pred = gold := by
  unfold exactMatch
  by_cases h : pred = gold <;> simp [h]

theorem exactMatch_eq_zero_iff {α : Type} [DecidableEq α] (gold pred : Answer α) :
    exactMatch gold pred = 0 ↔ pred ≠ gold := by
  unfold exactMatch
  by_cases h : pred = gold <;> simp [h]

theorem exactMatch_noanswer_of_substantive_gold {α : Type} [DecidableEq α] (y_star : α) :
    exactMatch (.substantive y_star) .noanswer = 0 := by
  unfold exactMatch
  simp

/-- Agent state `s_i^(r) = (y_i^(r), m_i^(r), c_i^(r), D_{q,i})` (§3.1):
    - `answer`: normalized answer `y_i^(r)` (substantive or `noanswer`)
    - `rationale`: message rationale `m_i^(r)`
    - `confidence`: confidence score `c_i^(r)`
    - `localEvidence`: local retrieved passage shard `D_{q,i}` -/
structure AgentState (α μ ε : Type) where
  answer : Answer α
  rationale : μ
  confidence : Nat
  localEvidence : ε
  deriving DecidableEq, Repr

/-- Directed message delivered along active edge `(sender, recipient)` at round `r`. -/
structure DeliveredMessage (N : Nat) (π : Type) where
  sender : Fin N
  payload : π
  deriving DecidableEq, Repr

/-- Deterministic outgoing payload constructor `κ`:
    Maps sender `i`, recipient `j`, and sender's prior state `s_i^(r-1)` to the filtered/truncated
    channel payload `m_tilde_{ij}^(r) = κ(m_i^(r-1), W_{ij}^(r); b)`. -/
abbrev PayloadFn (N : Nat) (α μ ε π : Type) :=
  Fin N → Fin N → AgentState α μ ε → π

/-- Collects all incoming payloads for recipient `j` in canonical ascending sender index order. -/
def collectIncomingMessages {N : Nat} {α μ ε π : Type}
    (G : DirectedGraph N)
    (κ : PayloadFn N α μ ε π)
    (priorProfile : Fin N → AgentState α μ ε)
    (j : Fin N) : List (DeliveredMessage N π) :=
  (G.inNeighbors j).map (fun i => { sender := i, payload := κ i j (priorProfile i) })

/-- Complete serialized or structured input supplied to recipient `j`'s LLM update call (§3.1):
    depends exclusively on recipient index `j`, prior state `s_j^(r-1)` (including local shard `D_{q,j}`),
    and ordered incoming messages `{m_tilde_{ij}^(r)}_{(i,j) ∈ G}`. -/
structure RecipientUpdateInput (N : Nat) (α μ ε π : Type) where
  recipient : Fin N
  priorState : AgentState α μ ε
  incomingMessages : List (DeliveredMessage N π)
  deriving DecidableEq, Repr

/-- Constructs the recipient update input for agent `j` under graph `G`. -/
def buildRecipientInput {N : Nat} {α μ ε π : Type}
    (G : DirectedGraph N)
    (κ : PayloadFn N α μ ε π)
    (priorProfile : Fin N → AgentState α μ ε)
    (j : Fin N) : RecipientUpdateInput N α μ ε π :=
  { recipient := j
    priorState := priorProfile j
    incomingMessages := collectIncomingMessages G κ priorProfile j }

/-- Deterministic recipient transition function modeling temperature-zero (`T_dec = 0`) decoding. -/
abbrev UpdateFn (N : Nat) (α μ ε π : Type) :=
  RecipientUpdateInput N α μ ε π → AgentState α μ ε

/-- One synchronous communication round (`r → r + 1`, §3.1):
    - Recipients `j ∈ U(G)` compute `s_j^(r)` via `upd (buildRecipientInput G κ priorProfile j)`.
    - Non-recipients `j ∉ U(G)` retain `s_j^(r) = s_j^(r-1)` without invoking the model. -/
def stepOneRound {N : Nat} {α μ ε π : Type}
    (G : DirectedGraph N)
    (κ : PayloadFn N α μ ε π)
    (upd : UpdateFn N α μ ε π)
    (state0 : Fin N → AgentState α μ ε) : Fin N → AgentState α μ ε :=
  fun j =>
    if G.isRecipient j then
      upd (buildRecipientInput G κ state0 j)
    else
      state0 j

/-- Multi-round synchronous execution over a sequence of round graphs `[G^(1), ..., G^(T)]`. -/
def runRounds {N : Nat} {α μ ε π : Type}
    (κ : PayloadFn N α μ ε π)
    (upd : UpdateFn N α μ ε π)
    (state0 : Fin N → AgentState α μ ε) : List (DirectedGraph N) → (Fin N → AgentState α μ ε)
  | [] => state0
  | G :: Gs => runRounds κ upd (stepOneRound G κ upd state0) Gs

/-- Non-recipient preservation lemma: any agent `j` with `G.isRecipient j = false`
    preserves its prior state identically after `stepOneRound`. -/
theorem stepOneRound_nonRecipient_eq {N : Nat} {α μ ε π : Type}
    (G : DirectedGraph N)
    (κ : PayloadFn N α μ ε π)
    (upd : UpdateFn N α μ ε π)
    (state0 : Fin N → AgentState α μ ε)
    (j : Fin N)
    (hNonRec : G.isRecipient j = false) :
    stepOneRound G κ upd state0 j = state0 j := by
  unfold stepOneRound
  rw [hNonRec]
  rfl

/-- Recipient update lemma: any agent `j` with `G.isRecipient j = true`
    updates its state via `upd (buildRecipientInput G κ state0 j)`. -/
theorem stepOneRound_recipient_eq {N : Nat} {α μ ε π : Type}
    (G : DirectedGraph N)
    (κ : PayloadFn N α μ ε π)
    (upd : UpdateFn N α μ ε π)
    (state0 : Fin N → AgentState α μ ε)
    (j : Fin N)
    (hRec : G.isRecipient j = true) :
    stepOneRound G κ upd state0 j = upd (buildRecipientInput G κ state0 j) := by
  unfold stepOneRound
  rw [hRec]
  rfl

end WhoGetsLastWord
