/-
  WhoGetsLastWord/Counterexamples.lean
  Adversarial verification and checked counterexamples validating the tightness of every
  formal assumption in the manuscript (Section 11 requirements):
  1. Two-round execution (`T = 2`) where updated non-sink messages break sink invariance.
  2. Nondeterministic recipient updates where equal inputs do not guarantee identical outputs.
  3. Different message orderings producing different serialized sink inputs and sink states.
  4. An unanswerable query (`y* = noanswer`) where fallback dominance over fixed-sink fails.
  5. Identical fixed-sink (`R_sink`) and fallback (`R_sp`) outputs but divergent all-agent
     voting (`R_aa` and `R_orig`) outputs.
  6. Equal nominal token caps (`V_bar`) with unequal realized transmitted volume (`Vol`).
  7. Equal transmitted-token volume (`Vol`) with different message contents and accuracy.
  8. Cases where additional recipient updates in Dense broadcast strictly degrade accuracy
     relative to In-Star (non-monotonicity of accuracy in update count).
-/

import WhoGetsLastWord.SinkInvariance
import WhoGetsLastWord.FallbackDominance
import WhoGetsLastWord.ReadoutDuality
import WhoGetsLastWord.AbstentionVeto
import WhoGetsLastWord.VolumeAccounting

namespace WhoGetsLastWord
namespace Counterexamples

/-- Designated sink `s = 1` in `Fin 3`. -/
def sink1 : Fin 3 := ⟨1, by decide⟩

/-! ## Counterexample 1: Two-Round Execution (`T = 2`) Breaks Sink Invariance -/

/-- Round-0 profile where leaf 0 holds rationale `10`, sink 1 holds `0`, leaf 2 holds `20`. -/
def twoRoundState0 : Fin 3 → AgentState Nat Nat Nat
  | ⟨0, _⟩ => { answer := .substantive 1, rationale := 10, confidence := 1, localEvidence := 0 }
  | ⟨1, _⟩ => { answer := .noanswer, rationale := 0, confidence := 1, localEvidence := 1 }
  | ⟨2, _⟩ => { answer := .substantive 2, rationale := 20, confidence := 1, localEvidence := 2 }

/-- Payload function transmitting the sender's current rationale. -/
def rationalePayload : PayloadFn 3 Nat Nat Nat Nat :=
  fun _ _ st => st.rationale

/-- Sum of payload values in an incoming message list. -/
def sumPayloads : List (DeliveredMessage 3 Nat) → Nat
  | [] => 0
  | m :: ms => m.payload + sumPayloads ms

/-- Recipient update rule that adds the sum of incoming rationales to the agent's rationale
    and sets the answer to that sum. -/
def sumRationaleUpdate : UpdateFn 3 Nat Nat Nat Nat :=
  fun inp =>
    let newRat := inp.priorState.rationale + sumPayloads inp.incomingMessages
    { answer := .substantive newRat
      rationale := newRat
      confidence := inp.priorState.confidence + 1
      localEvidence := inp.priorState.localEvidence }

/-- Two-round execution (`T = 2`) on graph `G`. -/
def stepTwoRounds (G : DirectedGraph 3) : Fin 3 → AgentState Nat Nat Nat :=
  runRounds rationalePayload sumRationaleUpdate twoRoundState0 [G, G]

/-- Counterexample 1 Theorem (`two_round_breaks_sink_invariance`):
    At Round 1 (`T = 1`), Sink 1's state is identical under `S_in(1)` and `G_dense` (`rationale = 30`).
    At Round 2 (`T = 2`), because `G_dense` updated leaves 0 and 2 at Round 1 (changing their
    rationales from `10, 20` to `30, 30`) while `S_in(1)` left them at `10, 20`, Sink 1's Round-2
    state under `S_in(1)` (`60`) diverges from Sink 1's Round-2 state under `G_dense` (`90`). -/
theorem two_round_breaks_sink_invariance :
    stepOneRound (DirectedGraph.inStarGraph 3 sink1) rationalePayload sumRationaleUpdate twoRoundState0 sink1 =
      stepOneRound (DirectedGraph.denseGraph 3) rationalePayload sumRationaleUpdate twoRoundState0 sink1 ∧
    (stepTwoRounds (DirectedGraph.inStarGraph 3 sink1) sink1).answer = .substantive 60 ∧
    (stepTwoRounds (DirectedGraph.denseGraph 3) sink1).answer = .substantive 90 ∧
    stepTwoRounds (DirectedGraph.inStarGraph 3 sink1) sink1 ≠
      stepTwoRounds (DirectedGraph.denseGraph 3) sink1 := by
  decide

/-! ## Counterexample 2: Nondeterministic Decoding Breaks Sink Output Invariance -/

/-- Nondeterministic recipient update parameterized by an execution seed / sampling draw `seed : Nat`. -/
def stochasticUpdate (seed : Nat) (inp : RecipientUpdateInput 3 Nat Nat Nat Nat) :
    AgentState Nat Nat Nat :=
  { answer := .substantive (sumPayloads inp.incomingMessages + seed)
    rationale := sumPayloads inp.incomingMessages + seed
    confidence := 1
    localEvidence := inp.priorState.localEvidence }

/-- Counterexample 2 Theorem (`nondeterministic_decoding_breaks_sink_invariance`):
    Even though the sink's update input is identical under `S_in(1)` and `G_dense`,
    if decoding is nondeterministic (`seed = 0` vs `seed = 1`, e.g. `T_dec > 0` without fixed seed),
    the realized sink predictions differ. -/
theorem nondeterministic_decoding_breaks_sink_invariance :
    let inpStar := buildRecipientInput (DirectedGraph.inStarGraph 3 sink1) rationalePayload twoRoundState0 sink1
    let inpDense := buildRecipientInput (DirectedGraph.denseGraph 3) rationalePayload twoRoundState0 sink1
    inpStar = inpDense ∧
    stochasticUpdate 0 inpStar ≠ stochasticUpdate 1 inpDense := by
  decide

/-! ## Counterexample 3: Permuted Incoming-Message Ordering Alters Serialized Sink Input -/

/-- Collects incoming messages in reverse (descending) sender index order rather than ascending. -/
def collectIncomingMessagesDesc (G : DirectedGraph 3)
    (κ : PayloadFn 3 Nat Nat Nat Nat)
    (priorProfile : Fin 3 → AgentState Nat Nat Nat)
    (j : Fin 3) : List (DeliveredMessage 3 Nat) :=
  (collectIncomingMessages G κ priorProfile j).reverse

/-- Order-sensitive prompt serializer / decoder (`2 * first_payload + second_payload`). -/
def orderSensitiveSerializer : List (DeliveredMessage 3 Nat) → Nat
  | [] => 0
  | m :: ms => m.payload + 2 * orderSensitiveSerializer ms

/-- Counterexample 3 Theorem (`message_ordering_breaks_prompt_invariance`):
    For Sink 1 receiving distinct payloads `10` (from Agent 0) and `20` (from Agent 2),
    ascending sender order `[0, 2]` and descending sender order `[2, 0]` have the exact same
    sender set `{0, 2}` but produce distinct ordered message lists and distinct serialized prompts. -/
theorem message_ordering_breaks_prompt_invariance :
    let ascMsgs := collectIncomingMessages (DirectedGraph.inStarGraph 3 sink1) rationalePayload twoRoundState0 sink1
    let descMsgs := collectIncomingMessagesDesc (DirectedGraph.inStarGraph 3 sink1) rationalePayload twoRoundState0 sink1
    ascMsgs ≠ descMsgs ∧
    orderSensitiveSerializer ascMsgs ≠ orderSensitiveSerializer descMsgs := by
  decide

/-! ## Counterexample 4: Unanswerable Query (`gold = noanswer`) Breaks Fallback Dominance -/

/-- Round-0 state where leaf 0 hallucinates `.substantive 99` on an unanswerable query. -/
def unanswerableState0 : Fin 3 → AgentState Nat Nat Nat
  | ⟨0, _⟩ => { answer := .substantive 99, rationale := 1, confidence := 1, localEvidence := 0 }
  | ⟨1, _⟩ => { answer := .noanswer, rationale := 0, confidence := 1, localEvidence := 1 }
  | ⟨2, _⟩ => { answer := .noanswer, rationale := 0, confidence := 1, localEvidence := 2 }

/-- Round-1 state where Sink 1 rightly abstains (`.noanswer`). -/
def unanswerableState1 : Fin 3 → AgentState Nat Nat Nat := unanswerableState0

/-- Counterexample 4 Theorem (`unanswerable_query_breaks_fallback_dominance`):
    When the target gold label is `Answer.noanswer` (unanswerable benchmark query),
    Fixed-Sink `R_sink` achieves accuracy `1` when Sink 1 abstains, whereas `R_sp` falls back
    to leaf 0's hallucinated substantive answer `.substantive 99` and gets accuracy `0 < 1`.
    Thus the hypothesis `y*_q ≠ noanswer` in Theorem 3.3(3) is strictly necessary. -/
theorem unanswerable_query_breaks_fallback_dominance :
    R_sink sink1 unanswerableState1 = .noanswer ∧
    R_sp sink1 unanswerableState0 unanswerableState1 = .substantive 99 ∧
    exactMatch .noanswer (R_sp sink1 unanswerableState0 unanswerableState1) <
      exactMatch .noanswer (R_sink sink1 unanswerableState1) := by
  decide

/-! ## Counterexample 5: Fixed-Sink & Fallback Agree while Both `R_aa` and `R_orig` Diverge -/

/-- Counterexample 5 Theorem (`fixed_sink_agrees_all_agent_votes_diverge`):
    On the `DualityWitness` instance from `ReadoutDuality.lean`, `R_sink` and `R_sp` are
    identical between `S_in(1)` and `G_dense`, while both `R_aa` and `R_orig` diverge. -/
theorem fixed_sink_agrees_all_agent_votes_diverge :
    R_sink sink1 DualityWitness.profileStar = R_sink sink1 DualityWitness.profileDense ∧
    R_sp sink1 DualityWitness.witnessState0 DualityWitness.profileStar =
      R_sp sink1 DualityWitness.witnessState0 DualityWitness.profileDense ∧
    R_aa DualityWitness.profileStar ≠ R_aa DualityWitness.profileDense ∧
    R_orig DualityWitness.profileStar ≠ R_orig DualityWitness.profileDense := by
  decide

/-! ## Counterexample 6: Equal Nominal Token Caps (`V_bar`) with Unequal Realized Volume -/

/-- Realized channel length under per-edge truncation ceiling `b = V_bar / |T|`:
    `min(rawLen, b)`. -/
def truncatedEdgeLen (rawLen capPerEdge : Nat) : Nat :=
  if rawLen ≤ capPerEdge then rawLen else capPerEdge

/-- Total realized volume across active edges under nominal budget `V_bar = 60`
    when Agent 0 has a 50-token message and Agents 1, 2 have 10-token messages:
    - Under 2-edge Out-Star from Agent 0 (`0 → 1, 0 → 2`, `b = 60 / 2 = 30` per edge),
      each edge transmits `min(50, 30) = 30` tokens, giving realized volume `60`.
    - Under 2-edge In-Star to Sink 1 (`0 → 1, 2 → 1`, `b = 60 / 2 = 30` per edge),
      edge `0 → 1` transmits `min(50, 30) = 30` tokens and edge `2 → 1` transmits
      `min(10, 30) = 10` tokens, giving realized volume `40 ≠ 60`. -/
def realizedVolOutStar0 (vBar : Nat) : Nat :=
  let b := vBar / 2
  truncatedEdgeLen 50 b + truncatedEdgeLen 50 b

def realizedVolInStar1 (vBar : Nat) : Nat :=
  let b := vBar / 2
  truncatedEdgeLen 50 b + truncatedEdgeLen 10 b

/-- Counterexample 6 Theorem (`equal_nominal_cap_unequal_realized_volume`):
    Matching nominal token ceiling `V_bar = 60` and even matching support cardinality `|T| = 2`
    does not equalize realized communication volume (`60 ≠ 40`). -/
theorem equal_nominal_cap_unequal_realized_volume :
    realizedVolOutStar0 60 = 60 ∧
    realizedVolInStar1 60 = 40 ∧
    realizedVolOutStar0 60 ≠ realizedVolInStar1 60 := by
  decide

/-! ## Counterexample 7: Equal Transmitted Token Volume with Different Message Contents -/

/-- Payload constructor A (order-preserving prefix of length 128 tokens carrying bridge entity `42`). -/
def prefixPayload128 : PayloadFn 3 Nat ( Nat × Nat ) Nat ( Nat × Nat ) :=
  fun _ _ st => (128, st.rationale.1)

/-- Payload constructor B (contiguous crop of length 128 tokens carrying distractor entity `99`). -/
def cropPayload128 : PayloadFn 3 Nat ( Nat × Nat ) Nat ( Nat × Nat ) :=
  fun _ _ st => (128, st.rationale.2)

/-- Round-0 profile where each rationale has prefix entity `42` and crop entity `99`. -/
def rationingState0 : Fin 3 → AgentState Nat ( Nat × Nat ) Nat
  | ⟨0, _⟩ => { answer := .noanswer, rationale := (42, 99), confidence := 1, localEvidence := 0 }
  | ⟨1, _⟩ => { answer := .noanswer, rationale := (42, 99), confidence := 1, localEvidence := 1 }
  | ⟨2, _⟩ => { answer := .noanswer, rationale := (42, 99), confidence := 1, localEvidence := 2 }

/-- Sum of realized token counts (`.1`) across delivered messages. -/
def deliveredTokenSum : List (DeliveredMessage 3 ( Nat × Nat )) → Nat
  | [] => 0
  | m :: ms => m.payload.1 + deliveredTokenSum ms

/-- Update rule adopting the semantic entity (`.2`) of the first incoming message. -/
def rationingUpdate : UpdateFn 3 Nat ( Nat × Nat ) Nat ( Nat × Nat ) :=
  fun inp =>
    match inp.incomingMessages with
    | [] => inp.priorState
    | m :: _ =>
      { answer := .substantive m.payload.2
        rationale := inp.priorState.rationale
        confidence := 2
        localEvidence := inp.priorState.localEvidence }

/-- Counterexample 7 Theorem (`equal_realized_volume_different_semantic_outcomes`):
    Under `S_in(1)`, `prefixPayload128` and `cropPayload128` transmit the exact same realized
    token volume (`256` tokens across `2` deliveries), yet induce distinct sink predictions
    (`.substantive 42` vs `.substantive 99`) and distinct exact-match accuracies (`1` vs `0`). -/
theorem equal_realized_volume_different_semantic_outcomes :
    let msgsPrefix := collectIncomingMessages (DirectedGraph.inStarGraph 3 sink1) prefixPayload128 rationingState0 sink1
    let msgsCrop := collectIncomingMessages (DirectedGraph.inStarGraph 3 sink1) cropPayload128 rationingState0 sink1
    let statePrefix := stepOneRound (DirectedGraph.inStarGraph 3 sink1) prefixPayload128 rationingUpdate rationingState0
    let stateCrop := stepOneRound (DirectedGraph.inStarGraph 3 sink1) cropPayload128 rationingUpdate rationingState0
    deliveredTokenSum msgsPrefix = 256 ∧
    deliveredTokenSum msgsCrop = 256 ∧
    deliveredTokenSum msgsPrefix = deliveredTokenSum msgsCrop ∧
    R_sink sink1 statePrefix = .substantive 42 ∧
    R_sink sink1 stateCrop = .substantive 99 ∧
    exactMatch (.substantive 42) (R_sink sink1 statePrefix) = 1 ∧
    exactMatch (.substantive 42) (R_sink sink1 stateCrop) = 0 := by
  decide

/-! ## Counterexample 8: Additional Recipient Updates Can Strictly Degrade Accuracy -/

/-- Round-0 profile where all non-sink leaves abstain (`noanswer`), while Sink 1 after update
    resolves the gold answer `.substantive 42`, but non-sink agents when updated in `G_dense`
    adopt a shared misconception `.substantive 99`. -/
def overupdateState0 : Fin 3 → AgentState Nat Nat Nat
  | ⟨0, _⟩ => { answer := .noanswer, rationale := 1, confidence := 1, localEvidence := 0 }
  | ⟨1, _⟩ => { answer := .noanswer, rationale := 2, confidence := 1, localEvidence := 1 }
  | ⟨2, _⟩ => { answer := .noanswer, rationale := 3, confidence := 1, localEvidence := 2 }

def overupdateRule : UpdateFn 3 Nat Nat Nat Nat :=
  fun inp =>
    if inp.recipient.val = 1 then
      { answer := .substantive 42, rationale := 42, confidence := 5, localEvidence := inp.priorState.localEvidence }
    else
      { answer := .substantive 99, rationale := 99, confidence := 2, localEvidence := inp.priorState.localEvidence }

/-- Counterexample 8 Theorem (`additional_updates_can_degrade_voting_accuracy`):
    With gold answer `.substantive 42`, `S_in(1)` (1 recipient update) achieves `R_aa` accuracy `1`
    (`.substantive 42`), whereas `G_dense` (3 recipient updates) causes the two updated non-sink
    agents to outvote Sink 1 with `.substantive 99`, reducing `R_aa` accuracy from `1` to `0`. -/
theorem additional_updates_can_degrade_voting_accuracy :
    let profStar := stepOneRound (DirectedGraph.inStarGraph 3 sink1) rationalePayload overupdateRule overupdateState0
    let profDense := stepOneRound (DirectedGraph.denseGraph 3) rationalePayload overupdateRule overupdateState0
    (DirectedGraph.inStarGraph 3 sink1).updateCount = 1 ∧
    (DirectedGraph.denseGraph 3).updateCount = 3 ∧
    exactMatch (.substantive 42) (R_aa profStar) = 1 ∧
    exactMatch (.substantive 42) (R_aa profDense) = 0 ∧
    exactMatch (.substantive 42) (R_aa profDense) < exactMatch (.substantive 42) (R_aa profStar) := by
  decide

end Counterexamples
end WhoGetsLastWord
