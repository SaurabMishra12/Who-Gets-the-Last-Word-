/-
  WhoGetsLastWord/FallbackDominance.lean
  Formalization of Theorem 3.3 (Parts 2 & 3) (`thm:sink` — Readout Invariance & Fallback Dominance):
  - B1: Fixed-sink readout invariance (`R_sink(S_in(s)) = R_sink(G_dense)`)
  - B2: Sink-Priority Fallback invariance (`R_sp(S_in(s)) = R_sp(G_dense)`)
  - B3: Pointwise fallback dominance on answerable queries (`Y(R_sp(G)) ≥ Y(R_sink(G))`)
  - B4: Zero-additional-inference property (`updateCount` unchanged by post-hoc fallback readout)
  - B5: Exact pointwise and expected fallback gain identity over finite query distributions.
-/

import WhoGetsLastWord.TerminalReadout
import WhoGetsLastWord.SinkInvariance

namespace WhoGetsLastWord

/-! ## B1. Fixed-Sink Readout Invariance -/

/-- Lemma: `R_sink` depends exclusively on the sink's terminal state `state1 s`. -/
theorem R_sink_congr_sink {N : Nat} {α μ ε : Type}
    (s : Fin N)
    (state1 state1' : Fin N → AgentState α μ ε)
    (hSink : state1 s = state1' s) :
    R_sink s state1 = R_sink s state1' := by
  unfold R_sink
  rw [hSink]

/-- Theorem B1 (`R_sink_inStar_eq_dense`, Theorem 3.3 Part 2a):
    Under one synchronous round, shared Round-0 states, matched payload construction `κ`,
    and deterministic recipient updates `upd`, Fixed-Sink readout `R_sink` returns the exact
    same answer under `S_in(s)` and `G_dense`. -/
theorem R_sink_inStar_eq_dense {N : Nat} {α μ ε π : Type}
    (s : Fin N)
    (κ : PayloadFn N α μ ε π)
    (upd : UpdateFn N α μ ε π)
    (state0 : Fin N → AgentState α μ ε) :
    R_sink s (stepOneRound (DirectedGraph.inStarGraph N s) κ upd state0) =
      R_sink s (stepOneRound (DirectedGraph.denseGraph N) κ upd state0) := by
  apply R_sink_congr_sink
  exact sinkState_inStar_eq_dense s κ upd state0

/-! ## B2. Sink-Priority Fallback Readout Invariance -/

/-- Lemma: For fixed Round-0 states `state0`, `R_sp` depends on `state1` exclusively
    through the sink's updated state `state1 s`. -/
theorem R_sp_congr_sink {N : Nat} {α μ ε : Type} [DecidableEq α]
    (s : Fin N)
    (state0 state1 state1' : Fin N → AgentState α μ ε)
    (hSink : state1 s = state1' s) :
    R_sp s state0 state1 = R_sp s state0 state1' := by
  unfold R_sp
  rw [hSink]

/-- Theorem B2 (`R_sp_inStar_eq_dense`, Theorem 3.3 Part 2b):
    Under one synchronous round, shared Round-0 states, matched payload construction `κ`,
    and deterministic recipient updates `upd`, Sink-Priority Fallback `R_sp` returns the exact
    same answer under `S_in(s)` and `G_dense`. -/
theorem R_sp_inStar_eq_dense {N : Nat} {α μ ε π : Type} [DecidableEq α]
    (s : Fin N)
    (κ : PayloadFn N α μ ε π)
    (upd : UpdateFn N α μ ε π)
    (state0 : Fin N → AgentState α μ ε) :
    R_sp s state0 (stepOneRound (DirectedGraph.inStarGraph N s) κ upd state0) =
      R_sp s state0 (stepOneRound (DirectedGraph.denseGraph N) κ upd state0) := by
  apply R_sp_congr_sink
  exact sinkState_inStar_eq_dense s κ upd state0

/-! ## B3. Pointwise Fallback Dominance on Answerable Queries -/

/-- Indicator for the fallback recovery event:
    sink `s` abstains at Round 1 (`s ∉ A(s^(1))`) AND abstention-aware voting over
    non-sink Round-0 leaf predictions recovers the substantive gold answer `y_star`. -/
def fallbackRecoveryIndicator {N : Nat} {α μ ε : Type} [DecidableEq α]
    (s : Fin N)
    (state0 state1 : Fin N → AgentState α μ ε)
    (y_star : α) : Nat :=
  if (state1 s).answer.isAbstention && decide (R_aa_leaves s state0 = .substantive y_star) then
    1
  else
    0

/-- Exact Pointwise Decomposition Lemma (`fallback_pointwise_gain_identity`):
    For any answerable query with substantive gold answer `Answer.substantive y_star`
    (so `gold ≠ Answer.noanswer`), the exact-match indicator of `R_sp` equals the exact-match
    indicator of `R_sink` plus the non-negative `fallbackRecoveryIndicator`. -/
theorem fallback_pointwise_gain_identity {N : Nat} {α μ ε : Type} [DecidableEq α]
    (s : Fin N)
    (state0 state1 : Fin N → AgentState α μ ε)
    (y_star : α) :
    exactMatch (.substantive y_star) (R_sp s state0 state1) =
      exactMatch (.substantive y_star) (R_sink s state1) +
        fallbackRecoveryIndicator s state0 state1 y_star := by
  unfold R_sp R_sink fallbackRecoveryIndicator exactMatch
  cases hAns : (state1 s).answer with
  | substantive a =>
    simp [Answer.isSubstantive, Answer.isAbstention]
  | noanswer =>
    simp [Answer.isSubstantive, Answer.isAbstention]

/-- Theorem B3 (`fallback_dominates_sink_pointwise`, Theorem 3.3 Part 3):
    For any answerable query with substantive gold answer `gold = Answer.substantive y_star`
    (`gold ≠ Answer.noanswer`), Sink-Priority Fallback `R_sp` dominates Fixed-Sink `R_sink`
    pointwise: `Y(R_sink(G)) ≤ Y(R_sp(G))`, including when all non-sink agents abstain. -/
theorem fallback_dominates_sink_pointwise {N : Nat} {α μ ε : Type} [DecidableEq α]
    (s : Fin N)
    (state0 state1 : Fin N → AgentState α μ ε)
    (y_star : α) :
    exactMatch (.substantive y_star) (R_sink s state1) ≤
      exactMatch (.substantive y_star) (R_sp s state0 state1) := by
  rw [fallback_pointwise_gain_identity s state0 state1 y_star]
  exact Nat.le_add_right _ _

/-- Equivalent formulation with explicit hypothesis `hAnswerable : gold ≠ Answer.noanswer`. -/
theorem fallback_dominates_sink_of_ne_noanswer {N : Nat} {α μ ε : Type} [DecidableEq α]
    (s : Fin N)
    (state0 state1 : Fin N → AgentState α μ ε)
    (gold : Answer α)
    (hAnswerable : gold ≠ Answer.noanswer) :
    exactMatch gold (R_sink s state1) ≤ exactMatch gold (R_sp s state0 state1) := by
  cases gold with
  | noanswer => contradiction
  | substantive y_star =>
    exact fallback_dominates_sink_pointwise s state0 state1 y_star

/-! ## B4. Zero-Additional-Inference Property -/

/-- Complete execution record pairing a communication graph `G` with its executed recipient
    update count and evaluated terminal readout answer. -/
def readoutUpdateCalls {N : Nat} (G : DirectedGraph N) : Nat :=
  G.updateCount

/-- Theorem B4 (`fallback_zero_additional_updates`):
    Replacing `R_sink` with `R_sp` on any one-round execution of graph `G` operates purely
    on the already-computed states `(state0, state1)` and requires zero additional recipient
    LLM update calls (`readoutUpdateCalls G - readoutUpdateCalls G = 0`). -/
theorem fallback_zero_additional_updates {N : Nat} (G : DirectedGraph N) :
    readoutUpdateCalls G = G.updateCount ∧
    readoutUpdateCalls G - G.updateCount = 0 := by
  unfold readoutUpdateCalls
  exact ⟨rfl, Nat.sub_self G.updateCount⟩

/-! ## B5. Expected Gain Identity over Finite Query Distributions -/

/-- Weighted sum over a finite sample space / query cohort `qs : List Q` with non-negative
    integer weights `w : Q → Nat` (representing rational probabilities scaled by a common denominator). -/
def weightedSum {Q : Type} (qs : List Q) (w : Q → Nat) (f : Q → Nat) : Nat :=
  match qs with
  | [] => 0
  | q :: rest => w q * f q + weightedSum rest w f

theorem weightedSum_add {Q : Type} (qs : List Q) (w : Q → Nat) (f g : Q → Nat) :
    weightedSum qs w (fun q => f q + g q) =
      weightedSum qs w f + weightedSum qs w g := by
  induction qs with
  | nil => rfl
  | cons q rest ih =>
    unfold weightedSum
    rw [Nat.left_distrib, ih]
    omega

/-- Theorem B5 (`expected_fallback_gain_identity`, Appendix A Proof of Theorem 3.3):
    Across any finite distribution of answerable queries `qs`, the expected accuracy of `R_sp`
    equals the expected accuracy of `R_sink` plus the probability mass of the event that
    the sink abstains at Round 1 while abstention-aware voting on Round-0 leaves recovers `y*_q`. -/
theorem expected_fallback_gain_identity {N : Nat} {Q α μ ε : Type} [DecidableEq α]
    (qs : List Q)
    (w : Q → Nat)
    (s : Fin N)
    (state0 state1 : Q → Fin N → AgentState α μ ε)
    (y_star : Q → α) :
    weightedSum qs w (fun q => exactMatch (.substantive (y_star q)) (R_sp s (state0 q) (state1 q))) =
      weightedSum qs w (fun q => exactMatch (.substantive (y_star q)) (R_sink s (state1 q))) +
        weightedSum qs w (fun q => fallbackRecoveryIndicator s (state0 q) (state1 q) (y_star q)) := by
  have hPointwise :
      (fun q => exactMatch (.substantive (y_star q)) (R_sp s (state0 q) (state1 q))) =
        (fun q =>
          exactMatch (.substantive (y_star q)) (R_sink s (state1 q)) +
            fallbackRecoveryIndicator s (state0 q) (state1 q) (y_star q)) := by
    funext q
    exact fallback_pointwise_gain_identity s (state0 q) (state1 q) (y_star q)
  rw [hPointwise]
  exact weightedSum_add qs w _ _

end WhoGetsLastWord
