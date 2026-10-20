/-
  WhoGetsLastWord/ReadoutDuality.lean
  Formalization of Theorem 3.4 (`thm:multiplicity` — Readout Duality and Synthesis Multiplicity):
  - Exact characterization of the In-Star terminal state profile `(s_s^(1), {s_i^(0)}_{i ≠ s})`
  - Exact characterization of the Dense terminal state profile `{s_i^(1)(G_dense)}_{i ∈ V}`
  - Sink component equality between both terminal profiles
  - Proof that any divergence under all-agent voting (`R_aa` / `R_orig`) arises solely from the
    `N - 1` non-sink recipient updates `{s_i^(1)(G_dense)}_{i ≠ s}`
  - Explicit, kernel-checked `N = 3` witness using the genuine voting functions where `R_sink` and
    `R_sp` agree between In-Star and Dense, but `R_aa` (and `R_orig`) diverge
  - Exact paired-correctness identity `E[Y_D - Y_S] = Pr(Y_D = 1, Y_S = 0) - Pr(Y_S = 1, Y_D = 0)`.
-/

import WhoGetsLastWord.FallbackDominance

namespace WhoGetsLastWord

/-! ## 1. Exact Composition of Terminal State Profiles -/

/-- Under `S_in(s)`, every non-sink agent `i ≠ s` retains its unupdated Round-0 state `state0 i`. -/
theorem inStar_nonSink_state_eq_state0 {N : Nat} {α μ ε π : Type}
    (s i : Fin N)
    (κ : PayloadFn N α μ ε π)
    (upd : UpdateFn N α μ ε π)
    (state0 : Fin N → AgentState α μ ε)
    (hi : i ≠ s) :
    stepOneRound (DirectedGraph.inStarGraph N s) κ upd state0 i = state0 i := by
  apply stepOneRound_nonRecipient_eq
  exact DirectedGraph.isRecipient_inStar_of_ne_sink s i hi

/-- Complete decomposition of the terminal state profile under `S_in(s)`:
    At `i = s` it equals the updated sink state (identical to `G_dense`), and at `i ≠ s`
    it equals the unupdated Round-0 leaf state `state0 i`. -/
theorem inStar_terminalProfile_characterization {N : Nat} {α μ ε π : Type}
    (s i : Fin N)
    (κ : PayloadFn N α μ ε π)
    (upd : UpdateFn N α μ ε π)
    (state0 : Fin N → AgentState α μ ε) :
    stepOneRound (DirectedGraph.inStarGraph N s) κ upd state0 i =
      if i = s then
        stepOneRound (DirectedGraph.denseGraph N) κ upd state0 s
      else
        state0 i := by
  by_cases hi : i = s
  · rcases hi.symm with rfl
    simp [sinkState_inStar_eq_dense s κ upd state0]
  · simp [hi, inStar_nonSink_state_eq_state0 s i κ upd state0 hi]

/-- Structural attribution theorem for Theorem 3.4:
    Because the sink component `s` is identical in `S_in(s)` and `G_dense`, if the `N - 1`
    non-sink updates in `G_dense` leave the non-sink states unchanged (`s_i^(1)(G_dense) = s_i^(0)`
    for all `i ≠ s`), then the entire terminal profiles coincide and `R_aa` returns the exact
    same answer on both topologies. -/
theorem R_aa_eq_if_nonSink_updates_unchanged {N : Nat} {α μ ε π : Type} [DecidableEq α]
    (s : Fin N)
    (κ : PayloadFn N α μ ε π)
    (upd : UpdateFn N α μ ε π)
    (state0 : Fin N → AgentState α μ ε)
    (hNonSink : ∀ i : Fin N, i ≠ s →
      stepOneRound (DirectedGraph.denseGraph N) κ upd state0 i = state0 i) :
    R_aa (stepOneRound (DirectedGraph.inStarGraph N s) κ upd state0) =
      R_aa (stepOneRound (DirectedGraph.denseGraph N) κ upd state0) := by
  have hProf :
      stepOneRound (DirectedGraph.inStarGraph N s) κ upd state0 =
        stepOneRound (DirectedGraph.denseGraph N) κ upd state0 := by
    funext i
    by_cases hi : i = s
    · rcases hi.symm with rfl
      exact sinkState_inStar_eq_dense s κ upd state0
    · rw [inStar_nonSink_state_eq_state0 s i κ upd state0 hi]
      exact (hNonSink i hi).symm
  rw [hProf]

/-! ## 2. Verified Counterexample: `R_sink` and `R_sp` Agree while `R_aa` Diverges -/

namespace DualityWitness

/-- Designated sink `s = 1` in a 3-agent network `V = {0, 1, 2}`. -/
def sink1 : Fin 3 := ⟨1, by decide⟩

/-- Shared Round-0 profile on `N = 3` agents:
    - Agent 0 (leaf): abstains (`noanswer`) on isolated shard 0
    - Agent 1 (sink): outputs partial misconception `.substantive 10`
    - Agent 2 (leaf): abstains (`noanswer`) on isolated shard 2 -/
def witnessState0 : Fin 3 → AgentState Nat Nat Nat
  | ⟨0, _⟩ => { answer := .noanswer, rationale := 100, confidence := 1, localEvidence := 0 }
  | ⟨1, _⟩ => { answer := .substantive 10, rationale := 101, confidence := 2, localEvidence := 1 }
  | ⟨2, _⟩ => { answer := .noanswer, rationale := 102, confidence := 1, localEvidence := 2 }

/-- Deterministic payload constructor transmitting each sender's Round-0 rationale. -/
def witnessPayload : PayloadFn 3 Nat Nat Nat Nat :=
  fun _ _ st => st.rationale

/-- Deterministic recipient update rule:
    - Sink 1 (`recipient = 1`) retains `.substantive 10`.
    - Non-sink agents (`recipient = 0` and `recipient = 2`), when updated with peer messages
      in `G_dense`, synthesize the cross-shard answer `.substantive 42`. -/
def witnessUpdate : UpdateFn 3 Nat Nat Nat Nat :=
  fun inp =>
    if inp.recipient.val = 1 then
      { answer := .substantive 10, rationale := 201, confidence := 3, localEvidence := inp.priorState.localEvidence }
    else
      { answer := .substantive 42, rationale := 242, confidence := 5, localEvidence := inp.priorState.localEvidence }

/-- Terminal profile under `S_in(1)`. -/
def profileStar : Fin 3 → AgentState Nat Nat Nat :=
  stepOneRound (DirectedGraph.inStarGraph 3 sink1) witnessPayload witnessUpdate witnessState0

/-- Terminal profile under `G_dense`. -/
def profileDense : Fin 3 → AgentState Nat Nat Nat :=
  stepOneRound (DirectedGraph.denseGraph 3) witnessPayload witnessUpdate witnessState0

/-- Theorem C-Witness (`readout_duality_verified_witness`):
    Using the genuine protocol execution `stepOneRound` and genuine voting operators:
    1. Sink 1's terminal state is identical under `S_in(1)` and `G_dense`.
    2. Fixed-Sink readout `R_sink` agrees (`Answer.substantive 10`).
    3. Sink-Priority Fallback `R_sp` agrees (`Answer.substantive 10`).
    4. All-Agent Abstention-Aware Vote `R_aa` strictly diverges:
       `R_aa(S_in(1)) = Answer.substantive 10` whereas `R_aa(G_dense) = Answer.substantive 42`. -/
theorem readout_duality_verified_witness :
    profileStar sink1 = profileDense sink1 ∧
    R_sink sink1 profileStar = .substantive 10 ∧
    R_sink sink1 profileDense = .substantive 10 ∧
    R_sp sink1 witnessState0 profileStar = .substantive 10 ∧
    R_sp sink1 witnessState0 profileDense = .substantive 10 ∧
    R_aa profileStar = .substantive 10 ∧
    R_aa profileDense = .substantive 42 ∧
    R_aa profileStar ≠ R_aa profileDense := by
  decide

end DualityWitness

/-! ## 3. Exact Paired-Correctness Identity -/

/-- Discordant Dense-win indicator: `1` if `Y_D = 1` and `Y_S = 0`, else `0`. -/
def denseWinDiscordant {α : Type} [DecidableEq α] (gold y_D y_S : Answer α) : Int :=
  if y_D = gold ∧ y_S ≠ gold then 1 else 0

/-- Discordant Star-win indicator: `1` if `Y_S = 1` and `Y_D = 0`, else `0`. -/
def starWinDiscordant {α : Type} [DecidableEq α] (gold y_D y_S : Answer α) : Int :=
  if y_S = gold ∧ y_D ≠ gold then 1 else 0

/-- Pointwise paired-correctness identity (Appendix A, Proof of Theorem 3.4):
    `Y(y_D) - Y(y_S) = I[y_D = y* ∧ y_S ≠ y*] - I[y_S = y* ∧ y_D ≠ y*]`. -/
theorem paired_correctness_pointwise_identity {α : Type} [DecidableEq α]
    (gold y_D y_S : Answer α) :
    (exactMatch gold y_D : Int) - (exactMatch gold y_S : Int) =
      denseWinDiscordant gold y_D y_S - starWinDiscordant gold y_D y_S := by
  unfold exactMatch denseWinDiscordant starWinDiscordant
  by_cases hD : y_D = gold <;> by_cases hS : y_S = gold <;> simp [hD, hS]

/-- Integer weighted sum over a finite query cohort `qs : List Q`. -/
def weightedSumInt {Q : Type} (qs : List Q) (w : Q → Int) (f : Q → Int) : Int :=
  match qs with
  | [] => 0
  | q :: rest => w q * f q + weightedSumInt rest w f

theorem weightedSumInt_sub {Q : Type} (qs : List Q) (w : Q → Int) (f g : Q → Int) :
    weightedSumInt qs w (fun q => f q - g q) =
      weightedSumInt qs w f - weightedSumInt qs w g := by
  induction qs with
  | nil => rfl
  | cons q rest ih =>
    unfold weightedSumInt
    rw [Int.mul_sub, ih]
    omega

/-- Expected paired-correctness identity across any finite query distribution `qs`:
    `E[Y(y_D) - Y(y_S)] = Pr(y_D = y*, y_S ≠ y*) - Pr(y_S = y*, y_D ≠ y*)`. -/
theorem expected_paired_correctness_identity {Q α : Type} [DecidableEq α]
    (qs : List Q)
    (w : Q → Int)
    (gold y_D y_S : Q → Answer α) :
    weightedSumInt qs w (fun q => (exactMatch (gold q) (y_D q) : Int) - (exactMatch (gold q) (y_S q) : Int)) =
      weightedSumInt qs w (fun q => denseWinDiscordant (gold q) (y_D q) (y_S q)) -
        weightedSumInt qs w (fun q => starWinDiscordant (gold q) (y_D q) (y_S q)) := by
  have hPt :
      (fun q => (exactMatch (gold q) (y_D q) : Int) - (exactMatch (gold q) (y_S q) : Int)) =
        (fun q => denseWinDiscordant (gold q) (y_D q) (y_S q) - starWinDiscordant (gold q) (y_D q) (y_S q)) := by
    funext q
    exact paired_correctness_pointwise_identity (gold q) (y_D q) (y_S q)
  rw [hPt]
  exact weightedSumInt_sub qs w _ _

end WhoGetsLastWord
