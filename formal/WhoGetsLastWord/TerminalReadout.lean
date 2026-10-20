/-
  WhoGetsLastWord/TerminalReadout.lean
  Formalization of Definition 3.2 (`def:readouts`) and Equation (4) (`eq:sp_fallback`):
  - Active non-abstaining voter set A(s)
  - Plurality voting with deterministic tie-breaking by ascending agent index
  - (1) Original Plurality Vote (`R_orig`)
  - (2) Abstention-Aware Plurality Vote (`R_aa`)
  - (3) Fixed-Sink Readout (`R_sink`)
  - (4) Sink-Priority Fallback (`R_sp`)
-/

import WhoGetsLastWord.Protocol

namespace WhoGetsLastWord

/-- Vote count for candidate answer `c` among a list of eligible `voters`. -/
def voteCount {N : Nat} {α : Type} [DecidableEq α]
    (voters : List (Fin N)) (ans : Fin N → Answer α) (c : Answer α) : Nat :=
  (voters.filter (fun i => decide (ans i = c))).length

/-- Auxiliary left-to-right scan implementing deterministic tie-breaking by ascending agent index:
    because `voters` is ordered by ascending agent index, replacing `bestAns` strictly when
    `bestCnt < cnt` preserves the earliest-index candidate among all maximum-vote answers. -/
def pickPluralityWinnerAux {N : Nat} {α : Type} [DecidableEq α]
    (allVoters : List (Fin N)) (ans : Fin N → Answer α)
    (bestAns : Answer α) (bestCnt : Nat) : List (Fin N) → Answer α
  | [] => bestAns
  | v :: vs =>
    let cnt := voteCount allVoters ans (ans v)
    if bestCnt < cnt then
      pickPluralityWinnerAux allVoters ans (ans v) cnt vs
    else
      pickPluralityWinnerAux allVoters ans bestAns bestCnt vs

/-- Plurality vote over `voters` (assumed ordered by ascending agent index),
    returning `Answer.noanswer` when `voters` is empty. -/
def pluralityVoteAsc {N : Nat} {α : Type} [DecidableEq α]
    (voters : List (Fin N)) (ans : Fin N → Answer α) : Answer α :=
  match voters with
  | [] => Answer.noanswer
  | v :: vs =>
    pickPluralityWinnerAux (v :: vs) ans (ans v) (voteCount (v :: vs) ans (ans v)) vs

/-- Active non-abstaining subset `A(s) = {i ∈ V : norm(y_i) ∉ {∅, noanswer}}` (§3.3). -/
def activeVoters {N : Nat} {α μ ε : Type}
    (profile : Fin N → AgentState α μ ε) : List (Fin N) :=
  (finRange N).filter (fun i => (profile i).answer.isSubstantive)

/-- Non-sink active Round-0 leaf voters `{i ∈ V \ {s} : i ∈ A(s^(0))}`. -/
def activeLeafVoters {N : Nat} {α μ ε : Type}
    (s : Fin N) (state0 : Fin N → AgentState α μ ε) : List (Fin N) :=
  (finRange N).filter (fun i => !(decide (i = s)) && (state0 i).answer.isSubstantive)

/-- Definition 3.2 (1): Original Plurality Vote (`R_orig`).
    Plurality vote over all normalized answers `{y_i^(1)}_{i ∈ V}`, treating `noanswer`
    as an ordinary ballot. -/
def R_orig {N : Nat} {α μ ε : Type} [DecidableEq α]
    (state1 : Fin N → AgentState α μ ε) : Answer α :=
  pluralityVoteAsc (finRange N) (fun i => (state1 i).answer)

/-- Definition 3.2 (2): Abstention-Aware Plurality Vote (`R_aa`).
    Plurality vote restricted to `{y_i^(1)}_{i ∈ A(s^(1))}`, returning `noanswer`
    only if `A(s^(1)) = ∅`. -/
def R_aa {N : Nat} {α μ ε : Type} [DecidableEq α]
    (state1 : Fin N → AgentState α μ ε) : Answer α :=
  pluralityVoteAsc (activeVoters state1) (fun i => (state1 i).answer)

/-- Definition 3.2 (3): Fixed-Sink Readout (`R_sink`).
    Returns `y_s^(1)` if `s ∈ A(s^(1))`, and `noanswer` otherwise. -/
def R_sink {N : Nat} {α μ ε : Type}
    (s : Fin N) (state1 : Fin N → AgentState α μ ε) : Answer α :=
  if (state1 s).answer.isSubstantive then
    (state1 s).answer
  else
    Answer.noanswer

/-- Abstention-aware plurality vote over non-sink Round-0 leaf predictions `{s_i^(0)}_{i ≠ s}`. -/
def R_aa_leaves {N : Nat} {α μ ε : Type} [DecidableEq α]
    (s : Fin N) (state0 : Fin N → AgentState α μ ε) : Answer α :=
  pluralityVoteAsc (activeLeafVoters s state0) (fun i => (state0 i).answer)

/-- Definition 3.2 (4) & Equation (4) (`eq:sp_fallback`): Sink-Priority Fallback (`R_sp`).
    Returns the sink's updated answer when substantive, and falls back to abstention-aware
    voting over Round-0 leaf predictions only when the sink abstains. -/
def R_sp {N : Nat} {α μ ε : Type} [DecidableEq α]
    (s : Fin N)
    (state0 : Fin N → AgentState α μ ε)
    (state1 : Fin N → AgentState α μ ε) : Answer α :=
  if (state1 s).answer.isSubstantive then
    (state1 s).answer
  else
    R_aa_leaves s state0

/-- Because normalized answers are either `.substantive a` or `.noanswer`,
    `R_sink s state1` is definitionally equal to `(state1 s).answer`. -/
theorem R_sink_eq_sink_answer {N : Nat} {α μ ε : Type}
    (s : Fin N) (state1 : Fin N → AgentState α μ ε) :
    R_sink s state1 = (state1 s).answer := by
  unfold R_sink
  cases h : (state1 s).answer <;> rfl

/-- When the sink produces a substantive answer, `R_sp` coincides with `R_sink`. -/
theorem R_sp_eq_R_sink_of_substantive {N : Nat} {α μ ε : Type} [DecidableEq α]
    (s : Fin N)
    (state0 state1 : Fin N → AgentState α μ ε)
    (hSub : (state1 s).answer.isSubstantive = true) :
    R_sp s state0 state1 = R_sink s state1 := by
  unfold R_sp R_sink
  simp [hSub]

/-- When the sink abstains (`isSubstantive = false`), `R_sp` evaluates `R_aa_leaves s state0`. -/
theorem R_sp_eq_leaf_aa_of_abstain {N : Nat} {α μ ε : Type} [DecidableEq α]
    (s : Fin N)
    (state0 state1 : Fin N → AgentState α μ ε)
    (hAbs : (state1 s).answer.isSubstantive = false) :
    R_sp s state0 state1 = R_aa_leaves s state0 := by
  unfold R_sp
  rw [hAbs]
  rfl

/-- If `activeVoters state1` is empty, `R_aa state1` returns `Answer.noanswer`. -/
theorem R_aa_eq_noanswer_of_active_empty {N : Nat} {α μ ε : Type} [DecidableEq α]
    (state1 : Fin N → AgentState α μ ε)
    (hEmpty : activeVoters state1 = []) :
    R_aa state1 = Answer.noanswer := by
  unfold R_aa
  rw [hEmpty]
  rfl

/-- Lemma: if `bestAns = c` and `bestCnt = voteCount allVoters ans c`, and `c` has at least as
    many votes as every candidate in `vs`, then `pickPluralityWinnerAux` returns `c`. -/
theorem pickPluralityWinnerAux_preserves_winner {N : Nat} {α : Type} [DecidableEq α]
    (allVoters : List (Fin N)) (ans : Fin N → Answer α) (c : Answer α)
    (vs : List (Fin N))
    (hDom : ∀ v ∈ vs, voteCount allVoters ans (ans v) ≤ voteCount allVoters ans c) :
    pickPluralityWinnerAux allVoters ans c (voteCount allVoters ans c) vs = c := by
  induction vs with
  | nil => rfl
  | cons v rest ih =>
    unfold pickPluralityWinnerAux
    have hv : voteCount allVoters ans (ans v) ≤ voteCount allVoters ans c :=
      hDom v (List.mem_cons_self v rest)
    have hNotLt : ¬ (voteCount allVoters ans c < voteCount allVoters ans (ans v)) :=
      Nat.not_lt.mpr hv
    simp [hNotLt]
    exact ih (fun u hu => hDom u (List.mem_cons_of_mem v hu))

/-- Lemma: if every voter in `vs` votes for `c`, and `bestAns = c`, then
    `pickPluralityWinnerAux` returns `c` regardless of `bestCnt`. -/
theorem pickPluralityWinnerAux_of_all_eq {N : Nat} {α : Type} [DecidableEq α]
    (allVoters : List (Fin N)) (ans : Fin N → Answer α) (c : Answer α)
    (vs : List (Fin N)) (bestCnt : Nat)
    (hAll : ∀ v ∈ vs, ans v = c) :
    pickPluralityWinnerAux allVoters ans c bestCnt vs = c := by
  induction vs generalizing bestCnt with
  | nil => rfl
  | cons v rest ih =>
    unfold pickPluralityWinnerAux
    have hv : ans v = c := hAll v (List.mem_cons_self v rest)
    rw [hv]
    by_cases hlt : bestCnt < voteCount allVoters ans c
    · simp [hlt]
      exact ih (voteCount allVoters ans c) (fun u hu => hAll u (List.mem_cons_of_mem v hu))
    · simp [hlt]
      exact ih bestCnt (fun u hu => hAll u (List.mem_cons_of_mem v hu))

/-- Unanimity theorem: if `voters` is non-empty and every voter in `voters` outputs `c`,
    then `pluralityVoteAsc voters ans = c`. -/
theorem pluralityVoteAsc_of_all_eq {N : Nat} {α : Type} [DecidableEq α]
    (voters : List (Fin N)) (ans : Fin N → Answer α) (c : Answer α)
    (hNonEmpty : voters ≠ [])
    (hAll : ∀ v ∈ voters, ans v = c) :
    pluralityVoteAsc voters ans = c := by
  cases voters with
  | nil => contradiction
  | cons v vs =>
    dsimp [pluralityVoteAsc]
    have hv : ans v = c := hAll v (List.mem_cons_self v vs)
    rw [hv]
    exact pickPluralityWinnerAux_of_all_eq (v :: vs) ans c vs
      (voteCount (v :: vs) ans c) (fun u hu => hAll u (List.mem_cons_of_mem v hu))

end WhoGetsLastWord
