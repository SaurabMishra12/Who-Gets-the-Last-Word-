/-
  WhoGetsLastWord/AbstentionVeto.lean
  Formalization of Proposition 3.5 (`prop:veto` — Plurality Abstention Veto & Specialist Recovery):
  1. Deterministic Strict-Majority Abstention Veto:
     When `k > N / 2` (`2 * k > N`) agents output `noanswer`, `noanswer` receives at least `k`
     ballots while every substantive answer `a ≠ noanswer` receives at most `N - k < k` ballots,
     so `R_orig` necessarily returns `noanswer` and has exact-match accuracy `0` on any answerable query.
  2. Deterministic Specialist Recovery under `R_aa` (`k = N - 1`):
     When `N - 1` uninformed agents abstain and the single specialist outputs the substantive gold
     answer `y_star`, `R_aa` filters out all abstentions and deterministically selects `y_star`.
  3. Exact Finite Product Probability & Independent Bernoulli Expectation Bounds:
     Over the `k`-fold independent Bernoulli product space with abstention weight `q` (`1 - ε`)
     and non-abstention weight `e` (`ε`) where `q + e = d`:
     - `Pr(all k uninformed abstain) = q^k / d^k = (1 - ε)^k`
     - `E[Y(R_orig)] ≤ 1 - (1 - ε)^k`
     - `E[Y(R_aa)] ≥ θ_spec * (1 - ε)^(N - 1)`
     - Zero-noise limit (`ε = 0`): `E[Y(R_orig)] = 0` and `E[Y(R_aa)] ≥ θ_spec`.
-/

import WhoGetsLastWord.TerminalReadout

namespace WhoGetsLastWord

/-! ## 1. Disjoint Filter Partition and Strict-Majority Plurality Dominance -/

/-- For any list `xs : List β` and two pointwise disjoint boolean predicates `p` and `q`,
    the sum of the lengths of `xs.filter p` and `xs.filter q` is at most `xs.length`. -/
theorem length_filter_add_length_filter_le {β : Type}
    (xs : List β) (p q : β → Bool)
    (hDisj : ∀ x : β, p x = true → q x = true → False) :
    (xs.filter p).length + (xs.filter q).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    by_cases hp : p x = true
    · by_cases hq : q x = true
      · exact False.elim (hDisj x hp hq)
      · simp [List.filter, hp, hq]
        omega
    · by_cases hq : q x = true
      · simp [List.filter, hp, hq]
        omega
      · simp [List.filter, hp, hq]
        omega

/-- For any distinct candidate answers `c1 ≠ c2`, the sum of their vote counts among `voters`
    cannot exceed `voters.length`. -/
theorem voteCount_add_voteCount_le_length {N : Nat} {α : Type} [DecidableEq α]
    (voters : List (Fin N)) (ans : Fin N → Answer α) (c1 c2 : Answer α)
    (hNe : c1 ≠ c2) :
    voteCount voters ans c1 + voteCount voters ans c2 ≤ voters.length := by
  unfold voteCount
  apply length_filter_add_length_filter_le
  intro i h1 h2
  have heq1 : ans i = c1 := of_decide_eq_true h1
  have heq2 : ans i = c2 := of_decide_eq_true h2
  exact hNe (heq1.symm.trans heq2)

/-- Strict-majority dominance lemma:
    If candidate `c` receives `voteCount voters ans c ≥ k` votes where `2 * k > voters.length`,
    then every distinct candidate `c' ≠ c` receives strictly fewer votes than `c`:
    `voteCount voters ans c' < voteCount voters ans c`. -/
theorem voteCount_lt_of_strict_majority {N : Nat} {α : Type} [DecidableEq α]
    (voters : List (Fin N)) (ans : Fin N → Answer α) (c c' : Answer α) (k : Nat)
    (hNe : c' ≠ c)
    (hMaj : 2 * k > voters.length)
    (hCount : voteCount voters ans c ≥ k) :
    voteCount voters ans c' < voteCount voters ans c := by
  have hSum : voteCount voters ans c' + voteCount voters ans c ≤ voters.length :=
    voteCount_add_voteCount_le_length voters ans c' c hNe
  omega

/-- Auxiliary invariant for `pickPluralityWinnerAux`:
    If `c` strictly beats every other candidate `x ≠ c`, and either `bestAns = c` (with
    `bestCnt = voteCount allVoters ans c`) or (`bestCnt = voteCount allVoters ans bestAns` and
    some voter `w ∈ vs` has `ans w = c`), then `pickPluralityWinnerAux` returns `c`. -/
theorem pickPluralityWinnerAux_eq_of_strict_winner {N : Nat} {α : Type} [DecidableEq α]
    (allVoters : List (Fin N)) (ans : Fin N → Answer α) (c : Answer α)
    (hStrict : ∀ x : Answer α, x ≠ c → voteCount allVoters ans x < voteCount allVoters ans c) :
    ∀ (vs : List (Fin N)) (bestAns : Answer α) (bestCnt : Nat),
      bestCnt = voteCount allVoters ans bestAns →
      (bestAns = c ∨ ∃ w ∈ vs, ans w = c) →
      pickPluralityWinnerAux allVoters ans bestAns bestCnt vs = c
  | [], bestAns, bestCnt, _, hState => by
    cases hState with
    | inl hEq => exact hEq
    | inr hEx =>
      rcases hEx with ⟨w, hw, _⟩
      cases hw
  | v :: rest, bestAns, bestCnt, hCntEq, hState => by
    unfold pickPluralityWinnerAux
    by_cases hBest : bestAns = c
    · rw [hBest] at hCntEq
      rw [hCntEq]
      have hLe : voteCount allVoters ans (ans v) ≤ voteCount allVoters ans c := by
        by_cases hv : ans v = c
        · rw [hv]; exact Nat.le_refl _
        · exact Nat.le_of_lt (hStrict (ans v) hv)
      have hNotLt : ¬ (voteCount allVoters ans c < voteCount allVoters ans (ans v)) :=
        Nat.not_lt.mpr hLe
      simp [hNotLt]
      rw [hBest]
      exact pickPluralityWinnerAux_eq_of_strict_winner allVoters ans c hStrict
        rest c (voteCount allVoters ans c) rfl (Or.inl rfl)
    · rcases hState with hEq | ⟨w, hw, hwAns⟩
      · exact False.elim (hBest hEq)
      · by_cases hv : ans v = c
        · have hStrictLt : bestCnt < voteCount allVoters ans (ans v) := by
            rw [hCntEq, hv]
            exact hStrict bestAns hBest
          simp [hStrictLt]
          exact pickPluralityWinnerAux_eq_of_strict_winner allVoters ans c hStrict
            rest (ans v) (voteCount allVoters ans (ans v)) rfl (Or.inl hv)
        · have hwRest : ∃ w ∈ rest, ans w = c := by
            cases List.mem_cons.mp hw with
            | inl hvw =>
              subst hvw
              exact False.elim (hv hwAns)
            | inr hInRest =>
              exact ⟨w, hInRest, hwAns⟩
          by_cases hlt : bestCnt < voteCount allVoters ans (ans v)
          · simp [hlt]
            exact pickPluralityWinnerAux_eq_of_strict_winner allVoters ans c hStrict
              rest (ans v) (voteCount allVoters ans (ans v)) rfl (Or.inr hwRest)
          · simp [hlt]
            exact pickPluralityWinnerAux_eq_of_strict_winner allVoters ans c hStrict
              rest bestAns bestCnt hCntEq (Or.inr hwRest)

/-- If `voteCount voters ans c > 0`, then there exists a voter `w ∈ voters` with `ans w = c`. -/
theorem exists_voter_of_voteCount_pos {N : Nat} {α : Type} [DecidableEq α]
    (voters : List (Fin N)) (ans : Fin N → Answer α) (c : Answer α)
    (hPos : voteCount voters ans c > 0) :
    ∃ w ∈ voters, ans w = c := by
  unfold voteCount at hPos
  induction voters with
  | nil =>
    simp at hPos
  | cons v rest ih =>
    by_cases hv : ans v = c
    · exact ⟨v, List.mem_cons_self v rest, hv⟩
    · simp [List.filter, hv] at hPos
      rcases ih hPos with ⟨w, hw, hwAns⟩
      exact ⟨w, List.mem_cons_of_mem v hw, hwAns⟩

/-- General Strict-Majority Winner Theorem (`pluralityVoteAsc_eq_of_strict_majority`):
    Whenever candidate `c` receives at least `k` votes among `voters` and `2 * k > voters.length`,
    `pluralityVoteAsc voters ans = c` regardless of how the remaining `voters.length - k`
    agents vote or how ties would otherwise be broken. -/
theorem pluralityVoteAsc_eq_of_strict_majority {N : Nat} {α : Type} [DecidableEq α]
    (voters : List (Fin N)) (ans : Fin N → Answer α) (c : Answer α) (k : Nat)
    (hMaj : 2 * k > voters.length)
    (hCount : voteCount voters ans c ≥ k) :
    pluralityVoteAsc voters ans = c := by
  have hkPos : voteCount voters ans c > 0 := by omega
  rcases exists_voter_of_voteCount_pos voters ans c hkPos with ⟨w, hw, hwAns⟩
  cases voters with
  | nil =>
    cases hw
  | cons v vs =>
    unfold pluralityVoteAsc
    apply pickPluralityWinnerAux_eq_of_strict_winner (v :: vs) ans c
    · intro x hx
      exact voteCount_lt_of_strict_majority (v :: vs) ans c x k hx hMaj hCount
    · rfl
    · cases List.mem_cons.mp hw with
      | inl hvw =>
        subst hvw
        exact Or.inl hwAns
      | inr hInVs =>
        exact Or.inr ⟨w, hInVs, hwAns⟩

/-! ## 2. Deterministic Part of Proposition 3.5: Plurality Abstention Veto -/

/-- Theorem D1 (`R_orig_eq_noanswer_of_majority_abstain`, Proposition 3.5 Deterministic Part):
    In an `N`-agent system, if at least `k` agents output `noanswer` at Round 1 with `2 * k > N`
    (i.e. `k > N / 2`), then Original Plurality Vote `R_orig` deterministically returns `noanswer`
    regardless of the remaining `N - k` agents' predictions. -/
theorem R_orig_eq_noanswer_of_majority_abstain {N : Nat} {α μ ε : Type} [DecidableEq α]
    (state1 : Fin N → AgentState α μ ε) (k : Nat)
    (hMaj : 2 * k > N)
    (hAbstain : voteCount (finRange N) (fun i => (state1 i).answer) .noanswer ≥ k) :
    R_orig state1 = Answer.noanswer := by
  unfold R_orig
  apply pluralityVoteAsc_eq_of_strict_majority (finRange N) (fun i => (state1 i).answer) .noanswer k
  · rw [length_finRange N]
    exact hMaj
  · exact hAbstain

/-- Corollary D2 (`R_orig_accuracy_zero_of_majority_abstain`):
    On any answerable query (`gold = Answer.substantive y_star`), whenever `k > N / 2` agents
    output `noanswer`, the exact-match accuracy `Y(R_orig)` is `0`. -/
theorem R_orig_accuracy_zero_of_majority_abstain {N : Nat} {α μ ε : Type} [DecidableEq α]
    (state1 : Fin N → AgentState α μ ε) (y_star : α) (k : Nat)
    (hMaj : 2 * k > N)
    (hAbstain : voteCount (finRange N) (fun i => (state1 i).answer) .noanswer ≥ k) :
    exactMatch (.substantive y_star) (R_orig state1) = 0 := by
  rw [R_orig_eq_noanswer_of_majority_abstain state1 k hMaj hAbstain]
  exact exactMatch_noanswer_of_substantive_gold y_star

/-! ## 3. Deterministic Specialist Recovery under `R_aa` (`k = N - 1`) -/

/-- Theorem D3 (`R_aa_eq_specialist_of_peers_abstain`):
    If a single informed specialist `spec : Fin N` outputs substantive answer `.substantive y_star`
    and all `N - 1` remaining peers `i ≠ spec` output `.noanswer`, then `R_aa` filters all
    abstentions and deterministically selects `.substantive y_star` (achieving accuracy `1`). -/
theorem R_aa_eq_specialist_of_peers_abstain {N : Nat} {α μ ε : Type} [DecidableEq α]
    (state1 : Fin N → AgentState α μ ε)
    (spec : Fin N) (y_star : α)
    (hSpec : (state1 spec).answer = .substantive y_star)
    (hPeers : ∀ i : Fin N, i ≠ spec → (state1 i).answer = .noanswer) :
    R_aa state1 = .substantive y_star ∧
    exactMatch (.substantive y_star) (R_aa state1) = 1 := by
  have hMemSpec : spec ∈ activeVoters state1 := by
    unfold activeVoters
    rw [List.mem_filter]
    refine ⟨mem_finRange spec, ?_⟩
    rw [hSpec]
    rfl
  have hNonEmpty : activeVoters state1 ≠ [] := by
    intro hNil
    rw [hNil] at hMemSpec
    cases hMemSpec
  have hAllEq : ∀ v ∈ activeVoters state1, (state1 v).answer = .substantive y_star := by
    intro v hv
    unfold activeVoters at hv
    rw [List.mem_filter] at hv
    by_cases hvs : v = spec
    · subst hvs
      exact hSpec
    · have hAbs : (state1 v).answer = .noanswer := hPeers v hvs
      rw [hAbs] at hv
      cases hv.2
  have hWin : R_aa state1 = .substantive y_star := by
    unfold R_aa
    exact pluralityVoteAsc_of_all_eq (activeVoters state1) (fun i => (state1 i).answer)
      (.substantive y_star) hNonEmpty hAllEq
  refine ⟨hWin, ?_⟩
  rw [hWin]
  unfold exactMatch
  simp

/-! ## 4. Probabilistic Part of Proposition 3.5: Independent Bernoulli Product Measure -/

/-- Prepends a boolean outcome `b` to a length-`k` boolean vector `ω : Fin k → Bool`. -/
def finCons {k : Nat} (b : Bool) (ω : Fin k → Bool) : Fin (k + 1) → Bool :=
  fun i =>
    match i with
    | ⟨0, _⟩ => b
    | ⟨n + 1, isLt⟩ => ω ⟨n, Nat.lt_of_succ_lt_succ isLt⟩

/-- Indicator for the event that all `k` uninformed agents abstain (`ω_i = false` for all `i`). -/
def allAbstainEvent : (k : Nat) → (Fin k → Bool) → Nat
  | 0, _ => 1
  | k + 1, ω =>
    if ω ⟨0, Nat.zero_lt_succ k⟩ then
      0
    else
      allAbstainEvent k (fun i => ω ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

theorem allAbstainEvent_le_one (k : Nat) (ω : Fin k → Bool) :
    allAbstainEvent k ω ≤ 1 := by
  revert ω
  induction k with
  | zero =>
    intro ω
    unfold allAbstainEvent
    exact Nat.le_refl 1
  | succ n ih =>
    intro ω
    unfold allAbstainEvent
    by_cases h0 : ω 0 = true
    · simp [h0]
    · simp [h0]
      exact ih _

theorem allAbstainEvent_finCons_false (k : Nat) (ω : Fin k → Bool) :
    allAbstainEvent (k + 1) (finCons false ω) = allAbstainEvent k ω := rfl

theorem allAbstainEvent_finCons_true (k : Nat) (ω : Fin k → Bool) :
    allAbstainEvent (k + 1) (finCons true ω) = 0 := rfl

/-- Exact scaled expectation over the `k`-fold independent Bernoulli product space `{false, true}^k`,
    where each uninformed agent independently abstains (`false`) with weight `q` (representing `1 - ε`)
    and outputs a non-abstaining answer (`true`) with weight `e` (representing `ε`), scaled by `(q + e)^k`. -/
def bernoulliExpectScaled : (k : Nat) → (q e : Nat) → ((Fin k → Bool) → Nat) → Nat
  | 0, _, _, f => f (fun i => Fin.elim0 i)
  | k + 1, q, e, f =>
    q * bernoulliExpectScaled k q e (fun ω => f (finCons false ω)) +
    e * bernoulliExpectScaled k q e (fun ω => f (finCons true ω))

/-- Linearity of `bernoulliExpectScaled` over addition. -/
theorem bernoulliExpectScaled_add (k q e : Nat) (f g : (Fin k → Bool) → Nat) :
    bernoulliExpectScaled k q e (fun ω => f ω + g ω) =
      bernoulliExpectScaled k q e f + bernoulliExpectScaled k q e g := by
  induction k with
  | zero => rfl
  | succ n ih =>
    unfold bernoulliExpectScaled
    rw [ih (fun ω => f (finCons false ω)) (fun ω => g (finCons false ω))]
    rw [ih (fun ω => f (finCons true ω)) (fun ω => g (finCons true ω))]
    rw [Nat.left_distrib, Nat.left_distrib]
    omega

/-- Monotonicity of `bernoulliExpectScaled` for pointwise ordered non-negative functions. -/
theorem bernoulliExpectScaled_mono (k q e : Nat) (f g : (Fin k → Bool) → Nat)
    (hLe : ∀ ω : Fin k → Bool, f ω ≤ g ω) :
    bernoulliExpectScaled k q e f ≤ bernoulliExpectScaled k q e g := by
  induction k with
  | zero => exact hLe _
  | succ n ih =>
    unfold bernoulliExpectScaled
    have hFalse :
        bernoulliExpectScaled n q e (fun ω => f (finCons false ω)) ≤
          bernoulliExpectScaled n q e (fun ω => g (finCons false ω)) :=
      ih _ _ (fun ω => hLe (finCons false ω))
    have hTrue :
        bernoulliExpectScaled n q e (fun ω => f (finCons true ω)) ≤
          bernoulliExpectScaled n q e (fun ω => g (finCons true ω)) :=
      ih _ _ (fun ω => hLe (finCons true ω))
    have hm1 : q * bernoulliExpectScaled n q e (fun ω => f (finCons false ω)) ≤
        q * bernoulliExpectScaled n q e (fun ω => g (finCons false ω)) :=
      Nat.mul_le_mul_left q hFalse
    have hm2 : e * bernoulliExpectScaled n q e (fun ω => f (finCons true ω)) ≤
        e * bernoulliExpectScaled n q e (fun ω => g (finCons true ω)) :=
      Nat.mul_le_mul_left e hTrue
    exact Nat.add_le_add hm1 hm2

/-- Constant multiplication rule for `bernoulliExpectScaled`. -/
theorem bernoulliExpectScaled_const_mul (k q e c : Nat) (f : (Fin k → Bool) → Nat) :
    bernoulliExpectScaled k q e (fun ω => c * f ω) =
      c * bernoulliExpectScaled k q e f := by
  induction k with
  | zero => rfl
  | succ n ih =>
    unfold bernoulliExpectScaled
    rw [ih (fun ω => f (finCons false ω)), ih (fun ω => f (finCons true ω))]
    rw [Nat.left_distrib, ← Nat.mul_assoc, ← Nat.mul_assoc]
    rw [Nat.mul_comm q c, Nat.mul_comm e c]
    rw [Nat.mul_assoc, Nat.mul_assoc]

/-- Zero expectation rule for `bernoulliExpectScaled`. -/
theorem bernoulliExpectScaled_zero (k q e : Nat) :
    bernoulliExpectScaled k q e (fun _ => 0) = 0 := by
  induction k with
  | zero => rfl
  | succ n ih =>
    unfold bernoulliExpectScaled
    change q * bernoulliExpectScaled n q e (fun _ => 0) + e * bernoulliExpectScaled n q e (fun _ => 0) = 0
    rw [ih]
    simp

/-- Total mass of the `k`-fold product measure equals `(q + e)^k`. -/
theorem bernoulliExpectScaled_one (k q e : Nat) :
    bernoulliExpectScaled k q e (fun _ => 1) = (q + e) ^ k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    unfold bernoulliExpectScaled
    change q * bernoulliExpectScaled n q e (fun _ => 1) + e * bernoulliExpectScaled n q e (fun _ => 1) = (q + e) ^ (n + 1)
    rw [ih, Nat.pow_succ]
    rw [← Nat.add_mul]
    rw [Nat.mul_comm]

/-- Theorem D4 (`prob_all_uninformed_abstain_eq`):
    Under `k` independent Bernoulli trials with abstention weight `q = 1 - ε` and non-abstention
    weight `e = ε`, the exact probability mass of the event that all `k` uninformed agents abstain
    is `q^k` (i.e. `(1 - ε)^k` after dividing by `(q + e)^k = 1^k`). -/
theorem prob_all_uninformed_abstain_eq (k q e : Nat) :
    bernoulliExpectScaled k q e (allAbstainEvent k) = q ^ k := by
  induction k with
  | zero => simp [bernoulliExpectScaled, allAbstainEvent]
  | succ n ih =>
    unfold bernoulliExpectScaled
    have hF : (fun ω => allAbstainEvent (n + 1) (finCons false ω)) = allAbstainEvent n := by
      funext ω
      rfl
    have hT : (fun ω => allAbstainEvent (n + 1) (finCons true ω)) = (fun _ => 0) := by
      funext ω
      rfl
    rw [hF, hT, ih, bernoulliExpectScaled_zero]
    rw [Nat.pow_succ, Nat.mul_comm (q ^ n) q]
    omega

/-- Theorem D5 (`expected_acc_R_orig_upper_bound`, Proposition 3.5 Probabilistic Bound):
    For any `{0, 1}`-valued accuracy random variable `Y_orig : (Fin k → Bool) → Nat` satisfying:
    1. `Y_orig ω ≤ 1` for all `ω`, and
    2. `Y_orig ω = 0` whenever `allAbstainEvent k ω = 1` (established by Theorem D2 for `R_orig`
       whenever `2 * k > N`),
    the scaled expected accuracy satisfies:
    `bernoulliExpectScaled k q e Y_orig ≤ (q + e)^k - q^k`
    (which upon dividing by `d^k = (q + e)^k` is `E[Y(R_orig)] ≤ 1 - (1 - ε)^k`). -/
theorem expected_acc_R_orig_upper_bound (k q e : Nat)
    (Y_orig : (Fin k → Bool) → Nat)
    (hBound : ∀ ω : Fin k → Bool, Y_orig ω ≤ 1)
    (hVeto : ∀ ω : Fin k → Bool, allAbstainEvent k ω = 1 → Y_orig ω = 0) :
    bernoulliExpectScaled k q e Y_orig + q ^ k ≤ (q + e) ^ k ∧
    bernoulliExpectScaled k q e Y_orig ≤ (q + e) ^ k - q ^ k := by
  have hPointwise : ∀ ω : Fin k → Bool, Y_orig ω + allAbstainEvent k ω ≤ 1 := by
    intro ω
    have hA : allAbstainEvent k ω ≤ 1 := allAbstainEvent_le_one k ω
    have hY : Y_orig ω ≤ 1 := hBound ω
    by_cases hEq1 : allAbstainEvent k ω = 1
    · have hY0 : Y_orig ω = 0 := hVeto ω hEq1
      omega
    · omega
  have hMono :
      bernoulliExpectScaled k q e (fun ω => Y_orig ω + allAbstainEvent k ω) ≤
        bernoulliExpectScaled k q e (fun _ => 1) :=
    bernoulliExpectScaled_mono k q e _ _ hPointwise
  rw [bernoulliExpectScaled_add, prob_all_uninformed_abstain_eq, bernoulliExpectScaled_one] at hMono
  refine ⟨hMono, ?_⟩
  omega

/-- Joint expectation over an independent specialist (`θ_num` success weight, `θ_comp` failure weight)
    and `k = N - 1` independent uninformed agents (`q` abstention weight, `e` speaking weight). -/
def specialistJointExpectScaled (k θ_num θ_comp q e : Nat)
    (Y_aa : Bool → (Fin k → Bool) → Nat) : Nat :=
  θ_num * bernoulliExpectScaled k q e (fun ω => Y_aa true ω) +
  θ_comp * bernoulliExpectScaled k q e (fun ω => Y_aa false ω)

/-- Theorem D6 (`expected_acc_R_aa_specialist_lower_bound`, Proposition 3.5 Specialist Bound):
    In the specialist configuration (`k = N - 1` uninformed agents and `1` independent specialist
    who answers correctly with probability weight `θ_num`), for any `{0, 1}`-valued accuracy
    variable `Y_aa` that equals `1` when the specialist is correct (`true`) and all `N - 1`
    uninformed agents abstain (`allAbstainEvent (N - 1) ω = 1`, established by Theorem D3),
    the scaled expected accuracy satisfies:
    `θ_num * q^(N - 1) ≤ specialistJointExpectScaled (N - 1) θ_num θ_comp q e Y_aa`
    (which upon dividing by `(θ_num + θ_comp) * (q + e)^(N - 1)` is `E[Y(R_aa)] ≥ θ_spec * (1 - ε)^(N - 1)`). -/
theorem expected_acc_R_aa_specialist_lower_bound (N θ_num θ_comp q e : Nat)
    (Y_aa : Bool → (Fin (N - 1) → Bool) → Nat)
    (hRecovery : ∀ ω : Fin (N - 1) → Bool, allAbstainEvent (N - 1) ω = 1 → Y_aa true ω = 1) :
    θ_num * (q ^ (N - 1)) ≤
      specialistJointExpectScaled (N - 1) θ_num θ_comp q e Y_aa := by
  unfold specialistJointExpectScaled
  have hPointwise : ∀ ω : Fin (N - 1) → Bool, allAbstainEvent (N - 1) ω ≤ Y_aa true ω := by
    intro ω
    have hA : allAbstainEvent (N - 1) ω ≤ 1 := allAbstainEvent_le_one (N - 1) ω
    by_cases hEq1 : allAbstainEvent (N - 1) ω = 1
    · have hY1 : Y_aa true ω = 1 := hRecovery ω hEq1
      omega
    · omega
  have hMono :
      bernoulliExpectScaled (N - 1) q e (allAbstainEvent (N - 1)) ≤
        bernoulliExpectScaled (N - 1) q e (fun ω => Y_aa true ω) :=
    bernoulliExpectScaled_mono (N - 1) q e _ _ hPointwise
  rw [prob_all_uninformed_abstain_eq] at hMono
  have hMul :
      θ_num * (q ^ (N - 1)) ≤ θ_num * bernoulliExpectScaled (N - 1) q e (fun ω => Y_aa true ω) :=
    Nat.mul_le_mul_left θ_num hMono
  omega

/-- Theorem D7 (`veto_limit_eps_zero`, Proposition 3.5 Asymptotic Limit `ε → 0`):
    At `e = 0` (`ε = 0`, where uninformed agents always output `noanswer`):
    1. `bernoulliExpectScaled k q 0 Y_orig = 0` (expected accuracy of `R_orig` vanishes identically).
    2. `specialistJointExpectScaled (N - 1) θ_num θ_comp q 0 Y_aa ≥ θ_num * q^(N - 1)`
       (expected accuracy of `R_aa` is at least `θ_spec`). -/
theorem veto_limit_eps_zero (N k θ_num θ_comp q : Nat)
    (Y_orig : (Fin k → Bool) → Nat)
    (Y_aa : Bool → (Fin (N - 1) → Bool) → Nat)
    (hBound : ∀ ω : Fin k → Bool, Y_orig ω ≤ 1)
    (hVeto : ∀ ω : Fin k → Bool, allAbstainEvent k ω = 1 → Y_orig ω = 0)
    (hRecovery : ∀ ω : Fin (N - 1) → Bool, allAbstainEvent (N - 1) ω = 1 → Y_aa true ω = 1) :
    bernoulliExpectScaled k q 0 Y_orig = 0 ∧
    θ_num * (q ^ (N - 1)) ≤ specialistJointExpectScaled (N - 1) θ_num θ_comp q 0 Y_aa := by
  have hOrig := (expected_acc_R_orig_upper_bound k q 0 Y_orig hBound hVeto).2
  simp at hOrig
  have hAa := expected_acc_R_aa_specialist_lower_bound N θ_num θ_comp q 0 Y_aa hRecovery
  exact ⟨hOrig, hAa⟩

end WhoGetsLastWord
