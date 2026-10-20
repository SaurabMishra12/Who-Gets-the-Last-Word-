/-
  WhoGetsLastWord/VolumeAccounting.lean
  Formalization of Proposition 3.1 (`prop:volume` — Support–Volume Coupling)
  and Equations (2)–(3) (`eq:mediation`, `eq:residual` — Counterfactual Accounting Identities):
  - Support projection `P_A(B) = A ⊙ B`
  - Linearity (`P_A(X + Y) = P_A(X) + P_A(Y)` and `P_A(c • X) = c • P_A(X)`)
  - Idempotence (`P_A(P_A(B)) = P_A(B)`)
  - Self-adjointness under the off-diagonal Frobenius inner product `<X, Y>_off`
  - Orthogonal-projection complement identity `<P_A(X), Y - P_A(Y)>_off = 0`
  - Non-negativity `0 ≤ Vol(A, B)` and upper bound `Vol(A, B) ≤ ||B||_{1,off}`
  - Exact equality conditions (`Vol(A, B) = 0` and `Vol(A, B) = ||B||_{1,off}`)
  - Exact signed support-change identity `Vol(A', B) - Vol(A, B) = ∑_{T'\T} B_{ij} - ∑_{T\T'} B_{ij}`
  - Pointwise and expected counterfactual accounting decompositions (Eqs. 2 and 3).
-/

import WhoGetsLastWord.CommunicationGraph

namespace WhoGetsLastWord

/-! ## 1. Finite Matrix Space and Support Projection Operator `P_A` -/

/-- `N × N` matrix over `Int` (representing token lengths, differences, or scaled weights). -/
abbrev MatrixN (N : Nat) := Fin N → Fin N → Int

/-- Pointwise matrix addition. -/
def matAdd {N : Nat} (X Y : MatrixN N) : MatrixN N :=
  fun i j => X i j + Y i j

/-- Pointwise matrix subtraction. -/
def matSub {N : Nat} (X Y : MatrixN N) : MatrixN N :=
  fun i j => X i j - Y i j

/-- Pointwise scalar multiplication. -/
def matSmul {N : Nat} (c : Int) (X : MatrixN N) : MatrixN N :=
  fun i j => c * X i j

/-- Binary adjacency indicator `A_{ij} ∈ {0, 1}` associated with a directed graph `A`. -/
def maskVal {N : Nat} (A : DirectedGraph N) (i j : Fin N) : Int :=
  if A.adj i j then 1 else 0

theorem maskVal_mul_self {N : Nat} (A : DirectedGraph N) (i j : Fin N) :
    maskVal A i j * maskVal A i j = maskVal A i j := by
  unfold maskVal
  cases A.adj i j <;> rfl

theorem maskVal_nonneg {N : Nat} (A : DirectedGraph N) (i j : Fin N) :
    0 ≤ maskVal A i j := by
  unfold maskVal
  cases A.adj i j <;> decide

theorem maskVal_le_one {N : Nat} (A : DirectedGraph N) (i j : Fin N) :
    maskVal A i j ≤ 1 := by
  unfold maskVal
  cases A.adj i j <;> decide

/-- Support projection operator `P_A(B) = A ⊙ B` (§3.2, Proposition 3.1). -/
def supportProj {N : Nat} (A : DirectedGraph N) (B : MatrixN N) : MatrixN N :=
  fun i j => maskVal A i j * B i j

/-- Linearity of `supportProj` with respect to matrix addition. -/
theorem supportProj_linear_add {N : Nat} (A : DirectedGraph N) (X Y : MatrixN N) :
    supportProj A (matAdd X Y) = matAdd (supportProj A X) (supportProj A Y) := by
  funext i j
  unfold supportProj matAdd
  exact Int.mul_add (maskVal A i j) (X i j) (Y i j)

/-- Linearity of `supportProj` with respect to scalar multiplication. -/
theorem supportProj_linear_smul {N : Nat} (A : DirectedGraph N) (c : Int) (X : MatrixN N) :
    supportProj A (matSmul c X) = matSmul c (supportProj A X) := by
  funext i j
  unfold supportProj matSmul
  rw [← Int.mul_assoc, Int.mul_comm (maskVal A i j) c, Int.mul_assoc]

/-- Idempotence of `supportProj`: `P_A(P_A(B)) = P_A(B)`. -/
theorem supportProj_idempotent {N : Nat} (A : DirectedGraph N) (B : MatrixN N) :
    supportProj A (supportProj A B) = supportProj A B := by
  funext i j
  unfold supportProj
  rw [← Int.mul_assoc, maskVal_mul_self A i j]

/-! ## 2. Off-Diagonal Frobenius Inner Product and Orthogonal Projection -/

/-- Sum of an integer-valued function `f` over a finite list `xs : List β`. -/
def listSumInt {β : Type} (xs : List β) (f : β → Int) : Int :=
  match xs with
  | [] => 0
  | x :: rest => f x + listSumInt rest f

theorem listSumInt_congr {β : Type} (xs : List β) (f g : β → Int)
    (hEq : ∀ x ∈ xs, f x = g x) :
    listSumInt xs f = listSumInt xs g := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    unfold listSumInt
    rw [hEq x (List.mem_cons_self x rest)]
    rw [ih (fun y hy => hEq y (List.mem_cons_of_mem x hy))]

theorem listSumInt_add {β : Type} (xs : List β) (f g : β → Int) :
    listSumInt xs (fun x => f x + g x) = listSumInt xs f + listSumInt xs g := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    unfold listSumInt
    rw [ih]
    omega

theorem listSumInt_sub {β : Type} (xs : List β) (f g : β → Int) :
    listSumInt xs (fun x => f x - g x) = listSumInt xs f - listSumInt xs g := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    unfold listSumInt
    rw [ih]
    omega

theorem listSumInt_zero {β : Type} (xs : List β) :
    listSumInt xs (fun _ => 0) = 0 := by
  induction xs with
  | nil => rfl
  | cons _ rest ih =>
    unfold listSumInt
    rw [ih]
    rfl

theorem listSumInt_nonneg {β : Type} (xs : List β) (f : β → Int)
    (hNonneg : ∀ x ∈ xs, 0 ≤ f x) :
    0 ≤ listSumInt xs f := by
  induction xs with
  | nil =>
    unfold listSumInt
    omega
  | cons x rest ih =>
    unfold listSumInt
    have hx : 0 ≤ f x := hNonneg x (List.mem_cons_self x rest)
    have hrest : 0 ≤ listSumInt rest f := ih (fun y hy => hNonneg y (List.mem_cons_of_mem x hy))
    omega

theorem listSumInt_mono {β : Type} (xs : List β) (f g : β → Int)
    (hLe : ∀ x ∈ xs, f x ≤ g x) :
    listSumInt xs f ≤ listSumInt xs g := by
  induction xs with
  | nil =>
    unfold listSumInt
    omega
  | cons x rest ih =>
    unfold listSumInt
    have hx : f x ≤ g x := hLe x (List.mem_cons_self x rest)
    have hrest : listSumInt rest f ≤ listSumInt rest g :=
      ih (fun y hy => hLe y (List.mem_cons_of_mem x hy))
    omega

/-- Off-diagonal Frobenius inner product `<X, Y>_off = ∑_{(i,j) ∈ O} X_{ij} Y_{ij}` (Appendix A). -/
def innerOff {N : Nat} (X Y : MatrixN N) : Int :=
  listSumInt (DirectedGraph.offDiagChannels N) (fun p => X p.1 p.2 * Y p.1 p.2)

/-- Self-adjointness of `supportProj` under `<·, ·>_off`:
    `<P_A(X), Y>_off = <X, P_A(Y)>_off`. -/
theorem supportProj_selfAdjoint {N : Nat} (A : DirectedGraph N) (X Y : MatrixN N) :
    innerOff (supportProj A X) Y = innerOff X (supportProj A Y) := by
  unfold innerOff supportProj
  apply listSumInt_congr
  intro p _
  unfold maskVal
  cases A.adj p.1 p.2 <;> simp

/-- Orthogonal-projection characterization:
    The image `P_A(X)` is orthogonal to the residual `Y - P_A(Y)` under `<·, ·>_off`. -/
theorem supportProj_orthogonal_complement {N : Nat} (A : DirectedGraph N) (X Y : MatrixN N) :
    innerOff (supportProj A X) (matSub Y (supportProj A Y)) = 0 := by
  unfold innerOff supportProj matSub
  have hZero :
      listSumInt (DirectedGraph.offDiagChannels N)
        (fun p => (maskVal A p.1 p.2 * X p.1 p.2) * (Y p.1 p.2 - maskVal A p.1 p.2 * Y p.1 p.2)) =
      listSumInt (DirectedGraph.offDiagChannels N) (fun _ => 0) := by
    apply listSumInt_congr
    intro p _
    unfold maskVal
    cases A.adj p.1 p.2 <;> simp [Int.sub_self]
  rw [hZero, listSumInt_zero]

/-! ## 3. Realized Volume Bounds, Equality Conditions, and Support-Change Identity -/

/-- Total realized communication volume `Vol(A, B) = ∑_{i ≠ j} A_{ij} B_{ij}` (§3.2). -/
def realizedVol {N : Nat} (A : DirectedGraph N) (B : MatrixN N) : Int :=
  listSumInt (DirectedGraph.offDiagChannels N) (fun p => maskVal A p.1 p.2 * B p.1 p.2)

/-- Off-diagonal L1 norm `||B||_{1,off} = ∑_{i ≠ j} B_{ij}` for non-negative `B`. -/
def l1OffNorm {N : Nat} (B : MatrixN N) : Int :=
  listSumInt (DirectedGraph.offDiagChannels N) (fun p => B p.1 p.2)

/-- Residual un-transmitted volume on complement off-diagonal channels `O \ T`. -/
def complementVol {N : Nat} (A : DirectedGraph N) (B : MatrixN N) : Int :=
  listSumInt (DirectedGraph.offDiagChannels N) (fun p => (1 - maskVal A p.1 p.2) * B p.1 p.2)

/-- Exact L1 partition identity: `||B||_{1,off} = Vol(A, B) + complementVol(A, B)`. -/
theorem l1OffNorm_eq_realizedVol_add_complementVol {N : Nat} (A : DirectedGraph N) (B : MatrixN N) :
    l1OffNorm B = realizedVol A B + complementVol A B := by
  unfold l1OffNorm realizedVol complementVol
  rw [← listSumInt_add]
  apply listSumInt_congr
  intro p _
  unfold maskVal
  cases A.adj p.1 p.2 <;> simp

/-- Proposition 3.1 (Bounds): For any non-negative potential length matrix `B` (`B_{ij} ≥ 0` on `O`),
    `0 ≤ Vol(A, B) ≤ ||B||_{1,off}`. -/
theorem realizedVol_bounds {N : Nat} (A : DirectedGraph N) (B : MatrixN N)
    (hNonneg : ∀ p ∈ DirectedGraph.offDiagChannels N, 0 ≤ B p.1 p.2) :
    0 ≤ realizedVol A B ∧ realizedVol A B ≤ l1OffNorm B := by
  refine ⟨?_, ?_⟩
  · unfold realizedVol
    apply listSumInt_nonneg
    intro p hp
    have hB : 0 ≤ B p.1 p.2 := hNonneg p hp
    unfold maskVal
    cases A.adj p.1 p.2 <;> simp [hB]
  · unfold realizedVol l1OffNorm
    apply listSumInt_mono
    intro p hp
    have hB : 0 ≤ B p.1 p.2 := hNonneg p hp
    unfold maskVal
    cases A.adj p.1 p.2 <;> simp [hB]

/-- Equality condition for lower bound: if `B_{ij} = 0` on all active edges `A.adj i j = true`,
    then `Vol(A, B) = 0`. -/
theorem realizedVol_eq_zero_of_zero_on_support {N : Nat} (A : DirectedGraph N) (B : MatrixN N)
    (hZero : ∀ p ∈ DirectedGraph.offDiagChannels N, A.adj p.1 p.2 = true → B p.1 p.2 = 0) :
    realizedVol A B = 0 := by
  unfold realizedVol
  have hCongr :
      listSumInt (DirectedGraph.offDiagChannels N) (fun p => maskVal A p.1 p.2 * B p.1 p.2) =
        listSumInt (DirectedGraph.offDiagChannels N) (fun _ => 0) := by
    apply listSumInt_congr
    intro p hp
    unfold maskVal
    by_cases hAdj : A.adj p.1 p.2 = true
    · rw [if_pos hAdj, hZero p hp hAdj]
      rfl
    · simp [hAdj]
  rw [hCongr, listSumInt_zero]

/-- Equality condition for upper bound: if `B_{ij} = 0` on all inactive off-diagonal edges
    `A.adj i j = false`, then `Vol(A, B) = ||B||_{1,off}`. -/
theorem realizedVol_eq_l1OffNorm_of_zero_off_support {N : Nat} (A : DirectedGraph N) (B : MatrixN N)
    (hZeroOff : ∀ p ∈ DirectedGraph.offDiagChannels N, A.adj p.1 p.2 = false → B p.1 p.2 = 0) :
    realizedVol A B = l1OffNorm B := by
  unfold realizedVol l1OffNorm
  apply listSumInt_congr
  intro p hp
  unfold maskVal
  cases hAdj : A.adj p.1 p.2 with
  | true => simp
  | false =>
    simp [hZeroOff p hp hAdj]

/-- Indicator for channels in the set difference `T' \ T` (`(i, j) ∈ T'` and `(i, j) ∉ T`). -/
def diffMask {N : Nat} (A' A : DirectedGraph N) (i j : Fin N) : Int :=
  if A'.adj i j && !(A.adj i j) then 1 else 0

/-- Volume sum over the support set difference `T' \ T`: `∑_{(i,j) ∈ T' \ T} B_{ij}`. -/
def supportDiffVol {N : Nat} (A' A : DirectedGraph N) (B : MatrixN N) : Int :=
  listSumInt (DirectedGraph.offDiagChannels N) (fun p => diffMask A' A p.1 p.2 * B p.1 p.2)

/-- Pointwise algebraic identity for support change at fixed `B_{ij}`:
    `A'_{ij} B_{ij} - A_{ij} B_{ij} = I[(i,j) ∈ T'\T] B_{ij} - I[(i,j) ∈ T\T'] B_{ij}`. -/
theorem maskVal_sub_maskVal_mul_eq_diffMask {N : Nat} (A A' : DirectedGraph N) (i j : Fin N) (b : Int) :
    maskVal A' i j * b - maskVal A i j * b =
      diffMask A' A i j * b - diffMask A A' i j * b := by
  unfold maskVal diffMask
  cases A.adj i j <;> cases A'.adj i j <;> simp

/-- Proposition 3.1 (`vol_support_change_identity`, Signed Support-Change Identity):
    For any fixed potential length matrix `B` and any two supports `T` (`A`) and `T'` (`A'`),
    `Vol(A', B) - Vol(A, B) = ∑_{(i,j) ∈ T' \ T} B_{ij} - ∑_{(i,j) ∈ T \ T'} B_{ij}`. -/
theorem vol_support_change_identity {N : Nat} (A A' : DirectedGraph N) (B : MatrixN N) :
    realizedVol A' B - realizedVol A B =
      supportDiffVol A' A B - supportDiffVol A A' B := by
  unfold realizedVol supportDiffVol
  rw [← listSumInt_sub, ← listSumInt_sub]
  apply listSumInt_congr
  intro p _
  exact maskVal_sub_maskVal_mul_eq_diffMask A A' p.1 p.2 (B p.1 p.2)

/-! ## 4. Proposition F: Counterfactual Accounting Identities (Equations 2 & 3) -/

/-- Pointwise Equation (2) (`eq:mediation`):
    For any potential outcome function `Y(c, t, v)` and realized volume `V(c, t)`,
    the total routing-policy contrast `Y(c, 1, V(c, 1)) - Y(c, 0, V(c, 0))` decomposes
    algebraically into the direct routing contrast at fixed baseline volume
    `Δ_route(c) = Y(c, 1, V(c, 0)) - Y(c, 0, V(c, 0))` plus the volume-shift contrast
    `Δ_vol(c) = Y(c, 1, V(c, 1)) - Y(c, 1, V(c, 0))`. -/
theorem pointwise_mediation_decomposition {C V : Type}
    (Y : C → Bool → V → Int)
    (V_real : C → Bool → V)
    (c : C) :
    Y c true (V_real c true) - Y c false (V_real c false) =
      (Y c true (V_real c false) - Y c false (V_real c false)) +
        (Y c true (V_real c true) - Y c true (V_real c false)) := by
  omega

/-- Expected Equation (2) (`expected_mediation_decomposition`, §3.2 Eq. 2):
    Over any finite query cohort `qs : List Q` with probability weights `w : Q → Int`,
    `β_T(c) = Δ_route(c) + Δ_vol(c)`. -/
theorem expected_mediation_decomposition {Q C V : Type}
    (qs : List Q)
    (w : Q → Int)
    (Y : Q → C → Bool → V → Int)
    (V_real : Q → C → Bool → V)
    (c : C) :
    listSumInt qs (fun q => w q * (Y q c true (V_real q c true) - Y q c false (V_real q c false))) =
      listSumInt qs (fun q => w q * (Y q c true (V_real q c false) - Y q c false (V_real q c false))) +
        listSumInt qs (fun q => w q * (Y q c true (V_real q c true) - Y q c true (V_real q c false))) := by
  rw [← listSumInt_add]
  apply listSumInt_congr
  intro q _
  have hPt := pointwise_mediation_decomposition (Y q) (V_real q) c
  rw [hPt, Int.mul_add]

/-- Pointwise Equation (3) (`eq:residual`):
    For any two routing policies `t, t' : Pol` evaluated at realized volumes `v_t, v_t' : V`,
    `Y(c, t, v_t) - Y(c, t', v_t') = (Y(c, t, v_t') - Y(c, t', v_t')) + R`,
    where `R = Y(c, t, v_t) - Y(c, t, v_t')`. -/
theorem pointwise_residual_identity {C Pol V : Type}
    (Y : C → Pol → V → Int)
    (c : C) (t t' : Pol) (v_t v_t' : V) :
    Y c t v_t - Y c t' v_t' =
      (Y c t v_t' - Y c t' v_t') + (Y c t v_t - Y c t v_t') := by
  omega

/-- Expected Equation (3) (`expected_residual_identity`, §3.2 Eq. 3):
    Over any finite query cohort `qs : List Q` with probability weights `w : Q → Int`,
    `E[Y(c, t, v_t)] - E[Y(c, t', v_t')] = (E[Y(c, t, v_t')] - E[Y(c, t', v_t')]) + R`. -/
theorem expected_residual_identity {Q C Pol V : Type}
    (qs : List Q)
    (w : Q → Int)
    (Y : Q → C → Pol → V → Int)
    (c : C) (t t' : Pol) (v_t v_t' : Q → V) :
    listSumInt qs (fun q => w q * Y q c t (v_t q)) -
      listSumInt qs (fun q => w q * Y q c t' (v_t' q)) =
      (listSumInt qs (fun q => w q * Y q c t (v_t' q)) -
        listSumInt qs (fun q => w q * Y q c t' (v_t' q))) +
      listSumInt qs (fun q => w q * (Y q c t (v_t q) - Y q c t (v_t' q))) := by
  rw [← listSumInt_sub, ← listSumInt_sub, ← listSumInt_add]
  apply listSumInt_congr
  intro q _
  rw [Int.mul_sub]
  omega

end WhoGetsLastWord
