import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import AppliedModelingLib.SocialChoice.Ranking.Mallows
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Exact Mallows Joint-Location Dynamic Program

This file formalizes the repeated-insertion dynamic program described in the
GGSG19 discussion of Theorem 4.  The stochastic semantics are expressed with
`PMF.bind`; the algorithm stores the same law as a dense real-valued table.
The correctness proof compares those two independently represented recursions
at every prefix.  The final table therefore gives the exact joint location law
for any two center ranks in the source's repeated-insertion model.
-/

open scoped BigOperators

namespace GGSG19TopThree

noncomputable section

/-- Unnormalized repeated-insertion mass at one stage. -/
def mallowsInsertionWeight {N : ℕ} (q : ℝ)
    (stage inserted : Fin N) : ℝ :=
  if inserted.val ≤ stage.val then q ^ (stage.val - inserted.val) else 0

/-- The finite geometric normalizer for one repeated-insertion stage. -/
def mallowsInsertionNormalizer {N : ℕ} (q : ℝ) (stage : Fin N) : ℝ :=
  Finset.sum (Finset.range (stage.val + 1))
    (fun r => q ^ (stage.val - r))

/-- The stage normalizer is positive throughout the source domain `0 ≤ q`. -/
theorem mallowsInsertionNormalizer_pos {N : ℕ} {q : ℝ}
    (hq : 0 ≤ q) (stage : Fin N) :
    0 < mallowsInsertionNormalizer q stage := by
  classical
  unfold mallowsInsertionNormalizer
  refine Finset.sum_pos' ?_ ?_
  · intro r _
    exact pow_nonneg hq _
  · exact ⟨stage.val, by simp, by simp⟩

/-- Summing the zero-extended `Fin N` weights gives the displayed normalizer. -/
theorem mallowsInsertionWeight_sum {N : ℕ} (q : ℝ) (stage : Fin N) :
    (∑ inserted : Fin N, mallowsInsertionWeight q stage inserted) =
      mallowsInsertionNormalizer q stage := by
  classical
  unfold mallowsInsertionWeight mallowsInsertionNormalizer
  calc
    (∑ inserted : Fin N,
        if inserted.val ≤ stage.val then
          q ^ (stage.val - inserted.val) else 0) =
        ∑ inserted ∈ Finset.range N,
          if inserted ≤ stage.val then q ^ (stage.val - inserted) else 0 := by
      simpa using
        (Fin.sum_univ_eq_sum_range
          (fun inserted : ℕ =>
            if inserted ≤ stage.val then q ^ (stage.val - inserted) else 0)
          N)
    _ = ∑ inserted ∈ Finset.range (stage.val + 1),
          if inserted ≤ stage.val then q ^ (stage.val - inserted) else 0 := by
      symm
      refine Finset.sum_subset ?_ ?_
      · intro inserted hin
        simp only [Finset.mem_range] at hin ⊢
        omega
      · intro inserted hinN hinSmall
        simp only [Finset.mem_range] at hinN hinSmall
        have hnot : ¬ inserted ≤ stage.val := by omega
        simp [hnot]
    _ = ∑ inserted ∈ Finset.range (stage.val + 1),
          q ^ (stage.val - inserted) := by
      refine Finset.sum_congr rfl ?_
      intro inserted hin
      have hle : inserted ≤ stage.val := by
        simpa [Finset.mem_range] using hin
      simp [hle]

/-- The source normalized insertion distribution, constructed from `q`. -/
noncomputable def mallowsInsertionPMF {N : ℕ} (q : ℝ)
    (hq : 0 ≤ q) (stage : Fin N) : PMF (Fin N) :=
  PMF.ofFintype
    (fun inserted : Fin N =>
      ENNReal.ofReal
        (mallowsInsertionWeight q stage inserted /
          mallowsInsertionNormalizer q stage))
    (by
      classical
      have hnormalizer_pos : 0 < mallowsInsertionNormalizer q stage :=
        mallowsInsertionNormalizer_pos hq stage
      have hnonneg :
          ∀ inserted ∈ (Finset.univ : Finset (Fin N)),
            0 ≤ mallowsInsertionWeight q stage inserted /
              mallowsInsertionNormalizer q stage := by
        intro inserted _
        exact div_nonneg
          (by
            unfold mallowsInsertionWeight
            split
            · exact pow_nonneg hq _
            · exact le_rfl)
          hnormalizer_pos.le
      have hsum :
          (∑ inserted : Fin N,
              mallowsInsertionWeight q stage inserted /
                mallowsInsertionNormalizer q stage) = 1 := by
        rw [(Finset.sum_div
          (s := (Finset.univ : Finset (Fin N)))
          (f := fun inserted : Fin N => mallowsInsertionWeight q stage inserted)
          (a := mallowsInsertionNormalizer q stage)).symm]
        rw [mallowsInsertionWeight_sum]
        exact div_self (ne_of_gt hnormalizer_pos)
      calc
        (∑ inserted : Fin N,
            ENNReal.ofReal
              (mallowsInsertionWeight q stage inserted /
                mallowsInsertionNormalizer q stage)) =
            ENNReal.ofReal
              (∑ inserted : Fin N,
                mallowsInsertionWeight q stage inserted /
                  mallowsInsertionNormalizer q stage) := by
              rw [ENNReal.ofReal_sum_of_nonneg hnonneg]
        _ = 1 := by rw [hsum]; simp)

@[simp] theorem mallowsInsertionPMF_apply_toReal {N : ℕ} (q : ℝ)
    (hq : 0 ≤ q) (stage inserted : Fin N) :
    ((mallowsInsertionPMF q hq stage) inserted).toReal =
      mallowsInsertionWeight q stage inserted /
        mallowsInsertionNormalizer q stage := by
  unfold mallowsInsertionPMF
  rw [PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal
    (div_nonneg
      (by
        unfold mallowsInsertionWeight
        split
        · exact pow_nonneg hq _
        · exact le_rfl)
      (mallowsInsertionNormalizer_pos hq stage).le)

/--
The source-cited Mallows repeated-insertion kernel.  At stage `k`, positions
`0,...,k` have mass proportional to `q^(k-j)` and all later positions have
mass zero.  Keeping the actual `PMF` and its displayed real formula together
prevents the dynamic program from assuming its desired output distribution.
-/
structure MallowsRepeatedInsertionModel (N : ℕ) where
  q : ℝ
  q_nonneg : 0 ≤ q
  q_le_one : q ≤ 1
  insertion : Fin N → PMF (Fin N)
  insertion_apply_toReal :
    ∀ (stage inserted : Fin N),
      ((insertion stage) inserted).toReal =
        if inserted.val ≤ stage.val then
          q ^ (stage.val - inserted.val) /
            Finset.sum (Finset.range (stage.val + 1))
              (fun r => q ^ (stage.val - r))
        else 0

namespace MallowsRepeatedInsertionModel

/-- Canonical source repeated-insertion model constructed from the noise parameter. -/
noncomputable def ofQ {N : ℕ} (q : ℝ) (hq_nonneg : 0 ≤ q)
    (hq_le_one : q ≤ 1) : MallowsRepeatedInsertionModel N where
  q := q
  q_nonneg := hq_nonneg
  q_le_one := hq_le_one
  insertion := fun stage => mallowsInsertionPMF q hq_nonneg stage
  insertion_apply_toReal := by
    intro stage inserted
    rw [mallowsInsertionPMF_apply_toReal]
    unfold mallowsInsertionWeight mallowsInsertionNormalizer
    by_cases hle : inserted.val ≤ stage.val <;> simp [hle]

end MallowsRepeatedInsertionModel

/-- The two tracked locations after a prefix of repeated insertions. -/
abbrev MallowsPairPositionState (N : ℕ) := Option (Fin N) × Option (Fin N)

/-- Neither tracked candidate has been inserted at the empty prefix. -/
def mallowsPairInitialState (N : ℕ) : MallowsPairPositionState N :=
  (none, none)

/--
Shift an already-present tracked item one slot down when a new item is inserted
weakly above it.  The saturated branch makes the function total on the dense
state space; it is unreachable in a valid repeated-insertion prefix.
-/
def mallowsBumpPosition {N : ℕ} (inserted current : Fin N) : Fin N :=
  if inserted.val ≤ current.val then
    if hnext : current.val + 1 < N then
      ⟨current.val + 1, hnext⟩
    else current
  else current

/-- Update one tracked location at one repeated-insertion stage. -/
def mallowsUpdateTrackedPosition {N : ℕ}
    (stage inserted trackedStage : Fin N) (current : Option (Fin N)) :
    Option (Fin N) :=
  if stage = trackedStage then
    some inserted
  else
    current.map (mallowsBumpPosition inserted)

/-- Update both tracked locations after one source-model insertion. -/
def mallowsUpdatePairState {N : ℕ}
    (leftStage rightStage stage inserted : Fin N)
    (state : MallowsPairPositionState N) : MallowsPairPositionState N :=
  (mallowsUpdateTrackedPosition stage inserted leftStage state.1,
    mallowsUpdateTrackedPosition stage inserted rightStage state.2)

/-- One stochastic repeated-insertion transition on the tracked pair. -/
noncomputable def mallowsPairTransition {N : ℕ}
    (model : MallowsRepeatedInsertionModel N)
    (leftStage rightStage stage : Fin N)
    (state : MallowsPairPositionState N) : PMF (MallowsPairPositionState N) :=
  (model.insertion stage).map
    (fun inserted =>
      mallowsUpdatePairState leftStage rightStage stage inserted state)

/--
Sequential PMF semantics of the source repeated-insertion process.  Prefixes
past `N` are stationary so the recursion is total on natural prefix lengths.
-/
noncomputable def mallowsPairProcess {N : ℕ}
    (model : MallowsRepeatedInsertionModel N)
    (leftStage rightStage : Fin N) :
    ℕ → PMF (MallowsPairPositionState N)
  | 0 => PMF.pure (mallowsPairInitialState N)
  | steps + 1 =>
      if hstage : steps < N then
        (mallowsPairProcess model leftStage rightStage steps).bind
          (mallowsPairTransition model leftStage rightStage ⟨steps, hstage⟩)
      else
        mallowsPairProcess model leftStage rightStage steps

/--
The executable mathematical dynamic program: a dense table of real masses.
Each stage performs the source recurrence by summing the previous-state mass
times the current repeated-insertion transition probability.
-/
noncomputable def mallowsPairDP {N : ℕ}
    (model : MallowsRepeatedInsertionModel N)
    (leftStage rightStage : Fin N) :
    ℕ → MallowsPairPositionState N → ℝ
  | 0, state =>
      ((PMF.pure (mallowsPairInitialState N) :
        PMF (MallowsPairPositionState N)) state).toReal
  | steps + 1, state =>
      if hstage : steps < N then
        ∑ previous : MallowsPairPositionState N,
          mallowsPairDP model leftStage rightStage steps previous *
            ((mallowsPairTransition model leftStage rightStage
              ⟨steps, hstage⟩ previous) state).toReal
      else
        mallowsPairDP model leftStage rightStage steps state

/-- A finite PMF bind is exactly finite matrix multiplication after `toReal`. -/
theorem pmf_bind_apply_toReal_finite
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (μ : PMF α) (kernel : α → PMF β) (target : β) :
    ((μ.bind kernel) target).toReal =
      ∑ source : α, (μ source).toReal * (kernel source target).toReal := by
  classical
  have hneTop :
      ∀ source ∈ (Finset.univ : Finset α),
        μ source * kernel source target ≠ ⊤ := by
    intro source _
    exact ENNReal.mul_ne_top
      (μ.apply_ne_top source) ((kernel source).apply_ne_top target)
  calc
    ((μ.bind kernel) target).toReal =
        (∑ source : α, μ source * kernel source target).toReal := by
          rw [PMF.bind_apply, tsum_fintype]
    _ = ∑ source : α, (μ source * kernel source target).toReal := by
          exact ENNReal.toReal_sum
            (s := (Finset.univ : Finset α))
            (f := fun source : α => μ source * kernel source target)
            hneTop
    _ = ∑ source : α,
        (μ source).toReal * (kernel source target).toReal := by
          simp [ENNReal.toReal_mul]

/--
Prefix-by-prefix correctness of the dynamic program against the independently
represented sequential PMF process.
-/
theorem mallowsPairDP_correct {N : ℕ}
    (model : MallowsRepeatedInsertionModel N)
    (leftStage rightStage : Fin N) (steps : ℕ)
    (state : MallowsPairPositionState N) :
    mallowsPairDP model leftStage rightStage steps state =
      ((mallowsPairProcess model leftStage rightStage steps) state).toReal := by
  classical
  induction steps generalizing state with
  | zero => rfl
  | succ steps ih =>
      rw [mallowsPairDP, mallowsPairProcess]
      split
      next hstage =>
        rw [pmf_bind_apply_toReal_finite]
        refine Finset.sum_congr rfl ?_
        intro previous _
        rw [ih previous]
      next _ =>
        exact ih state

/-- The final dynamic-program table is a normalized joint distribution. -/
theorem mallowsPairDP_sum_eq_one {N : ℕ}
    (model : MallowsRepeatedInsertionModel N)
    (leftStage rightStage : Fin N) :
    ∑ state : MallowsPairPositionState N,
      mallowsPairDP model leftStage rightStage N state = 1 := by
  classical
  simp_rw [mallowsPairDP_correct]
  exact AppliedModelingLib.pmfToRealSum
    (mallowsPairProcess model leftStage rightStage N)

/--
Dense-table scalar-operation budget: `N` stages, two state-table loops, and at
most `N` insertion positions when evaluating a mapped transition entry.
-/
def mallowsPairDPDenseOperationBudget (N : ℕ) : ℕ :=
  N * Fintype.card (MallowsPairPositionState N) *
    Fintype.card (MallowsPairPositionState N) * N

/-- The budget is the product of stages, target states, source states, and insertion choices. -/
theorem mallowsPairDPDenseOperationBudget_formula (N : ℕ) :
    mallowsPairDPDenseOperationBudget N = N ^ 2 * (N + 1) ^ 4 := by
  simp [mallowsPairDPDenseOperationBudget, MallowsPairPositionState]
  ring

/-- The dense exact dynamic program has an explicit degree-six polynomial bound. -/
theorem mallowsPairDPDenseOperationBudget_le (N : ℕ) :
    mallowsPairDPDenseOperationBudget N ≤ (N + 1) ^ 6 := by
  have hpow : N ^ 2 ≤ (N + 1) ^ 2 :=
    Nat.pow_le_pow_left (Nat.le_succ N) 2
  calc
    mallowsPairDPDenseOperationBudget N = N ^ 2 * (N + 1) ^ 4 :=
      mallowsPairDPDenseOperationBudget_formula N
    _ ≤ (N + 1) ^ 2 * (N + 1) ^ 4 :=
      Nat.mul_le_mul_right ((N + 1) ^ 4) hpow
    _ = (N + 1) ^ 6 := by ring

/-! ## Explicit costed tabulation runner -/

/--
One transition-table cell evaluated by the literal finite insertion loop.  It
does not call the semantic `PMF.map` transition as an oracle.
-/
noncomputable def mallowsPairExplicitTransitionMass {N : ℕ}
    (model : MallowsRepeatedInsertionModel N)
    (leftStage rightStage stage : Fin N)
    (previous target : MallowsPairPositionState N) : ℝ :=
  ∑ inserted : Fin N,
    if target =
        mallowsUpdatePairState leftStage rightStage stage inserted previous then
      ((model.insertion stage) inserted).toReal
    else 0

/-- The explicit insertion loop computes exactly the mapped transition mass. -/
theorem mallowsPairExplicitTransitionMass_eq_transition {N : ℕ}
    (model : MallowsRepeatedInsertionModel N)
    (leftStage rightStage stage : Fin N)
    (previous target : MallowsPairPositionState N) :
    mallowsPairExplicitTransitionMass model leftStage rightStage stage
        previous target =
      ((mallowsPairTransition model leftStage rightStage stage previous)
        target).toReal := by
  classical
  unfold mallowsPairExplicitTransitionMass mallowsPairTransition
  rw [PMF.map_apply, tsum_fintype]
  have hneTop :
      ∀ inserted ∈ (Finset.univ : Finset (Fin N)),
        (if target =
            mallowsUpdatePairState leftStage rightStage stage inserted previous then
          model.insertion stage inserted else 0) ≠ ⊤ := by
    intro inserted _
    split
    · exact (model.insertion stage).apply_ne_top inserted
    · simp
  have hneTopClassical :
      ∀ inserted ∈ (Finset.univ : Finset (Fin N)),
        (@ite ENNReal
          (target =
            mallowsUpdatePairState leftStage rightStage stage inserted previous)
          (Classical.propDecidable _)
          (model.insertion stage inserted) 0) ≠ ⊤ := by
    intro inserted _
    by_cases htarget :
        target = mallowsUpdatePairState leftStage rightStage stage inserted previous
    · simp [htarget, (model.insertion stage).apply_ne_top inserted]
    · simp [htarget]
  symm
  calc
    (∑ inserted : Fin N,
        @ite ENNReal
          (target =
            mallowsUpdatePairState leftStage rightStage stage inserted previous)
          (Classical.propDecidable _)
          (model.insertion stage inserted) 0).toReal =
        ∑ inserted : Fin N,
          (@ite ENNReal
            (target =
              mallowsUpdatePairState leftStage rightStage stage inserted previous)
            (Classical.propDecidable _)
            (model.insertion stage inserted) 0).toReal := by
          exact ENNReal.toReal_sum
            (s := (Finset.univ : Finset (Fin N)))
            (f := fun inserted : Fin N =>
              @ite ENNReal
                (target =
                  mallowsUpdatePairState leftStage rightStage stage inserted previous)
                (Classical.propDecidable _)
                (model.insertion stage inserted) 0)
            hneTopClassical
    _ = ∑ inserted : Fin N,
        if target = mallowsUpdatePairState leftStage rightStage stage inserted previous then
          ((model.insertion stage) inserted).toReal
        else 0 := by
          refine Finset.sum_congr rfl ?_
          intro inserted _
          by_cases htarget :
              target = mallowsUpdatePairState leftStage rightStage stage inserted previous
          · simp [htarget]
          · simp [htarget]

/--
One dense tabulation stage: for every target state, sum over every previous
state, evaluating each transition by its explicit insertion loop.
-/
noncomputable def mallowsPairExplicitTableStep {N : ℕ}
    (model : MallowsRepeatedInsertionModel N)
    (leftStage rightStage stage : Fin N)
    (previousTable : MallowsPairPositionState N → ℝ) :
    MallowsPairPositionState N → ℝ :=
  fun target =>
    ∑ previous : MallowsPairPositionState N,
      previousTable previous *
        mallowsPairExplicitTransitionMass model leftStage rightStage stage
          previous target

/-- Result of the explicit runner, including its transparent arithmetic count. -/
structure MallowsPairDPTabulationResult (N : ℕ) where
  table : MallowsPairPositionState N → ℝ
  scalarOperations : ℕ

/--
Materialized dense-tabulation runner.  Each active stage constructs a new
table from the previous table and charges one unit for every
target/source/insertion triple.  This is the algorithm whose cost is certified
below; the semantic PMF process is used only in the refinement proof.
-/
noncomputable def mallowsPairDPTabulationRun {N : ℕ}
    (model : MallowsRepeatedInsertionModel N)
    (leftStage rightStage : Fin N) :
    ℕ → MallowsPairDPTabulationResult N
  | 0 =>
      { table := fun state =>
          ((PMF.pure (mallowsPairInitialState N) :
            PMF (MallowsPairPositionState N)) state).toReal
        scalarOperations := 0 }
  | steps + 1 =>
      let previous :=
        mallowsPairDPTabulationRun model leftStage rightStage steps
      if hstage : steps < N then
        { table :=
            mallowsPairExplicitTableStep model leftStage rightStage
              ⟨steps, hstage⟩ previous.table
          scalarOperations :=
            previous.scalarOperations +
              Fintype.card (MallowsPairPositionState N) *
                Fintype.card (MallowsPairPositionState N) * N }
      else previous

/-- The costed runner's materialized table refines the mathematical DP. -/
theorem mallowsPairDPTabulationRun_table_eq_dp {N : ℕ}
    (model : MallowsRepeatedInsertionModel N)
    (leftStage rightStage : Fin N) (steps : ℕ) :
    (mallowsPairDPTabulationRun model leftStage rightStage steps).table =
      mallowsPairDP model leftStage rightStage steps := by
  classical
  induction steps with
  | zero => rfl
  | succ steps ih =>
      funext target
      rw [mallowsPairDPTabulationRun, mallowsPairDP]
      split
      next hstage =>
        unfold mallowsPairExplicitTableStep
        refine Finset.sum_congr rfl ?_
        intro previous _
        rw [ih, mallowsPairExplicitTransitionMass_eq_transition]
      next _ =>
        exact congrFun ih target

/-- Up to the final source stage, the counter is the literal dense-loop size. -/
theorem mallowsPairDPTabulationRun_scalarOperations_of_le {N : ℕ}
    (model : MallowsRepeatedInsertionModel N)
    (leftStage rightStage : Fin N) (steps : ℕ) (hsteps : steps ≤ N) :
    (mallowsPairDPTabulationRun model leftStage rightStage steps).scalarOperations =
      steps * Fintype.card (MallowsPairPositionState N) *
        Fintype.card (MallowsPairPositionState N) * N := by
  induction steps with
  | zero => simp [mallowsPairDPTabulationRun]
  | succ steps ih =>
      have hlt : steps < N := Nat.lt_of_succ_le hsteps
      rw [mallowsPairDPTabulationRun, dif_pos hlt, ih (Nat.le_of_succ_le hsteps)]
      ring

/-- At `N` stages, the runner counter is exactly the advertised budget. -/
theorem mallowsPairDPTabulationRun_scalarOperations_eq_budget {N : ℕ}
    (model : MallowsRepeatedInsertionModel N)
    (leftStage rightStage : Fin N) :
    (mallowsPairDPTabulationRun model leftStage rightStage N).scalarOperations =
      mallowsPairDPDenseOperationBudget N := by
  rw [mallowsPairDPTabulationRun_scalarOperations_of_le
    model leftStage rightStage N le_rfl]
  rfl

/-- The operational runner's table is the exact final process distribution. -/
theorem mallowsPairDPTabulationRun_correct {N : ℕ}
    (model : MallowsRepeatedInsertionModel N)
    (leftStage rightStage : Fin N)
    (state : MallowsPairPositionState N) :
    (mallowsPairDPTabulationRun model leftStage rightStage N).table state =
      ((mallowsPairProcess model leftStage rightStage N) state).toReal := by
  rw [mallowsPairDPTabulationRun_table_eq_dp]
  exact mallowsPairDP_correct model leftStage rightStage N state

/-- The operational runner's final table is normalized. -/
theorem mallowsPairDPTabulationRun_sum_eq_one {N : ℕ}
    (model : MallowsRepeatedInsertionModel N)
    (leftStage rightStage : Fin N) :
    ∑ state : MallowsPairPositionState N,
      (mallowsPairDPTabulationRun model leftStage rightStage N).table state = 1 := by
  simp_rw [mallowsPairDPTabulationRun_correct]
  exact AppliedModelingLib.pmfToRealSum
    (mallowsPairProcess model leftStage rightStage N)

/--
Transparent semantic contract for the source algorithm.  The contract names
the exact final-cell law, normalization, and the unit-cost dense recurrence
budget; it is kept separate from the proof theorem so the audit can compare
the advertised algorithm with a concrete proposition rather than a theorem
name.
-/
def MallowsArbitraryPairJointLocationDPSpec
    {N : ℕ} (model : MallowsRepeatedInsertionModel N)
    (leftStage rightStage : Fin N) : Prop :=
  (∀ state : MallowsPairPositionState N,
    (mallowsPairDPTabulationRun model leftStage rightStage N).table state =
      ((mallowsPairProcess model leftStage rightStage N) state).toReal) ∧
    (∑ state : MallowsPairPositionState N,
      (mallowsPairDPTabulationRun model leftStage rightStage N).table state = 1) ∧
    (mallowsPairDPTabulationRun model leftStage rightStage N).scalarOperations =
      mallowsPairDPDenseOperationBudget N ∧
    (mallowsPairDPTabulationRun model leftStage rightStage N).scalarOperations ≤
      (N + 1) ^ 6

/--
The source's advertised arbitrary-pair joint-location dynamic program: every
final table cell is exactly the corresponding repeated-insertion probability,
the cells sum to one, and dense evaluation has a polynomial operation bound.
-/
theorem mallows_arbitrary_pair_joint_location_dp_exact_and_polynomial
    {N : ℕ} (model : MallowsRepeatedInsertionModel N)
    (leftStage rightStage : Fin N) :
    (∀ state : MallowsPairPositionState N,
      (mallowsPairDPTabulationRun model leftStage rightStage N).table state =
        ((mallowsPairProcess model leftStage rightStage N) state).toReal) ∧
      (∑ state : MallowsPairPositionState N,
        (mallowsPairDPTabulationRun model leftStage rightStage N).table state = 1) ∧
      (mallowsPairDPTabulationRun model leftStage rightStage N).scalarOperations =
        mallowsPairDPDenseOperationBudget N ∧
      (mallowsPairDPTabulationRun model leftStage rightStage N).scalarOperations ≤
        (N + 1) ^ 6 := by
  refine ⟨mallowsPairDPTabulationRun_correct model leftStage rightStage,
    mallowsPairDPTabulationRun_sum_eq_one model leftStage rightStage,
    mallowsPairDPTabulationRun_scalarOperations_eq_budget
      model leftStage rightStage, ?_⟩
  rw [mallowsPairDPTabulationRun_scalarOperations_eq_budget]
  exact mallowsPairDPDenseOperationBudget_le N

/-- The checked algorithm theorem discharges its transparent semantic contract. -/
theorem mallows_arbitrary_pair_joint_location_dp_spec
    {N : ℕ} (model : MallowsRepeatedInsertionModel N)
    (leftStage rightStage : Fin N) :
    MallowsArbitraryPairJointLocationDPSpec model leftStage rightStage :=
  mallows_arbitrary_pair_joint_location_dp_exact_and_polynomial
    model leftStage rightStage

end

end GGSG19TopThree
