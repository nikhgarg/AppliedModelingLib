import AppliedModelingLib.Learning.Online.SequentialComplexity
import AppliedModelingLib.Learning.Online.SequentialRelaxation
import Mathlib.Tactic

/-!
# Bounded sequential minimax for correlation learning

This module gives a noncomputable minimax construction for an arbitrary
bounded class of real-valued comparators.  Its potential is the sequential
Rademacher relaxation with a doubled future perturbation.  The doubling is
what permits predictions to remain in `[-1, 1]` while giving the usual factor
two sequential-complexity upper bound.

The constructions are finite-horizon, but neither the context type nor the
comparator type is required to be finite.
-/

namespace AppliedModelingLib.Learning.Online

open scoped BigOperators

/-- Attach two continuation trees below a common current context.  The branch
selected by the first Rademacher sign supplies all later contexts. -/
def SequentialTree.splice {Context : Type*} {remaining : ℕ} (root : Context)
    (continuations : Bool → SequentialTree Context remaining) :
    SequentialTree Context (remaining + 1) :=
  fun ⟨round, hround⟩ history =>
    match round with
    | 0 => root
    | laterRound + 1 =>
        continuations (history ⟨0, Nat.succ_pos _⟩)
          ⟨laterRound, Nat.lt_of_succ_lt_succ hround⟩
          (fun earlierRound =>
            history ⟨earlierRound.1 + 1, Nat.succ_lt_succ earlierRound.2⟩)

/-- The root of a spliced sequential tree is its prescribed current context. -/
@[simp] theorem SequentialTree.splice_eval_zero {Context : Type*} {remaining : ℕ}
    (root : Context) (continuations : Bool → SequentialTree Context remaining)
    (signs : Fin (remaining + 1) → Bool) :
    (SequentialTree.splice root continuations).eval signs 0 = root := by
  simp [SequentialTree.splice, SequentialTree.eval]

/-- After the root, evaluation of a spliced tree follows the continuation
chosen by the first Rademacher sign. -/
@[simp] theorem SequentialTree.splice_eval_succ {Context : Type*} {remaining : ℕ}
    (root : Context) (continuations : Bool → SequentialTree Context remaining)
    (signs : Fin (remaining + 1) → Bool) (round : Fin remaining) :
    (SequentialTree.splice root continuations).eval signs round.succ =
      (continuations (signs 0)).eval (Fin.tail signs) round := by
  simp only [SequentialTree.splice, SequentialTree.eval]
  congr 1

/-- The correlation of a comparator with the observations already revealed to
the learner. -/
def sequentialHistoryCorrelation {Context Hypothesis : Type*}
    (evaluation : Hypothesis → Context → ℝ) (hypothesis : Hypothesis)
    (history : List (Context × ℝ)) : ℝ :=
  (history.map fun observation => evaluation hypothesis observation.1 * observation.2).sum

/-- The future signed correlation of a comparator along one adaptive context
tree.  The scale parameter is kept explicit so the ordinary Rademacher process
and the doubled minimax relaxation share the same definition. -/
def sequentialFutureCorrelation {Context Hypothesis : Type*} {horizon : ℕ}
    (evaluation : Hypothesis → Context → ℝ) (hypothesis : Hypothesis)
    (tree : SequentialTree Context horizon) (signs : Fin horizon → Bool) : ℝ :=
  ∑ round, rademacherSign (signs round) * evaluation hypothesis (tree.eval signs round)

/-- The pointwise comparator envelope at a history and a future Rademacher
path. -/
noncomputable def sequentialCorrelationEnvelope {Context Hypothesis : Type*}
    [Nonempty Hypothesis] {horizon : ℕ}
    (evaluation : Hypothesis → Context → ℝ) (history : List (Context × ℝ))
    (scale : ℝ) (tree : SequentialTree Context horizon)
    (signs : Fin horizon → Bool) : ℝ :=
  sSup (Set.range fun hypothesis =>
    sequentialHistoryCorrelation evaluation hypothesis history +
      scale * sequentialFutureCorrelation evaluation hypothesis tree signs)

/-- The comparator envelope associated with one prescribed root branch of a
doubled-future sequential Rademacher tree. -/
noncomputable def rootBranchEnvelope {Context Hypothesis : Type*}
    [Nonempty Hypothesis] {remaining : ℕ}
    (evaluation : Hypothesis → Context → ℝ) (history : List (Context × ℝ))
    (root : Context) (branch : Bool) (tree : SequentialTree Context remaining)
    (signs : Fin remaining → Bool) : ℝ :=
  sSup (Set.range fun hypothesis =>
    sequentialHistoryCorrelation evaluation hypothesis history +
      2 * rademacherSign branch * evaluation hypothesis root +
        2 * sequentialFutureCorrelation evaluation hypothesis tree signs)

/-- The future correlation of a spliced tree separates into its root term and
the future correlation of the Rademacher-selected continuation. -/
theorem sequentialFutureCorrelation_splice {Context Hypothesis : Type*} {remaining : ℕ}
    (evaluation : Hypothesis → Context → ℝ) (hypothesis : Hypothesis)
    (root : Context) (continuations : Bool → SequentialTree Context remaining)
    (branch : Bool) (signs : Fin remaining → Bool) :
    sequentialFutureCorrelation evaluation hypothesis (SequentialTree.splice root continuations)
      (Fin.cons branch signs) =
        rademacherSign branch * evaluation hypothesis root +
          sequentialFutureCorrelation evaluation hypothesis (continuations branch) signs := by
  unfold sequentialFutureCorrelation
  rw [Fin.sum_univ_succ]
  simp

/-- The doubled-future envelope of a spliced tree is its corresponding root
branch envelope after the first Rademacher sign is fixed. -/
theorem sequentialCorrelationEnvelope_splice {Context Hypothesis : Type*}
    [Nonempty Hypothesis] {remaining : ℕ}
    (evaluation : Hypothesis → Context → ℝ) (history : List (Context × ℝ))
    (root : Context) (continuations : Bool → SequentialTree Context remaining)
    (branch : Bool) (signs : Fin remaining → Bool) :
    sequentialCorrelationEnvelope evaluation history 2 (SequentialTree.splice root continuations)
      (Fin.cons branch signs) =
        rootBranchEnvelope evaluation history root branch (continuations branch) signs := by
  unfold sequentialCorrelationEnvelope rootBranchEnvelope
  apply congrArg sSup
  ext score
  constructor
  · rintro ⟨hypothesis, rfl⟩
    refine ⟨hypothesis, ?_⟩
    have hfuture :=
      sequentialFutureCorrelation_splice evaluation hypothesis root continuations branch signs
    have hscore : sequentialHistoryCorrelation evaluation hypothesis history + 2 *
        sequentialFutureCorrelation evaluation hypothesis (SequentialTree.splice root continuations)
          (Fin.cons branch signs) =
        sequentialHistoryCorrelation evaluation hypothesis history +
          2 * rademacherSign branch * evaluation hypothesis root +
            2 * sequentialFutureCorrelation evaluation hypothesis (continuations branch) signs := by
      rw [hfuture]
      ring
    simpa using hscore.symm
  · rintro ⟨hypothesis, rfl⟩
    refine ⟨hypothesis, ?_⟩
    have hfuture :=
      sequentialFutureCorrelation_splice evaluation hypothesis root continuations branch signs
    have hscore : sequentialHistoryCorrelation evaluation hypothesis history + 2 *
        sequentialFutureCorrelation evaluation hypothesis (SequentialTree.splice root continuations)
          (Fin.cons branch signs) =
        sequentialHistoryCorrelation evaluation hypothesis history +
          2 * rademacherSign branch * evaluation hypothesis root +
            2 * sequentialFutureCorrelation evaluation hypothesis (continuations branch) signs := by
      rw [hfuture]
      ring
    simpa using hscore

/-- The expected root-branch envelope on one continuation tree. -/
noncomputable def rootBranchValue {Context Hypothesis : Type*}
    [Nonempty Hypothesis] {remaining : ℕ}
    (evaluation : Hypothesis → Context → ℝ) (history : List (Context × ℝ))
    (root : Context) (branch : Bool) (tree : SequentialTree Context remaining) : ℝ :=
  pmfExp (pmfProduct (Fin remaining) Bool (uniformPMF Bool))
    (rootBranchEnvelope evaluation history root branch tree)

/-- The best expected root-branch value over all adaptive continuations. -/
noncomputable def rootBranchPotential {Context Hypothesis : Type*}
    [Nonempty Context] [Nonempty Hypothesis] (evaluation : Hypothesis → Context → ℝ)
    (history : List (Context × ℝ)) (root : Context) (branch : Bool)
    (remaining : ℕ) : ℝ :=
  sSup (Set.range (rootBranchValue evaluation history root branch :
    SequentialTree Context remaining → ℝ))

/-- The continuation value of a tree spliced at a root is the average of the
two root-branch values. -/
theorem doubledContinuation_splice_eq_average_branchValues {Context Hypothesis : Type*}
    [Nonempty Hypothesis] {remaining : ℕ}
    (evaluation : Hypothesis → Context → ℝ) (history : List (Context × ℝ))
    (root : Context) (continuations : Bool → SequentialTree Context remaining) :
    pmfExp (pmfProduct (Fin (remaining + 1)) Bool (uniformPMF Bool))
        (sequentialCorrelationEnvelope evaluation history 2 (SequentialTree.splice root continuations)) =
      (rootBranchValue evaluation history root true (continuations true) +
        rootBranchValue evaluation history root false (continuations false)) / 2 := by
  rw [pmfExp_pmfProduct_finCons_eq_pairExp]
  unfold pmfPairExp
  rw [show (fun signs =>
      pmfExp (uniformPMF Bool) (fun branch =>
        sequentialCorrelationEnvelope evaluation history 2 (SequentialTree.splice root continuations)
          (Fin.cons branch signs))) =
      fun signs =>
        (rootBranchEnvelope evaluation history root true (continuations true) signs +
          rootBranchEnvelope evaluation history root false (continuations false) signs) / 2 by
        funext signs
        rw [pmfExp_uniformPMF_bool_eq_average]
        rw [sequentialCorrelationEnvelope_splice, sequentialCorrelationEnvelope_splice]
    ]
  rw [show (fun signs =>
      (rootBranchEnvelope evaluation history root true (continuations true) signs +
        rootBranchEnvelope evaluation history root false (continuations false) signs) / 2) =
      fun signs => (1 / 2 : ℝ) *
        (rootBranchEnvelope evaluation history root true (continuations true) signs +
          rootBranchEnvelope evaluation history root false (continuations false) signs) by
        funext signs
        ring]
  rw [pmfExp_const_mul, pmfExp_add]
  unfold rootBranchValue
  ring

/-- The ordinary unnormalized sequential Rademacher value on one context tree
for an arbitrary nonempty comparator type. -/
noncomputable def boundedSequentialRademacherSum {Context Hypothesis : Type*}
    [Nonempty Hypothesis] {horizon : ℕ}
    (evaluation : Hypothesis → Context → ℝ)
    (tree : SequentialTree Context horizon) : ℝ :=
  pmfExp (pmfProduct (Fin horizon) Bool (uniformPMF Bool))
    (sequentialCorrelationEnvelope evaluation [] 1 tree)

/-- The unnormalized sequential Rademacher process for an arbitrary bounded
class.  Boundedness hypotheses are supplied to the theorems that use this
definition, not hidden in the data. -/
noncomputable def boundedSequentialRademacherProcess {Context Hypothesis : Type*}
    [Nonempty Context] [Nonempty Hypothesis] {horizon : ℕ}
    (evaluation : Hypothesis → Context → ℝ) : ℝ :=
  sSup (Set.range (boundedSequentialRademacherSum evaluation :
    SequentialTree Context horizon → ℝ))

/-- The source-normalized sequential Rademacher complexity. -/
noncomputable def boundedSequentialRademacherComplexity {Context Hypothesis : Type*}
    [Nonempty Context] [Nonempty Hypothesis] {horizon : ℕ}
    (evaluation : Hypothesis → Context → ℝ) : ℝ :=
  boundedSequentialRademacherProcess (horizon := horizon) evaluation / (horizon : ℝ)

/-- The doubled-future sequential Rademacher relaxation.  The history is
scored with its actual labels, while the remaining adaptive tree is scored
against fresh Rademacher signs at twice their ordinary scale. -/
noncomputable def boundedSequentialMinimaxPotential {Context Hypothesis : Type*}
    [Nonempty Context] [Nonempty Hypothesis]
    (evaluation : Hypothesis → Context → ℝ) (history : List (Context × ℝ))
    (remaining : ℕ) : ℝ :=
  sSup (Set.range fun tree : SequentialTree Context remaining =>
    pmfExp (pmfProduct (Fin remaining) Bool (uniformPMF Bool))
      (sequentialCorrelationEnvelope evaluation history 2 tree))

/-- The deterministic minimax prediction selected from the two one-step
continuation values of the doubled sequential relaxation. -/
noncomputable def boundedSequentialMinimaxStrategy {Context Hypothesis : Type*}
    [Nonempty Context] [Nonempty Hypothesis]
    (evaluation : Hypothesis → Context → ℝ) (horizon : ℕ)
    (history : List (Context × ℝ)) (context : Context) : ℝ :=
  let remaining := horizon - history.length - 1
  (boundedSequentialMinimaxPotential evaluation (history ++ [(context, 1)]) remaining -
    boundedSequentialMinimaxPotential evaluation (history ++ [(context, -1)]) remaining) / 2

/-- Multiplication by two commutes with the supremum of a nonempty bounded
real-valued range. -/
theorem two_mul_sSup_range {α : Type*} [Nonempty α] (value : α → ℝ)
    (hbounded : BddAbove (Set.range value)) :
    sSup (Set.range fun item => 2 * value item) = 2 * sSup (Set.range value) := by
  have hscaled : BddAbove (Set.range fun item => 2 * value item) := by
    rcases hbounded with ⟨upper, hupper⟩
    refine ⟨2 * upper, ?_⟩
    rintro _ ⟨item, rfl⟩
    exact mul_le_mul_of_nonneg_left (hupper ⟨item, rfl⟩) (by norm_num)
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨item, rfl⟩
    exact mul_le_mul_of_nonneg_left (le_csSup hbounded ⟨item, rfl⟩) (by norm_num)
  · refine (le_csSup_iff hscaled (Set.range_nonempty _)).mpr ?_
    intro upper hupper
    have hhalf : ∀ item, value item ≤ upper / 2 := by
      intro item
      have h := hupper ⟨item, rfl⟩
      nlinarith
    have hsup : sSup (Set.range value) ≤ upper / 2 :=
      csSup_le (Set.range_nonempty _) (fun item hitem => by
        rcases hitem with ⟨item, rfl⟩
        exact hhalf item)
    nlinarith

/-- A comparator bounded by one in absolute value has at most one unit of
correlation with each past unit-label observation. -/
theorem sequentialHistoryCorrelation_le_length {Context Hypothesis : Type*}
    (evaluation : Hypothesis → Context → ℝ) (hypothesis : Hypothesis)
    (history : List (Context × ℝ))
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (hhistory : ∀ observation ∈ history, observation.2 ∈ Set.Icc (-1 : ℝ) 1) :
    sequentialHistoryCorrelation evaluation hypothesis history ≤ history.length := by
  induction history with
  | nil => simp [sequentialHistoryCorrelation]
  | cons observation history inductionHypothesis =>
      have hterm : evaluation hypothesis observation.1 * observation.2 ≤ 1 := by
        have hevaluation' := hevaluation hypothesis observation.1
        have hlabel := hhistory observation (by simp)
        calc
          evaluation hypothesis observation.1 * observation.2 ≤
              |evaluation hypothesis observation.1 * observation.2| := le_abs_self _
          _ = |evaluation hypothesis observation.1| * |observation.2| := abs_mul _ _
          _ ≤ 1 * 1 :=
            mul_le_mul (abs_le.mpr hevaluation') (abs_le.mpr hlabel) (abs_nonneg _) (by norm_num)
          _ = 1 := by norm_num
      have htail : ∀ later ∈ history, later.2 ∈ Set.Icc (-1 : ℝ) 1 := by
        intro later hlater
        exact hhistory later (by simp [hlater])
      have hrest := inductionHypothesis htail
      have hsum := add_le_add hterm hrest
      simpa [sequentialHistoryCorrelation, add_comm] using hsum

/-- The signed future correlation of a unit-bounded comparator is no larger
than the number of remaining rounds. -/
theorem sequentialFutureCorrelation_le_horizon {Context Hypothesis : Type*}
    {horizon : ℕ} (evaluation : Hypothesis → Context → ℝ) (hypothesis : Hypothesis)
    (tree : SequentialTree Context horizon) (signs : Fin horizon → Bool)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1) :
    sequentialFutureCorrelation evaluation hypothesis tree signs ≤ horizon := by
  unfold sequentialFutureCorrelation
  calc
    (∑ round, rademacherSign (signs round) * evaluation hypothesis (tree.eval signs round)) ≤
        ∑ _round : Fin horizon, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro round _
          have hevaluation' := hevaluation hypothesis (tree.eval signs round)
          unfold rademacherSign
          split_ifs with hsign
          · simpa [hsign] using hevaluation'.2
          · have hlower := hevaluation'.1
            linarith
    _ = horizon := by simp

/-- The doubled-future envelope is bounded above by the past length plus two
per remaining round whenever both comparator values and labels lie in the
unit interval. -/
theorem sequentialCorrelationEnvelope_le_historyLength_add_two_mul {Context Hypothesis : Type*}
    [Nonempty Hypothesis] {horizon : ℕ}
    (evaluation : Hypothesis → Context → ℝ) (history : List (Context × ℝ))
    (tree : SequentialTree Context horizon) (signs : Fin horizon → Bool)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (hhistory : ∀ observation ∈ history, observation.2 ∈ Set.Icc (-1 : ℝ) 1) :
    sequentialCorrelationEnvelope evaluation history 2 tree signs ≤
      history.length + 2 * horizon := by
  unfold sequentialCorrelationEnvelope
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨hypothesis, rfl⟩
  have hpast := sequentialHistoryCorrelation_le_length evaluation hypothesis history
    hevaluation hhistory
  have hfuture := sequentialFutureCorrelation_le_horizon evaluation hypothesis tree signs
    hevaluation
  norm_num
  nlinarith

/-- Every doubled-future minimax potential is finite above under the source's
unit-range hypothesis. -/
theorem boundedSequentialMinimaxPotential_le_historyLength_add_two_mul
    {Context Hypothesis : Type*} [Nonempty Context] [Nonempty Hypothesis]
    (evaluation : Hypothesis → Context → ℝ) (history : List (Context × ℝ))
    (remaining : ℕ)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (hhistory : ∀ observation ∈ history, observation.2 ∈ Set.Icc (-1 : ℝ) 1) :
    boundedSequentialMinimaxPotential evaluation history remaining ≤
      history.length + 2 * remaining := by
  unfold boundedSequentialMinimaxPotential
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨tree, rfl⟩
  apply pmfExp_le_of_forall_le
  intro signs
  exact sequentialCorrelationEnvelope_le_historyLength_add_two_mul evaluation history tree signs
    hevaluation hhistory

/-- The continuation values whose supremum defines a doubled-future minimax
potential are bounded above under the source's unit-range condition. -/
theorem boundedSequentialMinimaxPotential_continuations_bddAbove
    {Context Hypothesis : Type*} [Nonempty Context] [Nonempty Hypothesis]
    (evaluation : Hypothesis → Context → ℝ) (history : List (Context × ℝ))
    (remaining : ℕ)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (hhistory : ∀ observation ∈ history, observation.2 ∈ Set.Icc (-1 : ℝ) 1) :
    BddAbove (Set.range fun tree : SequentialTree Context remaining =>
      pmfExp (pmfProduct (Fin remaining) Bool (uniformPMF Bool))
        (sequentialCorrelationEnvelope evaluation history 2 tree)) := by
  refine ⟨history.length + 2 * remaining, ?_⟩
  rintro _ ⟨tree, rfl⟩
  apply pmfExp_le_of_forall_le
  intro signs
  exact sequentialCorrelationEnvelope_le_historyLength_add_two_mul evaluation history tree signs
    hevaluation hhistory

/-- A root-branch envelope is bounded by the history length plus two for the
root perturbation and two for each later Rademacher perturbation. -/
theorem rootBranchEnvelope_le_historyLength_add_two_add_two_mul
    {Context Hypothesis : Type*} [Nonempty Hypothesis] {remaining : ℕ}
    (evaluation : Hypothesis → Context → ℝ) (history : List (Context × ℝ))
    (root : Context) (branch : Bool) (tree : SequentialTree Context remaining)
    (signs : Fin remaining → Bool)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (hhistory : ∀ observation ∈ history, observation.2 ∈ Set.Icc (-1 : ℝ) 1) :
    rootBranchEnvelope evaluation history root branch tree signs ≤
      history.length + 2 + 2 * remaining := by
  unfold rootBranchEnvelope
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨hypothesis, rfl⟩
  have hpast := sequentialHistoryCorrelation_le_length evaluation hypothesis history
    hevaluation hhistory
  have hfuture := sequentialFutureCorrelation_le_horizon evaluation hypothesis tree signs
    hevaluation
  have hroot : 2 * rademacherSign branch * evaluation hypothesis root ≤ 2 := by
    have hevaluation' := hevaluation hypothesis root
    unfold rademacherSign
    split_ifs with hbranch
    · nlinarith [hevaluation'.2]
    · nlinarith [hevaluation'.1]
  norm_num
  nlinarith

/-- The comparator scores inside one root-branch envelope are bounded above
under the source's unit-range hypothesis. -/
theorem rootBranchEnvelope_candidates_bddAbove {Context Hypothesis : Type*}
    [Nonempty Hypothesis] {remaining : ℕ}
    (evaluation : Hypothesis → Context → ℝ) (history : List (Context × ℝ))
    (root : Context) (branch : Bool) (tree : SequentialTree Context remaining)
    (signs : Fin remaining → Bool)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (hhistory : ∀ observation ∈ history, observation.2 ∈ Set.Icc (-1 : ℝ) 1) :
    BddAbove (Set.range fun hypothesis =>
      sequentialHistoryCorrelation evaluation hypothesis history +
        2 * rademacherSign branch * evaluation hypothesis root +
          2 * sequentialFutureCorrelation evaluation hypothesis tree signs) := by
  refine ⟨history.length + 2 + 2 * remaining, ?_⟩
  rintro _ ⟨hypothesis, rfl⟩
  have hpast := sequentialHistoryCorrelation_le_length evaluation hypothesis history
    hevaluation hhistory
  have hfuture := sequentialFutureCorrelation_le_horizon evaluation hypothesis tree signs
    hevaluation
  have hroot : 2 * rademacherSign branch * evaluation hypothesis root ≤ 2 := by
    have hevaluation' := hevaluation hypothesis root
    unfold rademacherSign
    split_ifs with hbranch
    · nlinarith [hevaluation'.2]
    · nlinarith [hevaluation'.1]
  norm_num
  nlinarith

/-- Root-branch values form a bounded-above range under the source's
unit-range hypothesis. -/
theorem rootBranchValue_bddAbove {Context Hypothesis : Type*}
    [Nonempty Hypothesis] {remaining : ℕ}
    (evaluation : Hypothesis → Context → ℝ) (history : List (Context × ℝ))
    (root : Context) (branch : Bool)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (hhistory : ∀ observation ∈ history, observation.2 ∈ Set.Icc (-1 : ℝ) 1) :
    BddAbove (Set.range (rootBranchValue evaluation history root branch :
      SequentialTree Context remaining → ℝ)) := by
  refine ⟨history.length + 2 + 2 * remaining, ?_⟩
  rintro _ ⟨tree, rfl⟩
  unfold rootBranchValue
  apply pmfExp_le_of_forall_le
  intro signs
  exact rootBranchEnvelope_le_historyLength_add_two_add_two_mul evaluation history root branch
    tree signs hevaluation hhistory

/-- After observing the positive endpoint, every continuation envelope is at
most the three-to-one convex combination of the two Rademacher root branches.
This is the elementary convexity calculation underlying the minimax step. -/
theorem sequentialCorrelationEnvelope_append_one_le_threeQuarter_true_add_quarter_false
    {Context Hypothesis : Type*} [Nonempty Hypothesis] {remaining : ℕ}
    (evaluation : Hypothesis → Context → ℝ) (history : List (Context × ℝ))
    (root : Context) (tree : SequentialTree Context remaining)
    (signs : Fin remaining → Bool)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (hhistory : ∀ observation ∈ history, observation.2 ∈ Set.Icc (-1 : ℝ) 1) :
    sequentialCorrelationEnvelope evaluation (history ++ [(root, 1)]) 2 tree signs ≤
      (3 / 4 : ℝ) * rootBranchEnvelope evaluation history root true tree signs +
        (1 / 4 : ℝ) * rootBranchEnvelope evaluation history root false tree signs := by
  have htrueBdd := rootBranchEnvelope_candidates_bddAbove evaluation history root true
    tree signs hevaluation hhistory
  have hfalseBdd := rootBranchEnvelope_candidates_bddAbove evaluation history root false
    tree signs hevaluation hhistory
  unfold sequentialCorrelationEnvelope
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨hypothesis, rfl⟩
  have htrue := le_csSup htrueBdd ⟨hypothesis, rfl⟩
  have hfalse := le_csSup hfalseBdd ⟨hypothesis, rfl⟩
  have hhistoryOne :
      sequentialHistoryCorrelation evaluation hypothesis (history ++ [(root, 1)]) =
        sequentialHistoryCorrelation evaluation hypothesis history + evaluation hypothesis root := by
    simp [sequentialHistoryCorrelation]
  change sequentialHistoryCorrelation evaluation hypothesis (history ++ [(root, 1)]) +
      2 * sequentialFutureCorrelation evaluation hypothesis tree signs ≤ _
  rw [hhistoryOne]
  unfold rootBranchEnvelope
  norm_num [rademacherSign] at htrue hfalse ⊢
  nlinarith

/-- Taking the Rademacher expectation preserves the positive-endpoint
convexity bound. -/
theorem doubledContinuation_append_one_le_threeQuarter_true_add_quarter_false
    {Context Hypothesis : Type*} [Nonempty Hypothesis] {remaining : ℕ}
    (evaluation : Hypothesis → Context → ℝ) (history : List (Context × ℝ))
    (root : Context) (tree : SequentialTree Context remaining)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (hhistory : ∀ observation ∈ history, observation.2 ∈ Set.Icc (-1 : ℝ) 1) :
    pmfExp (pmfProduct (Fin remaining) Bool (uniformPMF Bool))
        (sequentialCorrelationEnvelope evaluation (history ++ [(root, 1)]) 2 tree) ≤
      (3 / 4 : ℝ) * rootBranchValue evaluation history root true tree +
        (1 / 4 : ℝ) * rootBranchValue evaluation history root false tree := by
  calc
    pmfExp (pmfProduct (Fin remaining) Bool (uniformPMF Bool))
        (sequentialCorrelationEnvelope evaluation (history ++ [(root, 1)]) 2 tree) ≤
      pmfExp (pmfProduct (Fin remaining) Bool (uniformPMF Bool))
        (fun signs =>
          (3 / 4 : ℝ) * rootBranchEnvelope evaluation history root true tree signs +
            (1 / 4 : ℝ) * rootBranchEnvelope evaluation history root false tree signs) :=
        pmfExp_le_pmfExp_of_forall_le _ _ _ (fun signs =>
          sequentialCorrelationEnvelope_append_one_le_threeQuarter_true_add_quarter_false
            evaluation history root tree signs hevaluation hhistory)
    _ = (3 / 4 : ℝ) * rootBranchValue evaluation history root true tree +
          (1 / 4 : ℝ) * rootBranchValue evaluation history root false tree := by
        rw [pmfExp_add, pmfExp_const_mul, pmfExp_const_mul]
        rfl

/-- The doubled-future potential after the positive endpoint obeys the same
convexity bound. -/
theorem boundedSequentialMinimaxPotential_append_one_le_threeQuarter_true_add_quarter_false
    {Context Hypothesis : Type*} [Nonempty Context] [Nonempty Hypothesis]
    {remaining : ℕ} (evaluation : Hypothesis → Context → ℝ)
    (history : List (Context × ℝ)) (root : Context)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (hhistory : ∀ observation ∈ history, observation.2 ∈ Set.Icc (-1 : ℝ) 1) :
    boundedSequentialMinimaxPotential evaluation (history ++ [(root, 1)]) remaining ≤
      (3 / 4 : ℝ) * rootBranchPotential evaluation history root true remaining +
        (1 / 4 : ℝ) * rootBranchPotential evaluation history root false remaining := by
  have htrueBdd :=
    rootBranchValue_bddAbove (remaining := remaining) evaluation history root true hevaluation hhistory
  have hfalseBdd :=
    rootBranchValue_bddAbove (remaining := remaining) evaluation history root false hevaluation hhistory
  unfold boundedSequentialMinimaxPotential
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨tree, rfl⟩
  have htree := doubledContinuation_append_one_le_threeQuarter_true_add_quarter_false
    evaluation history root tree hevaluation hhistory
  unfold rootBranchPotential
  have htrue := le_csSup htrueBdd ⟨tree, rfl⟩
  have hfalse := le_csSup hfalseBdd ⟨tree, rfl⟩
  linarith

/-- The corresponding convexity estimate at the negative endpoint. -/
theorem sequentialCorrelationEnvelope_append_negOne_le_quarter_true_add_threeQuarter_false
    {Context Hypothesis : Type*} [Nonempty Hypothesis] {remaining : ℕ}
    (evaluation : Hypothesis → Context → ℝ) (history : List (Context × ℝ))
    (root : Context) (tree : SequentialTree Context remaining)
    (signs : Fin remaining → Bool)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (hhistory : ∀ observation ∈ history, observation.2 ∈ Set.Icc (-1 : ℝ) 1) :
    sequentialCorrelationEnvelope evaluation (history ++ [(root, -1)]) 2 tree signs ≤
      (1 / 4 : ℝ) * rootBranchEnvelope evaluation history root true tree signs +
        (3 / 4 : ℝ) * rootBranchEnvelope evaluation history root false tree signs := by
  have htrueBdd := rootBranchEnvelope_candidates_bddAbove evaluation history root true
    tree signs hevaluation hhistory
  have hfalseBdd := rootBranchEnvelope_candidates_bddAbove evaluation history root false
    tree signs hevaluation hhistory
  unfold sequentialCorrelationEnvelope
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨hypothesis, rfl⟩
  have htrue := le_csSup htrueBdd ⟨hypothesis, rfl⟩
  have hfalse := le_csSup hfalseBdd ⟨hypothesis, rfl⟩
  have hhistoryNegOne :
      sequentialHistoryCorrelation evaluation hypothesis (history ++ [(root, -1)]) =
        sequentialHistoryCorrelation evaluation hypothesis history - evaluation hypothesis root := by
    simp [sequentialHistoryCorrelation]
    ring
  change sequentialHistoryCorrelation evaluation hypothesis (history ++ [(root, -1)]) +
      2 * sequentialFutureCorrelation evaluation hypothesis tree signs ≤ _
  rw [hhistoryNegOne]
  unfold rootBranchEnvelope
  norm_num [rademacherSign] at htrue hfalse ⊢
  nlinarith

/-- Taking the Rademacher expectation preserves the negative-endpoint
convexity bound. -/
theorem doubledContinuation_append_negOne_le_quarter_true_add_threeQuarter_false
    {Context Hypothesis : Type*} [Nonempty Hypothesis] {remaining : ℕ}
    (evaluation : Hypothesis → Context → ℝ) (history : List (Context × ℝ))
    (root : Context) (tree : SequentialTree Context remaining)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (hhistory : ∀ observation ∈ history, observation.2 ∈ Set.Icc (-1 : ℝ) 1) :
    pmfExp (pmfProduct (Fin remaining) Bool (uniformPMF Bool))
        (sequentialCorrelationEnvelope evaluation (history ++ [(root, -1)]) 2 tree) ≤
      (1 / 4 : ℝ) * rootBranchValue evaluation history root true tree +
        (3 / 4 : ℝ) * rootBranchValue evaluation history root false tree := by
  calc
    pmfExp (pmfProduct (Fin remaining) Bool (uniformPMF Bool))
        (sequentialCorrelationEnvelope evaluation (history ++ [(root, -1)]) 2 tree) ≤
      pmfExp (pmfProduct (Fin remaining) Bool (uniformPMF Bool))
        (fun signs =>
          (1 / 4 : ℝ) * rootBranchEnvelope evaluation history root true tree signs +
            (3 / 4 : ℝ) * rootBranchEnvelope evaluation history root false tree signs) :=
        pmfExp_le_pmfExp_of_forall_le _ _ _ (fun signs =>
          sequentialCorrelationEnvelope_append_negOne_le_quarter_true_add_threeQuarter_false
            evaluation history root tree signs hevaluation hhistory)
    _ = (1 / 4 : ℝ) * rootBranchValue evaluation history root true tree +
          (3 / 4 : ℝ) * rootBranchValue evaluation history root false tree := by
        rw [pmfExp_add, pmfExp_const_mul, pmfExp_const_mul]
        rfl

/-- The doubled-future potential after the negative endpoint obeys the same
convexity bound. -/
theorem boundedSequentialMinimaxPotential_append_negOne_le_quarter_true_add_threeQuarter_false
    {Context Hypothesis : Type*} [Nonempty Context] [Nonempty Hypothesis]
    {remaining : ℕ} (evaluation : Hypothesis → Context → ℝ)
    (history : List (Context × ℝ)) (root : Context)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (hhistory : ∀ observation ∈ history, observation.2 ∈ Set.Icc (-1 : ℝ) 1) :
    boundedSequentialMinimaxPotential evaluation (history ++ [(root, -1)]) remaining ≤
      (1 / 4 : ℝ) * rootBranchPotential evaluation history root true remaining +
        (3 / 4 : ℝ) * rootBranchPotential evaluation history root false remaining := by
  have htrueBdd :=
    rootBranchValue_bddAbove (remaining := remaining) evaluation history root true hevaluation hhistory
  have hfalseBdd :=
    rootBranchValue_bddAbove (remaining := remaining) evaluation history root false hevaluation hhistory
  unfold boundedSequentialMinimaxPotential
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨tree, rfl⟩
  have htree := doubledContinuation_append_negOne_le_quarter_true_add_threeQuarter_false
    evaluation history root tree hevaluation hhistory
  unfold rootBranchPotential
  have htrue := le_csSup htrueBdd ⟨tree, rfl⟩
  have hfalse := le_csSup hfalseBdd ⟨tree, rfl⟩
  linarith

/-- Every feasible label is a convex mixture of the two endpoint branches;
the coefficients have been chosen so that the doubled Rademacher perturbation
has exactly the observed label's coefficient. -/
theorem sequentialCorrelationEnvelope_append_label_le_branch_mixture
    {Context Hypothesis : Type*} [Nonempty Hypothesis] {remaining : ℕ}
    (evaluation : Hypothesis → Context → ℝ) (history : List (Context × ℝ))
    (root : Context) (label : ℝ) (tree : SequentialTree Context remaining)
    (signs : Fin remaining → Bool)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (hhistory : ∀ observation ∈ history, observation.2 ∈ Set.Icc (-1 : ℝ) 1)
    (hlabel : label ∈ Set.Icc (-1 : ℝ) 1) :
    sequentialCorrelationEnvelope evaluation (history ++ [(root, label)]) 2 tree signs ≤
      ((2 + label) / 4 : ℝ) * rootBranchEnvelope evaluation history root true tree signs +
        ((2 - label) / 4 : ℝ) * rootBranchEnvelope evaluation history root false tree signs := by
  have htrueBdd := rootBranchEnvelope_candidates_bddAbove evaluation history root true
    tree signs hevaluation hhistory
  have hfalseBdd := rootBranchEnvelope_candidates_bddAbove evaluation history root false
    tree signs hevaluation hhistory
  have htrueWeight : 0 ≤ (2 + label) / 4 := by nlinarith [hlabel.1]
  have hfalseWeight : 0 ≤ (2 - label) / 4 := by nlinarith [hlabel.2]
  unfold sequentialCorrelationEnvelope
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨hypothesis, rfl⟩
  have htrue := le_csSup htrueBdd ⟨hypothesis, rfl⟩
  have hfalse := le_csSup hfalseBdd ⟨hypothesis, rfl⟩
  have hhistoryLabel :
      sequentialHistoryCorrelation evaluation hypothesis (history ++ [(root, label)]) =
        sequentialHistoryCorrelation evaluation hypothesis history +
          evaluation hypothesis root * label := by
    simp [sequentialHistoryCorrelation]
  change sequentialHistoryCorrelation evaluation hypothesis (history ++ [(root, label)]) +
      2 * sequentialFutureCorrelation evaluation hypothesis tree signs ≤ _
  rw [hhistoryLabel]
  unfold rootBranchEnvelope
  norm_num [rademacherSign] at htrue hfalse ⊢
  nlinarith

/-- The label-mixture bound is stable under the Rademacher expectation. -/
theorem doubledContinuation_append_label_le_branch_mixture
    {Context Hypothesis : Type*} [Nonempty Hypothesis] {remaining : ℕ}
    (evaluation : Hypothesis → Context → ℝ) (history : List (Context × ℝ))
    (root : Context) (label : ℝ) (tree : SequentialTree Context remaining)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (hhistory : ∀ observation ∈ history, observation.2 ∈ Set.Icc (-1 : ℝ) 1)
    (hlabel : label ∈ Set.Icc (-1 : ℝ) 1) :
    pmfExp (pmfProduct (Fin remaining) Bool (uniformPMF Bool))
        (sequentialCorrelationEnvelope evaluation (history ++ [(root, label)]) 2 tree) ≤
      ((2 + label) / 4 : ℝ) * rootBranchValue evaluation history root true tree +
        ((2 - label) / 4 : ℝ) * rootBranchValue evaluation history root false tree := by
  calc
    pmfExp (pmfProduct (Fin remaining) Bool (uniformPMF Bool))
        (sequentialCorrelationEnvelope evaluation (history ++ [(root, label)]) 2 tree) ≤
      pmfExp (pmfProduct (Fin remaining) Bool (uniformPMF Bool))
        (fun signs =>
          ((2 + label) / 4 : ℝ) * rootBranchEnvelope evaluation history root true tree signs +
            ((2 - label) / 4 : ℝ) * rootBranchEnvelope evaluation history root false tree signs) :=
        pmfExp_le_pmfExp_of_forall_le _ _ _ (fun signs =>
          sequentialCorrelationEnvelope_append_label_le_branch_mixture
            evaluation history root label tree signs hevaluation hhistory hlabel)
    _ = ((2 + label) / 4 : ℝ) * rootBranchValue evaluation history root true tree +
          ((2 - label) / 4 : ℝ) * rootBranchValue evaluation history root false tree := by
        rw [pmfExp_add, pmfExp_const_mul, pmfExp_const_mul]
        rfl

/-- The doubled-future minimax potential is convex along a feasible next
label, with the explicit two-branch coefficients. -/
theorem boundedSequentialMinimaxPotential_append_label_le_branch_mixture
    {Context Hypothesis : Type*} [Nonempty Context] [Nonempty Hypothesis]
    {remaining : ℕ} (evaluation : Hypothesis → Context → ℝ)
    (history : List (Context × ℝ)) (root : Context) (label : ℝ)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (hhistory : ∀ observation ∈ history, observation.2 ∈ Set.Icc (-1 : ℝ) 1)
    (hlabel : label ∈ Set.Icc (-1 : ℝ) 1) :
    boundedSequentialMinimaxPotential evaluation (history ++ [(root, label)]) remaining ≤
      ((2 + label) / 4 : ℝ) * rootBranchPotential evaluation history root true remaining +
        ((2 - label) / 4 : ℝ) * rootBranchPotential evaluation history root false remaining := by
  have htrueBdd :=
    rootBranchValue_bddAbove (remaining := remaining) evaluation history root true hevaluation hhistory
  have hfalseBdd :=
    rootBranchValue_bddAbove (remaining := remaining) evaluation history root false hevaluation hhistory
  unfold boundedSequentialMinimaxPotential
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨tree, rfl⟩
  have htree := doubledContinuation_append_label_le_branch_mixture
    (remaining := remaining) evaluation history root label tree hevaluation hhistory hlabel
  unfold rootBranchPotential
  have htrue := le_csSup htrueBdd ⟨tree, rfl⟩
  have hfalse := le_csSup hfalseBdd ⟨tree, rfl⟩
  nlinarith [show 0 ≤ (2 + label) / 4 by nlinarith [hlabel.1],
    show 0 ≤ (2 - label) / 4 by nlinarith [hlabel.2]]

/-- The sum of the two optimal root-branch values is bounded by twice the
doubled-future minimax potential with one extra round. -/
theorem rootBranchPotential_sum_le_two_minimaxPotential
    {Context Hypothesis : Type*} [Nonempty Context] [Nonempty Hypothesis]
    {remaining : ℕ} (evaluation : Hypothesis → Context → ℝ)
    (history : List (Context × ℝ)) (root : Context)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (hhistory : ∀ observation ∈ history, observation.2 ∈ Set.Icc (-1 : ℝ) 1) :
    rootBranchPotential evaluation history root true remaining +
      rootBranchPotential evaluation history root false remaining ≤
        2 * boundedSequentialMinimaxPotential evaluation history (remaining + 1) := by
  have htrueBdd :=
    rootBranchValue_bddAbove (remaining := remaining) evaluation history root true hevaluation hhistory
  have hfalseBdd :=
    rootBranchValue_bddAbove (remaining := remaining) evaluation history root false hevaluation hhistory
  have hcurrentBdd := boundedSequentialMinimaxPotential_continuations_bddAbove
    evaluation history (remaining + 1) hevaluation hhistory
  unfold rootBranchPotential
  rw [← csSup_add (Set.range_nonempty _) htrueBdd (Set.range_nonempty _) hfalseBdd]
  apply csSup_le
  · exact (Set.range_nonempty _).add (Set.range_nonempty _)
  · rintro value ⟨_, htrue, _, hfalse, rfl⟩
    rcases htrue with ⟨trueTree, rfl⟩
    rcases hfalse with ⟨falseTree, rfl⟩
    let continuations : Bool → SequentialTree Context remaining := fun branch =>
      if branch then trueTree else falseTree
    have hcurrent := le_csSup hcurrentBdd
      ⟨SequentialTree.splice root continuations, rfl⟩
    have hsplice := doubledContinuation_splice_eq_average_branchValues evaluation history root
      continuations
    change pmfExp (pmfProduct (Fin (remaining + 1)) Bool (uniformPMF Bool))
        (sequentialCorrelationEnvelope evaluation history 2 (SequentialTree.splice root continuations)) ≤ _ at hcurrent
    rw [hsplice] at hcurrent
    simp [continuations] at hcurrent
    unfold boundedSequentialMinimaxPotential
    nlinarith

/-- Averaging the two endpoint potentials cannot increase the doubled-future
potential before the round.  This is the branch inequality used by the
sequential minimax strategy. -/
theorem boundedSequentialMinimaxPotential_endpoints_average_le
    {Context Hypothesis : Type*} [Nonempty Context] [Nonempty Hypothesis]
    {remaining : ℕ} (evaluation : Hypothesis → Context → ℝ)
    (history : List (Context × ℝ)) (root : Context)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (hhistory : ∀ observation ∈ history, observation.2 ∈ Set.Icc (-1 : ℝ) 1) :
    boundedSequentialMinimaxPotential evaluation (history ++ [(root, 1)]) remaining +
      boundedSequentialMinimaxPotential evaluation (history ++ [(root, -1)]) remaining ≤
        2 * boundedSequentialMinimaxPotential evaluation history (remaining + 1) := by
  have hplus :=
    boundedSequentialMinimaxPotential_append_one_le_threeQuarter_true_add_quarter_false
      (remaining := remaining) evaluation history root hevaluation hhistory
  have hminus :=
    boundedSequentialMinimaxPotential_append_negOne_le_quarter_true_add_threeQuarter_false
      (remaining := remaining) evaluation history root hevaluation hhistory
  have hbranches := rootBranchPotential_sum_le_two_minimaxPotential
    (remaining := remaining) evaluation history root hevaluation hhistory
  linarith

/-- The comparator scores inside one doubled-future envelope are bounded
above under unit-bounded values and history labels. -/
theorem sequentialCorrelationEnvelope_candidates_bddAbove {Context Hypothesis : Type*}
    [Nonempty Hypothesis] {remaining : ℕ}
    (evaluation : Hypothesis → Context → ℝ) (history : List (Context × ℝ))
    (tree : SequentialTree Context remaining) (signs : Fin remaining → Bool)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (hhistory : ∀ observation ∈ history, observation.2 ∈ Set.Icc (-1 : ℝ) 1) :
    BddAbove (Set.range fun hypothesis =>
      sequentialHistoryCorrelation evaluation hypothesis history +
        2 * sequentialFutureCorrelation evaluation hypothesis tree signs) := by
  refine ⟨history.length + 2 * remaining, ?_⟩
  rintro _ ⟨hypothesis, rfl⟩
  have hpast := sequentialHistoryCorrelation_le_length evaluation hypothesis history
    hevaluation hhistory
  have hfuture := sequentialFutureCorrelation_le_horizon evaluation hypothesis tree signs
    hevaluation
  norm_num
  nlinarith

/-- With the future tree fixed, the doubled-future envelope is convex in a
feasible newly observed label. -/
theorem sequentialCorrelationEnvelope_append_label_le_endpoint_mixture
    {Context Hypothesis : Type*} [Nonempty Hypothesis] {remaining : ℕ}
    (evaluation : Hypothesis → Context → ℝ) (history : List (Context × ℝ))
    (root : Context) (label : ℝ) (tree : SequentialTree Context remaining)
    (signs : Fin remaining → Bool)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (hhistory : ∀ observation ∈ history, observation.2 ∈ Set.Icc (-1 : ℝ) 1)
    (hlabel : label ∈ Set.Icc (-1 : ℝ) 1) :
    sequentialCorrelationEnvelope evaluation (history ++ [(root, label)]) 2 tree signs ≤
      ((1 + label) / 2 : ℝ) *
          sequentialCorrelationEnvelope evaluation (history ++ [(root, 1)]) 2 tree signs +
        ((1 - label) / 2 : ℝ) *
          sequentialCorrelationEnvelope evaluation (history ++ [(root, -1)]) 2 tree signs := by
  have hplusHistory : ∀ observation ∈ history ++ [(root, 1)],
      observation.2 ∈ Set.Icc (-1 : ℝ) 1 := by
    intro observation hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hhistory observation hmem
    · simp only [List.mem_singleton] at hmem
      subst observation
      norm_num
  have hminusHistory : ∀ observation ∈ history ++ [(root, -1)],
      observation.2 ∈ Set.Icc (-1 : ℝ) 1 := by
    intro observation hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hhistory observation hmem
    · simp only [List.mem_singleton] at hmem
      subst observation
      norm_num
  have hplusBdd := sequentialCorrelationEnvelope_candidates_bddAbove evaluation
    (history ++ [(root, 1)]) tree signs hevaluation hplusHistory
  have hminusBdd := sequentialCorrelationEnvelope_candidates_bddAbove evaluation
    (history ++ [(root, -1)]) tree signs hevaluation hminusHistory
  have hplusWeight : 0 ≤ (1 + label) / 2 := by nlinarith [hlabel.1]
  have hminusWeight : 0 ≤ (1 - label) / 2 := by nlinarith [hlabel.2]
  unfold sequentialCorrelationEnvelope
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨hypothesis, rfl⟩
  have hplus := le_csSup hplusBdd ⟨hypothesis, rfl⟩
  have hminus := le_csSup hminusBdd ⟨hypothesis, rfl⟩
  have hhistoryLabel :
      sequentialHistoryCorrelation evaluation hypothesis (history ++ [(root, label)]) =
        sequentialHistoryCorrelation evaluation hypothesis history +
          evaluation hypothesis root * label := by
    simp [sequentialHistoryCorrelation]
  have hhistoryPlus :
      sequentialHistoryCorrelation evaluation hypothesis (history ++ [(root, 1)]) =
        sequentialHistoryCorrelation evaluation hypothesis history + evaluation hypothesis root := by
    simp [sequentialHistoryCorrelation]
  have hhistoryMinus :
      sequentialHistoryCorrelation evaluation hypothesis (history ++ [(root, -1)]) =
        sequentialHistoryCorrelation evaluation hypothesis history - evaluation hypothesis root := by
    simp [sequentialHistoryCorrelation]
    ring
  change sequentialHistoryCorrelation evaluation hypothesis (history ++ [(root, label)]) +
      2 * sequentialFutureCorrelation evaluation hypothesis tree signs ≤ _
  change sequentialHistoryCorrelation evaluation hypothesis (history ++ [(root, 1)]) +
      2 * sequentialFutureCorrelation evaluation hypothesis tree signs ≤ _ at hplus
  change sequentialHistoryCorrelation evaluation hypothesis (history ++ [(root, -1)]) +
      2 * sequentialFutureCorrelation evaluation hypothesis tree signs ≤ _ at hminus
  rw [hhistoryPlus] at hplus
  rw [hhistoryMinus] at hminus
  rw [hhistoryLabel]
  nlinarith

/-- Rademacher expectation preserves the feasible-label convexity bound. -/
theorem doubledContinuation_append_label_le_endpoint_mixture
    {Context Hypothesis : Type*} [Nonempty Hypothesis] {remaining : ℕ}
    (evaluation : Hypothesis → Context → ℝ) (history : List (Context × ℝ))
    (root : Context) (label : ℝ) (tree : SequentialTree Context remaining)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (hhistory : ∀ observation ∈ history, observation.2 ∈ Set.Icc (-1 : ℝ) 1)
    (hlabel : label ∈ Set.Icc (-1 : ℝ) 1) :
    pmfExp (pmfProduct (Fin remaining) Bool (uniformPMF Bool))
        (sequentialCorrelationEnvelope evaluation (history ++ [(root, label)]) 2 tree) ≤
      ((1 + label) / 2 : ℝ) *
          pmfExp (pmfProduct (Fin remaining) Bool (uniformPMF Bool))
            (sequentialCorrelationEnvelope evaluation (history ++ [(root, 1)]) 2 tree) +
        ((1 - label) / 2 : ℝ) *
          pmfExp (pmfProduct (Fin remaining) Bool (uniformPMF Bool))
            (sequentialCorrelationEnvelope evaluation (history ++ [(root, -1)]) 2 tree) := by
  calc
    pmfExp (pmfProduct (Fin remaining) Bool (uniformPMF Bool))
        (sequentialCorrelationEnvelope evaluation (history ++ [(root, label)]) 2 tree) ≤
      pmfExp (pmfProduct (Fin remaining) Bool (uniformPMF Bool))
        (fun signs =>
          ((1 + label) / 2 : ℝ) *
              sequentialCorrelationEnvelope evaluation (history ++ [(root, 1)]) 2 tree signs +
            ((1 - label) / 2 : ℝ) *
              sequentialCorrelationEnvelope evaluation (history ++ [(root, -1)]) 2 tree signs) :=
        pmfExp_le_pmfExp_of_forall_le _ _ _ (fun signs =>
          sequentialCorrelationEnvelope_append_label_le_endpoint_mixture
            evaluation history root label tree signs hevaluation hhistory hlabel)
    _ = ((1 + label) / 2 : ℝ) *
          pmfExp (pmfProduct (Fin remaining) Bool (uniformPMF Bool))
            (sequentialCorrelationEnvelope evaluation (history ++ [(root, 1)]) 2 tree) +
        ((1 - label) / 2 : ℝ) *
          pmfExp (pmfProduct (Fin remaining) Bool (uniformPMF Bool))
            (sequentialCorrelationEnvelope evaluation (history ++ [(root, -1)]) 2 tree) := by
        rw [pmfExp_add, pmfExp_const_mul, pmfExp_const_mul]

/-- The doubled-future minimax potential is convex in a feasible newly
observed label. -/
theorem boundedSequentialMinimaxPotential_append_label_le_endpoint_mixture
    {Context Hypothesis : Type*} [Nonempty Context] [Nonempty Hypothesis]
    {remaining : ℕ} (evaluation : Hypothesis → Context → ℝ)
    (history : List (Context × ℝ)) (root : Context) (label : ℝ)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (hhistory : ∀ observation ∈ history, observation.2 ∈ Set.Icc (-1 : ℝ) 1)
    (hlabel : label ∈ Set.Icc (-1 : ℝ) 1) :
    boundedSequentialMinimaxPotential evaluation (history ++ [(root, label)]) remaining ≤
      ((1 + label) / 2 : ℝ) *
          boundedSequentialMinimaxPotential evaluation (history ++ [(root, 1)]) remaining +
        ((1 - label) / 2 : ℝ) *
          boundedSequentialMinimaxPotential evaluation (history ++ [(root, -1)]) remaining := by
  have hplusHistory : ∀ observation ∈ history ++ [(root, 1)],
      observation.2 ∈ Set.Icc (-1 : ℝ) 1 := by
    intro observation hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hhistory observation hmem
    · simp only [List.mem_singleton] at hmem
      subst observation
      norm_num
  have hminusHistory : ∀ observation ∈ history ++ [(root, -1)],
      observation.2 ∈ Set.Icc (-1 : ℝ) 1 := by
    intro observation hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hhistory observation hmem
    · simp only [List.mem_singleton] at hmem
      subst observation
      norm_num
  have hplusBdd := boundedSequentialMinimaxPotential_continuations_bddAbove evaluation
    (history ++ [(root, 1)]) remaining hevaluation hplusHistory
  have hminusBdd := boundedSequentialMinimaxPotential_continuations_bddAbove evaluation
    (history ++ [(root, -1)]) remaining hevaluation hminusHistory
  unfold boundedSequentialMinimaxPotential
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨tree, rfl⟩
  have htree := doubledContinuation_append_label_le_endpoint_mixture
    (remaining := remaining) evaluation history root label tree hevaluation hhistory hlabel
  have hplus := le_csSup hplusBdd ⟨tree, rfl⟩
  have hminus := le_csSup hminusBdd ⟨tree, rfl⟩
  nlinarith [show 0 ≤ (1 + label) / 2 by nlinarith [hlabel.1],
    show 0 ≤ (1 - label) / 2 by nlinarith [hlabel.2]]

/-- The explicit minimax one-step choice pays for every feasible observed
label through a decrease of the doubled-future potential. -/
theorem boundedSequentialMinimaxPotential_step_le
    {Context Hypothesis : Type*} [Nonempty Context] [Nonempty Hypothesis]
    {remaining : ℕ} (evaluation : Hypothesis → Context → ℝ)
    (history : List (Context × ℝ)) (root : Context) (label : ℝ)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (hhistory : ∀ observation ∈ history, observation.2 ∈ Set.Icc (-1 : ℝ) 1)
    (hlabel : label ∈ Set.Icc (-1 : ℝ) 1) :
    boundedSequentialMinimaxPotential evaluation (history ++ [(root, label)]) remaining -
        ((boundedSequentialMinimaxPotential evaluation (history ++ [(root, 1)]) remaining -
          boundedSequentialMinimaxPotential evaluation (history ++ [(root, -1)]) remaining) / 2) * label ≤
      boundedSequentialMinimaxPotential evaluation history (remaining + 1) := by
  have hmixture := boundedSequentialMinimaxPotential_append_label_le_endpoint_mixture
    (remaining := remaining) evaluation history root label hevaluation hhistory hlabel
  have havg := boundedSequentialMinimaxPotential_endpoints_average_le
    (remaining := remaining) evaluation history root hevaluation hhistory
  linarith

/-- Increasing the newest realized label from `-1` to `1` changes a doubled
future envelope by at most two. -/
theorem sequentialCorrelationEnvelope_append_one_le_append_negOne_add_two
    {Context Hypothesis : Type*} [Nonempty Hypothesis] {remaining : ℕ}
    (evaluation : Hypothesis → Context → ℝ) (history : List (Context × ℝ))
    (context : Context) (tree : SequentialTree Context remaining)
    (signs : Fin remaining → Bool)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (hminusHistory : ∀ observation ∈ history ++ [(context, -1)],
      observation.2 ∈ Set.Icc (-1 : ℝ) 1) :
    sequentialCorrelationEnvelope evaluation (history ++ [(context, 1)]) 2 tree signs ≤
      sequentialCorrelationEnvelope evaluation (history ++ [(context, -1)]) 2 tree signs + 2 := by
  have hminusBdd := sequentialCorrelationEnvelope_candidates_bddAbove evaluation
    (history ++ [(context, -1)]) tree signs hevaluation hminusHistory
  unfold sequentialCorrelationEnvelope
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨hypothesis, rfl⟩
  have hminus := le_csSup hminusBdd ⟨hypothesis, rfl⟩
  have hevaluation' := (hevaluation hypothesis context).2
  have hhistory :
      sequentialHistoryCorrelation evaluation hypothesis (history ++ [(context, 1)]) =
        sequentialHistoryCorrelation evaluation hypothesis (history ++ [(context, -1)]) +
          2 * evaluation hypothesis context := by
    simp [sequentialHistoryCorrelation]
    ring
  change sequentialHistoryCorrelation evaluation hypothesis (history ++ [(context, 1)]) +
      2 * sequentialFutureCorrelation evaluation hypothesis tree signs ≤ _
  rw [hhistory]
  nlinarith

/-- Increasing the newest label from `-1` to `1` changes the corresponding
doubled-future continuation expectation by at most two. -/
theorem doubledContinuation_append_one_le_append_negOne_add_two
    {Context Hypothesis : Type*} [Nonempty Hypothesis] {remaining : ℕ}
    (evaluation : Hypothesis → Context → ℝ) (history : List (Context × ℝ))
    (context : Context) (tree : SequentialTree Context remaining)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (hminusHistory : ∀ observation ∈ history ++ [(context, -1)],
      observation.2 ∈ Set.Icc (-1 : ℝ) 1) :
    pmfExp (pmfProduct (Fin remaining) Bool (uniformPMF Bool))
        (sequentialCorrelationEnvelope evaluation (history ++ [(context, 1)]) 2 tree) ≤
      pmfExp (pmfProduct (Fin remaining) Bool (uniformPMF Bool))
        (sequentialCorrelationEnvelope evaluation (history ++ [(context, -1)]) 2 tree) + 2 := by
  calc
    pmfExp (pmfProduct (Fin remaining) Bool (uniformPMF Bool))
        (sequentialCorrelationEnvelope evaluation (history ++ [(context, 1)]) 2 tree) ≤
      pmfExp (pmfProduct (Fin remaining) Bool (uniformPMF Bool))
        (fun signs =>
          sequentialCorrelationEnvelope evaluation (history ++ [(context, -1)]) 2 tree signs + 2) :=
        pmfExp_le_pmfExp_of_forall_le _ _ _ (fun signs =>
          sequentialCorrelationEnvelope_append_one_le_append_negOne_add_two evaluation history
            context tree signs hevaluation hminusHistory)
    _ = pmfExp (pmfProduct (Fin remaining) Bool (uniformPMF Bool))
          (sequentialCorrelationEnvelope evaluation (history ++ [(context, -1)]) 2 tree) + 2 := by
        rw [pmfExp_add, pmfExp_const]

/-- The two minimax continuation potentials differ by at most two in the
direction that increases the newest label. -/
theorem boundedSequentialMinimaxPotential_append_one_le_append_negOne_add_two
    {Context Hypothesis : Type*} [Nonempty Context] [Nonempty Hypothesis]
    (evaluation : Hypothesis → Context → ℝ) (history : List (Context × ℝ))
    (context : Context) (remaining : ℕ)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (hhistory : ∀ observation ∈ history, observation.2 ∈ Set.Icc (-1 : ℝ) 1) :
    boundedSequentialMinimaxPotential evaluation (history ++ [(context, 1)]) remaining ≤
      boundedSequentialMinimaxPotential evaluation (history ++ [(context, -1)]) remaining + 2 := by
  have hminusHistory : ∀ observation ∈ history ++ [(context, -1)],
      observation.2 ∈ Set.Icc (-1 : ℝ) 1 := by
    intro observation hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hhistory observation hmem
    · simp only [List.mem_singleton] at hmem
      subst observation
      norm_num
  have hminusBdd := boundedSequentialMinimaxPotential_continuations_bddAbove
    evaluation (history ++ [(context, -1)]) remaining hevaluation hminusHistory
  unfold boundedSequentialMinimaxPotential
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨tree, rfl⟩
  have htree := doubledContinuation_append_one_le_append_negOne_add_two evaluation history
    context tree hevaluation hminusHistory
  have hle := le_csSup hminusBdd ⟨tree, rfl⟩
  linarith

/-- Decreasing the newest realized label from `1` to `-1` changes a doubled
future envelope by at most two. -/
theorem sequentialCorrelationEnvelope_append_negOne_le_append_one_add_two
    {Context Hypothesis : Type*} [Nonempty Hypothesis] {remaining : ℕ}
    (evaluation : Hypothesis → Context → ℝ) (history : List (Context × ℝ))
    (context : Context) (tree : SequentialTree Context remaining)
    (signs : Fin remaining → Bool)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (honeHistory : ∀ observation ∈ history ++ [(context, 1)],
      observation.2 ∈ Set.Icc (-1 : ℝ) 1) :
    sequentialCorrelationEnvelope evaluation (history ++ [(context, -1)]) 2 tree signs ≤
      sequentialCorrelationEnvelope evaluation (history ++ [(context, 1)]) 2 tree signs + 2 := by
  have honeBdd := sequentialCorrelationEnvelope_candidates_bddAbove evaluation
    (history ++ [(context, 1)]) tree signs hevaluation honeHistory
  unfold sequentialCorrelationEnvelope
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨hypothesis, rfl⟩
  have hone := le_csSup honeBdd ⟨hypothesis, rfl⟩
  have hevaluation' := (hevaluation hypothesis context).1
  have hhistory :
      sequentialHistoryCorrelation evaluation hypothesis (history ++ [(context, -1)]) =
        sequentialHistoryCorrelation evaluation hypothesis (history ++ [(context, 1)]) -
          2 * evaluation hypothesis context := by
    simp [sequentialHistoryCorrelation]
    ring
  change sequentialHistoryCorrelation evaluation hypothesis (history ++ [(context, -1)]) +
      2 * sequentialFutureCorrelation evaluation hypothesis tree signs ≤ _
  rw [hhistory]
  nlinarith

/-- Decreasing the newest label from `1` to `-1` changes the corresponding
doubled-future continuation expectation by at most two. -/
theorem doubledContinuation_append_negOne_le_append_one_add_two
    {Context Hypothesis : Type*} [Nonempty Hypothesis] {remaining : ℕ}
    (evaluation : Hypothesis → Context → ℝ) (history : List (Context × ℝ))
    (context : Context) (tree : SequentialTree Context remaining)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (honeHistory : ∀ observation ∈ history ++ [(context, 1)],
      observation.2 ∈ Set.Icc (-1 : ℝ) 1) :
    pmfExp (pmfProduct (Fin remaining) Bool (uniformPMF Bool))
        (sequentialCorrelationEnvelope evaluation (history ++ [(context, -1)]) 2 tree) ≤
      pmfExp (pmfProduct (Fin remaining) Bool (uniformPMF Bool))
        (sequentialCorrelationEnvelope evaluation (history ++ [(context, 1)]) 2 tree) + 2 := by
  calc
    pmfExp (pmfProduct (Fin remaining) Bool (uniformPMF Bool))
        (sequentialCorrelationEnvelope evaluation (history ++ [(context, -1)]) 2 tree) ≤
      pmfExp (pmfProduct (Fin remaining) Bool (uniformPMF Bool))
        (fun signs =>
          sequentialCorrelationEnvelope evaluation (history ++ [(context, 1)]) 2 tree signs + 2) :=
        pmfExp_le_pmfExp_of_forall_le _ _ _ (fun signs =>
          sequentialCorrelationEnvelope_append_negOne_le_append_one_add_two evaluation history
            context tree signs hevaluation honeHistory)
    _ = pmfExp (pmfProduct (Fin remaining) Bool (uniformPMF Bool))
          (sequentialCorrelationEnvelope evaluation (history ++ [(context, 1)]) 2 tree) + 2 := by
        rw [pmfExp_add, pmfExp_const]

/-- The two minimax continuation potentials differ by at most two in the
direction that decreases the newest label. -/
theorem boundedSequentialMinimaxPotential_append_negOne_le_append_one_add_two
    {Context Hypothesis : Type*} [Nonempty Context] [Nonempty Hypothesis]
    (evaluation : Hypothesis → Context → ℝ) (history : List (Context × ℝ))
    (context : Context) (remaining : ℕ)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (hhistory : ∀ observation ∈ history, observation.2 ∈ Set.Icc (-1 : ℝ) 1) :
    boundedSequentialMinimaxPotential evaluation (history ++ [(context, -1)]) remaining ≤
      boundedSequentialMinimaxPotential evaluation (history ++ [(context, 1)]) remaining + 2 := by
  have honeHistory : ∀ observation ∈ history ++ [(context, 1)],
      observation.2 ∈ Set.Icc (-1 : ℝ) 1 := by
    intro observation hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hhistory observation hmem
    · simp only [List.mem_singleton] at hmem
      subst observation
      norm_num
  have honeBdd := boundedSequentialMinimaxPotential_continuations_bddAbove
    evaluation (history ++ [(context, 1)]) remaining hevaluation honeHistory
  unfold boundedSequentialMinimaxPotential
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨tree, rfl⟩
  have htree := doubledContinuation_append_negOne_le_append_one_add_two evaluation history
    context tree hevaluation honeHistory
  have hle := le_csSup honeBdd ⟨tree, rfl⟩
  linarith

/-- At zero remaining rounds, the doubled-future potential dominates the
literal correlation of every named comparator with the revealed history. -/
theorem sequentialComparatorCorrelation_le_boundedSequentialMinimaxPotential_zero
    {Context Hypothesis : Type*} [Nonempty Context] [Nonempty Hypothesis]
    (evaluation : Hypothesis → Context → ℝ) (history : List (Context × ℝ))
    (hypothesis : Hypothesis)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (hhistory : ∀ observation ∈ history, observation.2 ∈ Set.Icc (-1 : ℝ) 1) :
    sequentialComparatorCorrelation (evaluation hypothesis) history ≤
      boundedSequentialMinimaxPotential evaluation history 0 := by
  let emptyTree : SequentialTree Context 0 := fun round => Fin.elim0 round
  let emptySigns : Fin 0 → Bool := fun round => Fin.elim0 round
  have henvelopeBdd := sequentialCorrelationEnvelope_candidates_bddAbove evaluation history
    emptyTree emptySigns hevaluation hhistory
  have henvelope := le_csSup henvelopeBdd ⟨hypothesis, rfl⟩
  have hfuture : sequentialFutureCorrelation evaluation hypothesis emptyTree emptySigns = 0 := by
    simp [sequentialFutureCorrelation]
  have henvelope' : sequentialHistoryCorrelation evaluation hypothesis history ≤
      sequentialCorrelationEnvelope evaluation history 2 emptyTree emptySigns := by
    unfold sequentialCorrelationEnvelope at henvelope ⊢
    simpa [hfuture] using henvelope
  have hpotentialBdd := boundedSequentialMinimaxPotential_continuations_bddAbove
    evaluation history 0 hevaluation hhistory
  have htree := le_csSup hpotentialBdd ⟨emptyTree, rfl⟩
  have hemptyExp :
      pmfExp (pmfProduct (Fin 0) Bool (uniformPMF Bool))
          (sequentialCorrelationEnvelope evaluation history 2 emptyTree) =
        sequentialCorrelationEnvelope evaluation history 2 emptyTree emptySigns := by
    calc
      pmfExp (pmfProduct (Fin 0) Bool (uniformPMF Bool))
          (sequentialCorrelationEnvelope evaluation history 2 emptyTree) =
        pmfExp (pmfProduct (Fin 0) Bool (uniformPMF Bool))
          (fun _ => sequentialCorrelationEnvelope evaluation history 2 emptyTree emptySigns) := by
            apply pmfExp_congr
            intro signs
            congr
            exact Subsingleton.elim _ _
      _ = sequentialCorrelationEnvelope evaluation history 2 emptyTree emptySigns := pmfExp_const _ _
  change sequentialHistoryCorrelation evaluation hypothesis history ≤ _
  calc
    sequentialHistoryCorrelation evaluation hypothesis history ≤
        sequentialCorrelationEnvelope evaluation history 2 emptyTree emptySigns := henvelope'
    _ = pmfExp (pmfProduct (Fin 0) Bool (uniformPMF Bool))
          (sequentialCorrelationEnvelope evaluation history 2 emptyTree) := hemptyExp.symm
    _ ≤ boundedSequentialMinimaxPotential evaluation history 0 := by
      simpa [boundedSequentialMinimaxPotential] using htree

/-- The deterministic minimax prediction selected from the two continuation
potentials is always feasible in the source interval `[-1, 1]`. -/
theorem boundedSequentialMinimaxStrategy_mem_Icc {Context Hypothesis : Type*}
    [Nonempty Context] [Nonempty Hypothesis]
    (evaluation : Hypothesis → Context → ℝ) (horizon : ℕ)
    (history : List (Context × ℝ)) (context : Context)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (hhistory : ∀ observation ∈ history, observation.2 ∈ Set.Icc (-1 : ℝ) 1) :
    boundedSequentialMinimaxStrategy evaluation horizon history context ∈ Set.Icc (-1 : ℝ) 1 := by
  let remaining := horizon - history.length - 1
  have hincrease := boundedSequentialMinimaxPotential_append_one_le_append_negOne_add_two
    evaluation history context remaining hevaluation hhistory
  have hdecrease := boundedSequentialMinimaxPotential_append_negOne_le_append_one_add_two
    evaluation history context remaining hevaluation hhistory
  unfold boundedSequentialMinimaxStrategy
  dsimp only
  constructor <;> nlinarith

/-- Re-indexing the remaining-round potential by one fixed horizon gives the
one-step certificate required by the fixed-horizon relaxation interface. -/
theorem boundedSequentialMinimaxRelaxation_step
    {Context Hypothesis : Type*} [Nonempty Context] [Nonempty Hypothesis]
    (evaluation : Hypothesis → Context → ℝ) (horizon : ℕ)
    (history : List (Context × ℝ)) (observation : Context × ℝ)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1)
    (hhistory : ∀ prior ∈ history, prior.2 ∈ Set.Icc (-1 : ℝ) 1)
    (hprefix : history.length < horizon)
    (hadmissible : observation.2 ∈ Set.Icc (-1 : ℝ) 1) :
    boundedSequentialMinimaxPotential evaluation (history ++ [observation])
        (horizon - (history ++ [observation]).length) -
      boundedSequentialMinimaxStrategy evaluation horizon history observation.1 * observation.2 ≤
        boundedSequentialMinimaxPotential evaluation history (horizon - history.length) := by
  have hremaining : horizon - history.length = (horizon - history.length - 1) + 1 := by omega
  have hnext : horizon - (history ++ [observation]).length = horizon - history.length - 1 := by
    simp only [List.length_append, List.length_singleton]
    omega
  rw [hnext, hremaining]
  unfold boundedSequentialMinimaxStrategy
  dsimp only
  exact boundedSequentialMinimaxPotential_step_le evaluation history observation.1 observation.2
    hevaluation hhistory hadmissible

/-- The doubled sequential-Rademacher potential and its balanced strategy
form a valid fixed-horizon relaxation for an arbitrary nonempty bounded
comparator class. -/
theorem isFixedHorizonSequentialCorrelationRelaxation_boundedSequentialMinimax
    {Context Hypothesis : Type*} [Nonempty Context] [Nonempty Hypothesis]
    (evaluation : Hypothesis → Context → ℝ) (horizon : ℕ)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1) :
    IsFixedHorizonSequentialCorrelationRelaxation horizon
      (boundedSequentialMinimaxStrategy evaluation horizon)
      (fun history => boundedSequentialMinimaxPotential evaluation history
        (horizon - history.length))
      (Set.range evaluation)
      (fun observation => observation.2 ∈ Set.Icc (-1 : ℝ) 1) := by
  constructor
  · intro history comparator hlength hhistory hcomparator
    rcases hcomparator with ⟨hypothesis, rfl⟩
    rw [show horizon - history.length = 0 by omega]
    exact sequentialComparatorCorrelation_le_boundedSequentialMinimaxPotential_zero
      evaluation history hypothesis hevaluation hhistory
  · intro history observation hprefix hhistory hadmissible
    exact boundedSequentialMinimaxRelaxation_step evaluation horizon history observation
      hevaluation hhistory hprefix hadmissible

/-- The ordinary single-tree sequential Rademacher value is bounded above by
the horizon for a unit-bounded comparator class. -/
theorem boundedSequentialRademacherSum_le_horizon {Context Hypothesis : Type*}
    [Nonempty Hypothesis] {horizon : ℕ}
    (evaluation : Hypothesis → Context → ℝ) (tree : SequentialTree Context horizon)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1) :
    boundedSequentialRademacherSum evaluation tree ≤ horizon := by
  unfold boundedSequentialRademacherSum
  apply pmfExp_le_of_forall_le
  intro signs
  unfold sequentialCorrelationEnvelope
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨hypothesis, rfl⟩
  have hfuture := sequentialFutureCorrelation_le_horizon evaluation hypothesis tree signs
    hevaluation
  simp only [sequentialHistoryCorrelation, List.map_nil, List.sum_nil, zero_add, one_mul]
  exact hfuture

/-- The ordinary sequential Rademacher values form a bounded-above range under
the source's unit-range hypothesis. -/
theorem boundedSequentialRademacherSum_bddAbove {Context Hypothesis : Type*}
    [Nonempty Hypothesis] {horizon : ℕ}
    (evaluation : Hypothesis → Context → ℝ)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1) :
    BddAbove (Set.range (boundedSequentialRademacherSum evaluation :
      SequentialTree Context horizon → ℝ)) := by
  refine ⟨horizon, ?_⟩
  rintro _ ⟨tree, rfl⟩
  exact boundedSequentialRademacherSum_le_horizon evaluation tree hevaluation

/-- At an empty history, doubling the future perturbation doubles the
pointwise Rademacher envelope. -/
theorem sequentialCorrelationEnvelope_empty_two_eq_two_mul {Context Hypothesis : Type*}
    [Nonempty Hypothesis] {horizon : ℕ}
    (evaluation : Hypothesis → Context → ℝ) (tree : SequentialTree Context horizon)
    (signs : Fin horizon → Bool)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1) :
    sequentialCorrelationEnvelope evaluation [] 2 tree signs =
      2 * sequentialCorrelationEnvelope evaluation [] 1 tree signs := by
  have hfuture : BddAbove (Set.range fun hypothesis =>
      sequentialFutureCorrelation evaluation hypothesis tree signs) := by
    refine ⟨horizon, ?_⟩
    rintro _ ⟨hypothesis, rfl⟩
    exact sequentialFutureCorrelation_le_horizon evaluation hypothesis tree signs hevaluation
  unfold sequentialCorrelationEnvelope
  simp only [sequentialHistoryCorrelation, List.map_nil, List.sum_nil, zero_add]
  rw [show (Set.range fun hypothesis =>
      2 * sequentialFutureCorrelation evaluation hypothesis tree signs) =
      Set.range fun hypothesis =>
        2 * sequentialFutureCorrelation evaluation hypothesis tree signs by rfl]
  simpa only [one_mul] using two_mul_sSup_range _ hfuture

/-- The doubled-future potential at the empty history is exactly twice the
ordinary global sequential Rademacher process. -/
theorem boundedSequentialMinimaxPotential_empty_eq_two_mul_process
    {Context Hypothesis : Type*} [Nonempty Context] [Nonempty Hypothesis]
    {horizon : ℕ} (evaluation : Hypothesis → Context → ℝ)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1) :
    boundedSequentialMinimaxPotential evaluation [] horizon =
      2 * boundedSequentialRademacherProcess (horizon := horizon) evaluation := by
  have hbounded :=
    boundedSequentialRademacherSum_bddAbove (horizon := horizon) evaluation hevaluation
  have htree : ∀ tree : SequentialTree Context horizon,
      pmfExp (pmfProduct (Fin horizon) Bool (uniformPMF Bool))
          (sequentialCorrelationEnvelope evaluation [] 2 tree) =
        2 * boundedSequentialRademacherSum evaluation tree := by
    intro tree
    unfold boundedSequentialRademacherSum
    rw [show sequentialCorrelationEnvelope evaluation [] 2 tree =
        fun signs => 2 * sequentialCorrelationEnvelope evaluation [] 1 tree signs by
          funext signs
          exact sequentialCorrelationEnvelope_empty_two_eq_two_mul evaluation tree signs hevaluation]
    rw [pmfExp_const_mul]
  unfold boundedSequentialMinimaxPotential boundedSequentialRademacherProcess
  rw [show (Set.range fun tree : SequentialTree Context horizon =>
      pmfExp (pmfProduct (Fin horizon) Bool (uniformPMF Bool))
        (sequentialCorrelationEnvelope evaluation [] 2 tree)) =
      Set.range fun tree : SequentialTree Context horizon =>
        2 * boundedSequentialRademacherSum evaluation tree by
          ext value
          constructor
          · rintro ⟨tree, rfl⟩
            exact ⟨tree, (htree tree).symm⟩
          · rintro ⟨tree, rfl⟩
            exact ⟨tree, htree tree⟩]
  exact two_mul_sSup_range _ hbounded

/-- The noncomputable minimax strategy has pathwise correlation regret at
most twice the unnormalized global sequential Rademacher process, for an
arbitrary nonempty bounded comparator class and context type. -/
theorem boundedSequentialMinimax_comparatorRegret_le_two_rademacherProcess
    {Context Hypothesis : Type*} [Nonempty Context] [Nonempty Hypothesis]
    (evaluation : Hypothesis → Context → ℝ) (horizon : ℕ)
    (observations : List (Context × ℝ)) (hlength : observations.length = horizon)
    (hlabels : ∀ observation ∈ observations, observation.2 ∈ Set.Icc (-1 : ℝ) 1)
    (hypothesis : Hypothesis)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1) :
    sequentialComparatorCorrelation (evaluation hypothesis) observations -
      sequentialStrategyCorrelation (boundedSequentialMinimaxStrategy evaluation horizon) observations ≤
        2 * boundedSequentialRademacherProcess (horizon := horizon) evaluation := by
  have hrelax := isFixedHorizonSequentialCorrelationRelaxation_boundedSequentialMinimax
    evaluation horizon hevaluation
  have hcorrelation :=
    IsFixedHorizonSequentialCorrelationRelaxation.comparatorCorrelation_sub_strategyCorrelation_le
      horizon (boundedSequentialMinimaxStrategy evaluation horizon)
      (fun history => boundedSequentialMinimaxPotential evaluation history
        (horizon - history.length))
      (Set.range evaluation)
      (fun observation => observation.2 ∈ Set.Icc (-1 : ℝ) 1)
      hrelax observations hlength hlabels (evaluation hypothesis) ⟨hypothesis, rfl⟩
  have hroot := boundedSequentialMinimaxPotential_empty_eq_two_mul_process
    (horizon := horizon) evaluation hevaluation
  calc
    sequentialComparatorCorrelation (evaluation hypothesis) observations -
        sequentialStrategyCorrelation (boundedSequentialMinimaxStrategy evaluation horizon) observations ≤
      boundedSequentialMinimaxPotential evaluation [] (horizon - [].length) := hcorrelation
    _ = boundedSequentialMinimaxPotential evaluation [] horizon := by simp
    _ = 2 * boundedSequentialRademacherProcess (horizon := horizon) evaluation := hroot

/-- Source-normalized form of the arbitrary-class sequential minimax upper
bound.  The constant is the explicit factor two from the doubled relaxation. -/
theorem boundedSequentialMinimax_comparatorRegret_le_two_horizon_mul_complexity
    {Context Hypothesis : Type*} [Nonempty Context] [Nonempty Hypothesis]
    {horizon : ℕ} (horizonPositive : 0 < horizon)
    (evaluation : Hypothesis → Context → ℝ)
    (observations : List (Context × ℝ)) (hlength : observations.length = horizon)
    (hlabels : ∀ observation ∈ observations, observation.2 ∈ Set.Icc (-1 : ℝ) 1)
    (hypothesis : Hypothesis)
    (hevaluation : ∀ hypothesis context,
      evaluation hypothesis context ∈ Set.Icc (-1 : ℝ) 1) :
    sequentialComparatorCorrelation (evaluation hypothesis) observations -
      sequentialStrategyCorrelation (boundedSequentialMinimaxStrategy evaluation horizon) observations ≤
        2 * (horizon : ℝ) *
          boundedSequentialRademacherComplexity (horizon := horizon) evaluation := by
  have hprocess := boundedSequentialMinimax_comparatorRegret_le_two_rademacherProcess
    evaluation horizon observations hlength hlabels hypothesis hevaluation
  rw [show 2 * (horizon : ℝ) *
      boundedSequentialRademacherComplexity (horizon := horizon) evaluation =
        2 * boundedSequentialRademacherProcess (horizon := horizon) evaluation by
      unfold boundedSequentialRademacherComplexity
      have hcast : (horizon : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt horizonPositive
      field_simp]
  exact hprocess

/-- The signed OWAL regret against an arbitrary nonempty comparator class on
one adaptive Rademacher-tree path. -/
noncomputable def boundedSequentialSignedRegret
    {Context Hypothesis : Type*} [Nonempty Hypothesis] {horizon : ℕ}
    (evaluation : Hypothesis → Context → ℝ)
    (tree : SequentialTree Context horizon) (predictor : SequentialPredictor Context horizon)
    (signs : Fin horizon → Bool) : ℝ :=
  sequentialCorrelationEnvelope evaluation [] 1 tree signs -
    sequentialPredictorSignedCorrelation tree predictor signs

/-- Under iid Rademacher labels on any adaptive context tree, the expected
signed regret of every predictable mean predictor is exactly the ordinary
sequential Rademacher value of the class. -/
theorem pmfExp_boundedSequentialSignedRegret_eq_rademacherSum
    {Context Hypothesis : Type*} [Nonempty Hypothesis] {horizon : ℕ}
    (evaluation : Hypothesis → Context → ℝ)
    (tree : SequentialTree Context horizon) (predictor : SequentialPredictor Context horizon) :
    pmfExp (pmfProduct (Fin horizon) Bool (uniformPMF Bool))
        (boundedSequentialSignedRegret evaluation tree predictor) =
      boundedSequentialRademacherSum evaluation tree := by
  unfold boundedSequentialSignedRegret boundedSequentialRademacherSum
  rw [pmfExp_sub, pmfExp_sequentialPredictorSignedCorrelation_eq_zero]
  ring

/-- Every predictable mean predictor has a concrete Rademacher path whose
signed regret is at least the arbitrary-class sequential Rademacher value of
the prescribed adaptive context tree. -/
theorem exists_boundedSequentialSignedRegret_ge_rademacherSum
    {Context Hypothesis : Type*} [Nonempty Hypothesis] {horizon : ℕ}
    (evaluation : Hypothesis → Context → ℝ)
    (tree : SequentialTree Context horizon) (predictor : SequentialPredictor Context horizon) :
    ∃ signs : Fin horizon → Bool,
      boundedSequentialRademacherSum evaluation tree ≤
        boundedSequentialSignedRegret evaluation tree predictor signs := by
  classical
  let law := pmfProduct (Fin horizon) Bool (uniformPMF Bool)
  let regret := boundedSequentialSignedRegret evaluation tree predictor
  let process := boundedSequentialRademacherSum evaluation tree
  by_contra hnone
  have hall : ∀ signs : Fin horizon → Bool, regret signs < process := by
    intro signs
    exact lt_of_not_ge (fun hge => hnone ⟨signs, hge⟩)
  let defaultSigns : Fin horizon → Bool := fun _ => false
  have hmass : 0 < (law defaultSigns).toReal := by
    unfold law
    rw [pmfProduct_uniformPMF_eq_uniformPMF_fun]
    exact uniformPMF_apply_toReal_pos defaultSigns
  have hmean_lt : pmfExp law regret < process :=
    pmfExp_lt_of_forall_le_exists_lt law regret process
      (fun signs => (hall signs).le) ⟨defaultSigns, hmass, hall defaultSigns⟩
  have hmean_eq : pmfExp law regret = process := by
    exact pmfExp_boundedSequentialSignedRegret_eq_rademacherSum evaluation tree predictor
  rw [hmean_eq] at hmean_lt
  exact lt_irrefl _ hmean_lt

/-- A uniform pathwise OWAL regret bound over all adaptive context trees
must dominate the arbitrary-class unnormalized sequential Rademacher process. -/
theorem boundedSequentialRademacherProcess_le_of_all_tree_path_regret_le
    {Context Hypothesis : Type*} [Nonempty Context] [Nonempty Hypothesis]
    {horizon : ℕ} (evaluation : Hypothesis → Context → ℝ)
    (predictor : SequentialPredictor Context horizon) (bound : ℝ)
    (hbound : ∀ (tree : SequentialTree Context horizon) (signs : Fin horizon → Bool),
      boundedSequentialSignedRegret evaluation tree predictor signs ≤ bound) :
    boundedSequentialRademacherProcess (horizon := horizon) evaluation ≤ bound := by
  unfold boundedSequentialRademacherProcess
  apply csSup_le (Set.range_nonempty _)
  intro process hprocess
  rcases hprocess with ⟨tree, rfl⟩
  rcases exists_boundedSequentialSignedRegret_ge_rademacherSum
    evaluation tree predictor with ⟨signs, hregret⟩
  exact hregret.trans (hbound tree signs)

/-- Source-normalized arbitrary-class lower half of the sequential OWAL
minimax theorem. -/
theorem horizon_mul_boundedSequentialRademacherComplexity_le_of_all_tree_path_regret_le
    {Context Hypothesis : Type*} [Nonempty Context] [Nonempty Hypothesis]
    {horizon : ℕ} (horizonPositive : 0 < horizon)
    (evaluation : Hypothesis → Context → ℝ)
    (predictor : SequentialPredictor Context horizon) (bound : ℝ)
    (hbound : ∀ (tree : SequentialTree Context horizon) (signs : Fin horizon → Bool),
      boundedSequentialSignedRegret evaluation tree predictor signs ≤ bound) :
    (horizon : ℝ) * boundedSequentialRademacherComplexity (horizon := horizon) evaluation ≤ bound := by
  have hcast : (horizon : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt horizonPositive
  calc
    (horizon : ℝ) * boundedSequentialRademacherComplexity (horizon := horizon) evaluation =
        boundedSequentialRademacherProcess (horizon := horizon) evaluation := by
          unfold boundedSequentialRademacherComplexity
          field_simp
    _ ≤ bound := boundedSequentialRademacherProcess_le_of_all_tree_path_regret_le
      evaluation predictor bound hbound

end AppliedModelingLib.Learning.Online
