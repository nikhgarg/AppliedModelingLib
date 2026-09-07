import AppliedModelingLib.Learning.Online.Basic
import Mathlib.Tactic

/-!
# Sequential relaxation certificates for correlation learning

The standard sequential-Rademacher upper-bound proof constructs a relaxation:
a potential on observed context-label histories that both upper-bounds every
fixed comparator and decreases after the learner's next prediction.  This
file isolates the purely algebraic telescope.  A paper-specific minimax proof
must still construct the certificate; once it does, the resulting OWAL
guarantee is a closed consequence rather than an informal induction.
-/

namespace AppliedModelingLib.Learning.Online

open scoped BigOperators

/-- A prediction strategy may use the complete preceding context-label
history and the current context, but not the current label. -/
abbrev SequentialCorrelationStrategy (Context : Type*) :=
  List (Context × ℝ) → Context → ℝ

/-- The correlation accumulated by a fixed comparator on a finite history. -/
def sequentialComparatorCorrelation {Context : Type*}
    (comparator : Context → ℝ) (history : List (Context × ℝ)) : ℝ :=
  (history.map fun observation => comparator observation.1 * observation.2).sum

/-- The learner's correlation on a remaining suffix, with predictions formed
from the supplied preceding history. -/
def sequentialStrategyCorrelationFrom {Context : Type*}
    (strategy : SequentialCorrelationStrategy Context) :
    List (Context × ℝ) → List (Context × ℝ) → ℝ
  | _, [] => 0
  | history, observation :: remaining =>
      strategy history observation.1 * observation.2 +
        sequentialStrategyCorrelationFrom strategy (history ++ [observation]) remaining

/-- The learner's correlation on a complete online sequence. -/
def sequentialStrategyCorrelation {Context : Type*}
    (strategy : SequentialCorrelationStrategy Context)
    (observations : List (Context × ℝ)) : ℝ :=
  sequentialStrategyCorrelationFrom strategy [] observations

/-- A relaxation certifies both its terminal comparator domination and its
one-step decrease after the learner's current prediction. -/
structure IsSequentialCorrelationRelaxation {Context : Type*}
    (strategy : SequentialCorrelationStrategy Context) (relaxation : List (Context × ℝ) → ℝ)
    (comparators : Set (Context → ℝ)) : Prop where
  terminal : ∀ history comparator, comparator ∈ comparators →
    sequentialComparatorCorrelation comparator history ≤ relaxation history
  step : ∀ history observation,
    relaxation (history ++ [observation]) - strategy history observation.1 * observation.2 ≤
      relaxation history

/-- The minimax-balanced scalar prediction for two possible labels.  The
positive branch contributes `-prediction` to the loss-form relaxation and the
negative branch contributes `+prediction`. -/
noncomputable def balancedTwoBranchPrediction (positiveBranch negativeBranch : ℝ) : ℝ :=
  (positiveBranch - negativeBranch) / 2

/-- If the two continuation values differ by at most two, their balancing
prediction is feasible in the OWAL prediction interval `[-1,1]`. -/
theorem balancedTwoBranchPrediction_mem_Icc
    {positiveBranch negativeBranch : ℝ}
    (hdifference : |positiveBranch - negativeBranch| ≤ 2) :
    balancedTwoBranchPrediction positiveBranch negativeBranch ∈ Set.Icc (-1 : ℝ) 1 := by
  unfold balancedTwoBranchPrediction
  apply abs_le.mp
  have hratio : |(positiveBranch - negativeBranch) / 2| ≤ 1 := by
    rw [abs_div]
    calc
      |positiveBranch - negativeBranch| / |(2 : ℝ)| ≤ 2 / |(2 : ℝ)| :=
        div_le_div_of_nonneg_right hdifference (by norm_num)
      _ = 1 := by norm_num
  exact hratio

/-- The balanced prediction makes the positive and negative continuation
costs identical, at their arithmetic mean. -/
theorem positiveBranch_sub_balancedTwoBranchPrediction
    (positiveBranch negativeBranch : ℝ) :
    positiveBranch - balancedTwoBranchPrediction positiveBranch negativeBranch =
      (positiveBranch + negativeBranch) / 2 := by
  unfold balancedTwoBranchPrediction
  ring

/-- The companion negative-label branch has the same balanced value. -/
theorem negativeBranch_add_balancedTwoBranchPrediction
    (positiveBranch negativeBranch : ℝ) :
    negativeBranch + balancedTwoBranchPrediction positiveBranch negativeBranch =
      (positiveBranch + negativeBranch) / 2 := by
  unfold balancedTwoBranchPrediction
  ring

/-- The one-step condition telescopes along every remaining suffix. -/
private theorem IsSequentialCorrelationRelaxation.relaxation_sub_strategyCorrelationFrom_le
    {Context : Type*} (strategy : SequentialCorrelationStrategy Context)
    (relaxation : List (Context × ℝ) → ℝ) (comparators : Set (Context → ℝ))
    (hrelax : IsSequentialCorrelationRelaxation strategy relaxation comparators) :
    ∀ (history remaining : List (Context × ℝ)),
      relaxation (history ++ remaining) -
        sequentialStrategyCorrelationFrom strategy history remaining ≤ relaxation history := by
  intro history remaining
  induction remaining generalizing history with
  | nil => simp [sequentialStrategyCorrelationFrom]
  | cons observation remaining ih =>
      have htail := ih (history ++ [observation])
      have hstep := hrelax.step history observation
      rw [show history ++ observation :: remaining =
        (history ++ [observation]) ++ remaining by simp [List.append_assoc]]
      simp only [sequentialStrategyCorrelationFrom]
      linarith

/-- A certified relaxation gives a pathwise OWAL correlation guarantee for
every comparator in its class. -/
theorem IsSequentialCorrelationRelaxation.comparatorCorrelation_sub_strategyCorrelation_le
    {Context : Type*} (strategy : SequentialCorrelationStrategy Context)
    (relaxation : List (Context × ℝ) → ℝ) (comparators : Set (Context → ℝ))
    (hrelax : IsSequentialCorrelationRelaxation strategy relaxation comparators)
    (observations : List (Context × ℝ)) (comparator : Context → ℝ)
    (hcomparator : comparator ∈ comparators) :
    sequentialComparatorCorrelation comparator observations -
      sequentialStrategyCorrelation strategy observations ≤ relaxation [] := by
  have hterminal := hrelax.terminal observations comparator hcomparator
  have htelescope :=
    IsSequentialCorrelationRelaxation.relaxation_sub_strategyCorrelationFrom_le
      strategy relaxation comparators hrelax [] observations
  unfold sequentialStrategyCorrelation
  calc
    sequentialComparatorCorrelation comparator observations -
        sequentialStrategyCorrelationFrom strategy [] observations ≤
        relaxation observations - sequentialStrategyCorrelationFrom strategy [] observations :=
      sub_le_sub_right hterminal _
    _ ≤ relaxation [] := by
      simpa using htelescope

/-- A sequential correlation relaxation required only along admissible
prefixes of one fixed finite horizon.  This is the appropriate certificate
when a potential is defined by the number of rounds remaining. -/
structure IsFixedHorizonSequentialCorrelationRelaxation {Context : Type*}
    (horizon : ℕ) (strategy : SequentialCorrelationStrategy Context)
    (relaxation : List (Context × ℝ) → ℝ) (comparators : Set (Context → ℝ))
    (admissible : Context × ℝ → Prop) : Prop where
  terminal : ∀ history comparator, history.length = horizon →
    (∀ observation ∈ history, admissible observation) → comparator ∈ comparators →
    sequentialComparatorCorrelation comparator history ≤ relaxation history
  step : ∀ history observation, history.length < horizon →
    (∀ prior ∈ history, admissible prior) → admissible observation →
    relaxation (history ++ [observation]) - strategy history observation.1 * observation.2 ≤
      relaxation history

/-- The fixed-horizon one-step certificate telescopes through every
admissible suffix that completes the declared horizon. -/
private theorem IsFixedHorizonSequentialCorrelationRelaxation.relaxation_sub_strategyCorrelationFrom_le
    {Context : Type*} (horizon : ℕ) (strategy : SequentialCorrelationStrategy Context)
    (relaxation : List (Context × ℝ) → ℝ) (comparators : Set (Context → ℝ))
    (admissible : Context × ℝ → Prop)
    (hrelax : IsFixedHorizonSequentialCorrelationRelaxation horizon strategy relaxation
      comparators admissible) :
    ∀ (history remaining : List (Context × ℝ)),
      history.length + remaining.length = horizon →
      (∀ observation ∈ history, admissible observation) →
      (∀ observation ∈ remaining, admissible observation) →
      relaxation (history ++ remaining) -
        sequentialStrategyCorrelationFrom strategy history remaining ≤ relaxation history := by
  intro history remaining
  induction remaining generalizing history with
  | nil =>
      intro hlength hhistory hadmissible
      simp [sequentialStrategyCorrelationFrom]
  | cons observation remaining ih =>
      intro hlength hhistory hadmissible
      simp only [List.length_cons] at hlength
      have hprefix : history.length < horizon := by omega
      have hstep := hrelax.step history observation hprefix
        hhistory (hadmissible observation (by simp))
      have htailLength : (history ++ [observation]).length + remaining.length = horizon := by
        simp only [List.length_append, List.length_singleton]
        omega
      have htailAdmissible : ∀ later ∈ remaining, admissible later := by
        intro later hlater
        exact hadmissible later (by simp [hlater])
      have htailHistory : ∀ prior ∈ history ++ [observation], admissible prior := by
        intro prior hprior
        rcases List.mem_append.mp hprior with hprior | hprior
        · exact hhistory prior hprior
        · simp only [List.mem_singleton] at hprior
          subst prior
          exact hadmissible observation (by simp)
      have htail := ih (history ++ [observation]) htailLength htailHistory htailAdmissible
      rw [show history ++ observation :: remaining =
        (history ++ [observation]) ++ remaining by simp [List.append_assoc]]
      simp only [sequentialStrategyCorrelationFrom]
      linarith

/-- A fixed-horizon relaxation gives a pathwise comparator-correlation
guarantee for every admissible observation sequence of that horizon. -/
theorem IsFixedHorizonSequentialCorrelationRelaxation.comparatorCorrelation_sub_strategyCorrelation_le
    {Context : Type*} (horizon : ℕ) (strategy : SequentialCorrelationStrategy Context)
    (relaxation : List (Context × ℝ) → ℝ) (comparators : Set (Context → ℝ))
    (admissible : Context × ℝ → Prop)
    (hrelax : IsFixedHorizonSequentialCorrelationRelaxation horizon strategy relaxation
      comparators admissible)
    (observations : List (Context × ℝ)) (hlength : observations.length = horizon)
    (hadmissible : ∀ observation ∈ observations, admissible observation)
    (comparator : Context → ℝ) (hcomparator : comparator ∈ comparators) :
    sequentialComparatorCorrelation comparator observations -
      sequentialStrategyCorrelation strategy observations ≤ relaxation [] := by
  have hterminal := hrelax.terminal observations comparator hlength hadmissible hcomparator
  have htelescope :=
    IsFixedHorizonSequentialCorrelationRelaxation.relaxation_sub_strategyCorrelationFrom_le
      horizon strategy relaxation comparators admissible hrelax [] observations (by simpa)
        (fun observation hmem => by simp at hmem) hadmissible
  unfold sequentialStrategyCorrelation
  calc
    sequentialComparatorCorrelation comparator observations -
        sequentialStrategyCorrelationFrom strategy [] observations ≤
        relaxation observations - sequentialStrategyCorrelationFrom strategy [] observations :=
      sub_le_sub_right hterminal _
    _ ≤ relaxation [] := by simpa using htelescope

end AppliedModelingLib.Learning.Online
