import Mathlib.Tactic

/-!
# Confidence-set agreement for preference-to-reward interfaces

This module records the deterministic no-query branch of a preference-to-reward
interface. If every candidate reward in a confidence set agrees on a trajectory
relative to a fixed reference trajectory, then an arbitrary in-set prediction
is accurate whenever the true reward remains in that set.
-/

namespace AppliedModelingLib

namespace PreferenceRL

/-- The reward label used by P2R is relative to its fixed reference trajectory. -/
noncomputable def relativeTrajectoryReward {Trajectory : Type*}
    (reward : Trajectory → ℝ) (trajectory reference : Trajectory) : ℝ :=
  reward trajectory - reward reference

/-- A reward function normalized relative to P2R's fixed reference trajectory. -/
noncomputable def relativeTrajectoryRewardFunction {Trajectory : Type*}
    (reward : Trajectory → ℝ) (reference : Trajectory) : Trajectory → ℝ :=
  fun trajectory => relativeTrajectoryReward reward trajectory reference

@[simp] theorem relativeTrajectoryRewardFunction_apply {Trajectory : Type*}
    (reward : Trajectory → ℝ) (trajectory reference : Trajectory) :
    relativeTrajectoryRewardFunction reward reference trajectory =
      relativeTrajectoryReward reward trajectory reference := rfl

/--
The closed version of P2R Algorithm 1, Line 6: every two candidate rewards
have relative labels separated by at most the supplied tolerance.
-/
def P2RConfidenceAgreement {Trajectory : Type*}
    (candidates : Set (Trajectory → ℝ)) (trajectory reference : Trajectory)
    (tolerance : ℝ) : Prop :=
  ∀ firstReward ∈ candidates, ∀ secondReward ∈ candidates,
    relativeTrajectoryReward firstReward trajectory reference -
      relativeTrajectoryReward secondReward trajectory reference ≤ tolerance

/--
The open version of P2R Algorithm 1's Line 6: two confidence-set rewards have
relative labels separated by more than twice the tolerance, so the comparison
oracle is queried.
-/
def P2RQueryNeeded {Trajectory : Type*}
    (candidates : Set (Trajectory → ℝ)) (trajectory reference : Trajectory)
    (tolerance : ℝ) : Prop :=
  ∃ firstReward ∈ candidates, ∃ secondReward ∈ candidates,
    2 * tolerance < relativeTrajectoryReward firstReward trajectory reference -
      relativeTrajectoryReward secondReward trajectory reference

/--
The literal Algorithm-1 query branch: Line 6 skips a comparison only when
the displayed maximum is strictly below `2 * tolerance`, so equality enters
the query branch.  This closed predicate is the source-faithful operational
condition; `P2RQueryNeeded` above remains useful for strict analytical
statements.
-/
def P2RQueryTriggered {Trajectory : Type*}
    (candidates : Set (Trajectory → ℝ)) (trajectory reference : Trajectory)
    (tolerance : ℝ) : Prop :=
  ∃ firstReward ∈ candidates, ∃ secondReward ∈ candidates,
    2 * tolerance ≤ relativeTrajectoryReward firstReward trajectory reference -
      relativeTrajectoryReward secondReward trajectory reference

/--
Two relative labels separated by more than twice a tolerance cannot both be
within that tolerance of the same true relative label.
-/
theorem relativeErrorWitness_of_relativeGap {Trajectory : Type*}
    (trueReward firstReward secondReward : Trajectory → ℝ)
    (trajectory reference : Trajectory) (tolerance : ℝ)
    (hgap : 2 * tolerance <
      relativeTrajectoryReward firstReward trajectory reference -
        relativeTrajectoryReward secondReward trajectory reference) :
    tolerance < |relativeTrajectoryReward firstReward trajectory reference -
        relativeTrajectoryReward trueReward trajectory reference| ∨
      tolerance < |relativeTrajectoryReward secondReward trajectory reference -
        relativeTrajectoryReward trueReward trajectory reference| := by
  by_contra hno
  push Not at hno
  have hfirst : relativeTrajectoryReward firstReward trajectory reference -
      relativeTrajectoryReward trueReward trajectory reference ≤ tolerance :=
    (abs_le.mp hno.1).2
  have hsecond : -tolerance ≤ relativeTrajectoryReward secondReward trajectory reference -
      relativeTrajectoryReward trueReward trajectory reference :=
    (abs_le.mp hno.2).1
  linarith

/--
Whenever P2R queries because its confidence set disagrees, one of the two
disagreeing in-set labels has relative error greater than the query tolerance.
-/
theorem p2rQueryNeeded_has_relativeErrorWitness {Trajectory : Type*}
    (candidates : Set (Trajectory → ℝ)) (trueReward : Trajectory → ℝ)
    (trajectory reference : Trajectory) (tolerance : ℝ)
    (hquery : P2RQueryNeeded candidates trajectory reference tolerance) :
    ∃ selectedReward ∈ candidates,
      tolerance < |relativeTrajectoryReward selectedReward trajectory reference -
        relativeTrajectoryReward trueReward trajectory reference| := by
  rcases hquery with ⟨firstReward, hfirst, secondReward, hsecond, hgap⟩
  rcases relativeErrorWitness_of_relativeGap trueReward firstReward secondReward
    trajectory reference tolerance hgap with herror | herror
  · exact ⟨firstReward, hfirst, herror⟩
  · exact ⟨secondReward, hsecond, herror⟩

/--
The equality-inclusive Algorithm-1 query condition still supplies an eluder
witness at the threshold scale. -/
theorem p2rQueryTriggered_has_relativeErrorWitness {Trajectory : Type*}
    (candidates : Set (Trajectory → ℝ)) (trueReward : Trajectory → ℝ)
    (trajectory reference : Trajectory) (tolerance : ℝ)
    (hquery : P2RQueryTriggered candidates trajectory reference tolerance) :
    ∃ selectedReward ∈ candidates,
      tolerance ≤ |relativeTrajectoryReward selectedReward trajectory reference -
        relativeTrajectoryReward trueReward trajectory reference| := by
  rcases hquery with ⟨firstReward, hfirst, secondReward, hsecond, hgap⟩
  by_contra hno
  push Not at hno
  have hfirstUpper :
      relativeTrajectoryReward firstReward trajectory reference -
        relativeTrajectoryReward trueReward trajectory reference < tolerance :=
    (abs_lt.mp (hno firstReward hfirst)).2
  have hsecondLower :
      -tolerance < relativeTrajectoryReward secondReward trajectory reference -
        relativeTrajectoryReward trueReward trajectory reference :=
    (abs_lt.mp (hno secondReward hsecond)).1
  linarith

/--
The literal no-query branch of Algorithm 1 gives the `2 * tolerance`
confidence-set agreement used for its returned label. -/
theorem p2rConfidenceAgreement_two_mul_of_not_queryTriggered {Trajectory : Type*}
    (candidates : Set (Trajectory → ℝ)) (trajectory reference : Trajectory)
    (tolerance : ℝ)
    (hnoQuery : ¬ P2RQueryTriggered candidates trajectory reference tolerance) :
    P2RConfidenceAgreement candidates trajectory reference (2 * tolerance) := by
  intro firstReward hfirst secondReward hsecond
  by_contra hnot
  exact hnoQuery ⟨firstReward, hfirst, secondReward, hsecond, le_of_lt (lt_of_not_ge hnot)⟩

/-- The squared relative-label fit of a reward on P2R's queried dataset. -/
noncomputable def p2rRelativeSquaredFit {Trajectory : Type*}
    (reward : Trajectory → ℝ) (reference : Trajectory)
    (queriedLabels : List (Trajectory × ℝ)) : ℝ :=
  (queriedLabels.map fun datum =>
    (relativeTrajectoryReward reward datum.1 reference - datum.2) ^ 2).sum

/-- P2R's finite reward confidence set, defined by squared relative-label fit. -/
def P2RRelativeConfidenceSet {Trajectory : Type*}
    (candidates : Set (Trajectory → ℝ)) (reference : Trajectory)
    (queriedLabels : List (Trajectory × ℝ)) (budget : ℝ) : Set (Trajectory → ℝ) :=
  { reward | reward ∈ candidates ∧
    p2rRelativeSquaredFit reward reference queriedLabels ≤ budget }

/-- The squared relative-reward discrepancy of two candidates on P2R's data. -/
noncomputable def p2rRelativeSquaredDifference {Trajectory : Type*}
    (firstReward secondReward : Trajectory → ℝ) (reference : Trajectory)
    (queriedLabels : List (Trajectory × ℝ)) : ℝ :=
  (queriedLabels.map fun datum =>
    (relativeTrajectoryReward firstReward datum.1 reference -
      relativeTrajectoryReward secondReward datum.1 reference) ^ 2).sum

/--
Two rewards' squared relative discrepancy is bounded by twice each reward's
squared residual to the same queried labels. This is the finite triangle
calculation used in P2R's confidence-set analysis.
-/
theorem p2rRelativeSquaredDifference_le_two_mul_fits {Trajectory : Type*}
    (firstReward secondReward : Trajectory → ℝ) (reference : Trajectory)
    (queriedLabels : List (Trajectory × ℝ)) :
    p2rRelativeSquaredDifference firstReward secondReward reference queriedLabels ≤
      2 * p2rRelativeSquaredFit firstReward reference queriedLabels +
        2 * p2rRelativeSquaredFit secondReward reference queriedLabels := by
  induction queriedLabels with
  | nil =>
      simp [p2rRelativeSquaredDifference, p2rRelativeSquaredFit]
  | cons datum remaining ih =>
      have hdatum :
          (relativeTrajectoryReward firstReward datum.1 reference -
            relativeTrajectoryReward secondReward datum.1 reference) ^ 2 ≤
            2 * (relativeTrajectoryReward firstReward datum.1 reference - datum.2) ^ 2 +
              2 * (relativeTrajectoryReward secondReward datum.1 reference - datum.2) ^ 2 := by
        nlinarith [sq_nonneg
          ((relativeTrajectoryReward firstReward datum.1 reference - datum.2) +
            (relativeTrajectoryReward secondReward datum.1 reference - datum.2))]
      calc
        p2rRelativeSquaredDifference firstReward secondReward reference (datum :: remaining) =
            (relativeTrajectoryReward firstReward datum.1 reference -
              relativeTrajectoryReward secondReward datum.1 reference) ^ 2 +
              p2rRelativeSquaredDifference firstReward secondReward reference remaining := by
                simp [p2rRelativeSquaredDifference]
        _ ≤ (2 * (relativeTrajectoryReward firstReward datum.1 reference - datum.2) ^ 2 +
              2 * (relativeTrajectoryReward secondReward datum.1 reference - datum.2) ^ 2) +
            (2 * p2rRelativeSquaredFit firstReward reference remaining +
              2 * p2rRelativeSquaredFit secondReward reference remaining) :=
          add_le_add hdatum ih
        _ = 2 * p2rRelativeSquaredFit firstReward reference (datum :: remaining) +
              2 * p2rRelativeSquaredFit secondReward reference (datum :: remaining) := by
          simp [p2rRelativeSquaredFit]
          ring

/--
Two members of the same finite P2R confidence set have squared relative
discrepancy at most four times its fit budget.
-/
theorem p2rRelativeSquaredDifference_le_four_mul_budget_of_confidenceMembers
    {Trajectory : Type*} (candidates : Set (Trajectory → ℝ))
    (firstReward secondReward : Trajectory → ℝ) (reference : Trajectory)
    (queriedLabels : List (Trajectory × ℝ)) (budget : ℝ)
    (hfirst : firstReward ∈
      P2RRelativeConfidenceSet candidates reference queriedLabels budget)
    (hsecond : secondReward ∈
      P2RRelativeConfidenceSet candidates reference queriedLabels budget) :
    p2rRelativeSquaredDifference firstReward secondReward reference queriedLabels ≤
      4 * budget := by
  calc
    p2rRelativeSquaredDifference firstReward secondReward reference queriedLabels ≤
        2 * p2rRelativeSquaredFit firstReward reference queriedLabels +
          2 * p2rRelativeSquaredFit secondReward reference queriedLabels :=
      p2rRelativeSquaredDifference_le_two_mul_fits firstReward secondReward reference queriedLabels
    _ ≤ 2 * budget + 2 * budget :=
      add_le_add (mul_le_mul_of_nonneg_left hfirst.2 (by norm_num))
        (mul_le_mul_of_nonneg_left hsecond.2 (by norm_num))
    _ = 4 * budget := by ring

/--
Uniform relative-label accuracy bounds the true reward's squared fit by the
number of queried labels times the squared label-error bound.
-/
theorem p2rRelativeSquaredFit_le_length_mul_sq_of_uniformLabelError {Trajectory : Type*}
    (reward : Trajectory → ℝ) (reference : Trajectory)
    (queriedLabels : List (Trajectory × ℝ)) (error : ℝ)
    (herror : ∀ datum ∈ queriedLabels,
      |relativeTrajectoryReward reward datum.1 reference - datum.2| ≤ error) :
    p2rRelativeSquaredFit reward reference queriedLabels ≤
      (queriedLabels.length : ℝ) * error ^ 2 := by
  induction queriedLabels with
  | nil =>
      simp [p2rRelativeSquaredFit]
  | cons datum remaining ih =>
      have hdatum :
          |relativeTrajectoryReward reward datum.1 reference - datum.2| ≤ error :=
        herror datum (by simp)
      have hremaining : ∀ later ∈ remaining,
          |relativeTrajectoryReward reward later.1 reference - later.2| ≤ error := by
        intro later hlater
        exact herror later (by simp [hlater])
      have hdatumSq :
          (relativeTrajectoryReward reward datum.1 reference - datum.2) ^ 2 ≤ error ^ 2 := by
        have hbounds := abs_le.mp hdatum
        nlinarith
      calc
        p2rRelativeSquaredFit reward reference (datum :: remaining) =
            (relativeTrajectoryReward reward datum.1 reference - datum.2) ^ 2 +
              p2rRelativeSquaredFit reward reference remaining := by
                simp [p2rRelativeSquaredFit]
        _ ≤ error ^ 2 + (remaining.length : ℝ) * error ^ 2 :=
          add_le_add hdatumSq (ih hremaining)
        _ = ((datum :: remaining).length : ℝ) * error ^ 2 := by
          simp
          ring

/--
Uniformly accurate queried labels retain the true reward in the P2R confidence
set whenever its stated fit budget covers the resulting finite sum.
-/
theorem p2r_mem_relativeConfidenceSet_of_uniformLabelError {Trajectory : Type*}
    (candidates : Set (Trajectory → ℝ)) (reward : Trajectory → ℝ)
    (reference : Trajectory) (queriedLabels : List (Trajectory × ℝ))
    (error budget : ℝ) (hmember : reward ∈ candidates)
    (herror : ∀ datum ∈ queriedLabels,
      |relativeTrajectoryReward reward datum.1 reference - datum.2| ≤ error)
    (hbudget : (queriedLabels.length : ℝ) * error ^ 2 ≤ budget) :
    reward ∈ P2RRelativeConfidenceSet candidates reference queriedLabels budget :=
  ⟨hmember,
    (p2rRelativeSquaredFit_le_length_mul_sq_of_uniformLabelError reward reference
      queriedLabels error herror).trans hbudget⟩

/--
The preceding confidence-set retention bound in the form used after an eluder
query-count cap: a length at most `dimension` suffices when the budget covers
`dimension * error²`.
-/
theorem p2r_mem_relativeConfidenceSet_of_uniformLabelError_of_length_le
    {Trajectory : Type*} (candidates : Set (Trajectory → ℝ))
    (reward : Trajectory → ℝ) (reference : Trajectory)
    (queriedLabels : List (Trajectory × ℝ)) (dimension : ℕ) (error budget : ℝ)
    (hmember : reward ∈ candidates)
    (herror : ∀ datum ∈ queriedLabels,
      |relativeTrajectoryReward reward datum.1 reference - datum.2| ≤ error)
    (hlength : queriedLabels.length ≤ dimension)
    (hbudget : (dimension : ℝ) * error ^ 2 ≤ budget) :
    reward ∈ P2RRelativeConfidenceSet candidates reference queriedLabels budget := by
  apply p2r_mem_relativeConfidenceSet_of_uniformLabelError candidates reward reference
    queriedLabels error budget hmember herror
  have hlengthReal : (queriedLabels.length : ℝ) ≤ (dimension : ℝ) := by
    exact_mod_cast hlength
  calc
    (queriedLabels.length : ℝ) * error ^ 2 ≤ (dimension : ℝ) * error ^ 2 :=
      mul_le_mul_of_nonneg_right hlengthReal (sq_nonneg error)
    _ ≤ budget := hbudget

/--
P2R's returned relative label is accurate in either branch: a queried label
uses its query-accuracy guarantee, while a no-query label uses confidence-set
agreement and membership of both the selected and true rewards.
-/
theorem p2rReturnedLabelError_le_of_query_or_confidence {Trajectory : Type*}
    (queryMade : Prop) [Decidable queryMade]
    (label : ℝ) (candidates : Set (Trajectory → ℝ))
    (trueReward selectedReward : Trajectory → ℝ)
    (trajectory reference : Trajectory) (tolerance : ℝ)
    (hqueried : queryMade →
      |label - relativeTrajectoryReward trueReward trajectory reference| ≤ tolerance)
    (hnoQueryLabel : ¬ queryMade →
      label = relativeTrajectoryReward selectedReward trajectory reference)
    (htrue : trueReward ∈ candidates) (hselected : selectedReward ∈ candidates)
    (hnoQueryAgreement : ¬ queryMade →
      P2RConfidenceAgreement candidates trajectory reference tolerance) :
    |label - relativeTrajectoryReward trueReward trajectory reference| ≤ tolerance := by
  by_cases hquery : queryMade
  · exact hqueried hquery
  · rw [hnoQueryLabel hquery]
    rw [abs_le]
    constructor
    · have hswap := hnoQueryAgreement hquery trueReward htrue selectedReward hselected
      linarith
    · exact hnoQueryAgreement hquery selectedReward hselected trueReward htrue

/--
An arbitrary in-set relative-reward prediction is close to the true relative
reward when the P2R confidence set agrees and contains the truth.
-/
theorem p2rConfidenceAgreement_relativeError_le {Trajectory : Type*}
    (candidates : Set (Trajectory → ℝ)) (trueReward selectedReward : Trajectory → ℝ)
    (trajectory reference : Trajectory) (tolerance : ℝ)
    (htrue : trueReward ∈ candidates) (hselected : selectedReward ∈ candidates)
    (hagreement : P2RConfidenceAgreement candidates trajectory reference tolerance) :
    |relativeTrajectoryReward selectedReward trajectory reference -
        relativeTrajectoryReward trueReward trajectory reference| ≤ tolerance := by
  rw [abs_le]
  constructor
  · have hswap := hagreement trueReward htrue selectedReward hselected
    linarith
  · exact hagreement selectedReward hselected trueReward htrue

end PreferenceRL

end AppliedModelingLib
