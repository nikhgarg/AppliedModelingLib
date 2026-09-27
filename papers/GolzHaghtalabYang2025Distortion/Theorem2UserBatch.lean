import GolzHaghtalabYang2025Distortion.Theorem5FiniteSample
import AppliedModelingLib.Foundations.Probability.IndependentProduct

/-!
# Source-faithful finite user batches for Theorem 2

Appendix D samples comparison labels independently within each user, while a
user's answers to the resulting comparisons may be correlated. In particular,
repeated displays of one pair receive the same answer. This module represents
one user by a random binary response table, independent of that user's iid
sampled comparison labels. Thus every within-user response dependence remains
available, while the source's label sampling is literal.
-/

namespace GolzHaghtalabYang2025Distortion

open scoped BigOperators

open AppliedModelingLib
open AppliedModelingLib.Learning.HumanFeedback
open AppliedModelingLib.Alignment.Welfare

/-- The source's one-user latent table of pairwise binary answers. -/
abbrev theorem2UserResponseTable (Alternative : Type*) := Alternative → Alternative → Bool

/-- A single user's answers are orientation-consistent on every unordered pair. -/
def theorem2UserResponseOrientationConsistent
    {Alternative : Type*} (response : theorem2UserResponseTable Alternative) : Prop :=
  ∀ first second, response second first = !response first second

/-- The response law is supported on orientation-consistent user tables. -/
def theorem2UserResponseLawOrientationConsistent
    {Alternative : Type*}
    (responseLaw : PMF (theorem2UserResponseTable Alternative)) : Prop :=
  ∀ response, responseLaw response ≠ 0 → theorem2UserResponseOrientationConsistent response

/--
The finite report bundle contributed by one source user. Its answer at a
displayed ordered pair is read from that user's one response table, so repeated
displays necessarily receive the same answer.
-/
abbrev theorem2UserBatchReport (Alternative : Type*) (comparisonsPerUser : ℕ) :=
  Fin comparisonsPerUser → ((Alternative × Alternative) × Bool)

/-- Independent source sampling of the two displayed alternatives. -/
noncomputable def theorem2UserPairLabelLaw
    {Alternative : Type*} [Fintype Alternative]
    (sampling : PMF Alternative) : PMF (Alternative × Alternative) :=
  pmfProd sampling sampling

/--
The literal one-user source law: draw one response table, then independently
draw every ordered pair label, and read each displayed answer from that table.
This leaves arbitrary dependence among a user's answers to distinct pairs.
-/
noncomputable def theorem2UserBatchLaw
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (comparisonsPerUser : ℕ) :
    PMF (theorem2UserBatchReport Alternative comparisonsPerUser) :=
  (pmfProd responseLaw
    (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
      (theorem2UserPairLabelLaw sampling))).map
    (fun draw position =>
      ((draw.2 position), draw.1 (draw.2 position).1 (draw.2 position).2))

/-- The number of Borda comparison incidences contributed by one user batch. -/
def theorem2UserBatchBordaIncidences
    {Alternative : Type*} [DecidableEq Alternative] {comparisonsPerUser : ℕ}
    (alternative : Alternative) (report : theorem2UserBatchReport Alternative comparisonsPerUser) : ℝ :=
  ∑ position, theorem12OneComparisonIncidences alternative (report position)

/-- The number of Borda wins contributed by one user batch. -/
def theorem2UserBatchBordaWins
    {Alternative : Type*} [DecidableEq Alternative] {comparisonsPerUser : ℕ}
    (alternative : Alternative) (report : theorem2UserBatchReport Alternative comparisonsPerUser) : ℝ :=
  ∑ position, theorem12OneComparisonWins alternative (report position)

/--
Calibration of the random response table to the paper's population pairwise
preference. It fixes only each pairwise marginal and deliberately imposes no
independence among the entries of one user's table.
-/
def theorem2UserResponseCalibrated
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (preference : PairwisePreference PUnit Alternative) : Prop :=
  ∀ first second,
    pmfExp responseLaw (fun response =>
      if response first second then (1 : ℝ) else 0) =
      preference.prob PUnit.unit first second

/-- The response-table expectation of a false binary answer is its true-answer complement. -/
theorem theorem2UserResponseCalibrated_false
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {preference : PairwisePreference PUnit Alternative}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (first second : Alternative) :
    pmfExp responseLaw (fun response =>
      if response first second then (0 : ℝ) else 1) =
      1 - preference.prob PUnit.unit first second := by
  calc
    pmfExp responseLaw (fun response =>
        if response first second then (0 : ℝ) else 1) =
      pmfExp responseLaw (fun response =>
        1 - if response first second then (1 : ℝ) else 0) := by
          apply pmfExp_congr
          intro response
          cases response first second <;> norm_num
    _ = 1 - pmfExp responseLaw (fun response =>
        if response first second then (1 : ℝ) else 0) := by
          rw [pmfExp_sub, pmfExp_const]
    _ = 1 - preference.prob PUnit.unit first second := by
          rw [hcalibrated first second]

/--
For a fixed displayed pair, the response-table model has the same expected
Borda wins as the paper's one-comparison marginal law.
-/
theorem theorem2UserResponse_pmfExp_wins_eq_oneComparison
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {preference : PairwisePreference PUnit Alternative}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (alternative first second : Alternative) :
    pmfExp responseLaw (fun response =>
      theorem12OneComparisonWins alternative
        ((first, second), response first second)) =
      preference.prob PUnit.unit first second *
        theorem12OneComparisonWins alternative ((first, second), true) +
      (1 - preference.prob PUnit.unit first second) *
        theorem12OneComparisonWins alternative ((first, second), false) := by
  by_cases hfirst : first = alternative <;> by_cases hsecond : second = alternative
  · subst first
    subst second
    rw [show (fun response : theorem2UserResponseTable Alternative =>
        theorem12OneComparisonWins alternative
          ((alternative, alternative), response alternative alternative)) =
        fun _ => (1 : ℝ) by
          funext response
          cases hresponse : response alternative alternative <;>
            simp [theorem12OneComparisonWins]]
    simp [theorem12OneComparisonWins]
  · subst first
    rw [show (fun response : theorem2UserResponseTable Alternative =>
        theorem12OneComparisonWins alternative
          ((alternative, second), response alternative second)) =
        fun response => if response alternative second then (1 : ℝ) else 0 by
          funext response
          simp [theorem12OneComparisonWins, hsecond]]
    rw [hcalibrated]
    simp [theorem12OneComparisonWins, hsecond]
  · subst second
    rw [show (fun response : theorem2UserResponseTable Alternative =>
        theorem12OneComparisonWins alternative
          ((first, alternative), response first alternative)) =
        fun response => if response first alternative then (0 : ℝ) else 1 by
          funext response
          cases hresponse : response first alternative <;>
            simp [theorem12OneComparisonWins, hfirst]]
    rw [theorem2UserResponseCalibrated_false hcalibrated]
    simp [theorem12OneComparisonWins, hfirst]
  · simp [theorem12OneComparisonWins, hfirst, hsecond]

/--
Integrating a response-table answer over an independently sampled displayed
pair gives exactly the source's one-comparison report expectation.
-/
theorem theorem2UserResponse_pairLabel_pmfExp_wins_eq_oneComparison
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {sampling : PMF Alternative} {preference : PairwisePreference PUnit Alternative}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (alternative : Alternative) :
    pmfPairExp responseLaw (theorem2UserPairLabelLaw sampling) (fun response pair =>
      theorem12OneComparisonWins alternative
        (pair, response pair.1 pair.2)) =
      pmfExp (theorem12OneComparisonReportLaw sampling preference)
        (theorem12OneComparisonWins alternative) := by
  calc
    pmfPairExp responseLaw (theorem2UserPairLabelLaw sampling) (fun response pair =>
        theorem12OneComparisonWins alternative
          (pair, response pair.1 pair.2)) =
      pmfPairExp (theorem2UserPairLabelLaw sampling) responseLaw (fun pair response =>
        theorem12OneComparisonWins alternative
          (pair, response pair.1 pair.2)) :=
        AppliedModelingLib.pmfPairExp_swap _ _ _
    _ = pmfPairExp sampling sampling (fun first second =>
        pmfExp responseLaw (fun response =>
          theorem12OneComparisonWins alternative
            ((first, second), response first second))) := by
        unfold theorem2UserPairLabelLaw
        unfold pmfPairExp
        rw [pmfExp_pmfProd_eq_pairExp]
        rfl
    _ = pmfPairExp sampling sampling (fun first second =>
        pmfExp (theorem12BernoulliReport
          (preference.prob PUnit.unit first second)
          (preference.nonneg PUnit.unit first second)
          (preference.le_one PUnit.unit first second))
          (fun outcome => theorem12OneComparisonWins alternative ((first, second), outcome))) := by
        unfold pmfPairExp
        apply pmfExp_congr
        intro first
        apply pmfExp_congr
        intro second
        change pmfExp responseLaw (fun response =>
          theorem12OneComparisonWins alternative
            ((first, second), response first second)) =
          pmfExp (theorem12BernoulliReport
            (preference.prob PUnit.unit first second)
            (preference.nonneg PUnit.unit first second)
            (preference.le_one PUnit.unit first second))
            (fun outcome => theorem12OneComparisonWins alternative ((first, second), outcome))
        exact (theorem2UserResponse_pmfExp_wins_eq_oneComparison hcalibrated
          alternative first second).trans
          (theorem12_pmfExp_bernoulli_apply
            (preference.prob PUnit.unit first second)
            (preference.nonneg PUnit.unit first second)
            (preference.le_one PUnit.unit first second)
            (fun outcome => theorem12OneComparisonWins alternative ((first, second), outcome))).symm
    _ = pmfExp (theorem12OneComparisonReportLaw sampling preference)
        (theorem12OneComparisonWins alternative) := by
        unfold theorem12OneComparisonReportLaw
        rw [pmfExp_bind]
        apply pmfExp_congr
        intro first
        rw [pmfExp_bind]
        apply pmfExp_congr
        intro second
        rw [pmfExp_map]

/--
Response-table correlation does not affect Borda comparison incidences: after
integrating over an independently sampled pair, their expectation is the
source's one-comparison incidence expectation.
-/
theorem theorem2UserResponse_pairLabel_pmfExp_incidences_eq_oneComparison
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative)
    (alternative : Alternative) :
    pmfPairExp responseLaw (theorem2UserPairLabelLaw sampling) (fun response pair =>
      theorem12OneComparisonIncidences alternative
        (pair, response pair.1 pair.2)) =
      pmfExp (theorem12OneComparisonReportLaw sampling preference)
        (theorem12OneComparisonIncidences alternative) := by
  calc
    pmfPairExp responseLaw (theorem2UserPairLabelLaw sampling) (fun response pair =>
        theorem12OneComparisonIncidences alternative
          (pair, response pair.1 pair.2)) =
      pmfPairExp (theorem2UserPairLabelLaw sampling) responseLaw (fun pair response =>
        theorem12OneComparisonIncidences alternative
          (pair, response pair.1 pair.2)) :=
        AppliedModelingLib.pmfPairExp_swap _ _ _
    _ = pmfPairExp sampling sampling (fun first second =>
        pmfExp responseLaw (fun response =>
          theorem12OneComparisonIncidences alternative
            ((first, second), response first second))) := by
        unfold theorem2UserPairLabelLaw
        unfold pmfPairExp
        rw [pmfExp_pmfProd_eq_pairExp]
        rfl
    _ = pmfPairExp sampling sampling (fun first second =>
        theorem12OneComparisonIncidences alternative ((first, second), true)) := by
        unfold pmfPairExp
        apply pmfExp_congr
        intro first
        apply pmfExp_congr
        intro second
        change pmfExp responseLaw (fun response =>
          theorem12OneComparisonIncidences alternative
            ((first, second), response first second)) =
          theorem12OneComparisonIncidences alternative ((first, second), true)
        rw [show (fun response : theorem2UserResponseTable Alternative =>
            theorem12OneComparisonIncidences alternative
              ((first, second), response first second)) =
            fun _ => theorem12OneComparisonIncidences alternative ((first, second), true) by
              funext response
              rfl]
        rw [pmfExp_const]
    _ = pmfExp (theorem12OneComparisonReportLaw sampling preference)
        (theorem12OneComparisonIncidences alternative) := by
        unfold theorem12OneComparisonReportLaw
        rw [pmfExp_bind]
        apply pmfExp_congr
        intro first
        rw [pmfExp_bind]
        apply pmfExp_congr
        intro second
        rw [pmfExp_map]
        rw [show (fun outcome : Bool => theorem12OneComparisonIncidences alternative
            ((first, second), outcome)) =
            fun _ => theorem12OneComparisonIncidences alternative ((first, second), true) by
              funext outcome
              rfl]
        rw [pmfExp_const]

/--
Every coordinate of a source-faithful user bundle has the paper's declared
one-comparison Borda-win expectation, despite arbitrary correlation among that
user's response-table entries.
-/
theorem theorem2UserBatchLaw_pmfExp_coordinateWins
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {sampling : PMF Alternative} {preference : PairwisePreference PUnit Alternative}
    {comparisonsPerUser : ℕ}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (alternative : Alternative) (position : Fin comparisonsPerUser) :
    pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser) (fun report =>
      theorem12OneComparisonWins alternative (report position)) =
      pmfExp (theorem12OneComparisonReportLaw sampling preference)
        (theorem12OneComparisonWins alternative) := by
  unfold theorem2UserBatchLaw
  rw [pmfExp_map]
  rw [pmfExp_pmfProd_eq_pairExp]
  rw [AppliedModelingLib.pmfPairExp_swap]
  let coordinateExpectation : Alternative × Alternative → ℝ := fun pair =>
    pmfExp responseLaw (fun response =>
      theorem12OneComparisonWins alternative
        (pair, response pair.1 pair.2))
  change pmfExp
    (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
      (theorem2UserPairLabelLaw sampling))
    (fun labels => coordinateExpectation (labels position)) = _
  rw [pmfExp_pmfProduct_eval (theorem2UserPairLabelLaw sampling) position]
  change pmfPairExp (theorem2UserPairLabelLaw sampling) responseLaw (fun pair response =>
    theorem12OneComparisonWins alternative
      (pair, response pair.1 pair.2)) = _
  exact (AppliedModelingLib.pmfPairExp_swap responseLaw (theorem2UserPairLabelLaw sampling)
    (fun response pair => theorem12OneComparisonWins alternative
      (pair, response pair.1 pair.2))).symm.trans
    (theorem2UserResponse_pairLabel_pmfExp_wins_eq_oneComparison
      (sampling := sampling) hcalibrated alternative)

/-- Each user-bundle coordinate has the source's one-comparison incidence expectation. -/
theorem theorem2UserBatchLaw_pmfExp_coordinateIncidences
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {sampling : PMF Alternative} {preference : PairwisePreference PUnit Alternative}
    {comparisonsPerUser : ℕ}
    (alternative : Alternative) (position : Fin comparisonsPerUser) :
    pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser) (fun report =>
      theorem12OneComparisonIncidences alternative (report position)) =
      pmfExp (theorem12OneComparisonReportLaw sampling preference)
        (theorem12OneComparisonIncidences alternative) := by
  unfold theorem2UserBatchLaw
  rw [pmfExp_map]
  rw [pmfExp_pmfProd_eq_pairExp]
  rw [AppliedModelingLib.pmfPairExp_swap]
  let coordinateExpectation : Alternative × Alternative → ℝ := fun pair =>
    pmfExp responseLaw (fun response =>
      theorem12OneComparisonIncidences alternative
        (pair, response pair.1 pair.2))
  change pmfExp
    (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
      (theorem2UserPairLabelLaw sampling))
    (fun labels => coordinateExpectation (labels position)) = _
  rw [pmfExp_pmfProduct_eval (theorem2UserPairLabelLaw sampling) position]
  change pmfPairExp (theorem2UserPairLabelLaw sampling) responseLaw (fun pair response =>
    theorem12OneComparisonIncidences alternative
      (pair, response pair.1 pair.2)) = _
  exact (AppliedModelingLib.pmfPairExp_swap responseLaw (theorem2UserPairLabelLaw sampling)
    (fun response pair => theorem12OneComparisonIncidences alternative
      (pair, response pair.1 pair.2))).symm.trans
    (theorem2UserResponse_pairLabel_pmfExp_incidences_eq_oneComparison
      responseLaw sampling preference alternative)

/--
The expected Borda wins of one literal source user are the number of that
user's sampled comparisons times the one-comparison Borda expectation.
-/
theorem theorem2UserBatchLaw_pmfExp_bordaWins
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {sampling : PMF Alternative} {preference : PairwisePreference PUnit Alternative}
    (comparisonsPerUser : ℕ)
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (alternative : Alternative) :
    pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser)
      (theorem2UserBatchBordaWins alternative) =
      (comparisonsPerUser : ℝ) *
        pmfExp (theorem12OneComparisonReportLaw sampling preference)
          (theorem12OneComparisonWins alternative) := by
  unfold theorem2UserBatchBordaWins
  rw [pmfExp_univ_sum]
  calc
    (∑ position : Fin comparisonsPerUser,
        pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser) (fun report =>
          theorem12OneComparisonWins alternative (report position))) =
      ∑ _position : Fin comparisonsPerUser,
        pmfExp (theorem12OneComparisonReportLaw sampling preference)
          (theorem12OneComparisonWins alternative) := by
        apply Finset.sum_congr rfl
        intro position _
        exact theorem2UserBatchLaw_pmfExp_coordinateWins hcalibrated alternative position
    _ = (comparisonsPerUser : ℝ) *
        pmfExp (theorem12OneComparisonReportLaw sampling preference)
          (theorem12OneComparisonWins alternative) := by
        simp [nsmul_eq_mul]

/--
The expected comparison-incidence count of one literal source user is twice
the sampling mass of the alternative times that user's comparison count.
-/
theorem theorem2UserBatchLaw_pmfExp_bordaIncidences
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {sampling : PMF Alternative} {preference : PairwisePreference PUnit Alternative}
    (comparisonsPerUser : ℕ) (alternative : Alternative) :
    pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser)
      (theorem2UserBatchBordaIncidences alternative) =
      (comparisonsPerUser : ℝ) * 2 * (sampling alternative).toReal := by
  unfold theorem2UserBatchBordaIncidences
  rw [pmfExp_univ_sum]
  calc
    (∑ position : Fin comparisonsPerUser,
        pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser) (fun report =>
          theorem12OneComparisonIncidences alternative (report position))) =
      ∑ _position : Fin comparisonsPerUser,
        pmfExp (theorem12OneComparisonReportLaw sampling preference)
          (theorem12OneComparisonIncidences alternative) := by
        apply Finset.sum_congr rfl
        intro position _
        exact theorem2UserBatchLaw_pmfExp_coordinateIncidences alternative position
    _ = ∑ _position : Fin comparisonsPerUser, 2 * (sampling alternative).toReal := by
        apply Finset.sum_congr rfl
        intro position _
        exact theorem12OneComparisonIncidences_pmfExp sampling preference alternative
    _ = (comparisonsPerUser : ℝ) * 2 * (sampling alternative).toReal := by
        simp [nsmul_eq_mul]
        ring

/-- One user batch has nonnegative Borda win counts. -/
theorem theorem2UserBatchBordaWins_nonneg
    {Alternative : Type*} [DecidableEq Alternative] {comparisonsPerUser : ℕ}
    (alternative : Alternative) (report : theorem2UserBatchReport Alternative comparisonsPerUser) :
    0 ≤ theorem2UserBatchBordaWins alternative report := by
  unfold theorem2UserBatchBordaWins
  exact Finset.sum_nonneg fun position _ =>
    theorem12OneComparisonWins_nonneg alternative (report position)

/-- One user batch's Borda wins never exceed its comparison incidences. -/
theorem theorem2UserBatchBordaWins_le_incidences
    {Alternative : Type*} [DecidableEq Alternative] {comparisonsPerUser : ℕ}
    (alternative : Alternative) (report : theorem2UserBatchReport Alternative comparisonsPerUser) :
    theorem2UserBatchBordaWins alternative report ≤
      theorem2UserBatchBordaIncidences alternative report := by
  unfold theorem2UserBatchBordaWins theorem2UserBatchBordaIncidences
  exact Finset.sum_le_sum fun position _ =>
    theorem12OneComparisonWins_le_incidences alternative (report position)

/--
The normalized population Borda score calibrates the literal user-batch win
and incidence expectations. This is the exact source-to-count bridge needed
before concentration is applied across independently sampled users.
-/
theorem theorem2UserBatchLaw_borda_calibrated
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {sampling : PMF Alternative} {preference : PairwisePreference PUnit Alternative}
    (comparisonsPerUser : ℕ)
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (alternative : Alternative) :
    pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser)
      (theorem2UserBatchBordaWins alternative) =
      pairwiseBordaScore sampling preference alternative *
        pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser)
          (theorem2UserBatchBordaIncidences
            (comparisonsPerUser := comparisonsPerUser) alternative) := by
  rw [theorem2UserBatchLaw_pmfExp_bordaWins (preference := preference)
      comparisonsPerUser hcalibrated alternative,
    theorem12OneComparisonWins_pmfExp sampling preference alternative,
    theorem2UserBatchLaw_pmfExp_bordaIncidences (preference := preference)]
  ring

/--
For the literal source model with a fixed positive number of comparisons per
user, iid user batches select every strict population Borda winner with
probability tending to one. The only independence used here is across users;
every within-user response-table correlation remains intact.
-/
theorem theorem2_iidUserBatchBordaFailure_tendsto_zero_of_strictBordaWinner
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative)
    (comparisonsPerUser : ℕ) (hcomparisons : 0 < comparisonsPerUser)
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (winner : Alternative) (hsampling_pos : ∀ alternative, 0 < (sampling alternative).toReal)
    (hstrict : ∀ ordinary, ordinary ≠ winner →
      pairwiseBordaScore sampling preference ordinary < pairwiseBordaScore sampling preference winner) :
    Filter.Tendsto
      (fun users => pmfProb (theorem12IidBordaReportBatchLaw
        (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser) users)
        (fun sample => theorem12IidEmpiricalBordaFailure theorem2UserBatchBordaWins
          theorem2UserBatchBordaIncidences winner sample))
      Filter.atTop (nhds 0) := by
  apply theorem12_iidEmpiricalBordaFailure_tendsto_zero_of_calibrated_strict_winner
    (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser)
    theorem2UserBatchBordaWins theorem2UserBatchBordaIncidences
    (pairwiseBordaScore sampling preference) winner
  · intro alternative report
    exact theorem2UserBatchBordaWins_nonneg alternative report
  · intro alternative report
    exact theorem2UserBatchBordaWins_le_incidences alternative report
  · intro alternative
    unfold pairwiseBordaScore
    exact pmfExp_nonneg_of_forall_nonneg sampling _
      (fun opponent => preference.nonneg PUnit.unit alternative opponent)
  · intro alternative
    exact theorem2UserBatchLaw_borda_calibrated comparisonsPerUser hcalibrated alternative
  · intro alternative
    rw [theorem2UserBatchLaw_pmfExp_bordaIncidences (preference := preference)]
    exact mul_pos
      (mul_pos (by exact_mod_cast hcomparisons) (by norm_num))
      (hsampling_pos alternative)
  · exact hstrict

end GolzHaghtalabYang2025Distortion
