import GolzHaghtalabYang2025Distortion.Lemma10FiniteSample

/-!
# Normalized Borda ingredients for Appendix D, Lemma 11

This module works directly with the source's iid user-report batches.  One
user may have arbitrarily correlated answers across its `d` displayed pairs;
only different users are independent.
-/

namespace GolzHaghtalabYang2025Distortion

open scoped BigOperators

open AppliedModelingLib
open AppliedModelingLib.Alignment.Welfare
open AppliedModelingLib.Learning.HumanFeedback
open AppliedModelingLib.Probability

/--
One user's raw Borda-win contribution for a fixed distinct unordered pair,
centered at its literal source expectation.  Unlike Lemma 10's ratio
numerator, this centers the raw win count itself; it is the quantity summed
over opponents in the source proof of Lemma 11.
-/
def theorem11UserUnorderedPairWinCentered
    {Alternative : Type*} [DecidableEq Alternative] {comparisonsPerUser : ℕ}
    (first second : Alternative) (winProbability : ℝ)
    (response : theorem2UserResponseTable Alternative)
    (labels : Fin comparisonsPerUser → Alternative × Alternative)
    (pairIncidenceProbability : ℝ) : ℝ :=
  theorem10UserUnorderedPairWins first second response labels -
    (comparisonsPerUser : ℝ) * winProbability * pairIncidenceProbability

/--
For one displayed label, the Borda win of `alternative` is assigned to the
unique unordered pair consisting of `alternative` and its displayed opponent.
When the label is `(alternative, alternative)`, that pair is counted once,
matching the source's diagonal Borda convention.
-/
theorem theorem11_oneComparisonWins_eq_sum_unorderedPairContributions
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (alternative : Alternative) (response : theorem2UserResponseTable Alternative)
    (label : Alternative × Alternative) :
    theorem12OneComparisonWins alternative
      (label, response label.1 label.2) =
      ∑ opponent : Alternative,
        theorem10UnorderedPairIndicator alternative opponent label *
          theorem12OneComparisonWins alternative
            (label, response label.1 label.2) := by
  rcases label with ⟨first, second⟩
  by_cases hfirst : first = alternative <;> by_cases hsecond : second = alternative
  · subst first
    subst second
    simp [theorem10UnorderedPairIndicator, theorem12OneComparisonWins]
  · subst first
    simp [theorem10UnorderedPairIndicator, theorem12OneComparisonWins, hsecond]
  · subst second
    simp [theorem10UnorderedPairIndicator, theorem12OneComparisonWins, hfirst]
  · simp [theorem10UnorderedPairIndicator, theorem12OneComparisonWins, hfirst, hsecond]

/--
The literal source user-batch Borda count decomposes into its raw unordered
pair contributions.  This is the summation identity used before the
variance-sensitive opponent union in Appendix D, Lemma 11.
-/
theorem theorem11_userLatentBordaWins_eq_sum_unorderedPairWins
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {comparisonsPerUser : ℕ}
    (alternative : Alternative) (response : theorem2UserResponseTable Alternative)
    (labels : Fin comparisonsPerUser → Alternative × Alternative) :
    theorem2UserBatchBordaWins alternative
      (fun position => ((labels position), response (labels position).1 (labels position).2)) =
      ∑ opponent : Alternative,
        theorem10UserUnorderedPairWins alternative opponent response labels := by
  unfold theorem2UserBatchBordaWins theorem10UserUnorderedPairWins
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro position _
  exact theorem11_oneComparisonWins_eq_sum_unorderedPairContributions alternative response
    (labels position)

/-- Indicator of a literal diagonal display `(alternative, alternative)`. -/
def theorem11DiagonalLabelIndicator
    {Alternative : Type*} [DecidableEq Alternative]
    (alternative : Alternative) : Alternative × Alternative → ℝ
  | (first, second) => if first = alternative ∧ second = alternative then 1 else 0

/-- The diagonal part of one user's raw Borda count. -/
def theorem11UserDiagonalBordaWins
    {Alternative : Type*} [DecidableEq Alternative] {comparisonsPerUser : ℕ}
    (alternative : Alternative)
    (labels : Fin comparisonsPerUser → Alternative × Alternative) : ℝ :=
  ∑ position, theorem11DiagonalLabelIndicator alternative (labels position)

/-- A literal self-comparison supplies one Borda win, independently of its recorded bit. -/
theorem theorem10UserUnorderedPairWins_self_eq_diagonalBordaWins
    {Alternative : Type*} [DecidableEq Alternative] {comparisonsPerUser : ℕ}
    (alternative : Alternative) (response : theorem2UserResponseTable Alternative)
    (labels : Fin comparisonsPerUser → Alternative × Alternative) :
    theorem10UserUnorderedPairWins alternative alternative response labels =
      theorem11UserDiagonalBordaWins alternative labels := by
  unfold theorem10UserUnorderedPairWins theorem11UserDiagonalBordaWins
    theorem11DiagonalLabelIndicator
  apply Finset.sum_congr rfl
  intro position _
  rcases labels position with ⟨first, second⟩
  by_cases hfirst : first = alternative <;> by_cases hsecond : second = alternative
  · subst first
    subst second
    cases hresponse : response alternative alternative <;>
      simp [theorem10UnorderedPairIndicator, theorem12OneComparisonWins]
  · subst first
    simp [theorem10UnorderedPairIndicator, theorem12OneComparisonWins, hsecond]
  · subst second
    simp [theorem10UnorderedPairIndicator, theorem12OneComparisonWins, hfirst]
  · simp [theorem10UnorderedPairIndicator, theorem12OneComparisonWins, hfirst, hsecond]

/-- One iid pair label is diagonal at `alternative` with probability `μ(alternative)^2`. -/
theorem theorem11_pmfExp_diagonalLabelIndicator
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (alternative : Alternative) :
    pmfExp (theorem2UserPairLabelLaw sampling)
      (theorem11DiagonalLabelIndicator alternative) =
      (sampling alternative).toReal ^ 2 := by
  unfold theorem2UserPairLabelLaw
  rw [pmfExp_pmfProd_eq_pairExp]
  rw [show (fun first second => theorem11DiagonalLabelIndicator alternative (first, second)) =
      fun first second =>
        (if first = alternative then (1 : ℝ) else 0) *
          if second = alternative then 1 else 0 by
        funext first second
        by_cases hfirst : first = alternative <;> by_cases hsecond : second = alternative <;>
          simp [theorem11DiagonalLabelIndicator, hfirst, hsecond]]
  rw [pmfPairExp_mul_separable, theorem12_pmfExp_eq_indicator]
  ring

/-- The mean diagonal Borda contribution of one user is `d μ(alternative)^2`. -/
theorem theorem11_pmfExp_userDiagonalBordaWins
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (comparisonsPerUser : ℕ) (alternative : Alternative) :
    pmfExp
      (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
        (theorem2UserPairLabelLaw sampling))
      (theorem11UserDiagonalBordaWins alternative) =
      (comparisonsPerUser : ℝ) * (sampling alternative).toReal ^ 2 := by
  unfold theorem11UserDiagonalBordaWins
  rw [pmfExp_univ_sum]
  calc
    (∑ position : Fin comparisonsPerUser,
        pmfExp
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))
          (fun labels => theorem11DiagonalLabelIndicator alternative (labels position))) =
        ∑ _position : Fin comparisonsPerUser,
          pmfExp (theorem2UserPairLabelLaw sampling)
            (theorem11DiagonalLabelIndicator alternative) := by
          apply Finset.sum_congr rfl
          intro position _
          exact pmfExp_pmfProduct_eval (theorem2UserPairLabelLaw sampling) position
            (theorem11DiagonalLabelIndicator alternative)
    _ = ∑ _position : Fin comparisonsPerUser, (sampling alternative).toReal ^ 2 := by
          apply Finset.sum_congr rfl
          intro position _
          exact theorem11_pmfExp_diagonalLabelIndicator sampling alternative
    _ = (comparisonsPerUser : ℝ) * (sampling alternative).toReal ^ 2 := by
          simp [nsmul_eq_mul]

/-- The response-table product law leaves the diagonal-label expectation unchanged. -/
theorem theorem11_pmfExp_sourceUserDiagonalBordaWins
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (comparisonsPerUser : ℕ) (alternative : Alternative) :
    pmfExp
      (pmfProd responseLaw
        (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
          (theorem2UserPairLabelLaw sampling)))
      (fun source => theorem11UserDiagonalBordaWins alternative source.2) =
      (comparisonsPerUser : ℝ) * (sampling alternative).toReal ^ 2 := by
  rw [pmfExp_pmfProd_eq_pairExp, pmfPairExp_ignore_left]
  exact theorem11_pmfExp_userDiagonalBordaWins sampling comparisonsPerUser alternative

/-- A diagonal Borda count is nonnegative. -/
theorem theorem11UserDiagonalBordaWins_nonneg
    {Alternative : Type*} [DecidableEq Alternative] {comparisonsPerUser : ℕ}
    (alternative : Alternative)
    (labels : Fin comparisonsPerUser → Alternative × Alternative) :
    0 ≤ theorem11UserDiagonalBordaWins alternative labels := by
  unfold theorem11UserDiagonalBordaWins
  exact Finset.sum_nonneg fun position _ => by
    rcases labels position with ⟨first, second⟩
    simp only [theorem11DiagonalLabelIndicator]
    split <;> norm_num

/-- A diagonal Borda count has at most one contribution per displayed pair. -/
theorem theorem11UserDiagonalBordaWins_le_comparisons
    {Alternative : Type*} [DecidableEq Alternative] {comparisonsPerUser : ℕ}
    (alternative : Alternative)
    (labels : Fin comparisonsPerUser → Alternative × Alternative) :
    theorem11UserDiagonalBordaWins alternative labels ≤ comparisonsPerUser := by
  unfold theorem11UserDiagonalBordaWins
  calc
    (∑ position, theorem11DiagonalLabelIndicator alternative (labels position)) ≤
        ∑ _position : Fin comparisonsPerUser, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro position _
          rcases labels position with ⟨first, second⟩
          simp only [theorem11DiagonalLabelIndicator]
          split <;> norm_num
    _ = comparisonsPerUser := by simp [nsmul_eq_mul]

/-- The square of the diagonal count is at most `d` times that count. -/
theorem theorem11UserDiagonalBordaWins_sq_le_comparisons_mul
    {Alternative : Type*} [DecidableEq Alternative] {comparisonsPerUser : ℕ}
    (alternative : Alternative)
    (labels : Fin comparisonsPerUser → Alternative × Alternative) :
    (theorem11UserDiagonalBordaWins alternative labels) ^ 2 ≤
      (comparisonsPerUser : ℝ) * theorem11UserDiagonalBordaWins alternative labels := by
  have hnonneg := theorem11UserDiagonalBordaWins_nonneg alternative labels
  have hle := theorem11UserDiagonalBordaWins_le_comparisons alternative labels
  nlinarith

/-- The diagonal Borda contribution centered at its literal label expectation. -/
def theorem11UserDiagonalBordaWinsCentered
    {Alternative : Type*} [DecidableEq Alternative] {comparisonsPerUser : ℕ}
    (sampling : PMF Alternative) (alternative : Alternative)
    (labels : Fin comparisonsPerUser → Alternative × Alternative) : ℝ :=
  theorem11UserDiagonalBordaWins alternative labels -
    (comparisonsPerUser : ℝ) * (sampling alternative).toReal ^ 2

/-- The centered diagonal Borda contribution has mean zero on the source law. -/
theorem theorem11_pmfExp_sourceUserDiagonalBordaWinsCentered_eq_zero
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (comparisonsPerUser : ℕ) (alternative : Alternative) :
    pmfExp
      (pmfProd responseLaw
        (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
          (theorem2UserPairLabelLaw sampling)))
      (fun source => theorem11UserDiagonalBordaWinsCentered sampling alternative source.2) = 0 := by
  unfold theorem11UserDiagonalBordaWinsCentered
  rw [pmfExp_sub, pmfExp_const]
  rw [theorem11_pmfExp_sourceUserDiagonalBordaWins responseLaw sampling comparisonsPerUser]
  ring

/--
The diagonal centered second moment is at most `d² μ(alternative)²`. This
deliberately uses only the bounded diagonal count; it is enough for the
source's final `min {1, d μ_min²}` rate after normalization.
-/
theorem theorem11_pmfExp_sourceUserDiagonalBordaWinsCentered_sq_le
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (comparisonsPerUser : ℕ) (alternative : Alternative) :
    pmfExp
      (pmfProd responseLaw
        (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
          (theorem2UserPairLabelLaw sampling)))
      (fun source => (theorem11UserDiagonalBordaWinsCentered sampling alternative source.2) ^ 2) ≤
      (comparisonsPerUser : ℝ) ^ 2 * (sampling alternative).toReal ^ 2 := by
  let sourceLaw := pmfProd responseLaw
    (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
      (theorem2UserPairLabelLaw sampling))
  let diagonal : (theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative)) → ℝ := fun source =>
    theorem11UserDiagonalBordaWins alternative source.2
  let centered : (theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative)) → ℝ := fun source =>
    theorem11UserDiagonalBordaWinsCentered sampling alternative source.2
  let mean : ℝ := (comparisonsPerUser : ℝ) * (sampling alternative).toReal ^ 2
  have hmean : pmfExp sourceLaw diagonal = mean := by
    simpa [sourceLaw, diagonal, mean] using
      (theorem11_pmfExp_sourceUserDiagonalBordaWins responseLaw sampling
        comparisonsPerUser alternative)
  have hcentered_sq : pmfExp sourceLaw (fun source => centered source ^ 2) =
      pmfVariance sourceLaw diagonal := by
    unfold pmfVariance
    apply pmfExp_congr
    intro source
    dsimp [centered, diagonal, theorem11UserDiagonalBordaWinsCentered]
    rw [hmean]
  have hdiagonal_sq : pmfExp sourceLaw (fun source => diagonal source ^ 2) ≤
      (comparisonsPerUser : ℝ) * pmfExp sourceLaw diagonal := by
    calc
      pmfExp sourceLaw (fun source => diagonal source ^ 2) ≤
          pmfExp sourceLaw (fun source => (comparisonsPerUser : ℝ) * diagonal source) := by
            apply pmfExp_le_pmfExp_of_forall_le
            intro source
            exact theorem11UserDiagonalBordaWins_sq_le_comparisons_mul alternative source.2
      _ = (comparisonsPerUser : ℝ) * pmfExp sourceLaw diagonal := by
            rw [pmfExp_const_mul]
  calc
    pmfExp sourceLaw (fun source => centered source ^ 2) = pmfVariance sourceLaw diagonal :=
      hcentered_sq
    _ = pmfExp sourceLaw (fun source => diagonal source ^ 2) -
        (pmfExp sourceLaw diagonal) ^ 2 :=
      pmfVariance_eq_exp_sq_sub_sq_exp sourceLaw diagonal
    _ ≤ pmfExp sourceLaw (fun source => diagonal source ^ 2) :=
      sub_le_self _ (sq_nonneg _)
    _ ≤ (comparisonsPerUser : ℝ) * pmfExp sourceLaw diagonal := hdiagonal_sq
    _ = (comparisonsPerUser : ℝ) ^ 2 * (sampling alternative).toReal ^ 2 := by
      rw [hmean]
      ring

/-- A centered diagonal Borda contribution is bounded by one user's `d` displays. -/
theorem theorem11UserDiagonalBordaWinsCentered_abs_le_comparisons
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (comparisonsPerUser : ℕ) (alternative : Alternative)
    (labels : Fin comparisonsPerUser → Alternative × Alternative) :
    |theorem11UserDiagonalBordaWinsCentered sampling alternative labels| ≤ comparisonsPerUser := by
  let diagonal := theorem11UserDiagonalBordaWins alternative labels
  let mean : ℝ := (comparisonsPerUser : ℝ) * (sampling alternative).toReal ^ 2
  have hdiagonal_nonneg : 0 ≤ diagonal := by
    exact theorem11UserDiagonalBordaWins_nonneg alternative labels
  have hdiagonal_le : diagonal ≤ comparisonsPerUser := by
    exact theorem11UserDiagonalBordaWins_le_comparisons alternative labels
  have hmass_nonneg : 0 ≤ (sampling alternative).toReal := ENNReal.toReal_nonneg
  have hmass_le : (sampling alternative).toReal ≤ 1 :=
    pmf_apply_toReal_le_one sampling alternative
  have hmass_sq_le : (sampling alternative).toReal ^ 2 ≤ 1 := by nlinarith
  have hmean_nonneg : 0 ≤ mean := by positivity
  have hmean_le : mean ≤ comparisonsPerUser := by
    dsimp [mean]
    nlinarith
  change |diagonal - mean| ≤ comparisonsPerUser
  rw [abs_le]
  constructor <;> linarith

/--
Two-sided iid Bernstein tail for the diagonal raw Borda contribution.  The
statistic is independent of the response table, so this preserves arbitrary
within-user response correlation exactly as in the source model.
-/
theorem theorem11_iidUserDiagonalBordaWinsCentered_absTail_bernstein
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (alternative : Alternative) (cutoff : ℝ) (hcutoff_nonneg : 0 ≤ cutoff)
    (hden_pos : 0 < (users : ℝ) *
      ((comparisonsPerUser : ℝ) ^ 2 * (sampling alternative).toReal ^ 2) +
      (comparisonsPerUser : ℝ) * cutoff) :
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample => cutoff ≤ |∑ user,
        theorem11UserDiagonalBordaWinsCentered sampling alternative (sample user).2|) ≤
      2 * Real.exp (-cutoff ^ 2 /
        (4 * ((users : ℝ) *
          ((comparisonsPerUser : ℝ) ^ 2 * (sampling alternative).toReal ^ 2) +
          (comparisonsPerUser : ℝ) * cutoff))) := by
  let sourceLaw := pmfProd responseLaw
    (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
      (theorem2UserPairLabelLaw sampling))
  let statistic : (theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative)) → ℝ := fun source =>
    theorem11UserDiagonalBordaWinsCentered sampling alternative source.2
  let varianceBound : ℝ :=
    (comparisonsPerUser : ℝ) ^ 2 * (sampling alternative).toReal ^ 2
  letI : MeasurableSpace (theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative)) := ⊤
  have hmean : pmfExp sourceLaw statistic = 0 := by
    simpa [sourceLaw, statistic] using
      (theorem11_pmfExp_sourceUserDiagonalBordaWinsCentered_eq_zero responseLaw sampling
        comparisonsPerUser alternative)
  have hvariance : pmfExp sourceLaw (fun source => statistic source ^ 2) ≤ varianceBound := by
    simpa [sourceLaw, statistic, varianceBound] using
      (theorem11_pmfExp_sourceUserDiagonalBordaWinsCentered_sq_le responseLaw sampling
        comparisonsPerUser alternative)
  have hvariance_nonneg : 0 ≤ varianceBound := by positivity
  have hbound : ∀ source, |statistic source| ≤ (comparisonsPerUser : ℝ) := by
    intro source
    simpa [statistic] using
      (theorem11UserDiagonalBordaWinsCentered_abs_le_comparisons sampling comparisonsPerUser
        alternative source.2)
  have htail := pmfProb_pmfProduct_centeredBoundedSum_abs_ge_le_bernstein
    (ι := Fin users)
    (α := theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative))
    sourceLaw statistic varianceBound (comparisonsPerUser : ℝ) cutoff hmean hvariance hbound
    hvariance_nonneg (by positivity) hcutoff_nonneg
    (by simpa [varianceBound, Fintype.card_fin] using hden_pos)
  simpa [sourceLaw, statistic, varianceBound, Fintype.card_fin] using htail

/-- Rebracket one ordered pair at each index as two Boolean-indexed iid draws. -/
private def theorem11PairLabelsEquiv (Index Alternative : Type*) :
    (Index → Alternative × Alternative) ≃ (Index → Bool → Alternative) where
  toFun labels index side := if side then (labels index).2 else (labels index).1
  invFun labels index := (labels index false, labels index true)
  left_inv labels := by
    funext index
    change ((labels index).1, (labels index).2) = labels index
    cases labels index
    rfl
  right_inv labels := by
    funext index side
    cases side <;> simp

/--
An iid product of ordered pair labels is equivalent, for finite expectations,
to an iid product of their two Boolean-indexed coordinates.  This is the
probability-space bridge behind Lemma 11's literal `2nd` incidence count.
-/
private theorem theorem11_pmfExp_pairLabels_rebracket
    {Index Alternative : Type*} [Fintype Index] [DecidableEq Index]
    [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (F : (Index → Bool → Alternative) → ℝ) :
    pmfExp (pmfProduct Index (Alternative × Alternative) (pmfProd sampling sampling))
      (fun labels => F (theorem11PairLabelsEquiv Index Alternative labels)) =
      pmfExp (pmfProduct Index (Bool → Alternative)
        (pmfProduct Bool Alternative sampling)) F := by
  classical
  let e := theorem11PairLabelsEquiv Index Alternative
  unfold pmfExp
  calc
    ∑ labels : Index → Alternative × Alternative,
        (pmfProduct Index (Alternative × Alternative) (pmfProd sampling sampling) labels).toReal *
          F (e labels) =
        ∑ labels : Index → Bool → Alternative,
          (pmfProduct Index (Alternative × Alternative) (pmfProd sampling sampling)
            (e.symm labels)).toReal * F labels := by
          simpa [e] using
            (Equiv.sum_comp e.symm
              (fun labels : Index → Alternative × Alternative =>
                (pmfProduct Index (Alternative × Alternative) (pmfProd sampling sampling)
                  labels).toReal * F (e labels))).symm
    _ = ∑ labels : Index → Bool → Alternative,
          (pmfProduct Index (Bool → Alternative)
            (pmfProduct Bool Alternative sampling) labels).toReal * F labels := by
          refine Finset.sum_congr rfl ?_
          intro labels _
          congr 1
          rw [pmfProduct_apply_toReal, pmfProduct_apply_toReal]
          apply Finset.prod_congr rfl
          intro index _
          simp [e, theorem11PairLabelsEquiv]
          ring

/-- Grouping literal user-batch incidences merely rebrackets the iid pair labels. -/
private theorem theorem11_iidUserBordaIncidences_eq_flattenedPair
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {users comparisonsPerUser : ℕ}
    (alternative : Alternative)
    (labels : Fin users → Fin comparisonsPerUser → Alternative × Alternative) :
    theorem12EmpiricalBordaIncidences theorem2UserBatchBordaIncidences alternative
      (fun user position => ((labels user position), false)) =
      ∑ index : Fin users × Fin comparisonsPerUser,
        theorem12OneComparisonIncidences alternative (labels index.1 index.2, false) := by
  unfold theorem12EmpiricalBordaIncidences finiteIidScoreSum
    theorem2UserBatchBordaIncidences
  simpa using
    (Fintype.sum_prod_type' (fun user position =>
      theorem12OneComparisonIncidences alternative (labels user position, false))).symm

/-- Rebracketing an ordered pair turns its two incidences into two equality indicators. -/
private theorem theorem11_flatPairBordaIncidences_eq_flatAlternativeIndicators
    {Index Alternative : Type*} [Fintype Index] [DecidableEq Index]
    [DecidableEq Alternative]
    (alternative : Alternative) (labels : Index → Alternative × Alternative) :
    (∑ index, theorem12OneComparisonIncidences alternative (labels index, false)) =
      ∑ index : Index × Bool,
        if theorem11PairLabelsEquiv Index Alternative labels index.1 index.2 = alternative
          then (1 : ℝ) else 0 := by
  calc
    (∑ index, theorem12OneComparisonIncidences alternative (labels index, false)) =
        ∑ index, ∑ side : Bool,
          if theorem11PairLabelsEquiv Index Alternative labels index side = alternative
            then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro index _
          rcases hlabel : labels index with ⟨first, second⟩
          by_cases hfirst : first = alternative <;> by_cases hsecond : second = alternative <;>
            rw [Fintype.sum_bool] <;>
              simp [theorem11PairLabelsEquiv, theorem12OneComparisonIncidences, hlabel,
                hfirst, hsecond]
    _ = ∑ index : Index × Bool,
        if theorem11PairLabelsEquiv Index Alternative labels index.1 index.2 = alternative
          then (1 : ℝ) else 0 := by
          simpa using
            (Fintype.sum_prod_type' (fun (index : Index) (side : Bool) =>
              if theorem11PairLabelsEquiv Index Alternative labels index side = alternative
                then (1 : ℝ) else 0)).symm

private theorem theorem11_exp_neg_one_le_three_eighths :
    Real.exp (-(1 : ℝ)) ≤ (3 : ℝ) / 8 := by
  have hseries := Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) (by norm_num) 4
  have hexp : (8 : ℝ) / 3 ≤ Real.exp 1 := by
    convert hseries using 1 <;> norm_num
  have hinv : 1 / Real.exp 1 ≤ 1 / ((8 : ℝ) / 3) := by
    exact one_div_le_one_div_of_le (by norm_num) hexp
  simpa [Real.exp_neg, one_div] using hinv

/--
The flattened `2nd` endpoint draws have the source Chernoff lower tail for
one alternative's total Borda incidence count.
-/
private theorem theorem11_iidAlternativeIncidence_halfMean_lowerTail_flat
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (alternative : Alternative) :
    pmfProb
      (pmfProduct ((Fin users × Fin comparisonsPerUser) × Bool) Alternative sampling)
      (fun labels =>
        (∑ index, if labels index = alternative then (1 : ℝ) else 0) ≤
          ((users * comparisonsPerUser : ℕ) : ℝ) * (sampling alternative).toReal) ≤
      Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) *
        (sampling alternative).toReal / 4) := by
  letI : MeasurableSpace Alternative := ⊤
  let mass : ℝ := (sampling alternative).toReal
  have hmass_nonneg : 0 ≤ mass := ENNReal.toReal_nonneg
  have hcount_nonneg : 0 ≤ ((users * comparisonsPerUser : ℕ) : ℝ) := by positivity
  have hproduct_nonneg : 0 ≤ ((users * comparisonsPerUser : ℕ) : ℝ) * mass :=
    mul_nonneg hcount_nonneg hmass_nonneg
  have htail := pmfProb_pmfProduct_indicatorSum_le_le_exponential
    (ι := (Fin users × Fin comparisonsPerUser) × Bool)
    (μ := sampling)
    (indicator := fun drawn => if drawn = alternative then (1 : ℝ) else 0)
    (meanLower := mass)
    (((users * comparisonsPerUser : ℕ) : ℝ) * mass) 1
    (fun drawn => by
      by_cases hdrawn : drawn = alternative <;> simp [hdrawn])
    (le_of_eq (by simpa [mass] using
      (theorem12_pmfExp_eq_indicator sampling alternative).symm))
    (by norm_num)
  have hexp_factor : 2 * (Real.exp (-(1 : ℝ)) - 1 / 2) ≤ -(1 : ℝ) / 4 := by
    linarith [theorem11_exp_neg_one_le_three_eighths]
  have hscaled := mul_le_mul_of_nonneg_left hexp_factor hproduct_nonneg
  calc
    pmfProb
        (pmfProduct ((Fin users × Fin comparisonsPerUser) × Bool) Alternative sampling)
        (fun labels =>
          (∑ index, if labels index = alternative then (1 : ℝ) else 0) ≤
            ((users * comparisonsPerUser : ℕ) : ℝ) * mass) ≤
      Real.exp
        ((1 : ℝ) * (((users * comparisonsPerUser : ℕ) : ℝ) * mass) +
          (((Finset.univ : Finset ((Fin users × Fin comparisonsPerUser) × Bool)).card : ℕ) : ℝ) *
            ((Real.exp (-((1 : ℝ))) - 1) * mass)) := by
          simpa using htail
    _ = Real.exp
        (((users * comparisonsPerUser : ℕ) : ℝ) * mass *
          (2 * (Real.exp (-(1 : ℝ)) - 1 / 2))) := by
          congr 1
          simp [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.cast_mul]
          ring
    _ ≤ Real.exp (((users * comparisonsPerUser : ℕ) : ℝ) * mass * (-(1 : ℝ) / 4)) := by
          exact Real.exp_le_exp.mpr hscaled
    _ = Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * mass / 4) := by
          congr 1
          ring

/--
The source user-batch incidence denominator is at least half its mean except
with the literal `exp(-nd μ(x)/4)` Chernoff probability.  The proof first
marginalizes response tables, then flattens the user and pair coordinates and
finally rebrackets each ordered pair into its two independent endpoint draws.
-/
theorem theorem11_iidUserBordaIncidences_halfMean_lowerTail
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (alternative : Alternative) :
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample =>
        (∑ user, theorem2UserBatchBordaIncidences alternative
          (fun position => ((sample user).2 position, false))) ≤
          ((users * comparisonsPerUser : ℕ) : ℝ) * (sampling alternative).toReal) ≤
      Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) *
        (sampling alternative).toReal / 4) := by
  classical
  let labelLaw := theorem2UserPairLabelLaw sampling
  let batchLabelLaw := pmfProduct (Fin comparisonsPerUser)
    (Alternative × Alternative) labelLaw
  let sourceLaw := pmfProd responseLaw batchLabelLaw
  let indexType := Fin users × Fin comparisonsPerUser
  let cutoff : ℝ := ((users * comparisonsPerUser : ℕ) : ℝ) *
    (sampling alternative).toReal
  let flatPairEvent : (indexType → Alternative × Alternative) → Prop := fun labels =>
    (∑ index, theorem12OneComparisonIncidences alternative (labels index, false)) ≤ cutoff
  let flatAlternativeEvent : (indexType × Bool → Alternative) → Prop := fun labels =>
    (∑ index, if labels index = alternative then (1 : ℝ) else 0) ≤ cutoff
  have hmarginal :
      pmfProb (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative)) sourceLaw)
        (fun sample =>
          (∑ user, theorem2UserBatchBordaIncidences alternative
            (fun position => ((sample user).2 position, false))) ≤ cutoff) =
      pmfProb (pmfProduct (Fin users)
        (Fin comparisonsPerUser → Alternative × Alternative) batchLabelLaw)
        (fun labels =>
          (∑ user, theorem2UserBatchBordaIncidences alternative
            (fun position => (labels user position, false))) ≤ cutoff) := by
        unfold pmfProb
        simpa [sourceLaw, batchLabelLaw] using
          (pmfExp_pmfProduct_pmfProd_snd responseLaw batchLabelLaw
            (fun labels => if (∑ user, theorem2UserBatchBordaIncidences alternative
              (fun position => (labels user position, false))) ≤ cutoff then (1 : ℝ) else 0))
  have hflattenPairs :
      pmfProb (pmfProduct (Fin users)
        (Fin comparisonsPerUser → Alternative × Alternative) batchLabelLaw)
        (fun labels =>
          (∑ user, theorem2UserBatchBordaIncidences alternative
            (fun position => (labels user position, false))) ≤ cutoff) =
      pmfProb (pmfProduct indexType (Alternative × Alternative) labelLaw) flatPairEvent := by
        unfold pmfProb
        calc
          pmfExp (pmfProduct (Fin users)
              (Fin comparisonsPerUser → Alternative × Alternative) batchLabelLaw)
              (fun labels => if (∑ user, theorem2UserBatchBordaIncidences alternative
                (fun position => (labels user position, false))) ≤ cutoff then (1 : ℝ) else 0) =
            pmfExp (pmfProduct (Fin users)
              (Fin comparisonsPerUser → Alternative × Alternative) batchLabelLaw)
              (fun labels => if flatPairEvent (fun index => labels index.1 index.2)
                then (1 : ℝ) else 0) := by
                  apply pmfExp_congr
                  intro labels
                  simp only [flatPairEvent]
                  change (if theorem12EmpiricalBordaIncidences
                    theorem2UserBatchBordaIncidences alternative
                    (fun user position => (labels user position, false)) ≤ cutoff
                    then (1 : ℝ) else 0) = _
                  rw [theorem11_iidUserBordaIncidences_eq_flattenedPair alternative labels]
          _ = pmfExp (pmfProduct indexType (Alternative × Alternative) labelLaw)
              (fun labels => if flatPairEvent labels then (1 : ℝ) else 0) :=
                pmfExp_pmfProduct_pmfProduct_flatten labelLaw
                  (fun labels => if flatPairEvent labels then (1 : ℝ) else 0)
  have hrebracket :
      pmfProb (pmfProduct indexType (Alternative × Alternative) labelLaw) flatPairEvent =
      pmfProb (pmfProduct indexType (Bool → Alternative)
        (pmfProduct Bool Alternative sampling))
        (fun labels => flatAlternativeEvent (fun index => labels index.1 index.2)) := by
        unfold pmfProb
        calc
          pmfExp (pmfProduct indexType (Alternative × Alternative) labelLaw)
              (fun labels => if flatPairEvent labels then (1 : ℝ) else 0) =
            pmfExp (pmfProduct indexType (Alternative × Alternative) labelLaw)
              (fun labels => if flatAlternativeEvent
                (fun index => theorem11PairLabelsEquiv indexType Alternative labels
                  index.1 index.2) then (1 : ℝ) else 0) := by
                  apply pmfExp_congr
                  intro labels
                  simp only [flatPairEvent, flatAlternativeEvent]
                  rw [theorem11_flatPairBordaIncidences_eq_flatAlternativeIndicators
                    alternative labels]
          _ = pmfExp (pmfProduct indexType (Bool → Alternative)
              (pmfProduct Bool Alternative sampling))
              (fun labels => if flatAlternativeEvent (fun index => labels index.1 index.2)
                then (1 : ℝ) else 0) := by
                  simpa [labelLaw] using
                    (theorem11_pmfExp_pairLabels_rebracket sampling
                      (fun labels => if flatAlternativeEvent (fun index => labels index.1 index.2)
                        then (1 : ℝ) else 0))
  have hflattenSides :
      pmfProb (pmfProduct indexType (Bool → Alternative)
        (pmfProduct Bool Alternative sampling))
        (fun labels => flatAlternativeEvent (fun index => labels index.1 index.2)) =
      pmfProb (pmfProduct (indexType × Bool) Alternative sampling) flatAlternativeEvent := by
        unfold pmfProb
        exact pmfExp_pmfProduct_pmfProduct_flatten sampling
          (fun labels => if flatAlternativeEvent labels then (1 : ℝ) else 0)
  calc
    pmfProb
        (pmfProduct (Fin users)
          (theorem2UserResponseTable Alternative ×
            (Fin comparisonsPerUser → Alternative × Alternative))
          (pmfProd responseLaw
            (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
              (theorem2UserPairLabelLaw sampling))))
        (fun sample =>
          (∑ user, theorem2UserBatchBordaIncidences alternative
            (fun position => ((sample user).2 position, false))) ≤
            ((users * comparisonsPerUser : ℕ) : ℝ) * (sampling alternative).toReal) =
      pmfProb (pmfProduct indexType (Alternative × Alternative) labelLaw) flatPairEvent := by
        simpa [sourceLaw, cutoff] using hmarginal.trans hflattenPairs
    _ = pmfProb (pmfProduct (indexType × Bool) Alternative sampling) flatAlternativeEvent :=
      hrebracket.trans hflattenSides
    _ ≤ Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) *
        (sampling alternative).toReal / 4) := by
      simpa [flatAlternativeEvent, cutoff, indexType] using
        (theorem11_iidAlternativeIncidence_halfMean_lowerTail_flat sampling users
          comparisonsPerUser alternative)

/--
Any event determined by total Borda incidence has the same probability on the
literal source law as on the flattened `2nd` independent endpoint labels.
This is the reusable law bridge for the lower-tail and two-sided denominator
arguments in Lemma 11.
-/
private theorem theorem11_iidUserBordaIncidences_pmfProb_eq_flatEndpoint
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (alternative : Alternative) (event : ℝ → Prop) [DecidablePred event] :
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample => event (∑ user, theorem2UserBatchBordaIncidences alternative
        (fun position => ((sample user).2 position, false)))) =
    pmfProb
      (pmfProduct ((Fin users × Fin comparisonsPerUser) × Bool) Alternative sampling)
      (fun labels => event (∑ index,
        if labels index = alternative then (1 : ℝ) else 0)) := by
  classical
  let labelLaw := theorem2UserPairLabelLaw sampling
  let batchLabelLaw := pmfProduct (Fin comparisonsPerUser)
    (Alternative × Alternative) labelLaw
  let sourceLaw := pmfProd responseLaw batchLabelLaw
  let indexType := Fin users × Fin comparisonsPerUser
  let flatPairEvent : (indexType → Alternative × Alternative) → Prop := fun labels =>
    event (∑ index, theorem12OneComparisonIncidences alternative (labels index, false))
  let flatAlternativeEvent : (indexType × Bool → Alternative) → Prop := fun labels =>
    event (∑ index, if labels index = alternative then (1 : ℝ) else 0)
  have hmarginal :
      pmfProb (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative)) sourceLaw)
        (fun sample => event (∑ user, theorem2UserBatchBordaIncidences alternative
          (fun position => ((sample user).2 position, false)))) =
      pmfProb (pmfProduct (Fin users)
        (Fin comparisonsPerUser → Alternative × Alternative) batchLabelLaw)
        (fun labels => event (∑ user, theorem2UserBatchBordaIncidences alternative
          (fun position => (labels user position, false)))) := by
        unfold pmfProb
        simpa [sourceLaw, batchLabelLaw] using
          (pmfExp_pmfProduct_pmfProd_snd responseLaw batchLabelLaw
            (fun labels => if event (∑ user, theorem2UserBatchBordaIncidences alternative
              (fun position => (labels user position, false))) then (1 : ℝ) else 0))
  have hflattenPairs :
      pmfProb (pmfProduct (Fin users)
        (Fin comparisonsPerUser → Alternative × Alternative) batchLabelLaw)
        (fun labels => event (∑ user, theorem2UserBatchBordaIncidences alternative
          (fun position => (labels user position, false)))) =
      pmfProb (pmfProduct indexType (Alternative × Alternative) labelLaw) flatPairEvent := by
        unfold pmfProb
        calc
          pmfExp (pmfProduct (Fin users)
              (Fin comparisonsPerUser → Alternative × Alternative) batchLabelLaw)
              (fun labels => if event (∑ user, theorem2UserBatchBordaIncidences alternative
                (fun position => (labels user position, false))) then (1 : ℝ) else 0) =
            pmfExp (pmfProduct (Fin users)
              (Fin comparisonsPerUser → Alternative × Alternative) batchLabelLaw)
              (fun labels => if flatPairEvent (fun index => labels index.1 index.2)
                then (1 : ℝ) else 0) := by
                  apply pmfExp_congr
                  intro labels
                  simp only [flatPairEvent]
                  change (if event (theorem12EmpiricalBordaIncidences
                    theorem2UserBatchBordaIncidences alternative
                    (fun user position => (labels user position, false))) then (1 : ℝ) else 0) = _
                  rw [theorem11_iidUserBordaIncidences_eq_flattenedPair alternative labels]
          _ = pmfExp (pmfProduct indexType (Alternative × Alternative) labelLaw)
              (fun labels => if flatPairEvent labels then (1 : ℝ) else 0) :=
                pmfExp_pmfProduct_pmfProduct_flatten labelLaw
                  (fun labels => if flatPairEvent labels then (1 : ℝ) else 0)
  have hrebracket :
      pmfProb (pmfProduct indexType (Alternative × Alternative) labelLaw) flatPairEvent =
      pmfProb (pmfProduct indexType (Bool → Alternative)
        (pmfProduct Bool Alternative sampling))
        (fun labels => flatAlternativeEvent (fun index => labels index.1 index.2)) := by
        unfold pmfProb
        calc
          pmfExp (pmfProduct indexType (Alternative × Alternative) labelLaw)
              (fun labels => if flatPairEvent labels then (1 : ℝ) else 0) =
            pmfExp (pmfProduct indexType (Alternative × Alternative) labelLaw)
              (fun labels => if flatAlternativeEvent
                (fun index => theorem11PairLabelsEquiv indexType Alternative labels
                  index.1 index.2) then (1 : ℝ) else 0) := by
                  apply pmfExp_congr
                  intro labels
                  simp only [flatPairEvent, flatAlternativeEvent]
                  exact congrArg (fun value : ℝ =>
                    if event value then (1 : ℝ) else 0)
                    (theorem11_flatPairBordaIncidences_eq_flatAlternativeIndicators
                      alternative labels)
          _ = pmfExp (pmfProduct indexType (Bool → Alternative)
              (pmfProduct Bool Alternative sampling))
              (fun labels => if flatAlternativeEvent (fun index => labels index.1 index.2)
                then (1 : ℝ) else 0) := by
                  simpa [labelLaw] using
                    (theorem11_pmfExp_pairLabels_rebracket sampling
                      (fun labels => if flatAlternativeEvent (fun index => labels index.1 index.2)
                        then (1 : ℝ) else 0))
  have hflattenSides :
      pmfProb (pmfProduct indexType (Bool → Alternative)
        (pmfProduct Bool Alternative sampling))
        (fun labels => flatAlternativeEvent (fun index => labels index.1 index.2)) =
      pmfProb (pmfProduct (indexType × Bool) Alternative sampling) flatAlternativeEvent := by
        unfold pmfProb
        exact pmfExp_pmfProduct_pmfProduct_flatten sampling
          (fun labels => if flatAlternativeEvent labels then (1 : ℝ) else 0)
  calc
    pmfProb
        (pmfProduct (Fin users)
          (theorem2UserResponseTable Alternative ×
            (Fin comparisonsPerUser → Alternative × Alternative))
          (pmfProd responseLaw
            (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
              (theorem2UserPairLabelLaw sampling))))
        (fun sample => event (∑ user, theorem2UserBatchBordaIncidences alternative
          (fun position => ((sample user).2 position, false)))) =
      pmfProb (pmfProduct indexType (Alternative × Alternative) labelLaw) flatPairEvent := by
        simpa [sourceLaw] using hmarginal.trans hflattenPairs
    _ = pmfProb (pmfProduct (indexType × Bool) Alternative sampling) flatAlternativeEvent :=
      hrebracket.trans hflattenSides
    _ = pmfProb
        (pmfProduct ((Fin users × Fin comparisonsPerUser) × Bool) Alternative sampling)
        (fun labels => event (∑ index,
          if labels index = alternative then (1 : ℝ) else 0)) := by
          rfl

/--
Two-sided Bernstein tail for the flattened binomial Borda-incidence count.
There are exactly `2nd` independent endpoint indicators, so the variance
proxy is their mean rather than a user-level range bound.
-/
private theorem theorem11_iidAlternativeIncidence_abs_centered_tail_flat
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (alternative : Alternative) (cutoff : ℝ) (hcutoff_nonneg : 0 ≤ cutoff)
    (hden_pos : 0 <
      (Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
        (sampling alternative).toReal + cutoff) :
    pmfProb
      (pmfProduct ((Fin users × Fin comparisonsPerUser) × Bool) Alternative sampling)
      (fun labels => cutoff ≤ |(∑ index,
        if labels index = alternative then (1 : ℝ) else 0) -
        (Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
          (sampling alternative).toReal|) ≤
      2 * Real.exp (-cutoff ^ 2 /
        (4 * ((Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
          (sampling alternative).toReal + cutoff))) := by
  letI : MeasurableSpace Alternative := ⊤
  let indexType := (Fin users × Fin comparisonsPerUser) × Bool
  let mass : ℝ := (sampling alternative).toReal
  let indicator : Alternative → ℝ := fun drawn =>
    if drawn = alternative then 1 else 0
  let statistic : Alternative → ℝ := fun drawn => indicator drawn - mass
  have hmass_nonneg : 0 ≤ mass := ENNReal.toReal_nonneg
  have hmass_le_one : mass ≤ 1 := pmf_apply_toReal_le_one sampling alternative
  have hmean_indicator : pmfExp sampling indicator = mass := by
    simpa [indicator, mass] using theorem12_pmfExp_eq_indicator sampling alternative
  have hmean : pmfExp sampling statistic = 0 := by
    unfold statistic
    rw [pmfExp_sub, pmfExp_const, hmean_indicator]
    ring
  have hindicator_sq : ∀ drawn, indicator drawn ^ 2 = indicator drawn := by
    intro drawn
    by_cases hdrawn : drawn = alternative <;> simp [indicator, hdrawn]
  have hcentered_sq : pmfExp sampling (fun drawn => statistic drawn ^ 2) =
      pmfVariance sampling indicator := by
    unfold pmfVariance
    apply pmfExp_congr
    intro drawn
    dsimp [statistic]
    rw [hmean_indicator]
  have hvariance : pmfExp sampling (fun drawn => statistic drawn ^ 2) ≤ mass := by
    calc
      pmfExp sampling (fun drawn => statistic drawn ^ 2) = pmfVariance sampling indicator :=
        hcentered_sq
      _ = pmfExp sampling (fun drawn => indicator drawn ^ 2) -
          (pmfExp sampling indicator) ^ 2 :=
        pmfVariance_eq_exp_sq_sub_sq_exp sampling indicator
      _ = mass - mass ^ 2 := by
        rw [show pmfExp sampling (fun drawn => indicator drawn ^ 2) =
            pmfExp sampling indicator by
              apply pmfExp_congr
              intro drawn
              exact hindicator_sq drawn,
          hmean_indicator]
      _ ≤ mass := sub_le_self _ (sq_nonneg _)
  have hbound : ∀ drawn, |statistic drawn| ≤ (1 : ℝ) := by
    intro drawn
    dsimp [statistic, indicator]
    by_cases hdrawn : drawn = alternative
    · subst drawn
      have hone : |(1 : ℝ) - mass| ≤ 1 := by
        rw [abs_of_nonneg (by linarith)]
        linarith
      simpa using hone
    · have hzero : |(0 : ℝ) - mass| ≤ 1 := by
        rw [zero_sub, abs_neg, abs_of_nonneg hmass_nonneg]
        exact hmass_le_one
      simpa [hdrawn] using hzero
  have htail := pmfProb_pmfProduct_centeredBoundedSum_abs_ge_le_bernstein
    (ι := indexType) (α := Alternative) sampling statistic mass 1 cutoff hmean hvariance hbound
    hmass_nonneg (by norm_num) hcutoff_nonneg (by simpa [indexType, mass] using hden_pos)
  simpa [indexType, statistic, indicator, mass, Finset.sum_sub_distrib] using htail

/-- Total raw Borda wins of one alternative in the literal latent user sample. -/
def theorem11IidUserLatentBordaWins
    {Alternative : Type*} [DecidableEq Alternative] {users comparisonsPerUser : ℕ}
    (alternative : Alternative)
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) : ℝ :=
  ∑ user, theorem2UserBatchBordaWins alternative
    (fun position => ((sample user).2 position,
      (sample user).1 ((sample user).2 position).1 ((sample user).2 position).2))

/-- The total raw Borda count is the sum of all of its unordered-pair contributions. -/
theorem theorem11_iidUserLatentBordaWins_eq_sum_unorderedPairWins
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {users comparisonsPerUser : ℕ}
    (alternative : Alternative)
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) :
    theorem11IidUserLatentBordaWins alternative sample =
      ∑ opponent : Alternative, ∑ user,
        theorem10UserUnorderedPairWins alternative opponent (sample user).1 (sample user).2 := by
  unfold theorem11IidUserLatentBordaWins
  calc
    (∑ user, theorem2UserBatchBordaWins alternative
        (fun position => ((sample user).2 position,
          (sample user).1 ((sample user).2 position).1 ((sample user).2 position).2))) =
        ∑ user, ∑ opponent : Alternative,
          theorem10UserUnorderedPairWins alternative opponent (sample user).1 (sample user).2 := by
            apply Finset.sum_congr rfl
            intro user _
            exact theorem11_userLatentBordaWins_eq_sum_unorderedPairWins alternative
              (sample user).1 (sample user).2
    _ = ∑ opponent : Alternative, ∑ user,
        theorem10UserUnorderedPairWins alternative opponent (sample user).1 (sample user).2 :=
      Finset.sum_comm

/--
The source-sharp centered numerator for one alternative: its diagonal label
count and all distinct unordered-pair raw Borda contributions are centered
separately, exactly as in the proof of Lemma 11.
-/
def theorem11IidUserBordaPairwiseCentered
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {users comparisonsPerUser : ℕ}
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative)
    (alternative : Alternative)
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) : ℝ :=
  (∑ user, theorem11UserDiagonalBordaWinsCentered sampling alternative (sample user).2) +
    ∑ opponent ∈ Finset.univ.erase alternative, ∑ user,
      theorem11UserUnorderedPairWinCentered alternative opponent
        (preference.prob PUnit.unit alternative opponent) (sample user).1 (sample user).2
        (theorem10FixedPairIncidenceProbability sampling alternative opponent)

/-- The explicit raw-Borda mean associated with the preceding centered numerator. -/
def theorem11IidUserBordaPairwiseMean
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative)
    (users comparisonsPerUser : ℕ) (alternative : Alternative) : ℝ :=
  (users : ℝ) * ((comparisonsPerUser : ℝ) * (sampling alternative).toReal ^ 2 +
    ∑ opponent ∈ Finset.univ.erase alternative,
      (comparisonsPerUser : ℝ) * preference.prob PUnit.unit alternative opponent *
        theorem10FixedPairIncidenceProbability sampling alternative opponent)

/--
The explicit raw-count mean is the source population Borda mean.  Separating
the diagonal label pair supplies the self-comparison probability `1 / 2`.
-/
theorem theorem11_iidUserBordaPairwiseMean_eq_populationBordaMean
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative)
    (users comparisonsPerUser : ℕ) (alternative : Alternative) :
    theorem11IidUserBordaPairwiseMean sampling preference users comparisonsPerUser alternative =
      (users : ℝ) * (comparisonsPerUser : ℝ) * 2 * (sampling alternative).toReal *
        pairwiseBordaScore sampling preference alternative := by
  let mass : ℝ := (sampling alternative).toReal
  have hscore : pairwiseBordaScore sampling preference alternative =
      mass * ((1 : ℝ) / 2) +
        ∑ opponent ∈ Finset.univ.erase alternative,
          (sampling opponent).toReal * preference.prob PUnit.unit alternative opponent := by
    unfold pairwiseBordaScore pmfExp
    rw [← Finset.sum_erase_add (Finset.univ : Finset Alternative)
      (fun opponent => (sampling opponent).toReal *
        preference.prob PUnit.unit alternative opponent) (Finset.mem_univ alternative)]
    rw [pairwisePreference_self_eq_half preference alternative]
    simp [mass]
    ring
  have hoffdiag :
      (∑ opponent ∈ Finset.univ.erase alternative,
        (comparisonsPerUser : ℝ) * preference.prob PUnit.unit alternative opponent *
          theorem10FixedPairIncidenceProbability sampling alternative opponent) =
        (comparisonsPerUser : ℝ) * 2 * mass *
          (∑ opponent ∈ Finset.univ.erase alternative,
            (sampling opponent).toReal * preference.prob PUnit.unit alternative opponent) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro opponent hopponent
      dsimp [theorem10FixedPairIncidenceProbability, mass]
      ring
  unfold theorem11IidUserBordaPairwiseMean
  rw [hoffdiag, hscore]
  dsimp [mass]
  ring

private theorem theorem11_iidDiagonalRaw_eq_centered_add_mean
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {users comparisonsPerUser : ℕ}
    (sampling : PMF Alternative) (alternative : Alternative)
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) :
    (∑ user, theorem10UserUnorderedPairWins alternative alternative
      (sample user).1 (sample user).2) =
      (∑ user, theorem11UserDiagonalBordaWinsCentered sampling alternative (sample user).2) +
        (users : ℝ) * ((comparisonsPerUser : ℝ) * (sampling alternative).toReal ^ 2) := by
  have hraw :
      (∑ user, theorem10UserUnorderedPairWins alternative alternative
        (sample user).1 (sample user).2) =
      ∑ user, theorem11UserDiagonalBordaWins alternative (sample user).2 := by
        apply Finset.sum_congr rfl
        intro user _
        exact theorem10UserUnorderedPairWins_self_eq_diagonalBordaWins alternative
          (sample user).1 (sample user).2
  unfold theorem11UserDiagonalBordaWinsCentered
  rw [hraw, Finset.sum_sub_distrib]
  have hconst :
      (∑ _user : Fin users,
        (comparisonsPerUser : ℝ) * (sampling alternative).toReal ^ 2) =
        (users : ℝ) * ((comparisonsPerUser : ℝ) * (sampling alternative).toReal ^ 2) := by
          simp [nsmul_eq_mul]
  rw [hconst]
  ring

private theorem theorem11_iidDistinctRaw_eq_centered_add_mean
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {users comparisonsPerUser : ℕ}
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative)
    (alternative opponent : Alternative)
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) :
    (∑ user, theorem10UserUnorderedPairWins alternative opponent
      (sample user).1 (sample user).2) =
      (∑ user, theorem11UserUnorderedPairWinCentered alternative opponent
        (preference.prob PUnit.unit alternative opponent) (sample user).1 (sample user).2
        (theorem10FixedPairIncidenceProbability sampling alternative opponent)) +
        (users : ℝ) * ((comparisonsPerUser : ℝ) *
          preference.prob PUnit.unit alternative opponent *
          theorem10FixedPairIncidenceProbability sampling alternative opponent) := by
  unfold theorem11UserUnorderedPairWinCentered
  rw [Finset.sum_sub_distrib]
  have hconst :
      (∑ _user : Fin users,
        (comparisonsPerUser : ℝ) * preference.prob PUnit.unit alternative opponent *
          theorem10FixedPairIncidenceProbability sampling alternative opponent) =
        (users : ℝ) * ((comparisonsPerUser : ℝ) *
          preference.prob PUnit.unit alternative opponent *
          theorem10FixedPairIncidenceProbability sampling alternative opponent) := by
          simp [nsmul_eq_mul]
  rw [hconst]
  ring

/-- The literal raw Borda count equals the sharp centered numerator plus its explicit mean. -/
theorem theorem11_iidUserLatentBordaWins_eq_pairwiseCentered_add_mean
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {users comparisonsPerUser : ℕ}
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative)
    (alternative : Alternative)
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) :
    theorem11IidUserLatentBordaWins alternative sample =
      theorem11IidUserBordaPairwiseCentered sampling preference alternative sample +
        theorem11IidUserBordaPairwiseMean sampling preference users comparisonsPerUser alternative := by
  rw [theorem11_iidUserLatentBordaWins_eq_sum_unorderedPairWins]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ alternative)]
  rw [theorem11_iidDiagonalRaw_eq_centered_add_mean sampling alternative sample]
  have hoffdiag :
      (∑ opponent ∈ Finset.univ.erase alternative, ∑ user,
        theorem10UserUnorderedPairWins alternative opponent (sample user).1 (sample user).2) =
        ∑ opponent ∈ Finset.univ.erase alternative,
          ((∑ user, theorem11UserUnorderedPairWinCentered alternative opponent
            (preference.prob PUnit.unit alternative opponent) (sample user).1 (sample user).2
            (theorem10FixedPairIncidenceProbability sampling alternative opponent)) +
            (users : ℝ) * ((comparisonsPerUser : ℝ) *
              preference.prob PUnit.unit alternative opponent *
              theorem10FixedPairIncidenceProbability sampling alternative opponent)) := by
        apply Finset.sum_congr rfl
        intro opponent hopponent
        exact theorem11_iidDistinctRaw_eq_centered_add_mean sampling preference alternative
          opponent sample
  rw [hoffdiag, Finset.sum_add_distrib]
  unfold theorem11IidUserBordaPairwiseCentered theorem11IidUserBordaPairwiseMean
  rw [mul_add, Finset.mul_sum]
  ring

/--
Finite-union Bernstein tail for the source-sharp centered Borda numerator.
The diagonal contribution and every distinct opponent contribution may use
their own cutoff.  This leaves the final minimum-mass choice of cutoffs
explicit instead of hiding finite-cardinality factors in big-O notation.
-/
theorem theorem11_iidUserBordaPairwiseCentered_absTail_union
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {preference : PairwisePreference PUnit Alternative}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (alternative : Alternative)
    (diagonalCutoff : ℝ) (pairCutoff : Alternative → ℝ)
    (hdiagonalCutoff_nonneg : 0 ≤ diagonalCutoff)
    (hpairCutoff_nonneg : ∀ opponent, 0 ≤ pairCutoff opponent)
    (hdiagonalDen_pos : 0 < (users : ℝ) *
      ((comparisonsPerUser : ℝ) ^ 2 * (sampling alternative).toReal ^ 2) +
      (comparisonsPerUser : ℝ) * diagonalCutoff)
    (hpairDen_pos : ∀ opponent, opponent ∈ Finset.univ.erase alternative → 0 <
      (users : ℝ) * theorem10FixedPairVarianceProxy sampling comparisonsPerUser
        alternative opponent + (comparisonsPerUser : ℝ) * pairCutoff opponent)
    (hpairTail_bound : ∀ opponent, opponent ∈ Finset.univ.erase alternative →
      pmfProb
        (pmfProduct (Fin users)
          (theorem2UserResponseTable Alternative ×
            (Fin comparisonsPerUser → Alternative × Alternative))
          (pmfProd responseLaw
            (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
              (theorem2UserPairLabelLaw sampling))))
        (fun sample => pairCutoff opponent ≤ |∑ user,
          theorem11UserUnorderedPairWinCentered alternative opponent
            (preference.prob PUnit.unit alternative opponent) (sample user).1 (sample user).2
            (theorem10FixedPairIncidenceProbability sampling alternative opponent)|) ≤
        2 * Real.exp (-pairCutoff opponent ^ 2 /
          (4 * ((users : ℝ) * theorem10FixedPairVarianceProxy sampling comparisonsPerUser
            alternative opponent + (comparisonsPerUser : ℝ) * pairCutoff opponent))) ) :
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample => diagonalCutoff +
        (∑ opponent ∈ Finset.univ.erase alternative, pairCutoff opponent) ≤
          |theorem11IidUserBordaPairwiseCentered sampling preference alternative sample|) ≤
      2 * Real.exp (-diagonalCutoff ^ 2 /
        (4 * ((users : ℝ) *
          ((comparisonsPerUser : ℝ) ^ 2 * (sampling alternative).toReal ^ 2) +
          (comparisonsPerUser : ℝ) * diagonalCutoff))) +
        ∑ opponent ∈ Finset.univ.erase alternative,
          2 * Real.exp (-pairCutoff opponent ^ 2 /
            (4 * ((users : ℝ) * theorem10FixedPairVarianceProxy sampling comparisonsPerUser
              alternative opponent + (comparisonsPerUser : ℝ) * pairCutoff opponent))) := by
  classical
  let sourceLaw := pmfProd responseLaw
    (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
      (theorem2UserPairLabelLaw sampling))
  let law := pmfProduct (Fin users)
    (theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative)) sourceLaw
  let diagonal : (Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) → ℝ := fun sample =>
    ∑ user, theorem11UserDiagonalBordaWinsCentered sampling alternative (sample user).2
  let pairTerm : Alternative →
      (Fin users → (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) → ℝ := fun opponent sample =>
    ∑ user, theorem11UserUnorderedPairWinCentered alternative opponent
      (preference.prob PUnit.unit alternative opponent) (sample user).1 (sample user).2
      (theorem10FixedPairIncidenceProbability sampling alternative opponent)
  let diagonalBad :
      (Fin users → (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) → Prop := fun sample =>
    diagonalCutoff ≤ |diagonal sample|
  let pairBad : Alternative →
      (Fin users → (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) → Prop := fun opponent sample =>
    pairCutoff opponent ≤ |pairTerm opponent sample|
  let unionEvent :
      (Fin users → (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) → Prop := fun sample =>
    ∃ opponent ∈ Finset.univ.erase alternative, pairBad opponent sample
  letI : DecidablePred unionEvent := fun _ => Classical.dec _
  have hpointwise : ∀ sample,
      diagonalCutoff + (∑ opponent ∈ Finset.univ.erase alternative, pairCutoff opponent) ≤
          |theorem11IidUserBordaPairwiseCentered sampling preference alternative sample| →
        diagonalBad sample ∨ unionEvent sample := by
    intro sample hlarge
    by_cases hdiagonal : diagonalBad sample
    · exact Or.inl hdiagonal
    · right
      by_contra hnoPair
      change ¬ (∃ opponent ∈ Finset.univ.erase alternative,
        pairBad opponent sample) at hnoPair
      push_neg at hnoPair
      have hdiagonal_lt : |diagonal sample| < diagonalCutoff :=
        lt_of_not_ge hdiagonal
      have hpair_le : ∀ opponent ∈ Finset.univ.erase alternative,
          |pairTerm opponent sample| ≤ pairCutoff opponent := by
        intro opponent hopponent
        exact (le_of_lt (lt_of_not_ge (hnoPair opponent hopponent)))
      have hsum_le :
          |∑ opponent ∈ Finset.univ.erase alternative, pairTerm opponent sample| ≤
            ∑ opponent ∈ Finset.univ.erase alternative, pairCutoff opponent := by
          calc
            |∑ opponent ∈ Finset.univ.erase alternative, pairTerm opponent sample| ≤
                ∑ opponent ∈ Finset.univ.erase alternative, |pairTerm opponent sample| :=
                  Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ opponent ∈ Finset.univ.erase alternative, pairCutoff opponent := by
                  exact Finset.sum_le_sum hpair_le
      have htotal_lt :
          |diagonal sample +
            ∑ opponent ∈ Finset.univ.erase alternative, pairTerm opponent sample| <
            diagonalCutoff +
              ∑ opponent ∈ Finset.univ.erase alternative, pairCutoff opponent := by
          calc
            |diagonal sample +
              ∑ opponent ∈ Finset.univ.erase alternative, pairTerm opponent sample| ≤
                |diagonal sample| +
                  |∑ opponent ∈ Finset.univ.erase alternative, pairTerm opponent sample| :=
                    abs_add_le _ _
            _ < diagonalCutoff +
                ∑ opponent ∈ Finset.univ.erase alternative, pairCutoff opponent := by
                  linarith
      have hcentered_eq :
          theorem11IidUserBordaPairwiseCentered sampling preference alternative sample =
            diagonal sample +
              ∑ opponent ∈ Finset.univ.erase alternative, pairTerm opponent sample := by
          rfl
      rw [hcentered_eq] at hlarge
      exact (not_lt_of_ge hlarge) htotal_lt
  have hdiagonalTail : pmfProb law diagonalBad ≤
      2 * Real.exp (-diagonalCutoff ^ 2 /
        (4 * ((users : ℝ) *
          ((comparisonsPerUser : ℝ) ^ 2 * (sampling alternative).toReal ^ 2) +
          (comparisonsPerUser : ℝ) * diagonalCutoff))) := by
    simpa [law, sourceLaw, diagonalBad, diagonal] using
      (theorem11_iidUserDiagonalBordaWinsCentered_absTail_bernstein responseLaw sampling
        users comparisonsPerUser alternative diagonalCutoff hdiagonalCutoff_nonneg hdiagonalDen_pos)
  have hpairTail : ∀ opponent, opponent ∈ Finset.univ.erase alternative →
      pmfProb law (pairBad opponent) ≤
        2 * Real.exp (-pairCutoff opponent ^ 2 /
          (4 * ((users : ℝ) * theorem10FixedPairVarianceProxy sampling comparisonsPerUser
            alternative opponent + (comparisonsPerUser : ℝ) * pairCutoff opponent))) := by
    intro opponent hopponent
    simpa [law, sourceLaw, pairBad, pairTerm] using hpairTail_bound opponent hopponent
  have hunion :
      pmfProb law unionEvent ≤
        ∑ opponent ∈ Finset.univ.erase alternative, pmfProb law (pairBad opponent) := by
    simpa [unionEvent] using
      (pmfProb_exists_mem_le_sum law (Finset.univ.erase alternative) pairBad)
  calc
    pmfProb law (fun sample => diagonalCutoff +
        (∑ opponent ∈ Finset.univ.erase alternative, pairCutoff opponent) ≤
          |theorem11IidUserBordaPairwiseCentered sampling preference alternative sample|) ≤
      pmfProb law (fun sample => diagonalBad sample ∨
        unionEvent sample) := by
          apply pmfProb_le_of_imp
          intro sample hlarge
          exact hpointwise sample hlarge
    _ ≤ pmfProb law diagonalBad +
        pmfProb law unionEvent := pmfProb_or_le law _ _
    _ ≤ 2 * Real.exp (-diagonalCutoff ^ 2 /
        (4 * ((users : ℝ) *
          ((comparisonsPerUser : ℝ) ^ 2 * (sampling alternative).toReal ^ 2) +
          (comparisonsPerUser : ℝ) * diagonalCutoff))) +
        ∑ opponent ∈ Finset.univ.erase alternative, pmfProb law (pairBad opponent) := by
          gcongr
    _ ≤ 2 * Real.exp (-diagonalCutoff ^ 2 /
        (4 * ((users : ℝ) *
          ((comparisonsPerUser : ℝ) ^ 2 * (sampling alternative).toReal ^ 2) +
          (comparisonsPerUser : ℝ) * diagonalCutoff))) +
        ∑ opponent ∈ Finset.univ.erase alternative,
          2 * Real.exp (-pairCutoff opponent ^ 2 /
            (4 * ((users : ℝ) * theorem10FixedPairVarianceProxy sampling comparisonsPerUser
              alternative opponent + (comparisonsPerUser : ℝ) * pairCutoff opponent))) := by
          apply add_le_add_right
          apply Finset.sum_le_sum
          intro opponent hopponent
          exact hpairTail opponent hopponent


/-- The raw restricted Borda-win count has square at most the label-count square. -/
theorem theorem11UserUnorderedPairWins_sq_le_count_sq
    {Alternative : Type*} [DecidableEq Alternative] {comparisonsPerUser : ℕ}
    (first second : Alternative) (hdistinct : first ≠ second)
    (response : theorem2UserResponseTable Alternative)
    (labels : Fin comparisonsPerUser → Alternative × Alternative) :
    (theorem10UserUnorderedPairWins first second response labels) ^ 2 ≤
      (theorem10UserUnorderedPairCount first second labels) ^ 2 := by
  have hwins_nonneg := theorem10UserUnorderedPairWins_nonneg first second response labels
  have hwins_le_count := theorem10UserUnorderedPairWins_le_count first second hdistinct
    response labels
  have hcount_nonneg : 0 ≤ theorem10UserUnorderedPairCount first second labels := by
    unfold theorem10UserUnorderedPairCount
    exact Finset.sum_nonneg fun position _ => by
      rcases labels position with ⟨left, right⟩
      simp only [theorem10UnorderedPairIndicator]
      split <;> norm_num
  have hfactor_nonneg : 0 ≤ theorem10UserUnorderedPairCount first second labels +
      theorem10UserUnorderedPairWins first second response labels := by linarith
  have hproduct := mul_nonneg (sub_nonneg.mpr hwins_le_count) hfactor_nonneg
  nlinarith

/-- The literal raw pair-win statistic has mean zero after source centering. -/
theorem theorem11_pmfExp_userUnorderedPairWinCentered_eq_zero
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {preference : PairwisePreference PUnit Alternative}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative) (comparisonsPerUser : ℕ)
    (first second : Alternative) (hdistinct : first ≠ second) :
    pmfExp
      (pmfProd responseLaw
        (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
          (theorem2UserPairLabelLaw sampling)))
      (fun source => theorem11UserUnorderedPairWinCentered first second
        (preference.prob PUnit.unit first second) source.1 source.2
        (theorem10FixedPairIncidenceProbability sampling first second)) = 0 := by
  unfold theorem11UserUnorderedPairWinCentered theorem10FixedPairIncidenceProbability
  rw [pmfExp_sub, pmfExp_const]
  rw [theorem10_pmfExp_userUnorderedPairWins hcalibrated sampling comparisonsPerUser
    first second hdistinct]
  ring

/--
The raw pair-win centered second moment has the same label-count variance
proxy as the source's `k_i p_i` calculation.  This uses only the literal
response table and iid pair labels; no within-user outcome independence is
introduced.
-/
theorem theorem11_pmfExp_userUnorderedPairWinCentered_sq_le
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {preference : PairwisePreference PUnit Alternative}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative) (comparisonsPerUser : ℕ)
    (first second : Alternative) (hdistinct : first ≠ second) :
    pmfExp
      (pmfProd responseLaw
        (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
          (theorem2UserPairLabelLaw sampling)))
      (fun source => (theorem11UserUnorderedPairWinCentered first second
        (preference.prob PUnit.unit first second) source.1 source.2
        (theorem10FixedPairIncidenceProbability sampling first second)) ^ 2) ≤
      theorem10FixedPairVarianceProxy sampling comparisonsPerUser first second := by
  let sourceLaw := pmfProd responseLaw
    (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
      (theorem2UserPairLabelLaw sampling))
  let wins : (theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative)) → ℝ := fun source =>
    theorem10UserUnorderedPairWins first second source.1 source.2
  let count : (theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative)) → ℝ := fun source =>
    theorem10UserUnorderedPairCount first second source.2
  let centered : (theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative)) → ℝ := fun source =>
    theorem11UserUnorderedPairWinCentered first second
      (preference.prob PUnit.unit first second) source.1 source.2
      (theorem10FixedPairIncidenceProbability sampling first second)
  let varianceProxy := theorem10FixedPairVarianceProxy sampling comparisonsPerUser first second
  have hwins_mean : pmfExp sourceLaw wins =
      (comparisonsPerUser : ℝ) * preference.prob PUnit.unit first second *
        (theorem10FixedPairIncidenceProbability sampling first second) := by
    simpa [sourceLaw, wins, theorem10FixedPairIncidenceProbability] using
      (theorem10_pmfExp_userUnorderedPairWins hcalibrated sampling comparisonsPerUser
        first second hdistinct)
  have hcentered_sq : pmfExp sourceLaw (fun source => centered source ^ 2) =
      pmfVariance sourceLaw wins := by
    unfold pmfVariance
    apply pmfExp_congr
    intro source
    dsimp [centered, wins, theorem11UserUnorderedPairWinCentered]
    rw [hwins_mean]
  have hcount_sq : pmfExp sourceLaw (fun source => count source ^ 2) = varianceProxy := by
    dsimp [sourceLaw, count, varianceProxy]
    rw [pmfExp_pmfProd_eq_pairExp]
    change pmfPairExp responseLaw
      (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
        (theorem2UserPairLabelLaw sampling))
      (fun _ labels => (theorem10UserUnorderedPairCount first second labels) ^ 2) = _
    rw [pmfPairExp_ignore_left]
    simpa [theorem10FixedPairVarianceProxy, theorem10FixedPairIncidenceProbability] using
      (theorem10_pmfExp_userUnorderedPairCount_sq sampling comparisonsPerUser first second hdistinct)
  calc
    pmfExp sourceLaw (fun source => centered source ^ 2) = pmfVariance sourceLaw wins :=
      hcentered_sq
    _ = pmfExp sourceLaw (fun source => wins source ^ 2) - (pmfExp sourceLaw wins) ^ 2 :=
      pmfVariance_eq_exp_sq_sub_sq_exp sourceLaw wins
    _ ≤ pmfExp sourceLaw (fun source => wins source ^ 2) :=
      sub_le_self _ (sq_nonneg _)
    _ ≤ pmfExp sourceLaw (fun source => count source ^ 2) := by
      apply pmfExp_le_pmfExp_of_forall_le
      intro source
      exact theorem11UserUnorderedPairWins_sq_le_count_sq first second hdistinct source.1 source.2
    _ = varianceProxy := hcount_sq

/-- A raw centered pair-win contribution is bounded by one user's `d` displays. -/
theorem theorem11UserUnorderedPairWinCentered_abs_le_comparisons
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {preference : PairwisePreference PUnit Alternative}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative) (comparisonsPerUser : ℕ)
    (first second : Alternative) (hdistinct : first ≠ second)
    (source : theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative)) :
    |theorem11UserUnorderedPairWinCentered first second
        (preference.prob PUnit.unit first second) source.1 source.2
        (theorem10FixedPairIncidenceProbability sampling first second)| ≤
      comparisonsPerUser := by
  let sourceLaw := pmfProd responseLaw
    (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
      (theorem2UserPairLabelLaw sampling))
  let wins : (theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative)) → ℝ := fun draw =>
    theorem10UserUnorderedPairWins first second draw.1 draw.2
  let mean : ℝ := (comparisonsPerUser : ℝ) * preference.prob PUnit.unit first second *
    theorem10FixedPairIncidenceProbability sampling first second
  have hwins_mean : pmfExp sourceLaw wins = mean := by
    simpa [sourceLaw, wins, mean, theorem10FixedPairIncidenceProbability] using
      (theorem10_pmfExp_userUnorderedPairWins hcalibrated sampling comparisonsPerUser
        first second hdistinct)
  have hwins_nonneg : ∀ draw, 0 ≤ wins draw := by
    intro draw
    exact theorem10UserUnorderedPairWins_nonneg first second draw.1 draw.2
  have hwins_le : ∀ draw, wins draw ≤ comparisonsPerUser := by
    intro draw
    exact (theorem10UserUnorderedPairWins_le_count first second hdistinct draw.1 draw.2).trans
      (theorem10UserUnorderedPairCount_le_comparisons first second draw.2)
  have hmean_nonneg : 0 ≤ mean := by
    rw [← hwins_mean]
    exact pmfExp_nonneg_of_forall_nonneg sourceLaw wins hwins_nonneg
  have hmean_le : mean ≤ comparisonsPerUser := by
    rw [← hwins_mean]
    calc
      pmfExp sourceLaw wins ≤ pmfExp sourceLaw (fun _ => (comparisonsPerUser : ℝ)) :=
        pmfExp_le_pmfExp_of_forall_le sourceLaw wins _ hwins_le
      _ = comparisonsPerUser := pmfExp_const sourceLaw _
  rw [abs_le]
  constructor
  · change -(comparisonsPerUser : ℝ) ≤ wins source - mean
    linarith [hwins_nonneg source]
  · change wins source - mean ≤ comparisonsPerUser
    linarith [hwins_le source]

/--
Two-sided iid Bernstein tail for a raw distinct-pair Borda-win count centered
at its source expectation. This is the pairwise input used in Lemma 11's
opponent summation, distinct from the empirical-ratio tail of Lemma 10.
-/
theorem theorem11_iidUserUnorderedPairWinCentered_absTail_bernstein
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {preference : PairwisePreference PUnit Alternative}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (first second : Alternative) (hdistinct : first ≠ second)
    (cutoff : ℝ) (hcutoff_nonneg : 0 ≤ cutoff)
    (hden_pos : 0 < (users : ℝ) *
      theorem10FixedPairVarianceProxy sampling comparisonsPerUser first second +
      (comparisonsPerUser : ℝ) * cutoff) :
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample => cutoff ≤ |∑ index,
        theorem11UserUnorderedPairWinCentered first second
          (preference.prob PUnit.unit first second) (sample index).1 (sample index).2
          (theorem10FixedPairIncidenceProbability sampling first second)|) ≤
      2 * Real.exp (-cutoff ^ 2 /
        (4 * ((users : ℝ) *
          theorem10FixedPairVarianceProxy sampling comparisonsPerUser first second +
          (comparisonsPerUser : ℝ) * cutoff))) := by
  let sourceLaw := pmfProd responseLaw
    (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
      (theorem2UserPairLabelLaw sampling))
  let statistic : (theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative)) → ℝ := fun source =>
    theorem11UserUnorderedPairWinCentered first second
      (preference.prob PUnit.unit first second) source.1 source.2
      (theorem10FixedPairIncidenceProbability sampling first second)
  let varianceProxy := theorem10FixedPairVarianceProxy sampling comparisonsPerUser first second
  letI : MeasurableSpace (theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative)) := ⊤
  have hmean : pmfExp sourceLaw statistic = 0 := by
    simpa [sourceLaw, statistic] using
      (theorem11_pmfExp_userUnorderedPairWinCentered_eq_zero hcalibrated sampling
        comparisonsPerUser first second hdistinct)
  have hvariance : pmfExp sourceLaw (fun source => statistic source ^ 2) ≤ varianceProxy := by
    simpa [sourceLaw, statistic, varianceProxy] using
      (theorem11_pmfExp_userUnorderedPairWinCentered_sq_le hcalibrated sampling
        comparisonsPerUser first second hdistinct)
  have hvariance_nonneg : 0 ≤ varianceProxy := by
    dsimp [varianceProxy, theorem10FixedPairVarianceProxy,
      theorem10FixedPairIncidenceProbability]
    positivity
  have hbound : ∀ source, |statistic source| ≤ (comparisonsPerUser : ℝ) := by
    intro source
    simpa [statistic] using
      (theorem11UserUnorderedPairWinCentered_abs_le_comparisons hcalibrated sampling
        comparisonsPerUser first second hdistinct source)
  have htail := pmfProb_pmfProduct_centeredBoundedSum_abs_ge_le_bernstein
    (ι := Fin users)
    (α := theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative))
    sourceLaw statistic varianceProxy (comparisonsPerUser : ℝ) cutoff hmean hvariance hbound
    hvariance_nonneg (by positivity) hcutoff_nonneg
    (by simpa [varianceProxy, Fintype.card_fin] using hden_pos)
  simpa [sourceLaw, statistic, varianceProxy, Fintype.card_fin] using htail


/--
Source-sharp finite-union Bernstein tail for the centered Borda numerator.
This instantiates the preceding union lemma with the literal distinct-pair
tail, so no concentration hypothesis remains in the public statement.
-/
theorem theorem11_iidUserBordaPairwiseCentered_absTail_bernstein
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {preference : PairwisePreference PUnit Alternative}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (alternative : Alternative)
    (diagonalCutoff : ℝ) (pairCutoff : Alternative → ℝ)
    (hdiagonalCutoff_nonneg : 0 ≤ diagonalCutoff)
    (hpairCutoff_nonneg : ∀ opponent, 0 ≤ pairCutoff opponent)
    (hdiagonalDen_pos : 0 < (users : ℝ) *
      ((comparisonsPerUser : ℝ) ^ 2 * (sampling alternative).toReal ^ 2) +
      (comparisonsPerUser : ℝ) * diagonalCutoff)
    (hpairDen_pos : ∀ opponent, opponent ∈ Finset.univ.erase alternative → 0 <
      (users : ℝ) * theorem10FixedPairVarianceProxy sampling comparisonsPerUser
        alternative opponent + (comparisonsPerUser : ℝ) * pairCutoff opponent) :
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample => diagonalCutoff +
        (∑ opponent ∈ Finset.univ.erase alternative, pairCutoff opponent) ≤
          |theorem11IidUserBordaPairwiseCentered sampling preference alternative sample|) ≤
      2 * Real.exp (-diagonalCutoff ^ 2 /
        (4 * ((users : ℝ) *
          ((comparisonsPerUser : ℝ) ^ 2 * (sampling alternative).toReal ^ 2) +
          (comparisonsPerUser : ℝ) * diagonalCutoff))) +
        ∑ opponent ∈ Finset.univ.erase alternative,
          2 * Real.exp (-pairCutoff opponent ^ 2 /
            (4 * ((users : ℝ) * theorem10FixedPairVarianceProxy sampling comparisonsPerUser
              alternative opponent + (comparisonsPerUser : ℝ) * pairCutoff opponent))) := by
  refine theorem11_iidUserBordaPairwiseCentered_absTail_union hcalibrated sampling users
    comparisonsPerUser alternative diagonalCutoff pairCutoff hdiagonalCutoff_nonneg
    hpairCutoff_nonneg hdiagonalDen_pos hpairDen_pos ?_
  intro opponent hopponent
  have hdistinct : alternative ≠ opponent := Ne.symm (Finset.ne_of_mem_erase hopponent)
  exact theorem11_iidUserUnorderedPairWinCentered_absTail_bernstein hcalibrated sampling users
    comparisonsPerUser alternative opponent hdistinct (pairCutoff opponent)
    (hpairCutoff_nonneg opponent) (hpairDen_pos opponent hopponent)


/-- Explicit Bernstein quantile for the diagonal raw-Borda contribution. -/
noncomputable def theorem11DiagonalBernsteinQuantile
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (alternative : Alternative) (logLevel : ℝ) : ℝ :=
  Real.sqrt (8 * ((users : ℝ) *
    ((comparisonsPerUser : ℝ) ^ 2 * (sampling alternative).toReal ^ 2)) * logLevel) +
    8 * (comparisonsPerUser : ℝ) * logLevel

/-- Explicit Bernstein quantile for one distinct raw-Borda pair contribution. -/
noncomputable def theorem11DistinctPairBernsteinQuantile
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (first second : Alternative) (logLevel : ℝ) : ℝ :=
  Real.sqrt (8 * ((users : ℝ) *
    theorem10FixedPairVarianceProxy sampling comparisonsPerUser first second) * logLevel) +
    8 * (comparisonsPerUser : ℝ) * logLevel

/--
The algebraic core of Lemma 11's distinct-opponent summation.  A variance
proxy bounded by `d q (1 + d q)` has a Bernstein root term controlled at the
source rate whenever `r ≤ min {1, d q}`.
-/
private theorem theorem11_pairQuantileRoot_le_rateEnvelope
    {users comparisons q varianceProxy rateScale logLevel : ℝ}
    (husers_pos : 0 < users) (hcomparisons_pos : 0 < comparisons)
    (hq_pos : 0 < q) (hrateScale_pos : 0 < rateScale)
    (hlogLevel_nonneg : 0 ≤ logLevel) (hvariance_nonneg : 0 ≤ varianceProxy)
    (hrateScale_le_one : rateScale ≤ 1)
    (hrateScale_le_comparisons_q : rateScale ≤ comparisons * q)
    (hvariance_le : varianceProxy ≤ comparisons * q * (1 + comparisons * q)) :
    Real.sqrt (8 * (users * varianceProxy) * logLevel) ≤
      4 * comparisons * q * Real.sqrt (users * logLevel / rateScale) := by
  have hcomparison_q_pos : 0 < comparisons * q := mul_pos hcomparisons_pos hq_pos
  have hroot_arg_nonneg : 0 ≤ 8 * (users * varianceProxy) * logLevel := by positivity
  have hsmall_root_arg_nonneg : 0 ≤ users * logLevel / rateScale := by positivity
  have haux : rateScale * (1 + comparisons * q) ≤ 2 * (comparisons * q) := by
    have hmul : rateScale * (comparisons * q) ≤ comparisons * q :=
      by simpa using mul_le_mul_of_nonneg_right hrateScale_le_one hcomparison_q_pos.le
    nlinarith
  have hvariance_mul : varianceProxy * rateScale ≤ 2 * comparisons ^ 2 * q ^ 2 := by
    calc
      varianceProxy * rateScale ≤
          (comparisons * q * (1 + comparisons * q)) * rateScale :=
        mul_le_mul_of_nonneg_right hvariance_le hrateScale_pos.le
      _ = comparisons * q * (rateScale * (1 + comparisons * q)) := by ring
      _ ≤ comparisons * q * (2 * (comparisons * q)) :=
        mul_le_mul_of_nonneg_left haux hcomparison_q_pos.le
      _ = 2 * comparisons ^ 2 * q ^ 2 := by ring
  apply (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (Real.sqrt_nonneg _))).mp
  rw [Real.sq_sqrt hroot_arg_nonneg]
  have hright_sq :
      (4 * comparisons * q * Real.sqrt (users * logLevel / rateScale)) ^ 2 =
        16 * users * comparisons ^ 2 * q ^ 2 * logLevel / rateScale := by
    calc
      (4 * comparisons * q * Real.sqrt (users * logLevel / rateScale)) ^ 2 =
          16 * comparisons ^ 2 * q ^ 2 *
            (Real.sqrt (users * logLevel / rateScale)) ^ 2 := by ring
      _ = 16 * comparisons ^ 2 * q ^ 2 * (users * logLevel / rateScale) := by
          rw [Real.sq_sqrt hsmall_root_arg_nonneg]
      _ = 16 * users * comparisons ^ 2 * q ^ 2 * logLevel / rateScale := by ring
  rw [hright_sq]
  apply (le_div_iff₀ hrateScale_pos).2
  have hscaled := mul_le_mul_of_nonneg_left hvariance_mul
    (show 0 ≤ 8 * users * logLevel by positivity)
  nlinarith

/--
Minimum-mass envelope for a binomial endpoint-count Bernstein quantile after
normalization by its mean.  The square-root term is kept as
`sqrt(n L / r) / n`, an algebraically source-equivalent form that avoids a
spurious choice of square-root normal form.
-/
private theorem theorem11_incidenceQuantile_normalized_le_rateEnvelope
    {users comparisons mass minimumMass logLevel : ℝ}
    (husers_pos : 0 < users) (hcomparisons_pos : 0 < comparisons)
    (hcomparisons_one : 1 ≤ comparisons)
    (hmass_pos : 0 < mass) (hmass_le_one : mass ≤ 1)
    (hminimumMass_pos : 0 < minimumMass) (hminimumMass_le_mass : minimumMass ≤ mass)
    (hlogLevel_nonneg : 0 ≤ logLevel) :
    2 * (Real.sqrt (8 * (2 * users * comparisons * mass) * logLevel) + 8 * logLevel) /
        (2 * users * comparisons * mass) ≤
      8 * Real.sqrt (users * logLevel /
        min 1 (comparisons * minimumMass ^ 2)) / users +
      8 * logLevel / (users * minimumMass) := by
  let rateScale : ℝ := min 1 (comparisons * minimumMass ^ 2)
  have hminimumMass_nonneg : 0 ≤ minimumMass := hminimumMass_pos.le
  have hcomparisons_nonneg : 0 ≤ comparisons := hcomparisons_pos.le
  have hmass_nonneg : 0 ≤ mass := hmass_pos.le
  have hminimumMass_le_one : minimumMass ≤ 1 :=
    hminimumMass_le_mass.trans hmass_le_one
  have hminimumMass_sq_le_mass : minimumMass ^ 2 ≤ mass := by
    have hsquare_le : minimumMass ^ 2 ≤ minimumMass := by
      nlinarith [mul_nonneg hminimumMass_nonneg (sub_nonneg.mpr hminimumMass_le_one)]
    exact hsquare_le.trans hminimumMass_le_mass
  have hrateScale_pos : 0 < rateScale := by
    dsimp [rateScale]
    exact lt_min (by norm_num) (by positivity)
  have hrateScale_le_one : rateScale ≤ 1 := min_le_left _ _
  have hrateScale_le_twiceComparisonMass : rateScale ≤ 2 * comparisons * mass := by
    calc
      rateScale ≤ comparisons * minimumMass ^ 2 := min_le_right _ _
      _ ≤ comparisons * mass :=
        mul_le_mul_of_nonneg_left hminimumMass_sq_le_mass hcomparisons_nonneg
      _ ≤ 2 * comparisons * mass := by nlinarith
  have hvariance_nonneg : 0 ≤ 2 * comparisons * mass := by positivity
  have hvariance_le : 2 * comparisons * mass ≤
      (2 * comparisons) * mass * (1 + (2 * comparisons) * mass) := by
    nlinarith [mul_self_nonneg (2 * comparisons * mass)]
  have hroot := theorem11_pairQuantileRoot_le_rateEnvelope
    (users := users) (comparisons := 2 * comparisons) (q := mass)
    (varianceProxy := 2 * comparisons * mass) (rateScale := rateScale)
    (logLevel := logLevel) husers_pos (by positivity) hmass_pos hrateScale_pos
    hlogLevel_nonneg hvariance_nonneg hrateScale_le_one
    (by simpa [mul_assoc] using hrateScale_le_twiceComparisonMass) hvariance_le
  have hroot' : Real.sqrt (8 * (2 * users * comparisons * mass) * logLevel) ≤
      8 * comparisons * mass * Real.sqrt (users * logLevel / rateScale) := by
    calc
      Real.sqrt (8 * (2 * users * comparisons * mass) * logLevel) =
          Real.sqrt (8 * (users * (2 * comparisons * mass)) * logLevel) := by
            congr 1 <;> ring
      _ ≤ 4 * (2 * comparisons) * mass *
          Real.sqrt (users * logLevel / rateScale) := hroot
      _ = 8 * comparisons * mass * Real.sqrt (users * logLevel / rateScale) := by ring
  have hden_pos : 0 < 2 * users * comparisons * mass := by positivity
  have hroot_normalized :
      2 * Real.sqrt (8 * (2 * users * comparisons * mass) * logLevel) /
          (2 * users * comparisons * mass) ≤
        8 * Real.sqrt (users * logLevel / rateScale) / users := by
    apply (div_le_iff₀ hden_pos).2
    calc
      2 * Real.sqrt (8 * (2 * users * comparisons * mass) * logLevel) ≤
          2 * (8 * comparisons * mass * Real.sqrt (users * logLevel / rateScale)) :=
            mul_le_mul_of_nonneg_left hroot' (by norm_num)
      _ = (8 * Real.sqrt (users * logLevel / rateScale) / users) *
          (2 * users * comparisons * mass) := by
            field_simp [ne_of_gt husers_pos]
  have hlinear_normalized :
      2 * (8 * logLevel) / (2 * users * comparisons * mass) ≤
        8 * logLevel / (users * minimumMass) := by
    have hden_right : 0 < users * minimumMass := by positivity
    have hmass_scale : users * minimumMass ≤ users * comparisons * mass := by
      calc
        users * minimumMass ≤ users * mass :=
          mul_le_mul_of_nonneg_left hminimumMass_le_mass husers_pos.le
        _ ≤ users * comparisons * mass := by
          have : mass ≤ comparisons * mass := by
            calc
              mass = 1 * mass := by ring
              _ ≤ comparisons * mass := mul_le_mul_of_nonneg_right hcomparisons_one hmass_nonneg
          nlinarith
    calc
      2 * (8 * logLevel) / (2 * users * comparisons * mass) =
          (8 * logLevel) / (users * comparisons * mass) := by
            field_simp [ne_of_gt husers_pos, ne_of_gt hcomparisons_pos,
              ne_of_gt hmass_pos] <;> ring
      _ ≤ 8 * logLevel / (users * minimumMass) := by
        apply (div_le_div_iff₀ (by positivity) hden_right).2
        have hscaled := mul_le_mul_of_nonneg_left hmass_scale
          (show 0 ≤ 8 * logLevel by positivity)
        nlinarith
  calc
    2 * (Real.sqrt (8 * (2 * users * comparisons * mass) * logLevel) + 8 * logLevel) /
        (2 * users * comparisons * mass) =
        2 * Real.sqrt (8 * (2 * users * comparisons * mass) * logLevel) /
            (2 * users * comparisons * mass) +
          2 * (8 * logLevel) / (2 * users * comparisons * mass) := by ring
    _ ≤ 8 * Real.sqrt (users * logLevel / rateScale) / users +
          8 * logLevel / (users * minimumMass) :=
            add_le_add hroot_normalized hlinear_normalized
    _ = 8 * Real.sqrt (users * logLevel /
          min 1 (comparisons * minimumMass ^ 2)) / users +
        8 * logLevel / (users * minimumMass) := by rfl

/--
The deterministic radius algebra shared by the fixed-alternative and uniform
forms of Lemma 11.  It combines the sharp raw-Borda envelope with the separate
endpoint-incidence Bernstein quantile after normalization by the exact mean.
-/
private theorem theorem11_sharpNormalizedQuantile_le_sourceRate
    {users comparisons mass minimumMass alternativesCard logLevel : ℝ}
    (husers_pos : 0 < users) (hcomparisons_pos : 0 < comparisons)
    (hcomparisons_one : 1 ≤ comparisons)
    (hmass_pos : 0 < mass) (hmass_le_one : mass ≤ 1)
    (hminimumMass_pos : 0 < minimumMass) (hminimumMass_le_mass : minimumMass ≤ mass)
    (halternativesCard_nonneg : 0 ≤ alternativesCard)
    (hlogLevel_nonneg : 0 ≤ logLevel) :
    2 *
        (12 * comparisons * mass *
            Real.sqrt (users * logLevel / min 1 (comparisons * minimumMass ^ 2)) +
          8 * alternativesCard * comparisons * logLevel +
          (Real.sqrt (8 * (2 * users * comparisons * mass) * logLevel) + 8 * logLevel)) /
        (2 * users * comparisons * mass) ≤
      20 * Real.sqrt (users * logLevel / min 1 (comparisons * minimumMass ^ 2)) / users +
        8 * (alternativesCard + 1) * logLevel / (users * minimumMass) := by
  have hincidence := theorem11_incidenceQuantile_normalized_le_rateEnvelope
    (users := users) (comparisons := comparisons) (mass := mass)
    (minimumMass := minimumMass) (logLevel := logLevel) husers_pos hcomparisons_pos
    hcomparisons_one hmass_pos hmass_le_one hminimumMass_pos hminimumMass_le_mass hlogLevel_nonneg
  have husers_minimumMass_le : users * minimumMass ≤ users * mass :=
    mul_le_mul_of_nonneg_left hminimumMass_le_mass husers_pos.le
  have hraw_linear_rate :
      8 * alternativesCard * logLevel / (users * mass) ≤
        8 * alternativesCard * logLevel / (users * minimumMass) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hscaled := mul_le_mul_of_nonneg_left husers_minimumMass_le
      (show 0 ≤ 8 * alternativesCard * logLevel by positivity)
    nlinarith
  have hraw_rate :
      2 *
          (12 * comparisons * mass *
              Real.sqrt (users * logLevel / min 1 (comparisons * minimumMass ^ 2)) +
            8 * alternativesCard * comparisons * logLevel) /
          (2 * users * comparisons * mass) ≤
        12 * Real.sqrt (users * logLevel / min 1 (comparisons * minimumMass ^ 2)) / users +
          8 * alternativesCard * logLevel / (users * minimumMass) := by
    calc
      2 *
          (12 * comparisons * mass *
              Real.sqrt (users * logLevel / min 1 (comparisons * minimumMass ^ 2)) +
            8 * alternativesCard * comparisons * logLevel) /
          (2 * users * comparisons * mass) =
          12 * Real.sqrt (users * logLevel / min 1 (comparisons * minimumMass ^ 2)) / users +
            8 * alternativesCard * logLevel / (users * mass) := by
              field_simp [ne_of_gt husers_pos, ne_of_gt hcomparisons_pos, ne_of_gt hmass_pos]
      _ ≤ 12 * Real.sqrt (users * logLevel / min 1 (comparisons * minimumMass ^ 2)) / users +
          8 * alternativesCard * logLevel / (users * minimumMass) :=
            by simpa [add_comm] using
              add_le_add_left hraw_linear_rate
                (12 * Real.sqrt (users * logLevel /
                  min 1 (comparisons * minimumMass ^ 2)) / users)
  calc
    2 *
        (12 * comparisons * mass *
            Real.sqrt (users * logLevel / min 1 (comparisons * minimumMass ^ 2)) +
          8 * alternativesCard * comparisons * logLevel +
          (Real.sqrt (8 * (2 * users * comparisons * mass) * logLevel) + 8 * logLevel)) /
        (2 * users * comparisons * mass) =
        2 *
            (12 * comparisons * mass *
                Real.sqrt (users * logLevel / min 1 (comparisons * minimumMass ^ 2)) +
              8 * alternativesCard * comparisons * logLevel) /
            (2 * users * comparisons * mass) +
          2 * (Real.sqrt (8 * (2 * users * comparisons * mass) * logLevel) + 8 * logLevel) /
            (2 * users * comparisons * mass) := by ring
    _ ≤ (12 * Real.sqrt (users * logLevel /
          min 1 (comparisons * minimumMass ^ 2)) / users +
          8 * alternativesCard * logLevel / (users * minimumMass)) +
        (8 * Real.sqrt (users * logLevel /
          min 1 (comparisons * minimumMass ^ 2)) / users +
          8 * logLevel / (users * minimumMass)) :=
            add_le_add hraw_rate hincidence
    _ = 20 * Real.sqrt (users * logLevel /
          min 1 (comparisons * minimumMass ^ 2)) / users +
        8 * (alternativesCard + 1) * logLevel / (users * minimumMass) := by ring

/--
Minimum-mass envelope for one distinct-opponent Borda quantile.  The
`μ_min²` lower bound is used only in the variance-rate simplification, while
the leading factor retains the actual pair incidence `q(x,y)` for summation.
-/
theorem theorem11DistinctPairBernsteinQuantile_le_minMassEnvelope
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (first second : Alternative) (minimumMass logLevel : ℝ)
    (husers_pos : 0 < users) (hcomparisons_pos : 0 < comparisonsPerUser)
    (hminimumMass_pos : 0 < minimumMass)
    (hminimumMass_first : minimumMass ≤ (sampling first).toReal)
    (hminimumMass_second : minimumMass ≤ (sampling second).toReal)
    (hlogLevel_nonneg : 0 ≤ logLevel) :
    theorem11DistinctPairBernsteinQuantile sampling users comparisonsPerUser first second logLevel ≤
      4 * (comparisonsPerUser : ℝ) *
        theorem10FixedPairIncidenceProbability sampling first second *
          Real.sqrt ((users : ℝ) * logLevel /
            min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) +
        8 * (comparisonsPerUser : ℝ) * logLevel := by
  let q : ℝ := theorem10FixedPairIncidenceProbability sampling first second
  let varianceProxy : ℝ := theorem10FixedPairVarianceProxy sampling comparisonsPerUser first second
  let rateScale : ℝ := min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)
  have hfirst_nonneg : 0 ≤ (sampling first).toReal := ENNReal.toReal_nonneg
  have hminimumMass_sq_pos : 0 < minimumMass ^ 2 := sq_pos_of_pos hminimumMass_pos
  have hmass_product_lower : minimumMass ^ 2 ≤
      (sampling first).toReal * (sampling second).toReal := by
    calc
      minimumMass ^ 2 = minimumMass * minimumMass := by ring
      _ ≤ (sampling first).toReal * minimumMass :=
        mul_le_mul_of_nonneg_right hminimumMass_first hminimumMass_pos.le
      _ ≤ (sampling first).toReal * (sampling second).toReal :=
        mul_le_mul_of_nonneg_left hminimumMass_second hfirst_nonneg
  have hq_pos : 0 < q := by
    dsimp [q, theorem10FixedPairIncidenceProbability]
    nlinarith
  have hminimumMass_sq_le_q : minimumMass ^ 2 ≤ q := by
    dsimp [q, theorem10FixedPairIncidenceProbability]
    nlinarith
  have hrateScale_pos : 0 < rateScale := by
    dsimp [rateScale]
    exact lt_min (by norm_num) (by positivity)
  have hrateScale_le_one : rateScale ≤ 1 := min_le_left _ _
  have hrateScale_le_comparisons_q : rateScale ≤ (comparisonsPerUser : ℝ) * q := by
    calc
      rateScale ≤ (comparisonsPerUser : ℝ) * minimumMass ^ 2 := min_le_right _ _
      _ ≤ (comparisonsPerUser : ℝ) * q :=
        mul_le_mul_of_nonneg_left hminimumMass_sq_le_q (by positivity)
  have hpredecessor_le : ((comparisonsPerUser - 1 : ℕ) : ℝ) ≤ comparisonsPerUser := by
    exact_mod_cast Nat.sub_le comparisonsPerUser 1
  have hvariance_nonneg : 0 ≤ varianceProxy := by
    dsimp [varianceProxy, theorem10FixedPairVarianceProxy,
      theorem10FixedPairIncidenceProbability]
    positivity
  have hvariance_le : varianceProxy ≤
      (comparisonsPerUser : ℝ) * q * (1 + (comparisonsPerUser : ℝ) * q) := by
    have hquadratic_le :
        (comparisonsPerUser : ℝ) * ((comparisonsPerUser - 1 : ℕ) : ℝ) * q ^ 2 ≤
          (comparisonsPerUser : ℝ) ^ 2 * q ^ 2 := by
      calc
        (comparisonsPerUser : ℝ) * ((comparisonsPerUser - 1 : ℕ) : ℝ) * q ^ 2 ≤
            (comparisonsPerUser : ℝ) * (comparisonsPerUser : ℝ) * q ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpredecessor_le (by positivity))
            (sq_nonneg q)
        _ = (comparisonsPerUser : ℝ) ^ 2 * q ^ 2 := by ring
    dsimp [varianceProxy, theorem10FixedPairVarianceProxy, q]
    rw [show theorem10FixedPairIncidenceProbability sampling first second = q by rfl]
    nlinarith
  have hroot := theorem11_pairQuantileRoot_le_rateEnvelope
    (users := (users : ℝ)) (comparisons := (comparisonsPerUser : ℝ)) (q := q)
    (varianceProxy := varianceProxy) (rateScale := rateScale) (logLevel := logLevel)
    (by exact_mod_cast husers_pos) (by exact_mod_cast hcomparisons_pos) hq_pos hrateScale_pos
    hlogLevel_nonneg hvariance_nonneg hrateScale_le_one hrateScale_le_comparisons_q hvariance_le
  simpa [theorem11DistinctPairBernsteinQuantile, q, varianceProxy, rateScale,
    theorem10FixedPairIncidenceProbability, theorem10FixedPairVarianceProxy, mul_assoc] using
    (add_le_add_right hroot (8 * (comparisonsPerUser : ℝ) * logLevel))

/--
Minimum-mass envelope for the diagonal Borda quantile.  Its leading factor is
the actual sampling mass of the selected alternative, as required before
summing the off-diagonal terms.
-/
theorem theorem11DiagonalBernsteinQuantile_le_minMassEnvelope
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (alternative : Alternative) (minimumMass logLevel : ℝ)
    (husers_pos : 0 < users) (hcomparisons_pos : 0 < comparisonsPerUser)
    (hminimumMass_pos : 0 < minimumMass)
    (hminimumMass_alternative : minimumMass ≤ (sampling alternative).toReal)
    (hlogLevel_nonneg : 0 ≤ logLevel) :
    theorem11DiagonalBernsteinQuantile sampling users comparisonsPerUser alternative logLevel ≤
      4 * (comparisonsPerUser : ℝ) * (sampling alternative).toReal *
          Real.sqrt ((users : ℝ) * logLevel /
            min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) +
        8 * (comparisonsPerUser : ℝ) * logLevel := by
  let mass : ℝ := (sampling alternative).toReal
  let rateScale : ℝ := min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)
  have hmass_pos : 0 < mass := lt_of_lt_of_le hminimumMass_pos hminimumMass_alternative
  have hmass_le_one : mass ≤ 1 := pmf_apply_toReal_le_one sampling alternative
  have hminimumMass_sq_pos : 0 < minimumMass ^ 2 := sq_pos_of_pos hminimumMass_pos
  have hminimumMass_sq_le_mass : minimumMass ^ 2 ≤ mass := by
    calc
      minimumMass ^ 2 = minimumMass * minimumMass := by ring
      _ ≤ mass * minimumMass :=
        mul_le_mul_of_nonneg_right hminimumMass_alternative hminimumMass_pos.le
      _ ≤ mass * mass :=
        mul_le_mul_of_nonneg_left hminimumMass_alternative hmass_pos.le
      _ ≤ mass := by nlinarith
  have hrateScale_pos : 0 < rateScale := by
    dsimp [rateScale]
    exact lt_min (by norm_num) (by positivity)
  have hrateScale_le_one : rateScale ≤ 1 := min_le_left _ _
  have hrateScale_le_comparisons_mass : rateScale ≤ (comparisonsPerUser : ℝ) * mass := by
    calc
      rateScale ≤ (comparisonsPerUser : ℝ) * minimumMass ^ 2 := min_le_right _ _
      _ ≤ (comparisonsPerUser : ℝ) * mass :=
        mul_le_mul_of_nonneg_left hminimumMass_sq_le_mass (by positivity)
  have hvariance_nonneg : 0 ≤ (comparisonsPerUser : ℝ) ^ 2 * mass ^ 2 := by positivity
  have hvariance_le : (comparisonsPerUser : ℝ) ^ 2 * mass ^ 2 ≤
      (comparisonsPerUser : ℝ) * mass * (1 + (comparisonsPerUser : ℝ) * mass) := by
    have hmain : 0 ≤ (comparisonsPerUser : ℝ) * mass := by positivity
    nlinarith
  have hroot := theorem11_pairQuantileRoot_le_rateEnvelope
    (users := (users : ℝ)) (comparisons := (comparisonsPerUser : ℝ)) (q := mass)
    (varianceProxy := (comparisonsPerUser : ℝ) ^ 2 * mass ^ 2)
    (rateScale := rateScale) (logLevel := logLevel)
    (by exact_mod_cast husers_pos) (by exact_mod_cast hcomparisons_pos) hmass_pos hrateScale_pos
    hlogLevel_nonneg hvariance_nonneg hrateScale_le_one hrateScale_le_comparisons_mass hvariance_le
  simpa [theorem11DiagonalBernsteinQuantile, mass, rateScale, mul_assoc] using
    (add_le_add_right hroot (8 * (comparisonsPerUser : ℝ) * logLevel))

/--
The diagonal-plus-opponent quantile sum has the source Lemma 11
minimum-mass envelope.  Keeping the selected alternative's actual mass in
front is what permits the later normalization by its Borda incidence count.
-/
theorem theorem11_bordaQuantileSum_le_minMassEnvelope
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (alternative : Alternative) (minimumMass logLevel : ℝ)
    (husers_pos : 0 < users) (hcomparisons_pos : 0 < comparisonsPerUser)
    (hminimumMass_pos : 0 < minimumMass)
    (hminimumMass : ∀ opponent, minimumMass ≤ (sampling opponent).toReal)
    (hlogLevel_nonneg : 0 ≤ logLevel) :
    theorem11DiagonalBernsteinQuantile sampling users comparisonsPerUser alternative logLevel +
      (∑ opponent ∈ Finset.univ.erase alternative,
        theorem11DistinctPairBernsteinQuantile sampling users comparisonsPerUser
          alternative opponent logLevel) ≤
      12 * (comparisonsPerUser : ℝ) * (sampling alternative).toReal *
          Real.sqrt ((users : ℝ) * logLevel /
            min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) +
        8 * (Fintype.card Alternative : ℝ) * (comparisonsPerUser : ℝ) * logLevel := by
  let mass : ℝ := (sampling alternative).toReal
  let rateScale : ℝ := min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)
  let root : ℝ := Real.sqrt ((users : ℝ) * logLevel / rateScale)
  let linear : ℝ := 8 * (comparisonsPerUser : ℝ) * logLevel
  have hmass_nonneg : 0 ≤ mass := ENNReal.toReal_nonneg
  have hroot_nonneg : 0 ≤ root := Real.sqrt_nonneg _
  have hlinear_nonneg : 0 ≤ linear := by
    dsimp [linear]
    positivity
  have hdiagonal := theorem11DiagonalBernsteinQuantile_le_minMassEnvelope sampling users
    comparisonsPerUser alternative minimumMass logLevel husers_pos hcomparisons_pos
    hminimumMass_pos (hminimumMass alternative) hlogLevel_nonneg
  have hpair : ∀ opponent, opponent ∈ Finset.univ.erase alternative →
      theorem11DistinctPairBernsteinQuantile sampling users comparisonsPerUser
          alternative opponent logLevel ≤
        4 * (comparisonsPerUser : ℝ) *
          theorem10FixedPairIncidenceProbability sampling alternative opponent * root + linear := by
    intro opponent _
    simpa [root, rateScale, linear] using
      (theorem11DistinctPairBernsteinQuantile_le_minMassEnvelope sampling users
        comparisonsPerUser alternative opponent minimumMass logLevel husers_pos hcomparisons_pos
        hminimumMass_pos (hminimumMass alternative) (hminimumMass opponent) hlogLevel_nonneg)
  have hmass_sum : (∑ opponent : Alternative, (sampling opponent).toReal) = 1 :=
    pmfToRealSum sampling
  have herase_mass_sum :
      (∑ opponent ∈ Finset.univ.erase alternative, (sampling opponent).toReal) + mass = 1 := by
    calc
      (∑ opponent ∈ Finset.univ.erase alternative, (sampling opponent).toReal) + mass =
          ∑ opponent : Alternative, (sampling opponent).toReal := by
            simpa [mass] using
              (Finset.sum_erase_add (Finset.univ : Finset Alternative)
                (fun opponent => (sampling opponent).toReal) (Finset.mem_univ alternative))
      _ = 1 := hmass_sum
  have herase_mass_le_one :
      ∑ opponent ∈ Finset.univ.erase alternative, (sampling opponent).toReal ≤ 1 := by
    linarith
  have hincidence_sum :
      ∑ opponent ∈ Finset.univ.erase alternative,
        theorem10FixedPairIncidenceProbability sampling alternative opponent ≤ 2 * mass := by
    change ∑ opponent ∈ Finset.univ.erase alternative,
        2 * mass * (sampling opponent).toReal ≤ 2 * mass
    calc
      (∑ opponent ∈ Finset.univ.erase alternative,
          2 * mass * (sampling opponent).toReal) =
          2 * mass * (∑ opponent ∈ Finset.univ.erase alternative,
            (sampling opponent).toReal) := by
              rw [Finset.mul_sum]
      _ ≤ 2 * mass * 1 :=
        mul_le_mul_of_nonneg_left herase_mass_le_one (by positivity)
      _ = 2 * mass := by ring
  have hroot_sum :
      (∑ opponent ∈ Finset.univ.erase alternative,
        4 * (comparisonsPerUser : ℝ) *
          theorem10FixedPairIncidenceProbability sampling alternative opponent * root) =
        4 * (comparisonsPerUser : ℝ) * root *
          (∑ opponent ∈ Finset.univ.erase alternative,
            theorem10FixedPairIncidenceProbability sampling alternative opponent) := by
    calc
      (∑ opponent ∈ Finset.univ.erase alternative,
          4 * (comparisonsPerUser : ℝ) *
            theorem10FixedPairIncidenceProbability sampling alternative opponent * root) =
          ∑ opponent ∈ Finset.univ.erase alternative,
            (4 * (comparisonsPerUser : ℝ) * root) *
              theorem10FixedPairIncidenceProbability sampling alternative opponent := by
              apply Finset.sum_congr rfl
              intro opponent _
              ring
      _ = 4 * (comparisonsPerUser : ℝ) * root *
          (∑ opponent ∈ Finset.univ.erase alternative,
            theorem10FixedPairIncidenceProbability sampling alternative opponent) := by
            rw [Finset.mul_sum]
  have hlinear_sum : linear + (∑ _opponent ∈ Finset.univ.erase alternative, linear) =
      (Fintype.card Alternative : ℝ) * linear := by
    calc
      linear + (∑ _opponent ∈ Finset.univ.erase alternative, linear) =
          (∑ _opponent ∈ Finset.univ.erase alternative, linear) + linear := by ring
      _ = ∑ _opponent : Alternative, linear := by
        simpa using
          (Finset.sum_erase_add (Finset.univ : Finset Alternative)
            (fun _opponent => linear) (Finset.mem_univ alternative))
      _ = (Fintype.card Alternative : ℝ) * linear := by
        simp [nsmul_eq_mul]
  have hroot_envelope :
      4 * (comparisonsPerUser : ℝ) * mass * root +
        (∑ opponent ∈ Finset.univ.erase alternative,
          4 * (comparisonsPerUser : ℝ) *
            theorem10FixedPairIncidenceProbability sampling alternative opponent * root) ≤
        12 * (comparisonsPerUser : ℝ) * mass * root := by
    rw [hroot_sum]
    calc
      4 * (comparisonsPerUser : ℝ) * mass * root +
          4 * (comparisonsPerUser : ℝ) * root *
            (∑ opponent ∈ Finset.univ.erase alternative,
              theorem10FixedPairIncidenceProbability sampling alternative opponent) ≤
          4 * (comparisonsPerUser : ℝ) * mass * root +
            4 * (comparisonsPerUser : ℝ) * root * (2 * mass) := by
              gcongr
      _ = 12 * (comparisonsPerUser : ℝ) * mass * root := by ring
  calc
    theorem11DiagonalBernsteinQuantile sampling users comparisonsPerUser alternative logLevel +
        (∑ opponent ∈ Finset.univ.erase alternative,
          theorem11DistinctPairBernsteinQuantile sampling users comparisonsPerUser
            alternative opponent logLevel) ≤
        (4 * (comparisonsPerUser : ℝ) * mass * root + linear) +
          ∑ opponent ∈ Finset.univ.erase alternative,
            (4 * (comparisonsPerUser : ℝ) *
              theorem10FixedPairIncidenceProbability sampling alternative opponent * root + linear) := by
          apply add_le_add hdiagonal
          apply Finset.sum_le_sum
          intro opponent hopponent
          exact hpair opponent hopponent
    _ = (4 * (comparisonsPerUser : ℝ) * mass * root +
          ∑ opponent ∈ Finset.univ.erase alternative,
            4 * (comparisonsPerUser : ℝ) *
              theorem10FixedPairIncidenceProbability sampling alternative opponent * root) +
          (linear + ∑ _opponent ∈ Finset.univ.erase alternative, linear) := by
          rw [Finset.sum_add_distrib]
          ring
    _ ≤ 12 * (comparisonsPerUser : ℝ) * mass * root +
          (linear + ∑ _opponent ∈ Finset.univ.erase alternative, linear) := by
          simpa only [add_assoc, add_left_comm, add_comm] using
            (add_le_add_right hroot_envelope
              (linear + ∑ _opponent ∈ Finset.univ.erase alternative, linear))
    _ = 12 * (comparisonsPerUser : ℝ) * mass *
          Real.sqrt ((users : ℝ) * logLevel /
            min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) +
        8 * (Fintype.card Alternative : ℝ) * (comparisonsPerUser : ℝ) * logLevel := by
          rw [hlinear_sum]
          dsimp [root, rateScale, linear]
          ring

/--
Confidence-level form of the source-sharp centered Borda numerator tail.
The displayed quantiles are explicit; the conclusion is a finite union bound
over the diagonal and the distinct opponents of the selected alternative.
-/
theorem theorem11_iidUserBordaPairwiseCentered_absTail_quantile
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {preference : PairwisePreference PUnit Alternative}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (alternative : Alternative) (logLevel : ℝ) (hlogLevel_nonneg : 0 ≤ logLevel)
    (hdiagonalDen_pos : 0 < (users : ℝ) *
      ((comparisonsPerUser : ℝ) ^ 2 * (sampling alternative).toReal ^ 2) +
      (comparisonsPerUser : ℝ) *
        theorem11DiagonalBernsteinQuantile sampling users comparisonsPerUser alternative logLevel)
    (hpairDen_pos : ∀ opponent, opponent ∈ Finset.univ.erase alternative → 0 <
      (users : ℝ) * theorem10FixedPairVarianceProxy sampling comparisonsPerUser
        alternative opponent + (comparisonsPerUser : ℝ) *
          theorem11DistinctPairBernsteinQuantile sampling users comparisonsPerUser
            alternative opponent logLevel) :
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample => theorem11DiagonalBernsteinQuantile sampling users comparisonsPerUser
          alternative logLevel +
        (∑ opponent ∈ Finset.univ.erase alternative,
          theorem11DistinctPairBernsteinQuantile sampling users comparisonsPerUser
            alternative opponent logLevel) ≤
          |theorem11IidUserBordaPairwiseCentered sampling preference alternative sample|) ≤
      2 * Real.exp (-logLevel) +
        ∑ opponent ∈ Finset.univ.erase alternative, 2 * Real.exp (-logLevel) := by
  have hdiagonalQuantile_nonneg : 0 ≤
      theorem11DiagonalBernsteinQuantile sampling users comparisonsPerUser alternative logLevel := by
    unfold theorem11DiagonalBernsteinQuantile
    positivity
  have hpairQuantile_nonneg : ∀ opponent, 0 ≤
      theorem11DistinctPairBernsteinQuantile sampling users comparisonsPerUser
        alternative opponent logLevel := by
    intro opponent
    unfold theorem11DistinctPairBernsteinQuantile
    positivity
  have htail := theorem11_iidUserBordaPairwiseCentered_absTail_bernstein hcalibrated sampling
    users comparisonsPerUser alternative
    (theorem11DiagonalBernsteinQuantile sampling users comparisonsPerUser alternative logLevel)
    (fun opponent => theorem11DistinctPairBernsteinQuantile sampling users comparisonsPerUser
      alternative opponent logLevel)
    hdiagonalQuantile_nonneg hpairQuantile_nonneg hdiagonalDen_pos hpairDen_pos
  calc
    pmfProb
        (pmfProduct (Fin users)
          (theorem2UserResponseTable Alternative ×
            (Fin comparisonsPerUser → Alternative × Alternative))
          (pmfProd responseLaw
            (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
              (theorem2UserPairLabelLaw sampling))))
        (fun sample => theorem11DiagonalBernsteinQuantile sampling users comparisonsPerUser
            alternative logLevel +
          (∑ opponent ∈ Finset.univ.erase alternative,
            theorem11DistinctPairBernsteinQuantile sampling users comparisonsPerUser
              alternative opponent logLevel) ≤
            |theorem11IidUserBordaPairwiseCentered sampling preference alternative sample|) ≤
        2 * Real.exp
          (-(theorem11DiagonalBernsteinQuantile sampling users comparisonsPerUser
            alternative logLevel) ^ 2 /
            (4 * ((users : ℝ) *
              ((comparisonsPerUser : ℝ) ^ 2 * (sampling alternative).toReal ^ 2) +
              (comparisonsPerUser : ℝ) * theorem11DiagonalBernsteinQuantile sampling users
                comparisonsPerUser alternative logLevel))) +
          ∑ opponent ∈ Finset.univ.erase alternative,
            2 * Real.exp
              (-(theorem11DistinctPairBernsteinQuantile sampling users comparisonsPerUser
                alternative opponent logLevel) ^ 2 /
                (4 * ((users : ℝ) * theorem10FixedPairVarianceProxy sampling comparisonsPerUser
                  alternative opponent + (comparisonsPerUser : ℝ) *
                    theorem11DistinctPairBernsteinQuantile sampling users comparisonsPerUser
                      alternative opponent logLevel))) := htail
    _ ≤ 2 * Real.exp (-logLevel) +
        ∑ opponent ∈ Finset.univ.erase alternative, 2 * Real.exp (-logLevel) := by
      apply add_le_add
      · let totalVariance : ℝ := (users : ℝ) *
            ((comparisonsPerUser : ℝ) ^ 2 * (sampling alternative).toReal ^ 2)
        let cutoff : ℝ := Real.sqrt (8 * totalVariance * logLevel) +
          8 * (comparisonsPerUser : ℝ) * logLevel
        have hcutoff : theorem11DiagonalBernsteinQuantile sampling users comparisonsPerUser
            alternative logLevel = cutoff := by rfl
        have hden : 0 < totalVariance + (comparisonsPerUser : ℝ) * cutoff := by
          simpa only [totalVariance, cutoff, theorem11DiagonalBernsteinQuantile] using
            hdiagonalDen_pos
        rw [hcutoff]
        exact bernstein_two_sided_exponential_at_quantile_le
          (totalVariance := totalVariance) (bound := (comparisonsPerUser : ℝ))
          (logLevel := logLevel) (by positivity) (by positivity) hlogLevel_nonneg hden
      · apply Finset.sum_le_sum
        intro opponent hopponent
        let totalVariance : ℝ := (users : ℝ) *
          theorem10FixedPairVarianceProxy sampling comparisonsPerUser alternative opponent
        let cutoff : ℝ := Real.sqrt (8 * totalVariance * logLevel) +
          8 * (comparisonsPerUser : ℝ) * logLevel
        have hcutoff : theorem11DistinctPairBernsteinQuantile sampling users comparisonsPerUser
            alternative opponent logLevel = cutoff := by rfl
        have hden : 0 < totalVariance + (comparisonsPerUser : ℝ) * cutoff := by
          simpa only [totalVariance, cutoff, theorem11DistinctPairBernsteinQuantile] using
            hpairDen_pos opponent hopponent
        rw [hcutoff]
        exact bernstein_two_sided_exponential_at_quantile_le
          (totalVariance := totalVariance) (bound := (comparisonsPerUser : ℝ))
          (logLevel := logLevel) (by
            dsimp [totalVariance]
            unfold theorem10FixedPairVarianceProxy theorem10FixedPairIncidenceProbability
            positivity)
          (by positivity) hlogLevel_nonneg hden

/--
Source-sharp minimum-mass tail for the centered raw Borda numerator of one
alternative.  This is Appendix D, Lemma 11's variance-sensitive numerator
bound before the deterministic ratio normalization.
-/
theorem theorem11_iidUserBordaPairwiseCentered_minMass_tail
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {preference : PairwisePreference PUnit Alternative}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (alternative : Alternative) (minimumMass logLevel : ℝ)
    (husers_pos : 0 < users) (hcomparisons_pos : 0 < comparisonsPerUser)
    (hminimumMass_pos : 0 < minimumMass)
    (hminimumMass : ∀ opponent, minimumMass ≤ (sampling opponent).toReal)
    (hlogLevel_nonneg : 0 ≤ logLevel) :
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample =>
        12 * (comparisonsPerUser : ℝ) * (sampling alternative).toReal *
            Real.sqrt ((users : ℝ) * logLevel /
              min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) +
          8 * (Fintype.card Alternative : ℝ) * (comparisonsPerUser : ℝ) * logLevel ≤
          |theorem11IidUserBordaPairwiseCentered sampling preference alternative sample|) ≤
      2 * (Fintype.card Alternative : ℝ) * Real.exp (-logLevel) := by
  classical
  let mass : ℝ := (sampling alternative).toReal
  let rateScale : ℝ := min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)
  let envelope : ℝ :=
    12 * (comparisonsPerUser : ℝ) * mass *
      Real.sqrt ((users : ℝ) * logLevel / rateScale) +
    8 * (Fintype.card Alternative : ℝ) * (comparisonsPerUser : ℝ) * logLevel
  have hmass_pos : 0 < mass := lt_of_lt_of_le hminimumMass_pos (hminimumMass alternative)
  have hdiagonalDen_pos : 0 < (users : ℝ) *
      ((comparisonsPerUser : ℝ) ^ 2 * (sampling alternative).toReal ^ 2) +
      (comparisonsPerUser : ℝ) *
        theorem11DiagonalBernsteinQuantile sampling users comparisonsPerUser alternative logLevel := by
    have htotal_pos : 0 < (users : ℝ) *
        ((comparisonsPerUser : ℝ) ^ 2 * (sampling alternative).toReal ^ 2) := by
      dsimp [mass] at hmass_pos
      positivity
    have hquantile_nonneg : 0 ≤ theorem11DiagonalBernsteinQuantile sampling users
        comparisonsPerUser alternative logLevel := by
      unfold theorem11DiagonalBernsteinQuantile
      positivity
    positivity
  have hpairDen_pos : ∀ opponent, opponent ∈ Finset.univ.erase alternative → 0 <
      (users : ℝ) * theorem10FixedPairVarianceProxy sampling comparisonsPerUser
        alternative opponent + (comparisonsPerUser : ℝ) *
          theorem11DistinctPairBernsteinQuantile sampling users comparisonsPerUser
            alternative opponent logLevel := by
    intro opponent _
    have hopponent_pos : 0 < (sampling opponent).toReal :=
      lt_of_lt_of_le hminimumMass_pos (hminimumMass opponent)
    have hvariance_pos : 0 < theorem10FixedPairVarianceProxy sampling comparisonsPerUser
        alternative opponent := by
      unfold theorem10FixedPairVarianceProxy theorem10FixedPairIncidenceProbability
      positivity
    have hquantile_nonneg : 0 ≤ theorem11DistinctPairBernsteinQuantile sampling users
        comparisonsPerUser alternative opponent logLevel := by
      unfold theorem11DistinctPairBernsteinQuantile
      positivity
    positivity
  have hquantile_tail := theorem11_iidUserBordaPairwiseCentered_absTail_quantile hcalibrated
    sampling users comparisonsPerUser alternative logLevel hlogLevel_nonneg hdiagonalDen_pos
    hpairDen_pos
  have henvelope := theorem11_bordaQuantileSum_le_minMassEnvelope sampling users
    comparisonsPerUser alternative minimumMass logLevel husers_pos hcomparisons_pos
    hminimumMass_pos hminimumMass hlogLevel_nonneg
  have htail_card :
      2 * Real.exp (-logLevel) +
        (∑ _opponent ∈ Finset.univ.erase alternative, 2 * Real.exp (-logLevel)) =
        2 * (Fintype.card Alternative : ℝ) * Real.exp (-logLevel) := by
    calc
      2 * Real.exp (-logLevel) +
          (∑ _opponent ∈ Finset.univ.erase alternative, 2 * Real.exp (-logLevel)) =
          (∑ _opponent ∈ Finset.univ.erase alternative, 2 * Real.exp (-logLevel)) +
            2 * Real.exp (-logLevel) := by ring
      _ = ∑ _opponent : Alternative, 2 * Real.exp (-logLevel) := by
        simpa using
          (Finset.sum_erase_add (Finset.univ : Finset Alternative)
            (fun _opponent => 2 * Real.exp (-logLevel)) (Finset.mem_univ alternative))
      _ = 2 * (Fintype.card Alternative : ℝ) * Real.exp (-logLevel) := by
        simp [nsmul_eq_mul]
        ring
  let quantileEvent :
      (Fin users → (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) → Prop := fun sample =>
      theorem11DiagonalBernsteinQuantile sampling users comparisonsPerUser alternative logLevel +
        (∑ opponent ∈ Finset.univ.erase alternative,
          theorem11DistinctPairBernsteinQuantile sampling users comparisonsPerUser
            alternative opponent logLevel) ≤
          |theorem11IidUserBordaPairwiseCentered sampling preference alternative sample|
  let envelopeEvent :
      (Fin users → (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) → Prop := fun sample =>
      envelope ≤ |theorem11IidUserBordaPairwiseCentered sampling preference alternative sample|
  have hsubset : ∀ sample, envelopeEvent sample → quantileEvent sample := by
    intro sample hlarge
    dsimp [envelopeEvent, quantileEvent, envelope] at hlarge ⊢
    exact le_trans henvelope hlarge
  change pmfProb _ envelopeEvent ≤ _
  calc
    pmfProb
        (pmfProduct (Fin users)
          (theorem2UserResponseTable Alternative ×
            (Fin comparisonsPerUser → Alternative × Alternative))
          (pmfProd responseLaw
            (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
              (theorem2UserPairLabelLaw sampling)))) envelopeEvent ≤
        pmfProb
          (pmfProduct (Fin users)
            (theorem2UserResponseTable Alternative ×
              (Fin comparisonsPerUser → Alternative × Alternative))
            (pmfProd responseLaw
              (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
                (theorem2UserPairLabelLaw sampling)))) quantileEvent := by
          apply pmfProb_le_of_imp
          exact hsubset
    _ ≤ 2 * Real.exp (-logLevel) +
          (∑ _opponent ∈ Finset.univ.erase alternative, 2 * Real.exp (-logLevel)) := by
            simpa [quantileEvent] using hquantile_tail
    _ = 2 * (Fintype.card Alternative : ℝ) * Real.exp (-logLevel) := htail_card

/-- Total Borda incidences in the literal latent source sample. -/
def theorem11IidUserLatentBordaIncidences
    {Alternative : Type*} [DecidableEq Alternative] {users comparisonsPerUser : ℕ}
    (alternative : Alternative)
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) : ℝ :=
  ∑ user, theorem2UserBatchBordaIncidences alternative
    (fun position => ((sample user).2 position,
      (sample user).1 ((sample user).2 position).1 ((sample user).2 position).2))

/-- Borda incidences depend only on displayed labels, not on their answer bits. -/
theorem theorem11_iidUserLatentBordaIncidences_eq_labelOnly
    {Alternative : Type*} [DecidableEq Alternative] {users comparisonsPerUser : ℕ}
    (alternative : Alternative)
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) :
    theorem11IidUserLatentBordaIncidences alternative sample =
      ∑ user, theorem2UserBatchBordaIncidences alternative
        (fun position => ((sample user).2 position, false)) := by
  unfold theorem11IidUserLatentBordaIncidences theorem2UserBatchBordaIncidences
  apply Finset.sum_congr rfl
  intro user _
  apply Finset.sum_congr rfl
  intro position _
  rfl

/-- The raw source Borda score, with the standard zero-denominator convention. -/
noncomputable def theorem11IidUserLatentBordaScore
    {Alternative : Type*} [DecidableEq Alternative] {users comparisonsPerUser : ℕ}
    (alternative : Alternative)
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) : ℝ :=
  if theorem11IidUserLatentBordaIncidences alternative sample = 0 then 0 else
    theorem11IidUserLatentBordaWins alternative sample /
      theorem11IidUserLatentBordaIncidences alternative sample

/--
The literal answer-bearing denominator has the same half-mean Chernoff lower
tail as the label-only count used to establish it.
-/
theorem theorem11_iidUserLatentBordaIncidences_halfMean_lowerTail
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (alternative : Alternative) :
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample => theorem11IidUserLatentBordaIncidences alternative sample ≤
          ((users * comparisonsPerUser : ℕ) : ℝ) * (sampling alternative).toReal) ≤
      Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) *
        (sampling alternative).toReal / 4) := by
  simpa only [theorem11_iidUserLatentBordaIncidences_eq_labelOnly] using
    (theorem11_iidUserBordaIncidences_halfMean_lowerTail responseLaw sampling users
      comparisonsPerUser alternative)

/--
Two-sided Bernstein tail for the literal answer-bearing Borda-incidence count.
The proof first removes answer bits, then transports the event to the exact
`2nd` independent endpoint-label product law.
-/
theorem theorem11_iidUserLatentBordaIncidences_abs_centered_tail
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (alternative : Alternative) (cutoff : ℝ) (hcutoff_nonneg : 0 ≤ cutoff)
    (hden_pos : 0 <
      (Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
        (sampling alternative).toReal + cutoff) :
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample => cutoff ≤
        |theorem11IidUserLatentBordaIncidences alternative sample -
          (Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
            (sampling alternative).toReal|) ≤
      2 * Real.exp (-cutoff ^ 2 /
        (4 * ((Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
          (sampling alternative).toReal + cutoff))) := by
  classical
  let event : ℝ → Prop := fun value => cutoff ≤
    |value - (Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
      (sampling alternative).toReal|
  letI : DecidablePred event := fun value => Classical.dec (event value)
  have hlabelOnly :
      pmfProb
        (pmfProduct (Fin users)
          (theorem2UserResponseTable Alternative ×
            (Fin comparisonsPerUser → Alternative × Alternative))
          (pmfProd responseLaw
            (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
              (theorem2UserPairLabelLaw sampling))))
        (fun sample => event (theorem11IidUserLatentBordaIncidences alternative sample)) =
      pmfProb
        (pmfProduct (Fin users)
          (theorem2UserResponseTable Alternative ×
            (Fin comparisonsPerUser → Alternative × Alternative))
          (pmfProd responseLaw
            (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
              (theorem2UserPairLabelLaw sampling))))
        (fun sample => event (∑ user,
          theorem2UserBatchBordaIncidences alternative
            (fun position => ((sample user).2 position, false)))) := by
          apply pmfProb_congr
          intro sample
          rw [theorem11_iidUserLatentBordaIncidences_eq_labelOnly]
  calc
    pmfProb
        (pmfProduct (Fin users)
          (theorem2UserResponseTable Alternative ×
            (Fin comparisonsPerUser → Alternative × Alternative))
          (pmfProd responseLaw
            (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
              (theorem2UserPairLabelLaw sampling))))
        (fun sample => cutoff ≤
          |theorem11IidUserLatentBordaIncidences alternative sample -
            (Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
              (sampling alternative).toReal|) =
      pmfProb
        (pmfProduct (Fin users)
          (theorem2UserResponseTable Alternative ×
            (Fin comparisonsPerUser → Alternative × Alternative))
          (pmfProd responseLaw
            (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
              (theorem2UserPairLabelLaw sampling))))
        (fun sample => event (theorem11IidUserLatentBordaIncidences alternative sample)) := by
          rfl
    _ = pmfProb
        (pmfProduct (Fin users)
          (theorem2UserResponseTable Alternative ×
            (Fin comparisonsPerUser → Alternative × Alternative))
          (pmfProd responseLaw
            (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
              (theorem2UserPairLabelLaw sampling))))
        (fun sample => event (∑ user,
          theorem2UserBatchBordaIncidences alternative
            (fun position => ((sample user).2 position, false)))) := hlabelOnly
    _ = pmfProb
        (pmfProduct ((Fin users × Fin comparisonsPerUser) × Bool) Alternative sampling)
        (fun labels => event (∑ index,
          if labels index = alternative then (1 : ℝ) else 0)) :=
      theorem11_iidUserBordaIncidences_pmfProb_eq_flatEndpoint responseLaw sampling users
        comparisonsPerUser alternative event
    _ ≤ 2 * Real.exp (-cutoff ^ 2 /
        (4 * ((Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
          (sampling alternative).toReal + cutoff))) := by
          simpa [event] using
            (theorem11_iidAlternativeIncidence_abs_centered_tail_flat sampling users
              comparisonsPerUser alternative cutoff hcutoff_nonneg hden_pos)

/-- Bernstein quantile for the literal `2nd` endpoint-label Borda denominator. -/
noncomputable def theorem11IncidenceBernsteinQuantile
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (alternative : Alternative) (logLevel : ℝ) : ℝ :=
  Real.sqrt (8 *
    ((Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
      (sampling alternative).toReal) * logLevel) + 8 * logLevel

/--
At its explicit quantile, the literal Borda-incidence denominator has failure
probability at most `2 exp(-L)`.
-/
theorem theorem11_iidUserLatentBordaIncidences_abs_centered_quantile_tail
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (alternative : Alternative) (logLevel : ℝ)
    (husers : 0 < users) (hcomparisons : 0 < comparisonsPerUser)
    (hsampling_pos : 0 < (sampling alternative).toReal) (hlogLevel_nonneg : 0 ≤ logLevel) :
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample => theorem11IncidenceBernsteinQuantile sampling users comparisonsPerUser
          alternative logLevel ≤
        |theorem11IidUserLatentBordaIncidences alternative sample -
          (Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
            (sampling alternative).toReal|) ≤
      2 * Real.exp (-logLevel) := by
  let meanIncidences : ℝ :=
    (Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
      (sampling alternative).toReal
  let cutoff : ℝ := theorem11IncidenceBernsteinQuantile sampling users comparisonsPerUser
    alternative logLevel
  have hmean_pos : 0 < meanIncidences := by
    dsimp [meanIncidences]
    simp [Fintype.card_prod, Fintype.card_fin]
    positivity
  have hcutoff_nonneg : 0 ≤ cutoff := by
    dsimp [cutoff, theorem11IncidenceBernsteinQuantile]
    positivity
  have hden_pos : 0 < meanIncidences + cutoff := by positivity
  have hden_quantile : 0 < meanIncidences + (1 : ℝ) *
      (Real.sqrt (8 * meanIncidences * logLevel) + 8 * (1 : ℝ) * logLevel) := by
    positivity
  have htail := theorem11_iidUserLatentBordaIncidences_abs_centered_tail
    responseLaw sampling users comparisonsPerUser alternative cutoff hcutoff_nonneg
    (by simpa [meanIncidences] using hden_pos)
  calc
    pmfProb
        (pmfProduct (Fin users)
          (theorem2UserResponseTable Alternative ×
            (Fin comparisonsPerUser → Alternative × Alternative))
          (pmfProd responseLaw
            (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
              (theorem2UserPairLabelLaw sampling))))
        (fun sample => cutoff ≤
          |theorem11IidUserLatentBordaIncidences alternative sample - meanIncidences|) ≤
      2 * Real.exp (-cutoff ^ 2 / (4 * (meanIncidences + cutoff))) := by
        simpa [meanIncidences] using htail
    _ ≤ 2 * Real.exp (-logLevel) := by
      change 2 * Real.exp
          (-(Real.sqrt (8 * meanIncidences * logLevel) + 8 * logLevel) ^ 2 /
            (4 * (meanIncidences + (Real.sqrt (8 * meanIncidences * logLevel) +
              8 * logLevel)))) ≤
        2 * Real.exp (-logLevel)
      simpa using (bernstein_two_sided_exponential_at_quantile_le
        (totalVariance := meanIncidences) (bound := (1 : ℝ)) (logLevel := logLevel)
        hmean_pos.le (by norm_num) hlogLevel_nonneg hden_quantile)


/-- One ordered comparison contributes at most two incidences to one alternative. -/
private theorem theorem11_oneComparisonIncidences_le_two
    {Alternative : Type*} [DecidableEq Alternative]
    (alternative : Alternative) (report : (Alternative × Alternative) × Bool) :
    theorem12OneComparisonIncidences alternative report ≤ 2 := by
  rcases report with ⟨⟨first, second⟩, outcome⟩
  by_cases hfirst : first = alternative <;> by_cases hsecond : second = alternative <;>
    simp [theorem12OneComparisonIncidences, hfirst, hsecond] <;> norm_num

/-- A source user contributes at most `2d` Borda incidences to one alternative. -/
theorem theorem11_userBatchBordaIncidences_le_two_mul_comparisons
    {Alternative : Type*} [DecidableEq Alternative] {comparisonsPerUser : ℕ}
    (alternative : Alternative) (report : theorem2UserBatchReport Alternative comparisonsPerUser) :
    theorem2UserBatchBordaIncidences alternative report ≤ 2 * comparisonsPerUser := by
  unfold theorem2UserBatchBordaIncidences
  calc
    (∑ position, theorem12OneComparisonIncidences alternative (report position)) ≤
        ∑ _position : Fin comparisonsPerUser, (2 : ℝ) := by
          apply Finset.sum_le_sum
          intro position _
          exact theorem11_oneComparisonIncidences_le_two alternative (report position)
    _ = 2 * comparisonsPerUser := by simp [nsmul_eq_mul]; ring

/-- A source user's Borda wins are likewise bounded by `2d`. -/
theorem theorem11_userBatchBordaWins_le_two_mul_comparisons
    {Alternative : Type*} [DecidableEq Alternative] {comparisonsPerUser : ℕ}
    (alternative : Alternative) (report : theorem2UserBatchReport Alternative comparisonsPerUser) :
    theorem2UserBatchBordaWins alternative report ≤ 2 * comparisonsPerUser :=
  (theorem2UserBatchBordaWins_le_incidences alternative report).trans
    (theorem11_userBatchBordaIncidences_le_two_mul_comparisons alternative report)

/--
Deterministic normalization with separate numerator and denominator errors.
This is the ratio step needed when the raw Borda numerator has its sharper
pairwise variance bound while the incidence denominator is binomial.
-/
theorem theorem11_normalizedBorda_error_le_of_asymmetric_errors_and_count_lower
    {wins incidences score meanWins meanIncidences winCutoff incidenceCutoff : ℝ}
    (hscore_nonneg : 0 ≤ score) (hscore_le_one : score ≤ 1)
    (hcalibrated : meanWins = score * meanIncidences)
    (hmeanIncidences_pos : 0 < meanIncidences)
    (hincidences_lower : meanIncidences / 2 ≤ incidences)
    (hwins_centered : |wins - meanWins| ≤ winCutoff)
    (hincidences_centered : |incidences - meanIncidences| ≤ incidenceCutoff)
    (hwinCutoff_nonneg : 0 ≤ winCutoff) (hincidenceCutoff_nonneg : 0 ≤ incidenceCutoff) :
    |wins / incidences - score| ≤
      2 * (winCutoff + incidenceCutoff) / meanIncidences := by
  have hincidences_pos : 0 < incidences := by linarith
  have hscore_abs : |score| ≤ 1 := by
    rw [abs_of_nonneg hscore_nonneg]
    exact hscore_le_one
  have hcentered : |wins - score * incidences| ≤ winCutoff + incidenceCutoff := by
    rw [show wins - score * incidences =
      (wins - meanWins) - score * (incidences - meanIncidences) by
        rw [hcalibrated]
        ring]
    calc
      |(wins - meanWins) - score * (incidences - meanIncidences)| ≤
          |wins - meanWins| + |score * (incidences - meanIncidences)| := by
            simpa [sub_eq_add_neg, abs_neg] using
              abs_add_le (wins - meanWins) (-score * (incidences - meanIncidences))
      _ = |wins - meanWins| + |score| * |incidences - meanIncidences| := by
        rw [abs_mul]
      _ ≤ winCutoff + 1 * incidenceCutoff := by gcongr
      _ = winCutoff + incidenceCutoff := by ring
  rw [show wins / incidences - score = (wins - score * incidences) / incidences by
    field_simp]
  rw [abs_div, abs_of_pos hincidences_pos]
  apply (div_le_iff₀ hincidences_pos).2
  have hfactor_nonneg : 0 ≤ 2 * (winCutoff + incidenceCutoff) / meanIncidences := by
    positivity
  calc
    |wins - score * incidences| ≤ winCutoff + incidenceCutoff := hcentered
    _ = (2 * (winCutoff + incidenceCutoff) / meanIncidences) *
        (meanIncidences / 2) := by
          field_simp [ne_of_gt hmeanIncidences_pos]
    _ ≤ (2 * (winCutoff + incidenceCutoff) / meanIncidences) * incidences := by
      exact mul_le_mul_of_nonneg_left hincidences_lower hfactor_nonneg

/--
Literal-source specialization of the asymmetric normalization step.  It joins
the sharp pairwise-centered raw numerator to the endpoint-label denominator
without replacing either by a user-level range bound.
-/
theorem theorem11_iidUserLatentBordaScore_error_le_of_sharp_centered
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative)
    (users comparisonsPerUser : ℕ) (husers : 0 < users) (hcomparisons : 0 < comparisonsPerUser)
    (alternative : Alternative) (hsampling_pos : 0 < (sampling alternative).toReal)
    (rawWinCutoff incidenceCutoff : ℝ)
    (hrawWinCutoff_nonneg : 0 ≤ rawWinCutoff)
    (hincidenceCutoff_nonneg : 0 ≤ incidenceCutoff)
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative)))
    (hincidences_lower :
      (Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
        (sampling alternative).toReal / 2 ≤
        theorem11IidUserLatentBordaIncidences alternative sample)
    (hrawWins_centered :
      |theorem11IidUserBordaPairwiseCentered sampling preference alternative sample| ≤ rawWinCutoff)
    (hincidences_centered :
      |theorem11IidUserLatentBordaIncidences alternative sample -
        (Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
          (sampling alternative).toReal| ≤ incidenceCutoff) :
    |theorem11IidUserLatentBordaScore alternative sample -
      pairwiseBordaScore sampling preference alternative| ≤
      2 * (rawWinCutoff + incidenceCutoff) /
        ((Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
          (sampling alternative).toReal) := by
  let score := pairwiseBordaScore sampling preference alternative
  let meanIncidences : ℝ :=
    (Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
      (sampling alternative).toReal
  let meanWins : ℝ :=
    (users : ℝ) * (comparisonsPerUser : ℝ) * 2 * (sampling alternative).toReal * score
  let wins := theorem11IidUserLatentBordaWins alternative sample
  let incidences := theorem11IidUserLatentBordaIncidences alternative sample
  have hcard :
      (Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) =
        (users : ℝ) * (comparisonsPerUser : ℝ) * 2 := by
          simp [Fintype.card_prod, Fintype.card_fin]
  have hscore_nonneg : 0 ≤ score := by
    dsimp [score, pairwiseBordaScore]
    exact pmfExp_nonneg_of_forall_nonneg sampling _
      (fun opponent => preference.nonneg PUnit.unit alternative opponent)
  have hscore_le_one : score ≤ 1 := by
    dsimp [score, pairwiseBordaScore]
    exact pmfExp_le_of_forall_le sampling _ 1
      (fun opponent => preference.le_one PUnit.unit alternative opponent)
  have hmeanIncidences_pos : 0 < meanIncidences := by
    dsimp [meanIncidences]
    rw [hcard]
    positivity
  have hmean_calibrated : meanWins = score * meanIncidences := by
    dsimp [meanWins, meanIncidences]
    rw [hcard]
    ring
  have hwins_centered : |wins - meanWins| ≤ rawWinCutoff := by
    calc
      |wins - meanWins| =
          |theorem11IidUserBordaPairwiseCentered sampling preference alternative sample| := by
            dsimp [wins, meanWins, score]
            rw [theorem11_iidUserLatentBordaWins_eq_pairwiseCentered_add_mean,
              theorem11_iidUserBordaPairwiseMean_eq_populationBordaMean]
            ring
      _ ≤ rawWinCutoff := hrawWins_centered
  have hmain := theorem11_normalizedBorda_error_le_of_asymmetric_errors_and_count_lower
    (wins := wins) (incidences := incidences) (score := score) (meanWins := meanWins)
    (meanIncidences := meanIncidences) (winCutoff := rawWinCutoff)
    (incidenceCutoff := incidenceCutoff) hscore_nonneg hscore_le_one hmean_calibrated
    hmeanIncidences_pos (by simpa [meanIncidences, incidences] using hincidences_lower)
    hwins_centered (by simpa [meanIncidences, incidences] using hincidences_centered)
    hrawWinCutoff_nonneg hincidenceCutoff_nonneg
  have hincidences_pos : 0 < incidences := by
    have : 0 < meanIncidences / 2 := by positivity
    have hlower : meanIncidences / 2 ≤ incidences := by
      simpa [meanIncidences, incidences] using hincidences_lower
    linarith
  unfold theorem11IidUserLatentBordaScore
  rw [if_neg (ne_of_gt hincidences_pos)]
  simpa [wins, incidences, score, meanIncidences] using hmain

/--
Finite source-sharp Lemma 11 tail for one alternative.  The first failure term
is the diagonal-plus-pairwise Bernstein union, the second is the exact
endpoint-label denominator tail, and the third enforces the denominator's
half-mean lower bound.
-/
theorem theorem11_iidUserLatentBordaScore_minMass_tail
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative)
    (users comparisonsPerUser : ℕ) (husers : 0 < users) (hcomparisons : 0 < comparisonsPerUser)
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (alternative : Alternative) (minimumMass logLevel incidenceCutoff : ℝ)
    (hminimumMass_pos : 0 < minimumMass)
    (hminimumMass : ∀ opponent, minimumMass ≤ (sampling opponent).toReal)
    (hlogLevel_nonneg : 0 ≤ logLevel) (hincidenceCutoff_nonneg : 0 ≤ incidenceCutoff)
    (hincidenceDen_pos : 0 <
      (Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
        (sampling alternative).toReal + incidenceCutoff) :
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample =>
        2 *
            (12 * (comparisonsPerUser : ℝ) * (sampling alternative).toReal *
                Real.sqrt ((users : ℝ) * logLevel /
                  min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) +
              8 * (Fintype.card Alternative : ℝ) * (comparisonsPerUser : ℝ) * logLevel +
              incidenceCutoff) /
            ((Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
              (sampling alternative).toReal) <
          |theorem11IidUserLatentBordaScore alternative sample -
            pairwiseBordaScore sampling preference alternative|) ≤
      2 * (Fintype.card Alternative : ℝ) * Real.exp (-logLevel) +
        2 * Real.exp (-incidenceCutoff ^ 2 /
          (4 * ((Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
            (sampling alternative).toReal + incidenceCutoff))) +
        Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) *
          (sampling alternative).toReal / 4) := by
  classical
  let law := pmfProduct (Fin users)
    (theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative))
    (pmfProd responseLaw
      (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
        (theorem2UserPairLabelLaw sampling)))
  let envelope : ℝ :=
    12 * (comparisonsPerUser : ℝ) * (sampling alternative).toReal *
        Real.sqrt ((users : ℝ) * logLevel /
          min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) +
      8 * (Fintype.card Alternative : ℝ) * (comparisonsPerUser : ℝ) * logLevel
  let meanIncidences : ℝ :=
    (Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
      (sampling alternative).toReal
  let rawEvent :
      (Fin users → (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) → Prop := fun sample =>
      envelope ≤ |theorem11IidUserBordaPairwiseCentered sampling preference alternative sample|
  let incidenceEvent :
      (Fin users → (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) → Prop := fun sample =>
      incidenceCutoff ≤ |theorem11IidUserLatentBordaIncidences alternative sample - meanIncidences|
  let lowerEvent :
      (Fin users → (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) → Prop := fun sample =>
      theorem11IidUserLatentBordaIncidences alternative sample ≤ meanIncidences / 2
  let rawTail : ℝ := 2 * (Fintype.card Alternative : ℝ) * Real.exp (-logLevel)
  let incidenceTail : ℝ := 2 * Real.exp (-incidenceCutoff ^ 2 /
    (4 * (meanIncidences + incidenceCutoff)))
  let lowerTail : ℝ := Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) *
    (sampling alternative).toReal / 4)
  have hsampling_pos : 0 < (sampling alternative).toReal :=
    lt_of_lt_of_le hminimumMass_pos (hminimumMass alternative)
  have henvelope_nonneg : 0 ≤ envelope := by
    dsimp [envelope]
    positivity
  have hraw_tail : pmfProb law rawEvent ≤ rawTail := by
    dsimp [law, rawEvent, envelope, rawTail]
    exact theorem11_iidUserBordaPairwiseCentered_minMass_tail hcalibrated sampling users
      comparisonsPerUser alternative minimumMass logLevel husers hcomparisons hminimumMass_pos
      hminimumMass hlogLevel_nonneg
  have hincidence_tail : pmfProb law incidenceEvent ≤ incidenceTail := by
    dsimp [law, incidenceEvent, incidenceTail, meanIncidences]
    exact theorem11_iidUserLatentBordaIncidences_abs_centered_tail responseLaw sampling users
      comparisonsPerUser alternative incidenceCutoff hincidenceCutoff_nonneg hincidenceDen_pos
  have hcard_half : meanIncidences / 2 =
      ((users * comparisonsPerUser : ℕ) : ℝ) * (sampling alternative).toReal := by
    dsimp [meanIncidences]
    simp [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    ring
  have hlower_tail : pmfProb law lowerEvent ≤ lowerTail := by
    dsimp [law, lowerEvent, lowerTail]
    rw [hcard_half]
    exact theorem11_iidUserLatentBordaIncidences_halfMean_lowerTail responseLaw sampling users
      comparisonsPerUser alternative
  have himp : ∀ sample,
      2 * (envelope + incidenceCutoff) / meanIncidences <
          |theorem11IidUserLatentBordaScore alternative sample -
            pairwiseBordaScore sampling preference alternative| →
        rawEvent sample ∨ incidenceEvent sample ∨ lowerEvent sample := by
    intro sample hbad
    by_cases hraw : rawEvent sample
    · exact Or.inl hraw
    by_cases hincidence : incidenceEvent sample
    · exact Or.inr (Or.inl hincidence)
    by_cases hlower : lowerEvent sample
    · exact Or.inr (Or.inr hlower)
    exfalso
    have hraw_good :
        |theorem11IidUserBordaPairwiseCentered sampling preference alternative sample| ≤ envelope := by
      dsimp [rawEvent] at hraw
      exact le_of_lt (lt_of_not_ge hraw)
    have hincidence_good :
        |theorem11IidUserLatentBordaIncidences alternative sample - meanIncidences| ≤
          incidenceCutoff := by
      dsimp [incidenceEvent] at hincidence
      exact le_of_lt (lt_of_not_ge hincidence)
    have hlower_good : meanIncidences / 2 ≤
        theorem11IidUserLatentBordaIncidences alternative sample := by
      dsimp [lowerEvent] at hlower
      exact le_of_lt (lt_of_not_ge hlower)
    have hgood := theorem11_iidUserLatentBordaScore_error_le_of_sharp_centered
      sampling preference users comparisonsPerUser husers hcomparisons alternative hsampling_pos
      envelope incidenceCutoff henvelope_nonneg hincidenceCutoff_nonneg sample hlower_good
      hraw_good hincidence_good
    exact (not_lt_of_ge hgood) hbad
  calc
    pmfProb law (fun sample =>
        2 * (envelope + incidenceCutoff) / meanIncidences <
          |theorem11IidUserLatentBordaScore alternative sample -
            pairwiseBordaScore sampling preference alternative|) ≤
      pmfProb law (fun sample => rawEvent sample ∨ incidenceEvent sample ∨ lowerEvent sample) :=
        pmfProb_le_of_imp law _ _ himp
    _ ≤ pmfProb law rawEvent + pmfProb law (fun sample => incidenceEvent sample ∨ lowerEvent sample) :=
      pmfProb_or_le law rawEvent (fun sample => incidenceEvent sample ∨ lowerEvent sample)
    _ ≤ rawTail + (incidenceTail + lowerTail) := by
      apply add_le_add hraw_tail
      calc
        pmfProb law (fun sample => incidenceEvent sample ∨ lowerEvent sample) ≤
            pmfProb law incidenceEvent + pmfProb law lowerEvent :=
              pmfProb_or_le law incidenceEvent lowerEvent
        _ ≤ incidenceTail + lowerTail := add_le_add hincidence_tail hlower_tail
    _ = rawTail + incidenceTail + lowerTail := by ring
    _ = 2 * (Fintype.card Alternative : ℝ) * Real.exp (-logLevel) +
        2 * Real.exp (-incidenceCutoff ^ 2 /
          (4 * ((Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
            (sampling alternative).toReal + incidenceCutoff))) +
        Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) *
          (sampling alternative).toReal / 4) := by
            rfl

/--
The source-sharp normalized tail with the denominator set to its explicit
Bernstein quantile.  This leaves only the paper's final `δ` substitution and
rate algebra beyond the literal finite concentration argument.
-/
theorem theorem11_iidUserLatentBordaScore_minMass_quantile_tail
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative)
    (users comparisonsPerUser : ℕ) (husers : 0 < users) (hcomparisons : 0 < comparisonsPerUser)
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (alternative : Alternative) (minimumMass logLevel : ℝ)
    (hminimumMass_pos : 0 < minimumMass)
    (hminimumMass : ∀ opponent, minimumMass ≤ (sampling opponent).toReal)
    (hlogLevel_nonneg : 0 ≤ logLevel) :
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample =>
        2 *
            (12 * (comparisonsPerUser : ℝ) * (sampling alternative).toReal *
                Real.sqrt ((users : ℝ) * logLevel /
                  min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) +
              8 * (Fintype.card Alternative : ℝ) * (comparisonsPerUser : ℝ) * logLevel +
              theorem11IncidenceBernsteinQuantile sampling users comparisonsPerUser
                alternative logLevel) /
            ((Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
              (sampling alternative).toReal) <
          |theorem11IidUserLatentBordaScore alternative sample -
            pairwiseBordaScore sampling preference alternative|) ≤
      2 * (Fintype.card Alternative : ℝ) * Real.exp (-logLevel) +
        2 * Real.exp (-logLevel) +
        Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) *
          (sampling alternative).toReal / 4) := by
  let meanIncidences : ℝ :=
    (Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
      (sampling alternative).toReal
  have hsampling_pos : 0 < (sampling alternative).toReal :=
    lt_of_lt_of_le hminimumMass_pos (hminimumMass alternative)
  have hmean_pos : 0 < meanIncidences := by
    dsimp [meanIncidences]
    simp [Fintype.card_prod, Fintype.card_fin]
    positivity
  have hquantile_nonneg : 0 ≤ theorem11IncidenceBernsteinQuantile sampling users
      comparisonsPerUser alternative logLevel := by
    unfold theorem11IncidenceBernsteinQuantile
    positivity
  have hden_pos : 0 < meanIncidences +
      theorem11IncidenceBernsteinQuantile sampling users comparisonsPerUser
        alternative logLevel := by positivity
  have htail := theorem11_iidUserLatentBordaScore_minMass_tail responseLaw sampling preference
    users comparisonsPerUser husers hcomparisons hcalibrated alternative minimumMass logLevel
    (theorem11IncidenceBernsteinQuantile sampling users comparisonsPerUser alternative logLevel)
    hminimumMass_pos hminimumMass hlogLevel_nonneg hquantile_nonneg
    (by simpa [meanIncidences] using hden_pos)
  have hden_quantile : 0 < meanIncidences + (1 : ℝ) *
      (Real.sqrt (8 * meanIncidences * logLevel) + 8 * (1 : ℝ) * logLevel) := by
    positivity
  have hquantile_exp :
      2 * Real.exp
          (-(theorem11IncidenceBernsteinQuantile sampling users comparisonsPerUser
              alternative logLevel) ^ 2 /
            (4 * (meanIncidences + theorem11IncidenceBernsteinQuantile sampling users
              comparisonsPerUser alternative logLevel))) ≤
        2 * Real.exp (-logLevel) := by
      simpa [meanIncidences, theorem11IncidenceBernsteinQuantile] using
        (bernstein_two_sided_exponential_at_quantile_le
          (totalVariance := meanIncidences) (bound := (1 : ℝ)) (logLevel := logLevel)
          hmean_pos.le (by norm_num) hlogLevel_nonneg hden_quantile)
  calc
    pmfProb
        (pmfProduct (Fin users)
          (theorem2UserResponseTable Alternative ×
            (Fin comparisonsPerUser → Alternative × Alternative))
          (pmfProd responseLaw
            (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
              (theorem2UserPairLabelLaw sampling))))
        (fun sample =>
          2 *
              (12 * (comparisonsPerUser : ℝ) * (sampling alternative).toReal *
                  Real.sqrt ((users : ℝ) * logLevel /
                    min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) +
                8 * (Fintype.card Alternative : ℝ) * (comparisonsPerUser : ℝ) * logLevel +
                theorem11IncidenceBernsteinQuantile sampling users comparisonsPerUser
                  alternative logLevel) /
              ((Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
                (sampling alternative).toReal) <
            |theorem11IidUserLatentBordaScore alternative sample -
              pairwiseBordaScore sampling preference alternative|) ≤
        2 * (Fintype.card Alternative : ℝ) * Real.exp (-logLevel) +
          2 * Real.exp
            (-(theorem11IncidenceBernsteinQuantile sampling users comparisonsPerUser
                alternative logLevel) ^ 2 /
              (4 * ((Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
                (sampling alternative).toReal +
                theorem11IncidenceBernsteinQuantile sampling users comparisonsPerUser
                  alternative logLevel))) +
          Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) *
            (sampling alternative).toReal / 4) := htail
    _ ≤ 2 * (Fintype.card Alternative : ℝ) * Real.exp (-logLevel) +
          2 * Real.exp (-logLevel) +
          Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) *
            (sampling alternative).toReal / 4) := by
            gcongr

/--
Confidence-level form of the source-sharp finite Lemma 11 tail.  The remaining
assumption is exactly the source denominator lower-tail budget; choosing a
sample size that implies it is separate elementary exponential algebra.
-/
theorem theorem11_iidUserLatentBordaScore_minMass_confidence
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative] [Nonempty Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative)
    (users comparisonsPerUser : ℕ) (husers : 0 < users) (hcomparisons : 0 < comparisonsPerUser)
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (alternative : Alternative) (minimumMass delta : ℝ)
    (hminimumMass_pos : 0 < minimumMass)
    (hminimumMass : ∀ opponent, minimumMass ≤ (sampling opponent).toReal)
    (hdelta_pos : 0 < delta) (hdelta_le_one : delta ≤ 1)
    (hlower_failure : Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) *
      (sampling alternative).toReal / 4) ≤ delta / 2) :
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample =>
        let logLevel := Real.log (8 * (Fintype.card Alternative : ℝ) / delta)
        2 *
            (12 * (comparisonsPerUser : ℝ) * (sampling alternative).toReal *
                Real.sqrt ((users : ℝ) * logLevel /
                  min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) +
              8 * (Fintype.card Alternative : ℝ) * (comparisonsPerUser : ℝ) * logLevel +
              theorem11IncidenceBernsteinQuantile sampling users comparisonsPerUser
                alternative logLevel) /
            ((Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
              (sampling alternative).toReal) <
          |theorem11IidUserLatentBordaScore alternative sample -
            pairwiseBordaScore sampling preference alternative|) ≤ delta := by
  let logLevel : ℝ := Real.log (8 * (Fintype.card Alternative : ℝ) / delta)
  have hcard_nat : 0 < Fintype.card Alternative := Fintype.card_pos
  have hcard_pos : 0 < (Fintype.card Alternative : ℝ) := by exact_mod_cast hcard_nat
  have hcard_one : (1 : ℝ) ≤ (Fintype.card Alternative : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hcard_nat)
  have hratio_ge_one : 1 ≤ 8 * (Fintype.card Alternative : ℝ) / delta := by
    apply (le_div_iff₀ hdelta_pos).2
    nlinarith
  have hlogLevel_nonneg : 0 ≤ logLevel := by
    dsimp [logLevel]
    exact Real.log_nonneg hratio_ge_one
  have htail := theorem11_iidUserLatentBordaScore_minMass_quantile_tail
    responseLaw sampling preference users comparisonsPerUser husers hcomparisons hcalibrated
    alternative minimumMass logLevel hminimumMass_pos hminimumMass hlogLevel_nonneg
  have hratio_pos : 0 < 8 * (Fintype.card Alternative : ℝ) / delta := by positivity
  have hexp : Real.exp (-logLevel) = delta / (8 * (Fintype.card Alternative : ℝ)) := by
    dsimp [logLevel]
    rw [Real.exp_neg, Real.exp_log hratio_pos]
    field_simp [ne_of_gt hdelta_pos]
  have hraw_failure :
      2 * (Fintype.card Alternative : ℝ) * Real.exp (-logLevel) = delta / 4 := by
    rw [hexp]
    field_simp [ne_of_gt hcard_pos]
    ring
  have hincidence_failure : 2 * Real.exp (-logLevel) ≤ delta / 4 := by
    rw [hexp]
    calc
      2 * (delta / (8 * (Fintype.card Alternative : ℝ))) =
          (delta / 4) / (Fintype.card Alternative : ℝ) := by
            field_simp [ne_of_gt hcard_pos]
            ring
      _ ≤ delta / 4 := by
        apply (div_le_iff₀ hcard_pos).2
        calc
          delta / 4 = (delta / 4) * 1 := by ring
          _ ≤ (delta / 4) * (Fintype.card Alternative : ℝ) :=
            mul_le_mul_of_nonneg_left hcard_one (by linarith)
  change pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample =>
        2 *
            (12 * (comparisonsPerUser : ℝ) * (sampling alternative).toReal *
                Real.sqrt ((users : ℝ) * logLevel /
                  min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) +
              8 * (Fintype.card Alternative : ℝ) * (comparisonsPerUser : ℝ) * logLevel +
              theorem11IncidenceBernsteinQuantile sampling users comparisonsPerUser
                alternative logLevel) /
            ((Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
              (sampling alternative).toReal) <
          |theorem11IidUserLatentBordaScore alternative sample -
            pairwiseBordaScore sampling preference alternative|) ≤ delta
  calc
    pmfProb
        (pmfProduct (Fin users)
          (theorem2UserResponseTable Alternative ×
            (Fin comparisonsPerUser → Alternative × Alternative))
          (pmfProd responseLaw
            (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
              (theorem2UserPairLabelLaw sampling))))
        (fun sample =>
          2 *
              (12 * (comparisonsPerUser : ℝ) * (sampling alternative).toReal *
                  Real.sqrt ((users : ℝ) * logLevel /
                    min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) +
                8 * (Fintype.card Alternative : ℝ) * (comparisonsPerUser : ℝ) * logLevel +
                theorem11IncidenceBernsteinQuantile sampling users comparisonsPerUser
                  alternative logLevel) /
              ((Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) *
                (sampling alternative).toReal) <
            |theorem11IidUserLatentBordaScore alternative sample -
              pairwiseBordaScore sampling preference alternative|) ≤
        2 * (Fintype.card Alternative : ℝ) * Real.exp (-logLevel) +
          2 * Real.exp (-logLevel) +
          Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) *
            (sampling alternative).toReal / 4) := htail
    _ = delta / 4 + 2 * Real.exp (-logLevel) +
          Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) *
            (sampling alternative).toReal / 4) := by rw [hraw_failure]
    _ ≤ delta / 4 + delta / 4 + delta / 2 := by gcongr
    _ = delta := by ring

/--
The source's minimum-mass sample-size condition implies the lower-tail budget
used by the confidence theorem.  The source condition is deliberately kept at
its printed weaker exponent `nd μ_min / 8`; the literal Borda denominator has
the stronger exponent `nd μ(x) / 4`.
-/
theorem theorem11_bordaLowerTail_failure_le_of_sourceMinimumMassCondition
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative] [Nonempty Alternative]
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (alternative : Alternative) (minimumMass delta : ℝ)
    (husers : 0 < users) (hcomparisons : 0 < comparisonsPerUser)
    (hminimumMass_pos : 0 < minimumMass)
    (hminimumMass : ∀ opponent, minimumMass ≤ (sampling opponent).toReal)
    (hdelta_pos : 0 < delta)
    (hsource_condition :
      2 * (Fintype.card Alternative : ℝ) *
        Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * minimumMass / 8) ≤ delta) :
    Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) *
      (sampling alternative).toReal / 4) ≤ delta / 2 := by
  have hnd_pos : 0 < ((users * comparisonsPerUser : ℕ) : ℝ) := by
    positivity
  have hmass : minimumMass ≤ (sampling alternative).toReal := hminimumMass alternative
  have hcard_nat : 0 < Fintype.card Alternative := Fintype.card_pos
  have hcard_pos : 0 < (Fintype.card Alternative : ℝ) := by exact_mod_cast hcard_nat
  have hcard_one : (1 : ℝ) ≤ (Fintype.card Alternative : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hcard_nat)
  have hexp_le_minimum :
      Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) *
        (sampling alternative).toReal / 4) ≤
      Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * minimumMass / 8) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hminimum_budget :
      Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * minimumMass / 8) ≤
        delta / (2 * (Fintype.card Alternative : ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * (Fintype.card Alternative : ℝ))).2
    nlinarith
  have hbudget_le_half : delta / (2 * (Fintype.card Alternative : ℝ)) ≤ delta / 2 := by
    calc
      delta / (2 * (Fintype.card Alternative : ℝ)) ≤ delta / (2 * 1) := by
        gcongr
      _ = delta / 2 := by ring
  exact hexp_le_minimum.trans (hminimum_budget.trans hbudget_le_half)

/--
Closed-form finite confidence consequence of Lemma 11.  This is the source's
`O(sqrt(log(m/δ)/(n min{1,d μ_min²})) + m log(m/δ)/(n μ_min))` rate with
explicit universal constants.  The source's printed minimum-mass sample-size
condition is retained as the hypothesis that controls the denominator event.
-/
theorem theorem11_iidUserLatentBordaScore_minMass_sourceRate_confidence
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative] [Nonempty Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative)
    (users comparisonsPerUser : ℕ) (husers : 0 < users) (hcomparisons : 0 < comparisonsPerUser)
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (alternative : Alternative) (minimumMass delta : ℝ)
    (hminimumMass_pos : 0 < minimumMass)
    (hminimumMass : ∀ opponent, minimumMass ≤ (sampling opponent).toReal)
    (hdelta_pos : 0 < delta) (hdelta_le_one : delta ≤ 1)
    (hsource_condition :
      2 * (Fintype.card Alternative : ℝ) *
        Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * minimumMass / 8) ≤ delta) :
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample =>
        let logLevel := Real.log (8 * (Fintype.card Alternative : ℝ) / delta)
        20 * Real.sqrt ((users : ℝ) * logLevel /
          min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) / (users : ℝ) +
          8 * ((Fintype.card Alternative : ℝ) + 1) * logLevel /
            ((users : ℝ) * minimumMass) <
          |theorem11IidUserLatentBordaScore alternative sample -
            pairwiseBordaScore sampling preference alternative|) ≤ delta := by
  classical
  let logLevel : ℝ := Real.log (8 * (Fintype.card Alternative : ℝ) / delta)
  let mass : ℝ := (sampling alternative).toReal
  let law := pmfProduct (Fin users)
    (theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative))
    (pmfProd responseLaw
      (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
        (theorem2UserPairLabelLaw sampling)))
  let oldThreshold : ℝ :=
    2 *
        (12 * (comparisonsPerUser : ℝ) * mass *
            Real.sqrt ((users : ℝ) * logLevel /
              min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) +
          8 * (Fintype.card Alternative : ℝ) * (comparisonsPerUser : ℝ) * logLevel +
          theorem11IncidenceBernsteinQuantile sampling users comparisonsPerUser alternative logLevel) /
      ((Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) * mass)
  let newThreshold : ℝ :=
    20 * Real.sqrt ((users : ℝ) * logLevel /
      min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) / (users : ℝ) +
      8 * ((Fintype.card Alternative : ℝ) + 1) * logLevel /
        ((users : ℝ) * minimumMass)
  have husers_real_pos : 0 < (users : ℝ) := by exact_mod_cast husers
  have hcomparisons_real_pos : 0 < (comparisonsPerUser : ℝ) := by exact_mod_cast hcomparisons
  have hcomparisons_real_one : (1 : ℝ) ≤ (comparisonsPerUser : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hcomparisons)
  have hmass_pos : 0 < mass :=
    lt_of_lt_of_le hminimumMass_pos (hminimumMass alternative)
  have hmass_le_one : mass ≤ 1 := by
    dsimp [mass]
    exact pmf_apply_toReal_le_one sampling alternative
  have hlogLevel_nonneg : 0 ≤ logLevel := by
    have hcard_nat : 0 < Fintype.card Alternative := Fintype.card_pos
    have hcard_one : (1 : ℝ) ≤ (Fintype.card Alternative : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hcard_nat)
    apply Real.log_nonneg
    apply (le_div_iff₀ hdelta_pos).2
    nlinarith
  have hlower := theorem11_bordaLowerTail_failure_le_of_sourceMinimumMassCondition
    sampling users comparisonsPerUser alternative minimumMass delta husers hcomparisons
    hminimumMass_pos hminimumMass hdelta_pos hsource_condition
  have htail := theorem11_iidUserLatentBordaScore_minMass_confidence
    responseLaw sampling preference users comparisonsPerUser husers hcomparisons hcalibrated
    alternative minimumMass delta hminimumMass_pos hminimumMass hdelta_pos hdelta_le_one hlower
  have hincidence_rate := theorem11_incidenceQuantile_normalized_le_rateEnvelope
    (users := (users : ℝ)) (comparisons := (comparisonsPerUser : ℝ)) (mass := mass)
    (minimumMass := minimumMass) (logLevel := logLevel) husers_real_pos hcomparisons_real_pos
    hcomparisons_real_one hmass_pos hmass_le_one hminimumMass_pos
    (hminimumMass alternative) hlogLevel_nonneg
  have hincidence_rate' :
      2 * theorem11IncidenceBernsteinQuantile sampling users comparisonsPerUser alternative logLevel /
          ((Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) * mass) ≤
        8 * Real.sqrt ((users : ℝ) * logLevel /
          min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) / (users : ℝ) +
          8 * logLevel / ((users : ℝ) * minimumMass) := by
    calc
      2 * theorem11IncidenceBernsteinQuantile sampling users comparisonsPerUser alternative logLevel /
          ((Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) * mass) =
          2 * (Real.sqrt (8 * (2 * (users : ℝ) * (comparisonsPerUser : ℝ) * mass) * logLevel) +
            8 * logLevel) / (2 * (users : ℝ) * (comparisonsPerUser : ℝ) * mass) := by
              simp [theorem11IncidenceBernsteinQuantile, Fintype.card_prod, Fintype.card_fin]
              dsimp [mass]
              ring
      _ ≤ 8 * Real.sqrt ((users : ℝ) * logLevel /
          min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) / (users : ℝ) +
          8 * logLevel / ((users : ℝ) * minimumMass) := hincidence_rate
  have husers_minimumMass_le : (users : ℝ) * minimumMass ≤ (users : ℝ) * mass :=
    mul_le_mul_of_nonneg_left (hminimumMass alternative) husers_real_pos.le
  have hraw_linear_rate :
      8 * (Fintype.card Alternative : ℝ) * logLevel / ((users : ℝ) * mass) ≤
        8 * (Fintype.card Alternative : ℝ) * logLevel / ((users : ℝ) * minimumMass) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hscaled := mul_le_mul_of_nonneg_left husers_minimumMass_le
      (show 0 ≤ 8 * (Fintype.card Alternative : ℝ) * logLevel by positivity)
    nlinarith
  have hraw_rate :
      2 *
          (12 * (comparisonsPerUser : ℝ) * mass *
              Real.sqrt ((users : ℝ) * logLevel /
                min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) +
            8 * (Fintype.card Alternative : ℝ) * (comparisonsPerUser : ℝ) * logLevel) /
          ((Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) * mass) ≤
        12 * Real.sqrt ((users : ℝ) * logLevel /
          min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) / (users : ℝ) +
          8 * (Fintype.card Alternative : ℝ) * logLevel / ((users : ℝ) * minimumMass) := by
    calc
      2 *
          (12 * (comparisonsPerUser : ℝ) * mass *
              Real.sqrt ((users : ℝ) * logLevel /
                min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) +
            8 * (Fintype.card Alternative : ℝ) * (comparisonsPerUser : ℝ) * logLevel) /
          ((Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) * mass) =
          12 * Real.sqrt ((users : ℝ) * logLevel /
            min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) / (users : ℝ) +
            8 * (Fintype.card Alternative : ℝ) * logLevel / ((users : ℝ) * mass) := by
              field_simp [ne_of_gt husers_real_pos, ne_of_gt hcomparisons_real_pos,
                ne_of_gt hmass_pos]
              simp [Fintype.card_prod, Fintype.card_fin]
              ring
      _ ≤ 12 * Real.sqrt ((users : ℝ) * logLevel /
          min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) / (users : ℝ) +
          8 * (Fintype.card Alternative : ℝ) * logLevel / ((users : ℝ) * minimumMass) :=
            by simpa [add_comm] using
              add_le_add_left hraw_linear_rate
                (12 * Real.sqrt ((users : ℝ) * logLevel /
                  min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) / (users : ℝ))
  have hthreshold : oldThreshold ≤ newThreshold := by
    calc
      oldThreshold =
          2 *
              (12 * (comparisonsPerUser : ℝ) * mass *
                  Real.sqrt ((users : ℝ) * logLevel /
                    min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) +
                8 * (Fintype.card Alternative : ℝ) * (comparisonsPerUser : ℝ) * logLevel) /
              ((Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) * mass) +
            2 * theorem11IncidenceBernsteinQuantile sampling users comparisonsPerUser alternative logLevel /
              ((Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) * mass) := by
                dsimp [oldThreshold]
                ring
      _ ≤ (12 * Real.sqrt ((users : ℝ) * logLevel /
            min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) / (users : ℝ) +
            8 * (Fintype.card Alternative : ℝ) * logLevel / ((users : ℝ) * minimumMass)) +
          (8 * Real.sqrt ((users : ℝ) * logLevel /
            min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) / (users : ℝ) +
            8 * logLevel / ((users : ℝ) * minimumMass)) :=
              add_le_add hraw_rate hincidence_rate'
      _ = newThreshold := by
        dsimp [newThreshold]
        ring
  change pmfProb law (fun sample => newThreshold <
    |theorem11IidUserLatentBordaScore alternative sample -
      pairwiseBordaScore sampling preference alternative|) ≤ delta
  have htail' : pmfProb law (fun sample => oldThreshold <
      |theorem11IidUserLatentBordaScore alternative sample -
        pairwiseBordaScore sampling preference alternative|) ≤ delta := by
    simpa [law, oldThreshold, logLevel, mass] using htail
  exact (pmfProb_le_of_imp law _ _ (fun sample hbad => lt_of_le_of_lt hthreshold hbad)).trans htail'

/--
Closed-form source-rate tail before choosing a failure allocation.  This keeps
the raw, incidence, and denominator lower-tail budgets separate so that the
source's later simultaneous union can use its actual `δ/(4m²)` allocation.
-/
theorem theorem11_iidUserLatentBordaScore_minMass_sourceRate_tail
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative)
    (users comparisonsPerUser : ℕ) (husers : 0 < users) (hcomparisons : 0 < comparisonsPerUser)
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (alternative : Alternative) (minimumMass logLevel lowerTailBudget : ℝ)
    (hminimumMass_pos : 0 < minimumMass)
    (hminimumMass : ∀ opponent, minimumMass ≤ (sampling opponent).toReal)
    (hlogLevel_nonneg : 0 ≤ logLevel)
    (hlowerTail : Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) *
      (sampling alternative).toReal / 4) ≤ lowerTailBudget) :
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample =>
        20 * Real.sqrt ((users : ℝ) * logLevel /
          min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) / (users : ℝ) +
          8 * ((Fintype.card Alternative : ℝ) + 1) * logLevel /
            ((users : ℝ) * minimumMass) <
          |theorem11IidUserLatentBordaScore alternative sample -
            pairwiseBordaScore sampling preference alternative|) ≤
      2 * (Fintype.card Alternative : ℝ) * Real.exp (-logLevel) +
        2 * Real.exp (-logLevel) + lowerTailBudget := by
  classical
  let mass : ℝ := (sampling alternative).toReal
  let law := pmfProduct (Fin users)
    (theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative))
    (pmfProd responseLaw
      (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
        (theorem2UserPairLabelLaw sampling)))
  let oldThreshold : ℝ :=
    2 *
        (12 * (comparisonsPerUser : ℝ) * mass *
            Real.sqrt ((users : ℝ) * logLevel /
              min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) +
          8 * (Fintype.card Alternative : ℝ) * (comparisonsPerUser : ℝ) * logLevel +
          theorem11IncidenceBernsteinQuantile sampling users comparisonsPerUser alternative logLevel) /
      ((Fintype.card ((Fin users × Fin comparisonsPerUser) × Bool) : ℝ) * mass)
  let newThreshold : ℝ :=
    20 * Real.sqrt ((users : ℝ) * logLevel /
      min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) / (users : ℝ) +
      8 * ((Fintype.card Alternative : ℝ) + 1) * logLevel /
        ((users : ℝ) * minimumMass)
  have husers_real_pos : 0 < (users : ℝ) := by exact_mod_cast husers
  have hcomparisons_real_pos : 0 < (comparisonsPerUser : ℝ) := by exact_mod_cast hcomparisons
  have hcomparisons_real_one : (1 : ℝ) ≤ (comparisonsPerUser : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hcomparisons)
  have hmass_pos : 0 < mass :=
    lt_of_lt_of_le hminimumMass_pos (hminimumMass alternative)
  have hmass_le_one : mass ≤ 1 := by
    dsimp [mass]
    exact pmf_apply_toReal_le_one sampling alternative
  have hthreshold : oldThreshold ≤ newThreshold := by
    calc
      oldThreshold =
          2 *
              (12 * (comparisonsPerUser : ℝ) * mass *
                  Real.sqrt ((users : ℝ) * logLevel /
                    min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) +
                8 * (Fintype.card Alternative : ℝ) * (comparisonsPerUser : ℝ) * logLevel +
                (Real.sqrt (8 * (2 * (users : ℝ) * (comparisonsPerUser : ℝ) * mass) * logLevel) +
                  8 * logLevel)) /
              (2 * (users : ℝ) * (comparisonsPerUser : ℝ) * mass) := by
                dsimp [oldThreshold]
                simp [theorem11IncidenceBernsteinQuantile, Fintype.card_prod, Fintype.card_fin]
                dsimp [mass]
                ring
      _ ≤ 20 * Real.sqrt ((users : ℝ) * logLevel /
            min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) / (users : ℝ) +
          8 * ((Fintype.card Alternative : ℝ) + 1) * logLevel /
            ((users : ℝ) * minimumMass) :=
              theorem11_sharpNormalizedQuantile_le_sourceRate husers_real_pos hcomparisons_real_pos
                hcomparisons_real_one hmass_pos hmass_le_one hminimumMass_pos
                (hminimumMass alternative) (by positivity) hlogLevel_nonneg
      _ = newThreshold := by rfl
  have htail := theorem11_iidUserLatentBordaScore_minMass_quantile_tail
    responseLaw sampling preference users comparisonsPerUser husers hcomparisons hcalibrated
    alternative minimumMass logLevel hminimumMass_pos hminimumMass hlogLevel_nonneg
  change pmfProb law (fun sample => newThreshold <
    |theorem11IidUserLatentBordaScore alternative sample -
      pairwiseBordaScore sampling preference alternative|) ≤
      2 * (Fintype.card Alternative : ℝ) * Real.exp (-logLevel) +
        2 * Real.exp (-logLevel) + lowerTailBudget
  have htail' : pmfProb law (fun sample => oldThreshold <
      |theorem11IidUserLatentBordaScore alternative sample -
        pairwiseBordaScore sampling preference alternative|) ≤
      2 * (Fintype.card Alternative : ℝ) * Real.exp (-logLevel) +
        2 * Real.exp (-logLevel) + lowerTailBudget := by
    calc
      pmfProb law (fun sample => oldThreshold <
          |theorem11IidUserLatentBordaScore alternative sample -
            pairwiseBordaScore sampling preference alternative|) ≤
          2 * (Fintype.card Alternative : ℝ) * Real.exp (-logLevel) +
            2 * Real.exp (-logLevel) +
              Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) *
                (sampling alternative).toReal / 4) := by
              simpa [law, oldThreshold, mass] using htail
      _ ≤ 2 * (Fintype.card Alternative : ℝ) * Real.exp (-logLevel) +
            2 * Real.exp (-logLevel) + lowerTailBudget := by gcongr
  exact (pmfProb_le_of_imp law _ _ (fun sample hbad => lt_of_le_of_lt hthreshold hbad)).trans htail'

/--
Simultaneous all-alternatives form of the source-sharp Lemma 11 rate.  The
proof uses the source allocation `δ₀ = δ/(4m²)`, so its logarithmic factor is
`log (8m²/δ)` rather than the fixed-alternative `log (8m/δ)` specialization.
-/
theorem theorem11_iidUserLatentBordaScore_minMass_sourceRate_uniform_confidence
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative] [Nonempty Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative)
    (users comparisonsPerUser : ℕ) (husers : 0 < users) (hcomparisons : 0 < comparisonsPerUser)
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (minimumMass delta : ℝ) (hminimumMass_pos : 0 < minimumMass)
    (hminimumMass : ∀ alternative, minimumMass ≤ (sampling alternative).toReal)
    (hdelta_pos : 0 < delta) (hdelta_le_one : delta ≤ 1)
    (hsource_condition :
      2 * (Fintype.card Alternative : ℝ) *
        Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * minimumMass / 8) ≤ delta) :
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample =>
        let logLevel := Real.log (8 * (Fintype.card Alternative : ℝ) ^ 2 / delta)
        ∃ alternative,
          20 * Real.sqrt ((users : ℝ) * logLevel /
            min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) / (users : ℝ) +
            8 * ((Fintype.card Alternative : ℝ) + 1) * logLevel /
              ((users : ℝ) * minimumMass) <
            |theorem11IidUserLatentBordaScore alternative sample -
              pairwiseBordaScore sampling preference alternative|) ≤ delta := by
  classical
  let alternativesCard : ℝ := Fintype.card Alternative
  let logLevel : ℝ := Real.log (8 * alternativesCard ^ 2 / delta)
  let rate : ℝ :=
    20 * Real.sqrt ((users : ℝ) * logLevel /
      min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) / (users : ℝ) +
      8 * (alternativesCard + 1) * logLevel / ((users : ℝ) * minimumMass)
  let law := pmfProduct (Fin users)
    (theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative))
    (pmfProd responseLaw
      (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
        (theorem2UserPairLabelLaw sampling)))
  have hcard_nat : 0 < Fintype.card Alternative := Fintype.card_pos
  have hcard_pos : 0 < alternativesCard := by
    dsimp [alternativesCard]
    exact_mod_cast hcard_nat
  have hcard_one : (1 : ℝ) ≤ alternativesCard := by
    dsimp [alternativesCard]
    exact_mod_cast (Nat.succ_le_iff.mpr hcard_nat)
  have hlogLevel_nonneg : 0 ≤ logLevel := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hdelta_pos).2
    nlinarith [sq_nonneg alternativesCard]
  have hratio_pos : 0 < 8 * alternativesCard ^ 2 / delta := by positivity
  have hexp : Real.exp (-logLevel) = delta / (8 * alternativesCard ^ 2) := by
    dsimp [logLevel]
    rw [Real.exp_neg, Real.exp_log hratio_pos]
    field_simp [ne_of_gt hcard_pos, ne_of_gt hdelta_pos]
  have hnd_pos : 0 < ((users * comparisonsPerUser : ℕ) : ℝ) := by positivity
  have hlower : ∀ alternative : Alternative,
      Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) *
        (sampling alternative).toReal / 4) ≤ delta / (2 * alternativesCard) := by
    intro alternative
    have hmass : minimumMass ≤ (sampling alternative).toReal := hminimumMass alternative
    have hexp_le_minimum :
        Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) *
          (sampling alternative).toReal / 4) ≤
        Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * minimumMass / 8) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hminimum_budget :
        Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * minimumMass / 8) ≤
          delta / (2 * alternativesCard) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * alternativesCard)).2
      nlinarith
    exact hexp_le_minimum.trans hminimum_budget
  have hfixed : ∀ alternative : Alternative,
      pmfProb law (fun sample => rate <
        |theorem11IidUserLatentBordaScore alternative sample -
          pairwiseBordaScore sampling preference alternative|) ≤ delta / alternativesCard := by
    intro alternative
    have htail := theorem11_iidUserLatentBordaScore_minMass_sourceRate_tail
      responseLaw sampling preference users comparisonsPerUser husers hcomparisons hcalibrated
      alternative minimumMass logLevel (delta / (2 * alternativesCard))
      hminimumMass_pos hminimumMass hlogLevel_nonneg (hlower alternative)
    calc
      pmfProb law (fun sample => rate <
          |theorem11IidUserLatentBordaScore alternative sample -
            pairwiseBordaScore sampling preference alternative|) ≤
          2 * alternativesCard * Real.exp (-logLevel) +
            2 * Real.exp (-logLevel) + delta / (2 * alternativesCard) := by
              simpa [law, rate, alternativesCard] using htail
      _ ≤ delta / alternativesCard := by
        rw [hexp]
        field_simp [ne_of_gt hcard_pos] <;> nlinarith [hcard_one]
  change pmfProb law (fun sample => ∃ alternative, rate <
    |theorem11IidUserLatentBordaScore alternative sample -
      pairwiseBordaScore sampling preference alternative|) ≤ delta
  calc
    pmfProb law (fun sample => ∃ alternative, rate <
        |theorem11IidUserLatentBordaScore alternative sample -
          pairwiseBordaScore sampling preference alternative|) ≤
        alternativesCard * (delta / alternativesCard) :=
          pmfProb_exists_le_card_mul law
            (fun alternative sample => rate <
              |theorem11IidUserLatentBordaScore alternative sample -
                pairwiseBordaScore sampling preference alternative|)
            (delta / alternativesCard) hfixed
    _ = delta := by field_simp [ne_of_gt hcard_pos]

/--
Deterministic ratio step behind Lemma 11.  If numerator and denominator are
within the same additive error of their calibrated means, and the denominator
stays above half of its total mean, then the normalized count is close to the
population score.  This makes no independence assumption.
-/
theorem theorem11_normalizedBorda_error_le_of_centered_and_count_lower
    {wins incidences score users meanWins meanIncidences cutoff : ℝ}
    (hscore_nonneg : 0 ≤ score) (hscore_le_one : score ≤ 1)
    (hcalibrated : meanWins = score * meanIncidences)
    (htotal_mean_pos : 0 < users * meanIncidences)
    (hincidences_lower : users * meanIncidences / 2 ≤ incidences)
    (hwins_centered : |wins - users * meanWins| ≤ cutoff)
    (hincidences_centered : |incidences - users * meanIncidences| ≤ cutoff)
    (hcutoff_nonneg : 0 ≤ cutoff) :
    |wins / incidences - score| ≤ 4 * cutoff / (users * meanIncidences) := by
  have hincidences_pos : 0 < incidences := by linarith
  have hscore_abs : |score| ≤ 1 := by
    rw [abs_of_nonneg hscore_nonneg]
    exact hscore_le_one
  have hcentered : |wins - score * incidences| ≤ 2 * cutoff := by
    rw [show wins - score * incidences =
      (wins - users * meanWins) - score * (incidences - users * meanIncidences) by
        rw [hcalibrated]
        ring]
    calc
      |(wins - users * meanWins) - score * (incidences - users * meanIncidences)| ≤
          |wins - users * meanWins| + |score * (incidences - users * meanIncidences)| :=
        by
          simpa [sub_eq_add_neg, abs_neg] using
            abs_add_le (wins - users * meanWins) (-score * (incidences - users * meanIncidences))
      _ = |wins - users * meanWins| + |score| * |incidences - users * meanIncidences| := by
        rw [abs_mul]
      _ ≤ cutoff + 1 * cutoff := by gcongr
      _ = 2 * cutoff := by ring
  rw [show wins / incidences - score = (wins - score * incidences) / incidences by
    field_simp]
  rw [abs_div, abs_of_pos hincidences_pos]
  apply (div_le_iff₀ hincidences_pos).2
  have hratio_identity (totalMean : ℝ) (htotalMean_pos : 0 < totalMean) :
      2 * cutoff = (4 * cutoff / totalMean) * (totalMean / 2) := by
    field_simp [ne_of_gt htotalMean_pos]
    ring
  calc
    |wins - score * incidences| ≤ 2 * cutoff := hcentered
    _ = (4 * cutoff / (users * meanIncidences)) *
        (users * meanIncidences / 2) :=
      hratio_identity (users * meanIncidences) htotal_mean_pos
    _ ≤ (4 * cutoff / (users * meanIncidences)) * incidences := by
      apply mul_le_mul_of_nonneg_left hincidences_lower
      exact div_nonneg (by positivity) htotal_mean_pos.le

/--
The preceding deterministic ratio bound specialized to the literal source
user-batch Borda counts.  Calibration identifies the ratio of the two means
with the source population Borda score.
-/
theorem theorem11_iidBordaScore_error_le_of_centered
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative)
    (users comparisonsPerUser : ℕ) (husers : 0 < users) (hcomparisons : 0 < comparisonsPerUser)
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (alternative : Alternative) (hsampling_pos : 0 < (sampling alternative).toReal)
    (cutoff : ℝ) (hcutoff_nonneg : 0 ≤ cutoff)
    (hcutoff_small : cutoff ≤
      (users : ℝ) *
        pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser)
          (theorem2UserBatchBordaIncidences alternative) / 2)
    (sample : Fin users → theorem2UserBatchReport Alternative comparisonsPerUser)
    (hwins_centered :
      |theorem12EmpiricalBordaWins theorem2UserBatchBordaWins alternative sample -
        (users : ℝ) *
          pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser)
            (theorem2UserBatchBordaWins alternative)| ≤ cutoff)
    (hincidences_centered :
      |theorem12EmpiricalBordaIncidences theorem2UserBatchBordaIncidences alternative sample -
        (users : ℝ) *
          pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser)
            (theorem2UserBatchBordaIncidences alternative)| ≤ cutoff) :
    |theorem12EmpiricalBordaScore theorem2UserBatchBordaWins theorem2UserBatchBordaIncidences
        alternative sample - pairwiseBordaScore sampling preference alternative| ≤
      4 * cutoff /
        ((users : ℝ) *
          pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser)
            (theorem2UserBatchBordaIncidences alternative)) := by
  let reportLaw := theorem2UserBatchLaw responseLaw sampling comparisonsPerUser
  let meanWins := pmfExp reportLaw (theorem2UserBatchBordaWins alternative)
  let meanIncidences := pmfExp reportLaw (theorem2UserBatchBordaIncidences alternative)
  let score := pairwiseBordaScore sampling preference alternative
  let wins := theorem12EmpiricalBordaWins theorem2UserBatchBordaWins alternative sample
  let incidences := theorem12EmpiricalBordaIncidences theorem2UserBatchBordaIncidences alternative sample
  have hscore_nonneg : 0 ≤ score := by
    dsimp [score, pairwiseBordaScore]
    exact pmfExp_nonneg_of_forall_nonneg sampling _
      (fun opponent => preference.nonneg PUnit.unit alternative opponent)
  have hscore_le_one : score ≤ 1 := by
    dsimp [score, pairwiseBordaScore]
    exact pmfExp_le_of_forall_le sampling _ 1
      (fun opponent => preference.le_one PUnit.unit alternative opponent)
  have hmean_calibrated : meanWins = score * meanIncidences := by
    dsimp [meanWins, score, meanIncidences, reportLaw]
    exact theorem2UserBatchLaw_borda_calibrated comparisonsPerUser hcalibrated alternative
  have hmeanIncidences_pos : 0 < meanIncidences := by
    rw [show meanIncidences = (comparisonsPerUser : ℝ) * 2 * (sampling alternative).toReal by
      dsimp [meanIncidences, reportLaw]
      exact theorem2UserBatchLaw_pmfExp_bordaIncidences
        (preference := preference) comparisonsPerUser alternative]
    positivity
  have htotal_mean_pos : 0 < (users : ℝ) * meanIncidences := by positivity
  have hincidences_lower : (users : ℝ) * meanIncidences / 2 ≤ incidences := by
    have hleft := neg_le_of_abs_le hincidences_centered
    dsimp [incidences, meanIncidences, reportLaw] at hleft ⊢
    linarith
  have hmain := theorem11_normalizedBorda_error_le_of_centered_and_count_lower
    (wins := wins) (incidences := incidences) (score := score) (users := users)
    (meanWins := meanWins) (meanIncidences := meanIncidences) (cutoff := cutoff)
    hscore_nonneg hscore_le_one hmean_calibrated htotal_mean_pos hincidences_lower
    (by simpa [wins, meanWins, reportLaw] using hwins_centered)
    (by simpa [incidences, meanIncidences, reportLaw] using hincidences_centered) hcutoff_nonneg
  unfold theorem12EmpiricalBordaScore
  rw [if_neg (ne_of_gt (lt_of_lt_of_le (by linarith [htotal_mean_pos]) hincidences_lower))]
  simpa [wins, incidences, score, meanIncidences, reportLaw] using hmain

/--
Two-sided finite tail for total Borda wins of a fixed alternative under the
literal iid-user source model.  Its centering is the exact user-batch mean.
-/
theorem theorem11_iidBordaWins_abs_centered_tail
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (alternative : Alternative) (cutoff : ℝ) (hcutoff_nonneg : 0 ≤ cutoff)
    (hden_pos : 0 < (users : ℝ) * (2 * comparisonsPerUser : ℝ) ^ 2 +
      (2 * comparisonsPerUser : ℝ) * cutoff) :
    pmfProb (theorem12IidBordaReportBatchLaw
      (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser) users)
      (fun sample => cutoff ≤
        |theorem12EmpiricalBordaWins theorem2UserBatchBordaWins alternative sample -
          (users : ℝ) *
            pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser)
              (theorem2UserBatchBordaWins alternative)|) ≤
      2 * Real.exp (-cutoff ^ 2 /
        (4 * ((users : ℝ) * (2 * comparisonsPerUser : ℝ) ^ 2 +
          (2 * comparisonsPerUser : ℝ) * cutoff))) := by
  letI : MeasurableSpace (theorem2UserBatchReport Alternative comparisonsPerUser) := ⊤
  let reportLaw := theorem2UserBatchLaw responseLaw sampling comparisonsPerUser
  let range : ℝ := 2 * comparisonsPerUser
  have hrange_nonneg : 0 ≤ range := by
    dsimp [range]
    positivity
  have htail := pmfProb_pmfProduct_abs_sum_sub_mean_ge_le_bernstein_of_nonneg_le
    (ι := Fin users) reportLaw (theorem2UserBatchBordaWins alternative) range cutoff
    (fun report => theorem2UserBatchBordaWins_nonneg alternative report)
    (fun report => theorem11_userBatchBordaWins_le_two_mul_comparisons alternative report)
    hrange_nonneg hcutoff_nonneg
    (by simpa [range, Fintype.card_fin] using hden_pos)
  simpa [theorem12IidBordaReportBatchLaw, theorem12EmpiricalBordaWins, reportLaw,
    range, Fintype.card_fin] using htail

/--
Two-sided finite tail for total Borda incidences of a fixed alternative under
the literal iid-user source model.
-/
theorem theorem11_iidBordaIncidences_abs_centered_tail
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (alternative : Alternative) (cutoff : ℝ) (hcutoff_nonneg : 0 ≤ cutoff)
    (hden_pos : 0 < (users : ℝ) * (2 * comparisonsPerUser : ℝ) ^ 2 +
      (2 * comparisonsPerUser : ℝ) * cutoff) :
    pmfProb (theorem12IidBordaReportBatchLaw
      (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser) users)
      (fun sample => cutoff ≤
        |theorem12EmpiricalBordaIncidences theorem2UserBatchBordaIncidences alternative sample -
          (users : ℝ) *
            pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser)
              (theorem2UserBatchBordaIncidences alternative)|) ≤
      2 * Real.exp (-cutoff ^ 2 /
        (4 * ((users : ℝ) * (2 * comparisonsPerUser : ℝ) ^ 2 +
          (2 * comparisonsPerUser : ℝ) * cutoff))) := by
  letI : MeasurableSpace (theorem2UserBatchReport Alternative comparisonsPerUser) := ⊤
  let reportLaw := theorem2UserBatchLaw responseLaw sampling comparisonsPerUser
  let range : ℝ := 2 * comparisonsPerUser
  have hrange_nonneg : 0 ≤ range := by
    dsimp [range]
    positivity
  have htail := pmfProb_pmfProduct_abs_sum_sub_mean_ge_le_bernstein_of_nonneg_le
    (ι := Fin users) reportLaw (theorem2UserBatchBordaIncidences alternative) range cutoff
    (fun report => by
      unfold theorem2UserBatchBordaIncidences
      exact Finset.sum_nonneg fun position _ => by
        rcases report position with ⟨⟨first, second⟩, outcome⟩
        by_cases hfirst : first = alternative <;> by_cases hsecond : second = alternative <;>
          simp [theorem12OneComparisonIncidences, hfirst, hsecond])
    (fun report => theorem11_userBatchBordaIncidences_le_two_mul_comparisons alternative report)
    hrange_nonneg hcutoff_nonneg
    (by simpa [range, Fintype.card_fin] using hden_pos)
  simpa [theorem12IidBordaReportBatchLaw, theorem12EmpiricalBordaIncidences, reportLaw,
    range, Fintype.card_fin] using htail

/--
Finite normalized-Borda deviation bound for one alternative in the literal
source user-batch model.  It is an exact finite statement, retaining the
source's potentially correlated answers within each user.  The displayed
constant comes from a bounded-count Bernstein estimate, not an asymptotic
independence approximation.
-/
theorem theorem11_iidBordaScore_tail_bound
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative)
    (users comparisonsPerUser : ℕ) (husers : 0 < users) (hcomparisons : 0 < comparisonsPerUser)
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (alternative : Alternative) (hsampling_pos : 0 < (sampling alternative).toReal)
    (cutoff : ℝ) (hcutoff_nonneg : 0 ≤ cutoff)
    (hcutoff_small : cutoff ≤
      (users : ℝ) *
        pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser)
          (theorem2UserBatchBordaIncidences alternative) / 2)
    (hden_pos : 0 < (users : ℝ) * (2 * comparisonsPerUser : ℝ) ^ 2 +
      (2 * comparisonsPerUser : ℝ) * cutoff) :
    pmfProb (theorem12IidBordaReportBatchLaw
      (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser) users)
      (fun sample =>
        4 * cutoff /
            ((users : ℝ) *
              pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser)
                (theorem2UserBatchBordaIncidences alternative)) <
          |theorem12EmpiricalBordaScore theorem2UserBatchBordaWins theorem2UserBatchBordaIncidences
              alternative sample - pairwiseBordaScore sampling preference alternative|) ≤
      4 * Real.exp (-cutoff ^ 2 /
        (4 * ((users : ℝ) * (2 * comparisonsPerUser : ℝ) ^ 2 +
          (2 * comparisonsPerUser : ℝ) * cutoff)) ) := by
  classical
  let law := theorem12IidBordaReportBatchLaw
    (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser) users
  let winsEvent : (Fin users → theorem2UserBatchReport Alternative comparisonsPerUser) → Prop :=
    fun sample => cutoff ≤
      |theorem12EmpiricalBordaWins theorem2UserBatchBordaWins alternative sample -
        (users : ℝ) *
          pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser)
            (theorem2UserBatchBordaWins alternative)|
  let incidencesEvent : (Fin users → theorem2UserBatchReport Alternative comparisonsPerUser) → Prop :=
    fun sample => cutoff ≤
      |theorem12EmpiricalBordaIncidences theorem2UserBatchBordaIncidences alternative sample -
        (users : ℝ) *
          pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser)
            (theorem2UserBatchBordaIncidences alternative)|
  let tail := 2 * Real.exp (-cutoff ^ 2 /
    (4 * ((users : ℝ) * (2 * comparisonsPerUser : ℝ) ^ 2 +
      (2 * comparisonsPerUser : ℝ) * cutoff)))
  have hwins_tail : pmfProb law winsEvent ≤ tail := by
    dsimp [law, winsEvent, tail]
    exact theorem11_iidBordaWins_abs_centered_tail responseLaw sampling users comparisonsPerUser
      alternative cutoff hcutoff_nonneg hden_pos
  have hincidences_tail : pmfProb law incidencesEvent ≤ tail := by
    dsimp [law, incidencesEvent, tail]
    exact theorem11_iidBordaIncidences_abs_centered_tail responseLaw sampling users comparisonsPerUser
      alternative cutoff hcutoff_nonneg hden_pos
  have himp : ∀ sample,
      4 * cutoff /
            ((users : ℝ) *
              pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser)
                (theorem2UserBatchBordaIncidences alternative)) <
          |theorem12EmpiricalBordaScore theorem2UserBatchBordaWins theorem2UserBatchBordaIncidences
              alternative sample - pairwiseBordaScore sampling preference alternative| →
        winsEvent sample ∨ incidencesEvent sample := by
    intro sample hbad
    by_cases hwins : winsEvent sample
    · exact Or.inl hwins
    by_cases hincidences : incidencesEvent sample
    · exact Or.inr hincidences
    exfalso
    have hgood := theorem11_iidBordaScore_error_le_of_centered
      responseLaw sampling preference users comparisonsPerUser husers hcomparisons hcalibrated
      alternative hsampling_pos cutoff hcutoff_nonneg hcutoff_small sample
      (le_of_lt (lt_of_not_ge hwins)) (le_of_lt (lt_of_not_ge hincidences))
    exact (not_lt_of_ge hgood) hbad
  calc
    pmfProb law (fun sample =>
        4 * cutoff /
            ((users : ℝ) *
              pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser)
                (theorem2UserBatchBordaIncidences alternative)) <
          |theorem12EmpiricalBordaScore theorem2UserBatchBordaWins theorem2UserBatchBordaIncidences
              alternative sample - pairwiseBordaScore sampling preference alternative|) ≤
        pmfProb law (fun sample => winsEvent sample ∨ incidencesEvent sample) :=
      pmfProb_le_of_imp law _ _ himp
    _ ≤ pmfProb law winsEvent + pmfProb law incidencesEvent :=
      pmfProb_or_le law winsEvent incidencesEvent
    _ ≤ tail + tail := add_le_add hwins_tail hincidences_tail
    _ = 4 * Real.exp (-cutoff ^ 2 /
        (4 * ((users : ℝ) * (2 * comparisonsPerUser : ℝ) ^ 2 +
          (2 * comparisonsPerUser : ℝ) * cutoff)) ) := by
      dsimp [tail]
      ring

/--
Finite all-alternatives union of the literal Lemma 11 Borda tails.  The
radius retains each alternative's exact expected incidence count, so this is
the concentration statement before a minimum-mass substitution.
-/
theorem theorem11_iidBordaScore_uniform_tail_bound
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative)
    (users comparisonsPerUser : ℕ) (husers : 0 < users) (hcomparisons : 0 < comparisonsPerUser)
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (hsampling_pos : ∀ alternative, 0 < (sampling alternative).toReal)
    (cutoff : ℝ) (hcutoff_nonneg : 0 ≤ cutoff)
    (hcutoff_small : ∀ alternative, cutoff ≤
      (users : ℝ) *
        pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser)
          (theorem2UserBatchBordaIncidences alternative) / 2)
    (hden_pos : 0 < (users : ℝ) * (2 * comparisonsPerUser : ℝ) ^ 2 +
      (2 * comparisonsPerUser : ℝ) * cutoff) :
    pmfProb (theorem12IidBordaReportBatchLaw
      (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser) users)
      (fun sample => ∃ alternative,
        4 * cutoff /
            ((users : ℝ) *
              pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser)
                (theorem2UserBatchBordaIncidences alternative)) <
          |theorem12EmpiricalBordaScore theorem2UserBatchBordaWins theorem2UserBatchBordaIncidences
              alternative sample - pairwiseBordaScore sampling preference alternative|) ≤
      ∑ _alternative : Alternative,
        4 * Real.exp (-cutoff ^ 2 /
          (4 * ((users : ℝ) * (2 * comparisonsPerUser : ℝ) ^ 2 +
            (2 * comparisonsPerUser : ℝ) * cutoff))) := by
  classical
  let law := theorem12IidBordaReportBatchLaw
    (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser) users
  let tail : ℝ := 4 * Real.exp (-cutoff ^ 2 /
    (4 * ((users : ℝ) * (2 * comparisonsPerUser : ℝ) ^ 2 +
      (2 * comparisonsPerUser : ℝ) * cutoff)))
  have hfixed : ∀ alternative : Alternative,
      pmfProb law (fun sample =>
        4 * cutoff /
            ((users : ℝ) *
              pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser)
                (theorem2UserBatchBordaIncidences alternative)) <
          |theorem12EmpiricalBordaScore theorem2UserBatchBordaWins theorem2UserBatchBordaIncidences
              alternative sample - pairwiseBordaScore sampling preference alternative|) ≤ tail := by
    intro alternative
    simpa [law, tail] using
      (theorem11_iidBordaScore_tail_bound responseLaw sampling preference users comparisonsPerUser
        husers hcomparisons hcalibrated alternative (hsampling_pos alternative) cutoff hcutoff_nonneg
        (hcutoff_small alternative) hden_pos)
  calc
    pmfProb law (fun sample => ∃ alternative,
        4 * cutoff /
            ((users : ℝ) *
              pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser)
                (theorem2UserBatchBordaIncidences alternative)) <
          |theorem12EmpiricalBordaScore theorem2UserBatchBordaWins theorem2UserBatchBordaIncidences
              alternative sample - pairwiseBordaScore sampling preference alternative|) ≤
        ∑ alternative : Alternative,
          pmfProb law (fun sample =>
            4 * cutoff /
                ((users : ℝ) *
                  pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser)
                    (theorem2UserBatchBordaIncidences alternative)) <
                |theorem12EmpiricalBordaScore theorem2UserBatchBordaWins
                    theorem2UserBatchBordaIncidences alternative sample -
                  pairwiseBordaScore sampling preference alternative|) := by
          simpa using (pmfProb_exists_mem_le_sum law (Finset.univ : Finset Alternative)
            (fun alternative sample =>
              4 * cutoff /
                  ((users : ℝ) *
                    pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser)
                      (theorem2UserBatchBordaIncidences alternative)) <
                |theorem12EmpiricalBordaScore theorem2UserBatchBordaWins
                    theorem2UserBatchBordaIncidences alternative sample -
                  pairwiseBordaScore sampling preference alternative|))
    _ ≤ ∑ _alternative : Alternative, tail := by
      apply Finset.sum_le_sum
      intro alternative _
      exact hfixed alternative
    _ = ∑ _alternative : Alternative,
        4 * Real.exp (-cutoff ^ 2 /
          (4 * ((users : ℝ) * (2 * comparisonsPerUser : ℝ) ^ 2 +
            (2 * comparisonsPerUser : ℝ) * cutoff))) := by rfl

/--
Minimum-mass form of the finite all-alternatives Lemma 11 tail.  It uses the
exact expected incidence `2d μ(a)` and so preserves the literal correlated
within-user model.  Its range-based exponent is intentionally not identified
with the sharper asymptotic Borda rate printed in the source.
-/
theorem theorem11_iidBordaScore_uniform_minMass_tail_bound
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative)
    (users comparisonsPerUser : ℕ) (husers : 0 < users) (hcomparisons : 0 < comparisonsPerUser)
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (minimumMass cutoff : ℝ) (hminimumMass_pos : 0 < minimumMass)
    (hminimumMass : ∀ alternative, minimumMass ≤ (sampling alternative).toReal)
    (hcutoff_nonneg : 0 ≤ cutoff)
    (hcutoff_small : cutoff ≤
      (users : ℝ) * (comparisonsPerUser : ℝ) * minimumMass) :
    pmfProb (theorem12IidBordaReportBatchLaw
      (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser) users)
      (fun sample => ∃ alternative,
        2 * cutoff / ((users : ℝ) * (comparisonsPerUser : ℝ) * minimumMass) <
          |theorem12EmpiricalBordaScore theorem2UserBatchBordaWins theorem2UserBatchBordaIncidences
              alternative sample - pairwiseBordaScore sampling preference alternative|) ≤
      ∑ _alternative : Alternative,
        4 * Real.exp (-cutoff ^ 2 /
          (4 * ((users : ℝ) * (2 * comparisonsPerUser : ℝ) ^ 2 +
            (2 * comparisonsPerUser : ℝ) * cutoff))) := by
  classical
  let law := theorem12IidBordaReportBatchLaw
    (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser) users
  have hsampling_pos : ∀ alternative, 0 < (sampling alternative).toReal := by
    intro alternative
    exact lt_of_lt_of_le hminimumMass_pos (hminimumMass alternative)
  have hcutoff_small_exact : ∀ alternative, cutoff ≤
      (users : ℝ) *
        pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser)
          (theorem2UserBatchBordaIncidences alternative) / 2 := by
    intro alternative
    rw [theorem2UserBatchLaw_pmfExp_bordaIncidences (preference := preference)]
    have hmass_lower := hminimumMass alternative
    nlinarith
  have hden_pos : 0 < (users : ℝ) * (2 * comparisonsPerUser : ℝ) ^ 2 +
      (2 * comparisonsPerUser : ℝ) * cutoff := by
    have hmain : 0 < (users : ℝ) * (2 * comparisonsPerUser : ℝ) ^ 2 := by positivity
    have hrest : 0 ≤ (2 * comparisonsPerUser : ℝ) * cutoff := by positivity
    linarith
  let minMassEvent :
      (Fin users → theorem2UserBatchReport Alternative comparisonsPerUser) → Prop :=
    fun sample => ∃ alternative,
      2 * cutoff / ((users : ℝ) * (comparisonsPerUser : ℝ) * minimumMass) <
        |theorem12EmpiricalBordaScore theorem2UserBatchBordaWins theorem2UserBatchBordaIncidences
            alternative sample - pairwiseBordaScore sampling preference alternative|
  let rawEvent :
      (Fin users → theorem2UserBatchReport Alternative comparisonsPerUser) → Prop :=
    fun sample => ∃ alternative,
      4 * cutoff /
          ((users : ℝ) *
            pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser)
              (theorem2UserBatchBordaIncidences alternative)) <
        |theorem12EmpiricalBordaScore theorem2UserBatchBordaWins theorem2UserBatchBordaIncidences
            alternative sample - pairwiseBordaScore sampling preference alternative|
  have hraw := theorem11_iidBordaScore_uniform_tail_bound responseLaw sampling preference users
    comparisonsPerUser husers hcomparisons hcalibrated hsampling_pos cutoff hcutoff_nonneg
    hcutoff_small_exact hden_pos
  change pmfProb law minMassEvent ≤ _
  refine (pmfProb_le_of_imp law minMassEvent rawEvent ?_).trans ?_
  · rintro sample ⟨alternative, hbad⟩
    refine ⟨alternative, ?_⟩
    have hmean : pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser)
        (theorem2UserBatchBordaIncidences alternative) =
        (comparisonsPerUser : ℝ) * 2 * (sampling alternative).toReal :=
      theorem2UserBatchLaw_pmfExp_bordaIncidences (preference := preference)
        comparisonsPerUser alternative
    have hden_small_pos : 0 < (users : ℝ) * (comparisonsPerUser : ℝ) * minimumMass := by
      positivity
    have hden_mass_pos : 0 < (users : ℝ) * (comparisonsPerUser : ℝ) *
        (sampling alternative).toReal := by
      exact mul_pos
        (mul_pos (by exact_mod_cast husers) (by exact_mod_cast hcomparisons))
        (hsampling_pos alternative)
    have hraw_radius_le :
        4 * cutoff /
            ((users : ℝ) *
              pmfExp (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser)
                (theorem2UserBatchBordaIncidences alternative)) ≤
          2 * cutoff / ((users : ℝ) * (comparisonsPerUser : ℝ) * minimumMass) := by
      rw [hmean]
      calc
        4 * cutoff /
            ((users : ℝ) * ((comparisonsPerUser : ℝ) * 2 *
              (sampling alternative).toReal)) =
            2 * cutoff /
              ((users : ℝ) * (comparisonsPerUser : ℝ) *
                (sampling alternative).toReal) := by
              field_simp [hden_mass_pos.ne']
              ring
        _ ≤ 2 * cutoff / ((users : ℝ) * (comparisonsPerUser : ℝ) * minimumMass) :=
          div_le_div_of_nonneg_left (by positivity) hden_small_pos
            (mul_le_mul_of_nonneg_left (hminimumMass alternative)
              (by positivity : 0 ≤ (users : ℝ) * (comparisonsPerUser : ℝ)))
    exact lt_of_le_of_lt hraw_radius_le hbad
  · simpa [law, rawEvent] using hraw

end GolzHaghtalabYang2025Distortion
