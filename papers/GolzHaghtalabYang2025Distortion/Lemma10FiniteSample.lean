import GolzHaghtalabYang2025Distortion.Theorem2UserBatch
import AppliedModelingLib.Foundations.Probability.IndependentIndicators
import AppliedModelingLib.Foundations.Probability.IndependentBounded

/-!
# Fixed-pair statistics for Appendix D, Lemma 10

This module begins the literal count-ratio route in the source proof. For a
fixed distinct unordered pair, each user's iid pair labels determine a binomial
incidence count. The user response itself is still shared across that user's
displays, as required by the source model.
-/

namespace GolzHaghtalabYang2025Distortion

open scoped BigOperators

open AppliedModelingLib
open AppliedModelingLib.Learning.HumanFeedback
open AppliedModelingLib.Probability

/-- Indicator that an ordered pair label displays a given unordered distinct pair. -/
def theorem10UnorderedPairIndicator
    {Alternative : Type*} [DecidableEq Alternative]
    (first second : Alternative) : Alternative × Alternative → ℝ
  | (left, right) =>
      if (left = first ∧ right = second) ∨ (left = second ∧ right = first) then 1 else 0

/--
For distinct alternatives, one iid ordered-pair label displays their unordered
pair with probability exactly twice the product of their sampling masses.
-/
theorem theorem10_pmfExp_unorderedPairIndicator
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (first second : Alternative) (hdistinct : first ≠ second) :
    pmfExp (theorem2UserPairLabelLaw sampling)
      (theorem10UnorderedPairIndicator first second) =
      2 * (sampling first).toReal * (sampling second).toReal := by
  unfold theorem2UserPairLabelLaw
  rw [pmfExp_pmfProd_eq_pairExp]
  rw [show (fun left right => theorem10UnorderedPairIndicator first second (left, right)) =
      fun left right =>
        (if left = first ∧ right = second then (1 : ℝ) else 0) +
        if left = second ∧ right = first then 1 else 0 by
        funext left right
        by_cases hforward : left = first ∧ right = second
        · rcases hforward with ⟨rfl, rfl⟩
          simp [theorem10UnorderedPairIndicator, hdistinct]
        · by_cases hreverse : left = second ∧ right = first
          · rcases hreverse with ⟨rfl, rfl⟩
            simp [theorem10UnorderedPairIndicator, hdistinct]
          · simp [theorem10UnorderedPairIndicator, hforward, hreverse]]
  rw [pmfPairExp_add]
  have hforward :
      pmfPairExp sampling sampling (fun left right =>
        if left = first ∧ right = second then (1 : ℝ) else 0) =
      (sampling first).toReal * (sampling second).toReal := by
    unfold pmfPairExp
    rw [show (fun left => pmfExp sampling (fun right =>
        if left = first ∧ right = second then (1 : ℝ) else 0)) =
        fun left => (if left = first then (1 : ℝ) else 0) * (sampling second).toReal by
          funext left
          by_cases hleft : left = first
          · subst left
            simp only [true_and, ↓reduceIte]
            rw [theorem12_pmfExp_eq_indicator]
            ring
          · simp [hleft]]
    rw [theorem12_pmfExp_eq_indicator_mul]
  have hreverse :
      pmfPairExp sampling sampling (fun left right =>
        if left = second ∧ right = first then (1 : ℝ) else 0) =
      (sampling second).toReal * (sampling first).toReal := by
    unfold pmfPairExp
    rw [show (fun left => pmfExp sampling (fun right =>
        if left = second ∧ right = first then (1 : ℝ) else 0)) =
        fun left => (if left = second then (1 : ℝ) else 0) * (sampling first).toReal by
          funext left
          by_cases hleft : left = second
          · subst left
            simp only [true_and, ↓reduceIte]
            rw [theorem12_pmfExp_eq_indicator]
            ring
          · simp [hleft]]
    rw [theorem12_pmfExp_eq_indicator_mul]
  rw [hforward, hreverse]
  ring

/-- The number of displays of a fixed unordered pair in one user's iid labels. -/
def theorem10UserUnorderedPairCount
    {Alternative : Type*} [DecidableEq Alternative] {comparisonsPerUser : ℕ}
    (first second : Alternative) (labels : Fin comparisonsPerUser → Alternative × Alternative) : ℝ :=
  ∑ position, theorem10UnorderedPairIndicator first second (labels position)

/--
The source pair-incidence count has the binomial mean `d * 2 μ(x) μ(y)`.
This is the exact first-moment part of Lemma 10's `kᵢ ∼ Binomial(d,q)`
reduction.
-/
theorem theorem10_pmfExp_userUnorderedPairCount
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (comparisonsPerUser : ℕ)
    (first second : Alternative) (hdistinct : first ≠ second) :
    pmfExp
      (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
        (theorem2UserPairLabelLaw sampling))
      (theorem10UserUnorderedPairCount first second) =
      (comparisonsPerUser : ℝ) * 2 *
        (sampling first).toReal * (sampling second).toReal := by
  unfold theorem10UserUnorderedPairCount
  rw [pmfExp_univ_sum]
  calc
    (∑ position : Fin comparisonsPerUser,
        pmfExp
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))
          (fun labels => theorem10UnorderedPairIndicator first second (labels position))) =
      ∑ _position : Fin comparisonsPerUser,
        pmfExp (theorem2UserPairLabelLaw sampling)
          (theorem10UnorderedPairIndicator first second) := by
        apply Finset.sum_congr rfl
        intro position _
        exact pmfExp_pmfProduct_eval (theorem2UserPairLabelLaw sampling) position
          (theorem10UnorderedPairIndicator first second)
    _ = ∑ _position : Fin comparisonsPerUser,
        2 * (sampling first).toReal * (sampling second).toReal := by
        apply Finset.sum_congr rfl
        intro position _
        exact theorem10_pmfExp_unorderedPairIndicator sampling first second hdistinct
    _ = (comparisonsPerUser : ℝ) * 2 *
        (sampling first).toReal * (sampling second).toReal := by
        simp [nsmul_eq_mul]
        ring

/-- The Boolean event that an ordered label displays a fixed unordered pair. -/
private def theorem10UnorderedPairEvent
    {Alternative : Type*} [DecidableEq Alternative]
    (first second : Alternative) (label : Alternative × Alternative) : Bool :=
  decide ((label.1 = first ∧ label.2 = second) ∨
    (label.1 = second ∧ label.2 = first))

/-- The finite double sum whose diagonal has value `a` and off-diagonal has value `b`. -/
private theorem theorem10_doubleSum_diag_offdiag
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ℝ) :
    (Finset.univ.sum fun i : ι =>
      Finset.univ.sum fun j : ι => if i = j then a else b) =
      (Fintype.card ι : ℝ) * a +
        (Fintype.card ι : ℝ) * ((Fintype.card ι - 1 : ℕ) : ℝ) * b := by
  calc
    (Finset.univ.sum fun i : ι =>
      Finset.univ.sum fun j : ι => if i = j then a else b) =
        Finset.univ.sum fun i : ι =>
          ((Finset.univ.erase i).sum fun _j : ι => b) + a := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
          rw [if_pos rfl]
          congr 1
          refine Finset.sum_congr rfl ?_
          intro j hj
          exact if_neg (Ne.symm (Finset.mem_erase.mp hj).1)
    _ = Finset.univ.sum fun _i : ι =>
        ((Fintype.card ι - 1 : ℕ) : ℝ) * b + a := by
          refine Finset.sum_congr rfl ?_
          intro i _
          simp [Finset.card_erase_of_mem, nsmul_eq_mul]
    _ = (Fintype.card ι : ℝ) * a +
        (Fintype.card ι : ℝ) * ((Fintype.card ι - 1 : ℕ) : ℝ) * b := by
          simp [nsmul_eq_mul]
          ring

/-- One label-position displays the fixed unordered pair with the source probability `q`. -/
private theorem theorem10_pmfProb_unorderedPairAt
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (comparisonsPerUser : ℕ)
    (first second : Alternative) (hdistinct : first ≠ second)
    (position : Fin comparisonsPerUser) :
    pmfProb
      (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
        (theorem2UserPairLabelLaw sampling))
      (fun labels => theorem10UnorderedPairEvent first second (labels position) = true) =
      2 * (sampling first).toReal * (sampling second).toReal := by
  classical
  change pmfExp
      (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
        (theorem2UserPairLabelLaw sampling))
      (fun labels => if theorem10UnorderedPairEvent first second (labels position) = true
        then (1 : ℝ) else 0) = _
  calc
    pmfExp
        (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
          (theorem2UserPairLabelLaw sampling))
        (fun labels => if theorem10UnorderedPairEvent first second (labels position) = true
          then (1 : ℝ) else 0) =
        pmfExp
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))
          (fun labels => theorem10UnorderedPairIndicator first second (labels position)) := by
            apply pmfExp_congr
            intro labels
            simp [theorem10UnorderedPairEvent, theorem10UnorderedPairIndicator]
    _ = pmfExp (theorem2UserPairLabelLaw sampling)
          (theorem10UnorderedPairIndicator first second) := by
            rw [pmfExp_pmfProduct_eval]
    _ = _ := theorem10_pmfExp_unorderedPairIndicator sampling first second hdistinct

/-- Distinct iid label positions display the pair jointly with probability `q²`. -/
private theorem theorem10_pmfProb_unorderedPairAt_inter
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (comparisonsPerUser : ℕ)
    (first second : Alternative) (hdistinct : first ≠ second)
    {left right : Fin comparisonsPerUser} (hposition : left ≠ right) :
    pmfProb
      (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
        (theorem2UserPairLabelLaw sampling))
      (fun labels => theorem10UnorderedPairEvent first second (labels left) = true ∧
        theorem10UnorderedPairEvent first second (labels right) = true) =
      (2 * (sampling first).toReal * (sampling second).toReal) ^ 2 := by
  classical
  change pmfProb (pmfPi (fun _ : Fin comparisonsPerUser =>
      theorem2UserPairLabelLaw sampling))
      (fun labels => theorem10UnorderedPairEvent first second (labels left) = true ∧
        theorem10UnorderedPairEvent first second (labels right) = true) = _
  rw [pmfProb_pmfPi_twoCoord_eq_pmfProd (fun _ : Fin comparisonsPerUser =>
    theorem2UserPairLabelLaw sampling) hposition
    (fun labelLeft labelRight => theorem10UnorderedPairEvent first second labelLeft = true ∧
      theorem10UnorderedPairEvent first second labelRight = true)]
  change pmfExp
      (pmfProd (theorem2UserPairLabelLaw sampling) (theorem2UserPairLabelLaw sampling))
      (fun labels => if theorem10UnorderedPairEvent first second labels.1 = true ∧
        theorem10UnorderedPairEvent first second labels.2 = true then (1 : ℝ) else 0) = _
  rw [pmfExp_pmfProd_eq_pairExp]
  rw [show (fun labelLeft labelRight =>
      if theorem10UnorderedPairEvent first second labelLeft = true ∧
        theorem10UnorderedPairEvent first second labelRight = true then (1 : ℝ) else 0) =
      fun labelLeft labelRight =>
        theorem10UnorderedPairIndicator first second labelLeft *
          theorem10UnorderedPairIndicator first second labelRight by
        funext labelLeft labelRight
        by_cases hleft :
          (labelLeft.1 = first ∧ labelLeft.2 = second) ∨
            (labelLeft.1 = second ∧ labelLeft.2 = first)
        · by_cases hright :
            (labelRight.1 = first ∧ labelRight.2 = second) ∨
              (labelRight.1 = second ∧ labelRight.2 = first)
          · simp [theorem10UnorderedPairEvent, theorem10UnorderedPairIndicator, hleft, hright]
          · simp [theorem10UnorderedPairEvent, theorem10UnorderedPairIndicator, hleft, hright]
        · by_cases hright :
            (labelRight.1 = first ∧ labelRight.2 = second) ∨
              (labelRight.1 = second ∧ labelRight.2 = first)
          · simp [theorem10UnorderedPairEvent, theorem10UnorderedPairIndicator, hleft, hright]
          · simp [theorem10UnorderedPairEvent, theorem10UnorderedPairIndicator, hleft, hright]]
  rw [pmfPairExp_mul_separable]
  rw [theorem10_pmfExp_unorderedPairIndicator sampling first second hdistinct]
  ring

/-- The indicator-sum representation is exactly the corresponding finite event count. -/
private theorem theorem10_unorderedPairCount_eq_card_filter
    {Alternative : Type*} [DecidableEq Alternative] {comparisonsPerUser : ℕ}
    (first second : Alternative)
    (labels : Fin comparisonsPerUser → Alternative × Alternative) :
    theorem10UserUnorderedPairCount first second labels =
      (((Finset.univ : Finset (Fin comparisonsPerUser)).filter
        (fun position => theorem10UnorderedPairEvent first second (labels position) = true)).card : ℝ) := by
  unfold theorem10UserUnorderedPairCount
  simp [theorem10UnorderedPairEvent, theorem10UnorderedPairIndicator]

/--
Exact second moment of the source's fixed-pair incidence count.  This is the
finite `Binomial(d,q)` identity in Appendix D, with `q = 2 μ(x) μ(y)`.
-/
theorem theorem10_pmfExp_userUnorderedPairCount_sq
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (comparisonsPerUser : ℕ)
    (first second : Alternative) (hdistinct : first ≠ second) :
    let q : ℝ := 2 * (sampling first).toReal * (sampling second).toReal
    pmfExp
      (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
        (theorem2UserPairLabelLaw sampling))
      (fun labels => (theorem10UserUnorderedPairCount first second labels) ^ 2) =
      (comparisonsPerUser : ℝ) * q +
        (comparisonsPerUser : ℝ) * ((comparisonsPerUser - 1 : ℕ) : ℝ) * q ^ 2 := by
  classical
  dsimp
  calc
    pmfExp
        (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
          (theorem2UserPairLabelLaw sampling))
        (fun labels => (theorem10UserUnorderedPairCount first second labels) ^ 2) =
        pmfExp
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))
          (fun labels =>
            (((Finset.univ : Finset (Fin comparisonsPerUser)).filter
              (fun position => theorem10UnorderedPairEvent first second (labels position) = true)).card : ℝ) ^ 2) := by
            apply pmfExp_congr
            intro labels
            rw [theorem10_unorderedPairCount_eq_card_filter]
    _ = ∑ left : Fin comparisonsPerUser, ∑ right : Fin comparisonsPerUser,
          pmfProb
            (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
              (theorem2UserPairLabelLaw sampling))
            (fun labels => theorem10UnorderedPairEvent first second (labels left) = true ∧
              theorem10UnorderedPairEvent first second (labels right) = true) := by
            exact pmfExp_card_filter_sq_eq_sum_pmfProb_inter _ _
    _ = Finset.univ.sum fun left : Fin comparisonsPerUser =>
          Finset.univ.sum fun right : Fin comparisonsPerUser =>
            if left = right then
              2 * (sampling first).toReal * (sampling second).toReal
            else (2 * (sampling first).toReal * (sampling second).toReal) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro left _
          refine Finset.sum_congr rfl ?_
          intro right _
          by_cases hposition : left = right
          · subst right
            simp [theorem10_pmfProb_unorderedPairAt sampling comparisonsPerUser first second hdistinct]
          · rw [theorem10_pmfProb_unorderedPairAt_inter sampling comparisonsPerUser first second hdistinct
              hposition]
            simp [hposition]
    _ = (comparisonsPerUser : ℝ) *
          (2 * (sampling first).toReal * (sampling second).toReal) +
        (comparisonsPerUser : ℝ) * ((comparisonsPerUser - 1 : ℕ) : ℝ) *
          (2 * (sampling first).toReal * (sampling second).toReal) ^ 2 := by
          simpa using
            (theorem10_doubleSum_diag_offdiag
              (ι := Fin comparisonsPerUser)
              (2 * (sampling first).toReal * (sampling second).toReal)
              ((2 * (sampling first).toReal * (sampling second).toReal) ^ 2))

/--
One user's number of wins by `first` on displays of the unordered pair
`{first, second}`. The response table is shared across that user's labels.
-/
def theorem10UserUnorderedPairWins
    {Alternative : Type*} [DecidableEq Alternative] {comparisonsPerUser : ℕ}
    (first second : Alternative) (response : theorem2UserResponseTable Alternative)
    (labels : Fin comparisonsPerUser → Alternative × Alternative) : ℝ :=
  ∑ position, theorem10UnorderedPairIndicator first second (labels position) *
    theorem12OneComparisonWins first
      ((labels position), response (labels position).1 (labels position).2)

/-- The centered per-user pair statistic used in Appendix D's Bernstein step. -/
def theorem10UserCenteredPairWin
    {Alternative : Type*} [DecidableEq Alternative] {comparisonsPerUser : ℕ}
    (first second : Alternative) (winProbability : ℝ)
    (response : theorem2UserResponseTable Alternative)
    (labels : Fin comparisonsPerUser → Alternative × Alternative) : ℝ :=
  theorem10UserUnorderedPairWins first second response labels -
    winProbability * theorem10UserUnorderedPairCount first second labels

/-- A fixed-pair incidence indicator is pointwise nonnegative. -/
private theorem theorem10_unorderedPairIndicator_nonneg
    {Alternative : Type*} [DecidableEq Alternative]
    (first second : Alternative) (label : Alternative × Alternative) :
    0 ≤ theorem10UnorderedPairIndicator first second label := by
  rcases label with ⟨left, right⟩
  simp only [theorem10UnorderedPairIndicator]
  split <;> norm_num

/-- The restricted win count is nonnegative. -/
theorem theorem10UserUnorderedPairWins_nonneg
    {Alternative : Type*} [DecidableEq Alternative] {comparisonsPerUser : ℕ}
    (first second : Alternative) (response : theorem2UserResponseTable Alternative)
    (labels : Fin comparisonsPerUser → Alternative × Alternative) :
    0 ≤ theorem10UserUnorderedPairWins first second response labels := by
  unfold theorem10UserUnorderedPairWins
  refine Finset.sum_nonneg ?_
  intro position _
  exact mul_nonneg (theorem10_unorderedPairIndicator_nonneg first second (labels position))
    (theorem12OneComparisonWins_nonneg first
      ((labels position), response (labels position).1 (labels position).2))

/-- A user's restricted wins cannot exceed their number of displays of that pair. -/
theorem theorem10UserUnorderedPairWins_le_count
    {Alternative : Type*} [DecidableEq Alternative] {comparisonsPerUser : ℕ}
    (first second : Alternative) (hdistinct : first ≠ second)
    (response : theorem2UserResponseTable Alternative)
    (labels : Fin comparisonsPerUser → Alternative × Alternative) :
    theorem10UserUnorderedPairWins first second response labels ≤
      theorem10UserUnorderedPairCount first second labels := by
  unfold theorem10UserUnorderedPairWins theorem10UserUnorderedPairCount
  refine Finset.sum_le_sum ?_
  intro position _
  generalize hlabel : labels position = label
  rcases label with ⟨left, right⟩
  dsimp
  by_cases hpair :
      (left = first ∧ right = second) ∨
        (left = second ∧ right = first)
  · rcases hpair with hforward | hreverse
    · rcases hforward with ⟨hleft, hright⟩
      subst left
      subst right
      cases hresponse : response first second <;>
        simp [theorem10UnorderedPairIndicator, theorem12OneComparisonWins, hdistinct,
          Ne.symm hdistinct]
    · rcases hreverse with ⟨hleft, hright⟩
      subst left
      subst right
      cases hresponse : response second first <;>
        simp [theorem10UnorderedPairIndicator, theorem12OneComparisonWins, hdistinct,
          Ne.symm hdistinct]
  · simp [theorem10UnorderedPairIndicator, hpair]

/--
Under the source's orientation-consistent response table, a user's restricted
win count is exactly its pair-display count times that user's fixed pair answer.
-/
theorem theorem10UserUnorderedPairWins_eq_count_mul_response
    {Alternative : Type*} [DecidableEq Alternative] {comparisonsPerUser : ℕ}
    (first second : Alternative) (hdistinct : first ≠ second)
    (response : theorem2UserResponseTable Alternative)
    (hconsistent : theorem2UserResponseOrientationConsistent response)
    (labels : Fin comparisonsPerUser → Alternative × Alternative) :
    theorem10UserUnorderedPairWins first second response labels =
      theorem10UserUnorderedPairCount first second labels *
        (if response first second then (1 : ℝ) else 0) := by
  unfold theorem10UserUnorderedPairWins theorem10UserUnorderedPairCount
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro position _
  generalize hlabel : labels position = label
  rcases label with ⟨left, right⟩
  dsimp
  by_cases hforward : left = first ∧ right = second
  · rcases hforward with ⟨hleft, hright⟩
    subst left
    subst right
    cases hresponse : response first second <;>
      simp [theorem10UnorderedPairIndicator, theorem12OneComparisonWins, hdistinct,
        Ne.symm hdistinct]
  · by_cases hreverse : left = second ∧ right = first
    · rcases hreverse with ⟨hleft, hright⟩
      subst left
      subst right
      have hreverseResponse := hconsistent first second
      cases hresponse : response first second <;>
        simp [theorem10UnorderedPairIndicator, theorem12OneComparisonWins, hdistinct,
          Ne.symm hdistinct, hreverseResponse, hresponse]
    · simp [theorem10UnorderedPairIndicator, hforward, hreverse]

/--
The response-dependent centered statistic is bounded by the corresponding
label count. This needs no within-user response independence.
-/
theorem theorem10UserCenteredPairWin_abs_le_count
    {Alternative : Type*} [DecidableEq Alternative] {comparisonsPerUser : ℕ}
    (first second : Alternative) (hdistinct : first ≠ second) (winProbability : ℝ)
    (hprob_nonneg : 0 ≤ winProbability) (hprob_le_one : winProbability ≤ 1)
    (response : theorem2UserResponseTable Alternative)
    (labels : Fin comparisonsPerUser → Alternative × Alternative) :
    |theorem10UserCenteredPairWin first second winProbability response labels| ≤
      theorem10UserUnorderedPairCount first second labels := by
  have hw_nonneg := theorem10UserUnorderedPairWins_nonneg first second response labels
  have hw_le := theorem10UserUnorderedPairWins_le_count first second hdistinct response labels
  have hcount_nonneg : 0 ≤ theorem10UserUnorderedPairCount first second labels := by
    unfold theorem10UserUnorderedPairCount
    exact Finset.sum_nonneg fun position _ =>
      theorem10_unorderedPairIndicator_nonneg first second (labels position)
  have hpcount_nonneg : 0 ≤ winProbability * theorem10UserUnorderedPairCount first second labels :=
    mul_nonneg hprob_nonneg hcount_nonneg
  have hpcount_le : winProbability * theorem10UserUnorderedPairCount first second labels ≤
      theorem10UserUnorderedPairCount first second labels := by
    nlinarith
  rw [abs_le]
  constructor <;> unfold theorem10UserCenteredPairWin <;> linarith

private theorem theorem10_unorderedPairIndicator_le_one
    {Alternative : Type*} [DecidableEq Alternative]
    (first second : Alternative) (label : Alternative × Alternative) :
    theorem10UnorderedPairIndicator first second label ≤ 1 := by
  rcases label with ⟨left, right⟩
  simp only [theorem10UnorderedPairIndicator]
  split <;> norm_num

/-- A fixed unordered-pair incidence count is at most the user's `d` displays. -/
theorem theorem10UserUnorderedPairCount_le_comparisons
    {Alternative : Type*} [DecidableEq Alternative] {comparisonsPerUser : ℕ}
    (first second : Alternative)
    (labels : Fin comparisonsPerUser → Alternative × Alternative) :
    theorem10UserUnorderedPairCount first second labels ≤ comparisonsPerUser := by
  unfold theorem10UserUnorderedPairCount
  calc
    (∑ position, theorem10UnorderedPairIndicator first second (labels position)) ≤
        ∑ _position : Fin comparisonsPerUser, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro position _
          exact theorem10_unorderedPairIndicator_le_one first second (labels position)
    _ = comparisonsPerUser := by simp

/-- The absolute centered pair statistic is bounded by the user's `d` displays. -/
theorem theorem10UserCenteredPairWin_abs_le_comparisons
    {Alternative : Type*} [DecidableEq Alternative] {comparisonsPerUser : ℕ}
    (first second : Alternative) (hdistinct : first ≠ second) (winProbability : ℝ)
    (hprob_nonneg : 0 ≤ winProbability) (hprob_le_one : winProbability ≤ 1)
    (response : theorem2UserResponseTable Alternative)
    (labels : Fin comparisonsPerUser → Alternative × Alternative) :
    |theorem10UserCenteredPairWin first second winProbability response labels| ≤
      comparisonsPerUser := by
  exact (theorem10UserCenteredPairWin_abs_le_count first second hdistinct winProbability
    hprob_nonneg hprob_le_one response labels).trans
      (theorem10UserUnorderedPairCount_le_comparisons first second labels)

/-- The centered pair statistic has square at most the incidence-count square. -/
theorem theorem10UserCenteredPairWin_sq_le_count_sq
    {Alternative : Type*} [DecidableEq Alternative] {comparisonsPerUser : ℕ}
    (first second : Alternative) (hdistinct : first ≠ second) (winProbability : ℝ)
    (hprob_nonneg : 0 ≤ winProbability) (hprob_le_one : winProbability ≤ 1)
    (response : theorem2UserResponseTable Alternative)
    (labels : Fin comparisonsPerUser → Alternative × Alternative) :
    (theorem10UserCenteredPairWin first second winProbability response labels) ^ 2 ≤
      (theorem10UserUnorderedPairCount first second labels) ^ 2 := by
  have habs := theorem10UserCenteredPairWin_abs_le_count first second hdistinct winProbability
    hprob_nonneg hprob_le_one response labels
  have hcount_nonneg : 0 ≤ theorem10UserUnorderedPairCount first second labels := by
    unfold theorem10UserUnorderedPairCount
    exact Finset.sum_nonneg fun position _ =>
      theorem10_unorderedPairIndicator_nonneg first second (labels position)
  rw [← sq_abs]
  have hproduct := mul_nonneg
    (sub_nonneg.mpr habs)
    (add_nonneg hcount_nonneg
      (abs_nonneg (theorem10UserCenteredPairWin first second winProbability response labels)))
  nlinarith

/--
The exact label-count second moment bounds the second moment of the
response-dependent centered statistic. Once its mean-zero calibration is
established, this is the variance proxy used in Appendix D's Bernstein step.
-/
theorem theorem10_pmfExp_userCenteredPairWin_sq_le
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (comparisonsPerUser : ℕ)
    (first second : Alternative) (hdistinct : first ≠ second) (winProbability : ℝ)
    (hprob_nonneg : 0 ≤ winProbability) (hprob_le_one : winProbability ≤ 1) :
    pmfExp
      (pmfProd responseLaw
        (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
          (theorem2UserPairLabelLaw sampling)))
      (fun source =>
        (theorem10UserCenteredPairWin first second winProbability source.1 source.2) ^ 2) ≤
      (comparisonsPerUser : ℝ) *
        (2 * (sampling first).toReal * (sampling second).toReal) +
      (comparisonsPerUser : ℝ) * ((comparisonsPerUser - 1 : ℕ) : ℝ) *
        (2 * (sampling first).toReal * (sampling second).toReal) ^ 2 := by
  calc
    pmfExp
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling)))
        (fun source =>
          (theorem10UserCenteredPairWin first second winProbability source.1 source.2) ^ 2) ≤
        pmfExp
          (pmfProd responseLaw
            (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
              (theorem2UserPairLabelLaw sampling)))
          (fun source => (theorem10UserUnorderedPairCount first second source.2) ^ 2) := by
            apply pmfExp_le_pmfExp_of_forall_le
            intro source
            exact theorem10UserCenteredPairWin_sq_le_count_sq first second hdistinct
              winProbability hprob_nonneg hprob_le_one source.1 source.2
    _ = pmfExp
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))
          (fun labels => (theorem10UserUnorderedPairCount first second labels) ^ 2) := by
            rw [pmfExp_pmfProd_eq_pairExp]
            change pmfPairExp responseLaw
              (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
                (theorem2UserPairLabelLaw sampling))
              (fun _ labels => (theorem10UserUnorderedPairCount first second labels) ^ 2) = _
            exact pmfPairExp_ignore_left responseLaw
              (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
                (theorem2UserPairLabelLaw sampling))
              (fun labels => (theorem10UserUnorderedPairCount first second labels) ^ 2)
    _ = _ := theorem10_pmfExp_userUnorderedPairCount_sq sampling comparisonsPerUser
      first second hdistinct

/-- The indicator of one specified ordered pair within the iid label law. -/
private def theorem10OrderedPairIndicator
    {Alternative : Type*} [DecidableEq Alternative]
    (first second : Alternative) : Alternative × Alternative → ℝ
  | (left, right) => if left = first ∧ right = second then 1 else 0

/-- The probability of one specified ordered pair is the product of its masses. -/
private theorem theorem10_pmfExp_orderedPairIndicator
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (first second : Alternative) :
    pmfExp (theorem2UserPairLabelLaw sampling)
      (theorem10OrderedPairIndicator first second) =
      (sampling first).toReal * (sampling second).toReal := by
  unfold theorem2UserPairLabelLaw
  rw [pmfExp_pmfProd_eq_pairExp]
  rw [show (fun left right => theorem10OrderedPairIndicator first second (left, right)) =
      fun left right =>
        (if left = first then (1 : ℝ) else 0) *
          if right = second then (1 : ℝ) else 0 by
        funext left right
        by_cases hleft : left = first <;> by_cases hright : right = second <;>
          simp [theorem10OrderedPairIndicator, hleft, hright]]
  rw [pmfPairExp_mul_separable]
  rw [theorem12_pmfExp_eq_indicator, theorem12_pmfExp_eq_indicator]

/--
One response-table/user-label coordinate has expected restricted win count
equal to the source pairwise win probability times its pair-display mass.
-/
private theorem theorem10_responsePairWin_coordinateExpectation
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {preference : PairwisePreference PUnit Alternative}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative)
    (first second : Alternative) (hdistinct : first ≠ second) :
    pmfPairExp responseLaw (theorem2UserPairLabelLaw sampling) (fun response label =>
      theorem10UnorderedPairIndicator first second label *
        theorem12OneComparisonWins first
          (label, response label.1 label.2)) =
      preference.prob PUnit.unit first second *
        (2 * (sampling first).toReal * (sampling second).toReal) := by
  have hdecompose :
      (fun response : theorem2UserResponseTable Alternative => fun label : Alternative × Alternative =>
        theorem10UnorderedPairIndicator first second label *
          theorem12OneComparisonWins first
            (label, response label.1 label.2)) =
        fun response : theorem2UserResponseTable Alternative => fun label : Alternative × Alternative =>
          (if response first second then (1 : ℝ) else 0) *
            theorem10OrderedPairIndicator first second label +
          (if response second first then (0 : ℝ) else 1) *
            theorem10OrderedPairIndicator second first label := by
    funext response label
    rcases label with ⟨left, right⟩
    by_cases hforward : left = first ∧ right = second
    · rcases hforward with ⟨hleft, hright⟩
      subst left
      subst right
      simp [theorem10UnorderedPairIndicator, theorem12OneComparisonWins,
        theorem10OrderedPairIndicator, hdistinct, Ne.symm hdistinct]
    · by_cases hreverse : left = second ∧ right = first
      · rcases hreverse with ⟨hleft, hright⟩
        subst left
        subst right
        cases hresponse : response second first <;>
          simp [theorem10UnorderedPairIndicator, theorem12OneComparisonWins,
            theorem10OrderedPairIndicator, hdistinct, Ne.symm hdistinct]
      · simp [theorem10UnorderedPairIndicator, theorem12OneComparisonWins,
          theorem10OrderedPairIndicator, hforward, hreverse]
  rw [hdecompose, pmfPairExp_add]
  rw [pmfPairExp_mul_separable, pmfPairExp_mul_separable]
  rw [hcalibrated first second, theorem10_pmfExp_orderedPairIndicator]
  rw [theorem2UserResponseCalibrated_false hcalibrated second first,
    theorem10_pmfExp_orderedPairIndicator]
  have hcomplement := preference.complementary PUnit.unit second first
  rw [show 1 - preference.prob PUnit.unit second first =
      preference.prob PUnit.unit first second by linarith]
  ring

/--
The literal one-user restricted win count has mean `d p q`, with
`q = 2 μ(first) μ(second)`. This retains arbitrary response-table dependence
within that user.
-/
theorem theorem10_pmfExp_userUnorderedPairWins
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
      (fun source => theorem10UserUnorderedPairWins first second source.1 source.2) =
      (comparisonsPerUser : ℝ) * preference.prob PUnit.unit first second *
        (2 * (sampling first).toReal * (sampling second).toReal) := by
  unfold theorem10UserUnorderedPairWins
  rw [pmfExp_univ_sum]
  calc
    (∑ position : Fin comparisonsPerUser,
        pmfExp
          (pmfProd responseLaw
            (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
              (theorem2UserPairLabelLaw sampling)))
          (fun source =>
            theorem10UnorderedPairIndicator first second (source.2 position) *
              theorem12OneComparisonWins first
                ((source.2 position), source.1 (source.2 position).1 (source.2 position).2))) =
      ∑ _position : Fin comparisonsPerUser,
        preference.prob PUnit.unit first second *
          (2 * (sampling first).toReal * (sampling second).toReal) := by
        apply Finset.sum_congr rfl
        intro position _
        rw [pmfExp_pmfProd_eq_pairExp]
        rw [AppliedModelingLib.pmfPairExp_swap]
        let coordinateExpectation : Alternative × Alternative → ℝ := fun label =>
          pmfExp responseLaw (fun response =>
            theorem10UnorderedPairIndicator first second label *
              theorem12OneComparisonWins first
                (label, response label.1 label.2))
        change pmfExp
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))
          (fun labels => coordinateExpectation (labels position)) = _
        rw [pmfExp_pmfProduct_eval]
        change pmfPairExp (theorem2UserPairLabelLaw sampling) responseLaw (fun label response =>
          theorem10UnorderedPairIndicator first second label *
            theorem12OneComparisonWins first
              (label, response label.1 label.2)) = _
        exact (AppliedModelingLib.pmfPairExp_swap responseLaw (theorem2UserPairLabelLaw sampling)
          (fun response label => theorem10UnorderedPairIndicator first second label *
            theorem12OneComparisonWins first
              (label, response label.1 label.2))).symm.trans
          (theorem10_responsePairWin_coordinateExpectation hcalibrated sampling first second hdistinct)
    _ = (comparisonsPerUser : ℝ) * preference.prob PUnit.unit first second *
        (2 * (sampling first).toReal * (sampling second).toReal) := by
        simp [nsmul_eq_mul]
        ring

/-- The literal source centered pair statistic has mean zero. -/
theorem theorem10_pmfExp_userCenteredPairWin_eq_zero
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
      (fun source => theorem10UserCenteredPairWin first second
        (preference.prob PUnit.unit first second) source.1 source.2) = 0 := by
  have hcount :
      pmfExp
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling)))
        (fun source => theorem10UserUnorderedPairCount first second source.2) =
        (comparisonsPerUser : ℝ) * 2 *
          (sampling first).toReal * (sampling second).toReal := by
    calc
      pmfExp
          (pmfProd responseLaw
            (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
              (theorem2UserPairLabelLaw sampling)))
          (fun source => theorem10UserUnorderedPairCount first second source.2) =
          pmfExp
            (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
              (theorem2UserPairLabelLaw sampling))
            (fun labels => theorem10UserUnorderedPairCount first second labels) := by
              rw [pmfExp_pmfProd_eq_pairExp]
              change pmfPairExp responseLaw
                (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
                  (theorem2UserPairLabelLaw sampling))
                (fun _ labels => theorem10UserUnorderedPairCount first second labels) = _
              exact pmfPairExp_ignore_left responseLaw
                (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
                  (theorem2UserPairLabelLaw sampling))
                (fun labels => theorem10UserUnorderedPairCount first second labels)
      _ = _ := theorem10_pmfExp_userUnorderedPairCount sampling comparisonsPerUser
        first second hdistinct
  unfold theorem10UserCenteredPairWin
  rw [pmfExp_sub, pmfExp_const_mul]
  rw [theorem10_pmfExp_userUnorderedPairWins hcalibrated sampling comparisonsPerUser
      first second hdistinct, hcount]
  ring

/-- The source centered statistic has the literal fixed-pair variance proxy required by Lemma 10. -/
theorem theorem10_pmfVariance_userCenteredPairWin_le
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {preference : PairwisePreference PUnit Alternative}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative) (comparisonsPerUser : ℕ)
    (first second : Alternative) (hdistinct : first ≠ second) :
    pmfVariance
      (pmfProd responseLaw
        (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
          (theorem2UserPairLabelLaw sampling)))
      (fun source => theorem10UserCenteredPairWin first second
        (preference.prob PUnit.unit first second) source.1 source.2) ≤
      (comparisonsPerUser : ℝ) *
        (2 * (sampling first).toReal * (sampling second).toReal) +
      (comparisonsPerUser : ℝ) * ((comparisonsPerUser - 1 : ℕ) : ℝ) *
        (2 * (sampling first).toReal * (sampling second).toReal) ^ 2 := by
  let sourceLaw := pmfProd responseLaw
    (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
      (theorem2UserPairLabelLaw sampling))
  let statistic : (theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative)) → ℝ := fun source =>
    theorem10UserCenteredPairWin first second
      (preference.prob PUnit.unit first second) source.1 source.2
  have hmean : pmfExp sourceLaw statistic = 0 := by
    exact theorem10_pmfExp_userCenteredPairWin_eq_zero hcalibrated sampling comparisonsPerUser
      first second hdistinct
  calc
    pmfVariance sourceLaw statistic = pmfExp sourceLaw (fun source => statistic source ^ 2) := by
      unfold pmfVariance
      apply pmfExp_congr
      intro source
      rw [hmean]
      ring
    _ ≤ (comparisonsPerUser : ℝ) *
          (2 * (sampling first).toReal * (sampling second).toReal) +
        (comparisonsPerUser : ℝ) * ((comparisonsPerUser - 1 : ℕ) : ℝ) *
          (2 * (sampling first).toReal * (sampling second).toReal) ^ 2 := by
          exact theorem10_pmfExp_userCenteredPairWin_sq_le responseLaw sampling comparisonsPerUser
            first second hdistinct (preference.prob PUnit.unit first second)
            (preference.nonneg PUnit.unit first second)
            (preference.le_one PUnit.unit first second)

private theorem theorem10_unorderedPairIndicator_zero_or_one
    {Alternative : Type*} [DecidableEq Alternative]
    (first second : Alternative) (label : Alternative × Alternative) :
    theorem10UnorderedPairIndicator first second label = 0 ∨
      theorem10UnorderedPairIndicator first second label = 1 := by
  rcases label with ⟨left, right⟩
  simp only [theorem10UnorderedPairIndicator]
  split <;> simp

private theorem theorem10_pmfExp_unorderedPairIndicator_complement
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (first second : Alternative) (hdistinct : first ≠ second) :
    pmfExp (theorem2UserPairLabelLaw sampling)
      (fun label => 1 - theorem10UnorderedPairIndicator first second label) =
      1 - 2 * (sampling first).toReal * (sampling second).toReal := by
  rw [pmfExp_sub, pmfExp_const,
    theorem10_pmfExp_unorderedPairIndicator sampling first second hdistinct]

/--
For the literal iid ordered-pair labels used in Appendix D, a fixed unordered
pair's total display count satisfies an exponential lower-tail bound. This is
the Chernoff denominator step before choosing the source's particular
threshold and simplifying its numerical constant.
-/
theorem theorem10_iidLabelCount_lowerTail_complement_exponential
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (first second : Alternative) (hdistinct : first ≠ second)
    (cutoff t : ℝ) (ht : 0 ≤ t) :
    pmfProb
      (pmfProduct (Fin users × Fin comparisonsPerUser) (Alternative × Alternative)
        (theorem2UserPairLabelLaw sampling))
      (fun labels =>
        (∑ index, theorem10UnorderedPairIndicator first second (labels index)) ≤ cutoff) ≤
      Real.exp
        (-t * ((users * comparisonsPerUser : ℕ) - cutoff) +
          (users * comparisonsPerUser : ℝ) *
            ((Real.exp t - 1) *
              (1 - 2 * (sampling first).toReal * (sampling second).toReal))) := by
  letI : MeasurableSpace Alternative := ⊤
  have htail := pmfProb_pmfProduct_indicatorSum_ge_le_exponential
    (ι := Fin users × Fin comparisonsPerUser)
    (μ := theorem2UserPairLabelLaw sampling)
    (indicator := fun label => 1 - theorem10UnorderedPairIndicator first second label)
    (meanBound := 1 - 2 * (sampling first).toReal * (sampling second).toReal)
    (cutoff := (users * comparisonsPerUser : ℕ) - cutoff)
    t
    (fun label => by
      rcases theorem10_unorderedPairIndicator_zero_or_one first second label with hzero | hone
      · right
        change 1 - theorem10UnorderedPairIndicator first second label = 1
        rw [hzero]
        norm_num
      · left
        change 1 - theorem10UnorderedPairIndicator first second label = 0
        rw [hone]
        norm_num)
    (by
      rw [theorem10_pmfExp_unorderedPairIndicator_complement sampling first second hdistinct]) ht
  calc
    pmfProb
        (pmfProduct (Fin users × Fin comparisonsPerUser) (Alternative × Alternative)
          (theorem2UserPairLabelLaw sampling))
        (fun labels =>
          (∑ index, theorem10UnorderedPairIndicator first second (labels index)) ≤ cutoff) =
      pmfProb
        (pmfProduct (Fin users × Fin comparisonsPerUser) (Alternative × Alternative)
          (theorem2UserPairLabelLaw sampling))
        (fun labels =>
          (users * comparisonsPerUser : ℕ) - cutoff ≤
            ∑ index, (1 - theorem10UnorderedPairIndicator first second (labels index))) := by
        apply pmfProb_congr
        intro labels
        have hsum :
            (∑ index, (1 - theorem10UnorderedPairIndicator first second (labels index))) =
              (users * comparisonsPerUser : ℝ) -
                ∑ index, theorem10UnorderedPairIndicator first second (labels index) := by
          rw [Finset.sum_sub_distrib]
          simp [nsmul_eq_mul]
        rw [hsum]
        constructor <;> intro h <;> norm_num [Nat.cast_mul] at * <;> linarith
    _ ≤ _ := by
      simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] using htail

/--
For the literal iid ordered-pair labels used in Appendix D, the direct
fixed-pair incidence indicators satisfy the lower-tail Chernoff bound needed
for the source's sparse-pair rate.
-/
theorem theorem10_iidLabelCount_lowerTail_exponential
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (first second : Alternative) (hdistinct : first ≠ second)
    (cutoff t : ℝ) (ht : 0 ≤ t) :
    pmfProb
      (pmfProduct (Fin users × Fin comparisonsPerUser) (Alternative × Alternative)
        (theorem2UserPairLabelLaw sampling))
      (fun labels =>
        (∑ index, theorem10UnorderedPairIndicator first second (labels index)) ≤ cutoff) ≤
      Real.exp
        (t * cutoff +
          (users * comparisonsPerUser : ℝ) *
            ((Real.exp (-t) - 1) *
              (2 * (sampling first).toReal * (sampling second).toReal))) := by
  letI : MeasurableSpace Alternative := ⊤
  have htail := pmfProb_pmfProduct_indicatorSum_le_le_exponential
    (ι := Fin users × Fin comparisonsPerUser)
    (μ := theorem2UserPairLabelLaw sampling)
    (indicator := theorem10UnorderedPairIndicator first second)
    (meanLower := 2 * (sampling first).toReal * (sampling second).toReal)
    cutoff t
    (theorem10_unorderedPairIndicator_zero_or_one first second)
    (by
      rw [theorem10_pmfExp_unorderedPairIndicator sampling first second hdistinct]) ht
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] using htail

private theorem theorem10_exp_neg_one_le_three_eighths :
    Real.exp (-(1 : ℝ)) ≤ (3 : ℝ) / 8 := by
  have hseries := Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) (by norm_num) 4
  have hexp : (8 : ℝ) / 3 ≤ Real.exp 1 := by
    convert hseries using 1 <;> norm_num
  have hinv : 1 / Real.exp 1 ≤ 1 / ((8 : ℝ) / 3) := by
    exact one_div_le_one_div_of_le (by norm_num) hexp
  simpa [Real.exp_neg, one_div] using hinv

/--
At the source threshold `ndq / 2`, the literal pair-incidence denominator
has the published `exp (-ndq / 8)` Chernoff failure bound.
-/
theorem theorem10_iidLabelCount_halfMean_lowerTail
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (first second : Alternative) (hdistinct : first ≠ second) :
    let q : ℝ := 2 * (sampling first).toReal * (sampling second).toReal
    pmfProb
      (pmfProduct (Fin users × Fin comparisonsPerUser) (Alternative × Alternative)
        (theorem2UserPairLabelLaw sampling))
      (fun labels =>
        (∑ index, theorem10UnorderedPairIndicator first second (labels index)) ≤
          ((users * comparisonsPerUser : ℕ) : ℝ) * q / 2) ≤
      Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * q / 8) := by
  dsimp
  let q : ℝ := 2 * (sampling first).toReal * (sampling second).toReal
  change
    pmfProb
      (pmfProduct (Fin users × Fin comparisonsPerUser) (Alternative × Alternative)
        (theorem2UserPairLabelLaw sampling))
      (fun labels =>
        (∑ index, theorem10UnorderedPairIndicator first second (labels index)) ≤
          ((users * comparisonsPerUser : ℕ) : ℝ) * q / 2) ≤
      Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * q / 8)
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    positivity
  have hcount_nonneg : 0 ≤ ((users * comparisonsPerUser : ℕ) : ℝ) := by positivity
  have hproduct_nonneg : 0 ≤ ((users * comparisonsPerUser : ℕ) : ℝ) * q :=
    mul_nonneg hcount_nonneg hq_nonneg
  have htail := theorem10_iidLabelCount_lowerTail_exponential
    sampling users comparisonsPerUser first second hdistinct
    (((users * comparisonsPerUser : ℕ) : ℝ) * q / 2) 1 (by norm_num)
  have hexp_factor : Real.exp (-(1 : ℝ)) - (1 : ℝ) / 2 ≤ -(1 : ℝ) / 8 := by
    linarith [theorem10_exp_neg_one_le_three_eighths]
  have hscaled := mul_le_mul_of_nonneg_left hexp_factor hproduct_nonneg
  calc
    pmfProb
        (pmfProduct (Fin users × Fin comparisonsPerUser) (Alternative × Alternative)
          (theorem2UserPairLabelLaw sampling))
        (fun labels =>
          (∑ index, theorem10UnorderedPairIndicator first second (labels index)) ≤
            ((users * comparisonsPerUser : ℕ) : ℝ) * q / 2) ≤
      Real.exp
        ((1 : ℝ) * (((users * comparisonsPerUser : ℕ) : ℝ) * q / 2) +
          (users * comparisonsPerUser : ℝ) *
            ((Real.exp (-((1 : ℝ)) ) - 1) * q)) := by
          simpa [q] using htail
    _ = Real.exp
        (((users * comparisonsPerUser : ℕ) : ℝ) * q *
          (Real.exp (-(1 : ℝ)) - (1 : ℝ) / 2)) := by
          congr 1
          norm_num [Nat.cast_mul]
          ring
    _ ≤ Real.exp
        (((users * comparisonsPerUser : ℕ) : ℝ) * q * (-(1 : ℝ) / 8)) := by
          exact Real.exp_le_exp.mpr hscaled
    _ = Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * q / 8) := by
          congr 1
          ring

/-- The total fixed-pair incidence count in an iid user batch. -/
def theorem10IidUserUnorderedPairCount
    {Alternative : Type*} [DecidableEq Alternative] {users comparisonsPerUser : ℕ}
    (first second : Alternative)
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) : ℝ :=
  ∑ user, theorem10UserUnorderedPairCount first second (sample user).2

/-- Grouping iid labels by user only rebrackets their fixed-pair incidence sum. -/
private theorem theorem10_iidUserUnorderedPairCount_eq_flattened
    {Alternative : Type*} [DecidableEq Alternative] {users comparisonsPerUser : ℕ}
    (first second : Alternative)
    (labels : Fin users → Fin comparisonsPerUser → Alternative × Alternative) :
    (∑ user, theorem10UserUnorderedPairCount first second (labels user)) =
      ∑ index : Fin users × Fin comparisonsPerUser,
        theorem10UnorderedPairIndicator first second (labels index.1 index.2) := by
  unfold theorem10UserUnorderedPairCount
  simpa using
    (Fintype.sum_prod_type'
      (fun user position =>
        theorem10UnorderedPairIndicator first second (labels user position))).symm

/-- The total fixed-pair win count in an iid user batch. -/
def theorem10IidUserUnorderedPairWins
    {Alternative : Type*} [DecidableEq Alternative] {users comparisonsPerUser : ℕ}
    (first second : Alternative)
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) : ℝ :=
  ∑ user, theorem10UserUnorderedPairWins first second (sample user).1 (sample user).2

/-- The aggregate centered fixed-pair statistic in an iid user batch. -/
def theorem10IidUserCenteredPairWin
    {Alternative : Type*} [DecidableEq Alternative] {users comparisonsPerUser : ℕ}
    (first second : Alternative) (winProbability : ℝ)
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) : ℝ :=
  ∑ user, theorem10UserCenteredPairWin first second winProbability
    (sample user).1 (sample user).2

/-- The source empirical win rate, with a total definition at zero incidence. -/
noncomputable def theorem10IidUserEmpiricalWinRate
    {Alternative : Type*} [DecidableEq Alternative] {users comparisonsPerUser : ℕ}
    (first second : Alternative)
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) : ℝ :=
  if theorem10IidUserUnorderedPairCount first second sample = 0 then 0
  else theorem10IidUserUnorderedPairWins first second sample /
    theorem10IidUserUnorderedPairCount first second sample

/-- Every fixed-pair display count is nonnegative. -/
theorem theorem10UserUnorderedPairCount_nonneg
    {Alternative : Type*} [DecidableEq Alternative] {comparisonsPerUser : ℕ}
    (first second : Alternative) (labels : Fin comparisonsPerUser → Alternative × Alternative) :
    0 ≤ theorem10UserUnorderedPairCount first second labels := by
  unfold theorem10UserUnorderedPairCount
  exact Finset.sum_nonneg fun position _ =>
    theorem10_unorderedPairIndicator_nonneg first second (labels position)

/-- Aggregate fixed-pair wins are nonnegative. -/
theorem theorem10IidUserUnorderedPairWins_nonneg
    {Alternative : Type*} [DecidableEq Alternative] {users comparisonsPerUser : ℕ}
    (first second : Alternative)
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) :
    0 ≤ theorem10IidUserUnorderedPairWins first second sample := by
  unfold theorem10IidUserUnorderedPairWins
  exact Finset.sum_nonneg fun user _ =>
    theorem10UserUnorderedPairWins_nonneg first second (sample user).1 (sample user).2

/-- Aggregate fixed-pair wins cannot exceed aggregate pair incidence. -/
theorem theorem10IidUserUnorderedPairWins_le_count
    {Alternative : Type*} [DecidableEq Alternative] {users comparisonsPerUser : ℕ}
    (first second : Alternative) (hdistinct : first ≠ second)
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) :
    theorem10IidUserUnorderedPairWins first second sample ≤
      theorem10IidUserUnorderedPairCount first second sample := by
  unfold theorem10IidUserUnorderedPairWins theorem10IidUserUnorderedPairCount
  apply Finset.sum_le_sum
  intro user _
  exact theorem10UserUnorderedPairWins_le_count first second hdistinct
    (sample user).1 (sample user).2

/-- The totalized off-diagonal empirical win rate is a genuine probability. -/
theorem theorem10IidUserEmpiricalWinRate_nonneg
    {Alternative : Type*} [DecidableEq Alternative] {users comparisonsPerUser : ℕ}
    (first second : Alternative)
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) :
    0 ≤ theorem10IidUserEmpiricalWinRate first second sample := by
  unfold theorem10IidUserEmpiricalWinRate
  split
  · norm_num
  · exact div_nonneg (theorem10IidUserUnorderedPairWins_nonneg first second sample)
      (Finset.sum_nonneg fun user _ =>
        theorem10UserUnorderedPairCount_nonneg first second (sample user).2)

/-- The totalized off-diagonal empirical win rate is at most one. -/
theorem theorem10IidUserEmpiricalWinRate_le_one
    {Alternative : Type*} [DecidableEq Alternative] {users comparisonsPerUser : ℕ}
    (first second : Alternative) (hdistinct : first ≠ second)
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) :
    theorem10IidUserEmpiricalWinRate first second sample ≤ 1 := by
  unfold theorem10IidUserEmpiricalWinRate
  split
  · norm_num
  · apply (div_le_one₀ (lt_of_le_of_ne
      (Finset.sum_nonneg fun user _ =>
        theorem10UserUnorderedPairCount_nonneg first second (sample user).2)
      (Ne.symm ‹theorem10IidUserUnorderedPairCount first second sample ≠ 0›))).mpr
    exact theorem10IidUserUnorderedPairWins_le_count first second hdistinct sample

/--
The paper's totalized empirical pairwise win rate.  On a diagonal pair the
same count occurs in both denominator slots, hence the source convention is
exactly one half; off the diagonal it is the literal normalized win count.
-/
noncomputable def theorem10IidUserPaperWinRate
    {Alternative : Type*} [DecidableEq Alternative] {users comparisonsPerUser : ℕ}
    (first second : Alternative)
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) : ℝ :=
  if first = second then (1 : ℝ) / 2
  else theorem10IidUserEmpiricalWinRate first second sample

/-- The paper's totalized empirical win rates lie in the unit interval. -/
theorem theorem10IidUserPaperWinRate_nonneg
    {Alternative : Type*} [DecidableEq Alternative] {users comparisonsPerUser : ℕ}
    (first second : Alternative)
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) :
    0 ≤ theorem10IidUserPaperWinRate first second sample := by
  unfold theorem10IidUserPaperWinRate
  split
  · norm_num
  · exact theorem10IidUserEmpiricalWinRate_nonneg first second sample

/-- The paper's totalized empirical win rates lie in the unit interval. -/
theorem theorem10IidUserPaperWinRate_le_one
    {Alternative : Type*} [DecidableEq Alternative] {users comparisonsPerUser : ℕ}
    (first second : Alternative)
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) :
    theorem10IidUserPaperWinRate first second sample ≤ 1 := by
  unfold theorem10IidUserPaperWinRate
  split
  · norm_num
  · exact theorem10IidUserEmpiricalWinRate_le_one first second
      (by simpa using ‹first ≠ second›) sample

/-- Diagonal empirical-pair error is exactly zero, as in the source Lemma 10. -/
theorem theorem10_iidUserPaperWinRate_diagonal
    {Alternative : Type*} [DecidableEq Alternative] {users comparisonsPerUser : ℕ}
    (preference : PairwisePreference PUnit Alternative) (alternative : Alternative)
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) :
    theorem10IidUserPaperWinRate alternative alternative sample =
      preference.prob PUnit.unit alternative alternative := by
  unfold theorem10IidUserPaperWinRate
  simp
  have hcomplementary := preference.complementary PUnit.unit alternative alternative
  linarith

/--
An all-pairs paper-rate failure is exactly an off-diagonal empirical-rate
failure.  This event identity is shared by the literal-tail and closed-form
confidence routes, so diagonal bookkeeping is proved once rather than copied
between audit endpoints.
-/
theorem theorem10_iidUserPaperWinRate_failure_iff_offDiag
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {users comparisonsPerUser : ℕ}
    (preference : PairwisePreference PUnit Alternative) (epsilon : ℝ)
    (hepsilon_nonneg : 0 ≤ epsilon)
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) :
    (∃ pair : Alternative × Alternative,
      epsilon < |theorem10IidUserPaperWinRate pair.1 pair.2 sample -
        preference.prob PUnit.unit pair.1 pair.2|) ↔
      ∃ pair ∈ (Finset.univ : Finset Alternative).offDiag,
        epsilon < |theorem10IidUserEmpiricalWinRate pair.1 pair.2 sample -
          preference.prob PUnit.unit pair.1 pair.2| := by
  constructor
  · rintro ⟨⟨first, second⟩, hbad⟩
    by_cases hdiagonal : first = second
    · subst second
      have hzero : theorem10IidUserPaperWinRate first first sample -
          preference.prob PUnit.unit first first = 0 := by
        rw [theorem10_iidUserPaperWinRate_diagonal preference first sample]
        ring
      rw [hzero] at hbad
      exact False.elim ((not_lt_of_ge hepsilon_nonneg) (by simpa using hbad))
    · refine ⟨(first, second), Finset.mem_offDiag.mpr
        ⟨Finset.mem_univ _, Finset.mem_univ _, hdiagonal⟩, ?_⟩
      simpa [theorem10IidUserPaperWinRate, hdiagonal] using hbad
  · rintro ⟨pair, hpair, hbad⟩
    refine ⟨pair, ?_⟩
    have hdistinct : pair.1 ≠ pair.2 := (Finset.mem_offDiag.mp hpair).2.2
    simpa [theorem10IidUserPaperWinRate, hdistinct] using hbad

/-- Aggregating centered user contributions is the centered aggregate count. -/
private theorem theorem10_iidUserCenteredPairWin_eq_wins_sub_mul_count
    {Alternative : Type*} [DecidableEq Alternative] {users comparisonsPerUser : ℕ}
    (first second : Alternative) (winProbability : ℝ)
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) :
    theorem10IidUserCenteredPairWin first second winProbability sample =
      theorem10IidUserUnorderedPairWins first second sample -
        winProbability * theorem10IidUserUnorderedPairCount first second sample := by
  unfold theorem10IidUserCenteredPairWin theorem10UserCenteredPairWin
    theorem10IidUserUnorderedPairWins theorem10IidUserUnorderedPairCount
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]

/--
On a positive denominator, a bound on the centered aggregate numerator gives
the corresponding deterministic empirical-win-rate bound.
-/
theorem theorem10_empiricalWinRate_error_le_of_centered_and_count_lower
    {Alternative : Type*} [DecidableEq Alternative] {users comparisonsPerUser : ℕ}
    (first second : Alternative) (winProbability cutoff denominator : ℝ)
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative)))
    (hcutoff_nonneg : 0 ≤ cutoff) (hdenominator_pos : 0 < denominator)
    (hcount_lower : denominator ≤ theorem10IidUserUnorderedPairCount first second sample)
    (hcentered : |theorem10IidUserCenteredPairWin first second winProbability sample| ≤ cutoff) :
    |theorem10IidUserEmpiricalWinRate first second sample - winProbability| ≤
      cutoff / denominator := by
  let count := theorem10IidUserUnorderedPairCount first second sample
  let wins := theorem10IidUserUnorderedPairWins first second sample
  let centered := theorem10IidUserCenteredPairWin first second winProbability sample
  have hcount_pos : 0 < count := lt_of_lt_of_le hdenominator_pos hcount_lower
  have hcount_ne : count ≠ 0 := ne_of_gt hcount_pos
  have hcentered_eq : centered = wins - winProbability * count := by
    exact theorem10_iidUserCenteredPairWin_eq_wins_sub_mul_count first second winProbability sample
  have hratio : wins / count - winProbability =
      (wins - winProbability * count) / count := by
    field_simp [hcount_ne]
  calc
    |theorem10IidUserEmpiricalWinRate first second sample - winProbability| =
        |wins / count - winProbability| := by
          simp only [theorem10IidUserEmpiricalWinRate, count, wins, hcount_ne, if_false]
    _ = |(wins - winProbability * count) / count| := by rw [hratio]
    _ = |centered / count| := by rw [hcentered_eq]
    _ = |centered| / count := by rw [abs_div, abs_of_pos hcount_pos]
    _ ≤ cutoff / count := by
          exact div_le_div_of_nonneg_right hcentered hcount_pos.le
    _ ≤ cutoff / denominator := by
          apply (div_le_div_iff₀ hcount_pos hdenominator_pos).2
          exact mul_le_mul_of_nonneg_left hcount_lower hcutoff_nonneg

/--
Probability-space composition for a normalized empirical rate: deterministic
ratio control turns a centered-numerator tail and a denominator tail into a
single deviation bound.
-/
private theorem theorem10_empiricalRate_tail_of_centeredTail_and_countTail
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (law : PMF Ω) (rate centered count : Ω → ℝ)
    (winProbability cutoff denominator numeratorTail denominatorTail : ℝ)
    (hdeterministic : ∀ outcome,
      |centered outcome| ≤ cutoff → denominator ≤ count outcome →
        |rate outcome - winProbability| ≤ cutoff / denominator)
    (hnumerator : pmfProb law (fun outcome => cutoff ≤ |centered outcome|) ≤ numeratorTail)
    (hdenominator : pmfProb law (fun outcome => count outcome ≤ denominator) ≤ denominatorTail) :
    pmfProb law (fun outcome => cutoff / denominator < |rate outcome - winProbability|) ≤
      numeratorTail + denominatorTail := by
  classical
  have himp : ∀ outcome,
      cutoff / denominator < |rate outcome - winProbability| →
        cutoff ≤ |centered outcome| ∨ count outcome ≤ denominator := by
    intro outcome hbad
    by_cases hcentered : cutoff ≤ |centered outcome|
    · exact Or.inl hcentered
    · by_cases hcount : count outcome ≤ denominator
      · exact Or.inr hcount
      · exfalso
        have hgood := hdeterministic outcome
          (le_of_lt (lt_of_not_ge hcentered)) (le_of_lt (lt_of_not_ge hcount))
        exact (not_lt_of_ge hgood) hbad
  calc
    pmfProb law (fun outcome => cutoff / denominator < |rate outcome - winProbability|) ≤
        pmfProb law (fun outcome => cutoff ≤ |centered outcome| ∨ count outcome ≤ denominator) :=
          pmfProb_le_of_imp law _ _ himp
    _ ≤ pmfProb law (fun outcome => cutoff ≤ |centered outcome|) +
          pmfProb law (fun outcome => count outcome ≤ denominator) :=
            pmfProb_or_le law _ _
    _ ≤ numeratorTail + denominatorTail := add_le_add hnumerator hdenominator

/--
The source's `ndq / 2` denominator event holds with its displayed Chernoff
bound on the *same iid user-batch probability space* as the numerator.  The
proof marginalizes latent response tables and then flattens the iid labels.
-/
theorem theorem10_iidUserPairCount_halfMean_lowerTail
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (first second : Alternative) (hdistinct : first ≠ second) :
    let q : ℝ := 2 * (sampling first).toReal * (sampling second).toReal
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample => theorem10IidUserUnorderedPairCount first second sample ≤
        ((users * comparisonsPerUser : ℕ) : ℝ) * q / 2) ≤
      Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * q / 8) := by
  classical
  dsimp
  let labelLaw := theorem2UserPairLabelLaw sampling
  let batchLabelLaw := pmfProduct (Fin comparisonsPerUser)
    (Alternative × Alternative) labelLaw
  let sourceLaw := pmfProd responseLaw batchLabelLaw
  let q : ℝ := 2 * (sampling first).toReal * (sampling second).toReal
  let flatEvent : (Fin users × Fin comparisonsPerUser → Alternative × Alternative) → Prop :=
    fun labels =>
      (∑ index, theorem10UnorderedPairIndicator first second (labels index)) ≤
        ((users * comparisonsPerUser : ℕ) : ℝ) * q / 2
  have hmarginal :
      pmfProb (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative)) sourceLaw)
        (fun sample => theorem10IidUserUnorderedPairCount first second sample ≤
          ((users * comparisonsPerUser : ℕ) : ℝ) * q / 2) =
      pmfProb (pmfProduct (Fin users)
        (Fin comparisonsPerUser → Alternative × Alternative) batchLabelLaw)
        (fun labels => (∑ user,
          theorem10UserUnorderedPairCount first second (labels user)) ≤
          ((users * comparisonsPerUser : ℕ) : ℝ) * q / 2) := by
    unfold pmfProb
    simpa [sourceLaw, batchLabelLaw] using
      (pmfExp_pmfProduct_pmfProd_snd responseLaw batchLabelLaw
        (fun labels => if (∑ user,
          theorem10UserUnorderedPairCount first second (labels user)) ≤
          ((users * comparisonsPerUser : ℕ) : ℝ) * q / 2 then (1 : ℝ) else 0))
  have hflatten :
      pmfProb (pmfProduct (Fin users)
        (Fin comparisonsPerUser → Alternative × Alternative) batchLabelLaw)
        (fun labels => (∑ user,
          theorem10UserUnorderedPairCount first second (labels user)) ≤
          ((users * comparisonsPerUser : ℕ) : ℝ) * q / 2) =
      pmfProb (pmfProduct (Fin users × Fin comparisonsPerUser)
        (Alternative × Alternative) labelLaw) flatEvent := by
    unfold pmfProb
    calc
      pmfExp (pmfProduct (Fin users)
          (Fin comparisonsPerUser → Alternative × Alternative) batchLabelLaw)
          (fun labels => if (∑ user,
            theorem10UserUnorderedPairCount first second (labels user)) ≤
            ((users * comparisonsPerUser : ℕ) : ℝ) * q / 2 then (1 : ℝ) else 0) =
        pmfExp (pmfProduct (Fin users)
          (Fin comparisonsPerUser → Alternative × Alternative) batchLabelLaw)
          (fun labels => if flatEvent (fun index => labels index.1 index.2)
            then (1 : ℝ) else 0) := by
            apply pmfExp_congr
            intro labels
            simp only [flatEvent]
            rw [theorem10_iidUserUnorderedPairCount_eq_flattened]
      _ = pmfExp (pmfProduct (Fin users × Fin comparisonsPerUser)
          (Alternative × Alternative) labelLaw)
          (fun labels => if flatEvent labels then (1 : ℝ) else 0) :=
            pmfExp_pmfProduct_pmfProduct_flatten labelLaw
              (fun labels => if flatEvent labels then (1 : ℝ) else 0)
  calc
    pmfProb
        (pmfProduct (Fin users)
          (theorem2UserResponseTable Alternative ×
            (Fin comparisonsPerUser → Alternative × Alternative)) sourceLaw)
        (fun sample => theorem10IidUserUnorderedPairCount first second sample ≤
          ((users * comparisonsPerUser : ℕ) : ℝ) * q / 2) =
      pmfProb (pmfProduct (Fin users × Fin comparisonsPerUser)
        (Alternative × Alternative) labelLaw) flatEvent := hmarginal.trans hflatten
    _ ≤ Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * q / 8) := by
      simpa [flatEvent, labelLaw, q] using
        (theorem10_iidLabelCount_halfMean_lowerTail sampling users comparisonsPerUser
          first second hdistinct)

/-- The probability that one ordered label displays a fixed unordered pair. -/
def theorem10FixedPairIncidenceProbability
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (first second : Alternative) : ℝ :=
  2 * (sampling first).toReal * (sampling second).toReal

/--
The source Lemma 10 variance proxy for one user's centered contribution to a
fixed distinct unordered pair.  Writing it once makes subsequent confidence
quantiles and minimum-mass algebra use exactly the same finite expression.
-/
def theorem10FixedPairVarianceProxy
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (comparisonsPerUser : ℕ)
    (first second : Alternative) : ℝ :=
  let q : ℝ := theorem10FixedPairIncidenceProbability sampling first second
  (comparisonsPerUser : ℝ) * q +
    (comparisonsPerUser : ℝ) * ((comparisonsPerUser - 1 : ℕ) : ℝ) * q ^ 2

/-- A conservative explicit Bernstein quantile for the fixed-pair numerator. -/
noncomputable def theorem10FixedPairBernsteinQuantile
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (first second : Alternative) (logLevel : ℝ) : ℝ :=
  Real.sqrt (8 * ((users : ℝ) *
    theorem10FixedPairVarianceProxy sampling comparisonsPerUser first second) * logLevel) +
    8 * (comparisonsPerUser : ℝ) * logLevel

/--
Explicit-constant realization of Lemma 10's minimum-mass big-O radius after
assigning a common failure budget to each off-diagonal pair.
-/
noncomputable def theorem10SourceRate
    (users comparisonsPerUser : ℕ) (minimumMass failureBudget : ℝ) : ℝ :=
  8 * Real.sqrt (Real.log (4 / failureBudget) /
    ((users : ℝ) * min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2))) +
    16 * Real.log (4 / failureBudget) / ((users : ℝ) * minimumMass ^ 2)

/--
Algebraic minimum-mass envelope for the source fixed-pair Bernstein quantile.
Here `r` will later be instantiated by `min {1, d μ_min²}`.  Separating this
from the probability proof keeps the source's rate simplification auditable.
-/
private theorem theorem10_quantile_div_halfMean_le_minMassEnvelope
    {users comparisons q mu r logLevel varianceProxy : ℝ}
    (husers_pos : 0 < users) (hcomparisons_pos : 0 < comparisons)
    (hq_pos : 0 < q) (hmu_pos : 0 < mu) (hr_pos : 0 < r)
    (hlogLevel_nonneg : 0 ≤ logLevel) (hvariance_nonneg : 0 ≤ varianceProxy)
    (hmu_sq_le_q : mu ^ 2 ≤ q) (hr_le_one : r ≤ 1) (hr_le_comparison_q : r ≤ comparisons * q)
    (hvariance_le : varianceProxy ≤ comparisons * q * (1 + comparisons * q)) :
    (Real.sqrt (8 * users * varianceProxy * logLevel) + 8 * comparisons * logLevel) /
        (users * comparisons * q / 2) ≤
      8 * Real.sqrt (logLevel / (users * r)) +
        16 * logLevel / (users * mu ^ 2) := by
  have hcomparison_q_pos : 0 < comparisons * q := mul_pos hcomparisons_pos hq_pos
  have hhalfMean_pos : 0 < users * comparisons * q / 2 := by positivity
  have hmu_sq_pos : 0 < mu ^ 2 := sq_pos_of_pos hmu_pos
  have husers_mu_sq_pos : 0 < users * mu ^ 2 := mul_pos husers_pos hmu_sq_pos
  have husers_r_pos : 0 < users * r := mul_pos husers_pos hr_pos
  have hroot_arg_nonneg : 0 ≤ 8 * users * varianceProxy * logLevel := by positivity
  have hsmall_root_arg_nonneg : 0 ≤ logLevel / (users * r) := by positivity
  have haux : r * (1 + comparisons * q) ≤ 2 * (comparisons * q) := by
    have hmul : r * (comparisons * q) ≤ comparisons * q :=
      by simpa using mul_le_mul_of_nonneg_right hr_le_one hcomparison_q_pos.le
    nlinarith
  have hvariance_mul : varianceProxy * r ≤ 2 * comparisons ^ 2 * q ^ 2 := by
    calc
      varianceProxy * r ≤ (comparisons * q * (1 + comparisons * q)) * r :=
        mul_le_mul_of_nonneg_right hvariance_le hr_pos.le
      _ = comparisons * q * (r * (1 + comparisons * q)) := by ring
      _ ≤ comparisons * q * (2 * (comparisons * q)) :=
        mul_le_mul_of_nonneg_left haux hcomparison_q_pos.le
      _ = 2 * comparisons ^ 2 * q ^ 2 := by ring
  rw [add_div]
  apply add_le_add
  · apply (div_le_iff₀ hhalfMean_pos).2
    apply (sq_le_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) hhalfMean_pos.le)).mp
    rw [Real.sq_sqrt hroot_arg_nonneg]
    have hright_sq :
        (8 * Real.sqrt (logLevel / (users * r)) * (users * comparisons * q / 2)) ^ 2 =
          16 * users * comparisons ^ 2 * q ^ 2 * logLevel / r := by
      calc
        (8 * Real.sqrt (logLevel / (users * r)) * (users * comparisons * q / 2)) ^ 2 =
            64 * (Real.sqrt (logLevel / (users * r))) ^ 2 *
              (users * comparisons * q / 2) ^ 2 := by ring
        _ = 64 * (logLevel / (users * r)) *
              (users * comparisons * q / 2) ^ 2 := by
            rw [Real.sq_sqrt hsmall_root_arg_nonneg]
        _ = 16 * users * comparisons ^ 2 * q ^ 2 * logLevel / r := by
            field_simp [husers_pos.ne', hcomparisons_pos.ne', hq_pos.ne', hr_pos.ne']
            ring
    rw [hright_sq]
    apply (le_div_iff₀ hr_pos).2
    have hscaled := mul_le_mul_of_nonneg_left hvariance_mul
      (show 0 ≤ 8 * users * logLevel by positivity)
    nlinarith
  · calc
      8 * comparisons * logLevel / (users * comparisons * q / 2) =
          16 * logLevel / (users * q) := by
            field_simp [husers_pos.ne', hcomparisons_pos.ne', hq_pos.ne']
            ring
      _ = 16 * (logLevel / (users * q)) := by ring
      _ ≤ 16 * (logLevel / (users * mu ^ 2)) := by
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left hlogLevel_nonneg husers_mu_sq_pos
            (mul_le_mul_of_nonneg_left hmu_sq_le_q husers_pos.le))
          (by norm_num)
      _ = 16 * logLevel / (users * mu ^ 2) := by ring

/--
The source minimum-mass simplification for a fixed-pair confidence radius,
with explicit universal constants.  `minimumMass` is a positive lower bound
on the two displayed alternatives' sampling masses; choosing the global
minimum sampling mass recovers the paper's stated dependence.
-/
theorem theorem10_fixedPairConfidenceRadius_le_minMassEnvelope
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (first second : Alternative) (minimumMass logLevel : ℝ)
    (husers_pos : 0 < users) (hcomparisons_pos : 0 < comparisonsPerUser)
    (hminimumMass_pos : 0 < minimumMass)
    (hminimumMass_first : minimumMass ≤ (sampling first).toReal)
    (hminimumMass_second : minimumMass ≤ (sampling second).toReal)
    (hlogLevel_nonneg : 0 ≤ logLevel) :
    theorem10FixedPairBernsteinQuantile sampling users comparisonsPerUser first second logLevel /
        ((((users * comparisonsPerUser : ℕ) : ℝ) *
          theorem10FixedPairIncidenceProbability sampling first second) / 2) ≤
      8 * Real.sqrt (logLevel /
        ((users : ℝ) * min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2))) +
        16 * logLevel / ((users : ℝ) * minimumMass ^ 2) := by
  let q : ℝ := theorem10FixedPairIncidenceProbability sampling first second
  let varianceProxy : ℝ :=
    theorem10FixedPairVarianceProxy sampling comparisonsPerUser first second
  let rateScale : ℝ := min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)
  have hfirst_nonneg : 0 ≤ (sampling first).toReal := ENNReal.toReal_nonneg
  have hsecond_nonneg : 0 ≤ (sampling second).toReal := ENNReal.toReal_nonneg
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
  have hrateScale_le_one : rateScale ≤ 1 := by
    exact min_le_left _ _
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
  simpa [q, varianceProxy, rateScale, theorem10FixedPairBernsteinQuantile,
    theorem10FixedPairVarianceProxy, theorem10FixedPairIncidenceProbability, Nat.cast_mul,
    mul_assoc] using
    (theorem10_quantile_div_halfMean_le_minMassEnvelope
      (users := (users : ℝ)) (comparisons := (comparisonsPerUser : ℝ)) (q := q)
      (mu := minimumMass) (r := rateScale) (logLevel := logLevel)
      (varianceProxy := varianceProxy) (by exact_mod_cast husers_pos)
      (by exact_mod_cast hcomparisons_pos) hq_pos hminimumMass_pos hrateScale_pos
      hlogLevel_nonneg hvariance_nonneg hminimumMass_sq_le_q hrateScale_le_one
      hrateScale_le_comparisons_q hvariance_le)

/--
The literal iid-user centered fixed-pair numerator satisfies a
variance-sensitive Bernstein-form upper tail. The variance proxy is exactly
the source `dq(1-q) + d²q²` upper bound written as `dq + d(d-1)q²`.
-/
theorem theorem10_iidUserCenteredPairWin_upperTail_bernstein
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {preference : PairwisePreference PUnit Alternative}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (first second : Alternative) (hdistinct : first ≠ second)
    (cutoff : ℝ) (hcutoff_nonneg : 0 ≤ cutoff)
    (hden_pos : 0 <
      (users : ℝ) *
        ((comparisonsPerUser : ℝ) *
          (2 * (sampling first).toReal * (sampling second).toReal) +
        (comparisonsPerUser : ℝ) * ((comparisonsPerUser - 1 : ℕ) : ℝ) *
          (2 * (sampling first).toReal * (sampling second).toReal) ^ 2) +
        (comparisonsPerUser : ℝ) * cutoff) :
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample => cutoff ≤ ∑ index,
        theorem10UserCenteredPairWin first second
          (preference.prob PUnit.unit first second) (sample index).1 (sample index).2) ≤
      Real.exp
        (-cutoff ^ 2 /
          (4 * ((users : ℝ) *
            ((comparisonsPerUser : ℝ) *
              (2 * (sampling first).toReal * (sampling second).toReal) +
            (comparisonsPerUser : ℝ) * ((comparisonsPerUser - 1 : ℕ) : ℝ) *
              (2 * (sampling first).toReal * (sampling second).toReal) ^ 2) +
            (comparisonsPerUser : ℝ) * cutoff))) := by
  let varianceProxy : ℝ :=
    (comparisonsPerUser : ℝ) *
      (2 * (sampling first).toReal * (sampling second).toReal) +
    (comparisonsPerUser : ℝ) * ((comparisonsPerUser - 1 : ℕ) : ℝ) *
      (2 * (sampling first).toReal * (sampling second).toReal) ^ 2
  let sourceLaw := pmfProd responseLaw
    (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
      (theorem2UserPairLabelLaw sampling))
  let statistic : (theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative)) → ℝ := fun source =>
    theorem10UserCenteredPairWin first second
      (preference.prob PUnit.unit first second) source.1 source.2
  letI : MeasurableSpace (theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative)) := ⊤
  have hvariance_nonneg : 0 ≤ varianceProxy := by
    dsimp [varianceProxy]
    positivity
  have hbound_nonneg : 0 ≤ (comparisonsPerUser : ℝ) := by positivity
  have hmean : pmfExp sourceLaw statistic = 0 := by
    exact theorem10_pmfExp_userCenteredPairWin_eq_zero hcalibrated sampling comparisonsPerUser
      first second hdistinct
  have hvariance : pmfExp sourceLaw (fun source => statistic source ^ 2) ≤ varianceProxy := by
    exact theorem10_pmfExp_userCenteredPairWin_sq_le responseLaw sampling comparisonsPerUser
      first second hdistinct (preference.prob PUnit.unit first second)
        (preference.nonneg PUnit.unit first second)
        (preference.le_one PUnit.unit first second)
  have hbound : ∀ source, |statistic source| ≤ (comparisonsPerUser : ℝ) := by
    intro source
    exact theorem10UserCenteredPairWin_abs_le_comparisons first second hdistinct
      (preference.prob PUnit.unit first second)
      (preference.nonneg PUnit.unit first second)
      (preference.le_one PUnit.unit first second) source.1 source.2
  have htail := pmfProb_pmfProduct_centeredBoundedSum_ge_le_bernstein
    (ι := Fin users)
    (α := theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative))
    sourceLaw statistic varianceProxy (comparisonsPerUser : ℝ) cutoff hmean hvariance hbound
    hvariance_nonneg hbound_nonneg hcutoff_nonneg
    (by simpa [varianceProxy, Fintype.card_fin] using hden_pos)
  simpa only [sourceLaw, statistic, Fintype.card_fin] using htail

/--
Two-sided form of the literal iid-user Bernstein step.  It is obtained from
the same calibrated, response-dependent user statistic; the factor two is
only the union over its two signs.
-/
theorem theorem10_iidUserCenteredPairWin_absTail_bernstein
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {preference : PairwisePreference PUnit Alternative}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (first second : Alternative) (hdistinct : first ≠ second)
    (cutoff : ℝ) (hcutoff_nonneg : 0 ≤ cutoff)
    (hden_pos : 0 <
      (users : ℝ) *
        ((comparisonsPerUser : ℝ) *
          (2 * (sampling first).toReal * (sampling second).toReal) +
        (comparisonsPerUser : ℝ) * ((comparisonsPerUser - 1 : ℕ) : ℝ) *
          (2 * (sampling first).toReal * (sampling second).toReal) ^ 2) +
        (comparisonsPerUser : ℝ) * cutoff) :
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample => cutoff ≤ |∑ index,
        theorem10UserCenteredPairWin first second
          (preference.prob PUnit.unit first second) (sample index).1 (sample index).2|) ≤
      2 * Real.exp
        (-cutoff ^ 2 /
          (4 * ((users : ℝ) *
            ((comparisonsPerUser : ℝ) *
              (2 * (sampling first).toReal * (sampling second).toReal) +
            (comparisonsPerUser : ℝ) * ((comparisonsPerUser - 1 : ℕ) : ℝ) *
              (2 * (sampling first).toReal * (sampling second).toReal) ^ 2) +
            (comparisonsPerUser : ℝ) * cutoff))) := by
  let varianceProxy : ℝ :=
    (comparisonsPerUser : ℝ) *
      (2 * (sampling first).toReal * (sampling second).toReal) +
    (comparisonsPerUser : ℝ) * ((comparisonsPerUser - 1 : ℕ) : ℝ) *
      (2 * (sampling first).toReal * (sampling second).toReal) ^ 2
  let sourceLaw := pmfProd responseLaw
    (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
      (theorem2UserPairLabelLaw sampling))
  let statistic : (theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative)) → ℝ := fun source =>
    theorem10UserCenteredPairWin first second
      (preference.prob PUnit.unit first second) source.1 source.2
  letI : MeasurableSpace (theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative)) := ⊤
  have hvariance_nonneg : 0 ≤ varianceProxy := by
    dsimp [varianceProxy]
    positivity
  have hbound_nonneg : 0 ≤ (comparisonsPerUser : ℝ) := by positivity
  have hmean : pmfExp sourceLaw statistic = 0 := by
    exact theorem10_pmfExp_userCenteredPairWin_eq_zero hcalibrated sampling comparisonsPerUser
      first second hdistinct
  have hvariance : pmfExp sourceLaw (fun source => statistic source ^ 2) ≤ varianceProxy := by
    exact theorem10_pmfExp_userCenteredPairWin_sq_le responseLaw sampling comparisonsPerUser
      first second hdistinct (preference.prob PUnit.unit first second)
        (preference.nonneg PUnit.unit first second)
        (preference.le_one PUnit.unit first second)
  have hbound : ∀ source, |statistic source| ≤ (comparisonsPerUser : ℝ) := by
    intro source
    exact theorem10UserCenteredPairWin_abs_le_comparisons first second hdistinct
      (preference.prob PUnit.unit first second)
      (preference.nonneg PUnit.unit first second)
      (preference.le_one PUnit.unit first second) source.1 source.2
  have htail := pmfProb_pmfProduct_centeredBoundedSum_abs_ge_le_bernstein
    (ι := Fin users)
    (α := theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative))
    sourceLaw statistic varianceProxy (comparisonsPerUser : ℝ) cutoff hmean hvariance hbound
    hvariance_nonneg hbound_nonneg hcutoff_nonneg
    (by simpa [varianceProxy, Fintype.card_fin] using hden_pos)
  simpa only [sourceLaw, statistic, Fintype.card_fin] using htail

/--
Confidence-level form of the literal fixed-pair numerator tail.  It instantiates
the reusable Bernstein quantile at the source variance proxy while retaining
the original iid-user probability space.
-/
theorem theorem10_iidUserCenteredPairWin_absTail_confidence
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {preference : PairwisePreference PUnit Alternative}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (first second : Alternative) (hdistinct : first ≠ second)
    (logLevel : ℝ) (hlogLevel_nonneg : 0 ≤ logLevel)
    (hden_pos : 0 < (users : ℝ) *
        theorem10FixedPairVarianceProxy sampling comparisonsPerUser first second +
      (comparisonsPerUser : ℝ) *
        (Real.sqrt (8 * ((users : ℝ) *
          theorem10FixedPairVarianceProxy sampling comparisonsPerUser first second) * logLevel) +
          8 * (comparisonsPerUser : ℝ) * logLevel)) :
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample =>
        Real.sqrt (8 * ((users : ℝ) *
          theorem10FixedPairVarianceProxy sampling comparisonsPerUser first second) * logLevel) +
            8 * (comparisonsPerUser : ℝ) * logLevel ≤
          |theorem10IidUserCenteredPairWin first second
            (preference.prob PUnit.unit first second) sample|) ≤
      2 * Real.exp (-logLevel) := by
  let varianceProxy : ℝ :=
    theorem10FixedPairVarianceProxy sampling comparisonsPerUser first second
  let cutoff : ℝ :=
    Real.sqrt (8 * ((users : ℝ) * varianceProxy) * logLevel) +
      8 * (comparisonsPerUser : ℝ) * logLevel
  have hvariance_nonneg : 0 ≤ varianceProxy := by
    dsimp [varianceProxy, theorem10FixedPairVarianceProxy,
      theorem10FixedPairIncidenceProbability]
    positivity
  have hbound_nonneg : 0 ≤ (comparisonsPerUser : ℝ) := by positivity
  have hcutoff_nonneg : 0 ≤ cutoff := by
    dsimp [cutoff]
    exact add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by positivity) hlogLevel_nonneg)
  have htail := theorem10_iidUserCenteredPairWin_absTail_bernstein
    hcalibrated sampling users comparisonsPerUser first second hdistinct cutoff hcutoff_nonneg
    (by simpa [varianceProxy, cutoff, theorem10FixedPairVarianceProxy] using hden_pos)
  have hquantile := bernstein_two_sided_exponential_at_quantile_le
    (totalVariance := (users : ℝ) * varianceProxy) (bound := (comparisonsPerUser : ℝ))
    (logLevel := logLevel) (by positivity) hbound_nonneg hlogLevel_nonneg
    (by simpa [varianceProxy, cutoff] using hden_pos)
  calc
    pmfProb
        (pmfProduct (Fin users)
          (theorem2UserResponseTable Alternative ×
            (Fin comparisonsPerUser → Alternative × Alternative))
          (pmfProd responseLaw
            (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
              (theorem2UserPairLabelLaw sampling))))
        (fun sample =>
          Real.sqrt (8 * ((users : ℝ) *
            theorem10FixedPairVarianceProxy sampling comparisonsPerUser first second) * logLevel) +
              8 * (comparisonsPerUser : ℝ) * logLevel ≤
            |theorem10IidUserCenteredPairWin first second
              (preference.prob PUnit.unit first second) sample|) =
        pmfProb
          (pmfProduct (Fin users)
            (theorem2UserResponseTable Alternative ×
              (Fin comparisonsPerUser → Alternative × Alternative))
            (pmfProd responseLaw
              (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
                (theorem2UserPairLabelLaw sampling))))
          (fun sample => cutoff ≤ |∑ index,
            theorem10UserCenteredPairWin first second
              (preference.prob PUnit.unit first second) (sample index).1 (sample index).2|) := by
          rfl
    _ ≤ 2 * Real.exp (-cutoff ^ 2 /
        (4 * ((users : ℝ) * varianceProxy + (comparisonsPerUser : ℝ) * cutoff))) := by
      simpa [varianceProxy, cutoff, theorem10FixedPairVarianceProxy] using htail
    _ ≤ 2 * Real.exp (-logLevel) := by
      simpa [varianceProxy, cutoff] using hquantile

/--
Explicit confidence-level fixed-pair empirical-rate bound.  It combines the
literal iid-user Bernstein numerator with the source `ndq / 2` Chernoff
incidence event.  The caller supplies the transparent denominator positivity
conditions rather than hiding them in asymptotic notation.
-/
theorem theorem10_iidUserEmpiricalWinRate_confidence
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {preference : PairwisePreference PUnit Alternative}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (first second : Alternative) (hdistinct : first ≠ second)
    (delta : ℝ) (hdelta_pos : 0 < delta) (hdelta_le_one : delta ≤ 1)
    (hdenominator_failure :
      2 * Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) *
        theorem10FixedPairIncidenceProbability sampling first second / 8) ≤ delta)
    (hbernstein_den_pos : 0 < (users : ℝ) *
        theorem10FixedPairVarianceProxy sampling comparisonsPerUser first second +
      (comparisonsPerUser : ℝ) *
        theorem10FixedPairBernsteinQuantile sampling users comparisonsPerUser first second
          (Real.log (4 / delta)))
    (hincidence_den_pos : 0 < ((users * comparisonsPerUser : ℕ) : ℝ) *
      theorem10FixedPairIncidenceProbability sampling first second / 2) :
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample =>
        theorem10FixedPairBernsteinQuantile sampling users comparisonsPerUser first second
            (Real.log (4 / delta)) /
          ((((users * comparisonsPerUser : ℕ) : ℝ) *
            theorem10FixedPairIncidenceProbability sampling first second) / 2) <
          |theorem10IidUserEmpiricalWinRate first second sample -
            preference.prob PUnit.unit first second|) ≤ delta := by
  let q : ℝ := theorem10FixedPairIncidenceProbability sampling first second
  let varianceProxy : ℝ :=
    theorem10FixedPairVarianceProxy sampling comparisonsPerUser first second
  let logLevel : ℝ := Real.log (4 / delta)
  let cutoff : ℝ := theorem10FixedPairBernsteinQuantile sampling users comparisonsPerUser
    first second logLevel
  let denominator : ℝ := ((users * comparisonsPerUser : ℕ) : ℝ) * q / 2
  have hratio_arg_lower : 1 ≤ 4 / delta := by
    apply (le_div_iff₀ hdelta_pos).2
    nlinarith
  have hlogLevel_nonneg : 0 ≤ logLevel := by
    dsimp [logLevel]
    exact Real.log_nonneg hratio_arg_lower
  have hcutoff_nonneg : 0 ≤ cutoff := by
    dsimp [cutoff, theorem10FixedPairBernsteinQuantile]
    exact add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by positivity) hlogLevel_nonneg)
  let sourceLaw := pmfProduct (Fin users)
    (theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative))
    (pmfProd responseLaw
      (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
        (theorem2UserPairLabelLaw sampling)))
  let rate : (Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) → ℝ :=
    theorem10IidUserEmpiricalWinRate first second
  let centered : (Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) → ℝ :=
    theorem10IidUserCenteredPairWin first second
      (preference.prob PUnit.unit first second)
  let count : (Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) → ℝ :=
    theorem10IidUserUnorderedPairCount first second
  have hnum : pmfProb sourceLaw (fun sample => cutoff ≤ |centered sample|) ≤
      2 * Real.exp (-logLevel) := by
    simpa [sourceLaw, centered, cutoff, varianceProxy, logLevel,
      theorem10FixedPairBernsteinQuantile] using
      (theorem10_iidUserCenteredPairWin_absTail_confidence hcalibrated sampling users
        comparisonsPerUser first second hdistinct logLevel hlogLevel_nonneg
        (by simpa [varianceProxy, cutoff, theorem10FixedPairBernsteinQuantile] using
          hbernstein_den_pos))
  have hcount : pmfProb sourceLaw (fun sample => count sample ≤ denominator) ≤
      Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * q / 8) := by
    simpa [sourceLaw, count, denominator, q, theorem10FixedPairIncidenceProbability] using
      (theorem10_iidUserPairCount_halfMean_lowerTail responseLaw sampling users
        comparisonsPerUser first second hdistinct)
  have hdeterministic : ∀ sample,
      |centered sample| ≤ cutoff → denominator ≤ count sample →
        |rate sample - preference.prob PUnit.unit first second| ≤ cutoff / denominator := by
    intro sample hcentered hcount_lower
    exact theorem10_empiricalWinRate_error_le_of_centered_and_count_lower
      first second (preference.prob PUnit.unit first second) cutoff denominator sample
      hcutoff_nonneg (by simpa [denominator, q] using hincidence_den_pos)
      (by simpa [count] using hcount_lower) (by simpa [centered] using hcentered)
  have hcombined := theorem10_empiricalRate_tail_of_centeredTail_and_countTail
    sourceLaw rate centered count (preference.prob PUnit.unit first second) cutoff denominator
    (2 * Real.exp (-logLevel))
    (Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * q / 8))
    hdeterministic hnum hcount
  have hlog_exp : 2 * Real.exp (-logLevel) = delta / 2 := by
    dsimp [logLevel]
    rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 4 / delta)]
    field_simp
    ring
  have hdenominator_half : Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * q / 8) ≤
      delta / 2 := by
    have hsource := hdenominator_failure
    dsimp [q] at hsource ⊢
    linarith
  calc
    pmfProb
        (pmfProduct (Fin users)
          (theorem2UserResponseTable Alternative ×
            (Fin comparisonsPerUser → Alternative × Alternative))
          (pmfProd responseLaw
            (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
              (theorem2UserPairLabelLaw sampling))))
        (fun sample =>
          theorem10FixedPairBernsteinQuantile sampling users comparisonsPerUser first second
              (Real.log (4 / delta)) /
            ((((users * comparisonsPerUser : ℕ) : ℝ) *
              theorem10FixedPairIncidenceProbability sampling first second) / 2) <
            |theorem10IidUserEmpiricalWinRate first second sample -
              preference.prob PUnit.unit first second|) =
      pmfProb sourceLaw (fun sample => cutoff / denominator <
        |rate sample - preference.prob PUnit.unit first second|) := by rfl
    _ ≤ 2 * Real.exp (-logLevel) +
          Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * q / 8) := hcombined
    _ = delta / 2 + Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * q / 8) := by
      rw [hlog_exp]
    _ ≤ delta / 2 + delta / 2 := by gcongr
    _ = delta := by ring

/--
Minimum-mass confidence form of the fixed-pair Lemma 10 conclusion.  The
probability estimate is the literal iid-user one; the preceding algebra only
enlarges its radius to a source-shaped, pair-mass-independent envelope.
-/
theorem theorem10_iidUserEmpiricalWinRate_minMass_confidence
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {preference : PairwisePreference PUnit Alternative}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (first second : Alternative) (hdistinct : first ≠ second)
    (minimumMass delta : ℝ)
    (husers_pos : 0 < users) (hcomparisons_pos : 0 < comparisonsPerUser)
    (hminimumMass_pos : 0 < minimumMass)
    (hminimumMass_first : minimumMass ≤ (sampling first).toReal)
    (hminimumMass_second : minimumMass ≤ (sampling second).toReal)
    (hdelta_pos : 0 < delta) (hdelta_le_one : delta ≤ 1)
    (hdenominator_failure :
      2 * Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) *
        theorem10FixedPairIncidenceProbability sampling first second / 8) ≤ delta)
    (hbernstein_den_pos : 0 < (users : ℝ) *
        theorem10FixedPairVarianceProxy sampling comparisonsPerUser first second +
      (comparisonsPerUser : ℝ) *
        theorem10FixedPairBernsteinQuantile sampling users comparisonsPerUser first second
          (Real.log (4 / delta)))
    (hincidence_den_pos : 0 < ((users * comparisonsPerUser : ℕ) : ℝ) *
      theorem10FixedPairIncidenceProbability sampling first second / 2) :
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample =>
        8 * Real.sqrt (Real.log (4 / delta) /
          ((users : ℝ) * min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2))) +
          16 * Real.log (4 / delta) / ((users : ℝ) * minimumMass ^ 2) <
          |theorem10IidUserEmpiricalWinRate first second sample -
            preference.prob PUnit.unit first second|) ≤ delta := by
  have hlogLevel_nonneg : 0 ≤ Real.log (4 / delta) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hdelta_pos).2
    nlinarith
  have hradius := theorem10_fixedPairConfidenceRadius_le_minMassEnvelope
    sampling users comparisonsPerUser first second minimumMass (Real.log (4 / delta))
    husers_pos hcomparisons_pos hminimumMass_pos hminimumMass_first hminimumMass_second
    hlogLevel_nonneg
  refine (pmfProb_le_of_imp _ _ _ ?_).trans
    (theorem10_iidUserEmpiricalWinRate_confidence hcalibrated sampling users
      comparisonsPerUser first second hdistinct delta hdelta_pos hdelta_le_one
      hdenominator_failure hbernstein_den_pos hincidence_den_pos)
  intro sample hbad
  exact lt_of_le_of_lt hradius hbad

/--
Uniform finite confidence statement obtained from the minimum-mass
fixed-pair envelope.  The caller chooses the common per-pair failure budget
and supplies its finite off-diagonal sum, making the all-pairs bookkeeping
explicit before any cardinality-to-big-O simplification.
-/
theorem theorem10_iidUserEmpiricalWinRate_uniformOffDiag_minMass_confidence
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {preference : PairwisePreference PUnit Alternative}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (minimumMass delta failureBudget : ℝ)
    (husers_pos : 0 < users) (hcomparisons_pos : 0 < comparisonsPerUser)
    (hminimumMass_pos : 0 < minimumMass)
    (hminimumMass : ∀ alternative, minimumMass ≤ (sampling alternative).toReal)
    (hfailureBudget_pos : 0 < failureBudget) (hfailureBudget_le_one : failureBudget ≤ 1)
    (hdenominator_failure : ∀ pair ∈ (Finset.univ : Finset Alternative).offDiag,
      2 * Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) *
        theorem10FixedPairIncidenceProbability sampling pair.1 pair.2 / 8) ≤ failureBudget)
    (hbudget_sum : ∑ pair ∈ (Finset.univ : Finset Alternative).offDiag,
      failureBudget ≤ delta) :
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample => ∃ pair ∈ (Finset.univ : Finset Alternative).offDiag,
        8 * Real.sqrt (Real.log (4 / failureBudget) /
          ((users : ℝ) * min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2))) +
          16 * Real.log (4 / failureBudget) / ((users : ℝ) * minimumMass ^ 2) <
          |theorem10IidUserEmpiricalWinRate pair.1 pair.2 sample -
            preference.prob PUnit.unit pair.1 pair.2|) ≤ delta := by
  classical
  let sourceLaw := pmfProduct (Fin users)
    (theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative))
    (pmfProd responseLaw
      (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
        (theorem2UserPairLabelLaw sampling)))
  have hlogLevel_nonneg : 0 ≤ Real.log (4 / failureBudget) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hfailureBudget_pos).2
    nlinarith
  have hquantile_nonneg : ∀ pair : Alternative × Alternative,
      0 ≤ theorem10FixedPairBernsteinQuantile sampling users comparisonsPerUser
        pair.1 pair.2 (Real.log (4 / failureBudget)) := by
    intro pair
    dsimp [theorem10FixedPairBernsteinQuantile]
    exact add_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by positivity) hlogLevel_nonneg)
  have hfixedPair : ∀ pair ∈ (Finset.univ : Finset Alternative).offDiag,
      pmfProb sourceLaw (fun sample =>
        8 * Real.sqrt (Real.log (4 / failureBudget) /
          ((users : ℝ) * min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2))) +
          16 * Real.log (4 / failureBudget) / ((users : ℝ) * minimumMass ^ 2) <
          |theorem10IidUserEmpiricalWinRate pair.1 pair.2 sample -
            preference.prob PUnit.unit pair.1 pair.2|) ≤ failureBudget := by
    intro pair hpair
    have hdistinct : pair.1 ≠ pair.2 := (Finset.mem_offDiag.mp hpair).2.2
    have hfirst_pos : 0 < (sampling pair.1).toReal :=
      lt_of_lt_of_le hminimumMass_pos (hminimumMass pair.1)
    have hsecond_pos : 0 < (sampling pair.2).toReal :=
      lt_of_lt_of_le hminimumMass_pos (hminimumMass pair.2)
    have hq_pos : 0 < theorem10FixedPairIncidenceProbability sampling pair.1 pair.2 := by
      dsimp [theorem10FixedPairIncidenceProbability]
      exact mul_pos (mul_pos (by norm_num) hfirst_pos) hsecond_pos
    have hvariance_pos : 0 <
        theorem10FixedPairVarianceProxy sampling comparisonsPerUser pair.1 pair.2 := by
      have hlead : 0 < (comparisonsPerUser : ℝ) *
          theorem10FixedPairIncidenceProbability sampling pair.1 pair.2 := by positivity
      have hrest : 0 ≤ (comparisonsPerUser : ℝ) *
          ((comparisonsPerUser - 1 : ℕ) : ℝ) *
          theorem10FixedPairIncidenceProbability sampling pair.1 pair.2 ^ 2 := by positivity
      dsimp [theorem10FixedPairVarianceProxy]
      linarith
    have hbernstein_den_pos : 0 < (users : ℝ) *
        theorem10FixedPairVarianceProxy sampling comparisonsPerUser pair.1 pair.2 +
      (comparisonsPerUser : ℝ) *
        theorem10FixedPairBernsteinQuantile sampling users comparisonsPerUser pair.1 pair.2
          (Real.log (4 / failureBudget)) := by
      apply add_pos_of_pos_of_nonneg
      · positivity
      · exact mul_nonneg (by positivity) (hquantile_nonneg pair)
    have hincidence_den_pos : 0 < ((users * comparisonsPerUser : ℕ) : ℝ) *
        theorem10FixedPairIncidenceProbability sampling pair.1 pair.2 / 2 := by
      rw [Nat.cast_mul]
      positivity
    simpa [sourceLaw] using
      (theorem10_iidUserEmpiricalWinRate_minMass_confidence hcalibrated sampling users
        comparisonsPerUser pair.1 pair.2 hdistinct minimumMass failureBudget husers_pos
        hcomparisons_pos hminimumMass_pos (hminimumMass pair.1) (hminimumMass pair.2)
        hfailureBudget_pos hfailureBudget_le_one (hdenominator_failure pair hpair)
        hbernstein_den_pos hincidence_den_pos)
  calc
    pmfProb sourceLaw (fun sample =>
        ∃ pair ∈ (Finset.univ : Finset Alternative).offDiag,
          8 * Real.sqrt (Real.log (4 / failureBudget) /
            ((users : ℝ) * min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2))) +
            16 * Real.log (4 / failureBudget) / ((users : ℝ) * minimumMass ^ 2) <
            |theorem10IidUserEmpiricalWinRate pair.1 pair.2 sample -
              preference.prob PUnit.unit pair.1 pair.2|) ≤
        ∑ pair ∈ (Finset.univ : Finset Alternative).offDiag,
          pmfProb sourceLaw (fun sample =>
            8 * Real.sqrt (Real.log (4 / failureBudget) /
              ((users : ℝ) * min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2))) +
              16 * Real.log (4 / failureBudget) / ((users : ℝ) * minimumMass ^ 2) <
              |theorem10IidUserEmpiricalWinRate pair.1 pair.2 sample -
                preference.prob PUnit.unit pair.1 pair.2|) :=
      pmfProb_exists_mem_le_sum sourceLaw
        ((Finset.univ : Finset Alternative).offDiag)
        (fun pair sample =>
          8 * Real.sqrt (Real.log (4 / failureBudget) /
            ((users : ℝ) * min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2))) +
            16 * Real.log (4 / failureBudget) / ((users : ℝ) * minimumMass ^ 2) <
            |theorem10IidUserEmpiricalWinRate pair.1 pair.2 sample -
              preference.prob PUnit.unit pair.1 pair.2|)
    _ ≤ ∑ pair ∈ (Finset.univ : Finset Alternative).offDiag, failureBudget := by
      apply Finset.sum_le_sum
      intro pair hpair
      exact hfixedPair pair hpair
    _ ≤ delta := hbudget_sum

/--
All-pairs source form of the closed-form minimum-mass confidence theorem.
The displayed radius is the explicit-constant realization of Lemma 10's
big-O rate; diagonal pairs contribute zero error by the paper convention.
-/
theorem theorem10_iidUserPaperWinRate_uniform_minMass_confidence
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {preference : PairwisePreference PUnit Alternative}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (minimumMass delta failureBudget : ℝ)
    (husers_pos : 0 < users) (hcomparisons_pos : 0 < comparisonsPerUser)
    (hminimumMass_pos : 0 < minimumMass)
    (hminimumMass : ∀ alternative, minimumMass ≤ (sampling alternative).toReal)
    (hfailureBudget_pos : 0 < failureBudget) (hfailureBudget_le_one : failureBudget ≤ 1)
    (hdenominator_failure : ∀ pair ∈ (Finset.univ : Finset Alternative).offDiag,
      2 * Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) *
        theorem10FixedPairIncidenceProbability sampling pair.1 pair.2 / 8) ≤ failureBudget)
    (hbudget_sum : ∑ pair ∈ (Finset.univ : Finset Alternative).offDiag,
      failureBudget ≤ delta) :
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample => ∃ pair : Alternative × Alternative,
        8 * Real.sqrt (Real.log (4 / failureBudget) /
          ((users : ℝ) * min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2))) +
          16 * Real.log (4 / failureBudget) / ((users : ℝ) * minimumMass ^ 2) <
          |theorem10IidUserPaperWinRate pair.1 pair.2 sample -
            preference.prob PUnit.unit pair.1 pair.2|) ≤ delta := by
  let sourceLaw := pmfProduct (Fin users)
    (theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative))
    (pmfProd responseLaw
      (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
        (theorem2UserPairLabelLaw sampling)))
  let error :=
    8 * Real.sqrt (Real.log (4 / failureBudget) /
      ((users : ℝ) * min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2))) +
      16 * Real.log (4 / failureBudget) / ((users : ℝ) * minimumMass ^ 2)
  have herror_nonneg : 0 ≤ error := by
    dsimp [error]
    have hlog_nonneg : 0 ≤ Real.log (4 / failureBudget) := by
      apply Real.log_nonneg
      exact (le_div_iff₀ hfailureBudget_pos).2 (by nlinarith)
    exact add_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (div_nonneg (mul_nonneg (by norm_num) hlog_nonneg) (by positivity))
  have hevent : ∀ sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative)),
      (∃ pair : Alternative × Alternative,
        error < |theorem10IidUserPaperWinRate pair.1 pair.2 sample -
          preference.prob PUnit.unit pair.1 pair.2|) ↔
      ∃ pair ∈ (Finset.univ : Finset Alternative).offDiag,
        error < |theorem10IidUserEmpiricalWinRate pair.1 pair.2 sample -
          preference.prob PUnit.unit pair.1 pair.2| :=
    theorem10_iidUserPaperWinRate_failure_iff_offDiag
      (users := users) (comparisonsPerUser := comparisonsPerUser)
      preference error herror_nonneg
  change pmfProb sourceLaw (fun sample => ∃ pair : Alternative × Alternative,
      error < |theorem10IidUserPaperWinRate pair.1 pair.2 sample -
        preference.prob PUnit.unit pair.1 pair.2|) ≤ delta
  calc
    pmfProb sourceLaw (fun sample => ∃ pair : Alternative × Alternative,
        error < |theorem10IidUserPaperWinRate pair.1 pair.2 sample -
          preference.prob PUnit.unit pair.1 pair.2|) =
      pmfProb sourceLaw (fun sample =>
        ∃ pair ∈ (Finset.univ : Finset Alternative).offDiag,
          error < |theorem10IidUserEmpiricalWinRate pair.1 pair.2 sample -
            preference.prob PUnit.unit pair.1 pair.2|) := by
      apply pmfProb_congr
      exact hevent
    _ ≤ delta := by
      simpa [sourceLaw, error] using
        theorem10_iidUserEmpiricalWinRate_uniformOffDiag_minMass_confidence
          hcalibrated sampling users comparisonsPerUser minimumMass delta failureBudget
          husers_pos hcomparisons_pos hminimumMass_pos hminimumMass
          hfailureBudget_pos hfailureBudget_le_one hdenominator_failure hbudget_sum

/--
Source-shaped explicit-constant realization of Lemma 10.  The paper states one
global confidence level `delta`; the per-pair allocation used by the union
bound is therefore fixed internally rather than exposed as an additional
premise of the paper-facing theorem.
-/
theorem theorem10_iidUserPaperWinRate_uniform_source_confidence
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    [Nonempty Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {preference : PairwisePreference PUnit Alternative}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (minimumMass delta : ℝ)
    (husers_pos : 0 < users) (hcomparisons_pos : 0 < comparisonsPerUser)
    (hminimumMass_pos : 0 < minimumMass)
    (hminimumMass : ∀ alternative, minimumMass ≤ (sampling alternative).toReal)
    (hdelta_pos : 0 < delta) (hdelta_le_one : delta ≤ 1)
    (hsource_failure :
      (Fintype.card Alternative : ℝ) ^ 2 *
          Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * minimumMass ^ 2 / 8) ≤
        delta) :
    let failureBudget := delta / (Fintype.card Alternative : ℝ) ^ 2
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample => ∃ pair : Alternative × Alternative,
        theorem10SourceRate users comparisonsPerUser minimumMass failureBudget <
          |theorem10IidUserPaperWinRate pair.1 pair.2 sample -
            preference.prob PUnit.unit pair.1 pair.2|) ≤ delta := by
  classical
  let alternativeCount : ℝ := Fintype.card Alternative
  let failureBudget : ℝ := delta / alternativeCount ^ 2
  have hcard_pos_nat : 0 < Fintype.card Alternative := Fintype.card_pos
  have hcard_pos : 0 < alternativeCount := by
    dsimp [alternativeCount]
    exact_mod_cast hcard_pos_nat
  have hcard_one : 1 ≤ alternativeCount := by
    dsimp [alternativeCount]
    exact_mod_cast hcard_pos_nat
  have hfailureBudget_pos : 0 < failureBudget :=
    div_pos hdelta_pos (sq_pos_of_pos hcard_pos)
  have hfailureBudget_le_one : failureBudget ≤ 1 := by
    have hcard_sq_one : 1 ≤ alternativeCount ^ 2 := by nlinarith
    calc
      failureBudget ≤ delta := by
        dsimp [failureBudget]
        exact (div_le_iff₀ (sq_pos_of_pos hcard_pos)).2 (by nlinarith)
      _ ≤ 1 := hdelta_le_one
  have hdenominator_failure :
      ∀ pair ∈ (Finset.univ : Finset Alternative).offDiag,
        2 * Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) *
          theorem10FixedPairIncidenceProbability sampling pair.1 pair.2 / 8) ≤
            failureBudget := by
    intro pair hpair
    have hdistinct : pair.1 ≠ pair.2 := by
      simpa [Finset.mem_offDiag] using hpair
    have hcard_two_nat : 2 ≤ Fintype.card Alternative := by
      have hsubset : ({pair.1, pair.2} : Finset Alternative) ⊆ Finset.univ := by simp
      have hcard_pair := Finset.card_le_card hsubset
      simpa [Finset.card_pair, hdistinct] using hcard_pair
    have hcard_two : (2 : ℝ) ≤ alternativeCount := by
      dsimp [alternativeCount]
      exact_mod_cast hcard_two_nat
    have hfirst_nonneg : 0 ≤ (sampling pair.1).toReal := ENNReal.toReal_nonneg
    have hsecond_nonneg : 0 ≤ (sampling pair.2).toReal := ENNReal.toReal_nonneg
    have hmass_product :
        minimumMass ^ 2 ≤ (sampling pair.1).toReal * (sampling pair.2).toReal := by
      have := mul_le_mul (hminimumMass pair.1) (hminimumMass pair.2)
        (le_of_lt hminimumMass_pos) hfirst_nonneg
      simpa [pow_two] using this
    have hincidence :
        2 * minimumMass ^ 2 ≤
          theorem10FixedPairIncidenceProbability sampling pair.1 pair.2 := by
      dsimp [theorem10FixedPairIncidenceProbability]
      nlinarith
    let sampleScale : ℝ := ((users * comparisonsPerUser : ℕ) : ℝ)
    let exponentUnit : ℝ := sampleScale * minimumMass ^ 2 / 8
    have hsampleScale_nonneg : 0 ≤ sampleScale := by
      dsimp [sampleScale]
      positivity
    have hexponent_order :
        -(sampleScale * theorem10FixedPairIncidenceProbability sampling pair.1 pair.2 / 8) ≤
          -(2 * exponentUnit) := by
      dsimp [exponentUnit]
      nlinarith
    have hexp_pair :
        Real.exp (-(sampleScale *
            theorem10FixedPairIncidenceProbability sampling pair.1 pair.2 / 8)) ≤
          Real.exp (-exponentUnit) ^ 2 := by
      calc
        Real.exp (-(sampleScale *
            theorem10FixedPairIncidenceProbability sampling pair.1 pair.2 / 8)) ≤
            Real.exp (-(2 * exponentUnit)) := Real.exp_le_exp.mpr hexponent_order
        _ = Real.exp (-exponentUnit) ^ 2 := by
          rw [show -(2 * exponentUnit) = -exponentUnit + -exponentUnit by ring,
            Real.exp_add, pow_two]
    have hsource_unit :
        alternativeCount ^ 2 * Real.exp (-exponentUnit) ≤ delta := by
      convert hsource_failure using 1 <;>
        simp only [alternativeCount, exponentUnit, sampleScale, Nat.cast_mul] <;> ring
    have hexp_unit_le_quarter : Real.exp (-exponentUnit) ≤ (1 : ℝ) / 4 := by
      have hcombined :
          alternativeCount ^ 2 * Real.exp (-exponentUnit) ≤ 1 :=
        hsource_unit.trans hdelta_le_one
      have hexp_pos := Real.exp_pos (-exponentUnit)
      have hfour_le_sq : (4 : ℝ) ≤ alternativeCount ^ 2 := by nlinarith
      have hfour_exp_le : 4 * Real.exp (-exponentUnit) ≤ 1 := by
        calc
          4 * Real.exp (-exponentUnit) ≤
              alternativeCount ^ 2 * Real.exp (-exponentUnit) :=
            mul_le_mul_of_nonneg_right hfour_le_sq (le_of_lt hexp_pos)
          _ ≤ 1 := hcombined
      nlinarith
    have hpair_to_unit :
        2 * Real.exp (-(sampleScale *
            theorem10FixedPairIncidenceProbability sampling pair.1 pair.2 / 8)) ≤
          Real.exp (-exponentUnit) := by
      have hexp_pos := Real.exp_pos (-exponentUnit)
      nlinarith
    have hunit_to_budget : Real.exp (-exponentUnit) ≤ failureBudget := by
      dsimp [failureBudget]
      exact (le_div_iff₀ (sq_pos_of_pos hcard_pos)).2 (by
        simpa [mul_comm] using hsource_unit)
    convert hpair_to_unit.trans hunit_to_budget using 1 <;>
      simp only [sampleScale, Nat.cast_mul] <;> ring
  have hbudget_sum :
      ∑ pair ∈ (Finset.univ : Finset Alternative).offDiag, failureBudget ≤ delta := by
    have hcard_offDiag :
        (((Finset.univ : Finset Alternative).offDiag).card : ℝ) ≤ alternativeCount ^ 2 := by
      have hcard_offDiag_nat :
          ((Finset.univ : Finset Alternative).offDiag).card ≤
            (Fintype.card Alternative) ^ 2 := by
        simpa [Finset.offDiag_card, pow_two] using
          (Nat.sub_le (Fintype.card Alternative * Fintype.card Alternative)
            (Fintype.card Alternative))
      dsimp [alternativeCount]
      exact_mod_cast hcard_offDiag_nat
    calc
      ∑ pair ∈ (Finset.univ : Finset Alternative).offDiag, failureBudget =
          (((Finset.univ : Finset Alternative).offDiag).card : ℝ) * failureBudget := by
            simp
      _ ≤ alternativeCount ^ 2 * failureBudget :=
        mul_le_mul_of_nonneg_right hcard_offDiag (le_of_lt hfailureBudget_pos)
      _ = delta := by
        dsimp [failureBudget]
        field_simp [ne_of_gt hcard_pos]
  simpa [alternativeCount, failureBudget] using
    theorem10_iidUserPaperWinRate_uniform_minMass_confidence
      hcalibrated sampling users comparisonsPerUser minimumMass delta failureBudget
      husers_pos hcomparisons_pos hminimumMass_pos hminimumMass
      hfailureBudget_pos hfailureBudget_le_one hdenominator_failure hbudget_sum

/--
Finite fixed-pair empirical-win-rate deviation bound from Appendix D, Lemma
10.  The two component events are evaluated under one literal iid-user source
law; in particular, the denominator is not borrowed from a separate flattened
label experiment.
-/
theorem theorem10_iidUserEmpiricalWinRate_tail_bound
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {preference : PairwisePreference PUnit Alternative}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (first second : Alternative) (hdistinct : first ≠ second)
    (cutoff : ℝ) (hcutoff_nonneg : 0 ≤ cutoff)
    (hbernstein_den_pos : 0 <
      (users : ℝ) *
        ((comparisonsPerUser : ℝ) *
          (2 * (sampling first).toReal * (sampling second).toReal) +
        (comparisonsPerUser : ℝ) * ((comparisonsPerUser - 1 : ℕ) : ℝ) *
          (2 * (sampling first).toReal * (sampling second).toReal) ^ 2) +
        (comparisonsPerUser : ℝ) * cutoff)
    (hincidence_den_pos : 0 < ((users * comparisonsPerUser : ℕ) : ℝ) *
      (2 * (sampling first).toReal * (sampling second).toReal) / 2) :
    let q : ℝ := 2 * (sampling first).toReal * (sampling second).toReal
    let varianceProxy : ℝ :=
      (comparisonsPerUser : ℝ) * q +
      (comparisonsPerUser : ℝ) * ((comparisonsPerUser - 1 : ℕ) : ℝ) * q ^ 2
    let denominator : ℝ := ((users * comparisonsPerUser : ℕ) : ℝ) * q / 2
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample => cutoff / denominator <
        |theorem10IidUserEmpiricalWinRate first second sample -
          preference.prob PUnit.unit first second|) ≤
      2 * Real.exp (-cutoff ^ 2 /
        (4 * ((users : ℝ) * varianceProxy + (comparisonsPerUser : ℝ) * cutoff))) +
        Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * q / 8) := by
  dsimp
  let q : ℝ := 2 * (sampling first).toReal * (sampling second).toReal
  let varianceProxy : ℝ :=
    (comparisonsPerUser : ℝ) * q +
    (comparisonsPerUser : ℝ) * ((comparisonsPerUser - 1 : ℕ) : ℝ) * q ^ 2
  let denominator : ℝ := ((users * comparisonsPerUser : ℕ) : ℝ) * q / 2
  let sourceLaw := pmfProduct (Fin users)
    (theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative))
    (pmfProd responseLaw
      (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
        (theorem2UserPairLabelLaw sampling)))
  let rate : (Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) → ℝ :=
    theorem10IidUserEmpiricalWinRate first second
  let centered : (Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) → ℝ :=
    theorem10IidUserCenteredPairWin first second
      (preference.prob PUnit.unit first second)
  let count : (Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) → ℝ :=
    theorem10IidUserUnorderedPairCount first second
  have hnum : pmfProb sourceLaw (fun sample => cutoff ≤ |centered sample|) ≤
      2 * Real.exp (-cutoff ^ 2 /
        (4 * ((users : ℝ) * varianceProxy + (comparisonsPerUser : ℝ) * cutoff))) := by
    simpa [sourceLaw, centered, varianceProxy, q] using
      (theorem10_iidUserCenteredPairWin_absTail_bernstein hcalibrated sampling users
        comparisonsPerUser first second hdistinct cutoff hcutoff_nonneg hbernstein_den_pos)
  have hcount : pmfProb sourceLaw (fun sample => count sample ≤ denominator) ≤
      Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * q / 8) := by
    simpa [sourceLaw, count, denominator, q] using
      (theorem10_iidUserPairCount_halfMean_lowerTail responseLaw sampling users
        comparisonsPerUser first second hdistinct)
  have hdeterministic : ∀ sample,
      |centered sample| ≤ cutoff → denominator ≤ count sample →
        |rate sample - preference.prob PUnit.unit first second| ≤ cutoff / denominator := by
    intro sample hcentered hcount_lower
    exact theorem10_empiricalWinRate_error_le_of_centered_and_count_lower
      first second (preference.prob PUnit.unit first second) cutoff denominator sample
      hcutoff_nonneg (by simpa [denominator, q] using hincidence_den_pos)
      (by simpa [count] using hcount_lower) (by simpa [centered] using hcentered)
  simpa [sourceLaw, rate, centered, count, denominator, varianceProxy, q] using
    (theorem10_empiricalRate_tail_of_centeredTail_and_countTail sourceLaw rate centered count
      (preference.prob PUnit.unit first second) cutoff denominator
      (2 * Real.exp (-cutoff ^ 2 /
        (4 * ((users : ℝ) * varianceProxy + (comparisonsPerUser : ℝ) * cutoff))))
      (Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * q / 8))
      hdeterministic hnum hcount)

/--
The explicit fixed-pair failure bound obtained by applying the count-ratio
theorem at an empirical-rate tolerance `epsilon`.
-/
noncomputable def theorem10FixedPairRateTailBound
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (first second : Alternative) (epsilon : ℝ) : ℝ :=
  let q : ℝ := 2 * (sampling first).toReal * (sampling second).toReal
  let varianceProxy : ℝ :=
    (comparisonsPerUser : ℝ) * q +
    (comparisonsPerUser : ℝ) * ((comparisonsPerUser - 1 : ℕ) : ℝ) * q ^ 2
  let denominator : ℝ := ((users * comparisonsPerUser : ℕ) : ℝ) * q / 2
  2 * Real.exp (-(epsilon * denominator) ^ 2 /
    (4 * ((users : ℝ) * varianceProxy +
      (comparisonsPerUser : ℝ) * (epsilon * denominator)))) +
    Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * q / 8)

/--
Exact all-distinct-pairs union bound for Lemma 10.  This precedes the source's
minimum-mass simplification: it retains the pairwise explicit tail terms so
the later rate algebra cannot hide a probability-space change.
-/
theorem theorem10_iidUserEmpiricalWinRate_uniformOffDiag_tail_bound
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {preference : PairwisePreference PUnit Alternative}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (husers_pos : 0 < users) (hcomparisons_pos : 0 < comparisonsPerUser)
    (hsampling_pos : ∀ alternative, 0 < (sampling alternative).toReal)
    (epsilon : ℝ) (hepsilon_nonneg : 0 ≤ epsilon) :
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample => ∃ pair ∈ (Finset.univ : Finset Alternative).offDiag,
        epsilon < |theorem10IidUserEmpiricalWinRate pair.1 pair.2 sample -
          preference.prob PUnit.unit pair.1 pair.2|) ≤
      ∑ pair ∈ (Finset.univ : Finset Alternative).offDiag,
        theorem10FixedPairRateTailBound sampling users comparisonsPerUser
          pair.1 pair.2 epsilon := by
  classical
  let sourceLaw := pmfProduct (Fin users)
    (theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative))
    (pmfProd responseLaw
      (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
        (theorem2UserPairLabelLaw sampling)))
  have hfixedPair : ∀ pair ∈ (Finset.univ : Finset Alternative).offDiag,
      pmfProb sourceLaw (fun sample =>
        epsilon < |theorem10IidUserEmpiricalWinRate pair.1 pair.2 sample -
          preference.prob PUnit.unit pair.1 pair.2|) ≤
        theorem10FixedPairRateTailBound sampling users comparisonsPerUser
          pair.1 pair.2 epsilon := by
    intro pair hpair
    have hdistinct : pair.1 ≠ pair.2 := (Finset.mem_offDiag.mp hpair).2.2
    let q : ℝ := 2 * (sampling pair.1).toReal * (sampling pair.2).toReal
    let varianceProxy : ℝ :=
      (comparisonsPerUser : ℝ) * q +
      (comparisonsPerUser : ℝ) * ((comparisonsPerUser - 1 : ℕ) : ℝ) * q ^ 2
    let denominator : ℝ := ((users * comparisonsPerUser : ℕ) : ℝ) * q / 2
    have hq_pos : 0 < q := by
      dsimp [q]
      exact mul_pos (mul_pos (by norm_num) (hsampling_pos pair.1))
        (hsampling_pos pair.2)
    have hvariance_pos : 0 < varianceProxy := by
      have hlead : 0 < (comparisonsPerUser : ℝ) * q := by positivity
      have hrest : 0 ≤ (comparisonsPerUser : ℝ) *
          ((comparisonsPerUser - 1 : ℕ) : ℝ) * q ^ 2 := by positivity
      dsimp [varianceProxy]
      linarith
    have hdenominator_pos : 0 < denominator := by
      dsimp [denominator]
      have hproduct_pos : 0 < ((users * comparisonsPerUser : ℕ) : ℝ) := by
        rw [Nat.cast_mul]
        exact mul_pos (by exact_mod_cast husers_pos) (by exact_mod_cast hcomparisons_pos)
      positivity
    have hbernstein_den_pos : 0 < (users : ℝ) * varianceProxy +
        (comparisonsPerUser : ℝ) * (epsilon * denominator) := by
      have hlead : 0 < (users : ℝ) * varianceProxy := by positivity
      have hrest : 0 ≤ (comparisonsPerUser : ℝ) * (epsilon * denominator) := by
        positivity
      linarith
    have hfixed := theorem10_iidUserEmpiricalWinRate_tail_bound
      hcalibrated sampling users comparisonsPerUser pair.1 pair.2 hdistinct
      (epsilon * denominator) (mul_nonneg hepsilon_nonneg hdenominator_pos.le)
      (by simpa [varianceProxy, q, denominator] using hbernstein_den_pos)
      (by simpa [q, denominator] using hdenominator_pos)
    have hepsilon : epsilon * denominator / denominator = epsilon := by
      field_simp [hdenominator_pos.ne']
    change pmfProb sourceLaw (fun sample =>
      epsilon * denominator / denominator <
        |theorem10IidUserEmpiricalWinRate pair.1 pair.2 sample -
          preference.prob PUnit.unit pair.1 pair.2|) ≤ _ at hfixed
    rw [hepsilon] at hfixed
    simpa [sourceLaw, theorem10FixedPairRateTailBound, varianceProxy, q, denominator] using hfixed
  exact (pmfProb_exists_mem_le_sum sourceLaw
    ((Finset.univ : Finset Alternative).offDiag)
    (fun pair sample =>
      epsilon < |theorem10IidUserEmpiricalWinRate pair.1 pair.2 sample -
        preference.prob PUnit.unit pair.1 pair.2|)).trans (by
      apply Finset.sum_le_sum
      intro pair hpair
      exact hfixedPair pair hpair)

/--
All-pairs form of the exact Lemma 10 union: diagonal pairs disappear because
their source empirical win-rate error is identically zero.
-/
theorem theorem10_iidUserPaperWinRate_uniform_tail_bound
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {preference : PairwisePreference PUnit Alternative}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (husers_pos : 0 < users) (hcomparisons_pos : 0 < comparisonsPerUser)
    (hsampling_pos : ∀ alternative, 0 < (sampling alternative).toReal)
    (epsilon : ℝ) (hepsilon_nonneg : 0 ≤ epsilon) :
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample : Fin users →
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative)) =>
        ∃ pair : Alternative × Alternative,
        epsilon < |theorem10IidUserPaperWinRate pair.1 pair.2 sample -
          preference.prob PUnit.unit pair.1 pair.2|) ≤
      ∑ pair ∈ (Finset.univ : Finset Alternative).offDiag,
        theorem10FixedPairRateTailBound sampling users comparisonsPerUser
          pair.1 pair.2 epsilon := by
  classical
  let sourceLaw := pmfProduct (Fin users)
    (theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative))
    (pmfProd responseLaw
      (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
        (theorem2UserPairLabelLaw sampling)))
  have hevent : ∀ sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative)),
      (∃ pair : Alternative × Alternative,
        epsilon < |theorem10IidUserPaperWinRate pair.1 pair.2 sample -
          preference.prob PUnit.unit pair.1 pair.2|) ↔
      ∃ pair ∈ (Finset.univ : Finset Alternative).offDiag,
        epsilon < |theorem10IidUserEmpiricalWinRate pair.1 pair.2 sample -
          preference.prob PUnit.unit pair.1 pair.2| :=
    theorem10_iidUserPaperWinRate_failure_iff_offDiag
      (users := users) (comparisonsPerUser := comparisonsPerUser)
      preference epsilon hepsilon_nonneg
  calc
    pmfProb sourceLaw (fun sample => ∃ pair : Alternative × Alternative,
        epsilon < |theorem10IidUserPaperWinRate pair.1 pair.2 sample -
          preference.prob PUnit.unit pair.1 pair.2|) =
      pmfProb sourceLaw (fun sample =>
        ∃ pair ∈ (Finset.univ : Finset Alternative).offDiag,
          epsilon < |theorem10IidUserEmpiricalWinRate pair.1 pair.2 sample -
            preference.prob PUnit.unit pair.1 pair.2|) := by
          apply pmfProb_congr
          exact hevent
    _ ≤ ∑ pair ∈ (Finset.univ : Finset Alternative).offDiag,
        theorem10FixedPairRateTailBound sampling users comparisonsPerUser
          pair.1 pair.2 epsilon :=
      theorem10_iidUserEmpiricalWinRate_uniformOffDiag_tail_bound hcalibrated sampling users
        comparisonsPerUser husers_pos hcomparisons_pos hsampling_pos epsilon hepsilon_nonneg

end GolzHaghtalabYang2025Distortion
