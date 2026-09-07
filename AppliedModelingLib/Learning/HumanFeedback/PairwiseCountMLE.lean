import AppliedModelingLib.Foundations.Optimization.CoinFlipLikelihood
import AppliedModelingLib.Foundations.Graph.Cycle
import AppliedModelingLib.Foundations.Math.Concavity
import AppliedModelingLib.Foundations.Math.IntervalCrossing
import AppliedModelingLib.Learning.HumanFeedback.PairwiseCount
import Mathlib.Analysis.Convex.Deriv

/-!
# Local Likelihood Facts for Pairwise-Count Random-Utility Models

The two directed count terms for one alternative pair reduce exactly to the
positive-weight binary log likelihood whenever the random-utility link has the
source symmetry `F(-z) + F(z) = 1`. This is the analytic core of local
perfect-fit arguments; it deliberately does not assert the graph-local MLE
conclusion by itself.
-/

namespace AppliedModelingLib
namespace Learning
namespace HumanFeedback
namespace PairwiseCountDataset

/--
If a CDF-like link is strictly increasing and differentiable, then its
logarithm is differentiable at every finite score gap.  Strict monotonicity is
used only to keep the link value away from zero.
-/
theorem differentiable_log_comp_of_differentiable
    (link : CDFLikePairwiseLink) (hstrict : StrictMono (link : ℝ → ℝ))
    (hdifferentiable : Differentiable ℝ (link : ℝ → ℝ)) :
    Differentiable ℝ (fun gap : ℝ => Real.log (link gap)) := by
  intro gap
  exact (Real.differentiableAt_log
    (ne_of_gt (link.openProbability hstrict gap).1)).comp gap (hdifferentiable gap)

/--
The derivative of a differentiable, strictly increasing, strictly log-concave
CDF-like link is strictly positive everywhere after taking logarithms.  This
is the source footnote's point: strict increase alone permits a zero
derivative, while strict concavity makes the derivative strictly decrease and
therefore rules a zero out.
-/
theorem deriv_log_comp_pos_of_strictMono_strictConcave_differentiable
    (link : CDFLikePairwiseLink) (hstrict : StrictMono (link : ℝ → ℝ))
    (hlogStrict : StrictConcaveOn ℝ Set.univ (fun gap => Real.log (link gap)))
    (hdifferentiable : Differentiable ℝ (link : ℝ → ℝ)) (gap : ℝ) :
    0 < deriv (fun point : ℝ => Real.log (link point)) gap := by
  have hlogStrictMono : StrictMono (fun point : ℝ => Real.log (link point)) := by
    intro first second hfirstSecond
    exact Real.strictMonoOn_log (link.openProbability hstrict first).1
      (link.openProbability hstrict second).1 (hstrict hfirstSecond)
  have hlogDifferentiable : Differentiable ℝ (fun point : ℝ => Real.log (link point)) :=
    differentiable_log_comp_of_differentiable link hstrict hdifferentiable
  have hnonnegative : 0 ≤ deriv (fun point : ℝ => Real.log (link point)) gap :=
    hlogStrictMono.monotone.deriv_nonneg
  by_contra hnotPositive
  have hnonpositive : deriv (fun point : ℝ => Real.log (link point)) gap ≤ 0 :=
    le_of_not_gt hnotPositive
  have hzero : deriv (fun point : ℝ => Real.log (link point)) gap = 0 :=
    le_antisymm hnonpositive hnonnegative
  have hstrictAnti : StrictAntiOn
      (deriv (fun point : ℝ => Real.log (link point))) Set.univ :=
    hlogStrict.strictAntiOn_deriv (fun point _ => hlogDifferentiable point)
  have hnegative : deriv (fun point : ℝ => Real.log (link point)) (gap + 1) < 0 := by
    calc
      deriv (fun point : ℝ => Real.log (link point)) (gap + 1) <
          deriv (fun point : ℝ => Real.log (link point)) gap :=
        hstrictAnti (by simp) (by simp) (by linarith)
      _ = 0 := hzero
  have hnonnegativeNext :
      0 ≤ deriv (fun point : ℝ => Real.log (link point)) (gap + 1) :=
    hlogStrictMono.monotone.deriv_nonneg
  linarith

/--
The final perturbation step in Supplement E: if a continuously varying score
path has a strict `second`-over-`first` order at zero, some parameter in
`(0, 1]` retains that order. The source's remaining analytic bridge is to prove
continuity of its unique MLE path for the displayed parametric dataset.
-/
theorem exists_pos_le_one_score_order_of_continuousAt
    {Alternative : Type*} (scorePath : ℝ → ScoreVector Alternative)
    (first second : Alternative)
    (hcontinuous : ContinuousAt
      (fun parameter => scorePath parameter second - scorePath parameter first) 0)
    (horder : scorePath 0 first < scorePath 0 second) :
    ∃ parameter : ℝ, 0 < parameter ∧ parameter ≤ 1 ∧
      scorePath parameter first < scorePath parameter second := by
  obtain ⟨parameter, hpositive, hle_one, hgap⟩ :=
    exists_pos_le_one_of_continuousAt_of_pos hcontinuous (sub_pos.mpr horder)
  exact ⟨parameter, hpositive, hle_one, sub_pos.mp hgap⟩

/--
The rational-count version of the final perturbation step: the persistent
strict order can be realized at `ε = 1 / denominator`, with a positive natural
denominator. This is suitable for an exact integer scaling of pairwise counts.
-/
theorem exists_pos_unitFraction_score_order_of_continuousAt
    {Alternative : Type*} (scorePath : ℝ → ScoreVector Alternative)
    (first second : Alternative)
    (hcontinuous : ContinuousAt
      (fun parameter => scorePath parameter second - scorePath parameter first) 0)
    (horder : scorePath 0 first < scorePath 0 second) :
    ∃ denominator : ℕ, 0 < denominator ∧ 1 ≤ denominator ∧
      scorePath ((1 : ℝ) / denominator) first <
        scorePath ((1 : ℝ) / denominator) second := by
  obtain ⟨denominator, hpositive, hle_one, hgap⟩ :=
    exists_pos_unitFraction_of_continuousAt_of_pos hcontinuous (sub_pos.mpr horder)
  exact ⟨denominator, hpositive, hle_one, sub_pos.mp hgap⟩

/-- Replace the score of one alternative while leaving all other coordinates unchanged. -/
def scoreReplace {Alternative : Type*} [DecidableEq Alternative] (score : ScoreVector Alternative)
    (alternative : Alternative) (value : ℝ) : ScoreVector Alternative :=
  fun candidate => if candidate = alternative then value else score candidate

/-- Paste two score vectors along a finite block of alternatives. -/
def scorePaste {Alternative : Type*} [DecidableEq Alternative]
    (left : Finset Alternative) (leftScore rightScore : ScoreVector Alternative) :
    ScoreVector Alternative :=
  fun alternative => if alternative ∈ left then leftScore alternative else rightScore alternative

/-- A pasted score vector uses its left score on the selected block. -/
theorem scorePaste_apply_of_mem {Alternative : Type*} [DecidableEq Alternative]
    (left : Finset Alternative) (leftScore rightScore : ScoreVector Alternative)
    {alternative : Alternative} (hmem : alternative ∈ left) :
    scorePaste left leftScore rightScore alternative = leftScore alternative := by
  simp [scorePaste, hmem]

/-- A pasted score vector uses its right score outside the selected block. -/
theorem scorePaste_apply_of_not_mem {Alternative : Type*} [DecidableEq Alternative]
    (left : Finset Alternative) (leftScore rightScore : ScoreVector Alternative)
    {alternative : Alternative} (hnotmem : alternative ∉ left) :
    scorePaste left leftScore rightScore alternative = rightScore alternative := by
  simp [scorePaste, hnotmem]

/-- Exchange the score coordinates of two alternatives. -/
def scoreSwap {Alternative : Type*} [DecidableEq Alternative] (score : ScoreVector Alternative)
    (first second : Alternative) : ScoreVector Alternative :=
  fun alternative =>
    if alternative = first then score second else
      if alternative = second then score first else score alternative

/-- The first coordinate of a score swap is the old second coordinate. -/
theorem scoreSwap_apply_first {Alternative : Type*} [DecidableEq Alternative]
    (score : ScoreVector Alternative) (first second : Alternative) :
    scoreSwap score first second first = score second := by
  simp [scoreSwap]

/-- The second coordinate of a score swap is the old first coordinate. -/
theorem scoreSwap_apply_second {Alternative : Type*} [DecidableEq Alternative]
    (score : ScoreVector Alternative) {first second : Alternative} (hne : first ≠ second) :
    scoreSwap score first second second = score first := by
  simp [scoreSwap, hne.symm]

/-- A score swap leaves every coordinate outside the exchanged pair unchanged. -/
theorem scoreSwap_apply_other {Alternative : Type*} [DecidableEq Alternative]
    (score : ScoreVector Alternative) (first second other : Alternative)
    (hfirst : other ≠ first) (hsecond : other ≠ second) :
    scoreSwap score first second other = score other := by
  simp [scoreSwap, hfirst, hsecond]

/--
If a larger weight is attached to a smaller positive value, exchanging the two
values strictly increases the weighted log sum. This is the algebraic exchange
step behind the Pareto proof in Supplement C.
-/
theorem weightedLogTwoPointSwap_strict
    {highWeight lowWeight lowValue highValue : ℝ}
    (hweights : lowWeight < highWeight)
    (hlowValue : 0 < lowValue) (hvalueOrder : lowValue < highValue) :
    highWeight * Real.log lowValue + lowWeight * Real.log highValue <
      highWeight * Real.log highValue + lowWeight * Real.log lowValue := by
  have hhighValue : 0 < highValue := lt_trans hlowValue hvalueOrder
  have hlogOrder : Real.log lowValue < Real.log highValue :=
    Real.strictMonoOn_log hlowValue hhighValue hvalueOrder
  have hweightGap : 0 < highWeight - lowWeight := sub_pos.mpr hweights
  have hlogGap : 0 < Real.log highValue - Real.log lowValue := sub_pos.mpr hlogOrder
  have hproduct : 0 < (highWeight - lowWeight) *
      (Real.log highValue - Real.log lowValue) := mul_pos hweightGap hlogGap
  nlinarith

/--
The outgoing-pair exchange in the Pareto proof: if `first` has both the lower
score and the larger count against a third alternative, swapping the two scores
strictly increases those two outgoing likelihood contributions.
-/
theorem outgoingPairwiseLogTerms_scoreSwap_strict
    {Alternative : Type*} [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (score : ScoreVector Alternative) {first second other : Alternative}
    (hscore : score first < score second)
    (hcount : dataset.count second other < dataset.count first other)
    (hother_first : other ≠ first) (hother_second : other ≠ second)
    (hstrict : StrictMono (link : ℝ → ℝ)) :
    (dataset.count first other : ℝ) *
          Real.log (randomUtilityWinProbability link score first other) +
        (dataset.count second other : ℝ) *
          Real.log (randomUtilityWinProbability link score second other) <
      (dataset.count first other : ℝ) *
          Real.log (randomUtilityWinProbability link (scoreSwap score first second) first other) +
        (dataset.count second other : ℝ) *
          Real.log (randomUtilityWinProbability link (scoreSwap score first second) second other) := by
  have hfirst_second : first ≠ second := by
    intro h
    subst second
    exact lt_irrefl _ hscore
  have hlow : 0 < randomUtilityWinProbability link score first other :=
    (link.openProbability hstrict (score first - score other)).1
  have hprobOrder : randomUtilityWinProbability link score first other <
      randomUtilityWinProbability link score second other := by
    unfold randomUtilityWinProbability
    exact hstrict (sub_lt_sub_right hscore (score other))
  have hswapFirst : randomUtilityWinProbability link (scoreSwap score first second) first other =
      randomUtilityWinProbability link score second other := by
    unfold randomUtilityWinProbability
    rw [scoreSwap_apply_first score first second,
      scoreSwap_apply_other score first second other hother_first hother_second]
  have hswapSecond : randomUtilityWinProbability link (scoreSwap score first second) second other =
      randomUtilityWinProbability link score first other := by
    unfold randomUtilityWinProbability
    rw [scoreSwap_apply_second score hfirst_second,
      scoreSwap_apply_other score first second other hother_first hother_second]
  rw [hswapFirst, hswapSecond]
  exact weightedLogTwoPointSwap_strict (by exact_mod_cast hcount) hlow hprobOrder

/--
The incoming-pair exchange in the Pareto proof. It is the dual count ordering
of `outgoingPairwiseLogTerms_scoreSwap_strict`.
-/
theorem incomingPairwiseLogTerms_scoreSwap_strict
    {Alternative : Type*} [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (score : ScoreVector Alternative) {first second other : Alternative}
    (hscore : score first < score second)
    (hcount : dataset.count other first < dataset.count other second)
    (hother_first : other ≠ first) (hother_second : other ≠ second)
    (hstrict : StrictMono (link : ℝ → ℝ)) :
    (dataset.count other first : ℝ) *
          Real.log (randomUtilityWinProbability link score other first) +
        (dataset.count other second : ℝ) *
          Real.log (randomUtilityWinProbability link score other second) <
      (dataset.count other first : ℝ) *
          Real.log (randomUtilityWinProbability link (scoreSwap score first second) other first) +
        (dataset.count other second : ℝ) *
          Real.log (randomUtilityWinProbability link (scoreSwap score first second) other second) := by
  have hfirst_second : first ≠ second := by
    intro h
    subst second
    exact lt_irrefl _ hscore
  have hlow : 0 < randomUtilityWinProbability link score other second :=
    (link.openProbability hstrict (score other - score second)).1
  have hprobOrder : randomUtilityWinProbability link score other second <
      randomUtilityWinProbability link score other first := by
    unfold randomUtilityWinProbability
    exact hstrict (sub_lt_sub_left hscore (score other))
  have hswapFirst : randomUtilityWinProbability link (scoreSwap score first second) other first =
      randomUtilityWinProbability link score other second := by
    unfold randomUtilityWinProbability
    rw [scoreSwap_apply_other score first second other hother_first hother_second,
      scoreSwap_apply_first score first second]
  have hswapSecond : randomUtilityWinProbability link (scoreSwap score first second) other second =
      randomUtilityWinProbability link score other first := by
    unfold randomUtilityWinProbability
    rw [scoreSwap_apply_other score first second other hother_first hother_second,
      scoreSwap_apply_second score hfirst_second]
  rw [hswapFirst, hswapSecond]
  have hswap := weightedLogTwoPointSwap_strict
    (highWeight := (dataset.count other second : ℝ))
    (lowWeight := (dataset.count other first : ℝ))
    (lowValue := randomUtilityWinProbability link score other second)
    (highValue := randomUtilityWinProbability link score other first)
    (by exact_mod_cast hcount) hlow hprobOrder
  linarith

/--
The direct-pair exchange in the Pareto proof: the more frequent `first ≻
second` outcome receives the larger link value after the scores are swapped.
-/
theorem directPairwiseLogTerms_scoreSwap_strict
    {Alternative : Type*} [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (score : ScoreVector Alternative) {first second : Alternative}
    (hscore : score first < score second)
    (hcount : dataset.count second first < dataset.count first second)
    (hstrict : StrictMono (link : ℝ → ℝ)) :
    (dataset.count first second : ℝ) *
          Real.log (randomUtilityWinProbability link score first second) +
        (dataset.count second first : ℝ) *
          Real.log (randomUtilityWinProbability link score second first) <
      (dataset.count first second : ℝ) *
          Real.log (randomUtilityWinProbability link (scoreSwap score first second) first second) +
        (dataset.count second first : ℝ) *
          Real.log (randomUtilityWinProbability link (scoreSwap score first second) second first) := by
  have hfirst_second : first ≠ second := by
    intro h
    subst second
    exact lt_irrefl _ hscore
  have hlow : 0 < randomUtilityWinProbability link score first second :=
    (link.openProbability hstrict (score first - score second)).1
  have hprobOrder : randomUtilityWinProbability link score first second <
      randomUtilityWinProbability link score second first := by
    unfold randomUtilityWinProbability
    have hgap : score second - score first = -(score first - score second) := by ring
    rw [hgap]
    have hnegativeGap : score first - score second < -(score first - score second) := by linarith
    exact hstrict hnegativeGap
  have hswapFirst : randomUtilityWinProbability link (scoreSwap score first second) first second =
      randomUtilityWinProbability link score second first := by
    unfold randomUtilityWinProbability
    rw [scoreSwap_apply_first score first second, scoreSwap_apply_second score hfirst_second]
  have hswapSecond : randomUtilityWinProbability link (scoreSwap score first second) second first =
      randomUtilityWinProbability link score first second := by
    unfold randomUtilityWinProbability
    rw [scoreSwap_apply_second score hfirst_second, scoreSwap_apply_first score first second]
  rw [hswapFirst, hswapSecond]
  exact weightedLogTwoPointSwap_strict (by exact_mod_cast hcount) hlow hprobOrder

/--
For one third alternative, the two outgoing and two incoming directed terms
strictly improve together under the Pareto score swap.
-/
theorem otherPairwiseLogTerms_scoreSwap_strict
    {Alternative : Type*} [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (score : ScoreVector Alternative) {first second other : Alternative}
    (hscore : score first < score second)
    (hcount_out : dataset.count second other < dataset.count first other)
    (hcount_in : dataset.count other first < dataset.count other second)
    (hother_first : other ≠ first) (hother_second : other ≠ second)
    (hstrict : StrictMono (link : ℝ → ℝ)) :
    ((dataset.count first other : ℝ) *
          Real.log (randomUtilityWinProbability link score first other) +
        (dataset.count second other : ℝ) *
          Real.log (randomUtilityWinProbability link score second other)) +
      ((dataset.count other first : ℝ) *
          Real.log (randomUtilityWinProbability link score other first) +
        (dataset.count other second : ℝ) *
          Real.log (randomUtilityWinProbability link score other second)) <
      ((dataset.count first other : ℝ) *
          Real.log (randomUtilityWinProbability link (scoreSwap score first second) first other) +
        (dataset.count second other : ℝ) *
          Real.log (randomUtilityWinProbability link (scoreSwap score first second) second other)) +
      ((dataset.count other first : ℝ) *
          Real.log (randomUtilityWinProbability link (scoreSwap score first second) other first) +
        (dataset.count other second : ℝ) *
          Real.log (randomUtilityWinProbability link (scoreSwap score first second) other second)) := by
  have hout := outgoingPairwiseLogTerms_scoreSwap_strict dataset link score hscore hcount_out
    hother_first hother_second hstrict
  have hin := incomingPairwiseLogTerms_scoreSwap_strict dataset link score hscore hcount_in
    hother_first hother_second hstrict
  linarith

/-- An ordered pair is incident to an alternative when it contains that alternative. -/
def incidentTo {Alternative : Type*} [DecidableEq Alternative] (alternative : Alternative)
    (pair : Alternative × Alternative) : Prop :=
  pair.1 = alternative ∨ pair.2 = alternative

/-- The finite off-diagonal pairs incident to one alternative. -/
noncomputable def incidentPairs {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (alternative : Alternative) : Finset (Alternative × Alternative) := by
  classical
  exact (Finset.univ : Finset Alternative).offDiag.filter (incidentTo alternative)

/-- The finite off-diagonal pairs not incident to one alternative. -/
noncomputable def nonincidentPairs {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (alternative : Alternative) : Finset (Alternative × Alternative) := by
  classical
  exact (Finset.univ : Finset Alternative).offDiag.filter
    (fun pair => ¬ incidentTo alternative pair)

/-- One summand of the finite ordered-pair likelihood. -/
noncomputable def pairwiseLogLikelihoodSummand
    {Alternative : Type*} (dataset : PairwiseCountDataset Alternative)
    (link : ℝ → ℝ) (score : ScoreVector Alternative)
    (pair : Alternative × Alternative) : ℝ :=
  (dataset.count pair.1 pair.2 : ℝ) *
    Real.log (randomUtilityWinProbability link score pair.1 pair.2)

/-- A likelihood summand is unchanged when its two endpoint scores agree. -/
theorem pairwiseLogLikelihoodSummand_eq_of_score_agree
    {Alternative : Type*} (dataset : PairwiseCountDataset Alternative) (link : ℝ → ℝ)
    (firstScore secondScore : ScoreVector Alternative) (first second : Alternative)
    (hfirst : firstScore first = secondScore first)
    (hsecond : firstScore second = secondScore second) :
    pairwiseLogLikelihoodSummand dataset link firstScore (first, second) =
      pairwiseLogLikelihoodSummand dataset link secondScore (first, second) := by
  unfold pairwiseLogLikelihoodSummand randomUtilityWinProbability
  rw [hfirst, hsecond]

/--
The finite likelihood sum over two score blocks is unchanged when the two
score vectors agree on every endpoint in the respective blocks.
-/
theorem sum_pairwiseLogLikelihoodSummand_eq_of_score_agree
    {Alternative : Type*} [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : ℝ → ℝ)
    (firstScore secondScore : ScoreVector Alternative)
    (firstBlock secondBlock : Finset Alternative)
    (hfirst : ∀ first ∈ firstBlock, firstScore first = secondScore first)
    (hsecond : ∀ second ∈ secondBlock, firstScore second = secondScore second) :
    (∑ first ∈ firstBlock, ∑ second ∈ secondBlock,
      pairwiseLogLikelihoodSummand dataset link firstScore (first, second)) =
      ∑ first ∈ firstBlock, ∑ second ∈ secondBlock,
        pairwiseLogLikelihoodSummand dataset link secondScore (first, second) := by
  apply Finset.sum_congr rfl
  intro first hfirstmem
  apply Finset.sum_congr rfl
  intro second hsecondmem
  exact pairwiseLogLikelihoodSummand_eq_of_score_agree dataset link firstScore secondScore
    first second (hfirst first hfirstmem) (hsecond second hsecondmem)

/--
The off-diagonal likelihood can be written as a sum over every ordered pair:
the added diagonal terms vanish by the dataset's diagonal-count invariant.
This is the finite reindexing needed to partition the Pareto score-swap proof.
-/
theorem pairwiseLogLikelihood_eq_sum_univ_product
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : ℝ → ℝ)
    (score : ScoreVector Alternative) :
    pairwiseLogLikelihood dataset link score =
      ∑ first : Alternative, ∑ second : Alternative,
        pairwiseLogLikelihoodSummand dataset link score (first, second) := by
  classical
  have hdiag_zero : ∀ pair ∈ (Finset.univ : Finset Alternative).diag,
      pairwiseLogLikelihoodSummand dataset link score pair = 0 := by
    rintro ⟨first, second⟩ hpair
    have hsame : first = second := (Finset.mem_diag.mp hpair).2
    subst second
    simp [pairwiseLogLikelihoodSummand, dataset.diagonal_zero]
  change (∑ pair ∈ (Finset.univ : Finset Alternative).offDiag,
    pairwiseLogLikelihoodSummand dataset link score pair) = _
  calc
    ∑ pair ∈ (Finset.univ : Finset Alternative).offDiag,
        pairwiseLogLikelihoodSummand dataset link score pair =
        (∑ pair ∈ (Finset.univ : Finset Alternative).diag,
          pairwiseLogLikelihoodSummand dataset link score pair) +
          ∑ pair ∈ (Finset.univ : Finset Alternative).offDiag,
            pairwiseLogLikelihoodSummand dataset link score pair := by
              rw [Finset.sum_eq_zero hdiag_zero]
              ring
    _ = ∑ pair ∈ (Finset.univ : Finset Alternative).diag ∪
          (Finset.univ : Finset Alternative).offDiag,
        pairwiseLogLikelihoodSummand dataset link score pair := by
          rw [Finset.sum_union (Finset.disjoint_diag_offDiag _)]
    _ = ∑ pair ∈ (Finset.univ : Finset Alternative) ×ˢ Finset.univ,
        pairwiseLogLikelihoodSummand dataset link score pair := by
          rw [Finset.diag_union_offDiag]
    _ = ∑ first : Alternative, ∑ second : Alternative,
        pairwiseLogLikelihoodSummand dataset link score (first, second) := by
          rw [Finset.sum_product]

/--
A score swap leaves a likelihood summand unchanged when neither endpoint is
one of the exchanged alternatives.
-/
theorem pairwiseLogLikelihoodSummand_scoreSwap_eq_of_outside
    {Alternative : Type*} [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : ℝ → ℝ)
    (score : ScoreVector Alternative) (first second left right : Alternative)
    (hleft_first : left ≠ first) (hleft_second : left ≠ second)
    (hright_first : right ≠ first) (hright_second : right ≠ second) :
    pairwiseLogLikelihoodSummand dataset link (scoreSwap score first second) (left, right) =
      pairwiseLogLikelihoodSummand dataset link score (left, right) := by
  unfold pairwiseLogLikelihoodSummand randomUtilityWinProbability
  rw [scoreSwap_apply_other score first second left hleft_first hleft_second,
    scoreSwap_apply_other score first second right hright_first hright_second]

/-- The alternatives distinct from the two endpoints of a Pareto score swap. -/
noncomputable def otherAlternatives {Alternative : Type*} [Fintype Alternative]
    [DecidableEq Alternative] (first second : Alternative) : Finset Alternative :=
  ((Finset.univ : Finset Alternative).erase first).erase second

/-- Split a finite sum into two selected alternatives and every remaining alternative. -/
theorem sum_univ_eq_two_add_others
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (f : Alternative → ℝ) {first second : Alternative} (hne : first ≠ second) :
    (∑ alternative : Alternative, f alternative) =
      f first + f second + ∑ alternative ∈ otherAlternatives first second, f alternative := by
  classical
  have huniv : (Finset.univ : Finset Alternative) =
      insert first (insert second (otherAlternatives first second)) := by
    ext alternative
    by_cases hfirst : alternative = first
    · simp [hfirst]
    by_cases hsecond : alternative = second
    · simp [hsecond]
    · simp [otherAlternatives, hfirst, hsecond]
  have hsecond : second ∉ otherAlternatives first second := by
    simp [otherAlternatives]
  have hfirst : first ∉ insert second (otherAlternatives first second) := by
    simp [otherAlternatives, hne]
  rw [huniv, Finset.sum_insert hfirst, Finset.sum_insert hsecond]
  ring

/--
`first` has `second` as its only neighbor in the source comparison graph:
the pair is compared in at least one direction, and every other incident
directed count is zero.
-/
def hasOnlyNeighbor {Alternative : Type*} (dataset : PairwiseCountDataset Alternative)
    (first second : Alternative) : Prop :=
  first ≠ second ∧
    0 < dataset.count first second + dataset.count second first ∧
    ∀ other, other ≠ first → other ≠ second →
      dataset.count first other = 0 ∧ dataset.count other first = 0

/-- The two directed log-likelihood terms associated with an unordered pair. -/
noncomputable def pairwiseLogTerm
    {Alternative : Type*} (dataset : PairwiseCountDataset Alternative)
    (link : ℝ → ℝ) (score : ScoreVector Alternative)
    (first second : Alternative) : ℝ :=
    (dataset.count first second : ℝ) *
      Real.log (randomUtilityWinProbability link score first second) +
    (dataset.count second first : ℝ) *
      Real.log (randomUtilityWinProbability link score second first)

/--
The two directed likelihood contributions for one unordered alternative pair,
viewed as a function of that pair's score difference. This is the `ℓ_xy`
function used in Supplement D's monotonicity proof.
-/
noncomputable def pairwiseLogTermAtGap
    {Alternative : Type*} (dataset : PairwiseCountDataset Alternative)
    (link : ℝ → ℝ) (first second : Alternative) (gap : ℝ) : ℝ :=
  (dataset.count first second : ℝ) * Real.log (link gap) +
    (dataset.count second first : ℝ) * Real.log (link (-gap))

/--
The source's two-directed likelihood term is exactly its score-gap form at the
gap induced by a score vector. This connects the concrete MLE likelihood to the
`ℓ_xy` notation used in Supplement D.
-/
theorem pairwiseLogTerm_eq_atGap
    {Alternative : Type*} (dataset : PairwiseCountDataset Alternative)
    (link : CDFLikePairwiseLink) (score : ScoreVector Alternative)
    (first second : Alternative) :
    pairwiseLogTerm dataset link score first second =
      pairwiseLogTermAtGap dataset link first second (score first - score second) := by
  unfold pairwiseLogTerm pairwiseLogTermAtGap randomUtilityWinProbability
  congr 2
  ring_nf

/-- The ordered-pair indices joining two disjoint blocks of alternatives. -/
def crossPairIndices {Alternative : Type*} [DecidableEq Alternative]
    (left right : Finset Alternative) : Finset (Alternative × Alternative) :=
  (left ×ˢ right) ∪ (right ×ˢ left)

/--
The two oriented ordered-pair blocks joining disjoint finite alternative sets
are disjoint. This permits their likelihood contributions to be combined into
the source's single two-direction `ℓ_xy` term.
-/
theorem disjoint_crossPairIndices_blocks
    {Alternative : Type*} [DecidableEq Alternative]
    (left right : Finset Alternative) (hdisjoint : Disjoint left right) :
    Disjoint (left ×ˢ right) (right ×ˢ left) := by
  refine Finset.disjoint_left.2 ?_
  intro pair hleft hright
  exact Finset.disjoint_left.1 hdisjoint
    (Finset.mem_product.mp hleft).1 (Finset.mem_product.mp hright).1

/--
The ordered likelihood summands between two disjoint alternative blocks equal
the sum of the source's two-direction pair terms, once for each `left × right`
pair. This is the finite reindexing underlying the cross-pair block in
Supplement D of Noothigattu--Peters--Procaccia (2020).
-/
theorem sum_crossPairIndices_pairwiseLogLikelihoodSummand
    {Alternative : Type*} [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : ℝ → ℝ)
    (score : ScoreVector Alternative) (left right : Finset Alternative)
    (hdisjoint : Disjoint left right) :
    ∑ pair ∈ crossPairIndices left right,
      pairwiseLogLikelihoodSummand dataset link score pair =
      ∑ leftAlternative ∈ left, ∑ rightAlternative ∈ right,
        pairwiseLogTerm dataset link score rightAlternative leftAlternative := by
  rw [crossPairIndices, Finset.sum_union
    (disjoint_crossPairIndices_blocks left right hdisjoint),
    Finset.sum_product, Finset.sum_product]
  have hreverse :
      (∑ rightAlternative ∈ right, ∑ leftAlternative ∈ left,
        pairwiseLogLikelihoodSummand dataset link score (rightAlternative, leftAlternative)) =
      ∑ leftAlternative ∈ left, ∑ rightAlternative ∈ right,
        pairwiseLogLikelihoodSummand dataset link score (rightAlternative, leftAlternative) := by
    rw [Finset.sum_comm]
  rw [hreverse, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro leftAlternative hleft
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rightAlternative hright
  unfold pairwiseLogLikelihoodSummand pairwiseLogTerm
  ring

/--
For a finite partition of all alternatives into `left` and `right`, the full
ordered-pair likelihood is the sum of the two within-block parts and the
cross-block part. The latter remains expressed through `crossPairIndices` so
that it can be converted to the source's `ℓ_xy` terms by the preceding lemma.
-/
theorem pairwiseLogLikelihood_eq_block_sums
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : ℝ → ℝ)
    (score : ScoreVector Alternative) (left right : Finset Alternative)
    (hcover : left ∪ right = Finset.univ)
    (hdisjoint : Disjoint left right) :
    pairwiseLogLikelihood dataset link score =
      (∑ leftAlternative ∈ left, ∑ secondAlternative ∈ left,
        pairwiseLogLikelihoodSummand dataset link score
          (leftAlternative, secondAlternative)) +
      (∑ rightAlternative ∈ right, ∑ secondAlternative ∈ right,
        pairwiseLogLikelihoodSummand dataset link score
          (rightAlternative, secondAlternative)) +
      ∑ pair ∈ crossPairIndices left right,
        pairwiseLogLikelihoodSummand dataset link score pair := by
  rw [pairwiseLogLikelihood_eq_sum_univ_product]
  rw [← hcover]
  rw [Finset.sum_union hdisjoint]
  simp_rw [Finset.sum_union hdisjoint]
  unfold crossPairIndices
  rw [Finset.sum_union (disjoint_crossPairIndices_blocks left right hdisjoint)]
  simp only [Finset.sum_product]
  simp_rw [Finset.sum_add_distrib]
  ring

/-- Swapping ordered distinct pairs permutes the finite off-diagonal pair set. -/
theorem sum_offDiag_swap
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (term : Alternative × Alternative → ℝ) :
    (∑ pair ∈ (Finset.univ : Finset Alternative).offDiag, term (pair.2, pair.1)) =
      ∑ pair ∈ (Finset.univ : Finset Alternative).offDiag, term pair := by
  let pairs : Finset (Alternative × Alternative) :=
    (Finset.univ : Finset Alternative).offDiag
  let swapEquiv : (Alternative × Alternative) ≃ (Alternative × Alternative) :=
    Equiv.prodComm Alternative Alternative
  change (∑ pair ∈ pairs, term (swapEquiv pair)) = ∑ pair ∈ pairs, term pair
  apply Finset.sum_equiv swapEquiv
  · rintro ⟨first, second⟩
    simp only [pairs, swapEquiv, Equiv.prodComm_apply, Finset.mem_offDiag,
      Finset.mem_univ, true_and]
    exact ne_comm
  · intro pair _
    rfl

/-- Reverse every directed pairwise comparison count. -/
def transpose {Alternative : Type*} (dataset : PairwiseCountDataset Alternative) :
    PairwiseCountDataset Alternative where
  count := fun first second => dataset.count second first
  diagonal_zero := by
    intro alternative
    exact dataset.diagonal_zero alternative

/-- Counts in the transposed dataset reverse their endpoints. -/
@[simp] theorem transpose_count {Alternative : Type*} (dataset : PairwiseCountDataset Alternative)
    (first second : Alternative) :
    (transpose dataset).count first second = dataset.count second first :=
  rfl

/-- Directed-count transposition is an involution. -/
theorem transpose_transpose {Alternative : Type*} (dataset : PairwiseCountDataset Alternative) :
    transpose (transpose dataset) = dataset := by
  apply PairwiseCountDataset.ext
  intro first second
  rfl

/-- A source one-pair count increase reverses direction after transposition. -/
theorem transpose_hasSinglePairCountIncrease
    {Alternative : Type*} (baseline updated : PairwiseCountDataset Alternative)
    (winner loser : Alternative)
    (hincrease : hasSinglePairCountIncrease baseline updated winner loser) :
    hasSinglePairCountIncrease (transpose baseline) (transpose updated) loser winner := by
  constructor
  · exact hincrease.1
  · intro first second hpair
    have horiginal : (second, first) ≠ (winner, loser) := by
      intro h
      apply hpair
      exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    exact hincrease.2 second first horiginal

/--
Negating every score converts the likelihood of a transposed directed-count
dataset back to the original likelihood.
-/
theorem pairwiseLogLikelihood_transpose_neg
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : ℝ → ℝ)
    (score : ScoreVector Alternative) :
    pairwiseLogLikelihood (transpose dataset) link (fun alternative => -score alternative) =
      pairwiseLogLikelihood dataset link score := by
  let term : Alternative × Alternative → ℝ := fun pair =>
    (dataset.count pair.1 pair.2 : ℝ) *
      Real.log (randomUtilityWinProbability link score pair.1 pair.2)
  unfold pairwiseLogLikelihood
  calc
    ∑ pair ∈ (Finset.univ : Finset Alternative).offDiag,
        ((transpose dataset).count pair.1 pair.2 : ℝ) *
          Real.log (randomUtilityWinProbability link (fun alternative => -score alternative)
            pair.1 pair.2) =
        ∑ pair ∈ (Finset.univ : Finset Alternative).offDiag, term (pair.2, pair.1) := by
          apply Finset.sum_congr rfl
          rintro ⟨first, second⟩ _
          dsimp [term, transpose, randomUtilityWinProbability]
          congr 2
          ring_nf
    _ = ∑ pair ∈ (Finset.univ : Finset Alternative).offDiag, term pair :=
      sum_offDiag_swap term
    _ = ∑ pair ∈ (Finset.univ : Finset Alternative).offDiag,
        (dataset.count pair.1 pair.2 : ℝ) *
          Real.log (randomUtilityWinProbability link score pair.1 pair.2) := rfl

/-- Negated scores transport a fixed-reference MLE to the transposed dataset. -/
theorem isPairwiseMLE_transpose_neg
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : ℝ → ℝ)
    (reference : Alternative) (score : ScoreVector Alternative)
    (hmle : isPairwiseMLE dataset link reference score) :
    isPairwiseMLE (transpose dataset) link reference (fun alternative => -score alternative) := by
  constructor
  · change -score reference = 0
    have hscoreReference := hmle.1
    change score reference = 0 at hscoreReference
    linarith
  · intro candidate hcandidate
    have hnegCandidate : (fun alternative => -candidate alternative) ∈
        {candidate : ScoreVector Alternative | isReferenceNormalized reference candidate} := by
      change candidate reference = 0 at hcandidate
      change -candidate reference = 0
      linarith
    have hmax := hmle.2 hnegCandidate
    calc
      pairwiseLogLikelihood (transpose dataset) link candidate =
          pairwiseLogLikelihood dataset link (fun alternative => -candidate alternative) := by
        simpa using pairwiseLogLikelihood_transpose_neg dataset link
          (fun alternative => -candidate alternative)
      _ ≤ pairwiseLogLikelihood dataset link score := hmax
      _ = pairwiseLogLikelihood (transpose dataset) link (fun alternative => -score alternative) :=
        (pairwiseLogLikelihood_transpose_neg dataset link score).symm

/-- Fixed-reference MLE uniqueness is preserved by count transposition and score negation. -/
theorem hasUniquePairwiseMLE_transpose_neg
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : ℝ → ℝ)
    (reference : Alternative)
    (hunique : hasUniquePairwiseMLE dataset link reference) :
    hasUniquePairwiseMLE (transpose dataset) link reference := by
  rcases hunique with ⟨score, hmle, huniqueScore⟩
  refine ⟨(fun alternative => -score alternative),
    isPairwiseMLE_transpose_neg dataset link reference score hmle, ?_⟩
  intro other hother
  have hnegOther : isPairwiseMLE dataset link reference (fun alternative => -other alternative) := by
    have htranspose := isPairwiseMLE_transpose_neg (transpose dataset) link reference other hother
    rw [transpose_transpose] at htranspose
    exact htranspose
  have hscore : (fun alternative => -other alternative) = score :=
    huniqueScore _ hnegOther
  funext alternative
  have hcoordinate := congrFun hscore alternative
  linarith

/--
The full ordered-pair likelihood equals one half of the off-diagonal sum of
two-direction pair terms. Each unordered pair occurs twice in that finite sum,
which gives the source's unordered-pair likelihood organization without
selecting an arbitrary orientation.
-/
theorem pairwiseLogLikelihood_eq_half_offDiag_sum_pairwiseLogTerm
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : ℝ → ℝ)
    (score : ScoreVector Alternative) :
    pairwiseLogLikelihood dataset link score =
      (1 / 2 : ℝ) * ∑ pair ∈ (Finset.univ : Finset Alternative).offDiag,
        pairwiseLogTerm dataset link score pair.1 pair.2 := by
  let pairs : Finset (Alternative × Alternative) :=
    (Finset.univ : Finset Alternative).offDiag
  let term : Alternative × Alternative → ℝ := fun pair =>
    (dataset.count pair.1 pair.2 : ℝ) *
      Real.log (randomUtilityWinProbability link score pair.1 pair.2)
  have hswap : (∑ pair ∈ pairs, term (pair.2, pair.1)) = ∑ pair ∈ pairs, term pair := by
    exact sum_offDiag_swap term
  change (∑ pair ∈ pairs, term pair) =
    (1 / 2 : ℝ) * ∑ pair ∈ pairs,
      (term pair + term (pair.2, pair.1))
  rw [Finset.sum_add_distrib, hswap]
  ring

/-- Log-concavity is preserved by reflecting the real score-gap argument. -/
theorem concaveOn_log_comp_neg
    (link : ℝ → ℝ)
    (hlogConcave : ConcaveOn ℝ Set.univ (fun gap => Real.log (link gap))) :
    ConcaveOn ℝ Set.univ (fun gap => Real.log (link (-gap))) := by
  refine ⟨convex_univ, ?_⟩
  intro first _ second _ left right hleft hright hsum
  have hconcave := hlogConcave.2
    (show -first ∈ Set.univ by simp)
    (show -second ∈ Set.univ by simp)
    hleft hright hsum
  convert hconcave using 1; simp only [smul_eq_mul]
  ring_nf

/--
If `log ∘ link` is concave, every two-directed-count pair likelihood is
concave in its score gap, exactly as used for the `ℓ_xy` terms in Supplement D.
-/
theorem pairwiseLogTermAtGap_concaveOn
    {Alternative : Type*} (dataset : PairwiseCountDataset Alternative)
    (link : ℝ → ℝ) (first second : Alternative)
    (hlogConcave : ConcaveOn ℝ Set.univ (fun gap => Real.log (link gap))) :
    ConcaveOn ℝ Set.univ (pairwiseLogTermAtGap dataset link first second) := by
  have hforward : ConcaveOn ℝ Set.univ
      (fun gap => (dataset.count first second : ℝ) * Real.log (link gap)) := by
    simpa only [smul_eq_mul] using hlogConcave.smul
      (show 0 ≤ (dataset.count first second : ℝ) by positivity)
  have hreverse : ConcaveOn ℝ Set.univ
      (fun gap => (dataset.count second first : ℝ) * Real.log (link (-gap))) := by
    simpa only [smul_eq_mul] using (concaveOn_log_comp_neg link hlogConcave).smul
      (show 0 ≤ (dataset.count second first : ℝ) by positivity)
  simpa only [pairwiseLogTermAtGap, Pi.add_apply] using hforward.add hreverse

/--
If `log ∘ F` is concave, the full finite ordered-pair log likelihood is
concave in the score vector.  Strictness requires a connected comparison
graph and is recorded separately.
-/
theorem pairwiseLogLikelihood_concaveOn
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : ℝ → ℝ)
    (hlogConcave : ConcaveOn ℝ Set.univ (fun gap => Real.log (link gap))) :
    ConcaveOn ℝ Set.univ (pairwiseLogLikelihood dataset link) := by
  classical
  refine ⟨convex_univ, ?_⟩
  intro first _ second _ left right hleft hright hsum
  simp only [smul_eq_mul]
  unfold pairwiseLogLikelihood
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  rintro ⟨winner, loser⟩ hpair
  have hconcave := hlogConcave.2
    (show first winner - first loser ∈ Set.univ by simp)
    (show second winner - second loser ∈ Set.univ by simp)
    hleft hright hsum
  have hgap :
      (left * first winner + right * second winner) -
          (left * first loser + right * second loser) =
        left * (first winner - first loser) + right * (second winner - second loser) := by
    ring
  calc
    left * ((dataset.count winner loser : ℝ) *
          Real.log (link (first winner - first loser))) +
        right * ((dataset.count winner loser : ℝ) *
          Real.log (link (second winner - second loser))) =
        (dataset.count winner loser : ℝ) *
          (left * Real.log (link (first winner - first loser)) +
            right * Real.log (link (second winner - second loser))) := by ring
    _ ≤ (dataset.count winner loser : ℝ) *
        Real.log (link (left * (first winner - first loser) +
          right * (second winner - second loser))) := by
      exact mul_le_mul_of_nonneg_left (by simpa only [smul_eq_mul] using hconcave) (by positivity)
    _ = (dataset.count winner loser : ℝ) *
        Real.log (link ((left * first winner + right * second winner) -
          (left * first loser + right * second loser))) := by rw [hgap]

/--
Under strict concavity of `log ∘ F`, connected positive-count comparisons
make the finite likelihood strictly concave after fixing one reference score.
The proof localizes any difference between two normalized score vectors to a
comparison edge, whose positive summand supplies the strict inequality.
-/
theorem pairwiseLogLikelihood_strictConcaveOn_of_isConnected
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : ℝ → ℝ)
    (hlogStrict : StrictConcaveOn ℝ Set.univ (fun gap => Real.log (link gap)))
    (reference : Alternative) (hconnected : dataset.isConnected) :
    StrictConcaveOn ℝ {score : ScoreVector Alternative | isReferenceNormalized reference score}
      (pairwiseLogLikelihood dataset link) := by
  classical
  refine ⟨?_, ?_⟩
  · rw [convex_iff_add_mem]
    intro first hfirst second hsecond left right hleft hright hsum
    change (left • first + right • second) reference = 0
    change left * first reference + right * second reference = 0
    change first reference = 0 at hfirst
    change second reference = 0 at hsecond
    rw [hfirst, hsecond]
    ring
  · intro first hfirst second hsecond hne left right hleft hright hsum
    change first reference = 0 at hfirst
    change second reference = 0 at hsecond
    have hcoordinate : ∃ alternative, first alternative ≠ second alternative := by
      by_contra hnot
      push_neg at hnot
      apply hne
      funext alternative
      exact hnot alternative
    obtain ⟨alternative, halternative⟩ := hcoordinate
    let potential : Alternative → ℝ := fun vertex => first vertex - second vertex
    have hpotential : potential alternative ≠ potential reference := by
      dsimp [potential]
      rw [hfirst, hsecond]
      simpa using sub_ne_zero.mpr halternative
    obtain ⟨edgeFirst, edgeSecond, hadjacent, hpotentialEdge⟩ :=
      AppliedModelingLib.Foundations.Graph.exists_edge_of_reflTransGen_of_potential_ne potential
        (hconnected alternative reference) hpotential
    obtain ⟨winner, loser, hedge, hpotentialGap⟩ :
        ∃ winner loser, dataset.edge winner loser ∧ potential winner ≠ potential loser := by
      rcases hadjacent with hforward | hreverse
      · exact ⟨edgeFirst, edgeSecond, hforward, hpotentialEdge⟩
      · exact ⟨edgeSecond, edgeFirst, hreverse, hpotentialEdge.symm⟩
    have hgapNe : first winner - first loser ≠ second winner - second loser := by
      intro hgap
      apply hpotentialGap
      dsimp [potential]
      linarith
    have hpair : (winner, loser) ∈ (Finset.univ : Finset Alternative).offDiag :=
      Finset.mem_offDiag.2 ⟨Finset.mem_univ _, Finset.mem_univ _, edge_ne dataset hedge⟩
    have htermLe : ∀ winner loser,
        left * ((dataset.count winner loser : ℝ) *
            Real.log (link (first winner - first loser))) +
          right * ((dataset.count winner loser : ℝ) *
            Real.log (link (second winner - second loser))) ≤
          (dataset.count winner loser : ℝ) *
            Real.log (link ((left * first winner + right * second winner) -
              (left * first loser + right * second loser))) := by
      intro localWinner localLoser
      have hconcave := hlogStrict.concaveOn.2
        (show first localWinner - first localLoser ∈ Set.univ by simp)
        (show second localWinner - second localLoser ∈ Set.univ by simp)
        hleft.le hright.le hsum
      have hgap :
          (left * first localWinner + right * second localWinner) -
              (left * first localLoser + right * second localLoser) =
            left * (first localWinner - first localLoser) +
              right * (second localWinner - second localLoser) := by
        ring
      calc
        left * ((dataset.count localWinner localLoser : ℝ) *
              Real.log (link (first localWinner - first localLoser))) +
            right * ((dataset.count localWinner localLoser : ℝ) *
              Real.log (link (second localWinner - second localLoser))) =
            (dataset.count localWinner localLoser : ℝ) *
              (left * Real.log (link (first localWinner - first localLoser)) +
                right * Real.log (link (second localWinner - second localLoser))) := by ring
        _ ≤ (dataset.count localWinner localLoser : ℝ) *
            Real.log (link (left * (first localWinner - first localLoser) +
              right * (second localWinner - second localLoser))) := by
          exact mul_le_mul_of_nonneg_left (by simpa only [smul_eq_mul] using hconcave)
            (by positivity)
        _ = (dataset.count localWinner localLoser : ℝ) *
            Real.log (link ((left * first localWinner + right * second localWinner) -
              (left * first localLoser + right * second localLoser))) := by rw [hgap]
    have htermStrict :
        left * ((dataset.count winner loser : ℝ) *
            Real.log (link (first winner - first loser))) +
          right * ((dataset.count winner loser : ℝ) *
            Real.log (link (second winner - second loser))) <
          (dataset.count winner loser : ℝ) *
            Real.log (link ((left * first winner + right * second winner) -
              (left * first loser + right * second loser))) := by
      have hstrict := hlogStrict.2
        (show first winner - first loser ∈ Set.univ by simp)
        (show second winner - second loser ∈ Set.univ by simp)
        hgapNe hleft hright hsum
      have hgap :
          (left * first winner + right * second winner) -
              (left * first loser + right * second loser) =
            left * (first winner - first loser) + right * (second winner - second loser) := by
        ring
      have hcountPos : 0 < (dataset.count winner loser : ℝ) := by
        exact_mod_cast hedge
      calc
        left * ((dataset.count winner loser : ℝ) *
              Real.log (link (first winner - first loser))) +
            right * ((dataset.count winner loser : ℝ) *
              Real.log (link (second winner - second loser))) =
            (dataset.count winner loser : ℝ) *
              (left * Real.log (link (first winner - first loser)) +
                right * Real.log (link (second winner - second loser))) := by ring
        _ < (dataset.count winner loser : ℝ) *
            Real.log (link (left * (first winner - first loser) +
              right * (second winner - second loser))) := by
          exact mul_lt_mul_of_pos_left (by simpa only [smul_eq_mul] using hstrict) hcountPos
        _ = (dataset.count winner loser : ℝ) *
            Real.log (link ((left * first winner + right * second winner) -
              (left * first loser + right * second loser))) := by rw [hgap]
    simp only [smul_eq_mul]
    unfold pairwiseLogLikelihood
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_lt_sum ?_ ?_
    · rintro ⟨localWinner, localLoser⟩ _
      exact htermLe localWinner localLoser
    · exact ⟨(winner, loser), hpair, htermStrict⟩

/--
If the undirected comparison graph is disconnected, translating the component
away from the fixed reference leaves every likelihood summand unchanged.  It
therefore prevents strict concavity on the reference-normalized score space.
-/
theorem not_pairwiseLogLikelihood_strictConcaveOn_of_not_isConnected
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : ℝ → ℝ)
    (reference : Alternative) (hnotConnected : ¬ dataset.isConnected) :
    ¬ StrictConcaveOn ℝ {score : ScoreVector Alternative | isReferenceNormalized reference score}
      (pairwiseLogLikelihood dataset link) := by
  classical
  have hadjacentSymmetric : Symmetric dataset.adjacent := by
    intro first second hadjacent
    exact hadjacent.elim Or.inr Or.inl
  have htarget : ∃ target, ¬ dataset.connectedTo reference target := by
    by_contra hnone
    push_neg at hnone
    apply hnotConnected
    intro first second
    exact (Relation.ReflTransGen.symmetric hadjacentSymmetric (hnone first)).trans (hnone second)
  obtain ⟨target, htarget⟩ := htarget
  let componentScore : ℝ → ScoreVector Alternative := fun shift alternative =>
    if dataset.connectedTo alternative target then shift else 0
  have hcomponentLikelihood : ∀ shift : ℝ,
      pairwiseLogLikelihood dataset link (componentScore shift) =
        pairwiseLogLikelihood dataset link 0 := by
    intro shift
    unfold pairwiseLogLikelihood
    apply Finset.sum_congr rfl
    rintro ⟨first, second⟩ hpair
    by_cases hcount : dataset.count first second = 0
    · simp [hcount]
    have hedge : dataset.edge first second := Nat.pos_of_ne_zero hcount
    have hconnected : dataset.connectedTo first target ↔ dataset.connectedTo second target := by
      have hfirstSecond : dataset.connectedTo first second :=
        Relation.ReflTransGen.single (Or.inl hedge)
      have hsecondFirst : dataset.connectedTo second first :=
        Relation.ReflTransGen.symmetric hadjacentSymmetric hfirstSecond
      constructor
      · intro hfirst
        exact hsecondFirst.trans hfirst
      · intro hsecond
        exact hfirstSecond.trans hsecond
    by_cases hfirst : dataset.connectedTo first target
    · have hsecond : dataset.connectedTo second target := hconnected.mp hfirst
      simp [componentScore, hfirst, hsecond, randomUtilityWinProbability]
    · have hsecond : ¬ dataset.connectedTo second target := by
        intro hsecond
        exact hfirst (hconnected.mpr hsecond)
      simp [componentScore, hfirst, hsecond, randomUtilityWinProbability]
  intro hstrict
  have hzero : isReferenceNormalized reference (0 : ScoreVector Alternative) := by
    rfl
  have hone : isReferenceNormalized reference (componentScore 1) := by
    dsimp [isReferenceNormalized, componentScore]
    simp [htarget]
  have hne : (0 : ScoreVector Alternative) ≠ componentScore 1 := by
    intro heq
    have hcoordinate := congrFun heq target
    have htargetSelf : dataset.connectedTo target target := Relation.ReflTransGen.refl
    simp [componentScore, htargetSelf] at hcoordinate
  have hmidpoint :
      ((1 / 2 : ℝ) • (0 : ScoreVector Alternative) +
          (1 / 2 : ℝ) • componentScore 1) = componentScore (1 / 2 : ℝ) := by
    funext alternative
    by_cases hcomponent : dataset.connectedTo alternative target <;>
      simp [componentScore, hcomponent]
  have hstrictInequality := hstrict.2 hzero hone hne
    (show 0 < (1 / 2 : ℝ) by norm_num)
    (show 0 < (1 / 2 : ℝ) by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  rw [hmidpoint, hcomponentLikelihood 1, hcomponentLikelihood (1 / 2 : ℝ)] at hstrictInequality
  norm_num at hstrictInequality
  linarith

/--
Source Lemma 2.4's strict-concavity characterization, for the finite
fixed-reference likelihood model.
-/
theorem pairwiseLogLikelihood_strictConcaveOn_iff_isConnected
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : ℝ → ℝ)
    (hlogStrict : StrictConcaveOn ℝ Set.univ (fun gap => Real.log (link gap)))
    (reference : Alternative) :
    StrictConcaveOn ℝ {score : ScoreVector Alternative | isReferenceNormalized reference score}
      (pairwiseLogLikelihood dataset link) ↔ dataset.isConnected := by
  constructor
  · intro hstrict
    by_contra hnotConnected
    exact not_pairwiseLogLikelihood_strictConcaveOn_of_not_isConnected dataset link reference
      hnotConnected hstrict
  · exact pairwiseLogLikelihood_strictConcaveOn_of_isConnected dataset link hlogStrict reference

/-- Under the connected strict-concavity condition, any fixed-reference MLE is unique. -/
theorem isPairwiseMLE_unique_of_isConnected
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : ℝ → ℝ)
    (hlogStrict : StrictConcaveOn ℝ Set.univ (fun gap => Real.log (link gap)))
    (reference : Alternative) (hconnected : dataset.isConnected)
    (score : ScoreVector Alternative) (hmle : isPairwiseMLE dataset link reference score)
    (other : ScoreVector Alternative) (hother : isPairwiseMLE dataset link reference other) :
    other = score := by
  exact (pairwiseLogLikelihood_strictConcaveOn_of_isConnected dataset link hlogStrict reference
    hconnected).eq_of_isMaxOn hother.2 hmle.2 hother.1 hmle.1

/--
The diminishing-increment form of the source's pairwise likelihood concavity:
after a nonnegative gap displacement, the gain from another nonnegative
displacement cannot increase.
-/
theorem pairwiseLogTermAtGap_increment_diminishes
    {Alternative : Type*} (dataset : PairwiseCountDataset Alternative)
    (link : ℝ → ℝ) (first second : Alternative)
    (hlogConcave : ConcaveOn ℝ Set.univ (fun gap => Real.log (link gap)))
    {base shiftLeft shiftRight : ℝ}
    (hshiftLeft : 0 ≤ shiftLeft) (hshiftRight : 0 ≤ shiftRight) :
    pairwiseLogTermAtGap dataset link first second (base + shiftLeft + shiftRight) +
        pairwiseLogTermAtGap dataset link first second base ≤
      pairwiseLogTermAtGap dataset link first second (base + shiftLeft) +
        pairwiseLogTermAtGap dataset link first second (base + shiftRight) :=
  concave_increment_diminishes _
    (pairwiseLogTermAtGap_concaveOn dataset link first second hlogConcave)
    hshiftLeft hshiftRight

/--
The finite-family form of the Supplement-D diminishing-increment step. It
sums the exact `ℓ_xy` comparison over any finite collection of ordered pairs;
the `U × V` cross-pair collection in the source is one such instance.
-/
theorem finset_sum_pairwiseLogTermAtGap_increment_diminishes
    {Alternative Index : Type*} (dataset : PairwiseCountDataset Alternative)
    (link : ℝ → ℝ) (indices : Finset Index) (pairs : Index → Alternative × Alternative)
    (hlogConcave : ConcaveOn ℝ Set.univ (fun gap => Real.log (link gap)))
    (base shiftLeft shiftRight : Index → ℝ)
    (hshiftLeft : ∀ index ∈ indices, 0 ≤ shiftLeft index)
    (hshiftRight : ∀ index ∈ indices, 0 ≤ shiftRight index) :
    (∑ index ∈ indices,
      (pairwiseLogTermAtGap dataset link (pairs index).1 (pairs index).2
        (base index + shiftLeft index + shiftRight index) -
        pairwiseLogTermAtGap dataset link (pairs index).1 (pairs index).2
          (base index + shiftLeft index))) ≤
      ∑ index ∈ indices,
        (pairwiseLogTermAtGap dataset link (pairs index).1 (pairs index).2
          (base index + shiftRight index) -
          pairwiseLogTermAtGap dataset link (pairs index).1 (pairs index).2
            (base index)) := by
  apply finset_sum_increment_diminishes indices
    (fun index => pairwiseLogTermAtGap dataset link (pairs index).1 (pairs index).2)
  · intro index _
    exact pairwiseLogTermAtGap_concaveOn dataset link (pairs index).1 (pairs index).2
      hlogConcave
  · exact hshiftLeft
  · exact hshiftRight

/--
The `U × V` cross-pair comparison in Supplement D of
Noothigattu--Peters--Procaccia (2020). Shifting the `U` scores down and the
`V` scores up cannot increase the total gain from the `V` shift: each
two-directed likelihood term is concave in its `V - U` score gap. This is the
finite summed inequality used immediately after the source's Eq. (8).
-/
theorem crossPairwiseLogTermAtGap_increment_diminishes
    {Alternative : Type*} [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : ℝ → ℝ)
    (left right : Finset Alternative)
    (hlogConcave : ConcaveOn ℝ Set.univ (fun gap => Real.log (link gap)))
    (baseline leftShift rightShift : Alternative → ℝ)
    (hleftShift : ∀ leftAlternative ∈ left, 0 ≤ leftShift leftAlternative)
    (hrightShift : ∀ rightAlternative ∈ right, 0 ≤ rightShift rightAlternative) :
    (∑ leftAlternative ∈ left, ∑ rightAlternative ∈ right,
      (pairwiseLogTermAtGap dataset link rightAlternative leftAlternative
          (baseline rightAlternative - baseline leftAlternative +
            leftShift leftAlternative + rightShift rightAlternative) -
        pairwiseLogTermAtGap dataset link rightAlternative leftAlternative
          (baseline rightAlternative - baseline leftAlternative +
            leftShift leftAlternative))) ≤
      ∑ leftAlternative ∈ left, ∑ rightAlternative ∈ right,
        (pairwiseLogTermAtGap dataset link rightAlternative leftAlternative
            (baseline rightAlternative - baseline leftAlternative +
              rightShift rightAlternative) -
          pairwiseLogTermAtGap dataset link rightAlternative leftAlternative
            (baseline rightAlternative - baseline leftAlternative)) := by
  classical
  let indices : Finset (Alternative × Alternative) := left ×ˢ right
  let pairs : Alternative × Alternative → Alternative × Alternative := fun pair => (pair.2, pair.1)
  let base : Alternative × Alternative → ℝ :=
    fun pair => baseline pair.2 - baseline pair.1
  let shiftLeft : Alternative × Alternative → ℝ := fun pair => leftShift pair.1
  let shiftRight : Alternative × Alternative → ℝ := fun pair => rightShift pair.2
  have hleft : ∀ index ∈ indices, 0 ≤ shiftLeft index := by
    rintro ⟨leftAlternative, rightAlternative⟩ hindex
    exact hleftShift leftAlternative (Finset.mem_product.mp hindex).1
  have hright : ∀ index ∈ indices, 0 ≤ shiftRight index := by
    rintro ⟨leftAlternative, rightAlternative⟩ hindex
    exact hrightShift rightAlternative (Finset.mem_product.mp hindex).2
  have hsum := finset_sum_pairwiseLogTermAtGap_increment_diminishes
    dataset link indices pairs hlogConcave base shiftLeft shiftRight hleft hright
  simpa only [indices, pairs, base, shiftLeft, shiftRight, Finset.sum_product] using hsum

/--
The source's Eq. (8) comparison, stated directly for finite ordered-pair
likelihood sums. If the left block moves weakly down and the right block moves
weakly up from `baseline`, concavity bounds the cross-block gain at the fully
updated score by the cross-block gain with only the right block updated.
-/
theorem crossPairwiseLogLikelihood_increment_diminishes
    {Alternative : Type*} [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (left right : Finset Alternative) (hdisjoint : Disjoint left right)
    (hlogConcave : ConcaveOn ℝ Set.univ (fun gap => Real.log (link gap)))
    (baseline updated leftShift rightShift : ScoreVector Alternative)
    (hleftScore : ∀ leftAlternative ∈ left,
      updated leftAlternative = baseline leftAlternative - leftShift leftAlternative)
    (hrightScore : ∀ rightAlternative ∈ right,
      updated rightAlternative = baseline rightAlternative + rightShift rightAlternative)
    (hleftShift : ∀ leftAlternative ∈ left, 0 ≤ leftShift leftAlternative)
    (hrightShift : ∀ rightAlternative ∈ right, 0 ≤ rightShift rightAlternative) :
    (∑ pair ∈ crossPairIndices left right,
      pairwiseLogLikelihoodSummand dataset link updated pair) -
      (∑ pair ∈ crossPairIndices left right,
        pairwiseLogLikelihoodSummand dataset link
          (scorePaste left updated baseline) pair) ≤
      (∑ pair ∈ crossPairIndices left right,
        pairwiseLogLikelihoodSummand dataset link
          (scorePaste left baseline updated) pair) -
        ∑ pair ∈ crossPairIndices left right,
          pairwiseLogLikelihoodSummand dataset link baseline pair := by
  have hrightNotLeft : ∀ rightAlternative ∈ right, rightAlternative ∉ left := by
    intro rightAlternative hright hleft
    exact Finset.disjoint_left.1 hdisjoint hleft hright
  have hupdated :
      (∑ pair ∈ crossPairIndices left right,
        pairwiseLogLikelihoodSummand dataset link updated pair) =
        ∑ leftAlternative ∈ left, ∑ rightAlternative ∈ right,
          pairwiseLogTermAtGap dataset link rightAlternative leftAlternative
            (baseline rightAlternative - baseline leftAlternative +
              leftShift leftAlternative + rightShift rightAlternative) := by
    rw [sum_crossPairIndices_pairwiseLogLikelihoodSummand dataset link updated left right
      hdisjoint]
    apply Finset.sum_congr rfl
    intro leftAlternative hleft
    apply Finset.sum_congr rfl
    intro rightAlternative hright
    calc
      pairwiseLogTerm dataset link updated rightAlternative leftAlternative =
          pairwiseLogTermAtGap dataset link rightAlternative leftAlternative
            (updated rightAlternative - updated leftAlternative) :=
        pairwiseLogTerm_eq_atGap dataset link updated rightAlternative leftAlternative
      _ = pairwiseLogTermAtGap dataset link rightAlternative leftAlternative
            (baseline rightAlternative - baseline leftAlternative +
              leftShift leftAlternative + rightShift rightAlternative) := by
        rw [hrightScore rightAlternative hright, hleftScore leftAlternative hleft]
        ring_nf
  have hupdatedLeft :
      (∑ pair ∈ crossPairIndices left right,
        pairwiseLogLikelihoodSummand dataset link
          (scorePaste left updated baseline) pair) =
        ∑ leftAlternative ∈ left, ∑ rightAlternative ∈ right,
          pairwiseLogTermAtGap dataset link rightAlternative leftAlternative
            (baseline rightAlternative - baseline leftAlternative + leftShift leftAlternative) := by
    rw [sum_crossPairIndices_pairwiseLogLikelihoodSummand dataset link
      (scorePaste left updated baseline) left right hdisjoint]
    apply Finset.sum_congr rfl
    intro leftAlternative hleft
    apply Finset.sum_congr rfl
    intro rightAlternative hright
    calc
      pairwiseLogTerm dataset link (scorePaste left updated baseline)
          rightAlternative leftAlternative =
          pairwiseLogTermAtGap dataset link rightAlternative leftAlternative
            (scorePaste left updated baseline rightAlternative -
              scorePaste left updated baseline leftAlternative) :=
        pairwiseLogTerm_eq_atGap dataset link (scorePaste left updated baseline)
          rightAlternative leftAlternative
      _ = pairwiseLogTermAtGap dataset link rightAlternative leftAlternative
            (baseline rightAlternative - baseline leftAlternative + leftShift leftAlternative) := by
        rw [scorePaste_apply_of_not_mem left updated baseline
              (hrightNotLeft rightAlternative hright),
          scorePaste_apply_of_mem left updated baseline hleft,
          hleftScore leftAlternative hleft]
        ring_nf
  have hupdatedRight :
      (∑ pair ∈ crossPairIndices left right,
        pairwiseLogLikelihoodSummand dataset link
          (scorePaste left baseline updated) pair) =
        ∑ leftAlternative ∈ left, ∑ rightAlternative ∈ right,
          pairwiseLogTermAtGap dataset link rightAlternative leftAlternative
            (baseline rightAlternative - baseline leftAlternative + rightShift rightAlternative) := by
    rw [sum_crossPairIndices_pairwiseLogLikelihoodSummand dataset link
      (scorePaste left baseline updated) left right hdisjoint]
    apply Finset.sum_congr rfl
    intro leftAlternative hleft
    apply Finset.sum_congr rfl
    intro rightAlternative hright
    calc
      pairwiseLogTerm dataset link (scorePaste left baseline updated)
          rightAlternative leftAlternative =
          pairwiseLogTermAtGap dataset link rightAlternative leftAlternative
            (scorePaste left baseline updated rightAlternative -
              scorePaste left baseline updated leftAlternative) :=
        pairwiseLogTerm_eq_atGap dataset link (scorePaste left baseline updated)
          rightAlternative leftAlternative
      _ = pairwiseLogTermAtGap dataset link rightAlternative leftAlternative
            (baseline rightAlternative - baseline leftAlternative + rightShift rightAlternative) := by
        rw [scorePaste_apply_of_not_mem left baseline updated
              (hrightNotLeft rightAlternative hright),
          scorePaste_apply_of_mem left baseline updated hleft,
          hrightScore rightAlternative hright]
        ring_nf
  have hbaseline :
      (∑ pair ∈ crossPairIndices left right,
        pairwiseLogLikelihoodSummand dataset link baseline pair) =
        ∑ leftAlternative ∈ left, ∑ rightAlternative ∈ right,
          pairwiseLogTermAtGap dataset link rightAlternative leftAlternative
            (baseline rightAlternative - baseline leftAlternative) := by
    rw [sum_crossPairIndices_pairwiseLogLikelihoodSummand dataset link baseline left right
      hdisjoint]
    apply Finset.sum_congr rfl
    intro leftAlternative hleft
    apply Finset.sum_congr rfl
    intro rightAlternative hright
    exact pairwiseLogTerm_eq_atGap dataset link baseline rightAlternative leftAlternative
  rw [hupdated, hupdatedLeft, hupdatedRight, hbaseline]
  simpa only [Finset.sum_sub_distrib] using
    (crossPairwiseLogTermAtGap_increment_diminishes dataset link left right hlogConcave
      baseline leftShift rightShift hleftShift hrightShift)

/--
The finite block-exchange implication in Supplement D. If replacing the right
block of a baseline score vector by its updated values strictly lowers the
baseline likelihood, then log-concavity forces the converse mixed replacement
to have strictly higher likelihood than the fully updated vector. The source
uses this conclusion to contradict updated-MLE maximality when `V` is nonempty.
-/
theorem pairwiseLogLikelihood_block_exchange_lt
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (left right : Finset Alternative)
    (hcover : left ∪ right = Finset.univ) (hdisjoint : Disjoint left right)
    (hlogConcave : ConcaveOn ℝ Set.univ (fun gap => Real.log (link gap)))
    (baseline updated leftShift rightShift : ScoreVector Alternative)
    (hleftScore : ∀ leftAlternative ∈ left,
      updated leftAlternative = baseline leftAlternative - leftShift leftAlternative)
    (hrightScore : ∀ rightAlternative ∈ right,
      updated rightAlternative = baseline rightAlternative + rightShift rightAlternative)
    (hleftShift : ∀ leftAlternative ∈ left, 0 ≤ leftShift leftAlternative)
    (hrightShift : ∀ rightAlternative ∈ right, 0 ≤ rightShift rightAlternative)
    (hbaselineMixed :
      pairwiseLogLikelihood dataset link (scorePaste left baseline updated) <
        pairwiseLogLikelihood dataset link baseline) :
    pairwiseLogLikelihood dataset link updated <
      pairwiseLogLikelihood dataset link (scorePaste left updated baseline) := by
  have hrightNotLeft : ∀ rightAlternative ∈ right, rightAlternative ∉ left := by
    intro rightAlternative hright hleft
    exact Finset.disjoint_left.1 hdisjoint hleft hright
  have hleftUpdated : ∀ leftAlternative ∈ left,
      updated leftAlternative = scorePaste left updated baseline leftAlternative := by
    intro leftAlternative hleft
    exact (scorePaste_apply_of_mem left updated baseline hleft).symm
  have hrightBaseline : ∀ rightAlternative ∈ right,
      baseline rightAlternative = scorePaste left updated baseline rightAlternative := by
    intro rightAlternative hright
    exact (scorePaste_apply_of_not_mem left updated baseline
      (hrightNotLeft rightAlternative hright)).symm
  have hleftBaseline : ∀ leftAlternative ∈ left,
      baseline leftAlternative = scorePaste left baseline updated leftAlternative := by
    intro leftAlternative hleft
    exact (scorePaste_apply_of_mem left baseline updated hleft).symm
  have hrightUpdated : ∀ rightAlternative ∈ right,
      updated rightAlternative = scorePaste left baseline updated rightAlternative := by
    intro rightAlternative hright
    exact (scorePaste_apply_of_not_mem left baseline updated
      (hrightNotLeft rightAlternative hright)).symm
  have hleftUpdatedBlock := sum_pairwiseLogLikelihoodSummand_eq_of_score_agree
    dataset link updated (scorePaste left updated baseline) left left hleftUpdated hleftUpdated
  have hrightBaselineBlock := sum_pairwiseLogLikelihoodSummand_eq_of_score_agree
    dataset link baseline (scorePaste left updated baseline) right right hrightBaseline hrightBaseline
  have hleftBaselineBlock := sum_pairwiseLogLikelihoodSummand_eq_of_score_agree
    dataset link baseline (scorePaste left baseline updated) left left hleftBaseline hleftBaseline
  have hrightUpdatedBlock := sum_pairwiseLogLikelihoodSummand_eq_of_score_agree
    dataset link updated (scorePaste left baseline updated) right right hrightUpdated hrightUpdated
  have hupdatedBlocks :=
    pairwiseLogLikelihood_eq_block_sums dataset link updated left right hcover hdisjoint
  have hupdatedLeftBlocks := pairwiseLogLikelihood_eq_block_sums dataset link
    (scorePaste left updated baseline) left right hcover hdisjoint
  have hupdatedRightBlocks := pairwiseLogLikelihood_eq_block_sums dataset link
    (scorePaste left baseline updated) left right hcover hdisjoint
  have hbaselineBlocks :=
    pairwiseLogLikelihood_eq_block_sums dataset link baseline left right hcover hdisjoint
  have hcross := crossPairwiseLogLikelihood_increment_diminishes dataset link left right
    hdisjoint hlogConcave baseline updated leftShift rightShift hleftScore hrightScore
    hleftShift hrightShift
  have hdelta :
      pairwiseLogLikelihood dataset link updated -
          pairwiseLogLikelihood dataset link (scorePaste left updated baseline) ≤
        pairwiseLogLikelihood dataset link (scorePaste left baseline updated) -
          pairwiseLogLikelihood dataset link baseline := by
    rw [hupdatedBlocks, hupdatedLeftBlocks, hupdatedRightBlocks, hbaselineBlocks,
      hleftUpdatedBlock, hrightBaselineBlock, hleftBaselineBlock, hrightUpdatedBlock]
    linarith
  linarith

/-- The four likelihood terms coupling a third alternative to a swapped pair. -/
noncomputable def otherPairwiseLogLikelihoodContribution
    {Alternative : Type*} (dataset : PairwiseCountDataset Alternative)
    (link : ℝ → ℝ) (score : ScoreVector Alternative)
    (first second other : Alternative) : ℝ :=
  pairwiseLogLikelihoodSummand dataset link score (first, other) +
    pairwiseLogLikelihoodSummand dataset link score (second, other) +
      pairwiseLogLikelihoodSummand dataset link score (other, first) +
        pairwiseLogLikelihoodSummand dataset link score (other, second)

/-- The packaged third-alternative contribution strictly improves under a Pareto score swap. -/
theorem otherPairwiseLogLikelihoodContribution_scoreSwap_strict
    {Alternative : Type*} [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (score : ScoreVector Alternative) {first second other : Alternative}
    (hscore : score first < score second)
    (hcount_out : dataset.count second other < dataset.count first other)
    (hcount_in : dataset.count other first < dataset.count other second)
    (hother_first : other ≠ first) (hother_second : other ≠ second)
    (hstrict : StrictMono (link : ℝ → ℝ)) :
    otherPairwiseLogLikelihoodContribution dataset link score first second other <
      otherPairwiseLogLikelihoodContribution dataset link (scoreSwap score first second)
        first second other := by
  simpa [otherPairwiseLogLikelihoodContribution, pairwiseLogLikelihoodSummand,
    add_assoc] using
    (otherPairwiseLogTerms_scoreSwap_strict dataset link score hscore hcount_out hcount_in
      hother_first hother_second hstrict)

/--
Partition the finite likelihood into the direct pair, the four terms attached
to each third alternative, and the part disjoint from both alternatives. This
is the exact finite bookkeeping step in the Supplement-C Pareto proof.
-/
theorem pairwiseLogLikelihood_eq_direct_add_other_add_unrelated
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (score : ScoreVector Alternative) {first second : Alternative} (hne : first ≠ second) :
    pairwiseLogLikelihood dataset link score =
      pairwiseLogTerm dataset link score first second +
        (∑ other ∈ otherAlternatives first second,
          otherPairwiseLogLikelihoodContribution dataset link score first second other) +
        ∑ left ∈ otherAlternatives first second, ∑ right ∈ otherAlternatives first second,
          pairwiseLogLikelihoodSummand dataset link score (left, right) := by
  rw [pairwiseLogLikelihood_eq_sum_univ_product]
  have hfirst_row := sum_univ_eq_two_add_others
    (fun right => pairwiseLogLikelihoodSummand dataset link score (first, right)) hne
  have hsecond_row := sum_univ_eq_two_add_others
    (fun right => pairwiseLogLikelihoodSummand dataset link score (second, right)) hne
  have hother_rows :
      (∑ left ∈ otherAlternatives first second, ∑ right : Alternative,
        pairwiseLogLikelihoodSummand dataset link score (left, right)) =
        ∑ left ∈ otherAlternatives first second,
          (pairwiseLogLikelihoodSummand dataset link score (left, first) +
            pairwiseLogLikelihoodSummand dataset link score (left, second) +
              ∑ right ∈ otherAlternatives first second,
                pairwiseLogLikelihoodSummand dataset link score (left, right)) := by
    refine Finset.sum_congr rfl ?_
    intro left hleft
    exact sum_univ_eq_two_add_others
      (fun right => pairwiseLogLikelihoodSummand dataset link score (left, right)) hne
  rw [sum_univ_eq_two_add_others
    (fun left => ∑ right : Alternative,
      pairwiseLogLikelihoodSummand dataset link score (left, right)) hne,
    hfirst_row, hsecond_row, hother_rows]
  dsimp only
  have hfirst_diag : pairwiseLogLikelihoodSummand dataset link score (first, first) = 0 := by
    simp [pairwiseLogLikelihoodSummand, dataset.diagonal_zero]
  have hsecond_diag : pairwiseLogLikelihoodSummand dataset link score (second, second) = 0 := by
    simp [pairwiseLogLikelihoodSummand, dataset.diagonal_zero]
  rw [hfirst_diag, hsecond_diag]
  have hdirect : pairwiseLogTerm dataset link score first second =
      pairwiseLogLikelihoodSummand dataset link score (first, second) +
        pairwiseLogLikelihoodSummand dataset link score (second, first) := rfl
  rw [hdirect]
  unfold otherPairwiseLogLikelihoodContribution
  simp only [Finset.sum_add_distrib]
  ring

/--
If the source's Definition-3.1 count inequalities hold while an MLE ranks the
two alternatives in the opposite strict order, swapping their scores strictly
increases the complete finite likelihood.
-/
theorem pairwiseLogLikelihood_scoreSwap_lt_of_hasParetoCountDominance
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (score : ScoreVector Alternative) {first second : Alternative}
    (hscore : score first < score second)
    (hpareto : dataset.hasParetoCountDominance first second)
    (hstrict : StrictMono (link : ℝ → ℝ)) :
    pairwiseLogLikelihood dataset link score <
      pairwiseLogLikelihood dataset link (scoreSwap score first second) := by
  have hne : first ≠ second := dataset.hasParetoCountDominance_ne hpareto
  have houtside : ∀ alternative, alternative ∈ otherAlternatives first second →
      alternative ≠ first ∧ alternative ≠ second := by
    intro alternative hmember
    have hmember' : alternative ≠ second ∧ alternative ≠ first := by
      simpa [otherAlternatives] using hmember
    exact ⟨hmember'.2, hmember'.1⟩
  have hdirect : pairwiseLogTerm dataset link score first second <
      pairwiseLogTerm dataset link (scoreSwap score first second) first second :=
    directPairwiseLogTerms_scoreSwap_strict dataset link score hscore hpareto.1 hstrict
  have hother_le :
      (∑ other ∈ otherAlternatives first second,
        otherPairwiseLogLikelihoodContribution dataset link score first second other) ≤
        ∑ other ∈ otherAlternatives first second,
          otherPairwiseLogLikelihoodContribution dataset link
            (scoreSwap score first second) first second other := by
    refine Finset.sum_le_sum ?_
    intro other hother
    rcases houtside other hother with ⟨hother_first, hother_second⟩
    exact (otherPairwiseLogLikelihoodContribution_scoreSwap_strict dataset link score hscore
      (hpareto.2 other hother_first hother_second).1
      (hpareto.2 other hother_first hother_second).2 hother_first hother_second hstrict).le
  have hunrelated :
      (∑ left ∈ otherAlternatives first second, ∑ right ∈ otherAlternatives first second,
        pairwiseLogLikelihoodSummand dataset link (scoreSwap score first second) (left, right)) =
        ∑ left ∈ otherAlternatives first second, ∑ right ∈ otherAlternatives first second,
          pairwiseLogLikelihoodSummand dataset link score (left, right) := by
    refine Finset.sum_congr rfl ?_
    intro left hleft
    refine Finset.sum_congr rfl ?_
    intro right hright
    rcases houtside left hleft with ⟨hleft_first, hleft_second⟩
    rcases houtside right hright with ⟨hright_first, hright_second⟩
    exact pairwiseLogLikelihoodSummand_scoreSwap_eq_of_outside dataset link score
      first second left right hleft_first hleft_second hright_first hright_second
  rw [pairwiseLogLikelihood_eq_direct_add_other_add_unrelated dataset link score hne,
    pairwiseLogLikelihood_eq_direct_add_other_add_unrelated dataset link
      (scoreSwap score first second) hne,
    hunrelated]
  linarith [add_lt_add_of_lt_of_le hdirect hother_le]

/--
Source Theorem 3.2's likelihood argument: a finite pairwise MLE cannot rank a
strictly Pareto-count-dominant alternative below the dominated alternative.
-/
theorem isPairwiseMLE_pareto_score_order
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (reference : Alternative) (score : ScoreVector Alternative)
    {first second : Alternative}
    (hmle : isPairwiseMLE dataset link reference score)
    (hpareto : dataset.hasParetoCountDominance first second)
    (hstrict : StrictMono (link : ℝ → ℝ)) :
    score second ≤ score first := by
  by_contra hnot
  have hscore : score first < score second := lt_of_not_ge hnot
  have hswap_lt := pairwiseLogLikelihood_scoreSwap_lt_of_hasParetoCountDominance
    dataset link score hscore hpareto hstrict
  have hmax := isPairwiseMLE_global_max dataset link reference score hmle
    (scoreSwap score first second)
  linarith

/--
The first comparison in Supplement D's proof of Theorem 4.2. Adding a positive
number of `winner ≻ loser` observations cannot make the fixed-reference MLE
raise `loser` relative to `winner`. This local result needs only strict
monotonicity; the source's global monotonicity theorem additionally needs its
strict-log-concavity argument for every third alternative.
-/
theorem isPairwiseMLE_loser_relative_score_le_after_addDirectedCount
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (reference winner loser : Alternative) (added : ℕ) (hwinner_loser : winner ≠ loser)
    (hadded : 0 < added) (hstrict : StrictMono (link : ℝ → ℝ))
    (baselineScore updatedScore : ScoreVector Alternative)
    (hbaseline : isPairwiseMLE dataset link reference baselineScore)
    (hupdated : isPairwiseMLE
      (dataset.addDirectedCount winner loser added hwinner_loser) link reference updatedScore) :
    updatedScore loser - updatedScore winner ≤ baselineScore loser - baselineScore winner := by
  by_contra hnot
  have hscore : baselineScore loser - baselineScore winner <
      updatedScore loser - updatedScore winner := lt_of_not_ge hnot
  have hgap : updatedScore winner - updatedScore loser <
      baselineScore winner - baselineScore loser := by
    linarith
  have hprob :
      randomUtilityWinProbability link updatedScore winner loser <
        randomUtilityWinProbability link baselineScore winner loser := by
    unfold randomUtilityWinProbability
    exact hstrict hgap
  have hprob_pos :
      0 < randomUtilityWinProbability link updatedScore winner loser :=
    (link.openProbability hstrict _).1
  have hlog :
      Real.log (randomUtilityWinProbability link updatedScore winner loser) <
        Real.log (randomUtilityWinProbability link baselineScore winner loser) :=
    Real.strictMonoOn_log hprob_pos (lt_trans hprob_pos hprob) hprob
  have hadded_real : 0 < (added : ℝ) := by exact_mod_cast hadded
  have hadded_term :
      (added : ℝ) *
          Real.log (randomUtilityWinProbability link updatedScore winner loser) <
        (added : ℝ) *
          Real.log (randomUtilityWinProbability link baselineScore winner loser) :=
    mul_lt_mul_of_pos_left hlog hadded_real
  have hbaseline_max := isPairwiseMLE_global_max dataset link reference baselineScore
    hbaseline updatedScore
  have hlikelihood_lt :
      pairwiseLogLikelihood
          (dataset.addDirectedCount winner loser added hwinner_loser) link updatedScore <
        pairwiseLogLikelihood
          (dataset.addDirectedCount winner loser added hwinner_loser) link baselineScore := by
    rw [pairwiseLogLikelihood_addDirectedCount,
      pairwiseLogLikelihood_addDirectedCount]
    linarith
  have hupdated_max := isPairwiseMLE_global_max
    (dataset.addDirectedCount winner loser added hwinner_loser) link reference updatedScore
    hupdated baselineScore
  linarith

/--
The first `b ∈ U` conclusion of Supplement D in Definition-4.1 form. The
abstract source premise that exactly one directed count increased is converted
to its exact finite `addDirectedCount` realization before applying the local
likelihood argument.
-/
theorem isPairwiseMLE_loser_relative_score_le_of_hasSinglePairCountIncrease
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (baseline updated : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (reference winner loser : Alternative)
    (hincrease : hasSinglePairCountIncrease baseline updated winner loser)
    (hstrict : StrictMono (link : ℝ → ℝ))
    (baselineScore updatedScore : ScoreVector Alternative)
    (hbaseline : isPairwiseMLE baseline link reference baselineScore)
    (hupdated : isPairwiseMLE updated link reference updatedScore) :
    updatedScore loser - updatedScore winner ≤ baselineScore loser - baselineScore winner := by
  let hwinner_loser : winner ≠ loser :=
    hasSinglePairCountIncrease_ne baseline updated hincrease
  obtain ⟨added, hadded, hupdate⟩ :=
    exists_addDirectedCount_eq_of_hasSinglePairCountIncrease baseline updated winner loser hincrease
  rw [hupdate] at hupdated
  simpa only using isPairwiseMLE_loser_relative_score_le_after_addDirectedCount
    baseline link reference winner loser added hwinner_loser hadded hstrict
    baselineScore updatedScore hbaseline hupdated

/--
The winner half of source Theorem 4.2. Under strict monotonicity and
log-concavity, increasing exactly the `winner ≻ loser` count cannot decrease
the winner's score relative to any alternative. The proof follows Supplement D:
partition alternatives by their normalized score movement, obtain a strict
baseline-MLE comparison from uniqueness, apply the finite block-exchange
inequality, and then contradict updated-MLE maximality.
-/
theorem isPairwiseMLE_winner_relative_score_le_of_hasSinglePairCountIncrease
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (baseline updated : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (reference winner loser : Alternative)
    (hincrease : hasSinglePairCountIncrease baseline updated winner loser)
    (hstrict : StrictMono (link : ℝ → ℝ))
    (hlogConcave : ConcaveOn ℝ Set.univ (fun gap => Real.log (link gap)))
    (baselineScore updatedScore : ScoreVector Alternative)
    (hbaselineUnique : hasUniquePairwiseMLE baseline link reference)
    (hbaseline : isPairwiseMLE baseline link reference baselineScore)
    (hupdated : isPairwiseMLE updated link reference updatedScore) :
    ∀ other,
      baselineScore winner - baselineScore other ≤
        updatedScore winner - updatedScore other := by
  let baselineRelative : ScoreVector Alternative :=
    fun alternative => baselineScore alternative - baselineScore winner
  let updatedRelative : ScoreVector Alternative :=
    fun alternative => updatedScore alternative - updatedScore winner
  let leftBlock : Finset Alternative :=
    (Finset.univ : Finset Alternative).filter
      (fun alternative => updatedRelative alternative ≤ baselineRelative alternative)
  let rightBlock : Finset Alternative :=
    (Finset.univ : Finset Alternative).filter
      (fun alternative => baselineRelative alternative < updatedRelative alternative)
  have hcover : leftBlock ∪ rightBlock = Finset.univ := by
    ext alternative
    simp [leftBlock, rightBlock, le_or_gt]
  have hdisjoint : Disjoint leftBlock rightBlock := by
    refine Finset.disjoint_left.2 ?_
    intro alternative hleft hright
    exact (not_lt_of_ge (Finset.mem_filter.mp hleft).2)
      (Finset.mem_filter.mp hright).2
  have hwinnerLeft : winner ∈ leftBlock := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simp [baselineRelative, updatedRelative]
  have hloserRelative :
      updatedScore loser - updatedScore winner ≤
        baselineScore loser - baselineScore winner :=
    isPairwiseMLE_loser_relative_score_le_of_hasSinglePairCountIncrease
      baseline updated link reference winner loser hincrease hstrict
      baselineScore updatedScore hbaseline hupdated
  have hloserLeft : loser ∈ leftBlock := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa [baselineRelative, updatedRelative] using hloserRelative
  have hleftInequality : ∀ alternative ∈ leftBlock,
      updatedRelative alternative ≤ baselineRelative alternative := by
    intro alternative hmem
    exact (Finset.mem_filter.mp hmem).2
  have hrightInequality : ∀ alternative ∈ rightBlock,
      baselineRelative alternative < updatedRelative alternative := by
    intro alternative hmem
    exact (Finset.mem_filter.mp hmem).2
  have hrightNotLeft : ∀ alternative ∈ rightBlock, alternative ∉ leftBlock := by
    intro alternative hright hleft
    exact Finset.disjoint_left.1 hdisjoint hleft hright
  let leftShift : ScoreVector Alternative :=
    fun alternative => baselineRelative alternative - updatedRelative alternative
  let rightShift : ScoreVector Alternative :=
    fun alternative => updatedRelative alternative - baselineRelative alternative
  have hleftScore : ∀ alternative ∈ leftBlock,
      updatedRelative alternative = baselineRelative alternative - leftShift alternative := by
    intro alternative _
    dsimp [leftShift]
    ring
  have hrightScore : ∀ alternative ∈ rightBlock,
      updatedRelative alternative = baselineRelative alternative + rightShift alternative := by
    intro alternative _
    dsimp [rightShift]
    ring
  have hleftShift : ∀ alternative ∈ leftBlock, 0 ≤ leftShift alternative := by
    intro alternative hmem
    dsimp [leftShift]
    linarith [hleftInequality alternative hmem]
  have hrightShift : ∀ alternative ∈ rightBlock, 0 ≤ rightShift alternative := by
    intro alternative hmem
    dsimp [rightShift]
    linarith [hrightInequality alternative hmem]
  rcases hbaselineUnique with ⟨uniqueScore, huniqueScore, hunique⟩
  have huniqueBaseline : ∀ candidate,
      isPairwiseMLE baseline link reference candidate → candidate = baselineScore := by
    intro candidate hcandidate
    exact (hunique candidate hcandidate).trans (hunique baselineScore hbaseline).symm
  have hbaselineShift :
      pairwiseLogLikelihood baseline link baselineRelative =
        pairwiseLogLikelihood baseline link baselineScore := by
    simpa [baselineRelative, sub_eq_add_neg] using
      (pairwiseLogLikelihood_shift baseline link baselineScore (-baselineScore winner))
  have hupdatedShift :
      pairwiseLogLikelihood updated link updatedRelative =
        pairwiseLogLikelihood updated link updatedScore := by
    simpa [updatedRelative, sub_eq_add_neg] using
      (pairwiseLogLikelihood_shift updated link updatedScore (-updatedScore winner))
  intro other
  have hresult : updatedRelative other ≤ baselineRelative other := by
    by_contra hnot
    have hright : other ∈ rightBlock := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, lt_of_not_ge hnot⟩
    have hcandidateDifference :
        scorePaste leftBlock baselineRelative updatedRelative other -
            scorePaste leftBlock baselineRelative updatedRelative winner ≠
          baselineScore other - baselineScore winner := by
      rw [scorePaste_apply_of_not_mem leftBlock baselineRelative updatedRelative
            (hrightNotLeft other hright),
        scorePaste_apply_of_mem leftBlock baselineRelative updatedRelative hwinnerLeft]
      have hbaselineWinner : baselineRelative winner = 0 := by
        simp [baselineRelative]
      have hbaselineGap : baselineScore other - baselineScore winner =
          baselineRelative other := by
        simp [baselineRelative]
      rw [hbaselineWinner, hbaselineGap]
      simpa using ne_of_gt (hrightInequality other hright)
    have hbaselineMixedRaw :
        pairwiseLogLikelihood baseline link
            (scorePaste leftBlock baselineRelative updatedRelative) <
          pairwiseLogLikelihood baseline link baselineScore :=
      isPairwiseMLE_strict_global_max_of_unique_of_score_sub_ne baseline link reference
        baselineScore hbaseline huniqueBaseline
        (scorePaste leftBlock baselineRelative updatedRelative) other winner hcandidateDifference
    have hbaselineMixed :
        pairwiseLogLikelihood baseline link
            (scorePaste leftBlock baselineRelative updatedRelative) <
          pairwiseLogLikelihood baseline link baselineRelative := by
      linarith
    have hblockExchange :
        pairwiseLogLikelihood baseline link updatedRelative <
          pairwiseLogLikelihood baseline link
            (scorePaste leftBlock updatedRelative baselineRelative) :=
      pairwiseLogLikelihood_block_exchange_lt baseline link leftBlock rightBlock hcover hdisjoint
        hlogConcave baselineRelative updatedRelative leftShift rightShift
        hleftScore hrightScore hleftShift hrightShift hbaselineMixed
    obtain ⟨added, hadded, hupdate⟩ :=
      exists_addDirectedCount_eq_of_hasSinglePairCountIncrease
        baseline updated winner loser hincrease
    have haddedGap :
        randomUtilityWinProbability link updatedRelative winner loser =
          randomUtilityWinProbability link
            (scorePaste leftBlock updatedRelative baselineRelative) winner loser := by
      unfold randomUtilityWinProbability
      rw [scorePaste_apply_of_mem leftBlock updatedRelative baselineRelative hwinnerLeft,
        scorePaste_apply_of_mem leftBlock updatedRelative baselineRelative hloserLeft]
    have hupdatedMixed :
        pairwiseLogLikelihood updated link updatedRelative <
          pairwiseLogLikelihood updated link
            (scorePaste leftBlock updatedRelative baselineRelative) := by
      rw [hupdate, pairwiseLogLikelihood_addDirectedCount,
        pairwiseLogLikelihood_addDirectedCount, haddedGap]
      linarith
    have hupdatedMax := isPairwiseMLE_global_max updated link reference updatedScore hupdated
      (scorePaste leftBlock updatedRelative baselineRelative)
    linarith
  dsimp [baselineRelative, updatedRelative] at hresult
  linarith

/--
The loser half of source Theorem 4.2. It follows from the winner half by
transposing directed counts and negating every score, which preserves the
finite likelihood while reversing the added comparison direction.
-/
theorem isPairwiseMLE_loser_relative_score_le_of_hasSinglePairCountIncrease_full
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (baseline updated : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (reference winner loser : Alternative)
    (hincrease : hasSinglePairCountIncrease baseline updated winner loser)
    (hstrict : StrictMono (link : ℝ → ℝ))
    (hlogConcave : ConcaveOn ℝ Set.univ (fun gap => Real.log (link gap)))
    (baselineScore updatedScore : ScoreVector Alternative)
    (hbaselineUnique : hasUniquePairwiseMLE baseline link reference)
    (hbaseline : isPairwiseMLE baseline link reference baselineScore)
    (hupdated : isPairwiseMLE updated link reference updatedScore) :
    ∀ other,
      updatedScore loser - updatedScore other ≤
        baselineScore loser - baselineScore other := by
  have htransposedIncrease :
      hasSinglePairCountIncrease (transpose baseline) (transpose updated) loser winner :=
    transpose_hasSinglePairCountIncrease baseline updated winner loser hincrease
  have htransposedBaseline :
      isPairwiseMLE (transpose baseline) link reference
        (fun alternative => -baselineScore alternative) :=
    isPairwiseMLE_transpose_neg baseline link reference baselineScore hbaseline
  have htransposedUpdated :
      isPairwiseMLE (transpose updated) link reference
        (fun alternative => -updatedScore alternative) :=
    isPairwiseMLE_transpose_neg updated link reference updatedScore hupdated
  have htransposedUnique :
      hasUniquePairwiseMLE (transpose baseline) link reference :=
    hasUniquePairwiseMLE_transpose_neg baseline link reference hbaselineUnique
  have hwinner := isPairwiseMLE_winner_relative_score_le_of_hasSinglePairCountIncrease
    (transpose baseline) (transpose updated) link reference loser winner
    htransposedIncrease hstrict hlogConcave
    (fun alternative => -baselineScore alternative)
    (fun alternative => -updatedScore alternative)
    htransposedUnique htransposedBaseline htransposedUpdated
  intro other
  have hresult := hwinner other
  dsimp at hresult
  linarith

/--
Source Theorem 4.2: a strictly monotone, log-concave pairwise link satisfies
Definition 4.1 monotonicity for every finite pairwise-count dataset whose
compared fixed-reference MLEs are unique.
-/
theorem pairwiseMLEMonotonicity_of_strictMono_logConcave
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (link : CDFLikePairwiseLink)
    (hstrict : StrictMono (link : ℝ → ℝ))
    (hlogConcave : ConcaveOn ℝ Set.univ (fun gap => Real.log (link gap))) :
    pairwiseMLEMonotonicity (Alternative := Alternative) link := by
  intro baseline updated reference winner loser hincrease hbaselineUnique _
    baselineScore updatedScore hbaseline hupdated other
  constructor
  · exact isPairwiseMLE_winner_relative_score_le_of_hasSinglePairCountIncrease
      baseline updated link reference winner loser hincrease hstrict hlogConcave
      baselineScore updatedScore hbaselineUnique hbaseline hupdated other
  · exact isPairwiseMLE_loser_relative_score_le_of_hasSinglePairCountIncrease_full
      baseline updated link reference winner loser hincrease hstrict hlogConcave
      baselineScore updatedScore hbaselineUnique hbaseline hupdated other

/--
The exact two-alternative special case of the source's monotonicity conclusion.
Once every alternative is one of the updated pair, the direct Supplement-D
comparison proves both required score-difference inequalities for every
alternative; no third-alternative concavity argument is needed.
-/
theorem isPairwiseMLE_monotone_after_addDirectedCount_of_pair_complete
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (reference winner loser : Alternative) (added : ℕ) (hwinner_loser : winner ≠ loser)
    (hadded : 0 < added) (hstrict : StrictMono (link : ℝ → ℝ))
    (baselineScore updatedScore : ScoreVector Alternative)
    (hbaseline : isPairwiseMLE dataset link reference baselineScore)
    (hupdated : isPairwiseMLE
      (dataset.addDirectedCount winner loser added hwinner_loser) link reference updatedScore)
    (hpairComplete : ∀ other : Alternative, other = winner ∨ other = loser) :
    ∀ other,
      baselineScore winner - baselineScore other ≤ updatedScore winner - updatedScore other ∧
        updatedScore loser - updatedScore other ≤ baselineScore loser - baselineScore other := by
  have hdirect := isPairwiseMLE_loser_relative_score_le_after_addDirectedCount
    dataset link reference winner loser added hwinner_loser hadded hstrict
    baselineScore updatedScore hbaseline hupdated
  intro other
  rcases hpairComplete other with rfl | rfl
  · constructor
    · norm_num
    · exact hdirect
  · constructor
    · linarith
    · norm_num

/-- The source link symmetry turns a directed pair term into a coin-flip likelihood. -/
theorem pairwiseLogTerm_eq_coinFlipLogLikelihood
    {Alternative : Type*} (dataset : PairwiseCountDataset Alternative)
    (link : CDFLikePairwiseLink) (score : ScoreVector Alternative)
    (first second : Alternative) :
    pairwiseLogTerm dataset link score first second =
      coinFlipLogLikelihood (dataset.count first second : ℝ)
        (dataset.count second first : ℝ)
        (randomUtilityWinProbability link score first second) := by
  unfold pairwiseLogTerm coinFlipLogLikelihood
  have hsum := randomUtilityWinProbability_add_swap link score first second
  have hswap : randomUtilityWinProbability link score second first =
      1 - randomUtilityWinProbability link score first second := by
    linarith
  rw [hswap]

/-- The gap form of a two-direction pair term is its positive-weight coin-flip likelihood. -/
theorem pairwiseLogTermAtGap_eq_coinFlipLogLikelihood
    {Alternative : Type*} (dataset : PairwiseCountDataset Alternative)
    (link : CDFLikePairwiseLink) (first second : Alternative) (gap : ℝ) :
    pairwiseLogTermAtGap dataset link first second gap =
      coinFlipLogLikelihood (dataset.count first second : ℝ)
        (dataset.count second first : ℝ) (link gap) := by
  unfold pairwiseLogTermAtGap coinFlipLogLikelihood
  have hcomplement : link (-gap) = 1 - link gap := by
    have := link.complementary gap
    linarith
  rw [hcomplement]

/--
If a score gap is strictly above its perfect-fit distance, decreasing it while
remaining strictly above that distance strictly improves the corresponding
two-direction pair likelihood.
-/
theorem pairwiseLogTermAtGap_lt_of_perfectFit_between
    {Alternative : Type*} (dataset : PairwiseCountDataset Alternative)
    (link : CDFLikePairwiseLink) (hstrict : StrictMono (link : ℝ → ℝ))
    (first second : Alternative) (perfectFit improvedGap currentGap : ℝ)
    (hforward : 0 < dataset.count first second)
    (hreverse : 0 < dataset.count second first)
    (hperfectFit : link perfectFit =
      (dataset.count first second : ℝ) /
        ((dataset.count first second : ℝ) + (dataset.count second first : ℝ)))
    (hperfectFitImproved : perfectFit < improvedGap)
    (himprovedCurrent : improvedGap < currentGap) :
    pairwiseLogTermAtGap dataset link first second currentGap <
      pairwiseLogTermAtGap dataset link first second improvedGap := by
  rw [pairwiseLogTermAtGap_eq_coinFlipLogLikelihood,
    pairwiseLogTermAtGap_eq_coinFlipLogLikelihood]
  have hforwardReal : 0 < (dataset.count first second : ℝ) := by
    exact_mod_cast hforward
  have hreverseReal : 0 < (dataset.count second first : ℝ) := by
    exact_mod_cast hreverse
  have himprovedProbability : link improvedGap ∈ Set.Ioo (0 : ℝ) 1 :=
    link.openProbability hstrict improvedGap
  have hcurrentProbability : link currentGap ∈ Set.Ioo (0 : ℝ) 1 :=
    link.openProbability hstrict currentGap
  have hmaxImproved :
      (dataset.count first second : ℝ) /
          ((dataset.count first second : ℝ) + (dataset.count second first : ℝ)) <
        link improvedGap := by
    rw [← hperfectFit]
    exact hstrict hperfectFitImproved
  exact coinFlipLogLikelihood_strictDecrease_above_maximizer hforwardReal hreverseReal
    himprovedProbability hcurrentProbability hmaxImproved (hstrict himprovedCurrent)

/--
The local pair likelihood is bounded above by the empirical success-frequency
value, provided the displayed pair probability is in the source's open
probability domain.
-/
theorem pairwiseLogTerm_le_empirical_frequency
    {Alternative : Type*} (dataset : PairwiseCountDataset Alternative)
    (link : CDFLikePairwiseLink) (score : ScoreVector Alternative)
    {first second : Alternative}
    (hforward : 0 < dataset.count first second)
    (hreverse : 0 < dataset.count second first)
    (hprobability :
      randomUtilityWinProbability link score first second ∈ Set.Ioo (0 : ℝ) 1) :
    pairwiseLogTerm dataset link score first second ≤
      coinFlipLogLikelihood (dataset.count first second : ℝ)
        (dataset.count second first : ℝ)
        ((dataset.count first second : ℝ) /
          ((dataset.count first second : ℝ) + (dataset.count second first : ℝ))) := by
  rw [pairwiseLogTerm_eq_coinFlipLogLikelihood]
  have hforwardReal : 0 < (dataset.count first second : ℝ) := by
    exact_mod_cast hforward
  have hreverseReal : 0 < (dataset.count second first : ℝ) := by
    exact_mod_cast hreverse
  exact coinFlipLogLikelihood_isMaxOn hforwardReal hreverseReal hprobability

/--
If a local pair term attains its empirical-frequency upper bound, its modeled
win probability equals that empirical frequency. This is the checked analytic
step used by the source's one-neighbor proof.
-/
theorem randomUtilityWinProbability_eq_empirical_frequency_of_pairwiseLogTerm_eq
    {Alternative : Type*} (dataset : PairwiseCountDataset Alternative)
    (link : CDFLikePairwiseLink) (score : ScoreVector Alternative)
    {first second : Alternative}
    (hforward : 0 < dataset.count first second)
    (hreverse : 0 < dataset.count second first)
    (hprobability :
      randomUtilityWinProbability link score first second ∈ Set.Ioo (0 : ℝ) 1)
    (heq : pairwiseLogTerm dataset link score first second =
      coinFlipLogLikelihood (dataset.count first second : ℝ)
        (dataset.count second first : ℝ)
        ((dataset.count first second : ℝ) /
          ((dataset.count first second : ℝ) + (dataset.count second first : ℝ)))) :
    randomUtilityWinProbability link score first second =
      (dataset.count first second : ℝ) /
        ((dataset.count first second : ℝ) + (dataset.count second first : ℝ)) := by
  rw [pairwiseLogTerm_eq_coinFlipLogLikelihood] at heq
  have hforwardReal : 0 < (dataset.count first second : ℝ) := by
    exact_mod_cast hforward
  have hreverseReal : 0 < (dataset.count second first : ℝ) := by
    exact_mod_cast hreverse
  exact coinFlipLogLikelihood_eq_maximizer hforwardReal hreverseReal hprobability heq

/-- Split the finite likelihood into terms incident and non-incident to one alternative. -/
theorem pairwiseLogLikelihood_eq_incident_add_nonincident
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : ℝ → ℝ)
    (score : ScoreVector Alternative) (alternative : Alternative) :
    pairwiseLogLikelihood dataset link score =
      (∑ pair ∈ incidentPairs alternative,
        pairwiseLogLikelihoodSummand dataset link score pair) +
      ∑ pair ∈ nonincidentPairs alternative,
        pairwiseLogLikelihoodSummand dataset link score pair := by
  classical
  unfold incidentPairs nonincidentPairs
  unfold pairwiseLogLikelihood pairwiseLogLikelihoodSummand
  simpa using
    (Finset.sum_filter_add_sum_filter_not
      ((Finset.univ : Finset Alternative).offDiag)
      (fun pair => incidentTo alternative pair)
      (fun pair =>
        (dataset.count pair.1 pair.2 : ℝ) *
          Real.log (randomUtilityWinProbability link score pair.1 pair.2))).symm

/-- Under the source's one-neighbor premise, all incident likelihood terms form one pair term. -/
theorem sum_incident_pairwiseLogLikelihoodSummand_eq_pairwiseLogTerm
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (score : ScoreVector Alternative) {first second : Alternative}
    (honly : dataset.hasOnlyNeighbor first second) :
    ∑ pair ∈ incidentPairs first,
      pairwiseLogLikelihoodSummand dataset link score pair =
      pairwiseLogTerm dataset link score first second := by
  classical
  unfold incidentPairs
  let allPairs : Finset (Alternative × Alternative) :=
    (Finset.univ : Finset Alternative).offDiag
  let relevantPairs : Finset (Alternative × Alternative) := {(first, second), (second, first)}
  have hfirst_second_mem : (first, second) ∈ allPairs := by
    change (first, second) ∈ (Finset.univ : Finset Alternative).offDiag
    exact Finset.mem_offDiag.2 ⟨Finset.mem_univ first, Finset.mem_univ second, honly.1⟩
  have hsecond_first_mem : (second, first) ∈ allPairs := by
    change (second, first) ∈ (Finset.univ : Finset Alternative).offDiag
    exact Finset.mem_offDiag.2 ⟨Finset.mem_univ second, Finset.mem_univ first, honly.1.symm⟩
  have hsubset : relevantPairs ⊆ allPairs.filter (incidentTo first) := by
    intro pair hpair
    simp only [relevantPairs, Finset.mem_insert, Finset.mem_singleton] at hpair
    rcases hpair with hpair | hpair
    · subst pair
      exact Finset.mem_filter.2 ⟨hfirst_second_mem, Or.inl rfl⟩
    · subst pair
      exact Finset.mem_filter.2 ⟨hsecond_first_mem, Or.inr rfl⟩
  have hzero : ∀ pair ∈ allPairs.filter (incidentTo first), pair ∉ relevantPairs →
      pairwiseLogLikelihoodSummand dataset link score pair = 0 := by
    rintro ⟨left, right⟩ hpair hnot
    rcases Finset.mem_filter.1 hpair with ⟨hoffDiag, hincident⟩
    rcases Finset.mem_offDiag.1 hoffDiag with ⟨_, _, hne⟩
    change left ≠ right at hne
    change left = first ∨ right = first at hincident
    rcases hincident with hleft | hright
    · subst left
      have hright_ne_first : right ≠ first := by
        intro h
        exact hne h.symm
      have hright_ne_second : right ≠ second := by
        intro h
        apply hnot
        simp [relevantPairs, h]
      have hcount := (honly.2.2 right hright_ne_first hright_ne_second).1
      simp [pairwiseLogLikelihoodSummand, hcount]
    · subst right
      have hleft_ne_first : left ≠ first := hne
      have hleft_ne_second : left ≠ second := by
        intro h
        apply hnot
        simp [relevantPairs, h]
      have hcount := (honly.2.2 left hleft_ne_first hleft_ne_second).2
      simp [pairwiseLogLikelihoodSummand, hcount]
  have hsum := Finset.sum_subset hsubset hzero
  rw [← hsum]
  have hpairs_ne : (first, second) ≠ (second, first) := by
    intro h
    exact honly.1 (congrArg Prod.fst h)
  simp [relevantPairs, hpairs_ne, pairwiseLogLikelihoodSummand, pairwiseLogTerm]

/-- Replacing one score leaves every non-incident likelihood summand unchanged. -/
theorem sum_nonincident_pairwiseLogLikelihoodSummand_scoreReplace
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : ℝ → ℝ)
    (score : ScoreVector Alternative) (alternative : Alternative) (value : ℝ) :
    ∑ pair ∈ nonincidentPairs alternative,
      pairwiseLogLikelihoodSummand dataset link (scoreReplace score alternative value) pair =
      ∑ pair ∈ nonincidentPairs alternative,
      pairwiseLogLikelihoodSummand dataset link score pair := by
  classical
  unfold nonincidentPairs
  refine Finset.sum_congr rfl ?_
  rintro ⟨first, second⟩ hpair
  rw [Finset.mem_filter] at hpair
  have hfirst : first ≠ alternative := by
    intro h
    exact hpair.2 (Or.inl h)
  have hsecond : second ≠ alternative := by
    intro h
    exact hpair.2 (Or.inr h)
  have hfirst_score : scoreReplace score alternative value first = score first := by
    simp [scoreReplace, hfirst]
  have hsecond_score : scoreReplace score alternative value second = score second := by
    simp [scoreReplace, hsecond]
  unfold pairwiseLogLikelihoodSummand randomUtilityWinProbability
  rw [hfirst_score, hsecond_score]

/--
With one neighbor, changing that alternative's score changes the whole finite
likelihood by exactly the corresponding two-direction pair-likelihood change.
-/
theorem pairwiseLogLikelihood_scoreReplace_sub_pairwiseLogTerm
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (score : ScoreVector Alternative) {first second : Alternative}
    (honly : dataset.hasOnlyNeighbor first second) (value : ℝ) :
    pairwiseLogLikelihood dataset link (scoreReplace score first value) -
        pairwiseLogLikelihood dataset link score =
      pairwiseLogTerm dataset link (scoreReplace score first value) first second -
        pairwiseLogTerm dataset link score first second := by
  rw [pairwiseLogLikelihood_eq_incident_add_nonincident,
    pairwiseLogLikelihood_eq_incident_add_nonincident,
    sum_incident_pairwiseLogLikelihoodSummand_eq_pairwiseLogTerm dataset link
      (scoreReplace score first value) honly,
    sum_incident_pairwiseLogLikelihoodSummand_eq_pairwiseLogTerm dataset link score honly,
    sum_nonincident_pairwiseLogLikelihoodSummand_scoreReplace]
  ring

/--
The one-neighbor MLE argument from Supplement A.2, factored through an
explicit perfect-fit witness. A fixed-reference MLE must assign the observed
pair frequency whenever that frequency is realized by a score difference.
-/
theorem isPairwiseMLE_randomUtilityWinProbability_eq_empirical_frequency
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (reference : Alternative) (score : ScoreVector Alternative)
    {first second : Alternative}
    (hmle : isPairwiseMLE dataset link reference score)
    (honly : dataset.hasOnlyNeighbor first second)
    (hforward : 0 < dataset.count first second)
    (hreverse : 0 < dataset.count second first)
    (hprobability :
      randomUtilityWinProbability link score first second ∈ Set.Ioo (0 : ℝ) 1)
    (delta : ℝ)
    (hperfectFit : link delta =
      (dataset.count first second : ℝ) /
        ((dataset.count first second : ℝ) + (dataset.count second first : ℝ))) :
    randomUtilityWinProbability link score first second =
      (dataset.count first second : ℝ) /
        ((dataset.count first second : ℝ) + (dataset.count second first : ℝ)) := by
  let candidate : ScoreVector Alternative := scoreReplace score first (score second + delta)
  have hcandidate_probability :
      randomUtilityWinProbability link candidate first second = link delta := by
    unfold candidate randomUtilityWinProbability
    simp [scoreReplace, honly.1.symm]
  have hcandidate_pairTerm :
      pairwiseLogTerm dataset link candidate first second =
        coinFlipLogLikelihood (dataset.count first second : ℝ)
          (dataset.count second first : ℝ)
          ((dataset.count first second : ℝ) /
            ((dataset.count first second : ℝ) + (dataset.count second first : ℝ))) := by
    rw [pairwiseLogTerm_eq_coinFlipLogLikelihood, hcandidate_probability, hperfectFit]
  have hglobal : pairwiseLogLikelihood dataset link candidate ≤
      pairwiseLogLikelihood dataset link score :=
    isPairwiseMLE_global_max dataset link reference score hmle candidate
  have hlocal_difference :=
    pairwiseLogLikelihood_scoreReplace_sub_pairwiseLogTerm dataset link score honly
      (score second + delta)
  have hlocal : pairwiseLogTerm dataset link candidate first second ≤
      pairwiseLogTerm dataset link score first second := by
    dsimp [candidate] at hlocal_difference hglobal ⊢
    linarith
  have hupper := pairwiseLogTerm_le_empirical_frequency dataset link score hforward hreverse hprobability
  have hscore_eq : pairwiseLogTerm dataset link score first second =
      coinFlipLogLikelihood (dataset.count first second : ℝ)
        (dataset.count second first : ℝ)
        ((dataset.count first second : ℝ) /
          ((dataset.count first second : ℝ) + (dataset.count second first : ℝ))) := by
    apply le_antisymm hupper
    rw [← hcandidate_pairTerm]
    exact hlocal
  exact randomUtilityWinProbability_eq_empirical_frequency_of_pairwiseLogTerm_eq
    dataset link score hforward hreverse hprobability hscore_eq

/--
If the source link is strictly monotone, the perfect-fit witness is the unique
score difference at a one-neighbor MLE. This is the distance conclusion of
Lemma 2.2 conditional on the supplied inverse-image witness.
-/
theorem isPairwiseMLE_score_sub_eq_perfectFit_witness
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (reference : Alternative) (score : ScoreVector Alternative)
    {first second : Alternative}
    (hmle : isPairwiseMLE dataset link reference score)
    (honly : dataset.hasOnlyNeighbor first second)
    (hforward : 0 < dataset.count first second)
    (hreverse : 0 < dataset.count second first)
    (hprobability :
      randomUtilityWinProbability link score first second ∈ Set.Ioo (0 : ℝ) 1)
    (hstrict : StrictMono (link : ℝ → ℝ))
    (delta : ℝ)
    (hperfectFit : link delta =
      (dataset.count first second : ℝ) /
        ((dataset.count first second : ℝ) + (dataset.count second first : ℝ))) :
    score first - score second = delta := by
  apply hstrict.injective
  change randomUtilityWinProbability link score first second = link delta
  rw [isPairwiseMLE_randomUtilityWinProbability_eq_empirical_frequency
    dataset link reference score hmle honly hforward hreverse hprobability delta hperfectFit,
    hperfectFit]

/--
Source-faithful one-neighbor perfect fit: continuity realizes the empirical
frequency, and strict monotonicity makes its score difference unique. This is
the mathematical content of Lemma 2.2, using an existential/intrinsic form of
the source notation `F⁻¹(p)`.
-/
theorem isPairwiseMLE_existsUnique_perfectFit_distance
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (reference : Alternative) (score : ScoreVector Alternative)
    {first second : Alternative}
    (hmle : isPairwiseMLE dataset link reference score)
    (honly : dataset.hasOnlyNeighbor first second)
    (hforward : 0 < dataset.count first second)
    (hreverse : 0 < dataset.count second first)
    (hcontinuous : Continuous (link : ℝ → ℝ))
    (hstrict : StrictMono (link : ℝ → ℝ)) :
    ∃! delta : ℝ,
      link delta = (dataset.count first second : ℝ) /
        ((dataset.count first second : ℝ) + (dataset.count second first : ℝ)) ∧
      score first - score second = delta := by
  have hforwardReal : 0 < (dataset.count first second : ℝ) := by
    exact_mod_cast hforward
  have hreverseReal : 0 < (dataset.count second first : ℝ) := by
    exact_mod_cast hreverse
  have hfrequency :
      (dataset.count first second : ℝ) /
          ((dataset.count first second : ℝ) + (dataset.count second first : ℝ)) ∈
        Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos hforwardReal (by linarith)
    · exact (div_lt_one (by linarith)).2 (by linarith)
  obtain ⟨delta, hperfectFit⟩ := link.exists_eq_of_mem_Ioo hcontinuous hfrequency
  have hprobability :
      randomUtilityWinProbability link score first second ∈ Set.Ioo (0 : ℝ) 1 := by
    unfold randomUtilityWinProbability
    exact link.openProbability hstrict (score first - score second)
  have hdistance := isPairwiseMLE_score_sub_eq_perfectFit_witness
    dataset link reference score hmle honly hforward hreverse hprobability hstrict delta hperfectFit
  refine ⟨delta, ⟨hperfectFit, hdistance⟩, ?_⟩
  intro other hother
  exact hother.2.symm.trans hdistance

/--
A one-neighbor MLE ranks the alternative with the strict direct-count majority
above its neighbor.  This is the order-only corollary of the source's Lemma
2.2, avoiding any arbitrary totalization of the inverse CDF.
-/
theorem isPairwiseMLE_score_lt_of_hasOnlyNeighbor_count_majority
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (reference : Alternative) (score : ScoreVector Alternative)
    {first second : Alternative}
    (hmle : isPairwiseMLE dataset link reference score)
    (honly : dataset.hasOnlyNeighbor first second)
    (hforward : 0 < dataset.count first second)
    (hreverse : 0 < dataset.count second first)
    (hmajority : dataset.count second first < dataset.count first second)
    (hcontinuous : Continuous (link : ℝ → ℝ))
    (hstrict : StrictMono (link : ℝ → ℝ)) :
    score second < score first := by
  obtain ⟨delta, ⟨hfit, hdistance⟩, -⟩ :=
    isPairwiseMLE_existsUnique_perfectFit_distance dataset link reference score hmle honly
      hforward hreverse hcontinuous hstrict
  have hforwardReal : 0 < (dataset.count first second : ℝ) := by
    exact_mod_cast hforward
  have hreverseReal : 0 < (dataset.count second first : ℝ) := by
    exact_mod_cast hreverse
  have hmajorityReal : (dataset.count second first : ℝ) <
      (dataset.count first second : ℝ) := by
    exact_mod_cast hmajority
  have hsumPos : 0 < (dataset.count first second : ℝ) +
      (dataset.count second first : ℝ) := by
    linarith
  have hfrequency : (1 / 2 : ℝ) <
      (dataset.count first second : ℝ) /
        ((dataset.count first second : ℝ) + (dataset.count second first : ℝ)) := by
    rw [lt_div_iff₀ hsumPos]
    nlinarith
  have hzero : link 0 = 1 / 2 := by
    have hcomplementary := link.complementary 0
    norm_num at hcomplementary ⊢
    linarith
  have hlinkIncrease : link 0 < link delta := by
    rw [hfit, hzero]
    exact hfrequency
  have hdeltaPos : 0 < delta := by
    by_contra hnot
    have hnonpos : delta ≤ 0 := le_of_not_gt hnot
    have hmonotone : link delta ≤ link 0 := hstrict.monotone hnonpos
    linarith
  linarith

/--
The reverse-majority form of the one-neighbor MLE order corollary.  The
one-neighbor alternative is ranked strictly below its neighbor when its direct
count is strictly smaller in the opposite direction.
-/
theorem isPairwiseMLE_score_lt_of_hasOnlyNeighbor_reverse_count_majority
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (dataset : PairwiseCountDataset Alternative) (link : CDFLikePairwiseLink)
    (reference : Alternative) (score : ScoreVector Alternative)
    {first second : Alternative}
    (hmle : isPairwiseMLE dataset link reference score)
    (honly : dataset.hasOnlyNeighbor first second)
    (hforward : 0 < dataset.count first second)
    (hreverse : 0 < dataset.count second first)
    (hminority : dataset.count first second < dataset.count second first)
    (hcontinuous : Continuous (link : ℝ → ℝ))
    (hstrict : StrictMono (link : ℝ → ℝ)) :
    score first < score second := by
  obtain ⟨delta, ⟨hfit, hdistance⟩, -⟩ :=
    isPairwiseMLE_existsUnique_perfectFit_distance dataset link reference score hmle honly
      hforward hreverse hcontinuous hstrict
  have hforwardReal : 0 < (dataset.count first second : ℝ) := by
    exact_mod_cast hforward
  have hreverseReal : 0 < (dataset.count second first : ℝ) := by
    exact_mod_cast hreverse
  have hminorityReal : (dataset.count first second : ℝ) <
      (dataset.count second first : ℝ) := by
    exact_mod_cast hminority
  have hsumPos : 0 < (dataset.count first second : ℝ) +
      (dataset.count second first : ℝ) := by
    linarith
  have hfrequency :
      (dataset.count first second : ℝ) /
          ((dataset.count first second : ℝ) + (dataset.count second first : ℝ)) <
        (1 / 2 : ℝ) := by
    rw [div_lt_iff₀ hsumPos]
    nlinarith
  have hzero : link 0 = 1 / 2 := by
    have hcomplementary := link.complementary 0
    norm_num at hcomplementary ⊢
    linarith
  have hlinkDecrease : link delta < link 0 := by
    rw [hfit, hzero]
    exact hfrequency
  have hdeltaNeg : delta < 0 := by
    by_contra hnot
    have hnonneg : 0 ≤ delta := le_of_not_gt hnot
    have hmonotone : link 0 ≤ link delta := hstrict.monotone hnonneg
    linarith
  linarith

end PairwiseCountDataset
end HumanFeedback
end Learning
end AppliedModelingLib
