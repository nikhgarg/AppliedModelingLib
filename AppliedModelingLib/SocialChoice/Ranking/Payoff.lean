import AppliedModelingLib.Foundations.Math.FiniteSigns
import AppliedModelingLib.Foundations.Probability.Conditional
import AppliedModelingLib.SocialChoice.Ranking.Kendall
import AppliedModelingLib.SocialChoice.Ranking.Probability
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Payoff Decompositions for Ranking Laws

Reusable finite PMF algebra for ranking laws with first-choice probabilities
and top-vs-runner-up value gaps.

These lemmas are paper-neutral.  Caller-specific welfare models, strategy names,
and theorem-number wrappers should remain in paper folders and call this layer.

## Main declarations

- `firstChoiceMissProb`
- `valueGap`
- `firstChoiceGapMass`
- `firstChoiceCollisionDiff`
- `secondMoverUtility`
- `expectedSecondMoverIndependent`
- `rerankingGainOnPair`
- `expectedRerankingGain`
- `PrefersIndependentReranking`
- `weakerCompetitionGain`
- `PrefersWeakerCompetition`
- `expectedWelfareShared`
- `disagreementConditionalGain`
- `secondMoverFirstLawSwitchGain`
- `sum_firstChoiceProb_eq_one`
- `sum_firstChoiceGapMass_eq_expectedGap`
-/

open scoped BigOperators

namespace AppliedModelingLib
namespace SocialChoice
namespace Ranking

noncomputable section

/-- The probability that a draw from `μ` does not put candidate `c` first. -/
def firstChoiceMissProb {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) : ℝ :=
  1 - firstChoiceProb μ c

/--
The loss from being forced down from a ranking's first candidate to its second
candidate.
-/
def valueGap {n : ℕ} (value : Candidate n → ℝ) (π : Ranking n) : ℝ :=
  value (firstChoice π) - value (secondChoice π)

/-- Expected value of the candidate selected by the firm that chooses first. -/
def expectedFirstMoverUtility {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  pmfExp μ (fun π => value (firstChoice π))

theorem expectedFirstMoverUtility_mul_value {n : ℕ}
    (μ : PMF (Ranking n)) (c : ℝ) (value : Candidate n → ℝ) :
    expectedFirstMoverUtility μ (fun i => c * value i) =
      c * expectedFirstMoverUtility μ value := by
  unfold expectedFirstMoverUtility
  simp [pmfExp_const_mul]

/-- Expected value of the candidate hired by the second mover when both firms use
the same realized ranking. -/
def expectedSecondMoverShared {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  pmfExp μ (fun π => value (secondChoice π))

/-- The real-valued probability that a draw from `μ` puts candidate `c` second. -/
def secondChoiceProb {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) : ℝ :=
  pmfProb μ (fun π => c = secondChoice π)

/-- Pointwise utility to the second mover when the first mover uses `σ`
and the second mover uses `π`. -/
def secondMoverUtility {n : ℕ} (value : Candidate n → ℝ)
    (π σ : Ranking n) : ℝ :=
  value (bestRemainingAfter π (firstChoice σ))

/-- Expected utility to the second mover when the second mover draws `π` from
`μ₂` and the first mover draws `σ` from `μ₁`. -/
def expectedSecondMoverIndependent {n : ℕ}
    (μ₂ μ₁ : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  pmfPairExp μ₂ μ₁ (fun π σ => secondMoverUtility value π σ)

@[simp] theorem secondMoverUtility_mul_value {n : ℕ}
    (c : ℝ) (value : Candidate n → ℝ) (π σ : Ranking n) :
    secondMoverUtility (fun i => c * value i) π σ =
      c * secondMoverUtility value π σ := rfl

theorem expectedSecondMoverIndependent_mul_value {n : ℕ}
    (μ₂ μ₁ : PMF (Ranking n)) (c : ℝ) (value : Candidate n → ℝ) :
    expectedSecondMoverIndependent μ₂ μ₁ (fun i => c * value i) =
      c * expectedSecondMoverIndependent μ₂ μ₁ value := by
  unfold expectedSecondMoverIndependent pmfPairExp
  simp [pmfExp_const_mul]

/--
Gain to a fixed second-mover law from switching the first-mover law from
`μFrom` to `μTo`.
-/
def secondMoverFirstLawSwitchGain {n : ℕ}
    (μSecond μFrom μTo : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  expectedSecondMoverIndependent μSecond μTo value -
    expectedSecondMoverIndependent μSecond μFrom value

/-- Social welfare in the ordered version of the game where the `σ`-firm chooses
first and the `π`-firm chooses second. -/
def welfareOrdered {n : ℕ} (value : Candidate n → ℝ) (π σ : Ranking n) : ℝ :=
  value (firstChoice σ) + secondMoverUtility value π σ

/-- Social welfare when the first mover uses `μ₁` and the second mover uses `μ₂`. -/
def expectedWelfareOrdered {n : ℕ}
    (μ₂ μ₁ : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  pmfPairExp μ₂ μ₁ (fun π σ => welfareOrdered value π σ)

/--
For a pair of rankings `(π, σ)`, this is the second mover's gain from using an
independent ranking `π` instead of sharing `π` when the first mover uses `σ`.
-/
def rerankingGainOnPair {n : ℕ} (value : Candidate n → ℝ)
    (π σ : Ranking n) : ℝ :=
  if firstChoice π = firstChoice σ then 0
  else value (firstChoice π) - value (secondChoice π)

/-- A pair-lifted version of shared-reranking utility on the common product
space `μ × μ`. -/
def expectedSecondMoverSharedOnPairs {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  pmfPairExp μ μ (fun π _σ => secondMoverUtility value π π)

/-- The expected gain from independent reranking over a pair of i.i.d. ranking
draws. -/
def expectedRerankingGain {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  pmfPairExp μ μ (fun π σ => rerankingGainOnPair value π σ)

@[simp] theorem firstChoiceProb_pure {n : ℕ}
    (π : Ranking n) (c : Candidate n) :
    firstChoiceProb (PMF.pure π) c = if c = firstChoice π then 1 else 0 := by
  classical
  unfold firstChoiceProb pmfProb
  simp [pmfExp_pure]

@[simp] theorem firstChoiceProb_pure_firstChoice {n : ℕ}
    (π : Ranking n) :
    firstChoiceProb (PMF.pure π) (firstChoice π) = 1 := by
  simp

@[simp] theorem firstChoiceMissProb_pure_firstChoice {n : ℕ}
    (π : Ranking n) :
    firstChoiceMissProb (PMF.pure π) (firstChoice π) = 0 := by
  simp [firstChoiceMissProb]

/-- First-choice probabilities are nonnegative. -/
theorem firstChoiceProb_nonneg {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    0 ≤ firstChoiceProb μ c := by
  classical
  unfold firstChoiceProb pmfProb pmfExp
  refine Finset.sum_nonneg ?_
  intro π _
  refine mul_nonneg ENNReal.toReal_nonneg ?_
  by_cases h : c = firstChoice π
  · have h' : c = π 0 := by simpa [firstChoice] using h
    simp [h']
  · have h' : c ≠ π 0 := by simpa [firstChoice] using h
    simp [h']

/-- First-choice probabilities are at most one. -/
theorem firstChoiceProb_le_one {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    firstChoiceProb μ c ≤ 1 := by
  classical
  unfold firstChoiceProb pmfProb pmfExp
  calc
    ∑ π : Ranking n, (μ π).toReal * (if c = firstChoice π then (1 : ℝ) else 0)
        ≤ ∑ π : Ranking n, (μ π).toReal * 1 := by
          refine Finset.sum_le_sum ?_
          intro π _
          refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
          by_cases h : c = firstChoice π
          · have h' : c = π 0 := by simpa [firstChoice] using h
            simp [h']
          · have h' : c ≠ π 0 := by simpa [firstChoice] using h
            simp [h']
    _ = ∑ π : Ranking n, (μ π).toReal := by simp
    _ = 1 := pmfToRealSum μ

/-- Miss probabilities are nonnegative. -/
theorem firstChoiceMissProb_nonneg {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    0 ≤ firstChoiceMissProb μ c := by
  unfold firstChoiceMissProb
  have h := firstChoiceProb_le_one (μ := μ) (c := c)
  linarith

/-- Miss probabilities are at most one. -/
theorem firstChoiceMissProb_le_one {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    firstChoiceMissProb μ c ≤ 1 := by
  unfold firstChoiceMissProb
  have h := firstChoiceProb_nonneg (μ := μ) (c := c)
  linarith

@[simp] theorem firstChoiceProb_add_firstChoiceMissProb {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    firstChoiceProb μ c + firstChoiceMissProb μ c = 1 := by
  unfold firstChoiceMissProb
  ring

@[simp] theorem firstChoiceMissProb_add_firstChoiceProb {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    firstChoiceMissProb μ c + firstChoiceProb μ c = 1 := by
  rw [add_comm]
  exact firstChoiceProb_add_firstChoiceMissProb (μ := μ) (c := c)

/-- The first-choice probabilities over all candidates sum to one. -/
theorem sum_firstChoiceProb_eq_one {n : ℕ}
    (μ : PMF (Ranking n)) :
    (∑ c : Candidate n, firstChoiceProb μ c) = 1 := by
  classical
  unfold firstChoiceProb pmfProb pmfExp
  rw [Finset.sum_comm]
  calc
    ∑ π : Ranking n, ∑ c : Candidate n,
        (μ π).toReal * (if c = firstChoice π then (1 : ℝ) else 0)
        = ∑ π : Ranking n,
            (μ π).toReal *
              (∑ c : Candidate n, (if c = firstChoice π then (1 : ℝ) else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          rw [Finset.mul_sum]
    _ = ∑ π : Ranking n, (μ π).toReal * 1 := by
          refine Finset.sum_congr rfl ?_
          intro π _
          have hsum :
              (∑ c : Candidate n, (if c = firstChoice π then (1 : ℝ) else 0)) = 1 := by
            simpa using
              (Finset.sum_ite_eq' Finset.univ (firstChoice π)
                (fun _ : Candidate n => (1 : ℝ)))
          rw [hsum]
    _ = ∑ π : Ranking n, (μ π).toReal := by simp
    _ = 1 := pmfToRealSum μ

/--
First-mover expected utility can be regrouped by the candidate selected first.
-/
theorem expectedFirstMoverUtility_eq_sum_firstChoiceProb {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedFirstMoverUtility μ value =
      ∑ c : Candidate n, firstChoiceProb μ c * value c := by
  classical
  unfold expectedFirstMoverUtility firstChoiceProb pmfProb pmfExp
  calc
    ∑ π : Ranking n, (μ π).toReal * value (firstChoice π)
        = ∑ π : Ranking n, ∑ c : Candidate n,
            if c = firstChoice π then (μ π).toReal * value c else 0 := by
          refine Finset.sum_congr rfl ?_
          intro π _
          have hsum :
              (∑ c : Candidate n,
                if c = firstChoice π then (μ π).toReal * value c else 0) =
                (μ π).toReal * value (firstChoice π) := by
            simpa using
              (Finset.sum_ite_eq' Finset.univ (firstChoice π)
                (fun c : Candidate n => (μ π).toReal * value c))
          rw [hsum]
    _ = ∑ c : Candidate n, ∑ π : Ranking n,
            if c = firstChoice π then (μ π).toReal * value c else 0 := by
          exact Finset.sum_comm
    _ = ∑ c : Candidate n, ∑ π : Ranking n,
            ((μ π).toReal *
              (if c = firstChoice π then (1 : ℝ) else 0)) * value c := by
          refine Finset.sum_congr rfl ?_
          intro c _
          refine Finset.sum_congr rfl ?_
          intro π _
          by_cases h : c = firstChoice π
          · simp [h]
          · simp
    _ = ∑ c : Candidate n,
          (∑ π : Ranking n,
            (μ π).toReal *
              (if c = firstChoice π then (1 : ℝ) else 0)) * value c := by
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [Finset.sum_mul]

/-- Shared second-mover utility can be regrouped by the second-position candidate. -/
theorem expectedSecondMoverShared_eq_sum_secondChoiceProb {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedSecondMoverShared μ value =
      ∑ c : Candidate n, secondChoiceProb μ c * value c := by
  classical
  unfold expectedSecondMoverShared secondChoiceProb pmfProb pmfExp
  calc
    ∑ π : Ranking n, (μ π).toReal * value (secondChoice π)
        = ∑ π : Ranking n, ∑ c : Candidate n,
            if c = secondChoice π then (μ π).toReal * value c else 0 := by
          refine Finset.sum_congr rfl ?_
          intro π _
          have hsum :
              (∑ c : Candidate n,
                if c = secondChoice π then (μ π).toReal * value c else 0) =
                (μ π).toReal * value (secondChoice π) := by
            simpa using
              (Finset.sum_ite_eq' Finset.univ (secondChoice π)
                (fun c : Candidate n => (μ π).toReal * value c))
          rw [hsum]
    _ = ∑ c : Candidate n, ∑ π : Ranking n,
            if c = secondChoice π then (μ π).toReal * value c else 0 := by
          exact Finset.sum_comm
    _ = ∑ c : Candidate n, ∑ π : Ranking n,
            ((μ π).toReal *
              (if c = secondChoice π then (1 : ℝ) else 0)) * value c := by
          refine Finset.sum_congr rfl ?_
          intro c _
          refine Finset.sum_congr rfl ?_
          intro π _
          by_cases h : c = secondChoice π
          · simp [h]
          · simp
    _ = ∑ c : Candidate n,
          (∑ π : Ranking n,
            (μ π).toReal *
              (if c = secondChoice π then (1 : ℝ) else 0)) * value c := by
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [Finset.sum_mul]

@[simp] theorem secondMoverUtility_self {n : ℕ} (value : Candidate n → ℝ)
    (π : Ranking n) :
    secondMoverUtility value π π = value (secondChoice π) := by
  simp [secondMoverUtility, bestRemainingAfter]

@[simp] theorem secondMoverUtility_eq_if {n : ℕ} (value : Candidate n → ℝ)
    (π σ : Ranking n) :
    secondMoverUtility value π σ =
      if firstChoice π = firstChoice σ then value (secondChoice π)
      else value (firstChoice π) := by
  by_cases h : firstChoice π = firstChoice σ
  · have h' : π 0 = σ 0 := by
      simpa [firstChoice] using h
    simp [secondMoverUtility, bestRemainingAfter, firstChoice, secondChoice, h']
  · have h' : π 0 ≠ σ 0 := by
      simpa [firstChoice] using h
    simp [secondMoverUtility, bestRemainingAfter, firstChoice, h']

@[simp] theorem welfareOrdered_eq {n : ℕ} (value : Candidate n → ℝ)
    (π σ : Ranking n) :
    welfareOrdered value π σ =
      value (firstChoice σ) + value (bestRemainingAfter π (firstChoice σ)) := rfl

@[simp] theorem welfareOrdered_self {n : ℕ} (value : Candidate n → ℝ)
    (π : Ranking n) :
    welfareOrdered value π π = value (firstChoice π) + value (secondChoice π) := by
  simp [welfareOrdered, secondMoverUtility, bestRemainingAfter]

@[simp] theorem rerankingGainOnPair_self {n : ℕ} (value : Candidate n → ℝ)
    (π : Ranking n) :
    rerankingGainOnPair value π π = 0 := by
  simp [rerankingGainOnPair]

@[simp] theorem rerankingGainOnPair_of_sameFirst {n : ℕ} (value : Candidate n → ℝ)
    (π σ : Ranking n) (h : firstChoice π = firstChoice σ) :
    rerankingGainOnPair value π σ = 0 := by
  have h' : π 0 = σ 0 := by
    simpa [firstChoice] using h
  simp [rerankingGainOnPair, firstChoice, h']

@[simp] theorem rerankingGainOnPair_of_neFirst {n : ℕ} (value : Candidate n → ℝ)
    (π σ : Ranking n) (h : firstChoice π ≠ firstChoice σ) :
    rerankingGainOnPair value π σ =
      value (firstChoice π) - value (secondChoice π) := by
  have h' : π 0 ≠ σ 0 := by
    simpa [firstChoice] using h
  simp [rerankingGainOnPair, firstChoice, secondChoice, h']

/--
Pointwise decomposition of second-mover utility into the shared-ranking utility
plus the reranking gain.
-/
theorem secondMoverUtility_eq_shared_add_rerankingGain {n : ℕ}
    (value : Candidate n → ℝ) (π σ : Ranking n) :
    secondMoverUtility value π σ =
      secondMoverUtility value π π + rerankingGainOnPair value π σ := by
  by_cases h : firstChoice π = firstChoice σ
  · have h' : π 0 = σ 0 := by
      simpa [firstChoice] using h
    simp [secondMoverUtility_eq_if, rerankingGainOnPair, firstChoice, secondChoice, h']
  · have h' : π 0 ≠ σ 0 := by
      simpa [firstChoice] using h
    simp [secondMoverUtility_eq_if, rerankingGainOnPair, firstChoice, secondChoice, h']

theorem secondMoverUtility_sub_self_eq_rerankingGain {n : ℕ}
    (value : Candidate n → ℝ) (π σ : Ranking n) :
    secondMoverUtility value π σ - secondMoverUtility value π π =
      rerankingGainOnPair value π σ := by
  rw [secondMoverUtility_eq_shared_add_rerankingGain]
  ring

/-- Finite-sum equation on the common product space `μ × μ`. -/
theorem expectedSecondMoverIndependent_sub_sharedOnPairs_eq_expectedRerankingGain
    {n : ℕ} (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedSecondMoverIndependent μ μ value - expectedSecondMoverSharedOnPairs μ value =
      expectedRerankingGain μ value := by
  unfold expectedSecondMoverIndependent expectedSecondMoverSharedOnPairs
    expectedRerankingGain pmfPairExp
  rw [← pmfExp_sub]
  congr 1
  funext π
  rw [← pmfExp_sub]
  congr 1
  funext σ
  exact secondMoverUtility_sub_self_eq_rerankingGain (value := value) π σ

theorem expectedSecondMoverIndependent_eq_sharedOnPairs_add_expectedRerankingGain
    {n : ℕ} (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedSecondMoverIndependent μ μ value =
      expectedSecondMoverSharedOnPairs μ value + expectedRerankingGain μ value := by
  have h :=
    expectedSecondMoverIndependent_sub_sharedOnPairs_eq_expectedRerankingGain
      (μ := μ) (value := value)
  linarith

@[simp] theorem expectedSecondMoverSharedOnPairs_eq_expectedSecondMoverShared
    {n : ℕ} (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedSecondMoverSharedOnPairs μ value = expectedSecondMoverShared μ value := by
  unfold expectedSecondMoverSharedOnPairs expectedSecondMoverShared pmfPairExp
  simp [pmfExp_const]

theorem expectedSecondMoverIndependent_sub_shared_eq_expectedRerankingGain
    {n : ℕ} (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedSecondMoverIndependent μ μ value - expectedSecondMoverShared μ value =
      expectedRerankingGain μ value := by
  rw [← expectedSecondMoverSharedOnPairs_eq_expectedSecondMoverShared]
  exact expectedSecondMoverIndependent_sub_sharedOnPairs_eq_expectedRerankingGain
    (μ := μ) (value := value)

/--
Source-shaped form of the independent-reranking gain: first condition on the
shared/first-mover realized ranking `τ`, then compare an independent second
draw's best remaining candidate against the shared ranking's second choice.
-/
theorem expectedRerankingGain_eq_expect_firstDraw_gain
    {n : ℕ} (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedRerankingGain μ value =
      pmfExp μ (fun τ =>
        pmfExp μ (fun π =>
          value (bestRemainingAfter π (firstChoice τ)) - value (secondChoice τ))) := by
  have hgain :
      expectedRerankingGain μ value =
        expectedSecondMoverIndependent μ μ value - expectedSecondMoverShared μ value := by
    exact (expectedSecondMoverIndependent_sub_shared_eq_expectedRerankingGain
      (μ := μ) (value := value)).symm
  have hswap :
      pmfPairExp μ μ
          (fun τ π => value (bestRemainingAfter π (firstChoice τ))) =
        expectedSecondMoverIndependent μ μ value := by
    unfold expectedSecondMoverIndependent secondMoverUtility
    rw [pmfPairExp_swap]
  rw [hgain]
  symm
  calc
    pmfExp μ (fun τ =>
        pmfExp μ (fun π =>
          value (bestRemainingAfter π (firstChoice τ)) - value (secondChoice τ)))
        =
      pmfExp μ (fun τ =>
        pmfExp μ (fun π => value (bestRemainingAfter π (firstChoice τ))) -
          value (secondChoice τ)) := by
        congr 1
        funext τ
        rw [pmfExp_sub, pmfExp_const]
    _ =
      pmfPairExp μ μ
          (fun τ π => value (bestRemainingAfter π (firstChoice τ))) -
        expectedSecondMoverShared μ value := by
        unfold pmfPairExp expectedSecondMoverShared
        rw [← pmfExp_sub]
    _ = expectedSecondMoverIndependent μ μ value -
        expectedSecondMoverShared μ value := by
        rw [hswap]

@[simp] theorem expectedRerankingGain_pure {n : ℕ}
    (π : Ranking n) (value : Candidate n → ℝ) :
    expectedRerankingGain (PMF.pure π) value = 0 := by
  unfold expectedRerankingGain pmfPairExp
  simp [pmfExp_pure]

private theorem pmf_compl_indicator_sum {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] :
    (∑ a : α, (μ a).toReal * (if p a then (0 : ℝ) else 1)) =
      1 - ∑ a : α, (μ a).toReal * (if p a then (1 : ℝ) else 0) := by
  classical
  calc
    ∑ a : α, (μ a).toReal * (if p a then (0 : ℝ) else 1)
        = ∑ a : α,
            ((μ a).toReal * 1 -
              (μ a).toReal * (if p a then (1 : ℝ) else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          by_cases h : p a <;> simp [h]
    _ = (∑ a : α, (μ a).toReal * 1) -
          ∑ a : α, (μ a).toReal * (if p a then (1 : ℝ) else 0) := by
          rw [Finset.sum_sub_distrib]
    _ = 1 - ∑ a : α, (μ a).toReal * (if p a then (1 : ℝ) else 0) := by
          simp [pmfToRealSum μ]

/-- Miss probability is the probability that the first choice is not `c`. -/
theorem firstChoiceMissProb_eq_pmfProb_ne {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    firstChoiceMissProb μ c = pmfProb μ (fun π => c ≠ firstChoice π) := by
  classical
  unfold firstChoiceMissProb firstChoiceProb pmfProb pmfExp
  rw [← pmf_compl_indicator_sum μ (fun π : Ranking n => c = firstChoice π)]
  refine Finset.sum_congr rfl ?_
  intro π _
  by_cases h : c = firstChoice π <;> simp [h]

/--
If a positive-mass ranking does not put `c` first, then the miss probability for
`c` is strictly positive.
-/
theorem firstChoiceMissProb_pos_of_mass_ne_firstChoice {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) (π₀ : Ranking n)
    (hne : c ≠ firstChoice π₀)
    (hmass : 0 < (μ π₀).toReal) :
    0 < firstChoiceMissProb μ c := by
  classical
  rw [firstChoiceMissProb_eq_pmfProb_ne]
  unfold pmfProb pmfExp
  refine AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg
    (f := fun π : Ranking n =>
      (μ π).toReal * if c ≠ firstChoice π then (1 : ℝ) else 0)
    (a₀ := π₀) ?hpos ?hnonneg
  · have hne' : c ≠ π₀ 0 := by simpa [firstChoice] using hne
    simpa [firstChoice, hne'] using hmass
  · intro π
    refine mul_nonneg ENNReal.toReal_nonneg ?_
    by_cases h : c = π 0 <;> simp [firstChoice, h]

/--
The contribution to expected value gap coming from rankings whose first choice
is `c`.
-/
def firstChoiceGapMass {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) (c : Candidate n) : ℝ :=
  pmfExp μ (fun π => if c = firstChoice π then valueGap value π else 0)

/--
The collision-probability difference between a better and worse ranking law,
viewed candidate-by-candidate.
-/
def firstChoiceCollisionDiff {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (c : Candidate n) : ℝ :=
  firstChoiceProb μBetter c - firstChoiceProb μWorse c

/-- Summing the first-choice fibers recovers the full expected value gap. -/
theorem sum_firstChoiceGapMass_eq_expectedGap {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    (∑ c : Candidate n, firstChoiceGapMass μ value c) =
      pmfExp μ (fun π => valueGap value π) := by
  classical
  unfold firstChoiceGapMass pmfExp
  rw [Finset.sum_comm]
  calc
    ∑ π : Ranking n, ∑ c : Candidate n,
        (μ π).toReal * (if c = firstChoice π then valueGap value π else 0)
        = ∑ π : Ranking n,
            (μ π).toReal *
              (∑ c : Candidate n,
                if c = firstChoice π then valueGap value π else 0) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          rw [← Finset.mul_sum]
    _ = ∑ π : Ranking n, (μ π).toReal * valueGap value π := by
          refine Finset.sum_congr rfl ?_
          intro π _
          have hsum :
              (∑ c : Candidate n,
                if c = firstChoice π then valueGap value π else 0) =
                valueGap value π := by
            simpa using
              (Finset.sum_ite_eq' Finset.univ (firstChoice π)
                (fun _ : Candidate n => valueGap value π))
          rw [hsum]
    _ = pmfExp μ (fun π => valueGap value π) := by
          rfl

/--
If every ranking in the first-choice fiber of `c` has nonnegative value gap,
then the corresponding first-choice gap mass is nonnegative.
-/
theorem firstChoiceGapMass_nonneg_of_gap_nonneg_onFiber {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) (c : Candidate n)
    (hgap : ∀ π : Ranking n, c = firstChoice π → 0 ≤ valueGap value π) :
    0 ≤ firstChoiceGapMass μ value c := by
  classical
  unfold firstChoiceGapMass pmfExp
  refine Finset.sum_nonneg ?_
  intro π _
  refine mul_nonneg ENNReal.toReal_nonneg ?_
  by_cases h : c = firstChoice π
  · simpa [h] using hgap π h
  · have h' : c ≠ π 0 := by simpa [firstChoice] using h
    simp [h']

/-- Strict reference-ordering gives a positive value gap at the reference ranking. -/
theorem center_valueGap_pos_of_strictlyOrderedBy {n : ℕ}
    {ρ : Ranking n} {value : Candidate n → ℝ}
    (hvalue : StrictlyOrderedBy ρ value) :
    0 < valueGap value ρ := by
  simpa [valueGap, topTwoValueGap] using
    center_topTwoValueGap_pos_of_strictlyOrderedBy
      (ρ := ρ) (value := value) hvalue

/-- Weak reference-ordering gives a nonnegative value gap at the reference ranking. -/
theorem center_valueGap_nonneg_of_weaklyOrderedBy {n : ℕ}
    {ρ : Ranking n} {value : Candidate n → ℝ}
    (hvalue : WeaklyOrderedBy ρ value) :
    0 ≤ valueGap value ρ := by
  simpa [valueGap, topTwoValueGap] using
    center_topTwoValueGap_nonneg_of_weaklyOrderedBy
      (ρ := ρ) (value := value) hvalue

/--
If a ranking shares the reference top candidate, then weak monotonicity along
the reference ranking makes its top-vs-runner-up value gap nonnegative.
-/
theorem valueGap_nonneg_on_firstFiber_of_weaklyOrderedBy {n : ℕ}
    {ρ : Ranking n} {value : Candidate n → ℝ} {π : Ranking n}
    (hvalue : WeaklyOrderedBy ρ value)
    (hfirst : firstChoice ρ = firstChoice π) :
    0 ≤ valueGap value π := by
  have hneq : secondChoice π ≠ firstChoice ρ := by
    intro h
    have h' : secondChoice π = firstChoice π := by
      calc
        secondChoice π = firstChoice ρ := h
        _ = firstChoice π := hfirst
    exact firstChoice_ne_secondChoice π h'.symm
  have hlt : rankOf ρ (firstChoice ρ) < rankOf ρ (secondChoice π) :=
    rankOf_firstChoice_lt_rankOf_of_ne (ρ := ρ) hneq
  have hle : value (secondChoice π) ≤ value (firstChoice ρ) := hvalue hlt
  have hsub : 0 ≤ value (firstChoice ρ) - value (secondChoice π) :=
    sub_nonneg.mpr hle
  have hfirst_raw : π 0 = ρ 0 := by
    simpa [firstChoice] using hfirst.symm
  simpa [valueGap, firstChoice, secondChoice, hfirst_raw] using hsub

/--
If a ranking shares the reference top candidate, then strict monotonicity along
the reference ranking makes its top-vs-runner-up value gap strictly positive.
-/
theorem valueGap_pos_on_firstFiber_of_strictlyOrderedBy {n : ℕ}
    {ρ : Ranking n} {value : Candidate n → ℝ} {π : Ranking n}
    (hvalue : StrictlyOrderedBy ρ value)
    (hfirst : firstChoice ρ = firstChoice π) :
    0 < valueGap value π := by
  have hneq : secondChoice π ≠ firstChoice ρ := by
    intro h
    have h' : secondChoice π = firstChoice π := by
      calc
        secondChoice π = firstChoice ρ := h
        _ = firstChoice π := hfirst
    exact firstChoice_ne_secondChoice π h'.symm
  have hlt : rankOf ρ (firstChoice ρ) < rankOf ρ (secondChoice π) :=
    rankOf_firstChoice_lt_rankOf_of_ne (ρ := ρ) hneq
  have hltv : value (secondChoice π) < value (firstChoice ρ) := hvalue hlt
  have hsub : 0 < value (firstChoice ρ) - value (secondChoice π) :=
    sub_pos.mpr hltv
  have hfirst_raw : π 0 = ρ 0 := by
    simpa [firstChoice] using hfirst.symm
  simpa [valueGap, firstChoice, secondChoice, hfirst_raw] using hsub

/--
Under a weak reference ordering, the gap mass of the reference top candidate is
nonnegative for every ranking law.
-/
theorem firstChoiceGapMass_nonneg_of_referenceTop_weaklyOrdered {n : ℕ}
    (μ : PMF (Ranking n)) (ρ : Ranking n) (value : Candidate n → ℝ)
    (hvalue : WeaklyOrderedBy ρ value) :
    0 ≤ firstChoiceGapMass μ value (firstChoice ρ) := by
  apply firstChoiceGapMass_nonneg_of_gap_nonneg_onFiber
  intro π hπ
  exact valueGap_nonneg_on_firstFiber_of_weaklyOrderedBy
    (ρ := ρ) (value := value) (π := π) hvalue hπ

/--
If the reference ranking has positive mass and values strictly decrease down
the reference ranking, then the gap mass attached to the reference top
candidate is strictly positive.
-/
theorem firstChoiceGapMass_pos_of_reference_mass_pos_and_strictlyOrderedBy {n : ℕ}
    (μ : PMF (Ranking n)) (ρ : Ranking n) (value : Candidate n → ℝ)
    (hmass : 0 < (μ ρ).toReal)
    (hvalue : StrictlyOrderedBy ρ value) :
    0 < firstChoiceGapMass μ value (firstChoice ρ) := by
  classical
  have hsum :
      0 < ∑ π : Ranking n,
        (μ π).toReal *
          (if firstChoice ρ = firstChoice π then valueGap value π else 0) := by
    apply AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg
      (f := fun π : Ranking n =>
        (μ π).toReal *
          (if firstChoice ρ = firstChoice π then valueGap value π else 0))
      (a₀ := ρ)
    · have hgap : 0 < valueGap value ρ :=
        center_valueGap_pos_of_strictlyOrderedBy hvalue
      simpa using mul_pos hmass hgap
    · intro π
      refine mul_nonneg ENNReal.toReal_nonneg ?_
      by_cases hπ : firstChoice ρ = firstChoice π
      · have hgap := valueGap_nonneg_on_firstFiber_of_weaklyOrderedBy
          (ρ := ρ) (value := value) (π := π)
          (weaklyOrderedBy_of_strictlyOrderedBy hvalue) hπ
        have hraw : ρ 0 = π 0 := by simpa [firstChoice] using hπ
        simp [hraw, hgap]
      · have hraw : ρ 0 ≠ π 0 := by simpa [firstChoice] using hπ
        simp [hraw]
  simpa [firstChoiceGapMass, pmfExp, valueGap, firstChoice] using hsum

/-- Miss probability is positive exactly when first-choice probability is below one. -/
theorem firstChoiceMissProb_pos_iff_firstChoiceProb_lt_one {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    0 < firstChoiceMissProb μ c ↔ firstChoiceProb μ c < 1 := by
  unfold firstChoiceMissProb
  constructor <;> intro h <;>
    linarith [firstChoiceProb_nonneg (μ := μ) (c := c),
      firstChoiceProb_le_one (μ := μ) (c := c)]

/-- Miss probability is nonnegative exactly when first-choice probability is at most one. -/
theorem firstChoiceMissProb_nonneg_iff_firstChoiceProb_le_one {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    0 ≤ firstChoiceMissProb μ c ↔ firstChoiceProb μ c ≤ 1 := by
  unfold firstChoiceMissProb
  constructor <;> intro h <;> linarith

/-- Collision difference is positive exactly when the better law puts more top mass on `c`. -/
theorem firstChoiceCollisionDiff_pos_iff {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (c : Candidate n) :
    0 < firstChoiceCollisionDiff μBetter μWorse c ↔
      firstChoiceProb μWorse c < firstChoiceProb μBetter c := by
  unfold firstChoiceCollisionDiff
  constructor <;> intro h <;> linarith

/--
Collision difference is nonnegative exactly when the better law puts at least
as much top mass on `c`.
-/
theorem firstChoiceCollisionDiff_nonneg_iff {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (c : Candidate n) :
    0 ≤ firstChoiceCollisionDiff μBetter μWorse c ↔
      firstChoiceProb μWorse c ≤ firstChoiceProb μBetter c := by
  unfold firstChoiceCollisionDiff
  constructor <;> intro h <;> linarith

/--
For a fixed second-mover ranking, the expected reranking gain over the first
mover's draw is the miss probability for the fixed top candidate times the
fixed top-vs-runner-up value gap.
-/
theorem innerRerankingGain_eq_missProb_mul_gap {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) (π : Ranking n) :
    pmfExp μ (fun σ => rerankingGainOnPair value π σ) =
      firstChoiceMissProb μ (firstChoice π) * valueGap value π := by
  classical
  unfold firstChoiceMissProb firstChoiceProb pmfProb valueGap rerankingGainOnPair pmfExp
  set gap : ℝ := value (firstChoice π) - value (secondChoice π)
  change
    (∑ σ : Ranking n, (μ σ).toReal *
        (if firstChoice π = firstChoice σ then (0 : ℝ) else gap)) =
      (1 - ∑ σ : Ranking n, (μ σ).toReal *
        (if firstChoice π = firstChoice σ then (1 : ℝ) else 0)) * gap
  calc
    ∑ σ : Ranking n, (μ σ).toReal *
        (if firstChoice π = firstChoice σ then (0 : ℝ) else gap)
        = ∑ σ : Ranking n,
            ((μ σ).toReal *
              (if firstChoice π = firstChoice σ then (0 : ℝ) else 1)) * gap := by
          refine Finset.sum_congr rfl ?_
          intro σ _
          by_cases h : firstChoice π = firstChoice σ <;> simp
    _ = (∑ σ : Ranking n, (μ σ).toReal *
            (if firstChoice π = firstChoice σ then (0 : ℝ) else 1)) * gap := by
          rw [Finset.sum_mul]
    _ = (1 - ∑ σ : Ranking n, (μ σ).toReal *
            (if firstChoice π = firstChoice σ then (1 : ℝ) else 0)) * gap := by
          rw [pmf_compl_indicator_sum]

/-- The utility of a fixed second-mover ranking against a first-mover distribution. -/
def secondMoverAgainst {n : ℕ}
    (μFirst : PMF (Ranking n)) (value : Candidate n → ℝ) (π : Ranking n) : ℝ :=
  pmfExp μFirst (fun σ => secondMoverUtility value π σ)

/--
Against a first-mover distribution, a fixed ranking gets its runner-up value plus
its expected reranking gain.
-/
theorem secondMoverAgainst_eq_runnerup_add_missProb_mul_gap {n : ℕ}
    (μFirst : PMF (Ranking n)) (value : Candidate n → ℝ) (π : Ranking n) :
    secondMoverAgainst μFirst value π =
      value (secondChoice π) +
        firstChoiceMissProb μFirst (firstChoice π) * valueGap value π := by
  classical
  unfold secondMoverAgainst
  calc
    pmfExp μFirst (fun σ => secondMoverUtility value π σ)
        = pmfExp μFirst
            (fun σ => value (secondChoice π) + rerankingGainOnPair value π σ) := by
          congr 1
          funext σ
          rw [secondMoverUtility_eq_shared_add_rerankingGain]
          simp
    _ = pmfExp μFirst (fun _ => value (secondChoice π)) +
          pmfExp μFirst (fun σ => rerankingGainOnPair value π σ) := by
          rw [pmfExp_add]
    _ = value (secondChoice π) +
          firstChoiceMissProb μFirst (firstChoice π) * valueGap value π := by
          simp [innerRerankingGain_eq_missProb_mul_gap]

/--
Equivalent loss form: expected utility equals top-candidate value minus the
probability that the competitor also takes that candidate times the top-second gap.
-/
theorem secondMoverAgainst_eq_top_sub_collisionProb_mul_gap {n : ℕ}
    (μFirst : PMF (Ranking n)) (value : Candidate n → ℝ) (π : Ranking n) :
    secondMoverAgainst μFirst value π =
      value (firstChoice π) -
        firstChoiceProb μFirst (firstChoice π) * valueGap value π := by
  rw [secondMoverAgainst_eq_runnerup_add_missProb_mul_gap]
  unfold firstChoiceMissProb valueGap firstChoice secondChoice
  ring

/-- Independent second-mover utility, rewritten by conditioning on the second ranking. -/
theorem expectedSecondMoverIndependent_eq_expect_secondMoverAgainst {n : ℕ}
    (μSecond μFirst : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedSecondMoverIndependent μSecond μFirst value =
      pmfExp μSecond (fun π => secondMoverAgainst μFirst value π) := by
  rfl

/--
Independent second-mover utility depends on the first mover only through
first-choice collision probabilities.
-/
theorem expectedSecondMoverIndependent_eq_expect_top_sub_collision_loss {n : ℕ}
    (μSecond μFirst : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedSecondMoverIndependent μSecond μFirst value =
      pmfExp μSecond
        (fun π => value (firstChoice π) -
          firstChoiceProb μFirst (firstChoice π) * valueGap value π) := by
  rw [expectedSecondMoverIndependent_eq_expect_secondMoverAgainst]
  congr 1
  funext π
  rw [secondMoverAgainst_eq_top_sub_collisionProb_mul_gap]

/--
Expected reranking gain is an expectation of a miss probability times the
top-vs-runner-up value gap.
-/
theorem expectedRerankingGain_eq_expect_missProb_mul_gap {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedRerankingGain μ value =
      pmfExp μ (fun π => firstChoiceMissProb μ (firstChoice π) * valueGap value π) := by
  classical
  unfold expectedRerankingGain pmfPairExp
  congr 1
  funext π
  exact innerRerankingGain_eq_missProb_mul_gap (μ := μ) (value := value) (π := π)

/--
If every positive-mass second-mover ranking has positive expected gain against
an independent first-mover draw, then independent reranking is strictly better.

This finite-probability bridge lets analytic or model-specific work focus on
the inner conditional gain for a fixed realized ranking, while this lemma
performs the outer averaging over the ranking law.
-/
theorem expectedRerankingGain_pos_of_inner_support_pos {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hinner : ∀ π : Ranking n, 0 < (μ π).toReal →
      0 < pmfExp μ (fun σ => rerankingGainOnPair value π σ)) :
    0 < expectedRerankingGain μ value := by
  unfold expectedRerankingGain pmfPairExp
  exact pmfExp_pos_of_support_forall_pos μ
    (fun π => pmfExp μ (fun σ => rerankingGainOnPair value π σ))
    hinner

/--
Candidate-fiber conditional gains imply positive independent-reranking gain.

This bridge conditions on the first mover's first-choice candidate and averages
the independent second draw's gain within that fiber.
-/
theorem expectedRerankingGain_pos_of_firstChoice_conditional_gain_pos {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hcond : ∀ c : Candidate n,
      0 < pmfProb μ (fun τ => firstChoice τ = c) →
        0 < pmfConditionalExp μ (fun τ => firstChoice τ = c)
          (fun τ =>
            pmfExp μ (fun π =>
              value (bestRemainingAfter π (firstChoice τ)) - value (secondChoice τ)))) :
    0 < expectedRerankingGain μ value := by
  rw [expectedRerankingGain_eq_expect_firstDraw_gain]
  exact pmfExp_pos_of_state_conditionalExp_pos
    (μ := μ) (state := fun τ : Ranking n => firstChoice τ)
    (f := fun τ =>
      pmfExp μ (fun π =>
        value (bestRemainingAfter π (firstChoice τ)) - value (secondChoice τ)))
    hcond

/--
Same as `expectedRerankingGain_pos_of_firstChoice_conditional_gain_pos`, with
the fiber probability written using `firstChoiceProb`.
-/
theorem expectedRerankingGain_pos_of_firstChoiceProb_conditional_gain_pos {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hcond : ∀ c : Candidate n,
      0 < firstChoiceProb μ c →
        0 < pmfConditionalExp μ (fun τ => c = firstChoice τ)
          (fun τ =>
            pmfExp μ (fun π =>
              value (bestRemainingAfter π (firstChoice τ)) - value (secondChoice τ)))) :
    0 < expectedRerankingGain μ value := by
  refine expectedRerankingGain_pos_of_firstChoice_conditional_gain_pos
    (μ := μ) (value := value) ?_
  intro c hc
  have hc' : 0 < firstChoiceProb μ c := by
    simpa [firstChoiceProb, eq_comm] using hc
  have h := hcond c hc'
  simpa [eq_comm] using h

theorem expectedRerankingGain_nonneg_of_gap_nonneg {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hgap : ∀ π : Ranking n, 0 ≤ valueGap value π) :
    0 ≤ expectedRerankingGain μ value := by
  classical
  rw [expectedRerankingGain_eq_expect_missProb_mul_gap]
  unfold pmfExp
  refine Finset.sum_nonneg ?_
  intro π _
  refine mul_nonneg ENNReal.toReal_nonneg ?_
  exact mul_nonneg
    (firstChoiceMissProb_nonneg (μ := μ) (c := firstChoice π))
    (hgap π)

/--
Equation grouped by the second mover's first-choice candidate rather than by full
rankings.
-/
theorem expectedRerankingGain_eq_sum_firstChoiceMissProb_mul_firstChoiceGapMass
    {n : ℕ} (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedRerankingGain μ value =
      ∑ c : Candidate n,
        firstChoiceMissProb μ c * firstChoiceGapMass μ value c := by
  classical
  rw [expectedRerankingGain_eq_expect_missProb_mul_gap]
  unfold firstChoiceGapMass pmfExp
  calc
    ∑ π : Ranking n,
        (μ π).toReal *
          (firstChoiceMissProb μ (firstChoice π) * valueGap value π)
        = ∑ π : Ranking n,
            (μ π).toReal *
              (∑ c : Candidate n,
                firstChoiceMissProb μ c *
                  (if c = firstChoice π then valueGap value π else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          have hsplit :
              firstChoiceMissProb μ (firstChoice π) * valueGap value π =
                ∑ c : Candidate n,
                  firstChoiceMissProb μ c *
                    (if c = firstChoice π then valueGap value π else 0) := by
            calc
              firstChoiceMissProb μ (firstChoice π) * valueGap value π
                  = ∑ c : Candidate n,
                      if c = firstChoice π
                      then firstChoiceMissProb μ c * valueGap value π
                      else 0 := by
                        symm
                        simpa using
                          (Finset.sum_ite_eq' Finset.univ (firstChoice π)
                            (fun c : Candidate n =>
                              firstChoiceMissProb μ c * valueGap value π))
              _ = ∑ c : Candidate n,
                    firstChoiceMissProb μ c *
                      (if c = firstChoice π then valueGap value π else 0) := by
                    refine Finset.sum_congr rfl ?_
                    intro c _
                    by_cases h : c = firstChoice π <;> simp [h]
          rw [hsplit]
    _ = ∑ π : Ranking n,
          ∑ c : Candidate n,
            (μ π).toReal *
              (firstChoiceMissProb μ c *
                (if c = firstChoice π then valueGap value π else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          rw [Finset.mul_sum]
    _ = ∑ π : Ranking n,
          ∑ c : Candidate n,
            firstChoiceMissProb μ c *
              ((μ π).toReal *
                (if c = firstChoice π then valueGap value π else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          refine Finset.sum_congr rfl ?_
          intro c _
          ring
    _ = ∑ c : Candidate n,
          ∑ π : Ranking n,
            firstChoiceMissProb μ c *
              ((μ π).toReal *
                (if c = firstChoice π then valueGap value π else 0)) := by
          rw [Finset.sum_comm]
    _ = ∑ c : Candidate n,
          firstChoiceMissProb μ c *
            (∑ π : Ranking n,
              (μ π).toReal *
                (if c = firstChoice π then valueGap value π else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [Finset.mul_sum]
    _ = ∑ c : Candidate n,
          firstChoiceMissProb μ c * firstChoiceGapMass μ value c := by
          rfl

/--
First-mover utility minus independent second-mover utility, grouped by the
second mover's first-choice candidate.
-/
theorem expectedFirstMover_sub_secondMoverIndependent_eq_sum_firstChoiceProb_mul_firstChoiceGapMass
    {n : ℕ} (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedFirstMoverUtility μ value - expectedSecondMoverIndependent μ μ value =
      ∑ c : Candidate n,
        firstChoiceProb μ c * firstChoiceGapMass μ value c := by
  classical
  rw [expectedSecondMoverIndependent_eq_expect_top_sub_collision_loss]
  unfold expectedFirstMoverUtility firstChoiceGapMass pmfExp
  calc
    (∑ π : Ranking n, (μ π).toReal * value (firstChoice π)) -
        (∑ π : Ranking n,
          (μ π).toReal *
            (value (firstChoice π) -
              firstChoiceProb μ (firstChoice π) * valueGap value π))
        =
        ∑ π : Ranking n,
          (μ π).toReal *
            (firstChoiceProb μ (firstChoice π) * valueGap value π) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro π _
          ring
    _ = ∑ π : Ranking n,
          (μ π).toReal *
            (∑ c : Candidate n,
              firstChoiceProb μ c *
                (if c = firstChoice π then valueGap value π else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          have hsplit :
              firstChoiceProb μ (firstChoice π) * valueGap value π =
                ∑ c : Candidate n,
                  firstChoiceProb μ c *
                    (if c = firstChoice π then valueGap value π else 0) := by
            calc
              firstChoiceProb μ (firstChoice π) * valueGap value π
                  = ∑ c : Candidate n,
                      if c = firstChoice π
                      then firstChoiceProb μ c * valueGap value π
                      else 0 := by
                        symm
                        simpa using
                          (Finset.sum_ite_eq' Finset.univ (firstChoice π)
                            (fun c : Candidate n =>
                              firstChoiceProb μ c * valueGap value π))
              _ = ∑ c : Candidate n,
                    firstChoiceProb μ c *
                      (if c = firstChoice π then valueGap value π else 0) := by
                    refine Finset.sum_congr rfl ?_
                    intro c _
                    by_cases h : c = firstChoice π <;> simp [h]
          rw [hsplit]
    _ = ∑ π : Ranking n,
          ∑ c : Candidate n,
            (μ π).toReal *
              (firstChoiceProb μ c *
                (if c = firstChoice π then valueGap value π else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          rw [Finset.mul_sum]
    _ = ∑ π : Ranking n,
          ∑ c : Candidate n,
            firstChoiceProb μ c *
              ((μ π).toReal *
                (if c = firstChoice π then valueGap value π else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          refine Finset.sum_congr rfl ?_
          intro c _
          ring
    _ = ∑ c : Candidate n,
          ∑ π : Ranking n,
            firstChoiceProb μ c *
              ((μ π).toReal *
                (if c = firstChoice π then valueGap value π else 0)) := by
          rw [Finset.sum_comm]
    _ = ∑ c : Candidate n,
          firstChoiceProb μ c *
            (∑ π : Ranking n,
              (μ π).toReal *
                (if c = firstChoice π then valueGap value π else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [Finset.mul_sum]
    _ = ∑ c : Candidate n,
          firstChoiceProb μ c * firstChoiceGapMass μ value c := by
          rfl

/--
Collision-loss differences between two first-mover laws, grouped by first-choice
candidate.
-/
theorem expectedCollisionLossDiff_eq_sum_collisionDiff_mul_firstChoiceGapMass
    {n : ℕ} (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ) :
    pmfExp μWorse
      (fun π =>
        (firstChoiceProb μBetter (firstChoice π) -
            firstChoiceProb μWorse (firstChoice π)) * valueGap value π) =
      ∑ c : Candidate n,
        firstChoiceCollisionDiff μBetter μWorse c *
          firstChoiceGapMass μWorse value c := by
  classical
  unfold firstChoiceCollisionDiff firstChoiceGapMass pmfExp
  calc
    ∑ π : Ranking n,
        (μWorse π).toReal *
          ((firstChoiceProb μBetter (firstChoice π) -
              firstChoiceProb μWorse (firstChoice π)) * valueGap value π)
        = ∑ π : Ranking n,
            (μWorse π).toReal *
              (∑ c : Candidate n,
                (firstChoiceProb μBetter c - firstChoiceProb μWorse c) *
                  (if c = firstChoice π then valueGap value π else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          have hsplit :
              (firstChoiceProb μBetter (firstChoice π) -
                  firstChoiceProb μWorse (firstChoice π)) * valueGap value π =
                ∑ c : Candidate n,
                  (firstChoiceProb μBetter c - firstChoiceProb μWorse c) *
                    (if c = firstChoice π then valueGap value π else 0) := by
            calc
              (firstChoiceProb μBetter (firstChoice π) -
                  firstChoiceProb μWorse (firstChoice π)) * valueGap value π
                  = ∑ c : Candidate n,
                      if c = firstChoice π
                      then (firstChoiceProb μBetter c - firstChoiceProb μWorse c) *
                        valueGap value π
                      else 0 := by
                        symm
                        simpa using
                          (Finset.sum_ite_eq' Finset.univ (firstChoice π)
                            (fun c : Candidate n =>
                              (firstChoiceProb μBetter c -
                                  firstChoiceProb μWorse c) *
                                valueGap value π))
              _ = ∑ c : Candidate n,
                    (firstChoiceProb μBetter c - firstChoiceProb μWorse c) *
                      (if c = firstChoice π then valueGap value π else 0) := by
                    refine Finset.sum_congr rfl ?_
                    intro c _
                    by_cases h : c = firstChoice π <;> simp [h]
          rw [hsplit]
    _ = ∑ π : Ranking n,
          ∑ c : Candidate n,
            (μWorse π).toReal *
              ((firstChoiceProb μBetter c - firstChoiceProb μWorse c) *
                (if c = firstChoice π then valueGap value π else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          rw [Finset.mul_sum]
    _ = ∑ π : Ranking n,
          ∑ c : Candidate n,
            (firstChoiceProb μBetter c - firstChoiceProb μWorse c) *
              ((μWorse π).toReal *
                (if c = firstChoice π then valueGap value π else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          refine Finset.sum_congr rfl ?_
          intro c _
          ring
    _ = ∑ c : Candidate n,
          ∑ π : Ranking n,
            (firstChoiceProb μBetter c - firstChoiceProb μWorse c) *
              ((μWorse π).toReal *
                (if c = firstChoice π then valueGap value π else 0)) := by
          rw [Finset.sum_comm]
    _ = ∑ c : Candidate n,
          (firstChoiceProb μBetter c - firstChoiceProb μWorse c) *
            (∑ π : Ranking n,
              (μWorse π).toReal *
                (if c = firstChoice π then valueGap value π else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [Finset.mul_sum]
    _ = ∑ c : Candidate n,
          firstChoiceCollisionDiff μBetter μWorse c *
            firstChoiceGapMass μWorse value c := by
          rfl

/--
Switching the first-mover law changes the second mover's payoff only through
first-choice collision probabilities.
-/
theorem secondMoverFirstLawSwitchGain_eq_expected_collision_loss_diff {n : ℕ}
    (μSecond μFrom μTo : PMF (Ranking n)) (value : Candidate n → ℝ) :
    secondMoverFirstLawSwitchGain μSecond μFrom μTo value =
      pmfExp μSecond
        (fun π =>
          (firstChoiceProb μFrom (firstChoice π) -
              firstChoiceProb μTo (firstChoice π)) * valueGap value π) := by
  classical
  unfold secondMoverFirstLawSwitchGain
  rw [expectedSecondMoverIndependent_eq_expect_top_sub_collision_loss
        (μSecond := μSecond) (μFirst := μTo) (value := value)]
  rw [expectedSecondMoverIndependent_eq_expect_top_sub_collision_loss
        (μSecond := μSecond) (μFirst := μFrom) (value := value)]
  rw [← pmfExp_sub]
  congr 1
  funext π
  ring

/--
If the target first-mover law collides weakly less often with every relevant top
choice, then switching to it weakly increases the second mover's payoff.
-/
theorem secondMoverFirstLawSwitchGain_nonneg_of_collisionProb_le_and_gap_nonneg
    {n : ℕ} (μSecond μFrom μTo : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hprob : ∀ π : Ranking n,
      firstChoiceProb μTo (firstChoice π) ≤ firstChoiceProb μFrom (firstChoice π))
    (hgap : ∀ π : Ranking n, 0 ≤ valueGap value π) :
    0 ≤ secondMoverFirstLawSwitchGain μSecond μFrom μTo value := by
  classical
  rw [secondMoverFirstLawSwitchGain_eq_expected_collision_loss_diff]
  unfold pmfExp
  refine Finset.sum_nonneg ?_
  intro π _
  refine mul_nonneg ENNReal.toReal_nonneg ?_
  refine mul_nonneg ?_ (hgap π)
  exact sub_nonneg.mpr (hprob π)

theorem expectedSecondMoverIndependent_le_of_collisionProb_le_and_gap_nonneg
    {n : ℕ} (μSecond μFrom μTo : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hprob : ∀ π : Ranking n,
      firstChoiceProb μTo (firstChoice π) ≤ firstChoiceProb μFrom (firstChoice π))
    (hgap : ∀ π : Ranking n, 0 ≤ valueGap value π) :
    expectedSecondMoverIndependent μSecond μFrom value ≤
      expectedSecondMoverIndependent μSecond μTo value := by
  have hgain :=
    secondMoverFirstLawSwitchGain_nonneg_of_collisionProb_le_and_gap_nonneg
      (μSecond := μSecond) (μFrom := μFrom) (μTo := μTo) (value := value)
      hprob hgap
  unfold secondMoverFirstLawSwitchGain at hgain
  linarith

/-- Utility-side preference for independent reranking over sharing one realized ranking. -/
def PrefersIndependentReranking {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) : Prop :=
  expectedSecondMoverShared μ value < expectedSecondMoverIndependent μ μ value

/--
The utility-side independent-reranking preference is exactly positivity of the
expected reranking gain.
-/
theorem prefersIndependentReranking_iff_expectedRerankingGain_pos {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    PrefersIndependentReranking μ value ↔ 0 < expectedRerankingGain μ value := by
  unfold PrefersIndependentReranking
  have h := expectedSecondMoverIndependent_sub_shared_eq_expectedRerankingGain
    (μ := μ) (value := value)
  constructor <;> intro hmain <;> linarith

/--
Supportwise positive inner reranking gains imply independent-reranking
preference.
-/
theorem prefersIndependentReranking_of_inner_support_pos {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hinner : ∀ π : Ranking n, 0 < (μ π).toReal →
      0 < pmfExp μ (fun σ => rerankingGainOnPair value π σ)) :
    PrefersIndependentReranking μ value := by
  rw [prefersIndependentReranking_iff_expectedRerankingGain_pos]
  exact expectedRerankingGain_pos_of_inner_support_pos μ value hinner

/--
Candidate-fiber conditional gains imply independent-reranking preference.
-/
theorem prefersIndependentReranking_of_firstChoiceProb_conditional_gain_pos {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hcond : ∀ c : Candidate n,
      0 < firstChoiceProb μ c →
        0 < pmfConditionalExp μ (fun τ => c = firstChoice τ)
          (fun τ =>
            pmfExp μ (fun π =>
              value (bestRemainingAfter π (firstChoice τ)) - value (secondChoice τ)))) :
    PrefersIndependentReranking μ value := by
  rw [prefersIndependentReranking_iff_expectedRerankingGain_pos]
  exact expectedRerankingGain_pos_of_firstChoiceProb_conditional_gain_pos μ value hcond

/-- The second mover's gain from facing `μWorse` rather than `μBetter`. -/
def weakerCompetitionGain {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  expectedSecondMoverIndependent μWorse μWorse value -
    expectedSecondMoverIndependent μWorse μBetter value

/--
Utility-side preference for weaker competition: the second mover does better
when the first mover uses the weaker law.
-/
def PrefersWeakerCompetition {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ) : Prop :=
  expectedSecondMoverIndependent μWorse μBetter value <
    expectedSecondMoverIndependent μWorse μWorse value

theorem prefersWeakerCompetition_mul_value_iff {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ)
    {c : ℝ} (hc : 0 < c) :
    PrefersWeakerCompetition μBetter μWorse (fun i => c * value i) ↔
      PrefersWeakerCompetition μBetter μWorse value := by
  unfold PrefersWeakerCompetition
  rw [expectedSecondMoverIndependent_mul_value,
    expectedSecondMoverIndependent_mul_value]
  constructor
  · intro h
    exact lt_of_mul_lt_mul_left h hc.le
  · intro h
    exact mul_lt_mul_of_pos_left h hc

/-- Preference for weaker competition is positivity of the weaker-competition gain. -/
theorem prefersWeakerCompetition_iff_weakerCompetitionGain_pos {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ) :
    PrefersWeakerCompetition μBetter μWorse value ↔
      0 < weakerCompetitionGain μBetter μWorse value := by
  unfold PrefersWeakerCompetition weakerCompetitionGain
  constructor <;> intro h <;> linarith

/--
First-choice-probability decomposition of weaker-competition gain.
-/
theorem weakerCompetitionGain_eq_expected_collision_loss_diff {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ) :
    weakerCompetitionGain μBetter μWorse value =
      pmfExp μWorse
        (fun π =>
          (firstChoiceProb μBetter (firstChoice π) -
              firstChoiceProb μWorse (firstChoice π)) * valueGap value π) := by
  simpa [weakerCompetitionGain, secondMoverFirstLawSwitchGain] using
    secondMoverFirstLawSwitchGain_eq_expected_collision_loss_diff
      (μSecond := μWorse) (μFrom := μBetter) (μTo := μWorse) (value := value)

/-- Weaker-competition preference through the collision-loss decomposition. -/
theorem prefersWeakerCompetition_iff_expected_collision_loss_diff_pos {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ) :
    PrefersWeakerCompetition μBetter μWorse value ↔
      0 < pmfExp μWorse
        (fun π =>
          (firstChoiceProb μBetter (firstChoice π) -
              firstChoiceProb μWorse (firstChoice π)) * valueGap value π) := by
  rw [prefersWeakerCompetition_iff_weakerCompetitionGain_pos]
  rw [weakerCompetitionGain_eq_expected_collision_loss_diff]

/--
If the better first-mover law collides at least as often with every relevant top
choice and all top-second gaps are nonnegative, then facing the worse law weakly
improves second-mover utility.
-/
theorem weakerCompetitionGain_nonneg_of_collisionProb_le_and_gap_nonneg {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hprob : ∀ π : Ranking n,
      firstChoiceProb μWorse (firstChoice π) ≤ firstChoiceProb μBetter (firstChoice π))
    (hgap : ∀ π : Ranking n, 0 ≤ valueGap value π) :
    0 ≤ weakerCompetitionGain μBetter μWorse value := by
  simpa [weakerCompetitionGain, secondMoverFirstLawSwitchGain] using
    secondMoverFirstLawSwitchGain_nonneg_of_collisionProb_le_and_gap_nonneg
      (μSecond := μWorse) (μFrom := μBetter) (μTo := μWorse) (value := value)
      hprob hgap

/-- Utility-side weaker-competition monotonicity corollary. -/
theorem expectedSecondMoverIndependent_le_self_of_collisionProb_le_and_gap_nonneg {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hprob : ∀ π : Ranking n,
      firstChoiceProb μWorse (firstChoice π) ≤ firstChoiceProb μBetter (firstChoice π))
    (hgap : ∀ π : Ranking n, 0 ≤ valueGap value π) :
    expectedSecondMoverIndependent μWorse μBetter value ≤
      expectedSecondMoverIndependent μWorse μWorse value :=
  expectedSecondMoverIndependent_le_of_collisionProb_le_and_gap_nonneg
    (μSecond := μWorse) (μFrom := μBetter) (μTo := μWorse) (value := value)
    hprob hgap

/-- Candidate-sum version of the independent-reranking preference. -/
theorem prefersIndependentReranking_iff_firstChoiceGapMassSum_pos {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    PrefersIndependentReranking μ value ↔
      0 < ∑ c : Candidate n,
        firstChoiceMissProb μ c * firstChoiceGapMass μ value c := by
  rw [prefersIndependentReranking_iff_expectedRerankingGain_pos]
  rw [expectedRerankingGain_eq_sum_firstChoiceMissProb_mul_firstChoiceGapMass]

/-- Weaker-competition gain grouped by first-choice candidate. -/
theorem weakerCompetitionGain_eq_sum_collisionDiff_mul_firstChoiceGapMass
    {n : ℕ} (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ) :
    weakerCompetitionGain μBetter μWorse value =
      ∑ c : Candidate n,
        firstChoiceCollisionDiff μBetter μWorse c *
          firstChoiceGapMass μWorse value c := by
  rw [weakerCompetitionGain_eq_expected_collision_loss_diff]
  exact expectedCollisionLossDiff_eq_sum_collisionDiff_mul_firstChoiceGapMass
    (μBetter := μBetter) (μWorse := μWorse) (value := value)

/-- Candidate-sum version of weaker-competition preference. -/
theorem prefersWeakerCompetition_iff_firstChoiceCollisionDiffSum_pos {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ) :
    PrefersWeakerCompetition μBetter μWorse value ↔
      0 < ∑ c : Candidate n,
        firstChoiceCollisionDiff μBetter μWorse c *
          firstChoiceGapMass μWorse value c := by
  rw [prefersWeakerCompetition_iff_weakerCompetitionGain_pos]
  rw [weakerCompetitionGain_eq_sum_collisionDiff_mul_firstChoiceGapMass]

/-- Expected welfare when both firms are forced to use the same ranking draw. -/
def expectedWelfareShared {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  pmfExp μ (fun π => welfareOrdered value π π)

/-- Shared-ranking welfare is first-position utility plus second-position utility. -/
theorem expectedWelfareShared_eq_firstMover_add_secondMoverShared {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedWelfareShared μ value =
      expectedFirstMoverUtility μ value + expectedSecondMoverShared μ value := by
  unfold expectedWelfareShared expectedFirstMoverUtility expectedSecondMoverShared
  rw [← pmfExp_add]
  congr 1
  funext π
  simp [welfareOrdered]

/--
Ordered independent welfare decomposes into first-mover expected utility plus
second-mover independent-ranking utility.
-/
theorem expectedWelfareOrdered_eq_firstMover_add_secondMoverIndependent {n : ℕ}
    (μ₂ μ₁ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedWelfareOrdered μ₂ μ₁ value =
      expectedFirstMoverUtility μ₁ value + expectedSecondMoverIndependent μ₂ μ₁ value := by
  unfold expectedWelfareOrdered welfareOrdered expectedFirstMoverUtility
    expectedSecondMoverIndependent
  rw [pmfPairExp_add]
  rw [pmfPairExp_ignore_left]

/--
For a single ranking law, the welfare gain from independent reranking over a
shared ranking is exactly expected reranking gain.
-/
theorem expectedWelfareOrdered_self_sub_expectedWelfareShared_eq_expectedRerankingGain
    {n : ℕ} (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedWelfareOrdered μ μ value - expectedWelfareShared μ value =
      expectedRerankingGain μ value := by
  rw [expectedWelfareOrdered_eq_firstMover_add_secondMoverIndependent]
  rw [expectedWelfareShared_eq_firstMover_add_secondMoverShared]
  have h := expectedSecondMoverIndependent_sub_shared_eq_expectedRerankingGain
    (μ := μ) (value := value)
  linarith

/-- Additive version of the shared-vs-independent welfare decomposition. -/
theorem expectedWelfareOrdered_self_eq_expectedWelfareShared_add_expectedRerankingGain
    {n : ℕ} (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedWelfareOrdered μ μ value =
      expectedWelfareShared μ value + expectedRerankingGain μ value := by
  have h := expectedWelfareOrdered_self_sub_expectedWelfareShared_eq_expectedRerankingGain
    (μ := μ) (value := value)
  linarith

/-- A pair of ranking draws. -/
abbrev RankingPair (n : ℕ) := Ranking n × Ranking n

/-- The event that two rankings disagree on the first-position candidate. -/
def disagreementEvent {n : ℕ} : RankingPair n → Prop :=
  fun p => firstChoice p.1 ≠ firstChoice p.2

instance decidableDisagreementEvent {n : ℕ} :
    DecidablePred (@disagreementEvent n) := by
  intro p
  unfold disagreementEvent
  infer_instance

/-- The reranking-gain integrand viewed as a function on ranking pairs. -/
def pairRerankingGain {n : ℕ} (value : Candidate n → ℝ) :
    RankingPair n → ℝ :=
  fun p => rerankingGainOnPair value p.1 p.2

/-- Probability that two i.i.d. ranking draws disagree on the first choice. -/
def disagreementProb {n : ℕ} (μ : PMF (Ranking n)) : ℝ :=
  pmfPairProb μ μ disagreementEvent

/-- Conditional expected reranking gain given first-choice disagreement. -/
def disagreementConditionalGain {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  pmfPairConditionalExp μ μ disagreementEvent (pairRerankingGain value)

@[simp] theorem pairRerankingGain_apply {n : ℕ} (value : Candidate n → ℝ)
    (π σ : Ranking n) :
    pairRerankingGain value (π, σ) = rerankingGainOnPair value π σ := rfl

/-- Since reranking gain is zero on agreement, the disagreement indicator is exact. -/
theorem expectedRerankingGain_eq_pairIndicatorExp {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedRerankingGain μ value =
      pmfPairIndicatorExp μ μ disagreementEvent (pairRerankingGain value) := by
  unfold expectedRerankingGain pmfPairIndicatorExp pmfPairExp pmfExp
    disagreementEvent pairRerankingGain
  refine Finset.sum_congr rfl ?_
  intro π _
  congr 1
  refine Finset.sum_congr rfl ?_
  intro σ _
  by_cases h : firstChoice π = firstChoice σ
  · have h' : π 0 = σ 0 := by simpa [firstChoice] using h
    simp [rerankingGainOnPair, firstChoice, h']
  · have h' : π 0 ≠ σ 0 := by simpa [firstChoice] using h
    simp [rerankingGainOnPair, firstChoice, secondChoice, h']

/-- On a positive-probability disagreement event, conditional gain is a ratio. -/
theorem disagreementConditionalGain_eq_expectedRerankingGain_div_of_pos {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (h : 0 < disagreementProb μ) :
    disagreementConditionalGain μ value =
      expectedRerankingGain μ value / disagreementProb μ := by
  unfold disagreementConditionalGain disagreementProb at *
  rw [pmfPairConditionalExp_eq_div_of_pos (μ := μ) (ν := μ)
    (p := disagreementEvent) (f := pairRerankingGain value) h]
  rw [← expectedRerankingGain_eq_pairIndicatorExp (μ := μ) (value := value)]

/--
Positive independent-reranking preference is equivalent to positive conditional
gain on disagreement, when disagreement has positive probability.
-/
theorem prefersIndependentReranking_iff_conditionalGain_pos_of_disagreementPos {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (h : 0 < disagreementProb μ) :
    PrefersIndependentReranking μ value ↔ 0 < disagreementConditionalGain μ value := by
  rw [prefersIndependentReranking_iff_expectedRerankingGain_pos]
  rw [disagreementConditionalGain_eq_expectedRerankingGain_div_of_pos
    (μ := μ) (value := value) h]
  exact (zero_lt_div_iff_pos_right h).symm

@[simp] theorem disagreementProb_pure {n : ℕ} (π : Ranking n) :
    disagreementProb (PMF.pure π) = 0 := by
  unfold disagreementProb pmfPairProb disagreementEvent
  simp [firstChoice]

@[simp] theorem disagreementConditionalGain_pure {n : ℕ}
    (π : Ranking n) (value : Candidate n → ℝ) :
    disagreementConditionalGain (PMF.pure π) value = 0 := by
  unfold disagreementConditionalGain
  rw [pmfPairConditionalExp_of_prob_zero]
  exact disagreementProb_pure (π := π)

/-- Independent reranking has zero gain if all relevant miss probabilities vanish. -/
theorem expectedRerankingGain_eq_zero_of_all_missProb_zero {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hmiss : ∀ π : Ranking n, firstChoiceMissProb μ (firstChoice π) = 0) :
    expectedRerankingGain μ value = 0 := by
  classical
  rw [expectedRerankingGain_eq_expect_missProb_mul_gap]
  unfold pmfExp
  refine Finset.sum_eq_zero ?_
  intro π _
  have hπ : firstChoiceMissProb μ (π 0) = 0 := by
    simpa [firstChoice] using hmiss π
  simp [hπ]

/-- Independent reranking has zero gain if all top-vs-runner-up value gaps vanish. -/
theorem expectedRerankingGain_eq_zero_of_all_valueGap_zero {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hgap : ∀ π : Ranking n, valueGap value π = 0) :
    expectedRerankingGain μ value = 0 := by
  classical
  rw [expectedRerankingGain_eq_expect_missProb_mul_gap]
  unfold pmfExp
  simp [hgap]

/-- Zero miss probability collapses independent and shared second-mover utility. -/
theorem expectedSecondMoverIndependent_eq_shared_of_all_missProb_zero {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hmiss : ∀ π : Ranking n, firstChoiceMissProb μ (firstChoice π) = 0) :
    expectedSecondMoverIndependent μ μ value = expectedSecondMoverShared μ value := by
  have hgain := expectedRerankingGain_eq_zero_of_all_missProb_zero
    (μ := μ) (value := value) hmiss
  have hmain := expectedSecondMoverIndependent_sub_shared_eq_expectedRerankingGain
    (μ := μ) (value := value)
  linarith

/-- Zero value gaps collapse independent and shared second-mover utility. -/
theorem expectedSecondMoverIndependent_eq_shared_of_all_valueGap_zero {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hgap : ∀ π : Ranking n, valueGap value π = 0) :
    expectedSecondMoverIndependent μ μ value = expectedSecondMoverShared μ value := by
  have hgain := expectedRerankingGain_eq_zero_of_all_valueGap_zero
    (μ := μ) (value := value) hgap
  have hmain := expectedSecondMoverIndependent_sub_shared_eq_expectedRerankingGain
    (μ := μ) (value := value)
  linarith

/-- No independent-reranking preference is possible when miss probabilities vanish. -/
theorem not_prefersIndependentReranking_of_all_missProb_zero {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hmiss : ∀ π : Ranking n, firstChoiceMissProb μ (firstChoice π) = 0) :
    ¬ PrefersIndependentReranking μ value := by
  intro hpref
  rw [prefersIndependentReranking_iff_expectedRerankingGain_pos] at hpref
  have hgain := expectedRerankingGain_eq_zero_of_all_missProb_zero
    (μ := μ) (value := value) hmiss
  linarith

/-- No independent-reranking preference is possible when every top-second gap is zero. -/
theorem not_prefersIndependentReranking_of_all_valueGap_zero {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hgap : ∀ π : Ranking n, valueGap value π = 0) :
    ¬ PrefersIndependentReranking μ value := by
  intro hpref
  rw [prefersIndependentReranking_iff_expectedRerankingGain_pos] at hpref
  have hgain := expectedRerankingGain_eq_zero_of_all_valueGap_zero
    (μ := μ) (value := value) hgap
  linarith

/--
Three-candidate first-mover monotonicity from first-choice probability shifts.

If the better law strictly gains probability on the highest-valued candidate and
does not gain probability on the lowest-valued candidate, then the expected
first-mover value strictly increases.  The middle-candidate probability change
is eliminated by total first-choice mass conservation.
-/
theorem expectedFirstMoverUtility_lt_of_fin3_top_gain_bottom_nongain
    (μBetter μWorse : PMF (Ranking 1)) (value : Candidate 1 → ℝ)
    {x1 x2 x3 : ℝ}
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (htop :
      0 <
        firstChoiceProb μBetter (0 : Candidate 1) -
          firstChoiceProb μWorse (0 : Candidate 1))
    (hbottom :
      firstChoiceProb μBetter (2 : Candidate 1) -
          firstChoiceProb μWorse (2 : Candidate 1) ≤ 0) :
    expectedFirstMoverUtility μWorse value <
      expectedFirstMoverUtility μBetter value := by
  classical
  let d0 : ℝ :=
    firstChoiceProb μBetter (0 : Candidate 1) -
      firstChoiceProb μWorse (0 : Candidate 1)
  let d1 : ℝ :=
    firstChoiceProb μBetter (1 : Candidate 1) -
      firstChoiceProb μWorse (1 : Candidate 1)
  let d2 : ℝ :=
    firstChoiceProb μBetter (2 : Candidate 1) -
      firstChoiceProb μWorse (2 : Candidate 1)
  have hbetter_sum :
      firstChoiceProb μBetter (0 : Candidate 1) +
          firstChoiceProb μBetter (1 : Candidate 1) +
          firstChoiceProb μBetter (2 : Candidate 1) = 1 := by
    have hsum := sum_firstChoiceProb_eq_one (μ := μBetter) (n := 1)
    change (∑ c : Fin 3, firstChoiceProb μBetter c) = 1 at hsum
    rw [Fin.sum_univ_three] at hsum
    exact hsum
  have hworse_sum :
      firstChoiceProb μWorse (0 : Candidate 1) +
          firstChoiceProb μWorse (1 : Candidate 1) +
          firstChoiceProb μWorse (2 : Candidate 1) = 1 := by
    have hsum := sum_firstChoiceProb_eq_one (μ := μWorse) (n := 1)
    change (∑ c : Fin 3, firstChoiceProb μWorse c) = 1 at hsum
    rw [Fin.sum_univ_three] at hsum
    exact hsum
  have hd_sum : d0 + d1 + d2 = 0 := by
    dsimp [d0, d1, d2]
    linarith
  have hdiff :
      expectedFirstMoverUtility μBetter value -
          expectedFirstMoverUtility μWorse value =
        d0 * x1 + d1 * x2 + d2 * x3 := by
    rw [expectedFirstMoverUtility_eq_sum_firstChoiceProb μBetter value]
    rw [expectedFirstMoverUtility_eq_sum_firstChoiceProb μWorse value]
    change
      (∑ c : Fin 3, firstChoiceProb μBetter c * value c) -
          (∑ c : Fin 3, firstChoiceProb μWorse c * value c) =
        d0 * x1 + d1 * x2 + d2 * x3
    rw [Fin.sum_univ_three]
    rw [Fin.sum_univ_three]
    simp [d0, d1, d2, hvalue1, hvalue2, hvalue3]
    ring_nf
  have hdelta_pos : 0 < d0 * (x1 - x2) := by
    exact mul_pos (by simpa [d0] using htop) (sub_pos.mpr hx12)
  have hbottom_term_nonneg : 0 ≤ d2 * (x3 - x2) := by
    exact mul_nonneg_of_nonpos_of_nonpos
      (by simpa [d2] using hbottom)
      (le_of_lt (sub_neg.mpr hx23))
  have halg :
      d0 * x1 + d1 * x2 + d2 * x3 =
        d0 * (x1 - x2) + d2 * (x3 - x2) := by
    have hd1_eq : d1 = -d0 - d2 := by linarith
    rw [hd1_eq]
    ring
  have hpos : 0 < d0 * x1 + d1 * x2 + d2 * x3 := by
    rw [halg]
    linarith
  linarith

end

end Ranking
end SocialChoice
end AppliedModelingLib
