import AppliedModelingLib.Learning.HumanFeedback.RewardEquivalence
import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-!
# Finite Plackett--Luce choice kernels

The Plackett--Luce ranking model chooses an item from each remaining finite
set with probability proportional to the exponential of its score.  This file
records that finite conditional-choice kernel and its invariance under the
context-only reward shifts that define reward equivalence.  Sequential ranking
likelihoods are products of these kernels, so this is the reusable local
ingredient behind the Plackett--Luce part of DPO Lemma 1.
-/

open scoped BigOperators

namespace AppliedModelingLib
namespace Learning
namespace HumanFeedback

/--
The Plackett--Luce conditional probability of selecting `candidate` from the
currently available finite set.  Candidates outside the set have probability
zero; on a nonempty available set this is the usual softmax choice rule.
-/
noncomputable def plackettLuceChoiceProbability
    {Context Response : Type*} [DecidableEq Response]
    (reward : Context → Response → ℝ) (context : Context)
    (available : Finset Response) (candidate : Response) : ℝ :=
  if candidate ∈ available then
    Real.exp (reward context candidate) /
      ∑ response ∈ available, Real.exp (reward context response)
  else 0

/--
On a nonempty finite available set, the Plackett--Luce choice kernel is a
probability distribution: its candidate weights sum to one.
-/
theorem sum_plackettLuceChoiceProbability_eq_one
    {Context Response : Type*} [DecidableEq Response]
    (reward : Context → Response → ℝ) (context : Context)
    (available : Finset Response) (hnonempty : available.Nonempty) :
    ∑ candidate ∈ available,
      plackettLuceChoiceProbability reward context available candidate = 1 := by
  have htermNonneg : ∀ candidate ∈ available,
      0 ≤ Real.exp (reward context candidate) := by
    intro candidate _
    exact (Real.exp_pos _).le
  obtain ⟨candidate, hcandidate⟩ := hnonempty
  have hsumPos : 0 < ∑ response ∈ available, Real.exp (reward context response) :=
    Finset.sum_pos' htermNonneg ⟨candidate, hcandidate, Real.exp_pos _⟩
  calc
    ∑ candidate ∈ available,
        plackettLuceChoiceProbability reward context available candidate =
        ∑ candidate ∈ available,
          Real.exp (reward context candidate) /
            ∑ response ∈ available, Real.exp (reward context response) := by
      apply Finset.sum_congr rfl
      intro candidate hcandidate
      simp [plackettLuceChoiceProbability, hcandidate]
    _ = (∑ candidate ∈ available, Real.exp (reward context candidate)) /
          ∑ response ∈ available, Real.exp (reward context response) := by
      rw [Finset.sum_div]
    _ = 1 := div_self (ne_of_gt hsumPos)

/--
Context-only reward shifts leave every finite Plackett--Luce conditional
choice probability unchanged.  The common exponential factor cancels from
the numerator and the available-set normalizer.
-/
theorem plackettLuceChoiceProbability_invariant
    {Context Response : Type*} [DecidableEq Response]
    {first second : Context → Response → ℝ}
    (h : RewardEquivalent first second) :
    ∀ context (available : Finset Response) candidate,
      plackettLuceChoiceProbability second context available candidate =
        plackettLuceChoiceProbability first context available candidate := by
  rcases h with ⟨shift, hshift⟩
  intro context available candidate
  by_cases hcandidate : candidate ∈ available
  · have hterm : ∀ response : Response,
        Real.exp (second context response) =
          Real.exp (first context response) * Real.exp (shift context) := by
      intro response
      rw [hshift context response, Real.exp_add]
    have hsum :
        (∑ response ∈ available, Real.exp (second context response)) =
          (∑ response ∈ available, Real.exp (first context response)) *
            Real.exp (shift context) := by
      calc
        (∑ response ∈ available, Real.exp (second context response)) =
            ∑ response ∈ available,
              Real.exp (first context response) * Real.exp (shift context) := by
                apply Finset.sum_congr rfl
                intro response _
                exact hterm response
        _ = (∑ response ∈ available, Real.exp (first context response)) *
              Real.exp (shift context) := by
                rw [Finset.sum_mul]
    unfold plackettLuceChoiceProbability
    rw [if_pos hcandidate, if_pos hcandidate, hterm candidate, hsum,
      mul_div_mul_right _ _ (Real.exp_ne_zero _)]
  · simp [plackettLuceChoiceProbability, hcandidate]

/--
The sequential Plackett--Luce likelihood assigned to a proposed ranking list.
At position `i`, the available set is the suffix beginning at `i`.  For a
duplicate-free complete list this is the usual complete-ranking likelihood;
the definition remains total for arbitrary finite lists so it is convenient
for later source-specific ranking carriers.
-/
noncomputable def plackettLuceRankingLikelihood
    {Context Response : Type*} [DecidableEq Response]
    (reward : Context → Response → ℝ) (context : Context)
    (ranking : List Response) : ℝ :=
  match ranking with
  | [] => 1
  | candidate :: remaining =>
      plackettLuceChoiceProbability reward context ranking.toFinset candidate *
        plackettLuceRankingLikelihood reward context remaining

/--
Reward-equivalent scores assign the same likelihood to every finite
Plackett--Luce ranking list, by equality of every sequential choice factor.
-/
theorem plackettLuceRankingLikelihood_invariant
    {Context Response : Type*} [DecidableEq Response]
    {first second : Context → Response → ℝ}
    (h : RewardEquivalent first second) (context : Context) (ranking : List Response) :
    plackettLuceRankingLikelihood second context ranking =
      plackettLuceRankingLikelihood first context ranking := by
  induction ranking with
  | nil => rfl
  | cons candidate remaining ih =>
      simp only [plackettLuceRankingLikelihood]
      rw [plackettLuceChoiceProbability_invariant h context
        (candidate :: remaining).toFinset candidate, ih]

/--
For two distinct available items, the Plackett--Luce choice probability is the
logistic link applied to their scaled score difference.  This is the exact
`K = 2` reduction used when a ranking oracle specializes to a pairwise
comparison oracle.
-/
theorem plackettLuceChoiceProbability_pair_eq_logisticDifference
    {Context Response : Type*} [DecidableEq Response]
    (score : Context → Response → ℝ) (eta : ℝ) (context : Context)
    (first second : Response) (hne : first ≠ second) :
    plackettLuceChoiceProbability
        (fun context response ↦ eta * score context response)
        context {first, second} first =
      Real.exp (eta * (score context first - score context second)) /
        (Real.exp (eta * (score context first - score context second)) + 1) := by
  simp only [plackettLuceChoiceProbability, Finset.mem_insert, true_or,
    if_true, Finset.sum_insert, Finset.mem_singleton, hne, not_false_eq_true,
    Finset.sum_singleton]
  have hfirst : Real.exp (eta * score context first) ≠ 0 := Real.exp_ne_zero _
  have hsecond : Real.exp (eta * score context second) ≠ 0 := Real.exp_ne_zero _
  rw [show eta * (score context first - score context second) =
      eta * score context first - eta * score context second by ring, Real.exp_sub]
  field_simp

/--
The logistic link with positive inverse temperature has an explicit derivative
floor on `[-H,H]`.  The source states this scale as
`Theta (eta * exp (-eta * H))`; the factor `1/4` below is a concrete global
constant and therefore realizes that informal asymptotic claim.
-/
theorem scaledSigmoid_deriv_lowerBound_Icc
    (eta horizon x : ℝ) (heta : 0 < eta) (hhorizon : 0 ≤ horizon)
    (hx : x ∈ Set.Icc (-horizon) horizon) :
    eta * Real.exp (-eta * horizon) / 4 ≤
      deriv (fun y : ℝ ↦ Real.sigmoid (eta * y)) x := by
  have ha : 0 ≤ eta * horizon := mul_nonneg heta.le hhorizon
  have hz : eta * x ∈ Set.Icc (-(eta * horizon)) (eta * horizon) := by
    constructor <;> nlinarith [hx.1, hx.2]
  have hsigmaEndpoint : Real.exp (-(eta * horizon)) / 2 ≤
      Real.sigmoid (-(eta * horizon)) := by
    rw [← Real.sigmoid_mul_rexp_neg (eta * horizon)]
    have hhalf : (1 : ℝ) / 2 ≤ Real.sigmoid (eta * horizon) := by
      calc
        (1 : ℝ) / 2 = Real.sigmoid 0 := by norm_num [Real.sigmoid_zero]
        _ ≤ Real.sigmoid (eta * horizon) := Real.sigmoid_le ha
    have hexp : 0 ≤ Real.exp (-(eta * horizon)) := (Real.exp_pos _).le
    nlinarith
  have hsigmaLower : Real.exp (-(eta * horizon)) / 2 ≤
      Real.sigmoid (eta * x) :=
    hsigmaEndpoint.trans (Real.sigmoid_le hz.1)
  have honeSubLower : Real.exp (-(eta * horizon)) / 2 ≤
      1 - Real.sigmoid (eta * x) := by
    rw [← Real.sigmoid_neg]
    exact hsigmaEndpoint.trans (Real.sigmoid_le (by linarith [hz.2]))
  have hproduct : Real.exp (-(eta * horizon)) / 4 ≤
      Real.sigmoid (eta * x) * (1 - Real.sigmoid (eta * x)) := by
    rcases le_total 0 (eta * x) with hnonneg | hnonpos
    · have hhalf : (1 : ℝ) / 2 ≤ Real.sigmoid (eta * x) := by
        calc
          (1 : ℝ) / 2 = Real.sigmoid 0 := by norm_num [Real.sigmoid_zero]
          _ ≤ Real.sigmoid (eta * x) := Real.sigmoid_le hnonneg
      have honeNonneg : 0 ≤ 1 - Real.sigmoid (eta * x) :=
        sub_nonneg.mpr (Real.sigmoid_le_one _)
      have hexpPos : 0 < Real.exp (-(eta * horizon)) := Real.exp_pos _
      nlinarith
    · have hhalf : (1 : ℝ) / 2 ≤ 1 - Real.sigmoid (eta * x) := by
        rw [← Real.sigmoid_neg]
        calc
          (1 : ℝ) / 2 = Real.sigmoid 0 := by norm_num [Real.sigmoid_zero]
          _ ≤ Real.sigmoid (-(eta * x)) := Real.sigmoid_le (by linarith)
      have hsigmaNonneg := Real.sigmoid_nonneg (eta * x)
      have hexpPos : 0 < Real.exp (-(eta * horizon)) := Real.exp_pos _
      nlinarith
  have hderiv : deriv (fun y : ℝ ↦ Real.sigmoid (eta * y)) x =
      (Real.sigmoid (eta * x) * (1 - Real.sigmoid (eta * x))) * eta := by
    convert ((Real.hasDerivAt_sigmoid (eta * x)).comp x
      ((hasDerivAt_id x).const_mul eta)).deriv using 1 <;> ring
  rw [hderiv]
  have hscaled := mul_le_mul_of_nonneg_right hproduct heta.le
  calc
    eta * Real.exp (-eta * horizon) / 4 =
        Real.exp (-(eta * horizon)) / 4 * eta := by ring
    _ ≤ Real.sigmoid (eta * x) * (1 - Real.sigmoid (eta * x)) * eta := hscaled

end HumanFeedback
end Learning
end AppliedModelingLib
