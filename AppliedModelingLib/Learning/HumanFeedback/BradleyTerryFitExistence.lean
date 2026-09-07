import AppliedModelingLib.Foundations.Optimization.Certificate
import AppliedModelingLib.Foundations.Math.FiniteOptimization
import AppliedModelingLib.Learning.HumanFeedback.BradleyTerryFit
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Existence of finite Bradley--Terry population fits

The finite Bradley--Terry objective is invariant under a common reward shift.
For a full-support sampling law and full-support comparison probabilities, its
restriction to a reference-normalized score cube is coercive.  Compactness
then supplies an attained global population maximum.

## Main declarations

- `referenceNormalizeReward`
- `bradleyTerryFitObjective_referenceNormalize`
- `exists_bradleyTerryFit_globalMax`
-/

namespace AppliedModelingLib
namespace Learning
namespace HumanFeedback

open scoped BigOperators

noncomputable section

/-- Subtract the reference reward from every coordinate. -/
def referenceNormalizeReward {Response : Type*}
    (reference : Response) (reward : Response → ℝ) : Response → ℝ :=
  fun response => reward response - reward reference

/-- Reference normalization fixes the selected coordinate at zero. -/
@[simp] theorem referenceNormalizeReward_apply_reference
    {Response : Type*} (reference : Response) (reward : Response → ℝ) :
    referenceNormalizeReward reference reward reference = 0 := by
  simp [referenceNormalizeReward]

/-- A common reference normalization preserves every Bradley--Terry gap. -/
theorem referenceNormalizeReward_sub
    {Response : Type*} (reference : Response) (reward : Response → ℝ)
    (first second : Response) :
    referenceNormalizeReward reference reward first -
      referenceNormalizeReward reference reward second = reward first - reward second := by
  simp only [referenceNormalizeReward]
  ring

/-- The population fit objective is invariant under reference normalization. -/
theorem bradleyTerryFitObjective_referenceNormalize
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response) (sampling : PMF Response)
    (reference : Response) (reward : Response → ℝ) :
    bradleyTerryFitObjective preference sampling (referenceNormalizeReward reference reward) =
      bradleyTerryFitObjective preference sampling reward := by
  unfold bradleyTerryFitObjective pmfPairExp
  apply pmfExp_congr
  intro first
  unfold pmfExp
  apply Finset.sum_congr rfl
  intro second _
  change (sampling second).toReal *
      (preference.prob () first second *
        Real.log (Real.sigmoid
          (referenceNormalizeReward reference reward first -
            referenceNormalizeReward reference reward second))) =
    (sampling second).toReal *
      (preference.prob () first second *
        Real.log (Real.sigmoid (reward first - reward second)))
  rw [referenceNormalizeReward_sub]

/-- The finite Bradley--Terry objective is continuous in its reward vector. -/
theorem continuous_bradleyTerryFitObjective
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response) (sampling : PMF Response) :
    Continuous (bradleyTerryFitObjective preference sampling) := by
  unfold bradleyTerryFitObjective pmfPairExp pmfExp
  apply continuous_finset_sum
  intro first _
  apply Continuous.const_mul
  apply continuous_finset_sum
  intro second _
  apply Continuous.const_mul
  apply Continuous.const_mul
  have hsigmoid : Continuous (fun reward : Response → ℝ =>
      Real.sigmoid (reward first - reward second)) :=
    continuous_sigmoid.comp
      ((continuous_apply first).sub (continuous_apply second))
  exact hsigmoid.log fun reward => ne_of_gt (Real.sigmoid_pos _)

/-- Every individual finite Bradley--Terry log-likelihood term is nonpositive. -/
theorem bradleyTerryFitTerm_nonpos
    {Response : Type*} (preference : PairwisePreference PUnit Response)
    (sampling : PMF Response) (reward : Response → ℝ) (first second : Response) :
    (sampling first).toReal * (sampling second).toReal * preference.prob () first second *
        Real.log (Real.sigmoid (reward first - reward second)) ≤ 0 := by
  apply mul_nonpos_of_nonneg_of_nonpos
  · exact mul_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (preference.nonneg () first second)
  · apply Real.log_nonpos
    · exact Real.sigmoid_nonneg _
    · exact Real.sigmoid_le_one _

/-- The full objective is bounded above by any one of its positive-weight terms. -/
theorem bradleyTerryFitObjective_le_term
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response) (sampling : PMF Response)
    (reward : Response → ℝ) (first second : Response) :
    bradleyTerryFitObjective preference sampling reward ≤
      (sampling first).toReal * (sampling second).toReal * preference.prob () first second *
        Real.log (Real.sigmoid (reward first - reward second)) := by
  classical
  unfold bradleyTerryFitObjective pmfPairExp pmfExp
  let term : Response → Response → ℝ := fun left right =>
    (sampling left).toReal * (sampling right).toReal * preference.prob () left right *
      Real.log (Real.sigmoid (reward left - reward right))
  have hpoint : ∀ left right : Response,
      term left right ≤ if left = first ∧ right = second then term left right else 0 := by
    intro left right
    by_cases hkey : left = first ∧ right = second
    · simp [hkey]
    · simp only [if_neg hkey]
      exact bradleyTerryFitTerm_nonpos preference sampling reward left right
  calc
    (∑ left : Response, (sampling left).toReal *
      ∑ right : Response, (sampling right).toReal *
        (preference.prob () left right *
          Real.log (Real.sigmoid (reward left - reward right)))) =
        ∑ left : Response, ∑ right : Response, term left right := by
          apply Finset.sum_congr rfl
          intro left _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro right _
          dsimp [term]
          ring
    _ ≤ ∑ left : Response, ∑ right : Response,
        if left = first ∧ right = second then term left right else 0 := by
          apply Finset.sum_le_sum
          intro left _
          apply Finset.sum_le_sum
          intro right _
          exact hpoint left right
    _ = term first second := by
      rw [Finset.sum_eq_single first]
      · rw [Finset.sum_eq_single second]
        · simp [term]
        · intro other _ hne
          simp [hne]
        · simp
      · intro other _ hne
        simp [hne]
      · simp

/-- The logistic log likelihood can be made smaller than any real threshold. -/
theorem exists_pos_log_sigmoid_neg_lt (target : ℝ) :
    ∃ bound : ℝ, 0 < bound ∧ Real.log (Real.sigmoid (-bound)) < target := by
  have hneighborhood : Set.Iio (Real.exp target) ∈ nhds (0 : ℝ) :=
    Iio_mem_nhds (Real.exp_pos target)
  have hsmall : ∀ᶠ gap in Filter.atBot, Real.sigmoid gap < Real.exp target :=
    Real.tendsto_sigmoid_atBot.eventually hneighborhood
  obtain ⟨gap, hgap, hnegative⟩ :=
    (hsmall.and (Filter.eventually_le_atBot (-1 : ℝ))).exists
  refine ⟨-gap, by linarith, ?_⟩
  have hlog : Real.log (Real.sigmoid gap) < Real.log (Real.exp target) :=
    Real.strictMonoOn_log (Real.sigmoid_pos gap)
      (Real.exp_pos target) hgap
  calc
    Real.log (Real.sigmoid (- -gap)) = Real.log (Real.sigmoid gap) := by ring_nf
    _ < Real.log (Real.exp target) := hlog
    _ = target := Real.log_exp target

/-- The positive coefficient multiplying a single ordered-pair fit term. -/
noncomputable def bradleyTerryFitTermWeight {Response : Type*}
    (preference : PairwisePreference PUnit Response) (sampling : PMF Response)
    (first second : Response) : ℝ :=
  (sampling first).toReal * (sampling second).toReal * preference.prob () first second

/-- Every comparison coefficient is positive under full-support sampling and preferences. -/
theorem bradleyTerryFitTermWeight_pos
    {Response : Type*} [DecidableEq Response]
    (preference : PairwisePreference PUnit Response) (sampling : PMF Response)
    (hsampling : PMFFullSupport sampling)
    (hpreference : ∀ first second : Response, first ≠ second →
      0 < preference.prob () first second)
    (first second : Response) :
    0 < bradleyTerryFitTermWeight preference sampling first second := by
  unfold bradleyTerryFitTermWeight
  apply mul_pos (mul_pos (hsampling first) (hsampling second))
  by_cases hsame : first = second
  · subst second
    rw [pairwisePreference_self_eq_half]
    norm_num
  · exact hpreference first second hsame

/--
Finite full-support Bradley--Terry population likelihoods attain a global
maximum.  The source's translation invariance is handled by normalizing one
reference reward, after which a compact score cube contains every maximizer.
-/
theorem exists_bradleyTerryFit_globalMax
    {Response : Type*} [Fintype Response] [DecidableEq Response] [Nonempty Response]
    (preference : PairwisePreference PUnit Response) (sampling : PMF Response)
    (hsampling : PMFFullSupport sampling)
    (hpreference : ∀ first second : Response, first ≠ second →
      0 < preference.prob () first second) :
    ∃ reward : Response → ℝ, ∀ candidate : Response → ℝ,
      bradleyTerryFitObjective preference sampling candidate ≤
        bradleyTerryFitObjective preference sampling reward := by
  classical
  let reference : Response := Classical.choice inferInstance
  let weight : Response × Response → ℝ := fun pair =>
    bradleyTerryFitTermWeight preference sampling pair.1 pair.2
  have hweight_pos : ∀ pair : Response × Response, 0 < weight pair := by
    rintro ⟨first, second⟩
    exact bradleyTerryFitTermWeight_pos preference sampling hsampling hpreference first second
  let minWeight : ℝ := finiteMin weight
  have hminWeight_pos : 0 < minWeight := finiteMin_pos weight hweight_pos
  let zeroObjective : ℝ := bradleyTerryFitObjective preference sampling 0
  obtain ⟨bound, hbound_pos, htail⟩ :=
    exists_pos_log_sigmoid_neg_lt (zeroObjective / minWeight)
  let cube : Set (Response → ℝ) :=
    Set.univ.pi (fun _ : Response => Set.Icc (-bound) bound)
  have hcube_compact : IsCompact cube := by
    dsimp [cube]
    exact isCompact_univ_pi fun _ : Response => isCompact_Icc
  have hzero_cube : (0 : Response → ℝ) ∈ cube := by
    change ∀ response : Response, response ∈ Set.univ →
      -bound ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ bound
    intro response _
    constructor <;> linarith
  obtain ⟨maxReward, hmax_cube, hmax⟩ := hcube_compact.exists_isMaxOn ⟨0, hzero_cube⟩
    (continuous_bradleyTerryFitObjective preference sampling).continuousOn
  have hbarrier : ∀ reward : Response → ℝ,
      reward reference = 0 → reward ∉ cube →
      bradleyTerryFitObjective preference sampling reward < zeroObjective := by
    intro reward href houtside
    have houtside' : ∃ response : Response, reward response < -bound ∨ bound < reward response := by
      by_contra hnot
      push_neg at hnot
      apply houtside
      intro response _
      exact ⟨hnot response |>.1, hnot response |>.2⟩
    rcases houtside' with ⟨response, hlow | hhigh⟩
    · have hne : response ≠ reference := by
        intro heq
        subst response
        rw [href] at hlow
        linarith
      have hgap : reward response - reward reference < -bound := by
        rw [href]
        simpa using hlow
      have hlog_gap : Real.log (Real.sigmoid (reward response - reward reference)) <
          Real.log (Real.sigmoid (-bound)) :=
        Real.strictMonoOn_log (Real.sigmoid_pos _) (Real.sigmoid_pos _)
          (Real.sigmoid_strictMono hgap)
      have hterm_weight : minWeight ≤
          bradleyTerryFitTermWeight preference sampling response reference :=
        finiteMin_le weight (response, reference)
      have htail_nonpos : Real.log (Real.sigmoid (-bound)) ≤ 0 := by
        apply Real.log_nonpos
        · exact Real.sigmoid_nonneg _
        · exact Real.sigmoid_le_one _
      have hweight_pos' := bradleyTerryFitTermWeight_pos preference sampling
        hsampling hpreference response reference
      have hterm_lt : bradleyTerryFitTermWeight preference sampling response reference *
          Real.log (Real.sigmoid (reward response - reward reference)) < zeroObjective := by
        calc
          bradleyTerryFitTermWeight preference sampling response reference *
              Real.log (Real.sigmoid (reward response - reward reference)) <
            bradleyTerryFitTermWeight preference sampling response reference *
              Real.log (Real.sigmoid (-bound)) :=
            mul_lt_mul_of_pos_left hlog_gap hweight_pos'
          _ ≤ minWeight * Real.log (Real.sigmoid (-bound)) :=
            mul_le_mul_of_nonpos_right hterm_weight htail_nonpos
          _ < zeroObjective := by
            have h := (lt_div_iff₀ hminWeight_pos).mp htail
            nlinarith
      calc
        bradleyTerryFitObjective preference sampling reward ≤
            bradleyTerryFitTermWeight preference sampling response reference *
              Real.log (Real.sigmoid (reward response - reward reference)) := by
          simpa [bradleyTerryFitTermWeight, mul_assoc] using
            (bradleyTerryFitObjective_le_term preference sampling reward response reference)
        _ < zeroObjective := hterm_lt
    · have hne : reference ≠ response := by
        intro heq
        subst response
        rw [href] at hhigh
        linarith
      have hgap : reward reference - reward response < -bound := by
        rw [href]
        linarith
      have hlog_gap : Real.log (Real.sigmoid (reward reference - reward response)) <
          Real.log (Real.sigmoid (-bound)) :=
        Real.strictMonoOn_log (Real.sigmoid_pos _) (Real.sigmoid_pos _)
          (Real.sigmoid_strictMono hgap)
      have hterm_weight : minWeight ≤
          bradleyTerryFitTermWeight preference sampling reference response :=
        finiteMin_le weight (reference, response)
      have htail_nonpos : Real.log (Real.sigmoid (-bound)) ≤ 0 := by
        apply Real.log_nonpos
        · exact Real.sigmoid_nonneg _
        · exact Real.sigmoid_le_one _
      have hweight_pos' := bradleyTerryFitTermWeight_pos preference sampling
        hsampling hpreference reference response
      have hterm_lt : bradleyTerryFitTermWeight preference sampling reference response *
          Real.log (Real.sigmoid (reward reference - reward response)) < zeroObjective := by
        calc
          bradleyTerryFitTermWeight preference sampling reference response *
              Real.log (Real.sigmoid (reward reference - reward response)) <
            bradleyTerryFitTermWeight preference sampling reference response *
              Real.log (Real.sigmoid (-bound)) :=
            mul_lt_mul_of_pos_left hlog_gap hweight_pos'
          _ ≤ minWeight * Real.log (Real.sigmoid (-bound)) :=
            mul_le_mul_of_nonpos_right hterm_weight htail_nonpos
          _ < zeroObjective := by
            have h := (lt_div_iff₀ hminWeight_pos).mp htail
            nlinarith
      calc
        bradleyTerryFitObjective preference sampling reward ≤
            bradleyTerryFitTermWeight preference sampling reference response *
              Real.log (Real.sigmoid (reward reference - reward response)) := by
          simpa [bradleyTerryFitTermWeight, mul_assoc] using
            (bradleyTerryFitObjective_le_term preference sampling reward reference response)
        _ < zeroObjective := hterm_lt
  refine ⟨maxReward, ?_⟩
  intro candidate
  let normalized : Response → ℝ := referenceNormalizeReward reference candidate
  have hnormalized_ref : normalized reference = 0 := by
    exact referenceNormalizeReward_apply_reference reference candidate
  have hnormalized_objective :
      bradleyTerryFitObjective preference sampling normalized =
        bradleyTerryFitObjective preference sampling candidate := by
    exact bradleyTerryFitObjective_referenceNormalize preference sampling reference candidate
  by_cases hnormalized_cube : normalized ∈ cube
  · calc
      bradleyTerryFitObjective preference sampling candidate =
          bradleyTerryFitObjective preference sampling normalized := hnormalized_objective.symm
      _ ≤ bradleyTerryFitObjective preference sampling maxReward :=
        hmax hnormalized_cube
  · have hless := hbarrier normalized hnormalized_ref hnormalized_cube
    have hzero_max := hmax hzero_cube
    calc
      bradleyTerryFitObjective preference sampling candidate =
          bradleyTerryFitObjective preference sampling normalized := hnormalized_objective.symm
      _ ≤ zeroObjective := hless.le
      _ = bradleyTerryFitObjective preference sampling 0 := rfl
      _ ≤ bradleyTerryFitObjective preference sampling maxReward := hzero_max

end

end HumanFeedback
end Learning
end AppliedModelingLib
