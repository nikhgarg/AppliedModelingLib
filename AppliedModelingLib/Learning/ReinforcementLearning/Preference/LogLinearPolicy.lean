import AppliedModelingLib.Foundations.Optimization.EntropyRegularized
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.PolicyCovering
import AppliedModelingLib.Foundations.Math.QuadraticParameterCover
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Finite log-linear policies

Paper-neutral constructions and stability estimates for softmax policies with
finite action spaces.  The main estimate transports a uniform score error into
an explicit `L1` error between the corresponding action laws.
-/

namespace AppliedModelingLib
namespace PreferenceRL

open FiniteDimensionalNorms
open scoped BigOperators

noncomputable section

/-- The softmax law obtained by exponentially tilting the uniform action law. -/
noncomputable def softmaxPMF
    {Action : Type*} [Fintype Action] [Nonempty Action] [DecidableEq Action]
    (score : Action → ℝ) : PMF Action :=
  exponentialTilt (uniformPMF Action) score 1

/-- Softmax/Gibbs law written with a positive temperature multiplying the
entropy regularizer. -/
noncomputable def temperatureSoftmaxPMF
    {Action : Type*} [Fintype Action] [Nonempty Action] [DecidableEq Action]
    (utility : Action → ℝ) (temperature : ℝ) : PMF Action :=
  exponentialTilt (uniformPMF Action) utility temperature⁻¹

/-- Temperature notation agrees with the score-vector softmax after dividing
the utility by the temperature. -/
theorem temperatureSoftmaxPMF_eq_softmaxPMF_div
    {Action : Type*} [Fintype Action] [Nonempty Action] [DecidableEq Action]
    (utility : Action → ℝ) (temperature : ℝ) :
    temperatureSoftmaxPMF utility temperature =
      softmaxPMF (fun action ↦ utility action / temperature) := by
  apply PMF.ext
  intro action
  apply (ENNReal.toReal_eq_toReal_iff'
    ((temperatureSoftmaxPMF utility temperature).apply_ne_top action)
    ((softmaxPMF (fun action ↦ utility action / temperature)).apply_ne_top action)).mp
  rw [temperatureSoftmaxPMF, softmaxPMF,
    exponentialTilt_apply_toReal, exponentialTilt_apply_toReal]
  congr 1 <;> simp [Probability.finiteMGF, div_eq_mul_inv, mul_comm]

/-- A positive-temperature softmax loses at most
`temperature * log |Action|` in expected utility against any competing action
law.  This is the finite Gibbs variational bound used by entropy-regularized
dynamic programming. -/
theorem pmfExp_le_temperatureSoftmaxPMF_add_log_card
    {Action : Type*} [Fintype Action] [Nonempty Action] [DecidableEq Action]
    (target : PMF Action) (utility : Action → ℝ) (temperature : ℝ)
    (htemperature : 0 < temperature) :
    pmfExp target utility ≤
      pmfExp (temperatureSoftmaxPMF utility temperature) utility +
        temperature * Real.log (Fintype.card Action : ℝ) := by
  let reference : PMF Action := uniformPMF Action
  let selected := temperatureSoftmaxPMF utility temperature
  have hreference : PMFFullSupport reference := by
    intro action
    exact uniformPMF_apply_toReal_pos action
  have hoptimal := exponentialTiltObjective_le_at_exponentialTilt
    reference target utility temperature⁻¹ hreference
  have htargetKL : finiteKLDivergence target reference ≤
      Real.log (Fintype.card Action : ℝ) := by
    simpa [reference] using finiteKLDivergence_uniform_le_log_card target
  have hselectedKL : 0 ≤ finiteKLDivergence selected reference :=
    finiteKLDivergence_nonneg selected reference hreference
  dsimp [reference] at htargetKL
  dsimp [selected, temperatureSoftmaxPMF, reference] at hselectedKL
  dsimp [selected, temperatureSoftmaxPMF, exponentialTiltObjective, reference] at hoptimal
  have hmainRaw : temperature⁻¹ * pmfExp target utility ≤
      temperature⁻¹ *
          pmfExp
            (exponentialTilt (uniformPMF Action) utility temperature⁻¹) utility +
        Real.log (Fintype.card Action : ℝ) := by
    linarith
  have hmain : temperature⁻¹ * pmfExp target utility ≤
      temperature⁻¹ *
          pmfExp (temperatureSoftmaxPMF utility temperature) utility +
        Real.log (Fintype.card Action : ℝ) := by
    simpa [temperatureSoftmaxPMF] using hmainRaw
  have hscaled := mul_le_mul_of_nonneg_left hmain htemperature.le
  calc
    pmfExp target utility =
        temperature * (temperature⁻¹ * pmfExp target utility) := by
          field_simp [htemperature.ne']
    _ ≤ temperature *
        (temperature⁻¹ *
            pmfExp (temperatureSoftmaxPMF utility temperature) utility +
          Real.log (Fintype.card Action : ℝ)) := hscaled
    _ = pmfExp (temperatureSoftmaxPMF utility temperature) utility +
        temperature * Real.log (Fintype.card Action : ℝ) := by
          field_simp [htemperature.ne']

/-- A nonempty policy class with an attained finite cover has a strictly
positive minimum covering number. -/
theorem stageIndexedPolicyCoveringNumber_pos_of_nonempty
    {Policy State Action : Type*}
    [Fintype Action] [DecidableEq Action]
    (interpret : Policy → StageIndexedPolicy State Action)
    (policyClass : Set Policy) (horizon : ℕ) (epsilon : ℝ)
    (hpolicyClass : policyClass.Nonempty)
    (hexists : ∃ number,
      StageIndexedPolicyCoveringNumberAtMost
        interpret policyClass horizon epsilon number) :
    0 < stageIndexedPolicyCoveringNumber
      interpret policyClass horizon epsilon := by
  obtain ⟨center, hcenter⟩ := stageIndexedPolicyCoveringNumber_spec
    interpret policyClass horizon epsilon hexists
  obtain ⟨policy, hpolicy⟩ := hpolicyClass
  obtain ⟨index, _hindex⟩ := hcenter.2 policy hpolicy
  exact (Nat.zero_le index.1).trans_lt index.isLt

/-- If two finite score vectors are uniformly within `eta`, their softmax laws
are within `exp (2 * eta) - 1` in `L1`.  This is the normalization-sensitive
estimate used in volumetric covers of log-linear policies. -/
theorem pmfL1Error_softmaxPMF_le_exp_two_mul_sub_one
    {Action : Type*} [Fintype Action] [Nonempty Action] [DecidableEq Action]
    (first second : Action → ℝ) (eta : ℝ)
    (heta : 0 ≤ eta) (hclose : ∀ action, |first action - second action| ≤ eta) :
    pmfL1Error (softmaxPMF first) (softmaxPMF second) ≤
      Real.exp (2 * eta) - 1 := by
  classical
  let reference : PMF Action := uniformPMF Action
  let firstPartition := Probability.finiteMGF reference first 1
  let secondPartition := Probability.finiteMGF reference second 1
  have hfirstPartition : 0 < firstPartition :=
    Probability.finiteMGF_pos reference first 1
  have hsecondPartition : 0 < secondPartition :=
    Probability.finiteMGF_pos reference second 1
  have hsecondLe : secondPartition ≤ Real.exp eta * firstPartition := by
    dsimp [secondPartition, firstPartition, Probability.finiteMGF]
    calc
      (∑ action : Action,
          (reference action).toReal * Real.exp (1 * second action)) ≤
          ∑ action : Action,
            Real.exp eta *
              ((reference action).toReal * Real.exp (1 * first action)) := by
        apply Finset.sum_le_sum
        intro action _
        have hscore : second action ≤ first action + eta := by
          linarith [(abs_le.mp (hclose action)).1]
        have hexp := Real.exp_le_exp.mpr hscore
        rw [Real.exp_add] at hexp
        have hmass : 0 ≤ (reference action).toReal := ENNReal.toReal_nonneg
        calc
          (reference action).toReal * Real.exp (1 * second action) ≤
              (reference action).toReal *
                (Real.exp (first action) * Real.exp eta) := by
            simpa using mul_le_mul_of_nonneg_left hexp hmass
          _ = Real.exp eta *
              ((reference action).toReal * Real.exp (1 * first action)) := by ring
      _ = Real.exp eta *
          (∑ action : Action,
            (reference action).toReal * Real.exp (1 * first action)) := by
        rw [Finset.mul_sum]
  have hfirstLe : firstPartition ≤ Real.exp eta * secondPartition := by
    dsimp [firstPartition, secondPartition, Probability.finiteMGF]
    calc
      (∑ action : Action,
          (reference action).toReal * Real.exp (1 * first action)) ≤
          ∑ action : Action,
            Real.exp eta *
              ((reference action).toReal * Real.exp (1 * second action)) := by
        apply Finset.sum_le_sum
        intro action _
        have hscore : first action ≤ second action + eta := by
          linarith [(abs_le.mp (hclose action)).2]
        have hexp := Real.exp_le_exp.mpr hscore
        rw [Real.exp_add] at hexp
        have hmass : 0 ≤ (reference action).toReal := ENNReal.toReal_nonneg
        calc
          (reference action).toReal * Real.exp (1 * first action) ≤
              (reference action).toReal *
                (Real.exp (second action) * Real.exp eta) := by
            simpa using mul_le_mul_of_nonneg_left hexp hmass
          _ = Real.exp eta *
              ((reference action).toReal * Real.exp (1 * second action)) := by ring
      _ = Real.exp eta *
          (∑ action : Action,
            (reference action).toReal * Real.exp (1 * second action)) := by
        rw [Finset.mul_sum]
  have hmassBounds : ∀ action,
      ((softmaxPMF second action).toReal ≤
          Real.exp (2 * eta) * (softmaxPMF first action).toReal) ∧
        ((softmaxPMF first action).toReal ≤
          Real.exp (2 * eta) * (softmaxPMF second action).toReal) := by
    intro action
    have hreference : 0 ≤ (reference action).toReal := ENNReal.toReal_nonneg
    have hfirstNumerator : 0 ≤
        (reference action).toReal * Real.exp (first action) :=
      mul_nonneg hreference (Real.exp_pos _).le
    have hsecondNumerator : 0 ≤
        (reference action).toReal * Real.exp (second action) :=
      mul_nonneg hreference (Real.exp_pos _).le
    have hsecondNumeratorLe :
        (reference action).toReal * Real.exp (second action) ≤
          Real.exp eta *
            ((reference action).toReal * Real.exp (first action)) := by
      have hscore : second action ≤ first action + eta := by
        linarith [(abs_le.mp (hclose action)).1]
      have hexp := Real.exp_le_exp.mpr hscore
      rw [Real.exp_add] at hexp
      calc
        (reference action).toReal * Real.exp (second action) ≤
            (reference action).toReal *
              (Real.exp (first action) * Real.exp eta) :=
          mul_le_mul_of_nonneg_left hexp hreference
        _ = Real.exp eta *
            ((reference action).toReal * Real.exp (first action)) := by ring
    have hfirstNumeratorLe :
        (reference action).toReal * Real.exp (first action) ≤
          Real.exp eta *
            ((reference action).toReal * Real.exp (second action)) := by
      have hscore : first action ≤ second action + eta := by
        linarith [(abs_le.mp (hclose action)).2]
      have hexp := Real.exp_le_exp.mpr hscore
      rw [Real.exp_add] at hexp
      calc
        (reference action).toReal * Real.exp (first action) ≤
            (reference action).toReal *
              (Real.exp (second action) * Real.exp eta) :=
          mul_le_mul_of_nonneg_left hexp hreference
        _ = Real.exp eta *
            ((reference action).toReal * Real.exp (second action)) := by ring
    have hcrossSecond :
        ((reference action).toReal * Real.exp (second action)) * firstPartition ≤
          (Real.exp (2 * eta) *
              ((reference action).toReal * Real.exp (first action))) *
            secondPartition := by
      calc
        ((reference action).toReal * Real.exp (second action)) * firstPartition ≤
            (Real.exp eta *
                ((reference action).toReal * Real.exp (first action))) *
              (Real.exp eta * secondPartition) :=
          mul_le_mul hsecondNumeratorLe hfirstLe
            hfirstPartition.le
            (mul_nonneg (Real.exp_pos _).le hfirstNumerator)
        _ = (Real.exp (2 * eta) *
              ((reference action).toReal * Real.exp (first action))) *
            secondPartition := by
          rw [show 2 * eta = eta + eta by ring, Real.exp_add]
          ring
    have hcrossFirst :
        ((reference action).toReal * Real.exp (first action)) * secondPartition ≤
          (Real.exp (2 * eta) *
              ((reference action).toReal * Real.exp (second action))) *
            firstPartition := by
      calc
        ((reference action).toReal * Real.exp (first action)) * secondPartition ≤
            (Real.exp eta *
                ((reference action).toReal * Real.exp (second action))) *
              (Real.exp eta * firstPartition) :=
          mul_le_mul hfirstNumeratorLe hsecondLe
            hsecondPartition.le
            (mul_nonneg (Real.exp_pos _).le hsecondNumerator)
        _ = (Real.exp (2 * eta) *
              ((reference action).toReal * Real.exp (second action))) *
            firstPartition := by
          rw [show 2 * eta = eta + eta by ring, Real.exp_add]
          ring
    constructor
    · simp only [softmaxPMF, exponentialTilt_apply_toReal]
      change
        ((reference action).toReal * Real.exp (1 * second action)) /
            secondPartition ≤
          Real.exp (2 * eta) *
            (((reference action).toReal * Real.exp (1 * first action)) /
              firstPartition)
      rw [show Real.exp (2 * eta) *
          (((reference action).toReal * Real.exp (1 * first action)) /
            firstPartition) =
          (Real.exp (2 * eta) *
            ((reference action).toReal * Real.exp (first action))) /
              firstPartition by ring]
      exact (div_le_div_iff₀ hsecondPartition hfirstPartition).2
        (by simpa using hcrossSecond)
    · simp only [softmaxPMF, exponentialTilt_apply_toReal]
      change
        ((reference action).toReal * Real.exp (1 * first action)) /
            firstPartition ≤
          Real.exp (2 * eta) *
            (((reference action).toReal * Real.exp (1 * second action)) /
              secondPartition)
      rw [show Real.exp (2 * eta) *
          (((reference action).toReal * Real.exp (1 * second action)) /
            secondPartition) =
          (Real.exp (2 * eta) *
            ((reference action).toReal * Real.exp (second action))) /
              secondPartition by ring]
      exact (div_le_div_iff₀ hfirstPartition hsecondPartition).2
        (by simpa using hcrossFirst)
  have hfactor : 0 ≤ Real.exp (2 * eta) - 1 := by
    exact sub_nonneg.mpr (Real.one_le_exp (by positivity))
  unfold pmfL1Error
  calc
    (∑ action : Action,
        |(softmaxPMF first action).toReal -
          (softmaxPMF second action).toReal|) ≤
        ∑ action : Action,
          (Real.exp (2 * eta) - 1) * (softmaxPMF first action).toReal := by
      apply Finset.sum_le_sum
      intro action _
      obtain ⟨hsecondMass, hfirstMass⟩ := hmassBounds action
      by_cases horder : (softmaxPMF first action).toReal ≤
          (softmaxPMF second action).toReal
      · rw [abs_of_nonpos (sub_nonpos.mpr horder)]
        linarith
      · have hreverse : (softmaxPMF second action).toReal ≤
            (softmaxPMF first action).toReal := le_of_not_ge horder
        rw [abs_of_nonneg (sub_nonneg.mpr hreverse)]
        calc
          (softmaxPMF first action).toReal -
              (softmaxPMF second action).toReal ≤
              (Real.exp (2 * eta) - 1) *
                (softmaxPMF second action).toReal := by linarith
          _ ≤ (Real.exp (2 * eta) - 1) *
                (softmaxPMF first action).toReal :=
            mul_le_mul_of_nonneg_left hreverse hfactor
    _ = (Real.exp (2 * eta) - 1) *
        (∑ action : Action, (softmaxPMF first action).toReal) := by
      rw [Finset.mul_sum]
    _ = Real.exp (2 * eta) - 1 := by
      rw [pmfToRealSum, mul_one]

/-- The chord of the exponential between `0` and `log 2`: for a unit-scale
error, `exp ((log 2) * epsilon) - 1` is at most `epsilon`. -/
theorem exp_log_two_mul_sub_one_le
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1) :
    Real.exp (Real.log 2 * epsilon) - 1 ≤ epsilon := by
  have hconvex := convexOn_exp.2 (Set.mem_univ (Real.log 2))
    (Set.mem_univ 0) hepsilon (sub_nonneg.mpr hepsilonOne)
    (by ring : epsilon + (1 - epsilon) = 1)
  have htwo : Real.exp (Real.log 2) = 2 := by
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hzero : Real.exp 0 = 1 := Real.exp_zero
  have hrewrite :
      epsilon • Real.log 2 + (1 - epsilon) • (0 : ℝ) =
        Real.log 2 * epsilon := by simp [smul_eq_mul, mul_comm]
  rw [hrewrite, smul_eq_mul, smul_eq_mul, htwo, hzero] at hconvex
  linarith

/-- A finite-stage log-linear policy with stagewise Euclidean parameters. -/
noncomputable def logLinearStageIndexedPolicy
    {State Action Coordinate : Type*}
    [Fintype Action] [Nonempty Action] [DecidableEq Action] [Fintype Coordinate]
    (feature : ℕ → State → Action → Coordinate → ℝ)
    (parameter : ℕ → Coordinate → ℝ) :
    StageIndexedPolicy State Action :=
  fun time state ↦ softmaxPMF fun action ↦
    dot (parameter time) (feature time state action)

/-- Euclidean parameter proximity and a uniform feature-radius bound imply
the exact exponential `L1` stability envelope for log-linear policies. -/
theorem pmfL1Error_logLinearStageIndexedPolicy_le
    {State Action Coordinate : Type*}
    [Fintype Action] [Nonempty Action] [DecidableEq Action] [Fintype Coordinate]
    (feature : ℕ → State → Action → Coordinate → ℝ)
    (first second : ℕ → Coordinate → ℝ)
    (time : ℕ) (state : State) (featureRadius parameterError : ℝ)
    (hfeatureRadius : 0 ≤ featureRadius)
    (hparameterError : 0 ≤ parameterError)
    (hfeature : ∀ action, l2 (feature time state action) ≤ featureRadius)
    (hparameter : l2 (fun coordinate ↦ first time coordinate -
      second time coordinate) ≤ parameterError) :
    pmfL1Error (logLinearStageIndexedPolicy feature first time state)
        (logLinearStageIndexedPolicy feature second time state) ≤
      Real.exp (2 * (parameterError * featureRadius)) - 1 := by
  apply pmfL1Error_softmaxPMF_le_exp_two_mul_sub_one
  · positivity
  · intro action
    calc
      |dot (first time) (feature time state action) -
          dot (second time) (feature time state action)| =
          |dot (fun coordinate ↦ first time coordinate - second time coordinate)
            (feature time state action)| := by
        rw [dot_sub_left]
      _ ≤ l2 (fun coordinate ↦ first time coordinate - second time coordinate) *
          l2 (feature time state action) := abs_dot_le_l2_mul_l2 _ _
      _ ≤ parameterError * featureRadius :=
        mul_le_mul hparameter (hfeature action) (normL2_nonneg _)
          hparameterError

/-- The paper's `log 2` parameter radius is sufficient for an `epsilon`
uniform action-law approximation. -/
theorem pmfL1Error_logLinearStageIndexedPolicy_le_epsilon
    {State Action Coordinate : Type*}
    [Fintype Action] [Nonempty Action] [DecidableEq Action] [Fintype Coordinate]
    (feature : ℕ → State → Action → Coordinate → ℝ)
    (first second : ℕ → Coordinate → ℝ)
    (time : ℕ) (state : State) (featureRadius parameterError epsilon : ℝ)
    (hfeatureRadius : 0 ≤ featureRadius)
    (hparameterError : 0 ≤ parameterError)
    (hepsilon : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1)
    (hfeature : ∀ action, l2 (feature time state action) ≤ featureRadius)
    (hparameter : l2 (fun coordinate ↦ first time coordinate -
      second time coordinate) ≤ parameterError)
    (hscale : 2 * (parameterError * featureRadius) ≤ Real.log 2 * epsilon) :
    pmfL1Error (logLinearStageIndexedPolicy feature first time state)
        (logLinearStageIndexedPolicy feature second time state) ≤ epsilon := by
  calc
    pmfL1Error (logLinearStageIndexedPolicy feature first time state)
        (logLinearStageIndexedPolicy feature second time state) ≤
        Real.exp (2 * (parameterError * featureRadius)) - 1 :=
      pmfL1Error_logLinearStageIndexedPolicy_le feature first second time state
        featureRadius parameterError hfeatureRadius hparameterError hfeature hparameter
    _ ≤ Real.exp (Real.log 2 * epsilon) - 1 := by
      linarith [Real.exp_le_exp.mpr hscale]
    _ ≤ epsilon := exp_log_two_mul_sub_one_le hepsilon hepsilonOne

end

end PreferenceRL
end AppliedModelingLib
