import FalahatgarEtAl2017MaxingRanking.BordaCore
import FalahatgarEtAl2017MaxingRanking.SampleBudget
import FalahatgarEtAl2017MaxingRanking.FiniteBatchConcentration

/-!
# Borda-score sampling bounds

Theorem 9 samples a fresh uniformly selected opponent for each arm and ranks
the resulting empirical Borda scores.  This file supplies the iid
concentration and finite-union layers for that reduction; the connection from
the concrete pairwise sampler to the stated Borda expectation is kept visible
as the `hmean` hypothesis.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The empirical score from a positive finite batch of Borda observations. -/
noncomputable def bordaEmpiricalScore {Ω : Type*}
    (observation : ℕ → Ω → ℝ) (count : ℕ) (outcome : Ω) : ℝ :=
  (∑ index ∈ Finset.range count, observation index outcome) / (count : ℝ)

/--
The source's per-arm Borda sampling budget for accuracy `epsilon` and a union
over `armCount` arms.  It is the Compare ceiling budget with interval
`[0, epsilon]` and per-arm confidence `delta / armCount`.
-/
noncomputable def bordaSampleBudget (armCount : ℕ) (epsilon delta : ℝ) : ℕ :=
  fixedSampleBudget 0 epsilon (delta / (armCount : ℝ))

/--
A generic two-sided iid concentration bound for an empirical Borda score.
The conclusion is written as the source's sample average rather than a
centered sum.
-/
theorem bordaEmpiricalScore_nonconcentration_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : ℕ → Ω → ℝ) (count : ℕ) (mean error : ℝ)
    (hcount : 0 < count)
    (hindependent : iIndepFun (fun index : Fin count => observation index.val) law)
    (hmeasurable : ∀ index < count, Measurable (observation index))
    (hbounded : ∀ index < count, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ index < count, law[observation index] = mean)
    (herror : 0 ≤ error) :
    law.real {outcome | ¬
      |bordaEmpiricalScore observation count outcome - mean| < error} ≤
      2 * Real.exp (-((count : ℝ) * error) ^ 2 /
        (2 * (count : ℝ) * (1 / 4 : ℝ))) := by
  have htail := finiteIidBoundedObservation_centeredSum_abs_upperTail law count
    (fun index : Fin count => observation index.val) hindependent
    (fun index => hmeasurable index.val index.isLt)
    (fun index => hbounded index.val index.isLt) error herror
  have hsumFin : ∀ outcome,
      (∑ index : Fin count,
        (observation index.val outcome - law[observation index.val])) =
      ∑ index ∈ Finset.range count,
        (observation index outcome - law[observation index]) := by
    intro outcome
    exact Fin.sum_univ_eq_sum_range
      (fun index => observation index outcome - law[observation index]) count
  have hsum : ∀ outcome,
      (∑ index ∈ Finset.range count,
        (observation index outcome - law[observation index])) =
          (∑ index ∈ Finset.range count, observation index outcome) -
            (count : ℝ) * mean := by
    intro outcome
    rw [Finset.sum_sub_distrib]
    have hmeans :
        (∑ index ∈ Finset.range count, law[observation index]) =
          (count : ℝ) * mean := by
      rw [show (∑ index ∈ Finset.range count, law[observation index]) =
          ∑ index ∈ Finset.range count, mean by
        apply Finset.sum_congr rfl
        intro index hindex
        exact hmean index (Finset.mem_range.mp hindex)]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hmeans]
  have hevent :
      {outcome | ¬
        |bordaEmpiricalScore observation count outcome - mean| < error} =
        {outcome | (count : ℝ) * error ≤
          |∑ index : Fin count,
            (observation index.val outcome - law[observation index.val])|} := by
    ext outcome
    simp only [Set.mem_setOf_eq, not_lt, bordaEmpiricalScore]
    have hcountReal : 0 < (count : ℝ) := by exact_mod_cast hcount
    rw [hsumFin, hsum]
    have hrewrite :
        (∑ index ∈ Finset.range count, observation index outcome) / (count : ℝ) - mean =
          ((∑ index ∈ Finset.range count, observation index outcome) -
            (count : ℝ) * mean) / (count : ℝ) := by
      field_simp [ne_of_gt hcountReal]
    rw [hrewrite, abs_div, abs_of_pos hcountReal]
    constructor <;> intro h
    · have hmul := (le_div_iff₀ hcountReal).mp h
      nlinarith
    · apply (le_div_iff₀ hcountReal).mpr
      nlinarith
  rw [hevent]
  exact htail

/--
The ceiling Borda budget makes one arm's `epsilon / 2` score error have mass
at most `delta / armCount`.
-/
theorem bordaSampleBudget_tail_le_delta_div_card
    (armCount : ℕ) (epsilon delta : ℝ)
    (hcard : 0 < armCount) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    2 * Real.exp (-((bordaSampleBudget armCount epsilon delta : ℝ) *
      (epsilon / 2)) ^ 2 /
      (2 * (bordaSampleBudget armCount epsilon delta : ℝ) * (1 / 4 : ℝ))) ≤
        delta / (armCount : ℝ) := by
  have hcardReal : 0 < (armCount : ℝ) := by exact_mod_cast hcard
  have hcardGeOne : 1 ≤ (armCount : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hcard)
  have hdeltaDiv : 0 < delta / (armCount : ℝ) := div_pos hdelta hcardReal
  have hdeltaDivLeOne : delta / (armCount : ℝ) ≤ 1 := by
    have hdeltaLe : delta / (armCount : ℝ) ≤ delta := by
      apply (div_le_iff₀ hcardReal).mpr
      nlinarith
    exact hdeltaLe.trans hdeltaLeOne
  change
    2 * Real.exp (-((fixedSampleBudget 0 epsilon (delta / (armCount : ℝ)) : ℝ) *
      (epsilon / 2)) ^ 2 /
      (2 * (fixedSampleBudget 0 epsilon (delta / (armCount : ℝ)) : ℝ) *
        (1 / 4 : ℝ))) ≤ delta / (armCount : ℝ)
  simpa using (fixedSampleCompare_tail_le_delta_of_ceilingBudget 0 epsilon
    (delta / (armCount : ℝ)) hepsilon hdeltaDiv hdeltaDivLeOne)

/--
The union bound over the source's empirical Borda batches.  Every arm's score
is within `epsilon / 2` of its Borda expectation except with probability at
most `delta`.
-/
theorem bordaUniformEstimate_failure_probability_of_budget
    {Ω Arm : Type*} [MeasurableSpace Ω] [Fintype Arm] [DecidableEq Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (winProbability : Arm → Arm → ℝ) (observation : Arm → ℕ → Ω → ℝ)
    (epsilon delta : ℝ)
    (hindependent : ∀ arm,
      iIndepFun (fun index : Fin (bordaSampleBudget (Fintype.card Arm) epsilon delta) =>
        observation arm index.val) law)
    (hmeasurable : ∀ arm index,
      index < bordaSampleBudget (Fintype.card Arm) epsilon delta →
        Measurable (observation arm index))
    (hbounded : ∀ arm, ∀ index < bordaSampleBudget (Fintype.card Arm) epsilon delta,
      ∀ᵐ outcome ∂law, observation arm index outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ arm, ∀ index < bordaSampleBudget (Fintype.card Arm) epsilon delta,
      law[observation arm index] = bordaScore winProbability arm)
    (hcard : 0 < Fintype.card Arm)
    (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    law.real {outcome | ∃ arm, ¬
      |bordaEmpiricalScore (observation arm)
        (bordaSampleBudget (Fintype.card Arm) epsilon delta) outcome -
          bordaScore winProbability arm| < epsilon / 2} ≤ delta := by
  let budget := bordaSampleBudget (Fintype.card Arm) epsilon delta
  let bad : Arm → Set Ω := fun arm => {outcome | ¬
    |bordaEmpiricalScore (observation arm) budget outcome -
      bordaScore winProbability arm| < epsilon / 2}
  have hbudgetPos : 0 < budget := by
    unfold budget bordaSampleBudget
    have hbudgetReal := fixedSampleBudget_pos 0 epsilon (delta / (Fintype.card Arm : ℝ))
      hepsilon (div_pos hdelta (by exact_mod_cast hcard)) (by
        have hcardReal : 0 < (Fintype.card Arm : ℝ) := by exact_mod_cast hcard
        have hcardGeOne : 1 ≤ (Fintype.card Arm : ℝ) := by
          exact_mod_cast (Nat.succ_le_iff.mpr hcard)
        calc
          delta / (Fintype.card Arm : ℝ) ≤ delta := by
            apply (div_le_iff₀ hcardReal).mpr
            nlinarith
          _ ≤ 1 := hdeltaLeOne)
    exact_mod_cast hbudgetReal
  have hsingle : ∀ arm,
      law.real (bad arm) ≤ delta / (Fintype.card Arm : ℝ) := by
    intro arm
    calc
      law.real (bad arm) ≤
          2 * Real.exp (-((budget : ℝ) * (epsilon / 2)) ^ 2 /
            (2 * (budget : ℝ) * (1 / 4 : ℝ))) := by
        dsimp [bad]
        exact bordaEmpiricalScore_nonconcentration_probability law (observation arm) budget
          (bordaScore winProbability arm) (epsilon / 2) hbudgetPos
          (hindependent arm) (hmeasurable arm)
          (fun index hindex => hbounded arm index (by simpa [budget] using hindex))
          (fun index hindex => hmean arm index (by simpa [budget] using hindex))
          (by linarith)
      _ ≤ delta / (Fintype.card Arm : ℝ) := by
        dsimp [budget]
        exact bordaSampleBudget_tail_le_delta_div_card (Fintype.card Arm) epsilon delta
          hcard hepsilon hdelta hdeltaLeOne
  calc
    law.real {outcome | ∃ arm, ¬
        |bordaEmpiricalScore (observation arm)
          (bordaSampleBudget (Fintype.card Arm) epsilon delta) outcome -
            bordaScore winProbability arm| < epsilon / 2} =
        law.real (⋃ arm ∈ (Finset.univ : Finset Arm), bad arm) := by
          congr 1
          ext outcome
          simp [bad, budget]
    _ ≤ ∑ arm ∈ (Finset.univ : Finset Arm), law.real (bad arm) :=
      measureReal_biUnion_finset_le (Finset.univ : Finset Arm) bad
    _ ≤ ∑ _arm ∈ (Finset.univ : Finset Arm), delta / (Fintype.card Arm : ℝ) := by
      apply Finset.sum_le_sum
      intro arm _
      exact hsingle arm
    _ = delta := by
      have hcardReal : (Fintype.card Arm : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hcard)
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp [hcardReal]

/--
A direct empirical Borda-maxing algorithm: selecting an empirical-score
maximizer at the all-arms sampling budget is an `epsilon`-Borda maximum except
with probability at most `delta`.  Its extra `log |S|` factor is not the
optimal-bandit reduction used for Theorem 8.
-/
theorem directBordaMaxing_failure_probability_of_budget
    {Ω Arm : Type*} [MeasurableSpace Ω] [Fintype Arm] [DecidableEq Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (winProbability : Arm → Arm → ℝ) (observation : Arm → ℕ → Ω → ℝ)
    (epsilon delta : ℝ) (selected : Ω → Arm)
    (hindependent : ∀ arm,
      iIndepFun (fun index : Fin (bordaSampleBudget (Fintype.card Arm) epsilon delta) =>
        observation arm index.val) law)
    (hmeasurable : ∀ arm index,
      index < bordaSampleBudget (Fintype.card Arm) epsilon delta →
        Measurable (observation arm index))
    (hbounded : ∀ arm, ∀ index < bordaSampleBudget (Fintype.card Arm) epsilon delta,
      ∀ᵐ outcome ∂law, observation arm index outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ arm, ∀ index < bordaSampleBudget (Fintype.card Arm) epsilon delta,
      law[observation arm index] = bordaScore winProbability arm)
    (hcard : 0 < Fintype.card Arm)
    (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hmaximalEstimate : ∀ outcome competitor,
      bordaEmpiricalScore (observation competitor)
        (bordaSampleBudget (Fintype.card Arm) epsilon delta) outcome ≤
      bordaEmpiricalScore (observation (selected outcome))
        (bordaSampleBudget (Fintype.card Arm) epsilon delta) outcome) :
    law.real {outcome | ¬ EpsilonBordaMaximum winProbability epsilon (selected outcome)} ≤ delta := by
  calc
    law.real {outcome | ¬ EpsilonBordaMaximum winProbability epsilon (selected outcome)} ≤
        law.real {outcome | ∃ arm, ¬
          |bordaEmpiricalScore (observation arm)
            (bordaSampleBudget (Fintype.card Arm) epsilon delta) outcome -
              bordaScore winProbability arm| < epsilon / 2} := by
          refine measureReal_mono (μ := law) ?_ (measure_ne_top law _)
          intro outcome hfailure
          by_contra hbad
          have huniform : ∀ arm,
              |bordaEmpiricalScore (observation arm)
                (bordaSampleBudget (Fintype.card Arm) epsilon delta) outcome -
                  bordaScore winProbability arm| < epsilon / 2 := by
            intro arm
            by_contra hbadArm
            apply hbad
            exact ⟨arm, hbadArm⟩
          apply hfailure
          apply epsilonBordaMaximum_of_uniformEstimate winProbability
            (fun arm => bordaEmpiricalScore (observation arm)
              (bordaSampleBudget (Fintype.card Arm) epsilon delta) outcome)
            epsilon (selected outcome)
          · exact huniform
          · exact hmaximalEstimate outcome
    _ ≤ delta := bordaUniformEstimate_failure_probability_of_budget law winProbability observation
      epsilon delta hindependent hmeasurable hbounded hmean hcard hepsilon hdelta hdeltaLeOne

/--
Theorem 8's exact reduction: a PAC best-arm guarantee for the Bernoulli arm
whose mean is each Borda score is immediately a PAC Borda-maxing guarantee.
The optimal best-arm identification theorem itself is the external result
cited by the paper, rather than being conflated with the direct sampling
algorithm above.
-/
theorem bordaMaxing_failure_probability_of_banditGuarantee
    {Ω Arm : Type*} [MeasurableSpace Ω] [Fintype Arm]
    (law : Measure Ω) (banditMean : Arm → ℝ) (winProbability : Arm → Arm → ℝ)
    (epsilon delta : ℝ) (selected : Ω → Arm)
    (hmean : ∀ arm, banditMean arm = bordaScore winProbability arm)
    (hbandit : law.real {outcome | ¬ ∀ competitor,
      banditMean competitor - epsilon ≤ banditMean (selected outcome)} ≤ delta) :
    law.real {outcome | ¬ EpsilonBordaMaximum winProbability epsilon (selected outcome)} ≤ delta := by
  calc
    law.real {outcome | ¬ EpsilonBordaMaximum winProbability epsilon (selected outcome)} =
        law.real {outcome | ¬ ∀ competitor,
          banditMean competitor - epsilon ≤ banditMean (selected outcome)} := by
          congr 1
          ext outcome
          simp only [Set.mem_setOf_eq, EpsilonBordaMaximum]
          constructor <;> intro h
          · simpa only [hmean] using h
          · simpa only [hmean] using h
    _ ≤ delta := hbandit

/--
Theorem 9: any bijective order sorted by the empirical Borda estimates at the
source's budget is an `epsilon`-Borda ranking except with probability at most
`delta`.
-/
theorem bordaRanking_failure_probability_of_budget
    {Ω Arm : Type*} [MeasurableSpace Ω] [Fintype Arm] [DecidableEq Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (winProbability : Arm → Arm → ℝ) (observation : Arm → ℕ → Ω → ℝ)
    (epsilon delta : ℝ) (ranking : Ω → Fin (Fintype.card Arm) → Arm)
    (hindependent : ∀ arm,
      iIndepFun (fun index : Fin (bordaSampleBudget (Fintype.card Arm) epsilon delta) =>
        observation arm index.val) law)
    (hmeasurable : ∀ arm index,
      index < bordaSampleBudget (Fintype.card Arm) epsilon delta →
        Measurable (observation arm index))
    (hbounded : ∀ arm, ∀ index < bordaSampleBudget (Fintype.card Arm) epsilon delta,
      ∀ᵐ outcome ∂law, observation arm index outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ arm, ∀ index < bordaSampleBudget (Fintype.card Arm) epsilon delta,
      law[observation arm index] = bordaScore winProbability arm)
    (hcard : 0 < Fintype.card Arm)
    (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hbijective : ∀ outcome, Function.Bijective (ranking outcome))
    (hsorted : ∀ outcome,
      EstimatedScoresSorted
        (fun arm => bordaEmpiricalScore (observation arm)
          (bordaSampleBudget (Fintype.card Arm) epsilon delta) outcome)
        (ranking outcome)) :
    law.real {outcome | ¬ EpsilonBordaRanking winProbability epsilon (ranking outcome)} ≤ delta := by
  calc
    law.real {outcome | ¬ EpsilonBordaRanking winProbability epsilon (ranking outcome)} ≤
        law.real {outcome | ∃ arm, ¬
          |bordaEmpiricalScore (observation arm)
            (bordaSampleBudget (Fintype.card Arm) epsilon delta) outcome -
              bordaScore winProbability arm| < epsilon / 2} := by
          refine measureReal_mono (μ := law) ?_ (measure_ne_top law _)
          intro outcome hfailure
          by_contra hbad
          have huniform : ∀ arm,
              |bordaEmpiricalScore (observation arm)
                (bordaSampleBudget (Fintype.card Arm) epsilon delta) outcome -
                  bordaScore winProbability arm| < epsilon / 2 := by
            intro arm
            by_contra hbadArm
            apply hbad
            exact ⟨arm, hbadArm⟩
          apply hfailure
          apply epsilonBordaRanking_of_uniformEstimate winProbability
            (fun arm => bordaEmpiricalScore (observation arm)
              (bordaSampleBudget (Fintype.card Arm) epsilon delta) outcome)
            epsilon (ranking outcome) (hbijective outcome) (hsorted outcome)
          exact huniform
    _ ≤ delta := bordaUniformEstimate_failure_probability_of_budget law winProbability observation
      epsilon delta hindependent hmeasurable hbounded hmean hcard hepsilon hdelta hdeltaLeOne

end FalahatgarEtAl2017MaxingRanking
