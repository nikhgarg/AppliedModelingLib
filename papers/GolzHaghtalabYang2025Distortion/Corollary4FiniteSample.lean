import GolzHaghtalabYang2025Distortion.Theorem7FiniteSample

/-!
# Empirical maximal lotteries for source Corollary 4

The source's Maximal-Lotteries rule is the unregularized finite zero-sum
preference game. This module realizes that game as the full finite simplex:
the uniform reference and radius log |A| contain every policy. Its empirical
rate gives an unobserved off-diagonal pair the neutral margin zero. That
explicit totalization is the minimal way to define the source rule on every
finite random sample; it adds no model assumption, and the accompanying
source-rate bound controls the finite-sample route.
-/

namespace GolzHaghtalabYang2025Distortion

open AppliedModelingLib
open AppliedModelingLib.Alignment.Welfare
open AppliedModelingLib.GameTheory.PreferenceGame
open AppliedModelingLib.Learning.HumanFeedback

noncomputable section

/-- The direct equilibrium form of the totalized empirical Maximal-Lotteries
rule. Every lottery against it has nonpositive antisymmetric payoff. -/
def IsEmpiricalMaximalLottery
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (empiricalRate : Alternative → Alternative → ℝ) (lottery : PMF Alternative) : Prop :=
  ∀ opponent : PMF Alternative,
    0 ≤ pmfPairExp lottery opponent
      (fun first second => empiricalRate first second - empiricalRate second first)

/-- The full-simplex radius is a valid nonnegative finite KL budget. -/
theorem corollary4_uniformFullSimplexBudget_nonneg
    (Alternative : Type*) [Fintype Alternative] [Nonempty Alternative] :
    0 ≤ Real.log (Fintype.card Alternative : ℝ) := by
  apply Real.log_nonneg
  exact_mod_cast Fintype.card_pos

/-- A concrete totalized Maximal-Lotteries output for each literal iid user
sample. The uniform-reference KL presentation is extensionally the
unregularized finite simplex, by the accompanying full-simplex theorem. -/
noncomputable def corollary4IidUserEmpiricalMaximalLottery
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative] [Nonempty Alternative]
    {users comparisonsPerUser : ℕ}
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) : PMF Alternative :=
  theorem7IidUserEmpiricalPolicy (uniformPMF Alternative)
    (Real.log (Fintype.card Alternative : ℝ))
    (corollary4_uniformFullSimplexBudget_nonneg Alternative) sample

/-- The concrete output satisfies the source's unregularized empirical
zero-sum equilibrium condition against every alternative lottery. -/
theorem corollary4IidUserEmpiricalMaximalLottery_isEmpiricalMaximalLottery
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative] [Nonempty Alternative]
    {users comparisonsPerUser : ℕ}
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) :
    IsEmpiricalMaximalLottery
      (fun first second => theorem10IidUserPaperWinRate first second sample)
      (corollary4IidUserEmpiricalMaximalLottery sample) := by
  intro opponent
  exact theorem7_empiricalMaximin_margin_nonneg
    (fun first second => theorem10IidUserPaperWinRate first second sample)
    (fun first second => theorem10IidUserPaperWinRate_nonneg first second sample)
    (fun first second => theorem10IidUserPaperWinRate_le_one first second sample)
    (uniformPMF Alternative) (Real.log (Fintype.card Alternative : ℝ))
    (corollary4IidUserEmpiricalMaximalLottery sample) opponent
    (theorem7IidUserEmpiricalPolicy_isMaximin (uniformPMF Alternative)
      (Real.log (Fintype.card Alternative : ℝ))
      (corollary4_uniformFullSimplexBudget_nonneg Alternative) sample)
    (finiteKLDivergence_uniform_le_log_card opponent)

/--
The source-rate finite-sample route for Corollary 4. The selected empirical
policy is an exact equilibrium of the totalized Maximal-Lotteries game by the
preceding theorem, and its expected welfare obeys Theorem 7's
one-linearization bound on the whole simplex.
-/
theorem corollary4_iidUserExpectedWelfare_exists_optimalBenchmark_lower_of_sourceConfidence
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative] [Nonempty Alternative]
    {users comparisonsPerUser : ℕ}
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (hutility : UnitIntervalUtilityProfile utility)
    {btScale : ℝ} (hbtScale : 0 < btScale)
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (preference : PairwisePreference PUnit.{1} Alternative)
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative)
    (husers_pos : 0 < users) (hcomparisons_pos : 0 < comparisonsPerUser)
    (minimumMass : ℝ) (hminimumMass_pos : 0 < minimumMass)
    (hminimumMass : ∀ alternative, minimumMass ≤ (sampling alternative).toReal)
    (delta : ℝ) (hdelta_pos : 0 < delta) (hdelta_le_one : delta ≤ 1)
    (hsource_failure :
      (Fintype.card Alternative : ℝ) ^ 2 *
          Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * minimumMass ^ 2 / 8) ≤
        delta)
    (hpreference : preference = populationBradleyTerryPreference population utility btScale) :
    let failureBudget := delta / (Fintype.card Alternative : ℝ) ^ 2
    ∃ benchmark : PMF Alternative,
      (∀ other : PMF Alternative,
        policyAverageUtility population utility other ≤
          policyAverageUtility population utility benchmark) ∧
      (1 - delta) *
          ((sigmoidChordSlope btScale / ((1 : ℝ) / 4)) *
              policyAverageUtility population utility benchmark -
            theorem10SourceRate users comparisonsPerUser minimumMass failureBudget /
              (btScale * ((1 : ℝ) / 4))) ≤
        pmfExp (theorem7IidUserBatchLaw responseLaw sampling users comparisonsPerUser)
          (fun sample => policyAverageUtility population utility
            (corollary4IidUserEmpiricalMaximalLottery sample)) := by
  obtain ⟨benchmark, hbenchmark, hmax, hbound⟩ :=
    theorem7_iidUserExpectedWelfare_exists_optimalBenchmark_lower_of_sourceConfidence
      population utility hutility hbtScale responseLaw preference hcalibrated sampling
      husers_pos hcomparisons_pos minimumMass hminimumMass_pos hminimumMass
      (uniformPMF Alternative) (Real.log (Fintype.card Alternative : ℝ))
      (corollary4_uniformFullSimplexBudget_nonneg Alternative)
      delta hdelta_pos hdelta_le_one hsource_failure hpreference
  refine ⟨benchmark, ?_, ?_⟩
  · intro other
    exact hmax other (finiteKLDivergence_uniform_le_log_card other)
  · simpa [corollary4IidUserEmpiricalMaximalLottery] using hbound

end

end GolzHaghtalabYang2025Distortion
