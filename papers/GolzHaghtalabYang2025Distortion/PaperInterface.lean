import GolzHaghtalabYang2025Distortion.AuditInterface
import GolzHaghtalabYang2025Distortion.Theorem3D2Source
import GolzHaghtalabYang2025Distortion.Theorem9
import GolzHaghtalabYang2025Distortion.Lemma15
import GolzHaghtalabYang2025Distortion.Corollary4FiniteSample
import AppliedModelingLib.Learning.HumanFeedback.DPO

/-!
# Source-facing interface: Distortion of AI Alignment

Each declaration below is one complete transparent semantic target for one
source claim. Proof decomposition and finite-support components remain in
AuditInterface; they are not additional paper claims.
-/

namespace GolzHaghtalabYang2025Distortion

open AppliedModelingLib
open AppliedModelingLib.Alignment.Welfare
open AppliedModelingLib.Learning.HumanFeedback
open AppliedModelingLib.Learning.HumanFeedback.PairwiseCountDataset
open AppliedModelingLib.Probability
open scoped Topology

/-! ## Source model definitions -/

/--
The source's empirical Borda rule: positive probability is assigned exactly
to normalized-score maximizers, with equal probability for every maximizer.
-/
def IsEmpiricalBordaRule
    {Report Alternative : Type*} [Fintype Alternative]
    (wins incidences : Alternative → Report → ℝ)
    (rule : ∀ horizon : ℕ, (Fin horizon → Report) → PMF Alternative) : Prop :=
  ∀ (horizon : ℕ) (sample : Fin horizon → Report),
    (∀ alternative,
      0 < (rule horizon sample alternative).toReal ↔
        ∀ other,
          theorem12EmpiricalBordaScore wins incidences other sample ≤
            theorem12EmpiricalBordaScore wins incidences alternative sample) ∧
    ∀ first second,
      (∀ other,
        theorem12EmpiricalBordaScore wins incidences other sample ≤
          theorem12EmpiricalBordaScore wins incidences first sample) →
      (∀ other,
        theorem12EmpiricalBordaScore wins incidences other sample ≤
          theorem12EmpiricalBordaScore wins incidences second sample) →
      (rule horizon sample first).toReal = (rule horizon sample second).toReal

/--
Source empirical Borda definition: normalized wins over positive incidences and
uniform selection from the score maximizers. The displayed source quotient has
no value when an alternative has no sampled incidence; for the literal finite
report-law evaluator below, that branch is explicitly assigned the neutral
score zero. This finite-rule convention is recorded in the source-correction
ledger rather than treated as an unstated source identity.
-/
def empiricalBordaDefinitionSpec
    {Report Alternative : Type*} [Fintype Alternative]
    (wins incidences : Alternative → Report → ℝ)
    (rule : ∀ horizon : ℕ, (Fin horizon → Report) → PMF Alternative) : Prop :=
  ∀ (horizon : ℕ) (sample : Fin horizon → Report),
      let score := fun alternative =>
        if finiteIidScoreSum (incidences alternative) sample = 0 then 0
        else finiteIidScoreSum (wins alternative) sample /
          finiteIidScoreSum (incidences alternative) sample
      (∀ alternative,
        0 < (rule horizon sample alternative).toReal ↔
          ∀ other, score other ≤ score alternative) ∧
      ∀ first second,
        (∀ other, score other ≤ score first) →
        (∀ other, score other ≤ score second) →
        (rule horizon sample first).toReal = (rule horizon sample second).toReal

/-- A source population-Borda winner maximizes the limiting expected score. -/
def IsPopulationBordaWinner
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit.{1} Alternative)
    (winner : Alternative) : Prop :=
  ∀ alternative,
    pairwiseBordaScore sampling preference alternative ≤
      pairwiseBordaScore sampling preference winner

/--
Source population Borda definition from the Theorem 2 proof sketch: the
sampling-weighted expected win probability and its maximizing alternative.
-/
def populationBordaDefinitionSpec
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit.{1} Alternative)
    (winner : Alternative) : Prop :=
  ∀ alternative,
    pmfExp sampling (fun opponent => preference.prob PUnit.unit alternative opponent) ≤
      pmfExp sampling (fun opponent => preference.prob PUnit.unit winner opponent)

/--
Source constrained-RLHF definition, expanded as the finite logistic MLE and
the subsequent expected-score maximization in the same finite KL ball.
-/
def rlhfDefinitionSpec
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {horizon : ℕ} (sample : Fin horizon → BinaryPairwiseReport Alternative)
    (scoreReference : Alternative) (reference policy : PMF Alternative)
    (klBudget : ℝ) (score : ScoreVector Alternative) : Prop :=
  PMFFullSupport reference ∧
  (
    score scoreReference = 0 ∧
      IsMaxOn
        (pairwiseLogLikelihood (ofBinaryReports sample) Real.sigmoid)
        {candidate : ScoreVector Alternative | candidate scoreReference = 0} score
  ) ∧
  (
    contextAveragedPolicyKLDivergence (PMF.pure PUnit.unit.{1})
        (contextFreeAlternativePolicy policy) (contextFreeAlternativePolicy reference) ≤
      klBudget ∧
      ∀ other : FinitePolicy PUnit.{1} Alternative,
        contextAveragedPolicyKLDivergence (PMF.pure PUnit.unit.{1}) other
            (contextFreeAlternativePolicy reference) ≤ klBudget →
          policyExpectedScore (PMF.pure PUnit.unit.{1}) other (fun _ => score) ≤
            policyExpectedScore (PMF.pure PUnit.unit.{1})
              (contextFreeAlternativePolicy policy) (fun _ => score)
  )

/--
Source constrained-NLHF definition, expanded as an attained maximum of the
worst centered comparison payoff over the finite KL ball.
-/
def nlhfDefinitionSpec
    {User Alternative : Type} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (btScale : ℝ) (reference : PMF Alternative) (klBudget : ℝ)
    (policy : PMF Alternative) : Prop :=
  PMFFullSupport reference ∧
    finiteKLDivergence policy reference ≤ klBudget ∧
    ∃ worst : PMF Alternative,
      finiteKLDivergence worst reference ≤ klBudget ∧
      (∀ opponent : PMF Alternative,
        finiteKLDivergence opponent reference ≤ klBudget →
          AppliedModelingLib.GameTheory.PreferenceGame.contextFreeCenteredPreferencePayoff
              (populationBradleyTerryPreference.{0, 0, 0} population utility btScale)
              policy worst ≤
            AppliedModelingLib.GameTheory.PreferenceGame.contextFreeCenteredPreferencePayoff
              (populationBradleyTerryPreference.{0, 0, 0} population utility btScale)
            policy opponent) ∧
      ∀ candidate : PMF Alternative,
        finiteKLDivergence candidate reference ≤ klBudget →
          AppliedModelingLib.GameTheory.PreferenceGame.contextFreeCenteredPreferencePayoff
              (populationBradleyTerryPreference.{0, 0, 0} population utility btScale)
              candidate worst ≤
            AppliedModelingLib.GameTheory.PreferenceGame.contextFreeCenteredPreferencePayoff
              (populationBradleyTerryPreference.{0, 0, 0} population utility btScale)
              policy worst

/-! ## Source distortion and maximal-lottery definitions -/

/-- The source's expected average utility of a voting rule after `horizon`
independent-sample slots.  The law may retain the source model's within-user
correlation; no independence across comparison coordinates is built into this
definition. -/
noncomputable def sourceSocialChoiceAverageUtility
    {Alternative Observation : Type*} [Fintype Alternative] [Fintype Observation]
    (averageUtility : Alternative → ℝ)
    (observationLaw : ∀ horizon : ℕ, PMF (Fin horizon → Observation))
    (rule : ∀ horizon : ℕ, (Fin horizon → Observation) → PMF Alternative)
    (horizon : ℕ) : ℝ :=
  pmfExp (observationLaw horizon) (fun observations =>
    pmfExp (rule horizon observations) averageUtility)

/-- The source's ``max_x AvgUtil(x)`` benchmark is an attained maximum. -/
def IsSourceSocialChoiceOptimalAverageUtility
    {Alternative : Type*} [Fintype Alternative]
    (averageUtility : Alternative → ℝ) (optimalAverageUtility : ℝ) : Prop :=
  (∃ alternative, averageUtility alternative = optimalAverageUtility) ∧
    ∀ alternative, averageUtility alternative ≤ optimalAverageUtility

/-- The fixed-instance social-choice distortion displayed in Section 2. -/
noncomputable def sourceSocialChoiceDistortion
    {Alternative Observation : Type*} [Fintype Alternative] [Fintype Observation]
    (averageUtility : Alternative → ℝ)
    (optimalAverageUtility : ℝ)
    (observationLaw : ∀ horizon : ℕ, PMF (Fin horizon → Observation))
    (rule : ∀ horizon : ℕ, (Fin horizon → Observation) → PMF Alternative) : ℝ :=
  Filter.limsup
    (fun horizon => optimalAverageUtility /
      sourceSocialChoiceAverageUtility averageUtility observationLaw rule horizon)
    Filter.atTop

/-- The source's worst-case social-choice distortion, with the instance type
holding the fixed model parameters other than the utility distribution. -/
noncomputable def sourceWorstCaseSocialChoiceDistortion
    {Instance : Type*} (distortion : Instance → ℝ) : ℝ :=
  sSup (Set.range distortion)

/-- The source's normalized empirical pairwise margin.  The explicit
nonzero-denominator premise is the domain on which the printed fraction is
defined; an unobserved unordered pair is not assigned an unstated value. -/
noncomputable def sourceMaximalLotteryMargin
    {Alternative : Type*}
    (wins : Alternative → Alternative → ℕ)
    (first second : Alternative)
    (_hdenominator : wins first second + wins second first ≠ 0) : ℝ :=
  ((wins first second : ℝ) - (wins second first : ℝ)) /
    ((wins first second : ℝ) + (wins second first : ℝ))

/-- The lower value of a candidate lottery in the source's antisymmetric
zero-sum margin game. -/
noncomputable def sourceMaximalLotteryValue
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (wins : Alternative → Alternative → ℕ)
    (hdenominator : ∀ first second, first ≠ second →
      wins first second + wins second first ≠ 0)
    (candidate : PMF Alternative) : ℝ :=
  sInf (Set.range fun opponent : PMF Alternative =>
    pmfExp candidate (fun first =>
      pmfExp opponent (fun second =>
        if h : first = second then 0 else
          sourceMaximalLotteryMargin wins first second
            (hdenominator first second h))))

/-- A source maximal lottery maximizes the minimum expected margin against a
second lottery. -/
def IsSourceMaximalLottery
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (wins : Alternative → Alternative → ℕ)
    (hdenominator : ∀ first second, first ≠ second →
      wins first second + wins second first ≠ 0)
    (lottery : PMF Alternative) : Prop :=
  ∀ candidate : PMF Alternative,
    sourceMaximalLotteryValue wins hdenominator candidate ≤
      sourceMaximalLotteryValue wins hdenominator lottery

/-- The source's expected average utility for a fixed alignment method. -/
noncomputable def sourceAlignmentAverageUtility
    {Alternative Observation : Type*} [Fintype Alternative] [Fintype Observation]
    (averageUtility : Alternative → ℝ)
    (observationLaw : ∀ horizon : ℕ, PMF (Fin horizon → Observation))
    (method : ∀ horizon : ℕ, (Fin horizon → Observation) → PMF Alternative → ℝ →
      PMF Alternative)
    (reference : PMF Alternative) (klBudget : ℝ) (horizon : ℕ) : ℝ :=
  pmfExp (observationLaw horizon) (fun observations =>
    pmfExp (method horizon observations reference klBudget) averageUtility)

/-- The source alignment benchmark is the highest average-utility policy in
the specified KL ball. -/
def IsSourceAlignmentBenchmark
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (averageUtility : Alternative → ℝ)
    (reference benchmark : PMF Alternative) (klBudget : ℝ) : Prop :=
  InFiniteKLBall reference klBudget benchmark ∧
    ∀ policy : PMF Alternative,
      InFiniteKLBall reference klBudget policy →
        pmfExp policy averageUtility ≤ pmfExp benchmark averageUtility

/-- The fixed-instance alignment distortion displayed in Section 2. -/
noncomputable def sourceAlignmentDistortion
    {Alternative Observation : Type*} [Fintype Alternative] [DecidableEq Alternative]
    [Fintype Observation]
    (averageUtility : Alternative → ℝ)
    (benchmarkUtility : ℝ)
    (observationLaw : ∀ horizon : ℕ, PMF (Fin horizon → Observation))
    (method : ∀ horizon : ℕ, (Fin horizon → Observation) → PMF Alternative → ℝ →
      PMF Alternative)
    (reference : PMF Alternative) (klBudget : ℝ) : ℝ :=
  Filter.limsup
    (fun horizon => benchmarkUtility /
      sourceAlignmentAverageUtility averageUtility observationLaw method reference klBudget horizon)
    Filter.atTop

/-- The source's worst-case alignment distortion over admissible utility
distributions, reference policies, and KL budgets. -/
noncomputable def sourceWorstCaseAlignmentDistortion
    {Instance : Type*} (distortion : Instance → ℝ) : ℝ :=
  sSup (Set.range distortion)

/-! ## Appendix F.3: normalized DPO/RLHF equivalence -/

/-- The finite literal-report DPO loss after the source change of variables.
It uses the policy/reference log-ratio reward, so the candidate remains a
normalized policy rather than the unnormalized expression printed in F.3. -/
noncomputable def sourceDpoBinaryReportLoss
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {horizon : ℕ} (sample : Fin horizon → BinaryPairwiseReport Alternative)
    (reference policy : PMF Alternative) (klWeight : ℝ) : ℝ :=
  -pairwiseLogLikelihood (ofBinaryReports sample) Real.sigmoid
    (fun alternative =>
      dpoImplicitReward (contextFreeAlternativePolicy policy)
        (contextFreeAlternativePolicy reference) klWeight PUnit.unit.{1} alternative)

/-- The same literal-report Bradley--Terry negative log likelihood used by
RLHF reward fitting. -/
noncomputable def sourceRlhfBinaryReportLoss
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {horizon : ℕ} (sample : Fin horizon → BinaryPairwiseReport Alternative)
    (reward : ScoreVector Alternative) : ℝ :=
  -pairwiseLogLikelihood (ofBinaryReports sample) Real.sigmoid reward

/-- The normalized DPO policy obtained from a fitted reward. -/
noncomputable def sourceDpoPolicy
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (reference : PMF Alternative) (reward : ScoreVector Alternative)
    (klWeight : ℝ) : PMF Alternative :=
  dpoOptimalPolicy (contextFreeAlternativePolicy reference) (fun _ => reward) klWeight PUnit.unit.{1}

/-- The fixed-reference representative of a full-support DPO policy's implicit
reward.  Subtracting the reference coordinate selects the same normalization
used by the source's finite reward MLE. -/
noncomputable def sourceDpoNormalizedMLEReward
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (scoreReference : Alternative) (reference policy : PMF Alternative)
    (klWeight : ℝ) : ScoreVector Alternative :=
  fun alternative =>
    dpoImplicitReward (contextFreeAlternativePolicy policy)
      (contextFreeAlternativePolicy reference) klWeight PUnit.unit.{1} alternative -
    dpoImplicitReward (contextFreeAlternativePolicy policy)
      (contextFreeAlternativePolicy reference) klWeight PUnit.unit.{1} scoreReference

/-- RLHF's finite KL-regularized exponential-tilt policy. -/
noncomputable def sourceRlhfPolicy
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (reference : PMF Alternative) (reward : ScoreVector Alternative)
    (klWeight : ℝ) : PMF Alternative :=
  contextExponentialTiltPolicy
    (contextFreeAlternativePolicy reference) (fun _ => reward) klWeight⁻¹ PUnit.unit.{1}

/-- A DPO optimizer is compared only with full-support policies, the domain on
which the policy/reference log-ratio appearing in the source objective is a
genuine finite real reward. -/
def IsSourceDpoLossMinimizer
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {horizon : ℕ} (sample : Fin horizon → BinaryPairwiseReport Alternative)
    (reference : PMF Alternative) (klWeight : ℝ) (policy : PMF Alternative) : Prop :=
  PMFFullSupport policy ∧
    ∀ candidate : PMF Alternative, PMFFullSupport candidate →
      sourceDpoBinaryReportLoss sample reference policy klWeight ≤
        sourceDpoBinaryReportLoss sample reference candidate klWeight

/-- Corrected Appendix-F.3 target: with positive DPO/RLHF weight and a
full-support reference policy, the normalized DPO and RLHF policies agree;
the induced DPO reward differs from the fitted reward only by its unavoidable
additive constant, and their literal-report objectives agree. -/
def appendixF3DpoRlhfEquivalenceSpec : Prop :=
  ∀ {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {horizon : ℕ} (sample : Fin horizon → BinaryPairwiseReport Alternative)
    (scoreReference : Alternative) (reference : PMF Alternative)
    (reward : ScoreVector Alternative) {klWeight : ℝ},
    isPairwiseMLE (ofBinaryReports sample) Real.sigmoid scoreReference reward →
    0 < klWeight → PMFFullSupport reference →
      sourceDpoPolicy reference reward klWeight = sourceRlhfPolicy reference reward klWeight ∧
      sourceDpoBinaryReportLoss sample reference
          (sourceDpoPolicy reference reward klWeight) klWeight =
        sourceRlhfBinaryReportLoss sample reward ∧
      RewardEquivalent
        (dpoImplicitReward
          (contextFreeAlternativePolicy (sourceDpoPolicy reference reward klWeight))
          (contextFreeAlternativePolicy reference) klWeight)
        (fun (_ : PUnit.{1}) => reward) ∧
      IsSourceDpoLossMinimizer sample reference klWeight
        (sourceDpoPolicy reference reward klWeight) ∧
      ∀ policy : PMF Alternative,
        IsSourceDpoLossMinimizer sample reference klWeight policy →
          isPairwiseMLE (ofBinaryReports sample) Real.sigmoid scoreReference
            (sourceDpoNormalizedMLEReward scoreReference reference policy klWeight) ∧
          sourceDpoPolicy reference
            (sourceDpoNormalizedMLEReward scoreReference reference policy klWeight)
            klWeight = policy

/-- Source Lemma 1: the population Bradley--Terry linearization bounds. -/
def lemma1Spec : Prop :=
  ∀ {User Alternative : Type} [Fintype User] [DecidableEq User]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative),
    UnitIntervalUtilityProfile utility → ∀ {btScale : ℝ}, 0 < btScale →
      ∀ first second : Alternative,
        btScale *
              (sigmoidChordSlope btScale * populationAverageUtility population utility first -
                (1 : ℝ) / 4 * populationAverageUtility population utility second) ≤
            (populationBradleyTerryPreference population utility btScale).prob PUnit.unit.{1}
              first second - (1 : ℝ) / 2 ∧
          (populationBradleyTerryPreference population utility btScale).prob PUnit.unit.{1}
              first second - (1 : ℝ) / 2 ≤
            btScale *
              ((1 : ℝ) / 4 * populationAverageUtility population utility first -
                sigmoidChordSlope btScale * populationAverageUtility population utility second)

/--
Source Theorem 2: the population Borda distortion factor together with the
literal finite-user expected-welfare guarantee and its explicit source rate.
-/
def theorem2Spec : Prop :=
  (
      ∀ {User Alternative : Type} [Fintype User] [DecidableEq User]
        [Fintype Alternative] [DecidableEq Alternative]
        (population : PMF User) (utility : FiniteUtilityProfile User Alternative),
        UnitIntervalUtilityProfile utility → ∀ (sampling : PMF Alternative)
          {btScale : ℝ}, 0 < btScale → ∀ (winner : Alternative),
            (∀ alternative,
              pairwiseBordaScore.{0, 0} sampling
                  (populationBradleyTerryPreference.{0, 0, 0} population utility btScale) alternative ≤
                pairwiseBordaScore.{0, 0} sampling
                  (populationBradleyTerryPreference.{0, 0, 0} population utility btScale) winner) →
              ∀ alternative,
                (sigmoidChordSlope btScale / ((1 : ℝ) / 4)) ^ 2 *
                    populationAverageUtility population utility alternative ≤
                  populationAverageUtility population utility winner
  ) ∧
  (
      ∀ {User Alternative : Type} [Fintype User] [DecidableEq User]
        [Fintype Alternative] [DecidableEq Alternative] [Nonempty Alternative]
        (population : PMF User) (utility : FiniteUtilityProfile User Alternative),
        UnitIntervalUtilityProfile utility → ∀ (sampling : PMF Alternative) {btScale : ℝ},
          0 < btScale → ∀ (responseLaw : PMF (theorem2UserResponseTable Alternative)),
          theorem2UserResponseCalibrated responseLaw
            (populationBradleyTerryPreference.{0, 0, 0} population utility btScale) →
          ∀ (users comparisonsPerUser : ℕ), 0 < users → 0 < comparisonsPerUser →
          ∀ (minimumMass delta : ℝ), 0 < minimumMass →
          (∀ alternative, minimumMass ≤ (sampling alternative).toReal) →
          0 < delta → delta ≤ 1 →
          2 * (Fintype.card Alternative : ℝ) *
            Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * minimumMass / 8) ≤ delta →
          ∀ (winner : (Fin users →
            (theorem2UserResponseTable Alternative ×
              (Fin comparisonsPerUser → Alternative × Alternative))) → Alternative),
          (∀ sample alternative,
            theorem11IidUserLatentBordaScore alternative sample ≤
              theorem11IidUserLatentBordaScore (winner sample) sample) →
          ∀ benchmark : Alternative,
          (1 - delta) *
            ((sigmoidChordSlope btScale / ((1 : ℝ) / 4)) ^ 2 *
                populationAverageUtility population utility benchmark -
              2 * theorem2SourceRate (Fintype.card Alternative) users comparisonsPerUser
                minimumMass delta / (btScale * ((1 : ℝ) / 4))) ≤
            pmfExp
              (pmfProduct (Fin users)
                (theorem2UserResponseTable Alternative ×
                  (Fin comparisonsPerUser → Alternative × Alternative))
                (pmfProd responseLaw
                  (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
                    (theorem2UserPairLabelLaw sampling))))
              (fun sample => populationAverageUtility population utility (winner sample))
  )

/--
Source Theorem 3: both the one-comparison and multi-comparison
Condorcet-loser branches of the voting-rule-independent lower bound.
-/
def theorem3Spec : Prop :=
  (
      ∀ {beta : ℝ} (hbeta : 0 < beta),
        ∀ (pairSampling : ∀ n : ℕ, PMF (Fin (n + 2) × Fin (n + 2)))
          (rule : ∀ n horizon,
            (Fin horizon → ((Fin (n + 2) × Fin (n + 2)) × Bool)) → PMF (Fin (n + 2)))
          (delta : ℝ),
          0 < delta →
          ∃ N : ℕ, ∀ n ≥ N, ∃ special : Fin (n + 2),
            Set.Infinite {horizon : ℕ |
              let policy := theorem3ObservationSelectionLaw
                (theorem3ManyAlternativeObservationLaw (pairSampling n) beta
                  (theorem3DiagonalEpsilon n) hbeta (theorem3DiagonalEpsilon_pos n)
                  special horizon)
                (rule n horizon)
              (∀ alternative,
                populationAverageUtility
                  (theorem3TwoTypePopulation beta (theorem3DiagonalEpsilon n) hbeta
                    (theorem3DiagonalEpsilon_pos n))
                  (theorem3ManyAlternativeUtility (theorem3DiagonalEpsilon n) 1 special)
                    alternative ≤
                  populationAverageUtility
                    (theorem3TwoTypePopulation beta (theorem3DiagonalEpsilon n) hbeta
                      (theorem3DiagonalEpsilon_pos n))
                    (theorem3ManyAlternativeUtility (theorem3DiagonalEpsilon n) 1 special)
                      special) ∧
                beta / 2 * (1 + Real.exp (-beta)) / (1 - Real.exp (-beta)) - delta <
                  theorem3SpecialTypeMass beta (theorem3DiagonalEpsilon n) /
                    policyAverageUtility
                      (theorem3TwoTypePopulation beta (theorem3DiagonalEpsilon n) hbeta
                        (theorem3DiagonalEpsilon_pos n))
                      (theorem3ManyAlternativeUtility (theorem3DiagonalEpsilon n) 1 special)
                      policy}
  ) ∧
  (∀ {beta : ℝ} (hbeta : 0 < beta) (d : ℕ) (hd : 2 ≤ d)
      (pairSampling : ∀ n : ℕ, PMF (Fin (n + 3) × Fin (n + 3)))
      (hpair : ∀ n (ordinary : Fin (n + 3)), ordinary ≠ (0 : Fin (n + 3)) →
        0 < (pairSampling n (ordinary, 0)).toReal)
      (reportLaw : ∀ n : ℕ,
        PMF (Fin d → ((Fin (n + 3) × Fin (n + 3)) × Bool)))
      (hcoordinate : ∀ n (comparisonIndex : Fin d),
        (reportLaw n).map (fun report => report comparisonIndex) =
          theorem3ManyAlternativeOneComparisonLawXi (pairSampling n) beta
            (theorem3D2DiagonalEpsilon n) (theorem3D2DiagonalXi n) hbeta
            (theorem3D2DiagonalEpsilon_pos n) (0 : Fin (n + 3)))
      (rule : ∀ n horizon,
        (Fin horizon → (Fin d → ((Fin (n + 3) × Fin (n + 3)) × Bool))) →
          PMF (Fin (n + 3)))
      (hcriterion : ∀ n horizon,
        theorem3ProbabilisticCondorcetLoserCriterion (rule n horizon)
          (fun observation alternative =>
            theorem3IidEmpiricalStrictCondorcetLoser
              (fun ordinary => theorem3ReportedOrdinarySpecialMargin alternative ordinary)
              alternative observation))
      (delta : ℝ) (hdelta : 0 < delta),
      ∃ N : ℕ, ∀ n ≥ N, ∀ᶠ horizon : ℕ in Filter.atTop,
        beta / 2 * (1 + Real.exp (-beta)) / (1 - Real.exp (-beta)) - delta <
          theorem3SpecialTypeMass beta (theorem3D2DiagonalEpsilon n) /
            policyAverageUtility
              (theorem3TwoTypePopulation beta (theorem3D2DiagonalEpsilon n) hbeta
                (theorem3D2DiagonalEpsilon_pos n))
              (theorem3ManyAlternativeUtility (theorem3D2DiagonalEpsilon n)
                (theorem3D2DiagonalXi n) (0 : Fin (n + 3)))
              (theorem3ObservationSelectionLaw
                (theorem3IidUserReportBatchLaw (reportLaw n) horizon)
                (rule n horizon)))

/--
Source Corollary 4: the population maximal-lottery inequality together with
the source's literal iid empirical-Maximal-Lotteries route. The latter records
the direct finite zero-sum equilibrium condition and the finite expected
welfare bound whose explicit source rate yields the displayed limiting
distortion guarantee. On a finite sample where an off-diagonal comparison
count is zero, the checked rule explicitly gives that unobserved margin the
neutral value zero; this totalization is a disclosed finite-sample convention,
not an additional source model assumption.
-/
def corollary4Spec : Prop :=
  (
      ∀ {User Alternative : Type} [Fintype User] [DecidableEq User]
        [Fintype Alternative] [DecidableEq Alternative]
        (population : PMF User) (utility : FiniteUtilityProfile User Alternative),
        UnitIntervalUtilityProfile utility → ∀ {btScale : ℝ}, 0 < btScale →
          ∀ (maximalLottery benchmark : PMF Alternative),
            (∀ opponent,
              0 ≤ populationBradleyTerryPolicyMargin
                population utility btScale maximalLottery opponent) →
              (sigmoidChordSlope btScale / ((1 : ℝ) / 4)) *
                  policyAverageUtility population utility benchmark ≤
                policyAverageUtility population utility maximalLottery
  ) ∧
  (
      ∀ {User Alternative : Type} [Fintype User] [DecidableEq User]
        [Fintype Alternative] [DecidableEq Alternative] [Nonempty Alternative]
        {users comparisonsPerUser : ℕ}
        (population : PMF User) (utility : FiniteUtilityProfile User Alternative),
        UnitIntervalUtilityProfile utility → ∀ {btScale : ℝ}, 0 < btScale →
          ∀ (responseLaw : PMF (theorem2UserResponseTable Alternative))
            (preference : PairwisePreference PUnit.{1} Alternative),
            theorem2UserResponseCalibrated responseLaw preference →
            ∀ (sampling : PMF Alternative),
              0 < users → 0 < comparisonsPerUser →
              ∀ (minimumMass : ℝ), 0 < minimumMass →
                (∀ alternative, minimumMass ≤ (sampling alternative).toReal) →
                ∀ (delta : ℝ), 0 < delta → delta ≤ 1 →
                  (Fintype.card Alternative : ℝ) ^ 2 *
                      Real.exp
                        (-((users * comparisonsPerUser : ℕ) : ℝ) * minimumMass ^ 2 / 8) ≤
                    delta →
                    preference =
                      populationBradleyTerryPreference population utility btScale →
                      (∀ sample : Fin users →
                          (theorem2UserResponseTable Alternative ×
                            (Fin comparisonsPerUser → Alternative × Alternative)),
                        IsEmpiricalMaximalLottery
                          (fun first second =>
                            theorem10IidUserPaperWinRate first second sample)
                          (corollary4IidUserEmpiricalMaximalLottery sample)) ∧
                      let failureBudget := delta / (Fintype.card Alternative : ℝ) ^ 2
                      ∃ benchmark : PMF Alternative,
                        (∀ other : PMF Alternative,
                          policyAverageUtility population utility other ≤
                            policyAverageUtility population utility benchmark) ∧
                        (1 - delta) *
                            ((sigmoidChordSlope btScale / ((1 : ℝ) / 4)) *
                                policyAverageUtility population utility benchmark -
                              theorem10SourceRate users comparisonsPerUser minimumMass
                                failureBudget / (btScale * ((1 : ℝ) / 4))) ≤
                          pmfExp
                            (theorem7IidUserBatchLaw
                              responseLaw sampling users comparisonsPerUser)
                            (fun sample => policyAverageUtility population utility
                              (corollary4IidUserEmpiricalMaximalLottery sample))
  )

/--
Source Theorem 5: for every positive temperature and every `m ≥ 3`, Borda has
a realized lower bound strictly above the universal voting-rule coefficient;
the construction's coefficient is asymptotic to `β`.
-/
def theorem5Spec : Prop :=
  (
    ∀ {beta : ℝ} (hbeta : 0 < beta),
      let gamma := theorem12LogChoice beta
      ∃ (hgamma : 0 < gamma) (hgamma_lt_one : gamma < 1),
        beta / 2 * (1 + Real.exp (-beta)) / (1 - Real.exp (-beta)) <
          theorem12Eq10Coefficient beta gamma ∧
        ∀ q : ℝ, q < theorem12Eq10Coefficient beta gamma →
          ∀ m : ℕ, 3 ≤ m →
            ∃ (epsilon : ℝ) (hepsilon : 0 < epsilon)
              (hepsilon_lt_half : epsilon < (1 : ℝ) / 2)
              (sampling : PMF (Fin 3 ⊕ Fin (m - 3))),
              epsilon ^ 2 < 1 - epsilon ∧ Fintype.card (Fin 3 ⊕ Fin (m - 3)) = m ∧
                let collapse := theorem12CloneCollapse (1 : Fin 3) (m - 3)
                let splitUtility :=
                  theorem12SplitUtility (theorem12Utility epsilon (epsilon ^ 2) gamma) collapse
                let population := theorem12Population beta epsilon gamma hbeta hepsilon (by linarith)
                  hgamma hgamma_lt_one
                let preference :=
                  populationBradleyTerryPreference.{0, 0, 0} population splitUtility beta
                UnitIntervalUtilityProfile splitUtility ∧
                  PMFFullSupport sampling ∧
                  q <
                    populationAverageUtility population splitUtility (Sum.inl (0 : Fin 3)) /
                      populationAverageUtility population splitUtility (Sum.inl (2 : Fin 3)) ∧
                  Filter.Tendsto
                    (fun horizon =>
                      AppliedModelingLib.pmfProb (theorem12IidBordaReportBatchLaw
                        (theorem12OneComparisonReportLaw sampling preference) horizon)
                        (fun sample => theorem12IidEmpiricalBordaFailure theorem12OneComparisonWins
                          theorem12OneComparisonIncidences (Sum.inl (2 : Fin 3)) sample))
                    Filter.atTop (𝓝 0)
  ) ∧
  Filter.Tendsto
    (fun beta : ℝ => theorem12Eq10Coefficient beta (theorem12LogChoice beta) / beta)
    Filter.atTop (𝓝 1)

/--
Source Appendix Theorem 12: the formal all-`m` Borda lower-bound construction,
its strict separation from the universal voting-rule coefficient, and its
asymptotic `β` coefficient.
-/
def theorem12Spec : Prop :=
  (
    ∀ {beta gamma q : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma)
      (hgamma_lt_one : gamma < 1),
      q < theorem12Eq10Coefficient beta gamma → ∀ m : ℕ, 3 ≤ m →
      ∃ (epsilon : ℝ) (hepsilon : 0 < epsilon)
        (hepsilon_lt_half : epsilon < (1 : ℝ) / 2)
        (sampling : PMF (Fin 3 ⊕ Fin (m - 3))),
        epsilon ^ 2 < 1 - epsilon ∧ Fintype.card (Fin 3 ⊕ Fin (m - 3)) = m ∧
          let collapse := theorem12CloneCollapse (1 : Fin 3) (m - 3)
          let splitUtility :=
            theorem12SplitUtility (theorem12Utility epsilon (epsilon ^ 2) gamma) collapse
          let population := theorem12Population beta epsilon gamma hbeta hepsilon (by linarith)
            hgamma hgamma_lt_one
          let preference :=
            populationBradleyTerryPreference.{0, 0, 0} population splitUtility beta
          UnitIntervalUtilityProfile splitUtility ∧
            PMFFullSupport sampling ∧
            q <
              populationAverageUtility population splitUtility (Sum.inl (0 : Fin 3)) /
                populationAverageUtility population splitUtility (Sum.inl (2 : Fin 3)) ∧
            Filter.Tendsto
              (fun horizon =>
                AppliedModelingLib.pmfProb (theorem12IidBordaReportBatchLaw
                  (theorem12OneComparisonReportLaw sampling preference) horizon)
                  (fun sample => theorem12IidEmpiricalBordaFailure theorem12OneComparisonWins
                    theorem12OneComparisonIncidences (Sum.inl (2 : Fin 3)) sample))
              Filter.atTop (𝓝 0)
  ) ∧
  (
    ∀ {beta gamma : ℝ}, 0 < beta → 0 < gamma → gamma < 1 →
      beta / 2 * (1 + Real.exp (-beta)) / (1 - Real.exp (-beta)) <
        theorem12Eq10Coefficient beta gamma
  ) ∧
  Filter.Tendsto
    (fun beta : ℝ => theorem12Eq10Coefficient beta (theorem12LogChoice beta) / beta)
    Filter.atTop (𝓝 1)

/--
Source Theorem 6: an explicit large-`β` tail of finite alignment instances.
The source's `exp(Ω(β))` wording is asymptotic, and its Appendix F.2
construction itself chooses the finite alternative count as a function of
`β`; `β ≥ 10` is a concrete tail witness for that sequence.
-/
def theorem6Spec : Prop :=
  ∀ {beta : ℝ} (hbeta_ten : 10 ≤ beta),
    ∃ (eta : ℝ) (heta_pos : 0 < eta) (heta_le_one : eta ≤ 1),
      3 ≤ Fintype.card (theorem6Alternative (theorem6CopyCount beta)) ∧
      letI : MeasurableSpace
        (BinaryPairwiseReport (theorem6Alternative (theorem6CopyCount beta))) := ⊤
      ∀ᵐ path ∂AppliedModelingLib.finitePMFIidPathMeasure
          (theorem12OneComparisonReportLaw
            (uniformPMF (theorem6Alternative (theorem6CopyCount beta)))
            (theorem6Preference beta)),
        ∀ᶠ horizon : ℕ in Filter.atTop,
          ∀ reward : ScoreVector (theorem6Alternative (theorem6CopyCount beta)),
            isPairwiseMLE
              (ofBinaryReports (AppliedModelingLib.finitePMFIidPathPrefix path horizon))
              Real.sigmoid
              (theorem6A : theorem6Alternative (theorem6CopyCount beta)) reward →
              ∃ rewardPolicy welfarePolicy : PMF
                  (theorem6Alternative (theorem6CopyCount beta)),
                finiteKLDivergence rewardPolicy
                    (theorem6Reference (theorem6Epsilon eta)
                      (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos)
                      (theorem6CopyCount_pos beta)) ≤ 1 ∧
                (∀ other : PMF (theorem6Alternative (theorem6CopyCount beta)),
                  finiteKLDivergence other
                      (theorem6Reference (theorem6Epsilon eta)
                        (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos)
                        (theorem6CopyCount_pos beta)) ≤ 1 →
                    pmfExp other reward ≤ pmfExp rewardPolicy reward) ∧
                finiteKLDivergence welfarePolicy
                    (theorem6Reference (theorem6Epsilon eta)
                      (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos)
                      (theorem6CopyCount_pos beta)) ≤ 1 ∧
                (∀ other : PMF (theorem6Alternative (theorem6CopyCount beta)),
                  finiteKLDivergence other
                      (theorem6Reference (theorem6Epsilon eta)
                        (theorem6Epsilon_pos eta) (theorem6Epsilon_lt_one heta_pos)
                        (theorem6CopyCount_pos beta)) ≤ 1 →
                    pmfExp other (theorem6Welfare beta) ≤
                      pmfExp welfarePolicy (theorem6Welfare beta)) ∧
                Real.exp beta / (44 * beta) ≤
                  pmfExp welfarePolicy (theorem6Welfare beta) /
                    pmfExp rewardPolicy (theorem6Welfare beta)

/--
Source Theorem 7: the population NLHF factor and its literal finite-user
expected-welfare guarantee.
-/
def theorem7Spec : Prop :=
  (
      ∀ {User Alternative : Type} [Fintype User] [DecidableEq User]
        [Fintype Alternative] [DecidableEq Alternative]
        (population : PMF User) (utility : FiniteUtilityProfile User Alternative),
        UnitIntervalUtilityProfile utility → ∀ {btScale : ℝ}, 0 < btScale →
          ∀ (reference : PMF Alternative) (klBudget : ℝ)
            (nlhfPolicy benchmark : PMF Alternative),
            0 ≤ klBudget →
            PMFFullSupport reference →
            IsConstrainedPopulationBradleyTerryMaximin
              population utility btScale reference klBudget nlhfPolicy →
            InFiniteKLBall reference klBudget benchmark →
              (sigmoidChordSlope btScale / ((1 : ℝ) / 4)) *
                  policyAverageUtility population utility benchmark ≤
                policyAverageUtility population utility nlhfPolicy
  ) ∧
  (
      ∀ {User Alternative : Type} [Fintype User] [DecidableEq User]
        [Fintype Alternative] [DecidableEq Alternative] [Nonempty Alternative]
        {users comparisonsPerUser : ℕ}
        (population : PMF User) (utility : FiniteUtilityProfile User Alternative),
        UnitIntervalUtilityProfile utility → ∀ {btScale : ℝ}, 0 < btScale →
          ∀ (responseLaw : PMF (theorem2UserResponseTable Alternative))
            (preference : PairwisePreference PUnit.{1} Alternative),
            theorem2UserResponseCalibrated responseLaw preference →
            ∀ (sampling : PMF Alternative), 0 < users → 0 < comparisonsPerUser →
              ∀ (minimumMass : ℝ), 0 < minimumMass →
              (∀ alternative, minimumMass ≤ (sampling alternative).toReal) →
              ∀ (reference : PMF Alternative) (klBudget : ℝ) (hbudget : 0 ≤ klBudget),
                PMFFullSupport reference →
                ∀ (delta : ℝ), 0 < delta → delta ≤ 1 →
                  (Fintype.card Alternative : ℝ) ^ 2 *
                    Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) *
                      minimumMass ^ 2 / 8) ≤ delta →
                  preference = populationBradleyTerryPreference population utility btScale →
                  let failureBudget := delta / (Fintype.card Alternative : ℝ) ^ 2
                  ∃ benchmark : PMF Alternative,
                    finiteKLDivergence benchmark reference ≤ klBudget ∧
                    (∀ other : PMF Alternative, finiteKLDivergence other reference ≤ klBudget →
                      policyAverageUtility population utility other ≤
                        policyAverageUtility population utility benchmark) ∧
                    (1 - delta) *
                        ((sigmoidChordSlope btScale / ((1 : ℝ) / 4)) *
                            policyAverageUtility population utility benchmark -
                          theorem10SourceRate users comparisonsPerUser minimumMass failureBudget /
                            (btScale * ((1 : ℝ) / 4))) ≤
                      pmfExp (theorem7IidUserBatchLaw responseLaw sampling users comparisonsPerUser)
                        (fun sample => policyAverageUtility population utility
                          (theorem7IidUserEmpiricalPolicy reference klBudget hbudget sample))
  )

/-- Source Corollary 8: the regularized NLHF welfare consequence. -/
def corollary8Spec : Prop :=
  ∀ {User Alternative : Type} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative),
    UnitIntervalUtilityProfile utility → ∀ {btScale : ℝ}, 0 < btScale →
      ∀ (reference policy : PMF Alternative) (klRegularization : ℝ),
        0 ≤ klRegularization →
        PMFFullSupport reference →
        AppliedModelingLib.GameTheory.PreferenceGame.IsRegularizedPreferenceGameEquilibrium
          (PMF.pure PUnit.unit.{1})
          (populationBradleyTerryPreference population utility btScale)
          (contextFreeAlternativePolicy reference) (contextFreeAlternativePolicy policy)
          klRegularization →
        ∀ benchmark : PMF Alternative,
          AppliedModelingLib.finiteKLDivergence benchmark reference ≤
            AppliedModelingLib.finiteKLDivergence policy reference →
            (sigmoidChordSlope btScale / ((1 : ℝ) / 4)) *
                policyAverageUtility population utility benchmark ≤
              policyAverageUtility population utility policy

/-- Source Theorem 9: unbounded RLHF distortion under correlated sampling. -/
def theorem9Spec : Prop :=
  ∀ {beta : ℝ} (hbeta : 0 < beta) (bound : ℝ),
    ∃ (m : ℕ) (hm : 3 ≤ m),
      ∃ (epsilon : NNReal) (hepsilon_pos : 0 < epsilon) (hepsilon_lt_one : epsilon < 1),
        let population := lemma15Population
        let utility := theorem9PrefixProfile beta m
        let comparisonSampling := theorem9ComparisonSampling m hm epsilon
        let reference := theorem9UniformReference m (by omega)
        let klBudget := Real.log (m : ℝ)
        UnitIntervalUtilityProfile utility ∧
          PMFFullSupport reference ∧
          comparisonSampling.IsSymmetric ∧
          comparisonSampling.HasZeroDiagonal ∧
          comparisonSampling.HasFullOffDiagonalSupport ∧
          0 ≤ klBudget ∧
          letI : MeasurableSpace (BinaryPairwiseReport (Fin m)) := ⊤
          ∀ᵐ path ∂AppliedModelingLib.finitePMFIidPathMeasure
              (theorem9OneComparisonReportLaw beta m hm epsilon),
            ∀ᶠ horizon : ℕ in Filter.atTop,
              (∃ reward : ScoreVector (Fin m),
                isPairwiseMLE
                  (ofBinaryReports (AppliedModelingLib.finitePMFIidPathPrefix path horizon))
                  sigmoidCDFLikePairwiseLink (⟨0, by omega⟩ : Fin m) reward) ∧
              ∀ reward : ScoreVector (Fin m),
                isPairwiseMLE
                    (ofBinaryReports (AppliedModelingLib.finitePMFIidPathPrefix path horizon))
                    sigmoidCDFLikePairwiseLink (⟨0, by omega⟩ : Fin m) reward →
                  ∃ rewardPolicy welfarePolicy : PMF (Fin m),
                    finiteKLDivergence rewardPolicy reference ≤ klBudget ∧
                    (∀ other : PMF (Fin m),
                      finiteKLDivergence other reference ≤ klBudget →
                        pmfExp other reward ≤ pmfExp rewardPolicy reward) ∧
                    finiteKLDivergence welfarePolicy reference ≤ klBudget ∧
                    (∀ other : PMF (Fin m),
                      finiteKLDivergence other reference ≤ klBudget →
                        policyAverageUtility population utility other ≤
                          policyAverageUtility population utility welfarePolicy) ∧
                    0 < policyAverageUtility population utility rewardPolicy ∧
                    bound < policyAverageUtility population utility welfarePolicy /
                      policyAverageUtility population utility rewardPolicy

/-- Source Lemma 10: uniform empirical pairwise-win concentration. -/
def lemma10Spec : Prop :=
  ∀ {Alternative : Type} [Fintype Alternative] [DecidableEq Alternative] [Nonempty Alternative]
    {responseLaw : PMF (theorem2UserResponseTable Alternative)}
    {preference : PairwisePreference PUnit.{1} Alternative}
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ)
    (minimumMass delta : ℝ),
    0 < users → 0 < comparisonsPerUser → 0 < minimumMass →
    (∀ alternative, minimumMass ≤ (sampling alternative).toReal) →
    0 < delta → delta ≤ 1 →
    (Fintype.card Alternative : ℝ) ^ 2 *
      Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * minimumMass ^ 2 / 8) ≤ delta →
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
            preference.prob PUnit.unit pair.1 pair.2|) ≤ delta

/-- Source Lemma 11: the simultaneous normalized-Borda source-rate bound. -/
def lemma11Spec : Prop :=
  ∀ {Alternative : Type} [Fintype Alternative] [DecidableEq Alternative] [Nonempty Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit.{1} Alternative)
    (users comparisonsPerUser : ℕ),
    0 < users → 0 < comparisonsPerUser →
    theorem2UserResponseCalibrated responseLaw preference →
    ∀ (minimumMass delta : ℝ),
      0 < minimumMass →
      (∀ alternative, minimumMass ≤ (sampling alternative).toReal) →
      0 < delta → delta ≤ 1 →
      2 * (Fintype.card Alternative : ℝ) *
        Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * minimumMass / 8) ≤ delta →
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
                pairwiseBordaScore sampling preference alternative|) ≤ delta

/-- Source Proposition 13: both directions of constrained/regularized NLHF equivalence. -/
def proposition13Spec : Prop :=
  (
      ∀ {Alternative : Type} [Fintype Alternative] [DecidableEq Alternative]
        (preference : PairwisePreference PUnit.{1} Alternative)
        (reference policy : PMF Alternative) (klWeight : WithTop ℝ),
        PMFFullSupport reference →
        AppliedModelingLib.GameTheory.PreferenceGame.IsContextFreeExtendedRegularizedPreferenceGameEquilibrium
          preference reference policy klWeight →
        AppliedModelingLib.GameTheory.PreferenceGame.IsFiniteKLPreferenceMaximin
          preference reference (finiteKLDivergence policy reference) policy
  ) ∧
  (
      ∀ {Alternative : Type} [Fintype Alternative] [DecidableEq Alternative]
        (preference : PairwisePreference PUnit.{1} Alternative)
        (reference policy : PMF Alternative) (klBudget : ℝ),
        0 ≤ klBudget → PMFFullSupport reference →
          AppliedModelingLib.GameTheory.PreferenceGame.IsFiniteKLPreferenceMaximin
            preference reference klBudget policy →
          ∃ klWeight : WithTop ℝ,
            AppliedModelingLib.GameTheory.PreferenceGame.IsContextFreeExtendedRegularizedPreferenceGameEquilibrium
                preference reference policy klWeight
  )

/-- Source Proposition 14: both directions of constrained/regularized RLHF equivalence. -/
def proposition14Spec : Prop :=
  (
      ∀ {Alternative : Type} [Fintype Alternative] [DecidableEq Alternative]
        (reference policy : PMF Alternative) (score : Alternative → ℝ)
        (klWeight : WithTop ℝ),
        PMFFullSupport reference →
        IsFiniteKLExtendedRegularizedUtilityMax reference policy score klWeight →
        finiteKLDivergence policy reference ≤ finiteKLDivergence policy reference ∧
          ∀ other : PMF Alternative,
            finiteKLDivergence other reference ≤ finiteKLDivergence policy reference →
              pmfExp other score ≤ pmfExp policy score
  ) ∧
  (
      ∀ {Alternative : Type} [Fintype Alternative] [DecidableEq Alternative]
        (reference policy : PMF Alternative) (score : Alternative → ℝ) (klBudget : ℝ),
        0 ≤ klBudget → PMFFullSupport reference →
          finiteKLDivergence policy reference ≤ klBudget →
          (∀ other : PMF Alternative,
            finiteKLDivergence other reference ≤ klBudget →
              pmfExp other score ≤ pmfExp policy score) →
          ∃ klWeight : WithTop ℝ,
            IsFiniteKLExtendedRegularizedUtilityMax reference policy score klWeight
  )

/--
Source Lemma 15: there exists an infinite sequence of alternatives and a user
utility distribution with the stated welfare decay and adjacent-comparison
property.  Natural number `n` names the source alternative `a_{n+1}`; the
finite user carrier represents the three-atom distribution used by the source
construction, without exposing that construction in the reviewed statement.
-/
def lemma15Spec : Prop :=
  ∀ {beta : ℝ} (hbeta : 0 < beta),
    ∃ (population : PMF (Fin 3))
      (utility : FiniteUtilityProfile (Fin 3) ℕ),
      UnitIntervalUtilityProfile utility ∧
      populationAverageUtility population utility 0 = (1 : ℝ) / 3 ∧
      (∀ n : ℕ,
        0 < populationAverageUtility population utility (n + 1) ∧
          populationAverageUtility population utility (n + 1) ≤
            populationAverageUtility population utility n -
            2 / (3 * beta) *
              Real.log (1 + Real.tanh
                ((beta * populationAverageUtility population utility n) / 4) ^ 3) ∧
          populationAverageUtility population utility (n + 1) <
            populationAverageUtility population utility n ∧
          (1 : ℝ) / 2 <
            (populationBradleyTerryPreference population utility beta).prob
              PUnit.unit.{1} (n + 1) n)

end GolzHaghtalabYang2025Distortion
