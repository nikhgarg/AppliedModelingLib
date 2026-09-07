import GGSG19TopThree.Implementation
import GGSG19TopThree.Assumptions
import GGSG19TopThree.MallowsJointDP
import GGSG19TopThree.UniformTieDesignInvariance

/-!
# Human-Facing Interface for GGSG19

This compact interface gives stable paper-label names for the main source
statements in Garg--Gelauff--Sakshuwong--Goel (2019).  The proofs are thin
wrappers around the detailed proof surface in `ProofInterface.lean`.
-/

namespace GGSG19TopThree.ProofBridge

open AppliedModelingLib.SocialChoice.Ranking
open AppliedModelingLib.Probability
open MeasureTheory
open scoped ProbabilityTheory

noncomputable section

/-! ## Source elicitation and aggregation model -/

/--
The paper's data-valued `K`-ranking score: a revealed candidate receives the
positional score at her reported rank, while an unrevealed candidate receives
zero.  Ranks are zero-based in Lean, so `rank < K` is the source condition
`sigma_v(i) <= K`.
-/
def kRankingScore {n : ℕ} (K : ℕ) (beta : Candidate n → ℝ)
    (ranking : Ranking n) (candidate : Candidate n) : ℝ :=
  if (rankOf ranking candidate).val < K then
    beta (rankOf ranking candidate)
  else 0

/--
Source status: direct source formula.

Source `K`-ranking formula, exposed as an equality of data-valued scores.
-/
theorem source_model_k_ranking_score {n : ℕ} (K : ℕ)
    (beta : Candidate n → ℝ) (ranking : Ranking n)
    (candidate : Candidate n) :
    kRankingScore K beta ranking candidate =
      (if (rankOf ranking candidate).val < K then
        beta (rankOf ranking candidate)
      else 0) := by
  rfl

/--
Source status: direct source formula.

Source `K`-approval formula: top-`K` candidates get one, all others zero.
-/
theorem source_model_k_approval_score {n : ℕ} (K : ℕ)
    (ranking : Ranking n) (candidate : Candidate n) :
    AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K ranking candidate =
      if (rankOf ranking candidate).val < K then 1 else 0 := by
  rfl

/--
The source class of nonconstant nonincreasing positional scores, expressed in
the adjacent-drop coordinates used by the formalization.  Nonincreasing
adjacent scores are exactly nonnegative drops, and nonconstancy is exactly one
strictly positive drop.
-/
theorem source_model_reasonable_positional_scoring_rules
    {n : ℕ} (beta : Candidate n → ℝ) :
    ReasonablePrefixWeights
        (fun cut : RankingProperPrefixCut n =>
          beta ⟨cut.val, by omega⟩ -
            beta ⟨cut.val + 1, by omega⟩) ↔
      (∀ cut : RankingProperPrefixCut n,
        beta ⟨cut.val + 1, by omega⟩ ≤
          beta ⟨cut.val, by omega⟩) ∧
      ∃ cut : RankingProperPrefixCut n,
        beta ⟨cut.val + 1, by omega⟩ <
          beta ⟨cut.val, by omega⟩ := by
  simp only [ReasonablePrefixWeights, sub_nonneg, sub_pos]

/-- Average cumulative score after `N` voters, in the source normalization. -/
def iidUniformTieCandidateAverageScore
    {Candidate Signal Tie : Type*}
    (score : Candidate → Signal → ℝ)
    (path : ℕ → Signal × Tie) (N : ℕ) (candidate : Candidate) : ℝ :=
  (N : ℝ)⁻¹ * iidUniformTieCandidateScore score path N candidate

/--
Source status: direct source formula and outcome definition.

Source cumulative-score and outcome formula.  For a nonempty sample, dividing
all cumulative scores by `N` preserves every strict comparison and equality;
the resulting tier outcome therefore uses exactly the independent uniform tie
ranking already present in `iidUniformTieTieredCorrect`.
-/
theorem source_model_cumulative_scores_ranking_and_outcome
    {n Stage : ℕ}
    (score : Candidate n → Ranking n → ℝ)
    (targetPrefix : Fin Stage → Finset (Candidate n))
    (path : ℕ → Ranking n × Ranking n) (N : ℕ) (hN : 0 < N) :
    (∀ candidate : Candidate n,
      iidUniformTieCandidateAverageScore score path N candidate =
        (N : ℝ)⁻¹ *
          (∑ voter ∈ Finset.range N, score candidate (path voter).1)) ∧
      (iidUniformTieTieredCorrect score targetPrefix path N ↔
        ∀ stage : Fin Stage,
          ∀ hi lo : Candidate n,
            hi ∈ targetPrefix stage → lo ∉ targetPrefix stage →
              iidUniformTieCandidateAverageScore score path N lo <
                  iidUniformTieCandidateAverageScore score path N hi ∨
                (iidUniformTieCandidateAverageScore score path N lo =
                    iidUniformTieCandidateAverageScore score path N hi ∧
                  rankOf (path N).2 hi < rankOf (path N).2 lo)) := by
  constructor
  · intro candidate
    rfl
  · have hscale : 0 < (N : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hN)
    unfold iidUniformTieTieredCorrect
    constructor
    · intro h stage hi lo hhi hlo
      rcases h stage hi lo hhi hlo with hlt | ⟨heq, hrank⟩
      · left
        exact mul_lt_mul_of_pos_left hlt hscale
      · right
        exact ⟨congrArg (fun value : ℝ => (N : ℝ)⁻¹ * value) heq, hrank⟩
    · intro h stage hi lo hhi hlo
      rcases h stage hi lo hhi hlo with hlt | ⟨heq, hrank⟩
      · left
        exact lt_of_mul_lt_mul_left hlt hscale.le
      · right
        refine ⟨?_, hrank⟩
        exact mul_left_cancel₀ (ne_of_gt hscale) heq

/--
Source status: direct source definition.

Paper definition of an exponential large-deviation rate.
-/
def paper_definition_large_deviation_rate (A : ℕ → ℝ) (r : ℝ) : Prop :=
  (∀ N : ℕ, 0 ≤ A N) ∧
    Filter.Tendsto A Filter.atTop (nhds 0) ∧
    0 < r ∧
    Filter.Tendsto
      (fun N : ℕ => -((N : ℝ)⁻¹) * Real.log (A N))
      Filter.atTop (nhds r)

/--
Source status: exact proved expansion of source Definition 2.

Definition 2 as a proved formula row.  This theorem, rather than an attested
`Prop` declaration, is the review-surface target for the source definition.
-/
theorem paper_definition_large_deviation_rate_statement
    (A : ℕ → ℝ) (r : ℝ) :
    paper_definition_large_deviation_rate A r ↔
      (∀ N : ℕ, 0 ≤ A N) ∧
        Filter.Tendsto A Filter.atTop (nhds 0) ∧
        0 < r ∧
        Filter.Tendsto
          (fun N : ℕ => -((N : ℝ)⁻¹) * Real.log (A N))
          Filter.atTop (nhds r) := by
  rfl

/--
Source Definition 1: asymptotic design invariance.

A reasonable rule family is design-invariant for a goal when all reasonable
rules induce the same limiting outcome.

Source status: direct paper-facing Definition 1 row.
-/
def paper_definition_design_invariant_for
    {Ω Rule Outcome : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (reasonable : Rule → Prop)
    (outcome : Rule → ℕ → Ω → Outcome) (Ostar : Outcome) : Prop :=
  ∀ β : Rule, reasonable β →
    ∀ᵐ ω ∂μ, ∀ᶠ N : ℕ in Filter.atTop, outcome β N ω = Ostar

/--
Source status: direct source definition.

Source Definition 1, including its probability-one path quantifier.
-/
def paper_definition_design_invariant
    {Ω Rule Outcome : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (reasonable : Rule → Prop)
    (outcome : Rule → ℕ → Ω → Outcome) : Prop :=
  ∃ Ostar : Outcome,
    paper_definition_design_invariant_for μ reasonable outcome Ostar

/--
Source status: exact proved expansion of source Definition 1.

Definition 1 exposed as an exact proved statement rather than a `Prop`
attestation.
-/
theorem paper_definition_design_invariant_statement
    {Ω Rule Outcome : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (reasonable : Rule → Prop)
    (outcome : Rule → ℕ → Ω → Outcome) :
    paper_definition_design_invariant μ reasonable outcome ↔
      ∃ Ostar : Outcome,
        ∀ β : Rule, reasonable β →
          ∀ᵐ ω ∂μ,
            ∀ᶠ N : ℕ in Filter.atTop, outcome β N ω = Ostar := by
  rfl

/--
Source Definition 3: rate optimality.

Within a feasible design class, a rule is rate-optimal when it maximizes the
finite learning rate.

Source status: direct paper-facing Definition 3 row.
-/
def paper_definition_rate_optimal
    {Rule : Type*} (feasible : Set Rule) (rate : Rule → ℝ) (βstar : Rule) : Prop :=
  βstar ∈ feasible ∧ ∀ β : Rule, β ∈ feasible → rate β ≤ rate βstar

/--
Source status: exact proved expansion of source Definition 3.

Definition 3 exposed as its exact feasibility-and-maximality formula.
-/
theorem paper_definition_rate_optimal_statement
    {Rule : Type*} (feasible : Set Rule) (rate : Rule → ℝ) (βstar : Rule) :
    paper_definition_rate_optimal feasible rate βstar ↔
      βstar ∈ feasible ∧
        ∀ β : Rule, β ∈ feasible → rate β ≤ rate βstar := by
  rfl

/--
Source status: direct source theorem.

Source Proposition `thm:consistency`, tiered finite-ranking form, with the
paper's literal independent uniform tie breaking.  The reverse implication
includes the exact-equality boundary: a centered nondegenerate score gap
crosses below zero infinitely often, while a degenerate gap is broken against
the target with positive probability.  No generic no-tie premise is added.
-/
theorem source_proposition1_thm_consistency_tiered
    {n Stage : ℕ}
    (law : PMF (Ranking n))
    (targetPrefix : Fin Stage → Finset (Candidate n)) :
    (∀ stage : Fin Stage,
      ∀ hi lo : Candidate n,
        hi ∈ targetPrefix stage →
          lo ∉ targetPrefix stage →
            ∀ cut : RankingProperPrefixCut n,
              rankingTopPrefixProb law lo cut <
                rankingTopPrefixProb law hi cut) ↔
      PropositionOneUniformTieConsistency law targetPrefix := by
  constructor
  · intro hdominance
    exact
      ⟨(rankingTieredStrictPrefixDominance_iff_almostSure_uniformTieCorrect
        law targetPrefix).mp hdominance⟩
  · intro hconsistency
    exact
      (rankingTieredStrictPrefixDominance_iff_almostSure_uniformTieCorrect
        law targetPrefix).mpr hconsistency.allReasonableRules

/--
Source Proposition `thm:pairwiselearning`, finite-support form.  The ordinary
two-sided case has the paper's displayed Chernoff exponent; the explicit
one-sided branches record finite-candidate boundary cases where the finite
real rate is a zero-gap rate or the error event is eventually empty.
-/
theorem source_proposition2_thm_pairwiselearning_finite_support
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal)) :
    (ExponentialRateCertificate
          (pairwiseScoringErrorProb law hiScore loScore)
          (pairwiseScoringRate law hiScore loScore) ∨
        (∃ pZero : ℝ,
          AppliedModelingLib.pmfProb law
              (fun signal => hiScore signal - loScore signal = 0) =
            pZero ∧
          0 < pZero ∧
          ExponentialRateCertificate
            (pairwiseScoringErrorProb law hiScore loScore)
            (-Real.log pZero)) ∨
        (∀ᶠ n in Filter.atTop,
          pairwiseScoringErrorProb law hiScore loScore n = 0)) ∧
      ∀ n,
        pairwiseScoringErrorProb law hiScore loScore n ≤
          Real.exp (-(n : ℝ) * pairwiseScoringRate law hiScore loScore) :=
  ⟨proposition2_pairwise_exact_rate_or_boundary_from_finite_support_mean_nonneg
      law hiScore loScore hmean,
    pairwiseScoringErrorProb_le_exp_neg_pairwiseScoringRate_of_mean_nonneg
      law hiScore loScore hmean⟩

/--
Source Proposition `lem:pairwiselearning_approval`, finite ternary form for
K-approval score gaps.  The finite-rate branch is exactly the paper's closed
form `approvalPairwiseRate`; the other branch is the strict boundary where the
mistake event is eventually empty.
-/
theorem source_proposition3_lem_pairwiselearning_approval_finite_ternary
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {pUp pDown pZero : ℝ}
    (hle : pDown ≤ pUp)
    (hscore :
      ∀ signal,
        hiScore signal - loScore signal = 1 ∨
          hiScore signal - loScore signal = 0 ∨
          hiScore signal - loScore signal = -1)
    (hUpProb :
      AppliedModelingLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = 1) =
        pUp)
    (hDownProb :
      AppliedModelingLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = -1) =
        pDown)
    (hZeroProb :
      AppliedModelingLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = 0) =
        pZero) :
    ExponentialRateCertificate
        (pairwiseScoringErrorProb law hiScore loScore)
        (approvalPairwiseRate pUp pDown) ∨
      (∀ᶠ n in Filter.atTop,
        pairwiseScoringErrorProb law hiScore loScore n = 0) :=
  proposition3_approval_pairwise_exact_rate_or_eventually_zero_from_ternary_scores
    law hiScore loScore hle hscore hUpProb hDownProb hZeroProb

/--
Source Proposition `thm:goal_learning`, finite relevant-pair aggregation form.
The finite aggregate has an exact finite exponent unless all relevant
pairwise errors are eventually empty, represented as extended rate `⊤`.
-/
theorem source_proposition4_thm_goal_learning_finite_support
    {Pair Candidate Signal : Type*} [Fintype Pair] [DecidableEq Pair]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    (hmean :
      ∀ pair,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal =>
            score (hi pair) signal - score (lo pair) signal)) :
    ∃ rate : WithTop ℝ,
      HasExtendedExponentialRate
        (fun sampleSize =>
          ∑ pair : Pair,
            finiteScoreGapPairwiseErrorProb law score
              (hi pair) (lo pair) sampleSize)
        rate := by
  simpa using
    (proposition4_outcome_error_extended_rate_from_relevant_pairs_finite_support_trichotomy
      law score hi lo hmean
      (pairWeight := fun _ => (1 : ℝ))
      (by intro pair; exact zero_le_one)
      (by intro pair; exact zero_lt_one))

/--
Source Proposition `thm:goal_learning`, exact minimum-rate endpoint.  The
unit-weight aggregate is the source quantity `Q^N`.  A pair with no positive-
sample errors has extended rate `⊤`, so it does not lower a finite aggregate
minimum.
-/
theorem source_proposition4_thm_goal_learning_exact_minimum_rate
    {Pair Candidate Signal : Type*} [Fintype Pair] [Nonempty Pair]
    [DecidableEq Pair] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    (hmean :
      ∀ pair,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score (hi pair) signal - score (lo pair) signal)) :
    HasExtendedExponentialRate
      (fun sampleSize =>
        ∑ pair : Pair,
          finiteScoreGapPairwiseErrorProb law score
            (hi pair) (lo pair) sampleSize)
      (finiteOutcomeLearningExtendedRate
        (fun pair : Pair =>
          pairwiseScoringExtendedRate law
            (score (hi pair)) (score (lo pair)))) :=
  by
    convert
      outcomeError_hasExtendedExponentialRate_at_finiteOutcomeLearningExtendedRate_of_relevant_pairs_finite_support
        law score hi lo hmean
        (by intro pair; exact zero_le_one)
        (by intro pair; exact zero_lt_one)
      using 1 ; simp

/--
Source Proposition `thm:goal_learning`, finite-`N` clause.  `Pair` indexes the
cross-tier ordered pairs for an arbitrary finite goal, and `hcard` is the
source observation that there are at most `M^2` such pairs.

Source status: direct source theorem clause.
Source note: Exact source TeX line 531 and proof lines 1337--1350.
-/
theorem source_proposition4_thm_goal_learning_finite_sample_M_sq_bound
    {Pair Candidate Signal : Type*} [Fintype Pair] [Nonempty Pair]
    [Fintype Candidate] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    (hmean :
      ∀ pair,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score (hi pair) signal - score (lo pair) signal))
    (hcard : Fintype.card Pair ≤ Fintype.card Candidate ^ 2)
    (n : ℕ) :
    (∑ pair : Pair,
      finiteScoreGapPairwiseErrorProb law score (hi pair) (lo pair) n) ≤
      (Fintype.card Candidate : ℝ) ^ 2 *
        Real.exp (-(n : ℝ) *
          finiteOutcomeLearningRate
            (fun pair : Pair =>
              pairwiseScoringRate law
                (score (hi pair)) (score (lo pair)))) := by
  calc
    (∑ pair : Pair,
        finiteScoreGapPairwiseErrorProb law score (hi pair) (lo pair) n) ≤
        (Fintype.card Pair : ℝ) *
          Real.exp (-(n : ℝ) *
            finiteOutcomeLearningRate
              (fun pair : Pair =>
                pairwiseScoringRate law
                  (score (hi pair)) (score (lo pair)))) :=
      finiteRelevantScoreGapErrorSum_le_card_mul_exp_at_finiteOutcomeLearningRate_of_mean_nonneg
        law score hi lo hmean n
    _ ≤ (Fintype.card Candidate : ℝ) ^ 2 *
          Real.exp (-(n : ℝ) *
            finiteOutcomeLearningRate
              (fun pair : Pair =>
                pairwiseScoringRate law
                  (score (hi pair)) (score (lo pair)))) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hcard
      · exact Real.exp_nonneg _

/--
Source Theorem `lem:randomizebetterscoring` for an arbitrary finite goal.
`Pair` is the goal's finite set of cross-tier pairs.  The premise `hstatic`
is the source formula `β* = ∑_p d_p β_p`; `hstatic_bdd` states that the
displayed finite real rates exist.  The theorem is not restricted to
W-selection.

Source status: direct source theorem.
Source note: Exact source TeX lines 679--689 and proof lines 1397--1430.
-/
theorem source_theorem1_lem_randomizebetterscoring_arbitrary_goal
    {Pair Rule Signal : Type*} [Fintype Pair] [Nonempty Pair]
    [Fintype Rule] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ)
    (gap : Pair → Rule → Signal → ℝ)
    (staticGap : Pair → Signal → ℝ)
    (hstatic :
      ∀ pair signal,
        staticGap pair signal =
          ∑ rule : Rule, weight rule * gap pair rule signal)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hstatic_bdd :
      ∀ pair,
        BddBelow (Set.range fun z : ℝ =>
          finiteLogMGF law (staticGap pair) z)) :
    finiteOutcomeLearningRate
        (fun pair : Pair =>
          randomizedScoringMixtureRate law weight (gap pair)) ≤
      finiteOutcomeLearningRate
        (fun pair : Pair => finiteChernoffRate law (staticGap pair)) :=
  randomized_scoring_outcome_rate_le_static_of_weighted_score
    law weight gap staticGap hstatic hweight hsum hstatic_bdd

/--
Boundary-aware W-selection specialization of Source Theorem
`lem:randomizebetterscoring`.  The
convex-combination static rule is reasonable, selects the target W-set, and
weakly dominates the randomized scoring rule in extended finite outcome rate.

Source status: support specialization.
Source note: The exact arbitrary-goal finite-rate row is
`source_theorem1_lem_randomizebetterscoring_arbitrary_goal`.
-/
theorem source_theorem1_lem_randomizebetterscoring
    {Rule Cut Candidate Signal : Type*}
    [Fintype Rule] [DecidableEq Rule] [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hdiff : ∀ rule, ReasonablePrefixWeights (diff rule))
    (hdom :
      StrictTopPrefixDominanceOn (prefixProbFromEvent law inPrefix)
        (fun hi lo => hi ∈ winnerSet ∧ lo ∉ winnerSet)) :
    ReasonablePrefixWeights
        (fun cut => ∑ rule : Rule, weight rule * diff rule cut) ∧
        Filter.Tendsto
        (scoreTopSelectionErrorProb law
          (fun candidate =>
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix candidate)
          winnerSet
          (fun n sample =>
            scoreTopSelectedSetOfCard
              (iidSampleCandidateScore
                (fun candidate =>
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix candidate)
                sample)
              winnerSet))
        Filter.atTop (nhds 0) ∧
      randomizedScoringPrefixStaticDominatesRandomized
        law weight diff inPrefix winnerSet hweight hsum := by
  simpa [randomizedScoringPrefixStaticDominatesRandomized] using
    randomized_scoring_prefix_actual_cross_tier_static_selection_and_automatic_extended_static_rate_comparison
      law weight diff inPrefix winnerSet hweight hsum hdiff hdom

/--
Source Theorem `lem:randomizenotbetterapproval`, fixed-pair form.  For any
finite randomized K-approval rule, some static component weakly dominates the
randomized pairwise rate; zero-base static boundaries are treated as top
extended rates.
-/
theorem source_theorem2_lem_randomizenotbetterapproval_pairwise
    {n : ℕ} {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (law : PMF (Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hi lo : Candidate n) :
    ∃ rule : Rule,
      (approvalPairwiseRate
          (∑ rule : Rule,
            weight rule * kApprovalPairUpProb law (K rule) hi lo)
          (∑ rule : Rule,
            weight rule * kApprovalPairDownProb law (K rule) hi lo) :
        WithTop ℝ) ≤
        approvalPairwiseExtendedRate
          (kApprovalPairUpProb law (K rule) hi lo)
          (kApprovalPairDownProb law (K rule) hi lo) :=
  randomized_k_approval_pairwise_extended_rate_le_static
    law K weight hweight hsum hi lo

/--
Source status: direct source theorem.

Source Theorem `lem:randomizebetterapproval_Wselection`, concrete finite
constructed-law endpoint: the six-ranking law is design-invariant for
W-selection and 50/50 randomized approval strictly beats every static
K-approval cutoff in the finite family.
-/
theorem source_theorem_lem_randomizebetterapproval_w_selection_constructed
    : StrictTopPrefixDominanceOn
        constructedWSelectionRanking1TopPrefixProb
        constructedWSelectionCrossTier ∧
      (Finset.univ : Finset (Fin 4)).sup' finiteUnivNonempty
          (fun K =>
            finiteOutcomeLearningRate
              (constructedWSelectionRanking1StaticKRate K)) <
        finiteOutcomeLearningRate
          constructedWSelectionRanking1RandomizedApprovalRate :=
  randomized_approval_w_selection_constructed_ranking_law_design_invariant_and_all_static_k

/--
Source empirical support example: the Durham Ward 1 probabilities, represented
exactly as the printed thousandths, make the equal 3/4-approval mixture's
two-pair outcome rate strictly exceed both static outcome rates.
-/
theorem source_example_durham_ward1_randomized_approval_improves_static3_static4 :
    max
        (finiteOutcomeLearningRate durhamWard1K3Rate)
        (finiteOutcomeLearningRate durhamWard1K4Rate) <
      finiteOutcomeLearningRate durhamWard1RandomizedRate :=
  durham_ward1_randomized_approval_improves_static3_static4

/-- Expected cross-tier pairwise errors under the source's deterministic `phi = 0` law. -/
def zeroNoiseTopWApprovalError {n : ℕ}
    (center : Ranking n) (W : Candidate n) (sampleSize : ℕ) : ℝ :=
  ∑ pair : TopWSelectionPair center W,
    finiteScoreGapPairwiseErrorProb (PMF.pure center)
      (fun candidate ranking =>
        AppliedModelingLib.SocialChoice.Ranking.kApprovalScore W.val ranking candidate)
      pair.hi pair.lo sampleSize

/--
Source Corollary `lem:mallowsnorando`, deterministic `phi = 0` endpoint.
W-approval makes every positive-support cross-tier score gap strictly positive,
so its error aggregate is eventually zero and has top extended rate.  It
therefore weakly dominates every randomized mechanism's extended rate.

Source status: direct source boundary clause.
Source note: Exact source TeX lines 291--295, 727--733, and 755.
-/
theorem source_corollary_lem_mallowsnorando_zero_noise
    {n : ℕ} (center : Ranking n) (W : Candidate n) (hW : 0 < W.val)
    (randomizedRate : WithTop ℝ) :
    HasExtendedExponentialRate (zeroNoiseTopWApprovalError center W) ⊤ ∧
      randomizedRate ≤ ⊤ := by
  letI : Nonempty (TopWSelectionPair center W) :=
    instNonemptyTopWSelectionPair center W hW
  have hsupport :
      ∀ pair : TopWSelectionPair center W,
        ∀ ranking : Ranking n,
          0 < ((PMF.pure center : PMF (Ranking n)) ranking).toReal →
            0 <
              AppliedModelingLib.SocialChoice.Ranking.kApprovalScore W.val ranking pair.hi -
                AppliedModelingLib.SocialChoice.Ranking.kApprovalScore W.val ranking pair.lo := by
    intro pair ranking hmass
    have hranking : ranking = center := by
      by_contra hne
      have hzero :
          ((PMF.pure center : PMF (Ranking n)) ranking).toReal = 0 := by
        simp [PMF.pure_apply, hne]
      rw [hzero] at hmass
      exact (lt_irrefl 0) hmass
    subst ranking
    have hhi :
        AppliedModelingLib.SocialChoice.Ranking.approvedByK W.val center pair.hi := by
      change (rankOf center pair.hi).val < W.val
      exact pair.rank_hi_lt_cut
    have hlo :
        ¬ AppliedModelingLib.SocialChoice.Ranking.approvedByK W.val center pair.lo := by
      change ¬ (rankOf center pair.lo).val < W.val
      exact Nat.not_lt.mpr pair.cut_le_rank_lo
    simp [AppliedModelingLib.SocialChoice.Ranking.kApprovalScore, hhi, hlo]
  have hzero :
      ∀ᶠ sampleSize in Filter.atTop,
        zeroNoiseTopWApprovalError center W sampleSize = 0 := by
    simpa [zeroNoiseTopWApprovalError] using
      (proposition4_relevant_score_gap_aggregate_eventually_zero_from_support_pos
        (PMF.pure center)
        (fun candidate ranking =>
          AppliedModelingLib.SocialChoice.Ranking.kApprovalScore W.val ranking candidate)
        (fun pair : TopWSelectionPair center W => pair.hi)
        (fun pair : TopWSelectionPair center W => pair.lo)
        (pairWeight := fun _ => (1 : ℝ)) hsupport)
  exact ⟨HasExtendedExponentialRate.infinite hzero, le_top⟩

/--
Source status: direct source proof step.

Source Mallows pivotal-pair step: for every nontrivial `K`-approval cutoff,
the overall top-`W` learning rate is attained at the adjacent center-rank pair
`(W,W+1)`.  This is the exact bridge used to lift the fixed-pair theorem to
the source corollary.
-/
theorem source_proof_mallows_common_pivotal_pair
    {n : ℕ} (center : Ranking n) (q : ℝ) (W : Candidate n)
    (hDomain : assumption_mallows_nontrivial_winner_and_parameter_domain q W)
    (K : ℕ) (hK_pos : 0 < K) (hK_lt : K < n + 2) :
    mallowsTopWKApprovalOutcomeRate
        (MallowsSpec.ofQ center q hDomain.2.1) W hDomain.1 K =
      mallowsTopWKApprovalPairRate
        (MallowsSpec.ofQ center q hDomain.2.1) W K
        (topWBoundaryPair center W hDomain.1) :=
  mallows_top_w_k_approval_boundary_pair_from_mallows_model_q_lt_one
    (MallowsSpec.ofQ center q hDomain.2.1) W hDomain.1 K
    hK_pos hK_lt hDomain.2.2

/--
Source Corollary `lem:mallowsnorando`, positive-parameter Mallows endpoint.
The redundant explicit premise `0 < M.q` has been removed: it is already a
field of `MallowsSpec`.  The separate theorem above covers the source's
deterministic `phi = 0` law without pretending that `MallowsSpec` contains it.

Source Corollary `lem:mallowsnorando`: under a finite Mallows model with
`q < 1`, an approval-rate-optimal static K-approval cutoff weakly dominates
any finite randomized family of nontrivial K-approval rules.

Source status: direct source theorem clause for `0 < q < 1`.
Source note: Exact source TeX lines 727--733 and proof lines 1531--1534.
-/
theorem source_corollary_lem_mallowsnorando
    {n : ℕ} (center : Ranking n) (q : ℝ) (W : Candidate n)
    (hDomain : assumption_mallows_nontrivial_winner_and_parameter_domain q W)
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (K : Rule → ℕ)
    (hK_pos : ∀ rule, 0 < K rule)
    (hK_lt : ∀ rule, K rule < n + 2)
    (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1) :
    ∃ cut : RankingProperPrefixCut n,
      (∀ cut' : RankingProperPrefixCut n,
        mallowsTopWKApprovalOutcomeRate
            (MallowsSpec.ofQ center q hDomain.2.1) W hDomain.1
            (cut'.val + 1) ≤
          mallowsTopWKApprovalOutcomeRate
            (MallowsSpec.ofQ center q hDomain.2.1) W hDomain.1
            (cut.val + 1)) ∧
      mallowsTopWRandomizedKApprovalOutcomeRate
          (MallowsSpec.ofQ center q hDomain.2.1) W hDomain.1 K weight ≤
        mallowsTopWKApprovalOutcomeRate
          (MallowsSpec.ofQ center q hDomain.2.1) W hDomain.1
          (cut.val + 1) := by
  exact
    mallows_k_approval_no_randomization_to_approval_rate_optimal_from_mallows_model_q_lt_one
      (MallowsSpec.ofQ center q hDomain.2.1) W hDomain.1 hDomain.2.2
      K hK_pos hK_lt weight hweight hsum

/--
Source Theorem `lem:mallowsnotWK`: a four-candidate high-noise Mallows
counterexample where W-approval is not approval-rate optimal.
-/
theorem source_theorem_lem_mallowsnotWK_counterexample :
    ∃ M : MallowsSpec 2,
      M.center = Equiv.refl (Candidate 2) ∧
        M.q = mallowsHighNoisePhi ∧
          ∃ better : Fin 3,
            better ≠ (2 : Fin 3) ∧
              finiteOutcomeLearningRate
                  (mallowsW3StaticKApprovalPairRate M (2 : Fin 3)) <
                finiteOutcomeLearningRate
                  (mallowsW3StaticKApprovalPairRate M better) :=
  mallows_high_noise_w3_w_approval_not_approval_rate_optimal_counterexample

/--
Joint-location probability for reference items three and four in the source's
four-candidate repeated-insertion construction.  The two insertion positions
are independent; the second insertion updates both tracked final positions.
-/
noncomputable def mallowsFourCandidate34JointLocationProb
    (q : ℝ) (hq : 0 ≤ q) (ell k : Fin 4) : ℝ :=
  ∑ inserted3 : Fin 4, ∑ inserted4 : Fin 4,
    if mallowsUpdatePairState
          (2 : Fin 4) (3 : Fin 4) (3 : Fin 4) inserted4
          (mallowsUpdatePairState
            (2 : Fin 4) (3 : Fin 4) (2 : Fin 4) inserted3
            (mallowsPairInitialState 4)) =
        (some ell, some k) then
      ((mallowsInsertionPMF q hq (2 : Fin 4)) inserted3).toReal *
        ((mallowsInsertionPMF q hq (3 : Fin 4)) inserted4).toReal
    else 0

/--
Source status: direct source appendix formula.

Source appendix matrix for the joint final positions of reference items three
and four.  Diagonal entries vanish.  Every off-diagonal entry is the printed
power of `q`, divided by `N_3 = 1+q+q^2` and
`N_4 = 1+q+q^2+q^3`; the exponent branch is exactly the push-down caused when
item four is inserted weakly above item three.
-/
theorem source_proof_mallows_four_candidate_joint_location_matrix
    (q : ℝ)
    (hDomain : assumption_mallows_repeated_insertion_parameter_domain q)
    (ell k : Fin 4) :
    mallowsFourCandidate34JointLocationProb q hDomain.1 ell k =
      if ell = k then 0
      else
        q ^ (if ell.val < k.val then
            5 - ell.val - k.val
          else
            6 - ell.val - k.val) /
          (1 + q + q ^ 2) /
          (1 + q + q ^ 2 + q ^ 3) := by
  fin_cases ell <;> fin_cases k <;>
    simp [mallowsFourCandidate34JointLocationProb,
      mallowsUpdatePairState, mallowsUpdateTrackedPosition,
      mallowsBumpPosition, mallowsPairInitialState,
      mallowsInsertionPMF_apply_toReal, mallowsInsertionWeight,
      mallowsInsertionNormalizer, Fin.sum_univ_four,
      Finset.sum_range_succ] <;>
    ring

/--
Source status: direct source algorithm specification.

Primitive-input semantic specification for the source's arbitrary-pair
repeated-insertion dynamic program.  It constructs the Mallows kernel from the
source parameter inequalities and requires exact cells, normalization, the
dense operation count, and the advertised polynomial bound.
-/
def MallowsArbitraryPairJointLocationDPOfQSpec
    {N : ℕ} (q : ℝ) (hq_nonneg : 0 ≤ q) (hq_le_one : q ≤ 1)
    (leftStage rightStage : Fin N) : Prop :=
  let model := MallowsRepeatedInsertionModel.ofQ q hq_nonneg hq_le_one
  (∀ state : MallowsPairPositionState N,
    (mallowsPairDPTabulationRun model leftStage rightStage N).table state =
      ((mallowsPairProcess model leftStage rightStage N) state).toReal) ∧
    (∑ state : MallowsPairPositionState N,
      (mallowsPairDPTabulationRun model leftStage rightStage N).table state = 1) ∧
    (mallowsPairDPTabulationRun model leftStage rightStage N).scalarOperations =
      mallowsPairDPDenseOperationBudget N ∧
    (mallowsPairDPTabulationRun model leftStage rightStage N).scalarOperations ≤
      (N + 1) ^ 6

/--
Source status: direct source algorithm theorem.

The primitive-input implementation discharges the complete source algorithm
specification rather than assuming a correctness-bearing record.
-/
theorem mallows_arbitrary_pair_joint_location_dp_ofQ_spec
    {N : ℕ} (q : ℝ) (hq_nonneg : 0 ≤ q) (hq_le_one : q ≤ 1)
    (leftStage rightStage : Fin N) :
    MallowsArbitraryPairJointLocationDPOfQSpec
      q hq_nonneg hq_le_one leftStage rightStage :=
  mallows_arbitrary_pair_joint_location_dp_spec
    (MallowsRepeatedInsertionModel.ofQ q hq_nonneg hq_le_one)
    leftStage rightStage

/--
Source status: direct source algorithm theorem.

Theorem 4 discussion and appendix repeated-insertion computation: for any two
center ranks, the displayed repeated-insertion recurrence computes every cell
of their exact joint location distribution.  The complete table is normalized,
and a dense implementation uses at most `(N+1)^6` scalar transition terms.
This is the general algorithm used by the paper, not merely its fixed
four-candidate output.
-/
theorem source_mallows_arbitrary_pair_joint_location_dynamic_program
    {N : ℕ} (q : ℝ)
    (hDomain : assumption_mallows_repeated_insertion_parameter_domain q)
    (leftStage rightStage : Fin N) :
    (∀ state : MallowsPairPositionState N,
      (mallowsPairDPTabulationRun
          (MallowsRepeatedInsertionModel.ofQ q hDomain.1 hDomain.2)
          leftStage rightStage N).table state =
        ((mallowsPairProcess
          (MallowsRepeatedInsertionModel.ofQ q hDomain.1 hDomain.2)
          leftStage rightStage N) state).toReal) ∧
      (∑ state : MallowsPairPositionState N,
        (mallowsPairDPTabulationRun
          (MallowsRepeatedInsertionModel.ofQ q hDomain.1 hDomain.2)
          leftStage rightStage N).table state = 1) ∧
      (mallowsPairDPTabulationRun
          (MallowsRepeatedInsertionModel.ofQ q hDomain.1 hDomain.2)
          leftStage rightStage N).scalarOperations =
        mallowsPairDPDenseOperationBudget N ∧
      (mallowsPairDPTabulationRun
          (MallowsRepeatedInsertionModel.ofQ q hDomain.1 hDomain.2)
          leftStage rightStage N).scalarOperations ≤ (N + 1) ^ 6 :=
  mallows_arbitrary_pair_joint_location_dp_exact_and_polynomial
    (MallowsRepeatedInsertionModel.ofQ q hDomain.1 hDomain.2)
    leftStage rightStage

/--
Source status: direct source formula.

The source repeated-insertion probability formula, including the full closed
Mallows parameter domain.  This row makes the kernel used by the dynamic
program reviewable independently of the algorithm-correctness conclusion.
-/
theorem source_mallows_repeated_insertion_probability_formula
    {N : ℕ} (q : ℝ)
    (hDomain : assumption_mallows_repeated_insertion_parameter_domain q)
    (stage inserted : Fin N) :
    ((mallowsInsertionPMF q hDomain.1 stage) inserted).toReal =
        if inserted.val ≤ stage.val then
          q ^ (stage.val - inserted.val) /
            Finset.sum (Finset.range (stage.val + 1))
              (fun r => q ^ (stage.val - r))
        else 0 := by
  rw [mallowsInsertionPMF_apply_toReal]
  unfold mallowsInsertionWeight mallowsInsertionNormalizer
  by_cases hle : inserted.val ≤ stage.val <;> simp [hle]

end

end GGSG19TopThree.ProofBridge
