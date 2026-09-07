import AppliedModelingLib.Foundations.Probability.FiniteSupportMGF
import AppliedModelingLib.Foundations.Probability.FiniteEmpiricalMultinomialCounts
import AppliedModelingLib.Foundations.Probability.FiniteProductMultinomialCounts
import AppliedModelingLib.Foundations.Probability.FiniteTypeLogMass
import AppliedModelingLib.Foundations.Probability.IIDLargeDeviations
import AppliedModelingLib.Foundations.Probability.LargeDeviations
import AppliedModelingLib.Foundations.Probability.Weighted
import AppliedModelingLib.SocialChoice.Ranking.Approval
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Implementation Theorems: Who is in Your Top Three?

This file starts the Lean audit for Garg, Gelauff, Sakshuwong, and Goel
(2019).  The first reusable surface is the large-deviation learning-rate
section: score-gap log-MGF formulas, the K-approval ternary simplification, and
the finite aggregation step from pairwise error rates to outcome error rates.

The finite Chernoff/LDP layer now includes reusable exact-rate constructors,
including a support-aware stationary-tilt method-of-types route.  The
formulas, finite aggregation, and most certificate-independent infrastructure
are paper-independent and live in `AppliedModelingLib`.
-/

open scoped BigOperators

namespace GGSG19TopThree

noncomputable section

open AppliedModelingLib.Probability

/-- Paper Definition: a sequence has large-deviation rate `r`. -/
abbrev largeDeviationRate (A : ℕ → ℝ) (r : ℝ) : Prop :=
  HasExponentialRate A r

/-! ## Asymptotic design-invariance core -/

/--
Prefix-score representation of a positional rule after summation by parts:
`diff k` is the nonnegative adjacent score drop at prefix cut `k`.
-/
def prefixExpectedScore
    {Cut Candidate : Type*} [Fintype Cut]
    (diff : Cut → ℝ) (topPrefixProb : Candidate → Cut → ℝ)
    (candidate : Candidate) : ℝ :=
  ∑ k : Cut, diff k * topPrefixProb candidate k

/-- Prefix probabilities induced by a finite one-voter signal law. -/
def prefixProbFromEvent
    {Cut Candidate Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (candidate : Candidate) (cut : Cut) : ℝ :=
  AppliedModelingLib.pmfProb law (fun signal => inPrefix signal candidate cut)

/-- One-voter prefix-score contribution induced by a prefix event. -/
def prefixScoreFromEvent
    {Cut Candidate Signal : Type*} [Fintype Cut]
    (diff : Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (candidate : Candidate) (signal : Signal) : ℝ :=
  ∑ cut : Cut,
    diff cut * if inPrefix signal candidate cut then (1 : ℝ) else 0

/--
Proper top-prefix cuts for a ranking over `n + 2` candidates.  Cut `k`
represents the source prefix of size `k + 1`, so these are exactly the proper
prefixes top-1 through top-(M-1).
-/
abbrev RankingProperPrefixCut (n : ℕ) := Fin (n + 1)

/--
Paper ranking-law top-prefix event: candidate `candidate` appears in the
proper top prefix represented by `cut` in ranking `ranking`.
-/
def rankingInTopPrefix {n : ℕ}
    (ranking : AppliedModelingLib.SocialChoice.Ranking.Ranking n)
    (candidate : AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (cut : RankingProperPrefixCut n) : Prop :=
  (AppliedModelingLib.SocialChoice.Ranking.rankOf ranking candidate).val ≤ cut.val

instance rankingInTopPrefix_decidable {n : ℕ}
    (ranking : AppliedModelingLib.SocialChoice.Ranking.Ranking n)
    (candidate : AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (cut : RankingProperPrefixCut n) :
    Decidable (rankingInTopPrefix ranking candidate cut) := by
  unfold rankingInTopPrefix
  infer_instance

/-- Paper ranking-law top-prefix probability induced by a finite ranking law. -/
def rankingTopPrefixProb {n : ℕ}
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (candidate : AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (cut : RankingProperPrefixCut n) : ℝ :=
  prefixProbFromEvent law rankingInTopPrefix candidate cut

/-- Prefix-score contribution for the paper's finite ranking model. -/
def rankingPrefixScore {n : ℕ}
    (diff : RankingProperPrefixCut n → ℝ)
    (candidate : AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (ranking : AppliedModelingLib.SocialChoice.Ranking.Ranking n) : ℝ :=
  prefixScoreFromEvent diff rankingInTopPrefix candidate ranking

/--
Prefix scores are linear in the adjacent prefix-weight vector.  This is the
finite algebra behind replacing a randomized scoring-rule mechanism by its
static convex combination.
-/
theorem prefixScoreFromEvent_weighted_sum
    {Rule Cut Candidate Signal : Type*} [Fintype Rule] [Fintype Cut]
    (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (candidate : Candidate) (signal : Signal) :
    prefixScoreFromEvent
        (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
        inPrefix candidate signal =
      ∑ rule : Rule,
        weight rule *
          prefixScoreFromEvent (diff rule) inPrefix candidate signal := by
  classical
  unfold prefixScoreFromEvent
  calc
    ∑ cut : Cut,
        (∑ rule : Rule, weight rule * diff rule cut) *
          (if inPrefix signal candidate cut then (1 : ℝ) else 0)
        =
        ∑ cut : Cut, ∑ rule : Rule,
          weight rule *
            (diff rule cut *
              (if inPrefix signal candidate cut then (1 : ℝ) else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro cut _
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro rule _
          ring
    _ =
        ∑ rule : Rule, ∑ cut : Cut,
          weight rule *
            (diff rule cut *
              (if inPrefix signal candidate cut then (1 : ℝ) else 0)) := by
          rw [Finset.sum_comm]
    _ =
        ∑ rule : Rule,
          weight rule *
            (∑ cut : Cut,
              diff rule cut *
                (if inPrefix signal candidate cut then (1 : ℝ) else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro rule _
          rw [Finset.mul_sum]

/--
Finite-law bridge for Proposition 1: the expectation of the one-voter
prefix-score contribution is the prefix-score expression formed from induced
prefix probabilities.
-/
theorem pmfExp_prefixScoreFromEvent_eq_prefixExpectedScore
    {Cut Candidate Signal : Type*} [Fintype Cut]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (diff : Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (candidate : Candidate) :
    AppliedModelingLib.pmfExp law
        (prefixScoreFromEvent diff inPrefix candidate) =
      prefixExpectedScore diff
        (prefixProbFromEvent law inPrefix) candidate := by
  classical
  unfold AppliedModelingLib.pmfExp prefixScoreFromEvent prefixExpectedScore
    prefixProbFromEvent AppliedModelingLib.pmfProb
  calc
    ∑ signal : Signal,
        (law signal).toReal *
          (∑ cut : Cut,
            diff cut * if inPrefix signal candidate cut then (1 : ℝ) else 0)
        =
        ∑ signal : Signal, ∑ cut : Cut,
          diff cut *
            ((law signal).toReal *
              if inPrefix signal candidate cut then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro signal _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro cut _
          by_cases h : inPrefix signal candidate cut
          · simp [h]
            ring
          · simp [h]
    _ =
        ∑ cut : Cut, ∑ signal : Signal,
          diff cut *
            ((law signal).toReal *
              if inPrefix signal candidate cut then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]
    _ =
        ∑ cut : Cut,
          diff cut *
            (∑ signal : Signal,
              (law signal).toReal *
                if inPrefix signal candidate cut then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro cut _
          rw [Finset.mul_sum]

/--
The source paper's "reasonable" nonconstant nonincreasing scoring rules,
projected to their adjacent nonnegative prefix-weight vector.
-/
def ReasonablePrefixWeights {Cut : Type*} (diff : Cut → ℝ) : Prop :=
  (∀ k : Cut, 0 ≤ diff k) ∧ ∃ k : Cut, 0 < diff k

/-- The single-prefix indicator score vector is a reasonable prefix weight. -/
theorem ReasonablePrefixWeights.indicator
    {Cut : Type*} [DecidableEq Cut] (cut : Cut) :
    ReasonablePrefixWeights (fun k : Cut => if k = cut then (1 : ℝ) else 0) := by
  constructor
  · intro k
    by_cases h : k = cut <;> simp [h]
  · exact ⟨cut, by simp⟩

/--
Finite convex combinations of reasonable prefix-weight vectors are reasonable.
Nonnegativity is pointwise; nonconstancy follows because the nonnegative
weights sum to one, so some component has positive weight and that component
has a strictly positive prefix drop.
-/
theorem ReasonablePrefixWeights.weighted_sum
    {Rule Cut : Type*} [Fintype Rule]
    (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hdiff : ∀ rule, ReasonablePrefixWeights (diff rule)) :
    ReasonablePrefixWeights
      (fun cut => ∑ rule : Rule, weight rule * diff rule cut) := by
  constructor
  · intro cut
    exact Finset.sum_nonneg (by
      intro rule _
      exact mul_nonneg (hweight rule) ((hdiff rule).1 cut))
  · have hweight_exists : ∃ rule : Rule, 0 < weight rule := by
      by_contra hnone
      have hnonpos : ∀ rule : Rule, weight rule ≤ 0 := by
        intro rule
        exact le_of_not_gt (fun hpos => hnone ⟨rule, hpos⟩)
      have hsum_nonpos : (∑ rule : Rule, weight rule) ≤ 0 :=
        Finset.sum_nonpos (by intro rule _; exact hnonpos rule)
      linarith
    rcases hweight_exists with ⟨rule0, hrule0_pos⟩
    rcases (hdiff rule0).2 with ⟨cut0, hcut0_pos⟩
    refine ⟨cut0, ?_⟩
    refine Finset.sum_pos' ?_ ?_
    · intro rule _
      exact mul_nonneg (hweight rule) ((hdiff rule).1 cut0)
    · exact
        ⟨rule0, Finset.mem_univ rule0,
          mul_pos hrule0_pos hcut0_pos⟩

/--
Strict top-prefix dominance for one higher-tier/lower-tier candidate pair.
This is the finite probability condition in Proposition `thm:consistency`.
-/
def StrictTopPrefixDominance
    {Cut Candidate : Type*}
    (topPrefixProb : Candidate → Cut → ℝ)
    (hi lo : Candidate) : Prop :=
  ∀ k : Cut, topPrefixProb lo k < topPrefixProb hi k

/--
All reasonable positional prefix-score rules rank `hi` above `lo` in
asymptotic expected score.
-/
def AllReasonablePrefixScoresSeparate
    {Cut Candidate : Type*} [Fintype Cut]
    (topPrefixProb : Candidate → Cut → ℝ)
    (hi lo : Candidate) : Prop :=
  ∀ diff : Cut → ℝ,
    ReasonablePrefixWeights diff →
      prefixExpectedScore diff topPrefixProb lo <
        prefixExpectedScore diff topPrefixProb hi

/--
Strict top-prefix dominance over all cross-tier pairs relevant to a goal.
The predicate `crossTier hi lo` selects higher-tier/lower-tier comparisons.
-/
def StrictTopPrefixDominanceOn
    {Cut Candidate : Type*}
    (topPrefixProb : Candidate → Cut → ℝ)
    (crossTier : Candidate → Candidate → Prop) : Prop :=
  ∀ hi lo, crossTier hi lo →
    StrictTopPrefixDominance topPrefixProb hi lo

/--
Every reasonable positional prefix-score rule separates every relevant
cross-tier pair.
-/
def AllReasonablePrefixScoresSeparateOn
    {Cut Candidate : Type*} [Fintype Cut]
    (topPrefixProb : Candidate → Cut → ℝ)
    (crossTier : Candidate → Candidate → Prop) : Prop :=
  ∀ hi lo, crossTier hi lo →
    AllReasonablePrefixScoresSeparate topPrefixProb hi lo

/--
Proposition 1 finite algebra core: strict dominance of every top-prefix
probability is exactly what makes every nonconstant nonincreasing positional
rule separate the two candidates in expected score.
-/
theorem strictTopPrefixDominance_iff_allReasonablePrefixScoresSeparate
    {Cut Candidate : Type*} [Fintype Cut] [DecidableEq Cut]
    (topPrefixProb : Candidate → Cut → ℝ) (hi lo : Candidate) :
    StrictTopPrefixDominance topPrefixProb hi lo ↔
      AllReasonablePrefixScoresSeparate topPrefixProb hi lo := by
  constructor
  · intro hdom diff hdiff
    have hsum_pos :
        0 < ∑ k : Cut,
          diff k * (topPrefixProb hi k - topPrefixProb lo k) := by
      rcases hdiff.2 with ⟨k0, hk0⟩
      refine Finset.sum_pos' ?_ ?_
      · intro k _
        exact mul_nonneg (hdiff.1 k)
          (sub_nonneg.mpr (le_of_lt (hdom k)))
      · refine ⟨k0, Finset.mem_univ k0, ?_⟩
        exact mul_pos hk0 (sub_pos.mpr (hdom k0))
    have hdiff_score :
        prefixExpectedScore diff topPrefixProb hi -
            prefixExpectedScore diff topPrefixProb lo =
          ∑ k : Cut, diff k *
            (topPrefixProb hi k - topPrefixProb lo k) := by
      unfold prefixExpectedScore
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro k _
      ring
    have hpos :
        0 <
          prefixExpectedScore diff topPrefixProb hi -
            prefixExpectedScore diff topPrefixProb lo := by
      rw [hdiff_score]
      exact hsum_pos
    linarith
  · intro hall k
    let diff : Cut → ℝ := fun l => if l = k then 1 else 0
    have hdiff : ReasonablePrefixWeights diff := by
      constructor
      · intro l
        by_cases h : l = k <;> simp [diff, h]
      · exact ⟨k, by simp [diff]⟩
    have hsep := hall diff hdiff
    have hhi : prefixExpectedScore diff topPrefixProb hi =
        topPrefixProb hi k := by
      simp [prefixExpectedScore, diff]
    have hlo : prefixExpectedScore diff topPrefixProb lo =
        topPrefixProb lo k := by
      simp [prefixExpectedScore, diff]
    simpa [hhi, hlo] using hsep

/--
If induced top-prefix probabilities strictly separate `hi` from `lo`, every
reasonable prefix score has a strictly positive expected one-voter score gap.
This is the finite expectation statement consumed by the later stochastic
convergence step.
-/
theorem pmfExp_prefixScore_gap_pos_of_strictTopPrefixDominance
    {Cut Candidate Signal : Type*} [Fintype Cut] [DecidableEq Cut]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (diff : Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    {hi lo : Candidate}
    (hdom :
      StrictTopPrefixDominance (prefixProbFromEvent law inPrefix) hi lo)
    (hdiff : ReasonablePrefixWeights diff) :
    0 <
      AppliedModelingLib.pmfExp law
        (fun signal =>
          prefixScoreFromEvent diff inPrefix hi signal -
            prefixScoreFromEvent diff inPrefix lo signal) := by
  have hsep :=
    (strictTopPrefixDominance_iff_allReasonablePrefixScoresSeparate
      (prefixProbFromEvent law inPrefix) hi lo).1 hdom diff hdiff
  rw [AppliedModelingLib.pmfExp_sub,
    pmfExp_prefixScoreFromEvent_eq_prefixExpectedScore,
    pmfExp_prefixScoreFromEvent_eq_prefixExpectedScore]
  linarith

/--
Proposition 1 finite tierwise algebra core: the source condition over all
required higher-tier/lower-tier pairs is equivalent to separation of every such
pair by every reasonable positional scoring rule.
-/
theorem strictTopPrefixDominanceOn_iff_allReasonablePrefixScoresSeparateOn
    {Cut Candidate : Type*} [Fintype Cut] [DecidableEq Cut]
    (topPrefixProb : Candidate → Cut → ℝ)
    (crossTier : Candidate → Candidate → Prop) :
    StrictTopPrefixDominanceOn topPrefixProb crossTier ↔
      AllReasonablePrefixScoresSeparateOn topPrefixProb crossTier := by
  constructor
  · intro hdom hi lo hcross
    exact
      (strictTopPrefixDominance_iff_allReasonablePrefixScoresSeparate
        topPrefixProb hi lo).1 (hdom hi lo hcross)
  · intro hall hi lo hcross
    exact
      (strictTopPrefixDominance_iff_allReasonablePrefixScoresSeparate
        topPrefixProb hi lo).2 (hall hi lo hcross)

/--
Proposition 2 source formula: pairwise positional-score rate for candidates
`hi` and `lo`, after packaging a single voter's ranking as a finite signal.
-/
def pairwiseScoringRate {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ) : ℝ :=
  finiteScoreGapChernoffRate law hiScore loScore

/--
Extended Chernoff rate for a pairwise score-gap error.  This is the source
formula `- inf log MGF`, with `⊤` when the infimum is minus infinity.
-/
def pairwiseScoringExtendedRate
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ) : WithTop ℝ :=
  finiteRateFunctionTop law
    (fun signal => hiScore signal - loScore signal) 0

/-- Finite-sample pairwise mistake probability for iid score gaps. -/
def pairwiseScoringErrorProb {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ) (n : ℕ) : ℝ :=
  finiteIidScoreGapLeftTailProb law hiScore loScore n

/--
A positive probability of a `-1` one-voter score gap is enough to make the iid
pairwise error event eventually positive.  Indeed, the constant sample whose
every coordinate has gap `-1` is always in the left tail.
-/
theorem pairwiseScoringError_eventually_pos_of_negative_gap_prob
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {pDown : ℝ}
    (hDown : 0 < pDown)
    (hDownProb :
      AppliedModelingLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = -1) =
        pDown) :
    ∀ᶠ n : ℕ in Filter.atTop,
      0 < pairwiseScoringErrorProb law hiScore loScore n := by
  classical
  have hevent_pos :
      0 < AppliedModelingLib.pmfProb law
        (fun signal => hiScore signal - loScore signal = -1) := by
    rw [hDownProb]
    exact hDown
  simpa [pairwiseScoringErrorProb, finiteIidScoreGapLeftTailProb] using
    finiteIidScoreLeftTailProb_eventually_pos_of_event
      (μ := law)
      (score := fun signal => hiScore signal - loScore signal)
      (event := fun signal => hiScore signal - loScore signal = -1)
      (threshold := 0)
      hevent_pos
      (by
        intro n sample hall
        unfold finiteIidScoreSum
        calc
          ∑ i : Fin n, (hiScore (sample i) - loScore (sample i))
              = ∑ _i : Fin n, (-1 : ℝ) := by
                  exact Finset.sum_congr rfl (fun i _ => hall i)
          _ = -(n : ℝ) := by
                  simp [Finset.sum_const, nsmul_eq_mul]
          _ ≤ 0 := by
                  exact neg_nonpos.mpr (Nat.cast_nonneg n))

/--
One-sided finite-real boundary case for Proposition 2: if every positive-mass
one-voter score gap is nonnegative, then pairwise mistakes occur exactly when
every sampled voter has zero score gap.  With positive zero-gap probability
`pZero`, this gives exact exponential rate `-log pZero`.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_support_nonneg_zero_gap_prob
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hsupport :
      ∀ signal, 0 < (law signal).toReal →
        0 ≤ hiScore signal - loScore signal)
    {pZero : ℝ}
    (hZeroProb :
      AppliedModelingLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = 0) =
        pZero)
    (hZero_pos : 0 < pZero) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (-Real.log pZero) := by
  simpa [pairwiseScoringErrorProb, finiteIidScoreGapLeftTailProb] using
    finiteIidScoreLeftTail_exponentialRateCertificate_of_support_nonneg_zero_prob
      law (fun signal => hiScore signal - loScore signal)
      hsupport hZeroProb hZero_pos

/--
Pointwise Chernoff bound at the source rate for the one-sided zero-gap branch.
The error event is exactly the event that every sampled score gap is zero.
-/
theorem pairwiseScoringErrorProb_le_exp_neg_pairwiseScoringRate_of_support_nonneg_zero_gap_prob
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hsupport :
      ∀ signal, 0 < (law signal).toReal →
        0 ≤ hiScore signal - loScore signal)
    {pZero : ℝ}
    (hZeroProb :
      AppliedModelingLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = 0) =
        pZero)
    (hZero_pos : 0 < pZero)
    (n : ℕ) :
    pairwiseScoringErrorProb law hiScore loScore n ≤
      Real.exp (-(n : ℝ) * pairwiseScoringRate law hiScore loScore) := by
  have hrate :
      pairwiseScoringRate law hiScore loScore = -Real.log pZero := by
    simpa [pairwiseScoringRate, finiteScoreGapChernoffRate] using
      finiteChernoffRate_eq_neg_log_pmfProb_score_eq_zero_of_support_nonneg
        law (fun signal => hiScore signal - loScore signal)
        hsupport hZeroProb hZero_pos
  apply le_of_eq
  calc
    pairwiseScoringErrorProb law hiScore loScore n = pZero ^ n := by
      rw [pairwiseScoringErrorProb, finiteIidScoreGapLeftTailProb,
        finiteIidScoreLeftTailProb_eq_zero_score_prob_pow_of_support_nonneg
          law (fun signal => hiScore signal - loScore signal) hsupport n,
        hZeroProb]
    _ = (Real.exp (Real.log pZero)) ^ n := by
      rw [Real.exp_log hZero_pos]
    _ = Real.exp ((n : ℝ) * Real.log pZero) := by
      rw [Real.exp_nat_mul]
    _ = Real.exp (-(n : ℝ) * (-Real.log pZero)) := by
      congr 1
      ring
    _ = Real.exp (-(n : ℝ) * pairwiseScoringRate law hiScore loScore) := by
      rw [hrate]

/--
If every positive-mass score gap is strictly positive, the legacy real-valued
Chernoff wrapper takes its default value zero because its log-MGF infimum is
unbounded below.  The corresponding probability is zero for every positive
sample size.
-/
theorem pairwiseScoringRate_eq_zero_of_support_pos
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hsupport :
      ∀ signal, 0 < (law signal).toReal →
        0 < hiScore signal - loScore signal) :
    pairwiseScoringRate law hiScore loScore = 0 := by
  have hsupport_nonneg :
      ∀ signal, 0 < (law signal).toReal →
        0 ≤ hiScore signal - loScore signal := by
    intro signal hmass
    exact (hsupport signal hmass).le
  have hzero_prob :
      AppliedModelingLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = 0) = 0 := by
    refine AppliedModelingLib.pmfProb_eq_zero_of_no_mass law
      (fun signal => hiScore signal - loScore signal = 0) ?_
    intro signal hgap_zero
    by_cases hmass : 0 < (law signal).toReal
    · have hgap_pos := hsupport signal hmass
      exfalso
      exact (lt_irrefl (0 : ℝ)) (by simpa [hgap_zero] using hgap_pos)
    · exact le_antisymm (le_of_not_gt hmass) ENNReal.toReal_nonneg
  have hmgf :
      Filter.Tendsto
        (fun z : ℝ =>
          finiteMGF law (fun signal => hiScore signal - loScore signal) z)
        Filter.atBot (nhds 0) := by
    simpa [hzero_prob] using
      finiteMGF_tendsto_pmfProb_score_eq_zero_atBot_of_support_nonneg
        law (fun signal => hiScore signal - loScore signal) hsupport_nonneg
  have hnotbdd :
      ¬ BddBelow (Set.range fun z : ℝ =>
        finiteLogMGF law (fun signal => hiScore signal - loScore signal) z) := by
    rw [not_bddBelow_iff]
    intro bound
    rcases (hmgf.eventually_lt_const (Real.exp_pos bound)).exists with
      ⟨z, hz⟩
    refine ⟨finiteLogMGF law
      (fun signal => hiScore signal - loScore signal) z, ⟨z, rfl⟩, ?_⟩
    unfold finiteLogMGF
    calc
      Real.log
          (finiteMGF law (fun signal => hiScore signal - loScore signal) z) <
          Real.log (Real.exp bound) :=
        Real.log_lt_log
          (finiteMGF_pos law (fun signal => hiScore signal - loScore signal) z)
          hz
      _ = bound := Real.log_exp bound
  unfold pairwiseScoringRate finiteScoreGapChernoffRate finiteChernoffRate
  rw [Real.sInf_of_not_bddBelow hnotbdd]
  norm_num

/--
Pointwise bound in the strict one-sided branch.  The real-valued source-rate
wrapper is zero in this boundary case; the all-sample-size inequality follows
from the probability bound by one, including the empty sample.
-/
theorem pairwiseScoringErrorProb_le_exp_neg_pairwiseScoringRate_of_support_pos
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hsupport :
      ∀ signal, 0 < (law signal).toReal →
        0 < hiScore signal - loScore signal)
    (n : ℕ) :
    pairwiseScoringErrorProb law hiScore loScore n ≤
      Real.exp (-(n : ℝ) * pairwiseScoringRate law hiScore loScore) := by
  rw [pairwiseScoringRate_eq_zero_of_support_pos law hiScore loScore hsupport]
  have hprob : pairwiseScoringErrorProb law hiScore loScore n ≤ 1 := by
    exact AppliedModelingLib.pmfProb_le_one
      (AppliedModelingLib.pmfProduct (Fin n) Signal law)
      (fun sample : Fin n → Signal =>
        finiteIidScoreSum
          (fun signal => hiScore signal - loScore signal) sample ≤ 0)
  simpa [pairwiseScoringErrorProb, finiteIidScoreGapLeftTailProb] using hprob

/--
Strict one-voter support boundary for Proposition 2: if every positive-mass
score gap is strictly positive, the finite iid pairwise mistake event is
eventually empty.
-/
theorem pairwiseScoringError_eventually_zero_of_support_pos
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hsupport :
      ∀ signal, 0 < (law signal).toReal →
        0 < hiScore signal - loScore signal) :
    ∀ᶠ n in Filter.atTop,
      pairwiseScoringErrorProb law hiScore loScore n = 0 := by
  simpa [pairwiseScoringErrorProb, finiteIidScoreGapLeftTailProb] using
    finiteIidScoreLeftTailProb_eventually_zero_of_support_pos
      law (fun signal => hiScore signal - loScore signal) hsupport

/--
Strict one-voter support boundary for Proposition 2: if every positive-mass
score gap is strictly positive, the pairwise mistake probability admits an
eventual exponential upper bound at any finite target rate.
-/
theorem pairwiseScoringError_hasExpUpperBoundWithConst_of_support_pos
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hsupport :
      ∀ signal, 0 < (law signal).toReal →
        0 < hiScore signal - loScore signal)
    (targetRate : ℝ) :
    HasExpUpperBoundWithConst
      (pairwiseScoringErrorProb law hiScore loScore)
      targetRate := by
  simpa [pairwiseScoringErrorProb, finiteIidScoreGapLeftTailProb] using
    finiteIidScoreLeftTail_hasExpUpperBoundWithConst_of_support_pos
      law (fun signal => hiScore signal - loScore signal) hsupport targetRate

theorem pairwiseScoringRate_eq_source_formula
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ) :
    pairwiseScoringRate law hiScore loScore =
      -sInf (Set.range fun z : ℝ =>
        finiteLogMGF law (fun signal => hiScore signal - loScore signal) z) := by
  rfl

/--
Pairwise score-gap rate identity from a certified global finite log-MGF
minimum, stated in the geometric-base form used by explicit periodic/type
lower-bound witnesses.
-/
theorem pairwiseScoringRate_eq_neg_log_base_of_logMGF_global_min
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ) {base z0 : ℝ}
    (hmin :
      ∀ z : ℝ,
        Real.log base ≤
          finiteLogMGF law
            (fun signal => hiScore signal - loScore signal) z)
    (hwitness :
      finiteLogMGF law
          (fun signal => hiScore signal - loScore signal) z0 =
        Real.log base) :
    pairwiseScoringRate law hiScore loScore = -Real.log base := by
  simpa [pairwiseScoringRate, finiteScoreGapChernoffRate] using
    finiteScoreGapChernoffRate_eq_neg_log_base_of_logMGF_global_min
      law hiScore loScore hmin hwitness

/--
Pairwise score-gap rate identity from the source proof's usual convex
first-order certificate for the minimizing log-MGF dual parameter.
-/
theorem pairwiseScoringRate_eq_neg_log_base_of_convex_logMGF_deriv_zero
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ) {base z0 : ℝ}
    (hconv :
      ConvexOn ℝ Set.univ
        (fun z : ℝ =>
          finiteLogMGF law
            (fun signal => hiScore signal - loScore signal) z))
    (hderiv :
      HasDerivAt
        (fun z : ℝ =>
          finiteLogMGF law
            (fun signal => hiScore signal - loScore signal) z)
        0 z0)
    (hwitness :
      finiteLogMGF law
          (fun signal => hiScore signal - loScore signal) z0 =
        Real.log base) :
    pairwiseScoringRate law hiScore loScore = -Real.log base := by
  simpa [pairwiseScoringRate, finiteScoreGapChernoffRate] using
    finiteScoreGapChernoffRate_eq_neg_log_base_of_convex_hasDerivAt_zero
      law hiScore loScore hconv hderiv hwitness

/--
Pairwise score-gap rate identity from convexity plus the explicit stationary
equation for the score-gap finite log-MGF.
-/
theorem pairwiseScoringRate_eq_neg_log_base_of_convex_stationary
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ) {base z0 : ℝ}
    (hconv :
      ConvexOn ℝ Set.univ
        (fun z : ℝ =>
          finiteLogMGF law
            (fun signal => hiScore signal - loScore signal) z))
    (hstationary :
      (∑ signal : Signal,
        (law signal).toReal *
          ((hiScore signal - loScore signal) *
            Real.exp (z0 * (hiScore signal - loScore signal)))) = 0)
    (hwitness :
      finiteLogMGF law
          (fun signal => hiScore signal - loScore signal) z0 =
        Real.log base) :
    pairwiseScoringRate law hiScore loScore = -Real.log base := by
  simpa [pairwiseScoringRate, finiteScoreGapChernoffRate] using
    finiteScoreGapChernoffRate_eq_neg_log_base_of_convex_stationary
      law hiScore loScore hconv hstationary hwitness

/--
Pairwise score-gap rate identity from a zero derivative at the displayed
finite log-MGF dual parameter.  Finite log-MGF convexity is discharged by the
reusable finite-support MGF theorem.
-/
theorem pairwiseScoringRate_eq_neg_log_base_of_logMGF_deriv_zero
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ) {base z0 : ℝ}
    (hderiv :
      HasDerivAt
        (fun z : ℝ =>
          finiteLogMGF law
            (fun signal => hiScore signal - loScore signal) z)
        0 z0)
    (hwitness :
      finiteLogMGF law
          (fun signal => hiScore signal - loScore signal) z0 =
        Real.log base) :
    pairwiseScoringRate law hiScore loScore = -Real.log base :=
  pairwiseScoringRate_eq_neg_log_base_of_convex_logMGF_deriv_zero
    law hiScore loScore
    (finiteLogMGF_convex law
      (fun signal => hiScore signal - loScore signal))
    hderiv hwitness

/--
Pairwise score-gap rate identity from the explicit stationary equation for
the finite log-MGF.  Convexity is supplied by finite-support log-MGF convexity.
-/
theorem pairwiseScoringRate_eq_neg_log_base_of_stationary
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ) {base z0 : ℝ}
    (hstationary :
      (∑ signal : Signal,
        (law signal).toReal *
          ((hiScore signal - loScore signal) *
            Real.exp (z0 * (hiScore signal - loScore signal)))) = 0)
    (hwitness :
      finiteLogMGF law
          (fun signal => hiScore signal - loScore signal) z0 =
        Real.log base) :
    pairwiseScoringRate law hiScore loScore = -Real.log base :=
  pairwiseScoringRate_eq_neg_log_base_of_convex_stationary
    law hiScore loScore
    (finiteLogMGF_convex law
      (fun signal => hiScore signal - loScore signal))
    hstationary hwitness

/--
Proposition 2 Chernoff upper-bound half: every nonpositive dual parameter gives
an exponential upper bound for the iid pairwise score-gap mistake probability.
-/
theorem pairwiseScoringError_hasExpUpperBoundWithConst_of_dual
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ) {z : ℝ}
    (hz : z ≤ 0) :
    HasExpUpperBoundWithConst
      (pairwiseScoringErrorProb law hiScore loScore)
      (-(finiteLogMGF law (fun signal => hiScore signal - loScore signal) z)) := by
  simpa [pairwiseScoringErrorProb] using
    finiteIidScoreGapLeftTail_hasExpUpperBoundWithConst_of_dual
      law hiScore loScore hz

/--
Pairwise Chernoff upper-bound target-rate form: a nonpositive dual whose
negative log-MGF is at least the requested rate gives an exponential upper
bound at that requested rate.
-/
theorem pairwiseScoringError_hasExpUpperBoundWithConst_of_nonpos_dual_rate_le
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ) {z rate : ℝ}
    (hz : z ≤ 0)
    (hrate :
      rate ≤
        -(finiteLogMGF law
          (fun signal => hiScore signal - loScore signal) z)) :
    HasExpUpperBoundWithConst
      (pairwiseScoringErrorProb law hiScore loScore) rate := by
  simpa [pairwiseScoringErrorProb] using
    finiteIidScoreGapLeftTail_hasExpUpperBoundWithConst_of_nonpos_dual_rate_le
      law hiScore loScore hz hrate

/--
Pointwise Proposition 2 Chernoff upper bound: a nonpositive dual whose
negative log-MGF is at least `rate` bounds the pairwise mistake probability by
`exp (-n * rate)` at every finite sample size.
-/
theorem pairwiseScoringErrorProb_le_exp_of_nonpos_dual_rate_le
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ) {z rate : ℝ}
    (hz : z ≤ 0)
    (hrate :
      rate ≤
        -(finiteLogMGF law
          (fun signal => hiScore signal - loScore signal) z))
    (n : ℕ) :
    pairwiseScoringErrorProb law hiScore loScore n ≤
      Real.exp (-(n : ℝ) * rate) := by
  simpa [pairwiseScoringErrorProb, finiteIidScoreGapLeftTailProb] using
    finiteIidScoreLeftTailProb_le_exp_of_nonpos_dual_rate_le
      law (fun signal => hiScore signal - loScore signal) hz hrate n

/--
Pointwise Proposition 2 upper bound at the exact source rate, from a supplied
stationary nonpositive Chernoff dual.
-/
theorem pairwiseScoringErrorProb_le_exp_neg_pairwiseScoringRate_of_stationary
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ) {z : ℝ}
    (hz : z ≤ 0)
    (hstationary :
      (∑ signal : Signal,
        (law signal).toReal *
          ((hiScore signal - loScore signal) *
            Real.exp (z * (hiScore signal - loScore signal)))) = 0)
    (n : ℕ) :
    pairwiseScoringErrorProb law hiScore loScore n ≤
      Real.exp (-(n : ℝ) * pairwiseScoringRate law hiScore loScore) := by
  have hrate_eq :
      pairwiseScoringRate law hiScore loScore =
        -finiteLogMGF law
          (fun signal => hiScore signal - loScore signal) z := by
    simpa [finiteLogMGF] using
      pairwiseScoringRate_eq_neg_log_base_of_stationary
        (law := law) (hiScore := hiScore) (loScore := loScore)
        (base := finiteMGF law
          (fun signal => hiScore signal - loScore signal) z)
        (z0 := z) hstationary rfl
  exact
    pairwiseScoringErrorProb_le_exp_of_nonpos_dual_rate_le
      law hiScore loScore hz (by rw [hrate_eq]) n

/--
Pointwise Proposition 2 upper bound at the exact source rate for finite signal
laws with nonnegative expected score gap and positive-mass atoms on both sides.
-/
theorem pairwiseScoringErrorProb_le_exp_neg_pairwiseScoringRate_of_mean_nonneg_pos_neg_atoms
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (n : ℕ) :
    pairwiseScoringErrorProb law hiScore loScore n ≤
      Real.exp (-(n : ℝ) * pairwiseScoringRate law hiScore loScore) := by
  rcases
      exists_nonpos_weighted_exp_score_sum_eq_zero_of_pmfExp_nonneg_pos_neg_atoms
        law (fun signal => hiScore signal - loScore signal)
        hmean hmassPos hgapPos hmassNeg hgapNeg with
    ⟨z, hz_nonpos, hstationary⟩
  exact
    pairwiseScoringErrorProb_le_exp_neg_pairwiseScoringRate_of_stationary
      law hiScore loScore hz_nonpos hstationary n

/--
Full finite-support Proposition 2 Chernoff bound.  A finite score-gap law
with nonnegative expected gap has the displayed source bound for every sample
size, including its one-sided zero-gap and strictly-positive-support cases.
-/
theorem pairwiseScoringErrorProb_le_exp_neg_pairwiseScoringRate_of_mean_nonneg
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤ AppliedModelingLib.pmfExp law
        (fun signal => hiScore signal - loScore signal))
    (n : ℕ) :
    pairwiseScoringErrorProb law hiScore loScore n ≤
      Real.exp (-(n : ℝ) * pairwiseScoringRate law hiScore loScore) := by
  classical
  let gap : Signal → ℝ := fun signal => hiScore signal - loScore signal
  by_cases hneg : ∃ aNeg : Signal, 0 < (law aNeg).toReal ∧ gap aNeg < 0
  · rcases hneg with ⟨aNeg, hmassNeg, hgapNeg⟩
    have hbelow :
        ∃ a, 0 < (law a).toReal ∧
          gap a < AppliedModelingLib.pmfExp law gap := by
      exact ⟨aNeg, hmassNeg, lt_of_lt_of_le hgapNeg hmean⟩
    rcases
        AppliedModelingLib.exists_support_value_gt_pmfExp_of_exists_value_lt_pmfExp
          law gap hbelow with
      ⟨aPos, hmassPos, hmean_lt_gap⟩
    have hgapPos : 0 < gap aPos := lt_of_le_of_lt hmean hmean_lt_gap
    exact
      pairwiseScoringErrorProb_le_exp_neg_pairwiseScoringRate_of_mean_nonneg_pos_neg_atoms
        law hiScore loScore hmean
        (aPos := aPos) (aNeg := aNeg)
        hmassPos (by simpa [gap] using hgapPos)
        hmassNeg (by simpa [gap] using hgapNeg) n
  · have hsupport_nonneg :
        ∀ signal, 0 < (law signal).toReal → 0 ≤ gap signal := by
      intro signal hmass
      exact le_of_not_gt (fun hgap => hneg ⟨signal, hmass, hgap⟩)
    by_cases hzero :
        ∃ aZero : Signal, 0 < (law aZero).toReal ∧ gap aZero = 0
    · rcases hzero with ⟨aZero, hmassZero, hgapZero⟩
      let pZero : ℝ :=
        AppliedModelingLib.pmfProb law (fun signal => gap signal = 0)
      have hpZero_pos : 0 < pZero := by
        dsimp [pZero]
        exact
          (AppliedModelingLib.pmfProb_pos_iff_exists_pos_mass
            law (fun signal => gap signal = 0)).2
            ⟨aZero, hgapZero, hmassZero⟩
      exact
        pairwiseScoringErrorProb_le_exp_neg_pairwiseScoringRate_of_support_nonneg_zero_gap_prob
          law hiScore loScore
          (by
            intro signal hmass
            simpa [gap] using hsupport_nonneg signal hmass)
          (pZero := pZero) (by rfl) hpZero_pos n
    · have hsupport_pos :
          ∀ signal, 0 < (law signal).toReal → 0 < gap signal := by
        intro signal hmass
        have hnonneg := hsupport_nonneg signal hmass
        have hne : gap signal ≠ 0 := by
          intro hgap
          exact hzero ⟨signal, hmass, hgap⟩
        exact lt_of_le_of_ne hnonneg (Ne.symm hne)
      exact
        pairwiseScoringErrorProb_le_exp_neg_pairwiseScoringRate_of_support_pos
          law hiScore loScore
          (by
            intro signal hmass
            simpa [gap] using hsupport_pos signal hmass)
          n

/--
Positive expected one-voter score gap gives some strictly positive exponential
upper-bound rate for the iid pairwise mistake probability.  This is the
probabilistic half of the paper's consistency argument before an exact Cramer
rate is supplied.
-/
theorem pairwiseScoringError_exists_pos_expUpperBoundWithConst_of_expected_gap_pos
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 <
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal)) :
    ∃ rate : ℝ,
      0 < rate ∧
        HasExpUpperBoundWithConst
          (pairwiseScoringErrorProb law hiScore loScore) rate := by
  simpa [pairwiseScoringErrorProb, finiteIidScoreGapLeftTailProb] using
    finiteIidScoreGapLeftTail_exists_pos_expUpperBoundWithConst_of_pmfExp_gap_pos
      law hiScore loScore hmean

/--
Positive expected one-voter score gap gives an explicit nonpositive Chernoff
dual parameter whose dual rate is strictly positive and certifies an iid
pairwise mistake upper bound.
-/
theorem pairwiseScoringError_exists_nonpos_dual_positive_rate
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 <
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal)) :
    ∃ z : ℝ,
      z ≤ 0 ∧
        0 <
          -(finiteLogMGF law
            (fun signal => hiScore signal - loScore signal) z) ∧
        HasExpUpperBoundWithConst
          (pairwiseScoringErrorProb law hiScore loScore)
          (-(finiteLogMGF law
            (fun signal => hiScore signal - loScore signal) z)) := by
  rcases exists_nonpos_dual_neg_finiteLogMGF_pos_of_pmfExp_pos
      (μ := law)
      (score := fun signal => hiScore signal - loScore signal)
      hmean with
    ⟨z, hz, hrate_pos⟩
  exact
    ⟨z, hz, hrate_pos,
      pairwiseScoringError_hasExpUpperBoundWithConst_of_dual
        law hiScore loScore hz⟩

/--
Strict prefix dominance plus any reasonable prefix-score vector gives a
strictly positive exponential upper-bound rate for the induced iid pairwise
score error.  This is the first stochastic bridge from Proposition 1's finite
algebra to asymptotic separation.
-/
theorem prefixScoringPairwiseError_exists_pos_expUpperBoundWithConst
    {Cut Candidate Signal : Type*} [Fintype Cut] [DecidableEq Cut]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (diff : Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    {hi lo : Candidate}
    (hdom :
      StrictTopPrefixDominance (prefixProbFromEvent law inPrefix) hi lo)
    (hdiff : ReasonablePrefixWeights diff) :
    ∃ rate : ℝ,
      0 < rate ∧
        HasExpUpperBoundWithConst
          (pairwiseScoringErrorProb law
            (prefixScoreFromEvent diff inPrefix hi)
            (prefixScoreFromEvent diff inPrefix lo)) rate := by
  have hmean :=
    pmfExp_prefixScore_gap_pos_of_strictTopPrefixDominance
      law diff inPrefix hdom hdiff
  exact
    pairwiseScoringError_exists_pos_expUpperBoundWithConst_of_expected_gap_pos
      law
      (prefixScoreFromEvent diff inPrefix hi)
      (prefixScoreFromEvent diff inPrefix lo)
      hmean

/--
Strict prefix dominance also gives the paper-facing asymptotic conclusion:
the induced iid pairwise prefix-score error probability converges to zero.
-/
theorem prefixScoringPairwiseError_tendsto_zero
    {Cut Candidate Signal : Type*} [Fintype Cut] [DecidableEq Cut]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (diff : Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    {hi lo : Candidate}
    (hdom :
      StrictTopPrefixDominance (prefixProbFromEvent law inPrefix) hi lo)
    (hdiff : ReasonablePrefixWeights diff) :
    Filter.Tendsto
      (pairwiseScoringErrorProb law
        (prefixScoreFromEvent diff inPrefix hi)
        (prefixScoreFromEvent diff inPrefix lo))
      Filter.atTop (nhds 0) := by
  rcases
      prefixScoringPairwiseError_exists_pos_expUpperBoundWithConst
        law diff inPrefix hdom hdiff with
    ⟨rate, hrate_pos, hbound⟩
  exact hbound.tendsto_zero_of_pos_rate hrate_pos

/--
Tierwise version of the stochastic prefix bridge: every required higher/lower
pair gets a strictly positive exponential upper-bound rate.
-/
theorem prefixScoringPairwiseError_exists_pos_expUpperBoundWithConst_on
    {Cut Candidate Signal : Type*} [Fintype Cut] [DecidableEq Cut]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (diff : Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (crossTier : Candidate → Candidate → Prop)
    (hdom :
      StrictTopPrefixDominanceOn (prefixProbFromEvent law inPrefix) crossTier)
    (hdiff : ReasonablePrefixWeights diff) :
    ∀ hi lo, crossTier hi lo →
      ∃ rate : ℝ,
        0 < rate ∧
          HasExpUpperBoundWithConst
            (pairwiseScoringErrorProb law
              (prefixScoreFromEvent diff inPrefix hi)
              (prefixScoreFromEvent diff inPrefix lo)) rate := by
  intro hi lo hcross
  exact
    prefixScoringPairwiseError_exists_pos_expUpperBoundWithConst
      law diff inPrefix (hdom hi lo hcross) hdiff

/--
Tierwise convergence version of the stochastic prefix bridge: every required
higher/lower pair has iid prefix-score error probability tending to zero.
-/
theorem prefixScoringPairwiseError_tendsto_zero_on
    {Cut Candidate Signal : Type*} [Fintype Cut] [DecidableEq Cut]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (diff : Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (crossTier : Candidate → Candidate → Prop)
    (hdom :
      StrictTopPrefixDominanceOn (prefixProbFromEvent law inPrefix) crossTier)
    (hdiff : ReasonablePrefixWeights diff) :
    ∀ hi lo, crossTier hi lo →
      Filter.Tendsto
        (pairwiseScoringErrorProb law
          (prefixScoreFromEvent diff inPrefix hi)
          (prefixScoreFromEvent diff inPrefix lo))
        Filter.atTop (nhds 0) := by
  intro hi lo hcross
  exact
    prefixScoringPairwiseError_tendsto_zero
      law diff inPrefix (hdom hi lo hcross) hdiff

/--
Proposition 2 exact-rate endpoint from the reusable finite iid Cramer
certificate.  The analytic input is now only the standard upper/lower Cramer
bounds around the source log-MGF formula.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_cramer
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (C : FiniteIidScoreGapCramerCertificate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) := by
  simpa [pairwiseScoringErrorProb, pairwiseScoringRate] using
    finiteIidScoreGapLeftTail_exponentialRateCertificate_of_cramer
      law hiScore loScore C

/--
Exact-rate endpoint from an explicit finite left-tail path lower certificate.
This is the reusable route for concrete finite-score laws: prove the Chernoff
upper side and give a polynomially corrected geometric lower-bound sample path,
then the standard Cramer certificate follows.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_pathLower
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hupper :
      ∀ targetRate, targetRate < pairwiseScoringRate law hiScore loScore →
        HasExpUpperBoundWithConst
          (pairwiseScoringErrorProb law hiScore loScore) targetRate)
    (C : FiniteIidScoreGapPathLowerCertificate law hiScore loScore)
    (hrate : -Real.log C.base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) := by
  simpa [pairwiseScoringErrorProb, pairwiseScoringRate] using
    finiteIidScoreGapLeftTail_exponentialRateCertificate_of_pathLower
      law hiScore loScore
      (fun targetRate htarget => by
        simpa [pairwiseScoringErrorProb] using
          hupper targetRate (by
            simpa [pairwiseScoringRate] using htarget))
      C
      (by simpa [pairwiseScoringRate] using hrate)

/--
Exact-rate endpoint from a direct finite left-tail probability lower
certificate.  This is the natural interface for empirical-type and
multinomial-count lower bounds, which prove a tail probability lower bound
directly rather than singling out one sample path.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_tailLower
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hupper :
      ∀ targetRate, targetRate < pairwiseScoringRate law hiScore loScore →
        HasExpUpperBoundWithConst
          (pairwiseScoringErrorProb law hiScore loScore) targetRate)
    (C : FiniteIidScoreGapTailLowerCertificate law hiScore loScore)
    (hrate : -Real.log C.base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) := by
  simpa [pairwiseScoringErrorProb, pairwiseScoringRate] using
    finiteIidScoreGapLeftTail_exponentialRateCertificate_of_tailLower
      law hiScore loScore
      (fun targetRate htarget => by
        simpa [pairwiseScoringErrorProb] using
          hupper targetRate (by
            simpa [pairwiseScoringRate] using htarget))
      C
      (by simpa [pairwiseScoringRate] using hrate)

/--
Exact-rate endpoint from a bounded left-tail window under an exponential tilt.
This packages the reusable change-of-measure lower-bound bridge for the
finite-support Cramer route in Proposition 2.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_tiltedWindow
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hupper :
      ∀ targetRate, targetRate < pairwiseScoringRate law hiScore loScore →
        HasExpUpperBoundWithConst
          (pairwiseScoringErrorProb law hiScore loScore) targetRate)
    {z windowBound lowerConst : ℝ} {degree : ℕ}
    (hz : z ≤ 0)
    (hlowerConst_pos : 0 < lowerConst)
    (hwindow :
      ∀ᶠ n : ℕ in Filter.atTop,
        lowerConst / (((n.succ : ℕ) : ℝ) ^ degree) ≤
          AppliedModelingLib.pmfProb
            (AppliedModelingLib.pmfProduct (Fin n) Signal
              (finiteExponentialTilt law
                (fun signal => hiScore signal - loScore signal) z))
            (fun sample : Fin n → Signal =>
              -windowBound ≤
                  finiteIidScoreSum
                    (fun signal => hiScore signal - loScore signal) sample ∧
                finiteIidScoreSum
                    (fun signal => hiScore signal - loScore signal) sample ≤ 0))
    (hrate :
      -Real.log
          (finiteMGF law
            (fun signal => hiScore signal - loScore signal) z) =
        pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) := by
  simpa [pairwiseScoringErrorProb, pairwiseScoringRate] using
    finiteIidScoreGapLeftTail_exponentialRateCertificate_of_tilted_window
      law hiScore loScore
      (fun targetRate htarget => by
        simpa [pairwiseScoringErrorProb] using
          hupper targetRate (by
            simpa [pairwiseScoringRate] using htarget))
      hz hlowerConst_pos hwindow
      (by simpa [pairwiseScoringRate] using hrate)

/--
Exact-rate endpoint from a stationary exponential tilt and a bounded
tilted-window lower bound.  The finite log-MGF convexity theorem identifies
the stationary tilt with the Chernoff exponent.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_stationaryTiltedWindow
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    {z windowBound lowerConst : ℝ} {degree : ℕ}
    (hz : z ≤ 0)
    (hstationary :
      (∑ signal : Signal,
        (law signal).toReal *
          ((hiScore signal - loScore signal) *
            Real.exp (z * (hiScore signal - loScore signal)))) = 0)
    (hlowerConst_pos : 0 < lowerConst)
    (hwindow :
      ∀ᶠ n : ℕ in Filter.atTop,
        lowerConst / (((n.succ : ℕ) : ℝ) ^ degree) ≤
          AppliedModelingLib.pmfProb
            (AppliedModelingLib.pmfProduct (Fin n) Signal
              (finiteExponentialTilt law
                (fun signal => hiScore signal - loScore signal) z))
            (fun sample : Fin n → Signal =>
              -windowBound ≤
                  finiteIidScoreSum
                    (fun signal => hiScore signal - loScore signal) sample ∧
                finiteIidScoreSum
                    (fun signal => hiScore signal - loScore signal) sample ≤ 0)) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_cramer
    law hiScore loScore
    (finiteIidScoreGapCramerCertificate_of_stationary_tilted_window_of_mean_nonneg_pos_neg_atoms
      law hiScore loScore hmean
      hmassPos hgapPos hmassNeg hgapNeg
      hz hstationary hlowerConst_pos hwindow)

/--
Exact-rate endpoint from an explicit finite left-tail path lower certificate
with the generic Chernoff upper side discharged from nonnegative expected score
gap and bounded-below log-MGF range.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_pathLower_of_mean_nonneg
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    (hbdd :
      BddBelow (Set.range fun z : ℝ =>
        finiteLogMGF law (fun signal => hiScore signal - loScore signal) z))
    (C : FiniteIidScoreGapPathLowerCertificate law hiScore loScore)
    (hrate : -Real.log C.base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  by
    simpa [pairwiseScoringErrorProb, pairwiseScoringRate] using
      finiteIidScoreGapLeftTail_exponentialRateCertificate_of_pathLower_of_mean_nonneg
        law hiScore loScore hmean hbdd C
        (by simpa [pairwiseScoringRate] using hrate)

/--
Exact-rate endpoint from an explicit finite left-tail path lower certificate,
with the generic Chernoff upper side discharged by nonnegative expected score
gap and two positive-mass atoms on opposite sides of the score gap.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_pathLower_of_mean_nonneg_pos_neg_atoms
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (C : FiniteIidScoreGapPathLowerCertificate law hiScore loScore)
    (hrate : -Real.log C.base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  by
    simpa [pairwiseScoringErrorProb, pairwiseScoringRate] using
      finiteIidScoreGapLeftTail_exponentialRateCertificate_of_pathLower_of_mean_nonneg_pos_neg_atoms
        law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg C
        (by simpa [pairwiseScoringRate] using hrate)

/--
Exact-rate endpoint from a direct finite left-tail probability lower
certificate, with the generic Chernoff upper side discharged from nonnegative
expected score gap and bounded-below finite log-MGF range.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_tailLower_of_mean_nonneg
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    (hbdd :
      BddBelow (Set.range fun z : ℝ =>
        finiteLogMGF law (fun signal => hiScore signal - loScore signal) z))
    (C : FiniteIidScoreGapTailLowerCertificate law hiScore loScore)
    (hrate : -Real.log C.base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  by
    simpa [pairwiseScoringErrorProb, pairwiseScoringRate] using
      finiteIidScoreGapLeftTail_exponentialRateCertificate_of_tailLower_of_mean_nonneg
        law hiScore loScore hmean hbdd C
        (by simpa [pairwiseScoringRate] using hrate)

/--
Exact-rate endpoint from a direct finite left-tail probability lower
certificate, with the generic Chernoff upper side discharged by nonnegative
expected score gap and two positive-mass atoms on opposite sides of the score
gap.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_tailLower_of_mean_nonneg_pos_neg_atoms
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (C : FiniteIidScoreGapTailLowerCertificate law hiScore loScore)
    (hrate : -Real.log C.base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  by
    simpa [pairwiseScoringErrorProb, pairwiseScoringRate] using
      finiteIidScoreGapLeftTail_exponentialRateCertificate_of_tailLower_of_mean_nonneg_pos_neg_atoms
        law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg C
        (by simpa [pairwiseScoringRate] using hrate)

/--
Exact-rate endpoint from an exact empirical-type lower certificate and an
externally supplied Chernoff upper side.  This certificate includes the
multinomial type-count entropy factor.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_empiricalTypeLower
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hupper :
      ∀ targetRate, targetRate < pairwiseScoringRate law hiScore loScore →
        HasExpUpperBoundWithConst
          (pairwiseScoringErrorProb law hiScore loScore) targetRate)
    (C : FiniteIidScoreGapEmpiricalTypeLowerCertificate law hiScore loScore)
    (hrate : -Real.log C.base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_tailLower
    law hiScore loScore hupper C.toTailLowerCertificate hrate

/--
Exact-rate endpoint from an exact empirical-type lower certificate, with the
generic Chernoff upper side discharged by nonnegative expected score gap and
bounded-below finite log-MGF range.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_empiricalTypeLower_of_mean_nonneg
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    (hbdd :
      BddBelow (Set.range fun z : ℝ =>
        finiteLogMGF law (fun signal => hiScore signal - loScore signal) z))
    (C : FiniteIidScoreGapEmpiricalTypeLowerCertificate law hiScore loScore)
    (hrate : -Real.log C.base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_tailLower_of_mean_nonneg
    law hiScore loScore hmean hbdd C.toTailLowerCertificate hrate

/--
Exact-rate endpoint from an exact empirical-type lower certificate, with the
generic Chernoff upper side discharged by nonnegative expected score gap and
two positive-mass atoms on opposite sides of the score gap.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_empiricalTypeLower_of_mean_nonneg_pos_neg_atoms
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (C : FiniteIidScoreGapEmpiricalTypeLowerCertificate law hiScore loScore)
    (hrate : -Real.log C.base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_empiricalTypeLower_of_mean_nonneg
    law hiScore loScore hmean
    (finiteScoreGapLogMGF_bddBelow_of_pos_neg_atoms
      law hiScore loScore hmassPos hgapPos hmassNeg hgapNeg)
    C hrate

/--
Exact-rate endpoint from an explicit finite bucket/type lower certificate and
an externally supplied Chernoff upper side.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_bucketLower
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hupper :
      ∀ targetRate, targetRate < pairwiseScoringRate law hiScore loScore →
        HasExpUpperBoundWithConst
          (pairwiseScoringErrorProb law hiScore loScore) targetRate)
    (C : FiniteIidScoreGapBucketLowerCertificate law hiScore loScore)
    (hrate : -Real.log C.base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_pathLower
    law hiScore loScore hupper C.toPathLowerCertificate hrate

/--
Exact-rate endpoint from an explicit finite bucket/type lower certificate, with
the generic Chernoff upper side discharged by nonnegative expected score gap
and bounded-below finite log-MGF range.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_bucketLower_of_mean_nonneg
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    (hbdd :
      BddBelow (Set.range fun z : ℝ =>
        finiteLogMGF law (fun signal => hiScore signal - loScore signal) z))
    (C : FiniteIidScoreGapBucketLowerCertificate law hiScore loScore)
    (hrate : -Real.log C.base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_pathLower_of_mean_nonneg
    law hiScore loScore hmean hbdd C.toPathLowerCertificate hrate

/--
Exact-rate endpoint from an explicit finite bucket/type lower certificate,
with the generic Chernoff upper side discharged by nonnegative expected score
gap and two positive-mass atoms on opposite sides of the score gap.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_bucketLower_of_mean_nonneg_pos_neg_atoms
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (C : FiniteIidScoreGapBucketLowerCertificate law hiScore loScore)
    (hrate : -Real.log C.base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_pathLower_of_mean_nonneg_pos_neg_atoms
    law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg
    C.toPathLowerCertificate hrate

/--
Exact-rate endpoint from an explicit finite empirical count-vector lower
certificate and an externally supplied Chernoff upper side.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_countVectorLower
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hupper :
      ∀ targetRate, targetRate < pairwiseScoringRate law hiScore loScore →
        HasExpUpperBoundWithConst
          (pairwiseScoringErrorProb law hiScore loScore) targetRate)
    (C : FiniteIidScoreGapCountVectorLowerCertificate law hiScore loScore)
    (hrate : -Real.log C.base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_pathLower
    law hiScore loScore hupper C.toPathLowerCertificate hrate

/--
Exact-rate endpoint from an explicit finite empirical count-vector lower
certificate, with the generic Chernoff upper side discharged by nonnegative
expected score gap and bounded-below finite log-MGF range.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_countVectorLower_of_mean_nonneg
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    (hbdd :
      BddBelow (Set.range fun z : ℝ =>
        finiteLogMGF law (fun signal => hiScore signal - loScore signal) z))
    (C : FiniteIidScoreGapCountVectorLowerCertificate law hiScore loScore)
    (hrate : -Real.log C.base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_pathLower_of_mean_nonneg
    law hiScore loScore hmean hbdd C.toPathLowerCertificate hrate

/--
Exact-rate endpoint from an empirical count-vector lower certificate, with the
generic Chernoff upper side discharged by nonnegative expected score gap and
two positive-mass atoms on opposite sides of the score gap.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_countVectorLower_of_mean_nonneg_pos_neg_atoms
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (C : FiniteIidScoreGapCountVectorLowerCertificate law hiScore loScore)
    (hrate : -Real.log C.base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_countVectorLower_of_mean_nonneg
    law hiScore loScore hmean
    (finiteScoreGapLogMGF_bddBelow_of_pos_neg_atoms
      law hiScore loScore hmassPos hgapPos hmassNeg hgapNeg)
    C hrate

/--
Periodic empirical-count lower certificate for one pairwise score gap.
This is a convenient concrete route for finite large-deviation witnesses:
repeat a tail-safe period count vector and fill residues with a tail-safe atom.
-/
def pairwiseScoringError_periodicCountVectorLowerCertificate
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {Q : ℕ} (hQpos : 0 < Q) (q : Signal → ℕ) (filler : Signal)
    (hqsum : ∑ signal : Signal, q signal = Q)
    (hqtail :
      ∑ signal : Signal,
        (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0)
    (hfiller_tail : hiScore filler - loScore filler ≤ 0)
    {base : ℝ}
    (hbase_pos : 0 < base)
    (hbase_period :
      base ^ Q ≤
        ∏ signal : Signal,
          (law signal).toReal ^ q signal)
    (hfiller_pos : 0 < (law filler).toReal) :
    FiniteIidScoreGapCountVectorLowerCertificate law hiScore loScore :=
  FiniteIidScoreCountVectorLowerCertificate.of_periodic
    law (fun signal => hiScore signal - loScore signal)
    hQpos q filler hqsum hqtail hfiller_tail
    hbase_pos hbase_period hfiller_pos

/--
Entropy-aware periodic empirical-type lower certificate for one pairwise score
gap.  The one-period geometric block may include the full multinomial type
mass, which is the method-of-types lower-bound surface used by finite-support
Cramer proofs.
-/
def pairwiseScoringError_periodicEmpiricalTypeLowerCertificate
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {Q : ℕ} (hQpos : 0 < Q) (q : Signal → ℕ) (filler : Signal)
    (hqsum : ∑ signal : Signal, q signal = Q)
    (hqtail :
      ∑ signal : Signal,
        (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0)
    (hfiller_tail : hiScore filler - loScore filler ≤ 0)
    {base : ℝ}
    (hbase_pos : 0 < base)
    (hbase_period :
      base ^ Q ≤
        (Nat.multinomial (Finset.univ : Finset Signal) q : ℝ) *
          ∏ signal : Signal,
            (law signal).toReal ^ q signal)
    (hfiller_pos : 0 < (law filler).toReal) :
    FiniteIidScoreGapEmpiricalTypeLowerCertificate law hiScore loScore :=
  FiniteIidScoreEmpiricalTypeLowerCertificate.of_periodic
    (μ := law) (score := fun signal => hiScore signal - loScore signal)
    hQpos q filler hqsum hqtail hfiller_tail
    hbase_pos hbase_period hfiller_pos

/--
Rate-parameterized entropy-aware periodic empirical-type lower certificate.
The geometric base is `exp (-baseRate)`, so the one-period check is stated as
`exp (-Q * baseRate) <=` the full type mass.
-/
def pairwiseScoringError_periodicEmpiricalTypeLowerCertificate_of_rate
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {Q : ℕ} (hQpos : 0 < Q) (q : Signal → ℕ) (filler : Signal)
    (hqsum : ∑ signal : Signal, q signal = Q)
    (hqtail :
      ∑ signal : Signal,
        (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0)
    (hfiller_tail : hiScore filler - loScore filler ≤ 0)
    {baseRate : ℝ}
    (hbase_period :
      Real.exp (-(Q : ℝ) * baseRate) ≤
        (Nat.multinomial (Finset.univ : Finset Signal) q : ℝ) *
          ∏ signal : Signal,
            (law signal).toReal ^ q signal)
    (hfiller_pos : 0 < (law filler).toReal) :
    FiniteIidScoreGapEmpiricalTypeLowerCertificate law hiScore loScore :=
  FiniteIidScoreEmpiricalTypeLowerCertificate.of_periodic_rate
    (μ := law) (score := fun signal => hiScore signal - loScore signal)
    hQpos q filler hqsum hqtail hfiller_tail
    hbase_period hfiller_pos

/--
Exact pairwise rate from periodic empirical-count data, nonnegative expected
score gap, and two-sided support.  The only remaining rate-side input is the
identification of the periodic geometric base with the paper's Chernoff rate.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_periodicCountVectorLower_of_mean_nonneg_pos_neg_atoms
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    {Q : ℕ} (hQpos : 0 < Q) (q : Signal → ℕ) (filler : Signal)
    (hqsum : ∑ signal : Signal, q signal = Q)
    (hqtail :
      ∑ signal : Signal,
        (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0)
    (hfiller_tail : hiScore filler - loScore filler ≤ 0)
    {base : ℝ}
    (hbase_pos : 0 < base)
    (hbase_period :
      base ^ Q ≤
        ∏ signal : Signal,
          (law signal).toReal ^ q signal)
    (hfiller_pos : 0 < (law filler).toReal)
    (hrate : -Real.log base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_cramer
    law hiScore loScore
    (finiteIidScoreGapCramerCertificate_of_periodic_countVectorLower_of_pos_neg_atoms
      law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg
      hQpos q filler hqsum hqtail hfiller_tail
      hbase_pos hbase_period hfiller_pos
      (by simpa [pairwiseScoringRate] using hrate))

/--
Exact pairwise rate from entropy-aware periodic empirical-type data,
nonnegative expected score gap, and two-sided support.  Compared with the
count-vector version, the geometric base can use the full one-period
multinomial type mass.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_periodicEmpiricalTypeLower_of_mean_nonneg_pos_neg_atoms
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    {Q : ℕ} (hQpos : 0 < Q) (q : Signal → ℕ) (filler : Signal)
    (hqsum : ∑ signal : Signal, q signal = Q)
    (hqtail :
      ∑ signal : Signal,
        (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0)
    (hfiller_tail : hiScore filler - loScore filler ≤ 0)
    {base : ℝ}
    (hbase_pos : 0 < base)
    (hbase_period :
      base ^ Q ≤
        (Nat.multinomial (Finset.univ : Finset Signal) q : ℝ) *
          ∏ signal : Signal,
            (law signal).toReal ^ q signal)
    (hfiller_pos : 0 < (law filler).toReal)
    (hrate : -Real.log base = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) := by
  let C :
      FiniteIidScoreGapEmpiricalTypeLowerCertificate law hiScore loScore :=
    pairwiseScoringError_periodicEmpiricalTypeLowerCertificate
      law hiScore loScore hQpos q filler hqsum hqtail hfiller_tail
      hbase_pos hbase_period hfiller_pos
  exact
    pairwiseScoringError_exponentialRateCertificate_of_empiricalTypeLower_of_mean_nonneg_pos_neg_atoms
      law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg C hrate

/--
Exact pairwise rate from a rate-parameterized entropy-aware periodic
empirical-type witness.  This avoids a separate real-root witness for the
geometric base.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_periodicEmpiricalTypeLower_rate_of_mean_nonneg_pos_neg_atoms
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    {Q : ℕ} (hQpos : 0 < Q) (q : Signal → ℕ) (filler : Signal)
    (hqsum : ∑ signal : Signal, q signal = Q)
    (hqtail :
      ∑ signal : Signal,
        (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0)
    (hfiller_tail : hiScore filler - loScore filler ≤ 0)
    {baseRate : ℝ}
    (hbase_period :
      Real.exp (-(Q : ℝ) * baseRate) ≤
        (Nat.multinomial (Finset.univ : Finset Signal) q : ℝ) *
          ∏ signal : Signal,
            (law signal).toReal ^ q signal)
    (hfiller_pos : 0 < (law filler).toReal)
    (hrate : baseRate = pairwiseScoringRate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) := by
  let C :
      FiniteIidScoreGapEmpiricalTypeLowerCertificate law hiScore loScore :=
    pairwiseScoringError_periodicEmpiricalTypeLowerCertificate_of_rate
      law hiScore loScore hQpos q filler hqsum hqtail hfiller_tail
      hbase_period hfiller_pos
  have hC_rate : -Real.log C.base = pairwiseScoringRate law hiScore loScore := by
    change -Real.log (Real.exp (-baseRate)) =
      pairwiseScoringRate law hiScore loScore
    rw [Real.log_exp]
    linarith
  exact
    pairwiseScoringError_exponentialRateCertificate_of_empiricalTypeLower_of_mean_nonneg_pos_neg_atoms
      law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg C hC_rate

/--
Exact pairwise rate from periodic empirical-count data plus a certified global
log-MGF minimizer for the resulting geometric base.  This replaces the raw
rate-identity assumption with a reusable minimization proof obligation.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_periodicCountVectorLower_of_logMGF_global_min
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    {Q : ℕ} (hQpos : 0 < Q) (q : Signal → ℕ) (filler : Signal)
    (hqsum : ∑ signal : Signal, q signal = Q)
    (hqtail :
      ∑ signal : Signal,
        (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0)
    (hfiller_tail : hiScore filler - loScore filler ≤ 0)
    {base z0 : ℝ}
    (hbase_pos : 0 < base)
    (hbase_period :
      base ^ Q ≤
        ∏ signal : Signal,
          (law signal).toReal ^ q signal)
    (hfiller_pos : 0 < (law filler).toReal)
    (hmin :
      ∀ z : ℝ,
        Real.log base ≤
          finiteLogMGF law
            (fun signal => hiScore signal - loScore signal) z)
    (hwitness :
      finiteLogMGF law
          (fun signal => hiScore signal - loScore signal) z0 =
        Real.log base) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_cramer
    law hiScore loScore
    (finiteIidScoreGapCramerCertificate_of_periodic_countVectorLower_of_logMGF_global_min
      law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg
      hQpos q filler hqsum hqtail hfiller_tail
      hbase_pos hbase_period hfiller_pos hmin hwitness)

/--
Exact pairwise rate from periodic empirical-count data plus a convex
first-order certificate for the finite log-MGF minimizer.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_periodicCountVectorLower_of_convex_logMGF_deriv_zero
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    {Q : ℕ} (hQpos : 0 < Q) (q : Signal → ℕ) (filler : Signal)
    (hqsum : ∑ signal : Signal, q signal = Q)
    (hqtail :
      ∑ signal : Signal,
        (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0)
    (hfiller_tail : hiScore filler - loScore filler ≤ 0)
    {base z0 : ℝ}
    (hbase_pos : 0 < base)
    (hbase_period :
      base ^ Q ≤
        ∏ signal : Signal,
          (law signal).toReal ^ q signal)
    (hfiller_pos : 0 < (law filler).toReal)
    (hconv :
      ConvexOn ℝ Set.univ
        (fun z : ℝ =>
          finiteLogMGF law
            (fun signal => hiScore signal - loScore signal) z))
    (hderiv :
      HasDerivAt
        (fun z : ℝ =>
          finiteLogMGF law
            (fun signal => hiScore signal - loScore signal) z)
        0 z0)
    (hwitness :
      finiteLogMGF law
          (fun signal => hiScore signal - loScore signal) z0 =
        Real.log base) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) := by
  have hmin :
      ∀ z : ℝ,
        Real.log base ≤
          finiteLogMGF law
            (fun signal => hiScore signal - loScore signal) z := by
    intro z
    have hmin_at_z0 :=
      finiteLogMGF_global_min_of_convex_hasDerivAt_zero
        law (fun signal => hiScore signal - loScore signal) hconv hderiv z
    simpa [hwitness] using hmin_at_z0
  exact
    pairwiseScoringError_exponentialRateCertificate_of_periodicCountVectorLower_of_logMGF_global_min
      law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg
      hQpos q filler hqsum hqtail hfiller_tail
      hbase_pos hbase_period hfiller_pos hmin hwitness

/--
Exact pairwise rate from periodic empirical-count data plus convexity and the
explicit stationary equation for the finite log-MGF minimizer.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_periodicCountVectorLower_of_convex_stationary
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    {Q : ℕ} (hQpos : 0 < Q) (q : Signal → ℕ) (filler : Signal)
    (hqsum : ∑ signal : Signal, q signal = Q)
    (hqtail :
      ∑ signal : Signal,
        (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0)
    (hfiller_tail : hiScore filler - loScore filler ≤ 0)
    {base z0 : ℝ}
    (hbase_pos : 0 < base)
    (hbase_period :
      base ^ Q ≤
        ∏ signal : Signal,
          (law signal).toReal ^ q signal)
    (hfiller_pos : 0 < (law filler).toReal)
    (hconv :
      ConvexOn ℝ Set.univ
        (fun z : ℝ =>
          finiteLogMGF law
            (fun signal => hiScore signal - loScore signal) z))
    (hstationary :
      (∑ signal : Signal,
        (law signal).toReal *
          ((hiScore signal - loScore signal) *
            Real.exp (z0 * (hiScore signal - loScore signal)))) = 0)
    (hwitness :
      finiteLogMGF law
          (fun signal => hiScore signal - loScore signal) z0 =
        Real.log base) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) := by
  exact
    pairwiseScoringError_exponentialRateCertificate_of_periodicCountVectorLower_of_convex_logMGF_deriv_zero
      law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg
      hQpos q filler hqsum hqtail hfiller_tail
      hbase_pos hbase_period hfiller_pos hconv
      (finiteLogMGF_hasDerivAt_zero_of_weighted_exp_score_sum_eq_zero
        law (fun signal => hiScore signal - loScore signal) hstationary)
      hwitness

/--
Exact pairwise rate from periodic empirical-count data plus a zero derivative
at the finite log-MGF minimizer.  Finite log-MGF convexity is supplied
internally by the reusable finite-support theorem.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_periodicCountVectorLower_of_logMGF_deriv_zero
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    {Q : ℕ} (hQpos : 0 < Q) (q : Signal → ℕ) (filler : Signal)
    (hqsum : ∑ signal : Signal, q signal = Q)
    (hqtail :
      ∑ signal : Signal,
        (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0)
    (hfiller_tail : hiScore filler - loScore filler ≤ 0)
    {base z0 : ℝ}
    (hbase_pos : 0 < base)
    (hbase_period :
      base ^ Q ≤
        ∏ signal : Signal,
          (law signal).toReal ^ q signal)
    (hfiller_pos : 0 < (law filler).toReal)
    (hderiv :
      HasDerivAt
        (fun z : ℝ =>
          finiteLogMGF law
            (fun signal => hiScore signal - loScore signal) z)
        0 z0)
    (hwitness :
      finiteLogMGF law
          (fun signal => hiScore signal - loScore signal) z0 =
        Real.log base) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_cramer
    law hiScore loScore
    (finiteIidScoreGapCramerCertificate_of_periodic_countVectorLower_of_logMGF_deriv_zero
      law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg
      hQpos q filler hqsum hqtail hfiller_tail
      hbase_pos hbase_period hfiller_pos hderiv hwitness)

/--
Exact pairwise rate from periodic empirical-count data plus the explicit
stationary equation for the finite log-MGF minimizer.  Convexity is supplied
internally by finite-support log-MGF convexity.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_periodicCountVectorLower_of_stationary
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    {Q : ℕ} (hQpos : 0 < Q) (q : Signal → ℕ) (filler : Signal)
    (hqsum : ∑ signal : Signal, q signal = Q)
    (hqtail :
      ∑ signal : Signal,
        (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0)
    (hfiller_tail : hiScore filler - loScore filler ≤ 0)
    {base z0 : ℝ}
    (hbase_pos : 0 < base)
    (hbase_period :
      base ^ Q ≤
        ∏ signal : Signal,
          (law signal).toReal ^ q signal)
    (hfiller_pos : 0 < (law filler).toReal)
    (hstationary :
      (∑ signal : Signal,
        (law signal).toReal *
          ((hiScore signal - loScore signal) *
            Real.exp (z0 * (hiScore signal - loScore signal)))) = 0)
    (hwitness :
      finiteLogMGF law
          (fun signal => hiScore signal - loScore signal) z0 =
        Real.log base) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_cramer
    law hiScore loScore
    (finiteIidScoreGapCramerCertificate_of_periodic_countVectorLower_of_stationary
      law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg
      hQpos q filler hqsum hqtail hfiller_tail
      hbase_pos hbase_period hfiller_pos hstationary hwitness)

/--
Exact pairwise rate from periodic empirical-count witnesses available at every
strictly slower target rate.  This is the method-of-types-facing form of
Proposition 2: the Chernoff upper side is discharged generically, and the lower
side is supplied by explicit periodic count vectors.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_periodicCountVectorLower_witnesses_of_mean_nonneg_pos_neg_atoms
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (hlower :
      ∀ targetRate,
        pairwiseScoringRate law hiScore loScore < targetRate →
        ∃ (Q : ℕ) (q : Signal → ℕ) (filler : Signal) (base : ℝ),
          0 < Q ∧
          (∑ signal : Signal, q signal = Q) ∧
          (∑ signal : Signal,
            (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0) ∧
          hiScore filler - loScore filler ≤ 0 ∧
          0 < base ∧
          base ^ Q ≤
            ∏ signal : Signal, (law signal).toReal ^ q signal ∧
          0 < (law filler).toReal ∧
          -Real.log base < targetRate) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) := by
  have hCramer :
      FiniteIidScoreGapCramerCertificate law hiScore loScore :=
    finiteIidScoreGapCramerCertificate_of_periodic_countVectorLower_witnesses_of_pos_neg_atoms
      law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg
      (fun targetRate htarget => by
        exact hlower targetRate (by
          simpa [pairwiseScoringRate, finiteScoreGapChernoffRate] using
            htarget))
  exact pairwiseScoringError_exponentialRateCertificate_of_cramer
    law hiScore loScore hCramer

/--
Exact pairwise rate from entropy-aware periodic empirical-type witnesses
available at every strictly slower target rate.  This is the periodic
method-of-types form of Proposition 2 with the full one-period type mass.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_periodicEmpiricalTypeLower_witnesses_of_mean_nonneg_pos_neg_atoms
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (hlower :
      ∀ targetRate,
        pairwiseScoringRate law hiScore loScore < targetRate →
        ∃ (Q : ℕ) (q : Signal → ℕ) (filler : Signal) (base : ℝ),
          0 < Q ∧
          (∑ signal : Signal, q signal = Q) ∧
          (∑ signal : Signal,
            (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0) ∧
          hiScore filler - loScore filler ≤ 0 ∧
          0 < base ∧
          base ^ Q ≤
            (Nat.multinomial (Finset.univ : Finset Signal) q : ℝ) *
              ∏ signal : Signal, (law signal).toReal ^ q signal ∧
          0 < (law filler).toReal ∧
          -Real.log base < targetRate) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) := by
  have hCramer :
      FiniteIidScoreGapCramerCertificate law hiScore loScore :=
    finiteIidScoreGapCramerCertificate_of_empiricalTypeLower_witnesses_of_pos_neg_atoms
      law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg
      (fun targetRate htarget => by
        rcases hlower targetRate (by
          simpa [pairwiseScoringRate, finiteScoreGapChernoffRate] using
            htarget) with
          ⟨Q, q, filler, base, hQpos, hqsum, hqtail, hfiller_tail,
            hbase_pos, hbase_period, hfiller_pos, hrate⟩
        refine
          ⟨pairwiseScoringError_periodicEmpiricalTypeLowerCertificate
            law hiScore loScore hQpos q filler hqsum hqtail hfiller_tail
            hbase_pos hbase_period hfiller_pos, hrate⟩)
  exact pairwiseScoringError_exponentialRateCertificate_of_cramer
    law hiScore loScore hCramer

/--
Exact pairwise rate from rate-parameterized periodic empirical-type witnesses
available at every strictly slower target rate.  The witness for target
`targetRate` supplies a block rate `baseRate < targetRate` and proves the full
one-period type mass is at least `exp (-Q * baseRate)`.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_periodicEmpiricalTypeLower_rate_witnesses_of_mean_nonneg_pos_neg_atoms
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (hlower :
      ∀ targetRate,
        pairwiseScoringRate law hiScore loScore < targetRate →
        ∃ (Q : ℕ) (q : Signal → ℕ) (filler : Signal) (baseRate : ℝ),
          0 < Q ∧
          (∑ signal : Signal, q signal = Q) ∧
          (∑ signal : Signal,
            (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0) ∧
          hiScore filler - loScore filler ≤ 0 ∧
          Real.exp (-(Q : ℝ) * baseRate) ≤
            (Nat.multinomial (Finset.univ : Finset Signal) q : ℝ) *
              ∏ signal : Signal, (law signal).toReal ^ q signal ∧
          0 < (law filler).toReal ∧
          baseRate < targetRate) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) := by
  have hCramer :
      FiniteIidScoreGapCramerCertificate law hiScore loScore :=
    finiteIidScoreGapCramerCertificate_of_empiricalTypeLower_witnesses_of_pos_neg_atoms
      law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg
      (fun targetRate htarget => by
        rcases hlower targetRate (by
          simpa [pairwiseScoringRate, finiteScoreGapChernoffRate] using
            htarget) with
          ⟨Q, q, filler, baseRate, hQpos, hqsum, hqtail, hfiller_tail,
            hbase_period, hfiller_pos, hrate⟩
        let C :
            FiniteIidScoreGapEmpiricalTypeLowerCertificate law hiScore loScore :=
          pairwiseScoringError_periodicEmpiricalTypeLowerCertificate_of_rate
            law hiScore loScore hQpos q filler hqsum hqtail hfiller_tail
            hbase_period hfiller_pos
        refine ⟨C, ?_⟩
        change -Real.log (Real.exp (-baseRate)) < targetRate
        rw [Real.log_exp]
        linarith)
  exact pairwiseScoringError_exponentialRateCertificate_of_cramer
    law hiScore loScore hCramer

/--
Exact pairwise rate from logarithmic periodic empirical-type witnesses
available at every strictly slower target rate.  This is the same certificate
boundary as
`pairwiseScoringError_exponentialRateCertificate_of_periodicEmpiricalTypeLower_rate_witnesses_of_mean_nonneg_pos_neg_atoms`,
but in the log form used by finite-alphabet method-of-types estimates.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_periodicEmpiricalTypeLower_log_witnesses_of_mean_nonneg_pos_neg_atoms
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (hlower :
      ∀ targetRate,
        pairwiseScoringRate law hiScore loScore < targetRate →
        ∃ (Q : ℕ) (q : Signal → ℕ) (filler : Signal) (baseRate : ℝ),
          0 < Q ∧
          (∑ signal : Signal, q signal = Q) ∧
          (∑ signal : Signal,
            (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0) ∧
          hiScore filler - loScore filler ≤ 0 ∧
          (∀ signal : Signal, q signal ≠ 0 → 0 < (law signal).toReal) ∧
          -(Q : ℝ) * baseRate ≤
            Real.log (Nat.multinomial (Finset.univ : Finset Signal) q : ℝ) +
              ∑ signal : Signal,
                (q signal : ℝ) * Real.log (law signal).toReal ∧
          0 < (law filler).toReal ∧
          baseRate < targetRate) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_periodicEmpiricalTypeLower_rate_witnesses_of_mean_nonneg_pos_neg_atoms
    law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg
    (fun targetRate htarget => by
      rcases hlower targetRate htarget with
        ⟨Q, q, filler, baseRate, hQpos, hqsum, hqtail, hfiller_tail,
          hμpos, hlog, hfiller_pos, hrate⟩
      refine
        ⟨Q, q, filler, baseRate, hQpos, hqsum, hqtail, hfiller_tail,
          ?_, hfiller_pos, hrate⟩
      exact empiricalTypeBlockMass_ge_exp_of_log_sum_bound law q hμpos hlog)

/--
Exact pairwise rate from method-of-types witnesses with the empirical-mode
polynomial loss separated from the product comparison.  This is the direct
bridge from the reusable modal bound
`multinomial_empirical_mode_mass_ge_inv_countVectors` to Proposition 2.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_periodicEmpiricalTypeLower_modal_product_witnesses_of_mean_nonneg_pos_neg_atoms
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (hlower :
      ∀ targetRate,
        pairwiseScoringRate law hiScore loScore < targetRate →
        ∃ (Q : ℕ) (q : Signal → ℕ) (filler : Signal)
          (baseRate eps : ℝ),
          0 < Q ∧
          (∑ signal : Signal, q signal = Q) ∧
          (∑ signal : Signal,
            (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0) ∧
          hiScore filler - loScore filler ≤ 0 ∧
          Real.exp (-(Q : ℝ) * eps) *
              ∏ signal : Signal, (((q signal : ℝ) / Q) ^ q signal) ≤
            ∏ signal : Signal, (law signal).toReal ^ q signal ∧
          Real.exp (-(Q : ℝ) * baseRate) ≤
            Real.exp (-(Q : ℝ) * eps) /
              (((Q.succ : ℕ) : ℝ) ^ Fintype.card Signal) ∧
          0 < (law filler).toReal ∧
          baseRate < targetRate) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_periodicEmpiricalTypeLower_rate_witnesses_of_mean_nonneg_pos_neg_atoms
    law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg
    (fun targetRate htarget => by
      rcases hlower targetRate htarget with
        ⟨Q, q, filler, baseRate, eps, hQpos, hqsum, hqtail, hfiller_tail,
          hcompare, hrate_poly, hfiller_pos, hrate⟩
      refine
        ⟨Q, q, filler, baseRate, hQpos, hqsum, hqtail, hfiller_tail,
          ?_, hfiller_pos, hrate⟩
      exact
        empiricalTypeBlockMass_ge_exp_of_product_compare
          (fun signal : Signal => (law signal).toReal)
          hQpos q hqsum hcompare hrate_poly)

/--
Exact pairwise rate from method-of-types witnesses stated in log-ratio form.
For each rounded type, the log ratio between the empirical law `q / Q` and the
source law controls the exponential part; the modal theorem supplies the
inverse-polynomial type-count loss.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_periodicEmpiricalTypeLower_modal_log_witnesses_of_mean_nonneg_pos_neg_atoms
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (hlower :
      ∀ targetRate,
        pairwiseScoringRate law hiScore loScore < targetRate →
        ∃ (Q : ℕ) (q : Signal → ℕ) (filler : Signal)
          (baseRate eps : ℝ),
          0 < Q ∧
          (∑ signal : Signal, q signal = Q) ∧
          (∑ signal : Signal,
            (q signal : ℝ) * (hiScore signal - loScore signal) ≤ 0) ∧
          hiScore filler - loScore filler ≤ 0 ∧
          (∀ signal : Signal, q signal ≠ 0 → 0 < (law signal).toReal) ∧
          (∑ signal : Signal,
              (q signal : ℝ) *
                (Real.log ((q signal : ℝ) / Q) -
                  Real.log (law signal).toReal) ≤
            (Q : ℝ) * eps) ∧
          Real.exp (-(Q : ℝ) * baseRate) ≤
            Real.exp (-(Q : ℝ) * eps) /
              (((Q.succ : ℕ) : ℝ) ^ Fintype.card Signal) ∧
          0 < (law filler).toReal ∧
          baseRate < targetRate) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_periodicEmpiricalTypeLower_modal_product_witnesses_of_mean_nonneg_pos_neg_atoms
    law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg
    (fun targetRate htarget => by
      rcases hlower targetRate htarget with
        ⟨Q, q, filler, baseRate, eps, hQpos, hqsum, hqtail, hfiller_tail,
          hmass_support, hlog, hrate_poly, hfiller_pos, hrate⟩
      refine
        ⟨Q, q, filler, baseRate, eps, hQpos, hqsum, hqtail, hfiller_tail,
          ?_, hrate_poly, hfiller_pos, hrate⟩
      exact
        empiricalFreqProduct_pow_ge_exp_neg_of_log_ratio_bound
          (fun signal : Signal => (law signal).toReal)
          hQpos q hmass_support hlog)

/--
Exact pairwise rate from a stationary finite exponential tilt plus
rate-sensitive rounded empirical types.

The remaining choice principle `hchoose` is intentionally narrow: it only says
that after the continuity radius and desired exponential rate are known, one
can choose a denominator large enough for simplex rounding and for absorbing
the empirical-mode polynomial loss.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_stationary_tilted_modal_log_witness_choices
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    {z : ℝ}
    (hstationary :
      (∑ signal : Signal,
        (law signal).toReal *
          ((hiScore signal - loScore signal) *
            Real.exp (z * (hiScore signal - loScore signal)))) = 0)
    (hchoose :
      ∀ targetRate,
        pairwiseScoringRate law hiScore loScore < targetRate →
        ∀ closeRadius,
          0 < closeRadius →
          ∀ epsRate,
            pairwiseScoringRate law hiScore loScore < epsRate →
            epsRate < targetRate →
            ∃ (Q : ℕ) (δ η baseRate : ℝ),
              0 < Q ∧
              0 ≤ δ ∧
              δ ≤ 1 ∧
              0 < η ∧
              (Fintype.card Signal : ℝ) / (Q : ℝ) < η ∧
              η * (∑ signal : Signal,
                  |hiScore signal - loScore signal|) ≤
                δ * (-(hiScore aNeg - loScore aNeg)) ∧
              η + δ < closeRadius ∧
              Real.exp (-(Q : ℝ) * baseRate) ≤
                Real.exp (-(Q : ℝ) * epsRate) /
                  (((Q.succ : ℕ) : ℝ) ^ Fintype.card Signal) ∧
              baseRate < targetRate) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) := by
  letI : Nonempty Signal := ⟨aNeg⟩
  let gap : Signal → ℝ := fun signal => hiScore signal - loScore signal
  have hrate_eq :
      pairwiseScoringRate law hiScore loScore =
        -Real.log (finiteMGF law gap z) := by
    simpa [gap, finiteLogMGF] using
      pairwiseScoringRate_eq_neg_log_base_of_stationary
        law hiScore loScore (base := finiteMGF law gap z) (z0 := z)
        hstationary rfl
  exact
    pairwiseScoringError_exponentialRateCertificate_of_periodicEmpiricalTypeLower_modal_log_witnesses_of_mean_nonneg_pos_neg_atoms
      law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg
      (fun targetRate htarget => by
        let epsRate : ℝ :=
          (pairwiseScoringRate law hiScore loScore + targetRate) / 2
        have hepsRate_gt :
            pairwiseScoringRate law hiScore loScore < epsRate := by
          dsimp [epsRate]
          linarith
        have hepsRate_lt : epsRate < targetRate := by
          dsimp [epsRate]
          linarith
        have hslack_pos :
            0 < epsRate - pairwiseScoringRate law hiScore loScore := by
          linarith
        have htilt_nonneg :
            ∀ signal : Signal,
              0 ≤
                (finiteExponentialTilt law gap z signal).toReal := by
          intro signal
          exact ENNReal.toReal_nonneg
        have hlaw_nonneg :
            ∀ signal : Signal, 0 ≤ (law signal).toReal := by
          intro signal
          exact ENNReal.toReal_nonneg
        have htilt_support :
            ∀ signal : Signal,
              0 < (finiteExponentialTilt law gap z signal).toReal ↔
                0 < (law signal).toReal := by
          intro signal
          exact finiteExponentialTilt_apply_toReal_pos_iff law gap z signal
        obtain ⟨closeRadius, hcloseRadius_pos, hclose_log⟩ :=
          exists_forall_close_log_ratio_sum_le_of_same_support
            (fun signal : Signal =>
              (finiteExponentialTilt law gap z signal).toReal)
            (fun signal : Signal => (law signal).toReal)
            htilt_nonneg hlaw_nonneg htilt_support hslack_pos
        obtain
          ⟨Q, δ, η, baseRate, hQpos, hδ_nonneg, hδ_le_one, hη_pos,
            hQ_large, hmargin, hclose_total, hrate_poly, hbaseRate_lt⟩ :=
          hchoose targetRate htarget closeRadius hcloseRadius_pos
            epsRate hepsRate_gt hepsRate_lt
        obtain ⟨q, hqsum, hqclose, hqtail, hq_support⟩ :=
          exists_countVector_tail_close_to_stationary_tilted_gap_law_via_neg_atom_of_large_denominator_with_support
            law hiScore loScore hstationary hmassNeg hgapNeg hQpos
            hδ_nonneg hδ_le_one hη_pos hQ_large hmargin hclose_total
        refine
          ⟨Q, q, aNeg, baseRate, epsRate, hQpos, hqsum, hqtail,
            le_of_lt hgapNeg, ?_, ?_, hrate_poly, hmassNeg,
            hbaseRate_lt⟩
        · exact hq_support
        · have hfreq_log_le :
              (∑ signal : Signal,
                  ((q signal : ℝ) / Q) *
                    (Real.log ((q signal : ℝ) / Q) -
                      Real.log (law signal).toReal)) ≤ epsRate := by
            have hfreq_nonneg :
                ∀ signal : Signal, 0 ≤ ((q signal : ℝ) / Q) := by
              intro signal
              exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
            have hfreq_support :
                ∀ signal : Signal,
                  ((q signal : ℝ) / Q) ≠ 0 →
                    0 < (law signal).toReal := by
              intro signal hfreq_ne
              exact hq_support signal (by
                intro hq_zero
                exact hfreq_ne (by simp [hq_zero]))
            have hcont :=
              hclose_log
                (fun signal : Signal => (q signal : ℝ) / Q)
                hfreq_nonneg
                hfreq_support
                (by
                  intro signal
                  simpa [gap] using hqclose signal)
            have htilt_log :
                (∑ signal : Signal,
                    (finiteExponentialTilt law gap z signal).toReal *
                      (Real.log
                          (finiteExponentialTilt law gap z signal).toReal -
                        Real.log (law signal).toReal)) =
                  pairwiseScoringRate law hiScore loScore := by
              rw [
                finiteExponentialTilt_log_ratio_sum_eq_neg_log_mgf_of_stationary
                  law gap hstationary,
                ← hrate_eq]
            have hcont' :
                (∑ signal : Signal,
                    ((q signal : ℝ) / Q) *
                      (Real.log ((q signal : ℝ) / Q) -
                        Real.log (law signal).toReal)) ≤
                  pairwiseScoringRate law hiScore loScore +
                    (epsRate - pairwiseScoringRate law hiScore loScore) := by
              calc
                (∑ signal : Signal,
                    ((q signal : ℝ) / Q) *
                      (Real.log ((q signal : ℝ) / Q) -
                        Real.log (law signal).toReal))
                    ≤
                      (∑ signal : Signal,
                        (finiteExponentialTilt law gap z signal).toReal *
                          (Real.log
                              (finiteExponentialTilt law gap z signal).toReal -
                            Real.log (law signal).toReal)) +
                        (epsRate -
                          pairwiseScoringRate law hiScore loScore) := hcont
                _ =
                      pairwiseScoringRate law hiScore loScore +
                        (epsRate -
                          pairwiseScoringRate law hiScore loScore) := by
                    rw [htilt_log]
            linarith
          have hQ_nonneg : 0 ≤ (Q : ℝ) := by
            exact_mod_cast (Nat.zero_le Q)
          have hscale :=
            mul_le_mul_of_nonneg_left hfreq_log_le hQ_nonneg
          rw [← count_log_ratio_sum_eq_denominator_mul_freq_log_ratio_sum
            (fun signal : Signal => (law signal).toReal) hQpos q]
            at hscale
          simpa using hscale)

/--
Exact pairwise rate from a finite law and a stationary exponential tilt.

The method-of-types lower-bound route preserves support during rounding, so no
full-support assumption is needed.  The only required positive atoms are the
positive-gap and negative-gap witnesses.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_stationary_tilted_modal_log_support
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    {z : ℝ}
    (hstationary :
      (∑ signal : Signal,
        (law signal).toReal *
          ((hiScore signal - loScore signal) *
            Real.exp (z * (hiScore signal - loScore signal)))) = 0) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) := by
  exact
    pairwiseScoringError_exponentialRateCertificate_of_stationary_tilted_modal_log_witness_choices
      law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg
      hstationary
      (fun targetRate htarget closeRadius hcloseRadius_pos
          epsRate hepsRate_gt hepsRate_lt => by
        let scoreScale : ℝ :=
          ∑ signal : Signal, |hiScore signal - loScore signal|
        let negGap : ℝ := -(hiScore aNeg - loScore aNeg)
        let δ : ℝ := min (closeRadius / 4) (1 / 2)
        have hquarter_pos : 0 < closeRadius / 4 := by linarith
        have hδ_pos : 0 < δ := by
          dsimp [δ]
          exact lt_min hquarter_pos (by norm_num)
        have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
        have hδ_le_one : δ ≤ 1 := by
          have hδ_le_half : δ ≤ 1 / 2 := by
            dsimp [δ]
            exact min_le_right _ _
          linarith
        have hscoreScale_nonneg : 0 ≤ scoreScale := by
          dsimp [scoreScale]
          exact Finset.sum_nonneg (fun signal _ => abs_nonneg _)
        have hscoreScale_add_pos : 0 < scoreScale + 1 := by
          linarith
        have hnegGap_pos : 0 < negGap := by
          dsimp [negGap]
          linarith
        let η : ℝ := min (closeRadius / 4) (δ * negGap / (scoreScale + 1))
        have hη_pos : 0 < η := by
          dsimp [η]
          exact lt_min hquarter_pos
            (div_pos (mul_pos hδ_pos hnegGap_pos) hscoreScale_add_pos)
        have hη_le_close_quarter : η ≤ closeRadius / 4 := by
          dsimp [η]
          exact min_le_left _ _
        have hη_le_margin : η ≤ δ * negGap / (scoreScale + 1) := by
          dsimp [η]
          exact min_le_right _ _
        have hmargin :
            η * (∑ signal : Signal,
                |hiScore signal - loScore signal|) ≤
              δ * (-(hiScore aNeg - loScore aNeg)) := by
          have hη_mul_le :
              η * scoreScale ≤
                (δ * negGap / (scoreScale + 1)) * scoreScale :=
            mul_le_mul_of_nonneg_right hη_le_margin hscoreScale_nonneg
          have hright_le : (δ * negGap / (scoreScale + 1)) *
                scoreScale ≤ δ * negGap := by
            have hδneg_nonneg : 0 ≤ δ * negGap :=
              mul_nonneg hδ_nonneg hnegGap_pos.le
            rw [div_mul_eq_mul_div]
            rw [div_le_iff₀ hscoreScale_add_pos]
            nlinarith
          dsimp [scoreScale, negGap] at hη_mul_le hright_le ⊢
          exact hη_mul_le.trans hright_le
        have hclose_total : η + δ < closeRadius := by
          have hδ_le_close_quarter : δ ≤ closeRadius / 4 := by
            dsimp [δ]
            exact min_le_left _ _
          nlinarith
        let baseRate : ℝ := (epsRate + targetRate) / 2
        have hbaseRate_lt : baseRate < targetRate := by
          dsimp [baseRate]
          linarith
        have hbaseRate_gt_eps : epsRate < baseRate := by
          dsimp [baseRate]
          linarith
        have hrate_slack_pos : 0 < baseRate - epsRate := by
          linarith
        obtain ⟨Q, hQpos, hQ_large, hpoly_lt⟩ :=
          exists_denominator_card_div_lt_and_polynomial_loss_lt
            (α := Signal) hη_pos hrate_slack_pos
        have hpoly_loss_lt :
            (Fintype.card Signal : ℝ) *
                Real.log (((Q.succ : ℕ) : ℝ)) / (Q : ℝ) <
              baseRate - epsRate := by
          simpa [mul_div_assoc] using hpoly_lt
        have hrate_poly_le :
            epsRate +
                (Fintype.card Signal : ℝ) *
                  Real.log (((Q.succ : ℕ) : ℝ)) / (Q : ℝ) ≤
              baseRate := by
          linarith
        refine
          ⟨Q, δ, η, baseRate, hQpos, hδ_nonneg, hδ_le_one,
            hη_pos, hQ_large, hmargin, hclose_total, ?_,
            hbaseRate_lt⟩
        exact
          exp_neg_mul_rate_le_exp_neg_mul_div_countBound
            (α := Signal) hQpos hrate_poly_le)

/--
Exact pairwise rate from a finite law with nonnegative expected score gap and
positive-mass atoms on both sides of the score gap.  The stationary
exponential tilt is found internally by the finite MGF root-existence lemma.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) := by
  rcases
      exists_nonpos_weighted_exp_score_sum_eq_zero_of_pmfExp_nonneg_pos_neg_atoms
        law (fun signal => hiScore signal - loScore signal)
        hmean hmassPos hgapPos hmassNeg hgapNeg with
    ⟨z, _hz_nonpos, hstationary⟩
  exact
    pairwiseScoringError_exponentialRateCertificate_of_stationary_tilted_modal_log_support
      law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg
      (z := z) hstationary

/--
Finite-support Proposition 2 trichotomy.  Under nonnegative expected score
gap, every finite pairwise score-gap law falls into one of the finite-real
exact-rate cases already proved:

* a two-sided support case with the source Chernoff rate;
* a one-sided zero-gap boundary with exact rate `-log pZero`; or
* a strict one-sided boundary where the finite iid mistake event is eventually
  empty.
-/
theorem pairwiseScoringError_exponentialRateCertificate_or_boundary_of_mean_nonneg
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal)) :
    ExponentialRateCertificate
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
        pairwiseScoringErrorProb law hiScore loScore n = 0) := by
  classical
  let gap : Signal → ℝ := fun signal => hiScore signal - loScore signal
  by_cases hneg : ∃ aNeg : Signal, 0 < (law aNeg).toReal ∧ gap aNeg < 0
  · rcases hneg with ⟨aNeg, hmassNeg, hgapNeg⟩
    have hbelow :
        ∃ a, 0 < (law a).toReal ∧
          gap a < AppliedModelingLib.pmfExp law gap := by
      exact ⟨aNeg, hmassNeg, lt_of_lt_of_le hgapNeg hmean⟩
    rcases
        AppliedModelingLib.exists_support_value_gt_pmfExp_of_exists_value_lt_pmfExp
          law gap hbelow with
      ⟨aPos, hmassPos, hmean_lt_gap⟩
    have hgapPos : 0 < gap aPos := lt_of_le_of_lt hmean hmean_lt_gap
    left
    exact
      pairwiseScoringError_exponentialRateCertificate_of_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms
        law hiScore loScore hmean
        (aPos := aPos) (aNeg := aNeg)
        hmassPos (by simpa [gap] using hgapPos)
        hmassNeg (by simpa [gap] using hgapNeg)
  · have hsupport_nonneg :
        ∀ signal, 0 < (law signal).toReal → 0 ≤ gap signal := by
      intro signal hmass
      exact le_of_not_gt (fun hgap => hneg ⟨signal, hmass, hgap⟩)
    by_cases hzero :
        ∃ aZero : Signal, 0 < (law aZero).toReal ∧ gap aZero = 0
    · rcases hzero with ⟨aZero, hmassZero, hgapZero⟩
      let pZero : ℝ :=
        AppliedModelingLib.pmfProb law (fun signal => gap signal = 0)
      have hpZero_pos : 0 < pZero := by
        dsimp [pZero]
        exact
          (AppliedModelingLib.pmfProb_pos_iff_exists_pos_mass
            law (fun signal => gap signal = 0)).2
            ⟨aZero, hgapZero, hmassZero⟩
      right
      left
      refine ⟨pZero, rfl, hpZero_pos, ?_⟩
      exact
        pairwiseScoringError_exponentialRateCertificate_of_support_nonneg_zero_gap_prob
          law hiScore loScore
          (by
            intro signal hmass
            simpa [gap] using hsupport_nonneg signal hmass)
          (pZero := pZero)
          (by rfl)
          hpZero_pos
    · have hsupport_pos :
          ∀ signal, 0 < (law signal).toReal → 0 < gap signal := by
        intro signal hmass
        have hnonneg := hsupport_nonneg signal hmass
        have hne : gap signal ≠ 0 := by
          intro hgap
          exact hzero ⟨signal, hmass, hgap⟩
        exact lt_of_le_of_ne hnonneg (Ne.symm hne)
      right
      right
      exact
        pairwiseScoringError_eventually_zero_of_support_pos
          law hiScore loScore
          (by
            intro signal hmass
            simpa [gap] using hsupport_pos signal hmass)

/--
Witness-preserving finite-support Proposition 2 trichotomy.  This is the same
mathematical split as
`pairwiseScoringError_exponentialRateCertificate_or_boundary_of_mean_nonneg`,
but the two-sided branch keeps the positive and negative support atoms needed
by randomized-comparison wrappers.
-/
theorem pairwiseScoringError_source_or_zero_certificate_or_eventually_zero_of_mean_nonneg
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal)) :
    (∃ aPos aNeg : Signal,
      0 < (law aPos).toReal ∧
        0 < hiScore aPos - loScore aPos ∧
        0 < (law aNeg).toReal ∧
        hiScore aNeg - loScore aNeg < 0 ∧
        ExponentialRateCertificate
          (pairwiseScoringErrorProb law hiScore loScore)
          (pairwiseScoringRate law hiScore loScore)) ∨
      (∃ pZero : ℝ,
        AppliedModelingLib.pmfProb law
            (fun signal => hiScore signal - loScore signal = 0) =
          pZero ∧
        0 < pZero ∧
        ExponentialRateCertificate
          (pairwiseScoringErrorProb law hiScore loScore)
          (-Real.log pZero)) ∨
      (∀ᶠ n in Filter.atTop,
        pairwiseScoringErrorProb law hiScore loScore n = 0) := by
  classical
  let gap : Signal → ℝ := fun signal => hiScore signal - loScore signal
  by_cases hneg : ∃ aNeg : Signal, 0 < (law aNeg).toReal ∧ gap aNeg < 0
  · rcases hneg with ⟨aNeg, hmassNeg, hgapNeg⟩
    have hbelow :
        ∃ a, 0 < (law a).toReal ∧
          gap a < AppliedModelingLib.pmfExp law gap := by
      exact ⟨aNeg, hmassNeg, lt_of_lt_of_le hgapNeg hmean⟩
    rcases
        AppliedModelingLib.exists_support_value_gt_pmfExp_of_exists_value_lt_pmfExp
          law gap hbelow with
      ⟨aPos, hmassPos, hmean_lt_gap⟩
    have hgapPos : 0 < gap aPos := lt_of_le_of_lt hmean hmean_lt_gap
    left
    refine ⟨aPos, aNeg, hmassPos, ?_, hmassNeg, ?_, ?_⟩
    · simpa [gap] using hgapPos
    · simpa [gap] using hgapNeg
    · exact
        pairwiseScoringError_exponentialRateCertificate_of_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms
          law hiScore loScore hmean
          (aPos := aPos) (aNeg := aNeg)
          hmassPos (by simpa [gap] using hgapPos)
          hmassNeg (by simpa [gap] using hgapNeg)
  · have hsupport_nonneg :
        ∀ signal, 0 < (law signal).toReal → 0 ≤ gap signal := by
      intro signal hmass
      exact le_of_not_gt (fun hgap => hneg ⟨signal, hmass, hgap⟩)
    by_cases hzero :
        ∃ aZero : Signal, 0 < (law aZero).toReal ∧ gap aZero = 0
    · rcases hzero with ⟨aZero, hmassZero, hgapZero⟩
      let pZero : ℝ :=
        AppliedModelingLib.pmfProb law (fun signal => gap signal = 0)
      have hpZero_pos : 0 < pZero := by
        dsimp [pZero]
        exact
          (AppliedModelingLib.pmfProb_pos_iff_exists_pos_mass
            law (fun signal => gap signal = 0)).2
            ⟨aZero, hgapZero, hmassZero⟩
      right
      left
      refine ⟨pZero, rfl, hpZero_pos, ?_⟩
      exact
        pairwiseScoringError_exponentialRateCertificate_of_support_nonneg_zero_gap_prob
          law hiScore loScore
          (by
            intro signal hmass
            simpa [gap] using hsupport_nonneg signal hmass)
          (pZero := pZero)
          (by rfl)
          hpZero_pos
    · have hsupport_pos :
          ∀ signal, 0 < (law signal).toReal → 0 < gap signal := by
        intro signal hmass
        have hnonneg := hsupport_nonneg signal hmass
        have hne : gap signal ≠ 0 := by
          intro hgap
          exact hzero ⟨signal, hmass, hgap⟩
        exact lt_of_le_of_ne hnonneg (Ne.symm hne)
      right
      right
      exact
        pairwiseScoringError_eventually_zero_of_support_pos
          law hiScore loScore
          (by
            intro signal hmass
            simpa [gap] using hsupport_pos signal hmass)

/--
Finite-support Proposition 2 dichotomy.  Under nonnegative expected score gap,
the iid pairwise mistake probability either has some exact finite exponential
rate or is eventually zero in the strict one-sided boundary case.
-/
theorem pairwiseScoringError_exponentialRateCertificate_or_eventually_zero_of_mean_nonneg
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal)) :
    (∃ rate : ℝ,
      ExponentialRateCertificate
        (pairwiseScoringErrorProb law hiScore loScore)
        rate) ∨
      (∀ᶠ n in Filter.atTop,
        pairwiseScoringErrorProb law hiScore loScore n = 0) := by
  rcases
      pairwiseScoringError_exponentialRateCertificate_or_boundary_of_mean_nonneg
        law hiScore loScore hmean with
    hsource | hboundary
  · exact Or.inl ⟨pairwiseScoringRate law hiScore loScore, hsource⟩
  · rcases hboundary with hzero | hstrict
    · rcases hzero with ⟨pZero, _hZeroProb, _hZero_pos, hcert⟩
      exact Or.inl ⟨-Real.log pZero, hcert⟩
    · exact Or.inr hstrict

/--
Finite-support Proposition 2 as a single extended-rate statement.  The rate is
finite in the source/tie-boundary cases and `⊤` when the pairwise error is
eventually zero.
-/
theorem pairwiseScoringError_hasExtendedExponentialRate_of_mean_nonneg
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal)) :
    ∃ rate : WithTop ℝ,
      HasExtendedExponentialRate
        (pairwiseScoringErrorProb law hiScore loScore)
        rate := by
  rcases
      pairwiseScoringError_exponentialRateCertificate_or_eventually_zero_of_mean_nonneg
        law hiScore loScore hmean with
    hfinite | hzero
  · rcases hfinite with ⟨rate, hcert⟩
    exact ⟨(rate : WithTop ℝ),
      HasExtendedExponentialRate.finite hcert.has_rate⟩
  · exact ⟨⊤, HasExtendedExponentialRate.infinite hzero⟩

/--
Exact extended-source-rate form of Proposition 2.  The finite branches agree
with the printed `- inf log MGF`; a strictly positive score-gap support has
infinite rate because errors are eventually absent.
-/
theorem pairwiseScoringError_hasExtendedExponentialRate_at_pairwiseScoringExtendedRate_of_mean_nonneg
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤ AppliedModelingLib.pmfExp law
        (fun signal => hiScore signal - loScore signal)) :
    HasExtendedExponentialRate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringExtendedRate law hiScore loScore) := by
  classical
  let gap : Signal → ℝ := fun signal => hiScore signal - loScore signal
  by_cases hneg : ∃ aNeg : Signal, 0 < (law aNeg).toReal ∧ gap aNeg < 0
  · rcases hneg with ⟨aNeg, hmassNeg, hgapNeg⟩
    have hbelow :
        ∃ a, 0 < (law a).toReal ∧
          gap a < AppliedModelingLib.pmfExp law gap := by
      exact ⟨aNeg, hmassNeg, lt_of_lt_of_le hgapNeg hmean⟩
    rcases
        AppliedModelingLib.exists_support_value_gt_pmfExp_of_exists_value_lt_pmfExp
          law gap hbelow with
      ⟨aPos, hmassPos, hmean_lt_gap⟩
    have hgapPos : 0 < gap aPos := lt_of_le_of_lt hmean hmean_lt_gap
    rcases
        exists_nonpos_weighted_exp_score_sum_eq_zero_of_pmfExp_nonneg_pos_neg_atoms
          law gap hmean hmassPos (by simpa [gap] using hgapPos)
          hmassNeg (by simpa [gap] using hgapNeg) with
      ⟨z, _hz, hstationary⟩
    have hderiv :
        HasDerivAt (fun z : ℝ => finiteLogMGF law gap z) 0 z := by
      exact
        finiteLogMGF_hasDerivAt_zero_of_weighted_exp_score_sum_eq_zero
          law gap hstationary
    have hrate :
        pairwiseScoringRate law hiScore loScore =
          -finiteLogMGF law gap z := by
      simpa [finiteLogMGF] using
        pairwiseScoringRate_eq_neg_log_base_of_stationary
          (law := law) (hiScore := hiScore) (loScore := loScore)
          (base := finiteMGF law gap z) (z0 := z) hstationary rfl
    have htop :
        pairwiseScoringExtendedRate law hiScore loScore =
          (pairwiseScoringRate law hiScore loScore : WithTop ℝ) := by
      unfold pairwiseScoringExtendedRate
      rw [finiteRateFunctionTop_eq_eval_of_logMGF_hasDerivAt law gap 0 z hderiv]
      rw [WithTop.coe_eq_coe]
      simpa [finiteLegendreValue] using hrate.symm
    rw [htop]
    exact HasExtendedExponentialRate.finite
      (pairwiseScoringError_exponentialRateCertificate_of_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms
        law hiScore loScore hmean
        (aPos := aPos) (aNeg := aNeg)
        hmassPos (by simpa [gap] using hgapPos)
        hmassNeg (by simpa [gap] using hgapNeg)).has_rate
  · have hsupport_nonneg :
        ∀ signal, 0 < (law signal).toReal → 0 ≤ gap signal := by
      intro signal hmass
      exact le_of_not_gt (fun hgap => hneg ⟨signal, hmass, hgap⟩)
    by_cases hzero :
        ∃ aZero : Signal, 0 < (law aZero).toReal ∧ gap aZero = 0
    · rcases hzero with ⟨aZero, hmassZero, hgapZero⟩
      let pZero : ℝ :=
        AppliedModelingLib.pmfProb law (fun signal => gap signal = 0)
      have hpZero_pos : 0 < pZero := by
        dsimp [pZero]
        exact
          (AppliedModelingLib.pmfProb_pos_iff_exists_pos_mass
            law (fun signal => gap signal = 0)).2
            ⟨aZero, hgapZero, hmassZero⟩
      have htop :
          pairwiseScoringExtendedRate law hiScore loScore =
            (-Real.log pZero : WithTop ℝ) := by
        unfold pairwiseScoringExtendedRate
        exact
          finiteRateFunctionTop_eq_neg_log_pmfProb_score_eq_zero_of_support_nonneg
            law gap
            (by
              intro signal hmass
              simpa [gap] using hsupport_nonneg signal hmass)
            (by rfl) hpZero_pos
      rw [htop]
      exact HasExtendedExponentialRate.finite
        (pairwiseScoringError_exponentialRateCertificate_of_support_nonneg_zero_gap_prob
          law hiScore loScore
          (by
            intro signal hmass
            simpa [gap] using hsupport_nonneg signal hmass)
          (pZero := pZero) (by rfl) hpZero_pos).has_rate
    · have hsupport_pos :
          ∀ signal, 0 < (law signal).toReal → 0 < gap signal := by
        intro signal hmass
        have hnonneg := hsupport_nonneg signal hmass
        have hne : gap signal ≠ 0 := by
          intro hgap
          exact hzero ⟨signal, hmass, hgap⟩
        exact lt_of_le_of_ne hnonneg (Ne.symm hne)
      have htop : pairwiseScoringExtendedRate law hiScore loScore = ⊤ := by
        unfold pairwiseScoringExtendedRate
        exact finiteRateFunctionTop_eq_top_of_support_pos law gap
          (by
            intro signal hmass
            simpa [gap] using hsupport_pos signal hmass)
      rw [htop]
      exact HasExtendedExponentialRate.infinite
        (pairwiseScoringError_eventually_zero_of_support_pos
          law hiScore loScore
          (by
            intro signal hmass
            simpa [gap] using hsupport_pos signal hmass))

/--
Certificate-level form of the extended Proposition 2 rate.  A finite branch
records the exact source rate; the remaining branch records both eventual
absence of pairwise errors and the infinite source rate.
-/
theorem pairwiseScoringError_extendedRateCertificate_or_eventually_zero_of_mean_nonneg
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤ AppliedModelingLib.pmfExp law
        (fun signal => hiScore signal - loScore signal)) :
    (∃ rate : ℝ,
      ExponentialRateCertificate
          (pairwiseScoringErrorProb law hiScore loScore) rate ∧
        pairwiseScoringExtendedRate law hiScore loScore =
          (rate : WithTop ℝ)) ∨
      ((∀ᶠ n in Filter.atTop,
          pairwiseScoringErrorProb law hiScore loScore n = 0) ∧
        pairwiseScoringExtendedRate law hiScore loScore = ⊤) := by
  classical
  let gap : Signal → ℝ := fun signal => hiScore signal - loScore signal
  by_cases hneg : ∃ aNeg : Signal, 0 < (law aNeg).toReal ∧ gap aNeg < 0
  · rcases hneg with ⟨aNeg, hmassNeg, hgapNeg⟩
    have hbelow :
        ∃ a, 0 < (law a).toReal ∧
          gap a < AppliedModelingLib.pmfExp law gap := by
      exact ⟨aNeg, hmassNeg, lt_of_lt_of_le hgapNeg hmean⟩
    rcases
        AppliedModelingLib.exists_support_value_gt_pmfExp_of_exists_value_lt_pmfExp
          law gap hbelow with
      ⟨aPos, hmassPos, hmean_lt_gap⟩
    have hgapPos : 0 < gap aPos := lt_of_le_of_lt hmean hmean_lt_gap
    rcases
        exists_nonpos_weighted_exp_score_sum_eq_zero_of_pmfExp_nonneg_pos_neg_atoms
          law gap hmean hmassPos (by simpa [gap] using hgapPos)
          hmassNeg (by simpa [gap] using hgapNeg) with
      ⟨z, _hz, hstationary⟩
    have hderiv :
        HasDerivAt (fun z : ℝ => finiteLogMGF law gap z) 0 z := by
      exact
        finiteLogMGF_hasDerivAt_zero_of_weighted_exp_score_sum_eq_zero
          law gap hstationary
    have hrate :
        pairwiseScoringRate law hiScore loScore =
          -finiteLogMGF law gap z := by
      simpa [finiteLogMGF] using
        pairwiseScoringRate_eq_neg_log_base_of_stationary
          (law := law) (hiScore := hiScore) (loScore := loScore)
          (base := finiteMGF law gap z) (z0 := z) hstationary rfl
    have htop :
        pairwiseScoringExtendedRate law hiScore loScore =
          (pairwiseScoringRate law hiScore loScore : WithTop ℝ) := by
      unfold pairwiseScoringExtendedRate
      rw [finiteRateFunctionTop_eq_eval_of_logMGF_hasDerivAt law gap 0 z hderiv]
      rw [WithTop.coe_eq_coe]
      simpa [finiteLegendreValue] using hrate.symm
    left
    refine ⟨pairwiseScoringRate law hiScore loScore, ?_, htop⟩
    exact
      pairwiseScoringError_exponentialRateCertificate_of_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms
        law hiScore loScore hmean
        (aPos := aPos) (aNeg := aNeg)
        hmassPos (by simpa [gap] using hgapPos)
        hmassNeg (by simpa [gap] using hgapNeg)
  · have hsupport_nonneg :
        ∀ signal, 0 < (law signal).toReal → 0 ≤ gap signal := by
      intro signal hmass
      exact le_of_not_gt (fun hgap => hneg ⟨signal, hmass, hgap⟩)
    by_cases hzero :
        ∃ aZero : Signal, 0 < (law aZero).toReal ∧ gap aZero = 0
    · rcases hzero with ⟨aZero, hmassZero, hgapZero⟩
      let pZero : ℝ :=
        AppliedModelingLib.pmfProb law (fun signal => gap signal = 0)
      have hpZero_pos : 0 < pZero := by
        dsimp [pZero]
        exact
          (AppliedModelingLib.pmfProb_pos_iff_exists_pos_mass
            law (fun signal => gap signal = 0)).2
            ⟨aZero, hgapZero, hmassZero⟩
      have htop :
          pairwiseScoringExtendedRate law hiScore loScore =
            (-Real.log pZero : WithTop ℝ) := by
        unfold pairwiseScoringExtendedRate
        exact
          finiteRateFunctionTop_eq_neg_log_pmfProb_score_eq_zero_of_support_nonneg
            law gap
            (by
              intro signal hmass
              simpa [gap] using hsupport_nonneg signal hmass)
            (by rfl) hpZero_pos
      left
      refine ⟨-Real.log pZero, ?_, htop⟩
      exact
        pairwiseScoringError_exponentialRateCertificate_of_support_nonneg_zero_gap_prob
          law hiScore loScore
          (by
            intro signal hmass
            simpa [gap] using hsupport_nonneg signal hmass)
          (pZero := pZero) (by rfl) hpZero_pos
    · have hsupport_pos :
          ∀ signal, 0 < (law signal).toReal → 0 < gap signal := by
        intro signal hmass
        have hnonneg := hsupport_nonneg signal hmass
        have hne : gap signal ≠ 0 := by
          intro hgap
          exact hzero ⟨signal, hmass, hgap⟩
        exact lt_of_le_of_ne hnonneg (Ne.symm hne)
      have htop : pairwiseScoringExtendedRate law hiScore loScore = ⊤ := by
        unfold pairwiseScoringExtendedRate
        exact finiteRateFunctionTop_eq_top_of_support_pos law gap
          (by
            intro signal hmass
            simpa [gap] using hsupport_pos signal hmass)
      right
      refine ⟨?_, htop⟩
      exact
        pairwiseScoringError_eventually_zero_of_support_pos
          law hiScore loScore
          (by
            intro signal hmass
            simpa [gap] using hsupport_pos signal hmass)

/--
Full-support convenience wrapper for
`pairwiseScoringError_exponentialRateCertificate_of_stationary_tilted_modal_log_support`.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_stationary_tilted_modal_log_full_support
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (_hlaw_full : ∀ signal : Signal, 0 < (law signal).toReal)
    {z : ℝ}
    (hstationary :
      (∑ signal : Signal,
        (law signal).toReal *
          ((hiScore signal - loScore signal) *
            Real.exp (z * (hiScore signal - loScore signal)))) = 0) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) :=
  pairwiseScoringError_exponentialRateCertificate_of_stationary_tilted_modal_log_support
    law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg hstationary

/--
Exact pairwise rate from empirical-type lower witnesses available at every
strictly slower target rate.  This is the entropy-aware method-of-types-facing
form of Proposition 2: each witness may use the full multinomial type mass,
not just a single periodic path.
-/
theorem pairwiseScoringError_exponentialRateCertificate_of_empiricalTypeLower_witnesses_of_mean_nonneg_pos_neg_atoms
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp law
          (fun signal => hiScore signal - loScore signal))
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (hlower :
      ∀ targetRate,
        pairwiseScoringRate law hiScore loScore < targetRate →
        ∃ C : FiniteIidScoreGapEmpiricalTypeLowerCertificate law hiScore loScore,
          -Real.log C.base < targetRate) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (pairwiseScoringRate law hiScore loScore) := by
  have hCramer :
      FiniteIidScoreGapCramerCertificate law hiScore loScore :=
    finiteIidScoreGapCramerCertificate_of_empiricalTypeLower_witnesses_of_pos_neg_atoms
      law hiScore loScore hmean hmassPos hgapPos hmassNeg hgapNeg
      (fun targetRate htarget => by
        exact hlower targetRate (by
          simpa [pairwiseScoringRate, finiteScoreGapChernoffRate] using
            htarget))
  exact pairwiseScoringError_exponentialRateCertificate_of_cramer
    law hiScore loScore hCramer

/--
Pairwise scoring-rate comparison from the source proof's convexity step.  If
the convex-combination scoring rule has pointwise no larger score-gap log-MGF
than the randomized scoring mechanism, then its Chernoff pairwise rate weakly
dominates the randomized mechanism's rate.
-/
theorem pairwiseScoringRate_le_static_of_logMGF_domination
    {StaticSignal RandomizedSignal : Type*}
    [Fintype StaticSignal] [Fintype RandomizedSignal]
    [DecidableEq StaticSignal] [DecidableEq RandomizedSignal]
    (staticLaw : PMF StaticSignal) (randomizedLaw : PMF RandomizedSignal)
    (staticHiScore staticLoScore : StaticSignal → ℝ)
    (randomizedHiScore randomizedLoScore : RandomizedSignal → ℝ)
    (hstatic_bdd :
      BddBelow (Set.range fun z : ℝ =>
        finiteLogMGF staticLaw
          (fun signal => staticHiScore signal - staticLoScore signal) z))
    (hlog :
      ∀ z : ℝ,
        finiteLogMGF staticLaw
            (fun signal => staticHiScore signal - staticLoScore signal) z ≤
          finiteLogMGF randomizedLaw
            (fun signal => randomizedHiScore signal - randomizedLoScore signal)
            z) :
    pairwiseScoringRate randomizedLaw randomizedHiScore randomizedLoScore ≤
      pairwiseScoringRate staticLaw staticHiScore staticLoScore := by
  simpa [pairwiseScoringRate] using
    finiteChernoffRate_mono_of_logMGF_le
      staticLaw randomizedLaw
      (fun signal => staticHiScore signal - staticLoScore signal)
      (fun signal => randomizedHiScore signal - randomizedLoScore signal)
      hstatic_bdd hlog

/--
Source-facing pairwise scoring-rate comparison with the bounded-below
log-MGF premise discharged from concrete positive and negative static atoms.
-/
theorem pairwiseScoringRate_le_static_of_logMGF_domination_of_pos_neg_atoms
    {StaticSignal RandomizedSignal : Type*}
    [Fintype StaticSignal] [Fintype RandomizedSignal]
    [DecidableEq StaticSignal] [DecidableEq RandomizedSignal]
    (staticLaw : PMF StaticSignal) (randomizedLaw : PMF RandomizedSignal)
    (staticHiScore staticLoScore : StaticSignal → ℝ)
    (randomizedHiScore randomizedLoScore : RandomizedSignal → ℝ)
    {aPos aNeg : StaticSignal}
    (hmassPos : 0 < (staticLaw aPos).toReal)
    (hgapPos : 0 < staticHiScore aPos - staticLoScore aPos)
    (hmassNeg : 0 < (staticLaw aNeg).toReal)
    (hgapNeg : staticHiScore aNeg - staticLoScore aNeg < 0)
    (hlog :
      ∀ z : ℝ,
        finiteLogMGF staticLaw
            (fun signal => staticHiScore signal - staticLoScore signal) z ≤
          finiteLogMGF randomizedLaw
            (fun signal => randomizedHiScore signal - randomizedLoScore signal)
            z) :
    pairwiseScoringRate randomizedLaw randomizedHiScore randomizedLoScore ≤
      pairwiseScoringRate staticLaw staticHiScore staticLoScore :=
  pairwiseScoringRate_le_static_of_logMGF_domination
    staticLaw randomizedLaw staticHiScore staticLoScore
    randomizedHiScore randomizedLoScore
    (finiteScoreGapLogMGF_bddBelow_of_pos_neg_atoms
      staticLaw staticHiScore staticLoScore
      hmassPos hgapPos hmassNeg hgapNeg)
    hlog

/-! ### Scoring-rule randomization -/

/-- MGF of a finite randomization over scoring-rule score gaps. -/
def randomizedScoringMixtureMGF
    {Rule Signal : Type*} [Fintype Rule] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ)
    (gap : Rule → Signal → ℝ) (z : ℝ) : ℝ :=
  ∑ rule : Rule, weight rule * finiteMGF law (gap rule) z

/-- Log-MGF of a finite randomization over scoring-rule score gaps. -/
def randomizedScoringMixtureLogMGF
    {Rule Signal : Type*} [Fintype Rule] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ)
    (gap : Rule → Signal → ℝ) (z : ℝ) : ℝ :=
  Real.log (randomizedScoringMixtureMGF law weight gap z)

/-- Chernoff exponent for the source's finite randomized scoring-rule mixture. -/
def randomizedScoringMixtureRate
    {Rule Signal : Type*} [Fintype Rule] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ)
    (gap : Rule → Signal → ℝ) : ℝ :=
  -sInf (Set.range fun z : ℝ =>
    randomizedScoringMixtureLogMGF law weight gap z)

/--
One-voter law for a randomized scoring rule: first draw the rule from the
finite weight vector, then draw the signal/ranking from the supplied law.
-/
noncomputable def randomizedScoringSamplingLaw
    {Rule Signal : Type*} [Fintype Rule] [DecidableEq Rule]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1) :
    PMF (Rule × Signal) :=
  let ruleLaw : PMF Rule :=
    AppliedModelingLib.finiteWeightedPMF weight hweight
      (by simpa [hsum] using zero_lt_one)
  ruleLaw.bind (fun rule => law.map (fun signal => (rule, signal)))

/--
Expectation under the actual randomized-scoring one-voter law is the weighted
average of the component-rule expectations.
-/
theorem randomizedScoringSamplingLaw_pmfExp_eq_weighted_sum
    {Rule Signal : Type*} [Fintype Rule] [DecidableEq Rule]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (f : Rule → Signal → ℝ) :
    AppliedModelingLib.pmfExp
        (randomizedScoringSamplingLaw law weight hweight hsum)
        (fun signal : Rule × Signal => f signal.1 signal.2) =
      ∑ rule : Rule, weight rule * AppliedModelingLib.pmfExp law (f rule) := by
  classical
  unfold randomizedScoringSamplingLaw
  rw [AppliedModelingLib.pmfExp_bind]
  change
    AppliedModelingLib.pmfExp
        (AppliedModelingLib.finiteWeightedPMF weight hweight
          (by simpa [hsum] using zero_lt_one))
        (fun rule =>
          AppliedModelingLib.pmfExp (law.map (fun signal => (rule, signal)))
            (fun signal : Rule × Signal => f signal.1 signal.2)) =
      ∑ rule : Rule, weight rule * AppliedModelingLib.pmfExp law (f rule)
  calc
    AppliedModelingLib.pmfExp
        (AppliedModelingLib.finiteWeightedPMF weight hweight
          (by simpa [hsum] using zero_lt_one))
        (fun rule =>
          AppliedModelingLib.pmfExp (law.map (fun signal => (rule, signal)))
            (fun signal : Rule × Signal => f signal.1 signal.2))
        =
        ∑ rule : Rule,
          weight rule *
            AppliedModelingLib.pmfExp (law.map (fun signal => (rule, signal)))
              (fun signal : Rule × Signal => f signal.1 signal.2) := by
          exact
            AppliedModelingLib.finiteWeightedPMF_pmfExp_eq_weighted_sum_of_sum_eq_one
              weight hweight hsum
              (fun rule =>
                AppliedModelingLib.pmfExp (law.map (fun signal => (rule, signal)))
                  (fun signal : Rule × Signal => f signal.1 signal.2))
    _ = ∑ rule : Rule, weight rule * AppliedModelingLib.pmfExp law (f rule) := by
          refine Finset.sum_congr rfl ?_
          intro rule _
          rw [AppliedModelingLib.pmfExp_map]

/--
The actual randomized-scoring one-voter law has exactly the MGF used in the
source Jensen calculation.
-/
theorem randomizedScoringSamplingLaw_finiteMGF_eq_mixtureMGF
    {Rule Signal : Type*} [Fintype Rule] [DecidableEq Rule]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (gap : Rule → Signal → ℝ) (z : ℝ) :
    finiteMGF
        (randomizedScoringSamplingLaw law weight hweight hsum)
        (fun signal : Rule × Signal => gap signal.1 signal.2) z =
      randomizedScoringMixtureMGF law weight gap z := by
  classical
  unfold randomizedScoringSamplingLaw
  change
    AppliedModelingLib.pmfExp
        ((AppliedModelingLib.finiteWeightedPMF weight hweight
          (by simpa [hsum] using zero_lt_one)).bind
          (fun rule => law.map (fun signal => (rule, signal))))
        (fun signal : Rule × Signal =>
          Real.exp (z * gap signal.1 signal.2)) =
      randomizedScoringMixtureMGF law weight gap z
  rw [AppliedModelingLib.pmfExp_bind]
  calc
    AppliedModelingLib.pmfExp
        (AppliedModelingLib.finiteWeightedPMF weight hweight
          (by simpa [hsum] using zero_lt_one))
        (fun rule : Rule =>
          AppliedModelingLib.pmfExp (law.map (fun signal => (rule, signal)))
            (fun signal : Rule × Signal =>
              Real.exp (z * gap signal.1 signal.2)))
        =
        AppliedModelingLib.pmfExp
          (AppliedModelingLib.finiteWeightedPMF weight hweight
            (by simpa [hsum] using zero_lt_one))
          (fun rule : Rule => finiteMGF law (gap rule) z) := by
          exact
            AppliedModelingLib.pmfExp_congr
              (AppliedModelingLib.finiteWeightedPMF weight hweight
                (by simpa [hsum] using zero_lt_one))
              (fun rule => by
                have hmap :
                    AppliedModelingLib.pmfExp
                        (law.map (fun signal => (rule, signal)))
                        (fun signal : Rule × Signal =>
                          Real.exp (z * gap signal.1 signal.2)) =
                      AppliedModelingLib.pmfExp law
                        (fun signal : Signal =>
                          Real.exp (z * gap rule signal)) := by
                  rw [AppliedModelingLib.pmfExp_map]
                simpa [finiteMGF] using hmap)
    _ = ∑ rule : Rule, weight rule * finiteMGF law (gap rule) z := by
          unfold AppliedModelingLib.pmfExp
          simp [AppliedModelingLib.finiteWeightedPMF_apply_toReal, hsum]
    _ = randomizedScoringMixtureMGF law weight gap z := by
          rfl

theorem randomizedScoringSamplingLaw_finiteLogMGF_eq_mixtureLogMGF
    {Rule Signal : Type*} [Fintype Rule] [DecidableEq Rule]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (gap : Rule → Signal → ℝ) (z : ℝ) :
    finiteLogMGF
        (randomizedScoringSamplingLaw law weight hweight hsum)
        (fun signal : Rule × Signal => gap signal.1 signal.2) z =
      randomizedScoringMixtureLogMGF law weight gap z := by
  unfold finiteLogMGF randomizedScoringMixtureLogMGF
  rw [randomizedScoringSamplingLaw_finiteMGF_eq_mixtureMGF
    law weight hweight hsum gap z]

/--
The Chernoff rate of the actual randomized-scoring sampling law is the mixture
rate appearing in the paper's convexity proof.
-/
theorem randomizedScoringSamplingLaw_finiteChernoffRate_eq_mixtureRate
    {Rule Signal : Type*} [Fintype Rule] [DecidableEq Rule]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (gap : Rule → Signal → ℝ) :
    finiteChernoffRate
        (randomizedScoringSamplingLaw law weight hweight hsum)
        (fun signal : Rule × Signal => gap signal.1 signal.2) =
      randomizedScoringMixtureRate law weight gap := by
  have hfun :
      (fun z : ℝ =>
        finiteLogMGF
          (randomizedScoringSamplingLaw law weight hweight hsum)
          (fun signal : Rule × Signal => gap signal.1 signal.2) z) =
        (fun z : ℝ =>
          randomizedScoringMixtureLogMGF law weight gap z) := by
    funext z
    exact randomizedScoringSamplingLaw_finiteLogMGF_eq_mixtureLogMGF
      law weight hweight hsum gap z
  simp [finiteChernoffRate, randomizedScoringMixtureRate, hfun]

/--
Pointwise Jensen step in the scoring-rule randomization proof: the MGF of the
static convex-combination score gap is bounded by the weighted average of the
component MGFs.
-/
theorem finiteMGF_weightedScore_le_weightedMGF
    {Rule Signal : Type*} [Fintype Rule] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (gap : Rule → Signal → ℝ)
    (staticGap : Signal → ℝ) (z : ℝ)
    (hstatic :
      ∀ signal,
        staticGap signal = ∑ rule : Rule, weight rule * gap rule signal)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1) :
    finiteMGF law staticGap z ≤
      randomizedScoringMixtureMGF law weight gap z := by
  have hpoint : ∀ signal : Signal,
      Real.exp (z * staticGap signal) ≤
        ∑ rule : Rule, weight rule * Real.exp (z * gap rule signal) := by
    intro signal
    have hj := convexOn_exp.map_sum_le
      (t := (Finset.univ : Finset Rule))
      (w := weight)
      (p := fun rule => z * gap rule signal)
      (by intro rule _; exact hweight rule)
      (by simpa using hsum)
      (by intro rule _; exact Set.mem_univ _)
    simp only [smul_eq_mul] at hj
    have hsum_arg :
        (∑ rule : Rule, weight rule * (z * gap rule signal)) =
          z * staticGap signal := by
      rw [hstatic signal]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro rule _
      ring
    rwa [hsum_arg] at hj
  calc
    finiteMGF law staticGap z
        = ∑ signal : Signal,
            (law signal).toReal * Real.exp (z * staticGap signal) := by
          rfl
    _ ≤ ∑ signal : Signal, (law signal).toReal *
          (∑ rule : Rule,
            weight rule * Real.exp (z * gap rule signal)) := by
      refine Finset.sum_le_sum ?_
      intro signal _
      exact mul_le_mul_of_nonneg_left
        (hpoint signal) ENNReal.toReal_nonneg
    _ = randomizedScoringMixtureMGF law weight gap z := by
      unfold randomizedScoringMixtureMGF
      calc
        (∑ signal : Signal, (law signal).toReal *
            (∑ rule : Rule,
              weight rule * Real.exp (z * gap rule signal)))
            = ∑ signal : Signal, ∑ rule : Rule,
                (law signal).toReal *
                  (weight rule * Real.exp (z * gap rule signal)) := by
              refine Finset.sum_congr rfl ?_
              intro signal _
              rw [Finset.mul_sum]
        _ = ∑ rule : Rule, ∑ signal : Signal,
                (law signal).toReal *
                  (weight rule * Real.exp (z * gap rule signal)) := by
              rw [Finset.sum_comm]
        _ = ∑ rule : Rule, weight rule * finiteMGF law (gap rule) z := by
              refine Finset.sum_congr rfl ?_
              intro rule _
              dsimp [finiteMGF]
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro signal _
              ring

theorem randomizedScoringMixtureMGF_pos
    {Rule Signal : Type*} [Fintype Rule] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ)
    (gap : Rule → Signal → ℝ) (z : ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1) :
    0 < randomizedScoringMixtureMGF law weight gap z := by
  have hweight_exists : ∃ rule : Rule, 0 < weight rule := by
    by_contra hnone
    have hnonpos : ∀ rule : Rule, weight rule ≤ 0 := by
      intro rule
      exact le_of_not_gt (fun hpos => hnone ⟨rule, hpos⟩)
    have hsum_nonpos : (∑ rule : Rule, weight rule) ≤ 0 :=
      Finset.sum_nonpos (by intro rule _; exact hnonpos rule)
    linarith
  unfold randomizedScoringMixtureMGF
  refine Finset.sum_pos' ?_ ?_
  · intro rule _
    exact mul_nonneg (hweight rule)
      (finiteMGF_nonneg law (gap rule) z)
  · rcases hweight_exists with ⟨rule, hpos⟩
    exact ⟨rule, Finset.mem_univ rule,
      mul_pos hpos (finiteMGF_pos law (gap rule) z)⟩

theorem finiteLogMGF_weightedScore_le_randomizedScoringMixtureLogMGF
    {Rule Signal : Type*} [Fintype Rule] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (gap : Rule → Signal → ℝ)
    (staticGap : Signal → ℝ) (z : ℝ)
    (hstatic :
      ∀ signal,
        staticGap signal = ∑ rule : Rule, weight rule * gap rule signal)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1) :
    finiteLogMGF law staticGap z ≤
      randomizedScoringMixtureLogMGF law weight gap z := by
  unfold finiteLogMGF randomizedScoringMixtureLogMGF
  exact Real.log_le_log
    (finiteMGF_pos law staticGap z)
    (finiteMGF_weightedScore_le_weightedMGF
      law weight gap staticGap z hstatic hweight hsum)

/--
Source theorem `lem:randomizebetterscoring`, pairwise-rate core: the static
convex-combination scoring rule weakly dominates the randomized scoring-rule
mixture in Chernoff rate.
-/
theorem randomizedScoringMixtureRate_le_static_of_weighted_score
    {Rule Signal : Type*} [Fintype Rule] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (gap : Rule → Signal → ℝ)
    (staticGap : Signal → ℝ)
    (hstatic :
      ∀ signal,
        staticGap signal = ∑ rule : Rule, weight rule * gap rule signal)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hstatic_bdd :
      BddBelow (Set.range fun z : ℝ => finiteLogMGF law staticGap z)) :
    randomizedScoringMixtureRate law weight gap ≤
      finiteChernoffRate law staticGap := by
  simpa [randomizedScoringMixtureRate, finiteChernoffRate] using
    neg_sInf_range_mono_of_pointwise_le hstatic_bdd
      (fun z =>
        finiteLogMGF_weightedScore_le_randomizedScoringMixtureLogMGF
          law weight gap staticGap z hstatic hweight hsum)

/--
Source-facing randomized-scoring Jensen endpoint with the bounded-below
log-MGF premise discharged from concrete positive and negative static atoms.
-/
theorem randomizedScoringMixtureRate_le_static_of_weighted_score_of_pos_neg_atoms
    {Rule Signal : Type*} [Fintype Rule] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (gap : Rule → Signal → ℝ)
    (staticGap : Signal → ℝ)
    (hstatic :
      ∀ signal,
        staticGap signal = ∑ rule : Rule, weight rule * gap rule signal)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    {aPos aNeg : Signal}
    (hmassPos : 0 < (law aPos).toReal)
    (hgapPos : 0 < staticGap aPos)
    (hmassNeg : 0 < (law aNeg).toReal)
    (hgapNeg : staticGap aNeg < 0) :
    randomizedScoringMixtureRate law weight gap ≤
      finiteChernoffRate law staticGap :=
  randomizedScoringMixtureRate_le_static_of_weighted_score
    law weight gap staticGap hstatic hweight hsum
    (finiteLogMGF_bddBelow_of_pos_neg_atoms
      law staticGap hmassPos hgapPos hmassNeg hgapNeg)

/-- Score-gap error probability for a pair of candidates under a common voter law. -/
def finiteScoreGapPairwiseErrorProb
    {Candidate Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Candidate) (n : ℕ) : ℝ :=
  pairwiseScoringErrorProb law (score hi) (score lo) n

/--
Relevant-pair finite aggregation for the strict-support boundary: if every
indexed relevant pair has a strictly positive one-voter score gap on every
positive-mass signal, then the corresponding finite weighted aggregate error
is eventually zero.
-/
theorem finiteRelevantScoreGapAggregateError_eventually_zero_of_support_pos
    {Pair Candidate Signal : Type*} [Fintype Pair]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    {pairWeight : Pair → ℝ}
    (hsupport :
      ∀ pair signal, 0 < (law signal).toReal →
        0 < score (hi pair) signal - score (lo pair) signal) :
    ∀ᶠ n in Filter.atTop,
      (∑ pair : Pair,
        pairWeight pair *
          finiteScoreGapPairwiseErrorProb law score
            (hi pair) (lo pair) n) = 0 := by
  simpa [finiteScoreGapPairwiseErrorProb] using
    finite_weighted_sum_eventually_zero
      (ι := Pair)
      (p := fun pair n =>
        pairwiseScoringErrorProb law (score (hi pair)) (score (lo pair)) n)
      (weight := pairWeight)
      (fun pair =>
        pairwiseScoringError_eventually_zero_of_support_pos
          law (score (hi pair)) (score (lo pair)) (hsupport pair))

/--
Relevant-pair finite aggregation for the strict-support boundary: if every
indexed relevant pair is eventually error-free, the aggregate has an eventual
exponential upper bound at every finite target rate.
-/
theorem finiteRelevantScoreGapAggregateError_hasExpUpperBoundWithConst_of_support_pos
    {Pair Candidate Signal : Type*} [Fintype Pair]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    {pairWeight : Pair → ℝ}
    (hsupport :
      ∀ pair signal, 0 < (law signal).toReal →
        0 < score (hi pair) signal - score (lo pair) signal)
    (targetRate : ℝ) :
    HasExpUpperBoundWithConst
      (fun n =>
        ∑ pair : Pair,
          pairWeight pair *
            finiteScoreGapPairwiseErrorProb law score
              (hi pair) (lo pair) n)
      targetRate :=
  HasExpUpperBoundWithConst.of_eventually_zero
    (finiteRelevantScoreGapAggregateError_eventually_zero_of_support_pos
      law score hi lo (pairWeight := pairWeight) hsupport)

/--
Exact-rate certificate for a finite family of relevant one-sided boundary
pairs: if every positive-mass score gap is nonnegative and each indexed pair
has positive zero-gap probability, then that pair's finite iid error
probability has rate `-log pZero`.
-/
def finiteScoreGapRelevantPairRateCertificate_of_support_nonneg_zero_gap_prob
    {Pair Candidate Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    (pZero : Pair → ℝ)
    (hsupport :
      ∀ pair signal, 0 < (law signal).toReal →
        0 ≤ score (hi pair) signal - score (lo pair) signal)
    (hZeroProb :
      ∀ pair,
        AppliedModelingLib.pmfProb law
            (fun signal =>
              score (hi pair) signal - score (lo pair) signal = 0) =
          pZero pair)
    (hZero_pos : ∀ pair, 0 < pZero pair) :
    FiniteErrorRateCertificate Pair where
  errorProb :=
    fun pair => finiteScoreGapPairwiseErrorProb law score (hi pair) (lo pair)
  rate := fun pair => -Real.log (pZero pair)
  has_rate := by
    intro pair
    simpa [finiteScoreGapPairwiseErrorProb] using
      pairwiseScoringError_exponentialRateCertificate_of_support_nonneg_zero_gap_prob
        law (score (hi pair)) (score (lo pair))
        (fun signal hmass => hsupport pair signal hmass)
        (hZeroProb pair) (hZero_pos pair)

/--
Relevant-pair exact finite aggregation for the one-sided zero-gap boundary.
One positive-weight relevant pair supplies the realized minimum rate
`-log pZero`; the remaining indexed pairs have rate at least that value.
-/
theorem finiteRelevantScoreGapAggregateError_hasExponentialRate_of_support_nonneg_zero_gap_prob
    {Pair Candidate Signal : Type*} [Fintype Pair] [DecidableEq Pair]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    (pZero : Pair → ℝ)
    (hsupport :
      ∀ pair signal, 0 < (law signal).toReal →
        0 ≤ score (hi pair) signal - score (lo pair) signal)
    (hZeroProb :
      ∀ pair,
        AppliedModelingLib.pmfProb law
            (fun signal =>
              score (hi pair) signal - score (lo pair) signal = 0) =
          pZero pair)
    (hZero_pos : ∀ pair, 0 < pZero pair)
    {pairWeight : Pair → ℝ} {minRate : ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (pairMin : Pair)
    (hweight_pos : 0 < pairWeight pairMin)
    (hrate_min : -Real.log (pZero pairMin) = minRate)
    (hrate_ge : ∀ pair, minRate ≤ -Real.log (pZero pair)) :
    HasExponentialRate
      ((finiteScoreGapRelevantPairRateCertificate_of_support_nonneg_zero_gap_prob
          law score hi lo pZero hsupport hZeroProb hZero_pos)
        |>.aggregateError pairWeight)
      minRate :=
  (finiteScoreGapRelevantPairRateCertificate_of_support_nonneg_zero_gap_prob
      law score hi lo pZero hsupport hZeroProb hZero_pos)
    |>.aggregateError_hasExponentialRate_of_min_component
      hweight pairMin hweight_pos hrate_min hrate_ge

/-- Dual-rate formula for one pair of candidates. -/
def finiteScoreGapPairwiseDualRate
    {Candidate Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (dual : Candidate → Candidate → ℝ) (hi lo : Candidate) : ℝ :=
  -(finiteLogMGF law
      (fun signal => score hi signal - score lo signal) (dual hi lo))

/--
Pointwise finite relevant-pair Chernoff sum bound.  If every indexed relevant
pair has a nonpositive dual certifying rate at least `targetRate`, then the
unweighted expected number of indexed pairwise mistakes is bounded by
`card(Pair) * exp (-n * targetRate)`.
-/
theorem finiteRelevantScoreGapErrorSum_le_card_mul_exp_of_nonpos_duals
    {Pair Candidate Signal : Type*} [Fintype Pair]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    (dual : Pair → ℝ) {targetRate : ℝ}
    (hdual : ∀ pair, dual pair ≤ 0)
    (hrate :
      ∀ pair,
        targetRate ≤
          -(finiteLogMGF law
            (fun signal => score (hi pair) signal - score (lo pair) signal)
            (dual pair)))
    (n : ℕ) :
    (∑ pair : Pair,
      finiteScoreGapPairwiseErrorProb law score (hi pair) (lo pair) n) ≤
      (Fintype.card Pair : ℝ) * Real.exp (-(n : ℝ) * targetRate) := by
  calc
    (∑ pair : Pair,
      finiteScoreGapPairwiseErrorProb law score (hi pair) (lo pair) n)
        ≤
        ∑ _pair : Pair, Real.exp (-(n : ℝ) * targetRate) := by
          refine Finset.sum_le_sum ?_
          intro pair _
          simpa [finiteScoreGapPairwiseErrorProb] using
            pairwiseScoringErrorProb_le_exp_of_nonpos_dual_rate_le
              law (score (hi pair)) (score (lo pair))
              (hdual pair) (hrate pair) n
    _ = (Fintype.card Pair : ℝ) *
          Real.exp (-(n : ℝ) * targetRate) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/--
Finite pairwise upper-bound certificate built from nonpositive Chernoff duals.
This is the reusable Section 3.1 bridge before exact Cramer lower bounds are
available.
-/
def finiteScoreGapPairwiseUpperBoundCertificate
    {Candidate Signal : Type*} [Fintype Candidate] [Fintype Signal]
    [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (dual : Candidate → Candidate → ℝ)
    (hdual : ∀ hi lo : Candidate, dual hi lo ≤ 0) :
    PairwiseErrorUpperBoundCertificate Candidate where
  errorProb := finiteScoreGapPairwiseErrorProb law score
  rate := finiteScoreGapPairwiseDualRate law score dual
  has_bound := by
    intro hi lo
    simpa [finiteScoreGapPairwiseErrorProb, finiteScoreGapPairwiseDualRate] using
      pairwiseScoringError_hasExpUpperBoundWithConst_of_dual
        law (score hi) (score lo) (hdual hi lo)

/--
For any finite nonempty relevant-pair index set, if every indexed score gap has
positive one-voter expectation, then the weighted aggregate of the corresponding
iid pairwise error probabilities has some strictly positive exponential
upper-bound rate.
-/
theorem finiteRelevantScoreGapAggregateError_exists_pos_expUpperBoundWithConst
    {Pair Candidate Signal : Type*} [Fintype Pair] [Nonempty Pair]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hmean :
      ∀ pair,
        0 <
          AppliedModelingLib.pmfExp law
            (fun signal => score (hi pair) signal - score (lo pair) signal)) :
    ∃ targetRate : ℝ,
      0 < targetRate ∧
        HasExpUpperBoundWithConst
          (fun n =>
            ∑ pair : Pair,
              pairWeight pair *
                finiteScoreGapPairwiseErrorProb law score
                  (hi pair) (lo pair) n)
          targetRate := by
  exact
    finite_weighted_sum_exists_pos_expUpperBoundWithConst
      (ι := Pair)
      (p := fun pair n =>
        finiteScoreGapPairwiseErrorProb law score (hi pair) (lo pair) n)
      (weight := pairWeight)
      hweight
      (fun pair => by
        simpa [finiteScoreGapPairwiseErrorProb] using
          pairwiseScoringError_exists_pos_expUpperBoundWithConst_of_expected_gap_pos
            law (score (hi pair)) (score (lo pair)) (hmean pair))

/--
Prefix-score aggregate version: strict prefix dominance for every indexed
relevant pair implies some strictly positive exponential upper-bound rate for
the finite weighted sum of all indexed iid pairwise prefix-score errors.
-/
theorem prefixScoringRelevantPairAggregateError_exists_pos_expUpperBoundWithConst
    {Cut Pair Candidate Signal : Type*} [Fintype Cut] [DecidableEq Cut]
    [Fintype Pair] [Nonempty Pair] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (diff : Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (hi lo : Pair → Candidate)
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hdom :
      ∀ pair,
        StrictTopPrefixDominance (prefixProbFromEvent law inPrefix)
          (hi pair) (lo pair))
    (hdiff : ReasonablePrefixWeights diff) :
    ∃ targetRate : ℝ,
      0 < targetRate ∧
        HasExpUpperBoundWithConst
          (fun n =>
            ∑ pair : Pair,
              pairWeight pair *
                pairwiseScoringErrorProb law
                  (prefixScoreFromEvent diff inPrefix (hi pair))
                  (prefixScoreFromEvent diff inPrefix (lo pair)) n)
          targetRate := by
  simpa [finiteScoreGapPairwiseErrorProb] using
    finiteRelevantScoreGapAggregateError_exists_pos_expUpperBoundWithConst
      (law := law)
      (score := fun candidate =>
        prefixScoreFromEvent diff inPrefix candidate)
      (hi := hi) (lo := lo)
      (pairWeight := pairWeight)
      hweight
      (fun pair =>
        pmfExp_prefixScore_gap_pos_of_strictTopPrefixDominance
          law diff inPrefix (hdom pair) hdiff)

/--
Prefix-score aggregate convergence version: strict prefix dominance for every
indexed relevant pair makes the finite weighted iid pairwise-error aggregate
tend to zero.
-/
theorem prefixScoringRelevantPairAggregateError_tendsto_zero
    {Cut Pair Candidate Signal : Type*} [Fintype Cut] [DecidableEq Cut]
    [Fintype Pair] [Nonempty Pair] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (diff : Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (hi lo : Pair → Candidate)
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hdom :
      ∀ pair,
        StrictTopPrefixDominance (prefixProbFromEvent law inPrefix)
          (hi pair) (lo pair))
    (hdiff : ReasonablePrefixWeights diff) :
    Filter.Tendsto
      (fun n =>
        ∑ pair : Pair,
          pairWeight pair *
            pairwiseScoringErrorProb law
              (prefixScoreFromEvent diff inPrefix (hi pair))
              (prefixScoreFromEvent diff inPrefix (lo pair)) n)
      Filter.atTop (nhds 0) := by
  rcases
      prefixScoringRelevantPairAggregateError_exists_pos_expUpperBoundWithConst
        law diff inPrefix hi lo hweight hdom hdiff with
    ⟨targetRate, hrate_pos, hbound⟩
  exact hbound.tendsto_zero_of_pos_rate hrate_pos

/-! ## Proposition 1 source-level selection bridge -/

/-- Cross-tier ordered pairs: a true winner against a true loser. -/
def CrossTierPair {Candidate : Type*} [DecidableEq Candidate]
    (winnerSet : Finset Candidate) : Type _ :=
  {pair : Candidate × Candidate // pair.1 ∈ winnerSet ∧ pair.2 ∉ winnerSet}

namespace CrossTierPair

variable {Candidate : Type*} [DecidableEq Candidate]
variable {winnerSet : Finset Candidate}

instance instFintype {Candidate : Type*} [Fintype Candidate]
    [DecidableEq Candidate] (winnerSet : Finset Candidate) :
    Fintype (CrossTierPair winnerSet) := by
  classical
  unfold CrossTierPair
  infer_instance

/-- Higher-tier endpoint of a cross-tier pair. -/
def hi (pair : CrossTierPair winnerSet) : Candidate := pair.1.1

/-- Lower-tier endpoint of a cross-tier pair. -/
def lo (pair : CrossTierPair winnerSet) : Candidate := pair.1.2

@[simp] theorem hi_mem (pair : CrossTierPair winnerSet) :
    pair.hi ∈ winnerSet := pair.2.1

@[simp] theorem lo_not_mem (pair : CrossTierPair winnerSet) :
    pair.lo ∉ winnerSet := pair.2.2

end CrossTierPair

/-- The number of cross-tier W-selection pairs is at most `M^2`. -/
theorem crossTierPair_card_le_candidate_card_sq
    {Candidate : Type*} [Fintype Candidate] [DecidableEq Candidate]
    (winnerSet : Finset Candidate) :
    Fintype.card (CrossTierPair winnerSet) ≤ Fintype.card Candidate ^ 2 := by
  have hsub :
      Fintype.card (CrossTierPair winnerSet) ≤
        Fintype.card (Candidate × Candidate) := by
    simpa [CrossTierPair] using
      (Fintype.card_subtype_le
        (fun pair : Candidate × Candidate =>
          pair.1 ∈ winnerSet ∧ pair.2 ∉ winnerSet))
  simpa [Fintype.card_prod, pow_two] using hsub

/--
Pointwise W-selection cross-tier Chernoff sum bound in the source's coarse
`M^2` form.
-/
theorem crossTierScoreGapErrorSum_le_candidate_card_sq_mul_exp_of_nonpos_duals
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (winnerSet : Finset Candidate)
    (dual : CrossTierPair winnerSet → ℝ) {targetRate : ℝ}
    (hdual : ∀ pair, dual pair ≤ 0)
    (hrate :
      ∀ pair,
        targetRate ≤
          -(finiteLogMGF law
            (fun signal => score pair.hi signal - score pair.lo signal)
            (dual pair)))
    (n : ℕ) :
    (∑ pair : CrossTierPair winnerSet,
      finiteScoreGapPairwiseErrorProb law score pair.hi pair.lo n) ≤
      (Fintype.card Candidate : ℝ) ^ 2 *
        Real.exp (-(n : ℝ) * targetRate) := by
  have hsum :=
    finiteRelevantScoreGapErrorSum_le_card_mul_exp_of_nonpos_duals
      (Pair := CrossTierPair winnerSet)
      (law := law) (score := score)
      (hi := fun pair : CrossTierPair winnerSet => pair.hi)
      (lo := fun pair : CrossTierPair winnerSet => pair.lo)
      (dual := dual) (targetRate := targetRate)
      hdual hrate n
  have hcard_real :
      (Fintype.card (CrossTierPair winnerSet) : ℝ) ≤
        (Fintype.card Candidate : ℝ) ^ 2 := by
    exact_mod_cast crossTierPair_card_le_candidate_card_sq winnerSet
  exact hsum.trans
    (mul_le_mul_of_nonneg_right hcard_real (Real.exp_pos _).le)

/-- Total score of a candidate in an iid sample. -/
def iidSampleCandidateScore
    {Candidate Signal : Type*} {n : ℕ}
    (score : Candidate → Signal → ℝ) (sample : Fin n → Signal)
    (candidate : Candidate) : ℝ :=
  ∑ voter : Fin n, score candidate (sample voter)

/--
A selected finite set is score-top-ranked if every selected candidate has
score at least every unselected candidate.
-/
def ScoreTopSelectedSet
    {Candidate : Type*} [DecidableEq Candidate]
    (score : Candidate → ℝ) (selected : Finset Candidate) : Prop :=
  ∀ {inside outside : Candidate},
    inside ∈ selected → outside ∉ selected → score outside ≤ score inside

/--
For any finite candidate universe and reference W-set, some selected set of
the same cardinality is score-top-ranked.  The proof chooses a cardinality-W
set maximizing total score and swaps any lower-scoring selected candidate with
a higher-scoring unselected candidate to contradict maximality.
-/
theorem exists_scoreTopSelectedSet_card_eq
    {Candidate : Type*} [Fintype Candidate] [DecidableEq Candidate]
    (score : Candidate → ℝ) (reference : Finset Candidate) :
    ∃ selected : Finset Candidate,
      selected.card = reference.card ∧ ScoreTopSelectedSet score selected := by
  classical
  let family : Finset (Finset Candidate) :=
    (Finset.univ : Finset (Finset Candidate)).filter
      (fun s => s.card = reference.card)
  have hfamily_nonempty : family.Nonempty := by
    refine ⟨reference, ?_⟩
    simp [family]
  obtain ⟨selected, hselected_mem, hselected_sup⟩ :=
    Finset.exists_mem_eq_sup'
      (s := family)
      (H := hfamily_nonempty)
      (f := fun s : Finset Candidate => ∑ c ∈ s, score c)
  have hselected_card : selected.card = reference.card := by
    simpa [family] using hselected_mem
  have hmax :
      ∀ t : Finset Candidate,
        t.card = reference.card →
          (∑ c ∈ t, score c) ≤ ∑ c ∈ selected, score c := by
    intro t ht
    have ht_mem : t ∈ family := by
      simp [family, ht]
    have hle :
        (∑ c ∈ t, score c) ≤
          family.sup' hfamily_nonempty
            (fun s : Finset Candidate => ∑ c ∈ s, score c) :=
      Finset.le_sup'
        (s := family)
        (f := fun s : Finset Candidate => ∑ c ∈ s, score c)
        ht_mem
    simpa [hselected_sup] using hle
  refine ⟨selected, hselected_card, ?_⟩
  intro inside outside hinside houtside
  by_contra hnot
  have hlt : score inside < score outside := lt_of_not_ge hnot
  let swapped : Finset Candidate := insert outside (selected.erase inside)
  have houtside_erase : outside ∉ selected.erase inside := by
    simp [houtside]
  have hswapped_card : swapped.card = reference.card := by
    have hcard_selected :
        (selected.erase inside).card + 1 = selected.card :=
      Finset.card_erase_add_one hinside
    have hcard_swapped :
        swapped.card = (selected.erase inside).card + 1 := by
      simp [swapped, houtside_erase]
    omega
  have hswapped_sum :
      (∑ c ∈ swapped, score c) =
        (∑ c ∈ selected, score c) - score inside + score outside := by
    have hselected_sum :
        (∑ c ∈ selected, score c) =
          (∑ c ∈ selected.erase inside, score c) + score inside := by
      rw [← Finset.sum_erase_add _ _ hinside]
    have hswap_sum :
        (∑ c ∈ swapped, score c) =
          score outside + ∑ c ∈ selected.erase inside, score c := by
      simp [swapped, houtside_erase]
    rw [hswap_sum, hselected_sum]
    ring
  have hmax_swapped := hmax swapped hswapped_card
  rw [hswapped_sum] at hmax_swapped
  linarith

/--
Chosen score-top set with the same cardinality as the reference W-set.  This
is a deterministic noncomputable tie-breaking device for source-facing
selection statements.
-/
noncomputable def scoreTopSelectedSetOfCard
    {Candidate : Type*} [Fintype Candidate] [DecidableEq Candidate]
    (score : Candidate → ℝ) (reference : Finset Candidate) : Finset Candidate :=
  Classical.choose (exists_scoreTopSelectedSet_card_eq score reference)

@[simp] theorem scoreTopSelectedSetOfCard_card
    {Candidate : Type*} [Fintype Candidate] [DecidableEq Candidate]
    (score : Candidate → ℝ) (reference : Finset Candidate) :
    (scoreTopSelectedSetOfCard score reference).card = reference.card :=
  (Classical.choose_spec
    (exists_scoreTopSelectedSet_card_eq score reference)).1

theorem scoreTopSelectedSetOfCard_top
    {Candidate : Type*} [Fintype Candidate] [DecidableEq Candidate]
    (score : Candidate → ℝ) (reference : Finset Candidate) :
    ScoreTopSelectedSet score (scoreTopSelectedSetOfCard score reference) :=
  (Classical.choose_spec
    (exists_scoreTopSelectedSet_card_eq score reference)).2

/--
If a score-top-ranked selected set has the correct cardinality but is not the
true winner set, then some true winner is weakly beaten by some true loser.
-/
theorem exists_crossTier_score_error_of_wrong_scoreTopSelectedSet
    {Candidate : Type*} [DecidableEq Candidate]
    (score : Candidate → ℝ) (winnerSet selected : Finset Candidate)
    (hcard : selected.card = winnerSet.card)
    (htop : ScoreTopSelectedSet score selected)
    (hwrong : selected ≠ winnerSet) :
    ∃ pair : CrossTierPair winnerSet, score pair.hi ≤ score pair.lo := by
  classical
  have hnot_winner_subset_selected : ¬ winnerSet ⊆ selected := by
    intro hsubset
    have heq : winnerSet = selected := by
      exact Finset.eq_of_subset_of_card_le hsubset (by simpa [hcard])
    exact hwrong heq.symm
  rcases Finset.not_subset.mp hnot_winner_subset_selected with
    ⟨hi, hhi_winner, hhi_not_selected⟩
  have hnot_selected_subset_winner : ¬ selected ⊆ winnerSet := by
    intro hsubset
    have heq : selected = winnerSet := by
      exact Finset.eq_of_subset_of_card_le hsubset (by simpa [hcard])
    exact hwrong heq
  rcases Finset.not_subset.mp hnot_selected_subset_winner with
    ⟨lo, hlo_selected, hlo_not_winner⟩
  refine ⟨⟨(hi, lo), hhi_winner, hlo_not_winner⟩, ?_⟩
  exact htop hlo_selected hhi_not_selected

/-- Probability that the score-top selection differs from the true winner set. -/
def scoreTopSelectionErrorProb
    {Candidate Signal : Type*} [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (winnerSet : Finset Candidate)
    (selected : (n : ℕ) → (Fin n → Signal) → Finset Candidate)
    (n : ℕ) : ℝ :=
  AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProduct (Fin n) Signal law)
    (fun sample => selected n sample ≠ winnerSet)

/--
Probability that at least one cumulative tier-prefix selected set differs from
its true prefix.  This packages a finite tiered outcome as finitely many
W-selection prefix checks.
-/
def scoreTopTieredPrefixSelectionErrorProb
    {Stage Candidate Signal : Type*} [Fintype Stage] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (targetPrefix : Stage → Finset Candidate)
    (selectedPrefix :
      Stage → (n : ℕ) → (Fin n → Signal) → Finset Candidate)
    (n : ℕ) : ℝ := by
  classical
  exact
    AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProduct (Fin n) Signal law)
      (fun sample =>
        ∃ stage : Stage, selectedPrefix stage n sample ≠ targetPrefix stage)

/--
The iid pairwise score-gap left-tail event is exactly the event that the
higher-tier candidate's sample score is weakly below the lower-tier candidate's
sample score.
-/
theorem pairwiseScoringErrorProb_eq_iidSampleCandidateScore_le
    {Candidate Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Candidate) (n : ℕ) :
    pairwiseScoringErrorProb law (score hi) (score lo) n =
      AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProduct (Fin n) Signal law)
        (fun sample : Fin n → Signal =>
          iidSampleCandidateScore score sample hi ≤
            iidSampleCandidateScore score sample lo) := by
  classical
  unfold pairwiseScoringErrorProb finiteIidScoreGapLeftTailProb
    finiteIidScoreLeftTailProb
  refine AppliedModelingLib.pmfProb_congr _ ?_
  intro sample
  unfold finiteIidScoreSum iidSampleCandidateScore
  rw [Finset.sum_sub_distrib]
  exact sub_nonpos

/--
Strict reverse pairwise beat probability is the complement of the reversed
weak pairwise-error event.
-/
theorem strictPairwiseScoringBeatProb_eq_one_sub_pairwiseScoringErrorProb
    {Candidate Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Candidate) (n : ℕ) :
    AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProduct (Fin n) Signal law)
        (fun sample : Fin n → Signal =>
          iidSampleCandidateScore score sample hi <
            iidSampleCandidateScore score sample lo) =
      1 - pairwiseScoringErrorProb law (score lo) (score hi) n := by
  classical
  rw [pairwiseScoringErrorProb_eq_iidSampleCandidateScore_le
    law score lo hi n]
  rw [← AppliedModelingLib.pmfProb_compl]
  refine AppliedModelingLib.pmfProb_congr _ ?_
  intro sample
  simp [not_le]

/--
If `lo` has strictly larger one-voter expected score than `hi`, then in iid
samples `lo` strictly beats `hi` with probability tending to one.
-/
theorem strictPairwiseScoringBeatProb_tendsto_one_of_expected_gap_neg
    {Candidate Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    {hi lo : Candidate}
    (hmean :
      AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal) < 0) :
    Filter.Tendsto
      (fun n : ℕ =>
        AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProduct (Fin n) Signal law)
          (fun sample : Fin n → Signal =>
            iidSampleCandidateScore score sample hi <
              iidSampleCandidateScore score sample lo))
      Filter.atTop (nhds 1) := by
  have hmean_rev :
      0 <
        AppliedModelingLib.pmfExp law
          (fun signal => score lo signal - score hi signal) := by
    rw [AppliedModelingLib.pmfExp_sub] at *
    linarith
  rcases
      pairwiseScoringError_exists_pos_expUpperBoundWithConst_of_expected_gap_pos
        law (score lo) (score hi) hmean_rev with
    ⟨rate, hrate_pos, hbound⟩
  have hzero :
      Filter.Tendsto (pairwiseScoringErrorProb law (score lo) (score hi))
        Filter.atTop (nhds 0) :=
    hbound.tendsto_zero_of_pos_rate hrate_pos
  have hcomp :
      Filter.Tendsto
        (fun n : ℕ => 1 - pairwiseScoringErrorProb law (score lo) (score hi) n)
        Filter.atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.sub hzero)
  simpa [strictPairwiseScoringBeatProb_eq_one_sub_pairwiseScoringErrorProb]
    using hcomp

/-- A sequence tending to one cannot also tend to zero. -/
theorem not_tendsto_zero_of_tendsto_one {f : ℕ → ℝ}
    (h : Filter.Tendsto f Filter.atTop (nhds 1)) :
    ¬ Filter.Tendsto f Filter.atTop (nhds 0) := by
  intro hzero
  have h10 : (1 : ℝ) = 0 := tendsto_nhds_unique h hzero
  norm_num at h10

/--
Finite union-bound bridge: the probability of selecting the wrong winner set
is at most the sum of cross-tier pairwise score-error probabilities.
-/
theorem scoreTopSelectionErrorProb_le_crossTierPairwiseError_sum
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (winnerSet : Finset Candidate)
    (selected : (n : ℕ) → (Fin n → Signal) → Finset Candidate)
    (hcard :
      ∀ n sample, (selected n sample).card = winnerSet.card)
    (htop :
      ∀ n sample,
        ScoreTopSelectedSet
          (iidSampleCandidateScore score sample) (selected n sample))
    (n : ℕ) :
    scoreTopSelectionErrorProb law score winnerSet selected n ≤
      ∑ pair : CrossTierPair winnerSet,
        pairwiseScoringErrorProb law (score pair.hi) (score pair.lo) n := by
  classical
  let μ := AppliedModelingLib.pmfProduct (Fin n) Signal law
  let pairEvent : CrossTierPair winnerSet → (Fin n → Signal) → Prop :=
    fun pair sample =>
      iidSampleCandidateScore score sample pair.hi ≤
        iidSampleCandidateScore score sample pair.lo
  have herror_subset :
      ∀ sample : Fin n → Signal,
        selected n sample ≠ winnerSet →
          ∃ pair : CrossTierPair winnerSet,
            pairEvent pair sample := by
    intro sample hwrong
    exact
      exists_crossTier_score_error_of_wrong_scoreTopSelectedSet
        (iidSampleCandidateScore score sample)
        winnerSet (selected n sample)
        (hcard n sample) (htop n sample) hwrong
  have hselection_le_union :
      scoreTopSelectionErrorProb law score winnerSet selected n ≤
        AppliedModelingLib.pmfProb μ
          (fun sample => ∃ pair : CrossTierPair winnerSet,
            pair ∈ (Finset.univ : Finset (CrossTierPair winnerSet)) ∧
              pairEvent pair sample) := by
    refine AppliedModelingLib.pmfProb_le_of_imp μ
      (fun sample => selected n sample ≠ winnerSet)
      (fun sample => ∃ pair : CrossTierPair winnerSet,
        pair ∈ (Finset.univ : Finset (CrossTierPair winnerSet)) ∧
          pairEvent pair sample) ?_
    intro sample hwrong
    rcases herror_subset sample hwrong with ⟨pair, hpair⟩
    exact ⟨pair, by simp, hpair⟩
  have hunion :
      AppliedModelingLib.pmfProb μ
          (fun sample => ∃ pair : CrossTierPair winnerSet,
            pair ∈ (Finset.univ : Finset (CrossTierPair winnerSet)) ∧
              pairEvent pair sample) ≤
        ∑ pair ∈ (Finset.univ : Finset (CrossTierPair winnerSet)),
          AppliedModelingLib.pmfProb μ (pairEvent pair) :=
    AppliedModelingLib.pmfProb_exists_mem_le_sum
      (μ := μ) (s := (Finset.univ : Finset (CrossTierPair winnerSet)))
      (p := pairEvent)
  calc
    scoreTopSelectionErrorProb law score winnerSet selected n ≤
        AppliedModelingLib.pmfProb μ
          (fun sample => ∃ pair : CrossTierPair winnerSet,
            pair ∈ (Finset.univ : Finset (CrossTierPair winnerSet)) ∧
              pairEvent pair sample) := hselection_le_union
    _ ≤ ∑ pair ∈ (Finset.univ : Finset (CrossTierPair winnerSet)),
          AppliedModelingLib.pmfProb μ (pairEvent pair) := hunion
    _ = ∑ pair : CrossTierPair winnerSet,
          AppliedModelingLib.pmfProb μ (pairEvent pair) := by simp
    _ = ∑ pair : CrossTierPair winnerSet,
          pairwiseScoringErrorProb law (score pair.hi) (score pair.lo) n := by
          refine Finset.sum_congr rfl ?_
          intro pair _
          rw [pairwiseScoringErrorProb_eq_iidSampleCandidateScore_le
            law score pair.hi pair.lo n]

/--
If the aggregate cross-tier pairwise score-error probability tends to zero,
then any score-top selected set of the correct size is asymptotically correct.
-/
theorem scoreTopSelectionErrorProb_tendsto_zero_of_crossTierPairwiseError_sum
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (winnerSet : Finset Candidate)
    (selected : (n : ℕ) → (Fin n → Signal) → Finset Candidate)
    (hcard :
      ∀ n sample, (selected n sample).card = winnerSet.card)
    (htop :
      ∀ n sample,
        ScoreTopSelectedSet
          (iidSampleCandidateScore score sample) (selected n sample))
    (hpair_tendsto :
      Filter.Tendsto
        (fun n =>
          ∑ pair : CrossTierPair winnerSet,
            pairwiseScoringErrorProb law (score pair.hi) (score pair.lo) n)
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (scoreTopSelectionErrorProb law score winnerSet selected)
      Filter.atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hpair_tendsto ?_ ?_
  · exact Filter.Eventually.of_forall (fun n =>
      AppliedModelingLib.pmfProb_nonneg (AppliedModelingLib.pmfProduct (Fin n) Signal law)
        (fun sample => selected n sample ≠ winnerSet))
  · exact Filter.Eventually.of_forall (fun n =>
      scoreTopSelectionErrorProb_le_crossTierPairwiseError_sum
        law score winnerSet selected hcard htop n)

/--
Strict reverse expected score for one true-winner/true-loser pair is enough to
make any score-top W-selector asymptotically wrong.  This is the strict
converse fragment of Proposition 1: it deliberately leaves the equality/tie
boundary to a separate argument.
-/
theorem scoreTopSelectionErrorProb_tendsto_one_of_crossTier_expected_gap_neg
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (winnerSet : Finset Candidate)
    (selected : (n : ℕ) → (Fin n → Signal) → Finset Candidate)
    {hi lo : Candidate}
    (hhi : hi ∈ winnerSet) (hlo : lo ∉ winnerSet)
    (htop :
      ∀ n sample,
        ScoreTopSelectedSet
          (iidSampleCandidateScore score sample) (selected n sample))
    (hmean :
      AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal) < 0) :
    Filter.Tendsto
      (scoreTopSelectionErrorProb law score winnerSet selected)
      Filter.atTop (nhds 1) := by
  have hbeat :
      Filter.Tendsto
        (fun n : ℕ =>
          AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProduct (Fin n) Signal law)
            (fun sample : Fin n → Signal =>
              iidSampleCandidateScore score sample hi <
                iidSampleCandidateScore score sample lo))
        Filter.atTop (nhds 1) :=
    strictPairwiseScoringBeatProb_tendsto_one_of_expected_gap_neg
      law score hmean
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hbeat tendsto_const_nhds ?_ ?_
  · exact Filter.Eventually.of_forall (fun n =>
      AppliedModelingLib.pmfProb_le_of_imp
        (AppliedModelingLib.pmfProduct (Fin n) Signal law)
        (fun sample : Fin n → Signal =>
          iidSampleCandidateScore score sample hi <
            iidSampleCandidateScore score sample lo)
        (fun sample : Fin n → Signal =>
          selected n sample ≠ winnerSet)
        (by
          intro sample hstrict hselected_eq
          have hhi_selected : hi ∈ selected n sample := by
            simpa [hselected_eq] using hhi
          have hlo_not_selected : lo ∉ selected n sample := by
            simpa [hselected_eq] using hlo
          have hle :
              iidSampleCandidateScore score sample lo ≤
                iidSampleCandidateScore score sample hi :=
            htop n sample hhi_selected hlo_not_selected
          exact not_lt_of_ge hle hstrict))
  · exact Filter.Eventually.of_forall (fun n =>
      AppliedModelingLib.pmfProb_le_one (AppliedModelingLib.pmfProduct (Fin n) Signal law)
        (fun sample : Fin n → Signal => selected n sample ≠ winnerSet))

/--
Strict reverse expected score prevents score-top W-selection error from
converging to zero.
-/
theorem scoreTopSelectionErrorProb_not_tendsto_zero_of_crossTier_expected_gap_neg
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (winnerSet : Finset Candidate)
    (selected : (n : ℕ) → (Fin n → Signal) → Finset Candidate)
    {hi lo : Candidate}
    (hhi : hi ∈ winnerSet) (hlo : lo ∉ winnerSet)
    (htop :
      ∀ n sample,
        ScoreTopSelectedSet
          (iidSampleCandidateScore score sample) (selected n sample))
    (hmean :
      AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal) < 0) :
    ¬ Filter.Tendsto
      (scoreTopSelectionErrorProb law score winnerSet selected)
      Filter.atTop (nhds 0) :=
  not_tendsto_zero_of_tendsto_one
    (scoreTopSelectionErrorProb_tendsto_one_of_crossTier_expected_gap_neg
      law score winnerSet selected hhi hlo htop hmean)

/--
Finite union bound for tiered prefix outcomes: the probability that any prefix
is wrong is at most the sum of the prefix-wise W-selection error probabilities.
-/
theorem scoreTopTieredPrefixSelectionErrorProb_le_sum
    {Stage Candidate Signal : Type*} [Fintype Stage] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (targetPrefix : Stage → Finset Candidate)
    (selectedPrefix :
      Stage → (n : ℕ) → (Fin n → Signal) → Finset Candidate)
    (n : ℕ) :
    scoreTopTieredPrefixSelectionErrorProb
        law score targetPrefix selectedPrefix n ≤
      ∑ stage : Stage,
        scoreTopSelectionErrorProb law score (targetPrefix stage)
          (selectedPrefix stage) n := by
  classical
  let μ := AppliedModelingLib.pmfProduct (Fin n) Signal law
  let prefixEvent : Stage → (Fin n → Signal) → Prop :=
    fun stage sample => selectedPrefix stage n sample ≠ targetPrefix stage
  have hunion :
      AppliedModelingLib.pmfProb μ
          (fun sample =>
            ∃ stage, stage ∈ (Finset.univ : Finset Stage) ∧
              prefixEvent stage sample) ≤
        ∑ stage ∈ (Finset.univ : Finset Stage),
          AppliedModelingLib.pmfProb μ (prefixEvent stage) :=
    AppliedModelingLib.pmfProb_exists_mem_le_sum
      (μ := μ) (s := (Finset.univ : Finset Stage))
      (p := prefixEvent)
  simpa [scoreTopTieredPrefixSelectionErrorProb, scoreTopSelectionErrorProb,
    prefixEvent, μ] using hunion

/--
A single cumulative-prefix error event is contained in the event that some
tier prefix is wrong.
-/
theorem scoreTopSelectionErrorProb_le_scoreTopTieredPrefixSelectionErrorProb
    {Stage Candidate Signal : Type*} [Fintype Stage] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (targetPrefix : Stage → Finset Candidate)
    (selectedPrefix :
      Stage → (n : ℕ) → (Fin n → Signal) → Finset Candidate)
    (stage : Stage) (n : ℕ) :
    scoreTopSelectionErrorProb law score (targetPrefix stage)
        (selectedPrefix stage) n ≤
      scoreTopTieredPrefixSelectionErrorProb
        law score targetPrefix selectedPrefix n := by
  classical
  refine AppliedModelingLib.pmfProb_le_of_imp
    (AppliedModelingLib.pmfProduct (Fin n) Signal law)
    (fun sample => selectedPrefix stage n sample ≠ targetPrefix stage)
    (fun sample =>
      ∃ stage : Stage, selectedPrefix stage n sample ≠ targetPrefix stage)
    ?_
  intro sample hstage
  exact ⟨stage, hstage⟩

/--
If the finite tiered-prefix error probability tends to zero, each individual
cumulative-prefix W-selection error probability also tends to zero.
-/
theorem scoreTopSelectionErrorProb_tendsto_zero_of_tieredPrefixSelectionErrorProb
    {Stage Candidate Signal : Type*} [Fintype Stage] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (targetPrefix : Stage → Finset Candidate)
    (selectedPrefix :
      Stage → (n : ℕ) → (Fin n → Signal) → Finset Candidate)
    (stage : Stage)
    (htier :
      Filter.Tendsto
        (scoreTopTieredPrefixSelectionErrorProb
          law score targetPrefix selectedPrefix)
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (scoreTopSelectionErrorProb law score (targetPrefix stage)
        (selectedPrefix stage))
      Filter.atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds htier ?_ ?_
  · exact Filter.Eventually.of_forall (fun n =>
      AppliedModelingLib.pmfProb_nonneg (AppliedModelingLib.pmfProduct (Fin n) Signal law)
        (fun sample => selectedPrefix stage n sample ≠ targetPrefix stage))
  · exact Filter.Eventually.of_forall (fun n =>
      scoreTopSelectionErrorProb_le_scoreTopTieredPrefixSelectionErrorProb
        law score targetPrefix selectedPrefix stage n)

/--
If every cumulative tier prefix is selected correctly with probability tending
to one, then the whole finite tiered prefix outcome is selected correctly with
probability tending to one.
-/
theorem scoreTopTieredPrefixSelectionErrorProb_tendsto_zero_of_prefix_errors
    {Stage Candidate Signal : Type*} [Fintype Stage] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (targetPrefix : Stage → Finset Candidate)
    (selectedPrefix :
      Stage → (n : ℕ) → (Fin n → Signal) → Finset Candidate)
    (hprefix :
      ∀ stage : Stage,
        Filter.Tendsto
          (scoreTopSelectionErrorProb law score (targetPrefix stage)
            (selectedPrefix stage))
          Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (scoreTopTieredPrefixSelectionErrorProb
        law score targetPrefix selectedPrefix)
      Filter.atTop (nhds 0) := by
  classical
  have hsum :
      Filter.Tendsto
        (fun n =>
          ∑ stage : Stage,
            scoreTopSelectionErrorProb law score (targetPrefix stage)
              (selectedPrefix stage) n)
        Filter.atTop (nhds 0) := by
    simpa using
      tendsto_finset_sum (Finset.univ : Finset Stage)
        (fun stage _ => hprefix stage)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsum ?_ ?_
  · exact Filter.Eventually.of_forall (fun n =>
      AppliedModelingLib.pmfProb_nonneg (AppliedModelingLib.pmfProduct (Fin n) Signal law)
        (fun sample =>
          ∃ stage : Stage,
            selectedPrefix stage n sample ≠ targetPrefix stage))
  · exact Filter.Eventually.of_forall (fun n =>
      scoreTopTieredPrefixSelectionErrorProb_le_sum
        law score targetPrefix selectedPrefix n)

/--
Proposition 1 source-level selection conclusion: strict prefix dominance makes
the probability of selecting a wrong W-set tend to zero for any score-top
selection rule of the correct size.
-/
theorem prefixScoringSelectionError_tendsto_zero
    {Cut Candidate Signal : Type*} [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (diff : Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    (selected : (n : ℕ) → (Fin n → Signal) → Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (hcard :
      ∀ n sample, (selected n sample).card = winnerSet.card)
    (htop :
      ∀ n sample,
        ScoreTopSelectedSet
          (iidSampleCandidateScore
            (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
            sample)
          (selected n sample))
    (hdom :
      ∀ pair : CrossTierPair winnerSet,
        StrictTopPrefixDominance (prefixProbFromEvent law inPrefix)
          pair.hi pair.lo)
    (hdiff : ReasonablePrefixWeights diff) :
    Filter.Tendsto
      (scoreTopSelectionErrorProb law
        (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
        winnerSet selected)
      Filter.atTop (nhds 0) := by
  refine
    scoreTopSelectionErrorProb_tendsto_zero_of_crossTierPairwiseError_sum
      law (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
      winnerSet selected hcard htop ?_
  simpa using
    prefixScoringRelevantPairAggregateError_tendsto_zero
      (law := law) (diff := diff) (inPrefix := inPrefix)
      (hi := fun pair : CrossTierPair winnerSet => pair.hi)
      (lo := fun pair : CrossTierPair winnerSet => pair.lo)
      (pairWeight := fun _pair : CrossTierPair winnerSet => (1 : ℝ))
      (by intro pair; norm_num)
      hdom hdiff

/--
Source-shaped Proposition 1 selection conclusion using the natural cross-tier
predicate induced by the true W-set.
-/
theorem prefixScoringSelectionError_tendsto_zero_on
    {Cut Candidate Signal : Type*} [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (diff : Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    (selected : (n : ℕ) → (Fin n → Signal) → Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (hcard :
      ∀ n sample, (selected n sample).card = winnerSet.card)
    (htop :
      ∀ n sample,
        ScoreTopSelectedSet
          (iidSampleCandidateScore
            (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
            sample)
          (selected n sample))
    (hdom :
      StrictTopPrefixDominanceOn (prefixProbFromEvent law inPrefix)
        (fun hi lo => hi ∈ winnerSet ∧ lo ∉ winnerSet))
    (hdiff : ReasonablePrefixWeights diff) :
    Filter.Tendsto
      (scoreTopSelectionErrorProb law
        (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
        winnerSet selected)
      Filter.atTop (nhds 0) :=
  prefixScoringSelectionError_tendsto_zero
    law diff inPrefix winnerSet selected hcard htop
    (fun pair => hdom pair.hi pair.lo ⟨pair.hi_mem, pair.lo_not_mem⟩)
    hdiff

/--
Strict reverse expected prefix score for one true-winner/true-loser pair makes
any score-top W-selector asymptotically wrong.  This is the source-shaped
strict converse fragment for Proposition 1; equality/tie boundaries are not
claimed here.
-/
theorem prefixScoringSelectionError_tendsto_one_of_reverse_prefix_expected_score
    {Cut Candidate Signal : Type*} [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (diff : Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    (selected : (n : ℕ) → (Fin n → Signal) → Finset Candidate)
    {hi lo : Candidate}
    (hhi : hi ∈ winnerSet) (hlo : lo ∉ winnerSet)
    (htop :
      ∀ n sample,
        ScoreTopSelectedSet
          (iidSampleCandidateScore
            (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
            sample)
          (selected n sample))
    (hreverse :
      prefixExpectedScore diff (prefixProbFromEvent law inPrefix) hi <
        prefixExpectedScore diff (prefixProbFromEvent law inPrefix) lo) :
    Filter.Tendsto
      (scoreTopSelectionErrorProb law
        (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
        winnerSet selected)
      Filter.atTop (nhds 1) := by
  have hmean :
      AppliedModelingLib.pmfExp law
          (fun signal =>
            prefixScoreFromEvent diff inPrefix hi signal -
              prefixScoreFromEvent diff inPrefix lo signal) < 0 := by
    rw [AppliedModelingLib.pmfExp_sub,
      pmfExp_prefixScoreFromEvent_eq_prefixExpectedScore,
      pmfExp_prefixScoreFromEvent_eq_prefixExpectedScore]
    exact sub_neg.mpr hreverse
  exact
    scoreTopSelectionErrorProb_tendsto_one_of_crossTier_expected_gap_neg
      law
      (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
      winnerSet selected hhi hlo htop hmean

/--
Strict reverse expected prefix score prevents source-shaped score-top
W-selection error from converging to zero.
-/
theorem prefixScoringSelectionError_not_tendsto_zero_of_reverse_prefix_expected_score
    {Cut Candidate Signal : Type*} [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (diff : Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    (selected : (n : ℕ) → (Fin n → Signal) → Finset Candidate)
    {hi lo : Candidate}
    (hhi : hi ∈ winnerSet) (hlo : lo ∉ winnerSet)
    (htop :
      ∀ n sample,
        ScoreTopSelectedSet
          (iidSampleCandidateScore
            (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
            sample)
          (selected n sample))
    (hreverse :
      prefixExpectedScore diff (prefixProbFromEvent law inPrefix) hi <
        prefixExpectedScore diff (prefixProbFromEvent law inPrefix) lo) :
    ¬ Filter.Tendsto
      (scoreTopSelectionErrorProb law
        (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
        winnerSet selected)
      Filter.atTop (nhds 0) :=
  not_tendsto_zero_of_tendsto_one
    (prefixScoringSelectionError_tendsto_one_of_reverse_prefix_expected_score
      law diff inPrefix winnerSet selected hhi hlo htop hreverse)

/--
Canonical Proposition 1 selection conclusion: strict prefix dominance for each
true-winner/true-loser pair implies that the internally chosen score-top W-set
has vanishing probability of being wrong.  The selected set and its
cardinality/topness witnesses are constructed in Lean by finite maximization.
-/
theorem prefixScoringCanonicalSelectionError_tendsto_zero
    {Cut Candidate Signal : Type*} [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (diff : Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (hdom :
      ∀ pair : CrossTierPair winnerSet,
        StrictTopPrefixDominance (prefixProbFromEvent law inPrefix)
          pair.hi pair.lo)
    (hdiff : ReasonablePrefixWeights diff) :
    Filter.Tendsto
      (scoreTopSelectionErrorProb law
        (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
        winnerSet
        (fun n sample =>
          scoreTopSelectedSetOfCard
            (iidSampleCandidateScore
              (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
              sample)
            winnerSet))
      Filter.atTop (nhds 0) :=
  prefixScoringSelectionError_tendsto_zero
    law diff inPrefix winnerSet
    (fun n sample =>
      scoreTopSelectedSetOfCard
        (iidSampleCandidateScore
          (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
          sample)
        winnerSet)
    (fun n sample =>
      scoreTopSelectedSetOfCard_card
        (iidSampleCandidateScore
          (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
          sample)
        winnerSet)
    (fun n sample =>
      scoreTopSelectedSetOfCard_top
        (iidSampleCandidateScore
          (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
          sample)
        winnerSet)
    hdom hdiff

/--
Canonical Proposition 1 selection conclusion: strict top-prefix dominance over
the W-set's natural cross-tier predicate implies that the internally chosen
score-top W-set has vanishing probability of being wrong.  The selected set
and its cardinality/topness witnesses are constructed in Lean by finite
maximization.
-/
theorem prefixScoringCanonicalSelectionError_tendsto_zero_on
    {Cut Candidate Signal : Type*} [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (diff : Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (hdom :
      StrictTopPrefixDominanceOn (prefixProbFromEvent law inPrefix)
        (fun hi lo => hi ∈ winnerSet ∧ lo ∉ winnerSet))
    (hdiff : ReasonablePrefixWeights diff) :
    Filter.Tendsto
      (scoreTopSelectionErrorProb law
        (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
        winnerSet
        (fun n sample =>
          scoreTopSelectedSetOfCard
            (iidSampleCandidateScore
              (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
              sample)
            winnerSet))
      Filter.atTop (nhds 0) :=
  prefixScoringSelectionError_tendsto_zero_on
    law diff inPrefix winnerSet
    (fun n sample =>
      scoreTopSelectedSetOfCard
        (iidSampleCandidateScore
          (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
          sample)
        winnerSet)
    (fun n sample =>
      scoreTopSelectedSetOfCard_card
        (iidSampleCandidateScore
          (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
          sample)
        winnerSet)
    (fun n sample =>
      scoreTopSelectedSetOfCard_top
        (iidSampleCandidateScore
          (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
          sample)
        winnerSet)
    hdom hdiff

/--
Canonical score-top version of the strict reverse expected-score converse
fragment for Proposition 1.
-/
theorem prefixScoringCanonicalSelectionError_tendsto_one_of_reverse_prefix_expected_score
    {Cut Candidate Signal : Type*} [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (diff : Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    {hi lo : Candidate}
    (hhi : hi ∈ winnerSet) (hlo : lo ∉ winnerSet)
    (hreverse :
      prefixExpectedScore diff (prefixProbFromEvent law inPrefix) hi <
        prefixExpectedScore diff (prefixProbFromEvent law inPrefix) lo) :
    Filter.Tendsto
      (scoreTopSelectionErrorProb law
        (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
        winnerSet
        (fun n sample =>
          scoreTopSelectedSetOfCard
            (iidSampleCandidateScore
              (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
              sample)
            winnerSet))
      Filter.atTop (nhds 1) :=
  prefixScoringSelectionError_tendsto_one_of_reverse_prefix_expected_score
    law diff inPrefix winnerSet
    (fun n sample =>
      scoreTopSelectedSetOfCard
        (iidSampleCandidateScore
          (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
          sample)
        winnerSet)
    hhi hlo
    (fun n sample =>
      scoreTopSelectedSetOfCard_top
        (iidSampleCandidateScore
          (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
          sample)
        winnerSet)
    hreverse

/--
Necessary weak expected-score separation for all-reasonable prefix-score
consistency: if every reasonable prefix score's canonical W-selection error
tends to zero, then every true winner weakly beats every true loser in
one-voter expected score for every reasonable prefix-score vector.
-/
theorem prefixScoringAllReasonableConsistency_implies_weak_expected_score_separation
    {Cut Candidate Signal : Type*} [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    (hall :
      ∀ diff : Cut → ℝ,
        ReasonablePrefixWeights diff →
          Filter.Tendsto
            (scoreTopSelectionErrorProb law
              (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
              winnerSet
              (fun n sample =>
                scoreTopSelectedSetOfCard
                  (iidSampleCandidateScore
                    (fun candidate =>
                      prefixScoreFromEvent diff inPrefix candidate)
                    sample)
                  winnerSet))
            Filter.atTop (nhds 0)) :
    ∀ diff : Cut → ℝ,
      ReasonablePrefixWeights diff →
        ∀ hi lo : Candidate,
          hi ∈ winnerSet →
            lo ∉ winnerSet →
              prefixExpectedScore diff (prefixProbFromEvent law inPrefix) lo ≤
                prefixExpectedScore diff (prefixProbFromEvent law inPrefix) hi := by
  intro diff hdiff hi lo hhi hlo
  by_contra hnot
  have hreverse :
      prefixExpectedScore diff (prefixProbFromEvent law inPrefix) hi <
        prefixExpectedScore diff (prefixProbFromEvent law inPrefix) lo :=
    lt_of_not_ge hnot
  have hbad :
      ¬ Filter.Tendsto
        (scoreTopSelectionErrorProb law
          (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
          winnerSet
          (fun n sample =>
            scoreTopSelectedSetOfCard
              (iidSampleCandidateScore
                (fun candidate => prefixScoreFromEvent diff inPrefix candidate)
                sample)
              winnerSet))
        Filter.atTop (nhds 0) :=
    not_tendsto_zero_of_tendsto_one
      (prefixScoringCanonicalSelectionError_tendsto_one_of_reverse_prefix_expected_score
        law diff inPrefix winnerSet hhi hlo hreverse)
  exact hbad (hall diff hdiff)

/--
Source-shaped Proposition 1 forward direction for the paper's finite ranking
model and W-selection goal.  If every true winner has strictly larger
top-prefix probability than every true loser at every prefix cut, then every
reasonable ranking-prefix scoring rule's canonical score-top W-set is
asymptotically correct.
-/
theorem rankingPrefixScoringCanonicalSelectionError_tendsto_zero_on
    {n : ℕ}
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (diff : RankingProperPrefixCut n → ℝ)
    (winnerSet : Finset (AppliedModelingLib.SocialChoice.Ranking.Candidate n))
    [Nonempty (CrossTierPair winnerSet)]
    (hdom :
      ∀ hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n,
        hi ∈ winnerSet →
          lo ∉ winnerSet →
            ∀ cut : RankingProperPrefixCut n,
              rankingTopPrefixProb law lo cut <
                rankingTopPrefixProb law hi cut)
    (hdiff : ReasonablePrefixWeights diff) :
    Filter.Tendsto
      (scoreTopSelectionErrorProb law
        (rankingPrefixScore diff)
        winnerSet
        (fun voters sample =>
          scoreTopSelectedSetOfCard
            (iidSampleCandidateScore (rankingPrefixScore diff) sample)
            winnerSet))
      Filter.atTop (nhds 0) := by
  simpa [rankingPrefixScore] using
    (prefixScoringCanonicalSelectionError_tendsto_zero_on
      (Cut := RankingProperPrefixCut n)
      (Candidate := AppliedModelingLib.SocialChoice.Ranking.Candidate n)
      (Signal := AppliedModelingLib.SocialChoice.Ranking.Ranking n)
      (law := law)
      (diff := diff)
      (inPrefix := rankingInTopPrefix)
      (winnerSet := winnerSet)
      (hdom := by
        intro hi lo hcross cut
        exact hdom hi lo hcross.1 hcross.2 cut)
      (hdiff := hdiff))

/--
Source-shaped Proposition 1 forward direction for any deterministic
score-top W-set selector of the correct cardinality, specialized to the
paper's finite ranking law and proper top-prefix cuts.
-/
theorem rankingPrefixScoringSelectionError_tendsto_zero_on
    {n : ℕ}
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (diff : RankingProperPrefixCut n → ℝ)
    (winnerSet : Finset (AppliedModelingLib.SocialChoice.Ranking.Candidate n))
    (selected :
      (voters : ℕ) →
        (Fin voters → AppliedModelingLib.SocialChoice.Ranking.Ranking n) →
          Finset (AppliedModelingLib.SocialChoice.Ranking.Candidate n))
    [Nonempty (CrossTierPair winnerSet)]
    (hcard :
      ∀ voters sample, (selected voters sample).card = winnerSet.card)
    (htop :
      ∀ voters sample,
        ScoreTopSelectedSet
          (iidSampleCandidateScore (rankingPrefixScore diff) sample)
          (selected voters sample))
    (hdom :
      ∀ hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n,
        hi ∈ winnerSet →
          lo ∉ winnerSet →
            ∀ cut : RankingProperPrefixCut n,
              rankingTopPrefixProb law lo cut <
                rankingTopPrefixProb law hi cut)
    (hdiff : ReasonablePrefixWeights diff) :
    Filter.Tendsto
      (scoreTopSelectionErrorProb law
        (rankingPrefixScore diff)
        winnerSet selected)
      Filter.atTop (nhds 0) := by
  simpa [rankingPrefixScore] using
    (prefixScoringSelectionError_tendsto_zero_on
      (Cut := RankingProperPrefixCut n)
      (Candidate := AppliedModelingLib.SocialChoice.Ranking.Candidate n)
      (Signal := AppliedModelingLib.SocialChoice.Ranking.Ranking n)
      (law := law)
      (diff := diff)
      (inPrefix := rankingInTopPrefix)
      (winnerSet := winnerSet)
      (selected := selected)
      (hcard := hcard)
      (htop := by
        simpa [rankingPrefixScore] using htop)
      (hdom := by
        intro hi lo hcross cut
        exact hdom hi lo hcross.1 hcross.2 cut)
      (hdiff := hdiff))

/--
Ranking-law strict reverse expected-score converse fragment for the canonical
score-top W-selector.
-/
theorem rankingPrefixScoringCanonicalSelectionError_tendsto_one_of_reverse_prefix_expected_score
    {n : ℕ}
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (diff : RankingProperPrefixCut n → ℝ)
    (winnerSet : Finset (AppliedModelingLib.SocialChoice.Ranking.Candidate n))
    {hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n}
    (hhi : hi ∈ winnerSet) (hlo : lo ∉ winnerSet)
    (hreverse :
      prefixExpectedScore diff (rankingTopPrefixProb law) hi <
        prefixExpectedScore diff (rankingTopPrefixProb law) lo) :
    Filter.Tendsto
      (scoreTopSelectionErrorProb law
        (rankingPrefixScore diff)
        winnerSet
        (fun voters sample =>
          scoreTopSelectedSetOfCard
            (iidSampleCandidateScore (rankingPrefixScore diff) sample)
            winnerSet))
      Filter.atTop (nhds 1) := by
  simpa [rankingPrefixScore, rankingTopPrefixProb] using
    (prefixScoringCanonicalSelectionError_tendsto_one_of_reverse_prefix_expected_score
      (Cut := RankingProperPrefixCut n)
      (Candidate := AppliedModelingLib.SocialChoice.Ranking.Candidate n)
      (Signal := AppliedModelingLib.SocialChoice.Ranking.Ranking n)
      (law := law)
      (diff := diff)
      (inPrefix := rankingInTopPrefix)
      (winnerSet := winnerSet)
      (hhi := hhi)
      (hlo := hlo)
      (hreverse := by
        simpa [rankingTopPrefixProb] using hreverse))

/--
If a lower candidate has strictly larger probability of appearing in one
proper top prefix than a true winner, then the corresponding indicator prefix
score makes the canonical W-selector asymptotically wrong.  This is the
strict, non-tie converse case behind Proposition 1's ranking-law finite
algebra.
-/
theorem rankingPrefixScoringCanonicalSelectionError_tendsto_one_of_reverse_top_prefix_prob
    {n : ℕ}
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (winnerSet : Finset (AppliedModelingLib.SocialChoice.Ranking.Candidate n))
    {hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n}
    (hhi : hi ∈ winnerSet) (hlo : lo ∉ winnerSet)
    {cut : RankingProperPrefixCut n}
    (hreverse :
      rankingTopPrefixProb law hi cut <
        rankingTopPrefixProb law lo cut) :
    Filter.Tendsto
      (scoreTopSelectionErrorProb law
        (rankingPrefixScore
          (fun k : RankingProperPrefixCut n =>
            if k = cut then (1 : ℝ) else 0))
        winnerSet
        (fun voters sample =>
          scoreTopSelectedSetOfCard
            (iidSampleCandidateScore
              (rankingPrefixScore
                (fun k : RankingProperPrefixCut n =>
                  if k = cut then (1 : ℝ) else 0))
              sample)
            winnerSet))
      Filter.atTop (nhds 1) := by
  exact
    rankingPrefixScoringCanonicalSelectionError_tendsto_one_of_reverse_prefix_expected_score
      law
      (fun k : RankingProperPrefixCut n => if k = cut then (1 : ℝ) else 0)
      winnerSet hhi hlo
      (by
        simpa [prefixExpectedScore] using hreverse)

/--
The strict reversed-prefix case is not asymptotically correct under the
corresponding indicator prefix score.
-/
theorem rankingPrefixScoringCanonicalSelectionError_not_tendsto_zero_of_reverse_top_prefix_prob
    {n : ℕ}
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (winnerSet : Finset (AppliedModelingLib.SocialChoice.Ranking.Candidate n))
    {hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n}
    (hhi : hi ∈ winnerSet) (hlo : lo ∉ winnerSet)
    {cut : RankingProperPrefixCut n}
    (hreverse :
      rankingTopPrefixProb law hi cut <
        rankingTopPrefixProb law lo cut) :
    ¬ Filter.Tendsto
      (scoreTopSelectionErrorProb law
        (rankingPrefixScore
          (fun k : RankingProperPrefixCut n =>
            if k = cut then (1 : ℝ) else 0))
        winnerSet
        (fun voters sample =>
          scoreTopSelectedSetOfCard
            (iidSampleCandidateScore
              (rankingPrefixScore
                (fun k : RankingProperPrefixCut n =>
                  if k = cut then (1 : ℝ) else 0))
              sample)
            winnerSet))
      Filter.atTop (nhds 0) :=
  not_tendsto_zero_of_tendsto_one
    (rankingPrefixScoringCanonicalSelectionError_tendsto_one_of_reverse_top_prefix_prob
      law winnerSet hhi hlo hreverse)

/--
A strict reversed top-prefix probability gives an admissible indicator prefix
score witnessing failure of asymptotic correctness.
-/
theorem rankingPrefixScoringCanonicalSelectionError_indicator_reasonable_and_not_tendsto_zero_of_reverse_top_prefix_prob
    {n : ℕ}
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (winnerSet : Finset (AppliedModelingLib.SocialChoice.Ranking.Candidate n))
    {hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n}
    (hhi : hi ∈ winnerSet) (hlo : lo ∉ winnerSet)
    {cut : RankingProperPrefixCut n}
    (hreverse :
      rankingTopPrefixProb law hi cut <
        rankingTopPrefixProb law lo cut) :
    ReasonablePrefixWeights
        (fun k : RankingProperPrefixCut n =>
          if k = cut then (1 : ℝ) else 0) ∧
      ¬ Filter.Tendsto
        (scoreTopSelectionErrorProb law
          (rankingPrefixScore
            (fun k : RankingProperPrefixCut n =>
              if k = cut then (1 : ℝ) else 0))
          winnerSet
          (fun voters sample =>
            scoreTopSelectedSetOfCard
              (iidSampleCandidateScore
                (rankingPrefixScore
                  (fun k : RankingProperPrefixCut n =>
                    if k = cut then (1 : ℝ) else 0))
                sample)
              winnerSet))
        Filter.atTop (nhds 0) :=
  ⟨ReasonablePrefixWeights.indicator cut,
    rankingPrefixScoringCanonicalSelectionError_not_tendsto_zero_of_reverse_top_prefix_prob
      law winnerSet hhi hlo hreverse⟩

/--
Strict reversal at one top-prefix cut refutes all-reasonable-score
asymptotic consistency: the indicator prefix score is reasonable and is not
consistent.
-/
theorem rankingStrictReverseTopPrefixProb_not_all_reasonable_prefix_score_consistency
    {n : ℕ}
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (winnerSet : Finset (AppliedModelingLib.SocialChoice.Ranking.Candidate n))
    {hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n}
    (hhi : hi ∈ winnerSet) (hlo : lo ∉ winnerSet)
    {cut : RankingProperPrefixCut n}
    (hreverse :
      rankingTopPrefixProb law hi cut <
        rankingTopPrefixProb law lo cut) :
    ¬ (∀ diff : RankingProperPrefixCut n → ℝ,
      ReasonablePrefixWeights diff →
        Filter.Tendsto
          (scoreTopSelectionErrorProb law
            (rankingPrefixScore diff)
            winnerSet
            (fun voters sample =>
              scoreTopSelectedSetOfCard
                (iidSampleCandidateScore (rankingPrefixScore diff) sample)
                winnerSet))
          Filter.atTop (nhds 0)) := by
  intro hall
  let diff : RankingProperPrefixCut n → ℝ :=
    fun k => if k = cut then (1 : ℝ) else 0
  have hbad :=
    rankingPrefixScoringCanonicalSelectionError_indicator_reasonable_and_not_tendsto_zero_of_reverse_top_prefix_prob
      law winnerSet hhi hlo hreverse
  exact hbad.2 (hall diff hbad.1)

/--
Necessary weak dominance fragment for Proposition 1: if every reasonable
ranking-prefix score has vanishing canonical W-selection error, then no lower
candidate can have a strictly larger probability at any top-prefix cut than a
true winner.
-/
theorem rankingAllReasonablePrefixScoreConsistency_implies_weak_top_prefix_dominance
    {n : ℕ}
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (winnerSet : Finset (AppliedModelingLib.SocialChoice.Ranking.Candidate n))
    (hall :
      ∀ diff : RankingProperPrefixCut n → ℝ,
        ReasonablePrefixWeights diff →
          Filter.Tendsto
            (scoreTopSelectionErrorProb law
              (rankingPrefixScore diff)
              winnerSet
              (fun voters sample =>
                scoreTopSelectedSetOfCard
                  (iidSampleCandidateScore (rankingPrefixScore diff) sample)
                  winnerSet))
            Filter.atTop (nhds 0)) :
    ∀ hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n,
      hi ∈ winnerSet →
        lo ∉ winnerSet →
          ∀ cut : RankingProperPrefixCut n,
            rankingTopPrefixProb law lo cut ≤
              rankingTopPrefixProb law hi cut := by
  intro hi lo hhi hlo cut
  by_contra hnot
  have hreverse :
      rankingTopPrefixProb law hi cut <
        rankingTopPrefixProb law lo cut := lt_of_not_ge hnot
  exact
    rankingStrictReverseTopPrefixProb_not_all_reasonable_prefix_score_consistency
      law winnerSet hhi hlo hreverse hall

/--
Paper-shaped Proposition 1 sandwich currently closed in Lean: the source's
strict cross-tier top-prefix condition is sufficient for all-reasonable-score
consistency, and all-reasonable-score consistency is sufficient for weak
top-prefix dominance. Exact cross-tier equality is outside the source strict
condition; finite-sample random tie-breaking and within-tier ties are separate
from this strict target-ranking/tier hypothesis.
-/
theorem rankingPrefixScoreConsistency_strict_forward_weak_necessary
    {n : ℕ}
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (winnerSet : Finset (AppliedModelingLib.SocialChoice.Ranking.Candidate n))
    [Nonempty (CrossTierPair winnerSet)] :
    ((∀ hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n,
      hi ∈ winnerSet →
        lo ∉ winnerSet →
          ∀ cut : RankingProperPrefixCut n,
            rankingTopPrefixProb law lo cut <
              rankingTopPrefixProb law hi cut) →
      ∀ diff : RankingProperPrefixCut n → ℝ,
        ReasonablePrefixWeights diff →
          Filter.Tendsto
            (scoreTopSelectionErrorProb law
              (rankingPrefixScore diff)
              winnerSet
              (fun voters sample =>
                scoreTopSelectedSetOfCard
                  (iidSampleCandidateScore (rankingPrefixScore diff) sample)
                  winnerSet))
            Filter.atTop (nhds 0)) ∧
      ((∀ diff : RankingProperPrefixCut n → ℝ,
        ReasonablePrefixWeights diff →
          Filter.Tendsto
            (scoreTopSelectionErrorProb law
              (rankingPrefixScore diff)
              winnerSet
              (fun voters sample =>
                scoreTopSelectedSetOfCard
                  (iidSampleCandidateScore (rankingPrefixScore diff) sample)
                  winnerSet))
            Filter.atTop (nhds 0)) →
        ∀ hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n,
          hi ∈ winnerSet →
            lo ∉ winnerSet →
              ∀ cut : RankingProperPrefixCut n,
                rankingTopPrefixProb law lo cut ≤
                  rankingTopPrefixProb law hi cut) :=
  ⟨by
      intro hdom diff hdiff
      exact
        rankingPrefixScoringCanonicalSelectionError_tendsto_zero_on
          law diff winnerSet hdom hdiff,
    rankingAllReasonablePrefixScoreConsistency_implies_weak_top_prefix_dominance
      law winnerSet⟩

/--
Source-shaped Proposition 1 iff in the source's strict cross-tier case. The
reverse stochastic direction already gives weak top-prefix dominance; under
the no-cross-tier-equality hypothesis corresponding to the source strict
top-prefix condition, weak dominance upgrades to strict dominance.
-/
theorem rankingStrictPrefixDominance_iff_all_reasonable_prefix_score_consistency_of_no_cross_tier_prefix_ties
    {n : ℕ}
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (winnerSet : Finset (AppliedModelingLib.SocialChoice.Ranking.Candidate n))
    [Nonempty (CrossTierPair winnerSet)]
    (hNoTie :
      ∀ hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n,
        hi ∈ winnerSet →
          lo ∉ winnerSet →
            ∀ cut : RankingProperPrefixCut n,
              rankingTopPrefixProb law lo cut ≠
                rankingTopPrefixProb law hi cut) :
    (∀ hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n,
      hi ∈ winnerSet →
        lo ∉ winnerSet →
          ∀ cut : RankingProperPrefixCut n,
            rankingTopPrefixProb law lo cut <
              rankingTopPrefixProb law hi cut) ↔
      (∀ diff : RankingProperPrefixCut n → ℝ,
        ReasonablePrefixWeights diff →
          Filter.Tendsto
            (scoreTopSelectionErrorProb law
              (rankingPrefixScore diff)
              winnerSet
              (fun voters sample =>
                scoreTopSelectedSetOfCard
                  (iidSampleCandidateScore (rankingPrefixScore diff) sample)
                  winnerSet))
            Filter.atTop (nhds 0)) := by
  constructor
  · intro hdom
    exact
      (rankingPrefixScoreConsistency_strict_forward_weak_necessary
        law winnerSet).1 hdom
  · intro hall hi lo hhi hlo cut
    have hweak :
        rankingTopPrefixProb law lo cut ≤
          rankingTopPrefixProb law hi cut :=
      rankingAllReasonablePrefixScoreConsistency_implies_weak_top_prefix_dominance
        law winnerSet hall hi lo hhi hlo cut
    exact lt_of_le_of_ne hweak (hNoTie hi lo hhi hlo cut)

/--
Source-shaped finite Proposition 1 ranking-law algebra: strict top-prefix
dominance over the W-set's cross-tier pairs is equivalent to separation by
every reasonable ranking-prefix score rule.
-/
theorem rankingStrictPrefixDominance_iff_all_reasonable_prefix_score_separation
    {n : ℕ}
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (winnerSet : Finset (AppliedModelingLib.SocialChoice.Ranking.Candidate n)) :
    (∀ hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n,
      hi ∈ winnerSet →
        lo ∉ winnerSet →
          ∀ cut : RankingProperPrefixCut n,
            rankingTopPrefixProb law lo cut <
              rankingTopPrefixProb law hi cut) ↔
    (∀ diff : RankingProperPrefixCut n → ℝ,
      ReasonablePrefixWeights diff →
        ∀ hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n,
          hi ∈ winnerSet →
            lo ∉ winnerSet →
              prefixExpectedScore diff (rankingTopPrefixProb law) lo <
                prefixExpectedScore diff (rankingTopPrefixProb law) hi) := by
  classical
  have hiff :=
    strictTopPrefixDominanceOn_iff_allReasonablePrefixScoresSeparateOn
      (topPrefixProb := rankingTopPrefixProb law)
      (crossTier := fun hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n =>
        hi ∈ winnerSet ∧ lo ∉ winnerSet)
  constructor
  · intro hdom diff hdiff hi lo hhi hlo
    have hall :
        AllReasonablePrefixScoresSeparateOn (rankingTopPrefixProb law)
          (fun hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n =>
            hi ∈ winnerSet ∧ lo ∉ winnerSet) := by
      exact hiff.1 (by
        intro hi lo hcross cut
        exact hdom hi lo hcross.1 hcross.2 cut)
    exact hall hi lo ⟨hhi, hlo⟩ diff hdiff
  · intro hall hi lo hhi hlo cut
    have hsep :
        AllReasonablePrefixScoresSeparateOn (rankingTopPrefixProb law)
          (fun hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n =>
            hi ∈ winnerSet ∧ lo ∉ winnerSet) := by
      intro hi lo hcross diff hdiff
      exact hall diff hdiff hi lo hcross.1 hcross.2
    exact hiff.2 hsep hi lo ⟨hhi, hlo⟩ cut

/--
Source-shaped finite Proposition 1 ranking-law algebra for tiered goals:
strict top-prefix dominance across every cumulative target prefix is
equivalent to separation across every cumulative target prefix by every
reasonable ranking-prefix score rule.
-/
theorem rankingTieredStrictPrefixDominance_iff_all_reasonable_prefix_score_separation
    {n Stage : ℕ}
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (targetPrefix :
      Fin Stage → Finset (AppliedModelingLib.SocialChoice.Ranking.Candidate n)) :
    (∀ stage : Fin Stage,
      ∀ hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n,
        hi ∈ targetPrefix stage →
          lo ∉ targetPrefix stage →
            ∀ cut : RankingProperPrefixCut n,
              rankingTopPrefixProb law lo cut <
                rankingTopPrefixProb law hi cut) ↔
    (∀ diff : RankingProperPrefixCut n → ℝ,
      ReasonablePrefixWeights diff →
        ∀ stage : Fin Stage,
          ∀ hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n,
            hi ∈ targetPrefix stage →
              lo ∉ targetPrefix stage →
                prefixExpectedScore diff (rankingTopPrefixProb law) lo <
                  prefixExpectedScore diff (rankingTopPrefixProb law) hi) := by
  constructor
  · intro hdom diff hdiff stage hi lo hhi hlo
    exact
      (rankingStrictPrefixDominance_iff_all_reasonable_prefix_score_separation
        law (targetPrefix stage)).1
        (hdom stage) diff hdiff hi lo hhi hlo
  · intro hall stage hi lo hhi hlo cut
    exact
      (rankingStrictPrefixDominance_iff_all_reasonable_prefix_score_separation
        law (targetPrefix stage)).2
        (fun diff hdiff hi lo hhi hlo =>
          hall diff hdiff stage hi lo hhi hlo)
        hi lo hhi hlo cut

/--
Source-shaped Proposition 1 forward direction over all reasonable
ranking-prefix scoring rules, specialized to the paper's finite ranking law
and W-selection goal.
-/
theorem rankingStrictPrefixDominance_implies_all_reasonable_prefix_score_consistency
    {n : ℕ}
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (winnerSet : Finset (AppliedModelingLib.SocialChoice.Ranking.Candidate n))
    [Nonempty (CrossTierPair winnerSet)]
    (hdom :
      ∀ hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n,
        hi ∈ winnerSet →
          lo ∉ winnerSet →
            ∀ cut : RankingProperPrefixCut n,
              rankingTopPrefixProb law lo cut <
                rankingTopPrefixProb law hi cut) :
    ∀ diff : RankingProperPrefixCut n → ℝ,
      ReasonablePrefixWeights diff →
        Filter.Tendsto
          (scoreTopSelectionErrorProb law
            (rankingPrefixScore diff)
            winnerSet
            (fun voters sample =>
              scoreTopSelectedSetOfCard
                (iidSampleCandidateScore (rankingPrefixScore diff) sample)
                winnerSet))
          Filter.atTop (nhds 0) := by
  intro diff hdiff
  exact
    rankingPrefixScoringCanonicalSelectionError_tendsto_zero_on
      law diff winnerSet hdom hdiff

/--
Source-shaped Proposition 1 forward direction from the equivalent finite
expected-score separation condition: if every reasonable ranking-prefix score
rule separates each true-winner/true-loser pair in one-voter expectation, then
every reasonable ranking-prefix score rule's canonical score-top W-set is
asymptotically correct.
-/
theorem rankingPrefixScoreSeparation_implies_all_reasonable_prefix_score_consistency
    {n : ℕ}
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (winnerSet : Finset (AppliedModelingLib.SocialChoice.Ranking.Candidate n))
    [Nonempty (CrossTierPair winnerSet)]
    (hsep :
      ∀ diff : RankingProperPrefixCut n → ℝ,
        ReasonablePrefixWeights diff →
          ∀ hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n,
            hi ∈ winnerSet →
              lo ∉ winnerSet →
                prefixExpectedScore diff (rankingTopPrefixProb law) lo <
                  prefixExpectedScore diff (rankingTopPrefixProb law) hi) :
    ∀ diff : RankingProperPrefixCut n → ℝ,
      ReasonablePrefixWeights diff →
        Filter.Tendsto
          (scoreTopSelectionErrorProb law
            (rankingPrefixScore diff)
            winnerSet
            (fun voters sample =>
              scoreTopSelectedSetOfCard
                (iidSampleCandidateScore (rankingPrefixScore diff) sample)
                winnerSet))
          Filter.atTop (nhds 0) := by
  have hdom :
      ∀ hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n,
        hi ∈ winnerSet →
          lo ∉ winnerSet →
            ∀ cut : RankingProperPrefixCut n,
              rankingTopPrefixProb law lo cut <
                rankingTopPrefixProb law hi cut :=
    (rankingStrictPrefixDominance_iff_all_reasonable_prefix_score_separation
      law winnerSet).2 hsep
  exact
    rankingStrictPrefixDominance_implies_all_reasonable_prefix_score_consistency
      law winnerSet hdom

/--
Source-shaped Proposition 1 forward direction for finite tiered goals,
represented by a finite family of cumulative true tier-prefix sets.  If strict
ranking-law top-prefix dominance holds across every cumulative prefix cut,
then every reasonable ranking-prefix score rule recovers every tier prefix
asymptotically.
-/
theorem rankingPrefixScoringCanonicalTieredPrefixSelectionError_tendsto_zero
    {n Stage : ℕ}
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (diff : RankingProperPrefixCut n → ℝ)
    (targetPrefix :
      Fin Stage → Finset (AppliedModelingLib.SocialChoice.Ranking.Candidate n))
    (hnonempty :
      ∀ stage : Fin Stage, Nonempty (CrossTierPair (targetPrefix stage)))
    (hdom :
      ∀ stage : Fin Stage,
        ∀ hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n,
          hi ∈ targetPrefix stage →
            lo ∉ targetPrefix stage →
              ∀ cut : RankingProperPrefixCut n,
                rankingTopPrefixProb law lo cut <
                  rankingTopPrefixProb law hi cut)
    (hdiff : ReasonablePrefixWeights diff) :
    Filter.Tendsto
      (scoreTopTieredPrefixSelectionErrorProb law
        (rankingPrefixScore diff)
        targetPrefix
        (fun stage voters sample =>
          scoreTopSelectedSetOfCard
            (iidSampleCandidateScore (rankingPrefixScore diff) sample)
            (targetPrefix stage)))
      Filter.atTop (nhds 0) := by
  refine
    scoreTopTieredPrefixSelectionErrorProb_tendsto_zero_of_prefix_errors
      law (rankingPrefixScore diff) targetPrefix
      (fun stage voters sample =>
        scoreTopSelectedSetOfCard
          (iidSampleCandidateScore (rankingPrefixScore diff) sample)
          (targetPrefix stage))
      ?_
  intro stage
  letI : Nonempty (CrossTierPair (targetPrefix stage)) := hnonempty stage
  exact
    rankingPrefixScoringCanonicalSelectionError_tendsto_zero_on
      law diff (targetPrefix stage) (hdom stage) hdiff

/--
Source-shaped Proposition 1 tiered forward direction from the equivalent
finite expected-score separation condition.  If every reasonable ranking-prefix
score rule separates every cumulative target-prefix boundary in expectation,
then every reasonable ranking-prefix score rule recovers all target prefixes
asymptotically.
-/
theorem rankingPrefixScoreSeparation_implies_all_reasonable_tiered_prefix_score_consistency
    {n Stage : ℕ}
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (targetPrefix :
      Fin Stage → Finset (AppliedModelingLib.SocialChoice.Ranking.Candidate n))
    (hnonempty :
      ∀ stage : Fin Stage, Nonempty (CrossTierPair (targetPrefix stage)))
    (hsep :
      ∀ diff : RankingProperPrefixCut n → ℝ,
        ReasonablePrefixWeights diff →
          ∀ stage : Fin Stage,
            ∀ hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n,
              hi ∈ targetPrefix stage →
                lo ∉ targetPrefix stage →
                  prefixExpectedScore diff (rankingTopPrefixProb law) lo <
                    prefixExpectedScore diff (rankingTopPrefixProb law) hi) :
    ∀ diff : RankingProperPrefixCut n → ℝ,
      ReasonablePrefixWeights diff →
        Filter.Tendsto
          (scoreTopTieredPrefixSelectionErrorProb law
            (rankingPrefixScore diff)
            targetPrefix
            (fun stage voters sample =>
              scoreTopSelectedSetOfCard
                (iidSampleCandidateScore (rankingPrefixScore diff) sample)
                (targetPrefix stage)))
          Filter.atTop (nhds 0) := by
  have hdom :
      ∀ stage : Fin Stage,
        ∀ hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n,
          hi ∈ targetPrefix stage →
            lo ∉ targetPrefix stage →
              ∀ cut : RankingProperPrefixCut n,
                rankingTopPrefixProb law lo cut <
                  rankingTopPrefixProb law hi cut :=
    (rankingTieredStrictPrefixDominance_iff_all_reasonable_prefix_score_separation
      law targetPrefix).2 hsep
  intro diff hdiff
  exact
    rankingPrefixScoringCanonicalTieredPrefixSelectionError_tendsto_zero
      law diff targetPrefix hnonempty hdom hdiff

/--
Source-shaped Proposition 1 tiered iff away from exact cross-tier prefix ties.
The forward direction is the finite tiered consistency bridge.  Conversely,
vanishing error for every reasonable prefix score implies weak top-prefix
dominance on each cumulative target prefix; the no-tie hypothesis upgrades
weak dominance to the strict source condition.
-/
theorem rankingTieredStrictPrefixDominance_iff_all_reasonable_tiered_prefix_score_consistency_of_no_cross_tier_prefix_ties
    {n Stage : ℕ}
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (targetPrefix :
      Fin Stage → Finset (AppliedModelingLib.SocialChoice.Ranking.Candidate n))
    (hnonempty :
      ∀ stage : Fin Stage, Nonempty (CrossTierPair (targetPrefix stage)))
    (hNoTie :
      ∀ stage : Fin Stage,
        ∀ hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n,
          hi ∈ targetPrefix stage →
            lo ∉ targetPrefix stage →
              ∀ cut : RankingProperPrefixCut n,
                rankingTopPrefixProb law lo cut ≠
                  rankingTopPrefixProb law hi cut) :
    (∀ stage : Fin Stage,
      ∀ hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n,
        hi ∈ targetPrefix stage →
          lo ∉ targetPrefix stage →
            ∀ cut : RankingProperPrefixCut n,
              rankingTopPrefixProb law lo cut <
                rankingTopPrefixProb law hi cut) ↔
      (∀ diff : RankingProperPrefixCut n → ℝ,
        ReasonablePrefixWeights diff →
          Filter.Tendsto
            (scoreTopTieredPrefixSelectionErrorProb law
              (rankingPrefixScore diff)
              targetPrefix
              (fun stage voters sample =>
                scoreTopSelectedSetOfCard
                  (iidSampleCandidateScore (rankingPrefixScore diff) sample)
                  (targetPrefix stage)))
            Filter.atTop (nhds 0)) := by
  constructor
  · intro hdom diff hdiff
    exact
      rankingPrefixScoringCanonicalTieredPrefixSelectionError_tendsto_zero
        law diff targetPrefix hnonempty hdom hdiff
  · intro hall stage hi lo hhi hlo cut
    have hallStage :
        ∀ diff : RankingProperPrefixCut n → ℝ,
          ReasonablePrefixWeights diff →
            Filter.Tendsto
              (scoreTopSelectionErrorProb law
                (rankingPrefixScore diff)
                (targetPrefix stage)
                (fun voters sample =>
                  scoreTopSelectedSetOfCard
                    (iidSampleCandidateScore (rankingPrefixScore diff) sample)
                    (targetPrefix stage)))
              Filter.atTop (nhds 0) := by
      intro diff hdiff
      exact
        scoreTopSelectionErrorProb_tendsto_zero_of_tieredPrefixSelectionErrorProb
          law (rankingPrefixScore diff) targetPrefix
          (fun stage voters sample =>
            scoreTopSelectedSetOfCard
              (iidSampleCandidateScore (rankingPrefixScore diff) sample)
              (targetPrefix stage))
          stage (hall diff hdiff)
    have hweak :
        rankingTopPrefixProb law lo cut ≤
          rankingTopPrefixProb law hi cut :=
      rankingAllReasonablePrefixScoreConsistency_implies_weak_top_prefix_dominance
        law (targetPrefix stage) hallStage hi lo hhi hlo cut
    exact lt_of_le_of_ne hweak (hNoTie stage hi lo hhi hlo cut)

/--
Exact pairwise finite iid score-gap certificate for a common voter law.  This
is the Proposition 2 Cramer endpoint packaged for the Proposition 4 finite
aggregation theorem.
-/
def finiteScoreGapPairwiseRateCertificate
    {Candidate Signal : Type*} [Fintype Candidate] [Fintype Signal]
    [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (cramer :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapCramerCertificate law (score hi) (score lo)) :
    PairwiseErrorRateCertificate Candidate :=
  finiteIidPairwiseScoreGapRateCertificate law score cramer

/--
Exact pairwise finite iid score-gap certificate for one-sided boundary pairs:
if every positive-mass score gap is nonnegative and zero-gap probability is
positive, the pairwise error probability has rate `-log pZero`.
-/
def finiteScoreGapPairwiseRateCertificate_of_support_nonneg_zero_gap_prob
    {Candidate Signal : Type*} [Fintype Candidate] [Fintype Signal]
    [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (pZero : Candidate → Candidate → ℝ)
    (hsupport :
      ∀ hi lo signal, 0 < (law signal).toReal →
        0 ≤ score hi signal - score lo signal)
    (hZeroProb :
      ∀ hi lo,
        AppliedModelingLib.pmfProb law
            (fun signal => score hi signal - score lo signal = 0) =
          pZero hi lo)
    (hZero_pos : ∀ hi lo, 0 < pZero hi lo) :
    PairwiseErrorRateCertificate Candidate where
  errorProb := finiteScoreGapPairwiseErrorProb law score
  rate := fun hi lo => -Real.log (pZero hi lo)
  has_rate := by
    intro hi lo
    simpa [finiteScoreGapPairwiseErrorProb] using
      pairwiseScoringError_exponentialRateCertificate_of_support_nonneg_zero_gap_prob
        law (score hi) (score lo)
        (fun signal hmass => hsupport hi lo signal hmass)
        (hZeroProb hi lo) (hZero_pos hi lo)

/--
Exact pairwise finite iid score-gap certificate from explicit per-pair
left-tail path lower certificates plus the Chernoff upper-bound side.
-/
def finiteScoreGapPairwiseRateCertificate_of_pathLower
    {Candidate Signal : Type*} [Fintype Candidate] [Fintype Signal]
    [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hupper :
      ∀ hi lo : Candidate, ∀ targetRate,
        targetRate < finiteIidPairwiseScoreGapChernoffRate law score hi lo →
          HasExpUpperBoundWithConst
            (finiteScoreGapPairwiseErrorProb law score hi lo) targetRate)
    (lower :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapPathLowerCertificate law (score hi) (score lo))
    (hrate :
      ∀ hi lo : Candidate,
        -Real.log (lower hi lo).base =
          finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    PairwiseErrorRateCertificate Candidate :=
  finiteScoreGapPairwiseRateCertificate law score
    (fun hi lo =>
      finiteIidScoreGapCramerCertificate_of_pathLower
        (μ := law) (hiScore := score hi) (loScore := score lo)
        (fun targetRate htarget => by
          simpa [finiteScoreGapPairwiseErrorProb, pairwiseScoringErrorProb,
            finiteIidScoreGapLeftTailProb] using
            hupper hi lo targetRate htarget)
        (lower hi lo)
        (by
          simpa [finiteIidPairwiseScoreGapChernoffRate] using
            hrate hi lo))

/--
Exact pairwise finite iid score-gap certificate from explicit per-pair direct
tail-probability lower certificates plus the Chernoff upper-bound side.
-/
def finiteScoreGapPairwiseRateCertificate_of_tailLower
    {Candidate Signal : Type*} [Fintype Candidate] [Fintype Signal]
    [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hupper :
      ∀ hi lo : Candidate, ∀ targetRate,
        targetRate < finiteIidPairwiseScoreGapChernoffRate law score hi lo →
          HasExpUpperBoundWithConst
            (finiteScoreGapPairwiseErrorProb law score hi lo) targetRate)
    (lower :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapTailLowerCertificate law (score hi) (score lo))
    (hrate :
      ∀ hi lo : Candidate,
        -Real.log (lower hi lo).base =
          finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    PairwiseErrorRateCertificate Candidate :=
  finiteScoreGapPairwiseRateCertificate law score
    (fun hi lo =>
      finiteIidScoreGapCramerCertificate_of_tailLower
        (μ := law) (hiScore := score hi) (loScore := score lo)
        (fun targetRate htarget => by
          simpa [finiteScoreGapPairwiseErrorProb, pairwiseScoringErrorProb,
            finiteIidScoreGapLeftTailProb] using
            hupper hi lo targetRate htarget)
        (lower hi lo)
        (by
          simpa [finiteIidPairwiseScoreGapChernoffRate] using
            hrate hi lo))

/--
Exact pairwise finite iid score-gap certificate from explicit per-pair
empirical-type lower certificates plus the Chernoff upper-bound side.
-/
def finiteScoreGapPairwiseRateCertificate_of_empiricalTypeLower
    {Candidate Signal : Type*} [Fintype Candidate] [Fintype Signal]
    [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hupper :
      ∀ hi lo : Candidate, ∀ targetRate,
        targetRate < finiteIidPairwiseScoreGapChernoffRate law score hi lo →
          HasExpUpperBoundWithConst
            (finiteScoreGapPairwiseErrorProb law score hi lo) targetRate)
    (lower :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapEmpiricalTypeLowerCertificate law (score hi) (score lo))
    (hrate :
      ∀ hi lo : Candidate,
        -Real.log (lower hi lo).base =
          finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    PairwiseErrorRateCertificate Candidate :=
  finiteScoreGapPairwiseRateCertificate_of_tailLower
    law score hupper
    (fun hi lo => (lower hi lo).toTailLowerCertificate)
    hrate

/--
Exact pairwise finite iid score-gap certificate from explicit per-pair
bucket/type lower certificates plus the Chernoff upper-bound side.
-/
def finiteScoreGapPairwiseRateCertificate_of_bucketLower
    {Candidate Signal : Type*} [Fintype Candidate] [Fintype Signal]
    [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hupper :
      ∀ hi lo : Candidate, ∀ targetRate,
        targetRate < finiteIidPairwiseScoreGapChernoffRate law score hi lo →
          HasExpUpperBoundWithConst
            (finiteScoreGapPairwiseErrorProb law score hi lo) targetRate)
    (lower :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapBucketLowerCertificate law (score hi) (score lo))
    (hrate :
      ∀ hi lo : Candidate,
        -Real.log (lower hi lo).base =
          finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    PairwiseErrorRateCertificate Candidate :=
  finiteScoreGapPairwiseRateCertificate_of_pathLower
    law score hupper
    (fun hi lo => (lower hi lo).toPathLowerCertificate)
    hrate

/--
Exact pairwise finite iid score-gap certificate from explicit per-pair
empirical count-vector lower certificates plus the Chernoff upper-bound side.
-/
def finiteScoreGapPairwiseRateCertificate_of_countVectorLower
    {Candidate Signal : Type*} [Fintype Candidate] [Fintype Signal]
    [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hupper :
      ∀ hi lo : Candidate, ∀ targetRate,
        targetRate < finiteIidPairwiseScoreGapChernoffRate law score hi lo →
          HasExpUpperBoundWithConst
            (finiteScoreGapPairwiseErrorProb law score hi lo) targetRate)
    (lower :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapCountVectorLowerCertificate law (score hi) (score lo))
    (hrate :
      ∀ hi lo : Candidate,
        -Real.log (lower hi lo).base =
          finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    PairwiseErrorRateCertificate Candidate :=
  finiteScoreGapPairwiseRateCertificate_of_pathLower
    law score hupper
    (fun hi lo => (lower hi lo).toPathLowerCertificate)
    hrate

/--
Exact pairwise finite iid score-gap certificate from per-pair count-vector
lower-bound witnesses available at every strictly slower target rate, with
each pair's Chernoff upper side discharged by nonnegative expected score gap
and positive-mass atoms on both sides.
-/
def finiteScoreGapPairwiseRateCertificate_of_countVectorLower_witnesses_of_mean_nonneg_pos_neg_atoms
    {Candidate Signal : Type*} [Fintype Candidate] [Fintype Signal]
    [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0)
    (lower :
      ∀ hi lo : Candidate, ∀ targetRate,
        finiteIidPairwiseScoreGapChernoffRate law score hi lo < targetRate →
          ∃ C : FiniteIidScoreGapCountVectorLowerCertificate
              law (score hi) (score lo),
            -Real.log C.base < targetRate) :
    PairwiseErrorRateCertificate Candidate :=
  finiteScoreGapPairwiseRateCertificate law score
    (fun hi lo =>
      finiteIidScoreGapCramerCertificate_of_countVectorLower_witnesses_of_pos_neg_atoms
        law (score hi) (score lo) (hmean hi lo)
        (hmassPos hi lo) (hgapPos hi lo)
        (hmassNeg hi lo) (hgapNeg hi lo)
        (fun targetRate htarget => lower hi lo targetRate (by
          simpa [finiteIidPairwiseScoreGapChernoffRate] using htarget)))

/--
Exact pairwise finite iid score-gap certificate from per-pair periodic
empirical-count witnesses available at every strictly slower target rate.
-/
def finiteScoreGapPairwiseRateCertificate_of_periodicCountVectorLower_witnesses_of_mean_nonneg_pos_neg_atoms
    {Candidate Signal : Type*} [Fintype Candidate] [Fintype Signal]
    [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0)
    (lower :
      ∀ hi lo : Candidate, ∀ targetRate,
        finiteIidPairwiseScoreGapChernoffRate law score hi lo < targetRate →
        ∃ (Q : ℕ) (q : Signal → ℕ) (filler : Signal) (base : ℝ),
          0 < Q ∧
          (∑ signal : Signal, q signal = Q) ∧
          (∑ signal : Signal,
            (q signal : ℝ) * (score hi signal - score lo signal) ≤ 0) ∧
          score hi filler - score lo filler ≤ 0 ∧
          0 < base ∧
          base ^ Q ≤
            ∏ signal : Signal, (law signal).toReal ^ q signal ∧
          0 < (law filler).toReal ∧
          -Real.log base < targetRate) :
    PairwiseErrorRateCertificate Candidate :=
  finiteScoreGapPairwiseRateCertificate law score
    (fun hi lo =>
      finiteIidScoreGapCramerCertificate_of_periodic_countVectorLower_witnesses_of_pos_neg_atoms
        law (score hi) (score lo) (hmean hi lo)
        (hmassPos hi lo) (hgapPos hi lo)
        (hmassNeg hi lo) (hgapNeg hi lo)
        (fun targetRate htarget => lower hi lo targetRate (by
          simpa [finiteIidPairwiseScoreGapChernoffRate] using htarget)))

/--
Exact pairwise finite iid score-gap certificate from per-pair empirical-type
lower-bound witnesses available at every strictly slower target rate.  This is
the entropy-aware method-of-types certificate surface for finite score gaps.
-/
def finiteScoreGapPairwiseRateCertificate_of_empiricalTypeLower_witnesses_of_mean_nonneg_pos_neg_atoms
    {Candidate Signal : Type*} [Fintype Candidate] [Fintype Signal]
    [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0)
    (lower :
      ∀ hi lo : Candidate, ∀ targetRate,
        finiteIidPairwiseScoreGapChernoffRate law score hi lo < targetRate →
          ∃ C : FiniteIidScoreGapEmpiricalTypeLowerCertificate
              law (score hi) (score lo),
            -Real.log C.base < targetRate) :
    PairwiseErrorRateCertificate Candidate :=
  finiteScoreGapPairwiseRateCertificate law score
    (fun hi lo =>
      finiteIidScoreGapCramerCertificate_of_empiricalTypeLower_witnesses_of_pos_neg_atoms
        law (score hi) (score lo) (hmean hi lo)
        (hmassPos hi lo) (hgapPos hi lo)
        (hmassNeg hi lo) (hgapNeg hi lo)
        (fun targetRate htarget => lower hi lo targetRate (by
          simpa [finiteIidPairwiseScoreGapChernoffRate] using htarget)))

/--
Exact pairwise finite iid score-gap certificate from explicit per-pair
empirical-type lower certificates, with each pair's Chernoff upper side
discharged by nonnegative expected score gap and positive-mass atoms on both
sides of the score gap.
-/
def finiteScoreGapPairwiseRateCertificate_of_empiricalTypeLower_of_mean_nonneg_pos_neg_atoms
    {Candidate Signal : Type*} [Fintype Candidate] [Fintype Signal]
    [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0)
    (lower :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapEmpiricalTypeLowerCertificate law (score hi) (score lo))
    (hrate :
      ∀ hi lo : Candidate,
        -Real.log (lower hi lo).base =
          finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    PairwiseErrorRateCertificate Candidate :=
  finiteScoreGapPairwiseRateCertificate_of_empiricalTypeLower
    law score
    (fun hi lo targetRate htarget => by
      simpa [finiteScoreGapPairwiseErrorProb, pairwiseScoringErrorProb,
        finiteIidScoreGapLeftTailProb] using
        finiteIidScoreGapLeftTail_upperBounds_of_lt_chernoffRate
          law (score hi) (score lo) (hmean hi lo)
          (finiteScoreGapLogMGF_bddBelow_of_pos_neg_atoms
            law (score hi) (score lo)
            (hmassPos hi lo) (hgapPos hi lo)
            (hmassNeg hi lo) (hgapNeg hi lo))
          targetRate htarget)
    lower hrate

/--
Exact pairwise finite iid score-gap certificate from per-pair stationary
finite exponential tilts, using the support-preserving method-of-types lower
bound.
-/
def finiteScoreGapPairwiseRateCertificate_of_stationary_tilted_modal_log_support
    {Candidate Signal : Type*} [Fintype Candidate] [Fintype Signal]
    [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0)
    (z : Candidate → Candidate → ℝ)
    (hstationary :
      ∀ hi lo : Candidate,
        (∑ signal : Signal,
          (law signal).toReal *
            ((score hi signal - score lo signal) *
              Real.exp
                (z hi lo * (score hi signal - score lo signal)))) = 0) :
    PairwiseErrorRateCertificate Candidate where
  errorProb := finiteScoreGapPairwiseErrorProb law score
  rate := finiteIidPairwiseScoreGapChernoffRate law score
  has_rate := by
    intro hi lo
    simpa [finiteScoreGapPairwiseErrorProb, pairwiseScoringErrorProb,
      finiteIidPairwiseScoreGapChernoffRate, pairwiseScoringRate,
      finiteScoreGapChernoffRate] using
      pairwiseScoringError_exponentialRateCertificate_of_stationary_tilted_modal_log_support
        law (score hi) (score lo) (hmean hi lo)
        (hmassPos hi lo) (hgapPos hi lo)
        (hmassNeg hi lo) (hgapNeg hi lo)
        (z := z hi lo) (hstationary hi lo)

/--
Exact pairwise finite iid score-gap certificate from nonnegative per-pair
expected gaps and positive-mass atoms on both sides.  The stationary
exponential tilts are found internally for each pair.
-/
def finiteScoreGapPairwiseRateCertificate_of_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms
    {Candidate Signal : Type*} [Fintype Candidate] [Fintype Signal]
    [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0) :
    PairwiseErrorRateCertificate Candidate where
  errorProb := finiteScoreGapPairwiseErrorProb law score
  rate := finiteIidPairwiseScoreGapChernoffRate law score
  has_rate := by
    intro hi lo
    simpa [finiteScoreGapPairwiseErrorProb, pairwiseScoringErrorProb,
      finiteIidPairwiseScoreGapChernoffRate, pairwiseScoringRate,
      finiteScoreGapChernoffRate] using
      pairwiseScoringError_exponentialRateCertificate_of_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms
        law (score hi) (score lo) (hmean hi lo)
        (hmassPos hi lo) (hgapPos hi lo)
        (hmassNeg hi lo) (hgapNeg hi lo)

/--
Exact-rate certificate for a finite family of relevant ordered candidate pairs
from nonnegative per-pair expected gaps and positive-mass atoms on both sides.
The relevant-pair index avoids forcing the theorem over all ordered candidate
pairs when a paper theorem only uses boundary or cross-tier comparisons.
-/
def finiteScoreGapRelevantPairRateCertificate_of_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms
    {Pair Candidate Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    (hmean :
      ∀ pair,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score (hi pair) signal - score (lo pair) signal))
    (aPos aNeg : Pair → Signal)
    (hmassPos : ∀ pair, 0 < (law (aPos pair)).toReal)
    (hgapPos :
      ∀ pair, 0 < score (hi pair) (aPos pair) -
        score (lo pair) (aPos pair))
    (hmassNeg : ∀ pair, 0 < (law (aNeg pair)).toReal)
    (hgapNeg :
      ∀ pair, score (hi pair) (aNeg pair) -
        score (lo pair) (aNeg pair) < 0) :
    FiniteErrorRateCertificate Pair where
  errorProb :=
    fun pair => finiteScoreGapPairwiseErrorProb law score (hi pair) (lo pair)
  rate :=
    fun pair => finiteIidPairwiseScoreGapChernoffRate law score
      (hi pair) (lo pair)
  has_rate := by
    intro pair
    simpa [finiteScoreGapPairwiseErrorProb, pairwiseScoringErrorProb,
      finiteIidPairwiseScoreGapChernoffRate, pairwiseScoringRate,
      finiteScoreGapChernoffRate] using
      pairwiseScoringError_exponentialRateCertificate_of_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms
        law (score (hi pair)) (score (lo pair)) (hmean pair)
        (hmassPos pair) (hgapPos pair)
        (hmassNeg pair) (hgapNeg pair)

/--
Full-support convenience wrapper for
`finiteScoreGapPairwiseRateCertificate_of_stationary_tilted_modal_log_support`.
-/
def finiteScoreGapPairwiseRateCertificate_of_stationary_tilted_modal_log_full_support
    {Candidate Signal : Type*} [Fintype Candidate] [Fintype Signal]
    [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0)
    (_hlaw_full : ∀ signal : Signal, 0 < (law signal).toReal)
    (z : Candidate → Candidate → ℝ)
    (hstationary :
      ∀ hi lo : Candidate,
        (∑ signal : Signal,
          (law signal).toReal *
            ((score hi signal - score lo signal) *
              Real.exp
                (z hi lo * (score hi signal - score lo signal)))) = 0) :
    PairwiseErrorRateCertificate Candidate :=
  finiteScoreGapPairwiseRateCertificate_of_stationary_tilted_modal_log_support
    law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg
    z hstationary

/--
Proposition 3 source formula for K-approval: `pUp` is the probability that a
voter approves the higher-scored candidate but not the lower-scored candidate;
`pDown` is the reverse probability.
-/
def approvalPairwiseRate (pUp pDown : ℝ) : ℝ :=
  ternaryGapClosedChernoffRate pUp pDown

/-- The closed-form base inside the K-approval pairwise exponent. -/
def approvalPairwiseBase (pUp pDown : ℝ) : ℝ :=
  2 * Real.sqrt (pUp * pDown) + 1 - pUp - pDown

/--
Extended approval pairwise rate: the real-valued source formula away from the
zero-base boundary, and `⊤` when the closed-form base is zero.  This keeps
boundary no-randomization statements ordered without relying on Lean's total
real logarithm at zero.
-/
def approvalPairwiseExtendedRate (pUp pDown : ℝ) : WithTop ℝ :=
  if approvalPairwiseBase pUp pDown = 0 then
    ⊤
  else
    (approvalPairwiseRate pUp pDown : WithTop ℝ)

theorem approvalPairwiseBase_zero_down_eq_one_sub_up (pUp : ℝ) :
    approvalPairwiseBase pUp 0 = 1 - pUp := by
  simp [approvalPairwiseBase]

/-- The K-approval closed-form base is positive for a nondegenerate ternary law. -/
theorem approvalPairwiseBase_pos_of_pos_sum_le
    {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hsum : pUp + pDown ≤ 1) :
    0 < approvalPairwiseBase pUp pDown := by
  simpa [approvalPairwiseBase] using
    ternaryGap_closedExpr_pos hUp hDown hsum

theorem approvalPairwiseRate_eq_source_formula (pUp pDown : ℝ) :
    approvalPairwiseRate pUp pDown =
      -Real.log (2 * Real.sqrt (pUp * pDown) + 1 - pUp - pDown) := by
  rfl

theorem approvalPairwiseRate_eq_neg_log_base (pUp pDown : ℝ) :
    approvalPairwiseRate pUp pDown =
      -Real.log (approvalPairwiseBase pUp pDown) := by
  rfl

theorem approvalPairwiseRate_zero_down_eq_neg_log_one_sub_up (pUp : ℝ) :
    approvalPairwiseRate pUp 0 = -Real.log (1 - pUp) := by
  simp [approvalPairwiseRate, ternaryGapClosedChernoffRate]

theorem approvalPairwiseRate_zero_zero :
    approvalPairwiseRate 0 0 = 0 := by
  simp [approvalPairwiseRate, ternaryGapClosedChernoffRate]

theorem approvalPairwiseRate_zero_down_lt_of_up_lt_exp_gap
    {pUp target : ℝ}
    (hpUp : pUp < 1 - Real.exp (-target)) :
    approvalPairwiseRate pUp 0 < target := by
  have h_exp_lt : Real.exp (-target) < 1 - pUp := by
    linarith
  have hlog :
      Real.log (Real.exp (-target)) < Real.log (1 - pUp) :=
    Real.log_lt_log (Real.exp_pos (-target)) h_exp_lt
  rw [Real.log_exp] at hlog
  rw [approvalPairwiseRate_zero_down_eq_neg_log_one_sub_up]
  linarith

theorem exists_pos_up_zero_down_rate_lt
    {target : ℝ} (htarget : 0 < target) :
    ∃ pUp, 0 < pUp ∧ pUp < 1 ∧
      approvalPairwiseRate pUp 0 < target := by
  let pUp : ℝ := (1 - Real.exp (-target)) / 2
  have hexp_lt_one : Real.exp (-target) < 1 := by
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have h_exp_pos : 0 < Real.exp (-target) := Real.exp_pos _
  have hpUp_pos : 0 < pUp := by
    dsimp [pUp]
    nlinarith
  have hpUp_lt_one : pUp < 1 := by
    dsimp [pUp]
    nlinarith
  have hpUp_lt_gap : pUp < 1 - Real.exp (-target) := by
    dsimp [pUp]
    nlinarith
  exact
    ⟨pUp, hpUp_pos, hpUp_lt_one,
      approvalPairwiseRate_zero_down_lt_of_up_lt_exp_gap hpUp_lt_gap⟩

/--
The K-approval pairwise base is one minus the squared gap between square-rooted
up/down probabilities.
-/
theorem approvalPairwiseBase_eq_one_sub_sq_sqrt_sub
    {pUp pDown : ℝ} (hUp : 0 ≤ pUp) (hDown : 0 ≤ pDown) :
    approvalPairwiseBase pUp pDown =
      1 - (Real.sqrt pUp - Real.sqrt pDown) ^ 2 := by
  unfold approvalPairwiseBase
  rw [Real.sqrt_mul hUp pDown]
  calc
    2 * (Real.sqrt pUp * Real.sqrt pDown) + 1 - pUp - pDown
        = 1 -
            ((Real.sqrt pUp) ^ 2 -
              2 * Real.sqrt pUp * Real.sqrt pDown +
              (Real.sqrt pDown) ^ 2) := by
          rw [Real.sq_sqrt hUp, Real.sq_sqrt hDown]
          ring
    _ = 1 - (Real.sqrt pUp - Real.sqrt pDown) ^ 2 := by
          ring

theorem approvalPairwiseRate_self_eq_zero
    {p : ℝ} (hp : 0 ≤ p) :
    approvalPairwiseRate p p = 0 := by
  rw [approvalPairwiseRate_eq_neg_log_base,
    approvalPairwiseBase_eq_one_sub_sq_sqrt_sub hp hp]
  simp

theorem sqrt_shift_sq_le
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 ≤ ε) :
    (Real.sqrt (a + ε) - Real.sqrt a) ^ 2 ≤ ε := by
  have hsum : 0 ≤ a + ε := by
    nlinarith
  have hsq_eq :
      (Real.sqrt (a + ε) - Real.sqrt a) ^ 2 =
        2 * a + ε - 2 * Real.sqrt (a * (a + ε)) := by
    rw [sub_sq, Real.sq_sqrt hsum, Real.sq_sqrt ha]
    rw [Real.sqrt_mul ha (a + ε)]
    ring
  have hroot_ge_a : a ≤ Real.sqrt (a * (a + ε)) := by
    have hsq_le : a ^ 2 ≤ a * (a + ε) := by
      nlinarith [mul_nonneg ha hε]
    have hsqrt_a_sq : Real.sqrt (a ^ 2) = a := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ha]
    have hroot_le := Real.sqrt_le_sqrt hsq_le
    rwa [hsqrt_a_sq] at hroot_le
  rw [hsq_eq]
  nlinarith

theorem approvalPairwiseRate_shift_le_zero_down
    {a ε : ℝ}
    (ha : 0 ≤ a) (hε_nonneg : 0 ≤ ε) (hε_lt : ε < 1) :
    approvalPairwiseRate (a + ε) a ≤ approvalPairwiseRate ε 0 := by
  have hsum : 0 ≤ a + ε := by
    nlinarith
  have hbase_ge :
      approvalPairwiseBase ε 0 ≤ approvalPairwiseBase (a + ε) a := by
    rw [approvalPairwiseBase_eq_one_sub_sq_sqrt_sub hε_nonneg (by norm_num),
      approvalPairwiseBase_eq_one_sub_sq_sqrt_sub hsum ha]
    simp only [Real.sqrt_zero, sub_zero]
    rw [Real.sq_sqrt hε_nonneg]
    nlinarith [sqrt_shift_sq_le ha hε_nonneg]
  have hε_base_pos : 0 < approvalPairwiseBase ε 0 := by
    rw [approvalPairwiseBase_eq_one_sub_sq_sqrt_sub hε_nonneg (by norm_num)]
    simp only [Real.sqrt_zero, sub_zero]
    rw [Real.sq_sqrt hε_nonneg]
    nlinarith
  have hlog_le :
      Real.log (approvalPairwiseBase ε 0) ≤
        Real.log (approvalPairwiseBase (a + ε) a) :=
    Real.log_le_log hε_base_pos hbase_ge
  rw [approvalPairwiseRate_eq_neg_log_base,
    approvalPairwiseRate_eq_neg_log_base]
  linarith

theorem exists_pos_shift_rate_lt
    {a target : ℝ} (ha : 0 ≤ a) (htarget : 0 < target) :
    ∃ ε, 0 < ε ∧ ε < 1 ∧
      approvalPairwiseRate (a + ε) a < target := by
  let ε : ℝ := (1 - Real.exp (-target)) / 2
  have hexp_lt_one : Real.exp (-target) < 1 := by
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have h_exp_pos : 0 < Real.exp (-target) := Real.exp_pos _
  have hε_pos : 0 < ε := by
    dsimp [ε]
    nlinarith
  have hε_lt_one : ε < 1 := by
    dsimp [ε]
    nlinarith
  have hε_lt_gap : ε < 1 - Real.exp (-target) := by
    dsimp [ε]
    nlinarith
  refine ⟨ε, hε_pos, hε_lt_one, ?_⟩
  exact lt_of_le_of_lt
    (approvalPairwiseRate_shift_le_zero_down ha (le_of_lt hε_pos) hε_lt_one)
    (approvalPairwiseRate_zero_down_lt_of_up_lt_exp_gap hε_lt_gap)

theorem approvalPairwiseBase_tendsto_one_of_tendsto_same
    {α : Type*} {l : Filter α} {pUp pDown : α → ℝ} {p : ℝ}
    (hpUp : Filter.Tendsto pUp l (nhds p))
    (hpDown : Filter.Tendsto pDown l (nhds p))
    (hp : 0 ≤ p) :
    Filter.Tendsto
      (fun x => approvalPairwiseBase (pUp x) (pDown x))
      l (nhds 1) := by
  have hprod : Filter.Tendsto
      (fun x => pUp x * pDown x) l (nhds (p * p)) :=
    hpUp.mul hpDown
  have hsqrt_prod : Filter.Tendsto
      (fun x => Real.sqrt (pUp x * pDown x)) l (nhds p) := by
    have hsqrt_const : Real.sqrt (p * p) = p := by
      rw [← sq, Real.sqrt_sq_eq_abs, abs_of_nonneg hp]
    simpa [hsqrt_const] using
      (Real.continuous_sqrt.tendsto (p * p)).comp hprod
  have hbase :
      Filter.Tendsto
        (fun x =>
          2 * Real.sqrt (pUp x * pDown x) + 1 - pUp x - pDown x)
        l (nhds (2 * p + 1 - p - p)) :=
    (((tendsto_const_nhds.mul hsqrt_prod).add tendsto_const_nhds).sub hpUp).sub
      hpDown
  have hone : 2 * p + 1 - p - p = (1 : ℝ) := by
    ring
  simpa [approvalPairwiseBase, hone] using hbase

theorem approvalPairwiseRate_tendsto_zero_of_tendsto_same
    {α : Type*} {l : Filter α} {pUp pDown : α → ℝ} {p : ℝ}
    (hpUp : Filter.Tendsto pUp l (nhds p))
    (hpDown : Filter.Tendsto pDown l (nhds p))
    (hp : 0 ≤ p) :
    Filter.Tendsto
      (fun x => approvalPairwiseRate (pUp x) (pDown x))
      l (nhds 0) := by
  have hbase : Filter.Tendsto
      (fun x => approvalPairwiseBase (pUp x) (pDown x))
      l (nhds 1) :=
    approvalPairwiseBase_tendsto_one_of_tendsto_same hpUp hpDown hp
  have hlog : Filter.Tendsto
      (fun x => Real.log (approvalPairwiseBase (pUp x) (pDown x)))
      l (nhds 0) := by
    simpa [Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
        hbase
  have hneg := hlog.neg
  simpa [approvalPairwiseRate_eq_neg_log_base] using hneg

theorem approvalPairwiseRate_eventually_lt_of_tendsto_same
    {α : Type*} {l : Filter α} {pUp pDown : α → ℝ} {p targetRate : ℝ}
    (hpUp : Filter.Tendsto pUp l (nhds p))
    (hpDown : Filter.Tendsto pDown l (nhds p))
    (hp : 0 ≤ p)
    (htarget : 0 < targetRate) :
    ∀ᶠ x in l,
      approvalPairwiseRate (pUp x) (pDown x) < targetRate := by
  exact
    (approvalPairwiseRate_tendsto_zero_of_tendsto_same hpUp hpDown hp).eventually_lt_const
      htarget

/--
If the down-probability is strictly smaller than the up-probability, the
closed-form K-approval base is strictly below one.
-/
theorem approvalPairwiseBase_lt_one_of_down_lt_up
    {pUp pDown : ℝ}
    (hUp : 0 ≤ pUp) (hDown : 0 ≤ pDown)
    (hlt : pDown < pUp) :
    approvalPairwiseBase pUp pDown < 1 := by
  rw [approvalPairwiseBase_eq_one_sub_sq_sqrt_sub hUp hDown]
  have hsqrt_lt : Real.sqrt pDown < Real.sqrt pUp :=
    Real.sqrt_lt_sqrt hDown hlt
  have hgap_pos : 0 < Real.sqrt pUp - Real.sqrt pDown :=
    sub_pos.mpr hsqrt_lt
  have hsq_pos : 0 < (Real.sqrt pUp - Real.sqrt pDown) ^ 2 :=
    sq_pos_of_pos hgap_pos
  nlinarith

/-- For valid ternary approval probabilities, the closed-form base is in `[0,1]`. -/
theorem approvalPairwiseBase_mem_Icc_of_probabilities
    {pUp pDown : ℝ}
    (hUp : 0 ≤ pUp) (hDown : 0 ≤ pDown)
    (hsum : pUp + pDown ≤ 1) :
    0 ≤ approvalPairwiseBase pUp pDown ∧
      approvalPairwiseBase pUp pDown ≤ 1 := by
  rw [approvalPairwiseBase_eq_one_sub_sq_sqrt_sub hUp hDown]
  have hsqrt_mul_nonneg :
      0 ≤ Real.sqrt pUp * Real.sqrt pDown :=
    mul_nonneg (Real.sqrt_nonneg pUp) (Real.sqrt_nonneg pDown)
  have hsq_le_one :
      (Real.sqrt pUp - Real.sqrt pDown) ^ 2 ≤ 1 := by
    rw [sub_sq, Real.sq_sqrt hUp, Real.sq_sqrt hDown]
    nlinarith
  exact ⟨by nlinarith, by nlinarith [sq_nonneg (Real.sqrt pUp - Real.sqrt pDown)]⟩

/-- The real-valued K-approval closed-form rate is nonnegative on valid probabilities. -/
theorem approvalPairwiseRate_nonneg_of_probabilities
    {pUp pDown : ℝ}
    (hUp : 0 ≤ pUp) (hDown : 0 ≤ pDown)
    (hsum : pUp + pDown ≤ 1) :
    0 ≤ approvalPairwiseRate pUp pDown := by
  rcases approvalPairwiseBase_mem_Icc_of_probabilities hUp hDown hsum with
    ⟨hbase_nonneg, hbase_le_one⟩
  have hlog_nonpos :
      Real.log (approvalPairwiseBase pUp pDown) ≤ 0 :=
    Real.log_nonpos hbase_nonneg hbase_le_one
  rw [approvalPairwiseRate_eq_neg_log_base]
  linarith

/--
The paper's strict pairwise separation condition makes the K-approval
closed-form learning rate positive.
-/
theorem approvalPairwiseRate_pos_of_down_lt_up
    {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hsum : pUp + pDown ≤ 1)
    (hlt : pDown < pUp) :
    0 < approvalPairwiseRate pUp pDown := by
  have hbase_pos : 0 < approvalPairwiseBase pUp pDown := by
    simpa [approvalPairwiseBase] using
      ternaryGap_closedExpr_pos hUp hDown hsum
  have hbase_lt_one :
      approvalPairwiseBase pUp pDown < 1 :=
    approvalPairwiseBase_lt_one_of_down_lt_up hUp.le hDown.le hlt
  have hlog_neg :
      Real.log (approvalPairwiseBase pUp pDown) < 0 :=
    Real.log_neg hbase_pos hbase_lt_one
  rw [approvalPairwiseRate_eq_neg_log_base]
  linarith

/--
Approval-rate comparison helper: because the rate is `-log(base)`, a smaller
positive base gives a strictly larger learning rate.
-/
theorem approvalPairwiseRate_gt_of_base_lt
    {leftUp leftDown rightUp rightDown : ℝ}
    (hleft_pos : 0 < approvalPairwiseBase leftUp leftDown)
    (hright_pos : 0 < approvalPairwiseBase rightUp rightDown)
    (hbase :
      approvalPairwiseBase leftUp leftDown <
        approvalPairwiseBase rightUp rightDown) :
    approvalPairwiseRate rightUp rightDown <
      approvalPairwiseRate leftUp leftDown := by
  have hlog :
      Real.log (approvalPairwiseBase leftUp leftDown) <
        Real.log (approvalPairwiseBase rightUp rightDown) :=
    Real.log_lt_log hleft_pos hbase
  simpa [approvalPairwiseRate_eq_neg_log_base] using neg_lt_neg hlog

/-- Dual orientation of `approvalPairwiseRate_gt_of_base_lt`. -/
theorem approvalPairwiseRate_lt_of_base_gt
    {leftUp leftDown rightUp rightDown : ℝ}
    (hleft_pos : 0 < approvalPairwiseBase leftUp leftDown)
    (hright_pos : 0 < approvalPairwiseBase rightUp rightDown)
    (hbase :
      approvalPairwiseBase rightUp rightDown <
        approvalPairwiseBase leftUp leftDown) :
    approvalPairwiseRate leftUp leftDown <
      approvalPairwiseRate rightUp rightDown :=
  approvalPairwiseRate_gt_of_base_lt hright_pos hleft_pos hbase

theorem approvalPairwiseRate_zero_down_lt_of_base_lt_one_sub_up
    {pUp betterUp betterDown : ℝ}
    (hbetter_base_pos : 0 < approvalPairwiseBase betterUp betterDown)
    (hbase_lt : approvalPairwiseBase betterUp betterDown < 1 - pUp) :
    approvalPairwiseRate pUp 0 <
      approvalPairwiseRate betterUp betterDown := by
  have hzero_base_pos : 0 < approvalPairwiseBase pUp 0 := by
    simpa [approvalPairwiseBase_zero_down_eq_one_sub_up] using
      lt_trans hbetter_base_pos hbase_lt
  exact approvalPairwiseRate_lt_of_base_gt
    hzero_base_pos hbetter_base_pos
    (by simpa [approvalPairwiseBase_zero_down_eq_one_sub_up] using hbase_lt)

/--
Approval-base monotonicity in the source-paper direction: if a comparison has
weakly larger favorable mass and weakly smaller unfavorable mass, while both
up/down gaps are correctly oriented, then its closed-form base is weakly
smaller.
-/
theorem approvalPairwiseBase_le_of_up_ge_down_le
    {up down betterUp betterDown : ℝ}
    (hUp : 0 ≤ up) (hDown : 0 ≤ down)
    (hBetterUp : 0 ≤ betterUp) (hBetterDown : 0 ≤ betterDown)
    (hdown_le_up : down ≤ up)
    (hbetter_down_le_better_up : betterDown ≤ betterUp)
    (hup_le : up ≤ betterUp)
    (hbetter_down_le : betterDown ≤ down) :
    approvalPairwiseBase betterUp betterDown ≤
      approvalPairwiseBase up down := by
  rw [approvalPairwiseBase_eq_one_sub_sq_sqrt_sub hBetterUp hBetterDown,
    approvalPairwiseBase_eq_one_sub_sq_sqrt_sub hUp hDown]
  have hsqrt_up_le : Real.sqrt up ≤ Real.sqrt betterUp :=
    Real.sqrt_le_sqrt hup_le
  have hsqrt_down_le : Real.sqrt betterDown ≤ Real.sqrt down :=
    Real.sqrt_le_sqrt hbetter_down_le
  have hgap_le :
      Real.sqrt up - Real.sqrt down ≤
        Real.sqrt betterUp - Real.sqrt betterDown := by
    linarith
  have hgap_nonneg :
      0 ≤ Real.sqrt up - Real.sqrt down := by
    exact sub_nonneg.mpr (Real.sqrt_le_sqrt hdown_le_up)
  have hbetter_gap_nonneg :
      0 ≤ Real.sqrt betterUp - Real.sqrt betterDown := by
    exact sub_nonneg.mpr
      (Real.sqrt_le_sqrt hbetter_down_le_better_up)
  have hsq_le :
      (Real.sqrt up - Real.sqrt down) ^ 2 ≤
        (Real.sqrt betterUp - Real.sqrt betterDown) ^ 2 := by
    nlinarith [mul_nonneg hgap_nonneg hgap_nonneg,
      mul_nonneg hbetter_gap_nonneg hbetter_gap_nonneg]
  nlinarith

/--
Strict version of `approvalPairwiseBase_le_of_up_ge_down_le`: in the oriented
region `down ≤ up`, weakly increasing favorable mass and weakly decreasing
unfavorable mass strictly lowers the approval base as soon as one coordinate
strictly improves.
-/
theorem approvalPairwiseBase_lt_of_up_gt_or_down_lt
    {up down betterUp betterDown : ℝ}
    (hUp : 0 ≤ up) (hDown : 0 ≤ down)
    (hBetterUp : 0 ≤ betterUp) (hBetterDown : 0 ≤ betterDown)
    (hdown_le_up : down ≤ up)
    (hbetter_down_le_better_up : betterDown ≤ betterUp)
    (hup_le : up ≤ betterUp)
    (hbetter_down_le : betterDown ≤ down)
    (hstrict : up < betterUp ∨ betterDown < down) :
    approvalPairwiseBase betterUp betterDown <
      approvalPairwiseBase up down := by
  rw [approvalPairwiseBase_eq_one_sub_sq_sqrt_sub hBetterUp hBetterDown,
    approvalPairwiseBase_eq_one_sub_sq_sqrt_sub hUp hDown]
  have hsqrt_up_le : Real.sqrt up ≤ Real.sqrt betterUp :=
    Real.sqrt_le_sqrt hup_le
  have hsqrt_down_le : Real.sqrt betterDown ≤ Real.sqrt down :=
    Real.sqrt_le_sqrt hbetter_down_le
  have hgap_nonneg :
      0 ≤ Real.sqrt up - Real.sqrt down := by
    exact sub_nonneg.mpr (Real.sqrt_le_sqrt hdown_le_up)
  have hbetter_gap_nonneg :
      0 ≤ Real.sqrt betterUp - Real.sqrt betterDown := by
    exact sub_nonneg.mpr
      (Real.sqrt_le_sqrt hbetter_down_le_better_up)
  have hgap_lt :
      Real.sqrt up - Real.sqrt down <
        Real.sqrt betterUp - Real.sqrt betterDown := by
    rcases hstrict with hup_lt | hdown_lt
    · have hsqrt_up_lt : Real.sqrt up < Real.sqrt betterUp :=
        Real.sqrt_lt_sqrt hUp hup_lt
      linarith
    · have hsqrt_down_lt : Real.sqrt betterDown < Real.sqrt down :=
        Real.sqrt_lt_sqrt hBetterDown hdown_lt
      linarith
  have hsq_lt :
      (Real.sqrt up - Real.sqrt down) ^ 2 <
        (Real.sqrt betterUp - Real.sqrt betterDown) ^ 2 := by
    have hmul_lt :
        (Real.sqrt up - Real.sqrt down) *
            (Real.sqrt up - Real.sqrt down) <
          (Real.sqrt betterUp - Real.sqrt betterDown) *
            (Real.sqrt betterUp - Real.sqrt betterDown) :=
      (mul_self_lt_mul_self_iff hgap_nonneg hbetter_gap_nonneg).mp hgap_lt
    nlinarith
  nlinarith

/--
Approval-rate monotonicity corresponding to Remark `tminusaplusa` in the
source: on the positive-base region, weakly increasing favorable mass and
weakly decreasing unfavorable mass weakly increases the learning rate.
-/
theorem approvalPairwiseRate_le_of_up_le_down_ge
    {up down betterUp betterDown : ℝ}
    (hUp : 0 ≤ up) (hDown : 0 ≤ down)
    (hBetterUp : 0 ≤ betterUp) (hBetterDown : 0 ≤ betterDown)
    (hbase_pos : 0 < approvalPairwiseBase up down)
    (hbetter_base_pos : 0 < approvalPairwiseBase betterUp betterDown)
    (hdown_le_up : down ≤ up)
    (hbetter_down_le_better_up : betterDown ≤ betterUp)
    (hup_le : up ≤ betterUp)
    (hbetter_down_le : betterDown ≤ down) :
    approvalPairwiseRate up down ≤
      approvalPairwiseRate betterUp betterDown := by
  have hbase_le :
      approvalPairwiseBase betterUp betterDown ≤
        approvalPairwiseBase up down :=
    approvalPairwiseBase_le_of_up_ge_down_le hUp hDown hBetterUp hBetterDown
      hdown_le_up hbetter_down_le_better_up hup_le hbetter_down_le
  have hlog_le :
      Real.log (approvalPairwiseBase betterUp betterDown) ≤
        Real.log (approvalPairwiseBase up down) :=
    Real.log_le_log hbetter_base_pos hbase_le
  rw [approvalPairwiseRate_eq_neg_log_base,
    approvalPairwiseRate_eq_neg_log_base]
  linarith

/--
Strict approval-rate monotonicity corresponding to Remark `tminusaplusa` in
the source: on the positive-base oriented region, weakly increasing favorable
mass and weakly decreasing unfavorable mass strictly increases the learning
rate whenever at least one coordinate improves strictly.
-/
theorem approvalPairwiseRate_lt_of_up_lt_or_down_gt
    {up down betterUp betterDown : ℝ}
    (hUp : 0 ≤ up) (hDown : 0 ≤ down)
    (hBetterUp : 0 ≤ betterUp) (hBetterDown : 0 ≤ betterDown)
    (hbase_pos : 0 < approvalPairwiseBase up down)
    (hbetter_base_pos : 0 < approvalPairwiseBase betterUp betterDown)
    (hdown_le_up : down ≤ up)
    (hbetter_down_le_better_up : betterDown ≤ betterUp)
    (hup_le : up ≤ betterUp)
    (hbetter_down_le : betterDown ≤ down)
    (hstrict : up < betterUp ∨ betterDown < down) :
    approvalPairwiseRate up down <
      approvalPairwiseRate betterUp betterDown := by
  exact approvalPairwiseRate_lt_of_base_gt hbase_pos hbetter_base_pos
    (approvalPairwiseBase_lt_of_up_gt_or_down_lt
      hUp hDown hBetterUp hBetterDown hdown_le_up
      hbetter_down_le_better_up hup_le hbetter_down_le hstrict)

/--
Positive mass shifted from the down event to the up event strictly improves the
approval pairwise learning rate on the positive-base oriented region.  This is
the symbolic `r(T1+a,T2-a) > r(T1,T2)` step used in the source proof of
`lem:randomizebetterapproval_Wselection`.
-/
theorem approvalPairwiseRate_lt_of_pos_mass_shift
    {T1 T2 a : ℝ}
    (hT1 : 0 ≤ T1) (hT2 : 0 ≤ T2) (ha : 0 < a)
    (hbase_pos : 0 < approvalPairwiseBase T1 T2)
    (hshift_base_pos : 0 < approvalPairwiseBase (T1 + a) (T2 - a))
    (horient : T2 ≤ T1)
    (hdown_nonneg : 0 ≤ T2 - a) :
    approvalPairwiseRate T1 T2 <
      approvalPairwiseRate (T1 + a) (T2 - a) := by
  have ha_nonneg : 0 ≤ a := le_of_lt ha
  refine approvalPairwiseRate_lt_of_up_lt_or_down_gt
    hT1 hT2 ?_ hdown_nonneg hbase_pos hshift_base_pos
    horient ?_ ?_ ?_ ?_
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · exact Or.inl (by nlinarith)

/--
For a fixed positive-base oriented pair, increasing the fraction of a
nonnegative mass shifted from the down event to the up event weakly increases
the approval pairwise learning rate.
-/
theorem approvalPairwiseRate_le_of_split_fraction_le
    {T1 T2 a δ ε : ℝ}
    (hT1 : 0 ≤ T1) (hT2 : 0 ≤ T2) (ha : 0 ≤ a)
    (hδ_nonneg : 0 ≤ δ) (hδε : δ ≤ ε)
    (hbaseδ : 0 < approvalPairwiseBase (T1 + δ * a) (T2 - δ * a))
    (hbaseε : 0 < approvalPairwiseBase (T1 + ε * a) (T2 - ε * a))
    (horient : T2 ≤ T1)
    (hdownδ : 0 ≤ T2 - δ * a)
    (hdownε : 0 ≤ T2 - ε * a) :
    approvalPairwiseRate (T1 + δ * a) (T2 - δ * a) ≤
      approvalPairwiseRate (T1 + ε * a) (T2 - ε * a) := by
  have hε_nonneg : 0 ≤ ε := le_trans hδ_nonneg hδε
  have hδa_nonneg : 0 ≤ δ * a := mul_nonneg hδ_nonneg ha
  have hεa_nonneg : 0 ≤ ε * a := mul_nonneg hε_nonneg ha
  have hδa_le_εa : δ * a ≤ ε * a :=
    mul_le_mul_of_nonneg_right hδε ha
  refine approvalPairwiseRate_le_of_up_le_down_ge
    ?_ hdownδ ?_ hdownε hbaseδ hbaseε ?_ ?_ ?_ ?_
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

/--
Paper-shaped split-rate identity: among the two randomized pivotal-pair rates
with split fractions `p` and `1-p`, the worse rate is the rate at the smaller
fraction `min p (1-p)`.
-/
theorem approvalPairwiseRate_min_split_eq_min_fraction
    {T1 T2 a p : ℝ}
    (hT1 : 0 ≤ T1) (hT2 : 0 ≤ T2) (ha : 0 ≤ a)
    (hp_nonneg : 0 ≤ p) (hp_le_one : p ≤ 1)
    (hbase_p : 0 < approvalPairwiseBase (T1 + p * a) (T2 - p * a))
    (hbase_one_sub :
      0 < approvalPairwiseBase (T1 + (1 - p) * a)
        (T2 - (1 - p) * a))
    (horient : T2 ≤ T1)
    (hdown_p : 0 ≤ T2 - p * a)
    (hdown_one_sub : 0 ≤ T2 - (1 - p) * a) :
    min
        (approvalPairwiseRate (T1 + p * a) (T2 - p * a))
        (approvalPairwiseRate (T1 + (1 - p) * a)
          (T2 - (1 - p) * a)) =
      approvalPairwiseRate (T1 + (min p (1 - p)) * a)
        (T2 - (min p (1 - p)) * a) := by
  have hone_sub_nonneg : 0 ≤ 1 - p := sub_nonneg.mpr hp_le_one
  by_cases hp_le : p ≤ 1 - p
  · have hrate_le :
        approvalPairwiseRate (T1 + p * a) (T2 - p * a) ≤
          approvalPairwiseRate (T1 + (1 - p) * a)
            (T2 - (1 - p) * a) :=
      approvalPairwiseRate_le_of_split_fraction_le
        hT1 hT2 ha hp_nonneg hp_le hbase_p hbase_one_sub
        horient hdown_p hdown_one_sub
    rw [min_eq_left hrate_le, min_eq_left hp_le]
  · have hone_sub_le_p : 1 - p ≤ p := le_of_not_ge hp_le
    have hrate_le :
        approvalPairwiseRate (T1 + (1 - p) * a)
            (T2 - (1 - p) * a) ≤
          approvalPairwiseRate (T1 + p * a) (T2 - p * a) :=
      approvalPairwiseRate_le_of_split_fraction_le
        hT1 hT2 ha hone_sub_nonneg hone_sub_le_p hbase_one_sub hbase_p
        horient hdown_one_sub hdown_p
    rw [min_eq_right hrate_le, min_eq_right hone_sub_le_p]

/--
Split-mass improvement used in the source proof of
`lem:randomizebetterapproval_Wselection`: if positive mass `a` is split
between two mechanisms with weights `p` and `1 - p`, and in both resulting
pairs that mass moves from the down event to the up event, then the original
pairwise approval rate is strictly below both improved rates.
-/
theorem approvalPairwiseRate_lt_min_of_split_mass_improvement
    {T1 T2 a p : ℝ}
    (hT1 : 0 ≤ T1) (hT2 : 0 ≤ T2) (ha : 0 < a)
    (hp_pos : 0 < p) (hp_lt : p < 1)
    (hbase_pos : 0 < approvalPairwiseBase T1 T2)
    (hbase_p_pos : 0 < approvalPairwiseBase (T1 + p * a) (T2 - p * a))
    (hbase_one_sub_pos :
      0 < approvalPairwiseBase (T1 + (1 - p) * a)
        (T2 - (1 - p) * a))
    (horient : T2 ≤ T1)
    (hp_down_nonneg : 0 ≤ T2 - p * a)
    (hone_sub_down_nonneg : 0 ≤ T2 - (1 - p) * a) :
    approvalPairwiseRate T1 T2 <
      min
        (approvalPairwiseRate (T1 + p * a) (T2 - p * a))
        (approvalPairwiseRate (T1 + (1 - p) * a)
          (T2 - (1 - p) * a)) := by
  have hp_a_pos : 0 < p * a := mul_pos hp_pos ha
  have hp_a_nonneg : 0 ≤ p * a := le_of_lt hp_a_pos
  have hone_sub_pos : 0 < 1 - p := sub_pos.mpr hp_lt
  have hone_sub_a_pos : 0 < (1 - p) * a := mul_pos hone_sub_pos ha
  have hone_sub_a_nonneg : 0 ≤ (1 - p) * a :=
    le_of_lt hone_sub_a_pos
  rw [lt_min_iff]
  constructor
  · refine approvalPairwiseRate_lt_of_up_lt_or_down_gt
      hT1 hT2 ?_ hp_down_nonneg hbase_pos hbase_p_pos
      horient ?_ ?_ ?_ ?_
    · nlinarith
    · nlinarith
    · nlinarith
    · nlinarith
    · exact Or.inl (by nlinarith)
  · refine approvalPairwiseRate_lt_of_up_lt_or_down_gt
      hT1 hT2 ?_ hone_sub_down_nonneg hbase_pos hbase_one_sub_pos
      horient ?_ ?_ ?_ ?_
    · nlinarith
    · nlinarith
    · nlinarith
    · nlinarith
    · exact Or.inl (by nlinarith)

/--
When the down-probability is a fixed nonnegative multiple `phi` of the
up-probability, the approval base is affine in the up-probability.
-/
theorem approvalPairwiseBase_same_ratio
    {phi p : ℝ} (hphi : 0 ≤ phi) (hp : 0 ≤ p) :
    approvalPairwiseBase p (phi * p) =
      1 - p * (1 + phi - 2 * Real.sqrt phi) := by
  have hsqrt : Real.sqrt (p * (phi * p)) = p * Real.sqrt phi := by
    have harg : p * (phi * p) = phi * (p * p) := by ring
    rw [harg, Real.sqrt_mul hphi, Real.sqrt_mul_self hp]
    ring
  dsimp [approvalPairwiseBase]
  rw [hsqrt]
  ring

/--
For a fixed non-unit same-ratio parameter, increasing the up-probability
strictly decreases the approval base and therefore strictly increases the
approval learning rate.
-/
theorem approvalPairwiseBase_same_ratio_strictAnti
    {phi p q : ℝ} (hphi : 0 ≤ phi)
    (hcoef : 0 < 1 + phi - 2 * Real.sqrt phi)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : q < p) :
    approvalPairwiseBase p (phi * p) <
      approvalPairwiseBase q (phi * q) := by
  rw [approvalPairwiseBase_same_ratio hphi hp,
    approvalPairwiseBase_same_ratio hphi hq]
  nlinarith

/-- A nonnegative finite weight vector with total mass one has a positive entry. -/
theorem exists_pos_of_nonneg_sum_eq_one
    {Rule : Type*} [Fintype Rule]
    (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1) :
    ∃ rule : Rule, 0 < weight rule :=
  AppliedModelingLib.exists_positive_weight_of_nonneg_sum_eq_one
    weight hweight hsum

/--
A convex combination of strictly positive values is strictly positive when the
weights are nonnegative and sum to one.
-/
theorem weighted_sum_pos_of_nonneg_sum_eq_one
    {Rule : Type*} [Fintype Rule]
    (weight value : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hvalue : ∀ rule, 0 < value rule) :
    0 < ∑ rule : Rule, weight rule * value rule :=
  AppliedModelingLib.weightedSum_pos_of_nonneg_sum_eq_one
    weight value hweight hsum hvalue

theorem sqrt_weightedApprovalTerm
    {w pUp pDown : ℝ} (hw : 0 ≤ w) (hUp : 0 ≤ pUp) :
    Real.sqrt (w * pUp) * Real.sqrt (w * pDown) =
      w * Real.sqrt (pUp * pDown) := by
  rw [Real.sqrt_mul hw, Real.sqrt_mul hw, Real.sqrt_mul hUp]
  rw [show Real.sqrt w * Real.sqrt pUp * (Real.sqrt w * Real.sqrt pDown) =
      (Real.sqrt w * Real.sqrt w) *
        (Real.sqrt pUp * Real.sqrt pDown) by ring]
  rw [← sq, Real.sq_sqrt hw]

/--
The approval-rate base is concave under finite mixtures of valid nonnegative
up/down probabilities.  This is the Cauchy-Schwarz step in the source proof of
K-approval no-randomization.
-/
theorem approvalPairwiseBase_weighted_le
    {Rule : Type*} [Fintype Rule]
    (weight pUp pDown : Rule → ℝ) {mixedUp mixedDown : ℝ}
    (hmixedUp : mixedUp = ∑ rule : Rule, weight rule * pUp rule)
    (hmixedDown : mixedDown = ∑ rule : Rule, weight rule * pDown rule)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hUp : ∀ rule, 0 ≤ pUp rule)
    (hDown : ∀ rule, 0 ≤ pDown rule) :
    (∑ rule : Rule,
      weight rule * approvalPairwiseBase (pUp rule) (pDown rule)) ≤
      approvalPairwiseBase mixedUp mixedDown := by
  have hcs := Real.sum_sqrt_mul_sqrt_le
    (s := (Finset.univ : Finset Rule))
    (f := fun rule => weight rule * pUp rule)
    (g := fun rule => weight rule * pDown rule)
    (fun rule => mul_nonneg (hweight rule) (hUp rule))
    (fun rule => mul_nonneg (hweight rule) (hDown rule))
  have hsqrt_le :
      (∑ rule : Rule, weight rule * Real.sqrt (pUp rule * pDown rule)) ≤
        Real.sqrt mixedUp * Real.sqrt mixedDown := by
    have hcs' :
        (∑ rule : Rule,
          Real.sqrt (weight rule * pUp rule) *
            Real.sqrt (weight rule * pDown rule)) ≤
          Real.sqrt (∑ rule : Rule, weight rule * pUp rule) *
            Real.sqrt (∑ rule : Rule, weight rule * pDown rule) := by
      simpa using hcs
    have hterm :
        (∑ rule : Rule,
          Real.sqrt (weight rule * pUp rule) *
            Real.sqrt (weight rule * pDown rule)) =
        ∑ rule : Rule, weight rule * Real.sqrt (pUp rule * pDown rule) := by
      refine Finset.sum_congr rfl ?_
      intro rule _
      exact sqrt_weightedApprovalTerm (hweight rule) (hUp rule)
    rw [hterm] at hcs'
    rwa [hmixedUp, hmixedDown]
  rw [hmixedUp, hmixedDown] at hsqrt_le
  have hsumUp_nonneg : 0 ≤ ∑ rule : Rule, weight rule * pUp rule := by
    exact Finset.sum_nonneg (by
      intro rule _
      exact mul_nonneg (hweight rule) (hUp rule))
  have hsum_base :
      (∑ rule : Rule,
        weight rule * approvalPairwiseBase (pUp rule) (pDown rule)) =
        2 * (∑ rule : Rule,
          weight rule * Real.sqrt (pUp rule * pDown rule)) +
        (∑ rule : Rule, weight rule) -
        (∑ rule : Rule, weight rule * pUp rule) -
        (∑ rule : Rule, weight rule * pDown rule) := by
    simp only [approvalPairwiseBase]
    have hpoint : ∀ rule : Rule,
        weight rule *
            (2 * Real.sqrt (pUp rule * pDown rule) + 1 -
              pUp rule - pDown rule) =
          2 * (weight rule * Real.sqrt (pUp rule * pDown rule)) +
            weight rule - weight rule * pUp rule -
            weight rule * pDown rule := by
      intro rule
      ring
    rw [Finset.sum_congr rfl (fun rule _ => hpoint rule)]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
    have htwo :
        (∑ rule : Rule,
          2 * (weight rule * Real.sqrt (pUp rule * pDown rule))) =
          2 * ∑ rule : Rule,
            weight rule * Real.sqrt (pUp rule * pDown rule) := by
      rw [Finset.mul_sum]
    rw [htwo]
  rw [hsum_base, hsum, hmixedUp, hmixedDown]
  unfold approvalPairwiseBase
  rw [Real.sqrt_mul hsumUp_nonneg]
  nlinarith

/--
If every component has the same down/up ratio, then the K-approval pairwise
base of the mixture is exactly the same weighted mixture of component bases.
-/
theorem approvalPairwiseBase_weighted_eq_same_ratio
    {Rule : Type*} [Fintype Rule]
    (weight pUp : Rule → ℝ) (ratio mixedUp mixedDown : ℝ)
    (hmixedUp : mixedUp = ∑ rule : Rule, weight rule * pUp rule)
    (hmixedDown :
      mixedDown = ∑ rule : Rule, weight rule * (ratio * pUp rule))
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hUp : ∀ rule, 0 ≤ pUp rule)
    (hratio : 0 ≤ ratio) :
    approvalPairwiseBase mixedUp mixedDown =
      ∑ rule : Rule,
        weight rule * approvalPairwiseBase (pUp rule) (ratio * pUp rule) := by
  let coef : ℝ := 1 + ratio - 2 * Real.sqrt ratio
  have hmixedUp_nonneg : 0 ≤ mixedUp := by
    rw [hmixedUp]
    exact Finset.sum_nonneg (by
      intro rule _
      exact mul_nonneg (hweight rule) (hUp rule))
  have hmixedDown_ratio : mixedDown = ratio * mixedUp := by
    rw [hmixedDown, hmixedUp, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro rule _
    ring
  rw [hmixedDown_ratio,
    approvalPairwiseBase_same_ratio hratio hmixedUp_nonneg]
  symm
  calc
    ∑ rule : Rule,
        weight rule * approvalPairwiseBase (pUp rule) (ratio * pUp rule)
        =
      ∑ rule : Rule, weight rule * (1 - pUp rule * coef) := by
        refine Finset.sum_congr rfl ?_
        intro rule _
        rw [approvalPairwiseBase_same_ratio hratio (hUp rule)]
    _ = 1 - mixedUp * coef := by
        have hpoint : ∀ rule : Rule,
            weight rule * (1 - pUp rule * coef) =
              weight rule - weight rule * pUp rule * coef := by
          intro rule
          ring
        rw [Finset.sum_congr rfl (fun rule _ => hpoint rule),
          Finset.sum_sub_distrib, hsum, ← Finset.sum_mul, ← hmixedUp]

/--
Finite Jensen theorem for the real-valued K-approval rate on the positive-base
region.  The positive-base hypotheses exclude boundary cases where Lean's
total real logarithm would not model the paper's extended `+∞` rate.
-/
theorem approvalPairwiseRate_weighted_le
    {Rule : Type*} [Fintype Rule]
    (weight pUp pDown : Rule → ℝ) {mixedUp mixedDown : ℝ}
    (hmixedUp : mixedUp = ∑ rule : Rule, weight rule * pUp rule)
    (hmixedDown : mixedDown = ∑ rule : Rule, weight rule * pDown rule)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hUp : ∀ rule, 0 ≤ pUp rule)
    (hDown : ∀ rule, 0 ≤ pDown rule)
    (hbase_pos :
      ∀ rule, 0 < approvalPairwiseBase (pUp rule) (pDown rule))
    (hmixed_base_pos : 0 < approvalPairwiseBase mixedUp mixedDown) :
    approvalPairwiseRate mixedUp mixedDown ≤
      ∑ rule : Rule,
        weight rule * approvalPairwiseRate (pUp rule) (pDown rule) := by
  let base : Rule → ℝ :=
    fun rule => approvalPairwiseBase (pUp rule) (pDown rule)
  have hbase_weighted_le :
      (∑ rule : Rule, weight rule * base rule) ≤
        approvalPairwiseBase mixedUp mixedDown := by
    simpa [base] using
      approvalPairwiseBase_weighted_le
        weight pUp pDown hmixedUp hmixedDown hweight hsum hUp hDown
  have hweight_exists : ∃ rule : Rule, 0 < weight rule := by
    by_contra hnone
    have hnonpos : ∀ rule : Rule, weight rule ≤ 0 := by
      intro rule
      exact le_of_not_gt (fun hpos => hnone ⟨rule, hpos⟩)
    have hsum_nonpos : (∑ rule : Rule, weight rule) ≤ 0 :=
      Finset.sum_nonpos (by intro rule _; exact hnonpos rule)
    linarith
  have hsum_base_pos : 0 < ∑ rule : Rule, weight rule * base rule := by
    refine Finset.sum_pos' ?_ ?_
    · intro rule _
      exact mul_nonneg (hweight rule) (le_of_lt (hbase_pos rule))
    · rcases hweight_exists with ⟨rule, hpos⟩
      exact ⟨rule, Finset.mem_univ rule,
        mul_pos hpos (hbase_pos rule)⟩
  have hlog_base :
      -Real.log (approvalPairwiseBase mixedUp mixedDown) ≤
        -Real.log (∑ rule : Rule, weight rule * base rule) := by
    exact neg_le_neg (Real.log_le_log hsum_base_pos hbase_weighted_le)
  have hlog_jensen :
      -Real.log (∑ rule : Rule, weight rule * base rule) ≤
        ∑ rule : Rule, weight rule * (-Real.log (base rule)) := by
    have hlog_jensen_raw :
        (∑ rule ∈ (Finset.univ : Finset Rule),
            weight rule • Real.log (base rule)) ≤
          Real.log
            (∑ rule ∈ (Finset.univ : Finset Rule),
              weight rule • base rule) := by
      exact strictConcaveOn_log_Ioi.concaveOn.le_map_sum
        (t := (Finset.univ : Finset Rule))
        (w := weight)
        (p := base)
        (by intro rule _; exact hweight rule)
        (by simpa using hsum)
        (by intro rule _; exact hbase_pos rule)
    simp only [smul_eq_mul] at hlog_jensen_raw
    have hneg := neg_le_neg hlog_jensen_raw
    simpa [Finset.sum_neg_distrib, mul_neg] using hneg
  calc
    approvalPairwiseRate mixedUp mixedDown
        = -Real.log (approvalPairwiseBase mixedUp mixedDown) := by
          rw [approvalPairwiseRate_eq_neg_log_base]
    _ ≤ -Real.log (∑ rule : Rule, weight rule * base rule) := hlog_base
    _ ≤ ∑ rule : Rule, weight rule * (-Real.log (base rule)) :=
          hlog_jensen
    _ = ∑ rule : Rule,
          weight rule * approvalPairwiseRate (pUp rule) (pDown rule) := by
      simp [base, approvalPairwiseRate_eq_neg_log_base]

/--
Proposition 3 exact minimization: for a valid ternary approval-gap law with
positive up/down probabilities, the paper's closed form equals the negative
infimum of the ternary log-MGF.
-/
theorem approvalPairwiseRate_eq_ternary_log_mgf_inf
    {pUp pDown : ℝ} (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hsum : pUp + pDown ≤ 1) :
    approvalPairwiseRate pUp pDown =
      -sInf (Set.range fun z : ℝ => ternaryGapLogMGF pUp pDown z) := by
  simpa [approvalPairwiseRate] using
    ternaryGapClosedChernoffRate_eq_neg_sInf_logMGF
      hUp hDown hsum

/--
If a finite score-gap law has the ternary approval-gap MGF at every dual
parameter, then its Chernoff exponent is exactly the source closed form.
-/
theorem finiteChernoffRate_eq_approvalPairwiseRate_of_ternary_mgf
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {pUp pDown : ℝ} (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hsum : pUp + pDown ≤ 1)
    (hmgf :
      ∀ z : ℝ,
        finiteMGF law (fun signal => hiScore signal - loScore signal) z =
          ternaryGapMGF pUp pDown z) :
    finiteChernoffRate law
        (fun signal => hiScore signal - loScore signal) =
      approvalPairwiseRate pUp pDown := by
  have hlog :
      (fun z : ℝ =>
        finiteLogMGF law
          (fun signal => hiScore signal - loScore signal) z) =
        fun z : ℝ => ternaryGapLogMGF pUp pDown z := by
    funext z
    simp [finiteLogMGF, ternaryGapLogMGF, hmgf z]
  calc
    finiteChernoffRate law
        (fun signal => hiScore signal - loScore signal)
        = -sInf (Set.range fun z : ℝ => ternaryGapLogMGF pUp pDown z) := by
          simp [finiteChernoffRate, hlog]
    _ = approvalPairwiseRate pUp pDown := by
          exact (approvalPairwiseRate_eq_ternary_log_mgf_inf
            hUp hDown hsum).symm

/--
Proposition 3 Chernoff upper-bound half for K-approval.  Once the per-voter
score-gap MGF is identified with the ternary approval-gap MGF, the paper's
closed-form exponent gives an iid pairwise mistake upper bound.
-/
theorem approvalPairwiseError_hasExpUpperBoundWithConst_of_ternary_mgf
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hle : pDown ≤ pUp) (hsum : pUp + pDown ≤ 1)
    (hmgf :
      finiteMGF law (fun signal => hiScore signal - loScore signal)
          (ternaryGapChernoffDual pUp pDown) =
        ternaryGapMGF pUp pDown (ternaryGapChernoffDual pUp pDown)) :
    HasExpUpperBoundWithConst
      (pairwiseScoringErrorProb law hiScore loScore)
      (approvalPairwiseRate pUp pDown) := by
  simpa [pairwiseScoringErrorProb, approvalPairwiseRate] using
    finiteIidScoreGapLeftTail_hasExpUpperBoundWithConst_of_ternaryGapMGF
      (μ := law) (hiScore := hiScore) (loScore := loScore)
      hUp hDown hle hsum hmgf

/--
Pointwise Proposition 3 Chernoff upper bound for K-approval: after identifying
the one-voter score-gap MGF with the ternary approval-gap MGF at the closed-form
dual, the pairwise mistake probability is bounded by
`exp (-n * approvalPairwiseRate pUp pDown)`.
-/
theorem approvalPairwiseErrorProb_le_exp_neg_approvalPairwiseRate_of_ternary_mgf
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hle : pDown ≤ pUp) (hsum : pUp + pDown ≤ 1)
    (hmgf :
      finiteMGF law (fun signal => hiScore signal - loScore signal)
          (ternaryGapChernoffDual pUp pDown) =
        ternaryGapMGF pUp pDown (ternaryGapChernoffDual pUp pDown))
    (n : ℕ) :
    pairwiseScoringErrorProb law hiScore loScore n ≤
      Real.exp (-(n : ℝ) * approvalPairwiseRate pUp pDown) := by
  have hmgf_exp :
      finiteMGF law (fun signal => hiScore signal - loScore signal)
          (ternaryGapChernoffDual pUp pDown) =
        Real.exp (-(approvalPairwiseRate pUp pDown)) := by
    rw [hmgf]
    simpa [approvalPairwiseRate] using
      ternaryGapMGF_chernoffDual_eq_exp_neg_closedRate hUp hDown hsum
  have hrate :
      approvalPairwiseRate pUp pDown ≤
        -finiteLogMGF law
          (fun signal => hiScore signal - loScore signal)
          (ternaryGapChernoffDual pUp pDown) := by
    unfold finiteLogMGF
    rw [hmgf_exp, Real.log_exp]
    linarith
  exact
    pairwiseScoringErrorProb_le_exp_of_nonpos_dual_rate_le
      law hiScore loScore
      (ternaryGapChernoffDual_nonpos hUp hDown hle)
      hrate n

/--
Proposition 3 exact-rate endpoint for K-approval from the reusable finite iid
Cramer certificate and the all-dual ternary MGF identification.
-/
theorem approvalPairwiseError_exponentialRateCertificate_of_cramer_ternary_mgf
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hsum : pUp + pDown ≤ 1)
    (hmgf :
      ∀ z : ℝ,
        finiteMGF law (fun signal => hiScore signal - loScore signal) z =
          ternaryGapMGF pUp pDown z)
    (C : FiniteIidScoreGapCramerCertificate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (approvalPairwiseRate pUp pDown) := by
  have hcert :=
    pairwiseScoringError_exponentialRateCertificate_of_cramer
      law hiScore loScore C
  have hrate :
      pairwiseScoringRate law hiScore loScore =
        approvalPairwiseRate pUp pDown := by
    simpa [pairwiseScoringRate, finiteScoreGapChernoffRate] using
      finiteChernoffRate_eq_approvalPairwiseRate_of_ternary_mgf
        law hiScore loScore hUp hDown hsum hmgf
  simpa [hrate] using hcert

/--
Exact K-approval pairwise rate from the natural finite score classification:
the score gap is always `+1`, `0`, or `-1`, and the two nonzero gap
probabilities are `pUp` and `pDown`.
-/
theorem approvalPairwiseError_exponentialRateCertificate_of_cramer_ternary_scores
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
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
    (C : FiniteIidScoreGapCramerCertificate law hiScore loScore) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (approvalPairwiseRate pUp pDown) := by
  classical
  let gap : Signal → ℝ := fun signal => hiScore signal - loScore signal
  let up : Signal → Prop := fun signal => gap signal = 1
  let down : Signal → Prop := fun signal => gap signal = -1
  have hdisjoint : ∀ signal, up signal → down signal → False := by
    intro signal hup hdown
    have : (1 : ℝ) = -1 := hup.symm.trans hdown
    norm_num at this
  have hzero_prob :
      AppliedModelingLib.pmfProb law (fun signal => ¬up signal ∧ ¬down signal) =
        1 - pUp - pDown := by
    have hsplit :=
      AppliedModelingLib.pmfProb_not_and_not_eq_one_sub_add_of_disjoint
        law up down hdisjoint
    simpa [gap, up, down, hUpProb, hDownProb] using hsplit
  have hsum : pUp + pDown ≤ 1 := by
    have hnonneg :
        0 ≤ AppliedModelingLib.pmfProb law
          (fun signal => ¬up signal ∧ ¬down signal) :=
      AppliedModelingLib.pmfProb_nonneg law
        (fun signal => ¬up signal ∧ ¬down signal)
    rw [hzero_prob] at hnonneg
    linarith
  exact
    approvalPairwiseError_exponentialRateCertificate_of_cramer_ternary_mgf
      law hiScore loScore hUp hDown hsum
      (fun z =>
        finiteMGF_eq_ternaryGapMGF_of_score_eq_ternary
          law gap
          (by simpa [gap] using hscore)
          (by simpa [gap] using hUpProb)
          (by simpa [gap] using hDownProb)
          z)
      C

/--
The finite iid Cramer certificate needed by the Cramer-form Proposition 3
endpoint is closed for nondegenerate ternary approval-style score gaps.
-/
theorem finiteIidScoreGapCramerCertificate_of_approval_ternary_scores
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
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
        pDown) :
    FiniteIidScoreGapCramerCertificate law hiScore loScore :=
  finiteIidScoreGapCramerCertificate_of_ternary_scores
    law hiScore loScore hUp hDown hle hscore hUpProb hDownProb

/--
Exact K-approval pairwise rate from only the lower-bound side of the Cramer
calculation.  The upper-bound side is discharged by the proved finite Chernoff
bound for ternary score gaps.
-/
theorem approvalPairwiseError_exponentialRateCertificate_of_ternary_scores_lower_bounds
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
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
    (hpos :
      ∀ᶠ n in Filter.atTop,
        0 < pairwiseScoringErrorProb law hiScore loScore n)
    (hlower :
      ∀ targetRate,
        approvalPairwiseRate pUp pDown < targetRate →
          HasExpLowerBoundWithConst
            (pairwiseScoringErrorProb law hiScore loScore) targetRate) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (approvalPairwiseRate pUp pDown) := by
  classical
  let gap : Signal → ℝ := fun signal => hiScore signal - loScore signal
  let up : Signal → Prop := fun signal => gap signal = 1
  let down : Signal → Prop := fun signal => gap signal = -1
  have hdisjoint : ∀ signal, up signal → down signal → False := by
    intro signal hup hdown
    have : (1 : ℝ) = -1 := hup.symm.trans hdown
    norm_num at this
  have hzero_prob :
      AppliedModelingLib.pmfProb law (fun signal => ¬up signal ∧ ¬down signal) =
        1 - pUp - pDown := by
    have hsplit :=
      AppliedModelingLib.pmfProb_not_and_not_eq_one_sub_add_of_disjoint
        law up down hdisjoint
    simpa [gap, up, down, hUpProb, hDownProb] using hsplit
  have hsum : pUp + pDown ≤ 1 := by
    have hnonneg :
        0 ≤ AppliedModelingLib.pmfProb law
          (fun signal => ¬up signal ∧ ¬down signal) :=
      AppliedModelingLib.pmfProb_nonneg law
        (fun signal => ¬up signal ∧ ¬down signal)
    rw [hzero_prob] at hnonneg
    linarith
  have hmgf :
      finiteMGF law
          (fun signal => hiScore signal - loScore signal)
          (ternaryGapChernoffDual pUp pDown) =
        ternaryGapMGF pUp pDown (ternaryGapChernoffDual pUp pDown) := by
    simpa [gap] using
      finiteMGF_eq_ternaryGapMGF_of_score_eq_ternary
        law gap
        (by simpa [gap] using hscore)
        (by simpa [gap] using hUpProb)
        (by simpa [gap] using hDownProb)
        (ternaryGapChernoffDual pUp pDown)
  refine ⟨hpos, ?_⟩
  refine hasExponentialRate_of_expUpperLowerBounds hpos ?_ hlower
  intro targetRate htarget
  exact
    HasExpUpperBoundWithConst.weaken_rate
      (approvalPairwiseError_hasExpUpperBoundWithConst_of_ternary_mgf
        law hiScore loScore hUp hDown hle hsum hmgf)
      (le_of_lt htarget)

/--
Exact K-approval pairwise rate from a concrete polynomially corrected
geometric lower bound.  This is the downstream shape expected from a
finite-type or multinomial lower-bound argument: once the lower tail is
eventually at least `c * exp(-rate)^n / (n+1)^d`, the general lower-bound
certificate required by the exact-rate theorem follows automatically.
-/
theorem approvalPairwiseError_exponentialRateCertificate_of_ternary_scores_poly_geometric_lower
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
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
    {lowerConst : ℝ} (hlowerConst : 0 < lowerConst) (lowerDegree : ℕ)
    (hlower :
      ∀ᶠ n : ℕ in Filter.atTop,
        lowerConst *
            Real.exp (-(approvalPairwiseRate pUp pDown)) ^ n /
              (((n.succ : ℕ) : ℝ) ^ lowerDegree) ≤
          pairwiseScoringErrorProb law hiScore loScore n) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (approvalPairwiseRate pUp pDown) := by
  refine
    approvalPairwiseError_exponentialRateCertificate_of_ternary_scores_lower_bounds
      law hiScore loScore hUp hDown hle hscore hUpProb hDownProb ?_ ?_
  · exact
      pairwiseScoringError_eventually_pos_of_negative_gap_prob
        law hiScore loScore hDown hDownProb
  intro targetRate htarget
  refine
    HasExpLowerBoundWithConst.of_eventually_geometric_div_polynomial_lower
      lowerDegree hlowerConst (Real.exp_pos _) ?_ hlower
  have hlog :
      -Real.log (Real.exp (-(approvalPairwiseRate pUp pDown))) =
        approvalPairwiseRate pUp pDown := by
    rw [Real.log_exp]
    ring
  simpa [hlog] using htarget

/--
Exact K-approval pairwise rate from a concrete ternary score-gap law.

This is a paper-facing wrapper around the reusable finite iid ternary exact-rate
certificate.
-/
theorem approvalPairwiseError_exponentialRateCertificate_of_ternary_scores
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
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
        pDown) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (approvalPairwiseRate pUp pDown) := by
  simpa [pairwiseScoringErrorProb, approvalPairwiseRate] using
    finiteIidScoreGapLeftTail_exponentialRateCertificate_of_ternary_scores
      law hiScore loScore hUp hDown hle hscore hUpProb hDownProb

/--
Ternary approval boundary support: if the down-event has zero probability,
then every positive-mass one-voter score gap is nonnegative.
-/
theorem approvalTernaryScore_support_nonneg_of_down_prob_zero
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hscore :
      ∀ signal,
        hiScore signal - loScore signal = 1 ∨
          hiScore signal - loScore signal = 0 ∨
          hiScore signal - loScore signal = -1)
    (hDownZero :
      AppliedModelingLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = -1) =
        0) :
    ∀ signal, 0 < (law signal).toReal →
      0 ≤ hiScore signal - loScore signal := by
  classical
  intro signal hmass
  rcases hscore signal with hpos | hzero | hneg
  · rw [hpos]
    norm_num
  · rw [hzero]
  · have hprob_pos :
        0 <
          AppliedModelingLib.pmfProb law
            (fun signal => hiScore signal - loScore signal = -1) :=
      AppliedModelingLib.pmfProb_pos_of_mass law
        (fun signal => hiScore signal - loScore signal = -1)
        signal hneg hmass
    rw [hDownZero] at hprob_pos
    exact False.elim (lt_irrefl (0 : ℝ) hprob_pos)

/--
Ternary approval strict boundary support: if both zero and down events have
zero probability, then every positive-mass one-voter score gap is strictly
positive.
-/
theorem approvalTernaryScore_support_pos_of_down_zero_prob_zero
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hscore :
      ∀ signal,
        hiScore signal - loScore signal = 1 ∨
          hiScore signal - loScore signal = 0 ∨
          hiScore signal - loScore signal = -1)
    (hZeroZero :
      AppliedModelingLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = 0) =
        0)
    (hDownZero :
      AppliedModelingLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = -1) =
        0) :
    ∀ signal, 0 < (law signal).toReal →
      0 < hiScore signal - loScore signal := by
  classical
  intro signal hmass
  rcases hscore signal with hpos | hzero | hneg
  · rw [hpos]
    norm_num
  · have hprob_pos :
        0 <
          AppliedModelingLib.pmfProb law
            (fun signal => hiScore signal - loScore signal = 0) :=
      AppliedModelingLib.pmfProb_pos_of_mass law
        (fun signal => hiScore signal - loScore signal = 0)
        signal hzero hmass
    rw [hZeroZero] at hprob_pos
    exact False.elim (lt_irrefl (0 : ℝ) hprob_pos)
  · have hprob_pos :
        0 <
          AppliedModelingLib.pmfProb law
            (fun signal => hiScore signal - loScore signal = -1) :=
      AppliedModelingLib.pmfProb_pos_of_mass law
        (fun signal => hiScore signal - loScore signal = -1)
        signal hneg hmass
    rw [hDownZero] at hprob_pos
    exact False.elim (lt_irrefl (0 : ℝ) hprob_pos)

/--
Approval ternary boundary exact rate: when the down-event has zero probability
and the zero-gap event has positive probability, the source closed form with
`pDown = 0` is the exact iid pairwise rate.
-/
theorem approvalPairwiseError_exponentialRateCertificate_of_ternary_scores_down_zero
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {pUp pZero : ℝ}
    (hscore :
      ∀ signal,
        hiScore signal - loScore signal = 1 ∨
          hiScore signal - loScore signal = 0 ∨
          hiScore signal - loScore signal = -1)
    (hUpProb :
      AppliedModelingLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = 1) =
        pUp)
    (hZeroProb :
      AppliedModelingLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = 0) =
        pZero)
    (hZero_pos : 0 < pZero)
    (hDownZero :
      AppliedModelingLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = -1) =
        0) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law hiScore loScore)
      (approvalPairwiseRate pUp 0) := by
  classical
  let gap : Signal → ℝ := fun signal => hiScore signal - loScore signal
  let up : Signal → Prop := fun signal => gap signal = 1
  let down : Signal → Prop := fun signal => gap signal = -1
  have hdisjoint : ∀ signal, up signal → down signal → False := by
    intro signal hup hdown
    have : (1 : ℝ) = -1 := hup.symm.trans hdown
    norm_num at this
  have hzero_event :
      AppliedModelingLib.pmfProb law (fun signal => gap signal = 0) =
        AppliedModelingLib.pmfProb law
          (fun signal => ¬up signal ∧ ¬down signal) := by
    refine AppliedModelingLib.pmfProb_congr law ?_
    intro signal
    constructor
    · intro hzero
      constructor
      · intro hup
        have : (1 : ℝ) = 0 := hup.symm.trans hzero
        norm_num at this
      · intro hdown
        have : (-1 : ℝ) = 0 := hdown.symm.trans hzero
        norm_num at this
    · intro hnot
      rcases hscore signal with hpos | hzero | hneg
      · exact False.elim (hnot.1 hpos)
      · exact hzero
      · exact False.elim (hnot.2 hneg)
  have hnot_up_down_prob :
      AppliedModelingLib.pmfProb law (fun signal => ¬up signal ∧ ¬down signal) =
        1 - pUp := by
    have hsplit :=
      AppliedModelingLib.pmfProb_not_and_not_eq_one_sub_add_of_disjoint
        law up down hdisjoint
    calc
      AppliedModelingLib.pmfProb law (fun signal => ¬up signal ∧ ¬down signal)
          = 1 - pUp - 0 := by
              simpa [gap, up, down, hUpProb, hDownZero] using hsplit
      _ = 1 - pUp := by ring
  have hpZero_eq : pZero = 1 - pUp := by
    calc
      pZero = AppliedModelingLib.pmfProb law (fun signal => gap signal = 0) := by
          simpa [gap] using hZeroProb.symm
      _ = AppliedModelingLib.pmfProb law
          (fun signal => ¬up signal ∧ ¬down signal) := hzero_event
      _ = 1 - pUp := hnot_up_down_prob
  have hsupport :
      ∀ signal, 0 < (law signal).toReal →
        0 ≤ hiScore signal - loScore signal :=
    approvalTernaryScore_support_nonneg_of_down_prob_zero
      law hiScore loScore hscore hDownZero
  have hcert :
      ExponentialRateCertificate
        (pairwiseScoringErrorProb law hiScore loScore)
        (-Real.log pZero) :=
    pairwiseScoringError_exponentialRateCertificate_of_support_nonneg_zero_gap_prob
      law hiScore loScore hsupport hZeroProb hZero_pos
  have hrate : approvalPairwiseRate pUp 0 = -Real.log pZero := by
    rw [approvalPairwiseRate_zero_down_eq_neg_log_one_sub_up, ← hpZero_eq]
  simpa [hrate] using hcert

/--
Exact pairwise finite iid K-approval-style boundary certificate for ternary
score gaps: if every ordered pair has zero down-gap probability and positive
zero-gap probability, the per-pair source rate is
`approvalPairwiseRate pUp 0`.
-/
def finiteScoreGapPairwiseRateCertificate_of_approval_ternary_scores_down_zero
    {Candidate Signal : Type*} [Fintype Candidate] [Fintype Signal]
    [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (pUp pZero : Candidate → Candidate → ℝ)
    (hscore :
      ∀ hi lo signal,
        score hi signal - score lo signal = 1 ∨
          score hi signal - score lo signal = 0 ∨
          score hi signal - score lo signal = -1)
    (hUpProb :
      ∀ hi lo,
        AppliedModelingLib.pmfProb law
            (fun signal => score hi signal - score lo signal = 1) =
          pUp hi lo)
    (hZeroProb :
      ∀ hi lo,
        AppliedModelingLib.pmfProb law
            (fun signal => score hi signal - score lo signal = 0) =
          pZero hi lo)
    (hZero_pos : ∀ hi lo, 0 < pZero hi lo)
    (hDownZero :
      ∀ hi lo,
        AppliedModelingLib.pmfProb law
            (fun signal => score hi signal - score lo signal = -1) =
          0) :
    PairwiseErrorRateCertificate Candidate where
  errorProb := finiteScoreGapPairwiseErrorProb law score
  rate := fun hi lo => approvalPairwiseRate (pUp hi lo) 0
  has_rate := by
    intro hi lo
    simpa [finiteScoreGapPairwiseErrorProb] using
      approvalPairwiseError_exponentialRateCertificate_of_ternary_scores_down_zero
        law (score hi) (score lo)
        (hscore hi lo) (hUpProb hi lo) (hZeroProb hi lo)
        (hZero_pos hi lo) (hDownZero hi lo)

/--
Approval ternary strict boundary: if neither a zero nor a down one-voter gap
has positive probability, the iid pairwise mistake event is eventually empty.
-/
theorem approvalPairwiseError_eventually_zero_of_ternary_scores_down_zero_zero_zero
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hscore :
      ∀ signal,
        hiScore signal - loScore signal = 1 ∨
          hiScore signal - loScore signal = 0 ∨
          hiScore signal - loScore signal = -1)
    (hZeroZero :
      AppliedModelingLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = 0) =
        0)
    (hDownZero :
      AppliedModelingLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = -1) =
        0) :
    ∀ᶠ n in Filter.atTop,
      pairwiseScoringErrorProb law hiScore loScore n = 0 :=
  pairwiseScoringError_eventually_zero_of_support_pos
    law hiScore loScore
    (approvalTernaryScore_support_pos_of_down_zero_prob_zero
      law hiScore loScore hscore hZeroZero hDownZero)

/--
Approval ternary strict boundary upper bound: if the iid pairwise mistake event
is eventually empty, it has an exponential upper bound at every target rate.
-/
theorem approvalPairwiseError_hasExpUpperBoundWithConst_of_ternary_scores_down_zero_zero_zero
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hscore :
      ∀ signal,
        hiScore signal - loScore signal = 1 ∨
          hiScore signal - loScore signal = 0 ∨
          hiScore signal - loScore signal = -1)
    (hZeroZero :
      AppliedModelingLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = 0) =
        0)
    (hDownZero :
      AppliedModelingLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = -1) =
        0)
    (targetRate : ℝ) :
    HasExpUpperBoundWithConst
      (pairwiseScoringErrorProb law hiScore loScore)
      targetRate :=
  pairwiseScoringError_hasExpUpperBoundWithConst_of_support_pos
    law hiScore loScore
    (approvalTernaryScore_support_pos_of_down_zero_prob_zero
      law hiScore loScore hscore hZeroZero hDownZero)
    targetRate

/--
Expectation of a ternary score gap equals the probability of a `+1` gap minus
the probability of a `-1` gap.
-/
theorem pmfExp_ternary_gap_eq_prob_one_sub_prob_neg_one
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (gap : Signal → ℝ)
    (hgap :
      ∀ signal, gap signal = 1 ∨ gap signal = 0 ∨ gap signal = -1) :
    AppliedModelingLib.pmfExp law gap =
      AppliedModelingLib.pmfProb law (fun signal => gap signal = 1) -
        AppliedModelingLib.pmfProb law (fun signal => gap signal = -1) :=
  AppliedModelingLib.pmfExp_ternary_eq_prob_one_sub_prob_neg_one law gap hgap

/--
Expected K-approval score gap is the K-approval up probability minus the down
probability.
-/
theorem kApprovalScoreGap_pmfExp_eq_upProb_sub_downProb
    {n : ℕ} (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : ℕ)
    (hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n) :
    AppliedModelingLib.pmfExp law
        (fun π =>
          AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π hi -
            AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π lo) =
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K hi lo -
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K hi lo := by
  rw [pmfExp_ternary_gap_eq_prob_one_sub_prob_neg_one]
  · rw [← AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb_eq_score_gap_one,
      ← AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb_eq_score_gap_neg_one]
  · intro π
    exact AppliedModelingLib.SocialChoice.Ranking.kApprovalScore_gap_ternary K π hi lo

/--
Finite ternary approval trichotomy.  For any finite ternary score-gap law with
`pDown <= pUp`, either the source closed-form approval rate is the exact iid
pairwise exponential rate, or the strict one-sided boundary makes the iid
pairwise mistake event eventually empty.
-/
theorem approvalPairwiseError_exponentialRateCertificate_or_eventually_zero_of_ternary_scores
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
        pairwiseScoringErrorProb law hiScore loScore n = 0) := by
  classical
  by_cases hDown_pos : 0 < pDown
  · left
    exact
      approvalPairwiseError_exponentialRateCertificate_of_ternary_scores
        law hiScore loScore (lt_of_lt_of_le hDown_pos hle) hDown_pos
        hle hscore hUpProb hDownProb
  · have hpDown_nonneg : 0 ≤ pDown := by
      rw [← hDownProb]
      exact
        AppliedModelingLib.pmfProb_nonneg law
          (fun signal => hiScore signal - loScore signal = -1)
    have hpDown_zero : pDown = 0 :=
      le_antisymm (le_of_not_gt hDown_pos) hpDown_nonneg
    have hDownZero :
        AppliedModelingLib.pmfProb law
            (fun signal => hiScore signal - loScore signal = -1) =
          0 := by
      simpa [hpDown_zero] using hDownProb
    by_cases hZero_pos : 0 < pZero
    · left
      simpa [hpDown_zero] using
        approvalPairwiseError_exponentialRateCertificate_of_ternary_scores_down_zero
          law hiScore loScore hscore hUpProb hZeroProb hZero_pos hDownZero
    · have hpZero_nonneg : 0 ≤ pZero := by
        rw [← hZeroProb]
        exact
          AppliedModelingLib.pmfProb_nonneg law
            (fun signal => hiScore signal - loScore signal = 0)
      have hpZero_zero : pZero = 0 :=
        le_antisymm (le_of_not_gt hZero_pos) hpZero_nonneg
      right
      exact
        approvalPairwiseError_eventually_zero_of_ternary_scores_down_zero_zero_zero
          law hiScore loScore hscore
          (by simpa [hpZero_zero] using hZeroProb) hDownZero

/--
Finite ternary approval trichotomy as a single extended-rate statement.  The
extended rate is finite at the source closed form, or `⊤` when the strict
one-sided boundary makes the iid pairwise mistake event eventually empty.
-/
theorem approvalPairwiseError_hasExtendedExponentialRate_of_ternary_scores
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
    ∃ rate : WithTop ℝ,
      HasExtendedExponentialRate
        (pairwiseScoringErrorProb law hiScore loScore)
        rate := by
  rcases
      approvalPairwiseError_exponentialRateCertificate_or_eventually_zero_of_ternary_scores
        law hiScore loScore hle hscore hUpProb hDownProb hZeroProb with
    hfinite | hzero
  · exact ⟨(approvalPairwiseRate pUp pDown : WithTop ℝ),
      HasExtendedExponentialRate.finite hfinite.has_rate⟩
  · exact ⟨⊤, HasExtendedExponentialRate.infinite hzero⟩

/--
Exact K-approval ternary pairwise rates imply the corresponding pairwise error
probability tends to zero whenever the source closed-form rate is positive.
-/
theorem approvalPairwiseError_tendsto_zero_of_ternary_scores
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
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
    (hrate_pos : 0 < approvalPairwiseRate pUp pDown) :
    Filter.Tendsto
      (pairwiseScoringErrorProb law hiScore loScore)
      Filter.atTop (nhds 0) :=
  (approvalPairwiseError_exponentialRateCertificate_of_ternary_scores
    law hiScore loScore hUp hDown hle hscore hUpProb hDownProb)
    |>.tendsto_zero_of_pos_rate hrate_pos

/--
Exact ternary K-approval pairwise rates imply convergence to zero under the
paper's strict up/down separation condition.
-/
theorem approvalPairwiseError_tendsto_zero_of_ternary_scores_of_down_lt_up
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hle : pDown ≤ pUp)
    (hsum : pUp + pDown ≤ 1)
    (hlt : pDown < pUp)
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
        pDown) :
    Filter.Tendsto
      (pairwiseScoringErrorProb law hiScore loScore)
      Filter.atTop (nhds 0) :=
  approvalPairwiseError_tendsto_zero_of_ternary_scores
    law hiScore loScore hUp hDown hle hscore hUpProb hDownProb
    (approvalPairwiseRate_pos_of_down_lt_up hUp hDown hsum hlt)

/--
Exact K-approval pairwise rate for a finite ranking law.  The ternary score-gap
classification and the two nonzero-event identifications are discharged by the
generic K-approval API.
-/
theorem kApprovalPairwiseError_exponentialRateCertificate
    {n : ℕ} (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : ℕ)
    (hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hle : pDown ≤ pUp)
    (hUpProb :
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K hi lo = pUp)
    (hDownProb :
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K hi lo =
        pDown) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law
        (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π hi)
        (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π lo))
      (approvalPairwiseRate pUp pDown) := by
  classical
  refine
    approvalPairwiseError_exponentialRateCertificate_of_ternary_scores
      law
      (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π hi)
      (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π lo)
      hUp hDown hle ?_ ?_ ?_
  · intro π
    exact AppliedModelingLib.SocialChoice.Ranking.kApprovalScore_gap_ternary
      K π hi lo
  · rw [← hUpProb]
    exact
      (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb_eq_score_gap_one
        law K hi lo).symm
  · rw [← hDownProb]
    exact
      (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb_eq_score_gap_neg_one
        law K hi lo).symm

/--
Exact K-approval pairwise rate stated directly in terms of the ranking-law
up/down event probabilities.
-/
theorem kApprovalPairwiseError_exponentialRateCertificate_of_probabilities
    {n : ℕ} (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : ℕ)
    (hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (hUp :
      0 <
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K hi lo)
    (hDown :
      0 <
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K hi lo)
    (hle :
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K hi lo ≤
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K hi lo) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law
        (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π hi)
        (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π lo))
      (approvalPairwiseRate
        (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K hi lo)
        (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K hi lo)) :=
  kApprovalPairwiseError_exponentialRateCertificate
    law K hi lo hUp hDown hle rfl rfl

/--
Boundary K-approval pairwise exact rate stated directly from a finite ranking
law.  If the down-event has zero probability and the zero-gap event has
positive probability, the source closed form with `pDown = 0` is exact.
-/
theorem kApprovalPairwiseError_exponentialRateCertificate_down_zero
    {n : ℕ} (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : ℕ)
    (hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    {pUp pZero : ℝ}
    (hUpProb :
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K hi lo = pUp)
    (hZeroProb :
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairZeroProb law K hi lo =
        pZero)
    (hZero_pos : 0 < pZero)
    (hDownZero :
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K hi lo =
        0) :
    ExponentialRateCertificate
      (pairwiseScoringErrorProb law
        (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π hi)
        (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π lo))
      (approvalPairwiseRate pUp 0) := by
  classical
  refine
    approvalPairwiseError_exponentialRateCertificate_of_ternary_scores_down_zero
      law
      (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π hi)
      (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π lo)
      ?_ ?_ ?_ hZero_pos ?_
  · intro π
    exact AppliedModelingLib.SocialChoice.Ranking.kApprovalScore_gap_ternary
      K π hi lo
  · rw [← hUpProb]
    exact
      (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb_eq_score_gap_one
        law K hi lo).symm
  · rw [← hZeroProb]
    rfl
  · rw [← hDownZero]
    exact
      (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb_eq_score_gap_neg_one
        law K hi lo).symm

/--
Strict boundary K-approval pairwise errors are eventually empty directly from
a finite ranking law.
-/
theorem kApprovalPairwiseError_eventually_zero_down_zero_zero_zero
    {n : ℕ} (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : ℕ)
    (hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (hZeroZero :
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairZeroProb law K hi lo =
        0)
    (hDownZero :
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K hi lo =
        0) :
    ∀ᶠ sampleSize in Filter.atTop,
      pairwiseScoringErrorProb law
        (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π hi)
        (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π lo)
        sampleSize = 0 := by
  classical
  refine
    approvalPairwiseError_eventually_zero_of_ternary_scores_down_zero_zero_zero
      law
      (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π hi)
      (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π lo)
      ?_ ?_ ?_
  · intro π
    exact AppliedModelingLib.SocialChoice.Ranking.kApprovalScore_gap_ternary
      K π hi lo
  · simpa [AppliedModelingLib.SocialChoice.Ranking.kApprovalPairZeroProb] using
      hZeroZero
  · rw [← hDownZero]
    exact
      (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb_eq_score_gap_neg_one
        law K hi lo).symm

/--
Strict boundary K-approval pairwise errors admit an exponential upper bound at
every target rate directly from a finite ranking law.
-/
theorem kApprovalPairwiseError_hasExpUpperBoundWithConst_down_zero_zero_zero
    {n : ℕ} (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : ℕ)
    (hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (hZeroZero :
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairZeroProb law K hi lo =
        0)
    (hDownZero :
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K hi lo =
        0)
    (targetRate : ℝ) :
    HasExpUpperBoundWithConst
      (pairwiseScoringErrorProb law
        (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π hi)
        (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π lo))
      targetRate := by
  classical
  refine
    approvalPairwiseError_hasExpUpperBoundWithConst_of_ternary_scores_down_zero_zero_zero
      law
      (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π hi)
      (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π lo)
      ?_ ?_ ?_ targetRate
  · intro π
    exact AppliedModelingLib.SocialChoice.Ranking.kApprovalScore_gap_ternary
      K π hi lo
  · simpa [AppliedModelingLib.SocialChoice.Ranking.kApprovalPairZeroProb] using
      hZeroZero
  · rw [← hDownZero]
    exact
      (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb_eq_score_gap_neg_one
        law K hi lo).symm

/--
Finite K-approval pairwise trichotomy directly from a ranking law.  Under the
paper's weak up/down ordering, either the source closed-form approval rate is
the exact iid pairwise exponential rate, or the strict one-sided boundary makes
the iid pairwise mistake event eventually empty.
-/
theorem kApprovalPairwiseError_exponentialRateCertificate_or_eventually_zero
    {n : ℕ} (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : ℕ)
    (hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (hle :
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K hi lo ≤
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K hi lo) :
    ExponentialRateCertificate
        (pairwiseScoringErrorProb law
          (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π hi)
          (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π lo))
        (approvalPairwiseRate
          (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K hi lo)
          (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K hi lo)) ∨
      (∀ᶠ sampleSize in Filter.atTop,
        pairwiseScoringErrorProb law
          (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π hi)
          (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π lo)
          sampleSize = 0) := by
  classical
  refine
    approvalPairwiseError_exponentialRateCertificate_or_eventually_zero_of_ternary_scores
      (pZero :=
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairZeroProb law K hi lo)
      law
      (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π hi)
      (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π lo)
      hle ?_ ?_ ?_ ?_
  · intro π
    exact AppliedModelingLib.SocialChoice.Ranking.kApprovalScore_gap_ternary
      K π hi lo
  · exact
      (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb_eq_score_gap_one
        law K hi lo).symm
  · exact
      (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb_eq_score_gap_neg_one
        law K hi lo).symm
  · rfl

/--
Finite K-approval pairwise trichotomy directly from a ranking law as a single
extended-rate statement.
-/
theorem kApprovalPairwiseError_hasExtendedExponentialRate
    {n : ℕ} (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : ℕ)
    (hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (hle :
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K hi lo ≤
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K hi lo) :
    ∃ rate : WithTop ℝ,
      HasExtendedExponentialRate
        (pairwiseScoringErrorProb law
          (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π hi)
          (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π lo))
        rate := by
  rcases
      kApprovalPairwiseError_exponentialRateCertificate_or_eventually_zero
        law K hi lo hle with
    hfinite | hzero
  · exact
      ⟨(approvalPairwiseRate
          (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K hi lo)
          (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K hi lo) :
        WithTop ℝ),
        HasExtendedExponentialRate.finite hfinite.has_rate⟩
  · exact ⟨⊤, HasExtendedExponentialRate.infinite hzero⟩

/--
K-approval pairwise error probabilities for a finite ranking law tend to zero
whenever the source closed-form pairwise approval rate is positive.
-/
theorem kApprovalPairwiseError_tendsto_zero
    {n : ℕ} (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : ℕ)
    (hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hle : pDown ≤ pUp)
    (hUpProb :
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K hi lo = pUp)
    (hDownProb :
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K hi lo =
        pDown)
    (hrate_pos : 0 < approvalPairwiseRate pUp pDown) :
    Filter.Tendsto
      (pairwiseScoringErrorProb law
        (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π hi)
        (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π lo))
      Filter.atTop (nhds 0) :=
  (kApprovalPairwiseError_exponentialRateCertificate
    law K hi lo hUp hDown hle hUpProb hDownProb)
    |>.tendsto_zero_of_pos_rate hrate_pos

/--
K-approval pairwise error probabilities for a finite ranking law tend to zero
under the paper's strict up/down separation condition.
-/
theorem kApprovalPairwiseError_tendsto_zero_of_down_lt_up
    {n : ℕ} (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : ℕ)
    (hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hle : pDown ≤ pUp)
    (hsum : pUp + pDown ≤ 1)
    (hlt : pDown < pUp)
    (hUpProb :
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K hi lo = pUp)
    (hDownProb :
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K hi lo =
        pDown) :
    Filter.Tendsto
      (pairwiseScoringErrorProb law
        (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π hi)
        (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π lo))
      Filter.atTop (nhds 0) :=
  kApprovalPairwiseError_tendsto_zero
    law K hi lo hUp hDown hle hUpProb hDownProb
    (approvalPairwiseRate_pos_of_down_lt_up hUp hDown hsum hlt)

/--
K-approval pairwise error probabilities for a finite ranking law tend to zero
under strict separation of the actual ranking-law up/down probabilities.
-/
theorem kApprovalPairwiseError_tendsto_zero_of_probabilities_down_lt_up
    {n : ℕ} (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : ℕ)
    (hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (hUp :
      0 <
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K hi lo)
    (hDown :
      0 <
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K hi lo)
    (hlt :
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K hi lo <
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K hi lo) :
    Filter.Tendsto
      (pairwiseScoringErrorProb law
        (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π hi)
        (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π lo))
      Filter.atTop (nhds 0) :=
  kApprovalPairwiseError_tendsto_zero_of_down_lt_up
    law K hi lo hUp hDown hlt.le
    (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb_add_downProb_le_one
      law K hi lo)
    hlt rfl rfl

/--
Exact-rate certificate for a finite family of relevant ordered candidate pairs
under a finite ranking law and K-approval scores.  The relevant-pair index
avoids forcing self-pairs, whose K-approval up/down probabilities are zero.
-/
def kApprovalRelevantPairRateCertificate
    {n : ℕ} {Pair : Type*}
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : ℕ)
    (hi lo : Pair → AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (pUp pDown : Pair → ℝ)
    (hUp : ∀ pair, 0 < pUp pair)
    (hDown : ∀ pair, 0 < pDown pair)
    (hle : ∀ pair, pDown pair ≤ pUp pair)
    (hUpProb :
      ∀ pair,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K
            (hi pair) (lo pair) =
          pUp pair)
    (hDownProb :
      ∀ pair,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K
            (hi pair) (lo pair) =
          pDown pair) :
    FiniteErrorRateCertificate Pair where
  errorProb :=
    fun pair =>
      pairwiseScoringErrorProb law
        (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π (hi pair))
        (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π (lo pair))
  rate := fun pair => approvalPairwiseRate (pUp pair) (pDown pair)
  has_rate := by
    intro pair
    exact
      kApprovalPairwiseError_exponentialRateCertificate law K
        (hi pair) (lo pair)
        (hUp pair) (hDown pair) (hle pair)
        (hUpProb pair) (hDownProb pair)

/--
Exact-rate certificate for a finite family of relevant ordered candidate pairs,
stated directly in terms of the ranking-law K-approval up/down probabilities.
-/
def kApprovalRelevantPairRateCertificate_of_probabilities
    {n : ℕ} {Pair : Type*}
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : ℕ)
    (hi lo : Pair → AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (hUp :
      ∀ pair,
        0 <
          AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K
            (hi pair) (lo pair))
    (hDown :
      ∀ pair,
        0 <
          AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K
            (hi pair) (lo pair))
    (hle :
      ∀ pair,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K
            (hi pair) (lo pair) ≤
          AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K
            (hi pair) (lo pair)) :
    FiniteErrorRateCertificate Pair :=
  kApprovalRelevantPairRateCertificate
    law K hi lo
    (fun pair =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K
        (hi pair) (lo pair))
    (fun pair =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K
        (hi pair) (lo pair))
    hUp hDown hle (fun _ => rfl) (fun _ => rfl)

/--
Exact-rate certificate for a finite family of relevant ordered candidate pairs
in the K-approval zero-down boundary case.
-/
def kApprovalRelevantPairRateCertificate_down_zero
    {n : ℕ} {Pair : Type*}
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : ℕ)
    (hi lo : Pair → AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (pUp pZero : Pair → ℝ)
    (hUpProb :
      ∀ pair,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K
            (hi pair) (lo pair) =
          pUp pair)
    (hZeroProb :
      ∀ pair,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairZeroProb law K
            (hi pair) (lo pair) =
          pZero pair)
    (hZero_pos : ∀ pair, 0 < pZero pair)
    (hDownZero :
      ∀ pair,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K
            (hi pair) (lo pair) =
          0) :
    FiniteErrorRateCertificate Pair where
  errorProb :=
    fun pair =>
      pairwiseScoringErrorProb law
        (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π (hi pair))
        (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π (lo pair))
  rate := fun pair => approvalPairwiseRate (pUp pair) 0
  has_rate := by
    intro pair
    exact
      kApprovalPairwiseError_exponentialRateCertificate_down_zero law K
        (hi pair) (lo pair)
        (hUpProb pair) (hZeroProb pair) (hZero_pos pair)
        (hDownZero pair)

/-- The universal finite set is nonempty when its index type is nonempty. -/
def finiteUnivNonempty {ι : Type*} [Fintype ι] [Nonempty ι] :
    (Finset.univ : Finset ι).Nonempty :=
  ⟨Classical.choice inferInstance, by simp⟩

/--
Finite outcome-learning rate as the minimum of finitely many pivotal pairwise
rates.
-/
def finiteOutcomeLearningRate
    {Pair : Type*} [Fintype Pair] [Nonempty Pair]
    (rate : Pair → ℝ) : ℝ :=
  (Finset.univ : Finset Pair).inf' finiteUnivNonempty rate

/--
Finite outcome-learning rate in the extended source convention.  A pair that
is error-free after a positive sample has rate `⊤` and therefore cannot lower
the aggregate minimum when any finite-rate pair remains.
-/
def finiteOutcomeLearningExtendedRate
    {Pair : Type*} [Fintype Pair] [Nonempty Pair]
    (rate : Pair → WithTop ℝ) : WithTop ℝ :=
  (Finset.univ : Finset Pair).inf' finiteUnivNonempty rate

/-- The extended finite outcome-learning rate is bounded above by every pair rate. -/
theorem finiteOutcomeLearningExtendedRate_le
    {Pair : Type*} [Fintype Pair] [Nonempty Pair]
    (rate : Pair → WithTop ℝ) (pair : Pair) :
    finiteOutcomeLearningExtendedRate rate ≤ rate pair := by
  unfold finiteOutcomeLearningExtendedRate
  exact Finset.inf'_le rate (Finset.mem_univ pair)

/-- A finite outcome-learning rate is realized by some pivotal pair. -/
theorem finiteOutcomeLearningRate_exists_minimizer
    {Pair : Type*} [Fintype Pair] [Nonempty Pair]
    (rate : Pair → ℝ) :
    ∃ pair : Pair,
      finiteOutcomeLearningRate rate = rate pair ∧
        ∀ other : Pair, finiteOutcomeLearningRate rate ≤ rate other := by
  classical
  unfold finiteOutcomeLearningRate
  rcases Finset.exists_mem_eq_inf'
      (s := (Finset.univ : Finset Pair))
      finiteUnivNonempty rate with
    ⟨pair, _hmem, hpair⟩
  refine ⟨pair, hpair, ?_⟩
  intro other
  exact Finset.inf'_le rate (Finset.mem_univ other)

/-- The finite outcome-learning rate is bounded above by every pair rate. -/
theorem finiteOutcomeLearningRate_le
    {Pair : Type*} [Fintype Pair] [Nonempty Pair]
    (rate : Pair → ℝ) (pair : Pair) :
    finiteOutcomeLearningRate rate ≤ rate pair := by
  unfold finiteOutcomeLearningRate
  exact Finset.inf'_le rate (Finset.mem_univ pair)

/-- A displayed pair realizes the finite outcome-learning rate. -/
theorem finiteOutcomeLearningRate_eq_of_min_pair
    {Pair : Type*} [Fintype Pair] [Nonempty Pair]
    (rate : Pair → ℝ) (pairMin : Pair) {minRate : ℝ}
    (hrate_min : rate pairMin = minRate)
    (hrate_ge : ∀ pair, minRate ≤ rate pair) :
    finiteOutcomeLearningRate rate = minRate := by
  apply le_antisymm
  · simpa [hrate_min] using finiteOutcomeLearningRate_le rate pairMin
  · unfold finiteOutcomeLearningRate
    exact Finset.le_inf' _ _ (by
      intro pair _
      exact hrate_ge pair)

theorem finiteOutcomeLearningRate_const
    {Pair : Type*} [Fintype Pair] [Nonempty Pair] (rate : ℝ) :
    finiteOutcomeLearningRate (fun _ : Pair => rate) = rate := by
  unfold finiteOutcomeLearningRate
  apply le_antisymm
  · exact Finset.inf'_le (fun _ : Pair => rate)
      (show Classical.choice inferInstance ∈
        (Finset.univ : Finset Pair) by simp)
  · exact Finset.le_inf' _ _ (by
      intro pair _
      rfl)

/-- A finite minimum of strictly positive pair rates is strictly positive. -/
theorem finiteOutcomeLearningRate_pos
    {Pair : Type*} [Fintype Pair] [Nonempty Pair]
    {rate : Pair → ℝ}
    (hpos : ∀ pair, 0 < rate pair) :
    0 < finiteOutcomeLearningRate rate := by
  unfold finiteOutcomeLearningRate
  rw [Finset.lt_inf'_iff]
  intro pair _hpair
  exact hpos pair

/--
Pointwise finite-min aggregation: if every indexed pairwise error is bounded
by `exp (-n * rate pair)`, then the unweighted finite sum is bounded by the
number of indexed pairs times the bound at the realized minimum rate.
-/
theorem finiteErrorSum_le_card_mul_exp_of_pairwise_rate_bounds
    {Pair : Type*} [Fintype Pair] [Nonempty Pair]
    (errorProb : Pair → ℕ → ℝ) (rate : Pair → ℝ)
    (hbound :
      ∀ pair n,
        errorProb pair n ≤ Real.exp (-(n : ℝ) * rate pair))
    (n : ℕ) :
    (∑ pair : Pair, errorProb pair n) ≤
      (Fintype.card Pair : ℝ) *
        Real.exp (-(n : ℝ) * finiteOutcomeLearningRate rate) := by
  calc
    (∑ pair : Pair, errorProb pair n)
        ≤
        ∑ _pair : Pair,
          Real.exp (-(n : ℝ) * finiteOutcomeLearningRate rate) := by
          refine Finset.sum_le_sum ?_
          intro pair _
          have hrate_le : finiteOutcomeLearningRate rate ≤ rate pair :=
            finiteOutcomeLearningRate_le rate pair
          have hexp :
              Real.exp (-(n : ℝ) * rate pair) ≤
                Real.exp (-(n : ℝ) * finiteOutcomeLearningRate rate) :=
            Real.exp_le_exp.mpr (by
              have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
              have hmul :
                  (n : ℝ) * finiteOutcomeLearningRate rate ≤
                    (n : ℝ) * rate pair :=
                mul_le_mul_of_nonneg_left hrate_le hn_nonneg
              have hneg :
                  -((n : ℝ) * rate pair) ≤
                    -((n : ℝ) * finiteOutcomeLearningRate rate) :=
                neg_le_neg hmul
              simpa [neg_mul] using hneg)
          exact (hbound pair n).trans hexp
    _ =
        (Fintype.card Pair : ℝ) *
          Real.exp (-(n : ℝ) * finiteOutcomeLearningRate rate) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/--
Source-shaped Proposition 4 finite-`N` relevant-pair bound at the realized
finite outcome-learning rate, using the support-aware Proposition 2 pointwise
bound for every indexed pair.
-/
theorem finiteRelevantScoreGapErrorSum_le_card_mul_exp_at_finiteOutcomeLearningRate_of_mean_nonneg_pos_neg_atoms
    {Pair Candidate Signal : Type*} [Fintype Pair] [Nonempty Pair]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    (hmean :
      ∀ pair,
        0 ≤
          AppliedModelingLib.pmfExp law
            (fun signal => score (hi pair) signal - score (lo pair) signal))
    {aPos aNeg : Pair → Signal}
    (hmassPos : ∀ pair, 0 < (law (aPos pair)).toReal)
    (hgapPos :
      ∀ pair,
        0 < score (hi pair) (aPos pair) - score (lo pair) (aPos pair))
    (hmassNeg : ∀ pair, 0 < (law (aNeg pair)).toReal)
    (hgapNeg :
      ∀ pair,
        score (hi pair) (aNeg pair) - score (lo pair) (aNeg pair) < 0)
    (n : ℕ) :
    (∑ pair : Pair,
      finiteScoreGapPairwiseErrorProb law score (hi pair) (lo pair) n) ≤
      (Fintype.card Pair : ℝ) *
        Real.exp (-(n : ℝ) *
          finiteOutcomeLearningRate
            (fun pair : Pair =>
              pairwiseScoringRate law
                (score (hi pair)) (score (lo pair)))) := by
  exact
    finiteErrorSum_le_card_mul_exp_of_pairwise_rate_bounds
      (fun pair n =>
        finiteScoreGapPairwiseErrorProb law score (hi pair) (lo pair) n)
      (fun pair : Pair =>
        pairwiseScoringRate law (score (hi pair)) (score (lo pair)))
      (by
        intro pair n
        simpa [finiteScoreGapPairwiseErrorProb] using
          pairwiseScoringErrorProb_le_exp_neg_pairwiseScoringRate_of_mean_nonneg_pos_neg_atoms
            law (score (hi pair)) (score (lo pair))
            (hmean pair)
            (hmassPos pair) (hgapPos pair)
            (hmassNeg pair) (hgapNeg pair) n)
      n

/--
Full finite-support Proposition 4 finite-`N` relevant-pair bound.  The
pairwise source bound applies to every finite score-gap branch, so this needs
no two-sided score-gap premise.
-/
theorem finiteRelevantScoreGapErrorSum_le_card_mul_exp_at_finiteOutcomeLearningRate_of_mean_nonneg
    {Pair Candidate Signal : Type*} [Fintype Pair] [Nonempty Pair]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    (hmean :
      ∀ pair,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score (hi pair) signal - score (lo pair) signal))
    (n : ℕ) :
    (∑ pair : Pair,
      finiteScoreGapPairwiseErrorProb law score (hi pair) (lo pair) n) ≤
      (Fintype.card Pair : ℝ) *
        Real.exp (-(n : ℝ) *
          finiteOutcomeLearningRate
            (fun pair : Pair =>
              pairwiseScoringRate law
                (score (hi pair)) (score (lo pair)))) := by
  exact
    finiteErrorSum_le_card_mul_exp_of_pairwise_rate_bounds
      (fun pair n =>
        finiteScoreGapPairwiseErrorProb law score (hi pair) (lo pair) n)
      (fun pair : Pair =>
        pairwiseScoringRate law (score (hi pair)) (score (lo pair)))
      (by
        intro pair n
        simpa [finiteScoreGapPairwiseErrorProb] using
          pairwiseScoringErrorProb_le_exp_neg_pairwiseScoringRate_of_mean_nonneg
            law (score (hi pair)) (score (lo pair)) (hmean pair) n)
      n

/--
Source-shaped Proposition 4 finite-`N` W-selection upper bound in the paper's
coarse `M^2` form, at the realized finite outcome-learning rate.
-/
theorem crossTierScoreGapErrorSum_le_candidate_card_sq_mul_exp_at_finiteOutcomeLearningRate_of_mean_nonneg_pos_neg_atoms
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (winnerSet : Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (hmean :
      ∀ pair : CrossTierPair winnerSet,
        0 ≤
          AppliedModelingLib.pmfExp law
            (fun signal => score pair.hi signal - score pair.lo signal))
    {aPos aNeg : CrossTierPair winnerSet → Signal}
    (hmassPos : ∀ pair, 0 < (law (aPos pair)).toReal)
    (hgapPos :
      ∀ pair,
        0 < score pair.hi (aPos pair) - score pair.lo (aPos pair))
    (hmassNeg : ∀ pair, 0 < (law (aNeg pair)).toReal)
    (hgapNeg :
      ∀ pair,
        score pair.hi (aNeg pair) - score pair.lo (aNeg pair) < 0)
    (n : ℕ) :
    (∑ pair : CrossTierPair winnerSet,
      finiteScoreGapPairwiseErrorProb law score pair.hi pair.lo n) ≤
      (Fintype.card Candidate : ℝ) ^ 2 *
        Real.exp (-(n : ℝ) *
          finiteOutcomeLearningRate
            (fun pair : CrossTierPair winnerSet =>
              pairwiseScoringRate law
                (score pair.hi) (score pair.lo))) := by
  have hsum :=
    finiteRelevantScoreGapErrorSum_le_card_mul_exp_at_finiteOutcomeLearningRate_of_mean_nonneg_pos_neg_atoms
      (Pair := CrossTierPair winnerSet)
      (law := law) (score := score)
      (hi := fun pair : CrossTierPair winnerSet => pair.hi)
      (lo := fun pair : CrossTierPair winnerSet => pair.lo)
      hmean hmassPos hgapPos hmassNeg hgapNeg n
  have hcard_real :
      (Fintype.card (CrossTierPair winnerSet) : ℝ) ≤
        (Fintype.card Candidate : ℝ) ^ 2 := by
    exact_mod_cast crossTierPair_card_le_candidate_card_sq winnerSet
  exact hsum.trans
    (mul_le_mul_of_nonneg_right hcard_real (Real.exp_pos _).le)

/--
Pairwise exact-rate certificate for a finite family of K-approval score gaps,
with each pair's rate stated in the source closed form.
-/
def approvalPairwiseRateCertificate
    {Candidate Signal : Type*} [Fintype Candidate] [Fintype Signal]
    [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (pUp pDown : Candidate → Candidate → ℝ)
    (hUp : ∀ hi lo, 0 < pUp hi lo)
    (hDown : ∀ hi lo, 0 < pDown hi lo)
    (hsum : ∀ hi lo, pUp hi lo + pDown hi lo ≤ 1)
    (hmgf :
      ∀ hi lo z,
        finiteMGF law
            (fun signal => score hi signal - score lo signal) z =
          ternaryGapMGF (pUp hi lo) (pDown hi lo) z)
    (cramer :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapCramerCertificate law (score hi) (score lo)) :
    PairwiseErrorRateCertificate Candidate where
  errorProb := finiteScoreGapPairwiseErrorProb law score
  rate := fun hi lo => approvalPairwiseRate (pUp hi lo) (pDown hi lo)
  has_rate := by
    intro hi lo
    exact
      approvalPairwiseError_exponentialRateCertificate_of_cramer_ternary_mgf
        law (score hi) (score lo)
        (hUp hi lo) (hDown hi lo) (hsum hi lo)
        (hmgf hi lo) (cramer hi lo)

/--
Pairwise exact-rate certificate for a finite family of K-approval ternary score
gaps, with the pairwise exact rate discharged by finite iid ternary counting.
-/
def approvalPairwiseRateCertificate_of_ternary_scores
    {Candidate Signal : Type*} [Fintype Candidate] [Fintype Signal]
    [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (pUp pDown : Candidate → Candidate → ℝ)
    (hUp : ∀ hi lo, 0 < pUp hi lo)
    (hDown : ∀ hi lo, 0 < pDown hi lo)
    (hle : ∀ hi lo, pDown hi lo ≤ pUp hi lo)
    (hscore :
      ∀ hi lo signal,
        score hi signal - score lo signal = 1 ∨
          score hi signal - score lo signal = 0 ∨
          score hi signal - score lo signal = -1)
    (hUpProb :
      ∀ hi lo,
        AppliedModelingLib.pmfProb law
            (fun signal => score hi signal - score lo signal = 1) =
          pUp hi lo)
    (hDownProb :
      ∀ hi lo,
        AppliedModelingLib.pmfProb law
            (fun signal => score hi signal - score lo signal = -1) =
          pDown hi lo) :
    PairwiseErrorRateCertificate Candidate where
  errorProb := finiteScoreGapPairwiseErrorProb law score
  rate := fun hi lo => approvalPairwiseRate (pUp hi lo) (pDown hi lo)
  has_rate := by
    intro hi lo
    exact
      approvalPairwiseError_exponentialRateCertificate_of_ternary_scores
        law (score hi) (score lo)
        (hUp hi lo) (hDown hi lo) (hle hi lo)
        (hscore hi lo) (hUpProb hi lo) (hDownProb hi lo)

/--
Proposition 4 finite aggregation bridge.  Once every cross-tier pairwise error
probability has a certified exponential rate above `targetRate`, any
nonnegative finite weighted sum of those pairwise errors has an eventual
exponential upper bound at `targetRate`.
-/
theorem outcomeError_hasExpUpperBound_of_pairwise_rate_certificates
    {Candidate : Type*} [Fintype Candidate]
    (C : PairwiseErrorRateCertificate Candidate)
    {pairWeight : Candidate → Candidate → ℝ} {targetRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hrate : ∀ hi lo, targetRate < C.rate hi lo) :
    HasExpUpperBoundWithConst
      (C.aggregateError pairWeight) targetRate :=
  C.aggregateError_hasExpUpperBoundWithConst_of_lt hweight hrate

/--
Proposition 4 exact finite-aggregation theorem: if one positively weighted
pair realizes the minimum relevant pairwise rate and every other relevant pair
has rate at least that value, then the weighted outcome-error aggregate has
that exact exponential rate.
-/
theorem outcomeError_hasExponentialRate_of_pairwise_min_rate
    {Candidate : Type*} [Fintype Candidate] [DecidableEq Candidate]
    (C : PairwiseErrorRateCertificate Candidate)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min : C.rate hiMin loMin = minRate)
    (hrate_ge : ∀ hi lo, minRate ≤ C.rate hi lo) :
    HasExponentialRate (C.aggregateError pairWeight) minRate :=
  C.aggregateError_hasExponentialRate_of_min_pair
    hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Finite-support Proposition 4 envelope certificate.  For a proposed aggregate
rate `minRate`, every relevant score-gap pair with nonnegative mean is either
certified at a finite real rate at least `minRate` or eventually has zero
mistake probability.  This packages the Proposition 2 trichotomy for reuse by
aggregation and later randomized-scoring wrappers.
-/
def finiteScoreGapRelevantPairRateEnvelopeCertificate_of_mean_nonneg
    {Pair Candidate Signal : Type*} [Fintype Pair]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    {minRate : ℝ}
    (hmean :
      ∀ pair,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal =>
            score (hi pair) signal - score (lo pair) signal))
    (hsource_rate_ge :
      ∀ pair,
        minRate ≤
          pairwiseScoringRate law
            (score (hi pair)) (score (lo pair)))
    (hzero_rate_ge :
      ∀ pair pZero,
        AppliedModelingLib.pmfProb law
            (fun signal =>
              score (hi pair) signal - score (lo pair) signal = 0) =
          pZero →
        0 < pZero →
          minRate ≤ -Real.log pZero) :
    FiniteErrorRateEnvelopeCertificate Pair minRate where
  errorProb := fun pair sampleSize =>
    finiteScoreGapPairwiseErrorProb law score
      (hi pair) (lo pair) sampleSize
  component := by
    intro pair
    rcases
        pairwiseScoringError_exponentialRateCertificate_or_boundary_of_mean_nonneg
          law (score (hi pair)) (score (lo pair)) (hmean pair) with
      hsource | hboundary
    · left
      refine
        ⟨pairwiseScoringRate law
            (score (hi pair)) (score (lo pair)),
          hsource_rate_ge pair, ?_⟩
      simpa [finiteScoreGapPairwiseErrorProb] using hsource
    · rcases hboundary with hzero | hstrict
      · rcases hzero with ⟨pZero, hZeroProb, hZero_pos, hcert⟩
        left
        refine ⟨-Real.log pZero, ?_, ?_⟩
        · exact hzero_rate_ge pair pZero hZeroProb hZero_pos
        · simpa [finiteScoreGapPairwiseErrorProb] using hcert
      · right
        simpa [finiteScoreGapPairwiseErrorProb] using hstrict

/--
Proposition 4 exact finite aggregation from the finite-support Proposition 2
trichotomy.  One positive-weight relevant pair supplies the exact minimum
rate.  Every relevant score-gap pair has nonnegative mean and therefore is
either certified at the source pairwise scoring rate, certified in the
zero-gap boundary at `-log pZero`, or eventually zero in the strict one-sided
boundary case.
-/
theorem outcomeError_hasExponentialRate_of_relevant_pairs_finite_support_exact_or_boundary_or_eventually_zero
    {Pair Candidate Signal : Type*} [Fintype Pair] [DecidableEq Pair]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    (hmean :
      ∀ pair,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal =>
            score (hi pair) signal - score (lo pair) signal))
    {pairWeight : Pair → ℝ} {minRate : ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (pairMin : Pair)
    (hweight_pos : 0 < pairWeight pairMin)
    (hpairMin_exact :
      ExponentialRateCertificate
        (finiteScoreGapPairwiseErrorProb law score
          (hi pairMin) (lo pairMin))
        minRate)
    (hsource_rate_ge :
      ∀ pair,
        minRate ≤
          pairwiseScoringRate law
            (score (hi pair)) (score (lo pair)))
    (hzero_rate_ge :
      ∀ pair pZero,
        AppliedModelingLib.pmfProb law
            (fun signal =>
              score (hi pair) signal - score (lo pair) signal = 0) =
          pZero →
        0 < pZero →
          minRate ≤ -Real.log pZero) :
    HasExponentialRate
      (fun sampleSize =>
        ∑ pair : Pair,
          pairWeight pair *
            finiteScoreGapPairwiseErrorProb law score
              (hi pair) (lo pair) sampleSize)
      minRate := by
  let C :=
    finiteScoreGapRelevantPairRateEnvelopeCertificate_of_mean_nonneg
      law score hi lo hmean hsource_rate_ge hzero_rate_ge
  have hmin :
      ExponentialRateCertificate (C.errorProb pairMin) minRate := by
    simpa [C, finiteScoreGapRelevantPairRateEnvelopeCertificate_of_mean_nonneg]
      using hpairMin_exact
  simpa [C, finiteScoreGapRelevantPairRateEnvelopeCertificate_of_mean_nonneg,
    FiniteErrorRateEnvelopeCertificate.aggregateError] using
    C.aggregateError_hasExponentialRate_of_min_component
      hweight pairMin hweight_pos hmin

/--
Automatic Proposition 4 finite aggregation from the finite-support Proposition
2 trichotomy.  If every relevant pair has nonnegative expected score gap, then
a positive-weight finite aggregate of the relevant pairwise errors either has
some exact finite exponential rate or is eventually zero.
-/
theorem outcomeError_hasExponentialRate_or_eventually_zero_of_relevant_pairs_finite_support_trichotomy
    {Pair Candidate Signal : Type*} [Fintype Pair] [DecidableEq Pair]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    (hmean :
      ∀ pair,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal =>
            score (hi pair) signal - score (lo pair) signal))
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hweight_pos : ∀ pair, 0 < pairWeight pair) :
    (∃ minRate : ℝ,
      HasExponentialRate
        (fun sampleSize =>
          ∑ pair : Pair,
            pairWeight pair *
              finiteScoreGapPairwiseErrorProb law score
                (hi pair) (lo pair) sampleSize)
        minRate) ∨
      (∀ᶠ sampleSize in Filter.atTop,
        (∑ pair : Pair,
          pairWeight pair *
            finiteScoreGapPairwiseErrorProb law score
              (hi pair) (lo pair) sampleSize) = 0) := by
  let errorProb : Pair → ℕ → ℝ :=
    fun pair sampleSize =>
      finiteScoreGapPairwiseErrorProb law score
        (hi pair) (lo pair) sampleSize
  have hcase :
      ∀ pair : Pair,
        (∃ rate_i : ℝ,
          ExponentialRateCertificate (errorProb pair) rate_i) ∨
          (∀ᶠ sampleSize in Filter.atTop,
            errorProb pair sampleSize = 0) := by
    intro pair
    rcases
        pairwiseScoringError_exponentialRateCertificate_or_boundary_of_mean_nonneg
          law (score (hi pair)) (score (lo pair)) (hmean pair) with
      hsource | hboundary
    · left
      exact
        ⟨pairwiseScoringRate law
            (score (hi pair)) (score (lo pair)),
          by simpa [errorProb, finiteScoreGapPairwiseErrorProb] using hsource⟩
    · rcases hboundary with hzero | hstrict
      · rcases hzero with ⟨pZero, _hZeroProb, _hZero_pos, hcert⟩
        left
        exact
          ⟨-Real.log pZero,
            by simpa [errorProb, finiteScoreGapPairwiseErrorProb] using hcert⟩
      · right
        simpa [errorProb, finiteScoreGapPairwiseErrorProb] using hstrict
  simpa [errorProb] using
    finite_weighted_sum_hasExponentialRate_or_eventually_zero_of_cert_or_eventually_zero
      (p := errorProb) (weight := pairWeight)
      hweight hweight_pos hcase

/--
Automatic Proposition 4 finite aggregation as a single extended-rate theorem.
The `⊤` branch is the strict boundary case where every relevant pairwise error
is eventually zero.
-/
theorem outcomeError_hasExtendedExponentialRate_of_relevant_pairs_finite_support_trichotomy
    {Pair Candidate Signal : Type*} [Fintype Pair] [DecidableEq Pair]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    (hmean :
      ∀ pair,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal =>
            score (hi pair) signal - score (lo pair) signal))
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hweight_pos : ∀ pair, 0 < pairWeight pair) :
    ∃ rate : WithTop ℝ,
      HasExtendedExponentialRate
        (fun sampleSize =>
          ∑ pair : Pair,
            pairWeight pair *
              finiteScoreGapPairwiseErrorProb law score
                (hi pair) (lo pair) sampleSize)
        rate := by
  rcases
      outcomeError_hasExponentialRate_or_eventually_zero_of_relevant_pairs_finite_support_trichotomy
        law score hi lo hmean hweight hweight_pos with
    hfinite | hzero
  · rcases hfinite with ⟨rate, hrate⟩
    exact ⟨(rate : WithTop ℝ),
      HasExtendedExponentialRate.finite hrate⟩
  · exact ⟨⊤, HasExtendedExponentialRate.infinite hzero⟩

/--
Exact extended-source-rate form of Proposition 4.  The aggregate rate is the
finite minimum of the pairwise extended rates; when every pair is eventually
error-free, that minimum is `⊤`.
-/
theorem outcomeError_hasExtendedExponentialRate_at_finiteOutcomeLearningExtendedRate_of_relevant_pairs_finite_support
    {Pair Candidate Signal : Type*} [Fintype Pair] [Nonempty Pair]
    [DecidableEq Pair] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    (hmean :
      ∀ pair,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal =>
            score (hi pair) signal - score (lo pair) signal))
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hweight_pos : ∀ pair, 0 < pairWeight pair) :
    HasExtendedExponentialRate
      (fun sampleSize =>
        ∑ pair : Pair,
          pairWeight pair *
            finiteScoreGapPairwiseErrorProb law score
              (hi pair) (lo pair) sampleSize)
      (finiteOutcomeLearningExtendedRate
        (fun pair : Pair =>
          pairwiseScoringExtendedRate law
            (score (hi pair)) (score (lo pair)))) := by
  classical
  let errorProb : Pair → ℕ → ℝ :=
    fun pair sampleSize =>
      finiteScoreGapPairwiseErrorProb law score
        (hi pair) (lo pair) sampleSize
  let sourceRate : Pair → WithTop ℝ :=
    fun pair =>
      pairwiseScoringExtendedRate law
        (score (hi pair)) (score (lo pair))
  have hcase :
      ∀ pair : Pair,
        (∃ rate_i : ℝ,
          ExponentialRateCertificate (errorProb pair) rate_i ∧
            sourceRate pair = (rate_i : WithTop ℝ)) ∨
          ((∀ᶠ sampleSize in Filter.atTop,
            errorProb pair sampleSize = 0) ∧ sourceRate pair = ⊤) := by
    intro pair
    rcases
        pairwiseScoringError_extendedRateCertificate_or_eventually_zero_of_mean_nonneg
          law (score (hi pair)) (score (lo pair)) (hmean pair) with
      hfinite | hzero
    · left
      rcases hfinite with ⟨rate_i, hcert, hrate⟩
      exact ⟨rate_i,
        by simpa [errorProb, finiteScoreGapPairwiseErrorProb] using hcert,
        by simpa [sourceRate] using hrate⟩
    · right
      exact ⟨by simpa [errorProb, finiteScoreGapPairwiseErrorProb] using hzero.1,
        by simpa [sourceRate] using hzero.2⟩
  by_cases hfinite_exists :
      ∃ pair : Pair, ∃ rate_i : ℝ,
        ExponentialRateCertificate (errorProb pair) rate_i ∧
          sourceRate pair = (rate_i : WithTop ℝ)
  · have hcase_for_sum :
        ∀ pair : Pair,
          (∃ rate_i : ℝ,
            ExponentialRateCertificate (errorProb pair) rate_i ∧
              sourceRate pair = (rate_i : WithTop ℝ)) ∨
            (∀ᶠ sampleSize in Filter.atTop,
              errorProb pair sampleSize = 0) := by
      intro pair
      rcases hcase pair with hfinite | hzero
      · exact Or.inl hfinite
      · exact Or.inr hzero.1
    rcases
        finite_weighted_sum_hasExponentialRate_with_min_component_payload_or_eventually_zero_of_cert_or_eventually_zero
          (p := errorProb) (weight := pairWeight)
          (fun pair rate_i => sourceRate pair = (rate_i : WithTop ℝ))
          hweight hweight_pos hcase_for_sum with
      hsum | hsum_zero
    · rcases hsum with
        ⟨pairMin, minRate, hmin_cert, hmin_payload, hcase_ge, hsum_rate⟩
      have hrate_eq :
          finiteOutcomeLearningExtendedRate sourceRate =
            (minRate : WithTop ℝ) := by
        apply le_antisymm
        · calc
            finiteOutcomeLearningExtendedRate sourceRate ≤ sourceRate pairMin :=
              finiteOutcomeLearningExtendedRate_le sourceRate pairMin
            _ = (minRate : WithTop ℝ) := hmin_payload
        · unfold finiteOutcomeLearningExtendedRate
          apply Finset.le_inf'
          intro pair _
          rcases hcase_ge pair with hfinite | hzero
          · rcases hfinite with ⟨rate_i, hmin_le_rate_i, hcert_i⟩
            rcases hcase pair with hsource | hsource_zero
            · rcases hsource with ⟨sourceRate_i, hsource_cert, hsource_eq⟩
              have hrate_i_eq : sourceRate_i = rate_i :=
                HasExponentialRate.unique hsource_cert.has_rate hcert_i.has_rate
              rw [hsource_eq, hrate_i_eq]
              exact WithTop.coe_le_coe.mpr hmin_le_rate_i
            · have hfalse : False := by
                rcases (hcert_i.eventually_pos.and hsource_zero.1).exists with
                  ⟨sampleSize, hpos, hzero⟩
                exact (ne_of_gt hpos) hzero
              exact hfalse.elim
          · rcases hcase pair with hsource | hsource_zero
            · rcases hsource with ⟨sourceRate_i, hsource_cert, _hsource_eq⟩
              have hfalse : False := by
                rcases (hsource_cert.eventually_pos.and hzero).exists with
                  ⟨sampleSize, hpos, hzero_at⟩
                exact (ne_of_gt hpos) hzero_at
              exact hfalse.elim
            · rw [hsource_zero.2]
              exact le_top
      rw [show
        finiteOutcomeLearningExtendedRate
          (fun pair : Pair =>
            pairwiseScoringExtendedRate law
              (score (hi pair)) (score (lo pair))) =
          finiteOutcomeLearningExtendedRate sourceRate by rfl,
        hrate_eq]
      exact HasExtendedExponentialRate.finite (by
        simpa [errorProb] using hsum_rate)
    · exfalso
      rcases hfinite_exists with ⟨pair, rate_i, hcert, _hrate⟩
      have herror_nonneg : ∀ pair sampleSize, 0 ≤ errorProb pair sampleSize := by
        intro pair sampleSize
        unfold errorProb finiteScoreGapPairwiseErrorProb
        unfold pairwiseScoringErrorProb finiteIidScoreGapLeftTailProb
        exact
          AppliedModelingLib.pmfProb_nonneg
            (AppliedModelingLib.pmfProduct (Fin sampleSize) Signal law) _
      rcases (hcert.eventually_pos.and hsum_zero).exists with
        ⟨sampleSize, hpos, hzero⟩
      have hterm_pos :
          0 < pairWeight pair * errorProb pair sampleSize :=
        mul_pos (hweight_pos pair) hpos
      have hterm_le :
          pairWeight pair * errorProb pair sampleSize ≤
            ∑ other : Pair, pairWeight other * errorProb other sampleSize := by
        exact Finset.single_le_sum
          (fun other _ => mul_nonneg (hweight other) (herror_nonneg other sampleSize))
          (Finset.mem_univ pair)
      rw [hzero] at hterm_le
      exact (not_lt_of_ge hterm_le) hterm_pos
  · have hzero_all :
        ∀ pair : Pair,
          ∀ᶠ sampleSize in Filter.atTop,
            errorProb pair sampleSize = 0 := by
      intro pair
      rcases hcase pair with hfinite | hzero
      · exfalso
        rcases hfinite with ⟨rate_i, hcert, hrate⟩
        exact hfinite_exists ⟨pair, rate_i, hcert, hrate⟩
      · exact hzero.1
    have hsource_top : ∀ pair : Pair, sourceRate pair = ⊤ := by
      intro pair
      rcases hcase pair with hfinite | hzero
      · exfalso
        rcases hfinite with ⟨rate_i, hcert, hrate⟩
        exact hfinite_exists ⟨pair, rate_i, hcert, hrate⟩
      · exact hzero.2
    have hsum_zero :
        ∀ᶠ sampleSize in Filter.atTop,
          (∑ pair : Pair, pairWeight pair * errorProb pair sampleSize) = 0 :=
      finite_weighted_sum_eventually_zero
        (p := errorProb) (weight := pairWeight) hzero_all
    have hrate_top : finiteOutcomeLearningExtendedRate sourceRate = ⊤ := by
      apply le_antisymm le_top
      unfold finiteOutcomeLearningExtendedRate
      apply Finset.le_inf'
      intro pair _
      rw [hsource_top pair]
    rw [show
      finiteOutcomeLearningExtendedRate
        (fun pair : Pair =>
          pairwiseScoringExtendedRate law
            (score (hi pair)) (score (lo pair))) =
        finiteOutcomeLearningExtendedRate sourceRate by rfl,
      hrate_top]
    exact HasExtendedExponentialRate.infinite (by simpa [errorProb] using hsum_zero)

/--
Proposition 4 exact finite aggregation specialized to K-approval over the
finite set of relevant ordered pairs.  The input probabilities are the source
up/down events from Proposition 3, and the conclusion is the exact
minimum-rate aggregate over those relevant pairs.
-/
theorem outcomeError_hasExponentialRate_of_kApproval_relevant_pairs
    {n : ℕ} {Pair : Type*} [Fintype Pair] [DecidableEq Pair]
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : ℕ)
    (hi lo : Pair → AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (pUp pDown : Pair → ℝ)
    (hUp : ∀ pair, 0 < pUp pair)
    (hDown : ∀ pair, 0 < pDown pair)
    (hle : ∀ pair, pDown pair ≤ pUp pair)
    (hUpProb :
      ∀ pair,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K
            (hi pair) (lo pair) =
          pUp pair)
    (hDownProb :
      ∀ pair,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K
            (hi pair) (lo pair) =
          pDown pair)
    {pairWeight : Pair → ℝ} {minRate : ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (pairMin : Pair)
    (hweight_pos : 0 < pairWeight pairMin)
    (hrate_min :
      approvalPairwiseRate (pUp pairMin) (pDown pairMin) = minRate)
    (hrate_ge :
      ∀ pair, minRate ≤ approvalPairwiseRate (pUp pair) (pDown pair)) :
    HasExponentialRate
      ((kApprovalRelevantPairRateCertificate law K hi lo pUp pDown
          hUp hDown hle hUpProb hDownProb).aggregateError pairWeight)
      minRate :=
  (kApprovalRelevantPairRateCertificate law K hi lo pUp pDown
    hUp hDown hle hUpProb hDownProb)
    |>.aggregateError_hasExponentialRate_of_min_component
      hweight pairMin hweight_pos hrate_min hrate_ge

/--
K-approval relevant-pair envelope certificate.  Relative to a proposed
aggregate rate `minRate`, each relevant pair either has the source closed-form
approval rate at least `minRate`, or its K-approval pairwise mistake
probability is eventually zero in the strict boundary case.
-/
def kApprovalRelevantPairRateEnvelopeCertificate
    {n : ℕ} {Pair : Type*} [Fintype Pair]
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : ℕ)
    (hi lo : Pair → AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    {minRate : ℝ}
    (hle :
      ∀ pair,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K
            (hi pair) (lo pair) ≤
          AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K
            (hi pair) (lo pair))
    (hrate_ge :
      ∀ pair,
        minRate ≤
          approvalPairwiseRate
            (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K
              (hi pair) (lo pair))
            (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K
              (hi pair) (lo pair))) :
    FiniteErrorRateEnvelopeCertificate Pair minRate where
  errorProb := fun pair sampleSize =>
    pairwiseScoringErrorProb law
      (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π (hi pair))
      (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π (lo pair))
      sampleSize
  component := by
    intro pair
    rcases
        kApprovalPairwiseError_exponentialRateCertificate_or_eventually_zero
          law K (hi pair) (lo pair) (hle pair) with
      hcert | hzero
    · left
      refine
        ⟨approvalPairwiseRate
            (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K
              (hi pair) (lo pair))
            (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K
              (hi pair) (lo pair)),
          hrate_ge pair, ?_⟩
      simpa using hcert
    · right
      simpa using hzero

/--
Proposition 4 exact finite aggregation for K-approval with mixed pairwise
boundary behavior.  The positively weighted pivotal pair has an exact source
approval-rate certificate and realizes `minRate`; every other relevant pair
either has the source closed-form exact rate at least `minRate` by the finite
K-approval trichotomy, or is a strict-boundary pair whose error is eventually
zero.
-/
theorem outcomeError_hasExponentialRate_of_kApproval_relevant_pairs_exact_or_eventually_zero
    {n : ℕ} {Pair : Type*} [Fintype Pair] [DecidableEq Pair]
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : ℕ)
    (hi lo : Pair → AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (hle :
      ∀ pair,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K
            (hi pair) (lo pair) ≤
          AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K
            (hi pair) (lo pair))
    {pairWeight : Pair → ℝ} {minRate : ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (pairMin : Pair)
    (hweight_pos : 0 < pairWeight pairMin)
    (hpairMin_exact :
      ExponentialRateCertificate
        (pairwiseScoringErrorProb law
          (fun π =>
            AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π (hi pairMin))
          (fun π =>
            AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π (lo pairMin)))
        (approvalPairwiseRate
          (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K
            (hi pairMin) (lo pairMin))
          (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K
            (hi pairMin) (lo pairMin))))
    (hrate_min :
      approvalPairwiseRate
          (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K
            (hi pairMin) (lo pairMin))
          (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K
            (hi pairMin) (lo pairMin)) =
        minRate)
    (hrate_ge :
      ∀ pair,
        minRate ≤
          approvalPairwiseRate
            (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K
              (hi pair) (lo pair))
            (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K
              (hi pair) (lo pair))) :
    HasExponentialRate
      (fun sampleSize =>
        ∑ pair : Pair,
          pairWeight pair *
            pairwiseScoringErrorProb law
              (fun π =>
                AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π (hi pair))
              (fun π =>
                AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π (lo pair))
              sampleSize)
      minRate := by
  let C :=
    kApprovalRelevantPairRateEnvelopeCertificate
      law K hi lo hle hrate_ge
  have hmin :
      ExponentialRateCertificate (C.errorProb pairMin) minRate := by
    simpa [C, kApprovalRelevantPairRateEnvelopeCertificate, hrate_min]
      using hpairMin_exact
  simpa [C, kApprovalRelevantPairRateEnvelopeCertificate,
    FiniteErrorRateEnvelopeCertificate.aggregateError] using
    C.aggregateError_hasExponentialRate_of_min_component
      hweight pairMin hweight_pos hmin

/--
Automatic K-approval Proposition 4 aggregation from the finite K-approval
pairwise trichotomy.  With positive aggregate weights, the relevant-pair
aggregate either has some exact finite exponential rate or is eventually zero.
-/
theorem outcomeError_hasExponentialRate_or_eventually_zero_of_kApproval_relevant_pairs_trichotomy
    {n : ℕ} {Pair : Type*} [Fintype Pair] [DecidableEq Pair]
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : ℕ)
    (hi lo : Pair → AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (hle :
      ∀ pair,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K
            (hi pair) (lo pair) ≤
          AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K
            (hi pair) (lo pair))
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hweight_pos : ∀ pair, 0 < pairWeight pair) :
    (∃ minRate : ℝ,
      HasExponentialRate
        (fun sampleSize =>
          ∑ pair : Pair,
            pairWeight pair *
              pairwiseScoringErrorProb law
                (fun π =>
                  AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π (hi pair))
                (fun π =>
                  AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π (lo pair))
                sampleSize)
        minRate) ∨
      (∀ᶠ sampleSize in Filter.atTop,
        (∑ pair : Pair,
          pairWeight pair *
            pairwiseScoringErrorProb law
              (fun π =>
                AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π (hi pair))
              (fun π =>
                AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π (lo pair))
              sampleSize) = 0) := by
  let errorProb : Pair → ℕ → ℝ :=
    fun pair sampleSize =>
      pairwiseScoringErrorProb law
        (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π (hi pair))
        (fun π => AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π (lo pair))
        sampleSize
  have hcase :
      ∀ pair : Pair,
        (∃ rate_i : ℝ,
          ExponentialRateCertificate (errorProb pair) rate_i) ∨
          (∀ᶠ sampleSize in Filter.atTop,
            errorProb pair sampleSize = 0) := by
    intro pair
    rcases
        kApprovalPairwiseError_exponentialRateCertificate_or_eventually_zero
          law K (hi pair) (lo pair) (hle pair) with
      hcert | hzero
    · left
      exact
        ⟨approvalPairwiseRate
            (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K
              (hi pair) (lo pair))
            (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K
              (hi pair) (lo pair)),
          by simpa [errorProb] using hcert⟩
    · right
      simpa [errorProb] using hzero
  simpa [errorProb] using
    finite_weighted_sum_hasExponentialRate_or_eventually_zero_of_cert_or_eventually_zero
      (p := errorProb) (weight := pairWeight)
      hweight hweight_pos hcase

/--
Automatic K-approval Proposition 4 aggregation as a single extended-rate
statement.  The `⊤` branch records strict-boundary eventual zero error.
-/
theorem outcomeError_hasExtendedExponentialRate_of_kApproval_relevant_pairs_trichotomy
    {n : ℕ} {Pair : Type*} [Fintype Pair] [DecidableEq Pair]
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : ℕ)
    (hi lo : Pair → AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (hle :
      ∀ pair,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K
            (hi pair) (lo pair) ≤
          AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K
            (hi pair) (lo pair))
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hweight_pos : ∀ pair, 0 < pairWeight pair) :
    ∃ rate : WithTop ℝ,
      HasExtendedExponentialRate
        (fun sampleSize =>
          ∑ pair : Pair,
            pairWeight pair *
              pairwiseScoringErrorProb law
                (fun π =>
                  AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π (hi pair))
                (fun π =>
                  AppliedModelingLib.SocialChoice.Ranking.kApprovalScore K π (lo pair))
                sampleSize)
        rate := by
  rcases
      outcomeError_hasExponentialRate_or_eventually_zero_of_kApproval_relevant_pairs_trichotomy
        law K hi lo hle hweight hweight_pos with
    hfinite | hzero
  · rcases hfinite with ⟨rate, hrate⟩
    exact ⟨(rate : WithTop ℝ),
      HasExtendedExponentialRate.finite hrate⟩
  · exact ⟨⊤, HasExtendedExponentialRate.infinite hzero⟩

/--
Automatic randomized K-approval relevant-pair aggregation.  For the actual
randomized one-voter sampling law, if every relevant pair has nonnegative
mixed expected K-approval score gap, then the finite weighted aggregate of
pairwise randomized K-approval mistakes either has an exact finite exponential
rate or is eventually zero.  This is the Theorem 2 aggregate counterpart to
the positive-probability exact-rate certificate.
-/
theorem randomizedKApprovalOutcomeError_hasExponentialRate_or_eventually_zero_of_mixed_expected_gap_nonneg
    {n : ℕ} {Rule Pair : Type*}
    [Fintype Rule] [DecidableEq Rule] [Fintype Pair] [DecidableEq Pair]
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hi lo : Pair → AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hmean :
      ∀ pair,
        0 ≤
          AppliedModelingLib.pmfExp
            (randomizedScoringSamplingLaw law weight hweight hsum)
            (fun signal : Rule × AppliedModelingLib.SocialChoice.Ranking.Ranking n =>
              AppliedModelingLib.SocialChoice.Ranking.kApprovalScore
                  (K signal.1) signal.2 (hi pair) -
                AppliedModelingLib.SocialChoice.Ranking.kApprovalScore
                  (K signal.1) signal.2 (lo pair)))
    {pairWeight : Pair → ℝ}
    (hpairWeight : ∀ pair, 0 ≤ pairWeight pair)
    (hpairWeight_pos : ∀ pair, 0 < pairWeight pair) :
    (∃ minRate : ℝ,
      HasExponentialRate
        (fun sampleSize =>
          ∑ pair : Pair,
            pairWeight pair *
              pairwiseScoringErrorProb
                (randomizedScoringSamplingLaw law weight hweight hsum)
                (fun signal : Rule × AppliedModelingLib.SocialChoice.Ranking.Ranking n =>
                  AppliedModelingLib.SocialChoice.Ranking.kApprovalScore
                    (K signal.1) signal.2 (hi pair))
                (fun signal : Rule × AppliedModelingLib.SocialChoice.Ranking.Ranking n =>
                  AppliedModelingLib.SocialChoice.Ranking.kApprovalScore
                    (K signal.1) signal.2 (lo pair))
                sampleSize)
        minRate) ∨
      (∀ᶠ sampleSize in Filter.atTop,
        (∑ pair : Pair,
          pairWeight pair *
            pairwiseScoringErrorProb
              (randomizedScoringSamplingLaw law weight hweight hsum)
              (fun signal : Rule × AppliedModelingLib.SocialChoice.Ranking.Ranking n =>
                AppliedModelingLib.SocialChoice.Ranking.kApprovalScore
                  (K signal.1) signal.2 (hi pair))
              (fun signal : Rule × AppliedModelingLib.SocialChoice.Ranking.Ranking n =>
                AppliedModelingLib.SocialChoice.Ranking.kApprovalScore
                  (K signal.1) signal.2 (lo pair))
              sampleSize) = 0) := by
  let randomizedLaw :
      PMF (Rule × AppliedModelingLib.SocialChoice.Ranking.Ranking n) :=
    randomizedScoringSamplingLaw law weight hweight hsum
  let score :
      AppliedModelingLib.SocialChoice.Ranking.Candidate n →
        Rule × AppliedModelingLib.SocialChoice.Ranking.Ranking n → ℝ :=
    fun candidate signal =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalScore
        (K signal.1) signal.2 candidate
  simpa [randomizedLaw, score] using
    outcomeError_hasExponentialRate_or_eventually_zero_of_relevant_pairs_finite_support_trichotomy
      (Pair := Pair)
      randomizedLaw
      score
      hi lo
      (by simpa [randomizedLaw, score] using hmean)
      (pairWeight := pairWeight)
      hpairWeight hpairWeight_pos

/--
Automatic randomized K-approval relevant-pair aggregation as a single
extended-rate statement for the actual randomized one-voter sampling law.
-/
theorem randomizedKApprovalOutcomeError_hasExtendedExponentialRate_of_mixed_expected_gap_nonneg
    {n : ℕ} {Rule Pair : Type*}
    [Fintype Rule] [DecidableEq Rule] [Fintype Pair] [DecidableEq Pair]
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hi lo : Pair → AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hmean :
      ∀ pair,
        0 ≤
          AppliedModelingLib.pmfExp
            (randomizedScoringSamplingLaw law weight hweight hsum)
            (fun signal : Rule × AppliedModelingLib.SocialChoice.Ranking.Ranking n =>
              AppliedModelingLib.SocialChoice.Ranking.kApprovalScore
                  (K signal.1) signal.2 (hi pair) -
                AppliedModelingLib.SocialChoice.Ranking.kApprovalScore
                  (K signal.1) signal.2 (lo pair)))
    {pairWeight : Pair → ℝ}
    (hpairWeight : ∀ pair, 0 ≤ pairWeight pair)
    (hpairWeight_pos : ∀ pair, 0 < pairWeight pair) :
    ∃ rate : WithTop ℝ,
      HasExtendedExponentialRate
        (fun sampleSize =>
          ∑ pair : Pair,
            pairWeight pair *
              pairwiseScoringErrorProb
                (randomizedScoringSamplingLaw law weight hweight hsum)
                (fun signal : Rule × AppliedModelingLib.SocialChoice.Ranking.Ranking n =>
                  AppliedModelingLib.SocialChoice.Ranking.kApprovalScore
                    (K signal.1) signal.2 (hi pair))
                (fun signal : Rule × AppliedModelingLib.SocialChoice.Ranking.Ranking n =>
                  AppliedModelingLib.SocialChoice.Ranking.kApprovalScore
                    (K signal.1) signal.2 (lo pair))
                sampleSize)
        rate := by
  rcases
      randomizedKApprovalOutcomeError_hasExponentialRate_or_eventually_zero_of_mixed_expected_gap_nonneg
        law K weight hi lo hweight hsum hmean hpairWeight hpairWeight_pos with
    hfinite | hzero
  · rcases hfinite with ⟨rate, hrate⟩
    exact ⟨(rate : WithTop ℝ),
      HasExtendedExponentialRate.finite hrate⟩
  · exact ⟨⊤, HasExtendedExponentialRate.infinite hzero⟩

/--
Proposition 4 exact finite aggregation specialized to K-approval over a finite
set of relevant ordered pairs in the zero-down boundary case.
-/
theorem outcomeError_hasExponentialRate_of_kApproval_relevant_pairs_down_zero
    {n : ℕ} {Pair : Type*} [Fintype Pair] [DecidableEq Pair]
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : ℕ)
    (hi lo : Pair → AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (pUp pZero : Pair → ℝ)
    (hUpProb :
      ∀ pair,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K
            (hi pair) (lo pair) =
          pUp pair)
    (hZeroProb :
      ∀ pair,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairZeroProb law K
            (hi pair) (lo pair) =
          pZero pair)
    (hZero_pos : ∀ pair, 0 < pZero pair)
    (hDownZero :
      ∀ pair,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K
            (hi pair) (lo pair) =
          0)
    {pairWeight : Pair → ℝ} {minRate : ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (pairMin : Pair)
    (hweight_pos : 0 < pairWeight pairMin)
    (hrate_min : approvalPairwiseRate (pUp pairMin) 0 = minRate)
    (hrate_ge :
      ∀ pair, minRate ≤ approvalPairwiseRate (pUp pair) 0) :
    HasExponentialRate
      ((kApprovalRelevantPairRateCertificate_down_zero law K hi lo pUp pZero
          hUpProb hZeroProb hZero_pos hDownZero).aggregateError pairWeight)
      minRate :=
  (kApprovalRelevantPairRateCertificate_down_zero law K hi lo pUp pZero
    hUpProb hZeroProb hZero_pos hDownZero)
    |>.aggregateError_hasExponentialRate_of_min_component
      hweight pairMin hweight_pos hrate_min hrate_ge

/--
Exact K-approval zero-down aggregation at the finite outcome-learning rate.
The minimizing relevant pair is chosen internally from finiteness.
-/
theorem outcomeError_hasExponentialRate_of_kApproval_relevant_pairs_down_zero_at_finiteOutcomeLearningRate
    {n : ℕ} {Pair : Type*} [Fintype Pair] [Nonempty Pair] [DecidableEq Pair]
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : ℕ)
    (hi lo : Pair → AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (pUp pZero : Pair → ℝ)
    (hUpProb :
      ∀ pair,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K
            (hi pair) (lo pair) =
          pUp pair)
    (hZeroProb :
      ∀ pair,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairZeroProb law K
            (hi pair) (lo pair) =
          pZero pair)
    (hZero_pos : ∀ pair, 0 < pZero pair)
    (hDownZero :
      ∀ pair,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K
            (hi pair) (lo pair) =
          0)
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hweight_pos : ∀ pair, 0 < pairWeight pair) :
    HasExponentialRate
      ((kApprovalRelevantPairRateCertificate_down_zero law K hi lo pUp pZero
          hUpProb hZeroProb hZero_pos hDownZero).aggregateError pairWeight)
      (finiteOutcomeLearningRate
        (fun pair : Pair => approvalPairwiseRate (pUp pair) 0)) := by
  let rate : Pair → ℝ := fun pair => approvalPairwiseRate (pUp pair) 0
  rcases finiteOutcomeLearningRate_exists_minimizer rate with
    ⟨pairMin, hrate_min, hrate_ge⟩
  exact
    outcomeError_hasExponentialRate_of_kApproval_relevant_pairs_down_zero
      law K hi lo pUp pZero hUpProb hZeroProb hZero_pos hDownZero
      hweight pairMin (hweight_pos pairMin)
      (by simpa [rate] using hrate_min.symm)
      (by simpa [rate] using hrate_ge)

/--
Exact K-approval aggregation at the finite outcome-learning rate.  This is the
same minimum-rate theorem as `outcomeError_hasExponentialRate_of_kApproval_relevant_pairs`,
but the minimizing relevant pair is chosen internally from finiteness.
-/
theorem outcomeError_hasExponentialRate_of_kApproval_relevant_pairs_at_finiteOutcomeLearningRate
    {n : ℕ} {Pair : Type*} [Fintype Pair] [Nonempty Pair] [DecidableEq Pair]
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : ℕ)
    (hi lo : Pair → AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (pUp pDown : Pair → ℝ)
    (hUp : ∀ pair, 0 < pUp pair)
    (hDown : ∀ pair, 0 < pDown pair)
    (hle : ∀ pair, pDown pair ≤ pUp pair)
    (hUpProb :
      ∀ pair,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K
            (hi pair) (lo pair) =
          pUp pair)
    (hDownProb :
      ∀ pair,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K
            (hi pair) (lo pair) =
          pDown pair)
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hweight_pos : ∀ pair, 0 < pairWeight pair) :
    HasExponentialRate
      ((kApprovalRelevantPairRateCertificate law K hi lo pUp pDown
          hUp hDown hle hUpProb hDownProb).aggregateError pairWeight)
      (finiteOutcomeLearningRate
        (fun pair : Pair => approvalPairwiseRate (pUp pair) (pDown pair))) := by
  let rate : Pair → ℝ :=
    fun pair => approvalPairwiseRate (pUp pair) (pDown pair)
  rcases finiteOutcomeLearningRate_exists_minimizer rate with
    ⟨pairMin, hrate_min, hrate_ge⟩
  exact
    outcomeError_hasExponentialRate_of_kApproval_relevant_pairs
      law K hi lo pUp pDown hUp hDown hle hUpProb hDownProb
      hweight pairMin (hweight_pos pairMin)
      (by simpa [rate] using hrate_min.symm)
      (by simpa [rate] using hrate_ge)

/--
Exact K-approval aggregation at the finite outcome-learning rate, deriving the
weak ordering assumption from strict up/down separation on every relevant pair.
-/
theorem outcomeError_hasExponentialRate_of_kApproval_relevant_pairs_at_finiteOutcomeLearningRate_of_down_lt_up
    {n : ℕ} {Pair : Type*} [Fintype Pair] [Nonempty Pair] [DecidableEq Pair]
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : ℕ)
    (hi lo : Pair → AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (pUp pDown : Pair → ℝ)
    (hUp : ∀ pair, 0 < pUp pair)
    (hDown : ∀ pair, 0 < pDown pair)
    (hlt : ∀ pair, pDown pair < pUp pair)
    (hUpProb :
      ∀ pair,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K
            (hi pair) (lo pair) =
          pUp pair)
    (hDownProb :
      ∀ pair,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K
            (hi pair) (lo pair) =
          pDown pair)
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hweight_pos : ∀ pair, 0 < pairWeight pair) :
    HasExponentialRate
      ((kApprovalRelevantPairRateCertificate law K hi lo pUp pDown
          hUp hDown (fun pair => (hlt pair).le) hUpProb hDownProb)
        |>.aggregateError pairWeight)
      (finiteOutcomeLearningRate
        (fun pair : Pair => approvalPairwiseRate (pUp pair) (pDown pair))) :=
  outcomeError_hasExponentialRate_of_kApproval_relevant_pairs_at_finiteOutcomeLearningRate
    law K hi lo pUp pDown hUp hDown (fun pair => (hlt pair).le)
    hUpProb hDownProb hweight hweight_pos

/--
Exact K-approval aggregation at the finite outcome-learning rate, stated
directly in terms of the ranking-law up/down event probabilities.
-/
theorem outcomeError_hasExponentialRate_of_kApproval_relevant_pairs_at_finiteOutcomeLearningRate_of_probabilities_down_lt_up
    {n : ℕ} {Pair : Type*} [Fintype Pair] [Nonempty Pair] [DecidableEq Pair]
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : ℕ)
    (hi lo : Pair → AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (hUp :
      ∀ pair,
        0 <
          AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K
            (hi pair) (lo pair))
    (hDown :
      ∀ pair,
        0 <
          AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K
            (hi pair) (lo pair))
    (hlt :
      ∀ pair,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K
            (hi pair) (lo pair) <
          AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K
            (hi pair) (lo pair))
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hweight_pos : ∀ pair, 0 < pairWeight pair) :
    HasExponentialRate
      ((kApprovalRelevantPairRateCertificate_of_probabilities
          law K hi lo hUp hDown (fun pair => (hlt pair).le))
        |>.aggregateError pairWeight)
      (finiteOutcomeLearningRate
        (fun pair : Pair =>
          approvalPairwiseRate
            (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K
              (hi pair) (lo pair))
            (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K
              (hi pair) (lo pair)))) :=
  outcomeError_hasExponentialRate_of_kApproval_relevant_pairs_at_finiteOutcomeLearningRate_of_down_lt_up
    law K hi lo
    (fun pair =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K
        (hi pair) (lo pair))
    (fun pair =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K
        (hi pair) (lo pair))
    hUp hDown hlt (fun _ => rfl) (fun _ => rfl)
    hweight hweight_pos

/--
Proposition 4 convergence form specialized to K-approval over a finite set of
relevant ordered pairs: a positive lower bound on all relevant pairwise
approval rates makes the weighted finite outcome-error aggregate tend to zero.
-/
theorem outcomeError_tendsto_zero_of_kApproval_relevant_pairs
    {n : ℕ} {Pair : Type*} [Fintype Pair]
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : ℕ)
    (hi lo : Pair → AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (pUp pDown : Pair → ℝ)
    (hUp : ∀ pair, 0 < pUp pair)
    (hDown : ∀ pair, 0 < pDown pair)
    (hle : ∀ pair, pDown pair ≤ pUp pair)
    (hUpProb :
      ∀ pair,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K
            (hi pair) (lo pair) =
          pUp pair)
    (hDownProb :
      ∀ pair,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K
            (hi pair) (lo pair) =
          pDown pair)
    {pairWeight : Pair → ℝ} {rateFloor : ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hrateFloor_pos : 0 < rateFloor)
    (hrateFloor :
      ∀ pair, rateFloor ≤ approvalPairwiseRate (pUp pair) (pDown pair)) :
    Filter.Tendsto
      ((kApprovalRelevantPairRateCertificate law K hi lo pUp pDown
          hUp hDown hle hUpProb hDownProb).aggregateError pairWeight)
      Filter.atTop (nhds 0) :=
  (kApprovalRelevantPairRateCertificate law K hi lo pUp pDown
    hUp hDown hle hUpProb hDownProb)
    |>.aggregateError_tendsto_zero_of_pos_rate_floor
      hweight hrateFloor_pos hrateFloor

/--
Proposition 4 convergence specialized to K-approval over a finite nonempty set
of relevant ordered pairs.  Strict up/down separation and the probability-mass
constraint on every relevant pair make the finite minimum rate positive.
-/
theorem outcomeError_tendsto_zero_of_kApproval_relevant_pairs_of_down_lt_up
    {n : ℕ} {Pair : Type*} [Fintype Pair] [Nonempty Pair]
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : ℕ)
    (hi lo : Pair → AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (pUp pDown : Pair → ℝ)
    (hUp : ∀ pair, 0 < pUp pair)
    (hDown : ∀ pair, 0 < pDown pair)
    (hsum : ∀ pair, pUp pair + pDown pair ≤ 1)
    (hlt : ∀ pair, pDown pair < pUp pair)
    (hUpProb :
      ∀ pair,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K
            (hi pair) (lo pair) =
          pUp pair)
    (hDownProb :
      ∀ pair,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K
            (hi pair) (lo pair) =
          pDown pair)
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair) :
    Filter.Tendsto
      ((kApprovalRelevantPairRateCertificate law K hi lo pUp pDown
          hUp hDown (fun pair => (hlt pair).le) hUpProb hDownProb)
        |>.aggregateError pairWeight)
      Filter.atTop (nhds 0) := by
  let rate : Pair → ℝ :=
    fun pair => approvalPairwiseRate (pUp pair) (pDown pair)
  exact
    outcomeError_tendsto_zero_of_kApproval_relevant_pairs
      law K hi lo pUp pDown hUp hDown (fun pair => (hlt pair).le)
      hUpProb hDownProb hweight
      (finiteOutcomeLearningRate_pos
        (Pair := Pair) (rate := rate)
        (by
          intro pair
          exact
            approvalPairwiseRate_pos_of_down_lt_up
              (hUp pair) (hDown pair) (hsum pair) (hlt pair)))
      (by
        intro pair
        exact finiteOutcomeLearningRate_le rate pair)

/--
Proposition 4 convergence specialized to K-approval, with the probability-mass
constraint discharged from the disjointness of K-approval up/down events.
-/
theorem outcomeError_tendsto_zero_of_kApproval_relevant_pairs_of_down_lt_up_auto_sum
    {n : ℕ} {Pair : Type*} [Fintype Pair] [Nonempty Pair]
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : ℕ)
    (hi lo : Pair → AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (pUp pDown : Pair → ℝ)
    (hUp : ∀ pair, 0 < pUp pair)
    (hDown : ∀ pair, 0 < pDown pair)
    (hlt : ∀ pair, pDown pair < pUp pair)
    (hUpProb :
      ∀ pair,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K
            (hi pair) (lo pair) =
          pUp pair)
    (hDownProb :
      ∀ pair,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K
            (hi pair) (lo pair) =
          pDown pair)
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair) :
    Filter.Tendsto
      ((kApprovalRelevantPairRateCertificate law K hi lo pUp pDown
          hUp hDown (fun pair => (hlt pair).le) hUpProb hDownProb)
        |>.aggregateError pairWeight)
      Filter.atTop (nhds 0) := by
  refine
    outcomeError_tendsto_zero_of_kApproval_relevant_pairs_of_down_lt_up
      law K hi lo pUp pDown hUp hDown ?_ hlt hUpProb hDownProb
      hweight
  intro pair
  rw [← hUpProb pair, ← hDownProb pair]
  exact
    AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb_add_downProb_le_one
      law K (hi pair) (lo pair)

/--
Proposition 4 convergence specialized to K-approval and stated directly in
terms of the ranking-law up/down event probabilities.
-/
theorem outcomeError_tendsto_zero_of_kApproval_relevant_pairs_of_probabilities_down_lt_up
    {n : ℕ} {Pair : Type*} [Fintype Pair] [Nonempty Pair]
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : ℕ)
    (hi lo : Pair → AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (hUp :
      ∀ pair,
        0 <
          AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K
            (hi pair) (lo pair))
    (hDown :
      ∀ pair,
        0 <
          AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K
            (hi pair) (lo pair))
    (hlt :
      ∀ pair,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K
            (hi pair) (lo pair) <
          AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K
            (hi pair) (lo pair))
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair) :
    Filter.Tendsto
      ((kApprovalRelevantPairRateCertificate_of_probabilities
          law K hi lo hUp hDown (fun pair => (hlt pair).le))
        |>.aggregateError pairWeight)
      Filter.atTop (nhds 0) :=
  outcomeError_tendsto_zero_of_kApproval_relevant_pairs_of_down_lt_up_auto_sum
    law K hi lo
    (fun pair =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law K
        (hi pair) (lo pair))
    (fun pair =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law K
        (hi pair) (lo pair))
    hUp hDown hlt (fun _ => rfl) (fun _ => rfl) hweight

/--
Proposition 4 upper-bound bridge from finite iid score-gap duals: if every
relevant pair's chosen Chernoff dual rate is at least `targetRate`, then the
weighted finite outcome-error sum has an exponential upper bound at
`targetRate`.
-/
theorem outcomeError_hasExpUpperBound_of_finite_score_gap_duals
    {Candidate Signal : Type*} [Fintype Candidate] [Fintype Signal]
    [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (dual : Candidate → Candidate → ℝ)
    {pairWeight : Candidate → Candidate → ℝ} {targetRate : ℝ}
    (hdual : ∀ hi lo : Candidate, dual hi lo ≤ 0)
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hrate :
      ∀ hi lo,
        targetRate ≤ finiteScoreGapPairwiseDualRate law score dual hi lo) :
    HasExpUpperBoundWithConst
      ((finiteScoreGapPairwiseUpperBoundCertificate
          law score dual hdual).aggregateError pairWeight)
      targetRate :=
  (finiteScoreGapPairwiseUpperBoundCertificate law score dual hdual)
    |>.aggregateError_hasExpUpperBoundWithConst hweight hrate

/--
Proposition 4 exact finite aggregation from finite iid score-gap Cramer
certificates: once every pair's iid score-gap mistake probability has the
source Chernoff exponent as its exact rate, the finite outcome-error rate is
the realized minimum pairwise Chernoff rate.
-/
theorem outcomeError_hasExponentialRate_of_finite_score_gap_cramer
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (cramer :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapCramerCertificate law (score hi) (score lo))
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate law score cramer)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_pairwise_min_rate
    (finiteScoreGapPairwiseRateCertificate law score cramer)
    hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation from per-pair periodic empirical-count
witness families.  Each pair supplies a method-of-types lower witness for
every strictly slower target rate; the Chernoff upper side and finite minimum
aggregation are discharged uniformly.
-/
theorem outcomeError_hasExponentialRate_of_finite_score_gap_periodicCountVectorLower_witnesses_of_mean_nonneg_pos_neg_atoms
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0)
    (lower :
      ∀ hi lo : Candidate, ∀ targetRate,
        finiteIidPairwiseScoreGapChernoffRate law score hi lo < targetRate →
        ∃ (Q : ℕ) (q : Signal → ℕ) (filler : Signal) (base : ℝ),
          0 < Q ∧
          (∑ signal : Signal, q signal = Q) ∧
          (∑ signal : Signal,
            (q signal : ℝ) * (score hi signal - score lo signal) ≤ 0) ∧
          score hi filler - score lo filler ≤ 0 ∧
          0 < base ∧
          base ^ Q ≤
            ∏ signal : Signal, (law signal).toReal ^ q signal ∧
          0 < (law filler).toReal ∧
          -Real.log base < targetRate)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_periodicCountVectorLower_witnesses_of_mean_nonneg_pos_neg_atoms
          law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg lower)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_pairwise_min_rate
    (finiteScoreGapPairwiseRateCertificate_of_periodicCountVectorLower_witnesses_of_mean_nonneg_pos_neg_atoms
      law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg lower)
    hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation from per-pair empirical-type witness
families.  This is the entropy-aware method-of-types route: each pair may
choose a different finite empirical type for every strictly slower target
rate, including the multinomial type-mass factor.
-/
theorem outcomeError_hasExponentialRate_of_finite_score_gap_empiricalTypeLower_witnesses_of_mean_nonneg_pos_neg_atoms
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0)
    (lower :
      ∀ hi lo : Candidate, ∀ targetRate,
        finiteIidPairwiseScoreGapChernoffRate law score hi lo < targetRate →
          ∃ C : FiniteIidScoreGapEmpiricalTypeLowerCertificate
              law (score hi) (score lo),
            -Real.log C.base < targetRate)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_empiricalTypeLower_witnesses_of_mean_nonneg_pos_neg_atoms
          law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg lower)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_pairwise_min_rate
    (finiteScoreGapPairwiseRateCertificate_of_empiricalTypeLower_witnesses_of_mean_nonneg_pos_neg_atoms
      law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg lower)
    hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation from explicit finite score-gap
path/type lower certificates.  This packages concrete lower-bound witnesses
into the same finite minimum-rate aggregation theorem used by the Cramer
certificate route.
-/
theorem outcomeError_hasExponentialRate_of_finite_score_gap_pathLower
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hupper :
      ∀ hi lo : Candidate, ∀ targetRate,
        targetRate < finiteIidPairwiseScoreGapChernoffRate law score hi lo →
          HasExpUpperBoundWithConst
            (finiteScoreGapPairwiseErrorProb law score hi lo) targetRate)
    (lower :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapPathLowerCertificate law (score hi) (score lo))
    (hrate :
      ∀ hi lo : Candidate,
        -Real.log (lower hi lo).base =
          finiteIidPairwiseScoreGapChernoffRate law score hi lo)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_pathLower
          law score hupper lower hrate)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_pairwise_min_rate
    (finiteScoreGapPairwiseRateCertificate_of_pathLower
      law score hupper lower hrate)
    hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation from path lower certificates, with each
pair's Chernoff upper side discharged by nonnegative expected score gap and
positive-mass atoms on both sides of the score gap.
-/
theorem outcomeError_hasExponentialRate_of_finite_score_gap_pathLower_of_mean_nonneg_pos_neg_atoms
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0)
    (lower :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapPathLowerCertificate law (score hi) (score lo))
    (hrate :
      ∀ hi lo : Candidate,
        -Real.log (lower hi lo).base =
          finiteIidPairwiseScoreGapChernoffRate law score hi lo)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_pathLower
          law score
          (fun hi lo targetRate htarget => by
            simpa [finiteScoreGapPairwiseErrorProb, pairwiseScoringErrorProb,
              finiteIidScoreGapLeftTailProb] using
              finiteIidScoreGapLeftTail_upperBounds_of_lt_chernoffRate
                law (score hi) (score lo) (hmean hi lo)
                (finiteScoreGapLogMGF_bddBelow_of_pos_neg_atoms
                  law (score hi) (score lo)
                  (hmassPos hi lo) (hgapPos hi lo)
                  (hmassNeg hi lo) (hgapNeg hi lo))
                targetRate htarget)
          lower hrate)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_pairwise_min_rate
    (finiteScoreGapPairwiseRateCertificate_of_pathLower
      law score
      (fun hi lo targetRate htarget => by
        simpa [finiteScoreGapPairwiseErrorProb, pairwiseScoringErrorProb,
          finiteIidScoreGapLeftTailProb] using
          finiteIidScoreGapLeftTail_upperBounds_of_lt_chernoffRate
            law (score hi) (score lo) (hmean hi lo)
            (finiteScoreGapLogMGF_bddBelow_of_pos_neg_atoms
              law (score hi) (score lo)
              (hmassPos hi lo) (hgapPos hi lo)
              (hmassNeg hi lo) (hgapNeg hi lo))
            targetRate htarget)
      lower hrate)
    hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation from explicit finite score-gap direct
tail-probability lower certificates.  This is the same finite minimum-rate
aggregation theorem as the path-lower route, but accepts lower bounds already
proved at the tail-probability level.
-/
theorem outcomeError_hasExponentialRate_of_finite_score_gap_tailLower
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hupper :
      ∀ hi lo : Candidate, ∀ targetRate,
        targetRate < finiteIidPairwiseScoreGapChernoffRate law score hi lo →
          HasExpUpperBoundWithConst
            (finiteScoreGapPairwiseErrorProb law score hi lo) targetRate)
    (lower :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapTailLowerCertificate law (score hi) (score lo))
    (hrate :
      ∀ hi lo : Candidate,
        -Real.log (lower hi lo).base =
          finiteIidPairwiseScoreGapChernoffRate law score hi lo)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_tailLower
          law score hupper lower hrate)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_pairwise_min_rate
    (finiteScoreGapPairwiseRateCertificate_of_tailLower
      law score hupper lower hrate)
    hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation from direct tail-probability lower
certificates, with each pair's Chernoff upper side discharged by nonnegative
expected score gap and positive-mass atoms on both sides of the score gap.
-/
theorem outcomeError_hasExponentialRate_of_finite_score_gap_tailLower_of_mean_nonneg_pos_neg_atoms
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0)
    (lower :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapTailLowerCertificate law (score hi) (score lo))
    (hrate :
      ∀ hi lo : Candidate,
        -Real.log (lower hi lo).base =
          finiteIidPairwiseScoreGapChernoffRate law score hi lo)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_tailLower
          law score
          (fun hi lo targetRate htarget => by
            simpa [finiteScoreGapPairwiseErrorProb, pairwiseScoringErrorProb,
              finiteIidScoreGapLeftTailProb] using
              finiteIidScoreGapLeftTail_upperBounds_of_lt_chernoffRate
                law (score hi) (score lo) (hmean hi lo)
                (finiteScoreGapLogMGF_bddBelow_of_pos_neg_atoms
                  law (score hi) (score lo)
                  (hmassPos hi lo) (hgapPos hi lo)
                  (hmassNeg hi lo) (hgapNeg hi lo))
                targetRate htarget)
          lower hrate)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_pairwise_min_rate
    (finiteScoreGapPairwiseRateCertificate_of_tailLower
      law score
      (fun hi lo targetRate htarget => by
        simpa [finiteScoreGapPairwiseErrorProb, pairwiseScoringErrorProb,
          finiteIidScoreGapLeftTailProb] using
          finiteIidScoreGapLeftTail_upperBounds_of_lt_chernoffRate
            law (score hi) (score lo) (hmean hi lo)
            (finiteScoreGapLogMGF_bddBelow_of_pos_neg_atoms
              law (score hi) (score lo)
              (hmassPos hi lo) (hgapPos hi lo)
              (hmassNeg hi lo) (hgapNeg hi lo))
            targetRate htarget)
      lower hrate)
    hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation from explicit finite score-gap
empirical-type lower certificates.  This is the same finite minimum-rate
aggregation theorem as the tail-lower route, with exact multinomial type
probabilities converted to tail lower bounds automatically.
-/
theorem outcomeError_hasExponentialRate_of_finite_score_gap_empiricalTypeLower
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hupper :
      ∀ hi lo : Candidate, ∀ targetRate,
        targetRate < finiteIidPairwiseScoreGapChernoffRate law score hi lo →
          HasExpUpperBoundWithConst
            (finiteScoreGapPairwiseErrorProb law score hi lo) targetRate)
    (lower :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapEmpiricalTypeLowerCertificate law (score hi) (score lo))
    (hrate :
      ∀ hi lo : Candidate,
        -Real.log (lower hi lo).base =
          finiteIidPairwiseScoreGapChernoffRate law score hi lo)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_empiricalTypeLower
          law score hupper lower hrate)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_pairwise_min_rate
    (finiteScoreGapPairwiseRateCertificate_of_empiricalTypeLower
      law score hupper lower hrate)
    hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation from empirical-type lower
certificates, with each pair's Chernoff upper side discharged by nonnegative
expected score gap and positive-mass atoms on both sides of the score gap.
-/
theorem outcomeError_hasExponentialRate_of_finite_score_gap_empiricalTypeLower_of_mean_nonneg_pos_neg_atoms
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0)
    (lower :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapEmpiricalTypeLowerCertificate law (score hi) (score lo))
    (hrate :
      ∀ hi lo : Candidate,
        -Real.log (lower hi lo).base =
          finiteIidPairwiseScoreGapChernoffRate law score hi lo)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_empiricalTypeLower_of_mean_nonneg_pos_neg_atoms
          law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg
          lower hrate)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_pairwise_min_rate
    (finiteScoreGapPairwiseRateCertificate_of_empiricalTypeLower_of_mean_nonneg_pos_neg_atoms
      law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg
      lower hrate)
    hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation from per-pair stationary exponential
tilts, with the pairwise exact rates closed by the support-preserving finite
method-of-types theorem.
-/
theorem outcomeError_hasExponentialRate_of_stationary_tilted_modal_log_support
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0)
    (z : Candidate → Candidate → ℝ)
    (hstationary :
      ∀ hi lo : Candidate,
        (∑ signal : Signal,
          (law signal).toReal *
            ((score hi signal - score lo signal) *
              Real.exp
                (z hi lo * (score hi signal - score lo signal)))) = 0)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_stationary_tilted_modal_log_support
          law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg
          z hstationary)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_pairwise_min_rate
    (finiteScoreGapPairwiseRateCertificate_of_stationary_tilted_modal_log_support
      law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg
      z hstationary)
    hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation from supplied per-pair stationary
finite exponential tilts, stated directly at the finite outcome-learning rate.
The minimizing ordered candidate pair is chosen internally from finiteness.
-/
theorem outcomeError_hasExponentialRate_of_stationary_tilted_modal_log_support_at_finiteOutcomeLearningRate
    {Candidate Signal : Type*} [Fintype Candidate] [Nonempty Candidate]
    [DecidableEq Candidate] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0)
    (z : Candidate → Candidate → ℝ)
    (hstationary :
      ∀ hi lo : Candidate,
        (∑ signal : Signal,
          (law signal).toReal *
            ((score hi signal - score lo signal) *
              Real.exp
                (z hi lo * (score hi signal - score lo signal)))) = 0)
    {pairWeight : Candidate → Candidate → ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hweight_pos : ∀ hi lo, 0 < pairWeight hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_stationary_tilted_modal_log_support
          law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg
          z hstationary)
        |>.aggregateError pairWeight)
      (finiteOutcomeLearningRate
        (fun pair : Candidate × Candidate =>
          finiteIidPairwiseScoreGapChernoffRate law score pair.1 pair.2)) := by
  let rate : Candidate × Candidate → ℝ :=
    fun pair => finiteIidPairwiseScoreGapChernoffRate law score pair.1 pair.2
  rcases finiteOutcomeLearningRate_exists_minimizer rate with
    ⟨minPair, hrate_min, hrate_ge⟩
  simpa [rate] using
    outcomeError_hasExponentialRate_of_stationary_tilted_modal_log_support
      law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg
      z hstationary hweight minPair.1 minPair.2
      (hweight_pos minPair.1 minPair.2)
      hrate_min.symm (fun hi lo => hrate_ge (hi, lo))

/--
Proposition 4 exact finite aggregation from nonnegative per-pair expected gaps
and positive-mass atoms on both sides of each score gap.  The stationary
exponential tilts are found internally for every pair, then the pairwise exact
rates are combined by finite minimum-rate aggregation.
-/
theorem outcomeError_hasExponentialRate_of_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms
          law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_pairwise_min_rate
    (finiteScoreGapPairwiseRateCertificate_of_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms
      law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg)
    hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation over a finite family of relevant
ordered candidate pairs.  This is the support-aware stationary-tilt route with
the pair index restricted to the comparisons used by the paper theorem.
-/
theorem outcomeError_hasExponentialRate_of_relevant_pairs_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms
    {Pair Candidate Signal : Type*} [Fintype Pair] [DecidableEq Pair]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    (hmean :
      ∀ pair,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score (hi pair) signal - score (lo pair) signal))
    (aPos aNeg : Pair → Signal)
    (hmassPos : ∀ pair, 0 < (law (aPos pair)).toReal)
    (hgapPos :
      ∀ pair, 0 < score (hi pair) (aPos pair) -
        score (lo pair) (aPos pair))
    (hmassNeg : ∀ pair, 0 < (law (aNeg pair)).toReal)
    (hgapNeg :
      ∀ pair, score (hi pair) (aNeg pair) -
        score (lo pair) (aNeg pair) < 0)
    {pairWeight : Pair → ℝ} {minRate : ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (pairMin : Pair)
    (hweight_pos : 0 < pairWeight pairMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score
        (hi pairMin) (lo pairMin) = minRate)
    (hrate_ge :
      ∀ pair,
        minRate ≤
          finiteIidPairwiseScoreGapChernoffRate law score
            (hi pair) (lo pair)) :
    HasExponentialRate
      ((finiteScoreGapRelevantPairRateCertificate_of_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms
          law score hi lo hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg)
        |>.aggregateError pairWeight)
      minRate :=
  (finiteScoreGapRelevantPairRateCertificate_of_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms
    law score hi lo hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg)
    |>.aggregateError_hasExponentialRate_of_min_component
      hweight pairMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation over relevant ordered candidate pairs,
stated at the finite outcome-learning rate over exactly that relevant-pair
index.  The minimizing relevant pair is chosen internally from finiteness.
-/
theorem outcomeError_hasExponentialRate_of_relevant_pairs_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms_at_finiteOutcomeLearningRate
    {Pair Candidate Signal : Type*} [Fintype Pair] [Nonempty Pair]
    [DecidableEq Pair] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    (hmean :
      ∀ pair,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score (hi pair) signal - score (lo pair) signal))
    (aPos aNeg : Pair → Signal)
    (hmassPos : ∀ pair, 0 < (law (aPos pair)).toReal)
    (hgapPos :
      ∀ pair, 0 < score (hi pair) (aPos pair) -
        score (lo pair) (aPos pair))
    (hmassNeg : ∀ pair, 0 < (law (aNeg pair)).toReal)
    (hgapNeg :
      ∀ pair, score (hi pair) (aNeg pair) -
        score (lo pair) (aNeg pair) < 0)
    {pairWeight : Pair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hweight_pos : ∀ pair, 0 < pairWeight pair) :
    HasExponentialRate
      ((finiteScoreGapRelevantPairRateCertificate_of_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms
          law score hi lo hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg)
        |>.aggregateError pairWeight)
      (finiteOutcomeLearningRate
        (fun pair : Pair =>
          finiteIidPairwiseScoreGapChernoffRate law score
            (hi pair) (lo pair))) := by
  let rate : Pair → ℝ :=
    fun pair => finiteIidPairwiseScoreGapChernoffRate law score
      (hi pair) (lo pair)
  rcases finiteOutcomeLearningRate_exists_minimizer rate with
    ⟨pairMin, hrate_min, hrate_ge⟩
  exact
    outcomeError_hasExponentialRate_of_relevant_pairs_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms
      law score hi lo hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg
      hweight pairMin (hweight_pos pairMin)
      (by simpa [rate] using hrate_min.symm)
      (by simpa [rate] using hrate_ge)

/--
Source-shaped Proposition 4 exact rate for W-selection: the expected number of
cross-tier pairwise errors has exponential rate equal to the finite minimum of
the source pairwise scoring rates over true-winner/true-loser pairs.
-/
theorem crossTierOutcomeError_hasExponentialRate_of_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms_at_finiteOutcomeLearningRate
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (winnerSet : Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (hmean :
      ∀ pair : CrossTierPair winnerSet,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score pair.hi signal - score pair.lo signal))
    (aPos aNeg : CrossTierPair winnerSet → Signal)
    (hmassPos : ∀ pair, 0 < (law (aPos pair)).toReal)
    (hgapPos :
      ∀ pair, 0 < score pair.hi (aPos pair) -
        score pair.lo (aPos pair))
    (hmassNeg : ∀ pair, 0 < (law (aNeg pair)).toReal)
    (hgapNeg :
      ∀ pair, score pair.hi (aNeg pair) -
        score pair.lo (aNeg pair) < 0) :
    HasExponentialRate
      (fun n =>
        ∑ pair : CrossTierPair winnerSet,
          finiteScoreGapPairwiseErrorProb law score pair.hi pair.lo n)
      (finiteOutcomeLearningRate
        (fun pair : CrossTierPair winnerSet =>
          pairwiseScoringRate law (score pair.hi) (score pair.lo))) := by
  classical
  have h :=
    outcomeError_hasExponentialRate_of_relevant_pairs_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms_at_finiteOutcomeLearningRate
      (Pair := CrossTierPair winnerSet)
      (law := law) (score := score)
      (hi := fun pair : CrossTierPair winnerSet => pair.hi)
      (lo := fun pair : CrossTierPair winnerSet => pair.lo)
      hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg
      (pairWeight := fun _ => (1 : ℝ))
      (by intro _; norm_num)
      (by intro _; norm_num)
  convert h using 1
  · ext n
    simp [
      finiteScoreGapRelevantPairRateCertificate_of_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms,
      finiteScoreGapPairwiseErrorProb,
      AppliedModelingLib.Probability.FiniteErrorRateCertificate.aggregateError]

/--
Proposition 4 exact finite aggregation at the finite outcome-learning rate.
The minimizing ordered candidate pair is chosen internally from finiteness, so
callers no longer need to supply `hiMin`, `loMin`, or rate-minimality
certificates.
-/
theorem outcomeError_hasExponentialRate_of_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms_at_finiteOutcomeLearningRate
    {Candidate Signal : Type*} [Fintype Candidate] [Nonempty Candidate]
    [DecidableEq Candidate] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0)
    {pairWeight : Candidate → Candidate → ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hweight_pos : ∀ hi lo, 0 < pairWeight hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms
          law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg)
        |>.aggregateError pairWeight)
      (finiteOutcomeLearningRate
        (fun pair : Candidate × Candidate =>
          finiteIidPairwiseScoreGapChernoffRate law score pair.1 pair.2)) := by
  let rate : Candidate × Candidate → ℝ :=
    fun pair => finiteIidPairwiseScoreGapChernoffRate law score pair.1 pair.2
  rcases finiteOutcomeLearningRate_exists_minimizer rate with
    ⟨pairMin, hrate_min, hrate_ge⟩
  exact
    outcomeError_hasExponentialRate_of_stationary_tilted_modal_log_support_of_mean_nonneg_pos_neg_atoms
      law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg
      hweight pairMin.1 pairMin.2 (hweight_pos pairMin.1 pairMin.2)
      (by simpa [rate] using hrate_min.symm)
      (by
        intro hi lo
        simpa [rate] using hrate_ge (hi, lo))

/--
Full-support convenience wrapper for
`outcomeError_hasExponentialRate_of_stationary_tilted_modal_log_support`.
-/
theorem outcomeError_hasExponentialRate_of_stationary_tilted_modal_log_full_support
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0)
    (_hlaw_full : ∀ signal : Signal, 0 < (law signal).toReal)
    (z : Candidate → Candidate → ℝ)
    (hstationary :
      ∀ hi lo : Candidate,
        (∑ signal : Signal,
          (law signal).toReal *
            ((score hi signal - score lo signal) *
              Real.exp
                (z hi lo * (score hi signal - score lo signal)))) = 0)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_stationary_tilted_modal_log_full_support
          law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg
          _hlaw_full z hstationary)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_pairwise_min_rate
    (finiteScoreGapPairwiseRateCertificate_of_stationary_tilted_modal_log_full_support
      law score hmean aPos aNeg hmassPos hgapPos hmassNeg hgapNeg
      _hlaw_full z hstationary)
    hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation from explicit finite score-gap
bucket/type lower certificates.  This is the same finite minimum-rate
aggregation theorem as the path-lower route, with buckets converted to sample
paths automatically.
-/
theorem outcomeError_hasExponentialRate_of_finite_score_gap_bucketLower
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hupper :
      ∀ hi lo : Candidate, ∀ targetRate,
        targetRate < finiteIidPairwiseScoreGapChernoffRate law score hi lo →
          HasExpUpperBoundWithConst
            (finiteScoreGapPairwiseErrorProb law score hi lo) targetRate)
    (lower :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapBucketLowerCertificate law (score hi) (score lo))
    (hrate :
      ∀ hi lo : Candidate,
        -Real.log (lower hi lo).base =
          finiteIidPairwiseScoreGapChernoffRate law score hi lo)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_bucketLower
          law score hupper lower hrate)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_pairwise_min_rate
    (finiteScoreGapPairwiseRateCertificate_of_bucketLower
      law score hupper lower hrate)
    hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation from bucket/type lower certificates,
with each pair's Chernoff upper side discharged by nonnegative expected score
gap and positive-mass atoms on both sides of the score gap.
-/
theorem outcomeError_hasExponentialRate_of_finite_score_gap_bucketLower_of_mean_nonneg_pos_neg_atoms
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0)
    (lower :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapBucketLowerCertificate law (score hi) (score lo))
    (hrate :
      ∀ hi lo : Candidate,
        -Real.log (lower hi lo).base =
          finiteIidPairwiseScoreGapChernoffRate law score hi lo)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_bucketLower
          law score
          (fun hi lo targetRate htarget => by
            simpa [finiteScoreGapPairwiseErrorProb, pairwiseScoringErrorProb,
              finiteIidScoreGapLeftTailProb] using
              finiteIidScoreGapLeftTail_upperBounds_of_lt_chernoffRate
                law (score hi) (score lo) (hmean hi lo)
                (finiteScoreGapLogMGF_bddBelow_of_pos_neg_atoms
                  law (score hi) (score lo)
                  (hmassPos hi lo) (hgapPos hi lo)
                  (hmassNeg hi lo) (hgapNeg hi lo))
                targetRate htarget)
          lower hrate)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_pairwise_min_rate
    (finiteScoreGapPairwiseRateCertificate_of_bucketLower
      law score
      (fun hi lo targetRate htarget => by
        simpa [finiteScoreGapPairwiseErrorProb, pairwiseScoringErrorProb,
          finiteIidScoreGapLeftTailProb] using
          finiteIidScoreGapLeftTail_upperBounds_of_lt_chernoffRate
            law (score hi) (score lo) (hmean hi lo)
            (finiteScoreGapLogMGF_bddBelow_of_pos_neg_atoms
              law (score hi) (score lo)
              (hmassPos hi lo) (hgapPos hi lo)
              (hmassNeg hi lo) (hgapNeg hi lo))
            targetRate htarget)
      lower hrate)
    hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation from explicit finite score-gap
empirical count-vector lower certificates.  This is the same finite
minimum-rate aggregation theorem as the path-lower route, with count vectors
converted to sample paths automatically.
-/
theorem outcomeError_hasExponentialRate_of_finite_score_gap_countVectorLower
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hupper :
      ∀ hi lo : Candidate, ∀ targetRate,
        targetRate < finiteIidPairwiseScoreGapChernoffRate law score hi lo →
          HasExpUpperBoundWithConst
            (finiteScoreGapPairwiseErrorProb law score hi lo) targetRate)
    (lower :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapCountVectorLowerCertificate law (score hi) (score lo))
    (hrate :
      ∀ hi lo : Candidate,
        -Real.log (lower hi lo).base =
          finiteIidPairwiseScoreGapChernoffRate law score hi lo)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_countVectorLower
          law score hupper lower hrate)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_pairwise_min_rate
    (finiteScoreGapPairwiseRateCertificate_of_countVectorLower
      law score hupper lower hrate)
    hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation from empirical count-vector lower
certificates, with each pair's Chernoff upper side discharged by nonnegative
expected score gap and positive-mass atoms on both sides of the score gap.
-/
theorem outcomeError_hasExponentialRate_of_finite_score_gap_countVectorLower_of_mean_nonneg_pos_neg_atoms
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hmean :
      ∀ hi lo : Candidate,
        0 ≤ AppliedModelingLib.pmfExp law
          (fun signal => score hi signal - score lo signal))
    (aPos aNeg : Candidate → Candidate → Signal)
    (hmassPos : ∀ hi lo, 0 < (law (aPos hi lo)).toReal)
    (hgapPos : ∀ hi lo, 0 < score hi (aPos hi lo) - score lo (aPos hi lo))
    (hmassNeg : ∀ hi lo, 0 < (law (aNeg hi lo)).toReal)
    (hgapNeg : ∀ hi lo, score hi (aNeg hi lo) - score lo (aNeg hi lo) < 0)
    (lower :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapCountVectorLowerCertificate law (score hi) (score lo))
    (hrate :
      ∀ hi lo : Candidate,
        -Real.log (lower hi lo).base =
          finiteIidPairwiseScoreGapChernoffRate law score hi lo)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      finiteIidPairwiseScoreGapChernoffRate law score hiMin loMin = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤
        finiteIidPairwiseScoreGapChernoffRate law score hi lo) :
    HasExponentialRate
      ((finiteScoreGapPairwiseRateCertificate_of_countVectorLower
          law score
          (fun hi lo targetRate htarget => by
            simpa [finiteScoreGapPairwiseErrorProb, pairwiseScoringErrorProb,
              finiteIidScoreGapLeftTailProb] using
              finiteIidScoreGapLeftTail_upperBounds_of_lt_chernoffRate
                law (score hi) (score lo) (hmean hi lo)
                (finiteScoreGapLogMGF_bddBelow_of_pos_neg_atoms
                  law (score hi) (score lo)
                  (hmassPos hi lo) (hgapPos hi lo)
                  (hmassNeg hi lo) (hgapNeg hi lo))
                targetRate htarget)
          lower hrate)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_pairwise_min_rate
    (finiteScoreGapPairwiseRateCertificate_of_countVectorLower
      law score
      (fun hi lo targetRate htarget => by
        simpa [finiteScoreGapPairwiseErrorProb, pairwiseScoringErrorProb,
          finiteIidScoreGapLeftTailProb] using
          finiteIidScoreGapLeftTail_upperBounds_of_lt_chernoffRate
            law (score hi) (score lo) (hmean hi lo)
            (finiteScoreGapLogMGF_bddBelow_of_pos_neg_atoms
              law (score hi) (score lo)
              (hmassPos hi lo) (hgapPos hi lo)
              (hmassNeg hi lo) (hgapNeg hi lo))
            targetRate htarget)
      lower hrate)
    hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation for K-approval rates, using the source
closed-form pairwise approval rates directly.
-/
theorem outcomeError_hasExponentialRate_of_approval_cramer
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (pUp pDown : Candidate → Candidate → ℝ)
    (hUp : ∀ hi lo, 0 < pUp hi lo)
    (hDown : ∀ hi lo, 0 < pDown hi lo)
    (hsum : ∀ hi lo, pUp hi lo + pDown hi lo ≤ 1)
    (hmgf :
      ∀ hi lo z,
        finiteMGF law
            (fun signal => score hi signal - score lo signal) z =
          ternaryGapMGF (pUp hi lo) (pDown hi lo) z)
    (cramer :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapCramerCertificate law (score hi) (score lo))
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      approvalPairwiseRate (pUp hiMin loMin) (pDown hiMin loMin) = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤ approvalPairwiseRate (pUp hi lo) (pDown hi lo)) :
    HasExponentialRate
      ((approvalPairwiseRateCertificate law score pUp pDown
          hUp hDown hsum hmgf cramer)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_pairwise_min_rate
    (approvalPairwiseRateCertificate law score pUp pDown
      hUp hDown hsum hmgf cramer)
    hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 exact finite aggregation for K-approval rates from concrete
ternary score gaps, using the source closed-form pairwise approval rates
directly and avoiding an external Cramer certificate.
-/
theorem outcomeError_hasExponentialRate_of_approval_ternary_scores
    {Candidate Signal : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (pUp pDown : Candidate → Candidate → ℝ)
    (hUp : ∀ hi lo, 0 < pUp hi lo)
    (hDown : ∀ hi lo, 0 < pDown hi lo)
    (hle : ∀ hi lo, pDown hi lo ≤ pUp hi lo)
    (hscore :
      ∀ hi lo signal,
        score hi signal - score lo signal = 1 ∨
          score hi signal - score lo signal = 0 ∨
          score hi signal - score lo signal = -1)
    (hUpProb :
      ∀ hi lo,
        AppliedModelingLib.pmfProb law
            (fun signal => score hi signal - score lo signal = 1) =
          pUp hi lo)
    (hDownProb :
      ∀ hi lo,
        AppliedModelingLib.pmfProb law
            (fun signal => score hi signal - score lo signal = -1) =
          pDown hi lo)
    {pairWeight : Candidate → Candidate → ℝ} {minRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hiMin loMin : Candidate)
    (hweight_pos : 0 < pairWeight hiMin loMin)
    (hrate_min :
      approvalPairwiseRate (pUp hiMin loMin) (pDown hiMin loMin) = minRate)
    (hrate_ge :
      ∀ hi lo, minRate ≤ approvalPairwiseRate (pUp hi lo) (pDown hi lo)) :
    HasExponentialRate
      ((approvalPairwiseRateCertificate_of_ternary_scores law score pUp pDown
          hUp hDown hle hscore hUpProb hDownProb)
        |>.aggregateError pairWeight)
      minRate :=
  outcomeError_hasExponentialRate_of_pairwise_min_rate
    (approvalPairwiseRateCertificate_of_ternary_scores law score pUp pDown
      hUp hDown hle hscore hUpProb hDownProb)
    hweight hiMin loMin hweight_pos hrate_min hrate_ge

/--
Proposition 4 convergence form from concrete ternary approval-style score
gaps: a positive lower bound on all pairwise approval rates makes the finite
weighted aggregate of pairwise errors tend to zero.
-/
theorem outcomeError_tendsto_zero_of_approval_ternary_scores
    {Candidate Signal : Type*} [Fintype Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (pUp pDown : Candidate → Candidate → ℝ)
    (hUp : ∀ hi lo, 0 < pUp hi lo)
    (hDown : ∀ hi lo, 0 < pDown hi lo)
    (hle : ∀ hi lo, pDown hi lo ≤ pUp hi lo)
    (hscore :
      ∀ hi lo signal,
        score hi signal - score lo signal = 1 ∨
          score hi signal - score lo signal = 0 ∨
          score hi signal - score lo signal = -1)
    (hUpProb :
      ∀ hi lo,
        AppliedModelingLib.pmfProb law
            (fun signal => score hi signal - score lo signal = 1) =
          pUp hi lo)
    (hDownProb :
      ∀ hi lo,
        AppliedModelingLib.pmfProb law
            (fun signal => score hi signal - score lo signal = -1) =
          pDown hi lo)
    {pairWeight : Candidate → Candidate → ℝ} {rateFloor : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hrateFloor_pos : 0 < rateFloor)
    (hrateFloor :
      ∀ hi lo,
        rateFloor ≤ approvalPairwiseRate (pUp hi lo) (pDown hi lo)) :
    Filter.Tendsto
      ((approvalPairwiseRateCertificate_of_ternary_scores law score pUp pDown
          hUp hDown hle hscore hUpProb hDownProb)
        |>.aggregateError pairWeight)
      Filter.atTop (nhds 0) :=
  (approvalPairwiseRateCertificate_of_ternary_scores law score pUp pDown
    hUp hDown hle hscore hUpProb hDownProb)
    |>.aggregateError_tendsto_zero_of_pos_rate_floor
      hweight hrateFloor_pos hrateFloor

/--
Generic finite-error version of the same bridge.  This is useful when the paper
indexes only the pivotal cross-tier comparisons rather than all ordered
candidate pairs.
-/
theorem finiteOutcomeError_hasExpUpperBound_of_rate_certificates
    {ι : Type*} [Fintype ι]
    (C : FiniteErrorRateCertificate ι)
    {weight : ι → ℝ} {targetRate : ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hrate : ∀ i, targetRate < C.rate i) :
    HasExpUpperBoundWithConst (C.aggregateError weight) targetRate :=
  C.aggregateError_hasExpUpperBoundWithConst_of_lt hweight hrate

/-! ## Randomization comparisons -/

/--
If every pivotal pair has weakly higher rate under one rule, then the finite
minimum outcome-learning rate is weakly higher under that rule.
-/
theorem finiteOutcomeLearningRate_mono
    {Pair : Type*} [Fintype Pair] [Nonempty Pair]
    {lowRate highRate : Pair → ℝ}
    (hpair : ∀ pair, lowRate pair ≤ highRate pair) :
    finiteOutcomeLearningRate lowRate ≤ finiteOutcomeLearningRate highRate := by
  unfold finiteOutcomeLearningRate
  exact Finset.le_inf' _ _ (fun pair hpair_mem =>
    (Finset.inf'_le _ hpair_mem).trans (hpair pair))

/--
Randomized scoring comparison core: once the pairwise convexity step supplies a
static scoring rule whose pivotal pair rates dominate the randomized scoring
rule pair-by-pair, the static rule also weakly dominates the randomized rule in
the finite outcome-learning rate.
-/
theorem randomizedScoring_outcomeRate_le_static_of_pairwise
    {Pair : Type*} [Fintype Pair] [Nonempty Pair]
    (staticRate randomizedRate : Pair → ℝ)
    (hpair : ∀ pair, randomizedRate pair ≤ staticRate pair) :
    finiteOutcomeLearningRate randomizedRate ≤
      finiteOutcomeLearningRate staticRate :=
  finiteOutcomeLearningRate_mono hpair

/--
Source theorem `lem:randomizebetterscoring`, finite-outcome version: the static
convex-combination scoring rule weakly dominates the randomized scoring-rule
mixture in the finite outcome-learning rate.
-/
theorem randomizedScoring_outcomeRate_le_static_of_weighted_score
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
  randomizedScoring_outcomeRate_le_static_of_pairwise
    (fun pair : Pair => finiteChernoffRate law (staticGap pair))
    (fun pair : Pair => randomizedScoringMixtureRate law weight (gap pair))
    (fun pair =>
      randomizedScoringMixtureRate_le_static_of_weighted_score
        law weight (gap pair) (staticGap pair)
        (hstatic pair) hweight hsum (hstatic_bdd pair))

/--
Source-facing finite-outcome randomized-scoring comparison with the per-pair
bounded-below log-MGF premises discharged from concrete positive and negative
static atoms.
-/
theorem randomizedScoring_outcomeRate_le_static_of_weighted_score_of_pos_neg_atoms
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
    {aPos aNeg : Pair → Signal}
    (hmassPos : ∀ pair, 0 < (law (aPos pair)).toReal)
    (hgapPos : ∀ pair, 0 < staticGap pair (aPos pair))
    (hmassNeg : ∀ pair, 0 < (law (aNeg pair)).toReal)
    (hgapNeg : ∀ pair, staticGap pair (aNeg pair) < 0) :
    finiteOutcomeLearningRate
        (fun pair : Pair =>
          randomizedScoringMixtureRate law weight (gap pair)) ≤
      finiteOutcomeLearningRate
        (fun pair : Pair => finiteChernoffRate law (staticGap pair)) :=
  randomizedScoring_outcomeRate_le_static_of_weighted_score
    law weight gap staticGap hstatic hweight hsum
    (fun pair =>
      finiteLogMGF_bddBelow_of_pos_neg_atoms
        law (staticGap pair)
        (hmassPos pair) (hgapPos pair) (hmassNeg pair) (hgapNeg pair))

/--
Source theorem `lem:randomizebetterscoring`, finite-outcome version for the
one-sided zero-gap boundary: positive zero static-gap probability is enough to
make the static log-MGF range bounded below, so the same convexity comparison
applies.
-/
theorem randomizedScoring_outcomeRate_le_static_of_weighted_score_of_zero_score_prob_pos
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
    (hzero_pos :
      ∀ pair,
        0 < AppliedModelingLib.pmfProb law (fun signal => staticGap pair signal = 0)) :
    finiteOutcomeLearningRate
        (fun pair : Pair =>
          randomizedScoringMixtureRate law weight (gap pair)) ≤
      finiteOutcomeLearningRate
        (fun pair : Pair => finiteChernoffRate law (staticGap pair)) :=
  randomizedScoring_outcomeRate_le_static_of_weighted_score
    law weight gap staticGap hstatic hweight hsum
    (fun pair =>
      finiteLogMGF_bddBelow_of_zero_score_prob_pos
        law (staticGap pair) (hzero_pos pair))

/--
Source theorem `lem:randomizebetterscoring`, actual finite-outcome version:
the one-voter experiment that first samples a scoring rule and then samples a
signal is weakly dominated by the static convex-combination scoring rule.
-/
theorem randomizedScoringActual_outcomeRate_le_static_of_weighted_score
    {Pair Rule Signal : Type*} [Fintype Pair] [Nonempty Pair]
    [Fintype Rule] [DecidableEq Rule] [Fintype Signal] [DecidableEq Signal]
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
          finiteChernoffRate
            (randomizedScoringSamplingLaw law weight hweight hsum)
            (fun signal : Rule × Signal => gap pair signal.1 signal.2)) ≤
      finiteOutcomeLearningRate
        (fun pair : Pair => finiteChernoffRate law (staticGap pair)) := by
  simpa [randomizedScoringSamplingLaw_finiteChernoffRate_eq_mixtureRate] using
    randomizedScoring_outcomeRate_le_static_of_weighted_score
      law weight gap staticGap hstatic hweight hsum hstatic_bdd

/--
Actual finite-outcome randomized-scoring comparison with the per-pair static
boundedness side conditions discharged from concrete positive and negative
static atoms.
-/
theorem randomizedScoringActual_outcomeRate_le_static_of_weighted_score_of_pos_neg_atoms
    {Pair Rule Signal : Type*} [Fintype Pair] [Nonempty Pair]
    [Fintype Rule] [DecidableEq Rule] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ)
    (gap : Pair → Rule → Signal → ℝ)
    (staticGap : Pair → Signal → ℝ)
    (hstatic :
      ∀ pair signal,
        staticGap pair signal =
          ∑ rule : Rule, weight rule * gap pair rule signal)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    {aPos aNeg : Pair → Signal}
    (hmassPos : ∀ pair, 0 < (law (aPos pair)).toReal)
    (hgapPos : ∀ pair, 0 < staticGap pair (aPos pair))
    (hmassNeg : ∀ pair, 0 < (law (aNeg pair)).toReal)
    (hgapNeg : ∀ pair, staticGap pair (aNeg pair) < 0) :
    finiteOutcomeLearningRate
        (fun pair : Pair =>
          finiteChernoffRate
            (randomizedScoringSamplingLaw law weight hweight hsum)
            (fun signal : Rule × Signal => gap pair signal.1 signal.2)) ≤
      finiteOutcomeLearningRate
        (fun pair : Pair => finiteChernoffRate law (staticGap pair)) :=
  randomizedScoringActual_outcomeRate_le_static_of_weighted_score
    law weight gap staticGap hstatic hweight hsum
    (fun pair =>
      finiteLogMGF_bddBelow_of_pos_neg_atoms
        law (staticGap pair)
        (hmassPos pair) (hgapPos pair) (hmassNeg pair) (hgapNeg pair))

/--
Actual finite-outcome randomized-scoring comparison for the one-sided
zero-gap boundary.
-/
theorem randomizedScoringActual_outcomeRate_le_static_of_weighted_score_of_zero_score_prob_pos
    {Pair Rule Signal : Type*} [Fintype Pair] [Nonempty Pair]
    [Fintype Rule] [DecidableEq Rule] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ)
    (gap : Pair → Rule → Signal → ℝ)
    (staticGap : Pair → Signal → ℝ)
    (hstatic :
      ∀ pair signal,
        staticGap pair signal =
          ∑ rule : Rule, weight rule * gap pair rule signal)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hzero_pos :
      ∀ pair,
        0 < AppliedModelingLib.pmfProb law (fun signal => staticGap pair signal = 0)) :
    finiteOutcomeLearningRate
        (fun pair : Pair =>
          finiteChernoffRate
            (randomizedScoringSamplingLaw law weight hweight hsum)
            (fun signal : Rule × Signal => gap pair signal.1 signal.2)) ≤
      finiteOutcomeLearningRate
        (fun pair : Pair => finiteChernoffRate law (staticGap pair)) := by
  simpa [randomizedScoringSamplingLaw_finiteChernoffRate_eq_mixtureRate] using
    randomizedScoring_outcomeRate_le_static_of_weighted_score_of_zero_score_prob_pos
      law weight gap staticGap hstatic hweight hsum hzero_pos

/--
One-pair actual-law randomized-scoring comparison to a named finite bound.  The
weighted static score first dominates the actual randomized pairwise Chernoff
rate; a separate bound on the static Chernoff expression then names the target
rate used by aggregate endpoints.
-/
theorem randomizedScoringActual_pairwiseRate_le_bound_of_weighted_score
    {Rule Signal : Type*} [Fintype Rule] [DecidableEq Rule]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ)
    (gap : Rule → Signal → ℝ)
    (staticGap : Signal → ℝ)
    (hstatic :
      ∀ signal,
        staticGap signal =
          ∑ rule : Rule, weight rule * gap rule signal)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hstatic_bdd :
      BddBelow (Set.range fun z : ℝ => finiteLogMGF law staticGap z))
    {targetRate : ℝ}
    (hstatic_le_target :
      finiteChernoffRate law staticGap ≤ targetRate) :
    finiteChernoffRate
        (randomizedScoringSamplingLaw law weight hweight hsum)
        (fun signal : Rule × Signal => gap signal.1 signal.2) ≤
      targetRate := by
  have hpair :
      finiteChernoffRate
          (randomizedScoringSamplingLaw law weight hweight hsum)
          (fun signal : Rule × Signal => gap signal.1 signal.2) ≤
        finiteChernoffRate law staticGap := by
    simpa [randomizedScoringSamplingLaw_finiteChernoffRate_eq_mixtureRate] using
      randomizedScoringMixtureRate_le_static_of_weighted_score
        law weight gap staticGap hstatic hweight hsum hstatic_bdd
  exact hpair.trans hstatic_le_target

/--
Prefix-score specialization of the one-pair actual-law randomized-scoring
comparison to a named finite bound.
-/
theorem randomizedScoringPrefixActual_pairwiseRate_le_bound_of_weighted_score
    {Rule Cut Candidate Signal : Type*}
    [Fintype Rule] [DecidableEq Rule] [Fintype Cut]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (hi lo : Candidate)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hstatic_bdd :
      BddBelow (Set.range fun z : ℝ =>
        finiteLogMGF law
          (fun signal =>
            prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix hi signal -
              prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix lo signal) z))
    {targetRate : ℝ}
    (hstatic_le_target :
      finiteChernoffRate law
          (fun signal =>
            prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix hi signal -
              prefixScoreFromEvent
                (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                inPrefix lo signal) ≤
        targetRate) :
    finiteChernoffRate
        (randomizedScoringSamplingLaw law weight hweight hsum)
        (fun signal : Rule × Signal =>
          prefixScoreFromEvent (diff signal.1) inPrefix hi signal.2 -
            prefixScoreFromEvent (diff signal.1) inPrefix lo signal.2) ≤
      targetRate :=
  randomizedScoringActual_pairwiseRate_le_bound_of_weighted_score
    law weight
    (fun rule signal =>
      prefixScoreFromEvent (diff rule) inPrefix hi signal -
        prefixScoreFromEvent (diff rule) inPrefix lo signal)
    (fun signal =>
      prefixScoreFromEvent
          (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
          inPrefix hi signal -
        prefixScoreFromEvent
          (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
          inPrefix lo signal)
    (by
      intro signal
      dsimp
      rw [prefixScoreFromEvent_weighted_sum weight diff inPrefix hi signal]
      rw [prefixScoreFromEvent_weighted_sum weight diff inPrefix lo signal]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro rule _
      ring)
    hweight hsum hstatic_bdd hstatic_le_target

/--
Prefix-score specialization of `lem:randomizebetterscoring`: for a finite
randomization over positional prefix-weight vectors, the static
convex-combination prefix-score rule weakly dominates the randomized scoring
mixture in finite outcome-learning rate.  The only analytic side condition is
the concrete two-sided support of each static convex-combination pairwise gap.
-/
theorem randomizedScoringPrefix_outcomeRate_le_static_of_weighted_score_of_pos_neg_atoms
    {Pair Rule Cut Candidate Signal : Type*}
    [Fintype Pair] [Nonempty Pair] [Fintype Rule] [Fintype Cut]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (hi lo : Pair → Candidate)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    {aPos aNeg : Pair → Signal}
    (hmassPos : ∀ pair, 0 < (law (aPos pair)).toReal)
    (hgapPos :
      ∀ pair,
        0 <
          prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix (hi pair) (aPos pair) -
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix (lo pair) (aPos pair))
    (hmassNeg : ∀ pair, 0 < (law (aNeg pair)).toReal)
    (hgapNeg :
      ∀ pair,
          prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix (hi pair) (aNeg pair) -
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix (lo pair) (aNeg pair) < 0) :
    finiteOutcomeLearningRate
        (fun pair : Pair =>
          randomizedScoringMixtureRate law weight
            (fun rule signal =>
              prefixScoreFromEvent (diff rule) inPrefix (hi pair) signal -
                prefixScoreFromEvent (diff rule) inPrefix (lo pair) signal)) ≤
      finiteOutcomeLearningRate
        (fun pair : Pair =>
          finiteChernoffRate law
            (fun signal =>
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix (hi pair) signal -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix (lo pair) signal)) :=
  randomizedScoring_outcomeRate_le_static_of_weighted_score_of_pos_neg_atoms
    law weight
    (fun pair rule signal =>
      prefixScoreFromEvent (diff rule) inPrefix (hi pair) signal -
        prefixScoreFromEvent (diff rule) inPrefix (lo pair) signal)
    (fun pair signal =>
      prefixScoreFromEvent
          (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
          inPrefix (hi pair) signal -
        prefixScoreFromEvent
          (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
          inPrefix (lo pair) signal)
    (by
      intro pair signal
      dsimp
      rw [prefixScoreFromEvent_weighted_sum weight diff inPrefix
          (hi pair) signal]
      rw [prefixScoreFromEvent_weighted_sum weight diff inPrefix
          (lo pair) signal]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro rule _
      ring)
    hweight hsum hmassPos hgapPos hmassNeg hgapNeg

/--
Actual prefix-score specialization of `lem:randomizebetterscoring`: the
one-voter law that samples a positional scoring rule before the signal is
weakly dominated by the static convex-combination prefix-score rule.
-/
theorem randomizedScoringPrefixActual_outcomeRate_le_static_of_weighted_score_of_pos_neg_atoms
    {Pair Rule Cut Candidate Signal : Type*}
    [Fintype Pair] [Nonempty Pair] [Fintype Rule] [DecidableEq Rule]
    [Fintype Cut] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (hi lo : Pair → Candidate)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    {aPos aNeg : Pair → Signal}
    (hmassPos : ∀ pair, 0 < (law (aPos pair)).toReal)
    (hgapPos :
      ∀ pair,
        0 <
          prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix (hi pair) (aPos pair) -
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix (lo pair) (aPos pair))
    (hmassNeg : ∀ pair, 0 < (law (aNeg pair)).toReal)
    (hgapNeg :
      ∀ pair,
          prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix (hi pair) (aNeg pair) -
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix (lo pair) (aNeg pair) < 0) :
    finiteOutcomeLearningRate
        (fun pair : Pair =>
          finiteChernoffRate
            (randomizedScoringSamplingLaw law weight hweight hsum)
            (fun signal : Rule × Signal =>
              prefixScoreFromEvent (diff signal.1) inPrefix
                  (hi pair) signal.2 -
                prefixScoreFromEvent (diff signal.1) inPrefix
                  (lo pair) signal.2)) ≤
      finiteOutcomeLearningRate
        (fun pair : Pair =>
          finiteChernoffRate law
            (fun signal =>
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix (hi pair) signal -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix (lo pair) signal)) :=
  randomizedScoringActual_outcomeRate_le_static_of_weighted_score_of_pos_neg_atoms
    law weight
    (fun pair rule signal =>
      prefixScoreFromEvent (diff rule) inPrefix (hi pair) signal -
        prefixScoreFromEvent (diff rule) inPrefix (lo pair) signal)
    (fun pair signal =>
      prefixScoreFromEvent
          (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
          inPrefix (hi pair) signal -
        prefixScoreFromEvent
          (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
          inPrefix (lo pair) signal)
    (by
      intro pair signal
      dsimp
      rw [prefixScoreFromEvent_weighted_sum weight diff inPrefix
          (hi pair) signal]
      rw [prefixScoreFromEvent_weighted_sum weight diff inPrefix
          (lo pair) signal]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro rule _
      ring)
    hweight hsum hmassPos hgapPos hmassNeg hgapNeg

/--
Actual prefix-score randomized-scoring comparison for the one-sided zero-gap
boundary.  Positive zero static-gap probability for every relevant pair
discharges the bounded-below log-MGF side condition.
-/
theorem randomizedScoringPrefixActual_outcomeRate_le_static_of_weighted_score_of_zero_score_prob_pos
    {Pair Rule Cut Candidate Signal : Type*}
    [Fintype Pair] [Nonempty Pair] [Fintype Rule] [DecidableEq Rule]
    [Fintype Cut] [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (hi lo : Pair → Candidate)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hzero_pos :
      ∀ pair,
        0 <
          AppliedModelingLib.pmfProb law
            (fun signal =>
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix (hi pair) signal -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix (lo pair) signal = 0)) :
    finiteOutcomeLearningRate
        (fun pair : Pair =>
          finiteChernoffRate
            (randomizedScoringSamplingLaw law weight hweight hsum)
            (fun signal : Rule × Signal =>
              prefixScoreFromEvent (diff signal.1) inPrefix
                  (hi pair) signal.2 -
                prefixScoreFromEvent (diff signal.1) inPrefix
                  (lo pair) signal.2)) ≤
      finiteOutcomeLearningRate
        (fun pair : Pair =>
          finiteChernoffRate law
            (fun signal =>
              prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix (hi pair) signal -
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix (lo pair) signal)) :=
  randomizedScoringActual_outcomeRate_le_static_of_weighted_score_of_zero_score_prob_pos
    law weight
    (fun pair rule signal =>
      prefixScoreFromEvent (diff rule) inPrefix (hi pair) signal -
        prefixScoreFromEvent (diff rule) inPrefix (lo pair) signal)
    (fun pair signal =>
      prefixScoreFromEvent
          (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
          inPrefix (hi pair) signal -
        prefixScoreFromEvent
          (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
          inPrefix (lo pair) signal)
    (by
      intro pair signal
      dsimp
      rw [prefixScoreFromEvent_weighted_sum weight diff inPrefix
          (hi pair) signal]
      rw [prefixScoreFromEvent_weighted_sum weight diff inPrefix
          (lo pair) signal]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro rule _
      ring)
    hweight hsum hzero_pos

/--
Source-shaped randomized-scoring theorem over the true W-set boundary pairs:
the finite randomized prefix-score mechanism has a reasonable static
convex-combination rule, that static rule selects the true W-set
asymptotically under Proposition 1 strict dominance, and the randomized
outcome-learning rate is weakly dominated by the static convex-combination
outcome-learning rate.
-/
theorem randomizedScoringPrefix_crossTier_static_selection_and_rate
    {Rule Cut Candidate Signal : Type*}
    [Fintype Rule] [Fintype Cut] [DecidableEq Cut]
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
        (fun hi lo => hi ∈ winnerSet ∧ lo ∉ winnerSet))
    {aPos aNeg : CrossTierPair winnerSet → Signal}
    (hmassPos : ∀ pair, 0 < (law (aPos pair)).toReal)
    (hgapPos :
      ∀ pair,
        0 <
          prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix pair.hi (aPos pair) -
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix pair.lo (aPos pair))
    (hmassNeg : ∀ pair, 0 < (law (aNeg pair)).toReal)
    (hgapNeg :
      ∀ pair,
          prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix pair.hi (aNeg pair) -
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix pair.lo (aNeg pair) < 0) :
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
      finiteOutcomeLearningRate
          (fun pair : CrossTierPair winnerSet =>
            randomizedScoringMixtureRate law weight
              (fun rule signal =>
                prefixScoreFromEvent (diff rule) inPrefix pair.hi signal -
                  prefixScoreFromEvent (diff rule) inPrefix pair.lo signal)) ≤
        finiteOutcomeLearningRate
          (fun pair : CrossTierPair winnerSet =>
            finiteChernoffRate law
              (fun signal =>
                prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix pair.hi signal -
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix pair.lo signal)) := by
  let staticDiff : Cut → ℝ :=
    fun cut => ∑ rule : Rule, weight rule * diff rule cut
  have hstatic_reasonable : ReasonablePrefixWeights staticDiff :=
    ReasonablePrefixWeights.weighted_sum weight diff hweight hsum hdiff
  refine ⟨hstatic_reasonable, ?_, ?_⟩
  · simpa [staticDiff] using
      prefixScoringCanonicalSelectionError_tendsto_zero_on
        law staticDiff inPrefix winnerSet hdom hstatic_reasonable
  · simpa [staticDiff] using
      randomizedScoringPrefix_outcomeRate_le_static_of_weighted_score_of_pos_neg_atoms
        (Pair := CrossTierPair winnerSet)
        law weight diff inPrefix
        (fun pair : CrossTierPair winnerSet => pair.hi)
        (fun pair : CrossTierPair winnerSet => pair.lo)
        hweight hsum hmassPos hgapPos hmassNeg hgapNeg

/--
Actual-law version of the source-shaped randomized-scoring theorem over the
true W-set boundary pairs.
-/
theorem randomizedScoringPrefixActual_crossTier_static_selection_and_rate
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
        (fun hi lo => hi ∈ winnerSet ∧ lo ∉ winnerSet))
    {aPos aNeg : CrossTierPair winnerSet → Signal}
    (hmassPos : ∀ pair, 0 < (law (aPos pair)).toReal)
    (hgapPos :
      ∀ pair,
        0 <
          prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix pair.hi (aPos pair) -
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix pair.lo (aPos pair))
    (hmassNeg : ∀ pair, 0 < (law (aNeg pair)).toReal)
    (hgapNeg :
      ∀ pair,
          prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix pair.hi (aNeg pair) -
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix pair.lo (aNeg pair) < 0) :
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
      finiteOutcomeLearningRate
          (fun pair : CrossTierPair winnerSet =>
            finiteChernoffRate
              (randomizedScoringSamplingLaw law weight hweight hsum)
              (fun signal : Rule × Signal =>
                prefixScoreFromEvent (diff signal.1) inPrefix
                    pair.hi signal.2 -
                  prefixScoreFromEvent (diff signal.1) inPrefix
                    pair.lo signal.2)) ≤
        finiteOutcomeLearningRate
          (fun pair : CrossTierPair winnerSet =>
            finiteChernoffRate law
              (fun signal =>
                prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix pair.hi signal -
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix pair.lo signal)) := by
  let staticDiff : Cut → ℝ :=
    fun cut => ∑ rule : Rule, weight rule * diff rule cut
  have hstatic_reasonable : ReasonablePrefixWeights staticDiff :=
    ReasonablePrefixWeights.weighted_sum weight diff hweight hsum hdiff
  refine ⟨hstatic_reasonable, ?_, ?_⟩
  · simpa [staticDiff] using
      prefixScoringCanonicalSelectionError_tendsto_zero_on
        law staticDiff inPrefix winnerSet hdom hstatic_reasonable
  · simpa [staticDiff] using
      randomizedScoringPrefixActual_outcomeRate_le_static_of_weighted_score_of_pos_neg_atoms
        (Pair := CrossTierPair winnerSet)
        law weight diff inPrefix
        (fun pair : CrossTierPair winnerSet => pair.hi)
        (fun pair : CrossTierPair winnerSet => pair.lo)
        hweight hsum hmassPos hgapPos hmassNeg hgapNeg

/--
Automatic source-shaped randomized-scoring static aggregate theorem over the
true W-set boundary pairs.  Proposition 1 strict dominance makes the
convex-combination static rule reasonable and asymptotically correct; the
finite-support Proposition 2 trichotomy then implies that its relevant
pairwise mistake aggregate either has an exact finite exponential rate or is
eventually zero.  This is the extended-rate-friendly branch of Theorem 1 that
does not require callers to pre-classify two-sided and one-sided supports.
-/
theorem randomizedScoringPrefixActual_crossTier_static_selection_and_automatic_static_aggregate
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
      ((∃ minRate : ℝ,
        HasExponentialRate
          (fun sampleSize =>
            ∑ pair : CrossTierPair winnerSet,
              finiteScoreGapPairwiseErrorProb law
                (fun candidate =>
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix candidate)
                pair.hi pair.lo sampleSize)
          minRate) ∨
        (∀ᶠ n in Filter.atTop,
          (∑ pair : CrossTierPair winnerSet,
            finiteScoreGapPairwiseErrorProb law
              (fun candidate =>
                prefixScoreFromEvent
                  (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                  inPrefix candidate)
              pair.hi pair.lo n) = 0)) := by
  classical
  let staticDiff : Cut → ℝ :=
    fun cut => ∑ rule : Rule, weight rule * diff rule cut
  have hstatic_reasonable : ReasonablePrefixWeights staticDiff :=
    ReasonablePrefixWeights.weighted_sum weight diff hweight hsum hdiff
  have hmean :
      ∀ pair : CrossTierPair winnerSet,
        0 ≤
          AppliedModelingLib.pmfExp law
            (fun signal =>
              prefixScoreFromEvent staticDiff inPrefix pair.hi signal -
                prefixScoreFromEvent staticDiff inPrefix pair.lo signal) := by
    intro pair
    exact le_of_lt
      (pmfExp_prefixScore_gap_pos_of_strictTopPrefixDominance
        law staticDiff inPrefix
        (hdom pair.hi pair.lo ⟨pair.hi_mem, pair.lo_not_mem⟩)
        hstatic_reasonable)
  have hagg :
      (∃ minRate : ℝ,
        HasExponentialRate
          (fun sampleSize =>
            ∑ pair : CrossTierPair winnerSet,
              (1 : ℝ) *
                finiteScoreGapPairwiseErrorProb law
                  (fun candidate =>
                    prefixScoreFromEvent staticDiff inPrefix candidate)
                  pair.hi pair.lo sampleSize)
          minRate) ∨
        (∀ᶠ n in Filter.atTop,
          (∑ pair : CrossTierPair winnerSet,
            (1 : ℝ) *
              finiteScoreGapPairwiseErrorProb law
                (fun candidate =>
                  prefixScoreFromEvent staticDiff inPrefix candidate)
                pair.hi pair.lo n) = 0) := by
    exact
      outcomeError_hasExponentialRate_or_eventually_zero_of_relevant_pairs_finite_support_trichotomy
        (Pair := CrossTierPair winnerSet)
        law
        (fun candidate => prefixScoreFromEvent staticDiff inPrefix candidate)
        (fun pair : CrossTierPair winnerSet => pair.hi)
        (fun pair : CrossTierPair winnerSet => pair.lo)
        hmean
        (pairWeight := fun _ => (1 : ℝ))
        (by intro pair; norm_num)
        (by intro pair; norm_num)
  refine ⟨hstatic_reasonable, ?_, ?_⟩
  · simpa [staticDiff] using
      prefixScoringCanonicalSelectionError_tendsto_zero_on
        law staticDiff inPrefix winnerSet hdom hstatic_reasonable
  · rcases hagg with hfinite | hzero
    · left
      rcases hfinite with ⟨minRate, hrate⟩
      exact ⟨minRate, by simpa [staticDiff] using hrate⟩
    · right
      simpa [staticDiff] using hzero

/--
A finite weighted average is no larger than the best static member of the
finite family.
-/
theorem finiteWeightedAverage_le_bestStatic
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (weight value : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1) :
    (∑ rule : Rule, weight rule * value rule) ≤
      (Finset.univ : Finset Rule).sup' finiteUnivNonempty value := by
  calc
    (∑ rule : Rule, weight rule * value rule) ≤
        ∑ rule : Rule,
          weight rule *
            ((Finset.univ : Finset Rule).sup' finiteUnivNonempty value) := by
      refine Finset.sum_le_sum ?_
      intro rule _
      exact mul_le_mul_of_nonneg_left
        (Finset.le_sup' value
          (by simp : rule ∈ (Finset.univ : Finset Rule)))
        (hweight rule)
    _ = (∑ rule : Rule, weight rule) *
        ((Finset.univ : Finset Rule).sup' finiteUnivNonempty value) := by
      rw [Finset.sum_mul]
    _ = (Finset.univ : Finset Rule).sup' finiteUnivNonempty value := by
      rw [hsum, one_mul]

/--
If a randomized rule's rate is bounded by the weighted average of finitely many
static-rule rates, then some static rule weakly beats that randomized rate.
-/
theorem exists_static_rule_beats_randomized_rate_of_average_bound
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (weight value : Rule → ℝ) {randomizedRate : ℝ}
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (haverage : randomizedRate ≤
      ∑ rule : Rule, weight rule * value rule) :
    ∃ rule : Rule, randomizedRate ≤ value rule := by
  rcases (Finset.univ : Finset Rule).exists_mem_eq_sup'
      finiteUnivNonempty value with
    ⟨rule, _, hbest⟩
  refine ⟨rule, ?_⟩
  rw [← hbest]
  exact haverage.trans
    (finiteWeightedAverage_le_bestStatic weight value hweight hsum)

/--
Randomized K-approval comparison core: once the paper's convexity step supplies
that the randomized approval rate is at most the weighted average of the static
K-approval rates, some static K-approval rule weakly beats the randomized rule
for that pair.
-/
theorem randomizedApproval_pairwiseRate_le_static_of_convexity
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (weight pUp pDown : Rule → ℝ)
    {mixedUp mixedDown : ℝ}
    (hmixedUp : mixedUp = ∑ rule : Rule, weight rule * pUp rule)
    (hmixedDown : mixedDown = ∑ rule : Rule, weight rule * pDown rule)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hconvex :
      approvalPairwiseRate mixedUp mixedDown ≤
        ∑ rule : Rule,
          weight rule * approvalPairwiseRate (pUp rule) (pDown rule)) :
    ∃ rule : Rule,
      approvalPairwiseRate mixedUp mixedDown ≤
        approvalPairwiseRate (pUp rule) (pDown rule) := by
  exact exists_static_rule_beats_randomized_rate_of_average_bound
    weight (fun rule => approvalPairwiseRate (pUp rule) (pDown rule))
    hweight hsum hconvex

/--
K-approval no-randomization pairwise theorem on the positive-base region:
some static K-approval rule weakly beats the randomized K-approval rule for the
pair.  Boundary zero-base cases require an extended-real rate and remain outside
this real-valued statement.
-/
theorem randomizedApproval_pairwiseRate_le_static
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (weight pUp pDown : Rule → ℝ)
    {mixedUp mixedDown : ℝ}
    (hmixedUp : mixedUp = ∑ rule : Rule, weight rule * pUp rule)
    (hmixedDown : mixedDown = ∑ rule : Rule, weight rule * pDown rule)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hUp : ∀ rule, 0 ≤ pUp rule)
    (hDown : ∀ rule, 0 ≤ pDown rule)
    (hbase_pos :
      ∀ rule, 0 < approvalPairwiseBase (pUp rule) (pDown rule))
    (hmixed_base_pos : 0 < approvalPairwiseBase mixedUp mixedDown) :
    ∃ rule : Rule,
      approvalPairwiseRate mixedUp mixedDown ≤
        approvalPairwiseRate (pUp rule) (pDown rule) := by
  exact randomizedApproval_pairwiseRate_le_static_of_convexity
    weight pUp pDown hmixedUp hmixedDown hweight hsum
    (approvalPairwiseRate_weighted_le
      weight pUp pDown hmixedUp hmixedDown hweight hsum
      hUp hDown hbase_pos hmixed_base_pos)

/--
K-approval no-randomization pairwise theorem allowing the randomized mixture
to land on the real-valued boundary.  Static rules remain in the positive-base
region used by the Jensen/log proof; if the mixed base is zero, the total-real
closed-form rate is `0`, so any valid static rule weakly beats it.
-/
theorem randomizedApproval_pairwiseRate_le_static_or_mixed_boundary
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (weight pUp pDown : Rule → ℝ)
    {mixedUp mixedDown : ℝ}
    (hmixedUp : mixedUp = ∑ rule : Rule, weight rule * pUp rule)
    (hmixedDown : mixedDown = ∑ rule : Rule, weight rule * pDown rule)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hUp : ∀ rule, 0 ≤ pUp rule)
    (hDown : ∀ rule, 0 ≤ pDown rule)
    (hprob : ∀ rule, pUp rule + pDown rule ≤ 1)
    (hbase_pos :
      ∀ rule, 0 < approvalPairwiseBase (pUp rule) (pDown rule)) :
    ∃ rule : Rule,
      approvalPairwiseRate mixedUp mixedDown ≤
        approvalPairwiseRate (pUp rule) (pDown rule) := by
  by_cases hmixed_base_pos : 0 < approvalPairwiseBase mixedUp mixedDown
  · exact randomizedApproval_pairwiseRate_le_static
      weight pUp pDown hmixedUp hmixedDown hweight hsum hUp hDown
      hbase_pos hmixed_base_pos
  · have hmixedUp_nonneg : 0 ≤ mixedUp := by
      rw [hmixedUp]
      exact (AppliedModelingLib.weightedPairProb_valid
        weight pUp pDown hweight hsum hUp hDown hprob).1
    have hmixedDown_nonneg : 0 ≤ mixedDown := by
      rw [hmixedDown]
      exact (AppliedModelingLib.weightedPairProb_valid
        weight pUp pDown hweight hsum hUp hDown hprob).2.1
    have hmixed_prob : mixedUp + mixedDown ≤ 1 := by
      rw [hmixedUp, hmixedDown]
      exact (AppliedModelingLib.weightedPairProb_valid
        weight pUp pDown hweight hsum hUp hDown hprob).2.2
    have hmixed_base_nonneg :
        0 ≤ approvalPairwiseBase mixedUp mixedDown :=
      (approvalPairwiseBase_mem_Icc_of_probabilities
        hmixedUp_nonneg hmixedDown_nonneg hmixed_prob).1
    have hmixed_base_zero :
        approvalPairwiseBase mixedUp mixedDown = 0 :=
      le_antisymm (le_of_not_gt hmixed_base_pos) hmixed_base_nonneg
    let rule : Rule := Classical.choice inferInstance
    refine ⟨rule, ?_⟩
    have hstatic_nonneg :
        0 ≤ approvalPairwiseRate (pUp rule) (pDown rule) :=
      approvalPairwiseRate_nonneg_of_probabilities
        (hUp rule) (hDown rule) (hprob rule)
    have hmixed_rate_zero :
        approvalPairwiseRate mixedUp mixedDown = 0 := by
      rw [approvalPairwiseRate_eq_neg_log_base, hmixed_base_zero]
      simp
    rw [hmixed_rate_zero]
    exact hstatic_nonneg

/--
Source-shaped fixed-pair K-approval no-randomization theorem over valid
approval probabilities.  If every static rule has a positive real-valued
approval base, then some static K-approval rule weakly beats the randomized
pairwise rate.  Otherwise Lean reports the static degenerate boundary rule
whose closed-form real rate is outside the positive-base Jensen argument.
-/
theorem randomizedApproval_pairwiseRate_le_static_of_valid_probabilities_or_static_boundary
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (weight pUp pDown : Rule → ℝ)
    {mixedUp mixedDown : ℝ}
    (hmixedUp : mixedUp = ∑ rule : Rule, weight rule * pUp rule)
    (hmixedDown : mixedDown = ∑ rule : Rule, weight rule * pDown rule)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hUp : ∀ rule, 0 ≤ pUp rule)
    (hDown : ∀ rule, 0 ≤ pDown rule)
    (hprob : ∀ rule, pUp rule + pDown rule ≤ 1) :
    (∃ rule : Rule,
      approvalPairwiseRate mixedUp mixedDown ≤
        approvalPairwiseRate (pUp rule) (pDown rule)) ∨
      (∃ rule : Rule,
        approvalPairwiseBase (pUp rule) (pDown rule) = 0) := by
  by_cases hbase_pos :
      ∀ rule, 0 < approvalPairwiseBase (pUp rule) (pDown rule)
  · left
    exact
      randomizedApproval_pairwiseRate_le_static_or_mixed_boundary
        weight pUp pDown hmixedUp hmixedDown hweight hsum
        hUp hDown hprob hbase_pos
  · right
    simp only [not_forall, not_lt] at hbase_pos
    rcases hbase_pos with ⟨rule, hnot_pos⟩
    refine ⟨rule, ?_⟩
    have hbase_nonneg :
        0 ≤ approvalPairwiseBase (pUp rule) (pDown rule) :=
      (approvalPairwiseBase_mem_Icc_of_probabilities
        (hUp rule) (hDown rule) (hprob rule)).1
    exact le_antisymm hnot_pos hbase_nonneg

/--
Source-shaped fixed-pair K-approval no-randomization theorem in extended-rate
form.  A static component weakly beats the randomized pairwise rate; when that
static component is on the zero-base boundary, its extended rate is `⊤`.
-/
theorem randomizedApproval_pairwiseRate_le_static_extended_of_valid_probabilities
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (weight pUp pDown : Rule → ℝ)
    {mixedUp mixedDown : ℝ}
    (hmixedUp : mixedUp = ∑ rule : Rule, weight rule * pUp rule)
    (hmixedDown : mixedDown = ∑ rule : Rule, weight rule * pDown rule)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hUp : ∀ rule, 0 ≤ pUp rule)
    (hDown : ∀ rule, 0 ≤ pDown rule)
    (hprob : ∀ rule, pUp rule + pDown rule ≤ 1) :
    ∃ rule : Rule,
      (approvalPairwiseRate mixedUp mixedDown : WithTop ℝ) ≤
        approvalPairwiseExtendedRate (pUp rule) (pDown rule) := by
  rcases
      randomizedApproval_pairwiseRate_le_static_of_valid_probabilities_or_static_boundary
        weight pUp pDown hmixedUp hmixedDown hweight hsum
        hUp hDown hprob with
    hfinite | hboundary
  · rcases hfinite with ⟨rule, hcompare⟩
    refine ⟨rule, ?_⟩
    by_cases hzero : approvalPairwiseBase (pUp rule) (pDown rule) = 0
    · simpa [approvalPairwiseExtendedRate, hzero]
    · simpa [approvalPairwiseExtendedRate, hzero] using hcompare
  · rcases hboundary with ⟨rule, hzero⟩
    refine ⟨rule, ?_⟩
    simpa [approvalPairwiseExtendedRate, hzero]

/--
Actual fixed-pair K-approval no-randomization theorem: for any finite
randomization over K-approval rules and any ordered candidate pair, either
some static K-approval rule weakly beats the randomized pairwise closed-form
rate, or a static rule lies on the degenerate zero-base boundary.
-/
theorem randomizedKApproval_pairwiseRate_le_static_of_valid_probabilities_or_static_boundary
    {n : ℕ} {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n) :
    (∃ rule : Rule,
      approvalPairwiseRate
          (∑ rule : Rule,
            weight rule *
              AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
                law (K rule) hi lo)
          (∑ rule : Rule,
            weight rule *
              AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
                law (K rule) hi lo) ≤
        approvalPairwiseRate
          (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
            law (K rule) hi lo)
          (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
            law (K rule) hi lo)) ∨
      (∃ rule : Rule,
        approvalPairwiseBase
          (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
            law (K rule) hi lo)
          (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
            law (K rule) hi lo) = 0) :=
  randomizedApproval_pairwiseRate_le_static_of_valid_probabilities_or_static_boundary
    weight
    (fun rule : Rule =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law (K rule) hi lo)
    (fun rule : Rule =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law (K rule) hi lo)
    rfl rfl hweight hsum
    (fun rule =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb_nonneg
        law (K rule) hi lo)
    (fun rule =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb_nonneg
        law (K rule) hi lo)
    (fun rule =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb_add_downProb_le_one
        law (K rule) hi lo)

/--
Actual fixed-pair K-approval no-randomization theorem in extended-rate form:
for any finite randomization over K-approval rules and any ordered candidate
pair, some static K-approval rule weakly beats the randomized pairwise rate,
with zero-base static boundaries interpreted as top extended rates.
-/
theorem randomizedKApproval_pairwiseRate_le_static_extended
    {n : ℕ} {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n) :
    ∃ rule : Rule,
      (approvalPairwiseRate
          (∑ rule : Rule,
            weight rule *
              AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
                law (K rule) hi lo)
          (∑ rule : Rule,
            weight rule *
              AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
                law (K rule) hi lo) : WithTop ℝ) ≤
        approvalPairwiseExtendedRate
          (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
            law (K rule) hi lo)
          (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
            law (K rule) hi lo) :=
  randomizedApproval_pairwiseRate_le_static_extended_of_valid_probabilities
    weight
    (fun rule : Rule =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law (K rule) hi lo)
    (fun rule : Rule =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law (K rule) hi lo)
    rfl rfl hweight hsum
    (fun rule =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb_nonneg
        law (K rule) hi lo)
    (fun rule =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb_nonneg
        law (K rule) hi lo)
    (fun rule =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb_add_downProb_le_one
        law (K rule) hi lo)

/--
The mixed up-error probability induced by a finite randomized K-approval rule
is nonnegative.
-/
theorem randomizedKApproval_mixedPairUpProb_nonneg
    {n : ℕ} {Rule : Type*} [Fintype Rule]
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n) :
    0 ≤
      ∑ rule : Rule,
        weight rule *
          AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
            law (K rule) hi lo := by
  exact AppliedModelingLib.weightedSum_nonneg
    weight
    (fun rule : Rule =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law (K rule) hi lo)
    hweight
    (fun rule =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb_nonneg
        law (K rule) hi lo)

/--
The mixed up-error probability is positive when every randomized K-approval
component has positive up-error probability.
-/
theorem randomizedKApproval_mixedPairUpProb_pos
    {n : ℕ} {Rule : Type*} [Fintype Rule]
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (hUp_pos :
      ∀ rule,
        0 <
          AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
            law (K rule) hi lo) :
    0 <
      ∑ rule : Rule,
        weight rule *
          AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
            law (K rule) hi lo :=
  AppliedModelingLib.weightedSum_pos_of_nonneg_sum_eq_one
    weight
    (fun rule : Rule =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law (K rule) hi lo)
    hweight hsum hUp_pos

/--
The mixed up-error probability is positive when a positive-weight randomized
K-approval component has positive up-error probability.
-/
theorem randomizedKApproval_mixedPairUpProb_pos_of_positive_component
    {n : ℕ} {Rule : Type*} [Fintype Rule]
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    {rule₀ : Rule}
    (hweight_pos : 0 < weight rule₀)
    (hUp_pos :
      0 <
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
          law (K rule₀) hi lo) :
    0 <
      ∑ rule : Rule,
        weight rule *
          AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
            law (K rule) hi lo :=
  AppliedModelingLib.weightedSum_pos_of_positive_component
    weight
    (fun rule : Rule =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law (K rule) hi lo)
    hweight
    (fun rule =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb_nonneg
        law (K rule) hi lo)
    hweight_pos hUp_pos

/--
The mixed down-error probability induced by a finite randomized K-approval rule
is nonnegative.
-/
theorem randomizedKApproval_mixedPairDownProb_nonneg
    {n : ℕ} {Rule : Type*} [Fintype Rule]
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n) :
    0 ≤
      ∑ rule : Rule,
        weight rule *
          AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
            law (K rule) hi lo := by
  exact AppliedModelingLib.weightedSum_nonneg
    weight
    (fun rule : Rule =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law (K rule) hi lo)
    hweight
    (fun rule =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb_nonneg
        law (K rule) hi lo)

/--
The mixed down-error probability is positive when every randomized K-approval
component has positive down-error probability.
-/
theorem randomizedKApproval_mixedPairDownProb_pos
    {n : ℕ} {Rule : Type*} [Fintype Rule]
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (hDown_pos :
      ∀ rule,
        0 <
          AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
            law (K rule) hi lo) :
    0 <
      ∑ rule : Rule,
        weight rule *
          AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
            law (K rule) hi lo :=
  AppliedModelingLib.weightedSum_pos_of_nonneg_sum_eq_one
    weight
    (fun rule : Rule =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law (K rule) hi lo)
    hweight hsum hDown_pos

/--
The mixed down-error probability is positive when a positive-weight randomized
K-approval component has positive down-error probability.
-/
theorem randomizedKApproval_mixedPairDownProb_pos_of_positive_component
    {n : ℕ} {Rule : Type*} [Fintype Rule]
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    {rule₀ : Rule}
    (hweight_pos : 0 < weight rule₀)
    (hDown_pos :
      0 <
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
          law (K rule₀) hi lo) :
    0 <
      ∑ rule : Rule,
        weight rule *
          AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
            law (K rule) hi lo :=
  AppliedModelingLib.weightedSum_pos_of_positive_component
    weight
    (fun rule : Rule =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law (K rule) hi lo)
    hweight
    (fun rule =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb_nonneg
        law (K rule) hi lo)
    hweight_pos hDown_pos

/--
If every static K-approval component is oriented with down-probability at most
up-probability for a pair, then the randomized mixture has the same
orientation.
-/
theorem randomizedKApproval_mixedPairDownProb_le_upProb
    {n : ℕ} {Rule : Type*} [Fintype Rule]
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (hle :
      ∀ rule,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
            law (K rule) hi lo ≤
          AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
            law (K rule) hi lo) :
    (∑ rule : Rule,
        weight rule *
          AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
            law (K rule) hi lo) ≤
      ∑ rule : Rule,
        weight rule *
          AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
            law (K rule) hi lo :=
  AppliedModelingLib.weightedSum_le_weightedSum_of_pointwise_le
    weight
    (fun rule : Rule =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law (K rule) hi lo)
    (fun rule : Rule =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law (K rule) hi lo)
    hweight hle

/--
If every static K-approval component is oriented with down-probability at most
up-probability for each relevant pair, then the actual randomized K-approval
sampling law has nonnegative expected score gap on that pair.
-/
theorem randomizedKApproval_mixedExpectedGap_nonneg_of_static_down_le_up
    {n : ℕ} {Rule : Type*} [Fintype Rule] [DecidableEq Rule]
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (hle :
      ∀ rule,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
            law (K rule) hi lo ≤
          AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
            law (K rule) hi lo) :
    0 ≤
      AppliedModelingLib.pmfExp
        (randomizedScoringSamplingLaw law weight hweight hsum)
        (fun signal : Rule × AppliedModelingLib.SocialChoice.Ranking.Ranking n =>
          AppliedModelingLib.SocialChoice.Ranking.kApprovalScore
              (K signal.1) signal.2 hi -
            AppliedModelingLib.SocialChoice.Ranking.kApprovalScore
              (K signal.1) signal.2 lo) := by
  let gap : Rule → AppliedModelingLib.SocialChoice.Ranking.Ranking n → ℝ :=
    fun rule π =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalScore (K rule) π hi -
        AppliedModelingLib.SocialChoice.Ranking.kApprovalScore (K rule) π lo
  change
    0 ≤
      AppliedModelingLib.pmfExp
        (randomizedScoringSamplingLaw law weight hweight hsum)
        (fun signal : Rule × AppliedModelingLib.SocialChoice.Ranking.Ranking n =>
          gap signal.1 signal.2)
  rw [randomizedScoringSamplingLaw_pmfExp_eq_weighted_sum]
  exact
    AppliedModelingLib.weightedSum_nonneg weight
      (fun rule : Rule =>
        AppliedModelingLib.pmfExp law (gap rule))
      hweight
      (fun rule => by
        dsimp [gap]
        rw [kApprovalScoreGap_pmfExp_eq_upProb_sub_downProb]
        linarith [hle rule])

/--
The mixed up/down K-approval pair probabilities are still a valid pairwise
one-voter error law.
-/
theorem randomizedKApproval_mixedPairProb_sum_le_one
    {n : ℕ} {Rule : Type*} [Fintype Rule]
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hi lo : AppliedModelingLib.SocialChoice.Ranking.Candidate n) :
    (∑ rule : Rule,
        weight rule *
          AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
            law (K rule) hi lo) +
      (∑ rule : Rule,
        weight rule *
          AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
            law (K rule) hi lo) ≤
        1 := by
  exact AppliedModelingLib.weightedPairProb_sum_le_one
    weight
    (fun rule : Rule =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb law (K rule) hi lo)
    (fun rule : Rule =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb law (K rule) hi lo)
    hweight hsum
    (fun rule =>
      AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb_add_downProb_le_one
        law (K rule) hi lo)

/--
Mallows W-selection no-randomization bridge.  If the same pivotal boundary pair
determines the outcome-learning rate for every static K-approval rule and for
the randomized K-approval rule, then the pairwise K-approval no-randomization
comparison lifts to the outcome-learning rate.
-/
theorem mallowsWSelection_no_randomization_of_common_pivotal_pair
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (weight pUp pDown : Rule → ℝ)
    {mixedUp mixedDown randomizedOutcomeRate : ℝ}
    (staticOutcomeRate : Rule → ℝ)
    (hmixedUp : mixedUp = ∑ rule : Rule, weight rule * pUp rule)
    (hmixedDown : mixedDown = ∑ rule : Rule, weight rule * pDown rule)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hstatic_pivotal :
      ∀ rule,
        staticOutcomeRate rule =
          approvalPairwiseRate (pUp rule) (pDown rule))
    (hrandomized_pivotal :
      randomizedOutcomeRate = approvalPairwiseRate mixedUp mixedDown)
    (hconvex :
      approvalPairwiseRate mixedUp mixedDown ≤
        ∑ rule : Rule,
          weight rule * approvalPairwiseRate (pUp rule) (pDown rule)) :
    ∃ rule : Rule, randomizedOutcomeRate ≤ staticOutcomeRate rule := by
  rcases randomizedApproval_pairwiseRate_le_static_of_convexity
      weight pUp pDown hmixedUp hmixedDown hweight hsum hconvex with
    ⟨rule, hrule⟩
  refine ⟨rule, ?_⟩
  rw [hrandomized_pivotal, hstatic_pivotal rule]
  exact hrule

/--
Positive-base version of the Mallows W-selection bridge, using the proved
K-approval Jensen theorem instead of an external convexity certificate.
-/
theorem mallowsWSelection_no_randomization_of_common_pivotal_pair_positive
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (weight pUp pDown : Rule → ℝ)
    {mixedUp mixedDown randomizedOutcomeRate : ℝ}
    (staticOutcomeRate : Rule → ℝ)
    (hmixedUp : mixedUp = ∑ rule : Rule, weight rule * pUp rule)
    (hmixedDown : mixedDown = ∑ rule : Rule, weight rule * pDown rule)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hUp : ∀ rule, 0 ≤ pUp rule)
    (hDown : ∀ rule, 0 ≤ pDown rule)
    (hbase_pos :
      ∀ rule, 0 < approvalPairwiseBase (pUp rule) (pDown rule))
    (hmixed_base_pos : 0 < approvalPairwiseBase mixedUp mixedDown)
    (hstatic_pivotal :
      ∀ rule,
        staticOutcomeRate rule =
          approvalPairwiseRate (pUp rule) (pDown rule))
    (hrandomized_pivotal :
      randomizedOutcomeRate = approvalPairwiseRate mixedUp mixedDown) :
    ∃ rule : Rule, randomizedOutcomeRate ≤ staticOutcomeRate rule := by
  rcases randomizedApproval_pairwiseRate_le_static
      weight pUp pDown hmixedUp hmixedDown hweight hsum hUp hDown
      hbase_pos hmixed_base_pos with
    ⟨rule, hrule⟩
  refine ⟨rule, ?_⟩
  rw [hrandomized_pivotal, hstatic_pivotal rule]
  exact hrule

/--
Mixed-boundary version of the Mallows W-selection bridge.  The static
K-approval rules remain in the positive-base region; the randomized mixture
may hit the real-valued zero-base boundary.
-/
theorem mallowsWSelection_no_randomization_of_common_pivotal_pair_or_mixed_boundary
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (weight pUp pDown : Rule → ℝ)
    {mixedUp mixedDown randomizedOutcomeRate : ℝ}
    (staticOutcomeRate : Rule → ℝ)
    (hmixedUp : mixedUp = ∑ rule : Rule, weight rule * pUp rule)
    (hmixedDown : mixedDown = ∑ rule : Rule, weight rule * pDown rule)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hUp : ∀ rule, 0 ≤ pUp rule)
    (hDown : ∀ rule, 0 ≤ pDown rule)
    (hprob : ∀ rule, pUp rule + pDown rule ≤ 1)
    (hbase_pos :
      ∀ rule, 0 < approvalPairwiseBase (pUp rule) (pDown rule))
    (hstatic_pivotal :
      ∀ rule,
        staticOutcomeRate rule =
          approvalPairwiseRate (pUp rule) (pDown rule))
    (hrandomized_pivotal :
      randomizedOutcomeRate = approvalPairwiseRate mixedUp mixedDown) :
    ∃ rule : Rule, randomizedOutcomeRate ≤ staticOutcomeRate rule := by
  rcases randomizedApproval_pairwiseRate_le_static_or_mixed_boundary
      weight pUp pDown hmixedUp hmixedDown hweight hsum hUp hDown
      hprob hbase_pos with
    ⟨rule, hrule⟩
  refine ⟨rule, ?_⟩
  rw [hrandomized_pivotal, hstatic_pivotal rule]
  exact hrule

/--
Valid-probability outcome bridge for the common-pivotal setting.  Either some
static K-approval rule weakly beats the randomized outcome rate, or a static
boundary pair is degenerate in the real-valued approval-rate formula.
-/
theorem mallowsWSelection_no_randomization_of_common_pivotal_pair_valid_probabilities_or_static_boundary
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (weight pUp pDown : Rule → ℝ)
    {mixedUp mixedDown randomizedOutcomeRate : ℝ}
    (staticOutcomeRate : Rule → ℝ)
    (hmixedUp : mixedUp = ∑ rule : Rule, weight rule * pUp rule)
    (hmixedDown : mixedDown = ∑ rule : Rule, weight rule * pDown rule)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hUp : ∀ rule, 0 ≤ pUp rule)
    (hDown : ∀ rule, 0 ≤ pDown rule)
    (hprob : ∀ rule, pUp rule + pDown rule ≤ 1)
    (hstatic_pivotal :
      ∀ rule,
        staticOutcomeRate rule =
          approvalPairwiseRate (pUp rule) (pDown rule))
    (hrandomized_pivotal :
      randomizedOutcomeRate = approvalPairwiseRate mixedUp mixedDown) :
    (∃ rule : Rule, randomizedOutcomeRate ≤ staticOutcomeRate rule) ∨
      (∃ rule : Rule,
        approvalPairwiseBase (pUp rule) (pDown rule) = 0) := by
  rcases
      randomizedApproval_pairwiseRate_le_static_of_valid_probabilities_or_static_boundary
        weight pUp pDown hmixedUp hmixedDown hweight hsum
        hUp hDown hprob with
    hstatic | hboundary
  · left
    rcases hstatic with ⟨rule, hrule⟩
    refine ⟨rule, ?_⟩
    rw [hrandomized_pivotal, hstatic_pivotal rule]
    exact hrule
  · right
    exact hboundary

/--
Finite outcome-rate form of the Mallows W-selection no-randomization bridge.
If the same concrete pivotal pair realizes the finite outcome-learning rate
for every static K-approval rule and for the randomized rule, the pairwise
K-approval no-randomization theorem lifts directly to the finite outcome rate.
-/
theorem kApprovalOutcome_no_randomization_of_common_pivotal_pair_positive
    {Rule Pair : Type*} [Fintype Rule] [Nonempty Rule]
    [Fintype Pair] [Nonempty Pair]
    (weight pUp pDown : Rule → ℝ)
    (staticPairRate : Rule → Pair → ℝ)
    (randomizedPairRate : Pair → ℝ)
    (pivotal : Pair)
    {mixedUp mixedDown : ℝ}
    (hmixedUp : mixedUp = ∑ rule : Rule, weight rule * pUp rule)
    (hmixedDown : mixedDown = ∑ rule : Rule, weight rule * pDown rule)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hUp : ∀ rule, 0 ≤ pUp rule)
    (hDown : ∀ rule, 0 ≤ pDown rule)
    (hbase_pos :
      ∀ rule, 0 < approvalPairwiseBase (pUp rule) (pDown rule))
    (hmixed_base_pos : 0 < approvalPairwiseBase mixedUp mixedDown)
    (hstatic_pivotal :
      ∀ rule,
        finiteOutcomeLearningRate (staticPairRate rule) =
          staticPairRate rule pivotal)
    (hstatic_boundary :
      ∀ rule,
        staticPairRate rule pivotal =
          approvalPairwiseRate (pUp rule) (pDown rule))
    (hrandomized_pivotal :
      finiteOutcomeLearningRate randomizedPairRate =
        randomizedPairRate pivotal)
    (hrandomized_boundary :
      randomizedPairRate pivotal =
        approvalPairwiseRate mixedUp mixedDown) :
    ∃ rule : Rule,
      finiteOutcomeLearningRate randomizedPairRate ≤
        finiteOutcomeLearningRate (staticPairRate rule) := by
  exact
    mallowsWSelection_no_randomization_of_common_pivotal_pair_positive
      weight pUp pDown
      (fun rule : Rule => finiteOutcomeLearningRate (staticPairRate rule))
      hmixedUp hmixedDown hweight hsum hUp hDown hbase_pos
      hmixed_base_pos
      (fun rule => by
        change finiteOutcomeLearningRate (staticPairRate rule) =
          approvalPairwiseRate (pUp rule) (pDown rule)
        rw [hstatic_pivotal rule, hstatic_boundary rule])
      (by
        rw [hrandomized_pivotal, hrandomized_boundary])

/--
Finite outcome-rate common-pivotal bridge with a mixed-rule boundary branch.
The randomized mixture may have zero real-valued boundary base.
-/
theorem kApprovalOutcome_no_randomization_of_common_pivotal_pair_or_mixed_boundary
    {Rule Pair : Type*} [Fintype Rule] [Nonempty Rule]
    [Fintype Pair] [Nonempty Pair]
    (weight pUp pDown : Rule → ℝ)
    (staticPairRate : Rule → Pair → ℝ)
    (randomizedPairRate : Pair → ℝ)
    (pivotal : Pair)
    {mixedUp mixedDown : ℝ}
    (hmixedUp : mixedUp = ∑ rule : Rule, weight rule * pUp rule)
    (hmixedDown : mixedDown = ∑ rule : Rule, weight rule * pDown rule)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hUp : ∀ rule, 0 ≤ pUp rule)
    (hDown : ∀ rule, 0 ≤ pDown rule)
    (hprob : ∀ rule, pUp rule + pDown rule ≤ 1)
    (hbase_pos :
      ∀ rule, 0 < approvalPairwiseBase (pUp rule) (pDown rule))
    (hstatic_pivotal :
      ∀ rule,
        finiteOutcomeLearningRate (staticPairRate rule) =
          staticPairRate rule pivotal)
    (hstatic_boundary :
      ∀ rule,
        staticPairRate rule pivotal =
          approvalPairwiseRate (pUp rule) (pDown rule))
    (hrandomized_pivotal :
      finiteOutcomeLearningRate randomizedPairRate =
        randomizedPairRate pivotal)
    (hrandomized_boundary :
      randomizedPairRate pivotal =
        approvalPairwiseRate mixedUp mixedDown) :
    ∃ rule : Rule,
      finiteOutcomeLearningRate randomizedPairRate ≤
        finiteOutcomeLearningRate (staticPairRate rule) := by
  exact
    mallowsWSelection_no_randomization_of_common_pivotal_pair_or_mixed_boundary
      weight pUp pDown
      (fun rule : Rule => finiteOutcomeLearningRate (staticPairRate rule))
      hmixedUp hmixedDown hweight hsum hUp hDown hprob hbase_pos
      (fun rule => by
        change finiteOutcomeLearningRate (staticPairRate rule) =
          approvalPairwiseRate (pUp rule) (pDown rule)
        rw [hstatic_pivotal rule, hstatic_boundary rule])
      (by
        rw [hrandomized_pivotal, hrandomized_boundary])

/--
Valid-probability common-pivotal outcome bridge.  Either a static rule weakly
beats the randomized finite outcome rate, or a static boundary pair is
degenerate in the real-valued approval-rate formula.
-/
theorem kApprovalOutcome_no_randomization_of_common_pivotal_pair_valid_probabilities_or_static_boundary
    {Rule Pair : Type*} [Fintype Rule] [Nonempty Rule]
    [Fintype Pair] [Nonempty Pair]
    (weight pUp pDown : Rule → ℝ)
    (staticPairRate : Rule → Pair → ℝ)
    (randomizedPairRate : Pair → ℝ)
    (pivotal : Pair)
    {mixedUp mixedDown : ℝ}
    (hmixedUp : mixedUp = ∑ rule : Rule, weight rule * pUp rule)
    (hmixedDown : mixedDown = ∑ rule : Rule, weight rule * pDown rule)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hUp : ∀ rule, 0 ≤ pUp rule)
    (hDown : ∀ rule, 0 ≤ pDown rule)
    (hprob : ∀ rule, pUp rule + pDown rule ≤ 1)
    (hstatic_pivotal :
      ∀ rule,
        finiteOutcomeLearningRate (staticPairRate rule) =
          staticPairRate rule pivotal)
    (hstatic_boundary :
      ∀ rule,
        staticPairRate rule pivotal =
          approvalPairwiseRate (pUp rule) (pDown rule))
    (hrandomized_pivotal :
      finiteOutcomeLearningRate randomizedPairRate =
        randomizedPairRate pivotal)
    (hrandomized_boundary :
      randomizedPairRate pivotal =
        approvalPairwiseRate mixedUp mixedDown) :
    (∃ rule : Rule,
      finiteOutcomeLearningRate randomizedPairRate ≤
        finiteOutcomeLearningRate (staticPairRate rule)) ∨
      (∃ rule : Rule,
        approvalPairwiseBase (pUp rule) (pDown rule) = 0) := by
  exact
    mallowsWSelection_no_randomization_of_common_pivotal_pair_valid_probabilities_or_static_boundary
      weight pUp pDown
      (fun rule : Rule => finiteOutcomeLearningRate (staticPairRate rule))
      hmixedUp hmixedDown hweight hsum hUp hDown hprob
      (fun rule => by
        change finiteOutcomeLearningRate (staticPairRate rule) =
          approvalPairwiseRate (pUp rule) (pDown rule)
        rw [hstatic_pivotal rule, hstatic_boundary rule])
      (by
        rw [hrandomized_pivotal, hrandomized_boundary])

/--
Finite outcome-rate K-approval no-randomization bridge with only static
pivotality.  The randomized rule need not have the same pivotal pair: the
finite outcome rate is always bounded above by the randomized boundary-pair
rate, so static boundary pivotality is enough to lift the pairwise
K-approval no-randomization theorem to the outcome rate.
-/
theorem kApprovalOutcome_no_randomization_of_static_pivotal_pair_positive
    {Rule Pair : Type*} [Fintype Rule] [Nonempty Rule]
    [Fintype Pair] [Nonempty Pair]
    (weight pUp pDown : Rule → ℝ)
    (staticPairRate : Rule → Pair → ℝ)
    (randomizedPairRate : Pair → ℝ)
    (pivotal : Pair)
    {mixedUp mixedDown : ℝ}
    (hmixedUp : mixedUp = ∑ rule : Rule, weight rule * pUp rule)
    (hmixedDown : mixedDown = ∑ rule : Rule, weight rule * pDown rule)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hUp : ∀ rule, 0 ≤ pUp rule)
    (hDown : ∀ rule, 0 ≤ pDown rule)
    (hbase_pos :
      ∀ rule, 0 < approvalPairwiseBase (pUp rule) (pDown rule))
    (hmixed_base_pos : 0 < approvalPairwiseBase mixedUp mixedDown)
    (hstatic_pivotal :
      ∀ rule,
        finiteOutcomeLearningRate (staticPairRate rule) =
          staticPairRate rule pivotal)
    (hstatic_boundary :
      ∀ rule,
        staticPairRate rule pivotal =
          approvalPairwiseRate (pUp rule) (pDown rule))
    (hrandomized_boundary :
      randomizedPairRate pivotal =
        approvalPairwiseRate mixedUp mixedDown) :
    ∃ rule : Rule,
      finiteOutcomeLearningRate randomizedPairRate ≤
        finiteOutcomeLearningRate (staticPairRate rule) := by
  rcases randomizedApproval_pairwiseRate_le_static
      weight pUp pDown hmixedUp hmixedDown hweight hsum hUp hDown
      hbase_pos hmixed_base_pos with
    ⟨rule, hrule⟩
  refine ⟨rule, ?_⟩
  calc
    finiteOutcomeLearningRate randomizedPairRate ≤ randomizedPairRate pivotal :=
      finiteOutcomeLearningRate_le randomizedPairRate pivotal
    _ = approvalPairwiseRate mixedUp mixedDown := hrandomized_boundary
    _ ≤ approvalPairwiseRate (pUp rule) (pDown rule) := hrule
    _ = staticPairRate rule pivotal := (hstatic_boundary rule).symm
    _ = finiteOutcomeLearningRate (staticPairRate rule) :=
      (hstatic_pivotal rule).symm

/--
Finite outcome-rate static-pivotal bridge with a mixed-rule boundary branch.
The randomized rule need not have the same pivotal pair, and its boundary
pair may have zero real-valued base.
-/
theorem kApprovalOutcome_no_randomization_of_static_pivotal_pair_or_mixed_boundary
    {Rule Pair : Type*} [Fintype Rule] [Nonempty Rule]
    [Fintype Pair] [Nonempty Pair]
    (weight pUp pDown : Rule → ℝ)
    (staticPairRate : Rule → Pair → ℝ)
    (randomizedPairRate : Pair → ℝ)
    (pivotal : Pair)
    {mixedUp mixedDown : ℝ}
    (hmixedUp : mixedUp = ∑ rule : Rule, weight rule * pUp rule)
    (hmixedDown : mixedDown = ∑ rule : Rule, weight rule * pDown rule)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hUp : ∀ rule, 0 ≤ pUp rule)
    (hDown : ∀ rule, 0 ≤ pDown rule)
    (hprob : ∀ rule, pUp rule + pDown rule ≤ 1)
    (hbase_pos :
      ∀ rule, 0 < approvalPairwiseBase (pUp rule) (pDown rule))
    (hstatic_pivotal :
      ∀ rule,
        finiteOutcomeLearningRate (staticPairRate rule) =
          staticPairRate rule pivotal)
    (hstatic_boundary :
      ∀ rule,
        staticPairRate rule pivotal =
          approvalPairwiseRate (pUp rule) (pDown rule))
    (hrandomized_boundary :
      randomizedPairRate pivotal =
        approvalPairwiseRate mixedUp mixedDown) :
    ∃ rule : Rule,
      finiteOutcomeLearningRate randomizedPairRate ≤
        finiteOutcomeLearningRate (staticPairRate rule) := by
  rcases randomizedApproval_pairwiseRate_le_static_or_mixed_boundary
      weight pUp pDown hmixedUp hmixedDown hweight hsum hUp hDown
      hprob hbase_pos with
    ⟨rule, hrule⟩
  refine ⟨rule, ?_⟩
  calc
    finiteOutcomeLearningRate randomizedPairRate ≤ randomizedPairRate pivotal :=
      finiteOutcomeLearningRate_le randomizedPairRate pivotal
    _ = approvalPairwiseRate mixedUp mixedDown := hrandomized_boundary
    _ ≤ approvalPairwiseRate (pUp rule) (pDown rule) := hrule
    _ = staticPairRate rule pivotal := (hstatic_boundary rule).symm
    _ = finiteOutcomeLearningRate (staticPairRate rule) :=
      (hstatic_pivotal rule).symm

/--
Valid-probability static-pivotal outcome bridge.  The randomized rule need not
share the static pivotal pair.  Either a static rule weakly beats the
randomized finite outcome rate, or a static boundary pair is degenerate in the
real-valued approval-rate formula.
-/
theorem kApprovalOutcome_no_randomization_of_static_pivotal_pair_valid_probabilities_or_static_boundary
    {Rule Pair : Type*} [Fintype Rule] [Nonempty Rule]
    [Fintype Pair] [Nonempty Pair]
    (weight pUp pDown : Rule → ℝ)
    (staticPairRate : Rule → Pair → ℝ)
    (randomizedPairRate : Pair → ℝ)
    (pivotal : Pair)
    {mixedUp mixedDown : ℝ}
    (hmixedUp : mixedUp = ∑ rule : Rule, weight rule * pUp rule)
    (hmixedDown : mixedDown = ∑ rule : Rule, weight rule * pDown rule)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hUp : ∀ rule, 0 ≤ pUp rule)
    (hDown : ∀ rule, 0 ≤ pDown rule)
    (hprob : ∀ rule, pUp rule + pDown rule ≤ 1)
    (hstatic_pivotal :
      ∀ rule,
        finiteOutcomeLearningRate (staticPairRate rule) =
          staticPairRate rule pivotal)
    (hstatic_boundary :
      ∀ rule,
        staticPairRate rule pivotal =
          approvalPairwiseRate (pUp rule) (pDown rule))
    (hrandomized_boundary :
      randomizedPairRate pivotal =
        approvalPairwiseRate mixedUp mixedDown) :
    (∃ rule : Rule,
      finiteOutcomeLearningRate randomizedPairRate ≤
        finiteOutcomeLearningRate (staticPairRate rule)) ∨
      (∃ rule : Rule,
        approvalPairwiseBase (pUp rule) (pDown rule) = 0) := by
  rcases
      randomizedApproval_pairwiseRate_le_static_of_valid_probabilities_or_static_boundary
        weight pUp pDown hmixedUp hmixedDown hweight hsum
        hUp hDown hprob with
    hstatic | hboundary
  · left
    rcases hstatic with ⟨rule, hrule⟩
    refine ⟨rule, ?_⟩
    calc
      finiteOutcomeLearningRate randomizedPairRate ≤
          randomizedPairRate pivotal :=
        finiteOutcomeLearningRate_le randomizedPairRate pivotal
      _ = approvalPairwiseRate mixedUp mixedDown := hrandomized_boundary
      _ ≤ approvalPairwiseRate (pUp rule) (pDown rule) := hrule
      _ = staticPairRate rule pivotal := (hstatic_boundary rule).symm
      _ = finiteOutcomeLearningRate (staticPairRate rule) :=
        (hstatic_pivotal rule).symm
  · right
    exact hboundary

/--
Actual ranking-law K-approval outcome-rate lift with a static pivotal pair.
The static component rates use the paper's K-approval up/down probabilities
for each relevant pair, while the randomized rate uses their weighted mixture.
If the supplied pivotal pair realizes every static component's finite outcome
rate and its static approval bases are positive, some static K-approval
component weakly beats the randomized finite outcome rate.
-/
theorem randomizedKApproval_outcomeRate_le_static_from_static_pivotal_pair_or_mixed_boundary
    {n : ℕ} {Rule Pair : Type*}
    [Fintype Rule] [Nonempty Rule] [Fintype Pair] [Nonempty Pair]
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hi lo : Pair → AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (pivotal : Pair)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hbase_pos :
      ∀ rule,
        0 <
          approvalPairwiseBase
            (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
              law (K rule) (hi pivotal) (lo pivotal))
            (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
              law (K rule) (hi pivotal) (lo pivotal)))
    (hstatic_pivotal :
      ∀ rule,
        finiteOutcomeLearningRate
          (fun pair : Pair =>
            approvalPairwiseRate
              (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
                law (K rule) (hi pair) (lo pair))
              (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
                law (K rule) (hi pair) (lo pair))) =
          approvalPairwiseRate
            (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
              law (K rule) (hi pivotal) (lo pivotal))
            (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
              law (K rule) (hi pivotal) (lo pivotal))) :
    ∃ rule : Rule,
      finiteOutcomeLearningRate
          (fun pair : Pair =>
            approvalPairwiseRate
              (∑ rule : Rule,
                weight rule *
                  AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
                    law (K rule) (hi pair) (lo pair))
              (∑ rule : Rule,
                weight rule *
                  AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
                    law (K rule) (hi pair) (lo pair))) ≤
        finiteOutcomeLearningRate
          (fun pair : Pair =>
            approvalPairwiseRate
              (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
                law (K rule) (hi pair) (lo pair))
              (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
                law (K rule) (hi pair) (lo pair))) := by
  exact
    kApprovalOutcome_no_randomization_of_static_pivotal_pair_or_mixed_boundary
      weight
      (fun rule : Rule =>
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
          law (K rule) (hi pivotal) (lo pivotal))
      (fun rule : Rule =>
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
          law (K rule) (hi pivotal) (lo pivotal))
      (fun rule : Rule => fun pair : Pair =>
        approvalPairwiseRate
          (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
            law (K rule) (hi pair) (lo pair))
          (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
            law (K rule) (hi pair) (lo pair)))
      (fun pair : Pair =>
        approvalPairwiseRate
          (∑ rule : Rule,
            weight rule *
              AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
                law (K rule) (hi pair) (lo pair))
          (∑ rule : Rule,
            weight rule *
              AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
                law (K rule) (hi pair) (lo pair)))
      pivotal rfl rfl hweight hsum
      (fun rule =>
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb_nonneg
          law (K rule) (hi pivotal) (lo pivotal))
      (fun rule =>
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb_nonneg
          law (K rule) (hi pivotal) (lo pivotal))
      (fun rule =>
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb_add_downProb_le_one
          law (K rule) (hi pivotal) (lo pivotal))
      hbase_pos hstatic_pivotal
      (fun rule => rfl) rfl

/--
Actual ranking-law K-approval outcome-rate lift over valid K-approval
probabilities.  Either a static component weakly beats the randomized finite
outcome rate, or the supplied static pivotal pair is a degenerate
zero-base boundary for some component in the real-valued approval-rate
formula.
-/
theorem randomizedKApproval_outcomeRate_le_static_from_static_pivotal_pair_valid_probabilities_or_static_boundary
    {n : ℕ} {Rule Pair : Type*}
    [Fintype Rule] [Nonempty Rule] [Fintype Pair] [Nonempty Pair]
    (law : PMF (AppliedModelingLib.SocialChoice.Ranking.Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hi lo : Pair → AppliedModelingLib.SocialChoice.Ranking.Candidate n)
    (pivotal : Pair)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hstatic_pivotal :
      ∀ rule,
        finiteOutcomeLearningRate
          (fun pair : Pair =>
            approvalPairwiseRate
              (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
                law (K rule) (hi pair) (lo pair))
              (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
                law (K rule) (hi pair) (lo pair))) =
          approvalPairwiseRate
            (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
              law (K rule) (hi pivotal) (lo pivotal))
            (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
              law (K rule) (hi pivotal) (lo pivotal))) :
    (∃ rule : Rule,
      finiteOutcomeLearningRate
          (fun pair : Pair =>
            approvalPairwiseRate
              (∑ rule : Rule,
                weight rule *
                  AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
                    law (K rule) (hi pair) (lo pair))
              (∑ rule : Rule,
                weight rule *
                  AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
                    law (K rule) (hi pair) (lo pair))) ≤
        finiteOutcomeLearningRate
          (fun pair : Pair =>
            approvalPairwiseRate
              (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
                law (K rule) (hi pair) (lo pair))
              (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
                law (K rule) (hi pair) (lo pair)))) ∨
      (∃ rule : Rule,
        approvalPairwiseBase
          (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
            law (K rule) (hi pivotal) (lo pivotal))
          (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
            law (K rule) (hi pivotal) (lo pivotal)) = 0) := by
  exact
    kApprovalOutcome_no_randomization_of_static_pivotal_pair_valid_probabilities_or_static_boundary
      weight
      (fun rule : Rule =>
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
          law (K rule) (hi pivotal) (lo pivotal))
      (fun rule : Rule =>
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
          law (K rule) (hi pivotal) (lo pivotal))
      (fun rule : Rule => fun pair : Pair =>
        approvalPairwiseRate
          (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
            law (K rule) (hi pair) (lo pair))
          (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
            law (K rule) (hi pair) (lo pair)))
      (fun pair : Pair =>
        approvalPairwiseRate
          (∑ rule : Rule,
            weight rule *
              AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
                law (K rule) (hi pair) (lo pair))
          (∑ rule : Rule,
            weight rule *
              AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
                law (K rule) (hi pair) (lo pair)))
      pivotal rfl rfl hweight hsum
      (fun rule =>
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb_nonneg
          law (K rule) (hi pivotal) (lo pivotal))
      (fun rule =>
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb_nonneg
          law (K rule) (hi pivotal) (lo pivotal))
      (fun rule =>
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb_add_downProb_le_one
          law (K rule) (hi pivotal) (lo pivotal))
      hstatic_pivotal (fun rule => rfl) rfl

/--
Finite min-rate certificate for the paper's "randomization can help W-selection"
examples.  If two static rules have the same finite outcome-learning rate and
the randomized rule beats that base rate on every pivotal pair, then the
randomized rule strictly improves on both static rules.
-/
theorem randomizedOutcomeRate_strictly_improves_two_static_minima
    {Pair : Type*} [Fintype Pair] [Nonempty Pair]
    (staticA staticB randomized : Pair → ℝ) {baseRate : ℝ}
    (hA : finiteOutcomeLearningRate staticA = baseRate)
    (hB : finiteOutcomeLearningRate staticB = baseRate)
    (hrandomized : ∀ pair, baseRate < randomized pair) :
    max (finiteOutcomeLearningRate staticA) (finiteOutcomeLearningRate staticB) <
      finiteOutcomeLearningRate randomized := by
  have hbase_randomized : baseRate < finiteOutcomeLearningRate randomized := by
    unfold finiteOutcomeLearningRate
    rw [Finset.lt_inf'_iff]
    intro pair _
    exact hrandomized pair
  simpa [hA, hB] using hbase_randomized

/--
More general finite min-rate certificate for empirical examples: if the
randomized rule's finite outcome-learning rate strictly dominates two static
rules separately, then it strictly dominates their better static rate.
-/
theorem randomizedOutcomeRate_strictly_improves_two_static_of_bounds
    {Pair : Type*} [Fintype Pair] [Nonempty Pair]
    (staticA staticB randomized : Pair → ℝ)
    (hA :
      finiteOutcomeLearningRate staticA <
        finiteOutcomeLearningRate randomized)
    (hB :
      finiteOutcomeLearningRate staticB <
        finiteOutcomeLearningRate randomized) :
    max (finiteOutcomeLearningRate staticA) (finiteOutcomeLearningRate staticB) <
      finiteOutcomeLearningRate randomized :=
  max_lt hA hB

/--
Finite max-rate certificate for the source's `max_K r(K)` conclusion: if every
static rule's finite outcome-learning rate is at most a common base rate, and
the randomized rule beats that base rate on every pivotal pair, then the
randomized rule strictly beats the best static rule in the finite family.
-/
theorem randomizedOutcomeRate_strictly_improves_all_static_of_bound
    {Rule Pair : Type*} [Fintype Rule] [Nonempty Rule]
    [Fintype Pair] [Nonempty Pair]
    (static : Rule → Pair → ℝ) (randomized : Pair → ℝ) {baseRate : ℝ}
    (hstatic :
      ∀ rule, finiteOutcomeLearningRate (static rule) ≤ baseRate)
    (hrandomized : ∀ pair, baseRate < randomized pair) :
    (Finset.univ : Finset Rule).sup' finiteUnivNonempty
        (fun rule => finiteOutcomeLearningRate (static rule)) <
      finiteOutcomeLearningRate randomized := by
  have hbase_randomized : baseRate < finiteOutcomeLearningRate randomized := by
    unfold finiteOutcomeLearningRate
    rw [Finset.lt_inf'_iff]
    intro pair _
    exact hrandomized pair
  have hsup_le :
      (Finset.univ : Finset Rule).sup' finiteUnivNonempty
          (fun rule => finiteOutcomeLearningRate (static rule)) ≤
        baseRate := by
    exact Finset.sup'_le finiteUnivNonempty _ (by
      intro rule _
      exact hstatic rule)
  exact lt_of_le_of_lt hsup_le hbase_randomized

/--
Approval-rate specialization of the W-selection improvement certificate.
Concrete examples need only supply the two static finite minima and the strict
approval-rate inequalities for the randomized rule's pivotal pairs.
-/
theorem randomizedApproval_outcomeRate_strictly_improves_two_static_minima
    {Pair : Type*} [Fintype Pair] [Nonempty Pair]
    (staticAUp staticADown staticBUp staticBDown
      randomizedUp randomizedDown : Pair → ℝ)
    {baseRate : ℝ}
    (hA :
      finiteOutcomeLearningRate
          (fun pair => approvalPairwiseRate (staticAUp pair) (staticADown pair)) =
        baseRate)
    (hB :
      finiteOutcomeLearningRate
          (fun pair => approvalPairwiseRate (staticBUp pair) (staticBDown pair)) =
        baseRate)
    (hrandomized :
      ∀ pair,
        baseRate <
          approvalPairwiseRate (randomizedUp pair) (randomizedDown pair)) :
    max
        (finiteOutcomeLearningRate
          (fun pair => approvalPairwiseRate (staticAUp pair) (staticADown pair)))
        (finiteOutcomeLearningRate
          (fun pair => approvalPairwiseRate (staticBUp pair) (staticBDown pair))) <
      finiteOutcomeLearningRate
        (fun pair =>
          approvalPairwiseRate (randomizedUp pair) (randomizedDown pair)) := by
  exact randomizedOutcomeRate_strictly_improves_two_static_minima
    (fun pair => approvalPairwiseRate (staticAUp pair) (staticADown pair))
    (fun pair => approvalPairwiseRate (staticBUp pair) (staticBDown pair))
    (fun pair => approvalPairwiseRate (randomizedUp pair) (randomizedDown pair))
    hA hB hrandomized

/--
Approval-rate specialization of the finite `max_K` certificate.  A source
construction can use this once it has shown every static approval cutoff has
finite outcome rate at most `baseRate`, and the randomized approval rule beats
`baseRate` on every pivotal pair.
-/
theorem randomizedApproval_outcomeRate_strictly_improves_all_static_of_bound
    {Rule Pair : Type*} [Fintype Rule] [Nonempty Rule]
    [Fintype Pair] [Nonempty Pair]
    (staticUp staticDown : Rule → Pair → ℝ)
    (randomizedUp randomizedDown : Pair → ℝ) {baseRate : ℝ}
    (hstatic :
      ∀ rule,
        finiteOutcomeLearningRate
            (fun pair =>
              approvalPairwiseRate (staticUp rule pair) (staticDown rule pair)) ≤
          baseRate)
    (hrandomized :
      ∀ pair,
        baseRate <
          approvalPairwiseRate (randomizedUp pair) (randomizedDown pair)) :
    (Finset.univ : Finset Rule).sup' finiteUnivNonempty
        (fun rule =>
          finiteOutcomeLearningRate
            (fun pair =>
              approvalPairwiseRate (staticUp rule pair) (staticDown rule pair))) <
      finiteOutcomeLearningRate
        (fun pair =>
          approvalPairwiseRate (randomizedUp pair) (randomizedDown pair)) :=
  randomizedOutcomeRate_strictly_improves_all_static_of_bound
    (fun rule pair =>
      approvalPairwiseRate (staticUp rule pair) (staticDown rule pair))
    (fun pair => approvalPairwiseRate (randomizedUp pair) (randomizedDown pair))
    hstatic hrandomized

/-! ## Durham Ward 1 randomized approval example -/

/-- The two pivotal pairs reported in the Durham Ward 1 example. -/
inductive DurhamWard1Pair where
  | hj
  | ij
  deriving DecidableEq, Fintype

namespace DurhamWard1Pair

instance : Nonempty DurhamWard1Pair := ⟨hj⟩

end DurhamWard1Pair

open DurhamWard1Pair

/-- Source decimal probabilities, represented exactly as thousandths. -/
def durhamWard1Prob (n : ℕ) : ℝ := (n : ℝ) / 1000

def durhamWard1K3Up : DurhamWard1Pair → ℝ
  | hj => durhamWard1Prob 277
  | ij => durhamWard1Prob 255

def durhamWard1K3Down : DurhamWard1Pair → ℝ
  | hj => durhamWard1Prob 200
  | ij => durhamWard1Prob 160

def durhamWard1K4Up : DurhamWard1Pair → ℝ
  | hj => durhamWard1Prob 266
  | ij => durhamWard1Prob 295

def durhamWard1K4Down : DurhamWard1Pair → ℝ
  | hj => durhamWard1Prob 188
  | ij => durhamWard1Prob 217

def durhamWard1RandomizedUp : DurhamWard1Pair → ℝ
  | hj => durhamWard1Prob 271
  | ij => durhamWard1Prob 275

def durhamWard1RandomizedDown : DurhamWard1Pair → ℝ
  | hj => durhamWard1Prob 194
  | ij => durhamWard1Prob 189

def durhamWard1K3Rate (pair : DurhamWard1Pair) : ℝ :=
  approvalPairwiseRate (durhamWard1K3Up pair) (durhamWard1K3Down pair)

def durhamWard1K4Rate (pair : DurhamWard1Pair) : ℝ :=
  approvalPairwiseRate (durhamWard1K4Up pair) (durhamWard1K4Down pair)

def durhamWard1RandomizedRate (pair : DurhamWard1Pair) : ℝ :=
  approvalPairwiseRate
    (durhamWard1RandomizedUp pair) (durhamWard1RandomizedDown pair)

private theorem durhamWard1_base_pos_277_200 :
    0 < approvalPairwiseBase (durhamWard1Prob 277) (durhamWard1Prob 200) := by
  have hup : 0 < durhamWard1Prob 277 := by norm_num [durhamWard1Prob]
  have hdown : 0 < durhamWard1Prob 200 := by norm_num [durhamWard1Prob]
  have hsum : durhamWard1Prob 277 + durhamWard1Prob 200 ≤ 1 := by
    norm_num [durhamWard1Prob]
  simpa [approvalPairwiseBase] using
    ternaryGap_closedExpr_pos hup hdown hsum

private theorem durhamWard1_base_pos_255_160 :
    0 < approvalPairwiseBase (durhamWard1Prob 255) (durhamWard1Prob 160) := by
  have hup : 0 < durhamWard1Prob 255 := by norm_num [durhamWard1Prob]
  have hdown : 0 < durhamWard1Prob 160 := by norm_num [durhamWard1Prob]
  have hsum : durhamWard1Prob 255 + durhamWard1Prob 160 ≤ 1 := by
    norm_num [durhamWard1Prob]
  simpa [approvalPairwiseBase] using
    ternaryGap_closedExpr_pos hup hdown hsum

private theorem durhamWard1_base_pos_266_188 :
    0 < approvalPairwiseBase (durhamWard1Prob 266) (durhamWard1Prob 188) := by
  have hup : 0 < durhamWard1Prob 266 := by norm_num [durhamWard1Prob]
  have hdown : 0 < durhamWard1Prob 188 := by norm_num [durhamWard1Prob]
  have hsum : durhamWard1Prob 266 + durhamWard1Prob 188 ≤ 1 := by
    norm_num [durhamWard1Prob]
  simpa [approvalPairwiseBase] using
    ternaryGap_closedExpr_pos hup hdown hsum

private theorem durhamWard1_base_pos_295_217 :
    0 < approvalPairwiseBase (durhamWard1Prob 295) (durhamWard1Prob 217) := by
  have hup : 0 < durhamWard1Prob 295 := by norm_num [durhamWard1Prob]
  have hdown : 0 < durhamWard1Prob 217 := by norm_num [durhamWard1Prob]
  have hsum : durhamWard1Prob 295 + durhamWard1Prob 217 ≤ 1 := by
    norm_num [durhamWard1Prob]
  simpa [approvalPairwiseBase] using
    ternaryGap_closedExpr_pos hup hdown hsum

private theorem durhamWard1_base_pos_271_194 :
    0 < approvalPairwiseBase (durhamWard1Prob 271) (durhamWard1Prob 194) := by
  have hup : 0 < durhamWard1Prob 271 := by norm_num [durhamWard1Prob]
  have hdown : 0 < durhamWard1Prob 194 := by norm_num [durhamWard1Prob]
  have hsum : durhamWard1Prob 271 + durhamWard1Prob 194 ≤ 1 := by
    norm_num [durhamWard1Prob]
  simpa [approvalPairwiseBase] using
    ternaryGap_closedExpr_pos hup hdown hsum

private theorem durhamWard1_base_pos_275_189 :
    0 < approvalPairwiseBase (durhamWard1Prob 275) (durhamWard1Prob 189) := by
  have hup : 0 < durhamWard1Prob 275 := by norm_num [durhamWard1Prob]
  have hdown : 0 < durhamWard1Prob 189 := by norm_num [durhamWard1Prob]
  have hsum : durhamWard1Prob 275 + durhamWard1Prob 189 ≤ 1 := by
    norm_num [durhamWard1Prob]
  simpa [approvalPairwiseBase] using
    ternaryGap_closedExpr_pos hup hdown hsum

private theorem durhamWard1_base_255_160_lt_277_200 :
    approvalPairwiseBase (durhamWard1Prob 255) (durhamWard1Prob 160) <
      approvalPairwiseBase (durhamWard1Prob 277) (durhamWard1Prob 200) := by
  have hleft_sqrt :
      Real.sqrt ((durhamWard1Prob 255) * (durhamWard1Prob 160)) <
        (203 : ℝ) / 1000 := by
    exact (Real.sqrt_lt
      (by norm_num [durhamWard1Prob] :
        0 ≤ (durhamWard1Prob 255) * (durhamWard1Prob 160))
      (by norm_num : 0 ≤ (203 : ℝ) / 1000)).2
      (by norm_num [durhamWard1Prob])
  have hright_sqrt :
      (235 : ℝ) / 1000 <
        Real.sqrt ((durhamWard1Prob 277) * (durhamWard1Prob 200)) := by
    exact (Real.lt_sqrt (by norm_num : 0 ≤ (235 : ℝ) / 1000)).2
      (by norm_num [durhamWard1Prob])
  unfold approvalPairwiseBase durhamWard1Prob at *
  nlinarith

private theorem durhamWard1_base_266_188_lt_295_217 :
    approvalPairwiseBase (durhamWard1Prob 266) (durhamWard1Prob 188) <
      approvalPairwiseBase (durhamWard1Prob 295) (durhamWard1Prob 217) := by
  have hleft_sqrt :
      Real.sqrt ((durhamWard1Prob 266) * (durhamWard1Prob 188)) <
        (2237 : ℝ) / 10000 := by
    exact (Real.sqrt_lt
      (by norm_num [durhamWard1Prob] :
        0 ≤ (durhamWard1Prob 266) * (durhamWard1Prob 188))
      (by norm_num : 0 ≤ (2237 : ℝ) / 10000)).2
      (by norm_num [durhamWard1Prob])
  have hright_sqrt :
      (253 : ℝ) / 1000 <
        Real.sqrt ((durhamWard1Prob 295) * (durhamWard1Prob 217)) := by
    exact (Real.lt_sqrt (by norm_num : 0 ≤ (253 : ℝ) / 1000)).2
      (by norm_num [durhamWard1Prob])
  unfold approvalPairwiseBase durhamWard1Prob at *
  nlinarith

private theorem durhamWard1_base_271_194_lt_277_200 :
    approvalPairwiseBase (durhamWard1Prob 271) (durhamWard1Prob 194) <
      approvalPairwiseBase (durhamWard1Prob 277) (durhamWard1Prob 200) := by
  have hleft_sqrt :
      Real.sqrt ((durhamWard1Prob 271) * (durhamWard1Prob 194)) <
        (2293 : ℝ) / 10000 := by
    exact (Real.sqrt_lt
      (by norm_num [durhamWard1Prob] :
        0 ≤ (durhamWard1Prob 271) * (durhamWard1Prob 194))
      (by norm_num : 0 ≤ (2293 : ℝ) / 10000)).2
      (by norm_num [durhamWard1Prob])
  have hright_sqrt :
      (23537 : ℝ) / 100000 <
        Real.sqrt ((durhamWard1Prob 277) * (durhamWard1Prob 200)) := by
    exact (Real.lt_sqrt (by norm_num : 0 ≤ (23537 : ℝ) / 100000)).2
      (by norm_num [durhamWard1Prob])
  unfold approvalPairwiseBase durhamWard1Prob at *
  nlinarith

private theorem durhamWard1_base_275_189_lt_277_200 :
    approvalPairwiseBase (durhamWard1Prob 275) (durhamWard1Prob 189) <
      approvalPairwiseBase (durhamWard1Prob 277) (durhamWard1Prob 200) := by
  have hleft_sqrt :
      Real.sqrt ((durhamWard1Prob 275) * (durhamWard1Prob 189)) <
        (228 : ℝ) / 1000 := by
    exact (Real.sqrt_lt
      (by norm_num [durhamWard1Prob] :
        0 ≤ (durhamWard1Prob 275) * (durhamWard1Prob 189))
      (by norm_num : 0 ≤ (228 : ℝ) / 1000)).2
      (by norm_num [durhamWard1Prob])
  have hright_sqrt :
      (235 : ℝ) / 1000 <
        Real.sqrt ((durhamWard1Prob 277) * (durhamWard1Prob 200)) := by
    exact (Real.lt_sqrt (by norm_num : 0 ≤ (235 : ℝ) / 1000)).2
      (by norm_num [durhamWard1Prob])
  unfold approvalPairwiseBase durhamWard1Prob at *
  nlinarith

private theorem durhamWard1_base_271_194_lt_295_217 :
    approvalPairwiseBase (durhamWard1Prob 271) (durhamWard1Prob 194) <
      approvalPairwiseBase (durhamWard1Prob 295) (durhamWard1Prob 217) := by
  have hleft_sqrt :
      Real.sqrt ((durhamWard1Prob 271) * (durhamWard1Prob 194)) <
        (2293 : ℝ) / 10000 := by
    exact (Real.sqrt_lt
      (by norm_num [durhamWard1Prob] :
        0 ≤ (durhamWard1Prob 271) * (durhamWard1Prob 194))
      (by norm_num : 0 ≤ (2293 : ℝ) / 10000)).2
      (by norm_num [durhamWard1Prob])
  have hright_sqrt :
      (253 : ℝ) / 1000 <
        Real.sqrt ((durhamWard1Prob 295) * (durhamWard1Prob 217)) := by
    exact (Real.lt_sqrt (by norm_num : 0 ≤ (253 : ℝ) / 1000)).2
      (by norm_num [durhamWard1Prob])
  unfold approvalPairwiseBase durhamWard1Prob at *
  nlinarith

private theorem durhamWard1_base_275_189_lt_295_217 :
    approvalPairwiseBase (durhamWard1Prob 275) (durhamWard1Prob 189) <
      approvalPairwiseBase (durhamWard1Prob 295) (durhamWard1Prob 217) := by
  have hleft_sqrt :
      Real.sqrt ((durhamWard1Prob 275) * (durhamWard1Prob 189)) <
        (228 : ℝ) / 1000 := by
    exact (Real.sqrt_lt
      (by norm_num [durhamWard1Prob] :
        0 ≤ (durhamWard1Prob 275) * (durhamWard1Prob 189))
      (by norm_num : 0 ≤ (228 : ℝ) / 1000)).2
      (by norm_num [durhamWard1Prob])
  have hright_sqrt :
      (253 : ℝ) / 1000 <
        Real.sqrt ((durhamWard1Prob 295) * (durhamWard1Prob 217)) := by
    exact (Real.lt_sqrt (by norm_num : 0 ≤ (253 : ℝ) / 1000)).2
      (by norm_num [durhamWard1Prob])
  unfold approvalPairwiseBase durhamWard1Prob at *
  nlinarith

theorem durhamWard1K3_outcomeRate_eq_hj :
    finiteOutcomeLearningRate durhamWard1K3Rate =
      durhamWard1K3Rate hj := by
  have hrate : durhamWard1K3Rate hj ≤ durhamWard1K3Rate ij := by
    exact (approvalPairwiseRate_lt_of_base_gt
      durhamWard1_base_pos_277_200
      durhamWard1_base_pos_255_160
      durhamWard1_base_255_160_lt_277_200).le
  unfold finiteOutcomeLearningRate
  apply le_antisymm
  · exact Finset.inf'_le durhamWard1K3Rate
      (by simp : hj ∈ (Finset.univ : Finset DurhamWard1Pair))
  · exact Finset.le_inf' _ _ (by
      intro pair _
      cases pair with
      | hj => rfl
      | ij => exact hrate)

theorem durhamWard1K4_outcomeRate_eq_ij :
    finiteOutcomeLearningRate durhamWard1K4Rate =
      durhamWard1K4Rate ij := by
  have hrate : durhamWard1K4Rate ij ≤ durhamWard1K4Rate hj := by
    exact (approvalPairwiseRate_lt_of_base_gt
      durhamWard1_base_pos_295_217
      durhamWard1_base_pos_266_188
      durhamWard1_base_266_188_lt_295_217).le
  unfold finiteOutcomeLearningRate
  apply le_antisymm
  · exact Finset.inf'_le durhamWard1K4Rate
      (by simp : ij ∈ (Finset.univ : Finset DurhamWard1Pair))
  · exact Finset.le_inf' _ _ (by
      intro pair _
      cases pair with
      | hj => exact hrate
      | ij => rfl)

theorem durhamWard1RandomizedApproval_improves_static3_static4 :
    max
        (finiteOutcomeLearningRate durhamWard1K3Rate)
        (finiteOutcomeLearningRate durhamWard1K4Rate) <
      finiteOutcomeLearningRate durhamWard1RandomizedRate := by
  refine randomizedOutcomeRate_strictly_improves_two_static_of_bounds
    durhamWard1K3Rate durhamWard1K4Rate durhamWard1RandomizedRate ?_ ?_
  · rw [durhamWard1K3_outcomeRate_eq_hj]
    unfold finiteOutcomeLearningRate
    rw [Finset.lt_inf'_iff]
    intro pair _
    cases pair with
    | hj =>
        exact approvalPairwiseRate_lt_of_base_gt
          durhamWard1_base_pos_277_200
          durhamWard1_base_pos_271_194
          durhamWard1_base_271_194_lt_277_200
    | ij =>
        exact approvalPairwiseRate_lt_of_base_gt
          durhamWard1_base_pos_277_200
          durhamWard1_base_pos_275_189
          durhamWard1_base_275_189_lt_277_200
  · rw [durhamWard1K4_outcomeRate_eq_ij]
    unfold finiteOutcomeLearningRate
    rw [Finset.lt_inf'_iff]
    intro pair _
    cases pair with
    | hj =>
        exact approvalPairwiseRate_lt_of_base_gt
          durhamWard1_base_pos_295_217
          durhamWard1_base_pos_271_194
          durhamWard1_base_271_194_lt_295_217
    | ij =>
        exact approvalPairwiseRate_lt_of_base_gt
          durhamWard1_base_pos_295_217
          durhamWard1_base_pos_275_189
          durhamWard1_base_275_189_lt_295_217

/-! ## Constructed design-invariant W-selection randomized approval example -/

/--
Three-candidate constructed W-selection example.  The candidate `winner` is
asymptotically selected; `loserI` and `loserJ` are the two losing candidates
whose pivotal pair changes between the two static approval rules.
-/
inductive ConstructedWSelectionCandidate where
  | winner
  | loserI
  | loserJ
  deriving DecidableEq, Fintype

namespace ConstructedWSelectionCandidate

instance : Nonempty ConstructedWSelectionCandidate := ⟨winner⟩

end ConstructedWSelectionCandidate

open ConstructedWSelectionCandidate

/-- The two relevant winner-vs-loser pairs in the constructed example. -/
inductive ConstructedWSelectionPair where
  | hi
  | hj
  deriving DecidableEq, Fintype

namespace ConstructedWSelectionPair

instance : Nonempty ConstructedWSelectionPair := ⟨hi⟩

end ConstructedWSelectionPair

/-- Exact thousandth probabilities used in the constructed example. -/
def constructedWSelectionProb (n : ℕ) : ℝ := (n : ℝ) / 1000

/--
The six strict rankings in the source constructed W-selection example, named
by their candidate order.
-/
inductive ConstructedWSelectionRanking where
  | hij
  | hji
  | ihj
  | ijh
  | jhi
  | jih
  deriving DecidableEq, Fintype

namespace ConstructedWSelectionRanking

instance : Nonempty ConstructedWSelectionRanking := ⟨hij⟩

end ConstructedWSelectionRanking

open ConstructedWSelectionRanking

/-- Exact real atom weights over the six source rankings. -/
def constructedWSelectionRankingMassReal :
    ConstructedWSelectionRanking → ℝ
  | hij => (46 : ℝ) / 1000
  | hji => (656 : ℝ) / 1000
  | ihj => (227 : ℝ) / 1000
  | ijh => (7 : ℝ) / 1000
  | jhi => (44 : ℝ) / 1000
  | jih => (20 : ℝ) / 1000

/-- Exact atom weights over the six source rankings, as `ENNReal` masses. -/
def constructedWSelectionRankingMass
    (ranking : ConstructedWSelectionRanking) : ENNReal :=
  ENNReal.ofReal (constructedWSelectionRankingMassReal ranking)

/-- Exact law over the six source rankings. -/
noncomputable def constructedWSelectionRankingLaw :
    PMF ConstructedWSelectionRanking :=
  PMF.ofFintype
    constructedWSelectionRankingMass
    (by
      have hnonneg :
          ∀ ranking ∈ (Finset.univ : Finset ConstructedWSelectionRanking),
            0 ≤ constructedWSelectionRankingMassReal ranking := by
        intro ranking _
        cases ranking <;> norm_num [constructedWSelectionRankingMassReal]
      have hsum_real :
          (∑ ranking : ConstructedWSelectionRanking,
            constructedWSelectionRankingMassReal ranking) = 1 := by
        rw [show (Finset.univ : Finset ConstructedWSelectionRanking) =
            ({hij, hji, ihj, ijh, jhi, jih} :
              Finset ConstructedWSelectionRanking) by
          decide]
        simp [constructedWSelectionRankingMassReal]
        norm_num [constructedWSelectionRankingMassReal]
      calc
        ∑ ranking : ConstructedWSelectionRanking,
            constructedWSelectionRankingMass ranking =
            ENNReal.ofReal
              (∑ ranking : ConstructedWSelectionRanking,
                constructedWSelectionRankingMassReal ranking) := by
              symm
              exact ENNReal.ofReal_sum_of_nonneg
                (s := (Finset.univ : Finset ConstructedWSelectionRanking))
                (f := constructedWSelectionRankingMassReal)
                hnonneg
        _ = 1 := by
              rw [hsum_real]
              norm_num)

/-- Boolean candidate membership in the proper top prefixes of the source rankings. -/
def constructedWSelectionRankingInTopPrefixBool :
    ConstructedWSelectionRanking →
      ConstructedWSelectionCandidate → Fin 2 → Bool
  | hij, winner, _ => true
  | hij, loserI, 0 => false
  | hij, loserI, 1 => true
  | hij, loserJ, _ => false
  | hji, winner, _ => true
  | hji, loserI, _ => false
  | hji, loserJ, 0 => false
  | hji, loserJ, 1 => true
  | ihj, winner, 0 => false
  | ihj, winner, 1 => true
  | ihj, loserI, _ => true
  | ihj, loserJ, _ => false
  | ijh, winner, _ => false
  | ijh, loserI, _ => true
  | ijh, loserJ, 0 => false
  | ijh, loserJ, 1 => true
  | jhi, winner, 0 => false
  | jhi, winner, 1 => true
  | jhi, loserI, _ => false
  | jhi, loserJ, _ => true
  | jih, winner, _ => false
  | jih, loserI, 0 => false
  | jih, loserI, 1 => true
  | jih, loserJ, _ => true

/-- Candidate membership in the proper top prefixes of the six source rankings. -/
def constructedWSelectionRankingInTopPrefix
    (ranking : ConstructedWSelectionRanking)
    (candidate : ConstructedWSelectionCandidate) (cut : Fin 2) : Prop :=
  constructedWSelectionRankingInTopPrefixBool ranking candidate cut = true

instance constructedWSelectionRankingInTopPrefix_decidable :
    ∀ ranking candidate cut,
      Decidable
        (constructedWSelectionRankingInTopPrefix ranking candidate cut) := by
  intro ranking candidate cut
  unfold constructedWSelectionRankingInTopPrefix
  infer_instance

/-- Top-prefix probabilities induced by the explicit six-ranking law. -/
def constructedWSelectionRankingTopPrefixProb :
    ConstructedWSelectionCandidate → Fin 2 → ℝ :=
  prefixProbFromEvent
    constructedWSelectionRankingLaw
    constructedWSelectionRankingInTopPrefix

/-- The three-candidate ranking universe used by the constructed example. -/
abbrev ConstructedWSelectionRanking1Candidate :=
  AppliedModelingLib.SocialChoice.Ranking.Candidate 1

/-- Actual three-candidate rankings for the constructed example. -/
abbrev ConstructedWSelectionRanking1 :=
  AppliedModelingLib.SocialChoice.Ranking.Ranking 1

/-- Embed the source candidate names into the canonical `Fin 3` ranking universe. -/
def constructedWSelectionCandidateToRanking1 :
    ConstructedWSelectionCandidate → ConstructedWSelectionRanking1Candidate
  | winner => 0
  | loserI => 1
  | loserJ => 2

/-- Embed the six source ranking rows into actual three-candidate rankings. -/
def constructedWSelectionRankingToRanking1 :
    ConstructedWSelectionRanking → ConstructedWSelectionRanking1
  | hij => Equiv.refl ConstructedWSelectionRanking1Candidate
  | hji => Equiv.swap
      (1 : ConstructedWSelectionRanking1Candidate) 2
  | ihj => Equiv.swap
      (0 : ConstructedWSelectionRanking1Candidate) 1
  | ijh => (Equiv.swap
      (0 : ConstructedWSelectionRanking1Candidate) 1).trans
        (Equiv.swap (0 : ConstructedWSelectionRanking1Candidate) 2)
  | jhi => (Equiv.swap
      (0 : ConstructedWSelectionRanking1Candidate) 2).trans
        (Equiv.swap (0 : ConstructedWSelectionRanking1Candidate) 1)
  | jih => Equiv.swap
      (0 : ConstructedWSelectionRanking1Candidate) 2

/-- The constructed source law as an actual PMF over three-candidate rankings. -/
noncomputable def constructedWSelectionRanking1Law :
    PMF ConstructedWSelectionRanking1 :=
  constructedWSelectionRankingLaw.map constructedWSelectionRankingToRanking1

theorem constructedWSelectionRankingToRanking1_inTopPrefix
    (ranking : ConstructedWSelectionRanking)
    (candidate : ConstructedWSelectionCandidate) (cut : Fin 2) :
    rankingInTopPrefix
        (constructedWSelectionRankingToRanking1 ranking)
        (constructedWSelectionCandidateToRanking1 candidate)
        cut ↔
      constructedWSelectionRankingInTopPrefix ranking candidate cut := by
  cases ranking <;> cases candidate <;> fin_cases cut <;>
    norm_num [rankingInTopPrefix, AppliedModelingLib.SocialChoice.Ranking.rankOf,
      constructedWSelectionRankingToRanking1,
      constructedWSelectionCandidateToRanking1,
      constructedWSelectionRankingInTopPrefix,
      constructedWSelectionRankingInTopPrefixBool,
      Equiv.swap_apply_def] <;>
    decide

/--
Top-prefix probabilities induced by the constructed ranking distribution over
the six strict rankings:
`hij`, `hji`, `ihj`, `ijh`, `jhi`, `jih` with probabilities
`46, 656, 227, 7, 44, 20` thousandths respectively.
-/
def constructedWSelectionTopPrefixProb :
    ConstructedWSelectionCandidate → Fin 2 → ℝ
  | winner, 0 => constructedWSelectionProb 702
  | loserI, 0 => constructedWSelectionProb 234
  | loserJ, 0 => constructedWSelectionProb 64
  | winner, 1 => constructedWSelectionProb 973
  | loserI, 1 => constructedWSelectionProb 300
  | loserJ, 1 => constructedWSelectionProb 727

theorem constructedWSelectionRankingTopPrefixProb_eq
    (candidate : ConstructedWSelectionCandidate) (cut : Fin 2) :
    constructedWSelectionRankingTopPrefixProb candidate cut =
      constructedWSelectionTopPrefixProb candidate cut := by
  cases candidate <;> fin_cases cut <;>
    unfold constructedWSelectionRankingTopPrefixProb prefixProbFromEvent
      AppliedModelingLib.pmfProb AppliedModelingLib.pmfExp <;>
    rw [show (Finset.univ : Finset ConstructedWSelectionRanking) =
        ({hij, hji, ihj, ijh, jhi, jih} :
          Finset ConstructedWSelectionRanking) by
      decide] <;>
    simp [constructedWSelectionRankingLaw,
      constructedWSelectionRankingMass,
      constructedWSelectionRankingMassReal,
      constructedWSelectionRankingInTopPrefix,
      constructedWSelectionRankingInTopPrefixBool,
      constructedWSelectionTopPrefixProb, constructedWSelectionProb] <;>
    norm_num

theorem constructedWSelectionRanking1TopPrefixProb_eq
    (candidate : ConstructedWSelectionCandidate) (cut : Fin 2) :
    rankingTopPrefixProb
        constructedWSelectionRanking1Law
        (constructedWSelectionCandidateToRanking1 candidate)
        cut =
      constructedWSelectionTopPrefixProb candidate cut := by
  unfold rankingTopPrefixProb prefixProbFromEvent
    constructedWSelectionRanking1Law
  rw [AppliedModelingLib.pmfProb_map]
  have hprob :
      AppliedModelingLib.pmfProb constructedWSelectionRankingLaw
          (fun ranking =>
            rankingInTopPrefix
              (constructedWSelectionRankingToRanking1 ranking)
              (constructedWSelectionCandidateToRanking1 candidate)
              cut) =
        constructedWSelectionRankingTopPrefixProb candidate cut := by
    unfold constructedWSelectionRankingTopPrefixProb prefixProbFromEvent
    exact
      AppliedModelingLib.pmfProb_congr
        constructedWSelectionRankingLaw
        (by
          intro ranking
          exact constructedWSelectionRankingToRanking1_inTopPrefix
            ranking candidate cut)
  exact hprob.trans
    (constructedWSelectionRankingTopPrefixProb_eq candidate cut)

/-- Source candidate-indexed top-prefix probabilities from the actual ranking law. -/
def constructedWSelectionRanking1TopPrefixProb :
    ConstructedWSelectionCandidate → Fin 2 → ℝ :=
  fun candidate cut =>
    rankingTopPrefixProb
      constructedWSelectionRanking1Law
      (constructedWSelectionCandidateToRanking1 candidate)
      cut

/-- The W-selection cross-tier relation: the winner must beat both losers. -/
def constructedWSelectionCrossTier :
    ConstructedWSelectionCandidate →
      ConstructedWSelectionCandidate → Prop
  | winner, loserI => True
  | winner, loserJ => True
  | _, _ => False

/--
The constructed example satisfies the strict prefix-dominance condition from
Proposition 1 for selecting the single winner.
-/
theorem constructedWSelection_strictTopPrefixDominanceOn :
    StrictTopPrefixDominanceOn
      constructedWSelectionTopPrefixProb
      constructedWSelectionCrossTier := by
  intro hi lo hcross cut
  cases hi <;> cases lo <;> try contradiction
  all_goals
    fin_cases cut <;>
      norm_num [constructedWSelectionTopPrefixProb,
        constructedWSelectionCrossTier, constructedWSelectionProb] at *

theorem constructedWSelectionRanking1Law_strictTopPrefixDominanceOn :
    StrictTopPrefixDominanceOn
      constructedWSelectionRanking1TopPrefixProb
      constructedWSelectionCrossTier := by
  intro hi lo hcross cut
  unfold constructedWSelectionRanking1TopPrefixProb
  rw [constructedWSelectionRanking1TopPrefixProb_eq lo cut,
    constructedWSelectionRanking1TopPrefixProb_eq hi cut]
  exact constructedWSelection_strictTopPrefixDominanceOn hi lo hcross cut

/-- The single true winner in the constructed three-candidate ranking law. -/
def constructedWSelectionRanking1WinnerSet :
    Finset ConstructedWSelectionRanking1Candidate :=
  {constructedWSelectionCandidateToRanking1 winner}

theorem constructedWSelectionRanking1Law_winnerSet_strictPrefixDominance :
    ∀ hi lo : ConstructedWSelectionRanking1Candidate,
      hi ∈ constructedWSelectionRanking1WinnerSet →
        lo ∉ constructedWSelectionRanking1WinnerSet →
          ∀ cut : RankingProperPrefixCut 1,
            rankingTopPrefixProb constructedWSelectionRanking1Law lo cut <
              rankingTopPrefixProb constructedWSelectionRanking1Law hi cut := by
  intro hi lo hhi hlo cut
  fin_cases hi <;>
    simp [constructedWSelectionRanking1WinnerSet,
      constructedWSelectionCandidateToRanking1] at hhi
  fin_cases lo
  · simp [constructedWSelectionRanking1WinnerSet,
      constructedWSelectionCandidateToRanking1] at hlo
  · simpa [constructedWSelectionRanking1TopPrefixProb,
      constructedWSelectionCandidateToRanking1] using
      constructedWSelectionRanking1Law_strictTopPrefixDominanceOn
        winner loserI trivial cut
  · simpa [constructedWSelectionRanking1TopPrefixProb,
      constructedWSelectionCandidateToRanking1] using
      constructedWSelectionRanking1Law_strictTopPrefixDominanceOn
        winner loserJ trivial cut

theorem constructedWSelectionRanking1Law_allReasonablePrefixScoreSeparation :
    ∀ diff : RankingProperPrefixCut 1 → ℝ,
      ReasonablePrefixWeights diff →
        ∀ hi lo : ConstructedWSelectionRanking1Candidate,
          hi ∈ constructedWSelectionRanking1WinnerSet →
            lo ∉ constructedWSelectionRanking1WinnerSet →
              prefixExpectedScore diff
                  (rankingTopPrefixProb constructedWSelectionRanking1Law)
                  lo <
                prefixExpectedScore diff
                  (rankingTopPrefixProb constructedWSelectionRanking1Law)
                  hi :=
  (rankingStrictPrefixDominance_iff_all_reasonable_prefix_score_separation
    constructedWSelectionRanking1Law
    constructedWSelectionRanking1WinnerSet).1
    constructedWSelectionRanking1Law_winnerSet_strictPrefixDominance

theorem constructedWSelectionRanking1Law_allReasonablePrefixScoreConsistency :
    ∀ diff : RankingProperPrefixCut 1 → ℝ,
      ReasonablePrefixWeights diff →
        Filter.Tendsto
          (scoreTopSelectionErrorProb constructedWSelectionRanking1Law
            (rankingPrefixScore diff)
            constructedWSelectionRanking1WinnerSet
            (fun _voters sample =>
              scoreTopSelectedSetOfCard
                (iidSampleCandidateScore (rankingPrefixScore diff) sample)
                constructedWSelectionRanking1WinnerSet))
          Filter.atTop (nhds 0) := by
  letI : Nonempty (CrossTierPair constructedWSelectionRanking1WinnerSet) :=
    ⟨⟨(constructedWSelectionCandidateToRanking1 winner,
        constructedWSelectionCandidateToRanking1 loserI), by
        simp [constructedWSelectionRanking1WinnerSet,
          constructedWSelectionCandidateToRanking1]⟩⟩
  exact
    rankingStrictPrefixDominance_implies_all_reasonable_prefix_score_consistency
      constructedWSelectionRanking1Law
      constructedWSelectionRanking1WinnerSet
      constructedWSelectionRanking1Law_winnerSet_strictPrefixDominance

def constructedWSelectionPairLoserToRanking1 :
    ConstructedWSelectionPair → ConstructedWSelectionRanking1Candidate
  | ConstructedWSelectionPair.hi =>
      constructedWSelectionCandidateToRanking1 loserI
  | ConstructedWSelectionPair.hj =>
      constructedWSelectionCandidateToRanking1 loserJ

def constructedWSelectionPairWinnerToRanking1 :
    ConstructedWSelectionPair → ConstructedWSelectionRanking1Candidate :=
  fun _ => constructedWSelectionCandidateToRanking1 winner

def constructedWSelectionK1Up : ConstructedWSelectionPair → ℝ
  | ConstructedWSelectionPair.hi => constructedWSelectionProb 702
  | ConstructedWSelectionPair.hj => constructedWSelectionProb 702

def constructedWSelectionK1Down : ConstructedWSelectionPair → ℝ
  | ConstructedWSelectionPair.hi => constructedWSelectionProb 234
  | ConstructedWSelectionPair.hj => constructedWSelectionProb 64

def constructedWSelectionK2Up : ConstructedWSelectionPair → ℝ
  | ConstructedWSelectionPair.hi => constructedWSelectionProb 700
  | ConstructedWSelectionPair.hj => constructedWSelectionProb 273

def constructedWSelectionK2Down : ConstructedWSelectionPair → ℝ
  | ConstructedWSelectionPair.hi => constructedWSelectionProb 27
  | ConstructedWSelectionPair.hj => constructedWSelectionProb 27

def constructedWSelectionRandomizedUp : ConstructedWSelectionPair → ℝ
  | ConstructedWSelectionPair.hi => (701 : ℝ) / 1000
  | ConstructedWSelectionPair.hj => (975 : ℝ) / 2000

def constructedWSelectionRandomizedDown : ConstructedWSelectionPair → ℝ
  | ConstructedWSelectionPair.hi => (261 : ℝ) / 2000
  | ConstructedWSelectionPair.hj => (91 : ℝ) / 2000

theorem constructedWSelectionRanking1K1UpProb_eq
    (pair : ConstructedWSelectionPair) :
    AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
        constructedWSelectionRanking1Law 1
        (constructedWSelectionCandidateToRanking1 winner)
        (constructedWSelectionPairLoserToRanking1 pair) =
      constructedWSelectionK1Up pair := by
  cases pair <;>
    unfold AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
      constructedWSelectionRanking1Law <;>
    rw [AppliedModelingLib.pmfProb_map] <;>
    unfold AppliedModelingLib.pmfProb AppliedModelingLib.pmfExp <;>
    rw [show (Finset.univ : Finset ConstructedWSelectionRanking) =
        ({hij, hji, ihj, ijh, jhi, jih} :
          Finset ConstructedWSelectionRanking) by
      decide] <;>
    simp [constructedWSelectionRankingLaw,
      constructedWSelectionRankingMass,
      constructedWSelectionRankingMassReal,
      constructedWSelectionRankingToRanking1,
      constructedWSelectionCandidateToRanking1,
      constructedWSelectionPairLoserToRanking1,
      AppliedModelingLib.SocialChoice.Ranking.approvedByK,
      AppliedModelingLib.SocialChoice.Ranking.rankOf,
      constructedWSelectionK1Up, constructedWSelectionProb,
      Equiv.swap_apply_def] <;>
    norm_num

theorem constructedWSelectionRanking1K1DownProb_eq
    (pair : ConstructedWSelectionPair) :
    AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
        constructedWSelectionRanking1Law 1
        (constructedWSelectionCandidateToRanking1 winner)
        (constructedWSelectionPairLoserToRanking1 pair) =
      constructedWSelectionK1Down pair := by
  cases pair <;>
    unfold AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
      constructedWSelectionRanking1Law <;>
    rw [AppliedModelingLib.pmfProb_map] <;>
    unfold AppliedModelingLib.pmfProb AppliedModelingLib.pmfExp <;>
    rw [show (Finset.univ : Finset ConstructedWSelectionRanking) =
        ({hij, hji, ihj, ijh, jhi, jih} :
          Finset ConstructedWSelectionRanking) by
      decide] <;>
    simp [constructedWSelectionRankingLaw,
      constructedWSelectionRankingMass,
      constructedWSelectionRankingMassReal,
      constructedWSelectionRankingToRanking1,
      constructedWSelectionCandidateToRanking1,
      constructedWSelectionPairLoserToRanking1,
      AppliedModelingLib.SocialChoice.Ranking.approvedByK,
      AppliedModelingLib.SocialChoice.Ranking.rankOf,
      constructedWSelectionK1Down, constructedWSelectionProb,
      Equiv.swap_apply_def] <;>
    norm_num

theorem constructedWSelectionRanking1K2UpProb_eq
    (pair : ConstructedWSelectionPair) :
    AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
        constructedWSelectionRanking1Law 2
        (constructedWSelectionCandidateToRanking1 winner)
        (constructedWSelectionPairLoserToRanking1 pair) =
      constructedWSelectionK2Up pair := by
  cases pair <;>
    unfold AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
      constructedWSelectionRanking1Law <;>
    rw [AppliedModelingLib.pmfProb_map] <;>
    unfold AppliedModelingLib.pmfProb AppliedModelingLib.pmfExp <;>
    rw [show (Finset.univ : Finset ConstructedWSelectionRanking) =
        ({hij, hji, ihj, ijh, jhi, jih} :
          Finset ConstructedWSelectionRanking) by
      decide] <;>
    simp [constructedWSelectionRankingLaw,
      constructedWSelectionRankingMass,
      constructedWSelectionRankingMassReal,
      constructedWSelectionRankingToRanking1,
      constructedWSelectionCandidateToRanking1,
      constructedWSelectionPairLoserToRanking1,
      AppliedModelingLib.SocialChoice.Ranking.approvedByK,
      AppliedModelingLib.SocialChoice.Ranking.rankOf,
      constructedWSelectionK2Up, constructedWSelectionProb,
      Equiv.swap_apply_def] <;>
    norm_num

theorem constructedWSelectionRanking1K2DownProb_eq
    (pair : ConstructedWSelectionPair) :
    AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
        constructedWSelectionRanking1Law 2
        (constructedWSelectionCandidateToRanking1 winner)
        (constructedWSelectionPairLoserToRanking1 pair) =
      constructedWSelectionK2Down pair := by
  cases pair <;>
    unfold AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
      constructedWSelectionRanking1Law <;>
    rw [AppliedModelingLib.pmfProb_map] <;>
    unfold AppliedModelingLib.pmfProb AppliedModelingLib.pmfExp <;>
    rw [show (Finset.univ : Finset ConstructedWSelectionRanking) =
        ({hij, hji, ihj, ijh, jhi, jih} :
          Finset ConstructedWSelectionRanking) by
      decide] <;>
    simp [constructedWSelectionRankingLaw,
      constructedWSelectionRankingMass,
      constructedWSelectionRankingMassReal,
      constructedWSelectionRankingToRanking1,
      constructedWSelectionCandidateToRanking1,
      constructedWSelectionPairLoserToRanking1,
      AppliedModelingLib.SocialChoice.Ranking.approvedByK,
      AppliedModelingLib.SocialChoice.Ranking.rankOf,
      constructedWSelectionK2Down, constructedWSelectionProb,
      Equiv.swap_apply_def] <;>
    norm_num

theorem constructedWSelectionRanking1RandomizedUpProb_eq_average
    (pair : ConstructedWSelectionPair) :
    (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
          constructedWSelectionRanking1Law 1
          (constructedWSelectionCandidateToRanking1 winner)
          (constructedWSelectionPairLoserToRanking1 pair) +
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
          constructedWSelectionRanking1Law 2
          (constructedWSelectionCandidateToRanking1 winner)
          (constructedWSelectionPairLoserToRanking1 pair)) / 2 =
      constructedWSelectionRandomizedUp pair := by
  rw [constructedWSelectionRanking1K1UpProb_eq pair,
    constructedWSelectionRanking1K2UpProb_eq pair]
  cases pair <;>
    norm_num [constructedWSelectionRandomizedUp,
      constructedWSelectionK1Up, constructedWSelectionK2Up,
      constructedWSelectionProb]

theorem constructedWSelectionRanking1RandomizedDownProb_eq_average
    (pair : ConstructedWSelectionPair) :
    (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
          constructedWSelectionRanking1Law 1
          (constructedWSelectionCandidateToRanking1 winner)
          (constructedWSelectionPairLoserToRanking1 pair) +
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
          constructedWSelectionRanking1Law 2
          (constructedWSelectionCandidateToRanking1 winner)
          (constructedWSelectionPairLoserToRanking1 pair)) / 2 =
      constructedWSelectionRandomizedDown pair := by
  rw [constructedWSelectionRanking1K1DownProb_eq pair,
    constructedWSelectionRanking1K2DownProb_eq pair]
  cases pair <;>
    norm_num [constructedWSelectionRandomizedDown,
      constructedWSelectionK1Down, constructedWSelectionK2Down,
      constructedWSelectionProb]

/-- Actual 50/50 randomized approval up-probabilities from K=1 and K=2. -/
def constructedWSelectionRanking1RandomizedApprovalUp
    (pair : ConstructedWSelectionPair) : ℝ :=
  (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
      constructedWSelectionRanking1Law 1
      (constructedWSelectionCandidateToRanking1 winner)
      (constructedWSelectionPairLoserToRanking1 pair) +
    AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
      constructedWSelectionRanking1Law 2
      (constructedWSelectionCandidateToRanking1 winner)
      (constructedWSelectionPairLoserToRanking1 pair)) / 2

/-- Actual 50/50 randomized approval down-probabilities from K=1 and K=2. -/
def constructedWSelectionRanking1RandomizedApprovalDown
    (pair : ConstructedWSelectionPair) : ℝ :=
  (AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
      constructedWSelectionRanking1Law 1
      (constructedWSelectionCandidateToRanking1 winner)
      (constructedWSelectionPairLoserToRanking1 pair) +
    AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
      constructedWSelectionRanking1Law 2
      (constructedWSelectionCandidateToRanking1 winner)
      (constructedWSelectionPairLoserToRanking1 pair)) / 2

/-- Actual 50/50 randomized approval pairwise rates from K=1 and K=2. -/
def constructedWSelectionRanking1RandomizedApprovalRate
    (pair : ConstructedWSelectionPair) : ℝ :=
  approvalPairwiseRate
    (constructedWSelectionRanking1RandomizedApprovalUp pair)
    (constructedWSelectionRanking1RandomizedApprovalDown pair)

theorem constructedWSelectionRanking1RandomizedApprovalUp_eq
    (pair : ConstructedWSelectionPair) :
    constructedWSelectionRanking1RandomizedApprovalUp pair =
      constructedWSelectionRandomizedUp pair :=
  constructedWSelectionRanking1RandomizedUpProb_eq_average pair

theorem constructedWSelectionRanking1RandomizedApprovalDown_eq
    (pair : ConstructedWSelectionPair) :
    constructedWSelectionRanking1RandomizedApprovalDown pair =
      constructedWSelectionRandomizedDown pair :=
  constructedWSelectionRanking1RandomizedDownProb_eq_average pair

def constructedWSelectionK1Rate (pair : ConstructedWSelectionPair) : ℝ :=
  approvalPairwiseRate
    (constructedWSelectionK1Up pair) (constructedWSelectionK1Down pair)

def constructedWSelectionK2Rate (pair : ConstructedWSelectionPair) : ℝ :=
  approvalPairwiseRate
    (constructedWSelectionK2Up pair) (constructedWSelectionK2Down pair)

def constructedWSelectionRandomizedRate
    (pair : ConstructedWSelectionPair) : ℝ :=
  approvalPairwiseRate
    (constructedWSelectionRandomizedUp pair)
    (constructedWSelectionRandomizedDown pair)

theorem constructedWSelectionRanking1RandomizedApprovalRate_eq
    (pair : ConstructedWSelectionPair) :
    constructedWSelectionRanking1RandomizedApprovalRate pair =
      constructedWSelectionRandomizedRate pair := by
  simp [constructedWSelectionRanking1RandomizedApprovalRate,
    constructedWSelectionRandomizedRate,
    constructedWSelectionRanking1RandomizedApprovalUp_eq,
    constructedWSelectionRanking1RandomizedApprovalDown_eq]

private theorem constructedWSelection_base_pos_702_234 :
    0 < approvalPairwiseBase
      (constructedWSelectionProb 702) (constructedWSelectionProb 234) := by
  have hup : 0 < constructedWSelectionProb 702 := by
    norm_num [constructedWSelectionProb]
  have hdown : 0 < constructedWSelectionProb 234 := by
    norm_num [constructedWSelectionProb]
  have hsum : constructedWSelectionProb 702 +
      constructedWSelectionProb 234 ≤ 1 := by
    norm_num [constructedWSelectionProb]
  simpa [approvalPairwiseBase] using
    ternaryGap_closedExpr_pos hup hdown hsum

private theorem constructedWSelection_base_pos_702_64 :
    0 < approvalPairwiseBase
      (constructedWSelectionProb 702) (constructedWSelectionProb 64) := by
  have hup : 0 < constructedWSelectionProb 702 := by
    norm_num [constructedWSelectionProb]
  have hdown : 0 < constructedWSelectionProb 64 := by
    norm_num [constructedWSelectionProb]
  have hsum : constructedWSelectionProb 702 +
      constructedWSelectionProb 64 ≤ 1 := by
    norm_num [constructedWSelectionProb]
  simpa [approvalPairwiseBase] using
    ternaryGap_closedExpr_pos hup hdown hsum

private theorem constructedWSelection_base_pos_700_27 :
    0 < approvalPairwiseBase
      (constructedWSelectionProb 700) (constructedWSelectionProb 27) := by
  have hup : 0 < constructedWSelectionProb 700 := by
    norm_num [constructedWSelectionProb]
  have hdown : 0 < constructedWSelectionProb 27 := by
    norm_num [constructedWSelectionProb]
  have hsum : constructedWSelectionProb 700 +
      constructedWSelectionProb 27 ≤ 1 := by
    norm_num [constructedWSelectionProb]
  simpa [approvalPairwiseBase] using
    ternaryGap_closedExpr_pos hup hdown hsum

private theorem constructedWSelection_base_pos_273_27 :
    0 < approvalPairwiseBase
      (constructedWSelectionProb 273) (constructedWSelectionProb 27) := by
  have hup : 0 < constructedWSelectionProb 273 := by
    norm_num [constructedWSelectionProb]
  have hdown : 0 < constructedWSelectionProb 27 := by
    norm_num [constructedWSelectionProb]
  have hsum : constructedWSelectionProb 273 +
      constructedWSelectionProb 27 ≤ 1 := by
    norm_num [constructedWSelectionProb]
  simpa [approvalPairwiseBase] using
    ternaryGap_closedExpr_pos hup hdown hsum

private theorem constructedWSelection_base_pos_701_261 :
    0 < approvalPairwiseBase ((701 : ℝ) / 1000) ((261 : ℝ) / 2000) := by
  have hup : 0 < (701 : ℝ) / 1000 := by norm_num
  have hdown : 0 < (261 : ℝ) / 2000 := by norm_num
  have hsum : (701 : ℝ) / 1000 + (261 : ℝ) / 2000 ≤ 1 := by
    norm_num
  simpa [approvalPairwiseBase] using
    ternaryGap_closedExpr_pos hup hdown hsum

private theorem constructedWSelection_base_pos_975_91 :
    0 < approvalPairwiseBase ((975 : ℝ) / 2000) ((91 : ℝ) / 2000) := by
  have hup : 0 < (975 : ℝ) / 2000 := by norm_num
  have hdown : 0 < (91 : ℝ) / 2000 := by norm_num
  have hsum : (975 : ℝ) / 2000 + (91 : ℝ) / 2000 ≤ 1 := by
    norm_num
  simpa [approvalPairwiseBase] using
    ternaryGap_closedExpr_pos hup hdown hsum

private theorem constructedWSelection_base_702_64_lt_702_234 :
    approvalPairwiseBase
        (constructedWSelectionProb 702) (constructedWSelectionProb 64) <
      approvalPairwiseBase
        (constructedWSelectionProb 702) (constructedWSelectionProb 234) := by
  have hleft_sqrt :
      Real.sqrt
          (constructedWSelectionProb 702 * constructedWSelectionProb 64) <
        (212 : ℝ) / 1000 := by
    exact (Real.sqrt_lt
      (by norm_num [constructedWSelectionProb] :
        0 ≤ constructedWSelectionProb 702 * constructedWSelectionProb 64)
      (by norm_num : 0 ≤ (212 : ℝ) / 1000)).2
      (by norm_num [constructedWSelectionProb])
  have hright_sqrt :
      (405 : ℝ) / 1000 <
        Real.sqrt
          (constructedWSelectionProb 702 * constructedWSelectionProb 234) := by
    exact (Real.lt_sqrt (by norm_num : 0 ≤ (405 : ℝ) / 1000)).2
      (by norm_num [constructedWSelectionProb])
  unfold approvalPairwiseBase constructedWSelectionProb at *
  nlinarith

private theorem constructedWSelection_base_700_27_lt_273_27 :
    approvalPairwiseBase
        (constructedWSelectionProb 700) (constructedWSelectionProb 27) <
      approvalPairwiseBase
        (constructedWSelectionProb 273) (constructedWSelectionProb 27) := by
  have hleft_sqrt :
      Real.sqrt
          (constructedWSelectionProb 700 * constructedWSelectionProb 27) <
        (138 : ℝ) / 1000 := by
    exact (Real.sqrt_lt
      (by norm_num [constructedWSelectionProb] :
        0 ≤ constructedWSelectionProb 700 * constructedWSelectionProb 27)
      (by norm_num : 0 ≤ (138 : ℝ) / 1000)).2
      (by norm_num [constructedWSelectionProb])
  have hright_sqrt :
      (85 : ℝ) / 1000 <
        Real.sqrt
          (constructedWSelectionProb 273 * constructedWSelectionProb 27) := by
    exact (Real.lt_sqrt (by norm_num : 0 ≤ (85 : ℝ) / 1000)).2
      (by norm_num [constructedWSelectionProb])
  unfold approvalPairwiseBase constructedWSelectionProb at *
  nlinarith

private theorem constructedWSelection_base_701_261_lt_702_234 :
    approvalPairwiseBase ((701 : ℝ) / 1000) ((261 : ℝ) / 2000) <
      approvalPairwiseBase
        (constructedWSelectionProb 702) (constructedWSelectionProb 234) := by
  have hleft_sqrt :
      Real.sqrt (((701 : ℝ) / 1000) * ((261 : ℝ) / 2000)) <
        (303 : ℝ) / 1000 := by
    exact (Real.sqrt_lt
      (by norm_num : 0 ≤ ((701 : ℝ) / 1000) * ((261 : ℝ) / 2000))
      (by norm_num : 0 ≤ (303 : ℝ) / 1000)).2
      (by norm_num)
  have hright_sqrt :
      (405 : ℝ) / 1000 <
        Real.sqrt
          (constructedWSelectionProb 702 * constructedWSelectionProb 234) := by
    exact (Real.lt_sqrt (by norm_num : 0 ≤ (405 : ℝ) / 1000)).2
      (by norm_num [constructedWSelectionProb])
  unfold approvalPairwiseBase constructedWSelectionProb at *
  nlinarith

private theorem constructedWSelection_base_975_91_lt_702_234 :
    approvalPairwiseBase ((975 : ℝ) / 2000) ((91 : ℝ) / 2000) <
      approvalPairwiseBase
        (constructedWSelectionProb 702) (constructedWSelectionProb 234) := by
  have hleft_sqrt :
      Real.sqrt (((975 : ℝ) / 2000) * ((91 : ℝ) / 2000)) <
        (149 : ℝ) / 1000 := by
    exact (Real.sqrt_lt
      (by norm_num : 0 ≤ ((975 : ℝ) / 2000) * ((91 : ℝ) / 2000))
      (by norm_num : 0 ≤ (149 : ℝ) / 1000)).2
      (by norm_num)
  have hright_sqrt :
      (405 : ℝ) / 1000 <
        Real.sqrt
          (constructedWSelectionProb 702 * constructedWSelectionProb 234) := by
    exact (Real.lt_sqrt (by norm_num : 0 ≤ (405 : ℝ) / 1000)).2
      (by norm_num [constructedWSelectionProb])
  unfold approvalPairwiseBase constructedWSelectionProb at *
  nlinarith

private theorem constructedWSelection_base_701_261_lt_273_27 :
    approvalPairwiseBase ((701 : ℝ) / 1000) ((261 : ℝ) / 2000) <
      approvalPairwiseBase
        (constructedWSelectionProb 273) (constructedWSelectionProb 27) := by
  have hleft_sqrt :
      Real.sqrt (((701 : ℝ) / 1000) * ((261 : ℝ) / 2000)) <
        (303 : ℝ) / 1000 := by
    exact (Real.sqrt_lt
      (by norm_num : 0 ≤ ((701 : ℝ) / 1000) * ((261 : ℝ) / 2000))
      (by norm_num : 0 ≤ (303 : ℝ) / 1000)).2
      (by norm_num)
  have hright_sqrt :
      (85 : ℝ) / 1000 <
        Real.sqrt
          (constructedWSelectionProb 273 * constructedWSelectionProb 27) := by
    exact (Real.lt_sqrt (by norm_num : 0 ≤ (85 : ℝ) / 1000)).2
      (by norm_num [constructedWSelectionProb])
  unfold approvalPairwiseBase constructedWSelectionProb at *
  nlinarith

private theorem constructedWSelection_base_975_91_lt_273_27 :
    approvalPairwiseBase ((975 : ℝ) / 2000) ((91 : ℝ) / 2000) <
      approvalPairwiseBase
        (constructedWSelectionProb 273) (constructedWSelectionProb 27) := by
  have hleft_sqrt :
      Real.sqrt (((975 : ℝ) / 2000) * ((91 : ℝ) / 2000)) <
        (149 : ℝ) / 1000 := by
    exact (Real.sqrt_lt
      (by norm_num : 0 ≤ ((975 : ℝ) / 2000) * ((91 : ℝ) / 2000))
      (by norm_num : 0 ≤ (149 : ℝ) / 1000)).2
      (by norm_num)
  have hright_sqrt :
      (85 : ℝ) / 1000 <
        Real.sqrt
          (constructedWSelectionProb 273 * constructedWSelectionProb 27) := by
    exact (Real.lt_sqrt (by norm_num : 0 ≤ (85 : ℝ) / 1000)).2
      (by norm_num [constructedWSelectionProb])
  unfold approvalPairwiseBase constructedWSelectionProb at *
  nlinarith

theorem constructedWSelectionK1_outcomeRate_eq_hi :
    finiteOutcomeLearningRate constructedWSelectionK1Rate =
      constructedWSelectionK1Rate ConstructedWSelectionPair.hi := by
  have hrate :
      constructedWSelectionK1Rate ConstructedWSelectionPair.hi ≤
        constructedWSelectionK1Rate ConstructedWSelectionPair.hj := by
    simpa [constructedWSelectionK1Rate, constructedWSelectionK1Up,
      constructedWSelectionK1Down] using
      (approvalPairwiseRate_lt_of_base_gt
      constructedWSelection_base_pos_702_234
      constructedWSelection_base_pos_702_64
      constructedWSelection_base_702_64_lt_702_234).le
  unfold finiteOutcomeLearningRate
  apply le_antisymm
  · exact Finset.inf'_le constructedWSelectionK1Rate
      (by
        simp : ConstructedWSelectionPair.hi ∈
          (Finset.univ : Finset ConstructedWSelectionPair))
  · exact Finset.le_inf' _ _ (by
      intro pair _
      cases pair
      · rfl
      · exact hrate)

theorem constructedWSelectionK2_outcomeRate_eq_hj :
    finiteOutcomeLearningRate constructedWSelectionK2Rate =
      constructedWSelectionK2Rate ConstructedWSelectionPair.hj := by
  have hrate :
      constructedWSelectionK2Rate ConstructedWSelectionPair.hj ≤
        constructedWSelectionK2Rate ConstructedWSelectionPair.hi := by
    simpa [constructedWSelectionK2Rate, constructedWSelectionK2Up,
      constructedWSelectionK2Down] using
      (approvalPairwiseRate_lt_of_base_gt
      constructedWSelection_base_pos_273_27
      constructedWSelection_base_pos_700_27
      constructedWSelection_base_700_27_lt_273_27).le
  unfold finiteOutcomeLearningRate
  apply le_antisymm
  · exact Finset.inf'_le constructedWSelectionK2Rate
      (by
        simp : ConstructedWSelectionPair.hj ∈
          (Finset.univ : Finset ConstructedWSelectionPair))
  · exact Finset.le_inf' _ _ (by
      intro pair _
      cases pair
      · exact hrate
      · rfl)

theorem constructedWSelectionK1Up_pos :
    ∀ pair : ConstructedWSelectionPair, 0 < constructedWSelectionK1Up pair := by
  intro pair
  cases pair <;> norm_num [constructedWSelectionK1Up, constructedWSelectionProb]

theorem constructedWSelectionK1Down_pos :
    ∀ pair : ConstructedWSelectionPair,
      0 < constructedWSelectionK1Down pair := by
  intro pair
  cases pair <;> norm_num [constructedWSelectionK1Down, constructedWSelectionProb]

theorem constructedWSelectionK1Down_lt_up :
    ∀ pair : ConstructedWSelectionPair,
      constructedWSelectionK1Down pair < constructedWSelectionK1Up pair := by
  intro pair
  cases pair <;>
    norm_num [constructedWSelectionK1Up, constructedWSelectionK1Down,
      constructedWSelectionProb]

theorem constructedWSelectionK2Up_pos :
    ∀ pair : ConstructedWSelectionPair, 0 < constructedWSelectionK2Up pair := by
  intro pair
  cases pair <;> norm_num [constructedWSelectionK2Up, constructedWSelectionProb]

theorem constructedWSelectionK2Down_pos :
    ∀ pair : ConstructedWSelectionPair,
      0 < constructedWSelectionK2Down pair := by
  intro pair
  cases pair <;> norm_num [constructedWSelectionK2Down, constructedWSelectionProb]

theorem constructedWSelectionK2Down_lt_up :
    ∀ pair : ConstructedWSelectionPair,
      constructedWSelectionK2Down pair < constructedWSelectionK2Up pair := by
  intro pair
  cases pair <;>
    norm_num [constructedWSelectionK2Up, constructedWSelectionK2Down,
      constructedWSelectionProb]

def constructedWSelectionRanking1K1RelevantPairRateCertificate :
    FiniteErrorRateCertificate ConstructedWSelectionPair :=
  kApprovalRelevantPairRateCertificate
    constructedWSelectionRanking1Law 1
    constructedWSelectionPairWinnerToRanking1
    constructedWSelectionPairLoserToRanking1
    constructedWSelectionK1Up
    constructedWSelectionK1Down
    constructedWSelectionK1Up_pos
    constructedWSelectionK1Down_pos
    (fun pair => (constructedWSelectionK1Down_lt_up pair).le)
    constructedWSelectionRanking1K1UpProb_eq
    constructedWSelectionRanking1K1DownProb_eq

def constructedWSelectionRanking1K2RelevantPairRateCertificate :
    FiniteErrorRateCertificate ConstructedWSelectionPair :=
  kApprovalRelevantPairRateCertificate
    constructedWSelectionRanking1Law 2
    constructedWSelectionPairWinnerToRanking1
    constructedWSelectionPairLoserToRanking1
    constructedWSelectionK2Up
    constructedWSelectionK2Down
    constructedWSelectionK2Up_pos
    constructedWSelectionK2Down_pos
    (fun pair => (constructedWSelectionK2Down_lt_up pair).le)
    constructedWSelectionRanking1K2UpProb_eq
    constructedWSelectionRanking1K2DownProb_eq

theorem constructedWSelectionRanking1K1_outcomeError_hasExponentialRate
    {pairWeight : ConstructedWSelectionPair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hweight_pos : ∀ pair, 0 < pairWeight pair) :
    HasExponentialRate
      (constructedWSelectionRanking1K1RelevantPairRateCertificate
        |>.aggregateError pairWeight)
      (finiteOutcomeLearningRate constructedWSelectionK1Rate) := by
  simpa [constructedWSelectionRanking1K1RelevantPairRateCertificate,
    constructedWSelectionK1Rate] using
    outcomeError_hasExponentialRate_of_kApproval_relevant_pairs_at_finiteOutcomeLearningRate_of_down_lt_up
      constructedWSelectionRanking1Law 1
      constructedWSelectionPairWinnerToRanking1
      constructedWSelectionPairLoserToRanking1
      constructedWSelectionK1Up
      constructedWSelectionK1Down
      constructedWSelectionK1Up_pos
      constructedWSelectionK1Down_pos
      constructedWSelectionK1Down_lt_up
      constructedWSelectionRanking1K1UpProb_eq
      constructedWSelectionRanking1K1DownProb_eq
      hweight
      hweight_pos

theorem constructedWSelectionRanking1K2_outcomeError_hasExponentialRate
    {pairWeight : ConstructedWSelectionPair → ℝ}
    (hweight : ∀ pair, 0 ≤ pairWeight pair)
    (hweight_pos : ∀ pair, 0 < pairWeight pair) :
    HasExponentialRate
      (constructedWSelectionRanking1K2RelevantPairRateCertificate
        |>.aggregateError pairWeight)
      (finiteOutcomeLearningRate constructedWSelectionK2Rate) := by
  simpa [constructedWSelectionRanking1K2RelevantPairRateCertificate,
    constructedWSelectionK2Rate] using
    outcomeError_hasExponentialRate_of_kApproval_relevant_pairs_at_finiteOutcomeLearningRate_of_down_lt_up
      constructedWSelectionRanking1Law 2
      constructedWSelectionPairWinnerToRanking1
      constructedWSelectionPairLoserToRanking1
      constructedWSelectionK2Up
      constructedWSelectionK2Down
      constructedWSelectionK2Up_pos
      constructedWSelectionK2Down_pos
      constructedWSelectionK2Down_lt_up
      constructedWSelectionRanking1K2UpProb_eq
      constructedWSelectionRanking1K2DownProb_eq
      hweight
      hweight_pos

/--
Constructed design-invariant W-selection example: randomizing 50/50 between
1-approval and 2-approval strictly improves the finite W-selection learning
rate over both static rules.
-/
theorem constructedWSelectionRandomizedApproval_improves_staticK1_staticK2 :
    max
        (finiteOutcomeLearningRate constructedWSelectionK1Rate)
        (finiteOutcomeLearningRate constructedWSelectionK2Rate) <
      finiteOutcomeLearningRate constructedWSelectionRandomizedRate := by
  refine randomizedOutcomeRate_strictly_improves_two_static_of_bounds
    constructedWSelectionK1Rate constructedWSelectionK2Rate
    constructedWSelectionRandomizedRate ?_ ?_
  · rw [constructedWSelectionK1_outcomeRate_eq_hi]
    unfold finiteOutcomeLearningRate
    rw [Finset.lt_inf'_iff]
    intro pair _
    cases pair with
    | hi =>
        simpa [constructedWSelectionK1Rate, constructedWSelectionK1Up,
          constructedWSelectionK1Down, constructedWSelectionRandomizedRate,
          constructedWSelectionRandomizedUp,
          constructedWSelectionRandomizedDown] using
          approvalPairwiseRate_lt_of_base_gt
          constructedWSelection_base_pos_702_234
          constructedWSelection_base_pos_701_261
          constructedWSelection_base_701_261_lt_702_234
    | hj =>
        simpa [constructedWSelectionK1Rate, constructedWSelectionK1Up,
          constructedWSelectionK1Down, constructedWSelectionRandomizedRate,
          constructedWSelectionRandomizedUp,
          constructedWSelectionRandomizedDown] using
          approvalPairwiseRate_lt_of_base_gt
          constructedWSelection_base_pos_702_234
          constructedWSelection_base_pos_975_91
          constructedWSelection_base_975_91_lt_702_234
  · rw [constructedWSelectionK2_outcomeRate_eq_hj]
    unfold finiteOutcomeLearningRate
    rw [Finset.lt_inf'_iff]
    intro pair _
    cases pair with
    | hi =>
        simpa [constructedWSelectionK2Rate, constructedWSelectionK2Up,
          constructedWSelectionK2Down, constructedWSelectionRandomizedRate,
          constructedWSelectionRandomizedUp,
          constructedWSelectionRandomizedDown] using
          approvalPairwiseRate_lt_of_base_gt
          constructedWSelection_base_pos_273_27
          constructedWSelection_base_pos_701_261
          constructedWSelection_base_701_261_lt_273_27
    | hj =>
        simpa [constructedWSelectionK2Rate, constructedWSelectionK2Up,
          constructedWSelectionK2Down, constructedWSelectionRandomizedRate,
          constructedWSelectionRandomizedUp,
          constructedWSelectionRandomizedDown] using
          approvalPairwiseRate_lt_of_base_gt
          constructedWSelection_base_pos_273_27
          constructedWSelection_base_pos_975_91
          constructedWSelection_base_975_91_lt_273_27

/--
Static approval categories used by the source proof of
`lem:randomizebetterapproval_Wselection`: the two constructive cutoffs `K` and
`L`, plus representative side-case buckets for the other static cutoffs.
-/
inductive ConstructedWSelectionStaticCategory where
  | sourceK
  | sourceL
  | oneSidedSmall
  | nearTie
  | oneSidedBoundary
  deriving DecidableEq, Fintype

namespace ConstructedWSelectionStaticCategory

instance : Nonempty ConstructedWSelectionStaticCategory := ⟨sourceK⟩

end ConstructedWSelectionStaticCategory

/-- Common static base rate for the two constructive K/L cutoffs. -/
def constructedWSelectionStaticBaseRate : ℝ :=
  max
    (finiteOutcomeLearningRate constructedWSelectionK1Rate)
    (finiteOutcomeLearningRate constructedWSelectionK2Rate)

theorem constructedWSelectionStaticBaseRate_pos :
    0 < constructedWSelectionStaticBaseRate := by
  have hK1_pos :
      0 < finiteOutcomeLearningRate constructedWSelectionK1Rate := by
    rw [constructedWSelectionK1_outcomeRate_eq_hi]
    simpa [constructedWSelectionK1Rate, constructedWSelectionK1Up,
      constructedWSelectionK1Down] using
      approvalPairwiseRate_pos_of_down_lt_up
        (by norm_num [constructedWSelectionProb])
        (by norm_num [constructedWSelectionProb])
        (by norm_num [constructedWSelectionProb])
        (by norm_num [constructedWSelectionProb])
  exact lt_of_lt_of_le hK1_pos (le_max_left _ _)

/-- Actual K-approval up-probabilities for the four static cutoffs on `Ranking 1`. -/
def constructedWSelectionRanking1StaticKUp
    (K : Fin 4) (pair : ConstructedWSelectionPair) : ℝ :=
  AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb
    constructedWSelectionRanking1Law K.val
    (constructedWSelectionCandidateToRanking1 winner)
    (constructedWSelectionPairLoserToRanking1 pair)

/-- Actual K-approval down-probabilities for the four static cutoffs on `Ranking 1`. -/
def constructedWSelectionRanking1StaticKDown
    (K : Fin 4) (pair : ConstructedWSelectionPair) : ℝ :=
  AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb
    constructedWSelectionRanking1Law K.val
    (constructedWSelectionCandidateToRanking1 winner)
    (constructedWSelectionPairLoserToRanking1 pair)

/-- Actual pairwise approval rates for the four static cutoffs on `Ranking 1`. -/
def constructedWSelectionRanking1StaticKRate
    (K : Fin 4) (pair : ConstructedWSelectionPair) : ℝ :=
  approvalPairwiseRate
    (constructedWSelectionRanking1StaticKUp K pair)
    (constructedWSelectionRanking1StaticKDown K pair)

theorem constructedWSelectionRanking1StaticKOutcomeRate_le_staticBaseRate
    (K : Fin 4) :
    finiteOutcomeLearningRate
        (constructedWSelectionRanking1StaticKRate K) ≤
      constructedWSelectionStaticBaseRate := by
  fin_cases K
  · have hrate :
        constructedWSelectionRanking1StaticKRate 0 = fun _ => 0 := by
      funext pair
      simp [constructedWSelectionRanking1StaticKRate,
        constructedWSelectionRanking1StaticKUp,
        constructedWSelectionRanking1StaticKDown,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb,
        approvalPairwiseRate_zero_zero]
    change finiteOutcomeLearningRate
        (constructedWSelectionRanking1StaticKRate (0 : Fin 4)) ≤
      constructedWSelectionStaticBaseRate
    rw [hrate, finiteOutcomeLearningRate_const]
    exact le_of_lt constructedWSelectionStaticBaseRate_pos
  · have hrate :
        constructedWSelectionRanking1StaticKRate 1 =
          constructedWSelectionK1Rate := by
      funext pair
      simp [constructedWSelectionRanking1StaticKRate,
        constructedWSelectionRanking1StaticKUp,
        constructedWSelectionRanking1StaticKDown,
        constructedWSelectionRanking1K1UpProb_eq,
        constructedWSelectionRanking1K1DownProb_eq,
        constructedWSelectionK1Rate]
    change finiteOutcomeLearningRate
        (constructedWSelectionRanking1StaticKRate (1 : Fin 4)) ≤
      constructedWSelectionStaticBaseRate
    rw [hrate]
    exact le_max_left _ _
  · have hrate :
        constructedWSelectionRanking1StaticKRate 2 =
          constructedWSelectionK2Rate := by
      funext pair
      simp [constructedWSelectionRanking1StaticKRate,
        constructedWSelectionRanking1StaticKUp,
        constructedWSelectionRanking1StaticKDown,
        constructedWSelectionRanking1K2UpProb_eq,
        constructedWSelectionRanking1K2DownProb_eq,
        constructedWSelectionK2Rate]
    change finiteOutcomeLearningRate
        (constructedWSelectionRanking1StaticKRate (2 : Fin 4)) ≤
      constructedWSelectionStaticBaseRate
    rw [hrate]
    exact le_max_right _ _
  · have hrate :
        constructedWSelectionRanking1StaticKRate 3 = fun _ => 0 := by
      funext pair
      simp [constructedWSelectionRanking1StaticKRate,
        constructedWSelectionRanking1StaticKUp,
        constructedWSelectionRanking1StaticKDown,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairUpProb,
        AppliedModelingLib.SocialChoice.Ranking.kApprovalPairDownProb,
        approvalPairwiseRate_zero_zero]
    change finiteOutcomeLearningRate
        (constructedWSelectionRanking1StaticKRate (3 : Fin 4)) ≤
      constructedWSelectionStaticBaseRate
    rw [hrate, finiteOutcomeLearningRate_const]
    exact le_of_lt constructedWSelectionStaticBaseRate_pos

/--
Actual finite `max_K` statement for the constructed three-candidate ranking
law: the 50/50 randomized approval rule beats every static K-approval cutoff
`K = 0, 1, 2, 3`.
-/
theorem constructedWSelectionRanking1RandomizedApproval_improves_all_staticK :
    (Finset.univ : Finset (Fin 4)).sup' finiteUnivNonempty
        (fun K =>
          finiteOutcomeLearningRate
            (constructedWSelectionRanking1StaticKRate K)) <
      finiteOutcomeLearningRate constructedWSelectionRandomizedRate := by
  have hbase_lt :
      constructedWSelectionStaticBaseRate <
        finiteOutcomeLearningRate constructedWSelectionRandomizedRate := by
    simpa [constructedWSelectionStaticBaseRate] using
      constructedWSelectionRandomizedApproval_improves_staticK1_staticK2
  exact
    randomizedOutcomeRate_strictly_improves_all_static_of_bound
      constructedWSelectionRanking1StaticKRate
      constructedWSelectionRandomizedRate
      constructedWSelectionRanking1StaticKOutcomeRate_le_staticBaseRate
      (fun pair =>
        hbase_lt.trans_le
          (finiteOutcomeLearningRate_le constructedWSelectionRandomizedRate pair))

theorem constructedWSelectionRanking1ActualRandomizedApproval_improves_all_staticK :
    (Finset.univ : Finset (Fin 4)).sup' finiteUnivNonempty
        (fun K =>
          finiteOutcomeLearningRate
            (constructedWSelectionRanking1StaticKRate K)) <
      finiteOutcomeLearningRate
        constructedWSelectionRanking1RandomizedApprovalRate := by
  have hrate :
      constructedWSelectionRanking1RandomizedApprovalRate =
        constructedWSelectionRandomizedRate := by
    funext pair
    exact constructedWSelectionRanking1RandomizedApprovalRate_eq pair
  rw [hrate]
  exact constructedWSelectionRanking1RandomizedApproval_improves_all_staticK

/--
Finite source-facing package for the constructed three-candidate law: the
explicit ranking law satisfies strict prefix dominance for W-selection, and the
50/50 randomized approval rule strictly beats every static K-approval cutoff.
-/
theorem constructedWSelectionRanking1_designInvariant_and_randomizedApproval_improves_all_staticK :
    StrictTopPrefixDominanceOn
        constructedWSelectionRanking1TopPrefixProb
        constructedWSelectionCrossTier ∧
      (Finset.univ : Finset (Fin 4)).sup' finiteUnivNonempty
          (fun K =>
            finiteOutcomeLearningRate
              (constructedWSelectionRanking1StaticKRate K)) <
        finiteOutcomeLearningRate
          constructedWSelectionRanking1RandomizedApprovalRate :=
  ⟨constructedWSelectionRanking1Law_strictTopPrefixDominanceOn,
    constructedWSelectionRanking1ActualRandomizedApproval_improves_all_staticK⟩

theorem constructedWSelectionRanking1_consistency_and_actualRandomizedApproval_improves_all_staticK :
    (∀ diff : RankingProperPrefixCut 1 → ℝ,
      ReasonablePrefixWeights diff →
        Filter.Tendsto
          (scoreTopSelectionErrorProb constructedWSelectionRanking1Law
            (rankingPrefixScore diff)
            constructedWSelectionRanking1WinnerSet
            (fun _voters sample =>
              scoreTopSelectedSetOfCard
                (iidSampleCandidateScore (rankingPrefixScore diff) sample)
                constructedWSelectionRanking1WinnerSet))
          Filter.atTop (nhds 0)) ∧
      (Finset.univ : Finset (Fin 4)).sup' finiteUnivNonempty
          (fun K =>
            finiteOutcomeLearningRate
              (constructedWSelectionRanking1StaticKRate K)) <
        finiteOutcomeLearningRate
          constructedWSelectionRanking1RandomizedApprovalRate :=
  ⟨constructedWSelectionRanking1Law_allReasonablePrefixScoreConsistency,
    constructedWSelectionRanking1ActualRandomizedApproval_improves_all_staticK⟩

def constructedWSelectionStaticCategoryUp
    (oneSidedUp nearTieBase nearTieEps oneSidedBoundaryUp : ℝ) :
    ConstructedWSelectionStaticCategory → ConstructedWSelectionPair → ℝ
  | ConstructedWSelectionStaticCategory.sourceK, pair =>
      constructedWSelectionK1Up pair
  | ConstructedWSelectionStaticCategory.sourceL, pair =>
      constructedWSelectionK2Up pair
  | ConstructedWSelectionStaticCategory.oneSidedSmall, _ =>
      oneSidedUp
  | ConstructedWSelectionStaticCategory.nearTie, _ =>
      nearTieBase + nearTieEps
  | ConstructedWSelectionStaticCategory.oneSidedBoundary, _ =>
      oneSidedBoundaryUp

def constructedWSelectionStaticCategoryDown
    (oneSidedUp nearTieBase nearTieEps oneSidedBoundaryUp : ℝ) :
    ConstructedWSelectionStaticCategory → ConstructedWSelectionPair → ℝ
  | ConstructedWSelectionStaticCategory.sourceK, pair =>
      constructedWSelectionK1Down pair
  | ConstructedWSelectionStaticCategory.sourceL, pair =>
      constructedWSelectionK2Down pair
  | ConstructedWSelectionStaticCategory.oneSidedSmall, _ =>
      0
  | ConstructedWSelectionStaticCategory.nearTie, _ =>
      nearTieBase
  | ConstructedWSelectionStaticCategory.oneSidedBoundary, _ =>
      0

/--
Source-shaped `max_K` package for the constructed W-selection proof.  Once the
three K′ side-case buckets have rates bounded by the K/L base rate, the
randomized approval rule strictly beats the best static category.
-/
theorem constructedWSelectionRandomizedApproval_improves_static_categories
    {oneSidedUp nearTieBase nearTieEps oneSidedBoundaryUp : ℝ}
    (hOneSided :
      approvalPairwiseRate oneSidedUp 0 ≤
        constructedWSelectionStaticBaseRate)
    (hNearTie :
      approvalPairwiseRate (nearTieBase + nearTieEps) nearTieBase ≤
        constructedWSelectionStaticBaseRate)
    (hOneSidedBoundary :
      approvalPairwiseRate oneSidedBoundaryUp 0 ≤
        constructedWSelectionStaticBaseRate) :
    (Finset.univ : Finset ConstructedWSelectionStaticCategory).sup'
        finiteUnivNonempty
        (fun rule =>
          finiteOutcomeLearningRate
            (fun pair =>
              approvalPairwiseRate
                (constructedWSelectionStaticCategoryUp
                  oneSidedUp nearTieBase nearTieEps oneSidedBoundaryUp
                  rule pair)
                (constructedWSelectionStaticCategoryDown
                  oneSidedUp nearTieBase nearTieEps oneSidedBoundaryUp
                  rule pair))) <
      finiteOutcomeLearningRate constructedWSelectionRandomizedRate := by
  refine randomizedApproval_outcomeRate_strictly_improves_all_static_of_bound
    (constructedWSelectionStaticCategoryUp
      oneSidedUp nearTieBase nearTieEps oneSidedBoundaryUp)
    (constructedWSelectionStaticCategoryDown
      oneSidedUp nearTieBase nearTieEps oneSidedBoundaryUp)
    constructedWSelectionRandomizedUp
    constructedWSelectionRandomizedDown
    (baseRate := constructedWSelectionStaticBaseRate) ?_ ?_
  · intro rule
    cases rule with
    | sourceK =>
        change finiteOutcomeLearningRate constructedWSelectionK1Rate ≤
          constructedWSelectionStaticBaseRate
        exact le_max_left _ _
    | sourceL =>
        change finiteOutcomeLearningRate constructedWSelectionK2Rate ≤
          constructedWSelectionStaticBaseRate
        exact le_max_right _ _
    | oneSidedSmall =>
        exact
          (finiteOutcomeLearningRate_le
            (fun _ : ConstructedWSelectionPair =>
              approvalPairwiseRate oneSidedUp 0)
            ConstructedWSelectionPair.hi).trans hOneSided
    | nearTie =>
        exact
          (finiteOutcomeLearningRate_le
            (fun _ : ConstructedWSelectionPair =>
              approvalPairwiseRate (nearTieBase + nearTieEps) nearTieBase)
            ConstructedWSelectionPair.hi).trans hNearTie
    | oneSidedBoundary =>
        exact
          (finiteOutcomeLearningRate_le
            (fun _ : ConstructedWSelectionPair =>
              approvalPairwiseRate oneSidedBoundaryUp 0)
            ConstructedWSelectionPair.hi).trans hOneSidedBoundary
  · have hbase_lt :
        constructedWSelectionStaticBaseRate <
          finiteOutcomeLearningRate constructedWSelectionRandomizedRate := by
      simpa [constructedWSelectionStaticBaseRate] using
        constructedWSelectionRandomizedApproval_improves_staticK1_staticK2
    intro pair
    exact hbase_lt.trans_le
      (by
        simpa [constructedWSelectionRandomizedRate] using
          finiteOutcomeLearningRate_le constructedWSelectionRandomizedRate pair)

/--
Source-shaped variant for the `K' = L + 1` side case: the one-sided-boundary
static category is bounded by the K/L base rate when the source base inequality
`base(refUp, refDown) < 1 - pUp` holds for a reference rate already below the
constructed K/L base.
-/
theorem constructedWSelectionRandomizedApproval_improves_static_categories_of_boundary_base
    {oneSidedUp nearTieBase nearTieEps oneSidedBoundaryUp refUp refDown : ℝ}
    (hOneSided :
      approvalPairwiseRate oneSidedUp 0 ≤
        constructedWSelectionStaticBaseRate)
    (hNearTie :
      approvalPairwiseRate (nearTieBase + nearTieEps) nearTieBase ≤
        constructedWSelectionStaticBaseRate)
    (href_base_pos : 0 < approvalPairwiseBase refUp refDown)
    (href_rate_le_base :
      approvalPairwiseRate refUp refDown ≤
        constructedWSelectionStaticBaseRate)
    (hboundary_base_lt :
      approvalPairwiseBase refUp refDown < 1 - oneSidedBoundaryUp) :
    (Finset.univ : Finset ConstructedWSelectionStaticCategory).sup'
        finiteUnivNonempty
        (fun rule =>
          finiteOutcomeLearningRate
            (fun pair =>
              approvalPairwiseRate
                (constructedWSelectionStaticCategoryUp
                  oneSidedUp nearTieBase nearTieEps oneSidedBoundaryUp
                  rule pair)
                (constructedWSelectionStaticCategoryDown
                  oneSidedUp nearTieBase nearTieEps oneSidedBoundaryUp
                  rule pair))) <
      finiteOutcomeLearningRate constructedWSelectionRandomizedRate := by
  have hboundary_rate_le_base :
      approvalPairwiseRate oneSidedBoundaryUp 0 ≤
        constructedWSelectionStaticBaseRate :=
    (le_of_lt
      (approvalPairwiseRate_zero_down_lt_of_base_lt_one_sub_up
        href_base_pos hboundary_base_lt)).trans href_rate_le_base
  exact
    constructedWSelectionRandomizedApproval_improves_static_categories
      hOneSided hNearTie hboundary_rate_le_base

/--
There are concrete positive side-case parameters small enough for the
constructed W-selection static-category package: the randomized approval rule
strictly beats the best finite static category after choosing small one-sided
and near-tie K′ rates.
-/
theorem constructedWSelectionRandomizedApproval_exists_static_categories_maxK :
    ∃ oneSidedUp nearTieEps oneSidedBoundaryUp : ℝ,
      0 < oneSidedUp ∧ oneSidedUp < 1 ∧
        0 < nearTieEps ∧ nearTieEps < 1 ∧
          0 < oneSidedBoundaryUp ∧ oneSidedBoundaryUp < 1 ∧
            (Finset.univ : Finset ConstructedWSelectionStaticCategory).sup'
                finiteUnivNonempty
                (fun rule =>
                  finiteOutcomeLearningRate
                    (fun pair =>
                      approvalPairwiseRate
                        (constructedWSelectionStaticCategoryUp
                          oneSidedUp (constructedWSelectionProb 27)
                          nearTieEps oneSidedBoundaryUp rule pair)
                        (constructedWSelectionStaticCategoryDown
                          oneSidedUp (constructedWSelectionProb 27)
                          nearTieEps oneSidedBoundaryUp rule pair))) <
              finiteOutcomeLearningRate constructedWSelectionRandomizedRate := by
  rcases exists_pos_up_zero_down_rate_lt
      constructedWSelectionStaticBaseRate_pos with
    ⟨oneSidedUp, hone_pos, hone_lt_one, hone_rate_lt⟩
  rcases exists_pos_shift_rate_lt
      (a := constructedWSelectionProb 27)
      (by norm_num [constructedWSelectionProb])
      constructedWSelectionStaticBaseRate_pos with
    ⟨nearTieEps, hnear_pos, hnear_lt_one, hnear_rate_lt⟩
  rcases exists_pos_up_zero_down_rate_lt
      constructedWSelectionStaticBaseRate_pos with
    ⟨oneSidedBoundaryUp, hboundary_pos, hboundary_lt_one,
      hboundary_rate_lt⟩
  refine
    ⟨oneSidedUp, nearTieEps, oneSidedBoundaryUp,
      hone_pos, hone_lt_one, hnear_pos, hnear_lt_one,
      hboundary_pos, hboundary_lt_one, ?_⟩
  exact
    constructedWSelectionRandomizedApproval_improves_static_categories
      (le_of_lt hone_rate_lt)
      (le_of_lt hnear_rate_lt)
      (le_of_lt hboundary_rate_lt)

/--
Constructive source-shaped package for
`lem:randomizebetterapproval_Wselection`: the exact finite table satisfies
strict prefix dominance for W-selection, and after choosing small side-case
parameters the randomized approval rule strictly beats the best finite static
category in the constructed `max_K` family.
-/
theorem constructedWSelection_designInvariant_and_randomizedApproval_improves_static_categories :
    StrictTopPrefixDominanceOn
        constructedWSelectionTopPrefixProb
        constructedWSelectionCrossTier ∧
      ∃ oneSidedUp nearTieEps oneSidedBoundaryUp : ℝ,
        0 < oneSidedUp ∧ oneSidedUp < 1 ∧
          0 < nearTieEps ∧ nearTieEps < 1 ∧
            0 < oneSidedBoundaryUp ∧ oneSidedBoundaryUp < 1 ∧
              (Finset.univ : Finset ConstructedWSelectionStaticCategory).sup'
                  finiteUnivNonempty
                  (fun rule =>
                    finiteOutcomeLearningRate
                      (fun pair =>
                        approvalPairwiseRate
                          (constructedWSelectionStaticCategoryUp
                            oneSidedUp (constructedWSelectionProb 27)
                            nearTieEps oneSidedBoundaryUp rule pair)
                          (constructedWSelectionStaticCategoryDown
                            oneSidedUp (constructedWSelectionProb 27)
                            nearTieEps oneSidedBoundaryUp rule pair))) <
                finiteOutcomeLearningRate constructedWSelectionRandomizedRate :=
  ⟨constructedWSelection_strictTopPrefixDominanceOn,
    constructedWSelectionRandomizedApproval_exists_static_categories_maxK⟩

/--
Concrete feasibility witness for the source proof's W-selection constants.
This checks the numeric side conditions stated after the constructed table.
-/
theorem constructedWSelection_source_constants_feasible :
    ∃ ε a T2 T1 Q : ℝ,
      0 < ε ∧ ε < a ∧ a < T2 / 2 ∧ T2 / 2 < T2 ∧ T2 < T1 ∧
        T1 + 2 * T2 + a = 1 ∧
          1 - ε > approvalPairwiseBase T1 T2 ∧
            (T1 + 2 * T2 - 3 * a - ε) / Q < T1 + 3 * a ∧
              3 * a > T1 / Q ∧
                2 < Q ∧
                  1 - T2 + a - ε > approvalPairwiseBase T1 T2 := by
  refine ⟨(1 : ℝ) / 100, (1 : ℝ) / 25, (1 : ℝ) / 10,
    (19 : ℝ) / 25, 10, ?_⟩
  have hsqrt :
      Real.sqrt (((19 : ℝ) / 25) * ((1 : ℝ) / 10)) < (3 : ℝ) / 10 := by
    exact
      (Real.sqrt_lt
        (by norm_num : 0 ≤ ((19 : ℝ) / 25) * ((1 : ℝ) / 10))
        (by norm_num : 0 ≤ (3 : ℝ) / 10)).2
        (by norm_num)
  have hbase_lt :
      approvalPairwiseBase ((19 : ℝ) / 25) ((1 : ℝ) / 10) <
        (3 : ℝ) / 4 := by
    unfold approvalPairwiseBase
    nlinarith
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · linarith
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · linarith

/--
Paper theorem `lem:randomizebetterapproval_Wselection`, constructive finite
core: the same exact table satisfies strict prefix dominance for W-selection
and has a randomized approval rule with strictly larger finite learning rate
than the two static approval rules that determine the construction.
-/
theorem constructedWSelection_designInvariant_and_randomizedApproval_improves :
    StrictTopPrefixDominanceOn
        constructedWSelectionTopPrefixProb
        constructedWSelectionCrossTier ∧
      max
          (finiteOutcomeLearningRate constructedWSelectionK1Rate)
          (finiteOutcomeLearningRate constructedWSelectionK2Rate) <
        finiteOutcomeLearningRate constructedWSelectionRandomizedRate :=
  ⟨constructedWSelection_strictTopPrefixDominanceOn,
    constructedWSelectionRandomizedApproval_improves_staticK1_staticK2⟩

/-! ## Mallows high-noise approval example -/

/-- High-noise parameter from the paper's `M = 4`, `W = 3` example. -/
def mallowsHighNoisePhi : ℝ := (4 : ℝ) / 5

/-- Normalizing denominator for inserting item 3 in the source example. -/
def mallowsW3N3 (phi : ℝ) : ℝ := 1 + phi + phi ^ 2

/-- Normalizing denominator for inserting item 4 in the source example. -/
def mallowsW3N4 (phi : ℝ) : ℝ := 1 + phi + phi ^ 2 + phi ^ 3

/-- The item-3 repeated-insertion normalizer is positive for positive noise. -/
theorem mallowsW3N3_pos_of_pos {phi : ℝ} (hphi : 0 < phi) :
    0 < mallowsW3N3 phi := by
  unfold mallowsW3N3
  have hphi2 : 0 < phi ^ 2 := sq_pos_of_pos hphi
  nlinarith

/-- The item-4 repeated-insertion normalizer is positive for positive noise. -/
theorem mallowsW3N4_pos_of_pos {phi : ℝ} (hphi : 0 < phi) :
    0 < mallowsW3N4 phi := by
  unfold mallowsW3N4
  have hphi2 : 0 < phi ^ 2 := sq_pos_of_pos hphi
  have hphi3 : 0 < phi ^ 3 := pow_pos hphi 3
  nlinarith

/-- `K = 1` up-event formula for source pair `(1,4)`. -/
def mallowsW3K1Up0 (phi : ℝ) : ℝ := 1 / mallowsW3N4 phi

/-- `K = 1` up-event formula for source pair `(2,4)`. -/
def mallowsW3K1Up1 (phi : ℝ) : ℝ := phi / mallowsW3N4 phi

/-- `K = 1` up-event formula for source pair `(3,4)`. -/
def mallowsW3K1Up (phi : ℝ) : ℝ := phi ^ 2 / mallowsW3N4 phi

/-- `K = 1` down-event formula for any source pair `(w,4)`. -/
def mallowsW3K1Down (phi : ℝ) : ℝ := phi ^ 3 / mallowsW3N4 phi

/-- Source formula for `t^3_34(3)` in the `M = 4`, `W = 3` example. -/
def mallowsW3K3Up (phi : ℝ) : ℝ := 1 / mallowsW3N4 phi

/-- Source formula for `t^4_34(3)` in the `M = 4`, `W = 3` example. -/
def mallowsW3K3Down (phi : ℝ) : ℝ := phi / mallowsW3N4 phi

/-- Source formula for `t^3_34(2)` in the `M = 4`, `W = 3` example. -/
def mallowsW3K2Up (phi : ℝ) : ℝ :=
  (phi + 2 * phi ^ 2 + phi ^ 3) / (mallowsW3N3 phi * mallowsW3N4 phi)

/-- Source formula for `t^4_34(2)` in the `M = 4`, `W = 3` example. -/
def mallowsW3K2Down (phi : ℝ) : ℝ :=
  (phi ^ 2 + 2 * phi ^ 3 + phi ^ 4) /
    (mallowsW3N3 phi * mallowsW3N4 phi)

/-- `K = 3` down-event formula for source pair `(1,4)`. -/
def mallowsW3K3Down0 (phi : ℝ) : ℝ := phi ^ 3 / mallowsW3N4 phi

/-- `K = 3` down-event formula for source pair `(2,4)`. -/
def mallowsW3K3Down1 (phi : ℝ) : ℝ := phi ^ 2 / mallowsW3N4 phi

/-- `K = 2` up-event formula for source pair `(1,4)`. -/
def mallowsW3K2Up0 (phi : ℝ) : ℝ :=
  (1 + 2 * phi + phi ^ 2) / (mallowsW3N3 phi * mallowsW3N4 phi)

/-- `K = 2` down-event formula for source pair `(1,4)`. -/
def mallowsW3K2Down0 (phi : ℝ) : ℝ :=
  (phi ^ 3 + 2 * phi ^ 4 + phi ^ 5) /
    (mallowsW3N3 phi * mallowsW3N4 phi)

/-- `K = 2` up-event formula for source pair `(2,4)`. -/
def mallowsW3K2Up1 (phi : ℝ) : ℝ :=
  (1 + phi + phi ^ 2 + phi ^ 3) /
    (mallowsW3N3 phi * mallowsW3N4 phi)

/-- `K = 2` down-event formula for source pair `(2,4)`. -/
def mallowsW3K2Down1 (phi : ℝ) : ℝ :=
  (phi ^ 2 + phi ^ 3 + phi ^ 4 + phi ^ 5) /
    (mallowsW3N3 phi * mallowsW3N4 phi)

theorem mallowsHighNoise_same_ratio_coef_pos :
    0 < 1 + mallowsHighNoisePhi - 2 * Real.sqrt mallowsHighNoisePhi := by
  have hnonneg : 0 ≤ mallowsHighNoisePhi := by
    norm_num [mallowsHighNoisePhi]
  have hsq :
      (Real.sqrt mallowsHighNoisePhi - 1) ^ 2 =
        1 + mallowsHighNoisePhi - 2 * Real.sqrt mallowsHighNoisePhi := by
    rw [sub_sq, Real.sq_sqrt hnonneg]
    ring
  have hne : Real.sqrt mallowsHighNoisePhi - 1 ≠ 0 := by
    intro hzero
    have hsqrt_eq : Real.sqrt mallowsHighNoisePhi = 1 := by
      linarith
    have hsq_eq :
        (Real.sqrt mallowsHighNoisePhi) ^ 2 = (1 : ℝ) ^ 2 := by
      rw [hsqrt_eq]
    rw [Real.sq_sqrt hnonneg] at hsq_eq
    norm_num [mallowsHighNoisePhi] at hsq_eq
  have hpos :
      0 < (Real.sqrt mallowsHighNoisePhi - 1) ^ 2 :=
    sq_pos_of_ne_zero hne
  rwa [hsq] at hpos

theorem mallowsHighNoiseW3K1_base_pos :
    0 < approvalPairwiseBase
      (mallowsW3K1Up mallowsHighNoisePhi)
      (mallowsW3K1Down mallowsHighNoisePhi) := by
  have hup : 0 < mallowsW3K1Up mallowsHighNoisePhi := by
    norm_num [mallowsW3K1Up, mallowsHighNoisePhi, mallowsW3N4]
  have hdown : 0 < mallowsW3K1Down mallowsHighNoisePhi := by
    norm_num [mallowsW3K1Down, mallowsHighNoisePhi, mallowsW3N4]
  have hsum :
      mallowsW3K1Up mallowsHighNoisePhi +
          mallowsW3K1Down mallowsHighNoisePhi ≤ 1 := by
    norm_num [mallowsW3K1Up, mallowsW3K1Down, mallowsHighNoisePhi,
      mallowsW3N4]
  simpa [approvalPairwiseBase] using
    ternaryGap_closedExpr_pos hup hdown hsum

theorem mallowsHighNoiseW3K2_base_pos :
    0 < approvalPairwiseBase
      (mallowsW3K2Up mallowsHighNoisePhi)
      (mallowsW3K2Down mallowsHighNoisePhi) := by
  have hup : 0 < mallowsW3K2Up mallowsHighNoisePhi := by
    norm_num [mallowsW3K2Up, mallowsHighNoisePhi, mallowsW3N3, mallowsW3N4]
  have hdown : 0 < mallowsW3K2Down mallowsHighNoisePhi := by
    norm_num [mallowsW3K2Down, mallowsHighNoisePhi, mallowsW3N3, mallowsW3N4]
  have hsum :
      mallowsW3K2Up mallowsHighNoisePhi +
          mallowsW3K2Down mallowsHighNoisePhi ≤ 1 := by
    norm_num [mallowsW3K2Up, mallowsW3K2Down, mallowsHighNoisePhi,
      mallowsW3N3, mallowsW3N4]
  simpa [approvalPairwiseBase] using
    ternaryGap_closedExpr_pos hup hdown hsum

theorem mallowsHighNoiseW3K3_base_pos :
    0 < approvalPairwiseBase
      (mallowsW3K3Up mallowsHighNoisePhi)
      (mallowsW3K3Down mallowsHighNoisePhi) := by
  have hup : 0 < mallowsW3K3Up mallowsHighNoisePhi := by
    norm_num [mallowsW3K3Up, mallowsHighNoisePhi, mallowsW3N4]
  have hdown : 0 < mallowsW3K3Down mallowsHighNoisePhi := by
    norm_num [mallowsW3K3Down, mallowsHighNoisePhi, mallowsW3N4]
  have hsum :
      mallowsW3K3Up mallowsHighNoisePhi +
          mallowsW3K3Down mallowsHighNoisePhi ≤ 1 := by
    norm_num [mallowsW3K3Up, mallowsW3K3Down, mallowsHighNoisePhi,
      mallowsW3N4]
  simpa [approvalPairwiseBase] using
    ternaryGap_closedExpr_pos hup hdown hsum

theorem mallowsW3_same_ratio_coef_pos_of_lt_one
    {phi : ℝ} (hphi_nonneg : 0 ≤ phi) (hphi_lt : phi < 1) :
    0 < 1 + phi - 2 * Real.sqrt phi := by
  have hsq :
      (Real.sqrt phi - 1) ^ 2 =
        1 + phi - 2 * Real.sqrt phi := by
    rw [sub_sq, Real.sq_sqrt hphi_nonneg]
    ring
  have hne : Real.sqrt phi - 1 ≠ 0 := by
    intro hzero
    have hsqrt_eq : Real.sqrt phi = 1 := by
      linarith
    have hsq_eq :
        (Real.sqrt phi) ^ 2 = (1 : ℝ) ^ 2 := by
      rw [hsqrt_eq]
    rw [Real.sq_sqrt hphi_nonneg] at hsq_eq
    nlinarith
  have hpos :
      0 < (Real.sqrt phi - 1) ^ 2 :=
    sq_pos_of_ne_zero hne
  rwa [hsq] at hpos

theorem mallowsW3K1_boundary_base_pos_of_phi_pos
    {phi : ℝ} (hphi : 0 < phi) :
    0 < approvalPairwiseBase (mallowsW3K1Up phi) (mallowsW3K1Down phi) := by
  have hN4 : 0 < mallowsW3N4 phi := mallowsW3N4_pos_of_pos hphi
  exact approvalPairwiseBase_pos_of_pos_sum_le
    (by unfold mallowsW3K1Up; positivity)
    (by unfold mallowsW3K1Down; positivity)
    (by
      unfold mallowsW3K1Up mallowsW3K1Down mallowsW3N4
      field_simp [hN4.ne']
      ring_nf
      nlinarith [hphi])

theorem mallowsW3K2_boundary_base_pos_of_phi_pos
    {phi : ℝ} (hphi : 0 < phi) :
    0 < approvalPairwiseBase (mallowsW3K2Up phi) (mallowsW3K2Down phi) := by
  have hN3 : 0 < mallowsW3N3 phi := mallowsW3N3_pos_of_pos hphi
  have hN4 : 0 < mallowsW3N4 phi := mallowsW3N4_pos_of_pos hphi
  have hden : 0 < mallowsW3N3 phi * mallowsW3N4 phi := mul_pos hN3 hN4
  exact approvalPairwiseBase_pos_of_pos_sum_le
    (by
      unfold mallowsW3K2Up
      have hnum : 0 < phi + 2 * phi ^ 2 + phi ^ 3 := by
        have hphi2 : 0 < phi ^ 2 := sq_pos_of_pos hphi
        have hphi3 : 0 < phi ^ 3 := pow_pos hphi 3
        nlinarith
      positivity)
    (by
      unfold mallowsW3K2Down
      have hnum : 0 < phi ^ 2 + 2 * phi ^ 3 + phi ^ 4 := by
        have hphi2 : 0 < phi ^ 2 := sq_pos_of_pos hphi
        have hphi3 : 0 < phi ^ 3 := pow_pos hphi 3
        have hphi4 : 0 < phi ^ 4 := pow_pos hphi 4
        nlinarith
      positivity)
    (by
      unfold mallowsW3K2Up mallowsW3K2Down mallowsW3N3 mallowsW3N4
      field_simp [hden.ne']
      ring_nf
      have hphi4 : 0 ≤ phi ^ 4 := pow_nonneg hphi.le 4
      have hphi5 : 0 ≤ phi ^ 5 := pow_nonneg hphi.le 5
      nlinarith [hphi, hphi4, hphi5])

theorem mallowsW3K3_boundary_base_pos_of_phi_pos
    {phi : ℝ} (hphi : 0 < phi) :
    0 < approvalPairwiseBase (mallowsW3K3Up phi) (mallowsW3K3Down phi) := by
  have hN4 : 0 < mallowsW3N4 phi := mallowsW3N4_pos_of_pos hphi
  exact approvalPairwiseBase_pos_of_pos_sum_le
    (by unfold mallowsW3K3Up; positivity)
    (by unfold mallowsW3K3Down; positivity)
    (by
      unfold mallowsW3K3Up mallowsW3K3Down mallowsW3N4
      field_simp [hN4.ne']
      ring_nf
      have hphi2 : 0 ≤ phi ^ 2 := sq_nonneg phi
      have hphi3 : 0 ≤ phi ^ 3 := pow_nonneg hphi.le 3
      nlinarith [hphi2, hphi3])

theorem mallowsW3K2_base_lt_K1_base_of_q_lt_one
    {phi : ℝ} (hphi : 0 < phi) (hphi_lt : phi < 1) :
    approvalPairwiseBase (mallowsW3K2Up phi) (mallowsW3K2Down phi) <
      approvalPairwiseBase (mallowsW3K1Up phi) (mallowsW3K1Down phi) := by
  have hphi_nonneg : 0 ≤ phi := hphi.le
  have hN3 : 0 < mallowsW3N3 phi := mallowsW3N3_pos_of_pos hphi
  have hN4 : 0 < mallowsW3N4 phi := mallowsW3N4_pos_of_pos hphi
  have hden : 0 < mallowsW3N3 phi * mallowsW3N4 phi := mul_pos hN3 hN4
  have hk1 :
      mallowsW3K1Down phi = phi * mallowsW3K1Up phi := by
    simp [mallowsW3K1Down, mallowsW3K1Up]
    ring
  have hk2 :
      mallowsW3K2Down phi = phi * mallowsW3K2Up phi := by
    simp [mallowsW3K2Down, mallowsW3K2Up]
    ring
  have hup1_nonneg : 0 ≤ mallowsW3K1Up phi := by
    unfold mallowsW3K1Up
    positivity
  have hup2_nonneg : 0 ≤ mallowsW3K2Up phi := by
    unfold mallowsW3K2Up
    have hnum : 0 ≤ phi + 2 * phi ^ 2 + phi ^ 3 := by
      have hphi2 : 0 ≤ phi ^ 2 := sq_nonneg phi
      have hphi3 : 0 ≤ phi ^ 3 := pow_nonneg hphi.le 3
      nlinarith [hphi.le, hphi2, hphi3]
    positivity
  have hup_lt :
      mallowsW3K1Up phi < mallowsW3K2Up phi := by
    unfold mallowsW3K1Up mallowsW3K2Up mallowsW3N3 mallowsW3N4
    field_simp [hN3.ne', hN4.ne', hden.ne']
    ring_nf
    have hphi3_lt_one : phi ^ 3 < 1 := by
      have hphi2_pos : 0 < phi ^ 2 := sq_pos_of_pos hphi
      have hmul := mul_lt_mul_of_pos_left hphi_lt hphi2_pos
      nlinarith
    have hphi4_lt_phi : phi ^ 4 < phi := by
      have hmul := mul_lt_mul_of_pos_left hphi3_lt_one hphi
      nlinarith
    nlinarith [hphi, hphi4_lt_phi]
  rw [hk1, hk2]
  exact approvalPairwiseBase_same_ratio_strictAnti hphi_nonneg
    (mallowsW3_same_ratio_coef_pos_of_lt_one hphi_nonneg hphi_lt)
    hup2_nonneg hup1_nonneg hup_lt

theorem mallowsW3K2_base_lt_K3_base_of_q_high_noise
    {phi : ℝ} (hphi : 0 < phi) (hphi_lt : phi < 1)
    (hhigh : 1 < phi ^ 2 + phi ^ 3) :
    approvalPairwiseBase (mallowsW3K2Up phi) (mallowsW3K2Down phi) <
      approvalPairwiseBase (mallowsW3K3Up phi) (mallowsW3K3Down phi) := by
  have hphi_nonneg : 0 ≤ phi := hphi.le
  have hN3 : 0 < mallowsW3N3 phi := mallowsW3N3_pos_of_pos hphi
  have hN4 : 0 < mallowsW3N4 phi := mallowsW3N4_pos_of_pos hphi
  have hden : 0 < mallowsW3N3 phi * mallowsW3N4 phi := mul_pos hN3 hN4
  have hk2 :
      mallowsW3K2Down phi = phi * mallowsW3K2Up phi := by
    simp [mallowsW3K2Down, mallowsW3K2Up]
    ring
  have hk3 :
      mallowsW3K3Down phi = phi * mallowsW3K3Up phi := by
    simp [mallowsW3K3Down, mallowsW3K3Up]
    ring
  have hup2_nonneg : 0 ≤ mallowsW3K2Up phi := by
    unfold mallowsW3K2Up
    have hnum : 0 ≤ phi + 2 * phi ^ 2 + phi ^ 3 := by
      have hphi2 : 0 ≤ phi ^ 2 := sq_nonneg phi
      have hphi3 : 0 ≤ phi ^ 3 := pow_nonneg hphi.le 3
      nlinarith [hphi.le, hphi2, hphi3]
    positivity
  have hup3_nonneg : 0 ≤ mallowsW3K3Up phi := by
    unfold mallowsW3K3Up
    positivity
  have hup_lt :
      mallowsW3K3Up phi < mallowsW3K2Up phi := by
    unfold mallowsW3K3Up mallowsW3K2Up mallowsW3N3 mallowsW3N4
    field_simp [hN3.ne', hN4.ne', hden.ne']
    ring_nf
    nlinarith [hhigh]
  rw [hk2, hk3]
  exact approvalPairwiseBase_same_ratio_strictAnti hphi_nonneg
    (mallowsW3_same_ratio_coef_pos_of_lt_one hphi_nonneg hphi_lt)
    hup2_nonneg hup3_nonneg hup_lt

theorem mallowsHighNoiseW3K2_base_lt_K3_base :
    approvalPairwiseBase
        (mallowsW3K2Up mallowsHighNoisePhi)
        (mallowsW3K2Down mallowsHighNoisePhi) <
      approvalPairwiseBase
        (mallowsW3K3Up mallowsHighNoisePhi)
        (mallowsW3K3Down mallowsHighNoisePhi) := by
  have hphi_nonneg : 0 ≤ mallowsHighNoisePhi := by
    norm_num [mallowsHighNoisePhi]
  have hk2 :
      mallowsW3K2Down mallowsHighNoisePhi =
        mallowsHighNoisePhi * mallowsW3K2Up mallowsHighNoisePhi := by
    norm_num [mallowsW3K2Down, mallowsW3K2Up, mallowsHighNoisePhi,
      mallowsW3N3, mallowsW3N4]
  have hk3 :
      mallowsW3K3Down mallowsHighNoisePhi =
        mallowsHighNoisePhi * mallowsW3K3Up mallowsHighNoisePhi := by
    norm_num [mallowsW3K3Down, mallowsW3K3Up, mallowsHighNoisePhi,
      mallowsW3N4]
  rw [hk2, hk3]
  exact approvalPairwiseBase_same_ratio_strictAnti hphi_nonneg
    mallowsHighNoise_same_ratio_coef_pos
    (by
      norm_num [mallowsW3K2Up, mallowsHighNoisePhi, mallowsW3N3,
        mallowsW3N4])
    (by
      norm_num [mallowsW3K3Up, mallowsHighNoisePhi, mallowsW3N4])
    (by
      norm_num [mallowsW3K3Up, mallowsW3K2Up, mallowsHighNoisePhi,
        mallowsW3N3, mallowsW3N4])

theorem mallowsHighNoiseW3K2_base_lt_K1_base :
    approvalPairwiseBase
        (mallowsW3K2Up mallowsHighNoisePhi)
        (mallowsW3K2Down mallowsHighNoisePhi) <
      approvalPairwiseBase
        (mallowsW3K1Up mallowsHighNoisePhi)
        (mallowsW3K1Down mallowsHighNoisePhi) := by
  have hphi_nonneg : 0 ≤ mallowsHighNoisePhi := by
    norm_num [mallowsHighNoisePhi]
  have hk1 :
      mallowsW3K1Down mallowsHighNoisePhi =
        mallowsHighNoisePhi * mallowsW3K1Up mallowsHighNoisePhi := by
    norm_num [mallowsW3K1Down, mallowsW3K1Up, mallowsHighNoisePhi,
      mallowsW3N4]
  have hk2 :
      mallowsW3K2Down mallowsHighNoisePhi =
        mallowsHighNoisePhi * mallowsW3K2Up mallowsHighNoisePhi := by
    norm_num [mallowsW3K2Down, mallowsW3K2Up, mallowsHighNoisePhi,
      mallowsW3N3, mallowsW3N4]
  rw [hk1, hk2]
  exact approvalPairwiseBase_same_ratio_strictAnti hphi_nonneg
    mallowsHighNoise_same_ratio_coef_pos
    (by
      norm_num [mallowsW3K2Up, mallowsHighNoisePhi, mallowsW3N3,
        mallowsW3N4])
    (by
      norm_num [mallowsW3K1Up, mallowsHighNoisePhi, mallowsW3N4])
    (by
      norm_num [mallowsW3K1Up, mallowsW3K2Up, mallowsHighNoisePhi,
        mallowsW3N3, mallowsW3N4])

private theorem mallowsHighNoiseW3K1_base_pos_0 :
    0 < approvalPairwiseBase
      (mallowsW3K1Up0 mallowsHighNoisePhi)
      (mallowsW3K1Down mallowsHighNoisePhi) := by
  have hup : 0 < mallowsW3K1Up0 mallowsHighNoisePhi := by
    norm_num [mallowsW3K1Up0, mallowsHighNoisePhi, mallowsW3N4]
  have hdown : 0 < mallowsW3K1Down mallowsHighNoisePhi := by
    norm_num [mallowsW3K1Down, mallowsHighNoisePhi, mallowsW3N4]
  have hsum :
      mallowsW3K1Up0 mallowsHighNoisePhi +
          mallowsW3K1Down mallowsHighNoisePhi ≤ 1 := by
    norm_num [mallowsW3K1Up0, mallowsW3K1Down, mallowsHighNoisePhi,
      mallowsW3N4]
  simpa [approvalPairwiseBase] using
    ternaryGap_closedExpr_pos hup hdown hsum

private theorem mallowsHighNoiseW3K1_base_pos_1 :
    0 < approvalPairwiseBase
      (mallowsW3K1Up1 mallowsHighNoisePhi)
      (mallowsW3K1Down mallowsHighNoisePhi) := by
  have hup : 0 < mallowsW3K1Up1 mallowsHighNoisePhi := by
    norm_num [mallowsW3K1Up1, mallowsHighNoisePhi, mallowsW3N4]
  have hdown : 0 < mallowsW3K1Down mallowsHighNoisePhi := by
    norm_num [mallowsW3K1Down, mallowsHighNoisePhi, mallowsW3N4]
  have hsum :
      mallowsW3K1Up1 mallowsHighNoisePhi +
          mallowsW3K1Down mallowsHighNoisePhi ≤ 1 := by
    norm_num [mallowsW3K1Up1, mallowsW3K1Down, mallowsHighNoisePhi,
      mallowsW3N4]
  simpa [approvalPairwiseBase] using
    ternaryGap_closedExpr_pos hup hdown hsum

private theorem mallowsHighNoiseW3K1_base_0_lt_2 :
    approvalPairwiseBase
        (mallowsW3K1Up0 mallowsHighNoisePhi)
        (mallowsW3K1Down mallowsHighNoisePhi) <
      approvalPairwiseBase
        (mallowsW3K1Up mallowsHighNoisePhi)
        (mallowsW3K1Down mallowsHighNoisePhi) := by
  have hleft_sqrt :
      Real.sqrt
          (mallowsW3K1Up0 mallowsHighNoisePhi *
            mallowsW3K1Down mallowsHighNoisePhi) <
        (90 : ℝ) / 369 := by
    exact (Real.sqrt_lt
      (by
        norm_num [mallowsW3K1Up0, mallowsW3K1Down,
          mallowsHighNoisePhi, mallowsW3N4] :
        0 ≤ mallowsW3K1Up0 mallowsHighNoisePhi *
          mallowsW3K1Down mallowsHighNoisePhi)
      (by norm_num : 0 ≤ (90 : ℝ) / 369)).2
      (by
        norm_num [mallowsW3K1Up0, mallowsW3K1Down,
          mallowsHighNoisePhi, mallowsW3N4])
  have hright_sqrt :
      (143 : ℝ) / (2 * 369) <
        Real.sqrt
          (mallowsW3K1Up mallowsHighNoisePhi *
            mallowsW3K1Down mallowsHighNoisePhi) := by
    exact (Real.lt_sqrt (by norm_num : 0 ≤ (143 : ℝ) / (2 * 369))).2
      (by
        norm_num [mallowsW3K1Up, mallowsW3K1Down, mallowsHighNoisePhi,
          mallowsW3N4])
  unfold approvalPairwiseBase at *
  norm_num [mallowsW3K1Up0, mallowsW3K1Up, mallowsW3K1Down,
    mallowsHighNoisePhi, mallowsW3N4] at *
  nlinarith

private theorem mallowsHighNoiseW3K1_base_1_lt_2 :
    approvalPairwiseBase
        (mallowsW3K1Up1 mallowsHighNoisePhi)
        (mallowsW3K1Down mallowsHighNoisePhi) <
      approvalPairwiseBase
        (mallowsW3K1Up mallowsHighNoisePhi)
        (mallowsW3K1Down mallowsHighNoisePhi) := by
  have hleft_sqrt :
      Real.sqrt
          (mallowsW3K1Up1 mallowsHighNoisePhi *
            mallowsW3K1Down mallowsHighNoisePhi) <
        (161 : ℝ) / (2 * 369) := by
    exact (Real.sqrt_lt
      (by
        norm_num [mallowsW3K1Up1, mallowsW3K1Down,
          mallowsHighNoisePhi, mallowsW3N4] :
        0 ≤ mallowsW3K1Up1 mallowsHighNoisePhi *
          mallowsW3K1Down mallowsHighNoisePhi)
      (by norm_num : 0 ≤ (161 : ℝ) / (2 * 369))).2
      (by
        norm_num [mallowsW3K1Up1, mallowsW3K1Down,
          mallowsHighNoisePhi, mallowsW3N4])
  have hright_sqrt :
      (143 : ℝ) / (2 * 369) <
        Real.sqrt
          (mallowsW3K1Up mallowsHighNoisePhi *
            mallowsW3K1Down mallowsHighNoisePhi) := by
    exact (Real.lt_sqrt (by norm_num : 0 ≤ (143 : ℝ) / (2 * 369))).2
      (by
        norm_num [mallowsW3K1Up, mallowsW3K1Down, mallowsHighNoisePhi,
          mallowsW3N4])
  unfold approvalPairwiseBase at *
  norm_num [mallowsW3K1Up1, mallowsW3K1Up, mallowsW3K1Down,
    mallowsHighNoisePhi, mallowsW3N4] at *
  nlinarith

private theorem mallowsHighNoiseW3K2_base_pos_0 :
    0 < approvalPairwiseBase
      (mallowsW3K2Up0 mallowsHighNoisePhi)
      (mallowsW3K2Down0 mallowsHighNoisePhi) := by
  have hup : 0 < mallowsW3K2Up0 mallowsHighNoisePhi := by
    norm_num [mallowsW3K2Up0, mallowsHighNoisePhi, mallowsW3N3, mallowsW3N4]
  have hdown : 0 < mallowsW3K2Down0 mallowsHighNoisePhi := by
    norm_num [mallowsW3K2Down0, mallowsHighNoisePhi, mallowsW3N3, mallowsW3N4]
  have hsum :
      mallowsW3K2Up0 mallowsHighNoisePhi +
          mallowsW3K2Down0 mallowsHighNoisePhi ≤ 1 := by
    norm_num [mallowsW3K2Up0, mallowsW3K2Down0, mallowsHighNoisePhi,
      mallowsW3N3, mallowsW3N4]
  simpa [approvalPairwiseBase] using
    ternaryGap_closedExpr_pos hup hdown hsum

private theorem mallowsHighNoiseW3K2_base_pos_1 :
    0 < approvalPairwiseBase
      (mallowsW3K2Up1 mallowsHighNoisePhi)
      (mallowsW3K2Down1 mallowsHighNoisePhi) := by
  have hup : 0 < mallowsW3K2Up1 mallowsHighNoisePhi := by
    norm_num [mallowsW3K2Up1, mallowsHighNoisePhi, mallowsW3N3, mallowsW3N4]
  have hdown : 0 < mallowsW3K2Down1 mallowsHighNoisePhi := by
    norm_num [mallowsW3K2Down1, mallowsHighNoisePhi, mallowsW3N3, mallowsW3N4]
  have hsum :
      mallowsW3K2Up1 mallowsHighNoisePhi +
          mallowsW3K2Down1 mallowsHighNoisePhi ≤ 1 := by
    norm_num [mallowsW3K2Up1, mallowsW3K2Down1, mallowsHighNoisePhi,
      mallowsW3N3, mallowsW3N4]
  simpa [approvalPairwiseBase] using
    ternaryGap_closedExpr_pos hup hdown hsum

private theorem mallowsHighNoiseW3K3_base_pos_0 :
    0 < approvalPairwiseBase
      (mallowsW3K3Up mallowsHighNoisePhi)
      (mallowsW3K3Down0 mallowsHighNoisePhi) := by
  have hup : 0 < mallowsW3K3Up mallowsHighNoisePhi := by
    norm_num [mallowsW3K3Up, mallowsHighNoisePhi, mallowsW3N4]
  have hdown : 0 < mallowsW3K3Down0 mallowsHighNoisePhi := by
    norm_num [mallowsW3K3Down0, mallowsHighNoisePhi, mallowsW3N4]
  have hsum :
      mallowsW3K3Up mallowsHighNoisePhi +
          mallowsW3K3Down0 mallowsHighNoisePhi ≤ 1 := by
    norm_num [mallowsW3K3Up, mallowsW3K3Down0, mallowsHighNoisePhi,
      mallowsW3N4]
  simpa [approvalPairwiseBase] using
    ternaryGap_closedExpr_pos hup hdown hsum

private theorem mallowsHighNoiseW3K3_base_pos_1 :
    0 < approvalPairwiseBase
      (mallowsW3K3Up mallowsHighNoisePhi)
      (mallowsW3K3Down1 mallowsHighNoisePhi) := by
  have hup : 0 < mallowsW3K3Up mallowsHighNoisePhi := by
    norm_num [mallowsW3K3Up, mallowsHighNoisePhi, mallowsW3N4]
  have hdown : 0 < mallowsW3K3Down1 mallowsHighNoisePhi := by
    norm_num [mallowsW3K3Down1, mallowsHighNoisePhi, mallowsW3N4]
  have hsum :
      mallowsW3K3Up mallowsHighNoisePhi +
          mallowsW3K3Down1 mallowsHighNoisePhi ≤ 1 := by
    norm_num [mallowsW3K3Up, mallowsW3K3Down1, mallowsHighNoisePhi,
      mallowsW3N4]
  simpa [approvalPairwiseBase] using
    ternaryGap_closedExpr_pos hup hdown hsum

private theorem mallowsHighNoiseW3K2_base_0_lt_2 :
    approvalPairwiseBase
        (mallowsW3K2Up0 mallowsHighNoisePhi)
        (mallowsW3K2Down0 mallowsHighNoisePhi) <
      approvalPairwiseBase
        (mallowsW3K2Up mallowsHighNoisePhi)
        (mallowsW3K2Down mallowsHighNoisePhi) := by
  have hsqrt :
      Real.sqrt
          (mallowsW3K2Up0 mallowsHighNoisePhi *
            mallowsW3K2Down0 mallowsHighNoisePhi) =
        Real.sqrt
          (mallowsW3K2Up mallowsHighNoisePhi *
            mallowsW3K2Down mallowsHighNoisePhi) := by
    congr 1
    norm_num [mallowsW3K2Up0, mallowsW3K2Down0, mallowsW3K2Up,
      mallowsW3K2Down, mallowsHighNoisePhi, mallowsW3N3, mallowsW3N4]
  unfold approvalPairwiseBase at *
  rw [hsqrt]
  norm_num [mallowsW3K2Up0, mallowsW3K2Down0, mallowsW3K2Up,
    mallowsW3K2Down, mallowsHighNoisePhi, mallowsW3N3, mallowsW3N4]
  linarith

private theorem mallowsHighNoiseW3K2_base_1_lt_2 :
    approvalPairwiseBase
        (mallowsW3K2Up1 mallowsHighNoisePhi)
        (mallowsW3K2Down1 mallowsHighNoisePhi) <
      approvalPairwiseBase
        (mallowsW3K2Up mallowsHighNoisePhi)
        (mallowsW3K2Down mallowsHighNoisePhi) := by
  have hleft_sqrt :
      Real.sqrt
          (mallowsW3K2Up1 mallowsHighNoisePhi *
            mallowsW3K2Down1 mallowsHighNoisePhi) =
        (20 : ℝ) / 61 := by
    rw [show
      mallowsW3K2Up1 mallowsHighNoisePhi *
          mallowsW3K2Down1 mallowsHighNoisePhi =
        ((20 : ℝ) / 61) ^ 2 by
      norm_num [mallowsW3K2Up1, mallowsW3K2Down1, mallowsHighNoisePhi,
        mallowsW3N3, mallowsW3N4]]
    exact Real.sqrt_sq (by norm_num : 0 ≤ (20 : ℝ) / 61)
  have hright_sqrt :
      (321 : ℝ) / 1000 <
        Real.sqrt
          (mallowsW3K2Up mallowsHighNoisePhi *
            mallowsW3K2Down mallowsHighNoisePhi) := by
    exact (Real.lt_sqrt (by norm_num : 0 ≤ (321 : ℝ) / 1000)).2
      (by
        norm_num [mallowsW3K2Up, mallowsW3K2Down, mallowsHighNoisePhi,
          mallowsW3N3, mallowsW3N4])
  unfold approvalPairwiseBase at *
  rw [hleft_sqrt]
  norm_num [mallowsW3K2Up1, mallowsW3K2Down1, mallowsW3K2Up,
    mallowsW3K2Down, mallowsHighNoisePhi, mallowsW3N3, mallowsW3N4] at *
  nlinarith

private theorem mallowsHighNoiseW3K3_base_0_lt_2 :
    approvalPairwiseBase
        (mallowsW3K3Up mallowsHighNoisePhi)
        (mallowsW3K3Down0 mallowsHighNoisePhi) <
      approvalPairwiseBase
        (mallowsW3K3Up mallowsHighNoisePhi)
        (mallowsW3K3Down mallowsHighNoisePhi) := by
  have hleft_sqrt :
      Real.sqrt
          (mallowsW3K3Up mallowsHighNoisePhi *
            mallowsW3K3Down0 mallowsHighNoisePhi) <
        (243 : ℝ) / 1000 := by
    exact (Real.sqrt_lt
      (by
        norm_num [mallowsW3K3Up, mallowsW3K3Down0, mallowsHighNoisePhi,
          mallowsW3N4] :
        0 ≤ mallowsW3K3Up mallowsHighNoisePhi *
          mallowsW3K3Down0 mallowsHighNoisePhi)
      (by norm_num : 0 ≤ (243 : ℝ) / 1000)).2
      (by
        norm_num [mallowsW3K3Up, mallowsW3K3Down0, mallowsHighNoisePhi,
          mallowsW3N4])
  have hright_sqrt :
      (302 : ℝ) / 1000 <
        Real.sqrt
          (mallowsW3K3Up mallowsHighNoisePhi *
            mallowsW3K3Down mallowsHighNoisePhi) := by
    exact (Real.lt_sqrt (by norm_num : 0 ≤ (302 : ℝ) / 1000)).2
      (by
        norm_num [mallowsW3K3Up, mallowsW3K3Down, mallowsHighNoisePhi,
          mallowsW3N4])
  unfold approvalPairwiseBase at *
  norm_num [mallowsW3K3Up, mallowsW3K3Down0, mallowsW3K3Down,
    mallowsHighNoisePhi, mallowsW3N4] at *
  nlinarith

private theorem mallowsHighNoiseW3K3_base_1_lt_2 :
    approvalPairwiseBase
        (mallowsW3K3Up mallowsHighNoisePhi)
        (mallowsW3K3Down1 mallowsHighNoisePhi) <
      approvalPairwiseBase
        (mallowsW3K3Up mallowsHighNoisePhi)
        (mallowsW3K3Down mallowsHighNoisePhi) := by
  have hleft_sqrt :
      Real.sqrt
          (mallowsW3K3Up mallowsHighNoisePhi *
            mallowsW3K3Down1 mallowsHighNoisePhi) =
        (100 : ℝ) / 369 := by
    rw [show
      mallowsW3K3Up mallowsHighNoisePhi *
          mallowsW3K3Down1 mallowsHighNoisePhi =
        ((100 : ℝ) / 369) ^ 2 by
      norm_num [mallowsW3K3Up, mallowsW3K3Down1, mallowsHighNoisePhi,
        mallowsW3N4]]
    exact Real.sqrt_sq (by norm_num : 0 ≤ (100 : ℝ) / 369)
  have hright_sqrt :
      (302 : ℝ) / 1000 <
        Real.sqrt
          (mallowsW3K3Up mallowsHighNoisePhi *
            mallowsW3K3Down mallowsHighNoisePhi) := by
    exact (Real.lt_sqrt (by norm_num : 0 ≤ (302 : ℝ) / 1000)).2
      (by
        norm_num [mallowsW3K3Up, mallowsW3K3Down, mallowsHighNoisePhi,
          mallowsW3N4])
  unfold approvalPairwiseBase at *
  rw [hleft_sqrt]
  norm_num [mallowsW3K3Up, mallowsW3K3Down1, mallowsW3K3Down,
    mallowsHighNoisePhi, mallowsW3N4] at *
  nlinarith

theorem mallowsHighNoiseW3K2_pair2_rate_lt_pair0_rate :
    approvalPairwiseRate
        (mallowsW3K2Up mallowsHighNoisePhi)
        (mallowsW3K2Down mallowsHighNoisePhi) <
      approvalPairwiseRate
        (mallowsW3K2Up0 mallowsHighNoisePhi)
        (mallowsW3K2Down0 mallowsHighNoisePhi) :=
  approvalPairwiseRate_gt_of_base_lt
    mallowsHighNoiseW3K2_base_pos_0
    mallowsHighNoiseW3K2_base_pos
    mallowsHighNoiseW3K2_base_0_lt_2

theorem mallowsHighNoiseW3K2_pair2_rate_lt_pair1_rate :
    approvalPairwiseRate
        (mallowsW3K2Up mallowsHighNoisePhi)
        (mallowsW3K2Down mallowsHighNoisePhi) <
      approvalPairwiseRate
        (mallowsW3K2Up1 mallowsHighNoisePhi)
        (mallowsW3K2Down1 mallowsHighNoisePhi) :=
  approvalPairwiseRate_gt_of_base_lt
    mallowsHighNoiseW3K2_base_pos_1
    mallowsHighNoiseW3K2_base_pos
    mallowsHighNoiseW3K2_base_1_lt_2

theorem mallowsHighNoiseW3K3_pair2_rate_lt_pair0_rate :
    approvalPairwiseRate
        (mallowsW3K3Up mallowsHighNoisePhi)
        (mallowsW3K3Down mallowsHighNoisePhi) <
      approvalPairwiseRate
        (mallowsW3K3Up mallowsHighNoisePhi)
        (mallowsW3K3Down0 mallowsHighNoisePhi) :=
  approvalPairwiseRate_gt_of_base_lt
    mallowsHighNoiseW3K3_base_pos_0
    mallowsHighNoiseW3K3_base_pos
    mallowsHighNoiseW3K3_base_0_lt_2

theorem mallowsHighNoiseW3K3_pair2_rate_lt_pair1_rate :
    approvalPairwiseRate
        (mallowsW3K3Up mallowsHighNoisePhi)
        (mallowsW3K3Down mallowsHighNoisePhi) <
      approvalPairwiseRate
        (mallowsW3K3Up mallowsHighNoisePhi)
        (mallowsW3K3Down1 mallowsHighNoisePhi) :=
  approvalPairwiseRate_gt_of_base_lt
    mallowsHighNoiseW3K3_base_pos_1
    mallowsHighNoiseW3K3_base_pos
    mallowsHighNoiseW3K3_base_1_lt_2

/-- For `0 < q < 1`, the `(3,4)` pair is no harder than `(1,4)` under one-approval. -/
theorem mallowsW3K1_pair2_rate_le_pair0_rate_of_q_lt_one
    {q : ℝ} (hq_pos : 0 < q) (hq_lt : q < 1) :
    approvalPairwiseRate (mallowsW3K1Up q) (mallowsW3K1Down q) ≤
      approvalPairwiseRate (mallowsW3K1Up0 q) (mallowsW3K1Down q) := by
  have hden : 0 < mallowsW3N4 q := mallowsW3N4_pos_of_pos hq_pos
  have hq2_lt_one : q ^ 2 < 1 := by
    have hmul := mul_lt_mul_of_pos_left hq_lt hq_pos
    nlinarith
  have hq3_lt_one : q ^ 3 < 1 := by
    have hq2_pos : 0 < q ^ 2 := sq_pos_of_pos hq_pos
    have hmul := mul_lt_mul_of_pos_left hq_lt hq2_pos
    nlinarith
  refine approvalPairwiseRate_le_of_up_le_down_ge ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · unfold mallowsW3K1Up
    positivity
  · unfold mallowsW3K1Down
    positivity
  · unfold mallowsW3K1Up0
    positivity
  · unfold mallowsW3K1Down
    positivity
  · exact approvalPairwiseBase_pos_of_pos_sum_le
      (by unfold mallowsW3K1Up; positivity)
      (by unfold mallowsW3K1Down; positivity)
      (by
        unfold mallowsW3K1Up mallowsW3K1Down mallowsW3N4
        field_simp [hden.ne']
        ring_nf
        nlinarith [hq_pos])
  · exact approvalPairwiseBase_pos_of_pos_sum_le
      (by unfold mallowsW3K1Up0; positivity)
      (by unfold mallowsW3K1Down; positivity)
      (by
        unfold mallowsW3K1Up0 mallowsW3K1Down mallowsW3N4
        field_simp [hden.ne']
        ring_nf
        have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
        have hq3 : 0 ≤ q ^ 3 := pow_nonneg hq_pos.le 3
        nlinarith [hq_pos, hq2, hq3])
  · unfold mallowsW3K1Up mallowsW3K1Down
    field_simp [hden.ne']
    ring_nf
    nlinarith [hq_pos, hq_lt]
  · unfold mallowsW3K1Up0 mallowsW3K1Down
    field_simp [hden.ne']
    ring_nf
    nlinarith [hq3_lt_one]
  · unfold mallowsW3K1Up mallowsW3K1Up0
    field_simp [hden.ne']
    ring_nf
    nlinarith [hq_pos, hq_lt]
  · rfl

/-- For `0 < q < 1`, the `(3,4)` pair is no harder than `(2,4)` under one-approval. -/
theorem mallowsW3K1_pair2_rate_le_pair1_rate_of_q_lt_one
    {q : ℝ} (hq_pos : 0 < q) (hq_lt : q < 1) :
    approvalPairwiseRate (mallowsW3K1Up q) (mallowsW3K1Down q) ≤
      approvalPairwiseRate (mallowsW3K1Up1 q) (mallowsW3K1Down q) := by
  have hden : 0 < mallowsW3N4 q := mallowsW3N4_pos_of_pos hq_pos
  have hq2_lt_one : q ^ 2 < 1 := by
    have hmul := mul_lt_mul_of_pos_left hq_lt hq_pos
    nlinarith
  refine approvalPairwiseRate_le_of_up_le_down_ge ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · unfold mallowsW3K1Up
    positivity
  · unfold mallowsW3K1Down
    positivity
  · unfold mallowsW3K1Up1
    positivity
  · unfold mallowsW3K1Down
    positivity
  · exact approvalPairwiseBase_pos_of_pos_sum_le
      (by unfold mallowsW3K1Up; positivity)
      (by unfold mallowsW3K1Down; positivity)
      (by
        unfold mallowsW3K1Up mallowsW3K1Down mallowsW3N4
        field_simp [hden.ne']
        ring_nf
        nlinarith [hq_pos])
  · exact approvalPairwiseBase_pos_of_pos_sum_le
      (by unfold mallowsW3K1Up1; positivity)
      (by unfold mallowsW3K1Down; positivity)
      (by
        unfold mallowsW3K1Up1 mallowsW3K1Down mallowsW3N4
        field_simp [hden.ne']
        ring_nf
        have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
        nlinarith [hq_pos, hq2])
  · unfold mallowsW3K1Up mallowsW3K1Down
    field_simp [hden.ne']
    ring_nf
    nlinarith [hq_pos, hq_lt]
  · unfold mallowsW3K1Up1 mallowsW3K1Down
    field_simp [hden.ne']
    ring_nf
    nlinarith [hq_pos, hq_lt]
  · unfold mallowsW3K1Up mallowsW3K1Up1
    field_simp [hden.ne']
    ring_nf
    nlinarith [hq_pos, hq_lt]
  · rfl

/-- For `0 < q < 1`, the `(3,4)` pair is no harder than `(1,4)` under two-approval. -/
theorem mallowsW3K2_pair2_rate_le_pair0_rate_of_q_lt_one
    {q : ℝ} (hq_pos : 0 < q) (hq_lt : q < 1) :
    approvalPairwiseRate (mallowsW3K2Up q) (mallowsW3K2Down q) ≤
      approvalPairwiseRate (mallowsW3K2Up0 q) (mallowsW3K2Down0 q) := by
  have hN3 : 0 < mallowsW3N3 q := mallowsW3N3_pos_of_pos hq_pos
  have hN4 : 0 < mallowsW3N4 q := mallowsW3N4_pos_of_pos hq_pos
  have hden : 0 < mallowsW3N3 q * mallowsW3N4 q := mul_pos hN3 hN4
  have hq3_lt_one : q ^ 3 < 1 := by
    have hq2_pos : 0 < q ^ 2 := sq_pos_of_pos hq_pos
    have hmul := mul_lt_mul_of_pos_left hq_lt hq2_pos
    nlinarith
  refine approvalPairwiseRate_le_of_up_le_down_ge ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · unfold mallowsW3K2Up
    positivity
  · unfold mallowsW3K2Down
    positivity
  · unfold mallowsW3K2Up0
    positivity
  · unfold mallowsW3K2Down0
    positivity
  · exact approvalPairwiseBase_pos_of_pos_sum_le
      (by unfold mallowsW3K2Up; positivity)
      (by unfold mallowsW3K2Down; positivity)
      (by
        unfold mallowsW3K2Up mallowsW3K2Down mallowsW3N3 mallowsW3N4
        field_simp [hden.ne']
        ring_nf
        have hq4 : 0 ≤ q ^ 4 := pow_nonneg hq_pos.le 4
        have hq5 : 0 ≤ q ^ 5 := pow_nonneg hq_pos.le 5
        nlinarith [hq_pos, hq4, hq5])
  · exact approvalPairwiseBase_pos_of_pos_sum_le
      (by unfold mallowsW3K2Up0; positivity)
      (by unfold mallowsW3K2Down0; positivity)
      (by
        unfold mallowsW3K2Up0 mallowsW3K2Down0 mallowsW3N3 mallowsW3N4
        field_simp [hden.ne']
        ring_nf
        have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
        have hq3 : 0 ≤ q ^ 3 := pow_nonneg hq_pos.le 3
        nlinarith [hq_pos, hq2, hq3])
  · unfold mallowsW3K2Up mallowsW3K2Down mallowsW3N3 mallowsW3N4
    field_simp [hden.ne']
    ring_nf
    nlinarith [hq_pos, hq_lt]
  · unfold mallowsW3K2Up0 mallowsW3K2Down0 mallowsW3N3 mallowsW3N4
    field_simp [hden.ne']
    ring_nf
    nlinarith [hq3_lt_one]
  · unfold mallowsW3K2Up mallowsW3K2Up0 mallowsW3N3 mallowsW3N4
    field_simp [hden.ne']
    ring_nf
    nlinarith [hq_pos, hq_lt]
  · unfold mallowsW3K2Down mallowsW3K2Down0 mallowsW3N3 mallowsW3N4
    field_simp [hden.ne']
    ring_nf
    nlinarith [hq_pos, hq_lt]

/-- For `0 < q < 1`, the `(3,4)` pair is no harder than `(2,4)` under two-approval. -/
theorem mallowsW3K2_pair2_rate_le_pair1_rate_of_q_lt_one
    {q : ℝ} (hq_pos : 0 < q) (hq_lt : q < 1) :
    approvalPairwiseRate (mallowsW3K2Up q) (mallowsW3K2Down q) ≤
      approvalPairwiseRate (mallowsW3K2Up1 q) (mallowsW3K2Down1 q) := by
  have hN3 : 0 < mallowsW3N3 q := mallowsW3N3_pos_of_pos hq_pos
  have hN4 : 0 < mallowsW3N4 q := mallowsW3N4_pos_of_pos hq_pos
  have hden : 0 < mallowsW3N3 q * mallowsW3N4 q := mul_pos hN3 hN4
  have hq2_lt_one : q ^ 2 < 1 := by
    have hmul := mul_lt_mul_of_pos_left hq_lt hq_pos
    nlinarith
  refine approvalPairwiseRate_le_of_up_le_down_ge ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · unfold mallowsW3K2Up
    positivity
  · unfold mallowsW3K2Down
    positivity
  · unfold mallowsW3K2Up1
    positivity
  · unfold mallowsW3K2Down1
    positivity
  · exact approvalPairwiseBase_pos_of_pos_sum_le
      (by unfold mallowsW3K2Up; positivity)
      (by unfold mallowsW3K2Down; positivity)
      (by
        unfold mallowsW3K2Up mallowsW3K2Down mallowsW3N3 mallowsW3N4
        field_simp [hden.ne']
        ring_nf
        have hq4 : 0 ≤ q ^ 4 := pow_nonneg hq_pos.le 4
        have hq5 : 0 ≤ q ^ 5 := pow_nonneg hq_pos.le 5
        nlinarith [hq_pos, hq4, hq5])
  · exact approvalPairwiseBase_pos_of_pos_sum_le
      (by unfold mallowsW3K2Up1; positivity)
      (by unfold mallowsW3K2Down1; positivity)
      (by
        unfold mallowsW3K2Up1 mallowsW3K2Down1 mallowsW3N3 mallowsW3N4
        field_simp [hden.ne']
        ring_nf
        have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
        have hq3 : 0 ≤ q ^ 3 := pow_nonneg hq_pos.le 3
        nlinarith [hq_pos, hq2, hq3])
  · unfold mallowsW3K2Up mallowsW3K2Down mallowsW3N3 mallowsW3N4
    field_simp [hden.ne']
    ring_nf
    nlinarith [hq_pos, hq_lt]
  · unfold mallowsW3K2Up1 mallowsW3K2Down1 mallowsW3N3 mallowsW3N4
    field_simp [hden.ne']
    ring_nf
    nlinarith [hq2_lt_one]
  · unfold mallowsW3K2Up mallowsW3K2Up1 mallowsW3N3 mallowsW3N4
    field_simp [hden.ne']
    ring_nf
    nlinarith [hq2_lt_one]
  · unfold mallowsW3K2Down mallowsW3K2Down1 mallowsW3N3 mallowsW3N4
    field_simp [hden.ne']
    ring_nf
    nlinarith [hq_pos, hq_lt]

/-- For `0 < q < 1`, the `(3,4)` pair is no harder than `(1,4)` under three-approval. -/
theorem mallowsW3K3_pair2_rate_le_pair0_rate_of_q_lt_one
    {q : ℝ} (hq_pos : 0 < q) (hq_lt : q < 1) :
    approvalPairwiseRate (mallowsW3K3Up q) (mallowsW3K3Down q) ≤
      approvalPairwiseRate (mallowsW3K3Up q) (mallowsW3K3Down0 q) := by
  have hden : 0 < mallowsW3N4 q := mallowsW3N4_pos_of_pos hq_pos
  have hq3_lt_one : q ^ 3 < 1 := by
    have hq2_pos : 0 < q ^ 2 := sq_pos_of_pos hq_pos
    have hmul := mul_lt_mul_of_pos_left hq_lt hq2_pos
    nlinarith
  refine approvalPairwiseRate_le_of_up_le_down_ge ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · unfold mallowsW3K3Up
    positivity
  · unfold mallowsW3K3Down
    positivity
  · unfold mallowsW3K3Up
    positivity
  · unfold mallowsW3K3Down0
    positivity
  · exact approvalPairwiseBase_pos_of_pos_sum_le
      (by unfold mallowsW3K3Up; positivity)
      (by unfold mallowsW3K3Down; positivity)
      (by
        unfold mallowsW3K3Up mallowsW3K3Down mallowsW3N4
        field_simp [hden.ne']
        ring_nf
        have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
        have hq3 : 0 ≤ q ^ 3 := pow_nonneg hq_pos.le 3
        nlinarith [hq2, hq3])
  · exact approvalPairwiseBase_pos_of_pos_sum_le
      (by unfold mallowsW3K3Up; positivity)
      (by unfold mallowsW3K3Down0; positivity)
      (by
        unfold mallowsW3K3Up mallowsW3K3Down0 mallowsW3N4
        field_simp [hden.ne']
        ring_nf
        nlinarith [hq_pos])
  · unfold mallowsW3K3Up mallowsW3K3Down
    field_simp [hden.ne']
    ring_nf
    nlinarith [hq_pos, hq_lt]
  · unfold mallowsW3K3Up mallowsW3K3Down0
    field_simp [hden.ne']
    ring_nf
    nlinarith [hq3_lt_one]
  · rfl
  · unfold mallowsW3K3Down mallowsW3K3Down0
    field_simp [hden.ne']
    ring_nf
    nlinarith [hq_pos, hq_lt]

/-- For `0 < q < 1`, the `(3,4)` pair is no harder than `(2,4)` under three-approval. -/
theorem mallowsW3K3_pair2_rate_le_pair1_rate_of_q_lt_one
    {q : ℝ} (hq_pos : 0 < q) (hq_lt : q < 1) :
    approvalPairwiseRate (mallowsW3K3Up q) (mallowsW3K3Down q) ≤
      approvalPairwiseRate (mallowsW3K3Up q) (mallowsW3K3Down1 q) := by
  have hden : 0 < mallowsW3N4 q := mallowsW3N4_pos_of_pos hq_pos
  have hq2_lt_one : q ^ 2 < 1 := by
    have hmul := mul_lt_mul_of_pos_left hq_lt hq_pos
    nlinarith
  refine approvalPairwiseRate_le_of_up_le_down_ge ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · unfold mallowsW3K3Up
    positivity
  · unfold mallowsW3K3Down
    positivity
  · unfold mallowsW3K3Up
    positivity
  · unfold mallowsW3K3Down1
    positivity
  · exact approvalPairwiseBase_pos_of_pos_sum_le
      (by unfold mallowsW3K3Up; positivity)
      (by unfold mallowsW3K3Down; positivity)
      (by
        unfold mallowsW3K3Up mallowsW3K3Down mallowsW3N4
        field_simp [hden.ne']
        ring_nf
        have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
        have hq3 : 0 ≤ q ^ 3 := pow_nonneg hq_pos.le 3
        nlinarith [hq2, hq3])
  · exact approvalPairwiseBase_pos_of_pos_sum_le
      (by unfold mallowsW3K3Up; positivity)
      (by unfold mallowsW3K3Down1; positivity)
      (by
        unfold mallowsW3K3Up mallowsW3K3Down1 mallowsW3N4
        field_simp [hden.ne']
        ring_nf
        nlinarith [hq_pos])
  · unfold mallowsW3K3Up mallowsW3K3Down
    field_simp [hden.ne']
    ring_nf
    nlinarith [hq_pos, hq_lt]
  · unfold mallowsW3K3Up mallowsW3K3Down1
    field_simp [hden.ne']
    ring_nf
    nlinarith [hq2_lt_one]
  · rfl
  · unfold mallowsW3K3Down mallowsW3K3Down1
    field_simp [hden.ne']
    ring_nf
    nlinarith [hq_pos, hq_lt]

theorem mallowsHighNoiseW3K1_pair2_rate_lt_pair0_rate :
    approvalPairwiseRate
        (mallowsW3K1Up mallowsHighNoisePhi)
        (mallowsW3K1Down mallowsHighNoisePhi) <
      approvalPairwiseRate
        (mallowsW3K1Up0 mallowsHighNoisePhi)
        (mallowsW3K1Down mallowsHighNoisePhi) :=
  approvalPairwiseRate_gt_of_base_lt
    mallowsHighNoiseW3K1_base_pos_0
    mallowsHighNoiseW3K1_base_pos
    mallowsHighNoiseW3K1_base_0_lt_2

theorem mallowsHighNoiseW3K1_pair2_rate_lt_pair1_rate :
    approvalPairwiseRate
        (mallowsW3K1Up mallowsHighNoisePhi)
        (mallowsW3K1Down mallowsHighNoisePhi) <
      approvalPairwiseRate
        (mallowsW3K1Up1 mallowsHighNoisePhi)
        (mallowsW3K1Down mallowsHighNoisePhi) :=
  approvalPairwiseRate_gt_of_base_lt
    mallowsHighNoiseW3K1_base_pos_1
    mallowsHighNoiseW3K1_base_pos
    mallowsHighNoiseW3K1_base_1_lt_2

/--
Symbolic high-noise boundary-pair comparison for the four-candidate `W = 3`
Mallows example: whenever `1 < q^2 + q^3`, 2-approval has a strictly larger
pairwise learning rate than 3-approval at the pivotal pair `(3,4)`.
-/
theorem mallowsW3K2_rate_gt_K3_rate_of_q_high_noise
    {q : ℝ} (hq_pos : 0 < q) (hq_lt : q < 1)
    (hhigh : 1 < q ^ 2 + q ^ 3) :
    approvalPairwiseRate (mallowsW3K3Up q) (mallowsW3K3Down q) <
      approvalPairwiseRate (mallowsW3K2Up q) (mallowsW3K2Down q) :=
  approvalPairwiseRate_gt_of_base_lt
    (mallowsW3K2_boundary_base_pos_of_phi_pos hq_pos)
    (mallowsW3K3_boundary_base_pos_of_phi_pos hq_pos)
    (mallowsW3K2_base_lt_K3_base_of_q_high_noise hq_pos hq_lt hhigh)

/--
For any nonzero Mallows noise below one, the same boundary-pair comparison
shows 2-approval has a strictly larger pairwise learning rate than 1-approval
in the four-candidate `W = 3` example.
-/
theorem mallowsW3K2_rate_gt_K1_rate_of_q_lt_one
    {q : ℝ} (hq_pos : 0 < q) (hq_lt : q < 1) :
    approvalPairwiseRate (mallowsW3K1Up q) (mallowsW3K1Down q) <
      approvalPairwiseRate (mallowsW3K2Up q) (mallowsW3K2Down q) :=
  approvalPairwiseRate_gt_of_base_lt
    (mallowsW3K2_boundary_base_pos_of_phi_pos hq_pos)
    (mallowsW3K1_boundary_base_pos_of_phi_pos hq_pos)
    (mallowsW3K2_base_lt_K1_base_of_q_lt_one hq_pos hq_lt)

/--
The paper's high-noise `M = 4`, `W = 3`, `phi = 0.8` example: for the pivotal
pair `(3,4)`, 2-approval has strictly larger pairwise learning rate than
W-approval, so W-approval is not optimal in this Mallows instance once the
source pair-probability calculation is supplied.
-/
theorem mallowsHighNoiseW3K2_rate_gt_K3_rate :
    approvalPairwiseRate
        (mallowsW3K3Up mallowsHighNoisePhi)
        (mallowsW3K3Down mallowsHighNoisePhi) <
      approvalPairwiseRate
        (mallowsW3K2Up mallowsHighNoisePhi)
        (mallowsW3K2Down mallowsHighNoisePhi) :=
  approvalPairwiseRate_gt_of_base_lt
    mallowsHighNoiseW3K2_base_pos
    mallowsHighNoiseW3K3_base_pos
    mallowsHighNoiseW3K2_base_lt_K3_base

/--
In the same high-noise example, 2-approval also has a strictly larger pairwise
learning rate than 1-approval for the pivotal pair `(3,4)`.
-/
theorem mallowsHighNoiseW3K2_rate_gt_K1_rate :
    approvalPairwiseRate
        (mallowsW3K1Up mallowsHighNoisePhi)
        (mallowsW3K1Down mallowsHighNoisePhi) <
      approvalPairwiseRate
        (mallowsW3K2Up mallowsHighNoisePhi)
        (mallowsW3K2Down mallowsHighNoisePhi) :=
  approvalPairwiseRate_gt_of_base_lt
    mallowsHighNoiseW3K2_base_pos
    mallowsHighNoiseW3K1_base_pos
    mallowsHighNoiseW3K2_base_lt_K1_base

end

end GGSG19TopThree
