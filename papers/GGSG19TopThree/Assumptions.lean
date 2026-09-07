import AppliedModelingLib.Foundations.Probability.FiniteIidStrongLaw
import GGSG19TopThree.Implementation

/-!
# Paper Assumptions: GGSG19 Top Three

This file records source theorem conditions used by the compact paper-facing
review surface. The assumptions are not proof certificates: they are the
strict-separation, finite-support, randomized-mechanism, and Mallows-domain
conditions appearing in the source statements.
-/

namespace GGSG19TopThree

open AppliedModelingLib.SocialChoice.Ranking
open AppliedModelingLib.Probability

/--
The source's finite-voter model as the canonical infinite iid path measure on
strict rankings.  Each finite election samples an initial segment of this
path; the definition keeps the common PMF and independence explicit.
-/
noncomputable def model_finite_iid_strict_rankings
    {n : ℕ} (law : PMF (Ranking n)) : MeasureTheory.Measure (ℕ → Ranking n) := by
  letI : MeasurableSpace (Ranking n) := ⊤
  exact AppliedModelingLib.finitePMFIidPathMeasure law

/--
The source's ordered election goal: candidate tiers are indexed in societal
order, partition the finite candidate set, and have fixed, declared sizes.
-/
abbrev model_arbitrary_ordered_tier_goal
    {Candidate : Type*} [Fintype Candidate] [DecidableEq Candidate]
    (Stage : ℕ) (tierSize : Fin Stage → ℕ)
    (tier : Fin Stage → Finset Candidate) : Prop :=
  (∀ candidate : Candidate, ∃! stage : Fin Stage, candidate ∈ tier stage) ∧
    ∀ stage : Fin Stage, (tier stage).card = tierSize stage

/--
The source's Mallows model: a strict-ranking PMF has mass proportional to the
Kendall--tau weight from a reference ranking, with the printed closed
parameter domain.  This deliberately includes the source's zero-noise
endpoint, unlike positive-parameter theorem premises.
-/
abbrev model_mallows_ranking_mass_and_parameter_domain
    {n : ℕ} (law : PMF (Ranking n)) (center : Ranking n) (q : ℝ) : Prop :=
  0 ≤ q ∧ q ≤ 1 ∧
    ∃ normalizer : ℝ, 0 < normalizer ∧
      ∀ ranking : Ranking n,
        (law ranking).toReal = mallowsWeight q center ranking / normalizer

/--
The source's finite randomized scoring mechanism: first sample a scoring-rule
index from the displayed probability vector, independently sample a strict
ranking, then evaluate that indexed score rule on the ranking.
-/
noncomputable def model_randomized_scoring_mechanism
    {n : ℕ} {Rule : Type*} [Fintype Rule] [DecidableEq Rule]
    (law : PMF (Ranking n)) (score : Rule → Candidate n → Ranking n → ℝ)
    (weight : Rule → ℝ) (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1) :
    PMF (Rule × Ranking n) × (Candidate n → Rule × Ranking n → ℝ) :=
  (randomizedScoringSamplingLaw law weight hweight hsum,
    fun candidate draw => score draw.1 candidate draw.2)

/-- Proposition 3's K-approval pairwise row uses the ternary score-gap domain. -/
-- audit-premise: hle : pDown ≤ pUp
-- audit-premise: hscore : ∀ signal, hiScore signal - loScore signal = 1 ∨ hiScore signal - loScore signal = 0 ∨ hiScore signal - loScore signal = -1
-- audit-premise: hpUp : AppliedModelingLib.pmfProb law (fun signal => hiScore signal - loScore signal = 1) = pUp
-- audit-premise: hpDown : AppliedModelingLib.pmfProb law (fun signal => hiScore signal - loScore signal = -1) = pDown
-- audit-premise: hpZero : AppliedModelingLib.pmfProb law (fun signal => hiScore signal - loScore signal = 0) = pZero
abbrev assumption_pairwise_approval_ternary_gap_domain
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (pUp pDown pZero : ℝ) : Prop :=
  pDown ≤ pUp ∧
    (∀ signal,
      hiScore signal - loScore signal = 1 ∨
        hiScore signal - loScore signal = 0 ∨
          hiScore signal - loScore signal = -1) ∧
    AppliedModelingLib.pmfProb law
        (fun signal => hiScore signal - loScore signal = 1) =
      pUp ∧
    AppliedModelingLib.pmfProb law
        (fun signal => hiScore signal - loScore signal = -1) =
      pDown ∧
    AppliedModelingLib.pmfProb law
        (fun signal => hiScore signal - loScore signal = 0) =
      pZero

/-- Randomized scoring and randomized K-approval mechanisms use probability weights. -/
-- audit-premise: hweight : ∀ rule, 0 ≤ weight rule
-- audit-premise: hsum : (∑ rule : Rule, weight rule) = 1
abbrev assumption_randomized_mechanism_probability_weights
    {Rule : Type*} [Fintype Rule] (weight : Rule → ℝ) : Prop :=
  (∀ rule, 0 ≤ weight rule) ∧
    (∑ rule : Rule, weight rule) = 1

/-- The positive-parameter Mallows corollary uses a nontrivial winner and `0 < q < 1`. -/
-- audit-premise: hDomain : 0 < W.val ∧ 0 < q ∧ q < 1
abbrev assumption_mallows_nontrivial_winner_and_parameter_domain
    {n : ℕ} (q : ℝ) (W : Candidate n) : Prop :=
  0 < W.val ∧ 0 < q ∧ q < 1

/-- The repeated-insertion algorithm uses the source's closed Mallows domain. -/
-- audit-premise: hDomain : 0 ≤ q ∧ q ≤ 1
abbrev assumption_mallows_repeated_insertion_parameter_domain (q : ℝ) : Prop :=
  0 ≤ q ∧ q ≤ 1

/-- Randomized Mallows K-approval families range over nontrivial proper cutoffs. -/
-- audit-premise: hK_pos : ∀ rule, 0 < K rule
-- audit-premise: hK_lt : ∀ rule, K rule < n + 2
abbrev assumption_nontrivial_k_approval_cutoffs
    {n : ℕ} {Rule : Type*} [Fintype Rule] (K : Rule → ℕ) : Prop :=
  (∀ rule, 0 < K rule) ∧
    (∀ rule, K rule < n + 2)

end GGSG19TopThree
