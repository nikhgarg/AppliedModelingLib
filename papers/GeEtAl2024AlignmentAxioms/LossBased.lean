import AppliedModelingLib.Alignment.Axioms.LinearModel
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Real.Pointwise
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Loss-based aggregation: source support for Ge et al. (2024), §3.1

This module begins the proof chain for Theorem 3.1.  The source reduces the
three-candidate core instance to the two-variable objective
`g (rₐ - r_b) + g rₐ + g r_b`, where
`g x = p ℓ (-x) + (1 - p) ℓ x`.  The definitions below preserve that reduction
and first formalize its optimizer-symmetrization argument from Appendix A.1.

No compactness, differentiability, or minimizer-existence claim is hidden in
these definitions: each such fact remains an explicit target of the source
Lemma 3.2 proof.
-/

namespace GeEtAl2024AlignmentAxioms

open Set
open Filter
open SignType
open scoped Topology Uniformity
open scoped Pointwise
open AppliedModelingLib.Alignment.Axioms
open AppliedModelingLib.SocialChoice.Ranking

/--
The source's standard §3.1 loss: every strict voter comparison contributes
one loss term.  Self-pairs contribute zero because no strict ranking orders a
candidate above itself.
-/
noncomputable def standardLoss
    {Voter : Type*} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (profile : RankingProfile Voter n) (loss : ℝ → ℝ)
    (parameter : LinearRewardParameter dimension) : ℝ := by
  classical
  exact ∑ voter : Voter, ∑ pair : Candidate n × Candidate n,
    if StrictlyPrefers (profile voter) pair.1 pair.2 then
      loss (linearReward parameter features pair.2 - linearReward parameter features pair.1)
    else 0

/-- The contribution to the standard loss from one complete input ranking. -/
noncomputable def rankingPairLoss
    {n dimension : ℕ} (features : Candidate n → FeatureVector dimension)
    (ranking : Ranking n) (loss : ℝ → ℝ)
    (parameter : LinearRewardParameter dimension) : ℝ := by
  classical
  exact ∑ pair : Candidate n × Candidate n,
    if StrictlyPrefers ranking pair.1 pair.2 then
      loss (linearReward parameter features pair.2 - linearReward parameter features pair.1)
    else 0

/-- The standard loss is the finite sum of its per-ranking contributions. -/
theorem standardLoss_eq_sum_rankingPairLoss
    {Voter : Type*} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (profile : RankingProfile Voter n) (loss : ℝ → ℝ)
    (parameter : LinearRewardParameter dimension) :
    standardLoss features profile loss parameter =
      ∑ voter : Voter, rankingPairLoss features (profile voter) loss parameter := rfl

/-- Two distinct submitted comparisons give a joint lower bound on one ranking's loss. -/
theorem two_terms_le_rankingPairLoss
    {n dimension : ℕ} (features : Candidate n → FeatureVector dimension)
    (ranking : Ranking n) (loss : ℝ → ℝ) (parameter : LinearRewardParameter dimension)
    (hloss_nonnegative : ∀ input, 0 ≤ loss input)
    {first₁ second₁ first₂ second₂ : Candidate n}
    (hfirst : StrictlyPrefers ranking first₁ second₁)
    (hsecond : StrictlyPrefers ranking first₂ second₂)
    (hpairs : (first₁, second₁) ≠ (first₂, second₂)) :
    loss (linearReward parameter features second₁ - linearReward parameter features first₁) +
      loss (linearReward parameter features second₂ - linearReward parameter features first₂) ≤
        rankingPairLoss features ranking loss parameter := by
  classical
  let contribution : Candidate n × Candidate n → ℝ := fun pair =>
    if StrictlyPrefers ranking pair.1 pair.2 then
      loss (linearReward parameter features pair.2 - linearReward parameter features pair.1)
    else 0
  let selected : Finset (Candidate n × Candidate n) :=
    {(first₁, second₁), (first₂, second₂)}
  have hselected :
      ∑ pair ∈ selected, contribution pair =
        loss (linearReward parameter features second₁ - linearReward parameter features first₁) +
          loss (linearReward parameter features second₂ - linearReward parameter features first₂) := by
    simp [selected, contribution, hfirst, hsecond, hpairs]
  have hsubset : selected ⊆ (Finset.univ : Finset (Candidate n × Candidate n)) := by
    intro pair _hpair
    exact Finset.mem_univ _
  have hsum : ∑ pair ∈ selected, contribution pair ≤
      ∑ pair : Candidate n × Candidate n, contribution pair := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro pair _hpair _hnot_selected
    unfold contribution
    split
    · exact hloss_nonnegative _
    · exact le_rfl
  rw [hselected] at hsum
  simpa only [rankingPairLoss, contribution] using hsum

/-- The standard-loss infimum restricted to parameters inducing one ranking. -/
noncomputable def restrictedStandardLossInfimum
    {Voter : Type*} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (profile : RankingProfile Voter n) (loss : ℝ → ℝ) (ranking : Ranking n) : ℝ :=
  sInf (standardLoss features profile loss ''
    { parameter | InducesRanking features parameter ranking })

/-- The unrestricted standard-loss infimum from source §3.1. -/
noncomputable def globalStandardLossInfimum
    {Voter : Type*} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (profile : RankingProfile Voter n) (loss : ℝ → ℝ) : ℝ :=
  sInf (Set.range (standardLoss features profile loss))

/-- Source's ranking-level minimization condition for the standard loss. -/
def IsStandardLossMinimizing
    {Voter : Type*} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension) (loss : ℝ → ℝ)
    (rule : LinearRankAggregationRule Voter n (LinearFeasibleRanking features)) : Prop :=
  ∀ profile, FeasibleProfile (LinearFeasibleRanking features) profile →
    restrictedStandardLossInfimum features profile loss (rule.run profile) =
      globalStandardLossInfimum features profile loss

/-- Every standard-loss term, and hence the total, is nonnegative for a nonnegative loss. -/
theorem standardLoss_nonnegative
    {Voter : Type*} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (profile : RankingProfile Voter n) (loss : ℝ → ℝ)
    (parameter : LinearRewardParameter dimension)
    (hloss_nonnegative : ∀ input, 0 ≤ loss input) :
    0 ≤ standardLoss features profile loss parameter := by
  classical
  unfold standardLoss
  apply Finset.sum_nonneg
  intro voter _
  apply Finset.sum_nonneg
  intro pair _
  split
  · exact hloss_nonnegative _
  · exact le_rfl

/--
If every voter ranks `first` above `second`, every parameter inducing an
output that preserves that pair pays at least `loss 0` in the standard loss.
This is the lower-bound step in the positive-input branch of Theorem 3.1.
-/
theorem loss_zero_le_standardLoss_of_universal_pair_of_nonpositive_lower
    {Voter : Type*} [Fintype Voter] [Nonempty Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (profile : RankingProfile Voter n) (loss : ℝ → ℝ)
    (parameter : LinearRewardParameter dimension) (output : Ranking n)
    (hloss_nonnegative : ∀ input, 0 ≤ loss input)
    (hloss_nonpositive_lower : ∀ input, input ≤ 0 → loss 0 ≤ loss input)
    {first second : Candidate n}
    (huniversal : UniversallyPreferred profile first second)
    (houtput : StrictlyPrefers output first second)
    (hinduced : InducesRanking features parameter output) :
    loss 0 ≤ standardLoss features profile loss parameter := by
  classical
  let voter : Voter := Classical.choice (inferInstance : Nonempty Voter)
  have hgap_nonpositive :
      linearReward parameter features second - linearReward parameter features first ≤ 0 :=
    sub_nonpos.mpr (hinduced first second houtput)
  have hterm : loss 0 ≤
      if StrictlyPrefers (profile voter) first second then
        loss (linearReward parameter features second - linearReward parameter features first)
      else 0 := by
    rw [if_pos (huniversal voter)]
    exact hloss_nonpositive_lower _ hgap_nonpositive
  have hsingle_pair : loss 0 ≤ ∑ pair : Candidate n × Candidate n,
      if StrictlyPrefers (profile voter) pair.1 pair.2 then
        loss (linearReward parameter features pair.2 - linearReward parameter features pair.1)
      else 0 := by
    calc
      loss 0 ≤ if StrictlyPrefers (profile voter) first second then
          loss (linearReward parameter features second - linearReward parameter features first)
        else 0 := hterm
      _ ≤ ∑ pair : Candidate n × Candidate n,
          if StrictlyPrefers (profile voter) pair.1 pair.2 then
            loss (linearReward parameter features pair.2 - linearReward parameter features pair.1)
          else 0 := by
        apply Finset.single_le_sum
          (s := Finset.univ)
          (f := fun pair : Candidate n × Candidate n =>
            if StrictlyPrefers (profile voter) pair.1 pair.2 then
              loss (linearReward parameter features pair.2 - linearReward parameter features pair.1)
            else 0)
          (a := (first, second))
        · intro pair _
          by_cases hprefers : StrictlyPrefers (profile voter) pair.1 pair.2
          · simp [hprefers, hloss_nonnegative]
          · simp [hprefers]
        · exact Finset.mem_univ _
  calc
    loss 0 ≤ ∑ pair : Candidate n × Candidate n,
        if StrictlyPrefers (profile voter) pair.1 pair.2 then
          loss (linearReward parameter features pair.2 - linearReward parameter features pair.1)
        else 0 := hsingle_pair
    _ ≤ ∑ voter : Voter, ∑ pair : Candidate n × Candidate n,
        if StrictlyPrefers (profile voter) pair.1 pair.2 then
          loss (linearReward parameter features pair.2 - linearReward parameter features pair.1)
        else 0 := by
      apply Finset.single_le_sum
        (s := Finset.univ)
        (f := fun otherVoter : Voter => ∑ pair : Candidate n × Candidate n,
          if StrictlyPrefers (profile otherVoter) pair.1 pair.2 then
            loss (linearReward parameter features pair.2 - linearReward parameter features pair.1)
          else 0)
        (a := voter)
      · intro otherVoter _
        apply Finset.sum_nonneg
        intro pair _
        by_cases hprefers : StrictlyPrefers (profile otherVoter) pair.1 pair.2
        · simp [hprefers, hloss_nonnegative]
        · simp [hprefers]
      · exact Finset.mem_univ _
    _ = standardLoss features profile loss parameter := rfl

/--
The ranking-level standard-loss minimization condition cannot output a
universally preferred pair when a strictly better loss witness exists.  This
is the decision-theoretic core of the final, two-candidate branch of the
source proof of Theorem 3.1.
-/
theorem standardLossMinimizing_rule_not_orders_universal_pair_of_witness
    {Voter : Type*} [Fintype Voter] [Nonempty Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (profile : RankingProfile Voter n) (loss : ℝ → ℝ)
    (rule : LinearRankAggregationRule Voter n (LinearFeasibleRanking features))
    (hloss_nonnegative : ∀ input, 0 ≤ loss input)
    (hloss_nonpositive_lower : ∀ input, input ≤ 0 → loss 0 ≤ loss input)
    (hminimizes : IsStandardLossMinimizing features loss rule)
    (hprofile_feasible : FeasibleProfile (LinearFeasibleRanking features) profile)
    {first second : Candidate n}
    (huniversal : UniversallyPreferred profile first second)
    (witness : LinearRewardParameter dimension)
    (hwitness : standardLoss features profile loss witness < loss 0) :
    ¬ StrictlyPrefers (rule.run profile) first second := by
  intro houtput
  have hrestricted_nonempty :
      (standardLoss features profile loss ''
        { parameter | InducesRanking features parameter (rule.run profile) }).Nonempty := by
    rcases rule.output_feasible profile with ⟨parameter, _hnondegenerate, hinduced⟩
    exact ⟨standardLoss features profile loss parameter, ⟨parameter, hinduced, rfl⟩⟩
  have hrestricted_below : BddBelow
      (standardLoss features profile loss ''
        { parameter | InducesRanking features parameter (rule.run profile) }) := by
    refine ⟨0, ?_⟩
    rintro value ⟨parameter, _hinduced, rfl⟩
    exact standardLoss_nonnegative features profile loss parameter hloss_nonnegative
  have hrestricted_lower : loss 0 ≤
      restrictedStandardLossInfimum features profile loss (rule.run profile) := by
    unfold restrictedStandardLossInfimum
    apply le_csInf
    · exact hrestricted_nonempty
    · rintro value ⟨parameter, hinduced, rfl⟩
      exact loss_zero_le_standardLoss_of_universal_pair_of_nonpositive_lower
        features profile loss parameter (rule.run profile)
        hloss_nonnegative hloss_nonpositive_lower huniversal houtput hinduced
  have hglobal_below : BddBelow (Set.range (standardLoss features profile loss)) := by
    refine ⟨0, ?_⟩
    rintro value ⟨parameter, rfl⟩
    exact standardLoss_nonnegative features profile loss parameter hloss_nonnegative
  have hglobal_lt : globalStandardLossInfimum features profile loss < loss 0 := by
    unfold globalStandardLossInfimum
    exact (csInf_le hglobal_below ⟨witness, rfl⟩).trans_lt hwitness
  rw [hminimizes profile hprofile_feasible] at hrestricted_lower
  exact (not_lt_of_ge hrestricted_lower) hglobal_lt

/--
With a complete ranking, the preceding exclusion forces the reverse strict
order.  This turns the standard-loss witness into an explicit Pareto failure.
-/
theorem standardLossMinimizing_rule_reverses_universal_pair_of_witness
    {Voter : Type*} [Fintype Voter] [Nonempty Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (profile : RankingProfile Voter n) (loss : ℝ → ℝ)
    (rule : LinearRankAggregationRule Voter n (LinearFeasibleRanking features))
    (hloss_nonnegative : ∀ input, 0 ≤ loss input)
    (hloss_nonpositive_lower : ∀ input, input ≤ 0 → loss 0 ≤ loss input)
    (hminimizes : IsStandardLossMinimizing features loss rule)
    (hprofile_feasible : FeasibleProfile (LinearFeasibleRanking features) profile)
    {first second : Candidate n} (hdistinct : first ≠ second)
    (huniversal : UniversallyPreferred profile first second)
    (witness : LinearRewardParameter dimension)
    (hwitness : standardLoss features profile loss witness < loss 0) :
    StrictlyPrefers (rule.run profile) second first := by
  rcases strictlyPrefers_or_reverse_of_ne (rule.run profile) hdistinct with hforward | hreverse
  · exact False.elim
      (standardLossMinimizing_rule_not_orders_universal_pair_of_witness
        features profile loss rule hloss_nonnegative hloss_nonpositive_lower hminimizes
        hprofile_feasible huniversal witness hwitness hforward)
  · exact hreverse

/--
The explicit strict reversal above violates Pareto optimality whenever the
unanimous input profile is feasible.
-/
theorem not_paretoOptimal_of_standardLoss_witness
    {Voter : Type*} [Fintype Voter] [Nonempty Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (profile : RankingProfile Voter n) (loss : ℝ → ℝ)
    (rule : LinearRankAggregationRule Voter n (LinearFeasibleRanking features))
    (hloss_nonnegative : ∀ input, 0 ≤ loss input)
    (hloss_nonpositive_lower : ∀ input, input ≤ 0 → loss 0 ≤ loss input)
    (hminimizes : IsStandardLossMinimizing features loss rule)
    {first second : Candidate n} (hdistinct : first ≠ second)
    (hprofile_feasible : FeasibleProfile (LinearFeasibleRanking features) profile)
    (huniversal : UniversallyPreferred profile first second)
    (witness : LinearRewardParameter dimension)
    (hwitness : standardLoss features profile loss witness < loss 0) :
    ¬ ParetoOptimal (LinearFeasibleRanking features) rule := by
  intro hpareto
  have hforward : StrictlyPrefers (rule.run profile) first second :=
    hpareto profile first second hprofile_feasible huniversal
  have hreverse : StrictlyPrefers (rule.run profile) second first :=
    standardLossMinimizing_rule_reverses_universal_pair_of_witness
      features profile loss rule hloss_nonnegative hloss_nonpositive_lower hminimizes
      hprofile_feasible hdistinct huniversal witness hwitness
  exact (not_lt_of_ge hforward.le) hreverse

/--
The same standard-loss witness also refutes pairwise majority consistency
whenever the submitted profile itself realizes the stated majority ranking.
This keeps the PO and PMC conclusions of the positive-input branch separate:
the loss calculation supplies a reversal, and this theorem applies the
definition of PMC to that reversal.
-/
theorem not_pairwiseMajorityConsistent_of_standardLoss_witness
    {Voter : Type*} [Fintype Voter] [Nonempty Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (profile : RankingProfile Voter n) (inputRanking : Ranking n) (loss : ℝ → ℝ)
    (rule : LinearRankAggregationRule Voter n (LinearFeasibleRanking features))
    (hloss_nonnegative : ∀ input, 0 ≤ loss input)
    (hloss_nonpositive_lower : ∀ input, input ≤ 0 → loss 0 ≤ loss input)
    (hminimizes : IsStandardLossMinimizing features loss rule)
    {first second : Candidate n} (hdistinct : first ≠ second)
    (hprofile_feasible : FeasibleProfile (LinearFeasibleRanking features) profile)
    (hinput_feasible : LinearFeasibleRanking features inputRanking)
    (hinput_majority : IsPairwiseMajorityRanking profile inputRanking)
    (hinput_prefers : StrictlyPrefers inputRanking first second)
    (huniversal : UniversallyPreferred profile first second)
    (witness : LinearRewardParameter dimension)
    (hwitness : standardLoss features profile loss witness < loss 0) :
    ¬ PairwiseMajorityConsistent (LinearFeasibleRanking features) rule := by
  intro hpmc
  have houtput_eq : rule.run profile = inputRanking :=
    hpmc profile inputRanking hprofile_feasible hinput_feasible hinput_majority
  have hforward : StrictlyPrefers (rule.run profile) first second := by
    rw [houtput_eq]
    exact hinput_prefers
  have hreverse : StrictlyPrefers (rule.run profile) second first :=
    standardLossMinimizing_rule_reverses_universal_pair_of_witness
      features profile loss rule hloss_nonnegative hloss_nonpositive_lower hminimizes
      hprofile_feasible hdistinct huniversal witness hwitness
  exact (not_lt_of_ge hforward.le) hreverse

/--
The direct ranking-level inference used at the end of the six-candidate
branch of Theorem 3.1.  Lemma 3.5 is intended to provide exactly the
strict infimum gap for every output ranking that puts the unanimous pair in
the wrong direction.
-/
theorem standardLossMinimizing_rule_reverses_of_pairwise_infimum_gap
    {Voter : Type*} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (profile : RankingProfile Voter n) (loss : ℝ → ℝ)
    (rule : LinearRankAggregationRule Voter n (LinearFeasibleRanking features))
    (hminimizes : IsStandardLossMinimizing features loss rule)
    (hprofile_feasible : FeasibleProfile (LinearFeasibleRanking features) profile)
    {first second : Candidate n} (hdistinct : first ≠ second)
    (hgap : ∀ output, StrictlyPrefers output first second →
      globalStandardLossInfimum features profile loss <
        restrictedStandardLossInfimum features profile loss output) :
    StrictlyPrefers (rule.run profile) second first := by
  rcases strictlyPrefers_or_reverse_of_ne (rule.run profile) hdistinct with hforward | hreverse
  · have hstrict := hgap (rule.run profile) hforward
    rw [← hminimizes profile hprofile_feasible] at hstrict
    exact False.elim (lt_irrefl _ hstrict)
  · exact hreverse

/--
The strict infimum gap produced by the intended Lemma 3.5 conclusion gives a
Pareto violation as soon as all voters submit the opposite strict pair.
-/
theorem not_paretoOptimal_of_pairwise_infimum_gap
    {Voter : Type*} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (profile : RankingProfile Voter n) (loss : ℝ → ℝ)
    (rule : LinearRankAggregationRule Voter n (LinearFeasibleRanking features))
    (hminimizes : IsStandardLossMinimizing features loss rule)
    {first second : Candidate n} (hdistinct : first ≠ second)
    (hprofile_feasible : FeasibleProfile (LinearFeasibleRanking features) profile)
    (huniversal : UniversallyPreferred profile first second)
    (hgap : ∀ output, StrictlyPrefers output first second →
      globalStandardLossInfimum features profile loss <
        restrictedStandardLossInfimum features profile loss output) :
    ¬ ParetoOptimal (LinearFeasibleRanking features) rule := by
  intro hpareto
  have hforward : StrictlyPrefers (rule.run profile) first second :=
    hpareto profile first second hprofile_feasible huniversal
  have hreverse : StrictlyPrefers (rule.run profile) second first :=
    standardLossMinimizing_rule_reverses_of_pairwise_infimum_gap
      features profile loss rule hminimizes hprofile_feasible hdistinct hgap
  exact (not_lt_of_ge hforward.le) hreverse

/--
Likewise, if the unanimous ranking is the feasible pairwise-majority ranking,
the same gap rules out pairwise majority consistency.
-/
theorem not_pairwiseMajorityConsistent_of_pairwise_infimum_gap
    {Voter : Type*} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (profile : RankingProfile Voter n) (inputRanking : Ranking n) (loss : ℝ → ℝ)
    (rule : LinearRankAggregationRule Voter n (LinearFeasibleRanking features))
    (hminimizes : IsStandardLossMinimizing features loss rule)
    {first second : Candidate n} (hdistinct : first ≠ second)
    (hprofile_feasible : FeasibleProfile (LinearFeasibleRanking features) profile)
    (hinput_feasible : LinearFeasibleRanking features inputRanking)
    (hinput_majority : IsPairwiseMajorityRanking profile inputRanking)
    (hinput_prefers : StrictlyPrefers inputRanking first second)
    (hgap : ∀ output, StrictlyPrefers output first second →
      globalStandardLossInfimum features profile loss <
        restrictedStandardLossInfimum features profile loss output) :
    ¬ PairwiseMajorityConsistent (LinearFeasibleRanking features) rule := by
  intro hpmc
  have houtput_eq : rule.run profile = inputRanking :=
    hpmc profile inputRanking hprofile_feasible hinput_feasible hinput_majority
  have hforward : StrictlyPrefers (rule.run profile) first second := by
    rw [houtput_eq]
    exact hinput_prefers
  have hreverse : StrictlyPrefers (rule.run profile) second first :=
    standardLossMinimizing_rule_reverses_of_pairwise_infimum_gap
      features profile loss rule hminimizes hprofile_feasible hdistinct hgap
  exact (not_lt_of_ge hforward.le) hreverse

/--
The elementary strict-convexity fact used in the positive-input branch of
source Theorem 3.1.  If a strictly convex loss drops below its value at zero
at a positive input, then it cannot also be below that value at a
nonpositive input: zero would be a strict interior convex combination of the
two inputs and would have to lie strictly below both endpoint values.
-/
theorem strictConvexOn_nonpositive_lower_of_positive_dip
    {loss : ℝ → ℝ} {x : ℝ}
    (hstrict : StrictConvexOn ℝ Set.univ loss)
    (hxpos : 0 < x) (hdip : loss x < loss 0) :
    ∀ y, y ≤ 0 → loss 0 ≤ loss y := by
  intro y hy
  rcases hy.eq_or_lt with rfl | hyneg
  · exact le_rfl
  let a : ℝ := x / (x - y)
  let b : ℝ := -y / (x - y)
  have hden : 0 < x - y := by linarith
  have hden_ne : x - y ≠ 0 := ne_of_gt hden
  have ha : 0 < a := by
    exact div_pos hxpos hden
  have hb : 0 < b := by
    exact div_pos (neg_pos.mpr hyneg) hden
  have hab : a + b = 1 := by
    dsimp [a, b]
    field_simp
    ring
  have hzero : a * y + b * x = 0 := by
    dsimp [a, b]
    field_simp
    ring
  have hne : y ≠ x := ne_of_lt (lt_trans hyneg hxpos)
  have hjensen := hstrict.2 (Set.mem_univ y) (Set.mem_univ x) hne ha hb hab
  have hjensen' : loss 0 < a * loss y + b * loss x := by
    rw [show a • y + b • x = (0 : ℝ) by simpa only [smul_eq_mul] using hzero] at hjensen
    simpa only [smul_eq_mul] using hjensen
  by_contra hnot
  have hylt : loss y < loss 0 := lt_of_not_ge hnot
  have hleft : a * loss y < a * loss 0 := mul_lt_mul_of_pos_left hylt ha
  have hright : b * loss x < b * loss 0 := mul_lt_mul_of_pos_left hdip hb
  have hupper : a * loss y + b * loss x < loss 0 := by
    calc
      a * loss y + b * loss x < a * loss 0 + b * loss 0 := add_lt_add hleft hright
      _ = loss 0 := by rw [← add_mul, hab, one_mul]
  exact (not_lt_of_ge hupper.le) hjensen'

/-- The two feature vectors in the positive-input endpoint of Theorem 3.1. -/
noncomputable def positiveInputFeatures : Candidate 0 → FeatureVector 2 :=
  fun candidate coordinate =>
    if candidate = 0 then
      if coordinate = 0 then 1 else 0
    else
      if coordinate = 0 then 0 else 1

/-- The single-voter input ranking `a ≻ b` in that endpoint. -/
noncomputable def positiveInputRanking : Ranking 0 := Equiv.refl _

/-- The source's one-voter profile for the positive-input endpoint. -/
noncomputable def positiveInputProfile : RankingProfile Unit 0 :=
  fun _ => positiveInputRanking

/-- On the source's two candidates, the reward coordinates are read directly. -/
theorem linearReward_positiveInputFeatures_zero
    (parameter : LinearRewardParameter 2) :
    linearReward parameter positiveInputFeatures (0 : Candidate 0) = parameter 0 := by
  rw [linearReward]
  simp [positiveInputFeatures]

/-- On the source's two candidates, the reward coordinates are read directly. -/
theorem linearReward_positiveInputFeatures_one
    (parameter : LinearRewardParameter 2) :
    linearReward parameter positiveInputFeatures (1 : Candidate 0) = parameter 1 := by
  rw [linearReward]
  simp [positiveInputFeatures]

/-- The nondegenerate parameter which realizes the input order `a ≻ b`. -/
noncomputable def positiveInputFeasibleParameter : LinearRewardParameter 2 :=
  fun coordinate => if coordinate = 0 then 1 else 0

/-- The source's input ranking places the first candidate above the second. -/
theorem strictlyPrefers_positiveInputRanking_zero_one :
    StrictlyPrefers positiveInputRanking (0 : Candidate 0) 1 := by
  norm_num [StrictlyPrefers, positiveInputRanking, rankOf]

/-- The one-voter input ranking in the positive-input endpoint is feasible. -/
theorem linearFeasibleRanking_positiveInputRanking :
    LinearFeasibleRanking positiveInputFeatures positiveInputRanking := by
  refine ⟨positiveInputFeasibleParameter, ?_, ?_⟩
  · intro first second hdistinct
    fin_cases first <;> fin_cases second
    all_goals simp_all [positiveInputFeasibleParameter,
      linearReward_positiveInputFeatures_zero, linearReward_positiveInputFeatures_one]
  · intro first second hpreference
    fin_cases first <;> fin_cases second
    all_goals simp_all [StrictlyPrefers, positiveInputRanking, rankOf,
      positiveInputFeasibleParameter, linearReward_positiveInputFeatures_zero,
      linearReward_positiveInputFeatures_one]

/-- The single submitted ranking in the positive-input endpoint is feasible. -/
theorem feasibleProfile_positiveInputProfile :
    FeasibleProfile (LinearFeasibleRanking positiveInputFeatures) positiveInputProfile := by
  intro voter
  exact linearFeasibleRanking_positiveInputRanking

/-- Every voter in the positive-input endpoint ranks the first candidate above the second. -/
theorem universallyPreferred_positiveInputProfile_zero_one :
    UniversallyPreferred positiveInputProfile (0 : Candidate 0) 1 := by
  intro voter
  exact strictlyPrefers_positiveInputRanking_zero_one

/-- With one voter, the submitted two-candidate ranking realizes every strict majority. -/
theorem isPairwiseMajorityRanking_positiveInputProfile :
    IsPairwiseMajorityRanking positiveInputProfile positiveInputRanking := by
  classical
  intro first second
  fin_cases first <;> fin_cases second <;>
    simp [StrictMajorityPrefers, StrictMajority,
      votersSatisfying, positiveInputProfile, positiveInputRanking,
      StrictlyPrefers, rankOf]

/-- The parameter which gives reward gap `x` in the positive-input endpoint. -/
noncomputable def positiveInputWitness (x : ℝ) : LinearRewardParameter 2 :=
  fun coordinate => if coordinate = 0 then 0 else x

/-- On the source's one-voter profile, this witness has exactly loss `ℓ(x)`. -/
theorem standardLoss_positiveInputWitness
    (loss : ℝ → ℝ) (x : ℝ) :
    standardLoss positiveInputFeatures positiveInputProfile loss (positiveInputWitness x) = loss x := by
  classical
  simp only [standardLoss, positiveInputProfile, Fintype.sum_unique]
  rw [Fintype.sum_prod_type]
  simp only [StrictlyPrefers, positiveInputRanking, rankOf]
  change (∑ first : Fin 2, ∑ second : Fin 2,
    if first < second then
      loss
        (linearReward (positiveInputWitness x) positiveInputFeatures second -
          linearReward (positiveInputWitness x) positiveInputFeatures first)
    else 0) = loss x
  repeat rw [Fin.sum_univ_two]
  simp [positiveInputWitness,
    linearReward_positiveInputFeatures_zero, linearReward_positiveInputFeatures_one]

/--
The positive-input endpoint of source Theorem 3.1, fully instantiated on its
two candidates and one voter.  Strict convexity supplies the lower bound on
parameters preserving the unanimous order; the witness with gap `x` lies
strictly below that bound, forcing both PO and PMC failure.
-/
theorem positiveInput_branch_fails_pareto_and_pmc
    {loss : ℝ → ℝ} {x : ℝ}
    (hloss_nonnegative : ∀ input, 0 ≤ loss input)
    (hstrict : StrictConvexOn ℝ Set.univ loss)
    (hxpos : 0 < x) (hdip : loss x < loss 0)
    (rule : LinearRankAggregationRule Unit 0 (LinearFeasibleRanking positiveInputFeatures))
    (hminimizes : IsStandardLossMinimizing positiveInputFeatures loss rule) :
    ¬ ParetoOptimal (LinearFeasibleRanking positiveInputFeatures) rule ∧
      ¬ PairwiseMajorityConsistent (LinearFeasibleRanking positiveInputFeatures) rule := by
  have hnonpositive_lower : ∀ input, input ≤ 0 → loss 0 ≤ loss input :=
    strictConvexOn_nonpositive_lower_of_positive_dip hstrict hxpos hdip
  have hdistinct : (0 : Candidate 0) ≠ 1 := by norm_num
  have hwitness :
      standardLoss positiveInputFeatures positiveInputProfile loss (positiveInputWitness x) <
        loss 0 := by
    rw [standardLoss_positiveInputWitness]
    exact hdip
  constructor
  · exact not_paretoOptimal_of_standardLoss_witness
      positiveInputFeatures positiveInputProfile loss rule hloss_nonnegative hnonpositive_lower
      hminimizes hdistinct feasibleProfile_positiveInputProfile
      universallyPreferred_positiveInputProfile_zero_one (positiveInputWitness x) hwitness
  · exact not_pairwiseMajorityConsistent_of_standardLoss_witness
      positiveInputFeatures positiveInputProfile positiveInputRanking loss rule
      hloss_nonnegative hnonpositive_lower hminimizes hdistinct
      feasibleProfile_positiveInputProfile linearFeasibleRanking_positiveInputRanking
      isPairwiseMajorityRanking_positiveInputProfile
      strictlyPrefers_positiveInputRanking_zero_one
      universallyPreferred_positiveInputProfile_zero_one (positiveInputWitness x) hwitness

/--
For the nondecreasing alternative in Theorem 3.1, any strict loss decrease
below `loss 0` is necessarily at a negative input.  Thus only the
six-candidate branch can arise in that alternative.
-/
theorem exists_negative_dip_of_monotone
    {loss : ℝ → ℝ} (hmonotone : Monotone loss)
    (hexists : ∃ input, loss input < loss 0) :
    ∃ negativeInput, negativeInput < 0 ∧ loss negativeInput < loss 0 := by
  obtain ⟨input, hdip⟩ := hexists
  refine ⟨input, ?_, hdip⟩
  by_contra hnot
  have hnonnegative : 0 ≤ input := le_of_not_gt hnot
  exact (not_lt_of_ge (hmonotone hnonnegative)) hdip

/--
The affine lower bound used at the start of Appendix A.1.  A convex loss
which is lower at a negative input than at zero must grow at least linearly
to the right of zero.  The denominator-free form makes the eventual tail
bound explicit without introducing an unverified limit argument.
-/
theorem convex_right_affine_lower_bound_of_negative_dip
    {loss : ℝ → ℝ} {negativeInput positiveInput : ℝ}
    (hconvex : ConvexOn ℝ Set.univ loss)
    (hnegative : negativeInput < 0) (hpositive : 0 < positiveInput) :
    positiveInput * (loss 0 - loss negativeInput) - negativeInput * loss 0 ≤
      -negativeInput * loss positiveInput := by
  let a : ℝ := positiveInput / (positiveInput - negativeInput)
  let b : ℝ := -negativeInput / (positiveInput - negativeInput)
  have hden : 0 < positiveInput - negativeInput := by linarith
  have ha : 0 ≤ a := (div_nonneg hpositive.le hden.le)
  have hb : 0 ≤ b := div_nonneg (neg_nonneg.mpr hnegative.le) hden.le
  have hab : a + b = 1 := by
    dsimp [a, b]
    field_simp
    ring
  have hzero : a * negativeInput + b * positiveInput = 0 := by
    dsimp [a, b]
    field_simp
    ring
  have hjensen := hconvex.2 (Set.mem_univ negativeInput) (Set.mem_univ positiveInput)
    ha hb hab
  have hjensen' : loss 0 ≤
      (positiveInput * loss negativeInput + (-negativeInput) * loss positiveInput) /
        (positiveInput - negativeInput) := by
    calc
      loss 0 = loss (a • negativeInput + b • positiveInput) := by
        rw [show a • negativeInput + b • positiveInput = (0 : ℝ) by
          simpa only [smul_eq_mul] using hzero]
      _ ≤ a • loss negativeInput + b • loss positiveInput := hjensen
      _ = (positiveInput * loss negativeInput + (-negativeInput) * loss positiveInput) /
          (positiveInput - negativeInput) := by
        dsimp [a, b]
        field_simp
  have hscaled : loss 0 * (positiveInput - negativeInput) ≤
      positiveInput * loss negativeInput + (-negativeInput) * loss positiveInput :=
    (le_div_iff₀ hden).mp hjensen'
  linarith

/--
The source's claimed right-tail consequence, stated in an elementary form:
every finite threshold is eventually exceeded.  This follows directly from
the checked affine lower bound and avoids treating a limit-to-infinity claim
as an unproved analytic black box.
-/
theorem exists_right_tail_gt_of_convex_negative_dip
    {loss : ℝ → ℝ} {negativeInput : ℝ}
    (hconvex : ConvexOn ℝ Set.univ loss)
    (hnegative : negativeInput < 0)
    (hdip : loss negativeInput < loss 0) (threshold : ℝ) :
    ∃ bound > 0, ∀ input, bound < input → threshold < loss input := by
  let gap : ℝ := loss 0 - loss negativeInput
  have hgap : 0 < gap := by
    dsimp [gap]
    linarith
  let quotient : ℝ := (-negativeInput) * (threshold - loss 0) / gap
  let bound : ℝ := max 0 quotient + 1
  have hbound_pos : 0 < bound := by
    dsimp [bound]
    linarith [le_max_left (0 : ℝ) quotient]
  refine ⟨bound, hbound_pos, ?_⟩
  intro input hlarge
  have hinput_pos : 0 < input := lt_trans hbound_pos hlarge
  have hquotient_lt_input : quotient < input := by
    have hquotient_le : quotient ≤ max 0 quotient := le_max_right _ _
    dsimp [bound] at hlarge
    linarith
  have hscaled_threshold :
      (-negativeInput) * (threshold - loss 0) < gap * input := by
    dsimp [quotient] at hquotient_lt_input
    simpa [mul_comm] using (div_lt_iff₀ hgap).mp hquotient_lt_input
  have haffine := convex_right_affine_lower_bound_of_negative_dip hconvex
    hnegative hinput_pos
  have hscaled_loss : (-negativeInput) * threshold < (-negativeInput) * loss input := by
    dsimp [gap] at hscaled_threshold
    linarith
  nlinarith [neg_pos.mpr hnegative]

/-- The source's weighted two-direction loss `g(x)`. -/
def weightedLoss (p : ℝ) (loss : ℝ → ℝ) (x : ℝ) : ℝ :=
  p * loss (-x) + (1 - p) * loss x

/-- The unconstrained two-reward objective in the proof of source Lemma 3.2. -/
def unconstrainedCoreLoss (g : ℝ → ℝ) (rewards : ℝ × ℝ) : ℝ :=
  g (rewards.1 - rewards.2) + g rewards.1 + g rewards.2

/-- A point minimizes a real-valued objective over all of its stated domain. -/
def IsGlobalMinimizer {α : Type*} (objective : α → ℝ) (point : α) : Prop :=
  ∀ contender, objective point ≤ objective contender

/-- A compact reward square used to localize the source's unconstrained problem. -/
def coreRewardSquare (bound : ℝ) : Set (ℝ × ℝ) :=
  Set.Icc (-bound) bound ×ˢ Set.Icc (-bound) bound

/-- The finite reward square is compact. -/
theorem isCompact_coreRewardSquare (bound : ℝ) :
    IsCompact (coreRewardSquare bound) := by
  exact isCompact_Icc.prod isCompact_Icc

/-- The zero reward pair belongs to the square whenever its bound is nonnegative. -/
theorem zero_mem_coreRewardSquare {bound : ℝ} (hbound : 0 ≤ bound) :
    (0, 0) ∈ coreRewardSquare bound := by
  rw [coreRewardSquare, Set.mem_prod]
  constructor <;> exact ⟨neg_nonpos.mpr hbound, hbound⟩

/--
Joint continuity gives a uniform small-perturbation estimate after restricting
parameters to a compact set.  This is the precise compact version needed for
argmin stability; joint continuity alone cannot supply such an estimate on an
unbounded parameter space.
-/
theorem continuous_uniformPerturbation_on_compact
    (objective : ℝ → (ℝ × ℝ) → ℝ) (compact : Set (ℝ × ℝ))
    (hcompact : IsCompact compact)
    (hcontinuous : Continuous (fun input : ℝ × (ℝ × ℝ) =>
      objective input.1 input.2)) :
    ∀ tolerance : ℝ, 0 < tolerance → ∃ radius : ℝ, 0 < radius ∧
      ∀ ε, |ε| < radius → ∀ parameter, parameter ∈ compact →
        |objective ε parameter - objective 0 parameter| < tolerance := by
  letI : CompactSpace { parameter // parameter ∈ compact } :=
    isCompact_iff_compactSpace.mp hcompact
  let restricted : ℝ → { parameter // parameter ∈ compact } → ℝ :=
    fun ε parameter => objective ε parameter.1
  have hrestricted : Continuous (Function.uncurry restricted) := by
    change Continuous (fun input : ℝ × { parameter // parameter ∈ compact } =>
      objective input.1 input.2.1)
    exact hcontinuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have htendsto : TendstoUniformly restricted (restricted 0) (𝓝 0) :=
    Continuous.tendstoUniformly restricted hrestricted 0
  intro tolerance htolerance
  let close : Set (ℝ × ℝ) := { values | dist values.1 values.2 < tolerance }
  have hclose : close ∈ 𝓤 ℝ := by
    exact Metric.dist_mem_uniformity htolerance
  have hevent :
      { ε | ∀ parameter : { parameter // parameter ∈ compact },
          (restricted 0 parameter, restricted ε parameter) ∈ close } ∈ 𝓝 0 :=
    htendsto close hclose
  obtain ⟨radius, hradius_pos, hball⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨radius, hradius_pos, ?_⟩
  intro ε hε parameter hparameter
  have hε_ball : ε ∈ Metric.ball 0 radius := by
    simpa [Metric.mem_ball, Real.dist_eq] using hε
  have hpair := hball hε_ball ⟨parameter, hparameter⟩
  change dist (objective 0 parameter) (objective ε parameter) < tolerance at hpair
  simpa [Real.dist_eq, abs_sub_comm] using hpair

/--
A continuous objective whose values outside a compact set are strictly worse
than a point in that set has a global minimizer.  This is the compactness step
used in the first paragraph of Appendix A.1.
-/
theorem exists_globalMinimizer_of_compact_capture
    {objective : (ℝ × ℝ) → ℝ} {capture : Set (ℝ × ℝ)}
    (hcompact : IsCompact capture) (hcontinuous : Continuous objective)
    {base : ℝ × ℝ} (hbase : base ∈ capture)
    (houtside : ∀ contender, contender ∉ capture → objective base < objective contender) :
    ∃ point, IsGlobalMinimizer objective point := by
  obtain ⟨point, hpoint, hminimum⟩ :=
    hcompact.exists_isMinOn ⟨base, hbase⟩ hcontinuous.continuousOn
  refine ⟨point, ?_⟩
  intro contender
  by_cases hcontender : contender ∈ capture
  · exact hminimum hcontender
  · exact le_trans (hminimum hbase) (le_of_lt (houtside contender hcontender))

/-- Continuity of the source's unconstrained two-reward objective. -/
theorem continuous_unconstrainedCoreLoss
    {g : ℝ → ℝ} (hcontinuous : Continuous g) :
    Continuous (unconstrainedCoreLoss g) := by
  have hdifference : Continuous (fun rewards : ℝ × ℝ => rewards.1 - rewards.2) :=
    continuous_fst.sub continuous_snd
  have hfirst : Continuous (fun rewards : ℝ × ℝ => g (rewards.1 - rewards.2)) :=
    hcontinuous.comp hdifference
  have hsecond : Continuous (fun rewards : ℝ × ℝ => g rewards.1) :=
    hcontinuous.comp continuous_fst
  have hthird : Continuous (fun rewards : ℝ × ℝ => g rewards.2) :=
    hcontinuous.comp continuous_snd
  simpa [unconstrainedCoreLoss] using (hfirst.add hsecond).add hthird

/--
The compactness half of source Lemma 3.2: nonnegative tails that exceed the
value at zero force the unconstrained core loss to attain a global minimum.
-/
theorem exists_unconstrainedCoreLoss_minimizer_of_tail_bound
    {g : ℝ → ℝ} {bound : ℝ} (hbound : 0 ≤ bound)
    (hcontinuous : Continuous g) (hnonnegative : ∀ x, 0 ≤ g x)
    (htail : ∀ x, bound < |x| → 3 * g 0 < g x) :
    ∃ rewards, IsGlobalMinimizer (unconstrainedCoreLoss g) rewards := by
  apply exists_globalMinimizer_of_compact_capture
    (isCompact_coreRewardSquare bound)
    (continuous_unconstrainedCoreLoss hcontinuous)
    (zero_mem_coreRewardSquare hbound)
  intro contender hnotin
  have hcoordinate : bound < |contender.1| ∨ bound < |contender.2| := by
    by_contra hnotlarge
    push Not at hnotlarge
    apply hnotin
    rw [coreRewardSquare, Set.mem_prod]
    constructor
    · exact abs_le.mp hnotlarge.1
    · exact abs_le.mp hnotlarge.2
  have hzero : unconstrainedCoreLoss g (0, 0) = 3 * g 0 := by
    simp [unconstrainedCoreLoss]
    ring
  rw [hzero]
  rcases hcoordinate with hfirst | hsecond
  · have hlarge := htail contender.1 hfirst
    have hremainingOne := hnonnegative (contender.1 - contender.2)
    have hremainingTwo := hnonnegative contender.2
    dsimp [unconstrainedCoreLoss]
    linarith
  · have hlarge := htail contender.2 hsecond
    have hremainingOne := hnonnegative (contender.1 - contender.2)
    have hremainingTwo := hnonnegative contender.1
    dsimp [unconstrainedCoreLoss]
    linarith

/-- The source's replacement of `(rₐ, r_b)` by `(rₐ, rₐ / 2)`. -/
noncomputable def symmetrizedRewards (rewards : ℝ × ℝ) : ℝ × ℝ :=
  (rewards.1, rewards.1 / 2)

/-- Jensen's midpoint inequality in the exact scalar form used below. -/
theorem convex_midpoint_le
    {g : ℝ → ℝ} (hconvex : ConvexOn ℝ Set.univ g) (x y : ℝ) :
    g ((x + y) / 2) ≤ (g x + g y) / 2 := by
  have h := hconvex.2 (Set.mem_univ x) (Set.mem_univ y)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have h' : g ((1 / 2 : ℝ) * x + (1 / 2 : ℝ) * y) ≤
      (1 / 2 : ℝ) * g x + (1 / 2 : ℝ) * g y := by
    simpa only [smul_eq_mul] using h
  calc
    g ((x + y) / 2) = g ((1 / 2 : ℝ) * x + (1 / 2 : ℝ) * y) := by
      congr 1
      ring
    _ ≤ (1 / 2 : ℝ) * g x + (1 / 2 : ℝ) * g y := h'
    _ = (g x + g y) / 2 := by ring

/-- Precomposing a real convex function with negation preserves convexity. -/
theorem convexOn_neg_comp
    {loss : ℝ → ℝ} (hconvex : ConvexOn ℝ Set.univ loss) :
    ConvexOn ℝ Set.univ (fun x => loss (-x)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have h := hconvex.2 (Set.mem_univ (-x)) (Set.mem_univ (-y)) ha hb hab
  have hneg : a * -x + b * -y = -(a * x + b * y) := by ring
  simpa only [smul_eq_mul, hneg] using h

/-- Precomposing a real convex function with a linear scalar map preserves convexity. -/
theorem convexOn_mul_comp
    {g : ℝ → ℝ} (hconvex : ConvexOn ℝ Set.univ g) (scale : ℝ) :
    ConvexOn ℝ Set.univ (fun x => g (scale * x)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have h := hconvex.2 (Set.mem_univ (scale * x)) (Set.mem_univ (scale * y)) ha hb hab
  have hscale : scale * (a * x + b * y) = a * (scale * x) + b * (scale * y) := by ring
  simpa only [smul_eq_mul, hscale] using h

/-- The weighted bidirectional loss `g` is convex when the base loss is convex. -/
theorem weightedLoss_convex
    {p : ℝ} {loss : ℝ → ℝ} (hp_nonneg : 0 ≤ p) (hp_le_one : p ≤ 1)
    (hconvex : ConvexOn ℝ Set.univ loss) :
    ConvexOn ℝ Set.univ (weightedLoss p loss) := by
  have hnegative := (convexOn_neg_comp hconvex).smul hp_nonneg
  have hpositive := hconvex.smul (sub_nonneg.mpr hp_le_one)
  simpa [weightedLoss, smul_eq_mul] using hnegative.add hpositive

/-- A weighted bidirectional loss is nonnegative when the base loss is. -/
theorem weightedLoss_nonnegative
    {p : ℝ} {loss : ℝ → ℝ} (hp_nonneg : 0 ≤ p) (hp_le_one : p ≤ 1)
    (hloss_nonnegative : ∀ x, 0 ≤ loss x) (x : ℝ) :
    0 ≤ weightedLoss p loss x := by
  unfold weightedLoss
  exact add_nonneg
    (mul_nonneg hp_nonneg (hloss_nonnegative (-x)))
    (mul_nonneg (sub_nonneg.mpr hp_le_one) (hloss_nonnegative x))

/--
The Appendix A.4 lower bound for one oppositely submitted comparison.  When
the first ranking has at least half the weight, its bidirectional loss controls
the loss at the absolute reward gap.  This uses both monotonicity and the
source's nonnegativity normalization.
-/
theorem weightedLoss_abs_lower_bound
    {p : ℝ} {loss : ℝ → ℝ} (hp_half : 1 / 2 ≤ p) (hp_le_one : p ≤ 1)
    (hloss_nonnegative : ∀ x, 0 ≤ loss x) (hmonotone : Monotone loss)
    (x : ℝ) :
    (1 - p) * loss |x| ≤ weightedLoss p loss x := by
  have hp_complement : 1 - p ≤ p := by linarith
  have hfirst : (1 - p) * loss (-x) ≤ p * loss (-x) :=
    mul_le_mul_of_nonneg_right hp_complement (hloss_nonnegative _)
  have hsecond : (1 - p) * loss |x| ≤
      (1 - p) * (loss (-x) + loss x) := by
    have hcoefficient : 0 ≤ 1 - p := sub_nonneg.mpr hp_le_one
    apply mul_le_mul_of_nonneg_left ?_ hcoefficient
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
      linarith [hloss_nonnegative (-x)]
    · have hx' : x ≤ 0 := le_of_not_ge hx
      rw [abs_of_nonpos hx']
      linarith [hloss_nonnegative x]
  unfold weightedLoss
  linarith

/--
The rational-interval calculation in Appendix A.1, stated with the correctly
scaled derivative values
`z₁ = ℓ'_−(-w)`, `z₂ = ℓ'_−(-w/2)`,
`z₃ = ℓ'_+(w/2)`, and `z₄ = ℓ'_+(w)`.
The published text subsequently lists a shifted set of arguments, but the
displayed thresholds (2)--(3) and its inequality argument use these values.
-/
theorem exists_rational_between_four_point_thresholds
    {z1 z2 z3 z4 : ℝ}
    (hz1_nonnegative : 0 ≤ z1) (hz12 : z1 < z2)
    (hz23 : z2 ≤ z3) (hz34 : z3 ≤ z4) :
    ∃ p : ℚ,
      (1 / 2 : ℝ) < (p : ℝ) ∧ (p : ℝ) < 1 ∧
        (z3 + z4) / (z1 + z2 + z3 + z4) < (p : ℝ) ∧
          (p : ℝ) < z4 / (z1 + z4) := by
  have hz2_pos : 0 < z2 := lt_of_le_of_lt hz1_nonnegative hz12
  have hz3_pos : 0 < z3 := lt_of_lt_of_le hz2_pos hz23
  have hz4_pos : 0 < z4 := lt_of_lt_of_le hz3_pos hz34
  have htotal_pos : 0 < z1 + z2 + z3 + z4 := by linarith
  have hupper_den_pos : 0 < z1 + z4 := by linarith
  have hleft_right : z1 + z2 < z3 + z4 := by linarith
  have hhalf_lower : (1 / 2 : ℝ) < (z3 + z4) / (z1 + z2 + z3 + z4) := by
    apply (lt_div_iff₀ htotal_pos).mpr
    linarith
  have hproduct_left : z1 * z3 < z2 * z3 :=
    mul_lt_mul_of_pos_right hz12 hz3_pos
  have hproduct_right : z2 * z3 ≤ z2 * z4 :=
    mul_le_mul_of_nonneg_left hz34 hz2_pos.le
  have hproduct : z1 * z3 < z2 * z4 := hproduct_left.trans_le hproduct_right
  have hlower_upper :
      (z3 + z4) / (z1 + z2 + z3 + z4) < z4 / (z1 + z4) := by
    apply (div_lt_div_iff₀ htotal_pos hupper_den_pos).mpr
    nlinarith
  have hupper_le_one : z4 / (z1 + z4) ≤ (1 : ℝ) := by
    apply (div_le_iff₀ hupper_den_pos).mpr
    linarith
  obtain ⟨p, hlower_p, hp_upper⟩ := exists_rat_btwn hlower_upper
  refine ⟨p, hhalf_lower.trans hlower_p, hp_upper.trans_le hupper_le_one,
    hlower_p, hp_upper⟩

/-- The upper threshold in Appendix A.1 makes the weighted-loss right slope positive. -/
theorem weightedRightSlope_positive_of_lt_upper_threshold
    {p z1 z4 : ℝ} (hden_pos : 0 < z1 + z4)
    (hp : p < z4 / (z1 + z4)) :
    0 < -p * z1 + (1 - p) * z4 := by
  have hscaled : p * (z1 + z4) < z4 := (lt_div_iff₀ hden_pos).mp hp
  linarith

/-- The lower threshold in Appendix A.1 makes the reduced-loss right slope negative. -/
theorem reducedRightSlope_negative_of_gt_lower_threshold
    {p z1 z2 z3 z4 : ℝ} (htotal_pos : 0 < z1 + z2 + z3 + z4)
    (hp : (z3 + z4) / (z1 + z2 + z3 + z4) < p) :
    -p * (z1 + z2) + (1 - p) * (z3 + z4) < 0 := by
  have hscaled : z3 + z4 < p * (z1 + z2 + z3 + z4) :=
    (div_lt_iff₀ htotal_pos).mp hp
  linarith

/-- A strictly positive ordinary derivative gives a strict value increase from the left. -/
theorem exists_value_lt_of_hasDerivAt_pos
    {f : ℝ → ℝ} {point derivative : ℝ}
    (hderiv : HasDerivAt f derivative point) (hderivative_pos : 0 < derivative) :
    ∃ leftPoint, leftPoint < point ∧ f leftPoint < f point := by
  have hshifted : HasDerivAt (fun input => f input - f point) derivative point :=
    hderiv.sub_const (f point)
  have hsign : ∀ᶠ input in 𝓝 point,
      sign (f input - f point) = sign (input - point) :=
    eventually_nhdsWithin_sign_eq_of_deriv_pos (by
      rw [hshifted.deriv]
      exact hderivative_pos) (by ring)
  obtain ⟨radius, hradius_pos, hball⟩ := Metric.mem_nhds_iff.mp hsign
  refine ⟨point - radius / 2, by linarith, ?_⟩
  have hmem : dist (point - radius / 2) point < radius := by
    rw [Real.dist_eq]
    simp only [sub_sub_cancel_left]
    rw [abs_of_nonpos]
    · linarith
    · linarith
  have hsign_at := hball hmem
  have hnegative : f (point - radius / 2) - f point < 0 := by
    rw [← sign_eq_neg_one_iff, hsign_at, sign_eq_neg_one_iff]
    linarith
  linarith

/-- A strictly negative ordinary derivative gives a strict value decrease to the right. -/
theorem exists_value_lt_of_hasDerivAt_neg
    {f : ℝ → ℝ} {point derivative : ℝ}
    (hderiv : HasDerivAt f derivative point) (hderivative_neg : derivative < 0) :
    ∃ rightPoint, point < rightPoint ∧ f rightPoint < f point := by
  have hshifted : HasDerivAt (fun input => f input - f point) derivative point :=
    hderiv.sub_const (f point)
  have hsign : ∀ᶠ input in 𝓝 point,
      sign (f input - f point) = sign (point - input) :=
    eventually_nhdsWithin_sign_eq_of_deriv_neg (by
      rw [hshifted.deriv]
      exact hderivative_neg) (by ring)
  obtain ⟨radius, hradius_pos, hball⟩ := Metric.mem_nhds_iff.mp hsign
  refine ⟨point + radius / 2, by linarith, ?_⟩
  have hmem : dist (point + radius / 2) point < radius := by
    rw [Real.dist_eq]
    simp only [add_sub_cancel_left]
    rw [abs_of_nonneg]
    · linarith
    · linarith
  have hsign_at := hball hmem
  have hnegative : f (point + radius / 2) - f point < 0 := by
    rw [← sign_eq_neg_one_iff, hsign_at, sign_eq_neg_one_iff]
    linarith
  linarith

/--
From a strict negative-side dip and continuity at zero, one can choose a
strictly negative point closer to zero whose value is already above the dip.
This is the finite-value substitute for the source's informal local argument.
-/
theorem exists_negative_between_with_value_gt_of_continuous_negative_dip
    {loss : ℝ → ℝ} {negativeInput : ℝ}
    (hcontinuous : Continuous loss)
    (hnegative : negativeInput < 0) (hdip : loss negativeInput < loss 0) :
    ∃ point, negativeInput < point ∧ point < 0 ∧ loss negativeInput < loss point := by
  let valueRadius : ℝ := (loss 0 - loss negativeInput) / 2
  have hvalueRadius_pos : 0 < valueRadius := by
    dsimp [valueRadius]
    linarith
  obtain ⟨radius, hradius_pos, hnearContinuous⟩ :=
    (Metric.continuousAt_iff.mp hcontinuous.continuousAt) valueRadius hvalueRadius_pos
  let step : ℝ := min (radius / 2) ((-negativeInput) / 2)
  have hstep_pos : 0 < step := by
    dsimp [step]
    exact lt_min (half_pos hradius_pos) (half_pos (neg_pos.mpr hnegative))
  have hstep_lt_radius : step < radius := by
    have hstep_le : step ≤ radius / 2 := by
      dsimp [step]
      exact min_le_left _ _
    linarith
  have hnegative_lt_point : negativeInput < -step := by
    have hstep_le : step ≤ (-negativeInput) / 2 := by
      dsimp [step]
      exact min_le_right _ _
    linarith
  refine ⟨-step, hnegative_lt_point, neg_lt_zero.mpr hstep_pos, ?_⟩
  have hnear : dist (-step) 0 < radius := by
    rw [Real.dist_eq]
    have hargument : -step - 0 = -step := by ring
    rw [hargument, abs_neg]
    rw [abs_of_pos hstep_pos]
    exact hstep_lt_radius
  have hvalue_near := hnearContinuous hnear
  rw [Real.dist_eq] at hvalue_near
  rw [abs_lt] at hvalue_near
  dsimp [valueRadius] at hvalue_near
  linarith

/--
The corrected finite algebraic core of the source's derivative construction:
a rational mixture gives the stated opposite signs for the two right-slope
expressions.  Connecting these algebraic expressions to one-sided derivatives
of `weightedLoss` and `reducedCoreLoss` is the remaining calculus bridge.
-/
theorem exists_rational_mixture_with_four_point_slope_signs
    {z1 z2 z3 z4 : ℝ}
    (hz1_nonnegative : 0 ≤ z1) (hz12 : z1 < z2)
    (hz23 : z2 ≤ z3) (hz34 : z3 ≤ z4) :
    ∃ p : ℚ,
      (1 / 2 : ℝ) < (p : ℝ) ∧ (p : ℝ) < 1 ∧
        0 < -(p : ℝ) * z1 + (1 - (p : ℝ)) * z4 ∧
          -(p : ℝ) * (z1 + z2) +
            (1 - (p : ℝ)) * (z3 + z4) < 0 := by
  obtain ⟨p, hhalf_p, hp_one, hlower_p, hp_upper⟩ :=
    exists_rational_between_four_point_thresholds hz1_nonnegative hz12 hz23 hz34
  have hupper_den_pos : 0 < z1 + z4 := by
    have hz2_pos : 0 < z2 := lt_of_le_of_lt hz1_nonnegative hz12
    have hz3_pos : 0 < z3 := lt_of_lt_of_le hz2_pos hz23
    have hz4_pos : 0 < z4 := lt_of_lt_of_le hz3_pos hz34
    linarith
  have htotal_pos : 0 < z1 + z2 + z3 + z4 := by
    have hz2_pos : 0 < z2 := lt_of_le_of_lt hz1_nonnegative hz12
    have hz3_pos : 0 < z3 := lt_of_lt_of_le hz2_pos hz23
    have hz4_pos : 0 < z4 := lt_of_lt_of_le hz3_pos hz34
    linarith
  refine ⟨p, hhalf_p, hp_one,
    weightedRightSlope_positive_of_lt_upper_threshold hupper_den_pos hp_upper,
    reducedRightSlope_negative_of_gt_lower_threshold htotal_pos hlower_p⟩

/--
Right-tail growth of `ℓ` transfers to two-sided tail growth of the weighted
loss `g(x) = p ℓ(-x) + (1-p) ℓ(x)` when both directions have positive weight.
This is the coercivity bridge needed by the minimizer-existence paragraph of
Appendix A.1.
-/
theorem exists_weightedLoss_tail_bound_of_loss_rightTail
    {p target : ℝ} {loss : ℝ → ℝ}
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hloss_nonnegative : ∀ input, 0 ≤ loss input)
    (hrightTail : ∀ threshold : ℝ,
      ∃ bound > 0, ∀ input, bound < input → threshold < loss input) :
    ∃ bound > 0, ∀ input, bound < |input| →
      target < weightedLoss p loss input := by
  let positiveThreshold : ℝ := target / (1 - p)
  let negativeThreshold : ℝ := target / p
  obtain ⟨positiveBound, hpositiveBound_pos, hpositiveBound⟩ :=
    hrightTail positiveThreshold
  obtain ⟨negativeBound, hnegativeBound_pos, hnegativeBound⟩ :=
    hrightTail negativeThreshold
  let bound : ℝ := max positiveBound negativeBound
  have hbound_pos : 0 < bound := by
    dsimp [bound]
    exact lt_of_lt_of_le hpositiveBound_pos (le_max_left _ _)
  refine ⟨bound, hbound_pos, ?_⟩
  intro input hlarge
  by_cases hinput_nonnegative : 0 ≤ input
  · have habs : |input| = input := abs_of_nonneg hinput_nonnegative
    have hpositiveBound_lt : positiveBound < input := by
      have : positiveBound < |input| :=
        lt_of_le_of_lt (le_max_left _ _) hlarge
      simpa [habs] using this
    have hpositive_loss : positiveThreshold < loss input :=
      hpositiveBound input hpositiveBound_lt
    have hscaled : target < loss input * (1 - p) := by
      dsimp [positiveThreshold] at hpositive_loss
      exact (div_lt_iff₀ (sub_pos.mpr hp_lt_one)).mp hpositive_loss
    have hother_nonnegative : 0 ≤ p * loss (-input) :=
      mul_nonneg hp_pos.le (hloss_nonnegative _)
    have hmain : target < (1 - p) * loss input := by
      simpa only [mul_comm] using hscaled
    calc
      target < (1 - p) * loss input := hmain
      _ ≤ weightedLoss p loss input := by
        unfold weightedLoss
        linarith
  · have hinput_nonpositive : input ≤ 0 := le_of_not_ge hinput_nonnegative
    have habs : |input| = -input := abs_of_nonpos hinput_nonpositive
    have hnegativeBound_lt : negativeBound < -input := by
      have : negativeBound < |input| :=
        lt_of_le_of_lt (le_max_right _ _) hlarge
      simpa [habs] using this
    have hnegative_loss : negativeThreshold < loss (-input) :=
      hnegativeBound (-input) hnegativeBound_lt
    have hscaled : target < loss (-input) * p := by
      dsimp [negativeThreshold] at hnegative_loss
      exact (div_lt_iff₀ hp_pos).mp hnegative_loss
    have hother_nonnegative : 0 ≤ (1 - p) * loss input :=
      mul_nonneg (sub_nonneg.mpr hp_lt_one.le) (hloss_nonnegative _)
    have hmain : target < p * loss (-input) := by
      simpa only [mul_comm] using hscaled
    calc
      target < p * loss (-input) := hmain
      _ ≤ weightedLoss p loss input := by
        unfold weightedLoss
        linarith

/-- Continuity of the weighted bidirectional loss follows from continuity of `ℓ`. -/
theorem continuous_weightedLoss
    {p : ℝ} {loss : ℝ → ℝ} (hcontinuous : Continuous loss) :
    Continuous (weightedLoss p loss) := by
  have hnegative : Continuous (fun input : ℝ => loss (-input)) :=
    hcontinuous.comp continuous_neg
  have hfirst : Continuous (fun input : ℝ => p * loss (-input)) :=
    continuous_const.mul hnegative
  have hsecond : Continuous (fun input : ℝ => (1 - p) * loss input) :=
    continuous_const.mul hcontinuous
  simpa [weightedLoss] using hfirst.add hsecond

/-- A real-valued convex loss on all of `ℝ` is continuous, as used in Theorem 3.1. -/
theorem continuous_of_convexOn_univ
    {loss : ℝ → ℝ} (hconvex : ConvexOn ℝ Set.univ loss) : Continuous loss := by
  rw [← continuousOn_univ]
  exact hconvex.continuousOn isOpen_univ

/--
The minimizer-existence paragraph of Appendix A.1, under the source's
negative-dip case and the logically necessary interior-weight condition
`0 < p < 1`.  The later derivative argument is responsible for choosing such
a `p` together with the separation properties of its minimizers.
-/
theorem exists_unconstrainedCoreLoss_minimizer_of_convex_negative_dip
    {p : ℝ} {loss : ℝ → ℝ} {negativeInput : ℝ}
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hloss_nonnegative : ∀ input, 0 ≤ loss input)
    (hcontinuous : Continuous loss) (hconvex : ConvexOn ℝ Set.univ loss)
    (hnegative : negativeInput < 0) (hdip : loss negativeInput < loss 0) :
    ∃ rewards, IsGlobalMinimizer (unconstrainedCoreLoss (weightedLoss p loss)) rewards := by
  obtain ⟨bound, hbound_pos, htail⟩ :=
    exists_weightedLoss_tail_bound_of_loss_rightTail
      (target := 3 * weightedLoss p loss 0) hp_pos hp_lt_one hloss_nonnegative
      (fun threshold =>
        exists_right_tail_gt_of_convex_negative_dip hconvex hnegative hdip threshold)
  exact exists_unconstrainedCoreLoss_minimizer_of_tail_bound hbound_pos.le
    (continuous_weightedLoss hcontinuous)
    (fun input => weightedLoss_nonnegative hp_pos.le hp_lt_one.le hloss_nonnegative input)
    htail

/--
The convexity step in Appendix A.1: replacing the second reward by half the
first cannot increase the source's unconstrained core loss.
-/
theorem unconstrainedCoreLoss_symmetrized_le
    {g : ℝ → ℝ} (hconvex : ConvexOn ℝ Set.univ g) (rewards : ℝ × ℝ) :
    unconstrainedCoreLoss g (symmetrizedRewards rewards) ≤
      unconstrainedCoreLoss g rewards := by
  have hmidpoint := convex_midpoint_le hconvex
    (rewards.1 - rewards.2) rewards.2
  dsimp [unconstrainedCoreLoss, symmetrizedRewards]
  have hmidpoint' :
      g (rewards.1 / 2) ≤ (g (rewards.1 - rewards.2) + g rewards.2) / 2 := by
    simpa only [sub_add_cancel] using hmidpoint
  have hhalf : rewards.1 - rewards.1 / 2 = rewards.1 / 2 := by ring
  rw [hhalf]
  linarith only [hmidpoint']

/-- The one-variable core loss after the source's symmetrization reduction. -/
noncomputable def reducedCoreLoss (g : ℝ → ℝ) (reward : ℝ) : ℝ :=
  2 * g (reward / 2) + g reward

/-- Continuity transfers from the weighted loss to the reduced one-variable core loss. -/
theorem continuous_reducedCoreLoss
    {g : ℝ → ℝ} (hcontinuous : Continuous g) :
    Continuous (reducedCoreLoss g) := by
  have hhalf : Continuous (fun reward : ℝ => g (reward / 2)) :=
    hcontinuous.comp (continuous_id.div_const 2)
  simpa [reducedCoreLoss] using (continuous_const.mul hhalf).add hcontinuous

/-- Ordinary derivative rule for the source's weighted bidirectional loss. -/
theorem hasDerivAt_weightedLoss
    {p : ℝ} {loss : ℝ → ℝ} {point leftDerivative rightDerivative : ℝ}
    (hleft : HasDerivAt loss leftDerivative (-point))
    (hright : HasDerivAt loss rightDerivative point) :
    HasDerivAt (weightedLoss p loss)
      (-p * leftDerivative + (1 - p) * rightDerivative) point := by
  have hnegative : HasDerivAt (fun input => loss (-input)) (-leftDerivative) point := by
    simpa [Function.comp_def] using hleft.comp point (hasDerivAt_neg point)
  simpa [weightedLoss] using (hnegative.const_mul p).add (hright.const_mul (1 - p))

/--
One-sided right derivative rule for the source's weighted bidirectional loss.
The first summand uses the left derivative of `loss` because the negation map
sends points just right of `point` to points just left of `-point`.
-/
theorem hasDerivWithinAt_weightedLoss_right
    {p : ℝ} {loss : ℝ → ℝ} {point leftDerivative rightDerivative : ℝ}
    (hleft : HasDerivWithinAt loss leftDerivative (Set.Iio (-point)) (-point))
    (hright : HasDerivWithinAt loss rightDerivative (Set.Ioi point) point) :
    HasDerivWithinAt (weightedLoss p loss)
      (-p * leftDerivative + (1 - p) * rightDerivative) (Set.Ioi point) point := by
  have hnegBase : HasDerivWithinAt (fun input : ℝ => -input) (-1) (Set.Ioi point) point :=
    (hasDerivAt_neg point).hasDerivWithinAt
  have hmaps : Set.MapsTo (fun input : ℝ => -input) (Set.Ioi point) (Set.Iio (-point)) := by
    intro input hinput
    change point < input at hinput
    change -input < -point
    linarith
  have hnegative : HasDerivWithinAt (fun input => loss (-input)) (-leftDerivative)
      (Set.Ioi point) point := by
    simpa [Function.comp_def] using hleft.comp point hnegBase hmaps
  simpa [weightedLoss] using (hnegative.const_mul p).add (hright.const_mul (1 - p))

/-- Ordinary derivative rule for the one-variable core loss. -/
theorem hasDerivAt_reducedCoreLoss
    {g : ℝ → ℝ} {point halfDerivative derivative : ℝ}
    (hhalf : HasDerivAt g halfDerivative (point / 2))
    (hfull : HasDerivAt g derivative point) :
    HasDerivAt (reducedCoreLoss g) (halfDerivative + derivative) point := by
  have hhalf_composed : HasDerivAt (fun input => g (input / 2))
      (halfDerivative / 2) point := by
    simpa [Function.comp_def] using hhalf.comp point ((hasDerivAt_id point).div_const 2)
  convert (hhalf_composed.const_mul 2).add hfull using 1
  ring

/-- One-sided right derivative rule for the source's one-variable core loss. -/
theorem hasDerivWithinAt_reducedCoreLoss_right
    {g : ℝ → ℝ} {point halfDerivative derivative : ℝ}
    (hhalf : HasDerivWithinAt g halfDerivative (Set.Ioi (point / 2)) (point / 2))
    (hfull : HasDerivWithinAt g derivative (Set.Ioi point) point) :
    HasDerivWithinAt (reducedCoreLoss g) (halfDerivative + derivative)
      (Set.Ioi point) point := by
  have hhalfBase : HasDerivWithinAt (fun input : ℝ => input / 2) (1 / 2)
      (Set.Ioi point) point := ((hasDerivAt_id point).div_const 2).hasDerivWithinAt
  have hmaps : Set.MapsTo (fun input : ℝ => input / 2) (Set.Ioi point)
      (Set.Ioi (point / 2)) := by
    intro input hinput
    change point < input at hinput
    change point / 2 < input / 2
    linarith
  have hhalf_composed : HasDerivWithinAt (fun input => g (input / 2))
      (halfDerivative / 2) (Set.Ioi point) point := by
    simpa [Function.comp_def] using hhalf.comp point hhalfBase hmaps
  convert (hhalf_composed.const_mul 2).add hfull using 1
  ring

/-- A negative right derivative yields a strict value decrease at some point to the right. -/
theorem exists_value_lt_of_hasDerivWithinAt_right_neg
    {f : ℝ → ℝ} {point derivative : ℝ}
    (hderiv : HasDerivWithinAt f derivative (Set.Ioi point) point)
    (hderivative_neg : derivative < 0) :
    ∃ rightPoint, point < rightPoint ∧ f rightPoint < f point := by
  have hnegativeSlope : ∀ᶠ rightPoint in 𝓝[>] point,
      slope f point rightPoint < 0 := by
    have htend : Tendsto (slope f point) (𝓝[>] point) (𝓝 derivative) :=
      (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp hderiv
    exact htend.eventually (eventually_lt_nhds hderivative_neg)
  have heventually : ∀ᶠ rightPoint in 𝓝[>] point,
      point < rightPoint ∧ slope f point rightPoint < 0 := by
    filter_upwards [self_mem_nhdsWithin, hnegativeSlope] with rightPoint hright hnegative
    exact ⟨hright, hnegative⟩
  obtain ⟨rightPoint, hpoint_lt_right, hnegativeSlope⟩ := heventually.exists
  refine ⟨rightPoint, hpoint_lt_right, ?_⟩
  exact (slope_neg_iff_of_le hpoint_lt_right.le).mp hnegativeSlope

/--
A positive right derivative of a globally convex real function makes it
strictly increasing from that point onward.  Unlike an ordinary derivative,
this does not claim a strict increase from points on the left of the kink.
-/
theorem strictMonoOn_Ici_of_convex_right_derivative_pos
    {f : ℝ → ℝ} {point derivative : ℝ}
    (hconvex : ConvexOn ℝ Set.univ f)
    (hderiv : HasDerivWithinAt f derivative (Set.Ioi point) point)
    (hderivative_pos : 0 < derivative) :
    StrictMonoOn f (Set.Ici point) := by
  intro left hleft right hright hleft_lt_right
  change point ≤ left at hleft
  change point ≤ right at hright
  rcases hleft.eq_or_lt with rfl | hpoint_lt_left
  · have hslope : derivative ≤ slope f point right :=
      hconvex.le_slope_of_hasDerivWithinAt_Ioi (Set.mem_univ point)
        (Set.mem_univ right) hleft_lt_right hderiv
    have hslope_pos : 0 < slope f point right := lt_of_lt_of_le hderivative_pos hslope
    exact (slope_pos_iff_of_le hleft_lt_right.le).mp hslope_pos
  · have hslope_left : derivative ≤ slope f point left :=
      hconvex.le_slope_of_hasDerivWithinAt_Ioi (Set.mem_univ point)
        (Set.mem_univ left) hpoint_lt_left hderiv
    have hslope_adjacent : slope f point left ≤ slope f left right := by
      simpa only [slope_def_field] using
        hconvex.slope_mono_adjacent (Set.mem_univ point) (Set.mem_univ right)
          hpoint_lt_left hleft_lt_right
    have hslope_pos : 0 < slope f left right :=
      lt_of_lt_of_le hderivative_pos (hslope_left.trans hslope_adjacent)
    exact (slope_pos_iff_of_le hleft_lt_right.le).mp hslope_pos

/--
A strict value decrease somewhere to the right can be moved to begin after a
strictly positive gap, provided the objective is continuous at the base point.
-/
theorem exists_reduced_drop_certificate_of_right_value_drop
    {g : ℝ → ℝ} {w right : ℝ}
    (hcontinuous : Continuous (reducedCoreLoss g))
    (hw_lt_right : w < right)
    (hright_drop : reducedCoreLoss g right < reducedCoreLoss g w) :
    ∃ gap rightStep : ℝ, 0 < gap ∧ 0 < rightStep ∧
      reducedCoreLoss g (w + gap + rightStep) < reducedCoreLoss g (w + gap) := by
  let valueRadius : ℝ := (reducedCoreLoss g w - reducedCoreLoss g right) / 2
  have hvalueRadius_pos : 0 < valueRadius := by
    dsimp [valueRadius]
    linarith
  obtain ⟨radius, hradius_pos, hnearContinuous⟩ :=
    (Metric.continuousAt_iff.mp hcontinuous.continuousAt) valueRadius hvalueRadius_pos
  let gap : ℝ := min (radius / 2) ((right - w) / 2)
  have hgap_pos : 0 < gap := by
    dsimp [gap]
    exact lt_min (half_pos hradius_pos) (half_pos (sub_pos.mpr hw_lt_right))
  let rightStep : ℝ := right - w - gap
  have hrightStep_pos : 0 < rightStep := by
    dsimp [rightStep]
    have hgap_le : gap ≤ (right - w) / 2 := by
      dsimp [gap]
      exact min_le_right _ _
    linarith
  refine ⟨gap, rightStep, hgap_pos, hrightStep_pos, ?_⟩
  have hgap_lt_radius : gap < radius := by
    have hgap_le : gap ≤ radius / 2 := by
      dsimp [gap]
      exact min_le_left _ _
    linarith
  have hnear : dist (w + gap) w < radius := by
    rw [Real.dist_eq]
    have hargument : w + gap - w = gap := by ring
    rw [hargument, abs_of_pos hgap_pos]
    exact hgap_lt_radius
  have hvalue_near := hnearContinuous hnear
  have hright_lt_near : reducedCoreLoss g right < reducedCoreLoss g (w + gap) := by
    rw [Real.dist_eq] at hvalue_near
    rw [abs_lt] at hvalue_near
    dsimp [valueRadius] at hvalue_near
    linarith
  have hendpoint : w + gap + rightStep = right := by
    dsimp [rightStep]
    ring
  rw [hendpoint]
  exact hright_lt_near

/--
The missing four-derivative data in the strictly-convex negative-input branch
of Appendix A.1.  A nearby negative point whose loss is above the initial dip
has a positive left derivative by strict convexity; strict secant inequalities
then give the ordering at its half-scale, while convexity orders the two
right derivatives on the positive side.
-/
theorem exists_four_oneSided_derivative_data_of_strictConvex_negative_dip
    {loss : ℝ → ℝ} {negativeInput : ℝ}
    (hcontinuous : Continuous loss) (hstrict : StrictConvexOn ℝ Set.univ loss)
    (hnegative : negativeInput < 0) (hdip : loss negativeInput < loss 0) :
    ∃ w z1 z2 z3 z4 : ℝ, 0 < w ∧
      HasDerivWithinAt loss z1 (Set.Iio (-w)) (-w) ∧
      HasDerivWithinAt loss z2 (Set.Iio (-(w / 2))) (-(w / 2)) ∧
      HasDerivWithinAt loss z3 (Set.Ioi (w / 2)) (w / 2) ∧
      HasDerivWithinAt loss z4 (Set.Ioi w) w ∧
      0 ≤ z1 ∧ z1 < z2 ∧ z2 ≤ z3 ∧ z3 ≤ z4 := by
  obtain ⟨point, hnegative_lt_point, hpoint_negative, hvalue⟩ :=
    exists_negative_between_with_value_gt_of_continuous_negative_dip
      hcontinuous hnegative hdip
  let hconvex : ConvexOn ℝ Set.univ loss := hstrict.convexOn
  let w : ℝ := -point
  let z1 : ℝ := derivWithin loss (Set.Iio point) point
  let z2 : ℝ := derivWithin loss (Set.Iio (point / 2)) (point / 2)
  let z3 : ℝ := derivWithin loss (Set.Ioi (-point / 2)) (-point / 2)
  let z4 : ℝ := derivWithin loss (Set.Ioi (-point)) (-point)
  have hleftPoint : HasDerivWithinAt loss z1 (Set.Iio point) point := by
    dsimp [z1]
    exact hconvex.hasDerivWithinAt_leftDeriv_of_mem_interior (by simp)
  have hrightPoint : HasDerivWithinAt loss (derivWithin loss (Set.Ioi point) point)
      (Set.Ioi point) point :=
    hconvex.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)
  have hleftHalf : HasDerivWithinAt loss z2 (Set.Iio (point / 2)) (point / 2) := by
    dsimp [z2]
    exact hconvex.hasDerivWithinAt_leftDeriv_of_mem_interior (by simp)
  have hrightHalf : HasDerivWithinAt loss z3 (Set.Ioi (-point / 2)) (-point / 2) := by
    dsimp [z3]
    exact hconvex.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)
  have hrightFull : HasDerivWithinAt loss z4 (Set.Ioi (-point)) (-point) := by
    dsimp [z4]
    exact hconvex.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)
  have hpoint_lt_half : point < point / 2 := by linarith
  have hhalf_lt_negHalf : point / 2 < -point / 2 := by linarith
  have hnegHalf_lt_negPoint : -point / 2 < -point := by linarith
  have hz1_pos : 0 < z1 := by
    have hslope_pos : 0 < slope loss negativeInput point :=
      (slope_pos_iff_of_le hnegative_lt_point.le).mpr hvalue
    exact lt_trans hslope_pos
      (hstrict.slope_lt_of_hasDerivWithinAt_Iio (Set.mem_univ negativeInput)
        (Set.mem_univ point) hnegative_lt_point hleftPoint)
  have hz12 : z1 < z2 := by
    have hleft_le_right : z1 ≤ derivWithin loss (Set.Ioi point) point := by
      dsimp [z1]
      exact hconvex.leftDeriv_le_rightDeriv_of_mem_interior (by simp)
    have hright_lt_slope : derivWithin loss (Set.Ioi point) point < slope loss point (point / 2) :=
      hstrict.lt_slope_of_hasDerivWithinAt_Ioi (Set.mem_univ point)
        (Set.mem_univ (point / 2)) hpoint_lt_half hrightPoint
    have hslope_lt_left : slope loss point (point / 2) < z2 :=
      hstrict.slope_lt_of_hasDerivWithinAt_Iio (Set.mem_univ point)
        (Set.mem_univ (point / 2)) hpoint_lt_half hleftHalf
    exact hleft_le_right.trans_lt (hright_lt_slope.trans hslope_lt_left)
  have hz23 : z2 ≤ z3 := by
    have hleft_le_right : z2 ≤ derivWithin loss (Set.Ioi (point / 2)) (point / 2) := by
      dsimp [z2]
      exact hconvex.leftDeriv_le_rightDeriv_of_mem_interior (by simp)
    have hright_mono : derivWithin loss (Set.Ioi (point / 2)) (point / 2) ≤ z3 := by
      dsimp [z3]
      exact hconvex.monotoneOn_rightDeriv (by simp) (by simp) hhalf_lt_negHalf.le
    exact hleft_le_right.trans hright_mono
  have hz34 : z3 ≤ z4 := by
    dsimp [z3, z4]
    exact hconvex.monotoneOn_rightDeriv (by simp) (by simp) hnegHalf_lt_negPoint.le
  refine ⟨w, z1, z2, z3, z4, neg_pos.mpr hpoint_negative, ?_, ?_, ?_, ?_,
    hz1_pos.le, hz12, hz23, hz34⟩
  · simpa [w] using hleftPoint
  · simpa [w, neg_div] using hleftHalf
  · simpa [w] using hrightHalf
  · simpa [w] using hrightFull

/--
Every continuous nonnegative convex loss with a strict negative-side dip has
a negative point where its left derivative strictly increases under halving.
This replaces the source's case split and supremum construction: if no such
point existed, the positive left derivative forced by a nearby value increase
would persist along all negative dyadic scales, contradicting nonnegativity.
-/
theorem exists_negative_point_leftDeriv_strict_doubling_of_convex_negative_dip
    {loss : ℝ → ℝ} {negativeInput : ℝ}
    (hloss_nonnegative : ∀ input, 0 ≤ loss input)
    (hmonotone : Monotone loss)
    (hcontinuous : Continuous loss) (hconvex : ConvexOn ℝ Set.univ loss)
    (hnegative : negativeInput < 0) (hdip : loss negativeInput < loss 0) :
    ∃ point : ℝ, point < 0 ∧
      0 ≤ derivWithin loss (Set.Iio point) point ∧
        derivWithin loss (Set.Iio point) point <
          derivWithin loss (Set.Iio (point / 2)) (point / 2) := by
  obtain ⟨point, hnegative_lt_point, hpoint_negative, hvalue⟩ :=
    exists_negative_between_with_value_gt_of_continuous_negative_dip
      hcontinuous hnegative hdip
  let leftDeriv : ℝ → ℝ := fun input => derivWithin loss (Set.Iio input) input
  have hleftPoint : HasDerivWithinAt loss (leftDeriv point) (Set.Iio point) point := by
    dsimp [leftDeriv]
    exact hconvex.hasDerivWithinAt_leftDeriv_of_mem_interior (by simp)
  have hleftPoint_pos : 0 < leftDeriv point := by
    have hslope_pos : 0 < slope loss negativeInput point :=
      (slope_pos_iff_of_le hnegative_lt_point.le).mpr hvalue
    exact lt_of_lt_of_le hslope_pos
      (hconvex.slope_le_of_hasDerivWithinAt_Iio (Set.mem_univ negativeInput)
        (Set.mem_univ point) hnegative_lt_point hleftPoint)
  have hleftDeriv_nonnegative : ∀ input : ℝ, 0 ≤ leftDeriv input := by
    intro input
    have hleft : HasDerivWithinAt loss (leftDeriv input) (Set.Iio input) input := by
      dsimp [leftDeriv]
      exact hconvex.hasDerivWithinAt_leftDeriv_of_mem_interior (by simp)
    have hprevious_lt : input - 1 < input := by linarith
    have hslope_nonnegative : 0 ≤ slope loss (input - 1) input :=
      (slope_nonneg_iff_of_le hprevious_lt.le).mpr (hmonotone hprevious_lt.le)
    exact hslope_nonnegative.trans
      (hconvex.slope_le_of_hasDerivWithinAt_Iio (Set.mem_univ (input - 1))
        (Set.mem_univ input) hprevious_lt hleft)
  by_contra hnot
  push Not at hnot
  have hscale_negative : ∀ n : ℕ, (2 : ℝ) ^ n * point < 0 := by
    intro n
    exact mul_neg_of_pos_of_neg (pow_pos (by norm_num) _) hpoint_negative
  have hscale_leftDeriv : ∀ n : ℕ,
      leftDeriv ((2 : ℝ) ^ n * point) = leftDeriv point := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hcurrent_negative : (2 : ℝ) ^ (n + 1) * point < 0 := hscale_negative (n + 1)
      have hcurrent_nonnegative : 0 ≤ leftDeriv ((2 : ℝ) ^ (n + 1) * point) :=
        hleftDeriv_nonnegative _
      have hcurrent_lt_half : (2 : ℝ) ^ (n + 1) * point <
          ((2 : ℝ) ^ (n + 1) * point) / 2 := by
        linarith
      have hmonotone : leftDeriv ((2 : ℝ) ^ (n + 1) * point) ≤
          leftDeriv (((2 : ℝ) ^ (n + 1) * point) / 2) := by
        dsimp [leftDeriv]
        exact hconvex.monotoneOn_leftDeriv (by simp) (by simp) hcurrent_lt_half.le
      have hcurrent_eq : leftDeriv ((2 : ℝ) ^ (n + 1) * point) =
          leftDeriv (((2 : ℝ) ^ (n + 1) * point) / 2) :=
        le_antisymm hmonotone (hnot _ hcurrent_negative hcurrent_nonnegative)
      calc
        leftDeriv ((2 : ℝ) ^ (n + 1) * point) =
            leftDeriv (((2 : ℝ) ^ (n + 1) * point) / 2) :=
              hcurrent_eq
        _ = leftDeriv ((2 : ℝ) ^ n * point) := by
              congr 2
              rw [pow_succ]
              ring
        _ = leftDeriv point := ih
  have hnat_le_pow : ∀ n : ℕ, (n : ℝ) ≤ (2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      have hone_le_pow : 1 ≤ (2 : ℝ) ^ n :=
        one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      calc
        ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
        _ ≤ (2 : ℝ) ^ n + 1 := by linarith
        _ ≤ (2 : ℝ) ^ n * 2 := by nlinarith
        _ = (2 : ℝ) ^ (n + 1) := by rw [pow_succ]
  have hden_pos : 0 < leftDeriv point * (-point) :=
    mul_pos hleftPoint_pos (neg_pos.mpr hpoint_negative)
  obtain ⟨n, hn⟩ := exists_nat_gt (loss 0 / (leftDeriv point * (-point)))
  have hvalue_lt_scale : loss 0 < leftDeriv point * (-point) * (2 : ℝ) ^ n := by
    have hscaled_by_nat : loss 0 < leftDeriv point * (-point) * (n : ℝ) := by
      have hquotient : loss 0 / (leftDeriv point * (-point)) < (n : ℝ) := by
        exact_mod_cast hn
      have := (div_lt_iff₀ hden_pos).mp hquotient
      nlinarith
    have hnat_bound := hnat_le_pow n
    nlinarith
  let scaled : ℝ := (2 : ℝ) ^ n * point
  have hscaled_negative : scaled < 0 := by
    dsimp [scaled]
    exact hscale_negative n
  have hleftScaled : HasDerivWithinAt loss (leftDeriv scaled) (Set.Iio scaled) scaled := by
    dsimp [leftDeriv]
    exact hconvex.hasDerivWithinAt_leftDeriv_of_mem_interior (by simp)
  have hrightScaled : HasDerivWithinAt loss (derivWithin loss (Set.Ioi scaled) scaled)
      (Set.Ioi scaled) scaled :=
    hconvex.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)
  have hleft_le_right : leftDeriv scaled ≤ derivWithin loss (Set.Ioi scaled) scaled := by
    dsimp [leftDeriv]
    exact hconvex.leftDeriv_le_rightDeriv_of_mem_interior (by simp)
  have hright_le_slope : derivWithin loss (Set.Ioi scaled) scaled ≤ slope loss scaled 0 :=
    hconvex.le_slope_of_hasDerivWithinAt_Ioi (Set.mem_univ scaled) (Set.mem_univ 0)
      hscaled_negative hrightScaled
  have hleft_le_slope : leftDeriv point ≤ slope loss scaled 0 := by
    rw [← hscale_leftDeriv n]
    exact hleft_le_right.trans hright_le_slope
  have hden_scaled_pos : 0 < 0 - scaled := sub_pos.mpr hscaled_negative
  have hslope_bound : leftDeriv point * (0 - scaled) ≤ loss 0 - loss scaled := by
    rw [slope_def_field] at hleft_le_slope
    exact (le_div_iff₀ hden_scaled_pos).mp hleft_le_slope
  have hnonnegative_scaled : 0 ≤ loss scaled := hloss_nonnegative scaled
  have hscale_le_value : leftDeriv point * (-point) * (2 : ℝ) ^ n ≤ loss 0 := by
    dsimp [scaled] at hslope_bound
    have hrewrite : 0 - (2 : ℝ) ^ n * point = (-point) * (2 : ℝ) ^ n := by ring
    rw [hrewrite] at hslope_bound
    nlinarith
  exact (not_lt_of_ge hscale_le_value) hvalue_lt_scale

/--
The four source one-sided derivatives in the nondecreasing weakly-convex
alternative of Appendix A.1.  The dyadic strict-increase lemma supplies the
two left derivatives; ordinary convex derivative monotonicity supplies the
two right-derivative inequalities.
-/
theorem exists_four_oneSided_derivative_data_of_monotone_convex_negative_dip
    {loss : ℝ → ℝ} {negativeInput : ℝ}
    (hloss_nonnegative : ∀ input, 0 ≤ loss input) (hmonotone : Monotone loss)
    (hcontinuous : Continuous loss) (hconvex : ConvexOn ℝ Set.univ loss)
    (hnegative : negativeInput < 0) (hdip : loss negativeInput < loss 0) :
    ∃ w z1 z2 z3 z4 : ℝ, 0 < w ∧
      HasDerivWithinAt loss z1 (Set.Iio (-w)) (-w) ∧
      HasDerivWithinAt loss z2 (Set.Iio (-(w / 2))) (-(w / 2)) ∧
      HasDerivWithinAt loss z3 (Set.Ioi (w / 2)) (w / 2) ∧
      HasDerivWithinAt loss z4 (Set.Ioi w) w ∧
      0 ≤ z1 ∧ z1 < z2 ∧ z2 ≤ z3 ∧ z3 ≤ z4 := by
  obtain ⟨point, hpoint_negative, hz1_nonnegative, hz12⟩ :=
    exists_negative_point_leftDeriv_strict_doubling_of_convex_negative_dip
      hloss_nonnegative hmonotone hcontinuous hconvex hnegative hdip
  let w : ℝ := -point
  let z1 : ℝ := derivWithin loss (Set.Iio point) point
  let z2 : ℝ := derivWithin loss (Set.Iio (point / 2)) (point / 2)
  let z3 : ℝ := derivWithin loss (Set.Ioi (-point / 2)) (-point / 2)
  let z4 : ℝ := derivWithin loss (Set.Ioi (-point)) (-point)
  have hleftPoint : HasDerivWithinAt loss z1 (Set.Iio point) point := by
    dsimp [z1]
    exact hconvex.hasDerivWithinAt_leftDeriv_of_mem_interior (by simp)
  have hleftHalf : HasDerivWithinAt loss z2 (Set.Iio (point / 2)) (point / 2) := by
    dsimp [z2]
    exact hconvex.hasDerivWithinAt_leftDeriv_of_mem_interior (by simp)
  have hrightHalf : HasDerivWithinAt loss z3 (Set.Ioi (-point / 2)) (-point / 2) := by
    dsimp [z3]
    exact hconvex.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)
  have hrightFull : HasDerivWithinAt loss z4 (Set.Ioi (-point)) (-point) := by
    dsimp [z4]
    exact hconvex.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)
  have hhalf_lt_negHalf : point / 2 < -point / 2 := by linarith
  have hnegHalf_lt_negPoint : -point / 2 < -point := by linarith
  have hz23 : z2 ≤ z3 := by
    have hleft_le_right : z2 ≤ derivWithin loss (Set.Ioi (point / 2)) (point / 2) := by
      dsimp [z2]
      exact hconvex.leftDeriv_le_rightDeriv_of_mem_interior (by simp)
    have hright_mono : derivWithin loss (Set.Ioi (point / 2)) (point / 2) ≤ z3 := by
      dsimp [z3]
      exact hconvex.monotoneOn_rightDeriv (by simp) (by simp) hhalf_lt_negHalf.le
    exact hleft_le_right.trans hright_mono
  have hz34 : z3 ≤ z4 := by
    dsimp [z3, z4]
    exact hconvex.monotoneOn_rightDeriv (by simp) (by simp) hnegHalf_lt_negPoint.le
  refine ⟨w, z1, z2, z3, z4, neg_pos.mpr hpoint_negative, ?_, ?_, ?_, ?_,
    hz1_nonnegative, hz12, hz23, hz34⟩
  · simpa [w] using hleftPoint
  · simpa [w, neg_div] using hleftHalf
  · simpa [w] using hrightHalf
  · simpa [w] using hrightFull

/--
Two strict derivative signs supply the finite strict-value certificate used by
the non-calculus conclusion of Lemma 3.2.
-/
theorem exists_value_certificate_of_derivative_signs
    {g : ℝ → ℝ} {w gDerivative reducedDerivative : ℝ}
    (hw_pos : 0 < w)
    (hgderiv : HasDerivAt g gDerivative w) (hgderivative_pos : 0 < gDerivative)
    (hreducedDeriv : HasDerivAt (reducedCoreLoss g) reducedDerivative w)
    (hreducedDerivative_neg : reducedDerivative < 0) :
    ∃ lower gap rightStep : ℝ,
      lower < w ∧ 0 < gap ∧ 0 < rightStep ∧
        g lower < g w ∧
          reducedCoreLoss g (w + gap + rightStep) < reducedCoreLoss g (w + gap) := by
  obtain ⟨lower, hlower_lt_w, hgincrease⟩ :=
    exists_value_lt_of_hasDerivAt_pos hgderiv hgderivative_pos
  obtain ⟨right, hw_lt_right, hright_drop⟩ :=
    exists_value_lt_of_hasDerivAt_neg hreducedDeriv hreducedDerivative_neg
  let valueRadius : ℝ := (reducedCoreLoss g w - reducedCoreLoss g right) / 2
  have hvalueRadius_pos : 0 < valueRadius := by
    dsimp [valueRadius]
    linarith
  obtain ⟨radius, hradius_pos, hcontinuous⟩ :=
    (Metric.continuousAt_iff.mp hreducedDeriv.continuousAt) valueRadius hvalueRadius_pos
  let gap : ℝ := min (radius / 2) ((right - w) / 2)
  have hgap_pos : 0 < gap := by
    dsimp [gap]
    exact lt_min (half_pos hradius_pos) (half_pos (sub_pos.mpr hw_lt_right))
  let rightStep : ℝ := right - w - gap
  have hrightStep_pos : 0 < rightStep := by
    dsimp [rightStep]
    have hgap_le : gap ≤ (right - w) / 2 := by
      dsimp [gap]
      exact min_le_right _ _
    linarith
  refine ⟨lower, gap, rightStep, hlower_lt_w, hgap_pos, hrightStep_pos,
    hgincrease, ?_⟩
  have hgap_lt_radius : gap < radius := by
    have hgap_le : gap ≤ radius / 2 := by
      dsimp [gap]
      exact min_le_left _ _
    linarith
  have hnear : dist (w + gap) w < radius := by
    rw [Real.dist_eq]
    have hargument : w + gap - w = gap := by ring
    rw [hargument, abs_of_pos hgap_pos]
    exact hgap_lt_radius
  have hvalue_near := hcontinuous hnear
  have hright_lt_near : reducedCoreLoss g right < reducedCoreLoss g (w + gap) := by
    rw [Real.dist_eq] at hvalue_near
    rw [abs_lt] at hvalue_near
    dsimp [valueRadius] at hvalue_near
    linarith
  have hendpoint : w + gap + rightStep = right := by
    dsimp [rightStep]
    ring
  rw [hendpoint]
  exact hright_lt_near

/-- Convexity of the source's one-variable reduced core loss. -/
theorem reducedCoreLoss_convex
    {g : ℝ → ℝ} (hconvex : ConvexOn ℝ Set.univ g) :
    ConvexOn ℝ Set.univ (reducedCoreLoss g) := by
  have hhalf := (convexOn_mul_comp hconvex (1 / 2)).smul (by norm_num : (0 : ℝ) ≤ 2)
  simpa [reducedCoreLoss, div_eq_mul_inv, smul_eq_mul, mul_comm] using hhalf.add hconvex

/--
A strict finite decrease just to the right of `bound` forces every global
minimizer of a convex function to lie strictly to the right of `bound`.
-/
theorem isGlobalMinimizer_gt_of_convex_drop
    {objective : ℝ → ℝ} {bound rightStep reward : ℝ}
    (hconvex : ConvexOn ℝ Set.univ objective) (hrightStep : 0 < rightStep)
    (hdrop : objective (bound + rightStep) < objective bound)
    (hminimum : IsGlobalMinimizer objective reward) :
    bound < reward := by
  by_contra hnot
  have hrewards_le : reward ≤ bound := le_of_not_gt hnot
  rcases lt_or_eq_of_le hrewards_le with hless | hequal
  · have hanti : StrictAntiOn objective (Set.Iic bound) := by
      simpa using hconvex.strictAntiOn (Set.mem_univ (bound + rightStep))
        (lt_add_of_pos_right bound hrightStep) hdrop
    have hstrict : objective bound < objective reward :=
      hanti (Set.mem_Iic.mpr hless.le) (Set.mem_Iic.mpr le_rfl) hless
    exact (not_lt_of_ge (hminimum bound)) hstrict
  · subst reward
    exact (not_lt_of_ge (hminimum (bound + rightStep))) hdrop

/-- A strict convex-function increase provides strict monotonicity thereafter. -/
theorem strictMonoOn_Ici_of_convex_increase
    {g : ℝ → ℝ} {lower bound : ℝ} (hconvex : ConvexOn ℝ Set.univ g)
    (hlower : lower < bound) (hincrease : g lower < g bound) :
    StrictMonoOn g (Set.Ici bound) := by
  simpa using hconvex.strictMonoOn (Set.mem_univ lower) hlower hincrease

/-- Evaluating the two-reward core objective at its symmetrized point. -/
theorem unconstrainedCoreLoss_symmetrized_eq_reduced
    (g : ℝ → ℝ) (rewards : ℝ × ℝ) :
    unconstrainedCoreLoss g (symmetrizedRewards rewards) =
      reducedCoreLoss g rewards.1 := by
  dsimp [unconstrainedCoreLoss, symmetrizedRewards, reducedCoreLoss]
  have hhalf : rewards.1 - rewards.1 / 2 = rewards.1 / 2 := by ring
  rw [hhalf]
  ring

/--
Appendix A.1's optimizer symmetrization: every global minimizer yields the
symmetrized global minimizer used to reduce the source proof to one variable.
-/
theorem isGlobalMinimizer_symmetrizedRewards
    {g : ℝ → ℝ} (hconvex : ConvexOn ℝ Set.univ g) (rewards : ℝ × ℝ)
    (hminimizes : IsGlobalMinimizer (unconstrainedCoreLoss g) rewards) :
    IsGlobalMinimizer (unconstrainedCoreLoss g) (symmetrizedRewards rewards) := by
  intro contender
  exact le_trans (unconstrainedCoreLoss_symmetrized_le hconvex rewards)
    (hminimizes contender)

/--
The first coordinate of any global two-reward minimizer minimizes the reduced
one-variable loss.  This is the reduction to `h` in Appendix A.1.
-/
theorem isGlobalMinimizer_reducedCoreLoss_of_unconstrained
    {g : ℝ → ℝ} (hconvex : ConvexOn ℝ Set.univ g) (rewards : ℝ × ℝ)
    (hminimizes : IsGlobalMinimizer (unconstrainedCoreLoss g) rewards) :
    IsGlobalMinimizer (reducedCoreLoss g) rewards.1 := by
  intro contender
  have hsymmetrized :=
    isGlobalMinimizer_symmetrizedRewards hconvex rewards hminimizes
  have hcomparison := hsymmetrized (contender, contender / 2)
  calc
    reducedCoreLoss g rewards.1 =
        unconstrainedCoreLoss g (symmetrizedRewards rewards) :=
      (unconstrainedCoreLoss_symmetrized_eq_reduced g rewards).symm
    _ ≤ unconstrainedCoreLoss g (contender, contender / 2) := hcomparison
    _ = unconstrainedCoreLoss g (symmetrizedRewards (contender, 0)) := rfl
    _ = reducedCoreLoss g contender :=
      unconstrainedCoreLoss_symmetrized_eq_reduced g (contender, 0)

/--
Rewards of the three source core candidates `(2, 1)`, `(1, 1)`, and `(0, 0)`
under a two-coordinate parameter, retaining the two nonconstant rewards.
-/
def coreFeatureRewards (parameter : ℝ × ℝ) : ℝ × ℝ :=
  (2 * parameter.1 + parameter.2, parameter.1 + parameter.2)

/-- The inverse parameter map for the source's two-by-two core feature matrix. -/
def coreParameterForRewards (rewards : ℝ × ℝ) : ℝ × ℝ :=
  (rewards.1 - rewards.2, 2 * rewards.2 - rewards.1)

/-- The source core feature map has the displayed inverse on reward pairs. -/
theorem coreFeatureRewards_parameterForRewards (rewards : ℝ × ℝ) :
    coreFeatureRewards (coreParameterForRewards rewards) = rewards := by
  ext <;> simp [coreFeatureRewards, coreParameterForRewards] <;> ring

/-- The inverse map recovers every two-coordinate core parameter. -/
theorem coreParameterForRewards_featureRewards (parameter : ℝ × ℝ) :
    coreParameterForRewards (coreFeatureRewards parameter) = parameter := by
  ext <;> simp [coreFeatureRewards, coreParameterForRewards] <;> ring

/-- The exact three-candidate core objective after substituting source features. -/
def coreLoss (g : ℝ → ℝ) (parameter : ℝ × ℝ) : ℝ :=
  unconstrainedCoreLoss g (coreFeatureRewards parameter)

/-- Transport global minimizers across the invertible source core feature map. -/
theorem isGlobalMinimizer_coreLoss_iff
    {g : ℝ → ℝ} (parameter : ℝ × ℝ) :
    IsGlobalMinimizer (coreLoss g) parameter ↔
      IsGlobalMinimizer (unconstrainedCoreLoss g) (coreFeatureRewards parameter) := by
  constructor
  · intro h contender
    calc
      unconstrainedCoreLoss g (coreFeatureRewards parameter) = coreLoss g parameter := rfl
      _ ≤ coreLoss g (coreParameterForRewards contender) :=
        h (coreParameterForRewards contender)
      _ = unconstrainedCoreLoss g contender := by
        rw [coreLoss, coreFeatureRewards_parameterForRewards]
  · intro h contender
    exact h (coreFeatureRewards contender)

/--
Source Lemma 3.3.  Once Lemma 3.2 supplies separating bounds for all global
minimizers of the unconstrained core objective, the explicit core feature
matrix transfers both minimizer existence and the stated parameter bounds.
-/
theorem lemma3_3_core_minimizers
    {g : ℝ → ℝ} {A1 A2 : ℝ} (hA : A1 < A2)
    (hminimizer : ∃ rewards, IsGlobalMinimizer (unconstrainedCoreLoss g) rewards)
    (hseparation : ∀ rewards, IsGlobalMinimizer (unconstrainedCoreLoss g) rewards →
      rewards.1 > A2 ∧ rewards.2 ≤ A1) :
    ∃ A3 A4, 0 < A3 ∧ ∃ parameter, IsGlobalMinimizer (coreLoss g) parameter ∧
      ∀ parameter, IsGlobalMinimizer (coreLoss g) parameter →
        parameter.1 > A3 ∧ parameter.2 < A4 := by
  refine ⟨A2 - A1, 2 * A1 - A2, sub_pos.mpr hA, ?_⟩
  obtain ⟨rewards, hminimum⟩ := hminimizer
  refine ⟨coreParameterForRewards rewards,
    (isGlobalMinimizer_coreLoss_iff (coreParameterForRewards rewards)).mpr ?_, ?_⟩
  · simpa only [coreFeatureRewards_parameterForRewards] using hminimum
  · intro parameter hparameter
    have hrewardMinimum :
        IsGlobalMinimizer (unconstrainedCoreLoss g) (coreFeatureRewards parameter) :=
      (isGlobalMinimizer_coreLoss_iff parameter).mp hparameter
    obtain ⟨hfirst, hsecond⟩ := hseparation _ hrewardMinimum
    change 2 * parameter.1 + parameter.2 > A2 at hfirst
    change parameter.1 + parameter.2 ≤ A1 at hsecond
    constructor <;> linarith

/--
The ε-independent open parameter cone that separates the source copy `c′`
from `c` in the intended direction.  At positive ε, membership says that the
copy has strictly *lower* reward than its original.
-/
def copyBelowOriginalCone (δ : ℝ) (parameter : ℝ × ℝ) : Prop :=
  -parameter.1 + δ * parameter.2 < 0

/--
The strict cone that ranks all three original candidates above their copied
counterparts at every positive perturbation.  The `a/a′` and `b/b′` gaps are
both `ε * parameter.1`; the `c/c′` gap is governed by
`-θ1 + δ * θ2 < 0`.
-/
def allCopiesBelowOriginalCone (δ : ℝ) (parameter : ℝ × ℝ) : Prop :=
  0 < parameter.1 ∧ copyBelowOriginalCone δ parameter

/--
The closed weak half-space corresponding to the source's bad region
`R_{c′ ≻ c}` at positive ε.  It is deliberately distinguished from the open
strict cone: Appendix A.4 incorrectly calls this weak region open.
-/
def copyAboveOrTiedCone (δ : ℝ) (parameter : ℝ × ℝ) : Prop :=
  0 ≤ -parameter.1 + δ * parameter.2

/-- The compact bad set used by the corrected bounded perturbation argument. -/
def copyBadRegion (bound δ : ℝ) : Set (ℝ × ℝ) :=
  coreRewardSquare bound ∩ { parameter | copyAboveOrTiedCone δ parameter }

/-- The bounded weak bad region is compact. -/
theorem isCompact_copyBadRegion (bound δ : ℝ) :
    IsCompact (copyBadRegion bound δ) := by
  unfold copyBadRegion copyAboveOrTiedCone
  apply (isCompact_coreRewardSquare bound).inter_right
  exact isClosed_le continuous_const
    (continuous_fst.neg.add (continuous_const.mul continuous_snd))

/-- The bounded weak bad region is nonempty whenever the parameter square contains zero. -/
theorem zero_mem_copyBadRegion {bound δ : ℝ} (hbound : 0 ≤ bound) :
    (0, 0) ∈ copyBadRegion bound δ := by
  unfold copyBadRegion copyAboveOrTiedCone
  constructor
  · exact zero_mem_coreRewardSquare hbound
  · norm_num

/-- The literal six-candidate feature family from source §3.1. -/
noncomputable def sixCandidateCopyFeatures (ε δ : ℝ) : Candidate 4 → FeatureVector 2 :=
  fun candidate coordinate =>
    if candidate = 0 then
      if coordinate = 0 then 2 else 1
    else if candidate = 1 then
      if coordinate = 0 then 2 - ε else 1
    else if candidate = 2 then
      if coordinate = 0 then 1 else 1
    else if candidate = 3 then
      if coordinate = 0 then 1 - ε else 1
    else if candidate = 4 then
      if coordinate = 0 then -ε else δ * ε
    else
      0

/-- The first six-candidate ranking in source §3.1: `a ≻ a′ ≻ b ≻ b′ ≻ c′ ≻ c`. -/
noncomputable def sixCandidateForwardRanking : Ranking 4 := Equiv.refl _

/-- The second six-candidate ranking in source §3.1: `c′ ≻ c ≻ b′ ≻ b ≻ a′ ≻ a`. -/
noncomputable def sixCandidateReverseRanking : Ranking 4 :=
  (Equiv.swap (0 : Candidate 4) 1).trans Fin.revPerm

/--
The corrected feasible witness for the source's first six-candidate ranking.
The printed witness `(1, 1)` has the copied pair in the wrong order under the
printed feature coordinates; `(δ, 2)` gives the stated ranking for
`0 < δ` and `0 < ε < 1`.
-/
noncomputable def sixCandidateForwardParameter (δ : ℝ) : LinearRewardParameter 2 :=
  fun coordinate => if coordinate = 0 then δ else 2

/-- The source's printed feasible witness for the reverse six-candidate ranking. -/
noncomputable def sixCandidateReverseParameter : LinearRewardParameter 2 :=
  fun coordinate => if coordinate = 0 then -1 else 0

/--
The first source ranking is feasible under the printed feature coordinates,
using the corrected witness `(δ, 2)` rather than the erroneous `(1, 1)`
footnote witness.
-/
theorem linearFeasibleRanking_sixCandidateForward
    {ε δ : ℝ} (hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) :
    LinearFeasibleRanking (sixCandidateCopyFeatures ε δ) sixCandidateForwardRanking := by
  have hstrict : ∀ first second : Candidate 4, first < second →
      linearReward (sixCandidateForwardParameter δ) (sixCandidateCopyFeatures ε δ) second <
        linearReward (sixCandidateForwardParameter δ) (sixCandidateCopyFeatures ε δ) first := by
    intro first second horder
    fin_cases first <;> fin_cases second
    all_goals simp_all [sixCandidateForwardParameter, sixCandidateCopyFeatures, linearReward]
    all_goals nlinarith [mul_pos hδ_pos hε_pos,
      mul_lt_mul_of_pos_left hε_lt_one hδ_pos]
  refine ⟨sixCandidateForwardParameter δ, ?_, ?_⟩
  · intro first second hdistinct
    rcases lt_or_gt_of_ne hdistinct with hforward | hreverse
    · exact ne_of_gt (hstrict first second hforward)
    · exact ne_of_lt (hstrict second first hreverse)
  · intro first second hpreference
    have horder : first < second := by
      simpa [StrictlyPrefers, sixCandidateForwardRanking, rankOf] using hpreference
    exact (hstrict first second horder).le

/-- The reverse source ranking is feasible with its printed witness `(-1, 0)`. -/
theorem linearFeasibleRanking_sixCandidateReverse
    {ε δ : ℝ} (hε_pos : 0 < ε) (hε_lt_one : ε < 1) :
    LinearFeasibleRanking (sixCandidateCopyFeatures ε δ) sixCandidateReverseRanking := by
  refine ⟨sixCandidateReverseParameter, ?_, ?_⟩
  · intro first second hdistinct
    fin_cases first <;> fin_cases second
    all_goals simp_all [sixCandidateReverseParameter, sixCandidateCopyFeatures, linearReward]
    all_goals nlinarith
  · intro first second hpreference
    fin_cases first <;> fin_cases second
    all_goals simp_all [StrictlyPrefers, sixCandidateReverseRanking, rankOf,
      sixCandidateReverseParameter, sixCandidateCopyFeatures, linearReward,
      Equiv.swap_apply_def]
    all_goals nlinarith

/-- The finite realization of the source's `p` versus `1-p` six-candidate profile. -/
noncomputable def sixCandidateProfile (majorityCount minorityCount : ℕ) :
    RankingProfile (Fin (majorityCount + minorityCount)) 4 :=
  fun voter =>
    if voter.1 < majorityCount then sixCandidateForwardRanking else sixCandidateReverseRanking

/-- The first source ranking places the copied candidate `c′` above `c`. -/
theorem strictlyPrefers_sixCandidateForward_copy_pair :
    StrictlyPrefers sixCandidateForwardRanking (4 : Candidate 4) 5 := by
  norm_num [StrictlyPrefers, sixCandidateForwardRanking, rankOf]
  decide

/-- The second source ranking likewise places the copied candidate `c′` above `c`. -/
theorem strictlyPrefers_sixCandidateReverse_copy_pair :
    StrictlyPrefers sixCandidateReverseRanking (4 : Candidate 4) 5 := by
  norm_num [StrictlyPrefers, sixCandidateReverseRanking, rankOf, Equiv.swap_apply_def]
  decide

/-- Every input ranking in the finite source profile is linearly feasible. -/
theorem feasibleProfile_sixCandidateProfile
    {ε δ : ℝ} (hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (majorityCount minorityCount : ℕ) :
    FeasibleProfile (LinearFeasibleRanking (sixCandidateCopyFeatures ε δ))
      (sixCandidateProfile majorityCount minorityCount) := by
  intro voter
  unfold sixCandidateProfile
  split
  · exact linearFeasibleRanking_sixCandidateForward hε_pos hε_lt_one hδ_pos hδ_lt_one
  · exact linearFeasibleRanking_sixCandidateReverse hε_pos hε_lt_one

/-- The six-candidate profile unanimously ranks `c′` above `c`, as used for PO. -/
theorem universallyPreferred_sixCandidateProfile_copy_pair
    (majorityCount minorityCount : ℕ) :
    UniversallyPreferred (sixCandidateProfile majorityCount minorityCount) (4 : Candidate 4) 5 := by
  intro voter
  unfold sixCandidateProfile
  split
  · exact strictlyPrefers_sixCandidateForward_copy_pair
  · exact strictlyPrefers_sixCandidateReverse_copy_pair

/-- The first block of the finite source profile contains exactly `majorityCount` voters. -/
theorem card_sixCandidateProfile_earlyVoters (majorityCount minorityCount : ℕ) :
    (Finset.univ.filter fun voter : Fin (majorityCount + minorityCount) =>
      voter.1 < majorityCount).card = majorityCount := by
  rw [Fin.card_filter_val_lt]
  omega

/-- The remaining block of the finite source profile contains exactly `minorityCount` voters. -/
theorem card_sixCandidateProfile_lateVoters (majorityCount minorityCount : ℕ) :
    (Finset.univ.filter fun voter : Fin (majorityCount + minorityCount) =>
      ¬ voter.1 < majorityCount).card = minorityCount := by
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (majorityCount + minorityCount))))
    (fun voter => voter.1 < majorityCount)
  rw [card_sixCandidateProfile_earlyVoters] at hpartition
  simpa using hpartition

/-- Every comparison in the first source ranking has a strict voter majority. -/
theorem strictMajorityPrefers_sixCandidateProfile_of_forward
    {majorityCount minorityCount : ℕ} (hmajority : minorityCount < majorityCount)
    {first second : Candidate 4}
    (hforward : StrictlyPrefers sixCandidateForwardRanking first second) :
    StrictMajorityPrefers (sixCandidateProfile majorityCount minorityCount) first second := by
  classical
  unfold StrictMajorityPrefers StrictMajority votersSatisfying
  simp only [Fintype.card_fin]
  have hsubset :
      (Finset.univ.filter fun voter : Fin (majorityCount + minorityCount) =>
        voter.1 < majorityCount) ⊆
        (Finset.univ.filter fun voter : Fin (majorityCount + minorityCount) =>
          StrictlyPrefers (sixCandidateProfile majorityCount minorityCount voter) first second) := by
    intro voter hvoter
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hvoter ⊢
    unfold sixCandidateProfile
    rw [if_pos hvoter]
    exact hforward
  have hsupport : majorityCount ≤
      (Finset.univ.filter fun voter : Fin (majorityCount + minorityCount) =>
        StrictlyPrefers (sixCandidateProfile majorityCount minorityCount voter) first second).card := by
    calc
      majorityCount =
          (Finset.univ.filter fun voter : Fin (majorityCount + minorityCount) =>
            voter.1 < majorityCount).card :=
        (card_sixCandidateProfile_earlyVoters majorityCount minorityCount).symm
      _ ≤ (Finset.univ.filter fun voter : Fin (majorityCount + minorityCount) =>
            StrictlyPrefers (sixCandidateProfile majorityCount minorityCount voter) first second).card :=
        Finset.card_le_card hsubset
  omega

/-- A pair not ordered by the first source ranking cannot have a strict majority. -/
theorem not_strictMajorityPrefers_sixCandidateProfile_of_not_forward
    {majorityCount minorityCount : ℕ} (hmajority : minorityCount < majorityCount)
    {first second : Candidate 4}
    (hnot_forward : ¬ StrictlyPrefers sixCandidateForwardRanking first second) :
    ¬ StrictMajorityPrefers (sixCandidateProfile majorityCount minorityCount) first second := by
  classical
  intro hmajority_preference
  unfold StrictMajorityPrefers StrictMajority votersSatisfying at hmajority_preference
  simp only [Fintype.card_fin] at hmajority_preference
  have hsubset :
      (Finset.univ.filter fun voter : Fin (majorityCount + minorityCount) =>
        StrictlyPrefers (sixCandidateProfile majorityCount minorityCount voter) first second) ⊆
        (Finset.univ.filter fun voter : Fin (majorityCount + minorityCount) =>
          ¬ voter.1 < majorityCount) := by
    intro voter hvoter
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hvoter ⊢
    by_contra hearly
    unfold sixCandidateProfile at hvoter
    rw [if_pos hearly] at hvoter
    exact hnot_forward hvoter
  have hsupport :
      (Finset.univ.filter fun voter : Fin (majorityCount + minorityCount) =>
        StrictlyPrefers (sixCandidateProfile majorityCount minorityCount voter) first second).card
          ≤ minorityCount := by
    calc
      (Finset.univ.filter fun voter : Fin (majorityCount + minorityCount) =>
        StrictlyPrefers (sixCandidateProfile majorityCount minorityCount voter) first second).card
          ≤ (Finset.univ.filter fun voter : Fin (majorityCount + minorityCount) =>
            ¬ voter.1 < majorityCount).card := Finset.card_le_card hsubset
      _ = minorityCount := card_sixCandidateProfile_lateVoters majorityCount minorityCount
  omega

/-- With more first than second-block voters, the first ranking is the PMC ranking. -/
theorem isPairwiseMajorityRanking_sixCandidateProfile
    {majorityCount minorityCount : ℕ} (hmajority : minorityCount < majorityCount) :
    IsPairwiseMajorityRanking (sixCandidateProfile majorityCount minorityCount)
      sixCandidateForwardRanking := by
  intro first second
  constructor
  · exact strictMajorityPrefers_sixCandidateProfile_of_forward hmajority
  · intro hmajority_preference
    by_contra hnot_forward
    exact (not_strictMajorityPrefers_sixCandidateProfile_of_not_forward
      hmajority hnot_forward) hmajority_preference

/-- Averaging a finite `m` versus `n` voter block gives its stated two weights. -/
theorem sum_sixCandidateProfile_blocks
    (majorityCount minorityCount : ℕ) (forwardValue reverseValue : ℝ) :
    (∑ voter : Fin (majorityCount + minorityCount),
      if voter.1 < majorityCount then forwardValue else reverseValue) =
        majorityCount * forwardValue + minorityCount * reverseValue := by
  change (∑ voter : Fin (majorityCount + minorityCount),
    (fun index : ℕ => if index < majorityCount then forwardValue else reverseValue) voter.1) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun index : ℕ => if index < majorityCount then forwardValue else reverseValue)
    (majorityCount + minorityCount)]
  rw [Finset.sum_range_add]
  have hfirst :
      (∑ index ∈ Finset.range majorityCount,
        if index < majorityCount then forwardValue else reverseValue) =
          majorityCount * forwardValue := by
    calc
      (∑ index ∈ Finset.range majorityCount,
          if index < majorityCount then forwardValue else reverseValue) =
          ∑ _index ∈ Finset.range majorityCount, forwardValue := by
        apply Finset.sum_congr rfl
        intro index hindex
        rw [if_pos (Finset.mem_range.mp hindex)]
      _ = majorityCount * forwardValue := by simp
  have hsecond :
      (∑ index ∈ Finset.range minorityCount,
        if majorityCount + index < majorityCount then forwardValue else reverseValue) =
          minorityCount * reverseValue := by
    calc
      (∑ index ∈ Finset.range minorityCount,
          if majorityCount + index < majorityCount then forwardValue else reverseValue) =
          ∑ _index ∈ Finset.range minorityCount, reverseValue := by
        apply Finset.sum_congr rfl
        intro index _hindex
        rw [if_neg (Nat.not_lt_of_ge (Nat.le_add_right _ _))]
      _ = minorityCount * reverseValue := by simp
  rw [hfirst, hsecond]

/-- The finite source profile realizes the corresponding integer-weighted loss. -/
theorem standardLoss_sixCandidateProfile_blocks
    {dimension : ℕ} (features : Candidate 4 → FeatureVector dimension)
    (majorityCount minorityCount : ℕ) (loss : ℝ → ℝ)
    (parameter : LinearRewardParameter dimension) :
    standardLoss features (sixCandidateProfile majorityCount minorityCount) loss parameter =
      majorityCount * rankingPairLoss features sixCandidateForwardRanking loss parameter +
        minorityCount * rankingPairLoss features sixCandidateReverseRanking loss parameter := by
  rw [standardLoss_eq_sum_rankingPairLoss]
  calc
    (∑ voter : Fin (majorityCount + minorityCount),
      rankingPairLoss features (sixCandidateProfile majorityCount minorityCount voter) loss parameter) =
        ∑ voter : Fin (majorityCount + minorityCount),
          if voter.1 < majorityCount then
            rankingPairLoss features sixCandidateForwardRanking loss parameter
          else rankingPairLoss features sixCandidateReverseRanking loss parameter := by
      apply Finset.sum_congr rfl
      intro voter _hvoter
      unfold sixCandidateProfile
      split <;> rfl
    _ = majorityCount * rankingPairLoss features sixCandidateForwardRanking loss parameter +
        minorityCount * rankingPairLoss features sixCandidateReverseRanking loss parameter :=
      sum_sixCandidateProfile_blocks majorityCount minorityCount
        (rankingPairLoss features sixCandidateForwardRanking loss parameter)
        (rankingPairLoss features sixCandidateReverseRanking loss parameter)

/-- The weighted objective written in source §3.1 for its two ranking types. -/
noncomputable def sixCandidateWeightedLoss
    {dimension : ℕ} (features : Candidate 4 → FeatureVector dimension)
    (weight : ℝ) (loss : ℝ → ℝ)
    (parameter : LinearRewardParameter dimension) : ℝ :=
  weight * rankingPairLoss features sixCandidateForwardRanking loss parameter +
    (1 - weight) * rankingPairLoss features sixCandidateReverseRanking loss parameter

/-- The two-coordinate linear parameter corresponding to a real reward pair. -/
noncomputable def twoCoordinateParameter (parameter : ℝ × ℝ) : LinearRewardParameter 2 :=
  fun coordinate => if coordinate = 0 then parameter.1 else parameter.2

/-- The source's literal six-candidate weighted objective. -/
noncomputable def sixCandidateSourceObjective
    (ε δ weight : ℝ) (loss : ℝ → ℝ) (parameter : ℝ × ℝ) : ℝ :=
  sixCandidateWeightedLoss (sixCandidateCopyFeatures ε δ) weight loss
    (twoCoordinateParameter parameter)

/-- At ε = 0 the literal six-candidate objective is four core copies plus three ties. -/
theorem sixCandidateSourceObjective_zero
    (δ weight : ℝ) (loss : ℝ → ℝ) (parameter : ℝ × ℝ) :
    sixCandidateSourceObjective 0 δ weight loss parameter =
      4 * coreLoss (weightedLoss weight loss) parameter + 3 * loss 0 := by
  classical
  unfold sixCandidateSourceObjective sixCandidateWeightedLoss rankingPairLoss
    twoCoordinateParameter coreLoss unconstrainedCoreLoss coreFeatureRewards weightedLoss
    linearReward
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  repeat' rw [Fin.sum_univ_six]
  simp [sixCandidateCopyFeatures, sixCandidateForwardRanking,
    sixCandidateReverseRanking, StrictlyPrefers, rankOf, Equiv.swap_apply_def,
    Fin.rev]
  ring_nf

/-- The zero parameter has the same finite loss for every perturbation ε. -/
theorem sixCandidateSourceObjective_at_zeroParameter
    (ε δ weight : ℝ) (loss : ℝ → ℝ) :
    sixCandidateSourceObjective ε δ weight loss (0, 0) = 15 * loss 0 := by
  classical
  unfold sixCandidateSourceObjective sixCandidateWeightedLoss rankingPairLoss
    twoCoordinateParameter linearReward
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  repeat' rw [Fin.sum_univ_six]
  simp [sixCandidateCopyFeatures, sixCandidateForwardRanking,
    sixCandidateReverseRanking, StrictlyPrefers, rankOf, Equiv.swap_apply_def,
    Fin.rev]
  ring_nf

/-- The literal source objective is jointly continuous in ε and the two parameters. -/
theorem continuous_sixCandidateSourceObjective
    (δ weight : ℝ) {loss : ℝ → ℝ} (hcontinuous : Continuous loss) :
    Continuous (fun input : ℝ × (ℝ × ℝ) =>
      sixCandidateSourceObjective input.1 δ weight loss input.2) := by
  classical
  have hparameter (coordinate : Fin 2) :
      Continuous (fun input : ℝ × (ℝ × ℝ) => twoCoordinateParameter input.2 coordinate) := by
    unfold twoCoordinateParameter
    split_ifs <;> fun_prop
  have hfeature (candidate : Candidate 4) (coordinate : Fin 2) :
      Continuous (fun input : ℝ × (ℝ × ℝ) =>
        sixCandidateCopyFeatures input.1 δ candidate coordinate) := by
    unfold sixCandidateCopyFeatures
    split_ifs <;> fun_prop
  have hreward (candidate : Candidate 4) :
      Continuous (fun input : ℝ × (ℝ × ℝ) =>
        linearReward (twoCoordinateParameter input.2)
          (sixCandidateCopyFeatures input.1 δ) candidate) := by
    unfold linearReward
    apply continuous_finset_sum
    intro coordinate _hcoordinate
    exact (hparameter coordinate).mul (hfeature candidate coordinate)
  have hranking (ranking : Ranking 4) :
      Continuous (fun input : ℝ × (ℝ × ℝ) =>
        rankingPairLoss (sixCandidateCopyFeatures input.1 δ) ranking loss
          (twoCoordinateParameter input.2)) := by
    unfold rankingPairLoss
    apply continuous_finset_sum
    intro pair _hpair
    by_cases hprefers : StrictlyPrefers ranking pair.1 pair.2
    · simpa only [if_pos hprefers] using
        hcontinuous.comp ((hreward pair.2).sub (hreward pair.1))
    · simpa only [if_neg hprefers] using (continuous_const :
        Continuous (fun _ : ℝ × (ℝ × ℝ) => (0 : ℝ)))
  unfold sixCandidateSourceObjective sixCandidateWeightedLoss
  exact (continuous_const.mul (hranking sixCandidateForwardRanking)).add
    (continuous_const.mul (hranking sixCandidateReverseRanking))

/--
Two oppositely submitted core comparisons already lower-bound the literal
six-candidate source objective by its two weighted core gaps.  This is the
coercivity calculation in Appendix A.4, expressed without omitting the other
nonnegative submitted comparisons.
-/
theorem two_weightedLoss_le_sixCandidateSourceObjective
    {ε δ weight : ℝ} {loss : ℝ → ℝ} (parameter : ℝ × ℝ)
    (hweight_nonnegative : 0 ≤ weight) (hweight_le_one : weight ≤ 1)
    (hloss_nonnegative : ∀ input, 0 ≤ loss input) :
    weightedLoss weight loss parameter.1 +
      weightedLoss weight loss (parameter.1 + parameter.2) ≤
        sixCandidateSourceObjective ε δ weight loss parameter := by
  have hforward := two_terms_le_rankingPairLoss
    (features := sixCandidateCopyFeatures ε δ)
    (ranking := sixCandidateForwardRanking) (loss := loss)
    (parameter := twoCoordinateParameter parameter) hloss_nonnegative
    (first₁ := (0 : Candidate 4)) (second₁ := 2)
    (first₂ := (2 : Candidate 4)) (second₂ := 5)
    (by
      norm_num [StrictlyPrefers, sixCandidateForwardRanking, rankOf]
      decide)
    (by
      norm_num [StrictlyPrefers, sixCandidateForwardRanking, rankOf]
      decide)
    (by
      norm_num
      decide)
  have hreverse := two_terms_le_rankingPairLoss
    (features := sixCandidateCopyFeatures ε δ)
    (ranking := sixCandidateReverseRanking) (loss := loss)
    (parameter := twoCoordinateParameter parameter) hloss_nonnegative
    (first₁ := (2 : Candidate 4)) (second₁ := 0)
    (first₂ := (5 : Candidate 4)) (second₂ := 2)
    (by
      norm_num [StrictlyPrefers, sixCandidateReverseRanking, rankOf, Equiv.swap_apply_def]
      decide)
    (by
      norm_num [StrictlyPrefers, sixCandidateReverseRanking, rankOf, Equiv.swap_apply_def]
      decide)
    (by
      norm_num
      decide)
  have hforward' :
      loss (-parameter.1) + loss (-(parameter.1 + parameter.2)) ≤
        rankingPairLoss (sixCandidateCopyFeatures ε δ) sixCandidateForwardRanking loss
          (twoCoordinateParameter parameter) := by
    convert hforward using 1
    all_goals
      simp [sixCandidateCopyFeatures, twoCoordinateParameter, linearReward]
      ring_nf
  have hreverse' :
      loss parameter.1 + loss (parameter.1 + parameter.2) ≤
        rankingPairLoss (sixCandidateCopyFeatures ε δ) sixCandidateReverseRanking loss
          (twoCoordinateParameter parameter) := by
    convert hreverse using 1
    all_goals
      simp [sixCandidateCopyFeatures, twoCoordinateParameter, linearReward]
      ring_nf
  have hforward_scaled := mul_le_mul_of_nonneg_left hforward' hweight_nonnegative
  have hreverse_scaled := mul_le_mul_of_nonneg_left hreverse'
    (sub_nonneg.mpr hweight_le_one)
  unfold sixCandidateSourceObjective sixCandidateWeightedLoss weightedLoss
  linarith

/--
The literal source objective controls the two absolute core reward gaps.  A
parameter leaving the source square must therefore have loss above its fixed
zero-parameter value once either gap passes the loss tail threshold.
-/
theorem abs_weightedLoss_lower_bound_sixCandidateSourceObjective
    {ε δ weight : ℝ} {loss : ℝ → ℝ} (parameter : ℝ × ℝ)
    (hweight_half : 1 / 2 ≤ weight) (hweight_le_one : weight ≤ 1)
    (hloss_nonnegative : ∀ input, 0 ≤ loss input) (hmonotone : Monotone loss) :
    (1 - weight) * loss |parameter.1| +
      (1 - weight) * loss |parameter.1 + parameter.2| ≤
        sixCandidateSourceObjective ε δ weight loss parameter := by
  have hfirst := weightedLoss_abs_lower_bound hweight_half hweight_le_one
    hloss_nonnegative hmonotone parameter.1
  have hsecond := weightedLoss_abs_lower_bound hweight_half hweight_le_one
    hloss_nonnegative hmonotone (parameter.1 + parameter.2)
  exact (add_le_add hfirst hsecond).trans
    (two_weightedLoss_le_sixCandidateSourceObjective parameter
      (by linarith) hweight_le_one hloss_nonnegative)

/--
The literal six-candidate source objective is uniformly stable in ε on each
fixed reward square.  This instantiates the compact continuity bridge used by
the corrected perturbation argument.
-/
theorem uniformPerturbation_sixCandidateSourceObjective_on_coreRewardSquare
    (bound δ weight : ℝ) {loss : ℝ → ℝ} (hcontinuous : Continuous loss) :
    ∀ tolerance : ℝ, 0 < tolerance → ∃ radius : ℝ, 0 < radius ∧
      ∀ ε, |ε| < radius → ∀ parameter, parameter ∈ coreRewardSquare bound →
        |sixCandidateSourceObjective ε δ weight loss parameter -
          sixCandidateSourceObjective 0 δ weight loss parameter| < tolerance := by
  exact continuous_uniformPerturbation_on_compact
    (sixCandidateSourceObjective · δ weight loss)
    (coreRewardSquare bound) (isCompact_coreRewardSquare bound)
    (continuous_sixCandidateSourceObjective δ weight hcontinuous)

/--
The two core gaps make every literal source objective coercive enough to
capture all of its global minimizers in one reward square.  The comparison is
with the fixed zero-parameter objective and holds uniformly over ε and δ.
-/
theorem exists_sixCandidateSourceObjective_capture_bound
    {weight : ℝ} {loss : ℝ → ℝ} (hweight_half : 1 / 2 ≤ weight)
    (hweight_lt_one : weight < 1) (hloss_nonnegative : ∀ input, 0 ≤ loss input)
    (hrightTail : ∀ threshold : ℝ,
      ∃ tailBound > 0, ∀ input, tailBound < input → threshold < loss input) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ ε δ parameter,
      parameter ∉ coreRewardSquare bound →
        sixCandidateSourceObjective ε δ weight loss (0, 0) <
          sixCandidateSourceObjective ε δ weight loss parameter := by
  have hweight_pos : 0 < weight := by linarith
  obtain ⟨tailBound, htailBound_pos, htailBound⟩ :=
    exists_weightedLoss_tail_bound_of_loss_rightTail
      (target := 15 * loss 0) hweight_pos hweight_lt_one hloss_nonnegative hrightTail
  refine ⟨2 * tailBound, mul_pos (by norm_num) htailBound_pos, ?_⟩
  intro ε δ parameter houtside
  have hlarge : tailBound < |parameter.1| ∨
      tailBound < |parameter.1 + parameter.2| := by
    by_contra hnotlarge
    push Not at hnotlarge
    apply houtside
    rw [coreRewardSquare, Set.mem_prod]
    constructor
    · exact abs_le.mp (le_trans hnotlarge.1 (by linarith))
    · have hsecond_abs : |parameter.2| ≤ 2 * tailBound := by
        calc
          |parameter.2| = |(parameter.1 + parameter.2) - parameter.1| := by
            congr 1
            ring
          _ ≤ |parameter.1 + parameter.2| + |parameter.1| :=
            by simpa using (abs_sub_le (parameter.1 + parameter.2) 0 parameter.1)
          _ ≤ 2 * tailBound := by linarith
      exact abs_le.mp hsecond_abs
  have hobjective := two_weightedLoss_le_sixCandidateSourceObjective parameter
    hweight_pos.le hweight_lt_one.le hloss_nonnegative (ε := ε) (δ := δ)
  have hzero := sixCandidateSourceObjective_at_zeroParameter ε δ weight loss
  rcases hlarge with hfirst | hsecond
  · have htail := htailBound parameter.1 hfirst
    have hremaining_nonnegative :
        0 ≤ weightedLoss weight loss (parameter.1 + parameter.2) :=
      weightedLoss_nonnegative hweight_pos.le hweight_lt_one.le hloss_nonnegative _
    rw [hzero]
    linarith
  · have htail := htailBound (parameter.1 + parameter.2) hsecond
    have hremaining_nonnegative : 0 ≤ weightedLoss weight loss parameter.1 :=
      weightedLoss_nonnegative hweight_pos.le hweight_lt_one.le hloss_nonnegative _
    rw [hzero]
    linarith

/--
Every literal perturbed source objective attains a global minimum once the
source loss has the required right tail.  This is a direct compactness proof,
not an invocation of an unproved argmin correspondence.
-/
theorem exists_globalMinimizer_sixCandidateSourceObjective
    {ε δ weight : ℝ} {loss : ℝ → ℝ} (hweight_half : 1 / 2 ≤ weight)
    (hweight_lt_one : weight < 1) (hloss_nonnegative : ∀ input, 0 ≤ loss input)
    (hcontinuous : Continuous loss)
    (hrightTail : ∀ threshold : ℝ,
      ∃ tailBound > 0, ∀ input, tailBound < input → threshold < loss input) :
    ∃ parameter, IsGlobalMinimizer
      (sixCandidateSourceObjective ε δ weight loss) parameter := by
  obtain ⟨bound, hbound_pos, houtside⟩ :=
    exists_sixCandidateSourceObjective_capture_bound hweight_half hweight_lt_one
      hloss_nonnegative hrightTail
  apply exists_globalMinimizer_of_compact_capture
    (isCompact_coreRewardSquare bound)
    ((continuous_sixCandidateSourceObjective δ weight hcontinuous).comp
      (continuous_const.prodMk continuous_id))
    (zero_mem_coreRewardSquare hbound_pos.le)
  intro parameter hparameter_outside
  exact houtside ε δ parameter hparameter_outside

/-- Dividing the finite profile loss by its voter count recovers the source weights. -/
theorem standardLoss_sixCandidateProfile_eq_scaledWeightedLoss
    {dimension : ℕ} (features : Candidate 4 → FeatureVector dimension)
    {majorityCount minorityCount : ℕ} (htotal_pos : 0 < majorityCount + minorityCount)
    (loss : ℝ → ℝ) (parameter : LinearRewardParameter dimension) :
    standardLoss features (sixCandidateProfile majorityCount minorityCount) loss parameter =
      (majorityCount + minorityCount : ℝ) *
        sixCandidateWeightedLoss features
          ((majorityCount : ℝ) / (majorityCount + minorityCount : ℝ)) loss parameter := by
  rw [standardLoss_sixCandidateProfile_blocks]
  unfold sixCandidateWeightedLoss
  have hden : (majorityCount + minorityCount : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt htotal_pos
  field_simp
  ring

/-- Every two-coordinate linear parameter is recovered from its two entries. -/
theorem twoCoordinateParameter_components
    (parameter : LinearRewardParameter 2) :
    twoCoordinateParameter (parameter 0, parameter 1) = parameter := by
  ext coordinate
  fin_cases coordinate <;> simp [twoCoordinateParameter]

/--
The finite `m` versus `n` source profile has standard loss equal to its
positive voter count times the literal two-coordinate source objective.
-/
theorem standardLoss_sixCandidateProfile_eq_scaledSourceObjective
    {majorityCount minorityCount : ℕ} (htotal_pos : 0 < majorityCount + minorityCount)
    {weight : ℝ}
    (hweight : weight = (majorityCount : ℝ) / (majorityCount + minorityCount : ℝ))
    (ε δ : ℝ) (loss : ℝ → ℝ) (parameter : LinearRewardParameter 2) :
    standardLoss (sixCandidateCopyFeatures ε δ)
      (sixCandidateProfile majorityCount minorityCount) loss parameter =
      (majorityCount + minorityCount : ℝ) *
        sixCandidateSourceObjective ε δ weight loss (parameter 0, parameter 1) := by
  rw [standardLoss_sixCandidateProfile_eq_scaledWeightedLoss
    (sixCandidateCopyFeatures ε δ) htotal_pos loss parameter]
  rw [← hweight]
  unfold sixCandidateSourceObjective
  rw [twoCoordinateParameter_components]

/--
Positive finite-voter scaling transports infima exactly from the literal
two-coordinate source objective to the standard loss, including a restricted
parameter region expressed through its two coordinates.
-/
theorem sInf_standardLoss_sixCandidateProfile_eq_scaledSourceObjective
    {majorityCount minorityCount : ℕ} (htotal_pos : 0 < majorityCount + minorityCount)
    {weight : ℝ}
    (hweight : weight = (majorityCount : ℝ) / (majorityCount + minorityCount : ℝ))
    (ε δ : ℝ) (loss : ℝ → ℝ) (region : Set (ℝ × ℝ)) :
    sInf (standardLoss (sixCandidateCopyFeatures ε δ)
      (sixCandidateProfile majorityCount minorityCount) loss ''
        { parameter | (parameter 0, parameter 1) ∈ region }) =
      (majorityCount + minorityCount : ℝ) *
        sInf (sixCandidateSourceObjective ε δ weight loss '' region) := by
  let scale : ℝ := (majorityCount + minorityCount : ℝ)
  let sourceObjective : (ℝ × ℝ) → ℝ :=
    sixCandidateSourceObjective ε δ weight loss
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    exact_mod_cast htotal_pos
  have hset :
      standardLoss (sixCandidateCopyFeatures ε δ)
          (sixCandidateProfile majorityCount minorityCount) loss ''
        { parameter | (parameter 0, parameter 1) ∈ region } =
        scale • (sourceObjective '' region) := by
    ext value
    constructor
    · rintro ⟨parameter, hparameter_region, rfl⟩
      refine ⟨sourceObjective (parameter 0, parameter 1),
        ⟨(parameter 0, parameter 1), hparameter_region, rfl⟩, ?_⟩
      symm
      simpa [scale, sourceObjective, smul_eq_mul] using
        (standardLoss_sixCandidateProfile_eq_scaledSourceObjective htotal_pos hweight
          ε δ loss parameter)
    · rintro ⟨value, ⟨parameter, hparameter_region, rfl⟩, hvalue⟩
      refine ⟨twoCoordinateParameter parameter, ?_, ?_⟩
      · simpa [twoCoordinateParameter] using hparameter_region
      · have hscale :=
          standardLoss_sixCandidateProfile_eq_scaledSourceObjective htotal_pos hweight
            ε δ loss (twoCoordinateParameter parameter)
        simpa [scale, sourceObjective, twoCoordinateParameter, smul_eq_mul] using
          hscale.trans hvalue
  rw [hset, Real.sInf_smul_of_nonneg hscale_pos.le]
  simp [scale, sourceObjective, smul_eq_mul]

/-- A rational weight strictly between one half and one has an exact finite-voter realization. -/
theorem exists_finiteVoterCounts_of_rational_strictMajority
    {weight : ℚ} (hhalf : (1 / 2 : ℚ) < weight) (hone : weight < 1) :
    ∃ majorityCount minorityCount : ℕ,
      minorityCount < majorityCount ∧ 0 < majorityCount + minorityCount ∧
        (weight : ℝ) = (majorityCount : ℝ) / (majorityCount + minorityCount : ℝ) := by
  let majorityCount : ℕ := weight.num.toNat
  let minorityCount : ℕ := weight.den - majorityCount
  have hweight_pos : 0 < weight := by linarith
  have hnum_pos : 0 < weight.num := Rat.num_pos.mpr hweight_pos
  have hnum_nonneg : 0 ≤ weight.num := hnum_pos.le
  have hden_pos : (0 : ℚ) < weight.den := by exact_mod_cast weight.den_pos
  have hhalf_div := hhalf
  rw [← Rat.num_div_den weight] at hhalf_div
  have hlt_one_div := hone
  rw [← Rat.num_div_den weight] at hlt_one_div
  have hnum_lt_den_q : (weight.num : ℚ) < weight.den :=
    (div_lt_one₀ hden_pos).mp hlt_one_div
  have hnum_lt_den_z : weight.num < (weight.den : ℤ) := by
    exact_mod_cast hnum_lt_den_q
  have hmajority_lt_den : majorityCount < weight.den := by
    rw [Int.toNat_lt hnum_nonneg]
    exact hnum_lt_den_z
  have hhalf_num : (1 / 2 : ℚ) * weight.den < weight.num :=
    (lt_div_iff₀ hden_pos).mp hhalf_div
  have hden_lt_twice_num_q : (weight.den : ℚ) < 2 * weight.num := by
    nlinarith
  have hden_lt_twice_num_z : (weight.den : ℤ) < 2 * weight.num := by
    exact_mod_cast hden_lt_twice_num_q
  have hnum_eq : (majorityCount : ℤ) = weight.num := by
    dsimp [majorityCount]
    exact Int.toNat_of_nonneg hnum_nonneg
  have hden_lt_twice_majority : weight.den < 2 * majorityCount := by
    have hinteger : (weight.den : ℤ) < 2 * (majorityCount : ℤ) := by
      rw [hnum_eq]
      exact hden_lt_twice_num_z
    exact_mod_cast hinteger
  have hmajority : minorityCount < majorityCount := by
    dsimp [minorityCount]
    omega
  have htotal : 0 < majorityCount + minorityCount := by omega
  refine ⟨majorityCount, minorityCount, hmajority, htotal, ?_⟩
  have hsum : majorityCount + minorityCount = weight.den := by
    dsimp [minorityCount]
    omega
  calc
    (weight : ℝ) = (weight.num : ℝ) / (weight.den : ℝ) := Rat.cast_def weight
    _ = (majorityCount : ℝ) / (weight.den : ℝ) := by
      congr 1
      exact_mod_cast hnum_eq.symm
    _ = (majorityCount : ℝ) / (majorityCount + minorityCount : ℝ) := by
      rw [← Nat.cast_add, hsum]

/--
The source-to-model bridge for the copied pair: its reward gap is exactly the
positive perturbation times the fixed copy-cone expression.
-/
theorem sixCandidateCopy_rewardGap
    (ε δ : ℝ) (parameter : LinearRewardParameter 2) :
    linearReward parameter (sixCandidateCopyFeatures ε δ) (4 : Candidate 4) -
      linearReward parameter (sixCandidateCopyFeatures ε δ) (5 : Candidate 4) =
        ε * (-parameter 0 + δ * parameter 1) := by
  unfold linearReward
  simp [sixCandidateCopyFeatures]
  ring

/--
For positive ε, the source's weak half-space `R_{c′ ≻ c}` is exactly the
closed copy-bad cone.  This is the concrete bridge used by the corrected
perturbation result.
-/
theorem sixCandidateCopy_cPrimeAboveOrTied_iff
    {ε δ : ℝ} (hε_pos : 0 < ε) (parameter : LinearRewardParameter 2) :
    linearReward parameter (sixCandidateCopyFeatures ε δ) (5 : Candidate 4) ≤
      linearReward parameter (sixCandidateCopyFeatures ε δ) (4 : Candidate 4) ↔
        copyAboveOrTiedCone δ (parameter 0, parameter 1) := by
  constructor
  · intro horder
    have hgap : 0 ≤
        linearReward parameter (sixCandidateCopyFeatures ε δ) (4 : Candidate 4) -
          linearReward parameter (sixCandidateCopyFeatures ε δ) (5 : Candidate 4) :=
      sub_nonneg.mpr horder
    rw [sixCandidateCopy_rewardGap] at hgap
    unfold copyAboveOrTiedCone
    nlinarith
  · intro hcone
    apply sub_nonneg.mp
    rw [sixCandidateCopy_rewardGap]
    exact mul_nonneg hε_pos.le hcone

/-- The coordinate bounds from Lemma 3.3 imply the intended copy cone. -/
theorem copyBelowOriginalCone_of_coordinate_bounds
    {A3 A4 δ : ℝ} {parameter : ℝ × ℝ}
    (hδ_pos : 0 < δ) (hδ_bounds : δ * A4 - A3 < 0)
    (hfirst : A3 < parameter.1) (hsecond : parameter.2 < A4) :
    copyBelowOriginalCone δ parameter := by
  unfold copyBelowOriginalCone
  have hfirst_neg : -parameter.1 < -A3 := neg_lt_neg hfirst
  have hsecond_scaled : δ * parameter.2 < δ * A4 :=
    mul_lt_mul_of_pos_left hsecond hδ_pos
  calc
    -parameter.1 + δ * parameter.2 < -A3 + δ * A4 :=
      add_lt_add hfirst_neg hsecond_scaled
    _ = δ * A4 - A3 := by ring
    _ < 0 := hδ_bounds

/-- A positive first-coordinate gap always admits a source-valid copy perturbation. -/
theorem exists_copyCone_delta
    {A3 A4 : ℝ} (hA3_pos : 0 < A3) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ * A4 - A3 < 0 := by
  by_cases hA4_nonpos : A4 ≤ 0
  · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    nlinarith
  · have hA4_pos : 0 < A4 := lt_of_not_ge hA4_nonpos
    let δ : ℝ := min (1 / 2) (A3 / (2 * A4))
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      exact lt_min (by norm_num) (div_pos hA3_pos (by positivity))
    have hδ_lt_one : δ < 1 := by
      dsimp [δ]
      exact (min_le_left _ _).trans_lt (by norm_num)
    have hδ_le : δ ≤ A3 / (2 * A4) := by
      dsimp [δ]
      exact min_le_right _ _
    have hscaled : δ * A4 ≤ (A3 / (2 * A4)) * A4 :=
      mul_le_mul_of_nonneg_right hδ_le hA4_pos.le
    have hright : (A3 / (2 * A4)) * A4 = A3 / 2 := by
      field_simp
    refine ⟨δ, hδ_pos, hδ_lt_one, ?_⟩
    rw [hright] at hscaled
    linarith

/-- The positive-ε reward gap between the source copy `c′` and `c`. -/
def perturbedCopyRewardGap (ε δ : ℝ) (parameter : ℝ × ℝ) : ℝ :=
  ε * (-parameter.1 + δ * parameter.2)

/-- A parameter in the copy cone strictly ranks the original above the copy. -/
theorem perturbedCopyRewardGap_negative
    {ε δ : ℝ} {parameter : ℝ × ℝ}
    (hε_pos : 0 < ε) (hcone : copyBelowOriginalCone δ parameter) :
    perturbedCopyRewardGap ε δ parameter < 0 := by
  unfold perturbedCopyRewardGap copyBelowOriginalCone at *
  exact mul_neg_of_pos_of_neg hε_pos hcone

/--
Corrected support statement for the useful calculation in Appendix A.3.
Because the source's `R_{c′ ≻ c}` is a weak half-space, its printed
`OPT(0)` containment is vacuous at coincident `ε = 0` features.  The final
calculation instead yields the strict positive-ε direction needed to exclude
that half-space.  This theorem records its valid ε-independent cone premise
from the Lemma 3.3 bounds.
-/
theorem corrected_lemma3_4_core_minimizers_in_copyBelowOriginalCone
    {g : ℝ → ℝ} {A3 A4 δ : ℝ}
    (hδ_pos : 0 < δ) (hδ_bounds : δ * A4 - A3 < 0)
    (hminimizer_bounds : ∀ parameter, IsGlobalMinimizer (coreLoss g) parameter →
      A3 < parameter.1 ∧ parameter.2 < A4) :
    ∀ parameter, IsGlobalMinimizer (coreLoss g) parameter →
      copyBelowOriginalCone δ parameter := by
  intro parameter hminimum
  obtain ⟨hfirst, hsecond⟩ := hminimizer_bounds parameter hminimum
  exact copyBelowOriginalCone_of_coordinate_bounds hδ_pos hδ_bounds hfirst hsecond

/--
The full corrected Lemma 3.4 cone.  Positivity of `A3` supplies the strict
`a/a′` and `b/b′` comparisons, while the displayed `δ` bound supplies the
strict `c/c′` comparison.
-/
theorem corrected_lemma3_4_core_minimizers_in_allCopiesBelowOriginalCone
    {g : ℝ → ℝ} {A3 A4 δ : ℝ}
    (hA3_pos : 0 < A3)
    (hδ_pos : 0 < δ) (hδ_bounds : δ * A4 - A3 < 0)
    (hminimizer_bounds : ∀ parameter, IsGlobalMinimizer (coreLoss g) parameter →
      A3 < parameter.1 ∧ parameter.2 < A4) :
    ∀ parameter, IsGlobalMinimizer (coreLoss g) parameter →
      allCopiesBelowOriginalCone δ parameter := by
  intro parameter hminimum
  obtain ⟨hfirst, hsecond⟩ := hminimizer_bounds parameter hminimum
  refine ⟨lt_trans hA3_pos hfirst, ?_⟩
  exact copyBelowOriginalCone_of_coordinate_bounds hδ_pos hδ_bounds hfirst hsecond

/--
The descent argument at the end of Appendix A.1.  If `g` is strictly
increasing from `w` onward, a global minimizer of the two-reward objective
cannot have both rewards strictly above `w`.
-/
theorem unconstrainedCoreLoss_minimizer_has_coordinate_le
    {g : ℝ → ℝ} {w : ℝ} {rewards : ℝ × ℝ}
    (hminimum : IsGlobalMinimizer (unconstrainedCoreLoss g) rewards)
    (hincreasing : StrictMonoOn g (Set.Ici w)) :
    rewards.1 ≤ w ∨ rewards.2 ≤ w := by
  by_contra hneither
  push Not at hneither
  let shift : ℝ := min rewards.1 rewards.2 - w
  have hshift_pos : 0 < shift := by
    dsimp [shift]
    exact sub_pos.mpr (lt_min hneither.1 hneither.2)
  have hshift_first_le : shift ≤ rewards.1 - w := by
    dsimp [shift]
    exact sub_le_sub_right (min_le_left _ _) _
  have hshift_second_le : shift ≤ rewards.2 - w := by
    dsimp [shift]
    exact sub_le_sub_right (min_le_right _ _) _
  have hfirst_mem : rewards.1 - shift ∈ Set.Ici w := by
    rw [Set.mem_Ici]
    linarith
  have hsecond_mem : rewards.2 - shift ∈ Set.Ici w := by
    rw [Set.mem_Ici]
    linarith
  have hfirst_old_mem : rewards.1 ∈ Set.Ici w := le_of_lt hneither.1
  have hsecond_old_mem : rewards.2 ∈ Set.Ici w := le_of_lt hneither.2
  have hfirst_lt : rewards.1 - shift < rewards.1 := by linarith
  have hsecond_lt : rewards.2 - shift < rewards.2 := by linarith
  have hfirstLoss : g (rewards.1 - shift) < g rewards.1 :=
    hincreasing hfirst_mem hfirst_old_mem hfirst_lt
  have hsecondLoss : g (rewards.2 - shift) < g rewards.2 :=
    hincreasing hsecond_mem hsecond_old_mem hsecond_lt
  have hdescent :
      unconstrainedCoreLoss g (rewards.1 - shift, rewards.2 - shift) <
        unconstrainedCoreLoss g rewards := by
    dsimp [unconstrainedCoreLoss]
    have hdifference :
        (rewards.1 - shift) - (rewards.2 - shift) = rewards.1 - rewards.2 := by
      ring
    rw [hdifference]
    linarith
  exact (not_lt_of_ge (hminimum (rewards.1 - shift, rewards.2 - shift))) hdescent

/--
The final ordering inference of source Lemma 3.2.  The analytic part of its
proof supplies the lower bound for the reduced one-variable minimizers; the
checked argument here transfers it to every two-reward global minimizer.
-/
theorem unconstrainedCoreLoss_minimizer_separates
    {g : ℝ → ℝ} {w gap : ℝ} {rewards : ℝ × ℝ}
    (hconvex : ConvexOn ℝ Set.univ g)
    (hincreasing : StrictMonoOn g (Set.Ici w))
    (hgap_pos : 0 < gap)
    (hreduced : ∀ reward, IsGlobalMinimizer (reducedCoreLoss g) reward →
      w + gap < reward)
    (hminimum : IsGlobalMinimizer (unconstrainedCoreLoss g) rewards) :
    w + gap < rewards.1 ∧ rewards.2 ≤ w := by
  have hfirst : w + gap < rewards.1 :=
    hreduced rewards.1
      (isGlobalMinimizer_reducedCoreLoss_of_unconstrained hconvex rewards hminimum)
  rcases unconstrainedCoreLoss_minimizer_has_coordinate_le hminimum hincreasing with
    hfirst_le | hsecond_le
  · linarith
  · exact ⟨hfirst, hsecond_le⟩

/--
The complete non-calculus conclusion of source Lemma 3.2.  Its preceding
analytic construction must provide a positive `w`, a positive right interval,
and the stated reduced-minimizer inequality; no such certificate is assumed
by a source-facing theorem endpoint.
-/
theorem lemma3_2_separation_from_reduced_analysis
    {g : ℝ → ℝ} {w gap : ℝ}
    (hw_pos : 0 < w) (hgap_pos : 0 < gap)
    (hconvex : ConvexOn ℝ Set.univ g)
    (hincreasing : StrictMonoOn g (Set.Ici w))
    (hminimum : ∃ rewards, IsGlobalMinimizer (unconstrainedCoreLoss g) rewards)
    (hreduced : ∀ reward, IsGlobalMinimizer (reducedCoreLoss g) reward →
      w + gap < reward) :
    ∃ A1 A2, A1 < A2 ∧ 0 < A2 ∧
      ∃ rewards, IsGlobalMinimizer (unconstrainedCoreLoss g) rewards ∧
        ∀ rewards, IsGlobalMinimizer (unconstrainedCoreLoss g) rewards →
          rewards.1 > A2 ∧ rewards.2 ≤ A1 := by
  refine ⟨w, w + gap, lt_add_of_pos_right w hgap_pos,
    add_pos_of_pos_of_nonneg hw_pos hgap_pos.le, ?_⟩
  obtain ⟨rewards, hminimum⟩ := hminimum
  refine ⟨rewards, hminimum, ?_⟩
  intro contender hcontender
  exact unconstrainedCoreLoss_minimizer_separates
    hconvex hincreasing hgap_pos hreduced hcontender

/--
Finite-value certificate form of source Lemma 3.2.  The source's one-sided
derivative calculation is intended to construct these two strict inequalities:
one makes `g` strictly increase from `w`, and the other excludes minimizers
of the reduced loss through `w + gap`.
-/
theorem lemma3_2_separation_from_value_certificate
    {g : ℝ → ℝ} {lower w gap rightStep : ℝ}
    (hlower_lt_w : lower < w) (hw_pos : 0 < w)
    (hgap_pos : 0 < gap) (hrightStep_pos : 0 < rightStep)
    (hconvex : ConvexOn ℝ Set.univ g)
    (hgincrease : g lower < g w)
    (hreduced_drop : reducedCoreLoss g (w + gap + rightStep) <
      reducedCoreLoss g (w + gap))
    (hminimum : ∃ rewards, IsGlobalMinimizer (unconstrainedCoreLoss g) rewards) :
    ∃ A1 A2, A1 < A2 ∧ 0 < A2 ∧
      ∃ rewards, IsGlobalMinimizer (unconstrainedCoreLoss g) rewards ∧
        ∀ rewards, IsGlobalMinimizer (unconstrainedCoreLoss g) rewards →
          rewards.1 > A2 ∧ rewards.2 ≤ A1 := by
  apply lemma3_2_separation_from_reduced_analysis hw_pos hgap_pos hconvex
    (strictMonoOn_Ici_of_convex_increase hconvex hlower_lt_w hgincrease) hminimum
  intro reward hreward
  exact isGlobalMinimizer_gt_of_convex_drop (reducedCoreLoss_convex hconvex)
    hrightStep_pos hreduced_drop hreward

/--
Lemma 3.2 reduced to its two finite strict-value certificates for the
source's actual weighted loss.  Convexity, two-sided coercivity, and
existence of an unconstrained minimizer are derived here; only the published
one-sided derivative calculation which supplies the certificates is abstracted
from this generic finite-value endpoint.  The branch theorems below derive it.
-/
theorem lemma3_2_weightedLoss_separation_from_value_certificate
    {p : ℝ} {loss : ℝ → ℝ} {negativeInput lower w gap rightStep : ℝ}
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hloss_nonnegative : ∀ input, 0 ≤ loss input)
    (hcontinuous : Continuous loss) (hconvex : ConvexOn ℝ Set.univ loss)
    (hnegative : negativeInput < 0) (hdip : loss negativeInput < loss 0)
    (hlower_lt_w : lower < w) (hw_pos : 0 < w)
    (hgap_pos : 0 < gap) (hrightStep_pos : 0 < rightStep)
    (hgincrease : weightedLoss p loss lower < weightedLoss p loss w)
    (hreduced_drop :
      reducedCoreLoss (weightedLoss p loss) (w + gap + rightStep) <
        reducedCoreLoss (weightedLoss p loss) (w + gap)) :
    ∃ A1 A2, A1 < A2 ∧ 0 < A2 ∧
      ∃ rewards, IsGlobalMinimizer (unconstrainedCoreLoss (weightedLoss p loss)) rewards ∧
        ∀ rewards, IsGlobalMinimizer (unconstrainedCoreLoss (weightedLoss p loss)) rewards →
          rewards.1 > A2 ∧ rewards.2 ≤ A1 := by
  apply lemma3_2_separation_from_value_certificate hlower_lt_w hw_pos hgap_pos
    hrightStep_pos
    (weightedLoss_convex hp_pos.le hp_lt_one.le hconvex)
    hgincrease hreduced_drop
  exact exists_unconstrainedCoreLoss_minimizer_of_convex_negative_dip hp_pos hp_lt_one
    hloss_nonnegative hcontinuous hconvex hnegative hdip

/--
Corrected differentiable form of the Appendix A.1 derivative calculation.
The four supplied derivative values are at the arguments actually used by the
displayed thresholds: `-w`, `-w/2`, `w/2`, and `w`.  From their ordered signs,
the rational-mixture algebra and the calculus bridge derive the complete
Lemma 3.2 optimizer separation.  The source's separate task of producing the
four-point data from its broad nonsmooth hypotheses remains explicit.
-/
theorem lemma3_2_weightedLoss_separation_from_four_derivatives
    {loss : ℝ → ℝ} {negativeInput w z1 z2 z3 z4 : ℝ}
    (hloss_nonnegative : ∀ input, 0 ≤ loss input)
    (hcontinuous : Continuous loss) (hconvex : ConvexOn ℝ Set.univ loss)
    (hnegative : negativeInput < 0) (hdip : loss negativeInput < loss 0)
    (hw_pos : 0 < w)
    (hderiv1 : HasDerivAt loss z1 (-w))
    (hderiv2 : HasDerivAt loss z2 (-w / 2))
    (hderiv3 : HasDerivAt loss z3 (w / 2))
    (hderiv4 : HasDerivAt loss z4 w)
    (hz1_nonnegative : 0 ≤ z1) (hz12 : z1 < z2)
    (hz23 : z2 ≤ z3) (hz34 : z3 ≤ z4) :
    ∃ p : ℚ, (1 / 2 : ℝ) < (p : ℝ) ∧ (p : ℝ) < 1 ∧
      ∃ A1 A2, A1 < A2 ∧ 0 < A2 ∧
        ∃ rewards, IsGlobalMinimizer
          (unconstrainedCoreLoss (weightedLoss (p : ℝ) loss)) rewards ∧
          ∀ rewards,
            IsGlobalMinimizer (unconstrainedCoreLoss (weightedLoss (p : ℝ) loss)) rewards →
              rewards.1 > A2 ∧ rewards.2 ≤ A1 := by
  obtain ⟨p, hhalf_p, hp_lt_one, hweighted_sign, hreduced_sign⟩ :=
    exists_rational_mixture_with_four_point_slope_signs hz1_nonnegative hz12 hz23 hz34
  let g : ℝ → ℝ := weightedLoss (p : ℝ) loss
  have hgderiv : HasDerivAt g
      (-(p : ℝ) * z1 + (1 - (p : ℝ)) * z4) w := by
    dsimp [g]
    exact hasDerivAt_weightedLoss hderiv1 hderiv4
  have hderiv2' : HasDerivAt loss z2 (-(w / 2)) := by
    convert hderiv2 using 1
    ring
  have hghalfderiv : HasDerivAt g
      (-(p : ℝ) * z2 + (1 - (p : ℝ)) * z3) (w / 2) := by
    dsimp [g]
    exact hasDerivAt_weightedLoss hderiv2' hderiv3
  have hreducedDeriv : HasDerivAt (reducedCoreLoss g)
      (-(p : ℝ) * (z1 + z2) + (1 - (p : ℝ)) * (z3 + z4)) w := by
    convert hasDerivAt_reducedCoreLoss hghalfderiv hgderiv using 1
    ring
  obtain ⟨lower, gap, rightStep, hlower_lt_w, hgap_pos, hrightStep_pos,
    hgincrease, hreduced_drop⟩ :=
    exists_value_certificate_of_derivative_signs hw_pos hgderiv hweighted_sign
      hreducedDeriv hreduced_sign
  have hp_pos : 0 < (p : ℝ) := by linarith
  refine ⟨p, hhalf_p, hp_lt_one, ?_⟩
  exact lemma3_2_weightedLoss_separation_from_value_certificate hp_pos hp_lt_one
    hloss_nonnegative hcontinuous hconvex hnegative hdip hlower_lt_w hw_pos hgap_pos
    hrightStep_pos hgincrease hreduced_drop

/--
Source-faithful nonsmooth form of the Appendix A.1 calculation.  Its four
inputs are exactly the two left and two right derivatives used in the paper:
at `-w`, `-w / 2`, `w / 2`, and `w`.  The proof then carries those one-sided
derivatives all the way through the finite optimizer-separation conclusion.

The separate source-level point-selection task is to derive the strict
ordering `z1 < z2` and the nonnegative first left derivative from the broad
loss hypotheses; it is deliberately not folded into this endpoint.
-/
theorem lemma3_2_weightedLoss_separation_from_four_oneSidedDerivatives
    {loss : ℝ → ℝ} {negativeInput w z1 z2 z3 z4 : ℝ}
    (hloss_nonnegative : ∀ input, 0 ≤ loss input)
    (hcontinuous : Continuous loss) (hconvex : ConvexOn ℝ Set.univ loss)
    (hnegative : negativeInput < 0) (hdip : loss negativeInput < loss 0)
    (hw_pos : 0 < w)
    (hderiv1 : HasDerivWithinAt loss z1 (Set.Iio (-w)) (-w))
    (hderiv2 : HasDerivWithinAt loss z2 (Set.Iio (-(w / 2))) (-(w / 2)))
    (hderiv3 : HasDerivWithinAt loss z3 (Set.Ioi (w / 2)) (w / 2))
    (hderiv4 : HasDerivWithinAt loss z4 (Set.Ioi w) w)
    (hz1_nonnegative : 0 ≤ z1) (hz12 : z1 < z2)
    (hz23 : z2 ≤ z3) (hz34 : z3 ≤ z4) :
    ∃ p : ℚ, (1 / 2 : ℝ) < (p : ℝ) ∧ (p : ℝ) < 1 ∧
      ∃ A1 A2, A1 < A2 ∧ 0 < A2 ∧
        ∃ rewards, IsGlobalMinimizer
          (unconstrainedCoreLoss (weightedLoss (p : ℝ) loss)) rewards ∧
          ∀ rewards,
            IsGlobalMinimizer (unconstrainedCoreLoss (weightedLoss (p : ℝ) loss)) rewards →
              rewards.1 > A2 ∧ rewards.2 ≤ A1 := by
  obtain ⟨p, hhalf_p, hp_lt_one, hweighted_sign, hreduced_sign⟩ :=
    exists_rational_mixture_with_four_point_slope_signs hz1_nonnegative hz12 hz23 hz34
  have hp_pos : 0 < (p : ℝ) := by linarith
  let g : ℝ → ℝ := weightedLoss (p : ℝ) loss
  have hgconvex : ConvexOn ℝ Set.univ g := by
    dsimp [g]
    exact weightedLoss_convex hp_pos.le hp_lt_one.le hconvex
  have hgderiv : HasDerivWithinAt g
      (-(p : ℝ) * z1 + (1 - (p : ℝ)) * z4) (Set.Ioi w) w := by
    dsimp [g]
    exact hasDerivWithinAt_weightedLoss_right hderiv1 hderiv4
  have hghalfderiv : HasDerivWithinAt g
      (-(p : ℝ) * z2 + (1 - (p : ℝ)) * z3) (Set.Ioi (w / 2)) (w / 2) := by
    dsimp [g]
    exact hasDerivWithinAt_weightedLoss_right hderiv2 hderiv3
  have hreducedDeriv : HasDerivWithinAt (reducedCoreLoss g)
      (-(p : ℝ) * (z1 + z2) + (1 - (p : ℝ)) * (z3 + z4)) (Set.Ioi w) w := by
    convert hasDerivWithinAt_reducedCoreLoss_right hghalfderiv hgderiv using 1
    ring
  have hgincreasing : StrictMonoOn g (Set.Ici w) :=
    strictMonoOn_Ici_of_convex_right_derivative_pos hgconvex hgderiv hweighted_sign
  obtain ⟨right, hw_lt_right, hright_drop⟩ :=
    exists_value_lt_of_hasDerivWithinAt_right_neg hreducedDeriv hreduced_sign
  have hcontinuous_g : Continuous g := by
    dsimp [g]
    exact continuous_weightedLoss hcontinuous
  obtain ⟨gap, rightStep, hgap_pos, hrightStep_pos, hreduced_drop⟩ :=
    exists_reduced_drop_certificate_of_right_value_drop
      (continuous_reducedCoreLoss hcontinuous_g) hw_lt_right hright_drop
  have hminimum : ∃ rewards, IsGlobalMinimizer (unconstrainedCoreLoss g) rewards := by
    dsimp [g]
    exact exists_unconstrainedCoreLoss_minimizer_of_convex_negative_dip hp_pos hp_lt_one
      hloss_nonnegative hcontinuous hconvex hnegative hdip
  have hreduced : ∀ reward, IsGlobalMinimizer (reducedCoreLoss g) reward →
      w + gap < reward := by
    intro reward hminimum_reward
    exact isGlobalMinimizer_gt_of_convex_drop (reducedCoreLoss_convex hgconvex)
      hrightStep_pos hreduced_drop hminimum_reward
  refine ⟨p, hhalf_p, hp_lt_one, ?_⟩
  exact lemma3_2_separation_from_reduced_analysis hw_pos hgap_pos hgconvex hgincreasing
    hminimum hreduced

/--
A continuous objective with a global minimizer has a positive value gap on a
compact set containing no global minimizer.  This is the compactness portion
of the Berge-style argument used in Appendix A.4.
-/
theorem exists_compact_gap_of_global_minimizers_avoid
    {Parameter : Type*} [TopologicalSpace Parameter]
    (objective : Parameter → ℝ) (base : Parameter) (bad : Set Parameter)
    (hglobal : IsGlobalMinimizer objective base)
    (havoid : ∀ parameter, IsGlobalMinimizer objective parameter → parameter ∉ bad)
    (hcompact : IsCompact bad) (hnonempty : bad.Nonempty)
    (hcontinuous : Continuous objective) :
    ∃ gap : ℝ, 0 < gap ∧
      ∀ parameter, parameter ∈ bad → objective base + 3 * gap ≤ objective parameter := by
  obtain ⟨minimizer, hminimizer_bad, hminimum⟩ :=
    hcompact.exists_isMinOn hnonempty hcontinuous.continuousOn
  have hbase_le : objective base ≤ objective minimizer := hglobal minimizer
  have hbase_ne : objective base ≠ objective minimizer := by
    intro hequal
    have hminimizer_global : IsGlobalMinimizer objective minimizer := by
      intro contender
      calc
        objective minimizer = objective base := hequal.symm
        _ ≤ objective contender := hglobal contender
    exact havoid minimizer hminimizer_global hminimizer_bad
  have hbase_lt : objective base < objective minimizer :=
    lt_of_le_of_ne hbase_le hbase_ne
  refine ⟨(objective minimizer - objective base) / 4,
    div_pos (sub_pos.mpr hbase_lt) (by norm_num), ?_⟩
  intro parameter hparameter_bad
  have hminimum_le : objective minimizer ≤ objective parameter :=
    hminimum hparameter_bad
  linarith

/--
The strict infimum comparison needed in Lemma 3.5 follows from compact
separation once a global minimizer exists.  This is stated directly for the
image of the forbidden parameter region, so a source instance only has to
supply its compactness and the corrected argmin-exclusion property.
-/
theorem restrictedInfimum_gt_global_of_compact_avoid
    {Parameter : Type*} [TopologicalSpace Parameter]
    (objective : Parameter → ℝ) (base : Parameter) (bad : Set Parameter)
    (hglobal : IsGlobalMinimizer objective base)
    (havoid : ∀ parameter, IsGlobalMinimizer objective parameter → parameter ∉ bad)
    (hcompact : IsCompact bad) (hnonempty : bad.Nonempty)
    (hcontinuous : Continuous objective) :
    sInf (objective '' bad) > sInf (Set.range objective) := by
  obtain ⟨gap, hgap_pos, hgap⟩ := exists_compact_gap_of_global_minimizers_avoid
    objective base bad hglobal havoid hcompact hnonempty hcontinuous
  have hbad_nonempty : (objective '' bad).Nonempty := hnonempty.image objective
  have hglobal_nonempty : (Set.range objective).Nonempty := ⟨objective base, ⟨base, rfl⟩⟩
  have hglobal_below : BddBelow (Set.range objective) := by
    refine ⟨objective base, ?_⟩
    rintro value ⟨parameter, rfl⟩
    exact hglobal parameter
  have hbad_lower : objective base + 3 * gap ≤ sInf (objective '' bad) := by
    apply le_csInf
    · exact hbad_nonempty
    · rintro value ⟨parameter, hparameter_bad, rfl⟩
      exact hgap parameter hparameter_bad
  have hglobal_lower : objective base ≤ sInf (Set.range objective) := by
    apply le_csInf
    · exact hglobal_nonempty
    · rintro value ⟨parameter, rfl⟩
      exact hglobal parameter
  have hglobal_upper : sInf (Set.range objective) ≤ objective base :=
    csInf_le hglobal_below ⟨base, rfl⟩
  have hglobal_infimum : sInf (Set.range objective) = objective base :=
    le_antisymm hglobal_upper hglobal_lower
  rw [hglobal_infimum]
  linarith

/--
Uniformly small objective perturbations cannot move a global minimizer into a
region separated by a three-gap margin at the reference parameter value.
-/
theorem globalMinimizer_avoids_bad_of_uniform_gap
    {Parameter : Type*} (objective : ℝ → Parameter → ℝ)
    (base parameter : Parameter) (bad : Set Parameter) {ε gap : ℝ}
    (hgap_pos : 0 < gap)
    (hgap : ∀ contender, contender ∈ bad →
      objective 0 base + 3 * gap ≤ objective 0 contender)
    (huniform : ∀ contender,
      |objective ε contender - objective 0 contender| < gap)
    (hminimum : IsGlobalMinimizer (objective ε) parameter) :
    parameter ∉ bad := by
  intro hparameter_bad
  have hparameter_error := abs_lt.mp (huniform parameter)
  have hbase_error := abs_lt.mp (huniform base)
  have hparameter_gap := hgap parameter hparameter_bad
  have hbetter : objective ε base < objective ε parameter := by
    linarith
  exact (not_lt_of_ge (hminimum base)) hbetter

/--
Compact argmin stability under an explicitly uniform perturbation bound.  In
the source, joint continuity on a bounded parameter region is intended to
supply this bound; keeping it explicit avoids treating Berge's theorem as an
unproved black box.
-/
theorem exists_radius_globalMinimizers_avoid_compact_bad
    {Parameter : Type*} [TopologicalSpace Parameter]
    (objective : ℝ → Parameter → ℝ) (base : Parameter) (bad : Set Parameter)
    (hglobal : IsGlobalMinimizer (objective 0) base)
    (havoid : ∀ parameter, IsGlobalMinimizer (objective 0) parameter → parameter ∉ bad)
    (hcompact : IsCompact bad) (hnonempty : bad.Nonempty)
    (hcontinuous_zero : Continuous (objective 0))
    (huniform : ∀ tolerance : ℝ, 0 < tolerance → ∃ radius : ℝ, 0 < radius ∧
      ∀ ε, |ε| < radius → ∀ parameter,
        |objective ε parameter - objective 0 parameter| < tolerance) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ ε, |ε| < radius → ∀ parameter,
      IsGlobalMinimizer (objective ε) parameter → parameter ∉ bad := by
  obtain ⟨gap, hgap_pos, hgap⟩ := exists_compact_gap_of_global_minimizers_avoid
    (objective 0) base bad hglobal havoid hcompact hnonempty hcontinuous_zero
  obtain ⟨radius, hradius_pos, huniform_radius⟩ := huniform gap hgap_pos
  refine ⟨radius, hradius_pos, ?_⟩
  intro ε hε parameter hminimum
  exact globalMinimizer_avoids_bad_of_uniform_gap objective base parameter bad hgap_pos hgap
    (huniform_radius ε hε) hminimum

/--
Corrected positive-ε replacement for the stability conclusion intended by
Lemmas 3.4--3.5.  If zero-perturbation minimizers lie in the strict copy cone
and all perturbed minimizers stay in the source's bounded parameter square,
then sufficiently small perturbations keep every minimizer in that strict
cone.  The conclusion is precisely what excludes the closed weak bad region.
-/
theorem exists_radius_globalMinimizers_in_copyBelowOriginalCone
    (objective : ℝ → (ℝ × ℝ) → ℝ) (base : ℝ × ℝ) (bound δ : ℝ)
    (hbound : 0 ≤ bound)
    (hglobal : IsGlobalMinimizer (objective 0) base)
    (hzero_below : ∀ parameter, IsGlobalMinimizer (objective 0) parameter →
      copyBelowOriginalCone δ parameter)
    (hcontinuous_zero : Continuous (objective 0))
    (huniform : ∀ tolerance : ℝ, 0 < tolerance → ∃ radius : ℝ, 0 < radius ∧
      ∀ ε, |ε| < radius → ∀ parameter,
        |objective ε parameter - objective 0 parameter| < tolerance)
    (hcapture : ∀ ε parameter, IsGlobalMinimizer (objective ε) parameter →
      parameter ∈ coreRewardSquare bound) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ ε, |ε| < radius → ∀ parameter,
      IsGlobalMinimizer (objective ε) parameter → copyBelowOriginalCone δ parameter := by
  have havoid : ∀ parameter, IsGlobalMinimizer (objective 0) parameter →
      parameter ∉ copyBadRegion bound δ := by
    intro parameter hminimum hbad
    exact (not_lt_of_ge hbad.2) (hzero_below parameter hminimum)
  obtain ⟨radius, hradius_pos, hradius⟩ :=
    exists_radius_globalMinimizers_avoid_compact_bad objective base
      (copyBadRegion bound δ) hglobal havoid
      (isCompact_copyBadRegion bound δ)
      ⟨(0, 0), zero_mem_copyBadRegion hbound⟩ hcontinuous_zero huniform
  refine ⟨radius, hradius_pos, ?_⟩
  intro ε hε parameter hminimum
  by_contra hnotbelow
  apply hradius ε hε parameter hminimum
  refine ⟨hcapture ε parameter hminimum, ?_⟩
  exact le_of_not_gt hnotbelow

/--
On the bounded bad region, the corrected small-perturbation conclusion yields
the strict restricted-versus-global infimum gap used in the final loss-based
decision step.  A concrete source instance must additionally prove that no
unbounded parameter can improve this restricted infimum.
-/
theorem exists_radius_boundedRestrictedInfimum_gt_global
    (objective : ℝ → (ℝ × ℝ) → ℝ) (base : ℝ × ℝ) (bound δ : ℝ)
    (hbound : 0 ≤ bound)
    (hglobal : IsGlobalMinimizer (objective 0) base)
    (hzero_below : ∀ parameter, IsGlobalMinimizer (objective 0) parameter →
      copyBelowOriginalCone δ parameter)
    (hcontinuous : ∀ ε, Continuous (objective ε))
    (huniform : ∀ tolerance : ℝ, 0 < tolerance → ∃ radius : ℝ, 0 < radius ∧
      ∀ ε, |ε| < radius → ∀ parameter,
        |objective ε parameter - objective 0 parameter| < tolerance)
    (hcapture : ∀ ε parameter, IsGlobalMinimizer (objective ε) parameter →
      parameter ∈ coreRewardSquare bound)
    (hminimizer : ∀ ε, ∃ parameter, IsGlobalMinimizer (objective ε) parameter) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ ε, |ε| < radius →
      sInf (objective ε '' copyBadRegion bound δ) > sInf (Set.range (objective ε)) := by
  obtain ⟨radius, hradius_pos, hradius⟩ :=
    exists_radius_globalMinimizers_in_copyBelowOriginalCone objective base bound δ hbound
      hglobal hzero_below (hcontinuous 0) huniform hcapture
  refine ⟨radius, hradius_pos, ?_⟩
  intro ε hε
  obtain ⟨parameter, hparameter_minimum⟩ := hminimizer ε
  apply restrictedInfimum_gt_global_of_compact_avoid
    (objective ε) parameter (copyBadRegion bound δ) hparameter_minimum
  · intro contender hcontender hbad
    exact (not_lt_of_ge hbad.2) (hradius ε hε contender hcontender)
  · exact isCompact_copyBadRegion bound δ
  · exact ⟨(0, 0), zero_mem_copyBadRegion hbound⟩
  · exact hcontinuous ε

/--
The bounded perturbation theorem with the uniformity hypothesis stated only on
the square that captures all global minimizers.  This is the valid form for
the literal six-candidate objective: requiring uniform ε-control over the
whole unbounded parameter space would be unjustified.
-/
theorem exists_radius_boundedRestrictedInfimum_gt_global_on_compactCapture
    (objective : ℝ → (ℝ × ℝ) → ℝ) (base : ℝ × ℝ) (bound δ : ℝ)
    (hbound : 0 ≤ bound)
    (hglobal : IsGlobalMinimizer (objective 0) base)
    (hzero_below : ∀ parameter, IsGlobalMinimizer (objective 0) parameter →
      copyBelowOriginalCone δ parameter)
    (hcontinuous : ∀ ε, Continuous (objective ε))
    (huniform : ∀ tolerance : ℝ, 0 < tolerance → ∃ radius : ℝ, 0 < radius ∧
      ∀ ε, |ε| < radius → ∀ parameter, parameter ∈ coreRewardSquare bound →
        |objective ε parameter - objective 0 parameter| < tolerance)
    (hcapture : ∀ ε parameter, IsGlobalMinimizer (objective ε) parameter →
      parameter ∈ coreRewardSquare bound)
    (hminimizer : ∀ ε, ∃ parameter, IsGlobalMinimizer (objective ε) parameter) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ ε, |ε| < radius →
      sInf (objective ε '' copyBadRegion bound δ) > sInf (Set.range (objective ε)) := by
  have havoid_zero : ∀ parameter, IsGlobalMinimizer (objective 0) parameter →
      parameter ∉ copyBadRegion bound δ := by
    intro parameter hminimum hbad
    exact (not_lt_of_ge hbad.2) (hzero_below parameter hminimum)
  obtain ⟨gap, hgap_pos, hgap⟩ := exists_compact_gap_of_global_minimizers_avoid
    (objective 0) base (copyBadRegion bound δ) hglobal havoid_zero
      (isCompact_copyBadRegion bound δ)
      ⟨(0, 0), zero_mem_copyBadRegion hbound⟩ (hcontinuous 0)
  obtain ⟨radius, hradius_pos, huniform_radius⟩ := huniform gap hgap_pos
  refine ⟨radius, hradius_pos, ?_⟩
  intro ε hε
  obtain ⟨parameter, hparameter_minimum⟩ := hminimizer ε
  apply restrictedInfimum_gt_global_of_compact_avoid
    (objective ε) parameter (copyBadRegion bound δ) hparameter_minimum
  · intro contender hcontender_minimum hcontender_bad
    have hcontender_error := abs_lt.mp
      (huniform_radius ε hε contender (hcapture ε contender hcontender_minimum))
    have hbase_error := abs_lt.mp
      (huniform_radius ε hε base (hcapture 0 base hglobal))
    have hgap_contender := hgap contender hcontender_bad
    have hbetter : objective ε base < objective ε contender := by
      linarith
    exact (not_lt_of_ge (hcontender_minimum base)) hbetter
  · exact isCompact_copyBadRegion bound δ
  · exact ⟨(0, 0), zero_mem_copyBadRegion hbound⟩
  · exact hcontinuous ε

/--
At ε = 0, the literal six-candidate objective and the source core objective
have exactly the same global minimizers: the former is four positive copies
of the latter plus a constant.
-/
theorem isGlobalMinimizer_sixCandidateSourceObjective_zero_iff
    (δ weight : ℝ) (loss : ℝ → ℝ) (parameter : ℝ × ℝ) :
    IsGlobalMinimizer (sixCandidateSourceObjective 0 δ weight loss) parameter ↔
      IsGlobalMinimizer (coreLoss (weightedLoss weight loss)) parameter := by
  constructor
  · intro hminimum contender
    have h := hminimum contender
    rw [sixCandidateSourceObjective_zero δ weight loss parameter,
      sixCandidateSourceObjective_zero δ weight loss contender] at h
    nlinarith
  · intro hminimum contender
    have h := hminimum contender
    rw [sixCandidateSourceObjective_zero δ weight loss parameter,
      sixCandidateSourceObjective_zero δ weight loss contender]
    nlinarith

/--
The source Lemma 3.3 coordinate separation puts every core optimizer in the
strict copy-below-original cone once δ has been chosen with
`δ * A4 - A3 < 0`.
-/
theorem copyBelowOriginalCone_of_core_coordinate_separation
    {A3 A4 δ : ℝ} {parameter : ℝ × ℝ}
    (hδ_pos : 0 < δ) (hchoice : δ * A4 - A3 < 0)
    (hfirst : A3 < parameter.1) (hsecond : parameter.2 < A4) :
    copyBelowOriginalCone δ parameter := by
  have hscaled_second : δ * parameter.2 < δ * A4 :=
    mul_lt_mul_of_pos_left hsecond hδ_pos
  unfold copyBelowOriginalCone
  linarith

/--
Corrected bounded version of the source's Lemma 3.5 for its literal
six-candidate objective.  The assumptions are exactly the valid seam from
Lemmas 3.2--3.4: core minimizers are strictly copy-below-original at ε = 0.
Unlike the published proof, uniform continuity is used only on the compact
square that the loss coercivity proof captures.
-/
theorem exists_radius_boundedGap_sixCandidateSourceObjective
    {δ weight : ℝ} {loss : ℝ → ℝ} {base : ℝ × ℝ}
    (hweight_half : 1 / 2 ≤ weight) (hweight_lt_one : weight < 1)
    (hloss_nonnegative : ∀ input, 0 ≤ loss input)
    (hcontinuous : Continuous loss)
    (hrightTail : ∀ threshold : ℝ,
      ∃ tailBound > 0, ∀ input, tailBound < input → threshold < loss input)
    (hcore_global : IsGlobalMinimizer (coreLoss (weightedLoss weight loss)) base)
    (hcore_below : ∀ parameter,
      IsGlobalMinimizer (coreLoss (weightedLoss weight loss)) parameter →
        copyBelowOriginalCone δ parameter) :
    ∃ bound radius : ℝ, 0 < bound ∧
      (∀ ε δ parameter, parameter ∉ coreRewardSquare bound →
        sixCandidateSourceObjective ε δ weight loss (0, 0) <
          sixCandidateSourceObjective ε δ weight loss parameter) ∧
      0 < radius ∧ ∀ ε, |ε| < radius →
        sInf (sixCandidateSourceObjective ε δ weight loss '' copyBadRegion bound δ) >
          sInf (Set.range (sixCandidateSourceObjective ε δ weight loss)) := by
  let objective : ℝ → (ℝ × ℝ) → ℝ :=
    fun ε parameter => sixCandidateSourceObjective ε δ weight loss parameter
  change ∃ bound radius : ℝ, 0 < bound ∧
    (∀ ε δ parameter, parameter ∉ coreRewardSquare bound →
      sixCandidateSourceObjective ε δ weight loss (0, 0) <
        sixCandidateSourceObjective ε δ weight loss parameter) ∧
    0 < radius ∧ ∀ ε, |ε| < radius →
      sInf (objective ε '' copyBadRegion bound δ) > sInf (Set.range (objective ε))
  obtain ⟨bound, hbound_pos, houtside⟩ :=
    exists_sixCandidateSourceObjective_capture_bound hweight_half hweight_lt_one
      hloss_nonnegative hrightTail
  have hglobal_zero :
      IsGlobalMinimizer (objective 0) base := by
    simpa [objective] using
      (isGlobalMinimizer_sixCandidateSourceObjective_zero_iff δ weight loss base).mpr
        hcore_global
  have hzero_below : ∀ parameter,
      IsGlobalMinimizer (objective 0) parameter →
        copyBelowOriginalCone δ parameter := by
    intro parameter hminimum
    exact hcore_below parameter
      ((isGlobalMinimizer_sixCandidateSourceObjective_zero_iff δ weight loss parameter).mp
        (by simpa [objective] using hminimum))
  obtain ⟨radius, hradius_pos, hradius⟩ :=
    exists_radius_boundedRestrictedInfimum_gt_global_on_compactCapture
      objective base bound δ hbound_pos.le
      hglobal_zero hzero_below
      (fun ε =>
        by simpa [objective] using
          ((continuous_sixCandidateSourceObjective δ weight hcontinuous).comp
            (continuous_const.prodMk continuous_id)))
      (by simpa [objective] using
        (uniformPerturbation_sixCandidateSourceObjective_on_coreRewardSquare
          bound δ weight hcontinuous))
      (fun ε parameter hminimum => by
        by_contra hnot_capture
        have hstrict := houtside ε δ parameter hnot_capture
        exact (not_lt_of_ge (hminimum (0, 0))) (by simpa [objective] using hstrict))
      (fun ε => by simpa [objective] using
        (exists_globalMinimizer_sixCandidateSourceObjective
          hweight_half hweight_lt_one hloss_nonnegative hcontinuous hrightTail))
  exact ⟨bound, radius, hbound_pos, houtside, hradius_pos, hradius⟩

/--
If every core global minimizer lies in the strict copy-below cone, then the
core global value is strictly below its value at the zero parameter.  In
particular, zero cannot itself be a global minimizer.
-/
theorem coreLoss_global_lt_zero_of_all_minimizers_copyBelow
    {δ weight : ℝ} {loss : ℝ → ℝ} {base : ℝ × ℝ}
    (hglobal : IsGlobalMinimizer (coreLoss (weightedLoss weight loss)) base)
    (hbelow : ∀ parameter,
      IsGlobalMinimizer (coreLoss (weightedLoss weight loss)) parameter →
        copyBelowOriginalCone δ parameter) :
    coreLoss (weightedLoss weight loss) base <
      coreLoss (weightedLoss weight loss) (0, 0) := by
  have hle := hglobal (0, 0)
  apply lt_of_le_of_ne hle
  intro hequal
  have hzero_global :
      IsGlobalMinimizer (coreLoss (weightedLoss weight loss)) (0, 0) := by
    intro contender
    rw [← hequal]
    exact hglobal contender
  have hzero_below := hbelow (0, 0) hzero_global
  unfold copyBelowOriginalCone at hzero_below
  linarith

/--
A strict objective improvement at a fixed reference parameter persists for
all sufficiently small perturbations.  This elementary continuity lemma is
used to keep the source's unbounded bad region above the global value.
-/
theorem exists_radius_objective_base_lt_zeroParameter
    (objective : ℝ → (ℝ × ℝ) → ℝ) (base : ℝ × ℝ)
    (hcontinuous : Continuous (fun ε =>
      objective ε base - objective ε (0, 0)))
    (hstrict : objective 0 base < objective 0 (0, 0)) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ ε, |ε| < radius →
      objective ε base < objective ε (0, 0) := by
  let difference : ℝ → ℝ := fun ε => objective ε base - objective ε (0, 0)
  have hdifference : Continuous difference := hcontinuous
  have hzero : difference 0 < 0 := by
    exact sub_neg.mpr hstrict
  have hneighborhood : difference ⁻¹' Set.Iio 0 ∈ 𝓝 0 :=
    (isOpen_Iio.preimage hdifference).mem_nhds hzero
  obtain ⟨radius, hradius_pos, hball⟩ := Metric.mem_nhds_iff.mp hneighborhood
  refine ⟨radius, hradius_pos, ?_⟩
  intro ε hε
  have hε_ball : ε ∈ Metric.ball 0 radius := by
    simpa [Metric.mem_ball, Real.dist_eq] using hε
  have hnegative : difference ε < 0 := hball hε_ball
  exact sub_neg.mp hnegative

/--
Extending a compact bad-region gap to the full closed copy-bad cone is valid
once the coercive exterior lies strictly above the zero parameter and a fixed
reference parameter lies strictly below zero.  This supplies the step that
the published Lemma 3.5 leaves implicit after localizing minimizers.
-/
theorem restrictedInfimum_gt_global_of_boundedGap_and_zeroBarrier
    (objective : (ℝ × ℝ) → ℝ) (base : ℝ × ℝ) (bound δ : ℝ)
    (hbound : 0 ≤ bound)
    (hbounded_gap :
      sInf (objective '' copyBadRegion bound δ) > sInf (Set.range objective))
    (hminimizer : ∃ parameter, IsGlobalMinimizer objective parameter)
    (hbase_below_zero : objective base < objective (0, 0))
    (houtside : ∀ parameter, parameter ∉ coreRewardSquare bound →
      objective (0, 0) < objective parameter) :
    sInf (objective '' { parameter | copyAboveOrTiedCone δ parameter }) >
      sInf (Set.range objective) := by
  obtain ⟨minimum, hminimum⟩ := hminimizer
  have hglobal_bdd : BddBelow (Set.range objective) := by
    refine ⟨objective minimum, ?_⟩
    rintro value ⟨parameter, rfl⟩
    exact hminimum parameter
  have hglobal_le_base : sInf (Set.range objective) ≤ objective base :=
    csInf_le hglobal_bdd ⟨base, rfl⟩
  have hzero_gt_global : sInf (Set.range objective) < objective (0, 0) := by
    linarith
  have hbounded_nonempty : (objective '' copyBadRegion bound δ).Nonempty :=
    ⟨objective (0, 0), ⟨(0, 0), zero_mem_copyBadRegion hbound, rfl⟩⟩
  have hbounded_bdd : BddBelow (objective '' copyBadRegion bound δ) := by
    refine ⟨objective minimum, ?_⟩
    rintro value ⟨parameter, _hparameter, rfl⟩
    exact hminimum parameter
  let lower : ℝ := min (sInf (objective '' copyBadRegion bound δ)) (objective (0, 0))
  have hlower_gt_global : sInf (Set.range objective) < lower := by
    dsimp [lower]
    exact lt_min hbounded_gap hzero_gt_global
  have hfull_nonempty :
      (objective '' { parameter | copyAboveOrTiedCone δ parameter }).Nonempty :=
    ⟨objective (0, 0), ⟨(0, 0), by
      unfold copyAboveOrTiedCone
      norm_num, rfl⟩⟩
  have hlower_bound : ∀ value,
      value ∈ objective '' { parameter | copyAboveOrTiedCone δ parameter } → lower ≤ value := by
    rintro value ⟨parameter, hparameter_bad, rfl⟩
    by_cases hparameter_square : parameter ∈ coreRewardSquare bound
    · have hbounded_member : parameter ∈ copyBadRegion bound δ :=
        ⟨hparameter_square, hparameter_bad⟩
      have hinf_le : sInf (objective '' copyBadRegion bound δ) ≤ objective parameter :=
        csInf_le hbounded_bdd ⟨parameter, hbounded_member, rfl⟩
      dsimp [lower]
      exact le_trans (min_le_left _ _) hinf_le
    · have hzero_lt := houtside parameter hparameter_square
      dsimp [lower]
      exact (min_le_right _ _).trans (le_of_lt hzero_lt)
  have hlower_le_full : lower ≤
      sInf (objective '' { parameter | copyAboveOrTiedCone δ parameter }) := by
    apply le_csInf hfull_nonempty
    exact hlower_bound
  exact lt_of_lt_of_le hlower_gt_global hlower_le_full

/--
Source-instance form of the repaired Lemma 3.5: under the Lemmas 3.2--3.4
core-minimizer seam, the literal six-candidate objective has a strict gap on
the entire closed copy-bad cone for all sufficiently small perturbations.
-/
theorem exists_radius_fullCopyBadConeGap_sixCandidateSourceObjective
    {δ weight : ℝ} {loss : ℝ → ℝ} {base : ℝ × ℝ}
    (hweight_half : 1 / 2 ≤ weight) (hweight_lt_one : weight < 1)
    (hloss_nonnegative : ∀ input, 0 ≤ loss input)
    (hcontinuous : Continuous loss)
    (hrightTail : ∀ threshold : ℝ,
      ∃ tailBound > 0, ∀ input, tailBound < input → threshold < loss input)
    (hcore_global : IsGlobalMinimizer (coreLoss (weightedLoss weight loss)) base)
    (hcore_below : ∀ parameter,
      IsGlobalMinimizer (coreLoss (weightedLoss weight loss)) parameter →
        copyBelowOriginalCone δ parameter) :
    ∃ bound radius : ℝ, 0 < bound ∧ 0 < radius ∧ ∀ ε, |ε| < radius →
      sInf (sixCandidateSourceObjective ε δ weight loss ''
        { parameter | copyAboveOrTiedCone δ parameter }) >
        sInf (Set.range (sixCandidateSourceObjective ε δ weight loss)) := by
  let objective : ℝ → (ℝ × ℝ) → ℝ :=
    fun ε parameter => sixCandidateSourceObjective ε δ weight loss parameter
  change ∃ bound radius : ℝ, 0 < bound ∧ 0 < radius ∧ ∀ ε, |ε| < radius →
    sInf (objective ε '' { parameter | copyAboveOrTiedCone δ parameter }) >
      sInf (Set.range (objective ε))
  obtain ⟨bound, boundedRadius, hbound_pos, houtside, hboundedRadius_pos, hboundedGap⟩ :=
    exists_radius_boundedGap_sixCandidateSourceObjective
      hweight_half hweight_lt_one hloss_nonnegative hcontinuous hrightTail
      hcore_global hcore_below
  have hcore_strict : coreLoss (weightedLoss weight loss) base <
      coreLoss (weightedLoss weight loss) (0, 0) :=
    coreLoss_global_lt_zero_of_all_minimizers_copyBelow hcore_global hcore_below
  have hzero_strict : objective 0 base < objective 0 (0, 0) := by
    change sixCandidateSourceObjective 0 δ weight loss base <
      sixCandidateSourceObjective 0 δ weight loss (0, 0)
    rw [sixCandidateSourceObjective_zero δ weight loss base,
      sixCandidateSourceObjective_zero δ weight loss (0, 0)]
    nlinarith
  have hdifference_continuous : Continuous (fun ε =>
      objective ε base - objective ε (0, 0)) := by
    have hbase : Continuous (fun ε => objective ε base) := by
      simpa [objective] using
        (continuous_sixCandidateSourceObjective δ weight hcontinuous).comp
          (continuous_id.prodMk continuous_const)
    have hzero : Continuous (fun ε => objective ε (0, 0)) := by
      simpa [objective] using
        (continuous_sixCandidateSourceObjective δ weight hcontinuous).comp
          (continuous_id.prodMk continuous_const)
    exact hbase.sub hzero
  obtain ⟨zeroRadius, hzeroRadius_pos, hbase_below_zero⟩ :=
    exists_radius_objective_base_lt_zeroParameter objective base
      hdifference_continuous hzero_strict
  refine ⟨bound, min boundedRadius zeroRadius,
    hbound_pos, lt_min hboundedRadius_pos hzeroRadius_pos, ?_⟩
  intro ε hε
  have hε_bounded : |ε| < boundedRadius := lt_of_lt_of_le hε (min_le_left _ _)
  have hε_zero : |ε| < zeroRadius := lt_of_lt_of_le hε (min_le_right _ _)
  apply restrictedInfimum_gt_global_of_boundedGap_and_zeroBarrier
    (objective ε) base bound δ hbound_pos.le
  · simpa [objective] using hboundedGap ε hε_bounded
  · simpa [objective] using
      (exists_globalMinimizer_sixCandidateSourceObjective
        hweight_half hweight_lt_one hloss_nonnegative hcontinuous hrightTail)
  · exact hbase_below_zero ε hε_zero
  · intro parameter hparameter_outside
    have hstrict := houtside ε δ parameter hparameter_outside
    simpa [objective] using hstrict

/--
For positive ε, the repaired gap is exactly a gap over parameters weakly
ranking the unanimously preferred source copy `c′` above its original `c`.
-/
theorem exists_radius_cPrimeAboveOrTiedGap_sixCandidateSourceObjective
    {δ weight : ℝ} {loss : ℝ → ℝ} {base : ℝ × ℝ}
    (hweight_half : 1 / 2 ≤ weight) (hweight_lt_one : weight < 1)
    (hloss_nonnegative : ∀ input, 0 ≤ loss input)
    (hcontinuous : Continuous loss)
    (hrightTail : ∀ threshold : ℝ,
      ∃ tailBound > 0, ∀ input, tailBound < input → threshold < loss input)
    (hcore_global : IsGlobalMinimizer (coreLoss (weightedLoss weight loss)) base)
    (hcore_below : ∀ parameter,
      IsGlobalMinimizer (coreLoss (weightedLoss weight loss)) parameter →
        copyBelowOriginalCone δ parameter) :
    ∃ bound radius : ℝ, 0 < bound ∧ 0 < radius ∧ ∀ ε, 0 < ε → ε < radius →
      sInf (sixCandidateSourceObjective ε δ weight loss ''
        { parameter |
          linearReward (twoCoordinateParameter parameter) (sixCandidateCopyFeatures ε δ)
              (5 : Candidate 4) ≤
            linearReward (twoCoordinateParameter parameter) (sixCandidateCopyFeatures ε δ)
              (4 : Candidate 4) }) >
        sInf (Set.range (sixCandidateSourceObjective ε δ weight loss)) := by
  obtain ⟨bound, radius, hbound_pos, hradius_pos, hcone_gap⟩ :=
    exists_radius_fullCopyBadConeGap_sixCandidateSourceObjective
      hweight_half hweight_lt_one hloss_nonnegative hcontinuous hrightTail
      hcore_global hcore_below
  refine ⟨bound, radius, hbound_pos, hradius_pos, ?_⟩
  intro ε hε_pos hε_radius
  have hcone := hcone_gap ε (by simpa [abs_of_pos hε_pos] using hε_radius)
  have hsets :
      { parameter : ℝ × ℝ |
          linearReward (twoCoordinateParameter parameter) (sixCandidateCopyFeatures ε δ)
              (5 : Candidate 4) ≤
            linearReward (twoCoordinateParameter parameter) (sixCandidateCopyFeatures ε δ)
              (4 : Candidate 4) } =
        { parameter | copyAboveOrTiedCone δ parameter } := by
    ext parameter
    simpa [twoCoordinateParameter] using
      (sixCandidateCopy_cPrimeAboveOrTied_iff hε_pos
        (twoCoordinateParameter parameter))
  rw [hsets]
  exact hcone

/--
The literal weighted-objective gap transports through the positive finite
voter-count scaling to the standard loss on all parameters whose two reward
coordinates are in the closed copy-bad cone.
-/
theorem globalStandardLossInfimum_lt_copyBadConeInfimum_of_sourceGap
    {majorityCount minorityCount : ℕ} (htotal_pos : 0 < majorityCount + minorityCount)
    {weight : ℝ}
    (hweight : weight = (majorityCount : ℝ) / (majorityCount + minorityCount : ℝ))
    (ε δ : ℝ) (loss : ℝ → ℝ)
    (hsource_gap :
      sInf (sixCandidateSourceObjective ε δ weight loss ''
        { parameter | copyAboveOrTiedCone δ parameter }) >
        sInf (Set.range (sixCandidateSourceObjective ε δ weight loss))) :
    globalStandardLossInfimum (sixCandidateCopyFeatures ε δ)
      (sixCandidateProfile majorityCount minorityCount) loss <
      sInf (standardLoss (sixCandidateCopyFeatures ε δ)
        (sixCandidateProfile majorityCount minorityCount) loss ''
          { parameter | copyAboveOrTiedCone δ (parameter 0, parameter 1) }) := by
  have hscale_pos : 0 < (majorityCount + minorityCount : ℝ) := by
    exact_mod_cast htotal_pos
  have hglobal_scale :=
    sInf_standardLoss_sixCandidateProfile_eq_scaledSourceObjective htotal_pos hweight
      ε δ loss (Set.univ : Set (ℝ × ℝ))
  simp only [Set.mem_univ, Set.setOf_true] at hglobal_scale
  have hbad_scale :=
    sInf_standardLoss_sixCandidateProfile_eq_scaledSourceObjective htotal_pos hweight
      ε δ loss { parameter | copyAboveOrTiedCone δ parameter }
  have hglobal_scale' :
      sInf (Set.range (standardLoss (sixCandidateCopyFeatures ε δ)
        (sixCandidateProfile majorityCount minorityCount) loss)) =
        (majorityCount + minorityCount : ℝ) *
          sInf (Set.range (sixCandidateSourceObjective ε δ weight loss)) := by
    simpa only [← Set.image_univ] using hglobal_scale
  have hbad_scale' :
      sInf (standardLoss (sixCandidateCopyFeatures ε δ)
        (sixCandidateProfile majorityCount minorityCount) loss ''
          { parameter | copyAboveOrTiedCone δ (parameter 0, parameter 1) }) =
        (majorityCount + minorityCount : ℝ) *
          sInf (sixCandidateSourceObjective ε δ weight loss ''
            { parameter | copyAboveOrTiedCone δ parameter }) := by
    simpa only [Set.mem_setOf_eq] using hbad_scale
  unfold globalStandardLossInfimum
  rw [hglobal_scale', hbad_scale']
  exact mul_lt_mul_of_pos_left hsource_gap hscale_pos

/--
For a feasible output ranking that puts `c′` above `c`, every inducing
parameter lies in the closed copy-bad cone.  The weighted source gap therefore
becomes the ranking-level standard-loss gap consumed by the PO and PMC
inference theorems.
-/
theorem standardLoss_pairwiseInfimumGap_sixCandidateProfile_of_sourceGap
    {majorityCount minorityCount : ℕ} (htotal_pos : 0 < majorityCount + minorityCount)
    {weight : ℝ}
    (hweight : weight = (majorityCount : ℝ) / (majorityCount + minorityCount : ℝ))
    {ε δ : ℝ} (hε_pos : 0 < ε) (loss : ℝ → ℝ)
    (hloss_nonnegative : ∀ input, 0 ≤ loss input)
    (output : Ranking 4)
    (houtput_feasible : LinearFeasibleRanking (sixCandidateCopyFeatures ε δ) output)
    (houtput_prefers : StrictlyPrefers output (4 : Candidate 4) 5)
    (hsource_gap :
      sInf (sixCandidateSourceObjective ε δ weight loss ''
        { parameter | copyAboveOrTiedCone δ parameter }) >
        sInf (Set.range (sixCandidateSourceObjective ε δ weight loss)) ) :
    globalStandardLossInfimum (sixCandidateCopyFeatures ε δ)
      (sixCandidateProfile majorityCount minorityCount) loss <
      restrictedStandardLossInfimum (sixCandidateCopyFeatures ε δ)
        (sixCandidateProfile majorityCount minorityCount) loss output := by
  have hcone_gap := globalStandardLossInfimum_lt_copyBadConeInfimum_of_sourceGap
    htotal_pos hweight ε δ loss hsource_gap
  have hcone_nonempty :
      (standardLoss (sixCandidateCopyFeatures ε δ)
        (sixCandidateProfile majorityCount minorityCount) loss ''
          { parameter | copyAboveOrTiedCone δ (parameter 0, parameter 1) }).Nonempty := by
    refine ⟨standardLoss (sixCandidateCopyFeatures ε δ)
      (sixCandidateProfile majorityCount minorityCount) loss (0 : LinearRewardParameter 2), ?_⟩
    refine ⟨0, ?_, rfl⟩
    unfold copyAboveOrTiedCone
    norm_num
  have hcone_bdd : BddBelow
      (standardLoss (sixCandidateCopyFeatures ε δ)
        (sixCandidateProfile majorityCount minorityCount) loss ''
          { parameter | copyAboveOrTiedCone δ (parameter 0, parameter 1) }) := by
    refine ⟨0, ?_⟩
    rintro value ⟨parameter, _hparameter, rfl⟩
    exact standardLoss_nonnegative _ _ _ _ hloss_nonnegative
  have hrestricted_nonempty :
      (standardLoss (sixCandidateCopyFeatures ε δ)
        (sixCandidateProfile majorityCount minorityCount) loss ''
          { parameter | InducesRanking (sixCandidateCopyFeatures ε δ) parameter output }).Nonempty := by
    obtain ⟨parameter, _hnondegenerate, hinduced⟩ := houtput_feasible
    exact ⟨standardLoss (sixCandidateCopyFeatures ε δ)
      (sixCandidateProfile majorityCount minorityCount) loss parameter,
      ⟨parameter, hinduced, rfl⟩⟩
  have hcone_le_restricted :
      sInf (standardLoss (sixCandidateCopyFeatures ε δ)
        (sixCandidateProfile majorityCount minorityCount) loss ''
          { parameter | copyAboveOrTiedCone δ (parameter 0, parameter 1) }) ≤
        restrictedStandardLossInfimum (sixCandidateCopyFeatures ε δ)
          (sixCandidateProfile majorityCount minorityCount) loss output := by
    unfold restrictedStandardLossInfimum
    apply le_csInf hrestricted_nonempty
    rintro value ⟨parameter, hinduced, rfl⟩
    apply csInf_le hcone_bdd
    refine ⟨parameter, ?_, rfl⟩
    apply (sixCandidateCopy_cPrimeAboveOrTied_iff hε_pos parameter).mp
    exact hinduced (4 : Candidate 4) 5 houtput_prefers
  exact hcone_gap.trans_le hcone_le_restricted

/--
Finite conditional endpoint for the negative-input six-candidate branch of
source Theorem 3.1.  Given the separated core-minimizer seam that Appendix A.1
is intended to construct, this produces a literal feasible finite profile on
which every standard-loss-minimizing linear rule violates both PO and PMC.
-/
theorem theorem3_1_negativeInputSixCandidate_from_coreSeam
    (weight : ℚ) {δ : ℝ} {loss : ℝ → ℝ} {base : ℝ × ℝ}
    (hweight_half : (1 / 2 : ℚ) < weight) (hweight_lt_one : weight < 1)
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hloss_nonnegative : ∀ input, 0 ≤ loss input)
    (hcontinuous : Continuous loss)
    (hrightTail : ∀ threshold : ℝ,
      ∃ tailBound > 0, ∀ input, tailBound < input → threshold < loss input)
    (hcore_global : IsGlobalMinimizer
      (coreLoss (weightedLoss (weight : ℝ) loss)) base)
    (hcore_below : ∀ parameter,
      IsGlobalMinimizer (coreLoss (weightedLoss (weight : ℝ) loss)) parameter →
        copyBelowOriginalCone δ parameter) :
    ∃ majorityCount minorityCount : ℕ, minorityCount < majorityCount ∧
      0 < majorityCount + minorityCount ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
        ∀ rule : LinearRankAggregationRule (Fin (majorityCount + minorityCount)) 4
          (LinearFeasibleRanking (sixCandidateCopyFeatures ε δ)),
          IsStandardLossMinimizing (sixCandidateCopyFeatures ε δ) loss rule →
            ¬ ParetoOptimal (LinearFeasibleRanking (sixCandidateCopyFeatures ε δ)) rule ∧
              ¬ PairwiseMajorityConsistent
                (LinearFeasibleRanking (sixCandidateCopyFeatures ε δ)) rule := by
  obtain ⟨majorityCount, minorityCount, hmajority, htotal_pos, hweight⟩ :=
    exists_finiteVoterCounts_of_rational_strictMajority hweight_half hweight_lt_one
  have hweight_half_real : 1 / 2 ≤ (weight : ℝ) := by
    have hdouble_rat : (1 : ℚ) < 2 * weight := by linarith
    have hdouble_real : (1 : ℝ) < 2 * (weight : ℝ) := by
      exact_mod_cast hdouble_rat
    linarith
  have hweight_lt_one_real : (weight : ℝ) < 1 := by
    exact_mod_cast hweight_lt_one
  obtain ⟨_bound, radius, _hbound_pos, hradius_pos, hsource_gap⟩ :=
    exists_radius_fullCopyBadConeGap_sixCandidateSourceObjective
      hweight_half_real hweight_lt_one_real hloss_nonnegative hcontinuous hrightTail
      hcore_global hcore_below
  let ε : ℝ := min (radius / 2) (1 / 2)
  have hε_pos : 0 < ε := by
    dsimp [ε]
    exact lt_min (half_pos hradius_pos) (by norm_num)
  have hε_lt_radius : ε < radius := by
    dsimp [ε]
    exact (min_le_left _ _).trans_lt (half_lt_self hradius_pos)
  have hε_lt_one : ε < 1 := by
    dsimp [ε]
    exact (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨majorityCount, minorityCount, hmajority, htotal_pos,
    ε, hε_pos, hε_lt_one, ?_⟩
  intro rule hminimizes
  have hprofile_feasible : FeasibleProfile
      (LinearFeasibleRanking (sixCandidateCopyFeatures ε δ))
      (sixCandidateProfile majorityCount minorityCount) :=
    feasibleProfile_sixCandidateProfile hε_pos hε_lt_one hδ_pos hδ_lt_one
      majorityCount minorityCount
  have hforward_feasible :
      LinearFeasibleRanking (sixCandidateCopyFeatures ε δ) sixCandidateForwardRanking :=
    linearFeasibleRanking_sixCandidateForward hε_pos hε_lt_one hδ_pos hδ_lt_one
  have hmajority_ranking :
      IsPairwiseMajorityRanking (sixCandidateProfile majorityCount minorityCount)
        sixCandidateForwardRanking :=
    isPairwiseMajorityRanking_sixCandidateProfile hmajority
  have huniversal : UniversallyPreferred
      (sixCandidateProfile majorityCount minorityCount) (4 : Candidate 4) 5 :=
    universallyPreferred_sixCandidateProfile_copy_pair majorityCount minorityCount
  have hsource_gap_at_ε := hsource_gap ε (by
    simpa [abs_of_pos hε_pos] using hε_lt_radius)
  constructor
  · intro hpareto
    have houtput_prefers : StrictlyPrefers
        (rule.run (sixCandidateProfile majorityCount minorityCount)) (4 : Candidate 4) 5 :=
      hpareto (sixCandidateProfile majorityCount minorityCount) 4 5 hprofile_feasible huniversal
    have hloss_gap := standardLoss_pairwiseInfimumGap_sixCandidateProfile_of_sourceGap
      htotal_pos hweight hε_pos loss hloss_nonnegative
      (rule.run (sixCandidateProfile majorityCount minorityCount))
      (rule.output_feasible (sixCandidateProfile majorityCount minorityCount))
      houtput_prefers hsource_gap_at_ε
    rw [← hminimizes (sixCandidateProfile majorityCount minorityCount) hprofile_feasible]
      at hloss_gap
    exact lt_irrefl _ hloss_gap
  · intro hpmc
    have houtput_eq : rule.run (sixCandidateProfile majorityCount minorityCount) =
        sixCandidateForwardRanking :=
      hpmc (sixCandidateProfile majorityCount minorityCount) sixCandidateForwardRanking
        hprofile_feasible hforward_feasible hmajority_ranking
    have houtput_prefers : StrictlyPrefers
        (rule.run (sixCandidateProfile majorityCount minorityCount)) (4 : Candidate 4) 5 := by
      rw [houtput_eq]
      norm_num [StrictlyPrefers, sixCandidateForwardRanking, rankOf]
      decide
    have hloss_gap := standardLoss_pairwiseInfimumGap_sixCandidateProfile_of_sourceGap
      htotal_pos hweight hε_pos loss hloss_nonnegative
      (rule.run (sixCandidateProfile majorityCount minorityCount))
      (rule.output_feasible (sixCandidateProfile majorityCount minorityCount))
      houtput_prefers hsource_gap_at_ε
    rw [← hminimizes (sixCandidateProfile majorityCount minorityCount) hprofile_feasible]
      at hloss_gap
    exact lt_irrefl _ hloss_gap

/--
The preceding conditional six-candidate endpoint under the paper's actual
negative-dip hypotheses.  Convexity supplies the required right-tail property;
the only remaining nontrivial seam is the one-sided-derivative construction
of the rational weight and separated core minimizers in Appendix A.1.
-/
theorem theorem3_1_negativeInputSixCandidate_from_convexCoreSeam
    (weight : ℚ) {δ : ℝ} {loss : ℝ → ℝ} {base : ℝ × ℝ}
    (hweight_half : (1 / 2 : ℚ) < weight) (hweight_lt_one : weight < 1)
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hloss_nonnegative : ∀ input, 0 ≤ loss input)
    (hcontinuous : Continuous loss) (hconvex : ConvexOn ℝ Set.univ loss)
    {negativeInput : ℝ} (hnegative : negativeInput < 0)
    (hdip : loss negativeInput < loss 0)
    (hcore_global : IsGlobalMinimizer
      (coreLoss (weightedLoss (weight : ℝ) loss)) base)
    (hcore_below : ∀ parameter,
      IsGlobalMinimizer (coreLoss (weightedLoss (weight : ℝ) loss)) parameter →
        copyBelowOriginalCone δ parameter) :
    ∃ majorityCount minorityCount : ℕ, minorityCount < majorityCount ∧
      0 < majorityCount + minorityCount ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
        ∀ rule : LinearRankAggregationRule (Fin (majorityCount + minorityCount)) 4
          (LinearFeasibleRanking (sixCandidateCopyFeatures ε δ)),
          IsStandardLossMinimizing (sixCandidateCopyFeatures ε δ) loss rule →
            ¬ ParetoOptimal (LinearFeasibleRanking (sixCandidateCopyFeatures ε δ)) rule ∧
              ¬ PairwiseMajorityConsistent
                (LinearFeasibleRanking (sixCandidateCopyFeatures ε δ)) rule := by
  apply theorem3_1_negativeInputSixCandidate_from_coreSeam
    weight hweight_half hweight_lt_one hδ_pos hδ_lt_one hloss_nonnegative
    hcontinuous
  · intro threshold
    exact exists_right_tail_gt_of_convex_negative_dip hconvex hnegative hdip threshold
  · exact hcore_global
  · exact hcore_below

/--
Fully finite negative-input endpoint of Theorem 3.1 from the corrected
four-derivative certificate.  This closes the paper's chain from that
certificate through Lemmas 3.2--3.5 to a literal finite standard-loss
counterexample.  It is retained as a differentiable specialization; the
source-faithful one-sided branch theorems below derive their own certificate.
-/
theorem theorem3_1_negativeInputSixCandidate_from_four_derivatives
    {loss : ℝ → ℝ} {negativeInput w z1 z2 z3 z4 : ℝ}
    (hloss_nonnegative : ∀ input, 0 ≤ loss input)
    (hcontinuous : Continuous loss) (hconvex : ConvexOn ℝ Set.univ loss)
    (hnegative : negativeInput < 0) (hdip : loss negativeInput < loss 0)
    (hw_pos : 0 < w)
    (hderiv1 : HasDerivAt loss z1 (-w))
    (hderiv2 : HasDerivAt loss z2 (-w / 2))
    (hderiv3 : HasDerivAt loss z3 (w / 2))
    (hderiv4 : HasDerivAt loss z4 w)
    (hz1_nonnegative : 0 ≤ z1) (hz12 : z1 < z2)
    (hz23 : z2 ≤ z3) (hz34 : z3 ≤ z4) :
    ∃ weight : ℚ, (1 / 2 : ℚ) < weight ∧ weight < 1 ∧
      ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
        ∃ majorityCount minorityCount : ℕ, minorityCount < majorityCount ∧
          0 < majorityCount + minorityCount ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
            ∀ rule : LinearRankAggregationRule (Fin (majorityCount + minorityCount)) 4
              (LinearFeasibleRanking (sixCandidateCopyFeatures ε δ)),
              IsStandardLossMinimizing (sixCandidateCopyFeatures ε δ) loss rule →
                ¬ ParetoOptimal (LinearFeasibleRanking (sixCandidateCopyFeatures ε δ)) rule ∧
                  ¬ PairwiseMajorityConsistent
                    (LinearFeasibleRanking (sixCandidateCopyFeatures ε δ)) rule := by
  obtain ⟨weight, hhalf_real, hweight_lt_one_real, A1, A2, hA12, _hA2_pos,
    rewards, hrewards_global, hrewards_separated⟩ :=
    lemma3_2_weightedLoss_separation_from_four_derivatives hloss_nonnegative
      hcontinuous hconvex hnegative hdip hw_pos hderiv1 hderiv2 hderiv3 hderiv4
      hz1_nonnegative hz12 hz23 hz34
  have hhalf : (1 / 2 : ℚ) < weight := by
    apply (Rat.cast_lt (K := ℝ)).mp
    simpa using hhalf_real
  have hweight_lt_one : weight < 1 := by
    exact_mod_cast hweight_lt_one_real
  obtain ⟨A3, A4, hA3_pos, base, hcore_global, hcore_bounds⟩ :=
    lemma3_3_core_minimizers hA12 ⟨rewards, hrewards_global⟩ hrewards_separated
  obtain ⟨δ, hδ_pos, hδ_lt_one, hδ_bounds⟩ := exists_copyCone_delta hA3_pos
  have hcore_below : ∀ parameter,
      IsGlobalMinimizer (coreLoss (weightedLoss (weight : ℝ) loss)) parameter →
        copyBelowOriginalCone δ parameter :=
    corrected_lemma3_4_core_minimizers_in_copyBelowOriginalCone hδ_pos hδ_bounds hcore_bounds
  refine ⟨weight, hhalf, hweight_lt_one, δ, hδ_pos, hδ_lt_one, ?_⟩
  exact theorem3_1_negativeInputSixCandidate_from_convexCoreSeam weight hhalf hweight_lt_one
    hδ_pos hδ_lt_one hloss_nonnegative hcontinuous hconvex hnegative hdip
    hcore_global hcore_below

/--
Fully finite negative-input endpoint from the source's actual four one-sided
derivatives.  This removes the artificial differentiability assumption from
the checked certificate-to-counterexample chain; only the source's selection
of a point with the stipulated strict derivative ordering remains to be
derived from its broad hypotheses.
-/
theorem theorem3_1_negativeInputSixCandidate_from_four_oneSidedDerivatives
    {loss : ℝ → ℝ} {negativeInput w z1 z2 z3 z4 : ℝ}
    (hloss_nonnegative : ∀ input, 0 ≤ loss input)
    (hcontinuous : Continuous loss) (hconvex : ConvexOn ℝ Set.univ loss)
    (hnegative : negativeInput < 0) (hdip : loss negativeInput < loss 0)
    (hw_pos : 0 < w)
    (hderiv1 : HasDerivWithinAt loss z1 (Set.Iio (-w)) (-w))
    (hderiv2 : HasDerivWithinAt loss z2 (Set.Iio (-(w / 2))) (-(w / 2)))
    (hderiv3 : HasDerivWithinAt loss z3 (Set.Ioi (w / 2)) (w / 2))
    (hderiv4 : HasDerivWithinAt loss z4 (Set.Ioi w) w)
    (hz1_nonnegative : 0 ≤ z1) (hz12 : z1 < z2)
    (hz23 : z2 ≤ z3) (hz34 : z3 ≤ z4) :
    ∃ weight : ℚ, (1 / 2 : ℚ) < weight ∧ weight < 1 ∧
      ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
        ∃ majorityCount minorityCount : ℕ, minorityCount < majorityCount ∧
          0 < majorityCount + minorityCount ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
            ∀ rule : LinearRankAggregationRule (Fin (majorityCount + minorityCount)) 4
              (LinearFeasibleRanking (sixCandidateCopyFeatures ε δ)),
              IsStandardLossMinimizing (sixCandidateCopyFeatures ε δ) loss rule →
                ¬ ParetoOptimal (LinearFeasibleRanking (sixCandidateCopyFeatures ε δ)) rule ∧
                  ¬ PairwiseMajorityConsistent
                    (LinearFeasibleRanking (sixCandidateCopyFeatures ε δ)) rule := by
  obtain ⟨weight, hhalf_real, hweight_lt_one_real, A1, A2, hA12, _hA2_pos,
    rewards, hrewards_global, hrewards_separated⟩ :=
    lemma3_2_weightedLoss_separation_from_four_oneSidedDerivatives hloss_nonnegative
      hcontinuous hconvex hnegative hdip hw_pos hderiv1 hderiv2 hderiv3 hderiv4
      hz1_nonnegative hz12 hz23 hz34
  have hhalf : (1 / 2 : ℚ) < weight := by
    apply (Rat.cast_lt (K := ℝ)).mp
    simpa using hhalf_real
  have hweight_lt_one : weight < 1 := by
    exact_mod_cast hweight_lt_one_real
  obtain ⟨A3, A4, hA3_pos, base, hcore_global, hcore_bounds⟩ :=
    lemma3_3_core_minimizers hA12 ⟨rewards, hrewards_global⟩ hrewards_separated
  obtain ⟨δ, hδ_pos, hδ_lt_one, hδ_bounds⟩ := exists_copyCone_delta hA3_pos
  have hcore_below : ∀ parameter,
      IsGlobalMinimizer (coreLoss (weightedLoss (weight : ℝ) loss)) parameter →
        copyBelowOriginalCone δ parameter :=
    corrected_lemma3_4_core_minimizers_in_copyBelowOriginalCone hδ_pos hδ_bounds hcore_bounds
  refine ⟨weight, hhalf, hweight_lt_one, δ, hδ_pos, hδ_lt_one, ?_⟩
  exact theorem3_1_negativeInputSixCandidate_from_convexCoreSeam weight hhalf hweight_lt_one
    hδ_pos hδ_lt_one hloss_nonnegative hcontinuous hconvex hnegative hdip
    hcore_global hcore_below

/--
The strictly-convex negative-input branch of source Theorem 3.1, with its
Appendix A.1 point-selection step derived rather than assumed.  The only
remaining source alternative is the merely nondecreasing convex branch.
-/
theorem theorem3_1_negativeInputSixCandidate_of_strictConvex
    {loss : ℝ → ℝ} {negativeInput : ℝ}
    (hloss_nonnegative : ∀ input, 0 ≤ loss input)
    (hcontinuous : Continuous loss) (hstrict : StrictConvexOn ℝ Set.univ loss)
    (hnegative : negativeInput < 0) (hdip : loss negativeInput < loss 0) :
    ∃ weight : ℚ, (1 / 2 : ℚ) < weight ∧ weight < 1 ∧
      ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
        ∃ majorityCount minorityCount : ℕ, minorityCount < majorityCount ∧
          0 < majorityCount + minorityCount ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
            ∀ rule : LinearRankAggregationRule (Fin (majorityCount + minorityCount)) 4
              (LinearFeasibleRanking (sixCandidateCopyFeatures ε δ)),
              IsStandardLossMinimizing (sixCandidateCopyFeatures ε δ) loss rule →
                ¬ ParetoOptimal (LinearFeasibleRanking (sixCandidateCopyFeatures ε δ)) rule ∧
                  ¬ PairwiseMajorityConsistent
                    (LinearFeasibleRanking (sixCandidateCopyFeatures ε δ)) rule := by
  obtain ⟨w, z1, z2, z3, z4, hw_pos, hderiv1, hderiv2, hderiv3, hderiv4,
    hz1_nonnegative, hz12, hz23, hz34⟩ :=
    exists_four_oneSided_derivative_data_of_strictConvex_negative_dip
      hcontinuous hstrict hnegative hdip
  exact theorem3_1_negativeInputSixCandidate_from_four_oneSidedDerivatives
    hloss_nonnegative hcontinuous hstrict.convexOn hnegative hdip hw_pos hderiv1 hderiv2
    hderiv3 hderiv4 hz1_nonnegative hz12 hz23 hz34

/--
The nondecreasing weakly-convex negative-input branch of source Theorem 3.1.
The checked dyadic argument supplies the one-sided derivative data that the
published proof obtained through a supremum construction.
-/
theorem theorem3_1_negativeInputSixCandidate_of_monotoneConvex
    {loss : ℝ → ℝ} {negativeInput : ℝ}
    (hloss_nonnegative : ∀ input, 0 ≤ loss input) (hmonotone : Monotone loss)
    (hcontinuous : Continuous loss) (hconvex : ConvexOn ℝ Set.univ loss)
    (hnegative : negativeInput < 0) (hdip : loss negativeInput < loss 0) :
    ∃ weight : ℚ, (1 / 2 : ℚ) < weight ∧ weight < 1 ∧
      ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
        ∃ majorityCount minorityCount : ℕ, minorityCount < majorityCount ∧
          0 < majorityCount + minorityCount ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
            ∀ rule : LinearRankAggregationRule (Fin (majorityCount + minorityCount)) 4
              (LinearFeasibleRanking (sixCandidateCopyFeatures ε δ)),
              IsStandardLossMinimizing (sixCandidateCopyFeatures ε δ) loss rule →
                ¬ ParetoOptimal (LinearFeasibleRanking (sixCandidateCopyFeatures ε δ)) rule ∧
                  ¬ PairwiseMajorityConsistent
                    (LinearFeasibleRanking (sixCandidateCopyFeatures ε δ)) rule := by
  obtain ⟨w, z1, z2, z3, z4, hw_pos, hderiv1, hderiv2, hderiv3, hderiv4,
    hz1_nonnegative, hz12, hz23, hz34⟩ :=
    exists_four_oneSided_derivative_data_of_monotone_convex_negative_dip
      hloss_nonnegative hmonotone hcontinuous hconvex hnegative hdip
  exact theorem3_1_negativeInputSixCandidate_from_four_oneSidedDerivatives
    hloss_nonnegative hcontinuous hconvex hnegative hdip hw_pos hderiv1 hderiv2 hderiv3
    hderiv4 hz1_nonnegative hz12 hz23 hz34

/-- Source-assumption form of the strictly-convex negative-input endpoint. -/
theorem theorem3_1_negativeInputSixCandidate_of_strictConvex_sourceAssumptions
    {loss : ℝ → ℝ} {negativeInput : ℝ}
    (hloss_nonnegative : ∀ input, 0 ≤ loss input) (hstrict : StrictConvexOn ℝ Set.univ loss)
    (hnegative : negativeInput < 0) (hdip : loss negativeInput < loss 0) :
    ∃ weight : ℚ, (1 / 2 : ℚ) < weight ∧ weight < 1 ∧
      ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
        ∃ majorityCount minorityCount : ℕ, minorityCount < majorityCount ∧
          0 < majorityCount + minorityCount ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
            ∀ rule : LinearRankAggregationRule (Fin (majorityCount + minorityCount)) 4
              (LinearFeasibleRanking (sixCandidateCopyFeatures ε δ)),
              IsStandardLossMinimizing (sixCandidateCopyFeatures ε δ) loss rule →
                ¬ ParetoOptimal (LinearFeasibleRanking (sixCandidateCopyFeatures ε δ)) rule ∧
                  ¬ PairwiseMajorityConsistent
                    (LinearFeasibleRanking (sixCandidateCopyFeatures ε δ)) rule := by
  exact theorem3_1_negativeInputSixCandidate_of_strictConvex hloss_nonnegative
    (continuous_of_convexOn_univ hstrict.convexOn) hstrict hnegative hdip

/-- Source-assumption form of the nondecreasing convex negative-input endpoint. -/
theorem theorem3_1_negativeInputSixCandidate_of_monotoneConvex_sourceAssumptions
    {loss : ℝ → ℝ} {negativeInput : ℝ}
    (hloss_nonnegative : ∀ input, 0 ≤ loss input) (hmonotone : Monotone loss)
    (hconvex : ConvexOn ℝ Set.univ loss)
    (hnegative : negativeInput < 0) (hdip : loss negativeInput < loss 0) :
    ∃ weight : ℚ, (1 / 2 : ℚ) < weight ∧ weight < 1 ∧
      ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
        ∃ majorityCount minorityCount : ℕ, minorityCount < majorityCount ∧
          0 < majorityCount + minorityCount ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
            ∀ rule : LinearRankAggregationRule (Fin (majorityCount + minorityCount)) 4
              (LinearFeasibleRanking (sixCandidateCopyFeatures ε δ)),
              IsStandardLossMinimizing (sixCandidateCopyFeatures ε δ) loss rule →
                ¬ ParetoOptimal (LinearFeasibleRanking (sixCandidateCopyFeatures ε δ)) rule ∧
                  ¬ PairwiseMajorityConsistent
                    (LinearFeasibleRanking (sixCandidateCopyFeatures ε δ)) rule := by
  exact theorem3_1_negativeInputSixCandidate_of_monotoneConvex hloss_nonnegative hmonotone
    (continuous_of_convexOn_univ hconvex) hconvex hnegative hdip

end GeEtAl2024AlignmentAxioms
