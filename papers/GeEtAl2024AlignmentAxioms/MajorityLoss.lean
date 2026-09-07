import AppliedModelingLib.Alignment.Axioms.LinearModel
import AppliedModelingLib.SocialChoice.Ranking.Kendall
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Fintype.Order
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith

/-!
# Majority-based loss formulation: Ge et al. (2024), §3.2

The source's majority-loss objective charges a loss only for an ordered pair
supported by a strict voter majority.  This module gives that finite objective
and proves the lower-bound half of Appendix A.5: any parameter inducing a
ranking that reverses one strict-majority comparison pays at least `ℓ(0)`.
-/

open scoped BigOperators

namespace GeEtAl2024AlignmentAxioms

open AppliedModelingLib.Alignment.Axioms
open AppliedModelingLib.SocialChoice.Ranking

/-- The finite majority-based loss objective in source §3.2. -/
noncomputable def majorityLoss
    {Voter : Type*} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (profile : RankingProfile Voter n) (loss : ℝ → ℝ)
    (parameter : LinearRewardParameter dimension) : ℝ := by
  classical
  exact ∑ pair : Candidate n × Candidate n,
    if StrictMajorityPrefers profile pair.1 pair.2 then
      loss (linearReward parameter features pair.2 - linearReward parameter features pair.1)
    else 0

/-- Parameters weakly inducing one specified output ranking. -/
def inducingParameters
    {n dimension : ℕ} (features : Candidate n → FeatureVector dimension)
    (ranking : Ranking n) : Set (LinearRewardParameter dimension) :=
  { parameter | InducesRanking features parameter ranking }

/-- The infimum of majority loss over parameters inducing one ranking. -/
noncomputable def restrictedMajorityLossInfimum
    {Voter : Type*} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (profile : RankingProfile Voter n) (loss : ℝ → ℝ) (ranking : Ranking n) : ℝ :=
  sInf (majorityLoss features profile loss '' inducingParameters features ranking)

/-- The unrestricted majority-loss infimum from source §3.2. -/
noncomputable def globalMajorityLossInfimum
    {Voter : Type*} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (profile : RankingProfile Voter n) (loss : ℝ → ℝ) : ℝ :=
  sInf (Set.range (majorityLoss features profile loss))

/-- Source's ranking-level majority-loss minimization condition. -/
def IsMajorityLossMinimizing
    {Voter : Type*} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension) (loss : ℝ → ℝ)
    (rule : LinearRankAggregationRule Voter n (LinearFeasibleRanking features)) : Prop :=
  ∀ profile, FeasibleProfile (LinearFeasibleRanking features) profile →
    restrictedMajorityLossInfimum features profile loss (rule.run profile) =
      globalMajorityLossInfimum features profile loss

/-- The source scaling argument's approximation conclusion for one profile. -/
def HasArbitrarilySmallMajorityLoss
    {Voter : Type*} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (profile : RankingProfile Voter n) (loss : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ parameter : LinearRewardParameter dimension,
    majorityLoss features profile loss parameter < ε

/-- The source's loss translation that normalizes its infimum to zero. -/
noncomputable def normalizedLoss (loss : ℝ → ℝ) : ℝ → ℝ :=
  fun input => loss input - sInf (Set.range loss)

/-- The number of strict-majority ordered pairs, represented as a real scalar. -/
noncomputable def strictMajorityPairMass
    {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) : ℝ := by
  classical
  exact ∑ pair : Candidate n × Candidate n,
    if StrictMajorityPrefers profile pair.1 pair.2 then 1 else 0

/--
Subtracting a fixed constant from every member of a nonempty bounded-below
set subtracts that constant from its infimum.
-/
theorem csInf_image_sub_const
    (values : Set ℝ) (constant : ℝ) (hbelow : BddBelow values)
    (hnonempty : values.Nonempty) :
    sInf ((fun value : ℝ => value - constant) '' values) =
      sInf values - constant := by
  have hshifted_below : BddBelow ((fun value : ℝ => value - constant) '' values) := by
    rcases hbelow with ⟨lower, hlower⟩
    refine ⟨lower - constant, ?_⟩
    rintro value ⟨original, horiginal, rfl⟩
    exact sub_le_sub_right (hlower horiginal) constant
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨value, hvalue, hvalue_lt⟩ :=
      (csInf_lt_iff hbelow hnonempty).mp (lt_add_of_pos_right _ hε)
    calc
      sInf ((fun value : ℝ => value - constant) '' values) ≤ value - constant :=
        csInf_le hshifted_below ⟨value, hvalue, rfl⟩
      _ ≤ (sInf values - constant) + ε := by linarith
  · apply le_csInf
    · exact hnonempty.image _
    · rintro value ⟨original, horiginal, rfl⟩
      exact sub_le_sub_right (csInf_le hbelow horiginal) constant

/-- A nonnegative loss makes its value range bounded below. -/
theorem bddBelow_range_of_loss_nonnegative
    (loss : ℝ → ℝ) (hloss_nonnegative : ∀ input, 0 ≤ loss input) :
    BddBelow (Set.range loss) := by
  refine ⟨0, ?_⟩
  rintro value ⟨input, rfl⟩
  exact hloss_nonnegative input

/-- Translation by the loss infimum preserves nonnegativity. -/
theorem normalizedLoss_nonnegative
    (loss : ℝ → ℝ) (hloss_nonnegative : ∀ input, 0 ≤ loss input) :
    ∀ input, 0 ≤ normalizedLoss loss input := by
  intro input
  unfold normalizedLoss
  exact sub_nonneg.mpr (csInf_le
    (bddBelow_range_of_loss_nonnegative loss hloss_nonnegative) ⟨input, rfl⟩)

/-- Translation by a constant preserves loss monotonicity. -/
theorem normalizedLoss_monotone
    (loss : ℝ → ℝ) (hloss_monotone : Monotone loss) :
    Monotone (normalizedLoss loss) := by
  intro first second hfirst_second
  unfold normalizedLoss
  exact sub_le_sub_right (hloss_monotone hfirst_second) _

/-- The translated loss has infimum exactly zero. -/
theorem sInf_range_normalizedLoss_eq_zero
    (loss : ℝ → ℝ) (hloss_nonnegative : ∀ input, 0 ≤ loss input) :
    sInf (Set.range (normalizedLoss loss)) = 0 := by
  have hrange : Set.range (normalizedLoss loss) =
      (fun value : ℝ => value - sInf (Set.range loss)) '' Set.range loss := by
    ext value
    constructor
    · rintro ⟨input, rfl⟩
      exact ⟨loss input, ⟨input, rfl⟩, rfl⟩
    · rintro ⟨value, ⟨input, rfl⟩, rfl⟩
      exact ⟨input, rfl⟩
  rw [hrange, csInf_image_sub_const]
  · ring
  · exact bddBelow_range_of_loss_nonnegative loss hloss_nonnegative
  · exact Set.range_nonempty loss

/-- Every term, hence the full majority loss, is nonnegative for a nonnegative loss. -/
theorem majorityLoss_nonnegative
    {Voter : Type*} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (profile : RankingProfile Voter n) (loss : ℝ → ℝ)
    (parameter : LinearRewardParameter dimension)
    (hloss_nonnegative : ∀ x, 0 ≤ loss x) :
    0 ≤ majorityLoss features profile loss parameter := by
  classical
  unfold majorityLoss
  apply Finset.sum_nonneg
  intro pair _
  split
  · exact hloss_nonnegative _
  · exact le_rfl

/--
For finitely many strictly negative gaps, one nonnegative scale makes every
active scaled gap lie below any prescribed real target.  This is the finite
uniformization implicit in the ray argument of Appendix A.5.
-/
theorem exists_nonnegative_scale_forall_active_gap_le
    {Index : Type*} [Fintype Index]
    (active : Index → Prop) (gap : Index → ℝ)
    (hgap : ∀ index, active index → gap index < 0) (target : ℝ) :
    ∃ scale : ℝ, 0 ≤ scale ∧
      ∀ index, active index → scale * gap index ≤ target := by
  classical
  let threshold : Index → ℝ := fun index =>
    if active index then (-target) / (-gap index) else 0
  obtain ⟨bound, hbound⟩ := Finite.bddAbove_range threshold
  refine ⟨max bound 0, le_max_right _ _, ?_⟩
  intro index hactive
  have hthreshold : (-target) / (-gap index) ≤ bound := by
    have hmem : threshold index ∈ Set.range threshold := ⟨index, rfl⟩
    simpa [threshold, hactive] using hbound hmem
  have hscale : (-target) / (-gap index) ≤ max bound 0 :=
    hthreshold.trans (le_max_left _ _)
  have hdenominator : 0 < -gap index := neg_pos.mpr (hgap index hactive)
  have hscaled : -target ≤ max bound 0 * (-gap index) :=
    (div_le_iff₀ hdenominator).mp hscale
  calc
    max bound 0 * gap index = -(max bound 0 * (-gap index)) := by ring
    _ ≤ target := by linarith

/--
If a nonnegative loss has infimum zero, it takes a value below every positive
threshold.  This makes the source's limiting statement usable without an
unformalized convergence claim.
-/
theorem exists_loss_lt_of_nonnegative_infimum_zero
    (loss : ℝ → ℝ) (hloss_nonnegative : ∀ x, 0 ≤ loss x)
    (hinfimum : sInf (Set.range loss) = 0) {threshold : ℝ}
    (hthreshold : 0 < threshold) :
    ∃ input, loss input < threshold := by
  have hbelow : BddBelow (Set.range loss) := by
    refine ⟨0, ?_⟩
    intro value hvalue
    rcases hvalue with ⟨input, rfl⟩
    exact hloss_nonnegative input
  have hnonempty : (Set.range loss).Nonempty := Set.range_nonempty loss
  obtain ⟨value, hvalue, hlt⟩ :=
    (csInf_lt_iff hbelow hnonempty).mp (by simpa [hinfimum] using hthreshold)
  rcases hvalue with ⟨input, rfl⟩
  exact ⟨input, hlt⟩

/--
The finite scaling step in Appendix A.5.  Under the source's normalized
assumption `inf ℓ = 0`, a feasible pairwise-majority ranking yields parameters
with arbitrarily small majority loss.
-/
theorem hasArbitrarilySmallMajorityLoss_of_feasible_pairwiseMajorityRanking
    {Voter : Type*} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (profile : RankingProfile Voter n) (loss : ℝ → ℝ)
    (majorityRanking : Ranking n)
    (hloss_nonnegative : ∀ x, 0 ≤ loss x) (hloss_monotone : Monotone loss)
    (hloss_infimum : sInf (Set.range loss) = 0)
    (hmajorityFeasible : LinearFeasibleRanking features majorityRanking)
    (hmajorityRanking : IsPairwiseMajorityRanking profile majorityRanking) :
    HasArbitrarilySmallMajorityLoss features profile loss := by
  classical
  intro ε hε
  let pairCount : ℝ :=
    ((Finset.univ : Finset (Candidate n × Candidate n)).card : ℝ)
  let threshold : ℝ := ε / (pairCount + 1)
  have hpairCount_nonnegative : 0 ≤ pairCount := by
    exact Nat.cast_nonneg _
  have hdenominator : 0 < pairCount + 1 := by linarith
  have hthreshold_positive : 0 < threshold :=
    div_pos hε hdenominator
  obtain ⟨input, hinput⟩ :=
    exists_loss_lt_of_nonnegative_infimum_zero loss hloss_nonnegative
      hloss_infimum hthreshold_positive
  rcases hmajorityFeasible with ⟨parameter, hnondegenerate, hinduced⟩
  let gap : Candidate n × Candidate n → ℝ := fun pair =>
    linearReward parameter features pair.2 - linearReward parameter features pair.1
  have hgap_negative : ∀ pair, StrictMajorityPrefers profile pair.1 pair.2 → gap pair < 0 := by
    intro pair hmajority
    dsimp [gap]
    exact sub_neg.mpr (inducesRanking_strictReward_of_nondegenerate
      features parameter majorityRanking hinduced hnondegenerate
      ((hmajorityRanking pair.1 pair.2).mpr hmajority))
  obtain ⟨scale, hscale_nonnegative, hscaled_gaps⟩ :=
    exists_nonnegative_scale_forall_active_gap_le
      (fun pair : Candidate n × Candidate n => StrictMajorityPrefers profile pair.1 pair.2)
      gap hgap_negative input
  refine ⟨scale • parameter, ?_⟩
  have hterm_bound : ∀ pair : Candidate n × Candidate n,
      (if StrictMajorityPrefers profile pair.1 pair.2 then
        loss (linearReward (scale • parameter) features pair.2 -
          linearReward (scale • parameter) features pair.1)
      else 0) ≤ threshold := by
    intro pair
    by_cases hmajority : StrictMajorityPrefers profile pair.1 pair.2
    · rw [if_pos hmajority]
      have hscaled_gap :
          linearReward (scale • parameter) features pair.2 -
              linearReward (scale • parameter) features pair.1 = scale * gap pair := by
        dsimp [gap]
        rw [linearReward_smul, linearReward_smul]
        ring
      rw [hscaled_gap]
      exact (hloss_monotone (hscaled_gaps pair hmajority)).trans hinput.le
    · rw [if_neg hmajority]
      exact hthreshold_positive.le
  change (∑ pair : Candidate n × Candidate n,
      if StrictMajorityPrefers profile pair.1 pair.2 then
        loss (linearReward (scale • parameter) features pair.2 -
          linearReward (scale • parameter) features pair.1)
      else 0) < ε
  calc
    (∑ pair : Candidate n × Candidate n,
        if StrictMajorityPrefers profile pair.1 pair.2 then
          loss (linearReward (scale • parameter) features pair.2 -
            linearReward (scale • parameter) features pair.1)
        else 0)
      ≤ ∑ _pair : Candidate n × Candidate n, threshold :=
        Finset.sum_le_sum (fun pair _ => hterm_bound pair)
    _ = pairCount * threshold := by
      simp [pairCount, nsmul_eq_mul]
    _ < ε := by
      dsimp [threshold]
      calc
        pairCount * (ε / (pairCount + 1)) =
            (pairCount * ε) / (pairCount + 1) := by ring
        _ < ε := (div_lt_iff₀ hdenominator).mpr (by nlinarith)

/--
For a nonnegative loss, arbitrarily small majority-loss values make the
unrestricted infimum exactly zero.
-/
theorem globalMajorityLossInfimum_eq_zero_of_nonnegative_and_arbitrarilySmall
    {Voter : Type*} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (profile : RankingProfile Voter n) (loss : ℝ → ℝ)
    (hloss_nonnegative : ∀ x, 0 ≤ loss x)
    (hsmall : HasArbitrarilySmallMajorityLoss features profile loss) :
    globalMajorityLossInfimum features profile loss = 0 := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨parameter, hparameter⟩ := hsmall ε hε
    have hbelow : BddBelow (Set.range (majorityLoss features profile loss)) := by
      refine ⟨0, ?_⟩
      intro value hvalue
      rcases hvalue with ⟨parameter, rfl⟩
      exact majorityLoss_nonnegative features profile loss parameter hloss_nonnegative
    change sInf (Set.range (majorityLoss features profile loss)) ≤ 0 + ε
    exact (csInf_le hbelow ⟨parameter, rfl⟩).trans (by simpa using hparameter.le)
  · unfold globalMajorityLossInfimum
    apply le_csInf
    · exact ⟨majorityLoss features profile loss 0, ⟨0, rfl⟩⟩
    · intro value hvalue
      rcases hvalue with ⟨parameter, rfl⟩
      exact majorityLoss_nonnegative features profile loss parameter hloss_nonnegative

/--
Appendix A.5's one-disagreement lower bound.  Reversing a strict-majority
pair forces a nonnegative reward gap in the loss direction; monotonicity then
makes that active majority-loss term at least `loss 0`.
-/
theorem loss_zero_le_majorityLoss_of_reversed_majority_pair
    {Voter : Type*} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (profile : RankingProfile Voter n) (loss : ℝ → ℝ)
    (parameter : LinearRewardParameter dimension) (output : Ranking n)
    (hloss_nonnegative : ∀ x, 0 ≤ loss x) (hloss_monotone : Monotone loss)
    {first second : Candidate n}
    (hmajority : StrictMajorityPrefers profile first second)
    (houtput_reverse : StrictlyPrefers output second first)
    (hinduced : InducesRanking features parameter output) :
    loss 0 ≤ majorityLoss features profile loss parameter := by
  classical
  have hgap_nonnegative :
      0 ≤ linearReward parameter features second - linearReward parameter features first := by
    exact sub_nonneg.mpr (hinduced second first houtput_reverse)
  have hterm : loss 0 ≤
      if StrictMajorityPrefers profile first second then
        loss (linearReward parameter features second - linearReward parameter features first)
      else 0 := by
    simp only [hmajority, ↓reduceIte]
    exact hloss_monotone hgap_nonnegative
  calc
    loss 0 ≤ if StrictMajorityPrefers profile first second then
        loss (linearReward parameter features second - linearReward parameter features first)
      else 0 := hterm
    _ ≤ ∑ pair : Candidate n × Candidate n,
        if StrictMajorityPrefers profile pair.1 pair.2 then
          loss (linearReward parameter features pair.2 - linearReward parameter features pair.1)
        else 0 := by
      apply Finset.single_le_sum
        (s := Finset.univ)
        (f := fun pair : Candidate n × Candidate n =>
          if StrictMajorityPrefers profile pair.1 pair.2 then
            loss (linearReward parameter features pair.2 - linearReward parameter features pair.1)
          else 0)
        (a := (first, second))
      · intro pair _
        dsimp
        split
        · exact hloss_nonnegative _
        · exact le_rfl
      · exact Finset.mem_univ _
    _ = majorityLoss features profile loss parameter := rfl

/--
If a ranking differs from a pairwise-majority ranking, it reverses at least
one strict-majority pair and therefore has the same `loss 0` lower bound.
-/
theorem loss_zero_le_majorityLoss_of_ne_pairwiseMajorityRanking
    {Voter : Type*} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (profile : RankingProfile Voter n) (loss : ℝ → ℝ)
    (parameter : LinearRewardParameter dimension)
    (majorityRanking output : Ranking n)
    (hloss_nonnegative : ∀ x, 0 ≤ loss x) (hloss_monotone : Monotone loss)
    (hmajorityRanking : IsPairwiseMajorityRanking profile majorityRanking)
    (houtput_ne : output ≠ majorityRanking)
    (hinduced : InducesRanking features parameter output) :
    loss 0 ≤ majorityLoss features profile loss parameter := by
  obtain ⟨pair, hpairs⟩ := exists_invertedPair_of_ne houtput_ne
  exact loss_zero_le_majorityLoss_of_reversed_majority_pair
    features profile loss parameter output hloss_nonnegative hloss_monotone
    ((hmajorityRanking pair.1 pair.2).mp hpairs.1) hpairs.2 hinduced

/--
The previous pointwise bound lifts to the infimum over all parameters inducing
a non-majority output.  Output feasibility supplies the required nonempty
inducing-parameter set.
-/
theorem loss_zero_le_restrictedMajorityLossInfimum_of_ne_pairwiseMajorityRanking
    {Voter : Type*} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (profile : RankingProfile Voter n) (loss : ℝ → ℝ)
    (rule : LinearRankAggregationRule Voter n (LinearFeasibleRanking features))
    (majorityRanking : Ranking n)
    (hloss_nonnegative : ∀ x, 0 ≤ loss x) (hloss_monotone : Monotone loss)
    (hmajorityRanking : IsPairwiseMajorityRanking profile majorityRanking)
    (houtput_ne : rule.run profile ≠ majorityRanking) :
    loss 0 ≤ restrictedMajorityLossInfimum features profile loss (rule.run profile) := by
  unfold restrictedMajorityLossInfimum
  apply le_csInf
  · rcases rule.output_feasible profile with ⟨parameter, _hnondegenerate, hinduced⟩
    exact ⟨majorityLoss features profile loss parameter, ⟨parameter, hinduced, rfl⟩⟩
  · intro value hvalue
    rcases hvalue with ⟨parameter, hinduced, rfl⟩
    exact loss_zero_le_majorityLoss_of_ne_pairwiseMajorityRanking
      features profile loss parameter majorityRanking (rule.run profile)
      hloss_nonnegative hloss_monotone hmajorityRanking houtput_ne hinduced

/--
The main comparison step in source Theorem 3.6, conditional on its preceding
scaling argument establishing a global majority-loss infimum of zero.
-/
theorem rule_returns_pairwiseMajorityRanking_of_zero_globalMajorityLossInfimum
    {Voter : Type*} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (profile : RankingProfile Voter n) (loss : ℝ → ℝ)
    (rule : LinearRankAggregationRule Voter n (LinearFeasibleRanking features))
    (majorityRanking : Ranking n)
    (hloss_nonnegative : ∀ x, 0 ≤ loss x) (hloss_monotone : Monotone loss)
    (hloss_zero_pos : 0 < loss 0)
    (hminimizes : IsMajorityLossMinimizing features loss rule)
    (hprofile_feasible : FeasibleProfile (LinearFeasibleRanking features) profile)
    (hmajorityRanking : IsPairwiseMajorityRanking profile majorityRanking)
    (hglobal_zero : globalMajorityLossInfimum features profile loss = 0) :
    rule.run profile = majorityRanking := by
  by_contra houtput_ne
  have hlower := loss_zero_le_restrictedMajorityLossInfimum_of_ne_pairwiseMajorityRanking
    features profile loss rule majorityRanking hloss_nonnegative hloss_monotone
    hmajorityRanking houtput_ne
  rw [hminimizes profile hprofile_feasible, hglobal_zero] at hlower
  exact (not_lt_of_ge hlower) hloss_zero_pos

/--
Profile-wise zero-infimum condition supplied by the scaling part of source
Appendix A.5.
-/
def HasZeroGlobalMajorityLossInfimumOnPairwiseMajorityProfiles
    {Voter : Type*} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension) (loss : ℝ → ℝ) : Prop :=
  ∀ (profile : RankingProfile Voter n) (majorityRanking : Ranking n),
    FeasibleProfile (LinearFeasibleRanking features) profile →
    LinearFeasibleRanking features majorityRanking →
    IsPairwiseMajorityRanking profile majorityRanking →
    globalMajorityLossInfimum features profile loss = 0

/--
Theorem 3.6 after discharging its source scaling subargument: a
majority-loss-minimizing rule returns every feasible pairwise-majority ranking.
-/
theorem theorem3_6_of_zero_globalMajorityLossInfimum
    {Voter : Type*} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension) (loss : ℝ → ℝ)
    (rule : LinearRankAggregationRule Voter n (LinearFeasibleRanking features))
    (hloss_nonnegative : ∀ x, 0 ≤ loss x) (hloss_monotone : Monotone loss)
    (hloss_zero_pos : 0 < loss 0)
    (hminimizes : IsMajorityLossMinimizing features loss rule)
    (hzero : HasZeroGlobalMajorityLossInfimumOnPairwiseMajorityProfiles
      (Voter := Voter) features loss) :
    PairwiseMajorityConsistent (LinearFeasibleRanking features) rule := by
  intro profile majorityRanking hprofile hmajorityFeasible hmajorityRanking
  exact rule_returns_pairwiseMajorityRanking_of_zero_globalMajorityLossInfimum
    features profile loss rule majorityRanking hloss_nonnegative hloss_monotone hloss_zero_pos
    hminimizes hprofile hmajorityRanking
      (hzero profile majorityRanking hprofile hmajorityFeasible hmajorityRanking)

/--
Theorem 3.6 with the source scaling step stated as an arbitrarily-small-loss
property rather than directly as an infimum equality.
-/
theorem theorem3_6_of_arbitrarilySmallMajorityLoss
    {Voter : Type*} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension) (loss : ℝ → ℝ)
    (rule : LinearRankAggregationRule Voter n (LinearFeasibleRanking features))
    (hloss_nonnegative : ∀ x, 0 ≤ loss x) (hloss_monotone : Monotone loss)
    (hloss_zero_pos : 0 < loss 0)
    (hminimizes : IsMajorityLossMinimizing features loss rule)
    (hsmall : ∀ (profile : RankingProfile Voter n) (majorityRanking : Ranking n),
      FeasibleProfile (LinearFeasibleRanking features) profile →
      LinearFeasibleRanking features majorityRanking →
      IsPairwiseMajorityRanking profile majorityRanking →
      HasArbitrarilySmallMajorityLoss features profile loss) :
    PairwiseMajorityConsistent (LinearFeasibleRanking features) rule := by
  apply theorem3_6_of_zero_globalMajorityLossInfimum
    features loss rule hloss_nonnegative hloss_monotone hloss_zero_pos hminimizes
  intro profile majorityRanking hprofile hmajorityFeasible hmajorityRanking
  exact globalMajorityLossInfimum_eq_zero_of_nonnegative_and_arbitrarilySmall
    features profile loss hloss_nonnegative
    (hsmall profile majorityRanking hprofile hmajorityFeasible hmajorityRanking)

/--
Normalizing a loss subtracts the same profile-dependent constant from every
parameter's majority loss.  This is the exact finite version of the source's
"without loss of generality" translation in Appendix A.5.
-/
theorem majorityLoss_normalizedLoss
    {Voter : Type*} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (profile : RankingProfile Voter n) (loss : ℝ → ℝ)
    (parameter : LinearRewardParameter dimension) :
    majorityLoss features profile (normalizedLoss loss) parameter =
      majorityLoss features profile loss parameter -
        strictMajorityPairMass profile * sInf (Set.range loss) := by
  classical
  unfold majorityLoss normalizedLoss strictMajorityPairMass
  calc
    (∑ pair : Candidate n × Candidate n,
        if StrictMajorityPrefers profile pair.1 pair.2 then
          loss (linearReward parameter features pair.2 - linearReward parameter features pair.1) -
            sInf (Set.range loss)
        else 0) =
        ∑ pair : Candidate n × Candidate n,
          ((if StrictMajorityPrefers profile pair.1 pair.2 then
            loss (linearReward parameter features pair.2 - linearReward parameter features pair.1)
          else 0) -
          (if StrictMajorityPrefers profile pair.1 pair.2 then sInf (Set.range loss) else 0)) := by
          apply Finset.sum_congr rfl
          intro pair _
          by_cases hmajority : StrictMajorityPrefers profile pair.1 pair.2 <;> simp [hmajority]
    _ = (∑ pair : Candidate n × Candidate n,
          if StrictMajorityPrefers profile pair.1 pair.2 then
            loss (linearReward parameter features pair.2 - linearReward parameter features pair.1)
          else 0) -
        ∑ pair : Candidate n × Candidate n,
          if StrictMajorityPrefers profile pair.1 pair.2 then sInf (Set.range loss) else 0 :=
          by rw [Finset.sum_sub_distrib]
    _ = (∑ pair : Candidate n × Candidate n,
          if StrictMajorityPrefers profile pair.1 pair.2 then
            loss (linearReward parameter features pair.2 - linearReward parameter features pair.1)
          else 0) -
        (∑ pair : Candidate n × Candidate n,
          if StrictMajorityPrefers profile pair.1 pair.2 then 1 else 0) * sInf (Set.range loss) := by
          congr 1
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro pair _
          by_cases hmajority : StrictMajorityPrefers profile pair.1 pair.2 <;> simp [hmajority]

/--
The source's ranking-level minimization condition is invariant under
translation of the loss by its infimum.
-/
theorem isMajorityLossMinimizing_normalizedLoss_of_original
    {Voter : Type*} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension) (loss : ℝ → ℝ)
    (rule : LinearRankAggregationRule Voter n (LinearFeasibleRanking features))
    (hloss_nonnegative : ∀ input, 0 ≤ loss input)
    (hminimizes : IsMajorityLossMinimizing features loss rule) :
    IsMajorityLossMinimizing features (normalizedLoss loss) rule := by
  classical
  unfold IsMajorityLossMinimizing at hminimizes ⊢
  intro profile hprofile
  unfold restrictedMajorityLossInfimum globalMajorityLossInfimum at hminimizes ⊢
  let constant : ℝ := strictMajorityPairMass profile * sInf (Set.range loss)
  have hpointwise (parameter : LinearRewardParameter dimension) :
      majorityLoss features profile (normalizedLoss loss) parameter =
        majorityLoss features profile loss parameter - constant := by
    simpa [constant] using majorityLoss_normalizedLoss features profile loss parameter
  have hrestricted :
      majorityLoss features profile (normalizedLoss loss) ''
          inducingParameters features (rule.run profile) =
        (fun value : ℝ => value - constant) ''
          (majorityLoss features profile loss ''
            inducingParameters features (rule.run profile)) := by
    ext value
    constructor
    · rintro ⟨parameter, hparameter, rfl⟩
      exact ⟨majorityLoss features profile loss parameter,
        ⟨parameter, hparameter, rfl⟩, (hpointwise parameter).symm⟩
    · rintro ⟨value, ⟨parameter, hparameter, rfl⟩, rfl⟩
      exact ⟨parameter, hparameter, hpointwise parameter⟩
  have hglobal : Set.range (majorityLoss features profile (normalizedLoss loss)) =
      (fun value : ℝ => value - constant) ''
        Set.range (majorityLoss features profile loss) := by
    ext value
    constructor
    · rintro ⟨parameter, rfl⟩
      exact ⟨majorityLoss features profile loss parameter, ⟨parameter, rfl⟩,
        (hpointwise parameter).symm⟩
    · rintro ⟨value, ⟨parameter, rfl⟩, rfl⟩
      exact ⟨parameter, hpointwise parameter⟩
  have hrestricted_nonempty :
      (majorityLoss features profile loss ''
        inducingParameters features (rule.run profile)).Nonempty := by
    rcases rule.output_feasible profile with ⟨parameter, _hnondegenerate, hinduced⟩
    exact ⟨majorityLoss features profile loss parameter, ⟨parameter, hinduced, rfl⟩⟩
  have hrestricted_below : BddBelow
      (majorityLoss features profile loss ''
        inducingParameters features (rule.run profile)) := by
    refine ⟨0, ?_⟩
    rintro value ⟨parameter, _hparameter, rfl⟩
    exact majorityLoss_nonnegative features profile loss parameter hloss_nonnegative
  have hglobal_nonempty : (Set.range (majorityLoss features profile loss)).Nonempty :=
    Set.range_nonempty _
  have hglobal_below : BddBelow (Set.range (majorityLoss features profile loss)) := by
    refine ⟨0, ?_⟩
    rintro value ⟨parameter, rfl⟩
    exact majorityLoss_nonnegative features profile loss parameter hloss_nonnegative
  rw [hrestricted, hglobal,
    csInf_image_sub_const _ constant hrestricted_below hrestricted_nonempty,
    csInf_image_sub_const _ constant hglobal_below hglobal_nonempty,
    hminimizes profile hprofile]

/--
Source Theorem 3.6: every linear rank aggregation rule that minimizes a
nonnegative nondecreasing majority loss with `ℓ(0) > inf ℓ` is pairwise
majority consistent.  The proof formalizes both the infimum-normalization and
the finite scaling argument from Appendix A.5.
-/
theorem theorem3_6_majorityLoss_core
    {Voter : Type*} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension) (loss : ℝ → ℝ)
    (rule : LinearRankAggregationRule Voter n (LinearFeasibleRanking features))
    (hloss_nonnegative : ∀ input, 0 ≤ loss input)
    (hloss_monotone : Monotone loss)
    (hloss_zero_gt_infimum : loss 0 > sInf (Set.range loss))
    (hminimizes : IsMajorityLossMinimizing features loss rule) :
    PairwiseMajorityConsistent (LinearFeasibleRanking features) rule := by
  have hnormalized_nonnegative := normalizedLoss_nonnegative loss hloss_nonnegative
  have hnormalized_monotone := normalizedLoss_monotone loss hloss_monotone
  have hnormalized_infimum := sInf_range_normalizedLoss_eq_zero loss hloss_nonnegative
  have hnormalized_zero_positive : 0 < normalizedLoss loss 0 := by
    unfold normalizedLoss
    exact sub_pos.mpr hloss_zero_gt_infimum
  apply theorem3_6_of_arbitrarilySmallMajorityLoss
    features (normalizedLoss loss) rule hnormalized_nonnegative hnormalized_monotone
      hnormalized_zero_positive
    (isMajorityLossMinimizing_normalizedLoss_of_original features loss rule
      hloss_nonnegative hminimizes)
  intro profile majorityRanking _hprofile hmajorityFeasible hmajorityRanking
  exact hasArbitrarilySmallMajorityLoss_of_feasible_pairwiseMajorityRanking
    features profile (normalizedLoss loss) majorityRanking hnormalized_nonnegative
      hnormalized_monotone hnormalized_infimum hmajorityFeasible hmajorityRanking

/--
At the normalized optimum value zero, an inducing parameter can only produce
the pairwise-majority ranking.  This is the finite uniqueness step in the
proof of source Theorem 3.6.
-/
theorem eq_pairwiseMajorityRanking_of_majorityLoss_eq_zero
    {Voter : Type*} [Fintype Voter] {n dimension : ℕ}
    (features : Candidate n → FeatureVector dimension)
    (profile : RankingProfile Voter n) (loss : ℝ → ℝ)
    (parameter : LinearRewardParameter dimension)
    (majorityRanking output : Ranking n)
    (hloss_nonnegative : ∀ x, 0 ≤ loss x) (hloss_monotone : Monotone loss)
    (hloss_zero_pos : 0 < loss 0)
    (hmajorityRanking : IsPairwiseMajorityRanking profile majorityRanking)
    (hinduced : InducesRanking features parameter output)
    (hvalue : majorityLoss features profile loss parameter = 0) :
    output = majorityRanking := by
  by_contra houtput_ne
  have hlower := loss_zero_le_majorityLoss_of_ne_pairwiseMajorityRanking
    features profile loss parameter majorityRanking output hloss_nonnegative hloss_monotone
    hmajorityRanking houtput_ne hinduced
  rw [hvalue] at hlower
  exact (not_lt_of_ge hlower) hloss_zero_pos

end GeEtAl2024AlignmentAxioms
