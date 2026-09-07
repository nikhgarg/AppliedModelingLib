import AL16SupplyDemandMatching.MainTheorems
import AppliedModelingLib.Foundations.Math.Asymptotics
import AppliedModelingLib.Foundations.Math.ExponentialBounds
import AppliedModelingLib.Foundations.Math.FiniteSum
import AppliedModelingLib.Foundations.Probability.Bernoulli
import AppliedModelingLib.Foundations.Probability.RealDistribution
import AppliedModelingLib.Markets.Matching.Affordability
import AppliedModelingLib.Markets.Matching.ContinuumCutoff
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Wisdom and Foolishness of Noisy Matching Markets: Top-Down Surface

PG24 works with arbitrary stable matchings and their market-clearing cutoff
representations.  Unlike PG23, the main route does not require uniqueness or
the A-L lattice theorem.
-/

open Filter Topology

namespace PG24NoisyMatchingMarkets

open AppliedModelingLib.Matching
open MeasureTheory

universe u v

variable {Student : Type u} {College : Type v}
variable (M : CutoffMarket Student College)

/-- Local PG24 copy: `(N + 1 : ℝ)` tends to infinity. -/
private theorem pg24_tendsto_nat_succ_cast_atTop :
    Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ))) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)

/-- Local PG24 copy: a fixed constant divided by `N + 1` is eventually small. -/
private theorem pg24_eventually_const_div_nat_succ_le_half (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, C / (((N + 1 : ℕ) : ℝ)) ≤ 1 / 2 := by
  have hlim :
      Tendsto (fun N : ℕ => C / (((N + 1 : ℕ) : ℝ))) atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop pg24_tendsto_nat_succ_cast_atTop C
  have hnear :
      ∀ᶠ N : ℕ in atTop,
        C / (((N + 1 : ℕ) : ℝ)) ∈ Set.Iio (1 / 2 : ℝ) :=
    hlim (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hnear] with N hN
  exact le_of_lt hN

/--
Local PG24 copy: a uniform negative-power upper bound is eventually below
every positive tolerance.
-/
private theorem pg24_eventually_forall_lt_of_uniform_rpow_neg_bound
    {α : ℕ → Type*} {f : ∀ N : ℕ, α N → ℝ}
    {A β : ℝ} {N0 : ℕ}
    (hβ_pos : 0 < β)
    (hbound :
      ∀ N : ℕ, N0 ≤ N →
        ∀ a : α N,
          f N a ≤ A * Real.rpow (((N + 1 : ℕ) : ℝ)) (-β)) :
    ∀ tol : ℝ, 0 < tol →
      ∀ᶠ N : ℕ in atTop, ∀ a : α N, f N a < tol := by
  intro tol htol
  have hpow :
      Tendsto
        (fun N : ℕ => Real.rpow (((N + 1 : ℕ) : ℝ)) (-β))
        atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hβ_pos).comp pg24_tendsto_nat_succ_cast_atTop
  have hupper_zero :
      Tendsto
        (fun N : ℕ => A * Real.rpow (((N + 1 : ℕ) : ℝ)) (-β))
        atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hpow : Tendsto
      (fun N : ℕ => A * Real.rpow (((N + 1 : ℕ) : ℝ)) (-β))
      atTop (nhds (A * 0)))
  have hsmall :
      ∀ᶠ N : ℕ in atTop,
        A * Real.rpow (((N + 1 : ℕ) : ℝ)) (-β) < tol :=
    hupper_zero (isOpen_Iio.mem_nhds htol)
  filter_upwards [eventually_ge_atTop N0, hsmall] with N hN hsmallN a
  exact lt_of_le_of_lt (hbound N hN a) hsmallN

/--
The source theorem route starts from any stable matching and obtains a
market-clearing cutoff representation by the A-L supply/demand interface.
-/
theorem stableMatching_has_marketClearing_cutoff
    (I : SupplyDemandInterface M) {μ : M.Matching}
    (hμ : M.Stable μ) :
    ∃ P : M.Cutoff, M.MarketClearing P ∧ M.RepresentedByCutoff μ P :=
  I.exists_marketClearing_cutoff_of_stable hμ

/--
PG24 cutoff affordance event: a value `v` student can afford some active
college iff one active noisy score crosses that college's cutoff.
-/
def cutoffAffordanceEvent {College : Type v} (active : Finset College)
    (v : ℝ) (noise cutoff : College → ℝ) : Prop :=
  AppliedModelingLib.Matching.cutoffCrossedOn active
    (AppliedModelingLib.Matching.noisyScore v noise) cutoff

/--
PG24 cutoff affordance probability: the real-valued probability that a value
`v` student can afford some college in the active set under a random noise
vector.
-/
noncomputable def cutoffAffordanceProbability {College : Type v}
    [MeasurableSpace (College → ℝ)]
    (noiseLaw : Measure (College → ℝ)) (active : Finset College)
    (v : ℝ) (cutoff : College → ℝ) : ℝ :=
  AppliedModelingLib.Matching.cutoffCrossingProbability noiseLaw active v cutoff

/-- Cutoff-affordance probabilities are nonnegative. -/
theorem cutoffAffordanceProbability_nonneg {College : Type v}
    [MeasurableSpace (College → ℝ)]
    (noiseLaw : Measure (College → ℝ)) (active : Finset College)
    (v : ℝ) (cutoff : College → ℝ) :
    0 ≤ cutoffAffordanceProbability noiseLaw active v cutoff :=
  AppliedModelingLib.Matching.cutoffCrossingProbability_nonneg
    noiseLaw active v cutoff

/-- Under a probability noise law, cutoff-affordance probabilities are at most one. -/
theorem cutoffAffordanceProbability_le_one {College : Type v}
    [MeasurableSpace (College → ℝ)]
    (noiseLaw : Measure (College → ℝ)) [IsProbabilityMeasure noiseLaw]
    (active : Finset College) (v : ℝ) (cutoff : College → ℝ) :
    cutoffAffordanceProbability noiseLaw active v cutoff ≤ 1 :=
  AppliedModelingLib.Matching.cutoffCrossingProbability_le_one
    noiseLaw active v cutoff

/--
PG24 single-college affordability probability: the real-valued probability
that one named college's noisy score crosses its cutoff.
-/
noncomputable def singleCollegeAffordanceProbability {College : Type v}
    [MeasurableSpace (College → ℝ)]
    (noiseLaw : Measure (College → ℝ)) (v : ℝ)
    (cutoff : College → ℝ) (c : College) : ℝ :=
  AppliedModelingLib.Matching.singleCutoffCrossingProbability noiseLaw v cutoff c

/--
PG24 max-concentration target around the expected maximum order statistic.
The source writes the center as `E[X^(n)]`.
-/
abbrev maximumOrderStatisticConcentrating
    (sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)) : Prop :=
  AppliedModelingLib.Probability.TopOrderDeviationConcentrating sampleLaw
    (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw)

/--
PG24 source definition of `β`-max-concentrating noise, expressed as the
paper's polynomial variance-rate condition for the maximum order statistic.
Here `maxVariance n` represents `Var[X^(n+1)]`.
-/
def betaMaxConcentratingVariance (maxVariance : ℕ → ℝ) (β : ℝ) : Prop :=
  0 < β ∧
    ∃ K : ℝ, ∃ N : ℕ, 0 ≤ K ∧
      ∀ n : ℕ, N ≤ n →
        maxVariance n ≤ K * Real.rpow (((n + 1 : ℕ) : ℝ)) (-β)

/--
The source variance-rate definition implies that the variance of the maximum
order statistic tends to zero.
-/
theorem betaMaxConcentratingVariance.tendsto_zero
    {maxVariance : ℕ → ℝ} {β : ℝ}
    (h : betaMaxConcentratingVariance maxVariance β)
    (hvariance_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ maxVariance n) :
    Tendsto maxVariance atTop (nhds 0) := by
  rcases h with ⟨hβ, K, N, hK_nonneg, hbound⟩
  have hupper_zero :
      Tendsto
        (fun n : ℕ => K * Real.rpow (((n + 1 : ℕ) : ℝ)) (-β))
        atTop (nhds 0) := by
    have hpow :=
      (AppliedModelingLib.Math.tendsto_nat_succ_cast_rpow_neg_nhds_zero hβ)
    simpa using (tendsto_const_nhds.mul hpow : Tendsto
      (fun n : ℕ => K * Real.rpow (((n + 1 : ℕ) : ℝ)) (-β))
      atTop (nhds (K * 0)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper_zero hvariance_nonneg ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  exact hbound n hn

/--
The Chebyshev source bound itself implies eventual nonnegativity of the
variance bound, so paper-facing Theorem 1 routes do not need a separate
`0 <= Var` premise.
-/
theorem betaMaxConcentratingVariance.tendsto_zero_of_chebyshev
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {maxVariance : ℕ → ℝ} {β : ℝ}
    (h : betaMaxConcentratingVariance maxVariance β)
    (hchebyshev :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
              (sampleLaw n)
              (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
              ε ≤
            maxVariance n / ε ^ 2) :
    Tendsto maxVariance atTop (nhds 0) := by
  have hvariance_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ maxVariance n := by
    have hcheb_one := hchebyshev 1 zero_lt_one
    filter_upwards [hcheb_one] with n hn
    have hprob_nonneg :
        0 ≤
          AppliedModelingLib.Probability.topOrderDeviationProbability
            (sampleLaw n)
            (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
            1 := by
      unfold AppliedModelingLib.Probability.topOrderDeviationProbability
      exact measureReal_nonneg
    have hdiv_nonneg : 0 ≤ maxVariance n / (1 : ℝ) ^ 2 :=
      le_trans hprob_nonneg hn
    simpa using hdiv_nonneg
  exact h.tendsto_zero hvariance_nonneg

/--
PG24 Chebyshev bridge from variance control to the concentration predicate
used in the attenuation proof.
-/
theorem maximumOrderStatisticConcentrating_of_chebyshev_variance_bound
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {varianceBound : ℕ → ℝ}
    (hvariance_zero : Tendsto varianceBound atTop (nhds 0))
    (hchebyshev :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
              (sampleLaw n)
              (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
              ε ≤
            varianceBound n / ε ^ 2) :
    maximumOrderStatisticConcentrating sampleLaw :=
  AppliedModelingLib.Probability.TopOrderDeviationConcentrating.of_chebyshev_bound
    hvariance_zero hchebyshev

/--
The paper-facing variance-bound route to maximum-order-statistic
concentration.  This exposes the variance bound on the maximum itself, and the
shared probability library supplies Chebyshev internally.
-/
theorem maximumOrderStatisticConcentrating_of_variance_bound
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {varianceBound : ℕ → ℝ}
    (hprob : ∀ n, IsProbabilityMeasure (sampleLaw n))
    (hvariance_zero : Tendsto varianceBound atTop (nhds 0))
    (hmem :
      ∀ᶠ n : ℕ in atTop,
        MemLp
          (fun sample : Fin (n + 1) → ℝ =>
            AppliedModelingLib.Probability.upperOrderStatistic sample
              (AppliedModelingLib.Probability.topSampleRank (n := n + 1))) 2
          (sampleLaw n))
    (hvariance_bound :
      ∀ᶠ n : ℕ in atTop,
        ProbabilityTheory.variance
          (fun sample : Fin (n + 1) → ℝ =>
            AppliedModelingLib.Probability.upperOrderStatistic sample
              (AppliedModelingLib.Probability.topSampleRank (n := n + 1)))
          (sampleLaw n) ≤ varianceBound n) :
    maximumOrderStatisticConcentrating sampleLaw :=
  AppliedModelingLib.Probability.TopOrderDeviationConcentrating.of_variance_bound
    (sampleLaw := sampleLaw)
    (varianceBound := varianceBound)
    (fun n => by
      letI : IsProbabilityMeasure (sampleLaw n) := hprob n
      infer_instance)
    hvariance_zero hmem hvariance_bound

/--
If the source variance-rate function eventually bounds the actual variance of
the maximum order statistic, then its polynomial rate still tends to zero.
-/
theorem betaMaxConcentratingVariance.tendsto_zero_of_variance_bound
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {maxVariance : ℕ → ℝ} {β : ℝ}
    (h : betaMaxConcentratingVariance maxVariance β)
    (hvariance_bound :
      ∀ᶠ n : ℕ in atTop,
        ProbabilityTheory.variance
          (fun sample : Fin (n + 1) → ℝ =>
            AppliedModelingLib.Probability.upperOrderStatistic sample
              (AppliedModelingLib.Probability.topSampleRank (n := n + 1)))
          (sampleLaw n) ≤ maxVariance n) :
    Tendsto maxVariance atTop (nhds 0) := by
  have hvariance_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ maxVariance n := by
    filter_upwards [hvariance_bound] with n hn
    exact
      (ProbabilityTheory.variance_nonneg
        (fun sample : Fin (n + 1) → ℝ =>
          AppliedModelingLib.Probability.upperOrderStatistic sample
            (AppliedModelingLib.Probability.topSampleRank (n := n + 1)))
        (sampleLaw n)).trans hn
  exact h.tendsto_zero hvariance_nonneg

theorem cutoffAffordanceProbability_le_sum_singleCollegeAffordanceProbability
    {College : Type v} [MeasurableSpace (College → ℝ)]
    (noiseLaw : Measure (College → ℝ)) (active : Finset College)
    (v : ℝ) (cutoff : College → ℝ) :
    cutoffAffordanceProbability noiseLaw active v cutoff ≤
      ∑ c ∈ active,
        singleCollegeAffordanceProbability noiseLaw v cutoff c :=
  AppliedModelingLib.Matching.cutoffCrossingProbability_le_sum_singleCutoffCrossingProbability
    noiseLaw active v cutoff

theorem cutoffAffordanceProbability_le_card_mul_of_singleCollegeAffordanceProbability_le
    {College : Type v} [MeasurableSpace (College → ℝ)]
    (noiseLaw : Measure (College → ℝ)) (active : Finset College)
    (v : ℝ) (cutoff : College → ℝ) {q : ℝ}
    (hbound :
      ∀ c ∈ active, singleCollegeAffordanceProbability noiseLaw v cutoff c ≤ q) :
    cutoffAffordanceProbability noiseLaw active v cutoff ≤
      (active.card : ℝ) * q :=
  AppliedModelingLib.Matching.cutoffCrossingProbability_le_card_mul_of_singleCutoffCrossingProbability_le
    noiseLaw active v cutoff hbound

theorem cutoffAffordanceProbability_le_cardBound_mul_of_singleCollegeAffordanceProbability_le
    {College : Type v} [MeasurableSpace (College → ℝ)]
    (noiseLaw : Measure (College → ℝ)) (active : Finset College)
    (v : ℝ) (cutoff : College → ℝ) {cardBound q : ℝ}
    (hcard : (active.card : ℝ) ≤ cardBound) (hq_nonneg : 0 ≤ q)
    (hbound :
      ∀ c ∈ active, singleCollegeAffordanceProbability noiseLaw v cutoff c ≤ q) :
    cutoffAffordanceProbability noiseLaw active v cutoff ≤
      cardBound * q :=
  AppliedModelingLib.Matching.cutoffCrossingProbability_le_cardBound_mul_of_singleCutoffCrossingProbability_le
    noiseLaw active v cutoff hcard hq_nonneg hbound

theorem cutoffAffordanceProbability_mono_active {College : Type v}
    [MeasurableSpace (College → ℝ)]
    (noiseLaw : Measure (College → ℝ)) [IsFiniteMeasure noiseLaw]
    {active larger : Finset College} {v : ℝ} {cutoff : College → ℝ}
    (hsubset : active ⊆ larger) :
    cutoffAffordanceProbability noiseLaw active v cutoff ≤
      cutoffAffordanceProbability noiseLaw larger v cutoff :=
  AppliedModelingLib.Matching.cutoffCrossingProbability_mono_active
    noiseLaw hsubset

/--
Cutoff-affordance union bound over a small/large active-set split.  This is
the concrete probability form of the upper side of the PG24 `C1/C2`
decomposition.
-/
theorem cutoffAffordanceProbability_union_le {College : Type v}
    [DecidableEq College] [MeasurableSpace (College → ℝ)]
    (noiseLaw : Measure (College → ℝ))
    (small large : Finset College) (v : ℝ) (cutoff : College → ℝ) :
    cutoffAffordanceProbability noiseLaw (small ∪ large) v cutoff ≤
      cutoffAffordanceProbability noiseLaw small v cutoff +
        cutoffAffordanceProbability noiseLaw large v cutoff :=
  AppliedModelingLib.Matching.cutoffCrossingProbability_union_le
    noiseLaw small large v cutoff

/--
Concrete PG24 decomposition inequalities for a total active set written as
the union of small and large colleges.
-/
theorem cutoffAffordanceProbability_decomposition_of_union
    {College : Type v} [DecidableEq College]
    [MeasurableSpace (College → ℝ)]
    (noiseLaw : Measure (College → ℝ)) [IsFiniteMeasure noiseLaw]
    {small large total : Finset College} {v : ℝ} {cutoff : College → ℝ}
    (htotal : total = small ∪ large) :
    cutoffAffordanceProbability noiseLaw large v cutoff ≤
        cutoffAffordanceProbability noiseLaw total v cutoff ∧
      cutoffAffordanceProbability noiseLaw total v cutoff ≤
        cutoffAffordanceProbability noiseLaw small v cutoff +
          cutoffAffordanceProbability noiseLaw large v cutoff := by
  constructor
  · refine cutoffAffordanceProbability_mono_active noiseLaw ?_
    intro c hc
    rw [htotal]
    exact Finset.mem_union.mpr (Or.inr hc)
  · rw [htotal]
    exact cutoffAffordanceProbability_union_le noiseLaw small large v cutoff

theorem cutoffAffordanceProbability_mono_lowerCutoff {College : Type v}
    [MeasurableSpace (College → ℝ)]
    (noiseLaw : Measure (College → ℝ)) [IsFiniteMeasure noiseLaw]
    {active : Finset College} {v : ℝ}
    {cutoff lowerCutoff : College → ℝ}
    (hlower : ∀ c ∈ active, lowerCutoff c ≤ cutoff c) :
    cutoffAffordanceProbability noiseLaw active v cutoff ≤
      cutoffAffordanceProbability noiseLaw active v lowerCutoff :=
  AppliedModelingLib.Matching.cutoffCrossingProbability_mono_lowerCutoff
    noiseLaw hlower

theorem constantCutoffAffordanceProbability_le_of_cutoff_le {College : Type v}
    [MeasurableSpace (College → ℝ)]
    (noiseLaw : Measure (College → ℝ)) [IsFiniteMeasure noiseLaw]
    {active : Finset College} {v P : ℝ} {cutoff : College → ℝ}
    (hupper : ∀ c ∈ active, cutoff c ≤ P) :
    cutoffAffordanceProbability noiseLaw active v (fun _ => P) ≤
      cutoffAffordanceProbability noiseLaw active v cutoff :=
  AppliedModelingLib.Matching.constantCutoffProbability_le_of_cutoff_le
    noiseLaw hupper

theorem cutoffAffordanceProbability_le_constantCutoff_of_le {College : Type v}
    [MeasurableSpace (College → ℝ)]
    (noiseLaw : Measure (College → ℝ)) [IsFiniteMeasure noiseLaw]
    {active : Finset College} {v P : ℝ} {cutoff : College → ℝ}
    (hlower : ∀ c ∈ active, P ≤ cutoff c) :
    cutoffAffordanceProbability noiseLaw active v cutoff ≤
      cutoffAffordanceProbability noiseLaw active v (fun _ => P) :=
  AppliedModelingLib.Matching.cutoffCrossingProbability_le_constantCutoff_of_le
    noiseLaw hlower

theorem cutoffAffordanceProbability_mono_value {College : Type v}
    [MeasurableSpace (College → ℝ)]
    (noiseLaw : Measure (College → ℝ)) [IsFiniteMeasure noiseLaw]
    {active : Finset College} {v w : ℝ} {cutoff : College → ℝ}
    (hvw : v ≤ w) :
    cutoffAffordanceProbability noiseLaw active v cutoff ≤
      cutoffAffordanceProbability noiseLaw active w cutoff :=
  AppliedModelingLib.Matching.cutoffCrossingProbability_mono_value
    noiseLaw hvw

/--
PG24 model regularity for college capacities: no college has capacity larger
than `alpha / C`.
-/
def capacityRegular (capacity : College → ℝ) (alpha : ℝ) (C : ℕ) : Prop :=
  ∀ c : College, capacity c < alpha / (C : ℝ)

/-- The source's strict capacity regularity gives the weak bound used in estimates. -/
theorem capacityRegular.le {capacity : College → ℝ} {alpha : ℝ} {C : ℕ}
    (h : capacityRegular (College := College) capacity alpha C) :
    ∀ c : College, capacity c ≤ alpha / (C : ℝ) :=
  fun c => le_of_lt (h c)

/-- Prefix block of colleges by the paper's sorted index convention. -/
def indexPrefixSmall (k C : ℕ) : Finset (Fin (C + 1)) :=
  Finset.univ.filter (fun c : Fin (C + 1) => (c : ℕ) < k)

/-- Suffix block of colleges by the paper's sorted index convention. -/
def indexSuffixLarge (k C : ℕ) : Finset (Fin (C + 1)) :=
  Finset.univ.filter (fun c : Fin (C + 1) => k ≤ (c : ℕ))

/--
The sorted-index prefix and suffix partition all colleges.  This is the
finite-set part of the paper's `F_1/F_2` split.
-/
theorem indexPrefixSmall_union_indexSuffixLarge (k C : ℕ) :
    (Finset.univ : Finset (Fin (C + 1))) =
      indexPrefixSmall k C ∪ indexSuffixLarge k C := by
  classical
  ext c
  by_cases hc : (c : ℕ) < k
  · simp [indexPrefixSmall, indexSuffixLarge, hc]
  · have hkc : k ≤ (c : ℕ) := le_of_not_gt hc
    simp [indexPrefixSmall, indexSuffixLarge, hc, hkc]

/--
The prefix block has at most `k` elements.  The proof is by injecting the
prefix into `Fin k`.
-/
theorem indexPrefixSmall_card_le_index (k C : ℕ) :
    ((indexPrefixSmall k C).card : ℝ) ≤ (k : ℝ) := by
  classical
  have hnat : (indexPrefixSmall k C).card ≤ k := by
    let f : {c // c ∈ indexPrefixSmall k C} → Fin k :=
      fun c => ⟨(c.1 : ℕ), (Finset.mem_filter.mp c.2).2⟩
    have hinj : Function.Injective f := by
      intro a b hab
      have hval : (a.1 : ℕ) = (b.1 : ℕ) := by
        change (f a).val = (f b).val
        exact congrArg Fin.val hab
      exact Subtype.ext (Fin.ext hval)
    have hcard := Fintype.card_le_of_injective f hinj
    simpa [Fintype.card_coe] using hcard
  exact_mod_cast hnat

/-- If the split index is a valid coordinate, the prefix block has exactly `k` colleges. -/
theorem indexPrefixSmall_card_eq_of_le {k C : ℕ} (hk : k ≤ C + 1) :
    (indexPrefixSmall k C).card = k := by
  classical
  have hupper : (indexPrefixSmall k C).card ≤ k := by
    exact_mod_cast (indexPrefixSmall_card_le_index k C)
  have hlower : k ≤ (indexPrefixSmall k C).card := by
    let f : Fin k → {c // c ∈ indexPrefixSmall k C} :=
      fun c =>
        ⟨⟨c.1, lt_of_lt_of_le c.2 hk⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, c.2⟩⟩
    have hinj : Function.Injective f := by
      intro a b hab
      have hval : (a : ℕ) = (b : ℕ) := by
        have h := congrArg
          (fun x : {c // c ∈ indexPrefixSmall k C} => (x.1 : ℕ)) hab
        simpa [f] using h
      exact Fin.ext hval
    have hcard := Fintype.card_le_of_injective f hinj
    simpa [Fintype.card_coe] using hcard
  exact Nat.le_antisymm hupper hlower

/-- The sorted-index prefix and suffix blocks are disjoint. -/
theorem indexPrefixSmall_disjoint_indexSuffixLarge (k C : ℕ) :
    Disjoint (indexPrefixSmall k C) (indexSuffixLarge k C) := by
  classical
  rw [Finset.disjoint_left]
  intro c hcPrefix hcSuffix
  have hlt : (c : ℕ) < k := (Finset.mem_filter.mp hcPrefix).2
  have hle : k ≤ (c : ℕ) := (Finset.mem_filter.mp hcSuffix).2
  exact (not_le_of_gt hlt) hle

/--
If cutoff coordinates are sorted by increasing index, every prefix cutoff is
weakly below the split cutoff.
-/
theorem indexPrefixSmall_cutoff_le_split_of_sorted
    {k C : ℕ} {cutoff : Fin (C + 1) → ℝ}
    (hk : k < C + 1)
    (hsorted :
      ∀ i j : Fin (C + 1), (i : ℕ) ≤ (j : ℕ) →
        cutoff i ≤ cutoff j) :
    ∀ c ∈ indexPrefixSmall k C,
      cutoff c ≤ cutoff (⟨k, hk⟩ : Fin (C + 1)) := by
  intro c hc
  have hlt : (c : ℕ) < k := (Finset.mem_filter.mp hc).2
  exact hsorted c (⟨k, hk⟩ : Fin (C + 1)) (Nat.le_of_lt hlt)

/--
If the sorted-index suffix is nonempty, then the split index itself is a valid
college coordinate and is the index-minimal element of that suffix.
-/
theorem indexSuffixLarge_splitIndex_mem_and_min_of_nonempty
    {k C : ℕ} (hne : (indexSuffixLarge k C).Nonempty) :
    ∃ hk : k < C + 1,
      (⟨k, hk⟩ : Fin (C + 1)) ∈ indexSuffixLarge k C ∧
        ∀ c ∈ indexSuffixLarge k C, k ≤ (c : ℕ) := by
  classical
  rcases hne with ⟨c, hc⟩
  have hk_le_c : k ≤ (c : ℕ) := (Finset.mem_filter.mp hc).2
  have hc_lt : (c : ℕ) < C + 1 := c.isLt
  have hk : k < C + 1 := lt_of_le_of_lt hk_le_c hc_lt
  refine ⟨hk, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩
  · intro c hc
    exact (Finset.mem_filter.mp hc).2

/-- Concrete floor split index for the paper's `epsilon*C` initial block. -/
noncomputable def epsilonFloorSplitIndex (epsilon : ℝ) (C : ℕ) : ℕ :=
  Nat.floor (epsilon * ((C + 1 : ℕ) : ℝ))

/-- The floor split index is bounded by `epsilon * (C+1)`. -/
theorem epsilonFloorSplitIndex_le (epsilon : ℝ) (C : ℕ)
    (hepsilon_nonneg : 0 ≤ epsilon) :
    (epsilonFloorSplitIndex epsilon C : ℝ) ≤
      epsilon * ((C + 1 : ℕ) : ℝ) := by
  unfold epsilonFloorSplitIndex
  exact Nat.floor_le
    (mul_nonneg hepsilon_nonneg (Nat.cast_nonneg _))

/-- For `0 ≤ epsilon < 1`, the floor split index is a valid college coordinate. -/
theorem epsilonFloorSplitIndex_lt_succ (epsilon : ℝ) (C : ℕ)
    (hepsilon_nonneg : 0 ≤ epsilon) (hepsilon_lt_one : epsilon < 1) :
    epsilonFloorSplitIndex epsilon C < C + 1 := by
  unfold epsilonFloorSplitIndex
  rw [Nat.floor_lt (mul_nonneg hepsilon_nonneg (Nat.cast_nonneg _))]
  have hC_pos : 0 < (((C + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos C
  nlinarith

/--
For the paper's floor split with `epsilon < 1`, the prefix block contains
exactly `epsilonFloorSplitIndex epsilon C` colleges.
-/
theorem indexPrefixSmall_card_eq_epsilonFloorSplitIndex
    (epsilon : ℝ) (C : ℕ)
    (hepsilon_nonneg : 0 ≤ epsilon) (hepsilon_lt_one : epsilon < 1) :
    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C).card =
      epsilonFloorSplitIndex epsilon C :=
  indexPrefixSmall_card_eq_of_le
    (Nat.le_of_lt
      (epsilonFloorSplitIndex_lt_succ epsilon C hepsilon_nonneg
        hepsilon_lt_one))

/--
The floor split eventually keeps at least half of its nominal linear size.
This is the finite-count ingredient for the appendix overflow proof.
-/
theorem epsilonFloorSplitIndex_eventually_half_mul_le
    (epsilon : ℝ) (hepsilon_pos : 0 < epsilon) :
    ∀ᶠ C : ℕ in atTop,
      (epsilon / 2) * ((C + 1 : ℕ) : ℝ) ≤
        (epsilonFloorSplitIndex epsilon C : ℝ) := by
  have hcoef_pos : 0 < epsilon / 2 := by linarith
  have hhalf_atTop :
      Tendsto
        (fun C : ℕ => (epsilon / 2) * (((C + 1 : ℕ) : ℝ)))
        atTop atTop :=
    Filter.Tendsto.const_mul_atTop hcoef_pos
      pg24_tendsto_nat_succ_cast_atTop
  have hlarge :
      ∀ᶠ C : ℕ in atTop,
        1 ≤ (epsilon / 2) * (((C + 1 : ℕ) : ℝ)) :=
    hhalf_atTop.eventually_ge_atTop 1
  filter_upwards [hlarge] with C hlargeC
  have hfloor_lt_add :
      epsilon * (((C + 1 : ℕ) : ℝ)) <
        (epsilonFloorSplitIndex epsilon C : ℝ) + 1 := by
    unfold epsilonFloorSplitIndex
    exact Nat.lt_floor_add_one (epsilon * (((C + 1 : ℕ) : ℝ)))
  have hhalf_le_sub :
      (epsilon / 2) * (((C + 1 : ℕ) : ℝ)) ≤
        epsilon * (((C + 1 : ℕ) : ℝ)) - 1 := by
    nlinarith
  exact le_of_lt (lt_of_le_of_lt hhalf_le_sub (by linarith))

/--
The actual prefix block at the paper's floor split eventually has linear
cardinality at least `(epsilon / 2) * (C + 1)`.
-/
theorem indexPrefixSmall_card_eventually_half_mul_le
    (epsilon : ℝ) (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) :
    ∀ᶠ C : ℕ in atTop,
      (epsilon / 2) * ((C + 1 : ℕ) : ℝ) ≤
        ((indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C).card : ℝ) := by
  filter_upwards
    [epsilonFloorSplitIndex_eventually_half_mul_le epsilon hepsilon_pos] with
    C hfloor
  rw [indexPrefixSmall_card_eq_epsilonFloorSplitIndex
    epsilon C hepsilon_pos.le hepsilon_lt_one]
  exact hfloor

/--
Active capacity decomposes over the paper's sorted-index `F_1/F_2` split.
-/
theorem activeCapacity_indexPrefixSmall_add_indexSuffixLarge
    (k C : ℕ) (capacity : Fin (C + 1) → ℝ) :
    AppliedModelingLib.Matching.activeCapacity
        (Finset.univ : Finset (Fin (C + 1))) capacity =
      AppliedModelingLib.Matching.activeCapacity (indexPrefixSmall k C) capacity +
        AppliedModelingLib.Matching.activeCapacity (indexSuffixLarge k C) capacity :=
  AppliedModelingLib.Matching.activeCapacity_eq_add_of_partition
    capacity (indexPrefixSmall_union_indexSuffixLarge k C)
    (indexPrefixSmall_disjoint_indexSuffixLarge k C)

/--
PG24 finite capacity arithmetic: if a subset has at most `epsilon * C`
colleges and each college has capacity at most `alpha / C`, then the subset's
total capacity is at most `epsilon * alpha`.
-/
theorem smallActiveSet_capacity_le_epsilon_mul_alpha {College : Type v}
    (active : Finset College) (capacity : College → ℝ)
    {epsilon alpha : ℝ} {C : ℕ}
    (hcard : (active.card : ℝ) ≤ epsilon * (C : ℝ))
    (halpha_nonneg : 0 ≤ alpha) (hC_pos : 0 < (C : ℝ))
    (hcap : ∀ c ∈ active, capacity c ≤ alpha / (C : ℝ)) :
    AppliedModelingLib.Matching.activeCapacity active capacity ≤ epsilon * alpha :=
  AppliedModelingLib.Matching.activeCapacity_le_epsilon_mul_alpha_of_card_le_mul
    active capacity hcard halpha_nonneg hC_pos hcap

/--
PG24 semantic mass-clearing interface for Theorem 2.

The abstract `CutoffMarket` API intentionally does not define interval or
matched masses.  This paper-local interface records the source model's mass
objects and the market-clearing capacity-fill laws needed by the amplification
proof.  Endpoint estimates remain outside this structure.
-/
structure Theorem2MassClearingInterface
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))) where
  largeIntervalMass : ∀ C : ℕ, (Mseq C).Cutoff → ℝ
  largeMatchedMass : ∀ C : ℕ, (Mseq C).Cutoff → ℝ
  smallMatchedMass : ∀ C : ℕ, (Mseq C).Cutoff → ℝ
  largeIntervalMass_le_totalActiveCapacity :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          largeIntervalMass C P ≤
            AppliedModelingLib.Matching.activeCapacity
              (Finset.univ : Finset (Fin (C + 1)))
              (Mseq C).capacity
  largeActiveCapacity_le_matchedMass :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          AppliedModelingLib.Matching.activeCapacity
              (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
              (Mseq C).capacity ≤
            largeMatchedMass C P
  smallMatchedMass_le_activeCapacity :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          smallMatchedMass C P ≤
            AppliedModelingLib.Matching.activeCapacity
              (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
              (Mseq C).capacity

/--
For a constant cutoff on a nonempty finite active set, the affordance event is
the same maximum-order-statistic crossing event used by the source proof.
-/
theorem constantCutoffAffordanceEvent_iff_topOrderStatistic_gt
    {C : ℕ} [NeZero C] (noise : Fin C → ℝ) (v P : ℝ) :
    cutoffAffordanceEvent (Finset.univ : Finset (Fin C)) v noise (fun _ => P) ↔
      P - v <
        AppliedModelingLib.Probability.upperOrderStatistic noise
          (AppliedModelingLib.Matching.topSampleRank (n := C)) := by
  rw [cutoffAffordanceEvent, AppliedModelingLib.Matching.cutoffCrossedOn_univ_iff_cutoffCrossed,
    AppliedModelingLib.Matching.cutoffCrossed]
  simpa using
    AppliedModelingLib.Matching.exists_constant_cutoff_noisyScore_iff_topOrderStatistic_gt
      noise v P

theorem constantCutoffAffordanceProbability_eq_topOrderCrossingProbability
    {C : ℕ} [NeZero C]
    (noiseLaw : Measure (Fin C → ℝ)) (v P : ℝ) :
    cutoffAffordanceProbability noiseLaw
        (Finset.univ : Finset (Fin C)) v (fun _ => P) =
      AppliedModelingLib.Matching.topOrderCrossingProbability noiseLaw (P - v) :=
  AppliedModelingLib.Matching.cutoffCrossingProbability_univ_constant_eq_topOrderCrossingProbability
    noiseLaw v P

theorem constantCutoffAffordanceProbability_iidProduct_tendsto_one_of_lowerCDFMass_lt_one
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw] {v P : ℝ}
    (hlt : AppliedModelingLib.Probability.lowerCDFMass noiseLaw (P - v) < 1) :
    Tendsto
      (fun C : ℕ =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) v (fun _ => P))
      atTop (nhds 1) :=
  AppliedModelingLib.Matching.cutoffCrossingProbability_univ_constant_iidProduct_tendsto_one_of_lowerCDFMass_lt_one
    noiseLaw hlt

theorem constantCutoffAffordanceProbability_le_topOrderDeviationProbability_of_center_add_le
    {C : ℕ} [NeZero C]
    (noiseLaw : Measure (Fin C → ℝ)) [IsFiniteMeasure noiseLaw]
    {v P center ε : ℝ} (hsep : center + ε ≤ P - v) :
    cutoffAffordanceProbability noiseLaw
        (Finset.univ : Finset (Fin C)) v (fun _ => P) ≤
      AppliedModelingLib.Matching.topOrderDeviationProbability noiseLaw center ε := by
  simpa [cutoffAffordanceProbability] using
    AppliedModelingLib.Matching.cutoffCrossingProbability_univ_constant_le_topOrderDeviationProbability_of_center_add_le
      noiseLaw hsep

theorem cutoffAffordanceProbability_le_topOrderDeviationProbability_of_uniform_lower_cutoff
    {C : ℕ} [NeZero C]
    (noiseLaw : Measure (Fin C → ℝ)) [IsFiniteMeasure noiseLaw]
    {v P center ε : ℝ} {cutoff : Fin C → ℝ}
    (hlower : ∀ c : Fin C, P ≤ cutoff c)
    (hsep : center + ε ≤ P - v) :
    cutoffAffordanceProbability noiseLaw
        (Finset.univ : Finset (Fin C)) v cutoff ≤
      AppliedModelingLib.Matching.topOrderDeviationProbability noiseLaw center ε := by
  simpa [cutoffAffordanceProbability] using
    AppliedModelingLib.Matching.cutoffCrossingProbability_univ_le_topOrderDeviationProbability_of_constant_le_cutoff
      noiseLaw hlower hsep

theorem one_sub_constantCutoffAffordanceProbability_le_topOrderDeviationProbability_of_lt_center_sub
    {C : ℕ} [NeZero C]
    (noiseLaw : Measure (Fin C → ℝ)) [IsProbabilityMeasure noiseLaw]
    {v P center ε : ℝ} (hε : 0 < ε) (hsep : P - v < center - ε) :
    1 - cutoffAffordanceProbability noiseLaw
        (Finset.univ : Finset (Fin C)) v (fun _ => P) ≤
      AppliedModelingLib.Matching.topOrderDeviationProbability noiseLaw center ε := by
  simpa [cutoffAffordanceProbability] using
    AppliedModelingLib.Matching.one_sub_cutoffCrossingProbability_univ_constant_le_topOrderDeviationProbability_of_lt_center_sub
      noiseLaw hε hsep

theorem one_sub_cutoffAffordanceProbability_le_topOrderDeviationProbability_of_uniform_upper_cutoff
    {C : ℕ} [NeZero C]
    (noiseLaw : Measure (Fin C → ℝ)) [IsProbabilityMeasure noiseLaw]
    {v P center ε : ℝ} {cutoff : Fin C → ℝ}
    (hupper : ∀ c : Fin C, cutoff c ≤ P)
    (hε : 0 < ε) (hsep : P - v < center - ε) :
    1 - cutoffAffordanceProbability noiseLaw
        (Finset.univ : Finset (Fin C)) v cutoff ≤
      AppliedModelingLib.Matching.topOrderDeviationProbability noiseLaw center ε := by
  simpa [cutoffAffordanceProbability] using
    AppliedModelingLib.Matching.one_sub_cutoffCrossingProbability_univ_le_topOrderDeviationProbability_of_cutoff_le_constant
      noiseLaw hupper hε hsep

theorem cutoffAffordanceProbability_tendsto_zero_of_eventually_uniform_lower_cutoff
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {center threshold : ℕ → ℝ}
    {cutoff : ∀ n : ℕ, Fin (n + 1) → ℝ}
    (v : ℝ)
    (hfinite : ∀ n, IsFiniteMeasure (sampleLaw n))
    (hconc : AppliedModelingLib.Probability.TopOrderDeviationConcentrating sampleLaw center)
    {ε : ℝ} (hε : 0 < ε)
    (hlower : ∀ᶠ n : ℕ in atTop, ∀ c : Fin (n + 1), threshold n ≤ cutoff n c)
    (hsep : ∀ᶠ n : ℕ in atTop, center n + ε ≤ threshold n - v) :
    Tendsto
      (fun n : ℕ =>
        cutoffAffordanceProbability (sampleLaw n)
          (Finset.univ : Finset (Fin (n + 1))) v (cutoff n))
      atTop (nhds 0) :=
  AppliedModelingLib.Matching.cutoffCrossingProbability_univ_tendsto_zero_of_eventually_constant_le_cutoff
    v hfinite hconc hε hlower hsep

theorem one_sub_cutoffAffordanceProbability_tendsto_zero_of_eventually_uniform_upper_cutoff
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {center threshold : ℕ → ℝ}
    {cutoff : ∀ n : ℕ, Fin (n + 1) → ℝ}
    (v : ℝ)
    (hprob : ∀ n, IsProbabilityMeasure (sampleLaw n))
    (hconc : AppliedModelingLib.Probability.TopOrderDeviationConcentrating sampleLaw center)
    {ε : ℝ} (hε : 0 < ε)
    (hupper : ∀ᶠ n : ℕ in atTop, ∀ c : Fin (n + 1), cutoff n c ≤ threshold n)
    (hsep : ∀ᶠ n : ℕ in atTop, threshold n - v < center n - ε) :
    Tendsto
      (fun n : ℕ =>
        1 - cutoffAffordanceProbability (sampleLaw n)
          (Finset.univ : Finset (Fin (n + 1))) v (cutoff n))
      atTop (nhds 0) :=
  AppliedModelingLib.Matching.one_sub_cutoffCrossingProbability_univ_tendsto_zero_of_eventually_cutoff_le_constant
    v hprob hconc hε hupper hsep

theorem cutoffAffordanceProbability_tendsto_zero_of_eventually_uniform_lower_cutoff_expectedTop
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {threshold : ℕ → ℝ}
    {cutoff : ∀ n : ℕ, Fin (n + 1) → ℝ}
    (v : ℝ)
    (hfinite : ∀ n, IsFiniteMeasure (sampleLaw n))
    (hconc : maximumOrderStatisticConcentrating sampleLaw)
    {ε : ℝ} (hε : 0 < ε)
    (hlower : ∀ᶠ n : ℕ in atTop, ∀ c : Fin (n + 1), threshold n ≤ cutoff n c)
    (hsep :
      ∀ᶠ n : ℕ in atTop,
        AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n + ε ≤
          threshold n - v) :
    Tendsto
      (fun n : ℕ =>
        cutoffAffordanceProbability (sampleLaw n)
          (Finset.univ : Finset (Fin (n + 1))) v (cutoff n))
      atTop (nhds 0) :=
  cutoffAffordanceProbability_tendsto_zero_of_eventually_uniform_lower_cutoff
    v hfinite hconc hε hlower hsep

theorem one_sub_cutoffAffordanceProbability_tendsto_zero_of_eventually_uniform_upper_cutoff_expectedTop
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {threshold : ℕ → ℝ}
    {cutoff : ∀ n : ℕ, Fin (n + 1) → ℝ}
    (v : ℝ)
    (hprob : ∀ n, IsProbabilityMeasure (sampleLaw n))
    (hconc : maximumOrderStatisticConcentrating sampleLaw)
    {ε : ℝ} (hε : 0 < ε)
    (hupper : ∀ᶠ n : ℕ in atTop, ∀ c : Fin (n + 1), cutoff n c ≤ threshold n)
    (hsep :
      ∀ᶠ n : ℕ in atTop,
        threshold n - v <
          AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n - ε) :
    Tendsto
      (fun n : ℕ =>
        1 - cutoffAffordanceProbability (sampleLaw n)
          (Finset.univ : Finset (Fin (n + 1))) v (cutoff n))
      atTop (nhds 0) :=
  one_sub_cutoffAffordanceProbability_tendsto_zero_of_eventually_uniform_upper_cutoff
    v hprob hconc hε hupper hsep

/--
Theorem 1 attenuation target: below the efficient threshold the match
probability tends to zero, and above it the match probability tends to one.

The eventual proof must instantiate `matchProb` with the paper's
stable-matching probability, uniformly over the admissible stable matchings.
-/
def theorem1_attenuationConclusion
    (matchProb : ℕ → ℝ → ℝ) (vS : ℝ) : Prop :=
  (∀ v : ℝ, v < vS → Tendsto (fun C : ℕ => matchProb C v) atTop (nhds 0)) ∧
  (∀ v : ℝ, vS < v → Tendsto (fun C : ℕ => matchProb C v) atTop (nhds 1))

/--
Attenuation route for cutoff vectors squeezed around the expected maximum
order statistic.  This captures the clean source heuristic before the full
PG24 dense-cluster argument: if every cutoff is eventually bounded below and
above by thresholds whose gaps from `E[X^(n)]` both converge to `vS`, then the
affordance probability converges to the `vS` step rule.
-/
theorem theorem1_attenuation_of_expected_max_cutoff_sandwich
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {lowerCutoff upperCutoff : ℕ → ℝ}
    {cutoff : ∀ n : ℕ, Fin (n + 1) → ℝ}
    {vS : ℝ}
    (hprob : ∀ n, IsProbabilityMeasure (sampleLaw n))
    (hconc : maximumOrderStatisticConcentrating sampleLaw)
    (hlower :
      ∀ᶠ n : ℕ in atTop,
        ∀ c : Fin (n + 1), lowerCutoff n ≤ cutoff n c)
    (hupper :
      ∀ᶠ n : ℕ in atTop,
        ∀ c : Fin (n + 1), cutoff n c ≤ upperCutoff n)
    (hlower_threshold :
      Tendsto
        (fun n : ℕ =>
          lowerCutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
        atTop (nhds vS))
    (hupper_threshold :
      Tendsto
        (fun n : ℕ =>
          upperCutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
        atTop (nhds vS)) :
    theorem1_attenuationConclusion
      (fun n : ℕ => fun v : ℝ =>
        cutoffAffordanceProbability (sampleLaw n)
          (Finset.univ : Finset (Fin (n + 1))) v (cutoff n))
      vS := by
  refine ⟨?_, ?_⟩
  · intro v hv
    let gap : ℝ := (vS - v) / 2
    have hgap_pos : 0 < gap := by
      dsimp [gap]
      linarith
    have htarget : v + gap < vS := by
      dsimp [gap]
      linarith
    have hnear :
        ∀ᶠ n : ℕ in atTop,
          v + gap <
            lowerCutoff n -
              AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n :=
      hlower_threshold (isOpen_Ioi.mem_nhds htarget)
    have hsep :
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n + gap ≤
            lowerCutoff n - v := by
      filter_upwards [hnear] with n hn
      linarith
    exact
      cutoffAffordanceProbability_tendsto_zero_of_eventually_uniform_lower_cutoff_expectedTop
        (sampleLaw := sampleLaw)
        (threshold := lowerCutoff)
        (cutoff := cutoff)
        v
        (fun n => by
          haveI : IsProbabilityMeasure (sampleLaw n) := hprob n
          infer_instance)
        hconc hgap_pos hlower hsep
  · intro v hv
    let gap : ℝ := (v - vS) / 2
    have hgap_pos : 0 < gap := by
      dsimp [gap]
      linarith
    have htarget : vS < v - gap := by
      dsimp [gap]
      linarith
    have hnear :
        ∀ᶠ n : ℕ in atTop,
          upperCutoff n -
              AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n <
            v - gap :=
      hupper_threshold (isOpen_Iio.mem_nhds htarget)
    have hsep :
        ∀ᶠ n : ℕ in atTop,
          upperCutoff n - v <
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n - gap := by
      filter_upwards [hnear] with n hn
      linarith
    have hfail :
        Tendsto
          (fun n : ℕ =>
            1 -
              cutoffAffordanceProbability (sampleLaw n)
                (Finset.univ : Finset (Fin (n + 1))) v (cutoff n))
          atTop (nhds 0) :=
      one_sub_cutoffAffordanceProbability_tendsto_zero_of_eventually_uniform_upper_cutoff_expectedTop
        (sampleLaw := sampleLaw)
        (threshold := upperCutoff)
        (cutoff := cutoff)
        v hprob hconc hgap_pos hupper hsep
    have hsum :
        Tendsto
          (fun n : ℕ =>
            1 - (1 -
              cutoffAffordanceProbability (sampleLaw n)
                (Finset.univ : Finset (Fin (n + 1))) v (cutoff n)))
          atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub hfail
    simpa using hsum

/--
Theorem 1 source-shaped target.  `Admissible C` represents the paper's
stable-matchings/economies `mu ∈ M(D,C)`, so the eventual bounds are uniform
over every admissible matching once `C` is large.
-/
def theorem1_uniformAttenuationConclusion
    (Admissible : ℕ → Type*) (matchProb : ∀ C, Admissible C → ℝ → ℝ)
    (vS : ℝ) : Prop :=
  (∀ v ε, v < vS → 0 < ε →
    ∀ᶠ C : ℕ in atTop, ∀ μ : Admissible C, matchProb C μ v < ε) ∧
  (∀ v ε, vS < v → 0 < ε →
    ∀ᶠ C : ℕ in atTop, ∀ μ : Admissible C, 1 - ε < matchProb C μ v)

/--
The uniform Theorem 1 attenuation statement implies the same source-style
eventual bounds along any selected sequence of admissible stable matchings.
-/
theorem theorem1_attenuation_eventual_bounds_of_uniform_selected
    {Admissible : ℕ → Type*} {matchProb : ∀ C, Admissible C → ℝ → ℝ}
    {vS : ℝ}
    (select : ∀ C : ℕ, Admissible C)
    (h : theorem1_uniformAttenuationConclusion
      Admissible matchProb vS) :
    (∀ v ε, v < vS → 0 < ε →
      ∀ᶠ C : ℕ in atTop, matchProb C (select C) v < ε) ∧
    (∀ v ε, vS < v → 0 < ε →
      ∀ᶠ C : ℕ in atTop, 1 - ε < matchProb C (select C) v) := by
  constructor
  · intro v ε hv hε
    filter_upwards [h.1 v ε hv hε] with C hC
    exact hC (select C)
  · intro v ε hv hε
    filter_upwards [h.2 v ε hv hε] with C hC
    exact hC (select C)

/--
Appendix-style uniform error certificate for Theorem 1.  The analytic proof
must derive the two visible error bounds from the max-concentration and
cutoff-vector arguments; once those bounds tend to zero, the paper's uniform
attenuation conclusion follows.
-/
structure Theorem1UniformAttenuationErrorCertificate
    (Admissible : ℕ → Type*) (matchProb : ∀ C, Admissible C → ℝ → ℝ)
    (vS : ℝ) where
  lowError : ℕ → ℝ
  highError : ℕ → ℝ
  lowError_tendsto_zero : Tendsto lowError atTop (nhds 0)
  highError_tendsto_zero : Tendsto highError atTop (nhds 0)
  low_value_bound :
    ∀ v, v < vS →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C, matchProb C μ v ≤ lowError C
  high_value_bound :
    ∀ v, vS < v →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C, 1 - highError C ≤ matchProb C μ v

/--
Theorem 1 top-down closure from the appendix error estimates.  This is the
formal target for the remaining attenuation proof propositions.
-/
theorem theorem1_uniformAttenuation_of_error_certificate
    {Admissible : ℕ → Type*} {matchProb : ∀ C, Admissible C → ℝ → ℝ}
    {vS : ℝ}
    (cert :
      Theorem1UniformAttenuationErrorCertificate
        Admissible matchProb vS) :
    theorem1_uniformAttenuationConclusion Admissible matchProb vS := by
  constructor
  · intro v ε hv hε
    have hsmall : ∀ᶠ C : ℕ in atTop, cert.lowError C < ε :=
      cert.lowError_tendsto_zero (isOpen_Iio.mem_nhds hε)
    filter_upwards [cert.low_value_bound v hv, hsmall] with C hbound herr μ
    exact lt_of_le_of_lt (hbound μ) herr
  · intro v ε hv hε
    have hsmall : ∀ᶠ C : ℕ in atTop, cert.highError C < ε :=
      cert.highError_tendsto_zero (isOpen_Iio.mem_nhds hε)
    filter_upwards [cert.high_value_bound v hv, hsmall] with C hbound herr μ
    have hstrict : 1 - ε < 1 - cert.highError C := by
      linarith
    exact lt_of_lt_of_le hstrict (hbound μ)

/--
If an interval/tail-mass argument gives `epsilon * p` as a lower bound on
matched mass, and the same mass is smaller than `epsilon^2`, then the pointwise
match probability is below `epsilon`.  This is the algebraic core of the
attenuation proof's low-value mass-splitting step.
-/
theorem theorem1_lowValue_pointwise_of_tail_mass_bound
    {p epsilon tailMass : ℝ}
    (hepsilon_pos : 0 < epsilon)
    (htail_lower : epsilon * p ≤ tailMass)
    (htail_small : tailMass < epsilon ^ 2) :
    p < epsilon := by
  have hmul_lt : epsilon * p < epsilon * epsilon := by
    nlinarith [htail_lower, htail_small]
  nlinarith [hmul_lt, hepsilon_pos]

/--
Low-value tail-mass step with the interval-mass lower bound visible.  If the
source interval has mass at least `epsilon`, the endpoint probability is
nonnegative, and the interval tail mass is at least `intervalMass * p`, then
the usual `epsilon * p` lower bound follows.
-/
theorem theorem1_lowValue_pointwise_of_interval_tail_mass_bound
    {p epsilon intervalMass tailMass : ℝ}
    (hepsilon_pos : 0 < epsilon)
    (hp_nonneg : 0 ≤ p)
    (hmass : epsilon ≤ intervalMass)
    (htail_lower : intervalMass * p ≤ tailMass)
    (htail_small : tailMass < epsilon ^ 2) :
    p < epsilon :=
  theorem1_lowValue_pointwise_of_tail_mass_bound
    hepsilon_pos
    (le_trans (mul_le_mul_of_nonneg_right hmass hp_nonneg) htail_lower)
    htail_small

/--
High-value analogue of the tail-mass step: if an interval/tail-mass argument
upper-bounds `epsilon * (1 - p)`, then the pointwise match probability is
above `1 - epsilon`.
-/
theorem theorem1_highValue_pointwise_of_unmatched_tail_mass_bound
    {p epsilon tailMass : ℝ}
    (hepsilon_pos : 0 < epsilon)
    (htail_lower : epsilon * (1 - p) ≤ tailMass)
    (htail_small : tailMass < epsilon ^ 2) :
    1 - epsilon < p := by
  have hmul_lt : epsilon * (1 - p) < epsilon * epsilon := by
    nlinarith [htail_lower, htail_small]
  have hfail_lt : 1 - p < epsilon :=
    by nlinarith [hmul_lt, hepsilon_pos]
  linarith

/--
High-value unmatched-tail step with the interval-mass lower bound visible.
This is the symmetric source argument: an interval of mass at least `epsilon`
and a nonnegative endpoint failure probability give the lower bound
`epsilon * (1 - p)` on unmatched tail mass.
-/
theorem theorem1_highValue_pointwise_of_interval_unmatched_tail_mass_bound
    {p epsilon intervalMass tailMass : ℝ}
    (hepsilon_pos : 0 < epsilon)
    (hfailure_nonneg : 0 ≤ 1 - p)
    (hmass : epsilon ≤ intervalMass)
    (htail_lower : intervalMass * (1 - p) ≤ tailMass)
    (htail_small : tailMass < epsilon ^ 2) :
    1 - epsilon < p :=
  theorem1_highValue_pointwise_of_unmatched_tail_mass_bound
    hepsilon_pos
    (le_trans
      (mul_le_mul_of_nonneg_right hmass hfailure_nonneg)
      htail_lower)
    htail_small

/--
Uniform low-value tail-mass bridge for Theorem 1.  Once the source proof
provides a uniformly small matched-mass tail whose lower bound is
`epsilon * matchProb`, the below-threshold pointwise bound follows uniformly
over all admissible stable matchings.
-/
theorem theorem1_uniform_lowValue_eventually_of_tail_mass_bound
    {Admissible : ℕ → Type*}
    {matchProb : ∀ C, Admissible C → ℝ → ℝ}
    {tailMass : ∀ C, Admissible C → ℝ}
    {v epsilon : ℝ}
    (hepsilon_pos : 0 < epsilon)
    (htail_small :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C, tailMass C μ < epsilon ^ 2)
    (htail_lower :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          epsilon * matchProb C μ v ≤ tailMass C μ) :
    ∀ᶠ C : ℕ in atTop,
      ∀ μ : Admissible C, matchProb C μ v < epsilon := by
  filter_upwards [htail_small, htail_lower] with C hsmall hlower μ
  exact
    theorem1_lowValue_pointwise_of_tail_mass_bound
      hepsilon_pos (hlower μ) (hsmall μ)

/--
Uniform high-value tail-mass bridge for Theorem 1.  Once the source proof
provides a uniformly small unmatched-mass tail whose lower bound is
`epsilon * (1 - matchProb)`, the above-threshold pointwise bound follows
uniformly over all admissible stable matchings.
-/
theorem theorem1_uniform_highValue_eventually_of_unmatched_tail_mass_bound
    {Admissible : ℕ → Type*}
    {matchProb : ∀ C, Admissible C → ℝ → ℝ}
    {tailMass : ∀ C, Admissible C → ℝ}
    {v epsilon : ℝ}
    (hepsilon_pos : 0 < epsilon)
    (htail_small :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C, tailMass C μ < epsilon ^ 2)
    (htail_lower :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          epsilon * (1 - matchProb C μ v) ≤ tailMass C μ) :
    ∀ᶠ C : ℕ in atTop,
      ∀ μ : Admissible C, 1 - epsilon < matchProb C μ v := by
  filter_upwards [htail_small, htail_lower] with C hsmall hlower μ
  exact
    theorem1_highValue_pointwise_of_unmatched_tail_mass_bound
      hepsilon_pos (hlower μ) (hsmall μ)

/--
Uniform low-value interval-mass bridge for Theorem 1.  This keeps the source
interval mass visible: an interval of value mass at least `epsilon`, together
with nonnegativity of the endpoint match probability, gives the lower bound
needed by the tail-mass step.
-/
theorem theorem1_uniform_lowValue_eventually_of_interval_tail_mass_bound
    {Admissible : ℕ → Type*}
    {matchProb : ∀ C, Admissible C → ℝ → ℝ}
    {intervalMass tailMass : ∀ C, Admissible C → ℝ}
    {v epsilon : ℝ}
    (hepsilon_pos : 0 < epsilon)
    (hprob_nonneg :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C, 0 ≤ matchProb C μ v)
    (hmass :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C, epsilon ≤ intervalMass C μ)
    (htail_lower :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          intervalMass C μ * matchProb C μ v ≤ tailMass C μ)
    (htail_small :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C, tailMass C μ < epsilon ^ 2) :
    ∀ᶠ C : ℕ in atTop,
      ∀ μ : Admissible C, matchProb C μ v < epsilon := by
  filter_upwards [hprob_nonneg, hmass, htail_lower, htail_small] with
    C hnonnegC hmassC hlowerC hsmallC μ
  exact
    theorem1_lowValue_pointwise_of_interval_tail_mass_bound
      hepsilon_pos (hnonnegC μ) (hmassC μ) (hlowerC μ) (hsmallC μ)

/--
Uniform high-value interval-mass bridge for Theorem 1.  This is the symmetric
source step for unmatched mass above the threshold.
-/
theorem theorem1_uniform_highValue_eventually_of_interval_unmatched_tail_mass_bound
    {Admissible : ℕ → Type*}
    {matchProb : ∀ C, Admissible C → ℝ → ℝ}
    {intervalMass tailMass : ∀ C, Admissible C → ℝ}
    {v epsilon : ℝ}
    (hepsilon_pos : 0 < epsilon)
    (hfailure_nonneg :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C, 0 ≤ 1 - matchProb C μ v)
    (hmass :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C, epsilon ≤ intervalMass C μ)
    (htail_lower :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          intervalMass C μ * (1 - matchProb C μ v) ≤ tailMass C μ)
    (htail_small :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C, tailMass C μ < epsilon ^ 2) :
    ∀ᶠ C : ℕ in atTop,
      ∀ μ : Admissible C, 1 - epsilon < matchProb C μ v := by
  filter_upwards [hfailure_nonneg, hmass, htail_lower, htail_small] with
    C hnonnegC hmassC hlowerC hsmallC μ
  exact
    theorem1_highValue_pointwise_of_interval_unmatched_tail_mass_bound
      hepsilon_pos (hnonnegC μ) (hmassC μ) (hlowerC μ) (hsmallC μ)

/--
Theorem 1 attenuation from the paper's tail-mass proof route.  This packages
the source argument that low-value matched mass and high-value unmatched mass
can be made uniformly smaller than `epsilon^2`; the preceding algebraic lemmas
turn those mass estimates into the pointwise match-probability conclusion.
-/
theorem theorem1_uniformAttenuation_of_tail_mass_bounds
    {Admissible : ℕ → Type*} {matchProb : ∀ C, Admissible C → ℝ → ℝ}
    {vS : ℝ}
    (hlow :
      ∀ v epsilon, v < vS → 0 < epsilon →
        ∃ tailMass : ∀ C : ℕ, Admissible C → ℝ,
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, tailMass C μ < epsilon ^ 2) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              epsilon * matchProb C μ v ≤ tailMass C μ))
    (hhigh :
      ∀ v epsilon, vS < v → 0 < epsilon →
        ∃ tailMass : ∀ C : ℕ, Admissible C → ℝ,
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, tailMass C μ < epsilon ^ 2) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              epsilon * (1 - matchProb C μ v) ≤ tailMass C μ)) :
    theorem1_uniformAttenuationConclusion Admissible matchProb vS := by
  constructor
  · intro v epsilon hv hepsilon
    rcases hlow v epsilon hv hepsilon with ⟨tailMass, hsmall, hlower⟩
    exact
      theorem1_uniform_lowValue_eventually_of_tail_mass_bound
        (Admissible := Admissible)
        (matchProb := matchProb)
        (tailMass := tailMass)
        (v := v)
        hepsilon hsmall hlower
  · intro v epsilon hv hepsilon
    rcases hhigh v epsilon hv hepsilon with ⟨tailMass, hsmall, hlower⟩
    exact
      theorem1_uniform_highValue_eventually_of_unmatched_tail_mass_bound
        (Admissible := Admissible)
        (matchProb := matchProb)
        (tailMass := tailMass)
        (v := v)
        hepsilon hsmall hlower

/--
Theorem 1 attenuation from the source interval-mass route.  This is the
paper-facing refinement of `theorem1_uniformAttenuation_of_tail_mass_bounds`:
the interval mass, endpoint nonnegativity, and interval-to-tail lower bound
are all explicit proof obligations.
-/
theorem theorem1_uniformAttenuation_of_interval_tail_mass_bounds
    {Admissible : ℕ → Type*} {matchProb : ∀ C, Admissible C → ℝ → ℝ}
    {vS : ℝ}
    (hlow :
      ∀ v epsilon, v < vS → 0 < epsilon →
        ∃ intervalMass tailMass : ∀ C : ℕ, Admissible C → ℝ,
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, 0 ≤ matchProb C μ v) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, epsilon ≤ intervalMass C μ) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              intervalMass C μ * matchProb C μ v ≤ tailMass C μ) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, tailMass C μ < epsilon ^ 2))
    (hhigh :
      ∀ v epsilon, vS < v → 0 < epsilon →
        ∃ intervalMass tailMass : ∀ C : ℕ, Admissible C → ℝ,
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, 0 ≤ 1 - matchProb C μ v) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, epsilon ≤ intervalMass C μ) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              intervalMass C μ * (1 - matchProb C μ v) ≤ tailMass C μ) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, tailMass C μ < epsilon ^ 2)) :
    theorem1_uniformAttenuationConclusion Admissible matchProb vS := by
  constructor
  · intro v epsilon hv hepsilon
    rcases hlow v epsilon hv hepsilon with
      ⟨intervalMass, tailMass, hnonneg, hmass, hlower, hsmall⟩
    exact
      theorem1_uniform_lowValue_eventually_of_interval_tail_mass_bound
        (Admissible := Admissible)
        (matchProb := matchProb)
        (intervalMass := intervalMass)
        (tailMass := tailMass)
        (v := v)
        hepsilon hnonneg hmass hlower hsmall
  · intro v epsilon hv hepsilon
    rcases hhigh v epsilon hv hepsilon with
      ⟨intervalMass, tailMass, hnonneg, hmass, hlower, hsmall⟩
    exact
      theorem1_uniform_highValue_eventually_of_interval_unmatched_tail_mass_bound
        (Admissible := Admissible)
        (matchProb := matchProb)
        (intervalMass := intervalMass)
        (tailMass := tailMass)
        (v := v)
        hepsilon hnonneg hmass hlower hsmall

/--
Theorem 1 attenuation from the source interval-mass route when the analytic
appendix proves a uniformly vanishing tail mass rather than directly proving
the target-dependent `epsilon^2` bound.  This matches the paper's Proposition
`thm1v2` style: once the relevant matched or unmatched interval tail mass
tends to zero uniformly over stable matchings, the existing interval-mass
algebra gives the pointwise attenuation theorem.
-/
theorem theorem1_uniformAttenuation_of_interval_tail_mass_tendsto_zero
    {Admissible : ℕ → Type*} {matchProb : ∀ C, Admissible C → ℝ → ℝ}
    {vS : ℝ}
    (hlow :
      ∀ v epsilon, v < vS → 0 < epsilon →
        ∃ intervalMass tailMass : ∀ C : ℕ, Admissible C → ℝ,
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, 0 ≤ matchProb C μ v) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, epsilon ≤ intervalMass C μ) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              intervalMass C μ * matchProb C μ v ≤ tailMass C μ) ∧
          (∀ tol : ℝ, 0 < tol →
            ∀ᶠ C : ℕ in atTop,
              ∀ μ : Admissible C, tailMass C μ < tol))
    (hhigh :
      ∀ v epsilon, vS < v → 0 < epsilon →
        ∃ intervalMass tailMass : ∀ C : ℕ, Admissible C → ℝ,
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, 0 ≤ 1 - matchProb C μ v) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, epsilon ≤ intervalMass C μ) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              intervalMass C μ * (1 - matchProb C μ v) ≤ tailMass C μ) ∧
          (∀ tol : ℝ, 0 < tol →
            ∀ᶠ C : ℕ in atTop,
              ∀ μ : Admissible C, tailMass C μ < tol)) :
    theorem1_uniformAttenuationConclusion Admissible matchProb vS := by
  refine theorem1_uniformAttenuation_of_interval_tail_mass_bounds ?_ ?_
  · intro v epsilon hv hepsilon
    rcases hlow v epsilon hv hepsilon with
      ⟨intervalMass, tailMass, hnonneg, hmass, hlower, hvanish⟩
    exact
      ⟨intervalMass, tailMass, hnonneg, hmass, hlower,
        hvanish (epsilon ^ 2) (sq_pos_of_pos hepsilon)⟩
  · intro v epsilon hv hepsilon
    rcases hhigh v epsilon hv hepsilon with
      ⟨intervalMass, tailMass, hnonneg, hmass, hlower, hvanish⟩
    exact
      ⟨intervalMass, tailMass, hnonneg, hmass, hlower,
        hvanish (epsilon ^ 2) (sq_pos_of_pos hepsilon)⟩

/--
Theorem 1 attenuation from source-style polynomial tail-mass estimates.  The
attenuation appendix proves bounds of the form `O(C^{-K})`; this theorem turns
those uniform negative-power bounds into the vanishing-tail-mass obligations
used by the interval-mass bridge.
-/
theorem theorem1_uniformAttenuation_of_interval_tail_mass_polynomial_bound
    {Admissible : ℕ → Type*} {matchProb : ∀ C, Admissible C → ℝ → ℝ}
    {vS : ℝ}
    (hlow :
      ∀ v epsilon, v < vS → 0 < epsilon →
        ∃ intervalMass tailMass : ∀ C : ℕ, Admissible C → ℝ,
        ∃ A rate : ℝ, ∃ N0 : ℕ,
          0 < rate ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, 0 ≤ matchProb C μ v) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, epsilon ≤ intervalMass C μ) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              intervalMass C μ * matchProb C μ v ≤ tailMass C μ) ∧
          (∀ C : ℕ, N0 ≤ C →
            ∀ μ : Admissible C,
              tailMass C μ ≤
                A * Real.rpow (((C + 1 : ℕ) : ℝ)) (-rate)))
    (hhigh :
      ∀ v epsilon, vS < v → 0 < epsilon →
        ∃ intervalMass tailMass : ∀ C : ℕ, Admissible C → ℝ,
        ∃ A rate : ℝ, ∃ N0 : ℕ,
          0 < rate ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, 0 ≤ 1 - matchProb C μ v) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, epsilon ≤ intervalMass C μ) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              intervalMass C μ * (1 - matchProb C μ v) ≤ tailMass C μ) ∧
          (∀ C : ℕ, N0 ≤ C →
            ∀ μ : Admissible C,
              tailMass C μ ≤
                A * Real.rpow (((C + 1 : ℕ) : ℝ)) (-rate))) :
    theorem1_uniformAttenuationConclusion Admissible matchProb vS := by
  refine theorem1_uniformAttenuation_of_interval_tail_mass_tendsto_zero ?_ ?_
  · intro v epsilon hv hepsilon
    rcases hlow v epsilon hv hepsilon with
      ⟨intervalMass, tailMass, A, rate, N0,
        hrate, hnonneg, hmass, hlower, hbound⟩
    refine ⟨intervalMass, tailMass, hnonneg, hmass, hlower, ?_⟩
    exact
      pg24_eventually_forall_lt_of_uniform_rpow_neg_bound
        (α := Admissible) (f := tailMass)
        hrate hbound
  · intro v epsilon hv hepsilon
    rcases hhigh v epsilon hv hepsilon with
      ⟨intervalMass, tailMass, A, rate, N0,
        hrate, hnonneg, hmass, hlower, hbound⟩
    refine ⟨intervalMass, tailMass, hnonneg, hmass, hlower, ?_⟩
    exact
      pg24_eventually_forall_lt_of_uniform_rpow_neg_bound
        (α := Admissible) (f := tailMass)
        hrate hbound

/--
Cutoff-probability specialization of the polynomial interval-tail route for
Theorem 1.  In this source-shaped form the paper proof supplies the interval
mass and tail-mass estimates; Lean derives the probability nonnegativity and
`≤ 1` bounds from the concrete cutoff-affordance probability definition.
-/
theorem theorem1_uniformAttenuation_of_cutoff_interval_tail_mass_polynomial_bound
    {Admissible : ℕ → Type*}
    {sampleLaw : ∀ C : ℕ, Measure (Fin (C + 1) → ℝ)}
    {active : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    {cutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ}
    {vS : ℝ}
    (hprob : ∀ C : ℕ, IsProbabilityMeasure (sampleLaw C))
    (hlow :
      ∀ v epsilon, v < vS → 0 < epsilon →
        ∃ intervalMass tailMass : ∀ C : ℕ, Admissible C → ℝ,
        ∃ A rate : ℝ, ∃ N0 : ℕ,
          0 < rate ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, epsilon ≤ intervalMass C μ) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              intervalMass C μ *
                  cutoffAffordanceProbability
                    (sampleLaw C) (active C μ) v (cutoff C μ) ≤
                tailMass C μ) ∧
          (∀ C : ℕ, N0 ≤ C →
            ∀ μ : Admissible C,
              tailMass C μ ≤
                A * Real.rpow (((C + 1 : ℕ) : ℝ)) (-rate)))
    (hhigh :
      ∀ v epsilon, vS < v → 0 < epsilon →
        ∃ intervalMass tailMass : ∀ C : ℕ, Admissible C → ℝ,
        ∃ A rate : ℝ, ∃ N0 : ℕ,
          0 < rate ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, epsilon ≤ intervalMass C μ) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              intervalMass C μ *
                  (1 - cutoffAffordanceProbability
                    (sampleLaw C) (active C μ) v (cutoff C μ)) ≤
                tailMass C μ) ∧
          (∀ C : ℕ, N0 ≤ C →
            ∀ μ : Admissible C,
              tailMass C μ ≤
                A * Real.rpow (((C + 1 : ℕ) : ℝ)) (-rate))) :
    theorem1_uniformAttenuationConclusion
      Admissible
      (fun C : ℕ => fun μ : Admissible C => fun v : ℝ =>
        cutoffAffordanceProbability
          (sampleLaw C) (active C μ) v (cutoff C μ))
      vS := by
  refine theorem1_uniformAttenuation_of_interval_tail_mass_polynomial_bound ?_ ?_
  · intro v epsilon hv hepsilon
    rcases hlow v epsilon hv hepsilon with
      ⟨intervalMass, tailMass, A, rate, N0, hrate, hmass, hlower, hbound⟩
    refine ⟨intervalMass, tailMass, A, rate, N0, hrate, ?_, hmass, hlower, hbound⟩
    filter_upwards with C μ
    exact
      cutoffAffordanceProbability_nonneg
        (sampleLaw C) (active C μ) v (cutoff C μ)
  · intro v epsilon hv hepsilon
    rcases hhigh v epsilon hv hepsilon with
      ⟨intervalMass, tailMass, A, rate, N0, hrate, hmass, hlower, hbound⟩
    refine ⟨intervalMass, tailMass, A, rate, N0, hrate, ?_, hmass, hlower, hbound⟩
    filter_upwards with C μ
    haveI : IsProbabilityMeasure (sampleLaw C) := hprob C
    have hle :
        cutoffAffordanceProbability
          (sampleLaw C) (active C μ) v (cutoff C μ) ≤ 1 :=
      cutoffAffordanceProbability_le_one
        (sampleLaw C) (active C μ) v (cutoff C μ)
    linarith

/--
Uniform version of the clean cutoff-sandwich attenuation route.  If every
admissible stable matching has a cutoff vector uniformly squeezed between
lower and upper threshold sequences whose expected-maximum gaps both converge
to `vS`, then PG24 Theorem 1's uniform-in-`mu` attenuation conclusion follows
directly from maximum-order-statistic concentration.
-/
theorem theorem1_uniformAttenuation_of_expected_max_cutoff_sandwich
    {Admissible : ℕ → Type*}
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {lowerCutoff upperCutoff : ℕ → ℝ}
    {cutoff : ∀ n : ℕ, Admissible n → Fin (n + 1) → ℝ}
    {vS : ℝ}
    (hprob : ∀ n, IsProbabilityMeasure (sampleLaw n))
    (hconc : maximumOrderStatisticConcentrating sampleLaw)
    (hlower :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n, ∀ c : Fin (n + 1),
          lowerCutoff n ≤ cutoff n μ c)
    (hupper :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n, ∀ c : Fin (n + 1),
          cutoff n μ c ≤ upperCutoff n)
    (hlower_threshold :
      Tendsto
        (fun n : ℕ =>
          lowerCutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
        atTop (nhds vS))
    (hupper_threshold :
      Tendsto
        (fun n : ℕ =>
          upperCutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
        atTop (nhds vS)) :
    theorem1_uniformAttenuationConclusion
      Admissible
      (fun n : ℕ => fun μ : Admissible n => fun v : ℝ =>
        cutoffAffordanceProbability (sampleLaw n)
          (Finset.univ : Finset (Fin (n + 1))) v (cutoff n μ))
      vS := by
  constructor
  · intro v tol hv htol
    let gap : ℝ := (vS - v) / 2
    have hgap_pos : 0 < gap := by
      dsimp [gap]
      linarith
    have htarget : v + gap < vS := by
      dsimp [gap]
      linarith
    have hnear :
        ∀ᶠ n : ℕ in atTop,
          v + gap <
            lowerCutoff n -
              AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n :=
      hlower_threshold (isOpen_Ioi.mem_nhds htarget)
    have hsep :
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n + gap ≤
            lowerCutoff n - v := by
      filter_upwards [hnear] with n hn
      linarith
    have hdev_small :
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Matching.topOrderDeviationProbability
              (sampleLaw n)
              (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
              gap < tol :=
      hconc gap hgap_pos (isOpen_Iio.mem_nhds htol)
    filter_upwards [hlower, hsep, hdev_small] with n hn_lower hn_sep hn_dev μ
    haveI : IsFiniteMeasure (sampleLaw n) := by
      haveI : IsProbabilityMeasure (sampleLaw n) := hprob n
      infer_instance
    exact
      lt_of_le_of_lt
        (cutoffAffordanceProbability_le_topOrderDeviationProbability_of_uniform_lower_cutoff
          (noiseLaw := sampleLaw n)
          (v := v) (P := lowerCutoff n)
          (center := AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
          (ε := gap)
          (cutoff := cutoff n μ)
          (fun c => hn_lower μ c) hn_sep)
        hn_dev
  · intro v tol hv htol
    let gap : ℝ := (v - vS) / 2
    have hgap_pos : 0 < gap := by
      dsimp [gap]
      linarith
    have htarget : vS < v - gap := by
      dsimp [gap]
      linarith
    have hnear :
        ∀ᶠ n : ℕ in atTop,
          upperCutoff n -
              AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n <
            v - gap :=
      hupper_threshold (isOpen_Iio.mem_nhds htarget)
    have hsep :
        ∀ᶠ n : ℕ in atTop,
          upperCutoff n - v <
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n - gap := by
      filter_upwards [hnear] with n hn
      linarith
    have hdev_small :
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Matching.topOrderDeviationProbability
              (sampleLaw n)
              (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
              gap < tol :=
      hconc gap hgap_pos (isOpen_Iio.mem_nhds htol)
    filter_upwards [hupper, hsep, hdev_small] with n hn_upper hn_sep hn_dev μ
    haveI : IsProbabilityMeasure (sampleLaw n) := hprob n
    have hfail_le :
        1 -
          cutoffAffordanceProbability (sampleLaw n)
            (Finset.univ : Finset (Fin (n + 1))) v (cutoff n μ) ≤
          AppliedModelingLib.Matching.topOrderDeviationProbability
            (sampleLaw n)
            (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
            gap :=
      one_sub_cutoffAffordanceProbability_le_topOrderDeviationProbability_of_uniform_upper_cutoff
        (noiseLaw := sampleLaw n)
        (v := v) (P := upperCutoff n)
        (center := AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
        (ε := gap)
        (cutoff := cutoff n μ)
        (fun c => hn_upper μ c) hgap_pos hn_sep
    linarith

/--
Uniform Theorem 1 route over stable matchings themselves.

For each finite market size, A-L Lemma 1 selects a market-clearing cutoff
representing the stable matching.  If all market-clearing cutoffs are
eventually squeezed between lower and upper expected-maximum thresholds, then
the uniform attenuation conclusion holds for every stable matching.
-/
theorem theorem1_uniformAttenuation_of_expected_max_stable_cutoff_sandwich
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ n : ℕ, CutoffMarket (StudentSeq n) (Fin (n + 1)))
    (Iseq : ∀ n : ℕ, SupplyDemandInterface (Mseq n))
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {lowerCutoff upperCutoff : ℕ → ℝ}
    (cutoffOut : ∀ n : ℕ, (Mseq n).Cutoff → Fin (n + 1) → ℝ)
    {vS : ℝ}
    (hprob : ∀ n, IsProbabilityMeasure (sampleLaw n))
    (hconc : maximumOrderStatisticConcentrating sampleLaw)
    (hlower_market :
      ∀ᶠ n : ℕ in atTop,
        ∀ P : (Mseq n).Cutoff, (Mseq n).MarketClearing P →
          ∀ c : Fin (n + 1), lowerCutoff n ≤ cutoffOut n P c)
    (hupper_market :
      ∀ᶠ n : ℕ in atTop,
        ∀ P : (Mseq n).Cutoff, (Mseq n).MarketClearing P →
          ∀ c : Fin (n + 1), cutoffOut n P c ≤ upperCutoff n)
    (hlower_threshold :
      Tendsto
        (fun n : ℕ =>
          lowerCutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
        atTop (nhds vS))
    (hupper_threshold :
      Tendsto
        (fun n : ℕ =>
          upperCutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
        atTop (nhds vS)) :
    theorem1_uniformAttenuationConclusion
      (fun n : ℕ => { μ : (Mseq n).Matching // (Mseq n).Stable μ })
      (fun n : ℕ =>
        fun μ : { μ : (Mseq n).Matching // (Mseq n).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability (sampleLaw n)
            (Finset.univ : Finset (Fin (n + 1))) v
            (cutoffOut n
              ((Iseq n).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      vS := by
  have hlower :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : { μ : (Mseq n).Matching // (Mseq n).Stable μ },
          ∀ c : Fin (n + 1),
            lowerCutoff n ≤
              cutoffOut n
                ((Iseq n).marketClearingCutoffOfStable (μ := μ.1) μ.2) c := by
    filter_upwards [hlower_market] with n hn μ c
    exact
      hn _ ((Iseq n).marketClearingCutoffOfStable_marketClearing
        (μ := μ.1) μ.2) c
  have hupper :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : { μ : (Mseq n).Matching // (Mseq n).Stable μ },
          ∀ c : Fin (n + 1),
            cutoffOut n
                ((Iseq n).marketClearingCutoffOfStable (μ := μ.1) μ.2) c ≤
              upperCutoff n := by
    filter_upwards [hupper_market] with n hn μ c
    exact
      hn _ ((Iseq n).marketClearingCutoffOfStable_marketClearing
        (μ := μ.1) μ.2) c
  exact
    theorem1_uniformAttenuation_of_expected_max_cutoff_sandwich
      (Admissible := fun n : ℕ =>
        { μ : (Mseq n).Matching // (Mseq n).Stable μ })
      (sampleLaw := sampleLaw)
      (lowerCutoff := lowerCutoff) (upperCutoff := upperCutoff)
      (cutoff := fun n μ =>
        cutoffOut n
          ((Iseq n).marketClearingCutoffOfStable (μ := μ.1) μ.2))
      (vS := vS)
      hprob hconc hlower hupper hlower_threshold hupper_threshold

/--
Theorem 1 source route from the paper's β-max-concentrating variance
definition.  The variance rate gives vanishing variance, Chebyshev gives
maximum-order-statistic concentration, and the cutoff-sandwich estimate gives
the uniform attenuation conclusion.
-/
theorem theorem1_uniformAttenuation_of_betaMax_variance_cutoff_sandwich
    {Admissible : ℕ → Type*}
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {maxVariance lowerCutoff upperCutoff : ℕ → ℝ}
    {cutoff : ∀ n : ℕ, Admissible n → Fin (n + 1) → ℝ}
    {β vS : ℝ}
    (hprob : ∀ n, IsProbabilityMeasure (sampleLaw n))
    (hbeta : betaMaxConcentratingVariance maxVariance β)
    (hchebyshev :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
              (sampleLaw n)
              (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
              ε ≤
            maxVariance n / ε ^ 2)
    (hlower :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n, ∀ c : Fin (n + 1),
          lowerCutoff n ≤ cutoff n μ c)
    (hupper :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n, ∀ c : Fin (n + 1),
          cutoff n μ c ≤ upperCutoff n)
    (hlower_threshold :
      Tendsto
        (fun n : ℕ =>
          lowerCutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
        atTop (nhds vS))
    (hupper_threshold :
      Tendsto
        (fun n : ℕ =>
          upperCutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
        atTop (nhds vS)) :
    theorem1_uniformAttenuationConclusion
      Admissible
      (fun n : ℕ => fun μ : Admissible n => fun v : ℝ =>
        cutoffAffordanceProbability (sampleLaw n)
          (Finset.univ : Finset (Fin (n + 1))) v (cutoff n μ))
      vS := by
  exact
    theorem1_uniformAttenuation_of_expected_max_cutoff_sandwich
      (Admissible := Admissible)
      (sampleLaw := sampleLaw)
      (lowerCutoff := lowerCutoff)
      (upperCutoff := upperCutoff)
      (cutoff := cutoff)
      (vS := vS)
      hprob
      (maximumOrderStatisticConcentrating_of_chebyshev_variance_bound
        (betaMaxConcentratingVariance.tendsto_zero_of_chebyshev
          (sampleLaw := sampleLaw) hbeta hchebyshev)
        hchebyshev)
      hlower hupper hlower_threshold hupper_threshold

/--
Theorem 1 source route from an actual variance bound on the maximum order
statistic.  This is the preferred PG24 route: `maxVariance` is tied directly
to the variance of `X^(n+1)`, and Chebyshev is supplied by the shared
order-statistics library.
-/
theorem theorem1_uniformAttenuation_of_betaMax_variance_bound_cutoff_sandwich
    {Admissible : ℕ → Type*}
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {maxVariance lowerCutoff upperCutoff : ℕ → ℝ}
    {cutoff : ∀ n : ℕ, Admissible n → Fin (n + 1) → ℝ}
    {β vS : ℝ}
    (hprob : ∀ n, IsProbabilityMeasure (sampleLaw n))
    (hbeta : betaMaxConcentratingVariance maxVariance β)
    (hmem :
      ∀ᶠ n : ℕ in atTop,
        MemLp
          (fun sample : Fin (n + 1) → ℝ =>
            AppliedModelingLib.Probability.upperOrderStatistic sample
              (AppliedModelingLib.Probability.topSampleRank (n := n + 1))) 2
          (sampleLaw n))
    (hvariance_bound :
      ∀ᶠ n : ℕ in atTop,
        ProbabilityTheory.variance
          (fun sample : Fin (n + 1) → ℝ =>
            AppliedModelingLib.Probability.upperOrderStatistic sample
              (AppliedModelingLib.Probability.topSampleRank (n := n + 1)))
          (sampleLaw n) ≤ maxVariance n)
    (hlower :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n, ∀ c : Fin (n + 1),
          lowerCutoff n ≤ cutoff n μ c)
    (hupper :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n, ∀ c : Fin (n + 1),
          cutoff n μ c ≤ upperCutoff n)
    (hlower_threshold :
      Tendsto
        (fun n : ℕ =>
          lowerCutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
        atTop (nhds vS))
    (hupper_threshold :
      Tendsto
        (fun n : ℕ =>
          upperCutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
        atTop (nhds vS)) :
    theorem1_uniformAttenuationConclusion
      Admissible
      (fun n : ℕ => fun μ : Admissible n => fun v : ℝ =>
        cutoffAffordanceProbability (sampleLaw n)
          (Finset.univ : Finset (Fin (n + 1))) v (cutoff n μ))
      vS := by
  exact
    theorem1_uniformAttenuation_of_expected_max_cutoff_sandwich
      (Admissible := Admissible)
      (sampleLaw := sampleLaw)
      (lowerCutoff := lowerCutoff)
      (upperCutoff := upperCutoff)
      (cutoff := cutoff)
      (vS := vS)
      hprob
      (maximumOrderStatisticConcentrating_of_variance_bound
        hprob
        (betaMaxConcentratingVariance.tendsto_zero_of_variance_bound
          (sampleLaw := sampleLaw) hbeta hvariance_bound)
        hmem hvariance_bound)
      hlower hupper hlower_threshold hupper_threshold

/--
Theorem 1 source route over stable matchings from the paper's
β-max-concentrating variance definition.  This combines the A-L
stable-to-cutoff bridge with the β-max/Chebyshev concentration route, so the
stable-matching theorem surface does not expose a separate concentration
predicate.
-/
theorem theorem1_uniformAttenuation_of_betaMax_variance_stable_cutoff_sandwich
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ n : ℕ, CutoffMarket (StudentSeq n) (Fin (n + 1)))
    (Iseq : ∀ n : ℕ, SupplyDemandInterface (Mseq n))
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {maxVariance lowerCutoff upperCutoff : ℕ → ℝ}
    (cutoffOut : ∀ n : ℕ, (Mseq n).Cutoff → Fin (n + 1) → ℝ)
    {β vS : ℝ}
    (hprob : ∀ n, IsProbabilityMeasure (sampleLaw n))
    (hbeta : betaMaxConcentratingVariance maxVariance β)
    (hchebyshev :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
              (sampleLaw n)
              (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
              ε ≤
            maxVariance n / ε ^ 2)
    (hlower_market :
      ∀ᶠ n : ℕ in atTop,
        ∀ P : (Mseq n).Cutoff, (Mseq n).MarketClearing P →
          ∀ c : Fin (n + 1), lowerCutoff n ≤ cutoffOut n P c)
    (hupper_market :
      ∀ᶠ n : ℕ in atTop,
        ∀ P : (Mseq n).Cutoff, (Mseq n).MarketClearing P →
          ∀ c : Fin (n + 1), cutoffOut n P c ≤ upperCutoff n)
    (hlower_threshold :
      Tendsto
        (fun n : ℕ =>
          lowerCutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
        atTop (nhds vS))
    (hupper_threshold :
      Tendsto
        (fun n : ℕ =>
          upperCutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
        atTop (nhds vS)) :
    theorem1_uniformAttenuationConclusion
      (fun n : ℕ => { μ : (Mseq n).Matching // (Mseq n).Stable μ })
      (fun n : ℕ =>
        fun μ : { μ : (Mseq n).Matching // (Mseq n).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability (sampleLaw n)
            (Finset.univ : Finset (Fin (n + 1))) v
            (cutoffOut n
              ((Iseq n).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      vS :=
  theorem1_uniformAttenuation_of_expected_max_stable_cutoff_sandwich
    Mseq Iseq cutoffOut hprob
    (maximumOrderStatisticConcentrating_of_chebyshev_variance_bound
      (betaMaxConcentratingVariance.tendsto_zero_of_chebyshev
        (sampleLaw := sampleLaw) hbeta hchebyshev)
      hchebyshev)
    hlower_market hupper_market hlower_threshold hupper_threshold

/--
Theorem 1 source route over stable matchings from an actual variance bound on
the maximum order statistic.  This keeps the stable-matching surface and the
variance-rate surface paper-facing while deriving Chebyshev internally.
-/
theorem theorem1_uniformAttenuation_of_betaMax_variance_bound_stable_cutoff_sandwich
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ n : ℕ, CutoffMarket (StudentSeq n) (Fin (n + 1)))
    (Iseq : ∀ n : ℕ, SupplyDemandInterface (Mseq n))
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {maxVariance lowerCutoff upperCutoff : ℕ → ℝ}
    (cutoffOut : ∀ n : ℕ, (Mseq n).Cutoff → Fin (n + 1) → ℝ)
    {β vS : ℝ}
    (hprob : ∀ n, IsProbabilityMeasure (sampleLaw n))
    (hbeta : betaMaxConcentratingVariance maxVariance β)
    (hmem :
      ∀ᶠ n : ℕ in atTop,
        MemLp
          (fun sample : Fin (n + 1) → ℝ =>
            AppliedModelingLib.Probability.upperOrderStatistic sample
              (AppliedModelingLib.Probability.topSampleRank (n := n + 1))) 2
          (sampleLaw n))
    (hvariance_bound :
      ∀ᶠ n : ℕ in atTop,
        ProbabilityTheory.variance
          (fun sample : Fin (n + 1) → ℝ =>
            AppliedModelingLib.Probability.upperOrderStatistic sample
              (AppliedModelingLib.Probability.topSampleRank (n := n + 1)))
          (sampleLaw n) ≤ maxVariance n)
    (hlower_market :
      ∀ᶠ n : ℕ in atTop,
        ∀ P : (Mseq n).Cutoff, (Mseq n).MarketClearing P →
          ∀ c : Fin (n + 1), lowerCutoff n ≤ cutoffOut n P c)
    (hupper_market :
      ∀ᶠ n : ℕ in atTop,
        ∀ P : (Mseq n).Cutoff, (Mseq n).MarketClearing P →
          ∀ c : Fin (n + 1), cutoffOut n P c ≤ upperCutoff n)
    (hlower_threshold :
      Tendsto
        (fun n : ℕ =>
          lowerCutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
        atTop (nhds vS))
    (hupper_threshold :
      Tendsto
        (fun n : ℕ =>
          upperCutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
        atTop (nhds vS)) :
    theorem1_uniformAttenuationConclusion
      (fun n : ℕ => { μ : (Mseq n).Matching // (Mseq n).Stable μ })
      (fun n : ℕ =>
        fun μ : { μ : (Mseq n).Matching // (Mseq n).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability (sampleLaw n)
            (Finset.univ : Finset (Fin (n + 1))) v
            (cutoffOut n
              ((Iseq n).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      vS :=
  theorem1_uniformAttenuation_of_expected_max_stable_cutoff_sandwich
    Mseq Iseq cutoffOut hprob
    (maximumOrderStatisticConcentrating_of_variance_bound
      hprob
      (betaMaxConcentratingVariance.tendsto_zero_of_variance_bound
        (sampleLaw := sampleLaw) hbeta hvariance_bound)
      hmem hvariance_bound)
    hlower_market hupper_market hlower_threshold hupper_threshold

/--
Theorem 1 source clauses.  This projection makes the final paper-facing
statement explicit: below the threshold every stable matching's match
probability is eventually small, and above the threshold it is eventually
within epsilon of one.
-/
theorem theorem1_uniformAttenuation_source_clauses
    {Admissible : ℕ → Type*} {matchProb : ∀ C, Admissible C → ℝ → ℝ}
    {vS : ℝ}
    (h : theorem1_uniformAttenuationConclusion Admissible matchProb vS) :
    (∀ v ε, v < vS → 0 < ε →
      ∀ᶠ C : ℕ in atTop, ∀ μ : Admissible C, matchProb C μ v < ε) ∧
    (∀ v ε, vS < v → 0 < ε →
      ∀ᶠ C : ℕ in atTop, ∀ μ : Admissible C, 1 - ε < matchProb C μ v) :=
  h

/--
Preferred Theorem 1 stable-matching route, stated directly as source clauses.
This composes the A-L stable-to-cutoff bridge, the source beta-max variance
condition with an actual variance bound for the maximum order statistic, and
the cutoff-sandwich estimates, then exposes the two eventual probability
clauses from the paper.
-/
theorem theorem1_uniformAttenuation_source_clauses_of_betaMax_variance_bound_stable_cutoff_sandwich
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ n : ℕ, CutoffMarket (StudentSeq n) (Fin (n + 1)))
    (Iseq : ∀ n : ℕ, SupplyDemandInterface (Mseq n))
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {maxVariance lowerCutoff upperCutoff : ℕ → ℝ}
    (cutoffOut : ∀ n : ℕ, (Mseq n).Cutoff → Fin (n + 1) → ℝ)
    {β vS : ℝ}
    (hprob : ∀ n, IsProbabilityMeasure (sampleLaw n))
    (hbeta : betaMaxConcentratingVariance maxVariance β)
    (hmem :
      ∀ᶠ n : ℕ in atTop,
        MemLp
          (fun sample : Fin (n + 1) → ℝ =>
            AppliedModelingLib.Probability.upperOrderStatistic sample
              (AppliedModelingLib.Probability.topSampleRank (n := n + 1))) 2
          (sampleLaw n))
    (hvariance_bound :
      ∀ᶠ n : ℕ in atTop,
        ProbabilityTheory.variance
          (fun sample : Fin (n + 1) → ℝ =>
            AppliedModelingLib.Probability.upperOrderStatistic sample
              (AppliedModelingLib.Probability.topSampleRank (n := n + 1)))
          (sampleLaw n) ≤ maxVariance n)
    (hlower_market :
      ∀ᶠ n : ℕ in atTop,
        ∀ P : (Mseq n).Cutoff, (Mseq n).MarketClearing P →
          ∀ c : Fin (n + 1), lowerCutoff n ≤ cutoffOut n P c)
    (hupper_market :
      ∀ᶠ n : ℕ in atTop,
        ∀ P : (Mseq n).Cutoff, (Mseq n).MarketClearing P →
          ∀ c : Fin (n + 1), cutoffOut n P c ≤ upperCutoff n)
    (hlower_threshold :
      Tendsto
        (fun n : ℕ =>
          lowerCutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
        atTop (nhds vS))
    (hupper_threshold :
      Tendsto
        (fun n : ℕ =>
          upperCutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
        atTop (nhds vS)) :
    (∀ v ε, v < vS → 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          cutoffAffordanceProbability (sampleLaw C)
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)) <
            ε) ∧
    (∀ v ε, vS < v → 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          1 - ε <
            cutoffAffordanceProbability (sampleLaw C)
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))) := by
  exact
    theorem1_uniformAttenuation_source_clauses
      (theorem1_uniformAttenuation_of_betaMax_variance_bound_stable_cutoff_sandwich
        Mseq Iseq cutoffOut hprob hbeta hmem hvariance_bound
        hlower_market hupper_market hlower_threshold hupper_threshold)

/--
Preferred Theorem 1 source clauses with the cutoff sandwich required only at
the selected A-L cutoff attached to each stable matching.  This is the exact
surface needed for the paper statement: the conclusion quantifies over stable
matchings, so the endpoint cutoff estimates need not be assumed for unrelated
market-clearing cutoffs.
-/
theorem theorem1_uniformAttenuation_source_clauses_of_betaMax_variance_bound_selected_stable_cutoff_sandwich
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ n : ℕ, CutoffMarket (StudentSeq n) (Fin (n + 1)))
    (Iseq : ∀ n : ℕ, SupplyDemandInterface (Mseq n))
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {maxVariance lowerCutoff upperCutoff : ℕ → ℝ}
    (cutoffOut : ∀ n : ℕ, (Mseq n).Cutoff → Fin (n + 1) → ℝ)
    {β vS : ℝ}
    (hprob : ∀ n, IsProbabilityMeasure (sampleLaw n))
    (hbeta : betaMaxConcentratingVariance maxVariance β)
    (hmem :
      ∀ᶠ n : ℕ in atTop,
        MemLp
          (fun sample : Fin (n + 1) → ℝ =>
            AppliedModelingLib.Probability.upperOrderStatistic sample
              (AppliedModelingLib.Probability.topSampleRank (n := n + 1))) 2
          (sampleLaw n))
    (hvariance_bound :
      ∀ᶠ n : ℕ in atTop,
        ProbabilityTheory.variance
          (fun sample : Fin (n + 1) → ℝ =>
            AppliedModelingLib.Probability.upperOrderStatistic sample
              (AppliedModelingLib.Probability.topSampleRank (n := n + 1)))
          (sampleLaw n) ≤ maxVariance n)
    (hlower_selected :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : { μ : (Mseq n).Matching // (Mseq n).Stable μ },
          ∀ c : Fin (n + 1),
            lowerCutoff n ≤
              cutoffOut n
                ((Iseq n).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2) c)
    (hupper_selected :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : { μ : (Mseq n).Matching // (Mseq n).Stable μ },
          ∀ c : Fin (n + 1),
            cutoffOut n
                ((Iseq n).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2) c ≤
              upperCutoff n)
    (hlower_threshold :
      Tendsto
        (fun n : ℕ =>
          lowerCutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
        atTop (nhds vS))
    (hupper_threshold :
      Tendsto
        (fun n : ℕ =>
          upperCutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
        atTop (nhds vS)) :
    (∀ v ε, v < vS → 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          cutoffAffordanceProbability (sampleLaw C)
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)) <
            ε) ∧
    (∀ v ε, vS < v → 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          1 - ε <
            cutoffAffordanceProbability (sampleLaw C)
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))) := by
  exact
    theorem1_uniformAttenuation_source_clauses
      (theorem1_uniformAttenuation_of_betaMax_variance_bound_cutoff_sandwich
        (Admissible := fun n : ℕ =>
          { μ : (Mseq n).Matching // (Mseq n).Stable μ })
        (sampleLaw := sampleLaw)
        (maxVariance := maxVariance)
        (lowerCutoff := lowerCutoff)
        (upperCutoff := upperCutoff)
        (cutoff := fun n μ =>
          cutoffOut n
            ((Iseq n).marketClearingCutoffOfStable (μ := μ.1) μ.2))
        (β := β) (vS := vS)
        hprob hbeta hmem hvariance_bound
        hlower_selected hupper_selected hlower_threshold hupper_threshold)

/--
Preferred Theorem 1 source clauses in the paper's iid product-noise model.
This specializes the selected-stable cutoff-sandwich route from an abstract
sample law to `Measure.pi (fun _ => noiseLaw)`.
-/
theorem theorem1_uniformAttenuation_source_clauses_of_iidProduct_betaMax_variance_bound_selected_stable_cutoff_sandwich
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ n : ℕ, CutoffMarket (StudentSeq n) (Fin (n + 1)))
    (Iseq : ∀ n : ℕ, SupplyDemandInterface (Mseq n))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance lowerCutoff upperCutoff : ℕ → ℝ}
    (cutoffOut : ∀ n : ℕ, (Mseq n).Cutoff → Fin (n + 1) → ℝ)
    {β vS : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance β)
    (hmem :
      ∀ᶠ n : ℕ in atTop,
        MemLp
          (fun sample : Fin (n + 1) → ℝ =>
            AppliedModelingLib.Probability.upperOrderStatistic sample
              (AppliedModelingLib.Probability.topSampleRank (n := n + 1))) 2
          (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)))
    (hvariance_bound :
      ∀ᶠ n : ℕ in atTop,
        ProbabilityTheory.variance
          (fun sample : Fin (n + 1) → ℝ =>
            AppliedModelingLib.Probability.upperOrderStatistic sample
              (AppliedModelingLib.Probability.topSampleRank (n := n + 1)))
          (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) ≤ maxVariance n)
    (hlower_selected :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : { μ : (Mseq n).Matching // (Mseq n).Stable μ },
          ∀ c : Fin (n + 1),
            lowerCutoff n ≤
              cutoffOut n
                ((Iseq n).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2) c)
    (hupper_selected :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : { μ : (Mseq n).Matching // (Mseq n).Stable μ },
          ∀ c : Fin (n + 1),
            cutoffOut n
                ((Iseq n).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2) c ≤
              upperCutoff n)
    (hlower_threshold :
      Tendsto
        (fun n : ℕ =>
          lowerCutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
              (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) n)
        atTop (nhds vS))
    (hupper_threshold :
      Tendsto
        (fun n : ℕ =>
          upperCutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
              (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) n)
        atTop (nhds vS)) :
    (∀ v ε, v < vS → 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)) <
            ε) ∧
    (∀ v ε, vS < v → 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          1 - ε <
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))) := by
  exact
    theorem1_uniformAttenuation_source_clauses_of_betaMax_variance_bound_selected_stable_cutoff_sandwich
      (Mseq := Mseq) (Iseq := Iseq)
      (sampleLaw := fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
      (maxVariance := maxVariance)
      (lowerCutoff := lowerCutoff)
      (upperCutoff := upperCutoff)
      cutoffOut
      (β := β) (vS := vS)
      (fun _n => by infer_instance)
      hbeta hmem hvariance_bound
      hlower_selected hupper_selected hlower_threshold hupper_threshold

/--
Theorem 1 in the source-style eventual form: below the threshold, every
positive epsilon eventually bounds match probability from above; above the
threshold, match probability is eventually within epsilon of one from below.
-/
theorem theorem1_attenuation_eventually_bounds
    {matchProb : ℕ → ℝ → ℝ} {vS : ℝ}
    (h : theorem1_attenuationConclusion matchProb vS) :
    (∀ v ε, v < vS → 0 < ε →
      ∀ᶠ C : ℕ in atTop, matchProb C v < ε) ∧
    (∀ v ε, vS < v → 0 < ε →
      ∀ᶠ C : ℕ in atTop, 1 - ε < matchProb C v) := by
  constructor
  · intro v ε hv hε
    exact (h.1 v hv) (isOpen_Iio.mem_nhds hε)
  · intro v ε hv hε
    have hmem : (1 : ℝ) ∈ Set.Ioi (1 - ε) := by
      simp
      linarith
    exact (h.2 v hv) (isOpen_Ioi.mem_nhds hmem)

/--
Theorem 2 amplification target: under long-tailed noise, match probability
converges to total supply.
-/
def theorem2_amplificationConclusion
    (matchProb : ℕ → ℝ → ℝ) (totalSupply : ℝ) : Prop :=
  ∀ v : ℝ, Tendsto (fun C : ℕ => matchProb C v) atTop (nhds totalSupply)

/--
Theorem 2 source-shaped target, uniform over admissible stable matchings
`mu ∈ M(D,C)`.
-/
def theorem2_uniformAmplificationConclusion
    (Admissible : ℕ → Type*) (matchProb : ∀ C, Admissible C → ℝ → ℝ)
    (totalSupply : ℝ) : Prop :=
  ∀ v ε, 0 < ε →
    ∀ᶠ C : ℕ in atTop,
      ∀ μ : Admissible C, |matchProb C μ v - totalSupply| < ε

/--
Theorem 2 source clauses.  This projection exposes the paper-facing
uniform-over-stable-matchings absolute-error conclusion without requiring a
reviewer to expand the packed theorem target.
-/
theorem theorem2_uniformAmplification_source_clauses
    {Admissible : ℕ → Type*} {matchProb : ∀ C, Admissible C → ℝ → ℝ}
    {totalSupply : ℝ}
    (h : theorem2_uniformAmplificationConclusion Admissible matchProb totalSupply) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C, |matchProb C μ v - totalSupply| < ε :=
  h

/--
The uniform Theorem 2 statement implies ordinary convergence along any
selected sequence of admissible stable matchings.
-/
theorem theorem2_amplification_of_uniform_selected
    {Admissible : ℕ → Type*} {matchProb : ∀ C, Admissible C → ℝ → ℝ}
    {totalSupply : ℝ}
    (select : ∀ C : ℕ, Admissible C)
    (h : theorem2_uniformAmplificationConclusion
      Admissible matchProb totalSupply) :
    theorem2_amplificationConclusion
      (fun C : ℕ => fun v : ℝ => matchProb C (select C) v)
      totalSupply := by
  intro v
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [h v ε hε] with C hC
  simpa [Real.dist_eq] using hC (select C)

/--
Appendix-style uniform error certificate for Theorem 2.  The long-tail proof
must derive the visible absolute-error bound uniformly over admissible
stable matchings.
-/
structure Theorem2UniformAmplificationErrorCertificate
    (Admissible : ℕ → Type*) (matchProb : ∀ C, Admissible C → ℝ → ℝ)
    (totalSupply : ℝ) where
  error : ℕ → ℝ
  error_tendsto_zero : Tendsto error atTop (nhds 0)
  abs_bound :
    ∀ v, ∀ᶠ C : ℕ in atTop,
      ∀ μ : Admissible C, |matchProb C μ v - totalSupply| ≤ error C

/--
Theorem 2 top-down closure from the long-tail uniform error estimate.
-/
theorem theorem2_uniformAmplification_of_error_certificate
    {Admissible : ℕ → Type*} {matchProb : ∀ C, Admissible C → ℝ → ℝ}
    {totalSupply : ℝ}
    (cert :
      Theorem2UniformAmplificationErrorCertificate
        Admissible matchProb totalSupply) :
    theorem2_uniformAmplificationConclusion Admissible matchProb totalSupply := by
  intro v ε hε
  have hsmall : ∀ᶠ C : ℕ in atTop, cert.error C < ε :=
    cert.error_tendsto_zero (isOpen_Iio.mem_nhds hε)
  filter_upwards [cert.abs_bound v, hsmall] with C hbound herr μ
  exact lt_of_le_of_lt (hbound μ) herr

/--
Theorem 2 closure from the source-style interval estimates.  The amplification
appendix proves that, for every fixed value and tolerance, all admissible
match probabilities eventually lie in a two-sided interval around total
supply.  This theorem converts that interval form into the absolute-value
uniform convergence statement.
-/
theorem theorem2_uniformAmplification_of_eventual_interval
    {Admissible : ℕ → Type*} {matchProb : ∀ C, Admissible C → ℝ → ℝ}
    {totalSupply : ℝ}
    (hinterval :
      ∀ v tol, 0 < tol →
        ∀ᶠ C : ℕ in atTop,
          ∀ μ : Admissible C,
            totalSupply - tol ≤ matchProb C μ v ∧
              matchProb C μ v ≤ totalSupply + tol) :
    theorem2_uniformAmplificationConclusion Admissible matchProb totalSupply := by
  intro v ε hε
  let tol : ℝ := ε / 2
  have htol : 0 < tol := by
    dsimp [tol]
    linarith
  have hevent := hinterval v tol htol
  filter_upwards [hevent] with C hC μ
  have hμ := hC μ
  rw [abs_sub_lt_iff]
  constructor <;> dsimp [tol] at hμ ⊢ <;> linarith

/--
The source lower-side error in the PG24 long-tail amplification window:
`(1 + alpha) epsilon` from the endpoint supply estimates plus the independent
product error `1 - exp (-2 epsilon sigma)`.
-/
noncomputable def theorem2_sourceLowerError (alpha epsilon sigma : ℝ) : ℝ :=
  (1 + alpha) * epsilon + (1 - Real.exp (-(2 * epsilon * sigma)))

/--
The source upper-side error in the PG24 long-tail amplification window:
the endpoint `epsilon`, the independent-product error, and the small-firm
capacity term from equation `equiv-lt`.
-/
noncomputable def theorem2_sourceUpperError
    (totalSupply alpha epsilon sigma : ℝ) : ℝ :=
  epsilon + (1 - Real.exp (-(2 * epsilon * sigma))) +
    alpha * Real.sqrt epsilon /
      (1 - totalSupply - epsilon - (1 - Real.exp (-(2 * epsilon * sigma))))

/--
Concrete shrinking source-error schedule for the Theorem 2 long-tail window.
The paper only needs that the displayed interval around `S` can be made
arbitrarily small; using `epsilon_n = 1 / sqrt(n+1)` and `sigma = 1` gives a
canonical Lean witness.
-/
theorem theorem2_source_exp_error_tendsto_zero_invSqrt_sigma_one :
    Tendsto
      (fun n : ℕ =>
        1 - Real.exp (-(2 * AppliedModelingLib.Math.invSqrtSuccError n * 1)))
      atTop (nhds 0) := by
  have heps :
      Tendsto AppliedModelingLib.Math.invSqrtSuccError atTop (nhds 0) :=
    AppliedModelingLib.Math.invSqrtSuccError_tendsToZero
  have harg :
      Tendsto
        (fun n : ℕ => -(2 * AppliedModelingLib.Math.invSqrtSuccError n * 1))
        atTop (nhds 0) := by
    have hbase :
        Tendsto
          (fun n : ℕ => 2 * AppliedModelingLib.Math.invSqrtSuccError n * 1)
          atTop (nhds (2 * 0 * 1)) :=
      (tendsto_const_nhds.mul heps).mul tendsto_const_nhds
    simpa using hbase.neg
  have hexp :
      Tendsto
        (fun n : ℕ =>
          Real.exp (-(2 * AppliedModelingLib.Math.invSqrtSuccError n * 1)))
        atTop (nhds 1) := by
    simpa [Real.exp_zero] using
      (Real.continuous_exp.tendsto 0).comp harg
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds (1 : ℝ)) :=
    tendsto_const_nhds
  simpa using hone.sub hexp

/-- Along the concrete source-error schedule, the lower Theorem 2 error vanishes. -/
theorem theorem2_sourceLowerError_tendsto_zero_invSqrt_sigma_one
    (alpha : ℝ) :
    Tendsto
      (fun n : ℕ =>
        theorem2_sourceLowerError
          alpha (AppliedModelingLib.Math.invSqrtSuccError n) 1)
      atTop (nhds 0) := by
  have heps :
      Tendsto AppliedModelingLib.Math.invSqrtSuccError atTop (nhds 0) :=
    AppliedModelingLib.Math.invSqrtSuccError_tendsToZero
  have hlinear :
      Tendsto
        (fun n : ℕ => (1 + alpha) * AppliedModelingLib.Math.invSqrtSuccError n)
        atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul heps : Tendsto
        (fun n : ℕ => (1 + alpha) * AppliedModelingLib.Math.invSqrtSuccError n)
        atTop (nhds ((1 + alpha) * 0)))
  have hsum :=
    hlinear.add theorem2_source_exp_error_tendsto_zero_invSqrt_sigma_one
  simpa [theorem2_sourceLowerError] using hsum

/-- The denominator in the upper Theorem 2 source error has positive limit. -/
theorem theorem2_sourceUpperDenominator_tendsto_invSqrt_sigma_one
    (totalSupply : ℝ) :
    Tendsto
      (fun n : ℕ =>
        1 - totalSupply - AppliedModelingLib.Math.invSqrtSuccError n -
          (1 - Real.exp (-(2 * AppliedModelingLib.Math.invSqrtSuccError n * 1))))
      atTop (nhds (1 - totalSupply)) := by
  have heps :
      Tendsto AppliedModelingLib.Math.invSqrtSuccError atTop (nhds 0) :=
    AppliedModelingLib.Math.invSqrtSuccError_tendsToZero
  have hbase :
      Tendsto
        (fun n : ℕ => 1 - totalSupply - AppliedModelingLib.Math.invSqrtSuccError n)
        atTop (nhds (1 - totalSupply)) := by
    simpa using
      (tendsto_const_nhds.sub heps : Tendsto
        (fun n : ℕ => (1 - totalSupply) - AppliedModelingLib.Math.invSqrtSuccError n)
        atTop (nhds ((1 - totalSupply) - 0)))
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
    hbase.sub theorem2_source_exp_error_tendsto_zero_invSqrt_sigma_one

/-- Along the concrete source-error schedule, the upper Theorem 2 error vanishes. -/
theorem theorem2_sourceUpperError_tendsto_zero_invSqrt_sigma_one
    {totalSupply alpha : ℝ} (htotalSupply_lt_one : totalSupply < 1) :
    Tendsto
      (fun n : ℕ =>
        theorem2_sourceUpperError
          totalSupply alpha (AppliedModelingLib.Math.invSqrtSuccError n) 1)
      atTop (nhds 0) := by
  have heps :
      Tendsto AppliedModelingLib.Math.invSqrtSuccError atTop (nhds 0) :=
    AppliedModelingLib.Math.invSqrtSuccError_tendsToZero
  have hexp :=
    theorem2_source_exp_error_tendsto_zero_invSqrt_sigma_one
  have hsqrt :
      Tendsto
        (fun n : ℕ => Real.sqrt (AppliedModelingLib.Math.invSqrtSuccError n))
        atTop (nhds 0) := by
    simpa [Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp heps
  have hnum :
      Tendsto
        (fun n : ℕ => alpha * Real.sqrt (AppliedModelingLib.Math.invSqrtSuccError n))
        atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul hsqrt : Tendsto
        (fun n : ℕ =>
          alpha * Real.sqrt (AppliedModelingLib.Math.invSqrtSuccError n))
        atTop (nhds (alpha * 0)))
  have hden :=
    theorem2_sourceUpperDenominator_tendsto_invSqrt_sigma_one totalSupply
  have hden_ne : 1 - totalSupply ≠ 0 := by
    linarith
  have hquot :
      Tendsto
        (fun n : ℕ =>
          alpha * Real.sqrt (AppliedModelingLib.Math.invSqrtSuccError n) /
            (1 - totalSupply - AppliedModelingLib.Math.invSqrtSuccError n -
              (1 - Real.exp
                (-(2 * AppliedModelingLib.Math.invSqrtSuccError n * 1)))))
        atTop (nhds 0) := by
    simpa using
      (hnum.div hden hden_ne : Tendsto
        (fun n : ℕ =>
          alpha * Real.sqrt (AppliedModelingLib.Math.invSqrtSuccError n) /
            (1 - totalSupply - AppliedModelingLib.Math.invSqrtSuccError n -
              (1 - Real.exp
                (-(2 * AppliedModelingLib.Math.invSqrtSuccError n * 1)))))
        atTop (nhds (0 / (1 - totalSupply))))
  have hsum := (heps.add hexp).add hquot
  simpa [theorem2_sourceUpperError, add_assoc] using hsum

/--
The displayed lower and upper PG24 Theorem 2 source errors can be made
arbitrarily small with fixed model capacity constant `alpha`.
-/
theorem theorem2_sourceErrorParameters_exist_small
    {totalSupply alpha tol : ℝ}
    (htotalSupply_lt_one : totalSupply < 1) (htol : 0 < tol) :
    ∃ epsilon sigma : ℝ,
      0 < epsilon ∧ 0 < sigma ∧
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) ∧
        theorem2_sourceLowerError alpha epsilon sigma < tol ∧
        theorem2_sourceUpperError totalSupply alpha epsilon sigma < tol := by
  have hlower_small :
      ∀ᶠ n : ℕ in atTop,
        theorem2_sourceLowerError
          alpha (AppliedModelingLib.Math.invSqrtSuccError n) 1 < tol :=
    (theorem2_sourceLowerError_tendsto_zero_invSqrt_sigma_one alpha)
      (isOpen_Iio.mem_nhds htol)
  have hupper_small :
      ∀ᶠ n : ℕ in atTop,
        theorem2_sourceUpperError
          totalSupply alpha (AppliedModelingLib.Math.invSqrtSuccError n) 1 < tol :=
    (theorem2_sourceUpperError_tendsto_zero_invSqrt_sigma_one
      (totalSupply := totalSupply) (alpha := alpha) htotalSupply_lt_one)
      (isOpen_Iio.mem_nhds htol)
  have hden_pos :
      ∀ᶠ n : ℕ in atTop,
        0 <
          1 - totalSupply - AppliedModelingLib.Math.invSqrtSuccError n -
            (1 - Real.exp (-(2 * AppliedModelingLib.Math.invSqrtSuccError n * 1))) := by
    have hlim_pos : 0 < 1 - totalSupply := by linarith
    exact
      (theorem2_sourceUpperDenominator_tendsto_invSqrt_sigma_one
        totalSupply) (isOpen_Ioi.mem_nhds hlim_pos)
  rcases Filter.eventually_atTop.1
      (hlower_small.and (hupper_small.and hden_pos)) with
    ⟨N, hN⟩
  refine
    ⟨AppliedModelingLib.Math.invSqrtSuccError N, 1,
      ?_, by norm_num, ?_, ?_, ?_⟩
  · unfold AppliedModelingLib.Math.invSqrtSuccError
    positivity
  · exact (hN N le_rfl).2.2
  · exact (hN N le_rfl).1
  · exact (hN N le_rfl).2.1

/--
The positive denominator used in Theorem 2 implies the simpler source
condition `S + epsilon < 1`.
-/
theorem theorem2_totalSupply_add_epsilon_lt_one_of_denominator_pos
    {totalSupply epsilon sigma : ℝ}
    (hepsilon_pos : 0 < epsilon)
    (hsigma_pos : 0 < sigma)
    (hden_pos :
      0 <
        1 - totalSupply - epsilon -
          (1 - Real.exp (-(2 * epsilon * sigma)))) :
    totalSupply + epsilon < 1 := by
  have hexp_le_one :
      Real.exp (-(2 * epsilon * sigma)) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have herr_nonneg :
      0 ≤ 1 - Real.exp (-(2 * epsilon * sigma)) := by
    linarith
  linarith

/-- The large-firm interval window from the PG24 amplification appendix. -/
def theorem2_largeFirmSourceWindow
    (totalSupply alpha epsilon sigma p : ℝ) : Prop :=
  totalSupply - theorem2_sourceLowerError alpha epsilon sigma ≤ p ∧
    p ≤ totalSupply + epsilon + (1 - Real.exp (-(2 * epsilon * sigma)))

/-- The small-firm capacity bound from the PG24 amplification appendix. -/
def theorem2_smallFirmSourceBound
    (totalSupply alpha epsilon sigma p : ℝ) : Prop :=
  p ≤
    alpha * Real.sqrt epsilon /
      (1 - totalSupply - epsilon -
        (1 - Real.exp (-(2 * epsilon * sigma))))

/--
PG24 Theorem 2 small-firm interval lower bound.

This is the measure-theoretic step in Proposition `lt-small-firms`: on the
source interval above `vStar`, monotonicity of small-firm affordability gives
`denom * pSmall vStar` as a pointwise lower bound, while nonnegativity off the
interval lets the shared two-piece integral lemma turn interval mass into an
integral lower bound.
-/
theorem theorem2_smallFirm_interval_integral_lower_bound
    (η : Measure ℝ) [IsProbabilityMeasure η]
    {region : Set ℝ} {mass denom : ℝ} {pSmall : ℝ → ℝ} {vStar : ℝ}
    (hregion_meas : MeasurableSet region)
    (hint : Integrable (fun w : ℝ => denom * pSmall w) η)
    (hmass : mass ≤ η.real region)
    (hdenom_nonneg : 0 ≤ denom)
    (hp_star_nonneg : 0 ≤ pSmall vStar)
    (hp_mono : Monotone pSmall)
    (hregion_ge : ∀ w : ℝ, w ∈ region → vStar ≤ w)
    (hnonneg_compl :
      ∀ w : ℝ, w ∉ region → 0 ≤ denom * pSmall w) :
    mass * denom * pSmall vStar ≤
      ∫ w : ℝ, denom * pSmall w ∂η := by
  have hlow :
      ∀ w : ℝ, w ∈ region →
        denom * pSmall vStar ≤ denom * pSmall w := by
    intro w hw
    exact
      mul_le_mul_of_nonneg_left
        (hp_mono (hregion_ge w hw)) hdenom_nonneg
  have hsplit :
      (denom * pSmall vStar) * η.real region ≤
        ∫ w : ℝ, denom * pSmall w ∂η :=
    AppliedModelingLib.measureReal_mul_le_integral_of_le_on_of_nonneg_on_compl
      η hregion_meas hint hlow hnonneg_compl
  have hlowBound_nonneg : 0 ≤ denom * pSmall vStar :=
    mul_nonneg hdenom_nonneg hp_star_nonneg
  have hmass_step :
      mass * (denom * pSmall vStar) ≤
        η.real region * (denom * pSmall vStar) :=
    mul_le_mul_of_nonneg_right hmass hlowBound_nonneg
  calc
    mass * denom * pSmall vStar =
        mass * (denom * pSmall vStar) := by ring
    _ ≤ η.real region * (denom * pSmall vStar) := hmass_step
    _ = (denom * pSmall vStar) * η.real region := by ring
    _ ≤ ∫ w : ℝ, denom * pSmall w ∂η := hsplit

/--
PG24 Theorem 2 small-firm matched-mass lower bound from the interval integral.

This composes the paper's event-semantics statement that the matched mass of
the small block dominates the displayed interval integral with the reusable
interval lower bound above.
-/
theorem theorem2_smallFirm_matchedMass_lower_bound_of_interval_integral
    (η : Measure ℝ) [IsProbabilityMeasure η]
    {region : Set ℝ} {mass denom matchedMass : ℝ}
    {pSmall : ℝ → ℝ} {vStar : ℝ}
    (hregion_meas : MeasurableSet region)
    (hint : Integrable (fun w : ℝ => denom * pSmall w) η)
    (hmass : mass ≤ η.real region)
    (hdenom_nonneg : 0 ≤ denom)
    (hp_star_nonneg : 0 ≤ pSmall vStar)
    (hp_mono : Monotone pSmall)
    (hregion_ge : ∀ w : ℝ, w ∈ region → vStar ≤ w)
    (hnonneg_compl :
      ∀ w : ℝ, w ∉ region → 0 ≤ denom * pSmall w)
    (hintegral_le_matched :
      ∫ w : ℝ, denom * pSmall w ∂η ≤ matchedMass) :
    mass * denom * pSmall vStar ≤ matchedMass :=
  le_trans
    (theorem2_smallFirm_interval_integral_lower_bound
      η hregion_meas hint hmass hdenom_nonneg hp_star_nonneg hp_mono
      hregion_ge hnonneg_compl)
    hintegral_le_matched

/--
PG24 Theorem 2 large-firm interval lower bound.

This is the source step behind the low-endpoint inequality
`(1 - epsilon) * p(vLow,F2) <= ...`: on a large value interval above `vLow`,
monotonicity gives `p(vLow,F2)` as a pointwise lower bound, and the shared
two-piece integral lemma turns the interval mass into an integral lower bound.
-/
theorem theorem2_largeFirm_interval_integral_lower_bound
    (η : Measure ℝ) [IsProbabilityMeasure η]
    {region : Set ℝ} {mass : ℝ} {pLarge : ℝ → ℝ} {vLow : ℝ}
    (hregion_meas : MeasurableSet region)
    (hint : Integrable pLarge η)
    (hmass : mass ≤ η.real region)
    (hp_low_nonneg : 0 ≤ pLarge vLow)
    (hp_mono : Monotone pLarge)
    (hregion_ge : ∀ w : ℝ, w ∈ region → vLow ≤ w)
    (hnonneg_compl : ∀ w : ℝ, w ∉ region → 0 ≤ pLarge w) :
    mass * pLarge vLow ≤ ∫ w : ℝ, pLarge w ∂η := by
  have hlow :
      ∀ w : ℝ, w ∈ region → pLarge vLow ≤ pLarge w := by
    intro w hw
    exact hp_mono (hregion_ge w hw)
  have hsplit :
      pLarge vLow * η.real region ≤ ∫ w : ℝ, pLarge w ∂η :=
    AppliedModelingLib.measureReal_mul_le_integral_of_le_on_of_nonneg_on_compl
      η hregion_meas hint hlow hnonneg_compl
  have hmass_step :
      mass * pLarge vLow ≤ η.real region * pLarge vLow :=
    mul_le_mul_of_nonneg_right hmass hp_low_nonneg
  calc
    mass * pLarge vLow ≤ η.real region * pLarge vLow := hmass_step
    _ = pLarge vLow * η.real region := by ring
    _ ≤ ∫ w : ℝ, pLarge w ∂η := hsplit

/--
PG24 Theorem 2 large-firm event-mass lower bound from the interval integral.

This composes the paper's interval lower bound with the source statement that
the large-interval event mass dominates the displayed integral.
-/
theorem theorem2_largeFirm_eventMass_lower_bound_of_interval_integral
    (η : Measure ℝ) [IsProbabilityMeasure η]
    {region : Set ℝ} {mass eventMass : ℝ}
    {pLarge : ℝ → ℝ} {vLow : ℝ}
    (hregion_meas : MeasurableSet region)
    (hint : Integrable pLarge η)
    (hmass : mass ≤ η.real region)
    (hp_low_nonneg : 0 ≤ pLarge vLow)
    (hp_mono : Monotone pLarge)
    (hregion_ge : ∀ w : ℝ, w ∈ region → vLow ≤ w)
    (hnonneg_compl : ∀ w : ℝ, w ∉ region → 0 ≤ pLarge w)
    (hintegral_le_event : ∫ w : ℝ, pLarge w ∂η ≤ eventMass) :
    mass * pLarge vLow ≤ eventMass :=
  le_trans
    (theorem2_largeFirm_interval_integral_lower_bound
      η hregion_meas hint hmass hp_low_nonneg hp_mono hregion_ge
      hnonneg_compl)
    hintegral_le_event

/--
PG24 Theorem 2 high-endpoint event bridge.

The source proof bounds large-block choice mass, up to the outside-window loss,
by an intermediate event mass and then bounds that event mass by the displayed
high-endpoint affordance probability.  This lemma records the transitivity step
so the paper interface can expose those two source clauses separately.
-/
theorem theorem2_largeFirm_highEndpoint_choiceMass_bound_of_interval_event
    {Ω : Type*} [MeasurableSpace Ω] {College : Type u}
    (μ : Measure Ω) (choice : Ω → Option College)
    (active : Finset College) {epsilon pHigh : ℝ} {event : Ω → Prop}
    (hchoice_loss :
      AppliedModelingLib.Matching.choiceMass μ choice active - epsilon ≤
        AppliedModelingLib.Matching.eventMass μ event)
    (hevent_affordance :
      AppliedModelingLib.Matching.eventMass μ event ≤ pHigh) :
    AppliedModelingLib.Matching.choiceMass μ choice active - epsilon ≤ pHigh :=
  le_trans hchoice_loss hevent_affordance

/--
PG24 Theorem 2 high-endpoint event bridge from source semantics.

If every outcome that chooses a large-block college is in the high-endpoint
affordability event, then the large-block choice mass, up to the paper's
outside-window loss, is bounded by that event mass.  Combining this with the
event's high-endpoint affordance bound gives the endpoint clause used by the
amplification proof.
-/
theorem theorem2_largeFirm_highEndpoint_choiceMass_bound_of_event_imp
    {Ω : Type*} [MeasurableSpace Ω] {College : Type u}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (choice : Ω → Option College)
    (active : Finset College) {epsilon pHigh : ℝ} {event : Ω → Prop}
    (hepsilon_nonneg : 0 ≤ epsilon)
    (hchoice_event :
      ∀ ω, AppliedModelingLib.Matching.chosenInActive choice active ω → event ω)
    (hevent_affordance :
      AppliedModelingLib.Matching.eventMass μ event ≤ pHigh) :
    AppliedModelingLib.Matching.choiceMass μ choice active - epsilon ≤ pHigh :=
  le_trans
    (AppliedModelingLib.Matching.choiceMass_sub_nonneg_le_eventMass_of_imp
      μ hepsilon_nonneg hchoice_event)
    hevent_affordance

/--
Scalar algebra behind PG24 Proposition `lt-small-firms`.  After the capacity
and integration argument supplies
`sqrt(epsilon) * denominator * p <= epsilon * alpha`, the displayed small-firm
probability bound follows by dividing through the positive factors.
-/
theorem theorem2_smallFirmSourceBound_of_capacity_mass_lower_bound
    {totalSupply alpha epsilon sigma p : ℝ}
    (hepsilon_pos : 0 < epsilon)
    (hden_pos :
      0 <
        1 - totalSupply - epsilon -
          (1 - Real.exp (-(2 * epsilon * sigma))))
    (hcapacity_mass :
      Real.sqrt epsilon *
          (1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma)))) * p ≤
        epsilon * alpha) :
    theorem2_smallFirmSourceBound totalSupply alpha epsilon sigma p := by
  let denom : ℝ :=
    1 - totalSupply - epsilon -
      (1 - Real.exp (-(2 * epsilon * sigma)))
  have hdenom_pos : 0 < denom := by
    simpa [denom] using hden_pos
  have hsqrt_pos : 0 < Real.sqrt epsilon :=
    Real.sqrt_pos.mpr hepsilon_pos
  have hmul_pos : 0 < Real.sqrt epsilon * denom :=
    mul_pos hsqrt_pos hdenom_pos
  have hdiv :
      p ≤ (epsilon * alpha) / (Real.sqrt epsilon * denom) := by
    rw [le_div_iff₀ hmul_pos]
    simpa [mul_assoc, mul_comm, mul_left_comm, denom] using hcapacity_mass
  have hrewrite :
      (epsilon * alpha) / (Real.sqrt epsilon * denom) =
        alpha * Real.sqrt epsilon / denom := by
    field_simp [ne_of_gt hsqrt_pos, ne_of_gt hdenom_pos]
    rw [Real.sq_sqrt hepsilon_pos.le]
    ring
  simpa [theorem2_smallFirmSourceBound, denom, hrewrite] using hdiv

/--
Capacity-mass inequality from the paper's active-capacity upper bound.  The
source proof obtains a lower bound on the mass of students matched to the
small firms, then compares that mass with the total capacity of the same
small-firm set.  This theorem supplies the finite-capacity side of that
comparison from regular capacities and the cardinality bound `|C1| <= ε C`.
-/
theorem theorem2_capacity_mass_le_of_active_capacity_lower_bound
    {College : Type v}
    (active : Finset College) (capacity : College → ℝ)
    {epsilon alpha totalSupply sigma p : ℝ} {C : ℕ}
    (hcard : (active.card : ℝ) ≤ epsilon * (C : ℝ))
    (halpha_nonneg : 0 ≤ alpha) (hC_pos : 0 < (C : ℝ))
    (hcap : ∀ c ∈ active, capacity c ≤ alpha / (C : ℝ))
    (hlower :
      Real.sqrt epsilon *
          (1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma)))) * p ≤
        AppliedModelingLib.Matching.activeCapacity active capacity) :
    Real.sqrt epsilon *
        (1 - totalSupply - epsilon -
          (1 - Real.exp (-(2 * epsilon * sigma)))) * p ≤
      epsilon * alpha := by
  exact le_trans hlower
    (smallActiveSet_capacity_le_epsilon_mul_alpha
      active capacity hcard halpha_nonneg hC_pos hcap)

/--
Small-firm source bound from the paper's active-capacity comparison.  This
combines the matching/integral lower bound on small-firm matched mass with
the regular-capacity upper bound for `C1`.
-/
theorem theorem2_smallFirmSourceBound_of_active_capacity_lower_bound
    {College : Type v}
    (active : Finset College) (capacity : College → ℝ)
    {totalSupply alpha epsilon sigma p : ℝ} {C : ℕ}
    (hepsilon_pos : 0 < epsilon)
    (hden_pos :
      0 <
        1 - totalSupply - epsilon -
          (1 - Real.exp (-(2 * epsilon * sigma))))
    (hcard : (active.card : ℝ) ≤ epsilon * (C : ℝ))
    (halpha_nonneg : 0 ≤ alpha) (hC_pos : 0 < (C : ℝ))
    (hcap : ∀ c ∈ active, capacity c ≤ alpha / (C : ℝ))
    (hlower :
      Real.sqrt epsilon *
          (1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma)))) * p ≤
        AppliedModelingLib.Matching.activeCapacity active capacity) :
    theorem2_smallFirmSourceBound totalSupply alpha epsilon sigma p :=
  theorem2_smallFirmSourceBound_of_capacity_mass_lower_bound
    hepsilon_pos hden_pos
    (theorem2_capacity_mass_le_of_active_capacity_lower_bound
      active capacity hcard halpha_nonneg hC_pos hcap hlower)

/--
Small-firm bound from the paper's `v*` monotonicity step.  The source proof
uses the capacity/integral lower bound at `v*` and then extends it to all
lower values because small-firm affordability is monotone in value.
-/
theorem theorem2_smallFirmSourceBound_of_star_capacity_mass
    {pSmall : ℝ → ℝ} {v vStar totalSupply alpha epsilon sigma : ℝ}
    (hepsilon_pos : 0 < epsilon)
    (hden_pos :
      0 <
        1 - totalSupply - epsilon -
          (1 - Real.exp (-(2 * epsilon * sigma))))
    (hp_mono : Monotone pSmall)
    (hv : v ≤ vStar)
    (hcapacity_mass_star :
      Real.sqrt epsilon *
          (1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma)))) * pSmall vStar ≤
        epsilon * alpha) :
    theorem2_smallFirmSourceBound totalSupply alpha epsilon sigma (pSmall v) := by
  have hstar :
      theorem2_smallFirmSourceBound
        totalSupply alpha epsilon sigma (pSmall vStar) :=
    theorem2_smallFirmSourceBound_of_capacity_mass_lower_bound
      hepsilon_pos hden_pos hcapacity_mass_star
  exact le_trans (hp_mono hv) hstar

/--
Small-firm bound from the paper's `v*` monotonicity step and the active
capacity comparison for `C1`.
-/
theorem theorem2_smallFirmSourceBound_of_star_active_capacity_lower_bound
    {College : Type v}
    (active : Finset College) (capacity : College → ℝ)
    {pSmall : ℝ → ℝ} {v vStar totalSupply alpha epsilon sigma : ℝ} {C : ℕ}
    (hepsilon_pos : 0 < epsilon)
    (hden_pos :
      0 <
        1 - totalSupply - epsilon -
          (1 - Real.exp (-(2 * epsilon * sigma))))
    (hp_mono : Monotone pSmall)
    (hv : v ≤ vStar)
    (hcard : (active.card : ℝ) ≤ epsilon * (C : ℝ))
    (halpha_nonneg : 0 ≤ alpha) (hC_pos : 0 < (C : ℝ))
    (hcap : ∀ c ∈ active, capacity c ≤ alpha / (C : ℝ))
    (hlower :
      Real.sqrt epsilon *
          (1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma)))) *
          pSmall vStar ≤
        AppliedModelingLib.Matching.activeCapacity active capacity) :
    theorem2_smallFirmSourceBound totalSupply alpha epsilon sigma (pSmall v) := by
  have hstar :
      theorem2_smallFirmSourceBound totalSupply alpha epsilon sigma
        (pSmall vStar) :=
    theorem2_smallFirmSourceBound_of_active_capacity_lower_bound
      active capacity hepsilon_pos hden_pos hcard halpha_nonneg hC_pos
      hcap hlower
  exact le_trans (hp_mono hv) hstar

/--
Eventual small-firm bound from the paper's `v*` monotonicity step.  This is
the form used after the capacity/integral estimate has been proved for all
sufficiently large markets.
-/
theorem theorem2_smallFirmSourceBound_eventually_of_star_capacity_mass
    {pSmall : ℕ → ℝ → ℝ} {v vStar totalSupply alpha epsilon sigma : ℝ}
    (hepsilon_pos : 0 < epsilon)
    (hden_pos :
      0 <
        1 - totalSupply - epsilon -
          (1 - Real.exp (-(2 * epsilon * sigma))))
    (hp_mono : ∀ᶠ C : ℕ in atTop, Monotone (pSmall C))
    (hv : v ≤ vStar)
    (hcapacity_mass_star :
      ∀ᶠ C : ℕ in atTop,
        Real.sqrt epsilon *
            (1 - totalSupply - epsilon -
              (1 - Real.exp (-(2 * epsilon * sigma)))) *
            pSmall C vStar ≤
          epsilon * alpha) :
    ∀ᶠ C : ℕ in atTop,
      theorem2_smallFirmSourceBound
        totalSupply alpha epsilon sigma (pSmall C v) := by
  filter_upwards [hp_mono, hcapacity_mass_star] with C hmono hcap
  exact
    theorem2_smallFirmSourceBound_of_star_capacity_mass
      hepsilon_pos hden_pos hmono hv hcap

/--
Eventual small-firm bound from the active-capacity comparison, for the
finite-market `Fin (C+1)` representation used by PG24.
-/
theorem theorem2_smallFirmSourceBound_eventually_of_star_active_capacity_lower_bound
    {Admissible : ℕ → Type*}
    (small : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1)))
    (capacity : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ)
    {pSmall : ∀ C : ℕ, Admissible C → ℝ → ℝ}
    {v vStar totalSupply alpha epsilon sigma : ℝ}
    (hepsilon_pos : 0 < epsilon)
    (hden_pos :
      0 <
        1 - totalSupply - epsilon -
          (1 - Real.exp (-(2 * epsilon * sigma))))
    (hp_mono :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C, Monotone (pSmall C μ))
    (hv : v ≤ vStar)
    (hcard :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          ((small C μ).card : ℝ) ≤ epsilon * ((C + 1 : ℕ) : ℝ))
    (halpha_nonneg : 0 ≤ alpha)
    (hcap :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C, ∀ c ∈ small C μ,
          capacity C μ c ≤ alpha / ((C + 1 : ℕ) : ℝ))
    (hlower :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          Real.sqrt epsilon *
              (1 - totalSupply - epsilon -
                (1 - Real.exp (-(2 * epsilon * sigma)))) *
              pSmall C μ vStar ≤
            AppliedModelingLib.Matching.activeCapacity (small C μ) (capacity C μ)) :
    ∀ᶠ C : ℕ in atTop,
      ∀ μ : Admissible C,
        theorem2_smallFirmSourceBound totalSupply alpha epsilon sigma
          (pSmall C μ v) := by
  filter_upwards [hp_mono, hcard, hcap, hlower] with
    C hmonoC hcardC hcapC hlowerC μ
  have hC_pos : 0 < (((C + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos C
  exact
    theorem2_smallFirmSourceBound_of_star_active_capacity_lower_bound
      (small C μ) (capacity C μ)
      hepsilon_pos hden_pos (hmonoC μ) hv (hcardC μ)
      halpha_nonneg hC_pos (hcapC μ) (hlowerC μ)

/-- The final total-probability window from PG24 equation `equiv-lt`. -/
def theorem2_totalSourceWindow
    (totalSupply alpha epsilon sigma p : ℝ) : Prop :=
  totalSupply - theorem2_sourceLowerError alpha epsilon sigma ≤ p ∧
    p ≤ totalSupply + theorem2_sourceUpperError totalSupply alpha epsilon sigma

/--
Pointwise final `C1/C2` source-window algebra: a large-firm source window,
a small-firm source bound, and the two decomposition inequalities imply the
total source window from equation `equiv-lt`.
-/
theorem theorem2_totalSourceWindow_of_large_small_firm_bounds
    {pTotal pSmall pLarge totalSupply alpha epsilon sigma : ℝ}
    (hlarge :
      theorem2_largeFirmSourceWindow totalSupply alpha epsilon sigma pLarge)
    (hsmall :
      theorem2_smallFirmSourceBound totalSupply alpha epsilon sigma pSmall)
    (hlarge_le_total : pLarge ≤ pTotal)
    (htotal_le_sum : pTotal ≤ pSmall + pLarge) :
    theorem2_totalSourceWindow totalSupply alpha epsilon sigma pTotal := by
  constructor
  · exact le_trans hlarge.1 hlarge_le_total
  · dsimp [theorem2_totalSourceWindow, theorem2_sourceUpperError,
      theorem2_smallFirmSourceBound] at hsmall ⊢
    linarith [hlarge.2, hsmall, htotal_le_sum]

/--
Concrete cutoff-affordance version of PG24 equation `equiv-lt`.  If the
total active colleges are exactly the union of the small and large active
sets, Lean derives both source decomposition inequalities from the cutoff
event definition and then applies the final Theorem 2 source-window algebra.
-/
theorem theorem2_totalSourceWindow_of_large_small_cutoff_affordance_bounds
    {College : Type v} [DecidableEq College]
    [MeasurableSpace (College → ℝ)]
    (noiseLaw : Measure (College → ℝ)) [IsFiniteMeasure noiseLaw]
    {small large total : Finset College} {v totalSupply alpha epsilon sigma : ℝ}
    {cutoff : College → ℝ}
    (htotal : total = small ∪ large)
    (hlarge :
      theorem2_largeFirmSourceWindow totalSupply alpha epsilon sigma
        (cutoffAffordanceProbability noiseLaw large v cutoff))
    (hsmall :
      theorem2_smallFirmSourceBound totalSupply alpha epsilon sigma
        (cutoffAffordanceProbability noiseLaw small v cutoff)) :
    theorem2_totalSourceWindow totalSupply alpha epsilon sigma
      (cutoffAffordanceProbability noiseLaw total v cutoff) := by
  rcases cutoffAffordanceProbability_decomposition_of_union
      noiseLaw (small := small) (large := large) (total := total)
      (v := v) (cutoff := cutoff) htotal with
    ⟨hlarge_le_total, htotal_le_sum⟩
  exact
    theorem2_totalSourceWindow_of_large_small_firm_bounds
      hlarge hsmall hlarge_le_total htotal_le_sum

/--
Eventual finite-market version of the concrete PG24 `C1/C2` decomposition.
This is the form needed when the college set is `Fin (C+1)` and the active
sets/cutoffs depend on the admissible stable matching.
-/
theorem theorem2_totalSourceWindow_eventually_of_large_small_cutoff_affordance_bounds
    {Admissible : ℕ → Type*}
    (noiseLaw : ∀ C : ℕ, Admissible C → Measure (Fin (C + 1) → ℝ))
    (small large total : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1)))
    (cutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ)
    {v totalSupply alpha epsilon sigma : ℝ}
    (hfinite : ∀ C μ, IsFiniteMeasure (noiseLaw C μ))
    (htotal :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C, total C μ = small C μ ∪ large C μ)
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          theorem2_largeFirmSourceWindow totalSupply alpha epsilon sigma
            (cutoffAffordanceProbability
              (noiseLaw C μ) (large C μ) v (cutoff C μ)))
    (hsmall :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          theorem2_smallFirmSourceBound totalSupply alpha epsilon sigma
            (cutoffAffordanceProbability
              (noiseLaw C μ) (small C μ) v (cutoff C μ))) :
    ∀ᶠ C : ℕ in atTop,
      ∀ μ : Admissible C,
        theorem2_totalSourceWindow totalSupply alpha epsilon sigma
          (cutoffAffordanceProbability
            (noiseLaw C μ) (total C μ) v (cutoff C μ)) := by
  filter_upwards [htotal, hlarge, hsmall] with C htotalC hlargeC hsmallC μ
  haveI : IsFiniteMeasure (noiseLaw C μ) := hfinite C μ
  exact
    theorem2_totalSourceWindow_of_large_small_cutoff_affordance_bounds
      (noiseLaw C μ)
      (small := small C μ) (large := large C μ) (total := total C μ)
      (v := v) (totalSupply := totalSupply)
      (alpha := alpha) (epsilon := epsilon) (sigma := sigma)
      (cutoff := cutoff C μ) (htotalC μ) (hlargeC μ) (hsmallC μ)

/--
Theorem 2 closure from the actual source-shaped long-tail windows.  The
amplification appendix obtains asymmetric bounds around total supply:
`S - lowerError <= p_mu(v) <= S + upperError`.  If, for every tolerance, the
source parameters can be chosen so both visible errors are below that
tolerance and the corresponding window holds eventually and uniformly over
admissible stable matchings, then the paper's uniform amplification theorem
follows.
-/
theorem theorem2_uniformAmplification_of_eventual_source_window
    {Admissible : ℕ → Type*} {matchProb : ∀ C, Admissible C → ℝ → ℝ}
    {totalSupply : ℝ}
    (hwindow :
      ∀ v tol, 0 < tol →
        ∃ alpha epsilon sigma : ℝ,
          theorem2_sourceLowerError alpha epsilon sigma < tol ∧
          theorem2_sourceUpperError totalSupply alpha epsilon sigma < tol ∧
          ∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              totalSupply - theorem2_sourceLowerError alpha epsilon sigma ≤
                  matchProb C μ v ∧
                matchProb C μ v ≤
                  totalSupply +
                    theorem2_sourceUpperError totalSupply alpha epsilon sigma) :
    theorem2_uniformAmplificationConclusion Admissible matchProb totalSupply := by
  intro v tol htol
  rcases hwindow v tol htol with
    ⟨alpha, epsilon, sigma, hlower_small, hupper_small, hevent⟩
  filter_upwards [hevent] with C hC μ
  have hμ := hC μ
  rw [abs_sub_lt_iff]
  constructor <;> linarith

/--
Uniform source-window construction from the large-firm and small-firm bounds
in the PG24 amplification appendix.  This is the uniform-in-`mu` version of
the final `C1/C2` decomposition: large-firm probability gives the lower
bound, while small-firm capacity plus large-firm probability gives the upper
bound.
-/
theorem theorem2_uniform_source_window_eventually_of_large_small_firm_bounds
    {Admissible : ℕ → Type*}
    {pTotal pSmall pLarge : ∀ C : ℕ, Admissible C → ℝ → ℝ}
    {v totalSupply alpha epsilon sigma : ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          theorem2_largeFirmSourceWindow
            totalSupply alpha epsilon sigma (pLarge C μ v))
    (hsmall :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          theorem2_smallFirmSourceBound
            totalSupply alpha epsilon sigma (pSmall C μ v))
    (hlarge_le_total :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C, pLarge C μ v ≤ pTotal C μ v)
    (htotal_le_sum :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          pTotal C μ v ≤ pSmall C μ v + pLarge C μ v) :
    ∀ᶠ C : ℕ in atTop,
      ∀ μ : Admissible C,
        theorem2_totalSourceWindow
          totalSupply alpha epsilon sigma (pTotal C μ v) := by
  filter_upwards [hlarge, hsmall, hlarge_le_total, htotal_le_sum] with
    C hlargeC hsmallC hleC hsumC μ
  have hlargeμ := hlargeC μ
  have hsmallμ := hsmallC μ
  constructor
  · exact le_trans hlargeμ.1 (hleC μ)
  · dsimp [theorem2_totalSourceWindow, theorem2_sourceUpperError,
      theorem2_smallFirmSourceBound] at hsmallμ ⊢
    linarith [hlargeμ.2, hsmallμ, hsumC μ]

/--
Theorem 2 closure directly from the source large- and small-firm appendix
windows.  For each value and target tolerance, choose source parameters
`alpha`, `epsilon`, and `sigma` whose visible lower and upper errors are below
the tolerance; if the large-firm, small-firm, and decomposition inequalities
then hold eventually and uniformly over admissible stable matchings, the
paper's uniform long-tail amplification conclusion follows.
-/
theorem theorem2_uniformAmplification_of_large_small_source_windows
    {Admissible : ℕ → Type*}
    {pTotal pSmall pLarge : ∀ C : ℕ, Admissible C → ℝ → ℝ}
    {totalSupply : ℝ}
    (hsource :
      ∀ v tol, 0 < tol →
        ∃ alpha epsilon sigma : ℝ,
          theorem2_sourceLowerError alpha epsilon sigma < tol ∧
          theorem2_sourceUpperError totalSupply alpha epsilon sigma < tol ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              theorem2_largeFirmSourceWindow
                totalSupply alpha epsilon sigma (pLarge C μ v)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              theorem2_smallFirmSourceBound
                totalSupply alpha epsilon sigma (pSmall C μ v)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, pLarge C μ v ≤ pTotal C μ v) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              pTotal C μ v ≤ pSmall C μ v + pLarge C μ v)) :
    theorem2_uniformAmplificationConclusion Admissible pTotal totalSupply := by
  refine theorem2_uniformAmplification_of_eventual_source_window ?_
  intro v tol htol
  rcases hsource v tol htol with
    ⟨alpha, epsilon, sigma, hlower_small, hupper_small,
      hlarge, hsmall, hlarge_le_total, htotal_le_sum⟩
  refine ⟨alpha, epsilon, sigma, hlower_small, hupper_small, ?_⟩
  exact
    theorem2_uniform_source_window_eventually_of_large_small_firm_bounds
      (Admissible := Admissible)
      (pTotal := pTotal) (pSmall := pSmall) (pLarge := pLarge)
      (v := v) (totalSupply := totalSupply)
      (alpha := alpha) (epsilon := epsilon) (sigma := sigma)
      hlarge hsmall hlarge_le_total htotal_le_sum

/--
Fixed-`alpha` version of the PG24 Theorem 2 closure.  The model capacity
constant `alpha` is not chosen as a proof parameter; Lean chooses only the
source approximation parameters `epsilon` and `sigma`, using the preceding
source-error schedule to make the displayed interval around `S` arbitrarily
small.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_large_small_source_windows
    {Admissible : ℕ → Type*}
    {pTotal pSmall pLarge : ∀ C : ℕ, Admissible C → ℝ → ℝ}
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              theorem2_largeFirmSourceWindow
                totalSupply alpha epsilon sigma (pLarge C μ v)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              theorem2_smallFirmSourceBound
                totalSupply alpha epsilon sigma (pSmall C μ v)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, pLarge C μ v ≤ pTotal C μ v) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              pTotal C μ v ≤ pSmall C μ v + pLarge C μ v)) :
    theorem2_uniformAmplificationConclusion Admissible pTotal totalSupply := by
  refine theorem2_uniformAmplification_of_large_small_source_windows
    (pTotal := pTotal) (pSmall := pSmall) (pLarge := pLarge) ?_
  intro v tol htol
  rcases theorem2_sourceErrorParameters_exist_small
      (totalSupply := totalSupply) (alpha := alpha)
      htotalSupply_lt_one htol with
    ⟨epsilon, sigma, hepsilon, hsigma, hden_pos,
      hlower_small, hupper_small⟩
  rcases hsource v epsilon sigma hepsilon hsigma hden_pos with
    ⟨hlarge, hsmall, hlarge_le_total, htotal_le_sum⟩
  exact
    ⟨alpha, epsilon, sigma, hlower_small, hupper_small,
      hlarge, hsmall, hlarge_le_total, htotal_le_sum⟩

/--
Uniform source-window construction when the paper's small/large split depends
on the approximation parameter `epsilon`.  This matches the amplification
appendix definition of `F_1` and `F_2`: after `epsilon` is chosen, the proof
uses the corresponding split to bound the total match probability.
-/
theorem theorem2_uniform_source_window_eventually_of_epsilon_indexed_large_small_firm_bounds
    {Admissible : ℕ → Type*}
    {pTotal : ∀ C : ℕ, Admissible C → ℝ → ℝ}
    {pSmall pLarge : ℝ → ∀ C : ℕ, Admissible C → ℝ → ℝ}
    {v totalSupply alpha epsilon sigma : ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          theorem2_largeFirmSourceWindow
            totalSupply alpha epsilon sigma (pLarge epsilon C μ v))
    (hsmall :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          theorem2_smallFirmSourceBound
            totalSupply alpha epsilon sigma (pSmall epsilon C μ v))
    (hlarge_le_total :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C, pLarge epsilon C μ v ≤ pTotal C μ v)
    (htotal_le_sum :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          pTotal C μ v ≤ pSmall epsilon C μ v + pLarge epsilon C μ v) :
    ∀ᶠ C : ℕ in atTop,
      ∀ μ : Admissible C,
        theorem2_totalSourceWindow
          totalSupply alpha epsilon sigma (pTotal C μ v) := by
  filter_upwards [hlarge, hsmall, hlarge_le_total, htotal_le_sum] with
    C hlargeC hsmallC hleC hsumC μ
  have hlargeμ := hlargeC μ
  have hsmallμ := hsmallC μ
  constructor
  · exact le_trans hlargeμ.1 (hleC μ)
  · dsimp [theorem2_totalSourceWindow, theorem2_sourceUpperError,
      theorem2_smallFirmSourceBound] at hsmallμ ⊢
    linarith [hlargeμ.2, hsmallμ, hsumC μ]

/--
Fixed-`alpha` Theorem 2 closure with an epsilon-indexed small/large split.
This is the source-faithful version of the large/small-window route: Lean
chooses `epsilon` and `sigma` for the target tolerance, then applies the
source estimates for the split associated with that chosen `epsilon`.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_epsilon_indexed_large_small_source_windows
    {Admissible : ℕ → Type*}
    {pTotal : ∀ C : ℕ, Admissible C → ℝ → ℝ}
    {pSmall pLarge : ℝ → ∀ C : ℕ, Admissible C → ℝ → ℝ}
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              theorem2_largeFirmSourceWindow
                totalSupply alpha epsilon sigma (pLarge epsilon C μ v)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              theorem2_smallFirmSourceBound
                totalSupply alpha epsilon sigma (pSmall epsilon C μ v)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, pLarge epsilon C μ v ≤ pTotal C μ v) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              pTotal C μ v ≤ pSmall epsilon C μ v + pLarge epsilon C μ v)) :
    theorem2_uniformAmplificationConclusion Admissible pTotal totalSupply := by
  refine theorem2_uniformAmplification_of_eventual_source_window ?_
  intro v tol htol
  rcases theorem2_sourceErrorParameters_exist_small
      (totalSupply := totalSupply) (alpha := alpha)
      htotalSupply_lt_one htol with
    ⟨epsilon, sigma, hepsilon, hsigma, hden_pos,
      hlower_small, hupper_small⟩
  rcases hsource v epsilon sigma hepsilon hsigma hden_pos with
    ⟨hlarge, hsmall, hlarge_le_total, htotal_le_sum⟩
  refine ⟨alpha, epsilon, sigma, hlower_small, hupper_small, ?_⟩
  exact
    theorem2_uniform_source_window_eventually_of_epsilon_indexed_large_small_firm_bounds
      (Admissible := Admissible)
      (pTotal := pTotal) (pSmall := pSmall) (pLarge := pLarge)
      (v := v) (totalSupply := totalSupply)
      (alpha := alpha) (epsilon := epsilon) (sigma := sigma)
      hlarge hsmall hlarge_le_total htotal_le_sum

/--
Selected-stable Theorem 2 closure from source large/small windows.

This specializes the generic large/small-window closure to the actual PG24
stable-matching surface: for each stable matching, use the A-L selected
market-clearing cutoff and the paper's epsilon-indexed `F_1/F_2` split.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_selected_stable_floor_split_large_small_source_windows
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              theorem2_largeFirmSourceWindow totalSupply alpha epsilon sigma
                (cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  v
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2)))) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              theorem2_smallFirmSourceBound totalSupply alpha epsilon sigma
                (cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                  v
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2)))) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  v
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2)) ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (Finset.univ : Finset (Fin (C + 1)))
                  v
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (Finset.univ : Finset (Fin (C + 1)))
                  v
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2)) ≤
                cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    v
                    (cutoffOut C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2)) +
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    v
                    (cutoffOut C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2)))) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_epsilon_indexed_large_small_source_windows
    (Admissible :=
      fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (pTotal := fun C μ v =>
      cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (Finset.univ : Finset (Fin (C + 1))) v
        (cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
    (pSmall := fun epsilon C μ v =>
      cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
        v
        (cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
    (pLarge := fun epsilon C μ v =>
      cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
        v
        (cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
    (totalSupply := totalSupply) (alpha := alpha)
    htotalSupply_lt_one hsource

/--
Theorem 2 in the source-style epsilon form: for each value, match probability
is eventually within epsilon of total supply.
-/
theorem theorem2_amplification_eventually_abs_bound
    {matchProb : ℕ → ℝ → ℝ} {totalSupply : ℝ}
    (h : theorem2_amplificationConclusion matchProb totalSupply) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop, |matchProb C v - totalSupply| < ε := by
  intro v ε hε
  have hmem : totalSupply ∈ Set.Ioo (totalSupply - ε) (totalSupply + ε) := by
    constructor <;> linarith
  have hevent := (h v) (isOpen_Ioo.mem_nhds hmem)
  filter_upwards [hevent] with C hC
  rcases hC with ⟨hlo, hhi⟩
  rw [abs_sub_lt_iff]
  exact ⟨by linarith, by linarith⟩

/--
Source-facing long-tail survival condition.  `survival x` represents
`Pr[X > x]`; the PG24 definition says the conditional upper-tail ratio after
any positive shift tends to one.
-/
def LongTailedSurvival (survival : ℝ → ℝ) : Prop :=
  ∀ d : ℝ, 0 < d →
    Tendsto (fun x : ℝ => survival (x + d) / survival x) atTop (nhds 1)

/--
A nonnegative long-tailed survival function is eventually strictly positive.
With Lean's real division convention, if the denominator were zero then the
ratio would be zero, contradicting convergence of the positive-shift ratio to
one.
-/
theorem LongTailedSurvival.eventually_pos
    {survival : ℝ → ℝ} (h : LongTailedSurvival survival)
    (hnonneg : ∀ x : ℝ, 0 ≤ survival x) :
    ∀ᶠ x : ℝ in atTop, 0 < survival x := by
  have hhalf :
      ∀ᶠ x : ℝ in atTop,
        (1 / 2 : ℝ) < survival (x + 1) / survival x := by
    have hmem : (1 : ℝ) ∈ Set.Ioi (1 / 2 : ℝ) := by norm_num
    exact (h 1 (by norm_num)) (isOpen_Ioi.mem_nhds hmem)
  filter_upwards [hhalf] with x hx
  by_contra hnot
  have hzero : survival x = 0 :=
    le_antisymm (le_of_not_gt hnot) (hnonneg x)
  have hxzero : (1 / 2 : ℝ) < 0 := by
    simpa [hzero] using hx
  norm_num at hxzero

/--
Upper-tail probabilities supply the generic survival-function facts used by
the long-tail PG24 arguments: antitonicity and `[0,1]` probability bounds.
This keeps the paper-level rows from treating those facts as separate source
premises once `survival x` is instantiated as `Pr[X > x]`.
-/
theorem upperTailMass_survival_probability_package
    {Admissible : ℕ → Type*}
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {active : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    {cutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ} :
    Antitone (AppliedModelingLib.Probability.upperTailMass noiseLaw) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C, ∀ v, ∀ c ∈ active C μ,
          0 ≤ AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff C μ c - v)) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C, ∀ v, ∀ c ∈ active C μ,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff C μ c - v) ≤ 1) := by
  constructor
  · exact AppliedModelingLib.Probability.upperTailMass_antitone noiseLaw
  constructor
  · filter_upwards with C μ v c hc
    exact AppliedModelingLib.Probability.upperTailMass_nonneg noiseLaw _
  · filter_upwards with C μ v c hc
    exact AppliedModelingLib.Probability.upperTailMass_le_one noiseLaw _

/--
Indexed no-`Admissible` variant of
`upperTailMass_survival_probability_package`, used by coalition witness rows.
-/
theorem upperTailMass_survival_probability_package_indexed
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {active : ∀ C : ℕ, Finset (Fin (C + 1))}
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ} :
    Antitone (AppliedModelingLib.Probability.upperTailMass noiseLaw) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ v, ∀ c ∈ active C,
          0 ≤ AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff C c - v)) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ v, ∀ c ∈ active C,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff C c - v) ≤ 1) := by
  constructor
  · exact AppliedModelingLib.Probability.upperTailMass_antitone noiseLaw
  constructor
  · filter_upwards with C v c hc
    exact AppliedModelingLib.Probability.upperTailMass_nonneg noiseLaw _
  · filter_upwards with C v c hc
    exact AppliedModelingLib.Probability.upperTailMass_le_one noiseLaw _

/--
Long-tailed upper-tail probabilities and an eventually diverging cutoff floor
derive the strict side conditions used in PG24 long-tail endpoint estimates.
The high endpoint has positive tail mass, and the low endpoint has strictly
positive failure probability, eventually and uniformly over admissible
instances and active colleges.
-/
theorem upperTailMass_strict_side_conditions_of_longTail_cutoff_floor
    {Admissible : ℕ → Type*}
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {active : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    {cutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ}
    {vLow vHigh : ℝ} {lowerCutoff : ℕ → ℝ}
    (hvStrict : vLow < vHigh)
    (hlower_atTop :
      Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop)
    (hcutoff_lower :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C, ∀ c ∈ active C μ,
          lowerCutoff C ≤ cutoff C μ c) :
    (∀ᶠ C : ℕ in atTop,
      ∀ μ : Admissible C, ∀ c ∈ active C μ,
        0 < AppliedModelingLib.Probability.upperTailMass noiseLaw
          (cutoff C μ c - vHigh)) ∧
    (∀ᶠ C : ℕ in atTop,
      ∀ μ : Admissible C, ∀ c ∈ active C μ,
        0 < 1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
          (cutoff C μ c - vLow)) := by
  have htail_pos_atTop :
      ∀ᶠ x : ℝ in atTop,
        0 < AppliedModelingLib.Probability.upperTailMass noiseLaw x :=
    hlong.eventually_pos
      (fun x => AppliedModelingLib.Probability.upperTailMass_nonneg noiseLaw x)
  rcases Filter.eventually_atTop.1 htail_pos_atTop with
    ⟨posFloor, hposFloor⟩
  have htail_lt_one_atTop :
      ∀ᶠ x : ℝ in atTop,
        AppliedModelingLib.Probability.upperTailMass noiseLaw x < 1 :=
    AppliedModelingLib.Probability.eventually_upperTailMass_lt_one_atTop noiseLaw
  rcases Filter.eventually_atTop.1 htail_lt_one_atTop with
    ⟨oneFloor, honeFloor⟩
  constructor
  · have hfloor :
        ∀ᶠ C : ℕ in atTop, posFloor ≤ lowerCutoff C - vHigh :=
      Filter.tendsto_atTop.1 hlower_atTop posFloor
    filter_upwards [hfloor, hcutoff_lower] with
      C hfloorC hcutoffC μ c hc
    exact hposFloor (cutoff C μ c - vHigh) (by linarith [hcutoffC μ c hc])
  · have hfloor :
        ∀ᶠ C : ℕ in atTop, oneFloor ≤ lowerCutoff C - vHigh :=
      Filter.tendsto_atTop.1 hlower_atTop oneFloor
    filter_upwards [hfloor, hcutoff_lower] with
      C hfloorC hcutoffC μ c hc
    have hlt :
        AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff C μ c - vLow) < 1 :=
      honeFloor (cutoff C μ c - vLow) (by
        have hle_high : oneFloor ≤ cutoff C μ c - vHigh := by
          linarith [hcutoffC μ c hc]
        linarith)
    linarith

/-- Indexed variant of `upperTailMass_strict_side_conditions_of_longTail_cutoff_floor`. -/
theorem upperTailMass_strict_side_conditions_of_longTail_cutoff_floor_indexed
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {active : ∀ C : ℕ, Finset (Fin (C + 1))}
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ}
    {vLow vHigh : ℝ} {lowerCutoff : ℕ → ℝ}
    (hvStrict : vLow < vHigh)
    (hlower_atTop :
      Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop)
    (hcutoff_lower :
      ∀ᶠ C : ℕ in atTop,
        ∀ c ∈ active C, lowerCutoff C ≤ cutoff C c) :
    (∀ᶠ C : ℕ in atTop,
      ∀ c ∈ active C,
        0 < AppliedModelingLib.Probability.upperTailMass noiseLaw
          (cutoff C c - vHigh)) ∧
    (∀ᶠ C : ℕ in atTop,
      ∀ c ∈ active C,
        0 < 1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
          (cutoff C c - vLow)) := by
  let Admissible : ℕ → Type := fun _ => PUnit
  let active' : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1)) :=
    fun C _ => active C
  let cutoff' : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ :=
    fun C _ => cutoff C
  have hcutoff_lower' :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C, ∀ c ∈ active' C μ,
          lowerCutoff C ≤ cutoff' C μ c := by
    filter_upwards [hcutoff_lower] with C hC μ c hc
    exact hC c hc
  have h :=
    upperTailMass_strict_side_conditions_of_longTail_cutoff_floor
      (Admissible := Admissible)
      (noiseLaw := noiseLaw)
      (hlong := hlong)
      (active := active')
      (cutoff := cutoff')
      (vLow := vLow)
      (vHigh := vHigh)
      (lowerCutoff := lowerCutoff)
      hvStrict hlower_atTop hcutoff_lower'
  constructor
  · filter_upwards [h.1] with C hC c hc
    exact hC PUnit.unit c hc
  · filter_upwards [h.2] with C hC c hc
    exact hC PUnit.unit c hc

/--
Long-tailed upper tails turn a common diverging cutoff floor into the
low/high tail transfer used by first-large-index product lower bounds.
-/
theorem upperTailMass_tail_ratio_uniform_eventually_of_longTail_cutoff_floor
    {Admissible : ℕ → Type*}
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {active : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    {cutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ}
    {lowerCutoff : ℕ → ℝ} {vLow vHigh epsilon : ℝ}
    (hvStrict : vLow < vHigh) (hepsilon : 0 < epsilon)
    (hlower_atTop :
      Tendsto (fun C : ℕ => lowerCutoff C - vHigh) atTop atTop)
    (hcutoff_lower :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C, ∀ c ∈ active C μ,
          lowerCutoff C ≤ cutoff C μ c) :
    ∀ᶠ C : ℕ in atTop,
      ∀ μ : Admissible C, ∀ c ∈ active C μ,
        (1 - epsilon) *
            AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoff C μ c - vHigh) ≤
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff C μ c - vLow) := by
  let d : ℝ := vHigh - vLow
  have hd : 0 < d := by
    dsimp [d]
    linarith
  have hmem : (1 : ℝ) ∈ Set.Ioi (1 - epsilon) := by
    simp
    linarith
  have hratio_event :
      ∀ᶠ x : ℝ in atTop,
        1 - epsilon <
          AppliedModelingLib.Probability.upperTailMass noiseLaw (x + d) /
            AppliedModelingLib.Probability.upperTailMass noiseLaw x :=
    (hlong d hd) (isOpen_Ioi.mem_nhds hmem)
  rcases Filter.eventually_atTop.1 hratio_event with
    ⟨x0, hx0⟩
  have hlower_ge :
      ∀ᶠ C : ℕ in atTop, x0 ≤ lowerCutoff C - vHigh :=
    hlower_atTop (Filter.eventually_atTop.2 ⟨x0, fun x hx => hx⟩)
  have hhigh_pos :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C, ∀ c ∈ active C μ,
          0 < AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff C μ c - vHigh) :=
    (upperTailMass_strict_side_conditions_of_longTail_cutoff_floor
      (Admissible := Admissible)
      (noiseLaw := noiseLaw)
      (hlong := hlong)
      (active := active)
      (cutoff := cutoff)
      (vLow := vLow)
      (vHigh := vHigh)
      (lowerCutoff := lowerCutoff)
      hvStrict hlower_atTop hcutoff_lower).1
  filter_upwards [hlower_ge, hcutoff_lower, hhigh_pos] with
    C hfloorC hcutoffC hposC μ c hc
  have hx_ge : x0 ≤ cutoff C μ c - vHigh := by
    have hcut := hcutoffC μ c hc
    linarith
  have hratio :
      1 - epsilon <
        AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff C μ c - vLow) /
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff C μ c - vHigh) := by
    have hbase :
        1 - epsilon <
          AppliedModelingLib.Probability.upperTailMass noiseLaw
              ((cutoff C μ c - vHigh) + d) /
            AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoff C μ c - vHigh) :=
      hx0 (cutoff C μ c - vHigh) hx_ge
    simpa [d, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hbase
  have hmul_lt :=
    mul_lt_mul_of_pos_right hratio (hposC μ c hc)
  have hcancel :
      (AppliedModelingLib.Probability.upperTailMass noiseLaw
          (cutoff C μ c - vLow) /
        AppliedModelingLib.Probability.upperTailMass noiseLaw
          (cutoff C μ c - vHigh)) *
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff C μ c - vHigh) =
        AppliedModelingLib.Probability.upperTailMass noiseLaw
          (cutoff C μ c - vLow) := by
    field_simp [ne_of_gt (hposC μ c hc)]
  exact le_of_lt (by
    simpa [hcancel, mul_assoc, mul_comm, mul_left_comm] using hmul_lt)

/--
In the selected-stable PG24 setting, a scalar high-tail rate of order
`sigma / (C+1)` forces the lower cutoff floor to diverge.  The only extra input
needed beyond the tail estimate is nonempty stable matchings, supplied here by
the bundled A-L cutoff-market consequence package.
-/
theorem theorem2_lowerCutoff_sub_vHigh_atTop_of_AL_high_tail_rate
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Aseq :
      ∀ C : ℕ,
        AL16SupplyDemandMatching.CutoffMarketConsequences (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {sigma vHigh : ℝ} {lowerCutoff : ℕ → ℝ}
    (htail :
      ∀ᶠ C : ℕ in atTop,
        ∀ _μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (lowerCutoff C - vHigh) ≤
          sigma / ((C + 1 : ℕ) : ℝ)) :
    Tendsto (fun C : ℕ => lowerCutoff C - vHigh) atTop atTop := by
  have hstable_nonempty :
      ∀ C : ℕ, Nonempty { μ : (Mseq C).Matching // (Mseq C).Stable μ } := by
    intro C
    rcases (Aseq C).supplyDemand.exists_stable_of_exists_marketClearing
        (Aseq C).lattice.nonempty_marketClearing with
      ⟨μ, hμ⟩
    exact ⟨⟨μ, hμ⟩⟩
  have htail_inst :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Probability.upperTailMass noiseLaw
          (lowerCutoff C - vHigh) ≤
        sigma / ((C + 1 : ℕ) : ℝ) := by
    filter_upwards [htail] with C htailC
    exact htailC (Classical.choice (hstable_nonempty C))
  have hbound_zero :
      Tendsto
        (fun C : ℕ => sigma / ((C + 1 : ℕ) : ℝ))
        atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop pg24_tendsto_nat_succ_cast_atTop sigma
  exact
    AppliedModelingLib.Probability.tendsto_atTop_of_upperTailMass_le_tendsto_zero
      noiseLaw
      (hlong.eventually_pos
        (fun x => AppliedModelingLib.Probability.upperTailMass_nonneg noiseLaw x))
      hbound_zero htail_inst

theorem LongTailedSurvival.eventually_ratio_gt
    {survival : ℝ → ℝ} (h : LongTailedSurvival survival)
    {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      1 - ε < survival (x + d) / survival x := by
  have hmem : (1 : ℝ) ∈ Set.Ioi (1 - ε) := by
    simp
    linarith
  exact (h d hd) (isOpen_Ioi.mem_nhds hmem)

/--
PG24 long-tail value-ratio step.  If `vLow < vHigh` and the relevant cutoff
threshold tends to infinity after subtracting `vHigh`, then the ratio
`Pr[vLow + X > P] / Pr[vHigh + X > P]` is eventually close to one from below.
-/
theorem LongTailedSurvival.eventually_value_ratio_gt
    {survival : ℝ → ℝ} (h : LongTailedSurvival survival)
    {threshold : ℕ → ℝ} {vLow vHigh ε : ℝ}
    (hv : vLow < vHigh) (hε : 0 < ε)
    (hthreshold : Tendsto (fun n : ℕ => threshold n - vHigh) atTop atTop) :
    ∀ᶠ n : ℕ in atTop,
      1 - ε < survival (threshold n - vLow) /
        survival (threshold n - vHigh) := by
  let d : ℝ := vHigh - vLow
  have hd : 0 < d := by
    dsimp [d]
    linarith
  have hratio :
      Tendsto
        (fun n : ℕ =>
          survival ((threshold n - vHigh) + d) /
            survival (threshold n - vHigh))
        atTop (nhds 1) :=
    (h d hd).comp hthreshold
  have hmem : (1 : ℝ) ∈ Set.Ioi (1 - ε) := by
    simp
    linarith
  have hevent :
      ∀ᶠ n : ℕ in atTop,
        1 - ε <
          survival ((threshold n - vHigh) + d) /
            survival (threshold n - vHigh) :=
    hratio (isOpen_Ioi.mem_nhds hmem)
  filter_upwards [hevent] with n hn
  simpa [d, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hn

/--
Uniform long-tail ratio over a finite active college set.  Once all active
cutoffs are eventually above a common lower threshold whose high-value
residual tends to infinity, the single-college low/high crossing-probability
ratio is eventually close to one for every active college.
-/
theorem LongTailedSurvival.eventually_uniform_value_ratio_gt_of_cutoff_lower_bound
    {survival : ℝ → ℝ} (h : LongTailedSurvival survival)
    {active : ∀ n : ℕ, Finset (Fin (n + 1))}
    {cutoff : ∀ n : ℕ, Fin (n + 1) → ℝ}
    {lowerCutoff : ℕ → ℝ} {vLow vHigh ε : ℝ}
    (hv : vLow < vHigh) (hε : 0 < ε)
    (hlower_atTop :
      Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop)
    (hcutoff_lower :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ active n, lowerCutoff n ≤ cutoff n c) :
    ∀ᶠ n : ℕ in atTop,
      ∀ c ∈ active n,
        1 - ε < survival (cutoff n c - vLow) /
          survival (cutoff n c - vHigh) := by
  let d : ℝ := vHigh - vLow
  have hd : 0 < d := by
    dsimp [d]
    linarith
  rcases Filter.eventually_atTop.1
      (LongTailedSurvival.eventually_ratio_gt h hd hε) with
    ⟨x0, hx0⟩
  have hlower_ge :
      ∀ᶠ n : ℕ in atTop, x0 ≤ lowerCutoff n - vHigh :=
    hlower_atTop (Filter.eventually_atTop.2 ⟨x0, fun x hx => hx⟩)
  filter_upwards [hlower_ge, hcutoff_lower] with n hn_ge hn_cutoff c hc
  have hx_ge : x0 ≤ cutoff n c - vHigh := by
    have hcut := hn_cutoff c hc
    linarith
  have hratio :
      1 - ε <
        survival ((cutoff n c - vHigh) + d) /
          survival (cutoff n c - vHigh) :=
    hx0 (cutoff n c - vHigh) hx_ge
  simpa [d, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hratio

/--
Independent-product affordance probability from single-college crossing
probabilities.  This is the deterministic product representation used in the
long-tail amplification proof before instantiating it with an actual product
noise law.
-/
noncomputable def independentAffordanceProbability {College : Type v}
    (active : Finset College) (crossingProbability : College → ℝ) : ℝ :=
  1 - ∏ c ∈ active, (1 - crossingProbability c)

/--
Under iid one-dimensional noise, the concrete cutoff-affordance probability
equals the independent product expression with per-college upper-tail masses.
This instantiates the long-tail amplification route with the paper's product
noise source model.
-/
theorem cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
    {n : ℕ} (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (active : Finset (Fin n)) (v : ℝ) (cutoff : Fin n → ℝ) :
    cutoffAffordanceProbability (Measure.pi (fun _ : Fin n => noiseLaw))
        active v cutoff =
      independentAffordanceProbability active
        (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff c - v)) := by
  simpa [cutoffAffordanceProbability, independentAffordanceProbability] using
    AppliedModelingLib.Matching.cutoffCrossingProbability_iidProduct_eq_one_sub_prod_one_sub_upperTailMass
      noiseLaw active v cutoff

/--
Iid active-set affordance is bounded by a scalar upper-tail bound times the
number of active colleges.  This is the finite-union-bound form used by the
coalition attenuation proof at the low endpoint.
-/
theorem cutoffAffordanceProbability_iidProduct_le_card_mul_of_upperTailMass_le
    {n : ℕ} (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (active : Finset (Fin n)) (v : ℝ) (cutoff : Fin n → ℝ) {q : ℝ}
    (hupper :
      ∀ c ∈ active,
        AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff c - v) ≤ q) :
    cutoffAffordanceProbability (Measure.pi (fun _ : Fin n => noiseLaw))
        active v cutoff ≤ (active.card : ℝ) * q := by
  have hsingle :
      ∀ c ∈ active,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin n => noiseLaw)) v cutoff c ≤ q := by
    intro c hc
    rw [AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_eq_upperTailMass]
    exact hupper c hc
  simpa [cutoffAffordanceProbability] using
    AppliedModelingLib.Matching.cutoffCrossingProbability_le_card_mul_of_singleCutoffCrossingProbability_le
      (Measure.pi (fun _ : Fin n => noiseLaw)) active v cutoff hsingle

/--
Strict low-endpoint version of the finite union bound for iid active-set
affordance.
-/
theorem cutoffAffordanceProbability_iidProduct_lt_of_card_mul_upperTailMass_le
    {n : ℕ} (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (active : Finset (Fin n)) (v : ℝ) (cutoff : Fin n → ℝ) {q epsilon : ℝ}
    (hcard_tail : (active.card : ℝ) * q < epsilon)
    (hupper :
      ∀ c ∈ active,
        AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff c - v) ≤ q) :
    cutoffAffordanceProbability (Measure.pi (fun _ : Fin n => noiseLaw))
        active v cutoff < epsilon :=
  lt_of_le_of_lt
    (cutoffAffordanceProbability_iidProduct_le_card_mul_of_upperTailMass_le
      noiseLaw active v cutoff hupper)
    hcard_tail

/--
High-endpoint iid product bridge: if the product of single-college
no-crossing probabilities is below `epsilon`, then the active-set affordance
probability is above `1 - epsilon`.
-/
theorem cutoffAffordanceProbability_iidProduct_gt_one_sub_of_prod_lowerCDFMass_lt
    {n : ℕ} (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (active : Finset (Fin n)) (v : ℝ) (cutoff : Fin n → ℝ) {epsilon : ℝ}
    (hprod :
      (∏ c ∈ active,
        AppliedModelingLib.Probability.lowerCDFMass noiseLaw (cutoff c - v)) <
        epsilon) :
    1 - epsilon <
      cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseLaw)) active v cutoff := by
  rw [cutoffAffordanceProbability]
  rw [AppliedModelingLib.Matching.cutoffCrossingProbability_iidProduct_eq_one_sub_prod_lowerCDFMass]
  linarith

/--
Finite product reduction for the high-endpoint no-crossing clause.  If every
factor is a probability and one active college already has no-crossing mass
below `epsilon`, then the whole no-crossing product is below `epsilon`.
-/
theorem prod_lt_of_exists_lt_of_nonneg_le_one
    {ι : Type*} [DecidableEq ι] (active : Finset ι) (f : ι → ℝ)
    {epsilon : ℝ}
    (hexists : ∃ c ∈ active, f c < epsilon)
    (hnonneg : ∀ c ∈ active, 0 ≤ f c)
    (hle_one : ∀ c ∈ active, f c ≤ 1) :
    (∏ c ∈ active, f c) < epsilon := by
  rcases hexists with ⟨c, hc, hlt⟩
  have hprod_nonneg :
      0 ≤ ∏ x ∈ active \ {c}, f x := by
    exact Finset.prod_nonneg fun x hx =>
      hnonneg x (Finset.mem_sdiff.mp hx).1
  have hprod_le_one :
      (∏ x ∈ active \ {c}, f x) ≤ 1 := by
    exact Finset.prod_le_one
      (fun x hx => hnonneg x (Finset.mem_sdiff.mp hx).1)
      (fun x hx => hle_one x (Finset.mem_sdiff.mp hx).1)
  have hprod_eq :
      (∏ x ∈ active, f x) = f c * ∏ x ∈ active \ {c}, f x := by
    rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem hc]
  calc
    (∏ x ∈ active, f x) = f c * ∏ x ∈ active \ {c}, f x := hprod_eq
    _ ≤ f c := by
      exact mul_le_of_le_one_right (hnonneg c hc) hprod_le_one
    _ < epsilon := hlt

/--
High-endpoint iid product bridge from a one-college no-crossing estimate.
This exposes a smaller source endpoint condition than the full lower-CDF
product: one sufficiently favorable college in the active set already makes
the probability of affording some active college exceed `1 - epsilon`.
-/
theorem cutoffAffordanceProbability_iidProduct_gt_one_sub_of_exists_lowerCDFMass_lt
    {n : ℕ} (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (active : Finset (Fin n)) (v : ℝ) (cutoff : Fin n → ℝ) {epsilon : ℝ}
    (hexists :
      ∃ c ∈ active,
        AppliedModelingLib.Probability.lowerCDFMass noiseLaw (cutoff c - v) <
          epsilon) :
    1 - epsilon <
      cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseLaw)) active v cutoff := by
  refine
    cutoffAffordanceProbability_iidProduct_gt_one_sub_of_prod_lowerCDFMass_lt
      noiseLaw active v cutoff ?_
  exact
    prod_lt_of_exists_lt_of_nonneg_le_one active
      (fun c => AppliedModelingLib.Probability.lowerCDFMass noiseLaw (cutoff c - v))
      hexists
      (fun c _hc => AppliedModelingLib.Probability.lowerCDFMass_nonneg noiseLaw _)
      (fun c _hc => AppliedModelingLib.Probability.lowerCDFMass_le_one noiseLaw _)

/--
Convert a high single-college crossing probability into the corresponding
small lower-CDF no-crossing probability.
-/
theorem lowerCDFMass_lt_of_one_sub_lt_upperTailMass
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {x epsilon : ℝ}
    (h : 1 - epsilon <
      AppliedModelingLib.Probability.upperTailMass noiseLaw x) :
    AppliedModelingLib.Probability.lowerCDFMass noiseLaw x < epsilon := by
  have hsum :=
    AppliedModelingLib.Probability.lowerCDFMass_add_upperTailMass_eq_one noiseLaw x
  linarith

/--
High-endpoint iid product bridge from a one-college upper-tail crossing
estimate.  This is the direct probability form of the source proof: if one
active college is affordable with probability above `1 - epsilon`, then the
probability of affording some active college is also above `1 - epsilon`.
-/
theorem cutoffAffordanceProbability_iidProduct_gt_one_sub_of_exists_upperTailMass_gt_one_sub
    {n : ℕ} (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (active : Finset (Fin n)) (v : ℝ) (cutoff : Fin n → ℝ) {epsilon : ℝ}
    (hexists :
      ∃ c ∈ active,
        1 - epsilon <
          AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff c - v)) :
    1 - epsilon <
      cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseLaw)) active v cutoff := by
  refine
    cutoffAffordanceProbability_iidProduct_gt_one_sub_of_exists_lowerCDFMass_lt
      noiseLaw active v cutoff ?_
  rcases hexists with ⟨c, hc, htail⟩
  exact ⟨c, hc,
    lowerCDFMass_lt_of_one_sub_lt_upperTailMass noiseLaw htail⟩

/--
Independent at-least-one affordability is monotone in pointwise
single-college crossing probabilities, as long as the larger crossing
probabilities are still at most one.
-/
theorem independentAffordanceProbability_mono_of_pointwise_le
    {College : Type v} (active : Finset College)
    {qLow qHigh : College → ℝ}
    (hpointwise : ∀ c ∈ active, qLow c ≤ qHigh c)
    (hhigh_le_one : ∀ c ∈ active, qHigh c ≤ 1) :
    independentAffordanceProbability active qLow ≤
      independentAffordanceProbability active qHigh := by
  have hprod :
      (∏ c ∈ active, (1 - qHigh c)) ≤
        ∏ c ∈ active, (1 - qLow c) := by
    exact Finset.prod_le_prod
      (fun c hc => by linarith [hhigh_le_one c hc])
      (fun c hc => by linarith [hpointwise c hc])
  dsimp [independentAffordanceProbability]
  linarith

/--
Independent at-least-one affordability dominates the standard exponential
lower bound when every active single-college crossing probability is at least
`q`.
-/
theorem independentAffordanceProbability_ge_one_sub_exp_neg_card_mul
    {College : Type v} (active : Finset College)
    {crossingProbability : College → ℝ} {q : ℝ}
    (hq_nonneg : 0 ≤ q) (hq_le_one : q ≤ 1)
    (hlower : ∀ c ∈ active, q ≤ crossingProbability c)
    (hle_one : ∀ c ∈ active, crossingProbability c ≤ 1) :
    1 - Real.exp (-((active.card : ℝ) * q)) ≤
      independentAffordanceProbability active crossingProbability := by
  have hconst_le :
      independentAffordanceProbability active (fun _ : College => q) ≤
        independentAffordanceProbability active crossingProbability :=
    independentAffordanceProbability_mono_of_pointwise_le
      active hlower hle_one
  have hconst :
      independentAffordanceProbability active (fun _ : College => q) =
        AppliedModelingLib.Probability.Bernoulli.atLeastOneValue q active.card := by
    simp [independentAffordanceProbability,
      AppliedModelingLib.Probability.Bernoulli.atLeastOneValue]
  exact le_trans
    (by
      simpa [hconst] using
        AppliedModelingLib.Probability.Bernoulli.one_sub_exp_neg_mul_le_atLeastOneValue
          active.card hq_nonneg hq_le_one)
    hconst_le

/--
Strict form of the exponential lower bound for independent at-least-one
affordance.
-/
theorem lt_independentAffordanceProbability_of_lt_one_sub_exp_neg_card_mul
    {College : Type v} (active : Finset College)
    {crossingProbability : College → ℝ} {q target : ℝ}
    (htarget : target < 1 - Real.exp (-((active.card : ℝ) * q)))
    (hq_nonneg : 0 ≤ q) (hq_le_one : q ≤ 1)
    (hlower : ∀ c ∈ active, q ≤ crossingProbability c)
    (hle_one : ∀ c ∈ active, crossingProbability c ≤ 1) :
    target < independentAffordanceProbability active crossingProbability :=
  lt_of_lt_of_le htarget
    (independentAffordanceProbability_ge_one_sub_exp_neg_card_mul
      active hq_nonneg hq_le_one hlower hle_one)

/--
Iid cutoff affordability dominates the exponential lower bound when every
active upper-tail crossing probability is at least `q`.
-/
theorem cutoffAffordanceProbability_iidProduct_ge_one_sub_exp_neg_card_mul_of_upperTailMass_ge
    {n : ℕ} (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (active : Finset (Fin n)) (v : ℝ) (cutoff : Fin n → ℝ) {q : ℝ}
    (hq_nonneg : 0 ≤ q) (hq_le_one : q ≤ 1)
    (hlower :
      ∀ c ∈ active,
        q ≤ AppliedModelingLib.Probability.upperTailMass noiseLaw
          (cutoff c - v)) :
    1 - Real.exp (-((active.card : ℝ) * q)) ≤
      cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin n => noiseLaw)) active v cutoff := by
  rw [
    cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass]
  exact
    independentAffordanceProbability_ge_one_sub_exp_neg_card_mul
      active hq_nonneg hq_le_one hlower
      (fun c _hc => AppliedModelingLib.Probability.upperTailMass_le_one noiseLaw _)

/--
Scaled strict form of the iid-product exponential lower bound.  This is the
finite product step used by the PG24 first-large-index capacity-overflow
argument.
-/
theorem lt_scaled_cutoffAffordanceProbability_iidProduct_of_lt_scaled_one_sub_exp_neg_card_mul
    {n : ℕ} (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (active : Finset (Fin n)) (v : ℝ) (cutoff : Fin n → ℝ)
    {scale q target : ℝ}
    (hscale_nonneg : 0 ≤ scale)
    (htarget :
      target < scale *
        (1 - Real.exp (-((active.card : ℝ) * q))))
    (hq_nonneg : 0 ≤ q) (hq_le_one : q ≤ 1)
    (hlower :
      ∀ c ∈ active,
        q ≤ AppliedModelingLib.Probability.upperTailMass noiseLaw
          (cutoff c - v)) :
    target <
      scale *
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) active v cutoff := by
  have hprod :
      1 - Real.exp (-((active.card : ℝ) * q)) ≤
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) active v cutoff :=
    cutoffAffordanceProbability_iidProduct_ge_one_sub_exp_neg_card_mul_of_upperTailMass_ge
      noiseLaw active v cutoff hq_nonneg hq_le_one hlower
  exact lt_of_lt_of_le htarget
    (mul_le_mul_of_nonneg_left hprod hscale_nonneg)

/--
Finite first-large-index overflow algebra.  If a split cutoff has high-value
tail at least `qSplit`, every prefix cutoff is weakly below that split cutoff,
and the low/high tail comparison gives a `(1 - ε)` transfer on the prefix,
then the iid prefix affordability is large enough to exceed `totalSupply`
whenever the corresponding exponential lower bound does.
-/
theorem theorem2_prefix_capacity_overflow_of_split_tail_ratio
    {n : ℕ} (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (active : Finset (Fin n)) (split : Fin n)
    (vLow vHigh : ℝ) (cutoff : Fin n → ℝ)
    {epsilon qSplit totalSupply : ℝ}
    (hscale_nonneg : 0 ≤ 1 - epsilon)
    (hqSplit_nonneg : 0 ≤ qSplit)
    (hq_le_one : (1 - epsilon) * qSplit ≤ 1)
    (htarget :
      totalSupply <
        (1 - epsilon) *
          (1 - Real.exp
            (-((active.card : ℝ) * ((1 - epsilon) * qSplit)))))
    (hprefix_order :
      ∀ c ∈ active, cutoff c ≤ cutoff split)
    (htail_ratio :
      ∀ c ∈ active,
        (1 - epsilon) *
            AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoff c - vHigh) ≤
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff c - vLow))
    (hsplit_tail :
      qSplit ≤
        AppliedModelingLib.Probability.upperTailMass noiseLaw
          (cutoff split - vHigh)) :
    totalSupply <
      (1 - epsilon) *
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) active vLow cutoff := by
  refine
    lt_scaled_cutoffAffordanceProbability_iidProduct_of_lt_scaled_one_sub_exp_neg_card_mul
      noiseLaw active vLow cutoff
      (scale := 1 - epsilon)
      (q := (1 - epsilon) * qSplit)
      hscale_nonneg htarget ?_ hq_le_one ?_
  · exact mul_nonneg hscale_nonneg hqSplit_nonneg
  · intro c hc
    have hsplit_le_c :
        AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff split - vHigh) ≤
          AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff c - vHigh) :=
      AppliedModelingLib.Probability.upperTailMass_antitone noiseLaw
        (sub_le_sub_right (hprefix_order c hc) vHigh)
    have hhigh :
        qSplit ≤
          AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff c - vHigh) :=
      le_trans hsplit_tail hsplit_le_c
    exact le_trans
      (mul_le_mul_of_nonneg_left hhigh hscale_nonneg)
      (htail_ratio c hc)

/--
Specialized first-large-index form of
`theorem2_prefix_capacity_overflow_of_split_tail_ratio`, with the paper's
`sigma / (C + 1)` threshold and sorted-prefix split.
-/
theorem theorem2_first_large_index_capacity_overflow_implication_of_product_tail_ratio
    {C : ℕ} (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoff : Fin (C + 1) → ℝ) {epsilon sigma totalSupply vLow vHigh : ℝ}
    (hsplit : epsilonFloorSplitIndex epsilon C < C + 1)
    (hscale_nonneg : 0 ≤ 1 - epsilon)
    (hsigma_nonneg : 0 ≤ sigma)
    (hq_le_one :
      (1 - epsilon) * (sigma / ((C + 1 : ℕ) : ℝ)) ≤ 1)
    (htarget :
      totalSupply <
        (1 - epsilon) *
          (1 - Real.exp
            (-(((indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C).card :
                ℝ) *
              ((1 - epsilon) *
                (sigma / ((C + 1 : ℕ) : ℝ)))))))
    (hprefix_order :
      ∀ c ∈ indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C,
        cutoff c ≤ cutoff
          (⟨epsilonFloorSplitIndex epsilon C, hsplit⟩ : Fin (C + 1)))
    (htail_ratio :
      ∀ c ∈ indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C,
        (1 - epsilon) *
            AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoff c - vHigh) ≤
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff c - vLow))
    (hsplit_tail :
      sigma / ((C + 1 : ℕ) : ℝ) <
        AppliedModelingLib.Probability.upperTailMass noiseLaw
          (cutoff
            (⟨epsilonFloorSplitIndex epsilon C, hsplit⟩ : Fin (C + 1)) -
            vHigh)) :
    totalSupply <
      (1 - epsilon) *
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
          vLow cutoff := by
  have hden_pos : 0 < (((C + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos C
  have hq_nonneg :
      0 ≤ sigma / ((C + 1 : ℕ) : ℝ) :=
    div_nonneg hsigma_nonneg (le_of_lt hden_pos)
  exact
    theorem2_prefix_capacity_overflow_of_split_tail_ratio
      noiseLaw
      (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
      (⟨epsilonFloorSplitIndex epsilon C, hsplit⟩ : Fin (C + 1))
      vLow vHigh cutoff
      (epsilon := epsilon)
      (qSplit := sigma / ((C + 1 : ℕ) : ℝ))
      (totalSupply := totalSupply)
      hscale_nonneg hq_nonneg hq_le_one htarget hprefix_order
      htail_ratio (le_of_lt hsplit_tail)

/--
The scaled first-large-index one-college probability threshold is eventually
at most one.  This is finite asymptotic bookkeeping, not a paper source
assumption.
-/
theorem theorem2_eventually_scaled_sigma_div_succ_le_one
    (epsilon sigma : ℝ) :
    ∀ᶠ C : ℕ in atTop,
      (1 - epsilon) * (sigma / ((C + 1 : ℕ) : ℝ)) ≤ 1 := by
  have hhalf :=
    pg24_eventually_const_div_nat_succ_le_half ((1 - epsilon) * sigma)
  filter_upwards [hhalf] with C hC
  have hrewrite :
      (1 - epsilon) * (sigma / ((C + 1 : ℕ) : ℝ)) =
        ((1 - epsilon) * sigma) / ((C + 1 : ℕ) : ℝ) := by
    ring
  rw [hrewrite]
  linarith

/--
Independent at-least-one affordability is monotone in the active college set
when all single-college crossing probabilities lie in `[0,1]`.
-/
theorem independentAffordanceProbability_mono_active
    {College : Type v} {active larger : Finset College}
    {q : College → ℝ}
    (hsubset : active ⊆ larger)
    (hq_nonneg : ∀ c ∈ larger, 0 ≤ q c)
    (hq_le_one : ∀ c ∈ larger, q c ≤ 1) :
    independentAffordanceProbability active q ≤
      independentAffordanceProbability larger q := by
  have hprod :
      (∏ c ∈ larger, (1 - q c)) ≤
        ∏ c ∈ active, (1 - q c) := by
    exact Finset.prod_le_prod_of_subset_of_le_one
      hsubset
      (fun c hc => by linarith [hq_le_one c hc])
      (fun c hc _hnot => by linarith [hq_nonneg c hc])
  dsimp [independentAffordanceProbability]
  linarith

/--
Independent at-least-one affordability is monotone in student value when every
single-college crossing probability is monotone in value.
-/
theorem independentAffordanceProbability_mono_value
    {College : Type v} (active : Finset College)
    {crossingProbability : ℝ → College → ℝ}
    (hpointwise_mono :
      ∀ c ∈ active, Monotone (fun v => crossingProbability v c))
    (hle_one :
      ∀ v c, c ∈ active → crossingProbability v c ≤ 1) :
    Monotone (fun v => independentAffordanceProbability active
      (crossingProbability v)) := by
  intro v w hvw
  exact independentAffordanceProbability_mono_of_pointwise_le
    active
    (fun c hc => hpointwise_mono c hc hvw)
    (fun c hc => hle_one w c hc)

/--
For a survival function, single-college crossing probabilities
`survival (cutoff - value)` are monotone in the student's value whenever the
survival function is antitone.
-/
theorem independentAffordanceProbability_mono_value_of_antitone_survival
    {College : Type v} (active : Finset College)
    {survival : ℝ → ℝ} {cutoff : College → ℝ}
    (hsurvival_antitone : Antitone survival)
    (hle_one :
      ∀ v c, c ∈ active → survival (cutoff c - v) ≤ 1) :
    Monotone (fun v : ℝ =>
      independentAffordanceProbability active
        (fun c => survival (cutoff c - v))) := by
  refine independentAffordanceProbability_mono_value active ?_ hle_one
  intro c hc v w hvw
  exact hsurvival_antitone (by linarith : cutoff c - w ≤ cutoff c - v)

/--
Single-college algebra used in the long-tail amplification proof.  If the
low-value crossing probability is at least `(1 - ε)` times the high-value
crossing probability, then the high/low failure ratio is at least any scalar
known to be below the corresponding `(1 - qHigh)/(1 - (1 - ε) qHigh)` bound.
-/
theorem failureRatio_floor_of_tailRatio_floor
    {qLow qHigh ε floor : ℝ}
    (hqHigh_le_one : qHigh ≤ 1)
    (hfloor :
      floor ≤ (1 - qHigh) / (1 - (1 - ε) * qHigh))
    (htail : (1 - ε) * qHigh ≤ qLow)
    (hlow_failure_pos : 0 < 1 - qLow) :
    floor ≤ (1 - qHigh) / (1 - qLow) := by
  have hden_le : 1 - qLow ≤ 1 - (1 - ε) * qHigh := by
    linarith
  have href_pos : 0 < 1 - (1 - ε) * qHigh := by
    exact lt_of_lt_of_le hlow_failure_pos hden_le
  have hnum_nonneg : 0 ≤ 1 - qHigh := by
    linarith
  have hratio_mono :
      (1 - qHigh) / (1 - (1 - ε) * qHigh) ≤
        (1 - qHigh) / (1 - qLow) :=
    div_le_div_of_nonneg_left hnum_nonneg hlow_failure_pos hden_le
  exact le_trans hfloor hratio_mono

/--
Division-form variant of `failureRatio_floor_of_tailRatio_floor`, matching the
paper's statement of long-tailedness as a low/high tail-probability ratio.
-/
theorem failureRatio_floor_of_tailRatio_div_floor
    {qLow qHigh ε floor : ℝ}
    (hqHigh_pos : 0 < qHigh) (hqHigh_le_one : qHigh ≤ 1)
    (hfloor :
      floor ≤ (1 - qHigh) / (1 - (1 - ε) * qHigh))
    (htail_ratio : 1 - ε ≤ qLow / qHigh)
    (hlow_failure_pos : 0 < 1 - qLow) :
    floor ≤ (1 - qHigh) / (1 - qLow) := by
  have htail : (1 - ε) * qHigh ≤ qLow := by
    have hmul :=
      mul_le_mul_of_nonneg_right htail_ratio hqHigh_pos.le
    simpa [div_mul_cancel₀ qLow (ne_of_gt hqHigh_pos),
      mul_comm, mul_left_comm, mul_assoc] using hmul
  exact failureRatio_floor_of_tailRatio_floor
    hqHigh_le_one hfloor htail hlow_failure_pos

/--
PG24 Proposition `lt-approx-F2`, product-comparison core.  If every
single-college high-value failure divided by its low-value failure is bounded
below by `exp (-(2 ε σ)/C)`, and the active set has at most `C` colleges, then
the high-value at-least-one affordability probability exceeds the low-value
one by at most `1 - exp (-2 ε σ)`.
-/
theorem independentAffordanceProbability_difference_le_exp_error
    {College : Type v} (active : Finset College)
    (qLow qHigh : College → ℝ) {C : ℕ} {ε σ : ℝ}
    (hε_nonneg : 0 ≤ ε) (hσ_nonneg : 0 ≤ σ)
    (hC_pos : 0 < (C : ℝ))
    (hcard : (active.card : ℝ) ≤ (C : ℝ))
    (hratio :
      ∀ c ∈ active,
        Real.exp (-(2 * ε * σ / (C : ℝ))) ≤
          (1 - qHigh c) / (1 - qLow c))
    (hlow_failure_pos : ∀ c ∈ active, 0 < 1 - qLow c)
    (hlow_failure_le_one : ∀ c ∈ active, 1 - qLow c ≤ 1) :
    independentAffordanceProbability active qHigh -
        independentAffordanceProbability active qLow ≤
      1 - Real.exp (-(2 * ε * σ)) := by
  have hA_nonneg : 0 ≤ 2 * ε * σ := by nlinarith
  have hprod_floor :
      Real.exp (-(2 * ε * σ)) ≤
        ∏ _c ∈ active, Real.exp (-(2 * ε * σ / (C : ℝ))) := by
    simpa [div_eq_mul_inv, mul_assoc] using
      AppliedModelingLib.Math.exp_neg_le_finset_prod_const_exp_neg_div_of_card_le
        (s := active) (A := 2 * ε * σ) (C := (C : ℝ))
        hA_nonneg hC_pos hcard
  have hglobal_le_one :
      Real.exp (-(2 * ε * σ)) ≤ 1 := by
    simpa using
      (Real.exp_le_exp.mpr (by nlinarith : -(2 * ε * σ) ≤ (0 : ℝ)))
  let lowProd : ℝ := ∏ c ∈ active, (1 - qLow c)
  let highProd : ℝ := ∏ c ∈ active, (1 - qHigh c)
  let ratioProd : ℝ :=
    ∏ c ∈ active, (1 - qHigh c) / (1 - qLow c)
  have hlow_nonneg : ∀ c ∈ active, 0 ≤ 1 - qLow c :=
    fun c hc => (hlow_failure_pos c hc).le
  have hlowProd_pos : 0 < lowProd := by
    dsimp [lowProd]
    exact Finset.prod_pos hlow_failure_pos
  have hlowProd_le_one : lowProd ≤ 1 := by
    dsimp [lowProd]
    exact Finset.prod_le_one hlow_nonneg hlow_failure_le_one
  have hfloor_le_ratioProd :
      Real.exp (-(2 * ε * σ)) ≤ ratioProd := by
    calc
      Real.exp (-(2 * ε * σ)) ≤
          ∏ c ∈ active, Real.exp (-(2 * ε * σ / (C : ℝ))) :=
        hprod_floor
      _ ≤ ratioProd := by
        dsimp [ratioProd]
        exact Finset.prod_le_prod (fun c hc => (Real.exp_pos _).le) hratio
  have hratioProd_eq : ratioProd = highProd / lowProd := by
    dsimp [ratioProd, highProd, lowProd]
    exact Finset.prod_div_distrib (s := active)
      (f := fun c => 1 - qHigh c) (g := fun c => 1 - qLow c)
  have hfloor_le_div :
      Real.exp (-(2 * ε * σ)) ≤ highProd / lowProd := by
    simpa [hratioProd_eq] using hfloor_le_ratioProd
  have hmul :
      Real.exp (-(2 * ε * σ)) * lowProd ≤ highProd := by
    have h :=
      mul_le_mul_of_nonneg_right hfloor_le_div hlowProd_pos.le
    have hcancel :
        highProd / lowProd * lowProd = highProd := by
      exact div_mul_cancel₀ highProd (ne_of_gt hlowProd_pos)
    simpa [hcancel] using h
  have hdiff :
      lowProd - highProd ≤
        lowProd - Real.exp (-(2 * ε * σ)) * lowProd :=
    sub_le_sub_left hmul lowProd
  have hfactor :
      lowProd - Real.exp (-(2 * ε * σ)) * lowProd =
        (1 - Real.exp (-(2 * ε * σ))) * lowProd := by
    ring
  have hscale :
      (1 - Real.exp (-(2 * ε * σ))) * lowProd ≤
        1 - Real.exp (-(2 * ε * σ)) := by
    exact mul_le_of_le_one_right (sub_nonneg.mpr hglobal_le_one)
      hlowProd_le_one
  have hproduct :
      (∏ c ∈ active, (1 - qLow c)) -
          (∏ c ∈ active, (1 - qHigh c)) ≤
        1 - Real.exp (-(2 * ε * σ)) := by
    calc
      (∏ c ∈ active, (1 - qLow c)) -
          (∏ c ∈ active, (1 - qHigh c)) =
          lowProd - highProd := by rfl
      _ ≤ lowProd - Real.exp (-(2 * ε * σ)) * lowProd := hdiff
      _ = (1 - Real.exp (-(2 * ε * σ))) * lowProd := hfactor
      _ ≤ 1 - Real.exp (-(2 * ε * σ)) := hscale
  simpa [independentAffordanceProbability, sub_eq_add_neg, add_comm,
    add_left_comm, add_assoc] using hproduct

/--
Eventual form of the product-comparison core for growing college sets.  This
is the formal counterpart of applying the `lt-approx-F2` product estimate once
the long-tail and small-crossing bounds hold for all sufficiently large `C`.
-/
theorem independentAffordanceProbability_difference_eventually_le_exp_error
    {active : ∀ n : ℕ, Finset (Fin (n + 1))}
    {qLow qHigh : ∀ n : ℕ, Fin (n + 1) → ℝ}
    {ε σ : ℝ}
    (hε_nonneg : 0 ≤ ε) (hσ_nonneg : 0 ≤ σ)
    (hratio :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ active n,
          Real.exp (-(2 * ε * σ / ((n + 1 : ℕ) : ℝ))) ≤
            (1 - qHigh n c) / (1 - qLow n c))
    (hlow_failure_pos :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ active n, 0 < 1 - qLow n c)
    (hlow_failure_le_one :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ active n, 1 - qLow n c ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      independentAffordanceProbability (active n) (qHigh n) -
          independentAffordanceProbability (active n) (qLow n) ≤
        1 - Real.exp (-(2 * ε * σ)) := by
  filter_upwards [hratio, hlow_failure_pos, hlow_failure_le_one] with
    n hn_ratio hn_low_pos hn_low_le_one
  have hC_pos : 0 < (((n + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos n
  have hcard : ((active n).card : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) := by
    have hcard_nat : (active n).card ≤ Fintype.card (Fin (n + 1)) :=
      Finset.card_le_univ (s := active n)
    simpa using (show ((active n).card : ℝ) ≤
        ((Fintype.card (Fin (n + 1))) : ℝ) from by
      exact_mod_cast hcard_nat)
  exact
    independentAffordanceProbability_difference_le_exp_error
      (active n) (qLow n) (qHigh n)
      (C := n + 1) hε_nonneg hσ_nonneg hC_pos hcard
      hn_ratio hn_low_pos hn_low_le_one

/--
Long-tail route to the `lt-approx-F2` product estimate.  The long-tailed
survival condition supplies the low/high tail-ratio bound uniformly over the
active colleges; the remaining scalar floor is the elementary "C large enough"
inequality from the source proof.
-/
theorem independentAffordanceProbability_difference_eventually_le_exp_error_of_longTailed
    {survival : ℝ → ℝ} (hlong : LongTailedSurvival survival)
    {active : ∀ n : ℕ, Finset (Fin (n + 1))}
    {cutoff : ∀ n : ℕ, Fin (n + 1) → ℝ}
    {lowerCutoff : ℕ → ℝ} {vLow vHigh ε σ : ℝ}
    (hv : vLow < vHigh) (hε : 0 < ε) (hσ_nonneg : 0 ≤ σ)
    (hlower_atTop :
      Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop)
    (hcutoff_lower :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ active n, lowerCutoff n ≤ cutoff n c)
    (hhigh_pos :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ active n, 0 < survival (cutoff n c - vHigh))
    (hhigh_le_one :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ active n, survival (cutoff n c - vHigh) ≤ 1)
    (hscalar_floor :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ active n,
          Real.exp (-(2 * ε * σ / ((n + 1 : ℕ) : ℝ))) ≤
            (1 - survival (cutoff n c - vHigh)) /
              (1 - (1 - ε) * survival (cutoff n c - vHigh)))
    (hlow_failure_pos :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ active n, 0 < 1 - survival (cutoff n c - vLow))
    (hlow_failure_le_one :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ active n, 1 - survival (cutoff n c - vLow) ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      independentAffordanceProbability
          (active n) (fun c => survival (cutoff n c - vHigh)) -
        independentAffordanceProbability
          (active n) (fun c => survival (cutoff n c - vLow)) ≤
        1 - Real.exp (-(2 * ε * σ)) := by
  have htail_ratio :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ active n,
          1 - ε < survival (cutoff n c - vLow) /
            survival (cutoff n c - vHigh) :=
    LongTailedSurvival.eventually_uniform_value_ratio_gt_of_cutoff_lower_bound
      hlong hv hε hlower_atTop hcutoff_lower
  filter_upwards
    [htail_ratio, hhigh_pos, hhigh_le_one, hscalar_floor,
      hlow_failure_pos, hlow_failure_le_one] with
    n hn_tail hn_high_pos hn_high_le_one hn_floor hn_low_pos hn_low_le_one
  have hC_pos : 0 < (((n + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos n
  have hcard : ((active n).card : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) := by
    have hcard_nat : (active n).card ≤ Fintype.card (Fin (n + 1)) :=
      Finset.card_le_univ (s := active n)
    simpa using (show ((active n).card : ℝ) ≤
        ((Fintype.card (Fin (n + 1))) : ℝ) from by
      exact_mod_cast hcard_nat)
  have hratio :
      ∀ c ∈ active n,
        Real.exp (-(2 * ε * σ / ((n + 1 : ℕ) : ℝ))) ≤
          (1 - survival (cutoff n c - vHigh)) /
            (1 - survival (cutoff n c - vLow)) := by
    intro c hc
    exact
      failureRatio_floor_of_tailRatio_div_floor
        (hqHigh_pos := hn_high_pos c hc)
        (hqHigh_le_one := hn_high_le_one c hc)
        (hfloor := hn_floor c hc)
        (htail_ratio := le_of_lt (hn_tail c hc))
        (hlow_failure_pos := hn_low_pos c hc)
  exact
    independentAffordanceProbability_difference_le_exp_error
      (active n)
      (fun c => survival (cutoff n c - vLow))
      (fun c => survival (cutoff n c - vHigh))
      (C := n + 1) hε.le hσ_nonneg hC_pos hcard hratio
      hn_low_pos hn_low_le_one

/--
Long-tail route with the scalar floor derived from the explicit high-value
crossing-probability bound.  This is the paper proof's "large enough market"
step: once every high-value single-college crossing probability is at most
`σ / (n + 1)` and that quantity is at most one half, the elementary
exponential floor used by `lt-approx-F2` follows without an extra premise.
-/
theorem independentAffordanceProbability_difference_eventually_le_exp_error_of_longTailed_highCrossingBound
    {survival : ℝ → ℝ} (hlong : LongTailedSurvival survival)
    {active : ∀ n : ℕ, Finset (Fin (n + 1))}
    {cutoff : ∀ n : ℕ, Fin (n + 1) → ℝ}
    {lowerCutoff : ℕ → ℝ} {vLow vHigh ε σ : ℝ}
    (hv : vLow < vHigh) (hε : 0 < ε) (hε_le_one : ε ≤ 1)
    (hσ_nonneg : 0 ≤ σ)
    (hlower_atTop :
      Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop)
    (hcutoff_lower :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ active n, lowerCutoff n ≤ cutoff n c)
    (hhigh_pos :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ active n, 0 < survival (cutoff n c - vHigh))
    (hhigh_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ active n,
          survival (cutoff n c - vHigh) ≤
            σ / ((n + 1 : ℕ) : ℝ))
    (hlow_failure_pos :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ active n, 0 < 1 - survival (cutoff n c - vLow)) :
    ∀ᶠ n : ℕ in atTop,
      independentAffordanceProbability
          (active n) (fun c => survival (cutoff n c - vHigh)) -
        independentAffordanceProbability
          (active n) (fun c => survival (cutoff n c - vLow)) ≤
        1 - Real.exp (-(2 * ε * σ)) := by
  have hsmall :
      ∀ᶠ n : ℕ in atTop,
        σ / ((n + 1 : ℕ) : ℝ) ≤ 1 / 2 :=
    pg24_eventually_const_div_nat_succ_le_half σ
  have hhigh_le_one :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ active n, survival (cutoff n c - vHigh) ≤ 1 := by
    filter_upwards [hhigh_le_sigma_div, hsmall] with n hn_bound hn_small c hc
    have hq_half :
        survival (cutoff n c - vHigh) ≤ 1 / 2 :=
      le_trans (hn_bound c hc) hn_small
    linarith
  have hscalar_floor :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ active n,
          Real.exp (-(2 * ε * σ / ((n + 1 : ℕ) : ℝ))) ≤
            (1 - survival (cutoff n c - vHigh)) /
              (1 - (1 - ε) * survival (cutoff n c - vHigh)) := by
    filter_upwards [hhigh_pos, hhigh_le_sigma_div, hsmall] with
      n hn_pos hn_bound hn_small c hc
    have hC_pos : 0 < (((n + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_pos n
    have hq_half :
        survival (cutoff n c - vHigh) ≤ 1 / 2 :=
      le_trans (hn_bound c hc) hn_small
    exact
      AppliedModelingLib.Math.exp_neg_two_mul_mul_div_le_one_sub_div_one_sub_one_sub_mul
        (epsilon := ε) (sigma := σ) (C := ((n + 1 : ℕ) : ℝ))
        (q := survival (cutoff n c - vHigh))
        hε.le hε_le_one hσ_nonneg hC_pos
        (le_of_lt (hn_pos c hc)) hq_half (hn_bound c hc)
  have htail_ratio :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ active n,
          1 - ε < survival (cutoff n c - vLow) /
            survival (cutoff n c - vHigh) :=
    LongTailedSurvival.eventually_uniform_value_ratio_gt_of_cutoff_lower_bound
      hlong hv hε hlower_atTop hcutoff_lower
  have hlow_failure_le_one :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ active n, 1 - survival (cutoff n c - vLow) ≤ 1 := by
    filter_upwards [htail_ratio, hhigh_pos] with n hn_tail hn_high_pos c hc
    have hone_sub_nonneg : 0 ≤ 1 - ε := by
      linarith
    have hratio_pos :
        0 < survival (cutoff n c - vLow) /
          survival (cutoff n c - vHigh) :=
      lt_of_le_of_lt hone_sub_nonneg (hn_tail c hc)
    have hlow_pos : 0 < survival (cutoff n c - vLow) := by
      have hmul :=
        mul_pos hratio_pos (hn_high_pos c hc)
      simpa [div_mul_cancel₀ _ (ne_of_gt (hn_high_pos c hc))] using hmul
    linarith
  exact
    independentAffordanceProbability_difference_eventually_le_exp_error_of_longTailed
      hlong hv hε hσ_nonneg hlower_atTop hcutoff_lower hhigh_pos
      hhigh_le_one hscalar_floor hlow_failure_pos hlow_failure_le_one

/--
Uniform-in-admissible-matchings version of the long-tail product estimate.
This is the form needed by PG24 because Theorem 2 quantifies over every
admissible stable matching once the market is sufficiently large.
-/
theorem independentAffordanceProbability_difference_uniform_eventually_le_exp_error_of_longTailed_highCrossingBound
    {Admissible : ℕ → Type*}
    {survival : ℝ → ℝ} (hlong : LongTailedSurvival survival)
    {active : ∀ n : ℕ, Admissible n → Finset (Fin (n + 1))}
    {cutoff : ∀ n : ℕ, Admissible n → Fin (n + 1) → ℝ}
    {lowerCutoff : ℕ → ℝ} {vLow vHigh ε σ : ℝ}
    (hv : vLow < vHigh) (hε : 0 < ε) (hε_le_one : ε ≤ 1)
    (hσ_nonneg : 0 ≤ σ)
    (hlower_atTop :
      Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop)
    (hcutoff_lower :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n, ∀ c ∈ active n μ,
          lowerCutoff n ≤ cutoff n μ c)
    (hhigh_pos :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n, ∀ c ∈ active n μ,
          0 < survival (cutoff n μ c - vHigh))
    (hhigh_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n, ∀ c ∈ active n μ,
          survival (cutoff n μ c - vHigh) ≤
            σ / ((n + 1 : ℕ) : ℝ))
    (hlow_failure_pos :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n, ∀ c ∈ active n μ,
          0 < 1 - survival (cutoff n μ c - vLow)) :
    ∀ᶠ n : ℕ in atTop,
      ∀ μ : Admissible n,
        independentAffordanceProbability
            (active n μ) (fun c => survival (cutoff n μ c - vHigh)) -
          independentAffordanceProbability
            (active n μ) (fun c => survival (cutoff n μ c - vLow)) ≤
          1 - Real.exp (-(2 * ε * σ)) := by
  let d : ℝ := vHigh - vLow
  have hd : 0 < d := by
    dsimp [d]
    linarith
  rcases Filter.eventually_atTop.1
      (LongTailedSurvival.eventually_ratio_gt hlong hd hε) with
    ⟨x0, hx0⟩
  have hlower_ge :
      ∀ᶠ n : ℕ in atTop, x0 ≤ lowerCutoff n - vHigh :=
    hlower_atTop (Filter.eventually_atTop.2 ⟨x0, fun x hx => hx⟩)
  have hsmall :
      ∀ᶠ n : ℕ in atTop,
        σ / ((n + 1 : ℕ) : ℝ) ≤ 1 / 2 :=
    pg24_eventually_const_div_nat_succ_le_half σ
  filter_upwards
    [hlower_ge, hcutoff_lower, hhigh_pos, hhigh_le_sigma_div,
      hlow_failure_pos, hsmall] with
    n hn_ge hn_cutoff hn_high_pos hn_high_bound hn_low_pos hn_small μ
  have hC_pos : 0 < (((n + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos n
  have hcard : ((active n μ).card : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) := by
    have hcard_nat : (active n μ).card ≤ Fintype.card (Fin (n + 1)) :=
      Finset.card_le_univ (s := active n μ)
    simpa using (show ((active n μ).card : ℝ) ≤
        ((Fintype.card (Fin (n + 1))) : ℝ) from by
      exact_mod_cast hcard_nat)
  have hhigh_le_one :
      ∀ c ∈ active n μ, survival (cutoff n μ c - vHigh) ≤ 1 := by
    intro c hc
    have hq_half :
        survival (cutoff n μ c - vHigh) ≤ 1 / 2 :=
      le_trans (hn_high_bound μ c hc) hn_small
    linarith
  have hscalar_floor :
      ∀ c ∈ active n μ,
        Real.exp (-(2 * ε * σ / ((n + 1 : ℕ) : ℝ))) ≤
          (1 - survival (cutoff n μ c - vHigh)) /
            (1 - (1 - ε) * survival (cutoff n μ c - vHigh)) := by
    intro c hc
    have hq_half :
        survival (cutoff n μ c - vHigh) ≤ 1 / 2 :=
      le_trans (hn_high_bound μ c hc) hn_small
    exact
      AppliedModelingLib.Math.exp_neg_two_mul_mul_div_le_one_sub_div_one_sub_one_sub_mul
        (epsilon := ε) (sigma := σ) (C := ((n + 1 : ℕ) : ℝ))
        (q := survival (cutoff n μ c - vHigh))
        hε.le hε_le_one hσ_nonneg hC_pos
        (le_of_lt (hn_high_pos μ c hc)) hq_half (hn_high_bound μ c hc)
  have htail_ratio :
      ∀ c ∈ active n μ,
        1 - ε < survival (cutoff n μ c - vLow) /
          survival (cutoff n μ c - vHigh) := by
    intro c hc
    have hx_ge : x0 ≤ cutoff n μ c - vHigh := by
      have hcut := hn_cutoff μ c hc
      linarith
    have hratio :
        1 - ε <
          survival ((cutoff n μ c - vHigh) + d) /
            survival (cutoff n μ c - vHigh) :=
      hx0 (cutoff n μ c - vHigh) hx_ge
    simpa [d, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hratio
  have hlow_failure_le_one :
      ∀ c ∈ active n μ, 1 - survival (cutoff n μ c - vLow) ≤ 1 := by
    intro c hc
    have hone_sub_nonneg : 0 ≤ 1 - ε := by
      linarith
    have hratio_pos :
        0 < survival (cutoff n μ c - vLow) /
          survival (cutoff n μ c - vHigh) :=
      lt_of_le_of_lt hone_sub_nonneg (htail_ratio c hc)
    have hlow_pos : 0 < survival (cutoff n μ c - vLow) := by
      have hmul :=
        mul_pos hratio_pos (hn_high_pos μ c hc)
      simpa [div_mul_cancel₀ _ (ne_of_gt (hn_high_pos μ c hc))] using hmul
    linarith
  have hratio :
      ∀ c ∈ active n μ,
        Real.exp (-(2 * ε * σ / ((n + 1 : ℕ) : ℝ))) ≤
          (1 - survival (cutoff n μ c - vHigh)) /
            (1 - survival (cutoff n μ c - vLow)) := by
    intro c hc
    exact
      failureRatio_floor_of_tailRatio_div_floor
        (hqHigh_pos := hn_high_pos μ c hc)
        (hqHigh_le_one := hhigh_le_one c hc)
        (hfloor := hscalar_floor c hc)
        (htail_ratio := le_of_lt (htail_ratio c hc))
        (hlow_failure_pos := hn_low_pos μ c hc)
  exact
    independentAffordanceProbability_difference_le_exp_error
      (active n μ)
      (fun c => survival (cutoff n μ c - vLow))
      (fun c => survival (cutoff n μ c - vHigh))
      (C := n + 1) hε.le hσ_nonneg hC_pos hcard hratio
      (hn_low_pos μ) hlow_failure_le_one

/--
Upper-tail specialized long-tail product estimate.

Compared with
`independentAffordanceProbability_difference_uniform_eventually_le_exp_error_of_longTailed_highCrossingBound`,
this version does not require a separate common lower-cutoff divergence
premise.  For real upper-tail probabilities, the high-value bound
`Pr[X > cutoff-vHigh] <= sigma/(n+1)` and long-tailed positivity force every
non-vacuous admissible high endpoint eventually into the tail region where the
long-tail ratio applies.
-/
theorem independentAffordanceProbability_difference_uniform_eventually_le_exp_error_of_upperTailMass_longTailed_highCrossingBound
    {Admissible : ℕ → Type*}
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {active : ∀ n : ℕ, Admissible n → Finset (Fin (n + 1))}
    {cutoff : ∀ n : ℕ, Admissible n → Fin (n + 1) → ℝ}
    {vLow vHigh ε σ : ℝ}
    (hv : vLow < vHigh) (hε : 0 < ε) (hε_le_one : ε ≤ 1)
    (hσ_nonneg : 0 ≤ σ)
    (hhigh_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n, ∀ c ∈ active n μ,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoff n μ c - vHigh) ≤
            σ / ((n + 1 : ℕ) : ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      ∀ μ : Admissible n,
        independentAffordanceProbability
            (active n μ)
            (fun c =>
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff n μ c - vHigh)) -
          independentAffordanceProbability
            (active n μ)
            (fun c =>
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff n μ c - vLow)) ≤
          1 - Real.exp (-(2 * ε * σ)) := by
  let survival : ℝ → ℝ := AppliedModelingLib.Probability.upperTailMass noiseLaw
  let d : ℝ := vHigh - vLow
  have hd : 0 < d := by
    dsimp [d]
    linarith
  rcases Filter.eventually_atTop.1
      (LongTailedSurvival.eventually_ratio_gt hlong hd hε) with
    ⟨x0, hx0⟩
  have htail_pos_atTop :
      ∀ᶠ x : ℝ in atTop, 0 < survival x :=
    hlong.eventually_pos
      (fun x => AppliedModelingLib.Probability.upperTailMass_nonneg noiseLaw x)
  rcases Filter.eventually_atTop.1 htail_pos_atTop with
    ⟨posFloor, hposFloor⟩
  have htail_lt_one_atTop :
      ∀ᶠ x : ℝ in atTop, survival x < 1 :=
    AppliedModelingLib.Probability.eventually_upperTailMass_lt_one_atTop noiseLaw
  rcases Filter.eventually_atTop.1 htail_lt_one_atTop with
    ⟨oneFloor, honeFloor⟩
  let floor : ℝ := max x0 (max posFloor oneFloor)
  have hx0_floor : x0 ≤ floor := by
    dsimp [floor]
    exact le_max_left _ _
  have hpos_floor : posFloor ≤ floor := by
    dsimp [floor]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hone_floor : oneFloor ≤ floor := by
    dsimp [floor]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have htail_floor_pos : 0 < survival floor :=
    hposFloor floor hpos_floor
  have hsmall_tail :
      ∀ᶠ n : ℕ in atTop,
        σ / ((n + 1 : ℕ) : ℝ) < survival floor := by
    have hlim :
        Tendsto (fun n : ℕ => σ / (((n + 1 : ℕ) : ℝ)))
          atTop (nhds 0) :=
      Filter.Tendsto.const_div_atTop pg24_tendsto_nat_succ_cast_atTop σ
    exact hlim (isOpen_Iio.mem_nhds htail_floor_pos)
  have hsmall :
      ∀ᶠ n : ℕ in atTop,
        σ / ((n + 1 : ℕ) : ℝ) ≤ 1 / 2 :=
    pg24_eventually_const_div_nat_succ_le_half σ
  filter_upwards [hhigh_le_sigma_div, hsmall_tail, hsmall] with
    n hn_high_bound hn_tail_small hn_small μ
  have hC_pos : 0 < (((n + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos n
  have hcard : ((active n μ).card : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) := by
    have hcard_nat : (active n μ).card ≤ Fintype.card (Fin (n + 1)) :=
      Finset.card_le_univ (s := active n μ)
    simpa using (show ((active n μ).card : ℝ) ≤
        ((Fintype.card (Fin (n + 1))) : ℝ) from by
      exact_mod_cast hcard_nat)
  have hfloor_le_high :
      ∀ c ∈ active n μ, floor ≤ cutoff n μ c - vHigh := by
    intro c hc
    by_contra hnot
    have hx_lt : cutoff n μ c - vHigh < floor := lt_of_not_ge hnot
    have htail_floor_le :
        survival floor ≤ survival (cutoff n μ c - vHigh) :=
      AppliedModelingLib.Probability.upperTailMass_antitone noiseLaw
        (le_of_lt hx_lt)
    have htail_x_lt :
        survival (cutoff n μ c - vHigh) < survival floor :=
      lt_of_le_of_lt (hn_high_bound μ c hc) hn_tail_small
    exact (not_lt_of_ge htail_floor_le) htail_x_lt
  have hhigh_pos :
      ∀ c ∈ active n μ, 0 < survival (cutoff n μ c - vHigh) := by
    intro c hc
    exact hposFloor (cutoff n μ c - vHigh)
      (le_trans hpos_floor (hfloor_le_high c hc))
  have hhigh_le_one :
      ∀ c ∈ active n μ, survival (cutoff n μ c - vHigh) ≤ 1 := by
    intro c hc
    have hq_half :
        survival (cutoff n μ c - vHigh) ≤ 1 / 2 :=
      le_trans (hn_high_bound μ c hc) hn_small
    linarith
  have hscalar_floor :
      ∀ c ∈ active n μ,
        Real.exp (-(2 * ε * σ / ((n + 1 : ℕ) : ℝ))) ≤
          (1 - survival (cutoff n μ c - vHigh)) /
            (1 - (1 - ε) * survival (cutoff n μ c - vHigh)) := by
    intro c hc
    have hq_half :
        survival (cutoff n μ c - vHigh) ≤ 1 / 2 :=
      le_trans (hn_high_bound μ c hc) hn_small
    exact
      AppliedModelingLib.Math.exp_neg_two_mul_mul_div_le_one_sub_div_one_sub_one_sub_mul
        (epsilon := ε) (sigma := σ) (C := ((n + 1 : ℕ) : ℝ))
        (q := survival (cutoff n μ c - vHigh))
        hε.le hε_le_one hσ_nonneg hC_pos
        (le_of_lt (hhigh_pos c hc)) hq_half (hn_high_bound μ c hc)
  have htail_ratio :
      ∀ c ∈ active n μ,
        1 - ε < survival (cutoff n μ c - vLow) /
          survival (cutoff n μ c - vHigh) := by
    intro c hc
    have hx_ge : x0 ≤ cutoff n μ c - vHigh :=
      le_trans hx0_floor (hfloor_le_high c hc)
    have hratio :
        1 - ε <
          survival ((cutoff n μ c - vHigh) + d) /
            survival (cutoff n μ c - vHigh) :=
      hx0 (cutoff n μ c - vHigh) hx_ge
    simpa [survival, d, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
      using hratio
  have hlow_failure_pos :
      ∀ c ∈ active n μ, 0 < 1 - survival (cutoff n μ c - vLow) := by
    intro c hc
    have hlow_ge : oneFloor ≤ cutoff n μ c - vLow := by
      have hhigh_ge := hfloor_le_high c hc
      linarith
    have hlt_one : survival (cutoff n μ c - vLow) < 1 :=
      honeFloor (cutoff n μ c - vLow) hlow_ge
    linarith
  have hlow_failure_le_one :
      ∀ c ∈ active n μ, 1 - survival (cutoff n μ c - vLow) ≤ 1 := by
    intro c hc
    have hnonneg :
        0 ≤ survival (cutoff n μ c - vLow) :=
      AppliedModelingLib.Probability.upperTailMass_nonneg noiseLaw _
    linarith
  have hratio :
      ∀ c ∈ active n μ,
        Real.exp (-(2 * ε * σ / ((n + 1 : ℕ) : ℝ))) ≤
          (1 - survival (cutoff n μ c - vHigh)) /
            (1 - survival (cutoff n μ c - vLow)) := by
    intro c hc
    exact
      failureRatio_floor_of_tailRatio_div_floor
        (hqHigh_pos := hhigh_pos c hc)
        (hqHigh_le_one := hhigh_le_one c hc)
        (hfloor := hscalar_floor c hc)
        (htail_ratio := le_of_lt (htail_ratio c hc))
        (hlow_failure_pos := hlow_failure_pos c hc)
  exact
    independentAffordanceProbability_difference_le_exp_error
      (active n μ)
      (fun c => survival (cutoff n μ c - vLow))
      (fun c => survival (cutoff n μ c - vHigh))
      (C := n + 1) hε.le hσ_nonneg hC_pos hcard hratio
      hlow_failure_pos hlow_failure_le_one

/--
PG24 Theorem 2, large-firm interval algebra.  If the large-firm affordance
probability is monotone in value, its endpoint values are squeezed around
total supply, and the high/low endpoint gap is at most the long-tail product
error, then every intermediate value lies in the source interval from
Proposition `lt-large-firms`.
-/
theorem theorem2_largeFirm_interval_of_endpoint_product_error
    {pLarge : ℝ → ℝ} {vLow vHigh v S α ε σ : ℝ}
    (hp_mono : Monotone pLarge)
    (hvLow : vLow ≤ v) (hvHigh : v ≤ vHigh)
    (hupper_low : pLarge vLow ≤ S + ε)
    (hlower_high : S - (1 + α) * ε ≤ pLarge vHigh)
    (hdiff :
      pLarge vHigh - pLarge vLow ≤
        1 - Real.exp (-(2 * ε * σ))) :
    S - (1 + α) * ε - (1 - Real.exp (-(2 * ε * σ))) ≤
        pLarge v ∧
      pLarge v ≤ S + ε + (1 - Real.exp (-(2 * ε * σ))) := by
  have hlow_mono : pLarge vLow ≤ pLarge v := hp_mono hvLow
  have hhigh_mono : pLarge v ≤ pLarge vHigh := hp_mono hvHigh
  constructor
  · linarith
  · linarith

/--
Large-firm source-window predicate from the endpoint/product estimate.  This
is the same algebra as `theorem2_largeFirm_interval_of_endpoint_product_error`,
restated in the source-window predicate used by the final Theorem 2 closure.
-/
theorem theorem2_largeFirmSourceWindow_of_endpoint_product_error
    {pLarge : ℝ → ℝ} {vLow vHigh v S α ε σ : ℝ}
    (hp_mono : Monotone pLarge)
    (hvLow : vLow ≤ v) (hvHigh : v ≤ vHigh)
    (hupper_low : pLarge vLow ≤ S + ε)
    (hlower_high : S - (1 + α) * ε ≤ pLarge vHigh)
    (hdiff :
      pLarge vHigh - pLarge vLow ≤
        1 - Real.exp (-(2 * ε * σ))) :
    theorem2_largeFirmSourceWindow S α ε σ (pLarge v) := by
  have hinterval :=
    theorem2_largeFirm_interval_of_endpoint_product_error
      (pLarge := pLarge)
      hp_mono hvLow hvHigh hupper_low hlower_high hdiff
  constructor
  · dsimp [theorem2_sourceLowerError]
    linarith [hinterval.1]
  · exact hinterval.2

/--
Scalar endpoint algebra used in the PG24 large-firm proof: if the interval
mass is at least `1 - epsilon`, then
`(1 - epsilon) * p(v_-) <= S` implies `p(v_-) < S + epsilon`, provided
`S + epsilon < 1`.
-/
theorem theorem2_lowEndpoint_upper_of_interval_mass_bound
    {pLow S ε : ℝ}
    (hε_pos : 0 < ε)
    (hS_nonneg : 0 ≤ S)
    (hS_eps_lt_one : S + ε < 1)
    (hmass_upper : (1 - ε) * pLow ≤ S) :
    pLow ≤ S + ε := by
  have hden_pos : 0 < 1 - ε := by linarith
  have hp_div : pLow ≤ S / (1 - ε) := by
    rw [le_div_iff₀ hden_pos]
    simpa [mul_comm] using hmass_upper
  have hdiv_lt : S / (1 - ε) < S + ε := by
    rw [div_lt_iff₀ hden_pos]
    nlinarith [mul_pos hε_pos (by linarith : 0 < 1 - S - ε)]
  exact le_trans hp_div (le_of_lt hdiv_lt)

/--
Large-firm source window from the endpoint estimates exactly visible in the
paper proof.  The low endpoint comes from the interval-mass/capacity bound,
the high endpoint from the capacity-loss estimate, and the endpoint gap from
`lt-approx-F2`.
-/
theorem theorem2_largeFirmSourceWindow_of_source_endpoint_estimates
    {pLarge : ℝ → ℝ} {vLow vHigh v S α ε σ : ℝ}
    (hp_mono : Monotone pLarge)
    (hvLow : vLow ≤ v) (hvHigh : v ≤ vHigh)
    (hε_pos : 0 < ε)
    (hS_nonneg : 0 ≤ S)
    (hS_eps_lt_one : S + ε < 1)
    (hmass_upper : (1 - ε) * pLarge vLow ≤ S)
    (hlower_high : S - α * ε - ε ≤ pLarge vHigh)
    (hdiff :
      pLarge vHigh - pLarge vLow ≤
        1 - Real.exp (-(2 * ε * σ))) :
    theorem2_largeFirmSourceWindow S α ε σ (pLarge v) := by
  have hupper_low : pLarge vLow ≤ S + ε :=
    theorem2_lowEndpoint_upper_of_interval_mass_bound
      hε_pos hS_nonneg hS_eps_lt_one hmass_upper
  have hlower_high' : S - (1 + α) * ε ≤ pLarge vHigh := by
    linarith
  exact
    theorem2_largeFirmSourceWindow_of_endpoint_product_error
      (pLarge := pLarge) hp_mono hvLow hvHigh
      hupper_low hlower_high' hdiff

/--
Two-scale lower-side error for the repaired PG24 Theorem 2 route.

The split size `delta` controls the small/large college partition and endpoint
capacity losses.  The long-tail ratio tolerance `rho` controls only the
independent-product error.  Keeping these parameters separate matches the
appendix argument more faithfully than using one epsilon for both roles.
-/
noncomputable def theorem2_twoScaleSourceLowerError
    (alpha delta rho sigma : ℝ) : ℝ :=
  (1 + alpha) * delta + (1 - Real.exp (-(2 * rho * sigma)))

/--
Two-scale upper-side error for the repaired PG24 Theorem 2 route.
-/
noncomputable def theorem2_twoScaleSourceUpperError
    (totalSupply alpha delta rho sigma : ℝ) : ℝ :=
  delta + (1 - Real.exp (-(2 * rho * sigma))) +
    alpha * Real.sqrt delta /
      (1 - totalSupply - delta - (1 - Real.exp (-(2 * rho * sigma))))

/--
Large-firm source-window predicate for the two-scale route.
-/
def theorem2_twoScaleLargeFirmSourceWindow
    (totalSupply alpha delta rho sigma p : ℝ) : Prop :=
  totalSupply -
        theorem2_twoScaleSourceLowerError alpha delta rho sigma ≤ p ∧
    p ≤ totalSupply + delta + (1 - Real.exp (-(2 * rho * sigma)))

/--
Small-firm source bound for the two-scale route.
-/
def theorem2_twoScaleSmallFirmSourceBound
    (totalSupply alpha delta rho sigma p : ℝ) : Prop :=
  p ≤
    alpha * Real.sqrt delta /
      (1 - totalSupply - delta - (1 - Real.exp (-(2 * rho * sigma))))

/--
Two-scale small-firm scalar algebra.  The proof is the same division step as
`theorem2_smallFirmSourceBound_of_capacity_mass_lower_bound`, with `delta`
controlling the small block and `rho * sigma` controlling the product error.
-/
theorem theorem2_twoScaleSmallFirmSourceBound_of_capacity_mass_lower_bound
    {totalSupply alpha delta rho sigma p : ℝ}
    (hdelta_pos : 0 < delta)
    (hden_pos :
      0 <
        1 - totalSupply - delta -
          (1 - Real.exp (-(2 * rho * sigma))))
    (hcapacity_mass :
      Real.sqrt delta *
          (1 - totalSupply - delta -
            (1 - Real.exp (-(2 * rho * sigma)))) * p ≤
        delta * alpha) :
    theorem2_twoScaleSmallFirmSourceBound
      totalSupply alpha delta rho sigma p := by
  let denom : ℝ :=
    1 - totalSupply - delta -
      (1 - Real.exp (-(2 * rho * sigma)))
  have hdenom_pos : 0 < denom := by
    simpa [denom] using hden_pos
  have hsqrt_pos : 0 < Real.sqrt delta :=
    Real.sqrt_pos.mpr hdelta_pos
  have hmul_pos : 0 < Real.sqrt delta * denom :=
    mul_pos hsqrt_pos hdenom_pos
  have hdiv :
      p ≤ (delta * alpha) / (Real.sqrt delta * denom) := by
    rw [le_div_iff₀ hmul_pos]
    simpa [mul_assoc, mul_comm, mul_left_comm, denom] using hcapacity_mass
  have hrewrite :
      (delta * alpha) / (Real.sqrt delta * denom) =
        alpha * Real.sqrt delta / denom := by
    field_simp [ne_of_gt hsqrt_pos, ne_of_gt hdenom_pos]
    rw [Real.sq_sqrt hdelta_pos.le]
    ring
  simpa [theorem2_twoScaleSmallFirmSourceBound, denom, hrewrite] using hdiv

/--
Two-scale small-firm bound from the active-capacity comparison.
-/
theorem theorem2_twoScaleSmallFirmSourceBound_of_star_active_capacity_lower_bound
    {College : Type v}
    (active : Finset College) (capacity : College → ℝ)
    {pSmall : ℝ → ℝ} {v vStar totalSupply alpha delta rho sigma : ℝ} {C : ℕ}
    (hdelta_pos : 0 < delta)
    (hden_pos :
      0 <
        1 - totalSupply - delta -
          (1 - Real.exp (-(2 * rho * sigma))))
    (hp_mono : Monotone pSmall)
    (hv : v ≤ vStar)
    (hcard : (active.card : ℝ) ≤ delta * (C : ℝ))
    (halpha_nonneg : 0 ≤ alpha) (hC_pos : 0 < (C : ℝ))
    (hcap : ∀ c ∈ active, capacity c ≤ alpha / (C : ℝ))
    (hlower :
      Real.sqrt delta *
          (1 - totalSupply - delta -
            (1 - Real.exp (-(2 * rho * sigma)))) *
          pSmall vStar ≤
        AppliedModelingLib.Matching.activeCapacity active capacity) :
    theorem2_twoScaleSmallFirmSourceBound
      totalSupply alpha delta rho sigma (pSmall v) := by
  have hcapacity_mass :
      Real.sqrt delta *
          (1 - totalSupply - delta -
            (1 - Real.exp (-(2 * rho * sigma)))) *
          pSmall vStar ≤
        delta * alpha :=
    le_trans hlower
      (smallActiveSet_capacity_le_epsilon_mul_alpha
        active capacity hcard halpha_nonneg hC_pos hcap)
  have hstar :
      theorem2_twoScaleSmallFirmSourceBound
        totalSupply alpha delta rho sigma (pSmall vStar) :=
    theorem2_twoScaleSmallFirmSourceBound_of_capacity_mass_lower_bound
      hdelta_pos hden_pos hcapacity_mass
  exact le_trans (hp_mono hv) hstar

/--
Eventual two-scale small-firm bound from the active-capacity comparison, for
the finite-market `Fin (C+1)` representation used by PG24.
-/
theorem theorem2_twoScaleSmallFirmSourceBound_eventually_of_star_active_capacity_lower_bound
    {Admissible : ℕ → Type*}
    (small : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1)))
    (capacity : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ)
    {pSmall : ∀ C : ℕ, Admissible C → ℝ → ℝ}
    {v vStar totalSupply alpha delta rho sigma : ℝ}
    (hdelta_pos : 0 < delta)
    (hden_pos :
      0 <
        1 - totalSupply - delta -
          (1 - Real.exp (-(2 * rho * sigma))))
    (hp_mono :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C, Monotone (pSmall C μ))
    (hv : v ≤ vStar)
    (hcard :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          ((small C μ).card : ℝ) ≤ delta * ((C + 1 : ℕ) : ℝ))
    (halpha_nonneg : 0 ≤ alpha)
    (hcap :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C, ∀ c ∈ small C μ,
          capacity C μ c ≤ alpha / ((C + 1 : ℕ) : ℝ))
    (hlower :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          Real.sqrt delta *
              (1 - totalSupply - delta -
                (1 - Real.exp (-(2 * rho * sigma)))) *
              pSmall C μ vStar ≤
            AppliedModelingLib.Matching.activeCapacity (small C μ) (capacity C μ)) :
    ∀ᶠ C : ℕ in atTop,
      ∀ μ : Admissible C,
        theorem2_twoScaleSmallFirmSourceBound
          totalSupply alpha delta rho sigma (pSmall C μ v) := by
  filter_upwards [hp_mono, hcard, hcap, hlower] with
    C hmonoC hcardC hcapC hlowerC μ
  have hC_pos : 0 < (((C + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos C
  exact
    theorem2_twoScaleSmallFirmSourceBound_of_star_active_capacity_lower_bound
      (small C μ) (capacity C μ)
      hdelta_pos hden_pos (hmonoC μ) hv (hcardC μ)
      halpha_nonneg hC_pos (hcapC μ) (hlowerC μ)

/--
Two-scale large-firm endpoint algebra.  This is the same argument as
`theorem2_largeFirm_interval_of_endpoint_product_error`, but with the
large/small split size separated from the long-tail ratio tolerance.
-/
theorem theorem2_twoScaleLargeFirm_interval_of_endpoint_product_error
    {pLarge : ℝ → ℝ} {vLow vHigh v S α delta rho sigma : ℝ}
    (hp_mono : Monotone pLarge)
    (hvLow : vLow ≤ v) (hvHigh : v ≤ vHigh)
    (hupper_low : pLarge vLow ≤ S + delta)
    (hlower_high : S - α * delta - delta ≤ pLarge vHigh)
    (hdiff :
      pLarge vHigh - pLarge vLow ≤
        1 - Real.exp (-(2 * rho * sigma))) :
    S - theorem2_twoScaleSourceLowerError α delta rho sigma ≤
        pLarge v ∧
      pLarge v ≤ S + delta + (1 - Real.exp (-(2 * rho * sigma))) := by
  have hlow_mono : pLarge vLow ≤ pLarge v := hp_mono hvLow
  have hhigh_mono : pLarge v ≤ pLarge vHigh := hp_mono hvHigh
  constructor
  · dsimp [theorem2_twoScaleSourceLowerError]
    linarith
  · linarith

/--
Two-scale large-firm source window from the endpoint estimates in the paper
proof.  The endpoint capacity losses use `delta`; the product gap uses
`rho * sigma`.
-/
theorem theorem2_twoScaleLargeFirmSourceWindow_of_source_endpoint_estimates
    {pLarge : ℝ → ℝ} {vLow vHigh v S α delta rho sigma : ℝ}
    (hp_mono : Monotone pLarge)
    (hvLow : vLow ≤ v) (hvHigh : v ≤ vHigh)
    (hdelta_pos : 0 < delta)
    (hS_nonneg : 0 ≤ S)
    (hS_delta_lt_one : S + delta < 1)
    (hmass_upper : (1 - delta) * pLarge vLow ≤ S)
    (hlower_high : S - α * delta - delta ≤ pLarge vHigh)
    (hdiff :
      pLarge vHigh - pLarge vLow ≤
        1 - Real.exp (-(2 * rho * sigma))) :
    theorem2_twoScaleLargeFirmSourceWindow
      S α delta rho sigma (pLarge v) := by
  have hupper_low : pLarge vLow ≤ S + delta :=
    theorem2_lowEndpoint_upper_of_interval_mass_bound
      hdelta_pos hS_nonneg hS_delta_lt_one hmass_upper
  exact
    theorem2_twoScaleLargeFirm_interval_of_endpoint_product_error
      (pLarge := pLarge) hp_mono hvLow hvHigh
      hupper_low hlower_high hdiff

/--
Pointwise final `C1/C2` algebra for the two-scale route.
-/
theorem theorem2_twoScaleSourceWindow_of_large_small_firm_bounds
    {pTotal pSmall pLarge totalSupply alpha delta rho sigma : ℝ}
    (hlarge :
      theorem2_twoScaleLargeFirmSourceWindow
        totalSupply alpha delta rho sigma pLarge)
    (hsmall :
      theorem2_twoScaleSmallFirmSourceBound
        totalSupply alpha delta rho sigma pSmall)
    (hlarge_le_total : pLarge ≤ pTotal)
    (htotal_le_sum : pTotal ≤ pSmall + pLarge) :
    totalSupply -
          theorem2_twoScaleSourceLowerError alpha delta rho sigma ≤
        pTotal ∧
      pTotal ≤
        totalSupply +
          theorem2_twoScaleSourceUpperError
            totalSupply alpha delta rho sigma := by
  constructor
  · exact le_trans hlarge.1 hlarge_le_total
  · dsimp [theorem2_twoScaleSourceUpperError,
      theorem2_twoScaleSmallFirmSourceBound] at hsmall ⊢
    linarith [hlarge.2, hsmall, htotal_le_sum]

/--
Eventual finite-market two-scale source-window construction from large- and
small-firm bounds plus the usual `C1/C2` decomposition inequalities.
-/
theorem theorem2_uniform_twoScale_source_window_eventually_of_large_small_firm_bounds
    {Admissible : ℕ → Type*}
    {pTotal pSmall pLarge : ∀ C : ℕ, Admissible C → ℝ → ℝ}
    {v totalSupply alpha delta rho sigma : ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          theorem2_twoScaleLargeFirmSourceWindow
            totalSupply alpha delta rho sigma (pLarge C μ v))
    (hsmall :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          theorem2_twoScaleSmallFirmSourceBound
            totalSupply alpha delta rho sigma (pSmall C μ v))
    (hlarge_le_total :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C, pLarge C μ v ≤ pTotal C μ v)
    (htotal_le_sum :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          pTotal C μ v ≤ pSmall C μ v + pLarge C μ v) :
    ∀ᶠ C : ℕ in atTop,
      ∀ μ : Admissible C,
        totalSupply -
              theorem2_twoScaleSourceLowerError alpha delta rho sigma ≤
            pTotal C μ v ∧
          pTotal C μ v ≤
            totalSupply +
              theorem2_twoScaleSourceUpperError
                totalSupply alpha delta rho sigma := by
  filter_upwards [hlarge, hsmall, hlarge_le_total, htotal_le_sum] with
    C hlargeC hsmallC hleC hsumC μ
  exact
    theorem2_twoScaleSourceWindow_of_large_small_firm_bounds
      (hlargeC μ) (hsmallC μ) (hleC μ) (hsumC μ)

/--
Theorem 2 closure from two-scale source-shaped long-tail windows.

This is the repaired top-level closure: the source may choose a split size,
a long-tail ratio tolerance, and a high-tail-rate constant for each target
tolerance.  Lean only requires that the displayed two-scale lower and upper
errors are below the target tolerance and that the corresponding source window
holds eventually.
-/
theorem theorem2_uniformAmplification_of_twoScale_eventual_source_window
    {Admissible : ℕ → Type*} {matchProb : ∀ C, Admissible C → ℝ → ℝ}
    {totalSupply : ℝ}
    (hwindow :
      ∀ v tol, 0 < tol →
        ∃ alpha delta rho sigma : ℝ,
          theorem2_twoScaleSourceLowerError alpha delta rho sigma < tol ∧
          theorem2_twoScaleSourceUpperError
              totalSupply alpha delta rho sigma < tol ∧
          ∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              totalSupply -
                    theorem2_twoScaleSourceLowerError
                      alpha delta rho sigma ≤
                  matchProb C μ v ∧
                matchProb C μ v ≤
                  totalSupply +
                    theorem2_twoScaleSourceUpperError
                      totalSupply alpha delta rho sigma) :
    theorem2_uniformAmplificationConclusion Admissible matchProb totalSupply := by
  intro v tol htol
  rcases hwindow v tol htol with
    ⟨alpha, delta, rho, sigma, hlower_small, hupper_small, hevent⟩
  filter_upwards [hevent] with C hC μ
  have hμ := hC μ
  rw [abs_sub_lt_iff]
  constructor <;> linarith

/--
Theorem 2 closure directly from two-scale large- and small-firm source
windows plus the final `C1/C2` decomposition.
-/
theorem theorem2_uniformAmplification_of_twoScale_large_small_source_windows
    {Admissible : ℕ → Type*}
    {pTotal pSmall pLarge : ∀ C : ℕ, Admissible C → ℝ → ℝ}
    {totalSupply : ℝ}
    (hsource :
      ∀ v tol, 0 < tol →
        ∃ alpha delta rho sigma : ℝ,
          theorem2_twoScaleSourceLowerError alpha delta rho sigma < tol ∧
          theorem2_twoScaleSourceUpperError
              totalSupply alpha delta rho sigma < tol ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              theorem2_twoScaleLargeFirmSourceWindow
                totalSupply alpha delta rho sigma (pLarge C μ v)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              theorem2_twoScaleSmallFirmSourceBound
                totalSupply alpha delta rho sigma (pSmall C μ v)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, pLarge C μ v ≤ pTotal C μ v) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              pTotal C μ v ≤ pSmall C μ v + pLarge C μ v)) :
    theorem2_uniformAmplificationConclusion Admissible pTotal totalSupply := by
  refine theorem2_uniformAmplification_of_twoScale_eventual_source_window ?_
  intro v tol htol
  rcases hsource v tol htol with
    ⟨alpha, delta, rho, sigma, hlower_small, hupper_small,
      hlarge, hsmall, hlarge_le_total, htotal_le_sum⟩
  refine ⟨alpha, delta, rho, sigma, hlower_small, hupper_small, ?_⟩
  exact
    theorem2_uniform_twoScale_source_window_eventually_of_large_small_firm_bounds
      (Admissible := Admissible)
      (pTotal := pTotal) (pSmall := pSmall) (pLarge := pLarge)
      (v := v) (totalSupply := totalSupply)
      (alpha := alpha) (delta := delta) (rho := rho) (sigma := sigma)
      hlarge hsmall hlarge_le_total htotal_le_sum

/--
Eventual large-firm source window from the source endpoint estimates.  This
is the market-asymptotic form of Proposition `lt-large-firms`.
-/
theorem theorem2_largeFirmSourceWindow_eventually_of_source_endpoint_estimates
    {pLarge : ℕ → ℝ → ℝ} {vLow vHigh v S α ε σ : ℝ}
    (hp_mono : ∀ᶠ C : ℕ in atTop, Monotone (pLarge C))
    (hvLow : vLow ≤ v) (hvHigh : v ≤ vHigh)
    (hε_pos : 0 < ε)
    (hS_nonneg : 0 ≤ S)
    (hS_eps_lt_one : S + ε < 1)
    (hmass_upper :
      ∀ᶠ C : ℕ in atTop, (1 - ε) * pLarge C vLow ≤ S)
    (hlower_high :
      ∀ᶠ C : ℕ in atTop, S - α * ε - ε ≤ pLarge C vHigh)
    (hdiff :
      ∀ᶠ C : ℕ in atTop,
        pLarge C vHigh - pLarge C vLow ≤
          1 - Real.exp (-(2 * ε * σ))) :
    ∀ᶠ C : ℕ in atTop,
      theorem2_largeFirmSourceWindow S α ε σ (pLarge C v) := by
  filter_upwards [hp_mono, hmass_upper, hlower_high, hdiff] with
    C hmono hmass hhigh hgap
  exact
    theorem2_largeFirmSourceWindow_of_source_endpoint_estimates
      (pLarge := pLarge C) hmono hvLow hvHigh
      hε_pos hS_nonneg hS_eps_lt_one hmass hhigh hgap

/--
Large-firm source window with the long-tail product gap derived internally.
This combines the `lt-approx-F2` long-tail product estimate with the
endpoint/capacity estimates used in Proposition `lt-large-firms`.
-/
theorem theorem2_largeFirmSourceWindow_eventually_of_longTail_source_endpoint_estimates
    {survival : ℝ → ℝ} (hlong : LongTailedSurvival survival)
    {active : ∀ n : ℕ, Finset (Fin (n + 1))}
    {cutoff : ∀ n : ℕ, Fin (n + 1) → ℝ}
    {lowerCutoff : ℕ → ℝ}
    {vLow vHigh v S α ε σ : ℝ}
    (hp_mono :
      ∀ᶠ n : ℕ in atTop,
        Monotone (fun w : ℝ =>
          independentAffordanceProbability
            (active n) (fun c => survival (cutoff n c - w))))
    (hvLow : vLow ≤ v) (hvHigh : v ≤ vHigh)
    (hvStrict : vLow < vHigh)
    (hε_pos : 0 < ε) (hε_le_one : ε ≤ 1)
    (hS_nonneg : 0 ≤ S) (hS_eps_lt_one : S + ε < 1)
    (hσ_nonneg : 0 ≤ σ)
    (hlower_atTop :
      Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop)
    (hcutoff_lower :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ active n, lowerCutoff n ≤ cutoff n c)
    (hhigh_pos :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ active n, 0 < survival (cutoff n c - vHigh))
    (hhigh_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ active n,
          survival (cutoff n c - vHigh) ≤
            σ / ((n + 1 : ℕ) : ℝ))
    (hlow_failure_pos :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ active n, 0 < 1 - survival (cutoff n c - vLow))
    (hmass_upper :
      ∀ᶠ n : ℕ in atTop,
        (1 - ε) *
            independentAffordanceProbability
              (active n) (fun c => survival (cutoff n c - vLow)) ≤ S)
    (hlower_high :
      ∀ᶠ n : ℕ in atTop,
        S - α * ε - ε ≤
          independentAffordanceProbability
            (active n) (fun c => survival (cutoff n c - vHigh))) :
    ∀ᶠ n : ℕ in atTop,
      theorem2_largeFirmSourceWindow S α ε σ
        (independentAffordanceProbability
          (active n) (fun c => survival (cutoff n c - v))) := by
  have hdiff :
      ∀ᶠ n : ℕ in atTop,
        independentAffordanceProbability
            (active n) (fun c => survival (cutoff n c - vHigh)) -
          independentAffordanceProbability
            (active n) (fun c => survival (cutoff n c - vLow)) ≤
          1 - Real.exp (-(2 * ε * σ)) :=
    independentAffordanceProbability_difference_eventually_le_exp_error_of_longTailed_highCrossingBound
      hlong hvStrict hε_pos hε_le_one hσ_nonneg hlower_atTop hcutoff_lower
      hhigh_pos hhigh_le_sigma_div hlow_failure_pos
  exact
    theorem2_largeFirmSourceWindow_eventually_of_source_endpoint_estimates
      (pLarge := fun n : ℕ => fun w : ℝ =>
        independentAffordanceProbability
          (active n) (fun c => survival (cutoff n c - w)))
      hp_mono hvLow hvHigh hε_pos hS_nonneg hS_eps_lt_one
      hmass_upper hlower_high hdiff

/--
Uniform large-firm source window with the long-tail product gap derived
internally.  This is the uniform-in-`mu` form of Proposition
`lt-large-firms` needed by the final PG24 Theorem 2 statement.
-/
theorem theorem2_largeFirmSourceWindow_uniform_eventually_of_longTail_source_endpoint_estimates
    {Admissible : ℕ → Type*}
    {survival : ℝ → ℝ} (hlong : LongTailedSurvival survival)
    {active : ∀ n : ℕ, Admissible n → Finset (Fin (n + 1))}
    {cutoff : ∀ n : ℕ, Admissible n → Fin (n + 1) → ℝ}
    {lowerCutoff : ℕ → ℝ}
    {vLow vHigh v S α ε σ : ℝ}
    (hp_mono :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n,
          Monotone (fun w : ℝ =>
            independentAffordanceProbability
              (active n μ) (fun c => survival (cutoff n μ c - w))))
    (hvLow : vLow ≤ v) (hvHigh : v ≤ vHigh)
    (hvStrict : vLow < vHigh)
    (hε_pos : 0 < ε) (hε_le_one : ε ≤ 1)
    (hS_nonneg : 0 ≤ S) (hS_eps_lt_one : S + ε < 1)
    (hσ_nonneg : 0 ≤ σ)
    (hlower_atTop :
      Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop)
    (hcutoff_lower :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n, ∀ c ∈ active n μ,
          lowerCutoff n ≤ cutoff n μ c)
    (hhigh_pos :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n, ∀ c ∈ active n μ,
          0 < survival (cutoff n μ c - vHigh))
    (hhigh_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n, ∀ c ∈ active n μ,
          survival (cutoff n μ c - vHigh) ≤
            σ / ((n + 1 : ℕ) : ℝ))
    (hlow_failure_pos :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n, ∀ c ∈ active n μ,
          0 < 1 - survival (cutoff n μ c - vLow))
    (hmass_upper :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n,
          (1 - ε) *
              independentAffordanceProbability
                (active n μ) (fun c => survival (cutoff n μ c - vLow)) ≤ S)
    (hlower_high :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n,
          S - α * ε - ε ≤
            independentAffordanceProbability
              (active n μ) (fun c => survival (cutoff n μ c - vHigh))) :
    ∀ᶠ n : ℕ in atTop,
      ∀ μ : Admissible n,
        theorem2_largeFirmSourceWindow S α ε σ
          (independentAffordanceProbability
            (active n μ) (fun c => survival (cutoff n μ c - v))) := by
  have hdiff :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n,
          independentAffordanceProbability
              (active n μ) (fun c => survival (cutoff n μ c - vHigh)) -
            independentAffordanceProbability
              (active n μ) (fun c => survival (cutoff n μ c - vLow)) ≤
            1 - Real.exp (-(2 * ε * σ)) :=
    independentAffordanceProbability_difference_uniform_eventually_le_exp_error_of_longTailed_highCrossingBound
      (Admissible := Admissible) hlong hvStrict hε_pos hε_le_one
      hσ_nonneg hlower_atTop hcutoff_lower hhigh_pos
      hhigh_le_sigma_div hlow_failure_pos
  filter_upwards [hp_mono, hmass_upper, hlower_high, hdiff] with
    n hmonoN hmassN hhighN hdiffN μ
  exact
    theorem2_largeFirmSourceWindow_of_source_endpoint_estimates
      (pLarge := fun w : ℝ =>
        independentAffordanceProbability
          (active n μ) (fun c => survival (cutoff n μ c - w)))
      (hmonoN μ) hvLow hvHigh hε_pos hS_nonneg hS_eps_lt_one
      (hmassN μ) (hhighN μ) (hdiffN μ)

/--
Uniform large-firm source window in the survival-function shape.  The
monotonicity of the large-firm independent affordance probability in the
student value is derived from antitonicity of the survival function.
-/
theorem theorem2_largeFirmSourceWindow_uniform_eventually_of_survival_longTail_source_endpoint_estimates
    {Admissible : ℕ → Type*}
    {survival : ℝ → ℝ} (hlong : LongTailedSurvival survival)
    {active : ∀ n : ℕ, Admissible n → Finset (Fin (n + 1))}
    {cutoff : ∀ n : ℕ, Admissible n → Fin (n + 1) → ℝ}
    {lowerCutoff : ℕ → ℝ}
    {vLow vHigh v S α ε σ : ℝ}
    (hsurvival_antitone : Antitone survival)
    (hvLow : vLow ≤ v) (hvHigh : v ≤ vHigh)
    (hvStrict : vLow < vHigh)
    (hε_pos : 0 < ε) (hε_le_one : ε ≤ 1)
    (hS_nonneg : 0 ≤ S) (hS_eps_lt_one : S + ε < 1)
    (hσ_nonneg : 0 ≤ σ)
    (hlower_atTop :
      Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop)
    (hcutoff_lower :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n, ∀ c ∈ active n μ,
          lowerCutoff n ≤ cutoff n μ c)
    (hhigh_pos :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n, ∀ c ∈ active n μ,
          0 < survival (cutoff n μ c - vHigh))
    (hhigh_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n, ∀ c ∈ active n μ,
          survival (cutoff n μ c - vHigh) ≤
            σ / ((n + 1 : ℕ) : ℝ))
    (hlow_failure_pos :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n, ∀ c ∈ active n μ,
          0 < 1 - survival (cutoff n μ c - vLow))
    (hprob_le_one :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n, ∀ w, ∀ c ∈ active n μ,
          survival (cutoff n μ c - w) ≤ 1)
    (hmass_upper :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n,
          (1 - ε) *
              independentAffordanceProbability
                (active n μ) (fun c => survival (cutoff n μ c - vLow)) ≤ S)
    (hlower_high :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n,
          S - α * ε - ε ≤
            independentAffordanceProbability
              (active n μ) (fun c => survival (cutoff n μ c - vHigh))) :
    ∀ᶠ n : ℕ in atTop,
      ∀ μ : Admissible n,
        theorem2_largeFirmSourceWindow S α ε σ
          (independentAffordanceProbability
            (active n μ) (fun c => survival (cutoff n μ c - v))) := by
  have hp_mono :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n,
          Monotone (fun w : ℝ =>
            independentAffordanceProbability
              (active n μ) (fun c => survival (cutoff n μ c - w))) := by
    filter_upwards [hprob_le_one] with n hleN μ
    exact
      independentAffordanceProbability_mono_value_of_antitone_survival
        (active := active n μ)
        (survival := survival)
        (cutoff := cutoff n μ)
        hsurvival_antitone
        (fun w c hc => hleN μ w c hc)
  exact
    theorem2_largeFirmSourceWindow_uniform_eventually_of_longTail_source_endpoint_estimates
      (Admissible := Admissible) hlong hp_mono hvLow hvHigh hvStrict
      hε_pos hε_le_one hS_nonneg hS_eps_lt_one hσ_nonneg
      hlower_atTop hcutoff_lower hhigh_pos hhigh_le_sigma_div
      hlow_failure_pos hmass_upper hlower_high

/--
Uniform large-firm source window for a concrete real noise law.  The
survival-function facts, including positivity of the high-endpoint tail and
positive failure probability at the low endpoint, are derived internally from
upper-tail probability, long-tailedness, and the diverging cutoff floor.
-/
theorem theorem2_largeFirmSourceWindow_uniform_eventually_of_upperTail_longTail_source_endpoint_estimates_strict_derived
    {Admissible : ℕ → Type*}
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {active : ∀ n : ℕ, Admissible n → Finset (Fin (n + 1))}
    {cutoff : ∀ n : ℕ, Admissible n → Fin (n + 1) → ℝ}
    {lowerCutoff : ℕ → ℝ}
    {vLow vHigh v S α ε σ : ℝ}
    (hvLow : vLow ≤ v) (hvHigh : v ≤ vHigh)
    (hvStrict : vLow < vHigh)
    (hε_pos : 0 < ε) (hε_le_one : ε ≤ 1)
    (hS_nonneg : 0 ≤ S) (hS_eps_lt_one : S + ε < 1)
    (hσ_nonneg : 0 ≤ σ)
    (hlower_atTop :
      Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop)
    (hcutoff_lower :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n, ∀ c ∈ active n μ,
          lowerCutoff n ≤ cutoff n μ c)
    (hhigh_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n, ∀ c ∈ active n μ,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff n μ c - vHigh) ≤
            σ / ((n + 1 : ℕ) : ℝ))
    (hmass_upper :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n,
          (1 - ε) *
              independentAffordanceProbability
                (active n μ)
                (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoff n μ c - vLow)) ≤ S)
    (hlower_high :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n,
          S - α * ε - ε ≤
            independentAffordanceProbability
              (active n μ)
              (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff n μ c - vHigh))) :
    ∀ᶠ n : ℕ in atTop,
      ∀ μ : Admissible n,
        theorem2_largeFirmSourceWindow S α ε σ
          (independentAffordanceProbability
            (active n μ)
            (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoff n μ c - v))) := by
  have htail_package :=
    upperTailMass_survival_probability_package
      (Admissible := Admissible)
      (noiseLaw := noiseLaw)
      (active := active)
      (cutoff := cutoff)
  have hstrict :=
    upperTailMass_strict_side_conditions_of_longTail_cutoff_floor
      (Admissible := Admissible)
      (noiseLaw := noiseLaw)
      (hlong := hlong)
      (active := active)
      (cutoff := cutoff)
      (vLow := vLow)
      (vHigh := vHigh)
      (lowerCutoff := lowerCutoff)
      hvStrict hlower_atTop hcutoff_lower
  exact
    theorem2_largeFirmSourceWindow_uniform_eventually_of_survival_longTail_source_endpoint_estimates
      (Admissible := Admissible)
      (survival := AppliedModelingLib.Probability.upperTailMass noiseLaw)
      (active := active)
      (cutoff := cutoff)
      (lowerCutoff := lowerCutoff)
      hlong htail_package.1 hvLow hvHigh hvStrict hε_pos hε_le_one
      hS_nonneg hS_eps_lt_one hσ_nonneg hlower_atTop hcutoff_lower
      hstrict.1 hhigh_le_sigma_div hstrict.2 htail_package.2.2
      hmass_upper hlower_high

/--
Uniform large-firm source window for a concrete real noise law using the
appendix's direct high-tail-rate estimate.

Unlike
`theorem2_largeFirmSourceWindow_uniform_eventually_of_upperTail_longTail_source_endpoint_estimates_strict_derived`,
this theorem has no common lower-cutoff floor premise.  The upper-tail
long-tail product estimate derives the needed tail-region side conditions
directly from the per-college bound
`upperTailMass (cutoff - vHigh) <= sigma / (n+1)`.
-/
theorem theorem2_largeFirmSourceWindow_uniform_eventually_of_upperTail_highTailRate_source_endpoint_estimates_strict_derived
    {Admissible : ℕ → Type*}
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {active : ∀ n : ℕ, Admissible n → Finset (Fin (n + 1))}
    {cutoff : ∀ n : ℕ, Admissible n → Fin (n + 1) → ℝ}
    {vLow vHigh v S α ε σ : ℝ}
    (hvLow : vLow ≤ v) (hvHigh : v ≤ vHigh)
    (hvStrict : vLow < vHigh)
    (hε_pos : 0 < ε) (hε_le_one : ε ≤ 1)
    (hS_nonneg : 0 ≤ S) (hS_eps_lt_one : S + ε < 1)
    (hσ_nonneg : 0 ≤ σ)
    (hhigh_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n, ∀ c ∈ active n μ,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff n μ c - vHigh) ≤
            σ / ((n + 1 : ℕ) : ℝ))
    (hmass_upper :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n,
          (1 - ε) *
              independentAffordanceProbability
                (active n μ)
                (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoff n μ c - vLow)) ≤ S)
    (hlower_high :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n,
          S - α * ε - ε ≤
            independentAffordanceProbability
              (active n μ)
              (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff n μ c - vHigh))) :
    ∀ᶠ n : ℕ in atTop,
      ∀ μ : Admissible n,
        theorem2_largeFirmSourceWindow S α ε σ
          (independentAffordanceProbability
            (active n μ)
            (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoff n μ c - v))) := by
  have htail_package :=
    upperTailMass_survival_probability_package
      (Admissible := Admissible)
      (noiseLaw := noiseLaw)
      (active := active)
      (cutoff := cutoff)
  have hp_mono :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n,
          Monotone (fun w : ℝ =>
            independentAffordanceProbability
              (active n μ)
              (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff n μ c - w))) := by
    filter_upwards [htail_package.2.2] with n hleN μ
    exact
      independentAffordanceProbability_mono_value_of_antitone_survival
        (active := active n μ)
        (survival := AppliedModelingLib.Probability.upperTailMass noiseLaw)
        (cutoff := cutoff n μ)
        htail_package.1
        (fun w c hc => hleN μ w c hc)
  have hdiff :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n,
          independentAffordanceProbability
              (active n μ)
              (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff n μ c - vHigh)) -
            independentAffordanceProbability
              (active n μ)
              (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff n μ c - vLow)) ≤
            1 - Real.exp (-(2 * ε * σ)) :=
    independentAffordanceProbability_difference_uniform_eventually_le_exp_error_of_upperTailMass_longTailed_highCrossingBound
      (Admissible := Admissible)
      noiseLaw hlong hvStrict hε_pos hε_le_one hσ_nonneg
      hhigh_le_sigma_div
  filter_upwards [hp_mono, hmass_upper, hlower_high, hdiff] with
    n hmonoN hmassN hhighN hdiffN μ
  exact
    theorem2_largeFirmSourceWindow_of_source_endpoint_estimates
      (pLarge := fun w : ℝ =>
        independentAffordanceProbability
          (active n μ)
          (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff n μ c - w)))
      (hmonoN μ) hvLow hvHigh hε_pos hS_nonneg hS_eps_lt_one
      (hmassN μ) (hhighN μ) (hdiffN μ)

/--
Two-scale version of the direct high-tail-rate large-firm lemma.

The split size `delta` controls the endpoint mass/capacity terms, while the
long-tail ratio tolerance `rho` controls the product error.  This is the
source-faithful shape needed for the amplification appendix: the high-tail
rate constant can be large enough for the prefix capacity contradiction while
`rho * sigma` remains small.
-/
theorem theorem2_twoScaleLargeFirmSourceWindow_uniform_eventually_of_upperTail_highTailRate_source_endpoint_estimates_strict_derived
    {Admissible : ℕ → Type*}
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {active : ∀ n : ℕ, Admissible n → Finset (Fin (n + 1))}
    {cutoff : ∀ n : ℕ, Admissible n → Fin (n + 1) → ℝ}
    {vLow vHigh v S α delta rho sigma : ℝ}
    (hvLow : vLow ≤ v) (hvHigh : v ≤ vHigh)
    (hvStrict : vLow < vHigh)
    (hdelta_pos : 0 < delta)
    (hrho_pos : 0 < rho) (hrho_le_one : rho ≤ 1)
    (hS_nonneg : 0 ≤ S) (hS_delta_lt_one : S + delta < 1)
    (hsigma_nonneg : 0 ≤ sigma)
    (hhigh_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n, ∀ c ∈ active n μ,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff n μ c - vHigh) ≤
            sigma / ((n + 1 : ℕ) : ℝ))
    (hmass_upper :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n,
          (1 - delta) *
              independentAffordanceProbability
                (active n μ)
                (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoff n μ c - vLow)) ≤ S)
    (hlower_high :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n,
          S - α * delta - delta ≤
            independentAffordanceProbability
              (active n μ)
              (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff n μ c - vHigh))) :
    ∀ᶠ n : ℕ in atTop,
      ∀ μ : Admissible n,
        theorem2_twoScaleLargeFirmSourceWindow S α delta rho sigma
          (independentAffordanceProbability
            (active n μ)
            (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoff n μ c - v))) := by
  have htail_package :=
    upperTailMass_survival_probability_package
      (Admissible := Admissible)
      (noiseLaw := noiseLaw)
      (active := active)
      (cutoff := cutoff)
  have hp_mono :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n,
          Monotone (fun w : ℝ =>
            independentAffordanceProbability
              (active n μ)
              (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff n μ c - w))) := by
    filter_upwards [htail_package.2.2] with n hleN μ
    exact
      independentAffordanceProbability_mono_value_of_antitone_survival
        (active := active n μ)
        (survival := AppliedModelingLib.Probability.upperTailMass noiseLaw)
        (cutoff := cutoff n μ)
        htail_package.1
        (fun w c hc => hleN μ w c hc)
  have hdiff :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n,
          independentAffordanceProbability
              (active n μ)
              (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff n μ c - vHigh)) -
            independentAffordanceProbability
              (active n μ)
              (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff n μ c - vLow)) ≤
            1 - Real.exp (-(2 * rho * sigma)) :=
    independentAffordanceProbability_difference_uniform_eventually_le_exp_error_of_upperTailMass_longTailed_highCrossingBound
      (Admissible := Admissible)
      noiseLaw hlong hvStrict hrho_pos hrho_le_one hsigma_nonneg
      hhigh_le_sigma_div
  filter_upwards [hp_mono, hmass_upper, hlower_high, hdiff] with
    n hmonoN hmassN hhighN hdiffN μ
  exact
    theorem2_twoScaleLargeFirmSourceWindow_of_source_endpoint_estimates
      (pLarge := fun w : ℝ =>
        independentAffordanceProbability
          (active n μ)
          (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff n μ c - w)))
      (hmonoN μ) hvLow hvHigh hdelta_pos hS_nonneg hS_delta_lt_one
      (hmassN μ) (hhighN μ) (hdiffN μ)

/--
Uniform large-firm source window for the concrete iid cutoff-affordance
probability used in PG24.  This keeps the endpoint mass inequalities and the
conclusion in the paper's `p_mu(v,C')` language, using the iid product bridge
internally to apply the long-tail upper-tail theorem.
-/
theorem theorem2_largeFirmSourceWindow_uniform_eventually_of_iidProduct_cutoff_upperTail_longTail_source_endpoint_estimates_strict_derived
    {Admissible : ℕ → Type*}
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {active : ∀ n : ℕ, Admissible n → Finset (Fin (n + 1))}
    {cutoff : ∀ n : ℕ, Admissible n → Fin (n + 1) → ℝ}
    {lowerCutoff : ℕ → ℝ}
    {vLow vHigh v S α ε σ : ℝ}
    (hvLow : vLow ≤ v) (hvHigh : v ≤ vHigh)
    (hvStrict : vLow < vHigh)
    (hε_pos : 0 < ε) (hε_le_one : ε ≤ 1)
    (hS_nonneg : 0 ≤ S) (hS_eps_lt_one : S + ε < 1)
    (hσ_nonneg : 0 ≤ σ)
    (hlower_atTop :
      Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop)
    (hcutoff_lower :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n, ∀ c ∈ active n μ,
          lowerCutoff n ≤ cutoff n μ c)
    (hhigh_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n, ∀ c ∈ active n μ,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff n μ c - vHigh) ≤
            σ / ((n + 1 : ℕ) : ℝ))
    (hmass_upper :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n,
          (1 - ε) *
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
                (active n μ) vLow (cutoff n μ) ≤ S)
    (hlower_high :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n,
          S - α * ε - ε ≤
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
              (active n μ) vHigh (cutoff n μ)) :
    ∀ᶠ n : ℕ in atTop,
      ∀ μ : Admissible n,
        theorem2_largeFirmSourceWindow S α ε σ
          (cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
            (active n μ) v (cutoff n μ)) := by
  have hmass_upper_tail :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n,
          (1 - ε) *
              independentAffordanceProbability
                (active n μ)
                (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoff n μ c - vLow)) ≤ S := by
    filter_upwards [hmass_upper] with n hn μ
    have hbridge :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (active n μ) vLow (cutoff n μ)
    simpa [hbridge] using hn μ
  have hlower_high_tail :
      ∀ᶠ n : ℕ in atTop,
        ∀ μ : Admissible n,
          S - α * ε - ε ≤
            independentAffordanceProbability
              (active n μ)
              (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff n μ c - vHigh)) := by
    filter_upwards [hlower_high] with n hn μ
    have hbridge :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (active n μ) vHigh (cutoff n μ)
    simpa [hbridge] using hn μ
  have htail :=
    theorem2_largeFirmSourceWindow_uniform_eventually_of_upperTail_longTail_source_endpoint_estimates_strict_derived
      (Admissible := Admissible)
      (noiseLaw := noiseLaw)
      (hlong := hlong)
      (active := active)
      (cutoff := cutoff)
      (lowerCutoff := lowerCutoff)
      (vLow := vLow) (vHigh := vHigh) (v := v)
      (S := S) (α := α) (ε := ε) (σ := σ)
      hvLow hvHigh hvStrict hε_pos hε_le_one hS_nonneg
      hS_eps_lt_one hσ_nonneg hlower_atTop hcutoff_lower
      hhigh_le_sigma_div hmass_upper_tail hlower_high_tail
  filter_upwards [htail] with n hn μ
  have hbridge :=
    cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
      noiseLaw (active n μ) v (cutoff n μ)
  simpa [hbridge] using hn μ

/--
Fixed-`alpha` Theorem 2 closure from the source endpoint estimates.  This
packages the proof route of Proposition `lt-large-firms`, Proposition
`lt-small-firms`, and the final `C1/C2` decomposition: callers provide the
endpoint mass/capacity estimates and product gap for each value and source
parameter choice, and Lean derives the uniform amplification conclusion.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_source_endpoint_estimates
    {Admissible : ℕ → Type*}
    {pTotal pSmall pLarge : ∀ C : ℕ, Admissible C → ℝ → ℝ}
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, Monotone (pLarge C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, Monotone (pSmall C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              (1 - epsilon) * pLarge C μ vLow ≤ totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              totalSupply - alpha * epsilon - epsilon ≤
                pLarge C μ vHigh) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              pLarge C μ vHigh - pLarge C μ vLow ≤
                1 - Real.exp (-(2 * epsilon * sigma))) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  pSmall C μ vStar ≤
                epsilon * alpha) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, pLarge C μ v ≤ pTotal C μ v) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              pTotal C μ v ≤ pSmall C μ v + pLarge C μ v)) :
    theorem2_uniformAmplificationConclusion Admissible pTotal totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_large_small_source_windows
      (pTotal := pTotal) (pSmall := pSmall) (pLarge := pLarge)
      (alpha := alpha)
      htotalSupply_lt_one ?_
  intro v epsilon sigma hepsilon_pos hsigma_pos hden_pos
  rcases hsource v epsilon sigma hepsilon_pos hsigma_pos hden_pos with
    ⟨vLow, vHigh, vStar, hvLow, hvHigh, hvStar,
      hpLarge_mono, hpSmall_mono, hmass_upper, hlower_high, hdiff,
      hcapacity_star, hlarge_le_total, htotal_le_sum⟩
  have hS_eps_lt_one :
      totalSupply + epsilon < 1 :=
    theorem2_totalSupply_add_epsilon_lt_one_of_denominator_pos
      hepsilon_pos hsigma_pos hden_pos
  have hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          theorem2_largeFirmSourceWindow
            totalSupply alpha epsilon sigma (pLarge C μ v) := by
    filter_upwards [hpLarge_mono, hmass_upper, hlower_high, hdiff] with
      C hmonoC hmassC hhighC hdiffC μ
    exact
      theorem2_largeFirmSourceWindow_of_source_endpoint_estimates
        (pLarge := pLarge C μ) (hmonoC μ) hvLow hvHigh
        hepsilon_pos htotalSupply_nonneg hS_eps_lt_one
        (hmassC μ) (hhighC μ) (hdiffC μ)
  have hsmall :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          theorem2_smallFirmSourceBound
            totalSupply alpha epsilon sigma (pSmall C μ v) := by
    filter_upwards [hpSmall_mono, hcapacity_star] with
      C hmonoC hcapC μ
    exact
      theorem2_smallFirmSourceBound_of_star_capacity_mass
        hepsilon_pos hden_pos (hmonoC μ) hvStar (hcapC μ)
  exact ⟨hlarge, hsmall, hlarge_le_total, htotal_le_sum⟩

/--
Fixed-`alpha` Theorem 2 closure from endpoint estimates and the paper's
active-capacity small-firm comparison.  This replaces the raw
`sqrt(epsilon) * denominator * pSmall <= epsilon * alpha` premise by the
source ingredients used to prove it: `|C1| <= epsilon C`, capacity regularity,
and the lower bound comparing the interval integral to `S(C1)`.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_source_endpoint_estimates_active_capacity
    {Admissible : ℕ → Type*}
    {pTotal pSmall pLarge : ∀ C : ℕ, Admissible C → ℝ → ℝ}
    (small : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1)))
    (capacity : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, Monotone (pLarge C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, Monotone (pSmall C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              (1 - epsilon) * pLarge C μ vLow ≤ totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              totalSupply - alpha * epsilon - epsilon ≤
                pLarge C μ vHigh) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              pLarge C μ vHigh - pLarge C μ vLow ≤
                1 - Real.exp (-(2 * epsilon * sigma))) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              ((small C μ).card : ℝ) ≤
                epsilon * ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, ∀ c ∈ small C μ,
              capacity C μ c ≤ alpha / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  pSmall C μ vStar ≤
                AppliedModelingLib.Matching.activeCapacity (small C μ) (capacity C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, pLarge C μ v ≤ pTotal C μ v) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              pTotal C μ v ≤ pSmall C μ v + pLarge C μ v)) :
    theorem2_uniformAmplificationConclusion Admissible pTotal totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_source_endpoint_estimates
      (pTotal := pTotal) (pSmall := pSmall) (pLarge := pLarge)
      (alpha := alpha)
      htotalSupply_nonneg htotalSupply_lt_one ?_
  intro v epsilon sigma hepsilon_pos hsigma_pos hden_pos
  rcases hsource v epsilon sigma hepsilon_pos hsigma_pos hden_pos with
    ⟨vLow, vHigh, vStar, hvLow, hvHigh, hvStar,
      hpLarge_mono, hpSmall_mono, hmass_upper, hlower_high, hdiff,
      hcard, hcap, hcapacity_lower, hlarge_le_total, htotal_le_sum⟩
  have hcapacity_star :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          Real.sqrt epsilon *
              (1 - totalSupply - epsilon -
                (1 - Real.exp (-(2 * epsilon * sigma)))) *
              pSmall C μ vStar ≤
            epsilon * alpha := by
    filter_upwards [hcard, hcap, hcapacity_lower] with
      C hcardC hcapC hlowerC μ
    have hC_pos : 0 < (((C + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_pos C
    exact
      theorem2_capacity_mass_le_of_active_capacity_lower_bound
        (small C μ) (capacity C μ)
        (epsilon := epsilon) (alpha := alpha)
        (totalSupply := totalSupply) (sigma := sigma)
        (p := pSmall C μ vStar) (C := C + 1)
        (hcardC μ) halpha_nonneg hC_pos (hcapC μ) (hlowerC μ)
  exact
    ⟨vLow, vHigh, vStar, hvLow, hvHigh, hvStar,
      hpLarge_mono, hpSmall_mono, hmass_upper, hlower_high, hdiff,
      hcapacity_star, hlarge_le_total, htotal_le_sum⟩

/--
Fixed-`alpha` Theorem 2 closure from endpoint estimates and the paper's
small-firm interval integral.

Compared with
`theorem2_uniformAmplification_of_fixed_alpha_source_endpoint_estimates_active_capacity`,
this source-facing variant does not assume the small-firm active-capacity
lower bound directly.  It derives it from the paper's interval mass
`η((v*,v+))`, monotonicity of small-firm affordability, nonnegativity outside
the interval, and the event/capacity statement that the interval integral is
bounded by the small block's matched capacity.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_source_endpoint_estimates_small_interval_integral_active_capacity
    {Admissible : ℕ → Type*}
    (η : Measure ℝ) [IsProbabilityMeasure η]
    {pTotal pSmall pLarge : ∀ C : ℕ, Admissible C → ℝ → ℝ}
    (small : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1)))
    (capacity : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ)
    (interval : ∀ C : ℕ, Admissible C → Set ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, Monotone (pLarge C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, Monotone (pSmall C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              (1 - epsilon) * pLarge C μ vLow ≤ totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              totalSupply - alpha * epsilon - epsilon ≤
                pLarge C μ vHigh) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              pLarge C μ vHigh - pLarge C μ vLow ≤
                1 - Real.exp (-(2 * epsilon * sigma))) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              ((small C μ).card : ℝ) ≤
                epsilon * ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, ∀ c ∈ small C μ,
              capacity C μ c ≤ alpha / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              MeasurableSet (interval C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              Integrable
                (fun w : ℝ =>
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                    pSmall C μ w) η) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              Real.sqrt epsilon ≤ η.real (interval C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, 0 ≤ pSmall C μ vStar) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              ∀ w : ℝ, w ∈ interval C μ → vStar ≤ w) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              ∀ w : ℝ, w ∉ interval C μ →
                0 ≤
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                    pSmall C μ w) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              (∫ w : ℝ,
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                    pSmall C μ w ∂η) ≤
                AppliedModelingLib.Matching.activeCapacity (small C μ)
                  (capacity C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, pLarge C μ v ≤ pTotal C μ v) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              pTotal C μ v ≤ pSmall C μ v + pLarge C μ v)) :
    theorem2_uniformAmplificationConclusion Admissible pTotal totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_source_endpoint_estimates_active_capacity
      (pTotal := pTotal) (pSmall := pSmall) (pLarge := pLarge)
      small capacity htotalSupply_nonneg htotalSupply_lt_one
      halpha_nonneg ?_
  intro v epsilon sigma hepsilon_pos hsigma_pos hden_pos
  rcases hsource v epsilon sigma hepsilon_pos hsigma_pos hden_pos with
    ⟨vLow, vHigh, vStar, hvLow, hvHigh, hvStar,
      hpLarge_mono, hpSmall_mono, hmass_upper, hlower_high, hdiff,
      hcard, hcap, hinterval_meas, hint, hinterval_mass,
      hp_star_nonneg, hinterval_ge, hnonneg_compl, hintegral_capacity,
      hlarge_le_total, htotal_le_sum⟩
  refine
    ⟨vLow, vHigh, vStar, hvLow, hvHigh, hvStar,
      hpLarge_mono, hpSmall_mono, hmass_upper, hlower_high, hdiff,
      hcard, hcap, ?_, hlarge_le_total, htotal_le_sum⟩
  filter_upwards
    [hinterval_meas, hint, hinterval_mass, hpSmall_mono, hp_star_nonneg,
      hinterval_ge, hnonneg_compl, hintegral_capacity] with
    C hmeasC hintC hmassC hmonoC hstarC hgeC hnonnegC hintegralC μ
  exact
    theorem2_smallFirm_matchedMass_lower_bound_of_interval_integral
      η
      (region := interval C μ)
      (mass := Real.sqrt epsilon)
      (denom :=
        1 - totalSupply - epsilon -
          (1 - Real.exp (-(2 * epsilon * sigma))))
      (matchedMass :=
        AppliedModelingLib.Matching.activeCapacity (small C μ) (capacity C μ))
      (pSmall := pSmall C μ) (vStar := vStar)
      (hmeasC μ) (hintC μ) (hmassC μ) (le_of_lt hden_pos)
      (hstarC μ) (hmonoC μ) (hgeC μ) (hnonnegC μ)
      (hintegralC μ)

/--
Fixed-`alpha` Theorem 2 closure from long-tailedness and source endpoint
estimates.  This source-facing variant derives the product-gap estimate from
the long-tailed noise condition, a common cutoff lower bound, and the
high-value crossing-probability bound, instead of exposing the product gap as
an independent premise.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_longTail_source_endpoint_estimates
    {Admissible : ℕ → Type*}
    {survival : ℝ → ℝ} (hlong : LongTailedSurvival survival)
    {active : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    {cutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ}
    {pTotal pSmall : ∀ C : ℕ, Admissible C → ℝ → ℝ}
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              Monotone (fun w : ℝ =>
                independentAffordanceProbability
                  (active C μ) (fun c => survival (cutoff C μ c - w)))) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, Monotone (pSmall C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, ∀ c ∈ active C μ,
              lowerCutoff C ≤ cutoff C μ c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, ∀ c ∈ active C μ,
              0 < survival (cutoff C μ c - vHigh)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, ∀ c ∈ active C μ,
              survival (cutoff C μ c - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, ∀ c ∈ active C μ,
              0 < 1 - survival (cutoff C μ c - vLow)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              (1 - epsilon) *
                  independentAffordanceProbability
                    (active C μ)
                    (fun c => survival (cutoff C μ c - vLow)) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              totalSupply - alpha * epsilon - epsilon ≤
                independentAffordanceProbability
                  (active C μ)
                  (fun c => survival (cutoff C μ c - vHigh))) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  pSmall C μ vStar ≤
                epsilon * alpha) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              independentAffordanceProbability
                  (active C μ) (fun c => survival (cutoff C μ c - v)) ≤
                pTotal C μ v) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              pTotal C μ v ≤
                pSmall C μ v +
                  independentAffordanceProbability
                    (active C μ) (fun c => survival (cutoff C μ c - v)))) :
    theorem2_uniformAmplificationConclusion Admissible pTotal totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_large_small_source_windows
      (pTotal := pTotal) (pSmall := pSmall)
      (pLarge := fun C : ℕ => fun μ : Admissible C => fun w : ℝ =>
        independentAffordanceProbability
          (active C μ) (fun c => survival (cutoff C μ c - w)))
      (alpha := alpha)
      htotalSupply_lt_one ?_
  intro v epsilon sigma hepsilon_pos hsigma_pos hden_pos
  rcases hsource v epsilon sigma hepsilon_pos hsigma_pos hden_pos with
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hpLarge_mono, hpSmall_mono, hcutoff_lower,
      hhigh_pos, hhigh_le_sigma_div, hlow_failure_pos,
      hmass_upper, hlower_high, hcapacity_star,
      hlarge_le_total, htotal_le_sum⟩
  have hS_eps_lt_one :
      totalSupply + epsilon < 1 :=
    theorem2_totalSupply_add_epsilon_lt_one_of_denominator_pos
      hepsilon_pos hsigma_pos hden_pos
  have hepsilon_le_one : epsilon ≤ 1 := by
    linarith
  have hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          theorem2_largeFirmSourceWindow totalSupply alpha epsilon sigma
            (independentAffordanceProbability
              (active C μ)
              (fun c => survival (cutoff C μ c - v))) :=
    theorem2_largeFirmSourceWindow_uniform_eventually_of_longTail_source_endpoint_estimates
      (Admissible := Admissible) hlong hpLarge_mono
      hvLow hvHigh hvStrict hepsilon_pos hepsilon_le_one
      htotalSupply_nonneg hS_eps_lt_one hsigma_pos.le
      hlower_atTop hcutoff_lower hhigh_pos hhigh_le_sigma_div
      hlow_failure_pos hmass_upper hlower_high
  have hsmall :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          theorem2_smallFirmSourceBound
            totalSupply alpha epsilon sigma (pSmall C μ v) := by
    filter_upwards [hpSmall_mono, hcapacity_star] with
      C hmonoC hcapC μ
    exact
      theorem2_smallFirmSourceBound_of_star_capacity_mass
        hepsilon_pos hden_pos (hmonoC μ) hvStar (hcapC μ)
  exact ⟨hlarge, hsmall, hlarge_le_total, htotal_le_sum⟩

/--
Fixed-`alpha` Theorem 2 closure from survival-function long-tailedness and
source endpoint estimates.  This removes the abstract large-firm value
monotonicity premise by deriving it from antitonicity of the survival
function.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_survival_longTail_source_endpoint_estimates
    {Admissible : ℕ → Type*}
    {survival : ℝ → ℝ} (hlong : LongTailedSurvival survival)
    {active : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    {cutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ}
    {pTotal pSmall : ∀ C : ℕ, Admissible C → ℝ → ℝ}
    {totalSupply alpha : ℝ}
    (hsurvival_antitone : Antitone survival)
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, Monotone (pSmall C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, ∀ c ∈ active C μ,
              lowerCutoff C ≤ cutoff C μ c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, ∀ c ∈ active C μ,
              0 < survival (cutoff C μ c - vHigh)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, ∀ c ∈ active C μ,
              survival (cutoff C μ c - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, ∀ c ∈ active C μ,
              0 < 1 - survival (cutoff C μ c - vLow)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, ∀ w, ∀ c ∈ active C μ,
              survival (cutoff C μ c - w) ≤ 1) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              (1 - epsilon) *
                  independentAffordanceProbability
                    (active C μ)
                    (fun c => survival (cutoff C μ c - vLow)) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              totalSupply - alpha * epsilon - epsilon ≤
                independentAffordanceProbability
                  (active C μ)
                  (fun c => survival (cutoff C μ c - vHigh))) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  pSmall C μ vStar ≤
                epsilon * alpha) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              independentAffordanceProbability
                  (active C μ) (fun c => survival (cutoff C μ c - v)) ≤
                pTotal C μ v) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              pTotal C μ v ≤
                pSmall C μ v +
                  independentAffordanceProbability
                    (active C μ) (fun c => survival (cutoff C μ c - v)))) :
    theorem2_uniformAmplificationConclusion Admissible pTotal totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_large_small_source_windows
      (pTotal := pTotal) (pSmall := pSmall)
      (pLarge := fun C : ℕ => fun μ : Admissible C => fun w : ℝ =>
        independentAffordanceProbability
          (active C μ) (fun c => survival (cutoff C μ c - w)))
      (alpha := alpha)
      htotalSupply_lt_one ?_
  intro v epsilon sigma hepsilon_pos hsigma_pos hden_pos
  rcases hsource v epsilon sigma hepsilon_pos hsigma_pos hden_pos with
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hpSmall_mono, hcutoff_lower, hhigh_pos,
      hhigh_le_sigma_div, hlow_failure_pos, hprob_le_one,
      hmass_upper, hlower_high, hcapacity_star,
      hlarge_le_total, htotal_le_sum⟩
  have hS_eps_lt_one :
      totalSupply + epsilon < 1 :=
    theorem2_totalSupply_add_epsilon_lt_one_of_denominator_pos
      hepsilon_pos hsigma_pos hden_pos
  have hepsilon_le_one : epsilon ≤ 1 := by
    linarith
  have hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          theorem2_largeFirmSourceWindow totalSupply alpha epsilon sigma
            (independentAffordanceProbability
              (active C μ)
              (fun c => survival (cutoff C μ c - v))) :=
    theorem2_largeFirmSourceWindow_uniform_eventually_of_survival_longTail_source_endpoint_estimates
      (Admissible := Admissible) hlong hsurvival_antitone
      hvLow hvHigh hvStrict hepsilon_pos hepsilon_le_one
      htotalSupply_nonneg hS_eps_lt_one hsigma_pos.le
      hlower_atTop hcutoff_lower hhigh_pos hhigh_le_sigma_div
      hlow_failure_pos hprob_le_one hmass_upper hlower_high
  have hsmall :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          theorem2_smallFirmSourceBound
            totalSupply alpha epsilon sigma (pSmall C μ v) := by
    filter_upwards [hpSmall_mono, hcapacity_star] with
      C hmonoC hcapC μ
    exact
      theorem2_smallFirmSourceBound_of_star_capacity_mass
        hepsilon_pos hden_pos (hmonoC μ) hvStar (hcapC μ)
  exact ⟨hlarge, hsmall, hlarge_le_total, htotal_le_sum⟩

/--
Fixed-`alpha` Theorem 2 closure for a concrete real noise law.  This is the
source-probability specialization of the survival-function row: once
`survival x` is instantiated as the upper-tail probability `Pr[X > x]`, Lean
derives antitonicity and the `[0,1]` probability bound from the measure API
instead of taking them as source premises.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_upperTail_longTail_source_endpoint_estimates
    {Admissible : ℕ → Type*}
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {active : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    {cutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ}
    {pTotal pSmall : ∀ C : ℕ, Admissible C → ℝ → ℝ}
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, Monotone (pSmall C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, ∀ c ∈ active C μ,
              lowerCutoff C ≤ cutoff C μ c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, ∀ c ∈ active C μ,
              0 < AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C μ c - vHigh)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, ∀ c ∈ active C μ,
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C μ c - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, ∀ c ∈ active C μ,
              0 < 1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C μ c - vLow)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              (1 - epsilon) *
                  independentAffordanceProbability
                    (active C μ)
                    (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                      (cutoff C μ c - vLow)) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              totalSupply - alpha * epsilon - epsilon ≤
                independentAffordanceProbability
                  (active C μ)
                  (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                    (cutoff C μ c - vHigh))) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  pSmall C μ vStar ≤
                epsilon * alpha) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              independentAffordanceProbability
                  (active C μ)
                  (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                    (cutoff C μ c - v)) ≤
                pTotal C μ v) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              pTotal C μ v ≤
                pSmall C μ v +
                  independentAffordanceProbability
                    (active C μ)
                    (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                      (cutoff C μ c - v)))) :
    theorem2_uniformAmplificationConclusion Admissible pTotal totalSupply := by
  have htail_package :=
    upperTailMass_survival_probability_package
      (Admissible := Admissible)
      (noiseLaw := noiseLaw)
      (active := active)
      (cutoff := cutoff)
  refine
    theorem2_uniformAmplification_of_fixed_alpha_survival_longTail_source_endpoint_estimates
      (Admissible := Admissible)
      (survival := AppliedModelingLib.Probability.upperTailMass noiseLaw)
      (active := active)
      (cutoff := cutoff)
      (pTotal := pTotal)
      (pSmall := pSmall)
      (totalSupply := totalSupply)
      (alpha := alpha)
      hlong htail_package.1 htotalSupply_nonneg htotalSupply_lt_one ?_
  intro v epsilon sigma hepsilon hsigma hden_pos
  rcases hsource v epsilon sigma hepsilon hsigma hden_pos with
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hpSmall_mono, hcutoff_lower, hhigh_pos,
      hhigh_le_sigma_div, hlow_failure_pos, hmass_upper, hlower_high,
      hcapacity_star, hlarge_le_total, htotal_le_sum⟩
  exact
    ⟨vLow, vHigh, vStar, lowerCutoff,
      hvLow, hvHigh, hvStar, hvStrict, hlower_atTop,
      hpSmall_mono, hcutoff_lower, hhigh_pos, hhigh_le_sigma_div,
      hlow_failure_pos, htail_package.2.2, hmass_upper, hlower_high,
      hcapacity_star, hlarge_le_total, htotal_le_sum⟩

/--
Theorem 2 upper-tail long-tail closure with the strict probability side
conditions derived internally.  The source endpoint package supplies the
cutoff floor, the high-endpoint `sigma / C` estimate, the capacity estimate,
and the total-probability decomposition; positivity of the high tail and of
the low-endpoint failure probability follow from long-tailed upper-tail
probabilities and the diverging cutoff floor.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_upperTail_longTail_source_endpoint_estimates_strict_derived
    {Admissible : ℕ → Type*}
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {active : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    {cutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ}
    {pTotal pSmall : ∀ C : ℕ, Admissible C → ℝ → ℝ}
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, Monotone (pSmall C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, ∀ c ∈ active C μ,
              lowerCutoff C ≤ cutoff C μ c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, ∀ c ∈ active C μ,
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C μ c - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              (1 - epsilon) *
                  independentAffordanceProbability
                    (active C μ)
                    (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                      (cutoff C μ c - vLow)) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              totalSupply - alpha * epsilon - epsilon ≤
                independentAffordanceProbability
                  (active C μ)
                  (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                    (cutoff C μ c - vHigh))) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  pSmall C μ vStar ≤
                epsilon * alpha) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              independentAffordanceProbability
                  (active C μ)
                  (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                    (cutoff C μ c - v)) ≤
                pTotal C μ v) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              pTotal C μ v ≤
                pSmall C μ v +
                  independentAffordanceProbability
                    (active C μ)
                    (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                      (cutoff C μ c - v)))) :
    theorem2_uniformAmplificationConclusion Admissible pTotal totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_upperTail_longTail_source_endpoint_estimates
      (Admissible := Admissible)
      (noiseLaw := noiseLaw)
      (hlong := hlong)
      (active := active)
      (cutoff := cutoff)
      (pTotal := pTotal)
      (pSmall := pSmall)
      (totalSupply := totalSupply)
      (alpha := alpha)
      htotalSupply_nonneg htotalSupply_lt_one ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hpSmall_mono, hcutoff_lower, hhigh_le_sigma_div,
      hmass_upper, hlower_high, hcapacity_star, hlarge_le_total,
      htotal_le_sum⟩
  have hstrict :=
    upperTailMass_strict_side_conditions_of_longTail_cutoff_floor
      (Admissible := Admissible)
      (noiseLaw := noiseLaw)
      (hlong := hlong)
      (active := active)
      (cutoff := cutoff)
      (vLow := vLow)
      (vHigh := vHigh)
      (lowerCutoff := lowerCutoff)
      hvStrict hlower_atTop hcutoff_lower
  exact
    ⟨vLow, vHigh, vStar, lowerCutoff,
      hvLow, hvHigh, hvStar, hvStrict, hlower_atTop,
      hpSmall_mono, hcutoff_lower, hstrict.1, hhigh_le_sigma_div,
      hstrict.2, hmass_upper, hlower_high, hcapacity_star,
      hlarge_le_total, htotal_le_sum⟩

/--
Fixed-`alpha` Theorem 2 closure for the concrete iid cutoff-affordance model.
The total and small probabilities are the actual cutoff-crossing
probabilities under iid product noise.  The large-firm independent-product
formula is introduced only internally via the iid product bridge, while the
small-firm capacity bound and the final small/large decomposition are derived
from the visible active sets.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_cutoff_source_endpoint_estimates_strict_derived
    {Admissible : ℕ → Type*}
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (small large total :
      ∀ C : ℕ, Admissible C → Finset (Fin (C + 1)))
    (cutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ)
    (capacity : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, total C μ = small C μ ∪ large C μ) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, ∀ c ∈ large C μ,
              lowerCutoff C ≤ cutoff C μ c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, ∀ c ∈ large C μ,
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C μ c - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (large C μ) vLow (cutoff C μ) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (large C μ) vHigh (cutoff C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              ((small C μ).card : ℝ) ≤
                epsilon * ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, ∀ c ∈ small C μ,
              capacity C μ c ≤ alpha / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (small C μ) vStar (cutoff C μ) ≤
                AppliedModelingLib.Matching.activeCapacity (small C μ) (capacity C μ))) :
    theorem2_uniformAmplificationConclusion Admissible
      (fun C : ℕ => fun μ : Admissible C => fun v : ℝ =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (total C μ) v (cutoff C μ))
      totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_upperTail_longTail_source_endpoint_estimates_strict_derived
      (Admissible := Admissible)
      (noiseLaw := noiseLaw)
      (hlong := hlong)
      (active := large)
      (cutoff := cutoff)
      (pTotal := fun C : ℕ => fun μ : Admissible C => fun v : ℝ =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (total C μ) v (cutoff C μ))
      (pSmall := fun C : ℕ => fun μ : Admissible C => fun v : ℝ =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (small C μ) v (cutoff C μ))
      (totalSupply := totalSupply)
      (alpha := alpha)
      htotalSupply_nonneg htotalSupply_lt_one ?_
  intro v epsilon sigma hepsilon_pos hsigma_pos hden_pos
  rcases hsource v epsilon sigma hepsilon_pos hsigma_pos hden_pos with
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, htotal, hcutoff_lower, hhigh_le_sigma_div,
      hmass_upper_cutoff, hlower_high_cutoff, hcard, hcap,
      hcapacity_lower⟩
  have hpSmall_mono :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          Monotone (fun w : ℝ =>
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (small C μ) w (cutoff C μ)) := by
    exact Filter.Eventually.of_forall (fun C => by
      intro μ x y hxy
      exact
        cutoffAffordanceProbability_mono_value
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (active := small C μ) (cutoff := cutoff C μ) hxy)
  have hmass_upper :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          (1 - epsilon) *
              independentAffordanceProbability
                (large C μ)
                (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoff C μ c - vLow)) ≤
            totalSupply := by
    filter_upwards [hmass_upper_cutoff] with C hmassC μ
    have hbridge :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (large C μ) vLow (cutoff C μ)
    simpa [← hbridge] using hmassC μ
  have hlower_high :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          totalSupply - alpha * epsilon - epsilon ≤
            independentAffordanceProbability
              (large C μ)
              (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C μ c - vHigh)) := by
    filter_upwards [hlower_high_cutoff] with C hhighC μ
    have hbridge :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (large C μ) vHigh (cutoff C μ)
    simpa [← hbridge] using hhighC μ
  have hcapacity_star :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          Real.sqrt epsilon *
              (1 - totalSupply - epsilon -
                (1 - Real.exp (-(2 * epsilon * sigma)))) *
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (small C μ) vStar (cutoff C μ) ≤
            epsilon * alpha := by
    filter_upwards [hcard, hcap, hcapacity_lower] with
      C hcardC hcapC hlowerC μ
    have hC_pos : 0 < (((C + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_pos C
    exact
      theorem2_capacity_mass_le_of_active_capacity_lower_bound
        (small C μ) (capacity C μ)
        (epsilon := epsilon) (alpha := alpha)
        (totalSupply := totalSupply) (sigma := sigma)
        (p :=
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (small C μ) vStar (cutoff C μ))
        (C := C + 1)
        (hcardC μ) halpha_nonneg hC_pos (hcapC μ) (hlowerC μ)
  have hlarge_le_total :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          independentAffordanceProbability
              (large C μ)
              (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C μ c - v)) ≤
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (total C μ) v (cutoff C μ) := by
    filter_upwards [htotal] with C htotalC μ
    have hsubset : large C μ ⊆ total C μ := by
      intro c hc
      rw [htotalC μ]
      exact Finset.mem_union_right (small C μ) hc
    have hmono :
        cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (large C μ) v (cutoff C μ) ≤
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (total C μ) v (cutoff C μ) :=
      cutoffAffordanceProbability_mono_active
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        hsubset
    have hbridge :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (large C μ) v (cutoff C μ)
    simpa [← hbridge] using hmono
  have htotal_le_sum :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (total C μ) v (cutoff C μ) ≤
            cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (small C μ) v (cutoff C μ) +
              independentAffordanceProbability
                (large C μ)
                (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoff C μ c - v)) := by
    filter_upwards [htotal] with C htotalC μ
    have hdecomp :=
      cutoffAffordanceProbability_decomposition_of_union
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (small := small C μ) (large := large C μ) (total := total C μ)
        (v := v) (cutoff := cutoff C μ) (htotalC μ)
    have hbridge :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (large C μ) v (cutoff C μ)
    simpa [← hbridge] using hdecomp.2
  exact
    ⟨vLow, vHigh, vStar, lowerCutoff,
      hvLow, hvHigh, hvStar, hvStrict, hlower_atTop,
      hpSmall_mono, hcutoff_lower, hhigh_le_sigma_div,
      hmass_upper, hlower_high, hcapacity_star,
      hlarge_le_total, htotal_le_sum⟩

/--
Concrete iid Theorem 2 closure from the appendix's direct high-tail-rate
estimate.

Compared with
`theorem2_uniformAmplification_of_fixed_alpha_iidProduct_cutoff_source_endpoint_estimates_strict_derived`,
this route does not ask the source package for a common lower-cutoff floor or
for divergence of that floor.  The large-firm product-gap estimate is derived
directly from the paper-style condition
`Pr[X > P_c - vHigh] <= sigma / (C+1)` on every college in the large suffix.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_cutoff_highTailRate_source_endpoint_estimates_strict_derived
    {Admissible : ℕ → Type*}
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (small large total :
      ∀ C : ℕ, Admissible C → Finset (Fin (C + 1)))
    (cutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ)
    (capacity : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, total C μ = small C μ ∪ large C μ) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, ∀ c ∈ large C μ,
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C μ c - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (large C μ) vLow (cutoff C μ) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (large C μ) vHigh (cutoff C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              ((small C μ).card : ℝ) ≤
                epsilon * ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, ∀ c ∈ small C μ,
              capacity C μ c ≤ alpha / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (small C μ) vStar (cutoff C μ) ≤
                AppliedModelingLib.Matching.activeCapacity (small C μ) (capacity C μ))) :
    theorem2_uniformAmplificationConclusion Admissible
      (fun C : ℕ => fun μ : Admissible C => fun v : ℝ =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (total C μ) v (cutoff C μ))
      totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_source_endpoint_estimates_active_capacity
      (pTotal := fun C : ℕ => fun μ : Admissible C => fun v : ℝ =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (total C μ) v (cutoff C μ))
      (pSmall := fun C : ℕ => fun μ : Admissible C => fun v : ℝ =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (small C μ) v (cutoff C μ))
      (pLarge := fun C : ℕ => fun μ : Admissible C => fun v : ℝ =>
        independentAffordanceProbability
          (large C μ)
          (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff C μ c - v)))
      small capacity htotalSupply_nonneg htotalSupply_lt_one
      halpha_nonneg ?_
  intro v epsilon sigma hepsilon_pos hsigma_pos hden_pos
  rcases hsource v epsilon sigma hepsilon_pos hsigma_pos hden_pos with
    ⟨vLow, vHigh, vStar, hvLow, hvHigh, hvStar, hvStrict,
      htotal, hhigh_le_sigma_div, hmass_upper_cutoff,
      hlower_high_cutoff, hcard, hcap, hcapacity_lower⟩
  have hsigma_nonneg : 0 ≤ sigma := le_of_lt hsigma_pos
  have herror_nonneg :
      0 ≤ 1 - Real.exp (-(2 * epsilon * sigma)) := by
    have hexp_le_one :
        Real.exp (-(2 * epsilon * sigma)) ≤ 1 := by
      simpa using
        (Real.exp_le_exp.mpr
          (by nlinarith [hepsilon_pos.le, hsigma_nonneg] :
            -(2 * epsilon * sigma) ≤ (0 : ℝ)))
    linarith
  have hS_eps_lt_one : totalSupply + epsilon < 1 := by
    linarith
  have hepsilon_le_one : epsilon ≤ 1 := by
    linarith
  have htail_package :=
    upperTailMass_survival_probability_package
      (Admissible := Admissible)
      (noiseLaw := noiseLaw)
      (active := large)
      (cutoff := cutoff)
  have hpLarge_mono :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          Monotone (fun w : ℝ =>
            independentAffordanceProbability
              (large C μ)
              (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C μ c - w))) := by
    filter_upwards [htail_package.2.2] with C hleC μ
    exact
      independentAffordanceProbability_mono_value_of_antitone_survival
        (active := large C μ)
        (survival := AppliedModelingLib.Probability.upperTailMass noiseLaw)
        (cutoff := cutoff C μ)
        htail_package.1
        (fun w c hc => hleC μ w c hc)
  have hpSmall_mono :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          Monotone (fun w : ℝ =>
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (small C μ) w (cutoff C μ)) := by
    exact Filter.Eventually.of_forall (fun C => by
      intro μ x y hxy
      exact
        cutoffAffordanceProbability_mono_value
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (active := small C μ) (cutoff := cutoff C μ) hxy)
  have hmass_upper :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          (1 - epsilon) *
              independentAffordanceProbability
                (large C μ)
                (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoff C μ c - vLow)) ≤
            totalSupply := by
    filter_upwards [hmass_upper_cutoff] with C hmassC μ
    have hbridge :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (large C μ) vLow (cutoff C μ)
    simpa [← hbridge] using hmassC μ
  have hlower_high :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          totalSupply - alpha * epsilon - epsilon ≤
            independentAffordanceProbability
              (large C μ)
              (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C μ c - vHigh)) := by
    filter_upwards [hlower_high_cutoff] with C hhighC μ
    have hbridge :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (large C μ) vHigh (cutoff C μ)
    simpa [← hbridge] using hhighC μ
  have hdiff :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          independentAffordanceProbability
              (large C μ)
              (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C μ c - vHigh)) -
            independentAffordanceProbability
              (large C μ)
              (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C μ c - vLow)) ≤
            1 - Real.exp (-(2 * epsilon * sigma)) :=
    independentAffordanceProbability_difference_uniform_eventually_le_exp_error_of_upperTailMass_longTailed_highCrossingBound
      (Admissible := Admissible)
      noiseLaw hlong hvStrict hepsilon_pos hepsilon_le_one
      hsigma_nonneg hhigh_le_sigma_div
  have hlarge_le_total :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          independentAffordanceProbability
              (large C μ)
              (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C μ c - v)) ≤
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (total C μ) v (cutoff C μ) := by
    filter_upwards [htotal] with C htotalC μ
    have hsubset : large C μ ⊆ total C μ := by
      intro c hc
      rw [htotalC μ]
      exact Finset.mem_union_right (small C μ) hc
    have hmono :
        cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (large C μ) v (cutoff C μ) ≤
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (total C μ) v (cutoff C μ) :=
      cutoffAffordanceProbability_mono_active
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        hsubset
    have hbridge :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (large C μ) v (cutoff C μ)
    simpa [← hbridge] using hmono
  have htotal_le_sum :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (total C μ) v (cutoff C μ) ≤
            cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (small C μ) v (cutoff C μ) +
              independentAffordanceProbability
                (large C μ)
                (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoff C μ c - v)) := by
    filter_upwards [htotal] with C htotalC μ
    have hdecomp :=
      cutoffAffordanceProbability_decomposition_of_union
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (small := small C μ) (large := large C μ) (total := total C μ)
        (v := v) (cutoff := cutoff C μ) (htotalC μ)
    have hbridge :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (large C μ) v (cutoff C μ)
    simpa [← hbridge] using hdecomp.2
  exact
    ⟨vLow, vHigh, vStar, hvLow, hvHigh, hvStar,
      hpLarge_mono, hpSmall_mono, hmass_upper, hlower_high, hdiff,
      hcard, hcap, hcapacity_lower, hlarge_le_total, htotal_le_sum⟩

/--
Fixed-`alpha` Theorem 2 closure for the concrete iid cutoff-affordance model
with the paper's epsilon-indexed `F_1/F_2` split.  The appendix defines the
small and large college sets after choosing `epsilon`; this theorem exposes
that dependence while still deriving the iid product bridge, small-capacity
bound, and final decomposition internally.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_cutoff_epsilon_indexed_source_endpoint_estimates_capacityRegular_strict_derived
    {Admissible : ℕ → Type*}
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (small large :
      ℝ → ∀ C : ℕ, Admissible C → Finset (Fin (C + 1)))
    (total : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1)))
    (cutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ)
    (capacity : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              total C μ = small epsilon C μ ∪ large epsilon C μ) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, ∀ c ∈ large epsilon C μ,
              lowerCutoff C ≤ cutoff C μ c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, ∀ c ∈ large epsilon C μ,
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C μ c - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (large epsilon C μ) vLow (cutoff C μ) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (large epsilon C μ) vHigh (cutoff C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              ((small epsilon C μ).card : ℝ) ≤
                epsilon * ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              capacityRegular (capacity C μ) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (small epsilon C μ) vStar (cutoff C μ) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (small epsilon C μ) (capacity C μ))) :
    theorem2_uniformAmplificationConclusion Admissible
      (fun C : ℕ => fun μ : Admissible C => fun v : ℝ =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (total C μ) v (cutoff C μ))
      totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_epsilon_indexed_large_small_source_windows
      (Admissible := Admissible)
      (pTotal := fun C : ℕ => fun μ : Admissible C => fun v : ℝ =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (total C μ) v (cutoff C μ))
      (pSmall := fun epsilon : ℝ => fun C : ℕ => fun μ : Admissible C =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (small epsilon C μ) v (cutoff C μ))
      (pLarge := fun epsilon : ℝ => fun C : ℕ => fun μ : Admissible C =>
        fun v : ℝ =>
          independentAffordanceProbability
            (large epsilon C μ)
            (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoff C μ c - v)))
      (totalSupply := totalSupply)
      (alpha := alpha)
      htotalSupply_lt_one ?_
  intro v epsilon sigma hepsilon_pos hsigma_pos hden_pos
  rcases hsource v epsilon sigma hepsilon_pos hsigma_pos hden_pos with
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, htotal, hcutoff_lower, hhigh_le_sigma_div,
      hmass_upper_cutoff, hlower_high_cutoff, hcard, hcapRegular,
      hcapacity_lower⟩
  have hsigma_nonneg : 0 ≤ sigma := le_of_lt hsigma_pos
  have herror_nonneg :
      0 ≤ 1 - Real.exp (-(2 * epsilon * sigma)) := by
    have hexp_le_one :
        Real.exp (-(2 * epsilon * sigma)) ≤ 1 := by
      simpa using
        (Real.exp_le_exp.mpr
          (by nlinarith [hepsilon_pos.le, hsigma_nonneg] :
            -(2 * epsilon * sigma) ≤ (0 : ℝ)))
    linarith
  have hS_eps_lt_one : totalSupply + epsilon < 1 := by
    linarith
  have hepsilon_le_one : epsilon ≤ 1 := by
    linarith
  have hmass_upper :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          (1 - epsilon) *
              independentAffordanceProbability
                (large epsilon C μ)
                (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoff C μ c - vLow)) ≤
            totalSupply := by
    filter_upwards [hmass_upper_cutoff] with C hmassC μ
    have hbridge :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (large epsilon C μ) vLow (cutoff C μ)
    simpa [← hbridge] using hmassC μ
  have hlower_high :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          totalSupply - alpha * epsilon - epsilon ≤
            independentAffordanceProbability
              (large epsilon C μ)
              (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C μ c - vHigh)) := by
    filter_upwards [hlower_high_cutoff] with C hhighC μ
    have hbridge :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (large epsilon C μ) vHigh (cutoff C μ)
    simpa [← hbridge] using hhighC μ
  have hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          theorem2_largeFirmSourceWindow totalSupply alpha epsilon sigma
            (independentAffordanceProbability
              (large epsilon C μ)
              (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C μ c - v))) :=
    theorem2_largeFirmSourceWindow_uniform_eventually_of_upperTail_longTail_source_endpoint_estimates_strict_derived
      (Admissible := Admissible)
      (noiseLaw := noiseLaw)
      (hlong := hlong)
      (active := fun C : ℕ => fun μ : Admissible C => large epsilon C μ)
      (cutoff := cutoff)
      (lowerCutoff := lowerCutoff)
      (vLow := vLow) (vHigh := vHigh) (v := v)
      (S := totalSupply) (α := alpha) (ε := epsilon) (σ := sigma)
      hvLow hvHigh hvStrict hepsilon_pos hepsilon_le_one
      htotalSupply_nonneg hS_eps_lt_one hsigma_nonneg
      hlower_atTop hcutoff_lower hhigh_le_sigma_div hmass_upper
      hlower_high
  have hpSmall_mono :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          Monotone (fun w : ℝ =>
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (small epsilon C μ) w (cutoff C μ)) := by
    exact Filter.Eventually.of_forall (fun C => by
      intro μ x y hxy
      exact
        cutoffAffordanceProbability_mono_value
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (active := small epsilon C μ) (cutoff := cutoff C μ) hxy)
  have hcap :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C, ∀ c ∈ small epsilon C μ,
          capacity C μ c ≤ alpha / ((C + 1 : ℕ) : ℝ) := by
    filter_upwards [hcapRegular] with C hC μ c hc
    exact capacityRegular.le (hC μ) c
  have hsmall :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          theorem2_smallFirmSourceBound totalSupply alpha epsilon sigma
            (cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (small epsilon C μ) v (cutoff C μ)) :=
    theorem2_smallFirmSourceBound_eventually_of_star_active_capacity_lower_bound
      (Admissible := Admissible)
      (small := fun C : ℕ => fun μ : Admissible C => small epsilon C μ)
      (capacity := capacity)
      (pSmall := fun C : ℕ => fun μ : Admissible C => fun v : ℝ =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (small epsilon C μ) v (cutoff C μ))
      (v := v) (vStar := vStar) (totalSupply := totalSupply)
      (alpha := alpha) (epsilon := epsilon) (sigma := sigma)
      hepsilon_pos hden_pos hpSmall_mono hvStar hcard
      halpha_nonneg hcap hcapacity_lower
  have hlarge_le_total :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          independentAffordanceProbability
              (large epsilon C μ)
              (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C μ c - v)) ≤
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (total C μ) v (cutoff C μ) := by
    filter_upwards [htotal] with C htotalC μ
    have hsubset : large epsilon C μ ⊆ total C μ := by
      intro c hc
      rw [htotalC μ]
      exact Finset.mem_union_right (small epsilon C μ) hc
    have hmono :
        cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (large epsilon C μ) v (cutoff C μ) ≤
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (total C μ) v (cutoff C μ) :=
      cutoffAffordanceProbability_mono_active
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        hsubset
    have hbridge :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (large epsilon C μ) v (cutoff C μ)
    simpa [← hbridge] using hmono
  have htotal_le_sum :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (total C μ) v (cutoff C μ) ≤
            cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (small epsilon C μ) v (cutoff C μ) +
              independentAffordanceProbability
                (large epsilon C μ)
                (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoff C μ c - v)) := by
    filter_upwards [htotal] with C htotalC μ
    have hdecomp :=
      cutoffAffordanceProbability_decomposition_of_union
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (small := small epsilon C μ) (large := large epsilon C μ)
        (total := total C μ) (v := v) (cutoff := cutoff C μ)
        (htotalC μ)
    have hbridge :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (large epsilon C μ) v (cutoff C μ)
    simpa [← hbridge] using hdecomp.2
  exact ⟨hlarge, hsmall, hlarge_le_total, htotal_le_sum⟩

/--
Concrete iid cutoff Theorem 2 route with the paper's epsilon-indexed
`F_1/F_2` split and a direct high-tail-rate large-firm premise.

This is the epsilon-indexed counterpart of
`theorem2_uniformAmplification_of_fixed_alpha_iidProduct_cutoff_highTailRate_source_endpoint_estimates_strict_derived`.
It keeps the appendix split shape but removes the lower-cutoff witness and its
divergence premise from the source package.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_cutoff_epsilon_indexed_highTailRate_source_endpoint_estimates_capacityRegular_strict_derived
    {Admissible : ℕ → Type*}
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (small large :
      ℝ → ∀ C : ℕ, Admissible C → Finset (Fin (C + 1)))
    (total : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1)))
    (cutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ)
    (capacity : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              total C μ = small epsilon C μ ∪ large epsilon C μ) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, ∀ c ∈ large epsilon C μ,
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C μ c - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (large epsilon C μ) vLow (cutoff C μ) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (large epsilon C μ) vHigh (cutoff C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              ((small epsilon C μ).card : ℝ) ≤
                epsilon * ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              capacityRegular (capacity C μ) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (small epsilon C μ) vStar (cutoff C μ) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (small epsilon C μ) (capacity C μ))) :
    theorem2_uniformAmplificationConclusion Admissible
      (fun C : ℕ => fun μ : Admissible C => fun v : ℝ =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (total C μ) v (cutoff C μ))
      totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_epsilon_indexed_large_small_source_windows
      (Admissible := Admissible)
      (pTotal := fun C : ℕ => fun μ : Admissible C => fun v : ℝ =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (total C μ) v (cutoff C μ))
      (pSmall := fun epsilon : ℝ => fun C : ℕ => fun μ : Admissible C =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (small epsilon C μ) v (cutoff C μ))
      (pLarge := fun epsilon : ℝ => fun C : ℕ => fun μ : Admissible C =>
        fun v : ℝ =>
          independentAffordanceProbability
            (large epsilon C μ)
            (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoff C μ c - v)))
      (totalSupply := totalSupply)
      (alpha := alpha)
      htotalSupply_lt_one ?_
  intro v epsilon sigma hepsilon_pos hsigma_pos hden_pos
  rcases hsource v epsilon sigma hepsilon_pos hsigma_pos hden_pos with
    ⟨vLow, vHigh, vStar, hvLow, hvHigh, hvStar, hvStrict,
      htotal, hhigh_le_sigma_div, hmass_upper_cutoff,
      hlower_high_cutoff, hcard, hcapRegular, hcapacity_lower⟩
  have hsigma_nonneg : 0 ≤ sigma := le_of_lt hsigma_pos
  have herror_nonneg :
      0 ≤ 1 - Real.exp (-(2 * epsilon * sigma)) := by
    have hexp_le_one :
        Real.exp (-(2 * epsilon * sigma)) ≤ 1 := by
      simpa using
        (Real.exp_le_exp.mpr
          (by nlinarith [hepsilon_pos.le, hsigma_nonneg] :
            -(2 * epsilon * sigma) ≤ (0 : ℝ)))
    linarith
  have hS_eps_lt_one : totalSupply + epsilon < 1 := by
    linarith
  have hepsilon_le_one : epsilon ≤ 1 := by
    linarith
  have hmass_upper :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          (1 - epsilon) *
              independentAffordanceProbability
                (large epsilon C μ)
                (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoff C μ c - vLow)) ≤
            totalSupply := by
    filter_upwards [hmass_upper_cutoff] with C hmassC μ
    have hbridge :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (large epsilon C μ) vLow (cutoff C μ)
    simpa [← hbridge] using hmassC μ
  have hlower_high :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          totalSupply - alpha * epsilon - epsilon ≤
            independentAffordanceProbability
              (large epsilon C μ)
              (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C μ c - vHigh)) := by
    filter_upwards [hlower_high_cutoff] with C hhighC μ
    have hbridge :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (large epsilon C μ) vHigh (cutoff C μ)
    simpa [← hbridge] using hhighC μ
  have hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          theorem2_largeFirmSourceWindow totalSupply alpha epsilon sigma
            (independentAffordanceProbability
              (large epsilon C μ)
              (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C μ c - v))) :=
    theorem2_largeFirmSourceWindow_uniform_eventually_of_upperTail_highTailRate_source_endpoint_estimates_strict_derived
      (Admissible := Admissible)
      (noiseLaw := noiseLaw)
      (hlong := hlong)
      (active := fun C : ℕ => fun μ : Admissible C => large epsilon C μ)
      (cutoff := cutoff)
      (vLow := vLow) (vHigh := vHigh) (v := v)
      (S := totalSupply) (α := alpha) (ε := epsilon) (σ := sigma)
      hvLow hvHigh hvStrict hepsilon_pos hepsilon_le_one
      htotalSupply_nonneg hS_eps_lt_one hsigma_nonneg
      hhigh_le_sigma_div hmass_upper hlower_high
  have hpSmall_mono :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          Monotone (fun w : ℝ =>
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (small epsilon C μ) w (cutoff C μ)) := by
    exact Filter.Eventually.of_forall (fun C => by
      intro μ x y hxy
      exact
        cutoffAffordanceProbability_mono_value
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (active := small epsilon C μ) (cutoff := cutoff C μ) hxy)
  have hcap :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C, ∀ c ∈ small epsilon C μ,
          capacity C μ c ≤ alpha / ((C + 1 : ℕ) : ℝ) := by
    filter_upwards [hcapRegular] with C hC μ c hc
    exact capacityRegular.le (hC μ) c
  have hsmall :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          theorem2_smallFirmSourceBound totalSupply alpha epsilon sigma
            (cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (small epsilon C μ) v (cutoff C μ)) :=
    theorem2_smallFirmSourceBound_eventually_of_star_active_capacity_lower_bound
      (Admissible := Admissible)
      (small := fun C : ℕ => fun μ : Admissible C => small epsilon C μ)
      (capacity := capacity)
      (pSmall := fun C : ℕ => fun μ : Admissible C => fun v : ℝ =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (small epsilon C μ) v (cutoff C μ))
      (v := v) (vStar := vStar) (totalSupply := totalSupply)
      (alpha := alpha) (epsilon := epsilon) (sigma := sigma)
      hepsilon_pos hden_pos hpSmall_mono hvStar hcard
      halpha_nonneg hcap hcapacity_lower
  have hlarge_le_total :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          independentAffordanceProbability
              (large epsilon C μ)
              (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C μ c - v)) ≤
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (total C μ) v (cutoff C μ) := by
    filter_upwards [htotal] with C htotalC μ
    have hsubset : large epsilon C μ ⊆ total C μ := by
      intro c hc
      rw [htotalC μ]
      exact Finset.mem_union_right (small epsilon C μ) hc
    have hmono :
        cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (large epsilon C μ) v (cutoff C μ) ≤
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (total C μ) v (cutoff C μ) :=
      cutoffAffordanceProbability_mono_active
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        hsubset
    have hbridge :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (large epsilon C μ) v (cutoff C μ)
    simpa [← hbridge] using hmono
  have htotal_le_sum :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (total C μ) v (cutoff C μ) ≤
            cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (small epsilon C μ) v (cutoff C μ) +
              independentAffordanceProbability
                (large epsilon C μ)
                (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoff C μ c - v)) := by
    filter_upwards [htotal] with C htotalC μ
    have hdecomp :=
      cutoffAffordanceProbability_decomposition_of_union
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (small := small epsilon C μ) (large := large epsilon C μ)
        (total := total C μ) (v := v) (cutoff := cutoff C μ)
        (htotalC μ)
    have hbridge :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (large epsilon C μ) v (cutoff C μ)
    simpa [← hbridge] using hdecomp.2
  exact ⟨hlarge, hsmall, hlarge_le_total, htotal_le_sum⟩

/--
Concrete iid cutoff Theorem 2 route with separated split and long-tail ratio
parameters.

The source contract is tolerance-level rather than universal in the displayed
one-scale `epsilon, sigma`: for each target tolerance it supplies a split size
`delta`, a long-tail ratio tolerance `rho`, and a high-tail-rate constant
`sigma` whose two-scale errors are already below the target.  This is the
source-faithful repaired shape of the amplification appendix.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_cutoff_twoScale_highTailRate_source_endpoint_estimates_capacityRegular_strict_derived
    {Admissible : ℕ → Type*}
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (small large :
      ℝ → ∀ C : ℕ, Admissible C → Finset (Fin (C + 1)))
    (total : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1)))
    (cutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ)
    (capacity : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (halpha_nonneg : 0 ≤ alpha)
    (hsource :
      ∀ v tol, 0 < tol →
        ∃ delta rho sigma : ℝ,
          0 < delta ∧ 0 < rho ∧ rho ≤ 1 ∧ 0 ≤ sigma ∧
          0 <
            1 - totalSupply - delta -
              (1 - Real.exp (-(2 * rho * sigma))) ∧
          theorem2_twoScaleSourceLowerError alpha delta rho sigma < tol ∧
          theorem2_twoScaleSourceUpperError
            totalSupply alpha delta rho sigma < tol ∧
          ∃ vLow vHigh vStar : ℝ,
            vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
            (∀ᶠ C : ℕ in atTop,
              ∀ μ : Admissible C,
                total C μ = small delta C μ ∪ large delta C μ) ∧
            (∀ᶠ C : ℕ in atTop,
              ∀ μ : Admissible C, ∀ c ∈ large delta C μ,
                AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoff C μ c - vHigh) ≤
                  sigma / ((C + 1 : ℕ) : ℝ)) ∧
            (∀ᶠ C : ℕ in atTop,
              ∀ μ : Admissible C,
                (1 - delta) *
                    cutoffAffordanceProbability
                      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                      (large delta C μ) vLow (cutoff C μ) ≤
                  totalSupply) ∧
            (∀ᶠ C : ℕ in atTop,
              ∀ μ : Admissible C,
                totalSupply - alpha * delta - delta ≤
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (large delta C μ) vHigh (cutoff C μ)) ∧
            (∀ᶠ C : ℕ in atTop,
              ∀ μ : Admissible C,
                ((small delta C μ).card : ℝ) ≤
                  delta * ((C + 1 : ℕ) : ℝ)) ∧
            (∀ᶠ C : ℕ in atTop,
              ∀ μ : Admissible C,
                capacityRegular (capacity C μ) alpha (C + 1)) ∧
            (∀ᶠ C : ℕ in atTop,
              ∀ μ : Admissible C,
                Real.sqrt delta *
                    (1 - totalSupply - delta -
                      (1 - Real.exp (-(2 * rho * sigma)))) *
                    cutoffAffordanceProbability
                      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                      (small delta C μ) vStar (cutoff C μ) ≤
                  AppliedModelingLib.Matching.activeCapacity
                    (small delta C μ) (capacity C μ))) :
    theorem2_uniformAmplificationConclusion Admissible
      (fun C : ℕ => fun μ : Admissible C => fun v : ℝ =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (total C μ) v (cutoff C μ))
      totalSupply := by
  refine theorem2_uniformAmplification_of_twoScale_eventual_source_window ?_
  intro v tol htol
  rcases hsource v tol htol with
    ⟨delta, rho, sigma, hdelta_pos, hrho_pos, hrho_le_one,
      hsigma_nonneg, hden_pos, hlower_small, hupper_small,
      vLow, vHigh, vStar, hvLow, hvHigh, hvStar, hvStrict,
      htotal, hhigh_le_sigma_div, hmass_upper_cutoff,
      hlower_high_cutoff, hcard, hcapRegular, hcapacity_lower⟩
  have herror_nonneg :
      0 ≤ 1 - Real.exp (-(2 * rho * sigma)) := by
    have hexp_le_one :
        Real.exp (-(2 * rho * sigma)) ≤ 1 := by
      simpa using
        (Real.exp_le_exp.mpr
          (by nlinarith [hrho_pos.le, hsigma_nonneg] :
            -(2 * rho * sigma) ≤ (0 : ℝ)))
    linarith
  have hS_delta_lt_one : totalSupply + delta < 1 := by
    linarith
  have hmass_upper :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          (1 - delta) *
              independentAffordanceProbability
                (large delta C μ)
                (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoff C μ c - vLow)) ≤
            totalSupply := by
    filter_upwards [hmass_upper_cutoff] with C hmassC μ
    have hbridge :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (large delta C μ) vLow (cutoff C μ)
    simpa [← hbridge] using hmassC μ
  have hlower_high :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          totalSupply - alpha * delta - delta ≤
            independentAffordanceProbability
              (large delta C μ)
              (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C μ c - vHigh)) := by
    filter_upwards [hlower_high_cutoff] with C hhighC μ
    have hbridge :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (large delta C μ) vHigh (cutoff C μ)
    simpa [← hbridge] using hhighC μ
  have hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          theorem2_twoScaleLargeFirmSourceWindow
            totalSupply alpha delta rho sigma
            (independentAffordanceProbability
              (large delta C μ)
              (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C μ c - v))) :=
    theorem2_twoScaleLargeFirmSourceWindow_uniform_eventually_of_upperTail_highTailRate_source_endpoint_estimates_strict_derived
      (Admissible := Admissible)
      (noiseLaw := noiseLaw) (hlong := hlong)
      (active := fun C : ℕ => fun μ : Admissible C => large delta C μ)
      (cutoff := cutoff)
      (vLow := vLow) (vHigh := vHigh) (v := v)
      (S := totalSupply) (α := alpha)
      (delta := delta) (rho := rho) (sigma := sigma)
      hvLow hvHigh hvStrict hdelta_pos hrho_pos hrho_le_one
      htotalSupply_nonneg hS_delta_lt_one hsigma_nonneg
      hhigh_le_sigma_div hmass_upper hlower_high
  have hpSmall_mono :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          Monotone (fun w : ℝ =>
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (small delta C μ) w (cutoff C μ)) := by
    exact Filter.Eventually.of_forall (fun C => by
      intro μ x y hxy
      exact
        cutoffAffordanceProbability_mono_value
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (active := small delta C μ) (cutoff := cutoff C μ) hxy)
  have hcap :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C, ∀ c ∈ small delta C μ,
          capacity C μ c ≤ alpha / ((C + 1 : ℕ) : ℝ) := by
    filter_upwards [hcapRegular] with C hC μ c hc
    exact capacityRegular.le (hC μ) c
  have hsmall :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          theorem2_twoScaleSmallFirmSourceBound
            totalSupply alpha delta rho sigma
            (cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (small delta C μ) v (cutoff C μ)) :=
    theorem2_twoScaleSmallFirmSourceBound_eventually_of_star_active_capacity_lower_bound
      (Admissible := Admissible)
      (small := fun C : ℕ => fun μ : Admissible C => small delta C μ)
      (capacity := capacity)
      (pSmall := fun C : ℕ => fun μ : Admissible C => fun v : ℝ =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (small delta C μ) v (cutoff C μ))
      (v := v) (vStar := vStar) (totalSupply := totalSupply)
      (alpha := alpha) (delta := delta) (rho := rho) (sigma := sigma)
      hdelta_pos hden_pos hpSmall_mono hvStar hcard
      halpha_nonneg hcap hcapacity_lower
  have hlarge_le_total :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          independentAffordanceProbability
              (large delta C μ)
              (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C μ c - v)) ≤
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (total C μ) v (cutoff C μ) := by
    filter_upwards [htotal] with C htotalC μ
    have hsubset : large delta C μ ⊆ total C μ := by
      intro c hc
      rw [htotalC μ]
      exact Finset.mem_union_right (small delta C μ) hc
    have hmono :
        cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (large delta C μ) v (cutoff C μ) ≤
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (total C μ) v (cutoff C μ) :=
      cutoffAffordanceProbability_mono_active
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        hsubset
    have hbridge :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (large delta C μ) v (cutoff C μ)
    simpa [← hbridge] using hmono
  have htotal_le_sum :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (total C μ) v (cutoff C μ) ≤
            cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (small delta C μ) v (cutoff C μ) +
              independentAffordanceProbability
                (large delta C μ)
                (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoff C μ c - v)) := by
    filter_upwards [htotal] with C htotalC μ
    have hdecomp :=
      cutoffAffordanceProbability_decomposition_of_union
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (small := small delta C μ) (large := large delta C μ)
        (total := total C μ) (v := v) (cutoff := cutoff C μ)
        (htotalC μ)
    have hbridge :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (large delta C μ) v (cutoff C μ)
    simpa [← hbridge] using hdecomp.2
  have hevent :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : Admissible C,
          totalSupply -
                theorem2_twoScaleSourceLowerError alpha delta rho sigma ≤
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (total C μ) v (cutoff C μ) ∧
            cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (total C μ) v (cutoff C μ) ≤
              totalSupply +
                theorem2_twoScaleSourceUpperError
                  totalSupply alpha delta rho sigma :=
    theorem2_uniform_twoScale_source_window_eventually_of_large_small_firm_bounds
      (Admissible := Admissible)
      (pTotal := fun C : ℕ => fun μ : Admissible C => fun v : ℝ =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (total C μ) v (cutoff C μ))
      (pSmall := fun C : ℕ => fun μ : Admissible C => fun v : ℝ =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (small delta C μ) v (cutoff C μ))
      (pLarge := fun C : ℕ => fun μ : Admissible C => fun v : ℝ =>
        independentAffordanceProbability
          (large delta C μ)
          (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff C μ c - v)))
      (v := v) (totalSupply := totalSupply)
      (alpha := alpha) (delta := delta) (rho := rho) (sigma := sigma)
      hlarge hsmall hlarge_le_total htotal_le_sum
  exact ⟨alpha, delta, rho, sigma, hlower_small, hupper_small, hevent⟩

/--
Concrete iid cutoff Theorem 2 route with the small-firm interval integral
exposed.

This is the paper-facing version of Proposition `lt-small-firms`: the source
chooses the value interval above `vStar`, proves its `η`-mass is at least
`sqrt(epsilon)`, and bounds the displayed integral by the small block's active
capacity.  Lean derives the previously assumed small-capacity lower bound
using monotonicity and nonnegativity of cutoff-affordance probabilities.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_cutoff_epsilon_indexed_source_endpoint_estimates_small_interval_integral_capacityRegular_strict_derived
    {Admissible : ℕ → Type*}
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (small large :
      ℝ → ∀ C : ℕ, Admissible C → Finset (Fin (C + 1)))
    (total : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1)))
    (cutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ)
    (capacity : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
        ∃ smallInterval : ∀ C : ℕ, Admissible C → Set ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              total C μ = small epsilon C μ ∪ large epsilon C μ) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, ∀ c ∈ large epsilon C μ,
              lowerCutoff C ≤ cutoff C μ c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C, ∀ c ∈ large epsilon C μ,
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C μ c - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (large epsilon C μ) vLow (cutoff C μ) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (large epsilon C μ) vHigh (cutoff C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              ((small epsilon C μ).card : ℝ) ≤
                epsilon * ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              capacityRegular (capacity C μ) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              MeasurableSet (smallInterval C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              Integrable
                (fun w : ℝ =>
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                    cutoffAffordanceProbability
                      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                      (small epsilon C μ) w (cutoff C μ)) η) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              Real.sqrt epsilon ≤ η.real (smallInterval C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              ∀ w : ℝ, w ∈ smallInterval C μ → vStar ≤ w) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              (∫ w : ℝ,
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                    cutoffAffordanceProbability
                      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                      (small epsilon C μ) w (cutoff C μ) ∂η) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (small epsilon C μ) (capacity C μ))) :
    theorem2_uniformAmplificationConclusion Admissible
      (fun C : ℕ => fun μ : Admissible C => fun v : ℝ =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (total C μ) v (cutoff C μ))
      totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_cutoff_epsilon_indexed_source_endpoint_estimates_capacityRegular_strict_derived
      noiseLaw hlong small large total cutoff capacity
      htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg ?_
  intro v epsilon sigma hepsilon_pos hsigma_pos hden_pos
  rcases hsource v epsilon sigma hepsilon_pos hsigma_pos hden_pos with
    ⟨vLow, vHigh, vStar, lowerCutoff, smallInterval,
      hvLow, hvHigh, hvStar, hvStrict, hlower_atTop, htotal,
      hcutoff_lower, hhigh_le_sigma_div, hmass_upper, hlower_high,
      hcard, hcapRegular, hsmall_meas, hsmall_int, hsmall_mass,
      hsmall_ge, hsmall_integral_capacity⟩
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff,
      hvLow, hvHigh, hvStar, hvStrict, hlower_atTop, htotal,
      hcutoff_lower, hhigh_le_sigma_div, hmass_upper, hlower_high,
      hcard, hcapRegular, ?_⟩
  filter_upwards
    [hsmall_meas, hsmall_int, hsmall_mass, hsmall_ge,
      hsmall_integral_capacity] with
    C hmeasC hintC hmassC hgeC hintegralC μ
  have hpSmall_mono :
      Monotone (fun w : ℝ =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (small epsilon C μ) w (cutoff C μ)) := by
    intro x y hxy
    exact
      cutoffAffordanceProbability_mono_value
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (active := small epsilon C μ) (cutoff := cutoff C μ) hxy
  have hpStar_nonneg :
      0 ≤
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (small epsilon C μ) vStar (cutoff C μ) :=
    cutoffAffordanceProbability_nonneg
      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
      (small epsilon C μ) vStar (cutoff C μ)
  have hnonneg_compl :
      ∀ w : ℝ, w ∉ smallInterval C μ →
        0 ≤
          (1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma)))) *
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (small epsilon C μ) w (cutoff C μ) := by
    intro w _hw
    exact
      mul_nonneg (le_of_lt hden_pos)
        (cutoffAffordanceProbability_nonneg
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (small epsilon C μ) w (cutoff C μ))
  exact
    theorem2_smallFirm_matchedMass_lower_bound_of_interval_integral
      η
      (region := smallInterval C μ)
      (mass := Real.sqrt epsilon)
      (denom :=
        1 - totalSupply - epsilon -
          (1 - Real.exp (-(2 * epsilon * sigma))))
      (matchedMass :=
        AppliedModelingLib.Matching.activeCapacity
          (small epsilon C μ) (capacity C μ))
      (pSmall := fun w : ℝ =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (small epsilon C μ) w (cutoff C μ))
      (vStar := vStar)
      (hmeasC μ) (hintC μ) (hmassC μ) (le_of_lt hden_pos)
      hpStar_nonneg hpSmall_mono (hgeC μ) hnonneg_compl
      (hintegralC μ)

/--
Concrete ordered-split Theorem 2 route for the finite iid cutoff-affordance
model.  The paper sorts colleges by cutoff and defines `F_1` as the initial
`epsilon*C` block and `F_2` as the remaining colleges.  This theorem exposes
that construction through a numeric split index: the union and small-cardinality
clauses are derived from `indexPrefixSmall`/`indexSuffixLarge`, while the
analytic endpoint estimates remain visible as source work.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_cutoff_index_split_source_endpoint_estimates_capacityRegular_strict_derived
    {Admissible : ℕ → Type*}
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (splitIndex : ℝ → ℕ → ℕ)
    (cutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ)
    (capacity : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hsplit_card :
      ∀ epsilon, 0 < epsilon →
        ∀ᶠ C : ℕ in atTop,
          (splitIndex epsilon C : ℝ) ≤
            epsilon * ((C + 1 : ℕ) : ℝ))
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              ∀ c ∈ indexSuffixLarge (splitIndex epsilon C) C,
                lowerCutoff C ≤ cutoff C μ c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              ∀ c ∈ indexSuffixLarge (splitIndex epsilon C) C,
                AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoff C μ c - vHigh) ≤
                  sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (splitIndex epsilon C) C)
                    vLow (cutoff C μ) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (splitIndex epsilon C) C)
                  vHigh (cutoff C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              capacityRegular (capacity C μ) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (splitIndex epsilon C) C)
                    vStar (cutoff C μ) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (indexPrefixSmall (splitIndex epsilon C) C)
                  (capacity C μ))) :
    theorem2_uniformAmplificationConclusion Admissible
      (fun C : ℕ => fun μ : Admissible C => fun v : ℝ =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) v (cutoff C μ))
      totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_cutoff_epsilon_indexed_source_endpoint_estimates_capacityRegular_strict_derived
      (Admissible := Admissible)
      (noiseLaw := noiseLaw) (hlong := hlong)
      (small := fun epsilon C _μ =>
        indexPrefixSmall (splitIndex epsilon C) C)
      (large := fun epsilon C _μ =>
        indexSuffixLarge (splitIndex epsilon C) C)
      (total := fun C _μ => (Finset.univ : Finset (Fin (C + 1))))
      (cutoff := cutoff) (capacity := capacity)
      (totalSupply := totalSupply) (alpha := alpha)
      htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_lower, hhigh_le_sigma_div, hmass_upper,
      hlower_high, hcapRegular, hcapacity_lower⟩
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, ?_, hcutoff_lower, hhigh_le_sigma_div, hmass_upper,
      hlower_high, ?_, hcapRegular, hcapacity_lower⟩
  · exact Filter.Eventually.of_forall (fun C => by
      intro μ
      exact indexPrefixSmall_union_indexSuffixLarge (splitIndex epsilon C) C)
  · filter_upwards [hsplit_card epsilon hepsilon] with C hC μ
    exact
      le_trans
        (indexPrefixSmall_card_le_index (splitIndex epsilon C) C)
        hC

/--
Concrete ordered-split Theorem 2 route with the small-firm interval integral
exposed.  This is the sorted-prefix/suffix specialization of the iid
interval-integral route, deriving the small-cardinality clause from the split
index and the small-capacity lower bound from the source integral.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_cutoff_index_split_source_endpoint_estimates_small_interval_integral_capacityRegular_strict_derived
    {Admissible : ℕ → Type*}
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (splitIndex : ℝ → ℕ → ℕ)
    (cutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ)
    (capacity : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hsplit_card :
      ∀ epsilon, 0 < epsilon →
        ∀ᶠ C : ℕ in atTop,
          (splitIndex epsilon C : ℝ) ≤
            epsilon * ((C + 1 : ℕ) : ℝ))
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
        ∃ smallInterval : ∀ C : ℕ, Admissible C → Set ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              ∀ c ∈ indexSuffixLarge (splitIndex epsilon C) C,
                lowerCutoff C ≤ cutoff C μ c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              ∀ c ∈ indexSuffixLarge (splitIndex epsilon C) C,
                AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoff C μ c - vHigh) ≤
                  sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (splitIndex epsilon C) C)
                    vLow (cutoff C μ) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (splitIndex epsilon C) C)
                  vHigh (cutoff C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              capacityRegular (capacity C μ) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              MeasurableSet (smallInterval C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              Integrable
                (fun w : ℝ =>
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                    cutoffAffordanceProbability
                      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                      (indexPrefixSmall (splitIndex epsilon C) C)
                      w (cutoff C μ)) η) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              Real.sqrt epsilon ≤ η.real (smallInterval C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              ∀ w : ℝ, w ∈ smallInterval C μ → vStar ≤ w) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              (∫ w : ℝ,
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                    cutoffAffordanceProbability
                      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                      (indexPrefixSmall (splitIndex epsilon C) C)
                      w (cutoff C μ) ∂η) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (indexPrefixSmall (splitIndex epsilon C) C)
                  (capacity C μ))) :
    theorem2_uniformAmplificationConclusion Admissible
      (fun C : ℕ => fun μ : Admissible C => fun v : ℝ =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) v (cutoff C μ))
      totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_cutoff_epsilon_indexed_source_endpoint_estimates_small_interval_integral_capacityRegular_strict_derived
      η noiseLaw hlong
      (small := fun epsilon C _μ =>
        indexPrefixSmall (splitIndex epsilon C) C)
      (large := fun epsilon C _μ =>
        indexSuffixLarge (splitIndex epsilon C) C)
      (total := fun C _μ => (Finset.univ : Finset (Fin (C + 1))))
      (cutoff := cutoff) (capacity := capacity)
      (totalSupply := totalSupply) (alpha := alpha)
      htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, smallInterval,
      hvLow, hvHigh, hvStar, hvStrict, hlower_atTop,
      hcutoff_lower, hhigh_le_sigma_div, hmass_upper, hlower_high,
      hcapRegular, hsmall_meas, hsmall_int, hsmall_mass, hsmall_ge,
      hsmall_integral_capacity⟩
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff, smallInterval,
      hvLow, hvHigh, hvStar, hvStrict, hlower_atTop, ?_,
      hcutoff_lower, hhigh_le_sigma_div, hmass_upper, hlower_high,
      ?_, hcapRegular, hsmall_meas, hsmall_int, hsmall_mass, hsmall_ge,
      hsmall_integral_capacity⟩
  · exact Filter.Eventually.of_forall (fun C => by
      intro μ
      exact indexPrefixSmall_union_indexSuffixLarge (splitIndex epsilon C) C)
  · filter_upwards [hsplit_card epsilon hepsilon] with C hC μ
    exact
      le_trans
        (indexPrefixSmall_card_le_index (splitIndex epsilon C) C)
        hC

/--
Concrete floor-index version of the ordered-split Theorem 2 route.  This
removes the separate split-cardinality premise by setting the split index to
`floor (epsilon * (C+1))`.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_cutoff_floor_index_split_source_endpoint_estimates_capacityRegular_strict_derived
    {Admissible : ℕ → Type*}
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ)
    (capacity : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
                lowerCutoff C ≤ cutoff C μ c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
                AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoff C μ c - vHigh) ≤
                  sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow (cutoff C μ) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh (cutoff C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              capacityRegular (capacity C μ) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar (cutoff C μ) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                  (capacity C μ))) :
    theorem2_uniformAmplificationConclusion Admissible
      (fun C : ℕ => fun μ : Admissible C => fun v : ℝ =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) v (cutoff C μ))
      totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_cutoff_index_split_source_endpoint_estimates_capacityRegular_strict_derived
      (Admissible := Admissible)
      (noiseLaw := noiseLaw) (hlong := hlong)
      (splitIndex := epsilonFloorSplitIndex)
      (cutoff := cutoff) (capacity := capacity)
      (totalSupply := totalSupply) (alpha := alpha)
      htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg ?_
      hsource
  intro epsilon hepsilon
  exact Filter.Eventually.of_forall (fun C =>
    epsilonFloorSplitIndex_le epsilon C hepsilon.le)

/--
Concrete floor-index Theorem 2 route with the small-firm interval integral
exposed.  This is the appendix split `floor(epsilon * (C+1))`, with the
small-firm source inequality derived from the value-interval integral.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_cutoff_floor_index_split_source_endpoint_estimates_small_interval_integral_capacityRegular_strict_derived
    {Admissible : ℕ → Type*}
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ)
    (capacity : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
        ∃ smallInterval : ∀ C : ℕ, Admissible C → Set ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
                lowerCutoff C ≤ cutoff C μ c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
                AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoff C μ c - vHigh) ≤
                  sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow (cutoff C μ) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh (cutoff C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              capacityRegular (capacity C μ) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              MeasurableSet (smallInterval C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              Integrable
                (fun w : ℝ =>
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                    cutoffAffordanceProbability
                      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                      (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                      w (cutoff C μ)) η) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              Real.sqrt epsilon ≤ η.real (smallInterval C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              ∀ w : ℝ, w ∈ smallInterval C μ → vStar ≤ w) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              (∫ w : ℝ,
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                    cutoffAffordanceProbability
                      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                      (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                      w (cutoff C μ) ∂η) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                  (capacity C μ))) :
    theorem2_uniformAmplificationConclusion Admissible
      (fun C : ℕ => fun μ : Admissible C => fun v : ℝ =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) v (cutoff C μ))
      totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_cutoff_index_split_source_endpoint_estimates_small_interval_integral_capacityRegular_strict_derived
      η noiseLaw hlong
      (splitIndex := epsilonFloorSplitIndex)
      (cutoff := cutoff) (capacity := capacity)
      (totalSupply := totalSupply) (alpha := alpha)
      htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg ?_
      hsource
  intro epsilon hepsilon
  exact Filter.Eventually.of_forall (fun C =>
    epsilonFloorSplitIndex_le epsilon C hepsilon.le)

/--
Fixed-`alpha` Theorem 2 closure over stable matchings themselves.

This is the stable-matching version of the concrete iid cutoff-affordance
route.  A-L Lemma 1 selects the market-clearing cutoff representing each
stable matching; the source endpoint, capacity, and decomposition estimates
are stated for all market-clearing cutoffs and then specialized internally to
those selected cutoffs.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_source_endpoint_estimates_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (small large total :
      ∀ C : ℕ, (Mseq C).Cutoff → Finset (Fin (C + 1)))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (capacity : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              total C P = small C P ∪ large C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c ∈ large C P, lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c ∈ large C P,
                AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoffOut C P c - vHigh) ≤
                  sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (large C P) vLow (cutoffOut C P) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (large C P) vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ((small C P).card : ℝ) ≤
                epsilon * ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c ∈ small C P,
                capacity C P c ≤ alpha / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (small C P) vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity (small C P) (capacity C P))) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (total C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))
            v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  have hmc :
      ∀ C : ℕ,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          (Mseq C).MarketClearing
            ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2) := by
    intro C μ
    exact
      (Iseq C).marketClearingCutoffOfStable_marketClearing
        (μ := μ.1) μ.2
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_cutoff_source_endpoint_estimates_strict_derived
      (Admissible := fun C : ℕ =>
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (noiseLaw := noiseLaw) (hlong := hlong)
      (small := fun C μ =>
        small C ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))
      (large := fun C μ =>
        large C ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))
      (total := fun C μ =>
        total C ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))
      (cutoff := fun C μ =>
        cutoffOut C ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))
      (capacity := fun C μ =>
        capacity C ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))
      (totalSupply := totalSupply) (alpha := alpha)
      htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, htotal, hcutoff_lower, hhigh_le_sigma_div,
      hmass_upper, hlower_high, hcard, hcap, hcapacity_lower⟩
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [htotal] with C hC μ
    exact hC _ (hmc C μ)
  · filter_upwards [hcutoff_lower] with C hC μ c hc
    exact hC _ (hmc C μ) c hc
  · filter_upwards [hhigh_le_sigma_div] with C hC μ c hc
    exact hC _ (hmc C μ) c hc
  · filter_upwards [hmass_upper] with C hC μ
    exact hC _ (hmc C μ)
  · filter_upwards [hlower_high] with C hC μ
    exact hC _ (hmc C μ)
  · filter_upwards [hcard] with C hC μ
    exact hC _ (hmc C μ)
  · filter_upwards [hcap] with C hC μ c hc
    exact hC _ (hmc C μ) c hc
  · filter_upwards [hcapacity_lower] with C hC μ
    exact hC _ (hmc C μ)

/--
Stable-cutoff Theorem 2 closure with the paper's capacity-regularity
condition.  This is the same concrete iid source route as
`theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_source_endpoint_estimates_strict_derived`,
but the source package supplies the model-level regularity predicate
`S_c < alpha / C` for every market-clearing cutoff; Lean derives the weak
per-college inequality used in the small-firm estimate.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_source_endpoint_estimates_capacityRegular_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (small large total :
      ∀ C : ℕ, (Mseq C).Cutoff → Finset (Fin (C + 1)))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (capacity : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              total C P = small C P ∪ large C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c ∈ large C P, lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c ∈ large C P,
                AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoffOut C P c - vHigh) ≤
                  sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (large C P) vLow (cutoffOut C P) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (large C P) vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ((small C P).card : ℝ) ≤
                epsilon * ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              capacityRegular (capacity C P) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (small C P) vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity (small C P) (capacity C P))) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (total C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))
            v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_source_endpoint_estimates_strict_derived
      Mseq Iseq noiseLaw hlong small large total cutoffOut capacity
      htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, htotal, hcutoff_lower, hhigh_le_sigma_div,
      hmass_upper, hlower_high, hcard, hcapRegular,
      hcapacity_lower⟩
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, htotal, hcutoff_lower, hhigh_le_sigma_div,
      hmass_upper, hlower_high, hcard, ?_, hcapacity_lower⟩
  filter_upwards [hcapRegular] with C hC P hP c hc
  exact capacityRegular.le (hC P hP) c

/--
Stable-cutoff Theorem 2 closure with the paper's epsilon-indexed `F_1/F_2`
split and capacity-regularity condition.  This is the stable-matching version
of
`theorem2_uniformAmplification_of_fixed_alpha_iidProduct_cutoff_epsilon_indexed_source_endpoint_estimates_capacityRegular_strict_derived`:
A-L Lemma 1 selects the market-clearing cutoff for each stable matching, and
the endpoint/source estimates are stated uniformly over all market-clearing
cutoffs after epsilon is fixed.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_epsilon_indexed_source_endpoint_estimates_capacityRegular_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (small large :
      ℝ → ∀ C : ℕ, (Mseq C).Cutoff → Finset (Fin (C + 1)))
    (total : ∀ C : ℕ, (Mseq C).Cutoff → Finset (Fin (C + 1)))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (capacity : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              total C P = small epsilon C P ∪ large epsilon C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c ∈ large epsilon C P,
                lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c ∈ large epsilon C P,
                AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoffOut C P c - vHigh) ≤
                  sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (large epsilon C P) vLow (cutoffOut C P) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (large epsilon C P) vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ((small epsilon C P).card : ℝ) ≤
                epsilon * ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              capacityRegular (capacity C P) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (small epsilon C P) vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (small epsilon C P) (capacity C P))) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (total C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))
            v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  have hmc :
      ∀ C : ℕ,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          (Mseq C).MarketClearing
            ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2) := by
    intro C μ
    exact
      (Iseq C).marketClearingCutoffOfStable_marketClearing
        (μ := μ.1) μ.2
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_cutoff_epsilon_indexed_source_endpoint_estimates_capacityRegular_strict_derived
      (Admissible := fun C : ℕ =>
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (noiseLaw := noiseLaw) (hlong := hlong)
      (small := fun epsilon C μ =>
        small epsilon C
          ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))
      (large := fun epsilon C μ =>
        large epsilon C
          ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))
      (total := fun C μ =>
        total C ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))
      (cutoff := fun C μ =>
        cutoffOut C ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))
      (capacity := fun C μ =>
        capacity C ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))
      (totalSupply := totalSupply) (alpha := alpha)
      htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, htotal, hcutoff_lower, hhigh_le_sigma_div,
      hmass_upper, hlower_high, hcard, hcapRegular,
      hcapacity_lower⟩
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [htotal] with C hC μ
    exact hC _ (hmc C μ)
  · filter_upwards [hcutoff_lower] with C hC μ c hc
    exact hC _ (hmc C μ) c hc
  · filter_upwards [hhigh_le_sigma_div] with C hC μ c hc
    exact hC _ (hmc C μ) c hc
  · filter_upwards [hmass_upper] with C hC μ
    exact hC _ (hmc C μ)
  · filter_upwards [hlower_high] with C hC μ
    exact hC _ (hmc C μ)
  · filter_upwards [hcard] with C hC μ
    exact hC _ (hmc C μ)
  · filter_upwards [hcapRegular] with C hC μ
    exact hC _ (hmc C μ)
  · filter_upwards [hcapacity_lower] with C hC μ
    exact hC _ (hmc C μ)

/--
Stable-cutoff Theorem 2 closure with the paper's ordered-index split.  The
conclusion is uniform over stable matchings, while the visible source endpoint
estimates are stated for every market-clearing cutoff after sorting colleges
and taking the prefix/suffix split.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_index_split_source_endpoint_estimates_capacityRegular_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (splitIndex : ℝ → ℕ → ℕ)
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (capacity : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hsplit_card :
      ∀ epsilon, 0 < epsilon →
        ∀ᶠ C : ℕ in atTop,
          (splitIndex epsilon C : ℝ) ≤
            epsilon * ((C + 1 : ℕ) : ℝ))
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c ∈ indexSuffixLarge (splitIndex epsilon C) C,
                lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c ∈ indexSuffixLarge (splitIndex epsilon C) C,
                AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoffOut C P c - vHigh) ≤
                  sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (splitIndex epsilon C) C)
                    vLow (cutoffOut C P) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (splitIndex epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              capacityRegular (capacity C P) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (splitIndex epsilon C) C)
                    vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (indexPrefixSmall (splitIndex epsilon C) C)
                  (capacity C P))) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  have hmc :
      ∀ C : ℕ,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          (Mseq C).MarketClearing
            ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2) := by
    intro C μ
    exact
      (Iseq C).marketClearingCutoffOfStable_marketClearing
        (μ := μ.1) μ.2
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_cutoff_index_split_source_endpoint_estimates_capacityRegular_strict_derived
      (Admissible := fun C : ℕ =>
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (noiseLaw := noiseLaw) (hlong := hlong)
      (splitIndex := splitIndex)
      (cutoff := fun C μ =>
        cutoffOut C ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))
      (capacity := fun C μ =>
        capacity C ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))
      (totalSupply := totalSupply) (alpha := alpha)
      htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg
      hsplit_card ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_lower, hhigh_le_sigma_div, hmass_upper,
      hlower_high, hcapRegular, hcapacity_lower⟩
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hcutoff_lower] with C hC μ c hc
    exact hC _ (hmc C μ) c hc
  · filter_upwards [hhigh_le_sigma_div] with C hC μ c hc
    exact hC _ (hmc C μ) c hc
  · filter_upwards [hmass_upper] with C hC μ
    exact hC _ (hmc C μ)
  · filter_upwards [hlower_high] with C hC μ
    exact hC _ (hmc C μ)
  · filter_upwards [hcapRegular] with C hC μ
    exact hC _ (hmc C μ)
  · filter_upwards [hcapacity_lower] with C hC μ
    exact hC _ (hmc C μ)

/--
Stable-cutoff Theorem 2 closure with the concrete floor-index `F_1/F_2`
split.  This is the strongest current stable-matching route: the finite split
and its cardinality are derived internally, leaving only the ordered endpoint
and capacity estimates as visible source work.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_source_endpoint_estimates_capacityRegular_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (capacity : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
                lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
                AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoffOut C P c - vHigh) ≤
                  sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow (cutoffOut C P) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              capacityRegular (capacity C P) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                  (capacity C P))) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_index_split_source_endpoint_estimates_capacityRegular_strict_derived
      Mseq Iseq noiseLaw hlong epsilonFloorSplitIndex cutoffOut capacity
      htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg ?_ hsource
  intro epsilon hepsilon
  exact Filter.Eventually.of_forall (fun C =>
    epsilonFloorSplitIndex_le epsilon C hepsilon.le)

/--
Stable-cutoff floor-index Theorem 2 route with the small-firm interval
integral exposed.  The source interval and integral estimates are stated for
all market-clearing cutoffs, and Lean specializes them to the A-L selected
cutoff attached to each stable matching.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_source_endpoint_estimates_small_interval_integral_capacityRegular_strict_derived
    {StudentSeq : ℕ → Type u}
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (capacity : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
        ∃ smallInterval : ∀ C : ℕ, (Mseq C).Cutoff → Set ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
                lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
                AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoffOut C P c - vHigh) ≤
                  sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow (cutoffOut C P) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              capacityRegular (capacity C P) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              MeasurableSet (smallInterval C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Integrable
                (fun w : ℝ =>
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                    cutoffAffordanceProbability
                      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                      (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                      w (cutoffOut C P)) η) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon ≤ η.real (smallInterval C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ w : ℝ, w ∈ smallInterval C P → vStar ≤ w) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (∫ w : ℝ,
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                    cutoffAffordanceProbability
                      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                      (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                      w (cutoffOut C P) ∂η) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                  (capacity C P))) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  have hmc :
      ∀ C : ℕ,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          (Mseq C).MarketClearing
            ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2) := by
    intro C μ
    exact
      (Iseq C).marketClearingCutoffOfStable_marketClearing
        (μ := μ.1) μ.2
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_cutoff_floor_index_split_source_endpoint_estimates_small_interval_integral_capacityRegular_strict_derived
      (Admissible := fun C : ℕ =>
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      η noiseLaw hlong
      (cutoff := fun C μ =>
        cutoffOut C ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))
      (capacity := fun C μ =>
        capacity C ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))
      (totalSupply := totalSupply) (alpha := alpha)
      htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, smallInterval,
      hvLow, hvHigh, hvStar, hvStrict, hlower_atTop,
      hcutoff_lower, hhigh_le_sigma_div, hmass_upper, hlower_high,
      hcapRegular, hsmall_meas, hsmall_int, hsmall_mass, hsmall_ge,
      hsmall_integral_capacity⟩
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff,
      (fun C μ =>
        smallInterval C
          ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)),
      hvLow, hvHigh, hvStar, hvStrict, hlower_atTop,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hcutoff_lower] with C hC μ c hc
    exact hC _ (hmc C μ) c hc
  · filter_upwards [hhigh_le_sigma_div] with C hC μ c hc
    exact hC _ (hmc C μ) c hc
  · filter_upwards [hmass_upper] with C hC μ
    exact hC _ (hmc C μ)
  · filter_upwards [hlower_high] with C hC μ
    exact hC _ (hmc C μ)
  · filter_upwards [hcapRegular] with C hC μ
    exact hC _ (hmc C μ)
  · filter_upwards [hsmall_meas] with C hC μ
    exact hC _ (hmc C μ)
  · filter_upwards [hsmall_int] with C hC μ
    exact hC _ (hmc C μ)
  · filter_upwards [hsmall_mass] with C hC μ
    exact hC _ (hmc C μ)
  · filter_upwards [hsmall_ge] with C hC μ w hw
    exact hC _ (hmc C μ) w hw
  · filter_upwards [hsmall_integral_capacity] with C hC μ
    exact hC _ (hmc C μ)

/--
Stable floor-split Theorem 2 route with the high-endpoint tail estimate stated
at the scalar cutoff floor.  Since every large-block college has cutoff above
that floor, antitonicity of the upper tail derives the per-college high-tail
bound used by the product estimate.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_scalar_tail_source_endpoint_estimates_capacityRegular_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (capacity : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
                lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow (cutoffOut C P) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              capacityRegular (capacity C P) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                  (capacity C P))) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_source_endpoint_estimates_capacityRegular_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut capacity
      htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_lower, htail_floor, hmass_upper, hlower_high,
      hcapRegular, hcapacity_lower⟩
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_lower, ?_, hmass_upper, hlower_high,
      hcapRegular, hcapacity_lower⟩
  filter_upwards [hcutoff_lower, htail_floor] with C hcutC htailC P hP c hc
  exact
    le_trans
      (AppliedModelingLib.Probability.upperTailMass_antitone noiseLaw
        (sub_le_sub_right (hcutC P hP c hc) vHigh))
      (htailC P hP)

/--
Stable floor-split Theorem 2 route with the small-firm step stated in the
paper's matched-mass form.  The source proof lower-bounds the mass of students
matched to `F_1`, then uses that this mass is at most the total capacity of
`F_1`; Lean combines those two visible clauses into the active-capacity
comparison needed by the small-firm bound.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_scalar_tail_matched_mass_source_endpoint_estimates_capacityRegular_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (capacity : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (smallMatchedMass : ∀ C : ℕ, (Mseq C).Cutoff → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
                lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow (cutoffOut C P) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              capacityRegular (capacity C P) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar (cutoffOut C P) ≤
                smallMatchedMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              smallMatchedMass C P ≤
                AppliedModelingLib.Matching.activeCapacity
                  (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                  (capacity C P))) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_scalar_tail_source_endpoint_estimates_capacityRegular_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut capacity
      htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_lower, htail_floor, hmass_upper, hlower_high,
      hcapRegular, hmatched_lower, hmatched_capacity⟩
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_lower, htail_floor, hmass_upper, hlower_high,
      hcapRegular, ?_⟩
  filter_upwards [hmatched_lower, hmatched_capacity] with
    C hlowerC hcapC P hP
  exact le_trans (hlowerC P hP) (hcapC P hP)

/--
Stable floor-split Theorem 2 route with the low-endpoint large-firm estimate
exposed through the paper's interval-mass comparison.  The source proof first
lower-bounds an interval integral by `(1-epsilon) * p(vLow,F_2)` and then
bounds that integral by total capacity; Lean combines those clauses into the
large-firm low-endpoint upper bound.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_scalar_tail_interval_mass_matched_mass_source_endpoint_estimates_capacityRegular_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (capacity : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (largeIntervalMass smallMatchedMass :
      ∀ C : ℕ, (Mseq C).Cutoff → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
                lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow (cutoffOut C P) ≤
                largeIntervalMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeIntervalMass C P ≤ totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              capacityRegular (capacity C P) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar (cutoffOut C P) ≤
                smallMatchedMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              smallMatchedMass C P ≤
                AppliedModelingLib.Matching.activeCapacity
                  (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                  (capacity C P))) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_scalar_tail_matched_mass_source_endpoint_estimates_capacityRegular_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut capacity smallMatchedMass
      htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_lower, htail_floor, hlarge_interval_lower,
      hlarge_interval_capacity, hlower_high, hcapRegular, hmatched_lower,
      hmatched_capacity⟩
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_lower, htail_floor, ?_, hlower_high,
      hcapRegular, hmatched_lower, hmatched_capacity⟩
  filter_upwards [hlarge_interval_lower, hlarge_interval_capacity] with
    C hlowerC hcapC P hP
  exact le_trans (hlowerC P hP) (hcapC P hP)

/--
Stable floor-split Theorem 2 route with the high-endpoint large-firm lower
bound exposed as two source clauses.  The paper obtains this lower endpoint
from total matched mass after losing the small-block capacity and the
outside-interval mass; Lean combines those visible clauses into the direct
`S - alpha*epsilon - epsilon` lower bound.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_scalar_tail_interval_mass_large_matched_mass_source_endpoint_estimates_capacityRegular_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (capacity : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (largeIntervalMass largeMatchedMass smallMatchedMass :
      ∀ C : ℕ, (Mseq C).Cutoff → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
                lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow (cutoffOut C P) ≤
                largeIntervalMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeIntervalMass C P ≤ totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              totalSupply - alpha * epsilon ≤ largeMatchedMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeMatchedMass C P - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              capacityRegular (capacity C P) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar (cutoffOut C P) ≤
                smallMatchedMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              smallMatchedMass C P ≤
                AppliedModelingLib.Matching.activeCapacity
                  (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                  (capacity C P))) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_scalar_tail_interval_mass_matched_mass_source_endpoint_estimates_capacityRegular_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut capacity largeIntervalMass
      smallMatchedMass htotalSupply_nonneg htotalSupply_lt_one
      halpha_nonneg ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_lower, htail_floor, hlarge_interval_lower,
      hlarge_interval_capacity, hlarge_mass_lower, hlarge_endpoint,
      hcapRegular, hmatched_lower, hmatched_capacity⟩
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_lower, htail_floor, hlarge_interval_lower,
      hlarge_interval_capacity, ?_, hcapRegular, hmatched_lower,
      hmatched_capacity⟩
  filter_upwards [hlarge_mass_lower, hlarge_endpoint] with
    C hmassC hendC P hP
  linarith [hmassC P hP, hendC P hP]

/--
Stable floor-split Theorem 2 route with the large-block cutoff-floor condition
stated as a numeric sorted-index suffix condition.  Lean unfolds membership in
`F_2` and turns `splitIndex <= c` into the finite-set cutoff-floor premise used
by the long-tail product estimate.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_source_endpoint_estimates_capacityRegular_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (capacity : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (largeIntervalMass largeMatchedMass smallMatchedMass :
      ∀ C : ℕ, (Mseq C).Cutoff → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c : Fin (C + 1),
                epsilonFloorSplitIndex epsilon C ≤ (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow (cutoffOut C P) ≤
                largeIntervalMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeIntervalMass C P ≤ totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              totalSupply - alpha * epsilon ≤ largeMatchedMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeMatchedMass C P - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              capacityRegular (capacity C P) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar (cutoffOut C P) ≤
                smallMatchedMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              smallMatchedMass C P ≤
                AppliedModelingLib.Matching.activeCapacity
                  (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                  (capacity C P))) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_scalar_tail_interval_mass_large_matched_mass_source_endpoint_estimates_capacityRegular_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut capacity largeIntervalMass
      largeMatchedMass smallMatchedMass htotalSupply_nonneg
      htotalSupply_lt_one halpha_nonneg ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_index, htail_floor, hlarge_interval_lower,
      hlarge_interval_capacity, hlarge_mass_lower, hlarge_endpoint,
      hcapRegular, hmatched_lower, hmatched_capacity⟩
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, ?_, htail_floor, hlarge_interval_lower,
      hlarge_interval_capacity, hlarge_mass_lower, hlarge_endpoint,
      hcapRegular, hmatched_lower, hmatched_capacity⟩
  filter_upwards [hcutoff_index] with C hC P hP c hc
  exact hC P hP c (Finset.mem_filter.mp hc).2

/--
Stable floor-split Theorem 2 route with the large-block high-endpoint estimate
derived from concrete active-capacity accounting.  The remaining high-side
source clause is the paper-facing statement that the large block's active
capacity, up to the `epsilon` outside-interval loss, is admitted at `vHigh`.
Lean derives that the large block has capacity at least `totalSupply -
alpha*epsilon` from total active capacity, capacity regularity, and the
finite `F_1/F_2` split.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_active_capacity_source_endpoint_estimates_capacityRegular_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (capacity : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c : Fin (C + 1),
                epsilonFloorSplitIndex epsilon C ≤ (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow (cutoffOut C P) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              totalSupply ≤
                AppliedModelingLib.Matching.activeCapacity
                  (Finset.univ : Finset (Fin (C + 1))) (capacity C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Matching.activeCapacity
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  (capacity C P) - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              capacityRegular (capacity C P) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                  (capacity C P))) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_scalar_tail_source_endpoint_estimates_capacityRegular_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut capacity
      htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_index, htail_floor, hmass_upper,
      htotal_capacity, hlarge_endpoint, hcapRegular, hsmall_capacity_lower⟩
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, ?_, htail_floor, hmass_upper, ?_, hcapRegular,
      hsmall_capacity_lower⟩
  · filter_upwards [hcutoff_index] with C hC P hP c hc
    exact hC P hP c (Finset.mem_filter.mp hc).2
  · filter_upwards [htotal_capacity, hlarge_endpoint, hcapRegular] with
      C htotalC hlargeC hcapC P hP
    have hcard :
        (((indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C).card) : ℝ) ≤
          epsilon * ((C + 1 : ℕ) : ℝ) := by
      exact le_trans
        (indexPrefixSmall_card_le_index (epsilonFloorSplitIndex epsilon C) C)
        (epsilonFloorSplitIndex_le epsilon C (le_of_lt hepsilon))
    have hC_pos : 0 < (((C + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_pos C
    have hcap_le :
        ∀ c ∈ indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C,
          capacity C P c ≤ alpha / ((C + 1 : ℕ) : ℝ) := by
      intro c hc
      exact capacityRegular.le (hcapC P hP) c
    have hsmall_cap :
        AppliedModelingLib.Matching.activeCapacity
            (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
            (capacity C P) ≤
          epsilon * alpha :=
      smallActiveSet_capacity_le_epsilon_mul_alpha
        (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
        (capacity C P) hcard halpha_nonneg hC_pos hcap_le
    have hlarge_cap :
        totalSupply - epsilon * alpha ≤
          AppliedModelingLib.Matching.activeCapacity
            (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
            (capacity C P) :=
      AppliedModelingLib.Matching.activeCapacity_right_ge_totalLower_sub_leftUpper_of_partition
        (total := (Finset.univ : Finset (Fin (C + 1))))
        (left := indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
        (right := indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
        (capacity C P)
        (indexPrefixSmall_union_indexSuffixLarge
          (epsilonFloorSplitIndex epsilon C) C)
        (indexPrefixSmall_disjoint_indexSuffixLarge
          (epsilonFloorSplitIndex epsilon C) C)
        (htotalC P hP) hsmall_cap
    have hlarge_cap' :
        totalSupply - alpha * epsilon ≤
          AppliedModelingLib.Matching.activeCapacity
            (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
            (capacity C P) := by
      simpa [mul_comm] using hlarge_cap
    linarith [hlarge_cap', hlargeC P hP]

/--
Stable floor-split Theorem 2 route using the capacity field of the cutoff
market itself.  This is the source-facing specialization of the
active-capacity wrapper above: capacity accounting is no longer supplied as a
separate function, so the remaining capacity assumptions are about the
paper's market primitives.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_source_endpoint_estimates_capacityRegular_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c : Fin (C + 1),
                epsilonFloorSplitIndex epsilon C ≤ (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow (cutoffOut C P) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              totalSupply ≤
                AppliedModelingLib.Matching.activeCapacity
                  (Finset.univ : Finset (Fin (C + 1)))
                  (Mseq C).capacity) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Matching.activeCapacity
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  (Mseq C).capacity - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              capacityRegular (Mseq C).capacity alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                  (Mseq C).capacity)) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_active_capacity_source_endpoint_estimates_capacityRegular_strict_derived
    Mseq Iseq noiseLaw hlong cutoffOut
    (fun C _P => (Mseq C).capacity)
    htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg hsource

/--
Market-capacity Theorem 2 route with capacity premises stated at the market
level.  Since capacities are primitive fields of the market and do not depend
on a cutoff, Lean specializes the global total-capacity and capacity-regularity
facts to each market-clearing cutoff internally.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_global_capacity_source_endpoint_estimates_capacityRegular_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c : Fin (C + 1),
                epsilonFloorSplitIndex epsilon C ≤ (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow (cutoffOut C P) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
              totalSupply ≤
                AppliedModelingLib.Matching.activeCapacity
                  (Finset.univ : Finset (Fin (C + 1)))
                  (Mseq C).capacity) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Matching.activeCapacity
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  (Mseq C).capacity - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
              capacityRegular (Mseq C).capacity alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                  (Mseq C).capacity)) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_source_endpoint_estimates_capacityRegular_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut htotalSupply_nonneg
      htotalSupply_lt_one halpha_nonneg ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_index, htail_floor, hmass_upper,
      htotal_capacity, hlarge_endpoint, hcapRegular,
      hsmall_capacity_lower⟩
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_index, htail_floor, hmass_upper, ?_,
      hlarge_endpoint, ?_, hsmall_capacity_lower⟩
  · filter_upwards [htotal_capacity] with C hC P hP
    exact hC
  · filter_upwards [hcapRegular] with C hC P hP
    exact hC

/--
Market-capacity Theorem 2 route with value-independent capacity facts pulled
out of the endpoint package.  The remaining source package now contains only
the cutoff, tail, and endpoint probability/capacity comparisons that depend
on the chosen value window.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_global_capacity_separate_capacity_source_endpoint_estimates_capacityRegular_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (htotal_capacity :
      ∀ᶠ C : ℕ in atTop,
        totalSupply ≤
          AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity)
    (hcapacity_regular :
      ∀ᶠ C : ℕ in atTop,
        capacityRegular (Mseq C).capacity alpha (C + 1))
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c : Fin (C + 1),
                epsilonFloorSplitIndex epsilon C ≤ (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow (cutoffOut C P) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Matching.activeCapacity
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  (Mseq C).capacity - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                  (Mseq C).capacity)) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_global_capacity_source_endpoint_estimates_capacityRegular_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut htotalSupply_nonneg
      htotalSupply_lt_one halpha_nonneg ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_index, htail_floor, hmass_upper,
      hlarge_endpoint, hsmall_capacity_lower⟩
  exact
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_index, htail_floor, hmass_upper,
      htotal_capacity, hlarge_endpoint, hcapacity_regular,
      hsmall_capacity_lower⟩

/--
Market-capacity Theorem 2 route with the paper's capacity primitives exposed
directly: total college capacity equals the fixed supply `S`, and every
college has capacity below `alpha / C`.  Lean derives the weaker capacity
lower bound and the `capacityRegular` predicate used by the current endpoint
route internally.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_capacity_source_endpoint_estimates_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hcapacity_total :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity =
          totalSupply)
    (hcapacity_bound :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1),
          (Mseq C).capacity c < alpha / ((C + 1 : ℕ) : ℝ))
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c : Fin (C + 1),
                epsilonFloorSplitIndex epsilon C ≤ (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow (cutoffOut C P) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Matching.activeCapacity
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  (Mseq C).capacity - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                  (Mseq C).capacity)) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  have htotal_capacity :
      ∀ᶠ C : ℕ in atTop,
        totalSupply ≤
          AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity := by
    filter_upwards [hcapacity_total] with C hC
    rw [hC]
  have hcapacity_regular :
      ∀ᶠ C : ℕ in atTop,
        capacityRegular (Mseq C).capacity alpha (C + 1) := by
    filter_upwards [hcapacity_bound] with C hC c
    exact hC c
  exact
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_global_capacity_separate_capacity_source_endpoint_estimates_capacityRegular_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut htotalSupply_nonneg
      htotalSupply_lt_one halpha_nonneg htotal_capacity hcapacity_regular
      hsource

/--
Market-capacity Theorem 2 route with the paper's positive capacity primitive.
The source model states each college capacity as positive and below
`alpha / (C+1)`; Lean derives nonnegativity of total supply, nonnegativity of
`alpha`, and the strict capacity-regularity bound before applying the direct
active-capacity endpoint route.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_source_endpoint_estimates_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_total :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity =
          totalSupply)
    (hcapacity_open_bound :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1),
          0 < (Mseq C).capacity c ∧
            (Mseq C).capacity c < alpha / ((C + 1 : ℕ) : ℝ))
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c : Fin (C + 1),
                epsilonFloorSplitIndex epsilon C ≤ (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow (cutoffOut C P) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Matching.activeCapacity
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  (Mseq C).capacity - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                  (Mseq C).capacity)) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  have hcapacity_bound :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1),
          (Mseq C).capacity c < alpha / ((C + 1 : ℕ) : ℝ) := by
    filter_upwards [hcapacity_open_bound] with C hboundC c
    exact (hboundC c).2
  have htotalSupply_nonneg : 0 ≤ totalSupply := by
    rcases (hcapacity_total.and hcapacity_open_bound).exists with
      ⟨C, htotalC, hboundC⟩
    have hactive_nonneg :
        0 ≤ AppliedModelingLib.Matching.activeCapacity
          (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity := by
      unfold AppliedModelingLib.Matching.activeCapacity
      exact Finset.sum_nonneg (fun c _hc => le_of_lt (hboundC c).1)
    simpa [htotalC] using hactive_nonneg
  have halpha_nonneg : 0 ≤ alpha := by
    rcases hcapacity_open_bound.exists with ⟨C, hboundC⟩
    let c0 : Fin (C + 1) := ⟨0, Nat.succ_pos C⟩
    have hdiv_pos :
        0 < alpha / (((C + 1 : ℕ) : ℝ)) :=
      lt_trans (hboundC c0).1 (hboundC c0).2
    have hden_pos : 0 < (((C + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_pos C
    have hmul_pos :
        0 < (alpha / (((C + 1 : ℕ) : ℝ))) *
          (((C + 1 : ℕ) : ℝ)) :=
      mul_pos hdiv_pos hden_pos
    have hmul_eq :
        (alpha / (((C + 1 : ℕ) : ℝ))) *
            (((C + 1 : ℕ) : ℝ)) = alpha := by
      field_simp [ne_of_gt hden_pos]
    have halpha_pos : 0 < alpha := by
      rw [← hmul_eq]
      exact hmul_pos
    exact le_of_lt halpha_pos
  exact
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_capacity_source_endpoint_estimates_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut htotalSupply_nonneg
      htotalSupply_lt_one halpha_nonneg hcapacity_total hcapacity_bound
      hsource

/--
Theorem 2 route with the paper's interval-mass decomposition but without
auxiliary matched-mass objects.  The source proof may state the low-endpoint
large-firm step through interval mass and the high/small endpoint steps
through active capacities directly; Lean derives the total-supply upper bound
for the large interval from total capacity and positive college capacities.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_bound_interval_active_capacity_source_endpoint_estimates_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (largeIntervalMass : ∀ C : ℕ, (Mseq C).Cutoff → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_total :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity =
          totalSupply)
    (hcapacity_open_bound :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1),
          0 < (Mseq C).capacity c ∧
            (Mseq C).capacity c < alpha / ((C + 1 : ℕ) : ℝ))
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c : Fin (C + 1),
                epsilonFloorSplitIndex epsilon C ≤ (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow (cutoffOut C P) ≤
                largeIntervalMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeIntervalMass C P ≤
                AppliedModelingLib.Matching.activeCapacity
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  (Mseq C).capacity) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Matching.activeCapacity
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  (Mseq C).capacity - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                  (Mseq C).capacity)) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  have hcapacity_nonneg :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1), 0 ≤ (Mseq C).capacity c := by
    filter_upwards [hcapacity_open_bound] with C hboundC c
    exact le_of_lt (hboundC c).1
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_source_endpoint_estimates_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut htotalSupply_lt_one
      hcapacity_total hcapacity_open_bound ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_index, htail_floor, hlarge_interval_lower,
      hlarge_interval_active_capacity, hlarge_active_endpoint,
      hsmall_capacity_lower⟩
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_index, htail_floor, ?_,
      hlarge_active_endpoint, hsmall_capacity_lower⟩
  filter_upwards
    [hlarge_interval_lower, hlarge_interval_active_capacity,
      hcapacity_total, hcapacity_nonneg] with
    C hlowerC hactiveC htotalC hnonnegC P hP
  calc
    (1 - epsilon) *
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
          vLow (cutoffOut C P) ≤
        largeIntervalMass C P := hlowerC P hP
    _ ≤ AppliedModelingLib.Matching.activeCapacity
        (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
        (Mseq C).capacity := hactiveC P hP
    _ ≤ AppliedModelingLib.Matching.activeCapacity
        (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity := by
          exact
            AppliedModelingLib.Matching.activeCapacity_mono_of_nonneg
              (by intro c hc; simp)
              (by intro c hc; exact hnonnegC c)
    _ = totalSupply := htotalC

/--
Clean floor-split Theorem 2 route with the paper's positive capacity
primitive.  The total-capacity equality and per-college open capacity bound
derive the sign and capacity-regularity side conditions; the visible source
package is then only the ordered cutoff/tail and endpoint estimates.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_market_capacity_paper_positive_capacity_source_endpoint_estimates_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_total :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity =
          totalSupply)
    (hcapacity_open_bound :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1),
          0 < (Mseq C).capacity c ∧
            (Mseq C).capacity c < alpha / ((C + 1 : ℕ) : ℝ))
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
                lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
                AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoffOut C P c - vHigh) ≤
                  sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow (cutoffOut C P) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                  (Mseq C).capacity)) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  have hcapacity_bound :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1),
          (Mseq C).capacity c < alpha / ((C + 1 : ℕ) : ℝ) := by
    filter_upwards [hcapacity_open_bound] with C hboundC c
    exact (hboundC c).2
  have htotalSupply_nonneg : 0 ≤ totalSupply := by
    rcases (hcapacity_total.and hcapacity_open_bound).exists with
      ⟨C, htotalC, hboundC⟩
    have hactive_nonneg :
        0 ≤ AppliedModelingLib.Matching.activeCapacity
          (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity := by
      unfold AppliedModelingLib.Matching.activeCapacity
      exact Finset.sum_nonneg (fun c _hc => le_of_lt (hboundC c).1)
    simpa [htotalC] using hactive_nonneg
  have halpha_nonneg : 0 ≤ alpha := by
    rcases hcapacity_open_bound.exists with ⟨C, hboundC⟩
    let c0 : Fin (C + 1) := ⟨0, Nat.succ_pos C⟩
    have hdiv_pos :
        0 < alpha / (((C + 1 : ℕ) : ℝ)) :=
      lt_trans (hboundC c0).1 (hboundC c0).2
    have hden_pos : 0 < (((C + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_pos C
    have hmul_pos :
        0 < (alpha / (((C + 1 : ℕ) : ℝ))) *
          (((C + 1 : ℕ) : ℝ)) :=
      mul_pos hdiv_pos hden_pos
    have hmul_eq :
        (alpha / (((C + 1 : ℕ) : ℝ))) *
            (((C + 1 : ℕ) : ℝ)) = alpha := by
      field_simp [ne_of_gt hden_pos]
    have halpha_pos : 0 < alpha := by
      rw [← hmul_eq]
      exact hmul_pos
    exact le_of_lt halpha_pos
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_source_endpoint_estimates_capacityRegular_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut
      (fun C _P => (Mseq C).capacity)
      htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_lower, hhigh_tail, hmass_upper, hlower_high,
      hsmall_capacity_lower⟩
  have hcapacity_regular :
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          capacityRegular (Mseq C).capacity alpha (C + 1) := by
    filter_upwards [hcapacity_bound] with C hboundC P hP c
    exact hboundC c
  exact
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_lower, hhigh_tail, hmass_upper, hlower_high,
      hcapacity_regular, hsmall_capacity_lower⟩

/--
Market-capacity Theorem 2 route with the paper's direct capacity primitives
and the low-endpoint/small-firm mass comparisons exposed in the form used by
the source proof.  Lean converts the large interval mass and small matched
mass clauses into the endpoint inequalities required by the active-capacity
route.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_capacity_interval_mass_matched_mass_source_endpoint_estimates_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (largeIntervalMass smallMatchedMass :
      ∀ C : ℕ, (Mseq C).Cutoff → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hcapacity_total :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity =
          totalSupply)
    (hcapacity_bound :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1),
          (Mseq C).capacity c < alpha / ((C + 1 : ℕ) : ℝ))
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c : Fin (C + 1),
                epsilonFloorSplitIndex epsilon C ≤ (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow (cutoffOut C P) ≤
                largeIntervalMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeIntervalMass C P ≤ totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Matching.activeCapacity
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  (Mseq C).capacity - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar (cutoffOut C P) ≤
                smallMatchedMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              smallMatchedMass C P ≤
                AppliedModelingLib.Matching.activeCapacity
                  (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                  (Mseq C).capacity)) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_capacity_source_endpoint_estimates_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut htotalSupply_nonneg
      htotalSupply_lt_one halpha_nonneg hcapacity_total hcapacity_bound ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_index, htail_floor, hlarge_interval_lower,
      hlarge_interval_capacity, hlarge_endpoint, hmatched_lower,
      hmatched_capacity⟩
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_index, htail_floor, ?_, hlarge_endpoint, ?_⟩
  · filter_upwards [hlarge_interval_lower, hlarge_interval_capacity] with
      C hlowerC hcapC P hP
    exact le_trans (hlowerC P hP) (hcapC P hP)
  · filter_upwards [hmatched_lower, hmatched_capacity] with
      C hlowerC hcapC P hP
    exact le_trans (hlowerC P hP) (hcapC P hP)

/--
Market-capacity Theorem 2 route with the paper's per-college capacity bound
and the large-firm high endpoint exposed through matched mass.  The paper's
capacity bound derives the `capacityRegular` predicate internally; the
remaining value-window package follows the proof's interval-mass,
large-matched-mass, and small-matched-mass comparisons.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_capacity_bound_interval_mass_large_matched_mass_source_endpoint_estimates_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (largeIntervalMass largeMatchedMass smallMatchedMass :
      ∀ C : ℕ, (Mseq C).Cutoff → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hcapacity_bound :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1),
          (Mseq C).capacity c < alpha / ((C + 1 : ℕ) : ℝ))
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c : Fin (C + 1),
                epsilonFloorSplitIndex epsilon C ≤ (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow (cutoffOut C P) ≤
                largeIntervalMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeIntervalMass C P ≤ totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              totalSupply - alpha * epsilon ≤ largeMatchedMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeMatchedMass C P - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar (cutoffOut C P) ≤
                smallMatchedMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              smallMatchedMass C P ≤
                AppliedModelingLib.Matching.activeCapacity
                  (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                  (Mseq C).capacity)) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  have hcapacity_regular :
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          capacityRegular (Mseq C).capacity alpha (C + 1) := by
    filter_upwards [hcapacity_bound] with C hC P hP c
    exact hC c
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_source_endpoint_estimates_capacityRegular_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut
      (fun C _P => (Mseq C).capacity)
      largeIntervalMass largeMatchedMass smallMatchedMass
      htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_index, htail_floor, hlarge_interval_lower,
      hlarge_interval_capacity, hlarge_mass_lower, hlarge_endpoint,
      hmatched_lower, hmatched_capacity⟩
  exact
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_index, htail_floor, hlarge_interval_lower,
      hlarge_interval_capacity, hlarge_mass_lower, hlarge_endpoint,
      hcapacity_regular, hmatched_lower, hmatched_capacity⟩

/--
Market-capacity Theorem 2 route with the large-interval capacity upper bound
derived from primitive capacity data.  Instead of taking
`largeIntervalMass <= S` directly, this row assumes the paper-level total
capacity equality, nonnegative college capacities, and a comparison of the
large interval mass with the active capacity of the large suffix.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_capacity_bound_interval_active_capacity_large_matched_mass_source_endpoint_estimates_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (largeIntervalMass largeMatchedMass smallMatchedMass :
      ∀ C : ℕ, (Mseq C).Cutoff → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hcapacity_total :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity =
          totalSupply)
    (hcapacity_nonneg :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1), 0 ≤ (Mseq C).capacity c)
    (hcapacity_bound :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1),
          (Mseq C).capacity c < alpha / ((C + 1 : ℕ) : ℝ))
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c : Fin (C + 1),
                epsilonFloorSplitIndex epsilon C ≤ (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow (cutoffOut C P) ≤
                largeIntervalMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeIntervalMass C P ≤
                AppliedModelingLib.Matching.activeCapacity
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  (Mseq C).capacity) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              totalSupply - alpha * epsilon ≤ largeMatchedMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeMatchedMass C P - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar (cutoffOut C P) ≤
                smallMatchedMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              smallMatchedMass C P ≤
                AppliedModelingLib.Matching.activeCapacity
                  (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                  (Mseq C).capacity)) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_capacity_bound_interval_mass_large_matched_mass_source_endpoint_estimates_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut largeIntervalMass
      largeMatchedMass smallMatchedMass htotalSupply_nonneg
      htotalSupply_lt_one halpha_nonneg hcapacity_bound ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_index, htail_floor, hlarge_interval_lower,
      hlarge_interval_active_capacity, hlarge_mass_lower, hlarge_endpoint,
      hmatched_lower, hmatched_capacity⟩
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_index, htail_floor, hlarge_interval_lower,
      ?_, hlarge_mass_lower, hlarge_endpoint, hmatched_lower,
      hmatched_capacity⟩
  filter_upwards
    [hlarge_interval_active_capacity, hcapacity_total, hcapacity_nonneg] with
    C hlargeC htotalC hnonnegC P hP
  calc
    largeIntervalMass C P ≤
        AppliedModelingLib.Matching.activeCapacity
          (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
          (Mseq C).capacity := hlargeC P hP
    _ ≤ AppliedModelingLib.Matching.activeCapacity
        (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity := by
          exact
            AppliedModelingLib.Matching.activeCapacity_mono_of_nonneg
              (by intro c hc; simp)
              (by intro c hc; exact hnonnegC c)
    _ = totalSupply := htotalC

/--
Market-capacity Theorem 2 route with both large-block capacity comparisons
stated at the source level.  The previous wrapper still required the broad
matched-mass lower bound `S - alpha*epsilon <= largeMatchedMass`.  Here Lean
derives that lower bound from the paper's total capacity, per-college capacity
bound, and the source fact that the large block's active capacity is matched.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_capacity_bound_interval_active_capacity_matched_large_matched_mass_source_endpoint_estimates_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (largeIntervalMass largeMatchedMass smallMatchedMass :
      ∀ C : ℕ, (Mseq C).Cutoff → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (hcapacity_total :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity =
          totalSupply)
    (hcapacity_nonneg :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1), 0 ≤ (Mseq C).capacity c)
    (hcapacity_bound :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1),
          (Mseq C).capacity c < alpha / ((C + 1 : ℕ) : ℝ))
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c : Fin (C + 1),
                epsilonFloorSplitIndex epsilon C ≤ (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow (cutoffOut C P) ≤
                largeIntervalMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeIntervalMass C P ≤
                AppliedModelingLib.Matching.activeCapacity
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  (Mseq C).capacity) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Matching.activeCapacity
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  (Mseq C).capacity ≤
                largeMatchedMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeMatchedMass C P - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar (cutoffOut C P) ≤
                smallMatchedMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              smallMatchedMass C P ≤
                AppliedModelingLib.Matching.activeCapacity
                  (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                  (Mseq C).capacity)) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  have htotalSupply_nonneg : 0 ≤ totalSupply := by
    rcases (hcapacity_total.and hcapacity_nonneg).exists with
      ⟨C, htotalC, hnonnegC⟩
    have hactive_nonneg :
        0 ≤ AppliedModelingLib.Matching.activeCapacity
          (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity := by
      unfold AppliedModelingLib.Matching.activeCapacity
      exact Finset.sum_nonneg (fun c _hc => hnonnegC c)
    simpa [htotalC] using hactive_nonneg
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_capacity_bound_interval_active_capacity_large_matched_mass_source_endpoint_estimates_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut largeIntervalMass
      largeMatchedMass smallMatchedMass htotalSupply_nonneg htotalSupply_lt_one
      halpha_nonneg hcapacity_total hcapacity_nonneg hcapacity_bound ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_index, htail_floor, hlarge_interval_lower,
      hlarge_interval_active_capacity, hlarge_active_capacity_matched,
      hlarge_endpoint, hmatched_lower, hmatched_capacity⟩
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_index, htail_floor, hlarge_interval_lower,
      hlarge_interval_active_capacity, ?_, hlarge_endpoint, hmatched_lower,
      hmatched_capacity⟩
  filter_upwards
    [hcapacity_total, hcapacity_bound, hlarge_active_capacity_matched] with
    C htotalC hboundC hmatchedC P hP
  have hcard :
      (((indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C).card) : ℝ) ≤
        epsilon * ((C + 1 : ℕ) : ℝ) := by
    exact le_trans
      (indexPrefixSmall_card_le_index (epsilonFloorSplitIndex epsilon C) C)
      (epsilonFloorSplitIndex_le epsilon C (le_of_lt hepsilon))
  have hC_pos : 0 < (((C + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos C
  have hcap_le :
      ∀ c ∈ indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C,
        (Mseq C).capacity c ≤ alpha / ((C + 1 : ℕ) : ℝ) := by
    intro c _hc
    exact le_of_lt (hboundC c)
  have hsmall_cap :
      AppliedModelingLib.Matching.activeCapacity
          (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
          (Mseq C).capacity ≤
        epsilon * alpha :=
    smallActiveSet_capacity_le_epsilon_mul_alpha
      (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
      (Mseq C).capacity hcard halpha_nonneg hC_pos hcap_le
  have htotal_lower :
      totalSupply ≤
        AppliedModelingLib.Matching.activeCapacity
          (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity := by
    rw [htotalC]
  have hlarge_cap :
      totalSupply - epsilon * alpha ≤
        AppliedModelingLib.Matching.activeCapacity
          (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
          (Mseq C).capacity :=
    AppliedModelingLib.Matching.activeCapacity_right_ge_totalLower_sub_leftUpper_of_partition
      (total := (Finset.univ : Finset (Fin (C + 1))))
      (left := indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
      (right := indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
      (Mseq C).capacity
      (indexPrefixSmall_union_indexSuffixLarge
        (epsilonFloorSplitIndex epsilon C) C)
      (indexPrefixSmall_disjoint_indexSuffixLarge
        (epsilonFloorSplitIndex epsilon C) C)
      htotal_lower hsmall_cap
  have hlarge_cap' :
      totalSupply - alpha * epsilon ≤
        AppliedModelingLib.Matching.activeCapacity
          (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
          (Mseq C).capacity := by
    simpa [mul_comm] using hlarge_cap
  exact le_trans hlarge_cap' (hmatchedC P hP)

/--
Theorem 2 route with the paper's positive-capacity primitive.  The model
states capacities as positive and bounded by `alpha / (C+1)`; Lean derives
the nonnegativity of capacities and of `alpha` before applying the current
active-capacity/matched-mass endpoint route.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_bound_interval_active_capacity_matched_large_matched_mass_source_endpoint_estimates_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (largeIntervalMass largeMatchedMass smallMatchedMass :
      ∀ C : ℕ, (Mseq C).Cutoff → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_total :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity =
          totalSupply)
    (hcapacity_open_bound :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1),
          0 < (Mseq C).capacity c ∧
            (Mseq C).capacity c < alpha / ((C + 1 : ℕ) : ℝ))
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c : Fin (C + 1),
                epsilonFloorSplitIndex epsilon C ≤ (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow (cutoffOut C P) ≤
                largeIntervalMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeIntervalMass C P ≤
                AppliedModelingLib.Matching.activeCapacity
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  (Mseq C).capacity) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Matching.activeCapacity
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  (Mseq C).capacity ≤
                largeMatchedMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeMatchedMass C P - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar (cutoffOut C P) ≤
                smallMatchedMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              smallMatchedMass C P ≤
                AppliedModelingLib.Matching.activeCapacity
                  (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                  (Mseq C).capacity)) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  have hcapacity_nonneg :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1), 0 ≤ (Mseq C).capacity c := by
    filter_upwards [hcapacity_open_bound] with C hboundC c
    exact le_of_lt (hboundC c).1
  have hcapacity_bound :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1),
          (Mseq C).capacity c < alpha / ((C + 1 : ℕ) : ℝ) := by
    filter_upwards [hcapacity_open_bound] with C hboundC c
    exact (hboundC c).2
  have halpha_nonneg : 0 ≤ alpha := by
    rcases hcapacity_open_bound.exists with ⟨C, hboundC⟩
    let c0 : Fin (C + 1) := ⟨0, Nat.succ_pos C⟩
    have hdiv_pos :
        0 < alpha / (((C + 1 : ℕ) : ℝ)) :=
      lt_trans (hboundC c0).1 (hboundC c0).2
    have hden_pos : 0 < (((C + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_pos C
    have hmul_pos :
        0 < (alpha / (((C + 1 : ℕ) : ℝ))) *
          (((C + 1 : ℕ) : ℝ)) :=
      mul_pos hdiv_pos hden_pos
    have hmul_eq :
        (alpha / (((C + 1 : ℕ) : ℝ))) *
            (((C + 1 : ℕ) : ℝ)) = alpha := by
      field_simp [ne_of_gt hden_pos]
    have halpha_pos : 0 < alpha := by
      rw [← hmul_eq]
      exact hmul_pos
    exact le_of_lt halpha_pos
  exact
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_capacity_bound_interval_active_capacity_matched_large_matched_mass_source_endpoint_estimates_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut largeIntervalMass
      largeMatchedMass smallMatchedMass htotalSupply_lt_one halpha_nonneg
      hcapacity_total hcapacity_nonneg hcapacity_bound hsource

/--
Theorem 2 route using a semantic mass-clearing interface.  The endpoint
estimates mention the paper's interval/matched-mass quantities, while the
interface supplies the market-clearing capacity-fill inequalities that connect
those quantities to active capacities.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_massClearing_endpoint_estimates_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (mass : Theorem2MassClearingInterface Mseq)
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_total :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity =
          totalSupply)
    (hcapacity_open_bound :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1),
          0 < (Mseq C).capacity c ∧
            (Mseq C).capacity c < alpha / ((C + 1 : ℕ) : ℝ))
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c : Fin (C + 1),
                epsilonFloorSplitIndex epsilon C ≤ (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow (cutoffOut C P) ≤
                mass.largeIntervalMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              mass.largeMatchedMass C P - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar (cutoffOut C P) ≤
                mass.smallMatchedMass C P)) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  have hcapacity_nonneg :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1), 0 ≤ (Mseq C).capacity c := by
    filter_upwards [hcapacity_open_bound] with C hboundC c
    exact le_of_lt (hboundC c).1
  have hcapacity_bound :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1),
          (Mseq C).capacity c < alpha / ((C + 1 : ℕ) : ℝ) := by
    filter_upwards [hcapacity_open_bound] with C hboundC c
    exact (hboundC c).2
  have halpha_nonneg : 0 ≤ alpha := by
    rcases hcapacity_open_bound.exists with ⟨C, hboundC⟩
    let c0 : Fin (C + 1) := ⟨0, Nat.succ_pos C⟩
    have hdiv_pos :
        0 < alpha / (((C + 1 : ℕ) : ℝ)) :=
      lt_trans (hboundC c0).1 (hboundC c0).2
    have hden_pos : 0 < (((C + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_pos C
    have hmul_pos :
        0 < (alpha / (((C + 1 : ℕ) : ℝ))) *
          (((C + 1 : ℕ) : ℝ)) :=
      mul_pos hdiv_pos hden_pos
    have hmul_eq :
        (alpha / (((C + 1 : ℕ) : ℝ))) *
            (((C + 1 : ℕ) : ℝ)) = alpha := by
      field_simp [ne_of_gt hden_pos]
    have halpha_pos : 0 < alpha := by
      rw [← hmul_eq]
      exact hmul_pos
    exact le_of_lt halpha_pos
  have htotalSupply_nonneg : 0 ≤ totalSupply := by
    rcases (hcapacity_total.and hcapacity_nonneg).exists with
      ⟨C, htotalC, hnonnegC⟩
    have hactive_nonneg :
        0 ≤ AppliedModelingLib.Matching.activeCapacity
          (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity := by
      unfold AppliedModelingLib.Matching.activeCapacity
      exact Finset.sum_nonneg (fun c _hc => hnonnegC c)
    simpa [htotalC] using hactive_nonneg
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_capacity_bound_interval_mass_large_matched_mass_source_endpoint_estimates_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut mass.largeIntervalMass
      mass.largeMatchedMass mass.smallMatchedMass htotalSupply_nonneg
      htotalSupply_lt_one halpha_nonneg hcapacity_bound ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_index, htail_floor, hlarge_interval_lower,
      hlarge_endpoint, hsmall_lower⟩
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_index, htail_floor, hlarge_interval_lower,
      ?_, ?_, hlarge_endpoint, hsmall_lower, ?_⟩
  · filter_upwards
      [mass.largeIntervalMass_le_totalActiveCapacity epsilon hepsilon,
        hcapacity_total] with C hmassC htotalC P hP
    calc
      mass.largeIntervalMass C P ≤
          AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity :=
        hmassC P hP
      _ = totalSupply := htotalC
  · filter_upwards
      [hcapacity_total, hcapacity_bound,
        mass.largeActiveCapacity_le_matchedMass epsilon hepsilon] with
      C htotalC hboundC hmatchedC P hP
    have hcard :
        (((indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C).card) : ℝ) ≤
          epsilon * ((C + 1 : ℕ) : ℝ) := by
      exact le_trans
        (indexPrefixSmall_card_le_index (epsilonFloorSplitIndex epsilon C) C)
        (epsilonFloorSplitIndex_le epsilon C (le_of_lt hepsilon))
    have hC_pos : 0 < (((C + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_pos C
    have hcap_le :
        ∀ c ∈ indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C,
          (Mseq C).capacity c ≤ alpha / ((C + 1 : ℕ) : ℝ) := by
      intro c _hc
      exact le_of_lt (hboundC c)
    have hsmall_cap :
        AppliedModelingLib.Matching.activeCapacity
            (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
            (Mseq C).capacity ≤
          epsilon * alpha :=
      smallActiveSet_capacity_le_epsilon_mul_alpha
        (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
        (Mseq C).capacity hcard halpha_nonneg hC_pos hcap_le
    have htotal_lower :
        totalSupply ≤
          AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity := by
      rw [htotalC]
    have hlarge_cap :
        totalSupply - epsilon * alpha ≤
          AppliedModelingLib.Matching.activeCapacity
            (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
            (Mseq C).capacity :=
      AppliedModelingLib.Matching.activeCapacity_right_ge_totalLower_sub_leftUpper_of_partition
        (total := (Finset.univ : Finset (Fin (C + 1))))
        (left := indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
        (right := indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
        (Mseq C).capacity
        (indexPrefixSmall_union_indexSuffixLarge
          (epsilonFloorSplitIndex epsilon C) C)
        (indexPrefixSmall_disjoint_indexSuffixLarge
          (epsilonFloorSplitIndex epsilon C) C)
        htotal_lower hsmall_cap
    have hlarge_cap' :
        totalSupply - alpha * epsilon ≤
          AppliedModelingLib.Matching.activeCapacity
            (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
            (Mseq C).capacity := by
      simpa [mul_comm] using hlarge_cap
    exact le_trans hlarge_cap' (hmatchedC P hP)
  · exact mass.smallMatchedMass_le_activeCapacity epsilon hepsilon

/--
Theorem 2 route with the semantic mass-clearing laws exposed as separate
visible hypotheses.  This is definitionally the same boundary as
`Theorem2MassClearingInterface`, but avoids hiding the interval/matched-mass
capacity-fill laws behind a record argument in paper-facing rows.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_massClearing_fields_endpoint_estimates_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (largeIntervalMass largeMatchedMass smallMatchedMass :
      ∀ C : ℕ, (Mseq C).Cutoff → ℝ)
    (hlargeIntervalMass_le_totalActiveCapacity :
      ∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ C : ℕ in atTop,
          ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
            largeIntervalMass C P ≤
              AppliedModelingLib.Matching.activeCapacity
                (Finset.univ : Finset (Fin (C + 1)))
                (Mseq C).capacity)
    (hlargeActiveCapacity_le_matchedMass :
      ∀ epsilon, 0 < epsilon →
        ∀ᶠ C : ℕ in atTop,
          ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
            AppliedModelingLib.Matching.activeCapacity
                (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                (Mseq C).capacity ≤
              largeMatchedMass C P)
    (hsmallMatchedMass_le_activeCapacity :
      ∀ epsilon, 0 < epsilon →
        ∀ᶠ C : ℕ in atTop,
          ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
            smallMatchedMass C P ≤
              AppliedModelingLib.Matching.activeCapacity
                (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                (Mseq C).capacity)
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_total :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity =
          totalSupply)
    (hcapacity_open_bound :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1),
          0 < (Mseq C).capacity c ∧
            (Mseq C).capacity c < alpha / ((C + 1 : ℕ) : ℝ))
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c : Fin (C + 1),
                epsilonFloorSplitIndex epsilon C ≤ (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow (cutoffOut C P) ≤
                largeIntervalMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeMatchedMass C P - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar (cutoffOut C P) ≤
                smallMatchedMass C P)) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  let mass : Theorem2MassClearingInterface Mseq :=
    { largeIntervalMass := largeIntervalMass
      largeMatchedMass := largeMatchedMass
      smallMatchedMass := smallMatchedMass
      largeIntervalMass_le_totalActiveCapacity :=
        hlargeIntervalMass_le_totalActiveCapacity
      largeActiveCapacity_le_matchedMass :=
        hlargeActiveCapacity_le_matchedMass
      smallMatchedMass_le_activeCapacity :=
        hsmallMatchedMass_le_activeCapacity }
  exact
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_massClearing_endpoint_estimates_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut mass htotalSupply_lt_one
      hcapacity_total hcapacity_open_bound hsource

/--
Theorem 2 route with source-level block-mass identities.

This wrapper derives the three visible mass-clearing inequalities from the
paper's semantic ingredients: total matched mass equals total capacity, matched
mass in a college block equals that block's capacity, the large interval mass
is bounded by total matched mass, and the small interval mass is bounded by the
small-block matched mass.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_source_block_mass_endpoint_estimates_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (largeIntervalMass largeMatchedMass smallMatchedMass :
      ∀ C : ℕ, (Mseq C).Cutoff → ℝ)
    (matchedMass :
      ∀ C : ℕ, (Mseq C).Cutoff → Finset (Fin (C + 1)) → ℝ)
    (hlargeIntervalMass_le_totalMatchedMass :
      ∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ C : ℕ in atTop,
          ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
            largeIntervalMass C P ≤
              matchedMass C P (Finset.univ : Finset (Fin (C + 1))))
    (htotalMatchedMass_eq_totalActiveCapacity :
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          matchedMass C P (Finset.univ : Finset (Fin (C + 1))) =
            AppliedModelingLib.Matching.activeCapacity
              (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity)
    (hlargeMatchedMass_eq_largeBlockMatchedMass :
      ∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ C : ℕ in atTop,
          ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
            largeMatchedMass C P =
              matchedMass C P
                (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C))
    (hlargeBlockMatchedMass_eq_activeCapacity :
      ∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ C : ℕ in atTop,
          ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
            matchedMass C P
                (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C) =
              AppliedModelingLib.Matching.activeCapacity
                (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                (Mseq C).capacity)
    (hsmallMatchedMass_le_smallBlockMatchedMass :
      ∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ C : ℕ in atTop,
          ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
            smallMatchedMass C P ≤
              matchedMass C P
                (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C))
    (hsmallBlockMatchedMass_eq_activeCapacity :
      ∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ C : ℕ in atTop,
          ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
            matchedMass C P
                (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C) =
              AppliedModelingLib.Matching.activeCapacity
                (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                (Mseq C).capacity)
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_total :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity =
          totalSupply)
    (hcapacity_open_bound :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1),
          0 < (Mseq C).capacity c ∧
            (Mseq C).capacity c < alpha / ((C + 1 : ℕ) : ℝ))
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c : Fin (C + 1),
                epsilonFloorSplitIndex epsilon C ≤ (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow (cutoffOut C P) ≤
                largeIntervalMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeMatchedMass C P - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar (cutoffOut C P) ≤
                smallMatchedMass C P)) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_massClearing_fields_endpoint_estimates_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut largeIntervalMass
      largeMatchedMass smallMatchedMass ?_ ?_ ?_ htotalSupply_lt_one
      hcapacity_total hcapacity_open_bound hsource
  · intro epsilon hepsilon
    filter_upwards
      [hlargeIntervalMass_le_totalMatchedMass epsilon hepsilon,
        htotalMatchedMass_eq_totalActiveCapacity] with C hlargeC htotalC P hP
    calc
      largeIntervalMass C P ≤
          matchedMass C P (Finset.univ : Finset (Fin (C + 1))) :=
        hlargeC P hP
      _ = AppliedModelingLib.Matching.activeCapacity
          (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity :=
        htotalC P hP
  · intro epsilon hepsilon
    filter_upwards
      [hlargeMatchedMass_eq_largeBlockMatchedMass epsilon hepsilon,
        hlargeBlockMatchedMass_eq_activeCapacity epsilon hepsilon] with
      C hlargeEqC hactiveEqC P hP
    calc
      AppliedModelingLib.Matching.activeCapacity
          (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
          (Mseq C).capacity =
          matchedMass C P
            (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C) :=
        (hactiveEqC P hP).symm
      _ ≤ largeMatchedMass C P := le_of_eq (hlargeEqC P hP).symm
  · intro epsilon hepsilon
    filter_upwards
      [hsmallMatchedMass_le_smallBlockMatchedMass epsilon hepsilon,
        hsmallBlockMatchedMass_eq_activeCapacity epsilon hepsilon] with
      C hsmallLeC hactiveEqC P hP
    calc
      smallMatchedMass C P ≤
          matchedMass C P
            (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C) :=
        hsmallLeC P hP
      _ = AppliedModelingLib.Matching.activeCapacity
          (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
          (Mseq C).capacity :=
        hactiveEqC P hP

/--
Theorem 2 route from aggregate-demand market-clearing semantics.

This strengthens the block-mass route by deriving every block-capacity
identity from a single matched-mass-as-aggregate-demand identity and the
paper's exact market-clearing equality between aggregate demand and capacity.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_aggregateDemand_block_mass_endpoint_estimates_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (largeIntervalMass largeMatchedMass smallMatchedMass :
      ∀ C : ℕ, (Mseq C).Cutoff → ℝ)
    (matchedMass :
      ∀ C : ℕ, (Mseq C).Cutoff → Finset (Fin (C + 1)) → ℝ)
    (hlargeIntervalMass_le_totalMatchedMass :
      ∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ C : ℕ in atTop,
          ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
            largeIntervalMass C P ≤
              matchedMass C P (Finset.univ : Finset (Fin (C + 1))))
    (hlargeMatchedMass_eq_largeBlockMatchedMass :
      ∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ C : ℕ in atTop,
          ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
            largeMatchedMass C P =
              matchedMass C P
                (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C))
    (hsmallMatchedMass_le_smallBlockMatchedMass :
      ∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ C : ℕ in atTop,
          ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
            smallMatchedMass C P ≤
              matchedMass C P
                (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C))
    (hmatchedMass_eq_aggregateDemand :
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          ∀ active : Finset (Fin (C + 1)),
            matchedMass C P active =
              ∑ c ∈ active, (Mseq C).aggregateDemand P c)
    (hmarketClearing_aggregateDemand_eq_capacity :
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          ∀ c : Fin (C + 1), (Mseq C).aggregateDemand P c = (Mseq C).capacity c)
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_total :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity =
          totalSupply)
    (hcapacity_open_bound :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1),
          0 < (Mseq C).capacity c ∧
            (Mseq C).capacity c < alpha / ((C + 1 : ℕ) : ℝ))
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c : Fin (C + 1),
                epsilonFloorSplitIndex epsilon C ≤ (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow (cutoffOut C P) ≤
                largeIntervalMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeMatchedMass C P - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar (cutoffOut C P) ≤
                smallMatchedMass C P)) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_source_block_mass_endpoint_estimates_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut largeIntervalMass
      largeMatchedMass smallMatchedMass matchedMass
      hlargeIntervalMass_le_totalMatchedMass ?_
      hlargeMatchedMass_eq_largeBlockMatchedMass ?_
      hsmallMatchedMass_le_smallBlockMatchedMass ?_
      htotalSupply_lt_one hcapacity_total hcapacity_open_bound hsource
  · filter_upwards
      [hmatchedMass_eq_aggregateDemand,
        hmarketClearing_aggregateDemand_eq_capacity] with C hmatchedC hclearC P hP
    calc
      matchedMass C P (Finset.univ : Finset (Fin (C + 1))) =
          ∑ c ∈ (Finset.univ : Finset (Fin (C + 1))),
            (Mseq C).aggregateDemand P c :=
        hmatchedC P hP (Finset.univ : Finset (Fin (C + 1)))
      _ = AppliedModelingLib.Matching.activeCapacity
          (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity :=
        AppliedModelingLib.Matching.activeAggregateDemand_eq_activeCapacity_of_forall_eq
          (Finset.univ : Finset (Fin (C + 1)))
          (by intro c _hc; exact hclearC P hP c)
  · intro epsilon hepsilon
    filter_upwards
      [hmatchedMass_eq_aggregateDemand,
        hmarketClearing_aggregateDemand_eq_capacity] with C hmatchedC hclearC P hP
    calc
      matchedMass C P (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C) =
          ∑ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
            (Mseq C).aggregateDemand P c :=
        hmatchedC P hP (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
      _ = AppliedModelingLib.Matching.activeCapacity
          (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
          (Mseq C).capacity :=
        AppliedModelingLib.Matching.activeAggregateDemand_eq_activeCapacity_of_forall_eq
          (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
          (by intro c _hc; exact hclearC P hP c)
  · intro epsilon hepsilon
    filter_upwards
      [hmatchedMass_eq_aggregateDemand,
        hmarketClearing_aggregateDemand_eq_capacity] with C hmatchedC hclearC P hP
    calc
      matchedMass C P (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C) =
          ∑ c ∈ indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C,
            (Mseq C).aggregateDemand P c :=
        hmatchedC P hP (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
      _ = AppliedModelingLib.Matching.activeCapacity
          (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
          (Mseq C).capacity :=
        AppliedModelingLib.Matching.activeAggregateDemand_eq_activeCapacity_of_forall_eq
          (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
          (by intro c _hc; exact hclearC P hP c)

/--
Theorem 2 route with epsilon-local source mass objects.

The source proof's interval and small-firm matched-mass quantities depend on
the value window chosen after `epsilon` is fixed.  This theorem keeps those
quantities local to the source package, and derives the capacity comparisons
from a single matched-mass-as-aggregate-demand law plus exact market clearing.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_local_aggregateDemand_mass_endpoint_estimates_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (matchedMass :
      ∀ C : ℕ, (Mseq C).Cutoff → Finset (Fin (C + 1)) → ℝ)
    (hmatchedMass_eq_aggregateDemand :
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          ∀ active : Finset (Fin (C + 1)),
            matchedMass C P active =
              ∑ c ∈ active, (Mseq C).aggregateDemand P c)
    (hmarketClearing_aggregateDemand_eq_capacity :
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          ∀ c : Fin (C + 1), (Mseq C).aggregateDemand P c = (Mseq C).capacity c)
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_total :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity =
          totalSupply)
    (hcapacity_open_bound :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1),
          0 < (Mseq C).capacity c ∧
            (Mseq C).capacity c < alpha / ((C + 1 : ℕ) : ℝ))
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          ∃ largeIntervalMass smallMatchedIntervalMass :
              ∀ C : ℕ, (Mseq C).Cutoff → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c : Fin (C + 1),
                epsilonFloorSplitIndex epsilon C ≤ (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow (cutoffOut C P) ≤
                largeIntervalMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeIntervalMass C P ≤
                matchedMass C P (Finset.univ : Finset (Fin (C + 1)))) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              matchedMass C P
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C) -
                  epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar (cutoffOut C P) ≤
                smallMatchedIntervalMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              smallMatchedIntervalMass C P ≤
                matchedMass C P
                  (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C))) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_source_endpoint_estimates_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut htotalSupply_lt_one
      hcapacity_total hcapacity_open_bound ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, largeIntervalMass,
      smallMatchedIntervalMass, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_index, htail_floor, hlarge_interval_lower,
      hlarge_interval_total_matched, hlarge_endpoint_matched,
      hsmall_interval_lower, hsmall_interval_matched⟩
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_index, htail_floor, ?_, ?_, ?_⟩
  · filter_upwards
      [hlarge_interval_lower, hlarge_interval_total_matched,
        hmatchedMass_eq_aggregateDemand,
        hmarketClearing_aggregateDemand_eq_capacity,
        hcapacity_total] with
      C hlargeLowerC hlargeTotalC hmatchedC hclearC hcapacityC P hP
    calc
      (1 - epsilon) *
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
            vLow (cutoffOut C P) ≤
          largeIntervalMass C P :=
        hlargeLowerC P hP
      _ ≤ matchedMass C P (Finset.univ : Finset (Fin (C + 1))) :=
        hlargeTotalC P hP
      _ = AppliedModelingLib.Matching.activeCapacity
          (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity := by
        exact
          AppliedModelingLib.Matching.mass_eq_activeCapacity_of_aggregateDemand_eq_capacity
            (Finset.univ : Finset (Fin (C + 1)))
            (hmatchedC P hP (Finset.univ : Finset (Fin (C + 1))))
            (by intro c _hc; exact hclearC P hP c)
      _ = totalSupply := hcapacityC
  · filter_upwards
      [hlarge_endpoint_matched, hmatchedMass_eq_aggregateDemand,
        hmarketClearing_aggregateDemand_eq_capacity] with
      C hlargeEndpointC hmatchedC hclearC P hP
    have hblock :
        matchedMass C P
            (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C) =
          AppliedModelingLib.Matching.activeCapacity
            (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
            (Mseq C).capacity := by
      exact
        AppliedModelingLib.Matching.mass_eq_activeCapacity_of_aggregateDemand_eq_capacity
          (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
          (hmatchedC P hP (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C))
          (by intro c _hc; exact hclearC P hP c)
    calc
      AppliedModelingLib.Matching.activeCapacity
          (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
          (Mseq C).capacity - epsilon =
          matchedMass C P
              (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C) -
            epsilon := by
        rw [hblock]
      _ ≤ cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
            vHigh (cutoffOut C P) :=
        hlargeEndpointC P hP
  · filter_upwards
      [hsmall_interval_lower, hsmall_interval_matched,
        hmatchedMass_eq_aggregateDemand,
        hmarketClearing_aggregateDemand_eq_capacity] with
      C hsmallLowerC hsmallMatchedC hmatchedC hclearC P hP
    calc
      Real.sqrt epsilon *
          (1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma)))) *
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
            vStar (cutoffOut C P) ≤
          smallMatchedIntervalMass C P :=
        hsmallLowerC P hP
      _ ≤ matchedMass C P
            (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C) :=
        hsmallMatchedC P hP
      _ = AppliedModelingLib.Matching.activeCapacity
          (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
          (Mseq C).capacity := by
        exact
          AppliedModelingLib.Matching.mass_eq_activeCapacity_of_aggregateDemand_eq_capacity
            (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
            (hmatchedC P hP (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C))
            (by intro c _hc; exact hclearC P hP c)

/--
Theorem 2 route from local event-mass semantics.

This refines the local-mass route by constructing the local interval and
small-firm masses as real masses of explicit outcome events.  The only
matching semantics needed for those masses are event-to-choice implications
and the equality between chosen-block mass and aggregate demand.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_local_eventMass_aggregateDemand_endpoint_estimates_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    (hfinite : ∀ C P, IsFiniteMeasure (outcomeLaw C P))
    (hchoiceMass_eq_aggregateDemand :
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          ∀ active : Finset (Fin (C + 1)),
            AppliedModelingLib.Matching.choiceMass
                (outcomeLaw C P) (chosenCollege C P) active =
              ∑ c ∈ active, (Mseq C).aggregateDemand P c)
    (hmarketClearing_aggregateDemand_eq_capacity :
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          ∀ c : Fin (C + 1), (Mseq C).aggregateDemand P c = (Mseq C).capacity c)
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_total :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity =
          totalSupply)
    (hcapacity_open_bound :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1),
          0 < (Mseq C).capacity c ∧
            (Mseq C).capacity c < alpha / ((C + 1 : ℕ) : ℝ))
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          ∃ largeIntervalEvent smallMatchedIntervalEvent :
              ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Prop,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c : Fin (C + 1),
                epsilonFloorSplitIndex epsilon C ≤ (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow (cutoffOut C P) ≤
                AppliedModelingLib.Matching.eventMass
                  (outcomeLaw C P) (largeIntervalEvent C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ ω : OutcomeSeq C,
                largeIntervalEvent C P ω →
                  AppliedModelingLib.Matching.chosenInActive
                    (chosenCollege C P)
                    (Finset.univ : Finset (Fin (C + 1))) ω) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Matching.choiceMass
                  (outcomeLaw C P) (chosenCollege C P)
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C) -
                  epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.eventMass
                  (outcomeLaw C P) (smallMatchedIntervalEvent C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ ω : OutcomeSeq C,
                smallMatchedIntervalEvent C P ω →
                  AppliedModelingLib.Matching.chosenInActive
                    (chosenCollege C P)
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C) ω)) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_local_aggregateDemand_mass_endpoint_estimates_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut
      (fun C P active =>
        AppliedModelingLib.Matching.choiceMass
          (outcomeLaw C P) (chosenCollege C P) active)
      hchoiceMass_eq_aggregateDemand
      hmarketClearing_aggregateDemand_eq_capacity htotalSupply_lt_one
      hcapacity_total hcapacity_open_bound ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, largeIntervalEvent,
      smallMatchedIntervalEvent, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_index, htail_floor, hlarge_interval_lower,
      hlarge_event_chosen, hlarge_endpoint_choice,
      hsmall_interval_lower, hsmall_event_chosen⟩
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff,
      (fun C P =>
        AppliedModelingLib.Matching.eventMass
          (outcomeLaw C P) (largeIntervalEvent C P)),
      (fun C P =>
        AppliedModelingLib.Matching.eventMass
          (outcomeLaw C P) (smallMatchedIntervalEvent C P)),
      hvLow, hvHigh, hvStar, hvStrict, hlower_atTop, hcutoff_index,
      htail_floor, hlarge_interval_lower, ?_, hlarge_endpoint_choice,
      hsmall_interval_lower, ?_⟩
  · filter_upwards [hlarge_event_chosen] with C hchosenC P hP
    haveI : IsFiniteMeasure (outcomeLaw C P) := hfinite C P
    exact
      AppliedModelingLib.Matching.eventMass_le_choiceMass_of_imp
        (outcomeLaw C P) (hchosenC P hP)
  · filter_upwards [hsmall_event_chosen] with C hchosenC P hP
    haveI : IsFiniteMeasure (outcomeLaw C P) := hfinite C P
    exact
      AppliedModelingLib.Matching.eventMass_le_choiceMass_of_imp
        (outcomeLaw C P) (hchosenC P hP)

/--
Theorem 2 route from probability-law local event semantics.

This is the same strongest local event-mass route, but with the source-facing
assumption that each outcome law is a probability measure.  Lean derives the
finite-measure instances required by the event-mass comparisons internally.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_local_probabilityEvent_aggregateDemand_endpoint_estimates_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    (houtcome_prob : ∀ C P, IsProbabilityMeasure (outcomeLaw C P))
    (hchoiceMass_eq_aggregateDemand :
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          ∀ active : Finset (Fin (C + 1)),
            AppliedModelingLib.Matching.choiceMass
                (outcomeLaw C P) (chosenCollege C P) active =
              ∑ c ∈ active, (Mseq C).aggregateDemand P c)
    (hmarketClearing_aggregateDemand_eq_capacity :
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          ∀ c : Fin (C + 1), (Mseq C).aggregateDemand P c = (Mseq C).capacity c)
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_total :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity =
          totalSupply)
    (hcapacity_open_bound :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1),
          0 < (Mseq C).capacity c ∧
            (Mseq C).capacity c < alpha / ((C + 1 : ℕ) : ℝ))
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          ∃ largeIntervalEvent smallMatchedIntervalEvent :
              ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Prop,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c : Fin (C + 1),
                epsilonFloorSplitIndex epsilon C ≤ (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow (cutoffOut C P) ≤
                AppliedModelingLib.Matching.eventMass
                  (outcomeLaw C P) (largeIntervalEvent C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ ω : OutcomeSeq C,
                largeIntervalEvent C P ω →
                  AppliedModelingLib.Matching.chosenInActive
                    (chosenCollege C P)
                    (Finset.univ : Finset (Fin (C + 1))) ω) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Matching.choiceMass
                  (outcomeLaw C P) (chosenCollege C P)
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C) -
                  epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.eventMass
                  (outcomeLaw C P) (smallMatchedIntervalEvent C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ ω : OutcomeSeq C,
                smallMatchedIntervalEvent C P ω →
                  AppliedModelingLib.Matching.chosenInActive
                    (chosenCollege C P)
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C) ω)) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_local_eventMass_aggregateDemand_endpoint_estimates_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut OutcomeSeq outcomeLaw chosenCollege
      ?_ hchoiceMass_eq_aggregateDemand
      hmarketClearing_aggregateDemand_eq_capacity htotalSupply_lt_one
      hcapacity_total hcapacity_open_bound hsource
  intro C P
  haveI : IsProbabilityMeasure (outcomeLaw C P) := houtcome_prob C P
  infer_instance

/--
At the selected A-L cutoff attached to each stable matching, singleton choice
events whose masses are aggregate demands lift to active-block choice mass for
every finite block of colleges.  This is the reusable source-model bridge used
by the Theorem 2 amplification route before exact-fill market clearing turns
aggregate demand into capacity.
-/
theorem selectedStable_choiceMass_eq_sum_aggregateDemand_of_singleton_eventMass_eq
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    (houtcome_prob :
      ∀ C : ℕ, ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
        IsProbabilityMeasure
          (outcomeLaw C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := μ.1) μ.2)))
    (hchosen_singleton_measurable :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          ∀ c : Fin (C + 1),
            MeasurableSet
              {ω : OutcomeSeq C |
                chosenCollege C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2) ω = some c})
    (hsingleton_choiceMass_eq_aggregateDemand :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          ∀ c : Fin (C + 1),
            AppliedModelingLib.Matching.eventMass
                (outcomeLaw C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := μ.1) μ.2))
                (fun ω : OutcomeSeq C =>
                  chosenCollege C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2) ω = some c) =
              (Mseq C).aggregateDemand
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2) c) :
    ∀ᶠ C : ℕ in atTop,
      ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
        ∀ active : Finset (Fin (C + 1)),
          AppliedModelingLib.Matching.choiceMass
              (outcomeLaw C
                ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))
              (chosenCollege C
                ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))
              active =
            ∑ c ∈ active,
              (Mseq C).aggregateDemand
                ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2) c := by
  filter_upwards
    [hchosen_singleton_measurable,
      hsingleton_choiceMass_eq_aggregateDemand] with
    C hmeasC hsingleC μ active
  let P :=
    (Iseq C).marketClearingCutoffOfStable
      (μ := μ.1) μ.2
  haveI : IsFiniteMeasure (outcomeLaw C P) := by
    haveI : IsProbabilityMeasure (outcomeLaw C P) :=
      houtcome_prob C μ
    infer_instance
  exact
    AppliedModelingLib.Matching.choiceMass_eq_sum_aggregateDemand_of_singleton_eventMass_eq
      (outcomeLaw C P) (chosenCollege C P) active
      (by
        intro c _hc
        exact hmeasC μ c)
      (by
        intro c _hc
        exact hsingleC μ c)

/--
Theorem 2 route from selected-stable local probability events.

The source package is only required on the selected A-L market-clearing cutoff
attached to each stable matching.  Lean derives the endpoint mass bounds,
capacity regularity, iid product bridge, and final `F_1/F_2` decomposition.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_selected_stable_cutoff_floor_index_split_local_probabilityEvent_aggregateDemand_endpoint_estimates_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    (houtcome_prob :
      ∀ C : ℕ, ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
        IsProbabilityMeasure
          (outcomeLaw C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := μ.1) μ.2)))
    (hchoiceMass_eq_aggregateDemand :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          ∀ active : Finset (Fin (C + 1)),
            AppliedModelingLib.Matching.choiceMass
                (outcomeLaw C
                  ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))
                (chosenCollege C
                  ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))
                active =
              ∑ c ∈ active,
                (Mseq C).aggregateDemand
                  ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2) c)
    (hmarketClearing_aggregateDemand_eq_capacity :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          ∀ c : Fin (C + 1),
            (Mseq C).aggregateDemand
                ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2) c =
              (Mseq C).capacity c)
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_total :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity =
          totalSupply)
    (hcapacity_open_bound :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1),
          0 < (Mseq C).capacity c ∧
            (Mseq C).capacity c < alpha / ((C + 1 : ℕ) : ℝ))
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          ∃ largeIntervalEvent smallMatchedIntervalEvent :
              ∀ C : ℕ,
                { μ : (Mseq C).Matching // (Mseq C).Stable μ } →
                  OutcomeSeq C → Prop,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
                lowerCutoff C ≤
                  cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2) c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
                AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2) c - vHigh) ≤
                  sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow
                    (cutoffOut C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2)) ≤
                AppliedModelingLib.Matching.eventMass
                  (outcomeLaw C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))
                  (largeIntervalEvent C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              ∀ ω : OutcomeSeq C,
                largeIntervalEvent C μ ω →
                  AppliedModelingLib.Matching.chosenInActive
                    (chosenCollege C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2))
                    (Finset.univ : Finset (Fin (C + 1))) ω) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              AppliedModelingLib.Matching.choiceMass
                  (outcomeLaw C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))
                  (chosenCollege C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C) -
                  epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar
                    (cutoffOut C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2)) ≤
                AppliedModelingLib.Matching.eventMass
                  (outcomeLaw C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))
                  (smallMatchedIntervalEvent C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              ∀ ω : OutcomeSeq C,
                smallMatchedIntervalEvent C μ ω →
                  AppliedModelingLib.Matching.chosenInActive
                    (chosenCollege C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    ω)) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  have hcapacity_nonneg :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1), 0 ≤ (Mseq C).capacity c := by
    filter_upwards [hcapacity_open_bound] with C hboundC c
    exact le_of_lt (hboundC c).1
  have halpha_nonneg : 0 ≤ alpha := by
    rcases hcapacity_open_bound.exists with ⟨C, hboundC⟩
    let c0 : Fin (C + 1) := ⟨0, Nat.succ_pos C⟩
    have hdiv_pos :
        0 < alpha / (((C + 1 : ℕ) : ℝ)) :=
      lt_trans (hboundC c0).1 (hboundC c0).2
    have hden_pos : 0 < (((C + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_pos C
    have hmul_pos :
        0 < (alpha / (((C + 1 : ℕ) : ℝ))) *
          (((C + 1 : ℕ) : ℝ)) :=
      mul_pos hdiv_pos hden_pos
    have hmul_eq :
        (alpha / (((C + 1 : ℕ) : ℝ))) *
            (((C + 1 : ℕ) : ℝ)) = alpha := by
      field_simp [ne_of_gt hden_pos]
    have halpha_pos : 0 < alpha := by
      rw [← hmul_eq]
      exact hmul_pos
    exact le_of_lt halpha_pos
  have htotalSupply_nonneg : 0 ≤ totalSupply := by
    rcases (hcapacity_total.and hcapacity_nonneg).exists with
      ⟨C, htotalC, hnonnegC⟩
    have hactive_nonneg :
        0 ≤ AppliedModelingLib.Matching.activeCapacity
          (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity := by
      unfold AppliedModelingLib.Matching.activeCapacity
      exact Finset.sum_nonneg (fun c _hc => hnonnegC c)
    simpa [htotalC] using hactive_nonneg
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_cutoff_floor_index_split_source_endpoint_estimates_capacityRegular_strict_derived
      (Admissible := fun C : ℕ =>
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (noiseLaw := noiseLaw) (hlong := hlong)
      (cutoff := fun C μ =>
        cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))
      (capacity := fun C _μ => (Mseq C).capacity)
      (totalSupply := totalSupply) (alpha := alpha)
      htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, largeIntervalEvent,
      smallMatchedIntervalEvent, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_index, htail_floor, hlarge_interval_lower,
      hlarge_event_chosen, hlarge_endpoint_choice, hsmall_interval_lower,
      hsmall_event_chosen⟩
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_index, htail_floor, ?_, ?_, ?_, ?_⟩
  · filter_upwards
      [hlarge_interval_lower, hlarge_event_chosen,
        hchoiceMass_eq_aggregateDemand,
        hmarketClearing_aggregateDemand_eq_capacity, hcapacity_total] with
      C hlargeLowerC hlargeChosenC hchoiceC hclearC htotalC μ
    let P :=
      (Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2
    haveI : IsFiniteMeasure (outcomeLaw C P) := by
      haveI : IsProbabilityMeasure (outcomeLaw C P) :=
        houtcome_prob C μ
      infer_instance
    have hevent_le_capacity :
        AppliedModelingLib.Matching.eventMass
            (outcomeLaw C P) (largeIntervalEvent C μ) ≤
          AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity :=
      AppliedModelingLib.Matching.eventMass_le_activeCapacity_of_imp_aggregateDemand_eq_capacity
        (outcomeLaw C P) (chosenCollege C P)
        (Finset.univ : Finset (Fin (C + 1)))
        (hlargeChosenC μ)
        (hchoiceC μ (Finset.univ : Finset (Fin (C + 1))))
        (by intro c _hc; exact hclearC μ c)
    calc
      (1 - epsilon) *
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
            vLow
            (cutoffOut C P) ≤
          AppliedModelingLib.Matching.eventMass
            (outcomeLaw C P) (largeIntervalEvent C μ) :=
        hlargeLowerC μ
      _ ≤ AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity := by
        exact hevent_le_capacity
      _ = totalSupply := htotalC
  · filter_upwards
      [hlarge_endpoint_choice, hchoiceMass_eq_aggregateDemand,
        hmarketClearing_aggregateDemand_eq_capacity, hcapacity_total,
        hcapacity_open_bound] with
      C hlargeEndpointC hchoiceC hclearC htotalC hcapacityC μ
    let P :=
      (Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2
    have hchoice_large :
        AppliedModelingLib.Matching.choiceMass
            (outcomeLaw C P) (chosenCollege C P)
            (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C) =
          AppliedModelingLib.Matching.activeCapacity
            (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
            (Mseq C).capacity :=
      AppliedModelingLib.Matching.choiceMass_eq_activeCapacity_of_aggregateDemand_eq_capacity
        (outcomeLaw C P) (chosenCollege C P)
        (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
        (hchoiceC μ
          (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C))
        (by intro c _hc; exact hclearC μ c)
    have hcard :
        (((indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C).card) : ℝ) ≤
          epsilon * ((C + 1 : ℕ) : ℝ) :=
      le_trans
        (indexPrefixSmall_card_le_index
          (epsilonFloorSplitIndex epsilon C) C)
        (epsilonFloorSplitIndex_le epsilon C hepsilon.le)
    have hC_pos : 0 < (((C + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_pos C
    have hcap_le :
        ∀ c ∈ indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C,
          (Mseq C).capacity c ≤ alpha / ((C + 1 : ℕ) : ℝ) := by
      intro c _hc
      exact le_of_lt (hcapacityC c).2
    have hsmall_cap :
        AppliedModelingLib.Matching.activeCapacity
            (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
            (Mseq C).capacity ≤
          epsilon * alpha :=
      smallActiveSet_capacity_le_epsilon_mul_alpha
        (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
        (Mseq C).capacity hcard halpha_nonneg hC_pos hcap_le
    have htotal_lower :
        totalSupply ≤
          AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity := by
      rw [htotalC]
    have hlarge_cap :
        totalSupply - epsilon * alpha ≤
          AppliedModelingLib.Matching.activeCapacity
            (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
            (Mseq C).capacity :=
      AppliedModelingLib.Matching.activeCapacity_right_ge_totalLower_sub_leftUpper_of_partition
        (total := (Finset.univ : Finset (Fin (C + 1))))
        (left := indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
        (right := indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
        (Mseq C).capacity
        (indexPrefixSmall_union_indexSuffixLarge
          (epsilonFloorSplitIndex epsilon C) C)
        (indexPrefixSmall_disjoint_indexSuffixLarge
          (epsilonFloorSplitIndex epsilon C) C)
        htotal_lower hsmall_cap
    have hlarge_cap' :
        totalSupply - alpha * epsilon ≤
          AppliedModelingLib.Matching.activeCapacity
            (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
            (Mseq C).capacity := by
      simpa [mul_comm] using hlarge_cap
    have hchoice_lower :
        totalSupply - alpha * epsilon - epsilon ≤
          AppliedModelingLib.Matching.choiceMass
            (outcomeLaw C P) (chosenCollege C P)
            (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C) -
            epsilon := by
      rw [hchoice_large]
      linarith
    exact le_trans hchoice_lower (hlargeEndpointC μ)
  · filter_upwards [hcapacity_open_bound] with C hcapacityC μ
    intro c
    exact (hcapacityC c).2
  · filter_upwards
      [hsmall_interval_lower, hsmall_event_chosen,
        hchoiceMass_eq_aggregateDemand,
        hmarketClearing_aggregateDemand_eq_capacity] with
      C hsmallLowerC hsmallChosenC hchoiceC hclearC μ
    let P :=
      (Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2
    haveI : IsFiniteMeasure (outcomeLaw C P) := by
      haveI : IsProbabilityMeasure (outcomeLaw C P) :=
        houtcome_prob C μ
      infer_instance
    have hevent_le_capacity :
        AppliedModelingLib.Matching.eventMass
            (outcomeLaw C P) (smallMatchedIntervalEvent C μ) ≤
          AppliedModelingLib.Matching.activeCapacity
            (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
            (Mseq C).capacity :=
      AppliedModelingLib.Matching.eventMass_le_activeCapacity_of_imp_aggregateDemand_eq_capacity
        (outcomeLaw C P) (chosenCollege C P)
        (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
        (hsmallChosenC μ)
        (hchoiceC μ
          (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C))
        (by intro c _hc; exact hclearC μ c)
    calc
      Real.sqrt epsilon *
          (1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma)))) *
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
            vStar
            (cutoffOut C P) ≤
          AppliedModelingLib.Matching.eventMass
            (outcomeLaw C P) (smallMatchedIntervalEvent C μ) :=
        hsmallLowerC μ
      _ ≤ AppliedModelingLib.Matching.activeCapacity
            (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
            (Mseq C).capacity := by
        exact hevent_le_capacity

/--
Theorem 2 route from selected-stable local probability events with the
small-firm interval integral exposed.

This replaces the direct source clause
`sqrt(epsilon) * denom * p(vStar,F1) <= eventMass(smallMatchedIntervalEvent)`
by the paper's interval ingredients: a value interval above `vStar`, its
`η`-mass, the displayed integral over that interval, and the statement that
the integral is bounded by the small matched event.
-/
theorem theorem2_uniformAmplification_of_fixed_alpha_iidProduct_selected_stable_cutoff_floor_index_split_local_probabilityEvent_aggregateDemand_small_interval_integral_endpoint_estimates_strict_derived
    {StudentSeq : ℕ → Type u}
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    (houtcome_prob :
      ∀ C : ℕ, ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
        IsProbabilityMeasure
          (outcomeLaw C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := μ.1) μ.2)))
    (hchoiceMass_eq_aggregateDemand :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          ∀ active : Finset (Fin (C + 1)),
            AppliedModelingLib.Matching.choiceMass
                (outcomeLaw C
                  ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))
                (chosenCollege C
                  ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))
                active =
              ∑ c ∈ active,
                (Mseq C).aggregateDemand
                  ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2) c)
    (hmarketClearing_aggregateDemand_eq_capacity :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          ∀ c : Fin (C + 1),
            (Mseq C).aggregateDemand
                ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2) c =
              (Mseq C).capacity c)
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_total :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity =
          totalSupply)
    (hcapacity_open_bound :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1),
          0 < (Mseq C).capacity c ∧
            (Mseq C).capacity c < alpha / ((C + 1 : ℕ) : ℝ))
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          ∃ largeIntervalEvent smallMatchedIntervalEvent :
              ∀ C : ℕ,
                { μ : (Mseq C).Matching // (Mseq C).Stable μ } →
                  OutcomeSeq C → Prop,
          ∃ smallInterval :
              ∀ C : ℕ,
                { μ : (Mseq C).Matching // (Mseq C).Stable μ } →
                  Set ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
                lowerCutoff C ≤
                  cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2) c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
                AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2) c - vHigh) ≤
                  sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow
                    (cutoffOut C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2)) ≤
                AppliedModelingLib.Matching.eventMass
                  (outcomeLaw C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))
                  (largeIntervalEvent C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              ∀ ω : OutcomeSeq C,
                largeIntervalEvent C μ ω →
                  AppliedModelingLib.Matching.chosenInActive
                    (chosenCollege C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2))
                    (Finset.univ : Finset (Fin (C + 1))) ω) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              AppliedModelingLib.Matching.choiceMass
                  (outcomeLaw C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))
                  (chosenCollege C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C) -
                  epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              MeasurableSet (smallInterval C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              Integrable
                (fun w : ℝ =>
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                    cutoffAffordanceProbability
                      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                      (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                      w
                      (cutoffOut C
                        ((Iseq C).marketClearingCutoffOfStable
                          (μ := μ.1) μ.2))) η) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              Real.sqrt epsilon ≤ η.real (smallInterval C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              ∀ w : ℝ, w ∈ smallInterval C μ → vStar ≤ w) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              (∫ w : ℝ,
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                    cutoffAffordanceProbability
                      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                      (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                      w
                      (cutoffOut C
                        ((Iseq C).marketClearingCutoffOfStable
                          (μ := μ.1) μ.2)) ∂η) ≤
                AppliedModelingLib.Matching.eventMass
                  (outcomeLaw C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))
                  (smallMatchedIntervalEvent C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              ∀ ω : OutcomeSeq C,
                smallMatchedIntervalEvent C μ ω →
                  AppliedModelingLib.Matching.chosenInActive
                    (chosenCollege C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    ω)) :
    theorem2_uniformAmplificationConclusion
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply := by
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_selected_stable_cutoff_floor_index_split_local_probabilityEvent_aggregateDemand_endpoint_estimates_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut
      OutcomeSeq outcomeLaw chosenCollege
      houtcome_prob hchoiceMass_eq_aggregateDemand
      hmarketClearing_aggregateDemand_eq_capacity htotalSupply_lt_one
      hcapacity_total hcapacity_open_bound ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, largeIntervalEvent,
      smallMatchedIntervalEvent, smallInterval,
      hvLow, hvHigh, hvStar, hvStrict, hlower_atTop, hcutoff_index,
      htail_floor, hlarge_interval_lower, hlarge_event_chosen,
      hlarge_endpoint_choice, hsmall_meas, hsmall_int, hsmall_mass,
      hsmall_ge, hsmall_integral_event, hsmall_event_chosen⟩
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff, largeIntervalEvent,
      smallMatchedIntervalEvent, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_index, htail_floor, hlarge_interval_lower,
      hlarge_event_chosen, hlarge_endpoint_choice, ?_,
      hsmall_event_chosen⟩
  filter_upwards
    [hsmall_meas, hsmall_int, hsmall_mass, hsmall_ge,
      hsmall_integral_event] with
    C hmeasC hintC hmassC hgeC hintegralC μ
  let P :=
    (Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2
  have hpSmall_mono :
      Monotone (fun w : ℝ =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
          w (cutoffOut C P)) := by
    intro x y hxy
    exact
      cutoffAffordanceProbability_mono_value
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (active := indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
        (cutoff := cutoffOut C P) hxy
  have hpStar_nonneg :
      0 ≤
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
          vStar (cutoffOut C P) :=
    cutoffAffordanceProbability_nonneg
      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
      (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
      vStar (cutoffOut C P)
  have hnonneg_compl :
      ∀ w : ℝ, w ∉ smallInterval C μ →
        0 ≤
          (1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma)))) *
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
            w (cutoffOut C P) := by
    intro w _hw
    exact
      mul_nonneg (le_of_lt hden)
        (cutoffAffordanceProbability_nonneg
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
          w (cutoffOut C P))
  exact
    theorem2_smallFirm_matchedMass_lower_bound_of_interval_integral
      η
      (region := smallInterval C μ)
      (mass := Real.sqrt epsilon)
      (denom :=
        1 - totalSupply - epsilon -
          (1 - Real.exp (-(2 * epsilon * sigma))))
      (matchedMass :=
        AppliedModelingLib.Matching.eventMass
          (outcomeLaw C P) (smallMatchedIntervalEvent C μ))
      (pSmall := fun w : ℝ =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
          w (cutoffOut C P))
      (vStar := vStar)
      (hmeasC μ) (hintC μ) (hmassC μ) (le_of_lt hden)
      hpStar_nonneg hpSmall_mono (hgeC μ) hnonneg_compl
      (hintegralC μ)

/--
Theorem 2 selected-stable source clauses from local probability-event
semantics.

This is the source-clause projection of the selected-stable local-event route.
The source laws are required only at the selected A-L cutoff attached to each
stable matching; singleton choice events and exact-fill market clearing derive
the block choice-mass equalities used by the amplification proof.
-/
theorem theorem2_uniformAmplification_source_clauses_of_fixed_alpha_iidProduct_selected_stable_cutoff_floor_index_split_local_probabilityEvent_aggregateDemand_endpoint_estimates_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (Kseq : ∀ C : ℕ, MarketClearingCapacityInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    (houtcome_prob :
      ∀ C : ℕ, ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
        IsProbabilityMeasure
          (outcomeLaw C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := μ.1) μ.2)))
    (hchosen_singleton_measurable :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          ∀ c : Fin (C + 1),
            MeasurableSet
              {ω : OutcomeSeq C |
                chosenCollege C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2) ω = some c})
    (hsingleton_choiceMass_eq_aggregateDemand :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          ∀ c : Fin (C + 1),
            AppliedModelingLib.Matching.eventMass
                (outcomeLaw C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := μ.1) μ.2))
                (fun ω : OutcomeSeq C =>
                  chosenCollege C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2) ω = some c) =
              (Mseq C).aggregateDemand
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2) c)
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_total :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity =
          totalSupply)
    (hcapacity_open_bound :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1),
          0 < (Mseq C).capacity c ∧
            (Mseq C).capacity c < alpha / ((C + 1 : ℕ) : ℝ))
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          ∃ largeIntervalEvent smallMatchedIntervalEvent :
              ∀ C : ℕ,
                { μ : (Mseq C).Matching // (Mseq C).Stable μ } →
                  OutcomeSeq C → Prop,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
                lowerCutoff C ≤
                  cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2) c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
                AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2) c - vHigh) ≤
                  sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow
                    (cutoffOut C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2)) ≤
                AppliedModelingLib.Matching.eventMass
                  (outcomeLaw C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))
                  (largeIntervalEvent C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              ∀ ω : OutcomeSeq C,
                largeIntervalEvent C μ ω →
                  AppliedModelingLib.Matching.chosenInActive
                    (chosenCollege C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2))
                    (Finset.univ : Finset (Fin (C + 1))) ω) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              AppliedModelingLib.Matching.choiceMass
                  (outcomeLaw C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))
                  (chosenCollege C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C) -
                  epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar
                    (cutoffOut C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2)) ≤
                AppliedModelingLib.Matching.eventMass
                  (outcomeLaw C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))
                  (smallMatchedIntervalEvent C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              ∀ ω : OutcomeSeq C,
                smallMatchedIntervalEvent C μ ω →
                  AppliedModelingLib.Matching.chosenInActive
                    (chosenCollege C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    ω)) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          |cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2)) -
            totalSupply| < ε :=
  theorem2_uniformAmplification_source_clauses
    (theorem2_uniformAmplification_of_fixed_alpha_iidProduct_selected_stable_cutoff_floor_index_split_local_probabilityEvent_aggregateDemand_endpoint_estimates_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut
      OutcomeSeq outcomeLaw chosenCollege
      houtcome_prob
      (selectedStable_choiceMass_eq_sum_aggregateDemand_of_singleton_eventMass_eq
        Mseq Iseq OutcomeSeq outcomeLaw chosenCollege
        houtcome_prob hchosen_singleton_measurable
        hsingleton_choiceMass_eq_aggregateDemand)
      (Filter.Eventually.of_forall (fun C => by
        intro μ c
        exact
          AppliedModelingLib.Matching.MarketClearingCapacityInterface.marketClearingCutoffOfStable_aggregateDemand_eq_capacity
            (Kseq C) (Iseq C) μ.2 c))
      htotalSupply_lt_one
      hcapacity_total hcapacity_open_bound hsource)

/--
Theorem 2 selected-stable source clauses with scalar high-tail input.

This is the paper-shaped variant of the selected-stable local-event route:
the appendix proof bounds the high-value tail at a common lower cutoff floor
and uses the fact that every large-block cutoff is above that floor.  Lean
derives the per-college high-tail bounds by antitonicity of upper-tail mass.
-/
theorem theorem2_uniformAmplification_source_clauses_of_fixed_alpha_iidProduct_selected_stable_cutoff_floor_index_split_scalar_tail_local_probabilityEvent_aggregateDemand_endpoint_estimates_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (Kseq : ∀ C : ℕ, MarketClearingCapacityInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    (houtcome_prob :
      ∀ C : ℕ, ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
        IsProbabilityMeasure
          (outcomeLaw C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := μ.1) μ.2)))
    (hchosen_singleton_measurable :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          ∀ c : Fin (C + 1),
            MeasurableSet
              {ω : OutcomeSeq C |
                chosenCollege C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2) ω = some c})
    (hsingleton_choiceMass_eq_aggregateDemand :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          ∀ c : Fin (C + 1),
            AppliedModelingLib.Matching.eventMass
                (outcomeLaw C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := μ.1) μ.2))
                (fun ω : OutcomeSeq C =>
                  chosenCollege C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2) ω = some c) =
              (Mseq C).aggregateDemand
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2) c)
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_total :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity =
          totalSupply)
    (hcapacity_open_bound :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1),
          0 < (Mseq C).capacity c ∧
            (Mseq C).capacity c < alpha / ((C + 1 : ℕ) : ℝ))
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          ∃ largeIntervalEvent smallMatchedIntervalEvent :
              ∀ C : ℕ,
                { μ : (Mseq C).Matching // (Mseq C).Stable μ } →
                  OutcomeSeq C → Prop,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
                lowerCutoff C ≤
                  cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2) c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ _μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow
                    (cutoffOut C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2)) ≤
                AppliedModelingLib.Matching.eventMass
                  (outcomeLaw C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))
                  (largeIntervalEvent C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              ∀ ω : OutcomeSeq C,
                largeIntervalEvent C μ ω →
                  AppliedModelingLib.Matching.chosenInActive
                    (chosenCollege C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2))
                    (Finset.univ : Finset (Fin (C + 1))) ω) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              AppliedModelingLib.Matching.choiceMass
                  (outcomeLaw C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))
                  (chosenCollege C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C) -
                  epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar
                    (cutoffOut C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2)) ≤
                AppliedModelingLib.Matching.eventMass
                  (outcomeLaw C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))
                  (smallMatchedIntervalEvent C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              ∀ ω : OutcomeSeq C,
                smallMatchedIntervalEvent C μ ω →
                  AppliedModelingLib.Matching.chosenInActive
                    (chosenCollege C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    ω)) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          |cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2)) -
            totalSupply| < ε := by
  refine
    theorem2_uniformAmplification_source_clauses_of_fixed_alpha_iidProduct_selected_stable_cutoff_floor_index_split_local_probabilityEvent_aggregateDemand_endpoint_estimates_strict_derived
      Mseq Iseq Kseq noiseLaw hlong cutoffOut
      OutcomeSeq outcomeLaw chosenCollege
      houtcome_prob
      hchosen_singleton_measurable
      hsingleton_choiceMass_eq_aggregateDemand
      htotalSupply_lt_one hcapacity_total hcapacity_open_bound ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, largeIntervalEvent,
      smallMatchedIntervalEvent, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_lower, htail_floor, hlarge_interval_lower,
      hlarge_event_chosen, hlarge_endpoint_choice,
      hsmall_interval_lower, hsmall_event_chosen⟩
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff, largeIntervalEvent,
      smallMatchedIntervalEvent, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_lower, ?_, hlarge_interval_lower,
      hlarge_event_chosen, hlarge_endpoint_choice,
      hsmall_interval_lower, hsmall_event_chosen⟩
  filter_upwards [hcutoff_lower, htail_floor] with C hcutoffC htailC μ c hc
  exact
    le_trans
      (AppliedModelingLib.Probability.upperTailMass_antitone noiseLaw
        (sub_le_sub_right (hcutoffC μ c hc) vHigh))
      (htailC μ)

/--
Theorem 2 selected-stable source clauses from scalar endpoint estimates.

This is the direct appendix-algebra route at the selected A-L cutoff attached
to each stable matching.  It avoids asking for endpoint estimates at every
abstract market-clearing cutoff: the source package is stated only for the
selected stable-matching cutoff, while Lean derives total-supply
nonnegativity, alpha nonnegativity, capacity regularity, the ordered split,
the iid product bridge, and the long-tail endpoint gap.
-/
theorem theorem2_uniformAmplification_source_clauses_of_fixed_alpha_iidProduct_selected_stable_cutoff_floor_index_split_scalar_tail_market_capacity_paper_positive_capacity_source_endpoint_estimates_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_total :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity =
          totalSupply)
    (hcapacity_open_bound :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1),
          0 < (Mseq C).capacity c ∧
            (Mseq C).capacity c < alpha / ((C + 1 : ℕ) : ℝ))
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
                lowerCutoff C ≤
                  cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2) c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ _μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              (1 - epsilon) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                    vLow
                    (cutoffOut C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2)) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              AppliedModelingLib.Matching.activeCapacity
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  (Mseq C).capacity - epsilon ≤
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                  vHigh
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                    vStar
                    (cutoffOut C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2)) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                  (Mseq C).capacity)) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          |cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2)) -
            totalSupply| < ε := by
  have hcapacity_nonneg :
      ∀ᶠ C : ℕ in atTop,
        ∀ c : Fin (C + 1), 0 ≤ (Mseq C).capacity c := by
    filter_upwards [hcapacity_open_bound] with C hboundC c
    exact le_of_lt (hboundC c).1
  have halpha_nonneg : 0 ≤ alpha := by
    rcases hcapacity_open_bound.exists with ⟨C, hboundC⟩
    let c0 : Fin (C + 1) := ⟨0, Nat.succ_pos C⟩
    have hdiv_pos :
        0 < alpha / (((C + 1 : ℕ) : ℝ)) :=
      lt_trans (hboundC c0).1 (hboundC c0).2
    have hden_pos : 0 < (((C + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_pos C
    have hmul_pos :
        0 < (alpha / (((C + 1 : ℕ) : ℝ))) *
          (((C + 1 : ℕ) : ℝ)) :=
      mul_pos hdiv_pos hden_pos
    have hmul_eq :
        (alpha / (((C + 1 : ℕ) : ℝ))) *
            (((C + 1 : ℕ) : ℝ)) = alpha := by
      field_simp [ne_of_gt hden_pos]
    have halpha_pos : 0 < alpha := by
      rw [← hmul_eq]
      exact hmul_pos
    exact le_of_lt halpha_pos
  have htotalSupply_nonneg : 0 ≤ totalSupply := by
    rcases (hcapacity_total.and hcapacity_nonneg).exists with
      ⟨C, htotalC, hnonnegC⟩
    have hactive_nonneg :
        0 ≤ AppliedModelingLib.Matching.activeCapacity
          (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity := by
      unfold AppliedModelingLib.Matching.activeCapacity
      exact Finset.sum_nonneg (fun c _hc => hnonnegC c)
    simpa [htotalC] using hactive_nonneg
  refine theorem2_uniformAmplification_source_clauses ?_
  refine
    theorem2_uniformAmplification_of_fixed_alpha_iidProduct_cutoff_floor_index_split_source_endpoint_estimates_capacityRegular_strict_derived
      (Admissible := fun C : ℕ =>
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (noiseLaw := noiseLaw) (hlong := hlong)
      (cutoff := fun C μ =>
        cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))
      (capacity := fun C _μ => (Mseq C).capacity)
      (totalSupply := totalSupply) (alpha := alpha)
      htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_lower, htail_floor, hmass_upper,
      hlarge_endpoint, hsmall_capacity_lower⟩
  have hlarge_direct :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          totalSupply - alpha * epsilon - epsilon ≤
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
              vHigh
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2)) := by
    filter_upwards [hlarge_endpoint, hcapacity_total, hcapacity_open_bound] with
      C hlargeC htotalC hcapacityC μ
    have hcard :
        (((indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C).card) : ℝ) ≤
          epsilon * ((C + 1 : ℕ) : ℝ) :=
      le_trans
        (indexPrefixSmall_card_le_index
          (epsilonFloorSplitIndex epsilon C) C)
        (epsilonFloorSplitIndex_le epsilon C hepsilon.le)
    have hC_pos : 0 < (((C + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_pos C
    have hcap_le :
        ∀ c ∈ indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C,
          (Mseq C).capacity c ≤ alpha / ((C + 1 : ℕ) : ℝ) := by
      intro c _hc
      exact le_of_lt (hcapacityC c).2
    have hsmall_cap :
        AppliedModelingLib.Matching.activeCapacity
            (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
            (Mseq C).capacity ≤
          epsilon * alpha :=
      smallActiveSet_capacity_le_epsilon_mul_alpha
        (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
        (Mseq C).capacity hcard halpha_nonneg hC_pos hcap_le
    have htotal_lower :
        totalSupply ≤
          AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity := by
      rw [htotalC]
    have hlarge_cap :
        totalSupply - epsilon * alpha ≤
          AppliedModelingLib.Matching.activeCapacity
            (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
            (Mseq C).capacity :=
      AppliedModelingLib.Matching.activeCapacity_right_ge_totalLower_sub_leftUpper_of_partition
        (total := (Finset.univ : Finset (Fin (C + 1))))
        (left := indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
        (right := indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
        (Mseq C).capacity
        (indexPrefixSmall_union_indexSuffixLarge
          (epsilonFloorSplitIndex epsilon C) C)
        (indexPrefixSmall_disjoint_indexSuffixLarge
          (epsilonFloorSplitIndex epsilon C) C)
        htotal_lower hsmall_cap
    have hlarge_cap' :
        totalSupply - alpha * epsilon ≤
          AppliedModelingLib.Matching.activeCapacity
            (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
            (Mseq C).capacity := by
      simpa [mul_comm] using hlarge_cap
    linarith [hlarge_cap', hlargeC μ]
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_lower, ?_, hmass_upper, hlarge_direct,
      ?_, hsmall_capacity_lower⟩
  · filter_upwards [hcutoff_lower, htail_floor] with C hcutoffC htailC μ c hc
    exact
      le_trans
        (AppliedModelingLib.Probability.upperTailMass_antitone noiseLaw
          (sub_le_sub_right (hcutoffC μ c hc) vHigh))
        (htailC μ)
  · filter_upwards [hcapacity_open_bound] with C hboundC μ
    intro c
    exact (hboundC c).2

/--
Eventual version of the PG24 large-firm interval step.  This is the form used
in the amplification appendix: after the endpoint supply estimates and
`lt-approx-F2` product comparison hold for all sufficiently large markets,
every intermediate value lies in the large-firm interval for all sufficiently
large markets.
-/
theorem theorem2_largeFirm_interval_eventually_of_endpoint_product_error
    {pLarge : ℕ → ℝ → ℝ} {vLow vHigh v S α ε σ : ℝ}
    (hp_mono : ∀ᶠ C : ℕ in atTop, Monotone (pLarge C))
    (hvLow : vLow ≤ v) (hvHigh : v ≤ vHigh)
    (hupper_low : ∀ᶠ C : ℕ in atTop, pLarge C vLow ≤ S + ε)
    (hlower_high : ∀ᶠ C : ℕ in atTop, S - (1 + α) * ε ≤ pLarge C vHigh)
    (hdiff :
      ∀ᶠ C : ℕ in atTop,
        pLarge C vHigh - pLarge C vLow ≤
          1 - Real.exp (-(2 * ε * σ))) :
    ∀ᶠ C : ℕ in atTop,
      S - (1 + α) * ε - (1 - Real.exp (-(2 * ε * σ))) ≤
          pLarge C v ∧
        pLarge C v ≤ S + ε + (1 - Real.exp (-(2 * ε * σ))) := by
  filter_upwards [hp_mono, hupper_low, hlower_high, hdiff] with
    C hmono hlow hhigh hgap
  exact
    theorem2_largeFirm_interval_of_endpoint_product_error
      (pLarge := pLarge C)
      hmono hvLow hvHigh hlow hhigh hgap

/--
Eventual large-firm source-window predicate from endpoint/product estimates.
-/
theorem theorem2_largeFirmSourceWindow_eventually_of_endpoint_product_error
    {pLarge : ℕ → ℝ → ℝ} {vLow vHigh v S α ε σ : ℝ}
    (hp_mono : ∀ᶠ C : ℕ in atTop, Monotone (pLarge C))
    (hvLow : vLow ≤ v) (hvHigh : v ≤ vHigh)
    (hupper_low : ∀ᶠ C : ℕ in atTop, pLarge C vLow ≤ S + ε)
    (hlower_high : ∀ᶠ C : ℕ in atTop, S - (1 + α) * ε ≤ pLarge C vHigh)
    (hdiff :
      ∀ᶠ C : ℕ in atTop,
        pLarge C vHigh - pLarge C vLow ≤
          1 - Real.exp (-(2 * ε * σ))) :
    ∀ᶠ C : ℕ in atTop,
      theorem2_largeFirmSourceWindow S α ε σ (pLarge C v) := by
  filter_upwards [hp_mono, hupper_low, hlower_high, hdiff] with
    C hmono hlow hhigh hgap
  exact
    theorem2_largeFirmSourceWindow_of_endpoint_product_error
      (pLarge := pLarge C)
      hmono hvLow hvHigh hlow hhigh hgap

/--
PG24 Theorem 2, final `C1/C2` decomposition algebra.  Once the large-college
probability is in the long-tail window and the small-college probability is
bounded by the capacity argument, the full affordability probability lies in
the source window from equation `equiv-lt`.
-/
theorem theorem2_full_interval_of_large_and_small_firm_bounds
    {pTotal pSmall pLarge : ℝ → ℝ}
    {v S α ε σ : ℝ}
    (hlarge :
      S - (1 + α) * ε - (1 - Real.exp (-(2 * ε * σ))) ≤
          pLarge v ∧
        pLarge v ≤ S + ε + (1 - Real.exp (-(2 * ε * σ))))
    (hsmall :
      pSmall v ≤
        α * Real.sqrt ε /
          (1 - S - ε - (1 - Real.exp (-(2 * ε * σ)))))
    (hlarge_le_total : pLarge v ≤ pTotal v)
    (htotal_le_sum : pTotal v ≤ pSmall v + pLarge v) :
    S - (1 + α) * ε - (1 - Real.exp (-(2 * ε * σ))) ≤
        pTotal v ∧
      pTotal v ≤
        S + ε + (1 - Real.exp (-(2 * ε * σ))) +
          α * Real.sqrt ε /
            (1 - S - ε - (1 - Real.exp (-(2 * ε * σ)))) := by
  constructor
  · exact le_trans hlarge.1 hlarge_le_total
  · linarith

/--
Eventual version of the PG24 final `C1/C2` decomposition.  Once the
large-firm interval, small-firm capacity error, and union/inclusion bounds all
hold for sufficiently large markets, the full probability lies in the source
window for sufficiently large markets.
-/
theorem theorem2_full_interval_eventually_of_large_and_small_firm_bounds
    {pTotal pSmall pLarge : ℕ → ℝ → ℝ}
    {v S α ε σ : ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        S - (1 + α) * ε - (1 - Real.exp (-(2 * ε * σ))) ≤
            pLarge C v ∧
          pLarge C v ≤ S + ε + (1 - Real.exp (-(2 * ε * σ))))
    (hsmall :
      ∀ᶠ C : ℕ in atTop,
        pSmall C v ≤
          α * Real.sqrt ε /
            (1 - S - ε - (1 - Real.exp (-(2 * ε * σ)))))
    (hlarge_le_total :
      ∀ᶠ C : ℕ in atTop, pLarge C v ≤ pTotal C v)
    (htotal_le_sum :
      ∀ᶠ C : ℕ in atTop, pTotal C v ≤ pSmall C v + pLarge C v) :
    ∀ᶠ C : ℕ in atTop,
      S - (1 + α) * ε - (1 - Real.exp (-(2 * ε * σ))) ≤
          pTotal C v ∧
        pTotal C v ≤
          S + ε + (1 - Real.exp (-(2 * ε * σ))) +
            α * Real.sqrt ε /
              (1 - S - ε - (1 - Real.exp (-(2 * ε * σ)))) := by
  filter_upwards [hlarge, hsmall, hlarge_le_total, htotal_le_sum] with
    C hlargeC hsmallC hleC hsumC
  exact
    theorem2_full_interval_of_large_and_small_firm_bounds
      (pTotal := pTotal C) (pSmall := pSmall C) (pLarge := pLarge C)
      hlargeC hsmallC hleC hsumC

/--
Theorem 3 coalition attenuation target.  The first predicate is the event that
low values cannot afford the large coalition subset; the second is the event
that high values can afford the coalition.
-/
structure Theorem3CoalitionAttenuationConclusion
    (lowBlocked highAdmitted : ℕ → ℝ → Prop) (threshold : ℝ) : Prop where
  low_values_eventually_blocked :
    ∀ v, v < threshold → ∀ᶠ C : ℕ in atTop, lowBlocked C v
  high_values_eventually_admitted :
    ∀ v, threshold < v → ∀ᶠ C : ℕ in atTop, highAdmitted C v

/--
Source-shaped Theorem 3 coalition attenuation target.  The paper states the
low- and high-value clauses with margins around the threshold: low values
below `v' - epsilon` are blocked from the large subset, while high values
above `v' + epsilon` are admitted by the coalition.
-/
structure Theorem3CoalitionAttenuationEpsilonConclusion
    (lowBlocked highAdmitted : ℕ → ℝ → Prop)
    (epsilon threshold : ℝ) : Prop where
  low_values_eventually_blocked :
    ∀ v, v < threshold - epsilon → ∀ᶠ C : ℕ in atTop, lowBlocked C v
  high_values_eventually_admitted :
    ∀ v, threshold + epsilon < v → ∀ᶠ C : ℕ in atTop, highAdmitted C v

/-- Theorem 3 unpacked into the two source-style eventual event clauses. -/
theorem theorem3_coalition_attenuation_eventually_bounds
    {lowBlocked highAdmitted : ℕ → ℝ → Prop} {threshold : ℝ}
    (h : Theorem3CoalitionAttenuationConclusion
      lowBlocked highAdmitted threshold) :
    (∀ v, v < threshold → ∀ᶠ C : ℕ in atTop, lowBlocked C v) ∧
    (∀ v, threshold < v → ∀ᶠ C : ℕ in atTop, highAdmitted C v) :=
  ⟨h.low_values_eventually_blocked, h.high_values_eventually_admitted⟩

/-- The source-shaped Theorem 3 target unpacked into its shifted clauses. -/
theorem theorem3_coalition_attenuation_epsilon_eventually_bounds
    {lowBlocked highAdmitted : ℕ → ℝ → Prop} {epsilon threshold : ℝ}
    (h : Theorem3CoalitionAttenuationEpsilonConclusion
      lowBlocked highAdmitted epsilon threshold) :
    (∀ v, v < threshold - epsilon →
      ∀ᶠ C : ℕ in atTop, lowBlocked C v) ∧
    (∀ v, threshold + epsilon < v →
      ∀ᶠ C : ℕ in atTop, highAdmitted C v) :=
  ⟨h.low_values_eventually_blocked, h.high_values_eventually_admitted⟩

/--
Source-shaped "large subset" certificate for the PG24 coalition theorems.
The paper states the subset condition as `|C'| / |C| > 1 - epsilon`.
-/
structure CoalitionLargeSubset {College : Type v}
    (coalition largeSubset : Finset College) (epsilon : ℝ) : Prop where
  subset : largeSubset ⊆ coalition
  coalition_card_pos : 0 < (coalition.card : ℝ)
  large_ratio : 1 - epsilon < (largeSubset.card : ℝ) / (coalition.card : ℝ)

/--
If a sorted prefix removes less than an `epsilon` fraction of an indexed
coalition, the remaining suffix is a large subset in the paper's sense.
-/
theorem coalitionLargeSubset_univ_of_prefix_fraction_lt
    {C k : ℕ} {epsilon : ℝ}
    (hprefix :
      ((indexPrefixSmall k C).card : ℝ) /
          (((Finset.univ : Finset (Fin (C + 1))).card : ℝ)) < epsilon) :
    CoalitionLargeSubset
      (Finset.univ : Finset (Fin (C + 1))) (indexSuffixLarge k C) epsilon := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro c _hc
    simp
  · simpa using (show 0 < (((C + 1 : ℕ) : ℝ)) by
      exact_mod_cast Nat.succ_pos C)
  · have hcard_nat :
        (Finset.univ : Finset (Fin (C + 1))).card =
          (indexPrefixSmall k C).card + (indexSuffixLarge k C).card := by
      have h :=
        congrArg Finset.card (indexPrefixSmall_union_indexSuffixLarge k C)
      rw [Finset.card_union_of_disjoint
        (indexPrefixSmall_disjoint_indexSuffixLarge k C)] at h
      exact h
    have hden_pos :
        0 < (((Finset.univ : Finset (Fin (C + 1))).card : ℝ)) := by
      simpa using (show 0 < (((C + 1 : ℕ) : ℝ)) by
        exact_mod_cast Nat.succ_pos C)
    have hden_ne :
        (((Finset.univ : Finset (Fin (C + 1))).card : ℝ)) ≠ 0 :=
      ne_of_gt hden_pos
    have hcard_real :
        (((Finset.univ : Finset (Fin (C + 1))).card : ℝ)) =
          ((indexPrefixSmall k C).card : ℝ) +
            ((indexSuffixLarge k C).card : ℝ) := by
      exact_mod_cast hcard_nat
    have hratio :
        ((indexSuffixLarge k C).card : ℝ) /
            (((Finset.univ : Finset (Fin (C + 1))).card : ℝ)) =
          1 -
            ((indexPrefixSmall k C).card : ℝ) /
              (((Finset.univ : Finset (Fin (C + 1))).card : ℝ)) := by
      field_simp [hden_ne]
      linarith
    calc
      1 - epsilon
          < 1 - ((indexPrefixSmall k C).card : ℝ) /
              (((Finset.univ : Finset (Fin (C + 1))).card : ℝ)) := by
            linarith
      _ = ((indexSuffixLarge k C).card : ℝ) /
          (((Finset.univ : Finset (Fin (C + 1))).card : ℝ)) :=
            hratio.symm

/--
Deleting the first `floor((epsilon/2) * (C+1))` indexed colleges leaves a
large subset with tolerance `epsilon`.
-/
theorem coalitionLargeSubset_univ_indexSuffixLarge_epsilonHalf
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon) (C : ℕ) :
    CoalitionLargeSubset
      (Finset.univ : Finset (Fin (C + 1)))
      (indexSuffixLarge (epsilonFloorSplitIndex (epsilon / 2) C) C)
      epsilon := by
  refine coalitionLargeSubset_univ_of_prefix_fraction_lt ?_
  have hden_eq :
      (((Finset.univ : Finset (Fin (C + 1))).card : ℝ)) =
        (((C + 1 : ℕ) : ℝ)) := by
    simp
  have hden_pos : 0 < (((C + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos C
  have hprefix_card :
      ((indexPrefixSmall (epsilonFloorSplitIndex (epsilon / 2) C) C).card : ℝ) ≤
        (epsilon / 2) * (((C + 1 : ℕ) : ℝ)) := by
    exact le_trans
      (indexPrefixSmall_card_le_index
        (epsilonFloorSplitIndex (epsilon / 2) C) C)
      (epsilonFloorSplitIndex_le (epsilon / 2) C (by linarith))
  have hprefix_div_le :
      ((indexPrefixSmall (epsilonFloorSplitIndex (epsilon / 2) C) C).card : ℝ) /
          (((C + 1 : ℕ) : ℝ)) ≤
        epsilon / 2 :=
    (div_le_iff₀ hden_pos).2 hprefix_card
  have hprefix_div_lt :
      ((indexPrefixSmall (epsilonFloorSplitIndex (epsilon / 2) C) C).card : ℝ) /
          (((C + 1 : ℕ) : ℝ)) <
        epsilon := by
    linarith
  simpa [hden_eq] using hprefix_div_lt

/--
The cutoff block obtained by deleting exactly the coordinates below a scalar
floor.  Unlike the sorted suffix, this block is defined semantically from the
cutoff vector itself, so its low-endpoint floor does not need a relabeling or
sorted-index premise.
-/
noncomputable def nonLowCutoffIndexSet {n : ℕ}
    (cutoff : Fin n → ℝ) (floor : ℝ) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)) \ lowCutoffIndexSet cutoff floor

/-- Every member of the non-low cutoff block is above the scalar floor. -/
theorem floor_le_of_mem_nonLowCutoffIndexSet
    {n : ℕ} {cutoff : Fin n → ℝ} {floor : ℝ}
    {c : Fin n} (hc : c ∈ nonLowCutoffIndexSet cutoff floor) :
    floor ≤ cutoff c := by
  classical
  rw [nonLowCutoffIndexSet, Finset.mem_sdiff] at hc
  exact le_of_not_gt (by
    intro hlt
    exact hc.2 (by
      simp [lowCutoffIndexSet, hlt]))

/--
If at most an `epsilon / 2` prefix-sized set of coordinates lie below the
floor, deleting those below-floor coordinates leaves a large subset in the
paper's coalition sense.
-/
theorem coalitionLargeSubset_univ_nonLowCutoffIndexSet_of_lowCutoff_card_le
    {C : ℕ} {epsilon : ℝ} (hepsilon_pos : 0 < epsilon)
    {cutoff : Fin (C + 1) → ℝ} {floor : ℝ}
    (hcard :
      (lowCutoffIndexSet cutoff floor).card ≤
        epsilonFloorSplitIndex (epsilon / 2) C) :
    CoalitionLargeSubset
      (Finset.univ : Finset (Fin (C + 1)))
      (nonLowCutoffIndexSet cutoff floor)
      epsilon := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro c _hc
    simp
  · simpa using (show 0 < (((C + 1 : ℕ) : ℝ)) by
      exact_mod_cast Nat.succ_pos C)
  · have hden_eq :
        (((Finset.univ : Finset (Fin (C + 1))).card : ℝ)) =
          (((C + 1 : ℕ) : ℝ)) := by
      simp
    have hden_pos :
        0 < (((Finset.univ : Finset (Fin (C + 1))).card : ℝ)) := by
      simpa [hden_eq] using (show 0 < (((C + 1 : ℕ) : ℝ)) by
        exact_mod_cast Nat.succ_pos C)
    have hden_ne :
        (((Finset.univ : Finset (Fin (C + 1))).card : ℝ)) ≠ 0 :=
      ne_of_gt hden_pos
    have hlow_subset :
        lowCutoffIndexSet cutoff floor ⊆
          (Finset.univ : Finset (Fin (C + 1))) := by
      intro c _hc
      simp
    have hcard_nat :
        (Finset.univ : Finset (Fin (C + 1))).card =
          (lowCutoffIndexSet cutoff floor).card +
            (nonLowCutoffIndexSet cutoff floor).card := by
      rw [nonLowCutoffIndexSet]
      have h :=
        Finset.card_sdiff_add_card_eq_card
          (s := lowCutoffIndexSet cutoff floor)
          (t := (Finset.univ : Finset (Fin (C + 1))))
          hlow_subset
      rw [add_comm] at h
      exact h.symm
    have hratio :
        ((nonLowCutoffIndexSet cutoff floor).card : ℝ) /
            (((Finset.univ : Finset (Fin (C + 1))).card : ℝ)) =
          1 -
            ((lowCutoffIndexSet cutoff floor).card : ℝ) /
              (((Finset.univ : Finset (Fin (C + 1))).card : ℝ)) := by
      have hcard_real :
          (((Finset.univ : Finset (Fin (C + 1))).card : ℝ)) =
            ((lowCutoffIndexSet cutoff floor).card : ℝ) +
              ((nonLowCutoffIndexSet cutoff floor).card : ℝ) := by
        exact_mod_cast hcard_nat
      field_simp [hden_ne]
      linarith
    have hsplit_card :
        ((epsilonFloorSplitIndex (epsilon / 2) C : ℕ) : ℝ) ≤
          (epsilon / 2) * (((C + 1 : ℕ) : ℝ)) :=
      epsilonFloorSplitIndex_le (epsilon / 2) C (by linarith)
    have hlow_div_le :
        ((lowCutoffIndexSet cutoff floor).card : ℝ) /
            (((Finset.univ : Finset (Fin (C + 1))).card : ℝ)) ≤
          epsilon / 2 := by
      rw [hden_eq]
      refine (div_le_iff₀ ?_).2 ?_
      · exact_mod_cast Nat.succ_pos C
      · exact le_trans (by exact_mod_cast hcard) hsplit_card
    have hlow_div_lt :
        ((lowCutoffIndexSet cutoff floor).card : ℝ) /
            (((Finset.univ : Finset (Fin (C + 1))).card : ℝ)) < epsilon := by
      linarith
    calc
      1 - epsilon
          < 1 -
              ((lowCutoffIndexSet cutoff floor).card : ℝ) /
                (((Finset.univ : Finset (Fin (C + 1))).card : ℝ)) := by
            linarith
      _ = ((nonLowCutoffIndexSet cutoff floor).card : ℝ) /
          (((Finset.univ : Finset (Fin (C + 1))).card : ℝ)) :=
            hratio.symm

/--
The semantic non-low block has the same coarse cardinality bound as any subset
of all `C + 1` colleges, so the same half-rate union-bound estimate applies.
-/
theorem nonLowCutoffIndexSet_card_mul_tailRate_lt_of_tailRate_le_half_div
    {C : ℕ} {epsilon tailRate : ℝ} {cutoff : Fin (C + 1) → ℝ}
    {floor : ℝ}
    (hepsilon_pos : 0 < epsilon)
    (htail :
      tailRate ≤ epsilon / (2 * (((C + 1 : ℕ) : ℝ)))) :
    ((nonLowCutoffIndexSet cutoff floor).card : ℝ) * tailRate < epsilon := by
  have hcard_nonneg :
      0 ≤ ((nonLowCutoffIndexSet cutoff floor).card : ℝ) := by
    positivity
  have hcard_le :
      ((nonLowCutoffIndexSet cutoff floor).card : ℝ) ≤
        (((C + 1 : ℕ) : ℝ)) := by
    have hnat :
        (nonLowCutoffIndexSet cutoff floor).card ≤ C + 1 := by
      simpa [Fintype.card_fin] using
        (Finset.card_le_univ
          (s := nonLowCutoffIndexSet cutoff floor))
    exact_mod_cast hnat
  have hn_pos : 0 < (((C + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos C
  have hmul_le_tail :
      ((nonLowCutoffIndexSet cutoff floor).card : ℝ) * tailRate ≤
        ((nonLowCutoffIndexSet cutoff floor).card : ℝ) *
          (epsilon / (2 * (((C + 1 : ℕ) : ℝ)))) :=
    mul_le_mul_of_nonneg_left htail hcard_nonneg
  have hmul_le_card :
      ((nonLowCutoffIndexSet cutoff floor).card : ℝ) *
          (epsilon / (2 * (((C + 1 : ℕ) : ℝ)))) ≤
        (((C + 1 : ℕ) : ℝ)) *
          (epsilon / (2 * (((C + 1 : ℕ) : ℝ)))) := by
    exact mul_le_mul_of_nonneg_right hcard_le (by positivity)
  have hhalf :
      (((C + 1 : ℕ) : ℝ)) *
          (epsilon / (2 * (((C + 1 : ℕ) : ℝ)))) =
        epsilon / 2 := by
    field_simp [ne_of_gt hn_pos]
  exact
    lt_of_le_of_lt
      (le_trans hmul_le_tail (le_trans hmul_le_card hhalf.le))
      (by linarith)

/--
The suffix-cardinality factor is small when the per-college tail rate is at
most `epsilon / (2 * (C+1))`.
-/
theorem indexSuffixLarge_card_mul_tailRate_lt_of_tailRate_le_half_div
    {C : ℕ} {epsilon tailRate : ℝ}
    (hepsilon_pos : 0 < epsilon)
    (htail :
      tailRate ≤ epsilon / (2 * (((C + 1 : ℕ) : ℝ)))) :
    ((indexSuffixLarge (epsilonFloorSplitIndex (epsilon / 2) C) C).card : ℝ) *
        tailRate < epsilon := by
  have hcard_nonneg :
      0 ≤
        ((indexSuffixLarge (epsilonFloorSplitIndex (epsilon / 2) C) C).card : ℝ) :=
    by positivity
  have hcard_le :
      ((indexSuffixLarge (epsilonFloorSplitIndex (epsilon / 2) C) C).card : ℝ) ≤
        (((C + 1 : ℕ) : ℝ)) := by
    have hnat :
        (indexSuffixLarge (epsilonFloorSplitIndex (epsilon / 2) C) C).card ≤
          C + 1 := by
      simpa [Fintype.card_fin] using
        (Finset.card_le_univ
          (s := indexSuffixLarge (epsilonFloorSplitIndex (epsilon / 2) C) C))
    exact_mod_cast hnat
  have hn_pos : 0 < (((C + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos C
  have htail_bound_nonneg :
      0 ≤ epsilon / (2 * (((C + 1 : ℕ) : ℝ))) := by
    positivity
  have hmul_le_tail :
      ((indexSuffixLarge (epsilonFloorSplitIndex (epsilon / 2) C) C).card : ℝ) *
          tailRate ≤
        ((indexSuffixLarge (epsilonFloorSplitIndex (epsilon / 2) C) C).card : ℝ) *
          (epsilon / (2 * (((C + 1 : ℕ) : ℝ)))) :=
    mul_le_mul_of_nonneg_left htail hcard_nonneg
  have hmul_le_card :
      ((indexSuffixLarge (epsilonFloorSplitIndex (epsilon / 2) C) C).card : ℝ) *
          (epsilon / (2 * (((C + 1 : ℕ) : ℝ)))) ≤
        (((C + 1 : ℕ) : ℝ)) *
          (epsilon / (2 * (((C + 1 : ℕ) : ℝ)))) :=
    mul_le_mul_of_nonneg_right hcard_le htail_bound_nonneg
  have hhalf :
      (((C + 1 : ℕ) : ℝ)) *
          (epsilon / (2 * (((C + 1 : ℕ) : ℝ)))) =
        epsilon / 2 := by
    field_simp [ne_of_gt hn_pos]
  calc
    ((indexSuffixLarge (epsilonFloorSplitIndex (epsilon / 2) C) C).card : ℝ) *
        tailRate
        ≤ ((indexSuffixLarge (epsilonFloorSplitIndex (epsilon / 2) C) C).card : ℝ) *
            (epsilon / (2 * (((C + 1 : ℕ) : ℝ)))) := hmul_le_tail
    _ ≤ (((C + 1 : ℕ) : ℝ)) *
          (epsilon / (2 * (((C + 1 : ℕ) : ℝ)))) := hmul_le_card
    _ = epsilon / 2 := hhalf
    _ < epsilon := by linarith

/--
PG24 Theorem 3 source-shaped witness: for a large subset `C'` of a coalition
`C`, low values cannot afford `C'`, while high values can afford the full
coalition `C`.
-/
structure Theorem3CoalitionAttenuationWitness {College : Type v}
    (coalition largeSubset : Finset College)
    (affordProb : ℝ → Finset College → ℝ)
    (epsilon threshold : ℝ) : Prop where
  large_subset : CoalitionLargeSubset coalition largeSubset epsilon
  low_values_blocked :
    ∀ v, v < threshold - epsilon → affordProb v largeSubset < epsilon
  high_values_admitted :
    ∀ v, threshold + epsilon < v → 1 - epsilon < affordProb v coalition

/--
Theorem 3 high-value transfer from the subset statement used in the proof to
the full-coalition statement in the theorem.  The source proof notes this via
monotonicity: affording a college in `C'` implies affording a college in `C`.
-/
theorem theorem3_coalitionAttenuationWitness_of_subset_high_values
    {College : Type v} {coalition largeSubset : Finset College}
    {affordProb : ℝ → Finset College → ℝ} {epsilon threshold : ℝ}
    (hlarge : CoalitionLargeSubset coalition largeSubset epsilon)
    (hlow :
      ∀ v, v < threshold - epsilon → affordProb v largeSubset < epsilon)
    (hhigh_subset :
      ∀ v, threshold + epsilon < v → 1 - epsilon < affordProb v largeSubset)
    (hmono :
      ∀ v, affordProb v largeSubset ≤ affordProb v coalition) :
    Theorem3CoalitionAttenuationWitness
      coalition largeSubset affordProb epsilon threshold := by
  refine ⟨hlarge, hlow, ?_⟩
  intro v hv
  exact lt_of_lt_of_le (hhigh_subset v hv) (hmono v)

/--
Theorem 3 low-value endpoint bridge: monotonicity in the student value turns
one endpoint inequality at `threshold - epsilon` into the full low-value
blocked clause.
-/
theorem theorem3_low_values_blocked_of_monotone_endpoint_bound
    {College : Type v} {largeSubset : Finset College}
    {affordProb : ℝ → Finset College → ℝ} {epsilon threshold : ℝ}
    (hp_mono : Monotone (fun v => affordProb v largeSubset))
    (hlow_endpoint : affordProb (threshold - epsilon) largeSubset < epsilon) :
    ∀ v, v < threshold - epsilon → affordProb v largeSubset < epsilon := by
  intro v hv
  exact lt_of_le_of_lt (hp_mono (le_of_lt hv)) hlow_endpoint

/--
Theorem 3 high-value endpoint bridge: monotonicity in the student value turns
one endpoint inequality at `threshold + epsilon` into the full high-value
admitted clause.
-/
theorem theorem3_high_values_admitted_of_monotone_endpoint_bound
    {College : Type v} {coalition : Finset College}
    {affordProb : ℝ → Finset College → ℝ} {epsilon threshold : ℝ}
    (hp_mono : Monotone (fun v => affordProb v coalition))
    (hhigh_endpoint : 1 - epsilon < affordProb (threshold + epsilon) coalition) :
    ∀ v, threshold + epsilon < v → 1 - epsilon < affordProb v coalition := by
  intro v hv
  exact lt_of_lt_of_le hhigh_endpoint (hp_mono (le_of_lt hv))

/--
Theorem 3 source witness from endpoint estimates.  The remaining source work
is reduced to the large-subset condition, monotonicity of affordability in
student value, and the two endpoint inequalities around the threshold.
-/
theorem theorem3_coalitionAttenuationWitness_of_monotone_endpoint_bounds
    {College : Type v} {coalition largeSubset : Finset College}
    {affordProb : ℝ → Finset College → ℝ} {epsilon threshold : ℝ}
    (hlarge : CoalitionLargeSubset coalition largeSubset epsilon)
    (hmono_large : Monotone (fun v => affordProb v largeSubset))
    (hmono_coalition : Monotone (fun v => affordProb v coalition))
    (hlow_endpoint : affordProb (threshold - epsilon) largeSubset < epsilon)
    (hhigh_endpoint : 1 - epsilon < affordProb (threshold + epsilon) coalition) :
    Theorem3CoalitionAttenuationWitness
      coalition largeSubset affordProb epsilon threshold := by
  refine ⟨hlarge, ?_, ?_⟩
  · exact theorem3_low_values_blocked_of_monotone_endpoint_bound
      hmono_large hlow_endpoint
  · exact theorem3_high_values_admitted_of_monotone_endpoint_bound
      hmono_coalition hhigh_endpoint

/--
Theorem 3 source clauses unpacked from the coalition witness: the chosen
subset is large, low values have affordability probability below `epsilon`
for `C'`, and high values have affordability probability above `1 - epsilon`
for the full coalition.
-/
theorem theorem3_coalitionAttenuationWitness_source_clauses
    {College : Type v} {coalition largeSubset : Finset College}
    {affordProb : ℝ → Finset College → ℝ} {epsilon threshold : ℝ}
    (h :
      Theorem3CoalitionAttenuationWitness
        coalition largeSubset affordProb epsilon threshold) :
    CoalitionLargeSubset coalition largeSubset epsilon ∧
      (∀ v, v < threshold - epsilon → affordProb v largeSubset < epsilon) ∧
      (∀ v, threshold + epsilon < v → 1 - epsilon < affordProb v coalition) :=
  ⟨h.large_subset, h.low_values_blocked, h.high_values_admitted⟩

/--
Indexed source-shaped Theorem 3 witness.  This combines the paper's large
subset condition with the two shifted affordability clauses for growing
coalition size.
-/
structure Theorem3CoalitionAttenuationEpsilonWitnessConclusion
    {College : ℕ → Type v}
    (coalition largeSubset : ∀ C : ℕ, Finset (College C))
    (affordProb : ∀ C : ℕ, ℝ → Finset (College C) → ℝ)
    (epsilon threshold : ℝ) : Prop where
  large_subset_eventually :
    ∀ᶠ C : ℕ in atTop,
      CoalitionLargeSubset (coalition C) (largeSubset C) epsilon
  low_values_eventually_blocked :
    ∀ v, v < threshold - epsilon →
      ∀ᶠ C : ℕ in atTop, affordProb C v (largeSubset C) < epsilon
  high_values_eventually_admitted :
    ∀ v, threshold + epsilon < v →
      ∀ᶠ C : ℕ in atTop, 1 - epsilon < affordProb C v (coalition C)

/--
Uniform source-shaped Theorem 3 witness over a family of admissible
economy/stable-matching/coalition instances at each market size.  This is the
paper's "for every sufficiently large coalition in every stable matching"
quantifier shape, with the chosen threshold and large subset allowed to depend
on the admissible instance.
-/
structure Theorem3CoalitionAttenuationUniformWitnessConclusion
    {College : ℕ → Type v} {Admissible : ℕ → Type u}
    (coalition largeSubset :
      ∀ C : ℕ, Admissible C → Finset (College C))
    (affordProb :
      ∀ C : ℕ, Admissible C → ℝ → Finset (College C) → ℝ)
    (epsilon : ℝ) (threshold : ∀ C : ℕ, Admissible C → ℝ) : Prop where
  large_subset_eventually :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon
  low_values_eventually_blocked :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C, ∀ v : ℝ,
        v < threshold C a - epsilon →
          affordProb C a v (largeSubset C a) < epsilon
  high_values_eventually_admitted :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C, ∀ v : ℝ,
        threshold C a + epsilon < v →
          1 - epsilon < affordProb C a v (coalition C a)

/--
Uniform Theorem 3 witness from endpoint estimates.  Compared with the
sequence-shaped witness, every eventual condition is required uniformly for
all admissible instances at the same market size.
-/
theorem theorem3_coalitionAttenuationUniformWitness_of_eventual_monotone_endpoint_bounds
    {College : ℕ → Type v} {Admissible : ℕ → Type u}
    {coalition largeSubset :
      ∀ C : ℕ, Admissible C → Finset (College C)}
    {affordProb :
      ∀ C : ℕ, Admissible C → ℝ → Finset (College C) → ℝ}
    {epsilon : ℝ} {threshold : ∀ C : ℕ, Admissible C → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon)
    (hmono_large :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          Monotone (fun v => affordProb C a v (largeSubset C a)))
    (hmono_coalition :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          Monotone (fun v => affordProb C a v (coalition C a)))
    (hlow_endpoint :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          affordProb C a (threshold C a - epsilon) (largeSubset C a) <
            epsilon)
    (hhigh_endpoint :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - epsilon <
            affordProb C a (threshold C a + epsilon) (coalition C a)) :
    Theorem3CoalitionAttenuationUniformWitnessConclusion
      coalition largeSubset affordProb epsilon threshold := by
  refine ⟨hlarge, ?_, ?_⟩
  · filter_upwards [hmono_large, hlow_endpoint] with C hmonoC hlowC
    intro a v hv
    exact
      theorem3_low_values_blocked_of_monotone_endpoint_bound
        (largeSubset := largeSubset C a)
        (affordProb := affordProb C a)
        (epsilon := epsilon) (threshold := threshold C a)
        (hmonoC a) (hlowC a) v hv
  · filter_upwards [hmono_coalition, hhigh_endpoint] with C hmonoC hhighC
    intro a v hv
    exact
      theorem3_high_values_admitted_of_monotone_endpoint_bound
        (coalition := coalition C a)
        (affordProb := affordProb C a)
        (epsilon := epsilon) (threshold := threshold C a)
        (hmonoC a) (hhighC a) v hv

/--
Uniform concrete iid-product cutoff specialization of the Theorem 3
coalition witness.  Value monotonicity and the transfer from the large subset
to the full coalition are derived from cutoff-affordance monotonicity.
-/
theorem theorem3_coalitionAttenuationUniformWitness_of_iidProduct_cutoff_subset_endpoint_bounds
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {Admissible : ℕ → Type u}
    {coalition largeSubset :
      ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    {cutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ}
    {epsilon : ℝ} {threshold : ∀ C : ℕ, Admissible C → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon)
    (hlow_endpoint :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (largeSubset C a) (threshold C a - epsilon) (cutoff C a) <
            epsilon)
    (hhigh_subset_endpoint :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - epsilon <
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) (threshold C a + epsilon) (cutoff C a)) :
    Theorem3CoalitionAttenuationUniformWitnessConclusion
      coalition largeSubset
      (fun C : ℕ => fun a : Admissible C => fun v : ℝ =>
        fun active : Finset (Fin (C + 1)) =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            active v (cutoff C a))
      epsilon threshold := by
  have hmono_large :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          Monotone (fun v =>
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) v (cutoff C a)) := by
    filter_upwards with C
    intro a v w hvw
    exact
      cutoffAffordanceProbability_mono_value
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) hvw
  have hmono_coalition :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          Monotone (fun v =>
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (coalition C a) v (cutoff C a)) := by
    filter_upwards with C
    intro a v w hvw
    exact
      cutoffAffordanceProbability_mono_value
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) hvw
  have hhigh_coalition :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - epsilon <
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (coalition C a) (threshold C a + epsilon) (cutoff C a) := by
    filter_upwards [hlarge, hhigh_subset_endpoint] with C hlargeC hhighC a
    exact
      lt_of_lt_of_le (hhighC a)
        (cutoffAffordanceProbability_mono_active
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (hlargeC a).subset)
  exact
    theorem3_coalitionAttenuationUniformWitness_of_eventual_monotone_endpoint_bounds
      hlarge hmono_large hmono_coalition hlow_endpoint hhigh_coalition

/--
Uniform concrete iid-product Theorem 3 over admissible instances carrying
selected stable matchings.  The A-L bridge supplies the market-clearing cutoff
for each selected stable matching, and endpoint estimates stated for all
market-clearing cutoffs are specialized uniformly over admissible instances.
-/
theorem theorem3_coalitionAttenuationUniformWitness_of_iidProduct_stable_cutoff_subset_endpoint_bounds
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {coalition largeSubset :
      ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon : ℝ} {threshold : ∀ C : ℕ, Admissible C → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon)
    (hlow_endpoint :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) (threshold C a - epsilon)
              (cutoffOut C P) < epsilon)
    (hhigh_subset_endpoint :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
            1 - epsilon <
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) (threshold C a + epsilon)
                (cutoffOut C P)) :
    Theorem3CoalitionAttenuationUniformWitnessConclusion
      coalition largeSubset
      (fun C : ℕ => fun a : Admissible C => fun v : ℝ =>
        fun active : Finset (Fin (C + 1)) =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            active v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2)))
      epsilon threshold := by
  have hmc :
      ∀ C : ℕ, ∀ a : Admissible C,
        (Mseq C).MarketClearing
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C a).1) (selected C a).2) := by
    intro C a
    exact
      (Iseq C).marketClearingCutoffOfStable_marketClearing
        (μ := (selected C a).1) (selected C a).2
  refine
    theorem3_coalitionAttenuationUniformWitness_of_iidProduct_cutoff_subset_endpoint_bounds
      (noiseLaw := noiseLaw)
      (coalition := coalition)
      (largeSubset := largeSubset)
      (cutoff := fun C : ℕ => fun a : Admissible C =>
        cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C a).1) (selected C a).2))
      (epsilon := epsilon)
      (threshold := threshold)
      hlarge ?_ ?_
  · filter_upwards [hlow_endpoint] with C hC a
    exact hC a _ (hmc C a)
  · filter_upwards [hhigh_subset_endpoint] with C hC a
    exact hC a _ (hmc C a)

/--
Uniform concrete iid-product Theorem 3 over admissible selected stable
matchings, with endpoint estimates stated only at the selected A-L cutoff.
-/
theorem theorem3_coalitionAttenuationUniformWitness_of_iidProduct_selected_stable_cutoff_subset_endpoint_bounds
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {coalition largeSubset :
      ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon : ℝ} {threshold : ∀ C : ℕ, Admissible C → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon)
    (hlow_endpoint :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (largeSubset C a) (threshold C a - epsilon)
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2)) <
            epsilon)
    (hhigh_subset_endpoint :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - epsilon <
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) (threshold C a + epsilon)
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2))) :
    Theorem3CoalitionAttenuationUniformWitnessConclusion
      coalition largeSubset
      (fun C : ℕ => fun a : Admissible C => fun v : ℝ =>
        fun active : Finset (Fin (C + 1)) =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            active v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2)))
      epsilon threshold :=
  theorem3_coalitionAttenuationUniformWitness_of_iidProduct_cutoff_subset_endpoint_bounds
    (noiseLaw := noiseLaw)
    (coalition := coalition)
    (largeSubset := largeSubset)
    (cutoff := fun C : ℕ => fun a : Admissible C =>
      cutoffOut C
        ((Iseq C).marketClearingCutoffOfStable
          (μ := (selected C a).1) (selected C a).2))
    (epsilon := epsilon)
    (threshold := threshold)
    hlarge hlow_endpoint hhigh_subset_endpoint

/--
Uniform Theorem 3 source clauses unpacked from the admissible-instance
witness.  This exposes the paper's three clauses directly: eventually large
subsets, low values cannot afford the large subset, and high values can afford
the full coalition.
-/
theorem theorem3_coalitionAttenuationUniformWitness_source_clauses
    {College : ℕ → Type v} {Admissible : ℕ → Type u}
    {coalition largeSubset :
      ∀ C : ℕ, Admissible C → Finset (College C)}
    {affordProb :
      ∀ C : ℕ, Admissible C → ℝ → Finset (College C) → ℝ}
    {epsilon : ℝ} {threshold : ∀ C : ℕ, Admissible C → ℝ}
    (h :
      Theorem3CoalitionAttenuationUniformWitnessConclusion
        coalition largeSubset affordProb epsilon threshold) :
    (∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v : ℝ,
          v < threshold C a - epsilon →
            affordProb C a v (largeSubset C a) < epsilon) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v : ℝ,
          threshold C a + epsilon < v →
            1 - epsilon < affordProb C a v (coalition C a)) :=
  ⟨h.large_subset_eventually,
    h.low_values_eventually_blocked,
    h.high_values_eventually_admitted⟩

/--
Uniform Theorem 3 existential source clauses.  This is the exact paper-facing
shape after a proof route has selected the large subset and threshold for each
admissible stable-matching instance.
-/
theorem theorem3_coalitionAttenuationUniformWitness_existential_source_clauses
    {College : ℕ → Type v} {Admissible : ℕ → Type u}
    {coalition largeSubset :
      ∀ C : ℕ, Admissible C → Finset (College C)}
    {affordProb :
      ∀ C : ℕ, Admissible C → ℝ → Finset (College C) → ℝ}
    {epsilon : ℝ} {threshold : ∀ C : ℕ, Admissible C → ℝ}
    (h :
      Theorem3CoalitionAttenuationUniformWitnessConclusion
        coalition largeSubset affordProb epsilon threshold) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ threshold' : ℝ, ∃ largeSubset' : Finset (College C),
          CoalitionLargeSubset (coalition C a) largeSubset' epsilon ∧
            (∀ v : ℝ, v < threshold' - epsilon →
              affordProb C a v largeSubset' < epsilon) ∧
            (∀ v : ℝ, threshold' + epsilon < v →
              1 - epsilon < affordProb C a v (coalition C a)) := by
  filter_upwards
    [h.large_subset_eventually, h.low_values_eventually_blocked,
      h.high_values_eventually_admitted] with
    C hlargeC hlowC hhighC a
  exact ⟨threshold C a, largeSubset C a, hlargeC a, hlowC a, hhighC a⟩

/--
Uniform selected-stable Theorem 3 source clauses from endpoint estimates.
This composes the selected-stable cutoff endpoint route with the source-clause
projection, so the conclusion is stated directly for every admissible stable
matching instance.
-/
theorem theorem3_coalitionAttenuationUniformWitness_source_clauses_of_iidProduct_stable_cutoff_subset_endpoint_bounds
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {coalition largeSubset :
      ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon : ℝ} {threshold : ∀ C : ℕ, Admissible C → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon)
    (hlow_endpoint :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) (threshold C a - epsilon)
              (cutoffOut C P) < epsilon)
    (hhigh_subset_endpoint :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
            1 - epsilon <
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) (threshold C a + epsilon)
                (cutoffOut C P)) :
    (∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v : ℝ,
          v < threshold C a - epsilon →
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2)) <
              epsilon) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v : ℝ,
          threshold C a + epsilon < v →
            1 - epsilon <
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (coalition C a) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))) := by
  have h :=
    theorem3_coalitionAttenuationUniformWitness_of_iidProduct_stable_cutoff_subset_endpoint_bounds
      Mseq Iseq selected noiseLaw cutoffOut hlarge hlow_endpoint
      hhigh_subset_endpoint
  exact theorem3_coalitionAttenuationUniformWitness_source_clauses h

/--
Uniform selected-stable Theorem 3 source clauses from endpoint estimates
stated only at the selected A-L cutoff for each admissible stable matching
instance.
-/
theorem theorem3_coalitionAttenuationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_subset_endpoint_bounds
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {coalition largeSubset :
      ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon : ℝ} {threshold : ∀ C : ℕ, Admissible C → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon)
    (hlow_endpoint :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (largeSubset C a) (threshold C a - epsilon)
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2)) <
            epsilon)
    (hhigh_subset_endpoint :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - epsilon <
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) (threshold C a + epsilon)
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2))) :
    (∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v : ℝ,
          v < threshold C a - epsilon →
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2)) <
              epsilon) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v : ℝ,
          threshold C a + epsilon < v →
            1 - epsilon <
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (coalition C a) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))) := by
  have h :=
    theorem3_coalitionAttenuationUniformWitness_of_iidProduct_selected_stable_cutoff_subset_endpoint_bounds
      Mseq Iseq selected noiseLaw cutoffOut hlarge hlow_endpoint
      hhigh_subset_endpoint
  exact theorem3_coalitionAttenuationUniformWitness_source_clauses h

/--
Concrete selected-stable Theorem 3 source clauses from scalar tail endpoint
estimates.  The low endpoint is derived from a per-college upper-tail bound
and a finite union bound; the high endpoint is derived from the iid product
formula and a small product of lower-tail no-crossing probabilities.
-/
theorem theorem3_coalitionAttenuationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_scalar_tail_product_endpoint_estimates
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {coalition largeSubset :
      ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon : ℝ} {threshold : ∀ C : ℕ, Admissible C → ℝ}
    {lowTailBound : ∀ C : ℕ, Admissible C → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon)
    (hlow_card_tail :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          ((largeSubset C a).card : ℝ) * lowTailBound C a < epsilon)
    (hlow_tail :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c ∈ largeSubset C a,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2) c -
              (threshold C a - epsilon)) ≤
            lowTailBound C a)
    (hhigh_product :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          (∏ c ∈ largeSubset C a,
            AppliedModelingLib.Probability.lowerCDFMass noiseLaw
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2) c -
                (threshold C a + epsilon))) <
            epsilon) :
    (∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v : ℝ,
          v < threshold C a - epsilon →
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2)) <
              epsilon) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v : ℝ,
          threshold C a + epsilon < v →
            1 - epsilon <
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (coalition C a) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))) := by
  have hlow_endpoint :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (largeSubset C a) (threshold C a - epsilon)
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2)) <
            epsilon := by
    filter_upwards [hlow_card_tail, hlow_tail] with C hcardC htailC a
    exact
      cutoffAffordanceProbability_iidProduct_lt_of_card_mul_upperTailMass_le
        noiseLaw (largeSubset C a) (threshold C a - epsilon)
        (cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C a).1) (selected C a).2))
        (hcardC a) (htailC a)
  have hhigh_subset_endpoint :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - epsilon <
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) (threshold C a + epsilon)
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2)) := by
    filter_upwards [hhigh_product] with C hprodC a
    exact
      cutoffAffordanceProbability_iidProduct_gt_one_sub_of_prod_lowerCDFMass_lt
        noiseLaw (largeSubset C a) (threshold C a + epsilon)
        (cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C a).1) (selected C a).2))
        (hprodC a)
  exact
    theorem3_coalitionAttenuationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_subset_endpoint_bounds
      Mseq Iseq selected noiseLaw cutoffOut hlarge hlow_endpoint
      hhigh_subset_endpoint

/--
Uniform selected-stable Theorem 3 source clauses from scalar low-tail controls
and a one-college high endpoint estimate.  The high endpoint estimate is
strictly smaller than the full lower-CDF product premise: Lean derives the
product bound from probability bounds for the remaining factors.
-/
theorem theorem3_coalitionAttenuationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_scalar_tail_exists_high_endpoint_estimates
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {coalition largeSubset :
      ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon : ℝ} {threshold : ∀ C : ℕ, Admissible C → ℝ}
    {lowTailBound : ∀ C : ℕ, Admissible C → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon)
    (hlow_card_tail :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          ((largeSubset C a).card : ℝ) * lowTailBound C a < epsilon)
    (hlow_tail :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c ∈ largeSubset C a,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2) c -
              (threshold C a - epsilon)) ≤
            lowTailBound C a)
    (hhigh_exists :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          ∃ c ∈ largeSubset C a,
            AppliedModelingLib.Probability.lowerCDFMass noiseLaw
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2) c -
                (threshold C a + epsilon)) <
              epsilon) :
    (∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v : ℝ,
          v < threshold C a - epsilon →
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2)) <
              epsilon) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v : ℝ,
          threshold C a + epsilon < v →
            1 - epsilon <
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (coalition C a) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))) := by
  have hhigh_product :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          (∏ c ∈ largeSubset C a,
            AppliedModelingLib.Probability.lowerCDFMass noiseLaw
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2) c -
                (threshold C a + epsilon))) <
            epsilon := by
    filter_upwards [hhigh_exists] with C hC a
    exact
      prod_lt_of_exists_lt_of_nonneg_le_one (largeSubset C a)
        (fun c =>
          AppliedModelingLib.Probability.lowerCDFMass noiseLaw
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2) c -
              (threshold C a + epsilon)))
        (hC a)
        (fun c _hc => AppliedModelingLib.Probability.lowerCDFMass_nonneg noiseLaw _)
        (fun c _hc => AppliedModelingLib.Probability.lowerCDFMass_le_one noiseLaw _)
  exact
    theorem3_coalitionAttenuationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_scalar_tail_product_endpoint_estimates
      Mseq Iseq selected noiseLaw cutoffOut hlarge hlow_card_tail
      hlow_tail hhigh_product

/--
Uniform selected-stable Theorem 3 source clauses from scalar low-tail controls
and a one-college high crossing estimate.  This is the direct upper-tail form
of the preceding lower-CDF endpoint route.
-/
theorem theorem3_coalitionAttenuationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_scalar_tail_exists_high_crossing_endpoint_estimates
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {coalition largeSubset :
      ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon : ℝ} {threshold : ∀ C : ℕ, Admissible C → ℝ}
    {lowTailBound : ∀ C : ℕ, Admissible C → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon)
    (hlow_card_tail :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          ((largeSubset C a).card : ℝ) * lowTailBound C a < epsilon)
    (hlow_tail :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c ∈ largeSubset C a,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2) c -
              (threshold C a - epsilon)) ≤
            lowTailBound C a)
    (hhigh_crossing :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          ∃ c ∈ largeSubset C a,
            1 - epsilon <
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2) c -
                  (threshold C a + epsilon))) :
    (∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v : ℝ,
          v < threshold C a - epsilon →
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2)) <
              epsilon) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v : ℝ,
          threshold C a + epsilon < v →
            1 - epsilon <
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (coalition C a) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))) := by
  have hhigh_exists :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          ∃ c ∈ largeSubset C a,
            AppliedModelingLib.Probability.lowerCDFMass noiseLaw
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2) c -
                (threshold C a + epsilon)) <
              epsilon := by
    filter_upwards [hhigh_crossing] with C hC a
    rcases hC a with ⟨c, hc, htail⟩
    exact ⟨c, hc,
      lowerCDFMass_lt_of_one_sub_lt_upperTailMass noiseLaw htail⟩
  exact
    theorem3_coalitionAttenuationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_scalar_tail_exists_high_endpoint_estimates
      Mseq Iseq selected noiseLaw cutoffOut hlarge hlow_card_tail
      hlow_tail hhigh_exists

/--
Uniform selected-stable Theorem 3 source clauses from a scalar lower-cutoff
floor.  The scalar floor estimate derives the low-tail controls for every
admissible selected stable matching and chosen large subset.
-/
theorem theorem3_coalitionAttenuationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_scalar_floor_lowTail_exists_high_crossing_endpoint_estimates
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {coalition largeSubset :
      ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon : ℝ} {threshold : ∀ C : ℕ, Admissible C → ℝ}
    {tailRate lowerCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon)
    (hlow_card_tail :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          ((largeSubset C a).card : ℝ) * tailRate C a < epsilon)
    (hcutoff_lower :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c ∈ largeSubset C a,
          lowerCutoff C a ≤
            cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2) c)
    (hlow_tail_floor :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (lowerCutoff C a - (threshold C a - epsilon)) ≤
          tailRate C a)
    (hhigh_crossing :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          ∃ c ∈ largeSubset C a,
            1 - epsilon <
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2) c -
                  (threshold C a + epsilon))) :
    (∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v : ℝ,
          v < threshold C a - epsilon →
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2)) <
              epsilon) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v : ℝ,
          threshold C a + epsilon < v →
            1 - epsilon <
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (coalition C a) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))) := by
  have hlow_tail :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c ∈ largeSubset C a,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2) c -
              (threshold C a - epsilon)) ≤
            tailRate C a := by
    filter_upwards [hcutoff_lower, hlow_tail_floor] with
      C hcutoffC htailC a c hc
    exact
      le_trans
        (AppliedModelingLib.Probability.upperTailMass_antitone noiseLaw
          (sub_le_sub_right (hcutoffC a c hc) (threshold C a - epsilon)))
        (htailC a)
  exact
    theorem3_coalitionAttenuationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_scalar_tail_exists_high_crossing_endpoint_estimates
      Mseq Iseq selected noiseLaw cutoffOut hlarge hlow_card_tail
      hlow_tail hhigh_crossing

/--
Uniform selected-stable Theorem 3 source clauses for the semantic block of
colleges whose selected-stable cutoffs are not below the scalar floor.

This is the sortedness-free low-side variant of the suffix route: the source
still must supply a high-crossing endpoint inside the same semantic block, but
the low endpoint follows directly from the below-floor count bound rather than
from any ordered-index or relabeling premise.
-/
theorem theorem3_coalitionAttenuationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_nonLow_scalar_floor_lowTail_halfDiv_exists_high_crossing_endpoint_estimates
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon)
    {threshold : ∀ C : ℕ, Admissible C → ℝ}
    {lowerCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (hlow_count :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          (lowCutoffIndexSet
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2))
            (lowerCutoff C a)).card ≤
          epsilonFloorSplitIndex (epsilon / 2) C)
    (hlow_tail_floor :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (lowerCutoff C a - (threshold C a - epsilon)) ≤
          epsilon / (2 * (((C + 1 : ℕ) : ℝ))))
    (hhigh_crossing :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          ∃ c ∈ nonLowCutoffIndexSet
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2))
              (lowerCutoff C a),
            1 - epsilon <
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2) c -
                  (threshold C a + epsilon))) :
    (∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        CoalitionLargeSubset
          (Finset.univ : Finset (Fin (C + 1)))
          (nonLowCutoffIndexSet
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2))
            (lowerCutoff C a))
          epsilon) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v : ℝ,
          v < threshold C a - epsilon →
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (nonLowCutoffIndexSet
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))
                (lowerCutoff C a)) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2)) <
              epsilon) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v : ℝ,
          threshold C a + epsilon < v →
            1 - epsilon <
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (Finset.univ : Finset (Fin (C + 1))) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))) := by
  let largeSubset : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1)) :=
    fun C a =>
      nonLowCutoffIndexSet
        (cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C a).1) (selected C a).2))
        (lowerCutoff C a)
  let coalition : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1)) :=
    fun C _a => Finset.univ
  let tailRate : ∀ C : ℕ, Admissible C → ℝ :=
    fun C _a => epsilon / (2 * (((C + 1 : ℕ) : ℝ)))
  have hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon := by
    filter_upwards [hlow_count] with C hcountC a
    exact
      coalitionLargeSubset_univ_nonLowCutoffIndexSet_of_lowCutoff_card_le
        (C := C) (epsilon := epsilon) hepsilon_pos (hcountC a)
  have hlow_card_tail :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          ((largeSubset C a).card : ℝ) * tailRate C a < epsilon := by
    exact Filter.Eventually.of_forall (fun C a =>
      nonLowCutoffIndexSet_card_mul_tailRate_lt_of_tailRate_le_half_div
        (C := C) (epsilon := epsilon)
        (tailRate := epsilon / (2 * (((C + 1 : ℕ) : ℝ))))
        (cutoff :=
          cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C a).1) (selected C a).2))
        (floor := lowerCutoff C a)
        hepsilon_pos le_rfl)
  have hcutoff_lower :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c ∈ largeSubset C a,
          lowerCutoff C a ≤
            cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2) c := by
    exact Filter.Eventually.of_forall (fun C a c hc =>
      floor_le_of_mem_nonLowCutoffIndexSet hc)
  simpa [largeSubset, coalition, tailRate] using
    theorem3_coalitionAttenuationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_scalar_floor_lowTail_exists_high_crossing_endpoint_estimates
      Mseq Iseq selected noiseLaw cutoffOut hlarge hlow_card_tail
      hcutoff_lower hlow_tail_floor hhigh_crossing

/--
Uniform selected-stable Theorem 3 source clauses for the paper's sorted
suffix `C₂`.  Lean derives the large-subset condition from deleting an
`epsilon/2` prefix, derives the cardinality-tail product from the scalar
tail-rate bound `epsilon / (2*(C+1))`, and turns the sorted-index cutoff
condition into the subset cutoff-floor condition.
-/
theorem theorem3_coalitionAttenuationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_suffix_scalar_floor_lowTail_exists_high_crossing_endpoint_estimates
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon)
    {threshold : ∀ C : ℕ, Admissible C → ℝ}
    {tailRate lowerCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (htailRate :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          tailRate C a ≤ epsilon / (2 * (((C + 1 : ℕ) : ℝ))))
    (hcutoff_lower :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c : Fin (C + 1),
          epsilonFloorSplitIndex (epsilon / 2) C ≤ (c : ℕ) →
            lowerCutoff C a ≤
              cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2) c)
    (hlow_tail_floor :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (lowerCutoff C a - (threshold C a - epsilon)) ≤
          tailRate C a)
    (hhigh_crossing :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          ∃ c ∈ indexSuffixLarge (epsilonFloorSplitIndex (epsilon / 2) C) C,
            1 - epsilon <
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2) c -
                  (threshold C a + epsilon))) :
    (∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        CoalitionLargeSubset
          (Finset.univ : Finset (Fin (C + 1)))
          (indexSuffixLarge (epsilonFloorSplitIndex (epsilon / 2) C) C)
          epsilon) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v : ℝ,
          v < threshold C a - epsilon →
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (indexSuffixLarge (epsilonFloorSplitIndex (epsilon / 2) C) C) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2)) <
              epsilon) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v : ℝ,
          threshold C a + epsilon < v →
            1 - epsilon <
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (Finset.univ : Finset (Fin (C + 1))) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))) := by
  let largeSubset : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1)) :=
    fun C _a => indexSuffixLarge (epsilonFloorSplitIndex (epsilon / 2) C) C
  let coalition : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1)) :=
    fun C _a => Finset.univ
  have hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon := by
    filter_upwards [Filter.Eventually.of_forall
      (fun C => coalitionLargeSubset_univ_indexSuffixLarge_epsilonHalf
        (epsilon := epsilon) hepsilon_pos C)] with C hC a
    exact hC
  have hlow_card_tail :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          ((largeSubset C a).card : ℝ) * tailRate C a < epsilon := by
    filter_upwards [htailRate] with C htailC a
    exact
      indexSuffixLarge_card_mul_tailRate_lt_of_tailRate_le_half_div
        (C := C) (epsilon := epsilon) (tailRate := tailRate C a)
        hepsilon_pos (htailC a)
  have hcutoff_lower_subset :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c ∈ largeSubset C a,
          lowerCutoff C a ≤
            cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2) c := by
    filter_upwards [hcutoff_lower] with C hcutoffC a c hc
    exact hcutoffC a c (Finset.mem_filter.mp hc).2
  simpa [largeSubset, coalition] using
    theorem3_coalitionAttenuationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_scalar_floor_lowTail_exists_high_crossing_endpoint_estimates
      Mseq Iseq selected noiseLaw cutoffOut hlarge hlow_card_tail
      hcutoff_lower_subset hlow_tail_floor hhigh_crossing

/--
Uniform selected-stable Theorem 3 source clauses for the paper's sorted
suffix `C₂`, with the low-tail endpoint stated directly at the rate needed
for the finite union bound.  This removes the auxiliary `tailRate` witness
from the paper-facing boundary.
-/
theorem theorem3_coalitionAttenuationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_suffix_scalar_floor_lowTail_halfDiv_exists_high_crossing_endpoint_estimates
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon)
    {threshold : ∀ C : ℕ, Admissible C → ℝ}
    {lowerCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (hcutoff_lower :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c : Fin (C + 1),
          epsilonFloorSplitIndex (epsilon / 2) C ≤ (c : ℕ) →
            lowerCutoff C a ≤
              cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2) c)
    (hlow_tail_floor :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (lowerCutoff C a - (threshold C a - epsilon)) ≤
          epsilon / (2 * (((C + 1 : ℕ) : ℝ))))
    (hhigh_crossing :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          ∃ c ∈ indexSuffixLarge (epsilonFloorSplitIndex (epsilon / 2) C) C,
            1 - epsilon <
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2) c -
                  (threshold C a + epsilon))) :
    (∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        CoalitionLargeSubset
          (Finset.univ : Finset (Fin (C + 1)))
          (indexSuffixLarge (epsilonFloorSplitIndex (epsilon / 2) C) C)
          epsilon) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v : ℝ,
          v < threshold C a - epsilon →
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (indexSuffixLarge (epsilonFloorSplitIndex (epsilon / 2) C) C) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2)) <
              epsilon) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v : ℝ,
          threshold C a + epsilon < v →
            1 - epsilon <
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (Finset.univ : Finset (Fin (C + 1))) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))) := by
  let tailRate : ∀ C : ℕ, Admissible C → ℝ :=
    fun C _a => epsilon / (2 * (((C + 1 : ℕ) : ℝ)))
  have htailRate :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          tailRate C a ≤ epsilon / (2 * (((C + 1 : ℕ) : ℝ))) := by
    exact Filter.Eventually.of_forall (fun C a => le_rfl)
  simpa [tailRate] using
    theorem3_coalitionAttenuationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_suffix_scalar_floor_lowTail_exists_high_crossing_endpoint_estimates
      Mseq Iseq selected noiseLaw cutoffOut hepsilon_pos htailRate
      hcutoff_lower hlow_tail_floor hhigh_crossing

/--
Uniform selected-stable Theorem 3 source clauses for the paper's sorted suffix
`C₂`, with both endpoint estimates stated as scalar cutoff-floor/ceiling
conditions.  The high-crossing witness is derived from a suffix college whose
selected-stable cutoff is below the scalar upper ceiling and antitonicity of the
upper tail.
-/
theorem theorem3_coalitionAttenuationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_suffix_scalar_floor_lowTail_halfDiv_upperCeiling_highTail_endpoint_estimates
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon)
    {threshold : ∀ C : ℕ, Admissible C → ℝ}
    {lowerCutoff upperCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (hcutoff_lower :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c : Fin (C + 1),
          epsilonFloorSplitIndex (epsilon / 2) C ≤ (c : ℕ) →
            lowerCutoff C a ≤
              cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2) c)
    (hlow_tail_floor :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (lowerCutoff C a - (threshold C a - epsilon)) ≤
          epsilon / (2 * (((C + 1 : ℕ) : ℝ))))
    (hcutoff_upper_exists :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          ∃ c ∈ indexSuffixLarge (epsilonFloorSplitIndex (epsilon / 2) C) C,
            cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2) c ≤
              upperCutoff C a)
    (hhigh_tail_ceiling :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - epsilon <
            AppliedModelingLib.Probability.upperTailMass noiseLaw
              (upperCutoff C a - (threshold C a + epsilon))) :
    (∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        CoalitionLargeSubset
          (Finset.univ : Finset (Fin (C + 1)))
          (indexSuffixLarge (epsilonFloorSplitIndex (epsilon / 2) C) C)
          epsilon) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v : ℝ,
          v < threshold C a - epsilon →
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (indexSuffixLarge (epsilonFloorSplitIndex (epsilon / 2) C) C) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2)) <
              epsilon) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v : ℝ,
          threshold C a + epsilon < v →
            1 - epsilon <
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (Finset.univ : Finset (Fin (C + 1))) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))) := by
  have hhigh_crossing :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          ∃ c ∈ indexSuffixLarge (epsilonFloorSplitIndex (epsilon / 2) C) C,
            1 - epsilon <
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2) c -
                  (threshold C a + epsilon)) := by
    filter_upwards [hcutoff_upper_exists, hhigh_tail_ceiling] with
      C hupperC htailC a
    rcases hupperC a with ⟨c, hc, hcutoff_le⟩
    refine ⟨c, hc, ?_⟩
    exact
      lt_of_lt_of_le (htailC a)
        (AppliedModelingLib.Probability.upperTailMass_antitone noiseLaw
          (sub_le_sub_right hcutoff_le (threshold C a + epsilon)))
  exact
    theorem3_coalitionAttenuationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_suffix_scalar_floor_lowTail_halfDiv_exists_high_crossing_endpoint_estimates
      Mseq Iseq selected noiseLaw cutoffOut hepsilon_pos hcutoff_lower
      hlow_tail_floor hhigh_crossing

/--
Uniform selected-stable Theorem 3 source clauses with the high-tail ceiling
derived from an eventual-at-`-∞` upper-ceiling separation.  This is the
asymptotic form of the paper's high-value endpoint argument: once the scalar
upper cutoff lies arbitrarily far below `threshold + epsilon`, the upper-tail
mass at that endpoint is eventually above `1 - epsilon`.
-/
theorem theorem3_coalitionAttenuationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_suffix_scalar_floor_lowTail_halfDiv_upperCeiling_atBot_endpoint_estimates
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon)
    {threshold : ∀ C : ℕ, Admissible C → ℝ}
    {lowerCutoff upperCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (hcutoff_lower :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c : Fin (C + 1),
          epsilonFloorSplitIndex (epsilon / 2) C ≤ (c : ℕ) →
            lowerCutoff C a ≤
              cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2) c)
    (hlow_tail_floor :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (lowerCutoff C a - (threshold C a - epsilon)) ≤
          epsilon / (2 * (((C + 1 : ℕ) : ℝ))))
    (hcutoff_upper_exists :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          ∃ c ∈ indexSuffixLarge (epsilonFloorSplitIndex (epsilon / 2) C) C,
            cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2) c ≤
              upperCutoff C a)
    (hupper_ceiling_atBot :
      ∀ B : ℝ, ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          upperCutoff C a - (threshold C a + epsilon) ≤ B) :
    (∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        CoalitionLargeSubset
          (Finset.univ : Finset (Fin (C + 1)))
          (indexSuffixLarge (epsilonFloorSplitIndex (epsilon / 2) C) C)
          epsilon) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v : ℝ,
          v < threshold C a - epsilon →
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (indexSuffixLarge (epsilonFloorSplitIndex (epsilon / 2) C) C) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2)) <
              epsilon) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v : ℝ,
          threshold C a + epsilon < v →
            1 - epsilon <
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (Finset.univ : Finset (Fin (C + 1))) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))) := by
  rcases Filter.eventually_atBot.1
      (AppliedModelingLib.Probability.eventually_one_sub_lt_upperTailMass_atBot
        noiseLaw hepsilon_pos) with
    ⟨B, hB⟩
  have hhigh_tail_ceiling :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - epsilon <
            AppliedModelingLib.Probability.upperTailMass noiseLaw
              (upperCutoff C a - (threshold C a + epsilon)) := by
    filter_upwards [hupper_ceiling_atBot B] with C hC a
    exact hB (upperCutoff C a - (threshold C a + epsilon)) (hC a)
  exact
    theorem3_coalitionAttenuationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_suffix_scalar_floor_lowTail_halfDiv_upperCeiling_highTail_endpoint_estimates
      Mseq Iseq selected noiseLaw cutoffOut hepsilon_pos hcutoff_lower
      hlow_tail_floor hcutoff_upper_exists hhigh_tail_ceiling

/--
Theorem 3 indexed witness from the endpoint form used in the source proof.
Once the chosen subsets are eventually large, affordability is monotone in
value, and the two endpoint inequalities hold eventually, the full shifted
low/high clauses follow for all values on the corresponding sides of the
threshold.
-/
theorem theorem3_coalitionAttenuationEpsilonWitness_of_eventual_monotone_endpoint_bounds
    {College : ℕ → Type v}
    {coalition largeSubset : ∀ C : ℕ, Finset (College C)}
    {affordProb : ∀ C : ℕ, ℝ → Finset (College C) → ℝ}
    {epsilon threshold : ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        CoalitionLargeSubset (coalition C) (largeSubset C) epsilon)
    (hmono_large :
      ∀ᶠ C : ℕ in atTop,
        Monotone (fun v => affordProb C v (largeSubset C)))
    (hmono_coalition :
      ∀ᶠ C : ℕ in atTop,
        Monotone (fun v => affordProb C v (coalition C)))
    (hlow_endpoint :
      ∀ᶠ C : ℕ in atTop,
        affordProb C (threshold - epsilon) (largeSubset C) < epsilon)
    (hhigh_endpoint :
      ∀ᶠ C : ℕ in atTop,
        1 - epsilon < affordProb C (threshold + epsilon) (coalition C)) :
    Theorem3CoalitionAttenuationEpsilonWitnessConclusion
      coalition largeSubset affordProb epsilon threshold := by
  refine ⟨hlarge, ?_, ?_⟩
  · intro v hv
    filter_upwards [hmono_large, hlow_endpoint] with C hmonoC hlowC
    exact
      theorem3_low_values_blocked_of_monotone_endpoint_bound
        (largeSubset := largeSubset C)
        (affordProb := affordProb C)
        (epsilon := epsilon) (threshold := threshold)
        hmonoC hlowC v hv
  · intro v hv
    filter_upwards [hmono_coalition, hhigh_endpoint] with C hmonoC hhighC
    exact
      theorem3_high_values_admitted_of_monotone_endpoint_bound
        (coalition := coalition C)
        (affordProb := affordProb C)
        (epsilon := epsilon) (threshold := threshold)
        hmonoC hhighC v hv

/--
Indexed Theorem 3 witness from the subset-to-coalition transfer used in the
source proof.  The proof often first obtains the high-value bound on the
large subset `C'`; active-set monotonicity then transfers that bound to the
full coalition `C`.
-/
theorem theorem3_coalitionAttenuationEpsilonWitness_of_eventual_subset_high_values
    {College : ℕ → Type v}
    {coalition largeSubset : ∀ C : ℕ, Finset (College C)}
    {affordProb : ∀ C : ℕ, ℝ → Finset (College C) → ℝ}
    {epsilon threshold : ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        CoalitionLargeSubset (coalition C) (largeSubset C) epsilon)
    (hlow :
      ∀ v, v < threshold - epsilon →
        ∀ᶠ C : ℕ in atTop, affordProb C v (largeSubset C) < epsilon)
    (hhigh_subset :
      ∀ v, threshold + epsilon < v →
        ∀ᶠ C : ℕ in atTop, 1 - epsilon < affordProb C v (largeSubset C))
    (hmono :
      ∀ᶠ C : ℕ in atTop,
        ∀ v, affordProb C v (largeSubset C) ≤ affordProb C v (coalition C)) :
    Theorem3CoalitionAttenuationEpsilonWitnessConclusion
      coalition largeSubset affordProb epsilon threshold := by
  refine ⟨hlarge, hlow, ?_⟩
  intro v hv
  filter_upwards [hhigh_subset v hv, hmono] with C hhighC hmonoC
  exact lt_of_lt_of_le hhighC (hmonoC v)

/--
Indexed Theorem 3 witness from endpoint estimates on the large subset and
monotonicity from the large subset to the full coalition.
-/
theorem theorem3_coalitionAttenuationEpsilonWitness_of_eventual_subset_endpoint_bounds
    {College : ℕ → Type v}
    {coalition largeSubset : ∀ C : ℕ, Finset (College C)}
    {affordProb : ∀ C : ℕ, ℝ → Finset (College C) → ℝ}
    {epsilon threshold : ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        CoalitionLargeSubset (coalition C) (largeSubset C) epsilon)
    (hmono_large :
      ∀ᶠ C : ℕ in atTop,
        Monotone (fun v => affordProb C v (largeSubset C)))
    (hlow_endpoint :
      ∀ᶠ C : ℕ in atTop,
        affordProb C (threshold - epsilon) (largeSubset C) < epsilon)
    (hhigh_subset_endpoint :
      ∀ᶠ C : ℕ in atTop,
        1 - epsilon < affordProb C (threshold + epsilon) (largeSubset C))
    (hmono_subset_coalition :
      ∀ᶠ C : ℕ in atTop,
        ∀ v, affordProb C v (largeSubset C) ≤ affordProb C v (coalition C)) :
    Theorem3CoalitionAttenuationEpsilonWitnessConclusion
      coalition largeSubset affordProb epsilon threshold := by
  refine
    theorem3_coalitionAttenuationEpsilonWitness_of_eventual_subset_high_values
      hlarge ?_ ?_ hmono_subset_coalition
  · intro v hv
    filter_upwards [hmono_large, hlow_endpoint] with C hmonoC hlowC
    exact
      theorem3_low_values_blocked_of_monotone_endpoint_bound
        (largeSubset := largeSubset C)
        (affordProb := affordProb C)
        (epsilon := epsilon) (threshold := threshold)
        hmonoC hlowC v hv
  · intro v hv
    filter_upwards [hmono_large, hhigh_subset_endpoint] with C hmonoC hhighC
    exact
      theorem3_high_values_admitted_of_monotone_endpoint_bound
        (coalition := largeSubset C)
        (affordProb := affordProb C)
        (epsilon := epsilon) (threshold := threshold)
      hmonoC hhighC v hv

/--
Indexed Theorem 3 witness for the independent-product affordance model.  The
source subset-to-coalition transfer is derived here from `C' ⊆ C` and the
fact that each single-college crossing probability lies in `[0,1]`.
-/
theorem theorem3_coalitionAttenuationEpsilonWitness_of_independent_subset_endpoint_bounds
    {coalition largeSubset : ∀ C : ℕ, Finset (Fin (C + 1))}
    {crossingProbability : ∀ C : ℕ, ℝ → Fin (C + 1) → ℝ}
    {epsilon threshold : ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        CoalitionLargeSubset (coalition C) (largeSubset C) epsilon)
    (hmono_large :
      ∀ᶠ C : ℕ in atTop,
        Monotone (fun v =>
          independentAffordanceProbability
            (largeSubset C) (crossingProbability C v)))
    (hlow_endpoint :
      ∀ᶠ C : ℕ in atTop,
        independentAffordanceProbability
          (largeSubset C) (crossingProbability C (threshold - epsilon)) <
            epsilon)
    (hhigh_subset_endpoint :
      ∀ᶠ C : ℕ in atTop,
        1 - epsilon <
          independentAffordanceProbability
            (largeSubset C) (crossingProbability C (threshold + epsilon)))
    (hprob_nonneg :
      ∀ᶠ C : ℕ in atTop,
        ∀ v, ∀ c ∈ coalition C, 0 ≤ crossingProbability C v c)
    (hprob_le_one :
      ∀ᶠ C : ℕ in atTop,
        ∀ v, ∀ c ∈ coalition C, crossingProbability C v c ≤ 1) :
    Theorem3CoalitionAttenuationEpsilonWitnessConclusion
      coalition largeSubset
      (fun C : ℕ => fun v : ℝ => fun active : Finset (Fin (C + 1)) =>
        independentAffordanceProbability active (crossingProbability C v))
      epsilon threshold := by
  have hmono_subset_coalition :
      ∀ᶠ C : ℕ in atTop,
        ∀ v,
          independentAffordanceProbability
              (largeSubset C) (crossingProbability C v) ≤
            independentAffordanceProbability
              (coalition C) (crossingProbability C v) := by
    filter_upwards [hlarge, hprob_nonneg, hprob_le_one] with
      C hlargeC hnonnegC hleC v
    exact
      independentAffordanceProbability_mono_active
        hlargeC.subset
        (fun c hc => hnonnegC v c hc)
        (fun c hc => hleC v c hc)
  exact
    theorem3_coalitionAttenuationEpsilonWitness_of_eventual_subset_endpoint_bounds
      (coalition := coalition) (largeSubset := largeSubset)
      (affordProb := fun C : ℕ => fun v : ℝ => fun active : Finset (Fin (C + 1)) =>
        independentAffordanceProbability active (crossingProbability C v))
      hlarge hmono_large hlow_endpoint hhigh_subset_endpoint
      hmono_subset_coalition

/--
Survival-function specialization of the indexed Theorem 3 witness.  The
large-subset value monotonicity is derived from antitonicity of the survival
function, and the subset-to-coalition transfer is derived from the concrete
independent-product affordance formula.
-/
theorem theorem3_coalitionAttenuationEpsilonWitness_of_survival_subset_endpoint_bounds
    {survival : ℝ → ℝ}
    {coalition largeSubset : ∀ C : ℕ, Finset (Fin (C + 1))}
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ}
    {epsilon threshold : ℝ}
    (hsurvival_antitone : Antitone survival)
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        CoalitionLargeSubset (coalition C) (largeSubset C) epsilon)
    (hlow_endpoint :
      ∀ᶠ C : ℕ in atTop,
        independentAffordanceProbability
          (largeSubset C)
          (fun c => survival (cutoff C c - (threshold - epsilon))) <
            epsilon)
    (hhigh_subset_endpoint :
      ∀ᶠ C : ℕ in atTop,
        1 - epsilon <
          independentAffordanceProbability
            (largeSubset C)
            (fun c => survival (cutoff C c - (threshold + epsilon))))
    (hprob_nonneg :
      ∀ᶠ C : ℕ in atTop,
        ∀ v, ∀ c ∈ coalition C, 0 ≤ survival (cutoff C c - v))
    (hprob_le_one :
      ∀ᶠ C : ℕ in atTop,
        ∀ v, ∀ c ∈ coalition C, survival (cutoff C c - v) ≤ 1) :
    Theorem3CoalitionAttenuationEpsilonWitnessConclusion
      coalition largeSubset
      (fun C : ℕ => fun v : ℝ => fun active : Finset (Fin (C + 1)) =>
        independentAffordanceProbability
          active (fun c => survival (cutoff C c - v)))
      epsilon threshold := by
  have hmono_large :
      ∀ᶠ C : ℕ in atTop,
        Monotone (fun v =>
          independentAffordanceProbability
            (largeSubset C)
            (fun c => survival (cutoff C c - v))) := by
    filter_upwards [hlarge, hprob_le_one] with C hlargeC hleC
    exact
      independentAffordanceProbability_mono_value_of_antitone_survival
        (active := largeSubset C)
        (survival := survival)
        (cutoff := cutoff C)
        hsurvival_antitone
        (fun v c hc => hleC v c (hlargeC.subset hc))
  exact
    theorem3_coalitionAttenuationEpsilonWitness_of_independent_subset_endpoint_bounds
      (coalition := coalition) (largeSubset := largeSubset)
      (crossingProbability := fun C : ℕ => fun v : ℝ => fun c : Fin (C + 1) =>
        survival (cutoff C c - v))
      hlarge hmono_large hlow_endpoint hhigh_subset_endpoint
      hprob_nonneg hprob_le_one

/--
Upper-tail-probability specialization of the indexed Theorem 3 witness.
The remaining source inputs are the large-subset condition and the two
endpoint affordability estimates; survival monotonicity and probability
bounds are derived from the real noise law.
-/
theorem theorem3_coalitionAttenuationEpsilonWitness_of_upperTail_subset_endpoint_bounds
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {coalition largeSubset : ∀ C : ℕ, Finset (Fin (C + 1))}
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ}
    {epsilon threshold : ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        CoalitionLargeSubset (coalition C) (largeSubset C) epsilon)
    (hlow_endpoint :
      ∀ᶠ C : ℕ in atTop,
        independentAffordanceProbability
          (largeSubset C)
          (fun c =>
            AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoff C c - (threshold - epsilon))) <
            epsilon)
    (hhigh_subset_endpoint :
      ∀ᶠ C : ℕ in atTop,
        1 - epsilon <
          independentAffordanceProbability
            (largeSubset C)
            (fun c =>
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C c - (threshold + epsilon)))) :
    Theorem3CoalitionAttenuationEpsilonWitnessConclusion
      coalition largeSubset
      (fun C : ℕ => fun v : ℝ => fun active : Finset (Fin (C + 1)) =>
        independentAffordanceProbability
          active
          (fun c =>
            AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoff C c - v)))
      epsilon threshold := by
  have htail_package :=
    upperTailMass_survival_probability_package_indexed
      (noiseLaw := noiseLaw)
      (active := coalition)
      (cutoff := cutoff)
  exact
    theorem3_coalitionAttenuationEpsilonWitness_of_survival_subset_endpoint_bounds
      (survival := AppliedModelingLib.Probability.upperTailMass noiseLaw)
      htail_package.1 hlarge hlow_endpoint hhigh_subset_endpoint
      htail_package.2.1 htail_package.2.2

/--
Concrete iid-product cutoff specialization of the indexed Theorem 3 witness.
The source endpoint estimates and the conclusion are stated directly in the
paper's product-noise cutoff-affordance probability; the independent product
formula is used only internally.
-/
theorem theorem3_coalitionAttenuationEpsilonWitness_of_iidProduct_cutoff_subset_endpoint_bounds
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {coalition largeSubset : ∀ C : ℕ, Finset (Fin (C + 1))}
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ}
    {epsilon threshold : ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        CoalitionLargeSubset (coalition C) (largeSubset C) epsilon)
    (hlow_endpoint :
      ∀ᶠ C : ℕ in atTop,
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (largeSubset C) (threshold - epsilon) (cutoff C) <
            epsilon)
    (hhigh_subset_endpoint :
      ∀ᶠ C : ℕ in atTop,
        1 - epsilon <
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (largeSubset C) (threshold + epsilon) (cutoff C)) :
    Theorem3CoalitionAttenuationEpsilonWitnessConclusion
      coalition largeSubset
      (fun C : ℕ => fun v : ℝ => fun active : Finset (Fin (C + 1)) =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          active v (cutoff C))
      epsilon threshold := by
  have hlow_tail :
      ∀ᶠ C : ℕ in atTop,
        independentAffordanceProbability
          (largeSubset C)
          (fun c =>
            AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoff C c - (threshold - epsilon))) <
            epsilon := by
    filter_upwards [hlow_endpoint] with C hlowC
    have hbridge :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (largeSubset C) (threshold - epsilon) (cutoff C)
    simpa [hbridge] using hlowC
  have hhigh_tail :
      ∀ᶠ C : ℕ in atTop,
        1 - epsilon <
          independentAffordanceProbability
            (largeSubset C)
            (fun c =>
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoff C c - (threshold + epsilon))) := by
    filter_upwards [hhigh_subset_endpoint] with C hhighC
    have hbridge :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (largeSubset C) (threshold + epsilon) (cutoff C)
    simpa [hbridge] using hhighC
  have htail :=
    theorem3_coalitionAttenuationEpsilonWitness_of_upperTail_subset_endpoint_bounds
      (noiseLaw := noiseLaw)
      (coalition := coalition)
      (largeSubset := largeSubset)
      (cutoff := cutoff)
      (epsilon := epsilon)
      (threshold := threshold)
      hlarge hlow_tail hhigh_tail
  refine ⟨htail.large_subset_eventually, ?_, ?_⟩
  · intro v hv
    filter_upwards [htail.low_values_eventually_blocked v hv] with C hC
    have hbridge :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (largeSubset C) v (cutoff C)
    simpa [hbridge] using hC
  · intro v hv
    filter_upwards [htail.high_values_eventually_admitted v hv] with C hC
    have hbridge :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (coalition C) v (cutoff C)
    simpa [hbridge] using hC

/--
Concrete iid-product Theorem 3 over a selected sequence of stable matchings.

The A-L bridge chooses the market-clearing cutoff representing each selected
stable matching.  The endpoint estimates are stated for all market-clearing
cutoffs, then specialized to the selected stable-matching cutoffs.
-/
theorem theorem3_coalitionAttenuationEpsilonWitness_of_iidProduct_selected_stable_cutoff_subset_endpoint_bounds
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (selected :
      ∀ C : ℕ, { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {coalition largeSubset : ∀ C : ℕ, Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon threshold : ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        CoalitionLargeSubset (coalition C) (largeSubset C) epsilon)
    (hlow_endpoint :
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (largeSubset C) (threshold - epsilon) (cutoffOut C P) <
              epsilon)
    (hhigh_subset_endpoint :
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          1 - epsilon <
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C) (threshold + epsilon) (cutoffOut C P)) :
    Theorem3CoalitionAttenuationEpsilonWitnessConclusion
      coalition largeSubset
      (fun C : ℕ => fun v : ℝ => fun active : Finset (Fin (C + 1)) =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          active v
          (cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C).1) (selected C).2)))
      epsilon threshold := by
  have hmc :
      ∀ C : ℕ,
        (Mseq C).MarketClearing
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C).1) (selected C).2) := by
    intro C
    exact
      (Iseq C).marketClearingCutoffOfStable_marketClearing
        (μ := (selected C).1) (selected C).2
  refine
    theorem3_coalitionAttenuationEpsilonWitness_of_iidProduct_cutoff_subset_endpoint_bounds
      (noiseLaw := noiseLaw)
      (coalition := coalition)
      (largeSubset := largeSubset)
      (cutoff := fun C : ℕ =>
        cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C).1) (selected C).2))
      (epsilon := epsilon)
      (threshold := threshold)
      hlarge ?_ ?_
  · filter_upwards [hlow_endpoint] with C hC
    exact hC _ (hmc C)
  · filter_upwards [hhigh_subset_endpoint] with C hC
    exact hC _ (hmc C)

/--
Indexed Theorem 3 source clauses unpacked from the witness conclusion.
-/
theorem theorem3_coalitionAttenuationEpsilonWitness_source_clauses
    {College : ℕ → Type v}
    {coalition largeSubset : ∀ C : ℕ, Finset (College C)}
    {affordProb : ∀ C : ℕ, ℝ → Finset (College C) → ℝ}
    {epsilon threshold : ℝ}
    (h :
      Theorem3CoalitionAttenuationEpsilonWitnessConclusion
        coalition largeSubset affordProb epsilon threshold) :
    (∀ᶠ C : ℕ in atTop,
      CoalitionLargeSubset (coalition C) (largeSubset C) epsilon) ∧
      (∀ v, v < threshold - epsilon →
        ∀ᶠ C : ℕ in atTop, affordProb C v (largeSubset C) < epsilon) ∧
      (∀ v, threshold + epsilon < v →
        ∀ᶠ C : ℕ in atTop, 1 - epsilon < affordProb C v (coalition C)) :=
  ⟨h.large_subset_eventually,
    h.low_values_eventually_blocked,
    h.high_values_eventually_admitted⟩

/--
Concrete selected-stable Theorem 3 source clauses.  This composes the
selected-stable cutoff endpoint route with the source-clause projection, so
the paper-facing conclusion is stated directly for the selected stable
matchings rather than through an abstract affordability function.
-/
theorem theorem3_coalitionAttenuationEpsilonWitness_source_clauses_of_iidProduct_selected_stable_cutoff_subset_endpoint_bounds
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (selected :
      ∀ C : ℕ, { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {coalition largeSubset : ∀ C : ℕ, Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon threshold : ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        CoalitionLargeSubset (coalition C) (largeSubset C) epsilon)
    (hlow_endpoint :
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (largeSubset C) (threshold - epsilon) (cutoffOut C P) <
              epsilon)
    (hhigh_subset_endpoint :
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          1 - epsilon <
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C) (threshold + epsilon) (cutoffOut C P)) :
    (∀ᶠ C : ℕ in atTop,
      CoalitionLargeSubset (coalition C) (largeSubset C) epsilon) ∧
      (∀ v, v < threshold - epsilon →
        ∀ᶠ C : ℕ in atTop,
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (largeSubset C) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C).1) (selected C).2)) < epsilon) ∧
      (∀ v, threshold + epsilon < v →
        ∀ᶠ C : ℕ in atTop,
          1 - epsilon <
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (coalition C) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C).1) (selected C).2))) := by
  have h :=
    theorem3_coalitionAttenuationEpsilonWitness_of_iidProduct_selected_stable_cutoff_subset_endpoint_bounds
      Mseq Iseq selected noiseLaw cutoffOut hlarge hlow_endpoint
      hhigh_subset_endpoint
  exact theorem3_coalitionAttenuationEpsilonWitness_source_clauses h

/--
Indexed selected-stable Theorem 3 source clauses from scalar tail endpoint
estimates.  This is the indexed analogue of the uniform scalar-tail/product
route: the low endpoint is derived from a per-college upper-tail bound and a
finite union bound, while the high endpoint is derived from the iid product
formula and a small product of no-crossing probabilities.
-/
theorem theorem3_coalitionAttenuationEpsilonWitness_source_clauses_of_iidProduct_selected_stable_cutoff_scalar_tail_product_endpoint_estimates
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (selected :
      ∀ C : ℕ, { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {coalition largeSubset : ∀ C : ℕ, Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon threshold : ℝ}
    {lowTailBound : ℕ → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        CoalitionLargeSubset (coalition C) (largeSubset C) epsilon)
    (hlow_card_tail :
      ∀ᶠ C : ℕ in atTop,
        ((largeSubset C).card : ℝ) * lowTailBound C < epsilon)
    (hlow_tail :
      ∀ᶠ C : ℕ in atTop,
        ∀ c ∈ largeSubset C,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C).1) (selected C).2) c -
              (threshold - epsilon)) ≤
            lowTailBound C)
    (hhigh_product :
      ∀ᶠ C : ℕ in atTop,
        (∏ c ∈ largeSubset C,
          AppliedModelingLib.Probability.lowerCDFMass noiseLaw
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C).1) (selected C).2) c -
              (threshold + epsilon))) <
          epsilon) :
    (∀ᶠ C : ℕ in atTop,
      CoalitionLargeSubset (coalition C) (largeSubset C) epsilon) ∧
      (∀ v, v < threshold - epsilon →
        ∀ᶠ C : ℕ in atTop,
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (largeSubset C) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C).1) (selected C).2)) < epsilon) ∧
      (∀ v, threshold + epsilon < v →
        ∀ᶠ C : ℕ in atTop,
          1 - epsilon <
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (coalition C) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C).1) (selected C).2))) := by
  have hlow_endpoint :
      ∀ᶠ C : ℕ in atTop,
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (largeSubset C) (threshold - epsilon)
          (cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C).1) (selected C).2)) <
            epsilon := by
    filter_upwards [hlow_card_tail, hlow_tail] with C hcardC htailC
    exact
      cutoffAffordanceProbability_iidProduct_lt_of_card_mul_upperTailMass_le
        noiseLaw (largeSubset C) (threshold - epsilon)
        (cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C).1) (selected C).2))
        hcardC htailC
  have hhigh_subset_endpoint :
      ∀ᶠ C : ℕ in atTop,
        1 - epsilon <
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (largeSubset C) (threshold + epsilon)
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C).1) (selected C).2)) := by
    filter_upwards [hhigh_product] with C hprodC
    exact
      cutoffAffordanceProbability_iidProduct_gt_one_sub_of_prod_lowerCDFMass_lt
        noiseLaw (largeSubset C) (threshold + epsilon)
        (cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C).1) (selected C).2))
        hprodC
  exact
    theorem3_coalitionAttenuationEpsilonWitness_source_clauses
      (theorem3_coalitionAttenuationEpsilonWitness_of_iidProduct_cutoff_subset_endpoint_bounds
        (noiseLaw := noiseLaw)
        (coalition := coalition)
        (largeSubset := largeSubset)
        (cutoff := fun C : ℕ =>
          cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C).1) (selected C).2))
        (epsilon := epsilon)
        (threshold := threshold)
        hlarge hlow_endpoint hhigh_subset_endpoint)

/--
Indexed selected-stable Theorem 3 source clauses from scalar low-tail controls
and a one-college high endpoint estimate.  This is the source-facing variant
of the product route when the proof has identified a single active college
whose no-crossing probability is already below the tolerance.
-/
theorem theorem3_coalitionAttenuationEpsilonWitness_source_clauses_of_iidProduct_selected_stable_cutoff_scalar_tail_exists_high_endpoint_estimates
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (selected :
      ∀ C : ℕ, { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {coalition largeSubset : ∀ C : ℕ, Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon threshold : ℝ}
    {lowTailBound : ℕ → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        CoalitionLargeSubset (coalition C) (largeSubset C) epsilon)
    (hlow_card_tail :
      ∀ᶠ C : ℕ in atTop,
        ((largeSubset C).card : ℝ) * lowTailBound C < epsilon)
    (hlow_tail :
      ∀ᶠ C : ℕ in atTop,
        ∀ c ∈ largeSubset C,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C).1) (selected C).2) c -
              (threshold - epsilon)) ≤
            lowTailBound C)
    (hhigh_exists :
      ∀ᶠ C : ℕ in atTop,
        ∃ c ∈ largeSubset C,
          AppliedModelingLib.Probability.lowerCDFMass noiseLaw
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C).1) (selected C).2) c -
              (threshold + epsilon)) <
            epsilon) :
    (∀ᶠ C : ℕ in atTop,
      CoalitionLargeSubset (coalition C) (largeSubset C) epsilon) ∧
      (∀ v, v < threshold - epsilon →
        ∀ᶠ C : ℕ in atTop,
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (largeSubset C) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C).1) (selected C).2)) < epsilon) ∧
      (∀ v, threshold + epsilon < v →
        ∀ᶠ C : ℕ in atTop,
          1 - epsilon <
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (coalition C) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C).1) (selected C).2))) := by
  have hhigh_product :
      ∀ᶠ C : ℕ in atTop,
        (∏ c ∈ largeSubset C,
          AppliedModelingLib.Probability.lowerCDFMass noiseLaw
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C).1) (selected C).2) c -
              (threshold + epsilon))) <
          epsilon := by
    filter_upwards [hhigh_exists] with C hC
    exact
      prod_lt_of_exists_lt_of_nonneg_le_one (largeSubset C)
        (fun c =>
          AppliedModelingLib.Probability.lowerCDFMass noiseLaw
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C).1) (selected C).2) c -
              (threshold + epsilon)))
        hC
        (fun c _hc => AppliedModelingLib.Probability.lowerCDFMass_nonneg noiseLaw _)
        (fun c _hc => AppliedModelingLib.Probability.lowerCDFMass_le_one noiseLaw _)
  exact
    theorem3_coalitionAttenuationEpsilonWitness_source_clauses_of_iidProduct_selected_stable_cutoff_scalar_tail_product_endpoint_estimates
      Mseq Iseq selected noiseLaw cutoffOut hlarge hlow_card_tail
      hlow_tail hhigh_product

/--
Indexed selected-stable Theorem 3 source clauses from scalar low-tail controls
and a one-college high crossing endpoint estimate.  This is the direct
upper-tail form of the preceding lower-CDF endpoint route.
-/
theorem theorem3_coalitionAttenuationEpsilonWitness_source_clauses_of_iidProduct_selected_stable_cutoff_scalar_tail_exists_high_crossing_endpoint_estimates
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (selected :
      ∀ C : ℕ, { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {coalition largeSubset : ∀ C : ℕ, Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon threshold : ℝ}
    {lowTailBound : ℕ → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        CoalitionLargeSubset (coalition C) (largeSubset C) epsilon)
    (hlow_card_tail :
      ∀ᶠ C : ℕ in atTop,
        ((largeSubset C).card : ℝ) * lowTailBound C < epsilon)
    (hlow_tail :
      ∀ᶠ C : ℕ in atTop,
        ∀ c ∈ largeSubset C,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C).1) (selected C).2) c -
              (threshold - epsilon)) ≤
            lowTailBound C)
    (hhigh_crossing :
      ∀ᶠ C : ℕ in atTop,
        ∃ c ∈ largeSubset C,
          1 - epsilon <
            AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C).1) (selected C).2) c -
                (threshold + epsilon))) :
    (∀ᶠ C : ℕ in atTop,
      CoalitionLargeSubset (coalition C) (largeSubset C) epsilon) ∧
      (∀ v, v < threshold - epsilon →
        ∀ᶠ C : ℕ in atTop,
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (largeSubset C) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C).1) (selected C).2)) < epsilon) ∧
      (∀ v, threshold + epsilon < v →
        ∀ᶠ C : ℕ in atTop,
          1 - epsilon <
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (coalition C) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C).1) (selected C).2))) := by
  have hhigh_exists :
      ∀ᶠ C : ℕ in atTop,
        ∃ c ∈ largeSubset C,
          AppliedModelingLib.Probability.lowerCDFMass noiseLaw
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C).1) (selected C).2) c -
              (threshold + epsilon)) <
            epsilon := by
    filter_upwards [hhigh_crossing] with C hC
    rcases hC with ⟨c, hc, htail⟩
    exact ⟨c, hc,
      lowerCDFMass_lt_of_one_sub_lt_upperTailMass noiseLaw htail⟩
  exact
    theorem3_coalitionAttenuationEpsilonWitness_source_clauses_of_iidProduct_selected_stable_cutoff_scalar_tail_exists_high_endpoint_estimates
      Mseq Iseq selected noiseLaw cutoffOut hlarge hlow_card_tail
      hlow_tail hhigh_exists

/--
Indexed selected-stable Theorem 3 source clauses from a scalar lower-cutoff
floor.  The low endpoint is no longer a per-college source package: cutoff
ordering and antitonicity of the upper tail derive the per-college low-tail
controls from the scalar floor estimate.
-/
theorem theorem3_coalitionAttenuationEpsilonWitness_source_clauses_of_iidProduct_selected_stable_cutoff_scalar_floor_lowTail_exists_high_crossing_endpoint_estimates
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (selected :
      ∀ C : ℕ, { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {coalition largeSubset : ∀ C : ℕ, Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon threshold : ℝ}
    {tailRate lowerCutoff : ℕ → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        CoalitionLargeSubset (coalition C) (largeSubset C) epsilon)
    (hlow_card_tail :
      ∀ᶠ C : ℕ in atTop,
        ((largeSubset C).card : ℝ) * tailRate C < epsilon)
    (hcutoff_lower :
      ∀ᶠ C : ℕ in atTop,
        ∀ c ∈ largeSubset C,
          lowerCutoff C ≤
            cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C).1) (selected C).2) c)
    (hlow_tail_floor :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Probability.upperTailMass noiseLaw
          (lowerCutoff C - (threshold - epsilon)) ≤
        tailRate C)
    (hhigh_crossing :
      ∀ᶠ C : ℕ in atTop,
        ∃ c ∈ largeSubset C,
          1 - epsilon <
            AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C).1) (selected C).2) c -
                (threshold + epsilon))) :
    (∀ᶠ C : ℕ in atTop,
      CoalitionLargeSubset (coalition C) (largeSubset C) epsilon) ∧
      (∀ v, v < threshold - epsilon →
        ∀ᶠ C : ℕ in atTop,
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (largeSubset C) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C).1) (selected C).2)) < epsilon) ∧
      (∀ v, threshold + epsilon < v →
        ∀ᶠ C : ℕ in atTop,
          1 - epsilon <
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (coalition C) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C).1) (selected C).2))) := by
  have hlow_tail :
      ∀ᶠ C : ℕ in atTop,
        ∀ c ∈ largeSubset C,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C).1) (selected C).2) c -
              (threshold - epsilon)) ≤
            tailRate C := by
    filter_upwards [hcutoff_lower, hlow_tail_floor] with
      C hcutoffC htailC c hc
    exact
      le_trans
        (AppliedModelingLib.Probability.upperTailMass_antitone noiseLaw
          (sub_le_sub_right (hcutoffC c hc) (threshold - epsilon)))
        htailC
  exact
    theorem3_coalitionAttenuationEpsilonWitness_source_clauses_of_iidProduct_selected_stable_cutoff_scalar_tail_exists_high_crossing_endpoint_estimates
      Mseq Iseq selected noiseLaw cutoffOut hlarge hlow_card_tail
      hlow_tail hhigh_crossing

/--
Theorem 4 coalition amplification target: away from a small exceptional set,
the coalition-restricted match probability converges to an effective supply.
-/
structure Theorem4CoalitionAmplificationConclusion
    (coalitionProb : ℕ → ℝ → ℝ) (effectiveSupply : ℝ)
    (regularValue : ℝ → Prop) : Prop where
  regular_values_converge :
    ∀ v, regularValue v →
      Tendsto (fun C : ℕ => coalitionProb C v) atTop (nhds effectiveSupply)

/--
Theorem 4 in the source-style epsilon form: at every regular value, the
coalition-restricted match probability is eventually within epsilon of the
effective supply.
-/
theorem theorem4_coalition_amplification_eventually_abs_bound
    {coalitionProb : ℕ → ℝ → ℝ} {effectiveSupply : ℝ}
    {regularValue : ℝ → Prop}
    (h : Theorem4CoalitionAmplificationConclusion
      coalitionProb effectiveSupply regularValue) :
    ∀ v ε, regularValue v → 0 < ε →
      ∀ᶠ C : ℕ in atTop, |coalitionProb C v - effectiveSupply| < ε := by
  intro v ε hv hε
  have hmem : effectiveSupply ∈ Set.Ioo (effectiveSupply - ε) (effectiveSupply + ε) := by
    constructor <;> linarith
  have hevent := (h.regular_values_converge v hv) (isOpen_Ioo.mem_nhds hmem)
  filter_upwards [hevent] with C hC
  rcases hC with ⟨hlo, hhi⟩
  rw [abs_sub_lt_iff]
  exact ⟨by linarith, by linarith⟩

/--
PG24 Theorem 4 source-shaped witness: a large subset `C'` of a coalition and a
large-measure regular value set on which affordance probabilities for `C'` are
epsilon-close to an effective supply `S'`.
-/
structure Theorem4CoalitionAmplificationWitness {College : Type v}
    (coalition largeSubset : Finset College)
    (affordProb : ℝ → Finset College → ℝ)
    (valueMass : Set ℝ → ℝ)
    (regularSet : Set ℝ)
    (epsilon effectiveSupply : ℝ) : Prop where
  large_subset : CoalitionLargeSubset coalition largeSubset epsilon
  regular_mass : 1 - epsilon < valueMass regularSet
  regular_values_close :
    ∀ v ∈ regularSet, |affordProb v largeSubset - effectiveSupply| < epsilon

/--
Constructor for Theorem 4's source witness from the regular set form used in
the proof.  The source phrases the exception as measure at most `epsilon` and
then equivalently works with a set of value mass greater than `1 - epsilon`.
-/
theorem theorem4_coalitionAmplificationWitness_of_regular_set
    {College : Type v} {coalition largeSubset : Finset College}
    {affordProb : ℝ → Finset College → ℝ}
    {valueMass : Set ℝ → ℝ} {epsilon effectiveSupply : ℝ}
    (hlarge : CoalitionLargeSubset coalition largeSubset epsilon)
    (regularSet : Set ℝ)
    (hmass : 1 - epsilon < valueMass regularSet)
    (hclose :
      ∀ v ∈ regularSet, |affordProb v largeSubset - effectiveSupply| < epsilon) :
    Theorem4CoalitionAmplificationWitness
      coalition largeSubset affordProb valueMass regularSet
      epsilon effectiveSupply :=
  ⟨hlarge, hmass, hclose⟩

/--
Theorem 4 exceptional-set algebra.  If a regular set and its exceptional
complement have total value mass one, and the exceptional set has mass at most
`delta < epsilon`, then the regular set has mass strictly greater than
`1 - epsilon`.
-/
theorem theorem4_regular_mass_gt_of_exception_bound
    {valueMass : Set ℝ → ℝ} {regularSet : Set ℝ} {delta epsilon : ℝ}
    (hpartition : valueMass regularSet + valueMass regularSetᶜ = 1)
    (hexception : valueMass regularSetᶜ ≤ delta)
    (hdelta : delta < epsilon) :
    1 - epsilon < valueMass regularSet := by
  linarith

/--
Theorem 4 witness from the exceptional-set form in the source theorem.  The
source phrases the conclusion as "except on a set of measure at most
epsilon"; this version uses a smaller exceptional bound `delta < epsilon` to
produce the strict large-regular-set condition used by the witness record.
-/
theorem theorem4_coalitionAmplificationWitness_of_exception_bound
    {College : Type v} {coalition largeSubset : Finset College}
    {affordProb : ℝ → Finset College → ℝ}
    {valueMass : Set ℝ → ℝ} {regularSet : Set ℝ}
    {delta epsilon effectiveSupply : ℝ}
    (hlarge : CoalitionLargeSubset coalition largeSubset epsilon)
    (hpartition : valueMass regularSet + valueMass regularSetᶜ = 1)
    (hexception : valueMass regularSetᶜ ≤ delta)
    (hdelta : delta < epsilon)
    (hclose :
      ∀ v ∈ regularSet, |affordProb v largeSubset - effectiveSupply| < epsilon) :
    Theorem4CoalitionAmplificationWitness
      coalition largeSubset affordProb valueMass regularSet
      epsilon effectiveSupply :=
  theorem4_coalitionAmplificationWitness_of_regular_set
    hlarge regularSet
    (theorem4_regular_mass_gt_of_exception_bound
      hpartition hexception hdelta)
    hclose

/--
Theorem 4 interval regularity bridge: if the restricted affordability
probability is monotone on values and the endpoint gap across a regular
interval is below `epsilon`, then every value in that interval is
`epsilon`-close to the low-endpoint effective supply.
-/
theorem theorem4_regular_values_close_of_monotone_endpoint_gap
    {College : Type v} {affordProb : ℝ → Finset College → ℝ}
    {largeSubset : Finset College} {vLow vHigh epsilon : ℝ}
    (hp_mono : Monotone (fun v => affordProb v largeSubset))
    (hgap : affordProb vHigh largeSubset - affordProb vLow largeSubset < epsilon) :
    ∀ v ∈ Set.Icc vLow vHigh,
      |affordProb v largeSubset - affordProb vLow largeSubset| < epsilon := by
  intro v hv
  rcases hv with ⟨hvLow, hvHigh⟩
  have hlow_le : affordProb vLow largeSubset ≤ affordProb v largeSubset :=
    hp_mono hvLow
  have hhigh_le : affordProb v largeSubset ≤ affordProb vHigh largeSubset :=
    hp_mono hvHigh
  have hnonneg : 0 ≤ affordProb v largeSubset - affordProb vLow largeSubset :=
    sub_nonneg.mpr hlow_le
  rw [abs_of_nonneg hnonneg]
  linarith

/--
Theorem 4 source witness from the interval form used in the proof: a
large-measure interval, monotone restricted affordability on values, and a
small endpoint gap provide the large regular set and effective supply.
-/
theorem theorem4_coalitionAmplificationWitness_of_monotone_endpoint_gap
    {College : Type v} {coalition largeSubset : Finset College}
    {affordProb : ℝ → Finset College → ℝ}
    {valueMass : Set ℝ → ℝ} {epsilon vLow vHigh : ℝ}
    (hlarge : CoalitionLargeSubset coalition largeSubset epsilon)
    (hmass : 1 - epsilon < valueMass (Set.Icc vLow vHigh))
    (hp_mono : Monotone (fun v => affordProb v largeSubset))
    (hgap : affordProb vHigh largeSubset - affordProb vLow largeSubset < epsilon) :
    Theorem4CoalitionAmplificationWitness
      coalition largeSubset affordProb valueMass (Set.Icc vLow vHigh)
      epsilon (affordProb vLow largeSubset) :=
  theorem4_coalitionAmplificationWitness_of_regular_set
    hlarge (Set.Icc vLow vHigh) hmass
    (theorem4_regular_values_close_of_monotone_endpoint_gap hp_mono hgap)

/--
Theorem 4 source clauses unpacked from the coalition witness: the chosen
subset is large, the regular value set has mass greater than `1 - epsilon`,
and the restricted affordability probability is `epsilon`-close to the
effective supply throughout that set.
-/
theorem theorem4_coalitionAmplificationWitness_source_clauses
    {College : Type v} {coalition largeSubset : Finset College}
    {affordProb : ℝ → Finset College → ℝ}
    {valueMass : Set ℝ → ℝ} {regularSet : Set ℝ}
    {epsilon effectiveSupply : ℝ}
    (h :
      Theorem4CoalitionAmplificationWitness
        coalition largeSubset affordProb valueMass regularSet
        epsilon effectiveSupply) :
    CoalitionLargeSubset coalition largeSubset epsilon ∧
      1 - epsilon < valueMass regularSet ∧
      (∀ v ∈ regularSet, |affordProb v largeSubset - effectiveSupply| < epsilon) :=
  ⟨h.large_subset, h.regular_mass, h.regular_values_close⟩

/--
Indexed source-shaped Theorem 4 witness.  This is the growing-coalition form
of the paper statement: eventually the chosen subset is large, the regular
value set has mass above `1 - epsilon`, and the restricted affordability
probability is `epsilon`-close to an effective supply on that set.
-/
structure Theorem4CoalitionAmplificationEpsilonWitnessConclusion
    {College : ℕ → Type v}
    (coalition largeSubset : ∀ C : ℕ, Finset (College C))
    (affordProb : ∀ C : ℕ, ℝ → Finset (College C) → ℝ)
    (valueMass : ∀ C : ℕ, Set ℝ → ℝ)
    (regularSet : ∀ C : ℕ, Set ℝ)
    (effectiveSupply : ℕ → ℝ)
    (epsilon : ℝ) : Prop where
  large_subset_eventually :
    ∀ᶠ C : ℕ in atTop,
      CoalitionLargeSubset (coalition C) (largeSubset C) epsilon
  regular_mass_eventually :
    ∀ᶠ C : ℕ in atTop,
      1 - epsilon < valueMass C (regularSet C)
  regular_values_close_eventually :
    ∀ᶠ C : ℕ in atTop,
      ∀ v ∈ regularSet C,
        |affordProb C v (largeSubset C) - effectiveSupply C| < epsilon

/--
Uniform source-shaped Theorem 4 witness over a family of admissible
economy/stable-matching/coalition instances at each market size.  The regular
set and effective supply may depend on the admissible instance.
-/
structure Theorem4CoalitionAmplificationUniformWitnessConclusion
    {College : ℕ → Type v} {Admissible : ℕ → Type u}
    (coalition largeSubset :
      ∀ C : ℕ, Admissible C → Finset (College C))
    (affordProb :
      ∀ C : ℕ, Admissible C → ℝ → Finset (College C) → ℝ)
    (valueMass : ∀ C : ℕ, Admissible C → Set ℝ → ℝ)
    (regularSet : ∀ C : ℕ, Admissible C → Set ℝ)
    (effectiveSupply : ∀ C : ℕ, Admissible C → ℝ)
    (epsilon : ℝ) : Prop where
  large_subset_eventually :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon
  regular_mass_eventually :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        1 - epsilon < valueMass C a (regularSet C a)
  regular_values_close_eventually :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C, ∀ v ∈ regularSet C a,
        |affordProb C a v (largeSubset C a) - effectiveSupply C a| <
          epsilon

/--
Uniform Theorem 4 witness from interval endpoint estimates.  This is the
family-indexed version of the source proof step used for the amplification
coalition theorem.
-/
theorem theorem4_coalitionAmplificationUniformWitness_of_eventual_monotone_endpoint_gap
    {College : ℕ → Type v} {Admissible : ℕ → Type u}
    {coalition largeSubset :
      ∀ C : ℕ, Admissible C → Finset (College C)}
    {affordProb :
      ∀ C : ℕ, Admissible C → ℝ → Finset (College C) → ℝ}
    {valueMass : ∀ C : ℕ, Admissible C → Set ℝ → ℝ}
    {epsilon : ℝ}
    {vLow vHigh : ∀ C : ℕ, Admissible C → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon)
    (hmass :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - epsilon < valueMass C a (Set.Icc (vLow C a) (vHigh C a)))
    (hp_mono :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          Monotone (fun v => affordProb C a v (largeSubset C a)))
    (hgap :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          affordProb C a (vHigh C a) (largeSubset C a) -
              affordProb C a (vLow C a) (largeSubset C a) <
            epsilon) :
    Theorem4CoalitionAmplificationUniformWitnessConclusion
      coalition largeSubset affordProb valueMass
      (fun C a => Set.Icc (vLow C a) (vHigh C a))
      (fun C a => affordProb C a (vLow C a) (largeSubset C a))
      epsilon := by
  refine ⟨hlarge, hmass, ?_⟩
  filter_upwards [hp_mono, hgap] with C hmonoC hgapC
  intro a v hv
  exact
    theorem4_regular_values_close_of_monotone_endpoint_gap
      (largeSubset := largeSubset C a)
      (affordProb := affordProb C a)
      (vLow := vLow C a) (vHigh := vHigh C a)
      (epsilon := epsilon)
      (hmonoC a) (hgapC a) v hv

/--
Uniform concrete iid-product cutoff specialization of the Theorem 4 interval
endpoint route.  Value monotonicity on each large subset is derived from
cutoff-affordance monotonicity.
-/
theorem theorem4_coalitionAmplificationUniformWitness_of_iidProduct_cutoff_monotone_endpoint_gap
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {Admissible : ℕ → Type u}
    {coalition largeSubset :
      ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    {cutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ}
    {valueMass : ∀ C : ℕ, Admissible C → Set ℝ → ℝ}
    {epsilon : ℝ}
    {vLow vHigh : ∀ C : ℕ, Admissible C → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon)
    (hmass :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - epsilon < valueMass C a (Set.Icc (vLow C a) (vHigh C a)))
    (hgap :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) (vHigh C a) (cutoff C a) -
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) (vLow C a) (cutoff C a) <
            epsilon) :
    Theorem4CoalitionAmplificationUniformWitnessConclusion
      coalition largeSubset
      (fun C : ℕ => fun a : Admissible C => fun v : ℝ =>
        fun active : Finset (Fin (C + 1)) =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            active v (cutoff C a))
      valueMass
      (fun C a => Set.Icc (vLow C a) (vHigh C a))
      (fun C a =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (largeSubset C a) (vLow C a) (cutoff C a))
      epsilon := by
  have hp_mono :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          Monotone (fun v =>
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) v (cutoff C a)) := by
    filter_upwards with C
    intro a v w hvw
    exact
      cutoffAffordanceProbability_mono_value
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) hvw
  exact
    theorem4_coalitionAmplificationUniformWitness_of_eventual_monotone_endpoint_gap
      hlarge hmass hp_mono hgap

/--
Uniform concrete iid-product Theorem 4 over admissible instances carrying
selected stable matchings.  The A-L bridge supplies the market-clearing cutoff
for each selected stable matching, and endpoint-gap estimates stated for all
market-clearing cutoffs are specialized uniformly over admissible instances.
-/
theorem theorem4_coalitionAmplificationUniformWitness_of_iidProduct_stable_cutoff_monotone_endpoint_gap
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {coalition largeSubset :
      ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {valueMass : ∀ C : ℕ, Admissible C → Set ℝ → ℝ}
    {epsilon : ℝ}
    {vLow vHigh : ∀ C : ℕ, Admissible C → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon)
    (hmass :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - epsilon < valueMass C a (Set.Icc (vLow C a) (vHigh C a)))
    (hgap :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
            cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) (vHigh C a) (cutoffOut C P) -
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) (vLow C a) (cutoffOut C P) <
              epsilon) :
    Theorem4CoalitionAmplificationUniformWitnessConclusion
      coalition largeSubset
      (fun C : ℕ => fun a : Admissible C => fun v : ℝ =>
        fun active : Finset (Fin (C + 1)) =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            active v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2)))
      valueMass
      (fun C a => Set.Icc (vLow C a) (vHigh C a))
      (fun C a =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (largeSubset C a) (vLow C a)
          (cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C a).1) (selected C a).2)))
      epsilon := by
  have hmc :
      ∀ C : ℕ, ∀ a : Admissible C,
        (Mseq C).MarketClearing
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C a).1) (selected C a).2) := by
    intro C a
    exact
      (Iseq C).marketClearingCutoffOfStable_marketClearing
        (μ := (selected C a).1) (selected C a).2
  refine
    theorem4_coalitionAmplificationUniformWitness_of_iidProduct_cutoff_monotone_endpoint_gap
      (noiseLaw := noiseLaw)
      (coalition := coalition)
      (largeSubset := largeSubset)
      (cutoff := fun C : ℕ => fun a : Admissible C =>
        cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C a).1) (selected C a).2))
      (valueMass := valueMass)
      (epsilon := epsilon)
      (vLow := vLow)
      (vHigh := vHigh)
      hlarge hmass ?_
  filter_upwards [hgap] with C hC a
  exact hC a _ (hmc C a)

/--
Uniform concrete iid-product Theorem 4 over admissible selected stable
matchings, with the endpoint-gap estimate stated only at the selected A-L
cutoff for each admissible instance.
-/
theorem theorem4_coalitionAmplificationUniformWitness_of_iidProduct_selected_stable_cutoff_monotone_endpoint_gap
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {coalition largeSubset :
      ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {valueMass : ∀ C : ℕ, Admissible C → Set ℝ → ℝ}
    {epsilon : ℝ}
    {vLow vHigh : ∀ C : ℕ, Admissible C → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon)
    (hmass :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - epsilon < valueMass C a (Set.Icc (vLow C a) (vHigh C a)))
    (hgap :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) (vHigh C a)
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2)) -
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) (vLow C a)
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2)) <
            epsilon) :
    Theorem4CoalitionAmplificationUniformWitnessConclusion
      coalition largeSubset
      (fun C : ℕ => fun a : Admissible C => fun v : ℝ =>
        fun active : Finset (Fin (C + 1)) =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            active v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2)))
      valueMass
      (fun C a => Set.Icc (vLow C a) (vHigh C a))
      (fun C a =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (largeSubset C a) (vLow C a)
          (cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C a).1) (selected C a).2)))
      epsilon :=
  theorem4_coalitionAmplificationUniformWitness_of_iidProduct_cutoff_monotone_endpoint_gap
    (noiseLaw := noiseLaw)
    (coalition := coalition)
    (largeSubset := largeSubset)
    (cutoff := fun C : ℕ => fun a : Admissible C =>
      cutoffOut C
        ((Iseq C).marketClearingCutoffOfStable
          (μ := (selected C a).1) (selected C a).2))
    (valueMass := valueMass)
    (epsilon := epsilon)
    (vLow := vLow)
    (vHigh := vHigh)
    hlarge hmass hgap

/--
Uniform Theorem 4 source clauses unpacked from the admissible-instance witness.
-/
theorem theorem4_coalitionAmplificationUniformWitness_source_clauses
    {College : ℕ → Type v} {Admissible : ℕ → Type u}
    {coalition largeSubset :
      ∀ C : ℕ, Admissible C → Finset (College C)}
    {affordProb :
      ∀ C : ℕ, Admissible C → ℝ → Finset (College C) → ℝ}
    {valueMass : ∀ C : ℕ, Admissible C → Set ℝ → ℝ}
    {regularSet : ∀ C : ℕ, Admissible C → Set ℝ}
    {effectiveSupply : ∀ C : ℕ, Admissible C → ℝ}
    {epsilon : ℝ}
    (h :
      Theorem4CoalitionAmplificationUniformWitnessConclusion
        coalition largeSubset affordProb valueMass regularSet
        effectiveSupply epsilon) :
    (∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - epsilon < valueMass C a (regularSet C a)) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v ∈ regularSet C a,
          |affordProb C a v (largeSubset C a) - effectiveSupply C a| <
            epsilon) :=
  ⟨h.large_subset_eventually,
    h.regular_mass_eventually,
    h.regular_values_close_eventually⟩

/--
Uniform Theorem 4 existential source clauses.  This packages the chosen large
subset, regular value set, and effective supply in the exact existential shape
of the paper's coalition amplification theorem.
-/
theorem theorem4_coalitionAmplificationUniformWitness_existential_source_clauses
    {College : ℕ → Type v} {Admissible : ℕ → Type u}
    {coalition largeSubset :
      ∀ C : ℕ, Admissible C → Finset (College C)}
    {affordProb :
      ∀ C : ℕ, Admissible C → ℝ → Finset (College C) → ℝ}
    {valueMass : ∀ C : ℕ, Admissible C → Set ℝ → ℝ}
    {regularSet : ∀ C : ℕ, Admissible C → Set ℝ}
    {effectiveSupply : ∀ C : ℕ, Admissible C → ℝ}
    {epsilon : ℝ}
    (h :
      Theorem4CoalitionAmplificationUniformWitnessConclusion
        coalition largeSubset affordProb valueMass regularSet
        effectiveSupply epsilon) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ effectiveSupply' : ℝ,
        ∃ largeSubset' : Finset (College C),
        ∃ regularSet' : Set ℝ,
          CoalitionLargeSubset (coalition C a) largeSubset' epsilon ∧
            1 - epsilon < valueMass C a regularSet' ∧
            (∀ v ∈ regularSet',
              |affordProb C a v largeSubset' - effectiveSupply'| < epsilon) := by
  filter_upwards
    [h.large_subset_eventually, h.regular_mass_eventually,
      h.regular_values_close_eventually] with
    C hlargeC hmassC hcloseC a
  exact
    ⟨effectiveSupply C a, largeSubset C a, regularSet C a,
      hlargeC a, hmassC a, hcloseC a⟩

/--
Concrete uniform selected-stable Theorem 4 source clauses.  This composes the
selected-stable cutoff endpoint route with the source-clause projection, so
the paper-facing conclusion is stated directly for every admissible stable
matching instance.
-/
theorem theorem4_coalitionAmplificationUniformWitness_source_clauses_of_iidProduct_stable_cutoff_monotone_endpoint_gap
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {coalition largeSubset :
      ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {valueMass : ∀ C : ℕ, Admissible C → Set ℝ → ℝ}
    {epsilon : ℝ}
    {vLow vHigh : ∀ C : ℕ, Admissible C → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon)
    (hmass :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - epsilon < valueMass C a (Set.Icc (vLow C a) (vHigh C a)))
    (hgap :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
            cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) (vHigh C a) (cutoffOut C P) -
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) (vLow C a) (cutoffOut C P) <
              epsilon) :
    (∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - epsilon < valueMass C a (Set.Icc (vLow C a) (vHigh C a))) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v ∈ Set.Icc (vLow C a) (vHigh C a),
          |cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) -
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) (vLow C a)
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))| < epsilon) := by
  have h :=
    theorem4_coalitionAmplificationUniformWitness_of_iidProduct_stable_cutoff_monotone_endpoint_gap
      Mseq Iseq selected noiseLaw cutoffOut hlarge hmass hgap
  exact theorem4_coalitionAmplificationUniformWitness_source_clauses h

/--
Concrete uniform selected-stable Theorem 4 source clauses with the endpoint
gap stated only at the selected A-L cutoff for each admissible stable matching
instance.  This is the source-clause version of the narrowed selected-cutoff
witness route above.
-/
theorem theorem4_coalitionAmplificationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_monotone_endpoint_gap
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {coalition largeSubset :
      ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {valueMass : ∀ C : ℕ, Admissible C → Set ℝ → ℝ}
    {epsilon : ℝ}
    {vLow vHigh : ∀ C : ℕ, Admissible C → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon)
    (hmass :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - epsilon < valueMass C a (Set.Icc (vLow C a) (vHigh C a)))
    (hgap :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) (vHigh C a)
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2)) -
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) (vLow C a)
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2)) <
            epsilon) :
    (∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - epsilon < valueMass C a (Set.Icc (vLow C a) (vHigh C a))) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v ∈ Set.Icc (vLow C a) (vHigh C a),
          |cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) -
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) (vLow C a)
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))| < epsilon) := by
  have h :=
    theorem4_coalitionAmplificationUniformWitness_of_iidProduct_selected_stable_cutoff_monotone_endpoint_gap
      Mseq Iseq selected noiseLaw cutoffOut hlarge hmass hgap
  exact theorem4_coalitionAmplificationUniformWitness_source_clauses h

/--
Uniform selected-stable Theorem 4 source clauses from long-tail endpoint
estimates.  The endpoint gap is derived internally from the existing uniform
long-tail product estimate and the strict side conditions supplied by the
diverging cutoff floor.
-/
theorem theorem4_coalitionAmplificationUniformWitness_source_clauses_of_iidProduct_stable_cutoff_upperTail_longTail_endpoint_estimates_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {coalition largeSubset :
      ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {valueMass : ∀ C : ℕ, Admissible C → Set ℝ → ℝ}
    {tol eps sigma vLow vHigh : ℝ} {lowerCutoff : ℕ → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (coalition C a) (largeSubset C a) tol)
    (hmass :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - tol < valueMass C a (Set.Icc vLow vHigh))
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_nonneg : 0 ≤ sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol)
    (hlower_atTop :
      Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop)
    (hcutoff_lower :
      ∀ᶠ n : ℕ in atTop,
        ∀ a : Admissible n,
          ∀ P : (Mseq n).Cutoff, (Mseq n).MarketClearing P →
            ∀ c ∈ largeSubset n a, lowerCutoff n ≤ cutoffOut n P c)
    (hhigh_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ a : Admissible n,
          ∀ P : (Mseq n).Cutoff, (Mseq n).MarketClearing P →
            ∀ c ∈ largeSubset n a,
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoffOut n P c - vHigh) ≤
                sigma / ((n + 1 : ℕ) : ℝ)) :
    (∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        CoalitionLargeSubset (coalition C a) (largeSubset C a) tol) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - tol < valueMass C a (Set.Icc vLow vHigh)) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v ∈ Set.Icc vLow vHigh,
          |cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) -
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) vLow
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))| < tol) := by
  let selectedCutoff : ∀ C : ℕ, Admissible C → (Mseq C).Cutoff :=
    fun C a =>
      (Iseq C).marketClearingCutoffOfStable
        (μ := (selected C a).1) (selected C a).2
  have hmc :
      ∀ C : ℕ, ∀ a : Admissible C,
        (Mseq C).MarketClearing (selectedCutoff C a) := by
    intro C a
    exact
      (Iseq C).marketClearingCutoffOfStable_marketClearing
        (μ := (selected C a).1) (selected C a).2
  let selectedCutoffOut :
      ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ :=
    fun C a => cutoffOut C (selectedCutoff C a)
  have hcutoff_lower_selected :
      ∀ᶠ n : ℕ in atTop,
        ∀ a : Admissible n, ∀ c ∈ largeSubset n a,
          lowerCutoff n ≤ selectedCutoffOut n a c := by
    filter_upwards [hcutoff_lower] with n hn a c hc
    exact hn a (selectedCutoff n a) (hmc n a) c hc
  have hhigh_le_selected :
      ∀ᶠ n : ℕ in atTop,
        ∀ a : Admissible n, ∀ c ∈ largeSubset n a,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
              (selectedCutoffOut n a c - vHigh) ≤
            sigma / ((n + 1 : ℕ) : ℝ) := by
    filter_upwards [hhigh_le_sigma_div] with n hn a c hc
    exact hn a (selectedCutoff n a) (hmc n a) c hc
  have hstrict :=
    upperTailMass_strict_side_conditions_of_longTail_cutoff_floor
      (Admissible := Admissible)
      (noiseLaw := noiseLaw)
      (hlong := hlong)
      (active := largeSubset)
      (cutoff := selectedCutoffOut)
      (vLow := vLow)
      (vHigh := vHigh)
      (lowerCutoff := lowerCutoff)
      hv hlower_atTop hcutoff_lower_selected
  have hdiff :
      ∀ᶠ n : ℕ in atTop,
        ∀ a : Admissible n,
          independentAffordanceProbability
              (largeSubset n a)
              (fun c =>
                AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (selectedCutoffOut n a c - vHigh)) -
            independentAffordanceProbability
              (largeSubset n a)
              (fun c =>
                AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (selectedCutoffOut n a c - vLow)) ≤
            1 - Real.exp (-(2 * eps * sigma)) :=
    independentAffordanceProbability_difference_uniform_eventually_le_exp_error_of_longTailed_highCrossingBound
      (Admissible := Admissible)
      (survival := AppliedModelingLib.Probability.upperTailMass noiseLaw)
      hlong hv heps_pos heps_le_one hsigma_nonneg hlower_atTop
      hcutoff_lower_selected hstrict.1 hhigh_le_selected hstrict.2
  have hgap :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) vHigh (selectedCutoffOut C a) -
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) vLow (selectedCutoffOut C a) <
            tol := by
    filter_upwards [hdiff] with C hC a
    have hbridge_high :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (largeSubset C a) vHigh (selectedCutoffOut C a)
    have hbridge_low :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (largeSubset C a) vLow (selectedCutoffOut C a)
    exact
      lt_of_le_of_lt
        (by simpa [hbridge_high, hbridge_low] using hC a)
        herror_lt
  have h :=
    theorem4_coalitionAmplificationUniformWitness_of_iidProduct_cutoff_monotone_endpoint_gap
      (noiseLaw := noiseLaw)
      (coalition := coalition)
      (largeSubset := largeSubset)
      (cutoff := selectedCutoffOut)
      (valueMass := valueMass)
      (epsilon := tol)
      (vLow := fun _C : ℕ => fun _a : Admissible _C => vLow)
      (vHigh := fun _C : ℕ => fun _a : Admissible _C => vHigh)
      hlarge hmass hgap
  exact theorem4_coalitionAmplificationUniformWitness_source_clauses h

/--
Uniform selected-stable Theorem 4 source clauses from long-tail endpoint
estimates, with cutoff-floor and high-tail estimates required only at the
selected A-L cutoff for each admissible stable matching instance.
-/
theorem theorem4_coalitionAmplificationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_upperTail_longTail_endpoint_estimates_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {coalition largeSubset :
      ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {valueMass : ∀ C : ℕ, Admissible C → Set ℝ → ℝ}
    {tol eps sigma vLow vHigh : ℝ} {lowerCutoff : ℕ → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (coalition C a) (largeSubset C a) tol)
    (hmass :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - tol < valueMass C a (Set.Icc vLow vHigh))
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_nonneg : 0 ≤ sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol)
    (hlower_atTop :
      Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop)
    (hcutoff_lower :
      ∀ᶠ n : ℕ in atTop,
        ∀ a : Admissible n, ∀ c ∈ largeSubset n a,
          lowerCutoff n ≤
            cutoffOut n
              ((Iseq n).marketClearingCutoffOfStable
                (μ := (selected n a).1) (selected n a).2) c)
    (hhigh_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ a : Admissible n, ∀ c ∈ largeSubset n a,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoffOut n
                ((Iseq n).marketClearingCutoffOfStable
                  (μ := (selected n a).1) (selected n a).2) c - vHigh) ≤
            sigma / ((n + 1 : ℕ) : ℝ)) :
    (∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        CoalitionLargeSubset (coalition C a) (largeSubset C a) tol) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - tol < valueMass C a (Set.Icc vLow vHigh)) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v ∈ Set.Icc vLow vHigh,
          |cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) -
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) vLow
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))| < tol) := by
  let selectedCutoffOut :
      ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ :=
    fun C a =>
      cutoffOut C
        ((Iseq C).marketClearingCutoffOfStable
          (μ := (selected C a).1) (selected C a).2)
  have hstrict :=
    upperTailMass_strict_side_conditions_of_longTail_cutoff_floor
      (Admissible := Admissible)
      (noiseLaw := noiseLaw)
      (hlong := hlong)
      (active := largeSubset)
      (cutoff := selectedCutoffOut)
      (vLow := vLow)
      (vHigh := vHigh)
      (lowerCutoff := lowerCutoff)
      hv hlower_atTop hcutoff_lower
  have hdiff :
      ∀ᶠ n : ℕ in atTop,
        ∀ a : Admissible n,
          independentAffordanceProbability
              (largeSubset n a)
              (fun c =>
                AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (selectedCutoffOut n a c - vHigh)) -
            independentAffordanceProbability
              (largeSubset n a)
              (fun c =>
                AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (selectedCutoffOut n a c - vLow)) ≤
            1 - Real.exp (-(2 * eps * sigma)) :=
    independentAffordanceProbability_difference_uniform_eventually_le_exp_error_of_longTailed_highCrossingBound
      (Admissible := Admissible)
      (survival := AppliedModelingLib.Probability.upperTailMass noiseLaw)
      hlong hv heps_pos heps_le_one hsigma_nonneg hlower_atTop
      hcutoff_lower hstrict.1 hhigh_le_sigma_div hstrict.2
  have hgap :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) vHigh (selectedCutoffOut C a) -
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) vLow (selectedCutoffOut C a) <
            tol := by
    filter_upwards [hdiff] with C hC a
    have hbridge_high :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (largeSubset C a) vHigh (selectedCutoffOut C a)
    have hbridge_low :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (largeSubset C a) vLow (selectedCutoffOut C a)
    exact
      lt_of_le_of_lt
        (by simpa [hbridge_high, hbridge_low] using hC a)
        herror_lt
  exact
    theorem4_coalitionAmplificationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_monotone_endpoint_gap
      (vLow := fun _C : ℕ => fun _a : Admissible _C => vLow)
      (vHigh := fun _C : ℕ => fun _a : Admissible _C => vHigh)
      Mseq Iseq selected noiseLaw cutoffOut hlarge hmass hgap

/--
Uniform selected-stable Theorem 4 source clauses from the high-tail endpoint
rate alone.

This variant avoids a separate scalar lower-cutoff divergence premise.  For
upper-tail probabilities, the long-tail positivity and the high-endpoint
`sigma/(n+1)` rate force every non-vacuous selected cutoff into the tail
region needed by the long-tail product estimate.
-/
theorem theorem4_coalitionAmplificationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_upperTail_longTail_endpoint_estimates_from_high_tail_rate
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {coalition largeSubset :
      ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {valueMass : ∀ C : ℕ, Admissible C → Set ℝ → ℝ}
    {tol eps sigma vLow vHigh : ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (coalition C a) (largeSubset C a) tol)
    (hmass :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - tol < valueMass C a (Set.Icc vLow vHigh))
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_nonneg : 0 ≤ sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol)
    (hhigh_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ a : Admissible n, ∀ c ∈ largeSubset n a,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoffOut n
                ((Iseq n).marketClearingCutoffOfStable
                  (μ := (selected n a).1) (selected n a).2) c - vHigh) ≤
            sigma / ((n + 1 : ℕ) : ℝ)) :
    (∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        CoalitionLargeSubset (coalition C a) (largeSubset C a) tol) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - tol < valueMass C a (Set.Icc vLow vHigh)) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v ∈ Set.Icc vLow vHigh,
          |cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) -
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) vLow
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))| < tol) := by
  let selectedCutoffOut :
      ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ :=
    fun C a =>
      cutoffOut C
        ((Iseq C).marketClearingCutoffOfStable
          (μ := (selected C a).1) (selected C a).2)
  have hdiff :
      ∀ᶠ n : ℕ in atTop,
        ∀ a : Admissible n,
          independentAffordanceProbability
              (largeSubset n a)
              (fun c =>
                AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (selectedCutoffOut n a c - vHigh)) -
            independentAffordanceProbability
              (largeSubset n a)
              (fun c =>
                AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (selectedCutoffOut n a c - vLow)) ≤
            1 - Real.exp (-(2 * eps * sigma)) :=
    independentAffordanceProbability_difference_uniform_eventually_le_exp_error_of_upperTailMass_longTailed_highCrossingBound
      (Admissible := Admissible)
      noiseLaw hlong hv heps_pos heps_le_one hsigma_nonneg
      hhigh_le_sigma_div
  have hgap :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) vHigh (selectedCutoffOut C a) -
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) vLow (selectedCutoffOut C a) <
            tol := by
    filter_upwards [hdiff] with C hC a
    have hbridge_high :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (largeSubset C a) vHigh (selectedCutoffOut C a)
    have hbridge_low :=
      cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
        noiseLaw (largeSubset C a) vLow (selectedCutoffOut C a)
    exact
      lt_of_le_of_lt
        (by simpa [hbridge_high, hbridge_low] using hC a)
        herror_lt
  exact
    theorem4_coalitionAmplificationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_monotone_endpoint_gap
      (vLow := fun _C : ℕ => fun _a : Admissible _C => vLow)
      (vHigh := fun _C : ℕ => fun _a : Admissible _C => vHigh)
      Mseq Iseq selected noiseLaw cutoffOut hlarge hmass hgap

/--
Uniform selected-stable Theorem 4 source clauses with the high-endpoint tail
estimate stated at the scalar lower cutoff floor.  Ordered large-subset
cutoffs and antitonicity of the upper tail derive the per-college high-tail
premise used by the long-tail product estimate.
-/
theorem theorem4_coalitionAmplificationUniformWitness_source_clauses_of_iidProduct_stable_cutoff_scalar_tail_upperTail_longTail_endpoint_estimates_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {coalition largeSubset :
      ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {valueMass : ∀ C : ℕ, Admissible C → Set ℝ → ℝ}
    {tol eps sigma vLow vHigh : ℝ} {lowerCutoff : ℕ → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (coalition C a) (largeSubset C a) tol)
    (hmass :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - tol < valueMass C a (Set.Icc vLow vHigh))
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_nonneg : 0 ≤ sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol)
    (hlower_atTop :
      Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop)
    (hcutoff_lower :
      ∀ᶠ n : ℕ in atTop,
        ∀ a : Admissible n,
          ∀ P : (Mseq n).Cutoff, (Mseq n).MarketClearing P →
            ∀ c ∈ largeSubset n a, lowerCutoff n ≤ cutoffOut n P c)
    (hhigh_floor_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ _a : Admissible n,
          ∀ P : (Mseq n).Cutoff, (Mseq n).MarketClearing P →
            AppliedModelingLib.Probability.upperTailMass noiseLaw
              (lowerCutoff n - vHigh) ≤
              sigma / ((n + 1 : ℕ) : ℝ)) :
    (∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        CoalitionLargeSubset (coalition C a) (largeSubset C a) tol) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - tol < valueMass C a (Set.Icc vLow vHigh)) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v ∈ Set.Icc vLow vHigh,
          |cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) -
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) vLow
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))| < tol) := by
  have hhigh_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ a : Admissible n,
          ∀ P : (Mseq n).Cutoff, (Mseq n).MarketClearing P →
            ∀ c ∈ largeSubset n a,
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoffOut n P c - vHigh) ≤
                sigma / ((n + 1 : ℕ) : ℝ) := by
    filter_upwards [hcutoff_lower, hhigh_floor_le_sigma_div] with
      n hcutoff_n htail_n a P hP c hc
    exact
      le_trans
        (AppliedModelingLib.Probability.upperTailMass_antitone noiseLaw
          (sub_le_sub_right (hcutoff_n a P hP c hc) vHigh))
        (htail_n a P hP)
  exact
    theorem4_coalitionAmplificationUniformWitness_source_clauses_of_iidProduct_stable_cutoff_upperTail_longTail_endpoint_estimates_strict_derived
      Mseq Iseq selected noiseLaw hlong cutoffOut hlarge hmass hv
      heps_pos heps_le_one hsigma_nonneg herror_lt hlower_atTop
      hcutoff_lower hhigh_le_sigma_div

/--
Uniform selected-stable Theorem 4 source clauses with scalar high-tail input
at the lower cutoff floor, requiring cutoff-floor ordering only at the
selected A-L cutoff for each admissible stable matching instance.
-/
theorem theorem4_coalitionAmplificationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_scalar_tail_upperTail_longTail_endpoint_estimates_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {coalition largeSubset :
      ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {valueMass : ∀ C : ℕ, Admissible C → Set ℝ → ℝ}
    {tol eps sigma vLow vHigh : ℝ} {lowerCutoff : ℕ → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (coalition C a) (largeSubset C a) tol)
    (hmass :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - tol < valueMass C a (Set.Icc vLow vHigh))
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_nonneg : 0 ≤ sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol)
    (hlower_atTop :
      Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop)
    (hcutoff_lower :
      ∀ᶠ n : ℕ in atTop,
        ∀ a : Admissible n, ∀ c ∈ largeSubset n a,
          lowerCutoff n ≤
            cutoffOut n
              ((Iseq n).marketClearingCutoffOfStable
                (μ := (selected n a).1) (selected n a).2) c)
    (hhigh_floor_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ _a : Admissible n,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (lowerCutoff n - vHigh) ≤
            sigma / ((n + 1 : ℕ) : ℝ)) :
    (∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        CoalitionLargeSubset (coalition C a) (largeSubset C a) tol) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - tol < valueMass C a (Set.Icc vLow vHigh)) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v ∈ Set.Icc vLow vHigh,
          |cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) -
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) vLow
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))| < tol) := by
  have hhigh_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ a : Admissible n, ∀ c ∈ largeSubset n a,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoffOut n
                ((Iseq n).marketClearingCutoffOfStable
                  (μ := (selected n a).1) (selected n a).2) c - vHigh) ≤
            sigma / ((n + 1 : ℕ) : ℝ) := by
    filter_upwards [hcutoff_lower, hhigh_floor_le_sigma_div] with
      n hcutoff_n htail_n a c hc
    exact
      le_trans
        (AppliedModelingLib.Probability.upperTailMass_antitone noiseLaw
          (sub_le_sub_right (hcutoff_n a c hc) vHigh))
        (htail_n a)
  exact
    theorem4_coalitionAmplificationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_upperTail_longTail_endpoint_estimates_strict_derived
      Mseq Iseq selected noiseLaw hlong cutoffOut hlarge hmass hv
      heps_pos heps_le_one hsigma_nonneg herror_lt hlower_atTop
      hcutoff_lower hhigh_le_sigma_div

/--
Uniform selected-stable Theorem 4 source clauses with scalar high-tail input,
using the high-tail rate to derive the needed tail-region condition.
-/
theorem theorem4_coalitionAmplificationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_scalar_tail_upperTail_longTail_endpoint_estimates_from_high_tail_rate
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {coalition largeSubset :
      ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {valueMass : ∀ C : ℕ, Admissible C → Set ℝ → ℝ}
    {tol eps sigma vLow vHigh : ℝ} {lowerCutoff : ℕ → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (coalition C a) (largeSubset C a) tol)
    (hmass :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - tol < valueMass C a (Set.Icc vLow vHigh))
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_nonneg : 0 ≤ sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol)
    (hcutoff_lower :
      ∀ᶠ n : ℕ in atTop,
        ∀ a : Admissible n, ∀ c ∈ largeSubset n a,
          lowerCutoff n ≤
            cutoffOut n
              ((Iseq n).marketClearingCutoffOfStable
                (μ := (selected n a).1) (selected n a).2) c)
    (hhigh_floor_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ _a : Admissible n,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (lowerCutoff n - vHigh) ≤
            sigma / ((n + 1 : ℕ) : ℝ)) :
    (∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        CoalitionLargeSubset (coalition C a) (largeSubset C a) tol) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - tol < valueMass C a (Set.Icc vLow vHigh)) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v ∈ Set.Icc vLow vHigh,
          |cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) -
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) vLow
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))| < tol) := by
  have hhigh_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ a : Admissible n, ∀ c ∈ largeSubset n a,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoffOut n
                ((Iseq n).marketClearingCutoffOfStable
                  (μ := (selected n a).1) (selected n a).2) c - vHigh) ≤
            sigma / ((n + 1 : ℕ) : ℝ) := by
    filter_upwards [hcutoff_lower, hhigh_floor_le_sigma_div] with
      n hcutoff_n htail_n a c hc
    exact
      le_trans
        (AppliedModelingLib.Probability.upperTailMass_antitone noiseLaw
          (sub_le_sub_right (hcutoff_n a c hc) vHigh))
        (htail_n a)
  exact
    theorem4_coalitionAmplificationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_upperTail_longTail_endpoint_estimates_from_high_tail_rate
      Mseq Iseq selected noiseLaw hlong cutoffOut hlarge hmass hv
      heps_pos heps_le_one hsigma_nonneg herror_lt hhigh_le_sigma_div

/--
The floor split has a strictly positive first-order tail mass.  This is the
numeric part of the Theorem 4 capacity argument: the first coordinate after
the deleted `floor (delta * (C + 1))` block yields an exponent larger than
`delta * tau` at a per-coordinate rate `tau / (C + 1)`.
-/
theorem pg24_epsilonFloorSplitIndex_add_one_mul_const_div_nat_succ_gt
    {delta tau : ℝ} (hdelta_pos : 0 < delta) (htau_pos : 0 < tau)
    (C : ℕ) :
    delta * tau <
      (((epsilonFloorSplitIndex delta C + 1 : ℕ) : ℝ) *
        (tau / (((C + 1 : ℕ) : ℝ)))) := by
  have hn_pos : 0 < (((C + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos C
  have hfloor_lt :
      delta * (((C + 1 : ℕ) : ℝ)) <
        ((epsilonFloorSplitIndex delta C + 1 : ℕ) : ℝ) := by
    simpa [epsilonFloorSplitIndex, Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one
        (delta * (((C + 1 : ℕ) : ℝ))))
  have htail_pos : 0 < tau / (((C + 1 : ℕ) : ℝ)) :=
    div_pos htau_pos hn_pos
  have hmul_lt :
      (delta * (((C + 1 : ℕ) : ℝ)) *
          (tau / (((C + 1 : ℕ) : ℝ)))) <
        (((epsilonFloorSplitIndex delta C + 1 : ℕ) : ℝ) *
          (tau / (((C + 1 : ℕ) : ℝ)))) :=
    mul_lt_mul_of_pos_right hfloor_lt htail_pos
  have hleft :
      delta * (((C + 1 : ℕ) : ℝ)) *
          (tau / (((C + 1 : ℕ) : ℝ))) =
        delta * tau := by
    field_simp [ne_of_gt hn_pos]
  have hmul_lt' := hmul_lt
  rw [hleft] at hmul_lt'
  simpa [Nat.cast_add, Nat.cast_one] using hmul_lt'

/--
An explicit scalar lower bound for the strict upper tail, together with a
static supply gap, proves the split-index crossing inequality used in the
Theorem 4 low-cutoff capacity contradiction.  No ordering or relabeling of
the cutoff vector is used here.
-/
theorem pg24_eventually_upperTail_split_crossing_of_scalar_lower_static_gap
    {Admissible : ℕ → Type u}
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {delta tau totalSupply : ℝ}
    {lowerCutoff eventValue : ∀ C : ℕ, Admissible C → ℝ}
    (hdelta_pos : 0 < delta) (htau_pos : 0 < tau)
    (hgap : totalSupply < 1 - Real.exp (-(delta * tau)))
    (htail :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          tau / (((C + 1 : ℕ) : ℝ)) ≤
            AppliedModelingLib.Probability.upperTailMass noiseLaw
              (lowerCutoff C a - eventValue C a)) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        totalSupply <
          1 -
            (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
              (lowerCutoff C a - eventValue C a)) ^
              (epsilonFloorSplitIndex delta C + 1) := by
  filter_upwards [htail] with C htailC a
  let tail : ℝ :=
    AppliedModelingLib.Probability.upperTailMass noiseLaw
      (lowerCutoff C a - eventValue C a)
  have htail_le_one : tail ≤ 1 := by
    simpa [tail] using
      (AppliedModelingLib.Probability.upperTailMass_le_one noiseLaw
        (lowerCutoff C a - eventValue C a))
  have htail_lower : tau / (((C + 1 : ℕ) : ℝ)) ≤ tail := by
    simpa [tail] using htailC a
  have hbase_nonneg : 0 ≤ 1 - tail := by
    linarith
  have hbase_le_exp : 1 - tail ≤ Real.exp (-tail) :=
    Real.one_sub_le_exp_neg tail
  have hpow_le_exp :
      (1 - tail) ^ (epsilonFloorSplitIndex delta C + 1) ≤
        Real.exp
          (-(((epsilonFloorSplitIndex delta C + 1 : ℕ) : ℝ) * tail)) := by
    have hpow :
        (1 - tail) ^ (epsilonFloorSplitIndex delta C + 1) ≤
          (Real.exp (-tail)) ^ (epsilonFloorSplitIndex delta C + 1) :=
      pow_le_pow_left₀ hbase_nonneg hbase_le_exp
        (epsilonFloorSplitIndex delta C + 1)
    have hexp_pow :
        (Real.exp (-tail)) ^ (epsilonFloorSplitIndex delta C + 1) =
          Real.exp
            (-(((epsilonFloorSplitIndex delta C + 1 : ℕ) : ℝ) * tail)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    simpa [hexp_pow] using hpow
  have hfloor_product :
      delta * tau <
        (((epsilonFloorSplitIndex delta C + 1 : ℕ) : ℝ) *
          (tau / (((C + 1 : ℕ) : ℝ)))) :=
    pg24_epsilonFloorSplitIndex_add_one_mul_const_div_nat_succ_gt
      hdelta_pos htau_pos C
  have hscaled_tail :
      (((epsilonFloorSplitIndex delta C + 1 : ℕ) : ℝ) *
          (tau / (((C + 1 : ℕ) : ℝ)))) ≤
        (((epsilonFloorSplitIndex delta C + 1 : ℕ) : ℝ) * tail) :=
    mul_le_mul_of_nonneg_left htail_lower (Nat.cast_nonneg _)
  have hexp_le :
      Real.exp
          (-(((epsilonFloorSplitIndex delta C + 1 : ℕ) : ℝ) * tail)) ≤
        Real.exp (-(delta * tau)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hpow_le :
      (1 - tail) ^ (epsilonFloorSplitIndex delta C + 1) ≤
        Real.exp (-(delta * tau)) :=
    le_trans hpow_le_exp hexp_le
  have hcross :
      totalSupply <
        1 - (1 - tail) ^ (epsilonFloorSplitIndex delta C + 1) := by
    have hsub_le :
        1 - Real.exp (-(delta * tau)) ≤
          1 - (1 - tail) ^ (epsilonFloorSplitIndex delta C + 1) := by
      linarith
    exact lt_of_lt_of_le hgap hsub_le
  simpa [tail] using hcross

/--
The finite selected-stable capacity contradiction for Theorem 4.  A
split-index iid crossing lower bound and the outcome-event bridge force the
number of below-floor cutoffs to be no larger than the split index.  This is
the capacity step that allows the final coalition to be selected semantically
as the complement of the below-floor block.
-/
theorem pg24_selectedStable_lowCutoff_card_le_of_iid_capacity_bridge
    {Student : Type u} {C : ℕ}
    {M : CutoffMarket Student (Fin (C + 1))}
    (I : SupplyDemandInterface M) (K : MarketClearingCapacityInterface M)
    (selected : { μ : M.Matching // M.Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoffOut : M.Cutoff → Fin (C + 1) → ℝ)
    {k : ℕ} {lowerCutoff eventValue totalSupply : ℝ}
    {Outcome : Type*} [MeasurableSpace Outcome]
    (outcomeLaw : M.Cutoff → Measure Outcome)
    (chosenCollege : M.Cutoff → Outcome → Option (Fin (C + 1)))
    (hfinite : ∀ P : M.Cutoff, IsFiniteMeasure (outcomeLaw P))
    (hchoice :
      ∀ P : M.Cutoff, M.MarketClearing P →
        AppliedModelingLib.Matching.choiceMass (outcomeLaw P) (chosenCollege P)
            (Finset.univ : Finset (Fin (C + 1))) =
          ∑ c : Fin (C + 1), M.aggregateDemand P c)
    (hcapacity_sum : ∑ c : Fin (C + 1), M.capacity c = totalSupply)
    (hupper_cross :
      totalSupply <
        1 -
          (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
            (lowerCutoff - eventValue)) ^ (k + 1))
    (hbridge :
      ∃ event : Outcome → Prop,
        cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (lowCutoffIndexSet
              (cutoffOut
                (I.marketClearingCutoffOfStable
                  (μ := selected.1) selected.2))
              lowerCutoff)
            eventValue
            (cutoffOut
              (I.marketClearingCutoffOfStable
                (μ := selected.1) selected.2)) ≤
          AppliedModelingLib.Matching.eventMass
            (outcomeLaw
              (I.marketClearingCutoffOfStable
                (μ := selected.1) selected.2)) event ∧
        ∀ ω : Outcome, event ω →
          AppliedModelingLib.Matching.chosenInActive
            (chosenCollege
              (I.marketClearingCutoffOfStable
                (μ := selected.1) selected.2))
            (Finset.univ : Finset (Fin (C + 1))) ω) :
    (lowCutoffIndexSet
      (cutoffOut
        (I.marketClearingCutoffOfStable
          (μ := selected.1) selected.2))
      lowerCutoff).card ≤ k := by
  let P : M.Cutoff :=
    I.marketClearingCutoffOfStable (μ := selected.1) selected.2
  let active : Finset (Fin (C + 1)) :=
    lowCutoffIndexSet (cutoffOut P) lowerCutoff
  have hP : M.MarketClearing P :=
    I.marketClearingCutoffOfStable_marketClearing
      (μ := selected.1) selected.2
  by_contra hnot
  have hcard : k + 1 ≤ active.card :=
    Nat.succ_le_of_lt (Nat.lt_of_not_ge hnot)
  let x : ℝ :=
    AppliedModelingLib.Probability.lowerCDFMass noiseLaw (lowerCutoff - eventValue)
  have hx_nonneg : 0 ≤ x := by
    simpa [x] using
      (AppliedModelingLib.Probability.lowerCDFMass_nonneg noiseLaw
        (lowerCutoff - eventValue))
  have hx_le_one : x ≤ 1 := by
    simpa [x] using
      (AppliedModelingLib.Probability.lowerCDFMass_le_one noiseLaw
        (lowerCutoff - eventValue))
  have hpow_le : x ^ active.card ≤ x ^ (k + 1) :=
    pow_right_anti₀ hx_nonneg hx_le_one hcard
  have htail_sum :=
    AppliedModelingLib.Probability.lowerCDFMass_add_upperTailMass_eq_one noiseLaw
      (lowerCutoff - eventValue)
  have htail_rewrite :
      x =
        1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
          (lowerCutoff - eventValue) := by
    dsimp [x]
    linarith
  have hsplit_cross : totalSupply < 1 - x ^ (k + 1) := by
    simpa [htail_rewrite] using hupper_cross
  have hfull_cross : totalSupply < 1 - x ^ active.card := by
    have hsub_le : 1 - x ^ (k + 1) ≤ 1 - x ^ active.card := by
      linarith
    exact lt_of_lt_of_le hsplit_cross hsub_le
  have hafford_gt :
      totalSupply <
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          active eventValue (cutoffOut P) := by
    simpa [cutoffAffordanceProbability, active, x] using
      (AppliedModelingLib.Matching.lt_cutoffCrossingProbability_iidProduct_lowCutoffIndexSet_of_lt_one_sub_lowerCDFMass_pow_card
        noiseLaw hfull_cross)
  rcases hbridge with ⟨event, hafford_le_event, hevent_matched⟩
  haveI : IsFiniteMeasure (outcomeLaw P) := hfinite P
  have hevent_le_capacity :
      AppliedModelingLib.Matching.eventMass (outcomeLaw P) event ≤
        ∑ c : Fin (C + 1), M.capacity c := by
    exact
      AppliedModelingLib.Matching.eventMass_le_totalCapacity_of_imp_aggregateDemand_eq_capacity
        (outcomeLaw P) (chosenCollege P) hevent_matched
        (hchoice P hP)
        (fun c =>
          K.marketClearingCutoffOfStable_aggregateDemand_eq_capacity
            I selected.2 c)
  linarith

/--
Uniform selected-stable Theorem 4 source clauses for the semantic block of
colleges whose selected-stable cutoffs are not below the scalar high-tail
floor.  This is the sortedness-free low-side variant of the suffix route: the
below-floor count bound gives the paper-large subset and the cutoff floor
directly, then the existing high-tail-rate route supplies the long-tail
endpoint estimate.
-/
theorem theorem4_coalitionAmplificationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_nonLow_scalar_tail_upperTail_longTail_endpoint_estimates_from_high_tail_rate
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {valueMass : ∀ C : ℕ, Admissible C → Set ℝ → ℝ}
    {tol eps sigma vLow vHigh : ℝ} (htol_pos : 0 < tol)
    {lowerCutoff : ℕ → ℝ}
    (hmass :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - tol < valueMass C a (Set.Icc vLow vHigh))
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_nonneg : 0 ≤ sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol)
    (hlow_count :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          (lowCutoffIndexSet
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2))
            (lowerCutoff C)).card ≤
          epsilonFloorSplitIndex (tol / 2) C)
    (hhigh_floor_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ _a : Admissible n,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (lowerCutoff n - vHigh) ≤
            sigma / ((n + 1 : ℕ) : ℝ)) :
    (∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        CoalitionLargeSubset
          (Finset.univ : Finset (Fin (C + 1)))
          (nonLowCutoffIndexSet
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2))
            (lowerCutoff C))
          tol) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - tol < valueMass C a (Set.Icc vLow vHigh)) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v ∈ Set.Icc vLow vHigh,
          |cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (nonLowCutoffIndexSet
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2))
                  (lowerCutoff C)) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) -
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (nonLowCutoffIndexSet
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2))
                  (lowerCutoff C)) vLow
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))| < tol) := by
  let largeSubset : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1)) :=
    fun C a =>
      nonLowCutoffIndexSet
        (cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C a).1) (selected C a).2))
        (lowerCutoff C)
  let coalition : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1)) :=
    fun C _a => Finset.univ
  have hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (coalition C a) (largeSubset C a) tol := by
    filter_upwards [hlow_count] with C hcountC a
    exact
      coalitionLargeSubset_univ_nonLowCutoffIndexSet_of_lowCutoff_card_le
        (C := C) (epsilon := tol) htol_pos (hcountC a)
  have hcutoff_lower :
      ∀ᶠ n : ℕ in atTop,
        ∀ a : Admissible n, ∀ c ∈ largeSubset n a,
          lowerCutoff n ≤
            cutoffOut n
              ((Iseq n).marketClearingCutoffOfStable
                (μ := (selected n a).1) (selected n a).2) c := by
    exact Filter.Eventually.of_forall (fun C a c hc =>
      floor_le_of_mem_nonLowCutoffIndexSet hc)
  simpa [largeSubset, coalition] using
    theorem4_coalitionAmplificationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_scalar_tail_upperTail_longTail_endpoint_estimates_from_high_tail_rate
      Mseq Iseq selected noiseLaw hlong cutoffOut hlarge hmass hv
      heps_pos heps_le_one hsigma_nonneg herror_lt
      hcutoff_lower hhigh_floor_le_sigma_div

/--
Theorem 4's semantic non-low coalition route with its split-index capacity
argument made explicit.  The proof does not require cutoff coordinates to be
sorted or relabeled: it derives the below-floor count from iid crossing,
outcome-event, and exact-capacity semantics, then takes the complement of that
below-floor set.

The remaining inputs are the source outcome bridge and capacity normalization,
the regular interval mass, and scalar lower and upper tail estimates at the
chosen floor.  The static gap is the exact numerical condition that turns the
lower tail estimate into a capacity contradiction.
-/
theorem theorem4_coalitionAmplificationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_nonLow_scalar_tail_iid_capacity_static_gap
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (Kseq : ∀ C : ℕ, MarketClearingCapacityInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {valueMass : ∀ C : ℕ, Admissible C → Set ℝ → ℝ}
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    {totalSupply tol eps sigma tau vLow vHigh : ℝ}
    {lowerCutoff : ℕ → ℝ}
    (htol_pos : 0 < tol) (htau_pos : 0 < tau)
    (hmass :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - tol < valueMass C a (Set.Icc vLow vHigh))
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_nonneg : 0 ≤ sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol)
    (hcapacity_gap :
      totalSupply < 1 - Real.exp (-((tol / 2) * tau)))
    (houtcome_finite :
      ∀ C : ℕ, ∀ P : (Mseq C).Cutoff,
        IsFiniteMeasure (outcomeLaw C P))
    (hchoice_mass :
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          ∀ active : Finset (Fin (C + 1)),
            AppliedModelingLib.Matching.choiceMass
                (outcomeLaw C P) (chosenCollege C P) active =
              ∑ c ∈ active, (Mseq C).aggregateDemand P c)
    (hcapacity_sum :
      ∀ᶠ C : ℕ in atTop,
        (∑ c : Fin (C + 1), (Mseq C).capacity c) = totalSupply)
    (haffordance_event :
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          ∀ active : Finset (Fin (C + 1)), ∀ v : ℝ,
            ∃ event : OutcomeSeq C → Prop,
              cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  active v (cutoffOut C P) ≤
                AppliedModelingLib.Matching.eventMass (outcomeLaw C P) event ∧
              ∀ omega : OutcomeSeq C, event omega →
                AppliedModelingLib.Matching.chosenInActive
                  (chosenCollege C P)
                  (Finset.univ : Finset (Fin (C + 1))) omega)
    (htail_lower :
      ∀ᶠ C : ℕ in atTop,
        ∀ _a : Admissible C,
          tau / (((C + 1 : ℕ) : ℝ)) ≤
            AppliedModelingLib.Probability.upperTailMass noiseLaw
              (lowerCutoff C - vHigh))
    (htail_upper :
      ∀ᶠ C : ℕ in atTop,
        ∀ _a : Admissible C,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (lowerCutoff C - vHigh) ≤
            sigma / (((C + 1 : ℕ) : ℝ))) :
    (∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        CoalitionLargeSubset
          (Finset.univ : Finset (Fin (C + 1)))
          (nonLowCutoffIndexSet
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2))
            (lowerCutoff C))
          tol) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - tol < valueMass C a (Set.Icc vLow vHigh)) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v ∈ Set.Icc vLow vHigh,
          |cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (nonLowCutoffIndexSet
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2))
                  (lowerCutoff C)) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) -
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (nonLowCutoffIndexSet
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2))
                  (lowerCutoff C)) vLow
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))| < tol) := by
  have hsplit_cross :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          totalSupply <
            1 -
              (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh)) ^
                (epsilonFloorSplitIndex (tol / 2) C + 1) := by
    simpa using
      (pg24_eventually_upperTail_split_crossing_of_scalar_lower_static_gap
        (Admissible := Admissible) noiseLaw
        (delta := tol / 2) (tau := tau)
        (totalSupply := totalSupply)
        (lowerCutoff := fun C _a => lowerCutoff C)
        (eventValue := fun _C _a => vHigh)
        (by linarith) htau_pos hcapacity_gap htail_lower)
  have hlow_count :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          (lowCutoffIndexSet
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2))
            (lowerCutoff C)).card ≤
            epsilonFloorSplitIndex (tol / 2) C := by
    filter_upwards
      [hchoice_mass, hcapacity_sum, haffordance_event, hsplit_cross] with
      C hchoiceC hsumC heventC hsplitC a
    let P : (Mseq C).Cutoff :=
      (Iseq C).marketClearingCutoffOfStable
        (μ := (selected C a).1) (selected C a).2
    have hP : (Mseq C).MarketClearing P :=
      (Iseq C).marketClearingCutoffOfStable_marketClearing
        (μ := (selected C a).1) (selected C a).2
    exact
      pg24_selectedStable_lowCutoff_card_le_of_iid_capacity_bridge
        (Iseq C) (Kseq C) (selected C a) noiseLaw (cutoffOut C)
        (outcomeLaw C) (chosenCollege C)
        (fun P => houtcome_finite C P)
        (fun P hP' => by
          simpa using hchoiceC P hP'
            (Finset.univ : Finset (Fin (C + 1))))
        hsumC (by simpa [P] using hsplitC a)
        (by
          simpa [P] using
            heventC P hP
              (lowCutoffIndexSet (cutoffOut C P) (lowerCutoff C)) vHigh)
  exact
    theorem4_coalitionAmplificationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_nonLow_scalar_tail_upperTail_longTail_endpoint_estimates_from_high_tail_rate
      Mseq Iseq selected noiseLaw hlong cutoffOut htol_pos hmass hv
      heps_pos heps_le_one hsigma_nonneg herror_lt hlow_count htail_upper

/--
Uniform selected-stable Theorem 4 source clauses for the paper's sorted
suffix `C₂`.  The large-subset condition is derived from deleting an
`tol/2` prefix, and the visible sorted-index cutoff floor is converted into
the membership-based cutoff-floor premise used by the long-tail endpoint
estimate.
-/
theorem theorem4_coalitionAmplificationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_suffix_scalar_tail_upperTail_longTail_endpoint_estimates_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {valueMass : ∀ C : ℕ, Admissible C → Set ℝ → ℝ}
    {tol eps sigma vLow vHigh : ℝ} (htol_pos : 0 < tol)
    {lowerCutoff : ℕ → ℝ}
    (hmass :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - tol < valueMass C a (Set.Icc vLow vHigh))
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_nonneg : 0 ≤ sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol)
    (hlower_atTop :
      Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop)
    (hcutoff_lower :
      ∀ᶠ n : ℕ in atTop,
        ∀ a : Admissible n, ∀ c : Fin (n + 1),
          epsilonFloorSplitIndex (tol / 2) n ≤ (c : ℕ) →
            lowerCutoff n ≤
              cutoffOut n
                ((Iseq n).marketClearingCutoffOfStable
                  (μ := (selected n a).1) (selected n a).2) c)
    (hhigh_floor_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ _a : Admissible n,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (lowerCutoff n - vHigh) ≤
            sigma / ((n + 1 : ℕ) : ℝ)) :
    (∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        CoalitionLargeSubset
          (Finset.univ : Finset (Fin (C + 1)))
          (indexSuffixLarge (epsilonFloorSplitIndex (tol / 2) C) C)
          tol) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - tol < valueMass C a (Set.Icc vLow vHigh)) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v ∈ Set.Icc vLow vHigh,
          |cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (indexSuffixLarge (epsilonFloorSplitIndex (tol / 2) C) C) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) -
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (indexSuffixLarge (epsilonFloorSplitIndex (tol / 2) C) C) vLow
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))| < tol) := by
  let largeSubset : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1)) :=
    fun C _a => indexSuffixLarge (epsilonFloorSplitIndex (tol / 2) C) C
  let coalition : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1)) :=
    fun C _a => Finset.univ
  have hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (coalition C a) (largeSubset C a) tol := by
    filter_upwards [Filter.Eventually.of_forall
      (fun C => coalitionLargeSubset_univ_indexSuffixLarge_epsilonHalf
        (epsilon := tol) htol_pos C)] with C hC a
    exact hC
  have hcutoff_lower_subset :
      ∀ᶠ n : ℕ in atTop,
        ∀ a : Admissible n, ∀ c ∈ largeSubset n a,
          lowerCutoff n ≤
            cutoffOut n
              ((Iseq n).marketClearingCutoffOfStable
                (μ := (selected n a).1) (selected n a).2) c := by
    filter_upwards [hcutoff_lower] with n hcutoff_n a c hc
    exact hcutoff_n a c (Finset.mem_filter.mp hc).2
  simpa [largeSubset, coalition] using
    theorem4_coalitionAmplificationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_scalar_tail_upperTail_longTail_endpoint_estimates_strict_derived
      Mseq Iseq selected noiseLaw hlong cutoffOut hlarge hmass hv
      heps_pos heps_le_one hsigma_nonneg herror_lt hlower_atTop
      hcutoff_lower_subset hhigh_floor_le_sigma_div

/--
Uniform selected-stable Theorem 4 source clauses for the paper's sorted
suffix `C₂`, deriving the long-tail tail-region condition from the high-tail
rate instead of taking lower-endpoint divergence as a separate premise.
-/
theorem theorem4_coalitionAmplificationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_suffix_scalar_tail_upperTail_longTail_endpoint_estimates_from_high_tail_rate
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {valueMass : ∀ C : ℕ, Admissible C → Set ℝ → ℝ}
    {tol eps sigma vLow vHigh : ℝ} (htol_pos : 0 < tol)
    {lowerCutoff : ℕ → ℝ}
    (hmass :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - tol < valueMass C a (Set.Icc vLow vHigh))
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_nonneg : 0 ≤ sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol)
    (hcutoff_lower :
      ∀ᶠ n : ℕ in atTop,
        ∀ a : Admissible n, ∀ c : Fin (n + 1),
          epsilonFloorSplitIndex (tol / 2) n ≤ (c : ℕ) →
            lowerCutoff n ≤
              cutoffOut n
                ((Iseq n).marketClearingCutoffOfStable
                  (μ := (selected n a).1) (selected n a).2) c)
    (hhigh_floor_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ _a : Admissible n,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (lowerCutoff n - vHigh) ≤
            sigma / ((n + 1 : ℕ) : ℝ)) :
    (∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        CoalitionLargeSubset
          (Finset.univ : Finset (Fin (C + 1)))
          (indexSuffixLarge (epsilonFloorSplitIndex (tol / 2) C) C)
          tol) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - tol < valueMass C a (Set.Icc vLow vHigh)) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v ∈ Set.Icc vLow vHigh,
          |cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (indexSuffixLarge (epsilonFloorSplitIndex (tol / 2) C) C) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) -
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (indexSuffixLarge (epsilonFloorSplitIndex (tol / 2) C) C) vLow
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))| < tol) := by
  let largeSubset : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1)) :=
    fun C _a => indexSuffixLarge (epsilonFloorSplitIndex (tol / 2) C) C
  let coalition : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1)) :=
    fun C _a => Finset.univ
  have hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (coalition C a) (largeSubset C a) tol := by
    filter_upwards [Filter.Eventually.of_forall
      (fun C => coalitionLargeSubset_univ_indexSuffixLarge_epsilonHalf
        (epsilon := tol) htol_pos C)] with C hC a
    exact hC
  have hcutoff_lower_subset :
      ∀ᶠ n : ℕ in atTop,
        ∀ a : Admissible n, ∀ c ∈ largeSubset n a,
          lowerCutoff n ≤
            cutoffOut n
              ((Iseq n).marketClearingCutoffOfStable
                (μ := (selected n a).1) (selected n a).2) c := by
    filter_upwards [hcutoff_lower] with n hcutoff_n a c hc
    exact hcutoff_n a c (Finset.mem_filter.mp hc).2
  simpa [largeSubset, coalition] using
    theorem4_coalitionAmplificationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_scalar_tail_upperTail_longTail_endpoint_estimates_from_high_tail_rate
      Mseq Iseq selected noiseLaw hlong cutoffOut hlarge hmass hv
      heps_pos heps_le_one hsigma_nonneg herror_lt
      hcutoff_lower_subset hhigh_floor_le_sigma_div

/--
Indexed Theorem 4 witness from the exceptional-set form in the source
statement.  The exceptional set is the complement of the regular set; a
strict slack bound `delta C < epsilon` turns the exceptional-mass estimate
into the large regular-set mass clause.
-/
theorem theorem4_coalitionAmplificationEpsilonWitness_of_eventual_exception_bound
    {College : ℕ → Type v}
    {coalition largeSubset : ∀ C : ℕ, Finset (College C)}
    {affordProb : ∀ C : ℕ, ℝ → Finset (College C) → ℝ}
    {valueMass : ∀ C : ℕ, Set ℝ → ℝ}
    {regularSet : ∀ C : ℕ, Set ℝ}
    {effectiveSupply delta : ℕ → ℝ}
    {epsilon : ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        CoalitionLargeSubset (coalition C) (largeSubset C) epsilon)
    (hpartition :
      ∀ᶠ C : ℕ in atTop,
        valueMass C (regularSet C) + valueMass C (regularSet C)ᶜ = 1)
    (hexception :
      ∀ᶠ C : ℕ in atTop,
        valueMass C (regularSet C)ᶜ ≤ delta C)
    (hdelta :
      ∀ᶠ C : ℕ in atTop, delta C < epsilon)
    (hclose :
      ∀ᶠ C : ℕ in atTop,
        ∀ v ∈ regularSet C,
          |affordProb C v (largeSubset C) - effectiveSupply C| < epsilon) :
    Theorem4CoalitionAmplificationEpsilonWitnessConclusion
      coalition largeSubset affordProb valueMass regularSet
      effectiveSupply epsilon := by
  refine ⟨hlarge, ?_, hclose⟩
  filter_upwards [hpartition, hexception, hdelta] with C hpartC hexC hdeltaC
  exact theorem4_regular_mass_gt_of_exception_bound hpartC hexC hdeltaC

/--
Indexed Theorem 4 witness from the source interval-gap proof.  The regular
set is the interval `[vLow C, vHigh C]`, and the effective supply is the
restricted affordance probability at the low endpoint.
-/
theorem theorem4_coalitionAmplificationEpsilonWitness_of_eventual_monotone_endpoint_gap
    {College : ℕ → Type v}
    {coalition largeSubset : ∀ C : ℕ, Finset (College C)}
    {affordProb : ∀ C : ℕ, ℝ → Finset (College C) → ℝ}
    {valueMass : ∀ C : ℕ, Set ℝ → ℝ}
    {epsilon : ℝ} {vLow vHigh : ℕ → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        CoalitionLargeSubset (coalition C) (largeSubset C) epsilon)
    (hmass :
      ∀ᶠ C : ℕ in atTop,
        1 - epsilon < valueMass C (Set.Icc (vLow C) (vHigh C)))
    (hp_mono :
      ∀ᶠ C : ℕ in atTop,
        Monotone (fun v => affordProb C v (largeSubset C)))
    (hgap :
      ∀ᶠ C : ℕ in atTop,
        affordProb C (vHigh C) (largeSubset C) -
            affordProb C (vLow C) (largeSubset C) <
          epsilon) :
    Theorem4CoalitionAmplificationEpsilonWitnessConclusion
      coalition largeSubset affordProb valueMass
      (fun C => Set.Icc (vLow C) (vHigh C))
      (fun C => affordProb C (vLow C) (largeSubset C))
      epsilon := by
  refine ⟨hlarge, hmass, ?_⟩
  filter_upwards [hp_mono, hgap] with C hmonoC hgapC
  exact
    theorem4_regular_values_close_of_monotone_endpoint_gap
      (largeSubset := largeSubset C)
      (affordProb := affordProb C)
      (vLow := vLow C) (vHigh := vHigh C)
      (epsilon := epsilon)
      hmonoC hgapC

/--
Indexed Theorem 4 witness from the long-tailed endpoint-gap estimate used in
the source proof.  The endpoint gap on the large subset is derived from
long-tailedness, cutoff lower bounds, and high-value crossing bounds.
-/
theorem theorem4_coalitionAmplificationEpsilonWitness_of_longTail_endpoint_estimates
    {survival : ℝ → ℝ} (hlong : LongTailedSurvival survival)
    {coalition largeSubset : ∀ C : ℕ, Finset (Fin (C + 1))}
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ}
    {valueMass : ∀ C : ℕ, Set ℝ → ℝ}
    {tol eps sigma vLow vHigh : ℝ} {lowerCutoff : ℕ → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        CoalitionLargeSubset (coalition C) (largeSubset C) tol)
    (hmass :
      ∀ᶠ C : ℕ in atTop,
        1 - tol < valueMass C (Set.Icc vLow vHigh))
    (hp_mono :
      ∀ᶠ C : ℕ in atTop,
        Monotone (fun v =>
          independentAffordanceProbability
            (largeSubset C) (fun c => survival (cutoff C c - v))))
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_nonneg : 0 ≤ sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol)
    (hlower_atTop :
      Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop)
    (hcutoff_lower :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ largeSubset n, lowerCutoff n ≤ cutoff n c)
    (hhigh_pos :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ largeSubset n, 0 < survival (cutoff n c - vHigh))
    (hhigh_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ largeSubset n,
          survival (cutoff n c - vHigh) ≤
            sigma / ((n + 1 : ℕ) : ℝ))
    (hlow_failure_pos :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ largeSubset n, 0 < 1 - survival (cutoff n c - vLow)) :
    Theorem4CoalitionAmplificationEpsilonWitnessConclusion
      coalition largeSubset
      (fun C : ℕ => fun v : ℝ => fun active : Finset (Fin (C + 1)) =>
        independentAffordanceProbability
          active (fun c => survival (cutoff C c - v)))
      valueMass
      (fun _C : ℕ => Set.Icc vLow vHigh)
      (fun C : ℕ =>
        independentAffordanceProbability
          (largeSubset C) (fun c => survival (cutoff C c - vLow)))
      tol := by
  refine
    theorem4_coalitionAmplificationEpsilonWitness_of_eventual_monotone_endpoint_gap
      (coalition := coalition) (largeSubset := largeSubset)
      (affordProb := fun C : ℕ => fun v : ℝ => fun active : Finset (Fin (C + 1)) =>
        independentAffordanceProbability
          active (fun c => survival (cutoff C c - v)))
      (valueMass := valueMass)
      (epsilon := tol)
      (vLow := fun _C : ℕ => vLow)
      (vHigh := fun _C : ℕ => vHigh)
      hlarge hmass hp_mono ?_
  have hdiff :
      ∀ᶠ n : ℕ in atTop,
        independentAffordanceProbability
            (largeSubset n) (fun c => survival (cutoff n c - vHigh)) -
          independentAffordanceProbability
            (largeSubset n) (fun c => survival (cutoff n c - vLow)) ≤
          1 - Real.exp (-(2 * eps * sigma)) :=
    independentAffordanceProbability_difference_eventually_le_exp_error_of_longTailed_highCrossingBound
      hlong hv heps_pos heps_le_one hsigma_nonneg
      hlower_atTop hcutoff_lower hhigh_pos hhigh_le_sigma_div
      hlow_failure_pos
  filter_upwards [hdiff] with C hC
  exact lt_of_le_of_lt hC herror_lt

/--
Survival-function specialization of the indexed Theorem 4 long-tail witness.
The value monotonicity used on the regular interval is derived from
antitonicity of the survival function instead of being supplied as a separate
proof-route premise.
-/
theorem theorem4_coalitionAmplificationEpsilonWitness_of_survival_longTail_endpoint_estimates
    {survival : ℝ → ℝ} (hlong : LongTailedSurvival survival)
    {coalition largeSubset : ∀ C : ℕ, Finset (Fin (C + 1))}
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ}
    {valueMass : ∀ C : ℕ, Set ℝ → ℝ}
    {tol eps sigma vLow vHigh : ℝ} {lowerCutoff : ℕ → ℝ}
    (hsurvival_antitone : Antitone survival)
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        CoalitionLargeSubset (coalition C) (largeSubset C) tol)
    (hmass :
      ∀ᶠ C : ℕ in atTop,
        1 - tol < valueMass C (Set.Icc vLow vHigh))
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_nonneg : 0 ≤ sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol)
    (hlower_atTop :
      Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop)
    (hcutoff_lower :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ largeSubset n, lowerCutoff n ≤ cutoff n c)
    (hhigh_pos :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ largeSubset n, 0 < survival (cutoff n c - vHigh))
    (hhigh_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ largeSubset n,
          survival (cutoff n c - vHigh) ≤
            sigma / ((n + 1 : ℕ) : ℝ))
    (hlow_failure_pos :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ largeSubset n, 0 < 1 - survival (cutoff n c - vLow))
    (hprob_le_one :
      ∀ᶠ n : ℕ in atTop,
        ∀ v, ∀ c ∈ largeSubset n, survival (cutoff n c - v) ≤ 1) :
    Theorem4CoalitionAmplificationEpsilonWitnessConclusion
      coalition largeSubset
      (fun C : ℕ => fun v : ℝ => fun active : Finset (Fin (C + 1)) =>
        independentAffordanceProbability
          active (fun c => survival (cutoff C c - v)))
      valueMass
      (fun _C : ℕ => Set.Icc vLow vHigh)
      (fun C : ℕ =>
        independentAffordanceProbability
          (largeSubset C) (fun c => survival (cutoff C c - vLow)))
      tol := by
  have hp_mono :
      ∀ᶠ C : ℕ in atTop,
        Monotone (fun v =>
          independentAffordanceProbability
            (largeSubset C) (fun c => survival (cutoff C c - v))) := by
    filter_upwards [hprob_le_one] with C hleC
    exact
      independentAffordanceProbability_mono_value_of_antitone_survival
        (active := largeSubset C)
        (survival := survival)
        (cutoff := cutoff C)
        hsurvival_antitone
        (fun v c hc => hleC v c hc)
  exact
    theorem4_coalitionAmplificationEpsilonWitness_of_longTail_endpoint_estimates
      hlong hlarge hmass hp_mono hv heps_pos heps_le_one
      hsigma_nonneg herror_lt hlower_atTop hcutoff_lower hhigh_pos
      hhigh_le_sigma_div hlow_failure_pos

/--
Upper-tail-probability specialization of the indexed Theorem 4 long-tail
witness.  The survival-function proof supplies the analytic long-tail step;
the real-noise-law wrapper discharges antitonicity and probability upper
bounds from the measure API.
-/
theorem theorem4_coalitionAmplificationEpsilonWitness_of_upperTail_longTail_endpoint_estimates
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {coalition largeSubset : ∀ C : ℕ, Finset (Fin (C + 1))}
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ}
    {valueMass : ∀ C : ℕ, Set ℝ → ℝ}
    {tol eps sigma vLow vHigh : ℝ} {lowerCutoff : ℕ → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        CoalitionLargeSubset (coalition C) (largeSubset C) tol)
    (hmass :
      ∀ᶠ C : ℕ in atTop,
        1 - tol < valueMass C (Set.Icc vLow vHigh))
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_nonneg : 0 ≤ sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol)
    (hlower_atTop :
      Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop)
    (hcutoff_lower :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ largeSubset n, lowerCutoff n ≤ cutoff n c)
    (hhigh_pos :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ largeSubset n,
          0 < AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff n c - vHigh))
    (hhigh_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ largeSubset n,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff n c - vHigh) ≤
            sigma / ((n + 1 : ℕ) : ℝ))
    (hlow_failure_pos :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ largeSubset n,
          0 < 1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff n c - vLow)) :
    Theorem4CoalitionAmplificationEpsilonWitnessConclusion
      coalition largeSubset
      (fun C : ℕ => fun v : ℝ => fun active : Finset (Fin (C + 1)) =>
        independentAffordanceProbability
          active
          (fun c =>
            AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoff C c - v)))
      valueMass
      (fun _C : ℕ => Set.Icc vLow vHigh)
      (fun C : ℕ =>
        independentAffordanceProbability
          (largeSubset C)
          (fun c =>
            AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoff C c - vLow)))
      tol := by
  have htail_package :=
    upperTailMass_survival_probability_package_indexed
      (noiseLaw := noiseLaw)
      (active := largeSubset)
      (cutoff := cutoff)
  exact
    theorem4_coalitionAmplificationEpsilonWitness_of_survival_longTail_endpoint_estimates
      (survival := AppliedModelingLib.Probability.upperTailMass noiseLaw)
      hlong htail_package.1 hlarge hmass hv heps_pos heps_le_one
      hsigma_nonneg herror_lt hlower_atTop hcutoff_lower hhigh_pos
      hhigh_le_sigma_div hlow_failure_pos htail_package.2.2

/--
Theorem 4 upper-tail long-tail witness with strict probability side
conditions derived internally from the diverging cutoff floor.  This removes
the separate high-tail-positivity and low-failure-positivity premises from the
source-facing endpoint package.
-/
theorem theorem4_coalitionAmplificationEpsilonWitness_of_upperTail_longTail_endpoint_estimates_strict_derived
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {coalition largeSubset : ∀ C : ℕ, Finset (Fin (C + 1))}
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ}
    {valueMass : ∀ C : ℕ, Set ℝ → ℝ}
    {tol eps sigma vLow vHigh : ℝ} {lowerCutoff : ℕ → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        CoalitionLargeSubset (coalition C) (largeSubset C) tol)
    (hmass :
      ∀ᶠ C : ℕ in atTop,
        1 - tol < valueMass C (Set.Icc vLow vHigh))
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_nonneg : 0 ≤ sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol)
    (hlower_atTop :
      Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop)
    (hcutoff_lower :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ largeSubset n, lowerCutoff n ≤ cutoff n c)
    (hhigh_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ largeSubset n,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff n c - vHigh) ≤
            sigma / ((n + 1 : ℕ) : ℝ)) :
    Theorem4CoalitionAmplificationEpsilonWitnessConclusion
      coalition largeSubset
      (fun C : ℕ => fun v : ℝ => fun active : Finset (Fin (C + 1)) =>
        independentAffordanceProbability
          active
          (fun c =>
            AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoff C c - v)))
      valueMass
      (fun _C : ℕ => Set.Icc vLow vHigh)
      (fun C : ℕ =>
        independentAffordanceProbability
          (largeSubset C)
          (fun c =>
            AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoff C c - vLow)))
      tol := by
  have hstrict :=
    upperTailMass_strict_side_conditions_of_longTail_cutoff_floor_indexed
      (noiseLaw := noiseLaw)
      (hlong := hlong)
      (active := largeSubset)
      (cutoff := cutoff)
      (vLow := vLow)
      (vHigh := vHigh)
      (lowerCutoff := lowerCutoff)
      hv hlower_atTop hcutoff_lower
  exact
    theorem4_coalitionAmplificationEpsilonWitness_of_upperTail_longTail_endpoint_estimates
      (noiseLaw := noiseLaw)
      (hlong := hlong)
      (coalition := coalition)
      (largeSubset := largeSubset)
      (cutoff := cutoff)
      (valueMass := valueMass)
      (tol := tol)
      (eps := eps)
      (sigma := sigma)
      (vLow := vLow)
      (vHigh := vHigh)
      (lowerCutoff := lowerCutoff)
      hlarge hmass hv heps_pos heps_le_one hsigma_nonneg herror_lt
      hlower_atTop hcutoff_lower hstrict.1 hhigh_le_sigma_div hstrict.2

/--
Concrete iid-product cutoff specialization of the indexed Theorem 4 long-tail
witness.  The final regular-set approximation is stated in terms of the
actual product-noise cutoff-affordance probability, with the independent
upper-tail product used only as the internal analytic bridge.
-/
theorem theorem4_coalitionAmplificationEpsilonWitness_of_iidProduct_cutoff_upperTail_longTail_endpoint_estimates_strict_derived
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {coalition largeSubset : ∀ C : ℕ, Finset (Fin (C + 1))}
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ}
    {valueMass : ∀ C : ℕ, Set ℝ → ℝ}
    {tol eps sigma vLow vHigh : ℝ} {lowerCutoff : ℕ → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        CoalitionLargeSubset (coalition C) (largeSubset C) tol)
    (hmass :
      ∀ᶠ C : ℕ in atTop,
        1 - tol < valueMass C (Set.Icc vLow vHigh))
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_nonneg : 0 ≤ sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol)
    (hlower_atTop :
      Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop)
    (hcutoff_lower :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ largeSubset n, lowerCutoff n ≤ cutoff n c)
    (hhigh_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ c ∈ largeSubset n,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoff n c - vHigh) ≤
            sigma / ((n + 1 : ℕ) : ℝ)) :
    Theorem4CoalitionAmplificationEpsilonWitnessConclusion
      coalition largeSubset
      (fun C : ℕ => fun v : ℝ => fun active : Finset (Fin (C + 1)) =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          active v (cutoff C))
      valueMass
      (fun _C : ℕ => Set.Icc vLow vHigh)
      (fun C : ℕ =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (largeSubset C) vLow (cutoff C))
      tol := by
  have htail :=
    theorem4_coalitionAmplificationEpsilonWitness_of_upperTail_longTail_endpoint_estimates_strict_derived
      (noiseLaw := noiseLaw)
      (hlong := hlong)
      (coalition := coalition)
      (largeSubset := largeSubset)
      (cutoff := cutoff)
      (valueMass := valueMass)
      (tol := tol)
      (eps := eps)
      (sigma := sigma)
      (vLow := vLow)
      (vHigh := vHigh)
      (lowerCutoff := lowerCutoff)
      hlarge hmass hv heps_pos heps_le_one hsigma_nonneg herror_lt
      hlower_atTop hcutoff_lower hhigh_le_sigma_div
  refine
    ⟨htail.large_subset_eventually,
      htail.regular_mass_eventually, ?_⟩
  filter_upwards [htail.regular_values_close_eventually] with C hcloseC
  intro v hv_mem
  have hbridge_v :=
    cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
      noiseLaw (largeSubset C) v (cutoff C)
  have hbridge_low :=
    cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
      noiseLaw (largeSubset C) vLow (cutoff C)
  simpa [hbridge_v, hbridge_low] using hcloseC v hv_mem

/--
Concrete iid-product Theorem 4 over a selected sequence of stable matchings.

The A-L bridge chooses the market-clearing cutoff representing each selected
stable matching.  The long-tail endpoint estimates are stated for all
market-clearing cutoffs, then specialized to the selected cutoffs.
-/
theorem theorem4_coalitionAmplificationEpsilonWitness_of_iidProduct_selected_stable_cutoff_upperTail_longTail_endpoint_estimates_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (selected :
      ∀ C : ℕ, { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {coalition largeSubset : ∀ C : ℕ, Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {valueMass : ∀ C : ℕ, Set ℝ → ℝ}
    {tol eps sigma vLow vHigh : ℝ} {lowerCutoff : ℕ → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        CoalitionLargeSubset (coalition C) (largeSubset C) tol)
    (hmass :
      ∀ᶠ C : ℕ in atTop,
        1 - tol < valueMass C (Set.Icc vLow vHigh))
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_nonneg : 0 ≤ sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol)
    (hlower_atTop :
      Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop)
    (hcutoff_lower :
      ∀ᶠ n : ℕ in atTop,
        ∀ P : (Mseq n).Cutoff, (Mseq n).MarketClearing P →
          ∀ c ∈ largeSubset n, lowerCutoff n ≤ cutoffOut n P c)
    (hhigh_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ P : (Mseq n).Cutoff, (Mseq n).MarketClearing P →
          ∀ c ∈ largeSubset n,
            AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoffOut n P c - vHigh) ≤
              sigma / ((n + 1 : ℕ) : ℝ)) :
    Theorem4CoalitionAmplificationEpsilonWitnessConclusion
      coalition largeSubset
      (fun C : ℕ => fun v : ℝ => fun active : Finset (Fin (C + 1)) =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          active v
          (cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C).1) (selected C).2)))
      valueMass
      (fun _C : ℕ => Set.Icc vLow vHigh)
      (fun C : ℕ =>
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (largeSubset C) vLow
          (cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C).1) (selected C).2)))
      tol := by
  have hmc :
      ∀ C : ℕ,
        (Mseq C).MarketClearing
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C).1) (selected C).2) := by
    intro C
    exact
      (Iseq C).marketClearingCutoffOfStable_marketClearing
        (μ := (selected C).1) (selected C).2
  refine
    theorem4_coalitionAmplificationEpsilonWitness_of_iidProduct_cutoff_upperTail_longTail_endpoint_estimates_strict_derived
      (noiseLaw := noiseLaw)
      (hlong := hlong)
      (coalition := coalition)
      (largeSubset := largeSubset)
      (cutoff := fun C : ℕ =>
        cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C).1) (selected C).2))
      (valueMass := valueMass)
      (tol := tol)
      (eps := eps)
      (sigma := sigma)
      (vLow := vLow)
      (vHigh := vHigh)
      (lowerCutoff := lowerCutoff)
      hlarge hmass hv heps_pos heps_le_one hsigma_nonneg herror_lt
      hlower_atTop ?_ ?_
  · filter_upwards [hcutoff_lower] with n hn c hc
    exact hn _ (hmc n) c hc
  · filter_upwards [hhigh_le_sigma_div] with n hn c hc
    exact hn _ (hmc n) c hc

/--
Indexed Theorem 4 source clauses unpacked from the growing-coalition witness.
-/
theorem theorem4_coalitionAmplificationEpsilonWitness_source_clauses
    {College : ℕ → Type v}
    {coalition largeSubset : ∀ C : ℕ, Finset (College C)}
    {affordProb : ∀ C : ℕ, ℝ → Finset (College C) → ℝ}
    {valueMass : ∀ C : ℕ, Set ℝ → ℝ}
    {regularSet : ∀ C : ℕ, Set ℝ}
    {effectiveSupply : ℕ → ℝ}
    {epsilon : ℝ}
    (h :
      Theorem4CoalitionAmplificationEpsilonWitnessConclusion
        coalition largeSubset affordProb valueMass regularSet
        effectiveSupply epsilon) :
    (∀ᶠ C : ℕ in atTop,
      CoalitionLargeSubset (coalition C) (largeSubset C) epsilon) ∧
      (∀ᶠ C : ℕ in atTop,
        1 - epsilon < valueMass C (regularSet C)) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ v ∈ regularSet C,
          |affordProb C v (largeSubset C) - effectiveSupply C| < epsilon) :=
  ⟨h.large_subset_eventually,
    h.regular_mass_eventually,
    h.regular_values_close_eventually⟩

/--
Concrete selected-stable Theorem 4 source clauses.  This composes the
strongest selected-stable long-tail endpoint route with the source-clause
projection, so the paper-facing conclusion is stated directly in terms of
large subsets, large regular intervals, and selected-stable cutoff-affordance
probabilities.
-/
theorem theorem4_coalitionAmplificationEpsilonWitness_source_clauses_of_iidProduct_selected_stable_cutoff_upperTail_longTail_endpoint_estimates_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (selected :
      ∀ C : ℕ, { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {coalition largeSubset : ∀ C : ℕ, Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {valueMass : ∀ C : ℕ, Set ℝ → ℝ}
    {tol eps sigma vLow vHigh : ℝ} {lowerCutoff : ℕ → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        CoalitionLargeSubset (coalition C) (largeSubset C) tol)
    (hmass :
      ∀ᶠ C : ℕ in atTop,
        1 - tol < valueMass C (Set.Icc vLow vHigh))
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_nonneg : 0 ≤ sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol)
    (hlower_atTop :
      Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop)
    (hcutoff_lower :
      ∀ᶠ n : ℕ in atTop,
        ∀ P : (Mseq n).Cutoff, (Mseq n).MarketClearing P →
          ∀ c ∈ largeSubset n, lowerCutoff n ≤ cutoffOut n P c)
    (hhigh_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ P : (Mseq n).Cutoff, (Mseq n).MarketClearing P →
          ∀ c ∈ largeSubset n,
            AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoffOut n P c - vHigh) ≤
              sigma / ((n + 1 : ℕ) : ℝ)) :
    (∀ᶠ C : ℕ in atTop,
      CoalitionLargeSubset (coalition C) (largeSubset C) tol) ∧
      (∀ᶠ C : ℕ in atTop,
        1 - tol < valueMass C (Set.Icc vLow vHigh)) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ v ∈ Set.Icc vLow vHigh,
          |cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C).1) (selected C).2)) -
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C) vLow
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C).1) (selected C).2))| < tol) := by
  have h :=
    theorem4_coalitionAmplificationEpsilonWitness_of_iidProduct_selected_stable_cutoff_upperTail_longTail_endpoint_estimates_strict_derived
      Mseq Iseq selected noiseLaw hlong cutoffOut hlarge hmass hv heps_pos
      heps_le_one hsigma_nonneg herror_lt hlower_atTop hcutoff_lower
      hhigh_le_sigma_div
  exact theorem4_coalitionAmplificationEpsilonWitness_source_clauses h

/--
Concrete selected-stable Theorem 4 source clauses with the high-endpoint tail
estimate stated at the scalar lower cutoff floor.  This is the selected
sequence analogue of the uniform scalar-tail route.
-/
theorem theorem4_coalitionAmplificationEpsilonWitness_source_clauses_of_iidProduct_selected_stable_cutoff_scalar_tail_upperTail_longTail_endpoint_estimates_strict_derived
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (selected :
      ∀ C : ℕ, { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {coalition largeSubset : ∀ C : ℕ, Finset (Fin (C + 1))}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {valueMass : ∀ C : ℕ, Set ℝ → ℝ}
    {tol eps sigma vLow vHigh : ℝ} {lowerCutoff : ℕ → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        CoalitionLargeSubset (coalition C) (largeSubset C) tol)
    (hmass :
      ∀ᶠ C : ℕ in atTop,
        1 - tol < valueMass C (Set.Icc vLow vHigh))
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_nonneg : 0 ≤ sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol)
    (hlower_atTop :
      Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop)
    (hcutoff_lower :
      ∀ᶠ n : ℕ in atTop,
        ∀ P : (Mseq n).Cutoff, (Mseq n).MarketClearing P →
          ∀ c ∈ largeSubset n, lowerCutoff n ≤ cutoffOut n P c)
    (hhigh_floor_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ P : (Mseq n).Cutoff, (Mseq n).MarketClearing P →
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (lowerCutoff n - vHigh) ≤
            sigma / ((n + 1 : ℕ) : ℝ)) :
    (∀ᶠ C : ℕ in atTop,
      CoalitionLargeSubset (coalition C) (largeSubset C) tol) ∧
      (∀ᶠ C : ℕ in atTop,
        1 - tol < valueMass C (Set.Icc vLow vHigh)) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ v ∈ Set.Icc vLow vHigh,
          |cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C).1) (selected C).2)) -
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C) vLow
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C).1) (selected C).2))| < tol) := by
  have hhigh_le_sigma_div :
      ∀ᶠ n : ℕ in atTop,
        ∀ P : (Mseq n).Cutoff, (Mseq n).MarketClearing P →
          ∀ c ∈ largeSubset n,
            AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoffOut n P c - vHigh) ≤
              sigma / ((n + 1 : ℕ) : ℝ) := by
    filter_upwards [hcutoff_lower, hhigh_floor_le_sigma_div] with
      n hcutoff_n htail_n P hP c hc
    exact
      le_trans
        (AppliedModelingLib.Probability.upperTailMass_antitone noiseLaw
          (sub_le_sub_right (hcutoff_n P hP c hc) vHigh))
        (htail_n P hP)
  exact
    theorem4_coalitionAmplificationEpsilonWitness_source_clauses_of_iidProduct_selected_stable_cutoff_upperTail_longTail_endpoint_estimates_strict_derived
      Mseq Iseq selected noiseLaw hlong cutoffOut hlarge hmass hv heps_pos
      heps_le_one hsigma_nonneg herror_lt hlower_atTop hcutoff_lower
      hhigh_le_sigma_div

end PG24NoisyMatchingMarkets
