import PG24NoisyMatchingMarkets.MainTheorems
import PG24NoisyMatchingMarkets.Assumptions
import PG24NoisyMatchingMarkets.Theorem4CapacityResolution
import PG24NoisyMatchingMarkets.Theorem4TrueValueSourceConclusion
import PG24NoisyMatchingMarkets.Theorem3ActualProof
import PG24NoisyMatchingMarkets.Theorem1LiteralUniformSourceConclusion
import PG24NoisyMatchingMarkets.PG24LiteralBasicMarket
import PG24NoisyMatchingMarkets.Theorem2AllRealLiteralBasic
import PG24NoisyMatchingMarkets.Theorem1SourceProofHelpers
import PG24NoisyMatchingMarkets.Theorem1RoundedChebyshevRates
import PG24NoisyMatchingMarkets.Theorem1LargeGapQualitativeRoute
import PG24NoisyMatchingMarkets.Theorem2AppendixSourceClaims
import PG24NoisyMatchingMarkets.Theorem2LiteralAppendixClaims
import AL16SupplyDemandMatching.Assumptions
import PG24NoisyMatchingMarkets.PaperInterface

/-!
# Human-Facing Paper Interface: Wisdom and Foolishness of Noisy Matching Markets

This interface exposes the current top-down formalization targets.  PG24 uses
the A-L supply/demand bridge to represent arbitrary stable matchings by
market-clearing cutoffs, then proves attenuation/amplification over those
cutoff vectors.
-/

open Filter Topology

namespace PG24NoisyMatchingMarkets

open AppliedModelingLib.Matching
open MeasureTheory

universe u v w x

variable {Student : Type u} {College : Type v}
variable (M : CutoffMarket Student College)

/--
Stable matchings have market-clearing cutoff representations.

Source status: PG24 model section, using the A-L supply/demand bridge for the
paper's stable-matching-as-cutoff representation.
-/
theorem stableMatching_cutoffRepresentation_statement
    (I : SupplyDemandInterface M) {μ : M.Matching}
    (hμ : M.Stable μ) :
    ∃ P : M.Cutoff, M.MarketClearing P ∧ M.RepresentedByCutoff μ P :=
  stableMatching_has_marketClearing_cutoff M I hμ

/--
Stable matchings have market-clearing cutoff representations from the exact
supply/demand theorem used by PG24.

Source status: PG24's model section cites the A-L cutoff characterization.
Only that characterization is required here; existence, lattice, and
exact-fill consequences are not premises of this result.
-/
theorem stableMatching_cutoffRepresentation_from_AL_source_model_statement
    (I : SupplyDemandInterface M)
    {μ : M.Matching} (hμ : M.Stable μ) :
    ∃ P : M.Cutoff, M.MarketClearing P ∧ M.RepresentedByCutoff μ P :=
  stableMatching_cutoffRepresentation_statement M I hμ

/--
Definition: β-max-concentrating noise.

Source status: PG24 model definition.  The paper defines this by the
polynomial variance-rate condition `Var[X^(n)] = O(n^{-β})` for some
positive `β`; here `maxVariance n` represents `Var[X^(n+1)]`.
-/
abbrev definition_betaMaxConcentrating_variance_statement
    (maxVariance : ℕ → ℝ) (β : ℝ) : Prop :=
  betaMaxConcentratingVariance maxVariance β

/--
The β-max-concentrating variance rate implies vanishing maximum-order
statistic variance.

Source status: analytic consequence of the PG24 definition
`Var[X^(n)] = O(n^{-β})` with positive `β`.
-/
theorem betaMaxConcentrating_variance_tendsto_zero_statement
    {maxVariance : ℕ → ℝ} {β : ℝ}
    (h : definition_betaMaxConcentrating_variance_statement maxVariance β)
    (hvariance_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ maxVariance n) :
    Tendsto maxVariance atTop (nhds 0) :=
  betaMaxConcentratingVariance.tendsto_zero h hvariance_nonneg

/--
Maximum-order-statistic concentration bridge used by the attenuation proof.

Source status: consequence route from the PG24 variance-rate definition, via
Chebyshev, to the concentration predicate used in the cutoff estimates.
-/
abbrev maxConcentrating_chebyshev_concentration_bridge_statement
    (sampleLaw : ∀ n : ℕ, MeasureTheory.Measure (Fin (n + 1) → ℝ)) : Prop :=
  maximumOrderStatisticConcentrating sampleLaw

/--
Chebyshev bridge from maximum-order-statistic variance to concentration.

Source status: PG24 model discussion after the max-concentration definition:
variance of the maximum order statistic tending to zero suffices, by
Chebyshev, for the concentration predicate used in the attenuation proof.
-/
theorem maxConcentrating_from_chebyshev_variance_bound_statement
    {sampleLaw : ∀ n : ℕ, MeasureTheory.Measure (Fin (n + 1) → ℝ)}
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
    maxConcentrating_chebyshev_concentration_bridge_statement sampleLaw :=
  maximumOrderStatisticConcentrating_of_chebyshev_variance_bound
    hvariance_zero hchebyshev

/--
Variance-bound bridge from maximum-order-statistic variance to concentration.

Source status: PG24 model discussion after the max-concentration definition:
the source variance calculation bounds `Var[X^(n)]`; Chebyshev is a derived
probability-library step rather than a paper-facing assumption.
-/
theorem maxConcentrating_from_variance_bound_statement
    {sampleLaw : ∀ n : ℕ, MeasureTheory.Measure (Fin (n + 1) → ℝ)}
    {varianceBound : ℕ → ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
    (hvariance_zero : Tendsto varianceBound atTop (nhds 0))
    (hvariance_bound :
      source_assumption_beta_max_variance_bound sampleLaw varianceBound) :
    maxConcentrating_chebyshev_concentration_bridge_statement sampleLaw :=
  maximumOrderStatisticConcentrating_of_variance_bound
    hprob hvariance_zero hvariance_bound.1 hvariance_bound.2

/--
Definition: long-tailed noise.

Source status: PG24 model definition.  If `survival x = Pr[X > x]`, then the
paper's condition `Pr[X > x + d | X > x] -> 1` is the survival-ratio limit
below for every positive shift `d`.
-/
abbrev definition_longTailed_survival_statement
    (survival : ℝ → ℝ) : Prop :=
  LongTailedSurvival survival

/--
Cutoff affordance event bridge for `p_mu(v, C')`.

Source status: PG24 model and extended-model definitions of `p_mu(v)` and
`p_mu(v,C')`, identifying "can afford some college" with a finite cutoff
crossing event.
-/
abbrev cutoffAffordanceEvent_statement {College : Type v}
    (active : Finset College) (v : ℝ) (noise cutoff : College → ℝ) : Prop :=
  cutoffAffordanceEvent active v noise cutoff

/--
Cutoff affordance probability bridge for `p_mu(v)`.

Source status: PG24 proof outline and model definition of `p_mu(v)`, where
the match probability is analyzed as the probability that one random noisy
score crosses its corresponding market-clearing cutoff.
-/
noncomputable abbrev cutoffAffordanceProbability_statement {College : Type v}
    [MeasurableSpace (College → ℝ)]
    (noiseLaw : MeasureTheory.Measure (College → ℝ))
    (active : Finset College) (v : ℝ) (cutoff : College → ℝ) : ℝ :=
  cutoffAffordanceProbability noiseLaw active v cutoff

/--
Iid product-noise bridge for active-set affordance probability.

Source status: PG24's noisy-score model has independent draws across
colleges.  This identifies the concrete cutoff event with the product
expression used in the large-firm long-tail amplification proof.
-/
theorem cutoffAffordanceProbability_iidProduct_independent_tail_statement
    {n : ℕ} (noiseLaw : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (active : Finset (Fin n)) (v : ℝ) (cutoff : Fin n → ℝ) :
    cutoffAffordanceProbability_statement
        (MeasureTheory.Measure.pi (fun _ : Fin n => noiseLaw))
        active v cutoff =
      independentAffordanceProbability active
        (fun c => AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff c - v)) :=
  cutoffAffordanceProbability_iidProduct_eq_independentAffordanceProbability_upperTailMass
    noiseLaw active v cutoff

/--
Iid product-noise CDF formula for a common cutoff on an active block.

Source status: PG24 coalition and block arguments use that, when all active
colleges share cutoff `P`, affordability is the event that at least one iid
noise draw exceeds `P-v`, giving `1 - F_X(P-v)^{|C'|}`.
-/
theorem cutoffAffordanceProbability_iidProduct_constant_lowerCDFMass_pow_card_statement
    {n : ℕ} (noiseLaw : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (active : Finset (Fin n)) (v P : ℝ) :
    cutoffAffordanceProbability_statement
        (MeasureTheory.Measure.pi (fun _ : Fin n => noiseLaw))
        active v (fun _ => P) =
      1 - (AppliedModelingLib.Probability.lowerCDFMass noiseLaw (P - v)) ^ active.card := by
  simpa [cutoffAffordanceProbability_statement, cutoffAffordanceProbability]
    using
      (AppliedModelingLib.Matching.cutoffCrossingProbability_iidProduct_constant_eq_one_sub_lowerCDFMass_pow_card
        (n := n) noiseLaw active v P)

/--
Single-college affordance probability used in finite union bounds.

Source status: PG24 appendix-style cutoff estimates; before using maximum
order statistics for equal-cutoff clusters, the arbitrary active-set event is
first bounded by summing the one-college crossing events.
-/
noncomputable abbrev singleCollegeAffordanceProbability_statement
    {College : Type v} [MeasurableSpace (College → ℝ)]
    (noiseLaw : MeasureTheory.Measure (College → ℝ))
    (v : ℝ) (cutoff : College → ℝ) (c : College) : ℝ :=
  singleCollegeAffordanceProbability noiseLaw v cutoff c

/--
Finite union bound for active-set affordance probability.

Source status: PG24 cutoff-vector proof step: affording some college in a
finite active set is a union of one-college crossing events.
-/
theorem cutoffAffordanceProbability_union_bound_statement
    {College : Type v} [MeasurableSpace (College → ℝ)]
    (noiseLaw : MeasureTheory.Measure (College → ℝ))
    (active : Finset College) (v : ℝ) (cutoff : College → ℝ) :
    cutoffAffordanceProbability_statement noiseLaw active v cutoff ≤
      ∑ c ∈ active,
        singleCollegeAffordanceProbability_statement noiseLaw v cutoff c :=
  cutoffAffordanceProbability_le_sum_singleCollegeAffordanceProbability
    noiseLaw active v cutoff

/--
Active-set split decomposition for affordance probability.

Source status: PG24 amplification appendix, equation `equiv-lt`, where the
total active set is decomposed into small and large colleges and the proof
uses `p(C2) <= p(C)` and `p(C) <= p(C1) + p(C2)`.
-/
theorem cutoffAffordanceProbability_active_split_decomposition_statement
    {College : Type v} [DecidableEq College]
    [MeasurableSpace (College → ℝ)]
    (noiseLaw : MeasureTheory.Measure (College → ℝ))
    [MeasureTheory.IsFiniteMeasure noiseLaw]
    {small large total : Finset College} {v : ℝ} {cutoff : College → ℝ}
    (htotal : total = small ∪ large) :
    cutoffAffordanceProbability_statement noiseLaw large v cutoff ≤
        cutoffAffordanceProbability_statement noiseLaw total v cutoff ∧
      cutoffAffordanceProbability_statement noiseLaw total v cutoff ≤
        cutoffAffordanceProbability_statement noiseLaw small v cutoff +
          cutoffAffordanceProbability_statement noiseLaw large v cutoff :=
  cutoffAffordanceProbability_decomposition_of_union
    noiseLaw (small := small) (large := large) (total := total)
    (v := v) (cutoff := cutoff) htotal

/--
Uniform finite union bound for active-set affordance probability.

Source status: PG24 proof step where a small or controlled class of active
colleges is bounded by a common one-college crossing probability.
-/
theorem cutoffAffordanceProbability_uniform_single_bound_statement
    {College : Type v} [MeasurableSpace (College → ℝ)]
    (noiseLaw : MeasureTheory.Measure (College → ℝ))
    (active : Finset College) (v : ℝ) (cutoff : College → ℝ) {q : ℝ}
    (hbound :
      ∀ c ∈ active,
        singleCollegeAffordanceProbability_statement noiseLaw v cutoff c ≤ q) :
    cutoffAffordanceProbability_statement noiseLaw active v cutoff ≤
      (active.card : ℝ) * q :=
  cutoffAffordanceProbability_le_card_mul_of_singleCollegeAffordanceProbability_le
    noiseLaw active v cutoff hbound

/--
Uniform finite union bound with a real cardinal upper bound.

Source status: PG24 proof step combining an active-set size estimate with a
common one-college crossing bound.
-/
theorem cutoffAffordanceProbability_uniform_card_bound_statement
    {College : Type v} [MeasurableSpace (College → ℝ)]
    (noiseLaw : MeasureTheory.Measure (College → ℝ))
    (active : Finset College) (v : ℝ) (cutoff : College → ℝ)
    {cardBound q : ℝ}
    (hcard : (active.card : ℝ) ≤ cardBound) (hq_nonneg : 0 ≤ q)
    (hbound :
      ∀ c ∈ active,
        singleCollegeAffordanceProbability_statement noiseLaw v cutoff c ≤ q) :
    cutoffAffordanceProbability_statement noiseLaw active v cutoff ≤
      cardBound * q :=
  cutoffAffordanceProbability_le_cardBound_mul_of_singleCollegeAffordanceProbability_le
    noiseLaw active v cutoff hcard hq_nonneg hbound

/--
Affordance probability is monotone in the active college set.

Source status: PG24 attenuation and amplification proof routes, where small
sets of cutoffs are ignored or larger cutoff clusters are compared by event
inclusion.
-/
theorem cutoffAffordanceProbability_activeSet_monotone_statement
    {College : Type v} [MeasurableSpace (College → ℝ)]
    (noiseLaw : MeasureTheory.Measure (College → ℝ))
    [MeasureTheory.IsFiniteMeasure noiseLaw]
    {active larger : Finset College} {v : ℝ} {cutoff : College → ℝ}
    (hsubset : active ⊆ larger) :
    cutoffAffordanceProbability_statement noiseLaw active v cutoff ≤
      cutoffAffordanceProbability_statement noiseLaw larger v cutoff :=
  cutoffAffordanceProbability_mono_active noiseLaw hsubset

/--
Affordance probability is monotone when active cutoffs are lowered.

Source status: PG24 cutoff-cluster comparisons; replacing a cutoff vector by a
lower active bound can only increase the chance of affording some college.
-/
theorem cutoffAffordanceProbability_lowerCutoff_monotone_statement
    {College : Type v} [MeasurableSpace (College → ℝ)]
    (noiseLaw : MeasureTheory.Measure (College → ℝ))
    [MeasureTheory.IsFiniteMeasure noiseLaw]
    {active : Finset College} {v : ℝ}
    {cutoff lowerCutoff : College → ℝ}
    (hlower : ∀ c ∈ active, lowerCutoff c ≤ cutoff c) :
    cutoffAffordanceProbability_statement noiseLaw active v cutoff ≤
      cutoffAffordanceProbability_statement noiseLaw active v lowerCutoff :=
  cutoffAffordanceProbability_mono_lowerCutoff noiseLaw hlower

/--
Cluster upper-cutoff comparison: if all active cutoffs are below a common
bound, the actual affordance probability is at least the corresponding
constant-cutoff probability.

Source status: PG24 attenuation proof, Proposition tomato lower-bound step
for a dense cluster in `[P*, P* + delta]`.
-/
theorem constantCutoffAffordanceProbability_lower_bound_statement
    {College : Type v} [MeasurableSpace (College → ℝ)]
    (noiseLaw : MeasureTheory.Measure (College → ℝ))
    [MeasureTheory.IsFiniteMeasure noiseLaw]
    {active : Finset College} {v P : ℝ} {cutoff : College → ℝ}
    (hupper : ∀ c ∈ active, cutoff c ≤ P) :
    cutoffAffordanceProbability_statement noiseLaw active v (fun _ => P) ≤
      cutoffAffordanceProbability_statement noiseLaw active v cutoff :=
  constantCutoffAffordanceProbability_le_of_cutoff_le
    noiseLaw hupper

/--
Cluster lower-cutoff comparison: if all active cutoffs are above a common
bound, the actual affordance probability is at most the corresponding
constant-cutoff probability.

Source status: PG24 attenuation proof, Proposition tomato upper-bound step
for colleges with cutoffs in `[P*, infinity)`.
-/
theorem cutoffAffordanceProbability_constant_upper_bound_statement
    {College : Type v} [MeasurableSpace (College → ℝ)]
    (noiseLaw : MeasureTheory.Measure (College → ℝ))
    [MeasureTheory.IsFiniteMeasure noiseLaw]
    {active : Finset College} {v P : ℝ} {cutoff : College → ℝ}
    (hlower : ∀ c ∈ active, P ≤ cutoff c) :
    cutoffAffordanceProbability_statement noiseLaw active v cutoff ≤
      cutoffAffordanceProbability_statement noiseLaw active v (fun _ => P) :=
  cutoffAffordanceProbability_le_constantCutoff_of_le
    noiseLaw hlower

/--
Affordance probability is monotone in student value.

Source status: PG24 threshold arguments; increasing the student's value
weakly increases the chance of crossing some cutoff.
-/
theorem cutoffAffordanceProbability_value_monotone_statement
    {College : Type v} [MeasurableSpace (College → ℝ)]
    (noiseLaw : MeasureTheory.Measure (College → ℝ))
    [MeasureTheory.IsFiniteMeasure noiseLaw]
    {active : Finset College} {v w : ℝ} {cutoff : College → ℝ}
    (hvw : v ≤ w) :
    cutoffAffordanceProbability_statement noiseLaw active v cutoff ≤
      cutoffAffordanceProbability_statement noiseLaw active w cutoff :=
  cutoffAffordanceProbability_mono_value noiseLaw hvw

/--
Definition: PG24 regular college capacities.

Source status: PG24 model regularity condition `S_c < alpha / C`, saying no
single college has disproportionately large capacity.
-/
abbrev definition_capacityRegular_statement
    (capacity : College → ℝ) (alpha : ℝ) (C : ℕ) : Prop :=
  capacityRegular (College := College) capacity alpha C

/--
Capacity regularity gives the weak per-college bound used in estimates.

Source status: bridge from the strict model condition `S_c < alpha / C` to
the weak inequality used by finite capacity arithmetic.
-/
theorem capacityRegular_le_statement
    {capacity : College → ℝ} {alpha : ℝ} {C : ℕ}
    (h : definition_capacityRegular_statement capacity alpha C) :
    ∀ c : College, capacity c ≤ alpha / (C : ℝ) :=
  capacityRegular.le h

/--
Definition: the initial sorted-index block `F_1`.

Source status: PG24 Theorem 2 proof sorts colleges by cutoff and defines the
small block as the initial segment of that sorted order.
-/
abbrev definition_indexPrefixSmall_statement (k C : ℕ) :
    Finset (Fin (C + 1)) :=
  indexPrefixSmall k C

/--
Definition: the remaining sorted-index block `F_2`.

Source status: PG24 Theorem 2 proof uses the complement/tail of the initial
sorted block as the large-college block.
-/
abbrev definition_indexSuffixLarge_statement (k C : ℕ) :
    Finset (Fin (C + 1)) :=
  indexSuffixLarge k C

/--
The sorted-index blocks partition all colleges.

Source status: finite-set part of the paper's `F_1/F_2` construction.
-/
theorem indexPrefixSmall_union_indexSuffixLarge_statement (k C : ℕ) :
    (Finset.univ : Finset (Fin (C + 1))) =
      definition_indexPrefixSmall_statement k C ∪
        definition_indexSuffixLarge_statement k C :=
  indexPrefixSmall_union_indexSuffixLarge k C

/--
The initial sorted-index block has at most its split index many colleges.

Source status: finite-cardinality part of the paper's `F_1` size estimate.
-/
theorem indexPrefixSmall_card_le_index_statement (k C : ℕ) :
    ((definition_indexPrefixSmall_statement k C).card : ℝ) ≤ (k : ℝ) :=
  indexPrefixSmall_card_le_index k C

/--
Definition: concrete floor split index for the paper's `epsilon` fraction.

Source status: PG24 Theorem 2 writes the small block as the first
approximately `epsilon*C` sorted colleges; this is the floor version for the
finite `Fin (C+1)` indexing used here.
-/
noncomputable abbrev definition_epsilonFloorSplitIndex_statement
    (epsilon : ℝ) (C : ℕ) : ℕ :=
  epsilonFloorSplitIndex epsilon C

/--
The floor split index is bounded by `epsilon * (C+1)`.

Source status: finite arithmetic behind the paper's `|F_1| ≤ epsilon C`
estimate.
-/
theorem epsilonFloorSplitIndex_le_statement
    (epsilon : ℝ) (C : ℕ) (hepsilon_nonneg : 0 ≤ epsilon) :
    (definition_epsilonFloorSplitIndex_statement epsilon C : ℝ) ≤
      epsilon * ((C + 1 : ℕ) : ℝ) :=
  epsilonFloorSplitIndex_le epsilon C hepsilon_nonneg

/--
The sorted-index prefix and suffix blocks are disjoint.

Source status: finite-set part of the paper's `F_1/F_2` partition.
-/
theorem indexPrefixSmall_disjoint_indexSuffixLarge_statement (k C : ℕ) :
    Disjoint
      (definition_indexPrefixSmall_statement k C)
      (definition_indexSuffixLarge_statement k C) :=
  indexPrefixSmall_disjoint_indexSuffixLarge k C

/--
Active capacity decomposes over the sorted-index `F_1/F_2` partition.

Source status: finite-capacity accounting used to show that, after removing
the small `F_1` block, the large `F_2` block retains almost all capacity.
-/
theorem activeCapacity_indexPrefixSmall_add_indexSuffixLarge_statement
    (k C : ℕ) (capacity : Fin (C + 1) → ℝ) :
    AppliedModelingLib.Matching.activeCapacity
        (Finset.univ : Finset (Fin (C + 1))) capacity =
      AppliedModelingLib.Matching.activeCapacity
          (definition_indexPrefixSmall_statement k C) capacity +
        AppliedModelingLib.Matching.activeCapacity
          (definition_indexSuffixLarge_statement k C) capacity :=
  activeCapacity_indexPrefixSmall_add_indexSuffixLarge k C capacity

/--
Small active subsets have small total capacity under the PG24 regular-capacity
condition.

Source status: PG24 model regularity condition `S_c < alpha / C` and
amplification proof step `S(C_1) <= epsilon C * alpha / C = epsilon alpha`.
-/
theorem smallActiveSet_capacity_bound_statement
    {College : Type v}
    (active : Finset College) (capacity : College → ℝ)
    {epsilon alpha : ℝ} {C : ℕ}
    (hcard : (active.card : ℝ) ≤ epsilon * (C : ℝ))
    (halpha_nonneg : 0 ≤ alpha) (hC_pos : 0 < (C : ℝ))
    (hcap : ∀ c ∈ active, capacity c ≤ alpha / (C : ℝ)) :
    AppliedModelingLib.Matching.activeCapacity active capacity ≤ epsilon * alpha :=
  smallActiveSet_capacity_le_epsilon_mul_alpha
    active capacity hcard halpha_nonneg hC_pos hcap

/--
Constant-cutoff maximum-order-statistic bridge.

Source status: PG24 attenuation proof and coalition proofs, where a dense
cluster with common cutoff bound is compared to a maximum of independent noise
draws.
-/
theorem constantCutoffAffordanceEvent_bridge_statement
    {C : ℕ} [NeZero C] (noise : Fin C → ℝ) (v P : ℝ) :
    cutoffAffordanceEvent_statement
        (Finset.univ : Finset (Fin C)) v noise (fun _ => P) ↔
      P - v <
        AppliedModelingLib.Probability.upperOrderStatistic noise
          (AppliedModelingLib.Matching.topSampleRank (n := C)) :=
  constantCutoffAffordanceEvent_iff_topOrderStatistic_gt noise v P

/--
Constant-cutoff probability bridge to the reusable maximum-order-statistic
tail probability.

Source status: PG24 attenuation proof, especially the equal-cutoff heuristic
`p_mu(v) = Pr[v + X^(C) > P*]`.
-/
theorem constantCutoffAffordanceProbability_bridge_statement
    {C : ℕ} [NeZero C]
    (noiseLaw : MeasureTheory.Measure (Fin C → ℝ)) (v P : ℝ) :
    cutoffAffordanceProbability_statement noiseLaw
        (Finset.univ : Finset (Fin C)) v (fun _ => P) =
      AppliedModelingLib.Matching.topOrderCrossingProbability noiseLaw (P - v) :=
  constantCutoffAffordanceProbability_eq_topOrderCrossingProbability
    noiseLaw v P

/--
Constant-cutoff iid CDF formula.

Source status: PG24 attenuation and coalition proof routes use the identity
`Pr[v + X^(C) > P] = 1 - F_X(P-v)^C` for iid college noise.  The Lean row
derives this from the shared cutoff-affordance and top-order-statistic bridge.
-/
theorem constantCutoffAffordanceProbability_iidProduct_lowerCDFMass_pow_statement
    {C : ℕ} [NeZero C]
    (noiseLaw : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure noiseLaw] (v P : ℝ) :
    cutoffAffordanceProbability_statement
        (MeasureTheory.Measure.pi (fun _ : Fin C => noiseLaw))
        (Finset.univ : Finset (Fin C)) v (fun _ => P) =
      1 - (AppliedModelingLib.Probability.lowerCDFMass noiseLaw (P - v)) ^ C := by
  simpa [cutoffAffordanceProbability_statement, cutoffAffordanceProbability]
    using
      (AppliedModelingLib.Matching.cutoffCrossingProbability_univ_constant_iidProduct_eq_one_sub_lowerCDFMass_pow
        (n := C) noiseLaw v P)

/--
Max-concentration low-value bound for a cutoff vector bounded below.

Source status: PG24 Proposition tomato upper-bound route; if every active
cutoff is at least `P` and `P - v` is above the center of the maximum order
statistic by `epsilon`, the affordability probability is bounded by the
maximum-order-statistic deviation probability.
-/
theorem cutoffAffordanceProbability_lowerCutoff_deviation_bound_statement
    {C : ℕ} [NeZero C]
    (noiseLaw : MeasureTheory.Measure (Fin C → ℝ))
    [MeasureTheory.IsFiniteMeasure noiseLaw]
    {v P center ε : ℝ} {cutoff : Fin C → ℝ}
    (hlower : ∀ c : Fin C, P ≤ cutoff c)
    (hsep : center + ε ≤ P - v) :
    cutoffAffordanceProbability_statement noiseLaw
        (Finset.univ : Finset (Fin C)) v cutoff ≤
      AppliedModelingLib.Matching.topOrderDeviationProbability noiseLaw center ε :=
  cutoffAffordanceProbability_le_topOrderDeviationProbability_of_uniform_lower_cutoff
    noiseLaw hlower hsep

/--
Max-concentration high-value bound for a cutoff vector bounded above.

Source status: PG24 Proposition tomato lower-bound route; if every active
cutoff is at most `P` and `P - v` is below the center of the maximum order
statistic by `epsilon`, the failure-to-afford probability is bounded by the
maximum-order-statistic deviation probability.
-/
theorem cutoffAffordanceProbability_upperCutoff_failure_deviation_bound_statement
    {C : ℕ} [NeZero C]
    (noiseLaw : MeasureTheory.Measure (Fin C → ℝ))
    [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {v P center ε : ℝ} {cutoff : Fin C → ℝ}
    (hupper : ∀ c : Fin C, cutoff c ≤ P)
    (hε : 0 < ε) (hsep : P - v < center - ε) :
    1 - cutoffAffordanceProbability_statement noiseLaw
        (Finset.univ : Finset (Fin C)) v cutoff ≤
      AppliedModelingLib.Matching.topOrderDeviationProbability noiseLaw center ε :=
  one_sub_cutoffAffordanceProbability_le_topOrderDeviationProbability_of_uniform_upper_cutoff
    noiseLaw hupper hε hsep

/--
Theorem 1 attenuation target.

Source status: PG24 Theorem 1 target.  The rows below expose the
expected-maximum cutoff-sandwich route, the eventual source bounds, the
uniform stable-matching statement, and selected-sequence consequences.
-/
abbrev theorem1_attenuation_statement
    (matchProb : ℕ → ℝ → ℝ) (vS : ℝ) : Prop :=
  theorem1_attenuationConclusion matchProb vS

/--
Theorem 1 clean cutoff-sandwich attenuation route.

Source status: PG24 Theorem 1 proof heuristic made formal: if the cutoff
vector is eventually squeezed between lower and upper thresholds whose gaps
from `E[X^(C)]` converge to the same `vS`, then the affordance probability
converges to the threshold step rule.
-/
theorem theorem1_attenuation_from_expected_max_cutoff_sandwich_statement
    {sampleLaw : ∀ n : ℕ, MeasureTheory.Measure (Fin (n + 1) → ℝ)}
    {lowerCutoff upperCutoff : ℕ → ℝ}
    {cutoff : ∀ n : ℕ, Fin (n + 1) → ℝ}
    {vS : ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
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
    theorem1_attenuation_statement
      (fun n : ℕ => fun v : ℝ =>
        cutoffAffordanceProbability_statement (sampleLaw n)
          (Finset.univ : Finset (Fin (n + 1))) v (cutoff n))
      vS :=
  theorem1_attenuation_of_expected_max_cutoff_sandwich
    hprob hconc hlower hupper hlower_threshold hupper_threshold

/--
Theorem 1 attenuation, eventual-epsilon form.

Source status: PG24 Theorem 1 prose conclusion; this is the source-style
unpacking of the convergence target above.
-/
theorem theorem1_attenuation_eventual_bounds_statement
    {matchProb : ℕ → ℝ → ℝ} {vS : ℝ}
    (h : theorem1_attenuation_statement matchProb vS) :
    (∀ v ε, v < vS → 0 < ε →
      ∀ᶠ C : ℕ in atTop, matchProb C v < ε) ∧
    (∀ v ε, vS < v → 0 < ε →
      ∀ᶠ C : ℕ in atTop, 1 - ε < matchProb C v) :=
  theorem1_attenuation_eventually_bounds h

/--
Theorem 1 attenuation, uniform over all admissible stable matchings.

Source status: PG24 Theorem 1 states the bound for every
`mu in M(D,C)` once `C` is sufficiently large. `Admissible C` is the
paper-facing placeholder for that admissible stable-matching/economy set.
-/
abbrev theorem1_uniform_attenuation_statement
    (Admissible : ℕ → Type*) (matchProb : ∀ C, Admissible C → ℝ → ℝ)
    (vS : ℝ) : Prop :=
  theorem1_uniformAttenuationConclusion Admissible matchProb vS

/--
Theorem 1 source-style bounds from the uniform stable-matching statement.

Source status: PG24 Theorem 1 is uniform over every `mu in M(D,C)`.  Hence
any selected admissible stable matching sequence inherits the below-threshold
and above-threshold eventual bounds.
-/
theorem theorem1_attenuation_eventual_bounds_from_uniform_selected_statement
    {Admissible : ℕ → Type*} {matchProb : ∀ C, Admissible C → ℝ → ℝ}
    {vS : ℝ}
    (select : ∀ C : ℕ, Admissible C)
    (h : theorem1_uniform_attenuation_statement
      Admissible matchProb vS) :
    (∀ v ε, v < vS → 0 < ε →
      ∀ᶠ C : ℕ in atTop, matchProb C (select C) v < ε) ∧
    (∀ v ε, vS < v → 0 < ε →
      ∀ᶠ C : ℕ in atTop, 1 - ε < matchProb C (select C) v) :=
  theorem1_attenuation_eventual_bounds_of_uniform_selected select h

/--
Theorem 1 attenuation follows from uniform appendix error estimates.

Source status: proof-route row for the attenuation appendix; the remaining
analytic work is to prove the visible low-value and high-value error bounds
from max-concentration and cutoff-vector arguments.
-/
theorem theorem1_uniform_attenuation_from_error_certificate_statement
    {Admissible : ℕ → Type*} {matchProb : ∀ C, Admissible C → ℝ → ℝ}
    {vS : ℝ}
    (cert :
      Theorem1UniformAttenuationErrorCertificate
        Admissible matchProb vS) :
    theorem1_uniform_attenuation_statement Admissible matchProb vS :=
  theorem1_uniformAttenuation_of_error_certificate cert

/--
Low-value attenuation algebra from the paper's tail-mass proof step.

Source status: the appendix proof bounds the total matched mass in a
below-threshold interval.  If that mass is at least `epsilon * p` by
monotonicity and below `epsilon^2` by the source estimate, then the pointwise
probability `p` is below `epsilon`.
-/
theorem theorem1_low_value_pointwise_from_tail_mass_statement
    {p epsilon tailMass : ℝ}
    (hepsilon_pos : 0 < epsilon)
    (htail_lower : epsilon * p ≤ tailMass)
    (htail_small : tailMass < epsilon ^ 2) :
    p < epsilon :=
  theorem1_lowValue_pointwise_of_tail_mass_bound
    hepsilon_pos htail_lower htail_small

/--
Low-value attenuation algebra from interval mass.

Source status: PG24 attenuation appendix footnote.  The source derives the
pointwise bound by choosing an interval of value mass at least `epsilon` and
using monotonicity to lower-bound the matched tail mass by
`intervalMass * p`.
-/
theorem theorem1_low_value_pointwise_from_interval_tail_mass_statement
    {p epsilon intervalMass tailMass : ℝ}
    (hepsilon_pos : 0 < epsilon)
    (hp_nonneg : 0 ≤ p)
    (hmass : epsilon ≤ intervalMass)
    (htail_lower : intervalMass * p ≤ tailMass)
    (htail_small : tailMass < epsilon ^ 2) :
    p < epsilon :=
  theorem1_lowValue_pointwise_of_interval_tail_mass_bound
    hepsilon_pos hp_nonneg hmass htail_lower htail_small

/--
High-value attenuation algebra from the paper's tail-mass proof step.

Source status: this is the symmetric unmatched-mass version used above the
threshold.  If the unmatched mass is at least `epsilon * (1 - p)` and below
`epsilon^2`, then `p` is above `1 - epsilon`.
-/
theorem theorem1_high_value_pointwise_from_unmatched_tail_mass_statement
    {p epsilon tailMass : ℝ}
    (hepsilon_pos : 0 < epsilon)
    (htail_lower : epsilon * (1 - p) ≤ tailMass)
    (htail_small : tailMass < epsilon ^ 2) :
    1 - epsilon < p :=
  theorem1_highValue_pointwise_of_unmatched_tail_mass_bound
    hepsilon_pos htail_lower htail_small

/--
High-value attenuation algebra from interval unmatched mass.

Source status: PG24 attenuation appendix footnote, symmetric high-value
argument.  An interval of mass at least `epsilon` and monotonicity lower-bound
the unmatched tail mass by `intervalMass * (1 - p)`.
-/
theorem theorem1_high_value_pointwise_from_interval_unmatched_tail_mass_statement
    {p epsilon intervalMass tailMass : ℝ}
    (hepsilon_pos : 0 < epsilon)
    (hfailure_nonneg : 0 ≤ 1 - p)
    (hmass : epsilon ≤ intervalMass)
    (htail_lower : intervalMass * (1 - p) ≤ tailMass)
    (htail_small : tailMass < epsilon ^ 2) :
    1 - epsilon < p :=
  theorem1_highValue_pointwise_of_interval_unmatched_tail_mass_bound
    hepsilon_pos hfailure_nonneg hmass htail_lower htail_small

/--
Theorem 1 uniform low-value bound from uniformly small matched tail mass.

Source status: paper-facing wrapper for the attenuation appendix.  The
remaining source work is to derive the visible tail-mass lower and upper
bounds from the cutoff-density decomposition.
-/
theorem theorem1_uniform_low_value_from_tail_mass_statement
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
      ∀ μ : Admissible C, matchProb C μ v < epsilon :=
  theorem1_uniform_lowValue_eventually_of_tail_mass_bound
    hepsilon_pos htail_small htail_lower

/--
Theorem 1 uniform high-value bound from uniformly small unmatched tail mass.

Source status: paper-facing wrapper for the attenuation appendix above the
threshold; the source proof must supply the displayed unmatched-mass bounds.
-/
theorem theorem1_uniform_high_value_from_unmatched_tail_mass_statement
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
      ∀ μ : Admissible C, 1 - epsilon < matchProb C μ v :=
  theorem1_uniform_highValue_eventually_of_unmatched_tail_mass_bound
    hepsilon_pos htail_small htail_lower

/--
Theorem 1 uniform low-value bound from interval matched mass.

Source status: PG24 attenuation appendix footnote.  This row keeps the
interval-mass lower bound visible before deriving the low-value pointwise
probability bound uniformly over stable matchings.
-/
theorem theorem1_uniform_low_value_from_interval_tail_mass_statement
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
      ∀ μ : Admissible C, matchProb C μ v < epsilon :=
  theorem1_uniform_lowValue_eventually_of_interval_tail_mass_bound
    hepsilon_pos hprob_nonneg hmass htail_lower htail_small

/--
Theorem 1 uniform high-value bound from interval unmatched mass.

Source status: PG24 attenuation appendix footnote, symmetric high-value
argument.  The visible interval-mass lower bound and unmatched-tail estimate
imply the uniform above-threshold pointwise bound.
-/
theorem theorem1_uniform_high_value_from_interval_unmatched_tail_mass_statement
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
      ∀ μ : Admissible C, 1 - epsilon < matchProb C μ v :=
  theorem1_uniform_highValue_eventually_of_interval_unmatched_tail_mass_bound
    hepsilon_pos hfailure_nonneg hmass htail_lower htail_small

/--
Theorem 1 uniform attenuation from the source tail-mass route.

Source status: this is the source-aligned replacement for a broad abstract
attenuation premise.  To close the row, the formalization must derive the
displayed low-value matched-mass and high-value unmatched-mass estimates from
the paper's cutoff-density decomposition.
-/
theorem theorem1_uniform_attenuation_from_tail_mass_bounds_statement
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
    theorem1_uniform_attenuation_statement Admissible matchProb vS :=
  theorem1_uniformAttenuation_of_tail_mass_bounds hlow hhigh

/--
Theorem 1 uniform attenuation from the source interval-mass route.

Source status: PG24 attenuation appendix.  This is the source-facing
refinement of the tail-mass route: it exposes the interval mass, probability
nonnegativity, and interval-to-tail lower bounds used in the proof.
-/
theorem theorem1_uniform_attenuation_from_interval_tail_mass_bounds_statement
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
    theorem1_uniform_attenuation_statement Admissible matchProb vS :=
  theorem1_uniformAttenuation_of_interval_tail_mass_bounds hlow hhigh

/--
Theorem 1 uniform attenuation from uniformly vanishing interval tail masses.

Source status: PG24 Proposition `thm1v2` proves the relevant matched or
unmatched tail masses vanish with a polynomial rate.  This row converts that
source-shaped vanishing statement into the `epsilon^2` interval-mass
obligations used by the pointwise attenuation algebra.
-/
theorem theorem1_uniform_attenuation_from_interval_tail_mass_vanishes_statement
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
    theorem1_uniform_attenuation_statement Admissible matchProb vS :=
  theorem1_uniformAttenuation_of_interval_tail_mass_tendsto_zero hlow hhigh

/--
Theorem 1 uniform attenuation from polynomial interval tail-mass bounds.

Source status: PG24 Proposition `thm1v2` proves the relevant tail masses are
`O(C^{-K})`.  This row exposes that rate-style source statement and derives
the vanishing-tail-mass bridge internally.
-/
theorem theorem1_uniform_attenuation_from_interval_tail_mass_polynomial_bound_statement
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
    theorem1_uniform_attenuation_statement Admissible matchProb vS :=
  theorem1_uniformAttenuation_of_interval_tail_mass_polynomial_bound hlow hhigh

/--
Theorem 1 uniform attenuation from cutoff-affordance interval tail-mass bounds.

Source status: PG24 Proposition `thm1v2` in the concrete cutoff-probability
shape.  The paper proof supplies interval-mass lower bounds and polynomial
tail-mass estimates; Lean derives the needed probability nonnegativity and
`1 - p` nonnegativity from the cutoff-affordance probability definition.
-/
theorem theorem1_uniform_attenuation_from_cutoff_interval_tail_mass_polynomial_bound_statement
    {Admissible : ℕ → Type*}
    {sampleLaw : ∀ C : ℕ, MeasureTheory.Measure (Fin (C + 1) → ℝ)}
    {active : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1))}
    {cutoff : ∀ C : ℕ, Admissible C → Fin (C + 1) → ℝ}
    {vS : ℝ}
    (hprob : ∀ C : ℕ, MeasureTheory.IsProbabilityMeasure (sampleLaw C))
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
                  cutoffAffordanceProbability_statement
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
                  (1 - cutoffAffordanceProbability_statement
                    (sampleLaw C) (active C μ) v (cutoff C μ)) ≤
                tailMass C μ) ∧
          (∀ C : ℕ, N0 ≤ C →
            ∀ μ : Admissible C,
              tailMass C μ ≤
                A * Real.rpow (((C + 1 : ℕ) : ℝ)) (-rate))) :
    theorem1_uniform_attenuation_statement
      Admissible
      (fun C : ℕ => fun μ : Admissible C => fun v : ℝ =>
        cutoffAffordanceProbability_statement
          (sampleLaw C) (active C μ) v (cutoff C μ))
      vS :=
  theorem1_uniformAttenuation_of_cutoff_interval_tail_mass_polynomial_bound
    hprob hlow hhigh

/--
Theorem 1 (attenuation), derived from the literal source economy.

Source status: corrected direct formalization of `main-results.tex:3-15` and
`proof-attenuating.tex`. The source proof's displayed polynomial intermediate
has endpoint, sign, rounding, and uniformity defects; this row proves the
published pointwise conclusion directly and does not assume either tail bound.
Every admissible economy and selected clearing cutoff remains inside the
eventual quantifier.
-/
theorem theorem1_attenuation_from_literal_source_primitives_statement
    {Admissible : ℕ → Type w}
    {StudentType : (C : ℕ) → Admissible C → Type u}
    [∀ (C : ℕ) (a : Admissible C), MeasurableSpace (StudentType C a)]
    {Cutoff : (C : ℕ) → Admissible C → Type v}
    (noiseLaw eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    {maxVariance : ℕ → ℝ} {alpha beta totalSupply vS : ℝ}
    (market : ∀ (C : ℕ) (a : Admissible C),
      PG24LiteralBasicMarket C noiseLaw eta totalSupply alpha
        (StudentType C a) (Cutoff C a))
    (selectedCutoff : ∀ (C : ℕ) (a : Admissible C), Cutoff C a)
    (selectedCutoff_clearing : ∀ (C : ℕ) (a : Admissible C),
      (market C a).marketClearing (selectedCutoff C a))
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (halpha_nonneg : 0 ≤ alpha)
    (hregular : PG24HolderIntervalRegular eta)
    (hconnected : IsPreconnected eta.support)
    (htotalSupply_pos : 0 < totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (htail_normalization : eta.real (Set.Ioi vS) = totalSupply) :
    (∀ value epsilon : ℝ, value < vS → 0 < epsilon →
      ∀ᶠ C : ℕ in atTop, ∀ a : Admissible C,
        cutoffAffordanceProbability_statement
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) value
          ((market C a).demand.cutoffCoordinates (selectedCutoff C a)) <
            epsilon) ∧
    (∀ value epsilon : ℝ, vS < value → 0 < epsilon →
      ∀ᶠ C : ℕ in atTop, ∀ a : Admissible C,
        1 - epsilon < cutoffAffordanceProbability_statement
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) value
          ((market C a).demand.cutoffCoordinates (selectedCutoff C a))) := by
  simpa only [PG24LiteralBasicMarket.basicInstanceAt_selectedCutoffVector] using
    (theorem1_literal_uniform_selected_attenuation_source_clauses_of_beta_holder
      (Admissible := Admissible) noiseLaw eta
      (fun C a =>
        (market C a).basicInstanceAt
          (selectedCutoff C a) (selectedCutoff_clearing C a))
      hbeta hvariance halpha_nonneg hregular hconnected htotalSupply_pos
      htotalSupply_lt_one htail_normalization)

/--
Theorem 1 uniform attenuation from a uniform cutoff-sandwich route.

Source status: PG24 Theorem 1 is uniform over every `mu in M(D,C)`.
This row removes the abstract error-certificate layer when the appendix proof
has already supplied uniform lower and upper cutoff thresholds around
`E[X^(C)]`.
-/
theorem theorem1_uniform_attenuation_from_expected_max_cutoff_sandwich_statement
    {Admissible : ℕ → Type*}
    {sampleLaw : ∀ n : ℕ, MeasureTheory.Measure (Fin (n + 1) → ℝ)}
    {lowerCutoff upperCutoff : ℕ → ℝ}
    {cutoff : ∀ n : ℕ, Admissible n → Fin (n + 1) → ℝ}
    {vS : ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
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
    theorem1_uniform_attenuation_statement
      Admissible
      (fun n : ℕ => fun μ : Admissible n => fun v : ℝ =>
        cutoffAffordanceProbability_statement (sampleLaw n)
          (Finset.univ : Finset (Fin (n + 1))) v (cutoff n μ))
      vS :=
  theorem1_uniformAttenuation_of_expected_max_cutoff_sandwich
    hprob hconc hlower hupper hlower_threshold hupper_threshold

/--
Theorem 1 uniform attenuation over stable matchings via the A-L
stable-to-cutoff bridge.

Source status: PG24 Theorem 1 is stated for every stable matching
`mu in M(D,C)`.  This row starts from stable matchings directly: A-L Lemma 1
chooses each stable matching's market-clearing cutoff, then the source
cutoff-sandwich bounds for all market-clearing cutoffs imply the uniform
attenuation conclusion.
-/
theorem theorem1_uniform_attenuation_from_stable_matching_cutoff_sandwich_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ n : ℕ, CutoffMarket (StudentSeq n) (Fin (n + 1)))
    (Iseq : ∀ n : ℕ, SupplyDemandInterface (Mseq n))
    {sampleLaw : ∀ n : ℕ, MeasureTheory.Measure (Fin (n + 1) → ℝ)}
    {lowerCutoff upperCutoff : ℕ → ℝ}
    (cutoffOut : ∀ n : ℕ, (Mseq n).Cutoff → Fin (n + 1) → ℝ)
    {vS : ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
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
    theorem1_uniform_attenuation_statement
      (fun n : ℕ => { μ : (Mseq n).Matching // (Mseq n).Stable μ })
      (fun n : ℕ =>
        fun μ : { μ : (Mseq n).Matching // (Mseq n).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability_statement (sampleLaw n)
            (Finset.univ : Finset (Fin (n + 1))) v
            (cutoffOut n
              ((Iseq n).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      vS :=
  theorem1_uniformAttenuation_of_expected_max_stable_cutoff_sandwich
    Mseq Iseq cutoffOut hprob hconc hlower_market hupper_market
    hlower_threshold hupper_threshold

/--
Theorem 1 attenuation from β-max-concentrating variance and cutoff-sandwich
estimates.

Source status: PG24 Theorem 1 proof route from the paper's
β-max-concentrating variance definition, Chebyshev concentration, and the
appendix cutoff-vector sandwich around the expected maximum order statistic.
-/
theorem theorem1_uniform_attenuation_from_betaMax_variance_cutoff_sandwich_statement
    {Admissible : ℕ → Type*}
    {sampleLaw : ∀ n : ℕ, MeasureTheory.Measure (Fin (n + 1) → ℝ)}
    {maxVariance lowerCutoff upperCutoff : ℕ → ℝ}
    {cutoff : ∀ n : ℕ, Admissible n → Fin (n + 1) → ℝ}
    {β vS : ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
    (hbeta : definition_betaMaxConcentrating_variance_statement maxVariance β)
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
    theorem1_uniform_attenuation_statement
      Admissible
      (fun n : ℕ => fun μ : Admissible n => fun v : ℝ =>
        cutoffAffordanceProbability_statement (sampleLaw n)
          (Finset.univ : Finset (Fin (n + 1))) v (cutoff n μ))
      vS :=
  theorem1_uniformAttenuation_of_betaMax_variance_cutoff_sandwich
    hprob hbeta hchebyshev hlower hupper hlower_threshold hupper_threshold

/--
Theorem 1 attenuation from β-max-concentrating variance, an actual variance
bound for the maximum order statistic, and cutoff-sandwich estimates.

Source status: preferred PG24 Theorem 1 proof route.  The visible
probabilistic input is the source variance calculation for the maximum order
statistic; Chebyshev is supplied by the shared order-statistics library.
-/
theorem theorem1_uniform_attenuation_from_betaMax_variance_bound_cutoff_sandwich_statement
    {Admissible : ℕ → Type*}
    {sampleLaw : ∀ n : ℕ, MeasureTheory.Measure (Fin (n + 1) → ℝ)}
    {maxVariance lowerCutoff upperCutoff : ℕ → ℝ}
    {cutoff : ∀ n : ℕ, Admissible n → Fin (n + 1) → ℝ}
    {β vS : ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
    (hbeta : definition_betaMaxConcentrating_variance_statement maxVariance β)
    (hvariance_bound :
      source_assumption_beta_max_variance_bound sampleLaw maxVariance)
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
    theorem1_uniform_attenuation_statement
      Admissible
      (fun n : ℕ => fun μ : Admissible n => fun v : ℝ =>
        cutoffAffordanceProbability_statement (sampleLaw n)
          (Finset.univ : Finset (Fin (n + 1))) v (cutoff n μ))
      vS :=
  theorem1_uniformAttenuation_of_betaMax_variance_bound_cutoff_sandwich
    hprob hbeta hvariance_bound.1 hvariance_bound.2
    hlower hupper hlower_threshold hupper_threshold

/--
Theorem 1 attenuation over stable matchings from β-max-concentrating variance.

Source status: PG24 Theorem 1 in the paper's stable-matching form.  A-L
selects each stable matching's market-clearing cutoff, and the paper's
β-max-concentrating variance definition plus Chebyshev supplies the
maximum-order concentration needed by the cutoff-sandwich proof.
-/
theorem theorem1_uniform_attenuation_from_betaMax_variance_stable_matching_cutoff_sandwich_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ n : ℕ, CutoffMarket (StudentSeq n) (Fin (n + 1)))
    (Iseq : ∀ n : ℕ, SupplyDemandInterface (Mseq n))
    {sampleLaw : ∀ n : ℕ, MeasureTheory.Measure (Fin (n + 1) → ℝ)}
    {maxVariance lowerCutoff upperCutoff : ℕ → ℝ}
    (cutoffOut : ∀ n : ℕ, (Mseq n).Cutoff → Fin (n + 1) → ℝ)
    {β vS : ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
    (hbeta : definition_betaMaxConcentrating_variance_statement maxVariance β)
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
    theorem1_uniform_attenuation_statement
      (fun n : ℕ => { μ : (Mseq n).Matching // (Mseq n).Stable μ })
      (fun n : ℕ =>
        fun μ : { μ : (Mseq n).Matching // (Mseq n).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability_statement (sampleLaw n)
            (Finset.univ : Finset (Fin (n + 1))) v
            (cutoffOut n
              ((Iseq n).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      vS :=
  theorem1_uniformAttenuation_of_betaMax_variance_stable_cutoff_sandwich
    Mseq Iseq cutoffOut hprob hbeta hchebyshev
    hlower_market hupper_market hlower_threshold hupper_threshold

/--
Theorem 1 attenuation over stable matchings from β-max-concentrating variance
and an actual variance bound for the maximum order statistic.

Source status: preferred PG24 Theorem 1 stable-matching route.  A-L selects
each stable matching's market-clearing cutoff, the source variance calculation
bounds `Var[X^(n)]`, and the shared library derives the Chebyshev
concentration step.
-/
theorem theorem1_uniform_attenuation_from_betaMax_variance_bound_stable_matching_cutoff_sandwich_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ n : ℕ, CutoffMarket (StudentSeq n) (Fin (n + 1)))
    (Iseq : ∀ n : ℕ, SupplyDemandInterface (Mseq n))
    {sampleLaw : ∀ n : ℕ, MeasureTheory.Measure (Fin (n + 1) → ℝ)}
    {maxVariance lowerCutoff upperCutoff : ℕ → ℝ}
    (cutoffOut : ∀ n : ℕ, (Mseq n).Cutoff → Fin (n + 1) → ℝ)
    {β vS : ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
    (hbeta : definition_betaMaxConcentrating_variance_statement maxVariance β)
    (hvariance_bound :
      source_assumption_beta_max_variance_bound sampleLaw maxVariance)
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
    theorem1_uniform_attenuation_statement
      (fun n : ℕ => { μ : (Mseq n).Matching // (Mseq n).Stable μ })
      (fun n : ℕ =>
        fun μ : { μ : (Mseq n).Matching // (Mseq n).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability_statement (sampleLaw n)
            (Finset.univ : Finset (Fin (n + 1))) v
            (cutoffOut n
              ((Iseq n).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      vS :=
  theorem1_uniformAttenuation_of_betaMax_variance_bound_stable_cutoff_sandwich
    Mseq Iseq cutoffOut hprob hbeta hvariance_bound.1 hvariance_bound.2
    hlower_market hupper_market hlower_threshold hupper_threshold

/--
Theorem 1 source clauses from the preferred stable-matching route.

Source status: PG24 Theorem 1 in its paper-facing eventual form.  A-L
selects a market-clearing cutoff for each stable matching; beta-max variance
and the maximum-order-statistic variance bound give concentration; the cutoff
sandwich estimates then imply the two explicit clauses: low values eventually
match with probability below any epsilon, and high values eventually match
with probability at least one minus epsilon.
-/
theorem theorem1_uniform_attenuation_source_clauses_from_betaMax_variance_bound_stable_matching_cutoff_sandwich_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ n : ℕ, CutoffMarket (StudentSeq n) (Fin (n + 1)))
    (Iseq : ∀ n : ℕ, SupplyDemandInterface (Mseq n))
    {sampleLaw : ∀ n : ℕ, MeasureTheory.Measure (Fin (n + 1) → ℝ)}
    {maxVariance lowerCutoff upperCutoff : ℕ → ℝ}
    (cutoffOut : ∀ n : ℕ, (Mseq n).Cutoff → Fin (n + 1) → ℝ)
    {β vS : ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
    (hbeta : definition_betaMaxConcentrating_variance_statement maxVariance β)
    (hvariance_bound :
      source_assumption_beta_max_variance_bound sampleLaw maxVariance)
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
          cutoffAffordanceProbability_statement (sampleLaw C)
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)) <
            ε) ∧
    (∀ v ε, vS < v → 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          1 - ε <
            cutoffAffordanceProbability_statement (sampleLaw C)
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))) :=
  theorem1_uniformAttenuation_source_clauses_of_betaMax_variance_bound_stable_cutoff_sandwich
    Mseq Iseq cutoffOut hprob hbeta hvariance_bound.1 hvariance_bound.2
    hlower_market hupper_market hlower_threshold hupper_threshold

/--
Theorem 1 source clauses from selected-stable cutoff-sandwich estimates.

Source status: narrowed PG24 Theorem 1 stable-matching route.  The lower and
upper cutoff estimates are required only for the A-L selected cutoff attached
to each stable matching, which is the only cutoff used in the final
uniform-over-stable-matchings conclusion.
-/
theorem theorem1_uniform_attenuation_source_clauses_from_betaMax_variance_bound_selected_stable_cutoff_sandwich_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ n : ℕ, CutoffMarket (StudentSeq n) (Fin (n + 1)))
    (Iseq : ∀ n : ℕ, SupplyDemandInterface (Mseq n))
    {sampleLaw : ∀ n : ℕ, MeasureTheory.Measure (Fin (n + 1) → ℝ)}
    {maxVariance lowerCutoff upperCutoff : ℕ → ℝ}
    (cutoffOut : ∀ n : ℕ, (Mseq n).Cutoff → Fin (n + 1) → ℝ)
    {β vS : ℝ}
    (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (sampleLaw n))
    (hbeta : definition_betaMaxConcentrating_variance_statement maxVariance β)
    (hvariance_bound :
      source_assumption_beta_max_variance_bound sampleLaw maxVariance)
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
          cutoffAffordanceProbability_statement (sampleLaw C)
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)) <
            ε) ∧
    (∀ v ε, vS < v → 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          1 - ε <
            cutoffAffordanceProbability_statement (sampleLaw C)
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))) :=
  theorem1_uniformAttenuation_source_clauses_of_betaMax_variance_bound_selected_stable_cutoff_sandwich
    Mseq Iseq cutoffOut hprob hbeta hvariance_bound.1 hvariance_bound.2
    hlower_selected hupper_selected hlower_threshold hupper_threshold

/--
Theorem 1 source clauses in the paper's iid product-noise model.

Source status: narrowed PG24 Theorem 1 route.  This is the selected-stable
cutoff-sandwich theorem specialized to the paper's independent product noise
law, so the conclusion and variance inputs are stated directly with
`Measure.pi (fun _ => noiseLaw)` rather than an abstract sample-law sequence.
-/
theorem theorem1_uniform_attenuation_source_clauses_from_iidProduct_betaMax_variance_bound_selected_stable_cutoff_sandwich_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ n : ℕ, CutoffMarket (StudentSeq n) (Fin (n + 1)))
    (Iseq : ∀ n : ℕ, SupplyDemandInterface (Mseq n))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance lowerCutoff upperCutoff : ℕ → ℝ}
    (cutoffOut : ∀ n : ℕ, (Mseq n).Cutoff → Fin (n + 1) → ℝ)
    {β vS : ℝ}
    (hbeta : definition_betaMaxConcentrating_variance_statement maxVariance β)
    (hvariance_bound :
      source_assumption_iid_beta_max_variance_bound noiseLaw maxVariance)
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
          cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)) <
            ε) ∧
    (∀ v ε, vS < v → 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          1 - ε <
            cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))) :=
  theorem1_uniformAttenuation_source_clauses_of_iidProduct_betaMax_variance_bound_selected_stable_cutoff_sandwich
    Mseq Iseq noiseLaw cutoffOut hbeta hvariance_bound.1 hvariance_bound.2
    hlower_selected hupper_selected hlower_threshold hupper_threshold

/--
Theorem 1 source clauses from the named PG24 attenuation source model.

Source status: active PG24 Theorem 1 route with the beta-max variance,
market-clearing cutoff sandwich, and threshold convergence source clauses
bundled for recursive source-record audit.  The selected-stable cutoff
inequalities used in the conclusion are derived from the A-L bridge.
-/
theorem theorem1_uniform_attenuation_source_assumptions_from_iidProduct_betaMax_variance_bound_selected_stable_cutoff_sandwich_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ n : ℕ, CutoffMarket (StudentSeq n) (Fin (n + 1)))
    (Iseq : ∀ n : ℕ, SupplyDemandInterface (Mseq n))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance lowerCutoff upperCutoff : ℕ → ℝ}
    (cutoffOut : ∀ n : ℕ, (Mseq n).Cutoff → Fin (n + 1) → ℝ)
    {β vS : ℝ}
    (H :
      Theorem1AttenuationSourceModel
        Mseq Iseq noiseLaw maxVariance lowerCutoff upperCutoff cutoffOut
        β vS) :
    (∀ v ε, v < vS → 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)) <
            ε) ∧
    (∀ v ε, vS < v → 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          1 - ε <
            cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))) :=
  theorem1_uniform_attenuation_source_clauses_from_betaMax_variance_bound_stable_matching_cutoff_sandwich_statement
    (Mseq := Mseq) (Iseq := Iseq)
    (sampleLaw := fun n : ℕ =>
      Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
    (maxVariance := maxVariance) (lowerCutoff := lowerCutoff)
    (upperCutoff := upperCutoff) (β := β) (vS := vS)
    cutoffOut
    (fun _ => by infer_instance)
    H.beta_variance H.variance_bound H.lower_market H.upper_market
    H.lower_threshold H.upper_threshold

/--
Theorem 1 attenuation from the named PG24 source model package and bundled
A-L cutoff-market consequence certificates.

Source status: same active PG24 Theorem 1 route as above, but each finite
market's supply/demand bridge is projected from the transparent A-L consequence
package shared with the other PG matching paper.
-/
theorem theorem1_uniform_attenuation_source_assumptions_from_AL_cutoffMarketConsequences_iidProduct_betaMax_variance_bound_selected_stable_cutoff_sandwich_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ n : ℕ, CutoffMarket (StudentSeq n) (Fin (n + 1)))
    (Aseq :
      ∀ n : ℕ,
        AL16SupplyDemandMatching.CutoffMarketConsequences (Mseq n))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance lowerCutoff upperCutoff : ℕ → ℝ}
    (cutoffOut : ∀ n : ℕ, (Mseq n).Cutoff → Fin (n + 1) → ℝ)
    {β vS : ℝ}
    (H :
      Theorem1AttenuationSourceModel
        Mseq (fun n => (Aseq n).supplyDemand) noiseLaw
        maxVariance lowerCutoff upperCutoff cutoffOut β vS) :
    (∀ v ε, v < vS → 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                (((Aseq C).supplyDemand).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2)) <
            ε) ∧
    (∀ v ε, vS < v → 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          1 - ε <
            cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                (((Aseq C).supplyDemand).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2))) :=
  theorem1_uniform_attenuation_source_assumptions_from_iidProduct_betaMax_variance_bound_selected_stable_cutoff_sandwich_statement
    Mseq (fun n => (Aseq n).supplyDemand) noiseLaw cutoffOut H

/--
Theorem 1 attenuation from the single explicit A-L source-model boundary.

Source status: same active PG24 Theorem 1 route as the A-L consequence wrapper,
but each finite market's consequence package is derived from the explicit AL
source-model record.
-/
theorem theorem1_uniform_attenuation_source_assumptions_from_AL_source_model_iidProduct_betaMax_variance_bound_selected_stable_cutoff_sandwich_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ n : ℕ, CutoffMarket (StudentSeq n) (Fin (n + 1)))
    (leCutoffSeq :
      ∀ n : ℕ, (Mseq n).Cutoff → (Mseq n).Cutoff → Prop)
    (HALseq :
      ∀ n : ℕ,
        AL16SupplyDemandMatching.CutoffMarketConsequenceSourceModel
          (Mseq n) (leCutoffSeq n))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance lowerCutoff upperCutoff : ℕ → ℝ}
    (cutoffOut : ∀ n : ℕ, (Mseq n).Cutoff → Fin (n + 1) → ℝ)
    {β vS : ℝ}
    (H :
      Theorem1AttenuationSourceModel
        Mseq
        (fun n =>
          (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
            (Mseq n) (HALseq n)).supplyDemand)
        noiseLaw maxVariance lowerCutoff upperCutoff cutoffOut β vS) :
    (∀ v ε, v < vS → 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                (SupplyDemandInterface.marketClearingCutoffOfStable
                  (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
                    (Mseq C) (HALseq C)).supplyDemand
                  (μ := μ.1) μ.2)) <
            ε) ∧
    (∀ v ε, vS < v → 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          1 - ε <
            cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                (SupplyDemandInterface.marketClearingCutoffOfStable
                  (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
                    (Mseq C) (HALseq C)).supplyDemand
                  (μ := μ.1) μ.2))) :=
  theorem1_uniform_attenuation_source_assumptions_from_AL_cutoffMarketConsequences_iidProduct_betaMax_variance_bound_selected_stable_cutoff_sandwich_statement
    Mseq
    (fun n =>
      AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
        (Mseq n) (HALseq n))
    noiseLaw cutoffOut H

/--
Theorem 2 amplification target.

Source status: PG24 Theorem 2 target.  The rows below expose the
source-window route, large- and small-firm decomposition, long-tail product
estimate, and uniform-to-selected convergence consequence.
-/
abbrev theorem2_amplification_statement
    (matchProb : ℕ → ℝ → ℝ) (totalSupply : ℝ) : Prop :=
  theorem2_amplificationConclusion matchProb totalSupply

/--
Theorem 2 amplification, eventual-epsilon form.

Source status: PG24 Theorem 2 prose conclusion; this is the source-style
unpacking of convergence to total supply.
-/
theorem theorem2_amplification_eventual_abs_bound_statement
    {matchProb : ℕ → ℝ → ℝ} {totalSupply : ℝ}
    (h : theorem2_amplification_statement matchProb totalSupply) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop, |matchProb C v - totalSupply| < ε :=
  theorem2_amplification_eventually_abs_bound h

/--
Theorem 2 amplification, uniform over all admissible stable matchings.

Source status: PG24 Theorem 2 states the bound for every
`mu in M(D,C)` once `C` is sufficiently large.
-/
abbrev theorem2_uniform_amplification_statement
    (Admissible : ℕ → Type*) (matchProb : ∀ C, Admissible C → ℝ → ℝ)
    (totalSupply : ℝ) : Prop :=
  theorem2_uniformAmplificationConclusion Admissible matchProb totalSupply

/--
Theorem 2 ordinary convergence from the uniform stable-matching statement.

Source status: PG24 Theorem 2 is stated uniformly over every
`mu in M(D,C)`.  Therefore any selected admissible stable matching sequence
inherits the pointwise convergence-to-supply conclusion.
-/
theorem theorem2_amplification_from_uniform_selected_statement
    {Admissible : ℕ → Type*} {matchProb : ∀ C, Admissible C → ℝ → ℝ}
    {totalSupply : ℝ}
    (select : ∀ C : ℕ, Admissible C)
    (h : theorem2_uniform_amplification_statement
      Admissible matchProb totalSupply) :
    theorem2_amplification_statement
      (fun C : ℕ => fun v : ℝ => matchProb C (select C) v)
      totalSupply :=
  theorem2_amplification_of_uniform_selected select h

/--
Theorem 2 amplification follows from a uniform long-tail error estimate.

Source status: proof-route row for the amplification appendix; the remaining
analytic work is to prove the visible absolute-error bound from long-tailed
cutoff-vector estimates.
-/
theorem theorem2_uniform_amplification_from_error_certificate_statement
    {Admissible : ℕ → Type*} {matchProb : ∀ C, Admissible C → ℝ → ℝ}
    {totalSupply : ℝ}
    (cert :
      Theorem2UniformAmplificationErrorCertificate
        Admissible matchProb totalSupply) :
    theorem2_uniform_amplification_statement
      Admissible matchProb totalSupply :=
  theorem2_uniformAmplification_of_error_certificate cert

/--
Theorem 2 amplification from source-style interval estimates.

Source status: PG24 amplification appendix proves two-sided eventual windows
around total supply, culminating in equation `equiv-lt`.  This row converts
those windows into the theorem's uniform absolute-value convergence claim.
-/
theorem theorem2_uniform_amplification_from_eventual_interval_statement
    {Admissible : ℕ → Type*} {matchProb : ∀ C, Admissible C → ℝ → ℝ}
    {totalSupply : ℝ}
    (hinterval :
      ∀ v tol, 0 < tol →
        ∀ᶠ C : ℕ in atTop,
          ∀ μ : Admissible C,
            totalSupply - tol ≤ matchProb C μ v ∧
              matchProb C μ v ≤ totalSupply + tol) :
    theorem2_uniform_amplification_statement
      Admissible matchProb totalSupply :=
  theorem2_uniformAmplification_of_eventual_interval hinterval

/--
The displayed Theorem 2 lower and upper source errors can be made arbitrarily
small.

Source status: PG24 amplification appendix, after equation `equiv-lt`, where
the source notes that the interval around `S` vanishes as the approximation
parameter goes to zero.
-/
theorem theorem2_source_error_parameters_exist_small_statement
    {totalSupply alpha tol : ℝ}
    (htotalSupply_lt_one : totalSupply < 1) (htol : 0 < tol) :
    ∃ epsilon sigma : ℝ,
      0 < epsilon ∧ 0 < sigma ∧
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) ∧
        theorem2_sourceLowerError alpha epsilon sigma < tol ∧
        theorem2_sourceUpperError totalSupply alpha epsilon sigma < tol :=
  theorem2_sourceErrorParameters_exist_small htotalSupply_lt_one htol

/--
Theorem 2 small-firm bound from the source capacity/integral inequality.

Source status: PG24 Proposition `lt-small-firms`.  This row proves the final
division algebra after the source capacity and integration argument supplies
the visible lower-bound inequality.
-/
theorem theorem2_small_firm_source_bound_from_capacity_mass_statement
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
    theorem2_smallFirmSourceBound totalSupply alpha epsilon sigma p :=
  theorem2_smallFirmSourceBound_of_capacity_mass_lower_bound
    hepsilon_pos hden_pos hcapacity_mass

/--
Theorem 2 small-firm bound from the paper's `v*` monotonicity step.

Source status: PG24 Proposition `lt-small-firms`.  The capacity/integral
argument bounds small-firm affordability at `v*`; monotonicity in value gives
the same bound for every `v <= v*`.
-/
theorem theorem2_small_firm_source_bound_from_star_capacity_mass_statement
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
    theorem2_smallFirmSourceBound totalSupply alpha epsilon sigma (pSmall v) :=
  theorem2_smallFirmSourceBound_of_star_capacity_mass
    hepsilon_pos hden_pos hp_mono hv hcapacity_mass_star

/--
Theorem 2 small-firm bound from the active-capacity comparison at `v*`.

Source status: PG24 Proposition `lt-small-firms`.  This row combines the
paper's lower bound on the mass of students matched to `C1`, the regular
capacity/cardinality bound `S(C1) <= epsilon * alpha`, and monotonicity in
student value.
-/
theorem theorem2_small_firm_source_bound_from_star_active_capacity_lower_bound_statement
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
    theorem2_smallFirmSourceBound totalSupply alpha epsilon sigma (pSmall v) :=
  theorem2_smallFirmSourceBound_of_star_active_capacity_lower_bound
    active capacity hepsilon_pos hden_pos hp_mono hv hcard halpha_nonneg
    hC_pos hcap hlower

/--
Theorem 2 eventual small-firm bound from the paper's `v*` monotonicity step.

Source status: PG24 Proposition `lt-small-firms`, eventual-market form used in
the final amplification proof.
-/
theorem theorem2_small_firm_source_bound_eventually_from_star_capacity_mass_statement
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
        totalSupply alpha epsilon sigma (pSmall C v) :=
  theorem2_smallFirmSourceBound_eventually_of_star_capacity_mass
    hepsilon_pos hden_pos hp_mono hv hcapacity_mass_star

/--
Theorem 2 eventual small-firm bound from active-capacity comparisons.

Source status: PG24 Proposition `lt-small-firms`, finite-market form.  The
remaining analytic input is the lower bound comparing the interval integral
with the active capacity of `C1`; Lean derives the regular-capacity upper
bound and the displayed source bound.
-/
theorem theorem2_small_firm_source_bound_eventually_from_star_active_capacity_lower_bound_statement
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
          (pSmall C μ v) :=
  theorem2_smallFirmSourceBound_eventually_of_star_active_capacity_lower_bound
    small capacity hepsilon_pos hden_pos hp_mono hv hcard halpha_nonneg
    hcap hlower

/--
Theorem 2 amplification directly from the source endpoint estimates.

Source status: PG24 Theorem 2 proof route through Proposition
`lt-large-firms`, Proposition `lt-small-firms`, and the final `C1/C2`
decomposition.  The remaining source work is to prove the listed endpoint
mass/capacity estimates and product gap from the primitive cutoff model.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_source_endpoint_estimates_statement
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
    theorem2_uniform_amplification_statement
      Admissible pTotal totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_source_endpoint_estimates
    htotalSupply_nonneg htotalSupply_lt_one hsource

/--
Theorem 2 amplification from endpoint estimates and active-capacity
small-firm comparison.

Source status: PG24 Theorem 2 proof route through Proposition
`lt-small-firms`; compared with the previous row, this derives the displayed
small-firm capacity bound from the paper's cardinality, regular-capacity, and
active-capacity comparison premises.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_source_endpoint_estimates_active_capacity_statement
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
    theorem2_uniform_amplification_statement
      Admissible pTotal totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_source_endpoint_estimates_active_capacity
    small capacity htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg
    hsource

/--
Theorem 2 amplification from long-tailed noise and source endpoint estimates.

Source status: PG24 Theorem 2 proof route through long-tailedness,
Proposition `lt-large-firms`, Proposition `lt-small-firms`, and the final
`C1/C2` decomposition.  The `lt-approx-F2` product comparison is derived from
the visible cutoff lower bound and high-value crossing bound, not assumed as a
separate endpoint premise.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_longTail_source_endpoint_estimates_statement
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
    theorem2_uniform_amplification_statement
      Admissible pTotal totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_longTail_source_endpoint_estimates
    hlong htotalSupply_nonneg htotalSupply_lt_one hsource

/--
Theorem 2 amplification from survival-function long-tailed noise and source
endpoint estimates.

Source status: PG24 Theorem 2 in the source survival-probability shape.  This
strengthens the long-tail endpoint row by deriving the large-firm value
monotonicity from antitonicity of the survival function.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_survival_longTail_source_endpoint_estimates_statement
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
    theorem2_uniform_amplification_statement
      Admissible pTotal totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_survival_longTail_source_endpoint_estimates
    hlong hsurvival_antitone htotalSupply_nonneg htotalSupply_lt_one hsource

/--
Theorem 2 amplification from concrete upper-tail long-tailed noise and source
endpoint estimates.

Source status: PG24 Theorem 2 in the real-noise-law shape.  Once
`survival x` is instantiated as `Pr[X > x]`, antitonicity and probability
upper bounds are derived by the library rather than listed as source
premises.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_upperTail_longTail_source_endpoint_estimates_statement
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
    theorem2_uniform_amplification_statement
      Admissible pTotal totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_upperTail_longTail_source_endpoint_estimates
    noiseLaw hlong htotalSupply_nonneg htotalSupply_lt_one hsource

/--
Theorem 2 amplification from concrete upper-tail long-tailed noise, deriving
strict probability side conditions internally.

Source status: PG24 Theorem 2 in the real-noise-law shape.  The source
supplies the diverging cutoff floor and endpoint estimates; Lean derives
positive high-tail mass and positive low-endpoint failure probability from
long-tailed upper-tail probabilities.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_upperTail_longTail_source_endpoint_estimates_strict_derived_statement
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
    theorem2_uniform_amplification_statement
      Admissible pTotal totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_upperTail_longTail_source_endpoint_estimates_strict_derived
    noiseLaw hlong htotalSupply_nonneg htotalSupply_lt_one hsource

/--
Theorem 2 amplification for the concrete iid cutoff-affordance model.

Source status: PG24 Theorem 2 in the finite cutoff-market shape.  The total
and small probabilities are concrete iid cutoff-crossing probabilities; the
large-firm product formula, strict long-tail side conditions, small-capacity
bound, and small/large decomposition are derived internally from the visible
source inputs.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_iidProduct_cutoff_source_endpoint_estimates_strict_derived_statement
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
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (large C μ) vLow (cutoff C μ) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability_statement
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
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (small C μ) vStar (cutoff C μ) ≤
                AppliedModelingLib.Matching.activeCapacity (small C μ) (capacity C μ))) :
    theorem2_uniform_amplification_statement Admissible
      (fun C : ℕ => fun μ : Admissible C => fun v : ℝ =>
        cutoffAffordanceProbability_statement
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (total C μ) v (cutoff C μ))
      totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_iidProduct_cutoff_source_endpoint_estimates_strict_derived
    noiseLaw hlong small large total cutoff capacity
    htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg hsource

/--
Theorem 2 amplification for the concrete iid cutoff-affordance model, with the
paper's epsilon-indexed small/large split.

Source status: PG24 Theorem 2 in the finite cutoff-market shape with the
appendix proof's `F_1/F_2` split chosen after epsilon is fixed.  The visible
source endpoint estimates are stated for that epsilon-indexed split; Lean
derives the iid product bridge, weak capacity bound from capacity regularity,
and final decomposition internally.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_iidProduct_cutoff_epsilon_indexed_source_endpoint_estimates_capacityRegular_strict_derived_statement
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
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (large epsilon C μ) vLow (cutoff C μ) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (large epsilon C μ) vHigh (cutoff C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              ((small epsilon C μ).card : ℝ) ≤
                epsilon * ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              definition_capacityRegular_statement (capacity C μ) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (small epsilon C μ) vStar (cutoff C μ) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (small epsilon C μ) (capacity C μ))) :
    theorem2_uniform_amplification_statement Admissible
      (fun C : ℕ => fun μ : Admissible C => fun v : ℝ =>
        cutoffAffordanceProbability_statement
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (total C μ) v (cutoff C μ))
      totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_iidProduct_cutoff_epsilon_indexed_source_endpoint_estimates_capacityRegular_strict_derived
    noiseLaw hlong small large total cutoff capacity
    htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg hsource

/--
Theorem 2 amplification for the concrete iid cutoff-affordance model with the
paper's ordered-index `F_1/F_2` split.

Source status: PG24 Theorem 2 after sorting colleges by cutoff.  The total set
is all colleges, `F_1`/`F_2` are the prefix/suffix induced by a split index, and
Lean derives the split union and `F_1` cardinality clauses.  The remaining
visible source work is the ordered cutoff endpoint/capacity estimates.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_iidProduct_cutoff_index_split_source_endpoint_estimates_capacityRegular_strict_derived_statement
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
              ∀ c ∈ definition_indexSuffixLarge_statement
                  (splitIndex epsilon C) C,
                lowerCutoff C ≤ cutoff C μ c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              ∀ c ∈ definition_indexSuffixLarge_statement
                  (splitIndex epsilon C) C,
                AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoff C μ c - vHigh) ≤
                  sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (splitIndex epsilon C) C)
                    vLow (cutoff C μ) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (splitIndex epsilon C) C)
                  vHigh (cutoff C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              definition_capacityRegular_statement (capacity C μ) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (splitIndex epsilon C) C)
                    vStar (cutoff C μ) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexPrefixSmall_statement
                    (splitIndex epsilon C) C)
                  (capacity C μ))) :
    theorem2_uniform_amplification_statement Admissible
      (fun C : ℕ => fun μ : Admissible C => fun v : ℝ =>
        cutoffAffordanceProbability_statement
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) v (cutoff C μ))
      totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_iidProduct_cutoff_index_split_source_endpoint_estimates_capacityRegular_strict_derived
    noiseLaw hlong splitIndex cutoff capacity
    htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg hsplit_card hsource

/--
Theorem 2 amplification for the concrete iid cutoff-affordance model with the
concrete floor-index `F_1/F_2` split.

Source status: PG24 Theorem 2 after sorting colleges by cutoff, with `F_1`
the first `floor(epsilon*(C+1))` colleges and `F_2` the rest.  Lean derives
the finite split union and cardinality clauses, so the remaining visible source
work is the ordered cutoff endpoint/capacity estimates.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_iidProduct_cutoff_floor_index_split_source_endpoint_estimates_capacityRegular_strict_derived_statement
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
              ∀ c ∈ definition_indexSuffixLarge_statement
                  (definition_epsilonFloorSplitIndex_statement epsilon C) C,
                lowerCutoff C ≤ cutoff C μ c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              ∀ c ∈ definition_indexSuffixLarge_statement
                  (definition_epsilonFloorSplitIndex_statement epsilon C) C,
                AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoff C μ c - vHigh) ≤
                  sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vLow (cutoff C μ) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh (cutoff C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              definition_capacityRegular_statement (capacity C μ) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : Admissible C,
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar (cutoff C μ) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexPrefixSmall_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (capacity C μ))) :
    theorem2_uniform_amplification_statement Admissible
      (fun C : ℕ => fun μ : Admissible C => fun v : ℝ =>
        cutoffAffordanceProbability_statement
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) v (cutoff C μ))
      totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_iidProduct_cutoff_floor_index_split_source_endpoint_estimates_capacityRegular_strict_derived
    noiseLaw hlong cutoff capacity
    htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg hsource

/--
Theorem 2 amplification over stable matchings in the concrete iid
cutoff-affordance model.

Source status: PG24 Theorem 2 is uniform over every stable matching. This row
uses A-L Lemma 1 to choose each stable matching's market-clearing cutoff;
endpoint, capacity, and decomposition estimates are stated for all
market-clearing cutoffs.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_iidProduct_stable_cutoff_source_endpoint_estimates_strict_derived_statement
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
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (large C P) vLow (cutoffOut C P) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability_statement
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
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (small C P) vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity (small C P) (capacity C P))) :
    theorem2_uniform_amplification_statement
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (total C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))
            v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_source_endpoint_estimates_strict_derived
    Mseq Iseq noiseLaw hlong small large total cutoffOut capacity
    htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg hsource

/--
Theorem 2 amplification over stable matchings with capacity regularity as the
source capacity premise.

Source status: PG24 Theorem 2 in the stable-cutoff iid model.  Compared with
the previous row, this states the small-firm capacity input using the paper's
regularity condition `S_c < alpha / C`; the weak per-college bound used in the
capacity squeeze is derived in Lean.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_iidProduct_stable_cutoff_source_endpoint_estimates_capacityRegular_strict_derived_statement
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
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (large C P) vLow (cutoffOut C P) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (large C P) vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ((small C P).card : ℝ) ≤
                epsilon * ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              definition_capacityRegular_statement (capacity C P) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (small C P) vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity (small C P) (capacity C P))) :
    theorem2_uniform_amplification_statement
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (total C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))
            v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_source_endpoint_estimates_capacityRegular_strict_derived
    Mseq Iseq noiseLaw hlong small large total cutoffOut capacity
    htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg hsource

/--
Theorem 2 amplification over stable matchings with the paper's
epsilon-indexed small/large split and capacity regularity.

Source status: PG24 Theorem 2 in the stable-cutoff iid model with `F_1/F_2`
chosen after epsilon is fixed.  A-L Lemma 1 supplies each stable matching's
market-clearing cutoff; the epsilon-indexed endpoint estimates are visible for
all market-clearing cutoffs, and Lean specializes them to stable matchings.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_iidProduct_stable_cutoff_epsilon_indexed_source_endpoint_estimates_capacityRegular_strict_derived_statement
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
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (large epsilon C P) vLow (cutoffOut C P) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (large epsilon C P) vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ((small epsilon C P).card : ℝ) ≤
                epsilon * ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              definition_capacityRegular_statement (capacity C P) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (small epsilon C P) vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (small epsilon C P) (capacity C P))) :
    theorem2_uniform_amplification_statement
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (total C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2))
            v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_epsilon_indexed_source_endpoint_estimates_capacityRegular_strict_derived
    Mseq Iseq noiseLaw hlong small large total cutoffOut capacity
    htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg hsource

/--
Theorem 2 amplification over stable matchings with the paper's ordered-index
`F_1/F_2` split.

Source status: strongest current PG24 Theorem 2 route.  The conclusion is
uniform over stable matchings; A-L Lemma 1 supplies the selected
market-clearing cutoff; the total set is all colleges; and Lean derives the
finite split union and small-block cardinality clauses from the split index.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_iidProduct_stable_cutoff_index_split_source_endpoint_estimates_capacityRegular_strict_derived_statement
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
              ∀ c ∈ definition_indexSuffixLarge_statement
                  (splitIndex epsilon C) C,
                lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c ∈ definition_indexSuffixLarge_statement
                  (splitIndex epsilon C) C,
                AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoffOut C P c - vHigh) ≤
                  sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (splitIndex epsilon C) C)
                    vLow (cutoffOut C P) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (splitIndex epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              definition_capacityRegular_statement (capacity C P) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (splitIndex epsilon C) C)
                    vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexPrefixSmall_statement
                    (splitIndex epsilon C) C)
                  (capacity C P))) :
    theorem2_uniform_amplification_statement
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_index_split_source_endpoint_estimates_capacityRegular_strict_derived
    Mseq Iseq noiseLaw hlong splitIndex cutoffOut capacity
    htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg hsplit_card hsource

/--
Theorem 2 amplification over stable matchings with the concrete floor-index
`F_1/F_2` split.

Source status: cleanest current PG24 Theorem 2 route.  The theorem is uniform
over stable matchings, uses A-L to select each market-clearing cutoff, fixes
the total set to all colleges, and derives the finite floor split and
cardinality facts internally.  The visible source work is the ordered endpoint
and capacity estimates.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_source_endpoint_estimates_capacityRegular_strict_derived_statement
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
              ∀ c ∈ definition_indexSuffixLarge_statement
                  (definition_epsilonFloorSplitIndex_statement epsilon C) C,
                lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c ∈ definition_indexSuffixLarge_statement
                  (definition_epsilonFloorSplitIndex_statement epsilon C) C,
                AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoffOut C P c - vHigh) ≤
                  sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vLow (cutoffOut C P) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              definition_capacityRegular_statement (capacity C P) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexPrefixSmall_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (capacity C P))) :
    theorem2_uniform_amplification_statement
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_source_endpoint_estimates_capacityRegular_strict_derived
    Mseq Iseq noiseLaw hlong cutoffOut capacity
    htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg hsource

/--
Theorem 2 amplification over stable matchings with floor-index split and a
scalar high-tail estimate at the cutoff floor.

Source status: strongest current PG24 Theorem 2 route.  It uses A-L for the
stable-to-cutoff bridge, derives the finite floor split/cardinality facts, and
derives per-large-college high-tail bounds from a scalar tail estimate at the
common lower cutoff using upper-tail monotonicity.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_scalar_tail_source_endpoint_estimates_capacityRegular_strict_derived_statement
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
              ∀ c ∈ definition_indexSuffixLarge_statement
                  (definition_epsilonFloorSplitIndex_statement epsilon C) C,
                lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vLow (cutoffOut C P) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              definition_capacityRegular_statement (capacity C P) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexPrefixSmall_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (capacity C P))) :
    theorem2_uniform_amplification_statement
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_scalar_tail_source_endpoint_estimates_capacityRegular_strict_derived
    Mseq Iseq noiseLaw hlong cutoffOut capacity
    htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg hsource

/--
Theorem 2 amplification over stable matchings with the small-firm step exposed
as matched-mass clauses.

Source status: PG24 Theorem 2 route matching the proof of Proposition
`lt-small-firms`: the source lower-bounds the mass matched to `F_1`, and this
matched mass is bounded by the total capacity of `F_1`.  Lean combines these
with the floor split, scalar-tail large-firm estimate, and capacity regularity.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_scalar_tail_matched_mass_source_endpoint_estimates_capacityRegular_strict_derived_statement
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
              ∀ c ∈ definition_indexSuffixLarge_statement
                  (definition_epsilonFloorSplitIndex_statement epsilon C) C,
                lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vLow (cutoffOut C P) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              definition_capacityRegular_statement (capacity C P) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar (cutoffOut C P) ≤
                smallMatchedMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              smallMatchedMass C P ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexPrefixSmall_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (capacity C P))) :
    theorem2_uniform_amplification_statement
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_scalar_tail_matched_mass_source_endpoint_estimates_capacityRegular_strict_derived
    Mseq Iseq noiseLaw hlong cutoffOut capacity smallMatchedMass
    htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg hsource

/--
Theorem 2 amplification over stable matchings with large-firm interval mass
and small-firm matched-mass source clauses.

Source status: PG24 Theorem 2 route matching the proof structure of both
Propositions `lt-large-firms` and `lt-small-firms`: the low-endpoint
large-firm estimate is obtained from an interval-mass comparison, and the
small-firm estimate is obtained from matched mass bounded by `F_1` capacity.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_scalar_tail_interval_mass_matched_mass_source_endpoint_estimates_capacityRegular_strict_derived_statement
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
              ∀ c ∈ definition_indexSuffixLarge_statement
                  (definition_epsilonFloorSplitIndex_statement epsilon C) C,
                lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vLow (cutoffOut C P) ≤
                largeIntervalMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeIntervalMass C P ≤ totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              definition_capacityRegular_statement (capacity C P) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar (cutoffOut C P) ≤
                smallMatchedMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              smallMatchedMass C P ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexPrefixSmall_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (capacity C P))) :
    theorem2_uniform_amplification_statement
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_scalar_tail_interval_mass_matched_mass_source_endpoint_estimates_capacityRegular_strict_derived
    Mseq Iseq noiseLaw hlong cutoffOut capacity largeIntervalMass
    smallMatchedMass htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg
    hsource

/--
Theorem 2 amplification over stable matchings with large-firm matched-mass
source clauses.

Source status: PG24 Theorem 2 route where the high-endpoint `F_2` lower bound
is exposed as large matched mass after small-capacity loss plus an endpoint
comparison.  Lean combines this with the interval-mass low endpoint,
small-firm matched mass, floor split, scalar-tail, and capacity-regularity
clauses.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_scalar_tail_interval_mass_large_matched_mass_source_endpoint_estimates_capacityRegular_strict_derived_statement
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
              ∀ c ∈ definition_indexSuffixLarge_statement
                  (definition_epsilonFloorSplitIndex_statement epsilon C) C,
                lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
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
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              definition_capacityRegular_statement (capacity C P) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar (cutoffOut C P) ≤
                smallMatchedMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              smallMatchedMass C P ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexPrefixSmall_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (capacity C P))) :
    theorem2_uniform_amplification_statement
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_scalar_tail_interval_mass_large_matched_mass_source_endpoint_estimates_capacityRegular_strict_derived
    Mseq Iseq noiseLaw hlong cutoffOut capacity largeIntervalMass
    largeMatchedMass smallMatchedMass htotalSupply_nonneg
    htotalSupply_lt_one halpha_nonneg hsource

/--
Theorem 2 amplification over stable matchings with the large-block cutoff
floor stated as a sorted-index suffix condition.

Source status: strongest current PG24 Theorem 2 route.  The source gives the
cutoff floor for every sorted index in the suffix `i >= floor(epsilon*(C+1))`;
Lean turns this into the `F_2` set condition and combines it with scalar-tail,
interval-mass, large-matched-mass, small-matched-mass, floor split, and
capacity-regularity clauses.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_source_endpoint_estimates_capacityRegular_strict_derived_statement
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
                definition_epsilonFloorSplitIndex_statement epsilon C ≤
                  (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
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
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              definition_capacityRegular_statement (capacity C P) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar (cutoffOut C P) ≤
                smallMatchedMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              smallMatchedMass C P ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexPrefixSmall_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (capacity C P))) :
    theorem2_uniform_amplification_statement
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_source_endpoint_estimates_capacityRegular_strict_derived
    Mseq Iseq noiseLaw hlong cutoffOut capacity largeIntervalMass
    largeMatchedMass smallMatchedMass htotalSupply_nonneg
    htotalSupply_lt_one halpha_nonneg hsource

/--
Theorem 2 amplification over stable matchings with concrete active-capacity
accounting for the high-endpoint large-firm bound.

Source status: stronger PG24 Theorem 2 route.  Lean derives the large block's
capacity lower bound from total capacity, the `F_1/F_2` split, and capacity
regularity, so the remaining high-endpoint source clause is stated directly
with the active capacity of `F_2` rather than an abstract matched-mass
bookkeeping variable.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_active_capacity_source_endpoint_estimates_capacityRegular_strict_derived_statement
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
                definition_epsilonFloorSplitIndex_statement epsilon C ≤
                  (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
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
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (capacity C P) - epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              definition_capacityRegular_statement (capacity C P) alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexPrefixSmall_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (capacity C P))) :
    theorem2_uniform_amplification_statement
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_active_capacity_source_endpoint_estimates_capacityRegular_strict_derived
    Mseq Iseq noiseLaw hlong cutoffOut capacity htotalSupply_nonneg
    htotalSupply_lt_one halpha_nonneg hsource

/--
Theorem 2 amplification over stable matchings using the market's own capacity
field.

Source status: preferred current PG24 Theorem 2 route.  This is the
active-capacity route specialized so that capacity is the capacity primitive
of the cutoff market, not an auxiliary function supplied beside the model.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_source_endpoint_estimates_capacityRegular_strict_derived_statement
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
                definition_epsilonFloorSplitIndex_statement epsilon C ≤
                  (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
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
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity - epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              definition_capacityRegular_statement (Mseq C).capacity alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexPrefixSmall_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity)) :
    theorem2_uniform_amplification_statement
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_source_endpoint_estimates_capacityRegular_strict_derived
    Mseq Iseq noiseLaw hlong cutoffOut htotalSupply_nonneg
    htotalSupply_lt_one halpha_nonneg hsource

/--
Theorem 2 amplification over stable matchings with market-level capacity
premises.

Source status: preferred current PG24 Theorem 2 route.  Total capacity and
capacity regularity are stated once for the market sequence, then Lean
specializes them to each market-clearing cutoff.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_global_capacity_source_endpoint_estimates_capacityRegular_strict_derived_statement
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
                definition_epsilonFloorSplitIndex_statement epsilon C ≤
                  (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
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
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity - epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
              definition_capacityRegular_statement (Mseq C).capacity alpha (C + 1)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexPrefixSmall_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity)) :
    theorem2_uniform_amplification_statement
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_global_capacity_source_endpoint_estimates_capacityRegular_strict_derived
    Mseq Iseq noiseLaw hlong cutoffOut htotalSupply_nonneg
    htotalSupply_lt_one halpha_nonneg hsource

/--
Theorem 2 amplification over stable matchings with market-level capacity
premises separated from the endpoint package.

Source status: preferred current PG24 Theorem 2 route.  Total capacity and
capacity regularity are value-independent market-sequence assumptions; the
remaining source package contains only cutoff, scalar-tail, and endpoint
probability/capacity comparisons for the chosen value window.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_global_capacity_separate_capacity_source_endpoint_estimates_capacityRegular_strict_derived_statement
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
        definition_capacityRegular_statement (Mseq C).capacity alpha (C + 1))
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
                definition_epsilonFloorSplitIndex_statement epsilon C ≤
                  (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vLow (cutoffOut C P) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Matching.activeCapacity
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity - epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexPrefixSmall_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity)) :
    theorem2_uniform_amplification_statement
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_global_capacity_separate_capacity_source_endpoint_estimates_capacityRegular_strict_derived
    Mseq Iseq noiseLaw hlong cutoffOut htotalSupply_nonneg
    htotalSupply_lt_one halpha_nonneg htotal_capacity hcapacity_regular
    hsource

/--
Theorem 2 amplification over stable matchings with the paper's capacity
primitives stated directly.

Source status: preferred current PG24 Theorem 2 route.  The source assumptions
`sum_c S_c = S` and `S_c < alpha / C` are the only capacity inputs; Lean
derives the internal total-capacity lower bound and capacity-regularity
predicate before applying the endpoint route.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_capacity_source_endpoint_estimates_strict_derived_statement
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
      source_assumption_capacity_upper_bound Mseq alpha)
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
                definition_epsilonFloorSplitIndex_statement epsilon C ≤
                  (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vLow (cutoffOut C P) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Matching.activeCapacity
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity - epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexPrefixSmall_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity)) :
    theorem2_uniform_amplification_statement
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_capacity_source_endpoint_estimates_strict_derived
    Mseq Iseq noiseLaw hlong cutoffOut htotalSupply_nonneg
    htotalSupply_lt_one halpha_nonneg hcapacity_total hcapacity_bound
    hsource

/--
Theorem 2 amplification over stable matchings with positive paper capacity
primitives stated directly.

Source status: preferred current PG24 Theorem 2 route.  The source assumptions
`sum_c S_c = S` and `0 < S_c < alpha / C` are the only capacity inputs; Lean
derives nonnegativity of supply, nonnegativity of `alpha`, and the internal
capacity-regularity predicate before applying the direct endpoint route.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_source_endpoint_estimates_strict_derived_statement
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
      source_assumption_capacity_open_bound Mseq alpha)
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
                definition_epsilonFloorSplitIndex_statement epsilon C ≤
                  (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vLow (cutoffOut C P) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Matching.activeCapacity
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity - epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexPrefixSmall_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity)) :
    theorem2_uniform_amplification_statement
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_source_endpoint_estimates_strict_derived
    Mseq Iseq noiseLaw hlong cutoffOut htotalSupply_lt_one
    hcapacity_total hcapacity_open_bound hsource

/--
Theorem 2 source clauses from the scalar-tail, paper-positive-capacity route.

Source status: cleanest current PG24 Theorem 2 eventual-form route.  The
visible high-tail input is the paper's scalar tail estimate at the lower
cutoff floor; Lean derives the per-large-college high-tail bounds using the
ordered cutoff-floor condition and upper-tail monotonicity.
-/
theorem theorem2_uniform_amplification_source_clauses_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_source_endpoint_estimates_strict_derived_statement
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
      source_assumption_capacity_open_bound Mseq alpha)
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
                definition_epsilonFloorSplitIndex_statement epsilon C ≤
                  (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vLow (cutoffOut C P) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Matching.activeCapacity
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity - epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexPrefixSmall_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity)) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          |cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)) -
            totalSupply| < ε :=
  theorem2_uniformAmplification_source_clauses
    (theorem2_uniform_amplification_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_source_endpoint_estimates_strict_derived_statement
      Mseq Iseq noiseLaw hlong cutoffOut htotalSupply_lt_one
      hcapacity_total hcapacity_open_bound hsource)

/--
Theorem 2 amplification over stable matchings with paper-positive capacities
and scalar endpoint estimates.

Source status: preferred clean PG24 Theorem 2 route.  Total capacity and
positive per-college capacity bounds are stated as paper model primitives;
Lean derives total-supply nonnegativity, alpha nonnegativity, capacity
regularity, split/cardinality facts, and product-noise steps internally.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_market_capacity_paper_positive_capacity_source_endpoint_estimates_strict_derived_statement
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
      source_assumption_capacity_open_bound Mseq alpha)
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
              ∀ c ∈ definition_indexSuffixLarge_statement
                  (definition_epsilonFloorSplitIndex_statement epsilon C) C,
                lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c ∈ definition_indexSuffixLarge_statement
                  (definition_epsilonFloorSplitIndex_statement epsilon C) C,
                AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoffOut C P c - vHigh) ≤
                  sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vLow (cutoffOut C P) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexPrefixSmall_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity)) :
    theorem2_uniform_amplification_statement
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_market_capacity_paper_positive_capacity_source_endpoint_estimates_strict_derived
    Mseq Iseq noiseLaw hlong cutoffOut htotalSupply_lt_one
    hcapacity_total hcapacity_open_bound hsource

/--
Theorem 2 source clauses from the preferred clean stable-matching route.

Source status: PG24 Theorem 2 in its paper-facing eventual form.  The paper's
positive capacity primitives and scalar endpoint estimates imply that, for
every value and epsilon, every stable matching eventually has match
probability within epsilon of total supply.
-/
theorem theorem2_uniform_amplification_source_clauses_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_market_capacity_paper_positive_capacity_source_endpoint_estimates_strict_derived_statement
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
      source_assumption_capacity_open_bound Mseq alpha)
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
              ∀ c ∈ definition_indexSuffixLarge_statement
                  (definition_epsilonFloorSplitIndex_statement epsilon C) C,
                lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ c ∈ definition_indexSuffixLarge_statement
                  (definition_epsilonFloorSplitIndex_statement epsilon C) C,
                AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoffOut C P c - vHigh) ≤
                  sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vLow (cutoffOut C P) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              totalSupply - alpha * epsilon - epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexPrefixSmall_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity)) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          |cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)) -
            totalSupply| < ε :=
  theorem2_uniformAmplification_source_clauses
    (theorem2_uniform_amplification_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_market_capacity_paper_positive_capacity_source_endpoint_estimates_strict_derived_statement
      Mseq Iseq noiseLaw hlong cutoffOut htotalSupply_lt_one
      hcapacity_total hcapacity_open_bound hsource)

/--
Theorem 2 amplification over stable matchings with paper-positive capacities
and interval/active-capacity endpoint estimates.

Source status: strengthened PG24 Theorem 2 route.  The source proof may state
the low-endpoint large-firm step through interval mass, while the high-endpoint
large-firm and small-firm steps are stated directly through active capacity;
Lean derives the total-supply large-firm upper bound from the paper's total
capacity identity and positive capacity primitive.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_bound_interval_active_capacity_source_endpoint_estimates_strict_derived_statement
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
      source_assumption_capacity_open_bound Mseq alpha)
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
                definition_epsilonFloorSplitIndex_statement epsilon C ≤
                  (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vLow (cutoffOut C P) ≤
                largeIntervalMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeIntervalMass C P ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Matching.activeCapacity
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity - epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexPrefixSmall_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity)) :
    theorem2_uniform_amplification_statement
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_bound_interval_active_capacity_source_endpoint_estimates_strict_derived
    Mseq Iseq noiseLaw hlong cutoffOut largeIntervalMass
    htotalSupply_lt_one hcapacity_total hcapacity_open_bound hsource

/--
Theorem 2 source clauses from the interval/active-capacity route.

Source status: PG24 Theorem 2 in expanded paper-facing form.  This route keeps
the paper's interval decomposition visible but removes the auxiliary matched
mass objects from the source package.
-/
theorem theorem2_uniform_amplification_source_clauses_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_bound_interval_active_capacity_source_endpoint_estimates_strict_derived_statement
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
      source_assumption_capacity_open_bound Mseq alpha)
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
                definition_epsilonFloorSplitIndex_statement epsilon C ≤
                  (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vLow (cutoffOut C P) ≤
                largeIntervalMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeIntervalMass C P ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Matching.activeCapacity
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity - epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexPrefixSmall_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity)) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          |cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)) -
            totalSupply| < ε :=
  theorem2_uniformAmplification_source_clauses
    (theorem2_uniform_amplification_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_bound_interval_active_capacity_source_endpoint_estimates_strict_derived_statement
      Mseq Iseq noiseLaw hlong cutoffOut largeIntervalMass
      htotalSupply_lt_one hcapacity_total hcapacity_open_bound hsource)

/--
Theorem 2 amplification over stable matchings with paper capacity primitives
and source-facing endpoint mass comparisons.

Source status: preferred current PG24 Theorem 2 route.  Total capacity and
per-college capacity are stated as in the model section; the low-endpoint
large-firm and small-firm steps are stated through the interval/matched-mass
comparisons used in the amplification proof, and Lean collapses them into the
active-capacity endpoint route.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_capacity_interval_mass_matched_mass_source_endpoint_estimates_strict_derived_statement
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
      source_assumption_capacity_upper_bound Mseq alpha)
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
                definition_epsilonFloorSplitIndex_statement epsilon C ≤
                  (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vLow (cutoffOut C P) ≤
                largeIntervalMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeIntervalMass C P ≤ totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Matching.activeCapacity
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity - epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar (cutoffOut C P) ≤
                smallMatchedMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              smallMatchedMass C P ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexPrefixSmall_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity)) :
    theorem2_uniform_amplification_statement
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_capacity_interval_mass_matched_mass_source_endpoint_estimates_strict_derived
    Mseq Iseq noiseLaw hlong cutoffOut largeIntervalMass smallMatchedMass
    htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg hcapacity_total
    hcapacity_bound hsource

/--
Theorem 2 amplification over stable matchings with the paper's per-college
capacity bound and source-facing interval/matched-mass endpoint comparisons.

Source status: strongest current PG24 Theorem 2 route.  The per-college
capacity assumption `S_c < alpha / C` derives the capacity regularity used in
the small-firm step; the high-endpoint large-firm step is stated through the
large-matched-mass lower bound and endpoint comparison used in the proof.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_capacity_bound_interval_mass_large_matched_mass_source_endpoint_estimates_strict_derived_statement
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
      source_assumption_capacity_upper_bound Mseq alpha)
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
                definition_epsilonFloorSplitIndex_statement epsilon C ≤
                  (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
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
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar (cutoffOut C P) ≤
                smallMatchedMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              smallMatchedMass C P ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexPrefixSmall_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity)) :
    theorem2_uniform_amplification_statement
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_capacity_bound_interval_mass_large_matched_mass_source_endpoint_estimates_strict_derived
    Mseq Iseq noiseLaw hlong cutoffOut largeIntervalMass largeMatchedMass
    smallMatchedMass htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg
    hcapacity_bound hsource

/--
Theorem 2 amplification over stable matchings with the paper's capacity
primitive deriving the large-interval capacity bound.

Source status: strengthened PG24 Theorem 2 route.  The paper-level facts that
total college capacity is `S`, capacities are nonnegative, and the large
interval mass is bounded by the large block's active capacity imply the
earlier `largeIntervalMass <= S` premise in Lean.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_capacity_bound_interval_active_capacity_large_matched_mass_source_endpoint_estimates_strict_derived_statement
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
      source_assumption_capacity_upper_bound Mseq alpha)
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
                definition_epsilonFloorSplitIndex_statement epsilon C ≤
                  (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vLow (cutoffOut C P) ≤
                largeIntervalMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeIntervalMass C P ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              totalSupply - alpha * epsilon ≤ largeMatchedMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeMatchedMass C P - epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar (cutoffOut C P) ≤
                smallMatchedMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              smallMatchedMass C P ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexPrefixSmall_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity)) :
    theorem2_uniform_amplification_statement
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_capacity_bound_interval_active_capacity_large_matched_mass_source_endpoint_estimates_strict_derived
    Mseq Iseq noiseLaw hlong cutoffOut largeIntervalMass largeMatchedMass
    smallMatchedMass htotalSupply_nonneg htotalSupply_lt_one halpha_nonneg
    hcapacity_total hcapacity_nonneg hcapacity_bound hsource

/--
Theorem 2 amplification over stable matchings with the large matched-mass
lower bound derived from large-block capacity filling.

Source status: strengthened PG24 Theorem 2 route.  Instead of taking the
broad lower bound `S - alpha*epsilon <= largeMatchedMass` as a source premise,
Lean derives it from total capacity, per-college capacity bounds, and the
source-facing fact that the large block's active capacity is matched.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_capacity_bound_interval_active_capacity_matched_large_matched_mass_source_endpoint_estimates_strict_derived_statement
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
      source_assumption_capacity_upper_bound Mseq alpha)
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
                definition_epsilonFloorSplitIndex_statement epsilon C ≤
                  (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vLow (cutoffOut C P) ≤
                largeIntervalMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeIntervalMass C P ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Matching.activeCapacity
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity ≤
                largeMatchedMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeMatchedMass C P - epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar (cutoffOut C P) ≤
                smallMatchedMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              smallMatchedMass C P ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexPrefixSmall_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity)) :
    theorem2_uniform_amplification_statement
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_capacity_bound_interval_active_capacity_matched_large_matched_mass_source_endpoint_estimates_strict_derived
    Mseq Iseq noiseLaw hlong cutoffOut largeIntervalMass largeMatchedMass
    smallMatchedMass htotalSupply_lt_one halpha_nonneg hcapacity_total
    hcapacity_nonneg hcapacity_bound hsource

/--
Theorem 2 amplification over stable matchings with paper-positive capacities.

Source status: strengthened PG24 Theorem 2 route.  The paper states capacities
as positive and bounded by `alpha / (C+1)`; Lean derives both capacity
nonnegativity and `0 <= alpha` before applying the active-capacity/matched-mass
endpoint route.
-/
theorem theorem2_uniform_amplification_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_bound_interval_active_capacity_matched_large_matched_mass_source_endpoint_estimates_strict_derived_statement
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
      source_assumption_capacity_open_bound Mseq alpha)
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
                definition_epsilonFloorSplitIndex_statement epsilon C ≤
                  (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vLow (cutoffOut C P) ≤
                largeIntervalMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeIntervalMass C P ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Matching.activeCapacity
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity ≤
                largeMatchedMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeMatchedMass C P - epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar (cutoffOut C P) ≤
                smallMatchedMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              smallMatchedMass C P ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexPrefixSmall_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity)) :
    theorem2_uniform_amplification_statement
      (fun C : ℕ => { μ : (Mseq C).Matching // (Mseq C).Stable μ })
      (fun C : ℕ =>
        fun μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ } =>
        fun v : ℝ =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)))
      totalSupply :=
  theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_bound_interval_active_capacity_matched_large_matched_mass_source_endpoint_estimates_strict_derived
    Mseq Iseq noiseLaw hlong cutoffOut largeIntervalMass largeMatchedMass
    smallMatchedMass htotalSupply_lt_one hcapacity_total hcapacity_open_bound
    hsource

/--
Theorem 2 source clauses from the strongest active-capacity/matched-mass route.

Source status: PG24 Theorem 2 in expanded paper-facing form.  This uses the
positive capacity primitive, total capacity, active-capacity filling of the
large block, large/small matched-mass comparisons, and scalar endpoint
estimates to prove the final uniform absolute-error clause for every stable
matching.
-/
theorem theorem2_uniform_amplification_source_clauses_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_bound_interval_active_capacity_matched_large_matched_mass_source_endpoint_estimates_strict_derived_statement
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
      source_assumption_capacity_open_bound Mseq alpha)
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
                definition_epsilonFloorSplitIndex_statement epsilon C ≤
                  (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vLow (cutoffOut C P) ≤
                largeIntervalMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeIntervalMass C P ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Matching.activeCapacity
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity ≤
                largeMatchedMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeMatchedMass C P - epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar (cutoffOut C P) ≤
                smallMatchedMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              smallMatchedMass C P ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexPrefixSmall_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity)) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          |cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)) -
            totalSupply| < ε :=
  theorem2_uniformAmplification_source_clauses
    (theorem2_uniform_amplification_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_bound_interval_active_capacity_matched_large_matched_mass_source_endpoint_estimates_strict_derived_statement
      Mseq Iseq noiseLaw hlong cutoffOut largeIntervalMass largeMatchedMass
      smallMatchedMass htotalSupply_lt_one hcapacity_total
      hcapacity_open_bound hsource)

/--
Theorem 2 source clauses from the visible mass-clearing-field route.

Source status: preferred audit-facing PG24 Theorem 2 row.  This is the same
semantic boundary as the mass-clearing interface row, but the three
market-clearing capacity-fill laws are visible as separate hypotheses rather
than hidden as record fields.  The remaining inputs are the paper's
positive-capacity condition, total capacity, long-tail noise, and endpoint
estimates.
-/
theorem theorem2_uniform_amplification_source_clauses_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_massClearing_fields_endpoint_estimates_strict_derived_statement
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
                (definition_indexSuffixLarge_statement
                  (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                (Mseq C).capacity ≤
              largeMatchedMass C P)
    (hsmallMatchedMass_le_activeCapacity :
      ∀ epsilon, 0 < epsilon →
        ∀ᶠ C : ℕ in atTop,
          ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
            smallMatchedMass C P ≤
              AppliedModelingLib.Matching.activeCapacity
                (definition_indexPrefixSmall_statement
                  (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                (Mseq C).capacity)
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_total :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity =
          totalSupply)
    (hcapacity_open_bound :
      source_assumption_capacity_open_bound Mseq alpha)
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
                definition_epsilonFloorSplitIndex_statement epsilon C ≤
                  (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vLow (cutoffOut C P) ≤
                largeIntervalMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeMatchedMass C P - epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar (cutoffOut C P) ≤
                smallMatchedMass C P)) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          |cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)) -
            totalSupply| < ε :=
  theorem2_uniformAmplification_source_clauses
    (theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_massClearing_fields_endpoint_estimates_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut largeIntervalMass largeMatchedMass
      smallMatchedMass hlargeIntervalMass_le_totalActiveCapacity
      hlargeActiveCapacity_le_matchedMass hsmallMatchedMass_le_activeCapacity
      htotalSupply_lt_one hcapacity_total hcapacity_open_bound hsource)

/--
Theorem 2 source clauses from paper block-mass identities.

Source status: strengthened PG24 Theorem 2 route.  The previous field route
exposed the three mass-capacity inequalities directly.  This row derives them
from source-level block semantics: total matched mass equals total capacity,
matched mass in a college block equals that block's capacity, large interval
mass is bounded by total matched mass, and the small interval mass is bounded
by the small-block matched mass.
-/
theorem theorem2_uniform_amplification_source_clauses_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_source_block_mass_endpoint_estimates_strict_derived_statement
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
                (definition_indexSuffixLarge_statement
                  (definition_epsilonFloorSplitIndex_statement epsilon C) C))
    (hlargeBlockMatchedMass_eq_activeCapacity :
      ∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ C : ℕ in atTop,
          ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
            matchedMass C P
                (definition_indexSuffixLarge_statement
                  (definition_epsilonFloorSplitIndex_statement epsilon C) C) =
              AppliedModelingLib.Matching.activeCapacity
                (definition_indexSuffixLarge_statement
                  (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                (Mseq C).capacity)
    (hsmallMatchedMass_le_smallBlockMatchedMass :
      ∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ C : ℕ in atTop,
          ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
            smallMatchedMass C P ≤
              matchedMass C P
                (definition_indexPrefixSmall_statement
                  (definition_epsilonFloorSplitIndex_statement epsilon C) C))
    (hsmallBlockMatchedMass_eq_activeCapacity :
      ∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ C : ℕ in atTop,
          ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
            matchedMass C P
                (definition_indexPrefixSmall_statement
                  (definition_epsilonFloorSplitIndex_statement epsilon C) C) =
              AppliedModelingLib.Matching.activeCapacity
                (definition_indexPrefixSmall_statement
                  (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                (Mseq C).capacity)
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_total :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity =
          totalSupply)
    (hcapacity_open_bound :
      source_assumption_capacity_open_bound Mseq alpha)
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
                definition_epsilonFloorSplitIndex_statement epsilon C ≤
                  (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vLow (cutoffOut C P) ≤
                largeIntervalMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeMatchedMass C P - epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar (cutoffOut C P) ≤
                smallMatchedMass C P)) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          |cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)) -
            totalSupply| < ε :=
  theorem2_uniformAmplification_source_clauses
    (theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_source_block_mass_endpoint_estimates_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut largeIntervalMass largeMatchedMass
      smallMatchedMass matchedMass hlargeIntervalMass_le_totalMatchedMass
      htotalMatchedMass_eq_totalActiveCapacity
      hlargeMatchedMass_eq_largeBlockMatchedMass
      hlargeBlockMatchedMass_eq_activeCapacity
      hsmallMatchedMass_le_smallBlockMatchedMass
      hsmallBlockMatchedMass_eq_activeCapacity htotalSupply_lt_one
      hcapacity_total hcapacity_open_bound hsource)

/--
Theorem 2 source clauses from aggregate-demand market-clearing semantics.

Source status: strengthened PG24 Theorem 2 route.  The block-capacity
equalities are derived in Lean from two paper-level semantic facts: matched
mass in any college block is the sum of aggregate demand in that block, and
the source model's exact-fill interface identifies aggregate demand with
capacity at market-clearing cutoffs.
-/
theorem theorem2_uniform_amplification_source_clauses_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_aggregateDemand_block_mass_endpoint_estimates_strict_derived_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (Kseq : ∀ C : ℕ, MarketClearingCapacityInterface (Mseq C))
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
                (definition_indexSuffixLarge_statement
                  (definition_epsilonFloorSplitIndex_statement epsilon C) C))
    (hsmallMatchedMass_le_smallBlockMatchedMass :
      ∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ C : ℕ in atTop,
          ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
            smallMatchedMass C P ≤
              matchedMass C P
                (definition_indexPrefixSmall_statement
                  (definition_epsilonFloorSplitIndex_statement epsilon C) C))
    (hmatchedMass_eq_aggregateDemand :
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          ∀ active : Finset (Fin (C + 1)),
            matchedMass C P active =
              ∑ c ∈ active, (Mseq C).aggregateDemand P c)
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_total :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity =
          totalSupply)
    (hcapacity_open_bound :
      source_assumption_capacity_open_bound Mseq alpha)
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
                definition_epsilonFloorSplitIndex_statement epsilon C ≤
                  (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vLow (cutoffOut C P) ≤
                largeIntervalMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeMatchedMass C P - epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar (cutoffOut C P) ≤
                smallMatchedMass C P)) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          |cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)) -
            totalSupply| < ε :=
  theorem2_uniformAmplification_source_clauses
    (theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_aggregateDemand_block_mass_endpoint_estimates_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut largeIntervalMass largeMatchedMass
      smallMatchedMass matchedMass hlargeIntervalMass_le_totalMatchedMass
      hlargeMatchedMass_eq_largeBlockMatchedMass
      hsmallMatchedMass_le_smallBlockMatchedMass
      hmatchedMass_eq_aggregateDemand
      (Filter.Eventually.of_forall (fun C => by
        intro P hP c
        exact
          AL16SupplyDemandMatching.marketClearingCutoff_aggregateDemand_eq_capacity
            (Mseq C) (Kseq C) hP c))
      htotalSupply_lt_one
      hcapacity_total hcapacity_open_bound hsource)

/--
Theorem 2 source clauses from local interval/matched-mass semantics.

Source status: preferred PG24 Theorem 2 route.  The interval and small-firm
matched-mass quantities are chosen inside the source endpoint package after
the value window is fixed, while Lean derives the block-capacity comparisons
from aggregate-demand and exact-fill market-clearing semantics.
-/
theorem theorem2_uniform_amplification_source_clauses_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_local_aggregateDemand_mass_endpoint_estimates_strict_derived_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (Kseq : ∀ C : ℕ, MarketClearingCapacityInterface (Mseq C))
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
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_total :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity =
          totalSupply)
    (hcapacity_open_bound :
      source_assumption_capacity_open_bound Mseq alpha)
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
                definition_epsilonFloorSplitIndex_statement epsilon C ≤
                  (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vLow (cutoffOut C P) ≤
                largeIntervalMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              largeIntervalMass C P ≤
                matchedMass C P (Finset.univ : Finset (Fin (C + 1)))) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              matchedMass C P
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C) -
                  epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar (cutoffOut C P) ≤
                smallMatchedIntervalMass C P) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              smallMatchedIntervalMass C P ≤
                matchedMass C P
                  (definition_indexPrefixSmall_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C))) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          |cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)) -
            totalSupply| < ε :=
  theorem2_uniformAmplification_source_clauses
    (theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_local_aggregateDemand_mass_endpoint_estimates_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut matchedMass
      hmatchedMass_eq_aggregateDemand
      (Filter.Eventually.of_forall (fun C => by
        intro P hP c
        exact
          AL16SupplyDemandMatching.marketClearingCutoff_aggregateDemand_eq_capacity
            (Mseq C) (Kseq C) hP c))
      htotalSupply_lt_one
      hcapacity_total hcapacity_open_bound hsource)

/--
Theorem 2 source clauses from local event-mass semantics.

Source status: strongest current PG24 Theorem 2 route.  The source endpoint
package gives local event predicates for the chosen value window; Lean turns
event-to-chosen-college implications into mass comparisons, then derives the
capacity laws from aggregate-demand and exact-fill market-clearing semantics.
-/
theorem theorem2_uniform_amplification_source_clauses_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_local_eventMass_aggregateDemand_endpoint_estimates_strict_derived_statement
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
    (hfinite : ∀ C P, IsFiniteMeasure (outcomeLaw C P))
    (hchosen_singleton_measurable :
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          ∀ c : Fin (C + 1),
            MeasurableSet
              {ω : OutcomeSeq C | chosenCollege C P ω = some c})
    (hsingleton_choiceMass_eq_aggregateDemand :
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          ∀ c : Fin (C + 1),
            AppliedModelingLib.Matching.eventMass
                (outcomeLaw C P)
                (fun ω : OutcomeSeq C => chosenCollege C P ω = some c) =
              (Mseq C).aggregateDemand P c)
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_total :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity =
          totalSupply)
    (hcapacity_open_bound :
      source_assumption_capacity_open_bound Mseq alpha)
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
                definition_epsilonFloorSplitIndex_statement epsilon C ≤
                  (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
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
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C) -
                  epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.eventMass
                  (outcomeLaw C P) (smallMatchedIntervalEvent C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ ω : OutcomeSeq C,
                smallMatchedIntervalEvent C P ω →
                  AppliedModelingLib.Matching.chosenInActive
                    (chosenCollege C P)
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    ω)) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          |cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)) -
            totalSupply| < ε :=
  theorem2_uniformAmplification_source_clauses
    (theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_local_eventMass_aggregateDemand_endpoint_estimates_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut OutcomeSeq outcomeLaw chosenCollege
      hfinite
      (by
        filter_upwards
          [hchosen_singleton_measurable,
            hsingleton_choiceMass_eq_aggregateDemand] with
          C hmeasC hsingleC P hP active
        haveI : IsFiniteMeasure (outcomeLaw C P) := hfinite C P
        exact
          AppliedModelingLib.Matching.choiceMass_eq_sum_aggregateDemand_of_singleton_eventMass_eq
            (outcomeLaw C P) (chosenCollege C P) active
            (by
              intro c _hc
              exact hmeasC P hP c)
            (by
              intro c _hc
              exact hsingleC P hP c))
      (Filter.Eventually.of_forall (fun C => by
        intro P hP c
        exact
          AL16SupplyDemandMatching.marketClearingCutoff_aggregateDemand_eq_capacity
            (Mseq C) (Kseq C) hP c))
      htotalSupply_lt_one
      hcapacity_total hcapacity_open_bound hsource)

/--
Theorem 2 source clauses from probability-law local event semantics.

Source status: preferred PG24 Theorem 2 route.  The source endpoint package
uses local event predicates over outcome laws, and the outcome laws are stated
as probability measures; Lean derives the finite-measure facts needed for
event-to-choice mass comparisons and uses the source model's exact-fill
interface for market-clearing capacity equality.
-/
theorem theorem2_uniform_amplification_source_clauses_from_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_local_probabilityEvent_aggregateDemand_endpoint_estimates_strict_derived_statement
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
    (houtcome_prob : ∀ C P, IsProbabilityMeasure (outcomeLaw C P))
    (hchosen_singleton_measurable :
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          ∀ c : Fin (C + 1),
            MeasurableSet
              {ω : OutcomeSeq C | chosenCollege C P ω = some c})
    (hsingleton_choiceMass_eq_aggregateDemand :
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          ∀ c : Fin (C + 1),
            AppliedModelingLib.Matching.eventMass
                (outcomeLaw C P)
                (fun ω : OutcomeSeq C => chosenCollege C P ω = some c) =
              (Mseq C).aggregateDemand P c)
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_total :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity =
          totalSupply)
    (hcapacity_open_bound :
      source_assumption_capacity_open_bound Mseq alpha)
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
                definition_epsilonFloorSplitIndex_statement epsilon C ≤
                  (c : ℕ) →
                  lowerCutoff C ≤ cutoffOut C P c) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (lowerCutoff C - vHigh) ≤
                sigma / ((C + 1 : ℕ) : ℝ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              (1 - epsilon) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
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
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C) -
                  epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh (cutoffOut C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar (cutoffOut C P) ≤
                AppliedModelingLib.Matching.eventMass
                  (outcomeLaw C P) (smallMatchedIntervalEvent C P)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
              ∀ ω : OutcomeSeq C,
                smallMatchedIntervalEvent C P ω →
                  AppliedModelingLib.Matching.chosenInActive
                    (chosenCollege C P)
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    ω)) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          |cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2)) -
            totalSupply| < ε :=
  theorem2_uniformAmplification_source_clauses
    (theorem2_uniformAmplification_of_fixed_alpha_iidProduct_stable_cutoff_floor_index_split_sorted_suffix_market_capacity_paper_positive_capacity_local_probabilityEvent_aggregateDemand_endpoint_estimates_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut OutcomeSeq outcomeLaw chosenCollege
      houtcome_prob
      (by
        filter_upwards
          [hchosen_singleton_measurable,
            hsingleton_choiceMass_eq_aggregateDemand] with
          C hmeasC hsingleC P hP active
        haveI : IsProbabilityMeasure (outcomeLaw C P) := houtcome_prob C P
        haveI : IsFiniteMeasure (outcomeLaw C P) := by infer_instance
        exact
          AppliedModelingLib.Matching.choiceMass_eq_sum_aggregateDemand_of_singleton_eventMass_eq
            (outcomeLaw C P) (chosenCollege C P) active
            (by
              intro c _hc
              exact hmeasC P hP c)
            (by
              intro c _hc
              exact hsingleC P hP c))
      (Filter.Eventually.of_forall (fun C => by
        intro P hP c
        exact
          AL16SupplyDemandMatching.marketClearingCutoff_aggregateDemand_eq_capacity
            (Mseq C) (Kseq C) hP c))
      htotalSupply_lt_one
      hcapacity_total hcapacity_open_bound hsource)

/--
Theorem 2 source clauses from the selected-stable local event route.

Source status: preferred narrowing of the Theorem 2 event route.  The local
event laws are only required at the A-L selected cutoff associated with each
stable matching, not at every abstract market-clearing cutoff.  Lean derives
active-block choice mass from measurable singleton choice events and
per-college aggregate demand, and uses the source-model exact-fill interface
for market-clearing capacity equality.  The high-tail estimate is stated at a
common cutoff floor, and Lean derives the per-college tail bounds by monotonicity.
-/
theorem theorem2_uniform_amplification_source_clauses_from_fixed_alpha_iidProduct_selected_stable_cutoff_floor_index_split_local_probabilityEvent_aggregateDemand_endpoint_estimates_strict_derived_statement
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
      source_assumption_capacity_open_bound Mseq alpha)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          ∃ largeIntervalEvent largeEndpointEvent smallMatchedIntervalEvent :
              ∀ C : ℕ,
                { μ : (Mseq C).Matching // (Mseq C).Stable μ } →
                  OutcomeSeq C → Prop,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              ∀ c ∈ definition_indexSuffixLarge_statement
                  (definition_epsilonFloorSplitIndex_statement epsilon C) C,
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
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
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
              ∀ ω : OutcomeSeq C,
                AppliedModelingLib.Matching.chosenInActive
                    (chosenCollege C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    ω →
                  largeEndpointEvent C μ ω) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              AppliedModelingLib.Matching.eventMass
                  (outcomeLaw C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))
                  (largeEndpointEvent C μ) ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
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
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    ω)) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          |cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2)) -
            totalSupply| < ε := by
  refine
    theorem2_uniformAmplification_source_clauses_of_fixed_alpha_iidProduct_selected_stable_cutoff_floor_index_split_scalar_tail_local_probabilityEvent_aggregateDemand_endpoint_estimates_strict_derived
      Mseq Iseq Kseq noiseLaw hlong cutoffOut
      OutcomeSeq outcomeLaw chosenCollege
      houtcome_prob hchosen_singleton_measurable
      hsingleton_choiceMass_eq_aggregateDemand
      htotalSupply_lt_one hcapacity_total hcapacity_open_bound ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, largeIntervalEvent,
      largeEndpointEvent, smallMatchedIntervalEvent, hvLow, hvHigh,
      hvStar, hvStrict, hlower_atTop, hcutoff_lower, htail_floor,
      hlarge_interval_lower, hlarge_event_chosen,
      hlarge_endpoint_event_chosen, hlarge_endpoint_event_bound,
      hsmall_interval_lower, hsmall_event_chosen⟩
  have hlarge_endpoint_choice :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          AppliedModelingLib.Matching.choiceMass
              (outcomeLaw C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2))
              (chosenCollege C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2))
              (definition_indexSuffixLarge_statement
                (definition_epsilonFloorSplitIndex_statement epsilon C) C) -
              epsilon ≤
            cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (definition_indexSuffixLarge_statement
                (definition_epsilonFloorSplitIndex_statement epsilon C) C)
              vHigh
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2)) := by
    filter_upwards
      [hlarge_endpoint_event_chosen, hlarge_endpoint_event_bound] with
      C hchosenC hboundC μ
    let P :=
      (Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2
    haveI : IsProbabilityMeasure (outcomeLaw C P) :=
      houtcome_prob C μ
    haveI : IsFiniteMeasure (outcomeLaw C P) := by infer_instance
    exact
      theorem2_largeFirm_highEndpoint_choiceMass_bound_of_event_imp
        (outcomeLaw C P)
        (chosenCollege C P)
        (definition_indexSuffixLarge_statement
          (definition_epsilonFloorSplitIndex_statement epsilon C) C)
        (event := largeEndpointEvent C μ)
        (le_of_lt hepsilon)
        (hchosenC μ)
        (hboundC μ)
  exact
    ⟨vLow, vHigh, vStar, lowerCutoff, largeIntervalEvent,
      smallMatchedIntervalEvent, hvLow, hvHigh, hvStar, hvStrict,
      hlower_atTop, hcutoff_lower, htail_floor, hlarge_interval_lower,
      hlarge_event_chosen, hlarge_endpoint_choice, hsmall_interval_lower,
      hsmall_event_chosen⟩

/--
Theorem 2 source clauses from the selected-stable local event route with the
paper's total-capacity equality stated as a finite sum.

Source status: preferred PG24 Theorem 2 row after capacity cleanup.  The paper
states total supply as `sum_c S_c = S`; Lean unfolds `activeCapacity` to obtain
the capacity premise used by the selected-stable event route.
-/
theorem theorem2_uniform_amplification_source_clauses_from_fixed_alpha_iidProduct_selected_stable_cutoff_floor_index_split_local_probabilityEvent_aggregateDemand_endpoint_estimates_paper_capacity_strict_derived_statement
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
    (hcapacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (hcapacity_open_bound :
      source_assumption_capacity_open_bound Mseq alpha)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          ∃ largeIntervalEvent largeEndpointEvent smallMatchedIntervalEvent :
              ∀ C : ℕ,
                { μ : (Mseq C).Matching // (Mseq C).Stable μ } →
                  OutcomeSeq C → Prop,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              ∀ c ∈ definition_indexSuffixLarge_statement
                  (definition_epsilonFloorSplitIndex_statement epsilon C) C,
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
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
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
              ∀ ω : OutcomeSeq C,
                AppliedModelingLib.Matching.chosenInActive
                    (chosenCollege C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    ω →
                  largeEndpointEvent C μ ω) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              AppliedModelingLib.Matching.eventMass
                  (outcomeLaw C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))
                  (largeEndpointEvent C μ) ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
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
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    ω)) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          |cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2)) -
            totalSupply| < ε := by
  have hcapacity_total :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity =
          totalSupply := by
    filter_upwards [hcapacity_sum] with C hC
    simpa using hC
  exact
    theorem2_uniform_amplification_source_clauses_from_fixed_alpha_iidProduct_selected_stable_cutoff_floor_index_split_local_probabilityEvent_aggregateDemand_endpoint_estimates_strict_derived_statement
      Mseq Iseq Kseq noiseLaw hlong cutoffOut
      OutcomeSeq outcomeLaw chosenCollege
      houtcome_prob hchosen_singleton_measurable
      hsingleton_choiceMass_eq_aggregateDemand
      htotalSupply_lt_one hcapacity_total hcapacity_open_bound hsource

/--
Theorem 2 source clauses from the selected-stable local event route with the
small-firm interval integral exposed.

Source status: strengthened preferred PG24 Theorem 2 row.  The small-firm
appendix step is no longer a pre-combined event-mass inequality: the source
package supplies the value interval, its `η`-mass, the displayed integral,
and the integral-to-small-matched-event comparison; Lean derives the lower
bound used by the amplification proof.
-/
theorem theorem2_uniform_amplification_source_clauses_from_fixed_alpha_iidProduct_selected_stable_cutoff_floor_index_split_local_probabilityEvent_aggregateDemand_small_interval_integral_endpoint_estimates_paper_capacity_strict_derived_statement
    {StudentSeq : ℕ → Type u}
    (η : Measure ℝ) [IsProbabilityMeasure η]
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
    (hcapacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (hcapacity_open_bound :
      source_assumption_capacity_open_bound Mseq alpha)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          ∃ largeIntervalEvent largeEndpointEvent smallMatchedIntervalEvent :
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
              ∀ c ∈ definition_indexSuffixLarge_statement
                  (definition_epsilonFloorSplitIndex_statement epsilon C) C,
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
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
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
              ∀ ω : OutcomeSeq C,
                AppliedModelingLib.Matching.chosenInActive
                    (chosenCollege C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    ω →
                  largeEndpointEvent C μ ω) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              AppliedModelingLib.Matching.eventMass
                  (outcomeLaw C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))
                  (largeEndpointEvent C μ) ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
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
                    cutoffAffordanceProbability_statement
                      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                      (definition_indexPrefixSmall_statement
                        (definition_epsilonFloorSplitIndex_statement epsilon C) C)
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
                    cutoffAffordanceProbability_statement
                      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                      (definition_indexPrefixSmall_statement
                        (definition_epsilonFloorSplitIndex_statement epsilon C) C)
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
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    ω)) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          |cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2)) -
            totalSupply| < ε := by
  refine
    theorem2_uniform_amplification_source_clauses_from_fixed_alpha_iidProduct_selected_stable_cutoff_floor_index_split_local_probabilityEvent_aggregateDemand_endpoint_estimates_paper_capacity_strict_derived_statement
      Mseq Iseq Kseq noiseLaw hlong cutoffOut
      OutcomeSeq outcomeLaw chosenCollege
      houtcome_prob hchosen_singleton_measurable
      hsingleton_choiceMass_eq_aggregateDemand
      htotalSupply_lt_one hcapacity_sum hcapacity_open_bound ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, largeIntervalEvent,
      largeEndpointEvent, smallMatchedIntervalEvent, smallInterval,
      hvLow, hvHigh, hvStar, hvStrict, hlower_atTop, hcutoff_lower,
      htail_floor, hlarge_interval_lower, hlarge_event_chosen,
      hlarge_endpoint_event_chosen, hlarge_endpoint_event_bound,
      hsmall_meas, hsmall_int, hsmall_mass, hsmall_ge,
      hsmall_integral_event, hsmall_event_chosen⟩
  have hlarge_endpoint_choice :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          AppliedModelingLib.Matching.choiceMass
              (outcomeLaw C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2))
              (chosenCollege C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2))
              (definition_indexSuffixLarge_statement
                (definition_epsilonFloorSplitIndex_statement epsilon C) C) -
              epsilon ≤
            cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (definition_indexSuffixLarge_statement
                (definition_epsilonFloorSplitIndex_statement epsilon C) C)
              vHigh
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2)) := by
    filter_upwards
      [hlarge_endpoint_event_chosen, hlarge_endpoint_event_bound] with
      C hchosenC hboundC μ
    let P :=
      (Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2
    haveI : IsProbabilityMeasure (outcomeLaw C P) :=
      houtcome_prob C μ
    haveI : IsFiniteMeasure (outcomeLaw C P) := by infer_instance
    exact
      theorem2_largeFirm_highEndpoint_choiceMass_bound_of_event_imp
        (outcomeLaw C P)
        (chosenCollege C P)
        (definition_indexSuffixLarge_statement
          (definition_epsilonFloorSplitIndex_statement epsilon C) C)
        (event := largeEndpointEvent C μ)
        (le_of_lt hepsilon)
        (hchosenC μ)
        (hboundC μ)
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff, largeIntervalEvent,
      largeEndpointEvent, smallMatchedIntervalEvent, hvLow, hvHigh, hvStar,
      hvStrict,
      hlower_atTop, hcutoff_lower, htail_floor, hlarge_interval_lower,
      hlarge_event_chosen, hlarge_endpoint_event_chosen,
      hlarge_endpoint_event_bound, ?_, hsmall_event_chosen⟩
  filter_upwards
    [hsmall_meas, hsmall_int, hsmall_mass, hsmall_ge,
      hsmall_integral_event] with
    C hmeasC hintC hmassC hgeC hintegralC μ
  let P :=
    (Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2
  have hpSmall_mono :
      Monotone (fun w : ℝ =>
        cutoffAffordanceProbability_statement
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (definition_indexPrefixSmall_statement
            (definition_epsilonFloorSplitIndex_statement epsilon C) C)
          w (cutoffOut C P)) := by
    intro x y hxy
    exact
      cutoffAffordanceProbability_mono_value
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (active := definition_indexPrefixSmall_statement
          (definition_epsilonFloorSplitIndex_statement epsilon C) C)
        (cutoff := cutoffOut C P) hxy
  have hpStar_nonneg :
      0 ≤
        cutoffAffordanceProbability_statement
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (definition_indexPrefixSmall_statement
            (definition_epsilonFloorSplitIndex_statement epsilon C) C)
          vStar (cutoffOut C P) :=
    cutoffAffordanceProbability_nonneg
      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
      (definition_indexPrefixSmall_statement
        (definition_epsilonFloorSplitIndex_statement epsilon C) C)
      vStar (cutoffOut C P)
  have hnonneg_compl :
      ∀ w : ℝ, w ∉ smallInterval C μ →
        0 ≤
          (1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma)))) *
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (definition_indexPrefixSmall_statement
              (definition_epsilonFloorSplitIndex_statement epsilon C) C)
            w (cutoffOut C P) := by
    intro w _hw
    exact
      mul_nonneg (le_of_lt hden)
        (cutoffAffordanceProbability_nonneg
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (definition_indexPrefixSmall_statement
            (definition_epsilonFloorSplitIndex_statement epsilon C) C)
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
        cutoffAffordanceProbability_statement
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (definition_indexPrefixSmall_statement
            (definition_epsilonFloorSplitIndex_statement epsilon C) C)
          w (cutoffOut C P))
      (vStar := vStar)
      (hmeasC μ) (hintC μ) (hmassC μ) (le_of_lt hden)
      hpStar_nonneg hpSmall_mono (hgeC μ) hnonneg_compl
      (hintegralC μ)

/--
Theorem 2 source clauses with both large- and small-firm interval integrals
exposed.

Source status: stronger PG24 Theorem 2 row.  The two appendix interval
steps are visible separately: the large-block low-endpoint bound comes from
a large value interval and the small-firm bound comes from the `vStar`
interval.  Lean converts both interval-integral clauses into the event-mass
bounds used by the amplification proof.  The high-endpoint large-block clause
is exposed as the source semantic implication from choosing in the large block
to the high-endpoint affordability event, plus that event's probability bound.
-/
theorem theorem2_uniform_amplification_source_clauses_from_fixed_alpha_iidProduct_selected_stable_cutoff_floor_index_split_local_probabilityEvent_aggregateDemand_large_small_interval_integral_endpoint_estimates_paper_capacity_strict_derived_statement
    {StudentSeq : ℕ → Type u}
    (η : Measure ℝ) [IsProbabilityMeasure η]
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
    (hcapacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (hcapacity_open_bound :
      source_assumption_capacity_open_bound Mseq alpha)
    (hsource :
      ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
        0 <
          1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
          ∃ largeIntervalEvent largeEndpointEvent smallMatchedIntervalEvent :
              ∀ C : ℕ,
                { μ : (Mseq C).Matching // (Mseq C).Stable μ } →
                  OutcomeSeq C → Prop,
          ∃ largeInterval smallInterval :
              ∀ C : ℕ,
                { μ : (Mseq C).Matching // (Mseq C).Stable μ } →
                  Set ℝ,
          vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              ∀ c ∈ definition_indexSuffixLarge_statement
                  (definition_epsilonFloorSplitIndex_statement epsilon C) C,
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
              MeasurableSet (largeInterval C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              1 - epsilon ≤ η.real (largeInterval C μ)) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              ∀ w : ℝ, w ∈ largeInterval C μ → vLow ≤ w) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              (∫ w : ℝ,
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    w
                    (cutoffOut C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2)) ∂η) ≤
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
              ∀ ω : OutcomeSeq C,
                AppliedModelingLib.Matching.chosenInActive
                    (chosenCollege C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    ω →
                  largeEndpointEvent C μ ω) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              AppliedModelingLib.Matching.eventMass
                  (outcomeLaw C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))
                  (largeEndpointEvent C μ) ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              MeasurableSet (smallInterval C μ)) ∧
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
                    cutoffAffordanceProbability_statement
                      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                      (definition_indexPrefixSmall_statement
                        (definition_epsilonFloorSplitIndex_statement epsilon C) C)
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
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    ω)) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          |cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2)) -
            totalSupply| < ε := by
  refine
    theorem2_uniform_amplification_source_clauses_from_fixed_alpha_iidProduct_selected_stable_cutoff_floor_index_split_local_probabilityEvent_aggregateDemand_small_interval_integral_endpoint_estimates_paper_capacity_strict_derived_statement
      η Mseq Iseq Kseq noiseLaw hlong cutoffOut
      OutcomeSeq outcomeLaw chosenCollege
      houtcome_prob hchosen_singleton_measurable
      hsingleton_choiceMass_eq_aggregateDemand
      htotalSupply_lt_one hcapacity_sum hcapacity_open_bound ?_
  intro v epsilon sigma hepsilon hsigma hden
  rcases hsource v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, largeIntervalEvent,
      largeEndpointEvent, smallMatchedIntervalEvent, largeInterval, smallInterval,
      hvLow, hvHigh, hvStar, hvStrict, hlower_atTop, hcutoff_lower,
      htail_floor, hlarge_meas, hlarge_mass, hlarge_ge,
      hlarge_integral_event, hlarge_event_chosen,
      hlarge_endpoint_event_chosen, hlarge_endpoint_event_bound,
      hsmall_meas, hsmall_mass, hsmall_ge, hsmall_integral_event,
      hsmall_event_chosen⟩
  have hlarge_int :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          Integrable
            (fun w : ℝ =>
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (definition_indexSuffixLarge_statement
                  (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                w
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := μ.1) μ.2))) η := by
    exact Filter.Eventually.of_forall (fun C μ => by
      let P :=
        (Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2
      simpa [cutoffAffordanceProbability_statement,
        cutoffAffordanceProbability, P] using
        (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) η
          (definition_indexSuffixLarge_statement
            (definition_epsilonFloorSplitIndex_statement epsilon C) C)
          (cutoffOut C P)))
  have hsmall_int :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          Integrable
            (fun w : ℝ =>
              (1 - totalSupply - epsilon -
                (1 - Real.exp (-(2 * epsilon * sigma)))) *
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexPrefixSmall_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  w
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))) η := by
    exact Filter.Eventually.of_forall (fun C μ => by
      let P :=
        (Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2
      have hbase :
          Integrable
            (fun w : ℝ =>
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (definition_indexPrefixSmall_statement
                  (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                w (cutoffOut C P)) η := by
        simpa [cutoffAffordanceProbability_statement,
          cutoffAffordanceProbability, P] using
          (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) η
            (definition_indexPrefixSmall_statement
              (definition_epsilonFloorSplitIndex_statement epsilon C) C)
            (cutoffOut C P))
      simpa [P] using
        hbase.const_mul
          (1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma)))))
  have hlarge_endpoint_choice :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          AppliedModelingLib.Matching.choiceMass
              (outcomeLaw C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2))
              (chosenCollege C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2))
              (definition_indexSuffixLarge_statement
                (definition_epsilonFloorSplitIndex_statement epsilon C) C) -
              epsilon ≤
            cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (definition_indexSuffixLarge_statement
                (definition_epsilonFloorSplitIndex_statement epsilon C) C)
              vHigh
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2)) := by
    filter_upwards
      [hlarge_endpoint_event_chosen, hlarge_endpoint_event_bound] with
      C hchosenC hboundC μ
    let P :=
      (Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2
    haveI : IsProbabilityMeasure (outcomeLaw C P) :=
      houtcome_prob C μ
    haveI : IsFiniteMeasure (outcomeLaw C P) := by infer_instance
    exact
      theorem2_largeFirm_highEndpoint_choiceMass_bound_of_event_imp
        (outcomeLaw C P)
        (chosenCollege C P)
        (definition_indexSuffixLarge_statement
          (definition_epsilonFloorSplitIndex_statement epsilon C) C)
        (event := largeEndpointEvent C μ)
        (le_of_lt hepsilon)
        (hchosenC μ)
        (hboundC μ)
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff, largeIntervalEvent,
      largeEndpointEvent, smallMatchedIntervalEvent, smallInterval,
      hvLow, hvHigh, hvStar, hvStrict, hlower_atTop, hcutoff_lower,
      htail_floor, ?_, hlarge_event_chosen,
      hlarge_endpoint_event_chosen, hlarge_endpoint_event_bound, hsmall_meas,
      hsmall_int, hsmall_mass, hsmall_ge, hsmall_integral_event,
      hsmall_event_chosen⟩
  · filter_upwards
      [hlarge_meas, hlarge_int, hlarge_mass, hlarge_ge,
        hlarge_integral_event] with
      C hmeasC hintC hmassC hgeC hintegralC μ
    let P :=
      (Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2
    have hpLarge_mono :
        Monotone (fun w : ℝ =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (definition_indexSuffixLarge_statement
              (definition_epsilonFloorSplitIndex_statement epsilon C) C)
            w (cutoffOut C P)) := by
      intro x y hxy
      exact
        cutoffAffordanceProbability_mono_value
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (active := definition_indexSuffixLarge_statement
            (definition_epsilonFloorSplitIndex_statement epsilon C) C)
          (cutoff := cutoffOut C P) hxy
    have hpLow_nonneg :
        0 ≤
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (definition_indexSuffixLarge_statement
              (definition_epsilonFloorSplitIndex_statement epsilon C) C)
            vLow (cutoffOut C P) :=
      cutoffAffordanceProbability_nonneg
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (definition_indexSuffixLarge_statement
          (definition_epsilonFloorSplitIndex_statement epsilon C) C)
        vLow (cutoffOut C P)
    have hnonneg_compl :
        ∀ w : ℝ, w ∉ largeInterval C μ →
          0 ≤
            cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (definition_indexSuffixLarge_statement
                (definition_epsilonFloorSplitIndex_statement epsilon C) C)
              w (cutoffOut C P) := by
      intro w _hw
      exact
        cutoffAffordanceProbability_nonneg
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (definition_indexSuffixLarge_statement
            (definition_epsilonFloorSplitIndex_statement epsilon C) C)
          w (cutoffOut C P)
    exact
      theorem2_largeFirm_eventMass_lower_bound_of_interval_integral
        η
        (region := largeInterval C μ)
        (mass := 1 - epsilon)
        (eventMass :=
          AppliedModelingLib.Matching.eventMass
            (outcomeLaw C P) (largeIntervalEvent C μ))
        (pLarge := fun w : ℝ =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (definition_indexSuffixLarge_statement
              (definition_epsilonFloorSplitIndex_statement epsilon C) C)
            w (cutoffOut C P))
        (vLow := vLow)
        (hmeasC μ) (hintC μ) (hmassC μ) hpLow_nonneg
        hpLarge_mono (hgeC μ) hnonneg_compl (hintegralC μ)

/--
Theorem 2 amplification from the named PG24 source model package.

Source status: active PG24 Theorem 2 route with selected-stable outcome
probability, singleton choice-event semantics, capacity regularity, and the
local large/small interval-event clauses bundled for recursive source-record
audit.
-/
theorem theorem2_uniform_amplification_source_assumptions_from_fixed_alpha_iidProduct_selected_stable_cutoff_floor_index_split_local_probabilityEvent_aggregateDemand_large_small_interval_integral_endpoint_estimates_paper_capacity_strict_derived_statement
    {StudentSeq : ℕ → Type u}
    (η : Measure ℝ) [IsProbabilityMeasure η]
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
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (H :
      Theorem2AmplificationSourceModel
        η Mseq Iseq noiseLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege
        totalSupply alpha) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          |cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2)) -
            totalSupply| < ε :=
  theorem2_uniform_amplification_source_clauses_from_fixed_alpha_iidProduct_selected_stable_cutoff_floor_index_split_local_probabilityEvent_aggregateDemand_large_small_interval_integral_endpoint_estimates_paper_capacity_strict_derived_statement
    η Mseq Iseq Kseq noiseLaw hlong cutoffOut
    OutcomeSeq outcomeLaw chosenCollege
    H.outcome_probability H.singleton_choice_measurable
    H.singleton_choice_mass_eq_aggregateDemand
    htotalSupply_lt_one hcapacity_sum H.capacity_open_bound
    (by
      simpa only [definition_indexSuffixLarge_statement,
        definition_indexPrefixSmall_statement,
        definition_epsilonFloorSplitIndex_statement] using
        H.local_interval_event_clauses)

/--
Theorem 2 amplification from a finite-outcome PG24 source model.

Source status: reviewed finite-outcome variant of the active PG24 Theorem 2
route.  The paper-facing statement lists each source clause directly rather
than hiding the remaining local large/small interval-event obligation in a
source-model record.  Lean derives singleton choice-event measurability from
the finite discrete outcome space.
-/
theorem theorem2_uniform_amplification_source_assumptions_from_AL_source_model_fixed_alpha_iidProduct_selected_stable_finite_outcome_local_event_source_model_statement
    {StudentSeq : ℕ → Type u}
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (Kseq : ∀ C : ℕ, MarketClearingCapacityInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    [∀ C, Finite (OutcomeSeq C)]
    [∀ C, MeasurableSingletonClass (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (outcome_probability :
      source_assumption_market_outcome_probability
        Mseq OutcomeSeq outcomeLaw)
    (choice_mass_eq_aggregateDemand :
      source_assumption_market_choice_mass_eq_aggregateDemand
        Mseq OutcomeSeq outcomeLaw chosenCollege)
    (capacity_open_bound :
      source_assumption_capacity_open_bound Mseq alpha)
    (hsource :
      source_assumption_theorem2_local_interval_event_clauses
        η Mseq Iseq noiseLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege
        (totalSupply := totalSupply)) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          |cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2)) -
            totalSupply| < ε :=
  theorem2_uniform_amplification_source_clauses_from_fixed_alpha_iidProduct_selected_stable_cutoff_floor_index_split_local_probabilityEvent_aggregateDemand_large_small_interval_integral_endpoint_estimates_paper_capacity_strict_derived_statement
    η Mseq Iseq Kseq noiseLaw hlong cutoffOut
    OutcomeSeq outcomeLaw chosenCollege
    (source_assumption_selected_stable_outcome_probability_of_market
      outcome_probability)
    source_assumption_selected_stable_singleton_choice_measurable_of_finite_outcome
    (source_assumption_selected_stable_singleton_choice_mass_eq_aggregateDemand_of_market
      choice_mass_eq_aggregateDemand)
    htotalSupply_lt_one hcapacity_sum capacity_open_bound hsource

/--
Theorem 2 (amplification) from the literal source economy.

Source status: repaired direct formalization of `main-results.tex:21-26` and
`proof-amplifying.tex:26-250`.  The printed quantile-window sentence does not
cover real targets outside a bounded connected support.  The formal proof
repairs that step by fixing one support-interior anchor and using long-tail
value-shift multipliers on the low-cutoff block.  It derives the local
interval/event estimates from the primitive iid market, clearing, Holder,
capacity, and long-tail inputs; no local-event or scalar-endpoint conclusion
is assumed.
-/
theorem theorem2_amplification_from_literal_source_primitives_statement
    {StudentTypeSeq : ℕ → Type u}
    [∀ C : ℕ, MeasurableSpace (StudentTypeSeq C)]
    {Admissible : ℕ → Type v}
    (CutoffSeq : ℕ → Type w)
    (noiseLaw eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    {totalSupply alpha : ℝ}
    (market : ∀ C : ℕ, Admissible C →
      PG24LiteralBasicMarket C noiseLaw eta totalSupply alpha
        (StudentTypeSeq C) (CutoffSeq C))
    (selectedCutoff : ∀ C : ℕ, Admissible C → CutoffSeq C)
    (selectedCutoff_clearing : ∀ (C : ℕ) (a : Admissible C),
      (market C a).marketClearing (selectedCutoff C a))
    (hregular : PG24HolderIntervalRegular eta)
    (hconnected : IsPreconnected eta.support)
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (htotalSupply_pos : 0 < totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_pos : 0 < alpha) :
    ∀ target epsilon : ℝ, 0 < epsilon →
      ∀ᶠ C : ℕ in atTop, ∀ a : Admissible C,
        |cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) target
            ((market C a).demand.cutoffCoordinates (selectedCutoff C a)) -
          totalSupply| < epsilon := by
  intro target epsilon hepsilon
  have heventual :=
    PG24LiteralBasicTwoScaleInstance.theorem2_eventually_allRealTargetAbsBound_uniform_of_holder_longTailed
      CutoffSeq
      (fun C a =>
        (market C a).basicInstanceAt
          (selectedCutoff C a) (selectedCutoff_clearing C a))
      hregular hlong htotalSupply_pos htotalSupply_lt_one halpha_pos.le
      target epsilon hepsilon
  filter_upwards [heventual] with C hC a
  simpa only [cutoffAffordanceProbability_statement,
    PG24LiteralBasicMarket.basicInstanceAt_selectedCutoffVector] using hC a

/--
Theorem 2 amplification from the named PG24 source model package and bundled
A-L cutoff-market consequence certificates.

Source status: same active PG24 Theorem 2 route as above, but the
supply/demand and exact-fill interfaces are projected from one transparent
A-L consequence package per finite market.
-/
theorem theorem2_uniform_amplification_source_assumptions_from_AL_cutoffMarketConsequences_fixed_alpha_iidProduct_selected_stable_cutoff_floor_index_split_local_probabilityEvent_aggregateDemand_large_small_interval_integral_endpoint_estimates_paper_capacity_strict_derived_statement
    {StudentSeq : ℕ → Type u}
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Aseq :
      ∀ C : ℕ,
        AL16SupplyDemandMatching.CutoffMarketConsequences (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (H :
      Theorem2AmplificationSourceModel
        η Mseq (fun C => (Aseq C).supplyDemand) noiseLaw cutoffOut
        OutcomeSeq outcomeLaw chosenCollege totalSupply alpha) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          |cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                (((Aseq C).supplyDemand).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2)) -
            totalSupply| < ε :=
  theorem2_uniform_amplification_source_assumptions_from_fixed_alpha_iidProduct_selected_stable_cutoff_floor_index_split_local_probabilityEvent_aggregateDemand_large_small_interval_integral_endpoint_estimates_paper_capacity_strict_derived_statement
    η Mseq (fun C => (Aseq C).supplyDemand) (fun C => (Aseq C).exactFill)
    noiseLaw hlong cutoffOut OutcomeSeq outcomeLaw chosenCollege
    htotalSupply_lt_one hcapacity_sum H

/--
The local event source model implies the scalar endpoint source package.

Source status: PG24 Theorem 2 bridge.  The paper's local value-window/event
clauses are stronger than the scalar endpoint package: Lean turns the interval
integrals into event-mass lower bounds, uses the selected-stable
chosen-college semantics to compare event mass to active capacity, and uses
the exact-fill market-clearing interface to identify aggregate demand with
capacity.
-/
theorem theorem2_scalar_endpoint_estimates_from_selected_stable_local_interval_event_source_model_statement
    {StudentSeq : ℕ → Type u}
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (Kseq : ∀ C : ℕ, MarketClearingCapacityInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    {totalSupply alpha : ℝ}
    (hcapacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (H :
      Theorem2AmplificationSourceModel
        η Mseq Iseq noiseLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege
        totalSupply alpha) :
    source_assumption_theorem2_scalar_endpoint_estimates
      Mseq Iseq noiseLaw cutoffOut (totalSupply := totalSupply) := by
  intro v epsilon sigma hepsilon hsigma hden
  rcases H.local_interval_event_clauses v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, largeIntervalEvent,
      largeEndpointEvent, smallMatchedIntervalEvent, largeInterval,
      smallInterval,
      hvLow, hvHigh, hvStar, hvStrict, _hlower_atTop, hcutoff_lower,
      htail_floor, hlarge_meas, hlarge_mass, hlarge_ge,
      hlarge_integral_event, hlarge_event_chosen,
      hlarge_endpoint_event_chosen, hlarge_endpoint_event_bound,
      hsmall_meas, hsmall_mass, hsmall_ge, hsmall_integral_event,
      hsmall_event_chosen⟩
  have hchoiceMass_eq_aggregateDemand :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          ∀ active : Finset (Fin (C + 1)),
            AppliedModelingLib.Matching.choiceMass
                (outcomeLaw C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := μ.1) μ.2))
                (chosenCollege C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := μ.1) μ.2))
                active =
              ∑ c ∈ active,
                (Mseq C).aggregateDemand
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := μ.1) μ.2) c := by
    filter_upwards
      [H.singleton_choice_measurable,
        H.singleton_choice_mass_eq_aggregateDemand] with
      C hmeasC hsingleC μ active
    let P :=
      (Iseq C).marketClearingCutoffOfStable
        (μ := μ.1) μ.2
    haveI : IsProbabilityMeasure (outcomeLaw C P) :=
      H.outcome_probability C μ
    haveI : IsFiniteMeasure (outcomeLaw C P) := by infer_instance
    exact
      AppliedModelingLib.Matching.choiceMass_eq_sum_aggregateDemand_of_singleton_eventMass_eq
        (outcomeLaw C P) (chosenCollege C P) active
        (by
          intro c hc
          exact hmeasC μ c)
        (by
          intro c hc
          exact hsingleC μ c)
  have hmarketClearing_aggregateDemand_eq_capacity :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          ∀ c : Fin (C + 1),
            (Mseq C).aggregateDemand
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2) c =
              (Mseq C).capacity c :=
    Filter.Eventually.of_forall (fun C μ c =>
      AppliedModelingLib.Matching.MarketClearingCapacityInterface.marketClearingCutoffOfStable_aggregateDemand_eq_capacity
        (Kseq C) (Iseq C) μ.2 c)
  have hlarge_interval_lower :
      ∀ᶠ C : ℕ in atTop,
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
              (largeIntervalEvent C μ) := by
    filter_upwards
      [hlarge_meas, hlarge_mass, hlarge_ge, hlarge_integral_event] with
      C hmeasC hmassC hgeC hintegralC μ
    let P :=
      (Iseq C).marketClearingCutoffOfStable
        (μ := μ.1) μ.2
    have hpLarge_mono :
        Monotone (fun w : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
            w (cutoffOut C P)) := by
      intro x y hxy
      exact
        cutoffAffordanceProbability_mono_value
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (active := indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
          (cutoff := cutoffOut C P) hxy
    have hint :
        Integrable
          (fun w : ℝ =>
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
              w (cutoffOut C P)) η := by
      simpa [cutoffAffordanceProbability, P] using
        (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) η
          (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
          (cutoffOut C P))
    have hpLow_nonneg :
        0 ≤
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
            vLow (cutoffOut C P) :=
      cutoffAffordanceProbability_nonneg
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
        vLow (cutoffOut C P)
    have hnonneg_compl :
        ∀ w : ℝ, w ∉ largeInterval C μ →
          0 ≤
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
              w (cutoffOut C P) := by
      intro w _hw
      exact
        cutoffAffordanceProbability_nonneg
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
          w (cutoffOut C P)
    exact
      theorem2_largeFirm_eventMass_lower_bound_of_interval_integral
        η
        (region := largeInterval C μ)
        (mass := 1 - epsilon)
        (eventMass :=
          AppliedModelingLib.Matching.eventMass
            (outcomeLaw C P) (largeIntervalEvent C μ))
        (pLarge := fun w : ℝ =>
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
            w (cutoffOut C P))
        (vLow := vLow)
        (hmeasC μ) hint (hmassC μ) hpLow_nonneg
        hpLarge_mono (hgeC μ) hnonneg_compl (hintegralC μ)
  have hsmall_interval_lower :
      ∀ᶠ C : ℕ in atTop,
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
              (smallMatchedIntervalEvent C μ) := by
    filter_upwards
      [hsmall_meas, hsmall_mass, hsmall_ge, hsmall_integral_event] with
      C hmeasC hmassC hgeC hintegralC μ
    let P :=
      (Iseq C).marketClearingCutoffOfStable
        (μ := μ.1) μ.2
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
    have hbase_int :
        Integrable
          (fun w : ℝ =>
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
              w (cutoffOut C P)) η := by
      simpa [cutoffAffordanceProbability, P] using
        (AppliedModelingLib.Matching.cutoffCrossingProbability_integrable_value
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) η
          (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
          (cutoffOut C P))
    have hint :
        Integrable
          (fun w : ℝ =>
            (1 - totalSupply - epsilon -
              (1 - Real.exp (-(2 * epsilon * sigma)))) *
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                w (cutoffOut C P)) η := by
      simpa [P] using
        hbase_int.const_mul
          (1 - totalSupply - epsilon -
            (1 - Real.exp (-(2 * epsilon * sigma))))
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
        (hmeasC μ) hint (hmassC μ) (le_of_lt hden)
        hpStar_nonneg hpSmall_mono (hgeC μ) hnonneg_compl
        (hintegralC μ)
  have hlarge_endpoint_choice :
      ∀ᶠ C : ℕ in atTop,
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
                  (μ := μ.1) μ.2)) := by
    filter_upwards
      [hlarge_endpoint_event_chosen, hlarge_endpoint_event_bound] with
      C hchosenC hboundC μ
    let P :=
      (Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2
    haveI : IsProbabilityMeasure (outcomeLaw C P) :=
      H.outcome_probability C μ
    haveI : IsFiniteMeasure (outcomeLaw C P) := by infer_instance
    exact
      theorem2_largeFirm_highEndpoint_choiceMass_bound_of_event_imp
        (outcomeLaw C P)
        (chosenCollege C P)
        (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
        (event := largeEndpointEvent C μ)
        (le_of_lt hepsilon)
        (hchosenC μ)
        (hboundC μ)
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar, hvStrict,
      hcutoff_lower, htail_floor, ?_, ?_, ?_⟩
  · filter_upwards
      [hlarge_interval_lower, hlarge_event_chosen,
        hchoiceMass_eq_aggregateDemand,
        hmarketClearing_aggregateDemand_eq_capacity,
        hcapacity_sum] with
      C hlargeLowerC hlargeChosenC hchoiceC hclearC htotalC μ
    let P :=
      (Iseq C).marketClearingCutoffOfStable
        (μ := μ.1) μ.2
    haveI : IsProbabilityMeasure (outcomeLaw C P) :=
      H.outcome_probability C μ
    haveI : IsFiniteMeasure (outcomeLaw C P) := by infer_instance
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
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity :=
        hevent_le_capacity
      _ = (∑ c : Fin (C + 1), (Mseq C).capacity c) := by
        simp [AppliedModelingLib.Matching.activeCapacity]
      _ = totalSupply := htotalC
  · filter_upwards
      [hlarge_endpoint_choice, hchoiceMass_eq_aggregateDemand,
        hmarketClearing_aggregateDemand_eq_capacity] with
      C hlargeEndpointC hchoiceC hclearC μ
    let P :=
      (Iseq C).marketClearingCutoffOfStable
        (μ := μ.1) μ.2
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
        (hchoiceC μ (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C))
        (by intro c _hc; exact hclearC μ c)
    calc
      AppliedModelingLib.Matching.activeCapacity
          (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
          (Mseq C).capacity - epsilon =
          AppliedModelingLib.Matching.choiceMass
            (outcomeLaw C P) (chosenCollege C P)
            (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C) -
            epsilon := by
        rw [hchoice_large]
      _ ≤ cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
            vHigh (cutoffOut C P) :=
        hlargeEndpointC μ
  · filter_upwards
      [hsmall_interval_lower, hsmall_event_chosen,
        hchoiceMass_eq_aggregateDemand,
        hmarketClearing_aggregateDemand_eq_capacity] with
      C hsmallLowerC hsmallChosenC hchoiceC hclearC μ
    let P :=
      (Iseq C).marketClearingCutoffOfStable
        (μ := μ.1) μ.2
    haveI : IsProbabilityMeasure (outcomeLaw C P) :=
      H.outcome_probability C μ
    haveI : IsFiniteMeasure (outcomeLaw C P) := by infer_instance
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
        (hchoiceC μ (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C))
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
            (Mseq C).capacity :=
        hevent_le_capacity

/--
The local event source model packages the scalar endpoint source model.

Source status: PG24 Theorem 2 source-record bridge used by provenance audits:
capacity regularity remains the same field, while the scalar endpoint field is
derived from the more primitive selected-stable local event semantics.
-/
theorem theorem2_scalar_endpoint_source_model_from_selected_stable_local_interval_event_source_model_statement
    {StudentSeq : ℕ → Type u}
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (Kseq : ∀ C : ℕ, MarketClearingCapacityInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    {totalSupply alpha : ℝ}
    (hcapacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (H :
      Theorem2AmplificationSourceModel
        η Mseq Iseq noiseLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege
        totalSupply alpha) :
    Theorem2ScalarEndpointSourceModel
      Mseq Iseq noiseLaw cutoffOut totalSupply alpha :=
  ⟨H.capacity_open_bound,
    theorem2_scalar_endpoint_estimates_from_selected_stable_local_interval_event_source_model_statement
      η Mseq Iseq Kseq noiseLaw cutoffOut OutcomeSeq outcomeLaw
      chosenCollege hcapacity_sum H⟩

/--
Theorem 2 source clauses from selected-stable scalar endpoint estimates with
the paper's total-capacity equality stated as a finite sum.

Source status: cleaner PG24 Theorem 2 route.  The source package is required
only at the A-L selected cutoff attached to each stable matching.  It exposes
the appendix's scalar cutoff-floor tail bound and endpoint capacity/probability
estimates directly; Lean derives the finite split, capacity regularity, product
noise bridge, and final amplification conclusion.
-/
theorem theorem2_uniform_amplification_source_clauses_from_fixed_alpha_iidProduct_selected_stable_cutoff_floor_index_split_scalar_tail_market_capacity_paper_sum_source_endpoint_estimates_strict_derived_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (hcapacity_open_bound :
      source_assumption_capacity_open_bound Mseq alpha)
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
              ∀ c ∈ definition_indexSuffixLarge_statement
                  (definition_epsilonFloorSplitIndex_statement epsilon C) C,
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
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexSuffixLarge_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vLow
                    (cutoffOut C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2)) ≤
                totalSupply) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              AppliedModelingLib.Matching.activeCapacity
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity - epsilon ≤
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (definition_indexSuffixLarge_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  vHigh
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2))) ∧
          (∀ᶠ C : ℕ in atTop,
            ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
              Real.sqrt epsilon *
                  (1 - totalSupply - epsilon -
                    (1 - Real.exp (-(2 * epsilon * sigma)))) *
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (definition_indexPrefixSmall_statement
                      (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                    vStar
                    (cutoffOut C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2)) ≤
                AppliedModelingLib.Matching.activeCapacity
                  (definition_indexPrefixSmall_statement
                    (definition_epsilonFloorSplitIndex_statement epsilon C) C)
                  (Mseq C).capacity)) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          |cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2)) -
            totalSupply| < ε := by
  have hcapacity_total :
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Matching.activeCapacity
            (Finset.univ : Finset (Fin (C + 1))) (Mseq C).capacity =
          totalSupply := by
    filter_upwards [hcapacity_sum] with C hC
    simpa using hC
  exact
    theorem2_uniformAmplification_source_clauses_of_fixed_alpha_iidProduct_selected_stable_cutoff_floor_index_split_scalar_tail_market_capacity_paper_positive_capacity_source_endpoint_estimates_strict_derived
      Mseq Iseq noiseLaw hlong cutoffOut htotalSupply_lt_one
      hcapacity_total hcapacity_open_bound hsource

/--
Theorem 2 amplification from scalar endpoint source clauses and bundled A-L
cutoff-market consequence certificates.

Source status: preferred PG24 Theorem 2 boundary.  It keeps the paper's
positive capacity regularity and scalar sorted-suffix endpoint estimates
visible, while projecting the selected-stable cutoff bridge from the A-L
consequence package and avoiding the heavier outcome-event source package.
-/
theorem theorem2_uniform_amplification_source_assumptions_from_AL_cutoffMarketConsequences_fixed_alpha_iidProduct_selected_stable_cutoff_floor_index_split_scalar_tail_market_capacity_paper_sum_source_endpoint_estimates_strict_derived_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Aseq :
      ∀ C : ℕ,
        AL16SupplyDemandMatching.CutoffMarketConsequences (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (H :
      Theorem2ScalarEndpointSourceModel
        Mseq (fun C => (Aseq C).supplyDemand) noiseLaw cutoffOut
        totalSupply alpha) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          |cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                (((Aseq C).supplyDemand).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2)) -
            totalSupply| < ε :=
  theorem2_uniform_amplification_source_clauses_from_fixed_alpha_iidProduct_selected_stable_cutoff_floor_index_split_scalar_tail_market_capacity_paper_sum_source_endpoint_estimates_strict_derived_statement
    Mseq (fun C => (Aseq C).supplyDemand) noiseLaw hlong cutoffOut
    htotalSupply_lt_one hcapacity_sum H.capacity_open_bound
    (by
      intro v epsilon sigma hepsilon hsigma hden
      rcases H.scalar_endpoint_estimates v epsilon sigma hepsilon hsigma hden with
        ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar,
          hvStrict, hcutoff_lower, htail_floor, hmass_upper,
          hlarge_endpoint, hsmall_capacity_lower⟩
      have hlower_atTop :
          Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop :=
        theorem2_lowerCutoff_sub_vHigh_atTop_of_AL_high_tail_rate
          Mseq Aseq noiseLaw hlong htail_floor
      exact
        ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar,
          hvStrict, hlower_atTop, hcutoff_lower, htail_floor, hmass_upper,
          hlarge_endpoint, hsmall_capacity_lower⟩)

/--
Theorem 2 amplification from the selected-stable local-event source model via
the scalar endpoint source bridge and bundled A-L cutoff-market consequences.

Source status: provenance wrapper.  It records that the preferred scalar
endpoint route is not an additional source boundary when the stronger local
selected-stable event clauses are available: Lean first derives the scalar
endpoint package and then reuses the scalar amplification theorem.
-/
theorem theorem2_uniform_amplification_source_assumptions_from_AL_cutoffMarketConsequences_fixed_alpha_iidProduct_selected_stable_local_event_source_model_via_scalar_endpoint_statement
    {StudentSeq : ℕ → Type u}
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Aseq :
      ∀ C : ℕ,
        AL16SupplyDemandMatching.CutoffMarketConsequences (Mseq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (H :
      Theorem2AmplificationSourceModel
        η Mseq (fun C => (Aseq C).supplyDemand) noiseLaw cutoffOut
        OutcomeSeq outcomeLaw chosenCollege totalSupply alpha) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          |cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                (((Aseq C).supplyDemand).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2)) -
            totalSupply| < ε :=
  theorem2_uniform_amplification_source_assumptions_from_AL_cutoffMarketConsequences_fixed_alpha_iidProduct_selected_stable_cutoff_floor_index_split_scalar_tail_market_capacity_paper_sum_source_endpoint_estimates_strict_derived_statement
    Mseq Aseq noiseLaw hlong cutoffOut htotalSupply_lt_one hcapacity_sum
    (theorem2_scalar_endpoint_source_model_from_selected_stable_local_interval_event_source_model_statement
      η Mseq (fun C => (Aseq C).supplyDemand)
      (fun C => (Aseq C).exactFill) noiseLaw cutoffOut OutcomeSeq
      outcomeLaw chosenCollege hcapacity_sum H)

/--
Theorem 2 amplification from scalar endpoint source clauses and the single
explicit A-L source-model boundary.

Source status: same active PG24 Theorem 2 scalar route as the A-L consequence
wrapper, deriving each finite market's consequence package from the explicit
AL source-model record.
-/
theorem theorem2_uniform_amplification_source_assumptions_from_AL_source_model_fixed_alpha_iidProduct_selected_stable_cutoff_floor_index_split_scalar_tail_market_capacity_paper_sum_source_endpoint_estimates_strict_derived_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (leCutoffSeq :
      ∀ C : ℕ, (Mseq C).Cutoff → (Mseq C).Cutoff → Prop)
    (HALseq :
      ∀ C : ℕ,
        AL16SupplyDemandMatching.CutoffMarketConsequenceSourceModel
          (Mseq C) (leCutoffSeq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (H :
      Theorem2ScalarEndpointSourceModel
        Mseq
        (fun C =>
          (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
            (Mseq C) (HALseq C)).supplyDemand)
        noiseLaw cutoffOut totalSupply alpha) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          |cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                (SupplyDemandInterface.marketClearingCutoffOfStable
                  (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
                    (Mseq C) (HALseq C)).supplyDemand
                  (μ := μ.1) μ.2)) -
            totalSupply| < ε :=
  theorem2_uniform_amplification_source_assumptions_from_AL_cutoffMarketConsequences_fixed_alpha_iidProduct_selected_stable_cutoff_floor_index_split_scalar_tail_market_capacity_paper_sum_source_endpoint_estimates_strict_derived_statement
    Mseq
    (fun C =>
      AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
        (Mseq C) (HALseq C))
    noiseLaw hlong cutoffOut htotalSupply_lt_one hcapacity_sum H

/--
Theorem 2 amplification from market-level scalar endpoint source clauses and
the single explicit A-L source-model boundary.

Source status: preferred PG24 Theorem 2 scalar route.  The endpoint estimates
are stated for every market-clearing cutoff; Lean derives the selected-stable
form using the A-L source-model bridge.
-/
theorem theorem2_uniform_amplification_source_assumptions_from_AL_source_model_fixed_alpha_iidProduct_market_cutoff_floor_index_split_scalar_tail_market_capacity_paper_sum_source_endpoint_estimates_strict_derived_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (leCutoffSeq :
      ∀ C : ℕ, (Mseq C).Cutoff → (Mseq C).Cutoff → Prop)
    (HALseq :
      ∀ C : ℕ,
        AL16SupplyDemandMatching.CutoffMarketConsequenceSourceModel
          (Mseq C) (leCutoffSeq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (H :
      Theorem2ScalarMarketEndpointSourceModel
        Mseq noiseLaw cutoffOut totalSupply alpha) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          |cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                (SupplyDemandInterface.marketClearingCutoffOfStable
                  (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
                    (Mseq C) (HALseq C)).supplyDemand
                  (μ := μ.1) μ.2)) -
            totalSupply| < ε :=
  theorem2_uniform_amplification_source_assumptions_from_AL_source_model_fixed_alpha_iidProduct_selected_stable_cutoff_floor_index_split_scalar_tail_market_capacity_paper_sum_source_endpoint_estimates_strict_derived_statement
    Mseq leCutoffSeq HALseq noiseLaw hlong cutoffOut htotalSupply_lt_one
    hcapacity_sum
    { capacity_open_bound := H.capacity_open_bound
      scalar_endpoint_estimates :=
        source_assumption_theorem2_scalar_endpoint_estimates_of_market
          (Iseq := fun C =>
            (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
              (Mseq C) (HALseq C)).supplyDemand)
          H.scalar_market_endpoint_estimates }

/--
Theorem 2 amplification from explicit market-level scalar endpoint source
clauses with an explicit high-tail quantile floor.

Source status: strengthened PG24 Theorem 2 scalar route.  The theorem-facing
premises expose capacity regularity and the market endpoint inequalities with
the lower cutoff fixed to a distributional quantile floor; Lean derives the
scalar high-tail-rate conjunct used by the long-tail proof.
-/
theorem theorem2_uniform_amplification_source_assumptions_from_AL_source_model_fixed_alpha_iidProduct_market_quantile_cutoff_floor_index_split_scalar_tail_market_capacity_paper_sum_source_endpoint_estimates_strict_derived_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (leCutoffSeq :
      ∀ C : ℕ, (Mseq C).Cutoff → (Mseq C).Cutoff → Prop)
    (HALseq :
      ∀ C : ℕ,
        AL16SupplyDemandMatching.CutoffMarketConsequenceSourceModel
          (Mseq C) (leCutoffSeq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (hcapacity_open_bound :
      source_assumption_capacity_open_bound Mseq alpha)
    (hscalar_market_endpoint_estimates :
      source_assumption_theorem2_scalar_market_endpoint_estimates_quantile_floor
        Mseq noiseLaw cutoffOut (totalSupply := totalSupply)) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          |cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                (SupplyDemandInterface.marketClearingCutoffOfStable
                  (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
                    (Mseq C) (HALseq C)).supplyDemand
                  (μ := μ.1) μ.2)) -
            totalSupply| < ε :=
  theorem2_uniform_amplification_source_assumptions_from_AL_source_model_fixed_alpha_iidProduct_market_cutoff_floor_index_split_scalar_tail_market_capacity_paper_sum_source_endpoint_estimates_strict_derived_statement
    Mseq leCutoffSeq HALseq noiseLaw hlong cutoffOut htotalSupply_lt_one
    hcapacity_sum
    { capacity_open_bound := hcapacity_open_bound
      scalar_market_endpoint_estimates :=
        source_assumption_theorem2_scalar_market_endpoint_estimates_of_quantile_floor
          hscalar_market_endpoint_estimates }

/--
Theorem 2 amplification from one bundled PG24 compatibility source package.

Source status: compatibility wrapper.  The audited theorem-facing quantile
route above exposes the total-supply, capacity, and endpoint clauses as visible
premises; this wrapper only unpacks the legacy source package before calling
that route.
-/
theorem theorem2_uniform_amplification_source_model_from_AL_source_model_fixed_alpha_iidProduct_market_quantile_cutoff_floor_index_split_scalar_tail_market_capacity_paper_sum_source_endpoint_estimates_strict_derived_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (leCutoffSeq :
      ∀ C : ℕ, (Mseq C).Cutoff → (Mseq C).Cutoff → Prop)
    (HALseq :
      ∀ C : ℕ,
        AL16SupplyDemandMatching.CutoffMarketConsequenceSourceModel
          (Mseq C) (leCutoffSeq C))
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply alpha : ℝ}
    (H :
      Theorem2ScalarMarketEndpointQuantileCapacitySourceModel
        Mseq noiseLaw cutoffOut totalSupply alpha) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          |cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                (SupplyDemandInterface.marketClearingCutoffOfStable
                  (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
                    (Mseq C) (HALseq C)).supplyDemand
                  (μ := μ.1) μ.2)) -
            totalSupply| < ε :=
  theorem2_uniform_amplification_source_assumptions_from_AL_source_model_fixed_alpha_iidProduct_market_quantile_cutoff_floor_index_split_scalar_tail_market_capacity_paper_sum_source_endpoint_estimates_strict_derived_statement
    Mseq leCutoffSeq HALseq noiseLaw hlong cutoffOut
    H.totalSupply_lt_one H.capacity_sum H.endpoint.capacity_open_bound
    H.endpoint.scalar_market_endpoint_estimates

/--
Theorem 2 amplification from the local-event source model and the exact
supply/demand and market-clearing-capacity interfaces used by the proof.

Source status: the local outcome/event clauses remain the open PG24 appendix
boundary. Lean derives the scalar endpoint estimates from those clauses before
deriving the final amplification conclusion; scalar endpoints are not accepted
as a field of this reviewed theorem.
-/
theorem theorem2_uniform_amplification_source_assumptions_from_AL_source_model_fixed_alpha_iidProduct_selected_stable_local_event_source_model_via_scalar_endpoint_statement
    {StudentSeq : ℕ → Type u}
    (η : Measure ℝ) [IsProbabilityMeasure η]
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
    {totalSupply alpha : ℝ}
    (htotalSupply_lt_one : totalSupply < 1)
    (hcapacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (H :
      Theorem2AmplificationSourceModel
        η Mseq Iseq
        noiseLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege
        totalSupply alpha) :
    ∀ v ε, 0 < ε →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          |cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2)) -
            totalSupply| < ε :=
  theorem2_uniform_amplification_source_assumptions_from_fixed_alpha_iidProduct_selected_stable_cutoff_floor_index_split_local_probabilityEvent_aggregateDemand_large_small_interval_integral_endpoint_estimates_paper_capacity_strict_derived_statement
    η Mseq Iseq Kseq noiseLaw hlong cutoffOut OutcomeSeq outcomeLaw
    chosenCollege htotalSupply_lt_one hcapacity_sum H

/--
Theorem 2 independent-product monotonicity.

Source status: PG24 amplification and coalition proof routes use that
affordability probabilities are monotone in the student's value.  For the
independent-product representation, this follows from pointwise monotonicity
of each single-college crossing probability.
-/
theorem independent_affordance_probability_monotone_in_value_statement
    {College : Type*} (active : Finset College)
    {crossingProbability : ℝ → College → ℝ}
    (hpointwise_mono :
      ∀ c ∈ active, Monotone (fun v => crossingProbability v c))
    (hle_one :
      ∀ v c, c ∈ active → crossingProbability v c ≤ 1) :
    Monotone (fun v => independentAffordanceProbability active
      (crossingProbability v)) :=
  independentAffordanceProbability_mono_value
    active hpointwise_mono hle_one

/--
Theorem 2 long-tail independent-product estimate with the scalar floor
derived from the high-value crossing bound.

Source status: PG24 amplification appendix, `lt-approx-F2` route.  The
single-college high-value crossing probabilities are bounded by `sigma / C`,
and the elementary exponential floor is proved in Lean rather than assumed.
-/
theorem theorem2_longTail_independent_product_highCrossing_statement
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
        1 - Real.exp (-(2 * ε * σ)) :=
  independentAffordanceProbability_difference_eventually_le_exp_error_of_longTailed_highCrossingBound
    hlong hv hε hε_le_one hσ_nonneg hlower_atTop hcutoff_lower hhigh_pos
    hhigh_le_sigma_div hlow_failure_pos

/--
Theorem 2 large-firm interval step.

Source status: PG24 amplification appendix, Proposition `lt-large-firms`
after the endpoint supply/capacity bounds and the `lt-approx-F2` product
estimate have been established.
-/
theorem theorem2_large_firm_interval_statement
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
      pLarge v ≤ S + ε + (1 - Real.exp (-(2 * ε * σ))) :=
  theorem2_largeFirm_interval_of_endpoint_product_error
    hp_mono hvLow hvHigh hupper_low hlower_high hdiff

/--
Theorem 2 large-firm interval step, eventual appendix form.

Source status: PG24 amplification appendix applies the large-firm interval
argument once `C` is sufficiently large and the endpoint/product estimates
hold uniformly along the tail.
-/
theorem theorem2_large_firm_interval_eventually_statement
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
        pLarge C v ≤ S + ε + (1 - Real.exp (-(2 * ε * σ))) :=
  theorem2_largeFirm_interval_eventually_of_endpoint_product_error
    hp_mono hvLow hvHigh hupper_low hlower_high hdiff

/--
Theorem 2 low-endpoint upper bound from interval mass.

Source status: PG24 proof of Proposition `lt-large-firms`, deriving
`p_mu(v_-, C2) <= S + epsilon` from
`(1 - epsilon) p_mu(v_-, C2) <= S` and `S + epsilon < 1`.
-/
theorem theorem2_low_endpoint_upper_from_interval_mass_statement
    {pLow S ε : ℝ}
    (hε_pos : 0 < ε)
    (hS_nonneg : 0 ≤ S)
    (hS_eps_lt_one : S + ε < 1)
    (hmass_upper : (1 - ε) * pLow ≤ S) :
    pLow ≤ S + ε :=
  theorem2_lowEndpoint_upper_of_interval_mass_bound
    hε_pos hS_nonneg hS_eps_lt_one hmass_upper

/--
Theorem 2 final full-probability window from the large- and small-firm
estimates.

Source status: PG24 amplification appendix, equation `equiv-lt`, combining
the `C2` interval with the `C1` capacity error through
`p(v,C2) <= p(v) <= p(v,C1)+p(v,C2)`.
-/
theorem theorem2_full_interval_from_large_small_firms_statement
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
            (1 - S - ε - (1 - Real.exp (-(2 * ε * σ)))) :=
  theorem2_full_interval_of_large_and_small_firm_bounds
    hlarge hsmall hlarge_le_total htotal_le_sum

/--
Theorem 2 final full-probability window, eventual appendix form.

Source status: PG24 amplification appendix derives the large-firm window and
small-firm capacity bound eventually, then combines them through the source
decomposition inequalities for total match probability.
-/
theorem theorem2_full_interval_eventually_from_large_small_firms_statement
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
              (1 - S - ε - (1 - Real.exp (-(2 * ε * σ)))) :=
  theorem2_full_interval_eventually_of_large_and_small_firm_bounds
    hlarge hsmall hlarge_le_total htotal_le_sum

/--
Theorem 3 coalition attenuation target.

Source status: PG24 extended-model Theorem 3 target.  The rows below expose
the eventual-event form and the source witness clauses for the large subset
and low/high affordability inequalities.
-/
abbrev theorem3_coalition_attenuation_statement
    (lowBlocked highAdmitted : ℕ → ℝ → Prop) (threshold : ℝ) : Prop :=
  Theorem3CoalitionAttenuationConclusion lowBlocked highAdmitted threshold

/--
Theorem 3 coalition attenuation target, source-shaped epsilon-margin form.

Source status: PG24 extended-model Theorem 3 states the low-value and
high-value clauses with the margins `v' - epsilon` and `v' + epsilon`.
-/
abbrev theorem3_coalition_attenuation_epsilon_statement
    (lowBlocked highAdmitted : ℕ → ℝ → Prop)
    (epsilon threshold : ℝ) : Prop :=
  Theorem3CoalitionAttenuationEpsilonConclusion
    lowBlocked highAdmitted epsilon threshold

/--
Theorem 3 coalition attenuation, eventual-event form.

Source status: PG24 extended-model Theorem 3 prose conclusion; this unpacks
the two eventual event clauses.
-/
theorem theorem3_coalition_attenuation_eventual_bounds_statement
    {lowBlocked highAdmitted : ℕ → ℝ → Prop} {threshold : ℝ}
    (h : theorem3_coalition_attenuation_statement
      lowBlocked highAdmitted threshold) :
    (∀ v, v < threshold → ∀ᶠ C : ℕ in atTop, lowBlocked C v) ∧
    (∀ v, threshold < v → ∀ᶠ C : ℕ in atTop, highAdmitted C v) :=
  theorem3_coalition_attenuation_eventually_bounds h

/--
Theorem 3 coalition attenuation, shifted eventual-event form.

Source status: PG24 extended-model Theorem 3 prose conclusion with the
source's explicit `epsilon` margin around the chosen threshold.
-/
theorem theorem3_coalition_attenuation_epsilon_eventual_bounds_statement
    {lowBlocked highAdmitted : ℕ → ℝ → Prop} {epsilon threshold : ℝ}
    (h : theorem3_coalition_attenuation_epsilon_statement
      lowBlocked highAdmitted epsilon threshold) :
    (∀ v, v < threshold - epsilon →
      ∀ᶠ C : ℕ in atTop, lowBlocked C v) ∧
    (∀ v, threshold + epsilon < v →
      ∀ᶠ C : ℕ in atTop, highAdmitted C v) :=
  theorem3_coalition_attenuation_epsilon_eventually_bounds h

/--
Theorem 3 coalition attenuation, source-shaped witness.

Source status: PG24 Theorem 3 produces a threshold `v'` and a subset
`C' subset C` with `|C'|/|C| > 1 - epsilon`; low values cannot afford `C'`
and high values can afford the full coalition.
-/
abbrev theorem3_coalition_attenuation_witness_statement
    {College : Type v}
    (coalition largeSubset : Finset College)
    (affordProb : ℝ → Finset College → ℝ)
    (epsilon threshold : ℝ) : Prop :=
  Theorem3CoalitionAttenuationWitness
    coalition largeSubset affordProb epsilon threshold

/--
Theorem 3 high-value transfer from subset to full coalition.

Source status: PG24 proof of Theorem 3 notes that once high-value students can
afford `C'`, they can also afford `C` by active-set monotonicity.
-/
theorem theorem3_coalition_attenuation_witness_from_subset_high_values_statement
    {College : Type v} {coalition largeSubset : Finset College}
    {affordProb : ℝ → Finset College → ℝ} {epsilon threshold : ℝ}
    (hlarge : CoalitionLargeSubset coalition largeSubset epsilon)
    (hlow :
      ∀ v, v < threshold - epsilon → affordProb v largeSubset < epsilon)
    (hhigh_subset :
      ∀ v, threshold + epsilon < v → 1 - epsilon < affordProb v largeSubset)
    (hmono :
      ∀ v, affordProb v largeSubset ≤ affordProb v coalition) :
    theorem3_coalition_attenuation_witness_statement
      coalition largeSubset affordProb epsilon threshold :=
  theorem3_coalitionAttenuationWitness_of_subset_high_values
    hlarge hlow hhigh_subset hmono

/--
Theorem 3 low-value clause from a monotone endpoint bound.

Source status: PG24 Theorem 3 proof uses value monotonicity; once the
large-subset affordability probability is below `epsilon` at
`threshold - epsilon`, it is below `epsilon` for all lower values.
-/
theorem theorem3_low_values_blocked_from_monotone_endpoint_bound_statement
    {College : Type v} {largeSubset : Finset College}
    {affordProb : ℝ → Finset College → ℝ} {epsilon threshold : ℝ}
    (hp_mono : Monotone (fun v => affordProb v largeSubset))
    (hlow_endpoint : affordProb (threshold - epsilon) largeSubset < epsilon) :
    ∀ v, v < threshold - epsilon → affordProb v largeSubset < epsilon :=
  theorem3_low_values_blocked_of_monotone_endpoint_bound
    hp_mono hlow_endpoint

/--
Theorem 3 high-value clause from a monotone endpoint bound.

Source status: PG24 Theorem 3 proof uses value monotonicity; once the full
coalition affordability probability is above `1 - epsilon` at
`threshold + epsilon`, it is above `1 - epsilon` for all higher values.
-/
theorem theorem3_high_values_admitted_from_monotone_endpoint_bound_statement
    {College : Type v} {coalition : Finset College}
    {affordProb : ℝ → Finset College → ℝ} {epsilon threshold : ℝ}
    (hp_mono : Monotone (fun v => affordProb v coalition))
    (hhigh_endpoint : 1 - epsilon < affordProb (threshold + epsilon) coalition) :
    ∀ v, threshold + epsilon < v → 1 - epsilon < affordProb v coalition :=
  theorem3_high_values_admitted_of_monotone_endpoint_bound
    hp_mono hhigh_endpoint

/--
Theorem 3 coalition attenuation witness from endpoint estimates.

Source status: PG24 Theorem 3 after choosing the threshold and large subset;
the remaining source work is the large-subset certificate, value monotonicity,
and the two displayed endpoint inequalities.
-/
theorem theorem3_coalition_attenuation_witness_from_monotone_endpoint_bounds_statement
    {College : Type v} {coalition largeSubset : Finset College}
    {affordProb : ℝ → Finset College → ℝ} {epsilon threshold : ℝ}
    (hlarge : CoalitionLargeSubset coalition largeSubset epsilon)
    (hmono_large : Monotone (fun v => affordProb v largeSubset))
    (hmono_coalition : Monotone (fun v => affordProb v coalition))
    (hlow_endpoint : affordProb (threshold - epsilon) largeSubset < epsilon)
    (hhigh_endpoint : 1 - epsilon < affordProb (threshold + epsilon) coalition) :
    theorem3_coalition_attenuation_witness_statement
      coalition largeSubset affordProb epsilon threshold :=
  theorem3_coalitionAttenuationWitness_of_monotone_endpoint_bounds
    hlarge hmono_large hmono_coalition hlow_endpoint hhigh_endpoint

/--
Theorem 3 source inequalities from the coalition witness.

Source status: PG24 extended-model Theorem 3 states exactly the large-subset
condition and the two affordability inequalities around the threshold shifted
down or up by `epsilon`; this row exposes those clauses from the formal
witness.
-/
theorem theorem3_coalition_attenuation_witness_source_clauses_statement
    {College : Type v} {coalition largeSubset : Finset College}
    {affordProb : ℝ → Finset College → ℝ} {epsilon threshold : ℝ}
    (h :
      theorem3_coalition_attenuation_witness_statement
        coalition largeSubset affordProb epsilon threshold) :
    CoalitionLargeSubset coalition largeSubset epsilon ∧
      (∀ v, v < threshold - epsilon → affordProb v largeSubset < epsilon) ∧
      (∀ v, threshold + epsilon < v → 1 - epsilon < affordProb v coalition) :=
  theorem3_coalitionAttenuationWitness_source_clauses h

/--
Theorem 3 coalition attenuation, indexed source-shaped witness.

Source status: PG24 Theorem 3 for growing coalition size.  This row combines
the eventual large-subset condition with the shifted low- and high-value
affordability clauses.
-/
abbrev theorem3_coalition_attenuation_indexed_witness_statement
    {College : ℕ → Type v}
    (coalition largeSubset : ∀ C : ℕ, Finset (College C))
    (affordProb : ∀ C : ℕ, ℝ → Finset (College C) → ℝ)
    (epsilon threshold : ℝ) : Prop :=
  Theorem3CoalitionAttenuationEpsilonWitnessConclusion
    coalition largeSubset affordProb epsilon threshold

/--
Theorem 3 coalition attenuation, uniform source-shaped witness.

Source status: PG24 Theorem 3 quantifies over every sufficiently large
coalition/stable-matching instance.  This row exposes that uniform shape by
using an admissible-instance family at each market size.
-/
abbrev theorem3_coalition_attenuation_uniform_witness_statement
    {College : ℕ → Type v} {Admissible : ℕ → Type u}
    (coalition largeSubset :
      ∀ C : ℕ, Admissible C → Finset (College C))
    (affordProb :
      ∀ C : ℕ, Admissible C → ℝ → Finset (College C) → ℝ)
    (epsilon : ℝ) (threshold : ∀ C : ℕ, Admissible C → ℝ) : Prop :=
  Theorem3CoalitionAttenuationUniformWitnessConclusion
    coalition largeSubset affordProb epsilon threshold

/--
Theorem 3 uniform witness from eventual endpoint estimates.

Source status: PG24 Theorem 3 proof after choosing the large subset and
threshold for each admissible instance.  The endpoint and monotonicity
conditions are required uniformly over all admissible instances at each
sufficiently large market size.
-/
theorem theorem3_coalition_attenuation_uniform_witness_from_eventual_endpoint_bounds_statement
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
    theorem3_coalition_attenuation_uniform_witness_statement
      coalition largeSubset affordProb epsilon threshold :=
  theorem3_coalitionAttenuationUniformWitness_of_eventual_monotone_endpoint_bounds
    hlarge hmono_large hmono_coalition hlow_endpoint hhigh_endpoint

/--
Theorem 3 uniform witness for the concrete iid cutoff-affordance model.

Source status: PG24 Theorem 3 in the product-noise cutoff-market shape, with
the theorem's uniform quantification represented by an admissible-instance
family.  Value monotonicity and subset-to-coalition transfer are derived
internally from cutoff-affordance monotonicity.
-/
theorem theorem3_coalition_attenuation_uniform_witness_from_iidProduct_cutoff_subset_endpoint_bounds_statement
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
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (largeSubset C a) (threshold C a - epsilon) (cutoff C a) <
            epsilon)
    (hhigh_subset_endpoint :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          1 - epsilon <
            cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) (threshold C a + epsilon) (cutoff C a)) :
    theorem3_coalition_attenuation_uniform_witness_statement
      coalition largeSubset
      (fun C : ℕ => fun a : Admissible C => fun v : ℝ =>
        fun active : Finset (Fin (C + 1)) =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            active v (cutoff C a))
      epsilon threshold :=
  theorem3_coalitionAttenuationUniformWitness_of_iidProduct_cutoff_subset_endpoint_bounds
    noiseLaw hlarge hlow_endpoint hhigh_subset_endpoint

/--
Theorem 3 uniform witness for selected stable matchings.

Source status: PG24 Theorem 3 is stated over stable matchings.  This row uses
the A-L supply-demand bridge to replace each selected stable matching by its
market-clearing cutoff, while keeping the theorem's uniform quantification
over admissible instances at each market size.
-/
theorem theorem3_coalition_attenuation_uniform_witness_from_iidProduct_stable_cutoff_subset_endpoint_bounds_statement
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
            cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) (threshold C a - epsilon)
              (cutoffOut C P) < epsilon)
    (hhigh_subset_endpoint :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
            1 - epsilon <
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) (threshold C a + epsilon)
                (cutoffOut C P)) :
    theorem3_coalition_attenuation_uniform_witness_statement
      coalition largeSubset
      (fun C : ℕ => fun a : Admissible C => fun v : ℝ =>
        fun active : Finset (Fin (C + 1)) =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            active v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2)))
      epsilon threshold :=
  theorem3_coalitionAttenuationUniformWitness_of_iidProduct_stable_cutoff_subset_endpoint_bounds
    Mseq Iseq selected noiseLaw cutoffOut hlarge hlow_endpoint
    hhigh_subset_endpoint

/--
Theorem 3 uniform witness for selected stable matchings with selected-cutoff
endpoint estimates.

Source status: narrowed PG24 Theorem 3 route.  Endpoint estimates are required
only at the A-L selected cutoff associated with each admissible stable
matching instance.
-/
theorem theorem3_coalition_attenuation_uniform_witness_from_iidProduct_selected_stable_cutoff_subset_endpoint_bounds_statement
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
          cutoffAffordanceProbability_statement
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
            cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) (threshold C a + epsilon)
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2))) :
    theorem3_coalition_attenuation_uniform_witness_statement
      coalition largeSubset
      (fun C : ℕ => fun a : Admissible C => fun v : ℝ =>
        fun active : Finset (Fin (C + 1)) =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            active v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2)))
      epsilon threshold :=
  theorem3_coalitionAttenuationUniformWitness_of_iidProduct_selected_stable_cutoff_subset_endpoint_bounds
    Mseq Iseq selected noiseLaw cutoffOut hlarge hlow_endpoint
    hhigh_subset_endpoint

/--
Theorem 3 uniform selected-stable source clauses from endpoint estimates.

Source status: preferred uniform PG24 Theorem 3 clause route.  The
large-subset condition and endpoint estimates are stated for market-clearing
cutoffs; Lean specializes them to every admissible selected stable matching
and exposes the low/high value clauses directly.
-/
theorem theorem3_coalition_attenuation_uniform_source_clauses_from_iidProduct_stable_cutoff_subset_endpoint_bounds_statement
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
            cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) (threshold C a - epsilon)
              (cutoffOut C P) < epsilon)
    (hhigh_subset_endpoint :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
            1 - epsilon <
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) (threshold C a + epsilon)
                (cutoffOut C P)) :
    (∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ v : ℝ,
          v < threshold C a - epsilon →
            cutoffAffordanceProbability_statement
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
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (coalition C a) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))) :=
  theorem3_coalitionAttenuationUniformWitness_source_clauses_of_iidProduct_stable_cutoff_subset_endpoint_bounds
    Mseq Iseq selected noiseLaw cutoffOut hlarge hlow_endpoint
    hhigh_subset_endpoint

/--
Theorem 3 uniform selected-stable source clauses with selected-cutoff endpoint
estimates.

Source status: narrowed PG24 Theorem 3 clause route.  Endpoint estimates are
required only at the A-L selected cutoff associated with each admissible
stable matching instance.
-/
theorem theorem3_coalition_attenuation_uniform_source_clauses_from_iidProduct_selected_stable_cutoff_subset_endpoint_bounds_statement
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
          cutoffAffordanceProbability_statement
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
            cutoffAffordanceProbability_statement
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
            cutoffAffordanceProbability_statement
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
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (coalition C a) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))) :=
  theorem3_coalitionAttenuationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_subset_endpoint_bounds
    Mseq Iseq selected noiseLaw cutoffOut hlarge hlow_endpoint
    hhigh_subset_endpoint

/--
Theorem 3 uniform selected-stable source clauses from scalar endpoint tail
estimates.

Source status: narrowed PG24 Theorem 3 route.  The visible low-endpoint input
is a per-college scalar upper-tail bound plus the finite union-bound size
condition, and the visible high-endpoint input is the iid product
no-crossing-probability estimate.  Lean derives the endpoint affordability
probabilities and then exposes the paper's large-subset, low-value, and
high-value clauses directly.
-/
theorem theorem3_coalition_attenuation_uniform_source_clauses_from_iidProduct_selected_stable_cutoff_scalar_tail_product_endpoint_estimates_statement
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
    {tailRate : ∀ C : ℕ, Admissible C → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon)
    (hlow_tail_controls :
      source_assumption_selected_stable_indexed_low_tail_controls
        Mseq Iseq selected noiseLaw cutoffOut largeSubset tailRate threshold
        epsilon)
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
            cutoffAffordanceProbability_statement
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
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (coalition C a) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))) :=
  theorem3_coalitionAttenuationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_scalar_tail_product_endpoint_estimates
    Mseq Iseq selected noiseLaw cutoffOut hlarge hlow_tail_controls.1
    hlow_tail_controls.2 hhigh_product

/--
Theorem 3 selected-stable existential source clauses.

Source status: paper-facing PG24 Theorem 3 shape.  The proof route above
selects the large subset `C'` and threshold `v'`; this row packages those
chosen witnesses into the theorem's existential statement for every
sufficiently large admissible stable-matching instance.
-/
theorem theorem3_coalition_attenuation_uniform_existential_source_clauses_from_iidProduct_selected_stable_cutoff_subset_endpoint_bounds_statement
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
          cutoffAffordanceProbability_statement
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
            cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) (threshold C a + epsilon)
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2))) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ threshold' : ℝ, ∃ largeSubset' : Finset (Fin (C + 1)),
          CoalitionLargeSubset (coalition C a) largeSubset' epsilon ∧
            (∀ v : ℝ, v < threshold' - epsilon →
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                largeSubset' v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) <
                epsilon) ∧
            (∀ v : ℝ, threshold' + epsilon < v →
              1 - epsilon <
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (coalition C a) v
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2))) := by
  have hclauses :=
    theorem3_coalition_attenuation_uniform_source_clauses_from_iidProduct_selected_stable_cutoff_subset_endpoint_bounds_statement
      Mseq Iseq selected noiseLaw cutoffOut hlarge hlow_endpoint
      hhigh_subset_endpoint
  filter_upwards [hclauses.1, hclauses.2.1, hclauses.2.2] with
    C hlargeC hlowC hhighC a
  exact ⟨threshold C a, largeSubset C a, hlargeC a, hlowC a, hhighC a⟩

/--
Theorem 3 selected-stable existential source clauses from scalar endpoint tail
estimates.

Source status: strongest current PG24 Theorem 3 existential route.  The
endpoint affordability estimates are not assumed directly: Lean derives the
low endpoint from per-college upper-tail bounds and a union bound, derives the
high endpoint from the iid no-crossing product, then packages the chosen
threshold and large subset into the theorem's existential conclusion.
-/
theorem theorem3_coalition_attenuation_uniform_existential_source_clauses_from_iidProduct_selected_stable_cutoff_scalar_tail_product_endpoint_estimates_statement
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
    {tailRate : ∀ C : ℕ, Admissible C → ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          CoalitionLargeSubset (coalition C a) (largeSubset C a) epsilon)
    (hlow_tail_controls :
      source_assumption_selected_stable_indexed_low_tail_controls
        Mseq Iseq selected noiseLaw cutoffOut largeSubset tailRate threshold
        epsilon)
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
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ threshold' : ℝ, ∃ largeSubset' : Finset (Fin (C + 1)),
          CoalitionLargeSubset (coalition C a) largeSubset' epsilon ∧
            (∀ v : ℝ, v < threshold' - epsilon →
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                largeSubset' v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) <
                epsilon) ∧
            (∀ v : ℝ, threshold' + epsilon < v →
              1 - epsilon <
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (coalition C a) v
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2))) := by
  have hclauses :=
    theorem3_coalition_attenuation_uniform_source_clauses_from_iidProduct_selected_stable_cutoff_scalar_tail_product_endpoint_estimates_statement
      Mseq Iseq selected noiseLaw cutoffOut hlarge hlow_tail_controls
      hhigh_product
  filter_upwards [hclauses.1, hclauses.2.1, hclauses.2.2] with
    C hlargeC hlowC hhighC a
  exact ⟨threshold C a, largeSubset C a, hlargeC a, hlowC a, hhighC a⟩

/--
Theorem 3 selected-stable existential source clauses from scalar cutoff-floor
and high-crossing endpoint estimates.

Source status: preferred PG24 Theorem 3 route.  The visible low-tail inputs
are the paper's large-subset size bound, an ordered scalar cutoff floor for
the selected stable cutoff, and a scalar upper-tail estimate at that floor.
Lean derives the per-college low-tail controls by upper-tail antitonicity,
derives the high endpoint from one college's upper-tail crossing estimate,
and packages the selected `v'` and `C'` into the theorem's existential
conclusion.
-/
theorem theorem3_coalition_attenuation_uniform_existential_source_clauses_from_iidProduct_selected_stable_cutoff_scalar_floor_tail_high_crossing_endpoint_estimates_statement
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
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ threshold' : ℝ, ∃ largeSubset' : Finset (Fin (C + 1)),
          CoalitionLargeSubset (coalition C a) largeSubset' epsilon ∧
            (∀ v : ℝ, v < threshold' - epsilon →
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                largeSubset' v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) <
                epsilon) ∧
            (∀ v : ℝ, threshold' + epsilon < v →
              1 - epsilon <
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (coalition C a) v
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2))) := by
  have hclauses :=
    theorem3_coalitionAttenuationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_scalar_floor_lowTail_exists_high_crossing_endpoint_estimates
      Mseq Iseq selected noiseLaw cutoffOut hlarge hlow_card_tail
      hcutoff_lower hlow_tail_floor hhigh_crossing
  filter_upwards [hclauses.1, hclauses.2.1, hclauses.2.2] with
    C hlargeC hlowC hhighC a
  exact ⟨threshold C a, largeSubset C a, hlargeC a, hlowC a, hhighC a⟩

/--
Theorem 3 selected-stable existential source clauses for the paper's sorted
suffix `C₂`.

Source status: preferred PG24 Theorem 3 route.  The chosen large subset is
the suffix after deleting the first `floor((epsilon/2)*(C+1))` sorted
colleges.  Lean derives that this suffix contains more than a `1-epsilon`
fraction of the coalition, derives the finite union-bound card-tail condition
from the scalar rate bound, and uses the visible sorted-index cutoff floor
to obtain the per-college low-tail controls.
-/
theorem theorem3_coalition_attenuation_uniform_existential_source_clauses_from_iidProduct_selected_stable_cutoff_suffix_scalar_floor_tail_high_crossing_endpoint_estimates_statement
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
          definition_epsilonFloorSplitIndex_statement (epsilon / 2) C ≤
            (c : ℕ) →
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
          ∃ c ∈ definition_indexSuffixLarge_statement
              (definition_epsilonFloorSplitIndex_statement (epsilon / 2) C) C,
            1 - epsilon <
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2) c -
                  (threshold C a + epsilon))) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ threshold' : ℝ, ∃ largeSubset' : Finset (Fin (C + 1)),
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' epsilon ∧
            (∀ v : ℝ, v < threshold' - epsilon →
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                largeSubset' v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) <
                epsilon) ∧
            (∀ v : ℝ, threshold' + epsilon < v →
              1 - epsilon <
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (Finset.univ : Finset (Fin (C + 1))) v
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2))) := by
  have hclauses :=
    theorem3_coalitionAttenuationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_suffix_scalar_floor_lowTail_exists_high_crossing_endpoint_estimates
      Mseq Iseq selected noiseLaw cutoffOut hepsilon_pos htailRate
      hcutoff_lower hlow_tail_floor hhigh_crossing
  filter_upwards [hclauses.1, hclauses.2.1, hclauses.2.2] with
    C hlargeC hlowC hhighC a
  exact
    ⟨threshold C a,
      definition_indexSuffixLarge_statement
        (definition_epsilonFloorSplitIndex_statement (epsilon / 2) C) C,
      hlargeC a, hlowC a, hhighC a⟩

/--
Theorem 3 selected-stable existential source clauses for the paper's sorted
suffix `C₂`, with the scalar low-tail endpoint stated directly at the
finite-union-bound rate `epsilon / (2*(C+1))`.

Source status: preferred PG24 Theorem 3 route.  Compared with the generic
suffix row, this removes the auxiliary `tailRate` witness from the visible
boundary.
-/
theorem theorem3_coalition_attenuation_uniform_existential_source_clauses_from_iidProduct_selected_stable_cutoff_suffix_scalar_floor_halfDiv_tail_high_crossing_endpoint_estimates_statement
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
          definition_epsilonFloorSplitIndex_statement (epsilon / 2) C ≤
            (c : ℕ) →
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
          ∃ c ∈ definition_indexSuffixLarge_statement
              (definition_epsilonFloorSplitIndex_statement (epsilon / 2) C) C,
            1 - epsilon <
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2) c -
                  (threshold C a + epsilon))) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ threshold' : ℝ, ∃ largeSubset' : Finset (Fin (C + 1)),
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' epsilon ∧
            (∀ v : ℝ, v < threshold' - epsilon →
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                largeSubset' v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) <
                epsilon) ∧
            (∀ v : ℝ, threshold' + epsilon < v →
              1 - epsilon <
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (Finset.univ : Finset (Fin (C + 1))) v
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2))) := by
  have hclauses :=
    theorem3_coalitionAttenuationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_suffix_scalar_floor_lowTail_halfDiv_exists_high_crossing_endpoint_estimates
      Mseq Iseq selected noiseLaw cutoffOut hepsilon_pos hcutoff_lower
      hlow_tail_floor hhigh_crossing
  filter_upwards [hclauses.1, hclauses.2.1, hclauses.2.2] with
    C hlargeC hlowC hhighC a
  exact
    ⟨threshold C a,
      definition_indexSuffixLarge_statement
        (definition_epsilonFloorSplitIndex_statement (epsilon / 2) C) C,
      hlargeC a, hlowC a, hhighC a⟩

/--
Theorem 3 selected-stable existential source clauses for the paper's sorted
suffix `C₂`, with both endpoints stated through scalar cutoff bounds.

Source status: preferred PG24 Theorem 3 route.  The low side uses the direct
finite-union-bound tail rate `epsilon / (2*(C+1))`; the high side derives the
one-college crossing witness from a suffix college whose selected-stable cutoff
is below a scalar upper ceiling and a scalar high-tail estimate at that ceiling.
-/
theorem theorem3_coalition_attenuation_uniform_existential_source_clauses_from_iidProduct_selected_stable_cutoff_suffix_scalar_floor_halfDiv_tail_upperCeiling_highTail_endpoint_estimates_statement
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
          definition_epsilonFloorSplitIndex_statement (epsilon / 2) C ≤
            (c : ℕ) →
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
          ∃ c ∈ definition_indexSuffixLarge_statement
              (definition_epsilonFloorSplitIndex_statement (epsilon / 2) C) C,
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
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ threshold' : ℝ, ∃ largeSubset' : Finset (Fin (C + 1)),
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' epsilon ∧
            (∀ v : ℝ, v < threshold' - epsilon →
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                largeSubset' v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) <
                epsilon) ∧
            (∀ v : ℝ, threshold' + epsilon < v →
              1 - epsilon <
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (Finset.univ : Finset (Fin (C + 1))) v
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2))) := by
  have hclauses :=
    theorem3_coalitionAttenuationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_suffix_scalar_floor_lowTail_halfDiv_upperCeiling_highTail_endpoint_estimates
      Mseq Iseq selected noiseLaw cutoffOut hepsilon_pos hcutoff_lower
      hlow_tail_floor hcutoff_upper_exists hhigh_tail_ceiling
  filter_upwards [hclauses.1, hclauses.2.1, hclauses.2.2] with
    C hlargeC hlowC hhighC a
  exact
    ⟨threshold C a,
      definition_indexSuffixLarge_statement
        (definition_epsilonFloorSplitIndex_statement (epsilon / 2) C) C,
      hlargeC a, hlowC a, hhighC a⟩

/--
Theorem 3 selected-stable existential source clauses for the paper's sorted
suffix `C₂`, with the high endpoint derived from upper-ceiling separation.

Source status: preferred PG24 Theorem 3 route.  The high-value tail estimate is
not a visible source premise here: Lean derives it from the fact that the scalar
upper ceiling minus `threshold + epsilon` is eventually arbitrarily negative.
-/
theorem theorem3_coalition_attenuation_uniform_existential_source_clauses_from_iidProduct_selected_stable_cutoff_suffix_scalar_floor_halfDiv_tail_upperCeiling_atBot_endpoint_estimates_statement
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
          definition_epsilonFloorSplitIndex_statement (epsilon / 2) C ≤
            (c : ℕ) →
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
          ∃ c ∈ definition_indexSuffixLarge_statement
              (definition_epsilonFloorSplitIndex_statement (epsilon / 2) C) C,
            cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2) c ≤
              upperCutoff C a)
    (hupper_ceiling_atBot :
      ∀ B : ℝ, ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          upperCutoff C a - (threshold C a + epsilon) ≤ B) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ threshold' : ℝ, ∃ largeSubset' : Finset (Fin (C + 1)),
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' epsilon ∧
            (∀ v : ℝ, v < threshold' - epsilon →
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                largeSubset' v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) <
                epsilon) ∧
            (∀ v : ℝ, threshold' + epsilon < v →
              1 - epsilon <
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (Finset.univ : Finset (Fin (C + 1))) v
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2))) := by
  have hclauses :=
    theorem3_coalitionAttenuationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_suffix_scalar_floor_lowTail_halfDiv_upperCeiling_atBot_endpoint_estimates
      Mseq Iseq selected noiseLaw cutoffOut hepsilon_pos hcutoff_lower
      hlow_tail_floor hcutoff_upper_exists hupper_ceiling_atBot
  filter_upwards [hclauses.1, hclauses.2.1, hclauses.2.2] with
    C hlargeC hlowC hhighC a
  exact
    ⟨threshold C a,
      definition_indexSuffixLarge_statement
        (definition_epsilonFloorSplitIndex_statement (epsilon / 2) C) C,
      hlargeC a, hlowC a, hhighC a⟩

/--
Theorem 3 selected-stable source-assumption route for the paper's sorted
suffix `C₂`.

Source status: preferred PG24 Theorem 3 boundary.  The remaining non-derived
inputs are named source assumptions: the suffix cutoff floor, the corresponding
low-tail rate, and the upper-ceiling separation used for high-value admission.
-/
theorem theorem3_coalition_attenuation_uniform_existential_source_assumptions_from_iidProduct_selected_stable_cutoff_suffix_statement
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
    {threshold lowerCutoff upperCutoff :
      ∀ C : ℕ, Admissible C → ℝ}
    (hcutoff_floor :
      source_assumption_theorem3_suffix_cutoff_floor
        Mseq Iseq selected cutoffOut (epsilon := epsilon) lowerCutoff)
    (hlow_tail_floor :
      source_assumption_theorem3_suffix_low_tail_floor_halfDiv
        noiseLaw (epsilon := epsilon) threshold lowerCutoff)
    (hupper_ceiling :
      source_assumption_theorem3_suffix_upper_ceiling_atBot
        Mseq Iseq selected cutoffOut (epsilon := epsilon)
        threshold upperCutoff) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ threshold' : ℝ, ∃ largeSubset' : Finset (Fin (C + 1)),
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' epsilon ∧
            (∀ v : ℝ, v < threshold' - epsilon →
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                largeSubset' v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) <
                epsilon) ∧
            (∀ v : ℝ, threshold' + epsilon < v →
              1 - epsilon <
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (Finset.univ : Finset (Fin (C + 1))) v
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2))) :=
  theorem3_coalition_attenuation_uniform_existential_source_clauses_from_iidProduct_selected_stable_cutoff_suffix_scalar_floor_halfDiv_tail_upperCeiling_atBot_endpoint_estimates_statement
    Mseq Iseq selected noiseLaw cutoffOut hepsilon_pos hcutoff_floor
    hlow_tail_floor hupper_ceiling.1 hupper_ceiling.2

/--
Theorem 3 selected-stable existential source model route.

Source status: same theorem as the source-assumption route, but with the
visible sorted-suffix cutoff-floor, low-tail, and upper-ceiling clauses bundled
into a single paper-facing source model record for audit.
-/
theorem theorem3_coalition_attenuation_uniform_existential_source_model_from_iidProduct_selected_stable_cutoff_suffix_statement
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
    {threshold lowerCutoff upperCutoff :
      ∀ C : ℕ, Admissible C → ℝ}
    (H :
      Theorem3CoalitionAttenuationSourceModel
        Mseq Iseq selected noiseLaw cutoffOut
        epsilon threshold lowerCutoff upperCutoff) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ threshold' : ℝ, ∃ largeSubset' : Finset (Fin (C + 1)),
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' epsilon ∧
            (∀ v : ℝ, v < threshold' - epsilon →
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                largeSubset' v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) <
                epsilon) ∧
            (∀ v : ℝ, threshold' + epsilon < v →
              1 - epsilon <
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (Finset.univ : Finset (Fin (C + 1))) v
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2))) :=
  theorem3_coalition_attenuation_uniform_existential_source_assumptions_from_iidProduct_selected_stable_cutoff_suffix_statement
    Mseq Iseq selected noiseLaw cutoffOut hepsilon_pos
    (source_assumption_theorem3_suffix_cutoff_floor_of_market
      (Iseq := Iseq) (selected := selected) H.cutoff_floor)
    H.low_tail_floor
    (source_assumption_theorem3_suffix_upper_ceiling_atBot_of_market
      (Iseq := Iseq) (selected := selected) H.upper_ceiling)

/--
Theorem 3 coalition attenuation from the named PG24 source model package and
bundled A-L cutoff-market consequence certificates.

Source status: same active PG24 Theorem 3 route as above, but the
supply/demand bridge used to read selected stable matchings as cutoffs is
projected from the transparent A-L consequence package.
-/
theorem theorem3_coalition_attenuation_uniform_existential_source_model_from_AL_cutoffMarketConsequences_iidProduct_selected_stable_cutoff_suffix_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Aseq :
      ∀ C : ℕ,
        AL16SupplyDemandMatching.CutoffMarketConsequences (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon)
    {threshold lowerCutoff upperCutoff :
      ∀ C : ℕ, Admissible C → ℝ}
    (H :
      Theorem3CoalitionAttenuationSourceModel
        Mseq (fun C => (Aseq C).supplyDemand) selected noiseLaw cutoffOut
        epsilon threshold lowerCutoff upperCutoff) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ threshold' : ℝ, ∃ largeSubset' : Finset (Fin (C + 1)),
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' epsilon ∧
            (∀ v : ℝ, v < threshold' - epsilon →
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                largeSubset' v
                (cutoffOut C
                  (((Aseq C).supplyDemand).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) <
                epsilon) ∧
            (∀ v : ℝ, threshold' + epsilon < v →
              1 - epsilon <
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (Finset.univ : Finset (Fin (C + 1))) v
                  (cutoffOut C
                    (((Aseq C).supplyDemand).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2))) :=
  theorem3_coalition_attenuation_uniform_existential_source_model_from_iidProduct_selected_stable_cutoff_suffix_statement
    Mseq (fun C => (Aseq C).supplyDemand) selected noiseLaw cutoffOut
    hepsilon_pos H

/--
Theorem 3 coalition attenuation from the single explicit A-L source-model
boundary.

Source status: same active PG24 Theorem 3 route as the A-L consequence wrapper,
deriving each finite market's consequence package from the explicit AL
source-model record.
-/
theorem theorem3_coalition_attenuation_uniform_existential_source_model_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (leCutoffSeq :
      ∀ C : ℕ, (Mseq C).Cutoff → (Mseq C).Cutoff → Prop)
    (HALseq :
      ∀ C : ℕ,
        AL16SupplyDemandMatching.CutoffMarketConsequenceSourceModel
          (Mseq C) (leCutoffSeq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon)
    {threshold lowerCutoff upperCutoff :
      ∀ C : ℕ, Admissible C → ℝ}
    (H :
      Theorem3CoalitionAttenuationSourceModel
        Mseq
        (fun C =>
          (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
            (Mseq C) (HALseq C)).supplyDemand)
        selected noiseLaw cutoffOut epsilon threshold lowerCutoff upperCutoff) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ threshold' : ℝ, ∃ largeSubset' : Finset (Fin (C + 1)),
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' epsilon ∧
            (∀ v : ℝ, v < threshold' - epsilon →
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                largeSubset' v
                (cutoffOut C
                  (SupplyDemandInterface.marketClearingCutoffOfStable
                    (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
                      (Mseq C) (HALseq C)).supplyDemand
                    (μ := (selected C a).1) (selected C a).2)) <
                epsilon) ∧
            (∀ v : ℝ, threshold' + epsilon < v →
              1 - epsilon <
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (Finset.univ : Finset (Fin (C + 1))) v
                  (cutoffOut C
                    (SupplyDemandInterface.marketClearingCutoffOfStable
                      (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
                        (Mseq C) (HALseq C)).supplyDemand
                      (μ := (selected C a).1) (selected C a).2))) :=
  theorem3_coalition_attenuation_uniform_existential_source_model_from_AL_cutoffMarketConsequences_iidProduct_selected_stable_cutoff_suffix_statement
    Mseq
    (fun C =>
      AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
        (Mseq C) (HALseq C))
    selected noiseLaw cutoffOut hepsilon_pos H

/--
Theorem 3 coalition attenuation from the A-L source model and an explicit
low-tail quantile floor.

Source status: active PG24 Theorem 3 route.  The visible source model assumes the
market cutoff floor at a concrete distributional quantile floor and the
upper-ceiling separation.  Lean derives the separate low-tail probability rate
from the quantile construction.
-/
theorem theorem3_coalition_attenuation_uniform_existential_quantile_source_model_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (leCutoffSeq :
      ∀ C : ℕ, (Mseq C).Cutoff → (Mseq C).Cutoff → Prop)
    (HALseq :
      ∀ C : ℕ,
        AL16SupplyDemandMatching.CutoffMarketConsequenceSourceModel
          (Mseq C) (leCutoffSeq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon)
    {threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (H :
      Theorem3CoalitionAttenuationQuantileSourceModel
        Mseq
        (fun C =>
          (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
            (Mseq C) (HALseq C)).supplyDemand)
        selected noiseLaw cutoffOut epsilon threshold upperCutoff) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ threshold' : ℝ, ∃ largeSubset' : Finset (Fin (C + 1)),
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' epsilon ∧
            (∀ v : ℝ, v < threshold' - epsilon →
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                largeSubset' v
                (cutoffOut C
                  (SupplyDemandInterface.marketClearingCutoffOfStable
                    (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
                      (Mseq C) (HALseq C)).supplyDemand
                    (μ := (selected C a).1) (selected C a).2)) <
                epsilon) ∧
            (∀ v : ℝ, threshold' + epsilon < v →
              1 - epsilon <
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (Finset.univ : Finset (Fin (C + 1))) v
                  (cutoffOut C
                    (SupplyDemandInterface.marketClearingCutoffOfStable
                      (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
                        (Mseq C) (HALseq C)).supplyDemand
                      (μ := (selected C a).1) (selected C a).2))) :=
  theorem3_coalition_attenuation_uniform_existential_source_model_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
    Mseq leCutoffSeq HALseq selected noiseLaw cutoffOut hepsilon_pos
    (lowerCutoff :=
      fun C a =>
        threshold C a - epsilon +
          theorem3LowTailQuantile noiseLaw epsilon C)
    { cutoff_floor := H.cutoff_floor
      low_tail_floor :=
        source_assumption_theorem3_suffix_low_tail_floor_halfDiv_of_quantile_floor
          noiseLaw hepsilon_pos threshold
      upper_ceiling := H.upper_ceiling }

/--
Theorem 3 coalition attenuation from the shared PG24 sorted-suffix
cutoff-geometry certificate.

Source status: strengthened active PG24 Theorem 3 route.  The theorem-specific
low-tail rate is derived from the explicit distributional quantile, while the
remaining cutoff-order facts are read from the single coalition suffix geometry
certificate shared with Theorem 4.
-/
theorem theorem3_coalition_attenuation_uniform_existential_geometry_source_model_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (leCutoffSeq :
      ∀ C : ℕ, (Mseq C).Cutoff → (Mseq C).Cutoff → Prop)
    (HALseq :
      ∀ C : ℕ,
        AL16SupplyDemandMatching.CutoffMarketConsequenceSourceModel
          (Mseq C) (leCutoffSeq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon tol sigma vHigh : ℝ} (hepsilon_pos : 0 < epsilon)
    {threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (H :
      Theorem34CoalitionSuffixCutoffGeometrySourceModel
        Mseq
        (fun C =>
          (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
            (Mseq C) (HALseq C)).supplyDemand)
        selected noiseLaw cutoffOut epsilon tol sigma vHigh
        threshold upperCutoff) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ threshold' : ℝ, ∃ largeSubset' : Finset (Fin (C + 1)),
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' epsilon ∧
            (∀ v : ℝ, v < threshold' - epsilon →
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                largeSubset' v
                (cutoffOut C
                  (SupplyDemandInterface.marketClearingCutoffOfStable
                    (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
                      (Mseq C) (HALseq C)).supplyDemand
                    (μ := (selected C a).1) (selected C a).2)) <
                epsilon) ∧
            (∀ v : ℝ, threshold' + epsilon < v →
              1 - epsilon <
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (Finset.univ : Finset (Fin (C + 1))) v
                  (cutoffOut C
                    (SupplyDemandInterface.marketClearingCutoffOfStable
                      (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
                        (Mseq C) (HALseq C)).supplyDemand
                      (μ := (selected C a).1) (selected C a).2))) :=
  theorem3_coalition_attenuation_uniform_existential_quantile_source_model_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
    Mseq leCutoffSeq HALseq selected noiseLaw cutoffOut hepsilon_pos
    { cutoff_floor := H.theorem3_cutoff_floor
      upper_ceiling := H.theorem3_upper_ceiling }

/--
Theorem 3 coalition attenuation from the count-based shared PG24 sorted-suffix
cutoff-geometry certificate.

Source status: strongest current PG24 Theorem 3 route.  The source supplies
sorted market-clearing cutoffs, a low-count bound for below-floor cutoffs, and
the upper-ceiling separation.  Lean derives the finite sorted-suffix cutoff
floor and the low-tail quantile rate.
-/
theorem theorem3_coalition_attenuation_uniform_existential_count_geometry_source_model_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (leCutoffSeq :
      ∀ C : ℕ, (Mseq C).Cutoff → (Mseq C).Cutoff → Prop)
    (HALseq :
      ∀ C : ℕ,
        AL16SupplyDemandMatching.CutoffMarketConsequenceSourceModel
          (Mseq C) (leCutoffSeq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon tol sigma vHigh : ℝ} (hepsilon_pos : 0 < epsilon)
    {threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (H :
      Theorem34CoalitionSuffixCutoffCountGeometrySourceModel
        Mseq
        (fun C =>
          (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
            (Mseq C) (HALseq C)).supplyDemand)
        selected noiseLaw cutoffOut epsilon tol sigma vHigh
        threshold upperCutoff) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ threshold' : ℝ, ∃ largeSubset' : Finset (Fin (C + 1)),
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' epsilon ∧
            (∀ v : ℝ, v < threshold' - epsilon →
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                largeSubset' v
                (cutoffOut C
                  (SupplyDemandInterface.marketClearingCutoffOfStable
                    (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
                      (Mseq C) (HALseq C)).supplyDemand
                    (μ := (selected C a).1) (selected C a).2)) <
                epsilon) ∧
            (∀ v : ℝ, threshold' + epsilon < v →
              1 - epsilon <
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (Finset.univ : Finset (Fin (C + 1))) v
                  (cutoffOut C
                    (SupplyDemandInterface.marketClearingCutoffOfStable
                      (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
                        (Mseq C) (HALseq C)).supplyDemand
                      (μ := (selected C a).1) (selected C a).2))) :=
  theorem3_coalition_attenuation_uniform_existential_geometry_source_model_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
    Mseq leCutoffSeq HALseq selected noiseLaw cutoffOut hepsilon_pos
    (theorem34_coalition_suffix_cutoff_geometry_of_sorted_low_count H)

/--
Theorem 3 coalition attenuation from the capacity-contradiction shared PG24
cutoff-geometry certificate.

Source status: stronger Theorem 3 route.  The source constructs a high-mass
matched event from a hypothetical failure of the low-cutoff count bound; Lean
uses A-L exact fill, choice-mass semantics, and total capacity to derive the
contradiction, then derives the sorted-suffix cutoff floor.
-/
theorem theorem3_coalition_attenuation_uniform_existential_capacity_contradiction_source_model_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (leCutoffSeq :
      ∀ C : ℕ, (Mseq C).Cutoff → (Mseq C).Cutoff → Prop)
    (HALseq :
      ∀ C : ℕ,
        AL16SupplyDemandMatching.CutoffMarketConsequenceSourceModel
          (Mseq C) (leCutoffSeq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    {totalSupply epsilon tol sigma vHigh : ℝ} (hepsilon_pos : 0 < epsilon)
    {threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (H :
      Theorem34CoalitionSuffixCutoffCapacityContradictionSourceModel
        Mseq
        (fun C =>
          (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
            (Mseq C) (HALseq C)).supplyDemand)
        selected noiseLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege
        totalSupply epsilon tol sigma vHigh threshold upperCutoff) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ threshold' : ℝ, ∃ largeSubset' : Finset (Fin (C + 1)),
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' epsilon ∧
            (∀ v : ℝ, v < threshold' - epsilon →
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                largeSubset' v
                (cutoffOut C
                  (SupplyDemandInterface.marketClearingCutoffOfStable
                    (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
                      (Mseq C) (HALseq C)).supplyDemand
                    (μ := (selected C a).1) (selected C a).2)) <
                epsilon) ∧
            (∀ v : ℝ, threshold' + epsilon < v →
              1 - epsilon <
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (Finset.univ : Finset (Fin (C + 1))) v
                  (cutoffOut C
                    (SupplyDemandInterface.marketClearingCutoffOfStable
                      (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
                        (Mseq C) (HALseq C)).supplyDemand
                      (μ := (selected C a).1) (selected C a).2))) :=
  theorem3_coalition_attenuation_uniform_existential_count_geometry_source_model_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
    Mseq leCutoffSeq HALseq selected noiseLaw cutoffOut hepsilon_pos
    (theorem34_coalition_suffix_cutoff_count_geometry_of_capacity_contradiction
      (Filter.Eventually.of_forall (fun C => by
        intro P hP c
        exact (HALseq C).exact_fill P hP c))
      H)

/--
Theorem 3 coalition attenuation from the integrated-capacity shared PG24
cutoff-geometry certificate.

Source status: strongest current Theorem 3 route.  The source states the
Lemma 11-style value-integrated low-cutoff affordability bound and the
outcome-model bridge from that integral to matched outcomes; Lean derives the
capacity contradiction, the low-count bound, and the sorted-suffix cutoff
floor.
-/
theorem theorem3_coalition_attenuation_uniform_existential_integrated_capacity_source_model_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (leCutoffSeq :
      ∀ C : ℕ, (Mseq C).Cutoff → (Mseq C).Cutoff → Prop)
    (HALseq :
      ∀ C : ℕ,
        AL16SupplyDemandMatching.CutoffMarketConsequenceSourceModel
          (Mseq C) (leCutoffSeq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (valueLaw : ∀ C : ℕ, Admissible C → Measure ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    {totalSupply epsilon tol sigma vHigh : ℝ} (hepsilon_pos : 0 < epsilon)
    {threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (H :
      Theorem34CoalitionSuffixCutoffIntegratedCapacitySourceModel
        Mseq
        (fun C =>
          (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
            (Mseq C) (HALseq C)).supplyDemand)
        selected noiseLaw cutoffOut valueLaw OutcomeSeq outcomeLaw
        chosenCollege totalSupply epsilon tol sigma vHigh
        threshold upperCutoff) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ threshold' : ℝ, ∃ largeSubset' : Finset (Fin (C + 1)),
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' epsilon ∧
            (∀ v : ℝ, v < threshold' - epsilon →
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                largeSubset' v
                (cutoffOut C
                  (SupplyDemandInterface.marketClearingCutoffOfStable
                    (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
                      (Mseq C) (HALseq C)).supplyDemand
                    (μ := (selected C a).1) (selected C a).2)) <
                epsilon) ∧
            (∀ v : ℝ, threshold' + epsilon < v →
              1 - epsilon <
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (Finset.univ : Finset (Fin (C + 1))) v
                  (cutoffOut C
                    (SupplyDemandInterface.marketClearingCutoffOfStable
                      (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
                        (Mseq C) (HALseq C)).supplyDemand
                      (μ := (selected C a).1) (selected C a).2))) :=
  theorem3_coalition_attenuation_uniform_existential_capacity_contradiction_source_model_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
    Mseq leCutoffSeq HALseq selected noiseLaw cutoffOut
    OutcomeSeq outcomeLaw chosenCollege hepsilon_pos
    (theorem34_coalition_suffix_cutoff_capacity_contradiction_of_integrated_capacity H)

/--
Theorem 3 coalition attenuation from the selected-stable integrated-capacity
PG24 cutoff-geometry certificate.

Source status: selected-stable strengthening of the integrated-capacity route.
The paper-facing statement lists the market/outcome identities and the still
unproved source estimates separately.  Lean derives finite mass, the high-mass
contradiction, the low-count bound, the sorted-suffix cutoff floor, and the
low-tail quantile rate without requiring the Theorem 4 floor estimate.
-/
theorem theorem3_coalition_attenuation_uniform_existential_selected_stable_integrated_capacity_source_model_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (Kseq : ∀ C : ℕ, MarketClearingCapacityInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (valueLaw : ∀ C : ℕ, Admissible C → Measure ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    {totalSupply epsilon tol sigma vHigh : ℝ} (hepsilon_pos : 0 < epsilon)
    {threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (outcome_probability :
      source_assumption_market_outcome_probability Mseq OutcomeSeq outcomeLaw)
    (choice_mass_eq_aggregateDemand :
      source_assumption_market_choice_mass_eq_aggregateDemand
        Mseq OutcomeSeq outcomeLaw chosenCollege)
    (capacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (value_probability :
      source_assumption_market_value_probability valueLaw)
    (selected_cutoff_sorted :
      source_assumption_selected_stable_cutoff_index_sorted
        Mseq Iseq selected cutoffOut)
    (integrated_affordance_event_bridge :
      source_assumption_market_integrated_affordance_event_bridge
        Mseq noiseLaw valueLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege)
    (theorem3_floor_pow_integral_exceeds_supply :
      source_assumption_selected_stable_low_cutoff_floor_pow_integral_exceeds_supply
        Mseq Iseq noiseLaw selected valueLaw cutoffOut
        (fun C : ℕ => epsilonFloorSplitIndex (epsilon / 2) C)
        (fun C a =>
          threshold C a - epsilon +
            theorem3LowTailQuantile noiseLaw epsilon C)
        totalSupply)
    (theorem3_upper_ceiling :
      source_assumption_theorem3_suffix_market_upper_ceiling_atBot
        Mseq cutoffOut (epsilon := epsilon) threshold upperCutoff) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ threshold' : ℝ, ∃ largeSubset' : Finset (Fin (C + 1)),
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' epsilon ∧
            (∀ v : ℝ, v < threshold' - epsilon →
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                largeSubset' v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) <
                epsilon) ∧
            (∀ v : ℝ, threshold' + epsilon < v →
              1 - epsilon <
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (Finset.univ : Finset (Fin (C + 1))) v
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2))) := by
  have hcapacity_clear :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c : Fin (C + 1),
          (Mseq C).aggregateDemand
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2) c =
            (Mseq C).capacity c := by
    exact Filter.Eventually.of_forall (fun C => by
      intro a c
      exact
        MarketClearingCapacityInterface.marketClearingCutoffOfStable_aggregateDemand_eq_capacity
          (Kseq C) (Iseq C) (selected C a).2 c)
  have hselected_sorted :
      source_assumption_selected_stable_cutoff_index_sorted
        Mseq Iseq selected cutoffOut :=
    selected_cutoff_sorted
  have htheorem3_low_count :
      source_assumption_theorem3_suffix_selected_stable_low_cutoff_count
        Mseq Iseq selected cutoffOut (epsilon := epsilon)
        (fun C a =>
          threshold C a - epsilon +
            theorem3LowTailQuantile noiseLaw epsilon C) :=
    source_assumption_theorem3_suffix_selected_stable_low_cutoff_count_of_capacity_contradiction
      (source_assumption_selected_stable_outcome_finite_of_probability
        (source_assumption_selected_stable_outcome_probability_of_market
          outcome_probability))
      (source_assumption_selected_stable_choice_mass_eq_aggregateDemand_of_market
        choice_mass_eq_aggregateDemand)
      hcapacity_clear
      capacity_sum
      (source_assumption_selected_stable_low_cutoff_capacity_contradiction_of_integrated_affordance_event_bridge
        (source_assumption_selected_stable_low_cutoff_integral_exceeds_supply_of_floor_pow_integral
          (source_assumption_market_value_finite_of_probability
            value_probability)
          theorem3_floor_pow_integral_exceeds_supply)
        (source_assumption_selected_stable_integrated_affordance_event_bridge_of_market
          integrated_affordance_event_bridge))
  have htheorem3_cutoff_floor :
      source_assumption_theorem3_suffix_cutoff_floor
        Mseq Iseq selected cutoffOut (epsilon := epsilon)
        (fun C a =>
          threshold C a - epsilon +
            theorem3LowTailQuantile noiseLaw epsilon C) :=
    source_assumption_theorem3_suffix_cutoff_floor_of_selected_stable_sorted_low_count
      hselected_sorted htheorem3_low_count
  have htheorem3_upper_ceiling :
      source_assumption_theorem3_suffix_upper_ceiling_atBot
        Mseq Iseq selected cutoffOut (epsilon := epsilon)
        threshold upperCutoff :=
    source_assumption_theorem3_suffix_upper_ceiling_atBot_of_market
      theorem3_upper_ceiling
  exact
    theorem3_coalition_attenuation_uniform_existential_source_assumptions_from_iidProduct_selected_stable_cutoff_suffix_statement
      Mseq Iseq selected noiseLaw cutoffOut hepsilon_pos
      htheorem3_cutoff_floor
      (source_assumption_theorem3_suffix_low_tail_floor_halfDiv_of_quantile_floor
        noiseLaw hepsilon_pos threshold)
      htheorem3_upper_ceiling

/--
Theorem 3 through integrated capacity and a direct high-crossing endpoint.

Source status: source-shaped repair surface for the coalition-attenuation
route.  It keeps the Lemma-11-style floor-power integral input used to derive
the selected-stable suffix floor, but it does not require the stronger
`upper_ceiling_atBot` package.  The high-value endpoint is exposed directly as
the one-college high-crossing estimate needed by the paper's endpoint route.
-/
theorem theorem3_coalition_attenuation_uniform_existential_selected_stable_integrated_capacity_high_crossing_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (Kseq : ∀ C : ℕ, MarketClearingCapacityInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (valueLaw : ∀ C : ℕ, Admissible C → Measure ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    {totalSupply epsilon tol sigma vHigh : ℝ} (hepsilon_pos : 0 < epsilon)
    {threshold : ∀ C : ℕ, Admissible C → ℝ}
    (outcome_probability :
      source_assumption_market_outcome_probability Mseq OutcomeSeq outcomeLaw)
    (choice_mass_eq_aggregateDemand :
      source_assumption_market_choice_mass_eq_aggregateDemand
        Mseq OutcomeSeq outcomeLaw chosenCollege)
    (capacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (value_probability :
      source_assumption_market_value_probability valueLaw)
    (selected_cutoff_sorted :
      source_assumption_selected_stable_cutoff_index_sorted
        Mseq Iseq selected cutoffOut)
    (integrated_affordance_event_bridge :
      source_assumption_market_integrated_affordance_event_bridge
        Mseq noiseLaw valueLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege)
    (theorem3_floor_pow_integral_exceeds_supply :
      source_assumption_selected_stable_low_cutoff_floor_pow_integral_exceeds_supply
        Mseq Iseq noiseLaw selected valueLaw cutoffOut
        (fun C : ℕ => epsilonFloorSplitIndex (epsilon / 2) C)
        (fun C a =>
          threshold C a - epsilon +
            theorem3LowTailQuantile noiseLaw epsilon C)
        totalSupply)
    (theorem3_high_crossing :
      source_assumption_theorem3_suffix_high_crossing_endpoint
        Mseq Iseq noiseLaw selected cutoffOut
        (epsilon := epsilon) threshold) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ threshold' : ℝ, ∃ largeSubset' : Finset (Fin (C + 1)),
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' epsilon ∧
            (∀ v : ℝ, v < threshold' - epsilon →
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                largeSubset' v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) <
                epsilon) ∧
            (∀ v : ℝ, threshold' + epsilon < v →
              1 - epsilon <
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (Finset.univ : Finset (Fin (C + 1))) v
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2))) := by
  have hcapacity_clear :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c : Fin (C + 1),
          (Mseq C).aggregateDemand
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2) c =
            (Mseq C).capacity c := by
    exact Filter.Eventually.of_forall (fun C => by
      intro a c
      exact
        MarketClearingCapacityInterface.marketClearingCutoffOfStable_aggregateDemand_eq_capacity
          (Kseq C) (Iseq C) (selected C a).2 c)
  have hselected_sorted :
      source_assumption_selected_stable_cutoff_index_sorted
        Mseq Iseq selected cutoffOut :=
    selected_cutoff_sorted
  have htheorem3_low_count :
      source_assumption_theorem3_suffix_selected_stable_low_cutoff_count
        Mseq Iseq selected cutoffOut (epsilon := epsilon)
        (fun C a =>
          threshold C a - epsilon +
            theorem3LowTailQuantile noiseLaw epsilon C) :=
    source_assumption_theorem3_suffix_selected_stable_low_cutoff_count_of_capacity_contradiction
      (source_assumption_selected_stable_outcome_finite_of_probability
        (source_assumption_selected_stable_outcome_probability_of_market
          outcome_probability))
      (source_assumption_selected_stable_choice_mass_eq_aggregateDemand_of_market
        choice_mass_eq_aggregateDemand)
      hcapacity_clear
      capacity_sum
      (source_assumption_selected_stable_low_cutoff_capacity_contradiction_of_integrated_affordance_event_bridge
        (source_assumption_selected_stable_low_cutoff_integral_exceeds_supply_of_floor_pow_integral
          (source_assumption_market_value_finite_of_probability
            value_probability)
          theorem3_floor_pow_integral_exceeds_supply)
        (source_assumption_selected_stable_integrated_affordance_event_bridge_of_market
          integrated_affordance_event_bridge))
  have htheorem3_cutoff_floor :
      source_assumption_theorem3_suffix_cutoff_floor
        Mseq Iseq selected cutoffOut (epsilon := epsilon)
        (fun C a =>
          threshold C a - epsilon +
            theorem3LowTailQuantile noiseLaw epsilon C) :=
    source_assumption_theorem3_suffix_cutoff_floor_of_selected_stable_sorted_low_count
      hselected_sorted htheorem3_low_count
  exact
    theorem3_coalition_attenuation_uniform_existential_source_clauses_from_iidProduct_selected_stable_cutoff_suffix_scalar_floor_halfDiv_tail_high_crossing_endpoint_estimates_statement
      Mseq Iseq selected noiseLaw cutoffOut hepsilon_pos
      htheorem3_cutoff_floor
      (source_assumption_theorem3_suffix_low_tail_floor_halfDiv_of_quantile_floor
        noiseLaw hepsilon_pos threshold)
      theorem3_high_crossing

/--
Theorem 3 through the pointwise low-CDF power/capacity route.

Source status: alternative audited repair surface for the coalition-attenuation
route.  It proves the same paper-facing conclusion as the integrated-capacity
row above, but exposes the remaining low-cutoff estimate as the pointwise
`1 - lowerCDFMass ^ card` inequality at the low-tail quantile floor.  Lean
derives the selected-stable capacity contradiction, low-count bound, and suffix
floor from that premise plus the pointwise outcome-event bridge.
-/
theorem theorem3_coalition_attenuation_uniform_existential_selected_stable_pointwise_capacity_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (Kseq : ∀ C : ℕ, MarketClearingCapacityInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    {totalSupply epsilon tol sigma vHigh : ℝ} (hepsilon_pos : 0 < epsilon)
    {threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (outcome_probability :
      source_assumption_market_outcome_probability Mseq OutcomeSeq outcomeLaw)
    (choice_mass_eq_aggregateDemand :
      source_assumption_market_choice_mass_eq_aggregateDemand
        Mseq OutcomeSeq outcomeLaw chosenCollege)
    (capacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (selected_cutoff_sorted :
      source_assumption_selected_stable_cutoff_index_sorted
        Mseq Iseq selected cutoffOut)
    (affordance_event_bridge :
      source_assumption_market_affordance_event_bridge
        Mseq noiseLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege)
    (theorem3_low_cutoff_pow_exceeds_supply :
      source_assumption_market_low_cutoff_pow_exceeds_supply
        Mseq noiseLaw cutoffOut
        (fun C : ℕ => epsilonFloorSplitIndex (epsilon / 2) C)
        (fun C a =>
          threshold C a - epsilon +
            theorem3LowTailQuantile noiseLaw epsilon C)
        (fun C a => threshold C a - epsilon)
        totalSupply)
    (theorem3_upper_ceiling :
      source_assumption_theorem3_suffix_market_upper_ceiling_atBot
        Mseq cutoffOut (epsilon := epsilon) threshold upperCutoff) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ threshold' : ℝ, ∃ largeSubset' : Finset (Fin (C + 1)),
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' epsilon ∧
            (∀ v : ℝ, v < threshold' - epsilon →
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                largeSubset' v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) <
                epsilon) ∧
            (∀ v : ℝ, threshold' + epsilon < v →
              1 - epsilon <
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (Finset.univ : Finset (Fin (C + 1))) v
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2))) := by
  have hcapacity_clear :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c : Fin (C + 1),
          (Mseq C).aggregateDemand
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2) c =
            (Mseq C).capacity c := by
    exact Filter.Eventually.of_forall (fun C => by
      intro a c
      exact
        MarketClearingCapacityInterface.marketClearingCutoffOfStable_aggregateDemand_eq_capacity
          (Kseq C) (Iseq C) (selected C a).2 c)
  have hselected_sorted :
      source_assumption_selected_stable_cutoff_index_sorted
        Mseq Iseq selected cutoffOut :=
    selected_cutoff_sorted
  have htheorem3_cutoff_floor :
      source_assumption_theorem3_suffix_cutoff_floor
        Mseq Iseq selected cutoffOut (epsilon := epsilon)
        (fun C a =>
          threshold C a - epsilon +
            theorem3LowTailQuantile noiseLaw epsilon C) :=
    source_assumption_theorem3_suffix_cutoff_floor_of_market_pow_affordance_event_bridge
      (source_assumption_selected_stable_outcome_finite_of_probability
        (source_assumption_selected_stable_outcome_probability_of_market
          outcome_probability))
      (source_assumption_selected_stable_choice_mass_eq_aggregateDemand_of_market
        choice_mass_eq_aggregateDemand)
      hcapacity_clear
      capacity_sum
      hselected_sorted
      theorem3_low_cutoff_pow_exceeds_supply
      affordance_event_bridge
  have htheorem3_upper_ceiling :
      source_assumption_theorem3_suffix_upper_ceiling_atBot
        Mseq Iseq selected cutoffOut (epsilon := epsilon)
        threshold upperCutoff :=
    source_assumption_theorem3_suffix_upper_ceiling_atBot_of_market
      theorem3_upper_ceiling
  exact
    theorem3_coalition_attenuation_uniform_existential_source_assumptions_from_iidProduct_selected_stable_cutoff_suffix_statement
      Mseq Iseq selected noiseLaw cutoffOut hepsilon_pos
      htheorem3_cutoff_floor
      (source_assumption_theorem3_suffix_low_tail_floor_halfDiv_of_quantile_floor
        noiseLaw hepsilon_pos threshold)
      htheorem3_upper_ceiling

/--
Theorem 3 through the pointwise upper-tail split-power route and the direct
semantic high-crossing endpoint.

Source status: active repair candidate for the coalition-attenuation route.
It uses the split-index strict upper-tail power estimate for the low-value side
and asks for the high-value endpoint on the semantic block of cutoffs that are
not below the scalar floor.  Lean derives the lower-CDF product form and then
the low-count premise from the split-index estimate, so this avoids the
integrated floor-power premise, the sorted relabeling premise, and the stronger
upper-ceiling package.
-/
theorem theorem3_coalition_attenuation_uniform_existential_selected_stable_pointwise_capacity_high_crossing_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (Kseq : ∀ C : ℕ, MarketClearingCapacityInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    {totalSupply epsilon : ℝ} (hepsilon_pos : 0 < epsilon)
    {threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (outcome_probability :
      source_assumption_market_outcome_probability Mseq OutcomeSeq outcomeLaw)
    (choice_mass_eq_aggregateDemand :
      source_assumption_market_choice_mass_eq_aggregateDemand
        Mseq OutcomeSeq outcomeLaw chosenCollege)
    (capacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (affordance_event_bridge :
      source_assumption_market_affordance_event_bridge
        Mseq noiseLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege)
    (theorem3_low_cutoff_upper_tail_split_pow_exceeds_supply :
      source_assumption_market_low_cutoff_upper_tail_split_pow_exceeds_supply
        Mseq noiseLaw
        (fun C : ℕ => epsilonFloorSplitIndex (epsilon / 2) C)
        (fun C a =>
          threshold C a - epsilon +
            theorem3LowTailQuantile noiseLaw epsilon C)
        (fun C a => threshold C a - epsilon)
        totalSupply)
    (theorem3_upper_ceiling :
      source_assumption_theorem3_nonLow_upper_ceiling_atBot
        Mseq Iseq selected cutoffOut (epsilon := epsilon)
        (fun C a =>
          threshold C a - epsilon +
            theorem3LowTailQuantile noiseLaw epsilon C)
        threshold upperCutoff) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ threshold' : ℝ, ∃ largeSubset' : Finset (Fin (C + 1)),
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' epsilon ∧
            (∀ v : ℝ, v < threshold' - epsilon →
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                largeSubset' v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) <
                epsilon) ∧
            (∀ v : ℝ, threshold' + epsilon < v →
              1 - epsilon <
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (Finset.univ : Finset (Fin (C + 1))) v
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2))) := by
  have hcapacity_clear :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c : Fin (C + 1),
          (Mseq C).aggregateDemand
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2) c =
            (Mseq C).capacity c := by
    exact Filter.Eventually.of_forall (fun C => by
      intro a c
      exact
        MarketClearingCapacityInterface.marketClearingCutoffOfStable_aggregateDemand_eq_capacity
          (Kseq C) (Iseq C) (selected C a).2 c)
  have htheorem3_low_count :
      source_assumption_theorem3_suffix_selected_stable_low_cutoff_count
        Mseq Iseq selected cutoffOut (epsilon := epsilon)
        (fun C a =>
          threshold C a - epsilon +
            theorem3LowTailQuantile noiseLaw epsilon C) :=
    source_assumption_theorem3_suffix_selected_stable_low_cutoff_count_of_capacity_contradiction
      (source_assumption_selected_stable_outcome_finite_of_probability
        (source_assumption_selected_stable_outcome_probability_of_market
          outcome_probability))
      (source_assumption_selected_stable_choice_mass_eq_aggregateDemand_of_market
        choice_mass_eq_aggregateDemand)
      hcapacity_clear
      capacity_sum
        (source_assumption_selected_stable_low_cutoff_capacity_contradiction_of_market_pow_affordance_event_bridge
        (source_assumption_market_low_cutoff_pow_exceeds_supply_of_split_pow
          (cutoffOut := cutoffOut)
          (source_assumption_market_low_cutoff_split_pow_exceeds_supply_of_upper_tail_split_pow
            theorem3_low_cutoff_upper_tail_split_pow_exceeds_supply))
        affordance_event_bridge)
  have theorem3_high_crossing :
      source_assumption_theorem3_nonLow_high_crossing_endpoint
        Mseq Iseq noiseLaw selected cutoffOut
        (epsilon := epsilon)
        (fun C a =>
          threshold C a - epsilon +
            theorem3LowTailQuantile noiseLaw epsilon C)
        threshold :=
    source_assumption_theorem3_nonLow_high_crossing_endpoint_of_upper_ceiling_atBot
      (Mseq := Mseq) (Iseq := Iseq) (selected := selected)
      (cutoffOut := cutoffOut) hepsilon_pos theorem3_upper_ceiling
  have hclauses :=
    theorem3_coalitionAttenuationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_nonLow_scalar_floor_lowTail_halfDiv_exists_high_crossing_endpoint_estimates
      Mseq Iseq selected noiseLaw cutoffOut hepsilon_pos
      htheorem3_low_count
      (source_assumption_theorem3_suffix_low_tail_floor_halfDiv_of_quantile_floor
        noiseLaw hepsilon_pos threshold)
      theorem3_high_crossing
  filter_upwards [hclauses.1, hclauses.2.1, hclauses.2.2] with
    C hlargeC hlowC hhighC a
  exact
    ⟨threshold C a,
      nonLowCutoffIndexSet
        (cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C a).1) (selected C a).2))
        (threshold C a - epsilon +
          theorem3LowTailQuantile noiseLaw epsilon C),
      hlargeC a, hlowC a, hhighC a⟩

/--
Theorem 3 indexed witness from eventual endpoint estimates.

Source status: PG24 proof of Theorem 3 after selecting the large subset.  It
uses value monotonicity and the two endpoint inequalities to obtain all
shifted low/high value clauses eventually.
-/
theorem theorem3_coalition_attenuation_indexed_witness_from_eventual_endpoint_bounds_statement
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
    theorem3_coalition_attenuation_indexed_witness_statement
      coalition largeSubset affordProb epsilon threshold :=
  theorem3_coalitionAttenuationEpsilonWitness_of_eventual_monotone_endpoint_bounds
    hlarge hmono_large hmono_coalition hlow_endpoint hhigh_endpoint

/--
Theorem 3 indexed witness from subset high-value transfer.

Source status: PG24 proof of Theorem 3 first proves the high-value
affordability bound for the large subset `C'`; active-set monotonicity then
transfers that bound to the full coalition `C`.
-/
theorem theorem3_coalition_attenuation_indexed_witness_from_subset_high_values_statement
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
    theorem3_coalition_attenuation_indexed_witness_statement
      coalition largeSubset affordProb epsilon threshold :=
  theorem3_coalitionAttenuationEpsilonWitness_of_eventual_subset_high_values
    hlarge hlow hhigh_subset hmono

/--
Theorem 3 indexed witness from subset endpoint estimates.

Source status: PG24 Theorem 3 after selecting `C'`; the low and high endpoint
estimates are both on `C'`, then high values transfer to `C` by monotonicity.
-/
theorem theorem3_coalition_attenuation_indexed_witness_from_subset_endpoint_bounds_statement
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
    theorem3_coalition_attenuation_indexed_witness_statement
      coalition largeSubset affordProb epsilon threshold :=
  theorem3_coalitionAttenuationEpsilonWitness_of_eventual_subset_endpoint_bounds
    hlarge hmono_large hlow_endpoint hhigh_subset_endpoint
    hmono_subset_coalition

/--
Theorem 3 indexed witness for independent-product affordance.

Source status: PG24 Theorem 3 in the concrete independent-noise affordance
shape.  The active-set transfer from `C'` to `C` is derived from
`C' subset C` and the fact that every single-college crossing probability is
in `[0,1]`, rather than assumed as an abstract monotonicity premise.
-/
theorem theorem3_coalition_attenuation_indexed_witness_from_independent_subset_endpoint_bounds_statement
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
    theorem3_coalition_attenuation_indexed_witness_statement
      coalition largeSubset
      (fun C : ℕ => fun v : ℝ => fun active : Finset (Fin (C + 1)) =>
        independentAffordanceProbability active (crossingProbability C v))
      epsilon threshold :=
  theorem3_coalitionAttenuationEpsilonWitness_of_independent_subset_endpoint_bounds
    hlarge hmono_large hlow_endpoint hhigh_subset_endpoint
    hprob_nonneg hprob_le_one

/--
Theorem 3 indexed witness for survival-function affordance.

Source status: PG24 Theorem 3 in the source survival-probability shape.  The
value monotonicity of large-subset affordability is derived from antitonicity
of the survival function, and the active-set transfer from `C'` to `C` is
derived from the concrete independent-product affordance formula.
-/
theorem theorem3_coalition_attenuation_indexed_witness_from_survival_subset_endpoint_bounds_statement
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
    theorem3_coalition_attenuation_indexed_witness_statement
      coalition largeSubset
      (fun C : ℕ => fun v : ℝ => fun active : Finset (Fin (C + 1)) =>
        independentAffordanceProbability
          active (fun c => survival (cutoff C c - v)))
      epsilon threshold :=
  theorem3_coalitionAttenuationEpsilonWitness_of_survival_subset_endpoint_bounds
    hsurvival_antitone hlarge hlow_endpoint hhigh_subset_endpoint
    hprob_nonneg hprob_le_one

/--
Theorem 3 indexed witness for concrete upper-tail affordance probabilities.

Source status: PG24 Theorem 3 in the real-noise-law shape.  The source only
supplies the large-subset condition and endpoint estimates; antitonicity and
probability bounds for `Pr[X > x]` are discharged by the library.
-/
theorem theorem3_coalition_attenuation_indexed_witness_from_upperTail_subset_endpoint_bounds_statement
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
    theorem3_coalition_attenuation_indexed_witness_statement
      coalition largeSubset
      (fun C : ℕ => fun v : ℝ => fun active : Finset (Fin (C + 1)) =>
        independentAffordanceProbability
          active
          (fun c =>
            AppliedModelingLib.Probability.upperTailMass noiseLaw
              (cutoff C c - v)))
      epsilon threshold :=
  theorem3_coalitionAttenuationEpsilonWitness_of_upperTail_subset_endpoint_bounds
    noiseLaw hlarge hlow_endpoint hhigh_subset_endpoint

/--
Theorem 3 indexed witness for the concrete iid cutoff-affordance model.

Source status: PG24 Theorem 3 in the product-noise cutoff-market shape.  The
endpoint estimates and conclusion are stated directly as cutoff-affordance
probabilities under the iid product noise law; Lean derives the independent
upper-tail product representation internally.
-/
theorem theorem3_coalition_attenuation_indexed_witness_from_iidProduct_cutoff_subset_endpoint_bounds_statement
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {coalition largeSubset : ∀ C : ℕ, Finset (Fin (C + 1))}
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ}
    {epsilon threshold : ℝ}
    (hlarge :
      ∀ᶠ C : ℕ in atTop,
        CoalitionLargeSubset (coalition C) (largeSubset C) epsilon)
    (hlow_endpoint :
      ∀ᶠ C : ℕ in atTop,
        cutoffAffordanceProbability_statement
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (largeSubset C) (threshold - epsilon) (cutoff C) <
            epsilon)
    (hhigh_subset_endpoint :
      ∀ᶠ C : ℕ in atTop,
        1 - epsilon <
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (largeSubset C) (threshold + epsilon) (cutoff C)) :
    theorem3_coalition_attenuation_indexed_witness_statement
      coalition largeSubset
      (fun C : ℕ => fun v : ℝ => fun active : Finset (Fin (C + 1)) =>
        cutoffAffordanceProbability_statement
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          active v (cutoff C))
      epsilon threshold :=
  theorem3_coalitionAttenuationEpsilonWitness_of_iidProduct_cutoff_subset_endpoint_bounds
    noiseLaw hlarge hlow_endpoint hhigh_subset_endpoint

/--
Theorem 3 indexed witness for a selected sequence of stable matchings.

Source status: PG24 Theorem 3 is applied to stable matchings.  This row uses
A-L Lemma 1 to choose each selected stable matching's market-clearing cutoff;
the endpoint estimates are stated for all market-clearing cutoffs.
-/
theorem theorem3_coalition_attenuation_indexed_witness_from_iidProduct_selected_stable_cutoff_subset_endpoint_bounds_statement
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
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (largeSubset C) (threshold - epsilon) (cutoffOut C P) <
              epsilon)
    (hhigh_subset_endpoint :
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          1 - epsilon <
            cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C) (threshold + epsilon) (cutoffOut C P)) :
    theorem3_coalition_attenuation_indexed_witness_statement
      coalition largeSubset
      (fun C : ℕ => fun v : ℝ => fun active : Finset (Fin (C + 1)) =>
        cutoffAffordanceProbability_statement
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          active v
          (cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C).1) (selected C).2)))
      epsilon threshold :=
  theorem3_coalitionAttenuationEpsilonWitness_of_iidProduct_selected_stable_cutoff_subset_endpoint_bounds
    Mseq Iseq selected noiseLaw cutoffOut hlarge hlow_endpoint
    hhigh_subset_endpoint

/--
Theorem 3 indexed source clauses from the growing-coalition witness.

Source status: PG24 Theorem 3 statement clauses: `C'` is eventually a large
subset, low values cannot afford `C'`, and high values can afford `C`.
-/
theorem theorem3_coalition_attenuation_indexed_witness_source_clauses_statement
    {College : ℕ → Type v}
    {coalition largeSubset : ∀ C : ℕ, Finset (College C)}
    {affordProb : ∀ C : ℕ, ℝ → Finset (College C) → ℝ}
    {epsilon threshold : ℝ}
    (h :
      theorem3_coalition_attenuation_indexed_witness_statement
        coalition largeSubset affordProb epsilon threshold) :
    (∀ᶠ C : ℕ in atTop,
      CoalitionLargeSubset (coalition C) (largeSubset C) epsilon) ∧
      (∀ v, v < threshold - epsilon →
        ∀ᶠ C : ℕ in atTop, affordProb C v (largeSubset C) < epsilon) ∧
      (∀ v, threshold + epsilon < v →
        ∀ᶠ C : ℕ in atTop, 1 - epsilon < affordProb C v (coalition C)) :=
  theorem3_coalitionAttenuationEpsilonWitness_source_clauses h

/--
Theorem 3 selected-stable source clauses from endpoint estimates.

Source status: preferred concrete PG24 Theorem 3 clause route.  The
large-subset condition and endpoint estimates are stated for market-clearing
cutoffs; Lean specializes them to the selected stable matchings and exposes
the low/high value clauses directly.
-/
theorem theorem3_coalition_attenuation_indexed_source_clauses_from_iidProduct_selected_stable_cutoff_subset_endpoint_bounds_statement
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
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (largeSubset C) (threshold - epsilon) (cutoffOut C P) <
              epsilon)
    (hhigh_subset_endpoint :
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          1 - epsilon <
            cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C) (threshold + epsilon) (cutoffOut C P)) :
    (∀ᶠ C : ℕ in atTop,
      CoalitionLargeSubset (coalition C) (largeSubset C) epsilon) ∧
      (∀ v, v < threshold - epsilon →
        ∀ᶠ C : ℕ in atTop,
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (largeSubset C) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C).1) (selected C).2)) < epsilon) ∧
      (∀ v, threshold + epsilon < v →
        ∀ᶠ C : ℕ in atTop,
          1 - epsilon <
            cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (coalition C) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C).1) (selected C).2))) :=
  theorem3_coalitionAttenuationEpsilonWitness_source_clauses_of_iidProduct_selected_stable_cutoff_subset_endpoint_bounds
    Mseq Iseq selected noiseLaw cutoffOut hlarge hlow_endpoint
    hhigh_subset_endpoint

/--
Theorem 3 indexed selected-stable source clauses from scalar endpoint tail
estimates.

Source status: narrowed PG24 Theorem 3 indexed route.  The visible low-endpoint
input is now a scalar lower-cutoff floor, a scalar upper-tail estimate at that
floor, and the finite union-bound size condition.  Lean derives the per-college
low-tail controls from cutoff ordering and upper-tail antitonicity.  The
visible high-endpoint input is a one-college upper-tail crossing estimate; Lean
converts this to the lower-CDF no-crossing form, derives the full no-crossing
product bound from probability bounds for the remaining factors, then exposes
the paper's eventual large-subset, low-value, and high-value clauses.
-/
theorem theorem3_coalition_attenuation_indexed_source_clauses_from_iidProduct_selected_stable_cutoff_scalar_tail_product_endpoint_estimates_statement
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
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (largeSubset C) v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C).1) (selected C).2)) < epsilon) ∧
      (∀ v, threshold + epsilon < v →
        ∀ᶠ C : ℕ in atTop,
          1 - epsilon <
            cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (coalition C) v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C).1) (selected C).2))) :=
  theorem3_coalitionAttenuationEpsilonWitness_source_clauses_of_iidProduct_selected_stable_cutoff_scalar_floor_lowTail_exists_high_crossing_endpoint_estimates
    Mseq Iseq selected noiseLaw cutoffOut hlarge hlow_card_tail
    hcutoff_lower hlow_tail_floor hhigh_crossing

/--
Theorem 4 coalition amplification target.

Source status: PG24 extended-model Theorem 4 target.  The rows below expose
the eventual-epsilon form and the source witness clauses for the large subset,
large-measure regular set, and effective-supply approximation inequality.
-/
abbrev theorem4_coalition_amplification_statement
    (coalitionProb : ℕ → ℝ → ℝ) (effectiveSupply : ℝ)
    (regularValue : ℝ → Prop) : Prop :=
  Theorem4CoalitionAmplificationConclusion
    coalitionProb effectiveSupply regularValue

/--
Theorem 4 coalition amplification, eventual-epsilon form.

Source status: PG24 extended-model Theorem 4 prose conclusion; this unpacks
convergence at regular values into the usual epsilon bound.
-/
theorem theorem4_coalition_amplification_eventual_abs_bound_statement
    {coalitionProb : ℕ → ℝ → ℝ} {effectiveSupply : ℝ}
    {regularValue : ℝ → Prop}
    (h : theorem4_coalition_amplification_statement
      coalitionProb effectiveSupply regularValue) :
    ∀ v ε, regularValue v → 0 < ε →
      ∀ᶠ C : ℕ in atTop, |coalitionProb C v - effectiveSupply| < ε :=
  theorem4_coalition_amplification_eventually_abs_bound h

/--
Theorem 4 coalition amplification, source-shaped witness.

Source status: PG24 Theorem 4 produces a large subset `C'`, an effective
supply `S'`, and a large-measure value set on which
`|p_mu(v,C') - S'| < epsilon`.
-/
abbrev theorem4_coalition_amplification_witness_statement
    {College : Type v}
    (coalition largeSubset : Finset College)
    (affordProb : ℝ → Finset College → ℝ)
    (valueMass : Set ℝ → ℝ)
    (regularSet : Set ℝ)
    (epsilon effectiveSupply : ℝ) : Prop :=
  Theorem4CoalitionAmplificationWitness
    coalition largeSubset affordProb valueMass regularSet
    epsilon effectiveSupply

/--
Theorem 4 witness from the regular-set form used in the proof.

Source status: PG24 proof rewrites the exceptional-set statement as existence
of a value set with mass greater than `1 - epsilon`.
-/
theorem theorem4_coalition_amplification_witness_from_regular_set_statement
    {College : Type v} {coalition largeSubset : Finset College}
    {affordProb : ℝ → Finset College → ℝ}
    {valueMass : Set ℝ → ℝ} {epsilon effectiveSupply : ℝ}
    (hlarge : CoalitionLargeSubset coalition largeSubset epsilon)
    (regularSet : Set ℝ)
    (hmass : 1 - epsilon < valueMass regularSet)
    (hclose :
      ∀ v ∈ regularSet, |affordProb v largeSubset - effectiveSupply| < epsilon) :
    theorem4_coalition_amplification_witness_statement
      coalition largeSubset affordProb valueMass regularSet
      epsilon effectiveSupply :=
  theorem4_coalitionAmplificationWitness_of_regular_set
    hlarge regularSet hmass hclose

/--
Theorem 4 regular-set mass from an exceptional-set bound.

Source status: PG24 extended-model Theorem 4 phrases the conclusion as
holding outside an exceptional value set.  This row converts a strict
exceptional-set slack bound into the large regular-set mass condition used by
the formal witness.
-/
theorem theorem4_regular_mass_from_exception_bound_statement
    {valueMass : Set ℝ → ℝ} {regularSet : Set ℝ} {delta epsilon : ℝ}
    (hpartition : valueMass regularSet + valueMass regularSetᶜ = 1)
    (hexception : valueMass regularSetᶜ ≤ delta)
    (hdelta : delta < epsilon) :
    1 - epsilon < valueMass regularSet :=
  theorem4_regular_mass_gt_of_exception_bound
    hpartition hexception hdelta

/--
Theorem 4 witness from the exceptional-set source form.

Source status: PG24 extended-model Theorem 4.  The source states that the
approximation holds except on a small value set; this row derives the existing
large-regular-set witness when the exceptional mass has strict slack.
-/
theorem theorem4_coalition_amplification_witness_from_exception_bound_statement
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
    theorem4_coalition_amplification_witness_statement
      coalition largeSubset affordProb valueMass regularSet
      epsilon effectiveSupply :=
  theorem4_coalitionAmplificationWitness_of_exception_bound
    hlarge hpartition hexception hdelta hclose

/--
Theorem 4 regular values from monotone interval endpoint estimates.

Source status: PG24 Theorem 4 proof works on a large regular value interval;
monotonicity plus a small endpoint gap makes every value in the interval close
to the low-endpoint effective supply.
-/
theorem theorem4_regular_values_close_from_monotone_endpoint_gap_statement
    {College : Type v} {affordProb : ℝ → Finset College → ℝ}
    {largeSubset : Finset College} {vLow vHigh epsilon : ℝ}
    (hp_mono : Monotone (fun v => affordProb v largeSubset))
    (hgap : affordProb vHigh largeSubset - affordProb vLow largeSubset < epsilon) :
    ∀ v ∈ Set.Icc vLow vHigh,
      |affordProb v largeSubset - affordProb vLow largeSubset| < epsilon :=
  theorem4_regular_values_close_of_monotone_endpoint_gap hp_mono hgap

/--
Theorem 4 coalition amplification witness from interval endpoint estimates.

Source status: PG24 Theorem 4 proof after choosing the regular interval; the
remaining source work is to prove large interval mass, monotonicity, and the
displayed endpoint gap from the cutoff model.
-/
theorem theorem4_coalition_amplification_witness_from_monotone_endpoint_gap_statement
    {College : Type v} {coalition largeSubset : Finset College}
    {affordProb : ℝ → Finset College → ℝ}
    {valueMass : Set ℝ → ℝ} {epsilon vLow vHigh : ℝ}
    (hlarge : CoalitionLargeSubset coalition largeSubset epsilon)
    (hmass : 1 - epsilon < valueMass (Set.Icc vLow vHigh))
    (hp_mono : Monotone (fun v => affordProb v largeSubset))
    (hgap : affordProb vHigh largeSubset - affordProb vLow largeSubset < epsilon) :
    theorem4_coalition_amplification_witness_statement
      coalition largeSubset affordProb valueMass (Set.Icc vLow vHigh)
      epsilon (affordProb vLow largeSubset) :=
  theorem4_coalitionAmplificationWitness_of_monotone_endpoint_gap
    hlarge hmass hp_mono hgap

/--
Theorem 4 source inequalities from the coalition witness.

Source status: PG24 extended-model Theorem 4 states existence of a large
subset, an effective supply, and a value set of mass greater than
`1 - epsilon` on which the approximation inequality holds.
-/
theorem theorem4_coalition_amplification_witness_source_clauses_statement
    {College : Type v} {coalition largeSubset : Finset College}
    {affordProb : ℝ → Finset College → ℝ}
    {valueMass : Set ℝ → ℝ} {regularSet : Set ℝ}
    {epsilon effectiveSupply : ℝ}
    (h :
      theorem4_coalition_amplification_witness_statement
        coalition largeSubset affordProb valueMass regularSet
        epsilon effectiveSupply) :
    CoalitionLargeSubset coalition largeSubset epsilon ∧
      1 - epsilon < valueMass regularSet ∧
      (∀ v ∈ regularSet, |affordProb v largeSubset - effectiveSupply| < epsilon) :=
  theorem4_coalitionAmplificationWitness_source_clauses h

/--
Theorem 4 coalition amplification, indexed source-shaped witness.

Source status: PG24 Theorem 4 for growing coalition size.  This row combines
the eventual large-subset condition, large regular-set mass, and approximation
inequality.
-/
abbrev theorem4_coalition_amplification_indexed_witness_statement
    {College : ℕ → Type v}
    (coalition largeSubset : ∀ C : ℕ, Finset (College C))
    (affordProb : ∀ C : ℕ, ℝ → Finset (College C) → ℝ)
    (valueMass : ∀ _ : ℕ, Set ℝ → ℝ)
    (regularSet : ∀ _ : ℕ, Set ℝ)
    (effectiveSupply : ℕ → ℝ)
    (epsilon : ℝ) : Prop :=
  Theorem4CoalitionAmplificationEpsilonWitnessConclusion
    coalition largeSubset affordProb valueMass regularSet effectiveSupply
    epsilon

/--
Theorem 4 coalition amplification, uniform source-shaped witness.

Source status: PG24 Theorem 4 quantifies over every sufficiently large
coalition/stable-matching instance.  This row exposes that uniform shape by
using an admissible-instance family at each market size.
-/
abbrev theorem4_coalition_amplification_uniform_witness_statement
    {College : ℕ → Type v} {Admissible : ℕ → Type u}
    (coalition largeSubset :
      ∀ C : ℕ, Admissible C → Finset (College C))
    (affordProb :
      ∀ C : ℕ, Admissible C → ℝ → Finset (College C) → ℝ)
    (valueMass : ∀ C : ℕ, Admissible C → Set ℝ → ℝ)
    (regularSet : ∀ C : ℕ, Admissible C → Set ℝ)
    (effectiveSupply : ∀ C : ℕ, Admissible C → ℝ)
    (epsilon : ℝ) : Prop :=
  Theorem4CoalitionAmplificationUniformWitnessConclusion
    coalition largeSubset affordProb valueMass regularSet effectiveSupply
    epsilon

/--
Theorem 4 uniform witness from interval endpoint estimates.

Source status: PG24 Theorem 4 proof after choosing each admissible instance's
large subset and regular interval.  Large-subset, interval-mass, monotonicity,
and endpoint-gap conditions are required uniformly over all admissible
instances at each sufficiently large market size.
-/
theorem theorem4_coalition_amplification_uniform_witness_from_monotone_endpoint_gap_statement
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
    theorem4_coalition_amplification_uniform_witness_statement
      coalition largeSubset affordProb valueMass
      (fun C a => Set.Icc (vLow C a) (vHigh C a))
      (fun C a => affordProb C a (vLow C a) (largeSubset C a))
      epsilon :=
  theorem4_coalitionAmplificationUniformWitness_of_eventual_monotone_endpoint_gap
    hlarge hmass hp_mono hgap

/--
Theorem 4 uniform witness for the concrete iid cutoff-affordance model.

Source status: PG24 Theorem 4 in the product-noise cutoff-market shape, with
the theorem's uniform quantification represented by an admissible-instance
family.  Value monotonicity on the regular interval is derived internally
from cutoff-affordance monotonicity.
-/
theorem theorem4_coalition_amplification_uniform_witness_from_iidProduct_cutoff_monotone_endpoint_gap_statement
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
          cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) (vHigh C a) (cutoff C a) -
            cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) (vLow C a) (cutoff C a) <
            epsilon) :
    theorem4_coalition_amplification_uniform_witness_statement
      coalition largeSubset
      (fun C : ℕ => fun a : Admissible C => fun v : ℝ =>
        fun active : Finset (Fin (C + 1)) =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            active v (cutoff C a))
      valueMass
      (fun C a => Set.Icc (vLow C a) (vHigh C a))
      (fun C a =>
        cutoffAffordanceProbability_statement
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (largeSubset C a) (vLow C a) (cutoff C a))
      epsilon :=
  theorem4_coalitionAmplificationUniformWitness_of_iidProduct_cutoff_monotone_endpoint_gap
    noiseLaw hlarge hmass hgap

/--
Theorem 4 uniform witness for selected stable matchings.

Source status: PG24 Theorem 4 is stated over stable matchings.  This row uses
the A-L supply-demand bridge to replace each selected stable matching by its
market-clearing cutoff, while keeping the theorem's uniform quantification
over admissible instances at each market size.
-/
theorem theorem4_coalition_amplification_uniform_witness_from_iidProduct_stable_cutoff_monotone_endpoint_gap_statement
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
            cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) (vHigh C a) (cutoffOut C P) -
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) (vLow C a) (cutoffOut C P) <
              epsilon) :
    theorem4_coalition_amplification_uniform_witness_statement
      coalition largeSubset
      (fun C : ℕ => fun a : Admissible C => fun v : ℝ =>
        fun active : Finset (Fin (C + 1)) =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            active v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2)))
      valueMass
      (fun C a => Set.Icc (vLow C a) (vHigh C a))
      (fun C a =>
        cutoffAffordanceProbability_statement
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (largeSubset C a) (vLow C a)
          (cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C a).1) (selected C a).2)))
      epsilon :=
  theorem4_coalitionAmplificationUniformWitness_of_iidProduct_stable_cutoff_monotone_endpoint_gap
    Mseq Iseq selected noiseLaw cutoffOut hlarge hmass hgap

/--
Theorem 4 uniform witness for selected stable matchings with selected-cutoff
endpoint gap.

Source status: narrowed PG24 Theorem 4 route.  The endpoint gap is required
only at the A-L selected cutoff associated with each admissible stable
matching instance, rather than at every market-clearing cutoff.
-/
theorem theorem4_coalition_amplification_uniform_witness_from_iidProduct_selected_stable_cutoff_monotone_endpoint_gap_statement
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
          cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) (vHigh C a)
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2)) -
            cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) (vLow C a)
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2)) <
            epsilon) :
    theorem4_coalition_amplification_uniform_witness_statement
      coalition largeSubset
      (fun C : ℕ => fun a : Admissible C => fun v : ℝ =>
        fun active : Finset (Fin (C + 1)) =>
          cutoffAffordanceProbability_statement
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            active v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2)))
      valueMass
      (fun C a => Set.Icc (vLow C a) (vHigh C a))
      (fun C a =>
        cutoffAffordanceProbability_statement
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (largeSubset C a) (vLow C a)
          (cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C a).1) (selected C a).2)))
      epsilon :=
  theorem4_coalitionAmplificationUniformWitness_of_iidProduct_selected_stable_cutoff_monotone_endpoint_gap
    Mseq Iseq selected noiseLaw cutoffOut hlarge hmass hgap

/--
Theorem 4 uniform selected-stable source clauses from endpoint estimates.

Source status: source-facing PG24 Theorem 4 route.  This exposes the uniform
large-subset, regular-mass, and regular-value approximation clauses directly
for every admissible stable matching instance, after the A-L cutoff bridge.
-/
theorem theorem4_coalition_amplification_uniform_source_clauses_from_iidProduct_stable_cutoff_monotone_endpoint_gap_statement
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
            cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) (vHigh C a) (cutoffOut C P) -
              cutoffAffordanceProbability_statement
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
          |cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) -
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) (vLow C a)
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))| < epsilon) :=
  theorem4_coalitionAmplificationUniformWitness_source_clauses_of_iidProduct_stable_cutoff_monotone_endpoint_gap
    Mseq Iseq selected noiseLaw cutoffOut hlarge hmass hgap

/--
Theorem 4 uniform selected-stable source clauses with selected-cutoff endpoint
gap.

Source status: narrowed PG24 Theorem 4 clause route.  The endpoint-gap input
is stated only at the A-L selected cutoff associated with each admissible
stable matching instance, rather than at every market-clearing cutoff.
-/
theorem theorem4_coalition_amplification_uniform_source_clauses_from_iidProduct_selected_stable_cutoff_monotone_endpoint_gap_statement
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
          cutoffAffordanceProbability_statement
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (largeSubset C a) (vHigh C a)
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2)) -
            cutoffAffordanceProbability_statement
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
          |cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) -
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) (vLow C a)
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))| < epsilon) :=
  theorem4_coalitionAmplificationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_monotone_endpoint_gap
    Mseq Iseq selected noiseLaw cutoffOut hlarge hmass hgap

/--
Theorem 4 uniform selected-stable source clauses from long-tail endpoint
estimates.

Source status: preferred uniform PG24 Theorem 4 route.  Long-tailed noise,
the diverging lower cutoff floor, and the high-endpoint `sigma / C` estimate
derive the endpoint gap internally; the conclusion is stated directly for
every admissible selected stable matching.
-/
theorem theorem4_coalition_amplification_uniform_source_clauses_from_iidProduct_stable_cutoff_upperTail_longTail_endpoint_estimates_strict_derived_statement
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
          |cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) -
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) vLow
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))| < tol) :=
  theorem4_coalitionAmplificationUniformWitness_source_clauses_of_iidProduct_stable_cutoff_upperTail_longTail_endpoint_estimates_strict_derived
    Mseq Iseq selected noiseLaw hlong cutoffOut hlarge hmass hv heps_pos
    heps_le_one hsigma_nonneg herror_lt hlower_atTop hcutoff_lower
    hhigh_le_sigma_div

/--
Theorem 4 uniform selected-stable source clauses from selected-cutoff
long-tail endpoint estimates.

Source status: narrowed PG24 Theorem 4 long-tail route.  The cutoff-floor and
high-tail endpoint estimates are required only at the A-L selected cutoff for
each admissible stable matching instance.
-/
theorem theorem4_coalition_amplification_uniform_source_clauses_from_iidProduct_selected_stable_cutoff_upperTail_longTail_endpoint_estimates_strict_derived_statement
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
          |cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) -
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) vLow
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))| < tol) :=
  theorem4_coalitionAmplificationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_upperTail_longTail_endpoint_estimates_strict_derived
    Mseq Iseq selected noiseLaw hlong cutoffOut hlarge hmass hv heps_pos
    heps_le_one hsigma_nonneg herror_lt hlower_atTop hcutoff_lower
    hhigh_le_sigma_div

/--
Theorem 4 uniform selected-stable source clauses from scalar-tail endpoint
estimates.

Source status: clean uniform PG24 Theorem 4 route.  The visible high-tail
input is the scalar upper-tail estimate at the lower cutoff floor; Lean
derives the per-large-college high-tail estimates using cutoff ordering and
upper-tail monotonicity.
-/
theorem theorem4_coalition_amplification_uniform_source_clauses_from_iidProduct_stable_cutoff_scalar_tail_upperTail_longTail_endpoint_estimates_strict_derived_statement
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
          |cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) -
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) vLow
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))| < tol) :=
  theorem4_coalitionAmplificationUniformWitness_source_clauses_of_iidProduct_stable_cutoff_scalar_tail_upperTail_longTail_endpoint_estimates_strict_derived
    Mseq Iseq selected noiseLaw hlong cutoffOut hlarge hmass hv heps_pos
    heps_le_one hsigma_nonneg herror_lt hlower_atTop hcutoff_lower
    hhigh_floor_le_sigma_div

/--
Theorem 4 uniform selected-stable source clauses from selected-cutoff
scalar-tail endpoint estimates.

Source status: narrowed clean PG24 Theorem 4 route.  The cutoff-floor
ordering is required only at the selected stable cutoff, and the high-tail
input is the scalar upper-tail estimate at the lower cutoff floor.
-/
theorem theorem4_coalition_amplification_uniform_source_clauses_from_iidProduct_selected_stable_cutoff_scalar_tail_upperTail_longTail_endpoint_estimates_strict_derived_statement
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
          |cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2)) -
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C a) vLow
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))| < tol) :=
  theorem4_coalitionAmplificationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_scalar_tail_upperTail_longTail_endpoint_estimates_strict_derived
    Mseq Iseq selected noiseLaw hlong cutoffOut hlarge hmass hv heps_pos
    heps_le_one hsigma_nonneg herror_lt hlower_atTop hcutoff_lower
    hhigh_floor_le_sigma_div

/--
Theorem 4 selected-stable existential source clauses.

Source status: paper-facing PG24 Theorem 4 shape.  The selected stable-cutoff
route proves the regular interval and restricted-affordance approximation;
this row packages the chosen `S'`, `C'`, and regular value set existentially.
-/
theorem theorem4_coalition_amplification_uniform_existential_source_clauses_from_iidProduct_selected_stable_cutoff_scalar_tail_upperTail_longTail_endpoint_estimates_strict_derived_statement
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
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ effectiveSupply' : ℝ,
        ∃ largeSubset' : Finset (Fin (C + 1)),
        ∃ regularSet' : Set ℝ,
          CoalitionLargeSubset (coalition C a) largeSubset' tol ∧
            1 - tol < valueMass C a regularSet' ∧
            (∀ v ∈ regularSet',
              |cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  largeSubset' v
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2)) -
                effectiveSupply'| < tol) := by
  have hclauses :=
    theorem4_coalition_amplification_uniform_source_clauses_from_iidProduct_selected_stable_cutoff_scalar_tail_upperTail_longTail_endpoint_estimates_strict_derived_statement
      Mseq Iseq selected noiseLaw hlong cutoffOut hlarge hmass hv
      heps_pos heps_le_one hsigma_nonneg herror_lt hlower_atTop
      hcutoff_lower hhigh_floor_le_sigma_div
  filter_upwards [hclauses.1, hclauses.2.1, hclauses.2.2] with
    C hlargeC hmassC hcloseC a
  refine
    ⟨cutoffAffordanceProbability_statement
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (largeSubset C a) vLow
        (cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C a).1) (selected C a).2)),
      largeSubset C a, Set.Icc vLow vHigh, hlargeC a, hmassC a, ?_⟩
  intro v hvmem
  exact hcloseC a v hvmem

/--
Theorem 4 selected-stable existential source clauses for the paper's sorted
suffix `C₂`.

Source status: preferred PG24 Theorem 4 route.  The chosen large subset is
the suffix after deleting the first `floor((tol/2)*(C+1))` sorted colleges.
Lean derives the large-subset certificate and turns the visible sorted-index
cutoff floor into the lower-cutoff premise used by the long-tail endpoint
estimate.  The long-tail tail-region condition is derived from the scalar
high-tail rate, so the remaining inputs are the source interval-mass and
scalar high-tail estimates.
-/
theorem theorem4_coalition_amplification_uniform_existential_source_clauses_from_iidProduct_selected_stable_cutoff_suffix_scalar_tail_upperTail_longTail_endpoint_estimates_strict_derived_statement
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
          definition_epsilonFloorSplitIndex_statement (tol / 2) n ≤
            (c : ℕ) →
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
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ effectiveSupply' : ℝ,
        ∃ largeSubset' : Finset (Fin (C + 1)),
        ∃ regularSet' : Set ℝ,
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' tol ∧
            1 - tol < valueMass C a regularSet' ∧
            (∀ v ∈ regularSet',
              |cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  largeSubset' v
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2)) -
                effectiveSupply'| < tol) := by
  have hclauses :=
    theorem4_coalitionAmplificationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_suffix_scalar_tail_upperTail_longTail_endpoint_estimates_from_high_tail_rate
      Mseq Iseq selected noiseLaw hlong cutoffOut htol_pos hmass hv
      heps_pos heps_le_one hsigma_nonneg herror_lt hcutoff_lower
      hhigh_floor_le_sigma_div
  filter_upwards [hclauses.1, hclauses.2.1, hclauses.2.2] with
    C hlargeC hmassC hcloseC a
  refine
    ⟨cutoffAffordanceProbability_statement
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (definition_indexSuffixLarge_statement
          (definition_epsilonFloorSplitIndex_statement (tol / 2) C) C)
        vLow
        (cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C a).1) (selected C a).2)),
      definition_indexSuffixLarge_statement
        (definition_epsilonFloorSplitIndex_statement (tol / 2) C) C,
      Set.Icc vLow vHigh, hlargeC a, hmassC a, ?_⟩
  intro v hvmem
  exact hcloseC a v hvmem

/--
Theorem 4 selected-stable source-assumption route for the paper's sorted
suffix `C₂`.

Source status: preferred PG24 Theorem 4 boundary.  The remaining non-derived
inputs are named source assumptions: regular-interval value mass, the sorted
suffix cutoff floor, and the scalar high-tail rate at that floor.
-/
theorem theorem4_coalition_amplification_uniform_existential_source_assumptions_from_iidProduct_selected_stable_cutoff_suffix_statement
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
      source_assumption_theorem4_regular_interval_mass
        valueMass (tol := tol) (vLow := vLow) (vHigh := vHigh))
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_nonneg : 0 ≤ sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol)
    (hcutoff_floor :
      source_assumption_theorem4_suffix_cutoff_floor
        Mseq Iseq selected cutoffOut (tol := tol) lowerCutoff)
    (hhigh_floor_rate :
      source_assumption_theorem4_high_tail_floor_rate
        (Admissible := Admissible) noiseLaw
        (sigma := sigma) (vHigh := vHigh) lowerCutoff) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ effectiveSupply' : ℝ,
        ∃ largeSubset' : Finset (Fin (C + 1)),
        ∃ regularSet' : Set ℝ,
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' tol ∧
            1 - tol < valueMass C a regularSet' ∧
            (∀ v ∈ regularSet',
              |cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  largeSubset' v
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2)) -
                effectiveSupply'| < tol) :=
  theorem4_coalition_amplification_uniform_existential_source_clauses_from_iidProduct_selected_stable_cutoff_suffix_scalar_tail_upperTail_longTail_endpoint_estimates_strict_derived_statement
    Mseq Iseq selected noiseLaw hlong cutoffOut htol_pos hmass hv
    heps_pos heps_le_one hsigma_nonneg herror_lt hcutoff_floor
    hhigh_floor_rate

/--
Theorem 4 selected-stable existential source model route.

Source status: same theorem as the source-assumption route, but with the
visible regular-interval mass, sorted-suffix cutoff-floor, and high-tail clauses
bundled into a single paper-facing source model record for audit.
-/
theorem theorem4_coalition_amplification_uniform_existential_source_model_from_iidProduct_selected_stable_cutoff_suffix_statement
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
    (H :
      Theorem4CoalitionAmplificationSourceModel
        Mseq Iseq selected noiseLaw cutoffOut valueMass
        tol sigma vLow vHigh lowerCutoff)
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_nonneg : 0 ≤ sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ effectiveSupply' : ℝ,
        ∃ largeSubset' : Finset (Fin (C + 1)),
        ∃ regularSet' : Set ℝ,
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' tol ∧
            1 - tol < valueMass C a regularSet' ∧
            (∀ v ∈ regularSet',
              |cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  largeSubset' v
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2)) -
                effectiveSupply'| < tol) :=
  theorem4_coalition_amplification_uniform_existential_source_assumptions_from_iidProduct_selected_stable_cutoff_suffix_statement
    Mseq Iseq selected noiseLaw hlong cutoffOut htol_pos
    H.regular_interval_mass hv heps_pos heps_le_one hsigma_nonneg
    herror_lt
    (source_assumption_theorem4_suffix_cutoff_floor_of_market
      (Iseq := Iseq) (selected := selected) H.cutoff_floor)
    H.high_tail_floor_rate

/--
Theorem 4 coalition amplification from the named PG24 source model package and
bundled A-L cutoff-market consequence certificates.

Source status: same active PG24 Theorem 4 route as above, but the
supply/demand bridge used to read selected stable matchings as cutoffs is
projected from the transparent A-L consequence package.
-/
theorem theorem4_coalition_amplification_uniform_existential_source_model_from_AL_cutoffMarketConsequences_iidProduct_selected_stable_cutoff_suffix_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Aseq :
      ∀ C : ℕ,
        AL16SupplyDemandMatching.CutoffMarketConsequences (Mseq C))
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
    (H :
      Theorem4CoalitionAmplificationSourceModel
        Mseq (fun C => (Aseq C).supplyDemand) selected noiseLaw cutoffOut
        valueMass tol sigma vLow vHigh lowerCutoff)
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_nonneg : 0 ≤ sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ effectiveSupply' : ℝ,
        ∃ largeSubset' : Finset (Fin (C + 1)),
        ∃ regularSet' : Set ℝ,
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' tol ∧
            1 - tol < valueMass C a regularSet' ∧
            (∀ v ∈ regularSet',
              |cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  largeSubset' v
                  (cutoffOut C
                    (((Aseq C).supplyDemand).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2)) -
                effectiveSupply'| < tol) :=
  theorem4_coalition_amplification_uniform_existential_source_model_from_iidProduct_selected_stable_cutoff_suffix_statement
    Mseq (fun C => (Aseq C).supplyDemand) selected noiseLaw hlong cutoffOut
    htol_pos H hv heps_pos heps_le_one hsigma_nonneg herror_lt

/--
Theorem 4 coalition amplification from the single explicit A-L source-model
boundary.

Source status: same active PG24 Theorem 4 route as the A-L consequence wrapper,
deriving each finite market's consequence package from the explicit AL
source-model record.
-/
theorem theorem4_coalition_amplification_uniform_existential_source_model_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (leCutoffSeq :
      ∀ C : ℕ, (Mseq C).Cutoff → (Mseq C).Cutoff → Prop)
    (HALseq :
      ∀ C : ℕ,
        AL16SupplyDemandMatching.CutoffMarketConsequenceSourceModel
          (Mseq C) (leCutoffSeq C))
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
    (H :
      Theorem4CoalitionAmplificationSourceModel
        Mseq
        (fun C =>
          (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
            (Mseq C) (HALseq C)).supplyDemand)
        selected noiseLaw cutoffOut valueMass tol sigma vLow vHigh
        lowerCutoff)
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_nonneg : 0 ≤ sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ effectiveSupply' : ℝ,
        ∃ largeSubset' : Finset (Fin (C + 1)),
        ∃ regularSet' : Set ℝ,
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' tol ∧
            1 - tol < valueMass C a regularSet' ∧
            (∀ v ∈ regularSet',
              |cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  largeSubset' v
                  (cutoffOut C
                    (SupplyDemandInterface.marketClearingCutoffOfStable
                      (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
                        (Mseq C) (HALseq C)).supplyDemand
                      (μ := (selected C a).1) (selected C a).2)) -
                effectiveSupply'| < tol) :=
  theorem4_coalition_amplification_uniform_existential_source_model_from_AL_cutoffMarketConsequences_iidProduct_selected_stable_cutoff_suffix_statement
    Mseq
    (fun C =>
      AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
        (Mseq C) (HALseq C))
    selected noiseLaw hlong cutoffOut htol_pos H hv heps_pos heps_le_one
    hsigma_nonneg herror_lt

/--
Theorem 4 coalition amplification from the A-L source model and an explicit
high-tail quantile floor.

Source status: active PG24 Theorem 4 route.  The visible source model assumes
regular interval mass and the market cutoff floor at a concrete high-tail
quantile floor.  Lean derives the scalar high-tail rate from the quantile
construction.
-/
theorem theorem4_coalition_amplification_uniform_existential_quantile_source_model_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (leCutoffSeq :
      ∀ C : ℕ, (Mseq C).Cutoff → (Mseq C).Cutoff → Prop)
    (HALseq :
      ∀ C : ℕ,
        AL16SupplyDemandMatching.CutoffMarketConsequenceSourceModel
          (Mseq C) (leCutoffSeq C))
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
    (H :
      Theorem4CoalitionAmplificationQuantileSourceModel
        Mseq
        (fun C =>
          (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
            (Mseq C) (HALseq C)).supplyDemand)
        selected noiseLaw cutoffOut valueMass tol sigma vLow vHigh)
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_pos : 0 < sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ effectiveSupply' : ℝ,
        ∃ largeSubset' : Finset (Fin (C + 1)),
        ∃ regularSet' : Set ℝ,
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' tol ∧
            1 - tol < valueMass C a regularSet' ∧
            (∀ v ∈ regularSet',
              |cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  largeSubset' v
                  (cutoffOut C
                    (SupplyDemandInterface.marketClearingCutoffOfStable
                      (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
                        (Mseq C) (HALseq C)).supplyDemand
                      (μ := (selected C a).1) (selected C a).2)) -
                effectiveSupply'| < tol) :=
  theorem4_coalition_amplification_uniform_existential_source_model_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
    Mseq leCutoffSeq HALseq selected noiseLaw hlong cutoffOut htol_pos
    (lowerCutoff :=
      fun C => vHigh + theorem4HighTailQuantile noiseLaw sigma C)
    { regular_interval_mass := H.regular_interval_mass
      cutoff_floor := H.cutoff_floor
      high_tail_floor_rate :=
        source_assumption_theorem4_high_tail_floor_rate_of_quantile_floor
          (Admissible := Admissible) noiseLaw hsigma_pos vHigh }
    hv heps_pos heps_le_one hsigma_pos.le herror_lt

/--
Theorem 4 coalition amplification from the A-L source model, the paper's
exceptional-set regularity form, and an explicit high-tail quantile floor.

Source status: strengthened active PG24 Theorem 4 route.  The visible source
model states that the complement of the chosen regular interval has mass at
most `delta < tol`; Lean derives the large regular-interval mass condition and
the scalar high-tail rate before applying the existing quantile route.
-/
theorem theorem4_coalition_amplification_uniform_existential_exception_quantile_source_model_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (leCutoffSeq :
      ∀ C : ℕ, (Mseq C).Cutoff → (Mseq C).Cutoff → Prop)
    (HALseq :
      ∀ C : ℕ,
        AL16SupplyDemandMatching.CutoffMarketConsequenceSourceModel
          (Mseq C) (leCutoffSeq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {valueMass : ∀ C : ℕ, Admissible C → Set ℝ → ℝ}
    {delta tol eps sigma vLow vHigh : ℝ} (htol_pos : 0 < tol)
    (H :
      Theorem4CoalitionAmplificationExceptionQuantileSourceModel
        Mseq
        (fun C =>
          (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
            (Mseq C) (HALseq C)).supplyDemand)
        selected noiseLaw cutoffOut valueMass delta tol sigma vLow vHigh)
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_pos : 0 < sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ effectiveSupply' : ℝ,
        ∃ largeSubset' : Finset (Fin (C + 1)),
        ∃ regularSet' : Set ℝ,
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' tol ∧
            1 - tol < valueMass C a regularSet' ∧
            (∀ v ∈ regularSet',
              |cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  largeSubset' v
                  (cutoffOut C
                    (SupplyDemandInterface.marketClearingCutoffOfStable
                      (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
                        (Mseq C) (HALseq C)).supplyDemand
                      (μ := (selected C a).1) (selected C a).2)) -
                effectiveSupply'| < tol) :=
  theorem4_coalition_amplification_uniform_existential_quantile_source_model_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
    Mseq leCutoffSeq HALseq selected noiseLaw hlong cutoffOut htol_pos
    { regular_interval_mass :=
        source_assumption_theorem4_regular_interval_mass_of_exception_bound
          H.regular_interval_exception
      cutoff_floor := H.cutoff_floor }
    hv heps_pos heps_le_one hsigma_pos herror_lt

/--
Theorem 4 coalition amplification from the shared PG24 sorted-suffix
cutoff-geometry certificate and the paper's exceptional-set regularity form.

Source status: strengthened active PG24 Theorem 4 route.  The regular-value
condition is supplied in the paper's exceptional-set form, the high-tail rate
is derived from the explicit quantile floor, and the remaining cutoff-order
fact is read from the same coalition suffix geometry certificate used by
Theorem 3.
-/
theorem theorem4_coalition_amplification_uniform_existential_exception_geometry_source_model_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (leCutoffSeq :
      ∀ C : ℕ, (Mseq C).Cutoff → (Mseq C).Cutoff → Prop)
    (HALseq :
      ∀ C : ℕ,
        AL16SupplyDemandMatching.CutoffMarketConsequenceSourceModel
          (Mseq C) (leCutoffSeq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {valueMass : ∀ C : ℕ, Admissible C → Set ℝ → ℝ}
    {delta epsilon tol eps sigma vLow vHigh : ℝ} (htol_pos : 0 < tol)
    {threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (hregular :
      source_assumption_theorem4_regular_interval_exception_bound
        valueMass (delta := delta) (tol := tol)
        (vLow := vLow) (vHigh := vHigh))
    (H :
      Theorem34CoalitionSuffixCutoffGeometrySourceModel
        Mseq
        (fun C =>
          (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
            (Mseq C) (HALseq C)).supplyDemand)
        selected noiseLaw cutoffOut epsilon tol sigma vHigh
        threshold upperCutoff)
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_pos : 0 < sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ effectiveSupply' : ℝ,
        ∃ largeSubset' : Finset (Fin (C + 1)),
        ∃ regularSet' : Set ℝ,
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' tol ∧
            1 - tol < valueMass C a regularSet' ∧
            (∀ v ∈ regularSet',
              |cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  largeSubset' v
                  (cutoffOut C
                    (SupplyDemandInterface.marketClearingCutoffOfStable
                      (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
                        (Mseq C) (HALseq C)).supplyDemand
                      (μ := (selected C a).1) (selected C a).2)) -
                effectiveSupply'| < tol) :=
  theorem4_coalition_amplification_uniform_existential_exception_quantile_source_model_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
    Mseq leCutoffSeq HALseq selected noiseLaw hlong cutoffOut htol_pos
    { regular_interval_exception := hregular
      cutoff_floor := H.theorem4_cutoff_floor }
    hv heps_pos heps_le_one hsigma_pos herror_lt

/--
Theorem 4 coalition amplification from a concrete regular-value probability
law, the paper's small exceptional-set bound, and the shared sorted-suffix
cutoff-geometry certificate.

Source status: strongest current PG24 Theorem 4 route.  The source supplies
only the regular-value probability laws, the exceptional-set mass bound
`mass(complement interval) ≤ delta < tol`, and the shared cutoff-geometry
certificate.  Lean derives the interval/complement partition, the large
regular-interval mass clause, and the scalar high-tail rate.
-/
theorem theorem4_coalition_amplification_uniform_existential_measure_exception_geometry_source_model_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (leCutoffSeq :
      ∀ C : ℕ, (Mseq C).Cutoff → (Mseq C).Cutoff → Prop)
    (HALseq :
      ∀ C : ℕ,
        AL16SupplyDemandMatching.CutoffMarketConsequenceSourceModel
          (Mseq C) (leCutoffSeq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (valueLaw :
      ∀ C : ℕ, Admissible C → Measure ℝ)
    {delta epsilon tol eps sigma vLow vHigh : ℝ} (htol_pos : 0 < tol)
    {threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (hdelta : delta < tol)
    (hvalue_probability :
      source_assumption_theorem4_regular_value_probability valueLaw)
    (hexception :
      source_assumption_theorem4_regular_interval_measure_exception_bound
        valueLaw (delta := delta) (vLow := vLow) (vHigh := vHigh))
    (H :
      Theorem34CoalitionSuffixCutoffGeometrySourceModel
        Mseq
        (fun C =>
          (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
            (Mseq C) (HALseq C)).supplyDemand)
        selected noiseLaw cutoffOut epsilon tol sigma vHigh
        threshold upperCutoff)
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_pos : 0 < sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ effectiveSupply' : ℝ,
        ∃ largeSubset' : Finset (Fin (C + 1)),
        ∃ regularSet' : Set ℝ,
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' tol ∧
            1 - tol < (valueLaw C a).real regularSet' ∧
            (∀ v ∈ regularSet',
              |cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  largeSubset' v
                  (cutoffOut C
                    (SupplyDemandInterface.marketClearingCutoffOfStable
                      (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
                        (Mseq C) (HALseq C)).supplyDemand
                      (μ := (selected C a).1) (selected C a).2)) -
                effectiveSupply'| < tol) :=
  theorem4_coalition_amplification_uniform_existential_exception_geometry_source_model_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
    (valueMass := fun C a S => (valueLaw C a).real S)
    Mseq leCutoffSeq HALseq selected noiseLaw hlong cutoffOut htol_pos
    (source_assumption_theorem4_regular_interval_exception_bound_of_measure
      hdelta hvalue_probability hexception)
    H hv heps_pos heps_le_one hsigma_pos herror_lt

/--
Theorem 4 coalition amplification from concrete probability laws and the
count-based shared PG24 sorted-suffix cutoff-geometry certificate.

Source status: strongest current PG24 Theorem 4 route.  The source supplies
the regular-value probability laws, the paper's exceptional-set mass bound,
sorted market-clearing cutoffs, and a low-count bound for below-floor cutoffs.
Lean derives the interval/complement partition, the large interval-mass clause,
the scalar high-tail rate, and the finite sorted-suffix cutoff floor.
-/
theorem theorem4_coalition_amplification_uniform_existential_measure_exception_count_geometry_source_model_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (leCutoffSeq :
      ∀ C : ℕ, (Mseq C).Cutoff → (Mseq C).Cutoff → Prop)
    (HALseq :
      ∀ C : ℕ,
        AL16SupplyDemandMatching.CutoffMarketConsequenceSourceModel
          (Mseq C) (leCutoffSeq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (valueLaw :
      ∀ C : ℕ, Admissible C → Measure ℝ)
    {delta epsilon tol eps sigma vLow vHigh : ℝ} (htol_pos : 0 < tol)
    {threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (hdelta : delta < tol)
    (hvalue_probability :
      source_assumption_theorem4_regular_value_probability valueLaw)
    (hexception :
      source_assumption_theorem4_regular_interval_measure_exception_bound
        valueLaw (delta := delta) (vLow := vLow) (vHigh := vHigh))
    (H :
      Theorem34CoalitionSuffixCutoffCountGeometrySourceModel
        Mseq
        (fun C =>
          (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
            (Mseq C) (HALseq C)).supplyDemand)
        selected noiseLaw cutoffOut epsilon tol sigma vHigh
        threshold upperCutoff)
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_pos : 0 < sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ effectiveSupply' : ℝ,
        ∃ largeSubset' : Finset (Fin (C + 1)),
        ∃ regularSet' : Set ℝ,
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' tol ∧
            1 - tol < (valueLaw C a).real regularSet' ∧
            (∀ v ∈ regularSet',
              |cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  largeSubset' v
                  (cutoffOut C
                    (SupplyDemandInterface.marketClearingCutoffOfStable
                      (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
                        (Mseq C) (HALseq C)).supplyDemand
                      (μ := (selected C a).1) (selected C a).2)) -
                effectiveSupply'| < tol) :=
  theorem4_coalition_amplification_uniform_existential_measure_exception_geometry_source_model_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
    Mseq leCutoffSeq HALseq selected noiseLaw hlong cutoffOut valueLaw
    htol_pos hdelta hvalue_probability hexception
    (theorem34_coalition_suffix_cutoff_geometry_of_sorted_low_count H)
    hv heps_pos heps_le_one hsigma_pos herror_lt

/--
Theorem 4 coalition amplification from concrete probability laws and the
capacity-contradiction shared PG24 cutoff-geometry certificate.

Source status: stronger Theorem 4 route.  The source constructs the high-mass
matched event that rules out too many low sorted cutoffs; Lean derives the
low-count bound from A-L exact fill and then continues through the existing
measure-exception and sorted-suffix geometry proof.
-/
theorem theorem4_coalition_amplification_uniform_existential_measure_exception_capacity_contradiction_source_model_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (leCutoffSeq :
      ∀ C : ℕ, (Mseq C).Cutoff → (Mseq C).Cutoff → Prop)
    (HALseq :
      ∀ C : ℕ,
        AL16SupplyDemandMatching.CutoffMarketConsequenceSourceModel
          (Mseq C) (leCutoffSeq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    (valueLaw :
      ∀ C : ℕ, Admissible C → Measure ℝ)
    {totalSupply delta epsilon tol eps sigma vLow vHigh : ℝ}
    (htol_pos : 0 < tol)
    {threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (hdelta : delta < tol)
    (hvalue_probability :
      source_assumption_theorem4_regular_value_probability valueLaw)
    (hexception :
      source_assumption_theorem4_regular_interval_measure_exception_bound
        valueLaw (delta := delta) (vLow := vLow) (vHigh := vHigh))
    (H :
      Theorem34CoalitionSuffixCutoffCapacityContradictionSourceModel
        Mseq
        (fun C =>
          (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
            (Mseq C) (HALseq C)).supplyDemand)
        selected noiseLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege
        totalSupply epsilon tol sigma vHigh threshold upperCutoff)
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_pos : 0 < sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ effectiveSupply' : ℝ,
        ∃ largeSubset' : Finset (Fin (C + 1)),
        ∃ regularSet' : Set ℝ,
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' tol ∧
            1 - tol < (valueLaw C a).real regularSet' ∧
            (∀ v ∈ regularSet',
              |cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  largeSubset' v
                  (cutoffOut C
                    (SupplyDemandInterface.marketClearingCutoffOfStable
                      (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
                        (Mseq C) (HALseq C)).supplyDemand
                      (μ := (selected C a).1) (selected C a).2)) -
                effectiveSupply'| < tol) :=
  theorem4_coalition_amplification_uniform_existential_measure_exception_count_geometry_source_model_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
    Mseq leCutoffSeq HALseq selected noiseLaw hlong cutoffOut
    valueLaw htol_pos hdelta hvalue_probability hexception
    (theorem34_coalition_suffix_cutoff_count_geometry_of_capacity_contradiction
      (Filter.Eventually.of_forall (fun C => by
        intro P hP c
        exact (HALseq C).exact_fill P hP c))
      H)
    hv heps_pos heps_le_one hsigma_pos herror_lt

/--
Theorem 4 coalition amplification from concrete probability laws and the
integrated-capacity shared PG24 cutoff-geometry certificate.

Source status: strongest current Theorem 4 route.  The source states the
Lemma 11-style value-integrated low-cutoff affordability bound and the
outcome-model bridge from that integral to matched outcomes; Lean derives the
capacity contradiction, the low-count bound, the sorted-suffix cutoff floor,
and then the regular-value measure-exception conclusion.
-/
theorem theorem4_coalition_amplification_uniform_existential_measure_exception_integrated_capacity_source_model_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (leCutoffSeq :
      ∀ C : ℕ, (Mseq C).Cutoff → (Mseq C).Cutoff → Prop)
    (HALseq :
      ∀ C : ℕ,
        AL16SupplyDemandMatching.CutoffMarketConsequenceSourceModel
          (Mseq C) (leCutoffSeq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (valueLaw :
      ∀ C : ℕ, Admissible C → Measure ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    {totalSupply delta epsilon tol eps sigma vLow vHigh : ℝ}
    (htol_pos : 0 < tol)
    {threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (hdelta : delta < tol)
    (hexception :
      source_assumption_theorem4_regular_interval_measure_exception_bound
        valueLaw (delta := delta) (vLow := vLow) (vHigh := vHigh))
    (H :
      Theorem34CoalitionSuffixCutoffIntegratedCapacitySourceModel
        Mseq
        (fun C =>
          (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
            (Mseq C) (HALseq C)).supplyDemand)
        selected noiseLaw cutoffOut valueLaw OutcomeSeq outcomeLaw
        chosenCollege totalSupply epsilon tol sigma vHigh
        threshold upperCutoff)
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_pos : 0 < sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ effectiveSupply' : ℝ,
        ∃ largeSubset' : Finset (Fin (C + 1)),
        ∃ regularSet' : Set ℝ,
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' tol ∧
            1 - tol < (valueLaw C a).real regularSet' ∧
            (∀ v ∈ regularSet',
              |cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  largeSubset' v
                  (cutoffOut C
                    (SupplyDemandInterface.marketClearingCutoffOfStable
                      (AL16SupplyDemandMatching.cutoffMarketConsequences_of_source_model
                        (Mseq C) (HALseq C)).supplyDemand
                      (μ := (selected C a).1) (selected C a).2)) -
                effectiveSupply'| < tol) :=
  theorem4_coalition_amplification_uniform_existential_measure_exception_capacity_contradiction_source_model_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
    Mseq leCutoffSeq HALseq selected noiseLaw hlong cutoffOut
    OutcomeSeq outcomeLaw chosenCollege valueLaw htol_pos hdelta
    H.value_probability hexception
    (theorem34_coalition_suffix_cutoff_capacity_contradiction_of_integrated_capacity H)
    hv heps_pos heps_le_one hsigma_pos herror_lt

/--
Theorem 4 coalition amplification from concrete probability laws and the
selected-stable integrated-capacity PG24 cutoff-geometry certificate.

Source status: selected-stable strengthening of the integrated-capacity route.
The paper-facing statement lists each market/outcome identity and the remaining
Theorem 4 floor estimate directly.  Lean derives finite mass, the high-mass
contradiction, the low-count bound, the sorted-suffix cutoff floor, the
interval/complement partition, and the scalar high-tail rate without requiring
the Theorem 3 floor or upper-ceiling estimates.
-/
theorem theorem4_coalition_amplification_uniform_existential_measure_exception_selected_stable_integrated_capacity_source_model_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
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
    (valueLaw :
      ∀ C : ℕ, Admissible C → Measure ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    {totalSupply delta tol eps sigma vLow vHigh : ℝ}
    (htol_pos : 0 < tol)
    (hdelta : delta < tol)
    (hexception :
      source_assumption_theorem4_regular_interval_measure_exception_bound
        valueLaw (delta := delta) (vLow := vLow) (vHigh := vHigh))
    (outcome_probability :
      source_assumption_market_outcome_probability Mseq OutcomeSeq outcomeLaw)
    (choice_mass_eq_aggregateDemand :
      source_assumption_market_choice_mass_eq_aggregateDemand
        Mseq OutcomeSeq outcomeLaw chosenCollege)
    (capacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (value_probability :
      source_assumption_market_value_probability valueLaw)
    (selected_cutoff_sorted :
      source_assumption_selected_stable_cutoff_index_sorted
        Mseq Iseq selected cutoffOut)
    (integrated_affordance_event_bridge :
      source_assumption_market_integrated_affordance_event_bridge
        Mseq noiseLaw valueLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege)
    (theorem4_floor_pow_integral_exceeds_supply :
      source_assumption_selected_stable_low_cutoff_floor_pow_integral_exceeds_supply
        Mseq Iseq noiseLaw selected valueLaw cutoffOut
        (fun C : ℕ => epsilonFloorSplitIndex (tol / 2) C)
        (fun C (_a : Admissible C) =>
          vHigh + theorem4HighTailQuantile noiseLaw sigma C)
        totalSupply)
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_pos : 0 < sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ effectiveSupply' : ℝ,
        ∃ largeSubset' : Finset (Fin (C + 1)),
        ∃ regularSet' : Set ℝ,
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' tol ∧
            1 - tol < (valueLaw C a).real regularSet' ∧
            (∀ v ∈ regularSet',
              |cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  largeSubset' v
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2)) -
                effectiveSupply'| < tol) := by
  have hcapacity_clear :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c : Fin (C + 1),
          (Mseq C).aggregateDemand
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2) c =
            (Mseq C).capacity c := by
    exact Filter.Eventually.of_forall (fun C => by
      intro a c
      exact
        MarketClearingCapacityInterface.marketClearingCutoffOfStable_aggregateDemand_eq_capacity
          (Kseq C) (Iseq C) (selected C a).2 c)
  have hselected_sorted :
      source_assumption_selected_stable_cutoff_index_sorted
        Mseq Iseq selected cutoffOut :=
    selected_cutoff_sorted
  have htheorem4_low_count :
      source_assumption_theorem4_suffix_selected_stable_low_cutoff_count
        Mseq Iseq selected cutoffOut (tol := tol)
        (fun C => vHigh + theorem4HighTailQuantile noiseLaw sigma C) :=
    source_assumption_theorem4_suffix_selected_stable_low_cutoff_count_of_capacity_contradiction
      (source_assumption_selected_stable_outcome_finite_of_probability
        (source_assumption_selected_stable_outcome_probability_of_market
          outcome_probability))
      (source_assumption_selected_stable_choice_mass_eq_aggregateDemand_of_market
        choice_mass_eq_aggregateDemand)
      hcapacity_clear
      capacity_sum
      (source_assumption_selected_stable_low_cutoff_capacity_contradiction_of_integrated_affordance_event_bridge
        (source_assumption_selected_stable_low_cutoff_integral_exceeds_supply_of_floor_pow_integral
          (source_assumption_market_value_finite_of_probability
            value_probability)
          theorem4_floor_pow_integral_exceeds_supply)
        (source_assumption_selected_stable_integrated_affordance_event_bridge_of_market
          integrated_affordance_event_bridge))
  have htheorem4_cutoff_floor :
      source_assumption_theorem4_suffix_cutoff_floor
        Mseq Iseq selected cutoffOut (tol := tol)
        (fun C => vHigh + theorem4HighTailQuantile noiseLaw sigma C) :=
    source_assumption_theorem4_suffix_cutoff_floor_of_selected_stable_sorted_low_count
      hselected_sorted htheorem4_low_count
  exact
    theorem4_coalition_amplification_uniform_existential_source_assumptions_from_iidProduct_selected_stable_cutoff_suffix_statement
      (valueMass := fun C a S => (valueLaw C a).real S)
      Mseq Iseq selected noiseLaw hlong cutoffOut htol_pos
      (source_assumption_theorem4_regular_interval_mass_of_exception_bound
        (source_assumption_theorem4_regular_interval_exception_bound_of_measure
          hdelta value_probability hexception))
      hv heps_pos heps_le_one hsigma_pos.le herror_lt
      htheorem4_cutoff_floor
      (source_assumption_theorem4_high_tail_floor_rate_of_quantile_floor
        (Admissible := Admissible) noiseLaw hsigma_pos vHigh)

/--
Theorem 4 through the pointwise low-CDF power/capacity route.

Source status: active audited repair surface for the coalition-amplification
route.  It keeps the regular value-mass and long-tail endpoint assumptions
visible, while exposing the remaining low-cutoff capacity estimate as the
split-index strict upper-tail crossing inequality at the explicit high-tail
quantile floor.  Lean derives the lower-CDF product form, the full pointwise
low-cutoff-set capacity premise, and selected-stable low-count from that
premise plus the
pointwise outcome-event bridge, then uses the semantic non-low cutoff block as
the large coalition.  This avoids both the integrated floor-power premise and
the selected-stable sorted-relabeling premise for Theorem 4.
-/
theorem theorem4_coalition_amplification_uniform_existential_measure_exception_selected_stable_pointwise_capacity_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
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
    (valueLaw :
      ∀ C : ℕ, Admissible C → Measure ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    {totalSupply delta tol eps sigma vLow vHigh : ℝ}
    (htol_pos : 0 < tol)
    (hdelta : delta < tol)
    (hexception :
      source_assumption_theorem4_regular_interval_measure_exception_bound
        valueLaw (delta := delta) (vLow := vLow) (vHigh := vHigh))
    (outcome_probability :
      source_assumption_market_outcome_probability Mseq OutcomeSeq outcomeLaw)
    (choice_mass_eq_aggregateDemand :
      source_assumption_market_choice_mass_eq_aggregateDemand
        Mseq OutcomeSeq outcomeLaw chosenCollege)
    (capacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (value_probability :
      source_assumption_market_value_probability valueLaw)
    (affordance_event_bridge :
      source_assumption_market_affordance_event_bridge
        Mseq noiseLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege)
    (theorem4_low_cutoff_upper_tail_split_pow_exceeds_supply :
      source_assumption_market_low_cutoff_upper_tail_split_pow_exceeds_supply
        Mseq noiseLaw
        (fun C : ℕ => epsilonFloorSplitIndex (tol / 2) C)
        (fun C (_a : Admissible C) =>
          vHigh + theorem4HighTailQuantile noiseLaw sigma C)
        (fun _C (_a : Admissible _C) => vHigh)
        totalSupply)
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_pos : 0 < sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ effectiveSupply' : ℝ,
        ∃ largeSubset' : Finset (Fin (C + 1)),
        ∃ regularSet' : Set ℝ,
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' tol ∧
            1 - tol < (valueLaw C a).real regularSet' ∧
            (∀ v ∈ regularSet',
              |cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  largeSubset' v
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2)) -
                effectiveSupply'| < tol) := by
  have hcapacity_clear :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c : Fin (C + 1),
          (Mseq C).aggregateDemand
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2) c =
            (Mseq C).capacity c := by
    exact Filter.Eventually.of_forall (fun C => by
      intro a c
      exact
        MarketClearingCapacityInterface.marketClearingCutoffOfStable_aggregateDemand_eq_capacity
          (Kseq C) (Iseq C) (selected C a).2 c)
  have htheorem4_low_count :
      source_assumption_theorem4_suffix_selected_stable_low_cutoff_count
        Mseq Iseq selected cutoffOut (tol := tol)
        (fun C => vHigh + theorem4HighTailQuantile noiseLaw sigma C) :=
    source_assumption_theorem4_suffix_selected_stable_low_cutoff_count_of_capacity_contradiction
      (source_assumption_selected_stable_outcome_finite_of_probability
        (source_assumption_selected_stable_outcome_probability_of_market
          outcome_probability))
      (source_assumption_selected_stable_choice_mass_eq_aggregateDemand_of_market
        choice_mass_eq_aggregateDemand)
      hcapacity_clear
      capacity_sum
      (source_assumption_selected_stable_low_cutoff_capacity_contradiction_of_market_pow_affordance_event_bridge
        (source_assumption_market_low_cutoff_pow_exceeds_supply_of_split_pow
          (cutoffOut := cutoffOut)
          (source_assumption_market_low_cutoff_split_pow_exceeds_supply_of_upper_tail_split_pow
            theorem4_low_cutoff_upper_tail_split_pow_exceeds_supply))
        affordance_event_bridge)
  have hregular_mass :
      source_assumption_theorem4_regular_interval_mass
        (fun C a S => (valueLaw C a).real S)
        (tol := tol) (vLow := vLow) (vHigh := vHigh) :=
    source_assumption_theorem4_regular_interval_mass_of_exception_bound
      (source_assumption_theorem4_regular_interval_exception_bound_of_measure
        hdelta value_probability hexception)
  have hclauses :=
    theorem4_coalitionAmplificationUniformWitness_source_clauses_of_iidProduct_selected_stable_cutoff_nonLow_scalar_tail_upperTail_longTail_endpoint_estimates_from_high_tail_rate
      (valueMass := fun C a S => (valueLaw C a).real S)
      Mseq Iseq selected noiseLaw hlong cutoffOut htol_pos
      hregular_mass hv heps_pos heps_le_one hsigma_pos.le herror_lt
      htheorem4_low_count
      (source_assumption_theorem4_high_tail_floor_rate_of_quantile_floor
        (Admissible := Admissible) noiseLaw hsigma_pos vHigh)
  filter_upwards [hclauses.1, hclauses.2.1, hclauses.2.2] with
    C hlargeC hmassC hcloseC a
  refine
    ⟨cutoffAffordanceProbability_statement
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (nonLowCutoffIndexSet
          (cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C a).1) (selected C a).2))
          (vHigh + theorem4HighTailQuantile noiseLaw sigma C))
        vLow
        (cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C a).1) (selected C a).2)),
      nonLowCutoffIndexSet
        (cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C a).1) (selected C a).2))
        (vHigh + theorem4HighTailQuantile noiseLaw sigma C),
      Set.Icc vLow vHigh, hlargeC a, hmassC a, ?_⟩
  intro v hvmem
  exact hcloseC a v hvmem

/--
Theorem 4 through the pointwise-capacity route with the paper's fixed coalition
value law.  The extended model fixes one probability measure `η` for a
`(D, η)`-coalition.  Thus the regular-interval mass condition is stated for
that one law, rather than as a uniform interval-exception premise for an
arbitrary family of value laws.

The remaining visible proof obligation is the split-index strict upper-tail
capacity estimate at the selected interval endpoint.  The checked tightness
lemma in `Assumptions.lean` proves that suitable endpoints exist for `η`, but
it cannot select them independently of this endpoint-indexed capacity proof.
-/
theorem theorem4_coalition_amplification_uniform_existential_fixed_value_law_selected_stable_pointwise_capacity_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
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
    (valueLaw :
      ∀ C : ℕ, Admissible C → Measure ℝ)
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (value_law_eq_eta :
      source_assumption_theorem4_value_law_eq_eta valueLaw η)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    {totalSupply delta tol eps sigma vLow vHigh : ℝ}
    (htol_pos : 0 < tol)
    (hdelta : delta < tol)
    (eta_exception :
      source_assumption_theorem4_eta_regular_interval_exception_bound
        η (delta := delta) (vLow := vLow) (vHigh := vHigh))
    (outcome_probability :
      source_assumption_market_outcome_probability Mseq OutcomeSeq outcomeLaw)
    (choice_mass_eq_aggregateDemand :
      source_assumption_market_choice_mass_eq_aggregateDemand
        Mseq OutcomeSeq outcomeLaw chosenCollege)
    (capacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (affordance_event_bridge :
      source_assumption_market_affordance_event_bridge
        Mseq noiseLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege)
    (theorem4_low_cutoff_upper_tail_split_pow_exceeds_supply :
      source_assumption_market_low_cutoff_upper_tail_split_pow_exceeds_supply
        Mseq noiseLaw
        (fun C : ℕ => epsilonFloorSplitIndex (tol / 2) C)
        (fun C (_a : Admissible C) =>
          vHigh + theorem4HighTailQuantile noiseLaw sigma C)
        (fun _C (_a : Admissible _C) => vHigh)
        totalSupply)
    (hv : vLow < vHigh) (heps_pos : 0 < eps) (heps_le_one : eps ≤ 1)
    (hsigma_pos : 0 < sigma)
    (herror_lt : 1 - Real.exp (-(2 * eps * sigma)) < tol) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ effectiveSupply' : ℝ,
        ∃ largeSubset' : Finset (Fin (C + 1)),
        ∃ regularSet' : Set ℝ,
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' tol ∧
            1 - tol < (valueLaw C a).real regularSet' ∧
            (∀ v ∈ regularSet',
              |cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  largeSubset' v
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2)) -
                effectiveSupply'| < tol) := by
  have hexception :
      source_assumption_theorem4_regular_interval_measure_exception_bound
        valueLaw (delta := delta) (vLow := vLow) (vHigh := vHigh) :=
    source_assumption_theorem4_regular_interval_measure_exception_bound_of_value_law_eq_eta
      η value_law_eq_eta eta_exception
  have value_probability : source_assumption_market_value_probability valueLaw :=
    source_assumption_market_value_probability_of_theorem4_value_law_eq_eta
      η value_law_eq_eta
  exact
    theorem4_coalition_amplification_uniform_existential_measure_exception_selected_stable_pointwise_capacity_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
      Mseq Iseq Kseq selected noiseLaw hlong cutoffOut valueLaw
      OutcomeSeq outcomeLaw chosenCollege htol_pos hdelta hexception
      outcome_probability choice_mass_eq_aggregateDemand capacity_sum
      value_probability affordance_event_bridge
      theorem4_low_cutoff_upper_tail_split_pow_exceeds_supply hv heps_pos
      heps_le_one hsigma_pos herror_lt

/--
Theorem 4 with its capacity and endpoint-error parameters selected internally.

The source model fixes total coalition capacity strictly below the unit mass of
students (`model.tex:12-15`).  Long-tailedness then supplies a slackened
strict-tail lower bound at the explicit quantile, and Lean chooses the tail
scale large enough to make the split-index capacity crossing exceed that
fixed supply.  The regular interval is selected from tightness of the one
fixed coalition value law `eta`.

No nonatomicity, sorted-relabeling, endpoint-specific capacity premise, or
family-uniform tightness premise is assumed here.
-/
theorem theorem4_coalition_amplification_uniform_existential_fixed_value_law_selected_stable_resolved_capacity_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
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
    (valueLaw :
      ∀ C : ℕ, Admissible C → Measure ℝ)
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (value_law_eq_eta :
      source_assumption_theorem4_value_law_eq_eta valueLaw η)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    {totalSupply tol : ℝ}
    (htol_pos : 0 < tol) (htotalSupply_lt_one : totalSupply < 1)
    (outcome_probability :
      source_assumption_market_outcome_probability Mseq OutcomeSeq outcomeLaw)
    (choice_mass_eq_aggregateDemand :
      source_assumption_market_choice_mass_eq_aggregateDemand
        Mseq OutcomeSeq outcomeLaw chosenCollege)
    (capacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (affordance_event_bridge :
      source_assumption_market_affordance_event_bridge
        Mseq noiseLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        ∃ effectiveSupply' : ℝ,
        ∃ largeSubset' : Finset (Fin (C + 1)),
        ∃ regularSet' : Set ℝ,
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset' tol ∧
            1 - tol < (valueLaw C a).real regularSet' ∧
            (∀ v ∈ regularSet',
              |cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  largeSubset' v
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2)) -
                effectiveSupply'| < tol) := by
  have hdelta_pos : 0 < tol / 2 := by linarith
  have hdelta_lt : tol / 2 < tol := by linarith
  rcases exists_regular_interval_measure_compl_le_of_probability η hdelta_pos with
    ⟨vLow, vHigh, hv, heta_exception⟩
  rcases exists_theorem4_highTailQuantile_capacity_witness_of_longTailed
    (Admissible := Admissible) Mseq noiseLaw hlong
    (tol := tol) (totalSupply := totalSupply) (vHigh := vHigh)
    htol_pos htotalSupply_lt_one with
    ⟨sigma, tau, eps, hsigma_pos, _htau_pos, heps_pos, heps_le_one,
      _htau_eq, _hstatic_gap, herror_lt, hcapacity⟩
  exact
    theorem4_coalition_amplification_uniform_existential_fixed_value_law_selected_stable_pointwise_capacity_from_AL_source_model_iidProduct_selected_stable_cutoff_suffix_statement
      (totalSupply := totalSupply) (delta := tol / 2) (tol := tol)
      (eps := eps) (sigma := sigma) (vLow := vLow) (vHigh := vHigh)
      Mseq Iseq Kseq selected noiseLaw hlong cutoffOut valueLaw η
      value_law_eq_eta OutcomeSeq outcomeLaw chosenCollege
      htol_pos hdelta_lt heta_exception outcome_probability
      choice_mass_eq_aggregateDemand capacity_sum affordance_event_bridge
      hcapacity hv heps_pos heps_le_one hsigma_pos herror_lt

/--
Theorem 4 indexed witness from eventual interval endpoint estimates.

Source status: PG24 proof of Theorem 4 after choosing the large subset and
regular interval.  Monotonicity and a small endpoint gap imply the source
approximation inequality throughout the interval.
-/
theorem theorem4_coalition_amplification_indexed_witness_from_eventual_endpoint_gap_statement
    {College : ℕ → Type v}
    {coalition largeSubset : ∀ C : ℕ, Finset (College C)}
    {affordProb : ∀ C : ℕ, ℝ → Finset (College C) → ℝ}
    {valueMass : ∀ _ : ℕ, Set ℝ → ℝ}
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
    theorem4_coalition_amplification_indexed_witness_statement
      coalition largeSubset affordProb valueMass
      (fun C => Set.Icc (vLow C) (vHigh C))
      (fun C => affordProb C (vLow C) (largeSubset C))
      epsilon :=
  theorem4_coalitionAmplificationEpsilonWitness_of_eventual_monotone_endpoint_gap
    hlarge hmass hp_mono hgap

/--
Theorem 4 indexed witness from long-tailed endpoint estimates.

Source status: PG24 Theorem 4 proof route through the long-tailed
`lt-approx-F2` estimate.  The endpoint gap on the large subset is derived
from long-tailedness, cutoff lower bounds, and high-value crossing bounds.
-/
theorem theorem4_coalition_amplification_indexed_witness_from_longTail_endpoint_estimates_statement
    {survival : ℝ → ℝ} (hlong : LongTailedSurvival survival)
    {coalition largeSubset : ∀ C : ℕ, Finset (Fin (C + 1))}
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ}
    {valueMass : ∀ _ : ℕ, Set ℝ → ℝ}
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
    theorem4_coalition_amplification_indexed_witness_statement
      coalition largeSubset
      (fun C : ℕ => fun v : ℝ => fun active : Finset (Fin (C + 1)) =>
        independentAffordanceProbability
          active (fun c => survival (cutoff C c - v)))
      valueMass
      (fun _C : ℕ => Set.Icc vLow vHigh)
      (fun C : ℕ =>
        independentAffordanceProbability
          (largeSubset C) (fun c => survival (cutoff C c - vLow)))
      tol :=
  theorem4_coalitionAmplificationEpsilonWitness_of_longTail_endpoint_estimates
    hlong hlarge hmass hp_mono hv heps_pos heps_le_one hsigma_nonneg
    herror_lt hlower_atTop hcutoff_lower hhigh_pos hhigh_le_sigma_div
    hlow_failure_pos

/--
Theorem 4 indexed witness from survival-function long-tailed endpoint
estimates.

Source status: PG24 Theorem 4 in the source survival-probability shape.  The
regular-interval value monotonicity is derived from antitonicity of the
survival function rather than supplied as an abstract premise.
-/
theorem theorem4_coalition_amplification_indexed_witness_from_survival_longTail_endpoint_estimates_statement
    {survival : ℝ → ℝ} (hlong : LongTailedSurvival survival)
    {coalition largeSubset : ∀ C : ℕ, Finset (Fin (C + 1))}
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ}
    {valueMass : ∀ _ : ℕ, Set ℝ → ℝ}
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
    theorem4_coalition_amplification_indexed_witness_statement
      coalition largeSubset
      (fun C : ℕ => fun v : ℝ => fun active : Finset (Fin (C + 1)) =>
        independentAffordanceProbability
          active (fun c => survival (cutoff C c - v)))
      valueMass
      (fun _C : ℕ => Set.Icc vLow vHigh)
      (fun C : ℕ =>
        independentAffordanceProbability
          (largeSubset C) (fun c => survival (cutoff C c - vLow)))
      tol :=
  theorem4_coalitionAmplificationEpsilonWitness_of_survival_longTail_endpoint_estimates
    hlong hsurvival_antitone hlarge hmass hv heps_pos heps_le_one
    hsigma_nonneg herror_lt hlower_atTop hcutoff_lower hhigh_pos
    hhigh_le_sigma_div hlow_failure_pos hprob_le_one

/--
Theorem 4 indexed witness for concrete upper-tail affordance probabilities.

Source status: PG24 Theorem 4 in the real-noise-law shape.  The source keeps
the long-tail law and endpoint estimates; antitonicity and probability upper
bounds for `Pr[X > x]` are derived in the library.
-/
theorem theorem4_coalition_amplification_indexed_witness_from_upperTail_longTail_endpoint_estimates_statement
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {coalition largeSubset : ∀ C : ℕ, Finset (Fin (C + 1))}
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ}
    {valueMass : ∀ _ : ℕ, Set ℝ → ℝ}
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
    theorem4_coalition_amplification_indexed_witness_statement
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
      tol :=
  theorem4_coalitionAmplificationEpsilonWitness_of_upperTail_longTail_endpoint_estimates
    noiseLaw hlong hlarge hmass hv heps_pos heps_le_one hsigma_nonneg
    herror_lt hlower_atTop hcutoff_lower hhigh_pos hhigh_le_sigma_div
    hlow_failure_pos

/--
Theorem 4 indexed witness for concrete upper-tail affordance probabilities,
deriving strict probability side conditions internally.

Source status: PG24 Theorem 4 in the real-noise-law shape.  The source keeps
the long-tail law, large-set/regular-interval facts, diverging cutoff floor,
and high-endpoint `sigma/C` estimate; Lean derives positive high-tail mass and
positive low-endpoint failure probability.
-/
theorem theorem4_coalition_amplification_indexed_witness_from_upperTail_longTail_endpoint_estimates_strict_derived_statement
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {coalition largeSubset : ∀ C : ℕ, Finset (Fin (C + 1))}
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ}
    {valueMass : ∀ _ : ℕ, Set ℝ → ℝ}
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
    theorem4_coalition_amplification_indexed_witness_statement
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
      tol :=
  theorem4_coalitionAmplificationEpsilonWitness_of_upperTail_longTail_endpoint_estimates_strict_derived
    noiseLaw hlong hlarge hmass hv heps_pos heps_le_one hsigma_nonneg
    herror_lt hlower_atTop hcutoff_lower hhigh_le_sigma_div

/--
Theorem 4 indexed witness for the concrete iid cutoff-affordance model.

Source status: PG24 Theorem 4 in the product-noise cutoff-market shape.  The
regular-interval approximation is stated directly for cutoff-affordance
probabilities under the iid product noise law; the independent upper-tail
long-tail estimate is used only internally.
-/
theorem theorem4_coalition_amplification_indexed_witness_from_iidProduct_cutoff_upperTail_longTail_endpoint_estimates_strict_derived_statement
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {coalition largeSubset : ∀ C : ℕ, Finset (Fin (C + 1))}
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ}
    {valueMass : ∀ _ : ℕ, Set ℝ → ℝ}
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
    theorem4_coalition_amplification_indexed_witness_statement
      coalition largeSubset
      (fun C : ℕ => fun v : ℝ => fun active : Finset (Fin (C + 1)) =>
        cutoffAffordanceProbability_statement
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          active v (cutoff C))
      valueMass
      (fun _C : ℕ => Set.Icc vLow vHigh)
      (fun C : ℕ =>
        cutoffAffordanceProbability_statement
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (largeSubset C) vLow (cutoff C))
      tol :=
  theorem4_coalitionAmplificationEpsilonWitness_of_iidProduct_cutoff_upperTail_longTail_endpoint_estimates_strict_derived
    noiseLaw hlong hlarge hmass hv heps_pos heps_le_one hsigma_nonneg
    herror_lt hlower_atTop hcutoff_lower hhigh_le_sigma_div

/--
Theorem 4 indexed witness for a selected sequence of stable matchings.

Source status: PG24 Theorem 4 is applied to stable matchings.  This row uses
A-L Lemma 1 to choose each selected stable matching's market-clearing cutoff;
the long-tail endpoint estimates are stated for all market-clearing cutoffs.
-/
theorem theorem4_coalition_amplification_indexed_witness_from_iidProduct_selected_stable_cutoff_upperTail_longTail_endpoint_estimates_strict_derived_statement
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
    {valueMass : ∀ _ : ℕ, Set ℝ → ℝ}
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
    theorem4_coalition_amplification_indexed_witness_statement
      coalition largeSubset
      (fun C : ℕ => fun v : ℝ => fun active : Finset (Fin (C + 1)) =>
        cutoffAffordanceProbability_statement
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          active v
          (cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C).1) (selected C).2)))
      valueMass
      (fun _C : ℕ => Set.Icc vLow vHigh)
      (fun C : ℕ =>
        cutoffAffordanceProbability_statement
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (largeSubset C) vLow
          (cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C).1) (selected C).2)))
      tol :=
  theorem4_coalitionAmplificationEpsilonWitness_of_iidProduct_selected_stable_cutoff_upperTail_longTail_endpoint_estimates_strict_derived
    Mseq Iseq selected noiseLaw hlong cutoffOut hlarge hmass hv heps_pos
    heps_le_one hsigma_nonneg herror_lt hlower_atTop hcutoff_lower
    hhigh_le_sigma_div

/--
Theorem 4 selected-stable source clauses from long-tail endpoint estimates.

Source status: preferred concrete PG24 Theorem 4 clause route.  This exposes
the paper-facing conclusion directly: the large subset is eventually large,
the regular interval has value mass above `1 - tol`, and every regular value
has selected-stable cutoff-affordance probability within `tol` of the
low-endpoint effective supply.
-/
theorem theorem4_coalition_amplification_indexed_source_clauses_from_iidProduct_selected_stable_cutoff_upperTail_longTail_endpoint_estimates_strict_derived_statement
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
    {valueMass : ∀ _ : ℕ, Set ℝ → ℝ}
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
          |cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C).1) (selected C).2)) -
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C) vLow
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C).1) (selected C).2))| < tol) :=
  theorem4_coalitionAmplificationEpsilonWitness_source_clauses_of_iidProduct_selected_stable_cutoff_upperTail_longTail_endpoint_estimates_strict_derived
    Mseq Iseq selected noiseLaw hlong cutoffOut hlarge hmass hv heps_pos
    heps_le_one hsigma_nonneg herror_lt hlower_atTop hcutoff_lower
    hhigh_le_sigma_div

/--
Theorem 4 selected-stable source clauses from a scalar lower-cutoff tail
estimate.

Source status: preferred concrete PG24 Theorem 4 clause route.  Compared with
the preceding row, this states the high-tail estimate once at the scalar
lower-cutoff floor and derives the per-large-college tail premises internally
from the monotone cutoff lower bound.
-/
theorem theorem4_coalition_amplification_indexed_source_clauses_from_iidProduct_selected_stable_cutoff_scalar_tail_upperTail_longTail_endpoint_estimates_strict_derived_statement
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
    {valueMass : ∀ _ : ℕ, Set ℝ → ℝ}
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
          |cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C) v
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C).1) (selected C).2)) -
              cutoffAffordanceProbability_statement
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (largeSubset C) vLow
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C).1) (selected C).2))| < tol) :=
  theorem4_coalitionAmplificationEpsilonWitness_source_clauses_of_iidProduct_selected_stable_cutoff_scalar_tail_upperTail_longTail_endpoint_estimates_strict_derived
    Mseq Iseq selected noiseLaw hlong cutoffOut hlarge hmass hv heps_pos
    heps_le_one hsigma_nonneg herror_lt hlower_atTop hcutoff_lower
    hhigh_floor_le_sigma_div

/--
Theorem 4 indexed witness from eventual exceptional-set bounds.

Source status: PG24 Theorem 4 statement form.  The approximation holds on a
regular value set whose complement has mass bounded with strict slack below
`epsilon`.
-/
theorem theorem4_coalition_amplification_indexed_witness_from_eventual_exception_bound_statement
    {College : ℕ → Type v}
    {coalition largeSubset : ∀ C : ℕ, Finset (College C)}
    {affordProb : ∀ C : ℕ, ℝ → Finset (College C) → ℝ}
    {valueMass : ∀ _ : ℕ, Set ℝ → ℝ}
    {regularSet : ∀ _ : ℕ, Set ℝ}
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
    theorem4_coalition_amplification_indexed_witness_statement
      coalition largeSubset affordProb valueMass regularSet
      effectiveSupply epsilon :=
  theorem4_coalitionAmplificationEpsilonWitness_of_eventual_exception_bound
    hlarge hpartition hexception hdelta hclose

/--
Theorem 4 indexed source clauses from the growing-coalition witness.

Source status: PG24 Theorem 4 statement clauses: `C'` is eventually large,
the regular value set is eventually large in value mass, and the approximation
inequality holds on that set.
-/
theorem theorem4_coalition_amplification_indexed_witness_source_clauses_statement
    {College : ℕ → Type v}
    {coalition largeSubset : ∀ C : ℕ, Finset (College C)}
    {affordProb : ∀ C : ℕ, ℝ → Finset (College C) → ℝ}
    {valueMass : ∀ _ : ℕ, Set ℝ → ℝ}
    {regularSet : ∀ _ : ℕ, Set ℝ}
    {effectiveSupply : ℕ → ℝ}
    {epsilon : ℝ}
    (h :
      theorem4_coalition_amplification_indexed_witness_statement
        coalition largeSubset affordProb valueMass regularSet
        effectiveSupply epsilon) :
    (∀ᶠ C : ℕ in atTop,
      CoalitionLargeSubset (coalition C) (largeSubset C) epsilon) ∧
      (∀ᶠ C : ℕ in atTop,
        1 - epsilon < valueMass C (regularSet C)) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ v ∈ regularSet C,
          |affordProb C v (largeSubset C) - effectiveSupply C| < epsilon) :=
  theorem4_coalitionAmplificationEpsilonWitness_source_clauses h

/--
Theorem 3, Attenuation in Coalitions, stated at the paper boundary.

Source: `source_tex/model-extended.tex:81-90`.  The selected stable matching
is represented by its A-L market-clearing cutoff, and iid coalition noise is
the product law.  The source's max-concentrating condition is its
positive-beta variance-rate definition (`source_tex/model.tex:54-59`).

This deliberately has no cutoff-floor, cutoff-count, capacity-contradiction,
or endpoint-ceiling premise: those are intermediate consequences that the
source derives through the dense-cluster / large-gap argument
(`source_tex/proofs-extended.tex:5-17`).  That derivation is formalized in
`Theorem3ActualProof.lean` from the stated beta-max variance condition.
-/
theorem theorem3_attenuation_in_coalitions_source_statement
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {beta : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          ∃ threshold : ℝ, ∃ largeSubset : Finset (Fin (C + 1)),
            largeSubset ⊆ (Finset.univ : Finset (Fin (C + 1))) ∧
              1 - epsilon <
                (largeSubset.card : ℝ) /
                  ((Finset.univ : Finset (Fin (C + 1))).card : ℝ) ∧
              (∀ v : ℝ, v < threshold - epsilon →
                cutoffAffordanceProbability_statement
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  largeSubset v
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2)) <
                  epsilon) ∧
              (∀ v : ℝ, threshold + epsilon < v →
                1 - epsilon <
                  cutoffAffordanceProbability_statement
                    (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                    (Finset.univ : Finset (Fin (C + 1))) v
                    (cutoffOut C
                      ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2))) := by
  intro epsilon hepsilon
  have hattention := theorem3_attenuation_in_coalitions_of_iid_beta
    noiseLaw hbeta hvariance hepsilon
  filter_upwards [hattention] with C hC a
  let selectedCutoff : Fin (C + 1) → ℝ :=
    cutoffOut C
      ((Iseq C).marketClearingCutoffOfStable
        (μ := (selected C a).1) (selected C a).2)
  rcases hC selectedCutoff with ⟨threshold, largeSubset, hlarge, hlow, hhigh⟩
  refine ⟨threshold, largeSubset, hlarge.subset, hlarge.large_ratio, ?_, ?_⟩
  · intro v hv
    simpa [cutoffAffordanceProbability_statement, selectedCutoff] using hlow v hv
  · intro v hv
    simpa [cutoffAffordanceProbability_statement, selectedCutoff] using hhigh v hv

/--
Theorem 4 (amplification in coalitions) at the extended source-model boundary.

Source: `source_tex/model-extended.tex:40-109` and
`source_tex/proofs-extended.tex:19-30`.  The theorem quantifies over the actual
broader college carrier and an embedded `(noiseLaw, eta)` coalition.  Student
preferences depend only on the source student state, coalition true values are
common almost everywhere, coalition estimates are true value plus iid noise,
and the selected cutoff clears every global college exactly.

The large-subset and approximation clauses are displayed directly.  No
split-index capacity estimate, sorted relabeling, endpoint package, or record
containing the theorem conclusion is a premise.
-/
theorem theorem4_amplification_in_coalitions_from_true_value_source_primitives_statement
    (noiseLaw eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {totalSupply : ℝ} (htotalSupply_pos : 0 < totalSupply)
    (htotalSupply_lt_one : totalSupply < 1) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N : ℕ, ∀ C : ℕ, N ≤ C →
        ∀ (StudentType : Type u) [MeasurableSpace StudentType]
          (Outcome : Type v) [MeasurableSpace Outcome]
          (GlobalCollege : Type w) [Fintype GlobalCollege]
          (Cutoff : Type x)
          (sampling :
            PG24CoalitionSourceSampling C noiseLaw eta StudentType Outcome)
          (rankOfStudent : StudentType → GlobalCollege → ℕ)
          (rankOfStudent_injective :
            ∀ student : StudentType, Function.Injective (rankOfStudent student))
          (cutoffCoordinates : Cutoff → GlobalCollege → ℝ)
          (globalScore : Cutoff → Outcome → GlobalCollege → ℝ)
          (singletonDemandMeasurable :
            ∀ P : Cutoff, ∀ college : GlobalCollege,
              MeasurableSet
                {outcome : Outcome |
                  theorem4DemandFromPreferences
                      (fun outcome college =>
                        rankOfStudent (sampling.sourceStudent outcome) college)
                      cutoffCoordinates globalScore P outcome = some college})
          (capacity : GlobalCollege → ℝ)
          (totalCapacity_eq :
            (∑ college : GlobalCollege, capacity college) = totalSupply)
          (selectedCutoff : Cutoff)
          (selectedCutoff_clearing :
            ∀ college : GlobalCollege,
              eventMass sampling.outcomeLaw
                (fun outcome =>
                  theorem4DemandFromPreferences
                      (fun outcome college =>
                        rankOfStudent (sampling.sourceStudent outcome) college)
                      cutoffCoordinates globalScore selectedCutoff outcome =
                    some college) = capacity college)
          (approximateScore : Outcome → GlobalCollege → ℝ)
          (globalScore_eq_approximateScore :
            ∀ (P : Cutoff) (outcome : Outcome) (college : GlobalCollege),
              globalScore P outcome college = approximateScore outcome college)
          (coalitionEmbedding : Fin (C + 1) ↪ GlobalCollege)
          (trueValue : StudentType → GlobalCollege → ℝ)
          (hcoalition_trueValue :
            ∀ᵐ student ∂sampling.studentLaw,
              ∀ college : Fin (C + 1),
                trueValue student (coalitionEmbedding college) =
                  sampling.commonValue student)
          (hscore_trueValue :
            ∀ᵐ outcome ∂sampling.outcomeLaw,
              ∀ college : Fin (C + 1),
                approximateScore outcome (coalitionEmbedding college) =
                  trueValue (sampling.sourceStudent outcome)
                      (coalitionEmbedding college) +
                    sampling.coalitionNoise outcome college),
          ∃ effectiveSupply : ℝ,
          ∃ actualCoalition actualLargeSubset : Finset GlobalCollege,
          ∃ regularSet : Set ℝ,
            actualCoalition = theorem4ActualCoalition coalitionEmbedding ∧
              actualLargeSubset ⊆ actualCoalition ∧
              1 - epsilon <
                (actualLargeSubset.card : ℝ) / (actualCoalition.card : ℝ) ∧
              N < actualCoalition.card ∧
              eta.real regularSetᶜ ≤ epsilon ∧
              (∀ value ∈ regularSet,
                |(PG24StudentTypedSourceStableData.ofTrueValueSource
                    sampling rankOfStudent rankOfStudent_injective
                    cutoffCoordinates globalScore singletonDemandMeasurable
                    capacity totalCapacity_eq selectedCutoff
                    selectedCutoff_clearing approximateScore
                    globalScore_eq_approximateScore coalitionEmbedding trueValue
                    hcoalition_trueValue hscore_trueValue).toLiteralSourceStableData.pMuOnActualSubset
                    value actualLargeSubset - effectiveSupply| < epsilon) := by
  intro epsilon hepsilon
  rcases theorem4_trueValue_source_coalition_amplification_fixed_eta_of_longTailed
      noiseLaw eta hlong htotalSupply_pos htotalSupply_lt_one epsilon hepsilon with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro C hC StudentType _ Outcome _ GlobalCollege _ Cutoff sampling
    rankOfStudent rankOfStudent_injective cutoffCoordinates globalScore
    singletonDemandMeasurable capacity totalCapacity_eq selectedCutoff
    selectedCutoff_clearing approximateScore globalScore_eq_approximateScore
    coalitionEmbedding trueValue hcoalition_trueValue hscore_trueValue
  rcases hN C hC StudentType Outcome GlobalCollege Cutoff sampling rankOfStudent
      rankOfStudent_injective cutoffCoordinates globalScore
      singletonDemandMeasurable capacity totalCapacity_eq selectedCutoff
      selectedCutoff_clearing approximateScore globalScore_eq_approximateScore
      coalitionEmbedding trueValue hcoalition_trueValue hscore_trueValue with
    ⟨effectiveSupply, actualCoalition, actualLargeSubset, regularSet,
      hcoalition, hlarge, hcard, hregular, hclose⟩
  refine ⟨effectiveSupply, actualCoalition, actualLargeSubset.actualSubset,
    regularSet, hcoalition, hlarge.subset, hlarge.large_ratio, hcard, hregular,
    ?_⟩
  intro value hvalue
  simpa only [PG24StudentTypedSourceStableData.pMuOnActualCoalitionSubset,
    PG24LiteralSourceStableData.pMuOnActualSubset] using hclose value hvalue

namespace ProofInterface

/-- Theorem 1 (Attenuation), uniformly over literal source economies and
selected market-clearing cutoffs. -/
theorem review_theorem1_attenuationSpec_proof
    {Admissible : ℕ → Type w}
    {StudentType : (C : ℕ) → Admissible C → Type u}
    [∀ (C : ℕ) (a : Admissible C), MeasurableSpace (StudentType C a)]
    {Cutoff : (C : ℕ) → Admissible C → Type v}
    (noiseLaw eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    {maxVariance : ℕ → ℝ} {alpha beta totalSupply vS : ℝ}
    (market : ∀ (C : ℕ) (a : Admissible C),
      PG24LiteralBasicMarket C noiseLaw eta totalSupply alpha
        (StudentType C a) (Cutoff C a))
    (selectedCutoff : ∀ (C : ℕ) (a : Admissible C), Cutoff C a)
    (selectedCutoff_clearing : ∀ (C : ℕ) (a : Admissible C),
      (market C a).marketClearing (selectedCutoff C a))
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (halpha_pos : 0 < alpha)
    (hregular : PG24HolderIntervalRegular eta)
    (hconnected : IsPreconnected eta.support)
    (htotalSupply_pos : 0 < totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (htail_normalization : eta.real (Set.Ioi vS) = totalSupply) :
    (∀ value epsilon : ℝ, value < vS → 0 < epsilon →
      ∀ᶠ C : ℕ in atTop, ∀ a : Admissible C,
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) value
          ((market C a).demand.cutoffCoordinates (selectedCutoff C a)) <
            epsilon) ∧
    (∀ value epsilon : ℝ, vS < value → 0 < epsilon →
      ∀ᶠ C : ℕ in atTop, ∀ a : Admissible C,
        1 - epsilon < cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) value
          ((market C a).demand.cutoffCoordinates (selectedCutoff C a))) := by
  exact theorem1_attenuation_from_literal_source_primitives_statement
    noiseLaw eta market selectedCutoff selectedCutoff_clearing hbeta hvariance
    halpha_pos.le hregular hconnected htotalSupply_pos htotalSupply_lt_one
    htail_normalization

/-- Theorem 2 (Amplification), including fixed targets outside bounded value
support. -/
theorem review_theorem2_amplificationSpec_proof
    {StudentTypeSeq : ℕ → Type u}
    [∀ C : ℕ, MeasurableSpace (StudentTypeSeq C)]
    {Admissible : ℕ → Type v}
    (CutoffSeq : ℕ → Type w)
    (noiseLaw eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    {totalSupply alpha : ℝ}
    (market : ∀ C : ℕ, Admissible C →
      PG24LiteralBasicMarket C noiseLaw eta totalSupply alpha
        (StudentTypeSeq C) (CutoffSeq C))
    (selectedCutoff : ∀ C : ℕ, Admissible C → CutoffSeq C)
    (selectedCutoff_clearing : ∀ (C : ℕ) (a : Admissible C),
      (market C a).marketClearing (selectedCutoff C a))
    (hregular : PG24HolderIntervalRegular eta)
    (hconnected : IsPreconnected eta.support)
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (htotalSupply_pos : 0 < totalSupply)
    (htotalSupply_lt_one : totalSupply < 1)
    (halpha_pos : 0 < alpha) :
    ∀ target epsilon : ℝ, 0 < epsilon →
      ∀ᶠ C : ℕ in atTop, ∀ a : Admissible C,
        |cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) target
            ((market C a).demand.cutoffCoordinates (selectedCutoff C a)) -
          totalSupply| < epsilon := by
  exact theorem2_amplification_from_literal_source_primitives_statement
    CutoffSeq noiseLaw eta market selectedCutoff selectedCutoff_clearing
    hregular hconnected hlong htotalSupply_pos htotalSupply_lt_one halpha_pos


/-- Theorem 3 (Attenuation in Coalitions) in the literal extended economy. -/
theorem review_theorem3_attenuationInCoalitionsExpandedSpec_proof
    (noiseLaw eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    {maxVariance : ℕ → ℝ} {beta : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    {totalSupply : ℝ} (htotalSupply_pos : 0 < totalSupply)
    (htotalSupply_lt_one : totalSupply < 1) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N : ℕ, ∀ C : ℕ, N ≤ C →
        ∀ (StudentType : Type u) [MeasurableSpace StudentType]
          (Outcome : Type v) [MeasurableSpace Outcome]
          (GlobalCollege : Type w) [Fintype GlobalCollege]
          (Cutoff : Type x)
          (sampling :
            PG24CoalitionSourceSampling C noiseLaw eta StudentType Outcome)
          (rankOfStudent : StudentType → GlobalCollege → ℕ)
          (rankOfStudent_injective :
            ∀ student : StudentType, Function.Injective (rankOfStudent student))
          (cutoffCoordinates : Cutoff → GlobalCollege → ℝ)
          (globalScore : Cutoff → Outcome → GlobalCollege → ℝ)
          (singletonDemandMeasurable :
            ∀ P : Cutoff, ∀ college : GlobalCollege,
              MeasurableSet
                {outcome : Outcome |
                  theorem4DemandFromPreferences
                      (fun outcome college =>
                        rankOfStudent (sampling.sourceStudent outcome) college)
                      cutoffCoordinates globalScore P outcome = some college})
          (capacity : GlobalCollege → ℝ)
          (totalCapacity_eq :
            (∑ college : GlobalCollege, capacity college) = totalSupply)
          (selectedCutoff : Cutoff)
          (selectedCutoff_clearing :
            ∀ college : GlobalCollege,
              eventMass sampling.outcomeLaw
                (fun outcome =>
                  theorem4DemandFromPreferences
                      (fun outcome college =>
                        rankOfStudent (sampling.sourceStudent outcome) college)
                      cutoffCoordinates globalScore selectedCutoff outcome =
                    some college) = capacity college)
          (approximateScore : Outcome → GlobalCollege → ℝ)
          (globalScore_eq_approximateScore :
            ∀ (P : Cutoff) (outcome : Outcome) (college : GlobalCollege),
              globalScore P outcome college = approximateScore outcome college)
          (coalitionEmbedding : Fin (C + 1) ↪ GlobalCollege)
          (trueValue : StudentType → GlobalCollege → ℝ)
          (hcoalition_trueValue :
            ∀ᵐ student ∂sampling.studentLaw,
              ∀ college : Fin (C + 1),
                trueValue student (coalitionEmbedding college) =
                  sampling.commonValue student)
          (hscore_trueValue :
            ∀ᵐ outcome ∂sampling.outcomeLaw,
              ∀ college : Fin (C + 1),
                approximateScore outcome (coalitionEmbedding college) =
                  trueValue (sampling.sourceStudent outcome)
                      (coalitionEmbedding college) +
                    sampling.coalitionNoise outcome college),
        ∃ threshold : ℝ,
        ∃ actualCoalition actualLargeSubset : Finset GlobalCollege,
          actualCoalition = theorem4ActualCoalition coalitionEmbedding ∧
          actualLargeSubset ⊆ actualCoalition ∧
          1 - epsilon <
            (actualLargeSubset.card : ℝ) / (actualCoalition.card : ℝ) ∧
          N < actualCoalition.card ∧
          (∀ value : ℝ, value < threshold - epsilon →
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (theorem4PullbackCoalitionSubset
                coalitionEmbedding actualLargeSubset)
              value
              (fun college =>
                cutoffCoordinates selectedCutoff (coalitionEmbedding college)) <
              epsilon) ∧
          (∀ value : ℝ, threshold + epsilon < value →
            1 - epsilon < cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) value
              (fun college =>
                cutoffCoordinates selectedCutoff
                  (coalitionEmbedding college))) := by
  intro epsilon hepsilon
  rcases PG24StudentTypedSourceStableData.theorem3_studentTyped_source_coalition_attenuation_threshold_of_iid_beta
      noiseLaw hbeta hvariance hepsilon with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro C hC StudentType _ Outcome _ GlobalCollege _ Cutoff sampling
    rankOfStudent rankOfStudent_injective cutoffCoordinates globalScore
    singletonDemandMeasurable capacity totalCapacity_eq selectedCutoff
    selectedCutoff_clearing approximateScore globalScore_eq_approximateScore
    coalitionEmbedding trueValue hcoalition_trueValue hscore_trueValue
  let data := PG24StudentTypedSourceStableData.ofTrueValueSource
    sampling rankOfStudent rankOfStudent_injective cutoffCoordinates globalScore
    singletonDemandMeasurable capacity totalCapacity_eq selectedCutoff
    selectedCutoff_clearing approximateScore globalScore_eq_approximateScore
    coalitionEmbedding trueValue hcoalition_trueValue hscore_trueValue
  rcases hN C hC StudentType Outcome GlobalCollege Cutoff data with
    ⟨threshold, actualCoalition, actualLargeSubset, hcoalition, hcard,
      hlarge, hlow, hhigh⟩
  refine ⟨threshold, actualCoalition, actualLargeSubset.actualSubset,
    hcoalition, hlarge.subset, hlarge.large_ratio, hcard, ?_, ?_⟩
  · intro value hvalue
    simpa only [cutoffAffordanceProbability,
      PG24StudentTypedSourceStableData.pMuOnActualCoalitionSubset,
      PG24LiteralSourceStableData.pMuOnActualSubset,
      PG24ExtendedCoalitionSourceStableInstance.pMu,
      PG24ExtendedCoalitionSourceStableInstance.localCutoff,
      coalitionCutoffRestriction,
      PG24LiteralSourceStableData.toExtendedCoalitionSourceStableInstance,
      PG24StudentTypedSourceStableData.toLiteralSourceStableData,
      PG24StudentTypedSourceStableData.demand,
      data, PG24StudentTypedSourceStableData.ofTrueValueSource] using
      hlow value hvalue
  · intro value hvalue
    have hhigh_value := hhigh value hvalue
    rw [PG24StudentTypedSourceStableData.pMuOnActualCoalitionSubset_ofIndexed_eq_indexed]
      at hhigh_value
    simpa only [cutoffAffordanceProbability,
      PG24LiteralSourceStableData.pMuOnActualSubset,
      PG24ExtendedCoalitionSourceStableInstance.pMu,
      PG24ExtendedCoalitionSourceStableInstance.localCutoff,
      coalitionCutoffRestriction,
      PG24LiteralSourceStableData.toExtendedCoalitionSourceStableInstance,
      PG24StudentTypedSourceStableData.toLiteralSourceStableData,
      PG24StudentTypedSourceStableData.demand,
      data, PG24StudentTypedSourceStableData.ofTrueValueSource] using
      hhigh_value

/-- Theorem 4 (Amplification in Coalitions) in the broader source economy. -/
theorem review_theorem4_amplificationInCoalitionsExpandedSpec_proof
    (noiseLaw eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {totalSupply : ℝ} (htotalSupply_pos : 0 < totalSupply)
    (htotalSupply_lt_one : totalSupply < 1) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N : ℕ, ∀ C : ℕ, N ≤ C →
        ∀ (StudentType : Type u) [MeasurableSpace StudentType]
          (Outcome : Type v) [MeasurableSpace Outcome]
          (GlobalCollege : Type w) [Fintype GlobalCollege]
          (Cutoff : Type x)
          (sampling :
            PG24CoalitionSourceSampling C noiseLaw eta StudentType Outcome)
          (rankOfStudent : StudentType → GlobalCollege → ℕ)
          (rankOfStudent_injective :
            ∀ student : StudentType, Function.Injective (rankOfStudent student))
          (cutoffCoordinates : Cutoff → GlobalCollege → ℝ)
          (globalScore : Cutoff → Outcome → GlobalCollege → ℝ)
          (singletonDemandMeasurable :
            ∀ P : Cutoff, ∀ college : GlobalCollege,
              MeasurableSet
                {outcome : Outcome |
                  theorem4DemandFromPreferences
                      (fun outcome college =>
                        rankOfStudent (sampling.sourceStudent outcome) college)
                      cutoffCoordinates globalScore P outcome = some college})
          (capacity : GlobalCollege → ℝ)
          (totalCapacity_eq :
            (∑ college : GlobalCollege, capacity college) = totalSupply)
          (selectedCutoff : Cutoff)
          (selectedCutoff_clearing :
            ∀ college : GlobalCollege,
              eventMass sampling.outcomeLaw
                (fun outcome =>
                  theorem4DemandFromPreferences
                      (fun outcome college =>
                        rankOfStudent (sampling.sourceStudent outcome) college)
                      cutoffCoordinates globalScore selectedCutoff outcome =
                    some college) = capacity college)
          (approximateScore : Outcome → GlobalCollege → ℝ)
          (globalScore_eq_approximateScore :
            ∀ (P : Cutoff) (outcome : Outcome) (college : GlobalCollege),
              globalScore P outcome college = approximateScore outcome college)
          (coalitionEmbedding : Fin (C + 1) ↪ GlobalCollege)
          (trueValue : StudentType → GlobalCollege → ℝ)
          (hcoalition_trueValue :
            ∀ᵐ student ∂sampling.studentLaw,
              ∀ college : Fin (C + 1),
                trueValue student (coalitionEmbedding college) =
                  sampling.commonValue student)
          (hscore_trueValue :
            ∀ᵐ outcome ∂sampling.outcomeLaw,
              ∀ college : Fin (C + 1),
                approximateScore outcome (coalitionEmbedding college) =
                  trueValue (sampling.sourceStudent outcome)
                      (coalitionEmbedding college) +
                    sampling.coalitionNoise outcome college),
          ∃ effectiveSupply : ℝ,
          ∃ actualCoalition actualLargeSubset : Finset GlobalCollege,
          ∃ regularSet : Set ℝ,
            actualCoalition = theorem4ActualCoalition coalitionEmbedding ∧
            actualLargeSubset ⊆ actualCoalition ∧
            1 - epsilon <
              (actualLargeSubset.card : ℝ) / (actualCoalition.card : ℝ) ∧
            N < actualCoalition.card ∧
            eta.real regularSetᶜ ≤ epsilon ∧
            (∀ value ∈ regularSet,
              |cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (theorem4PullbackCoalitionSubset
                    coalitionEmbedding actualLargeSubset)
                  value
                  (fun college =>
                    cutoffCoordinates selectedCutoff
                      (coalitionEmbedding college)) - effectiveSupply| <
                epsilon) := by
  simpa only [cutoffAffordanceProbability,
    PG24LiteralSourceStableData.pMuOnActualSubset,
    PG24ExtendedCoalitionSourceStableInstance.pMu,
    PG24ExtendedCoalitionSourceStableInstance.localCutoff,
    coalitionCutoffRestriction,
    PG24LiteralSourceStableData.toExtendedCoalitionSourceStableInstance,
    PG24StudentTypedSourceStableData.toLiteralSourceStableData,
    PG24StudentTypedSourceStableData.demand,
    PG24StudentTypedSourceStableData.ofTrueValueSource] using
    (theorem4_amplification_in_coalitions_from_true_value_source_primitives_statement
      noiseLaw eta hlong htotalSupply_pos htotalSupply_lt_one)
/-- Theorem 3 over the readable literal extended-model source bundle. -/
theorem review_theorem3_attenuationInCoalitionsSpec_proof
    (noiseLaw eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    {maxVariance : ℕ → ℝ} {beta : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    {totalSupply : ℝ} (htotalSupply_pos : 0 < totalSupply)
    (htotalSupply_lt_one : totalSupply < 1) :
    PaperInterface.review_theorem3_attenuationInCoalitionsSpec
      noiseLaw eta hbeta hvariance htotalSupply_pos htotalSupply_lt_one := by
  intro epsilon hepsilon
  rcases PG24StudentTypedSourceStableData.theorem3_studentTyped_source_coalition_attenuation_threshold_of_iid_beta
      noiseLaw hbeta hvariance hepsilon with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro C hC StudentType _ Outcome _ GlobalCollege _ Cutoff data
  rcases hN C hC StudentType Outcome GlobalCollege Cutoff
      data.toStudentTypedSourceStableData with
    ⟨threshold, actualCoalition, actualLargeSubset, hcoalition, hcard,
      hlarge, hlow, hhigh⟩
  exact ⟨threshold, actualCoalition, actualLargeSubset, hcoalition, hlarge,
    hcard, hlow, hhigh⟩

/-- Theorem 4 over the readable literal extended-model source bundle. -/
theorem review_theorem4_amplificationInCoalitionsSpec_proof
    (noiseLaw eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {totalSupply : ℝ} (htotalSupply_pos : 0 < totalSupply)
    (htotalSupply_lt_one : totalSupply < 1) :
    PaperInterface.review_theorem4_amplificationInCoalitionsSpec
      noiseLaw eta hlong htotalSupply_pos htotalSupply_lt_one := by
  intro epsilon hepsilon
  rcases PG24StudentTypedSourceStableData.theorem4_studentTyped_source_coalition_amplification_fixed_eta_of_longTailed
      noiseLaw eta hlong htotalSupply_pos htotalSupply_lt_one epsilon hepsilon with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro C hC StudentType _ Outcome _ GlobalCollege _ Cutoff data
  exact hN C hC StudentType Outcome GlobalCollege Cutoff
    data.toStudentTypedSourceStableData

/-- Exact proof endpoint for the Holder-regularity source target. -/
theorem holder_value_law_regularitySpec_proof :
    PaperInterface.holder_value_law_regularitySpec := by
  unfold PaperInterface.holder_value_law_regularitySpec
  intro eta
  rfl

/-- Exact proof endpoint for the capacity-regularity source target. -/
theorem capacity_regularitySpec_proof :
    PaperInterface.capacity_regularitySpec := by
  unfold PaperInterface.capacity_regularitySpec
  intro College _ capacity alpha totalSupply
  rfl

/-- Exact proof endpoint for the beta-max-concentration source target. -/
theorem beta_max_concentratingSpec_proof :
    PaperInterface.beta_max_concentratingSpec := by
  unfold PaperInterface.beta_max_concentratingSpec
  intro noiseLaw maxVariance beta hvariance hbeta
  rcases hbeta with ⟨hbeta_pos, K, N, hK_nonneg, hbound⟩
  rcases Filter.eventually_atTop.1 hvariance.2 with ⟨Nvariance, hvariance_bound⟩
  refine ⟨hbeta_pos, K, max N Nvariance, hK_nonneg, ?_⟩
  intro n hn
  exact (hvariance_bound n (le_trans (le_max_right _ _) hn)).trans
    (hbound n (le_trans (le_max_left _ _) hn))

/--
Appendix Lemma `log-bound`: beta-max concentration forces the expected iid
maximum to be little-o of the logarithmic sample scale.  The iid two-block
coupling and finite-second-moment bridge are derived in
`Theorem3IidExpectedMaximumLog`, rather than supplied as an endpoint premise.
-/
theorem source_log_boundSpec_proof :
    PaperInterface.source_log_boundSpec := by
  intro noiseLaw _ maxVariance beta hbeta hvariance
  exact theorem3_iidExpectedMaximum_div_log_tendsto_zero_of_beta
    noiseLaw hbeta hvariance

/-- Corrected lower-tail endpoint for Appendix Proposition `thm1v2`. -/
theorem source_thm1_corrected_lower_tailSpec_proof :
    PaperInterface.source_thm1_corrected_lower_tailSpec := by
  intro Admissible StudentType _ Cutoff noiseLaw eta _ _ maxVariance alpha beta
    totalSupply vS inst hbeta hvariance halpha_nonneg hregular htail_normalization
  exact theorem1_literal_uniform_low_matched_mass_eventually_small_of_beta_holder
    (Admissible := Admissible) noiseLaw eta inst hbeta hvariance halpha_nonneg
      hregular htail_normalization

/-- A positive limiting upper-tail mass is incompatible with the printed
negative-power display in Appendix Proposition `thm1v2`. -/
theorem source_thm1_printed_upper_tail_obstructionSpec_proof :
    PaperInterface.source_thm1_printed_upper_tail_obstructionSpec := by
  rintro mass totalSupply rate htotalSupply hrate hmass ⟨A, hbound⟩
  have hpower : Tendsto (fun C : ℕ =>
      Real.rpow (C : ℝ) (-rate)) atTop (nhds 0) := by
    simpa using (tendsto_rpow_neg_atTop hrate).comp tendsto_natCast_atTop_atTop
  have hright : Tendsto (fun C : ℕ =>
      A * Real.rpow (C : ℝ) (-rate)) atTop (nhds 0) := by
    simpa using hpower.const_mul A
  have hmass_large : ∀ᶠ C : ℕ in atTop, totalSupply / 2 < mass C := by
    have hhalf_lt : totalSupply / 2 < totalSupply := by linarith
    exact hmass (Ioi_mem_nhds hhalf_lt)
  have hright_small : ∀ᶠ C : ℕ in atTop,
      A * Real.rpow (C : ℝ) (-rate) < totalSupply / 2 :=
    hright (Iio_mem_nhds (by linarith))
  have hfalse : ∀ᶠ C : ℕ in atTop, False := by
    filter_upwards [hmass_large, hbound, hright_small] with C hmass_C hbound_C hright_C
    linarith
  obtain ⟨C, hfalse_C⟩ := hfalse.exists
  exact hfalse_C

/-- Appendix Proposition `duck-1`, at its displayed `phi3 - 1` rate. -/
theorem source_duck_1Spec_proof :
    PaperInterface.source_duck_1Spec := by
  intro College active capacity alpha beta gamma C hC_pos halpha_pos hcard hcapacity
  exact theorem1Tail_sparseBlock_capacity_le_alpha_rpow_phi3_sub_one
    active capacity hC_pos (le_of_lt halpha_pos) (le_of_lt hcard)
      (fun c hc => le_of_lt (hcapacity c hc))

/-- Appendix Proposition `goose-1`, with its literal displayed `-K` rate. -/
theorem source_goose_1Spec_proof :
    PaperInterface.source_goose_1Spec := by
  intro College active capacity alpha beta gamma C hC_pos halpha_pos hcard hcapacity
  exact theorem1Tail_sparseBlock_capacity_lt_alpha_rpow_neg_K
    active capacity hC_pos halpha_pos hcard hcapacity

/-- Appendix Proposition `lt-large-firms`, with its strict open interval. -/
theorem source_lt_large_firmsSpec_proof :
    PaperInterface.source_lt_large_firmsSpec := by
  intro pLarge vLow vHigh S alpha epsilon sigma hmono hupper hlower hdiff
  exact theorem2_largeFirm_strict_interval_eventually_of_endpoint_product_error
    hmono hupper hlower hdiff

/-- Appendix Proposition `lt-small-firms`, uniformly for all values below `v*`. -/
theorem source_lt_small_firmsSpec_proof :
    PaperInterface.source_lt_small_firmsSpec := by
  intro pSmall vStar totalSupply alpha epsilon sigma hepsilon hden hmono hcapacity
  exact theorem2_smallFirmSourceBound_eventually_uniform_of_star_capacity_mass
    hepsilon hden hmono hcapacity

/-- Appendix Proposition `lt-approx-F2`, retaining the source's strict gap. -/
theorem source_lt_approx_f2Spec_proof :
    PaperInterface.source_lt_approx_f2Spec := by
  intro active qLow qHigh epsilon sigma hepsilon hsigma hactive hratio
    hlowPos hlowLe
  exact theorem2_independentAffordanceProbability_difference_eventually_lt_exp_error
    hepsilon hsigma hactive hratio hlowPos hlowLe

/-- Appendix Lemma `unbounded-cutoffs`, through literal clearing demand. -/
theorem source_unbounded_cutoffsSpec_proof :
    PaperInterface.source_unbounded_cutoffsSpec := by
  intro StudentTypeSeq _ OutcomeSeq _ GlobalCollegeSeq _ CutoffSeq noiseLaw eta
    _ _ hlong totalSupply epsilon hepsilon htotalSupply data hsorted
  exact theorem2_literalSource_unbounded_cutoffs_eventually
    CutoffSeq noiseLaw eta hlong hepsilon htotalSupply data hsorted

/-- Appendix Lemma `apple`, with the long-tail denominator made explicit. -/
theorem source_appleSpec_proof :
    PaperInterface.source_appleSpec := by
  intro StudentTypeSeq _ OutcomeSeq _ GlobalCollegeSeq _ CutoffSeq noiseLaw eta
    _ _ hlong totalSupply epsilon vLow vHigh hepsilon hv htotalSupply data hsorted
  exact theorem2_literalSource_apple_eventually
    CutoffSeq noiseLaw eta hlong hepsilon hv htotalSupply data hsorted

/-- Unnamed appendix large-firm tail lemma, at its literal sigma/C rate. -/
theorem source_large_firm_tail_boundSpec_proof :
    PaperInterface.source_large_firm_tail_boundSpec := by
  intro StudentTypeSeq _ OutcomeSeq _ GlobalCollegeSeq _ CutoffSeq noiseLaw eta
    _ _ hlong totalSupply epsilon vHigh hepsilon htotalSupply data hsorted
  exact theorem2_literalSource_large_firm_tail_bound_eventually
    CutoffSeq noiseLaw eta hlong hepsilon htotalSupply data hsorted

/-- Appendix Proposition `tomato`, with both literal Chebyshev exponents. -/
theorem source_tomatoSpec_proof :
    PaperInterface.source_tomatoSpec := by
  intro noiseLaw _ maxVariance beta gamma hbeta hgamma hvariance dense upper cutoff
    highValue ceiling lowValue pivot hdense_subset hdense_card hupper hhigh_separation
    hlower hlow_separation
  rcases theorem1DenseGroup_one_sub_cutoff_affordance_eventually_le_chebyshev_rate_of_beta
    noiseLaw hbeta hgamma hvariance dense upper cutoff highValue ceiling
      hdense_subset hdense_card hupper hhigh_separation with ⟨A, hA, hhigh⟩
  rcases theorem1DenseGroup_cutoff_affordance_eventually_le_source_rate_of_beta
    noiseLaw hbeta hgamma hvariance upper cutoff lowValue pivot
      hlower hlow_separation with ⟨B, hB, hlow⟩
  refine ⟨⟨A, hA, ?_⟩, ⟨B, hB, ?_⟩⟩
  · filter_upwards [hhigh] with C hC
    convert hC using 1 <;> ring
  · filter_upwards [hlow] with C hC
    rw [theorem1Tail_case1_chebyshev_exp_eq_neg_K hbeta.1 hgamma]
    exact hC

/-- Appendix Proposition `duck-2`, at its literal first-case integral rate. -/
theorem source_duck_2Spec_proof :
    PaperInterface.source_duck_2Spec := by
  intro noiseLaw valueLaw _ _ maxVariance beta gamma hbeta hgamma hvariance
    upper cutoff lowValue pivot hlower hseparation
  exact theorem1DenseGroup_low_affordance_integral_eventually_le_source_rate_of_beta
    noiseLaw hbeta hgamma hvariance valueLaw upper cutoff lowValue pivot
      hlower hseparation

/-- Appendix Proposition `beet`: literal low rate and repaired high endpoint. -/
theorem source_beetSpec_proof :
    PaperInterface.source_beetSpec := by
  intro noiseLaw _ maxVariance beta gamma hbeta hgamma hvariance cutoff hlarge_gap
  rcases theorem1_fullBlock_deviation_eventually_le_source_rate_of_beta
    noiseLaw hbeta hgamma hvariance with ⟨A, hA, hdeviation⟩
  constructor
  · refine ⟨A, hA, ?_⟩
    filter_upwards [hdeviation] with C hC
    have hseparation :
        AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
            (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) C +
          Real.rpow (C : ℝ) (theorem1TailPhi4 beta gamma) ≤
          theorem3RankedCutoffNat C (cutoff C)
              (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma)) -
            (theorem3RankedCutoffNat C (cutoff C)
                (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma)) -
              AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) C -
              Real.rpow (C : ℝ) (theorem1TailPhi4 beta gamma)) := by
      linarith
    calc
      cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (theorem1CutoffAtOrAboveBlock
            (Finset.univ : Finset (Fin (C + 1))) (cutoff C)
            (theorem3RankedCutoffNat C (cutoff C)
              (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma))))
          (theorem3RankedCutoffNat C (cutoff C)
            (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma)) -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
              (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) C -
            Real.rpow (C : ℝ) (theorem1TailPhi4 beta gamma))
          (cutoff C) ≤
          AppliedModelingLib.Probability.topOrderDeviationProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
              (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) C)
            (Real.rpow (C : ℝ) (theorem1TailPhi4 beta gamma)) := by
          exact theorem1_iid_atOrAbove_affordance_le_full_max_deviation
            noiseLaw (Finset.univ : Finset (Fin (C + 1))) (cutoff C)
            (theorem3RankedCutoffNat C (cutoff C)
              (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma))) _ _ _ hseparation
      _ ≤ A * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma)) := hC
      _ = A * Real.rpow (C : ℝ)
            (-beta - 2 * theorem1TailPhi4 beta gamma) := by
          rw [theorem1Tail_case2_chebyshev_exp_eq_neg_K]
  · intro value hvalue
    have hendpoint := theorem1_ranked_largeGap_full_affordance_tendsto_one
      noiseLaw hbeta hgamma hvariance hlarge_gap
    rw [tendsto_order]
    constructor
    · intro lower hlower
      filter_upwards [hendpoint (Ioi_mem_nhds hlower), hvalue] with C hC hvalueC
      exact lt_of_lt_of_le hC
        (cutoffAffordanceProbability_mono_value
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) (le_of_lt hvalueC))
    · intro upper hupper
      filter_upwards with C
      exact lt_of_le_of_lt
        (cutoffAffordanceProbability_le_one
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) (value C) (cutoff C)) hupper

/-- Appendix Proposition `goose-2`, under its source-valid qualitative repair. -/
theorem source_goose_2Spec_proof :
    PaperInterface.source_goose_2Spec := by
  intro noiseLaw valueLaw _ _ maxVariance beta gamma vS totalSupply
    hbeta hgamma hvariance cutoff hfull_capacity htail_normalization hlarge_gap
  exact theorem1_largeGap_upper_low_integral_tendsto_zero_of_beta
    noiseLaw valueLaw hbeta hgamma hvariance hfull_capacity htail_normalization
      hlarge_gap

/-- Proposition `thm2v2`, derived from the all-real source theorem at its endpoints. -/
theorem source_thm2_equivalent_boundSpec_proof :
    PaperInterface.source_thm2_equivalent_boundSpec := by
  intro Admissible matchProb eta _ totalSupply hmono hall epsilon vLow vHigh
    hepsilon _hLowerTail _hUpperTail hwindow
  filter_upwards [hall vLow epsilon hepsilon, hall vHigh epsilon hepsilon]
    with C hlow hhigh a value hvalueLow hvalueHigh
  have hmono_low : matchProb C a vLow ≤ matchProb C a value :=
    hmono C a (le_of_lt hvalueLow)
  have hmono_high : matchProb C a value ≤ matchProb C a vHigh :=
    hmono C a (le_of_lt hvalueHigh)
  have hlow_a := hlow a
  have hhigh_a := hhigh a
  rw [abs_sub_lt_iff] at hlow_a hhigh_a
  constructor <;> linarith

/-- Exact proof endpoint for the long-tailed-noise source target. -/
theorem long_tailed_noiseSpec_proof :
    PaperInterface.long_tailed_noiseSpec := by
  unfold PaperInterface.long_tailed_noiseSpec
  intro noiseLaw
  rfl

/-- Exact proof endpoint for the stable-matching cutoff source target. -/
theorem stable_matching_cutoff_definitionSpec_proof :
    PaperInterface.stable_matching_cutoff_definitionSpec := by
  unfold PaperInterface.stable_matching_cutoff_definitionSpec
  intro C noiseLaw eta totalSupply alpha StudentType _ Cutoff market matching
  rfl

/-- Exact proof endpoint for the matching-probability source target. -/
theorem match_probability_formulaSpec_proof :
    PaperInterface.match_probability_formulaSpec := by
  unfold PaperInterface.match_probability_formulaSpec
  intro College _ sampleLaw active value cutoff
  rfl

end ProofInterface

end PG24NoisyMatchingMarkets
