import PG24NoisyMatchingMarkets.MainTheorems
import PG24NoisyMatchingMarkets.Assumptions
import PG24NoisyMatchingMarkets.Theorem4CapacityResolution
import PG24NoisyMatchingMarkets.Theorem4TrueValueSourceConclusion
import PG24NoisyMatchingMarkets.Theorem3ActualProof
import PG24NoisyMatchingMarkets.Theorem1LiteralUniformSourceConclusion
import PG24NoisyMatchingMarkets.PG24LiteralBasicMarket
import PG24NoisyMatchingMarkets.Theorem2AllRealLiteralBasic
import PG24NoisyMatchingMarkets.Theorem2LiteralAppendixClaims
import AL16SupplyDemandMatching.Assumptions
import PG24NoisyMatchingMarkets.Theorem3StudentTypedSourceConclusion

/-!
# Source-Facing Interface: Wisdom and Foolishness of Noisy Matching Markets

This file is the compact review surface for the paper's model predicates,
cutoff characterization, and four theoretical results.  The historical
derivation and bridge API remains available through `ProofInterface.lean`.
-/

open Filter Topology
open scoped BigOperators

namespace PG24NoisyMatchingMarkets

open AppliedModelingLib.Matching MeasureTheory

universe u v w x

noncomputable section pg24PaperInterfaceScope

namespace PaperInterface

/-- Transparent v11 source-item target for `holder_value_law_regularity`. -/
def holder_value_law_regularitySpec : Prop :=
  ∀ eta : Measure ℝ,
    (IsPreconnected eta.support ∧ PG24HolderIntervalRegular eta) ↔
      (IsPreconnected eta.support ∧
        ∃ holderConstant exponent : ℝ,
          0 < exponent ∧
            0 ≤ holderConstant ∧
              ∀ (x delta : ℝ), 0 < delta →
                eta.real (Set.Ioo x (x + delta)) ≤
                  holderConstant * Real.rpow delta exponent)

/-- Transparent v11 source-item target for `capacity_regularity`. -/
def capacity_regularitySpec : Prop :=
  ∀ {College : Type u} [Fintype College] (capacity : College → ℝ) (alpha totalSupply : ℝ),
    (capacityRegular capacity alpha (Fintype.card College) ∧
      (∑ c : College, capacity c) = totalSupply) ↔
      ((∀ c : College, capacity c < alpha / (Fintype.card College : ℝ)) ∧
        (∑ c : College, capacity c) = totalSupply)

/-- Transparent v11 source-item target for `beta_max_concentrating`. -/
def beta_max_concentratingSpec : Prop :=
  ∀ (noiseLaw : Measure ℝ) (maxVariance : ℕ → ℝ) (beta : ℝ),
    source_assumption_iid_beta_max_variance_bound noiseLaw maxVariance →
      betaMaxConcentratingVariance maxVariance beta →
        0 < beta ∧
          ∃ K : ℝ, ∃ N : ℕ, 0 ≤ K ∧
            ∀ n : ℕ, N ≤ n →
              ProbabilityTheory.variance
                (fun sample : Fin (n + 1) → ℝ =>
                  AppliedModelingLib.Probability.upperOrderStatistic sample
                    (AppliedModelingLib.Probability.topSampleRank (n := n + 1)))
                (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) ≤
                  K * Real.rpow (((n + 1 : ℕ) : ℝ)) (-beta)

/-- Transparent v11 source-item target for Appendix Lemma `log-bound`.

The paper writes `X^(n)` for the maximum of `n` iid draws.  The nonempty
finite-product convention used throughout this development indexes that same
sequence as `Fin (n + 1)`, which is an asymptotically harmless shift while
avoiding an empty order statistic. -/
def source_log_boundSpec : Prop :=
  ∀ (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (maxVariance : ℕ → ℝ) (beta : ℝ),
    betaMaxConcentratingVariance maxVariance beta →
      source_assumption_iid_beta_max_variance_bound noiseLaw maxVariance →
        Tendsto
          (fun n : ℕ =>
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
              (fun k : ℕ => Measure.pi (fun _ : Fin (k + 1) => noiseLaw)) n /
              Real.log (n : ℝ))
          atTop (nhds 0)

/-- Corrected source target for Appendix Proposition `thm1v2`.

The displayed source integral has the wrong tail orientation: it integrates
above `vS`, whereas the surrounding prose and the attenuation theorem concern
students below `vS`.  This target states the latter as the actual matched mass
in a literal PG24 stable market.  It retains the source model primitives and
the theorem's uniformity over all admissible selected instances, but records a
vanishing conclusion rather than a polynomial rate: the source's printed
proposition does not make its `O` constant uniform over those instances.
-/
def source_thm1_corrected_lower_tailSpec : Prop :=
  ∀ {Admissible : ℕ → Type w}
    {StudentType : (C : ℕ) → Admissible C → Type u}
    [∀ (C : ℕ) (a : Admissible C), MeasurableSpace (StudentType C a)]
    {Cutoff : (C : ℕ) → Admissible C → Type v}
    (noiseLaw eta : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    [IsProbabilityMeasure eta]
    {maxVariance : ℕ → ℝ} {alpha beta totalSupply vS : ℝ}
    (inst : ∀ (C : ℕ) (a : Admissible C),
      PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
        (StudentType C a) (Cutoff C a)),
    betaMaxConcentratingVariance maxVariance beta →
      source_assumption_iid_beta_max_variance_bound noiseLaw maxVariance →
        0 ≤ alpha →
          PG24HolderIntervalRegular eta →
            eta.real (Set.Ioi vS) = totalSupply →
              ∀ epsilon : ℝ, 0 < epsilon →
                ∀ᶠ C : ℕ in atTop, ∀ a : Admissible C,
                  eventMass
                    ((inst C a).studentLaw.prod
                      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)))
                    (fun outcome : StudentType C a × (Fin (C + 1) → ℝ) =>
                      (inst C a).value outcome.1 ∈ Set.Iic vS ∧
                        chosenInActive
                          ((inst C a).literal.demand.demandAt
                            (inst C a).literal.selectedCutoff)
                          (Finset.univ : Finset (Fin (C + 1))) outcome) < epsilon

/-- Analytic obstruction to the printed upper-tail display in Proposition
`thm1v2`.  A mass converging to a positive supply level cannot be bounded by a
negative power of market size. -/
def source_thm1_printed_upper_tail_obstructionSpec : Prop :=
  ∀ (mass : ℕ → ℝ) (totalSupply rate : ℝ),
    0 < totalSupply →
      0 < rate →
        Tendsto mass atTop (nhds totalSupply) →
          ¬ ∃ A : ℝ, ∀ᶠ C : ℕ in atTop,
            mass C ≤ A * Real.rpow (C : ℝ) (-rate)

/-- Transparent source target for Appendix Proposition `duck-1`.

The source model has strictly sub-`alpha / C` individual capacities and the
first cutoff case supplies a strictly sparse set.  The displayed proposition
only concludes the corresponding non-strict `phi3 - 1` capacity bound. -/
def source_duck_1Spec : Prop :=
  ∀ {College : Type u} (active : Finset College) (capacity : College → ℝ)
    {alpha beta gamma : ℝ} {C : ℕ},
    0 < (C : ℝ) →
      0 < alpha →
        (active.card : ℝ) <
          Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma) →
          (∀ c ∈ active, capacity c < alpha / (C : ℝ)) →
            activeCapacity active capacity ≤
              alpha * Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma - 1)

/-- Transparent source target for Appendix Proposition `goose-1`.

Its printed displayed rate is `alpha * C^(-K(beta,gamma))`.  The strict
source capacity and cardinality hypotheses suffice for that exact displayed
inequality; the source proof's intermediate `1 - phi3` exponent has the
opposite sign and is not used here. -/
def source_goose_1Spec : Prop :=
  ∀ {College : Type u} (active : Finset College) (capacity : College → ℝ)
    {alpha beta gamma : ℝ} {C : ℕ},
    0 < (C : ℝ) →
      0 < alpha →
        (active.card : ℝ) <
          Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma) →
          (∀ c ∈ active, capacity c < alpha / (C : ℝ)) →
            activeCapacity active capacity <
              alpha * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma))

/-- Transparent source target for Appendix Proposition `lt-large-firms`.

The proposition is an eventual statement uniform over the source's open value
interval.  Its local hypotheses are precisely the monotonicity, two endpoint,
and strict product-gap estimates established by the preceding appendix steps.
-/
def source_lt_large_firmsSpec : Prop :=
  ∀ {pLarge : ℕ → ℝ → ℝ} {vLow vHigh S alpha epsilon sigma : ℝ},
    (∀ᶠ C : ℕ in atTop, Monotone (pLarge C)) →
      (∀ᶠ C : ℕ in atTop, pLarge C vLow ≤ S + epsilon) →
        (∀ᶠ C : ℕ in atTop,
          S - (1 + alpha) * epsilon ≤ pLarge C vHigh) →
          (∀ᶠ C : ℕ in atTop,
            pLarge C vHigh - pLarge C vLow <
              1 - Real.exp (-(2 * epsilon * sigma))) →
            ∀ᶠ C : ℕ in atTop, ∀ v : ℝ, vLow < v → v < vHigh →
              S - (1 + alpha) * epsilon -
                  (1 - Real.exp (-(2 * epsilon * sigma))) < pLarge C v ∧
                pLarge C v < S + epsilon +
                  (1 - Real.exp (-(2 * epsilon * sigma)))

/-- Transparent source target for Appendix Proposition `lt-small-firms`.

The source's capacity/integral calculation is at `v*`; monotonicity then
makes its displayed bound simultaneous for all values strictly below `v*`.
-/
def source_lt_small_firmsSpec : Prop :=
  ∀ {pSmall : ℕ → ℝ → ℝ} {vStar totalSupply alpha epsilon sigma : ℝ},
    0 < epsilon →
      0 <
        1 - totalSupply - epsilon -
          (1 - Real.exp (-(2 * epsilon * sigma))) →
        (∀ᶠ C : ℕ in atTop, Monotone (pSmall C)) →
          (∀ᶠ C : ℕ in atTop,
            Real.sqrt epsilon *
                (1 - totalSupply - epsilon -
                  (1 - Real.exp (-(2 * epsilon * sigma)))) *
                pSmall C vStar ≤
              epsilon * alpha) →
            ∀ᶠ C : ℕ in atTop, ∀ v : ℝ, v < vStar →
              theorem2_smallFirmSourceBound
                totalSupply alpha epsilon sigma (pSmall C v)

/-- Transparent source target for Appendix Proposition `lt-approx-F2`.

The source's strict product estimate requires the large-firm set to be
nonempty and the per-college failure-ratio comparison to be strict.  Both are
made explicit instead of being lost when passing to a weak product bound.
-/
def source_lt_approx_f2Spec : Prop :=
  ∀ {active : ∀ n : ℕ, Finset (Fin (n + 1))}
    {qLow qHigh : ∀ n : ℕ, Fin (n + 1) → ℝ} {epsilon sigma : ℝ},
    0 < epsilon →
      0 < sigma →
        (∀ᶠ n : ℕ in atTop, (active n).Nonempty) →
          (∀ᶠ n : ℕ in atTop, ∀ c ∈ active n,
            Real.exp (-(2 * epsilon * sigma / ((n + 1 : ℕ) : ℝ))) <
              (1 - qHigh n c) / (1 - qLow n c)) →
            (∀ᶠ n : ℕ in atTop, ∀ c ∈ active n,
              0 < 1 - qLow n c) →
              (∀ᶠ n : ℕ in atTop, ∀ c ∈ active n,
                1 - qLow n c ≤ 1) →
                ∀ᶠ n : ℕ in atTop,
                  independentAffordanceProbability (active n) (qHigh n) -
                      independentAffordanceProbability (active n) (qLow n) <
                    1 - Real.exp (-(2 * epsilon * sigma))

/-- Transparent source target for Appendix Lemma `unbounded-cutoffs`.

The source sorts its local cutoffs and proves that every college past the
`epsilon C` prefix eventually exceeds every fixed floor.  `Fin (C + 1)` and
`epsilonFloorSplitIndex` are this formalization's nonempty-product and
rounding conventions for the same large-firm suffix.
-/
def source_unbounded_cutoffsSpec : Prop :=
  ∀ {StudentTypeSeq : ℕ → Type u} [∀ C, MeasurableSpace (StudentTypeSeq C)]
    {OutcomeSeq : ℕ → Type v} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {GlobalCollegeSeq : ℕ → Type w} [∀ C, Fintype (GlobalCollegeSeq C)]
    (CutoffSeq : ℕ → Type x)
    (noiseLaw eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {totalSupply epsilon : ℝ},
    0 < epsilon → totalSupply < 1 →
      (data : ∀ C : ℕ,
        PG24LiteralSourceStableData C noiseLaw eta totalSupply
          (StudentTypeSeq C) (OutcomeSeq C) (GlobalCollegeSeq C) (CutoffSeq C)) →
      (∀ C : ℕ, ∀ i j : Fin (C + 1), (i : ℕ) ≤ (j : ℕ) →
        ((data C).toExtendedCoalitionSourceStableInstance.localCutoff i) ≤
          ((data C).toExtendedCoalitionSourceStableInstance.localCutoff j)) →
      ∀ P : ℝ, ∀ᶠ C : ℕ in atTop,
        ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
          P < (data C).toExtendedCoalitionSourceStableInstance.localCutoff c

/-- Transparent source target for Appendix Lemma `apple`.

The printed tail ratio is stated only after the preceding cutoff-divergence
lemma.  The formal target makes its eventual positive denominator explicit;
this follows from the paper's long-tailed survival premise.
-/
def source_appleSpec : Prop :=
  ∀ {StudentTypeSeq : ℕ → Type u} [∀ C, MeasurableSpace (StudentTypeSeq C)]
    {OutcomeSeq : ℕ → Type v} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {GlobalCollegeSeq : ℕ → Type w} [∀ C, Fintype (GlobalCollegeSeq C)]
    (CutoffSeq : ℕ → Type x)
    (noiseLaw eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {totalSupply epsilon vLow vHigh : ℝ},
    0 < epsilon → vLow < vHigh → totalSupply < 1 →
      (data : ∀ C : ℕ,
        PG24LiteralSourceStableData C noiseLaw eta totalSupply
          (StudentTypeSeq C) (OutcomeSeq C) (GlobalCollegeSeq C) (CutoffSeq C)) →
      (∀ C : ℕ, ∀ i j : Fin (C + 1), (i : ℕ) ≤ (j : ℕ) →
        ((data C).toExtendedCoalitionSourceStableInstance.localCutoff i) ≤
          ((data C).toExtendedCoalitionSourceStableInstance.localCutoff j)) →
      ∀ᶠ C : ℕ in atTop,
        ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
          0 < AppliedModelingLib.Probability.upperTailMass noiseLaw
              ((data C).toExtendedCoalitionSourceStableInstance.localCutoff c - vHigh) ∧
            1 - epsilon <
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                  ((data C).toExtendedCoalitionSourceStableInstance.localCutoff c - vLow) /
                AppliedModelingLib.Probability.upperTailMass noiseLaw
                  ((data C).toExtendedCoalitionSourceStableInstance.localCutoff c - vHigh)

/-- Transparent source target for the unnamed large-firm tail lemma.

The source writes `sigma / C`; the target uses that same rate, after the
literal finite-product proof internally establishes the slightly stronger
`sigma / (C + 1)` estimate.
-/
def source_large_firm_tail_boundSpec : Prop :=
  ∀ {StudentTypeSeq : ℕ → Type u} [∀ C, MeasurableSpace (StudentTypeSeq C)]
    {OutcomeSeq : ℕ → Type v} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {GlobalCollegeSeq : ℕ → Type w} [∀ C, Fintype (GlobalCollegeSeq C)]
    (CutoffSeq : ℕ → Type x)
    (noiseLaw eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {totalSupply epsilon vHigh : ℝ},
    0 < epsilon → totalSupply < 1 →
      (data : ∀ C : ℕ,
        PG24LiteralSourceStableData C noiseLaw eta totalSupply
          (StudentTypeSeq C) (OutcomeSeq C) (GlobalCollegeSeq C) (CutoffSeq C)) →
      (∀ C : ℕ, ∀ i j : Fin (C + 1), (i : ℕ) ≤ (j : ℕ) →
        ((data C).toExtendedCoalitionSourceStableInstance.localCutoff i) ≤
          ((data C).toExtendedCoalitionSourceStableInstance.localCutoff j)) →
      ∃ sigma : ℝ, 0 < sigma ∧
        ∀ᶠ C : ℕ in atTop,
          ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
            AppliedModelingLib.Probability.upperTailMass noiseLaw
                ((data C).toExtendedCoalitionSourceStableInstance.localCutoff c - vHigh) ≤
              sigma / (C : ℝ)

/-- Transparent source target for Appendix Proposition `tomato`.

The two branches use the source's same high-cutoff block.  The explicit dense
subblock and lower-cutoff geometry are the facts supplied by the first cutoff
case; the low-side conclusion retains the printed Chebyshev exponent rather
than silently replacing it by its algebraically equal `-K` form.
-/
def source_tomatoSpec : Prop :=
  ∀ (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (maxVariance : ℕ → ℝ) {beta gamma : ℝ},
    betaMaxConcentratingVariance maxVariance beta →
      0 < gamma →
        source_assumption_iid_beta_max_variance_bound noiseLaw maxVariance →
          (dense upper : ∀ C : ℕ, Finset (Fin C)) →
            (cutoff : ∀ C : ℕ, Fin C → ℝ) →
              (highValue ceiling lowValue pivot : ℕ → ℝ) →
                (∀ᶠ C : ℕ in atTop, dense C ⊆ upper C) →
                  (∀ᶠ C : ℕ in atTop,
                    Real.rpow (C : ℝ) (theorem1TailPhi2 beta gamma) ≤
                      (dense C).card) →
                    (∀ᶠ C : ℕ in atTop,
                      ∀ c ∈ dense C, cutoff C c ≤ ceiling C) →
                      (∀ᶠ C : ℕ in atTop,
                        ceiling C - highValue C <
                          theorem1DenseGroupCenter noiseLaw C beta gamma -
                            theorem1DenseDeviationRadius C beta gamma) →
                        (∀ᶠ C : ℕ in atTop,
                          ∀ c ∈ upper C, pivot C ≤ cutoff C c) →
                          (∀ᶠ C : ℕ in atTop,
                            theorem1DenseGroupCenter noiseLaw C beta gamma +
                              theorem1DenseDeviationRadius C beta gamma ≤
                                pivot C - lowValue C) →
                            (∃ A : ℝ, 0 ≤ A ∧
                              ∀ᶠ C : ℕ in atTop,
                                1 - cutoffAffordanceProbability
                                    (Measure.pi (fun _ : Fin C => noiseLaw))
                                    (upper C) (highValue C) (cutoff C) ≤
                                  A * Real.rpow (C : ℝ)
                                    (-2 * theorem1TailPhi1 beta gamma -
                                      beta * theorem1TailPhi2 beta gamma)) ∧
                              (∃ B : ℝ, 0 ≤ B ∧
                                ∀ᶠ C : ℕ in atTop,
                                  cutoffAffordanceProbability
                                      (Measure.pi (fun _ : Fin C => noiseLaw))
                                      (upper C) (lowValue C) (cutoff C) ≤
                                    B * Real.rpow (C : ℝ)
                                      (1 - 2 * theorem1TailPhi1 beta gamma -
                                        (1 + beta) * theorem1TailPhi2 beta gamma))

/-- Transparent source target for Appendix Proposition `duck-2`.

The source proposition occurs inside its first-cutoff case.  Its cutoff lower
bound and low-value separation are consequently explicit here; the integral
is the actual iid cutoff-affordance probability integrated against the value
law, rather than a supplied tail-mass certificate.
-/
def source_duck_2Spec : Prop :=
  ∀ (noiseLaw valueLaw : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure valueLaw]
    (maxVariance : ℕ → ℝ) {beta gamma : ℝ},
    betaMaxConcentratingVariance maxVariance beta →
      0 < gamma →
        source_assumption_iid_beta_max_variance_bound noiseLaw maxVariance →
          (upper : ∀ C : ℕ, Finset (Fin C)) →
            (cutoff : ∀ C : ℕ, Fin C → ℝ) →
              (lowValue pivot : ℕ → ℝ) →
                (∀ᶠ C : ℕ in atTop,
                  ∀ c ∈ upper C, pivot C ≤ cutoff C c) →
                  (∀ᶠ C : ℕ in atTop,
                    theorem1DenseGroupCenter noiseLaw C beta gamma +
                      theorem1DenseDeviationRadius C beta gamma ≤
                        pivot C - lowValue C) →
                    ∃ A : ℝ, 0 ≤ A ∧
                      ∀ᶠ C : ℕ in atTop,
                        (∫ v : ℝ,
                          (Set.Iic (lowValue C)).indicator
                            (fun v => cutoffAffordanceProbability
                              (Measure.pi (fun _ : Fin C => noiseLaw))
                              (upper C) v (cutoff C)) v ∂valueLaw) ≤
                          A * Real.rpow (C : ℝ) (-(theorem1TailK beta gamma))

/-- Source-facing Case-2 target for Appendix Proposition `beet`.

The low-side maximum estimate has its printed polynomial rate.  Under the
paper's stated beta-max premise, the high-side conclusion is the valid
qualitative one: any value sequence strictly above the source threshold has
full-market affordance converging to one.  Recovering the printed high-side
polynomial rate additionally requires a one-draw lower-tail moment bound.
-/
def source_beetSpec : Prop :=
  ∀ (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (maxVariance : ℕ → ℝ) {beta gamma : ℝ},
    betaMaxConcentratingVariance maxVariance beta →
      0 < gamma →
        source_assumption_iid_beta_max_variance_bound noiseLaw maxVariance →
          (cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ) →
            (∀ᶠ C : ℕ in atTop,
              theorem3RankedCutoffNat C (cutoff C) 0 +
                  (theorem3DenseGapBlockCount C
                    (theorem1TailPhi2 beta gamma)
                    (theorem1TailPhi3 beta gamma) : ℝ) *
                    Real.rpow (C : ℝ) (theorem1TailPhi1 beta gamma) <
                theorem3RankedCutoffNat C (cutoff C)
                  (theorem3EarlyPrefixRank C
                    (theorem1TailPhi3 beta gamma))) →
              (∃ A : ℝ, 0 ≤ A ∧
                ∀ᶠ C : ℕ in atTop,
                  cutoffAffordanceProbability
                      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                      (theorem1CutoffAtOrAboveBlock
                        (Finset.univ : Finset (Fin (C + 1))) (cutoff C)
                        (theorem3RankedCutoffNat C (cutoff C)
                          (theorem3EarlyPrefixRank C
                            (theorem1TailPhi3 beta gamma))))
                      (theorem3RankedCutoffNat C (cutoff C)
                        (theorem3EarlyPrefixRank C
                          (theorem1TailPhi3 beta gamma)) -
                        AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                          (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) C -
                        Real.rpow (C : ℝ) (theorem1TailPhi4 beta gamma))
                      (cutoff C) ≤
                    A * Real.rpow (C : ℝ)
                      (-beta - 2 * theorem1TailPhi4 beta gamma)) ∧
                ∀ value : ℕ → ℝ,
                  (∀ᶠ C : ℕ in atTop,
                    theorem3RankedCutoffNat C (cutoff C)
                      (theorem3EarlyPrefixRank C
                        (theorem1TailPhi3 beta gamma)) -
                        AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                          (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) C -
                        Real.rpow (C : ℝ) (theorem1TailPhi4 beta gamma) < value C) →
                    Tendsto (fun C : ℕ =>
                      cutoffAffordanceProbability
                        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                        (Finset.univ : Finset (Fin (C + 1))) (value C) (cutoff C))
                      atTop (nhds 1)

/-- Source-facing corrected target for Appendix Proposition `goose-2`.

The source prints an `O(C^-K)` rate.  With only beta-max concentration, its
Case-2 high-side input is qualitative, so the source-valid conclusion is that
the same high-cutoff low-value integral tends to zero.  A one-draw tail moment
assumption is needed to upgrade this endpoint to the printed rate.
-/
def source_goose_2Spec : Prop :=
  ∀ (noiseLaw valueLaw : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure valueLaw]
    (maxVariance : ℕ → ℝ) {beta gamma vS totalSupply : ℝ},
    betaMaxConcentratingVariance maxVariance beta →
      0 < gamma →
        source_assumption_iid_beta_max_variance_bound noiseLaw maxVariance →
          (cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ) →
            (∀ C : ℕ,
              (∫ value : ℝ,
                cutoffAffordanceProbability
                  (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                  (Finset.univ : Finset (Fin (C + 1))) value (cutoff C)
                ∂valueLaw) = totalSupply) →
              valueLaw.real (Set.Ioi vS) = totalSupply →
                (∀ᶠ C : ℕ in atTop,
                  theorem3RankedCutoffNat C (cutoff C) 0 +
                      (theorem3DenseGapBlockCount C
                        (theorem1TailPhi2 beta gamma)
                        (theorem1TailPhi3 beta gamma) : ℝ) *
                        Real.rpow (C : ℝ) (theorem1TailPhi1 beta gamma) <
                    theorem3RankedCutoffNat C (cutoff C)
                      (theorem3EarlyPrefixRank C
                        (theorem1TailPhi3 beta gamma))) →
                  Tendsto (fun C : ℕ =>
                    ∫ value : ℝ,
                      (Set.Iic vS).indicator
                        (fun value => cutoffAffordanceProbability
                          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                          (theorem1CutoffAtOrAboveBlock
                            (Finset.univ : Finset (Fin (C + 1))) (cutoff C)
                            (theorem3RankedCutoffNat C (cutoff C)
                              (theorem3EarlyPrefixRank C
                                (theorem1TailPhi3 beta gamma))))
                          value (cutoff C)) value
                      ∂valueLaw) atTop (nhds 0)

/-- Transparent source target for Proposition `thm2v2`.

The source's central interval is specified by its two exact value-law tails.
The formal target makes its endpoint ordering explicit and states the intended
quantifier order: after fixing epsilon and its window, one eventual market
threshold works simultaneously for every admissible matching and every value
strictly inside that window.
-/
def source_thm2_equivalent_boundSpec : Prop :=
  ∀ {Admissible : ℕ → Type u} {matchProb : ∀ C : ℕ, Admissible C → ℝ → ℝ}
    (eta : Measure ℝ) [IsProbabilityMeasure eta] {totalSupply : ℝ},
    (∀ C : ℕ, ∀ a : Admissible C, Monotone (matchProb C a)) →
      (∀ target tolerance : ℝ, 0 < tolerance →
        ∀ᶠ C : ℕ in atTop, ∀ a : Admissible C,
          |matchProb C a target - totalSupply| < tolerance) →
        ∀ epsilon vLow vHigh : ℝ, 0 < epsilon →
          eta.real (Set.Iio vLow) = epsilon →
            eta.real (Set.Ioi vHigh) = epsilon →
              vLow < vHigh →
                ∀ᶠ C : ℕ in atTop, ∀ a : Admissible C, ∀ value : ℝ,
                  vLow < value → value < vHigh →
                    totalSupply - epsilon < matchProb C a value ∧
                      matchProb C a value < totalSupply + epsilon

/-- Transparent v11 source-item target for `long_tailed_noise`. -/
def long_tailed_noiseSpec : Prop :=
  ∀ noiseLaw : Measure ℝ,
    LongTailedSurvival (AppliedModelingLib.Probability.upperTailMass noiseLaw) ↔
      ∀ d : ℝ, 0 < d →
        Tendsto
          (fun x : ℝ =>
            AppliedModelingLib.Probability.upperTailMass noiseLaw (x + d) /
              AppliedModelingLib.Probability.upperTailMass noiseLaw x)
          atTop (nhds 1)

/-- Transparent v11 source-item target for `stable_matching_cutoff_definition`. -/
def stable_matching_cutoff_definitionSpec : Prop :=
  ∀ {C : ℕ} {noiseLaw eta : Measure ℝ} {totalSupply alpha : ℝ}
    {StudentType : Type u} [MeasurableSpace StudentType] {Cutoff : Type v}
    (market :
      PG24LiteralBasicMarket C noiseLaw eta totalSupply alpha StudentType Cutoff)
    (matching :
      StudentType × (Fin (C + 1) → ℝ) → Option (Fin (C + 1))),
    market.isStable matching ↔
      ∃ cutoffPoint : Cutoff,
        market.marketClearing cutoffPoint ∧
          matching = market.demand.demandAt cutoffPoint

/-- Transparent v11 source-item target for `match_probability_formula`. -/
def match_probability_formulaSpec : Prop :=
  ∀ {College : Type u} [Fintype College] (sampleLaw : Measure (College → ℝ))
    (active : Finset College) (value : ℝ) (cutoff : College → ℝ),
    cutoffAffordanceProbability sampleLaw active value cutoff =
      sampleLaw.real {noise : College → ℝ |
        ∃ college, college ∈ active ∧ cutoff college < value + noise college}

/-- Transparent v11 semantic target for `review_theorem1_attenuation`. -/
def review_theorem1_attenuationSpec
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
    (htail_normalization : eta.real (Set.Ioi vS) = totalSupply) : Prop :=
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
        ((market C a).demand.cutoffCoordinates (selectedCutoff C a)))

/-- Transparent v11 semantic target for `review_theorem2_amplification`. -/
def review_theorem2_amplificationSpec
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
    (halpha_pos : 0 < alpha) : Prop :=
  ∀ target epsilon : ℝ, 0 < epsilon →
    ∀ᶠ C : ℕ in atTop, ∀ a : Admissible C,
      |cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) target
          ((market C a).demand.cutoffCoordinates (selectedCutoff C a)) -
        totalSupply| < epsilon

/-- Transparent v11 semantic target for `review_theorem3_attenuationInCoalitions`. -/
def review_theorem3_attenuationInCoalitionsExpandedSpec
    (noiseLaw eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    {maxVariance : ℕ → ℝ} {beta : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    {totalSupply : ℝ} (htotalSupply_pos : 0 < totalSupply)
    (htotalSupply_lt_one : totalSupply < 1) : Prop :=
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
                  (coalitionEmbedding college)))

/-- Transparent v11 semantic target for `review_theorem4_amplificationInCoalitions`. -/
def review_theorem4_amplificationInCoalitionsExpandedSpec
    (noiseLaw eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {totalSupply : ℝ} (htotalSupply_pos : 0 < totalSupply)
    (htotalSupply_lt_one : totalSupply < 1) : Prop :=
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
              epsilon)

/--
Source-facing Theorem 3 target over one literal extended-model economy.

`PG24TrueValueSourceStableData` packages only the source model's primitive
sampling, preference, cutoff-clearing, true-value, and score conditions.  The
conversion to local analytic data is derived in
`PG24TrueValueSourceStableData.toStudentTypedSourceStableData`; it does not
store a threshold, large subset, or attenuation conclusion.  This bundled
presentation preserves the source hypothesis list of the expanded bridge
above while remaining readable to an independent source reviewer.
-/
def review_theorem3_attenuationInCoalitionsSpec
    (noiseLaw eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    {maxVariance : ℕ → ℝ} {beta : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    {totalSupply : ℝ} (htotalSupply_pos : 0 < totalSupply)
    (htotalSupply_lt_one : totalSupply < 1) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ N : ℕ, ∀ C : ℕ, N ≤ C →
      ∀ (StudentType : Type u) [MeasurableSpace StudentType]
        (Outcome : Type v) [MeasurableSpace Outcome]
        (GlobalCollege : Type w) [Fintype GlobalCollege]
        (Cutoff : Type x)
        (data : PG24TrueValueSourceStableData C noiseLaw eta totalSupply
          StudentType Outcome GlobalCollege Cutoff),
      ∃ threshold : ℝ,
      ∃ actualCoalition : Finset GlobalCollege,
      ∃ actualLargeSubset :
        Theorem4ActualCoalitionSubset data.coalitionEmbedding,
        actualCoalition = theorem4ActualCoalition data.coalitionEmbedding ∧
        CoalitionLargeSubset actualCoalition actualLargeSubset.actualSubset epsilon ∧
        N < actualCoalition.card ∧
        (∀ value : ℝ, value < threshold - epsilon →
          data.toStudentTypedSourceStableData.pMuOnActualCoalitionSubset
            value actualLargeSubset < epsilon) ∧
        (∀ value : ℝ, threshold + epsilon < value →
          1 - epsilon <
            data.toStudentTypedSourceStableData.pMuOnActualCoalitionSubset value
              (Theorem4ActualCoalitionSubset.ofIndexed data.coalitionEmbedding
                Finset.univ))

/--
Source-facing Theorem 4 target over one literal extended-model economy.

As in Theorem 3, the bundled `data` argument exposes only source primitives;
the effective supply, regular set, and large coalition subset remain part of
the conclusion.
-/
def review_theorem4_amplificationInCoalitionsSpec
    (noiseLaw eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {totalSupply : ℝ} (htotalSupply_pos : 0 < totalSupply)
    (htotalSupply_lt_one : totalSupply < 1) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ N : ℕ, ∀ C : ℕ, N ≤ C →
      ∀ (StudentType : Type u) [MeasurableSpace StudentType]
        (Outcome : Type v) [MeasurableSpace Outcome]
        (GlobalCollege : Type w) [Fintype GlobalCollege]
        (Cutoff : Type x)
        (data : PG24TrueValueSourceStableData C noiseLaw eta totalSupply
          StudentType Outcome GlobalCollege Cutoff),
      ∃ effectiveSupply : ℝ,
      ∃ actualCoalition : Finset GlobalCollege,
      ∃ actualLargeSubset :
        Theorem4ActualCoalitionSubset data.coalitionEmbedding,
      ∃ regularSet : Set ℝ,
        actualCoalition = theorem4ActualCoalition data.coalitionEmbedding ∧
        CoalitionLargeSubset actualCoalition actualLargeSubset.actualSubset epsilon ∧
        N < actualCoalition.card ∧
        eta.real regularSetᶜ ≤ epsilon ∧
        (∀ value ∈ regularSet,
          |data.toStudentTypedSourceStableData.pMuOnActualCoalitionSubset
              value actualLargeSubset - effectiveSupply| < epsilon)

end PaperInterface

end pg24PaperInterfaceScope

end PG24NoisyMatchingMarkets
