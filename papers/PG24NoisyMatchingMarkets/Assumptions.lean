import Mathlib.MeasureTheory.Measure.TightNormed
import PG24NoisyMatchingMarkets.MainTheorems

/-!
# Paper Assumptions: Wisdom and Foolishness of Noisy Matching Markets

This file names paper-source conditions that remain visible inputs to the
paper-facing theorem rows. Each declaration should correspond to an explicit
source condition, not a proof convenience.
-/

open Filter
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

universe u

/--
The paper's beta-max-concentration source condition supplies an eventual
finite second moment and variance upper bound for the top order statistic.
-/
-- audit-premise: eventually, max sampleLaw n has finite second moment and Var(max sampleLaw n) <= maxVariance n
abbrev source_assumption_beta_max_variance_bound
    (sampleLaw : ∀ n : ℕ, MeasureTheory.Measure (Fin (n + 1) → ℝ))
    (maxVariance : ℕ → ℝ) : Prop :=
  (∀ᶠ n : ℕ in atTop,
    MeasureTheory.MemLp
      (fun sample : Fin (n + 1) → ℝ =>
        AppliedModelingLib.Probability.upperOrderStatistic sample
          (AppliedModelingLib.Probability.topSampleRank (n := n + 1))) 2
      (sampleLaw n)) ∧
  (∀ᶠ n : ℕ in atTop,
    ProbabilityTheory.variance
      (fun sample : Fin (n + 1) → ℝ =>
        AppliedModelingLib.Probability.upperOrderStatistic sample
          (AppliedModelingLib.Probability.topSampleRank (n := n + 1)))
      (sampleLaw n) ≤ maxVariance n)

/--
The paper's iid-noise beta-max source condition, specialized to product
noise over the `n + 1` colleges.
-/
-- audit-premise: eventually, max iid noise over n+1 colleges has finite second moment and variance <= maxVariance n
abbrev source_assumption_iid_beta_max_variance_bound
    (noiseLaw : MeasureTheory.Measure ℝ) (maxVariance : ℕ → ℝ) : Prop :=
  source_assumption_beta_max_variance_bound
    (fun n : ℕ => MeasureTheory.Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
    maxVariance

/--
Source-used clarification for the Case-2 one-college tail step: one noise draw
has a finite second moment.  This is not implied by beta-max concentration,
which controls only the maximum of an iid sample.
-/
-- audit-premise: one noise draw has finite second moment for the Case-2 lower-tail Chebyshev bound
abbrev source_clarification_one_draw_finite_second_moment
    (noiseLaw : MeasureTheory.Measure ℝ) : Prop :=
  MeasureTheory.MemLp (fun x : ℝ => x) 2 noiseLaw

/--
Source model package for the active PG24 Theorem 1 attenuation route.

This records the paper's beta-max variance condition together with the
selected-stable cutoff sandwich and threshold convergence estimates.  The
paper-facing theorem derives the low- and high-value attenuation clauses from
this package using the checked Chebyshev and cutoff-affordance route.
-/
-- audit-premise: PG24 Theorem 1 beta-max variance and selected-stable cutoff-sandwich source clauses
structure Theorem1AttenuationSourceModel
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ n : ℕ, CutoffMarket (StudentSeq n) (Fin (n + 1)))
    (Iseq : ∀ n : ℕ, SupplyDemandInterface (Mseq n))
    (noiseLaw : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (maxVariance lowerCutoff upperCutoff : ℕ → ℝ)
    (cutoffOut : ∀ n : ℕ, (Mseq n).Cutoff → Fin (n + 1) → ℝ)
    (β vS : ℝ) : Prop where
  beta_variance :
    betaMaxConcentratingVariance maxVariance β
  variance_bound :
    source_assumption_iid_beta_max_variance_bound noiseLaw maxVariance
  lower_market :
    ∀ᶠ n : ℕ in atTop,
      ∀ P : (Mseq n).Cutoff, (Mseq n).MarketClearing P →
        ∀ c : Fin (n + 1),
          lowerCutoff n ≤ cutoffOut n P c
  upper_market :
    ∀ᶠ n : ℕ in atTop,
      ∀ P : (Mseq n).Cutoff, (Mseq n).MarketClearing P →
        ∀ c : Fin (n + 1),
          cutoffOut n P c ≤ upperCutoff n
  lower_threshold :
    Tendsto
      (fun n : ℕ =>
        lowerCutoff n -
          AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
            (fun n : ℕ =>
              MeasureTheory.Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) n)
      atTop (nhds vS)
  upper_threshold :
    Tendsto
      (fun n : ℕ =>
        upperCutoff n -
          AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
            (fun n : ℕ =>
              MeasureTheory.Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) n)
      atTop (nhds vS)

/--
The paper's capacity-regularity condition: every college capacity is eventually
below `alpha / (C + 1)`.
-/
-- audit-premise: eventually, every capacity is below alpha/(C+1)
abbrev source_assumption_capacity_upper_bound
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (alpha : ℝ) : Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ c : Fin (C + 1),
      (Mseq C).capacity c < alpha / ((C + 1 : ℕ) : ℝ)

/--
The paper's positive capacity-regularity condition: every college capacity is
eventually positive and below `alpha / (C + 1)`.
-/
-- audit-premise: eventually, every capacity is positive and below alpha/(C+1)
abbrev source_assumption_capacity_open_bound
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (alpha : ℝ) : Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ c : Fin (C + 1),
      0 < (Mseq C).capacity c ∧
        (Mseq C).capacity c < alpha / ((C + 1 : ℕ) : ℝ)

/--
The paper's total-capacity normalization: the sum of all college capacities is
eventually the stated aggregate supply.
-/
-- audit-premise: eventually, the sum of all college capacities equals totalSupply
abbrev source_assumption_total_capacity_sum
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (totalSupply : ℝ) : Prop :=
  ∀ᶠ C : ℕ in atTop,
    (∑ c : Fin (C + 1), (Mseq C).capacity c) = totalSupply

/--
Theorem 2 outcome model: the selected-stable outcome law is a probability
measure.
-/
-- audit-premise: for every selected stable matching, the induced outcome law is a probability measure
abbrev source_assumption_selected_stable_outcome_probability
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C)) :
    Prop :=
  ∀ C : ℕ, ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
    MeasureTheory.IsProbabilityMeasure
      (outcomeLaw C
        ((Iseq C).marketClearingCutoffOfStable
          (μ := μ.1) μ.2))

/--
The selected-stable outcome laws have finite mass.
-/
-- audit-premise: every selected-stable outcome law has finite mass
abbrev source_assumption_selected_stable_outcome_finite
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C)) :
    Prop :=
  ∀ C : ℕ, ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
    MeasureTheory.IsFiniteMeasure
      (outcomeLaw C
        ((Iseq C).marketClearingCutoffOfStable
          (μ := μ.1) μ.2))

theorem source_assumption_selected_stable_outcome_finite_of_probability
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {OutcomeSeq : ℕ → Type*} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C)}
    (hprob :
      source_assumption_selected_stable_outcome_probability
        Mseq Iseq OutcomeSeq outcomeLaw) :
    source_assumption_selected_stable_outcome_finite
      Mseq Iseq OutcomeSeq outcomeLaw := by
  intro C μ
  haveI :
      MeasureTheory.IsProbabilityMeasure
        (outcomeLaw C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := μ.1) μ.2)) := hprob C μ
  infer_instance

/--
Theorem 2 outcome model: singleton choice events are measurable at the
selected-stable cutoff.
-/
-- audit-premise: eventually, every selected-stable singleton chosen-college event is measurable
abbrev source_assumption_selected_stable_singleton_choice_measurable
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1))) :
    Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
      ∀ c : Fin (C + 1),
        MeasurableSet
          {ω : OutcomeSeq C |
            chosenCollege C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2) ω = some c}

/--
Finite discrete outcome spaces make every selected-stable singleton
chosen-college event measurable. This discharges the previous direct
singleton-event measurability premise for source models whose outcome is a
finite chosen-college label.
-/
theorem source_assumption_selected_stable_singleton_choice_measurable_of_finite_outcome
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {OutcomeSeq : ℕ → Type*} [∀ C, MeasurableSpace (OutcomeSeq C)]
    [∀ C, Finite (OutcomeSeq C)]
    [∀ C, MeasurableSingletonClass (OutcomeSeq C)]
    {chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1))} :
    source_assumption_selected_stable_singleton_choice_measurable
      Mseq Iseq OutcomeSeq chosenCollege := by
  exact Filter.Eventually.of_forall (fun C => by
    intro μ c
    classical
    exact (Set.toFinite
      {ω : OutcomeSeq C |
        chosenCollege C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := μ.1) μ.2) ω = some c}).measurableSet)

/--
Theorem 2 outcome model: singleton choice-event masses agree with aggregate
demand at the selected-stable cutoff.
-/
-- audit-premise: eventually, every singleton choice-event mass equals the selected-stable aggregate demand for that college
abbrev source_assumption_selected_stable_singleton_choice_mass_eq_aggregateDemand
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1))) :
    Prop :=
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
              (μ := μ.1) μ.2) c

/--
Market-level outcome model: every outcome law used by a market-clearing cutoff
is a probability measure.
-/
-- audit-premise: every market-clearing outcome law is a probability measure
abbrev source_assumption_market_outcome_probability
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C)) :
    Prop :=
  ∀ C : ℕ, ∀ P : (Mseq C).Cutoff,
    MeasureTheory.IsProbabilityMeasure (outcomeLaw C P)

/--
Market-level outcome model: every outcome law used by a market-clearing cutoff
has finite mass.
-/
-- audit-premise: every market-clearing outcome law has finite mass
abbrev source_assumption_market_outcome_finite
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C)) :
    Prop :=
  ∀ C : ℕ, ∀ P : (Mseq C).Cutoff,
    MeasureTheory.IsFiniteMeasure (outcomeLaw C P)

theorem source_assumption_market_outcome_finite_of_probability
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {OutcomeSeq : ℕ → Type*} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C)}
    (hprob :
      source_assumption_market_outcome_probability
        Mseq OutcomeSeq outcomeLaw) :
    source_assumption_market_outcome_finite Mseq OutcomeSeq outcomeLaw := by
  intro C P
  haveI : MeasureTheory.IsProbabilityMeasure (outcomeLaw C P) := hprob C P
  infer_instance

/--
Market-level outcome-law probability implies probability at every selected
stable cutoff.
-/
theorem source_assumption_selected_stable_outcome_probability_of_market
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {OutcomeSeq : ℕ → Type*} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C)}
    (hprob :
      source_assumption_market_outcome_probability
        Mseq OutcomeSeq outcomeLaw) :
    source_assumption_selected_stable_outcome_probability
      Mseq Iseq OutcomeSeq outcomeLaw := by
  intro C μ
  exact
    hprob C
      ((Iseq C).marketClearingCutoffOfStable
        (μ := μ.1) μ.2)

/--
Market-level outcome model: choice mass over every finite block agrees with
aggregate demand at every market-clearing cutoff.
-/
-- audit-premise: eventually, every market-clearing active-block choice mass equals aggregate demand over that block
abbrev source_assumption_market_choice_mass_eq_aggregateDemand
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1))) :
    Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
      ∀ active : Finset (Fin (C + 1)),
        AppliedModelingLib.Matching.choiceMass
            (outcomeLaw C P) (chosenCollege C P) active =
          ∑ c ∈ active, (Mseq C).aggregateDemand P c

/--
Selected-stable outcome model: choice mass over every finite block agrees with
aggregate demand at the selected-stable cutoff.
-/
-- audit-premise: eventually, every selected-stable active-block choice mass equals aggregate demand over that block
abbrev source_assumption_selected_stable_choice_mass_eq_aggregateDemand
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1))) :
    Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C, ∀ active : Finset (Fin (C + 1)),
      AppliedModelingLib.Matching.choiceMass
          (outcomeLaw C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C a).1) (selected C a).2))
          (chosenCollege C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C a).1) (selected C a).2))
          active =
        ∑ c ∈ active,
          (Mseq C).aggregateDemand
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C a).1) (selected C a).2) c

/--
Market-level block choice-mass semantics imply the selected-stable block
choice-mass semantics by applying them to the selected market-clearing cutoff.
-/
theorem source_assumption_selected_stable_choice_mass_eq_aggregateDemand_of_market
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {OutcomeSeq : ℕ → Type*} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C)}
    {chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1))}
    (h :
      source_assumption_market_choice_mass_eq_aggregateDemand
        Mseq OutcomeSeq outcomeLaw chosenCollege) :
    source_assumption_selected_stable_choice_mass_eq_aggregateDemand
      Mseq Iseq selected OutcomeSeq outcomeLaw chosenCollege := by
  filter_upwards [h] with C hC a active
  exact
    hC
      ((Iseq C).marketClearingCutoffOfStable
        (μ := (selected C a).1) (selected C a).2)
      ((Iseq C).marketClearingCutoffOfStable_marketClearing
        (μ := (selected C a).1) (selected C a).2)
      active

/--
Market-level block choice-mass semantics imply the selected-stable singleton
choice-event semantics used by the finite-outcome Theorem 2 route.
-/
theorem source_assumption_selected_stable_singleton_choice_mass_eq_aggregateDemand_of_market
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {OutcomeSeq : ℕ → Type*} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C)}
    {chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1))}
    (h :
      source_assumption_market_choice_mass_eq_aggregateDemand
        Mseq OutcomeSeq outcomeLaw chosenCollege) :
    source_assumption_selected_stable_singleton_choice_mass_eq_aggregateDemand
      Mseq Iseq OutcomeSeq outcomeLaw chosenCollege := by
  filter_upwards [h] with C hC μ c
  let P :=
    (Iseq C).marketClearingCutoffOfStable
      (μ := μ.1) μ.2
  have hsingle :=
    hC P
      ((Iseq C).marketClearingCutoffOfStable_marketClearing
        (μ := μ.1) μ.2)
      ({c} : Finset (Fin (C + 1)))
  have hsingleton_event :
      AppliedModelingLib.Matching.chosenInActive
          (chosenCollege C P) ({c} : Finset (Fin (C + 1))) =
        (fun ω : OutcomeSeq C => chosenCollege C P ω = some c) := by
    funext ω
    apply propext
    constructor
    · intro hω
      rcases hω with ⟨d, hd, hchoice⟩
      have hdc : d = c := by
        simpa using hd
      simpa [hdc] using hchoice
    · intro hω
      exact ⟨c, by simp, hω⟩
  rw [AppliedModelingLib.Matching.choiceMass, hsingleton_event] at hsingle
  simpa [P] using hsingle

/--
Selected singleton choice-event semantics imply the selected active-block
choice-mass equality used by the capacity argument.
-/
theorem source_assumption_selected_stable_choice_mass_eq_aggregateDemand_of_singleton
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {OutcomeSeq : ℕ → Type*} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C)}
    {chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1))}
    (hfinite :
      source_assumption_selected_stable_outcome_finite
        Mseq Iseq OutcomeSeq outcomeLaw)
    (hmeas :
      source_assumption_selected_stable_singleton_choice_measurable
        Mseq Iseq OutcomeSeq chosenCollege)
    (hsingle :
      source_assumption_selected_stable_singleton_choice_mass_eq_aggregateDemand
        Mseq Iseq OutcomeSeq outcomeLaw chosenCollege) :
    source_assumption_selected_stable_choice_mass_eq_aggregateDemand
      Mseq Iseq selected OutcomeSeq outcomeLaw chosenCollege := by
  filter_upwards [hmeas, hsingle] with C hmeasC hsingleC a active
  let P :=
    (Iseq C).marketClearingCutoffOfStable
      (μ := (selected C a).1) (selected C a).2
  haveI : MeasureTheory.IsFiniteMeasure (outcomeLaw C P) :=
    hfinite C (selected C a)
  exact
    AppliedModelingLib.Matching.choiceMass_eq_sum_aggregateDemand_of_singleton_eventMass_eq
      (outcomeLaw C P) (chosenCollege C P) active
      (by
        intro c hc
        simpa [P] using hmeasC (selected C a) c)
      (by
        intro c hc
        simpa [P] using hsingleC (selected C a) c)

/--
Theorem 2 local interval/event source package.  This is the explicit source
proof data used to derive the large-block low endpoint and small-block capacity
bounds before the final amplification conclusion.  The high endpoint is stated
through an explicit event bridge: chosen large-block outcomes enter the
high-endpoint affordability event, and that event's mass is bounded by the
displayed affordance probability.
-/
-- audit-premise: for every target value and slack, the paper's local large/small interval clauses and high-endpoint event bridge hold at selected-stable cutoffs
def source_assumption_theorem2_local_interval_event_clauses
    {StudentSeq : ℕ → Type u}
    (η : MeasureTheory.Measure ℝ)
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : MeasureTheory.Measure ℝ)
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    {totalSupply : ℝ} : Prop :=
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
              cutoffAffordanceProbability
                (MeasureTheory.Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
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
                (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C) ω →
              largeEndpointEvent C μ ω) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          AppliedModelingLib.Matching.eventMass
              (outcomeLaw C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2))
              (largeEndpointEvent C μ) ≤
            cutoffAffordanceProbability
              (MeasureTheory.Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
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
                  (MeasureTheory.Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
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
                ω)

/--
Theorem 2 local interval/event source package with the cutoff-divergence
conjunct removed.

The divergence of `lowerCutoff n - vHigh` is not independent source data when
stable matchings are nonempty: it follows from the high-tail rate and
long-tailed survival.  This predicate keeps the paper's interval, event, and
endpoint clauses visible while allowing Lean to discharge that divergence
internally.
-/
-- audit-premise: PG24 Theorem 2 local interval/event clauses without the redundant lower-cutoff divergence conjunct
def source_assumption_theorem2_local_interval_event_clauses_no_divergence
    {StudentSeq : ℕ → Type u}
    (η : MeasureTheory.Measure ℝ)
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : MeasureTheory.Measure ℝ)
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    {totalSupply : ℝ} : Prop :=
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
              cutoffAffordanceProbability
                (MeasureTheory.Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
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
                (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C) ω →
              largeEndpointEvent C μ ω) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          AppliedModelingLib.Matching.eventMass
              (outcomeLaw C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2))
              (largeEndpointEvent C μ) ≤
            cutoffAffordanceProbability
              (MeasureTheory.Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
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
                  (MeasureTheory.Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
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
                ω)

/--
Source stable-matching existence for each finite PG24 market.

This is the source-model existence condition needed to turn the Theorem 2
high-tail-rate clause into cutoff divergence; without a selected stable
matching the high-tail-rate clause over selected-stable cutoffs is vacuous.
-/
-- audit-premise: each finite PG24 cutoff market has at least one stable matching
abbrev source_assumption_selected_stable_nonempty
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))) : Prop :=
  ∀ C : ℕ, Nonempty { μ : (Mseq C).Matching // (Mseq C).Stable μ }

/--
The no-divergence local-event source package implies the original package once
stable matchings are nonempty.  The missing divergence follows from the
high-tail rate tending to zero and the long-tailed distribution's eventually
positive upper tail.
-/
theorem source_assumption_theorem2_local_interval_event_clauses_of_no_divergence
    {StudentSeq : ℕ → Type u}
    {η : MeasureTheory.Measure ℝ}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {noiseLaw : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {OutcomeSeq : ℕ → Type*} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C)}
    {chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1))}
    {totalSupply : ℝ}
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (hstable_nonempty :
      source_assumption_selected_stable_nonempty Mseq)
    (h :
      source_assumption_theorem2_local_interval_event_clauses_no_divergence
        η Mseq Iseq noiseLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege
        (totalSupply := totalSupply)) :
    source_assumption_theorem2_local_interval_event_clauses
      η Mseq Iseq noiseLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege
      (totalSupply := totalSupply) := by
  intro v epsilon sigma hepsilon hsigma hden
  rcases h v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, largeIntervalEvent,
      largeEndpointEvent, smallMatchedIntervalEvent, largeInterval,
      smallInterval, hvLow, hvHigh, hvStar, hvStrict, hcutoff_lower,
      htail_floor, hlarge_meas, hlarge_mass, hlarge_ge,
      hlarge_integral_event, hlarge_event_chosen,
      hlarge_endpoint_event_chosen, hlarge_endpoint_event_bound,
      hsmall_meas, hsmall_mass, hsmall_ge, hsmall_integral_event,
      hsmall_event_chosen⟩
  have hlower_atTop :
      Tendsto (fun n : ℕ => lowerCutoff n - vHigh) atTop atTop := by
    have htail_inst :
        ∀ᶠ C : ℕ in atTop,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (lowerCutoff C - vHigh) ≤
          sigma / ((C + 1 : ℕ) : ℝ) := by
      filter_upwards [htail_floor] with C htailC
      exact htailC (Classical.choice (hstable_nonempty C))
    have hbound_zero :
        Tendsto
          (fun C : ℕ => sigma / ((C + 1 : ℕ) : ℝ))
          atTop (nhds 0) :=
      Filter.Tendsto.const_div_atTop
        AppliedModelingLib.Math.tendsto_nat_succ_cast_atTop sigma
    exact
      AppliedModelingLib.Probability.tendsto_atTop_of_upperTailMass_le_tendsto_zero
        noiseLaw
        (hlong.eventually_pos
          (fun x => AppliedModelingLib.Probability.upperTailMass_nonneg noiseLaw x))
        hbound_zero htail_inst
  exact
    ⟨vLow, vHigh, vStar, lowerCutoff, largeIntervalEvent,
      largeEndpointEvent, smallMatchedIntervalEvent, largeInterval,
      smallInterval, hvLow, hvHigh, hvStar, hvStrict, hlower_atTop,
      hcutoff_lower, htail_floor, hlarge_meas, hlarge_mass, hlarge_ge,
      hlarge_integral_event, hlarge_event_chosen,
      hlarge_endpoint_event_chosen, hlarge_endpoint_event_bound,
      hsmall_meas, hsmall_mass, hsmall_ge, hsmall_integral_event,
      hsmall_event_chosen⟩

/--
The scalar endpoint package used by the cleaner Theorem 2 amplification route.

This is the paper appendix boundary after the selected-stable outcome/event
semantics have been eliminated: a sorted-suffix cutoff floor, high-tail rate,
large-firm endpoint bounds, and small-firm active-capacity bound.  The
divergence of `lowerCutoff n - vHigh` is derived in the A-L-backed wrapper from
the high-tail rate and nonempty stable matchings, rather than assumed here.
-/
-- audit-premise: PG24 Theorem 2 scalar sorted-suffix endpoint estimates for the selected-stable cutoff route
def source_assumption_theorem2_scalar_endpoint_estimates
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : MeasureTheory.Measure ℝ)
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply : ℝ} : Prop :=
  ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
    0 <
      1 - totalSupply - epsilon -
        (1 - Real.exp (-(2 * epsilon * sigma))) →
    ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
      vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
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
                (MeasureTheory.Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
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
              (MeasureTheory.Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
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
                (MeasureTheory.Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                vStar
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := μ.1) μ.2)) ≤
            AppliedModelingLib.Matching.activeCapacity
              (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
              (Mseq C).capacity)

/--
Theorem 2 scalar endpoint package stated over all market-clearing cutoffs.

This is the cleaner market-level source boundary.  The selected-stable scalar
endpoint package follows by applying these clauses to the A-L cutoff selected
from a stable matching.
-/
-- audit-premise: PG24 Theorem 2 scalar sorted-suffix endpoint estimates for every market-clearing cutoff
def source_assumption_theorem2_scalar_market_endpoint_estimates
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (noiseLaw : MeasureTheory.Measure ℝ)
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply : ℝ} : Prop :=
  ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
    0 <
      1 - totalSupply - epsilon -
        (1 - Real.exp (-(2 * epsilon * sigma))) →
    ∃ vLow vHigh vStar : ℝ, ∃ lowerCutoff : ℕ → ℝ,
      vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
            lowerCutoff C ≤ cutoffOut C P c) ∧
      (∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Probability.upperTailMass noiseLaw
          (lowerCutoff C - vHigh) ≤
            sigma / ((C + 1 : ℕ) : ℝ)) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          (1 - epsilon) *
              cutoffAffordanceProbability
                (MeasureTheory.Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                vLow
                (cutoffOut C P) ≤
            totalSupply) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          AppliedModelingLib.Matching.activeCapacity
              (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
              (Mseq C).capacity - epsilon ≤
            cutoffAffordanceProbability
              (MeasureTheory.Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
              vHigh
              (cutoffOut C P)) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          Real.sqrt epsilon *
              (1 - totalSupply - epsilon -
                (1 - Real.exp (-(2 * epsilon * sigma)))) *
              cutoffAffordanceProbability
                (MeasureTheory.Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                vStar
                (cutoffOut C P) ≤
            AppliedModelingLib.Matching.activeCapacity
              (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
              (Mseq C).capacity)

/--
Market-level scalar endpoint estimates imply the selected-stable scalar
endpoint package.
-/
theorem source_assumption_theorem2_scalar_endpoint_estimates_of_market
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {noiseLaw : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {totalSupply : ℝ}
    (h :
      source_assumption_theorem2_scalar_market_endpoint_estimates
        Mseq noiseLaw cutoffOut (totalSupply := totalSupply)) :
    source_assumption_theorem2_scalar_endpoint_estimates
      Mseq Iseq noiseLaw cutoffOut (totalSupply := totalSupply) := by
  intro v epsilon sigma hepsilon hsigma hden
  rcases h v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar,
      hvStrict, hcutoff_lower, htail_floor, hlarge_endpoint,
      hlarge_capacity_lower, hsmall_capacity_lower⟩
  refine
    ⟨vLow, vHigh, vStar, lowerCutoff, hvLow, hvHigh, hvStar,
      hvStrict, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hcutoff_lower] with C hC μ c hc
    exact
      hC
        ((Iseq C).marketClearingCutoffOfStable
          (μ := μ.1) μ.2)
        ((Iseq C).marketClearingCutoffOfStable_marketClearing
          (μ := μ.1) μ.2)
        c hc
  · filter_upwards [htail_floor] with C hC _μ
    exact hC
  · filter_upwards [hlarge_endpoint] with C hC μ
    exact
      hC
        ((Iseq C).marketClearingCutoffOfStable
          (μ := μ.1) μ.2)
        ((Iseq C).marketClearingCutoffOfStable_marketClearing
          (μ := μ.1) μ.2)
  · filter_upwards [hlarge_capacity_lower] with C hC μ
    exact
      hC
        ((Iseq C).marketClearingCutoffOfStable
          (μ := μ.1) μ.2)
        ((Iseq C).marketClearingCutoffOfStable_marketClearing
          (μ := μ.1) μ.2)
  · filter_upwards [hsmall_capacity_lower] with C hC μ
    exact
      hC
        ((Iseq C).marketClearingCutoffOfStable
          (μ := μ.1) μ.2)
        ((Iseq C).marketClearingCutoffOfStable_marketClearing
          (μ := μ.1) μ.2)

/--
Source model package for the active PG24 Theorem 2 amplification route.

This groups the selected-stable outcome probability model, singleton
choice-event measurability and aggregate-demand identity, positive
capacity-regularity, and the paper's local large/small interval-event
clauses.  The paper-facing theorem projects this record and derives the
uniform amplification conclusion through the existing checked route.
-/
-- audit-premise: PG24 Theorem 2 selected-stable outcome, capacity, and local interval/event source clauses
structure Theorem2AmplificationSourceModel
    {StudentSeq : ℕ → Type u}
    (η : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure η]
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    (totalSupply alpha : ℝ) : Prop where
  outcome_probability :
    source_assumption_selected_stable_outcome_probability
      Mseq Iseq OutcomeSeq outcomeLaw
  singleton_choice_measurable :
    source_assumption_selected_stable_singleton_choice_measurable
      Mseq Iseq OutcomeSeq chosenCollege
  singleton_choice_mass_eq_aggregateDemand :
    source_assumption_selected_stable_singleton_choice_mass_eq_aggregateDemand
      Mseq Iseq OutcomeSeq outcomeLaw chosenCollege
  capacity_open_bound :
    source_assumption_capacity_open_bound Mseq alpha
  local_interval_event_clauses :
    source_assumption_theorem2_local_interval_event_clauses
      η Mseq Iseq noiseLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege
      (totalSupply := totalSupply)

/--
Finite-outcome source model for the active PG24 Theorem 2 amplification route.

Compared with `Theorem2AmplificationSourceModel`, this model does not assume
singleton choice-event measurability. The reviewed finite-outcome theorem
derives that measurability from `Finite` and `MeasurableSingletonClass`
instances for the outcome space, while keeping the local interval/event clauses
as the remaining source proof obligation.
-/
-- audit-premise: PG24 Theorem 2 selected-stable finite outcome, capacity, and local interval/event source clauses
structure Theorem2AmplificationFiniteOutcomeSourceModel
    {StudentSeq : ℕ → Type u}
    (η : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure η]
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    (totalSupply alpha : ℝ) : Prop where
  outcome_probability :
    source_assumption_selected_stable_outcome_probability
      Mseq Iseq OutcomeSeq outcomeLaw
  singleton_choice_mass_eq_aggregateDemand :
    source_assumption_selected_stable_singleton_choice_mass_eq_aggregateDemand
      Mseq Iseq OutcomeSeq outcomeLaw chosenCollege
  capacity_open_bound :
    source_assumption_capacity_open_bound Mseq alpha
  local_interval_event_clauses :
    source_assumption_theorem2_local_interval_event_clauses
      η Mseq Iseq noiseLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege
      (totalSupply := totalSupply)

/--
Source model package for the scalar-endpoint PG24 Theorem 2 route.

This keeps capacity regularity visible and replaces the heavier outcome/event
semantics package with the appendix endpoint inequalities needed by the
selected-stable scalar-tail proof.
-/
-- audit-premise: PG24 Theorem 2 capacity and scalar sorted-suffix endpoint source clauses
structure Theorem2ScalarEndpointSourceModel
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : MeasureTheory.Measure ℝ)
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (totalSupply alpha : ℝ) : Prop where
  capacity_open_bound :
    source_assumption_capacity_open_bound Mseq alpha
  scalar_endpoint_estimates :
    source_assumption_theorem2_scalar_endpoint_estimates
      Mseq Iseq noiseLaw cutoffOut (totalSupply := totalSupply)

/--
Source model package for the market-level scalar-endpoint PG24 Theorem 2
route.
-/
-- audit-premise: PG24 Theorem 2 capacity and market-clearing scalar sorted-suffix endpoint source clauses
structure Theorem2ScalarMarketEndpointSourceModel
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (noiseLaw : MeasureTheory.Measure ℝ)
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (totalSupply alpha : ℝ) : Prop where
  capacity_open_bound :
    source_assumption_capacity_open_bound Mseq alpha
  scalar_market_endpoint_estimates :
    source_assumption_theorem2_scalar_market_endpoint_estimates
      Mseq noiseLaw cutoffOut (totalSupply := totalSupply)

/--
The positive capacity-regularity condition implies the weak upper-capacity
condition used by earlier proof-route rows.
-/
theorem source_assumption_capacity_upper_bound_of_open_bound
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {alpha : ℝ}
    (h : source_assumption_capacity_open_bound Mseq alpha) :
    source_assumption_capacity_upper_bound Mseq alpha := by
  filter_upwards [h] with C hC c
  exact (hC c).2

/--
Positive capacity regularity and the total-capacity normalization imply that
aggregate supply is positive.
-/
theorem source_assumption_total_capacity_sum_pos_of_open_bound
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {totalSupply alpha : ℝ}
    (hsum : source_assumption_total_capacity_sum Mseq totalSupply)
    (hopen : source_assumption_capacity_open_bound Mseq alpha) :
    0 < totalSupply := by
  have hevent : ∀ᶠ C : ℕ in atTop, 0 < totalSupply := by
    filter_upwards [hsum, hopen] with C hsumC hopenC
    rw [← hsumC]
    exact Finset.sum_pos
      (fun c _hc => (hopenC c).1)
      ⟨0, by simp⟩
  rcases eventually_atTop.1 hevent with ⟨N, hN⟩
  exact hN N le_rfl

/--
Nonnegative aggregate supply follows from the positive-capacity normalization.
-/
theorem source_assumption_total_capacity_sum_nonneg_of_open_bound
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {totalSupply alpha : ℝ}
    (hsum : source_assumption_total_capacity_sum Mseq totalSupply)
    (hopen : source_assumption_capacity_open_bound Mseq alpha) :
    0 ≤ totalSupply :=
  (source_assumption_total_capacity_sum_pos_of_open_bound hsum hopen).le

/--
The paper's Theorem 3 low-tail source control for admissible selected stable
matchings: the per-college lower endpoint tail estimates are small enough,
after multiplying by the chosen large-subset cardinality.
-/
-- audit-premise: eventually, card(C')*tailRate < epsilon and each selected-stable low endpoint tail is <= tailRate
abbrev source_assumption_selected_stable_indexed_low_tail_controls
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : MeasureTheory.Measure ℝ)
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (largeSubset : ∀ C : ℕ, Admissible C → Finset (Fin (C + 1)))
    (tailRate : ∀ C : ℕ, Admissible C → ℝ)
    (threshold : ∀ C : ℕ, Admissible C → ℝ)
    (epsilon : ℝ) : Prop :=
  (∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C,
      ((largeSubset C a).card : ℝ) * tailRate C a < epsilon) ∧
  (∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C, ∀ c ∈ largeSubset C a,
      AppliedModelingLib.Probability.upperTailMass noiseLaw
        (cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C a).1) (selected C a).2) c -
          (threshold C a - epsilon)) ≤
        tailRate C a)

/--
The paper's Theorem 3 low-tail source control for the single selected stable
matching sequence.
-/
-- audit-premise: eventually, card(C')*tailRate < epsilon and each selected-stable low endpoint tail is <= tailRate
abbrev source_assumption_selected_stable_scalar_low_tail_controls
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (selected :
      ∀ C : ℕ, { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : MeasureTheory.Measure ℝ)
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (largeSubset : ∀ C : ℕ, Finset (Fin (C + 1)))
    (tailRate : ℕ → ℝ)
    (threshold epsilon : ℝ) : Prop :=
  (∀ᶠ C : ℕ in atTop,
    ((largeSubset C).card : ℝ) * tailRate C < epsilon) ∧
  (∀ᶠ C : ℕ in atTop,
    ∀ c ∈ largeSubset C,
      AppliedModelingLib.Probability.upperTailMass noiseLaw
        (cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C).1) (selected C).2) c -
          (threshold - epsilon)) ≤
        tailRate C)

/--
Theorem 3 source cutoff-floor clause for the sorted suffix used as the large
coalition subset.
-/
-- audit-premise: eventually, every selected-stable cutoff in the sorted suffix is above the scalar lower cutoff floor
abbrev source_assumption_theorem3_suffix_cutoff_floor
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon : ℝ}
    (lowerCutoff : ∀ C : ℕ, Admissible C → ℝ) : Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C, ∀ c : Fin (C + 1),
      epsilonFloorSplitIndex (epsilon / 2) C ≤ (c : ℕ) →
        lowerCutoff C a ≤
          cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C a).1) (selected C a).2) c

/--
Theorem 3 cutoff-floor clause stated over all market-clearing cutoffs.

The selected-stable version is derived from this via the A-L supply/demand
bridge.
-/
-- audit-premise: eventually, every market-clearing cutoff in the sorted suffix is above the scalar lower cutoff floor
abbrev source_assumption_theorem3_suffix_market_cutoff_floor
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    {Admissible : ℕ → Type u}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon : ℝ}
    (lowerCutoff : ∀ C : ℕ, Admissible C → ℝ) : Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C, ∀ P : (Mseq C).Cutoff,
      (Mseq C).MarketClearing P →
        ∀ c : Fin (C + 1),
          epsilonFloorSplitIndex (epsilon / 2) C ≤ (c : ℕ) →
            lowerCutoff C a ≤ cutoffOut C P c

/--
Market-clearing cutoff-floor clauses imply the selected-stable form.
-/
theorem source_assumption_theorem3_suffix_cutoff_floor_of_market
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {epsilon : ℝ}
    {lowerCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (h :
      source_assumption_theorem3_suffix_market_cutoff_floor
        Mseq cutoffOut (epsilon := epsilon) lowerCutoff) :
    source_assumption_theorem3_suffix_cutoff_floor
      Mseq Iseq selected cutoffOut (epsilon := epsilon) lowerCutoff := by
  filter_upwards [h] with C hC a c hc
  exact
    hC a
      ((Iseq C).marketClearingCutoffOfStable
        (μ := (selected C a).1) (selected C a).2)
      ((Iseq C).marketClearingCutoffOfStable_marketClearing
        (μ := (selected C a).1) (selected C a).2)
      c hc

/--
Source sorted-index clause: the paper's `c = 0, ..., C` indexing is already
ordered by increasing cutoff.
-/
-- audit-premise: eventually, market-clearing cutoff coordinates are sorted by the paper's increasing-cutoff index convention
abbrev source_assumption_market_cutoff_index_sorted
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ) : Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
      ∀ i j : Fin (C + 1), (i : ℕ) ≤ (j : ℕ) →
        cutoffOut C P i ≤ cutoffOut C P j

/--
Selected-stable sorted-index clause: the paper's `c = 0, ..., C` indexing is
already ordered by increasing cutoff at the selected stable cutoff.
-/
-- audit-premise: eventually, selected-stable cutoff coordinates are sorted by the paper's increasing-cutoff index convention
abbrev source_assumption_selected_stable_cutoff_index_sorted
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ) : Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C,
      ∀ i j : Fin (C + 1), (i : ℕ) ≤ (j : ℕ) →
        cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C a).1) (selected C a).2) i ≤
        cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C a).1) (selected C a).2) j

/--
Market-level sorted indexing implies sorted indexing at the selected stable
cutoff, because the A-L supply/demand interface turns a stable matching into a
market-clearing cutoff.
-/
theorem source_assumption_selected_stable_cutoff_index_sorted_of_market
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    (h : source_assumption_market_cutoff_index_sorted Mseq cutoffOut) :
    source_assumption_selected_stable_cutoff_index_sorted
      Mseq Iseq selected cutoffOut := by
  filter_upwards [h] with C hC a i j hij
  exact
    hC
      ((Iseq C).marketClearingCutoffOfStable
        (μ := (selected C a).1) (selected C a).2)
      ((Iseq C).marketClearingCutoffOfStable_marketClearing
        (μ := (selected C a).1) (selected C a).2)
      i j hij

/-!
The next audit guardrail is intentionally concrete: it shows that the
selected-stable sorted-index clause above is not derivable from the abstract
`CutoffMarket` and `SupplyDemandInterface` APIs alone.  The source proof sorts
coalition cutoffs without loss of generality, so a full proof must transport the
economy through that relabeling instead of proving sortedness from these
abstract interfaces.
-/

def abstractUnsortedCutoffMarket (C : ℕ) :
    CutoffMarket PUnit (Fin (C + 1)) where
  Cutoff := PUnit
  Matching := PUnit
  demandAt := fun _ _ => none
  aggregateDemand := fun _ _ => 0
  capacity := fun _ => 0
  isStable := fun _ => True
  marketClearing := fun _ => True
  representedByCutoff := fun _ _ => True

theorem abstractUnsortedCutoffMarket_supplyDemandInterface (C : ℕ) :
    SupplyDemandInterface (abstractUnsortedCutoffMarket C) where
  stable_iff_exists_marketClearing_cutoff := by
    intro μ
    constructor
    · intro _hμ
      exact ⟨PUnit.unit, trivial, trivial⟩
    · intro _h
      trivial
  marketClearing_induces_stable := by
    intro P _hP
    exact ⟨PUnit.unit, trivial, trivial⟩

def abstractUnsortedSelectedStable (C : ℕ) (_a : PUnit) :
    { μ : (abstractUnsortedCutoffMarket C).Matching //
        (abstractUnsortedCutoffMarket C).Stable μ } :=
  ⟨PUnit.unit, trivial⟩

def abstractUnsortedCutoffOut (C : ℕ)
    (_P : (abstractUnsortedCutoffMarket C).Cutoff) (c : Fin (C + 1)) : ℝ :=
  if (c : ℕ) = 0 then 1 else 0

theorem source_assumption_selected_stable_cutoff_index_sorted_not_automatic :
    ¬ source_assumption_selected_stable_cutoff_index_sorted
        (fun C : ℕ => abstractUnsortedCutoffMarket C)
        (fun C : ℕ => abstractUnsortedCutoffMarket_supplyDemandInterface C)
        (fun C : ℕ => abstractUnsortedSelectedStable C)
        abstractUnsortedCutoffOut := by
  intro hsorted
  rcases Filter.eventually_atTop.1 hsorted with ⟨N, hN⟩
  let C : ℕ := max N 1
  have hN_le_C : N ≤ C := Nat.le_max_left N 1
  have hC_pos : 1 ≤ C := Nat.le_max_right N 1
  have hsortedC := hN C hN_le_C PUnit.unit
  let i : Fin (C + 1) := ⟨0, Nat.succ_pos C⟩
  let j : Fin (C + 1) := ⟨1, by omega⟩
  have hij : (i : ℕ) ≤ (j : ℕ) := by
    simp [i, j]
  have hbad := hsortedC i j hij
  norm_num [abstractUnsortedCutoffOut, i, j] at hbad

/--
Theorem 2 selected-stable sorted-index clause over the stable matchings used
directly in the paper-facing Theorem 2 statement.
-/
-- audit-premise: eventually, every selected stable cutoff in Theorem 2 is sorted by the paper's increasing-cutoff index convention
abbrev source_assumption_theorem2_selected_stable_cutoff_index_sorted
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ) :
    Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
      ∀ i j : Fin (C + 1), (i : ℕ) ≤ (j : ℕ) →
        cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := μ.1) μ.2) i ≤
        cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := μ.1) μ.2) j

/--
Market-level sorted indexing implies the Theorem 2 selected-stable sorted
indexing clause.
-/
theorem source_assumption_theorem2_selected_stable_cutoff_index_sorted_of_market
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    (h : source_assumption_market_cutoff_index_sorted Mseq cutoffOut) :
    source_assumption_theorem2_selected_stable_cutoff_index_sorted
      Mseq Iseq cutoffOut := by
  filter_upwards [h] with C hC μ i j hij
  exact
    hC
      ((Iseq C).marketClearingCutoffOfStable
        (μ := μ.1) μ.2)
      ((Iseq C).marketClearingCutoffOfStable_marketClearing
        (μ := μ.1) μ.2)
      i j hij

/--
First-large-index product lower-bound source surface for Theorem 2.

This is the paper-facing replacement for directly assuming the
capacity-overflow implication.  It exposes the remaining ingredients needed
by Lean's checked finite-product argument: the exponential prefix lower bound
is above total supply, and the low/high tail transfer holds on the sorted
prefix.  Lean derives the auxiliary bound
`(1 - epsilon) * sigma / (C + 1) <= 1` from `C -> infinity`.
-/
-- audit-premise: PG24 Theorem 2 first-large-index prefix product lower bound and low/high tail-ratio transfer
abbrev source_assumption_theorem2_first_large_index_product_tail_ratio_overflow_clause
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply : ℝ} : Prop :=
  ∀ vLow vHigh epsilon sigma, vLow < vHigh → 0 < epsilon → 0 < sigma →
    0 <
      1 - totalSupply - epsilon -
        (1 - Real.exp (-(2 * epsilon * sigma))) →
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          ∀ hsplit : epsilonFloorSplitIndex epsilon C < C + 1,
            totalSupply <
              (1 - epsilon) *
                (1 - Real.exp
                  (-(((indexPrefixSmall
                        (epsilonFloorSplitIndex epsilon C) C).card : ℝ) *
                    ((1 - epsilon) *
                      (sigma / ((C + 1 : ℕ) : ℝ)))))) ∧
            (∀ c ∈ indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C,
              (1 - epsilon) *
                  AppliedModelingLib.Probability.upperTailMass noiseLaw
                    (cutoffOut C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2) c - vHigh) ≤
                AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2) c - vLow))

/--
First-large-index product lower-bound source surface with the low/high tail
transfer reduced to a common diverging prefix cutoff floor.

Lean combines this source surface with long-tailedness of the noise law to
derive the tail-ratio transfer in
`source_assumption_theorem2_first_large_index_product_tail_ratio_overflow_clause`.
-/
-- audit-premise: PG24 Theorem 2 first-large-index prefix product lower bound plus a common diverging prefix cutoff floor
abbrev source_assumption_theorem2_first_large_index_product_cutoff_floor_overflow_clause
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply : ℝ} : Prop :=
  ∀ vLow vHigh epsilon sigma, vLow < vHigh → 0 < epsilon → 0 < sigma →
    0 <
      1 - totalSupply - epsilon -
        (1 - Real.exp (-(2 * epsilon * sigma))) →
      ∃ lowerCutoff : ℕ → ℝ,
        Tendsto (fun C : ℕ => lowerCutoff C - vHigh) atTop atTop ∧
        (∀ᶠ C : ℕ in atTop,
          ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
            ∀ c ∈ indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C,
              lowerCutoff C ≤
                cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := μ.1) μ.2) c) ∧
        (∀ᶠ C : ℕ in atTop,
          ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
            ∀ _hsplit : epsilonFloorSplitIndex epsilon C < C + 1,
              totalSupply <
                (1 - epsilon) *
                  (1 - Real.exp
                    (-(((indexPrefixSmall
                          (epsilonFloorSplitIndex epsilon C) C).card : ℝ) *
                      ((1 - epsilon) *
                        (sigma / ((C + 1 : ℕ) : ℝ)))))))

/--
First-large-index cutoff-floor source surface with the finite product lower
bound reduced to a scalar margin.

The scalar inequality is independent of the market size.  Lean uses the
eventual lower bound
`(epsilon / 2) * (C + 1) <= |indexPrefixSmall|` to recover the exact
finite-product lower bound required by
`source_assumption_theorem2_first_large_index_product_cutoff_floor_overflow_clause`.
-/
-- audit-premise: PG24 Theorem 2 first-large-index common diverging prefix cutoff floor plus scalar product margin
abbrev source_assumption_theorem2_first_large_index_scalar_cutoff_floor_overflow_clause
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply : ℝ} : Prop :=
  ∀ vLow vHigh epsilon sigma, vLow < vHigh → 0 < epsilon → 0 < sigma →
    0 <
      1 - totalSupply - epsilon -
        (1 - Real.exp (-(2 * epsilon * sigma))) →
      ∃ lowerCutoff : ℕ → ℝ,
        Tendsto (fun C : ℕ => lowerCutoff C - vHigh) atTop atTop ∧
        (∀ᶠ C : ℕ in atTop,
          ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
            ∀ c ∈ indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C,
              lowerCutoff C ≤
                cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := μ.1) μ.2) c) ∧
        totalSupply <
          (1 - epsilon) *
            (1 - Real.exp
              (-((epsilon / 2) * ((1 - epsilon) * sigma))))

/--
The scalar cutoff-floor source surface implies the finite product cutoff-floor
surface.  The proof is deterministic finite-cardinality algebra.
-/
theorem source_assumption_theorem2_first_large_index_product_cutoff_floor_overflow_clause_of_scalar
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {totalSupply : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (hscalar :
      source_assumption_theorem2_first_large_index_scalar_cutoff_floor_overflow_clause
        Mseq Iseq cutoffOut (totalSupply := totalSupply)) :
    source_assumption_theorem2_first_large_index_product_cutoff_floor_overflow_clause
      Mseq Iseq cutoffOut (totalSupply := totalSupply) := by
  intro vLow vHigh epsilon sigma hvStrict hepsilon hsigma hden
  rcases hscalar vLow vHigh epsilon sigma
      hvStrict hepsilon hsigma hden with
    ⟨lowerCutoff, hlower_atTop, hprefix_floor, hscalar_target⟩
  refine ⟨lowerCutoff, hlower_atTop, hprefix_floor, ?_⟩
  have heps_lt_one : epsilon < 1 := by
    have hS_eps_lt_one :
        totalSupply + epsilon < 1 :=
      theorem2_totalSupply_add_epsilon_lt_one_of_denominator_pos
        hepsilon hsigma hden
    linarith
  have hscale_nonneg : 0 ≤ 1 - epsilon := by
    linarith
  filter_upwards
    [indexPrefixSmall_card_eventually_half_mul_le
      epsilon hepsilon heps_lt_one] with
    C hcard μ hsplit
  have hdenC_pos : 0 < (((C + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos C
  have hmult_nonneg :
      0 ≤ (1 - epsilon) * (sigma / ((C + 1 : ℕ) : ℝ)) := by
    exact mul_nonneg hscale_nonneg
      (div_nonneg (le_of_lt hsigma) (le_of_lt hdenC_pos))
  have hcard_mul :
      (epsilon / 2) * (((C + 1 : ℕ) : ℝ)) *
          ((1 - epsilon) * (sigma / ((C + 1 : ℕ) : ℝ))) ≤
        ((indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C).card : ℝ) *
          ((1 - epsilon) * (sigma / ((C + 1 : ℕ) : ℝ))) :=
    mul_le_mul_of_nonneg_right hcard hmult_nonneg
  have hleft_eq :
      (epsilon / 2) * (((C + 1 : ℕ) : ℝ)) *
          ((1 - epsilon) * (sigma / ((C + 1 : ℕ) : ℝ))) =
        (epsilon / 2) * ((1 - epsilon) * sigma) := by
    field_simp [ne_of_gt hdenC_pos]
  have hA_le_B :
      (epsilon / 2) * ((1 - epsilon) * sigma) ≤
        ((indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C).card : ℝ) *
          ((1 - epsilon) * (sigma / ((C + 1 : ℕ) : ℝ))) := by
    rw [hleft_eq] at hcard_mul
    exact hcard_mul
  have hexp_le :
      Real.exp
          (-(((indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C).card : ℝ) *
            ((1 - epsilon) * (sigma / ((C + 1 : ℕ) : ℝ))))) ≤
        Real.exp (-((epsilon / 2) * ((1 - epsilon) * sigma))) :=
    Real.exp_le_exp.mpr (by linarith)
  have hone_sub_le :
      1 - Real.exp (-((epsilon / 2) * ((1 - epsilon) * sigma)) ) ≤
        1 - Real.exp
          (-(((indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C).card : ℝ) *
            ((1 - epsilon) * (sigma / ((C + 1 : ℕ) : ℝ))))) := by
    linarith
  exact lt_of_lt_of_le hscalar_target
    (mul_le_mul_of_nonneg_left hone_sub_le hscale_nonneg)

/--
The cutoff-floor product source surface implies the product-tail source
surface.  The only analytic step is the long-tail prefix transfer proved in
`MainTheorems.lean`.
-/
theorem source_assumption_theorem2_first_large_index_product_tail_ratio_overflow_clause_of_cutoff_floor
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {noiseLaw : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {totalSupply : ℝ}
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (hcutoff_floor :
      source_assumption_theorem2_first_large_index_product_cutoff_floor_overflow_clause
        Mseq Iseq cutoffOut (totalSupply := totalSupply)) :
    source_assumption_theorem2_first_large_index_product_tail_ratio_overflow_clause
      Mseq Iseq noiseLaw cutoffOut (totalSupply := totalSupply) := by
  intro vLow vHigh epsilon sigma hvStrict hepsilon hsigma hden
  rcases hcutoff_floor vLow vHigh epsilon sigma
      hvStrict hepsilon hsigma hden with
    ⟨lowerCutoff, hlower_atTop, hprefix_floor, htarget⟩
  have htail :
      ∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          ∀ c ∈ indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C,
            (1 - epsilon) *
                AppliedModelingLib.Probability.upperTailMass noiseLaw
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := μ.1) μ.2) c - vHigh) ≤
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := μ.1) μ.2) c - vLow) := by
    exact
      upperTailMass_tail_ratio_uniform_eventually_of_longTail_cutoff_floor
        (Admissible :=
          fun C : ℕ =>
            { μ : (Mseq C).Matching // (Mseq C).Stable μ })
        (noiseLaw := noiseLaw)
        hlong
        (active := fun C _μ =>
          indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
        (cutoff := fun C μ c =>
          cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := μ.1) μ.2) c)
        (lowerCutoff := lowerCutoff)
        (vLow := vLow)
        (vHigh := vHigh)
        (epsilon := epsilon)
        hvStrict hepsilon hlower_atTop hprefix_floor
  filter_upwards [htarget, htail] with C htargetC htailC μ hsplit
  exact ⟨htargetC μ hsplit, htailC μ⟩

/--
The product lower-bound source surface plus sorted selected-stable cutoffs
implies the first-large-index capacity-overflow implication used by the
current Theorem 2 local-event source package.
-/
theorem source_assumption_theorem2_first_large_index_capacity_overflow_implication_of_product_tail_ratio
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {noiseLaw : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {totalSupply : ℝ}
    (htotalSupply_nonneg : 0 ≤ totalSupply)
    (hsorted :
      source_assumption_theorem2_selected_stable_cutoff_index_sorted
        Mseq Iseq cutoffOut)
    (hproduct :
      source_assumption_theorem2_first_large_index_product_tail_ratio_overflow_clause
        Mseq Iseq noiseLaw cutoffOut (totalSupply := totalSupply)) :
    ∀ vLow vHigh epsilon sigma, vLow < vHigh → 0 < epsilon → 0 < sigma →
      0 <
        1 - totalSupply - epsilon -
          (1 - Real.exp (-(2 * epsilon * sigma))) →
        ∀ᶠ C : ℕ in atTop,
          ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
            ∀ hsplit : epsilonFloorSplitIndex epsilon C < C + 1,
              sigma / ((C + 1 : ℕ) : ℝ) <
                  AppliedModelingLib.Probability.upperTailMass noiseLaw
                    (cutoffOut C
                      ((Iseq C).marketClearingCutoffOfStable
                        (μ := μ.1) μ.2)
                      (⟨epsilonFloorSplitIndex epsilon C, hsplit⟩ :
                        Fin (C + 1)) -
                      vHigh) →
                totalSupply <
                  (1 - epsilon) *
                    cutoffAffordanceProbability
                      (MeasureTheory.Measure.pi
                        (fun _ : Fin (C + 1) => noiseLaw))
                      (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                      vLow
                      (cutoffOut C
                        ((Iseq C).marketClearingCutoffOfStable
                          (μ := μ.1) μ.2)) := by
  intro vLow vHigh epsilon sigma hvStrict hepsilon hsigma hden
  have hS_eps_lt_one :
      totalSupply + epsilon < 1 :=
    theorem2_totalSupply_add_epsilon_lt_one_of_denominator_pos
      hepsilon hsigma hden
  have hscale : 0 ≤ 1 - epsilon := by
    linarith
  filter_upwards
    [hsorted,
      hproduct vLow vHigh epsilon sigma hvStrict hepsilon hsigma hden,
      theorem2_eventually_scaled_sigma_div_succ_le_one epsilon sigma] with
    C hsortedC hproductC hq_le_one μ hsplit hsplit_tail
  rcases hproductC μ hsplit with
    ⟨htarget, htail_ratio⟩
  let P :=
    (Iseq C).marketClearingCutoffOfStable (μ := μ.1) μ.2
  exact
    theorem2_first_large_index_capacity_overflow_implication_of_product_tail_ratio
      (noiseLaw := noiseLaw)
      (cutoff := cutoffOut C P)
      (hsplit := hsplit)
      (epsilon := epsilon)
      (sigma := sigma)
      (totalSupply := totalSupply)
      (vLow := vLow)
      (vHigh := vHigh)
      hscale (le_of_lt hsigma) hq_le_one htarget
      (indexPrefixSmall_cutoff_le_split_of_sorted
        (cutoff := cutoffOut C P) hsplit (hsortedC μ))
      htail_ratio hsplit_tail

/--
Theorem 3 source low-count clause: eventually fewer than the deleted prefix
many market-clearing cutoffs lie below the scalar lower floor.
-/
-- audit-premise: eventually, at most the deleted prefix many market-clearing cutoffs are below the Theorem 3 scalar lower floor
abbrev source_assumption_theorem3_suffix_market_low_cutoff_count
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    {Admissible : ℕ → Type u}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon : ℝ}
    (lowerCutoff : ∀ C : ℕ, Admissible C → ℝ) : Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C, ∀ P : (Mseq C).Cutoff,
      (Mseq C).MarketClearing P →
        (lowCutoffIndexSet (cutoffOut C P) (lowerCutoff C a)).card ≤
          epsilonFloorSplitIndex (epsilon / 2) C

/--
Theorem 3 selected-stable low-count clause: eventually fewer than the deleted
prefix many selected-stable cutoffs lie below the scalar lower floor.
-/
-- audit-premise: eventually, at most the deleted prefix many selected-stable cutoffs are below the Theorem 3 scalar lower floor
abbrev source_assumption_theorem3_suffix_selected_stable_low_cutoff_count
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon : ℝ}
    (lowerCutoff : ∀ C : ℕ, Admissible C → ℝ) : Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C,
      (lowCutoffIndexSet
          (cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C a).1) (selected C a).2))
          (lowerCutoff C a)).card ≤
        epsilonFloorSplitIndex (epsilon / 2) C

/--
Generic low-cutoff capacity-contradiction source clause.

This is the paper's market-clearing contradiction isolated from the finite
sorted-index step: if too many cutoffs lie below a scalar floor, the source
model supplies an outcome event whose mass exceeds total supply and whose
outcomes all match somewhere.
-/
-- audit-premise: if too many market-clearing cutoffs are below the floor, the paper constructs a matched event with mass exceeding total supply
abbrev source_assumption_market_low_cutoff_capacity_contradiction
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    {Admissible : ℕ → Type u}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (splitIndex : ℕ → ℕ)
    (lowerCutoff : ∀ C : ℕ, Admissible C → ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    (totalSupply : ℝ) : Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C, ∀ P : (Mseq C).Cutoff,
      (Mseq C).MarketClearing P →
        splitIndex C <
          (lowCutoffIndexSet (cutoffOut C P) (lowerCutoff C a)).card →
          ∃ event : OutcomeSeq C → Prop,
            totalSupply <
              AppliedModelingLib.Matching.eventMass (outcomeLaw C P) event ∧
            ∀ ω : OutcomeSeq C,
              event ω →
                AppliedModelingLib.Matching.chosenInActive
                  (chosenCollege C P)
                  (Finset.univ : Finset (Fin (C + 1))) ω

/--
Selected-stable capacity-contradiction source clause.

This is the same high-mass matched-event contradiction, restricted to the
selected stable cutoff used by the paper-facing theorem route.
-/
-- audit-premise: if too many selected-stable cutoffs are below the floor, the paper constructs a matched event with mass exceeding total supply
abbrev source_assumption_selected_stable_low_cutoff_capacity_contradiction
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (splitIndex : ℕ → ℕ)
    (lowerCutoff : ∀ C : ℕ, Admissible C → ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    (totalSupply : ℝ) : Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C,
      splitIndex C <
        (lowCutoffIndexSet
          (cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C a).1) (selected C a).2))
          (lowerCutoff C a)).card →
        ∃ event : OutcomeSeq C → Prop,
          totalSupply <
            AppliedModelingLib.Matching.eventMass
              (outcomeLaw C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2))
              event ∧
          ∀ ω : OutcomeSeq C,
            event ω →
              AppliedModelingLib.Matching.chosenInActive
                (chosenCollege C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))
                (Finset.univ : Finset (Fin (C + 1))) ω

/--
Analytic low-cutoff probability clause: if too many cutoffs lie below a scalar
floor, the iid no-crossing power bound is already below `1 - totalSupply`.
-/
-- audit-premise: if too many market-clearing cutoffs are below the floor, the iid low-cutoff-set crossing probability lower bound exceeds total supply
abbrev source_assumption_market_low_cutoff_pow_exceeds_supply
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (noiseLaw : MeasureTheory.Measure ℝ)
    {Admissible : ℕ → Type u}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (splitIndex : ℕ → ℕ)
    (lowerCutoff eventValue : ∀ C : ℕ, Admissible C → ℝ)
    (totalSupply : ℝ) : Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C, ∀ P : (Mseq C).Cutoff,
      (Mseq C).MarketClearing P →
        splitIndex C <
          (lowCutoffIndexSet (cutoffOut C P) (lowerCutoff C a)).card →
          totalSupply <
            1 -
              (AppliedModelingLib.Probability.lowerCDFMass noiseLaw
                (lowerCutoff C a - eventValue C a)) ^
                (lowCutoffIndexSet
                  (cutoffOut C P) (lowerCutoff C a)).card

/--
Analytic split-index low-CDF power clause: it is enough to prove the
constant-cutoff crossing bound at the first cardinality strictly above the
deleted prefix.  Monotonicity of powers on `[0, 1]` then handles any larger
low-cutoff set.
-/
-- audit-premise: the split-index iid low-cutoff crossing lower bound exceeds total supply
abbrev source_assumption_market_low_cutoff_split_pow_exceeds_supply
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (noiseLaw : MeasureTheory.Measure ℝ)
    {Admissible : ℕ → Type u}
    (splitIndex : ℕ → ℕ)
    (lowerCutoff eventValue : ∀ C : ℕ, Admissible C → ℝ)
    (totalSupply : ℝ) : Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C,
      totalSupply <
        1 -
          (AppliedModelingLib.Probability.lowerCDFMass noiseLaw
            (lowerCutoff C a - eventValue C a)) ^
            (splitIndex C + 1)

/--
Analytic split-index upper-tail power clause.  This is the same iid crossing
lower bound as `source_assumption_market_low_cutoff_split_pow_exceeds_supply`,
but stated with the paper's strict upper-tail probability rather than the
closed lower-CDF convention used by the product formula.
-/
-- audit-premise: the split-index iid strict upper-tail crossing lower bound exceeds total supply
abbrev source_assumption_market_low_cutoff_upper_tail_split_pow_exceeds_supply
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (noiseLaw : MeasureTheory.Measure ℝ)
    {Admissible : ℕ → Type u}
    (splitIndex : ℕ → ℕ)
    (lowerCutoff eventValue : ∀ C : ℕ, Admissible C → ℝ)
    (totalSupply : ℝ) : Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C,
      totalSupply <
        1 -
          (1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
            (lowerCutoff C a - eventValue C a)) ^
            (splitIndex C + 1)

/--
A scalar lower bound on the strict upper tail is enough to discharge the
split-index strict-tail crossing clause, provided the resulting scalar
crossing inequality is eventually large enough.  This bridge is intentionally
separate from the paper-facing assumptions: it reduces the remaining analytic
obligation without treating the strict-tail lower bound as a source axiom.
-/
theorem source_assumption_market_low_cutoff_upper_tail_split_pow_exceeds_supply_of_scalar_tail_lower_bound
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {noiseLaw : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {Admissible : ℕ → Type u}
    {splitIndex : ℕ → ℕ}
    {lowerCutoff eventValue : ∀ C : ℕ, Admissible C → ℝ}
    {scalarTail : ∀ C : ℕ, Admissible C → ℝ}
    {totalSupply : ℝ}
    (htail :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          scalarTail C a ≤
            AppliedModelingLib.Probability.upperTailMass noiseLaw
              (lowerCutoff C a - eventValue C a))
    (hcross :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          totalSupply <
            1 - (1 - scalarTail C a) ^ (splitIndex C + 1)) :
    source_assumption_market_low_cutoff_upper_tail_split_pow_exceeds_supply
      Mseq noiseLaw splitIndex lowerCutoff eventValue totalSupply := by
  filter_upwards [htail, hcross] with C htailC hcrossC a
  let tail : ℝ :=
    AppliedModelingLib.Probability.upperTailMass noiseLaw
      (lowerCutoff C a - eventValue C a)
  have htail_le_one : tail ≤ 1 := by
    simpa [tail] using
      (AppliedModelingLib.Probability.upperTailMass_le_one noiseLaw
        (lowerCutoff C a - eventValue C a))
  have htail_lower : scalarTail C a ≤ tail := by
    simpa [tail] using htailC a
  have hbase_nonneg : 0 ≤ 1 - tail := by
    linarith
  have hbase_le : 1 - tail ≤ 1 - scalarTail C a := by
    linarith
  have hpow_le :
      (1 - tail) ^ (splitIndex C + 1) ≤
        (1 - scalarTail C a) ^ (splitIndex C + 1) :=
    pow_le_pow_left₀ hbase_nonneg hbase_le (splitIndex C + 1)
  have hsub_le :
      1 - (1 - scalarTail C a) ^ (splitIndex C + 1) ≤
        1 - (1 - tail) ^ (splitIndex C + 1) := by
    simpa using (sub_le_sub_left hpow_le 1)
  exact lt_of_lt_of_le (hcrossC a) hsub_le

/--
For a scalar crossing probability `p ∈ [0,1]`, the no-crossing power is bounded
by the exponential relaxation `exp (-n*p)`.
-/
theorem one_sub_pow_le_exp_neg_nat_mul
    {p : ℝ} (n : ℕ) (hp_nonneg : 0 ≤ p) (hp_le_one : p ≤ 1) :
    (1 - p) ^ n ≤ Real.exp (-((n : ℝ) * p)) := by
  have _hp_nonneg : 0 ≤ p := hp_nonneg
  have hbase_nonneg : 0 ≤ 1 - p := by
    linarith
  have hbase_le_exp : 1 - p ≤ Real.exp (-p) :=
    Real.one_sub_le_exp_neg p
  have hpow :
      (1 - p) ^ n ≤ (Real.exp (-p)) ^ n :=
    pow_le_pow_left₀ hbase_nonneg hbase_le_exp n
  have hexp_pow :
      (Real.exp (-p)) ^ n = Real.exp (-((n : ℝ) * p)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simpa [hexp_pow] using hpow

/--
The exponential relaxation is a sufficient scalar crossing condition for the
split-index strict-tail clause.
-/
theorem source_assumption_market_low_cutoff_upper_tail_split_pow_exceeds_supply_of_scalar_tail_lower_bound_exp
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {noiseLaw : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {Admissible : ℕ → Type u}
    {splitIndex : ℕ → ℕ}
    {lowerCutoff eventValue : ∀ C : ℕ, Admissible C → ℝ}
    {scalarTail : ∀ C : ℕ, Admissible C → ℝ}
    {totalSupply : ℝ}
    (htail :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          scalarTail C a ≤
            AppliedModelingLib.Probability.upperTailMass noiseLaw
              (lowerCutoff C a - eventValue C a))
    (hscalar_nonneg :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, 0 ≤ scalarTail C a)
    (hscalar_le_one :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, scalarTail C a ≤ 1)
    (hcross_exp :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          totalSupply <
            1 - Real.exp (-(((splitIndex C + 1 : ℕ) : ℝ) *
              scalarTail C a))) :
    source_assumption_market_low_cutoff_upper_tail_split_pow_exceeds_supply
      Mseq noiseLaw splitIndex lowerCutoff eventValue totalSupply := by
  refine
    source_assumption_market_low_cutoff_upper_tail_split_pow_exceeds_supply_of_scalar_tail_lower_bound
      (Mseq := Mseq) (noiseLaw := noiseLaw) (splitIndex := splitIndex)
      (lowerCutoff := lowerCutoff) (eventValue := eventValue)
      (scalarTail := scalarTail) htail ?_
  filter_upwards [hscalar_nonneg, hscalar_le_one, hcross_exp] with
    C hnonnegC hleC hcrossC a
  have hpow_le :
      (1 - scalarTail C a) ^ (splitIndex C + 1) ≤
        Real.exp (-(((splitIndex C + 1 : ℕ) : ℝ) * scalarTail C a)) :=
    one_sub_pow_le_exp_neg_nat_mul
      (splitIndex C + 1) (hnonnegC a) (hleC a)
  have hsub_le :
      1 - Real.exp (-(((splitIndex C + 1 : ℕ) : ℝ) *
          scalarTail C a)) ≤
        1 - (1 - scalarTail C a) ^ (splitIndex C + 1) := by
    simpa using (sub_le_sub_left hpow_le 1)
  exact lt_of_lt_of_le (hcrossC a) hsub_le

/--
The paper's floor split has the expected positive first-order mass: deleting
`floor(delta * (C+1))` coordinates and then taking the first omitted coordinate
gives an exponent strictly larger than `delta * tau` when the one-coordinate
tail lower bound is `tau / (C+1)`.
-/
theorem epsilonFloorSplitIndex_add_one_mul_const_div_nat_succ_gt
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
The split-index exponential crossing target follows from a static supply gap.
This records the exact extra inequality needed after the floor-index arithmetic:
it is not a consequence of `totalSupply < 1` alone.
-/
theorem epsilonFloorSplitIndex_exp_supply_gap_of_static_gap
    {Admissible : ℕ → Type u}
    {delta tau totalSupply : ℝ}
    (hdelta_pos : 0 < delta) (htau_pos : 0 < tau)
    (hgap : totalSupply < 1 - Real.exp (-(delta * tau))) :
    ∀ᶠ C : ℕ in atTop,
      ∀ _a : Admissible C,
        totalSupply <
          1 - Real.exp
            (-(((epsilonFloorSplitIndex delta C + 1 : ℕ) : ℝ) *
              (tau / (((C + 1 : ℕ) : ℝ))))) := by
  exact Filter.Eventually.of_forall (fun C a => by
    have hprod :
        delta * tau <
          (((epsilonFloorSplitIndex delta C + 1 : ℕ) : ℝ) *
            (tau / (((C + 1 : ℕ) : ℝ)))) :=
      epsilonFloorSplitIndex_add_one_mul_const_div_nat_succ_gt
        hdelta_pos htau_pos C
    have hexp_le :
        Real.exp
            (-(((epsilonFloorSplitIndex delta C + 1 : ℕ) : ℝ) *
              (tau / (((C + 1 : ℕ) : ℝ))))) ≤
          Real.exp (-(delta * tau)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hsub_le :
        1 - Real.exp (-(delta * tau)) ≤
          1 - Real.exp
            (-(((epsilonFloorSplitIndex delta C + 1 : ℕ) : ℝ) *
              (tau / (((C + 1 : ℕ) : ℝ))))) := by
      linarith
    exact lt_of_lt_of_le hgap hsub_le)

/--
The source-facing strict upper-tail split-power clause implies the lower-CDF
split-power clause used by the existing finite-product bridge.
-/
theorem source_assumption_market_low_cutoff_split_pow_exceeds_supply_of_upper_tail_split_pow
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {noiseLaw : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {Admissible : ℕ → Type u}
    {splitIndex : ℕ → ℕ}
    {lowerCutoff eventValue : ∀ C : ℕ, Admissible C → ℝ}
    {totalSupply : ℝ}
    (h :
      source_assumption_market_low_cutoff_upper_tail_split_pow_exceeds_supply
        Mseq noiseLaw splitIndex lowerCutoff eventValue totalSupply) :
    source_assumption_market_low_cutoff_split_pow_exceeds_supply
      Mseq noiseLaw splitIndex lowerCutoff eventValue totalSupply := by
  filter_upwards [h] with C hC a
  have hsum :=
    AppliedModelingLib.Probability.lowerCDFMass_add_upperTailMass_eq_one noiseLaw
      (lowerCutoff C a - eventValue C a)
  have hrewrite :
      AppliedModelingLib.Probability.lowerCDFMass noiseLaw
          (lowerCutoff C a - eventValue C a) =
        1 - AppliedModelingLib.Probability.upperTailMass noiseLaw
          (lowerCutoff C a - eventValue C a) := by
    linarith
  simpa [hrewrite] using hC a

/--
The split-index low-CDF power clause implies the full low-cutoff-set clause
used by the capacity contradiction: if the low set has more than `splitIndex`
members, its no-crossing power is no larger than the split-index power.
-/
theorem source_assumption_market_low_cutoff_pow_exceeds_supply_of_split_pow
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {noiseLaw : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {Admissible : ℕ → Type u}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {splitIndex : ℕ → ℕ}
    {lowerCutoff eventValue : ∀ C : ℕ, Admissible C → ℝ}
    {totalSupply : ℝ}
    (h :
      source_assumption_market_low_cutoff_split_pow_exceeds_supply
        Mseq noiseLaw splitIndex lowerCutoff eventValue totalSupply) :
    source_assumption_market_low_cutoff_pow_exceeds_supply
      Mseq noiseLaw cutoffOut splitIndex lowerCutoff eventValue
      totalSupply := by
  filter_upwards [h] with C hC a P _hP hlt
  let active : Finset (Fin (C + 1)) :=
    lowCutoffIndexSet (cutoffOut C P) (lowerCutoff C a)
  let x : ℝ :=
    AppliedModelingLib.Probability.lowerCDFMass noiseLaw
      (lowerCutoff C a - eventValue C a)
  have hx_nonneg : 0 ≤ x := by
    simpa [x] using
      (AppliedModelingLib.Probability.lowerCDFMass_nonneg noiseLaw
        (lowerCutoff C a - eventValue C a))
  have hx_le_one : x ≤ 1 := by
    simpa [x] using
      (AppliedModelingLib.Probability.lowerCDFMass_le_one noiseLaw
        (lowerCutoff C a - eventValue C a))
  have hcard_le : splitIndex C + 1 ≤ active.card :=
    Nat.succ_le_of_lt hlt
  have hpow_le :
      x ^ active.card ≤ x ^ (splitIndex C + 1) :=
    pow_right_anti₀ hx_nonneg hx_le_one hcard_le
  have hsub_le :
      1 - x ^ (splitIndex C + 1) ≤ 1 - x ^ active.card := by
    simpa using (sub_le_sub_left hpow_le 1)
  exact lt_of_lt_of_le (hC a) hsub_le

/--
Outcome-model bridge from cutoff-affordance probabilities to matched events.

This is the source semantics that the outcome law includes the relevant
applicant/noise population and that an applicant who can afford an active
college is matched somewhere.
-/
-- audit-premise: market-level cutoff-affordance probability is represented by an outcome event whose outcomes are matched somewhere
abbrev source_assumption_market_affordance_event_bridge
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (noiseLaw : MeasureTheory.Measure ℝ)
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1))) :
    Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
      ∀ active : Finset (Fin (C + 1)), ∀ v : ℝ,
        ∃ event : OutcomeSeq C → Prop,
          cutoffAffordanceProbability
              (MeasureTheory.Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              active v (cutoffOut C P) ≤
            AppliedModelingLib.Matching.eventMass (outcomeLaw C P) event ∧
          ∀ ω : OutcomeSeq C,
            event ω →
              AppliedModelingLib.Matching.chosenInActive
                (chosenCollege C P)
                (Finset.univ : Finset (Fin (C + 1))) ω

/--
Integrated low-cutoff probability clause matching PG24 Lemma 11: if too many
market-clearing cutoffs are below a scalar floor, the value-integrated
probability of affording one of those low-cutoff colleges exceeds total supply.
-/
-- audit-premise: if too many market-clearing cutoffs are below the floor, the value-integrated probability of affording that low-cutoff block exceeds total supply
abbrev source_assumption_market_low_cutoff_integral_exceeds_supply
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (noiseLaw : MeasureTheory.Measure ℝ)
    {Admissible : ℕ → Type u}
    (valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ)
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (splitIndex : ℕ → ℕ)
    (lowerCutoff : ∀ C : ℕ, Admissible C → ℝ)
    (totalSupply : ℝ) : Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C, ∀ P : (Mseq C).Cutoff,
      (Mseq C).MarketClearing P →
        splitIndex C <
          (lowCutoffIndexSet (cutoffOut C P) (lowerCutoff C a)).card →
          totalSupply <
            ∫ v : ℝ,
              cutoffAffordanceProbability
                (MeasureTheory.Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (lowCutoffIndexSet (cutoffOut C P) (lowerCutoff C a))
                v (cutoffOut C P) ∂(valueLaw C a)

/--
Selected-stable low-cutoff probability clause matching PG24 Lemma 11 at the
only cutoff used in the paper-facing theorem route.
-/
-- audit-premise: if too many selected-stable cutoffs are below the floor, the value-integrated probability of affording that low-cutoff block exceeds total supply
abbrev source_assumption_selected_stable_low_cutoff_integral_exceeds_supply
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : MeasureTheory.Measure ℝ)
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ)
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (splitIndex : ℕ → ℕ)
    (lowerCutoff : ∀ C : ℕ, Admissible C → ℝ)
    (totalSupply : ℝ) : Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C,
      splitIndex C <
        (lowCutoffIndexSet
          (cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C a).1) (selected C a).2))
          (lowerCutoff C a)).card →
        totalSupply <
          ∫ v : ℝ,
            cutoffAffordanceProbability
              (MeasureTheory.Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (lowCutoffIndexSet
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := (selected C a).1) (selected C a).2))
                (lowerCutoff C a))
              v
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2))
              ∂(valueLaw C a)

/--
Market-level value laws are probability measures.
-/
-- audit-premise: every market-level applicant value law is a probability measure
abbrev source_assumption_market_value_probability
    {Admissible : ℕ → Type u}
    (valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ) : Prop :=
  ∀ C : ℕ, ∀ a : Admissible C,
    MeasureTheory.IsProbabilityMeasure (valueLaw C a)

/--
Market-level value laws have finite mass.
-/
-- audit-premise: every market-level applicant value law has finite mass
abbrev source_assumption_market_value_finite
    {Admissible : ℕ → Type u}
    (valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ) : Prop :=
  ∀ C : ℕ, ∀ a : Admissible C,
    MeasureTheory.IsFiniteMeasure (valueLaw C a)

theorem source_assumption_market_value_finite_of_probability
    {Admissible : ℕ → Type u}
    {valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ}
    (hprob : source_assumption_market_value_probability valueLaw) :
    source_assumption_market_value_finite valueLaw := by
  intro C a
  haveI : MeasureTheory.IsProbabilityMeasure (valueLaw C a) := hprob C a
  infer_instance

/--
Constant-cutoff integral lower-bound clause matching the final inequality in
PG24 Lemma 11: if too many cutoffs are below the scalar floor, the integral of
the constant-cutoff maximum-crossing lower bound exceeds total supply.
-/
-- audit-premise: if too many market-clearing cutoffs are below the floor, the constant-cutoff maximum-crossing integral lower bound exceeds total supply
abbrev source_assumption_market_low_cutoff_floor_pow_integral_exceeds_supply
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (noiseLaw : MeasureTheory.Measure ℝ)
    {Admissible : ℕ → Type u}
    (valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ)
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (splitIndex : ℕ → ℕ)
    (lowerCutoff : ∀ C : ℕ, Admissible C → ℝ)
    (totalSupply : ℝ) : Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C, ∀ P : (Mseq C).Cutoff,
      (Mseq C).MarketClearing P →
        splitIndex C <
          (lowCutoffIndexSet (cutoffOut C P) (lowerCutoff C a)).card →
          totalSupply <
            ∫ v : ℝ,
              1 -
                (AppliedModelingLib.Probability.lowerCDFMass noiseLaw
                  (lowerCutoff C a - v)) ^
                  (lowCutoffIndexSet
                    (cutoffOut C P) (lowerCutoff C a)).card
              ∂(valueLaw C a)

/--
Region/CDF lower-bound form of the PG24 Lemma 11 floor-power integral.

Instead of assuming the displayed floor-power integral directly, this source
clause exposes a value region and a scalar CDF cap on that region.  The shared
matching-affordability library then proves that the integral exceeds supply.
-/
-- audit-premise: if too many market-clearing cutoffs are below the floor, a value region with a uniform CDF cap makes the constant-cutoff maximum-crossing lower bound exceed supply
abbrev source_assumption_market_low_cutoff_floor_region_bound_exceeds_supply
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (noiseLaw : MeasureTheory.Measure ℝ)
    {Admissible : ℕ → Type u}
    (valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ)
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (splitIndex : ℕ → ℕ)
    (lowerCutoff : ∀ C : ℕ, Admissible C → ℝ)
    (totalSupply : ℝ) : Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C, ∀ P : (Mseq C).Cutoff,
      (Mseq C).MarketClearing P →
        splitIndex C <
          (lowCutoffIndexSet (cutoffOut C P) (lowerCutoff C a)).card →
          ∃ region : Set ℝ, ∃ q : ℝ,
            MeasurableSet region ∧
            0 ≤ q ∧
            (∀ v : ℝ, v ∈ region →
              AppliedModelingLib.Probability.lowerCDFMass noiseLaw
                (lowerCutoff C a - v) ≤ q) ∧
            totalSupply <
              (1 - q ^
                (lowCutoffIndexSet
                  (cutoffOut C P) (lowerCutoff C a)).card) *
                (valueLaw C a).real region

/--
Split-index form of the PG24 Lemma 11 region/CDF lower bound.

The source proof only needs to certify the value-region lower bound at the
deleted-prefix threshold.  Lean then uses the contradiction hypothesis
`splitIndex C < lowCutoffCount` and monotonicity of powers on `[0,1]` to lift
the bound to the actual low-cutoff block cardinality.
-/
-- audit-premise: if too many market-clearing cutoffs are below the floor, a value region with a uniform CDF cap makes the split-index maximum-crossing lower bound exceed supply
abbrev source_assumption_market_low_cutoff_floor_split_region_bound_exceeds_supply
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (noiseLaw : MeasureTheory.Measure ℝ)
    {Admissible : ℕ → Type u}
    (valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ)
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (splitIndex : ℕ → ℕ)
    (lowerCutoff : ∀ C : ℕ, Admissible C → ℝ)
    (totalSupply : ℝ) : Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C, ∀ P : (Mseq C).Cutoff,
      (Mseq C).MarketClearing P →
        splitIndex C <
          (lowCutoffIndexSet (cutoffOut C P) (lowerCutoff C a)).card →
          ∃ region : Set ℝ, ∃ q : ℝ,
            MeasurableSet region ∧
            0 ≤ q ∧
            q ≤ 1 ∧
            (∀ v : ℝ, v ∈ region →
              AppliedModelingLib.Probability.lowerCDFMass noiseLaw
                (lowerCutoff C a - v) ≤ q) ∧
            totalSupply <
              (1 - q ^ (splitIndex C + 1)) *
                (valueLaw C a).real region

/--
Selected-stable constant-cutoff integral lower-bound clause matching the final
inequality in PG24 Lemma 11 at the selected cutoff.
-/
-- audit-premise: if too many selected-stable cutoffs are below the floor, the constant-cutoff maximum-crossing integral lower bound exceeds total supply
abbrev source_assumption_selected_stable_low_cutoff_floor_pow_integral_exceeds_supply
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : MeasureTheory.Measure ℝ)
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ)
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (splitIndex : ℕ → ℕ)
    (lowerCutoff : ∀ C : ℕ, Admissible C → ℝ)
    (totalSupply : ℝ) : Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C,
      splitIndex C <
        (lowCutoffIndexSet
          (cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C a).1) (selected C a).2))
          (lowerCutoff C a)).card →
        totalSupply <
          ∫ v : ℝ,
            1 -
              (AppliedModelingLib.Probability.lowerCDFMass noiseLaw
                (lowerCutoff C a - v)) ^
                (lowCutoffIndexSet
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2))
                (lowerCutoff C a)).card
            ∂(valueLaw C a)

/--
Selected-stable region/CDF lower-bound form of the PG24 Lemma 11 floor-power
integral.
-/
-- audit-premise: if too many selected-stable cutoffs are below the floor, a value region with a uniform CDF cap makes the constant-cutoff maximum-crossing lower bound exceed supply
abbrev source_assumption_selected_stable_low_cutoff_floor_region_bound_exceeds_supply
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : MeasureTheory.Measure ℝ)
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ)
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (splitIndex : ℕ → ℕ)
    (lowerCutoff : ∀ C : ℕ, Admissible C → ℝ)
    (totalSupply : ℝ) : Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C,
      splitIndex C <
        (lowCutoffIndexSet
          (cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C a).1) (selected C a).2))
          (lowerCutoff C a)).card →
        ∃ region : Set ℝ, ∃ q : ℝ,
          MeasurableSet region ∧
          0 ≤ q ∧
          (∀ v : ℝ, v ∈ region →
            AppliedModelingLib.Probability.lowerCDFMass noiseLaw
              (lowerCutoff C a - v) ≤ q) ∧
            totalSupply <
              (1 - q ^
                (lowCutoffIndexSet
                  (cutoffOut C
                    ((Iseq C).marketClearingCutoffOfStable
                      (μ := (selected C a).1) (selected C a).2))
                  (lowerCutoff C a)).card) *
                (valueLaw C a).real region

/--
Selected-stable split-index form of the PG24 Lemma 11 region/CDF lower bound.
-/
-- audit-premise: if too many selected-stable cutoffs are below the floor, a value region with a uniform CDF cap makes the split-index maximum-crossing lower bound exceed supply
abbrev source_assumption_selected_stable_low_cutoff_floor_split_region_bound_exceeds_supply
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : MeasureTheory.Measure ℝ)
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ)
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (splitIndex : ℕ → ℕ)
    (lowerCutoff : ∀ C : ℕ, Admissible C → ℝ)
    (totalSupply : ℝ) : Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C,
      splitIndex C <
        (lowCutoffIndexSet
          (cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C a).1) (selected C a).2))
          (lowerCutoff C a)).card →
        ∃ region : Set ℝ, ∃ q : ℝ,
          MeasurableSet region ∧
          0 ≤ q ∧
          q ≤ 1 ∧
          (∀ v : ℝ, v ∈ region →
            AppliedModelingLib.Probability.lowerCDFMass noiseLaw
              (lowerCutoff C a - v) ≤ q) ∧
          totalSupply <
            (1 - q ^ (splitIndex C + 1)) *
              (valueLaw C a).real region

/--
The split-index region/CDF bound implies the original market-level
region-bound clause.
-/
theorem source_assumption_market_low_cutoff_floor_region_bound_exceeds_supply_of_split_region_bound
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {noiseLaw : MeasureTheory.Measure ℝ}
    {Admissible : ℕ → Type u}
    {valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {splitIndex : ℕ → ℕ}
    {lowerCutoff : ∀ C : ℕ, Admissible C → ℝ}
    {totalSupply : ℝ}
    (h :
      source_assumption_market_low_cutoff_floor_split_region_bound_exceeds_supply
        Mseq noiseLaw valueLaw cutoffOut splitIndex lowerCutoff
        totalSupply) :
    source_assumption_market_low_cutoff_floor_region_bound_exceeds_supply
      Mseq noiseLaw valueLaw cutoffOut splitIndex lowerCutoff
      totalSupply := by
  filter_upwards [h] with C hC a P hP hlt
  rcases hC a P hP hlt with
    ⟨region, q, hregion_meas, hq_nonneg, hq_le_one, hcdf,
      htarget_split⟩
  refine ⟨region, q, hregion_meas, hq_nonneg, hcdf, ?_⟩
  have hcard_succ :
      splitIndex C + 1 ≤
        (lowCutoffIndexSet (cutoffOut C P) (lowerCutoff C a)).card :=
    Nat.succ_le_of_lt hlt
  have hpow :
      q ^
          (lowCutoffIndexSet (cutoffOut C P) (lowerCutoff C a)).card ≤
        q ^ (splitIndex C + 1) := by
    rcases Nat.exists_eq_add_of_le hcard_succ with ⟨k, hk⟩
    rw [hk, pow_add]
    exact
      mul_le_of_le_one_right
        (pow_nonneg hq_nonneg (splitIndex C + 1))
        (pow_le_one₀ hq_nonneg hq_le_one)
  have hfactor :
      1 - q ^ (splitIndex C + 1) ≤
        1 -
          q ^
            (lowCutoffIndexSet (cutoffOut C P) (lowerCutoff C a)).card := by
    linarith
  have hmass_nonneg : 0 ≤ (valueLaw C a).real region := by
    simpa [MeasureTheory.Measure.real] using
      (ENNReal.toReal_nonneg : 0 ≤ ((valueLaw C a) region).toReal)
  exact
    htarget_split.trans_le
      (mul_le_mul_of_nonneg_right hfactor hmass_nonneg)

/--
Market-level split-index region/CDF bounds imply the selected-stable
split-index form.
-/
theorem source_assumption_selected_stable_low_cutoff_floor_split_region_bound_exceeds_supply_of_market
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {noiseLaw : MeasureTheory.Measure ℝ}
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {splitIndex : ℕ → ℕ}
    {lowerCutoff : ∀ C : ℕ, Admissible C → ℝ}
    {totalSupply : ℝ}
    (h :
      source_assumption_market_low_cutoff_floor_split_region_bound_exceeds_supply
        Mseq noiseLaw valueLaw cutoffOut splitIndex lowerCutoff
        totalSupply) :
    source_assumption_selected_stable_low_cutoff_floor_split_region_bound_exceeds_supply
      Mseq Iseq noiseLaw selected valueLaw cutoffOut splitIndex
      lowerCutoff totalSupply := by
  filter_upwards [h] with C hC a hlt
  exact
    hC a
      ((Iseq C).marketClearingCutoffOfStable
        (μ := (selected C a).1) (selected C a).2)
      ((Iseq C).marketClearingCutoffOfStable_marketClearing
        (μ := (selected C a).1) (selected C a).2)
      hlt

/--
The selected-stable split-index region/CDF bound implies the original
selected-stable region-bound clause.
-/
theorem source_assumption_selected_stable_low_cutoff_floor_region_bound_exceeds_supply_of_split_region_bound
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {noiseLaw : MeasureTheory.Measure ℝ}
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {splitIndex : ℕ → ℕ}
    {lowerCutoff : ∀ C : ℕ, Admissible C → ℝ}
    {totalSupply : ℝ}
    (h :
      source_assumption_selected_stable_low_cutoff_floor_split_region_bound_exceeds_supply
        Mseq Iseq noiseLaw selected valueLaw cutoffOut splitIndex
        lowerCutoff totalSupply) :
    source_assumption_selected_stable_low_cutoff_floor_region_bound_exceeds_supply
      Mseq Iseq noiseLaw selected valueLaw cutoffOut splitIndex
      lowerCutoff totalSupply := by
  filter_upwards [h] with C hC a hlt
  rcases hC a hlt with
    ⟨region, q, hregion_meas, hq_nonneg, hq_le_one, hcdf,
      htarget_split⟩
  refine ⟨region, q, hregion_meas, hq_nonneg, hcdf, ?_⟩
  let P :=
    (Iseq C).marketClearingCutoffOfStable
      (μ := (selected C a).1) (selected C a).2
  have hcard_succ :
      splitIndex C + 1 ≤
        (lowCutoffIndexSet (cutoffOut C P) (lowerCutoff C a)).card :=
    Nat.succ_le_of_lt hlt
  have hpow :
      q ^ (lowCutoffIndexSet (cutoffOut C P) (lowerCutoff C a)).card ≤
        q ^ (splitIndex C + 1) := by
    rcases Nat.exists_eq_add_of_le hcard_succ with ⟨k, hk⟩
    rw [hk, pow_add]
    exact
      mul_le_of_le_one_right
        (pow_nonneg hq_nonneg (splitIndex C + 1))
        (pow_le_one₀ hq_nonneg hq_le_one)
  have hfactor :
      1 - q ^ (splitIndex C + 1) ≤
        1 - q ^ (lowCutoffIndexSet (cutoffOut C P) (lowerCutoff C a)).card := by
    linarith
  have hmass_nonneg : 0 ≤ (valueLaw C a).real region := by
    simpa [MeasureTheory.Measure.real] using
      (ENNReal.toReal_nonneg : 0 ≤ ((valueLaw C a) region).toReal)
  simpa [P] using
    htarget_split.trans_le
      (mul_le_mul_of_nonneg_right hfactor hmass_nonneg)

/--
Market-level Lemma 11 floor-power bounds imply the selected-stable form,
because the A-L supply/demand interface turns a selected stable matching into a
market-clearing cutoff.
-/
theorem source_assumption_selected_stable_low_cutoff_floor_pow_integral_exceeds_supply_of_market
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {noiseLaw : MeasureTheory.Measure ℝ}
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {splitIndex : ℕ → ℕ}
    {lowerCutoff : ∀ C : ℕ, Admissible C → ℝ}
    {totalSupply : ℝ}
    (h :
      source_assumption_market_low_cutoff_floor_pow_integral_exceeds_supply
        Mseq noiseLaw valueLaw cutoffOut splitIndex lowerCutoff
        totalSupply) :
    source_assumption_selected_stable_low_cutoff_floor_pow_integral_exceeds_supply
      Mseq Iseq noiseLaw selected valueLaw cutoffOut splitIndex
      lowerCutoff totalSupply := by
  filter_upwards [h] with C hC a hlt
  let P :=
    (Iseq C).marketClearingCutoffOfStable
      (μ := (selected C a).1) (selected C a).2
  exact
    hC a P
      ((Iseq C).marketClearingCutoffOfStable_marketClearing
        (μ := (selected C a).1) (selected C a).2)
      hlt

/--
Market-level region/CDF bounds imply the selected-stable region/CDF bounds.
-/
theorem source_assumption_selected_stable_low_cutoff_floor_region_bound_exceeds_supply_of_market
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {noiseLaw : MeasureTheory.Measure ℝ}
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {splitIndex : ℕ → ℕ}
    {lowerCutoff : ∀ C : ℕ, Admissible C → ℝ}
    {totalSupply : ℝ}
    (h :
      source_assumption_market_low_cutoff_floor_region_bound_exceeds_supply
        Mseq noiseLaw valueLaw cutoffOut splitIndex lowerCutoff
        totalSupply) :
    source_assumption_selected_stable_low_cutoff_floor_region_bound_exceeds_supply
      Mseq Iseq noiseLaw selected valueLaw cutoffOut splitIndex
      lowerCutoff totalSupply := by
  filter_upwards [h] with C hC a hlt
  let P :=
    (Iseq C).marketClearingCutoffOfStable
      (μ := (selected C a).1) (selected C a).2
  exact
    hC a P
      ((Iseq C).marketClearingCutoffOfStable_marketClearing
        (μ := (selected C a).1) (selected C a).2)
      hlt

/--
The region/CDF lower-bound form implies the market-level floor-power integral
clause.
-/
theorem source_assumption_market_low_cutoff_floor_pow_integral_exceeds_supply_of_region_bound
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {noiseLaw : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {Admissible : ℕ → Type u}
    {valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {splitIndex : ℕ → ℕ}
    {lowerCutoff : ∀ C : ℕ, Admissible C → ℝ}
    {totalSupply : ℝ}
    (hvalue :
      source_assumption_market_value_probability valueLaw)
    (hregion :
      source_assumption_market_low_cutoff_floor_region_bound_exceeds_supply
        Mseq noiseLaw valueLaw cutoffOut splitIndex lowerCutoff
        totalSupply) :
    source_assumption_market_low_cutoff_floor_pow_integral_exceeds_supply
      Mseq noiseLaw valueLaw cutoffOut splitIndex lowerCutoff
      totalSupply := by
  filter_upwards [hregion] with C hregionC a P hP hlt
  rcases hregionC a P hP hlt with
    ⟨region, q, hregion_meas, hq_nonneg, hcdf, htarget⟩
  haveI : MeasureTheory.IsProbabilityMeasure (valueLaw C a) := hvalue C a
  exact
    AppliedModelingLib.Matching.lt_integral_one_sub_lowerCDFMass_pow_of_region_cdf_le
      noiseLaw (valueLaw C a)
      (floor := lowerCutoff C a)
      (q := q)
      (target := totalSupply)
      (m :=
        (lowCutoffIndexSet (cutoffOut C P) (lowerCutoff C a)).card)
      (region := region)
      hregion_meas hq_nonneg hcdf htarget

/--
The selected-stable region/CDF lower-bound form implies the selected-stable
floor-power integral clause.
-/
theorem source_assumption_selected_stable_low_cutoff_floor_pow_integral_exceeds_supply_of_region_bound
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {noiseLaw : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {splitIndex : ℕ → ℕ}
    {lowerCutoff : ∀ C : ℕ, Admissible C → ℝ}
    {totalSupply : ℝ}
    (hvalue :
      source_assumption_market_value_probability valueLaw)
    (hregion :
      source_assumption_selected_stable_low_cutoff_floor_region_bound_exceeds_supply
        Mseq Iseq noiseLaw selected valueLaw cutoffOut splitIndex
        lowerCutoff totalSupply) :
    source_assumption_selected_stable_low_cutoff_floor_pow_integral_exceeds_supply
      Mseq Iseq noiseLaw selected valueLaw cutoffOut splitIndex
      lowerCutoff totalSupply := by
  filter_upwards [hregion] with C hregionC a hlt
  rcases hregionC a hlt with
    ⟨region, q, hregion_meas, hq_nonneg, hcdf, htarget⟩
  haveI : MeasureTheory.IsProbabilityMeasure (valueLaw C a) := hvalue C a
  exact
    AppliedModelingLib.Matching.lt_integral_one_sub_lowerCDFMass_pow_of_region_cdf_le
      noiseLaw (valueLaw C a)
      (floor := lowerCutoff C a)
      (q := q)
      (target := totalSupply)
      (m :=
        (lowCutoffIndexSet
          (cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C a).1) (selected C a).2))
          (lowerCutoff C a)).card)
      (region := region)
      hregion_meas hq_nonneg hcdf htarget

/--
The constant-cutoff maximum-crossing integral lower bound implies the actual
low-cutoff affordability integral lower bound.
-/
theorem source_assumption_market_low_cutoff_integral_exceeds_supply_of_floor_pow_integral
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {noiseLaw : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {Admissible : ℕ → Type u}
    {valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {splitIndex : ℕ → ℕ}
    {lowerCutoff : ∀ C : ℕ, Admissible C → ℝ}
    {totalSupply : ℝ}
    (hfinite : source_assumption_market_value_finite valueLaw)
    (hfloor :
      source_assumption_market_low_cutoff_floor_pow_integral_exceeds_supply
        Mseq noiseLaw valueLaw cutoffOut splitIndex lowerCutoff
        totalSupply) :
    source_assumption_market_low_cutoff_integral_exceeds_supply
      Mseq noiseLaw valueLaw cutoffOut splitIndex lowerCutoff
      totalSupply := by
  filter_upwards [hfloor] with C hfloorC a P hP hlt
  haveI : MeasureTheory.IsFiniteMeasure (valueLaw C a) := hfinite C a
  have hstrict := hfloorC a P hP hlt
  simpa [cutoffAffordanceProbability] using
    (AppliedModelingLib.Matching.lt_integral_cutoffCrossingProbability_iidProduct_lowCutoffIndexSet_of_lt_integral_one_sub_lowerCDFMass_pow_card
      noiseLaw (valueLaw C a) hstrict)

/--
The selected-stable constant-cutoff maximum-crossing integral lower bound
implies the selected-stable actual low-cutoff affordability integral lower
bound.
-/
theorem source_assumption_selected_stable_low_cutoff_integral_exceeds_supply_of_floor_pow_integral
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {noiseLaw : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {splitIndex : ℕ → ℕ}
    {lowerCutoff : ∀ C : ℕ, Admissible C → ℝ}
    {totalSupply : ℝ}
    (hfinite : source_assumption_market_value_finite valueLaw)
    (hfloor :
      source_assumption_selected_stable_low_cutoff_floor_pow_integral_exceeds_supply
        Mseq Iseq noiseLaw selected valueLaw cutoffOut splitIndex
        lowerCutoff totalSupply) :
    source_assumption_selected_stable_low_cutoff_integral_exceeds_supply
      Mseq Iseq noiseLaw selected valueLaw cutoffOut splitIndex
      lowerCutoff totalSupply := by
  filter_upwards [hfloor] with C hfloorC a hlt
  let P :=
    (Iseq C).marketClearingCutoffOfStable
      (μ := (selected C a).1) (selected C a).2
  haveI : MeasureTheory.IsFiniteMeasure (valueLaw C a) := hfinite C a
  have hstrict := hfloorC a hlt
  simpa [cutoffAffordanceProbability, P] using
    (AppliedModelingLib.Matching.lt_integral_cutoffCrossingProbability_iidProduct_lowCutoffIndexSet_of_lt_integral_one_sub_lowerCDFMass_pow_card
      noiseLaw (valueLaw C a) hstrict)

/--
Outcome-model bridge from integrated cutoff-affordance probabilities to
matched events.

This is the source semantics that the applicant value/noise population in the
outcome law realizes the displayed value integral, and that any applicant who
can afford an active college is matched somewhere.
-/
-- audit-premise: market-level integrated cutoff-affordance probability is represented by an outcome event whose outcomes are matched somewhere
abbrev source_assumption_market_integrated_affordance_event_bridge
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (noiseLaw : MeasureTheory.Measure ℝ)
    {Admissible : ℕ → Type u}
    (valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ)
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1))) :
    Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C, ∀ P : (Mseq C).Cutoff,
      (Mseq C).MarketClearing P →
        ∀ active : Finset (Fin (C + 1)),
          ∃ event : OutcomeSeq C → Prop,
            (∫ v : ℝ,
              cutoffAffordanceProbability
                (MeasureTheory.Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                active v (cutoffOut C P) ∂(valueLaw C a)) ≤
              AppliedModelingLib.Matching.eventMass (outcomeLaw C P) event ∧
            ∀ ω : OutcomeSeq C,
              event ω →
                AppliedModelingLib.Matching.chosenInActive
                  (chosenCollege C P)
                  (Finset.univ : Finset (Fin (C + 1))) ω

/--
Selected-stable outcome-model bridge from integrated cutoff-affordance
probabilities to matched events.
-/
-- audit-premise: selected-stable integrated cutoff-affordance probability is represented by an outcome event whose outcomes are matched somewhere
abbrev source_assumption_selected_stable_integrated_affordance_event_bridge
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : MeasureTheory.Measure ℝ)
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ)
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1))) :
    Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C, ∀ active : Finset (Fin (C + 1)),
      ∃ event : OutcomeSeq C → Prop,
        (∫ v : ℝ,
          cutoffAffordanceProbability
            (MeasureTheory.Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            active v
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2))
            ∂(valueLaw C a)) ≤
          AppliedModelingLib.Matching.eventMass
            (outcomeLaw C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2))
            event ∧
        ∀ ω : OutcomeSeq C,
          event ω →
            AppliedModelingLib.Matching.chosenInActive
              (chosenCollege C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := (selected C a).1) (selected C a).2))
              (Finset.univ : Finset (Fin (C + 1))) ω

/--
The market-level integrated outcome bridge implies the selected-stable bridge
by applying it to the market-clearing cutoff induced by the selected stable
matching.
-/
theorem source_assumption_selected_stable_integrated_affordance_event_bridge_of_market
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {noiseLaw : MeasureTheory.Measure ℝ}
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {OutcomeSeq : ℕ → Type*} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C)}
    {chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1))}
    (h :
      source_assumption_market_integrated_affordance_event_bridge
        Mseq noiseLaw valueLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege) :
    source_assumption_selected_stable_integrated_affordance_event_bridge
      Mseq Iseq noiseLaw selected valueLaw cutoffOut OutcomeSeq
      outcomeLaw chosenCollege := by
  filter_upwards [h] with C hC a active
  exact
    hC a
      ((Iseq C).marketClearingCutoffOfStable
        (μ := (selected C a).1) (selected C a).2)
      ((Iseq C).marketClearingCutoffOfStable_marketClearing
        (μ := (selected C a).1) (selected C a).2)
      active

/--
The integrated low-cutoff probability clause plus the integrated outcome bridge
derive the high-mass matched event used by the capacity contradiction.
-/
theorem source_assumption_market_low_cutoff_capacity_contradiction_of_integrated_affordance_event_bridge
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {noiseLaw : MeasureTheory.Measure ℝ}
    {Admissible : ℕ → Type u}
    {valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {splitIndex : ℕ → ℕ}
    {lowerCutoff : ∀ C : ℕ, Admissible C → ℝ}
    {OutcomeSeq : ℕ → Type*} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C)}
    {chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1))}
    {totalSupply : ℝ}
    (hintegral :
      source_assumption_market_low_cutoff_integral_exceeds_supply
        Mseq noiseLaw valueLaw cutoffOut splitIndex lowerCutoff
        totalSupply)
    (hbridge :
      source_assumption_market_integrated_affordance_event_bridge
        Mseq noiseLaw valueLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege) :
    source_assumption_market_low_cutoff_capacity_contradiction
      Mseq cutoffOut splitIndex lowerCutoff OutcomeSeq outcomeLaw
      chosenCollege totalSupply := by
  filter_upwards [hintegral, hbridge] with C hintegralC hbridgeC a P hP hlt
  let active : Finset (Fin (C + 1)) :=
    lowCutoffIndexSet (cutoffOut C P) (lowerCutoff C a)
  rcases hbridgeC a P hP active with ⟨event, hintegral_le_event, himp⟩
  exact ⟨event, lt_of_lt_of_le (hintegralC a P hP hlt) hintegral_le_event, himp⟩

/--
The selected-stable integrated low-cutoff probability clause plus the
selected-stable integrated outcome bridge derive the high-mass matched event
used by the selected capacity contradiction.
-/
theorem source_assumption_selected_stable_low_cutoff_capacity_contradiction_of_integrated_affordance_event_bridge
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {noiseLaw : MeasureTheory.Measure ℝ}
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {splitIndex : ℕ → ℕ}
    {lowerCutoff : ∀ C : ℕ, Admissible C → ℝ}
    {OutcomeSeq : ℕ → Type*} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C)}
    {chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1))}
    {totalSupply : ℝ}
    (hintegral :
      source_assumption_selected_stable_low_cutoff_integral_exceeds_supply
        Mseq Iseq noiseLaw selected valueLaw cutoffOut splitIndex
        lowerCutoff totalSupply)
    (hbridge :
      source_assumption_selected_stable_integrated_affordance_event_bridge
        Mseq Iseq noiseLaw selected valueLaw cutoffOut OutcomeSeq
        outcomeLaw chosenCollege) :
    source_assumption_selected_stable_low_cutoff_capacity_contradiction
      Mseq Iseq selected cutoffOut splitIndex lowerCutoff
      OutcomeSeq outcomeLaw chosenCollege totalSupply := by
  filter_upwards [hintegral, hbridge] with C hintegralC hbridgeC a hlt
  let P :=
    (Iseq C).marketClearingCutoffOfStable
      (μ := (selected C a).1) (selected C a).2
  let active : Finset (Fin (C + 1)) :=
    lowCutoffIndexSet (cutoffOut C P) (lowerCutoff C a)
  rcases hbridgeC a active with ⟨event, hintegral_le_event, himp⟩
  exact ⟨event, lt_of_lt_of_le (hintegralC a hlt) hintegral_le_event, himp⟩

/--
The low-CDF power clause plus the outcome-model affordance bridge derive the
high-mass matched event used by the capacity contradiction.
-/
theorem source_assumption_market_low_cutoff_capacity_contradiction_of_pow_affordance_event_bridge
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {noiseLaw : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {Admissible : ℕ → Type u}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {splitIndex : ℕ → ℕ}
    {lowerCutoff eventValue : ∀ C : ℕ, Admissible C → ℝ}
    {OutcomeSeq : ℕ → Type*} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C)}
    {chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1))}
    {totalSupply : ℝ}
    (hpow :
      source_assumption_market_low_cutoff_pow_exceeds_supply
        Mseq noiseLaw cutoffOut splitIndex lowerCutoff eventValue
        totalSupply)
    (hbridge :
      source_assumption_market_affordance_event_bridge
        Mseq noiseLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege) :
    source_assumption_market_low_cutoff_capacity_contradiction
      Mseq cutoffOut splitIndex lowerCutoff OutcomeSeq outcomeLaw
      chosenCollege totalSupply := by
  filter_upwards [hpow, hbridge] with C hpowC hbridgeC a P hP hlt
  let active : Finset (Fin (C + 1)) :=
    lowCutoffIndexSet (cutoffOut C P) (lowerCutoff C a)
  rcases hbridgeC P hP active (eventValue C a) with
    ⟨event, hafford_le_event, himp⟩
  refine ⟨event, ?_, himp⟩
  have hafford_gt :
      totalSupply <
        cutoffAffordanceProbability
          (MeasureTheory.Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          active (eventValue C a) (cutoffOut C P) := by
    have hprob := hpowC a P hP hlt
    simpa [cutoffAffordanceProbability, active] using
      (AppliedModelingLib.Matching.lt_cutoffCrossingProbability_iidProduct_lowCutoffIndexSet_of_lt_one_sub_lowerCDFMass_pow_card
        noiseLaw hprob)
  exact lt_of_lt_of_le hafford_gt hafford_le_event

/--
The market-level low-CDF power clause and pointwise outcome bridge also give
the selected-stable capacity contradiction at the selected market-clearing
cutoff.  This is the non-integrated route used to expose the remaining
polynomial tail-mass obligation directly.
-/
theorem source_assumption_selected_stable_low_cutoff_capacity_contradiction_of_market_pow_affordance_event_bridge
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {noiseLaw : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {splitIndex : ℕ → ℕ}
    {lowerCutoff eventValue : ∀ C : ℕ, Admissible C → ℝ}
    {OutcomeSeq : ℕ → Type*} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C)}
    {chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1))}
    {totalSupply : ℝ}
    (hpow :
      source_assumption_market_low_cutoff_pow_exceeds_supply
        Mseq noiseLaw cutoffOut splitIndex lowerCutoff eventValue
        totalSupply)
    (hbridge :
      source_assumption_market_affordance_event_bridge
        Mseq noiseLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege) :
    source_assumption_selected_stable_low_cutoff_capacity_contradiction
      Mseq Iseq selected cutoffOut splitIndex lowerCutoff OutcomeSeq
      outcomeLaw chosenCollege totalSupply := by
  filter_upwards [hpow, hbridge] with C hpowC hbridgeC a hlt
  let P :=
    (Iseq C).marketClearingCutoffOfStable
      (μ := (selected C a).1) (selected C a).2
  let active : Finset (Fin (C + 1)) :=
    lowCutoffIndexSet (cutoffOut C P) (lowerCutoff C a)
  have hP : (Mseq C).MarketClearing P :=
    (Iseq C).marketClearingCutoffOfStable_marketClearing
      (μ := (selected C a).1) (selected C a).2
  rcases hbridgeC P hP active (eventValue C a) with
    ⟨event, hafford_le_event, himp⟩
  refine ⟨event, ?_, himp⟩
  have hafford_gt :
      totalSupply <
        cutoffAffordanceProbability
          (MeasureTheory.Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          active (eventValue C a) (cutoffOut C P) := by
    have hprob := hpowC a P hP hlt
    simpa [cutoffAffordanceProbability, active, P] using
      (AppliedModelingLib.Matching.lt_cutoffCrossingProbability_iidProduct_lowCutoffIndexSet_of_lt_one_sub_lowerCDFMass_pow_card
        noiseLaw hprob)
  exact lt_of_lt_of_le hafford_gt hafford_le_event

/--
The market-level capacity contradiction proves the advertised low-count bound.

The source clause only constructs the too-large matched event from a
hypothetical low-count failure; Lean supplies the capacity contradiction from
choice-mass semantics, market clearing, and the total-capacity normalization.
-/
theorem source_assumption_market_low_cutoff_count_of_capacity_contradiction
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Admissible : ℕ → Type u}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {splitIndex : ℕ → ℕ}
    {lowerCutoff : ∀ C : ℕ, Admissible C → ℝ}
    {OutcomeSeq : ℕ → Type*} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C)}
    {chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1))}
    {totalSupply : ℝ}
    (hfinite :
      source_assumption_market_outcome_finite Mseq OutcomeSeq outcomeLaw)
    (hchoiceMass_eq_aggregateDemand :
      source_assumption_market_choice_mass_eq_aggregateDemand
        Mseq OutcomeSeq outcomeLaw chosenCollege)
    (hcapacity_clear :
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          ∀ c : Fin (C + 1),
            (Mseq C).aggregateDemand P c = (Mseq C).capacity c)
    (hcapacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (hcontr :
      source_assumption_market_low_cutoff_capacity_contradiction
        Mseq cutoffOut splitIndex lowerCutoff
        OutcomeSeq outcomeLaw chosenCollege totalSupply) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C, ∀ P : (Mseq C).Cutoff,
        (Mseq C).MarketClearing P →
          (lowCutoffIndexSet (cutoffOut C P) (lowerCutoff C a)).card ≤
            splitIndex C := by
  filter_upwards
    [hchoiceMass_eq_aggregateDemand, hcapacity_clear, hcapacity_sum,
      hcontr] with
    C hchoiceC hclearC hsumC hcontrC a P hP
  by_contra hnot
  have hlt :
      splitIndex C <
        (lowCutoffIndexSet (cutoffOut C P) (lowerCutoff C a)).card :=
    Nat.lt_of_not_ge hnot
  rcases hcontrC a P hP hlt with ⟨event, hmass_gt, himp⟩
  haveI : MeasureTheory.IsFiniteMeasure (outcomeLaw C P) :=
    hfinite C P
  have hmass_le :
      AppliedModelingLib.Matching.eventMass (outcomeLaw C P) event ≤
        ∑ c : Fin (C + 1), (Mseq C).capacity c :=
    AppliedModelingLib.Matching.eventMass_le_totalCapacity_of_imp_aggregateDemand_eq_capacity
      (outcomeLaw C P) (chosenCollege C P) himp
      (by
        simpa using
          hchoiceC P hP (Finset.univ : Finset (Fin (C + 1))))
      (by intro c; exact hclearC P hP c)
  linarith

/--
The selected-stable capacity contradiction proves the selected-stable
low-count bound.
-/
theorem source_assumption_selected_stable_low_cutoff_count_of_capacity_contradiction
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {splitIndex : ℕ → ℕ}
    {lowerCutoff : ∀ C : ℕ, Admissible C → ℝ}
    {OutcomeSeq : ℕ → Type*} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C)}
    {chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1))}
    {totalSupply : ℝ}
    (hfinite :
      source_assumption_selected_stable_outcome_finite
        Mseq Iseq OutcomeSeq outcomeLaw)
    (hchoiceMass_eq_aggregateDemand :
      source_assumption_selected_stable_choice_mass_eq_aggregateDemand
        Mseq Iseq selected OutcomeSeq outcomeLaw chosenCollege)
    (hcapacity_clear :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c : Fin (C + 1),
          (Mseq C).aggregateDemand
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2) c =
            (Mseq C).capacity c)
    (hcapacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (hcontr :
      source_assumption_selected_stable_low_cutoff_capacity_contradiction
        Mseq Iseq selected cutoffOut splitIndex lowerCutoff
        OutcomeSeq outcomeLaw chosenCollege totalSupply) :
    ∀ᶠ C : ℕ in atTop,
      ∀ a : Admissible C,
        (lowCutoffIndexSet
          (cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C a).1) (selected C a).2))
          (lowerCutoff C a)).card ≤
          splitIndex C := by
  filter_upwards
    [hchoiceMass_eq_aggregateDemand, hcapacity_clear, hcapacity_sum,
      hcontr] with
    C hchoiceC hclearC hsumC hcontrC a
  let P :=
    (Iseq C).marketClearingCutoffOfStable
      (μ := (selected C a).1) (selected C a).2
  by_contra hnot
  have hlt :
      splitIndex C <
        (lowCutoffIndexSet (cutoffOut C P) (lowerCutoff C a)).card := by
    exact Nat.lt_of_not_ge hnot
  rcases hcontrC a hlt with ⟨event, hmass_gt, himp⟩
  haveI : MeasureTheory.IsFiniteMeasure (outcomeLaw C P) :=
    hfinite C (selected C a)
  have hmass_le :
      AppliedModelingLib.Matching.eventMass (outcomeLaw C P) event ≤
        ∑ c : Fin (C + 1), (Mseq C).capacity c :=
    AppliedModelingLib.Matching.eventMass_le_totalCapacity_of_imp_aggregateDemand_eq_capacity
      (outcomeLaw C P) (chosenCollege C P) himp
      (by
        simpa [P] using
          hchoiceC a (Finset.univ : Finset (Fin (C + 1))))
      (by
        intro c
        simpa [P] using hclearC a c)
  linarith

/--
Theorem 3 low-count bound from the market-level capacity contradiction.
-/
theorem source_assumption_theorem3_suffix_market_low_cutoff_count_of_capacity_contradiction
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Admissible : ℕ → Type u}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {epsilon : ℝ}
    {lowerCutoff : ∀ C : ℕ, Admissible C → ℝ}
    {OutcomeSeq : ℕ → Type*} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C)}
    {chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1))}
    {totalSupply : ℝ}
    (hfinite :
      source_assumption_market_outcome_finite Mseq OutcomeSeq outcomeLaw)
    (hchoiceMass_eq_aggregateDemand :
      source_assumption_market_choice_mass_eq_aggregateDemand
        Mseq OutcomeSeq outcomeLaw chosenCollege)
    (hcapacity_clear :
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          ∀ c : Fin (C + 1),
            (Mseq C).aggregateDemand P c = (Mseq C).capacity c)
    (hcapacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (hcontr :
      source_assumption_market_low_cutoff_capacity_contradiction
        Mseq cutoffOut
        (fun C : ℕ => epsilonFloorSplitIndex (epsilon / 2) C)
        lowerCutoff OutcomeSeq outcomeLaw chosenCollege totalSupply) :
    source_assumption_theorem3_suffix_market_low_cutoff_count
      Mseq cutoffOut (epsilon := epsilon) lowerCutoff :=
  source_assumption_market_low_cutoff_count_of_capacity_contradiction
    hfinite hchoiceMass_eq_aggregateDemand hcapacity_clear hcapacity_sum
    hcontr

/--
Theorem 3 low-count bound from the selected-stable capacity contradiction.
-/
theorem source_assumption_theorem3_suffix_selected_stable_low_cutoff_count_of_capacity_contradiction
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {epsilon : ℝ}
    {lowerCutoff : ∀ C : ℕ, Admissible C → ℝ}
    {OutcomeSeq : ℕ → Type*} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C)}
    {chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1))}
    {totalSupply : ℝ}
    (hfinite :
      source_assumption_selected_stable_outcome_finite
        Mseq Iseq OutcomeSeq outcomeLaw)
    (hchoiceMass_eq_aggregateDemand :
      source_assumption_selected_stable_choice_mass_eq_aggregateDemand
        Mseq Iseq selected OutcomeSeq outcomeLaw chosenCollege)
    (hcapacity_clear :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c : Fin (C + 1),
          (Mseq C).aggregateDemand
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2) c =
            (Mseq C).capacity c)
    (hcapacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (hcontr :
      source_assumption_selected_stable_low_cutoff_capacity_contradiction
        Mseq Iseq selected cutoffOut
        (fun C : ℕ => epsilonFloorSplitIndex (epsilon / 2) C)
        lowerCutoff OutcomeSeq outcomeLaw chosenCollege totalSupply) :
    source_assumption_theorem3_suffix_selected_stable_low_cutoff_count
      Mseq Iseq selected cutoffOut (epsilon := epsilon) lowerCutoff :=
  source_assumption_selected_stable_low_cutoff_count_of_capacity_contradiction
    hfinite hchoiceMass_eq_aggregateDemand hcapacity_clear hcapacity_sum
    hcontr

/--
Sorted market-clearing cutoffs and the Theorem 3 low-count bound imply the
visible sorted-suffix cutoff-floor clause.
-/
theorem source_assumption_theorem3_suffix_market_cutoff_floor_of_sorted_low_count
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Admissible : ℕ → Type u}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {epsilon : ℝ}
    {lowerCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (hsorted : source_assumption_market_cutoff_index_sorted Mseq cutoffOut)
    (hcount :
      source_assumption_theorem3_suffix_market_low_cutoff_count
        Mseq cutoffOut (epsilon := epsilon) lowerCutoff) :
    source_assumption_theorem3_suffix_market_cutoff_floor
      Mseq cutoffOut (epsilon := epsilon) lowerCutoff := by
  filter_upwards [hsorted, hcount] with C hsortedC hcountC a P hP c hc
  exact
    suffix_floor_of_sorted_lowCutoffIndexSet_card_le
      (hsortedC P hP) (hcountC a P hP) hc

/--
Sorted selected-stable cutoffs and the selected-stable Theorem 3 low-count
bound imply the visible sorted-suffix cutoff-floor clause.
-/
theorem source_assumption_theorem3_suffix_cutoff_floor_of_selected_stable_sorted_low_count
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {epsilon : ℝ}
    {lowerCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (hsorted :
      source_assumption_selected_stable_cutoff_index_sorted
        Mseq Iseq selected cutoffOut)
    (hcount :
      source_assumption_theorem3_suffix_selected_stable_low_cutoff_count
        Mseq Iseq selected cutoffOut (epsilon := epsilon) lowerCutoff) :
    source_assumption_theorem3_suffix_cutoff_floor
      Mseq Iseq selected cutoffOut (epsilon := epsilon) lowerCutoff := by
  filter_upwards [hsorted, hcount] with C hsortedC hcountC a c hc
  exact
    suffix_floor_of_sorted_lowCutoffIndexSet_card_le
      (hsortedC a) (hcountC a) hc

/--
Pointwise low-CDF power and outcome-event clauses imply the selected-stable
Theorem 3 sorted-suffix cutoff floor, without routing through an integrated
source-model package.
-/
theorem source_assumption_theorem3_suffix_cutoff_floor_of_market_pow_affordance_event_bridge
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {noiseLaw : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {epsilon : ℝ}
    {lowerCutoff eventValue : ∀ C : ℕ, Admissible C → ℝ}
    {OutcomeSeq : ℕ → Type*} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C)}
    {chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1))}
    {totalSupply : ℝ}
    (hfinite :
      source_assumption_selected_stable_outcome_finite
        Mseq Iseq OutcomeSeq outcomeLaw)
    (hchoiceMass_eq_aggregateDemand :
      source_assumption_selected_stable_choice_mass_eq_aggregateDemand
        Mseq Iseq selected OutcomeSeq outcomeLaw chosenCollege)
    (hcapacity_clear :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c : Fin (C + 1),
          (Mseq C).aggregateDemand
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2) c =
            (Mseq C).capacity c)
    (hcapacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (hsorted :
      source_assumption_selected_stable_cutoff_index_sorted
        Mseq Iseq selected cutoffOut)
    (hpow :
      source_assumption_market_low_cutoff_pow_exceeds_supply
        Mseq noiseLaw cutoffOut
        (fun C : ℕ => epsilonFloorSplitIndex (epsilon / 2) C)
        lowerCutoff eventValue totalSupply)
    (hbridge :
      source_assumption_market_affordance_event_bridge
        Mseq noiseLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege) :
    source_assumption_theorem3_suffix_cutoff_floor
      Mseq Iseq selected cutoffOut (epsilon := epsilon) lowerCutoff :=
  source_assumption_theorem3_suffix_cutoff_floor_of_selected_stable_sorted_low_count
    hsorted
    (source_assumption_theorem3_suffix_selected_stable_low_cutoff_count_of_capacity_contradiction
      hfinite hchoiceMass_eq_aggregateDemand hcapacity_clear hcapacity_sum
      (source_assumption_selected_stable_low_cutoff_capacity_contradiction_of_market_pow_affordance_event_bridge
        hpow hbridge))

/--
Theorem 3 source low-tail rate at the scalar lower cutoff floor.
-/
-- audit-premise: eventually, the lower-cutoff tail at threshold-epsilon is at most epsilon/(2(C+1))
abbrev source_assumption_theorem3_suffix_low_tail_floor_halfDiv
    {Admissible : ℕ → Type u}
    (noiseLaw : MeasureTheory.Measure ℝ)
    {epsilon : ℝ}
    (threshold lowerCutoff : ∀ C : ℕ, Admissible C → ℝ) : Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C,
      AppliedModelingLib.Probability.upperTailMass noiseLaw
        (lowerCutoff C a - (threshold C a - epsilon)) ≤
      epsilon / (2 * (((C + 1 : ℕ) : ℝ)))

/--
Explicit low-tail quantile used by the Theorem 3 sorted-suffix route.

For large `C`, this chooses a threshold whose upper-tail mass is at most
`epsilon / (2 * (C + 1))`.  Early indices use a harmless default because the
source clause is eventual.
-/
noncomputable def theorem3LowTailQuantile
    (noiseLaw : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (epsilon : ℝ) (C : ℕ) : ℝ :=
  if htarget :
      0 < epsilon / (2 * (((C + 1 : ℕ) : ℝ))) ∧
        epsilon / (2 * (((C + 1 : ℕ) : ℝ))) < 1 then
    Classical.choose
      (AppliedModelingLib.Probability.exists_upperTailMass_Ici_bracket
        noiseLaw htarget.1 htarget.2)
  else
    0

/--
The explicit low-tail quantile satisfies the Theorem 3 low-tail rate
eventually.
-/
theorem theorem3LowTailQuantile_upperTailMass_le_eventually
    (noiseLaw : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon) :
    ∀ᶠ C : ℕ in atTop,
      AppliedModelingLib.Probability.upperTailMass noiseLaw
          (theorem3LowTailQuantile noiseLaw epsilon C) ≤
        epsilon / (2 * (((C + 1 : ℕ) : ℝ))) := by
  have hden_tendsto :
      Tendsto (fun C : ℕ => (((C + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have htarget_tendsto :
      Tendsto
        (fun C : ℕ => (epsilon / 2) / (((C + 1 : ℕ) : ℝ)))
        atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop hden_tendsto (epsilon / 2)
  have htarget_lt_one :
      ∀ᶠ C : ℕ in atTop,
        epsilon / (2 * (((C + 1 : ℕ) : ℝ))) < 1 := by
    have hnear :
        ∀ᶠ C : ℕ in atTop,
          (epsilon / 2) / (((C + 1 : ℕ) : ℝ)) ∈ Set.Iio (1 : ℝ) :=
      htarget_tendsto (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hnear] with C hC
    have hrewrite :
        (epsilon / 2) / (((C + 1 : ℕ) : ℝ)) =
          epsilon / (2 * (((C + 1 : ℕ) : ℝ))) := by
      ring
    rw [← hrewrite]
    exact hC
  filter_upwards [htarget_lt_one] with C htarget_lt
  have htarget_pos :
      0 < epsilon / (2 * (((C + 1 : ℕ) : ℝ))) := by
    positivity
  unfold theorem3LowTailQuantile
  rw [dif_pos ⟨htarget_pos, htarget_lt⟩]
  exact
    (Classical.choose_spec
      (AppliedModelingLib.Probability.exists_upperTailMass_Ici_bracket
        noiseLaw htarget_pos htarget_lt)).1

/--
For a long-tailed noise law, a vanishing sequence of closed/strict quantile
brackets gives an asymptotically matching lower bound for the strict tail.

This does not assert that a fixed quantile has no atom.  Instead, shifting the
threshold left by any fixed positive amount makes the closed upper tail sit
inside a strict upper tail, and long-tailedness makes that shifted tail
asymptotically equivalent to the original strict tail.
-/
theorem upperTailMass_quantile_lower_bound_eventually_of_longTailed
    (noiseLaw : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {target threshold : ℕ → ℝ}
    (htarget_zero : Tendsto target atTop (nhds 0))
    (hbracket : ∀ᶠ n : ℕ in atTop,
      AppliedModelingLib.Probability.upperTailMass noiseLaw (threshold n) ≤ target n ∧
        target n ≤ noiseLaw.real (Set.Ici (threshold n)))
    {d slack : ℝ} (hd : 0 < d) (hslack_pos : 0 < slack)
    (hslack_le_one : slack ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      (1 - slack) * target n ≤
        AppliedModelingLib.Probability.upperTailMass noiseLaw (threshold n) := by
  let survival : ℝ → ℝ := AppliedModelingLib.Probability.upperTailMass noiseLaw
  have hpositive : ∀ᶠ x : ℝ in atTop, 0 < survival x :=
    hlong.eventually_pos
      (fun x => AppliedModelingLib.Probability.upperTailMass_nonneg noiseLaw x)
  have hthreshold_top : Tendsto threshold atTop atTop := by
    rw [tendsto_atTop]
    intro B
    rcases Filter.eventually_atTop.1 hpositive with ⟨Bpos, hBpos⟩
    let B' : ℝ := max B Bpos
    have hB'_pos : 0 < survival B' :=
      hBpos B' (le_max_right _ _)
    have hsmall : ∀ᶠ n : ℕ in atTop, target n < survival B' :=
      htarget_zero (isOpen_Iio.mem_nhds hB'_pos)
    filter_upwards [hsmall, hbracket] with n hn hbracket_n
    by_contra hnot
    have hlt_B : threshold n < B := lt_of_not_ge hnot
    have hle : threshold n ≤ B' :=
      le_trans (le_of_lt hlt_B) (le_max_left _ _)
    have htail_le : survival B' ≤ survival (threshold n) :=
      AppliedModelingLib.Probability.upperTailMass_antitone noiseLaw hle
    have hbracket_le := hbracket_n.1
    dsimp [survival] at htail_le hB'_pos ⊢
    linarith
  have hshift_top : Tendsto (fun n : ℕ => threshold n - d) atTop atTop := by
    rw [tendsto_atTop]
    intro B
    filter_upwards [hthreshold_top (eventually_ge_atTop (B + d))] with n hn
    change B + d ≤ threshold n at hn
    linarith
  have hratio : Tendsto
      (fun n : ℕ => survival (threshold n) / survival (threshold n - d))
      atTop (nhds 1) := by
    have hraw := (hlong d hd).comp hshift_top
    convert hraw using 1
    ext n
    dsimp [Function.comp]
    congr 2 <;> ring
  have hratio_lower : ∀ᶠ n : ℕ in atTop,
      1 - slack < survival (threshold n) / survival (threshold n - d) :=
    hratio (isOpen_Ioi.mem_nhds (by linarith : (1 - slack) < (1 : ℝ)))
  have hshift_pos : ∀ᶠ n : ℕ in atTop,
      0 < survival (threshold n - d) :=
    hshift_top.eventually hpositive
  filter_upwards [hratio_lower, hshift_pos, hbracket] with
    n hratio_n hshift_pos_n hbracket_n
  have hclosed_le_shift :
      noiseLaw.real (Set.Ici (threshold n)) ≤ survival (threshold n - d) := by
    apply MeasureTheory.measureReal_mono (μ := noiseLaw)
    intro x hx
    simp only [Set.mem_Ici, Set.mem_Ioi] at hx ⊢
    linarith
  have htarget_le_shift : target n ≤ survival (threshold n - d) :=
    le_trans hbracket_n.2
      (by simpa [survival, AppliedModelingLib.Probability.upperTailMass] using
        hclosed_le_shift)
  have hfactor_nonneg : 0 ≤ 1 - slack := by linarith
  have hscaled : (1 - slack) * target n ≤
      (1 - slack) * survival (threshold n - d) :=
    mul_le_mul_of_nonneg_left htarget_le_shift hfactor_nonneg
  have hratio_mul :
      (1 - slack) * survival (threshold n - d) < survival (threshold n) := by
    have hmul := mul_lt_mul_of_pos_right hratio_n hshift_pos_n
    field_simp [ne_of_gt hshift_pos_n] at hmul
    nlinarith
  exact le_trans hscaled (le_of_lt hratio_mul)

/--
Closed upper-tail bracket data does not by itself give a lower bound on the
strict upper tail used by the split-power crossing clauses.  A point mass at the
threshold has closed upper tail one and strict upper tail zero.
-/
theorem strict_upper_tail_lower_bound_not_from_closed_bracket_guardrail :
    AppliedModelingLib.Probability.upperTailMass
          (MeasureTheory.Measure.dirac (0 : ℝ)) 0 ≤ (1 / 2 : ℝ) ∧
      (1 / 2 : ℝ) ≤
          (MeasureTheory.Measure.dirac (0 : ℝ)).real (Set.Ici 0) ∧
      ¬ (1 / 2 : ℝ) ≤
          AppliedModelingLib.Probability.upperTailMass
            (MeasureTheory.Measure.dirac (0 : ℝ)) 0 := by
  constructor
  · norm_num [AppliedModelingLib.Probability.upperTailMass, MeasureTheory.Measure.real]
  constructor
  · norm_num [MeasureTheory.Measure.real]
  · norm_num [AppliedModelingLib.Probability.upperTailMass, MeasureTheory.Measure.real]

/--
For nonatomic noise laws, the closed upper-tail lower side of
`exists_upperTailMass_Ici_bracket` is legitimately the same as a strict
upper-tail lower bound.
-/
theorem upperTailMass_eq_real_Ici_of_noAtoms
    (noiseLaw : MeasureTheory.Measure ℝ) [MeasureTheory.NoAtoms noiseLaw]
    (x : ℝ) :
    AppliedModelingLib.Probability.upperTailMass noiseLaw x =
      noiseLaw.real (Set.Ici x) := by
  have hIciIoi :
      noiseLaw.real (Set.Ici x) = noiseLaw.real (Set.Ioi x) := by
    simpa using
      (MeasureTheory.measureReal_congr
        (μ := noiseLaw)
        ((MeasureTheory.Ioi_ae_eq_Ici (μ := noiseLaw) (a := x)).symm))
  simpa [AppliedModelingLib.Probability.upperTailMass] using hIciIoi.symm

/--
Consequently, a future PG24 route may use the closed-tail side of the quantile
bracket for strict split-power estimates only after it has proved or assumed
nonatomicity explicitly.
-/
theorem upperTailMass_lower_bound_of_real_Ici_bracket_noAtoms
    {noiseLaw : MeasureTheory.Measure ℝ} [MeasureTheory.NoAtoms noiseLaw]
    {x target : ℝ}
    (hclosed : target ≤ noiseLaw.real (Set.Ici x)) :
    target ≤ AppliedModelingLib.Probability.upperTailMass noiseLaw x := by
  simpa [upperTailMass_eq_real_Ici_of_noAtoms noiseLaw x] using hclosed

/--
Under an explicit nonatomicity hypothesis, the low-tail quantile chosen for
Theorem 3 also carries the closed-bracket lower side as a strict upper-tail
lower bound.  Without `NoAtoms`, the preceding Dirac guardrail shows this step
is invalid.
-/
theorem theorem3LowTailQuantile_upperTailMass_lower_bound_eventually_noAtoms
    (noiseLaw : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure noiseLaw] [MeasureTheory.NoAtoms noiseLaw]
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon) :
    ∀ᶠ C : ℕ in atTop,
      epsilon / (2 * (((C + 1 : ℕ) : ℝ))) ≤
        AppliedModelingLib.Probability.upperTailMass noiseLaw
          (theorem3LowTailQuantile noiseLaw epsilon C) := by
  have hden_tendsto :
      Tendsto (fun C : ℕ => (((C + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have htarget_tendsto :
      Tendsto
        (fun C : ℕ => (epsilon / 2) / (((C + 1 : ℕ) : ℝ)))
        atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop hden_tendsto (epsilon / 2)
  have htarget_lt_one :
      ∀ᶠ C : ℕ in atTop,
        epsilon / (2 * (((C + 1 : ℕ) : ℝ))) < 1 := by
    have hnear :
        ∀ᶠ C : ℕ in atTop,
          (epsilon / 2) / (((C + 1 : ℕ) : ℝ)) ∈ Set.Iio (1 : ℝ) :=
      htarget_tendsto (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hnear] with C hC
    have hrewrite :
        (epsilon / 2) / (((C + 1 : ℕ) : ℝ)) =
          epsilon / (2 * (((C + 1 : ℕ) : ℝ))) := by
      ring
    rw [← hrewrite]
    exact hC
  filter_upwards [htarget_lt_one] with C htarget_lt
  have htarget_pos :
      0 < epsilon / (2 * (((C + 1 : ℕ) : ℝ))) := by
    positivity
  unfold theorem3LowTailQuantile
  rw [dif_pos ⟨htarget_pos, htarget_lt⟩]
  exact
    upperTailMass_lower_bound_of_real_Ici_bracket_noAtoms
      (noiseLaw := noiseLaw)
      ((Classical.choose_spec
        (AppliedModelingLib.Probability.exists_upperTailMass_Ici_bracket
          noiseLaw htarget_pos htarget_lt)).2)

/--
For nonatomic noise laws, the active Theorem 3 strict-tail split-power
obligation reduces to the scalar crossing inequality at the explicit low-tail
quantile target.  The scalar inequality remains a real analytic proof
obligation; this lemma only removes the closed-vs-strict tail ambiguity.
-/
theorem source_assumption_theorem3_low_cutoff_upper_tail_split_pow_exceeds_supply_of_quantile_noAtoms
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {noiseLaw : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsProbabilityMeasure noiseLaw] [MeasureTheory.NoAtoms noiseLaw]
    {Admissible : ℕ → Type u}
    {epsilon totalSupply : ℝ} (hepsilon_pos : 0 < epsilon)
    {threshold : ∀ C : ℕ, Admissible C → ℝ}
    (hcross :
      ∀ᶠ C : ℕ in atTop,
        ∀ _a : Admissible C,
          totalSupply <
            1 -
              (1 - epsilon / (2 * (((C + 1 : ℕ) : ℝ)))) ^
                (epsilonFloorSplitIndex (epsilon / 2) C + 1)) :
    source_assumption_market_low_cutoff_upper_tail_split_pow_exceeds_supply
      Mseq noiseLaw
      (fun C : ℕ => epsilonFloorSplitIndex (epsilon / 2) C)
      (fun C a =>
        threshold C a - epsilon + theorem3LowTailQuantile noiseLaw epsilon C)
      (fun C a => threshold C a - epsilon)
      totalSupply := by
  refine
    source_assumption_market_low_cutoff_upper_tail_split_pow_exceeds_supply_of_scalar_tail_lower_bound
      (Mseq := Mseq)
      (noiseLaw := noiseLaw)
      (splitIndex := fun C : ℕ => epsilonFloorSplitIndex (epsilon / 2) C)
      (lowerCutoff := fun C a =>
        threshold C a - epsilon + theorem3LowTailQuantile noiseLaw epsilon C)
      (eventValue := fun C a => threshold C a - epsilon)
      (scalarTail := fun C (_a : Admissible C) =>
        epsilon / (2 * (((C + 1 : ℕ) : ℝ))))
      ?_ hcross
  filter_upwards
    [theorem3LowTailQuantile_upperTailMass_lower_bound_eventually_noAtoms
      noiseLaw hepsilon_pos] with C hC a
  have harg :
      (threshold C a - epsilon + theorem3LowTailQuantile noiseLaw epsilon C) -
          (threshold C a - epsilon) =
        theorem3LowTailQuantile noiseLaw epsilon C := by
    ring
  simpa [harg] using hC

/--
Exponential-relaxation version of the nonatomic Theorem 3 quantile helper.
It replaces the raw split-power crossing premise by the stronger but simpler
eventual bound against `1 - exp (-m*p)`.
-/
theorem source_assumption_theorem3_low_cutoff_upper_tail_split_pow_exceeds_supply_of_quantile_noAtoms_exp
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {noiseLaw : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsProbabilityMeasure noiseLaw] [MeasureTheory.NoAtoms noiseLaw]
    {Admissible : ℕ → Type u}
    {epsilon totalSupply : ℝ} (hepsilon_pos : 0 < epsilon)
    {threshold : ∀ C : ℕ, Admissible C → ℝ}
    (hcross_exp :
      ∀ᶠ C : ℕ in atTop,
        ∀ _a : Admissible C,
          totalSupply <
            1 - Real.exp
              (-(((epsilonFloorSplitIndex (epsilon / 2) C + 1 : ℕ) : ℝ) *
                (epsilon / (2 * (((C + 1 : ℕ) : ℝ))))))) :
    source_assumption_market_low_cutoff_upper_tail_split_pow_exceeds_supply
      Mseq noiseLaw
      (fun C : ℕ => epsilonFloorSplitIndex (epsilon / 2) C)
      (fun C a =>
        threshold C a - epsilon + theorem3LowTailQuantile noiseLaw epsilon C)
      (fun C a => threshold C a - epsilon)
      totalSupply := by
  refine
    source_assumption_market_low_cutoff_upper_tail_split_pow_exceeds_supply_of_scalar_tail_lower_bound_exp
      (Mseq := Mseq)
      (noiseLaw := noiseLaw)
      (splitIndex := fun C : ℕ => epsilonFloorSplitIndex (epsilon / 2) C)
      (lowerCutoff := fun C a =>
        threshold C a - epsilon + theorem3LowTailQuantile noiseLaw epsilon C)
      (eventValue := fun C a => threshold C a - epsilon)
      (scalarTail := fun C (_a : Admissible C) =>
        epsilon / (2 * (((C + 1 : ℕ) : ℝ))))
      ?_ ?_ ?_ hcross_exp
  · filter_upwards
      [theorem3LowTailQuantile_upperTailMass_lower_bound_eventually_noAtoms
        noiseLaw hepsilon_pos] with C hC a
    have harg :
        (threshold C a - epsilon + theorem3LowTailQuantile noiseLaw epsilon C) -
            (threshold C a - epsilon) =
          theorem3LowTailQuantile noiseLaw epsilon C := by
      ring
    simpa [harg] using hC
  · exact Filter.Eventually.of_forall (fun C a => by positivity)
  · filter_upwards
      [theorem3LowTailQuantile_upperTailMass_lower_bound_eventually_noAtoms
        noiseLaw hepsilon_pos] with C hC a
    exact
      le_trans hC
        (AppliedModelingLib.Probability.upperTailMass_le_one noiseLaw
          (theorem3LowTailQuantile noiseLaw epsilon C))

/--
Static-gap version of the nonatomic Theorem 3 quantile helper.  The floor
arithmetic proves the exponential target from the explicit supply gap
`totalSupply < 1 - exp (-(epsilon/2)^2)`.
-/
theorem source_assumption_theorem3_low_cutoff_upper_tail_split_pow_exceeds_supply_of_quantile_noAtoms_static_exp_gap
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {noiseLaw : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsProbabilityMeasure noiseLaw] [MeasureTheory.NoAtoms noiseLaw]
    {Admissible : ℕ → Type u}
    {epsilon totalSupply : ℝ} (hepsilon_pos : 0 < epsilon)
    {threshold : ∀ C : ℕ, Admissible C → ℝ}
    (hgap :
      totalSupply <
        1 - Real.exp (-((epsilon / 2) * (epsilon / 2)))) :
    source_assumption_market_low_cutoff_upper_tail_split_pow_exceeds_supply
      Mseq noiseLaw
      (fun C : ℕ => epsilonFloorSplitIndex (epsilon / 2) C)
      (fun C a =>
        threshold C a - epsilon + theorem3LowTailQuantile noiseLaw epsilon C)
      (fun C a => threshold C a - epsilon)
      totalSupply := by
  refine
    source_assumption_theorem3_low_cutoff_upper_tail_split_pow_exceeds_supply_of_quantile_noAtoms_exp
      (Mseq := Mseq) (noiseLaw := noiseLaw)
      (Admissible := Admissible) hepsilon_pos ?_
  have hcross :
      ∀ᶠ C : ℕ in atTop,
        ∀ _a : Admissible C,
          totalSupply <
            1 - Real.exp
              (-(((epsilonFloorSplitIndex (epsilon / 2) C + 1 : ℕ) : ℝ) *
                ((epsilon / 2) / (((C + 1 : ℕ) : ℝ))))) :=
    epsilonFloorSplitIndex_exp_supply_gap_of_static_gap
      (Admissible := Admissible)
      (delta := epsilon / 2) (tau := epsilon / 2)
      (totalSupply := totalSupply)
      (by linarith) (by linarith) hgap
  filter_upwards [hcross] with C hC a
  have htail_eq :
      (epsilon / 2) / ((C : ℝ) + 1) =
        epsilon / (2 * ((C : ℝ) + 1)) := by
    have hn_ne : ((C : ℝ) + 1) ≠ 0 := by positivity
    field_simp [hn_ne]
  simpa [Nat.cast_add, Nat.cast_one, htail_eq] using hC a

/--
Choosing the lower cutoff as the source threshold minus `epsilon` plus the
explicit low-tail quantile discharges the separate low-tail-rate source clause.
-/
theorem source_assumption_theorem3_suffix_low_tail_floor_halfDiv_of_quantile_floor
    {Admissible : ℕ → Type u}
    (noiseLaw : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon)
    (threshold : ∀ C : ℕ, Admissible C → ℝ) :
    source_assumption_theorem3_suffix_low_tail_floor_halfDiv
      noiseLaw (epsilon := epsilon) threshold
      (fun C a =>
        threshold C a - epsilon +
          theorem3LowTailQuantile noiseLaw epsilon C) := by
  filter_upwards
    [theorem3LowTailQuantile_upperTailMass_le_eventually
      noiseLaw hepsilon_pos] with C hC a
  have harg :
      (threshold C a - epsilon +
          theorem3LowTailQuantile noiseLaw epsilon C) -
          (threshold C a - epsilon) =
        theorem3LowTailQuantile noiseLaw epsilon C := by
    ring
  simpa [harg] using hC

/--
Theorem 3 source high-crossing endpoint for the sorted suffix: eventually,
some selected-stable suffix college is crossed with probability above
`1 - epsilon` at the high endpoint `threshold + epsilon`.
-/
-- audit-premise: eventually, a sorted-suffix selected-stable cutoff has high crossing probability above one minus epsilon at threshold+epsilon
abbrev source_assumption_theorem3_suffix_high_crossing_endpoint
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : MeasureTheory.Measure ℝ)
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon : ℝ}
    (threshold : ∀ C : ℕ, Admissible C → ℝ) : Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C,
      ∃ c ∈ indexSuffixLarge (epsilonFloorSplitIndex (epsilon / 2) C) C,
        1 - epsilon <
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2) c -
              (threshold C a + epsilon))

/--
Theorem 3 high-crossing clause for the semantic block of cutoffs that are not
below the scalar lower floor.  This is the sortedness-free high endpoint used
by the active pointwise-capacity route.
-/
-- audit-premise: eventually, a non-low selected-stable cutoff has high crossing probability above one minus epsilon at threshold+epsilon
abbrev source_assumption_theorem3_nonLow_high_crossing_endpoint
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : MeasureTheory.Measure ℝ)
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon : ℝ}
    (lowerCutoff threshold : ∀ C : ℕ, Admissible C → ℝ) : Prop :=
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
              (threshold C a + epsilon))

/--
A sorted-suffix high-crossing endpoint transports to the active semantic
non-low endpoint once the suffix-floor premise proves suffix cutoffs are above
the scalar lower floor.
-/
theorem source_assumption_theorem3_nonLow_high_crossing_endpoint_of_suffix_cutoff_floor_high_crossing_endpoint
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {noiseLaw : MeasureTheory.Measure ℝ}
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {epsilon : ℝ}
    {lowerCutoff threshold : ∀ C : ℕ, Admissible C → ℝ}
    (hfloor :
      source_assumption_theorem3_suffix_cutoff_floor
        Mseq Iseq selected cutoffOut (epsilon := epsilon) lowerCutoff)
    (hhigh :
      source_assumption_theorem3_suffix_high_crossing_endpoint
        Mseq Iseq noiseLaw selected cutoffOut (epsilon := epsilon)
        threshold) :
    source_assumption_theorem3_nonLow_high_crossing_endpoint
      Mseq Iseq noiseLaw selected cutoffOut (epsilon := epsilon)
      lowerCutoff threshold := by
  filter_upwards [hfloor, hhigh] with C hfloorC hhighC a
  rcases hhighC a with ⟨c, hcSuffix, hcross⟩
  refine ⟨c, ?_, hcross⟩
  have hcIndex :
      epsilonFloorSplitIndex (epsilon / 2) C ≤ (c : ℕ) :=
    (Finset.mem_filter.mp hcSuffix).2
  have hfloor_le :
      lowerCutoff C a ≤
        cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C a).1) (selected C a).2) c :=
    hfloorC a c hcIndex
  rw [nonLowCutoffIndexSet, Finset.mem_sdiff]
  constructor
  · simp
  · intro hcLow
    exact not_lt_of_ge hfloor_le ((Finset.mem_filter.mp hcLow).2)

/--
Theorem 3 upper-ceiling clause for the semantic block of cutoffs that are not
below the scalar lower floor.  This is the sortedness-free counterpart of
`source_assumption_theorem3_suffix_upper_ceiling_atBot`: it keeps the
source-side geometric obligation visible, while the high-crossing probability
is derived from the upper-tail limit at `-∞`.
-/
-- audit-premise: eventually, a non-low cutoff is below the upper ceiling, and the upper ceiling minus threshold+epsilon tends to -infinity
abbrev source_assumption_theorem3_nonLow_upper_ceiling_atBot
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon : ℝ}
    (lowerCutoff threshold upperCutoff :
      ∀ C : ℕ, Admissible C → ℝ) : Prop :=
  (∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C,
      ∃ c ∈ nonLowCutoffIndexSet
          (cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C a).1) (selected C a).2))
          (lowerCutoff C a),
        cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C a).1) (selected C a).2) c ≤
        upperCutoff C a) ∧
  (∀ B : ℝ, ∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C,
      upperCutoff C a - (threshold C a + epsilon) ≤ B)

/--
The semantic non-low upper-ceiling source package discharges the direct
high-crossing endpoint used by the pointwise-capacity Theorem 3 route.
-/
theorem source_assumption_theorem3_nonLow_high_crossing_endpoint_of_upper_ceiling_atBot
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {noiseLaw : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon)
    {lowerCutoff threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (h :
      source_assumption_theorem3_nonLow_upper_ceiling_atBot
        Mseq Iseq selected cutoffOut (epsilon := epsilon)
        lowerCutoff threshold upperCutoff) :
    source_assumption_theorem3_nonLow_high_crossing_endpoint
      Mseq Iseq noiseLaw selected cutoffOut (epsilon := epsilon)
      lowerCutoff threshold := by
  rcases Filter.eventually_atBot.1
      (AppliedModelingLib.Probability.eventually_one_sub_lt_upperTailMass_atBot
        noiseLaw hepsilon_pos) with
    ⟨B, hB⟩
  filter_upwards [h.1, h.2 B] with C hupperC htailC a
  rcases hupperC a with ⟨c, hc, hcutoff_le⟩
  refine ⟨c, hc, ?_⟩
  exact
    lt_of_lt_of_le
      (hB (upperCutoff C a - (threshold C a + epsilon)) (htailC a))
      (AppliedModelingLib.Probability.upperTailMass_antitone noiseLaw
        (sub_le_sub_right hcutoff_le (threshold C a + epsilon)))

/--
Theorem 3 source upper-ceiling clause for the sorted suffix: some suffix
college is below the scalar upper ceiling, and that ceiling is eventually
arbitrarily far below `threshold + epsilon`.
-/
-- audit-premise: eventually, a sorted-suffix cutoff is below the upper ceiling, and the upper ceiling minus threshold+epsilon tends to -infinity
abbrev source_assumption_theorem3_suffix_upper_ceiling_atBot
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon : ℝ}
    (threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ) : Prop :=
  (∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C,
      ∃ c ∈ indexSuffixLarge (epsilonFloorSplitIndex (epsilon / 2) C) C,
        cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C a).1) (selected C a).2) c ≤
        upperCutoff C a) ∧
  (∀ B : ℝ, ∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C,
      upperCutoff C a - (threshold C a + epsilon) ≤ B)

/--
Theorem 3 upper-ceiling clause stated over all market-clearing cutoffs.

The selected-stable version is derived from this via the A-L supply/demand
bridge.
-/
-- audit-premise: eventually, every market-clearing cutoff has a sorted-suffix coordinate below the upper ceiling, and the upper ceiling minus threshold+epsilon tends to -infinity
abbrev source_assumption_theorem3_suffix_market_upper_ceiling_atBot
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    {Admissible : ℕ → Type u}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {epsilon : ℝ}
    (threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ) : Prop :=
  (∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C, ∀ P : (Mseq C).Cutoff,
      (Mseq C).MarketClearing P →
        ∃ c ∈ indexSuffixLarge (epsilonFloorSplitIndex (epsilon / 2) C) C,
          cutoffOut C P c ≤ upperCutoff C a) ∧
  (∀ B : ℝ, ∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C,
      upperCutoff C a - (threshold C a + epsilon) ≤ B)

/--
Market-clearing upper-ceiling clauses imply the selected-stable form.
-/
theorem source_assumption_theorem3_suffix_upper_ceiling_atBot_of_market
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {epsilon : ℝ}
    {threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (h :
      source_assumption_theorem3_suffix_market_upper_ceiling_atBot
        Mseq cutoffOut (epsilon := epsilon) threshold upperCutoff) :
    source_assumption_theorem3_suffix_upper_ceiling_atBot
      Mseq Iseq selected cutoffOut (epsilon := epsilon)
      threshold upperCutoff := by
  constructor
  · filter_upwards [h.1] with C hC a
    exact
      hC a
        ((Iseq C).marketClearingCutoffOfStable
          (μ := (selected C a).1) (selected C a).2)
        ((Iseq C).marketClearingCutoffOfStable_marketClearing
          (μ := (selected C a).1) (selected C a).2)
  · exact h.2

/--
A sorted-suffix upper-ceiling clause gives the active semantic non-low
upper-ceiling clause once the suffix-floor premise has proved that every
suffix cutoff is above the scalar lower floor.
-/
theorem source_assumption_theorem3_nonLow_upper_ceiling_atBot_of_suffix_cutoff_floor_upper_ceiling_atBot
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {epsilon : ℝ}
    {lowerCutoff threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (hfloor :
      source_assumption_theorem3_suffix_cutoff_floor
        Mseq Iseq selected cutoffOut (epsilon := epsilon) lowerCutoff)
    (hupper :
      source_assumption_theorem3_suffix_upper_ceiling_atBot
        Mseq Iseq selected cutoffOut (epsilon := epsilon)
        threshold upperCutoff) :
    source_assumption_theorem3_nonLow_upper_ceiling_atBot
      Mseq Iseq selected cutoffOut (epsilon := epsilon)
      lowerCutoff threshold upperCutoff := by
  constructor
  · filter_upwards [hfloor, hupper.1] with C hfloorC hupperC a
    rcases hupperC a with ⟨c, hcSuffix, hcutoff_le⟩
    refine ⟨c, ?_, hcutoff_le⟩
    have hcIndex :
        epsilonFloorSplitIndex (epsilon / 2) C ≤ (c : ℕ) :=
      (Finset.mem_filter.mp hcSuffix).2
    have hfloor_le :
        lowerCutoff C a ≤
          cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable
              (μ := (selected C a).1) (selected C a).2) c :=
      hfloorC a c hcIndex
    rw [nonLowCutoffIndexSet, Finset.mem_sdiff]
    constructor
    · simp
    · intro hcLow
      exact not_lt_of_ge hfloor_le ((Finset.mem_filter.mp hcLow).2)
  · exact hupper.2

/--
Market-level sorted-suffix floor and upper-ceiling clauses imply the active
semantic non-low upper-ceiling clause after A-L selected-stable transport.
-/
theorem source_assumption_theorem3_nonLow_upper_ceiling_atBot_of_market_suffix_cutoff_floor_upper_ceiling_atBot
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {epsilon : ℝ}
    {lowerCutoff threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (hfloor :
      source_assumption_theorem3_suffix_market_cutoff_floor
        Mseq cutoffOut (epsilon := epsilon) lowerCutoff)
    (hupper :
      source_assumption_theorem3_suffix_market_upper_ceiling_atBot
        Mseq cutoffOut (epsilon := epsilon) threshold upperCutoff) :
    source_assumption_theorem3_nonLow_upper_ceiling_atBot
      Mseq Iseq selected cutoffOut (epsilon := epsilon)
      lowerCutoff threshold upperCutoff :=
  source_assumption_theorem3_nonLow_upper_ceiling_atBot_of_suffix_cutoff_floor_upper_ceiling_atBot
    (source_assumption_theorem3_suffix_cutoff_floor_of_market
      (Iseq := Iseq) (selected := selected) hfloor)
    (source_assumption_theorem3_suffix_upper_ceiling_atBot_of_market
      (Iseq := Iseq) (selected := selected) hupper)

/--
The selected-stable upper-ceiling source package discharges the direct
high-crossing endpoint used by the repaired Theorem 3 route.
-/
theorem source_assumption_theorem3_suffix_high_crossing_endpoint_of_upper_ceiling_atBot
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {noiseLaw : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon)
    {threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (h :
      source_assumption_theorem3_suffix_upper_ceiling_atBot
        Mseq Iseq selected cutoffOut (epsilon := epsilon)
        threshold upperCutoff) :
    source_assumption_theorem3_suffix_high_crossing_endpoint
      Mseq Iseq noiseLaw selected cutoffOut (epsilon := epsilon)
      threshold := by
  rcases Filter.eventually_atBot.1
      (AppliedModelingLib.Probability.eventually_one_sub_lt_upperTailMass_atBot
        noiseLaw hepsilon_pos) with
    ⟨B, hB⟩
  filter_upwards [h.1, h.2 B] with C hupperC htailC a
  rcases hupperC a with ⟨c, hc, hcutoff_le⟩
  refine ⟨c, hc, ?_⟩
  exact
    lt_of_lt_of_le
      (hB (upperCutoff C a - (threshold C a + epsilon)) (htailC a))
      (AppliedModelingLib.Probability.upperTailMass_antitone noiseLaw
        (sub_le_sub_right hcutoff_le (threshold C a + epsilon)))

/--
Market-level upper-ceiling clauses imply the direct selected-stable
high-crossing endpoint after the A-L supply/demand transport.
-/
theorem source_assumption_theorem3_suffix_high_crossing_endpoint_of_market_upper_ceiling_atBot
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {noiseLaw : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon)
    {threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (h :
      source_assumption_theorem3_suffix_market_upper_ceiling_atBot
        Mseq cutoffOut (epsilon := epsilon) threshold upperCutoff) :
    source_assumption_theorem3_suffix_high_crossing_endpoint
      Mseq Iseq noiseLaw selected cutoffOut (epsilon := epsilon)
      threshold :=
  source_assumption_theorem3_suffix_high_crossing_endpoint_of_upper_ceiling_atBot
    (Mseq := Mseq) (Iseq := Iseq) (selected := selected)
    (cutoffOut := cutoffOut) hepsilon_pos
    (source_assumption_theorem3_suffix_upper_ceiling_atBot_of_market
      (Iseq := Iseq) (selected := selected) h)

/--
Market-level suffix floor and upper-ceiling clauses directly imply the active
semantic non-low high-crossing endpoint after selected-stable transport.
-/
theorem source_assumption_theorem3_nonLow_high_crossing_endpoint_of_market_suffix_cutoff_floor_upper_ceiling_atBot
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {noiseLaw : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon)
    {lowerCutoff threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (hfloor :
      source_assumption_theorem3_suffix_market_cutoff_floor
        Mseq cutoffOut (epsilon := epsilon) lowerCutoff)
    (hupper :
      source_assumption_theorem3_suffix_market_upper_ceiling_atBot
        Mseq cutoffOut (epsilon := epsilon) threshold upperCutoff) :
    source_assumption_theorem3_nonLow_high_crossing_endpoint
      Mseq Iseq noiseLaw selected cutoffOut (epsilon := epsilon)
      lowerCutoff threshold :=
  source_assumption_theorem3_nonLow_high_crossing_endpoint_of_suffix_cutoff_floor_high_crossing_endpoint
    (source_assumption_theorem3_suffix_cutoff_floor_of_market
      (Iseq := Iseq) (selected := selected) hfloor)
    (source_assumption_theorem3_suffix_high_crossing_endpoint_of_market_upper_ceiling_atBot
      (Iseq := Iseq) (selected := selected) (cutoffOut := cutoffOut)
      hepsilon_pos hupper)

/--
Theorem 4 source interval-mass clause for the regular value interval.
-/
-- audit-premise: eventually, the chosen regular interval has value mass greater than 1-tol
abbrev source_assumption_theorem4_regular_interval_mass
    {Admissible : ℕ → Type u}
    (valueMass : ∀ C : ℕ, Admissible C → Set ℝ → ℝ)
    {tol vLow vHigh : ℝ} : Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C,
      1 - tol < valueMass C a (Set.Icc vLow vHigh)

/--
Theorem 4 source exceptional-set form for the regular interval.

The paper phrases the approximation as holding outside a small exceptional
set.  For the interval route, that exceptional set is the complement of the
regular interval.  The strict slack `delta < tol` is the algebraic form needed
to produce the formal large-regular-set inequality `1 - tol < mass`.
-/
-- audit-premise: eventually, the complement of the chosen regular interval has value mass at most delta < tol
abbrev source_assumption_theorem4_regular_interval_exception_bound
    {Admissible : ℕ → Type u}
    (valueMass : ∀ C : ℕ, Admissible C → Set ℝ → ℝ)
    {delta tol vLow vHigh : ℝ} : Prop :=
  delta < tol ∧
  (∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C,
      valueMass C a (Set.Icc vLow vHigh) +
          valueMass C a (Set.Icc vLow vHigh)ᶜ =
        1) ∧
  (∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C,
      valueMass C a (Set.Icc vLow vHigh)ᶜ ≤ delta)

/--
Theorem 4 source probability-law clause for regular-value distributions.
-/
-- audit-premise: every regular-value law used in Theorem 4 is a probability measure
abbrev source_assumption_theorem4_regular_value_probability
    {Admissible : ℕ → Type u}
    (valueLaw :
      ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ) : Prop :=
  ∀ C : ℕ, ∀ a : Admissible C,
    MeasureTheory.IsProbabilityMeasure (valueLaw C a)

theorem source_assumption_market_value_probability_of_theorem4_regular_value_probability
    {Admissible : ℕ → Type u}
    {valueLaw :
      ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ}
    (hprob :
      source_assumption_theorem4_regular_value_probability valueLaw) :
    source_assumption_market_value_probability valueLaw :=
  hprob

/--
Theorem 4 source exceptional-set mass bound for concrete probability laws.

The partition identity for the interval and its complement is not a source
premise in this form: it is derived from probability-measure algebra.  The
remaining mathematical content is the paper's small exceptional-set bound.
-/
-- audit-premise: eventually, the complement of the chosen regular interval has probability mass at most delta
abbrev source_assumption_theorem4_regular_interval_measure_exception_bound
    {Admissible : ℕ → Type u}
    (valueLaw :
      ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ)
    {delta vLow vHigh : ℝ} : Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ a : Admissible C,
      (valueLaw C a).real (Set.Icc vLow vHigh)ᶜ ≤ delta

/--
Every individual probability law on `ℝ` has a bounded closed interval whose
complement has arbitrarily small real mass.

This is deliberately only a single-law fact.  It does not discharge
`source_assumption_theorem4_regular_interval_measure_exception_bound`, which
requires one fixed interval to work eventually and uniformly for every
admissible market.  A repair of that source premise must either make the
endpoints depend on the law or provide an explicit uniform-tightness argument.
-/
theorem exists_regular_interval_measure_compl_le_of_probability
    (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ]
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ vLow vHigh : ℝ, vLow < vHigh ∧
      μ.real (Set.Icc vLow vHigh)ᶜ ≤ delta := by
  haveI : MeasureTheory.IsFiniteMeasure μ := inferInstance
  have htight : MeasureTheory.IsTightMeasureSet ({μ} : Set (MeasureTheory.Measure ℝ)) :=
    MeasureTheory.isTightMeasureSet_singleton (μ := μ)
  have hclosed :
      Tendsto
        (fun r : ℝ =>
          (⨆ ν ∈ ({μ} : Set (MeasureTheory.Measure ℝ)),
            ν (Metric.closedBall (0 : ℝ) r)ᶜ))
        atTop (nhds 0) :=
    MeasureTheory.tendsto_measure_compl_closedBall_of_isTightMeasureSet htight 0
  have hofReal_pos : 0 < ENNReal.ofReal delta := ENNReal.ofReal_pos.mpr hdelta
  rw [ENNReal.tendsto_atTop_zero] at hclosed
  obtain ⟨r, hr⟩ := hclosed (ENNReal.ofReal delta) hofReal_pos
  let R : ℝ := max (max r 1) 0
  have hr_le_R : r ≤ R :=
    le_trans (le_max_left r 1) (le_max_left (max r 1) 0)
  have hR_pos : 0 < R := by
    exact
      lt_of_lt_of_le zero_lt_one
        (le_trans (le_max_right r 1) (le_max_left (max r 1) 0))
  have hball_le :
      μ (Metric.closedBall (0 : ℝ) R)ᶜ ≤ ENNReal.ofReal delta := by
    have hR := hr R hr_le_R
    simpa using hR
  have hinterval_le : μ (Set.Icc (-R) R)ᶜ ≤ ENNReal.ofReal delta := by
    simpa [Real.closedBall_eq_Icc, sub_eq_add_neg] using hball_le
  refine ⟨-R, R, ?_, ?_⟩
  · linarith
  · exact ENNReal.toReal_le_of_le_ofReal hdelta.le hinterval_le

/--
The extended-model coalition definition fixes one true-value probability law
`η` for every represented economy and stable selection.  This is the source
model condition in `model-extended.tex:43-63`, not a uniform-tightness
assumption: the common interval below is derived from it and probability-law
tightness.
-/
-- audit-premise: every represented Theorem 4 coalition has the fixed source value law eta
abbrev source_assumption_theorem4_value_law_eq_eta
    {Admissible : ℕ → Type u}
    (valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ)
    (η : MeasureTheory.Measure ℝ) : Prop :=
  ∀ C : ℕ, ∀ a : Admissible C, valueLaw C a = η

/--
The Theorem 4 regular-interval exception fact for the one source value law
`η`.  Unlike the older family-wide interval bound, this is a single-measure
mathematical obligation.  It follows existentially from tightness, but the
capacity proof still determines which interval endpoint can be used.
-/
-- audit-premise: the chosen Theorem 4 regular interval has eta-exception mass at most delta
abbrev source_assumption_theorem4_eta_regular_interval_exception_bound
    (η : MeasureTheory.Measure ℝ)
    {delta vLow vHigh : ℝ} : Prop :=
  η.real (Set.Icc vLow vHigh)ᶜ ≤ delta

/--
The fixed source value law supplies the market-level probability-law clause.
-/
theorem source_assumption_market_value_probability_of_theorem4_value_law_eq_eta
    {Admissible : ℕ → Type u}
    {valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ}
    (η : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure η]
    (hvalue : source_assumption_theorem4_value_law_eq_eta valueLaw η) :
    source_assumption_market_value_probability valueLaw := by
  intro C a
  rw [hvalue C a]
  infer_instance

/--
The fixed source value-law condition transports a one-law exceptional-set bound
to the legacy family-shaped interval predicate.
-/
theorem source_assumption_theorem4_regular_interval_measure_exception_bound_of_value_law_eq_eta
    {Admissible : ℕ → Type u}
    {valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ}
    (η : MeasureTheory.Measure ℝ)
    (hvalue : source_assumption_theorem4_value_law_eq_eta valueLaw η)
    {delta vLow vHigh : ℝ}
    (heta :
      source_assumption_theorem4_eta_regular_interval_exception_bound
        η (delta := delta) (vLow := vLow) (vHigh := vHigh)) :
    source_assumption_theorem4_regular_interval_measure_exception_bound
      valueLaw (delta := delta) (vLow := vLow) (vHigh := vHigh) :=
  Filter.Eventually.of_forall (fun C a => by
    rw [hvalue C a]
    exact heta)

/--
The fixed source value law makes the Theorem 4 regular-interval exception
bound a theorem.  This does not infer uniform tightness for arbitrary
`valueLaw`; it uses the source condition that every represented law is the
same `η`.
-/
theorem exists_theorem4_regular_interval_measure_exception_bound_of_value_law_eq_eta
    {Admissible : ℕ → Type u}
    {valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ}
    (η : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure η]
    (hvalue : source_assumption_theorem4_value_law_eq_eta valueLaw η)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ vLow vHigh : ℝ, vLow < vHigh ∧
      source_assumption_theorem4_regular_interval_measure_exception_bound
        valueLaw (delta := delta) (vLow := vLow) (vHigh := vHigh) := by
  rcases exists_regular_interval_measure_compl_le_of_probability η hdelta with
    ⟨vLow, vHigh, hv, hmeasure⟩
  refine ⟨vLow, vHigh, hv, ?_⟩
  exact
    source_assumption_theorem4_regular_interval_measure_exception_bound_of_value_law_eq_eta
      η hvalue hmeasure

/--
The regular-interval exceptional-set source form implies the existing large
regular-interval mass clause.
-/
theorem source_assumption_theorem4_regular_interval_mass_of_exception_bound
    {Admissible : ℕ → Type u}
    {valueMass : ∀ C : ℕ, Admissible C → Set ℝ → ℝ}
    {delta tol vLow vHigh : ℝ}
    (h :
      source_assumption_theorem4_regular_interval_exception_bound
        valueMass (delta := delta) (tol := tol)
        (vLow := vLow) (vHigh := vHigh)) :
    source_assumption_theorem4_regular_interval_mass
      valueMass (tol := tol) (vLow := vLow) (vHigh := vHigh) := by
  rcases h with ⟨hdelta, hpartition, hexception⟩
  filter_upwards [hpartition, hexception] with C hpartC hexC a
  exact
    theorem4_regular_mass_gt_of_exception_bound
      (valueMass := valueMass C a) (regularSet := Set.Icc vLow vHigh)
      (delta := delta) (epsilon := tol)
        (hpartC a) (hexC a) hdelta

/--
Concrete probability-law exceptional-set bounds imply the abstract Theorem 4
regular-interval exception source form.
-/
theorem source_assumption_theorem4_regular_interval_exception_bound_of_measure
    {Admissible : ℕ → Type u}
    {valueLaw :
      ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ}
    {delta tol vLow vHigh : ℝ}
    (hdelta : delta < tol)
    (hprob :
      source_assumption_theorem4_regular_value_probability valueLaw)
    (hexception :
      source_assumption_theorem4_regular_interval_measure_exception_bound
        valueLaw (delta := delta) (vLow := vLow) (vHigh := vHigh)) :
    source_assumption_theorem4_regular_interval_exception_bound
      (fun C a S => (valueLaw C a).real S)
      (delta := delta) (tol := tol) (vLow := vLow) (vHigh := vHigh) := by
  refine ⟨hdelta, ?_, hexception⟩
  filter_upwards [Filter.Eventually.of_forall (fun C => True.intro)] with
    C _ a
  haveI : MeasureTheory.IsProbabilityMeasure (valueLaw C a) := hprob C a
  calc
    (valueLaw C a).real (Set.Icc vLow vHigh) +
        (valueLaw C a).real (Set.Icc vLow vHigh)ᶜ =
      (valueLaw C a).real Set.univ :=
        MeasureTheory.measureReal_add_measureReal_compl
          (μ := valueLaw C a) measurableSet_Icc
    _ = 1 := MeasureTheory.probReal_univ

/--
Theorem 4 source cutoff-floor clause for the sorted suffix.
-/
-- audit-premise: eventually, every selected-stable cutoff in the sorted suffix is above the common scalar lower cutoff floor
abbrev source_assumption_theorem4_suffix_cutoff_floor
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {tol : ℝ} (lowerCutoff : ℕ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    ∀ a : Admissible n, ∀ c : Fin (n + 1),
      epsilonFloorSplitIndex (tol / 2) n ≤ (c : ℕ) →
        lowerCutoff n ≤
          cutoffOut n
            ((Iseq n).marketClearingCutoffOfStable
              (μ := (selected n a).1) (selected n a).2) c

/--
Theorem 4 cutoff-floor clause stated over all market-clearing cutoffs.
-/
-- audit-premise: eventually, every market-clearing cutoff in the sorted suffix is above the common scalar lower cutoff floor
abbrev source_assumption_theorem4_suffix_market_cutoff_floor
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    {Admissible : ℕ → Type u}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {tol : ℝ} (lowerCutoff : ℕ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    ∀ a : Admissible n, ∀ P : (Mseq n).Cutoff,
      (Mseq n).MarketClearing P →
        ∀ c : Fin (n + 1),
          epsilonFloorSplitIndex (tol / 2) n ≤ (c : ℕ) →
            lowerCutoff n ≤ cutoffOut n P c

/--
Market-clearing cutoff-floor clauses imply the selected-stable Theorem 4 form.
-/
theorem source_assumption_theorem4_suffix_cutoff_floor_of_market
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {tol : ℝ} {lowerCutoff : ℕ → ℝ}
    (h :
      source_assumption_theorem4_suffix_market_cutoff_floor
        Mseq (Admissible := Admissible) cutoffOut
        (tol := tol) lowerCutoff) :
    source_assumption_theorem4_suffix_cutoff_floor
      Mseq Iseq selected cutoffOut (tol := tol) lowerCutoff := by
  filter_upwards [h] with n hn a c hc
  exact
    hn a
      ((Iseq n).marketClearingCutoffOfStable
        (μ := (selected n a).1) (selected n a).2)
      ((Iseq n).marketClearingCutoffOfStable_marketClearing
        (μ := (selected n a).1) (selected n a).2)
      c hc

/--
Theorem 4 source low-count clause: eventually fewer than the deleted prefix
many market-clearing cutoffs lie below the common scalar lower floor.
-/
-- audit-premise: eventually, at most the deleted prefix many market-clearing cutoffs are below the Theorem 4 scalar lower floor
abbrev source_assumption_theorem4_suffix_market_low_cutoff_count
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    {Admissible : ℕ → Type u}
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {tol : ℝ} (lowerCutoff : ℕ → ℝ) : Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ _a : Admissible C, ∀ P : (Mseq C).Cutoff,
      (Mseq C).MarketClearing P →
        (lowCutoffIndexSet (cutoffOut C P) (lowerCutoff C)).card ≤
          epsilonFloorSplitIndex (tol / 2) C

/--
Theorem 4 selected-stable low-count clause: eventually fewer than the deleted
prefix many selected-stable cutoffs lie below the common scalar lower floor.
-/
-- audit-premise: eventually, at most the deleted prefix many selected-stable cutoffs are below the Theorem 4 scalar lower floor
abbrev source_assumption_theorem4_suffix_selected_stable_low_cutoff_count
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {tol : ℝ} (lowerCutoff : ℕ → ℝ) : Prop :=
  ∀ᶠ C : ℕ in atTop,
    ∀ _a : Admissible C,
      (lowCutoffIndexSet
        (cutoffOut C
          ((Iseq C).marketClearingCutoffOfStable
            (μ := (selected C _a).1) (selected C _a).2))
        (lowerCutoff C)).card ≤
          epsilonFloorSplitIndex (tol / 2) C

/--
Theorem 4 low-count bound from the market-level capacity contradiction.
-/
theorem source_assumption_theorem4_suffix_market_low_cutoff_count_of_capacity_contradiction
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Admissible : ℕ → Type u}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {tol : ℝ} {lowerCutoff : ℕ → ℝ}
    {OutcomeSeq : ℕ → Type*} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C)}
    {chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1))}
    {totalSupply : ℝ}
    (hfinite :
      source_assumption_market_outcome_finite Mseq OutcomeSeq outcomeLaw)
    (hchoiceMass_eq_aggregateDemand :
      source_assumption_market_choice_mass_eq_aggregateDemand
        Mseq OutcomeSeq outcomeLaw chosenCollege)
    (hcapacity_clear :
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          ∀ c : Fin (C + 1),
            (Mseq C).aggregateDemand P c = (Mseq C).capacity c)
    (hcapacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (hcontr :
      source_assumption_market_low_cutoff_capacity_contradiction
        Mseq cutoffOut
        (fun C : ℕ => epsilonFloorSplitIndex (tol / 2) C)
        (fun C (_a : Admissible C) => lowerCutoff C)
        OutcomeSeq outcomeLaw chosenCollege totalSupply) :
    source_assumption_theorem4_suffix_market_low_cutoff_count
      Mseq (Admissible := Admissible) cutoffOut
      (tol := tol) lowerCutoff :=
  source_assumption_market_low_cutoff_count_of_capacity_contradiction
    hfinite hchoiceMass_eq_aggregateDemand hcapacity_clear hcapacity_sum
    hcontr

/--
Theorem 4 low-count bound from the selected-stable capacity contradiction.
-/
theorem source_assumption_theorem4_suffix_selected_stable_low_cutoff_count_of_capacity_contradiction
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {tol : ℝ} {lowerCutoff : ℕ → ℝ}
    {OutcomeSeq : ℕ → Type*} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C)}
    {chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1))}
    {totalSupply : ℝ}
    (hfinite :
      source_assumption_selected_stable_outcome_finite
        Mseq Iseq OutcomeSeq outcomeLaw)
    (hchoiceMass_eq_aggregateDemand :
      source_assumption_selected_stable_choice_mass_eq_aggregateDemand
        Mseq Iseq selected OutcomeSeq outcomeLaw chosenCollege)
    (hcapacity_clear :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c : Fin (C + 1),
          (Mseq C).aggregateDemand
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2) c =
            (Mseq C).capacity c)
    (hcapacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (hcontr :
      source_assumption_selected_stable_low_cutoff_capacity_contradiction
        Mseq Iseq selected cutoffOut
        (fun C : ℕ => epsilonFloorSplitIndex (tol / 2) C)
        (fun C (_a : Admissible C) => lowerCutoff C)
        OutcomeSeq outcomeLaw chosenCollege totalSupply) :
    source_assumption_theorem4_suffix_selected_stable_low_cutoff_count
      Mseq Iseq selected cutoffOut (tol := tol) lowerCutoff :=
  source_assumption_selected_stable_low_cutoff_count_of_capacity_contradiction
    hfinite hchoiceMass_eq_aggregateDemand hcapacity_clear hcapacity_sum
    hcontr

/--
Sorted market-clearing cutoffs and the Theorem 4 low-count bound imply the
visible sorted-suffix cutoff-floor clause.
-/
theorem source_assumption_theorem4_suffix_market_cutoff_floor_of_sorted_low_count
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Admissible : ℕ → Type u}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {tol : ℝ} {lowerCutoff : ℕ → ℝ}
    (hsorted : source_assumption_market_cutoff_index_sorted Mseq cutoffOut)
    (hcount :
      source_assumption_theorem4_suffix_market_low_cutoff_count
        Mseq (Admissible := Admissible) cutoffOut
        (tol := tol) lowerCutoff) :
    source_assumption_theorem4_suffix_market_cutoff_floor
      Mseq (Admissible := Admissible) cutoffOut
      (tol := tol) lowerCutoff := by
  filter_upwards [hsorted, hcount] with C hsortedC hcountC a P hP c hc
  exact
    suffix_floor_of_sorted_lowCutoffIndexSet_card_le
      (hsortedC P hP) (hcountC a P hP) hc

/--
Sorted selected-stable cutoffs and the Theorem 4 selected low-count bound
imply the visible sorted-suffix cutoff-floor clause.
-/
theorem source_assumption_theorem4_suffix_cutoff_floor_of_selected_stable_sorted_low_count
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {tol : ℝ} {lowerCutoff : ℕ → ℝ}
    (hsorted :
      source_assumption_selected_stable_cutoff_index_sorted
        Mseq Iseq selected cutoffOut)
    (hcount :
      source_assumption_theorem4_suffix_selected_stable_low_cutoff_count
        Mseq Iseq selected cutoffOut (tol := tol) lowerCutoff) :
    source_assumption_theorem4_suffix_cutoff_floor
      Mseq Iseq selected cutoffOut (tol := tol) lowerCutoff := by
  filter_upwards [hsorted, hcount] with C hsortedC hcountC a c hc
  exact
    suffix_floor_of_sorted_lowCutoffIndexSet_card_le
      (hsortedC a) (hcountC a) hc

/--
Pointwise low-CDF power and outcome-event clauses imply the selected-stable
Theorem 4 sorted-suffix cutoff floor, without routing through an integrated
source-model package.
-/
theorem source_assumption_theorem4_suffix_cutoff_floor_of_market_pow_affordance_event_bridge
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {noiseLaw : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {tol : ℝ} {lowerCutoff : ℕ → ℝ}
    {eventValue : ∀ C : ℕ, Admissible C → ℝ}
    {OutcomeSeq : ℕ → Type*} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C)}
    {chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1))}
    {totalSupply : ℝ}
    (hfinite :
      source_assumption_selected_stable_outcome_finite
        Mseq Iseq OutcomeSeq outcomeLaw)
    (hchoiceMass_eq_aggregateDemand :
      source_assumption_selected_stable_choice_mass_eq_aggregateDemand
        Mseq Iseq selected OutcomeSeq outcomeLaw chosenCollege)
    (hcapacity_clear :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c : Fin (C + 1),
          (Mseq C).aggregateDemand
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2) c =
            (Mseq C).capacity c)
    (hcapacity_sum :
      source_assumption_total_capacity_sum Mseq totalSupply)
    (hsorted :
      source_assumption_selected_stable_cutoff_index_sorted
        Mseq Iseq selected cutoffOut)
    (hpow :
      source_assumption_market_low_cutoff_pow_exceeds_supply
        Mseq noiseLaw cutoffOut
        (fun C : ℕ => epsilonFloorSplitIndex (tol / 2) C)
        (fun C (_a : Admissible C) => lowerCutoff C)
        eventValue totalSupply)
    (hbridge :
      source_assumption_market_affordance_event_bridge
        Mseq noiseLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege) :
    source_assumption_theorem4_suffix_cutoff_floor
      Mseq Iseq selected cutoffOut (tol := tol) lowerCutoff :=
  source_assumption_theorem4_suffix_cutoff_floor_of_selected_stable_sorted_low_count
    hsorted
    (source_assumption_theorem4_suffix_selected_stable_low_cutoff_count_of_capacity_contradiction
      hfinite hchoiceMass_eq_aggregateDemand hcapacity_clear hcapacity_sum
      (source_assumption_selected_stable_low_cutoff_capacity_contradiction_of_market_pow_affordance_event_bridge
        hpow hbridge))

/--
Theorem 4 source high-tail rate at the scalar lower cutoff floor.
-/
-- audit-premise: eventually, the upper-tail mass at lowerCutoff-vHigh is at most sigma/(C+1)
abbrev source_assumption_theorem4_high_tail_floor_rate
    {Admissible : ℕ → Type u}
    (noiseLaw : MeasureTheory.Measure ℝ)
    {sigma vHigh : ℝ} (lowerCutoff : ℕ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    ∀ _a : Admissible n,
      AppliedModelingLib.Probability.upperTailMass noiseLaw
        (lowerCutoff n - vHigh) ≤
        sigma / ((n + 1 : ℕ) : ℝ)

/--
Explicit high-tail quantile used for the Theorem 4 lower cutoff floor.
-/
noncomputable def theorem4HighTailQuantile
    (noiseLaw : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (sigma : ℝ) (C : ℕ) : ℝ :=
  if htarget :
      0 < sigma / (((C + 1 : ℕ) : ℝ)) ∧
        sigma / (((C + 1 : ℕ) : ℝ)) < 1 then
    Classical.choose
      (AppliedModelingLib.Probability.exists_upperTailMass_Ici_bracket
        noiseLaw htarget.1 htarget.2)
  else
    0

/--
The explicit Theorem 4 high-tail quantile satisfies the required scalar
`sigma/(C+1)` tail rate eventually.
-/
theorem theorem4HighTailQuantile_upperTailMass_le_eventually
    (noiseLaw : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {sigma : ℝ} (hsigma_pos : 0 < sigma) :
    ∀ᶠ C : ℕ in atTop,
      AppliedModelingLib.Probability.upperTailMass noiseLaw
          (theorem4HighTailQuantile noiseLaw sigma C) ≤
        sigma / (((C + 1 : ℕ) : ℝ)) := by
  have hden_tendsto :
      Tendsto (fun C : ℕ => (((C + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have htarget_tendsto :
      Tendsto
        (fun C : ℕ => sigma / (((C + 1 : ℕ) : ℝ)))
        atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop hden_tendsto sigma
  have htarget_lt_one :
      ∀ᶠ C : ℕ in atTop,
        sigma / (((C + 1 : ℕ) : ℝ)) < 1 := by
    have hnear :
        ∀ᶠ C : ℕ in atTop,
          sigma / (((C + 1 : ℕ) : ℝ)) ∈ Set.Iio (1 : ℝ) :=
      htarget_tendsto (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) < 1))
    simpa using hnear
  filter_upwards [htarget_lt_one] with C htarget_lt
  have htarget_pos :
      0 < sigma / (((C + 1 : ℕ) : ℝ)) := by
    positivity
  unfold theorem4HighTailQuantile
  rw [dif_pos ⟨htarget_pos, htarget_lt⟩]
  exact
    (Classical.choose_spec
      (AppliedModelingLib.Probability.exists_upperTailMass_Ici_bracket
        noiseLaw htarget_pos htarget_lt)).1

/--
Under the paper's long-tail condition, the Theorem 4 high-tail quantile has
strict upper-tail mass asymptotically at least every fixed slack below its
target rate.  This bridge permits atoms; it does not use `NoAtoms`.
-/
theorem theorem4HighTailQuantile_upperTailMass_lower_bound_eventually_of_longTailed
    (noiseLaw : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {sigma slack : ℝ} (hsigma_pos : 0 < sigma)
    (hslack_pos : 0 < slack) (hslack_le_one : slack ≤ 1) :
    ∀ᶠ C : ℕ in atTop,
      (1 - slack) * (sigma / (((C + 1 : ℕ) : ℝ))) ≤
        AppliedModelingLib.Probability.upperTailMass noiseLaw
          (theorem4HighTailQuantile noiseLaw sigma C) := by
  have hden_tendsto :
      Tendsto (fun C : ℕ => (((C + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have htarget_zero :
      Tendsto (fun C : ℕ => sigma / (((C + 1 : ℕ) : ℝ)))
        atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop hden_tendsto sigma
  have htarget_lt_one :
      ∀ᶠ C : ℕ in atTop,
        sigma / (((C + 1 : ℕ) : ℝ)) < 1 := by
    have hnear :
        ∀ᶠ C : ℕ in atTop,
          sigma / (((C + 1 : ℕ) : ℝ)) ∈ Set.Iio (1 : ℝ) :=
      htarget_zero (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) < 1))
    simpa using hnear
  have hbracket : ∀ᶠ C : ℕ in atTop,
      AppliedModelingLib.Probability.upperTailMass noiseLaw
          (theorem4HighTailQuantile noiseLaw sigma C) ≤
        sigma / (((C + 1 : ℕ) : ℝ)) ∧
      sigma / (((C + 1 : ℕ) : ℝ)) ≤
        noiseLaw.real (Set.Ici (theorem4HighTailQuantile noiseLaw sigma C)) := by
    filter_upwards [htarget_lt_one] with C htarget_lt
    have htarget_pos :
        0 < sigma / (((C + 1 : ℕ) : ℝ)) := by
      positivity
    unfold theorem4HighTailQuantile
    rw [dif_pos ⟨htarget_pos, htarget_lt⟩]
    exact
      Classical.choose_spec
        (AppliedModelingLib.Probability.exists_upperTailMass_Ici_bracket
          noiseLaw htarget_pos htarget_lt)
  exact
    upperTailMass_quantile_lower_bound_eventually_of_longTailed
      noiseLaw hlong htarget_zero hbracket (d := 1) (by norm_num)
      hslack_pos hslack_le_one

/--
Under an explicit nonatomicity hypothesis, the Theorem 4 high-tail quantile
also supplies a strict upper-tail lower bound at the scalar target
`sigma / (C + 1)`.
-/
theorem theorem4HighTailQuantile_upperTailMass_lower_bound_eventually_noAtoms
    (noiseLaw : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure noiseLaw] [MeasureTheory.NoAtoms noiseLaw]
    {sigma : ℝ} (hsigma_pos : 0 < sigma) :
    ∀ᶠ C : ℕ in atTop,
      sigma / (((C + 1 : ℕ) : ℝ)) ≤
        AppliedModelingLib.Probability.upperTailMass noiseLaw
          (theorem4HighTailQuantile noiseLaw sigma C) := by
  have hden_tendsto :
      Tendsto (fun C : ℕ => (((C + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have htarget_tendsto :
      Tendsto
        (fun C : ℕ => sigma / (((C + 1 : ℕ) : ℝ)))
        atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop hden_tendsto sigma
  have htarget_lt_one :
      ∀ᶠ C : ℕ in atTop,
        sigma / (((C + 1 : ℕ) : ℝ)) < 1 := by
    have hnear :
        ∀ᶠ C : ℕ in atTop,
          sigma / (((C + 1 : ℕ) : ℝ)) ∈ Set.Iio (1 : ℝ) :=
      htarget_tendsto (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) < 1))
    simpa using hnear
  filter_upwards [htarget_lt_one] with C htarget_lt
  have htarget_pos :
      0 < sigma / (((C + 1 : ℕ) : ℝ)) := by
    positivity
  unfold theorem4HighTailQuantile
  rw [dif_pos ⟨htarget_pos, htarget_lt⟩]
  exact
    upperTailMass_lower_bound_of_real_Ici_bracket_noAtoms
      (noiseLaw := noiseLaw)
      ((Classical.choose_spec
        (AppliedModelingLib.Probability.exists_upperTailMass_Ici_bracket
          noiseLaw htarget_pos htarget_lt)).2)

/--
For the long-tailed regime of Theorem 4, the explicit high-tail quantile turns
a scalar crossing inequality at any fixed slack below `sigma / (C + 1)` into
the strict-tail split-power capacity clause.  Unlike the older nonatomic
route, this is valid for the paper's allowed atomic noise laws.
-/
theorem source_assumption_theorem4_low_cutoff_upper_tail_split_pow_exceeds_supply_of_quantile_longTailed
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {noiseLaw : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {Admissible : ℕ → Type u}
    {tol sigma slack totalSupply vHigh : ℝ}
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    (hsigma_pos : 0 < sigma)
    (hslack_pos : 0 < slack) (hslack_le_one : slack ≤ 1)
    (hcross :
      ∀ᶠ C : ℕ in atTop,
        ∀ _a : Admissible C,
          totalSupply <
            1 -
              (1 - (1 - slack) * (sigma / (((C + 1 : ℕ) : ℝ)))) ^
                (epsilonFloorSplitIndex (tol / 2) C + 1)) :
    source_assumption_market_low_cutoff_upper_tail_split_pow_exceeds_supply
      Mseq noiseLaw
      (fun C : ℕ => epsilonFloorSplitIndex (tol / 2) C)
      (fun C (_a : Admissible C) =>
        vHigh + theorem4HighTailQuantile noiseLaw sigma C)
      (fun _C (_a : Admissible _C) => vHigh)
      totalSupply := by
  refine
    source_assumption_market_low_cutoff_upper_tail_split_pow_exceeds_supply_of_scalar_tail_lower_bound
      (Mseq := Mseq)
      (noiseLaw := noiseLaw)
      (splitIndex := fun C : ℕ => epsilonFloorSplitIndex (tol / 2) C)
      (lowerCutoff := fun C (_a : Admissible C) =>
        vHigh + theorem4HighTailQuantile noiseLaw sigma C)
      (eventValue := fun _C (_a : Admissible _C) => vHigh)
      (scalarTail := fun C (_a : Admissible C) =>
        (1 - slack) * (sigma / (((C + 1 : ℕ) : ℝ))))
      ?_ hcross
  filter_upwards
    [theorem4HighTailQuantile_upperTailMass_lower_bound_eventually_of_longTailed
      noiseLaw hlong hsigma_pos hslack_pos hslack_le_one] with C hC a
  have harg :
      (vHigh + theorem4HighTailQuantile noiseLaw sigma C) - vHigh =
        theorem4HighTailQuantile noiseLaw sigma C := by
    ring
  simpa [harg] using hC

/--
For nonatomic noise laws, the active Theorem 4 strict-tail split-power
obligation reduces to the scalar crossing inequality at
`sigma / (C + 1)`.  This proves the legitimate quantile-to-strict-tail bridge
and leaves the scalar crossing estimate as the remaining analytic work.
-/
theorem source_assumption_theorem4_low_cutoff_upper_tail_split_pow_exceeds_supply_of_quantile_noAtoms
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {noiseLaw : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsProbabilityMeasure noiseLaw] [MeasureTheory.NoAtoms noiseLaw]
    {Admissible : ℕ → Type u}
    {tol sigma totalSupply vHigh : ℝ} (hsigma_pos : 0 < sigma)
    (hcross :
      ∀ᶠ C : ℕ in atTop,
        ∀ _a : Admissible C,
          totalSupply <
            1 -
              (1 - sigma / (((C + 1 : ℕ) : ℝ))) ^
                (epsilonFloorSplitIndex (tol / 2) C + 1)) :
    source_assumption_market_low_cutoff_upper_tail_split_pow_exceeds_supply
      Mseq noiseLaw
      (fun C : ℕ => epsilonFloorSplitIndex (tol / 2) C)
      (fun C (_a : Admissible C) =>
        vHigh + theorem4HighTailQuantile noiseLaw sigma C)
      (fun _C (_a : Admissible _C) => vHigh)
      totalSupply := by
  refine
    source_assumption_market_low_cutoff_upper_tail_split_pow_exceeds_supply_of_scalar_tail_lower_bound
      (Mseq := Mseq)
      (noiseLaw := noiseLaw)
      (splitIndex := fun C : ℕ => epsilonFloorSplitIndex (tol / 2) C)
      (lowerCutoff := fun C (_a : Admissible C) =>
        vHigh + theorem4HighTailQuantile noiseLaw sigma C)
      (eventValue := fun _C (_a : Admissible _C) => vHigh)
      (scalarTail := fun C (_a : Admissible C) =>
        sigma / (((C + 1 : ℕ) : ℝ)))
      ?_ hcross
  filter_upwards
    [theorem4HighTailQuantile_upperTailMass_lower_bound_eventually_noAtoms
      noiseLaw hsigma_pos] with C hC a
  have harg :
      (vHigh + theorem4HighTailQuantile noiseLaw sigma C) - vHigh =
        theorem4HighTailQuantile noiseLaw sigma C := by
    ring
  simpa [harg] using hC

/--
Exponential-relaxation version of the nonatomic Theorem 4 quantile helper.
It reduces the active strict-tail split-power premise to the corresponding
eventual `1 - exp (-m*p)` supply-gap inequality.
-/
theorem source_assumption_theorem4_low_cutoff_upper_tail_split_pow_exceeds_supply_of_quantile_noAtoms_exp
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {noiseLaw : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsProbabilityMeasure noiseLaw] [MeasureTheory.NoAtoms noiseLaw]
    {Admissible : ℕ → Type u}
    {tol sigma totalSupply vHigh : ℝ} (hsigma_pos : 0 < sigma)
    (hcross_exp :
      ∀ᶠ C : ℕ in atTop,
        ∀ _a : Admissible C,
          totalSupply <
            1 - Real.exp
              (-(((epsilonFloorSplitIndex (tol / 2) C + 1 : ℕ) : ℝ) *
                (sigma / (((C + 1 : ℕ) : ℝ)))))) :
    source_assumption_market_low_cutoff_upper_tail_split_pow_exceeds_supply
      Mseq noiseLaw
      (fun C : ℕ => epsilonFloorSplitIndex (tol / 2) C)
      (fun C (_a : Admissible C) =>
        vHigh + theorem4HighTailQuantile noiseLaw sigma C)
      (fun _C (_a : Admissible _C) => vHigh)
      totalSupply := by
  refine
    source_assumption_market_low_cutoff_upper_tail_split_pow_exceeds_supply_of_scalar_tail_lower_bound_exp
      (Mseq := Mseq)
      (noiseLaw := noiseLaw)
      (splitIndex := fun C : ℕ => epsilonFloorSplitIndex (tol / 2) C)
      (lowerCutoff := fun C (_a : Admissible C) =>
        vHigh + theorem4HighTailQuantile noiseLaw sigma C)
      (eventValue := fun _C (_a : Admissible _C) => vHigh)
      (scalarTail := fun C (_a : Admissible C) =>
        sigma / (((C + 1 : ℕ) : ℝ)))
      ?_ ?_ ?_ hcross_exp
  · filter_upwards
      [theorem4HighTailQuantile_upperTailMass_lower_bound_eventually_noAtoms
        noiseLaw hsigma_pos] with C hC a
    have harg :
        (vHigh + theorem4HighTailQuantile noiseLaw sigma C) - vHigh =
          theorem4HighTailQuantile noiseLaw sigma C := by
      ring
    simpa [harg] using hC
  · exact Filter.Eventually.of_forall (fun C a => by positivity)
  · filter_upwards
      [theorem4HighTailQuantile_upperTailMass_lower_bound_eventually_noAtoms
        noiseLaw hsigma_pos] with C hC a
    exact
      le_trans hC
        (AppliedModelingLib.Probability.upperTailMass_le_one noiseLaw
          (theorem4HighTailQuantile noiseLaw sigma C))

/--
Static-gap version of the nonatomic Theorem 4 quantile helper.  The floor
arithmetic proves the exponential target from the explicit supply gap
`totalSupply < 1 - exp (-(tol/2) * sigma)`.
-/
theorem source_assumption_theorem4_low_cutoff_upper_tail_split_pow_exceeds_supply_of_quantile_noAtoms_static_exp_gap
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {noiseLaw : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsProbabilityMeasure noiseLaw] [MeasureTheory.NoAtoms noiseLaw]
    {Admissible : ℕ → Type u}
    {tol sigma totalSupply vHigh : ℝ}
    (htol_pos : 0 < tol) (hsigma_pos : 0 < sigma)
    (hgap :
      totalSupply <
        1 - Real.exp (-((tol / 2) * sigma))) :
    source_assumption_market_low_cutoff_upper_tail_split_pow_exceeds_supply
      Mseq noiseLaw
      (fun C : ℕ => epsilonFloorSplitIndex (tol / 2) C)
      (fun C (_a : Admissible C) =>
        vHigh + theorem4HighTailQuantile noiseLaw sigma C)
      (fun _C (_a : Admissible _C) => vHigh)
      totalSupply := by
  refine
    source_assumption_theorem4_low_cutoff_upper_tail_split_pow_exceeds_supply_of_quantile_noAtoms_exp
      (Mseq := Mseq) (noiseLaw := noiseLaw)
      (Admissible := Admissible) (tol := tol) (sigma := sigma)
      (totalSupply := totalSupply) (vHigh := vHigh) hsigma_pos ?_
  exact
    epsilonFloorSplitIndex_exp_supply_gap_of_static_gap
      (Admissible := Admissible)
      (delta := tol / 2) (tau := sigma)
      (totalSupply := totalSupply)
      (by linarith) hsigma_pos hgap

/--
Choosing the Theorem 4 lower cutoff as the high endpoint plus the explicit
high-tail quantile discharges the separate high-tail-rate source clause.
-/
theorem source_assumption_theorem4_high_tail_floor_rate_of_quantile_floor
    {Admissible : ℕ → Type u}
    (noiseLaw : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {sigma : ℝ} (hsigma_pos : 0 < sigma) (vHigh : ℝ) :
    source_assumption_theorem4_high_tail_floor_rate
      (Admissible := Admissible) noiseLaw
      (sigma := sigma) (vHigh := vHigh)
      (fun C => vHigh + theorem4HighTailQuantile noiseLaw sigma C) := by
  filter_upwards
    [theorem4HighTailQuantile_upperTailMass_le_eventually
      noiseLaw hsigma_pos] with C hC a
  have harg :
      (vHigh + theorem4HighTailQuantile noiseLaw sigma C) - vHigh =
        theorem4HighTailQuantile noiseLaw sigma C := by
    ring
  simpa [harg] using hC

/--
Theorem 2 scalar market endpoint package with the high-tail-rate lower cutoff
chosen as an explicit distributional quantile floor.

This keeps the market cutoff-floor and endpoint inequalities visible, while the
separate scalar high-tail rate is derived by
`source_assumption_theorem2_scalar_market_endpoint_estimates_of_quantile_floor`.
-/
-- audit-premise: PG24 Theorem 2 scalar sorted-suffix endpoint estimates with the lower cutoff fixed to the explicit high-tail quantile floor
def source_assumption_theorem2_scalar_market_endpoint_estimates_quantile_floor
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (noiseLaw : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply : ℝ} : Prop :=
  ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
    0 <
      1 - totalSupply - epsilon -
        (1 - Real.exp (-(2 * epsilon * sigma))) →
    ∃ vLow vHigh vStar : ℝ,
      vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
            vHigh + theorem4HighTailQuantile noiseLaw sigma C ≤
              cutoffOut C P c) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          (1 - epsilon) *
              cutoffAffordanceProbability
                (MeasureTheory.Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
                vLow
                (cutoffOut C P) ≤
            totalSupply) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          AppliedModelingLib.Matching.activeCapacity
              (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
              (Mseq C).capacity - epsilon ≤
            cutoffAffordanceProbability
              (MeasureTheory.Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C)
              vHigh
              (cutoffOut C P)) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          Real.sqrt epsilon *
              (1 - totalSupply - epsilon -
                (1 - Real.exp (-(2 * epsilon * sigma)))) *
              cutoffAffordanceProbability
                (MeasureTheory.Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                vStar
                (cutoffOut C P) ≤
            AppliedModelingLib.Matching.activeCapacity
              (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
              (Mseq C).capacity)

/--
The explicit quantile-floor endpoint package implies the existing Theorem 2
scalar market endpoint package.
-/
theorem source_assumption_theorem2_scalar_market_endpoint_estimates_of_quantile_floor
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {noiseLaw : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {totalSupply : ℝ}
    (h :
      source_assumption_theorem2_scalar_market_endpoint_estimates_quantile_floor
        Mseq noiseLaw cutoffOut (totalSupply := totalSupply)) :
    source_assumption_theorem2_scalar_market_endpoint_estimates
      Mseq noiseLaw cutoffOut (totalSupply := totalSupply) := by
  intro v epsilon sigma hepsilon hsigma hden
  rcases h v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, hvLow, hvHigh, hvStar, hvStrict,
      hcutoff_lower, hlarge_endpoint, hlarge_capacity_lower,
      hsmall_capacity_lower⟩
  refine
    ⟨vLow, vHigh, vStar,
      (fun C => vHigh + theorem4HighTailQuantile noiseLaw sigma C),
      hvLow, hvHigh, hvStar, hvStrict, hcutoff_lower, ?_,
      hlarge_endpoint, hlarge_capacity_lower, hsmall_capacity_lower⟩
  filter_upwards
    [theorem4HighTailQuantile_upperTailMass_le_eventually
      noiseLaw hsigma] with C hC
  have harg :
      (vHigh + theorem4HighTailQuantile noiseLaw sigma C) - vHigh =
        theorem4HighTailQuantile noiseLaw sigma C := by
    ring
  simpa [harg] using hC

/--
Theorem 2 selected-stable scalar endpoint package with the lower cutoff fixed
to the explicit distributional high-tail quantile floor.

This is the narrower form needed by the active PG24 theorem route: the final
statement quantifies over stable matchings through the A-L selected
market-clearing cutoff, so the endpoint inequalities only need to hold at
those selected-stable cutoffs.
-/
-- audit-premise: PG24 Theorem 2 selected-stable scalar sorted-suffix endpoint estimates with the lower cutoff fixed to the explicit high-tail quantile floor
def source_assumption_theorem2_scalar_endpoint_estimates_quantile_floor
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (noiseLaw : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    {totalSupply : ℝ} : Prop :=
  ∀ v epsilon sigma, 0 < epsilon → 0 < sigma →
    0 <
      1 - totalSupply - epsilon -
        (1 - Real.exp (-(2 * epsilon * sigma))) →
    ∃ vLow vHigh vStar : ℝ,
      vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar ∧ vLow < vHigh ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
            vHigh + theorem4HighTailQuantile noiseLaw sigma C ≤
              cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable
                  (μ := μ.1) μ.2) c) ∧
      (∀ᶠ C : ℕ in atTop,
        ∀ μ : { μ : (Mseq C).Matching // (Mseq C).Stable μ },
          (1 - epsilon) *
              cutoffAffordanceProbability
                (MeasureTheory.Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
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
              (MeasureTheory.Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
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
                (MeasureTheory.Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
                vStar
                (cutoffOut C
                  ((Iseq C).marketClearingCutoffOfStable
                    (μ := μ.1) μ.2)) ≤
            AppliedModelingLib.Matching.activeCapacity
              (indexPrefixSmall (epsilonFloorSplitIndex epsilon C) C)
              (Mseq C).capacity)

/--
The selected-stable explicit quantile-floor endpoint package implies the
existing selected-stable scalar endpoint package.
-/
theorem source_assumption_theorem2_scalar_endpoint_estimates_of_quantile_floor
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {noiseLaw : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {totalSupply : ℝ}
    (h :
      source_assumption_theorem2_scalar_endpoint_estimates_quantile_floor
        Mseq Iseq noiseLaw cutoffOut (totalSupply := totalSupply)) :
    source_assumption_theorem2_scalar_endpoint_estimates
      Mseq Iseq noiseLaw cutoffOut (totalSupply := totalSupply) := by
  intro v epsilon sigma hepsilon hsigma hden
  rcases h v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, hvLow, hvHigh, hvStar, hvStrict,
      hcutoff_lower, hlarge_endpoint, hlarge_capacity_lower,
      hsmall_capacity_lower⟩
  refine
    ⟨vLow, vHigh, vStar,
      (fun C => vHigh + theorem4HighTailQuantile noiseLaw sigma C),
      hvLow, hvHigh, hvStar, hvStrict, hcutoff_lower, ?_,
      hlarge_endpoint, hlarge_capacity_lower, hsmall_capacity_lower⟩
  filter_upwards
    [theorem4HighTailQuantile_upperTailMass_le_eventually
      noiseLaw hsigma] with C hC _μ
  have harg :
      (vHigh + theorem4HighTailQuantile noiseLaw sigma C) - vHigh =
        theorem4HighTailQuantile noiseLaw sigma C := by
    ring
  simpa [harg] using hC

/--
Market-level quantile-floor endpoint estimates imply the selected-stable
quantile-floor endpoint package.
-/
theorem source_assumption_theorem2_scalar_endpoint_estimates_quantile_floor_of_market
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {noiseLaw : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {totalSupply : ℝ}
    (h :
      source_assumption_theorem2_scalar_market_endpoint_estimates_quantile_floor
        Mseq noiseLaw cutoffOut (totalSupply := totalSupply)) :
    source_assumption_theorem2_scalar_endpoint_estimates_quantile_floor
      Mseq Iseq noiseLaw cutoffOut (totalSupply := totalSupply) := by
  intro v epsilon sigma hepsilon hsigma hden
  rcases h v epsilon sigma hepsilon hsigma hden with
    ⟨vLow, vHigh, vStar, hvLow, hvHigh, hvStar, hvStrict,
      hcutoff_lower, hlarge_endpoint, hlarge_capacity_lower,
      hsmall_capacity_lower⟩
  refine
    ⟨vLow, vHigh, vStar, hvLow, hvHigh, hvStar, hvStrict,
      ?_, ?_, ?_, ?_⟩
  · filter_upwards [hcutoff_lower] with C hC μ c hc
    exact
      hC
        ((Iseq C).marketClearingCutoffOfStable
          (μ := μ.1) μ.2)
        ((Iseq C).marketClearingCutoffOfStable_marketClearing
          (μ := μ.1) μ.2)
        c hc
  · filter_upwards [hlarge_endpoint] with C hC μ
    exact
      hC
        ((Iseq C).marketClearingCutoffOfStable
          (μ := μ.1) μ.2)
        ((Iseq C).marketClearingCutoffOfStable_marketClearing
          (μ := μ.1) μ.2)
  · filter_upwards [hlarge_capacity_lower] with C hC μ
    exact
      hC
        ((Iseq C).marketClearingCutoffOfStable
          (μ := μ.1) μ.2)
        ((Iseq C).marketClearingCutoffOfStable_marketClearing
          (μ := μ.1) μ.2)
  · filter_upwards [hsmall_capacity_lower] with C hC μ
    exact
      hC
        ((Iseq C).marketClearingCutoffOfStable
          (μ := μ.1) μ.2)
        ((Iseq C).marketClearingCutoffOfStable_marketClearing
          (μ := μ.1) μ.2)

/--
Source model package for the active PG24 Theorem 3 coalition-attenuation
route.

This bundles the sorted-suffix cutoff floor, low-tail floor, and upper-ceiling
separation clauses.  The paper-facing theorem derives the existential
coalition attenuation witness from these clauses and the concrete iid
cutoff-affordance calculations.
-/
-- audit-premise: PG24 Theorem 3 sorted-suffix cutoff-floor, low-tail, and upper-ceiling source clauses
structure Theorem3CoalitionAttenuationSourceModel
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (epsilon : ℝ)
    (threshold lowerCutoff upperCutoff :
      ∀ C : ℕ, Admissible C → ℝ) : Prop where
  cutoff_floor :
    source_assumption_theorem3_suffix_market_cutoff_floor
      Mseq cutoffOut (epsilon := epsilon) lowerCutoff
  low_tail_floor :
    source_assumption_theorem3_suffix_low_tail_floor_halfDiv
      noiseLaw (epsilon := epsilon) threshold lowerCutoff
  upper_ceiling :
    source_assumption_theorem3_suffix_market_upper_ceiling_atBot
      Mseq cutoffOut (epsilon := epsilon) threshold upperCutoff

/--
Theorem 3 source model with the low-tail floor derived from an explicit
distributional quantile instead of assumed separately.

The only market primitives exposed here are the sorted-suffix cutoff floor at the
explicit low-tail quantile floor and the upper-ceiling separation.  The low-tail
probability rate follows from `theorem3LowTailQuantile_upperTailMass_le_eventually`.
-/
-- audit-premise: PG24 Theorem 3 sorted-suffix cutoff-floor at the explicit low-tail quantile and upper-ceiling source clauses
structure Theorem3CoalitionAttenuationQuantileSourceModel
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (epsilon : ℝ)
    (threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ) : Prop where
  cutoff_floor :
    source_assumption_theorem3_suffix_market_cutoff_floor
      Mseq cutoffOut (epsilon := epsilon)
      (fun C a =>
        threshold C a - epsilon +
          theorem3LowTailQuantile noiseLaw epsilon C)
  upper_ceiling :
    source_assumption_theorem3_suffix_market_upper_ceiling_atBot
      Mseq cutoffOut (epsilon := epsilon) threshold upperCutoff

/--
Source model package for the active PG24 Theorem 4 coalition-amplification
route.

This bundles the regular interval mass, sorted-suffix cutoff floor, and
long-tail high-endpoint rate clauses.  The checked endpoint calculation derives
the needed tail-region condition from the high-tail rate and long-tailed
upper-tail positivity, so no separate lower-endpoint divergence premise is
exposed here.
-/
-- audit-premise: PG24 Theorem 4 regular-interval mass, sorted-suffix cutoff-floor, and high-tail source clauses
structure Theorem4CoalitionAmplificationSourceModel
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (valueMass : ∀ C : ℕ, Admissible C → Set ℝ → ℝ)
    (tol sigma vLow vHigh : ℝ)
    (lowerCutoff : ℕ → ℝ) : Prop where
  regular_interval_mass :
    source_assumption_theorem4_regular_interval_mass
      valueMass (tol := tol) (vLow := vLow) (vHigh := vHigh)
  cutoff_floor :
    source_assumption_theorem4_suffix_market_cutoff_floor
      Mseq (Admissible := Admissible) cutoffOut (tol := tol) lowerCutoff
  high_tail_floor_rate :
    source_assumption_theorem4_high_tail_floor_rate
      (Admissible := Admissible) noiseLaw
      (sigma := sigma) (vHigh := vHigh) lowerCutoff

/--
Theorem 4 source model with the scalar high-tail rate derived from an explicit
distributional quantile instead of assumed separately.

The visible market primitive is the sorted-suffix cutoff floor at
`vHigh + theorem4HighTailQuantile noiseLaw sigma C`; the high-tail probability
rate follows from the quantile construction when `sigma > 0`.
-/
-- audit-premise: PG24 Theorem 4 regular-interval mass and sorted-suffix cutoff-floor at the explicit high-tail quantile
structure Theorem4CoalitionAmplificationQuantileSourceModel
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (valueMass : ∀ C : ℕ, Admissible C → Set ℝ → ℝ)
    (tol sigma vLow vHigh : ℝ) : Prop where
  regular_interval_mass :
    source_assumption_theorem4_regular_interval_mass
      valueMass (tol := tol) (vLow := vLow) (vHigh := vHigh)
  cutoff_floor :
    source_assumption_theorem4_suffix_market_cutoff_floor
      Mseq (Admissible := Admissible) cutoffOut (tol := tol)
      (fun C => vHigh + theorem4HighTailQuantile noiseLaw sigma C)

/--
Theorem 4 source model with the regular-set mass derived from the paper's
exceptional-set form, and the scalar high-tail rate derived from an explicit
distributional quantile.
-/
-- audit-premise: PG24 Theorem 4 exceptional-set regular interval source clause and sorted-suffix cutoff-floor at the explicit high-tail quantile
structure Theorem4CoalitionAmplificationExceptionQuantileSourceModel
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (valueMass : ∀ C : ℕ, Admissible C → Set ℝ → ℝ)
    (delta tol sigma vLow vHigh : ℝ) : Prop where
  regular_interval_exception :
    source_assumption_theorem4_regular_interval_exception_bound
      valueMass (delta := delta) (tol := tol)
      (vLow := vLow) (vHigh := vHigh)
  cutoff_floor :
    source_assumption_theorem4_suffix_market_cutoff_floor
      Mseq (Admissible := Admissible) cutoffOut (tol := tol)
      (fun C => vHigh + theorem4HighTailQuantile noiseLaw sigma C)

/--
Shared sorted-suffix cutoff-geometry certificate for the PG24 coalition
theorems.

The source proofs for Theorems 3 and 4 both rely on the same market-clearing
phenomenon: after deleting a small sorted prefix, the remaining coalition
cutoffs satisfy the large-cutoff floor needed by the endpoint estimates, while
Theorem 3 also needs the complementary upper-ceiling separation for the high
endpoint.  This record keeps that remaining A-L/market-clearing proof debt as a
single reusable certificate instead of duplicating theorem-specific cutoff
floor premises.
-/
-- audit-premise: PG24 coalition sorted-suffix cutoff geometry for Theorems 3 and 4
structure Theorem34CoalitionSuffixCutoffGeometrySourceModel
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (epsilon tol sigma vHigh : ℝ)
    (threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ) : Prop where
  theorem3_cutoff_floor :
    source_assumption_theorem3_suffix_market_cutoff_floor
      Mseq cutoffOut (epsilon := epsilon)
      (fun C a =>
        threshold C a - epsilon +
          theorem3LowTailQuantile noiseLaw epsilon C)
  theorem3_upper_ceiling :
    source_assumption_theorem3_suffix_market_upper_ceiling_atBot
      Mseq cutoffOut (epsilon := epsilon) threshold upperCutoff
  theorem4_cutoff_floor :
    source_assumption_theorem4_suffix_market_cutoff_floor
      Mseq (Admissible := Admissible) cutoffOut (tol := tol)
      (fun C => vHigh + theorem4HighTailQuantile noiseLaw sigma C)

/--
Count-based version of the shared PG24 coalition cutoff-geometry certificate.

This is closer to the paper proof: the market argument shows that only the
deleted sorted prefix can remain below the relevant scalar cutoff floor; Lean
then proves the finite sorted-suffix implication via
`suffix_floor_of_sorted_lowCutoffIndexSet_card_le`.
-/
-- audit-premise: PG24 coalition sorted-cutoff order, low-count bounds, and upper-ceiling geometry for Theorems 3 and 4
structure Theorem34CoalitionSuffixCutoffCountGeometrySourceModel
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (epsilon tol sigma vHigh : ℝ)
    (threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ) : Prop where
  cutoff_sorted :
    source_assumption_market_cutoff_index_sorted Mseq cutoffOut
  theorem3_low_count :
    source_assumption_theorem3_suffix_market_low_cutoff_count
      Mseq cutoffOut (epsilon := epsilon)
      (fun C a =>
        threshold C a - epsilon +
          theorem3LowTailQuantile noiseLaw epsilon C)
  theorem3_upper_ceiling :
    source_assumption_theorem3_suffix_market_upper_ceiling_atBot
      Mseq cutoffOut (epsilon := epsilon) threshold upperCutoff
  theorem4_low_count :
    source_assumption_theorem4_suffix_market_low_cutoff_count
      Mseq (Admissible := Admissible) cutoffOut (tol := tol)
      (fun C => vHigh + theorem4HighTailQuantile noiseLaw sigma C)

/--
Capacity-contradiction version of the shared PG24 coalition cutoff-geometry
certificate.

This exposes the remaining market argument at the level used in the paper:
too many low cutoffs must create a matched event whose mass exceeds total
capacity.  Lean then derives the low-count bounds from choice-mass semantics,
exact-fill market clearing, and total-capacity normalization.
-/
-- audit-premise: PG24 coalition sorted-cutoff order plus low-cutoff high-mass matched-event contradictions for Theorems 3 and 4
structure Theorem34CoalitionSuffixCutoffCapacityContradictionSourceModel
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    (totalSupply epsilon tol sigma vHigh : ℝ)
    (threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ) : Prop where
  outcome_probability :
    source_assumption_market_outcome_probability Mseq OutcomeSeq outcomeLaw
  choice_mass_eq_aggregateDemand :
    source_assumption_market_choice_mass_eq_aggregateDemand
      Mseq OutcomeSeq outcomeLaw chosenCollege
  capacity_sum :
    source_assumption_total_capacity_sum Mseq totalSupply
  cutoff_sorted :
    source_assumption_market_cutoff_index_sorted Mseq cutoffOut
  theorem3_capacity_contradiction :
    source_assumption_market_low_cutoff_capacity_contradiction
      Mseq cutoffOut
      (fun C : ℕ => epsilonFloorSplitIndex (epsilon / 2) C)
      (fun C a =>
        threshold C a - epsilon +
          theorem3LowTailQuantile noiseLaw epsilon C)
      OutcomeSeq outcomeLaw chosenCollege totalSupply
  theorem3_upper_ceiling :
    source_assumption_theorem3_suffix_market_upper_ceiling_atBot
      Mseq cutoffOut (epsilon := epsilon) threshold upperCutoff
  theorem4_capacity_contradiction :
    source_assumption_market_low_cutoff_capacity_contradiction
      Mseq cutoffOut
      (fun C : ℕ => epsilonFloorSplitIndex (tol / 2) C)
      (fun C (_a : Admissible C) =>
        vHigh + theorem4HighTailQuantile noiseLaw sigma C)
      OutcomeSeq outcomeLaw chosenCollege totalSupply

/--
Integrated-capacity version of the shared PG24 coalition cutoff-geometry
certificate.

This is closer to Lemma 11 in the paper than a pre-built high-mass event: the
source supplies the value-integrated low-cutoff affordability lower bound and
the outcome-model bridge turning that integral into matched outcomes.
-/
-- audit-premise: PG24 coalition sorted-cutoff order plus integrated low-cutoff affordability contradictions for Theorems 3 and 4
structure Theorem34CoalitionSuffixCutoffIntegratedCapacitySourceModel
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    (totalSupply epsilon tol sigma vHigh : ℝ)
    (threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ) : Prop where
  outcome_probability :
    source_assumption_market_outcome_probability Mseq OutcomeSeq outcomeLaw
  choice_mass_eq_aggregateDemand :
    source_assumption_market_choice_mass_eq_aggregateDemand
      Mseq OutcomeSeq outcomeLaw chosenCollege
  capacity_sum :
    source_assumption_total_capacity_sum Mseq totalSupply
  value_probability :
    source_assumption_market_value_probability valueLaw
  cutoff_sorted :
    source_assumption_market_cutoff_index_sorted Mseq cutoffOut
  integrated_affordance_event_bridge :
    source_assumption_market_integrated_affordance_event_bridge
      Mseq noiseLaw valueLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege
  theorem3_floor_region_bound_exceeds_supply :
    source_assumption_market_low_cutoff_floor_split_region_bound_exceeds_supply
      Mseq noiseLaw valueLaw cutoffOut
      (fun C : ℕ => epsilonFloorSplitIndex (epsilon / 2) C)
      (fun C a =>
        threshold C a - epsilon +
          theorem3LowTailQuantile noiseLaw epsilon C)
      totalSupply
  theorem3_upper_ceiling :
    source_assumption_theorem3_suffix_market_upper_ceiling_atBot
      Mseq cutoffOut (epsilon := epsilon) threshold upperCutoff
  theorem4_floor_region_bound_exceeds_supply :
    source_assumption_market_low_cutoff_floor_split_region_bound_exceeds_supply
      Mseq noiseLaw valueLaw cutoffOut
      (fun C : ℕ => epsilonFloorSplitIndex (tol / 2) C)
      (fun C (_a : Admissible C) =>
        vHigh + theorem4HighTailQuantile noiseLaw sigma C)
      totalSupply

/--
The integrated-capacity certificate implies the capacity-contradiction
certificate.
-/
theorem theorem34_coalition_suffix_cutoff_capacity_contradiction_of_integrated_capacity
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {noiseLaw : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ}
    {OutcomeSeq : ℕ → Type*} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C)}
    {chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1))}
    {totalSupply epsilon tol sigma vHigh : ℝ}
    {threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (H :
      Theorem34CoalitionSuffixCutoffIntegratedCapacitySourceModel
        Mseq Iseq selected noiseLaw cutoffOut valueLaw OutcomeSeq
        outcomeLaw chosenCollege totalSupply epsilon tol sigma vHigh
        threshold upperCutoff) :
    Theorem34CoalitionSuffixCutoffCapacityContradictionSourceModel
      Mseq Iseq selected noiseLaw cutoffOut OutcomeSeq outcomeLaw
      chosenCollege totalSupply epsilon tol sigma vHigh
      threshold upperCutoff where
  outcome_probability := H.outcome_probability
  choice_mass_eq_aggregateDemand := H.choice_mass_eq_aggregateDemand
  capacity_sum := H.capacity_sum
  cutoff_sorted := H.cutoff_sorted
  theorem3_capacity_contradiction :=
    source_assumption_market_low_cutoff_capacity_contradiction_of_integrated_affordance_event_bridge
      (source_assumption_market_low_cutoff_integral_exceeds_supply_of_floor_pow_integral
        (source_assumption_market_value_finite_of_probability
          H.value_probability)
        (source_assumption_market_low_cutoff_floor_pow_integral_exceeds_supply_of_region_bound
          H.value_probability
          (source_assumption_market_low_cutoff_floor_region_bound_exceeds_supply_of_split_region_bound
            H.theorem3_floor_region_bound_exceeds_supply)))
      H.integrated_affordance_event_bridge
  theorem3_upper_ceiling := H.theorem3_upper_ceiling
  theorem4_capacity_contradiction :=
    source_assumption_market_low_cutoff_capacity_contradiction_of_integrated_affordance_event_bridge
      (source_assumption_market_low_cutoff_integral_exceeds_supply_of_floor_pow_integral
        (source_assumption_market_value_finite_of_probability
          H.value_probability)
        (source_assumption_market_low_cutoff_floor_pow_integral_exceeds_supply_of_region_bound
          H.value_probability
          (source_assumption_market_low_cutoff_floor_region_bound_exceeds_supply_of_split_region_bound
            H.theorem4_floor_region_bound_exceeds_supply)))
      H.integrated_affordance_event_bridge

/--
The capacity-contradiction certificate implies the count-based geometry
certificate once exact-fill market clearing is supplied by the A-L source
model.
-/
theorem theorem34_coalition_suffix_cutoff_count_geometry_of_capacity_contradiction
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {noiseLaw : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {OutcomeSeq : ℕ → Type*} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C)}
    {chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1))}
    {totalSupply epsilon tol sigma vHigh : ℝ}
    {threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (hcapacity_clear :
      ∀ᶠ C : ℕ in atTop,
        ∀ P : (Mseq C).Cutoff, (Mseq C).MarketClearing P →
          ∀ c : Fin (C + 1),
            (Mseq C).aggregateDemand P c = (Mseq C).capacity c)
    (H :
      Theorem34CoalitionSuffixCutoffCapacityContradictionSourceModel
        Mseq Iseq selected noiseLaw cutoffOut OutcomeSeq outcomeLaw
        chosenCollege totalSupply epsilon tol sigma vHigh
        threshold upperCutoff) :
    Theorem34CoalitionSuffixCutoffCountGeometrySourceModel
      Mseq Iseq selected noiseLaw cutoffOut epsilon tol sigma vHigh
      threshold upperCutoff where
  cutoff_sorted := H.cutoff_sorted
  theorem3_low_count :=
    source_assumption_theorem3_suffix_market_low_cutoff_count_of_capacity_contradiction
      (source_assumption_market_outcome_finite_of_probability
        H.outcome_probability)
      H.choice_mass_eq_aggregateDemand hcapacity_clear
      H.capacity_sum H.theorem3_capacity_contradiction
  theorem3_upper_ceiling := H.theorem3_upper_ceiling
  theorem4_low_count :=
    source_assumption_theorem4_suffix_market_low_cutoff_count_of_capacity_contradiction
      (source_assumption_market_outcome_finite_of_probability
        H.outcome_probability)
      H.choice_mass_eq_aggregateDemand hcapacity_clear
      H.capacity_sum H.theorem4_capacity_contradiction

/--
The count-based geometry certificate implies the older suffix-floor geometry
certificate.
-/
theorem theorem34_coalition_suffix_cutoff_geometry_of_sorted_low_count
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {noiseLaw : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {epsilon tol sigma vHigh : ℝ}
    {threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (H :
      Theorem34CoalitionSuffixCutoffCountGeometrySourceModel
        Mseq Iseq selected noiseLaw cutoffOut epsilon tol sigma vHigh
        threshold upperCutoff) :
    Theorem34CoalitionSuffixCutoffGeometrySourceModel
      Mseq Iseq selected noiseLaw cutoffOut epsilon tol sigma vHigh
      threshold upperCutoff where
  theorem3_cutoff_floor :=
    source_assumption_theorem3_suffix_market_cutoff_floor_of_sorted_low_count
      H.cutoff_sorted H.theorem3_low_count
  theorem3_upper_ceiling := H.theorem3_upper_ceiling
  theorem4_cutoff_floor :=
    source_assumption_theorem4_suffix_market_cutoff_floor_of_sorted_low_count
      H.cutoff_sorted H.theorem4_low_count

/--
Selected-stable version of the shared PG24 coalition cutoff-geometry
certificate.

Unlike `Theorem34CoalitionSuffixCutoffGeometrySourceModel`, this source package
only speaks about the selected stable cutoff used in the paper-facing theorem
route.
-/
-- audit-premise: PG24 selected-stable coalition sorted-suffix cutoff geometry for Theorems 3 and 4
structure Theorem34SelectedStableCoalitionSuffixCutoffGeometrySourceModel
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (epsilon tol sigma vHigh : ℝ)
    (threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ) : Prop where
  theorem3_cutoff_floor :
    source_assumption_theorem3_suffix_cutoff_floor
      Mseq Iseq selected cutoffOut (epsilon := epsilon)
      (fun C a =>
        threshold C a - epsilon +
          theorem3LowTailQuantile noiseLaw epsilon C)
  theorem3_upper_ceiling :
    source_assumption_theorem3_suffix_upper_ceiling_atBot
      Mseq Iseq selected cutoffOut (epsilon := epsilon)
      threshold upperCutoff
  theorem4_cutoff_floor :
    source_assumption_theorem4_suffix_cutoff_floor
      Mseq Iseq selected cutoffOut (tol := tol)
      (fun C => vHigh + theorem4HighTailQuantile noiseLaw sigma C)

/--
Selected-stable count-based version of the shared PG24 coalition cutoff
geometry certificate.
-/
-- audit-premise: PG24 selected-stable sorted-cutoff order, low-count bounds, and upper-ceiling geometry for Theorems 3 and 4
structure Theorem34SelectedStableCoalitionSuffixCutoffCountGeometrySourceModel
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (epsilon tol sigma vHigh : ℝ)
    (threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ) : Prop where
  cutoff_sorted :
    source_assumption_selected_stable_cutoff_index_sorted
      Mseq Iseq selected cutoffOut
  theorem3_low_count :
    source_assumption_theorem3_suffix_selected_stable_low_cutoff_count
      Mseq Iseq selected cutoffOut (epsilon := epsilon)
      (fun C a =>
        threshold C a - epsilon +
          theorem3LowTailQuantile noiseLaw epsilon C)
  theorem3_upper_ceiling :
    source_assumption_theorem3_suffix_upper_ceiling_atBot
      Mseq Iseq selected cutoffOut (epsilon := epsilon)
      threshold upperCutoff
  theorem4_low_count :
    source_assumption_theorem4_suffix_selected_stable_low_cutoff_count
      Mseq Iseq selected cutoffOut (tol := tol)
      (fun C => vHigh + theorem4HighTailQuantile noiseLaw sigma C)

/--
Selected-stable integrated-capacity version of the shared PG24 coalition
cutoff-geometry certificate.

This is the narrowest current source boundary for the active Theorem 3 and
Theorem 4 routes: the source supplies the paper's market-level outcome
probability, block choice-mass, sorted-index, upper-ceiling, Lemma 11
floor-power integral, and integrated outcome-bridge conventions; Lean derives
selected outcome-law probability, selected block choice-mass, the selected
integrated bridge, the selected Lemma 11 instances, selected sortedness, the
selected upper-ceiling clause, the capacity contradiction, low-count bounds,
and sorted-suffix cutoff floors.
-/
-- audit-premise: PG24 market sorted-cutoff order plus selected-stable integrated low-cutoff affordability contradictions for Theorems 3 and 4
structure Theorem34SelectedStableCoalitionSuffixCutoffIntegratedCapacitySourceModel
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    {Admissible : ℕ → Type u}
    (selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ })
    (noiseLaw : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ)
    (OutcomeSeq : ℕ → Type*) [∀ C, MeasurableSpace (OutcomeSeq C)]
    (outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C))
    (chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1)))
    (totalSupply epsilon tol sigma vHigh : ℝ)
    (threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ) : Prop where
  outcome_probability :
    source_assumption_market_outcome_probability Mseq OutcomeSeq outcomeLaw
  choice_mass_eq_aggregateDemand :
    source_assumption_market_choice_mass_eq_aggregateDemand
      Mseq OutcomeSeq outcomeLaw chosenCollege
  capacity_sum :
    source_assumption_total_capacity_sum Mseq totalSupply
  value_probability :
    source_assumption_market_value_probability valueLaw
  cutoff_sorted :
    source_assumption_market_cutoff_index_sorted Mseq cutoffOut
  integrated_affordance_event_bridge :
    source_assumption_market_integrated_affordance_event_bridge
      Mseq noiseLaw valueLaw cutoffOut OutcomeSeq outcomeLaw chosenCollege
  theorem3_floor_pow_integral_exceeds_supply :
    source_assumption_market_low_cutoff_floor_pow_integral_exceeds_supply
      Mseq noiseLaw valueLaw cutoffOut
      (fun C : ℕ => epsilonFloorSplitIndex (epsilon / 2) C)
      (fun C a =>
        threshold C a - epsilon +
          theorem3LowTailQuantile noiseLaw epsilon C)
      totalSupply
  theorem3_upper_ceiling :
    source_assumption_theorem3_suffix_market_upper_ceiling_atBot
      Mseq cutoffOut (epsilon := epsilon) threshold upperCutoff
  theorem4_floor_pow_integral_exceeds_supply :
    source_assumption_market_low_cutoff_floor_pow_integral_exceeds_supply
      Mseq noiseLaw valueLaw cutoffOut
      (fun C : ℕ => epsilonFloorSplitIndex (tol / 2) C)
      (fun C (_a : Admissible C) =>
        vHigh + theorem4HighTailQuantile noiseLaw sigma C)
      totalSupply

/--
The selected-stable integrated-capacity certificate implies the selected
count-based geometry certificate once exact-fill is supplied by the A-L source
model at the selected stable cutoff.
-/
theorem theorem34_selected_stable_coalition_suffix_cutoff_count_geometry_of_integrated_capacity
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {noiseLaw : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {valueLaw : ∀ C : ℕ, Admissible C → MeasureTheory.Measure ℝ}
    {OutcomeSeq : ℕ → Type*} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {outcomeLaw : ∀ C : ℕ, (Mseq C).Cutoff → MeasureTheory.Measure (OutcomeSeq C)}
    {chosenCollege :
      ∀ C : ℕ, (Mseq C).Cutoff → OutcomeSeq C → Option (Fin (C + 1))}
    {totalSupply epsilon tol sigma vHigh : ℝ}
    {threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (hcapacity_clear :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C, ∀ c : Fin (C + 1),
          (Mseq C).aggregateDemand
              ((Iseq C).marketClearingCutoffOfStable
                (μ := (selected C a).1) (selected C a).2) c =
            (Mseq C).capacity c)
    (H :
      Theorem34SelectedStableCoalitionSuffixCutoffIntegratedCapacitySourceModel
        Mseq Iseq selected noiseLaw cutoffOut valueLaw OutcomeSeq
        outcomeLaw chosenCollege totalSupply epsilon tol sigma vHigh
        threshold upperCutoff) :
      Theorem34SelectedStableCoalitionSuffixCutoffCountGeometrySourceModel
      Mseq Iseq selected noiseLaw cutoffOut epsilon tol sigma vHigh
      threshold upperCutoff where
  cutoff_sorted :=
    source_assumption_selected_stable_cutoff_index_sorted_of_market
      H.cutoff_sorted
  theorem3_low_count :=
    source_assumption_theorem3_suffix_selected_stable_low_cutoff_count_of_capacity_contradiction
      (source_assumption_selected_stable_outcome_finite_of_probability
        (source_assumption_selected_stable_outcome_probability_of_market
          H.outcome_probability))
      (source_assumption_selected_stable_choice_mass_eq_aggregateDemand_of_market
        H.choice_mass_eq_aggregateDemand)
      hcapacity_clear
      H.capacity_sum
      (source_assumption_selected_stable_low_cutoff_capacity_contradiction_of_integrated_affordance_event_bridge
        (source_assumption_selected_stable_low_cutoff_integral_exceeds_supply_of_floor_pow_integral
          (source_assumption_market_value_finite_of_probability
        H.value_probability)
          (source_assumption_selected_stable_low_cutoff_floor_pow_integral_exceeds_supply_of_market
            H.theorem3_floor_pow_integral_exceeds_supply))
        (source_assumption_selected_stable_integrated_affordance_event_bridge_of_market
          H.integrated_affordance_event_bridge))
  theorem3_upper_ceiling :=
    source_assumption_theorem3_suffix_upper_ceiling_atBot_of_market
      H.theorem3_upper_ceiling
  theorem4_low_count :=
    source_assumption_theorem4_suffix_selected_stable_low_cutoff_count_of_capacity_contradiction
      (source_assumption_selected_stable_outcome_finite_of_probability
        (source_assumption_selected_stable_outcome_probability_of_market
          H.outcome_probability))
      (source_assumption_selected_stable_choice_mass_eq_aggregateDemand_of_market
        H.choice_mass_eq_aggregateDemand)
      hcapacity_clear
      H.capacity_sum
      (source_assumption_selected_stable_low_cutoff_capacity_contradiction_of_integrated_affordance_event_bridge
        (source_assumption_selected_stable_low_cutoff_integral_exceeds_supply_of_floor_pow_integral
          (source_assumption_market_value_finite_of_probability
        H.value_probability)
          (source_assumption_selected_stable_low_cutoff_floor_pow_integral_exceeds_supply_of_market
            H.theorem4_floor_pow_integral_exceeds_supply))
        (source_assumption_selected_stable_integrated_affordance_event_bridge_of_market
          H.integrated_affordance_event_bridge))

/--
The selected-stable count-based geometry certificate implies the selected
suffix-floor geometry certificate.
-/
theorem theorem34_selected_stable_coalition_suffix_cutoff_geometry_of_sorted_low_count
    {StudentSeq : ℕ → Type u}
    {Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1))}
    {Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C)}
    {Admissible : ℕ → Type u}
    {selected :
      ∀ C : ℕ, Admissible C →
        { μ : (Mseq C).Matching // (Mseq C).Stable μ }}
    {noiseLaw : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure noiseLaw]
    {cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ}
    {epsilon tol sigma vHigh : ℝ}
    {threshold upperCutoff : ∀ C : ℕ, Admissible C → ℝ}
    (H :
      Theorem34SelectedStableCoalitionSuffixCutoffCountGeometrySourceModel
        Mseq Iseq selected noiseLaw cutoffOut epsilon tol sigma vHigh
        threshold upperCutoff) :
    Theorem34SelectedStableCoalitionSuffixCutoffGeometrySourceModel
      Mseq Iseq selected noiseLaw cutoffOut epsilon tol sigma vHigh
      threshold upperCutoff where
  theorem3_cutoff_floor :=
    source_assumption_theorem3_suffix_cutoff_floor_of_selected_stable_sorted_low_count
      H.cutoff_sorted H.theorem3_low_count
  theorem3_upper_ceiling := H.theorem3_upper_ceiling
  theorem4_cutoff_floor :=
    source_assumption_theorem4_suffix_cutoff_floor_of_selected_stable_sorted_low_count
      H.cutoff_sorted H.theorem4_low_count

/--
Compatibility package for the PG24 Theorem 2 market-level scalar endpoint route
with the high-tail rate derived from an explicit quantile floor.  The audited
theorem-facing route exposes these fields as separate visible premises.
-/
-- audit-premise: PG24 Theorem 2 capacity and market-clearing scalar endpoint source clauses with explicit quantile cutoff floor
structure Theorem2ScalarMarketEndpointQuantileSourceModel
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (noiseLaw : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (totalSupply alpha : ℝ) : Prop where
  capacity_open_bound :
    source_assumption_capacity_open_bound Mseq alpha
  scalar_market_endpoint_estimates :
    source_assumption_theorem2_scalar_market_endpoint_estimates_quantile_floor
      Mseq noiseLaw cutoffOut (totalSupply := totalSupply)

/--
Compatibility PG24 Theorem 2 source package.

This bundles the loose scalar-amplification side conditions with the quantile
endpoint source model for legacy callers.  The audited theorem-facing route
unpacks these fields and states them as visible premises.
-/
-- audit-premise: PG24 Theorem 2 source package for total supply, capacity regularity, and scalar endpoint estimates
structure Theorem2ScalarMarketEndpointQuantileCapacitySourceModel
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    (noiseLaw : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff → Fin (C + 1) → ℝ)
    (totalSupply alpha : ℝ) : Prop where
  totalSupply_lt_one :
    totalSupply < 1
  capacity_sum :
    source_assumption_total_capacity_sum Mseq totalSupply
  endpoint :
    Theorem2ScalarMarketEndpointQuantileSourceModel
      Mseq noiseLaw cutoffOut totalSupply alpha

end PG24NoisyMatchingMarkets
