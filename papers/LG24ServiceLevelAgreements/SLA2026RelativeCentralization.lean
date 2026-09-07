import LG24ServiceLevelAgreements.SLA2026CentralizationComparison
import LG24ServiceLevelAgreements.SLA2026RelativePriceOfEquity
import Mathlib.Tactic

/-!
# Relative centralization gain for the active SLA source

The source now normalizes the city-versus-Borough efficiency gap by the
Borough-efficient all-request baseline.  This file derives that exact
statement from the prior additive value identity and the explicit baseline
positivity theorem used by relative price of equity.
-/

namespace LG24ServiceLevelAgreements

open scoped BigOperators

noncomputable section

/-- The exact relative centralization-gain identity printed in the current
source. -/
theorem sla2026_relativeCentralizationGain_eq
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough]
    {tail capacity : ℝ}
    {arrival admitted priority noninspectionPenalty : Category → Borough → ℝ}
    (htail : 0 < tail)
    (harrival : ∀ k b, 0 < arrival k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hadmitted_le_arrival : ∀ k b, admitted k b ≤ arrival k b)
    (hpriority : ∀ k b, 0 < priority k b)
    (hnoninspectionPenalty : ∀ k b, 0 ≤ noninspectionPenalty k b)
    (hexcess : 0 < sla2026ExcessCapacity capacity admitted) :
    sla2026RelativeCentralizationGain arrival admitted priority
        noninspectionPenalty
        (sla2026EfficientDelay tail capacity admitted priority)
        (sla2026CityEfficientDelay tail
          (sla2026ExcessCapacity capacity admitted) admitted priority) =
      (sla2026EffectiveLoad tail admitted priority ^ 2 -
        sla2026CityEffectiveLoad tail admitted priority ^ 2) /
        (sla2026ExcessCapacity capacity admitted *
          sla2026Efficiency arrival admitted priority noninspectionPenalty
            (sla2026EfficientDelay tail capacity admitted priority)) := by
  let borough := sla2026EfficientDelay tail capacity admitted priority
  let city := sla2026CityEfficientDelay tail
    (sla2026ExcessCapacity capacity admitted) admitted priority
  let baseline := sla2026Efficiency arrival admitted priority noninspectionPenalty borough
  have hbaseline : 0 < baseline := by
    simpa [baseline, borough] using
      (sla2026Efficiency_efficientDelay_pos htail harrival hadmitted
        hadmitted_le_arrival hpriority hnoninspectionPenalty hexcess)
  have hadditive := sla2026_centralization_gain
    (tail := tail) (capacity := capacity) (arrival := arrival)
    (admitted := admitted) (priority := priority)
    (noninspectionPenalty := noninspectionPenalty)
    htail harrival hadmitted hpriority hexcess
  change sla2026RelativeCentralizationGain arrival admitted priority
      noninspectionPenalty borough city = _
  unfold sla2026RelativeCentralizationGain
  calc
    1 - sla2026CityEfficiency arrival admitted priority noninspectionPenalty city /
        baseline =
        (baseline - sla2026CityEfficiency arrival admitted priority
          noninspectionPenalty city) / baseline := by
          field_simp [hbaseline.ne']
    _ = ((sla2026EffectiveLoad tail admitted priority ^ 2 -
          sla2026CityEffectiveLoad tail admitted priority ^ 2) /
          sla2026ExcessCapacity capacity admitted) / baseline := by
          rw [show baseline = sla2026Efficiency arrival admitted priority
            noninspectionPenalty borough by rfl, hadditive]
    _ = (sla2026EffectiveLoad tail admitted priority ^ 2 -
          sla2026CityEffectiveLoad tail admitted priority ^ 2) /
        (sla2026ExcessCapacity capacity admitted * baseline) := by
          field_simp [hexcess.ne', hbaseline.ne']

/-- The source comparison between relative centralization gain and relative
price of equity has the same Pearson form because both use the identical
positive Borough-efficient baseline. -/
theorem sla2026_relativeCentralizationGain_ge_relativePrice_comparison
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough] [Nontrivial Borough]
    {tail capacity : ℝ}
    {arrival admitted priority noninspectionPenalty : Category → Borough → ℝ}
    {equitable : Category → Borough → ℝ}
    (htail : 0 < tail)
    (harrival : ∀ k b, 0 < arrival k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hadmitted_le_arrival : ∀ k b, admitted k b ≤ arrival k b)
    (hpriority : ∀ k b, 0 < priority k b)
    (hnoninspectionPenalty : ∀ k b, 0 ≤ noninspectionPenalty k b)
    (hexcess : 0 < sla2026ExcessCapacity capacity admitted)
    (hbest : sla2026EfficiencyBestEquitable tail capacity arrival admitted
      priority noninspectionPenalty equitable) :
    sla2026RelativeCentralizationGain arrival admitted priority
        noninspectionPenalty
        (sla2026EfficientDelay tail capacity admitted priority)
        (sla2026CityEfficientDelay tail
          (sla2026ExcessCapacity capacity admitted) admitted priority) ≥
      sla2026RelativePriceOfEquity arrival admitted priority noninspectionPenalty
        equitable (sla2026EfficientDelay tail capacity admitted priority) ↔
      1 - sla2026CityEffectiveLoad tail admitted priority ^ 2 /
          sla2026EffectiveLoad tail admitted priority ^ 2 ≥
        sla2026PearsonChiSquare
          (sla2026CapacityShare tail capacity admitted
            (sla2026EfficientDelay tail capacity admitted priority))
          (sla2026CapacityShare tail capacity admitted equitable) := by
  let borough := sla2026EfficientDelay tail capacity admitted priority
  let city := sla2026CityEfficientDelay tail
    (sla2026ExcessCapacity capacity admitted) admitted priority
  let baseline := sla2026Efficiency arrival admitted priority noninspectionPenalty borough
  let additiveGain := sla2026Efficiency arrival admitted priority noninspectionPenalty
    borough - sla2026CityEfficiency arrival admitted priority noninspectionPenalty city
  let additivePrice := sla2026PriceOfEquity arrival admitted priority
    noninspectionPenalty equitable borough
  have hbaseline : 0 < baseline := by
    simpa [baseline, borough] using
      (sla2026Efficiency_efficientDelay_pos htail harrival hadmitted
        hadmitted_le_arrival hpriority hnoninspectionPenalty hexcess)
  have hgain : sla2026RelativeCentralizationGain arrival admitted priority
      noninspectionPenalty borough city = additiveGain / baseline := by
    change 1 - sla2026CityEfficiency arrival admitted priority noninspectionPenalty city /
        baseline =
      (baseline - sla2026CityEfficiency arrival admitted priority
        noninspectionPenalty city) / baseline
    field_simp [hbaseline.ne']
  have hprice : sla2026RelativePriceOfEquity arrival admitted priority
      noninspectionPenalty equitable borough = additivePrice / baseline := by
    exact sla2026RelativePriceOfEquity_eq_additive_div hbaseline.ne'
  have hadditive := sla2026_centralization_gain_ge_price_comparison
    (tail := tail) (capacity := capacity) (arrival := arrival)
    (admitted := admitted) (priority := priority)
    (noninspectionPenalty := noninspectionPenalty)
    htail harrival hadmitted hpriority hexcess hbest
  change sla2026RelativeCentralizationGain arrival admitted priority
      noninspectionPenalty borough city ≥
      sla2026RelativePriceOfEquity arrival admitted priority noninspectionPenalty
        equitable borough ↔ _
  rw [hgain, hprice]
  calc
    additiveGain / baseline ≥ additivePrice / baseline ↔
        additiveGain ≥ additivePrice := div_le_div_iff_of_pos_right hbaseline
    _ ↔ _ := hadditive

end

end LG24ServiceLevelAgreements
