import LG24ServiceLevelAgreements.SLA2026Centralization
import LG24ServiceLevelAgreements.SLA2026PriceOfEquity
import Mathlib.Tactic

namespace LG24ServiceLevelAgreements

open scoped BigOperators

noncomputable section

/--
The comparison clause of the active source's centralization proposition.
The centralization-gain and price-of-equity identities are both derived from
the source primitives inside this proof; the only endpoint input is the
source-facing efficiency-best equitable definition.
-/
theorem sla2026_centralization_gain_ge_price_comparison
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough]
    [Nonempty Category] [Nonempty Borough] [Nontrivial Borough]
    {tail capacity : ℝ}
    {arrival admitted priority noninspectionPenalty : Category → Borough → ℝ}
    {equitable : Category → Borough → ℝ}
    (htail : 0 < tail)
    (harrival : ∀ k b, 0 < arrival k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hpriority : ∀ k b, 0 < priority k b)
    (hexcess : 0 < sla2026ExcessCapacity capacity admitted)
    (hbest : sla2026EfficiencyBestEquitable tail capacity arrival admitted
      priority noninspectionPenalty equitable) :
    sla2026Efficiency arrival admitted priority noninspectionPenalty
        (sla2026EfficientDelay tail capacity admitted priority) -
      sla2026CityEfficiency arrival admitted priority noninspectionPenalty
        (sla2026CityEfficientDelay tail
          (sla2026ExcessCapacity capacity admitted) admitted priority) ≥
        sla2026PriceOfEquity arrival admitted priority noninspectionPenalty
          equitable (sla2026EfficientDelay tail capacity admitted priority) ↔
      1 - sla2026CityEffectiveLoad tail admitted priority ^ 2 /
          sla2026EffectiveLoad tail admitted priority ^ 2 ≥
        sla2026PearsonChiSquare
          (sla2026CapacityShare tail capacity admitted
            (sla2026EfficientDelay tail capacity admitted priority))
          (sla2026CapacityShare tail capacity admitted equitable) := by
  have heffective : 0 < sla2026EffectiveLoad tail admitted priority :=
    sla2026EffectiveLoad_pos htail hadmitted hpriority
  have heffectiveSq : 0 < sla2026EffectiveLoad tail admitted priority ^ 2 :=
    sq_pos_of_pos heffective
  have hgain := sla2026_centralization_gain
    (tail := tail) (capacity := capacity) (arrival := arrival)
    (admitted := admitted) (priority := priority)
    (noninspectionPenalty := noninspectionPenalty)
    htail harrival hadmitted hpriority hexcess
  have hprice := sla2026_price_of_equity_chi_square
    (tail := tail) (capacity := capacity) (arrival := arrival)
    (admitted := admitted) (priority := priority)
    (noninspectionPenalty := noninspectionPenalty)
    htail harrival hadmitted hpriority hexcess hbest
  rw [hgain, hprice,
    sla2026_centralization_gain_ge_price_iff heffective hexcess]
  have hcancel :
      (sla2026EffectiveLoad tail admitted priority ^ 2 /
        sla2026ExcessCapacity capacity admitted *
        sla2026PearsonChiSquare
          (sla2026CapacityShare tail capacity admitted
            (sla2026EfficientDelay tail capacity admitted priority))
          (sla2026CapacityShare tail capacity admitted equitable)) *
          sla2026ExcessCapacity capacity admitted /
        sla2026EffectiveLoad tail admitted priority ^ 2 =
      sla2026PearsonChiSquare
        (sla2026CapacityShare tail capacity admitted
          (sla2026EfficientDelay tail capacity admitted priority))
        (sla2026CapacityShare tail capacity admitted equitable) := by
    field_simp [hexcess.ne', heffectiveSq.ne'] <;> ring
  rw [hcancel]

end

end LG24ServiceLevelAgreements
