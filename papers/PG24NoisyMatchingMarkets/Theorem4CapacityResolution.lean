import PG24NoisyMatchingMarkets.Assumptions
import PG24NoisyMatchingMarkets.Theorem4ParameterSelection

/-!
# Theorem 4 Capacity Resolution

This module discharges the analytic split-power capacity condition for the
explicit Theorem 4 high-tail quantile.  The construction uses only the
source-level strict supply bound and long-tailedness; in particular, it does
not assume that the noise law is nonatomic.
-/

open Filter Topology
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

universe u

/--
For the explicit high-tail quantile, strict aggregate supply below one and
long-tailed noise provide all analytic witnesses needed by the Theorem 4
low-cutoff capacity crossing.  The fixed one-half slack is a proof choice,
not a source-model assumption.
-/
theorem exists_theorem4_highTailQuantile_capacity_witness_of_longTailed
    {StudentSeq : ℕ → Type u}
    (Mseq : ∀ C : ℕ, CutoffMarket (StudentSeq C) (Fin (C + 1)))
    {Admissible : ℕ → Type u}
    (noiseLaw : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {tol totalSupply vHigh : ℝ}
    (htol_pos : 0 < tol) (htotalSupply_lt_one : totalSupply < 1) :
    ∃ sigma tau epsilon : ℝ,
      0 < sigma ∧ 0 < tau ∧ 0 < epsilon ∧ epsilon ≤ 1 ∧
        tau = (1 - (1 / 2 : ℝ)) * sigma ∧
          totalSupply < 1 - Real.exp (-((tol / 2) * tau)) ∧
            1 - Real.exp (-(2 * epsilon * sigma)) < tol ∧
              source_assumption_market_low_cutoff_upper_tail_split_pow_exceeds_supply
                (Admissible := Admissible) Mseq noiseLaw
                (fun C : ℕ => epsilonFloorSplitIndex (tol / 2) C)
                (fun C _a =>
                  vHigh + theorem4HighTailQuantile noiseLaw sigma C)
                (fun _C _a => vHigh)
                totalSupply := by
  have hdelta_pos : 0 < tol / 2 := by
    positivity
  rcases exists_theorem4_capacity_and_error_parameters_of_totalSupply_lt_one
    (delta := tol / 2) (slack := (1 / 2 : ℝ)) hdelta_pos
    htotalSupply_lt_one (by norm_num) htol_pos with
    ⟨sigma, tau, epsilon, hsigma_pos, htau_pos, htau_eq, hstatic_gap,
      hepsilon_pos, hepsilon_le_one, herror⟩
  have hquantile_tail :
      ∀ᶠ C : ℕ in atTop,
        (1 - (1 / 2 : ℝ)) * (sigma / (((C + 1 : ℕ) : ℝ))) ≤
          AppliedModelingLib.Probability.upperTailMass noiseLaw
            (theorem4HighTailQuantile noiseLaw sigma C) :=
    theorem4HighTailQuantile_upperTailMass_lower_bound_eventually_of_longTailed
      noiseLaw hlong hsigma_pos (by norm_num) (by norm_num)
  have htail :
      ∀ᶠ C : ℕ in atTop,
        ∀ a : Admissible C,
          tau / (((C + 1 : ℕ) : ℝ)) ≤
            AppliedModelingLib.Probability.upperTailMass noiseLaw
              ((vHigh + theorem4HighTailQuantile noiseLaw sigma C) - vHigh) := by
    filter_upwards [hquantile_tail] with C hquantile_tail_C a
    calc
      tau / (((C + 1 : ℕ) : ℝ)) =
          (1 - (1 / 2 : ℝ)) * (sigma / (((C + 1 : ℕ) : ℝ)) ) := by
        rw [htau_eq]
        ring
      _ ≤ AppliedModelingLib.Probability.upperTailMass noiseLaw
          (theorem4HighTailQuantile noiseLaw sigma C) := hquantile_tail_C
      _ = AppliedModelingLib.Probability.upperTailMass noiseLaw
          ((vHigh + theorem4HighTailQuantile noiseLaw sigma C) - vHigh) := by
        congr 1; ring
  have hcross :=
    pg24_eventually_upperTail_split_crossing_of_scalar_lower_static_gap
      (Admissible := Admissible) noiseLaw (delta := tol / 2) (tau := tau)
      (totalSupply := totalSupply)
      (lowerCutoff := fun C _a =>
        vHigh + theorem4HighTailQuantile noiseLaw sigma C)
      (eventValue := fun _C _a => vHigh)
      hdelta_pos htau_pos hstatic_gap htail
  exact ⟨sigma, tau, epsilon, hsigma_pos, htau_pos, hepsilon_pos,
    hepsilon_le_one, htau_eq, hstatic_gap, herror, by simpa using hcross⟩

end PG24NoisyMatchingMarkets
