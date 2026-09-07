import PG24NoisyMatchingMarkets.Theorem2QuantileWindowCoverage

/-!
# PG24 value-law Holder regularity

The source model assumes a uniform Holder bound on every open value interval:
`model.tex:17` states that its mass is `O(delta^gamma)`, uniformly in the
left endpoint.  This module records that condition with an explicit constant
and proves its endpoint consequence: the value law has no atoms.
-/

open Filter MeasureTheory Topology

namespace PG24NoisyMatchingMarkets

noncomputable section

/--
The uniform interval-mass regularity from `model.tex:17`.

The source's `O(delta^gamma)` is made explicit by one nonnegative global
constant and a positive exponent.  The condition is stated for every real
left endpoint and every positive interval width.
-/
def PG24HolderIntervalRegular (eta : Measure ℝ) : Prop :=
  ∃ holderConstant exponent : ℝ,
    0 < exponent ∧
    0 ≤ holderConstant ∧
    ∀ (x delta : ℝ), 0 < delta →
      eta.real (Set.Ioo x (x + delta)) ≤
        holderConstant * Real.rpow delta exponent

/--
Every singleton has zero real mass under the source Holder interval bound.
The proof sandwiches a point in intervals of width `2 / (n + 1)` and sends
their Holder upper bounds to zero.
-/
theorem PG24HolderIntervalRegular.measureReal_singleton_eq_zero
    {eta : Measure ℝ} [IsFiniteMeasure eta]
    (hregular : PG24HolderIntervalRegular eta) (x : ℝ) :
    eta.real ({x} : Set ℝ) = 0 := by
  rcases hregular with ⟨holderConstant, exponent, hexponent_pos,
    hholderConstant_nonneg, hinterval_mass_le⟩
  have hwidth :
      Tendsto (fun n : ℕ => (2 : ℝ) * (1 / ((n : ℝ) + 1)))
        atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hpower :
      Tendsto
        (fun n : ℕ =>
          Real.rpow ((2 : ℝ) * (1 / ((n : ℝ) + 1))) exponent)
        atTop (nhds 0) := by
    have hcontinuity :
        Tendsto (fun delta : ℝ => Real.rpow delta exponent)
          (nhds 0) (nhds 0) := by
      simpa [Real.zero_rpow hexponent_pos.ne'] using
        (Real.continuous_rpow_const hexponent_pos.le).tendsto (0 : ℝ)
    exact hcontinuity.comp hwidth
  have hbound_tendsto :
      Tendsto
        (fun n : ℕ =>
          holderConstant *
            Real.rpow ((2 : ℝ) * (1 / ((n : ℝ) + 1))) exponent)
        atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hpower
  have hmass_le : ∀ n : ℕ,
      eta.real ({x} : Set ℝ) ≤
        holderConstant *
          Real.rpow ((2 : ℝ) * (1 / ((n : ℝ) + 1))) exponent := by
    intro n
    let delta : ℝ := 1 / ((n : ℝ) + 1)
    have hdelta_pos : 0 < delta := by
      dsimp [delta]
      positivity
    calc
      eta.real ({x} : Set ℝ) ≤
          eta.real (Set.Ioo (x - delta) ((x - delta) + 2 * delta)) :=
        MeasureTheory.measureReal_mono
          (by
            intro y hy
            rcases Set.mem_singleton_iff.mp hy with rfl
            constructor <;> linarith)
          (by finiteness)
      _ ≤ holderConstant * Real.rpow (2 * delta) exponent :=
        hinterval_mass_le (x - delta) (2 * delta) (by positivity)
      _ = holderConstant *
            Real.rpow ((2 : ℝ) * (1 / ((n : ℝ) + 1))) exponent := by
        rfl
  have hle_zero : eta.real ({x} : Set ℝ) ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hbound_tendsto
      (Filter.Eventually.of_forall hmass_le)
  exact le_antisymm hle_zero (MeasureTheory.measureReal_nonneg)

/--
The source Holder interval regularity rules out point atoms in the value law.
-/
theorem PG24HolderIntervalRegular.noAtoms
    {eta : Measure ℝ} [IsFiniteMeasure eta]
    (hregular : PG24HolderIntervalRegular eta) :
    NoAtoms eta := by
  refine { measure_singleton := fun x => ?_ }
  exact (MeasureTheory.measureReal_eq_zero_iff (by finiteness)).mp
    (hregular.measureReal_singleton_eq_zero x)

/--
The quantile-window coverage bridge with nonatomicity discharged by the
source Holder interval regularity, rather than supplied as an extra premise.
-/
theorem theorem2_localWindowMembership_eventually_of_quantileWindows_holder
    (eta : Measure ℝ) [IsFiniteMeasure eta]
    (hregular : PG24HolderIntervalRegular eta)
    {epsilon vLow vHigh vStar : ℕ → ℝ} {v : ℝ}
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hlow : ∀ᶠ n : ℕ in atTop,
      eta.real (Set.Iio (vLow n)) ≤ epsilon n / 2)
    (hwindow : ∀ᶠ n : ℕ in atTop,
      eta.real (Set.Ioo (vStar n) (vHigh n)) ≤ Real.sqrt (epsilon n))
    (hhigh : ∀ᶠ n : ℕ in atTop,
      eta.real (Set.Ioi (vHigh n)) ≤ epsilon n / 2)
    (horder : ∀ᶠ n : ℕ in atTop, vStar n ≤ vHigh n)
    (hvLower : 0 < eta.real (Set.Iio v))
    (hvUpper : 0 < eta.real (Set.Ioi v)) :
    ∀ᶠ n : ℕ in atTop,
      theorem2_localWindowMembership (vLow n) (vHigh n) (vStar n) v := by
  letI : NoAtoms eta := hregular.noAtoms
  exact theorem2_localWindowMembership_eventually_of_quantileWindows_noAtoms
    eta hepsilon hlow hwindow hhigh horder hvLower hvUpper

end

end PG24NoisyMatchingMarkets
