import KR21Monoculture.GumbelRUMPlackettLuce

/-!
# Reindexing strict exponential-race cells

An arbitrary ranking is a relabeling of the natural finite position order.
This module records that relabeling at both the set and product-measure level,
so the finite exponential-race calculation can work on ordered coordinates
without treating a ranking as notation for a different probability law.
-/

open AppliedModelingLib MeasureTheory ProbabilityTheory

namespace KR21Monoculture

noncomputable section

/-- Strictly increasing arrival times in natural candidate-position order. -/
def strictIncreasingRaceCoordinateCell (n : ℕ) : Set (Candidate n → ℝ) :=
  {time | ∀ p q : Candidate n, p < q → time p < time q}

/-- Reindex a natural-position arrival vector into the candidate labels listed
by a ranking. -/
def raceOrderCoordinateReindex {n : ℕ} (ranking : Ranking n) :
    (Candidate n → ℝ) ≃ᵐ (Candidate n → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Candidate n => ℝ) ranking

@[simp]
theorem raceOrderCoordinateReindex_apply_ranking {n : ℕ}
    (ranking : Ranking n) (time : Candidate n → ℝ) (position : Candidate n) :
    raceOrderCoordinateReindex ranking time (ranking position) = time position := by
  exact MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : Candidate n => ℝ) ranking time position

/-- Pulling an arbitrary ranking's strict order cell back along coordinate
relabeling gives the ordinary increasing cell. -/
theorem preimage_strictExponentialRaceOrderCell_eq_strictIncreasing {n : ℕ}
    (ranking : Ranking n) :
    (raceOrderCoordinateReindex ranking) ⁻¹'
        strictExponentialRaceOrderCell ranking =
      strictIncreasingRaceCoordinateCell n := by
  ext time
  simp only [Set.mem_preimage, strictExponentialRaceOrderCell,
    strictIncreasingRaceCoordinateCell, Set.mem_setOf_eq]
  constructor
  · intro h p q hpq
    simpa using h p q hpq
  · intro h p q hpq
    simpa using h p q hpq

/-- Coordinate relabeling transports the position-indexed product law with
rates `rate (ranking p)` to the candidate-indexed product law with rates
`rate i`. -/
theorem raceOrderCoordinateReindex_measurePreserving {n : ℕ}
    (rate : Candidate n → ℝ) (hrate : ∀ candidate, 0 < rate candidate)
    (ranking : Ranking n) :
    MeasurePreserving (raceOrderCoordinateReindex ranking)
      (Measure.pi fun position : Candidate n => expMeasure (rate (ranking position)))
      (Measure.pi fun candidate : Candidate n => expMeasure (rate candidate)) := by
  letI : ∀ candidate : Candidate n, IsProbabilityMeasure (expMeasure (rate candidate)) :=
    fun candidate => isProbabilityMeasure_expMeasure (hrate candidate)
  exact MeasureTheory.measurePreserving_piCongrLeft
    (fun candidate : Candidate n => expMeasure (rate candidate)) ranking

/-- The strict-order probability of an arbitrary candidate ranking equals the
strictly increasing probability after reindexing the rates by that ranking. -/
theorem strictExponentialRaceOrderCell_measure_eq_reindexedIncreasing {n : ℕ}
    (rate : Candidate n → ℝ) (hrate : ∀ candidate, 0 < rate candidate)
    (ranking : Ranking n) :
    (Measure.pi fun candidate : Candidate n => expMeasure (rate candidate))
        (strictExponentialRaceOrderCell ranking) =
      (Measure.pi fun position : Candidate n => expMeasure (rate (ranking position)))
        (strictIncreasingRaceCoordinateCell n) := by
  let e := raceOrderCoordinateReindex ranking
  let source : Measure (Candidate n → ℝ) :=
    Measure.pi fun position : Candidate n => expMeasure (rate (ranking position))
  let target : Measure (Candidate n → ℝ) :=
    Measure.pi fun candidate : Candidate n => expMeasure (rate candidate)
  have hpres : MeasurePreserving e source target :=
    raceOrderCoordinateReindex_measurePreserving rate hrate ranking
  calc
    target (strictExponentialRaceOrderCell ranking) =
        Measure.map e source (strictExponentialRaceOrderCell ranking) := by
          rw [hpres.map_eq]
    _ = source (e ⁻¹' strictExponentialRaceOrderCell ranking) := by
          rw [Measure.map_apply e.measurable
            (measurableSet_strictExponentialRaceOrderCell ranking)]
    _ = source (strictIncreasingRaceCoordinateCell n) := by
          rw [preimage_strictExponentialRaceOrderCell_eq_strictIncreasing ranking]

end

end KR21Monoculture
