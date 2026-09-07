import KR21Monoculture.FiniteExponentialRace

/-!
# Exact finite Gumbel--Plackett--Luce bridge

This module instantiates the genuine finite exponential-race calculation with
the Plackett--Luce weights.  It closes the previously conditional Gumbel
certificate without identifying either distribution by definition.
-/

open AppliedModelingLib MeasureTheory ProbabilityTheory

namespace KR21Monoculture

noncomputable section

/-- The finite exponential-race order formula required by the Gumbel bridge
is now discharged for every ranking. -/
theorem hasFiniteExponentialRaceOrderFormula
    {n : ℕ} (theta : ℝ) (value : Candidate n → ℝ) :
    HasFiniteExponentialRaceOrderFormula theta value := by
  intro ranking
  exact strictExponentialRaceOrderCell_measure_eq_plackettLuceRankingPMF
    theta value ranking

/-- The actual finite scale-one Gumbel random-utility ranking law equals the
independently defined Plackett--Luce PMF. -/
theorem scaleOneGumbelRUMRankingPMF_eq_plackettLuce
    {n : ℕ} (theta : ℝ) (value : Candidate n → ℝ) :
    scaleOneGumbelRUMRankingPMF theta value =
      plackettLuceRankingPMF theta value := by
  exact scaleOneGumbelRUMRankingPMF_eq_plackettLuce_of_certificate theta value
    (gumbelRaceCertificate_of_exponentialOrderFormula theta value
      (hasFiniteExponentialRaceOrderFormula theta value))

/-- Exact endpoint for the repository's explicitly scaled Gumbel convention:
the matching Plackett--Luce inverse temperature is
`theta / unitVarianceGumbelScale`, not `theta` itself.  Its identification
with the paper's unit-variance Gumbel parameterization is a separate
source-model obligation. -/
theorem unitVarianceGumbelRUMRankingPMF_eq_plackettLuce
    {n : ℕ} {theta : ℝ} (htheta : 0 < theta) (value : Candidate n → ℝ) :
    unitVarianceGumbelRUMRankingPMF theta value =
      plackettLuceRankingPMF (theta / unitVarianceGumbelScale) value := by
  exact unitVarianceGumbelRUMRankingPMF_eq_plackettLuce_of_certificate
    htheta value
    (gumbelRaceCertificate_of_exponentialOrderFormula
      (theta / unitVarianceGumbelScale) value
      (hasFiniteExponentialRaceOrderFormula
        (theta / unitVarianceGumbelScale) value))

end

end KR21Monoculture
