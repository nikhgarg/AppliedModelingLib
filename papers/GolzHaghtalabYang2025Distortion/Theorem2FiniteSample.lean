import AppliedModelingLib.Alignment.Welfare.Borda

/-!
# Deterministic finite-score bridge for source Theorem 2

The quantitative part of Theorem 2 is a concentration problem for the paper's
multi-comparison user reports.  This module isolates the subsequent
deterministic step: a Borda winner for empirical scores that are uniformly
close to population Borda scores inherits the source welfare factor with the
corresponding explicit additive error.
-/

namespace GolzHaghtalabYang2025Distortion

open AppliedModelingLib
open AppliedModelingLib.Alignment.Welfare

/--
Finite-score form of Gölz--Haghtalab--Yang Theorem 2.  If `winner` maximizes
an empirical Borda score and every such score is within `scoreError` of the
literal population Borda score, then its welfare satisfies the source
squared-chord guarantee with the resulting `2 * scoreError` near-maximizer
loss.  The later Lemma-11 concentration proof must supply `happrox` for the
paper's iid multi-comparison user reports.
-/
theorem theorem2_welfare_square_bound_of_uniform_empirical_borda_error
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (hutility : UnitIntervalUtilityProfile utility)
    (sampling : PMF Alternative) {btScale : ℝ} (hbtScale : 0 < btScale)
    (empiricalScore : Alternative → ℝ) (winner : Alternative) (scoreError : ℝ)
    (hmax : ∀ alternative, empiricalScore alternative ≤ empiricalScore winner)
    (happrox : ∀ alternative,
      |empiricalScore alternative -
        pairwiseBordaScore sampling
          (populationBradleyTerryPreference population utility btScale) alternative| ≤ scoreError)
    (alternative : Alternative) :
    (sigmoidChordSlope btScale) ^ 2 * populationAverageUtility population utility alternative ≤
      ((1 : ℝ) / 4) ^ 2 * populationAverageUtility population utility winner +
        ((1 : ℝ) / 4) * (2 * scoreError) / btScale := by
  have hnear : ∀ alternative,
      pairwiseBordaScore sampling
          (populationBradleyTerryPreference population utility btScale) alternative ≤
        pairwiseBordaScore sampling
          (populationBradleyTerryPreference population utility btScale) winner + 2 * scoreError := by
    intro contender
    have hcontender := happrox contender
    have hwinner := happrox winner
    have hmax' := hmax contender
    rw [abs_le] at hcontender hwinner
    linarith
  exact pairwiseBordaScore_welfare_square_bound_of_additive_nearMaximizer
    population utility hutility sampling hbtScale winner (2 * scoreError) hnear alternative

end GolzHaghtalabYang2025Distortion
