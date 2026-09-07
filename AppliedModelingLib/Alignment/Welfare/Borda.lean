import AppliedModelingLib.Alignment.Welfare.Linearization

/-!
# Finite Borda scores from pairwise preference probabilities

The distortion paper's population Borda score averages an alternative's
pairwise win probability against an independently sampled alternative.  This
module keeps the alternative-sampling distribution explicit and works for any
valid finite pairwise preference model.

## Main declarations

- `pairwiseBordaScore`
- `pmfPairExp_swap`
- `pmfExp_pairwiseBordaScore`
- `pairwiseBordaScore_linearization_source`
-/

namespace AppliedModelingLib
namespace Alignment
namespace Welfare

open Learning.HumanFeedback

/--
The expected pairwise win probability of `alternative` against an independently
sampled opponent.  The explicit `sampling` argument is the source model's
alternative distribution, not the user population.
-/
noncomputable def pairwiseBordaScore {Alternative : Type*}
    [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative)
    (alternative : Alternative) : ℝ :=
  pmfExp sampling (fun opponent => preference.prob PUnit.unit alternative opponent)

/-- Independent finite pair expectations are invariant under swapping draws. -/
theorem pmfPairExp_swap {Alternative : Type*}
    [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (f : Alternative → Alternative → ℝ) :
    pmfPairExp sampling sampling (fun first second => f second first) =
      pmfPairExp sampling sampling f := by
  unfold pmfPairExp pmfExp
  calc
    (∑ first : Alternative, (sampling first).toReal *
        ∑ second : Alternative, (sampling second).toReal * f second first) =
        ∑ first : Alternative, ∑ second : Alternative,
          (sampling first).toReal * ((sampling second).toReal * f second first) := by
            apply Finset.sum_congr rfl
            intro first _
            rw [Finset.mul_sum]
    _ = ∑ second : Alternative, ∑ first : Alternative,
          (sampling first).toReal * ((sampling second).toReal * f second first) := by
            rw [Finset.sum_comm]
    _ = ∑ second : Alternative, ∑ first : Alternative,
          (sampling second).toReal * ((sampling first).toReal * f second first) := by
            apply Finset.sum_congr rfl
            intro second _
            apply Finset.sum_congr rfl
            intro first _
            ring
    _ = ∑ second : Alternative, (sampling second).toReal *
        ∑ first : Alternative, (sampling first).toReal * f second first := by
            apply Finset.sum_congr rfl
            intro second _
            symm
            rw [Finset.mul_sum]

/-- The sampling-average Borda score of a valid pairwise model is one half. -/
theorem pmfExp_pairwiseBordaScore {Alternative : Type*}
    [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (preference : PairwisePreference PUnit Alternative) :
    pmfExp sampling (pairwiseBordaScore sampling preference) = (1 : ℝ) / 2 := by
  let winRate : Alternative → Alternative → ℝ :=
    fun first second => preference.prob PUnit.unit first second
  have hcomplement :
      pmfPairExp sampling sampling winRate +
        pmfPairExp sampling sampling (fun first second => winRate second first) = 1 := by
    unfold pmfPairExp
    calc
      pmfExp sampling (fun first => pmfExp sampling (fun second => winRate first second)) +
          pmfExp sampling (fun first => pmfExp sampling (fun second => winRate second first)) =
        pmfExp sampling (fun first =>
          pmfExp sampling (fun second => winRate first second) +
            pmfExp sampling (fun second => winRate second first)) := by
              rw [← pmfExp_add]
      _ = pmfExp sampling (fun first =>
          pmfExp sampling (fun second => winRate first second + winRate second first)) := by
            apply pmfExp_congr
            intro first
            rw [pmfExp_add]
      _ = pmfExp sampling (fun _ => (1 : ℝ)) := by
            apply pmfExp_congr
            intro first
            calc
              pmfExp sampling (fun second => winRate first second + winRate second first) =
                  pmfExp sampling (fun _ => (1 : ℝ)) := by
                    apply pmfExp_congr
                    intro second
                    exact preference.complementary PUnit.unit first second
              _ = 1 := pmfExp_const sampling 1
      _ = 1 := pmfExp_const sampling 1
  have hswap :
      pmfPairExp sampling sampling (fun first second => winRate second first) =
        pmfPairExp sampling sampling winRate :=
    pmfPairExp_swap sampling winRate
  change pmfPairExp sampling sampling winRate = (1 : ℝ) / 2
  linarith

/--
Source Lemma 1 averaged over the explicit Borda opponent distribution. The
user population and alternative-sampling PMFs remain distinct arguments.
-/
theorem pairwiseBordaScore_linearization_source
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (hutility : UnitIntervalUtilityProfile utility)
    (sampling : PMF Alternative) {btScale : ℝ} (hbtScale : 0 < btScale)
    (alternative : Alternative) :
    btScale *
          (sigmoidChordSlope btScale * populationAverageUtility population utility alternative -
            (1 : ℝ) / 4 * policyAverageUtility population utility sampling) ≤
        pairwiseBordaScore sampling
          (populationBradleyTerryPreference population utility btScale) alternative - (1 : ℝ) / 2 ∧
      pairwiseBordaScore sampling
          (populationBradleyTerryPreference population utility btScale) alternative - (1 : ℝ) / 2 ≤
        btScale *
          ((1 : ℝ) / 4 * populationAverageUtility population utility alternative -
            sigmoidChordSlope btScale * policyAverageUtility population utility sampling) := by
  change
    btScale *
          (sigmoidChordSlope btScale * populationAverageUtility population utility alternative -
            (1 : ℝ) / 4 * policyAverageUtility population utility sampling) ≤
        pmfExp sampling (fun opponent => pmfExp population (fun user =>
          Real.sigmoid (btScale * (utility user alternative - utility user opponent)))) - (1 : ℝ) / 2 ∧
      pmfExp sampling (fun opponent => pmfExp population (fun user =>
          Real.sigmoid (btScale * (utility user alternative - utility user opponent)))) - (1 : ℝ) / 2 ≤
        btScale *
          ((1 : ℝ) / 4 * populationAverageUtility population utility alternative -
            sigmoidChordSlope btScale * policyAverageUtility population utility sampling)
  have hlower := pmfExp_le_pmfExp_of_forall_le sampling
    (fun opponent =>
      btScale *
        (sigmoidChordSlope btScale * populationAverageUtility population utility alternative -
          (1 : ℝ) / 4 * populationAverageUtility population utility opponent))
    (fun opponent => pmfExp population (fun user =>
      Real.sigmoid (btScale * (utility user alternative - utility user opponent))) - (1 : ℝ) / 2)
    (fun opponent =>
      (populationBradleyTerryPreference_linearization_source population utility hutility hbtScale
        alternative opponent).1)
  have hupper := pmfExp_le_pmfExp_of_forall_le sampling
    (fun opponent => pmfExp population (fun user =>
      Real.sigmoid (btScale * (utility user alternative - utility user opponent))) - (1 : ℝ) / 2)
    (fun opponent =>
      btScale *
        ((1 : ℝ) / 4 * populationAverageUtility population utility alternative -
          sigmoidChordSlope btScale * populationAverageUtility population utility opponent))
    (fun opponent =>
      (populationBradleyTerryPreference_linearization_source population utility hutility hbtScale
        alternative opponent).2)
  constructor
  · calc
      btScale *
            (sigmoidChordSlope btScale * populationAverageUtility population utility alternative -
              (1 : ℝ) / 4 * policyAverageUtility population utility sampling) =
          pmfExp sampling (fun opponent =>
            btScale *
              (sigmoidChordSlope btScale * populationAverageUtility population utility alternative -
                (1 : ℝ) / 4 * populationAverageUtility population utility opponent)) := by
              simp [policyAverageUtility, pmfExp_const_mul, pmfExp_sub]
      _ ≤ pmfExp sampling (fun opponent => pmfExp population (fun user =>
          Real.sigmoid (btScale * (utility user alternative - utility user opponent))) - (1 : ℝ) / 2) :=
        hlower
      _ = pmfExp sampling (fun opponent => pmfExp population (fun user =>
          Real.sigmoid (btScale * (utility user alternative - utility user opponent)))) - (1 : ℝ) / 2 := by
            rw [pmfExp_sub, pmfExp_const]
  · calc
      pmfExp sampling (fun opponent => pmfExp population (fun user =>
          Real.sigmoid (btScale * (utility user alternative - utility user opponent)))) - (1 : ℝ) / 2 =
          pmfExp sampling (fun opponent => pmfExp population (fun user =>
            Real.sigmoid (btScale * (utility user alternative - utility user opponent))) - (1 : ℝ) / 2) := by
              rw [pmfExp_sub, pmfExp_const]
      _ ≤ pmfExp sampling (fun opponent =>
          btScale *
            ((1 : ℝ) / 4 * populationAverageUtility population utility alternative -
              sigmoidChordSlope btScale * populationAverageUtility population utility opponent)) :=
        hupper
      _ = btScale *
            ((1 : ℝ) / 4 * populationAverageUtility population utility alternative -
              sigmoidChordSlope btScale * policyAverageUtility population utility sampling) := by
              simp [policyAverageUtility, pmfExp_const_mul, pmfExp_sub]

/--
The population-limit core of the source Borda argument: any maximizer of the
explicit Borda score has squared-chord welfare at least that of every
alternative. This is the division-free form of the source factor
`(ℓ_β / L)^2`, where `L = 1 / 4`.
-/
theorem pairwiseBordaScore_welfare_square_bound_of_maximizer
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (hutility : UnitIntervalUtilityProfile utility)
    (sampling : PMF Alternative) {btScale : ℝ} (hbtScale : 0 < btScale)
    (winner : Alternative)
    (hmax : ∀ alternative,
      pairwiseBordaScore sampling
          (populationBradleyTerryPreference population utility btScale) alternative ≤
        pairwiseBordaScore sampling
          (populationBradleyTerryPreference population utility btScale) winner)
    (alternative : Alternative) :
    (sigmoidChordSlope btScale) ^ 2 * populationAverageUtility population utility alternative ≤
      ((1 : ℝ) / 4) ^ 2 * populationAverageUtility population utility winner := by
  let preference := populationBradleyTerryPreference population utility btScale
  let averageUtility := policyAverageUtility population utility sampling
  let chordSlope := sigmoidChordSlope btScale
  let tangentSlope : ℝ := (1 : ℝ) / 4
  have hlinear := pairwiseBordaScore_linearization_source population utility hutility sampling
    hbtScale
  have hmean : (1 : ℝ) / 2 ≤ pairwiseBordaScore sampling preference winner := by
    calc
      (1 : ℝ) / 2 = pmfExp sampling (pairwiseBordaScore sampling preference) :=
        (pmfExp_pairwiseBordaScore sampling preference).symm
      _ ≤ pmfExp sampling (fun _ => pairwiseBordaScore sampling preference winner) :=
        pmfExp_le_pmfExp_of_forall_le sampling _ _ hmax
      _ = pairwiseBordaScore sampling preference winner := pmfExp_const sampling _
  have hwinner := hlinear winner
  have hwinner_nonneg :
      0 ≤ btScale *
        (tangentSlope * populationAverageUtility population utility winner -
          chordSlope * averageUtility) := by
    change 0 ≤ btScale *
      ((1 : ℝ) / 4 * populationAverageUtility population utility winner -
        sigmoidChordSlope btScale * policyAverageUtility population utility sampling)
    linarith [hmean, hwinner.2]
  have haverage_bound :
      chordSlope * averageUtility ≤ tangentSlope * populationAverageUtility population utility winner := by
    apply sub_nonneg.mp
    apply nonneg_of_mul_nonneg_right hwinner_nonneg hbtScale
  have hcomparison := hlinear alternative
  have hscore_comparison :
      pairwiseBordaScore sampling preference alternative ≤ pairwiseBordaScore sampling preference winner :=
    hmax alternative
  have hfirst_bound :
      chordSlope * populationAverageUtility population utility alternative ≤
        tangentSlope * populationAverageUtility population utility winner +
          (tangentSlope - chordSlope) * averageUtility := by
    have hscaled :
        btScale *
          (chordSlope * populationAverageUtility population utility alternative -
            tangentSlope * averageUtility) ≤
          btScale *
            (tangentSlope * populationAverageUtility population utility winner -
              chordSlope * averageUtility) := by
      change
        btScale *
          (sigmoidChordSlope btScale * populationAverageUtility population utility alternative -
            (1 : ℝ) / 4 * policyAverageUtility population utility sampling) ≤
          btScale *
            ((1 : ℝ) / 4 * populationAverageUtility population utility winner -
              sigmoidChordSlope btScale * policyAverageUtility population utility sampling)
      linarith [hcomparison.1, hscore_comparison, hwinner.2]
    have hunscaled :
        chordSlope * populationAverageUtility population utility alternative -
            tangentSlope * averageUtility ≤
          tangentSlope * populationAverageUtility population utility winner -
              chordSlope * averageUtility :=
      le_of_mul_le_mul_left hscaled hbtScale
    linarith
  have hchord_pos : 0 < chordSlope := by
    exact sigmoidChordSlope_pos hbtScale
  have hslope_gap : 0 ≤ tangentSlope - chordSlope := by
    change 0 ≤ (1 : ℝ) / 4 - sigmoidChordSlope btScale
    exact sub_nonneg.mpr (sigmoidChordSlope_le_one_quarter hbtScale)
  have hfirst_scaled := mul_le_mul_of_nonneg_left hfirst_bound hchord_pos.le
  have haverage_scaled := mul_le_mul_of_nonneg_left haverage_bound hslope_gap
  change chordSlope ^ 2 * populationAverageUtility population utility alternative ≤
    tangentSlope ^ 2 * populationAverageUtility population utility winner
  calc
    chordSlope ^ 2 * populationAverageUtility population utility alternative =
        chordSlope *
          (chordSlope * populationAverageUtility population utility alternative) := by ring
    _ ≤ chordSlope *
          (tangentSlope * populationAverageUtility population utility winner +
            (tangentSlope - chordSlope) * averageUtility) := hfirst_scaled
    _ = chordSlope * tangentSlope * populationAverageUtility population utility winner +
          chordSlope * (tangentSlope - chordSlope) * averageUtility := by ring
    _ ≤ chordSlope * tangentSlope * populationAverageUtility population utility winner +
          (tangentSlope - chordSlope) *
            (tangentSlope * populationAverageUtility population utility winner) := by
      refine add_le_add (le_refl _) ?_
      calc
        chordSlope * (tangentSlope - chordSlope) * averageUtility =
            (tangentSlope - chordSlope) * (chordSlope * averageUtility) := by ring
        _ ≤ (tangentSlope - chordSlope) *
            (tangentSlope * populationAverageUtility population utility winner) :=
          haverage_scaled
    _ = tangentSlope ^ 2 * populationAverageUtility population utility winner := by ring

/--
Finite-score stability form of the source Borda argument.  If `winner` is an
additive `scoreError` near-maximizer of the population Borda score, its welfare
retains the squared-chord guarantee up to the explicit linear error term.  This
is the deterministic bridge from a uniform empirical-Borda estimate to the
finite-sample part of Gölz--Haghtalab--Yang Theorem 2.
-/
theorem pairwiseBordaScore_welfare_square_bound_of_additive_nearMaximizer
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (hutility : UnitIntervalUtilityProfile utility)
    (sampling : PMF Alternative) {btScale : ℝ} (hbtScale : 0 < btScale)
    (winner : Alternative) (scoreError : ℝ)
    (hnear : ∀ alternative,
      pairwiseBordaScore sampling
          (populationBradleyTerryPreference population utility btScale) alternative ≤
        pairwiseBordaScore sampling
          (populationBradleyTerryPreference population utility btScale) winner + scoreError)
    (alternative : Alternative) :
    (sigmoidChordSlope btScale) ^ 2 * populationAverageUtility population utility alternative ≤
      ((1 : ℝ) / 4) ^ 2 * populationAverageUtility population utility winner +
        ((1 : ℝ) / 4) * scoreError / btScale := by
  let preference := populationBradleyTerryPreference population utility btScale
  let averageUtility := policyAverageUtility population utility sampling
  let chordSlope := sigmoidChordSlope btScale
  let tangentSlope : ℝ := (1 : ℝ) / 4
  have hlinear := pairwiseBordaScore_linearization_source population utility hutility sampling
    hbtScale
  have hmean : (1 : ℝ) / 2 ≤
      pairwiseBordaScore sampling preference winner + scoreError := by
    calc
      (1 : ℝ) / 2 = pmfExp sampling (pairwiseBordaScore sampling preference) :=
        (pmfExp_pairwiseBordaScore sampling preference).symm
      _ ≤ pmfExp sampling (fun _ =>
          pairwiseBordaScore sampling preference winner + scoreError) :=
        pmfExp_le_pmfExp_of_forall_le sampling _ _ hnear
      _ = pairwiseBordaScore sampling preference winner + scoreError :=
        pmfExp_const sampling _
  have hwinner := hlinear winner
  have haverage_bound :
      chordSlope * averageUtility ≤
        tangentSlope * populationAverageUtility population utility winner + scoreError / btScale := by
    have hscaled :
        btScale *
          (chordSlope * averageUtility -
            tangentSlope * populationAverageUtility population utility winner) ≤ scoreError := by
      change btScale *
        (sigmoidChordSlope btScale * policyAverageUtility population utility sampling -
          (1 : ℝ) / 4 * populationAverageUtility population utility winner) ≤ scoreError
      linarith [hmean, hwinner.2]
    calc
      chordSlope * averageUtility =
          tangentSlope * populationAverageUtility population utility winner +
            (chordSlope * averageUtility -
              tangentSlope * populationAverageUtility population utility winner) := by ring
      _ ≤ tangentSlope * populationAverageUtility population utility winner +
            scoreError / btScale := by
          gcongr
          exact (le_div_iff₀ hbtScale).mpr (by simpa [mul_comm] using hscaled)
  have hcomparison := hlinear alternative
  have hscore_comparison :
      pairwiseBordaScore sampling preference alternative ≤
        pairwiseBordaScore sampling preference winner + scoreError :=
    hnear alternative
  have hfirst_bound :
      chordSlope * populationAverageUtility population utility alternative ≤
        tangentSlope * populationAverageUtility population utility winner +
          (tangentSlope - chordSlope) * averageUtility + scoreError / btScale := by
    have hscaled :
        btScale *
          ((chordSlope * populationAverageUtility population utility alternative -
            tangentSlope * averageUtility) -
            (tangentSlope * populationAverageUtility population utility winner -
              chordSlope * averageUtility)) ≤ scoreError := by
      change btScale *
          ((sigmoidChordSlope btScale * populationAverageUtility population utility alternative -
            (1 : ℝ) / 4 * policyAverageUtility population utility sampling) -
            ((1 : ℝ) / 4 * populationAverageUtility population utility winner -
              sigmoidChordSlope btScale * policyAverageUtility population utility sampling)) ≤
        scoreError
      linarith [hcomparison.1, hscore_comparison, hwinner.2]
    have hunscaled :
        chordSlope * populationAverageUtility population utility alternative -
            tangentSlope * averageUtility ≤
          tangentSlope * populationAverageUtility population utility winner -
            chordSlope * averageUtility + scoreError / btScale := by
      calc
        chordSlope * populationAverageUtility population utility alternative -
            tangentSlope * averageUtility =
          tangentSlope * populationAverageUtility population utility winner -
            chordSlope * averageUtility +
            ((chordSlope * populationAverageUtility population utility alternative -
              tangentSlope * averageUtility) -
              (tangentSlope * populationAverageUtility population utility winner -
                chordSlope * averageUtility)) := by ring
        _ ≤ tangentSlope * populationAverageUtility population utility winner -
              chordSlope * averageUtility + scoreError / btScale := by
            gcongr
            exact (le_div_iff₀ hbtScale).mpr (by simpa [mul_comm] using hscaled)
    linarith
  have hchord_pos : 0 < chordSlope := sigmoidChordSlope_pos hbtScale
  have hslope_gap : 0 ≤ tangentSlope - chordSlope := by
    change 0 ≤ (1 : ℝ) / 4 - sigmoidChordSlope btScale
    exact sub_nonneg.mpr (sigmoidChordSlope_le_one_quarter hbtScale)
  have hfirst_scaled := mul_le_mul_of_nonneg_left hfirst_bound hchord_pos.le
  have haverage_scaled := mul_le_mul_of_nonneg_left haverage_bound hslope_gap
  change chordSlope ^ 2 * populationAverageUtility population utility alternative ≤
    tangentSlope ^ 2 * populationAverageUtility population utility winner +
      tangentSlope * scoreError / btScale
  calc
    chordSlope ^ 2 * populationAverageUtility population utility alternative =
        chordSlope *
          (chordSlope * populationAverageUtility population utility alternative) := by ring
    _ ≤ chordSlope *
          (tangentSlope * populationAverageUtility population utility winner +
            (tangentSlope - chordSlope) * averageUtility + scoreError / btScale) :=
      hfirst_scaled
    _ = chordSlope * tangentSlope * populationAverageUtility population utility winner +
          chordSlope * (tangentSlope - chordSlope) * averageUtility +
          chordSlope * scoreError / btScale := by ring
    _ ≤ chordSlope * tangentSlope * populationAverageUtility population utility winner +
          (tangentSlope - chordSlope) *
            (tangentSlope * populationAverageUtility population utility winner + scoreError / btScale) +
          chordSlope * scoreError / btScale := by
      refine add_le_add (add_le_add (le_refl _) ?_) (le_refl _)
      calc
        chordSlope * (tangentSlope - chordSlope) * averageUtility =
            (tangentSlope - chordSlope) * (chordSlope * averageUtility) := by ring
        _ ≤ (tangentSlope - chordSlope) *
              (tangentSlope * populationAverageUtility population utility winner +
                scoreError / btScale) := haverage_scaled
    _ = tangentSlope ^ 2 * populationAverageUtility population utility winner +
          tangentSlope * scoreError / btScale := by ring

/--
Ratio form of the source Borda population-limit guarantee. Every Borda-score
maximizer has at least `(ℓ_β / L)^2` times the welfare of every alternative,
with `L = 1 / 4`.
-/
theorem pairwiseBordaScore_welfare_lower_bound_of_maximizer
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (hutility : UnitIntervalUtilityProfile utility)
    (sampling : PMF Alternative) {btScale : ℝ} (hbtScale : 0 < btScale)
    (winner : Alternative)
    (hmax : ∀ alternative,
      pairwiseBordaScore sampling
          (populationBradleyTerryPreference population utility btScale) alternative ≤
        pairwiseBordaScore sampling
          (populationBradleyTerryPreference population utility btScale) winner)
    (alternative : Alternative) :
    (sigmoidChordSlope btScale / ((1 : ℝ) / 4)) ^ 2 *
        populationAverageUtility population utility alternative ≤
      populationAverageUtility population utility winner := by
  have hsquare := pairwiseBordaScore_welfare_square_bound_of_maximizer
    population utility hutility sampling hbtScale winner hmax alternative
  have htangent_pos : 0 < ((1 : ℝ) / 4) ^ 2 := by norm_num
  calc
    (sigmoidChordSlope btScale / ((1 : ℝ) / 4)) ^ 2 *
        populationAverageUtility population utility alternative =
        ((sigmoidChordSlope btScale) ^ 2 *
          populationAverageUtility population utility alternative) / (((1 : ℝ) / 4) ^ 2) := by
            field_simp
    _ ≤ (((1 : ℝ) / 4) ^ 2 * populationAverageUtility population utility winner) /
          (((1 : ℝ) / 4) ^ 2) :=
      (div_le_div_iff_of_pos_right htangent_pos).mpr hsquare
    _ = populationAverageUtility population utility winner := by
      field_simp

end Welfare
end Alignment
end AppliedModelingLib
