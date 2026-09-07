import AppliedModelingLib.Alignment.Welfare.Linearization

/-!
# Bradley--Terry linearization for randomized policies

The pointwise affine bounds from `Linearization` also apply after independently
drawing two alternatives from arbitrary finite policies. Keeping this bridge
separate from Borda makes it reusable for zero-sum preference-game arguments.

## Main declarations

- `populationBradleyTerryPolicyMargin`
- `populationBradleyTerryPolicyMargin_upper_linearization_source`
- `IsPopulationBradleyTerryMaximinOver`
- `populationBradleyTerryMaximin_welfare_lower_bound_source`
-/

namespace AppliedModelingLib
namespace Alignment
namespace Welfare

/--
The centered expected Bradley--Terry win probability of `firstPolicy` against
`secondPolicy` in a finite heterogeneous population.
-/
noncomputable def populationBradleyTerryPolicyMargin
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (btScale : ℝ) (firstPolicy secondPolicy : PMF Alternative) : ℝ :=
  pmfPairExp firstPolicy secondPolicy (fun first second =>
    (populationBradleyTerryPreference population utility btScale).prob PUnit.unit.{1} first second -
      (1 : ℝ) / 2)

/--
The upper half of the source Lemma-1 affine sandwich, averaged over two
independent policies. This is the direct reusable bridge in the proof of the
population-limit NLHF distortion bound.
-/
theorem populationBradleyTerryPolicyMargin_upper_linearization_source
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (hutility : UnitIntervalUtilityProfile utility)
    {btScale : ℝ} (hbtScale : 0 < btScale)
    (firstPolicy secondPolicy : PMF Alternative) :
    populationBradleyTerryPolicyMargin population utility btScale firstPolicy secondPolicy ≤
      btScale *
        ((1 : ℝ) / 4 * policyAverageUtility population utility firstPolicy -
          sigmoidChordSlope btScale * policyAverageUtility population utility secondPolicy) := by
  unfold populationBradleyTerryPolicyMargin
  calc
    pmfPairExp firstPolicy secondPolicy (fun first second =>
        (populationBradleyTerryPreference population utility btScale).prob PUnit.unit.{1} first second -
          (1 : ℝ) / 2) ≤
        pmfPairExp firstPolicy secondPolicy (fun first second =>
          btScale *
            ((1 : ℝ) / 4 * populationAverageUtility population utility first -
              sigmoidChordSlope btScale * populationAverageUtility population utility second)) := by
          unfold pmfPairExp
          apply pmfExp_le_pmfExp_of_forall_le
          intro first
          apply pmfExp_le_pmfExp_of_forall_le
          intro second
          exact (populationBradleyTerryPreference_linearization_source population utility hutility
            hbtScale first second).2
    _ = btScale *
        ((1 : ℝ) / 4 * policyAverageUtility population utility firstPolicy -
          sigmoidChordSlope btScale * policyAverageUtility population utility secondPolicy) := by
          simp [pmfPairExp, policyAverageUtility, pmfExp_const_mul, pmfExp_sub]

/--
The source's population-limit NLHF game condition over an explicit feasible
policy set. Centering makes the symmetric zero-sum game value zero, so a
maximin policy has nonnegative margin against each feasible opponent.
-/
def IsPopulationBradleyTerryMaximinOver
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (btScale : ℝ) (feasible : PMF Alternative → Prop) (policy : PMF Alternative) : Prop :=
  feasible policy ∧ ∀ opponent, feasible opponent →
    0 ≤ populationBradleyTerryPolicyMargin population utility btScale policy opponent

/--
Population-limit welfare guarantee for a centered Bradley--Terry maximin
policy. This is the one-linearization argument behind the source's NLHF
distortion upper bound, stated for an arbitrary explicit feasible set rather
than only a KL ball.
-/
theorem populationBradleyTerryMaximin_welfare_lower_bound_source
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (hutility : UnitIntervalUtilityProfile utility)
    {btScale : ℝ} (hbtScale : 0 < btScale)
    (feasible : PMF Alternative → Prop) (policy benchmark : PMF Alternative)
    (hpolicy : IsPopulationBradleyTerryMaximinOver population utility btScale feasible policy)
    (hbenchmark : feasible benchmark) :
    (sigmoidChordSlope btScale / ((1 : ℝ) / 4)) *
        policyAverageUtility population utility benchmark ≤
      policyAverageUtility population utility policy := by
  have hmargin := hpolicy.2 benchmark hbenchmark
  have hupper := populationBradleyTerryPolicyMargin_upper_linearization_source
    population utility hutility hbtScale policy benchmark
  have hscaled :
      0 ≤ btScale *
        ((1 : ℝ) / 4 * policyAverageUtility population utility policy -
          sigmoidChordSlope btScale * policyAverageUtility population utility benchmark) :=
    le_trans hmargin hupper
  have hlinear :
      sigmoidChordSlope btScale * policyAverageUtility population utility benchmark ≤
        (1 : ℝ) / 4 * policyAverageUtility population utility policy := by
    have := nonneg_of_mul_nonneg_right hscaled hbtScale
    linarith
  have hquarter : (0 : ℝ) < (1 : ℝ) / 4 := by norm_num
  calc
    (sigmoidChordSlope btScale / ((1 : ℝ) / 4)) *
        policyAverageUtility population utility benchmark =
        (sigmoidChordSlope btScale * policyAverageUtility population utility benchmark) /
          ((1 : ℝ) / 4) := by ring
    _ ≤ policyAverageUtility population utility policy :=
      (div_le_iff₀ hquarter).2 (by simpa [mul_comm] using hlinear)

end Welfare
end Alignment
end AppliedModelingLib
