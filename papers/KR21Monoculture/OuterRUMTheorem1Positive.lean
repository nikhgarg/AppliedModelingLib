import KR21Monoculture.OuterRUMTheorem1Lift

open AppliedModelingLib MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace KR21Monoculture
namespace DistributionalAccuracyFamily

/-!
# Positive-accuracy outer Theorem 1 lift for KR21

KR21 defines its noisy permutation family only at positive accuracy.  The
generic outer lift predates that source-domain distinction and asks for
atomwise continuity at every real parameter.  This source-scoped variant
proves the same outer conclusion while requiring continuity only at positive
accuracies actually reached from the positive human baseline.
-/

/--
The outer Theorem 1 crossing proof under source-domain atomwise regularity.
Every parameter at which continuity is used is at least `thetaH`, hence
positive.  All outer-D integrability, atom measurability, pointwise Definition
2, Definition 3, and Definition 1 monotonicity obligations remain explicit.
-/
theorem distributional_theorem1_of_outer_atomwise_regular_positive
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) (thetaH : ℝ) (center : Ranking n)
    (hthetaH : 0 < thetaH)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hatom_measurable : ∀ theta pi,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((F.dist theta value) pi).toReal) D)
    (hatom_continuous : ∀ value pi theta, 0 < theta →
      EpsilonContinuousAt (fun theta' => ((F.dist theta' value) pi).toReal) theta)
    (hatom_tendsto : ∀ᵐ value ∂D, ∀ pi,
      Tendsto (fun theta => ((F.dist theta value) pi).toReal) atTop
        (nhds (((PMF.pure center : PMF (Ranking n)) pi).toReal)))
    (hprefers_independent : F.PrefersIndependentReranking D thetaH)
    (hpure_gap : F.theorem1_g_pureCenterLimit D thetaH center <
      theorem1_f_pureCenterLimit D center)
    (hprefers_weaker : ∀ thetaA, thetaH < thetaA →
      F.PrefersWeakerCompetition D thetaA thetaH)
    (halgorithm_against_human : ∀ thetaA, thetaH < thetaA →
      F.theorem1_h D thetaA thetaH <
        F.theorem1_algorithmAgainstHuman D thetaA thetaH) :
    F.DistributionalTheorem1Target D thetaH := by
  apply distributional_theorem1 F D thetaH
  refine {
    prefers_independent_at_equal := hprefers_independent
    f_continuity := ?_
    g_continuity := ?_
    asymptotic_first_dominance := ?_
    prefers_weaker_above := hprefers_weaker
    algorithm_against_human_above := halgorithm_against_human
  }
  · intro theta htheta
    exact epsilonContinuousAt_theorem1_f_of_atomwise F D thetaH theta hvalue
      hatom_measurable
      (fun value pi => hatom_continuous value pi theta
        (lt_of_lt_of_le hthetaH htheta))
  · intro theta htheta
    exact epsilonContinuousAt_theorem1_g_of_atomwise F D thetaH theta hvalue
      hatom_measurable
      (fun value pi => hatom_continuous value pi theta
        (lt_of_lt_of_le hthetaH htheta))
  · exact exists_outer_first_dominance_of_atomwise_tendsto
      F D thetaH center hvalue hatom_measurable hatom_tendsto hpure_gap

end DistributionalAccuracyFamily
end KR21Monoculture
