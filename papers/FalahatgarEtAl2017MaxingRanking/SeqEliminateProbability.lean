import FalahatgarEtAl2017MaxingRanking.SequentialElimination
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.PAC

/-!
# Seq-Eliminate probability composition

This file is the finite union-bound layer in Appendix A.3.  It is deliberately
separate from the implementation of `Compare`: a caller supplies a finite
indexing of the realized calls and their individual failure guarantees.  The
deterministic path theorem then turns simultaneous call success into the
paper's `ε`-maximum conclusion.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL

/--
When the realized Seq-Eliminate path is valid, the output event contains that
path-success event and therefore has at least the same finite-PMF probability.
-/
theorem seqEliminate_success_probability_of_pathValid
    {Arm Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ)
    (step : Outcome → Arm → Arm → Arm)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (maximum initial : Arm) (challengers : List Arm)
    (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (happears : initial = maximum ∨ maximum ∈ challengers)
    (delta : ℝ)
    (hpathProbability : 1 - delta ≤ pmfProbClassical law
      (fun outcome => SequentialEliminationPathValid preferenceGap epsilon
        (step outcome) initial challengers)) :
    1 - delta ≤ pmfProbClassical law
      (fun outcome => EpsilonMaximum preferenceGap epsilon
        (sequentialEliminate (step outcome) initial challengers)) := by
  calc
    1 - delta ≤ pmfProbClassical law
        (fun outcome => SequentialEliminationPathValid preferenceGap epsilon
          (step outcome) initial challengers) := hpathProbability
    _ ≤ pmfProbClassical law
        (fun outcome => EpsilonMaximum preferenceGap epsilon
          (sequentialEliminate (step outcome) initial challengers)) := by
          apply pmfProbClassical_le_of_imp
          intro outcome hvalid
          exact sequentialEliminate_epsilonMaximum_of_maximumAppears_of_pathValid
            preferenceGap epsilon (step outcome) hantisymmetric hsst hepsilon
            maximum initial challengers hvalid hmaximum happears

/--
Appendix A.3's finite union-bound interface.  If a finite collection of
randomized Compare calls each has failure probability at most `δ / #calls`,
and simultaneous success entails realized-path validity, Seq-Eliminate returns
an `ε`-maximum with probability at least `1 - δ`.
-/
theorem seqEliminate_success_probability_of_indexedCallGuarantees
    {Arm Index Outcome : Type*} [Fintype Index] [Nonempty Index]
    [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ)
    (step : Outcome → Arm → Arm → Arm)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (maximum initial : Arm) (challengers : List Arm)
    (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (happears : initial = maximum ∨ maximum ∈ challengers)
    (delta : ℝ) (callFailure : Index → Outcome → Prop)
    (hpathValid : ∀ outcome, AllPACSucceed callFailure outcome →
      SequentialEliminationPathValid preferenceGap epsilon
        (step outcome) initial challengers)
    (hfailure : ∀ call,
      pmfProbClassical law (callFailure call) ≤
        delta / (Fintype.card Index : ℝ)) :
    1 - delta ≤ pmfProbClassical law
      (fun outcome => EpsilonMaximum preferenceGap epsilon
        (sequentialEliminate (step outcome) initial challengers)) := by
  apply seqEliminate_success_probability_of_pathValid law preferenceGap epsilon step
    hantisymmetric hsst hepsilon maximum initial challengers hmaximum happears delta
  calc
    1 - delta ≤ pmfProbClassical law (AllPACSucceed callFailure) :=
      pmfProb_allPACSucceed_ge_one_sub law callFailure delta hfailure
    _ ≤ pmfProbClassical law
        (fun outcome => SequentialEliminationPathValid preferenceGap epsilon
          (step outcome) initial challengers) := by
          apply pmfProbClassical_le_of_imp
          intro outcome hsuccess
          exact hpathValid outcome hsuccess

end FalahatgarEtAl2017MaxingRanking
