import FalahatgarEtAl2017MaxingRanking.CoreDefinitions
import FalahatgarEtAl2017MaxingRanking.FixedSampleCompare

/-!
# OPT-Maximize final check

This is the deterministic correctness argument in Appendix A.7 / Lemma 18.
It separates the final comparison loop from the earlier Pick-Anchor and Prune
probability calculations.
-/

namespace FalahatgarEtAl2017MaxingRanking

/--
The final phase of OPT-Maximize returns the anchor unless one candidate passes
the `Compare(e, anchor, 2ε/3, ε, _)` upper test, in which case it returns the
Seq-Eliminate fallback on the pruned set.
-/
noncomputable def optMaximizeFinalOutput {Arm : Type*}
    (anchor fallback : Arm) (candidates : Finset Arm)
    (decision : Arm → CompareDecision) : Arm :=
  if ∃ candidate ∈ candidates, decision candidate = .upper then fallback else anchor

/--
Lemma 18's deterministic conclusion.  When the pruned candidate set contains
an absolute maximum, a successful upper test on that maximum selects the
subset winner; otherwise the anchor is already an `ε`-maximum.
-/
theorem optMaximizeFinalOutput_epsilonMaximum_of_subsetWinner {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (maximum anchor fallback : Arm) (candidates : Finset Arm)
    (decision : Arm → CompareDecision)
    (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (hmaximumMem : maximum ∈ candidates)
    (hfallback : ∀ candidate ∈ candidates,
      -epsilon ≤ preferenceGap fallback candidate)
    (hdetect : epsilon < preferenceGap maximum anchor → decision maximum = .upper) :
    EpsilonMaximum preferenceGap epsilon
      (optMaximizeFinalOutput anchor fallback candidates decision) := by
  by_cases hstrict : epsilon < preferenceGap maximum anchor
  · have hupper : decision maximum = .upper := hdetect hstrict
    have hreturns :
        optMaximizeFinalOutput anchor fallback candidates decision = fallback := by
      unfold optMaximizeFinalOutput
      rw [if_pos ⟨maximum, hmaximumMem, hupper⟩]
    rw [hreturns]
    exact epsilonMaximum_of_subsetContainsAbsoluteMaximum preferenceGap epsilon hantisymmetric
      hsst hepsilon (↑candidates : Set Arm) maximum fallback hmaximum (by simpa using hmaximumMem)
      (by
        intro candidate hcandidate
        exact hfallback candidate (by simpa using hcandidate))
  · have hanchorMaximum : EpsilonMaximum preferenceGap epsilon anchor := by
      apply epsilonMaximum_of_epsilonPreferableTo_absoluteMaximum preferenceGap epsilon
        hantisymmetric hsst hepsilon maximum
      · exact hmaximum
      · rw [hantisymmetric maximum anchor]
        linarith
    have hfallbackMaximum : EpsilonMaximum preferenceGap epsilon fallback :=
      epsilonMaximum_of_subsetContainsAbsoluteMaximum preferenceGap epsilon hantisymmetric
        hsst hepsilon (↑candidates : Set Arm) maximum fallback hmaximum (by simpa using hmaximumMem)
        (by
          intro candidate hcandidate
          exact hfallback candidate (by simpa using hcandidate))
    unfold optMaximizeFinalOutput
    split
    · exact hfallbackMaximum
    · exact hanchorMaximum

end FalahatgarEtAl2017MaxingRanking
