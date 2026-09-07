import FalahatgarEtAl2017MaxingRanking.CoreDefinitions

/-!
# Good-anchor consequences of SST

Appendix A.5's deterministic step is separated from the sampling-without-
replacement probability calculation: an approximate winner of a sample that
contains a sufficiently high arm is a good anchor for the whole arm set.
-/

namespace FalahatgarEtAl2017MaxingRanking

/-- The finite set of arms strictly preferable to a given pivot. -/
noncomputable def strictlyBetterArms {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ) (pivot : Arm) : Finset Arm :=
  Finset.univ.filter fun arm => 0 < preferenceGap arm pivot

/--
If `pivot` is weakly preferable to an arm, SST bounds that arm's preference
over an output which is `ε`-preferable to `pivot`.
-/
theorem preference_le_epsilon_of_epsilonPreferableTo_pivot {Arm : Type*}
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (pivot output competitor : Arm)
    (houtputPivot : -epsilon ≤ preferenceGap output pivot)
    (hpivotCompetitor : 0 ≤ preferenceGap pivot competitor) :
    preferenceGap competitor output ≤ epsilon := by
  by_cases hcompetitorOutput : preferenceGap competitor output ≤ 0
  · exact hcompetitorOutput.trans hepsilon
  have hcompetitorOutputPos : 0 ≤ preferenceGap competitor output := le_of_lt (lt_of_not_ge hcompetitorOutput)
  have hchain := hsst pivot competitor output hpivotCompetitor hcompetitorOutputPos
  have hcompetitor_le_pivot :
      preferenceGap competitor output ≤ preferenceGap pivot output :=
    (le_max_right _ _).trans hchain
  have hpivotOutput : preferenceGap pivot output ≤ epsilon := by
    rw [hantisymmetric output pivot]
    linarith
  exact hcompetitor_le_pivot.trans hpivotOutput

/--
Appendix A.5's deterministic good-anchor step.  If at most `cutoff` arms
strictly beat a pivot and the output is `ε`-preferable to that pivot, then at
most `cutoff` arms beat the output by more than `ε`.
-/
theorem goodAnchor_of_epsilonPreferableTo_pivot {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ) (cutoff : ℕ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (pivot output : Arm)
    (houtputPivot : -epsilon ≤ preferenceGap output pivot)
    (hpivotCount : (strictlyBetterArms preferenceGap pivot).card ≤ cutoff) :
    GoodAnchor preferenceGap epsilon cutoff output := by
  unfold GoodAnchor
  calc
    (Finset.univ.filter fun arm => epsilon < preferenceGap arm output).card ≤
        (strictlyBetterArms preferenceGap pivot).card := by
          apply Finset.card_le_card
          intro arm harm
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at harm ⊢
          by_contra hnotBetter
          have hnotStrict : ¬ 0 < preferenceGap arm pivot := by
            simpa [strictlyBetterArms] using hnotBetter
          have harmPivot : preferenceGap arm pivot ≤ 0 := le_of_not_gt hnotStrict
          have hpivotArm : 0 ≤ preferenceGap pivot arm := by
            rw [hantisymmetric arm pivot]
            linarith
          have hbound := preference_le_epsilon_of_epsilonPreferableTo_pivot
            preferenceGap epsilon hantisymmetric hsst hepsilon pivot output arm
            houtputPivot hpivotArm
          linarith
    _ ≤ cutoff := hpivotCount

/--
The sampled-set form used by Pick-Anchor: an `ε`-maximum of a subset inherits
the good-anchor conclusion whenever that subset contains the chosen pivot.
-/
theorem goodAnchor_of_subsetEpsilonMaximum {Arm : Type*}
    [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ) (cutoff : ℕ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (subset : Finset Arm) (pivot output : Arm)
    (hpivotMem : pivot ∈ subset)
    (hsubsetWinner : ∀ arm ∈ subset, -epsilon ≤ preferenceGap output arm)
    (hpivotCount : (strictlyBetterArms preferenceGap pivot).card ≤ cutoff) :
    GoodAnchor preferenceGap epsilon cutoff output :=
  goodAnchor_of_epsilonPreferableTo_pivot preferenceGap epsilon cutoff hantisymmetric hsst
    hepsilon pivot output (hsubsetWinner pivot hpivotMem) hpivotCount

end FalahatgarEtAl2017MaxingRanking
