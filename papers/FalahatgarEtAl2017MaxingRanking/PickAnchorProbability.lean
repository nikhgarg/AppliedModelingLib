import FalahatgarEtAl2017MaxingRanking.GoodAnchors
import FalahatgarEtAl2017MaxingRanking.PickAnchorSampling
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.PAC

/-!
# Pick-Anchor probability composition

Appendix A.5 separates into a random top-set hit and a successful
Seq-Eliminate call on the sampled set.  This file proves their exact finite-PMF
union-bound composition.  The source's separate without-replacement sampling
inequality is intentionally left as the next input theorem rather than being
silently folded into this result.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL

/-- The finite set of ordered Pick-Anchor samples which miss a given top set. -/
noncomputable def pickAnchorMissSamples {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (count : ℕ) (top : Finset Arm) : Finset (finiteFreshList Arm count ∅) :=
  (Finset.univ : Finset (finiteFreshList Arm count ∅)).filter fun sample =>
    ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ pickAnchorSampleSet sample

/--
The Pick-Anchor miss probability is exactly a finite cardinal ratio.  Together
with `pickAnchorUniformSampleLaw_eq_uniformPMF`, this isolates the remaining
without-replacement tail inequality as a purely combinatorial statement.
-/
theorem pickAnchor_miss_probability_eq_card_ratio
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (count : ℕ) (hcountLe : count ≤ Fintype.card Arm) (top : Finset Arm) :
    pmfProbClassical (pickAnchorUniformSampleLaw count hcountLe)
      (fun sample => ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ pickAnchorSampleSet sample) =
      ((pickAnchorMissSamples count top).card : ℝ) /
        (Fintype.card (finiteFreshList Arm count ∅) : ℝ) := by
  classical
  letI : Nonempty (finiteFreshList Arm count ∅) :=
    ⟨pickAnchorCanonicalSample count hcountLe⟩
  letI : DecidablePred (fun sample : finiteFreshList Arm count ∅ =>
      ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ pickAnchorSampleSet sample) := Classical.decPred _
  unfold pmfProbClassical
  rw [pickAnchorUniformSampleLaw_eq_uniformPMF count hcountLe]
  unfold pickAnchorUniformFreshSamplePMF
  refine Eq.trans ?_ (pmfProb_uniformPMF_finset (pickAnchorMissSamples count top))
  apply pmfProb_congr
  intro sample
  simp [pickAnchorMissSamples]

/-- The number of miss samples is the falling factorial of the complement size. -/
theorem pickAnchorMissSamples_card_eq_descFactorial
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (count : ℕ) (top : Finset Arm) :
    (pickAnchorMissSamples count top).card =
      (Fintype.card Arm - top.card).descFactorial count := by
  classical
  letI : DecidablePred (fun sample : finiteFreshList Arm count ∅ =>
      pickAnchorAvoidsTop top sample) := Classical.decPred _
  letI : Fintype {sample : finiteFreshList Arm count ∅ //
      pickAnchorAvoidsTop top sample} :=
    Fintype.ofFinite _
  have hcard : Fintype.card
      {sample : finiteFreshList Arm count ∅ // pickAnchorAvoidsTop top sample} =
      (pickAnchorMissSamples count top).card := by
    apply Fintype.card_of_subtype (pickAnchorMissSamples count top)
    intro sample
    simp only [pickAnchorMissSamples, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (pickAnchorAvoidsTop_iff_noHit top sample).symm
  calc
    (pickAnchorMissSamples count top).card = Fintype.card
        {sample : finiteFreshList Arm count ∅ // pickAnchorAvoidsTop top sample} := hcard.symm
    _ = Fintype.card (finiteFreshList Arm count top) :=
      Fintype.card_congr (pickAnchorAvoidingFreshListEquiv top)
    _ = (Fintype.card Arm - top.card).descFactorial count :=
      finiteFreshList_card_eq_descFactorial count top

/--
Exact hypergeometric form of Pick-Anchor's top-set miss probability.  The
only remaining analytic step in the source is to upper-bound this falling
factorial ratio by its exponential display.
-/
theorem pickAnchor_miss_probability_eq_descFactorial_ratio
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (count : ℕ) (hcountLe : count ≤ Fintype.card Arm) (top : Finset Arm) :
    pmfProbClassical (pickAnchorUniformSampleLaw count hcountLe)
      (fun sample => ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ pickAnchorSampleSet sample) =
      ((Fintype.card Arm - top.card).descFactorial count : ℝ) /
        ((Fintype.card Arm).descFactorial count : ℝ) := by
  rw [pickAnchor_miss_probability_eq_card_ratio count hcountLe top,
    pickAnchorMissSamples_card_eq_descFactorial count top,
    finiteFreshList_card_eq_descFactorial count ∅]
  simp

/--
The capped full-sample branch of Pick-Anchor has zero top-set miss probability.
This is the deterministic endpoint of the source's without-replacement hit
calculation when the requested sample count is the full arm set.
-/
theorem pickAnchor_fullSample_miss_probability_zero
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (count : ℕ) (hcountLe : count ≤ Fintype.card Arm)
    (hcount : count = Fintype.card Arm) (top : Finset Arm) (htop : top.Nonempty) :
    pmfProbClassical (pickAnchorUniformSampleLaw count hcountLe)
      (fun sample => ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ pickAnchorSampleSet sample) = 0 := by
  classical
  letI : DecidableEq (finiteFreshList Arm count ∅) := Classical.decEq _
  letI : Fintype (finiteFreshList Arm count ∅) := Fintype.ofFinite _
  letI : DecidablePred (fun sample : finiteFreshList Arm count ∅ =>
      ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ pickAnchorSampleSet sample) := Classical.decPred _
  unfold pmfProbClassical
  unfold pmfProb pmfExp
  apply Finset.sum_eq_zero
  intro sample _
  by_cases hmiss : ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ pickAnchorSampleSet sample
  · exact False.elim (hmiss (pickAnchor_topSet_hit_of_fullSample sample top hcount htop))
  · simp [hmiss]

/--
The deterministic near-full-sample regime has zero top-set miss probability
under Pick-Anchor's exact without-replacement PMF.
-/
theorem pickAnchor_miss_probability_zero_of_card_add_gt_armCount
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (count : ℕ) (hcountLe : count ≤ Fintype.card Arm) (top : Finset Arm)
    (hcapacity : Fintype.card Arm < count + top.card) :
    pmfProbClassical (pickAnchorUniformSampleLaw count hcountLe)
      (fun sample => ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ pickAnchorSampleSet sample) = 0 := by
  classical
  letI : DecidableEq (finiteFreshList Arm count ∅) := Classical.decEq _
  letI : Fintype (finiteFreshList Arm count ∅) := Fintype.ofFinite _
  letI : DecidablePred (fun sample : finiteFreshList Arm count ∅ =>
      ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ pickAnchorSampleSet sample) := Classical.decPred _
  unfold pmfProbClassical
  unfold pmfProb pmfExp
  apply Finset.sum_eq_zero
  intro sample _
  by_cases hmiss : ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ pickAnchorSampleSet sample
  · exact False.elim (hmiss
      (pickAnchor_topSet_hit_of_card_add_gt_armCount sample top hcapacity))
  · simp [hmiss]

/-- The source's ceiling-and-cap Pick-Anchor rule has zero miss probability in its capped branch. -/
theorem pickAnchor_miss_probability_zero_of_rawCeiling
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (cutoff : ℕ) (delta : ℝ) (top : Finset Arm) (htop : top.Nonempty)
    (hraw : Fintype.card Arm ≤
      ⌈(Fintype.card Arm : ℝ) / (cutoff : ℝ) * Real.log (2 / delta)⌉₊) :
    pmfProbClassical
      (pickAnchorUniformSampleLaw (pickAnchorSampleCount (Fintype.card Arm) cutoff delta)
        (pickAnchorSampleCount_le_armCount (Fintype.card Arm) cutoff delta))
      (fun sample => ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ pickAnchorSampleSet sample) = 0 := by
  apply pickAnchor_fullSample_miss_probability_zero
    (pickAnchorSampleCount (Fintype.card Arm) cutoff delta)
    (pickAnchorSampleCount_le_armCount (Fintype.card Arm) cutoff delta)
  · exact pickAnchorSampleCount_eq_armCount_of_armCount_le_rawCeiling
      (Fintype.card Arm) cutoff delta hraw
  · exact htop

/-- The two failure events in Appendix A.5's Pick-Anchor argument. -/
def PickAnchorFailure {Arm Outcome : Type*} [DecidableEq Arm]
    (sample : Outcome → Finset Arm) (winner : Outcome → Arm) (pivot : Arm)
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ) : Bool → Outcome → Prop
  | false, outcome => pivot ∉ sample outcome
  | true, outcome => ¬ ∀ arm ∈ sample outcome,
      -epsilon ≤ preferenceGap (winner outcome) arm

/--
The top-set version of Pick-Anchor's two failures.  An explicit finite top set
is tie-safe: every one of its members will satisfy the rank premise needed by
the deterministic good-anchor argument.
-/
def PickAnchorTopSetFailure {Arm Outcome : Type*} [DecidableEq Arm]
    (sample : Outcome → Finset Arm) (winner : Outcome → Arm) (top : Finset Arm)
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ) : Bool → Outcome → Prop
  | false, outcome => ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ sample outcome
  | true, outcome => ¬ ∀ arm ∈ sample outcome,
      -epsilon ≤ preferenceGap (winner outcome) arm

/--
Lemma 3's probability composition.  A sampled pivot hit and an `ε`-maximum
sample winner, each failing with probability at most `δ / 2`, make the winner
an `(ε, cutoff)`-good anchor with probability at least `1 - δ`.
-/
theorem pickAnchor_goodAnchor_probability_of_hit_and_sampleWinner
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (sample : Outcome → Finset Arm) (winner : Outcome → Arm)
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ) (cutoff : ℕ) (pivot : Arm)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (hpivotCount : (strictlyBetterArms preferenceGap pivot).card ≤ cutoff)
    (delta : ℝ)
    (hmiss : pmfProbClassical law (fun outcome => pivot ∉ sample outcome) ≤ delta / 2)
    (hwinnerFailure : pmfProbClassical law
      (fun outcome => ¬ ∀ arm ∈ sample outcome,
        -epsilon ≤ preferenceGap (winner outcome) arm) ≤ delta / 2) :
    1 - delta ≤ pmfProbClassical law
      (fun outcome => GoodAnchor preferenceGap epsilon cutoff (winner outcome)) := by
  have hsimultaneous :
      1 - delta ≤ pmfProbClassical law
        (AllPACSucceed
          (PickAnchorFailure sample winner pivot preferenceGap epsilon)) := by
    apply pmfProb_allPACSucceed_ge_one_sub law
      (PickAnchorFailure sample winner pivot preferenceGap epsilon) delta
    intro failure
    cases failure <;>
      simpa [PickAnchorFailure] using (by
        first | exact hmiss | exact hwinnerFailure)
  calc
    1 - delta ≤ pmfProbClassical law
        (AllPACSucceed
          (PickAnchorFailure sample winner pivot preferenceGap epsilon)) := hsimultaneous
    _ ≤ pmfProbClassical law
        (fun outcome => GoodAnchor preferenceGap epsilon cutoff (winner outcome)) := by
          apply pmfProbClassical_le_of_imp
          intro outcome hsuccess
          apply goodAnchor_of_subsetEpsilonMaximum preferenceGap epsilon cutoff
            hantisymmetric hsst hepsilon (sample outcome) pivot (winner outcome)
          · simpa [PickAnchorFailure, AllPACSucceed] using hsuccess false
          · simpa [PickAnchorFailure, AllPACSucceed] using hsuccess true
          · exact hpivotCount

/--
Lemma 3's top-`n'` form.  It applies the same finite union bound to a sampled
hit of an explicit tie-safe top set and to Seq-Eliminate's sampled-winner
event.
-/
theorem pickAnchor_goodAnchor_probability_of_topSetHit_and_sampleWinner
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (sample : Outcome → Finset Arm) (winner : Outcome → Arm)
    (top : Finset Arm) (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ) (cutoff : ℕ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (htopRank : ∀ pivot ∈ top,
      (strictlyBetterArms preferenceGap pivot).card ≤ cutoff)
    (delta : ℝ)
    (hmiss : pmfProbClassical law
      (fun outcome => ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ sample outcome) ≤ delta / 2)
    (hwinnerFailure : pmfProbClassical law
      (fun outcome => ¬ ∀ arm ∈ sample outcome,
        -epsilon ≤ preferenceGap (winner outcome) arm) ≤ delta / 2) :
    1 - delta ≤ pmfProbClassical law
      (fun outcome => GoodAnchor preferenceGap epsilon cutoff (winner outcome)) := by
  have hsimultaneous :
      1 - delta ≤ pmfProbClassical law
        (AllPACSucceed
          (PickAnchorTopSetFailure sample winner top preferenceGap epsilon)) := by
    apply pmfProb_allPACSucceed_ge_one_sub law
      (PickAnchorTopSetFailure sample winner top preferenceGap epsilon) delta
    intro failure
    cases failure <;>
      simpa [PickAnchorTopSetFailure] using (by
        first | exact hmiss | exact hwinnerFailure)
  calc
    1 - delta ≤ pmfProbClassical law
        (AllPACSucceed
          (PickAnchorTopSetFailure sample winner top preferenceGap epsilon)) := hsimultaneous
    _ ≤ pmfProbClassical law
        (fun outcome => GoodAnchor preferenceGap epsilon cutoff (winner outcome)) := by
          apply pmfProbClassical_le_of_imp
          intro outcome hsuccess
          have hhit : ∃ pivot, pivot ∈ top ∧ pivot ∈ sample outcome := by
            by_contra hnoHit
            apply hsuccess false
            simpa [PickAnchorTopSetFailure] using hnoHit
          rcases hhit with ⟨pivot, hpivotTop, hpivotSample⟩
          apply goodAnchor_of_subsetEpsilonMaximum preferenceGap epsilon cutoff
            hantisymmetric hsst hepsilon (sample outcome) pivot (winner outcome)
          · exact hpivotSample
          · simpa [PickAnchorTopSetFailure, AllPACSucceed] using hsuccess true
          · exact htopRank pivot hpivotTop

end FalahatgarEtAl2017MaxingRanking
