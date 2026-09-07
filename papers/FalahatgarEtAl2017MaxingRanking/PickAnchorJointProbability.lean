import FalahatgarEtAl2017MaxingRanking.PickAnchorSeqEliminate
import AppliedModelingLib.Foundations.Probability.IndependentProduct
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.IIDConcentration

/-!
# Pick-Anchor probability composition on a joint experiment

The source draws a fresh sample and runs randomized comparisons.  This module
states the final two-event union bound on one joint probability space, rather
than silently treating the sample and comparison randomness as the same PMF.
The product construction used by a concrete caller is responsible for the
required marginal and iid facts.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/--
The source's fresh sample remains exactly uniform under an independent product
with arbitrary comparison randomness: events depending only on the first
coordinate have their Pick-Anchor sampling probability.
-/
theorem pickAnchorUniformSample_jointMiss_probability_le_delta_half
    {Arm ComparisonOutcome : Type*}
    [Fintype Arm] [DecidableEq Arm]
    [Fintype ComparisonOutcome] [DecidableEq ComparisonOutcome]
    (cutoff : ℕ) (delta : ℝ) (top : Finset Arm)
    (hcutoff : 0 < cutoff) (htopCard : top.card = cutoff)
    (hdeltaPos : 0 < delta) (hdeltaLe : delta ≤ 1)
    (comparisonLaw : PMF ComparisonOutcome) :
    pmfProbClassical
      (pmfProd
        (pickAnchorUniformSampleLaw
          (pickAnchorSampleCount (Fintype.card Arm) cutoff delta)
          (pickAnchorSampleCount_le_armCount (Fintype.card Arm) cutoff delta))
        comparisonLaw)
      (fun joint => ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ pickAnchorSampleSet joint.1) ≤
      delta / 2 := by
  classical
  let sampleLaw := pickAnchorUniformSampleLaw
    (pickAnchorSampleCount (Fintype.card Arm) cutoff delta)
    (pickAnchorSampleCount_le_armCount (Fintype.card Arm) cutoff delta)
  let miss : finiteFreshList Arm
      (pickAnchorSampleCount (Fintype.card Arm) cutoff delta) ∅ → Prop :=
    fun sample => ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ pickAnchorSampleSet sample
  letI : DecidablePred miss := Classical.decPred miss
  letI : DecidablePred (fun joint : finiteFreshList Arm
      (pickAnchorSampleCount (Fintype.card Arm) cutoff delta) ∅ × ComparisonOutcome =>
      miss joint.1) := Classical.decPred _
  have hmiss : pmfProb sampleLaw miss ≤ delta / 2 := by
    simpa only [sampleLaw, miss, pmfProbClassical] using
      (pickAnchor_miss_probability_le_delta_half cutoff delta top
        hcutoff htopCard hdeltaPos hdeltaLe)
  have hmarginal : pmfProb (pmfProd sampleLaw comparisonLaw)
      (fun joint => miss joint.1) = pmfProb sampleLaw miss :=
    pmfProb_pmfProd_fst_eq sampleLaw comparisonLaw miss
  simpa only [sampleLaw, miss, pmfProbClassical] using hmarginal.le.trans hmiss

/--
The same marginal fact for the general product measure used by the adaptive
comparison analysis.  The finite fresh-sample coordinate carries its discrete
sigma algebra, while the comparison-stream coordinate may be arbitrary.
-/
theorem pickAnchorUniformSample_measureProd_miss_probability_le_delta_half
    {Arm ComparisonOutcome : Type*}
    [Fintype Arm] [DecidableEq Arm]
    [MeasurableSpace ComparisonOutcome]
    (cutoff : ℕ) (delta : ℝ) (top : Finset Arm)
    (hcutoff : 0 < cutoff) (htopCard : top.card = cutoff)
    (hdeltaPos : 0 < delta) (hdeltaLe : delta ≤ 1)
    (comparisonLaw : Measure ComparisonOutcome) [IsProbabilityMeasure comparisonLaw]
    [MeasurableSpace (finiteFreshList Arm
      (pickAnchorSampleCount (Fintype.card Arm) cutoff delta) ∅)]
    [DiscreteMeasurableSpace (finiteFreshList Arm
      (pickAnchorSampleCount (Fintype.card Arm) cutoff delta) ∅)] :
    ((pickAnchorUniformSampleLaw
      (pickAnchorSampleCount (Fintype.card Arm) cutoff delta)
      (pickAnchorSampleCount_le_armCount (Fintype.card Arm) cutoff delta)).toMeasure.prod
      comparisonLaw).real
      {joint | ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ pickAnchorSampleSet joint.1} ≤
      delta / 2 := by
  classical
  let sampleLaw := pickAnchorUniformSampleLaw
    (pickAnchorSampleCount (Fintype.card Arm) cutoff delta)
    (pickAnchorSampleCount_le_armCount (Fintype.card Arm) cutoff delta)
  let miss : finiteFreshList Arm
      (pickAnchorSampleCount (Fintype.card Arm) cutoff delta) ∅ → Prop :=
    fun sample => ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ pickAnchorSampleSet sample
  letI : DecidablePred miss := Classical.decPred miss
  have hmissPMF : pmfProb sampleLaw miss ≤ delta / 2 := by
    simpa only [sampleLaw, miss, pmfProbClassical] using
      (pickAnchor_miss_probability_le_delta_half cutoff delta top
        hcutoff htopCard hdeltaPos hdeltaLe)
  have hmissMeasure : sampleLaw.toMeasure.real {sample | miss sample} ≤ delta / 2 := by
    rw [← AppliedModelingLib.pmfProb_eq_toMeasure_real sampleLaw miss]
    exact hmissPMF
  have hfst : MeasurePreserving Prod.fst (sampleLaw.toMeasure.prod comparisonLaw)
      sampleLaw.toMeasure := measurePreserving_fst
  have hmarginal : (sampleLaw.toMeasure.prod comparisonLaw).real
      {joint | miss joint.1} = sampleLaw.toMeasure.real {sample | miss sample} := by
    have hmass : (sampleLaw.toMeasure.prod comparisonLaw)
        {joint | miss joint.1} = sampleLaw.toMeasure {sample | miss sample} := by
      simpa only using hfst.measure_preimage
        (MeasurableSet.of_discrete : MeasurableSet {sample | miss sample}).nullMeasurableSet
    exact congrArg ENNReal.toReal hmass
  simpa only [sampleLaw, miss] using hmarginal.le.trans hmissMeasure

/--
Adjoining an independent first coordinate does not change independence of a
comparison-stream family living on the second coordinate.  This is the
probabilistic transport needed to combine the uniform Pick-Anchor sample with
the source's iid comparison observations.
-/
theorem iIndepFun_snd_of_iIndepFun
    {Sample ComparisonOutcome Index Value : Type*}
    [MeasurableSpace Sample] [MeasurableSpace ComparisonOutcome]
    [MeasurableSpace Value]
    (sampleLaw : Measure Sample) [IsProbabilityMeasure sampleLaw]
    (comparisonLaw : Measure ComparisonOutcome) [IsProbabilityMeasure comparisonLaw]
    (stream : Index → ComparisonOutcome → Value)
    (hindependent : iIndepFun stream comparisonLaw)
    (hmeasurable : ∀ index, Measurable (stream index)) :
    iIndepFun (fun (index : Index) (joint : Sample × ComparisonOutcome) => stream index joint.2)
      (sampleLaw.prod comparisonLaw) := by
  refine iIndepFun_iff_measure_inter_preimage_eq_mul.mpr ?_
  intro indices sets hsets
  have hinterMeasurable : MeasurableSet (⋂ index ∈ indices,
      stream index ⁻¹' sets index) := by
    refine Finset.measurableSet_biInter (s := indices) ?_
    intro index hindex
    exact (hmeasurable index) (hsets index hindex)
  have hprojection : MeasurePreserving Prod.snd (sampleLaw.prod comparisonLaw)
      comparisonLaw := measurePreserving_snd
  have hinter : (sampleLaw.prod comparisonLaw)
      (⋂ index ∈ indices,
        (fun joint : Sample × ComparisonOutcome => stream index joint.2) ⁻¹' sets index) =
      comparisonLaw (⋂ index ∈ indices, stream index ⁻¹' sets index) := by
    rw [show (⋂ index ∈ indices,
        (fun joint : Sample × ComparisonOutcome => stream index joint.2) ⁻¹' sets index) =
        Prod.snd ⁻¹' (⋂ index ∈ indices, stream index ⁻¹' sets index) by
          ext joint
          simp]
    exact hprojection.measure_preimage hinterMeasurable.nullMeasurableSet
  calc
    (sampleLaw.prod comparisonLaw)
        (⋂ index ∈ indices,
          (fun joint : Sample × ComparisonOutcome => stream index joint.2) ⁻¹' sets index) =
        comparisonLaw (⋂ index ∈ indices, stream index ⁻¹' sets index) := hinter
    _ = ∏ index ∈ indices, comparisonLaw (stream index ⁻¹' sets index) :=
      hindependent.measure_inter_preimage_eq_mul indices hsets
    _ = ∏ index ∈ indices,
        (sampleLaw.prod comparisonLaw)
          ((fun joint : Sample × ComparisonOutcome => stream index joint.2) ⁻¹' sets index) := by
      apply Finset.prod_congr rfl
      intro index hindex
      have hpreimageMeasurable : MeasurableSet (stream index ⁻¹' sets index) :=
        (hmeasurable index) (hsets index hindex)
      symm
      exact hprojection.measure_preimage hpreimageMeasurable.nullMeasurableSet

/-- Expectations of second-coordinate comparison variables are unchanged by the product lift. -/
theorem integral_snd_eq_of_productProbability
    {Sample ComparisonOutcome : Type*}
    [MeasurableSpace Sample] [MeasurableSpace ComparisonOutcome]
    (sampleLaw : Measure Sample) [IsProbabilityMeasure sampleLaw]
    (comparisonLaw : Measure ComparisonOutcome) [IsProbabilityMeasure comparisonLaw]
    (value : ComparisonOutcome → ℝ) :
    (∫ joint, value joint.2 ∂sampleLaw.prod comparisonLaw) =
      ∫ outcome, value outcome ∂comparisonLaw := by
  rw [integral_fun_snd]
  simp

/-- Almost-sure second-coordinate comparison conditions lift through the product measure. -/
theorem ae_snd_of_productProbability
    {Sample ComparisonOutcome : Type*}
    [MeasurableSpace Sample] [MeasurableSpace ComparisonOutcome]
    (sampleLaw : Measure Sample) [IsProbabilityMeasure sampleLaw]
    (comparisonLaw : Measure ComparisonOutcome) [IsProbabilityMeasure comparisonLaw]
    (property : ComparisonOutcome → Prop)
    (hproperty : ∀ᵐ outcome ∂comparisonLaw, property outcome) :
    ∀ᵐ joint ∂sampleLaw.prod comparisonLaw, property joint.2 := by
  have hprojection : MeasurePreserving Prod.snd (sampleLaw.prod comparisonLaw)
      comparisonLaw := measurePreserving_snd
  simpa using hprojection.quasiMeasurePreserving.ae hproperty

/--
Lemma 3's final union bound on a joint sample-and-comparison experiment.  A
top-set hit and an `ε`-maximum of the realized sample, each failing with mass
at most `δ / 2`, yield a good anchor with probability at least `1 - δ`.
-/
theorem pickAnchor_goodAnchor_measure_probability_of_topSetHit_and_sampleWinner
    {Arm Ω : Type*} [Fintype Arm] [DecidableEq Arm] [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (sample : Ω → Finset Arm) (winner : Ω → Arm)
    (top : Finset Arm) (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ) (cutoff : ℕ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (htopRank : ∀ pivot ∈ top,
      (strictlyBetterArms preferenceGap pivot).card ≤ cutoff)
    (delta : ℝ)
    (hmiss : law.real {outcome | ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ sample outcome} ≤ delta / 2)
    (hwinnerFailure : law.real {outcome | ¬ ∀ arm ∈ sample outcome,
      -epsilon ≤ preferenceGap (winner outcome) arm} ≤ delta / 2)
    (hgoodMeasurable : MeasurableSet {outcome |
      GoodAnchor preferenceGap epsilon cutoff (winner outcome)}) :
    1 - delta ≤ law.real {outcome |
      GoodAnchor preferenceGap epsilon cutoff (winner outcome)} := by
  let miss : Set Ω := {outcome | ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ sample outcome}
  let winnerFailure : Set Ω := {outcome | ¬ ∀ arm ∈ sample outcome,
    -epsilon ≤ preferenceGap (winner outcome) arm}
  have hfailureSubset :
      {outcome | ¬ GoodAnchor preferenceGap epsilon cutoff (winner outcome)} ⊆
        miss ∪ winnerFailure := by
    intro outcome hnotGood
    by_contra hnotUnion
    have hhit : ∃ pivot, pivot ∈ top ∧ pivot ∈ sample outcome := by
      by_contra hnoHit
      exact hnotUnion (Or.inl hnoHit)
    have hwinner : ∀ arm ∈ sample outcome,
        -epsilon ≤ preferenceGap (winner outcome) arm := by
      by_contra hnoWinner
      exact hnotUnion (Or.inr hnoWinner)
    rcases hhit with ⟨pivot, hpivotTop, hpivotSample⟩
    exact hnotGood (goodAnchor_of_subsetEpsilonMaximum preferenceGap epsilon cutoff
      hantisymmetric hsst hepsilon (sample outcome) pivot (winner outcome)
      hpivotSample hwinner (htopRank pivot hpivotTop))
  have hfailure : law.real {outcome |
      ¬ GoodAnchor preferenceGap epsilon cutoff (winner outcome)} ≤ delta := by
    calc
      law.real {outcome | ¬ GoodAnchor preferenceGap epsilon cutoff (winner outcome)} ≤
          law.real (miss ∪ winnerFailure) :=
        measureReal_mono hfailureSubset (measure_ne_top law _)
      _ ≤ law.real miss + law.real winnerFailure := measureReal_union_le _ _
      _ ≤ delta := by
        change law.real {outcome | ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ sample outcome} +
            law.real {outcome | ¬ ∀ arm ∈ sample outcome,
              -epsilon ≤ preferenceGap (winner outcome) arm} ≤ delta
        linarith
  have hcomplement : {outcome | ¬ GoodAnchor preferenceGap epsilon cutoff (winner outcome)} =
      {outcome | GoodAnchor preferenceGap epsilon cutoff (winner outcome)}ᶜ := by
    ext outcome
    simp
  rw [hcomplement, probReal_compl_eq_one_sub hgoodMeasurable] at hfailure
  linarith

/--
The complete probabilistic implication in Lemma 3 once a joint experiment has
the source's uniform-sample top-hit bound.  The sampled Seq-Eliminate failure
bound is discharged here from the actual complete-SST adaptive comparison
model, with the paper's `δ / 2` allocation.
-/
theorem pickAnchorSource_goodAnchor_highProbability_of_jointTopHit
    {Arm Ω : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (cutoff : ℕ) (delta epsilon : ℝ)
    (sample : Ω → finiteFreshList Arm
      (pickAnchorSampleCount (Fintype.card Arm) cutoff delta) ∅)
    (observation : Arm → Arm → ℕ → Ω → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (top : Finset Arm)
    (hindependent : ∀ challenger incumbent,
      iIndepFun (observation challenger incumbent) law)
    (hmeasurable : ∀ challenger incumbent sampleIndex,
      Measurable (observation challenger incumbent sampleIndex))
    (hbounded : ∀ challenger incumbent,
      ∀ sampleIndex < fixedSampleBudget 0 epsilon
          ((delta / 2) / (Fintype.card (Arm × Arm) : ℝ)),
        ∀ᵐ outcome ∂law, observation challenger incumbent sampleIndex outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ challenger incumbent,
      ∀ sampleIndex < fixedSampleBudget 0 epsilon
          ((delta / 2) / (Fintype.card (Arm × Arm) : ℝ)),
        law[observation challenger incumbent sampleIndex] =
          1 / 2 + preferenceGap challenger incumbent)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hcutoff : 0 < cutoff)
    (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (htopRank : ∀ pivot ∈ top,
      (strictlyBetterArms preferenceGap pivot).card ≤ cutoff)
    (hmiss : law.real {outcome | ¬ ∃ pivot, pivot ∈ top ∧
      pivot ∈ pickAnchorSampleSet (sample outcome)} ≤ delta / 2)
    (hgoodMeasurable : MeasurableSet {outcome |
      GoodAnchor preferenceGap epsilon cutoff
        (pickAnchorSampleSeqEliminate
          (adaptiveCompareStep observation
            (fixedSampleBudget 0 epsilon
              ((delta / 2) / (Fintype.card (Arm × Arm) : ℝ)))
            epsilon ((delta / 2) / (Fintype.card (Arm × Arm) : ℝ)) outcome)
          (sample outcome)
          (pickAnchorSampleCount_pos (Fintype.card Arm) cutoff delta
            Fintype.card_pos hcutoff hdelta hdeltaLeOne))}) :
    1 - delta ≤ law.real {outcome |
      GoodAnchor preferenceGap epsilon cutoff
        (pickAnchorSampleSeqEliminate
          (adaptiveCompareStep observation
            (fixedSampleBudget 0 epsilon
              ((delta / 2) / (Fintype.card (Arm × Arm) : ℝ)))
            epsilon ((delta / 2) / (Fintype.card (Arm × Arm) : ℝ)) outcome)
          (sample outcome)
          (pickAnchorSampleCount_pos (Fintype.card Arm) cutoff delta
            Fintype.card_pos hcutoff hdelta hdeltaLeOne))} := by
  apply pickAnchor_goodAnchor_measure_probability_of_topSetHit_and_sampleWinner
    law (fun outcome => pickAnchorSampleSet (sample outcome))
    (fun outcome => pickAnchorSampleSeqEliminate
      (adaptiveCompareStep observation
        (fixedSampleBudget 0 epsilon ((delta / 2) / (Fintype.card (Arm × Arm) : ℝ)))
        epsilon ((delta / 2) / (Fintype.card (Arm × Arm) : ℝ)) outcome)
      (sample outcome)
      (pickAnchorSampleCount_pos (Fintype.card Arm) cutoff delta
        Fintype.card_pos hcutoff hdelta hdeltaLeOne))
    top preferenceGap epsilon cutoff hantisymmetric hsst (le_of_lt hepsilon) htopRank delta
  · exact hmiss
  · exact pickAnchorSource_sampleWinner_failure_probability_le_delta_half
      law cutoff delta epsilon observation preferenceGap hindependent hmeasurable hbounded hmean
      hantisymmetric hself hcomplete hsst hcutoff hepsilon hdelta hdeltaLeOne sample
  · exact hgoodMeasurable

/--
Lemma 3's complete probability conclusion on the explicit independent product
of its uniform-without-replacement sample and comparison-stream experiment.
The product transport discharges both `δ / 2` premises rather than assuming
either a sampled-winner guarantee or a top-hit probability.
-/
theorem pickAnchorSource_goodAnchor_highProbability_of_independentProduct
    {Arm ComparisonOutcome : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    [MeasurableSpace ComparisonOutcome]
    (comparisonLaw : Measure ComparisonOutcome) [IsProbabilityMeasure comparisonLaw]
    (cutoff : ℕ) (delta epsilon : ℝ)
    (observation : Arm → Arm → ℕ → ComparisonOutcome → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (top : Finset Arm)
    (hindependent : ∀ challenger incumbent,
      iIndepFun (observation challenger incumbent) comparisonLaw)
    (hmeasurable : ∀ challenger incumbent sampleIndex,
      Measurable (observation challenger incumbent sampleIndex))
    (hbounded : ∀ challenger incumbent,
      ∀ sampleIndex < fixedSampleBudget 0 epsilon
          ((delta / 2) / (Fintype.card (Arm × Arm) : ℝ)),
        ∀ᵐ outcome ∂comparisonLaw,
          observation challenger incumbent sampleIndex outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ challenger incumbent,
      ∀ sampleIndex < fixedSampleBudget 0 epsilon
          ((delta / 2) / (Fintype.card (Arm × Arm) : ℝ)),
        comparisonLaw[observation challenger incumbent sampleIndex] =
          1 / 2 + preferenceGap challenger incumbent)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hcutoff : 0 < cutoff)
    (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (htopCard : top.card = cutoff)
    (htopRank : ∀ pivot ∈ top,
      (strictlyBetterArms preferenceGap pivot).card ≤ cutoff)
    [MeasurableSpace (finiteFreshList Arm
      (pickAnchorSampleCount (Fintype.card Arm) cutoff delta) ∅)]
    [DiscreteMeasurableSpace (finiteFreshList Arm
      (pickAnchorSampleCount (Fintype.card Arm) cutoff delta) ∅)]
    (hgoodMeasurable : MeasurableSet {joint |
      GoodAnchor preferenceGap epsilon cutoff
        (pickAnchorSampleSeqEliminate
          (adaptiveCompareStep
            (fun (challenger : Arm) (incumbent : Arm) (sampleIndex : ℕ)
              (joint : (finiteFreshList Arm
                (pickAnchorSampleCount (Fintype.card Arm) cutoff delta) ∅) ×
                ComparisonOutcome) =>
              observation challenger incumbent sampleIndex joint.2)
            (fixedSampleBudget 0 epsilon
              ((delta / 2) / (Fintype.card (Arm × Arm) : ℝ)))
            epsilon ((delta / 2) / (Fintype.card (Arm × Arm) : ℝ)) joint)
          joint.1
          (pickAnchorSampleCount_pos (Fintype.card Arm) cutoff delta
            Fintype.card_pos hcutoff hdelta hdeltaLeOne))}) :
    1 - delta ≤
      ((pickAnchorUniformSampleLaw
        (pickAnchorSampleCount (Fintype.card Arm) cutoff delta)
        (pickAnchorSampleCount_le_armCount (Fintype.card Arm) cutoff delta)).toMeasure.prod
        comparisonLaw).real {joint |
        GoodAnchor preferenceGap epsilon cutoff
          (pickAnchorSampleSeqEliminate
            (adaptiveCompareStep
              (fun (challenger : Arm) (incumbent : Arm) (sampleIndex : ℕ)
                (joint : (finiteFreshList Arm
                  (pickAnchorSampleCount (Fintype.card Arm) cutoff delta) ∅) ×
                  ComparisonOutcome) =>
                observation challenger incumbent sampleIndex joint.2)
              (fixedSampleBudget 0 epsilon
                ((delta / 2) / (Fintype.card (Arm × Arm) : ℝ)))
              epsilon ((delta / 2) / (Fintype.card (Arm × Arm) : ℝ)) joint)
            joint.1
            (pickAnchorSampleCount_pos (Fintype.card Arm) cutoff delta
              Fintype.card_pos hcutoff hdelta hdeltaLeOne))} := by
  let sampleLaw := pickAnchorUniformSampleLaw
    (pickAnchorSampleCount (Fintype.card Arm) cutoff delta)
    (pickAnchorSampleCount_le_armCount (Fintype.card Arm) cutoff delta)
  refine pickAnchorSource_goodAnchor_highProbability_of_jointTopHit
    (sampleLaw.toMeasure.prod comparisonLaw) cutoff delta epsilon
    (fun joint => joint.1)
    (fun (challenger : Arm) (incumbent : Arm) (sampleIndex : ℕ)
      (joint : (finiteFreshList Arm
        (pickAnchorSampleCount (Fintype.card Arm) cutoff delta) ∅) × ComparisonOutcome) =>
      observation challenger incumbent sampleIndex joint.2)
    preferenceGap top
    ?_ ?_ ?_ ?_
    hantisymmetric hself hcomplete hsst hcutoff hepsilon hdelta hdeltaLeOne htopRank
    ?_ ?_
  · intro challenger incumbent
    exact iIndepFun_snd_of_iIndepFun sampleLaw.toMeasure comparisonLaw
      (observation challenger incumbent) (hindependent challenger incumbent)
      (fun sampleIndex => hmeasurable challenger incumbent sampleIndex)
  · intro challenger incumbent sampleIndex
    exact (hmeasurable challenger incumbent sampleIndex).comp measurable_snd
  · intro challenger incumbent sampleIndex hsampleIndex
    exact ae_snd_of_productProbability sampleLaw.toMeasure comparisonLaw _
      (hbounded challenger incumbent sampleIndex hsampleIndex)
  · intro challenger incumbent sampleIndex hsampleIndex
    change (∫ joint,
      observation challenger incumbent sampleIndex joint.2 ∂sampleLaw.toMeasure.prod comparisonLaw) =
      1 / 2 + preferenceGap challenger incumbent
    rw [integral_snd_eq_of_productProbability sampleLaw.toMeasure comparisonLaw]
    exact hmean challenger incumbent sampleIndex hsampleIndex
  · simpa only [sampleLaw] using
      (pickAnchorUniformSample_measureProd_miss_probability_le_delta_half
        cutoff delta top hcutoff htopCard hdelta hdeltaLeOne comparisonLaw)
  · simpa only [sampleLaw] using hgoodMeasurable

end FalahatgarEtAl2017MaxingRanking
