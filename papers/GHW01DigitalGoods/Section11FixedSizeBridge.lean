import GHW01DigitalGoods.BoundedSupply

/-!
# Section 11 fixed-size sampling bridge

The Section 11 mechanisms use `uniformFixedSizeSampleLaw`, whereas the exact
without-replacement concentration theorem is stated with the finite
cardinality ratio `fixedSizeSampleProbability`.  This module proves that the
two probability models coincide for every finite event.  It is deliberately
separate from the mechanism claims: the bridge supplies a real probability
obligation and cannot itself turn a caller-supplied good event into a source
theorem.
-/

namespace GHW01DigitalGoods

open AppliedModelingLib

noncomputable section

/-- `fixedSizeSampleProbability` is independent of the computational choice
of a decidable predicate for the same event. -/
theorem fixedSizeSampleProbability_decidable_pred_irrel
    {Agent : Type*} [DecidableEq Agent]
    (all : Finset Agent) (sampleSize : ℕ) (event : Finset Agent → Prop)
    (d₁ d₂ : DecidablePred event) :
    @fixedSizeSampleProbability Agent _ all sampleSize event d₁ =
      @fixedSizeSampleProbability Agent _ all sampleSize event d₂ := by
  unfold fixedSizeSampleProbability
  have hfilter :
      @Finset.filter (Finset Agent) event d₁ (all.powersetCard sampleSize) =
        @Finset.filter (Finset Agent) event d₂ (all.powersetCard sampleSize) := by
    ext sample
    simp
  rw [hfilter]

/-- The uniform PMF on exactly `sampleSize` bidders agrees exactly with the
cardinality-ratio probability used by Lemma 6.1. -/
theorem uniformFixedSizeSampleLaw_event_probability_eq_fixedSizeSampleProbability
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (sampleSize : ℕ) (hsize : sampleSize ≤ Fintype.card Agent)
    (event : Finset Agent → Prop) :
    pmfEventProbability (uniformFixedSizeSampleLaw sampleSize hsize)
        (fun sample => event sample.1) =
      @fixedSizeSampleProbability Agent _ (Finset.univ : Finset Agent)
        sampleSize event (Classical.decPred event) := by
  classical
  let samples : Finset (Finset Agent) :=
    (Finset.univ : Finset Agent).powersetCard sampleSize
  let eventSamples : Finset (Finset Agent) := samples.filter event
  have hsamples_nonempty : samples.Nonempty := by
    simpa [samples] using
      Finset.powersetCard_nonempty.mpr (by simpa using hsize)
  letI : Nonempty (FixedSizeSampleSpace Agent sampleSize) :=
    Finset.nonempty_coe_sort.mpr hsamples_nonempty
  let eventSet : Finset (FixedSizeSampleSpace Agent sampleSize) :=
    Finset.univ.filter fun sample => event sample.1
  have hevent_card : eventSet.card = eventSamples.card := by
    let embed : FixedSizeSampleSpace Agent sampleSize ↪ Finset Agent :=
      Function.Embedding.subtype _
    have hmap : eventSet.map embed = eventSamples := by
      ext sample
      simp [eventSet, eventSamples, samples, embed, and_comm]
    calc
      eventSet.card = (eventSet.map embed).card := (Finset.card_map _).symm
      _ = eventSamples.card := congrArg Finset.card hmap
  have hspace_card : Fintype.card (FixedSizeSampleSpace Agent sampleSize) =
      samples.card := by
    simp [samples]
  unfold pmfEventProbability uniformFixedSizeSampleLaw
  have hprob : AppliedModelingLib.pmfProb
      (AppliedModelingLib.uniformPMF (FixedSizeSampleSpace Agent sampleSize))
      (fun sample => event sample.1) =
        (eventSet.card : ℝ) /
          (Fintype.card (FixedSizeSampleSpace Agent sampleSize) : ℝ) := by
    rw [← AppliedModelingLib.pmfProb_uniformPMF_finset eventSet]
    apply AppliedModelingLib.pmfProb_congr
    intro sample
    simp [eventSet]
  rw [hprob, hevent_card, hspace_card]
  rfl

/-- Lemma 6.1 expressed in the exact PMF used by the Section 11 samplers.
This is a derived lower-tail probability, not a caller-supplied good-event
premise. -/
theorem uniformFixedSizeSampleLaw_lower_tail
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (eligible : Finset Agent) {sampleSize : ℕ}
    (hsample_pos : 0 < sampleSize)
    (hsample_lt : sampleSize < Fintype.card Agent)
    {delta : ℝ} (hdelta_pos : 0 < delta) (hdelta_le_one : delta ≤ 1) :
    pmfEventProbability
        (uniformFixedSizeSampleLaw sampleSize hsample_lt.le)
        (fun sample =>
          (fixedSizeHitCount eligible sample.1 : ℝ) <
            (1 - delta) * (eligible.card : ℝ) *
              (sampleSize : ℝ) / (Fintype.card Agent : ℝ)) <
      Real.exp
        (-((eligible.card : ℝ) * (sampleSize : ℝ) * delta ^ 2 /
          (2 * (Fintype.card Agent : ℝ)))) := by
  classical
  rw [uniformFixedSizeSampleLaw_event_probability_eq_fixedSizeSampleProbability
    (Agent := Agent) sampleSize hsample_lt.le
    (fun sample =>
      (fixedSizeHitCount eligible sample : ℝ) <
        (1 - delta) * (eligible.card : ℝ) *
          (sampleSize : ℝ) / (Fintype.card Agent : ℝ))]
  simpa using
    (lemma6_1_fixed_size_lower_tail
      (A := (Finset.univ : Finset Agent)) (B := eligible)
      (Finset.subset_univ eligible) hsample_pos hsample_lt
      hdelta_pos hdelta_le_one)

/-- A non-strict lower-tail support bound for a nonempty eligible set.  This
is not a restatement of source Lemma 6.1: it is the auxiliary strengthening
needed when the selected-prefix reduction yields a non-strict event. -/
theorem uniformFixedSizeSampleLaw_lower_tail_le_of_nonempty
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (eligible : Finset Agent) (heligible : eligible.Nonempty)
    {sampleSize : ℕ}
    (hsample_pos : 0 < sampleSize)
    (hsample_lt : sampleSize < Fintype.card Agent)
    {delta : ℝ} (hdelta_pos : 0 < delta) (hdelta_le_one : delta ≤ 1) :
    pmfEventProbability
        (uniformFixedSizeSampleLaw sampleSize hsample_lt.le)
        (fun sample =>
          (fixedSizeHitCount eligible sample.1 : ℝ) ≤
            (1 - delta) * (eligible.card : ℝ) *
              (sampleSize : ℝ) / (Fintype.card Agent : ℝ)) <
      Real.exp
        (-((eligible.card : ℝ) * (sampleSize : ℝ) * delta ^ 2 /
          (2 * (Fintype.card Agent : ℝ)))) := by
  classical
  rw [uniformFixedSizeSampleLaw_event_probability_eq_fixedSizeSampleProbability
    (Agent := Agent) sampleSize hsample_lt.le
    (fun sample =>
      (fixedSizeHitCount eligible sample : ℝ) ≤
        (1 - delta) * (eligible.card : ℝ) *
          (sampleSize : ℝ) / (Fintype.card Agent : ℝ))]
  simpa using
    (lemma6_1_fixed_size_lower_tail_le_of_nonempty
      (A := (Finset.univ : Finset Agent)) (B := eligible)
      (Finset.subset_univ eligible) heligible hsample_pos hsample_lt
      hdelta_pos hdelta_le_one)

end

end GHW01DigitalGoods
