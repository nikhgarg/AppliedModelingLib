import GHW01DigitalGoods.AuctionMainTheorems
import GHW01DigitalGoods.Section11FixedSizeBridge
import AppliedModelingLib.Foundations.Math.FiniteRounding

/-!
# Directional random-sampling optimal-threshold auction

The source Section 6 auction draws one sample, computes its optimal threshold,
and sells only to the opposite market.  This module keeps that directional
auction distinct from the later dual-price variant, which prices both sides.
-/

namespace GHW01DigitalGoods

open AppliedModelingLib
open AppliedModelingLib.Auction
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- Complementation is a checked permutation of the uniform sample space when
the population is split into two equal-size halves.  This is the exact
fixed-cardinality symmetry used in the source proof of Theorem 6.2. -/
noncomputable def fixedHalfSampleComplementEquiv
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (sampleSize : ℕ) (hhalf : Fintype.card Agent = sampleSize + sampleSize) :
    FixedSizeSampleSpace Agent sampleSize ≃ FixedSizeSampleSpace Agent sampleSize := by
  classical
  let all : Finset Agent := Finset.univ
  let complement : FixedSizeSampleSpace Agent sampleSize →
      FixedSizeSampleSpace Agent sampleSize := fun sample =>
    ⟨all \ sample.1, by
      apply Finset.mem_powersetCard.mpr
      constructor
      · exact Finset.sdiff_subset
      · have hsample_card : sample.1.card = sampleSize :=
          (Finset.mem_powersetCard.mp sample.2).2
        have hall_card : all.card = sampleSize + sampleSize := by
          simpa [all] using hhalf
        rw [Finset.card_sdiff_of_subset (Finset.mem_powersetCard.mp sample.2).1,
          hall_card, hsample_card]
        omega⟩
  refine
    { toFun := complement
      invFun := complement
      left_inv := ?_
      right_inv := ?_ }
  · intro sample
    apply Subtype.ext
    dsimp [complement]
    exact Finset.sdiff_sdiff_eq_self
      (Finset.mem_powersetCard.mp sample.2).1
  · intro sample
    apply Subtype.ext
    dsimp [complement]
    exact Finset.sdiff_sdiff_eq_self
      (Finset.mem_powersetCard.mp sample.2).1

@[simp]
theorem fixedHalfSampleComplementEquiv_val
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (sampleSize : ℕ) (hhalf : Fintype.card Agent = sampleSize + sampleSize)
    (sample : FixedSizeSampleSpace Agent sampleSize) :
    (fixedHalfSampleComplementEquiv sampleSize hhalf sample).1 =
      (Finset.univ : Finset Agent) \ sample.1 := by
  rfl

/-- Counting a fixed sample side inside a set is exactly the fixed-size hit
count used by Lemma 6.1. -/
theorem sideCountInSet_sampledSide_true_eq_fixedSizeHitCount
    {Agent : Type*} [DecidableEq Agent]
    (sample s : Finset Agent) :
    sideCountInSet (sampledSideAssignment sample) true s =
      fixedSizeHitCount s sample := by
  classical
  unfold sideCountInSet sampledSideAssignment fixedSizeHitCount
  congr 1
  ext i
  simp [and_comm]

/-- The nonsample side is the hit count of the complementary sample. -/
theorem sideCountInSet_sampledSide_false_eq_complement_hitCount
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (sample s : Finset Agent) :
    sideCountInSet (sampledSideAssignment sample) false s =
      fixedSizeHitCount s ((Finset.univ : Finset Agent) \ sample) := by
  classical
  unfold sideCountInSet sampledSideAssignment fixedSizeHitCount
  congr 1
  ext i
  simp [and_comm]

/-- A uniformly chosen exact half-sample has the same law as its complement.
This is the finite-law bridge needed to use Lemma 6.1 for the source proof's
nonsample-side tail event. -/
theorem uniformFixedSizeSampleLaw_complement_event_probability_eq
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (sampleSize : ℕ) (hhalf : Fintype.card Agent = sampleSize + sampleSize)
    (event : FixedSizeSampleSpace Agent sampleSize → Prop) :
    pmfEventProbability
        (uniformFixedSizeSampleLaw sampleSize (by omega : sampleSize ≤ Fintype.card Agent))
        (fun sample =>
          event (fixedHalfSampleComplementEquiv sampleSize hhalf sample)) =
      pmfEventProbability
        (uniformFixedSizeSampleLaw sampleSize (by omega : sampleSize ≤ Fintype.card Agent))
        event := by
  classical
  have hsize : sampleSize ≤ Fintype.card Agent := by omega
  letI : Nonempty (FixedSizeSampleSpace Agent sampleSize) :=
    Finset.nonempty_coe_sort.mpr
      (Finset.powersetCard_nonempty.mpr (by simpa using hsize))
  simpa [pmfEventProbability, uniformFixedSizeSampleLaw] using
    (AppliedModelingLib.pmfProb_uniformPMF_eq_of_comp_equiv
      (fixedHalfSampleComplementEquiv sampleSize hhalf) event
      (fun sample => event (fixedHalfSampleComplementEquiv sampleSize hhalf sample))
      (fun _ => Iff.rfl)).symm

/-- In a uniform exact half-sample, any fixed eligible set has at least a third
of its members in the sample except with the Lemma 6.1 exponential tail. -/
theorem uniformFixedHalf_hitCount_ge_third_probability
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (eligible : Finset Agent) (sampleSize : ℕ)
    (hsample_pos : 0 < sampleSize)
    (hhalf : Fintype.card Agent = sampleSize + sampleSize) :
    1 - Real.exp (-(eligible.card : ℝ) / 36) ≤
      pmfEventProbability
        (uniformFixedSizeSampleLaw sampleSize (by omega : sampleSize ≤ Fintype.card Agent))
        (fun sample =>
          (eligible.card : ℝ) / 3 ≤ fixedSizeHitCount eligible sample.1) := by
  classical
  have hsample_lt : sampleSize < Fintype.card Agent := by omega
  have htail := uniformFixedSizeSampleLaw_lower_tail eligible hsample_pos hsample_lt
    (show (0 : ℝ) < 1 / 3 by norm_num)
    (show (1 / 3 : ℝ) ≤ 1 by norm_num)
  have hthreshold :
      (1 - (1 / 3 : ℝ)) * (eligible.card : ℝ) * (sampleSize : ℝ) /
          (Fintype.card Agent : ℝ) =
        (eligible.card : ℝ) / 3 := by
    have hsample_real : (sampleSize : ℝ) ≠ 0 := by positivity
    have hhalf_real : (Fintype.card Agent : ℝ) =
        (sampleSize : ℝ) + sampleSize := by exact_mod_cast hhalf
    rw [hhalf_real]
    field_simp
    ring
  have hexponent :
      -((eligible.card : ℝ) * (sampleSize : ℝ) * (1 / 3 : ℝ) ^ 2 /
          (2 * (Fintype.card Agent : ℝ))) =
        -(eligible.card : ℝ) / 36 := by
    have hsample_real : (sampleSize : ℝ) ≠ 0 := by positivity
    have hhalf_real : (Fintype.card Agent : ℝ) =
        (sampleSize : ℝ) + sampleSize := by exact_mod_cast hhalf
    rw [hhalf_real]
    field_simp
    ring
  have htail' :
      pmfEventProbability
          (uniformFixedSizeSampleLaw sampleSize (by omega : sampleSize ≤ Fintype.card Agent))
          (fun sample =>
            (fixedSizeHitCount eligible sample.1 : ℝ) <
              (eligible.card : ℝ) / 3) ≤
        Real.exp (-(eligible.card : ℝ) / 36) := by
    have htail_raw :
        pmfEventProbability
            (uniformFixedSizeSampleLaw sampleSize
              (by omega : sampleSize ≤ Fintype.card Agent))
            (fun sample =>
              (fixedSizeHitCount eligible sample.1 : ℝ) <
                (1 - (1 / 3 : ℝ)) * (eligible.card : ℝ) *
                    (sampleSize : ℝ) / (Fintype.card Agent : ℝ)) <
          Real.exp
            (-((eligible.card : ℝ) * (sampleSize : ℝ) * (1 / 3 : ℝ) ^ 2 /
              (2 * (Fintype.card Agent : ℝ)))) := htail
    rw [hthreshold, hexponent] at htail_raw
    exact le_of_lt htail_raw
  have hcompl :
      pmfEventProbability
          (uniformFixedSizeSampleLaw sampleSize (by omega : sampleSize ≤ Fintype.card Agent))
          (fun sample =>
            (eligible.card : ℝ) / 3 ≤ fixedSizeHitCount eligible sample.1) =
        1 -
          pmfEventProbability
            (uniformFixedSizeSampleLaw sampleSize
              (by omega : sampleSize ≤ Fintype.card Agent))
            (fun sample =>
              (fixedSizeHitCount eligible sample.1 : ℝ) <
                (eligible.card : ℝ) / 3) := by
    unfold pmfEventProbability
    simpa only [not_lt] using
      (AppliedModelingLib.pmfProb_compl
        (uniformFixedSizeSampleLaw sampleSize
          (by omega : sampleSize ≤ Fintype.card Agent))
        (fun sample =>
          (fixedSizeHitCount eligible sample.1 : ℝ) <
            (eligible.card : ℝ) / 3))
  rw [hcompl]
  linarith

/-- The lower-tail bound also applies to the complementary half-sample. -/
theorem uniformFixedHalf_complement_hitCount_lt_third_probability
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (eligible : Finset Agent) (sampleSize : ℕ)
    (hsample_pos : 0 < sampleSize)
    (hhalf : Fintype.card Agent = sampleSize + sampleSize) :
    pmfEventProbability
        (uniformFixedSizeSampleLaw sampleSize (by omega : sampleSize ≤ Fintype.card Agent))
        (fun sample =>
          (fixedSizeHitCount eligible
            (fixedHalfSampleComplementEquiv sampleSize hhalf sample).1 : ℝ) <
              (eligible.card : ℝ) / 3) ≤
      Real.exp (-(eligible.card : ℝ) / 36) := by
  classical
  let law : PMF (FixedSizeSampleSpace Agent sampleSize) :=
    uniformFixedSizeSampleLaw sampleSize (by omega : sampleSize ≤ Fintype.card Agent)
  let bad : FixedSizeSampleSpace Agent sampleSize → Prop := fun sample =>
    (fixedSizeHitCount eligible sample.1 : ℝ) < (eligible.card : ℝ) / 3
  have hgood := uniformFixedHalf_hitCount_ge_third_probability
    eligible sampleSize hsample_pos hhalf
  have hcompl :
      pmfEventProbability law
          (fun sample => (eligible.card : ℝ) / 3 ≤ fixedSizeHitCount eligible sample.1) =
        1 - pmfEventProbability law bad := by
    unfold pmfEventProbability
    simpa only [bad, not_lt] using
      (AppliedModelingLib.pmfProb_compl law bad)
  have hbad : pmfEventProbability law bad ≤
      Real.exp (-(eligible.card : ℝ) / 36) := by
    change 1 - Real.exp (-(eligible.card : ℝ) / 36) ≤
      pmfEventProbability law
        (fun sample => (eligible.card : ℝ) / 3 ≤ fixedSizeHitCount eligible sample.1) at hgood
    rw [hcompl] at hgood
    linarith
  have hsymm := uniformFixedSizeSampleLaw_complement_event_probability_eq
    sampleSize hhalf bad
  change pmfEventProbability law
    (fun sample => bad (fixedHalfSampleComplementEquiv sampleSize hhalf sample)) ≤ _
  rw [hsymm]
  exact hbad

/-- The exact-half complement also satisfies the non-strict prefix tail needed
by the selected-price reduction.  The eligible-set nonemptiness hypothesis is
essential here: unlike the literal strict Lemma 6.1 event, the non-strict
zero-threshold event is certain for an empty set. -/
theorem uniformFixedHalf_complement_hitCount_le_third_probability
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (eligible : Finset Agent) (heligible : eligible.Nonempty)
    (sampleSize : ℕ) (hsample_pos : 0 < sampleSize)
    (hhalf : Fintype.card Agent = sampleSize + sampleSize) :
    pmfEventProbability
        (uniformFixedSizeSampleLaw sampleSize (by omega : sampleSize ≤ Fintype.card Agent))
        (fun sample =>
          (fixedSizeHitCount eligible
            (fixedHalfSampleComplementEquiv sampleSize hhalf sample).1 : ℝ) ≤
              (eligible.card : ℝ) / 3) ≤
      Real.exp (-(eligible.card : ℝ) / 36) := by
  classical
  have hsample_lt : sampleSize < Fintype.card Agent := by omega
  let law : PMF (FixedSizeSampleSpace Agent sampleSize) :=
    uniformFixedSizeSampleLaw sampleSize (by omega : sampleSize ≤ Fintype.card Agent)
  let bad : FixedSizeSampleSpace Agent sampleSize → Prop := fun sample =>
    (fixedSizeHitCount eligible sample.1 : ℝ) ≤ (eligible.card : ℝ) / 3
  have htail := uniformFixedSizeSampleLaw_lower_tail_le_of_nonempty
    eligible heligible hsample_pos hsample_lt
    (show (0 : ℝ) < 1 / 3 by norm_num)
    (show (1 / 3 : ℝ) ≤ 1 by norm_num)
  have hthreshold :
      (1 - (1 / 3 : ℝ)) * (eligible.card : ℝ) * (sampleSize : ℝ) /
          (Fintype.card Agent : ℝ) =
        (eligible.card : ℝ) / 3 := by
    have hsample_real : (sampleSize : ℝ) ≠ 0 := by positivity
    have hhalf_real : (Fintype.card Agent : ℝ) =
        (sampleSize : ℝ) + sampleSize := by exact_mod_cast hhalf
    rw [hhalf_real]
    field_simp
    ring
  have hexponent :
      -((eligible.card : ℝ) * (sampleSize : ℝ) * (1 / 3 : ℝ) ^ 2 /
          (2 * (Fintype.card Agent : ℝ))) =
        -(eligible.card : ℝ) / 36 := by
    have hsample_real : (sampleSize : ℝ) ≠ 0 := by positivity
    have hhalf_real : (Fintype.card Agent : ℝ) =
        (sampleSize : ℝ) + sampleSize := by exact_mod_cast hhalf
    rw [hhalf_real]
    field_simp
    ring
  have hbad : pmfEventProbability law bad ≤
      Real.exp (-(eligible.card : ℝ) / 36) := by
    have htail_raw :
        pmfEventProbability law
            (fun sample =>
              (fixedSizeHitCount eligible sample.1 : ℝ) ≤
                (1 - (1 / 3 : ℝ)) * (eligible.card : ℝ) *
                  (sampleSize : ℝ) / (Fintype.card Agent : ℝ)) <
          Real.exp
            (-((eligible.card : ℝ) * (sampleSize : ℝ) * (1 / 3 : ℝ) ^ 2 /
              (2 * (Fintype.card Agent : ℝ)))) := htail
    rw [hthreshold, hexponent] at htail_raw
    simpa [bad] using le_of_lt htail_raw
  have hsymm := uniformFixedSizeSampleLaw_complement_event_probability_eq
    sampleSize hhalf bad
  change pmfEventProbability law
    (fun sample => bad (fixedHalfSampleComplementEquiv sampleSize hhalf sample)) ≤ _
  rw [hsymm]
  exact hbad

/-- Finite PMF union bound in the paper module's probability wrapper. -/
theorem pmfEventProbability_exists_mem_le_sum
    {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω]
    (law : PMF Ω) (indices : Finset ι) (event : ι → Ω → Prop) :
    pmfEventProbability law (fun ω => ∃ i ∈ indices, event i ω) ≤
      ∑ i ∈ indices, pmfEventProbability law (event i) := by
  classical
  unfold pmfEventProbability
  exact @AppliedModelingLib.pmfProb_exists_mem_le_sum Ω ι _ _ law indices event
    (Classical.decPred _) (fun i => Classical.decPred _)

/-- Finite PMF probabilities do not depend on a computational choice of the
decidable predicate for the same mathematical event. -/
theorem pmfProb_decidable_pred_irrel
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (law : PMF Ω) (event : Ω → Prop)
    (d₁ d₂ : DecidablePred event) :
    @AppliedModelingLib.pmfProb Ω _ law event d₁ =
      @AppliedModelingLib.pmfProb Ω _ law event d₂ := by
  unfold AppliedModelingLib.pmfProb
  apply AppliedModelingLib.pmfExp_congr
  intro ω
  by_cases h : event ω <;> simp [h]

/-- Nonnegativity of the module's finite-event probability wrapper. -/
theorem pmfEventProbability_nonneg
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (law : PMF Ω) (event : Ω → Prop) :
    0 ≤ pmfEventProbability law event := by
  classical
  unfold pmfEventProbability
  exact AppliedModelingLib.pmfProb_nonneg law event

/-- For a fixed exact-half sample, sample-side winners are precisely the
fixed-size hits in the winner set. -/
theorem sideSaleCount_sampledSide_true_eq_fixedSizeHitCount_winners
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (p : ℝ) (sample : Finset Agent) :
    sideSaleCount (sampledSideAssignment sample) true values p =
      fixedSizeHitCount
        ((Finset.univ : Finset Agent).filter fun i => p ≤ values i) sample := by
  classical
  unfold sideSaleCount sampledSideAssignment fixedSizeHitCount
  congr 1
  ext i
  simp [and_comm]

/-- The source proof's first good event under the exact uniform half-sample. -/
theorem uniformFixedHalf_side_sale_sample_good_probability
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (p : ℝ)
    (sampleSize : ℕ) (hsample_pos : 0 < sampleSize)
    (hhalf : Fintype.card Agent = sampleSize + sampleSize) :
    1 - Real.exp (-(saleCount values p : ℝ) / 36) ≤
      pmfEventProbability
        (uniformFixedSizeSampleLaw sampleSize (by omega : sampleSize ≤ Fintype.card Agent))
        (fun sample =>
          saleCount values p ≤
            3 * sideSaleCount (sampledSideAssignment sample.1) true values p) := by
  classical
  let winners : Finset Agent :=
    (Finset.univ : Finset Agent).filter fun i => p ≤ values i
  have htail := uniformFixedHalf_hitCount_ge_third_probability
    winners sampleSize hsample_pos hhalf
  have htarget :
      pmfEventProbability
          (uniformFixedSizeSampleLaw sampleSize
            (by omega : sampleSize ≤ Fintype.card Agent))
          (fun sample =>
            (winners.card : ℝ) / 3 ≤ fixedSizeHitCount winners sample.1) ≤
        pmfEventProbability
          (uniformFixedSizeSampleLaw sampleSize
            (by omega : sampleSize ≤ Fintype.card Agent))
          (fun sample =>
            saleCount values p ≤
              3 * sideSaleCount (sampledSideAssignment sample.1) true values p) := by
    apply pmfEventProbability_mono
    intro sample hsample
    have hcount : saleCount values p = winners.card := by
      rfl
    have hsample_count :
        sideSaleCount (sampledSideAssignment sample.1) true values p =
          fixedSizeHitCount winners sample.1 := by
      simpa [winners] using
        sideSaleCount_sampledSide_true_eq_fixedSizeHitCount_winners
          values p sample.1
    have hreal : (winners.card : ℝ) ≤
        3 * (fixedSizeHitCount winners sample.1 : ℝ) := by
      nlinarith
    have hnat : winners.card ≤ 3 * fixedSizeHitCount winners sample.1 := by
      exact_mod_cast hreal
    simpa [hcount, hsample_count] using hnat
  simpa [winners] using le_trans htail htarget

/-- The source Section 6 random-sampling auction for a fixed partition: bids on
`sampleSide` determine the threshold and are rejected; only the opposite side
is offered that threshold. -/
noncomputable def randomSamplingOptimalThresholdAuction
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (sampleSide : Bool) (minWinners : ℕ) :
    DigitalGoodsAuction Agent where
  allocation bids i :=
    if side i = sampleSide then 0
    else if finiteCandidateOfferPrice
          (restrictBidsBySide side sampleSide bids) minWinners ≤ bids i then 1
    else 0
  payment bids i :=
    if side i = sampleSide then 0
    else if finiteCandidateOfferPrice
          (restrictBidsBySide side sampleSide bids) minWinners ≤ bids i then
      finiteCandidateOfferPrice
        (restrictBidsBySide side sampleSide bids) minWinners
    else 0

/-- Every realized directional random-sampling outcome is a source-style
binary accept/reject allocation. -/
theorem randomSamplingOptimalThresholdAuction_binaryAllocation
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (sampleSide : Bool) (minWinners : ℕ) :
    (randomSamplingOptimalThresholdAuction side sampleSide minWinners).BinaryAllocation := by
  intro bids i
  by_cases hsample : side i = sampleSide
  · simp [randomSamplingOptimalThresholdAuction, hsample]
  · by_cases hwin :
      finiteCandidateOfferPrice
          (restrictBidsBySide side sampleSide bids) minWinners ≤ bids i
    <;> simp [randomSamplingOptimalThresholdAuction, hsample, hwin]

/-- The source directional random-sampling auction is dominant-strategy
truthful: sample bidders are always rejected, and a market bidder's threshold
depends only on the sample, not on that bidder's report. -/
theorem randomSamplingOptimalThresholdAuction_truthful
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (sampleSide : Bool) (minWinners : ℕ) :
    (randomSamplingOptimalThresholdAuction side sampleSide minWinners).TruthfulDominantStrategy := by
  intro values i report
  by_cases hsample : side i = sampleSide
  · simp [DigitalGoodsAuction.utility, randomSamplingOptimalThresholdAuction,
      hsample]
  · let p : ℝ :=
      finiteCandidateOfferPrice
        (restrictBidsBySide side sampleSide values) minWinners
    have hp_update :
        finiteCandidateOfferPrice
            (restrictBidsBySide side sampleSide
              (Function.update values i report)) minWinners = p := by
      dsimp [p]
      apply congrArg (fun bids => finiteCandidateOfferPrice bids minWinners)
      exact restrictBidsBySide_update_of_not_kept
        side sampleSide values i report hsample
    have htruth_utility :
        (randomSamplingOptimalThresholdAuction side sampleSide minWinners).utility
            values i values =
          if p ≤ values i then values i - p else 0 := by
      by_cases hwin : p ≤ values i <;>
        simp [DigitalGoodsAuction.utility, randomSamplingOptimalThresholdAuction,
          hsample, p, hwin]
    have hreport_utility :
        (randomSamplingOptimalThresholdAuction side sampleSide minWinners).utility
            values i (Function.update values i report) =
          if p ≤ report then values i - p else 0 := by
      by_cases hwin : p ≤ report <;>
        simp [DigitalGoodsAuction.utility, randomSamplingOptimalThresholdAuction,
          hsample, hp_update, Function.update, hwin]
    rw [htruth_utility, hreport_utility]
    by_cases htruth : p ≤ values i <;> by_cases hreport : p ≤ report
    · simp [htruth, hreport]
    · simp [htruth, hreport]
    · simpa only [htruth, hreport, ↓reduceIte, ge_iff_le]
        using sub_nonpos.mpr (lt_of_not_ge htruth).le
    · simp [htruth, hreport]

/-- Truthful reporting in the directional random-sampling auction is
individually rational. -/
theorem randomSamplingOptimalThresholdAuction_individuallyRational
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (sampleSide : Bool) (minWinners : ℕ) :
    (randomSamplingOptimalThresholdAuction side sampleSide minWinners).IndividuallyRational := by
  intro values i
  by_cases hsample : side i = sampleSide
  · simp [DigitalGoodsAuction.utility, randomSamplingOptimalThresholdAuction,
      hsample]
  · let p : ℝ :=
      finiteCandidateOfferPrice
        (restrictBidsBySide side sampleSide values) minWinners
    by_cases hwin : p ≤ values i
    · simp [DigitalGoodsAuction.utility, randomSamplingOptimalThresholdAuction,
        hsample, p, hwin, sub_nonneg.mpr hwin]
    · simp [DigitalGoodsAuction.utility, randomSamplingOptimalThresholdAuction,
        hsample, p, hwin]

/-- The directional random-sampling auction never makes positive transfers. -/
theorem randomSamplingOptimalThresholdAuction_noPositiveTransfers
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (sampleSide : Bool) (minWinners : ℕ) :
    (randomSamplingOptimalThresholdAuction side sampleSide minWinners).NoPositiveTransfers := by
  intro bids i
  by_cases hsample : side i = sampleSide
  · simp [randomSamplingOptimalThresholdAuction, hsample]
  · let p : ℝ :=
      finiteCandidateOfferPrice
        (restrictBidsBySide side sampleSide bids) minWinners
    by_cases hwin : p ≤ bids i
    · simpa [randomSamplingOptimalThresholdAuction, hsample, p, hwin] using
        finiteCandidateOfferPrice_nonneg
          (restrictBidsBySide side sampleSide bids) minWinners
    · simp [randomSamplingOptimalThresholdAuction, hsample, p, hwin]

/-- The directional auction's revenue is exactly the market-side posted-price
revenue at the threshold selected from the sample. -/
theorem randomSamplingOptimalThresholdAuction_revenue_eq_sidePriceRevenue
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (sampleSide : Bool)
    (values : Agent → ℝ) (minWinners : ℕ) :
    (randomSamplingOptimalThresholdAuction side sampleSide minWinners).revenue
        values =
      sidePriceRevenue side (!sampleSide) values
        (finiteCandidateOfferPrice
          (restrictBidsBySide side sampleSide values) minWinners) := by
  classical
  unfold DigitalGoodsAuction.revenue randomSamplingOptimalThresholdAuction
    sidePriceRevenue
  refine Finset.sum_congr rfl ?_
  intro i _
  cases hside : side i <;> cases sampleSide <;> simp [hside]

/-- The deterministic sample/market count condition controls the sampled
benchmark directly by the revenue of the source directional auction. -/
theorem finiteCandidateBenchmark_restrictBidsBySide_le_two_directionalRevenue
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (sampleSide : Bool)
    (values : Agent → ℝ) (minWinners : ℕ)
    (hhalf :
      sideSaleCount side sampleSide values
          (finiteCandidateOfferPrice
            (restrictBidsBySide side sampleSide values) minWinners) ≤
        2 * sideSaleCount side (!sampleSide) values
          (finiteCandidateOfferPrice
            (restrictBidsBySide side sampleSide values) minWinners)) :
    finiteCandidateFixedPriceBenchmark
        (restrictBidsBySide side sampleSide values) minWinners ≤
      2 *
        (randomSamplingOptimalThresholdAuction side sampleSide minWinners).revenue
          values := by
  classical
  let p :=
    finiteCandidateOfferPrice
      (restrictBidsBySide side sampleSide values) minWinners
  have hsample_revenue :
      finiteCandidateFixedPriceBenchmark
          (restrictBidsBySide side sampleSide values) minWinners =
        singlePriceRevenue (restrictBidsBySide side sampleSide values) p := by
    rw [singlePriceRevenue_finiteCandidateOfferPrice_eq_benchmark]
  have hsample_count :
      singlePriceRevenue (restrictBidsBySide side sampleSide values) p =
        (saleCount (restrictBidsBySide side sampleSide values) p : ℝ) * p := by
    exact singlePriceRevenue_eq_saleCount_mul
      (restrictBidsBySide side sampleSide values) p
  have hp_nonneg : 0 ≤ p := by
    exact finiteCandidateOfferPrice_nonneg
      (restrictBidsBySide side sampleSide values) minWinners
  rcases hp_nonneg.eq_or_lt with hp_zero | hp_pos
  · have hbench_zero :
        finiteCandidateFixedPriceBenchmark
            (restrictBidsBySide side sampleSide values) minWinners = 0 := by
      rw [hsample_revenue, ← hp_zero]
      simp [singlePriceRevenue]
    have hmarket_nonneg : 0 ≤ sidePriceRevenue side (!sampleSide) values p := by
      unfold sidePriceRevenue
      refine Finset.sum_nonneg ?_
      intro i _
      by_cases hmarket : side i = !sampleSide ∧ p ≤ values i
      · simp [hmarket, hp_nonneg]
      · simp [hmarket]
    calc
      finiteCandidateFixedPriceBenchmark
          (restrictBidsBySide side sampleSide values) minWinners = 0 := hbench_zero
      _ ≤ 2 * sidePriceRevenue side (!sampleSide) values p := by nlinarith
      _ = 2 *
          (randomSamplingOptimalThresholdAuction side sampleSide minWinners).revenue
            values := by
          rw [randomSamplingOptimalThresholdAuction_revenue_eq_sidePriceRevenue]
  have hcount_cast :
      (saleCount (restrictBidsBySide side sampleSide values) p : ℝ) ≤
        2 * (sideSaleCount side (!sampleSide) values p : ℝ) := by
    have hside_count :
        sideSaleCount side sampleSide values p =
          saleCount (restrictBidsBySide side sampleSide values) p := by
      unfold sideSaleCount saleCount restrictBidsBySide
      congr 1
      ext i
      by_cases hsample : side i = sampleSide
      · simp [hsample]
      · have hp_not_zero : ¬ p ≤ (0 : ℝ) := not_le_of_gt hp_pos
        simp [hsample, hp_not_zero]
    rw [← hside_count]
    exact_mod_cast hhalf
  have hsample_le_market :
      singlePriceRevenue (restrictBidsBySide side sampleSide values) p ≤
        2 * sidePriceRevenue side (!sampleSide) values p := by
    rw [hsample_count, sidePriceRevenue_eq_sideSaleCount_mul]
    calc
      (saleCount (restrictBidsBySide side sampleSide values) p : ℝ) * p
          ≤ (2 * (sideSaleCount side (!sampleSide) values p : ℝ)) * p :=
            mul_le_mul_of_nonneg_right hcount_cast hp_nonneg
      _ = 2 * ((sideSaleCount side (!sampleSide) values p : ℝ) * p) := by
        ring
  calc
    finiteCandidateFixedPriceBenchmark
        (restrictBidsBySide side sampleSide values) minWinners
        = singlePriceRevenue (restrictBidsBySide side sampleSide values) p :=
          hsample_revenue
    _ ≤ 2 * sidePriceRevenue side (!sampleSide) values p := hsample_le_market
    _ = 2 *
        (randomSamplingOptimalThresholdAuction side sampleSide minWinners).revenue
          values := by
      rw [randomSamplingOptimalThresholdAuction_revenue_eq_sidePriceRevenue]

/-- The deterministic good-event implication in the form advertised by the
source directional random-sampling auction. -/
theorem theorem6_2_directional_deterministic_six_revenue_bound_of_large_sale_count
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (sampleSide : Bool)
    (values : Agent → ℝ) {minWinners : ℕ} {p : ℝ}
    (hmin : 1 ≤ minWinners)
    (hp : 0 ≤ p)
    (hlarge : 3 * minWinners ≤ saleCount values p)
    (hthird :
      saleCount values p ≤ 3 * sideSaleCount side sampleSide values p)
    (hhalf :
      sideSaleCount side sampleSide values
          (finiteCandidateOfferPrice
            (restrictBidsBySide side sampleSide values) minWinners) ≤
        2 * sideSaleCount side (!sampleSide) values
          (finiteCandidateOfferPrice
            (restrictBidsBySide side sampleSide values) minWinners)) :
    singlePriceRevenue values p ≤
      6 *
        (randomSamplingOptimalThresholdAuction side sampleSide minWinners).revenue
          values := by
  have hcount_min : minWinners ≤ sideSaleCount side sampleSide values p := by
    omega
  have hsample :
      singlePriceRevenue values p ≤
        3 * finiteCandidateFixedPriceBenchmark
          (restrictBidsBySide side sampleSide values) minWinners :=
    singlePriceRevenue_le_three_finiteCandidateBenchmark_restrictBidsBySide
      side sampleSide values hmin hp hcount_min hthird
  have hrevenue :
      finiteCandidateFixedPriceBenchmark
          (restrictBidsBySide side sampleSide values) minWinners ≤
        2 *
          (randomSamplingOptimalThresholdAuction side sampleSide minWinners).revenue
            values :=
    finiteCandidateBenchmark_restrictBidsBySide_le_two_directionalRevenue
      side sampleSide values minWinners hhalf
  calc
    singlePriceRevenue values p
        ≤ 3 * finiteCandidateFixedPriceBenchmark
          (restrictBidsBySide side sampleSide values) minWinners := hsample
    _ ≤ 3 *
          (2 *
            (randomSamplingOptimalThresholdAuction side sampleSide minWinners).revenue
              values) := by
        exact mul_le_mul_of_nonneg_left hrevenue (by norm_num)
    _ = 6 *
          (randomSamplingOptimalThresholdAuction side sampleSide minWinners).revenue
            values := by ring

/-- Exact-half selected-price bad-event bound.  This is the fixed-cardinality
version of the source proof's top-prefix union step; the `a >= 3` condition is
used only to ensure that every selected prefix is nonempty before invoking the
non-strict support tail bound. -/
theorem theorem6_2_directional_fixed_half_selected_price_bad_large_sample_top_prefix_le_exp
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (sampleSize : ℕ)
    (hsample_pos : 0 < sampleSize)
    (hhalf : Fintype.card Agent = sampleSize + sampleSize)
    (minWinners a : ℕ) (top : TopPrefixFamily values)
    (ha_ge_three : 3 ≤ a) (ha_card : a ≤ Fintype.card Agent) :
    pmfEventProbability
        (uniformFixedSizeSampleLaw sampleSize
          (by omega : sampleSize ≤ Fintype.card Agent))
        (fun sample =>
          a ≤
            3 * sideSaleCount (sampledSideAssignment sample.1) true values
              (finiteCandidateOfferPrice
                (restrictBidsBySide (sampledSideAssignment sample.1) true values)
                minWinners) ∧
          ¬ sideSaleCount (sampledSideAssignment sample.1) true values
                (finiteCandidateOfferPrice
                  (restrictBidsBySide (sampledSideAssignment sample.1) true values)
                  minWinners) ≤
              2 * sideSaleCount (sampledSideAssignment sample.1) false values
                (finiteCandidateOfferPrice
                  (restrictBidsBySide (sampledSideAssignment sample.1) true values)
                  minWinners)) ≤
      40 * Real.exp (-(a : ℝ) / 72) := by
  classical
  let law : PMF (FixedSizeSampleSpace Agent sampleSize) :=
    uniformFixedSizeSampleLaw sampleSize
      (by omega : sampleSize ≤ Fintype.card Agent)
  let badLarge : FixedSizeSampleSpace Agent sampleSize → Prop := fun sample =>
    a ≤
      3 * sideSaleCount (sampledSideAssignment sample.1) true values
        (finiteCandidateOfferPrice
          (restrictBidsBySide (sampledSideAssignment sample.1) true values)
          minWinners) ∧
    ¬ sideSaleCount (sampledSideAssignment sample.1) true values
          (finiteCandidateOfferPrice
            (restrictBidsBySide (sampledSideAssignment sample.1) true values)
            minWinners) ≤
        2 * sideSaleCount (sampledSideAssignment sample.1) false values
          (finiteCandidateOfferPrice
            (restrictBidsBySide (sampledSideAssignment sample.1) true values)
            minWinners)
  let indices : Finset ℕ := Finset.Icc (a / 2) (Fintype.card Agent)
  let prefixBad : ℕ → FixedSizeSampleSpace Agent sampleSize → Prop :=
    fun m sample =>
      (sideCountInSet (sampledSideAssignment sample.1) false (top.top m) : ℝ) ≤
        ((top.top m).card : ℝ) / 3
  have hsubset :
      ∀ sample, badLarge sample →
        ∃ m ∈ indices, prefixBad m sample := by
    intro sample hbad
    simpa [badLarge, indices, prefixBad] using
      (paper_aux_theorem6_2_selected_price_bad_large_sample_subset_top_prefix_union
        values true minWinners a top ha_card hbad)
  have hbad_le_union :
      pmfEventProbability law badLarge ≤
        pmfEventProbability law
          (fun sample => ∃ m ∈ indices, prefixBad m sample) := by
    exact pmfEventProbability_mono law badLarge _ hsubset
  have hunion :
      pmfEventProbability law
          (fun sample => ∃ m ∈ indices, prefixBad m sample) ≤
        ∑ m ∈ indices, pmfEventProbability law (prefixBad m) :=
    pmfEventProbability_exists_mem_le_sum law indices prefixBad
  have hterms :
      (∑ m ∈ indices, pmfEventProbability law (prefixBad m)) ≤
        ∑ m ∈ indices, Real.exp (-(m : ℝ) / 36) := by
    refine Finset.sum_le_sum ?_
    intro m hm
    have hm_lower : a / 2 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm_upper : m ≤ Fintype.card Agent := (Finset.mem_Icc.mp hm).2
    have ha_half_pos : 0 < a / 2 := by omega
    have hm_pos : 0 < m := lt_of_lt_of_le ha_half_pos hm_lower
    have htop_card : (top.top m).card = m := top.card_top hm_upper
    have htop_nonempty : (top.top m).Nonempty :=
      Finset.card_pos.mp (by simpa [htop_card] using hm_pos)
    have htail := uniformFixedHalf_complement_hitCount_le_third_probability
      (top.top m) htop_nonempty sampleSize hsample_pos hhalf
    have hpref :
        pmfEventProbability law (prefixBad m) =
          pmfEventProbability law
            (fun sample =>
              (fixedSizeHitCount (top.top m)
                (fixedHalfSampleComplementEquiv sampleSize hhalf sample).1 : ℝ) ≤
                  ((top.top m).card : ℝ) / 3) := by
      congr 1
      funext sample
      simp only [prefixBad]
      rw [sideCountInSet_sampledSide_false_eq_complement_hitCount]
      rw [← fixedHalfSampleComplementEquiv_val]
    calc
      pmfEventProbability law (prefixBad m)
          = pmfEventProbability law
              (fun sample =>
                (fixedSizeHitCount (top.top m)
                  (fixedHalfSampleComplementEquiv sampleSize hhalf sample).1 : ℝ) ≤
                    ((top.top m).card : ℝ) / 3) := hpref
      _ ≤ Real.exp (-((top.top m).card : ℝ) / 36) := by
            simpa [law] using htail
      _ = Real.exp (-(m : ℝ) / 36) := by rw [htop_card]
  have hsum :
      (∑ m ∈ indices, Real.exp (-(m : ℝ) / 36)) ≤
        40 * Real.exp (-(a : ℝ) / 72) := by
    simpa [indices] using
      (paper_aux_theorem6_2_top_prefix_exp_sum_le_forty
        a (Fintype.card Agent))
  change pmfEventProbability law badLarge ≤ _
  exact le_trans hbad_le_union (le_trans hunion (le_trans hterms hsum))

/-- The source directional auction's fixed-half revenue guarantee once the
sample-selected price is known to have enough sample-side acceptors. -/
theorem theorem6_2_directional_fixed_half_revenue_bound_top_prefix_of_selected_large
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (sampleSize : ℕ)
    (hsample_pos : 0 < sampleSize)
    (hhalf : Fintype.card Agent = sampleSize + sampleSize)
    {minWinners a : ℕ} {p : ℝ} (top : TopPrefixFamily values)
    (hmin : 1 ≤ minWinners)
    (hp : 0 ≤ p)
    (hminWinners_alpha : 3 * minWinners ≤ a)
    (ha_sale : a ≤ saleCount values p)
    (hselected_large :
      ∀ sample : FixedSizeSampleSpace Agent sampleSize,
        saleCount values p ≤
            3 * sideSaleCount (sampledSideAssignment sample.1) true values p →
          a ≤
            3 * sideSaleCount (sampledSideAssignment sample.1) true values
              (finiteCandidateOfferPrice
                (restrictBidsBySide (sampledSideAssignment sample.1) true values)
                minWinners)) :
    1 - Real.exp (-(a : ℝ) / 36) -
        40 * Real.exp (-(a : ℝ) / 72) ≤
      pmfEventProbability
        (uniformFixedSizeSampleLaw sampleSize
          (by omega : sampleSize ≤ Fintype.card Agent))
        (fun sample =>
          singlePriceRevenue values p ≤
            6 *
              (randomSamplingOptimalThresholdAuction
                (sampledSideAssignment sample.1) true minWinners).revenue values) := by
  classical
  let law : PMF (FixedSizeSampleSpace Agent sampleSize) :=
    uniformFixedSizeSampleLaw sampleSize
      (by omega : sampleSize ≤ Fintype.card Agent)
  let sampleGood : FixedSizeSampleSpace Agent sampleSize → Prop := fun sample =>
    saleCount values p ≤
      3 * sideSaleCount (sampledSideAssignment sample.1) true values p
  let badLarge : FixedSizeSampleSpace Agent sampleSize → Prop := fun sample =>
    a ≤
      3 * sideSaleCount (sampledSideAssignment sample.1) true values
        (finiteCandidateOfferPrice
          (restrictBidsBySide (sampledSideAssignment sample.1) true values)
          minWinners) ∧
    ¬ sideSaleCount (sampledSideAssignment sample.1) true values
          (finiteCandidateOfferPrice
            (restrictBidsBySide (sampledSideAssignment sample.1) true values)
            minWinners) ≤
        2 * sideSaleCount (sampledSideAssignment sample.1) false values
          (finiteCandidateOfferPrice
            (restrictBidsBySide (sampledSideAssignment sample.1) true values)
            minWinners)
  let target : FixedSizeSampleSpace Agent sampleSize → Prop := fun sample =>
    singlePriceRevenue values p ≤
      6 *
        (randomSamplingOptimalThresholdAuction
          (sampledSideAssignment sample.1) true minWinners).revenue values
  have hsample_sale :
      1 - Real.exp (-(saleCount values p : ℝ) / 36) ≤
        pmfEventProbability law sampleGood := by
    simpa [law, sampleGood] using
      (uniformFixedHalf_side_sale_sample_good_probability
        values p sampleSize hsample_pos hhalf)
  have harg_sample :
      -(saleCount values p : ℝ) / 36 ≤ -(a : ℝ) / 36 := by
    have ha_real : (a : ℝ) ≤ saleCount values p := by
      exact_mod_cast ha_sale
    nlinarith
  have hexp_sample :
      Real.exp (-(saleCount values p : ℝ) / 36) ≤
        Real.exp (-(a : ℝ) / 36) :=
    Real.exp_le_exp.mpr harg_sample
  have hsample :
      1 - Real.exp (-(a : ℝ) / 36) ≤ pmfEventProbability law sampleGood := by
    have hleft :
        1 - Real.exp (-(a : ℝ) / 36) ≤
          1 - Real.exp (-(saleCount values p : ℝ) / 36) := by
      linarith
    exact le_trans hleft hsample_sale
  have ha_card : a ≤ Fintype.card Agent :=
    le_trans ha_sale (saleCount_le_card values p)
  have ha_ge_three : 3 ≤ a := by omega
  have hbad_le :
      pmfEventProbability law badLarge ≤
        40 * Real.exp (-(a : ℝ) / 72) := by
    simpa [law, badLarge] using
      (theorem6_2_directional_fixed_half_selected_price_bad_large_sample_top_prefix_le_exp
        values sampleSize hsample_pos hhalf minWinners a top ha_ge_three ha_card)
  have hbad_compl :
      pmfEventProbability law (fun sample => ¬ badLarge sample) =
        1 - pmfEventProbability law badLarge := by
    have hraw := @AppliedModelingLib.pmfProb_compl _ _ _ law badLarge
      (Classical.decPred badLarge)
    unfold pmfEventProbability
    calc
      @AppliedModelingLib.pmfProb _ _ law (fun sample => ¬ badLarge sample)
          (Classical.decPred _) = _ :=
        pmfProb_decidable_pred_irrel law _ _ _
      _ = 1 - @AppliedModelingLib.pmfProb _ _ law badLarge
          (Classical.decPred _) := hraw
  have hnot_bad :
      1 - 40 * Real.exp (-(a : ℝ) / 72) ≤
        pmfEventProbability law (fun sample => ¬ badLarge sample) := by
    rw [hbad_compl]
    linarith
  have hlarge : 3 * minWinners ≤ saleCount values p :=
    le_trans hminWinners_alpha ha_sale
  have hcombined :
      1 - Real.exp (-(a : ℝ) / 36) -
          40 * Real.exp (-(a : ℝ) / 72) ≤
        pmfEventProbability law target := by
    change 1 - Real.exp (-(a : ℝ) / 36) -
          40 * Real.exp (-(a : ℝ) / 72) ≤
        @AppliedModelingLib.pmfProb _ _ law target (Classical.decPred target)
    exact @paper_theorem6_2_random_sampling_union_bound _ _ _ law sampleGood
      (fun sample => ¬ badLarge sample) target
      (Classical.decPred sampleGood)
      (Classical.decPred (fun sample => ¬ badLarge sample))
      (Classical.decPred target)
      _ _ hsample hnot_bad
      (by
        intro sample hsample_side hnot_bad_side
        have hselected_count :
            a ≤
              3 * sideSaleCount (sampledSideAssignment sample.1) true values
                (finiteCandidateOfferPrice
                  (restrictBidsBySide (sampledSideAssignment sample.1) true values)
                  minWinners) :=
          hselected_large sample hsample_side
        have hrevenue_good :
            sideSaleCount (sampledSideAssignment sample.1) true values
                (finiteCandidateOfferPrice
                  (restrictBidsBySide (sampledSideAssignment sample.1) true values)
                  minWinners) ≤
              2 * sideSaleCount (sampledSideAssignment sample.1) false values
                (finiteCandidateOfferPrice
                  (restrictBidsBySide (sampledSideAssignment sample.1) true values)
                  minWinners) := by
          by_contra hbad
          exact hnot_bad_side ⟨hselected_count, hbad⟩
        exact
          theorem6_2_directional_deterministic_six_revenue_bound_of_large_sale_count
            (sampledSideAssignment sample.1) true values hmin hp hlarge
            hsample_side hrevenue_good)
  simpa [law, target] using hcombined

/-- The existing Section 6 concentration and top-prefix estimates imply the
source directional auction's fair-coin guarantee once its sample-selected price
has enough sample-side acceptors. -/
theorem theorem6_2_directional_fair_coin_revenue_bound_top_prefix_of_selected_large
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (keep : Bool) {minWinners a : ℕ} {p : ℝ}
    (top : TopPrefixFamily values)
    (hmin : 1 ≤ minWinners)
    (hp : 0 ≤ p)
    (hminWinners_alpha : 3 * minWinners ≤ a)
    (ha_sale : a ≤ saleCount values p)
    (hselected_large :
      ∀ side : Agent → Bool,
        saleCount values p ≤ 3 * sideSaleCount side keep values p →
          a ≤
            3 * sideSaleCount side keep values
              (finiteCandidateOfferPrice
                (restrictBidsBySide side keep values) minWinners)) :
    1 - Real.exp (-(a : ℝ) / 36) -
        40 * Real.exp (-(a : ℝ) / 72) ≤
      (FairCoin.productMeasure Agent).real
        {side |
          singlePriceRevenue values p ≤
            6 *
              (randomSamplingOptimalThresholdAuction side keep minWinners).revenue
                values} := by
  classical
  let μ : Measure (Agent → Bool) := FairCoin.productMeasure Agent
  haveI : IsProbabilityMeasure μ :=
    FairCoin.productMeasure_isProbabilityMeasure Agent
  let sampleGood : Set (Agent → Bool) :=
    {side | saleCount values p ≤ 3 * sideSaleCount side keep values p}
  let badLarge : Set (Agent → Bool) :=
    {side : Agent → Bool |
      a ≤
        3 * sideSaleCount side keep values
          (finiteCandidateOfferPrice
            (restrictBidsBySide side keep values) minWinners) ∧
      ¬ sideSaleCount side keep values
          (finiteCandidateOfferPrice
            (restrictBidsBySide side keep values) minWinners) ≤
        2 * sideSaleCount side (!keep) values
          (finiteCandidateOfferPrice
            (restrictBidsBySide side keep values) minWinners)}
  let target : Set (Agent → Bool) :=
    {side |
      singlePriceRevenue values p ≤
        6 *
          (randomSamplingOptimalThresholdAuction side keep minWinners).revenue
            values}
  have hsample_sale :
      1 - Real.exp (-(saleCount values p : ℝ) / 36) ≤
        μ.real sampleGood := by
    simpa [μ, sampleGood] using
      paper_aux_theorem6_2_side_sale_sample_good_probability values p keep
  have harg_sample :
      -(saleCount values p : ℝ) / 36 ≤ -(a : ℝ) / 36 := by
    have ha_real : (a : ℝ) ≤ saleCount values p := by
      exact_mod_cast ha_sale
    nlinarith
  have hexp_sample :
      Real.exp (-(saleCount values p : ℝ) / 36) ≤
        Real.exp (-(a : ℝ) / 36) :=
    Real.exp_le_exp.mpr harg_sample
  have hsample :
      1 - Real.exp (-(a : ℝ) / 36) ≤ μ.real sampleGood := by
    have hleft :
        1 - Real.exp (-(a : ℝ) / 36) ≤
          1 - Real.exp (-(saleCount values p : ℝ) / 36) := by
      linarith
    exact le_trans hleft hsample_sale
  have ha_card : a ≤ Fintype.card Agent :=
    le_trans ha_sale (saleCount_le_card values p)
  have hbad_le :
      μ.real badLarge ≤ 40 * Real.exp (-(a : ℝ) / 72) := by
    simpa [μ, badLarge] using
      paper_aux_theorem6_2_selected_price_bad_large_sample_top_prefix_le_exp
        values keep minWinners a top ha_card
  have hbad_meas : MeasurableSet badLarge :=
    (Set.toFinite badLarge).measurableSet
  have hnot_bad_meas : MeasurableSet badLargeᶜ :=
    (Set.toFinite badLargeᶜ).measurableSet
  have hbad_compl :
      μ.real badLargeᶜ = 1 - μ.real badLarge :=
    probReal_compl_eq_one_sub (μ := μ) hbad_meas
  have hnot_bad :
      1 - 40 * Real.exp (-(a : ℝ) / 72) ≤ μ.real badLargeᶜ := by
    rw [hbad_compl]
    linarith
  have hsample_meas : MeasurableSet sampleGood :=
    (Set.toFinite sampleGood).measurableSet
  have hlarge : 3 * minWinners ≤ saleCount values p :=
    le_trans hminWinners_alpha ha_sale
  have hcombined :
      1 - Real.exp (-(a : ℝ) / 36) -
          40 * Real.exp (-(a : ℝ) / 72) ≤ μ.real target :=
    paper_theorem6_2_random_sampling_measure_union_bound
      (μ := μ) sampleGood badLargeᶜ target
      hsample_meas hnot_bad_meas hsample hnot_bad
      (by
        intro side hside
        rcases hside with ⟨hsample_side, hnot_bad_side⟩
        have hselected_count :
            a ≤
              3 * sideSaleCount side keep values
                (finiteCandidateOfferPrice
                  (restrictBidsBySide side keep values) minWinners) :=
          hselected_large side hsample_side
        have hrevenue_good :
            sideSaleCount side keep values
                (finiteCandidateOfferPrice
                  (restrictBidsBySide side keep values) minWinners) ≤
              2 * sideSaleCount side (!keep) values
                (finiteCandidateOfferPrice
                  (restrictBidsBySide side keep values) minWinners) := by
          by_contra hbad
          exact hnot_bad_side ⟨hselected_count, hbad⟩
        exact
          theorem6_2_directional_deterministic_six_revenue_bound_of_large_sale_count
            side keep values hmin hp hlarge hsample_side hrevenue_good)
  simpa [μ, target] using hcombined

/-- Ranked finite-bid form of the alpha/high-value Section 6 source guarantee.
The top-prefix family is constructed from bidder values, so no sorted-index
convention is imposed. -/
theorem theorem6_2_directional_fair_coin_revenue_bound_top_prefix_alpha_h_fin_ranked
    {n : ℕ} [NeZero n] (values : Fin n → ℝ) (keep : Bool)
    {minWinners a : ℕ} {p h : ℝ}
    (hmin : 1 ≤ minWinners)
    (hp : 0 ≤ p)
    (hh_pos : 0 < h)
    (hminWinners_alpha : 3 * minWinners ≤ a)
    (hvalue_bound : ∀ i, values i ≤ h)
    (halpha_h : (a : ℝ) * h ≤ singlePriceRevenue values p) :
    1 - Real.exp (-(a : ℝ) / 36) -
        40 * Real.exp (-(a : ℝ) / 72) ≤
      (FairCoin.productMeasure (Fin n)).real
        {side |
          singlePriceRevenue values p ≤
            6 *
              (randomSamplingOptimalThresholdAuction side keep minWinners).revenue
                values} := by
  have hfixed_le_count_h :
      singlePriceRevenue values p ≤ (saleCount values p : ℝ) * h :=
    singlePriceRevenue_le_saleCount_mul_bound values hp hvalue_bound
  have ha_sale : a ≤ saleCount values p := by
    have ha_real : (a : ℝ) ≤ saleCount values p := by
      have hmul :
          (a : ℝ) * h ≤ (saleCount values p : ℝ) * h :=
        le_trans halpha_h hfixed_le_count_h
      exact (mul_le_mul_iff_of_pos_right hh_pos).mp hmul
    exact_mod_cast ha_real
  exact
    theorem6_2_directional_fair_coin_revenue_bound_top_prefix_of_selected_large
      (values := values) (keep := keep) (minWinners := minWinners)
      (a := a) (p := p) (rankedTopPrefixFamily values)
      hmin hp hminWinners_alpha ha_sale
      (fun side hthird =>
        paper_aux_theorem6_2_selected_offer_large_sample_count_of_alpha_h
          side keep values hmin hp hh_pos hminWinners_alpha ha_sale
          hvalue_bound halpha_h hthird)

/-- GHW Theorem 6.2 for the source directional auction, in the ranked finite
candidate fixed-price benchmark model and with the nonvacuous large-market
condition made explicit. -/
theorem theorem6_2_directional_fair_coin_revenue_bound_of_finite_candidate_benchmark_ranked
    {n : ℕ} [NeZero n] (values : Fin n → ℝ) (keep : Bool)
    {alpha : ℕ} {highValue : ℝ}
    (hhigh_pos : 0 < highValue)
    (hvalue_bound : ∀ i, values i ≤ highValue)
    (halpha_ge_three : 3 ≤ alpha)
    (halpha_highValue :
      (alpha : ℝ) * highValue ≤
        finiteCandidateFixedPriceBenchmark values 1) :
    1 - Real.exp (-(alpha : ℝ) / 36) -
        40 * Real.exp (-(alpha : ℝ) / 72) ≤
      (FairCoin.productMeasure (Fin n)).real
        {side |
          finiteCandidateFixedPriceBenchmark values 1 ≤
            6 *
              (randomSamplingOptimalThresholdAuction side keep 1).revenue values} := by
  simpa [singlePriceRevenue_finiteCandidateOfferPrice_eq_benchmark] using
    theorem6_2_directional_fair_coin_revenue_bound_top_prefix_alpha_h_fin_ranked
      (values := values) (keep := keep) (minWinners := 1)
      (a := alpha) (p := finiteCandidateOfferPrice values 1)
      (h := highValue) (by simp)
      (finiteCandidateOfferPrice_nonneg values 1) hhigh_pos
      (by simpa using halpha_ge_three) hvalue_bound
      (by
        simpa [singlePriceRevenue_finiteCandidateOfferPrice_eq_benchmark] using
          halpha_highValue)

/-- GHW Theorem 6.2 directional fair-coin guarantee without a separate
large-`alpha` premise. For small `alpha`, the displayed probability lower bound
is nonpositive. -/
theorem theorem6_2_directional_fair_coin_revenue_bound_of_finite_candidate_benchmark_all_alpha
    {n : ℕ} [NeZero n] (values : Fin n → ℝ) (keep : Bool)
    {alpha : ℕ} {highValue : ℝ}
    (hhigh_pos : 0 < highValue)
    (hvalue_bound : ∀ i, values i ≤ highValue)
    (halpha_highValue :
      (alpha : ℝ) * highValue ≤
        finiteCandidateFixedPriceBenchmark values 1) :
    1 - Real.exp (-(alpha : ℝ) / 36) -
        40 * Real.exp (-(alpha : ℝ) / 72) ≤
      (FairCoin.productMeasure (Fin n)).real
        {side |
          finiteCandidateFixedPriceBenchmark values 1 ≤
            6 *
              (randomSamplingOptimalThresholdAuction side keep 1).revenue values} := by
  by_cases halpha_ge_three : 3 ≤ alpha
  · exact
      theorem6_2_directional_fair_coin_revenue_bound_of_finite_candidate_benchmark_ranked
        values keep hhigh_pos hvalue_bound halpha_ge_three halpha_highValue
  · have halpha_lt_three : alpha < 3 := Nat.lt_of_not_ge halpha_ge_three
    exact le_trans
      (paper_theorem6_2_probability_bound_nonpos_of_alpha_lt_three
        halpha_lt_three)
      (by positivity)

/-! The printed real-parameter endpoint.  The probability argument is still
indexed by the natural count `⌈alpha⌉`, but the source scale condition is
used before that integerization through the real selected-offer bridge. -/
theorem theorem6_2_directional_fair_coin_revenue_bound_of_finite_candidate_benchmark_real_alpha
    {n : ℕ} [NeZero n] (values : Fin n → ℝ) (keep : Bool)
    {alpha highValue : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (hhigh_pos : 0 < highValue)
    (hvalue_bound : ∀ i, values i ≤ highValue)
    (halpha_highValue : alpha * highValue ≤
      finiteCandidateFixedPriceBenchmark values 1) :
    1 - Real.exp (-alpha / 36) - 40 * Real.exp (-alpha / 72) ≤
      (FairCoin.productMeasure (Fin n)).real
        {side |
          finiteCandidateFixedPriceBenchmark values 1 ≤
            6 * (randomSamplingOptimalThresholdAuction side keep 1).revenue values} := by
  let f : ℝ → ℝ := fun x =>
    1 - Real.exp (-x / 36) - 40 * Real.exp (-x / 72)
  have hmono : ∀ {x y : ℝ}, x ≤ y → f x ≤ f y := by
    intro x y hxy
    dsimp [f]
    have h36 : Real.exp (-y / 36) ≤ Real.exp (-x / 36) := by
      apply Real.exp_le_exp.mpr
      linarith
    have h72 : Real.exp (-y / 72) ≤ Real.exp (-x / 72) := by
      apply Real.exp_le_exp.mpr
      linarith
    linarith
  by_cases halpha_le_two : alpha ≤ 2
  · have htwo : f (2 : ℝ) ≤ 0 := by
      have htwo_nat :=
        paper_theorem6_2_probability_bound_nonpos_of_alpha_lt_three
          (alpha := 2) (by omega)
      simpa [f] using htwo_nat
    have hbound : f alpha ≤ 0 := hmono halpha_le_two |>.trans htwo
    exact hbound.trans (by positivity)
  · have halpha_gt_two : 2 < alpha := lt_of_not_ge halpha_le_two
    let a : ℕ := Nat.ceil alpha
    have halpha_le_a : alpha ≤ (a : ℝ) := by
      simpa [a] using Nat.le_ceil alpha
    have ha_ge_three : 3 ≤ a := by
      by_contra hnot
      have ha_le_two : a ≤ 2 := by omega
      have : alpha ≤ 2 := le_trans halpha_le_a (by exact_mod_cast ha_le_two)
      linarith
    have hfixed_le_count_h :
        finiteCandidateFixedPriceBenchmark values 1 ≤
          (saleCount values (finiteCandidateOfferPrice values 1) : ℝ) * highValue := by
      simpa [singlePriceRevenue_finiteCandidateOfferPrice_eq_benchmark] using
        singlePriceRevenue_le_saleCount_mul_bound values
          (finiteCandidateOfferPrice_nonneg values 1) hvalue_bound
    have halpha_sale_real :
        alpha ≤ saleCount values (finiteCandidateOfferPrice values 1) := by
      have hmul : alpha * highValue ≤
          (saleCount values (finiteCandidateOfferPrice values 1) : ℝ) * highValue :=
        le_trans halpha_highValue hfixed_le_count_h
      exact (mul_le_mul_iff_of_pos_right hhigh_pos).mp hmul
    have ha_sale : a ≤ saleCount values (finiteCandidateOfferPrice values 1) := by
      apply Nat.ceil_le.mpr
      exact halpha_sale_real
    have hlarge_real : (3 : ℝ) ≤
        saleCount values (finiteCandidateOfferPrice values 1) := by
      have ha_real : (a : ℝ) ≤ saleCount values (finiteCandidateOfferPrice values 1) := by
        exact_mod_cast ha_sale
      have ha_three : (3 : ℝ) ≤ a := by exact_mod_cast ha_ge_three
      linarith
    have hreal_result :=
      theorem6_2_directional_fair_coin_revenue_bound_top_prefix_of_selected_large
        (values := values) (keep := keep) (minWinners := 1)
        (a := a) (p := finiteCandidateOfferPrice values 1)
        (rankedTopPrefixFamily values) (by simp)
        (finiteCandidateOfferPrice_nonneg values 1) (by simpa using ha_ge_three)
        ha_sale
        (fun side hthird => by
          have hreal :=
            paper_aux_theorem6_2_selected_offer_large_sample_count_of_real_alpha_h
              side keep values (minWinners := 1)
              (p := finiteCandidateOfferPrice values 1) (h := highValue)
              (by simp) (finiteCandidateOfferPrice_nonneg values 1) hhigh_pos
              halpha_sale_real (by simpa using hlarge_real) hvalue_bound
              (by simpa [singlePriceRevenue_finiteCandidateOfferPrice_eq_benchmark] using
                halpha_highValue) hthird
          exact Nat.ceil_le.mpr (by simpa [Nat.cast_mul] using hreal))
    have hfinal : f alpha ≤ f (a : ℝ) := hmono halpha_le_a
    exact hfinal.trans (by simpa [f, a,
      singlePriceRevenue_finiteCandidateOfferPrice_eq_benchmark] using hreal_result)

/-- Real-`alpha` bridge under an explicit integer majorant.  The finite tail
argument is indexed by a natural winner count, so this theorem separates the
source-level real parameter from that discrete proof index.  The majorant
condition is stronger than the printed `alpha * h ≤ F` premise and is exposed
rather than hidden behind a rounding convention. -/
theorem theorem6_2_directional_fair_coin_revenue_bound_of_finite_candidate_benchmark_real_alpha_of_integer_majorant
    {n : ℕ} [NeZero n] (values : Fin n → ℝ) (keep : Bool)
    {alpha : ℝ} {a : ℕ} {highValue : ℝ}
    (hhigh_pos : 0 < highValue)
    (hvalue_bound : ∀ i, values i ≤ highValue)
    (halpha_le_a : alpha ≤ a)
    (ha_highValue : (a : ℝ) * highValue ≤
      finiteCandidateFixedPriceBenchmark values 1) :
    1 - Real.exp (-alpha / 36) - 40 * Real.exp (-alpha / 72) ≤
      (FairCoin.productMeasure (Fin n)).real
        {side |
          finiteCandidateFixedPriceBenchmark values 1 ≤
            6 *
              (randomSamplingOptimalThresholdAuction side keep 1).revenue values} := by
  have ha_bound :=
    theorem6_2_directional_fair_coin_revenue_bound_of_finite_candidate_benchmark_all_alpha
      (values := values) (keep := keep) (alpha := a) (highValue := highValue)
      hhigh_pos hvalue_bound ha_highValue
  have harg36 : -(a : ℝ) / 36 ≤ -alpha / 36 := by linarith
  have harg72 : -(a : ℝ) / 72 ≤ -alpha / 72 := by linarith
  have hexp36 : Real.exp (-(a : ℝ) / 36) ≤ Real.exp (-alpha / 36) :=
    Real.exp_le_exp.mpr harg36
  have hexp72 : Real.exp (-(a : ℝ) / 72) ≤ Real.exp (-alpha / 72) :=
    Real.exp_le_exp.mpr harg72
  have hbound :
      1 - Real.exp (-alpha / 36) - 40 * Real.exp (-alpha / 72) ≤
        1 - Real.exp (-(a : ℝ) / 36) - 40 * Real.exp (-(a : ℝ) / 72) := by
    linarith
  exact le_trans hbound ha_bound

/-! A source-premise-compatible real-parameter variant.  The discrete proof
can always use `⌊alpha⌋`; this keeps the printed benchmark premise but makes
the unavoidable loss in the exponent explicit rather than silently coercing a
real threshold to a natural number. -/

theorem theorem6_2_directional_fair_coin_revenue_bound_of_finite_candidate_benchmark_real_alpha_floor
    {n : ℕ} [NeZero n] (values : Fin n → ℝ) (keep : Bool)
    {alpha : ℝ} {highValue : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (hhigh_pos : 0 < highValue)
    (hvalue_bound : ∀ i, values i ≤ highValue)
    (halpha_highValue : alpha * highValue ≤
      finiteCandidateFixedPriceBenchmark values 1) :
    1 - Real.exp (-(Nat.floor alpha : ℝ) / 36) -
        40 * Real.exp (-(Nat.floor alpha : ℝ) / 72) ≤
      (FairCoin.productMeasure (Fin n)).real
        {side |
          finiteCandidateFixedPriceBenchmark values 1 ≤
            6 *
              (randomSamplingOptimalThresholdAuction side keep 1).revenue values} := by
  let a : ℕ := Nat.floor alpha
  have ha_le : (a : ℝ) ≤ alpha := by
    simpa [a] using (Nat.floor_le halpha_nonneg)
  have ha_highValue : (a : ℝ) * highValue ≤
      finiteCandidateFixedPriceBenchmark values 1 := by
    exact (mul_le_mul_of_nonneg_right ha_le (le_of_lt hhigh_pos)).trans
      halpha_highValue
  simpa [a] using
    (theorem6_2_directional_fair_coin_revenue_bound_of_finite_candidate_benchmark_all_alpha
      (values := values) (keep := keep) (alpha := a) (highValue := highValue)
      hhigh_pos hvalue_bound ha_highValue)

/-- Recover the source's printed real-`alpha` exponent under the transparent
ceiling-majorant repair.  The extra premise is exactly what lets the
integer-indexed tail proof use `ceil alpha` without weakening the exponent. -/
theorem theorem6_2_directional_fair_coin_revenue_bound_of_finite_candidate_benchmark_real_alpha_of_ceiling_majorant
    {n : ℕ} [NeZero n] (values : Fin n → ℝ) (keep : Bool)
    {alpha : ℝ} {highValue : ℝ}
    (hhigh_pos : 0 < highValue)
    (hvalue_bound : ∀ i, values i ≤ highValue)
    (hceil_highValue : (Nat.ceil alpha : ℝ) * highValue ≤
      finiteCandidateFixedPriceBenchmark values 1) :
    1 - Real.exp (-alpha / 36) - 40 * Real.exp (-alpha / 72) ≤
      (FairCoin.productMeasure (Fin n)).real
    {side |
          finiteCandidateFixedPriceBenchmark values 1 ≤
            6 *
              (randomSamplingOptimalThresholdAuction side keep 1).revenue values} := by
  have hmajorant : ∃ a : ℕ, alpha ≤ (a : ℝ) ∧
      (a : ℝ) * highValue ≤ finiteCandidateFixedPriceBenchmark values 1 :=
    (AppliedModelingLib.FiniteRounding.exists_nat_majorant_mul_le_iff
      (hscale := le_of_lt hhigh_pos)).2 hceil_highValue
  rcases hmajorant with ⟨a, ha, ha_budget⟩
  exact
    theorem6_2_directional_fair_coin_revenue_bound_of_finite_candidate_benchmark_real_alpha_of_integer_majorant
      (values := values) (keep := keep) (alpha := alpha) (a := a)
      (highValue := highValue) hhigh_pos hvalue_bound ha ha_budget

/-- Ranked finite-bid exact-half form of the alpha/high-value directional
guarantee.  `a` remains a natural number deliberately: this is the current
visible discrete-alpha convention, not an implicit rounding of a real source
parameter. -/
theorem theorem6_2_directional_fixed_half_revenue_bound_top_prefix_alpha_h_fin_ranked
    {n : ℕ} [NeZero n] (values : Fin n → ℝ)
    (sampleSize : ℕ) (hsample_pos : 0 < sampleSize)
    (hhalf : n = sampleSize + sampleSize)
    {minWinners a : ℕ} {p h : ℝ}
    (hmin : 1 ≤ minWinners)
    (hp : 0 ≤ p)
    (hh_pos : 0 < h)
    (hminWinners_alpha : 3 * minWinners ≤ a)
    (hvalue_bound : ∀ i, values i ≤ h)
    (halpha_h : (a : ℝ) * h ≤ singlePriceRevenue values p) :
    1 - Real.exp (-(a : ℝ) / 36) -
        40 * Real.exp (-(a : ℝ) / 72) ≤
      pmfEventProbability
        (uniformFixedSizeSampleLaw sampleSize (by
          rw [Fintype.card_fin, hhalf]
          omega))
        (fun sample =>
          singlePriceRevenue values p ≤
            6 *
              (randomSamplingOptimalThresholdAuction
                (sampledSideAssignment sample.1) true minWinners).revenue values) := by
  have hfixed_le_count_h :
      singlePriceRevenue values p ≤ (saleCount values p : ℝ) * h :=
    singlePriceRevenue_le_saleCount_mul_bound values hp hvalue_bound
  have ha_sale : a ≤ saleCount values p := by
    have ha_real : (a : ℝ) ≤ saleCount values p := by
      have hmul :
          (a : ℝ) * h ≤ (saleCount values p : ℝ) * h :=
        le_trans halpha_h hfixed_le_count_h
      exact (mul_le_mul_iff_of_pos_right hh_pos).mp hmul
    exact_mod_cast ha_real
  exact
    theorem6_2_directional_fixed_half_revenue_bound_top_prefix_of_selected_large
      values sampleSize hsample_pos (by simpa using hhalf)
      (minWinners := minWinners) (a := a) (p := p)
      (rankedTopPrefixFamily values)
      hmin hp hminWinners_alpha ha_sale
      (fun sample hthird =>
        paper_aux_theorem6_2_selected_offer_large_sample_count_of_alpha_h
          (sampledSideAssignment sample.1) true values hmin hp hh_pos
          hminWinners_alpha ha_sale hvalue_bound halpha_h hthird)

/-- Exact fixed-half directional Theorem 6.2 in the finite candidate-price
benchmark model, under the visible discrete-alpha convention. -/
theorem theorem6_2_directional_fixed_half_revenue_bound_of_finite_candidate_benchmark_ranked
    {n : ℕ} [NeZero n] (values : Fin n → ℝ)
    (sampleSize : ℕ) (hsample_pos : 0 < sampleSize)
    (hhalf : n = sampleSize + sampleSize)
    {alpha : ℕ} {highValue : ℝ}
    (hhigh_pos : 0 < highValue)
    (hvalue_bound : ∀ i, values i ≤ highValue)
    (halpha_ge_three : 3 ≤ alpha)
    (halpha_highValue :
      (alpha : ℝ) * highValue ≤
        finiteCandidateFixedPriceBenchmark values 1) :
    1 - Real.exp (-(alpha : ℝ) / 36) -
        40 * Real.exp (-(alpha : ℝ) / 72) ≤
      pmfEventProbability
        (uniformFixedSizeSampleLaw sampleSize (by
          rw [Fintype.card_fin, hhalf]
          omega))
        (fun sample =>
          finiteCandidateFixedPriceBenchmark values 1 ≤
            6 *
              (randomSamplingOptimalThresholdAuction
                (sampledSideAssignment sample.1) true 1).revenue values) := by
  simpa [singlePriceRevenue_finiteCandidateOfferPrice_eq_benchmark] using
    theorem6_2_directional_fixed_half_revenue_bound_top_prefix_alpha_h_fin_ranked
      values sampleSize hsample_pos hhalf
      (minWinners := 1) (a := alpha)
      (p := finiteCandidateOfferPrice values 1) (h := highValue)
      (by simp) (finiteCandidateOfferPrice_nonneg values 1) hhigh_pos
      (by simpa using halpha_ge_three) hvalue_bound
      (by
        simpa [singlePriceRevenue_finiteCandidateOfferPrice_eq_benchmark] using
          halpha_highValue)

/-- Exact fixed-half directional guarantee without a separate large-alpha
premise.  The small-alpha branch uses only that the displayed lower bound is
nonpositive; it does not invoke the non-strict prefix-tail strengthening. -/
theorem theorem6_2_directional_fixed_half_revenue_bound_of_finite_candidate_benchmark_all_alpha
    {n : ℕ} [NeZero n] (values : Fin n → ℝ)
    (sampleSize : ℕ) (hsample_pos : 0 < sampleSize)
    (hhalf : n = sampleSize + sampleSize)
    {alpha : ℕ} {highValue : ℝ}
    (hhigh_pos : 0 < highValue)
    (hvalue_bound : ∀ i, values i ≤ highValue)
    (halpha_highValue :
      (alpha : ℝ) * highValue ≤
        finiteCandidateFixedPriceBenchmark values 1) :
    1 - Real.exp (-(alpha : ℝ) / 36) -
        40 * Real.exp (-(alpha : ℝ) / 72) ≤
      pmfEventProbability
        (uniformFixedSizeSampleLaw sampleSize (by
          rw [Fintype.card_fin, hhalf]
          omega))
        (fun sample =>
          finiteCandidateFixedPriceBenchmark values 1 ≤
            6 *
              (randomSamplingOptimalThresholdAuction
                (sampledSideAssignment sample.1) true 1).revenue values) := by
  by_cases halpha_ge_three : 3 ≤ alpha
  · exact
      theorem6_2_directional_fixed_half_revenue_bound_of_finite_candidate_benchmark_ranked
        values sampleSize hsample_pos hhalf hhigh_pos hvalue_bound
        halpha_ge_three halpha_highValue
  · have halpha_lt_three : alpha < 3 := Nat.lt_of_not_ge halpha_ge_three
    exact le_trans
      (paper_theorem6_2_probability_bound_nonpos_of_alpha_lt_three
        halpha_lt_three)
      (pmfEventProbability_nonneg _ _)

end

end GHW01DigitalGoods
