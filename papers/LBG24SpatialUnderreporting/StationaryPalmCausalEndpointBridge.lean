import LBG24SpatialUnderreporting.CollapsedCausalObservationLaw
import AppliedModelingLib.Foundations.Probability.PalmCampbell
import AppliedModelingLib.Foundations.Probability.PalmFiniteTaggedArrival
import AppliedModelingLib.Foundations.Probability.PoissonSuspensionMarkedTransport
import Mathlib.Tactic

/-!
# Stationary/Palm source bridge for a causal LBG endpoint model

This module separates the source primitives needed to instantiate the finite
causal endpoint-density model from that model itself.
-/

namespace LBG24SpatialUnderreporting

open MeasureTheory ProbabilityTheory
open AppliedModelingLib.Probability.PoissonProcess
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

/--
A stationary source and its Palm law at a tagged report arrival.  The
post-tag finite-gap law is the Palm renewal input used below; the Campbell
certificate records its provenance from a stationary base law.
-/
structure StationaryPalmTaggedArrivalSource
    (Ωbase Ω : Type*) [MeasurableSpace Ωbase] [MeasurableSpace Ω]
    (P : Measure Ω)
    (count : ℕ) (rate : ℝ) where
  base : AppliedModelingLib.Probability.Palm.ShiftInvariantProbabilityLaw Ωbase
  tagged : AppliedModelingLib.Probability.Queueing.TaggedArrivalAtZero Ω
  tagged_law : tagged.Ptag = P
  palm : AppliedModelingLib.Probability.Palm.CampbellPalmTaggedArrivalCertificate base tagged
  palm_arrivalRate_eq_rate : palm.arrivalRate = rate
  rate_pos : 0 < rate
  /-- The selected-start density evaluated at the fixed tagged history. -/
  startWeight : ℝ≥0∞
  /-- The first finite post-tag gaps and the following terminal gap. -/
  postTagGapTail : Ω → (Fin count → ℝ) × ℝ
  postTagGapTail_measurable : Measurable postTagGapTail
  palm_postTagGapTail_law :
    P.map postTagGapTail =
      (Measure.pi (fun _ : Fin count => expMeasure rate)).prod (expMeasure rate)

namespace StationaryPalmTaggedArrivalSource

variable {Ωbase Ω : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ω]
  {P : Measure Ω} {count : ℕ} {rate : ℝ}

/-- The report epochs visible before the next post-tag gap. -/
def visiblePrefix (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate)
    (j : Fin (count + 1)) : Ω → Fin j.1 → ℝ :=
  fun ω => finiteArrivalPrefix (S.postTagGapTail ω).1 j

/-- The next gap at a visible prefix, with the terminal coordinate used after
the final displayed report. -/
def nextGap (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate)
    (j : Fin (count + 1)) : Ω → ℝ :=
  fun ω => if h : j.1 < count then (S.postTagGapTail ω).1 ⟨j.1, h⟩
    else (S.postTagGapTail ω).2

/-- The tagged source supplies a probability law on its designated carrier. -/
theorem isProbabilityMeasure
    (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate) :
    IsProbabilityMeasure P := by
  rw [← S.tagged_law]
  exact S.tagged.isProbability

/-- The finite post-tag gap block has the iid exponential law used by the
collapsed observation density. -/
theorem postTagGapBlock_law
    (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate) :
    P.map (fun ω => (S.postTagGapTail ω).1) =
      CollapsedFiniteStageEndpointModel.iidGapLaw count rate := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure S.rate_pos
  calc
    P.map (fun ω => (S.postTagGapTail ω).1) =
        Measure.map Prod.fst (P.map S.postTagGapTail) := by
      rw [Measure.map_map measurable_fst S.postTagGapTail_measurable]
      rfl
    _ = Measure.map Prod.fst
        ((Measure.pi (fun _ : Fin count => expMeasure rate)).prod
          (expMeasure rate)) := by
      rw [S.palm_postTagGapTail_law]
    _ = CollapsedFiniteStageEndpointModel.iidGapLaw count rate := by
      rw [Measure.map_fst_prod, measure_univ, one_smul]
      rfl

/-- The displayed post-tag gaps and their following gap have the iid block
law and an independent exponential next-gap coordinate. -/
theorem postTagGapTail_law
    (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate) :
    P.map S.postTagGapTail =
      (CollapsedFiniteStageEndpointModel.iidGapLaw count rate).prod
        (expMeasure rate) := by
  simpa [CollapsedFiniteStageEndpointModel.iidGapLaw] using
    S.palm_postTagGapTail_law

/-- The stationary Poisson suspension and its verified Campbell/Palm law give
a concrete tagged-arrival source with iid exponential post-tag gaps. -/
noncomputable def ofPoissonSuspension
    (rate : ℝ) (rate_pos : 0 < rate) (count : ℕ) (startWeight : ℝ≥0∞) :
    StationaryPalmTaggedArrivalSource
      GoodSuspensionState (ℤ → ℝ)
      (candidateTaggedArrivalAtZero rate rate_pos).Ptag count rate := by
  let tagged := candidateTaggedArrivalAtZero rate rate_pos
  refine
    { base := goodSuspensionShiftInvariantLaw rate_pos
      tagged := tagged
      tagged_law := rfl
      palm := poissonSuspensionCampbellCertificate rate_pos
      palm_arrivalRate_eq_rate := rfl
      rate_pos := rate_pos
      startWeight := startWeight
      postTagGapTail := fun gaps =>
        (taggedFutureGapBlock count gaps,
          twoSidedGap (Int.ofNat count) gaps)
      postTagGapTail_measurable := ?_
      palm_postTagGapTail_law := ?_ }
  · exact
      (measurable_taggedFutureGapBlock count).prodMk
        (measurable_twoSidedGap (Int.ofNat count))
  · simpa [tagged, candidateTaggedArrivalAtZero] using
      map_taggedFutureGapBlock_nextGap_twoSidedInterarrivalMeasure rate_pos count

/-- A concrete tagged-gap source built from an independent stationary base and
the canonical two-sided post-tag Poisson gaps. -/
noncomputable def ofIndependentProductTaggedArrivalAtZero
    (base : AppliedModelingLib.Probability.Palm.ShiftInvariantProbabilityLaw Ωbase)
    [IsProbabilityMeasure base.Pbase]
    (rate : ℝ) (rate_pos : 0 < rate) (count : ℕ) (startWeight : ℝ≥0∞)
    (palm : AppliedModelingLib.Probability.Palm.CampbellPalmTaggedArrivalCertificate base
      (AppliedModelingLib.Probability.PoissonProcess.independentProductTaggedArrivalAtZero
        base.Pbase rate rate_pos))
    (palm_arrivalRate_eq_rate : palm.arrivalRate = rate) :
    StationaryPalmTaggedArrivalSource Ωbase (Ωbase × (ℤ → ℝ))
      (AppliedModelingLib.Probability.PoissonProcess.independentProductTaggedArrivalAtZero
        base.Pbase rate rate_pos).Ptag count rate := by
  let tagged :=
    AppliedModelingLib.Probability.PoissonProcess.independentProductTaggedArrivalAtZero
      base.Pbase rate rate_pos
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  refine
    { base := base
      tagged := tagged
      tagged_law := rfl
      palm := ?_
      palm_arrivalRate_eq_rate := ?_
      rate_pos := rate_pos
      startWeight := startWeight
      postTagGapTail := fun x =>
        (AppliedModelingLib.Probability.PoissonProcess.taggedFutureGapBlock count x.2,
          AppliedModelingLib.Probability.PoissonProcess.twoSidedGap (Int.ofNat count) x.2)
      postTagGapTail_measurable := ?_
      palm_postTagGapTail_law := ?_ }
  · simpa [tagged] using palm
  · simpa [tagged] using palm_arrivalRate_eq_rate
  · exact
      (AppliedModelingLib.Probability.PoissonProcess.measurable_taggedFutureGapBlock count).comp
        measurable_snd |>.prodMk
      ((AppliedModelingLib.Probability.PoissonProcess.measurable_twoSidedGap
        (Int.ofNat count)).comp measurable_snd)
  · simpa [tagged] using
      (AppliedModelingLib.Probability.PoissonProcess.map_taggedFutureGapBlock_nextGap_independentProductTaggedArrivalAtZero
        base.Pbase rate_pos count)

end StationaryPalmTaggedArrivalSource

/--
A causal endpoint-clock package on a stationary/Palm tagged source.  At every
visible prefix, `stage j` identifies the source law of the next gap and its
candidate endpoint with a product kernel.
-/
structure CausalPreEndEndpointProductPackage
    {Ωbase Ω : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ω]
    [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {count : ℕ} {rate : ℝ}
    (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate) where
  stage : ∀ j : Fin (count + 1),
    FinitePredictableEndpointProductModel Ω P (Fin j.1 → ℝ) rate
  stage_preHistory_eq_visiblePrefix : ∀ j,
    (stage j).preHistory = S.visiblePrefix j
  stage_nextGap_eq_source_nextGap : ∀ j,
    (stage j).nextGap = S.nextGap j
  /-- Survival masses remain measurable along finite post-tag gap blocks. -/
  stageSurvival_measurable : ∀ i : Fin count,
    Measurable (fun gaps : Fin count → ℝ =>
      (stage i.castSucc).endKernel (finiteArrivalPrefix gaps i.castSucc)
        (Set.Ioi (gaps i)))
  /-- The terminal endpoint density is measurable in finite history and tail. -/
  terminalDensity_measurable :
    Measurable (fun p : (Fin count → ℝ) × ℝ =>
      (stage (Fin.last count)).endDensity
        (finiteArrivalPrefix p.1 (Fin.last count)) p.2)

namespace CausalPreEndEndpointProductPackage

variable {Ωbase Ω : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ω]
  [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {count : ℕ} {rate : ℝ}
  {S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate}

/-- Construct the finite endpoint-density model from the tagged source and
its causal pre-end product kernels. -/
def toCollapsed (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate)
    (K : CausalPreEndEndpointProductPackage S) :
    CollapsedFiniteStageEndpointModel count where
  startWeight := S.startWeight
  endKernel := fun j => (K.stage j).endKernel
  endKernel_isMarkov := fun j => (K.stage j).endKernel_isMarkov
  endDensity := fun j => (K.stage j).endDensity
  endDensity_measurable := fun j => (K.stage j).endDensity_measurable
  endKernel_eq_withDensity := fun j => (K.stage j).endKernel_eq_withDensity
  stageSurvival_measurable := K.stageSurvival_measurable
  terminalDensity_measurable := K.terminalDensity_measurable

/-- The constructed endpoint kernel is the source product kernel at each
visible prefix. -/
theorem toCollapsed_endKernel
    (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate)
    (K : CausalPreEndEndpointProductPackage S)
    (j : Fin (count + 1)) :
    (K.toCollapsed S).endKernel j = (K.stage j).endKernel :=
  rfl

/-- The constructed endpoint density is the source endpoint density at each
visible prefix. -/
theorem toCollapsed_endDensity
    (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate)
    (K : CausalPreEndEndpointProductPackage S)
    (j : Fin (count + 1)) :
    (K.toCollapsed S).endDensity j = (K.stage j).endDensity :=
  rfl

/-- The constructed endpoint kernel has the source stage density with respect
to Lebesgue measure. -/
theorem toCollapsed_endKernel_eq_withDensity
    (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate)
    (K : CausalPreEndEndpointProductPackage S)
    (j : Fin (count + 1)) :
    (K.toCollapsed S).endKernel j = Kernel.withDensity
      (Kernel.const (Fin j.1 → ℝ) (volume : Measure ℝ))
      ((K.toCollapsed S).endDensity j) := by
  simpa [toCollapsed] using (K.stage j).endKernel_eq_withDensity

/-- The source law of a visible prefix, its next gap, and its candidate
endpoint has the product-kernel form used by the constructed model. -/
theorem source_stage_product_law
    (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate)
    (K : CausalPreEndEndpointProductPackage S)
    (j : Fin (count + 1)) :
    P.map (fun ω => (S.visiblePrefix j ω,
      (S.nextGap j ω, (K.stage j).endTime ω))) =
      (P.map (S.visiblePrefix j)) ⊗ₘ
        ((Kernel.const (Fin j.1 → ℝ) (expMeasure rate)) ×ₖ
          (K.toCollapsed S).endKernel j) := by
  rw [← K.stage_preHistory_eq_visiblePrefix j,
    ← K.stage_nextGap_eq_source_nextGap j]
  simpa [toCollapsed] using (K.stage j).preHistory_nextGap_end_product

/-- The source stage law has the constructed model's endpoint density in its
conditional product kernel. -/
theorem source_stage_product_law_withDensity
    (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate)
    (K : CausalPreEndEndpointProductPackage S)
    (j : Fin (count + 1)) :
    P.map (fun ω => (S.visiblePrefix j ω,
      (S.nextGap j ω, (K.stage j).endTime ω))) =
      (P.map (S.visiblePrefix j)) ⊗ₘ
        ((Kernel.const (Fin j.1 → ℝ) (expMeasure rate)) ×ₖ
          Kernel.withDensity (Kernel.const (Fin j.1 → ℝ) (volume : Measure ℝ))
            ((K.toCollapsed S).endDensity j)) := by
  rw [K.source_stage_product_law S j,
    K.toCollapsed_endKernel_eq_withDensity S j]

/-- A source-level rectangle likelihood factorization for the next report gap
and candidate endpoint. -/
theorem source_stage_tail_rectangle_factorization
    (S : StationaryPalmTaggedArrivalSource Ωbase Ω P count rate)
    (K : CausalPreEndEndpointProductPackage S)
    (j : Fin (count + 1)) {A : Set (Fin j.1 → ℝ)} {E : Set ℝ}
    (elapsed : ℝ) (hA : MeasurableSet A) (hE : MeasurableSet E) :
    P.map (fun ω => (S.visiblePrefix j ω,
      (S.nextGap j ω, (K.stage j).endTime ω)))
        (A ×ˢ (Set.Ioi elapsed ×ˢ E)) =
      ∫⁻ h in A, (expMeasure rate) (Set.Ioi elapsed) *
        (K.toCollapsed S).endKernel j h E ∂P.map (S.visiblePrefix j) := by
  rw [← K.stage_preHistory_eq_visiblePrefix j,
    ← K.stage_nextGap_eq_source_nextGap j]
  simpa [toCollapsed] using
    (FinitePredictableEndpointProductModel.tail_rectangle_factorization
      (K.stage j) S.rate_pos elapsed hA hE)

end CausalPreEndEndpointProductPackage

end

end LBG24SpatialUnderreporting
