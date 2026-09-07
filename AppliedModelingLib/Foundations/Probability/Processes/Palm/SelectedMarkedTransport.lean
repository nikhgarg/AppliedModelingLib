import AppliedModelingLib.Foundations.Probability.PoissonSuspensionMarkedTransport
import AppliedModelingLib.Foundations.Probability.Processes.TimedEmbedded.Core
import Mathlib.Probability.ConditionalProbability

/-!
# Selected marked-event Campbell/Palm transport

This module formalizes the exact conditioning and selected-count transport
steps needed to pass from an all-event stationary Campbell certificate to a
true-mark selection. It intentionally leaves the substantive marked
all-event product Campbell lift as an explicit premise: unmarked Poisson
transport alone does not determine full re-centered mark-path events.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

noncomputable section

/- The conditional tagged law is structurally a tagged-arrival law whenever
the conditioning event has positive mass.  This does not assert a Palm
transport identity; it only carries the zero-tag and strict-order facts
through absolute continuity. -/
noncomputable def TaggedArrivalAtZero.conditionOn
    {Ω : Type*} [MeasurableSpace Ω] (tagged : TaggedArrivalAtZero Ω)
    (u : Set Ω) (hu : tagged.Ptag u ≠ 0) : TaggedArrivalAtZero Ω := by
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  exact
    { Ptag := tagged.Ptag[|u]
      isProbability := ProbabilityTheory.cond_isProbabilityMeasure hu
      arrivals := tagged.arrivals
      tag_at_zero :=
        (ProbabilityTheory.cond_absolutelyContinuous (μ := tagged.Ptag)
          (s := u)).ae_le tagged.tag_at_zero
      arrivals_strict :=
        (ProbabilityTheory.cond_absolutelyContinuous (μ := tagged.Ptag)
          (s := u)).ae_le tagged.arrivals_strict }

@[simp]
theorem TaggedArrivalAtZero.conditionOn_Ptag
    {Ω : Type*} [MeasurableSpace Ω] (tagged : TaggedArrivalAtZero Ω)
    (u : Set Ω) (hu : tagged.Ptag u ≠ 0) :
    (tagged.conditionOn u hu).Ptag = tagged.Ptag[|u] := rfl

end

end AppliedModelingLib.Probability.Queueing

namespace AppliedModelingLib.Probability.Palm

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

noncomputable section

/-- Conditioning on a positive finite tagged slice gives its exact
unnormalized mass factorization. -/
theorem measure_inter_eq_measure_mul_cond
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (u s : Set Ω) (hu : MeasurableSet u)
    (hu_ne_zero : μ u ≠ 0) (hu_ne_top : μ u ≠ ∞) :
    μ (u ∩ s) = μ u * μ[s | u] := by
  rw [ProbabilityTheory.cond_apply hu, ← mul_assoc,
    ENNReal.mul_inv_cancel hu_ne_zero hu_ne_top, one_mul]

/-- The conditional tagged law factors an unnormalized tagged slice exactly
by the slice mass. -/
theorem tagged_conditionOn_slice_factorization
    {Ω : Type*} [MeasurableSpace Ω] (tagged : Queueing.TaggedArrivalAtZero Ω)
    (u s : Set Ω) (hu : MeasurableSet u) (hu_ne_zero : tagged.Ptag u ≠ 0) :
    tagged.Ptag (u ∩ s) = tagged.Ptag u *
      (tagged.conditionOn u hu_ne_zero).Ptag s := by
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  rw [Queueing.TaggedArrivalAtZero.conditionOn_Ptag]
  exact measure_inter_eq_measure_mul_cond tagged.Ptag u s hu hu_ne_zero
    (measure_ne_top _ _)

/-- The preceding conditional tagged slice factorization in the form needed
for Bernoulli thinning: the slice has mass `p`, hence the unnormalized law is
`p` times the conditional tagged law. -/
theorem tagged_conditionOn_slice_factorization_ofReal
    {Ω : Type*} [MeasurableSpace Ω] (tagged : Queueing.TaggedArrivalAtZero Ω)
    (u s : Set Ω) (hu : MeasurableSet u) (hu_ne_zero : tagged.Ptag u ≠ 0)
    (p : ℝ) (hmass : tagged.Ptag u = ENNReal.ofReal p) :
    tagged.Ptag (u ∩ s) = ENNReal.ofReal p *
      (tagged.conditionOn u hu_ne_zero).Ptag s := by
  rw [← hmass]
  exact tagged_conditionOn_slice_factorization tagged u s hu hu_ne_zero

/-- The unit-window Campbell count after retaining only indices whose Boolean
mark is `true`.  This is a weighted/selected count; it intentionally does not
pretend that the surviving indices have already been re-enumerated by `ℤ`. -/
noncomputable def trueMarkedUnitWindowCampbellCount
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    (arrivalsIn : ℝ → ℝ → Ωbase → Finset ℤ)
    (recenterAt : Ωbase → ℤ → Ωtag)
    (markAt : Ωbase → ℤ → Bool)
    (s : Set Ωtag) (ω : Ωbase) : ℕ := by
  classical
  exact ((arrivalsIn 0 1 ω).filter fun i =>
    markAt ω i = true ∧ recenterAt ω i ∈ s).card

/-- If the mark selected at a base index is the zero-coordinate mark of its
recentered sample, the selected count is the ordinary all-event count tested
against the true-mark slice of the tagged space. -/
theorem trueMarkedUnitWindowCampbellCount_eq_unitWindowCampbellCount_slice
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    (arrivalsIn : ℝ → ℝ → Ωbase → Finset ℤ)
    (recenterAt : Ωbase → ℤ → Ωtag)
    (markAt : Ωbase → ℤ → Bool) (tagMark : Ωtag → Bool)
    (hmark : ∀ ω i, markAt ω i = tagMark (recenterAt ω i))
    (s : Set Ωtag) (ω : Ωbase) :
    trueMarkedUnitWindowCampbellCount arrivalsIn recenterAt markAt s ω =
      unitWindowCampbellCount arrivalsIn recenterAt
        ((tagMark ⁻¹' ({true} : Set Bool)) ∩ s) ω := by
  classical
  unfold trueMarkedUnitWindowCampbellCount unitWindowCampbellCount
  congr 1
  ext i
  simp [hmark]

/-- A generic selected-Palm transport step.  Given a marked all-event
Campbell certificate and the exact true-slice factorization of its tagged law,
it yields the expected intensity factor `p`.  The result is deliberately a
transport identity. `PalmMarkedCampbell` packages this identity with the
all-event enumeration and a covariant selector as a genuine marked-point Palm
certificate, without a noncanonical separate re-enumeration of the surviving
true-mark indices. -/
theorem trueMarkedCampbell_transport_of_allEvent
    {Ωbase Ωtag Ωtrue : Type*}
    [MeasurableSpace Ωbase] [MeasurableSpace Ωtag] [MeasurableSpace Ωtrue]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (tagMark : Ωtag → Bool) (htagMark : Measurable tagMark)
    (markAt : Ωbase → ℤ → Bool)
    (hmark : ∀ ω i, markAt ω i = tagMark (H.recenterAt ω i))
    (selectedTagged : Queueing.TaggedArrivalAtZero Ωtrue)
    (p : ℝ)
    (lift : Ωtag → Ωtrue)
    (hlift : Measurable lift)
    (hfactor : ∀ s : Set Ωtrue, MeasurableSet s →
      tagged.Ptag ((tagMark ⁻¹' ({true} : Set Bool)) ∩ lift ⁻¹' s) =
        ENNReal.ofReal p * selectedTagged.Ptag s)
    (s : Set Ωtrue) (hs : MeasurableSet s) :
    ∫⁻ ω, (trueMarkedUnitWindowCampbellCount H.arrivalsIn
      (fun ω i => lift (H.recenterAt ω i)) markAt s ω : ENNReal) ∂base.Pbase =
      ENNReal.ofReal (H.arrivalRate * p) * selectedTagged.Ptag s := by
  let t : Set Ωtag := (tagMark ⁻¹' ({true} : Set Bool)) ∩ lift ⁻¹' s
  have ht : MeasurableSet t := by
    exact ((MeasurableSet.singleton true).preimage htagMark).inter (hs.preimage hlift)
  have hcount :
      (fun ω => trueMarkedUnitWindowCampbellCount H.arrivalsIn
        (fun ω i => lift (H.recenterAt ω i)) markAt s ω) =
        (fun ω => unitWindowCampbellCount H.arrivalsIn H.recenterAt t ω) := by
    funext ω
    unfold trueMarkedUnitWindowCampbellCount unitWindowCampbellCount
    congr 1
    ext i
    simp [t, hmark ω i]
  have hcountENN :
      (fun ω => (trueMarkedUnitWindowCampbellCount H.arrivalsIn
        (fun ω i => lift (H.recenterAt ω i)) markAt s ω : ENNReal)) =
        (fun ω => (unitWindowCampbellCount H.arrivalsIn H.recenterAt t ω : ENNReal)) := by
    funext ω
    rw [congrFun hcount ω]
  rw [hcountENN, H.campbell_unit_interval t ht, hfactor s hs]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt H.arrivalRate_pos)]

/-- A concrete selected tagged law is obtained by conditioning the all-event
tagged law on a true zero-coordinate mark.  If that slice has mass `p`, the
generic selected Campbell transport has intensity `arrivalRate * p`.

This is the selected-count transport theorem consumed by
`PalmMarkedCampbell.markedCampbellCertificate_conditionOnTrue`; the resulting
marked certificate retains the all-event indexing and the selected-point
covariance rather than requiring a separate survivor re-enumeration. -/
theorem trueMarkedCampbell_transport_to_conditionedTagged
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (tagMark : Ωtag → Bool) (htagMark : Measurable tagMark)
    (markAt : Ωbase → ℤ → Bool)
    (hmark : ∀ ω i, markAt ω i = tagMark (H.recenterAt ω i))
    (p : ℝ)
    (htrueMass : tagged.Ptag (tagMark ⁻¹' ({true} : Set Bool)) = ENNReal.ofReal p)
    (htrue_ne_zero : tagged.Ptag (tagMark ⁻¹' ({true} : Set Bool)) ≠ 0)
    (s : Set Ωtag) (hs : MeasurableSet s) :
    ∫⁻ ω, (trueMarkedUnitWindowCampbellCount H.arrivalsIn H.recenterAt
      markAt s ω : ENNReal) ∂base.Pbase =
      ENNReal.ofReal (H.arrivalRate * p) *
        (tagged.conditionOn (tagMark ⁻¹' ({true} : Set Bool)) htrue_ne_zero).Ptag s := by
  have hslice : MeasurableSet (tagMark ⁻¹' ({true} : Set Bool)) :=
    (MeasurableSet.singleton true).preimage htagMark
  have hfactor : ∀ t : Set Ωtag, MeasurableSet t →
      tagged.Ptag ((tagMark ⁻¹' ({true} : Set Bool)) ∩ id ⁻¹' t) =
        ENNReal.ofReal p *
          (tagged.conditionOn (tagMark ⁻¹' ({true} : Set Bool)) htrue_ne_zero).Ptag t := by
    intro t ht
    simpa only [Set.preimage_id] using
      (tagged_conditionOn_slice_factorization_ofReal tagged
        (tagMark ⁻¹' ({true} : Set Bool)) t hslice htrue_ne_zero p htrueMass)
  simpa only [id_eq] using
    (trueMarkedCampbell_transport_of_allEvent H tagMark htagMark markAt hmark
      (tagged.conditionOn (tagMark ⁻¹' ({true} : Set Bool)) htrue_ne_zero)
      p id measurable_id hfactor s hs)

end

end AppliedModelingLib.Probability.Palm

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

noncomputable section

open PoissonProcess

/-- A tagged Poisson gap path together with an arbitrary integer-indexed
embedded mark/state path.  The event epochs use the gap coordinate only. -/
noncomputable def timedEmbeddedTaggedArrivalAtZero
    {α : Type*} [MeasurableSpace α]
    (rate : ℝ) (hrate : 0 < rate) (PtagPath : Measure (ℤ → α))
    [IsProbabilityMeasure PtagPath] :
    TaggedArrivalAtZero ((ℤ → ℝ) × (ℤ → α)) where
  Ptag := (candidateTaggedArrivalAtZero rate hrate).Ptag.prod PtagPath
  isProbability := by
    letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
      isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
    change IsProbabilityMeasure ((twoSidedInterarrivalMeasure rate).prod PtagPath)
    infer_instance
  arrivals := fun z => candidatePalmArrival z.1
  tag_at_zero := by
    letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
      isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
    refine ae_of_ae_map
      (μ := (twoSidedInterarrivalMeasure rate).prod PtagPath)
      (f := Prod.fst) (p := fun g : ℤ → ℝ => candidatePalmArrival g 0 = 0)
      measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact ae_candidatePalmArrival_tag_at_zero
  arrivals_strict := by
    letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
      isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
    refine ae_of_ae_map
      (μ := (twoSidedInterarrivalMeasure rate).prod PtagPath)
      (f := Prod.fst) (p := fun g : ℤ → ℝ => StrictMono (candidatePalmArrival g))
      measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact ae_candidatePalmArrival_strictMono hrate

/-- Any measurable statistic of the embedded path factor retains its law
under the concrete tagged product. This is a genuine tagged probability-space
fact, but does not identify the gap and path factors through a real-time Palm
transport. -/
theorem timedEmbeddedTaggedArrivalAtZero_pathStatistic_hasLaw
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (PtagPath : Measure (ℤ → α)) [IsProbabilityMeasure PtagPath]
    (pathStatistic : (ℤ → α) → β) (hpathStatistic : Measurable pathStatistic)
    (rate : ℝ) (hrate : 0 < rate) :
    HasLaw (fun z : (ℤ → ℝ) × (ℤ → α) => pathStatistic z.2)
      (PtagPath.map pathStatistic)
      (timedEmbeddedTaggedArrivalAtZero rate hrate PtagPath).Ptag := by
  let G : Measure (ℤ → ℝ) := twoSidedInterarrivalMeasure rate
  letI : IsProbabilityMeasure G := isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  refine ⟨(hpathStatistic.comp measurable_snd).aemeasurable, ?_⟩
  change Measure.map (fun z : (ℤ → ℝ) × (ℤ → α) => pathStatistic z.2)
      (G.prod PtagPath) = PtagPath.map pathStatistic
  calc
    Measure.map (fun z : (ℤ → ℝ) × (ℤ → α) => pathStatistic z.2)
        (G.prod PtagPath) =
        Measure.map pathStatistic (Measure.map Prod.snd (G.prod PtagPath)) := by
          symm
          rw [Measure.map_map hpathStatistic measurable_snd]
          rfl
    _ = Measure.map pathStatistic PtagPath := by
          rw [Measure.map_snd_prod, measure_univ, one_smul]

/-- Recenter both the Poisson gap path and its synchronously indexed embedded
path at event `i`. -/
def timedEmbeddedRecenterAt
    {α : Type*} (z : GoodSuspensionState × (ℤ → α)) (i : ℤ) :
    (ℤ → ℝ) × (ℤ → α) :=
  (suspensionBaseRecenter z.1 i, intPathShift i z.2)

theorem measurable_timedEmbeddedRecenterAt
    {α : Type*} [MeasurableSpace α] (i : ℤ) :
    Measurable (fun z : GoodSuspensionState × (ℤ → α) =>
      timedEmbeddedRecenterAt z i) := by
  exact ((measurable_suspensionBaseRecenter i).comp measurable_fst).prodMk
    ((measurable_intPathShift (α := α) i).comp measurable_snd)

/-- Recentring a labelled event of a good stationary suspension preserves the
two-sided positive-gap and nonexplosion conditions of the resulting Palm gap
path. -/
theorem suspensionGoodGapPath_timedEmbeddedRecenterAt
    {α : Type*} (z : GoodSuspensionState × (ℤ → α)) (i : ℤ) :
    suspensionGoodGapPath (timedEmbeddedRecenterAt z i).1 := by
  change suspensionGoodGapPath (suspensionGapShift i z.1.1.1)
  exact suspensionGoodGapPath_shift z.1.1.1 z.1.2.2 i

theorem timedEmbeddedRecenterAt_arrivals
    {α : Type*} (z : GoodSuspensionState × (ℤ → α)) (i j : ℤ) :
    candidatePalmArrival (timedEmbeddedRecenterAt z i).1 j =
      timedEmbeddedArrival z (i + j) - timedEmbeddedArrival z i := by
  exact suspensionBaseRecenter_arrivals z.1 i j

/-- At the physical epoch of a labelled stationary arrival, the
boundary-correct time-flow crossing label is that arrival's own integer
label. -/
theorem suspensionCrossingIndexPastClosed_suspensionBaseArrival
    {α : Type*} (z : GoodSuspensionState × (ℤ → α)) (i : ℤ) :
    suspensionCrossingIndexPastClosed (timedEmbeddedArrival z i) z.1.1 = i := by
  have hstrict : StrictMono (candidatePalmArrival z.1.1.1) :=
    suspensionGoodGapPath_strictMono z.1.1.1 z.1.2.2
  have hcross : candidatePalmArrival z.1.1.1
      (suspensionCrossingIndexPastClosed (timedEmbeddedArrival z i) z.1.1) ≤
        z.1.1.2 + timedEmbeddedArrival z i ∧
      z.1.1.2 + timedEmbeddedArrival z i < candidatePalmArrival z.1.1.1
        (suspensionCrossingIndexPastClosed (timedEmbeddedArrival z i) z.1.1 + 1) := by
    simpa [timedEmbeddedArrival] using
      (suspensionCrossingIndexPastClosed_interval z.1.1.1
        (suspensionGoodGapPath_future z.1.1.1 z.1.2.2)
        (suspensionGoodGapPath_past z.1.1.1 z.1.2.2)
        z.1.1.2 (timedEmbeddedArrival z i))
  have harrival : candidatePalmArrival z.1.1.1 i ≤
      z.1.1.2 + timedEmbeddedArrival z i ∧
      z.1.1.2 + timedEmbeddedArrival z i < candidatePalmArrival z.1.1.1 (i + 1) := by
    constructor
    · simp only [timedEmbeddedArrival, suspensionBaseArrival]
      linarith
    · have hnext : candidatePalmArrival z.1.1.1 i < candidatePalmArrival z.1.1.1 (i + 1) :=
        hstrict (by omega)
      simp only [timedEmbeddedArrival, suspensionBaseArrival]
      linarith
  exact candidatePalmArrival_interval_index_unique z.1.1.1 hstrict hcross harrival

/-- Flowing a marked stationary input to one of its labelled arrival epochs
and then discarding the zero phase gives exactly the ordinary Palm-recentered
arrival and mark paths. -/
theorem timedEmbeddedSuspensionFlow_at_timedEmbeddedArrival_eq_recenter
    {α : Type*} (z : GoodSuspensionState × (ℤ → α)) (i : ℤ) :
    ((timedEmbeddedSuspensionFlow (timedEmbeddedArrival z i) z).1.1.1,
      (timedEmbeddedSuspensionFlow (timedEmbeddedArrival z i) z).2) =
      timedEmbeddedRecenterAt z i := by
  change (suspensionGapShift
      (suspensionCrossingIndexPastClosed (timedEmbeddedArrival z i) z.1.1) z.1.1.1,
      intPathShift (suspensionCrossingIndexPastClosed (timedEmbeddedArrival z i) z.1.1) z.2) =
    (suspensionBaseRecenter z.1 i, intPathShift i z.2)
  rw [suspensionCrossingIndexPastClosed_suspensionBaseArrival z i]
  rfl

/-- At a labelled embedded arrival epoch, the real-time suspension flow has
zero phase.  Together with the preceding recentering identity, this lets a
Palm-selected input be identified with the literal stationary input viewed
from that arrival. -/
theorem timedEmbeddedSuspensionFlow_at_timedEmbeddedArrival_phase_zero
    {α : Type*} (z : GoodSuspensionState × (ℤ → α)) (i : ℤ) :
    (timedEmbeddedSuspensionFlow (timedEmbeddedArrival z i) z).1.1.2 = 0 := by
  change z.1.1.2 + timedEmbeddedArrival z i -
      candidatePalmArrival z.1.1.1
        (suspensionCrossingIndexPastClosed (timedEmbeddedArrival z i) z.1.1) = 0
  rw [suspensionCrossingIndexPastClosed_suspensionBaseArrival z i]
  simp only [timedEmbeddedArrival, suspensionBaseArrival]
  ring

/-- Recentring after a physical-time flow agrees with recentering the
corresponding restored arrival label in the original marked input.  This is
the label-level covariance needed when a Campbell summand is compared with a
time-translation-invariant queue observable. -/
theorem timedEmbeddedRecenterAt_flow_restore
    {α : Type*} (z : GoodSuspensionState × (ℤ → α)) (t : ℝ) (j : ℤ) :
    timedEmbeddedRecenterAt (timedEmbeddedSuspensionFlow (α := α) t z) j =
      timedEmbeddedRecenterAt z
        (suspensionCrossingIndexPastClosed t z.1.1 + j) := by
  let c : ℤ := suspensionCrossingIndexPastClosed t z.1.1
  change
    (suspensionGapShift j (suspensionGapShift c z.1.1.1),
      intPathShift j (intPathShift c z.2)) =
      (suspensionGapShift (c + j) z.1.1.1,
        intPathShift (c + j) z.2)
  rw [suspensionGapShift_comp, intPathShift_comp]
  simp [add_comm]

/-- The finite all-event index set of the timed embedded suspension. -/
def timedEmbeddedArrivalIndices
    {α : Type*} (a b : ℝ) (z : GoodSuspensionState × (ℤ → α)) : Finset ℤ :=
  suspensionBaseArrivalIndices a b z.1

theorem mem_timedEmbeddedArrivalIndices_iff
    {α : Type*} (a b : ℝ) (z : GoodSuspensionState × (ℤ → α)) (i : ℤ) :
    i ∈ timedEmbeddedArrivalIndices a b z ↔
      a ≤ timedEmbeddedArrival z i ∧ timedEmbeddedArrival z i < b := by
  exact mem_suspensionBaseArrivalIndices_iff a b z.1 i

/-- The injective restoration of a marked-input label after a physical-time
translation. -/
def timedEmbeddedFlowRestoreEmbedding
    {α : Type*} (z : GoodSuspensionState × (ℤ → α)) (t : ℝ) : ℤ ↪ ℤ :=
  ⟨fun j => suspensionCrossingIndexPastClosed t z.1.1 + j, by
    intro first second heq
    change suspensionCrossingIndexPastClosed t z.1.1 + first =
      suspensionCrossingIndexPastClosed t z.1.1 + second at heq
    omega⟩

/-- Restoring labels maps a translated marked-input arrival window exactly
onto the original physical-time window. -/
theorem timedEmbeddedArrivalIndices_flow_restore
    {α : Type*} (z : GoodSuspensionState × (ℤ → α))
    (t a b : ℝ) :
    Finset.map (timedEmbeddedFlowRestoreEmbedding z t)
      (timedEmbeddedArrivalIndices (a - t) (b - t)
        (timedEmbeddedSuspensionFlow (α := α) t z)) =
      timedEmbeddedArrivalIndices a b z := by
  classical
  let c : ℤ := suspensionCrossingIndexPastClosed t z.1.1
  ext k
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨j, hj, hrestore⟩
    have hjwindow : a - t ≤
        timedEmbeddedArrival (timedEmbeddedSuspensionFlow (α := α) t z) j ∧
        timedEmbeddedArrival (timedEmbeddedSuspensionFlow (α := α) t z) j < b - t :=
      mem_timedEmbeddedArrivalIndices_iff (a - t) (b - t)
        (timedEmbeddedSuspensionFlow (α := α) t z) j |>.mp hj
    have htime : timedEmbeddedArrival
        (timedEmbeddedSuspensionFlow (α := α) t z) j =
        timedEmbeddedArrival z (c + j) - t := by
      simpa [c] using timedEmbeddedArrival_flow z t j
    have hindex : c + j = k := by
      simpa [timedEmbeddedFlowRestoreEmbedding, c] using hrestore
    apply mem_timedEmbeddedArrivalIndices_iff a b z k |>.mpr
    rw [← hindex]
    rw [htime] at hjwindow
    constructor <;> linarith
  · intro hk
    let j : ℤ := k - c
    have hindex : c + j = k := by
      dsimp [j]
      omega
    have hkwindow : a ≤ timedEmbeddedArrival z k ∧
        timedEmbeddedArrival z k < b :=
      mem_timedEmbeddedArrivalIndices_iff a b z k |>.mp hk
    have htime : timedEmbeddedArrival
        (timedEmbeddedSuspensionFlow (α := α) t z) j =
        timedEmbeddedArrival z (c + j) - t := by
      simpa [c] using timedEmbeddedArrival_flow z t j
    refine ⟨j, ?_, ?_⟩
    · apply mem_timedEmbeddedArrivalIndices_iff (a - t) (b - t)
        (timedEmbeddedSuspensionFlow (α := α) t z) j |>.mpr
      rw [htime, hindex]
      constructor <;> linarith
    · change c + j = k
      exact hindex

/-- Recentring every arrival in a finite physical-time window commutes with
translation once the translated labels are restored. -/
theorem sum_timedEmbeddedArrivalIndices_recenter_flow_restore
    {α β : Type*} [AddCommMonoid β]
    (f : ((ℤ → ℝ) × (ℤ → α)) → β)
    (z : GoodSuspensionState × (ℤ → α)) (t a b : ℝ) :
    ∑ j ∈ timedEmbeddedArrivalIndices (a - t) (b - t)
        (timedEmbeddedSuspensionFlow (α := α) t z),
      f (timedEmbeddedRecenterAt (timedEmbeddedSuspensionFlow (α := α) t z) j) =
      ∑ k ∈ timedEmbeddedArrivalIndices a b z, f (timedEmbeddedRecenterAt z k) := by
  classical
  rw [← timedEmbeddedArrivalIndices_flow_restore z t a b, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro j hj
  rw [timedEmbeddedRecenterAt_flow_restore]
  rfl

theorem measurable_timedEmbeddedArrival
    {α : Type*} [MeasurableSpace α] (i : ℤ) :
    Measurable (fun z : GoodSuspensionState × (ℤ → α) =>
      timedEmbeddedArrival z i) := by
  exact (measurable_suspensionBaseArrival i).comp measurable_fst

/-- The all-event Campbell count of the timed embedded suspension is
measurable for every measurable tagged event. -/
theorem measurable_timedEmbeddedUnitWindowCampbellCount
    {α : Type*} [MeasurableSpace α]
    (s : Set ((ℤ → ℝ) × (ℤ → α))) (hs : MeasurableSet s) :
    Measurable (fun z : GoodSuspensionState × (ℤ → α) =>
      Palm.unitWindowCampbellCount timedEmbeddedArrivalIndices
        timedEmbeddedRecenterAt s z) := by
  classical
  let state : GoodSuspensionState × (ℤ → α) → ℤ × ℤ := fun z =>
    (suspensionCrossingIndexPastClosed 0 z.1.1,
      suspensionCrossingIndexPastClosed 1 z.1.1)
  let indices : ℤ × ℤ → Finset ℤ := fun n => Finset.Icc n.1 n.2
  have hstate : Measurable state := by
    exact ((measurable_suspensionCrossingIndexPastClosed 0).comp
      (measurable_subtype_coe.comp measurable_fst)).prodMk
      ((measurable_suspensionCrossingIndexPastClosed 1).comp
        (measurable_subtype_coe.comp measurable_fst))
  let selected : (GoodSuspensionState × (ℤ → α)) → ℤ → Bool := fun z i =>
    decide (0 ≤ timedEmbeddedArrival z i ∧ timedEmbeddedArrival z i < 1 ∧
      timedEmbeddedRecenterAt z i ∈ s)
  have hselected : Measurable selected := by
    refine measurable_pi_iff.2 fun i => ?_
    change Measurable (fun z : GoodSuspensionState × (ℤ → α) => if
      0 ≤ timedEmbeddedArrival z i ∧ timedEmbeddedArrival z i < 1 ∧
        timedEmbeddedRecenterAt z i ∈ s then true else false)
    have hleft : MeasurableSet {z : GoodSuspensionState × (ℤ → α) |
        (0 : ℝ) ≤ timedEmbeddedArrival z i} :=
      measurableSet_le measurable_const (measurable_timedEmbeddedArrival i)
    have hright : MeasurableSet {z : GoodSuspensionState × (ℤ → α) |
        timedEmbeddedArrival z i < (1 : ℝ)} :=
      measurableSet_lt (measurable_timedEmbeddedArrival i) measurable_const
    have hmark : MeasurableSet {z : GoodSuspensionState × (ℤ → α) |
        timedEmbeddedRecenterAt z i ∈ s} :=
      (measurable_timedEmbeddedRecenterAt i) hs
    exact Measurable.ite (hleft.inter (hright.inter hmark))
      measurable_const measurable_const
  have hcount := Palm.measurable_count_from_countable_parameter state hstate indices
    selected hselected
  change Measurable (fun z =>
    ((timedEmbeddedArrivalIndices 0 1 z).filter fun i =>
      timedEmbeddedRecenterAt z i ∈ s).card)
  convert hcount using 1
  funext z
  simp only [state, indices, selected, timedEmbeddedArrivalIndices,
    suspensionBaseArrivalIndices, Finset.filter_filter, decide_eq_true_eq]
  congr 1
  apply Finset.filter_congr
  intro i hi
  constructor <;> intro h
  · exact ⟨h.1.1, h.1.2, h.2⟩
  · exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

theorem timedEmbeddedArrival_range_flow
    {α : Type*} (z : GoodSuspensionState × (ℤ → α)) (t : ℝ) :
    Set.range (timedEmbeddedArrival (timedEmbeddedSuspensionFlow (α := α) t z)) =
      (fun u : ℝ => u - t) '' Set.range (timedEmbeddedArrival z) := by
  exact suspensionBaseArrival_range_goodSuspensionFlow z.1 t

/-- All structural fields of the all-event Campbell certificate for a timed
embedded product are available.  The supplied premise is the one remaining
marked transport identity; this constructor does not hide it. -/
noncomputable def timedEmbeddedCampbellCertificate_of_transport
    {α : Type*} [MeasurableSpace α] {rate : ℝ} (hrate : 0 < rate)
    (P : Measure (ℤ → α)) [IsProbabilityMeasure P]
    (hpath : ∀ k : ℤ, MeasurePreserving (intPathShift (α := α) k) P P)
    (PtagPath : Measure (ℤ → α)) [IsProbabilityMeasure PtagPath]
    (hcampbell : ∀ s : Set ((ℤ → ℝ) × (ℤ → α)), MeasurableSet s →
      ∫⁻ z, (Palm.unitWindowCampbellCount timedEmbeddedArrivalIndices
        timedEmbeddedRecenterAt s z : ENNReal) ∂
          (timedEmbeddedSuspensionShiftInvariantLaw_of_intPathShift
            hrate P hpath).Pbase =
        ENNReal.ofReal rate *
          (timedEmbeddedTaggedArrivalAtZero rate hrate PtagPath).Ptag s) :
    Palm.CampbellPalmTaggedArrivalCertificate
      (timedEmbeddedSuspensionShiftInvariantLaw_of_intPathShift hrate P hpath)
      (timedEmbeddedTaggedArrivalAtZero rate hrate PtagPath) where
  arrivalRate := rate
  arrivalRate_pos := hrate
  baseArrivals := timedEmbeddedArrival
  baseArrivals_measurable := measurable_timedEmbeddedArrival
  baseArrivals_strict := Filter.Eventually.of_forall fun z =>
    suspensionBaseArrival_strictMono z.1
  arrivalsIn := timedEmbeddedArrivalIndices
  arrivalsIn_spec := fun a b => Filter.Eventually.of_forall fun z i =>
    mem_timedEmbeddedArrivalIndices_iff a b z i
  recenterAt := timedEmbeddedRecenterAt
  recenterAt_measurable := measurable_timedEmbeddedRecenterAt
  recenter_arrivals := Filter.Eventually.of_forall fun z i j =>
    timedEmbeddedRecenterAt_arrivals z i j
  baseArrivals_shift := fun t => Filter.Eventually.of_forall fun z =>
    timedEmbeddedArrival_range_flow z t
  campbellCount_aemeasurable := fun s hs =>
    (measurable_timedEmbeddedUnitWindowCampbellCount s hs).aemeasurable
  campbell_unit_interval := hcampbell

/-- The Boolean mark at the event chosen as the temporal origin of a
recentered timed embedded sample. -/
def timedEmbeddedTaggedZeroMark : ((ℤ → ℝ) × (ℤ → Bool)) → Bool :=
  fun z => z.2 0

theorem timedEmbedded_mark_recenterAt_zero
    (z : GoodSuspensionState × (ℤ → Bool)) (i : ℤ) :
    z.2 i = timedEmbeddedTaggedZeroMark (timedEmbeddedRecenterAt z i) := by
  simp [timedEmbeddedTaggedZeroMark, timedEmbeddedRecenterAt, intPathShift]

/-- The true-mark count is exactly the all-event unit-window count on the
true-zero-mark slice of the full tagged space. -/
theorem timedEmbedded_trueMarked_count_eq_slice
    (s : Set ((ℤ → ℝ) × (ℤ → Bool)))
    (z : GoodSuspensionState × (ℤ → Bool)) :
    Palm.trueMarkedUnitWindowCampbellCount timedEmbeddedArrivalIndices
      timedEmbeddedRecenterAt (fun z i => z.2 i) s z =
      Palm.unitWindowCampbellCount timedEmbeddedArrivalIndices timedEmbeddedRecenterAt
        ((timedEmbeddedTaggedZeroMark ⁻¹' ({true} : Set Bool)) ∩ s) z := by
  exact Palm.trueMarkedUnitWindowCampbellCount_eq_unitWindowCampbellCount_slice
    timedEmbeddedArrivalIndices timedEmbeddedRecenterAt (fun z i => z.2 i)
    timedEmbeddedTaggedZeroMark timedEmbedded_mark_recenterAt_zero s z

/-- Exact outstanding analytic theorem for selected true marks.  Its left
side is already reduced to the true-zero-mark slice of an all-event tagged
law by `timedEmbedded_trueMarked_count_eq_slice`; the expected intensity is
the all-event clock rate multiplied by the Bernoulli true probability. -/
def HasTimedEmbeddedTrueMarkCampbellTransport
    {rate p : ℝ} (base : Palm.ShiftInvariantProbabilityLaw
      (GoodSuspensionState × (ℤ → Bool)))
    (selectedTagged : TaggedArrivalAtZero ((ℤ → ℝ) × (ℤ → Bool))) : Prop :=
  ∀ s : Set ((ℤ → ℝ) × (ℤ → Bool)), MeasurableSet s →
    ∫⁻ z, (Palm.trueMarkedUnitWindowCampbellCount timedEmbeddedArrivalIndices
      timedEmbeddedRecenterAt (fun z i => z.2 i) s z : ENNReal) ∂base.Pbase =
      ENNReal.ofReal (rate * p) * selectedTagged.Ptag s

/-- Once the all-event timed marked transport and the true-slice
factorization of the tagged law are supplied, Bernoulli thinning factors the
selected Campbell intensity exactly as `rate * p`. -/
theorem hasTimedEmbeddedTrueMarkCampbellTransport_of_markedAllEvent
    {rate p : ℝ} (hrate : 0 < rate)
    (P : Measure (ℤ → Bool)) [IsProbabilityMeasure P]
    (hpath : ∀ k : ℤ, MeasurePreserving (intPathShift (α := Bool) k) P P)
    (PtagPath : Measure (ℤ → Bool)) [IsProbabilityMeasure PtagPath]
    (hcampbell : ∀ s : Set ((ℤ → ℝ) × (ℤ → Bool)), MeasurableSet s →
      ∫⁻ z, (Palm.unitWindowCampbellCount timedEmbeddedArrivalIndices
        timedEmbeddedRecenterAt s z : ENNReal) ∂
          (timedEmbeddedSuspensionShiftInvariantLaw_of_intPathShift
            hrate P hpath).Pbase =
        ENNReal.ofReal rate *
          (timedEmbeddedTaggedArrivalAtZero rate hrate PtagPath).Ptag s)
    (selectedTagged : TaggedArrivalAtZero ((ℤ → ℝ) × (ℤ → Bool)))
    (hfactor : ∀ s : Set ((ℤ → ℝ) × (ℤ → Bool)), MeasurableSet s →
      (timedEmbeddedTaggedArrivalAtZero rate hrate PtagPath).Ptag
        ((timedEmbeddedTaggedZeroMark ⁻¹' ({true} : Set Bool)) ∩ s) =
          ENNReal.ofReal p * selectedTagged.Ptag s) :
    HasTimedEmbeddedTrueMarkCampbellTransport
      (rate := rate) (p := p)
      (timedEmbeddedSuspensionShiftInvariantLaw_of_intPathShift hrate P hpath)
      selectedTagged := by
  intro s hs
  let H := timedEmbeddedCampbellCertificate_of_transport
    hrate P hpath PtagPath hcampbell
  have hmarkMeas : Measurable timedEmbeddedTaggedZeroMark :=
    (measurable_pi_apply 0).comp measurable_snd
  have hfactor' : ∀ s : Set ((ℤ → ℝ) × (ℤ → Bool)), MeasurableSet s →
      (timedEmbeddedTaggedArrivalAtZero rate hrate PtagPath).Ptag
        ((timedEmbeddedTaggedZeroMark ⁻¹' ({true} : Set Bool)) ∩
        id ⁻¹' s) = ENNReal.ofReal p * selectedTagged.Ptag s := by
    intro t ht
    simpa [H] using hfactor t ht
  have h := Palm.trueMarkedCampbell_transport_of_allEvent
    H timedEmbeddedTaggedZeroMark hmarkMeas (fun z i => z.2 i)
    timedEmbedded_mark_recenterAt_zero selectedTagged p
    id measurable_id hfactor' s hs
  simpa [H] using h

end

end AppliedModelingLib.Probability.Queueing
