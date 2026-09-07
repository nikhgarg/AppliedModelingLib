import AppliedModelingLib.Foundations.Probability.Processes.Palm.SelectedMarkedTransport

namespace AppliedModelingLib.Probability.Palm

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

noncomputable section

open AppliedModelingLib.Probability
open AppliedModelingLib.Probability.Queueing

/-- The selected physical point set of a marked candidate-event enumeration. -/
def trueMarkedPointSet
    {Ωbase : Type*} (baseArrivals : Ωbase → ℤ → ℝ)
    (markAt : Ωbase → ℤ → Bool) (ω : Ωbase) : Set ℝ :=
  {u | ∃ i, markAt ω i = true ∧ baseArrivals ω i = u}

/-- A genuine Palm certificate for a selected marked point
process.  It keeps the all-event integer indexing and records the measurable
selector rather than requiring an independent integer re-enumeration of the
selected sub-process. -/
structure MarkedCampbellPalmTaggedArrivalCertificate
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    (base : ShiftInvariantProbabilityLaw Ωbase)
    (tagged : TaggedArrivalAtZero Ωtag) where
  arrivalRate : ℝ
  arrivalRate_pos : 0 < arrivalRate
  baseArrivals : Ωbase → ℤ → ℝ
  baseArrivals_measurable : ∀ i, Measurable (fun ω => baseArrivals ω i)
  baseArrivals_strict : ∀ᵐ ω ∂base.Pbase, StrictMono (baseArrivals ω)
  arrivalsIn : ℝ → ℝ → Ωbase → Finset ℤ
  arrivalsIn_spec : ∀ a b, ∀ᵐ ω ∂base.Pbase, ∀ i,
    i ∈ arrivalsIn a b ω ↔ a ≤ baseArrivals ω i ∧ baseArrivals ω i < b
  recenterAt : Ωbase → ℤ → Ωtag
  recenterAt_measurable : ∀ i, Measurable (fun ω => recenterAt ω i)
  recenter_arrivals : ∀ᵐ ω ∂base.Pbase, ∀ i j,
    tagged.arrivals (recenterAt ω i) j =
      baseArrivals ω (i + j) - baseArrivals ω i
  baseArrivals_shift : ∀ t, ∀ᵐ ω ∂base.Pbase,
    Set.range (baseArrivals (base.shift t ω)) =
      (fun u : ℝ => u - t) '' Set.range (baseArrivals ω)
  markAt : Ωbase → ℤ → Bool
  markAt_measurable : ∀ i, Measurable (fun ω => markAt ω i)
  tagMark : Ωtag → Bool
  tagMark_measurable : Measurable tagMark
  mark_recenter : ∀ᵐ ω ∂base.Pbase, ∀ i,
    markAt ω i = tagMark (recenterAt ω i)
  /-- The selected point set, not only the candidate point set, covaries
  under the stationary real-time action. -/
  trueMarkedPointSet_shift : ∀ t, ∀ᵐ ω ∂base.Pbase,
    trueMarkedPointSet baseArrivals markAt (base.shift t ω) =
      (fun u : ℝ => u - t) '' trueMarkedPointSet baseArrivals markAt ω
  tagged_zero_mark : ∀ᵐ z ∂tagged.Ptag, tagMark z = true
  campbellCount_aemeasurable : ∀ s : Set Ωtag, MeasurableSet s →
    AEMeasurable (fun ω =>
      trueMarkedUnitWindowCampbellCount arrivalsIn recenterAt markAt s ω)
      base.Pbase
  campbell_unit_interval : ∀ s : Set Ωtag, MeasurableSet s →
    ∫⁻ ω, (trueMarkedUnitWindowCampbellCount arrivalsIn recenterAt markAt s ω :
      ENNReal) ∂base.Pbase =
      ENNReal.ofReal arrivalRate * tagged.Ptag s

theorem ae_tagMark_eq_true_conditionOn
    {Ω : Type*} [MeasurableSpace Ω]
    (tagged : TaggedArrivalAtZero Ω)
    (tagMark : Ω → Bool) (htagMark : Measurable tagMark)
    (htrue_ne_zero : tagged.Ptag
      (tagMark ⁻¹' ({true} : Set Bool)) ≠ 0) :
    ∀ᵐ z ∂(tagged.conditionOn
      (tagMark ⁻¹' ({true} : Set Bool)) htrue_ne_zero).Ptag,
      tagMark z = true := by
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  rw [TaggedArrivalAtZero.conditionOn_Ptag, ae_iff]
  have hu : MeasurableSet (tagMark ⁻¹' ({true} : Set Bool)) :=
    (MeasurableSet.singleton true).preimage htagMark
  have hinter : (tagMark ⁻¹' ({true} : Set Bool)) ∩
      {z : Ω | tagMark z = false} = ∅ := by
    ext z
    simp
  rw [ProbabilityTheory.cond_apply hu]
  simp [hinter]

/-- A positive true-mark conditional slice of an all-event certificate yields
the marked-point Palm certificate without enumerating surviving
indices. -/
noncomputable def markedCampbellCertificate_conditionOnTrue
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (tagMark : Ωtag → Bool) (htagMark : Measurable tagMark)
    (markAt : Ωbase → ℤ → Bool)
    (hmark : ∀ ω i, markAt ω i = tagMark (H.recenterAt ω i))
    (htrueMarkedPointSet_shift : ∀ t, ∀ᵐ ω ∂base.Pbase,
      trueMarkedPointSet H.baseArrivals markAt (base.shift t ω) =
        (fun u : ℝ => u - t) '' trueMarkedPointSet H.baseArrivals markAt ω)
    (p : ℝ)
    (htrueMass : tagged.Ptag (tagMark ⁻¹' ({true} : Set Bool)) = ENNReal.ofReal p)
    (htrue_ne_zero : tagged.Ptag (tagMark ⁻¹' ({true} : Set Bool)) ≠ 0)
    (hselectedRate : 0 < H.arrivalRate * p) :
    MarkedCampbellPalmTaggedArrivalCertificate base
      (tagged.conditionOn (tagMark ⁻¹' ({true} : Set Bool)) htrue_ne_zero) where
  arrivalRate := H.arrivalRate * p
  arrivalRate_pos := hselectedRate
  baseArrivals := H.baseArrivals
  baseArrivals_measurable := H.baseArrivals_measurable
  baseArrivals_strict := H.baseArrivals_strict
  arrivalsIn := H.arrivalsIn
  arrivalsIn_spec := H.arrivalsIn_spec
  recenterAt := H.recenterAt
  recenterAt_measurable := H.recenterAt_measurable
  recenter_arrivals := by
    simpa [TaggedArrivalAtZero.conditionOn] using H.recenter_arrivals
  baseArrivals_shift := H.baseArrivals_shift
  markAt := markAt
  markAt_measurable := by
    intro i
    have h : (fun ω => markAt ω i) =
        (fun ω => tagMark (H.recenterAt ω i)) := by
      funext ω
      exact hmark ω i
    rw [h]
    exact htagMark.comp (H.recenterAt_measurable i)
  tagMark := tagMark
  tagMark_measurable := htagMark
  mark_recenter := Filter.Eventually.of_forall hmark
  trueMarkedPointSet_shift := htrueMarkedPointSet_shift
  tagged_zero_mark := ae_tagMark_eq_true_conditionOn
    tagged tagMark htagMark htrue_ne_zero
  campbellCount_aemeasurable := by
    intro s hs
    have ht : MeasurableSet
        ((tagMark ⁻¹' ({true} : Set Bool)) ∩ s) :=
      ((MeasurableSet.singleton true).preimage htagMark).inter hs
    let f : Ωbase → ℕ := fun ω =>
      trueMarkedUnitWindowCampbellCount H.arrivalsIn H.recenterAt markAt s ω
    let g : Ωbase → ℕ := fun ω =>
      unitWindowCampbellCount H.arrivalsIn H.recenterAt
        ((tagMark ⁻¹' ({true} : Set Bool)) ∩ s) ω
    have hfg : f = g := by
      funext ω
      exact trueMarkedUnitWindowCampbellCount_eq_unitWindowCampbellCount_slice
        H.arrivalsIn H.recenterAt markAt tagMark hmark s ω
    rw [show (fun ω => trueMarkedUnitWindowCampbellCount H.arrivalsIn
      H.recenterAt markAt s ω) = g by
      exact hfg]
    exact H.campbellCount_aemeasurable _ ht
  campbell_unit_interval := by
    intro s hs
    exact trueMarkedCampbell_transport_to_conditionedTagged H tagMark htagMark
      markAt hmark p htrueMass htrue_ne_zero s hs

/-- Stationary-Palm/PASTA package for a selected marked point
process.  The PASTA field remains an independent theorem, exactly as in the
unmarked certificate. -/
structure MarkedStationaryPalmPASTAQueueLengthCertificate
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    (base : ShiftInvariantProbabilityLaw Ωbase)
    (tagged : TaggedArrivalAtZero Ωtag)
    extends MarkedCampbellPalmTaggedArrivalCertificate base tagged,
      PalmPASTAQueueLengthCertificate Ωbase Ωtag base tagged

def MarkedStationaryPalmPASTAQueueLengthCertificate.to_pasta
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : TaggedArrivalAtZero Ωtag}
    (H : MarkedStationaryPalmPASTAQueueLengthCertificate base tagged) :
    PalmPASTAQueueLengthCertificate Ωbase Ωtag base tagged :=
  H.toPalmPASTAQueueLengthCertificate

end

end AppliedModelingLib.Probability.Palm
