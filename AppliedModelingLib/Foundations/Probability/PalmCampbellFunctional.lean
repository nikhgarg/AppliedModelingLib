import AppliedModelingLib.Foundations.Probability.PalmCampbell

/-!
# Functional Campbell transport

`CampbellPalmTaggedArrivalCertificate` records its defining identity on
measurable events.  This module turns that setwise identity into the
corresponding nonnegative measurable-function identity by constructing the
unit-window Campbell intensity as a countable sum of restricted pushforwards.

The result is generic: it does not depend on a particular queue, mark type, or
Poisson construction.
-/

namespace AppliedModelingLib.Probability.Palm

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

noncomputable section

/-- The event that labelled arrival `i` falls in the unit time window. -/
def unitWindowArrivalSet
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged) (i : ℤ) : Set Ωbase :=
  {ω | 0 ≤ H.baseArrivals ω i ∧ H.baseArrivals ω i < 1}

theorem measurableSet_unitWindowArrivalSet
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged) (i : ℤ) :
    MeasurableSet (unitWindowArrivalSet H i) := by
  exact (measurableSet_le measurable_const (H.baseArrivals_measurable i)).inter
    (measurableSet_lt (H.baseArrivals_measurable i) measurable_const)

/-- The unit-window intensity measure obtained by summing the pushforward of
each labelled arrival restricted to the event that it lies in `[0, 1)`. -/
noncomputable def unitWindowCampbellIntensity
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged) : Measure Ωtag :=
  Measure.sum fun i : ℤ =>
    Measure.map (H.recenterAt · i)
      (base.Pbase.restrict (unitWindowArrivalSet H i))

/-- The nonnegative contribution of one labelled arrival to a measurable
tagged event. -/
noncomputable def unitWindowCampbellSummand
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (s : Set Ωtag) (i : ℤ) : Ωbase → ℝ≥0∞ := by
  classical
  exact fun ω => if ω ∈ unitWindowArrivalSet H i ∧ H.recenterAt ω i ∈ s
    then 1 else 0

theorem unitWindowCampbellIntensity_apply
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (s : Set Ωtag) (hs : MeasurableSet s) :
    unitWindowCampbellIntensity H s =
      ∑' i : ℤ, ∫⁻ ω, unitWindowCampbellSummand H s i ω ∂base.Pbase := by
  classical
  rw [unitWindowCampbellIntensity, Measure.sum_apply _ hs]
  apply tsum_congr
  intro i
  rw [Measure.map_apply (H.recenterAt_measurable i) hs]
  rw [Measure.restrict_apply (hs.preimage (H.recenterAt_measurable i))]
  rw [← MeasureTheory.lintegral_indicator_one]
  · apply MeasureTheory.lintegral_congr
    intro ω
    simp only [unitWindowCampbellSummand, Set.indicator_apply,
      Set.mem_inter_iff, Set.mem_preimage]
    by_cases hwindow : ω ∈ unitWindowArrivalSet H i
    · by_cases htag : H.recenterAt ω i ∈ s <;> simp [hwindow, htag]
    · by_cases htag : H.recenterAt ω i ∈ s <;> simp [hwindow, htag]
  · exact (hs.preimage (H.recenterAt_measurable i)).inter
      (measurableSet_unitWindowArrivalSet H i)

/-- Almost surely, the finite unit-window Campbell count is the countable sum
of its labelled restricted-pushforward summands. -/
theorem ae_unitWindowCampbellCount_coe_eq_tsum
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (s : Set Ωtag) :
    ∀ᵐ ω ∂base.Pbase,
      (unitWindowCampbellCount H.arrivalsIn H.recenterAt s ω : ℝ≥0∞) =
        ∑' i : ℤ, unitWindowCampbellSummand H s i ω := by
  filter_upwards [H.arrivalsIn_spec 0 1] with ω hspec
  classical
  rw [tsum_eq_sum (s := H.arrivalsIn 0 1 ω)]
  · unfold unitWindowCampbellCount
    rw [Finset.card_filter]
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hwindow : ω ∈ unitWindowArrivalSet H i := by
      exact (hspec i).mp hi
    simp [unitWindowCampbellSummand, hwindow]
  · intro i hi
    have hnotwindow : ω ∉ unitWindowArrivalSet H i := by
      intro hwindow
      exact hi ((hspec i).mpr hwindow)
    simp [unitWindowCampbellSummand, hnotwindow]

/-- The setwise Campbell certificate identifies the constructed unit-window
intensity measure with the arrival-rate multiple of the tagged law.  The proof
uses only: measurable labelled arrival times and recenterings, the almost
sure finite-window enumeration in `H.arrivalsIn_spec`, and Tonelli for the
nonnegative countable sum. -/
theorem unitWindowCampbellIntensity_eq_rate_smul
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged) :
    unitWindowCampbellIntensity H = ENNReal.ofReal H.arrivalRate • tagged.Ptag := by
  classical
  ext s hs
  rw [unitWindowCampbellIntensity_apply H s hs]
  calc
    (∑' i : ℤ, ∫⁻ ω, unitWindowCampbellSummand H s i ω ∂base.Pbase) =
        ∫⁻ ω, ∑' i : ℤ, unitWindowCampbellSummand H s i ω ∂base.Pbase := by
          symm
          apply MeasureTheory.lintegral_tsum
          intro i
          let A : Set Ωbase := unitWindowArrivalSet H i
          have hA : MeasurableSet A := measurableSet_unitWindowArrivalSet H i
          have htag : MeasurableSet {ω : Ωbase | H.recenterAt ω i ∈ s} :=
            hs.preimage (H.recenterAt_measurable i)
          change AEMeasurable (fun ω => if ω ∈ A ∧ H.recenterAt ω i ∈ s
            then (1 : ℝ≥0∞) else 0) base.Pbase
          exact (Measurable.ite (hA.inter htag) measurable_const measurable_const).aemeasurable
    _ = ∫⁻ ω, (unitWindowCampbellCount H.arrivalsIn H.recenterAt s ω : ℝ≥0∞)
        ∂base.Pbase := by
          apply MeasureTheory.lintegral_congr_ae
          filter_upwards [ae_unitWindowCampbellCount_coe_eq_tsum H s] with ω hω
          exact hω.symm
    _ = ENNReal.ofReal H.arrivalRate * tagged.Ptag s :=
      H.campbell_unit_interval s hs
    _ = (ENNReal.ofReal H.arrivalRate • tagged.Ptag) s := by
      rw [Measure.smul_apply, smul_eq_mul]

/-- The contribution of a labelled unit-window arrival to a nonnegative
measurable tagged statistic. -/
noncomputable def unitWindowCampbellWeightedSummand
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (f : Ωtag → ℝ≥0∞) (i : ℤ) : Ωbase → ℝ≥0∞ := by
  classical
  exact fun ω => if ω ∈ unitWindowArrivalSet H i then f (H.recenterAt ω i) else 0

theorem measurable_unitWindowCampbellWeightedSummand
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (f : Ωtag → ℝ≥0∞) (hf : Measurable f) (i : ℤ) :
    Measurable (unitWindowCampbellWeightedSummand H f i) := by
  classical
  change Measurable (fun ω => if ω ∈ unitWindowArrivalSet H i
    then f (H.recenterAt ω i) else 0)
  exact Measurable.ite (measurableSet_unitWindowArrivalSet H i)
    (hf.comp (H.recenterAt_measurable i)) measurable_const

/-- Almost surely, the finite sum of a nonnegative tagged statistic over the
unit-window arrivals is the countable weighted Campbell sum used by Tonelli. -/
theorem ae_sum_unitWindow_arrivalsIn_recenter_eq_tsum
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (f : Ωtag → ℝ≥0∞) :
    ∀ᵐ ω ∂base.Pbase,
      (∑ i ∈ H.arrivalsIn 0 1 ω, f (H.recenterAt ω i)) =
        ∑' i : ℤ, unitWindowCampbellWeightedSummand H f i ω := by
  filter_upwards [H.arrivalsIn_spec 0 1] with ω hspec
  classical
  rw [tsum_eq_sum (s := H.arrivalsIn 0 1 ω)]
  · apply Finset.sum_congr rfl
    intro i hi
    have hwindow : ω ∈ unitWindowArrivalSet H i := (hspec i).mp hi
    simp [unitWindowCampbellWeightedSummand, hwindow]
  · intro i hi
    have hnotwindow : ω ∉ unitWindowArrivalSet H i := by
      intro hwindow
      exact hi ((hspec i).mpr hwindow)
    simp [unitWindowCampbellWeightedSummand, hnotwindow]

/-- Integrating the sum of weighted unit-window arrivals is exactly
integration of the tagged statistic against the constructed Campbell
intensity. -/
theorem lintegral_tsum_unitWindowCampbellWeightedSummand_eq_intensity
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (f : Ωtag → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ ω, ∑' i : ℤ, unitWindowCampbellWeightedSummand H f i ω ∂base.Pbase =
      ∫⁻ z, f z ∂unitWindowCampbellIntensity H := by
  classical
  calc
    (∫⁻ ω, ∑' i : ℤ, unitWindowCampbellWeightedSummand H f i ω ∂base.Pbase) =
        ∑' i : ℤ, ∫⁻ ω, unitWindowCampbellWeightedSummand H f i ω ∂base.Pbase := by
          apply MeasureTheory.lintegral_tsum
          intro i
          exact (measurable_unitWindowCampbellWeightedSummand H f hf i).aemeasurable
    _ = ∑' i : ℤ, ∫⁻ z, f z ∂Measure.map (H.recenterAt · i)
        (base.Pbase.restrict (unitWindowArrivalSet H i)) := by
          apply tsum_congr
          intro i
          calc
            (∫⁻ ω, unitWindowCampbellWeightedSummand H f i ω ∂base.Pbase) =
                ∫⁻ ω, (unitWindowArrivalSet H i).indicator
                  (fun ω => f (H.recenterAt ω i)) ω ∂base.Pbase := by
                    apply MeasureTheory.lintegral_congr
                    intro ω
                    by_cases hwindow : ω ∈ unitWindowArrivalSet H i <;>
                      simp [unitWindowCampbellWeightedSummand, hwindow]
            _ = ∫⁻ ω, f (H.recenterAt ω i) ∂
                base.Pbase.restrict (unitWindowArrivalSet H i) :=
                  MeasureTheory.lintegral_indicator
                    (measurableSet_unitWindowArrivalSet H i) _
            _ = ∫⁻ z, f z ∂Measure.map (H.recenterAt · i)
                (base.Pbase.restrict (unitWindowArrivalSet H i)) :=
                  (MeasureTheory.lintegral_map hf (H.recenterAt_measurable i)).symm
    _ = ∫⁻ z, f z ∂unitWindowCampbellIntensity H := by
          symm
          exact MeasureTheory.lintegral_sum_measure f _

/-- Functional form of the unit-window Campbell identity.  For every
nonnegative measurable tagged statistic, summing it over the finitely many
unit-window arrivals and then integrating under the stationary base law equals
the arrival rate times its tagged-law integral.

The proof uses no integrability assumption: nonnegativity permits Tonelli,
and finiteness of each sample's window follows from the certificate's finite
`arrivalsIn` enumeration. -/
theorem lintegral_tsum_unitWindowCampbellWeightedSummand
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (f : Ωtag → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ ω, ∑' i : ℤ, unitWindowCampbellWeightedSummand H f i ω ∂base.Pbase =
      ENNReal.ofReal H.arrivalRate * (∫⁻ z, f z ∂tagged.Ptag) := by
  calc
    (∫⁻ ω, ∑' i : ℤ, unitWindowCampbellWeightedSummand H f i ω ∂base.Pbase) =
        ∫⁻ z, f z ∂unitWindowCampbellIntensity H :=
      lintegral_tsum_unitWindowCampbellWeightedSummand_eq_intensity H f hf
    _ = ∫⁻ z, f z ∂(ENNReal.ofReal H.arrivalRate • tagged.Ptag) := by
      rw [unitWindowCampbellIntensity_eq_rate_smul H]
    _ = ENNReal.ofReal H.arrivalRate * (∫⁻ z, f z ∂tagged.Ptag) := by
      rw [MeasureTheory.lintegral_smul_measure]
      rfl

/-- Functional Campbell identity in finite-sum form for the literal unit
arrival window. -/
theorem lintegral_sum_unitWindow_arrivalsIn_recenter
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (f : Ωtag → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ ω, (∑ i ∈ H.arrivalsIn 0 1 ω, f (H.recenterAt ω i)) ∂base.Pbase =
      ENNReal.ofReal H.arrivalRate * (∫⁻ z, f z ∂tagged.Ptag) := by
  calc
    (∫⁻ ω, (∑ i ∈ H.arrivalsIn 0 1 ω, f (H.recenterAt ω i)) ∂base.Pbase) =
        ∫⁻ ω, ∑' i : ℤ, unitWindowCampbellWeightedSummand H f i ω ∂base.Pbase := by
          apply MeasureTheory.lintegral_congr_ae
          exact ae_sum_unitWindow_arrivalsIn_recenter_eq_tsum H f
    _ = ENNReal.ofReal H.arrivalRate * (∫⁻ z, f z ∂tagged.Ptag) :=
      lintegral_tsum_unitWindowCampbellWeightedSummand H f hf

end

end AppliedModelingLib.Probability.Palm
