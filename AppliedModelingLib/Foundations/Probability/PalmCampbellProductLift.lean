import AppliedModelingLib.Foundations.Probability.PalmCampbellFunctional
import AppliedModelingLib.Foundations.Probability.PalmMarkedCampbell

/-!
# Campbell product lift with a stationary passive system

This module lifts a genuine target Campbell/Palm certificate across an
independent stationary passive system.  At a target arrival labelled `i`, the
passive coordinate is translated by that target arrival's *physical* epoch
before the pair is evaluated.  Thus the result is not a bare product tagged
law: its transport identity is derived from the target certificate, Tonelli,
and passive real-time stationarity.
-/

namespace AppliedModelingLib.Probability.Palm

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

noncomputable section

/-- Recenter a target event and translate the independent passive system by
the physical target arrival epoch.  With the library's shift convention,
`passive.shift u` moves an epoch at time `u` to zero. -/
def targetPassiveRecenter
    {Ωbase Ωtag Γ : Type*}
    [MeasurableSpace Ωbase] [MeasurableSpace Ωtag] [MeasurableSpace Γ]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (passive : ShiftInvariantProbabilityLaw Γ)
    (x : Ωbase × Γ) (i : ℤ) : Ωtag × Γ :=
  (H.recenterAt x.1 i, passive.shift (H.baseArrivals x.1 i) x.2)

/-- Joint measurability of `targetPassiveRecenter` requires joint
measurability of the passive real-time flow. -/
theorem measurable_targetPassiveRecenter
    {Ωbase Ωtag Γ : Type*}
    [MeasurableSpace Ωbase] [MeasurableSpace Ωtag] [MeasurableSpace Γ]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (passive : ShiftInvariantProbabilityLaw Γ)
    (hpassiveFlow : Measurable (Function.uncurry passive.shift))
    (i : ℤ) :
    Measurable (fun x : Ωbase × Γ => targetPassiveRecenter H passive x i) := by
  unfold targetPassiveRecenter
  apply Measurable.prodMk
  · exact (H.recenterAt_measurable i).comp measurable_fst
  · exact hpassiveFlow.comp
      (((H.baseArrivals_measurable i).comp measurable_fst).prodMk measurable_snd)

/-- The nonnegative contribution of one target arrival to a statistic of its
correctly time-recentered target/passive pair. -/
noncomputable def targetPassiveWeightedSummand
    {Ωbase Ωtag Γ : Type*}
    [MeasurableSpace Ωbase] [MeasurableSpace Ωtag] [MeasurableSpace Γ]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (passive : ShiftInvariantProbabilityLaw Γ)
    (f : Ωtag × Γ → ℝ≥0∞) (i : ℤ) : Ωbase × Γ → ℝ≥0∞ := by
  classical
  exact fun x => if x.1 ∈ unitWindowArrivalSet H i
    then f (targetPassiveRecenter H passive x i) else 0

theorem measurable_targetPassiveWeightedSummand
    {Ωbase Ωtag Γ : Type*}
    [MeasurableSpace Ωbase] [MeasurableSpace Ωtag] [MeasurableSpace Γ]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (passive : ShiftInvariantProbabilityLaw Γ)
    (hpassiveFlow : Measurable (Function.uncurry passive.shift))
    (f : Ωtag × Γ → ℝ≥0∞) (hf : Measurable f) (i : ℤ) :
    Measurable (targetPassiveWeightedSummand H passive f i) := by
  classical
  change Measurable (fun x : Ωbase × Γ => if x.1 ∈ unitWindowArrivalSet H i
    then f (targetPassiveRecenter H passive x i) else 0)
  exact Measurable.ite
    ((measurableSet_unitWindowArrivalSet H i).preimage measurable_fst)
    (hf.comp (measurable_targetPassiveRecenter H passive hpassiveFlow i)) measurable_const

/-- Integrate a nonnegative joint statistic over the passive base law while
holding the target tagged configuration fixed. -/
noncomputable def passiveSectionLIntegral
    {Ωtag Γ : Type*} [MeasurableSpace Ωtag] [MeasurableSpace Γ]
    (passive : ShiftInvariantProbabilityLaw Γ)
    (f : Ωtag × Γ → ℝ≥0∞) : Ωtag → ℝ≥0∞ :=
  fun z => ∫⁻ γ, f (z, γ) ∂passive.Pbase

theorem measurable_passiveSectionLIntegral
    {Ωtag Γ : Type*} [MeasurableSpace Ωtag] [MeasurableSpace Γ]
    (passive : ShiftInvariantProbabilityLaw Γ)
    (f : Ωtag × Γ → ℝ≥0∞) (hf : Measurable f) :
    Measurable (passiveSectionLIntegral passive f) := by
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  letI : SFinite passive.Pbase := by infer_instance
  exact hf.lintegral_prod_right'

/-- Passive stationarity removes the target arrival time from an inner
passive integral, but only after the passive coordinate has first been
translated by that time. -/
theorem lintegral_targetPassiveRecenter_eq_passiveSectionLIntegral
    {Ωbase Ωtag Γ : Type*}
    [MeasurableSpace Ωbase] [MeasurableSpace Ωtag] [MeasurableSpace Γ]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (passive : ShiftInvariantProbabilityLaw Γ)
    (f : Ωtag × Γ → ℝ≥0∞) (hf : Measurable f)
    (ω : Ωbase) (i : ℤ) :
    ∫⁻ γ, f (targetPassiveRecenter H passive (ω, γ) i) ∂passive.Pbase =
      passiveSectionLIntegral passive f (H.recenterAt ω i) := by
  change ∫⁻ γ, f (H.recenterAt ω i,
      passive.shift (H.baseArrivals ω i) γ) ∂passive.Pbase =
    ∫⁻ γ, f (H.recenterAt ω i, γ) ∂passive.Pbase
  exact (passive.shift_preserving (H.baseArrivals ω i)).lintegral_comp
    (hf.comp (measurable_const.prodMk measurable_id))

/-- Integrating one time-recentered target/passive summand over the passive
law gives the corresponding target weighted summand with the passive section
integrated out. -/
theorem lintegral_targetPassiveWeightedSummand_eq_unitWindowWeightedSummand
    {Ωbase Ωtag Γ : Type*}
    [MeasurableSpace Ωbase] [MeasurableSpace Ωtag] [MeasurableSpace Γ]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (passive : ShiftInvariantProbabilityLaw Γ)
    (f : Ωtag × Γ → ℝ≥0∞) (hf : Measurable f)
    (ω : Ωbase) (i : ℤ) :
    ∫⁻ γ, targetPassiveWeightedSummand H passive f i (ω, γ) ∂passive.Pbase =
      unitWindowCampbellWeightedSummand H (passiveSectionLIntegral passive f) i ω := by
  classical
  by_cases hwindow : ω ∈ unitWindowArrivalSet H i
  · simp only [targetPassiveWeightedSummand, unitWindowCampbellWeightedSummand,
      hwindow, if_true]
    exact lintegral_targetPassiveRecenter_eq_passiveSectionLIntegral H passive f hf ω i
  · simp [targetPassiveWeightedSummand, unitWindowCampbellWeightedSummand, hwindow]

/-- Functional Campbell product lift.  The passive system is evaluated after
translation by the physical target arrival time in every summand.  This is
derived from the target Campbell certificate, passive stationarity, and
Tonelli; it is not a declaration that an arbitrary product tagged law is
Palm. -/
theorem lintegral_tsum_targetPassiveWeightedSummand
    {Ωbase Ωtag Γ : Type*}
    [MeasurableSpace Ωbase] [MeasurableSpace Ωtag] [MeasurableSpace Γ]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (passive : ShiftInvariantProbabilityLaw Γ)
    (hpassiveFlow : Measurable (Function.uncurry passive.shift))
    (f : Ωtag × Γ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, ∑' i : ℤ, targetPassiveWeightedSummand H passive f i x
      ∂(base.Pbase.prod passive.Pbase) =
      ENNReal.ofReal H.arrivalRate *
        (∫⁻ z, f z ∂(tagged.Ptag.prod passive.Pbase)) := by
  letI : IsProbabilityMeasure base.Pbase := base.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  letI : SFinite base.Pbase := by infer_instance
  letI : SFinite passive.Pbase := by infer_instance
  calc
    (∫⁻ x, ∑' i : ℤ, targetPassiveWeightedSummand H passive f i x
        ∂(base.Pbase.prod passive.Pbase)) =
        ∑' i : ℤ, ∫⁻ x, targetPassiveWeightedSummand H passive f i x
          ∂(base.Pbase.prod passive.Pbase) := by
            apply MeasureTheory.lintegral_tsum
            intro i
            exact (measurable_targetPassiveWeightedSummand H passive hpassiveFlow f hf i).aemeasurable
    _ = ∑' i : ℤ, ∫⁻ ω, ∫⁻ γ,
        targetPassiveWeightedSummand H passive f i (ω, γ) ∂passive.Pbase ∂base.Pbase := by
          apply tsum_congr
          intro i
          exact MeasureTheory.lintegral_prod _
            (measurable_targetPassiveWeightedSummand H passive hpassiveFlow f hf i).aemeasurable
    _ = ∑' i : ℤ, ∫⁻ ω,
        unitWindowCampbellWeightedSummand H (passiveSectionLIntegral passive f) i ω
          ∂base.Pbase := by
          apply tsum_congr
          intro i
          apply MeasureTheory.lintegral_congr
          intro ω
          exact lintegral_targetPassiveWeightedSummand_eq_unitWindowWeightedSummand
            H passive f hf ω i
    _ = ∫⁻ ω, ∑' i : ℤ,
        unitWindowCampbellWeightedSummand H (passiveSectionLIntegral passive f) i ω
          ∂base.Pbase := by
          symm
          apply MeasureTheory.lintegral_tsum
          intro i
          exact (measurable_unitWindowCampbellWeightedSummand H
            (passiveSectionLIntegral passive f)
            (measurable_passiveSectionLIntegral passive f hf) i).aemeasurable
    _ = ENNReal.ofReal H.arrivalRate *
        (∫⁻ z, passiveSectionLIntegral passive f z ∂tagged.Ptag) :=
          lintegral_tsum_unitWindowCampbellWeightedSummand H
            (passiveSectionLIntegral passive f)
            (measurable_passiveSectionLIntegral passive f hf)
    _ = ENNReal.ofReal H.arrivalRate *
        (∫⁻ z, f z ∂(tagged.Ptag.prod passive.Pbase)) := by
          rw [MeasureTheory.lintegral_prod f hf.aemeasurable]
          rfl

/-- The actual finite unit-window count for target events recentered jointly
with a passive stationary system. -/
noncomputable def targetPassiveUnitWindowCampbellCount
    {Ωbase Ωtag Γ : Type*}
    [MeasurableSpace Ωbase] [MeasurableSpace Ωtag] [MeasurableSpace Γ]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (passive : ShiftInvariantProbabilityLaw Γ)
    (s : Set (Ωtag × Γ)) (x : Ωbase × Γ) : ℕ :=
  unitWindowCampbellCount
    (fun a b x => H.arrivalsIn a b x.1)
    (targetPassiveRecenter H passive) s x

/-- Measurable indicator statistic for a joint target/passive event. -/
noncomputable def targetPassiveEventIndicator
    {Ωtag Γ : Type*} [MeasurableSpace Ωtag] [MeasurableSpace Γ]
    (s : Set (Ωtag × Γ)) : Ωtag × Γ → ℝ≥0∞ := by
  classical
  exact s.indicator (fun _ => 1)

theorem measurable_targetPassiveEventIndicator
    {Ωtag Γ : Type*} [MeasurableSpace Ωtag] [MeasurableSpace Γ]
    (s : Set (Ωtag × Γ)) (hs : MeasurableSet s) :
    Measurable (targetPassiveEventIndicator s) := by
  classical
  change Measurable (s.indicator (fun _ => (1 : ℝ≥0∞)))
  exact measurable_const.indicator hs

/-- The finite count agrees almost everywhere with the nonnegative countable
sum used in the functional product proof.  This explicitly supplies the
measurability bridge for the random passive recentering; it is not inferred
from an unshifted product law. -/
theorem ae_targetPassiveUnitWindowCampbellCount_coe_eq_tsum
    {Ωbase Ωtag Γ : Type*}
    [MeasurableSpace Ωbase] [MeasurableSpace Ωtag] [MeasurableSpace Γ]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (passive : ShiftInvariantProbabilityLaw Γ)
    (s : Set (Ωtag × Γ)) :
    ∀ᵐ x ∂(base.Pbase.prod passive.Pbase),
      (targetPassiveUnitWindowCampbellCount H passive s x : ℝ≥0∞) =
        ∑' i : ℤ, targetPassiveWeightedSummand H passive
          (targetPassiveEventIndicator s) i x := by
  letI : IsProbabilityMeasure base.Pbase := base.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  have hspec : ∀ᵐ x ∂(base.Pbase.prod passive.Pbase), ∀ i,
      i ∈ H.arrivalsIn 0 1 x.1 ↔ x.1 ∈ unitWindowArrivalSet H i := by
    refine ae_of_ae_map (μ := base.Pbase.prod passive.Pbase) (f := Prod.fst)
      (p := fun ω => ∀ i, i ∈ H.arrivalsIn 0 1 ω ↔
        ω ∈ unitWindowArrivalSet H i) measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    filter_upwards [H.arrivalsIn_spec 0 1] with ω hω
    intro i
    exact hω i
  filter_upwards [hspec] with x hspec
  classical
  rw [tsum_eq_sum (s := H.arrivalsIn 0 1 x.1)]
  · unfold targetPassiveUnitWindowCampbellCount unitWindowCampbellCount
    rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hwindow : x.1 ∈ unitWindowArrivalSet H i := (hspec i).mp hi
    unfold targetPassiveWeightedSummand targetPassiveEventIndicator
    rw [if_pos hwindow]
    by_cases htag : targetPassiveRecenter H passive x i ∈ s <;> simp [htag]
  · intro i hi
    have hnotwindow : x.1 ∉ unitWindowArrivalSet H i := by
      intro hwindow
      exact hi ((hspec i).mpr hwindow)
    simp [targetPassiveWeightedSummand, hnotwindow]

/-- The random-time-recentered target/passive count is almost everywhere
measurable for every measurable joint event.  Its proof uses the preceding
explicit count/sum equality and the jointly measurable passive flow. -/
theorem aemeasurable_targetPassiveUnitWindowCampbellCount
    {Ωbase Ωtag Γ : Type*}
    [MeasurableSpace Ωbase] [MeasurableSpace Ωtag] [MeasurableSpace Γ]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (passive : ShiftInvariantProbabilityLaw Γ)
    (hpassiveFlow : Measurable (Function.uncurry passive.shift))
    (s : Set (Ωtag × Γ)) (hs : MeasurableSet s) :
    AEMeasurable (fun x => targetPassiveUnitWindowCampbellCount H passive s x)
      (base.Pbase.prod passive.Pbase) := by
  letI : IsProbabilityMeasure base.Pbase := base.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  have hsum : AEMeasurable (fun x : Ωbase × Γ => ∑' i : ℤ,
      targetPassiveWeightedSummand H passive (targetPassiveEventIndicator s) i x)
      (base.Pbase.prod passive.Pbase) := by
    apply AEMeasurable.ennreal_tsum
    intro i
    exact (measurable_targetPassiveWeightedSummand H passive hpassiveFlow
      (targetPassiveEventIndicator s) (measurable_targetPassiveEventIndicator s hs) i).aemeasurable
  have hcoe : AEMeasurable (fun x : Ωbase × Γ =>
      (targetPassiveUnitWindowCampbellCount H passive s x : ℝ≥0∞))
      (base.Pbase.prod passive.Pbase) :=
    hsum.congr ((ae_targetPassiveUnitWindowCampbellCount_coe_eq_tsum H passive s).mono
      fun _ h => h.symm)
  apply (MeasurableEmbedding.natCast :
    MeasurableEmbedding (Nat.cast : ℕ → ℝ≥0∞)).aemeasurable_comp_iff.mp
  simpa only [Function.comp_apply] using hcoe

/-- Setwise form of the genuine target/passive Campbell product lift.  The
right-hand product law is justified by the displayed left-hand transport in
which every passive sample is shifted by the selected target epoch. -/
theorem targetPassiveUnitWindowCampbell_transport
    {Ωbase Ωtag Γ : Type*}
    [MeasurableSpace Ωbase] [MeasurableSpace Ωtag] [MeasurableSpace Γ]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (passive : ShiftInvariantProbabilityLaw Γ)
    (hpassiveFlow : Measurable (Function.uncurry passive.shift))
    (s : Set (Ωtag × Γ)) (hs : MeasurableSet s) :
    ∫⁻ x, (targetPassiveUnitWindowCampbellCount H passive s x : ℝ≥0∞)
      ∂(base.Pbase.prod passive.Pbase) =
      ENNReal.ofReal H.arrivalRate * (tagged.Ptag.prod passive.Pbase) s := by
  letI : IsProbabilityMeasure base.Pbase := base.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  calc
    (∫⁻ x, (targetPassiveUnitWindowCampbellCount H passive s x : ℝ≥0∞)
        ∂(base.Pbase.prod passive.Pbase)) =
        ∫⁻ x, ∑' i : ℤ, targetPassiveWeightedSummand H passive
          (targetPassiveEventIndicator s) i x ∂(base.Pbase.prod passive.Pbase) := by
            apply MeasureTheory.lintegral_congr_ae
            exact ae_targetPassiveUnitWindowCampbellCount_coe_eq_tsum H passive s
    _ = ENNReal.ofReal H.arrivalRate *
        (∫⁻ z, targetPassiveEventIndicator s z ∂(tagged.Ptag.prod passive.Pbase)) :=
          lintegral_tsum_targetPassiveWeightedSummand H passive hpassiveFlow
            (targetPassiveEventIndicator s) (measurable_targetPassiveEventIndicator s hs)
    _ = ENNReal.ofReal H.arrivalRate * (tagged.Ptag.prod passive.Pbase) s := by
          congr 1
          simpa only [targetPassiveEventIndicator, Pi.one_apply] using
            (MeasureTheory.lintegral_indicator_one
              (μ := tagged.Ptag.prod passive.Pbase) hs)

/-- Independent product stationary base law, with both the target and passive
systems translated by the common real-time clock. -/
noncomputable def targetPassiveProductBaseLaw
    {Ωbase Γ : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Γ]
    (base : ShiftInvariantProbabilityLaw Ωbase)
    (passive : ShiftInvariantProbabilityLaw Γ) :
    ShiftInvariantProbabilityLaw (Ωbase × Γ) where
  Pbase := base.Pbase.prod passive.Pbase
  isProbability := by
    letI : IsProbabilityMeasure base.Pbase := base.isProbability
    letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
    infer_instance
  shift := fun t x => (base.shift t x.1, passive.shift t x.2)
  shift_zero := by
    funext x
    change (base.shift 0 x.1, passive.shift 0 x.2) = x
    simp only [base.shift_zero, passive.shift_zero, id_eq]
  shift_add := by
    intro s t
    funext x
    change (base.shift (s + t) x.1, passive.shift (s + t) x.2) =
      (base.shift s (base.shift t x.1), passive.shift s (passive.shift t x.2))
    simp only [base.shift_add, passive.shift_add, Function.comp_apply]
  shift_preserving := by
    intro t
    letI : IsProbabilityMeasure base.Pbase := base.isProbability
    letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
    letI : SFinite base.Pbase := by infer_instance
    letI : SFinite passive.Pbase := by infer_instance
    exact (base.shift_preserving t).prod (passive.shift_preserving t)

/-- Product tagged law whose target coordinate is a genuine target Palm tag
and whose passive coordinate remains independently stationary.  The
`targetPassiveCampbellCertificate` below, not this definition alone, supplies
its Palm provenance. -/
noncomputable def targetPassiveTaggedArrivalAtZero
    {Ωtag Γ : Type*} [MeasurableSpace Ωtag] [MeasurableSpace Γ]
    (tagged : Queueing.TaggedArrivalAtZero Ωtag)
    (passive : ShiftInvariantProbabilityLaw Γ) :
    Queueing.TaggedArrivalAtZero (Ωtag × Γ) where
  Ptag := tagged.Ptag.prod passive.Pbase
  isProbability := by
    letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
    letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
    infer_instance
  arrivals := fun z => tagged.arrivals z.1
  tag_at_zero := by
    letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
    letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
    refine ae_of_ae_map (μ := tagged.Ptag.prod passive.Pbase) (f := Prod.fst)
      (p := fun z : Ωtag => tagged.arrivals z 0 = 0) measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact tagged.tag_at_zero
  arrivals_strict := by
    letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
    letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
    refine ae_of_ae_map (μ := tagged.Ptag.prod passive.Pbase) (f := Prod.fst)
      (p := fun z : Ωtag => StrictMono (tagged.arrivals z)) measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact tagged.arrivals_strict

/-- Lift a genuine target all-event Campbell certificate across an independent
stationary passive system.  The decisive `campbell_unit_interval` field is
proved by `targetPassiveUnitWindowCampbell_transport`, whose left side shifts
the passive state at the actual target arrival epoch. -/
noncomputable def targetPassiveCampbellCertificate
    {Ωbase Ωtag Γ : Type*}
    [MeasurableSpace Ωbase] [MeasurableSpace Ωtag] [MeasurableSpace Γ]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (passive : ShiftInvariantProbabilityLaw Γ)
    (hpassiveFlow : Measurable (Function.uncurry passive.shift)) :
    CampbellPalmTaggedArrivalCertificate
      (targetPassiveProductBaseLaw base passive)
      (targetPassiveTaggedArrivalAtZero tagged passive) where
  arrivalRate := H.arrivalRate
  arrivalRate_pos := H.arrivalRate_pos
  baseArrivals := fun x i => H.baseArrivals x.1 i
  baseArrivals_measurable := fun i => (H.baseArrivals_measurable i).comp measurable_fst
  baseArrivals_strict := by
    letI : IsProbabilityMeasure base.Pbase := base.isProbability
    letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
    refine ae_of_ae_map (μ := base.Pbase.prod passive.Pbase) (f := Prod.fst)
      (p := fun ω : Ωbase => StrictMono (H.baseArrivals ω)) measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact H.baseArrivals_strict
  arrivalsIn := fun a b x => H.arrivalsIn a b x.1
  arrivalsIn_spec := by
    intro a b
    letI : IsProbabilityMeasure base.Pbase := base.isProbability
    letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
    refine ae_of_ae_map (μ := base.Pbase.prod passive.Pbase) (f := Prod.fst)
      (p := fun ω : Ωbase => ∀ i, i ∈ H.arrivalsIn a b ω ↔
        a ≤ H.baseArrivals ω i ∧ H.baseArrivals ω i < b) measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact H.arrivalsIn_spec a b
  recenterAt := targetPassiveRecenter H passive
  recenterAt_measurable := measurable_targetPassiveRecenter H passive hpassiveFlow
  recenter_arrivals := by
    letI : IsProbabilityMeasure base.Pbase := base.isProbability
    letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
    have htarget : ∀ᵐ x ∂(base.Pbase.prod passive.Pbase), ∀ i j,
        tagged.arrivals (H.recenterAt x.1 i) j =
          H.baseArrivals x.1 (i + j) - H.baseArrivals x.1 i := by
      refine ae_of_ae_map (μ := base.Pbase.prod passive.Pbase) (f := Prod.fst)
        (p := fun ω : Ωbase => ∀ i j,
          tagged.arrivals (H.recenterAt ω i) j =
            H.baseArrivals ω (i + j) - H.baseArrivals ω i)
        measurable_fst.aemeasurable ?_
      rw [Measure.map_fst_prod, measure_univ, one_smul]
      exact H.recenter_arrivals
    filter_upwards [htarget] with x hx
    intro i j
    simpa [targetPassiveTaggedArrivalAtZero, targetPassiveRecenter] using hx i j
  baseArrivals_shift := by
    intro t
    letI : IsProbabilityMeasure base.Pbase := base.isProbability
    letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
    have htarget : ∀ᵐ x ∂(base.Pbase.prod passive.Pbase),
        Set.range (H.baseArrivals (base.shift t x.1)) =
          (fun u : ℝ => u - t) '' Set.range (H.baseArrivals x.1) := by
      refine ae_of_ae_map (μ := base.Pbase.prod passive.Pbase) (f := Prod.fst)
        (p := fun ω : Ωbase =>
          Set.range (H.baseArrivals (base.shift t ω)) =
            (fun u : ℝ => u - t) '' Set.range (H.baseArrivals ω))
        measurable_fst.aemeasurable ?_
      rw [Measure.map_fst_prod, measure_univ, one_smul]
      exact H.baseArrivals_shift t
    filter_upwards [htarget] with x hx
    simpa [targetPassiveProductBaseLaw] using hx
  campbellCount_aemeasurable := by
    intro s hs
    simpa only [targetPassiveProductBaseLaw, targetPassiveUnitWindowCampbellCount]
      using aemeasurable_targetPassiveUnitWindowCampbellCount H passive hpassiveFlow s hs
  campbell_unit_interval := by
    intro s hs
    simpa only [targetPassiveProductBaseLaw, targetPassiveTaggedArrivalAtZero,
      targetPassiveUnitWindowCampbellCount] using
      targetPassiveUnitWindowCampbell_transport H passive hpassiveFlow s hs

/-- Boolean tag read from the target coordinate of a jointly recentered
target/passive tagged sample. -/
def targetPassiveTagMark
    {Ωtag Γ : Type*} [MeasurableSpace Ωtag] [MeasurableSpace Γ]
    (tagMark : Ωtag → Bool) : Ωtag × Γ → Bool :=
  fun z => tagMark z.1

/-- Boolean mark attached to a target base arrival; the passive coordinate is
irrelevant to whether that target event is selected. -/
def targetPassiveMarkAt
    {Ωbase Γ : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Γ]
    (markAt : Ωbase → ℤ → Bool) : (Ωbase × Γ) → ℤ → Bool :=
  fun x i => markAt x.1 i

theorem measurable_targetPassiveTagMark
    {Ωtag Γ : Type*} [MeasurableSpace Ωtag] [MeasurableSpace Γ]
    (tagMark : Ωtag → Bool) (htagMark : Measurable tagMark) :
    Measurable (targetPassiveTagMark tagMark : Ωtag × Γ → Bool) :=
  htagMark.comp measurable_fst

theorem targetPassiveTagMark_trueSet
    {Ωtag Γ : Type*} [MeasurableSpace Ωtag] [MeasurableSpace Γ]
    (tagMark : Ωtag → Bool) :
    targetPassiveTagMark tagMark ⁻¹' ({true} : Set Bool) =
      (tagMark ⁻¹' ({true} : Set Bool)) ×ˢ (Set.univ : Set Γ) := by
  ext z
  simp [targetPassiveTagMark]

/-- Conditioning the lifted target mark has the same unnormalized true-mark
mass as conditioning the target coordinate itself.  This is only a product
measure calculation; the Palm provenance is supplied separately by
`targetPassiveMarkedCampbellCertificate_conditionOnTrue`. -/
theorem targetPassiveTagMark_true_mass
    {Ωtag Γ : Type*} [MeasurableSpace Ωtag] [MeasurableSpace Γ]
    (tagged : Queueing.TaggedArrivalAtZero Ωtag)
    (passive : ShiftInvariantProbabilityLaw Γ)
    (tagMark : Ωtag → Bool) :
    (targetPassiveTaggedArrivalAtZero tagged passive).Ptag
      (targetPassiveTagMark tagMark ⁻¹' ({true} : Set Bool)) =
      tagged.Ptag (tagMark ⁻¹' ({true} : Set Bool)) := by
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  letI : SFinite passive.Pbase := by infer_instance
  change (tagged.Ptag.prod passive.Pbase)
    (targetPassiveTagMark tagMark ⁻¹' ({true} : Set Bool)) = _
  rw [targetPassiveTagMark_trueSet, Measure.prod_prod, measure_univ, mul_one]

theorem targetPassive_mark_recenter
    {Ωbase Ωtag Γ : Type*}
    [MeasurableSpace Ωbase] [MeasurableSpace Ωtag] [MeasurableSpace Γ]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (passive : ShiftInvariantProbabilityLaw Γ)
    (tagMark : Ωtag → Bool) (markAt : Ωbase → ℤ → Bool)
    (hmark : ∀ ω i, markAt ω i = tagMark (H.recenterAt ω i))
    (x : Ωbase × Γ) (i : ℤ) :
    targetPassiveMarkAt markAt x i =
      targetPassiveTagMark tagMark (targetPassiveRecenter H passive x i) := by
  simpa [targetPassiveMarkAt, targetPassiveTagMark, targetPassiveRecenter] using hmark x.1 i

/-- Lift covariance of the selected target point set to the joint product
base. The proof uses the diagonal product shift and does not infer any
selected-process property from a product marginal. -/
theorem targetPassive_trueMarkedPointSet_shift
    {Ωbase Ωtag Γ : Type*}
    [MeasurableSpace Ωbase] [MeasurableSpace Ωtag] [MeasurableSpace Γ]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (passive : ShiftInvariantProbabilityLaw Γ)
    (markAt : Ωbase → ℤ → Bool)
    (hpointShift : ∀ t, ∀ᵐ ω ∂base.Pbase,
      trueMarkedPointSet H.baseArrivals markAt (base.shift t ω) =
        (fun u : ℝ => u - t) '' trueMarkedPointSet H.baseArrivals markAt ω) :
    ∀ t, ∀ᵐ x ∂(base.Pbase.prod passive.Pbase),
      trueMarkedPointSet (fun x i => H.baseArrivals x.1 i)
        (targetPassiveMarkAt markAt)
        ((targetPassiveProductBaseLaw base passive).shift t x) =
        (fun u : ℝ => u - t) ''
          trueMarkedPointSet (fun x i => H.baseArrivals x.1 i)
            (targetPassiveMarkAt markAt) x := by
  intro t
  letI : IsProbabilityMeasure base.Pbase := base.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  have htarget : ∀ᵐ x ∂(base.Pbase.prod passive.Pbase),
      trueMarkedPointSet H.baseArrivals markAt (base.shift t x.1) =
        (fun u : ℝ => u - t) '' trueMarkedPointSet H.baseArrivals markAt x.1 := by
    refine ae_of_ae_map (μ := base.Pbase.prod passive.Pbase) (f := Prod.fst)
      (p := fun ω : Ωbase =>
        trueMarkedPointSet H.baseArrivals markAt (base.shift t ω) =
          (fun u : ℝ => u - t) '' trueMarkedPointSet H.baseArrivals markAt ω)
      measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact hpointShift t
  filter_upwards [htarget] with x hx
  simpa [targetPassiveProductBaseLaw, targetPassiveMarkAt,
    trueMarkedPointSet] using hx

/-- Genuine selected marked Campbell/Palm lift.  It first invokes the proved
all-event target/passive certificate and only then conditions the target
zero-coordinate mark.  The conditional product law is therefore the result
of a Campbell transport, not evidence asserted from a bare product measure. -/
noncomputable def targetPassiveMarkedCampbellCertificate_conditionOnTrue
    {Ωbase Ωtag Γ : Type*}
    [MeasurableSpace Ωbase] [MeasurableSpace Ωtag] [MeasurableSpace Γ]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (passive : ShiftInvariantProbabilityLaw Γ)
    (hpassiveFlow : Measurable (Function.uncurry passive.shift))
    (tagMark : Ωtag → Bool) (htagMark : Measurable tagMark)
    (markAt : Ωbase → ℤ → Bool)
    (hmark : ∀ ω i, markAt ω i = tagMark (H.recenterAt ω i))
    (hpointShift : ∀ t, ∀ᵐ ω ∂base.Pbase,
      trueMarkedPointSet H.baseArrivals markAt (base.shift t ω) =
        (fun u : ℝ => u - t) '' trueMarkedPointSet H.baseArrivals markAt ω)
    (p : ℝ)
    (htrueMass : (targetPassiveTaggedArrivalAtZero tagged passive).Ptag
      (targetPassiveTagMark tagMark ⁻¹' ({true} : Set Bool)) = ENNReal.ofReal p)
    (htrue_ne_zero : (targetPassiveTaggedArrivalAtZero tagged passive).Ptag
      (targetPassiveTagMark tagMark ⁻¹' ({true} : Set Bool)) ≠ 0)
    (hselectedRate : 0 < H.arrivalRate * p) :
    MarkedCampbellPalmTaggedArrivalCertificate
      (targetPassiveProductBaseLaw base passive)
      ((targetPassiveTaggedArrivalAtZero tagged passive).conditionOn
        (targetPassiveTagMark tagMark ⁻¹' ({true} : Set Bool)) htrue_ne_zero) := by
  let Hprod := targetPassiveCampbellCertificate H passive hpassiveFlow
  exact markedCampbellCertificate_conditionOnTrue Hprod
    (targetPassiveTagMark tagMark)
    (measurable_targetPassiveTagMark tagMark htagMark)
    (targetPassiveMarkAt markAt)
    (fun x i => targetPassive_mark_recenter H passive tagMark markAt hmark x i)
    (by
      simpa only [Hprod, targetPassiveCampbellCertificate] using
        targetPassive_trueMarkedPointSet_shift H passive markAt hpointShift)
    p htrueMass htrue_ne_zero hselectedRate

/-- Convenience form of the genuine selected lift when the target
zero-coordinate true-mark mass has already been proved under the original
target tagged law. -/
noncomputable def targetPassiveMarkedCampbellCertificate_conditionOnTrue_of_targetMass
    {Ωbase Ωtag Γ : Type*}
    [MeasurableSpace Ωbase] [MeasurableSpace Ωtag] [MeasurableSpace Γ]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (passive : ShiftInvariantProbabilityLaw Γ)
    (hpassiveFlow : Measurable (Function.uncurry passive.shift))
    (tagMark : Ωtag → Bool) (htagMark : Measurable tagMark)
    (markAt : Ωbase → ℤ → Bool)
    (hmark : ∀ ω i, markAt ω i = tagMark (H.recenterAt ω i))
    (hpointShift : ∀ t, ∀ᵐ ω ∂base.Pbase,
      trueMarkedPointSet H.baseArrivals markAt (base.shift t ω) =
        (fun u : ℝ => u - t) '' trueMarkedPointSet H.baseArrivals markAt ω)
    (p : ℝ)
    (htrueMass : tagged.Ptag (tagMark ⁻¹' ({true} : Set Bool)) = ENNReal.ofReal p)
    (htrue_ne_zero : tagged.Ptag (tagMark ⁻¹' ({true} : Set Bool)) ≠ 0)
    (hselectedRate : 0 < H.arrivalRate * p) :
    MarkedCampbellPalmTaggedArrivalCertificate
      (targetPassiveProductBaseLaw base passive)
      ((targetPassiveTaggedArrivalAtZero tagged passive).conditionOn
        (targetPassiveTagMark tagMark ⁻¹' ({true} : Set Bool))
        (by
          rw [targetPassiveTagMark_true_mass tagged passive tagMark]
          exact htrue_ne_zero)) := by
  exact targetPassiveMarkedCampbellCertificate_conditionOnTrue
    H passive hpassiveFlow tagMark htagMark markAt hmark hpointShift p
    (by
      rw [targetPassiveTagMark_true_mass tagged passive tagMark]
      exact htrueMass)
    (by
      rw [targetPassiveTagMark_true_mass tagged passive tagMark]
      exact htrue_ne_zero)
    hselectedRate

end

end AppliedModelingLib.Probability.Palm
