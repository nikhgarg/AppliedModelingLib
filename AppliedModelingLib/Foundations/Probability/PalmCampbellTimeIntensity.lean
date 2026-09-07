import AppliedModelingLib.Foundations.Probability.PalmCampbellFunctional
import Mathlib.MeasureTheory.Group.Prod

/-!
# Arrival-time Campbell intensity

For a genuine Campbell/Palm certificate and a nonnegative tagged reward, this
module defines the induced measure on physical time.  The construction is a
countable sum of the literal labelled-arrival pushforwards; later results can
identify it with a multiple of Lebesgue measure from concrete translation
covariance.
-/

namespace AppliedModelingLib.Probability.Palm

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- Adding a measurable, sample-dependent origin to a Lebesgue-time
coordinate preserves the corresponding product measure.  This is the
measure-theoretic bridge from elapsed time after a random arrival to its
physical-time epoch. -/
theorem measurePreserving_prod_add_measurable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    (origin : Ω → ℝ) (horigin : Measurable origin) :
    MeasurePreserving (fun p : Ω × ℝ => (p.1, origin p.1 + p.2))
      (μ.prod volume) (μ.prod volume) := by
  refine MeasurePreserving.skew_product (g := fun omega time => origin omega + time)
    (MeasurePreserving.id μ) ?_ ?_
  · exact (horigin.comp measurable_fst).add measurable_snd
  · filter_upwards [] with omega
    exact map_add_left_eq_self volume (origin omega)

/-- The same random-origin translation, with physical time placed first.
This is the form used to pull a product-almost-everywhere statement about a
stationary trajectory back to arrival-labelled elapsed-time coordinates. -/
theorem measurePreserving_prod_add_measurable_swap
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    (origin : Ω → ℝ) (horigin : Measurable origin) :
    MeasurePreserving (fun p : Ω × ℝ => (origin p.1 + p.2, p.1))
      (μ.prod volume) (volume.prod μ) := by
  simpa only [Function.comp_apply] using
    MeasurePreserving.comp Measure.measurePreserving_swap
      (measurePreserving_prod_add_measurable μ origin horigin)

/-- A product-almost-everywhere equality can be read in the opposite order of
its two coordinates.  This is the Fubini section form used when a jointly
measurable reward is compared with a time-indexed reward. -/
theorem ae_ae_of_ae_prod_swap
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableEq γ]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {f g : α → β → γ}
    (hf : Measurable (Function.uncurry f))
    (hg : Measurable (Function.uncurry g))
    (hfg : (fun p : α × β => f p.1 p.2) =ᵐ[μ.prod ν]
      fun p => g p.1 p.2) :
    ∀ᵐ y : β ∂ν, ∀ᵐ x : α ∂μ, f x y = g x y := by
  have hswapmeas : MeasurableSet {p : β × α | f p.2 p.1 = g p.2 p.1} := by
    apply measurableSet_eq_fun
    · exact hf.comp (measurable_snd.prodMk measurable_fst)
    · exact hg.comp (measurable_snd.prodMk measurable_fst)
  have hswap : ∀ᵐ p : β × α ∂(ν.prod μ), f p.2 p.1 = g p.2 p.1 := by
    have hmap : ∀ᵐ p : β × α ∂Measure.map Prod.swap (μ.prod ν),
        f p.2 p.1 = g p.2 p.1 := by
      rw [MeasureTheory.ae_map_iff measurable_swap.aemeasurable hswapmeas]
      simpa [Prod.swap] using hfg
    rwa [Measure.prod_swap] at hmap
  exact MeasureTheory.Measure.ae_ae_of_ae_prod hswap

/-- Recentring an elapsed-time integral at a measurable sample-dependent
origin is a literal change of variables on the product measure.  The result
is deliberately stated before any Palm or queueing specialization: it is the
analytic time-shear used to compare customer coverage with physical-time
state occupation. -/
theorem lintegral_arrivalTimeShear_indicator_eq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    (origin : Ω → ℝ) (horigin : Measurable origin)
    (F : ℝ × Ω → ℝ≥0∞) (hF : Measurable F) (a b : ℝ) :
    (∫⁻ p : Ω × ℝ,
      if origin p.1 + p.2 ∈ Set.Ico a b then F (origin p.1 + p.2, p.1) else 0
        ∂(μ.prod volume)) =
      ∫⁻ p : ℝ × Ω, if p.1 ∈ Set.Ico a b then F p else 0 ∂(volume.prod μ) := by
  let G : ℝ × Ω → ℝ≥0∞ := fun p => if p.1 ∈ Set.Ico a b then F p else 0
  have hG : Measurable G := by
    exact Measurable.ite ((measurable_fst) measurableSet_Ico) hF measurable_const
  simpa [G] using
    (measurePreserving_prod_add_measurable_swap μ origin horigin).lintegral_comp hG

/-- The physical-time intensity of a nonnegative tagged reward.  It sums the
literal reward carried by every labelled base arrival, rather than assuming a
reward-rate formula. -/
noncomputable def arrivalTimeCampbellIntensity
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (f : Ωtag → ℝ≥0∞) : Measure ℝ :=
  Measure.sum fun i : ℤ =>
    Measure.map (H.baseArrivals · i)
      (base.Pbase.withDensity (fun omega => f (H.recenterAt omega i)))

/-- Translate a physical-time event set forward by `t`.  The preimage form
keeps its measurable-space behavior explicit. -/
def arrivalTimeTranslateSet (t : ℝ) (s : Set ℝ) : Set ℝ :=
  (fun u : ℝ => u - t) ⁻¹' s

theorem measurableSet_arrivalTimeTranslateSet (t : ℝ) {s : Set ℝ}
    (hs : MeasurableSet s) :
    MeasurableSet (arrivalTimeTranslateSet t s) := by
  exact (measurable_id.sub measurable_const) hs

/-- The base event that a fixed label lies in a physical half-open time
window. -/
def arrivalTimeCampbellWindowSet
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (a b : ℝ) (i : ℤ) : Set Ωbase :=
  {omega | a ≤ H.baseArrivals omega i ∧ H.baseArrivals omega i < b}

theorem measurableSet_arrivalTimeCampbellWindowSet
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (a b : ℝ) (i : ℤ) :
    MeasurableSet (arrivalTimeCampbellWindowSet H a b i) := by
  exact (measurableSet_le measurable_const (H.baseArrivals_measurable i)).inter
    (measurableSet_lt (H.baseArrivals_measurable i) measurable_const)

/-- One labelled contribution to a physical-time Campbell intensity. -/
noncomputable def arrivalTimeCampbellWeightedSummand
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (f : Ωtag → ℝ≥0∞) (a b : ℝ) (i : ℤ) : Ωbase → ℝ≥0∞ := by
  classical
  exact fun omega => if omega ∈ arrivalTimeCampbellWindowSet H a b i then
    f (H.recenterAt omega i) else 0

theorem measurable_arrivalTimeCampbellWeightedSummand
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (f : Ωtag → ℝ≥0∞) (hf : Measurable f) (a b : ℝ) (i : ℤ) :
    Measurable (arrivalTimeCampbellWeightedSummand H f a b i) := by
  classical
  change Measurable (fun omega => if omega ∈ arrivalTimeCampbellWindowSet H a b i then
    f (H.recenterAt omega i) else 0)
  exact Measurable.ite (measurableSet_arrivalTimeCampbellWindowSet H a b i)
    (hf.comp (H.recenterAt_measurable i)) measurable_const

/-- One labelled contribution to the weighted intensity of an arbitrary
measurable physical-time set. -/
noncomputable def arrivalTimeCampbellSetWeightedSummand
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (f : Ωtag → ℝ≥0∞) (s : Set ℝ) (i : ℤ) : Ωbase → ℝ≥0∞ := by
  classical
  exact fun omega => if H.baseArrivals omega i ∈ s then f (H.recenterAt omega i) else 0

theorem measurable_arrivalTimeCampbellSetWeightedSummand
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (f : Ωtag → ℝ≥0∞) (hf : Measurable f)
    (s : Set ℝ) (hs : MeasurableSet s) (i : ℤ) :
    Measurable (arrivalTimeCampbellSetWeightedSummand H f s i) := by
  classical
  change Measurable (fun omega => if H.baseArrivals omega i ∈ s then
    f (H.recenterAt omega i) else 0)
  exact Measurable.ite ((H.baseArrivals_measurable i) hs)
    (hf.comp (H.recenterAt_measurable i)) measurable_const

/-- The weighted time intensity of every measurable time set is the Tonelli
integral of its literal countable labelled-arrival sum. -/
theorem arrivalTimeCampbellIntensity_apply_eq_lintegral_tsum
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (f : Ωtag → ℝ≥0∞) (hf : Measurable f)
    (s : Set ℝ) (hs : MeasurableSet s) :
    arrivalTimeCampbellIntensity H f s =
      ∫⁻ omega, ∑' i : ℤ,
        arrivalTimeCampbellSetWeightedSummand H f s i omega ∂base.Pbase := by
  classical
  calc
    arrivalTimeCampbellIntensity H f s = ∑' i : ℤ,
        Measure.map (H.baseArrivals · i)
          (base.Pbase.withDensity (fun omega => f (H.recenterAt omega i))) s := by
      rw [arrivalTimeCampbellIntensity]
      exact Measure.sum_apply _ hs
    _ = ∑' i : ℤ, ∫⁻ omega in
        (H.baseArrivals · i) ⁻¹' s, f (H.recenterAt omega i) ∂base.Pbase := by
      apply tsum_congr
      intro i
      rw [Measure.map_apply (H.baseArrivals_measurable i) hs]
      exact withDensity_apply _ ((H.baseArrivals_measurable i) hs)
    _ = ∫⁻ omega, ∑' i : ℤ,
        arrivalTimeCampbellSetWeightedSummand H f s i omega ∂base.Pbase := by
      symm
      rw [MeasureTheory.lintegral_tsum]
      · apply tsum_congr
        intro i
        calc
          (∫⁻ omega, arrivalTimeCampbellSetWeightedSummand H f s i omega ∂base.Pbase) =
              ∫⁻ omega, ((H.baseArrivals · i) ⁻¹' s).indicator
                (fun omega => f (H.recenterAt omega i)) omega ∂base.Pbase := by
                apply MeasureTheory.lintegral_congr
                intro omega
                by_cases hi : H.baseArrivals omega i ∈ s <;>
                  simp [arrivalTimeCampbellSetWeightedSummand, hi]
          _ = ∫⁻ omega in (H.baseArrivals · i) ⁻¹' s,
              f (H.recenterAt omega i) ∂base.Pbase :=
            MeasureTheory.lintegral_indicator ((H.baseArrivals_measurable i) hs) _
      · intro i
        exact (measurable_arrivalTimeCampbellSetWeightedSummand H f hf s hs i).aemeasurable

/-- One labelled customer contribution to a physical-time coverage functional.
The second coordinate is elapsed time after that customer's arrival, so a
queueing application can make the contribution nonzero precisely while the
customer is waiting. -/
noncomputable def arrivalTimeCampbellCoverageSummand
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (g : Ωtag → ℝ → ℝ≥0∞) (s : Set ℝ) (i : ℤ) : Ωbase × ℝ → ℝ≥0∞ := by
  classical
  exact fun p => if H.baseArrivals p.1 i + p.2 ∈ s then
    g (H.recenterAt p.1 i) p.2 else 0

theorem measurable_arrivalTimeCampbellCoverageSummand
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (g : Ωtag → ℝ → ℝ≥0∞) (hg : Measurable (Function.uncurry g))
    (s : Set ℝ) (hs : MeasurableSet s) (i : ℤ) :
    Measurable (arrivalTimeCampbellCoverageSummand H g s i) := by
  classical
  change Measurable (fun p : Ωbase × ℝ => if H.baseArrivals p.1 i + p.2 ∈ s then
    g (H.recenterAt p.1 i) p.2 else 0)
  exact Measurable.ite
    ((((H.baseArrivals_measurable i).comp measurable_fst).add measurable_snd) hs)
    (hg.comp ((H.recenterAt_measurable i).comp measurable_fst |>.prodMk measurable_snd))
    measurable_const

/-- The literal expected customer coverage of a physical time set.  Unlike
an arrival reward, a customer's mass is spread over its elapsed-time
coordinate. -/
noncomputable def arrivalTimeCampbellCoverage
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (g : Ωtag → ℝ → ℝ≥0∞) (s : Set ℝ) : ℝ≥0∞ :=
  ∫⁻ p, ∑' i : ℤ, arrivalTimeCampbellCoverageSummand H g s i p ∂
    (base.Pbase.prod MeasureTheory.volume)

/-- A coverage functional over a physical half-open interval can be expanded
as a countable sum of physical-time integrals, one for each labelled arrival.
The elapsed time in the customer reward is translated back from physical time
by that label's arrival epoch.  This is only Tonelli and the measurable
time-shear; no state-occupation equality is used here. -/
theorem arrivalTimeCampbellCoverage_Ico_eq_tsum_physicalTime
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (g : Ωtag → ℝ → ℝ≥0∞) (hg : Measurable (Function.uncurry g))
    (a b : ℝ) :
    arrivalTimeCampbellCoverage H g (Set.Ico a b) =
      ∑' i : ℤ, ∫⁻ p : ℝ × Ωbase,
        if p.1 ∈ Set.Ico a b then
          g (H.recenterAt p.2 i) (p.1 - H.baseArrivals p.2 i)
        else 0 ∂(MeasureTheory.volume.prod base.Pbase) := by
  classical
  letI : IsProbabilityMeasure base.Pbase := base.isProbability
  letI : SFinite base.Pbase := by infer_instance
  unfold arrivalTimeCampbellCoverage
  rw [MeasureTheory.lintegral_tsum]
  · apply tsum_congr
    intro i
    let F : ℝ × Ωbase → ℝ≥0∞ := fun p =>
      g (H.recenterAt p.2 i) (p.1 - H.baseArrivals p.2 i)
    have hF : Measurable F := by
      exact hg.comp
        ((H.recenterAt_measurable i).comp measurable_snd |>.prodMk
          (measurable_fst.sub ((H.baseArrivals_measurable i).comp measurable_snd)))
    simpa [arrivalTimeCampbellCoverageSummand, F] using
      (lintegral_arrivalTimeShear_indicator_eq base.Pbase
        (H.baseArrivals · i) (H.baseArrivals_measurable i) F hF a b)
  · intro i
    exact (measurable_arrivalTimeCampbellCoverageSummand H g hg (Set.Ico a b)
      measurableSet_Ico i).aemeasurable

/-- Spreading every labelled customer's reward over elapsed time is exactly
the integral of the ordinary arrival-time intensity evaluated on the
corresponding translated physical window.  This is Tonelli plus the literal
change of membership `arrival + elapsed ∈ s`; it assumes no queue-state
identity. -/
theorem arrivalTimeCampbellCoverage_eq_lintegral_arrivalTimeCampbellIntensity_Ico
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (g : Ωtag → ℝ → ℝ≥0∞) (hg : Measurable (Function.uncurry g))
    (a b : ℝ) :
    arrivalTimeCampbellCoverage H g (Set.Ico a b) =
      ∫⁻ elapsed : ℝ,
        arrivalTimeCampbellIntensity H (fun z => g z elapsed)
          (Set.Ico (a - elapsed) (b - elapsed)) ∂MeasureTheory.volume := by
  classical
  letI : IsProbabilityMeasure base.Pbase := base.isProbability
  letI : SFinite base.Pbase := by infer_instance
  let F : (Ωbase × ℝ) → ℝ≥0∞ := fun p => ∑' i : ℤ,
    arrivalTimeCampbellCoverageSummand H g (Set.Ico a b) i p
  let G : ℝ → Ωbase → ℝ≥0∞ := fun elapsed omega => ∑' i : ℤ,
    arrivalTimeCampbellSetWeightedSummand H (fun z => g z elapsed)
      (Set.Ico (a - elapsed) (b - elapsed)) i omega
  have hslice : ∀ elapsed : ℝ, Measurable (fun z : Ωtag => g z elapsed) := by
    intro elapsed
    exact hg.comp (measurable_id.prodMk measurable_const)
  have hFmeas : Measurable F := by
    apply Measurable.ennreal_tsum
    intro i
    exact measurable_arrivalTimeCampbellCoverageSummand H g hg (Set.Ico a b)
      measurableSet_Ico i
  have hpoint : ∀ p : Ωbase × ℝ, F p = G p.2 p.1 := by
    intro p
    apply tsum_congr
    intro i
    unfold arrivalTimeCampbellCoverageSummand
      arrivalTimeCampbellSetWeightedSummand
    have hmem : H.baseArrivals p.1 i + p.2 ∈ Set.Ico a b ↔
        H.baseArrivals p.1 i ∈ Set.Ico (a - p.2) (b - p.2) := by
      constructor <;> intro hp
      · exact ⟨by linarith [hp.1], by linarith [hp.2]⟩
      · exact ⟨by linarith [hp.1], by linarith [hp.2]⟩
    simp only [hmem]
  calc
    arrivalTimeCampbellCoverage H g (Set.Ico a b) =
        ∫⁻ p, F p ∂(base.Pbase.prod MeasureTheory.volume) := rfl
    _ = ∫⁻ elapsed : ℝ, ∫⁻ omega : Ωbase, G elapsed omega ∂base.Pbase
        ∂MeasureTheory.volume := by
          rw [MeasureTheory.lintegral_prod_symm' F hFmeas]
          apply MeasureTheory.lintegral_congr
          intro elapsed
          apply MeasureTheory.lintegral_congr
          intro omega
          exact hpoint (omega, elapsed)
    _ = ∫⁻ elapsed : ℝ,
        arrivalTimeCampbellIntensity H (fun z => g z elapsed)
          (Set.Ico (a - elapsed) (b - elapsed)) ∂MeasureTheory.volume := by
          apply MeasureTheory.lintegral_congr
          intro elapsed
          exact (arrivalTimeCampbellIntensity_apply_eq_lintegral_tsum H
            (fun z => g z elapsed) (hslice elapsed)
            (Set.Ico (a - elapsed) (b - elapsed)) measurableSet_Ico).symm

/-- If every elapsed-time slice has the stated ordinary Campbell intensity,
then the literal customer coverage of a physical interval is its interval
length times the Palm integral of the elapsed-time reward.  The hypothesis is
an intensity equality to be proved by the concrete input model; this theorem
only performs the source-neutral Tonelli and time-translation calculation. -/
theorem arrivalTimeCampbellCoverage_Ico_eq_rate_mul_lintegral
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (g : Ωtag → ℝ → ℝ≥0∞) (hg : Measurable (Function.uncurry g))
    (rate : ℝ≥0∞)
    (hfull : ∀ elapsed : ℝ,
      arrivalTimeCampbellIntensity H (fun z => g z elapsed) =
        (rate * ∫⁻ z, g z elapsed ∂tagged.Ptag) •
          (MeasureTheory.volume : Measure ℝ))
    (a b : ℝ) :
    arrivalTimeCampbellCoverage H g (Set.Ico a b) =
      (rate * ENNReal.ofReal (b - a)) *
        ∫⁻ p : Ωtag × ℝ, g p.1 p.2 ∂(tagged.Ptag.prod MeasureTheory.volume) := by
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : SFinite tagged.Ptag := by infer_instance
  have hsection : Measurable (fun elapsed : ℝ =>
      ∫⁻ z, g z elapsed ∂tagged.Ptag) :=
    hg.lintegral_prod_left
  calc
    arrivalTimeCampbellCoverage H g (Set.Ico a b) =
        ∫⁻ elapsed : ℝ,
          arrivalTimeCampbellIntensity H (fun z => g z elapsed)
            (Set.Ico (a - elapsed) (b - elapsed)) ∂MeasureTheory.volume :=
      arrivalTimeCampbellCoverage_eq_lintegral_arrivalTimeCampbellIntensity_Ico H g hg a b
    _ = ∫⁻ elapsed : ℝ,
        ((rate * ∫⁻ z, g z elapsed ∂tagged.Ptag) •
          (MeasureTheory.volume : Measure ℝ))
          (Set.Ico (a - elapsed) (b - elapsed)) ∂MeasureTheory.volume := by
            apply MeasureTheory.lintegral_congr
            intro elapsed
            exact congrArg (fun μ : Measure ℝ =>
              μ (Set.Ico (a - elapsed) (b - elapsed))) (hfull elapsed)
    _ = ∫⁻ elapsed : ℝ,
        rate * (∫⁻ z, g z elapsed ∂tagged.Ptag) * ENNReal.ofReal (b - a)
          ∂MeasureTheory.volume := by
            apply MeasureTheory.lintegral_congr
            intro elapsed
            rw [Measure.smul_apply, Real.volume_Ico]
            congr 2
            ring_nf
    _ = ∫⁻ elapsed : ℝ,
        (rate * ENNReal.ofReal (b - a)) *
          (∫⁻ z, g z elapsed ∂tagged.Ptag) ∂MeasureTheory.volume := by
            apply MeasureTheory.lintegral_congr
            intro elapsed
            ring
    _ = (rate * ENNReal.ofReal (b - a)) *
        ∫⁻ elapsed : ℝ, (∫⁻ z, g z elapsed ∂tagged.Ptag) ∂MeasureTheory.volume := by
          rw [MeasureTheory.lintegral_const_mul _ hsection]
    _ = (rate * ENNReal.ofReal (b - a)) *
        ∫⁻ p : Ωtag × ℝ, g p.1 p.2 ∂(tagged.Ptag.prod MeasureTheory.volume) := by
          congr 1
          simpa only [Function.uncurry] using
            (MeasureTheory.lintegral_prod_symm' (Function.uncurry g) hg).symm

/-- The almost-everywhere form of
`arrivalTimeCampbellCoverage_Ico_eq_rate_mul_lintegral`.  Null elapsed-time
slices do not affect either side of the Tonelli calculation. -/
theorem arrivalTimeCampbellCoverage_Ico_eq_rate_mul_lintegral_ae
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (g : Ωtag → ℝ → ℝ≥0∞) (hg : Measurable (Function.uncurry g))
    (rate : ℝ≥0∞)
    (hfull : ∀ᵐ elapsed : ℝ ∂MeasureTheory.volume,
      arrivalTimeCampbellIntensity H (fun z => g z elapsed) =
        (rate * ∫⁻ z, g z elapsed ∂tagged.Ptag) •
          (MeasureTheory.volume : Measure ℝ))
    (a b : ℝ) :
    arrivalTimeCampbellCoverage H g (Set.Ico a b) =
      (rate * ENNReal.ofReal (b - a)) *
        ∫⁻ p : Ωtag × ℝ, g p.1 p.2 ∂(tagged.Ptag.prod MeasureTheory.volume) := by
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : SFinite tagged.Ptag := by infer_instance
  have hsection : Measurable (fun elapsed : ℝ =>
      ∫⁻ z, g z elapsed ∂tagged.Ptag) :=
    hg.lintegral_prod_left
  calc
    arrivalTimeCampbellCoverage H g (Set.Ico a b) =
        ∫⁻ elapsed : ℝ,
          arrivalTimeCampbellIntensity H (fun z => g z elapsed)
            (Set.Ico (a - elapsed) (b - elapsed)) ∂MeasureTheory.volume :=
      arrivalTimeCampbellCoverage_eq_lintegral_arrivalTimeCampbellIntensity_Ico H g hg a b
    _ = ∫⁻ elapsed : ℝ,
        ((rate * ∫⁻ z, g z elapsed ∂tagged.Ptag) •
          (MeasureTheory.volume : Measure ℝ))
          (Set.Ico (a - elapsed) (b - elapsed)) ∂MeasureTheory.volume := by
            apply MeasureTheory.lintegral_congr_ae
            filter_upwards [hfull] with elapsed helapsed
            exact congrArg (fun μ : Measure ℝ =>
              μ (Set.Ico (a - elapsed) (b - elapsed))) helapsed
    _ = ∫⁻ elapsed : ℝ,
        rate * (∫⁻ z, g z elapsed ∂tagged.Ptag) * ENNReal.ofReal (b - a)
          ∂MeasureTheory.volume := by
            apply MeasureTheory.lintegral_congr
            intro elapsed
            rw [Measure.smul_apply, Real.volume_Ico]
            congr 2
            ring_nf
    _ = ∫⁻ elapsed : ℝ,
        (rate * ENNReal.ofReal (b - a)) *
          (∫⁻ z, g z elapsed ∂tagged.Ptag) ∂MeasureTheory.volume := by
            apply MeasureTheory.lintegral_congr
            intro elapsed
            ring
    _ = (rate * ENNReal.ofReal (b - a)) *
        ∫⁻ elapsed : ℝ, (∫⁻ z, g z elapsed ∂tagged.Ptag) ∂MeasureTheory.volume := by
          rw [MeasureTheory.lintegral_const_mul _ hsection]
    _ = (rate * ENNReal.ofReal (b - a)) *
        ∫⁻ p : Ωtag × ℝ, g p.1 p.2 ∂(tagged.Ptag.prod MeasureTheory.volume) := by
          congr 1
          simpa only [Function.uncurry] using
            (MeasureTheory.lintegral_prod_symm' (Function.uncurry g) hg).symm

/-- The finite literal reward sum over a time window is almost surely the
countable Tonelli sum associated with the arrival-time intensity. -/
theorem ae_sum_arrivalsIn_recenter_eq_tsum_arrivalTimeCampbell
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (f : Ωtag → ℝ≥0∞) (a b : ℝ) :
    ∀ᵐ omega ∂base.Pbase,
      (∑ i ∈ H.arrivalsIn a b omega, f (H.recenterAt omega i)) =
        ∑' i : ℤ, arrivalTimeCampbellWeightedSummand H f a b i omega := by
  filter_upwards [H.arrivalsIn_spec a b] with omega hspec
  classical
  rw [tsum_eq_sum (s := H.arrivalsIn a b omega)]
  · apply Finset.sum_congr rfl
    intro i hi
    have hwindow : omega ∈ arrivalTimeCampbellWindowSet H a b i := (hspec i).mp hi
    simp [arrivalTimeCampbellWeightedSummand, hwindow]
  · intro i hi
    have hnotwindow : omega ∉ arrivalTimeCampbellWindowSet H a b i := by
      intro hwindow
      exact hi ((hspec i).mpr hwindow)
    simp [arrivalTimeCampbellWeightedSummand, hnotwindow]

/-- On every physical half-open window, the arrival-time intensity is exactly
the expected literal finite reward sum over the certificate's arrival ledger. -/
theorem arrivalTimeCampbellIntensity_apply_Ico
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (f : Ωtag → ℝ≥0∞) (hf : Measurable f) (a b : ℝ) :
    arrivalTimeCampbellIntensity H f (Set.Ico a b) =
      ∫⁻ omega, (∑ i ∈ H.arrivalsIn a b omega,
        f (H.recenterAt omega i)) ∂base.Pbase := by
  classical
  let g : ℤ → Measure ℝ := fun i =>
    Measure.map (H.baseArrivals · i)
      (base.Pbase.withDensity (fun omega => f (H.recenterAt omega i)))
  calc
    arrivalTimeCampbellIntensity H f (Set.Ico a b) = ∑' i : ℤ, g i (Set.Ico a b) := by
      rw [arrivalTimeCampbellIntensity]
      exact Measure.sum_apply _ measurableSet_Ico
    _ = ∑' i : ℤ, ∫⁻ omega in arrivalTimeCampbellWindowSet H a b i,
        f (H.recenterAt omega i) ∂base.Pbase := by
      apply tsum_congr
      intro i
      change Measure.map (H.baseArrivals · i)
        (base.Pbase.withDensity (fun omega => f (H.recenterAt omega i)))
          (Set.Ico a b) = _
      rw [Measure.map_apply (H.baseArrivals_measurable i) measurableSet_Ico]
      change (base.Pbase.withDensity (fun omega => f (H.recenterAt omega i)))
        (arrivalTimeCampbellWindowSet H a b i) = _
      exact withDensity_apply _ (measurableSet_arrivalTimeCampbellWindowSet H a b i)
    _ = ∫⁻ omega, ∑' i : ℤ,
        arrivalTimeCampbellWeightedSummand H f a b i omega ∂base.Pbase := by
      symm
      rw [MeasureTheory.lintegral_tsum]
      · apply tsum_congr
        intro i
        calc
          (∫⁻ omega, arrivalTimeCampbellWeightedSummand H f a b i omega ∂base.Pbase) =
              ∫⁻ omega, (arrivalTimeCampbellWindowSet H a b i).indicator
                (fun omega => f (H.recenterAt omega i)) omega ∂base.Pbase := by
                apply MeasureTheory.lintegral_congr
                intro omega
                by_cases hi : omega ∈ arrivalTimeCampbellWindowSet H a b i <;>
                  simp [arrivalTimeCampbellWeightedSummand, hi]
          _ = ∫⁻ omega in arrivalTimeCampbellWindowSet H a b i,
              f (H.recenterAt omega i) ∂base.Pbase :=
            MeasureTheory.lintegral_indicator
              (measurableSet_arrivalTimeCampbellWindowSet H a b i) _
      · intro i
        exact (measurable_arrivalTimeCampbellWeightedSummand H f hf a b i).aemeasurable
    _ = ∫⁻ omega, (∑ i ∈ H.arrivalsIn a b omega,
        f (H.recenterAt omega i)) ∂base.Pbase := by
      apply MeasureTheory.lintegral_congr_ae
      exact (ae_sum_arrivalsIn_recenter_eq_tsum_arrivalTimeCampbell H f a b).mono
        fun _ h => h.symm

/-- The weighted arrival-time intensity of the unit interval is the genuine
Campbell rate times the tagged reward expectation. -/
theorem arrivalTimeCampbellIntensity_unit
    {Ωbase Ωtag : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    {base : ShiftInvariantProbabilityLaw Ωbase}
    {tagged : Queueing.TaggedArrivalAtZero Ωtag}
    (H : CampbellPalmTaggedArrivalCertificate base tagged)
    (f : Ωtag → ℝ≥0∞) (hf : Measurable f) :
    arrivalTimeCampbellIntensity H f (Set.Ico 0 1) =
      ENNReal.ofReal H.arrivalRate * (∫⁻ z, f z ∂tagged.Ptag) := by
  classical
  let g : ℤ → Measure ℝ := fun i =>
    Measure.map (H.baseArrivals · i)
      (base.Pbase.withDensity (fun omega => f (H.recenterAt omega i)))
  calc
    arrivalTimeCampbellIntensity H f (Set.Ico 0 1) = ∑' i : ℤ, g i (Set.Ico 0 1) := by
      rw [arrivalTimeCampbellIntensity]
      exact Measure.sum_apply _ measurableSet_Ico
    _ = ∑' i : ℤ, ∫⁻ omega in unitWindowArrivalSet H i,
        f (H.recenterAt omega i) ∂base.Pbase := by
      apply tsum_congr
      intro i
      change Measure.map (H.baseArrivals · i)
        (base.Pbase.withDensity (fun omega => f (H.recenterAt omega i)))
          (Set.Ico 0 1) = _
      rw [Measure.map_apply (H.baseArrivals_measurable i) measurableSet_Ico]
      change (base.Pbase.withDensity (fun omega => f (H.recenterAt omega i)))
        (unitWindowArrivalSet H i) = _
      exact withDensity_apply _ (measurableSet_unitWindowArrivalSet H i)
    _ = ∫⁻ omega, ∑' i : ℤ,
        unitWindowCampbellWeightedSummand H f i omega ∂base.Pbase := by
      symm
      rw [MeasureTheory.lintegral_tsum]
      · apply tsum_congr
        intro i
        calc
          (∫⁻ omega, unitWindowCampbellWeightedSummand H f i omega ∂base.Pbase) =
              ∫⁻ omega, (unitWindowArrivalSet H i).indicator
                (fun omega => f (H.recenterAt omega i)) omega ∂base.Pbase := by
                apply MeasureTheory.lintegral_congr
                intro omega
                by_cases hi : omega ∈ unitWindowArrivalSet H i <;>
                  simp [unitWindowCampbellWeightedSummand, hi]
          _ = ∫⁻ omega in unitWindowArrivalSet H i,
              f (H.recenterAt omega i) ∂base.Pbase :=
            MeasureTheory.lintegral_indicator (measurableSet_unitWindowArrivalSet H i) _
      · intro i
        exact (measurable_unitWindowCampbellWeightedSummand H f hf i).aemeasurable
    _ = ENNReal.ofReal H.arrivalRate * (∫⁻ z, f z ∂tagged.Ptag) :=
      lintegral_tsum_unitWindowCampbellWeightedSummand H f hf

end

end AppliedModelingLib.Probability.Palm
