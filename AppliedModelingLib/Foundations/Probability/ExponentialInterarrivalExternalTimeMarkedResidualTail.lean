import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalDeterministicResidualTail
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalForwardPoisson
import AppliedModelingLib.Foundations.Probability.IidStatePrefixStopping

/-!
# Marked exponential renewal tails at an independent external time

This module extends the external-time residual construction by carrying an
IID mark stream at the renewal-count-selected suffix.  The result is a
product-space law, derived from the exponential residual-tail theorem and the
externally indexed IID-tail theorem; it is not a strong-Markov assumption.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory ProbabilityTheory Filter

noncomputable section

/-- The marked future of an exponential renewal stream after an external
clock time: its residual gap path and the IID mark suffix after the arrivals
strictly before that clock time. -/
def externalTimeMarkedResidualTail
    {β α : Type*} [MeasurableSpace β] (time : β → Real) :
    (β × (Nat -> Real)) × (Nat -> α) -> (Nat -> Real) × (Nat -> α) :=
  fun z =>
    (externalTimeResidualTail time z.1,
      IIDStream.externalIndexTail
        (fun h : β × (Nat -> Real) => canonicalRenewalCount (time h.1) h.2)
        z)

/-- The marked external-time residual map is Borel measurable. -/
theorem measurable_externalTimeMarkedResidualTail
    {β α : Type*} [MeasurableSpace β] [MeasurableSpace α]
    (time : β -> Real) (htime : Measurable time) :
    Measurable (externalTimeMarkedResidualTail (α := α) time) := by
  let index : β × (Nat -> Real) -> Nat :=
    fun h => canonicalRenewalCount (time h.1) h.2
  have hindex : Measurable index := by
    exact measurable_canonicalRenewalCount_joint.comp
      ((htime.comp measurable_fst).prodMk measurable_snd)
  exact ((measurable_externalTimeResidualTail time htime).comp measurable_fst).prodMk
    (IIDStream.measurable_externalIndexTail (α := α) index hindex)

/-- Restarting a marked exponential renewal input at `s` and then after a
further nonnegative duration `h` is almost surely the literal marked input
obtained by restarting once at `s + h`.  The mark suffix identity follows
from the same renewal-count cocycle as the gap residual; it is path algebra,
not a postulated strong-Markov restart. -/
theorem ae_externalTimeMarkedResidualTail_add_eq_comp
    {α : Type*} [MeasurableSpace α] (markLaw : Measure α)
    [IsProbabilityMeasure markLaw]
    {rate s h : Real}
    (hrate : 0 < rate) (hh : 0 ≤ h) :
    ∀ᵐ z ∂((exponentialInterarrivalMeasure rate).prod (IIDStream.measure markLaw)),
      externalTimeMarkedResidualTail (α := α) (fun _ : Unit => s + h)
        (((), z.1), z.2) =
      externalTimeMarkedResidualTail (α := α) (fun _ : Unit => h)
        (((), residualTail s z.1),
          IIDStream.externalIndexTail
            (fun _ : Unit => canonicalRenewalCount s z.1) ((), z.2)) := by
  let gaps : Measure (Nat -> Real) := exponentialInterarrivalMeasure rate
  let marks : Measure (Nat -> α) := IIDStream.measure markLaw
  letI : IsProbabilityMeasure marks := by
    dsimp [marks, IIDStream.measure]
    infer_instance
  have hfst : Measure.map Prod.fst (gaps.prod marks) = gaps := by simp
  have hcountSource : ∀ᵐ z ∂gaps.prod marks,
      canonicalRenewalCount (s + h) z.1 =
        canonicalRenewalCount s z.1 + canonicalRenewalCount h (residualTail s z.1) := by
    refine ae_of_ae_map (μ := gaps.prod marks) (f := Prod.fst)
      (p := fun ω : Nat -> Real =>
        canonicalRenewalCount (s + h) ω =
          canonicalRenewalCount s ω + canonicalRenewalCount h (residualTail s ω))
      measurable_fst.aemeasurable ?_
    rw [hfst]
    exact ae_canonicalRenewalCount_add_eq_residualTailCount hrate s h hh
  have htailSource : ∀ᵐ z ∂gaps.prod marks,
      residualTail (s + h) z.1 = residualTail h (residualTail s z.1) := by
    refine ae_of_ae_map (μ := gaps.prod marks) (f := Prod.fst)
      (p := fun ω : Nat -> Real =>
        residualTail (s + h) ω = residualTail h (residualTail s ω))
      measurable_fst.aemeasurable ?_
    rw [hfst]
    exact ae_residualTail_add_eq_residualTail_comp hrate hh
  filter_upwards [hcountSource, htailSource] with z hcount htail
  apply Prod.ext
  · exact htail
  · funext i
    simp only [externalTimeMarkedResidualTail, externalTimeResidualTail,
      IIDStream.externalIndexTail, IIDStream.coordinate, hcount, Nat.add_assoc]

/-- One full-measure event supports the marked renewal-tail cocycle for every
base time and every nonnegative increment simultaneously.  This stronger
pathwise form is what permits an increment chosen from a stopped source
history to be substituted later without treating it as an independent draw. -/
theorem ae_externalTimeMarkedResidualTail_add_eq_comp_all
    {α : Type*} [MeasurableSpace α] (markLaw : Measure α)
    [IsProbabilityMeasure markLaw] {rate : Real} (hrate : 0 < rate) :
    ∀ᵐ z ∂((exponentialInterarrivalMeasure rate).prod (IIDStream.measure markLaw)),
      ∀ (s h : Real), 0 ≤ h →
        externalTimeMarkedResidualTail (α := α) (fun _ : Unit => s + h)
          (((), z.1), z.2) =
        externalTimeMarkedResidualTail (α := α) (fun _ : Unit => h)
          (((), residualTail s z.1),
            IIDStream.externalIndexTail
              (fun _ : Unit => canonicalRenewalCount s z.1) ((), z.2)) := by
  let gaps : Measure (Nat -> Real) := exponentialInterarrivalMeasure rate
  let marks : Measure (Nat -> α) := IIDStream.measure markLaw
  letI : IsProbabilityMeasure marks := by
    dsimp [marks, IIDStream.measure]
    infer_instance
  have hfst : Measure.map Prod.fst (gaps.prod marks) = gaps := by simp
  have hgood : ∀ᵐ ω ∂gaps, ∀ (s h : Real), 0 ≤ h →
      canonicalRenewalCount (s + h) ω =
        canonicalRenewalCount s ω + canonicalRenewalCount h (residualTail s ω) ∧
      residualTail (s + h) ω = residualTail h (residualTail s ω) := by
    filter_upwards [ae_arrivalTime_tendsto_atTop hrate] with ω hdiv
    intro s h hh
    have hS : ∃ n : Nat, s < arrivalTime n ω :=
      (hdiv.eventually_gt_atTop s).exists
    have hSH : ∃ n : Nat, s + h < arrivalTime n ω :=
      (hdiv.eventually_gt_atTop (s + h)).exists
    have hTail : ∃ n : Nat, h < arrivalTime n (residualTail s ω) :=
      exists_residualTail_arrival_gt_of_tendsto s h ω hdiv
    constructor
    · exact canonicalRenewalCount_add_eq_residualTailCount s h hh ω hS hSH hTail
    · exact residualTail_add_eq_residualTail_comp s h hh ω hS hSH hTail
  have hgoodSource : ∀ᵐ z ∂gaps.prod marks, ∀ (s h : Real), 0 ≤ h →
      canonicalRenewalCount (s + h) z.1 =
        canonicalRenewalCount s z.1 + canonicalRenewalCount h (residualTail s z.1) ∧
      residualTail (s + h) z.1 = residualTail h (residualTail s z.1) := by
    refine ae_of_ae_map (μ := gaps.prod marks) (f := Prod.fst)
      (p := fun ω : Nat -> Real => ∀ (s h : Real), 0 ≤ h →
        canonicalRenewalCount (s + h) ω =
          canonicalRenewalCount s ω + canonicalRenewalCount h (residualTail s ω) ∧
        residualTail (s + h) ω = residualTail h (residualTail s ω))
      measurable_fst.aemeasurable ?_
    rw [hfst]
    exact hgood
  filter_upwards [hgoodSource] with z hgood
  intro s h hh
  obtain ⟨hcount, htail⟩ := hgood s h hh
  apply Prod.ext
  · exact htail
  · funext i
    simp only [externalTimeMarkedResidualTail, externalTimeResidualTail,
      IIDStream.externalIndexTail, IIDStream.coordinate, hcount, Nat.add_assoc]

/-- At every deterministic renewal epoch simultaneously, the marked residual
input is the literal future gap stream and literal IID mark suffix.  The
all-indices form permits a mark-selected stopping index to be substituted
later while preserving the original source coordinate. -/
theorem ae_externalTimeMarkedResidualTail_arrivalPrefix_eq_future
    {α : Type*} [MeasurableSpace α] (markLaw : Measure α)
    [IsProbabilityMeasure markLaw] {rate : Real} (hrate : 0 < rate) :
    ∀ᵐ z ∂((exponentialInterarrivalMeasure rate).prod (IIDStream.measure markLaw)),
      ∀ n : Nat,
        externalTimeMarkedResidualTail (α := α)
          (fun _ : Unit => arrivalPrefix n z.1) (((), z.1), z.2) =
        (futureInterarrival n z.1,
          IIDStream.externalIndexTail (fun _ : Unit => n) ((), z.2)) := by
  let gaps : Measure (Nat -> Real) := exponentialInterarrivalMeasure rate
  let marks : Measure (Nat -> α) := IIDStream.measure markLaw
  letI : IsProbabilityMeasure marks := by
    dsimp [marks, IIDStream.measure]
    infer_instance
  have hfst : Measure.map Prod.fst (gaps.prod marks) = gaps := by simp
  have hfixed : ∀ n : Nat, ∀ᵐ ω ∂gaps,
      canonicalRenewalCount (arrivalPrefix n ω) ω = n ∧
      residualTail (arrivalPrefix n ω) ω = futureInterarrival n ω := by
    intro n
    filter_upwards [ae_canonicalRenewalCount_arrivalPrefix_add hrate n 0 le_rfl,
      ae_all_interarrival_positive hrate,
      ae_residualTail_arrivalPrefix_eq_futureInterarrival hrate n] with ω hcount hpos htail
    have htailZero : canonicalRenewalCount 0 (futureInterarrival n ω) = 0 := by
      rw [canonicalRenewalCount_eq_zero_iff]
      left
      simpa [arrivalTime, futureInterarrival, interarrival] using hpos n
    constructor
    · simpa [htailZero] using hcount
    · exact htail
  have hall : ∀ᵐ ω ∂gaps, ∀ n : Nat,
      canonicalRenewalCount (arrivalPrefix n ω) ω = n ∧
      residualTail (arrivalPrefix n ω) ω = futureInterarrival n ω :=
    ae_all_iff.2 hfixed
  have hallSource : ∀ᵐ z ∂gaps.prod marks, ∀ n : Nat,
      canonicalRenewalCount (arrivalPrefix n z.1) z.1 = n ∧
      residualTail (arrivalPrefix n z.1) z.1 = futureInterarrival n z.1 := by
    refine ae_of_ae_map (μ := gaps.prod marks) (f := Prod.fst)
      (p := fun ω : Nat -> Real => ∀ n : Nat,
        canonicalRenewalCount (arrivalPrefix n ω) ω = n ∧
        residualTail (arrivalPrefix n ω) ω = futureInterarrival n ω)
      measurable_fst.aemeasurable ?_
    rw [hfst]
    exact hall
  filter_upwards [hallSource] with z hallz
  intro n
  obtain ⟨hcount, htail⟩ := hallz n
  apply Prod.ext
  · exact htail
  · funext i
    simp only [externalTimeMarkedResidualTail, externalTimeResidualTail,
      IIDStream.externalIndexTail, IIDStream.coordinate, hcount]

/-- At a nonnegative time chosen independently of an exponential renewal path
and an IID mark stream, the marked residual path has the original product
law.  The theorem concerns the full future input pair, not merely either
marginal. -/
theorem externalTimeMarkedResidualTail_hasLaw
    {β α : Type*} [MeasurableSpace β] [MeasurableSpace α]
    (ν : Measure β) [IsProbabilityMeasure ν]
    (markLaw : Measure α) [IsProbabilityMeasure markLaw]
    {rate : Real} (hrate : 0 < rate)
    (time : β -> Real) (htime : Measurable time)
    (htime_nonneg : ∀ b, 0 ≤ time b) :
    HasLaw (externalTimeMarkedResidualTail (α := α) time)
      ((exponentialInterarrivalMeasure rate).prod (IIDStream.measure markLaw))
      ((ν.prod (exponentialInterarrivalMeasure rate)).prod
        (IIDStream.measure markLaw)) := by
  let gaps : Measure (Nat -> Real) := exponentialInterarrivalMeasure rate
  let marks : Measure (Nat -> α) := IIDStream.measure markLaw
  let history : β × (Nat -> Real) -> β × (Nat × (Nat -> Real)) :=
    externalTimePastHistory time
  let residual : β × (Nat -> Real) -> Nat -> Real :=
    externalTimeResidualTail time
  let index : β × (Nat -> Real) -> Nat :=
    fun h => canonicalRenewalCount (time h.1) h.2
  let source : Measure ((β × (Nat -> Real)) × (Nat -> α)) :=
    (ν.prod gaps).prod marks
  letI : IsProbabilityMeasure gaps := by
    simpa [gaps] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure marks := by
    dsimp [marks, IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure (ν.prod gaps) := by infer_instance
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  have hhistory : Measurable history := by
    simpa [history] using measurable_externalTimePastHistory time htime
  have hresidual : Measurable residual := by
    simpa [residual] using measurable_externalTimeResidualTail time htime
  letI : IsProbabilityMeasure (Measure.map history (ν.prod gaps)) :=
    Measure.isProbabilityMeasure_map hhistory.aemeasurable
  have hindex : Measurable index := by
    exact measurable_canonicalRenewalCount_joint.comp
      ((htime.comp measurable_fst).prodMk measurable_snd)
  have hfactor : Measure.map (fun z : β × (Nat -> Real) =>
      (history z, residual z)) (ν.prod gaps) =
      (Measure.map history (ν.prod gaps)).prod gaps := by
    simpa [history, residual, gaps] using
      map_externalTimePastHistory_residualTail ν hrate time htime htime_nonneg
  have hresidualLaw : Measure.map residual (ν.prod gaps) = gaps := by
    calc
      Measure.map residual (ν.prod gaps) =
          Measure.map Prod.snd (Measure.map (fun z : β × (Nat -> Real) =>
            (history z, residual z)) (ν.prod gaps)) := by
              rw [Measure.map_map measurable_snd (hhistory.prodMk hresidual)]
              rfl
      _ = Measure.map Prod.snd ((Measure.map history (ν.prod gaps)).prod gaps) := by
            rw [hfactor]
      _ = gaps := by simp
  have hjoint := IIDStream.externalIndexTail_joint_hasLaw
    (ν.prod gaps) markLaw index hindex residual hresidual
  refine ⟨(measurable_externalTimeMarkedResidualTail (α := α) time htime).aemeasurable, ?_⟩
  change Measure.map (externalTimeMarkedResidualTail (α := α) time) source = gaps.prod marks
  change Measure.map (fun z : (β × (Nat -> Real)) × (Nat -> α) =>
    (residual z.1, IIDStream.externalIndexTail (α := α) index z)) source = gaps.prod marks
  rw [hjoint.map_eq, hresidualLaw]

/-- A prefix event about marks already exposed before an independent external
clock time leaves the complete marked residual input fresh.  The event is
described on the finite arrival history and the corresponding mark prefix;
the conclusion is an unnormalized restricted-law identity, not a conditional
resampling or strong-Markov axiom. -/
theorem map_externalTimeMarkedResidualTail_restrict_eq_smul_of_pastPrefixEvent
    {β α : Type*} [MeasurableSpace β] [MeasurableSpace α]
    (ν : Measure β) [IsProbabilityMeasure ν]
    (markLaw : Measure α) [IsProbabilityMeasure markLaw]
    {rate : Real} (hrate : 0 < rate)
    (time : β -> Real) (htime : Measurable time)
    (htime_nonneg : ∀ b, 0 ≤ time b)
    (A : Set ((β × (Nat × (Nat -> Real))) × (Nat -> α)))
    (hA : IIDStream.ExternalIndexPrefixEvent (fun h : β × (Nat × (Nat -> Real)) =>
      h.2.1) A) :
    Measure.map (externalTimeMarkedResidualTail (α := α) time)
      (((ν.prod (exponentialInterarrivalMeasure rate)).prod
        (IIDStream.measure markLaw)).restrict
          {z | (externalTimePastHistory time z.1, z.2) ∈ A}) =
      ((Measure.map (externalTimePastHistory time)
        (ν.prod (exponentialInterarrivalMeasure rate))).prod
          (IIDStream.measure markLaw)) A •
        ((exponentialInterarrivalMeasure rate).prod (IIDStream.measure markLaw)) := by
  let gaps : Measure (Nat -> Real) := exponentialInterarrivalMeasure rate
  let marks : Measure (Nat -> α) := IIDStream.measure markLaw
  let history : β × (Nat -> Real) -> β × (Nat × (Nat -> Real)) :=
    externalTimePastHistory time
  let residual : β × (Nat -> Real) -> Nat -> Real :=
    externalTimeResidualTail time
  let factor : β × (Nat -> Real) ->
      (β × (Nat × (Nat -> Real))) × (Nat -> Real) :=
    fun z => (history z, residual z)
  let index : β × (Nat × (Nat -> Real)) -> Nat := fun h => h.2.1
  let source : Measure ((β × (Nat -> Real)) × (Nat -> α)) :=
    (ν.prod gaps).prod marks
  let historyLaw : Measure (β × (Nat × (Nat -> Real))) :=
    Measure.map history (ν.prod gaps)
  let postLaw : Measure (((β × (Nat × (Nat -> Real))) × (Nat -> Real)) ×
      (Nat -> α)) := (historyLaw.prod gaps).prod marks
  let transform : ((β × (Nat -> Real)) × (Nat -> α)) ->
      ((β × (Nat × (Nat -> Real))) × (Nat -> Real)) × (Nat -> α) :=
    Prod.map factor id
  let initialCarrier : Set ((β × (Nat -> Real)) × (Nat -> α)) :=
    {z | (history z.1, z.2) ∈ A}
  let lifted : Set (((β × (Nat × (Nat -> Real))) × (Nat -> Real)) ×
      (Nat -> α)) := {z | (z.1.1, z.2) ∈ A}
  let tail : (β × (Nat × (Nat -> Real))) × (Nat -> α) -> Nat -> α :=
    IIDStream.externalIndexTail index
  let companionOutput :
      ((β × (Nat × (Nat -> Real))) × (Nat -> Real)) × (Nat -> α) ->
        (Nat -> α) × (Nat -> Real) :=
    fun z => (tail (z.1.1, z.2), z.1.2)
  let output : ((β × (Nat × (Nat -> Real))) × (Nat -> Real)) ×
      (Nat -> α) -> (Nat -> Real) × (Nat -> α) :=
    fun z => (z.1.2, tail (z.1.1, z.2))
  letI : IsProbabilityMeasure gaps := by
    simpa [gaps] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure marks := by
    dsimp [marks, IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  have hhistory : Measurable history := by
    simpa [history] using measurable_externalTimePastHistory time htime
  have hresidual : Measurable residual := by
    simpa [residual] using measurable_externalTimeResidualTail time htime
  have hfactor : Measurable factor := hhistory.prodMk hresidual
  letI : IsProbabilityMeasure historyLaw := by
    dsimp [historyLaw]
    exact Measure.isProbabilityMeasure_map hhistory.aemeasurable
  letI : IsProbabilityMeasure postLaw := by
    dsimp [postLaw]
    infer_instance
  have hindex : Measurable index := by
    exact measurable_fst.comp measurable_snd
  have hhistoryResidual :
      Measure.map factor (ν.prod gaps) = historyLaw.prod gaps := by
    simpa [factor, history, residual, historyLaw, gaps] using
      map_externalTimePastHistory_residualTail ν hrate time htime htime_nonneg
  have htransform : Measure.map transform source = postLaw := by
    calc
      Measure.map transform source =
          (Measure.map factor (ν.prod gaps)).prod (Measure.map id marks) := by
            symm
            simpa [transform, source] using
              Measure.map_prod_map (ν.prod gaps) marks hfactor measurable_id
      _ = postLaw := by rw [hhistoryResidual, Measure.map_id]
  have htransform_meas : Measurable transform :=
    (hfactor.comp measurable_fst).prodMk measurable_snd
  have hAmeas : MeasurableSet A :=
    IIDStream.measurableSet_externalIndexPrefixEvent index hindex A hA
  have hlifted : MeasurableSet lifted := by
    exact hAmeas.preimage
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hpreimage : transform ⁻¹' lifted = initialCarrier := by
    ext z
    simp [transform, factor, history, residual, lifted, initialCarrier]
  have hrestrict :
      Measure.map transform (source.restrict initialCarrier) =
        postLaw.restrict lifted := by
    calc
      Measure.map transform (source.restrict initialCarrier) =
          Measure.map transform (source.restrict (transform ⁻¹' lifted)) := by
            rw [hpreimage]
      _ = (Measure.map transform source).restrict lifted := by
            rw [Measure.restrict_map htransform_meas hlifted]
      _ = postLaw.restrict lifted := by rw [htransform]
  have htail : Measurable tail := by
    simpa [tail] using IIDStream.measurable_externalIndexTail (α := α) index hindex
  have hcompanionOutput : Measurable companionOutput := by
    exact (htail.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
        (measurable_snd.comp measurable_fst)
  have houtput : Measurable output := by
    exact (measurable_snd.comp measurable_fst).prodMk
      (htail.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have houtput_comp : externalTimeMarkedResidualTail (α := α) time =
      output ∘ transform := by
    funext z
    rfl
  have hswap_comp : output = Prod.swap ∘ companionOutput := by
    funext z
    rfl
  calc
    Measure.map (externalTimeMarkedResidualTail (α := α) time)
        (((ν.prod (exponentialInterarrivalMeasure rate)).prod
          (IIDStream.measure markLaw)).restrict
            {z | (externalTimePastHistory time z.1, z.2) ∈ A}) =
        Measure.map output (Measure.map transform (source.restrict initialCarrier)) := by
          rw [houtput_comp, Measure.map_map houtput htransform_meas]
    _ = Measure.map output (postLaw.restrict lifted) := by rw [hrestrict]
    _ = Measure.map Prod.swap
        (Measure.map companionOutput (postLaw.restrict lifted)) := by
          rw [hswap_comp, Measure.map_map measurable_swap hcompanionOutput]
    _ = Measure.map Prod.swap
        (((historyLaw.prod marks) A) • (marks.prod gaps)) := by
          rw [IIDStream.map_externalIndexTail_withCompanion_restrict_eq_smul
            historyLaw gaps markLaw index hindex A hA]
    _ = ((historyLaw.prod marks) A) • (gaps.prod marks) := by
          rw [Measure.map_smul, Measure.prod_swap]
    _ = ((Measure.map (externalTimePastHistory time)
        (ν.prod (exponentialInterarrivalMeasure rate))).prod
          (IIDStream.measure markLaw)) A •
        ((exponentialInterarrivalMeasure rate).prod (IIDStream.measure markLaw)) := by
          rfl

/-- A marked external-time prefix restriction retains its actual past clock
history jointly with the complete future marked residual input.  The past
history marginal is left unnormalized, so the result applies directly to
event-restricted stopped constructions without a conditional resampling step. -/
theorem map_externalTimeMarkedResidualTail_withPastHistory_restrict_eq_prod
    {β α : Type*} [MeasurableSpace β] [MeasurableSpace α]
    (ν : Measure β) [IsProbabilityMeasure ν]
    (markLaw : Measure α) [IsProbabilityMeasure markLaw]
    {rate : Real} (hrate : 0 < rate)
    (time : β -> Real) (htime : Measurable time)
    (htime_nonneg : ∀ b, 0 ≤ time b)
    (A : Set ((β × (Nat × (Nat -> Real))) × (Nat -> α)))
    (hA : IIDStream.ExternalIndexPrefixEvent (fun h : β × (Nat × (Nat -> Real)) =>
      h.2.1) A) :
    Measure.map (fun z : (β × (Nat -> Real)) × (Nat -> α) =>
      let history := externalTimePastHistory time z.1
      (history, (IIDStream.externalIndexTail (α := α) (fun h => h.2.1)
        (history, z.2), externalTimeResidualTail time z.1)))
      (((ν.prod (exponentialInterarrivalMeasure rate)).prod
        (IIDStream.measure markLaw)).restrict
          {z | (externalTimePastHistory time z.1, z.2) ∈ A}) =
      (Measure.map Prod.fst
        (((Measure.map (externalTimePastHistory time)
          (ν.prod (exponentialInterarrivalMeasure rate))).prod
            (IIDStream.measure markLaw)).restrict A)).prod
        ((IIDStream.measure markLaw).prod
          (exponentialInterarrivalMeasure rate)) := by
  let gaps : Measure (Nat -> Real) := exponentialInterarrivalMeasure rate
  let marks : Measure (Nat -> α) := IIDStream.measure markLaw
  let history : β × (Nat -> Real) -> β × (Nat × (Nat -> Real)) :=
    externalTimePastHistory time
  let residual : β × (Nat -> Real) -> Nat -> Real :=
    externalTimeResidualTail time
  let factor : β × (Nat -> Real) ->
      (β × (Nat × (Nat -> Real))) × (Nat -> Real) := fun z => (history z, residual z)
  let index : β × (Nat × (Nat -> Real)) -> Nat := fun h => h.2.1
  let source : Measure ((β × (Nat -> Real)) × (Nat -> α)) :=
    (ν.prod gaps).prod marks
  let historyLaw : Measure (β × (Nat × (Nat -> Real))) :=
    Measure.map history (ν.prod gaps)
  let postLaw : Measure (((β × (Nat × (Nat -> Real))) × (Nat -> Real)) ×
      (Nat -> α)) := (historyLaw.prod gaps).prod marks
  let transform : ((β × (Nat -> Real)) × (Nat -> α)) ->
      ((β × (Nat × (Nat -> Real))) × (Nat -> Real)) × (Nat -> α) :=
    Prod.map factor id
  let initialCarrier : Set ((β × (Nat -> Real)) × (Nat -> α)) :=
    {z | (history z.1, z.2) ∈ A}
  let lifted : Set (((β × (Nat × (Nat -> Real))) × (Nat -> Real)) ×
      (Nat -> α)) := {z | (z.1.1, z.2) ∈ A}
  let tail : (β × (Nat × (Nat -> Real))) × (Nat -> α) -> Nat -> α :=
    IIDStream.externalIndexTail index
  let output : ((β × (Nat × (Nat -> Real))) × (Nat -> Real)) ×
      (Nat -> α) -> (β × (Nat × (Nat -> Real))) × ((Nat -> α) × (Nat -> Real)) := fun z =>
    (z.1.1, (tail (z.1.1, z.2), z.1.2))
  letI : IsProbabilityMeasure gaps := by
    simpa [gaps] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure marks := by
    dsimp [marks, IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  have hhistory : Measurable history := by
    simpa [history] using measurable_externalTimePastHistory time htime
  have hresidual : Measurable residual := by
    simpa [residual] using measurable_externalTimeResidualTail time htime
  have hfactor : Measurable factor := hhistory.prodMk hresidual
  letI : IsProbabilityMeasure historyLaw := by
    dsimp [historyLaw]
    exact Measure.isProbabilityMeasure_map hhistory.aemeasurable
  letI : IsProbabilityMeasure postLaw := by
    dsimp [postLaw]
    infer_instance
  have hindex : Measurable index := measurable_fst.comp measurable_snd
  have hfactorLaw : Measure.map factor (ν.prod gaps) = historyLaw.prod gaps := by
    simpa [factor, history, residual, historyLaw, gaps] using
      map_externalTimePastHistory_residualTail ν hrate time htime htime_nonneg
  have htransform : Measure.map transform source = postLaw := by
    calc
      Measure.map transform source =
          (Measure.map factor (ν.prod gaps)).prod (Measure.map id marks) := by
            symm
            simpa [transform, source] using
              Measure.map_prod_map (ν.prod gaps) marks hfactor measurable_id
      _ = postLaw := by rw [hfactorLaw, Measure.map_id]
  have htransformMeas : Measurable transform :=
    (hfactor.comp measurable_fst).prodMk measurable_snd
  have hAmeas : MeasurableSet A :=
    IIDStream.measurableSet_externalIndexPrefixEvent index hindex A hA
  have hlifted : MeasurableSet lifted :=
    hAmeas.preimage ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hpreimage : transform ⁻¹' lifted = initialCarrier := by
    ext z
    simp [transform, factor, history, residual, lifted, initialCarrier]
  have hrestrict : Measure.map transform (source.restrict initialCarrier) =
      postLaw.restrict lifted := by
    calc
      Measure.map transform (source.restrict initialCarrier) =
          Measure.map transform (source.restrict (transform ⁻¹' lifted)) := by
            rw [hpreimage]
      _ = (Measure.map transform source).restrict lifted := by
            rw [Measure.restrict_map htransformMeas hlifted]
      _ = postLaw.restrict lifted := by rw [htransform]
  have htail : Measurable tail := by
    simpa [tail] using IIDStream.measurable_externalIndexTail (α := α) index hindex
  have houtput : Measurable output :=
    (measurable_fst.comp measurable_fst).prodMk
      ((htail.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
        (measurable_snd.comp measurable_fst))
  have hstate := IIDStream.map_externalIndexTail_withStateAndCompanion_restrict_eq_prod
    historyLaw gaps markLaw index hindex A hA
  calc
    Measure.map (fun z : (β × (Nat -> Real)) × (Nat -> α) =>
        let h := externalTimePastHistory time z.1
        (h, (IIDStream.externalIndexTail (α := α) (fun h => h.2.1) (h, z.2),
          externalTimeResidualTail time z.1)))
        (((ν.prod (exponentialInterarrivalMeasure rate)).prod
          (IIDStream.measure markLaw)).restrict
            {z | (externalTimePastHistory time z.1, z.2) ∈ A}) =
        Measure.map output (Measure.map transform (source.restrict initialCarrier)) := by
          rw [show (fun z : (β × (Nat -> Real)) × (Nat -> α) =>
              let h := externalTimePastHistory time z.1
              (h, (IIDStream.externalIndexTail (α := α) (fun h => h.2.1) (h, z.2),
                externalTimeResidualTail time z.1))) = output ∘ transform by
                funext z
                rfl,
            Measure.map_map houtput htransformMeas]
    _ = Measure.map output (postLaw.restrict lifted) := by rw [hrestrict]
    _ = (Measure.map Prod.fst ((historyLaw.prod marks).restrict A)).prod
        (marks.prod gaps) := by
          simpa [postLaw, lifted, output, tail] using hstate
    _ = (Measure.map Prod.fst
        ((Measure.map (externalTimePastHistory time) (ν.prod gaps)).prod marks |>.restrict A)).prod
        (marks.prod gaps) := by rfl
    _ = (Measure.map Prod.fst
        ((Measure.map (externalTimePastHistory time)
          (ν.prod (exponentialInterarrivalMeasure rate))).prod
            (IIDStream.measure markLaw) |>.restrict A)).prod
        ((IIDStream.measure markLaw).prod
          (exponentialInterarrivalMeasure rate)) := by rfl

/-- A marked external-time prefix restriction retains its actual past clock
history while carrying an independent companion together with the complete
future marked residual input.  The companion is deliberately placed on the
future side of the product, so deterministic reassembly can use it without
sharing any coordinate with the reported stopped history. -/
theorem map_externalTimeMarkedResidualTail_withPastHistoryAndCompanion_restrict_eq_prod
    {β α γ : Type*} [MeasurableSpace β] [MeasurableSpace α] [MeasurableSpace γ]
    (ν : Measure β) [IsProbabilityMeasure ν]
    (κ : Measure γ) [IsProbabilityMeasure κ]
    (markLaw : Measure α) [IsProbabilityMeasure markLaw]
    {rate : Real} (hrate : 0 < rate)
    (time : β -> Real) (htime : Measurable time)
    (htime_nonneg : ∀ b, 0 ≤ time b)
    (A : Set ((β × (Nat × (Nat -> Real))) × (Nat -> α)))
    (hA : IIDStream.ExternalIndexPrefixEvent (fun h : β × (Nat × (Nat -> Real)) =>
      h.2.1) A) :
    Measure.map (fun z : ((β × γ) × (Nat -> Real)) × (Nat -> α) =>
      let history := externalTimePastHistory time (z.1.1.1, z.1.2)
      (history, ((IIDStream.externalIndexTail (α := α) (fun h => h.2.1)
        (history, z.2), externalTimeResidualTail time (z.1.1.1, z.1.2)), z.1.1.2)))
      ((((ν.prod κ).prod (exponentialInterarrivalMeasure rate)).prod
        (IIDStream.measure markLaw)).restrict
          {z | (externalTimePastHistory time (z.1.1.1, z.1.2), z.2) ∈ A}) =
      (Measure.map Prod.fst
        (((Measure.map (externalTimePastHistory time)
          (ν.prod (exponentialInterarrivalMeasure rate))).prod
            (IIDStream.measure markLaw)).restrict A)).prod
        (((IIDStream.measure markLaw).prod
          (exponentialInterarrivalMeasure rate)).prod κ) := by
  let gaps : Measure (Nat -> Real) := exponentialInterarrivalMeasure rate
  let marks : Measure (Nat -> α) := IIDStream.measure markLaw
  let markedSource : Measure ((β × (Nat -> Real)) × (Nat -> α)) :=
    (ν.prod gaps).prod marks
  let source : Measure (((β × γ) × (Nat -> Real)) × (Nat -> α)) :=
    ((ν.prod κ).prod gaps).prod marks
  let history : β × (Nat -> Real) -> β × (Nat × (Nat -> Real)) :=
    externalTimePastHistory time
  let index : β × (Nat × (Nat -> Real)) -> Nat := fun h => h.2.1
  let tail : (β × (Nat × (Nat -> Real))) × (Nat -> α) -> Nat -> α :=
    IIDStream.externalIndexTail index
  let residual : β × (Nat -> Real) -> Nat -> Real :=
    externalTimeResidualTail time
  let stoppedCarrier : Set ((β × (Nat -> Real)) × (Nat -> α)) :=
    {z | (history z.1, z.2) ∈ A}
  let carrier : Set (((β × (Nat -> Real)) × (Nat -> α)) × γ) :=
    stoppedCarrier ×ˢ Set.univ
  let lifted : Set (((β × γ) × (Nat -> Real)) × (Nat -> α)) :=
    {z | (history (z.1.1.1, z.1.2), z.2) ∈ A}
  let reorder : ((β × γ) × (Nat -> Real)) × (Nat -> α) ->
      ((β × (Nat -> Real)) × (Nat -> α)) × γ :=
    fun z => (((z.1.1.1, z.1.2), z.2), z.1.1.2)
  let markedOutput : ((β × (Nat -> Real)) × (Nat -> α)) ->
      (β × (Nat × (Nat -> Real))) × ((Nat -> α) × (Nat -> Real)) := fun z =>
    (history z.1, (tail (history z.1, z.2), residual z.1))
  let paired : ((β × (Nat -> Real)) × (Nat -> α)) × γ ->
      ((β × (Nat × (Nat -> Real))) × ((Nat -> α) × (Nat -> Real))) × γ := fun z =>
    (markedOutput z.1, z.2)
  let output : ((β × (Nat -> Real)) × (Nat -> α)) × γ ->
      (β × (Nat × (Nat -> Real))) × (((Nat -> α) × (Nat -> Real)) × γ) :=
    MeasurableEquiv.prodAssoc ∘ paired
  letI : IsProbabilityMeasure gaps := by
    simpa [gaps] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure marks := by
    dsimp [marks, IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure markedSource := by
    dsimp [markedSource]
    infer_instance
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  have hhistory : Measurable history := by
    simpa [history] using measurable_externalTimePastHistory time htime
  have hindex : Measurable index := measurable_fst.comp measurable_snd
  have htail : Measurable tail := by
    simpa [tail] using IIDStream.measurable_externalIndexTail (α := α) index hindex
  have hresidual : Measurable residual := by
    simpa [residual] using measurable_externalTimeResidualTail time htime
  have hmarkedOutput : Measurable markedOutput :=
    (hhistory.comp measurable_fst).prodMk
      ((htail.comp ((hhistory.comp measurable_fst).prodMk measurable_snd)).prodMk
        (hresidual.comp measurable_fst))
  have hpaired : Measurable paired :=
    (hmarkedOutput.comp measurable_fst).prodMk measurable_snd
  have houtput : Measurable output :=
    MeasurableEquiv.prodAssoc.measurable.comp hpaired
  let assoc1 : ((β × γ) × (Nat -> Real)) × (Nat -> α) ->
      (β × γ) × ((Nat -> Real) × (Nat -> α)) :=
    MeasurableEquiv.prodAssoc
  let assoc2 : (β × γ) × ((Nat -> Real) × (Nat -> α)) ->
      β × (γ × ((Nat -> Real) × (Nat -> α))) :=
    MeasurableEquiv.prodAssoc
  let swapTail : β × (γ × ((Nat -> Real) × (Nat -> α))) ->
      β × (((Nat -> Real) × (Nat -> α)) × γ) :=
    Prod.map id Prod.swap
  let assoc3 : β × (((Nat -> Real) × (Nat -> α)) × γ) ->
      (β × ((Nat -> Real) × (Nat -> α))) × γ :=
    MeasurableEquiv.prodAssoc.symm
  let assoc4 : (β × ((Nat -> Real) × (Nat -> α))) × γ ->
      ((β × (Nat -> Real)) × (Nat -> α)) × γ :=
    Prod.map MeasurableEquiv.prodAssoc.symm id
  let p1 := measurePreserving_prodAssoc (ν.prod κ) gaps marks
  let p2 := measurePreserving_prodAssoc ν κ (gaps.prod marks)
  let swap : MeasurePreserving (Prod.swap : γ × ((Nat -> Real) × (Nat -> α)) ->
      ((Nat -> Real) × (Nat -> α)) × γ) (κ.prod (gaps.prod marks))
      ((gaps.prod marks).prod κ) :=
    ⟨measurable_swap, Measure.prod_swap⟩
  let p3 := MeasurePreserving.prod (MeasurePreserving.id ν) swap
  let p4 := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc ν (gaps.prod marks) κ)
  let p5 := MeasurePreserving.prod
    (MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc ν gaps marks))
    (MeasurePreserving.id κ)
  have hreorder : MeasurePreserving reorder source (markedSource.prod κ) := by
    have hfun : reorder = assoc4 ∘ assoc3 ∘ swapTail ∘ assoc2 ∘ assoc1 := by
      funext z
      rfl
    rw [hfun]
    simpa [assoc1, assoc2, swapTail, assoc3, assoc4, source, markedSource, gaps, marks] using
      (p5.comp (p4.comp (p3.comp (p2.comp p1))))
  have hAmeas : MeasurableSet A :=
    IIDStream.measurableSet_externalIndexPrefixEvent index hindex A hA
  have hstoppedCarrier : MeasurableSet stoppedCarrier :=
    hAmeas.preimage ((hhistory.comp measurable_fst).prodMk measurable_snd)
  have hcarrier : MeasurableSet carrier :=
    hstoppedCarrier.prod MeasurableSet.univ
  have hpreimage : reorder ⁻¹' carrier = lifted := by
    ext z
    simp [reorder, carrier, stoppedCarrier, lifted, history]
  have hrestrict : Measure.map reorder (source.restrict lifted) =
      (markedSource.prod κ).restrict carrier := by
    calc
      Measure.map reorder (source.restrict lifted) =
          Measure.map reorder (source.restrict (reorder ⁻¹' carrier)) := by
            rw [hpreimage]
      _ = (Measure.map reorder source).restrict carrier := by
            rw [Measure.restrict_map hreorder.measurable hcarrier]
      _ = (markedSource.prod κ).restrict carrier := by rw [hreorder.map_eq]
  have hfactor := map_externalTimeMarkedResidualTail_withPastHistory_restrict_eq_prod
    ν markLaw hrate time htime htime_nonneg A hA
  calc
    Measure.map (fun z : ((β × γ) × (Nat -> Real)) × (Nat -> α) =>
        let h := externalTimePastHistory time (z.1.1.1, z.1.2)
        (h, ((IIDStream.externalIndexTail (α := α) (fun h => h.2.1) (h, z.2),
          externalTimeResidualTail time (z.1.1.1, z.1.2)), z.1.1.2)))
        (source.restrict lifted) =
        Measure.map output (Measure.map reorder (source.restrict lifted)) := by
          rw [show (fun z : ((β × γ) × (Nat -> Real)) × (Nat -> α) =>
              let h := externalTimePastHistory time (z.1.1.1, z.1.2)
              (h, ((IIDStream.externalIndexTail (α := α) (fun h => h.2.1) (h, z.2),
                externalTimeResidualTail time (z.1.1.1, z.1.2)), z.1.1.2))) =
              output ∘ reorder by
                funext z
                rfl,
            Measure.map_map houtput hreorder.measurable]
    _ = Measure.map output ((markedSource.prod κ).restrict carrier) := by rw [hrestrict]
    _ = Measure.map output ((markedSource.restrict stoppedCarrier).prod κ) := by
          rw [← Measure.restrict_prod_eq_prod_univ]
    _ = Measure.map MeasurableEquiv.prodAssoc
        (Measure.map paired ((markedSource.restrict stoppedCarrier).prod κ)) := by
          change Measure.map (MeasurableEquiv.prodAssoc ∘ paired)
            ((markedSource.restrict stoppedCarrier).prod κ) = _
          rw [Measure.map_map MeasurableEquiv.prodAssoc.measurable hpaired]
    _ = Measure.map MeasurableEquiv.prodAssoc
        ((Measure.map markedOutput (markedSource.restrict stoppedCarrier)).prod κ) := by
          congr 1
          rw [show paired = Prod.map markedOutput id by rfl,
            ← Measure.map_prod_map (markedSource.restrict stoppedCarrier) κ
              hmarkedOutput measurable_id,
            Measure.map_id]
    _ = Measure.map MeasurableEquiv.prodAssoc
        (((Measure.map Prod.fst
          ((Measure.map history (ν.prod gaps)).prod marks |>.restrict A)).prod
          (marks.prod gaps)).prod κ) := by
            rw [show Measure.map markedOutput (markedSource.restrict stoppedCarrier) =
                (Measure.map Prod.fst
                  ((Measure.map history (ν.prod gaps)).prod marks |>.restrict A)).prod
                  (marks.prod gaps) by
                  simpa [markedOutput, markedSource, stoppedCarrier, history, tail, residual] using
                    hfactor]
    _ = (Measure.map Prod.fst
        ((Measure.map history (ν.prod gaps)).prod marks |>.restrict A)).prod
        ((marks.prod gaps).prod κ) := by
          simpa using
            (measurePreserving_prodAssoc
              (Measure.map Prod.fst ((Measure.map history (ν.prod gaps)).prod marks |>.restrict A))
              (marks.prod gaps) κ).map_eq
    _ = (Measure.map Prod.fst
        ((Measure.map (externalTimePastHistory time)
          (ν.prod (exponentialInterarrivalMeasure rate))).prod
            (IIDStream.measure markLaw) |>.restrict A)).prod
        (((IIDStream.measure markLaw).prod
          (exponentialInterarrivalMeasure rate)).prod κ) := by rfl

/-- In particular, conditioning on no mark from a measurable hit set before
the external clock leaves both the residual exponential path and the residual
IID mark path fresh.  The left-hand event only exposes the finite prefix
strictly before the clock; it does not restart either stream. -/
theorem map_externalTimeMarkedResidualTail_restrict_eq_smul_of_noHit
    {β α : Type*} [MeasurableSpace β] [MeasurableSpace α]
    (ν : Measure β) [IsProbabilityMeasure ν]
    (markLaw : Measure α) [IsProbabilityMeasure markLaw]
    {rate : Real} (hrate : 0 < rate)
    (time : β -> Real) (htime : Measurable time)
    (htime_nonneg : ∀ b, 0 ≤ time b)
    (s : Set α) (hs : MeasurableSet s) :
    Measure.map (externalTimeMarkedResidualTail (α := α) time)
      (((ν.prod (exponentialInterarrivalMeasure rate)).prod
        (IIDStream.measure markLaw)).restrict
          {z | ∀ i, i < canonicalRenewalCount (time z.1.1) z.1.2 → z.2 i ∉ s}) =
      ((Measure.map (externalTimePastHistory time)
        (ν.prod (exponentialInterarrivalMeasure rate))).prod
          (IIDStream.measure markLaw))
        (IIDStream.externalIndexNoHit
          (fun h : β × (Nat × (Nat -> Real)) => h.2.1) s) •
        ((exponentialInterarrivalMeasure rate).prod (IIDStream.measure markLaw)) := by
  let index : β × (Nat × (Nat -> Real)) -> Nat := fun h => h.2.1
  let A : Set ((β × (Nat × (Nat -> Real))) × (Nat -> α)) :=
    IIDStream.externalIndexNoHit index s
  have hA : IIDStream.ExternalIndexPrefixEvent index A := by
    exact IIDStream.externalIndexNoHit_prefixEvent index s hs
  simpa [A, index, IIDStream.externalIndexNoHit, externalTimePastHistory,
    canonicalRenewalPastHistory] using
    map_externalTimeMarkedResidualTail_restrict_eq_smul_of_pastPrefixEvent
      ν markLaw hrate time htime htime_nonneg A hA

/-- A no-hit restriction on one marked renewal stream leaves an independent
companion coordinate untouched, jointly with the marked residual tail.  The
companion is kept in the output rather than replaced by a new sample, which
makes this usable when a stopped source transition must retain other future
coordinates. -/
theorem map_externalTimeMarkedResidualTail_withCompanion_restrict_eq_smul_of_noHit
    {β α γ : Type*} [MeasurableSpace β] [MeasurableSpace α] [MeasurableSpace γ]
    (ν : Measure β) [IsProbabilityMeasure ν]
    (κ : Measure γ) [IsProbabilityMeasure κ]
    (markLaw : Measure α) [IsProbabilityMeasure markLaw]
    {rate : Real} (hrate : 0 < rate)
    (time : β -> Real) (htime : Measurable time)
    (htime_nonneg : ∀ b, 0 ≤ time b)
    (s : Set α) (hs : MeasurableSet s) :
    Measure.map (fun z : ((β × γ) × (Nat -> Real)) × (Nat -> α) =>
      (externalTimeMarkedResidualTail (α := α) time ((z.1.1.1, z.1.2), z.2),
        z.1.1.2))
      ((((ν.prod κ).prod (exponentialInterarrivalMeasure rate)).prod
        (IIDStream.measure markLaw)).restrict
          {z | ∀ i, i < canonicalRenewalCount (time z.1.1.1) z.1.2 → z.2 i ∉ s}) =
      ((Measure.map (externalTimePastHistory time)
        (ν.prod (exponentialInterarrivalMeasure rate))).prod
          (IIDStream.measure markLaw))
        (IIDStream.externalIndexNoHit
          (fun h : β × (Nat × (Nat -> Real)) => h.2.1) s) •
        (((exponentialInterarrivalMeasure rate).prod
          (IIDStream.measure markLaw)).prod κ) := by
  let gaps : Measure (Nat -> Real) := exponentialInterarrivalMeasure rate
  let marks : Measure (Nat -> α) := IIDStream.measure markLaw
  let markedSource : Measure ((β × (Nat -> Real)) × (Nat -> α)) :=
    (ν.prod gaps).prod marks
  let source : Measure (((β × γ) × (Nat -> Real)) × (Nat -> α)) :=
    ((ν.prod κ).prod gaps).prod marks
  let reorder : ((β × γ) × (Nat -> Real)) × (Nat -> α) ->
      ((β × (Nat -> Real)) × (Nat -> α)) × γ :=
    fun z => (((z.1.1.1, z.1.2), z.2), z.1.1.2)
  let residual : ((β × (Nat -> Real)) × (Nat -> α)) ->
      (Nat -> Real) × (Nat -> α) :=
    externalTimeMarkedResidualTail (α := α) time
  let output : ((β × (Nat -> Real)) × (Nat -> α)) × γ ->
      ((Nat -> Real) × (Nat -> α)) × γ :=
    fun z => (residual z.1, z.2)
  let A : Set ((β × (Nat -> Real)) × (Nat -> α)) :=
    {z | ∀ i, i < canonicalRenewalCount (time z.1.1) z.1.2 → z.2 i ∉ s}
  let carrier : Set (((β × (Nat -> Real)) × (Nat -> α)) × γ) := A ×ˢ Set.univ
  let lifted : Set (((β × γ) × (Nat -> Real)) × (Nat -> α)) :=
    {z | ∀ i, i < canonicalRenewalCount (time z.1.1.1) z.1.2 → z.2 i ∉ s}
  letI : IsProbabilityMeasure gaps := by
    simpa [gaps] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure marks := by
    dsimp [marks, IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure markedSource := by
    dsimp [markedSource]
    infer_instance
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  let assoc1 : ((β × γ) × (Nat -> Real)) × (Nat -> α) ->
      (β × γ) × ((Nat -> Real) × (Nat -> α)) :=
    MeasurableEquiv.prodAssoc
  let assoc2 : (β × γ) × ((Nat -> Real) × (Nat -> α)) ->
      β × (γ × ((Nat -> Real) × (Nat -> α))) :=
    MeasurableEquiv.prodAssoc
  let swapTail : β × (γ × ((Nat -> Real) × (Nat -> α))) ->
      β × (((Nat -> Real) × (Nat -> α)) × γ) :=
    Prod.map id Prod.swap
  let assoc3 : β × (((Nat -> Real) × (Nat -> α)) × γ) ->
      (β × ((Nat -> Real) × (Nat -> α))) × γ :=
    MeasurableEquiv.prodAssoc.symm
  let assoc4 : (β × ((Nat -> Real) × (Nat -> α))) × γ ->
      ((β × (Nat -> Real)) × (Nat -> α)) × γ :=
    Prod.map MeasurableEquiv.prodAssoc.symm id
  let p1 := measurePreserving_prodAssoc (ν.prod κ) gaps marks
  let p2 := measurePreserving_prodAssoc ν κ (gaps.prod marks)
  let swap : MeasurePreserving (Prod.swap : γ × ((Nat -> Real) × (Nat -> α)) ->
      ((Nat -> Real) × (Nat -> α)) × γ) (κ.prod (gaps.prod marks))
      ((gaps.prod marks).prod κ) :=
    ⟨measurable_swap, Measure.prod_swap⟩
  let p3 := MeasurePreserving.prod (MeasurePreserving.id ν) swap
  let p4 := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc ν (gaps.prod marks) κ)
  let p5 := MeasurePreserving.prod
    (MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc ν gaps marks))
    (MeasurePreserving.id κ)
  have hreorder : MeasurePreserving reorder source (markedSource.prod κ) := by
    have hfun : reorder = assoc4 ∘ assoc3 ∘ swapTail ∘ assoc2 ∘ assoc1 := by
      funext z
      rfl
    rw [hfun]
    simpa [assoc1, assoc2, swapTail, assoc3, assoc4, source, markedSource, gaps, marks] using
      (p5.comp (p4.comp (p3.comp (p2.comp p1))))
  have hA : MeasurableSet A := by
    have hAeq : A = IIDStream.externalIndexNoHit
        (fun h : β × (Nat -> Real) => canonicalRenewalCount (time h.1) h.2) s := by
      ext z
      rfl
    rw [hAeq]
    exact IIDStream.measurableSet_externalIndexPrefixEvent
      (fun h : β × (Nat -> Real) => canonicalRenewalCount (time h.1) h.2)
      (measurable_canonicalRenewalCount_joint.comp
        ((htime.comp measurable_fst).prodMk measurable_snd))
      (IIDStream.externalIndexNoHit
        (fun h : β × (Nat -> Real) => canonicalRenewalCount (time h.1) h.2) s)
      (IIDStream.externalIndexNoHit_prefixEvent
        (fun h : β × (Nat -> Real) => canonicalRenewalCount (time h.1) h.2) s hs)
  have hcarrier : MeasurableSet carrier := hA.prod MeasurableSet.univ
  have hpreimage : reorder ⁻¹' carrier = lifted := by
    ext z
    simp [reorder, carrier, lifted, A]
  have hrestrict : Measure.map reorder (source.restrict lifted) =
      (markedSource.prod κ).restrict carrier := by
    calc
      Measure.map reorder (source.restrict lifted) =
          Measure.map reorder (source.restrict (reorder ⁻¹' carrier)) := by
            rw [hpreimage]
      _ = (Measure.map reorder source).restrict carrier := by
            rw [Measure.restrict_map hreorder.measurable hcarrier]
      _ = (markedSource.prod κ).restrict carrier := by rw [hreorder.map_eq]
  have hresidual : Measurable residual := by
    simpa [residual] using measurable_externalTimeMarkedResidualTail (α := α)
      time htime
  have houtput : Measurable output := by
    exact (hresidual.comp measurable_fst).prodMk measurable_snd
  have hfactor := map_externalTimeMarkedResidualTail_restrict_eq_smul_of_noHit
    ν markLaw hrate time htime htime_nonneg s hs
  calc
    Measure.map (fun z : ((β × γ) × (Nat -> Real)) × (Nat -> α) =>
        (externalTimeMarkedResidualTail (α := α) time ((z.1.1.1, z.1.2), z.2),
          z.1.1.2))
        (source.restrict lifted) =
        Measure.map output (Measure.map reorder (source.restrict lifted)) := by
          rw [Measure.map_map houtput hreorder.measurable]
          rfl
    _ = Measure.map output ((markedSource.prod κ).restrict carrier) := by
          rw [hrestrict]
    _ = Measure.map output ((markedSource.restrict A).prod κ) := by
          rw [← Measure.restrict_prod_eq_prod_univ]
    _ = (Measure.map residual (markedSource.restrict A)).prod κ := by
          rw [show output = Prod.map residual id by rfl,
            ← Measure.map_prod_map (markedSource.restrict A) κ hresidual measurable_id,
            Measure.map_id]
    _ = ((Measure.map (externalTimePastHistory time) (ν.prod gaps)).prod marks)
        (IIDStream.externalIndexNoHit
          (fun h : β × (Nat × (Nat -> Real)) => h.2.1) s) •
        ((gaps.prod marks).prod κ) := by
          rw [show Measure.map residual (markedSource.restrict A) =
              ((Measure.map (externalTimePastHistory time) (ν.prod gaps)).prod marks)
                (IIDStream.externalIndexNoHit
                  (fun h : β × (Nat × (Nat -> Real)) => h.2.1) s) •
                (gaps.prod marks) by
                simpa [residual, markedSource, A,
                  IIDStream.externalIndexNoHit] using hfactor,
            Measure.prod_smul_left]
    _ = ((Measure.map (externalTimePastHistory time)
        (ν.prod (exponentialInterarrivalMeasure rate))).prod
          (IIDStream.measure markLaw))
        (IIDStream.externalIndexNoHit
          (fun h : β × (Nat × (Nat -> Real)) => h.2.1) s) •
        (((exponentialInterarrivalMeasure rate).prod
          (IIDStream.measure markLaw)).prod κ) := by
          rfl

/-- An external observable and the marked residual input at its associated
clock time have a joint product law.  This retains the event-bearing external
coordinate explicitly, so later applications may restrict on a source event
without replacing it by an independent resample. -/
theorem externalTimeMarkedResidualTail_joint_hasLaw
    {β α γ : Type*} [MeasurableSpace β] [MeasurableSpace α] [MeasurableSpace γ]
    (ν : Measure β) [IsProbabilityMeasure ν]
    (markLaw : Measure α) [IsProbabilityMeasure markLaw]
    {rate : Real} (hrate : 0 < rate)
    (time : β -> Real) (htime : Measurable time)
    (htime_nonneg : ∀ b, 0 ≤ time b)
    (external : β -> γ) (hexternal : Measurable external) :
    HasLaw (fun z : (β × (Nat -> Real)) × (Nat -> α) =>
      (external z.1.1, externalTimeMarkedResidualTail (α := α) time z))
      ((Measure.map external ν).prod
        ((exponentialInterarrivalMeasure rate).prod (IIDStream.measure markLaw)))
      ((ν.prod (exponentialInterarrivalMeasure rate)).prod
        (IIDStream.measure markLaw)) := by
  let gaps : Measure (Nat -> Real) := exponentialInterarrivalMeasure rate
  let marks : Measure (Nat -> α) := IIDStream.measure markLaw
  let history : β × (Nat -> Real) -> β × (Nat × (Nat -> Real)) :=
    externalTimePastHistory time
  let residual : β × (Nat -> Real) -> Nat -> Real :=
    externalTimeResidualTail time
  let index : β × (Nat -> Real) -> Nat :=
    fun h => canonicalRenewalCount (time h.1) h.2
  let observed : β × (Nat -> Real) -> γ × (Nat -> Real) :=
    fun h => (external h.1, residual h)
  let source : Measure ((β × (Nat -> Real)) × (Nat -> α)) :=
    (ν.prod gaps).prod marks
  letI : IsProbabilityMeasure gaps := by
    simpa [gaps] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure marks := by
    dsimp [marks, IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure (ν.prod gaps) := by infer_instance
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  have hhistory : Measurable history := by
    simpa [history] using measurable_externalTimePastHistory time htime
  have hresidual : Measurable residual := by
    simpa [residual] using measurable_externalTimeResidualTail time htime
  have hindex : Measurable index := by
    exact measurable_canonicalRenewalCount_joint.comp
      ((htime.comp measurable_fst).prodMk measurable_snd)
  have hhistoryResidual : Measure.map (fun z : β × (Nat -> Real) =>
      (history z, residual z)) (ν.prod gaps) =
      (Measure.map history (ν.prod gaps)).prod gaps := by
    simpa [history, residual, gaps] using
      map_externalTimePastHistory_residualTail ν hrate time htime htime_nonneg
  have hobserved : Measurable observed := by
    exact (hexternal.comp measurable_fst).prodMk hresidual
  have hproject : Measurable (fun h : β × (Nat × (Nat -> Real)) => external h.1) :=
    hexternal.comp measurable_fst
  have hobservedLaw : Measure.map observed (ν.prod gaps) =
      (Measure.map external ν).prod gaps := by
    let projector : β × (Nat × (Nat -> Real)) -> γ :=
      fun h => external h.1
    let factor : (β × (Nat × (Nat -> Real))) × (Nat -> Real) ->
        γ × (Nat -> Real) := fun h => (projector h.1, h.2)
    have hprojector : Measurable projector := by
      simpa [projector] using hproject
    have hfactor : Measurable factor :=
      (hprojector.comp measurable_fst).prodMk measurable_snd
    have hprojectorLaw : Measure.map projector (Measure.map history (ν.prod gaps)) =
        Measure.map external ν := by
      calc
        Measure.map projector (Measure.map history (ν.prod gaps)) =
            Measure.map (projector ∘ history) (ν.prod gaps) := by
              rw [Measure.map_map hprojector hhistory]
        _ = Measure.map (external ∘ Prod.fst) (ν.prod gaps) := by
              rfl
        _ = Measure.map external (Measure.map Prod.fst (ν.prod gaps)) := by
              rw [Measure.map_map hexternal measurable_fst]
        _ = Measure.map external ν := by simp
    calc
      Measure.map observed (ν.prod gaps) =
          Measure.map factor (Measure.map (fun z : β × (Nat -> Real) =>
            (history z, residual z)) (ν.prod gaps)) := by
              rw [Measure.map_map hfactor (hhistory.prodMk hresidual)]
              rfl
      _ = Measure.map factor ((Measure.map history (ν.prod gaps)).prod gaps) := by
            rw [hhistoryResidual]
      _ = (Measure.map projector (Measure.map history (ν.prod gaps))).prod gaps := by
            rw [show factor = Prod.map projector id by rfl,
              ← Measure.map_prod_map _ _ hprojector measurable_id,
              Measure.map_id]
      _ = (Measure.map external ν).prod gaps := by rw [hprojectorLaw]
  have hmarked := IIDStream.externalIndexTail_joint_hasLaw
    (ν.prod gaps) markLaw index hindex observed hobserved
  have hraw : Measurable (fun z : (β × (Nat -> Real)) × (Nat -> α) =>
      (observed z.1, IIDStream.externalIndexTail (α := α) index z)) :=
    (hobserved.comp measurable_fst).prodMk
      (IIDStream.measurable_externalIndexTail (α := α) index hindex)
  let reassociate : (γ × (Nat -> Real)) × (Nat -> α) ->
      γ × ((Nat -> Real) × (Nat -> α)) := MeasurableEquiv.prodAssoc
  have hreassociate : Measurable reassociate := MeasurableEquiv.prodAssoc.measurable
  refine ⟨((hexternal.comp (measurable_fst.comp measurable_fst)).prodMk
    (measurable_externalTimeMarkedResidualTail (α := α) time htime)).aemeasurable, ?_⟩
  change Measure.map (reassociate ∘ fun z : (β × (Nat -> Real)) × (Nat -> α) =>
      (observed z.1, IIDStream.externalIndexTail (α := α) index z)) source =
      (Measure.map external ν).prod (gaps.prod marks)
  rw [← Measure.map_map hreassociate hraw, hmarked.map_eq, hobservedLaw]
  exact Measure.prodAssoc_prod

/-- An external-time marked residual may be formed while retaining both its
actual external clock coordinate and an independent companion.  The result is
an exact raw product law: neither the clock nor the companion is resampled.
This is the joint form needed to stop two independent marked renewal streams
at the same source-clock time. -/
theorem externalTimeMarkedResidualTail_withCompanion_joint_hasLaw
    {β α γ : Type*} [MeasurableSpace β] [MeasurableSpace α] [MeasurableSpace γ]
    (ν : Measure β) [IsProbabilityMeasure ν]
    (κ : Measure γ) [IsProbabilityMeasure κ]
    (markLaw : Measure α) [IsProbabilityMeasure markLaw]
    {rate : Real} (hrate : 0 < rate)
    (time : β -> Real) (htime : Measurable time)
    (htime_nonneg : ∀ b, 0 ≤ time b) :
    HasLaw (fun z : ((β × γ) × (Nat -> Real)) × (Nat -> α) =>
      ((z.1.1.1,
        externalTimeMarkedResidualTail (α := α) time
          ((z.1.1.1, z.1.2), z.2)), z.1.1.2))
      ((ν.prod ((exponentialInterarrivalMeasure rate).prod
        (IIDStream.measure markLaw))).prod κ)
      (((ν.prod κ).prod (exponentialInterarrivalMeasure rate)).prod
        (IIDStream.measure markLaw)) := by
  let gaps : Measure (Nat -> Real) := exponentialInterarrivalMeasure rate
  let marks : Measure (Nat -> α) := IIDStream.measure markLaw
  let markedSource : Measure ((β × (Nat -> Real)) × (Nat -> α)) :=
    (ν.prod gaps).prod marks
  let source : Measure (((β × γ) × (Nat -> Real)) × (Nat -> α)) :=
    ((ν.prod κ).prod gaps).prod marks
  let reorder : ((β × γ) × (Nat -> Real)) × (Nat -> α) ->
      ((β × (Nat -> Real)) × (Nat -> α)) × γ :=
    fun z => (((z.1.1.1, z.1.2), z.2), z.1.1.2)
  let output : ((β × (Nat -> Real)) × (Nat -> α)) ->
      β × ((Nat -> Real) × (Nat -> α)) :=
    fun z => (z.1.1, externalTimeMarkedResidualTail (α := α) time z)
  let outputPair : ((β × (Nat -> Real)) × (Nat -> α)) × γ ->
      (β × ((Nat -> Real) × (Nat -> α))) × γ :=
    Prod.map output id
  letI : IsProbabilityMeasure gaps := by
    simpa [gaps] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure marks := by
    dsimp [marks, IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure markedSource := by
    dsimp [markedSource]
    infer_instance
  letI : IsProbabilityMeasure source := by
    dsimp [source]
    infer_instance
  let assoc1 : ((β × γ) × (Nat -> Real)) × (Nat -> α) ->
      (β × γ) × ((Nat -> Real) × (Nat -> α)) :=
    MeasurableEquiv.prodAssoc
  let assoc2 : (β × γ) × ((Nat -> Real) × (Nat -> α)) ->
      β × (γ × ((Nat -> Real) × (Nat -> α))) :=
    MeasurableEquiv.prodAssoc
  let swapTail : β × (γ × ((Nat -> Real) × (Nat -> α))) ->
      β × (((Nat -> Real) × (Nat -> α)) × γ) :=
    Prod.map id Prod.swap
  let assoc3 : β × (((Nat -> Real) × (Nat -> α)) × γ) ->
      (β × ((Nat -> Real) × (Nat -> α))) × γ :=
    MeasurableEquiv.prodAssoc.symm
  let assoc4 : (β × ((Nat -> Real) × (Nat -> α))) × γ ->
      ((β × (Nat -> Real)) × (Nat -> α)) × γ :=
    Prod.map MeasurableEquiv.prodAssoc.symm id
  let p1 := measurePreserving_prodAssoc (ν.prod κ) gaps marks
  let p2 := measurePreserving_prodAssoc ν κ (gaps.prod marks)
  let swap : MeasurePreserving (Prod.swap : γ × ((Nat -> Real) × (Nat -> α)) ->
      ((Nat -> Real) × (Nat -> α)) × γ) (κ.prod (gaps.prod marks))
      ((gaps.prod marks).prod κ) :=
    ⟨measurable_swap, Measure.prod_swap⟩
  let p3 := MeasurePreserving.prod (MeasurePreserving.id ν) swap
  let p4 := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc ν (gaps.prod marks) κ)
  let p5 := MeasurePreserving.prod
    (MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc ν gaps marks))
    (MeasurePreserving.id κ)
  have hreorder : MeasurePreserving reorder source (markedSource.prod κ) := by
    have hfun : reorder = assoc4 ∘ assoc3 ∘ swapTail ∘ assoc2 ∘ assoc1 := by
      funext z
      rfl
    rw [hfun]
    simpa [assoc1, assoc2, swapTail, assoc3, assoc4, source, markedSource, gaps, marks] using
      (p5.comp (p4.comp (p3.comp (p2.comp p1))))
  have houtput : Measurable output := by
    exact (measurable_fst.comp measurable_fst).prodMk
      (measurable_externalTimeMarkedResidualTail (α := α) time htime)
  have houtputPair : Measurable outputPair := by
    change Measurable (fun z : ((β × (Nat -> Real)) × (Nat -> α)) × γ =>
      (output z.1, z.2))
    exact (houtput.comp measurable_fst).prodMk measurable_snd
  have hraw : Measurable (fun z : ((β × γ) × (Nat -> Real)) × (Nat -> α) =>
      ((z.1.1.1,
        externalTimeMarkedResidualTail (α := α) time
          ((z.1.1.1, z.1.2), z.2)), z.1.1.2)) := by
    have hmarkedInput : Measurable (fun z : ((β × γ) × (Nat -> Real)) ×
        (Nat -> α) => ((z.1.1.1, z.1.2), z.2)) :=
      ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_snd.comp measurable_fst)).prodMk measurable_snd
    exact ((houtput.comp hmarkedInput).prodMk
      (measurable_snd.comp (measurable_fst.comp measurable_fst)))
  have hmarked := externalTimeMarkedResidualTail_joint_hasLaw
    ν markLaw hrate time htime htime_nonneg id measurable_id
  have hmarkedLaw : Measure.map output markedSource =
      ν.prod (gaps.prod marks) := by
    simpa [output, markedSource, gaps, marks] using hmarked.map_eq
  refine ⟨hraw.aemeasurable, ?_⟩
  have hraw_comp : (fun z : ((β × γ) × (Nat -> Real)) × (Nat -> α) =>
      ((z.1.1.1,
        externalTimeMarkedResidualTail (α := α) time
          ((z.1.1.1, z.1.2), z.2)), z.1.1.2)) = outputPair ∘ reorder := by
    funext z
    rfl
  calc
    Measure.map (fun z : ((β × γ) × (Nat -> Real)) × (Nat -> α) =>
        ((z.1.1.1,
          externalTimeMarkedResidualTail (α := α) time
            ((z.1.1.1, z.1.2), z.2)), z.1.1.2)) source =
        Measure.map outputPair (Measure.map reorder source) := by
          rw [hraw_comp, Measure.map_map houtputPair hreorder.measurable]
    _ = Measure.map outputPair (markedSource.prod κ) := by rw [hreorder.map_eq]
    _ = (Measure.map output markedSource).prod (Measure.map id κ) := by
          symm
          simpa [outputPair] using
            (Measure.map_prod_map markedSource κ houtput measurable_id)
    _ = (ν.prod (gaps.prod marks)).prod κ := by rw [hmarkedLaw, Measure.map_id]
    _ = ((ν.prod ((exponentialInterarrivalMeasure rate).prod
        (IIDStream.measure markLaw))).prod κ) := by rfl

end

end AppliedModelingLib.Probability.PoissonProcess
