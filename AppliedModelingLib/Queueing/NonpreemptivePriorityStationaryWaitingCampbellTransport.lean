import AppliedModelingLib.Queueing.NonpreemptivePriorityStationaryWaitingCampbell
import AppliedModelingLib.Queueing.NonpreemptivePriorityStationaryClassCanonical
import Mathlib.Tactic

/-!
# Campbell transport of stationary priority waiting work

This module converts the selected-customer Borel replay reward into the
corresponding original-label canonical contribution on the physical-time
Campbell product.  The remaining countable Tonelli aggregation is deliberately
kept separate.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- On the physical-time Campbell product, a selected customer's Borel
finite-replay waiting-work reward agrees almost everywhere with the canonical
original-label contribution of that arrival.  The only excluded elapsed-time
slice is the arrival epoch itself, which is Lebesgue-null. -/
theorem ae_uncurry_stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN_campbellRecenter_eq_remoteCanonical
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) (k : ℤ) :
    (fun p : ℝ × (StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath)) =>
      stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN meanService i
        ((multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i).recenterAt p.2 k)
        (p.1 - Probability.Queueing.timedEmbeddedArrival p.2.1 k)) =ᵐ[
      MeasureTheory.volume.prod
        (Probability.Palm.targetPassiveProductBaseLaw
          (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Pbase]
      (fun p => ENNReal.ofReal
        (stationaryPriorityRemotePastWaitingIdentifierContributionCanonical meanService
          (Sigma.mk i k)
          (p.1, multiclassStationaryPoissonWorkClassAssemble i p.2))) := by
  let P := (Probability.Palm.targetPassiveProductBaseLaw
    (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Pbase
  let H := multiclassStationaryPoissonWorkClassCampbellCertificate
    arrivalRate harrivalRate i
  let F : (StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath)) × ℝ → ℝ≥0∞ :=
    fun p => stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN meanService i
      (H.recenterAt p.1 k) p.2
  let G : (StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath)) × ℝ → ℝ≥0∞ :=
    fun p => ENNReal.ofReal
      (stationaryPriorityRemotePastWaitingIdentifierContributionCanonical meanService
        (Sigma.mk i k)
        (H.baseArrivals p.1 k + p.2,
          multiclassStationaryPoissonWorkClassAssemble i p.1))
  let targetF : ℝ × (StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath)) → ℝ≥0∞ :=
    fun p => stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN meanService i
      (H.recenterAt p.2 k) (p.1 - H.baseArrivals p.2 k)
  let targetG : ℝ × (StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath)) → ℝ≥0∞ :=
    fun p => ENNReal.ofReal
      (stationaryPriorityRemotePastWaitingIdentifierContributionCanonical meanService
        (Sigma.mk i k)
        (p.1, multiclassStationaryPoissonWorkClassAssemble i p.2))
  change targetF =ᵐ[MeasureTheory.volume.prod P] targetG
  letI : IsProbabilityMeasure P := by
    simpa only [P] using
      (Probability.Palm.targetPassiveProductBaseLaw
        (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).isProbability
  letI : SFinite P := by infer_instance
  have hF : Measurable F := by
    simpa only [F] using
      (measurable_stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN
        meanService i).comp
        (((H.recenterAt_measurable k).comp measurable_fst).prodMk measurable_snd)
  have hG : Measurable G := by
    simpa only [G] using
      (measurable_uncurry_stationaryPriorityRemotePastWaitingIdentifierContributionCanonical
        meanService (Sigma.mk i k)).ennreal_ofReal.comp
        ((((H.baseArrivals_measurable k).comp measurable_fst).add measurable_snd).prodMk
          ((measurable_multiclassStationaryPoissonWorkClassAssemble i).comp measurable_fst))
  have hFGmeas : MeasurableSet {p | F p = G p} := measurableSet_eq_fun hF hG
  have hzero : ∀ᵐ t : ℝ ∂MeasureTheory.volume, t ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    have hset : {t : ℝ | ¬ t ≠ 0} = {0} := by
      ext t
      simp
    rw [hset, Real.volume_singleton]
  have hbase :=
    ae_forall_stationaryPriorityClassTaggedStabilizedWaitingWorkResponse_campbellRecenter_eq_remoteCanonical
      arrivalRate meanService harrivalRate hmeanService hstable i
  have hsections : ∀ᵐ x ∂P, ∀ᵐ t : ℝ ∂MeasureTheory.volume, F (x, t) = G (x, t) := by
    filter_upwards [hbase] with x hx
    filter_upwards [hzero] with t ht
    simpa [F, G, H, stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN] using
      congrArg ENNReal.ofReal (hx k t ht)
  have hFG : F =ᵐ[P.prod MeasureTheory.volume] G :=
    (MeasureTheory.Measure.ae_prod_iff_ae_ae hFGmeas).2 hsections
  have htargetF : Measurable targetF := by
    simpa only [targetF] using
      (measurable_stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN
        meanService i).comp
        (((H.recenterAt_measurable k).comp measurable_snd).prodMk
          (measurable_fst.sub ((H.baseArrivals_measurable k).comp measurable_snd)))
  have htargetG : Measurable targetG := by
    simpa only [targetG] using
      (measurable_uncurry_stationaryPriorityRemotePastWaitingIdentifierContributionCanonical
        meanService (Sigma.mk i k)).ennreal_ofReal.comp
        (measurable_fst.prodMk
          ((measurable_multiclassStationaryPoissonWorkClassAssemble i).comp measurable_snd))
  have htargetmeas : MeasurableSet {p | targetF p = targetG p} :=
    measurableSet_eq_fun htargetF htargetG
  let T : (StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath)) × ℝ →
      ℝ × (StationaryPoissonWorkPath ×
        ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath)) :=
    fun p => (H.baseArrivals p.1 k + p.2, p.1)
  have hT : MeasurePreserving T (P.prod MeasureTheory.volume)
      (MeasureTheory.volume.prod P) := by
    simpa only [T] using
      (Probability.Palm.measurePreserving_prod_add_measurable_swap P
        (H.baseArrivals · k) (H.baseArrivals_measurable k))
  have htargetF_comp_T : targetF ∘ T = F := by
    funext p
    simp only [targetF, T, F, Function.comp_apply, add_sub_cancel_left]
  have htargetG_comp_T : targetG ∘ T = G := by
    funext p
    rfl
  have hmap : ∀ᵐ p ∂Measure.map T (P.prod MeasureTheory.volume),
      targetF p = targetG p := by
    rw [MeasureTheory.ae_map_iff hT.measurable.aemeasurable htargetmeas]
    filter_upwards [hFG] with p hp
    calc
      targetF (T p) = F p := congrFun htargetF_comp_T p
      _ = G p := hp
      _ = targetG (T p) := (congrFun htargetG_comp_T p).symm
  rw [hT.map_eq] at hmap
  exact hmap

/-- Integrating one labelled selected-customer replay reward over a physical
interval is the same as integrating that label's canonical contribution under
the stationary multiclass input law.  This combines the per-label Campbell
transport with the class-split product-law equivalence; summing labels is a
separate Tonelli step. -/
theorem lintegral_indicator_stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN_eq_canonical
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) (k : ℤ) (a b : ℝ) :
    (∫⁻ p : ℝ × (StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath)),
        if p.1 ∈ Set.Ico a b then
          stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN meanService i
            ((multiclassStationaryPoissonWorkClassCampbellCertificate
              arrivalRate harrivalRate i).recenterAt p.2 k)
            (p.1 - Probability.Queueing.timedEmbeddedArrival p.2.1 k)
        else 0 ∂(MeasureTheory.volume.prod
          (Probability.Palm.targetPassiveProductBaseLaw
            (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
            (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Pbase)) =
      ∫⁻ p : ℝ × (Fin n → StationaryPoissonWorkPath),
        if p.1 ∈ Set.Ico a b then
          ENNReal.ofReal
            (stationaryPriorityRemotePastWaitingIdentifierContributionCanonical meanService
              (Sigma.mk i k) p)
        else 0 ∂(MeasureTheory.volume.prod
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)) := by
  classical
  let Pbase := (Probability.Palm.targetPassiveProductBaseLaw
    (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Pbase
  let Pstationary := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  letI : IsProbabilityMeasure Pbase := by
    simpa only [Pbase] using
      (Probability.Palm.targetPassiveProductBaseLaw
        (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).isProbability
  letI : SFinite Pbase := by infer_instance
  letI : IsProbabilityMeasure Pstationary := by
    simpa only [Pstationary] using
      Probability.PoissonProcess.isProbabilityMeasure_multiclassStationaryPoissonWorkMeasure
        arrivalRate harrivalRate
  letI : SFinite Pstationary := by infer_instance
  letI : IsProbabilityMeasure
      (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i)).Pbase :=
    (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i)).isProbability
  letI : IsProbabilityMeasure
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).Pbase :=
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).isProbability
  let sourceResponse : ℝ × (StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath)) → ℝ≥0∞ :=
    fun p => if p.1 ∈ Set.Ico a b then
      stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN meanService i
        ((multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i).recenterAt p.2 k)
        (p.1 - Probability.Queueing.timedEmbeddedArrival p.2.1 k)
      else 0
  let sourceCanonical : ℝ × (StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath)) → ℝ≥0∞ :=
    fun p => if p.1 ∈ Set.Ico a b then
      ENNReal.ofReal
        (stationaryPriorityRemotePastWaitingIdentifierContributionCanonical meanService
          (Sigma.mk i k) (p.1, multiclassStationaryPoissonWorkClassAssemble i p.2))
      else 0
  let targetCanonical : ℝ × (Fin n → StationaryPoissonWorkPath) → ℝ≥0∞ :=
    fun p => if p.1 ∈ Set.Ico a b then
      ENNReal.ofReal
        (stationaryPriorityRemotePastWaitingIdentifierContributionCanonical meanService
          (Sigma.mk i k) p)
      else 0
  change (∫⁻ p, sourceResponse p ∂MeasureTheory.volume.prod Pbase) =
    ∫⁻ p, targetCanonical p ∂MeasureTheory.volume.prod Pstationary
  have htransport : sourceResponse =ᵐ[MeasureTheory.volume.prod Pbase] sourceCanonical := by
    filter_upwards [
      ae_uncurry_stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN_campbellRecenter_eq_remoteCanonical
        arrivalRate meanService harrivalRate hmeanService hstable i k] with p hp
    by_cases hmem : p.1 ∈ Set.Ico a b
    · simp only [sourceResponse, sourceCanonical, hmem, if_true]
      exact hp
    · simp only [sourceResponse, sourceCanonical, hmem, if_false]
  have htargetmeas : Measurable targetCanonical := by
    let f : ℝ × (Fin n → StationaryPoissonWorkPath) → ℝ≥0∞ := fun p =>
      ENNReal.ofReal
        (stationaryPriorityRemotePastWaitingIdentifierContributionCanonical meanService
          (Sigma.mk i k) p)
    have hf : Measurable f := by
      simpa only [f] using
        (measurable_uncurry_stationaryPriorityRemotePastWaitingIdentifierContributionCanonical
          meanService (Sigma.mk i k)).ennreal_ofReal
    change Measurable (fun p : ℝ × (Fin n → StationaryPoissonWorkPath) =>
      if p.1 ∈ Set.Ico a b then f p else 0)
    exact Measurable.ite
      (p := fun p : ℝ × (Fin n → StationaryPoissonWorkPath) => p.1 ∈ Set.Ico a b)
      (measurableSet_Ico.preimage measurable_fst) hf measurable_const
  let L : ℝ × (StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath)) →
      ℝ × (Fin n → StationaryPoissonWorkPath) := fun p =>
    (p.1, multiclassStationaryPoissonWorkClassAssemble i p.2)
  have hL : MeasurePreserving L (MeasureTheory.volume.prod Pbase)
      (MeasureTheory.volume.prod Pstationary) := by
    simpa only [L, Pbase, Pstationary, Prod.map_apply] using
      ((MeasurePreserving.id (μ := (MeasureTheory.volume : Measure ℝ))).prod
        (measurePreserving_multiclassStationaryPoissonWorkClassAssemble
          arrivalRate harrivalRate i))
  have hsourceCanonical : sourceCanonical = targetCanonical ∘ L := by
    funext p
    rfl
  calc
    (∫⁻ p, sourceResponse p ∂MeasureTheory.volume.prod Pbase) =
        ∫⁻ p, sourceCanonical p ∂MeasureTheory.volume.prod Pbase :=
      MeasureTheory.lintegral_congr_ae htransport
    _ = ∫⁻ p, targetCanonical (L p) ∂MeasureTheory.volume.prod Pbase := by
      apply MeasureTheory.lintegral_congr
      intro p
      exact congrFun hsourceCanonical p
    _ = ∫⁻ p, targetCanonical p ∂MeasureTheory.volume.prod Pstationary :=
      hL.lintegral_comp htargetmeas

/-- Tonelli aggregation of every labelled arrival in one class turns the
physical-time replay rewards into the classwise canonical stationary
waiting-work sum. -/
theorem tsum_lintegral_indicator_stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN_eq_classCanonical
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) (a b : ℝ) :
    (∑' k : ℤ, ∫⁻ p : ℝ × (StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath)),
        if p.1 ∈ Set.Ico a b then
          stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN meanService i
            ((multiclassStationaryPoissonWorkClassCampbellCertificate
              arrivalRate harrivalRate i).recenterAt p.2 k)
            (p.1 - Probability.Queueing.timedEmbeddedArrival p.2.1 k)
        else 0 ∂(MeasureTheory.volume.prod
          (Probability.Palm.targetPassiveProductBaseLaw
            (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
            (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Pbase)) =
      ∫⁻ p : ℝ × (Fin n → StationaryPoissonWorkPath),
        if p.1 ∈ Set.Ico a b then
          stationaryPriorityRemotePastClassWaitingWorkCanonicalNN meanService i p
        else 0 ∂(MeasureTheory.volume.prod
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)) := by
  classical
  let Pstationary := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let f : ℤ → ℝ × (Fin n → StationaryPoissonWorkPath) → ℝ≥0∞ := fun k p =>
    if p.1 ∈ Set.Ico a b then
      ENNReal.ofReal
        (stationaryPriorityRemotePastWaitingIdentifierContributionCanonical meanService
          (Sigma.mk i k) p)
    else 0
  let g : ℝ × (Fin n → StationaryPoissonWorkPath) → ℝ≥0∞ := fun p =>
    if p.1 ∈ Set.Ico a b then
      stationaryPriorityRemotePastClassWaitingWorkCanonicalNN meanService i p
    else 0
  change (∑' k : ℤ, ∫⁻ p : ℝ × (StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath)),
        if p.1 ∈ Set.Ico a b then
          stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN meanService i
            ((multiclassStationaryPoissonWorkClassCampbellCertificate
              arrivalRate harrivalRate i).recenterAt p.2 k)
            (p.1 - Probability.Queueing.timedEmbeddedArrival p.2.1 k)
        else 0 ∂(MeasureTheory.volume.prod
          (Probability.Palm.targetPassiveProductBaseLaw
            (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
            (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Pbase)) =
      ∫⁻ p, g p ∂MeasureTheory.volume.prod Pstationary
  have hf : ∀ k : ℤ, Measurable (f k) := by
    intro k
    let h : ℝ × (Fin n → StationaryPoissonWorkPath) → ℝ≥0∞ := fun p =>
      ENNReal.ofReal
        (stationaryPriorityRemotePastWaitingIdentifierContributionCanonical meanService
          (Sigma.mk i k) p)
    have hh : Measurable h := by
      simpa only [h] using
        (measurable_uncurry_stationaryPriorityRemotePastWaitingIdentifierContributionCanonical
          meanService (Sigma.mk i k)).ennreal_ofReal
    change Measurable (fun p : ℝ × (Fin n → StationaryPoissonWorkPath) =>
      if p.1 ∈ Set.Ico a b then h p else 0)
    exact Measurable.ite
      (p := fun p : ℝ × (Fin n → StationaryPoissonWorkPath) => p.1 ∈ Set.Ico a b)
      (measurableSet_Ico.preimage measurable_fst) hh measurable_const
  have hlabel : ∀ k : ℤ,
      (∫⁻ p : ℝ × (StationaryPoissonWorkPath ×
        ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath)),
          if p.1 ∈ Set.Ico a b then
            stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN meanService i
              ((multiclassStationaryPoissonWorkClassCampbellCertificate
                arrivalRate harrivalRate i).recenterAt p.2 k)
              (p.1 - Probability.Queueing.timedEmbeddedArrival p.2.1 k)
          else 0 ∂(MeasureTheory.volume.prod
            (Probability.Palm.targetPassiveProductBaseLaw
              (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
              (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Pbase)) =
        ∫⁻ p, f k p ∂MeasureTheory.volume.prod Pstationary := by
    intro k
    simpa only [f, Pstationary] using
      (lintegral_indicator_stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN_eq_canonical
        arrivalRate meanService harrivalRate hmeanService hstable i k a b)
  calc
    (∑' k : ℤ, ∫⁻ p : ℝ × (StationaryPoissonWorkPath ×
        ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath)),
          if p.1 ∈ Set.Ico a b then
            stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN meanService i
              ((multiclassStationaryPoissonWorkClassCampbellCertificate
                arrivalRate harrivalRate i).recenterAt p.2 k)
              (p.1 - Probability.Queueing.timedEmbeddedArrival p.2.1 k)
          else 0 ∂(MeasureTheory.volume.prod
            (Probability.Palm.targetPassiveProductBaseLaw
              (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
              (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Pbase)) =
        ∑' k : ℤ, ∫⁻ p, f k p ∂MeasureTheory.volume.prod Pstationary := by
          apply tsum_congr
          exact hlabel
    _ = ∫⁻ p, ∑' k : ℤ, f k p ∂MeasureTheory.volume.prod Pstationary := by
      rw [MeasureTheory.lintegral_tsum]
      intro k
      exact (hf k).aemeasurable
    _ = ∫⁻ p, g p ∂MeasureTheory.volume.prod Pstationary := by
      apply MeasureTheory.lintegral_congr
      intro p
      by_cases hmem : p.1 ∈ Set.Ico a b
      · simp only [f, g, hmem, if_true,
          stationaryPriorityRemotePastClassWaitingWorkCanonicalNN]
      · simp only [f, g, hmem, if_false, tsum_zero]

/-- The class-tagged Campbell coverage of the nonnegative selected-customer
waiting-work reward over a physical interval is the corresponding classwise
canonical workload integrated under the stationary multiclass input law. -/
theorem arrivalTimeCampbellCoverage_stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN_Ico_eq_lintegral_classCanonical
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) (a b : ℝ) :
    Probability.Palm.arrivalTimeCampbellCoverage
        (multiclassStationaryPoissonWorkClassCampbellCertificate arrivalRate harrivalRate i)
        (stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN meanService i)
        (Set.Ico a b) =
      ∫⁻ p : ℝ × (Fin n → StationaryPoissonWorkPath),
        if p.1 ∈ Set.Ico a b then
          stationaryPriorityRemotePastClassWaitingWorkCanonicalNN meanService i p
        else 0 ∂(MeasureTheory.volume.prod
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)) := by
  rw [Probability.Palm.arrivalTimeCampbellCoverage_Ico_eq_tsum_physicalTime
    (multiclassStationaryPoissonWorkClassCampbellCertificate arrivalRate harrivalRate i)
    (stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN meanService i)
    (measurable_stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN meanService i) a b]
  exact
    tsum_lintegral_indicator_stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN_eq_classCanonical
      arrivalRate meanService harrivalRate hmeanService hstable i a b

/-- Aggregating the class-tagged Campbell coverage through a priority level
produces the stationary canonical workload of all customers at least as
urgent as that level over the same physical interval. -/
theorem sum_arrivalTimeCampbellCoverage_stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN_Ico_eq_lintegral_atLeastAsUrgentCanonical
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (priority : Fin n) (a b : ℝ) :
    (∑ i ∈ Finset.univ.filter (fun j : Fin n => j ≤ priority),
      Probability.Palm.arrivalTimeCampbellCoverage
        (multiclassStationaryPoissonWorkClassCampbellCertificate arrivalRate harrivalRate i)
        (stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN meanService i)
        (Set.Ico a b)) =
      ∫⁻ p : ℝ × (Fin n → StationaryPoissonWorkPath),
        if p.1 ∈ Set.Ico a b then
          stationaryPriorityRemotePastAtLeastAsUrgentWaitingWorkCanonicalNN meanService priority p
        else 0 ∂(MeasureTheory.volume.prod
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)) := by
  classical
  let P := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let s : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => j ≤ priority)
  let f : Fin n → ℝ × (Fin n → StationaryPoissonWorkPath) → ℝ≥0∞ := fun i p =>
    if p.1 ∈ Set.Ico a b then
      stationaryPriorityRemotePastClassWaitingWorkCanonicalNN meanService i p
    else 0
  let g : ℝ × (Fin n → StationaryPoissonWorkPath) → ℝ≥0∞ := fun p =>
    if p.1 ∈ Set.Ico a b then
      stationaryPriorityRemotePastAtLeastAsUrgentWaitingWorkCanonicalNN meanService priority p
    else 0
  change (∑ i ∈ s,
      Probability.Palm.arrivalTimeCampbellCoverage
        (multiclassStationaryPoissonWorkClassCampbellCertificate arrivalRate harrivalRate i)
        (stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN meanService i)
        (Set.Ico a b)) =
      ∫⁻ p, g p ∂MeasureTheory.volume.prod P
  have hf : ∀ i ∈ s, Measurable (f i) := by
    intro i _
    let h : ℝ × (Fin n → StationaryPoissonWorkPath) → ℝ≥0∞ := fun p =>
      stationaryPriorityRemotePastClassWaitingWorkCanonicalNN meanService i p
    have hh : Measurable h := by
      simpa only [h] using
        measurable_uncurry_stationaryPriorityRemotePastClassWaitingWorkCanonicalNN meanService i
    change Measurable (fun p : ℝ × (Fin n → StationaryPoissonWorkPath) =>
      if p.1 ∈ Set.Ico a b then h p else 0)
    exact Measurable.ite
      (p := fun p : ℝ × (Fin n → StationaryPoissonWorkPath) => p.1 ∈ Set.Ico a b)
      (measurableSet_Ico.preimage measurable_fst) hh measurable_const
  have hcoverage : ∀ i : Fin n,
      Probability.Palm.arrivalTimeCampbellCoverage
          (multiclassStationaryPoissonWorkClassCampbellCertificate arrivalRate harrivalRate i)
          (stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN meanService i)
          (Set.Ico a b) =
        ∫⁻ p, f i p ∂MeasureTheory.volume.prod P := by
    intro i
    simpa only [f, P] using
      arrivalTimeCampbellCoverage_stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN_Ico_eq_lintegral_classCanonical
        arrivalRate meanService harrivalRate hmeanService hstable i a b
  calc
    (∑ i ∈ s,
        Probability.Palm.arrivalTimeCampbellCoverage
          (multiclassStationaryPoissonWorkClassCampbellCertificate arrivalRate harrivalRate i)
          (stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN meanService i)
          (Set.Ico a b)) =
        ∑ i ∈ s, ∫⁻ p, f i p ∂MeasureTheory.volume.prod P := by
          apply Finset.sum_congr rfl
          intro i _
          exact hcoverage i
    _ = ∫⁻ p, ∑ i ∈ s, f i p ∂MeasureTheory.volume.prod P := by
      symm
      simpa only using MeasureTheory.lintegral_finset_sum' (μ := MeasureTheory.volume.prod P) s
        (fun i hi => (hf i hi).aemeasurable)
    _ = ∫⁻ p, g p ∂MeasureTheory.volume.prod P := by
      apply MeasureTheory.lintegral_congr
      intro p
      by_cases hmem : p.1 ∈ Set.Ico a b
      · simpa only [s, f, g, hmem, if_true] using
          sum_stationaryPriorityRemotePastClassWaitingWorkCanonicalNN_eq_atLeastAsUrgent
            meanService priority p
      · simp only [f, g, hmem, if_false, Finset.sum_const_zero]

/-- The stationary priority-filtered waiting workload equals the sum of the
arrival rates times the selected-Palm work-times-wait means of every class at
least as urgent as the given priority.  This is the waiting-work occupation
identity used in the nonpreemptive-priority mean-work balance. -/
theorem sum_arrivalRate_mul_lintegral_stationaryPriorityClassTaggedWorkQueueWaitRewardNN_eq_lintegral_remotePastAtLeastAsUrgentWaitingWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (priority : Fin n) :
    (∑ i ∈ Finset.univ.filter (fun j : Fin n => j ≤ priority),
      ENNReal.ofReal (arrivalRate i) *
        (∫⁻ z, stationaryPriorityClassTaggedWorkQueueWaitRewardNN meanService i z ∂
          stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate i)) =
      ∫⁻ omega, ENNReal.ofReal
        (stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService priority omega) ∂
          Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate := by
  classical
  let P := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let s : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => j ≤ priority)
  let f : (Fin n → StationaryPoissonWorkPath) → ℝ≥0∞ := fun omega =>
    ENNReal.ofReal
      (stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService priority omega)
  let G : ℝ × (Fin n → StationaryPoissonWorkPath) → ℝ≥0∞ := fun p =>
    f (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow p.1 p.2)
  let μI : Measure ℝ := MeasureTheory.volume.restrict (Set.Ico (0 : ℝ) 1)
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact Probability.PoissonProcess.isProbabilityMeasure_multiclassStationaryPoissonWorkMeasure
      arrivalRate harrivalRate
  letI : SFinite P := by infer_instance
  letI : IsFiniteMeasure μI := by
    dsimp [μI]
    infer_instance
  have hselected : ∀ i : Fin n,
      Probability.Palm.arrivalTimeCampbellCoverage
          (multiclassStationaryPoissonWorkClassCampbellCertificate arrivalRate harrivalRate i)
          (stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN meanService i)
          (Set.Ico (0 : ℝ) 1) =
        ENNReal.ofReal (arrivalRate i) *
          (∫⁻ z, stationaryPriorityClassTaggedWorkQueueWaitRewardNN meanService i z ∂
            stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate i) := by
    intro i
    simpa only [stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN,
      sub_zero, ENNReal.ofReal_one, mul_one] using
      arrivalTimeCampbellCoverage_stationaryPriorityClassTaggedStabilizedWaitingWorkResponse_Ico_eq_rate_mul_lintegral_workQueueWaitRewardNN
        arrivalRate meanService harrivalRate hmeanService hstable i 0 1
  have hintegrable :=
    integrable_stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork_of_totalStable
      arrivalRate meanService harrivalRate hmeanService hstable priority
  have hf : AEMeasurable f P := by
    simpa only [f, P] using hintegrable.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hcanonical :
      stationaryPriorityRemotePastAtLeastAsUrgentWaitingWorkCanonicalNN meanService priority =ᵐ[
        MeasureTheory.volume.prod P] G := by
    simpa only [P, f, G] using
      ae_uncurry_stationaryPriorityRemotePastAtLeastAsUrgentWaitingWorkCanonicalNN_eq_remotePast_flow
        arrivalRate meanService harrivalRate hmeanService hstable priority
  have hindicator :
      (fun p : ℝ × (Fin n → StationaryPoissonWorkPath) =>
        if p.1 ∈ Set.Ico (0 : ℝ) 1 then
          stationaryPriorityRemotePastAtLeastAsUrgentWaitingWorkCanonicalNN meanService priority p
        else 0) =ᵐ[MeasureTheory.volume.prod P]
      (fun p => if p.1 ∈ Set.Ico (0 : ℝ) 1 then G p else 0) := by
    filter_upwards [hcanonical] with p hp
    by_cases hmem : p.1 ∈ Set.Ico (0 : ℝ) 1
    · simp only [hmem, if_true, hp]
    · simp only [hmem, if_false]
  have hrestrict :
      (∫⁻ p : ℝ × (Fin n → StationaryPoissonWorkPath),
        if p.1 ∈ Set.Ico (0 : ℝ) 1 then G p else 0 ∂MeasureTheory.volume.prod P) =
      ∫⁻ p, G p ∂(μI.prod P) := by
    let E : Set (ℝ × (Fin n → StationaryPoissonWorkPath)) :=
      Set.Ico (0 : ℝ) 1 ×ˢ Set.univ
    have hE : MeasurableSet E :=
      measurableSet_Ico.prod MeasurableSet.univ
    have hindicator_eq :
        (fun p : ℝ × (Fin n → StationaryPoissonWorkPath) =>
          if p.1 ∈ Set.Ico (0 : ℝ) 1 then G p else 0) = E.indicator G := by
      funext p
      simp only [E, Set.mem_prod, Set.mem_univ, and_true, Set.indicator]
    rw [hindicator_eq, MeasureTheory.lintegral_indicator hE]
    change ∫⁻ p, G p ∂((MeasureTheory.volume.prod P).restrict E) = _
    rw [← Measure.restrict_prod_eq_prod_univ]
  have hunit : μI Set.univ = 1 := by
    simp only [μI, Measure.restrict_apply_univ, Real.volume_Ico, sub_zero,
      ENNReal.ofReal_one]
  have hstationary : (∫⁻ p, G p ∂(μI.prod P)) = ∫⁻ omega, f omega ∂P := by
    have hraw :=
      Probability.PoissonProcess.lintegral_uncurry_comp_multiclassStationaryPoissonWorkFlow
        arrivalRate harrivalRate μI f (by simpa only [P] using hf)
    rw [hunit, one_mul] at hraw
    simpa only [P, G] using hraw
  calc
    (∑ i ∈ s, ENNReal.ofReal (arrivalRate i) *
        (∫⁻ z, stationaryPriorityClassTaggedWorkQueueWaitRewardNN meanService i z ∂
          stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate i)) =
        ∑ i ∈ s,
          Probability.Palm.arrivalTimeCampbellCoverage
            (multiclassStationaryPoissonWorkClassCampbellCertificate arrivalRate harrivalRate i)
            (stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN meanService i)
            (Set.Ico (0 : ℝ) 1) := by
              apply Finset.sum_congr rfl
              intro i _
              exact (hselected i).symm
    _ = ∫⁻ p : ℝ × (Fin n → StationaryPoissonWorkPath),
        if p.1 ∈ Set.Ico (0 : ℝ) 1 then
          stationaryPriorityRemotePastAtLeastAsUrgentWaitingWorkCanonicalNN meanService priority p
        else 0 ∂MeasureTheory.volume.prod P := by
          simpa only [s, P] using
            sum_arrivalTimeCampbellCoverage_stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN_Ico_eq_lintegral_atLeastAsUrgentCanonical
              arrivalRate meanService harrivalRate hmeanService hstable priority 0 1
    _ = ∫⁻ p : ℝ × (Fin n → StationaryPoissonWorkPath),
        if p.1 ∈ Set.Ico (0 : ℝ) 1 then G p else 0 ∂MeasureTheory.volume.prod P :=
      MeasureTheory.lintegral_congr_ae hindicator
    _ = ∫⁻ p, G p ∂(μI.prod P) := hrestrict
    _ = ∫⁻ omega, f omega ∂P := hstationary
    _ = ∫⁻ omega, ENNReal.ofReal
        (stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService priority omega) ∂P := by
          rfl

/-- The real-valued form of the stationary waiting-work transport.  The
extended-real Campbell aggregation above is converted only after the existing
selected-Palm and stationary integrability results establish finiteness and
nonnegativity of every term. -/
theorem sum_arrivalRate_mul_integral_stationaryPriorityClassTaggedWorkRequirement_mul_queueWait_eq_integral_remotePastAtLeastAsUrgentWaitingWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (priority : Fin n) :
    (∑ i ∈ Finset.univ.filter (fun j : Fin n => j ≤ priority),
      arrivalRate i *
        (∫ z, stationaryPriorityClassTaggedWorkRequirement meanService i z *
          stationaryPriorityClassTaggedQueueWait meanService i z ∂
          stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate i)) =
      ∫ omega, stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService priority omega ∂
        Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => j ≤ priority)
  let P := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let selectedP := stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate priority
  let remote := stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService priority
  change (∑ i ∈ s,
      arrivalRate i *
        (∫ z, stationaryPriorityClassTaggedWorkRequirement meanService i z *
          stationaryPriorityClassTaggedQueueWait meanService i z ∂
          stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate i)) =
    ∫ omega, remote omega ∂P
  have hintegrable : ∀ i : Fin n,
      Integrable (fun z => stationaryPriorityClassTaggedWorkRequirement meanService i z *
        stationaryPriorityClassTaggedQueueWait meanService i z)
        (stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate i) := by
    intro i
    simpa only [stationaryPriorityClassTaggedPalmMeasure] using
      (integrable_stationaryPriorityClassTaggedWorkRequirement_mul_queueWait
        arrivalRate meanService harrivalRate hmeanService hstable i)
  have hworkWaitNonnegative : ∀ i : Fin n,
      0 ≤ᵐ[stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate i]
        (fun z => stationaryPriorityClassTaggedWorkRequirement meanService i z *
          stationaryPriorityClassTaggedQueueWait meanService i z) := by
    intro i
    filter_upwards [
      ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
        arrivalRate meanService harrivalRate hmeanService i,
      ae_nonneg_stationaryPriorityClassTaggedQueueWait
        arrivalRate meanService harrivalRate hmeanService hstable i] with z hwork hwait
    have hwork' : 0 ≤ stationaryPriorityClassTaggedWorkRequirement meanService i z := by
      have hpositive : 0 < stationaryPriorityClassTaggedWorkRequirement meanService i z := by
        simpa [stationaryPriorityClassTaggedWorkRequirement_eq_fullCoordinate] using hwork i 0
      exact hpositive.le
    exact mul_nonneg hwork' hwait
  have hrewardIntegral : ∀ i : Fin n,
      ENNReal.ofReal
          (∫ z, stationaryPriorityClassTaggedWorkRequirement meanService i z *
            stationaryPriorityClassTaggedQueueWait meanService i z ∂
            stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate i) =
        ∫⁻ z, stationaryPriorityClassTaggedWorkQueueWaitRewardNN meanService i z ∂
          stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate i := by
    intro i
    simpa only [stationaryPriorityClassTaggedWorkQueueWaitRewardNN] using
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (hintegrable i) (hworkWaitNonnegative i))
  have hremoteIntegrable : Integrable remote P := by
    simpa only [remote, P] using
      (integrable_stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork_of_totalStable
        arrivalRate meanService harrivalRate hmeanService hstable priority)
  have hstationaryLaw : HasLaw remote (P.map remote) P := ⟨by
    simpa only [remote, P] using
      (aemeasurable_stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork
        arrivalRate meanService harrivalRate hmeanService hstable priority), rfl⟩
  have hselectedLaw : HasLaw
      (stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork meanService priority)
      (P.map remote) selectedP := by
    simpa only [remote, P, selectedP] using
      (stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork_hasLaw_stationary
        arrivalRate meanService harrivalRate hmeanService hstable priority)
  have hremoteNonnegative : ∀ᵐ omega ∂P, 0 ≤ remote omega := by
    apply (hstationaryLaw.ae_iff (p := fun x : ℝ => 0 ≤ x) (by fun_prop)).mpr
    apply (hselectedLaw.ae_iff (p := fun x : ℝ => 0 ≤ x) (by fun_prop)).mp
    simpa only [selectedP, stationaryPriorityClassTaggedPalmMeasure] using
      (ae_nonneg_stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork
        arrivalRate meanService harrivalRate hmeanService hstable priority)
  have hremoteIntegral : ENNReal.ofReal (∫ omega, remote omega ∂P) =
      ∫⁻ omega, ENNReal.ofReal (remote omega) ∂P :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hremoteIntegrable hremoteNonnegative
  have hleftNonnegative : 0 ≤ ∑ i ∈ s,
      arrivalRate i *
        (∫ z, stationaryPriorityClassTaggedWorkRequirement meanService i z *
          stationaryPriorityClassTaggedQueueWait meanService i z ∂
          stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate i) := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (harrivalRate i).le
      (MeasureTheory.integral_nonneg_of_ae (hworkWaitNonnegative i))
  have htransport :=
    sum_arrivalRate_mul_lintegral_stationaryPriorityClassTaggedWorkQueueWaitRewardNN_eq_lintegral_remotePastAtLeastAsUrgentWaitingWork
      arrivalRate meanService harrivalRate hmeanService hstable priority
  apply (ENNReal.ofReal_eq_ofReal_iff hleftNonnegative
    (MeasureTheory.integral_nonneg_of_ae hremoteNonnegative)).mp
  calc
    ENNReal.ofReal (∑ i ∈ s,
        arrivalRate i *
          (∫ z, stationaryPriorityClassTaggedWorkRequirement meanService i z *
            stationaryPriorityClassTaggedQueueWait meanService i z ∂
            stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate i)) =
        ∑ i ∈ s, ENNReal.ofReal
          (arrivalRate i *
            (∫ z, stationaryPriorityClassTaggedWorkRequirement meanService i z *
              stationaryPriorityClassTaggedQueueWait meanService i z ∂
              stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate i)) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro i _
          exact mul_nonneg (harrivalRate i).le
            (MeasureTheory.integral_nonneg_of_ae (hworkWaitNonnegative i))
    _ = ∑ i ∈ s, ENNReal.ofReal (arrivalRate i) *
        (∫⁻ z, stationaryPriorityClassTaggedWorkQueueWaitRewardNN meanService i z ∂
          stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [ENNReal.ofReal_mul (harrivalRate i).le, hrewardIntegral i]
    _ = ∫⁻ omega, ENNReal.ofReal (remote omega) ∂P := by
          simpa only [s, remote, P] using htransport
    _ = ENNReal.ofReal (∫ omega, remote omega ∂P) := hremoteIntegral.symm

end

end AppliedModelingLib.Queueing
