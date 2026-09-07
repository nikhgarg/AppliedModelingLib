import AppliedModelingLib.Queueing.MM1.ForwardReverse.MarkedPalm
import AppliedModelingLib.Queueing.MM1.PostTagFalseMarkCount
import AppliedModelingLib.Queueing.MM1.AnalyticTail

/-!
# Post-tag potential-service counts on the direct marked-Palm M/M/1 path

This module connects the actual selected true-arrival Palm carrier to the
finite marked-Poisson thinning construction.  It proves the fixed-horizon
law of the path-derived post-tag `false`-mark count, jointly with the
pre-arrival queue length.  It does not construct queue response dynamics or
a fluid GPS path.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

noncomputable section

open PoissonProcess

/-- At a fixed horizon, the selected true-arrival Palm path has the joint law
of its pre-arrival queue length, its all-event Poisson-clock count, and every
finite block of subsequent iid uniformization marks. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_state_allEventCount_futureMarkPrefix_hasLaw
    {rate t : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho) (ht : 0 ≤ t) (n : ℕ) :
    HasLaw
      (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) =>
        ((z.2 0).1, (canonicalRenewalCount t (suspensionFuturePath z.1),
          fun i : Fin n => (z.2 (Int.ofNat (i.1 + 1))).2)))
      ((geoNNPMF rho hrho).toMeasure.prod
        ((ProbabilityTheory.poissonMeasure
          (⟨rate * t, mul_nonneg hrate.le ht⟩ : ℝ≥0)).prod
          (FiniteHorizonMarkedPoisson.iidMarks (uniformizedBirthProbability rho)
            (uniformizedBirthProbability_le_one rho) n).toMeasure))
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag := by
  let G : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let π : Measure ℕ := (geoNNPMF rho hrho).toMeasure
  let p : ℝ≥0 := uniformizedBirthProbability rho
  let hp : p ≤ 1 := uniformizedBirthProbability_le_one rho
  let I : Measure (Fin n → Bool) :=
    (FiniteHorizonMarkedPoisson.iidMarks p hp n).toMeasure
  let C : Measure ℕ := ProbabilityTheory.poissonMeasure
    (⟨rate * t, mul_nonneg hrate.le ht⟩ : ℝ≥0)
  let P : Measure ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) :=
    ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
      hrate rho hrho).conditionOn
        (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
          hrate rho hrho hrho_pos)).Ptag
  let stat : (ℤ → (ℕ × Bool)) → ℕ × (Fin n → Bool) :=
    fun x => ((x 0).1, fun i => (x (Int.ofNat (i.1 + 1))).2)
  letI : IsProbabilityMeasure G := by
    dsimp [G]
    exact isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure π := by
    dsimp [π]
    infer_instance
  letI : IsProbabilityMeasure I := by
    dsimp [I]
    infer_instance
  have hstat : HasLaw (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => stat z.2)
      (π.prod I) P := by
    simpa [stat, π, p, hp, I, P] using
      (geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_state_futureMarkPrefix_hasLaw
        hrate rho hrho hrho_pos n)
  have hstat_meas : Measurable stat := by
    apply (measurable_fst.comp (measurable_pi_apply 0)).prodMk
    apply measurable_pi_lambda
    intro i
    exact measurable_snd.comp (measurable_pi_apply (Int.ofNat (i.1 + 1)))
  have hpair :=
    geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_futureGapPath_pathStatistic_hasLaw_of_hasLaw
      hrate rho hrho hrho_pos stat hstat_meas
      (π.prod I) hstat
  have hcount : HasLaw (canonicalRenewalCount t) C G := by
    simpa [G, C] using canonicalRenewalCount_hasLaw_poisson hrate ht
  let F : (ℕ → ℝ) × (ℕ × (Fin n → Bool)) → ℕ × (ℕ × (Fin n → Bool)) :=
    fun x => (x.2.1, (canonicalRenewalCount t x.1, x.2.2))
  have hF : Measurable F := by
    exact (measurable_fst.comp measurable_snd).prodMk
      (((measurable_canonicalRenewalCount t).comp measurable_fst).prodMk
        (measurable_snd.comp measurable_snd))
  have htransform : HasLaw F (π.prod (C.prod I)) (G.prod (π.prod I)) := by
    refine ⟨hF.aemeasurable, ?_⟩
    change Measure.map F (G.prod (π.prod I)) = π.prod (C.prod I)
    have hprod :
        Measure.map (Prod.map (canonicalRenewalCount t) id) (G.prod (π.prod I)) =
          C.prod (π.prod I) := by
      calc
        Measure.map (Prod.map (canonicalRenewalCount t) id) (G.prod (π.prod I)) =
            (G.map (canonicalRenewalCount t)).prod ((π.prod I).map id) := by
              exact (Measure.map_prod_map G (π.prod I)
                (measurable_canonicalRenewalCount t) measurable_id).symm
        _ = C.prod (π.prod I) := by rw [hcount.map_eq, Measure.map_id]
    let a : ℕ × (ℕ × (Fin n → Bool)) → (ℕ × ℕ) × (Fin n → Bool) :=
      MeasurableEquiv.prodAssoc.symm
    let b : (ℕ × ℕ) × (Fin n → Bool) → (ℕ × ℕ) × (Fin n → Bool) :=
      Prod.map Prod.swap id
    let c : (ℕ × ℕ) × (Fin n → Bool) → ℕ × (ℕ × (Fin n → Bool)) :=
      MeasurableEquiv.prodAssoc
    let reorder : ℕ × (ℕ × (Fin n → Bool)) → ℕ × (ℕ × (Fin n → Bool)) :=
      c ∘ b ∘ a
    have ha_m : Measurable a := MeasurableEquiv.prodAssoc.symm.measurable
    have hb_m : Measurable b := measurable_swap.prodMap measurable_id
    have hc_m : Measurable c := MeasurableEquiv.prodAssoc.measurable
    have ha : Measure.map a (C.prod (π.prod I)) = (C.prod π).prod I := by
      simpa [a] using (measurePreserving_prodAssoc C π I).symm.map_eq
    have hb : Measure.map b ((C.prod π).prod I) = (π.prod C).prod I := by
      calc
        Measure.map b ((C.prod π).prod I) =
            (Measure.map Prod.swap (C.prod π)).prod (Measure.map id I) := by
              rw [show b = Prod.map Prod.swap id by rfl,
                Measure.map_prod_map (C.prod π) I measurable_swap measurable_id]
        _ = (π.prod C).prod I := by rw [Measure.prod_swap, Measure.map_id]
    have hc : Measure.map c ((π.prod C).prod I) = π.prod (C.prod I) := by
      simpa [c] using (Measure.prodAssoc_prod (μ := π) (ν := C) (τ := I))
    have horder : Measure.map reorder (C.prod (π.prod I)) = π.prod (C.prod I) := by
      calc
        Measure.map reorder (C.prod (π.prod I)) =
            Measure.map c (Measure.map b (Measure.map a (C.prod (π.prod I)))) := by
              rw [Measure.map_map hc_m hb_m,
                Measure.map_map (hc_m.comp hb_m) ha_m]
              congr 1
        _ = Measure.map c (Measure.map b ((C.prod π).prod I)) := by rw [ha]
        _ = Measure.map c ((π.prod C).prod I) := by rw [hb]
        _ = π.prod (C.prod I) := hc
    have hF_eq : F = reorder ∘ Prod.map (canonicalRenewalCount t) id := by
      funext x
      rfl
    calc
      Measure.map F (G.prod (π.prod I)) =
          Measure.map reorder
            (Measure.map (Prod.map (canonicalRenewalCount t) id) (G.prod (π.prod I))) := by
              rw [hF_eq, Measure.map_map (by
                exact hc_m.comp (hb_m.comp ha_m))
                ((measurable_canonicalRenewalCount t).prodMap measurable_id)]
      _ = Measure.map reorder (C.prod (π.prod I)) := by rw [hprod]
      _ = π.prod (C.prod I) := horder
  have hcomp := htransform.comp hpair
  simpa [G, π, p, hp, I, C, P, stat, F, candidateFutureGapPath,
    suspensionFuturePath, Function.comp_def] using hcomp

/-- The actual selected Palm path's pre-tag queue and path-derived post-tag
potential-service count have the exact finite-horizon product law.  This
proves finite marked-Poisson thinning for the same path, not a synthetic
service process. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_preArrivalQueueLength_postTagFalseMarkCount_hasLaw
    {rate t : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho) (ht : 0 ≤ t) :
    let mean : ℝ≥0 := ⟨rate * t, mul_nonneg hrate.le ht⟩
    let p : ℝ≥0 := uniformizedBirthProbability rho
    HasLaw
      (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) =>
        ((z.2 0).1, postTagFalseMarkCount t z))
      ((geoNNPMF rho hrho).toMeasure.prod
        (ProbabilityTheory.poissonMeasure (mean * (1 - p))))
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag := by
  let π : Measure ℕ := (geoNNPMF rho hrho).toMeasure
  let p : ℝ≥0 := uniformizedBirthProbability rho
  let hp : p ≤ 1 := uniformizedBirthProbability_le_one rho
  let mean : ℝ≥0 := ⟨rate * t, mul_nonneg hrate.le ht⟩
  let P : Measure ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) :=
    ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
      hrate rho hrho).conditionOn
        (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
        (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
          hrate rho hrho hrho_pos)).Ptag
  let state : ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) → ℕ :=
    fun z => (z.2 0).1
  have hstate : Measurable state :=
    measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd)
  have hprefix : ∀ n : ℕ, HasLaw
      (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) =>
        (state z, (canonicalRenewalCount t (suspensionFuturePath z.1),
          fun i : Fin n => (z.2 (Int.ofNat (i.1 + 1))).2)))
      (π.prod ((ProbabilityTheory.poissonMeasure mean).prod
        (FiniteHorizonMarkedPoisson.iidMarks p hp n).toMeasure)) P := by
    intro n
    simpa [π, p, hp, mean, P, state] using
      (geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_state_allEventCount_futureMarkPrefix_hasLaw
        hrate rho hrho hrho_pos ht n)
  have hsample := postTagFalseMarkHorizonSample_state_hasLaw_of_count_prefix_hasLaw
    (P := P) t state hstate π mean p hp hprefix
  have hcount := postTagFalseMarkCount_state_hasLaw_of_horizonSample_state_hasLaw
    (P := P) t state π mean p hp hsample
  simpa [π, p, hp, mean, P, state] using hcount

/-- At each fixed horizon, the path-derived post-tag potential-service count
is independent of the selected tag's pre-arrival queue length. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_preArrivalQueueLength_indep_postTagFalseMarkCount
    {rate t : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho) (ht : 0 ≤ t) :
    (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => (z.2 0).1) ⟂ᵢ[
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag]
      (postTagFalseMarkCount t) := by
  let π : Measure ℕ := (geoNNPMF rho hrho).toMeasure
  let mean : ℝ≥0 := ⟨rate * t, mul_nonneg hrate.le ht⟩
  let p : ℝ≥0 := uniformizedBirthProbability rho
  let C : Measure ℕ := ProbabilityTheory.poissonMeasure (mean * (1 - p))
  let tagged := geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
    hrate rho hrho
  let selected := tagged.conditionOn
    (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
    (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
      hrate rho hrho hrho_pos)
  let P : Measure ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) := selected.Ptag
  let q : ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) → ℕ := fun z => (z.2 0).1
  let c : ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) → ℕ := postTagFalseMarkCount t
  letI : IsProbabilityMeasure P := by
    exact selected.isProbability
  letI : IsProbabilityMeasure π := by
    dsimp [π]
    infer_instance
  change q ⟂ᵢ[P] c
  have hjoint :=
    geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_preArrivalQueueLength_postTagFalseMarkCount_hasLaw
      hrate rho hrho hrho_pos ht
  have hq := geoNNPMF_uniformized_forwardReverseMarked_selected_tag_zero_state_hasLaw
    hrate rho hrho hrho_pos
  have hsnd : HasLaw Prod.snd C (π.prod C) := by
    refine ⟨measurable_snd.aemeasurable, ?_⟩
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hc := hsnd.comp hjoint
  have hc' : HasLaw c C P := by
    simpa [c, P, C, Function.comp_def] using hc
  apply (indepFun_iff_map_prod_eq_prod_map_map
    ((measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd)).aemeasurable)
    ((measurable_postTagFalseMarkCount t).aemeasurable)).2
  change Measure.map (fun z => (q z, c z)) P = (P.map q).prod (P.map c)
  change Measure.map (fun z => ((z.2 0).1, postTagFalseMarkCount t z)) P = _
  rw [hjoint.map_eq, hq.map_eq, hc'.map_eq]

/-- At physical M/M/1 rates, the all-event-clock mean times the potential-
service (`false`-mark) probability is the potential-service mean. -/
theorem uniformizedPhysicalFalseMarkMean_eq_serviceMean
    {arrivalRate serviceRate : ℝ≥0} (hservice_pos : 0 < serviceRate)
    {t : ℝ} (ht : 0 ≤ t) :
    let total : ℝ≥0 := arrivalRate + serviceRate
    let mean : ℝ≥0 := ⟨(total : ℝ) * t, mul_nonneg (by positivity) ht⟩
    let p : ℝ≥0 := uniformizedBirthProbability
      (mm1TrafficIntensityNN arrivalRate serviceRate)
    let serviceMean : ℝ≥0 :=
      ⟨(serviceRate : ℝ) * t, mul_nonneg (by positivity) ht⟩
    mean * (1 - p) = serviceMean := by
  dsimp
  apply NNReal.eq
  change
    (((arrivalRate + serviceRate : ℝ≥0) : ℝ) * t) *
      ((1 - uniformizedBirthProbability
        (mm1TrafficIntensityNN arrivalRate serviceRate) : ℝ≥0) : ℝ) =
      (serviceRate : ℝ) * t
  have hmass := congrArg (fun x : ℝ≥0 => (x : ℝ))
    (total_uniformized_rate_mul_potentialServiceProbability
      (arrivalRate := arrivalRate) (serviceRate := serviceRate) hservice_pos)
  change
    (((arrivalRate + serviceRate) *
      (1 - uniformizedBirthProbability
        (mm1TrafficIntensityNN arrivalRate serviceRate)) : ℝ≥0) : ℝ) =
      (serviceRate : ℝ) at hmass
  calc
    (((arrivalRate + serviceRate : ℝ≥0) : ℝ) * t) *
        ((1 - uniformizedBirthProbability
          (mm1TrafficIntensityNN arrivalRate serviceRate) : ℝ≥0) : ℝ) =
        ((((arrivalRate + serviceRate : ℝ≥0) *
          (1 - uniformizedBirthProbability
            (mm1TrafficIntensityNN arrivalRate serviceRate)) : ℝ≥0) : ℝ)) * t := by
              rw [NNReal.coe_mul]
              ring
    _ = (serviceRate : ℝ) * t := by rw [hmass]

/-- At physical stable M/M/1 rates, the actual selected Palm path's
pre-arrival queue and its path-derived post-tag potential-service count have
the product of the stationary geometric and Poisson service-count laws. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_preArrivalQueueLength_postTagFalseMarkCount_hasLaw_of_rates
    {arrivalRate serviceRate : ℝ≥0}
    (harrival_pos : 0 < arrivalRate) (hstable : arrivalRate < serviceRate)
    {t : ℝ} (ht : 0 ≤ t) :
    let rate : ℝ := ((arrivalRate + serviceRate : ℝ≥0) : ℝ)
    let hrate : 0 < rate := by
      exact_mod_cast (add_pos_of_pos_of_nonneg harrival_pos (zero_le serviceRate))
    let rho : ℝ≥0 := mm1TrafficIntensityNN arrivalRate serviceRate
    let hrho : rho < 1 := mm1TrafficIntensityNN_lt_one hstable
    let hrho_pos : 0 < rho := mm1TrafficIntensityNN_pos harrival_pos
      (lt_trans harrival_pos hstable)
    HasLaw
      (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) =>
        ((z.2 0).1, postTagFalseMarkCount t z))
      ((geoNNPMF rho hrho).toMeasure.prod
        (ProbabilityTheory.poissonMeasure
          (⟨(serviceRate : ℝ) * t,
            mul_nonneg (by positivity) ht⟩ : ℝ≥0)))
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag := by
  dsimp only
  have hservice_pos : 0 < serviceRate := lt_trans harrival_pos hstable
  let mean : ℝ≥0 :=
    ⟨((arrivalRate + serviceRate : ℝ≥0) : ℝ) * t,
      mul_nonneg (by positivity) ht⟩
  let p : ℝ≥0 := uniformizedBirthProbability
    (mm1TrafficIntensityNN arrivalRate serviceRate)
  let serviceMean : ℝ≥0 :=
    ⟨(serviceRate : ℝ) * t, mul_nonneg (by positivity) ht⟩
  have hmean : mean * (1 - p) = serviceMean := by
    simpa [mean, p, serviceMean] using
      (uniformizedPhysicalFalseMarkMean_eq_serviceMean
        (arrivalRate := arrivalRate) (serviceRate := serviceRate) hservice_pos ht)
  have hgeneric :=
    geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_preArrivalQueueLength_postTagFalseMarkCount_hasLaw
      (rate := ((arrivalRate + serviceRate : ℝ≥0) : ℝ))
      (t := t)
      (by exact_mod_cast
        (add_pos_of_pos_of_nonneg harrival_pos (zero_le serviceRate)))
      (mm1TrafficIntensityNN arrivalRate serviceRate)
      (mm1TrafficIntensityNN_lt_one hstable)
      (mm1TrafficIntensityNN_pos harrival_pos (lt_trans harrival_pos hstable)) ht
  change HasLaw
    (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) =>
      ((z.2 0).1, postTagFalseMarkCount t z))
    ((geoNNPMF (mm1TrafficIntensityNN arrivalRate serviceRate)
      (mm1TrafficIntensityNN_lt_one hstable)).toMeasure.prod
      (ProbabilityTheory.poissonMeasure (mean * (1 - p)))) _ at hgeneric
  rw [hmean] at hgeneric
  simpa [serviceMean] using hgeneric

/-- At physical stable M/M/1 rates, the actual selected Palm path's
path-derived post-tag potential-service count has the Poisson service-count
law at every fixed nonnegative horizon. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_postTagFalseMarkCount_hasLaw_poisson_of_rates
    {arrivalRate serviceRate : ℝ≥0}
    (harrival_pos : 0 < arrivalRate) (hstable : arrivalRate < serviceRate)
    {t : ℝ} (ht : 0 ≤ t) :
    let rate : ℝ := ((arrivalRate + serviceRate : ℝ≥0) : ℝ)
    let hrate : 0 < rate := by
      exact_mod_cast (add_pos_of_pos_of_nonneg harrival_pos (zero_le serviceRate))
    let rho : ℝ≥0 := mm1TrafficIntensityNN arrivalRate serviceRate
    let hrho : rho < 1 := mm1TrafficIntensityNN_lt_one hstable
    let hrho_pos : 0 < rho := mm1TrafficIntensityNN_pos harrival_pos
      (lt_trans harrival_pos hstable)
    HasLaw (postTagFalseMarkCount t)
      (ProbabilityTheory.poissonMeasure
        (⟨(serviceRate : ℝ) * t, mul_nonneg (by positivity) ht⟩ : ℝ≥0))
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag := by
  dsimp only
  let π : Measure ℕ := (geoNNPMF
    (mm1TrafficIntensityNN arrivalRate serviceRate)
    (mm1TrafficIntensityNN_lt_one hstable)).toMeasure
  let C : Measure ℕ := ProbabilityTheory.poissonMeasure
    (⟨(serviceRate : ℝ) * t, mul_nonneg (by positivity) ht⟩ : ℝ≥0)
  letI : IsProbabilityMeasure π := by
    dsimp [π]
    infer_instance
  have hjoint :=
    geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_preArrivalQueueLength_postTagFalseMarkCount_hasLaw_of_rates
      harrival_pos hstable ht
  have hsnd : HasLaw Prod.snd C (π.prod C) := by
    refine ⟨measurable_snd.aemeasurable, ?_⟩
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hcomp := hsnd.comp hjoint
  simpa [π, C] using hcomp

/-- Physical-rate specialization of the selected-tag queue/service-count
independence theorem. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_preArrivalQueueLength_indep_postTagFalseMarkCount_of_rates
    {arrivalRate serviceRate : ℝ≥0}
    (harrival_pos : 0 < arrivalRate) (hstable : arrivalRate < serviceRate)
    {t : ℝ} (ht : 0 ≤ t) :
    let rate : ℝ := ((arrivalRate + serviceRate : ℝ≥0) : ℝ)
    let hrate : 0 < rate := by
      exact_mod_cast (add_pos_of_pos_of_nonneg harrival_pos (zero_le serviceRate))
    let rho : ℝ≥0 := mm1TrafficIntensityNN arrivalRate serviceRate
    let hrho : rho < 1 := mm1TrafficIntensityNN_lt_one hstable
    let hrho_pos : 0 < rho := mm1TrafficIntensityNN_pos harrival_pos
      (lt_trans harrival_pos hstable)
    (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => (z.2 0).1) ⟂ᵢ[
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag]
      (postTagFalseMarkCount t) := by
  dsimp only
  exact
    geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_preArrivalQueueLength_indep_postTagFalseMarkCount
      (by exact_mod_cast
        (add_pos_of_pos_of_nonneg harrival_pos (zero_le serviceRate)))
      (mm1TrafficIntensityNN arrivalRate serviceRate)
      (mm1TrafficIntensityNN_lt_one hstable)
      (mm1TrafficIntensityNN_pos harrival_pos (lt_trans harrival_pos hstable)) ht

/-- The path-derived post-tag false-mark count supplies exactly the fixed-
horizon potential-service marginals consumed by the stationary M/M/1 tail
calculation, at the physical service rate. -/
noncomputable def geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_postTagFalseMarkCountMarginals_of_rates
    {arrivalRate serviceRate : ℝ≥0}
    (harrival_pos : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    let rate : ℝ := ((arrivalRate + serviceRate : ℝ≥0) : ℝ)
    let hrate : 0 < rate := by
      exact_mod_cast (add_pos_of_pos_of_nonneg harrival_pos (zero_le serviceRate))
    let rho : ℝ≥0 := mm1TrafficIntensityNN arrivalRate serviceRate
    let hrho : rho < 1 := mm1TrafficIntensityNN_lt_one hstable
    let hrho_pos : 0 < rho := mm1TrafficIntensityNN_pos harrival_pos
      (lt_trans harrival_pos hstable)
    PostTagPoissonCompletionCountMarginals
      ((ℤ → ℝ) × (ℤ → (ℕ × Bool)))
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag := by
  dsimp only
  refine
    { rate := (serviceRate : ℝ)
      rate_pos := by exact_mod_cast (lt_trans harrival_pos hstable)
      completionCount := postTagFalseMarkCount
      completionCount_measurable := measurable_postTagFalseMarkCount
      completionCount_poisson_law := ?_ }
  intro z hz k
  calc
    _ = PoissonProcess.countLikelihood (serviceRate : ℝ) z k :=
      PoissonProcess.hasLaw_poissonMeasure_real_singleton_eq_countLikelihood
        (mul_nonneg (by exact_mod_cast (zero_le serviceRate)) hz)
        (geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_postTagFalseMarkCount_hasLaw_poisson_of_rates
          harrival_pos hstable hz) k
    _ = PoissonProcess.countLikelihood 1 ((serviceRate : ℝ) * z) k := by
      simp [PoissonProcess.countLikelihood]

/-- The actual selected Palm carrier has a nonexplosive post-tag all-event
clock.  This is lifted from its verified full iid exponential future-gap law,
without replacing the path by a synthetic clock. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_ae_futureGap_tendsto_atTop
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho) :
    ∀ᵐ z ∂((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
      hrate rho hrho).conditionOn
        (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
        (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
          hrate rho hrho hrho_pos)).Ptag,
      Tendsto (fun n : ℕ =>
        arrivalTime n (suspensionFuturePath z.1)) atTop atTop := by
  have hfuture :=
    geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_futureGapPath_hasLaw
      hrate rho hrho hrho_pos
  have hmap : ∀ᵐ g ∂Measure.map
      (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => candidateFutureGapPath z.1)
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag,
      Tendsto (fun n : ℕ => arrivalTime n g) atTop atTop := by
    rw [hfuture.map_eq]
    exact ae_arrivalTime_tendsto_atTop hrate
  simpa [candidateFutureGapPath, suspensionFuturePath] using
    (Measure.tendsto_ae_map hfuture.aemeasurable hmap)

/-- The actual selected Palm carrier's post-tag all-event epochs are almost
surely monotone. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_ae_futureGap_monotone
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho) :
    ∀ᵐ z ∂((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
      hrate rho hrho).conditionOn
        (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
        (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
          hrate rho hrho hrho_pos)).Ptag,
      Monotone (fun n : ℕ =>
        arrivalTime n (suspensionFuturePath z.1)) := by
  have hfuture :=
    geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_futureGapPath_hasLaw
      hrate rho hrho hrho_pos
  have hmap : ∀ᵐ g ∂Measure.map
      (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => candidateFutureGapPath z.1)
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag,
      Monotone (fun n : ℕ => arrivalTime n g) := by
    rw [hfuture.map_eq]
    exact ae_arrivalTime_monotone hrate
  simpa [candidateFutureGapPath, suspensionFuturePath] using
    (Measure.tendsto_ae_map hfuture.aemeasurable hmap)

/-- The actual selected Palm carrier's post-tag all-event epochs are almost
surely strictly increasing. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_ae_futureGap_strictMono
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho) :
    ∀ᵐ z ∂((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
      hrate rho hrho).conditionOn
        (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
        (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
          hrate rho hrho hrho_pos)).Ptag,
      StrictMono (fun n : ℕ =>
        arrivalTime n (suspensionFuturePath z.1)) := by
  have hfuture :=
    geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_futureGapPath_hasLaw
      hrate rho hrho hrho_pos
  have hmap : ∀ᵐ g ∂Measure.map
      (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => candidateFutureGapPath z.1)
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag,
      StrictMono (fun n : ℕ => arrivalTime n g) := by
    rw [hfuture.map_eq]
    exact ae_arrivalTime_strictMono hrate
  simpa [candidateFutureGapPath, suspensionFuturePath] using
    (Measure.tendsto_ae_map hfuture.aemeasurable hmap)

/-- The actual selected Palm carrier's post-tag all-event epochs are almost
surely nonnegative. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_ae_futureGap_arrivalTime_nonnegative
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho) :
    ∀ᵐ z ∂((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
      hrate rho hrho).conditionOn
        (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
        (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
          hrate rho hrho hrho_pos)).Ptag,
      ∀ n : ℕ, 0 ≤ arrivalTime n (suspensionFuturePath z.1) := by
  have hfuture :=
    geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_futureGapPath_hasLaw
      hrate rho hrho hrho_pos
  have hmap : ∀ᵐ g ∂Measure.map
      (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => candidateFutureGapPath z.1)
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag,
      ∀ n : ℕ, 0 ≤ arrivalTime n g := by
    rw [hfuture.map_eq]
    exact ae_all_arrivalTime_nonnegative hrate
  simpa [candidateFutureGapPath, suspensionFuturePath] using
    (Measure.tendsto_ae_map hfuture.aemeasurable hmap)

/-- The actual selected Palm carrier's post-tag all-event epochs are almost
surely positive. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_ae_futureGap_arrivalTime_positive
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho) :
    ∀ᵐ z ∂((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
      hrate rho hrho).conditionOn
        (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
        (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
          hrate rho hrho hrho_pos)).Ptag,
      ∀ n : ℕ, 0 < arrivalTime n (suspensionFuturePath z.1) := by
  have hfuture :=
    geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_futureGapPath_hasLaw
      hrate rho hrho hrho_pos
  have hmap : ∀ᵐ g ∂Measure.map
      (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => candidateFutureGapPath z.1)
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag,
      ∀ n : ℕ, 0 < arrivalTime n g := by
    rw [hfuture.map_eq]
    exact ae_all_arrivalTime_positive hrate
  simpa [candidateFutureGapPath, suspensionFuturePath] using
    (Measure.tendsto_ae_map hfuture.aemeasurable hmap)

/-- In the stable physical M/M/1 marked-Palm construction, almost every
literal post-tag mark path eventually contains enough `false` marks to clear
the finite pre-arrival queue.  The proof uses the already-derived exact
geometric--Poisson count tail at each deterministic horizon and its
exponential decay; it does not posit an infinite synthetic mark stream. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_ae_falseMarkPrefix_reaches_preArrivalQueue_of_rates
    {arrivalRate serviceRate : ℝ≥0}
    (harrival_pos : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    let rate : ℝ := ((arrivalRate + serviceRate : ℝ≥0) : ℝ)
    let hrate : 0 < rate := by
      exact_mod_cast (add_pos_of_pos_of_nonneg harrival_pos (zero_le serviceRate))
    let rho : ℝ≥0 := mm1TrafficIntensityNN arrivalRate serviceRate
    let hrho : rho < 1 := mm1TrafficIntensityNN_lt_one hstable
    let hrho_pos : 0 < rho := mm1TrafficIntensityNN_pos harrival_pos
      (lt_trans harrival_pos hstable)
    ∀ᵐ z ∂((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
      hrate rho hrho).conditionOn
        (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
        (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
          hrate rho hrho hrho_pos)).Ptag,
      ∃ n : ℕ, (z.2 0).1 < postTagFalseMarkPrefixCount (n + 1) z.2 := by
  dsimp only
  let rate : ℝ := ((arrivalRate + serviceRate : ℝ≥0) : ℝ)
  let hrate : 0 < rate := by
    exact_mod_cast (add_pos_of_pos_of_nonneg harrival_pos (zero_le serviceRate))
  let rho : ℝ≥0 := mm1TrafficIntensityNN arrivalRate serviceRate
  let hrho : rho < 1 := mm1TrafficIntensityNN_lt_one hstable
  let hrho_pos : 0 < rho := mm1TrafficIntensityNN_pos harrival_pos
    (lt_trans harrival_pos hstable)
  let selected := (geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
    hrate rho hrho).conditionOn
      (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
      (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
        hrate rho hrho hrho_pos)
  let P : Measure ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) := selected.Ptag
  letI : IsProbabilityMeasure P := by
    exact selected.isProbability
  have hservice_pos : 0 < serviceRate := lt_trans harrival_pos hstable
  have hservice_ne : (serviceRate : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast hservice_pos)
  have ha : 0 < (serviceRate : ℝ) - (arrivalRate : ℝ) := by
    exact sub_pos.mpr (by exact_mod_cast hstable)
  have hqueue_meas : Measurable
      (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => (z.2 0).1) :=
    measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd)
  have hqueue_tail : ∀ k : ℕ,
      P.real {z | k ≤ (z.2 0).1} =
        ((arrivalRate : ℝ) / (serviceRate : ℝ)) ^ k := by
    intro k
    let H := geoNNPMF_uniformized_forwardReverseMarked_stationaryPalmPASTACertificate
      hrate rho hrho hrho_pos
    calc
      P.real {z | k ≤ (z.2 0).1} =
          (geoNNPMF_uniformized_forwardReverseMarkedSuspensionShiftInvariantLaw_of_unmarkedIntPathShift
            hrate rho hrho
            (fun j => geoNNPMF_uniformized_forwardReverseTraj_intPathShift_measurePreserving
              rho hrho j)).Pbase.real
            {z | k ≤ H.to_pasta.stationaryQueueLength z} := by
              simpa [P, selected, H] using
                (H.to_pasta.real_preArrivalQueueLength_tail_eq_stationary k)
      _ = ((arrivalRate : ℝ) / (serviceRate : ℝ)) ^ k := by
        simpa [rate, rho, hrho, hrho_pos, H] using
          (geoNNPMF_uniformized_forwardReverseMarked_stationaryPalmPASTA_embeddedQueueLength_tail_of_rates
            harrival_pos hstable k)
  have htail : ∀ t : ℝ, 0 ≤ t →
      P.real {z | postTagFalseMarkCount t z ≤ (z.2 0).1} =
        Real.exp (-(((serviceRate : ℝ) - (arrivalRate : ℝ)) * t)) := by
    intro t ht
    have hind : (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => (z.2 0).1) ⟂ᵢ[P]
        postTagFalseMarkCount t := by
      simpa [P, selected, rate, rho, hrho, hrho_pos] using
        (geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_preArrivalQueueLength_indep_postTagFalseMarkCount_of_rates
          harrival_pos hstable ht)
    have hcount_law :=
      geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_postTagFalseMarkCount_hasLaw_poisson_of_rates
        harrival_pos hstable ht
    have hcount : ∀ k : ℕ,
        P.real {z | postTagFalseMarkCount t z = k} =
          PoissonProcess.countLikelihood 1 ((serviceRate : ℝ) * t) k := by
      intro k
      simpa [P, selected, rate, rho, hrho, hrho_pos,
        PoissonProcess.countLikelihood] using
        (PoissonProcess.hasLaw_poissonMeasure_real_singleton_eq_countLikelihood
          (mul_nonneg (by exact_mod_cast (zero_le serviceRate)) ht)
          hcount_law k)
    calc
      P.real {z | postTagFalseMarkCount t z ≤ (z.2 0).1} =
          PoissonProcess.noArrivalProb
            (1 - (arrivalRate : ℝ) / (serviceRate : ℝ))
            ((serviceRate : ℝ) * t) :=
        measureReal_geometric_poisson_mixture P
          (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => (z.2 0).1)
          (postTagFalseMarkCount t) hqueue_meas
          (measurable_postTagFalseMarkCount t) hind
          ((arrivalRate : ℝ) / (serviceRate : ℝ)) ((serviceRate : ℝ) * t)
          hqueue_tail hcount
      _ = Real.exp (-(((serviceRate : ℝ) - (arrivalRate : ℝ)) * t)) := by
        simpa only [neg_mul] using
          (hasSum_poissonCountLikelihood_mul_pow
            ((serviceRate : ℝ) * t) ((arrivalRate : ℝ) / (serviceRate : ℝ)) |>.tsum_eq).symm.trans
          (hasSum_stationaryMM1_mixture (arrivalRate : ℝ) (serviceRate : ℝ) t
            hservice_ne |>.tsum_eq)
  simpa [P, selected] using
    (ae_exists_postTagFalseMarkPrefix_gt_of_exponential_count_tail
      (P := P) (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => (z.2 0).1)
      ((serviceRate : ℝ) - (arrivalRate : ℝ)) ha htail)

/-- The physical selected Palm path's false-mark busy-until time is
nonnegative almost surely. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_ae_postTagFalseMarkBusyUntil_nonneg_of_rates
    {arrivalRate serviceRate : ℝ≥0}
    (harrival_pos : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    let rate : ℝ := ((arrivalRate + serviceRate : ℝ≥0) : ℝ)
    let hrate : 0 < rate := by
      exact_mod_cast (add_pos_of_pos_of_nonneg harrival_pos (zero_le serviceRate))
    let rho : ℝ≥0 := mm1TrafficIntensityNN arrivalRate serviceRate
    let hrho : rho < 1 := mm1TrafficIntensityNN_lt_one hstable
    let hrho_pos : 0 < rho := mm1TrafficIntensityNN_pos harrival_pos
      (lt_trans harrival_pos hstable)
    ∀ᵐ z ∂((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
      hrate rho hrho).conditionOn
        (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
      (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
          hrate rho hrho hrho_pos)).Ptag,
      0 ≤ postTagFalseMarkBusyUntil (z.2 0).1 z := by
  dsimp only
  have hrate : 0 < ((arrivalRate + serviceRate : ℝ≥0) : ℝ) := by
    exact_mod_cast (add_pos_of_pos_of_nonneg harrival_pos (zero_le serviceRate))
  have hrho : mm1TrafficIntensityNN arrivalRate serviceRate < 1 :=
    mm1TrafficIntensityNN_lt_one hstable
  have hrho_pos : 0 < mm1TrafficIntensityNN arrivalRate serviceRate :=
    mm1TrafficIntensityNN_pos harrival_pos (lt_trans harrival_pos hstable)
  have hfuture_nonneg :=
    geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_ae_futureGap_arrivalTime_nonnegative
      hrate (mm1TrafficIntensityNN arrivalRate serviceRate) hrho hrho_pos
  filter_upwards [hfuture_nonneg] with z hnonneg
  exact postTagFalseMarkBusyUntil_nonneg_of_arrivalTime_nonneg
    (z.2 0).1 z hnonneg

/-- The physical selected Palm path's false-mark busy-until time precedes the
tagged false-mark response time almost surely. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_ae_postTagFalseMarkBusyUntil_le_response_of_rates
    {arrivalRate serviceRate : ℝ≥0}
    (harrival_pos : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    let rate : ℝ := ((arrivalRate + serviceRate : ℝ≥0) : ℝ)
    let hrate : 0 < rate := by
      exact_mod_cast (add_pos_of_pos_of_nonneg harrival_pos (zero_le serviceRate))
    let rho : ℝ≥0 := mm1TrafficIntensityNN arrivalRate serviceRate
    let hrho : rho < 1 := mm1TrafficIntensityNN_lt_one hstable
    let hrho_pos : 0 < rho := mm1TrafficIntensityNN_pos harrival_pos
      (lt_trans harrival_pos hstable)
    ∀ᵐ z ∂((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
      hrate rho hrho).conditionOn
        (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
      (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
          hrate rho hrho hrho_pos)).Ptag,
      postTagFalseMarkBusyUntil (z.2 0).1 z ≤
        postTagFalseMarkResponseFromState z := by
  dsimp only
  have hrate : 0 < ((arrivalRate + serviceRate : ℝ≥0) : ℝ) := by
    exact_mod_cast (add_pos_of_pos_of_nonneg harrival_pos (zero_le serviceRate))
  have hrho : mm1TrafficIntensityNN arrivalRate serviceRate < 1 :=
    mm1TrafficIntensityNN_lt_one hstable
  have hrho_pos : 0 < mm1TrafficIntensityNN arrivalRate serviceRate :=
    mm1TrafficIntensityNN_pos harrival_pos (lt_trans harrival_pos hstable)
  have hfuture_nonneg :=
    geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_ae_futureGap_arrivalTime_nonnegative
      hrate (mm1TrafficIntensityNN arrivalRate serviceRate) hrho hrho_pos
  have hfuture_mono :=
    geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_ae_futureGap_monotone
      hrate (mm1TrafficIntensityNN arrivalRate serviceRate) hrho hrho_pos
  have hhit :=
    geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_ae_falseMarkPrefix_reaches_preArrivalQueue_of_rates
      harrival_pos hstable
  filter_upwards [hfuture_nonneg, hfuture_mono, hhit] with
    z hnonneg hmono hhit_z
  exact postTagFalseMarkBusyUntil_le_response_of_arrivalTime_order
    (z.2 0).1 z hnonneg hmono hhit_z

/-- The physical selected Palm path's tagged false-mark work is strictly
positive almost surely. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_ae_postTagFalseMarkTaggedServiceWork_zero_pos_of_rates
    {arrivalRate serviceRate : ℝ≥0}
    (harrival_pos : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    let rate : ℝ := ((arrivalRate + serviceRate : ℝ≥0) : ℝ)
    let hrate : 0 < rate := by
      exact_mod_cast (add_pos_of_pos_of_nonneg harrival_pos (zero_le serviceRate))
    let rho : ℝ≥0 := mm1TrafficIntensityNN arrivalRate serviceRate
    let hrho : rho < 1 := mm1TrafficIntensityNN_lt_one hstable
    let hrho_pos : 0 < rho := mm1TrafficIntensityNN_pos harrival_pos
      (lt_trans harrival_pos hstable)
    ∀ᵐ z ∂((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
      hrate rho hrho).conditionOn
        (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
      (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
          hrate rho hrho hrho_pos)).Ptag,
      0 < postTagFalseMarkTaggedServiceWork (serviceRate : ℝ) (z.2 0).1 z 0 := by
  dsimp only
  have hrate : 0 < ((arrivalRate + serviceRate : ℝ≥0) : ℝ) := by
    exact_mod_cast (add_pos_of_pos_of_nonneg harrival_pos (zero_le serviceRate))
  have hrho : mm1TrafficIntensityNN arrivalRate serviceRate < 1 :=
    mm1TrafficIntensityNN_lt_one hstable
  have hrho_pos : 0 < mm1TrafficIntensityNN arrivalRate serviceRate :=
    mm1TrafficIntensityNN_pos harrival_pos (lt_trans harrival_pos hstable)
  have hservice_pos : 0 < (serviceRate : ℝ) := by
    exact_mod_cast (lt_trans harrival_pos hstable)
  have hfuture_pos :=
    geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_ae_futureGap_arrivalTime_positive
      hrate (mm1TrafficIntensityNN arrivalRate serviceRate) hrho hrho_pos
  have hfuture_strict :=
    geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_ae_futureGap_strictMono
      hrate (mm1TrafficIntensityNN arrivalRate serviceRate) hrho hrho_pos
  have hhit :=
    geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_ae_falseMarkPrefix_reaches_preArrivalQueue_of_rates
      harrival_pos hstable
  filter_upwards [hfuture_pos, hfuture_strict, hhit] with
    z hpos hstrict hhit_z
  exact postTagFalseMarkTaggedServiceWork_zero_pos_of_arrivalTime_strict
    hservice_pos (z.2 0).1 z hpos hstrict hhit_z

/-- Once the direct marked-Palm path is known almost surely to contain enough
post-tag false marks to clear its finite pre-arrival queue, the literal
false-mark stopping time supplies the required strict response/count event
identity on that same stationary/Palm carrier. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_ae_strict_falseMarkResponse_event_of_ae_hit
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho)
    (hhit : ∀ᵐ z ∂((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
      hrate rho hrho).conditionOn
        (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
        (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
          hrate rho hrho hrho_pos)).Ptag,
      ∃ n : ℕ, (z.2 0).1 < postTagFalseMarkPrefixCount (n + 1) z.2)
    (t : ℝ) :
    {z | t < postTagFalseMarkResponseFromState z} =ᵐ[
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag]
      {z | postTagFalseMarkCount t z ≤ (z.2 0).1} := by
  exact ae_lt_postTagFalseMarkResponseFromState_iff_postTagFalseMarkCount_le
    (geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_ae_futureGap_tendsto_atTop
      hrate rho hrho hrho_pos)
    (geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_ae_futureGap_monotone
      hrate rho hrho hrho_pos)
    hhit t

/-- The selected stable uniformized M/M/1 path has the exponential strict
tail for its literal post-tag false-mark response time.  The queue state,
potential-service count, and response time are all functions of that same
conditioned marked path. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_strict_falseMarkResponse_tail_of_rates
    {arrivalRate serviceRate : ℝ≥0}
    (harrival_pos : 0 < arrivalRate) (hstable : arrivalRate < serviceRate)
    {t : ℝ} (ht : 0 ≤ t) :
    let rate : ℝ := ((arrivalRate + serviceRate : ℝ≥0) : ℝ)
    let hrate : 0 < rate := by
      exact_mod_cast (add_pos_of_pos_of_nonneg harrival_pos (zero_le serviceRate))
    let rho : ℝ≥0 := mm1TrafficIntensityNN arrivalRate serviceRate
    let hrho : rho < 1 := mm1TrafficIntensityNN_lt_one hstable
    let hrho_pos : 0 < rho := mm1TrafficIntensityNN_pos harrival_pos
      (lt_trans harrival_pos hstable)
    Measure.real (((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
      hrate rho hrho).conditionOn
        (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
        (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
          hrate rho hrho hrho_pos)).Ptag)
      {z | t < postTagFalseMarkResponseFromState z} =
      Real.exp (-(((serviceRate : ℝ) - (arrivalRate : ℝ)) * t)) := by
  dsimp only
  let rate : ℝ := ((arrivalRate + serviceRate : ℝ≥0) : ℝ)
  let hrate : 0 < rate := by
    exact_mod_cast (add_pos_of_pos_of_nonneg harrival_pos (zero_le serviceRate))
  let rho : ℝ≥0 := mm1TrafficIntensityNN arrivalRate serviceRate
  let hrho : rho < 1 := mm1TrafficIntensityNN_lt_one hstable
  let hrho_pos : 0 < rho := mm1TrafficIntensityNN_pos harrival_pos
    (lt_trans harrival_pos hstable)
  let selected := (geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
    hrate rho hrho).conditionOn
      (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
      (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
        hrate rho hrho hrho_pos)
  let P : Measure ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) := selected.Ptag
  letI : IsProbabilityMeasure P := selected.isProbability
  have hservice_pos : 0 < serviceRate := lt_trans harrival_pos hstable
  have hservice_ne : (serviceRate : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast hservice_pos)
  have hqueue_meas : Measurable
      (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => (z.2 0).1) :=
    measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd)
  have hqueue_tail : ∀ k : ℕ,
      P.real {z | k ≤ (z.2 0).1} =
        ((arrivalRate : ℝ) / (serviceRate : ℝ)) ^ k := by
    intro k
    let H := geoNNPMF_uniformized_forwardReverseMarked_stationaryPalmPASTACertificate
      hrate rho hrho hrho_pos
    calc
      P.real {z | k ≤ (z.2 0).1} =
          (geoNNPMF_uniformized_forwardReverseMarkedSuspensionShiftInvariantLaw_of_unmarkedIntPathShift
            hrate rho hrho
            (fun j => geoNNPMF_uniformized_forwardReverseTraj_intPathShift_measurePreserving
              rho hrho j)).Pbase.real
            {z | k ≤ H.to_pasta.stationaryQueueLength z} := by
              simpa [P, selected, H] using
                (H.to_pasta.real_preArrivalQueueLength_tail_eq_stationary k)
      _ = ((arrivalRate : ℝ) / (serviceRate : ℝ)) ^ k := by
        simpa [rate, rho, hrho, hrho_pos, H] using
          (geoNNPMF_uniformized_forwardReverseMarked_stationaryPalmPASTA_embeddedQueueLength_tail_of_rates
            harrival_pos hstable k)
  have hind : (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => (z.2 0).1) ⟂ᵢ[P]
      postTagFalseMarkCount t := by
    simpa [P, selected, rate, rho, hrho, hrho_pos] using
      (geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_preArrivalQueueLength_indep_postTagFalseMarkCount_of_rates
        harrival_pos hstable ht)
  have hcount : ∀ k : ℕ,
      P.real {z | postTagFalseMarkCount t z = k} =
        PoissonProcess.countLikelihood 1 ((serviceRate : ℝ) * t) k := by
    intro k
    have hcount_law :=
      geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_postTagFalseMarkCount_hasLaw_poisson_of_rates
        harrival_pos hstable ht
    simpa [P, selected, rate, rho, hrho, hrho_pos,
      PoissonProcess.countLikelihood] using
      (PoissonProcess.hasLaw_poissonMeasure_real_singleton_eq_countLikelihood
        (mul_nonneg (by exact_mod_cast (zero_le serviceRate)) ht)
        hcount_law k)
  have hhit :=
    geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_ae_falseMarkPrefix_reaches_preArrivalQueue_of_rates
      harrival_pos hstable
  have hresponse : {z | t < postTagFalseMarkResponseFromState z} =ᵐ[P]
      {z | postTagFalseMarkCount t z ≤ (z.2 0).1} := by
    simpa [P, selected, rate, rho, hrho, hrho_pos] using
      (geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_ae_strict_falseMarkResponse_event_of_ae_hit
        hrate rho hrho hrho_pos hhit t)
  simpa [P, selected] using
    (responseTail_strict_eq_of_stationaryPalmCountCoupling P
      (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => (z.2 0).1)
      (postTagFalseMarkCount t) postTagFalseMarkResponseFromState
      hqueue_meas (measurable_postTagFalseMarkCount t) hind
      (arrivalRate : ℝ) (serviceRate : ℝ) t hservice_ne hqueue_tail hcount hresponse)

end

end AppliedModelingLib.Probability.Queueing
