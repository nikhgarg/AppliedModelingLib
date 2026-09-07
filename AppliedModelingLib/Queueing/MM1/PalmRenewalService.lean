import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalRenewalCountMarginal
import AppliedModelingLib.Queueing.MM1.AnalyticTail
import AppliedModelingLib.Queueing.RenewalFCFS

/-!
# Independent canonical-renewal service on a tagged arrival law

This module makes a concrete product-space construction useful to the
count-level M/M/1 proof.  It independently adjoins the canonical iid
exponential renewal path to an already tagged arrival law, proves the
fixed-horizon Poisson completion-count law, and proves state/count
independence.  It deliberately does not identify this product law with a
stationary Palm construction or assert independent increments.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Lift a tagged arrival law by an independent right-hand probability factor. -/
noncomputable def TaggedArrivalAtZero.prodRight
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (tagged : TaggedArrivalAtZero Ω) (Pextra : Measure Ξ)
    (hPextra : IsProbabilityMeasure Pextra) :
    TaggedArrivalAtZero (Ω × Ξ) where
  Ptag := tagged.Ptag.prod Pextra
  isProbability := by
    letI : IsProbabilityMeasure Pextra := hPextra
    letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
    infer_instance
  arrivals := fun x => tagged.arrivals x.1
  tag_at_zero := by
    letI : IsProbabilityMeasure Pextra := hPextra
    letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
    refine ae_of_ae_map (μ := tagged.Ptag.prod Pextra) (f := Prod.fst)
      (p := fun ω : Ω => tagged.arrivals ω 0 = 0) measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact tagged.tag_at_zero
  arrivals_strict := by
    letI : IsProbabilityMeasure Pextra := hPextra
    letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
    refine ae_of_ae_map (μ := tagged.Ptag.prod Pextra) (f := Prod.fst)
      (p := fun ω : Ω => StrictMono (tagged.arrivals ω)) measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact tagged.arrivals_strict

/-- Adjoin an independent iid-exponential renewal-service path to a tagged arrival law. -/
noncomputable def TaggedArrivalAtZero.withCanonicalRenewalService
    {Ω : Type*} [MeasurableSpace Ω] (tagged : TaggedArrivalAtZero Ω)
    (serviceRate : ℝ) (hserviceRate : 0 < serviceRate) :
    TaggedArrivalAtZero (Ω × (ℕ → ℝ)) :=
  tagged.prodRight (PoissonProcess.exponentialInterarrivalMeasure serviceRate)
    (PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hserviceRate)

/-- On the lifted tagged law, the canonical renewal service count has its actual fixed-time
Poisson law. -/
theorem TaggedArrivalAtZero.prodRight_canonicalRenewalCount_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] (tagged : TaggedArrivalAtZero Ω)
    (serviceRate : ℝ) (hserviceRate : 0 < serviceRate)
    (z : ℝ) (hz : 0 ≤ z) :
    HasLaw (fun x : Ω × (ℕ → ℝ) =>
      PoissonProcess.canonicalRenewalCount z x.2)
      (ProbabilityTheory.poissonMeasure
        (⟨serviceRate * z, mul_nonneg hserviceRate.le hz⟩ : NNReal))
      (tagged.withCanonicalRenewalService serviceRate hserviceRate).Ptag := by
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure (PoissonProcess.exponentialInterarrivalMeasure serviceRate) :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hserviceRate
  refine ⟨((PoissonProcess.measurable_canonicalRenewalCount z).comp measurable_snd).aemeasurable, ?_⟩
  change (tagged.Ptag.prod (PoissonProcess.exponentialInterarrivalMeasure serviceRate)).map
      (fun x : Ω × (ℕ → ℝ) => PoissonProcess.canonicalRenewalCount z x.2) = _
  calc
    (tagged.Ptag.prod (PoissonProcess.exponentialInterarrivalMeasure serviceRate)).map
        (fun x : Ω × (ℕ → ℝ) => PoissonProcess.canonicalRenewalCount z x.2) =
        ((tagged.Ptag.prod (PoissonProcess.exponentialInterarrivalMeasure serviceRate)).map
          Prod.snd).map (PoissonProcess.canonicalRenewalCount z) := by
      symm
      simpa [Function.comp_def] using
        (Measure.map_map
          (μ := tagged.Ptag.prod (PoissonProcess.exponentialInterarrivalMeasure serviceRate))
          (PoissonProcess.measurable_canonicalRenewalCount z) measurable_snd)
    _ = (PoissonProcess.exponentialInterarrivalMeasure serviceRate).map
        (PoissonProcess.canonicalRenewalCount z) := by
      rw [Measure.map_snd_prod, measure_univ, one_smul]
    _ = ProbabilityTheory.poissonMeasure
        (⟨serviceRate * z, mul_nonneg hserviceRate.le hz⟩ : NNReal) :=
      (PoissonProcess.canonicalRenewalCount_hasLaw_poisson hserviceRate hz).map_eq

/-- The old tagged state and the new canonical renewal service count are independent by the
product construction. -/
theorem TaggedArrivalAtZero.prodRight_queue_indep_canonicalRenewalCount
    {Ω : Type*} [MeasurableSpace Ω] (tagged : TaggedArrivalAtZero Ω)
    (queueLength : Ω → ℕ) (hqueueLength : Measurable queueLength)
    (serviceRate : ℝ) (hserviceRate : 0 < serviceRate)
    (z : ℝ) :
    IndepFun (fun x : Ω × (ℕ → ℝ) => queueLength x.1)
      (fun x => PoissonProcess.canonicalRenewalCount z x.2)
      (tagged.withCanonicalRenewalService serviceRate hserviceRate).Ptag := by
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure (PoissonProcess.exponentialInterarrivalMeasure serviceRate) :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hserviceRate
  change IndepFun (fun x : Ω × (ℕ → ℝ) => queueLength x.1)
    (fun x => PoissonProcess.canonicalRenewalCount z x.2)
    (tagged.Ptag.prod (PoissonProcess.exponentialInterarrivalMeasure serviceRate))
  exact indepFun_prod hqueueLength (PoissonProcess.measurable_canonicalRenewalCount z)

/-- On the independent renewal-service extension, the natural time to clear the
pre-arrival queue has the count characterization almost everywhere.  The
exceptional set accounts for boundary paths in the canonical renewal-count
definition; it is null under the exponential product law. -/
theorem TaggedArrivalAtZero.ae_strict_canonicalRenewalResponse_event
    {Ω : Type*} [MeasurableSpace Ω] (tagged : TaggedArrivalAtZero Ω)
    (queueLength : Ω → ℕ) (serviceRate : ℝ) (hserviceRate : 0 < serviceRate)
    (z : ℝ) :
    {x : Ω × (ℕ → ℝ) |
      z < PoissonProcess.arrivalTime (queueLength x.1) x.2} =ᵐ[
        (tagged.withCanonicalRenewalService serviceRate hserviceRate).Ptag]
      {x | PoissonProcess.canonicalRenewalCount z x.2 ≤ queueLength x.1} := by
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure (PoissonProcess.exponentialInterarrivalMeasure serviceRate) :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hserviceRate
  have hthreshold : ∀ᵐ ξ ∂PoissonProcess.exponentialInterarrivalMeasure serviceRate,
      ∀ t : ℝ, ∀ n : ℕ,
        n < PoissonProcess.canonicalRenewalCount t ξ ↔
          PoissonProcess.arrivalTime n ξ ≤ t :=
    PoissonProcess.ae_lt_canonicalRenewalCount_iff_arrivalTime_le hserviceRate
  have hthreshold_prod : ∀ᵐ x ∂
      (tagged.Ptag.prod (PoissonProcess.exponentialInterarrivalMeasure serviceRate)),
      ∀ t : ℝ, ∀ n : ℕ,
        n < PoissonProcess.canonicalRenewalCount t x.2 ↔
          PoissonProcess.arrivalTime n x.2 ≤ t := by
    refine ae_of_ae_map
      (μ := tagged.Ptag.prod (PoissonProcess.exponentialInterarrivalMeasure serviceRate))
      (f := Prod.snd)
      (p := fun ξ : ℕ → ℝ => ∀ t : ℝ, ∀ n : ℕ,
        n < PoissonProcess.canonicalRenewalCount t ξ ↔
          PoissonProcess.arrivalTime n ξ ≤ t)
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact hthreshold
  change {x : Ω × (ℕ → ℝ) |
      z < PoissonProcess.arrivalTime (queueLength x.1) x.2} =ᵐ[
        tagged.Ptag.prod (PoissonProcess.exponentialInterarrivalMeasure serviceRate)]
      {x | PoissonProcess.canonicalRenewalCount z x.2 ≤ queueLength x.1}
  filter_upwards [hthreshold_prod] with x hx
  apply propext
  constructor
  · intro hresponse
    apply Nat.le_of_not_gt
    intro hcount
    exact (not_le_of_gt hresponse) ((hx z (queueLength x.1)).mp hcount)
  · intro hcount
    apply lt_of_not_ge
    intro harrival
    exact (not_lt_of_ge hcount) ((hx z (queueLength x.1)).mpr harrival)

/-- The canonical renewal time at a measurable natural-valued queue index is
measurable on the independent product space. -/
theorem measurable_canonicalRenewalResponse
    {Ω : Type*} [MeasurableSpace Ω]
    (queueLength : Ω → ℕ) (hqueueLength : Measurable queueLength) :
    Measurable (fun x : Ω × (ℕ → ℝ) =>
      PoissonProcess.arrivalTime (queueLength x.1) x.2) := by
  have huncurried : Measurable (fun p : ℕ × (ℕ → ℝ) =>
      PoissonProcess.arrivalTime p.1 p.2) :=
    measurable_from_prod_countable_right (fun n =>
      PoissonProcess.measurable_arrivalTime n)
  exact huncurried.comp
    ((hqueueLength.comp measurable_fst).prodMk measurable_snd)

/-- The renewal time at an arbitrary inherited natural queue index has no
atoms.  Each fixed epoch is atomless, and the random-index event is contained
in their countable union. -/
theorem TaggedArrivalAtZero.canonicalRenewalQueueResponse_atom_zero
    {Ω : Type*} [MeasurableSpace Ω] (tagged : TaggedArrivalAtZero Ω)
    (queueLength : Ω → ℕ) (serviceRate : ℝ) (hserviceRate : 0 < serviceRate)
    (z : ℝ) :
    (tagged.withCanonicalRenewalService serviceRate hserviceRate).Ptag.real
      {x | PoissonProcess.arrivalTime (queueLength x.1) x.2 = z} = 0 := by
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure (PoissonProcess.exponentialInterarrivalMeasure serviceRate) :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hserviceRate
  let μ : Measure (Ω × (ℕ → ℝ)) :=
    tagged.Ptag.prod (PoissonProcess.exponentialInterarrivalMeasure serviceRate)
  let S : ℕ → Set (Ω × (ℕ → ℝ)) := fun n =>
    {x | PoissonProcess.arrivalTime n x.2 = z}
  have hSnull : ∀ n : ℕ, μ (S n) = 0 := by
    intro n
    have hmap : μ.map (PoissonProcess.arrivalTime n ∘ Prod.snd) =
        (PoissonProcess.exponentialInterarrivalMeasure serviceRate).map
          (PoissonProcess.arrivalTime n) := by
      calc
        μ.map (PoissonProcess.arrivalTime n ∘ Prod.snd) =
            (μ.map Prod.snd).map (PoissonProcess.arrivalTime n) := by
          symm
          simpa [μ] using
            (Measure.map_map
              (μ := tagged.Ptag.prod
                (PoissonProcess.exponentialInterarrivalMeasure serviceRate))
              (PoissonProcess.measurable_arrivalTime n) measurable_snd)
        _ = (PoissonProcess.exponentialInterarrivalMeasure serviceRate).map
            (PoissonProcess.arrivalTime n) := by
          change
            ((tagged.Ptag.prod
              (PoissonProcess.exponentialInterarrivalMeasure serviceRate)).map
                Prod.snd).map (PoissonProcess.arrivalTime n) =
              (PoissonProcess.exponentialInterarrivalMeasure serviceRate).map
                (PoissonProcess.arrivalTime n)
          rw [Measure.map_snd_prod, measure_univ, one_smul]
    calc
      μ (S n) = (μ.map (PoissonProcess.arrivalTime n ∘ Prod.snd)) {z} := by
        symm
        simpa [S, Function.comp_def] using
          (Measure.map_apply (μ := μ)
            ((PoissonProcess.measurable_arrivalTime n).comp measurable_snd)
            (measurableSet_singleton z))
      _ = (PoissonProcess.exponentialInterarrivalMeasure serviceRate).map
          (PoissonProcess.arrivalTime n) {z} := by rw [hmap]
      _ = PoissonProcess.exponentialInterarrivalMeasure serviceRate
          {ξ | PoissonProcess.arrivalTime n ξ = z} := by
        rw [Measure.map_apply (PoissonProcess.measurable_arrivalTime n)
          (measurableSet_singleton z)]
        rfl
      _ = 0 :=
        PoissonProcess.arrivalTime_measure_singleton_eq_zero hserviceRate n z
  have hsubset :
      {x : Ω × (ℕ → ℝ) |
        PoissonProcess.arrivalTime (queueLength x.1) x.2 = z} ⊆ ⋃ n, S n := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨queueLength x.1, hx⟩
  have hnull : μ {x : Ω × (ℕ → ℝ) |
      PoissonProcess.arrivalTime (queueLength x.1) x.2 = z} = 0 :=
    measure_mono_null hsubset (measure_iUnion_null hSnull)
  change μ.real {x : Ω × (ℕ → ℝ) |
    PoissonProcess.arrivalTime (queueLength x.1) x.2 = z} = 0
  simp [Measure.real, hnull]

/-- On the independent exponential-service product law, the canonical renewal
response agrees almost everywhere with the isolated tagged FCFS comparator
response. -/
theorem TaggedArrivalAtZero.ae_canonicalRenewalResponse_eq_fcfsTaggedResponse
    {Ω : Type*} [MeasurableSpace Ω]
    (tagged : TaggedArrivalAtZero Ω) (queueLength : Ω → ℕ)
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ x ∂(tagged.withCanonicalRenewalService rate hrate).Ptag,
      responseTime tagOnlyArrival
        (fcfsDepartureFrom (preTagBusyUntil (queueLength x.1) x.2)
          tagOnlyArrival (taggedServiceWork rate (queueLength x.1) x.2) rate) 0 =
        PoissonProcess.arrivalTime (queueLength x.1) x.2 := by
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure (PoissonProcess.exponentialInterarrivalMeasure rate) :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  change ∀ᵐ x ∂tagged.Ptag.prod (PoissonProcess.exponentialInterarrivalMeasure rate),
    responseTime tagOnlyArrival
      (fcfsDepartureFrom (preTagBusyUntil (queueLength x.1) x.2)
        tagOnlyArrival (taggedServiceWork rate (queueLength x.1) x.2) rate) 0 =
      PoissonProcess.arrivalTime (queueLength x.1) x.2
  have hpos_prod : ∀ᵐ x ∂tagged.Ptag.prod (PoissonProcess.exponentialInterarrivalMeasure rate),
      ∀ i : ℕ, 0 < PoissonProcess.interarrival i x.2 := by
    refine ae_of_ae_map
      (μ := tagged.Ptag.prod (PoissonProcess.exponentialInterarrivalMeasure rate))
      (f := Prod.snd)
      (p := fun g : ℕ → ℝ => ∀ i : ℕ, 0 < PoissonProcess.interarrival i g)
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact PoissonProcess.ae_all_interarrival_positive hrate
  filter_upwards [hpos_prod] with x hx
  exact canonicalRenewalResponse_eq_fcfsTaggedResponse hrate (queueLength x.1) x.2 hx

/-- Build the count-level M/M/1 certificate by independently adjoining a concrete canonical
renewal service path.  The Poisson fixed-time service law and queue/service independence are
proved here; queue-tail, an a.e. response-event identity, and no-atom facts remain explicit. -/
noncomputable def TaggedArrivalAtZero.withIndependentRenewalServiceCountCertificateAE
    {Ω : Type*} [MeasurableSpace Ω]
    (tagged : TaggedArrivalAtZero Ω)
    (arrivalRate : ℝ) (harrivalRate : 0 < arrivalRate)
    (serviceRate : ℝ) (hserviceRate : 0 < serviceRate)
    (hstable : arrivalRate < serviceRate)
    (queueLength : Ω → ℕ) (hqueueLength : Measurable queueLength)
    (hqueueTail : ∀ k : ℕ,
      tagged.Ptag.real {ω | k ≤ queueLength ω} = (arrivalRate / serviceRate) ^ k)
    (response : Ω × (ℕ → ℝ) → ℝ) (hresponse : Measurable response)
    (hstrict : ∀ z : ℝ, 0 ≤ z →
      {ω | z < response ω} =ᵐ[
        (tagged.withCanonicalRenewalService serviceRate hserviceRate).Ptag]
        {ω | PoissonProcess.canonicalRenewalCount z ω.2 ≤ queueLength ω.1})
    (hatom : ∀ z : ℝ,
      (tagged.withCanonicalRenewalService serviceRate hserviceRate).Ptag.real
        {ω | response ω = z} = 0) :
    TaggedPASTAMM1CountCertificate (Ω × (ℕ → ℝ)) where
  toTaggedArrivalAtZero :=
    tagged.withCanonicalRenewalService serviceRate hserviceRate
  arrivalRate := arrivalRate
  serviceRate := serviceRate
  arrivalRate_pos := harrivalRate
  serviceRate_pos := hserviceRate
  stable := hstable
  preArrivalQueueLength := fun x => queueLength x.1
  completionCount := fun z x => PoissonProcess.canonicalRenewalCount z x.2
  response := response
  preArrivalQueueLength_measurable := hqueueLength.comp measurable_fst
  completionCount_measurable := fun z =>
    (PoissonProcess.measurable_canonicalRenewalCount z).comp measurable_snd
  response_measurable := hresponse
  preArrivalQueueLength_indep_completionCount := by
    intro z hz
    exact TaggedArrivalAtZero.prodRight_queue_indep_canonicalRenewalCount
      tagged queueLength hqueueLength serviceRate hserviceRate z
  stationary_preArrivalQueueLength_tail := by
    intro k
    letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
    letI : IsProbabilityMeasure (PoissonProcess.exponentialInterarrivalMeasure serviceRate) :=
      PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hserviceRate
    have hmeas : MeasurableSet {ω : Ω | k ≤ queueLength ω} :=
      measurableSet_le measurable_const hqueueLength
    calc
      (tagged.withCanonicalRenewalService serviceRate hserviceRate).Ptag.real
          {ω | k ≤ queueLength ω.1} =
          ((tagged.withCanonicalRenewalService serviceRate hserviceRate).Ptag.map
            Prod.fst).real {ω | k ≤ queueLength ω} := by
          change (tagged.Ptag.prod (PoissonProcess.exponentialInterarrivalMeasure serviceRate)).real
              {ω | k ≤ queueLength ω.1} =
            ((tagged.Ptag.prod (PoissonProcess.exponentialInterarrivalMeasure serviceRate)).map
              Prod.fst).real {ω | k ≤ queueLength ω}
          change
            ((tagged.Ptag.prod (PoissonProcess.exponentialInterarrivalMeasure serviceRate))
              {ω | k ≤ queueLength ω.1}).toReal =
            (((tagged.Ptag.prod (PoissonProcess.exponentialInterarrivalMeasure serviceRate)).map
              Prod.fst) {ω | k ≤ queueLength ω}).toReal
          rw [Measure.map_apply measurable_fst hmeas]
          rfl
      _ = tagged.Ptag.real {ω | k ≤ queueLength ω} := by
          change
            ((tagged.Ptag.prod (PoissonProcess.exponentialInterarrivalMeasure serviceRate)).map
              Prod.fst).real {ω | k ≤ queueLength ω} =
              tagged.Ptag.real {ω | k ≤ queueLength ω}
          rw [Measure.map_fst_prod, measure_univ, one_smul]
      _ = (arrivalRate / serviceRate) ^ k := hqueueTail k
  completionCount_poisson_law := by
    intro z hz k
    calc
      (tagged.withCanonicalRenewalService serviceRate hserviceRate).Ptag.real
          {ω | PoissonProcess.canonicalRenewalCount z ω.2 = k} =
          PoissonProcess.countLikelihood serviceRate z k :=
        PoissonProcess.hasLaw_poissonMeasure_real_singleton_eq_countLikelihood
          (mul_nonneg hserviceRate.le hz)
          (TaggedArrivalAtZero.prodRight_canonicalRenewalCount_hasLaw
            tagged serviceRate hserviceRate z hz) k
      _ = PoissonProcess.countLikelihood 1 (serviceRate * z) k := by
        simp [PoissonProcess.countLikelihood]
  strict_response_event := hstrict
  response_atom_zero := hatom

/-- Compatibility constructor for an everywhere response/count identity. -/
noncomputable def TaggedArrivalAtZero.withIndependentRenewalServiceCountCertificate
    {Ω : Type*} [MeasurableSpace Ω]
    (tagged : TaggedArrivalAtZero Ω)
    (arrivalRate : ℝ) (harrivalRate : 0 < arrivalRate)
    (serviceRate : ℝ) (hserviceRate : 0 < serviceRate)
    (hstable : arrivalRate < serviceRate)
    (queueLength : Ω → ℕ) (hqueueLength : Measurable queueLength)
    (hqueueTail : ∀ k : ℕ,
      tagged.Ptag.real {ω | k ≤ queueLength ω} = (arrivalRate / serviceRate) ^ k)
    (response : Ω × (ℕ → ℝ) → ℝ) (hresponse : Measurable response)
    (hstrict : ∀ z : ℝ, 0 ≤ z →
      {ω | z < response ω} =
        {ω | PoissonProcess.canonicalRenewalCount z ω.2 ≤ queueLength ω.1})
    (hatom : ∀ z : ℝ,
      (tagged.withCanonicalRenewalService serviceRate hserviceRate).Ptag.real
        {ω | response ω = z} = 0) :
    TaggedPASTAMM1CountCertificate (Ω × (ℕ → ℝ)) :=
  tagged.withIndependentRenewalServiceCountCertificateAE
    arrivalRate harrivalRate serviceRate hserviceRate hstable
    queueLength hqueueLength hqueueTail response hresponse
    (by
      intro z hz
      rw [hstrict z hz])
    hatom

/-- For the canonical renewal time to clear the inherited queue, the response
measurability and almost-everywhere count identity are derived internally.
The inherited queue tail is the only remaining count-level premise. -/
noncomputable def TaggedArrivalAtZero.withIndependentCanonicalRenewalResponseCountCertificate
    {Ω : Type*} [MeasurableSpace Ω]
    (tagged : TaggedArrivalAtZero Ω)
    (arrivalRate : ℝ) (harrivalRate : 0 < arrivalRate)
    (serviceRate : ℝ) (hserviceRate : 0 < serviceRate)
    (hstable : arrivalRate < serviceRate)
    (queueLength : Ω → ℕ) (hqueueLength : Measurable queueLength)
    (hqueueTail : ∀ k : ℕ,
      tagged.Ptag.real {ω | k ≤ queueLength ω} = (arrivalRate / serviceRate) ^ k) :
    TaggedPASTAMM1CountCertificate (Ω × (ℕ → ℝ)) :=
  tagged.withIndependentRenewalServiceCountCertificateAE
    arrivalRate harrivalRate serviceRate hserviceRate hstable
    queueLength hqueueLength hqueueTail
    (fun x => PoissonProcess.arrivalTime (queueLength x.1) x.2)
    (measurable_canonicalRenewalResponse queueLength hqueueLength)
    (fun z _ => tagged.ae_strict_canonicalRenewalResponse_event
      queueLength serviceRate hserviceRate z)
    (fun z => tagged.canonicalRenewalQueueResponse_atom_zero
      queueLength serviceRate hserviceRate z)

end

end AppliedModelingLib.Probability.Queueing
