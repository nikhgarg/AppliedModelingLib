import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalRenewalCountMarginal
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalFuture
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Post-arrival regeneration of canonical exponential renewal counts

At every deterministic arrival index, the canonical exponential interarrival
path regenerates: the count after that arrival is a fresh canonical count and
has its fixed-time Poisson law. This is a genuine post-tag component, but it
does not assert arbitrary deterministic-time increments: those start inside a
random interarrival gap and require a stopped residual-tail memorylessness
theorem.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal NNReal Topology ProbabilityTheory

noncomputable section

/--
Deterministic-index renewal regeneration: after the first `n` arrivals, the
count at the shifted horizon is exactly `n` plus the count of the fresh tail.
This is pathwise and does not assert an arbitrary deterministic-time increment
law.
-/
theorem canonicalRenewalCount_arrivalPrefix_add
    (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (ω : ℕ → ℝ)
    (hpos : ∀ i : ℕ, 0 < interarrival i ω)
    (htail : Tendsto (fun m : ℕ => futureArrivalTime n m ω) atTop atTop) :
    canonicalRenewalCount (arrivalPrefix n ω + t) ω =
      n + canonicalRenewalCount t (futureInterarrival n ω) := by
  let q := canonicalRenewalCount t (futureInterarrival n ω)
  have htailFuture : ∃ m : ℕ, t < arrivalTime m (futureInterarrival n ω) := by
    obtain ⟨m, hm⟩ := (htail.eventually_gt_atTop t).exists
    exact ⟨m, by
      simpa only [futureArrivalTime_eq_arrivalTime_tail, Function.comp_apply] using hm⟩
  have hqFuture : t < futureArrivalTime n q ω := by
    have h := lt_arrivalTime_canonicalRenewalCount t (futureInterarrival n ω)
      htailFuture
    simpa only [q, futureArrivalTime_eq_arrivalTime_tail, Function.comp_apply] using h
  have hsourceFuture : ∃ k : ℕ,
      arrivalPrefix n ω + t < arrivalTime k ω := by
    refine ⟨n + q, ?_⟩
    rw [arrivalTime_add_eq_arrivalPrefix_add_futureArrivalTime]
    simpa only [Function.comp_apply, add_comm] using
      (add_lt_add_left hqFuture (arrivalPrefix n ω))
  have hsource_le :
      canonicalRenewalCount (arrivalPrefix n ω + t) ω ≤ n + q := by
    rw [canonicalRenewalCount_eq_find _ _ hsourceFuture]
    apply Nat.find_min'
    rw [arrivalTime_add_eq_arrivalPrefix_add_futureArrivalTime]
    simpa only [Function.comp_apply, add_comm] using
      (add_lt_add_left hqFuture (arrivalPrefix n ω))
  have hbefore : ∀ k : ℕ, k < n + q →
      arrivalTime k ω ≤ arrivalPrefix n ω + t := by
    intro k hk
    by_cases hkn : k < n
    · cases n with
      | zero => omega
      | succ n' =>
        have hle : k ≤ n' := by omega
        have htime : arrivalTime k ω ≤ arrivalTime n' ω :=
          (arrivalTime_strictMono_of_positive ω hpos).monotone hle
        have hpref : arrivalPrefix (n' + 1) ω = arrivalTime n' ω := by
          rfl
        rw [hpref]
        linarith
    · have hnle : n ≤ k := Nat.le_of_not_gt hkn
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hnle
      have hm : m < q := by omega
      have htaille : arrivalTime m (futureInterarrival n ω) ≤ t :=
        arrivalTime_le_of_lt_canonicalRenewalCount t (futureInterarrival n ω)
          htailFuture hm
      rw [arrivalTime_add_eq_arrivalPrefix_add_futureArrivalTime]
      simpa only [futureArrivalTime_eq_arrivalTime_tail, Function.comp_apply, add_comm] using
        (add_le_add_left htaille (arrivalPrefix n ω))
  have hsource_ge : n + q ≤ canonicalRenewalCount (arrivalPrefix n ω + t) ω := by
    by_contra hnot
    have hlt : canonicalRenewalCount (arrivalPrefix n ω + t) ω < n + q :=
      Nat.lt_of_not_ge hnot
    have hle := hbefore (canonicalRenewalCount (arrivalPrefix n ω + t) ω) hlt
    exact (not_le_of_gt
      (lt_arrivalTime_canonicalRenewalCount (arrivalPrefix n ω + t) ω hsourceFuture)) hle
  exact Nat.le_antisymm hsource_le hsource_ge

/-- The deterministic post-arrival tail has the fixed-time Poisson law. -/
theorem canonicalRenewalCount_futureInterarrival_hasLaw_poisson
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) (n : ℕ) :
    ProbabilityTheory.HasLaw
      (fun ω : ℕ → ℝ => canonicalRenewalCount t (futureInterarrival n ω))
      (ProbabilityTheory.poissonMeasure
        (⟨rate * t, mul_nonneg hrate.le ht⟩ : ℝ≥0))
      (exponentialInterarrivalMeasure rate) := by
  simpa only [Function.comp_apply] using
    (canonicalRenewalCount_hasLaw_poisson hrate ht).comp
      (futureInterarrival_hasLaw_path hrate n)

/-- The pathwise deterministic-index regeneration identity holds almost surely
under the canonical exponential product law. -/
theorem ae_canonicalRenewalCount_arrivalPrefix_add
    {rate : ℝ} (hrate : 0 < rate) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      canonicalRenewalCount (arrivalPrefix n ω + t) ω =
        n + canonicalRenewalCount t (futureInterarrival n ω) := by
  have htailRaw : ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      Tendsto (fun m : ℕ => arrivalTime m (futureInterarrival n ω)) atTop atTop := by
    have hmap : ∀ᵐ ξ ∂Measure.map (futureInterarrival n)
        (exponentialInterarrivalMeasure rate),
        Tendsto (fun m : ℕ => arrivalTime m ξ) atTop atTop := by
      rw [(futureInterarrival_hasLaw_path hrate n).map_eq]
      exact ae_arrivalTime_tendsto_atTop hrate
    exact (Measure.tendsto_ae_map
      (futureInterarrival_hasLaw_path hrate n).aemeasurable) hmap
  have htail : ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      Tendsto (fun m : ℕ => futureArrivalTime n m ω) atTop atTop := by
    filter_upwards [htailRaw] with ω hω
    simpa only [futureArrivalTime_eq_arrivalTime_tail, Function.comp_apply] using hω
  filter_upwards [ae_all_interarrival_positive hrate, htail] with ω hpos htail
  exact canonicalRenewalCount_arrivalPrefix_add n t ht ω hpos htail

/--
At a deterministic arrival index, the subsequent renewal-count increment has
the fixed-time Poisson law. This does not make the origin stationary or prove
arbitrary clock-time independent increments.
-/
theorem canonicalRenewalCount_postArrivalIncrement_hasLaw_poisson
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) (n : ℕ) :
    ProbabilityTheory.HasLaw
      (fun ω : ℕ → ℝ => canonicalRenewalCount (arrivalPrefix n ω + t) ω - n)
      (ProbabilityTheory.poissonMeasure
        (⟨rate * t, mul_nonneg hrate.le ht⟩ : ℝ≥0))
      (exponentialInterarrivalMeasure rate) := by
  apply (canonicalRenewalCount_futureInterarrival_hasLaw_poisson hrate ht n).congr
  filter_upwards [ae_canonicalRenewalCount_arrivalPrefix_add hrate n t ht] with ω hω
  rw [hω]
  simp

/-- The deterministic arrival-prefix time is measurable. -/
theorem measurable_arrivalPrefix (n : ℕ) :
    Measurable (arrivalPrefix n) := by
  unfold arrivalPrefix
  exact (Finset.range n).measurable_sum fun i _ => measurable_interarrival i

/-- The complete finite interarrival prefix before deterministic index `n`. -/
def prefixInterarrival (n : ℕ) : (ℕ → ℝ) → Fin n → ℝ :=
  fun ω i => interarrival i ω

/-- The finite interarrival prefix is measurable. -/
theorem measurable_prefixInterarrival (n : ℕ) :
    Measurable (prefixInterarrival n) := by
  apply measurable_pi_iff.2
  intro i
  exact measurable_interarrival i

/-- The complete finite interarrival prefix before deterministic index `n` is
independent of the entire future interarrival tail starting at that index. -/
theorem prefixInterarrival_indep_futureInterarrival
    {rate : ℝ} (hrate : 0 < rate) (n : ℕ) :
    ProbabilityTheory.IndepFun (prefixInterarrival n) (futureInterarrival n)
      (exponentialInterarrivalMeasure rate) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let m : ℕ → MeasurableSpace (ℕ → ℝ) :=
    fun i => MeasurableSpace.comap (interarrival i) inferInstance
  change ProbabilityTheory.IndepFun (prefixInterarrival n) (futureInterarrival n) μ
  have h_indep_big : ProbabilityTheory.Indep
      (⨆ i ∈ Set.Iio n, m i)
      (⨆ i ∈ Set.Ici n, m i) μ := by
    apply ProbabilityTheory.indep_iSup_of_disjoint
    · intro i
      exact (measurable_interarrival i).comap_le
    · exact (iIndepFun_interarrival hrate).iIndep
    · refine Set.disjoint_left.2 ?_
      intro i hiIio hiIci
      change i < n at hiIio
      change n ≤ i at hiIci
      omega
  have hprefix_meas : @Measurable (ℕ → ℝ) (Fin n → ℝ)
      (⨆ i ∈ Set.Iio n, m i) inferInstance (prefixInterarrival n) := by
    apply Measurable.of_comap_le
    rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    apply iSup_le
    intro i
    rw [MeasurableSpace.comap_comp]
    change m i ≤ ⨆ j ∈ Set.Iio n, m j
    exact le_iSup_of_le i (le_iSup_of_le i.2 le_rfl)
  have htail_meas : @Measurable (ℕ → ℝ) (ℕ → ℝ)
      (⨆ i ∈ Set.Ici n, m i) inferInstance (futureInterarrival n) := by
    apply Measurable.of_comap_le
    rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    apply iSup_le
    intro k
    rw [MeasurableSpace.comap_comp]
    change m (n + k) ≤ ⨆ i ∈ Set.Ici n, m i
    exact le_iSup_of_le (n + k) (le_iSup_of_le (Nat.le_add_right n k) le_rfl)
  refine (ProbabilityTheory.IndepFun_iff_Indep _ _ _).mpr ?_
  intro s t hs ht
  exact h_indep_big s t (hprefix_meas.comap_le s hs) (htail_meas.comap_le t ht)

/-- The total length of a finite interarrival prefix is its arrival-prefix
time. -/
theorem sum_prefixInterarrival (n : ℕ) (ω : ℕ → ℝ) :
    (∑ i : Fin n, prefixInterarrival n ω i) = arrivalPrefix n ω := by
  induction n with
  | zero => simp [prefixInterarrival, arrivalPrefix]
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [prefixInterarrival, Fin.val_castSucc, Fin.val_last]
      have hsum : (∑ i : Fin n, interarrival i ω) = arrivalPrefix n ω := by
        simpa [prefixInterarrival] using ih
      rw [hsum]
      simp [arrivalPrefix, Finset.sum_range_succ]

/-- The finite prefix and entire future tail have their product law.  Keeping
the prefix marginal abstract makes this suitable for conditioning on any
finite prefix statistic, not only its total arrival time. -/
theorem prefixInterarrival_futureInterarrival_hasLaw_prod
    {rate : ℝ} (hrate : 0 < rate) (n : ℕ) :
    ProbabilityTheory.HasLaw
      (fun ω : ℕ → ℝ => (prefixInterarrival n ω, futureInterarrival n ω))
      ((Measure.map (prefixInterarrival n) (exponentialInterarrivalMeasure rate)).prod
        (exponentialInterarrivalMeasure rate))
      (exponentialInterarrivalMeasure rate) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let X : (ℕ → ℝ) → Fin n → ℝ := prefixInterarrival n
  let Y : (ℕ → ℝ) → ℕ → ℝ := futureInterarrival n
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hX : Measurable X := by simpa [X] using measurable_prefixInterarrival n
  have hY : Measurable Y := by
    simpa [Y] using measurable_pi_iff.2 (fun k => measurable_futureInterarrival n k)
  have hIndep : ProbabilityTheory.IndepFun X Y μ := by
    simpa [μ, X, Y] using prefixInterarrival_indep_futureInterarrival hrate n
  have htail : μ.map Y = μ := by
    simpa [μ, Y] using (futureInterarrival_hasLaw_path hrate n).map_eq
  refine ⟨(hX.prodMk hY).aemeasurable, ?_⟩
  calc
    μ.map (fun ω => (X ω, Y ω)) = (μ.map X).prod (μ.map Y) :=
      (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
        hX.aemeasurable hY.aemeasurable).mp hIndep
    _ = (μ.map X).prod μ := by rw [htail]

/--
The time of the `n`th canonical arrival is independent of the entire tail
starting at that arrival.  Here `arrivalPrefix 1` is the first arrival time,
and `arrivalPrefix 2` is the second.  This is a deterministic arrival-index
split, rather than a claim about an arbitrary clock-time stopping rule.
-/
theorem arrivalPrefix_indep_futureInterarrival
    {rate : ℝ} (hrate : 0 < rate) (n : ℕ) :
    ProbabilityTheory.IndepFun (arrivalPrefix n) (futureInterarrival n)
      (exponentialInterarrivalMeasure rate) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let m : ℕ → MeasurableSpace (ℕ → ℝ) :=
    fun i => MeasurableSpace.comap (interarrival i) inferInstance
  change ProbabilityTheory.IndepFun (arrivalPrefix n) (futureInterarrival n) μ
  have h_indep_big : ProbabilityTheory.Indep
      (⨆ i ∈ Set.Iio n, m i)
      (⨆ i ∈ Set.Ici n, m i) μ := by
    apply ProbabilityTheory.indep_iSup_of_disjoint
    · intro i
      exact (measurable_interarrival i).comap_le
    · exact (iIndepFun_interarrival hrate).iIndep
    · refine Set.disjoint_left.2 ?_
      intro i hiIio hiIci
      change i < n at hiIio
      change n ≤ i at hiIci
      omega
  have hprefix_meas : @Measurable (ℕ → ℝ) ℝ
      (⨆ i ∈ Set.Iio n, m i) inferInstance (arrivalPrefix n) := by
    unfold arrivalPrefix
    apply Finset.measurable_sum
    intro i hi
    apply Measurable.of_comap_le
    change m i ≤ ⨆ j ∈ Set.Iio n, m j
    exact le_iSup_of_le i (le_iSup_of_le (Finset.mem_range.mp hi) le_rfl)
  have htail_meas : @Measurable (ℕ → ℝ) (ℕ → ℝ)
      (⨆ i ∈ Set.Ici n, m i) inferInstance (futureInterarrival n) := by
    apply Measurable.of_comap_le
    rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    apply iSup_le
    intro k
    rw [MeasurableSpace.comap_comp]
    change m (n + k) ≤ ⨆ i ∈ Set.Ici n, m i
    exact le_iSup_of_le (n + k) (le_iSup_of_le (Nat.le_add_right n k) le_rfl)
  refine (ProbabilityTheory.IndepFun_iff_Indep _ _ _).mpr ?_
  intro s t hs ht
  exact h_indep_big s t (hprefix_meas.comap_le s hs) (htail_meas.comap_le t ht)

/-- The regular conditional law of the entire tail after any deterministic
arrival index is the original exponential-interarrival product measure.  This
is the kernel form of deterministic-index regeneration; it is not a
random-clock or stopped-filtration result. -/
theorem arrivalPrefix_condDistrib_futureInterarrival_eq_const
    {rate : ℝ} (hrate : 0 < rate) (n : ℕ) :
    letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
      isProbabilityMeasure_exponentialInterarrivalMeasure hrate
    ProbabilityTheory.condDistrib (futureInterarrival n) (arrivalPrefix n)
        (exponentialInterarrivalMeasure rate) =ᵐ[
          (exponentialInterarrivalMeasure rate).map (arrivalPrefix n)]
        Kernel.const ℝ (exponentialInterarrivalMeasure rate) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let X : (ℕ → ℝ) → ℝ := arrivalPrefix n
  let Y : (ℕ → ℝ) → ℕ → ℝ := futureInterarrival n
  letI : IsProbabilityMeasure μ := by
    simpa only [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hX : Measurable X := by
    simpa only [X] using measurable_arrivalPrefix n
  have hY : Measurable Y := by
    simpa only [Y] using measurable_pi_iff.2
      (fun k => measurable_futureInterarrival n k)
  have hIndep : ProbabilityTheory.IndepFun X Y μ := by
    simpa only [μ, X, Y] using arrivalPrefix_indep_futureInterarrival hrate n
  have htail : μ.map Y = μ := by
    simpa only [μ, Y] using (futureInterarrival_hasLaw_path hrate n).map_eq
  have hjoint : μ.map (fun ω => (X ω, Y ω)) = (μ.map X).prod μ := by
    calc
      μ.map (fun ω => (X ω, Y ω)) = (μ.map X).prod (μ.map Y) :=
        (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
          hX.aemeasurable hY.aemeasurable).mp hIndep
      _ = (μ.map X).prod μ := by rw [htail]
  change ProbabilityTheory.condDistrib Y X μ =ᵐ[μ.map X] Kernel.const ℝ μ
  apply ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hX hY
  simpa only [Measure.compProd_const] using hjoint

/--
Atomwise regular conditional law of the canonical tail count after any fixed
arrival index, conditioned on that arrival time.  It gives the concrete
Poisson restart needed when a reporting interval starts at a first, second, or
other fixed-index report.
-/
theorem arrivalPrefix_conditional_futureRenewalCount_atom
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) (n k : ℕ) :
    letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
      isProbabilityMeasure_exponentialInterarrivalMeasure hrate
    ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      (ProbabilityTheory.condExpKernel (exponentialInterarrivalMeasure rate)
        (MeasurableSpace.comap (arrivalPrefix n) inferInstance) ω).real
          {ω' | canonicalRenewalCount t (futureInterarrival n ω') = k} =
        (ProbabilityTheory.poissonMeasure
          (⟨rate * t, mul_nonneg hrate.le ht⟩ : ℝ≥0)).real {k} := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let ν : Measure ℕ := ProbabilityTheory.poissonMeasure
    (⟨rate * t, mul_nonneg hrate.le ht⟩ : ℝ≥0)
  letI : IsProbabilityMeasure μ := by
    simpa only [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  let X : (ℕ → ℝ) → ℝ := arrivalPrefix n
  let Y : (ℕ → ℝ) → ℕ :=
    fun ω => canonicalRenewalCount t (futureInterarrival n ω)
  let A : Set (ℕ → ℝ) := {ω | Y ω = k}
  have hX : Measurable X := by
    simpa only [X] using measurable_arrivalPrefix n
  have hY : Measurable Y := by
    simpa only [Y] using (measurable_canonicalRenewalCount t).comp
      (measurable_pi_iff.2 fun j => measurable_futureInterarrival n j)
  have hA : @MeasurableSet (ℕ → ℝ) MeasurableSpace.pi A := by
    simpa only [A, Set.preimage_setOf_eq] using hY (measurableSet_singleton k)
  have hA_mY : MeasurableSet[MeasurableSpace.comap Y Nat.instMeasurableSpace] A := by
    simpa only [A, Set.preimage_setOf_eq] using
      (MeasurableSpace.measurableSet_comap.2
        ⟨{k}, measurableSet_singleton k, rfl⟩)
  have hIndep : ProbabilityTheory.IndepFun X Y μ := by
    simpa only [X, Y] using
      (arrivalPrefix_indep_futureInterarrival hrate n).comp
        measurable_id (measurable_canonicalRenewalCount t)
  have hIndepYX : ProbabilityTheory.Indep
      (MeasurableSpace.comap Y Nat.instMeasurableSpace)
      (MeasurableSpace.comap X Real.measurableSpace) μ := by
    exact ((ProbabilityTheory.IndepFun_iff_Indep X Y μ).mp hIndep).symm
  have hXle : MeasurableSpace.comap X Real.measurableSpace ≤ MeasurableSpace.pi :=
    hX.comap_le
  have hYle : MeasurableSpace.comap Y Nat.instMeasurableSpace ≤ MeasurableSpace.pi :=
    hY.comap_le
  letI : IsFiniteMeasure (μ.trim hXle) := MeasureTheory.isFiniteMeasure_trim hXle
  have hcond : μ[A.indicator fun _ => (1 : ℝ) |
      MeasurableSpace.comap X Real.measurableSpace] =ᵐ[μ]
      fun _ => ∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂μ := by
    exact MeasureTheory.condExp_indep_eq
      (m₁ := MeasurableSpace.comap Y Nat.instMeasurableSpace)
      (m₂ := MeasurableSpace.comap X Real.measurableSpace)
      (m := MeasurableSpace.pi)
      hYle hXle
      ((measurable_const.indicator hA_mY).stronglyMeasurable) hIndepYX
  have hYlaw : @ProbabilityTheory.HasLaw (ℕ → ℝ) ℕ
      MeasurableSpace.pi Nat.instMeasurableSpace Y ν μ := by
    simpa only [μ, ν, Y, Function.comp_apply] using
      canonicalRenewalCount_futureInterarrival_hasLaw_poisson hrate ht n
  have hintegral : (∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂μ) = ν.real {k} := by
    rw [integral_indicator hA, setIntegral_const, smul_eq_mul, mul_one]
    calc
      μ.real A = (μ.map Y).real {k} := by
        rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
          Measure.map_apply hY (measurableSet_singleton k)]
        rfl
      _ = ν.real {k} := by rw [hYlaw.map_eq]
  have hcond' : μ[A.indicator fun _ => (1 : ℝ) |
      MeasurableSpace.comap X Real.measurableSpace] =ᵐ[μ]
      fun _ => ν.real {k} :=
    hcond.trans (Filter.Eventually.of_forall fun _ => hintegral)
  have hkernel : (fun ω =>
      (ProbabilityTheory.condExpKernel μ
        (MeasurableSpace.comap X Real.measurableSpace) ω).real A) =ᵐ[μ]
      μ[A.indicator fun _ => (1 : ℝ) |
        MeasurableSpace.comap X Real.measurableSpace] :=
    ProbabilityTheory.condExpKernel_ae_eq_condExp hXle hA
  simpa only [μ, ν, X, Y, A] using hkernel.trans hcond'

/--
The full conditional Poisson law for a renewal count after a deterministic
arrival index.
-/
theorem arrivalPrefix_conditional_futureRenewalCount_hasLaw_poisson
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) (n : ℕ) :
    letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
      isProbabilityMeasure_exponentialInterarrivalMeasure hrate
    ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      ProbabilityTheory.HasLaw
        (fun ω' : ℕ → ℝ => canonicalRenewalCount t (futureInterarrival n ω'))
        (ProbabilityTheory.poissonMeasure
          (⟨rate * t, mul_nonneg hrate.le ht⟩ : ℝ≥0))
        (ProbabilityTheory.condExpKernel (exponentialInterarrivalMeasure rate)
          (MeasurableSpace.comap (arrivalPrefix n) inferInstance) ω) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let ν : Measure ℕ := ProbabilityTheory.poissonMeasure
    (⟨rate * t, mul_nonneg hrate.le ht⟩ : ℝ≥0)
  letI : IsProbabilityMeasure μ := by
    simpa only [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  let Y : (ℕ → ℝ) → ℕ :=
    fun ω => canonicalRenewalCount t (futureInterarrival n ω)
  have hY : Measurable Y := by
    simpa only [Y] using (measurable_canonicalRenewalCount t).comp
      (measurable_pi_iff.2 fun j => measurable_futureInterarrival n j)
  have hatoms : ∀ᵐ ω ∂μ, ∀ k : ℕ,
      (ProbabilityTheory.condExpKernel μ
        (MeasurableSpace.comap (arrivalPrefix n) inferInstance) ω).real
          {ω' | Y ω' = k} = ν.real {k} := by
    rw [ae_all_iff]
    intro k
    simpa only [μ, ν, Y] using
      arrivalPrefix_conditional_futureRenewalCount_atom hrate ht n k
  filter_upwards [hatoms] with ω hω
  refine ⟨hY.aemeasurable, ?_⟩
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  intro k
  rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
    Measure.map_apply hY (measurableSet_singleton k)]
  exact hω k

/--
Conditional no-report probability after any deterministic arrival index.
-/
theorem arrivalPrefix_conditional_futureRenewalCount_zero_real
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) (n : ℕ) :
    letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
      isProbabilityMeasure_exponentialInterarrivalMeasure hrate
    ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      (ProbabilityTheory.condExpKernel (exponentialInterarrivalMeasure rate)
        (MeasurableSpace.comap (arrivalPrefix n) inferInstance) ω).real
          {ω' | canonicalRenewalCount t (futureInterarrival n ω') = 0} =
        noArrivalProb rate t := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure μ := by
    simpa only [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  filter_upwards [arrivalPrefix_conditional_futureRenewalCount_hasLaw_poisson
    hrate ht n] with ω hω
  exact hasLaw_poissonMeasure_real_singleton_eq_countLikelihood
    (mul_nonneg hrate.le ht) hω 0 |>.trans
      (noArrivalProb_eq_countLikelihood_zero rate t).symm

/--
The first canonical interarrival is independent of the full future gap path.

Unlike the finite-block regeneration results, this is an independence statement
for the whole deterministic tail.  It is the concrete first-arrival split used
below; it does not assert regeneration at an arbitrary random stopping index.
-/
theorem interarrival_zero_indep_futureInterarrival
    {rate : ℝ} (hrate : 0 < rate) :
    ProbabilityTheory.IndepFun (interarrival 0) (futureInterarrival 1)
      (exponentialInterarrivalMeasure rate) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let m : ℕ → MeasurableSpace (ℕ → ℝ) :=
    fun i => MeasurableSpace.comap (interarrival i) inferInstance
  change ProbabilityTheory.IndepFun (interarrival 0) (futureInterarrival 1) μ
  have h_indep_big : ProbabilityTheory.Indep
      (⨆ i ∈ ({0} : Set ℕ), m i)
      (⨆ i ∈ Set.Ici (1 : ℕ), m i) μ := by
    apply ProbabilityTheory.indep_iSup_of_disjoint
    · intro i
      exact (measurable_interarrival i).comap_le
    · exact (iIndepFun_interarrival hrate).iIndep
    · exact Set.disjoint_singleton_left.mpr (by simp)
  have hhead_le : m 0 ≤ ⨆ i ∈ ({0} : Set ℕ), m i := by
    exact le_iSup_of_le 0 (le_iSup_of_le (by simp) le_rfl)
  have htail_meas : @Measurable (ℕ → ℝ) (ℕ → ℝ)
      (⨆ i ∈ Set.Ici (1 : ℕ), m i) inferInstance (futureInterarrival 1) := by
    apply Measurable.of_comap_le
    rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    apply iSup_le
    intro k
    rw [MeasurableSpace.comap_comp]
    change m (1 + k) ≤ ⨆ i ∈ Set.Ici (1 : ℕ), m i
    exact le_iSup_of_le (1 + k) (le_iSup_of_le (by simp) le_rfl)
  refine (ProbabilityTheory.IndepFun_iff_Indep _ _ _).mpr ?_
  intro s t hs ht
  exact h_indep_big s t (hhead_le s hs) (htail_meas.comap_le t ht)

/-- Kernel form of the first-arrival/tail split on the nonnegative time axis.
The `toNNReal` coercion makes the first arrival suitable for a forward-time
consumer; the conclusion is still only deterministic-index regeneration. -/
theorem canonicalFirstArrival_toNNReal_condDistrib_futureInterarrival_eq_const
    {rate : ℝ} (hrate : 0 < rate) :
    letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
      isProbabilityMeasure_exponentialInterarrivalMeasure hrate
    ProbabilityTheory.condDistrib
        (futureInterarrival 1)
        (fun ω : ℕ → ℝ => (canonicalFirstArrival ω).toNNReal)
        (exponentialInterarrivalMeasure rate) =ᵐ[
          (exponentialInterarrivalMeasure rate).map
            (fun ω : ℕ → ℝ => (canonicalFirstArrival ω).toNNReal)]
        Kernel.const ℝ≥0 (exponentialInterarrivalMeasure rate) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let X : (ℕ → ℝ) → ℝ≥0 := fun ω => (canonicalFirstArrival ω).toNNReal
  let Y : (ℕ → ℝ) → ℕ → ℝ := futureInterarrival 1
  letI : IsProbabilityMeasure μ := by
    simpa only [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hX : Measurable X := by
    simpa only [X, canonicalFirstArrival] using
      measurable_real_toNNReal.comp (measurable_interarrival 0)
  have hY : Measurable Y := by
    simpa only [Y] using measurable_pi_iff.2
      (fun k => measurable_futureInterarrival 1 k)
  have hIndep : ProbabilityTheory.IndepFun X Y μ := by
    simpa only [μ, X, Y, canonicalFirstArrival] using
      (interarrival_zero_indep_futureInterarrival hrate).comp
        measurable_real_toNNReal measurable_id
  have htail : μ.map Y = μ := by
    simpa only [μ, Y] using (futureInterarrival_hasLaw_path hrate 1).map_eq
  have hjoint : μ.map (fun ω => (X ω, Y ω)) = (μ.map X).prod μ := by
    calc
      μ.map (fun ω => (X ω, Y ω)) = (μ.map X).prod (μ.map Y) :=
        (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
          hX.aemeasurable hY.aemeasurable).mp hIndep
      _ = (μ.map X).prod μ := by rw [htail]
  change ProbabilityTheory.condDistrib Y X μ =ᵐ[μ.map X] Kernel.const ℝ≥0 μ
  apply ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hX hY
  simpa only [Measure.compProd_const] using hjoint

/--
Transport the post-first-arrival regeneration law to any measurable path with
the iid exponential interarrival law.  This is the process-level form of the
standard Poisson restart after the first arrival; it does not impose any
selected-start or observation-window condition.
-/
theorem condDistrib_futureInterarrival_one_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {rate : ℝ} (rate_pos : 0 < rate)
    (interarrivalPath : Ω → ℕ → ℝ)
    (interarrivalPath_measurable : Measurable interarrivalPath)
    (interarrivalPath_hasLaw : ProbabilityTheory.HasLaw interarrivalPath
      (exponentialInterarrivalMeasure rate) P) :
    ProbabilityTheory.condDistrib
      (fun ω => futureInterarrival 1 (interarrivalPath ω))
      (fun ω => (canonicalFirstArrival (interarrivalPath ω)).toNNReal) P =ᵐ[
        P.map (fun ω => (canonicalFirstArrival (interarrivalPath ω)).toNNReal)]
      Kernel.const ℝ≥0 (exponentialInterarrivalMeasure rate) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let X : (ℕ → ℝ) → ℝ≥0 :=
    fun path => (canonicalFirstArrival path).toNNReal
  let Y : (ℕ → ℝ) → (ℕ → ℝ) := futureInterarrival 1
  letI : IsProbabilityMeasure μ := by
    simpa only [μ] using
      isProbabilityMeasure_exponentialInterarrivalMeasure rate_pos
  have hX : Measurable X := by
    simpa only [X, canonicalFirstArrival] using
      measurable_real_toNNReal.comp (measurable_interarrival 0)
  have hY : Measurable Y := by
    simpa only [Y] using
      measurable_pi_iff.2 fun k => measurable_futureInterarrival 1 k
  have hcanonical :
      ProbabilityTheory.condDistrib Y X μ =ᵐ[μ.map X]
        Kernel.const ℝ≥0 μ := by
    simpa only [μ, X, Y] using
      canonicalFirstArrival_toNNReal_condDistrib_futureInterarrival_eq_const
        rate_pos
  have htransport := ProbabilityTheory.condDistrib_map
    (ν := P) (X := X) (Y := Y) (f := interarrivalPath)
    (by simpa only [interarrivalPath_hasLaw.map_eq] using hX.aemeasurable)
    (by simpa only [interarrivalPath_hasLaw.map_eq] using hY.aemeasurable)
    interarrivalPath_measurable.aemeasurable
  have hfirstMap : P.map (X ∘ interarrivalPath) = μ.map X := by
    rw [← Measure.map_map hX interarrivalPath_measurable,
      interarrivalPath_hasLaw.map_eq]
  have htransport' :
      ProbabilityTheory.condDistrib Y X μ =ᵐ[P.map (X ∘ interarrivalPath)]
        ProbabilityTheory.condDistrib (Y ∘ interarrivalPath)
          (X ∘ interarrivalPath) P := by
    simpa only [interarrivalPath_hasLaw.map_eq] using htransport
  have hcanonical' :
      ProbabilityTheory.condDistrib Y X μ =ᵐ[P.map (X ∘ interarrivalPath)]
        Kernel.const ℝ≥0 μ := by
    rw [hfirstMap]
    exact hcanonical
  simpa only [μ, X, Y, Function.comp_apply] using
    htransport'.symm.trans hcanonical'

/--
The first report time is independent of the canonical renewal count in the
full post-first-report tail at every fixed horizon.
-/
theorem canonicalFirstArrival_indep_futureRenewalCount
    {rate t : ℝ} (hrate : 0 < rate) :
    ProbabilityTheory.IndepFun canonicalFirstArrival
      (fun ω : ℕ → ℝ => canonicalRenewalCount t (futureInterarrival 1 ω))
      (exponentialInterarrivalMeasure rate) := by
  simpa only [canonicalFirstArrival, Function.comp_def] using
    (interarrival_zero_indep_futureInterarrival hrate).comp
      measurable_id (measurable_canonicalRenewalCount t)

/--
Joint exponential--Poisson law of the first canonical report and a fixed
post-first-report count.  This is the finite-horizon first-report component of
the Poisson restart used by first-report process specializations.
-/
theorem canonicalFirstArrival_futureRenewalCount_hasLaw_prod
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    ProbabilityTheory.HasLaw
      (fun ω : ℕ → ℝ =>
        (canonicalFirstArrival ω,
          canonicalRenewalCount t (futureInterarrival 1 ω)))
      ((ProbabilityTheory.expMeasure rate).prod
        (ProbabilityTheory.poissonMeasure
          (⟨rate * t, mul_nonneg hrate.le ht⟩ : ℝ≥0)))
      (exponentialInterarrivalMeasure rate) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure μ := by
    simpa only [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  let ν : Measure ℕ := ProbabilityTheory.poissonMeasure
    (⟨rate * t, mul_nonneg hrate.le ht⟩ : ℝ≥0)
  let X : (ℕ → ℝ) → ℝ := canonicalFirstArrival
  let Y : (ℕ → ℝ) → ℕ :=
    fun ω => canonicalRenewalCount t (futureInterarrival 1 ω)
  have hX : Measurable X := by
    exact measurable_interarrival 0
  have hY : Measurable Y := by
    exact (measurable_canonicalRenewalCount t).comp
      (measurable_pi_iff.2 fun k => measurable_futureInterarrival 1 k)
  have hIndep : ProbabilityTheory.IndepFun X Y μ := by
    exact canonicalFirstArrival_indep_futureRenewalCount hrate
  refine ⟨(hX.prodMk hY).aemeasurable, ?_⟩
  calc
    μ.map (fun ω => (X ω, Y ω)) = (μ.map X).prod (μ.map Y) :=
      (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
        hX.aemeasurable hY.aemeasurable).mp hIndep
    _ = (ProbabilityTheory.expMeasure rate).prod ν := by
      rw [show μ.map X = ProbabilityTheory.expMeasure rate by
        simpa only [μ, X, canonicalFirstArrival] using (interarrival_hasLaw hrate 0).map_eq,
        show μ.map Y = ν by
        simpa only [μ, Y, ν, Function.comp_apply] using
          (canonicalRenewalCount_futureInterarrival_hasLaw_poisson hrate ht 1).map_eq]

/--
Atomwise regular conditional law of a post-first-report count, conditional on
the sigma-field generated by the first report time.  The type-level local
probability instance makes the conditional kernel's finite-measure hypothesis
explicit while preserving the positive-rate source model.
-/
theorem canonicalFirstArrival_conditional_futureRenewalCount_atom
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) (k : ℕ) :
    letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
      isProbabilityMeasure_exponentialInterarrivalMeasure hrate
    ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      (ProbabilityTheory.condExpKernel (exponentialInterarrivalMeasure rate)
        (MeasurableSpace.comap canonicalFirstArrival inferInstance) ω).real
          {ω' | canonicalRenewalCount t (futureInterarrival 1 ω') = k} =
        (ProbabilityTheory.poissonMeasure
          (⟨rate * t, mul_nonneg hrate.le ht⟩ : ℝ≥0)).real {k} := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let ν : Measure ℕ := ProbabilityTheory.poissonMeasure
    (⟨rate * t, mul_nonneg hrate.le ht⟩ : ℝ≥0)
  letI : IsProbabilityMeasure μ := by
    simpa only [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  let X : (ℕ → ℝ) → ℝ := canonicalFirstArrival
  let Y : (ℕ → ℝ) → ℕ :=
    fun ω => canonicalRenewalCount t (futureInterarrival 1 ω)
  let A : Set (ℕ → ℝ) := {ω | Y ω = k}
  have hX : Measurable X := by
    simpa only [X, canonicalFirstArrival] using measurable_interarrival 0
  have hY : Measurable Y := by
    simpa only [Y] using (measurable_canonicalRenewalCount t).comp
      (measurable_pi_iff.2 fun j => measurable_futureInterarrival 1 j)
  have hA : @MeasurableSet (ℕ → ℝ) MeasurableSpace.pi A := by
    simpa only [A, Set.preimage_setOf_eq] using hY (measurableSet_singleton k)
  have hA_mY : MeasurableSet[MeasurableSpace.comap Y Nat.instMeasurableSpace] A := by
    simpa only [A, Set.preimage_setOf_eq] using
      (MeasurableSpace.measurableSet_comap.2
        ⟨{k}, measurableSet_singleton k, rfl⟩)
  have hIndep : ProbabilityTheory.IndepFun X Y μ := by
    exact canonicalFirstArrival_indep_futureRenewalCount hrate
  have hIndepYX : ProbabilityTheory.Indep
      (MeasurableSpace.comap Y Nat.instMeasurableSpace)
      (MeasurableSpace.comap X Real.measurableSpace) μ := by
    exact ((ProbabilityTheory.IndepFun_iff_Indep X Y μ).mp hIndep).symm
  have hXle : MeasurableSpace.comap X Real.measurableSpace ≤ MeasurableSpace.pi :=
    hX.comap_le
  have hYle : MeasurableSpace.comap Y Nat.instMeasurableSpace ≤ MeasurableSpace.pi :=
    hY.comap_le
  letI : IsFiniteMeasure (μ.trim hXle) := MeasureTheory.isFiniteMeasure_trim hXle
  have hcond : μ[A.indicator fun _ => (1 : ℝ) |
      MeasurableSpace.comap X Real.measurableSpace] =ᵐ[μ]
      fun _ => ∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂μ := by
    exact MeasureTheory.condExp_indep_eq
      (m₁ := MeasurableSpace.comap Y Nat.instMeasurableSpace)
      (m₂ := MeasurableSpace.comap X Real.measurableSpace)
      (m := MeasurableSpace.pi)
      hYle hXle
      ((measurable_const.indicator hA_mY).stronglyMeasurable) hIndepYX
  have hYlaw : @ProbabilityTheory.HasLaw (ℕ → ℝ) ℕ
      MeasurableSpace.pi Nat.instMeasurableSpace Y ν μ := by
    simpa only [μ, ν, Y, Function.comp_apply] using
      canonicalRenewalCount_futureInterarrival_hasLaw_poisson hrate ht 1
  have hintegral : (∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂μ) = ν.real {k} := by
    rw [integral_indicator hA, setIntegral_const, smul_eq_mul, mul_one]
    calc
      μ.real A = (μ.map Y).real {k} := by
        rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
          Measure.map_apply hY (measurableSet_singleton k)]
        rfl
      _ = ν.real {k} := by rw [hYlaw.map_eq]
  have hcond' : μ[A.indicator fun _ => (1 : ℝ) |
      MeasurableSpace.comap X Real.measurableSpace] =ᵐ[μ]
      fun _ => ν.real {k} :=
    hcond.trans (Filter.Eventually.of_forall fun _ => hintegral)
  have hkernel : (fun ω =>
      (ProbabilityTheory.condExpKernel μ
        (MeasurableSpace.comap X Real.measurableSpace) ω).real A) =ᵐ[μ]
      μ[A.indicator fun _ => (1 : ℝ) |
        MeasurableSpace.comap X Real.measurableSpace] :=
    ProbabilityTheory.condExpKernel_ae_eq_condExp hXle hA
  simpa only [μ, ν, X, Y, A] using hkernel.trans hcond'

/--
Regular conditional Poisson law of the canonical post-first-report count,
given the first report time.  This is a concrete first-report result, not a
claim of a continuous-time strong-Markov theorem at arbitrary stopping times.
-/
theorem canonicalFirstArrival_conditional_futureRenewalCount_hasLaw_poisson
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
      isProbabilityMeasure_exponentialInterarrivalMeasure hrate
    ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      ProbabilityTheory.HasLaw
        (fun ω' : ℕ → ℝ => canonicalRenewalCount t (futureInterarrival 1 ω'))
        (ProbabilityTheory.poissonMeasure
          (⟨rate * t, mul_nonneg hrate.le ht⟩ : ℝ≥0))
        (ProbabilityTheory.condExpKernel (exponentialInterarrivalMeasure rate)
          (MeasurableSpace.comap canonicalFirstArrival inferInstance) ω) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let ν : Measure ℕ := ProbabilityTheory.poissonMeasure
    (⟨rate * t, mul_nonneg hrate.le ht⟩ : ℝ≥0)
  letI : IsProbabilityMeasure μ := by
    simpa only [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  let Y : (ℕ → ℝ) → ℕ :=
    fun ω => canonicalRenewalCount t (futureInterarrival 1 ω)
  have hY : Measurable Y := by
    simpa only [Y] using (measurable_canonicalRenewalCount t).comp
      (measurable_pi_iff.2 fun j => measurable_futureInterarrival 1 j)
  have hatoms : ∀ᵐ ω ∂μ, ∀ k : ℕ,
      (ProbabilityTheory.condExpKernel μ
        (MeasurableSpace.comap canonicalFirstArrival inferInstance) ω).real
          {ω' | Y ω' = k} = ν.real {k} := by
    rw [ae_all_iff]
    intro k
    simpa only [μ, ν, Y] using
      canonicalFirstArrival_conditional_futureRenewalCount_atom hrate ht k
  filter_upwards [hatoms] with ω hω
  refine ⟨hY.aemeasurable, ?_⟩
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  intro k
  rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
    Measure.map_apply hY (measurableSet_singleton k)]
  exact hω k

/--
Conditional no-report probability after the canonical first report.  It is the
first-report specialization of the Poisson residual-waiting statement used in
reporting-process models, stated without extending it to an arbitrary stopping
time.
-/
theorem canonicalFirstArrival_conditional_futureRenewalCount_zero_real
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
      isProbabilityMeasure_exponentialInterarrivalMeasure hrate
    ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      (ProbabilityTheory.condExpKernel (exponentialInterarrivalMeasure rate)
        (MeasurableSpace.comap canonicalFirstArrival inferInstance) ω).real
          {ω' | canonicalRenewalCount t (futureInterarrival 1 ω') = 0} =
        noArrivalProb rate t := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure μ := by
    simpa only [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  filter_upwards [canonicalFirstArrival_conditional_futureRenewalCount_hasLaw_poisson
    hrate ht] with ω hω
  exact hasLaw_poissonMeasure_real_singleton_eq_countLikelihood
    (mul_nonneg hrate.le ht) hω 0 |>.trans
      (noArrivalProb_eq_countLikelihood_zero rate t).symm

end

end AppliedModelingLib.Probability.PoissonProcess
