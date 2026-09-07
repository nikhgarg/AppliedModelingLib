import AppliedModelingLib.Foundations.Probability.PalmTaggedArrivalFiniteLedger
import AppliedModelingLib.Foundations.Probability.ExponentialMarkedRenewalWorkRate

/-!
# Past work rate for a Palm-tagged marked Poisson input

This module identifies the literal marked work of a two-sided Poisson input
before its selected arrival at time zero.  It is an input-process result: no
queue state, service discipline, or response-time claim is made here.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory Filter Finset
open scoped Topology ProbabilityTheory

noncomputable section

/-- Total unit work of the Palm-tagged arrivals in the literal interval
`[-t, 0)`. -/
def palmTaggedPoissonWorkPastAggregate
    (z : (ℤ → ℝ) × (ℤ → ℝ)) (t : ℝ) : ℝ :=
  (palmTaggedArrivalIndices (-t) 0 z.1).sum z.2

/-- The negative-index half of an iid two-sided path is a canonical
one-sided exponential path. -/
theorem candidatePastGapPath_measurePreserving
    {rate : ℝ} (hrate : 0 < rate) :
    MeasurePreserving candidatePastGapPath
      (twoSidedInterarrivalMeasure rate)
      (exponentialInterarrivalMeasure rate) := by
  refine ⟨measurable_pi_iff.2 (fun n => measurable_twoSidedGap (Int.negSucc n)), ?_⟩
  exact (candidatePastGapPath_hasLaw hrate).map_eq

/-- The negative-index half of the independent unit-work path has its
canonical unit-exponential law. -/
theorem candidatePastUnitWorkPath_measurePreserving :
    MeasurePreserving candidatePastGapPath
      (twoSidedInterarrivalMeasure (1 : ℝ))
      (exponentialInterarrivalMeasure 1) :=
  candidatePastGapPath_measurePreserving (by norm_num)

/-- The joint canonical marked input carried by the strict past of a selected
arrival. -/
def candidatePastMarkedInput :
    (ℤ → ℝ) × (ℤ → ℝ) → (ℕ → ℝ) × (ℕ → ℝ) :=
  fun z => (candidatePastGapPath z.1, candidatePastGapPath z.2)

/-- The selected arrival's complete strict past has the independent canonical
marked-renewal product law. -/
theorem candidatePastMarkedInput_measurePreserving
    {rate : ℝ} (hrate : 0 < rate) :
    MeasurePreserving candidatePastMarkedInput
      ((twoSidedInterarrivalMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ)))
      ((exponentialInterarrivalMeasure rate).prod
        (exponentialInterarrivalMeasure (1 : ℝ))) := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  simpa [candidatePastMarkedInput] using
    (candidatePastGapPath_measurePreserving hrate).prod
      candidatePastUnitWorkPath_measurePreserving

/-- On a good tagged gap path, the physical indices in `[-t, 0)` are exactly
the negative labels whose canonical past-renewal epochs have occurred by
`t`. -/
theorem palmTaggedArrivalIndices_neg_to_zero_eq_pastCanonicalIndices
    (g : ℤ → ℝ) (hgood : suspensionGoodGapPath g) (t : ℝ) :
    palmTaggedArrivalIndices (-t) 0 g =
      (Finset.range (canonicalRenewalCount t (candidatePastGapPath g))).image Int.negSucc := by
  classical
  have hpastTend : Tendsto
      (fun n : ℕ => arrivalTime n (candidatePastGapPath g)) atTop atTop := by
    simpa [candidatePastGapPath, suspensionPastPath] using
      suspensionGoodGapPath_past g hgood
  have hpastMono : Monotone
      (fun n : ℕ => arrivalTime n (candidatePastGapPath g)) := by
    apply (arrivalTime_strictMono_of_positive (candidatePastGapPath g) ?_).monotone
    intro n
    exact hgood.1 (Int.negSucc n)
  ext k
  cases k with
  | ofNat n =>
      have hnonnegative : 0 ≤ candidatePalmArrival g (Int.ofNat n) := by
        have hindex : (0 : ℤ) ≤ Int.ofNat n := by
          change 0 ≤ (n : ℤ)
          exact Int.natCast_nonneg _
        simpa [candidatePalmArrival_zero] using
          (suspensionGoodGapPath_strictMono g hgood).monotone hindex
      constructor
      · intro hk
        have hinterval := (mem_palmTaggedArrivalIndices_iff (-t) 0 g hgood
          (Int.ofNat n)).mp hk
        exact (not_lt_of_ge hnonnegative hinterval.2).elim
      · simp
  | negSucc n =>
      have harrival : candidatePalmArrival g (Int.negSucc n) =
          -arrivalTime n (candidatePastGapPath g) := by
        rw [candidatePalmArrival_negSucc]
        exact congrArg Neg.neg (congrFun (candidatePastGapSum_succ_eq_arrivalTime n) g)
      have hbefore : candidatePalmArrival g (Int.negSucc n) < 0 := by
        have hlt : Int.negSucc n < (0 : ℤ) := Int.negSucc_lt_zero n
        simpa [candidatePalmArrival_zero] using
          (suspensionGoodGapPath_strictMono g hgood) hlt
      constructor
      · intro hk
        have hinterval := (mem_palmTaggedArrivalIndices_iff (-t) 0 g hgood
          (Int.negSucc n)).mp hk
        have htime : arrivalTime n (candidatePastGapPath g) ≤ t := by
          rw [harrival] at hinterval
          linarith
        refine Finset.mem_image.mpr ⟨n, ?_, rfl⟩
        simpa [Finset.mem_range] using
          (lt_canonicalRenewalCount_iff_arrivalTime_le_of_tendsto
            (candidatePastGapPath g) hpastTend hpastMono t n).mpr htime
      · intro hk
        rcases Finset.mem_image.mp hk with ⟨m, hm, hmn⟩
        have hmn' : m = n := Int.negSucc.inj hmn
        subst m
        have htime : arrivalTime n (candidatePastGapPath g) ≤ t := by
          exact (lt_canonicalRenewalCount_iff_arrivalTime_le_of_tendsto
            (candidatePastGapPath g) hpastTend hpastMono t n).mp
              (by simpa [Finset.mem_range] using hm)
        apply (mem_palmTaggedArrivalIndices_iff (-t) 0 g hgood
          (Int.negSucc n)).mpr
        rw [harrival]
        constructor <;> linarith

/-- On the good tagged-gap carrier, literal marked work in `[-t, 0)` is the
canonical marked-renewal work of the negative-index arrival and work paths. -/
theorem palmTaggedPoissonWorkPastAggregate_eq_canonicalMarkedWork
    (g work : ℤ → ℝ) (hgood : suspensionGoodGapPath g) (t : ℝ) :
    palmTaggedPoissonWorkPastAggregate (g, work) t =
      canonicalMarkedWork (candidatePastGapPath g) (candidatePastGapPath work) t := by
  unfold palmTaggedPoissonWorkPastAggregate canonicalMarkedWork
  rw [palmTaggedArrivalIndices_neg_to_zero_eq_pastCanonicalIndices g hgood t]
  rw [Finset.sum_image]
  · rfl
  · intro first _ second _ heq
    exact Int.negSucc.inj heq

/-- Finite-horizon work strictly before a selected Poisson arrival is
integrable under the literal Palm gap-and-mark product law.  This is an
input-process calculation: the past ledger is first converted to a canonical
marked renewal prefix and is not treated as a queue-state assertion. -/
theorem integrable_palmTaggedPoissonWorkPastAggregate
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    Integrable (fun z => palmTaggedPoissonWorkPastAggregate z t)
      ((twoSidedInterarrivalMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ))) := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  let F : (ℤ → ℝ) × (ℤ → ℝ) → (ℕ → ℝ) × (ℕ → ℝ) :=
    fun z => (candidatePastGapPath z.1, candidatePastGapPath z.2)
  have hmap : MeasurePreserving F
      ((twoSidedInterarrivalMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ)))
      ((exponentialInterarrivalMeasure rate).prod
        (exponentialInterarrivalMeasure (1 : ℝ))) := by
    simpa [F] using (candidatePastGapPath_measurePreserving hrate).prod
      candidatePastUnitWorkPath_measurePreserving
  have hgood : ∀ᵐ z ∂(twoSidedInterarrivalMeasure rate).prod
      (twoSidedInterarrivalMeasure (1 : ℝ)), suspensionGoodGapPath z.1 := by
    refine ae_of_ae_map
      (μ := (twoSidedInterarrivalMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ)))
      (f := Prod.fst) (p := suspensionGoodGapPath)
      ((measurePreserving_fst : MeasurePreserving Prod.fst
        ((twoSidedInterarrivalMeasure rate).prod
          (twoSidedInterarrivalMeasure (1 : ℝ)))
        (twoSidedInterarrivalMeasure rate)).measurable.aemeasurable) ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact ae_suspensionGoodGapPath hrate
  have hcanonical : Integrable (fun z =>
      canonicalMarkedWork (candidatePastGapPath z.1)
        (candidatePastGapPath z.2) t)
      ((twoSidedInterarrivalMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ))) := by
    simpa [F, Function.comp_def] using
      (hmap.integrable_comp (measurable_canonicalMarkedWork t).aestronglyMeasurable).mpr
        (integrable_canonicalMarkedWork hrate ht)
  refine hcanonical.congr ?_
  filter_upwards [hgood] with z hz
  exact (palmTaggedPoissonWorkPastAggregate_eq_canonicalMarkedWork z.1 z.2 hz t).symm

/-- The expected literal unit work in a finite interval before a selected
Poisson arrival is exactly its Poisson exposure.  Together with the matching
stationary-window theorem, this is a finite input-level Palm equality; it
does not identify any remote-past queue state. -/
theorem integral_palmTaggedPoissonWorkPastAggregate
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    ∫ z, palmTaggedPoissonWorkPastAggregate z t
      ∂(twoSidedInterarrivalMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ)) = rate * t := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  let F : (ℤ → ℝ) × (ℤ → ℝ) → (ℕ → ℝ) × (ℕ → ℝ) :=
    fun z => (candidatePastGapPath z.1, candidatePastGapPath z.2)
  have hmap : MeasurePreserving F
      ((twoSidedInterarrivalMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ)))
      ((exponentialInterarrivalMeasure rate).prod
        (exponentialInterarrivalMeasure (1 : ℝ))) := by
    simpa [F] using (candidatePastGapPath_measurePreserving hrate).prod
      candidatePastUnitWorkPath_measurePreserving
  have hgood : ∀ᵐ z ∂(twoSidedInterarrivalMeasure rate).prod
      (twoSidedInterarrivalMeasure (1 : ℝ)), suspensionGoodGapPath z.1 := by
    refine ae_of_ae_map
      (μ := (twoSidedInterarrivalMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ)))
      (f := Prod.fst) (p := suspensionGoodGapPath)
      ((measurePreserving_fst : MeasurePreserving Prod.fst
        ((twoSidedInterarrivalMeasure rate).prod
          (twoSidedInterarrivalMeasure (1 : ℝ)))
        (twoSidedInterarrivalMeasure rate)).measurable.aemeasurable) ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact ae_suspensionGoodGapPath hrate
  calc
    ∫ z, palmTaggedPoissonWorkPastAggregate z t
        ∂(twoSidedInterarrivalMeasure rate).prod
          (twoSidedInterarrivalMeasure (1 : ℝ)) =
        ∫ z, canonicalMarkedWork (candidatePastGapPath z.1)
          (candidatePastGapPath z.2) t
          ∂(twoSidedInterarrivalMeasure rate).prod
            (twoSidedInterarrivalMeasure (1 : ℝ)) := by
              refine MeasureTheory.integral_congr_ae ?_
              filter_upwards [hgood] with z hz
              exact palmTaggedPoissonWorkPastAggregate_eq_canonicalMarkedWork
                z.1 z.2 hz t
    _ = ∫ y : (ℕ → ℝ) × (ℕ → ℝ), canonicalMarkedWork y.1 y.2 t
          ∂((exponentialInterarrivalMeasure rate).prod
            (exponentialInterarrivalMeasure (1 : ℝ))) := by
              simpa [F, Function.comp_def] using
                hmap.hasLaw.integral_comp
                  (f := fun y : (ℕ → ℝ) × (ℕ → ℝ) =>
                    canonicalMarkedWork y.1 y.2 t)
                  (measurable_canonicalMarkedWork t).aestronglyMeasurable
    _ = rate * t := integral_canonicalMarkedWork hrate ht

/-- Under the literal selected-arrival product law, work arriving before the
tag has almost-sure long-run rate `rate`.  The proof first identifies every
finite physical window with a canonical past renewal sum, so it does not
substitute an unrelated untagged stationary process. -/
theorem ae_tendsto_palmTaggedPoissonWorkPastAggregate_div_atTop
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ z ∂(twoSidedInterarrivalMeasure rate).prod
      (twoSidedInterarrivalMeasure (1 : ℝ)),
      Tendsto (fun t : ℝ => palmTaggedPoissonWorkPastAggregate z t / t)
        atTop (nhds rate) := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  have hcanonical : ∀ᵐ z ∂(twoSidedInterarrivalMeasure rate).prod
      (twoSidedInterarrivalMeasure (1 : ℝ)),
      Tendsto (fun t : ℝ =>
        canonicalMarkedWork (candidatePastGapPath z.1) (candidatePastGapPath z.2) t / t)
        atTop (nhds rate) := by
    exact ae_tendsto_canonicalMarkedWork_div_atTop_of_marginal_measurePreserving
      hrate
      (fun z : (ℤ → ℝ) × (ℤ → ℝ) => candidatePastGapPath z.1)
      (fun z : (ℤ → ℝ) × (ℤ → ℝ) => candidatePastGapPath z.2)
      ((candidatePastGapPath_measurePreserving hrate).comp measurePreserving_fst)
      (candidatePastUnitWorkPath_measurePreserving.comp measurePreserving_snd)
  have hgood : ∀ᵐ z ∂(twoSidedInterarrivalMeasure rate).prod
      (twoSidedInterarrivalMeasure (1 : ℝ)),
      suspensionGoodGapPath z.1 := by
    refine ae_of_ae_map
      (μ := (twoSidedInterarrivalMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ)))
      (f := Prod.fst) (p := suspensionGoodGapPath)
      measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact ae_suspensionGoodGapPath hrate
  filter_upwards [hcanonical, hgood] with z hcanonical hgood
  refine hcanonical.congr' ?_
  filter_upwards [Filter.Eventually.of_forall (fun t : ℝ =>
    (palmTaggedPoissonWorkPastAggregate_eq_canonicalMarkedWork z.1 z.2 hgood t).symm)]
    with t ht
  exact congrArg (fun x : ℝ => x / t) ht

end

end AppliedModelingLib.Probability.PoissonProcess
