import AppliedModelingLib.Foundations.Probability.PalmTaggedArrivalFiniteLedger
import AppliedModelingLib.Foundations.Probability.ExponentialMarkedRenewalWorkRate
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalRenewalCountMarginal

/-!
# Future work rate for a Palm-tagged marked Poisson input

This module identifies the literal marked work arriving strictly after a
selected arrival at time zero and no later than a physical horizon.  The
right-closed convention `(0, t]` is intentional: it is exactly the endpoint
convention of the canonical renewal count used in the rate proof.  This is an
input-process result only; it makes no queue-response or stationarity claim.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory Filter Finset
open scoped Topology ProbabilityTheory NNReal

noncomputable section

/-- Total unit work of the Palm-tagged arrivals in the literal interval
`(0, t]`.  The tag at zero is excluded. -/
def palmTaggedPoissonWorkFutureAggregate
    (z : (ℤ → ℝ) × (ℤ → ℝ)) (t : ℝ) : ℝ :=
  (palmTaggedArrivalIndicesRightClosed 0 t z.1).sum z.2

/-- The number of Palm-tagged arrivals strictly after the tag and no later
than `t`, represented by the canonical renewal count of the future gap path.
The corresponding finite-ledger cardinality is identified below on good
two-sided paths. -/
def palmTaggedPoissonFutureCount (g : ℤ → ℝ) (t : ℝ) : ℕ :=
  canonicalRenewalCount t (candidateFutureGapPath g)

/-- The Palm-tagged future arrival count has the exact fixed-time Poisson
law.  This follows by transporting the canonical count marginal through the
actual future half of the tagged gap path. -/
theorem palmTaggedPoissonFutureCount_hasLaw_poisson
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    ProbabilityTheory.HasLaw (fun g : ℤ → ℝ => palmTaggedPoissonFutureCount g t)
      (ProbabilityTheory.poissonMeasure
        (⟨rate * t, mul_nonneg hrate.le ht⟩ : ℝ≥0))
      (twoSidedInterarrivalMeasure rate) := by
  simpa [palmTaggedPoissonFutureCount] using
    (canonicalRenewalCount_hasLaw_poisson hrate ht).comp
      (candidateFutureGapPath_hasLaw hrate)

/-- The expected Palm-tagged future arrival count is `rate * t`. -/
theorem integral_palmTaggedPoissonFutureCount
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    ∫ g : ℤ → ℝ, (palmTaggedPoissonFutureCount g t : ℝ)
      ∂twoSidedInterarrivalMeasure rate = rate * t := by
  let r : ℝ≥0 := ⟨rate * t, mul_nonneg hrate.le ht⟩
  calc
    ∫ g : ℤ → ℝ, (palmTaggedPoissonFutureCount g t : ℝ)
        ∂twoSidedInterarrivalMeasure rate =
        ∫ n : ℕ, (n : ℝ) ∂ProbabilityTheory.poissonMeasure r := by
          simpa [r, Function.comp_def] using
            (palmTaggedPoissonFutureCount_hasLaw_poisson hrate ht).integral_comp
              (f := fun n : ℕ => (n : ℝ))
              (measurable_of_countable _).aestronglyMeasurable
    _ = r := integral_id_poissonMeasure r
    _ = rate * t := rfl

/-- The future work marks are shifted by one label because the first positive
arrival is label `1`, while the canonical renewal path starts at index `0`. -/
def candidateFutureUnitWorkPath : (ℤ → ℝ) → ℕ → ℝ :=
  fun work n => twoSidedGap (Int.ofNat (n + 1)) work

/-- The future gap half of a tagged path has the canonical exponential law. -/
theorem candidateFutureGapPath_measurePreserving
    {rate : ℝ} (hrate : 0 < rate) :
    MeasurePreserving candidateFutureGapPath
      (twoSidedInterarrivalMeasure rate)
      (exponentialInterarrivalMeasure rate) := by
  refine ⟨measurable_pi_iff.2 (fun n => measurable_twoSidedGap (Int.ofNat n)), ?_⟩
  exact (candidateFutureGapPath_hasLaw hrate).map_eq

/-- The shifted positive-index work marks still form a canonical iid
unit-exponential path. -/
theorem iIndepFun_candidateFutureUnitWorkPath :
    ProbabilityTheory.iIndepFun (fun n work => candidateFutureUnitWorkPath work n)
      (twoSidedInterarrivalMeasure (1 : ℝ)) := by
  simpa [candidateFutureUnitWorkPath] using
    (ProbabilityTheory.iIndepFun.precomp (g := fun n : ℕ => Int.ofNat (n + 1))
      (by
        intro a b hab
        exact Nat.add_right_cancel (Int.ofNat.inj hab))
      (iIndepFun_twoSidedGap (by norm_num : 0 < (1 : ℝ))))

theorem candidateFutureUnitWorkPath_hasLaw :
    ProbabilityTheory.HasLaw candidateFutureUnitWorkPath
      (exponentialInterarrivalMeasure (1 : ℝ))
      (twoSidedInterarrivalMeasure (1 : ℝ)) := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  refine ⟨(measurable_pi_iff.2
    (fun n => measurable_twoSidedGap (Int.ofNat (n + 1)))).aemeasurable, ?_⟩
  change Measure.map (fun work n => twoSidedGap (Int.ofNat (n + 1)) work)
    (twoSidedInterarrivalMeasure (1 : ℝ)) = exponentialInterarrivalMeasure 1
  rw [ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun n => measurable_twoSidedGap (Int.ofNat (n + 1)) ) |>.mp
    iIndepFun_candidateFutureUnitWorkPath]
  simp only [exponentialInterarrivalMeasure]
  congr 1
  funext n
  exact (twoSidedGap_hasLaw (by norm_num : 0 < (1 : ℝ))
    (Int.ofNat (n + 1))).map_eq

theorem candidateFutureUnitWorkPath_measurePreserving :
    MeasurePreserving candidateFutureUnitWorkPath
      (twoSidedInterarrivalMeasure (1 : ℝ))
      (exponentialInterarrivalMeasure (1 : ℝ)) := by
  refine ⟨measurable_pi_iff.2
    (fun n => measurable_twoSidedGap (Int.ofNat (n + 1))), ?_⟩
  exact candidateFutureUnitWorkPath_hasLaw.map_eq

/-- On a good tagged gap path, physical positive labels in `(0, t]` are
exactly the canonical future-renewal labels, shifted by one. -/
theorem palmTaggedArrivalIndices_zero_to_eq_eq_futureCanonicalIndices
    (g : ℤ → ℝ) (hgood : suspensionGoodGapPath g) (t : ℝ) :
    palmTaggedArrivalIndicesRightClosed 0 t g =
      (Finset.range (canonicalRenewalCount t (candidateFutureGapPath g))).image
        (fun n => Int.ofNat (n + 1)) := by
  classical
  have hfutureTend : Tendsto
      (fun n : ℕ => arrivalTime n (candidateFutureGapPath g)) atTop atTop := by
    simpa [candidateFutureGapPath, suspensionFuturePath] using
      suspensionGoodGapPath_future g hgood
  have hfutureMono : Monotone
      (fun n : ℕ => arrivalTime n (candidateFutureGapPath g)) := by
    apply (arrivalTime_strictMono_of_positive (candidateFutureGapPath g) ?_).monotone
    intro n
    exact hgood.1 (Int.ofNat n)
  ext k
  cases k with
  | ofNat n =>
      cases n with
      | zero =>
          constructor
          · intro hk
            have hinterval := (mem_palmTaggedArrivalIndicesRightClosed_iff 0 t g hgood 0).mp hk
            simpa [candidatePalmArrival_zero] using hinterval.1
          · intro hk
            rcases Finset.mem_image.mp hk with ⟨m, hm, hmzero⟩
            have hpositive : (0 : ℤ) < Int.ofNat (m + 1) := by
              change (0 : ℤ) < ((m + 1 : ℕ) : ℤ)
              exact_mod_cast Nat.zero_lt_succ m
            have hmzero' : Int.ofNat (m + 1) = 0 := by
              simpa using hmzero
            linarith
      | succ n =>
          have harrival : candidatePalmArrival g (Int.ofNat (n + 1)) =
              arrivalTime n (candidateFutureGapPath g) := by
            rw [candidatePalmArrival_ofNat]
            exact congrFun (candidateFutureEpoch_succ_eq_arrivalTime n) g
          have hpositive : 0 < candidatePalmArrival g (Int.ofNat (n + 1)) := by
            have hindex : (0 : ℤ) < Int.ofNat (n + 1) := by
              change (0 : ℤ) < ((n + 1 : ℕ) : ℤ)
              exact_mod_cast Nat.zero_lt_succ n
            simpa [candidatePalmArrival_zero] using
              (suspensionGoodGapPath_strictMono g hgood) hindex
          constructor
          · intro hk
            have hinterval := (mem_palmTaggedArrivalIndicesRightClosed_iff 0 t g hgood
              (Int.ofNat (n + 1))).mp hk
            refine Finset.mem_image.mpr ⟨n, ?_, rfl⟩
            simpa [Finset.mem_range] using
              (lt_canonicalRenewalCount_iff_arrivalTime_le_of_tendsto
                (candidateFutureGapPath g) hfutureTend hfutureMono t n).mpr
                (by simpa [harrival] using hinterval.2)
          · intro hk
            rcases Finset.mem_image.mp hk with ⟨m, hm, hmn⟩
            have hmn' : m = n := Nat.add_right_cancel (Int.ofNat.inj hmn)
            subst m
            apply (mem_palmTaggedArrivalIndicesRightClosed_iff 0 t g hgood
              (Int.ofNat (n + 1))).mpr
            rw [harrival]
            constructor
            · exact hpositive
            · exact (lt_canonicalRenewalCount_iff_arrivalTime_le_of_tendsto
                (candidateFutureGapPath g) hfutureTend hfutureMono t n).mp
                (by simpa [Finset.mem_range] using hm)
  | negSucc n =>
      have hbefore : candidatePalmArrival g (Int.negSucc n) < 0 := by
        have hlt : Int.negSucc n < (0 : ℤ) := Int.negSucc_lt_zero n
        simpa [candidatePalmArrival_zero] using
          (suspensionGoodGapPath_strictMono g hgood) hlt
      constructor
      · intro hk
        have hinterval := (mem_palmTaggedArrivalIndicesRightClosed_iff 0 t g hgood
          (Int.negSucc n)).mp hk
        linarith
      · intro hk
        rcases Finset.mem_image.mp hk with ⟨m, hm, hmn⟩
        have hnonnegative : 0 ≤ Int.ofNat (m + 1) := by
          change 0 ≤ ((m + 1 : ℕ) : ℤ)
          exact Int.natCast_nonneg _
        have hnegative : Int.negSucc n < 0 := Int.negSucc_lt_zero n
        linarith

/-- On a good Palm-tagged gap path, the literal right-closed future ledger
has exactly its canonical renewal-count cardinality. -/
theorem palmTaggedArrivalIndicesRightClosed_zero_card_eq_futureCount
    (g : ℤ → ℝ) (hgood : suspensionGoodGapPath g) (t : ℝ) :
    (palmTaggedArrivalIndicesRightClosed 0 t g).card =
      palmTaggedPoissonFutureCount g t := by
  rw [palmTaggedArrivalIndices_zero_to_eq_eq_futureCanonicalIndices g hgood t,
    Finset.card_image_of_injective]
  · simp [palmTaggedPoissonFutureCount]
  · intro a b hab
    apply Nat.succ.inj
    apply Int.ofNat.inj
    simpa using hab

/-- Literal marked work arriving after the tag and no later than `t` is the
canonical marked-renewal work of the future gap and shifted-mark paths. -/
theorem palmTaggedPoissonWorkFutureAggregate_eq_canonicalMarkedWork
    (g work : ℤ → ℝ) (hgood : suspensionGoodGapPath g) (t : ℝ) :
    palmTaggedPoissonWorkFutureAggregate (g, work) t =
      canonicalMarkedWork (candidateFutureGapPath g)
        (candidateFutureUnitWorkPath work) t := by
  unfold palmTaggedPoissonWorkFutureAggregate canonicalMarkedWork
  rw [palmTaggedArrivalIndices_zero_to_eq_eq_futureCanonicalIndices g hgood t]
  rw [Finset.sum_image]
  · rfl
  · intro first _ second _ heq
    exact Nat.add_right_cancel (Int.ofNat.inj heq)

/-- Finite-horizon Palm-tagged future work is integrable under the literal
two-sided gap and independent mark product. -/
theorem integrable_palmTaggedPoissonWorkFutureAggregate
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    Integrable (fun z => palmTaggedPoissonWorkFutureAggregate z t)
      ((twoSidedInterarrivalMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ))) := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  let F : (ℤ → ℝ) × (ℤ → ℝ) -> (ℕ → ℝ) × (ℕ → ℝ) :=
    fun z => (candidateFutureGapPath z.1, candidateFutureUnitWorkPath z.2)
  have hmap : MeasurePreserving F
      ((twoSidedInterarrivalMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ)))
      ((exponentialInterarrivalMeasure rate).prod
        (exponentialInterarrivalMeasure (1 : ℝ))) := by
    simpa [F] using (candidateFutureGapPath_measurePreserving hrate).prod
      candidateFutureUnitWorkPath_measurePreserving
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
      canonicalMarkedWork (candidateFutureGapPath z.1)
        (candidateFutureUnitWorkPath z.2) t)
      ((twoSidedInterarrivalMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ))) := by
    simpa [F, Function.comp_def] using
      (hmap.integrable_comp (measurable_canonicalMarkedWork t).aestronglyMeasurable).mpr
        (integrable_canonicalMarkedWork hrate ht)
  refine hcanonical.congr ?_
  filter_upwards [hgood] with z hz
  exact (palmTaggedPoissonWorkFutureAggregate_eq_canonicalMarkedWork z.1 z.2 hz t).symm

/-- Under the literal Palm-tagged gap and independent mark product, the
expected work arriving in the finite physical window `(0,t]` is `rate * t`.
The proof first identifies the actual finite ledger with the canonical future
renewal sum, then transports the concrete product law into the marked-renewal
calculation. -/
theorem integral_palmTaggedPoissonWorkFutureAggregate
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    ∫ z, palmTaggedPoissonWorkFutureAggregate z t
      ∂(twoSidedInterarrivalMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ)) = rate * t := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  let F : (ℤ → ℝ) × (ℤ → ℝ) -> (ℕ → ℝ) × (ℕ → ℝ) :=
    fun z => (candidateFutureGapPath z.1, candidateFutureUnitWorkPath z.2)
  have hmap : MeasurePreserving F
      ((twoSidedInterarrivalMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ)))
      ((exponentialInterarrivalMeasure rate).prod
        (exponentialInterarrivalMeasure (1 : ℝ))) := by
    simpa [F] using (candidateFutureGapPath_measurePreserving hrate).prod
      candidateFutureUnitWorkPath_measurePreserving
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
    ∫ z, palmTaggedPoissonWorkFutureAggregate z t
        ∂(twoSidedInterarrivalMeasure rate).prod
          (twoSidedInterarrivalMeasure (1 : ℝ)) =
        ∫ z, canonicalMarkedWork (candidateFutureGapPath z.1)
          (candidateFutureUnitWorkPath z.2) t
          ∂(twoSidedInterarrivalMeasure rate).prod
            (twoSidedInterarrivalMeasure (1 : ℝ)) := by
              refine MeasureTheory.integral_congr_ae ?_
              filter_upwards [hgood] with z hz
              exact palmTaggedPoissonWorkFutureAggregate_eq_canonicalMarkedWork
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

/-- Under the literal selected-arrival product law, marked work arriving
strictly after the tag has almost-sure long-run rate `rate`.  Every finite
right-closed physical window is first identified with its canonical renewal
sum, so the proof stays on the selected Palm input rather than substituting
an unrelated forward process. -/
theorem ae_tendsto_palmTaggedPoissonWorkFutureAggregate_div_atTop
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ z ∂(twoSidedInterarrivalMeasure rate).prod
      (twoSidedInterarrivalMeasure (1 : ℝ)),
      Tendsto (fun t : ℝ => palmTaggedPoissonWorkFutureAggregate z t / t)
        atTop (nhds rate) := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  have hcanonical : ∀ᵐ z ∂(twoSidedInterarrivalMeasure rate).prod
      (twoSidedInterarrivalMeasure (1 : ℝ)),
      Tendsto (fun t : ℝ =>
        canonicalMarkedWork (candidateFutureGapPath z.1)
          (candidateFutureUnitWorkPath z.2) t / t)
        atTop (nhds rate) := by
    exact ae_tendsto_canonicalMarkedWork_div_atTop_of_marginal_measurePreserving
      hrate
      (fun z : (ℤ → ℝ) × (ℤ → ℝ) => candidateFutureGapPath z.1)
      (fun z : (ℤ → ℝ) × (ℤ → ℝ) => candidateFutureUnitWorkPath z.2)
      ((candidateFutureGapPath_measurePreserving hrate).comp measurePreserving_fst)
      (candidateFutureUnitWorkPath_measurePreserving.comp measurePreserving_snd)
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
    (palmTaggedPoissonWorkFutureAggregate_eq_canonicalMarkedWork z.1 z.2 hgood t).symm)]
    with t ht
  exact congrArg (fun x : ℝ => x / t) ht

end

end AppliedModelingLib.Probability.PoissonProcess
