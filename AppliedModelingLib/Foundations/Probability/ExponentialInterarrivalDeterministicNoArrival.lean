import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalIncrementBoundary

/-!
# Deterministic-clock no-arrival tail for canonical exponential renewals

This module proves the exact probability of no canonical renewal in a fixed
increment after an arbitrary deterministic nonnegative clock time.  The proof
does not assume a residual-tail or strong-Markov certificate: it factors the
event at each possible straddling interarrival and then sums the count fibers
on the almost-sure positive, nonexplosive carrier.

It is deliberately a zero-increment result.  A full deterministic-increment
Poisson law and a random/stopping-time theorem require further work.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory Filter
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

private theorem expMeasure_residual_tail
    {rate elapsed future : ℝ} (hrate : 0 < rate)
    (helapsed : 0 ≤ elapsed) (hfuture : 0 ≤ future) :
    ProbabilityTheory.expMeasure rate
        {x : ℝ | elapsed < x ∧ future < x - elapsed} =
      ProbabilityTheory.expMeasure rate (Set.Ioi elapsed) *
        ProbabilityTheory.expMeasure rate (Set.Ioi future) := by
  let M : Exponential.Model := ⟨rate, hrate⟩
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure rate) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).mp
  simpa only [ENNReal.toReal_mul, M, Exponential.Model.measure] using
    M.measure_residual_tail_toReal helapsed hfuture

/-- Slice-level exponential memorylessness for a possible renewal-prefix
clock value. -/
private theorem futureFirst_slice_noArrival_factorization
    {rate s h a : ℝ} (hrate : 0 < rate) (hh : 0 ≤ h) :
    exponentialInterarrivalMeasure rate
        {ξ | a ≤ s ∧ s + h < a + interarrival 0 ξ} =
      ProbabilityTheory.expMeasure rate (Set.Ioi h) *
        exponentialInterarrivalMeasure rate
          {ξ | a ≤ s ∧ s < a + interarrival 0 ξ} := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let X : (ℕ → ℝ) → ℝ := interarrival 0
  let e : ℝ := s - a
  letI : IsProbabilityMeasure μ := by
    simpa only [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hmap : μ.map X = ProbabilityTheory.expMeasure rate := by
    simpa only [μ, X] using (interarrival_hasLaw hrate 0).map_eq
  by_cases ha : a ≤ s
  · have he : 0 ≤ e := by
      dsimp [e]
      linarith
    let A : Set ℝ := {x | e < x ∧ h < x - e}
    let B : Set ℝ := Set.Ioi e
    have hA : MeasurableSet A := by
      exact (measurableSet_lt measurable_const measurable_id).inter
        (measurableSet_lt measurable_const (measurable_id.sub_const e))
    have hB : MeasurableSet B := measurableSet_Ioi
    have hleft : {ξ | a ≤ s ∧ s + h < a + X ξ} = X ⁻¹' A := by
      ext ξ
      simp only [Set.mem_setOf_eq, Set.mem_preimage, A]
      constructor <;> intro hξ
      · constructor <;> dsimp [e] <;> linarith [hξ.2]
      · constructor
        · exact ha
        · dsimp [e] at hξ
          linarith [hξ.1, hξ.2]
    have hright : {ξ | a ≤ s ∧ s < a + X ξ} = X ⁻¹' B := by
      ext ξ
      simp only [Set.mem_setOf_eq, Set.mem_preimage, B, Set.mem_Ioi]
      constructor <;> intro hξ
      · dsimp [e]
        linarith [hξ.2]
      · constructor
        · exact ha
        · dsimp [e] at hξ
          linarith
    rw [show exponentialInterarrivalMeasure rate = μ by rfl, hleft, hright]
    calc
      μ (X ⁻¹' A) = (ProbabilityTheory.expMeasure rate) A := by
        rw [← hmap]
        exact (Measure.map_apply (measurable_interarrival 0) hA).symm
      _ = (ProbabilityTheory.expMeasure rate) (Set.Ioi h) *
          (ProbabilityTheory.expMeasure rate) B := by
        calc
          (ProbabilityTheory.expMeasure rate) A =
              (ProbabilityTheory.expMeasure rate) (Set.Ioi e) *
                (ProbabilityTheory.expMeasure rate) (Set.Ioi h) := by
              rw [show A = {x : ℝ | e < x ∧ h < x - e} by rfl,
                expMeasure_residual_tail hrate he hh]
          _ = (ProbabilityTheory.expMeasure rate) (Set.Ioi h) *
                (ProbabilityTheory.expMeasure rate) (Set.Ioi e) := by
              ac_rfl
          _ = (ProbabilityTheory.expMeasure rate) (Set.Ioi h) *
                (ProbabilityTheory.expMeasure rate) B := by
              rfl
      _ = (ProbabilityTheory.expMeasure rate) (Set.Ioi h) * μ (X ⁻¹' B) := by
        congr 1
        rw [← hmap]
        exact Measure.map_apply (measurable_interarrival 0) hB
  · have hleft_empty : {ξ | a ≤ s ∧ s + h < a + X ξ} = ∅ := by
      ext ξ
      simp [ha]
    have hright_empty : {ξ | a ≤ s ∧ s < a + X ξ} = ∅ := by
      ext ξ
      simp [ha]
    change μ {ξ | a ≤ s ∧ s + h < a + X ξ} =
      ProbabilityTheory.expMeasure rate (Set.Ioi h) *
        μ {ξ | a ≤ s ∧ s < a + X ξ}
    rw [hleft_empty, hright_empty]
    simp

private def fixedStraddleEvent (s : ℝ) (n : ℕ) : Set (ℕ → ℝ) :=
  {ω | arrivalPrefix n ω ≤ s ∧ s < arrivalTime n ω}

private def fixedStraddleNoArrivalEvent (s h : ℝ) (n : ℕ) : Set (ℕ → ℝ) :=
  {ω | arrivalPrefix n ω ≤ s ∧ s + h < arrivalTime n ω}

private theorem measurableSet_fixedStraddleEvent (s : ℝ) (n : ℕ) :
    MeasurableSet (fixedStraddleEvent s n) := by
  exact (measurableSet_le (measurable_arrivalPrefix n) measurable_const).inter
    (measurableSet_lt measurable_const (measurable_arrivalTime n))

private theorem measurableSet_fixedStraddleNoArrivalEvent (s h : ℝ) (n : ℕ) :
    MeasurableSet (fixedStraddleNoArrivalEvent s h n) := by
  exact (measurableSet_le (measurable_arrivalPrefix n) measurable_const).inter
    (measurableSet_lt (measurable_const.add_const h) (measurable_arrivalTime n))

private theorem arrivalPrefix_futureInterarrival_hasLaw_prod
    {rate : ℝ} (hrate : 0 < rate) (n : ℕ) :
    ProbabilityTheory.HasLaw
      (fun ω : ℕ → ℝ => (arrivalPrefix n ω, futureInterarrival n ω))
      ((Measure.map (arrivalPrefix n) (exponentialInterarrivalMeasure rate)).prod
        (exponentialInterarrivalMeasure rate))
      (exponentialInterarrivalMeasure rate) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let X : (ℕ → ℝ) → ℝ := arrivalPrefix n
  let Y : (ℕ → ℝ) → (ℕ → ℝ) := futureInterarrival n
  letI : IsProbabilityMeasure μ := by
    simpa only [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hX : Measurable X := by
    simpa only [X] using measurable_arrivalPrefix n
  have hY : Measurable Y := by
    simpa only [Y] using measurable_pi_iff.2 (fun k => measurable_futureInterarrival n k)
  have hIndep : ProbabilityTheory.IndepFun X Y μ := by
    simpa only [μ, X, Y] using arrivalPrefix_indep_futureInterarrival hrate n
  refine ⟨(hX.prodMk hY).aemeasurable, ?_⟩
  have htail : μ.map Y = μ := by
    simpa only [μ, Y] using (futureInterarrival_hasLaw_path hrate n).map_eq
  calc
    μ.map (fun ω => (X ω, Y ω)) = (μ.map X).prod (μ.map Y) :=
      (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
        hX.aemeasurable hY.aemeasurable).mp hIndep
    _ = (μ.map X).prod μ := by rw [htail]

private def straddleProductSet (s : ℝ) : Set (ℝ × (ℕ → ℝ)) :=
  {p | p.1 ≤ s ∧ s < p.1 + interarrival 0 p.2}

private def straddleNoArrivalProductSet (s h : ℝ) : Set (ℝ × (ℕ → ℝ)) :=
  {p | p.1 ≤ s ∧ s + h < p.1 + interarrival 0 p.2}

private theorem measurableSet_straddleProductSet (s : ℝ) :
    MeasurableSet (straddleProductSet s) := by
  exact (measurableSet_le measurable_fst measurable_const).inter
    (measurableSet_lt measurable_const
      (measurable_fst.add ((measurable_interarrival 0).comp measurable_snd)))

private theorem measurableSet_straddleNoArrivalProductSet (s h : ℝ) :
    MeasurableSet (straddleNoArrivalProductSet s h) := by
  exact (measurableSet_le measurable_fst measurable_const).inter
    (measurableSet_lt (measurable_const.add_const h)
      (measurable_fst.add ((measurable_interarrival 0).comp measurable_snd)))

private theorem product_straddleNoArrival_factorization
    {rate : ℝ} (hrate : 0 < rate) (s h : ℝ) (hh : 0 ≤ h)
    (ν : Measure ℝ) :
    (ν.prod (exponentialInterarrivalMeasure rate))
        (straddleNoArrivalProductSet s h) =
      ProbabilityTheory.expMeasure rate (Set.Ioi h) *
        (ν.prod (exponentialInterarrivalMeasure rate)) (straddleProductSet s) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure μ := by
    simpa only [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure rate) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  change (ν.prod μ) (straddleNoArrivalProductSet s h) =
    ProbabilityTheory.expMeasure rate (Set.Ioi h) *
      (ν.prod μ) (straddleProductSet s)
  have hslice (a : ℝ) :
      μ (Prod.mk a ⁻¹' straddleNoArrivalProductSet s h) =
        ProbabilityTheory.expMeasure rate (Set.Ioi h) *
          μ (Prod.mk a ⁻¹' straddleProductSet s) := by
    change μ {ξ | a ≤ s ∧ s + h < a + interarrival 0 ξ} =
      ProbabilityTheory.expMeasure rate (Set.Ioi h) *
        μ {ξ | a ≤ s ∧ s < a + interarrival 0 ξ}
    exact futureFirst_slice_noArrival_factorization hrate hh
  rw [Measure.prod_apply (measurableSet_straddleNoArrivalProductSet s h),
    Measure.prod_apply (measurableSet_straddleProductSet s)]
  calc
    ∫⁻ a, μ (Prod.mk a ⁻¹' straddleNoArrivalProductSet s h) ∂ν =
        ∫⁻ a, ProbabilityTheory.expMeasure rate (Set.Ioi h) *
          μ (Prod.mk a ⁻¹' straddleProductSet s) ∂ν := by
            exact lintegral_congr hslice
    _ = ProbabilityTheory.expMeasure rate (Set.Ioi h) *
          ∫⁻ a, μ (Prod.mk a ⁻¹' straddleProductSet s) ∂ν := by
            exact lintegral_const_mul' _ _ (measure_ne_top _ _)

private theorem measure_fixedStraddleEvent_eq_product
    {rate : ℝ} (hrate : 0 < rate) (s : ℝ) (n : ℕ) :
    exponentialInterarrivalMeasure rate (fixedStraddleEvent s n) =
      ((Measure.map (arrivalPrefix n) (exponentialInterarrivalMeasure rate)).prod
        (exponentialInterarrivalMeasure rate)) (straddleProductSet s) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let f : (ℕ → ℝ) → ℝ × (ℕ → ℝ) :=
    fun ω => (arrivalPrefix n ω, futureInterarrival n ω)
  have hf : Measurable f := by
    exact (measurable_arrivalPrefix n).prodMk
      (measurable_pi_iff.2 fun k => measurable_futureInterarrival n k)
  have hpreimage : f ⁻¹' straddleProductSet s = fixedStraddleEvent s n := by
    ext ω
    simp only [f, straddleProductSet, Set.mem_preimage, Set.mem_setOf_eq]
    have htail : interarrival 0 (futureInterarrival n ω) = interarrival n ω := by
      rfl
    rw [htail]
    simp [fixedStraddleEvent, arrivalTime, arrivalPrefix, Finset.sum_range_succ]
  calc
    μ (fixedStraddleEvent s n) = μ (f ⁻¹' straddleProductSet s) := by
      rw [hpreimage]
    _ = (Measure.map f μ) (straddleProductSet s) := by
      symm
      exact Measure.map_apply hf (measurableSet_straddleProductSet s)
    _ = ((Measure.map (arrivalPrefix n) μ).prod μ) (straddleProductSet s) := by
      rw [(arrivalPrefix_futureInterarrival_hasLaw_prod hrate n).map_eq]

private theorem measure_fixedStraddleNoArrivalEvent_eq_product
    {rate : ℝ} (hrate : 0 < rate) (s h : ℝ) (n : ℕ) :
    exponentialInterarrivalMeasure rate (fixedStraddleNoArrivalEvent s h n) =
      ((Measure.map (arrivalPrefix n) (exponentialInterarrivalMeasure rate)).prod
        (exponentialInterarrivalMeasure rate)) (straddleNoArrivalProductSet s h) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let f : (ℕ → ℝ) → ℝ × (ℕ → ℝ) :=
    fun ω => (arrivalPrefix n ω, futureInterarrival n ω)
  have hf : Measurable f := by
    exact (measurable_arrivalPrefix n).prodMk
      (measurable_pi_iff.2 fun k => measurable_futureInterarrival n k)
  have hpreimage : f ⁻¹' straddleNoArrivalProductSet s h =
      fixedStraddleNoArrivalEvent s h n := by
    ext ω
    simp only [f, straddleNoArrivalProductSet, Set.mem_preimage, Set.mem_setOf_eq]
    have htail : interarrival 0 (futureInterarrival n ω) = interarrival n ω := by
      rfl
    rw [htail]
    simp [fixedStraddleNoArrivalEvent, arrivalTime, arrivalPrefix,
      Finset.sum_range_succ]
  calc
    μ (fixedStraddleNoArrivalEvent s h n) =
        μ (f ⁻¹' straddleNoArrivalProductSet s h) := by
          rw [hpreimage]
    _ = (Measure.map f μ) (straddleNoArrivalProductSet s h) := by
      symm
      exact Measure.map_apply hf (measurableSet_straddleNoArrivalProductSet s h)
    _ = ((Measure.map (arrivalPrefix n) μ).prod μ)
        (straddleNoArrivalProductSet s h) := by
          rw [(arrivalPrefix_futureInterarrival_hasLaw_prod hrate n).map_eq]

private theorem measure_fixedStraddleNoArrivalEvent_factorization
    {rate : ℝ} (hrate : 0 < rate) (s h : ℝ) (hh : 0 ≤ h) (n : ℕ) :
    exponentialInterarrivalMeasure rate (fixedStraddleNoArrivalEvent s h n) =
      ProbabilityTheory.expMeasure rate (Set.Ioi h) *
        exponentialInterarrivalMeasure rate (fixedStraddleEvent s n) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let ν : Measure ℝ := μ.map (arrivalPrefix n)
  calc
    μ (fixedStraddleNoArrivalEvent s h n) =
        (ν.prod μ) (straddleNoArrivalProductSet s h) := by
          simpa only [μ, ν] using
            measure_fixedStraddleNoArrivalEvent_eq_product hrate s h n
    _ = ProbabilityTheory.expMeasure rate (Set.Ioi h) *
        (ν.prod μ) (straddleProductSet s) := by
          exact product_straddleNoArrival_factorization hrate s h hh ν
    _ = ProbabilityTheory.expMeasure rate (Set.Ioi h) *
        μ (fixedStraddleEvent s n) := by
          congr 1
          simpa only [μ, ν] using
            (measure_fixedStraddleEvent_eq_product hrate s n).symm

private theorem fixedStraddleEvent_iff_canonicalRenewalCount_eq
    (s : ℝ) (hs : 0 ≤ s) (ω : ℕ → ℝ)
    (hdiv : Tendsto (fun n : ℕ => arrivalTime n ω) atTop atTop)
    (hpos : ∀ i : ℕ, 0 < interarrival i ω) (n : ℕ) :
    fixedStraddleEvent s n ω ↔ canonicalRenewalCount s ω = n := by
  cases n with
  | zero =>
      constructor
      · intro h
        rw [canonicalRenewalCount_eq_zero_iff]
        exact Or.inl h.2
      · intro h
        rw [canonicalRenewalCount_eq_zero_iff] at h
        rcases h with h | h
        · exact ⟨by simp [arrivalPrefix, hs], h⟩
        · exact (h (exists_arrivalTime_gt_of_tendsto_atTop ω hdiv s)).elim
  | succ n =>
      constructor
      · rintro ⟨hpref, hupper⟩
        apply (canonicalRenewalCount_eq_succ_iff s ω n).mpr
        refine ⟨hupper, ?_⟩
        intro m hm hsm
        have hle : arrivalTime m ω ≤ arrivalTime n ω :=
          (arrivalTime_strictMono_of_positive ω hpos).monotone
            (Nat.le_of_lt_succ hm)
        have hpref' : arrivalTime n ω ≤ s := by
          simpa [fixedStraddleEvent, arrivalPrefix] using hpref
        exact (not_lt_of_ge (hle.trans hpref')) hsm
      · intro h
        rw [canonicalRenewalCount_eq_succ_iff] at h
        rcases h with ⟨hupper, hbefore⟩
        constructor
        · have hnot : ¬ s < arrivalTime n ω :=
            hbefore n (Nat.lt_succ_self n)
          simpa [fixedStraddleEvent, arrivalPrefix] using le_of_not_gt hnot
        · exact hupper

private theorem fixedStraddleNoArrivalEvent_iff_countFibers
    (s h : ℝ) (hs : 0 ≤ s) (hh : 0 ≤ h) (ω : ℕ → ℝ)
    (hdiv : Tendsto (fun n : ℕ => arrivalTime n ω) atTop atTop)
    (hpos : ∀ i : ℕ, 0 < interarrival i ω) (n : ℕ) :
    fixedStraddleNoArrivalEvent s h n ω ↔
      canonicalRenewalCount s ω = n ∧ canonicalRenewalCount (s + h) ω = n := by
  have hs' : 0 ≤ s + h := add_nonneg hs hh
  have hstraddle :
      fixedStraddleNoArrivalEvent s h n ω ↔
        fixedStraddleEvent s n ω ∧ fixedStraddleEvent (s + h) n ω := by
    constructor
    · rintro ⟨hpref, hupper⟩
      constructor
      · exact ⟨hpref, lt_of_le_of_lt (le_add_of_nonneg_right hh) hupper⟩
      · exact ⟨le_trans hpref (le_add_of_nonneg_right hh), hupper⟩
    · rintro ⟨hleft, hright⟩
      exact ⟨hleft.1, hright.2⟩
  rw [hstraddle,
    fixedStraddleEvent_iff_canonicalRenewalCount_eq s hs ω hdiv hpos n,
    fixedStraddleEvent_iff_canonicalRenewalCount_eq (s + h) hs' ω hdiv hpos n]

private def renewalCountFiber (s : ℝ) (n : ℕ) : Set (ℕ → ℝ) :=
  {ω | canonicalRenewalCount s ω = n}

private def sameRenewalCountFiber (s h : ℝ) (n : ℕ) : Set (ℕ → ℝ) :=
  {ω | canonicalRenewalCount s ω = n ∧ canonicalRenewalCount (s + h) ω = n}

private def sameRenewalCountEvent (s h : ℝ) : Set (ℕ → ℝ) :=
  {ω | canonicalRenewalCount (s + h) ω = canonicalRenewalCount s ω}

private theorem measurableSet_renewalCountFiber (s : ℝ) (n : ℕ) :
    MeasurableSet (renewalCountFiber s n) := by
  exact (measurable_canonicalRenewalCount s) (measurableSet_singleton n)

private theorem measurableSet_sameRenewalCountFiber (s h : ℝ) (n : ℕ) :
    MeasurableSet (sameRenewalCountFiber s h n) := by
  exact (measurableSet_renewalCountFiber s n).inter
    (measurableSet_renewalCountFiber (s + h) n)

private theorem renewalCountFiber_pairwiseDisjoint (s : ℝ) :
    Pairwise (Function.onFun Disjoint (renewalCountFiber s)) := by
  intro n m hnm
  refine Set.disjoint_left.2 ?_
  intro ω hn hm
  exact hnm (hn.symm.trans hm)

private theorem sameRenewalCountFiber_pairwiseDisjoint (s h : ℝ) :
    Pairwise (Function.onFun Disjoint (sameRenewalCountFiber s h)) := by
  intro n m hnm
  refine Set.disjoint_left.2 ?_
  intro ω hn hm
  exact hnm (hn.1.symm.trans hm.1)

private theorem iUnion_renewalCountFiber_eq_univ (s : ℝ) :
    ⋃ n, renewalCountFiber s n = Set.univ := by
  ext ω
  constructor
  · intro _
    simp
  · intro _
    exact Set.mem_iUnion.2 ⟨canonicalRenewalCount s ω, rfl⟩

private theorem iUnion_sameRenewalCountFiber_eq_sameEvent (s h : ℝ) :
    ⋃ n, sameRenewalCountFiber s h n = sameRenewalCountEvent s h := by
  ext ω
  simp only [Set.mem_iUnion, sameRenewalCountFiber, sameRenewalCountEvent,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hn⟩
    exact hn.2.trans hn.1.symm
  · intro hω
    refine ⟨canonicalRenewalCount s ω, ?_⟩
    exact ⟨rfl, hω⟩

/-- The exact deterministic-clock no-arrival tail for the canonical renewal
count. `canonicalRenewalCount (s + h) = canonicalRenewalCount s` uses the
right-endpoint convention induced by the strict next-arrival inequality. -/
theorem canonicalRenewalCount_same_increment_measure_eq_expMeasure_Ioi
    {rate s h : ℝ} (hrate : 0 < rate) (hs : 0 ≤ s) (hh : 0 ≤ h) :
    exponentialInterarrivalMeasure rate
        {ω | canonicalRenewalCount (s + h) ω = canonicalRenewalCount s ω} =
      ProbabilityTheory.expMeasure rate (Set.Ioi h) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let c : ℝ≥0∞ := ProbabilityTheory.expMeasure rate (Set.Ioi h)
  letI : IsProbabilityMeasure μ := by
    simpa only [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  change μ (sameRenewalCountEvent s h) = ProbabilityTheory.expMeasure rate (Set.Ioi h)
  have hae_straddle : ∀ n : ℕ,
      fixedStraddleEvent s n =ᵐ[μ] renewalCountFiber s n := by
    intro n
    filter_upwards [ae_arrivalTime_tendsto_atTop hrate,
      ae_all_interarrival_positive hrate] with ω hdiv hpos
    apply propext
    exact fixedStraddleEvent_iff_canonicalRenewalCount_eq s hs ω hdiv hpos n
  have hae_noArrival : ∀ n : ℕ,
      fixedStraddleNoArrivalEvent s h n =ᵐ[μ] sameRenewalCountFiber s h n := by
    intro n
    filter_upwards [ae_arrivalTime_tendsto_atTop hrate,
      ae_all_interarrival_positive hrate] with ω hdiv hpos
    apply propext
    exact fixedStraddleNoArrivalEvent_iff_countFibers s h hs hh ω hdiv hpos n
  have hfactor : ∀ n : ℕ,
      μ (sameRenewalCountFiber s h n) = c * μ (renewalCountFiber s n) := by
    intro n
    calc
      μ (sameRenewalCountFiber s h n) =
          μ (fixedStraddleNoArrivalEvent s h n) := by
            exact (measure_congr (hae_noArrival n)).symm
      _ = c * μ (fixedStraddleEvent s n) := by
            simpa only [μ, c] using
              measure_fixedStraddleNoArrivalEvent_factorization hrate s h hh n
      _ = c * μ (renewalCountFiber s n) := by
            rw [measure_congr (hae_straddle n)]
  have hsum_fiber : ∑' n : ℕ, μ (renewalCountFiber s n) = 1 := by
    calc
      ∑' n : ℕ, μ (renewalCountFiber s n) = μ (⋃ n : ℕ, renewalCountFiber s n) := by
        symm
        exact measure_iUnion (renewalCountFiber_pairwiseDisjoint s)
          (measurableSet_renewalCountFiber s)
      _ = μ Set.univ := by
        rw [iUnion_renewalCountFiber_eq_univ]
      _ = 1 := measure_univ
  calc
    μ (sameRenewalCountEvent s h) =
        μ (⋃ n : ℕ, sameRenewalCountFiber s h n) := by
          rw [iUnion_sameRenewalCountFiber_eq_sameEvent]
    _ = ∑' n : ℕ, μ (sameRenewalCountFiber s h n) := by
          exact measure_iUnion (sameRenewalCountFiber_pairwiseDisjoint s h)
            (measurableSet_sameRenewalCountFiber s h)
    _ = ∑' n : ℕ, c * μ (renewalCountFiber s n) := by
          exact tsum_congr hfactor
    _ = c * ∑' n : ℕ, μ (renewalCountFiber s n) := by
          exact ENNReal.tsum_mul_left
    _ = c := by rw [hsum_fiber, mul_one]
    _ = ProbabilityTheory.expMeasure rate (Set.Ioi h) := by rfl

/-- Real-valued form of the deterministic-clock no-arrival tail. -/
theorem canonicalRenewalCount_same_increment_real_eq_exp
    {rate s h : ℝ} (hrate : 0 < rate) (hs : 0 ≤ s) (hh : 0 ≤ h) :
    (exponentialInterarrivalMeasure rate).real
        {ω | canonicalRenewalCount (s + h) ω = canonicalRenewalCount s ω} =
      Real.exp (-(rate * h)) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let M : Exponential.Model := ⟨rate, hrate⟩
  change μ.real (sameRenewalCountEvent s h) = Real.exp (-(rate * h))
  calc
    μ.real (sameRenewalCountEvent s h) =
        (ProbabilityTheory.expMeasure rate (Set.Ioi h)).toReal := by
          exact congrArg ENNReal.toReal
            (canonicalRenewalCount_same_increment_measure_eq_expMeasure_Ioi
              hrate hs hh)
    _ = Real.exp (-(rate * h)) := by
          simpa only [M, Exponential.Model.measure] using M.measure_Ioi_toReal hh

end

end AppliedModelingLib.Probability.PoissonProcess
