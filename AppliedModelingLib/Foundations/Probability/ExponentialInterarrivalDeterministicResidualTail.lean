import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalRenewalCountMarginal
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalResidualTail

/-!
# Deterministic-clock residual tails for exponential renewal paths

This module proves that the residual interarrival path seen from any
nonnegative deterministic clock time has the original iid exponential law.
The proof decomposes over the countably many possible straddling gaps, applies
the exponential memoryless law on each gap, and sums the resulting factorization.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory Filter
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

private def straddleProductSet (s : ℝ) : Set (ℝ × (ℕ → ℝ)) :=
  {p | p.1 ≤ s ∧ s < p.1 + interarrival 0 p.2}

private def straddleResidualTail (s : ℝ) (p : ℝ × (ℕ → ℝ)) : ℕ → ℝ :=
  firstGapResidualTail (s - p.1) p.2

private theorem measurable_straddleProductSet (s : ℝ) :
    MeasurableSet (straddleProductSet s) := by
  exact (measurableSet_le measurable_fst measurable_const).inter
    (measurableSet_lt measurable_const
      (measurable_fst.add ((measurable_interarrival 0).comp measurable_snd)))

private theorem measurable_straddleResidualTail (s : ℝ) :
    Measurable (straddleResidualTail s) := by
  apply measurable_pi_iff.2
  intro k
  cases k with
  | zero =>
      simpa [straddleResidualTail, firstGapResidualTail] using
        ((measurable_interarrival 0).comp measurable_snd).sub
          (measurable_const.sub measurable_fst)
  | succ k =>
      simpa [straddleResidualTail, firstGapResidualTail] using
        (measurable_interarrival (k + 1)).comp measurable_snd

private theorem slice_straddleResidualTail_factorization
    {rate s a : ℝ} (hrate : 0 < rate)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
    exponentialInterarrivalMeasure rate
        {ξ | a ≤ s ∧ s < a + interarrival 0 ξ ∧
          firstGapResidualTail (s - a) ξ ∈ B} =
      exponentialInterarrivalMeasure rate B *
        exponentialInterarrivalMeasure rate
          {ξ | a ≤ s ∧ s < a + interarrival 0 ξ} := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  change μ {ξ | a ≤ s ∧ s < a + interarrival 0 ξ ∧
      firstGapResidualTail (s - a) ξ ∈ B} =
    μ B * μ {ξ | a ≤ s ∧ s < a + interarrival 0 ξ}
  by_cases ha : a ≤ s
  · let elapsed : ℝ := s - a
    have helapsed : 0 ≤ elapsed := by
      dsimp [elapsed]
      linarith
    have hsurvival : {ξ | elapsed < interarrival 0 ξ} =
        {ξ | a ≤ s ∧ s < a + interarrival 0 ξ} := by
      ext ξ
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hξ
        exact ⟨ha, by dsimp [elapsed] at hξ; linarith⟩
      · rintro ⟨_, hξ⟩
        dsimp [elapsed]
        linarith
    have hleft : {ξ | a ≤ s ∧ s < a + interarrival 0 ξ ∧
        firstGapResidualTail (s - a) ξ ∈ B} =
        {ξ | elapsed < interarrival 0 ξ} ∩
          firstGapResidualTail elapsed ⁻¹' B := by
      ext ξ
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨_, hstraddle, hBξ⟩
        exact ⟨by dsimp [elapsed]; linarith, by simpa [elapsed] using hBξ⟩
      · rintro ⟨hsurvive, hBξ⟩
        exact ⟨ha, by dsimp [elapsed] at hsurvive; linarith,
          by simpa [elapsed] using hBξ⟩
    have hsurvival_measure :
        μ {ξ | elapsed < interarrival 0 ξ} =
          ProbabilityTheory.expMeasure rate (Set.Ioi elapsed) := by
      calc
        μ {ξ | elapsed < interarrival 0 ξ} =
            μ ((interarrival 0) ⁻¹' Set.Ioi elapsed) := by rfl
        _ = (μ.map (interarrival 0)) (Set.Ioi elapsed) := by
            exact (Measure.map_apply (measurable_interarrival 0) measurableSet_Ioi).symm
        _ = ProbabilityTheory.expMeasure rate (Set.Ioi elapsed) := by
            simpa [μ] using congrArg (fun m : Measure ℝ => m (Set.Ioi elapsed))
              (interarrival_hasLaw hrate 0).map_eq
    have hmap := firstGapResidualTail_restrict_map_eq_smul hrate helapsed
    have hresidual :
        μ ({ξ | elapsed < interarrival 0 ξ} ∩ firstGapResidualTail elapsed ⁻¹' B) =
          μ {ξ | elapsed < interarrival 0 ξ} * μ B := by
      calc
        μ ({ξ | elapsed < interarrival 0 ξ} ∩ firstGapResidualTail elapsed ⁻¹' B) =
            (μ.restrict {ξ | elapsed < interarrival 0 ξ})
              (firstGapResidualTail elapsed ⁻¹' B) := by
              rw [Measure.restrict_apply]
              · rw [Set.inter_comm]
              · exact (measurable_firstGapResidualTail elapsed) hB
        _ = ((μ.restrict {ξ | elapsed < interarrival 0 ξ}).map
              (firstGapResidualTail elapsed)) B := by
              rw [Measure.map_apply (measurable_firstGapResidualTail elapsed) hB]
        _ = (ProbabilityTheory.expMeasure rate (Set.Ioi elapsed) • μ) B := by
              simpa [μ] using congrArg (fun m : Measure (ℕ → ℝ) => m B) hmap
        _ = ProbabilityTheory.expMeasure rate (Set.Ioi elapsed) * μ B := by simp
        _ = μ {ξ | elapsed < interarrival 0 ξ} * μ B := by
              rw [hsurvival_measure]
    calc
      μ {ξ | a ≤ s ∧ s < a + interarrival 0 ξ ∧
          firstGapResidualTail (s - a) ξ ∈ B} =
          μ ({ξ | elapsed < interarrival 0 ξ} ∩ firstGapResidualTail elapsed ⁻¹' B) := by
            rw [hleft]
      _ = μ {ξ | elapsed < interarrival 0 ξ} * μ B := hresidual
      _ = μ B * μ {ξ | a ≤ s ∧ s < a + interarrival 0 ξ} := by
            rw [hsurvival]
            ac_rfl
  · have hleft_empty : {ξ | a ≤ s ∧ s < a + interarrival 0 ξ ∧
        firstGapResidualTail (s - a) ξ ∈ B} = ∅ := by
      ext ξ
      simp [ha]
    have hright_empty : {ξ | a ≤ s ∧ s < a + interarrival 0 ξ} = ∅ := by
      ext ξ
      simp [ha]
    rw [hleft_empty, hright_empty]
    simp

private theorem product_straddleResidualTail_factorization
    {rate s : ℝ} (hrate : 0 < rate) (ν : Measure ℝ)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
    (ν.prod (exponentialInterarrivalMeasure rate))
        {p | p ∈ straddleProductSet s ∧ straddleResidualTail s p ∈ B} =
      (exponentialInterarrivalMeasure rate B) *
        (ν.prod (exponentialInterarrivalMeasure rate)) (straddleProductSet s) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hEvent : MeasurableSet {p | p ∈ straddleProductSet s ∧
      straddleResidualTail s p ∈ B} :=
    (measurable_straddleProductSet s).inter ((measurable_straddleResidualTail s) hB)
  rw [Measure.prod_apply hEvent, Measure.prod_apply (measurable_straddleProductSet s)]
  have hslice : ∀ a : ℝ,
      μ (Prod.mk a ⁻¹' {p | p ∈ straddleProductSet s ∧
        straddleResidualTail s p ∈ B}) =
        μ B * μ (Prod.mk a ⁻¹' straddleProductSet s) := by
    intro a
    have hpreEvent :
        Prod.mk a ⁻¹' {p | p ∈ straddleProductSet s ∧
          straddleResidualTail s p ∈ B} =
          {ξ | a ≤ s ∧ s < a + interarrival 0 ξ ∧
            firstGapResidualTail (s - a) ξ ∈ B} := by
      ext ξ
      simp [straddleProductSet, straddleResidualTail, and_assoc]
    have hpreStraddle : Prod.mk a ⁻¹' straddleProductSet s =
        {ξ | a ≤ s ∧ s < a + interarrival 0 ξ} := by
      ext ξ
      simp [straddleProductSet]
    rw [hpreEvent, hpreStraddle]
    exact slice_straddleResidualTail_factorization hrate B hB
  calc
    ∫⁻ a, μ (Prod.mk a ⁻¹' {p | p ∈ straddleProductSet s ∧
        straddleResidualTail s p ∈ B}) ∂ν =
        ∫⁻ a, μ B * μ (Prod.mk a ⁻¹' straddleProductSet s) ∂ν := by
          exact lintegral_congr hslice
    _ = μ B * ∫⁻ a, μ (Prod.mk a ⁻¹' straddleProductSet s) ∂ν := by
          exact lintegral_const_mul' _ _ (measure_ne_top _ _)

/-! The preceding factorization only retains the elapsed clock value.  The
following version keeps an arbitrary measurable pre-clock state, which is
needed when a state process depends on all prior interarrival times rather
than only on their sum. -/

private def clockStraddleProductSet
    {β : Type*} (s : ℝ) (clock : β → ℝ) : Set (β × (ℕ → ℝ)) :=
  {p | clock p.1 ≤ s ∧ s < clock p.1 + interarrival 0 p.2}

private def clockStraddleResidualTail
    {β : Type*} (s : ℝ) (clock : β → ℝ) (p : β × (ℕ → ℝ)) : ℕ → ℝ :=
  firstGapResidualTail (s - clock p.1) p.2

private theorem measurable_clockStraddleProductSet
    {β : Type*} [MeasurableSpace β] (s : ℝ) (clock : β → ℝ)
    (hclock : Measurable clock) :
    MeasurableSet (clockStraddleProductSet s clock) := by
  exact (measurableSet_le (hclock.comp measurable_fst) measurable_const).inter
    (measurableSet_lt measurable_const
      ((hclock.comp measurable_fst).add
        ((measurable_interarrival 0).comp measurable_snd)))

private theorem measurable_clockStraddleResidualTail
    {β : Type*} [MeasurableSpace β] (s : ℝ) (clock : β → ℝ)
    (hclock : Measurable clock) :
    Measurable (clockStraddleResidualTail s clock) := by
  apply measurable_pi_iff.2
  intro k
  cases k with
  | zero =>
      simpa [clockStraddleResidualTail, firstGapResidualTail] using
        ((measurable_interarrival 0).comp measurable_snd).sub
          (measurable_const.sub (hclock.comp measurable_fst))
  | succ k =>
      simpa [clockStraddleResidualTail, firstGapResidualTail] using
        (measurable_interarrival (k + 1)).comp measurable_snd

private theorem clockStraddleResidualTail_slice_factorization
    {β : Type*} {rate s : ℝ} (hrate : 0 < rate)
    (clock : β → ℝ) (b : β)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
    exponentialInterarrivalMeasure rate
        (Prod.mk b ⁻¹' {p | p ∈ clockStraddleProductSet s clock ∧
          clockStraddleResidualTail s clock p ∈ B}) =
      exponentialInterarrivalMeasure rate B *
        exponentialInterarrivalMeasure rate
          (Prod.mk b ⁻¹' clockStraddleProductSet s clock) := by
  have hpreEvent :
      Prod.mk b ⁻¹' {p | p ∈ clockStraddleProductSet s clock ∧
        clockStraddleResidualTail s clock p ∈ B} =
        {ξ | clock b ≤ s ∧ s < clock b + interarrival 0 ξ ∧
          firstGapResidualTail (s - clock b) ξ ∈ B} := by
    ext ξ
    simp [clockStraddleProductSet, clockStraddleResidualTail, and_assoc]
  have hpreStraddle : Prod.mk b ⁻¹' clockStraddleProductSet s clock =
      {ξ | clock b ≤ s ∧ s < clock b + interarrival 0 ξ} := by
    ext ξ
    simp [clockStraddleProductSet]
  rw [hpreEvent, hpreStraddle]
  exact slice_straddleResidualTail_factorization hrate B hB

private theorem product_clockStraddleResidualTail_factorization
    {β : Type*} [MeasurableSpace β] {rate s : ℝ} (hrate : 0 < rate)
    (ν : Measure β) (clock : β → ℝ) (hclock : Measurable clock)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
    (ν.prod (exponentialInterarrivalMeasure rate))
        {p | p ∈ clockStraddleProductSet s clock ∧
          clockStraddleResidualTail s clock p ∈ B} =
      (exponentialInterarrivalMeasure rate B) *
        (ν.prod (exponentialInterarrivalMeasure rate))
          (clockStraddleProductSet s clock) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hEvent : MeasurableSet {p | p ∈ clockStraddleProductSet s clock ∧
      clockStraddleResidualTail s clock p ∈ B} :=
    (measurable_clockStraddleProductSet s clock hclock).inter
      ((measurable_clockStraddleResidualTail s clock hclock) hB)
  rw [Measure.prod_apply hEvent,
    Measure.prod_apply (measurable_clockStraddleProductSet s clock hclock)]
  have hslice : ∀ b : β,
      μ (Prod.mk b ⁻¹' {p | p ∈ clockStraddleProductSet s clock ∧
        clockStraddleResidualTail s clock p ∈ B}) =
        μ B * μ (Prod.mk b ⁻¹' clockStraddleProductSet s clock) := by
    intro b
    have hpreEvent :
        Prod.mk b ⁻¹' {p | p ∈ clockStraddleProductSet s clock ∧
          clockStraddleResidualTail s clock p ∈ B} =
          {ξ | clock b ≤ s ∧ s < clock b + interarrival 0 ξ ∧
            firstGapResidualTail (s - clock b) ξ ∈ B} := by
      ext ξ
      simp [clockStraddleProductSet, clockStraddleResidualTail, and_assoc]
    have hpreStraddle : Prod.mk b ⁻¹' clockStraddleProductSet s clock =
        {ξ | clock b ≤ s ∧ s < clock b + interarrival 0 ξ} := by
      ext ξ
      simp [clockStraddleProductSet]
    rw [hpreEvent, hpreStraddle]
    exact slice_straddleResidualTail_factorization hrate B hB
  calc
    ∫⁻ b, μ (Prod.mk b ⁻¹' {p | p ∈ clockStraddleProductSet s clock ∧
        clockStraddleResidualTail s clock p ∈ B}) ∂ν =
        ∫⁻ b, μ B * μ (Prod.mk b ⁻¹' clockStraddleProductSet s clock) ∂ν := by
          exact lintegral_congr hslice
    _ = μ B * ∫⁻ b, μ (Prod.mk b ⁻¹' clockStraddleProductSet s clock) ∂ν := by
          exact lintegral_const_mul' _ _ (measure_ne_top _ _)

private theorem measurable_prefixInterarrivalSum (n : ℕ) :
    Measurable (fun gaps : Fin n → ℝ => ∑ i, gaps i) := by
  induction n with
  | zero => simpa using (measurable_const : Measurable (fun _ : Fin 0 → ℝ => (0 : ℝ)))
  | succ n ih =>
      let restrict : (Fin (n + 1) → ℝ) → Fin n → ℝ :=
        fun gaps i => gaps i.castSucc
      have hrestrict : Measurable restrict := by
        apply measurable_pi_iff.2
        intro i
        exact measurable_pi_apply i.castSucc
      have hlast : Measurable (fun gaps : Fin (n + 1) → ℝ => gaps (Fin.last n)) :=
        measurable_pi_apply _
      simpa [Function.comp_def, restrict, Fin.sum_univ_castSucc] using
        (ih.comp hrestrict).add hlast

private theorem product_clockStraddleResidualTail_factorization_on
    {β : Type*} [MeasurableSpace β] {rate s : ℝ} (hrate : 0 < rate)
    (ν : Measure β) (clock : β → ℝ) (hclock : Measurable clock)
    (A : Set β) (hA : MeasurableSet A)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
    (ν.prod (exponentialInterarrivalMeasure rate))
        {p | p.1 ∈ A ∧ p ∈ clockStraddleProductSet s clock ∧
          clockStraddleResidualTail s clock p ∈ B} =
      (exponentialInterarrivalMeasure rate B) *
        (ν.prod (exponentialInterarrivalMeasure rate))
          {p | p.1 ∈ A ∧ p ∈ clockStraddleProductSet s clock} := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hstraddle : MeasurableSet (clockStraddleProductSet s clock) :=
    measurable_clockStraddleProductSet s clock hclock
  have htail : Measurable (clockStraddleResidualTail s clock) :=
    measurable_clockStraddleResidualTail s clock hclock
  have hEvent : MeasurableSet {p | p.1 ∈ A ∧ p ∈ clockStraddleProductSet s clock ∧
      clockStraddleResidualTail s clock p ∈ B} :=
    by
      convert ((hA.preimage measurable_fst).inter hstraddle).inter (htail hB) using 1
      ext p
      simp [and_assoc]
  have hPreEvent : MeasurableSet {p : β × (ℕ → ℝ) |
      p.1 ∈ A ∧ p ∈ clockStraddleProductSet s clock} :=
    by
      simpa only [Set.preimage, Set.mem_inter_iff] using
        (hA.preimage measurable_fst).inter hstraddle
  rw [Measure.prod_apply hEvent, Measure.prod_apply hPreEvent]
  have hslice : ∀ b : β,
      μ (Prod.mk b ⁻¹' {p | p.1 ∈ A ∧ p ∈ clockStraddleProductSet s clock ∧
        clockStraddleResidualTail s clock p ∈ B}) =
        μ B * μ (Prod.mk b ⁻¹' {p | p.1 ∈ A ∧ p ∈ clockStraddleProductSet s clock}) := by
    intro b
    by_cases hb : b ∈ A
    · have hleft :
          Prod.mk b ⁻¹' {p | p.1 ∈ A ∧ p ∈ clockStraddleProductSet s clock ∧
            clockStraddleResidualTail s clock p ∈ B} =
            Prod.mk b ⁻¹' {p | p ∈ clockStraddleProductSet s clock ∧
              clockStraddleResidualTail s clock p ∈ B} := by
            ext ξ
            simp [hb]
      have hright :
          Prod.mk b ⁻¹' {p | p.1 ∈ A ∧ p ∈ clockStraddleProductSet s clock} =
            Prod.mk b ⁻¹' clockStraddleProductSet s clock := by
            ext ξ
            simp [hb]
      rw [hleft, hright]
      simpa [μ] using
        (clockStraddleResidualTail_slice_factorization hrate clock b B hB)
    · have hleft_empty :
          Prod.mk b ⁻¹' {p | p.1 ∈ A ∧ p ∈ clockStraddleProductSet s clock ∧
            clockStraddleResidualTail s clock p ∈ B} = ∅ := by
            ext ξ
            simp [hb]
      have hright_empty :
          Prod.mk b ⁻¹' {p | p.1 ∈ A ∧ p ∈ clockStraddleProductSet s clock} = ∅ := by
            ext ξ
            simp [hb]
      rw [hleft_empty, hright_empty]
      simp
  calc
    ∫⁻ b, μ (Prod.mk b ⁻¹' {p | p.1 ∈ A ∧ p ∈ clockStraddleProductSet s clock ∧
        clockStraddleResidualTail s clock p ∈ B}) ∂ν =
        ∫⁻ b, μ B * μ (Prod.mk b ⁻¹' {p | p.1 ∈ A ∧
          p ∈ clockStraddleProductSet s clock}) ∂ν := by
          exact lintegral_congr hslice
    _ = μ B * ∫⁻ b, μ (Prod.mk b ⁻¹' {p | p.1 ∈ A ∧
        p ∈ clockStraddleProductSet s clock}) ∂ν := by
          exact lintegral_const_mul' _ _ (measure_ne_top _ _)

private def fixedStraddleEvent (s : ℝ) (n : ℕ) : Set (ℕ → ℝ) :=
  {ω | arrivalPrefix n ω ≤ s ∧ s < arrivalTime n ω}

private def fixedStraddleFirstGapResidualEvent
    (s : ℝ) (n : ℕ) (B : Set (ℕ → ℝ)) : Set (ℕ → ℝ) :=
  {ω | fixedStraddleEvent s n ω ∧
    firstGapResidualTail (s - arrivalPrefix n ω) (futureInterarrival n ω) ∈ B}

private def renewalCountFiber (s : ℝ) (n : ℕ) : Set (ℕ → ℝ) :=
  {ω | canonicalRenewalCount s ω = n}

private theorem residualTail_eq_firstGapResidualTail_of_count_eq
    (s : ℝ) (ω : ℕ → ℝ) (n : ℕ)
    (hcount : canonicalRenewalCount s ω = n) :
    residualTail s ω =
      firstGapResidualTail (s - arrivalPrefix n ω) (futureInterarrival n ω) := by
  funext k
  cases k with
  | zero =>
      simp [residualTail, firstGapResidualTail, hcount, arrivalTime, arrivalPrefix,
        futureInterarrival, interarrival, Finset.sum_range_succ]
      ring
  | succ k =>
      simp [residualTail, firstGapResidualTail, hcount, futureInterarrival, interarrival]

/-- On a specified renewal-count fiber, the literal clock-time residual path
is the corresponding deterministic coordinate tail with its first gap reduced
by the elapsed amount.  This is path algebra; no distributional conclusion is
used. -/
theorem residualTail_eq_firstGapResidualTail_on_countFiber
    (s : ℝ) (ω : ℕ → ℝ) (n : ℕ)
    (hcount : canonicalRenewalCount s ω = n) :
    residualTail s ω =
      firstGapResidualTail (s - arrivalPrefix n ω) (futureInterarrival n ω) := by
  funext k
  cases k with
  | zero =>
      simp [residualTail, firstGapResidualTail, hcount, arrivalTime, arrivalPrefix,
        futureInterarrival, interarrival, Finset.sum_range_succ]
      ring
  | succ k =>
      simp [residualTail, firstGapResidualTail, hcount, futureInterarrival, interarrival]

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
    simpa [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hX : Measurable X := by simpa [X] using measurable_arrivalPrefix n
  have hY : Measurable Y := by
    simpa [Y] using measurable_pi_iff.2 (fun k => measurable_futureInterarrival n k)
  have hIndep : ProbabilityTheory.IndepFun X Y μ := by
    simpa [μ, X, Y] using arrivalPrefix_indep_futureInterarrival hrate n
  refine ⟨(hX.prodMk hY).aemeasurable, ?_⟩
  have htail : μ.map Y = μ := by
    simpa [μ, Y] using (futureInterarrival_hasLaw_path hrate n).map_eq
  calc
    μ.map (fun ω => (X ω, Y ω)) = (μ.map X).prod (μ.map Y) :=
      (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
        hX.aemeasurable hY.aemeasurable).mp hIndep
    _ = (μ.map X).prod μ := by rw [htail]

private theorem measurableSet_fixedStraddleEvent (s : ℝ) (n : ℕ) :
    MeasurableSet (fixedStraddleEvent s n) := by
  exact (measurableSet_le (measurable_arrivalPrefix n) measurable_const).inter
    (measurableSet_lt measurable_const (measurable_arrivalTime n))

private theorem measurableSet_fixedStraddleFirstGapResidualEvent
    (s : ℝ) (n : ℕ) (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
    MeasurableSet (fixedStraddleFirstGapResidualEvent s n B) := by
  have htail : Measurable (fun ω : ℕ → ℝ =>
      firstGapResidualTail (s - arrivalPrefix n ω) (futureInterarrival n ω)) := by
    apply measurable_pi_iff.2
    intro k
    cases k with
    | zero =>
        simpa [firstGapResidualTail] using
          ((measurable_interarrival 0).comp
            (measurable_pi_iff.2 fun j => measurable_futureInterarrival n j)).sub
              (measurable_const.sub (measurable_arrivalPrefix n))
    | succ k =>
        simpa [firstGapResidualTail] using
          (measurable_interarrival (k + 1)).comp
            (measurable_pi_iff.2 fun j => measurable_futureInterarrival n j)
  exact (measurableSet_fixedStraddleEvent s n).inter (htail hB)

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
    have htail : interarrival 0 (futureInterarrival n ω) = interarrival n ω := by rfl
    rw [htail]
    simp [fixedStraddleEvent, arrivalTime, arrivalPrefix, Finset.sum_range_succ]
  calc
    μ (fixedStraddleEvent s n) = μ (f ⁻¹' straddleProductSet s) := by rw [hpreimage]
    _ = (Measure.map f μ) (straddleProductSet s) := by
      symm
      exact Measure.map_apply hf (measurable_straddleProductSet s)
    _ = ((Measure.map (arrivalPrefix n) μ).prod μ) (straddleProductSet s) := by
      rw [(arrivalPrefix_futureInterarrival_hasLaw_prod hrate n).map_eq]

private theorem measure_fixedStraddleFirstGapResidualEvent_eq_product
    {rate : ℝ} (hrate : 0 < rate) (s : ℝ) (n : ℕ)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
    exponentialInterarrivalMeasure rate (fixedStraddleFirstGapResidualEvent s n B) =
      ((Measure.map (arrivalPrefix n) (exponentialInterarrivalMeasure rate)).prod
        (exponentialInterarrivalMeasure rate))
        {p | p ∈ straddleProductSet s ∧ straddleResidualTail s p ∈ B} := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let f : (ℕ → ℝ) → ℝ × (ℕ → ℝ) :=
    fun ω => (arrivalPrefix n ω, futureInterarrival n ω)
  have hf : Measurable f := by
    exact (measurable_arrivalPrefix n).prodMk
      (measurable_pi_iff.2 fun k => measurable_futureInterarrival n k)
  have hpreimage : f ⁻¹' {p | p ∈ straddleProductSet s ∧
      straddleResidualTail s p ∈ B} =
      fixedStraddleFirstGapResidualEvent s n B := by
    ext ω
    change
      ((arrivalPrefix n ω ≤ s ∧
          s < arrivalPrefix n ω + interarrival 0 (futureInterarrival n ω)) ∧
        firstGapResidualTail (s - arrivalPrefix n ω) (futureInterarrival n ω) ∈ B) ↔
      ((arrivalPrefix n ω ≤ s ∧ s < arrivalTime n ω) ∧
        firstGapResidualTail (s - arrivalPrefix n ω) (futureInterarrival n ω) ∈ B)
    have htail : interarrival 0 (futureInterarrival n ω) = interarrival n ω := by rfl
    have harrival : arrivalTime n ω =
        arrivalPrefix n ω + interarrival n ω := by
      simp [arrivalTime, arrivalPrefix, Finset.sum_range_succ]
    rw [htail, harrival]
  calc
    μ (fixedStraddleFirstGapResidualEvent s n B) =
        μ (f ⁻¹' {p | p ∈ straddleProductSet s ∧ straddleResidualTail s p ∈ B}) := by
          rw [hpreimage]
    _ = (Measure.map f μ) {p | p ∈ straddleProductSet s ∧ straddleResidualTail s p ∈ B} := by
      symm
      exact Measure.map_apply hf
        ((measurable_straddleProductSet s).inter ((measurable_straddleResidualTail s) hB))
    _ = ((Measure.map (arrivalPrefix n) μ).prod μ)
        {p | p ∈ straddleProductSet s ∧ straddleResidualTail s p ∈ B} := by
          rw [(arrivalPrefix_futureInterarrival_hasLaw_prod hrate n).map_eq]

private theorem measure_fixedStraddleFirstGapResidualEvent_factorization
    {rate : ℝ} (hrate : 0 < rate) (s : ℝ) (n : ℕ)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
    exponentialInterarrivalMeasure rate (fixedStraddleFirstGapResidualEvent s n B) =
      exponentialInterarrivalMeasure rate B *
        exponentialInterarrivalMeasure rate (fixedStraddleEvent s n) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let ν : Measure ℝ := μ.map (arrivalPrefix n)
  calc
    μ (fixedStraddleFirstGapResidualEvent s n B) =
        (ν.prod μ) {p | p ∈ straddleProductSet s ∧ straddleResidualTail s p ∈ B} := by
          simpa [μ, ν] using
            measure_fixedStraddleFirstGapResidualEvent_eq_product hrate s n B hB
    _ = μ B * (ν.prod μ) (straddleProductSet s) := by
          exact product_straddleResidualTail_factorization hrate ν B hB
    _ = μ B * μ (fixedStraddleEvent s n) := by
          rw [measure_fixedStraddleEvent_eq_product hrate s n]

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

private theorem ae_fixedStraddleEvent_eq_renewalCountFiber
    {rate s : ℝ} (hrate : 0 < rate) (hs : 0 ≤ s) (n : ℕ) :
    fixedStraddleEvent s n =ᵐ[exponentialInterarrivalMeasure rate]
      renewalCountFiber s n := by
  filter_upwards [ae_arrivalTime_tendsto_atTop hrate,
    ae_all_interarrival_positive hrate] with ω hdiv hpos
  apply propext
  exact fixedStraddleEvent_iff_canonicalRenewalCount_eq s hs ω hdiv hpos n

private def renewalCountResidualTailFiber
    (s : ℝ) (n : ℕ) (B : Set (ℕ → ℝ)) : Set (ℕ → ℝ) :=
  {ω | canonicalRenewalCount s ω = n ∧ residualTail s ω ∈ B}

private theorem ae_fixedStraddleFirstGapResidualEvent_eq_renewalCountResidualTailFiber
    {rate s : ℝ} (hrate : 0 < rate) (hs : 0 ≤ s) (n : ℕ)
    (B : Set (ℕ → ℝ)) :
    fixedStraddleFirstGapResidualEvent s n B =ᵐ[exponentialInterarrivalMeasure rate]
      renewalCountResidualTailFiber s n B := by
  filter_upwards [ae_fixedStraddleEvent_eq_renewalCountFiber hrate hs n] with ω hstraddle
  apply propext
  constructor
  · rintro ⟨hfixed, hfirst⟩
    have hcount : canonicalRenewalCount s ω = n := hstraddle.mp hfixed
    refine ⟨hcount, ?_⟩
    rw [residualTail_eq_firstGapResidualTail_of_count_eq s ω n hcount]
    exact hfirst
  · rintro ⟨hcount, hresidual⟩
    refine ⟨hstraddle.mpr hcount, ?_⟩
    rw [← residualTail_eq_firstGapResidualTail_of_count_eq s ω n hcount]
    exact hresidual

private theorem measure_renewalCountResidualTailFiber_factorization
    {rate s : ℝ} (hrate : 0 < rate) (hs : 0 ≤ s) (n : ℕ)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
    exponentialInterarrivalMeasure rate (renewalCountResidualTailFiber s n B) =
      exponentialInterarrivalMeasure rate B *
        exponentialInterarrivalMeasure rate (renewalCountFiber s n) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  calc
    μ (renewalCountResidualTailFiber s n B) =
        μ (fixedStraddleFirstGapResidualEvent s n B) := by
          exact (measure_congr
            (ae_fixedStraddleFirstGapResidualEvent_eq_renewalCountResidualTailFiber
              hrate hs n B)).symm
    _ = μ B * μ (fixedStraddleEvent s n) := by
          simpa [μ] using
            measure_fixedStraddleFirstGapResidualEvent_factorization hrate s n B hB
    _ = μ B * μ (renewalCountFiber s n) := by
          rw [measure_congr (ae_fixedStraddleEvent_eq_renewalCountFiber hrate hs n)]

private def fixedPrefixStraddleEvent
    (s : ℝ) (n : ℕ) (A : Set (Fin n → ℝ)) : Set (ℕ → ℝ) :=
  {ω | prefixInterarrival n ω ∈ A ∧ fixedStraddleEvent s n ω}

private def fixedPrefixStraddleFirstGapResidualEvent
    (s : ℝ) (n : ℕ) (A : Set (Fin n → ℝ)) (B : Set (ℕ → ℝ)) :
    Set (ℕ → ℝ) :=
  {ω | prefixInterarrival n ω ∈ A ∧ fixedStraddleEvent s n ω ∧
    firstGapResidualTail (s - arrivalPrefix n ω) (futureInterarrival n ω) ∈ B}

private def renewalCountPrefixFiber
    (s : ℝ) (n : ℕ) (A : Set (Fin n → ℝ)) : Set (ℕ → ℝ) :=
  {ω | canonicalRenewalCount s ω = n ∧ prefixInterarrival n ω ∈ A}

private def renewalCountPrefixResidualTailFiber
    (s : ℝ) (n : ℕ) (A : Set (Fin n → ℝ)) (B : Set (ℕ → ℝ)) :
    Set (ℕ → ℝ) :=
  {ω | canonicalRenewalCount s ω = n ∧ prefixInterarrival n ω ∈ A ∧
    residualTail s ω ∈ B}

private theorem measurableSet_fixedPrefixStraddleEvent
    (s : ℝ) (n : ℕ) (A : Set (Fin n → ℝ)) (hA : MeasurableSet A) :
    MeasurableSet (fixedPrefixStraddleEvent s n A) := by
  exact ((measurable_prefixInterarrival n) hA).inter
    (measurableSet_fixedStraddleEvent s n)

private theorem measurableSet_fixedPrefixStraddleFirstGapResidualEvent
    (s : ℝ) (n : ℕ) (A : Set (Fin n → ℝ)) (hA : MeasurableSet A)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
    MeasurableSet (fixedPrefixStraddleFirstGapResidualEvent s n A B) := by
  have htail : Measurable (fun ω : ℕ → ℝ =>
      firstGapResidualTail (s - arrivalPrefix n ω) (futureInterarrival n ω)) := by
    apply measurable_pi_iff.2
    intro k
    cases k with
    | zero =>
        simpa [firstGapResidualTail] using
          ((measurable_interarrival 0).comp
            (measurable_pi_iff.2 fun j => measurable_futureInterarrival n j)).sub
              (measurable_const.sub (measurable_arrivalPrefix n))
    | succ k =>
        simpa [firstGapResidualTail] using
          (measurable_interarrival (k + 1)).comp
            (measurable_pi_iff.2 fun j => measurable_futureInterarrival n j)
  exact ((measurable_prefixInterarrival n) hA).inter
    ((measurableSet_fixedStraddleEvent s n).inter (htail hB))

private theorem measure_fixedPrefixStraddleEvent_eq_product
    {rate : ℝ} (hrate : 0 < rate) (s : ℝ) (n : ℕ)
    (A : Set (Fin n → ℝ)) (hA : MeasurableSet A) :
    exponentialInterarrivalMeasure rate (fixedPrefixStraddleEvent s n A) =
      ((Measure.map (prefixInterarrival n) (exponentialInterarrivalMeasure rate)).prod
        (exponentialInterarrivalMeasure rate))
        {p | p.1 ∈ A ∧ p ∈ clockStraddleProductSet s (fun gaps : Fin n → ℝ => ∑ i, gaps i)} := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let f : (ℕ → ℝ) → (Fin n → ℝ) × (ℕ → ℝ) :=
    fun ω => (prefixInterarrival n ω, futureInterarrival n ω)
  let clock : (Fin n → ℝ) → ℝ := fun gaps => ∑ i, gaps i
  have hclock : Measurable clock := by
    simpa [clock] using measurable_prefixInterarrivalSum n
  have hf : Measurable f := by
    exact (measurable_prefixInterarrival n).prodMk
      (measurable_pi_iff.2 fun k => measurable_futureInterarrival n k)
  have hProductSet : MeasurableSet
      {p : (Fin n → ℝ) × (ℕ → ℝ) | p.1 ∈ A ∧ p ∈ clockStraddleProductSet s clock} := by
    exact (hA.preimage measurable_fst).inter
      (measurable_clockStraddleProductSet s clock hclock)
  have hpreimage : f ⁻¹'
      {p | p.1 ∈ A ∧ p ∈ clockStraddleProductSet s clock} =
      fixedPrefixStraddleEvent s n A := by
    ext ω
    change
      (prefixInterarrival n ω ∈ A ∧
        ((∑ i : Fin n, prefixInterarrival n ω i) ≤ s ∧
          s < (∑ i : Fin n, prefixInterarrival n ω i) +
            interarrival 0 (futureInterarrival n ω))) ↔
        (prefixInterarrival n ω ∈ A ∧
          (arrivalPrefix n ω ≤ s ∧ s < arrivalTime n ω))
    rw [sum_prefixInterarrival]
    have htail : interarrival 0 (futureInterarrival n ω) = interarrival n ω := by rfl
    have harrival : arrivalTime n ω =
        arrivalPrefix n ω + interarrival n ω := by
      simp [arrivalTime, arrivalPrefix, Finset.sum_range_succ]
    rw [htail, harrival]
  calc
    μ (fixedPrefixStraddleEvent s n A) =
        μ (f ⁻¹' {p | p.1 ∈ A ∧ p ∈ clockStraddleProductSet s clock}) := by
          rw [hpreimage]
    _ = (Measure.map f μ)
        {p | p.1 ∈ A ∧ p ∈ clockStraddleProductSet s clock} := by
          symm
          exact Measure.map_apply hf hProductSet
    _ = ((Measure.map (prefixInterarrival n) μ).prod μ)
        {p | p.1 ∈ A ∧ p ∈ clockStraddleProductSet s clock} := by
          rw [(prefixInterarrival_futureInterarrival_hasLaw_prod hrate n).map_eq]

private theorem measure_fixedPrefixStraddleFirstGapResidualEvent_eq_product
    {rate : ℝ} (hrate : 0 < rate) (s : ℝ) (n : ℕ)
    (A : Set (Fin n → ℝ)) (hA : MeasurableSet A)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
    exponentialInterarrivalMeasure rate
        (fixedPrefixStraddleFirstGapResidualEvent s n A B) =
      ((Measure.map (prefixInterarrival n) (exponentialInterarrivalMeasure rate)).prod
        (exponentialInterarrivalMeasure rate))
        {p | p.1 ∈ A ∧ p ∈ clockStraddleProductSet s (fun gaps : Fin n → ℝ => ∑ i, gaps i) ∧
          clockStraddleResidualTail s (fun gaps : Fin n → ℝ => ∑ i, gaps i) p ∈ B} := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let f : (ℕ → ℝ) → (Fin n → ℝ) × (ℕ → ℝ) :=
    fun ω => (prefixInterarrival n ω, futureInterarrival n ω)
  let clock : (Fin n → ℝ) → ℝ := fun gaps => ∑ i, gaps i
  have hclock : Measurable clock := by
    simpa [clock] using measurable_prefixInterarrivalSum n
  have hf : Measurable f := by
    exact (measurable_prefixInterarrival n).prodMk
      (measurable_pi_iff.2 fun k => measurable_futureInterarrival n k)
  have hProductSet : MeasurableSet
      {p : (Fin n → ℝ) × (ℕ → ℝ) | p.1 ∈ A ∧
        p ∈ clockStraddleProductSet s clock ∧
        clockStraddleResidualTail s clock p ∈ B} := by
    exact (hA.preimage measurable_fst).inter
      ((measurable_clockStraddleProductSet s clock hclock).inter
        ((measurable_clockStraddleResidualTail s clock hclock) hB))
  have hpreimage : f ⁻¹'
      {p | p.1 ∈ A ∧ p ∈ clockStraddleProductSet s clock ∧
        clockStraddleResidualTail s clock p ∈ B} =
      fixedPrefixStraddleFirstGapResidualEvent s n A B := by
    ext ω
    change
      (prefixInterarrival n ω ∈ A ∧
        ((∑ i : Fin n, prefixInterarrival n ω i) ≤ s ∧
          s < (∑ i : Fin n, prefixInterarrival n ω i) +
            interarrival 0 (futureInterarrival n ω)) ∧
        firstGapResidualTail (s - (∑ i : Fin n, prefixInterarrival n ω i))
          (futureInterarrival n ω) ∈ B) ↔
        (prefixInterarrival n ω ∈ A ∧
          (arrivalPrefix n ω ≤ s ∧ s < arrivalTime n ω) ∧
          firstGapResidualTail (s - arrivalPrefix n ω) (futureInterarrival n ω) ∈ B)
    rw [sum_prefixInterarrival]
    have htail : interarrival 0 (futureInterarrival n ω) = interarrival n ω := by rfl
    have harrival : arrivalTime n ω =
        arrivalPrefix n ω + interarrival n ω := by
      simp [arrivalTime, arrivalPrefix, Finset.sum_range_succ]
    rw [htail, harrival]
  calc
    μ (fixedPrefixStraddleFirstGapResidualEvent s n A B) =
        μ (f ⁻¹' {p | p.1 ∈ A ∧ p ∈ clockStraddleProductSet s clock ∧
          clockStraddleResidualTail s clock p ∈ B}) := by
          rw [hpreimage]
    _ = (Measure.map f μ)
        {p | p.1 ∈ A ∧ p ∈ clockStraddleProductSet s clock ∧
          clockStraddleResidualTail s clock p ∈ B} := by
          symm
          exact Measure.map_apply hf hProductSet
    _ = ((Measure.map (prefixInterarrival n) μ).prod μ)
        {p | p.1 ∈ A ∧ p ∈ clockStraddleProductSet s clock ∧
          clockStraddleResidualTail s clock p ∈ B} := by
          rw [(prefixInterarrival_futureInterarrival_hasLaw_prod hrate n).map_eq]

private theorem measure_fixedPrefixStraddleFirstGapResidualEvent_factorization
    {rate : ℝ} (hrate : 0 < rate) (s : ℝ) (n : ℕ)
    (A : Set (Fin n → ℝ)) (hA : MeasurableSet A)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
    exponentialInterarrivalMeasure rate
        (fixedPrefixStraddleFirstGapResidualEvent s n A B) =
      exponentialInterarrivalMeasure rate B *
        exponentialInterarrivalMeasure rate (fixedPrefixStraddleEvent s n A) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let ν : Measure (Fin n → ℝ) := μ.map (prefixInterarrival n)
  let clock : (Fin n → ℝ) → ℝ := fun gaps => ∑ i, gaps i
  have hclock : Measurable clock := by
    simpa [clock] using measurable_prefixInterarrivalSum n
  calc
    μ (fixedPrefixStraddleFirstGapResidualEvent s n A B) =
        (ν.prod μ) {p | p.1 ∈ A ∧ p ∈ clockStraddleProductSet s clock ∧
          clockStraddleResidualTail s clock p ∈ B} := by
          simpa [μ, ν, clock] using
            measure_fixedPrefixStraddleFirstGapResidualEvent_eq_product
              hrate s n A hA B hB
    _ = μ B * (ν.prod μ) {p | p.1 ∈ A ∧
        p ∈ clockStraddleProductSet s clock} := by
          exact product_clockStraddleResidualTail_factorization_on
            hrate ν clock hclock A hA B hB
    _ = μ B * μ (fixedPrefixStraddleEvent s n A) := by
          rw [measure_fixedPrefixStraddleEvent_eq_product hrate s n A hA]

private theorem ae_fixedPrefixStraddleEvent_eq_renewalCountPrefixFiber
    {rate s : ℝ} (hrate : 0 < rate) (hs : 0 ≤ s) (n : ℕ)
    (A : Set (Fin n → ℝ)) :
    fixedPrefixStraddleEvent s n A =ᵐ[exponentialInterarrivalMeasure rate]
      renewalCountPrefixFiber s n A := by
  filter_upwards [ae_fixedStraddleEvent_eq_renewalCountFiber hrate hs n] with ω hstraddle
  apply propext
  change
    (prefixInterarrival n ω ∈ A ∧ fixedStraddleEvent s n ω) ↔
      (canonicalRenewalCount s ω = n ∧ prefixInterarrival n ω ∈ A)
  constructor
  · rintro ⟨hprefix, hfixed⟩
    exact ⟨hstraddle.mp hfixed, hprefix⟩
  · rintro ⟨hcount, hprefix⟩
    exact ⟨hprefix, hstraddle.mpr hcount⟩

private theorem ae_fixedPrefixStraddleFirstGapResidualEvent_eq_renewalCountPrefixResidualTailFiber
    {rate s : ℝ} (hrate : 0 < rate) (hs : 0 ≤ s) (n : ℕ)
    (A : Set (Fin n → ℝ)) (B : Set (ℕ → ℝ)) :
    fixedPrefixStraddleFirstGapResidualEvent s n A B =ᵐ[
      exponentialInterarrivalMeasure rate]
      renewalCountPrefixResidualTailFiber s n A B := by
  filter_upwards [ae_fixedPrefixStraddleEvent_eq_renewalCountPrefixFiber
    hrate hs n A] with ω hstraddle
  apply propext
  change
    (prefixInterarrival n ω ∈ A ∧ fixedStraddleEvent s n ω ∧
      firstGapResidualTail (s - arrivalPrefix n ω) (futureInterarrival n ω) ∈ B) ↔
      (canonicalRenewalCount s ω = n ∧ prefixInterarrival n ω ∈ A ∧ residualTail s ω ∈ B)
  constructor
  · rintro ⟨hprefix, hfixed, hfirst⟩
    have hcount : canonicalRenewalCount s ω = n := hstraddle.mp ⟨hprefix, hfixed⟩ |>.1
    refine ⟨hcount, hprefix, ?_⟩
    rw [residualTail_eq_firstGapResidualTail_of_count_eq s ω n hcount]
    exact hfirst
  · rintro ⟨hcount, hprefix, hresidual⟩
    have hfixed : fixedStraddleEvent s n ω :=
      (hstraddle.mpr ⟨hcount, hprefix⟩).2
    refine ⟨hprefix, hfixed, ?_⟩
    rw [← residualTail_eq_firstGapResidualTail_of_count_eq s ω n hcount]
    exact hresidual

/-- On a fixed renewal-count fiber, an arbitrary measurable finite
interarrival prefix is independent of the complete residual tail observed at
a nonnegative deterministic clock. -/
theorem renewalCountPrefix_residualTail_measure_factorization
    {rate s : ℝ} (hrate : 0 < rate) (hs : 0 ≤ s) (n : ℕ)
    (A : Set (Fin n → ℝ)) (hA : MeasurableSet A)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
    exponentialInterarrivalMeasure rate
        (renewalCountPrefixResidualTailFiber s n A B) =
      exponentialInterarrivalMeasure rate B *
        exponentialInterarrivalMeasure rate (renewalCountPrefixFiber s n A) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  calc
    μ (renewalCountPrefixResidualTailFiber s n A B) =
        μ (fixedPrefixStraddleFirstGapResidualEvent s n A B) := by
          exact (measure_congr
            (ae_fixedPrefixStraddleFirstGapResidualEvent_eq_renewalCountPrefixResidualTailFiber
              hrate hs n A B)).symm
    _ = μ B * μ (fixedPrefixStraddleEvent s n A) := by
          simpa [μ] using
            measure_fixedPrefixStraddleFirstGapResidualEvent_factorization
              hrate s n A hA B hB
    _ = μ B * μ (renewalCountPrefixFiber s n A) := by
          rw [measure_congr
            (ae_fixedPrefixStraddleEvent_eq_renewalCountPrefixFiber hrate hs n A)]

/-- Extend a finite interarrival prefix by zeros.  Together with its length,
this gives a fixed codomain representation of a finite arrival history. -/
def paddedInterarrivalPrefix (n : ℕ) (gaps : Fin n → ℝ) : ℕ → ℝ :=
  fun i => if h : i < n then gaps ⟨i, h⟩ else 0

theorem measurable_paddedInterarrivalPrefix (n : ℕ) :
    Measurable (paddedInterarrivalPrefix n) := by
  apply measurable_pi_iff.2
  intro i
  by_cases hi : i < n
  · simp only [paddedInterarrivalPrefix, dif_pos hi]
    exact measurable_pi_apply (X := fun _ : Fin n => ℝ) ⟨i, hi⟩
  · simp only [paddedInterarrivalPrefix, dif_neg hi]
    exact measurable_const

theorem paddedInterarrivalPrefix_prefixInterarrival
    (n : ℕ) (ω : ℕ → ℝ) :
    paddedInterarrivalPrefix n (prefixInterarrival n ω) =
      fun i => if h : i < n then interarrival i ω else 0 := by
  funext i
  by_cases hi : i < n
  · simp [paddedInterarrivalPrefix, prefixInterarrival, hi]
  · simp [paddedInterarrivalPrefix, hi]

/-- The finite arrival history accumulated by a deterministic clock, encoded
by its length and its zero-padded interarrival prefix. -/
def canonicalRenewalPastHistory (s : ℝ) (ω : ℕ → ℝ) : ℕ × (ℕ → ℝ) :=
  (canonicalRenewalCount s ω,
    paddedInterarrivalPrefix (canonicalRenewalCount s ω)
      (prefixInterarrival (canonicalRenewalCount s ω) ω))

theorem measurable_canonicalRenewalPastHistory (s : ℝ) :
    Measurable (canonicalRenewalPastHistory s) := by
  apply (measurable_canonicalRenewalCount s).prodMk
  apply measurable_pi_iff.2
  intro i
  change Measurable (fun ω : ℕ → ℝ => (canonicalRenewalPastHistory s ω).2 i)
  have hcoord : (fun ω : ℕ → ℝ => (canonicalRenewalPastHistory s ω).2 i) =
      fun ω => if i < canonicalRenewalCount s ω then interarrival i ω else 0 := by
    funext ω
    change (paddedInterarrivalPrefix (canonicalRenewalCount s ω)
      (prefixInterarrival (canonicalRenewalCount s ω) ω)) i = _
    rw [paddedInterarrivalPrefix_prefixInterarrival]
    simp
  rw [hcoord]
  exact Measurable.ite
    ((measurable_canonicalRenewalCount s) measurableSet_Ioi)
    (measurable_interarrival i) measurable_const

/-- The residual tail is jointly measurable in a clock value and its
interarrival path.  This is only a measurability result; the stochastic
factorization at a randomized clock is proved separately below. -/
theorem measurable_residualTail_joint :
    Measurable (fun p : ℝ × (ℕ → ℝ) => residualTail p.1 p.2) := by
  apply measurable_pi_iff.2
  intro k
  let h : ∀ p : ℝ × (ℕ → ℝ), ∃ n, canonicalRenewalCount p.1 p.2 = n :=
    fun p => ⟨canonicalRenewalCount p.1 p.2, rfl⟩
  cases k with
  | zero =>
      have hmeas : Measurable (fun p : ℝ × (ℕ → ℝ) =>
          arrivalTime (Nat.find (h p)) p.2) :=
        Measurable.find
          (fun n => (measurable_arrivalTime n).comp measurable_snd)
          (fun n => measurable_canonicalRenewalCount_joint (measurableSet_singleton n)) h
      convert hmeas.sub measurable_fst using 1
      funext p
      have hfind : Nat.find (h p) = canonicalRenewalCount p.1 p.2 :=
        (Nat.find_spec (h p)).symm
      simp [residualTail, hfind]
  | succ k =>
      have hmeas : Measurable (fun p : ℝ × (ℕ → ℝ) =>
          interarrival (Nat.find (h p) + (k + 1)) p.2) :=
        Measurable.find
          (fun n => (measurable_interarrival (n + (k + 1))).comp measurable_snd)
          (fun n => measurable_canonicalRenewalCount_joint (measurableSet_singleton n)) h
      convert hmeas using 1
      funext p
      have hfind : Nat.find (h p) = canonicalRenewalCount p.1 p.2 :=
        (Nat.find_spec (h p)).symm
      simp [residualTail, hfind]

/-- The complete canonical arrival history is jointly measurable in its
clock value and interarrival path. -/
theorem measurable_canonicalRenewalPastHistory_joint :
    Measurable (fun p : ℝ × (ℕ → ℝ) => canonicalRenewalPastHistory p.1 p.2) := by
  apply measurable_canonicalRenewalCount_joint.prodMk
  apply measurable_pi_iff.2
  intro i
  change Measurable (fun p : ℝ × (ℕ → ℝ) =>
    (canonicalRenewalPastHistory p.1 p.2).2 i)
  have hcoord : (fun p : ℝ × (ℕ → ℝ) =>
      (canonicalRenewalPastHistory p.1 p.2).2 i) =
      fun p => if i < canonicalRenewalCount p.1 p.2 then interarrival i p.2 else 0 := by
    funext p
    change (paddedInterarrivalPrefix (canonicalRenewalCount p.1 p.2)
      (prefixInterarrival (canonicalRenewalCount p.1 p.2) p.2)) i = _
    rw [paddedInterarrivalPrefix_prefixInterarrival]
    simp
  rw [hcoord]
  exact Measurable.ite
    (measurable_canonicalRenewalCount_joint measurableSet_Ioi)
    ((measurable_interarrival i).comp measurable_snd) measurable_const

/-- The finite clock history exposed at an external, potentially randomized
nonnegative clock. -/
def externalTimePastHistory
    {β : Type*} (time : β → ℝ) : β × (ℕ → ℝ) → β × (ℕ × (ℕ → ℝ)) :=
  fun z => (z.1, canonicalRenewalPastHistory (time z.1) z.2)

/-- The fresh residual interarrival path exposed at an external, potentially
randomized clock. -/
def externalTimeResidualTail
    {β : Type*} (time : β → ℝ) : β × (ℕ → ℝ) → ℕ → ℝ :=
  fun z => residualTail (time z.1) z.2

theorem measurable_externalTimePastHistory
    {β : Type*} [MeasurableSpace β] (time : β → ℝ) (htime : Measurable time) :
    Measurable (externalTimePastHistory time) := by
  exact measurable_fst.prodMk (measurable_canonicalRenewalPastHistory_joint.comp
    ((htime.comp measurable_fst).prodMk measurable_snd))

theorem measurable_externalTimeResidualTail
    {β : Type*} [MeasurableSpace β] (time : β → ℝ) (htime : Measurable time) :
    Measurable (externalTimeResidualTail time) := by
  exact measurable_residualTail_joint.comp
    ((htime.comp measurable_fst).prodMk measurable_snd)

private theorem measurableSet_renewalCountFiber (s : ℝ) (n : ℕ) :
    MeasurableSet (renewalCountFiber s n) := by
  exact (measurable_canonicalRenewalCount s) (measurableSet_singleton n)

private theorem measurableSet_renewalCountResidualTailFiber
    (s : ℝ) (n : ℕ) (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
    MeasurableSet (renewalCountResidualTailFiber s n B) := by
  exact (measurableSet_renewalCountFiber s n).inter ((measurable_residualTail s) hB)

private theorem renewalCountFiber_pairwiseDisjoint (s : ℝ) :
    Pairwise (Function.onFun Disjoint (renewalCountFiber s)) := by
  intro n m hnm
  refine Set.disjoint_left.2 ?_
  intro ω hn hm
  exact hnm (hn.symm.trans hm)

private theorem renewalCountResidualTailFiber_pairwiseDisjoint
    (s : ℝ) (B : Set (ℕ → ℝ)) :
    Pairwise (Function.onFun Disjoint (renewalCountResidualTailFiber s · B)) := by
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

private theorem iUnion_renewalCountResidualTailFiber_eq_preimage
    (s : ℝ) (B : Set (ℕ → ℝ)) :
    ⋃ n, renewalCountResidualTailFiber s n B = residualTail s ⁻¹' B := by
  ext ω
  simp [renewalCountResidualTailFiber]

private theorem tsum_measure_renewalCountFiber
    {rate s : ℝ} (hrate : 0 < rate) :
    ∑' n : ℕ, exponentialInterarrivalMeasure rate (renewalCountFiber s n) = 1 := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  calc
    ∑' n : ℕ, μ (renewalCountFiber s n) =
        μ (⋃ n : ℕ, renewalCountFiber s n) := by
          symm
          exact measure_iUnion (renewalCountFiber_pairwiseDisjoint s)
            (measurableSet_renewalCountFiber s)
    _ = μ Set.univ := by rw [iUnion_renewalCountFiber_eq_univ]
    _ = 1 := measure_univ

/-- The residual interarrival path observed at a nonnegative deterministic
clock time has the original iid exponential law. -/
theorem residualTail_hasLaw_path
    {rate s : ℝ} (hrate : 0 < rate) (hs : 0 ≤ s) :
    ProbabilityTheory.HasLaw (residualTail s)
      (exponentialInterarrivalMeasure rate) (exponentialInterarrivalMeasure rate) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  refine ⟨(measurable_residualTail s).aemeasurable, ?_⟩
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (measurable_residualTail s) hB]
  change μ (residualTail s ⁻¹' B) = μ B
  calc
    μ (residualTail s ⁻¹' B) =
        μ (⋃ n : ℕ, renewalCountResidualTailFiber s n B) := by
          rw [iUnion_renewalCountResidualTailFiber_eq_preimage]
    _ = ∑' n : ℕ, μ (renewalCountResidualTailFiber s n B) := by
          exact measure_iUnion (renewalCountResidualTailFiber_pairwiseDisjoint s B)
            (fun n => measurableSet_renewalCountResidualTailFiber s n B hB)
    _ = ∑' n : ℕ, μ B * μ (renewalCountFiber s n) := by
          exact tsum_congr
            (measure_renewalCountResidualTailFiber_factorization hrate hs · B hB)
    _ = μ B * ∑' n : ℕ, μ (renewalCountFiber s n) := by
          exact ENNReal.tsum_mul_left
    _ = μ B * 1 := by rw [tsum_measure_renewalCountFiber hrate]
    _ = μ B := by rw [mul_one]

/-- The count accumulated by a nonnegative deterministic clock time is
independent of the complete residual interarrival path after that time. -/
theorem canonicalRenewalCount_indep_residualTail
    {rate s : ℝ} (hrate : 0 < rate) (hs : 0 ≤ s) :
    ProbabilityTheory.IndepFun (canonicalRenewalCount s) (residualTail s)
      (exponentialInterarrivalMeasure rate) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul]
  intro A B hA hB
  let pieces : {n : ℕ // n ∈ A} → Set (ℕ → ℝ) :=
    fun n => renewalCountResidualTailFiber s n.1 B
  let counts : {n : ℕ // n ∈ A} → Set (ℕ → ℝ) :=
    fun n => renewalCountFiber s n.1
  have hpieces_union :
      ⋃ n : {n : ℕ // n ∈ A}, pieces n =
        (canonicalRenewalCount s) ⁻¹' A ∩ residualTail s ⁻¹' B := by
    ext ω
    constructor
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨n, hn⟩
      change canonicalRenewalCount s ω = n.1 ∧ residualTail s ω ∈ B at hn
      refine ⟨?_, hn.2⟩
      change canonicalRenewalCount s ω ∈ A
      rw [hn.1]
      exact n.2
    · rintro ⟨hAω, hBω⟩
      apply Set.mem_iUnion.2
      refine ⟨⟨canonicalRenewalCount s ω, hAω⟩, ?_⟩
      change canonicalRenewalCount s ω = canonicalRenewalCount s ω ∧ residualTail s ω ∈ B
      exact ⟨rfl, hBω⟩
  have hpieces_disjoint : Pairwise (Function.onFun Disjoint pieces) := by
    intro n m hnm
    refine Set.disjoint_left.2 ?_
    intro ω hn hm
    change canonicalRenewalCount s ω = n.1 ∧ residualTail s ω ∈ B at hn
    change canonicalRenewalCount s ω = m.1 ∧ residualTail s ω ∈ B at hm
    exact hnm (Subtype.ext (hn.1.symm.trans hm.1))
  have hpieces_meas : ∀ n : {n : ℕ // n ∈ A}, MeasurableSet (pieces n) := by
    intro n
    exact measurableSet_renewalCountResidualTailFiber s n.1 B hB
  have hcounts_union :
      ⋃ n : {n : ℕ // n ∈ A}, counts n = (canonicalRenewalCount s) ⁻¹' A := by
    ext ω
    constructor
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨n, hn⟩
      change canonicalRenewalCount s ω = n.1 at hn
      change canonicalRenewalCount s ω ∈ A
      rw [hn]
      exact n.2
    · intro hAω
      apply Set.mem_iUnion.2
      refine ⟨⟨canonicalRenewalCount s ω, hAω⟩, ?_⟩
      change canonicalRenewalCount s ω = canonicalRenewalCount s ω
      rfl
  have hcounts_disjoint : Pairwise (Function.onFun Disjoint counts) := by
    intro n m hnm
    refine Set.disjoint_left.2 ?_
    intro ω hn hm
    change canonicalRenewalCount s ω = n.1 at hn
    change canonicalRenewalCount s ω = m.1 at hm
    exact hnm (Subtype.ext (hn.symm.trans hm))
  have hcounts_meas : ∀ n : {n : ℕ // n ∈ A}, MeasurableSet (counts n) := by
    intro n
    exact measurableSet_renewalCountFiber s n.1
  have hresidual : μ (residualTail s ⁻¹' B) = μ B := by
    calc
      μ (residualTail s ⁻¹' B) = (μ.map (residualTail s)) B := by
        exact (Measure.map_apply (measurable_residualTail s) hB).symm
      _ = μ B := by
        simpa [μ] using congrArg (fun ν : Measure (ℕ → ℝ) => ν B)
          (residualTail_hasLaw_path hrate hs).map_eq
  calc
    μ ((canonicalRenewalCount s) ⁻¹' A ∩ residualTail s ⁻¹' B) =
        μ (⋃ n : {n : ℕ // n ∈ A}, pieces n) := by
          rw [hpieces_union]
    _ = ∑' n : {n : ℕ // n ∈ A}, μ (pieces n) := by
          exact measure_iUnion hpieces_disjoint hpieces_meas
    _ = ∑' n : {n : ℕ // n ∈ A}, μ B * μ (counts n) := by
          apply tsum_congr
          intro n
          simpa [pieces, counts] using
            measure_renewalCountResidualTailFiber_factorization hrate hs n.1 B hB
    _ = μ B * ∑' n : {n : ℕ // n ∈ A}, μ (counts n) := by
          exact ENNReal.tsum_mul_left
    _ = μ B * μ (⋃ n : {n : ℕ // n ∈ A}, counts n) := by
          rw [measure_iUnion hcounts_disjoint hcounts_meas]
    _ = μ B * μ ((canonicalRenewalCount s) ⁻¹' A) := by rw [hcounts_union]
    _ = μ ((canonicalRenewalCount s) ⁻¹' A) * μ (residualTail s ⁻¹' B) := by
          rw [hresidual]
          ac_rfl

/-- The complete finite interarrival history accumulated by a nonnegative
deterministic clock is independent of the complete residual tail after that
clock. -/
theorem canonicalRenewalPastHistory_indep_residualTail
    {rate s : ℝ} (hrate : 0 < rate) (hs : 0 ≤ s) :
    ProbabilityTheory.IndepFun (canonicalRenewalPastHistory s) (residualTail s)
      (exponentialInterarrivalMeasure rate) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul]
  intro A B hA hB
  let sectionMap : (n : ℕ) → (Fin n → ℝ) → ℕ × (ℕ → ℝ) :=
    fun n gaps => (n, paddedInterarrivalPrefix n gaps)
  let sections : (n : ℕ) → Set (Fin n → ℝ) :=
    fun n => (sectionMap n) ⁻¹' A
  let pieces : (n : ℕ) → Set (ℕ → ℝ) :=
    fun n => renewalCountPrefixResidualTailFiber s n (sections n) B
  let counts : (n : ℕ) → Set (ℕ → ℝ) :=
    fun n => renewalCountPrefixFiber s n (sections n)
  have hsectionMap_meas : ∀ n : ℕ, Measurable (sectionMap n) := by
    intro n
    exact measurable_const.prodMk (measurable_paddedInterarrivalPrefix n)
  have hsections_meas : ∀ n : ℕ, MeasurableSet (sections n) := by
    intro n
    exact hA.preimage (hsectionMap_meas n)
  have hpieces_union :
      ⋃ n : ℕ, pieces n =
        (canonicalRenewalPastHistory s) ⁻¹' A ∩ residualTail s ⁻¹' B := by
    ext ω
    constructor
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨n, hn⟩
      change canonicalRenewalCount s ω = n ∧ prefixInterarrival n ω ∈ sections n ∧
        residualTail s ω ∈ B at hn
      refine ⟨?_, hn.2.2⟩
      change canonicalRenewalPastHistory s ω ∈ A
      change (canonicalRenewalCount s ω,
        paddedInterarrivalPrefix (canonicalRenewalCount s ω)
          (prefixInterarrival (canonicalRenewalCount s ω) ω)) ∈ A
      rw [hn.1]
      exact hn.2.1
    · rintro ⟨hAω, hBω⟩
      apply Set.mem_iUnion.2
      refine ⟨canonicalRenewalCount s ω, ?_⟩
      change canonicalRenewalCount s ω = canonicalRenewalCount s ω ∧
        prefixInterarrival (canonicalRenewalCount s ω) ω ∈
          sections (canonicalRenewalCount s ω) ∧ residualTail s ω ∈ B
      refine ⟨rfl, ?_, hBω⟩
      change (canonicalRenewalCount s ω,
        paddedInterarrivalPrefix (canonicalRenewalCount s ω)
          (prefixInterarrival (canonicalRenewalCount s ω) ω)) ∈ A
      simpa [canonicalRenewalPastHistory] using hAω
  have hpieces_disjoint : Pairwise (Function.onFun Disjoint pieces) := by
    intro n m hnm
    refine Set.disjoint_left.2 ?_
    intro ω hn hm
    change canonicalRenewalCount s ω = n ∧ prefixInterarrival n ω ∈ sections n ∧
      residualTail s ω ∈ B at hn
    change canonicalRenewalCount s ω = m ∧ prefixInterarrival m ω ∈ sections m ∧
      residualTail s ω ∈ B at hm
    exact hnm (hn.1.symm.trans hm.1)
  have hpieces_meas : ∀ n : ℕ, MeasurableSet (pieces n) := by
    intro n
    exact (measurableSet_renewalCountFiber s n).inter
      (((measurable_prefixInterarrival n) (hsections_meas n)).inter
        ((measurable_residualTail s) hB))
  have hcounts_union :
      ⋃ n : ℕ, counts n = (canonicalRenewalPastHistory s) ⁻¹' A := by
    ext ω
    constructor
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨n, hn⟩
      change canonicalRenewalCount s ω = n ∧ prefixInterarrival n ω ∈ sections n at hn
      change canonicalRenewalPastHistory s ω ∈ A
      change (canonicalRenewalCount s ω,
        paddedInterarrivalPrefix (canonicalRenewalCount s ω)
          (prefixInterarrival (canonicalRenewalCount s ω) ω)) ∈ A
      rw [hn.1]
      exact hn.2
    · intro hAω
      apply Set.mem_iUnion.2
      refine ⟨canonicalRenewalCount s ω, ?_⟩
      change canonicalRenewalCount s ω = canonicalRenewalCount s ω ∧
        prefixInterarrival (canonicalRenewalCount s ω) ω ∈
          sections (canonicalRenewalCount s ω)
      refine ⟨rfl, ?_⟩
      change (canonicalRenewalCount s ω,
        paddedInterarrivalPrefix (canonicalRenewalCount s ω)
          (prefixInterarrival (canonicalRenewalCount s ω) ω)) ∈ A
      simpa [canonicalRenewalPastHistory] using hAω
  have hcounts_disjoint : Pairwise (Function.onFun Disjoint counts) := by
    intro n m hnm
    refine Set.disjoint_left.2 ?_
    intro ω hn hm
    change canonicalRenewalCount s ω = n ∧ prefixInterarrival n ω ∈ sections n at hn
    change canonicalRenewalCount s ω = m ∧ prefixInterarrival m ω ∈ sections m at hm
    exact hnm (hn.1.symm.trans hm.1)
  have hcounts_meas : ∀ n : ℕ, MeasurableSet (counts n) := by
    intro n
    exact (measurableSet_renewalCountFiber s n).inter
      ((measurable_prefixInterarrival n) (hsections_meas n))
  have hresidual : μ (residualTail s ⁻¹' B) = μ B := by
    calc
      μ (residualTail s ⁻¹' B) = (μ.map (residualTail s)) B := by
        exact (Measure.map_apply (measurable_residualTail s) hB).symm
      _ = μ B := by
        simpa [μ] using congrArg (fun ν : Measure (ℕ → ℝ) => ν B)
          (residualTail_hasLaw_path hrate hs).map_eq
  calc
    μ ((canonicalRenewalPastHistory s) ⁻¹' A ∩ residualTail s ⁻¹' B) =
        μ (⋃ n : ℕ, pieces n) := by
          rw [hpieces_union]
    _ = ∑' n : ℕ, μ (pieces n) := by
          exact measure_iUnion hpieces_disjoint hpieces_meas
    _ = ∑' n : ℕ, μ B * μ (counts n) := by
          apply tsum_congr
          intro n
          simpa [pieces, counts] using
            renewalCountPrefix_residualTail_measure_factorization
              hrate hs n (sections n) (hsections_meas n) B hB
    _ = μ B * ∑' n : ℕ, μ (counts n) := by
          exact ENNReal.tsum_mul_left
    _ = μ B * μ (⋃ n : ℕ, counts n) := by
          rw [measure_iUnion hcounts_disjoint hcounts_meas]
    _ = μ B * μ ((canonicalRenewalPastHistory s) ⁻¹' A) := by
          rw [hcounts_union]
    _ = μ ((canonicalRenewalPastHistory s) ⁻¹' A) * μ (residualTail s ⁻¹' B) := by
          rw [hresidual]
          ac_rfl

/-- The complete finite arrival history at time `s` is independent of the
renewal count accrued over every following deterministic interval. -/
theorem canonicalRenewalPastHistory_indep_increment
    {rate s h : ℝ} (hrate : 0 < rate) (hs : 0 ≤ s) (hh : 0 ≤ h) :
    ProbabilityTheory.IndepFun (canonicalRenewalPastHistory s)
      (fun ω => canonicalRenewalCount (s + h) ω - canonicalRenewalCount s ω)
      (exponentialInterarrivalMeasure rate) := by
  have hcomp : ProbabilityTheory.IndepFun (canonicalRenewalPastHistory s)
      (fun ω => canonicalRenewalCount h (residualTail s ω))
      (exponentialInterarrivalMeasure rate) := by
    simpa [Function.comp_def] using
      (canonicalRenewalPastHistory_indep_residualTail hrate hs).comp
        measurable_id (measurable_canonicalRenewalCount h)
  have htail_eq_increment :
      (fun ω => canonicalRenewalCount h (residualTail s ω)) =ᵐ[
        exponentialInterarrivalMeasure rate]
        fun ω => canonicalRenewalCount (s + h) ω - canonicalRenewalCount s ω := by
    filter_upwards [ae_canonicalRenewalCount_increment_eq_residualTailCount hrate s h hh]
      with ω hω
    exact hω.symm
  exact hcomp.congr (Filter.Eventually.of_forall fun _ => rfl)
    htail_eq_increment

/-- An independent external state may be retained together with the complete
arrival history at a deterministic clock; the residual tail still factors as
a fresh exponential-interarrival path. -/
theorem map_external_canonicalRenewalPastHistory_residualTail
    {β : Type*} [MeasurableSpace β] (ν : Measure β) [IsProbabilityMeasure ν]
    {rate s : ℝ} (hrate : 0 < rate) (hs : 0 ≤ s) :
    Measure.map (fun z : β × (ℕ → ℝ) =>
      ((z.1, canonicalRenewalPastHistory s z.2), residualTail s z.2))
      (ν.prod (exponentialInterarrivalMeasure rate)) =
      (ν.prod (Measure.map (canonicalRenewalPastHistory s)
        (exponentialInterarrivalMeasure rate))).prod
        (exponentialInterarrivalMeasure rate) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let H : (ℕ → ℝ) → ℕ × (ℕ → ℝ) := canonicalRenewalPastHistory s
  let R : (ℕ → ℝ) → ℕ → ℝ := residualTail s
  let f : β × (ℕ → ℝ) → (β × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ) :=
    fun z => ((z.1, H z.2), R z.2)
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hH : Measurable H := by
    simpa [H] using measurable_canonicalRenewalPastHistory s
  have hR : Measurable R := by
    simpa [R] using measurable_residualTail s
  letI : IsProbabilityMeasure (Measure.map H μ) :=
    Measure.isProbabilityMeasure_map hH.aemeasurable
  have hpair : Measurable (fun ξ : ℕ → ℝ => (H ξ, R ξ)) := hH.prodMk hR
  have hf : Measurable f := by
    exact ((measurable_fst).prodMk (hH.comp measurable_snd)).prodMk
      (hR.comp measurable_snd)
  let assoc : β × ((ℕ × (ℕ → ℝ)) × (ℕ → ℝ)) →
      (β × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ) :=
    (MeasurableEquiv.prodAssoc :
      (β × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ) ≃ᵐ
        β × ((ℕ × (ℕ → ℝ)) × (ℕ → ℝ))).symm
  let raw : β × (ℕ → ℝ) → β × ((ℕ × (ℕ → ℝ)) × (ℕ → ℝ)) :=
    fun z => (z.1, (H z.2, R z.2))
  have hraw : Measurable raw := measurable_id.prodMap hpair
  have hassoc : Measurable assoc := by
    exact (MeasurableEquiv.prodAssoc :
      (β × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ) ≃ᵐ
        β × ((ℕ × (ℕ → ℝ)) × (ℕ → ℝ))).symm.measurable
  have hHR : Measure.map (fun ξ : ℕ → ℝ => (H ξ, R ξ)) μ =
      (Measure.map H μ).prod μ := by
    calc
      Measure.map (fun ξ : ℕ → ℝ => (H ξ, R ξ)) μ =
          (Measure.map H μ).prod (Measure.map R μ) := by
            exact (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
              hH.aemeasurable hR.aemeasurable).mp
              (canonicalRenewalPastHistory_indep_residualTail hrate hs)
      _ = (Measure.map H μ).prod μ := by
            rw [(residualTail_hasLaw_path hrate hs).map_eq]
  change Measure.map (assoc ∘ raw) (ν.prod μ) =
    (ν.prod (Measure.map H μ)).prod μ
  rw [← Measure.map_map hassoc hraw]
  change Measure.map assoc
    (Measure.map (Prod.map id (fun ξ : ℕ → ℝ => (H ξ, R ξ))) (ν.prod μ)) = _
  rw [← Measure.map_prod_map ν μ measurable_id hpair,
    Measure.map_id, hHR]
  exact (measurePreserving_prodAssoc ν (Measure.map H μ) μ).symm.map_eq

/-- An IID exponential renewal path can be observed at a nonnegative time
chosen by an independent external state.  The entire exposed finite past,
together with that external state, factors from the literal residual path.
This is derived by integrating the deterministic residual-tail factorization
over the external clock value; it is not a strong-Markov axiom. -/
theorem map_externalTimePastHistory_residualTail
    {β : Type*} [MeasurableSpace β] (ν : Measure β) [IsProbabilityMeasure ν]
    {rate : ℝ} (hrate : 0 < rate) (time : β → ℝ) (htime : Measurable time)
    (htime_nonneg : ∀ b, 0 ≤ time b) :
    Measure.map (fun z : β × (ℕ → ℝ) =>
      (externalTimePastHistory time z, externalTimeResidualTail time z))
      (ν.prod (exponentialInterarrivalMeasure rate)) =
      (Measure.map (externalTimePastHistory time)
        (ν.prod (exponentialInterarrivalMeasure rate))).prod
        (exponentialInterarrivalMeasure rate) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let H : β × (ℕ → ℝ) → β × (ℕ × (ℕ → ℝ)) := externalTimePastHistory time
  let R : β × (ℕ → ℝ) → ℕ → ℝ := externalTimeResidualTail time
  let F : β × (ℕ → ℝ) → ((β × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ)) :=
    fun z => (H z, R z)
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hH : Measurable H := by
    simpa [H] using measurable_externalTimePastHistory time htime
  have hR : Measurable R := by
    simpa [R] using measurable_externalTimeResidualTail time htime
  have hF : Measurable F := hH.prodMk hR
  symm
  apply Measure.prod_eq
  intro A B hA hB
  have hSA : MeasurableSet (H ⁻¹' A) := hA.preimage hH
  have hFA : MeasurableSet (F ⁻¹' (A ×ˢ B)) := (hA.prod hB).preimage hF
  have hsection : ∀ b : β,
      μ (Prod.mk b ⁻¹' (F ⁻¹' (A ×ˢ B))) =
        μ (Prod.mk b ⁻¹' (H ⁻¹' A)) * μ B := by
    intro b
    let D : Set (ℕ × (ℕ → ℝ)) := {q | (b, q) ∈ A}
    have hD : MeasurableSet D := hA.preimage (measurable_const.prodMk measurable_id)
    have hindep := canonicalRenewalPastHistory_indep_residualTail
      hrate (htime_nonneg b)
    have hfactor :=
      (ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul).mp hindep D B hD hB
    have htail : μ (residualTail (time b) ⁻¹' B) = μ B := by
      calc
        μ (residualTail (time b) ⁻¹' B) =
            (Measure.map (residualTail (time b)) μ) B := by
              exact (Measure.map_apply (measurable_residualTail (time b)) hB).symm
        _ = μ B := by
              simpa [μ] using congrArg (fun m : Measure (ℕ → ℝ) => m B)
                (residualTail_hasLaw_path hrate (htime_nonneg b)).map_eq
    change μ ({a | (b, canonicalRenewalPastHistory (time b) a) ∈ A} ∩
      residualTail (time b) ⁻¹' B) =
      μ {a | (b, canonicalRenewalPastHistory (time b) a) ∈ A} * μ B
    simpa [μ, D, htail] using hfactor
  calc
    Measure.map F (ν.prod μ) (A ×ˢ B) =
        (ν.prod μ) (F ⁻¹' (A ×ˢ B)) := by
          exact Measure.map_apply hF (hA.prod hB)
    _ = ∫⁻ b, μ (Prod.mk b ⁻¹' (F ⁻¹' (A ×ˢ B))) ∂ν := by
      rw [Measure.prod_apply hFA]
    _ = ∫⁻ b, μ (Prod.mk b ⁻¹' (H ⁻¹' A)) * μ B ∂ν := by
      apply lintegral_congr
      intro b
      exact hsection b
    _ = (∫⁻ b, μ (Prod.mk b ⁻¹' (H ⁻¹' A)) ∂ν) * μ B := by
      exact lintegral_mul_const (μ := ν) (μ B)
        (measurable_measure_prodMk_left hSA)
    _ = (ν.prod μ) (H ⁻¹' A) * μ B := by
      rw [Measure.prod_apply hSA]
    _ = Measure.map H (ν.prod μ) A * μ B := by
      rw [Measure.map_apply hH hA]

/-- The count accumulated by time `s` is independent of the count increment
over the following deterministic interval of length `h`. -/
theorem canonicalRenewalCount_indep_increment
    {rate s h : ℝ} (hrate : 0 < rate) (hs : 0 ≤ s) (hh : 0 ≤ h) :
    ProbabilityTheory.IndepFun (canonicalRenewalCount s)
      (fun ω => canonicalRenewalCount (s + h) ω - canonicalRenewalCount s ω)
      (exponentialInterarrivalMeasure rate) := by
  have hcomp : ProbabilityTheory.IndepFun (canonicalRenewalCount s)
      (fun ω => canonicalRenewalCount h (residualTail s ω))
      (exponentialInterarrivalMeasure rate) := by
    simpa [Function.comp_def] using
      (canonicalRenewalCount_indep_residualTail hrate hs).comp
        measurable_id (measurable_canonicalRenewalCount h)
  have htail_eq_increment :
      (fun ω => canonicalRenewalCount h (residualTail s ω)) =ᵐ[
        exponentialInterarrivalMeasure rate]
        fun ω => canonicalRenewalCount (s + h) ω - canonicalRenewalCount s ω := by
    filter_upwards [ae_canonicalRenewalCount_increment_eq_residualTailCount hrate s h hh]
      with ω hω
    exact hω.symm
  exact hcomp.congr (Filter.Eventually.of_forall fun _ => rfl)
    htail_eq_increment

/-- A canonical exponential renewal count has Poisson-distributed increments
over every nonnegative deterministic interval. -/
theorem canonicalRenewalCount_increment_hasLaw_poisson
    {rate s h : ℝ} (hrate : 0 < rate) (hs : 0 ≤ s) (hh : 0 ≤ h) :
    ProbabilityTheory.HasLaw
      (fun ω => canonicalRenewalCount (s + h) ω - canonicalRenewalCount s ω)
      (ProbabilityTheory.poissonMeasure
        (⟨rate * h, mul_nonneg hrate.le hh⟩ : ℝ≥0))
      (exponentialInterarrivalMeasure rate) := by
  exact canonicalRenewalCount_increment_hasLaw_poisson_of_residualTail_hasLaw
    hrate s h hh (residualTail_hasLaw_path hrate hs)

/-- Exact deterministic-interval compensation for a Poisson renewal count.
An arbitrary independent external state and the complete arrival history
through `s` may choose the multiplier; the following count increment then
contributes its Poisson mean `rate * h`. -/
theorem integral_externalCanonicalRenewalPastHistorySelector_mul_increment
    {β : Type*} [MeasurableSpace β] (ν : Measure β) [IsProbabilityMeasure ν]
    {rate s h : ℝ} (hrate : 0 < rate) (hs : 0 ≤ s) (hh : 0 ≤ h)
    (f : β × (ℕ × (ℕ → ℝ)) → ℝ) (hf : Measurable f) :
    ∫ z, f (z.1, canonicalRenewalPastHistory s z.2) *
        ((canonicalRenewalCount (s + h) z.2 - canonicalRenewalCount s z.2 : ℕ) : ℝ)
        ∂(ν.prod (exponentialInterarrivalMeasure rate)) =
      (∫ z, f (z.1, canonicalRenewalPastHistory s z.2)
        ∂(ν.prod (exponentialInterarrivalMeasure rate))) * (rate * h) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let H : (ℕ → ℝ) → ℕ × (ℕ → ℝ) := canonicalRenewalPastHistory s
  let R : (ℕ → ℝ) → ℕ → ℝ := residualTail s
  let L : β × (ℕ → ℝ) → β × (ℕ × (ℕ → ℝ)) := fun z => (z.1, H z.2)
  let T : β × (ℕ → ℝ) → ℕ → ℝ := fun z => R z.2
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hH : Measurable H := by
    simpa [H] using measurable_canonicalRenewalPastHistory s
  have hR : Measurable R := by
    simpa [R] using measurable_residualTail s
  have hL : Measurable L := by
    exact measurable_fst.prodMk (hH.comp measurable_snd)
  have hT : Measurable T := by
    exact hR.comp measurable_snd
  have hmapL : Measure.map L (ν.prod μ) = ν.prod (Measure.map H μ) := by
    change Measure.map (Prod.map id H) (ν.prod μ) = ν.prod (Measure.map H μ)
    rw [← Measure.map_prod_map ν μ measurable_id hH, Measure.map_id]
  have hmapT : Measure.map T (ν.prod μ) = μ := by
    calc
      Measure.map T (ν.prod μ) = Measure.map R (Measure.map Prod.snd (ν.prod μ)) := by
        rw [Measure.map_map hR measurable_snd]
        rfl
      _ = Measure.map R μ := by
        rw [Measure.map_snd_prod, measure_univ, one_smul]
      _ = μ := by
        simpa [μ, R] using (residualTail_hasLaw_path hrate hs).map_eq
  have hindTail : ProbabilityTheory.IndepFun L T (ν.prod μ) := by
    apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      hL.aemeasurable hT.aemeasurable).mpr
    calc
      Measure.map (fun z : β × (ℕ → ℝ) => (L z, T z)) (ν.prod μ) =
          (ν.prod (Measure.map H μ)).prod μ := by
            simpa [L, T, H, R, μ] using
              (map_external_canonicalRenewalPastHistory_residualTail ν hrate hs)
      _ = (Measure.map L (ν.prod μ)).prod (Measure.map T (ν.prod μ)) := by
            rw [hmapL, hmapT]
  have hindCount : ProbabilityTheory.IndepFun
      (fun z : β × (ℕ → ℝ) => f (L z))
      (fun z : β × (ℕ → ℝ) => (canonicalRenewalCount h (T z) : ℝ))
      (ν.prod μ) := by
    exact hindTail.comp hf
      ((measurable_of_countable fun n : ℕ => (n : ℝ)).comp
        (measurable_canonicalRenewalCount h))
  have hincrement :
      (fun z : β × (ℕ → ℝ) =>
        (canonicalRenewalCount h (T z) : ℝ)) =ᵐ[ν.prod μ]
        fun z =>
          ((canonicalRenewalCount (s + h) z.2 - canonicalRenewalCount s z.2 : ℕ) : ℝ) := by
    change
      (fun z : β × (ℕ → ℝ) =>
        (canonicalRenewalCount h (residualTail s z.2) : ℝ)) =ᵐ[ν.prod μ]
        fun z =>
          ((canonicalRenewalCount (s + h) z.2 - canonicalRenewalCount s z.2 : ℕ) : ℝ)
    refine ae_of_ae_map (μ := ν.prod μ) (f := Prod.snd)
      (p := fun omega : ℕ → ℝ =>
        (canonicalRenewalCount h (residualTail s omega) : ℝ) =
          ((canonicalRenewalCount (s + h) omega - canonicalRenewalCount s omega : ℕ) : ℝ))
      measurable_snd.aemeasurable ?_
    change ∀ᵐ omega ∂Measure.map Prod.snd (ν.prod μ),
      (canonicalRenewalCount h (R omega) : ℝ) =
        ((canonicalRenewalCount (s + h) omega - canonicalRenewalCount s omega : ℕ) : ℝ)
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    filter_upwards [ae_canonicalRenewalCount_increment_eq_residualTailCount hrate s h hh]
      with omega homega
    exact_mod_cast homega.symm
  have htailIntegral :
      (∫ z : β × (ℕ → ℝ), (canonicalRenewalCount h (T z) : ℝ) ∂(ν.prod μ)) =
        rate * h := by
    calc
      (∫ z : β × (ℕ → ℝ), (canonicalRenewalCount h (T z) : ℝ) ∂(ν.prod μ)) =
          ∫ omega : ℕ → ℝ, (canonicalRenewalCount h (R omega) : ℝ) ∂μ := by
            simpa [T, Function.comp_def] using
              (measurePreserving_snd : MeasurePreserving Prod.snd (ν.prod μ) μ).hasLaw.integral_comp
                (f := fun omega : ℕ → ℝ => (canonicalRenewalCount h (R omega) : ℝ))
                ((measurable_of_countable fun n : ℕ => (n : ℝ)).comp
                  ((measurable_canonicalRenewalCount h).comp hR)).aestronglyMeasurable
      _ = ∫ omega : ℕ → ℝ, (canonicalRenewalCount h omega : ℝ) ∂μ := by
            simpa [μ, R, Function.comp_def] using
              (residualTail_hasLaw_path hrate hs).integral_comp
                (f := fun omega : ℕ → ℝ => (canonicalRenewalCount h omega : ℝ))
                ((measurable_of_countable fun n : ℕ => (n : ℝ)).comp
                  (measurable_canonicalRenewalCount h)).aestronglyMeasurable
      _ = rate * h := by
            simpa [μ] using integral_canonicalRenewalCount hrate hh
  calc
    ∫ z, f (z.1, canonicalRenewalPastHistory s z.2) *
        ((canonicalRenewalCount (s + h) z.2 - canonicalRenewalCount s z.2 : ℕ) : ℝ)
        ∂(ν.prod (exponentialInterarrivalMeasure rate)) =
        ∫ z : β × (ℕ → ℝ), f (L z) * (canonicalRenewalCount h (T z) : ℝ) ∂(ν.prod μ) := by
          apply integral_congr_ae
          filter_upwards [hincrement] with z hz
          simp only [L, H]
          rw [hz]
    _ = (∫ z : β × (ℕ → ℝ), f (L z) ∂(ν.prod μ)) *
          (∫ z : β × (ℕ → ℝ), (canonicalRenewalCount h (T z) : ℝ) ∂(ν.prod μ)) := by
          simpa using hindCount.integral_mul_eq_mul_integral
            (hf.comp hL).aestronglyMeasurable
            (((measurable_of_countable fun n : ℕ => (n : ℝ)).comp
              ((measurable_canonicalRenewalCount h).comp hT)).aestronglyMeasurable)
    _ = (∫ z, f (z.1, canonicalRenewalPastHistory s z.2) ∂(ν.prod μ)) *
          (rate * h) := by
          simpa [μ, L, H] using congrArg (fun x =>
            (∫ z : β × (ℕ → ℝ), f (L z) ∂(ν.prod μ)) * x) htailIntegral
    _ = _ := by rfl

end
end AppliedModelingLib.Probability.PoissonProcess
