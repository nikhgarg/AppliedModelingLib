import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalFuture
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalRenewalCount

/-!
# Finite occupation decompositions for renewal-clock step paths

This module records deterministic finite-sum identities for a path observed
through a monotone, nonexplosive renewal clock.  The formulas are independent
of the distribution of the interarrivals.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open Filter MeasureTheory

noncomputable section

/-- On a finite clock horizon, a value read at the renewal count is its
terminal value plus the telescoping jumps whose arrival epochs are still in
the future. -/
theorem canonicalRenewalCount_value_eq_terminal_add_sum_before_arrivals
    (values : ℕ → ℝ) (gaps : ℕ → ℝ)
    (hdiverges : Tendsto (fun index : ℕ => arrivalTime index gaps) atTop atTop)
    (hmono : Monotone (fun index : ℕ => arrivalTime index gaps))
    (time u : ℝ) (hu : u ≤ time) :
    values (canonicalRenewalCount u gaps) =
      values (canonicalRenewalCount time gaps) +
        ∑ index ∈ Finset.range (canonicalRenewalCount time gaps),
          if u < arrivalTime index gaps then values index - values (index + 1) else 0 := by
  let terminal := canonicalRenewalCount time gaps
  let current := canonicalRenewalCount u gaps
  have hcurrent_le_terminal : current ≤ terminal := by
    exact canonicalRenewalCount_monotone_of_tendsto gaps hdiverges hu
  have hthreshold : ∀ index : ℕ,
      index < current ↔ arrivalTime index gaps ≤ u := by
    intro index
    exact lt_canonicalRenewalCount_iff_arrivalTime_le_of_tendsto
      gaps hdiverges hmono u index
  have hfuture : ∀ index : ℕ,
      u < arrivalTime index gaps ↔ current ≤ index := by
    intro index
    constructor
    · intro hbefore
      by_contra hnot
      have hindex : index < current := Nat.lt_of_not_ge hnot
      have harrival : arrivalTime index gaps ≤ u := (hthreshold index).mp hindex
      linarith
    · intro hindex
      by_contra hnot
      have harrival : arrivalTime index gaps ≤ u := le_of_not_gt hnot
      exact (Nat.not_lt_of_ge hindex) ((hthreshold index).mpr harrival)
  have hfilter : (Finset.range terminal).filter (fun index => current ≤ index) =
      Finset.Ico current terminal := by
    ext index
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  have htelescopes : ∀ n : ℕ,
      ∑ index ∈ Finset.range n, (values index - values (index + 1)) =
        values 0 - values n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  calc
    values (canonicalRenewalCount u gaps) = values current := rfl
    _ = values terminal + (values current - values terminal) := by ring
    _ = values terminal + ∑ index ∈ Finset.Ico current terminal,
        (values index - values (index + 1)) := by
          rw [Finset.sum_Ico_eq_sub _ hcurrent_le_terminal]
          rw [htelescopes terminal, htelescopes current]
          ring
    _ = values terminal + ∑ index ∈ Finset.range terminal,
        if current ≤ index then values index - values (index + 1) else 0 := by
          rw [← hfilter, Finset.sum_filter]
    _ = values terminal + ∑ index ∈ Finset.range terminal,
        if u < arrivalTime index gaps then values index - values (index + 1) else 0 := by
          apply congrArg (fun sum => values terminal + sum)
          apply Finset.sum_congr rfl
          intro index hindex
          simp only [hfuture index]
    _ = values (canonicalRenewalCount time gaps) +
        ∑ index ∈ Finset.range (canonicalRenewalCount time gaps),
          if u < arrivalTime index gaps then values index - values (index + 1) else 0 := by
            rfl

/-- A value path read through a monotone nonexplosive renewal clock is
integrable on every finite time interval.  On each such interval the path is
a finite sum of measurable step functions, with the terminal renewal count as
the finite bound. -/
theorem intervalIntegrable_canonicalRenewalCount_value
    (values : ℕ → ℝ) (gaps : ℕ → ℝ)
    (hdiverges : Tendsto (fun index : ℕ => arrivalTime index gaps) atTop atTop)
    (hmono : Monotone (fun index : ℕ => arrivalTime index gaps))
    (first second : ℝ) :
    IntervalIntegrable (fun time : ℝ => values (canonicalRenewalCount time gaps))
      volume first second := by
  let terminal := canonicalRenewalCount (max first second) gaps
  let step : ℕ → ℝ → ℝ := fun index time =>
    if time < arrivalTime index gaps then values index - values (index + 1) else 0
  let representation : ℝ → ℝ := fun time =>
    values terminal + ∑ index ∈ Finset.range terminal, step index time
  have hstep : ∀ index : ℕ,
      IntervalIntegrable (step index) volume first second := by
    intro index
    rw [intervalIntegrable_iff]
    apply Measure.integrableOn_of_bounded (M := |values index - values (index + 1)|)
    · exact ((measure_mono Set.uIoc_subset_uIcc).trans_lt measure_Icc_lt_top).ne
    · exact (Measurable.ite (measurableSet_lt measurable_id measurable_const)
        measurable_const measurable_const).aestronglyMeasurable
    · filter_upwards [] with time
      by_cases htime : time < arrivalTime index gaps <;> simp [step, htime]
  have hsum : ∀ count : ℕ,
      IntervalIntegrable (fun time : ℝ =>
        ∑ index ∈ Finset.range count, step index time) volume first second := by
    intro count
    induction count with
    | zero => simpa using (intervalIntegrable_const (μ := volume) (a := first) (b := second)
      (c := (0 : ℝ)))
    | succ count ih =>
        have hsum_eq : (fun time : ℝ =>
            ∑ index ∈ Finset.range (count + 1), step index time) =
            (fun time : ℝ =>
              (∑ index ∈ Finset.range count, step index time) + step count time) := by
          funext time
          simp [Finset.sum_range_succ]
        rw [hsum_eq]
        exact ih.add (hstep count)
  have hrepresentation : IntervalIntegrable representation volume first second := by
    exact (intervalIntegrable_const (μ := volume) (a := first) (b := second)
      (c := values terminal)).add (hsum terminal)
  apply (IntervalIntegrable.congr ?_) hrepresentation
  intro time htime
  have htime_le : time ≤ max first second := by
    simpa only [Set.mem_uIoc, Set.mem_Ioc] using htime |>.2
  simpa [representation, step, terminal] using
    (canonicalRenewalCount_value_eq_terminal_add_sum_before_arrivals
      values gaps hdiverges hmono (max first second) time htime_le).symm

/-- The physical-time primitive of a renewal-step path is continuous.  This
is the deterministic regularity fact used when a queue-state occupation is
written as an interval integral. -/
theorem continuous_intervalIntegral_canonicalRenewalCount_value
    (values : ℕ → ℝ) (gaps : ℕ → ℝ)
    (hdiverges : Tendsto (fun index : ℕ => arrivalTime index gaps) atTop atTop)
    (hmono : Monotone (fun index : ℕ => arrivalTime index gaps)) :
    Continuous (fun time : ℝ =>
      ∫ u in (0 : ℝ)..time, values (canonicalRenewalCount u gaps)) := by
  exact intervalIntegral.continuous_primitive
    (fun first second => intervalIntegrable_canonicalRenewalCount_value
      values gaps hdiverges hmono first second) 0

private theorem intervalIntegrable_ite_lt_const
    (threshold coefficient horizon : ℝ) (hhorizon : 0 ≤ horizon) :
    IntervalIntegrable (fun time : ℝ => if time < threshold then coefficient else 0)
      volume 0 horizon := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hhorizon]
  apply Measure.integrableOn_of_bounded (M := |coefficient|) (measure_Icc_lt_top.ne)
  · exact (Measurable.ite (measurableSet_lt measurable_id measurable_const)
      measurable_const measurable_const).aestronglyMeasurable
  · filter_upwards [] with time
    by_cases htime : time < threshold <;> simp [htime]

private theorem intervalIntegral_ite_lt_const
    (threshold coefficient horizon : ℝ) (hthreshold_nonneg : 0 ≤ threshold)
    (hthreshold_le_horizon : threshold ≤ horizon) :
    ∫ time in (0 : ℝ)..horizon,
      (if time < threshold then coefficient else 0) = coefficient * threshold := by
  have hae : (fun time : ℝ => if time < threshold then coefficient else 0) =ᵐ[volume]
      (Set.Iic threshold).indicator (fun _ => coefficient) := by
    filter_upwards [show ∀ᵐ time : ℝ ∂volume, time ≠ threshold by
      simp only [ae_iff, not_ne_iff, Set.setOf_eq_eq_singleton, measure_singleton]]
      with time htime
    by_cases hbefore : time < threshold
    · have hle : time ≤ threshold := hbefore.le
      simp [hbefore, Set.indicator, hle]
    · have hafter : threshold < time :=
        lt_of_le_of_ne (le_of_not_gt hbefore) (Ne.symm htime)
      have hnotle : ¬ time ≤ threshold := not_le_of_gt hafter
      simp [hbefore, Set.indicator, hnotle]
  calc
    ∫ time in (0 : ℝ)..horizon,
        (if time < threshold then coefficient else 0) =
        ∫ time in (0 : ℝ)..horizon,
          (Set.Iic threshold).indicator (fun _ => coefficient) time :=
      intervalIntegral.integral_congr_ae (by
        filter_upwards [hae] with time htime _
        exact htime)
    _ = ∫ _time in (0 : ℝ)..threshold, coefficient :=
      intervalIntegral.integral_indicator ⟨hthreshold_nonneg, hthreshold_le_horizon⟩
    _ = coefficient * threshold := by
      rw [intervalIntegral.integral_const]
      ring

/-- The physical-time occupation of a renewal-clock step path is a finite
summation-by-parts expression in its values and arrival epochs. -/
theorem intervalIntegral_canonicalRenewalCount_value_eq_terminal_add_sum_arrivalTime
    (values : ℕ → ℝ) (gaps : ℕ → ℝ)
    (hdiverges : Tendsto (fun index : ℕ => arrivalTime index gaps) atTop atTop)
    (hmono : Monotone (fun index : ℕ => arrivalTime index gaps))
    (harrival_nonneg : ∀ index : ℕ, 0 ≤ arrivalTime index gaps)
    (time : ℝ) (htime : 0 ≤ time) :
    ∫ u in (0 : ℝ)..time, values (canonicalRenewalCount u gaps) =
      values (canonicalRenewalCount time gaps) * time +
        ∑ index ∈ Finset.range (canonicalRenewalCount time gaps),
          (values index - values (index + 1)) * arrivalTime index gaps := by
  let terminal := canonicalRenewalCount time gaps
  let term : ℕ → ℝ → ℝ := fun index u =>
    if u < arrivalTime index gaps then values index - values (index + 1) else 0
  let rhs : ℝ → ℝ := fun u => values terminal + ∑ index ∈ Finset.range terminal,
    term index u
  have harrival_le_time : ∀ index ∈ Finset.range terminal,
      arrivalTime index gaps ≤ time := by
    intro index hindex
    exact (lt_canonicalRenewalCount_iff_arrivalTime_le_of_tendsto
      gaps hdiverges hmono time index).mp (Finset.mem_range.mp hindex)
  have hterm_integrable : ∀ index : ℕ,
      IntervalIntegrable (term index) volume 0 time := by
    intro index
    exact intervalIntegrable_ite_lt_const
      (arrivalTime index gaps) (values index - values (index + 1)) time htime
  have hsum_integrable_range : ∀ n : ℕ, IntervalIntegrable
      (fun u => ∑ index ∈ Finset.range n, term index u) volume 0 time := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have heq : (fun u => ∑ index ∈ Finset.range (n + 1), term index u) =
            (fun u => ∑ index ∈ Finset.range n, term index u) + term n := by
          funext u
          rw [Finset.sum_range_succ]
          rfl
        rw [heq]
        exact ih.add (hterm_integrable n)
  have hsum_integrable : IntervalIntegrable
      (fun u => ∑ index ∈ Finset.range terminal, term index u) volume 0 time :=
    hsum_integrable_range terminal
  have hrhs_integrable : IntervalIntegrable rhs volume 0 time := by
    exact (intervalIntegrable_const (μ := volume)).add hsum_integrable
  have hpoint : ∀ u ∈ Set.Icc (0 : ℝ) time,
      values (canonicalRenewalCount u gaps) = rhs u := by
    intro u hu
    simpa [rhs, term, terminal] using
      canonicalRenewalCount_value_eq_terminal_add_sum_before_arrivals
        values gaps hdiverges hmono time u hu.2
  have hsum_integral :
      (∫ u in (0 : ℝ)..time, ∑ index ∈ Finset.range terminal, term index u) =
        ∑ index ∈ Finset.range terminal, ∫ u in (0 : ℝ)..time, term index u := by
    induction terminal with
    | zero => simp
    | succ n ih =>
        have heq : (fun u => ∑ index ∈ Finset.range (n + 1), term index u) =
            (fun u => ∑ index ∈ Finset.range n, term index u) + term n := by
          funext u
          rw [Finset.sum_range_succ]
          rfl
        rw [heq]
        change (∫ u in (0 : ℝ)..time,
          (∑ index ∈ Finset.range n, term index u) + term n u) = _
        rw [intervalIntegral.integral_add (hsum_integrable_range n)
          (hterm_integrable n), ih, Finset.sum_range_succ]
  calc
    ∫ u in (0 : ℝ)..time, values (canonicalRenewalCount u gaps) =
        ∫ u in (0 : ℝ)..time, rhs u :=
      intervalIntegral.integral_congr (by
        intro u hu
        have hu' : u ∈ Set.Icc (0 : ℝ) time := by
          simpa [Set.uIcc_of_le htime] using hu
        exact hpoint u hu')
    _ = (∫ _u in (0 : ℝ)..time, values terminal) +
          ∫ u in (0 : ℝ)..time, ∑ index ∈ Finset.range terminal, term index u := by
            change (∫ u in (0 : ℝ)..time,
              values terminal + ∑ index ∈ Finset.range terminal, term index u) = _
            rw [intervalIntegral.integral_add (intervalIntegrable_const (μ := volume))
              hsum_integrable]
    _ = values terminal * time +
          ∑ index ∈ Finset.range terminal,
            (values index - values (index + 1)) * arrivalTime index gaps := by
          rw [hsum_integral, intervalIntegral.integral_const]
          have hterm_integral : ∀ index ∈ Finset.range terminal,
              (∫ u in (0 : ℝ)..time, term index u) =
                (values index - values (index + 1)) * arrivalTime index gaps := by
            intro index hindex
            exact intervalIntegral_ite_lt_const
              (arrivalTime index gaps) (values index - values (index + 1)) time
              (harrival_nonneg index) (harrival_le_time index hindex)
          calc
            (time - 0) • values terminal +
                ∑ index ∈ Finset.range terminal, ∫ u in (0 : ℝ)..time, term index u =
                time * values terminal +
                  ∑ index ∈ Finset.range terminal,
                    (values index - values (index + 1)) * arrivalTime index gaps := by
                      rw [smul_eq_mul, sub_zero]
                      apply congrArg (fun sum => time * values terminal + sum)
                      apply Finset.sum_congr rfl
                      intro index hindex
                      exact hterm_integral index hindex
            _ = values terminal * time +
                  ∑ index ∈ Finset.range terminal,
                    (values index - values (index + 1)) * arrivalTime index gaps := by
                      ring
    _ = values (canonicalRenewalCount time gaps) * time +
        ∑ index ∈ Finset.range (canonicalRenewalCount time gaps),
          (values index - values (index + 1)) * arrivalTime index gaps := by
            rfl

/-- Finite summation by parts converts renewal-epoch jumps into the completed
interarrival rewards and the terminal pre-arrival time. -/
theorem sum_value_sub_succ_mul_arrivalTime_eq_sum_value_mul_interarrival_sub_terminal
    (values : ℕ → ℝ) (gaps : ℕ → ℝ) (n : ℕ) :
    ∑ index ∈ Finset.range n,
      (values index - values (index + 1)) * arrivalTime index gaps =
      (∑ index ∈ Finset.range n, values index * interarrival index gaps) -
        values n * arrivalPrefix n gaps := by
  induction n with
  | zero => simp [arrivalPrefix]
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      have harrival : arrivalTime n gaps = arrivalPrefix (n + 1) gaps := by
        rfl
      have hprefix : arrivalPrefix (n + 1) gaps =
          arrivalPrefix n gaps + interarrival n gaps := by
        simp [arrivalPrefix, Finset.sum_range_succ]
      rw [harrival, hprefix]
      ring

/-- A renewal-clock step-path occupation is the reward accumulated over its
completed interarrivals plus its explicitly retained terminal partial gap. -/
theorem intervalIntegral_canonicalRenewalCount_value_eq_sum_interarrival_add_terminal
    (values : ℕ → ℝ) (gaps : ℕ → ℝ)
    (hdiverges : Tendsto (fun index : ℕ => arrivalTime index gaps) atTop atTop)
    (hmono : Monotone (fun index : ℕ => arrivalTime index gaps))
    (harrival_nonneg : ∀ index : ℕ, 0 ≤ arrivalTime index gaps)
    (time : ℝ) (htime : 0 ≤ time) :
    ∫ u in (0 : ℝ)..time, values (canonicalRenewalCount u gaps) =
      (∑ index ∈ Finset.range (canonicalRenewalCount time gaps),
        values index * interarrival index gaps) +
        values (canonicalRenewalCount time gaps) *
          (time - arrivalPrefix (canonicalRenewalCount time gaps) gaps) := by
  rw [intervalIntegral_canonicalRenewalCount_value_eq_terminal_add_sum_arrivalTime
    values gaps hdiverges hmono harrival_nonneg time htime]
  rw [sum_value_sub_succ_mul_arrivalTime_eq_sum_value_mul_interarrival_sub_terminal]
  ring

/-- The difference between a renewal-index reward prefix and its rate-scaled
physical-time occupation is its centered clock reward, with the terminal
residual interval retained explicitly. -/
theorem renewalRewardPrefix_sub_rate_mul_occupation_eq_centeredClock_sub_terminal
    (values : ℕ → ℝ) (gaps : ℕ → ℝ)
    (hdiverges : Tendsto (fun index : ℕ => arrivalTime index gaps) atTop atTop)
    (hmono : Monotone (fun index : ℕ => arrivalTime index gaps))
    (harrival_nonneg : ∀ index : ℕ, 0 ≤ arrivalTime index gaps)
    (rate time : ℝ) (htime : 0 ≤ time) :
    (∑ index ∈ Finset.range (canonicalRenewalCount time gaps), values index) -
        rate * ∫ u in (0 : ℝ)..time, values (canonicalRenewalCount u gaps) =
      (∑ index ∈ Finset.range (canonicalRenewalCount time gaps),
        values index * (1 - rate * interarrival index gaps)) -
        rate * values (canonicalRenewalCount time gaps) *
          (time - arrivalPrefix (canonicalRenewalCount time gaps) gaps) := by
  rw [intervalIntegral_canonicalRenewalCount_value_eq_sum_interarrival_add_terminal
    values gaps hdiverges hmono harrival_nonneg time htime]
  have hcentered :
      (∑ index ∈ Finset.range (canonicalRenewalCount time gaps), values index) -
          rate * (∑ index ∈ Finset.range (canonicalRenewalCount time gaps),
            values index * interarrival index gaps) =
        ∑ index ∈ Finset.range (canonicalRenewalCount time gaps),
          values index * (1 - rate * interarrival index gaps) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro index _
    ring
  calc
    (∑ index ∈ Finset.range (canonicalRenewalCount time gaps), values index) -
        rate * ((∑ index ∈ Finset.range (canonicalRenewalCount time gaps),
          values index * interarrival index gaps) +
          values (canonicalRenewalCount time gaps) *
            (time - arrivalPrefix (canonicalRenewalCount time gaps) gaps)) =
        ((∑ index ∈ Finset.range (canonicalRenewalCount time gaps), values index) -
          rate * (∑ index ∈ Finset.range (canonicalRenewalCount time gaps),
            values index * interarrival index gaps)) -
          rate * values (canonicalRenewalCount time gaps) *
            (time - arrivalPrefix (canonicalRenewalCount time gaps) gaps) := by
              ring
    _ = (∑ index ∈ Finset.range (canonicalRenewalCount time gaps),
          values index * (1 - rate * interarrival index gaps)) -
          rate * values (canonicalRenewalCount time gaps) *
            (time - arrivalPrefix (canonicalRenewalCount time gaps) gaps) := by
              rw [hcentered]

/-- The elapsed portion of the interarrival interval currently straddling a
finite clock time is strictly smaller than that interval. -/
theorem time_sub_arrivalPrefix_canonicalRenewalCount_lt_interarrival
    (time : ℝ) (gaps : ℕ → ℝ)
    (hfuture : ∃ index : ℕ, time < arrivalTime index gaps) :
    time - arrivalPrefix (canonicalRenewalCount time gaps) gaps <
      interarrival (canonicalRenewalCount time gaps) gaps := by
  have hnext := lt_arrivalTime_canonicalRenewalCount time gaps hfuture
  change time - arrivalPrefix (canonicalRenewalCount time gaps) gaps <
    interarrival (canonicalRenewalCount time gaps) gaps
  rw [show arrivalTime (canonicalRenewalCount time gaps) gaps =
      arrivalPrefix (canonicalRenewalCount time gaps + 1) gaps by rfl] at hnext
  rw [show arrivalPrefix (canonicalRenewalCount time gaps + 1) gaps =
      arrivalPrefix (canonicalRenewalCount time gaps) gaps +
        interarrival (canonicalRenewalCount time gaps) gaps by
          simp [arrivalPrefix, Finset.sum_range_succ]] at hnext
  linarith

/-- On a nondecreasing renewal path started at zero, the elapsed portion of
the straddling interval is nonnegative at every nonnegative clock time. -/
theorem zero_le_time_sub_arrivalPrefix_canonicalRenewalCount
    (time : ℝ) (gaps : ℕ → ℝ) (htime : 0 ≤ time)
    (hfuture : ∃ index : ℕ, time < arrivalTime index gaps) :
    0 ≤ time - arrivalPrefix (canonicalRenewalCount time gaps) gaps := by
  let count := canonicalRenewalCount time gaps
  cases hcount : count with
  | zero =>
      simpa [count, hcount, arrivalPrefix] using htime
  | succ index =>
      have hprior : arrivalTime index gaps ≤ time :=
        arrivalTime_le_of_lt_canonicalRenewalCount time gaps hfuture (by
          simpa [count, hcount] using Nat.lt_succ_self index)
      have hprefix : arrivalPrefix (index + 1) gaps = arrivalTime index gaps := by
        rfl
      simpa [count, hcount, hprefix] using sub_nonneg.mpr hprior

/-- A finite union bound for rate-scaled exponential interarrival tails. -/
theorem real_measure_exists_interarrival_rate_mul_gt_le
    {rate z : ℝ} (hrate : 0 < rate) (hz : 0 ≤ z) (count : ℕ) :
    (exponentialInterarrivalMeasure rate).real
      {gaps | ∃ index ≤ count, z < rate * interarrival index gaps} ≤
      (count + 1 : ℝ) * Real.exp (-z) := by
  induction count with
  | zero =>
      exact le_of_eq (by
        simpa using interarrival_rate_mul_tail_toReal hrate 0 hz)
  | succ count ih =>
      norm_num [Nat.cast_add, Nat.cast_one] at ih ⊢
      let earlier : Set (ℕ → ℝ) :=
        {gaps | ∃ index ≤ count, z < rate * interarrival index gaps}
      let current : Set (ℕ → ℝ) :=
        {gaps | z < rate * interarrival (count + 1) gaps}
      have hevent : {gaps | ∃ index ≤ count + 1,
          z < rate * interarrival index gaps} = earlier ∪ current := by
        ext gaps
        constructor
        · rintro ⟨index, hindex, hgap⟩
          rcases Nat.lt_or_eq_of_le hindex with hlt | rfl
          · exact Or.inl ⟨index, Nat.lt_succ_iff.mp hlt, hgap⟩
          · exact Or.inr hgap
        · intro hgap
          rcases hgap with hgap | hgap
          · obtain ⟨index, hindex, hvalue⟩ := hgap
            exact ⟨index, Nat.le_succ_of_le hindex, hvalue⟩
          · exact ⟨count + 1, le_rfl, hgap⟩
      rw [hevent]
      have hearlier : (exponentialInterarrivalMeasure rate).real earlier ≤
          (count + 1 : ℝ) * Real.exp (-z) := by
        simpa [earlier] using ih
      have hcurrent : (exponentialInterarrivalMeasure rate).real current =
          Real.exp (-z) := by
        simpa [current] using interarrival_rate_mul_tail_toReal hrate (count + 1) hz
      calc
        (exponentialInterarrivalMeasure rate).real (earlier ∪ current) ≤
            (exponentialInterarrivalMeasure rate).real earlier +
              (exponentialInterarrivalMeasure rate).real current :=
          measureReal_union_le _ _
        _ ≤ (count + 1 : ℝ) * Real.exp (-z) + Real.exp (-z) := by
          exact add_le_add hearlier (le_of_eq hcurrent)
        _ = ((count + 1 : ℝ) + 1) * Real.exp (-z) := by ring

end

end AppliedModelingLib.Probability.PoissonProcess
