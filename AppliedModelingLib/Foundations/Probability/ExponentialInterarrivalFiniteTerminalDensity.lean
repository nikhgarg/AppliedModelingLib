import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalFiniteDensity
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalUnboundedStopping
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalRenewalCount

/-!
# Canonical finite-horizon exponential-arrival densities

This module transfers the finite terminal-survival density from an iid finite
gap block to the canonical exponential-renewal path.  The result is a
deterministic-horizon, finite-index theorem and does not assert a generic
clock-time strong-Markov property.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

noncomputable section

/-- Reorder a block of `m + 1` gaps into its first `m` gaps and its last gap. -/
def splitLastFiniteGaps (m : ℕ) :
    (Fin (m + 1) → ℝ) → (Fin m → ℝ) × ℝ :=
  Prod.swap ∘ MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (m + 1) => ℝ) (Fin.last m)

theorem measurable_splitLastFiniteGaps (m : ℕ) :
    Measurable (splitLastFiniteGaps m) := by
  exact measurable_swap.comp
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).measurable

/-- The last-gap reordering maps a finite iid exponential block to a prefix block and gap. -/
theorem splitLastFiniteGaps_hasLaw
    {rate : ℝ} (hrate : 0 < rate) (m : ℕ) :
    HasLaw (splitLastFiniteGaps m)
      ((Measure.pi (fun _ : Fin m => expMeasure rate)).prod (expMeasure rate))
      (Measure.pi (fun _ : Fin (m + 1) => expMeasure rate)) := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  refine ⟨(measurable_splitLastFiniteGaps m).aemeasurable, ?_⟩
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (m + 1) => ℝ) (Fin.last m)
  calc
    Measure.map (splitLastFiniteGaps m)
        (Measure.pi (fun _ : Fin (m + 1) => expMeasure rate)) =
        Measure.map Prod.swap
          (Measure.map e (Measure.pi (fun _ : Fin (m + 1) => expMeasure rate))) := by
      rw [Measure.map_map measurable_swap e.measurable]
      rfl
    _ = Measure.map Prod.swap
          ((expMeasure rate).prod (Measure.pi (fun _ : Fin m => expMeasure rate))) := by
      congr 1
      simpa [e, Fin.succAbove_last] using
        (MeasureTheory.measurePreserving_piFinSuccAbove
          (fun _ : Fin (m + 1) => expMeasure rate) (Fin.last m)).map_eq
    _ = (Measure.pi (fun _ : Fin m => expMeasure rate)).prod (expMeasure rate) := by
      exact Measure.prod_swap

/-- The first `m` canonical gaps and one terminal gap, separated into a pair. -/
def canonicalSplitLastFiniteGaps (m : ℕ) : (ℕ → ℝ) → (Fin m → ℝ) × ℝ :=
  splitLastFiniteGaps m ∘ interarrivalBlock 0 (m + 1)

theorem measurable_canonicalSplitLastFiniteGaps (m : ℕ) :
    Measurable (canonicalSplitLastFiniteGaps m) := by
  exact (measurable_splitLastFiniteGaps m).comp
    (measurable_interarrivalBlock 0 (m + 1))

theorem canonicalSplitLastFiniteGaps_hasLaw
    {rate : ℝ} (hrate : 0 < rate) (m : ℕ) :
    HasLaw (canonicalSplitLastFiniteGaps m)
      ((Measure.pi (fun _ : Fin m => expMeasure rate)).prod (expMeasure rate))
      (exponentialInterarrivalMeasure rate) := by
  exact (splitLastFiniteGaps_hasLaw hrate m).comp
    (interarrivalBlock_hasLaw hrate 0 (m + 1))

/-- The canonical finite-gap event of `m` arrivals before a deterministic horizon. -/
def canonicalFiniteArrivalEvent (m : ℕ) (horizon : ℝ) : Set (ℕ → ℝ) :=
  canonicalSplitLastFiniteGaps m ⁻¹'
    terminalSurvivalEvent (finiteGapPrefixTime m)
      (finiteGapPrefixCarrier m horizon) horizon

theorem canonicalFiniteArrivalEvent_measurableSet (m : ℕ) (horizon : ℝ) :
    MeasurableSet (canonicalFiniteArrivalEvent m horizon) := by
  exact (measurable_canonicalSplitLastFiniteGaps m)
    (measurableSet_terminalSurvivalEvent (measurable_finiteGapPrefixTime m)
      (measurableSet_finiteGapPrefixCarrier m horizon))

/--
The canonical cumulative-arrival vector, restricted to a finite terminal
survival event, has the exact arbitrary-finite-count Lebesgue density.
-/
theorem canonical_cumulativeArrival_restrict_finiteTerminal_eq_withDensity
    {rate horizon : ℝ} (hrate : 0 < rate) (m : ℕ) :
    Measure.map (fun ω => cumulativeArrivalVector m (canonicalSplitLastFiniteGaps m ω).1)
      ((exponentialInterarrivalMeasure rate).restrict
        (canonicalFiniteArrivalEvent m horizon)) =
      (volume : Measure (Fin m → ℝ)).withDensity
        (finiteArrivalTerminalDensity rate horizon m) := by
  let X := canonicalSplitLastFiniteGaps m
  let S := terminalSurvivalEvent (finiteGapPrefixTime m)
    (finiteGapPrefixCarrier m horizon) horizon
  let F : (Fin m → ℝ) × ℝ → Fin m → ℝ :=
    fun p => cumulativeArrivalVector m p.1
  have hX : HasLaw X
      ((Measure.pi (fun _ : Fin m => expMeasure rate)).prod (expMeasure rate))
      (exponentialInterarrivalMeasure rate) :=
    canonicalSplitLastFiniteGaps_hasLaw hrate m
  have hXmeas : Measurable X := measurable_canonicalSplitLastFiniteGaps m
  have hS : MeasurableSet S :=
    measurableSet_terminalSurvivalEvent (measurable_finiteGapPrefixTime m)
      (measurableSet_finiteGapPrefixCarrier m horizon)
  have hcum : Measurable (cumulativeArrivalVector m) := by
    have hcoord : cumulativeArrivalVector m = cumulativeArrivalLinearMap m := by
      funext gaps
      exact (cumulativeArrivalLinearMap_apply m gaps).symm
    rw [hcoord]
    exact (LinearMap.continuous_on_pi (cumulativeArrivalLinearMap m)).measurable
  have hF : Measurable F := hcum.comp measurable_fst
  change Measure.map (F ∘ X)
      ((exponentialInterarrivalMeasure rate).restrict (X ⁻¹' S)) =
      (volume : Measure (Fin m → ℝ)).withDensity
        (finiteArrivalTerminalDensity rate horizon m)
  calc
    Measure.map (F ∘ X) ((exponentialInterarrivalMeasure rate).restrict (X ⁻¹' S)) =
        Measure.map F (Measure.map X
          ((exponentialInterarrivalMeasure rate).restrict (X ⁻¹' S))) := by
      simpa using (Measure.map_map hF hXmeas).symm
    _ = Measure.map F
        ((Measure.map X (exponentialInterarrivalMeasure rate)).restrict S) := by
      rw [Measure.restrict_map hXmeas hS]
    _ = Measure.map F
        (((Measure.pi (fun _ : Fin m => expMeasure rate)).prod (expMeasure rate)).restrict S) := by
      rw [hX.map_eq]
    _ = (volume : Measure (Fin m → ℝ)).withDensity
        (finiteArrivalTerminalDensity rate horizon m) := by
      exact map_cumulativeArrival_finiteTerminal_eq_withDensity hrate m

/-- The first `m + 1` canonical gaps together with their next terminal gap. -/
private def canonicalPrefixTerminalBlock (m : ℕ) :
    (ℕ → ℝ) → (Fin (m + 1) → ℝ) × ℝ :=
  fun ω => (interarrivalBlock 0 (m + 1) ω, interarrival (m + 1) ω)

private theorem finiteGapPrefixTime_interarrivalBlock_eq_arrivalTime
    (m : ℕ) (ω : ℕ → ℝ) :
    finiteGapPrefixTime (m + 1) (interarrivalBlock 0 (m + 1) ω) =
      arrivalTime m ω := by
  change (∑ i : Fin (m + 1), interarrival (0 + (i : ℕ)) ω) = arrivalTime m ω
  simp only [Nat.zero_add]
  rw [Fin.sum_univ_eq_sum_range (fun i => interarrival i ω)]
  rfl

private theorem finiteGapPrefixTime_add_terminal_interarrivalBlock_eq_arrivalTime
    (m : ℕ) (ω : ℕ → ℝ) :
    finiteGapPrefixTime (m + 1) (interarrivalBlock 0 (m + 1) ω) +
        interarrival (m + 1) ω =
      arrivalTime (m + 1) ω := by
  rw [finiteGapPrefixTime_interarrivalBlock_eq_arrivalTime]
  simp [arrivalTime, Finset.sum_range_succ]

private theorem canonicalSplitLastFiniteGaps_succ_eq_prefixTerminalBlock (m : ℕ) :
    canonicalSplitLastFiniteGaps (m + 1) = canonicalPrefixTerminalBlock m := by
  funext ω
  ext i <;>
    simp [canonicalSplitLastFiniteGaps, splitLastFiniteGaps, canonicalPrefixTerminalBlock,
      interarrivalBlock, Function.comp_apply, Fin.init_def]

private theorem canonicalFiniteArrivalEvent_zero_eq (horizon : ℝ) :
    canonicalFiniteArrivalEvent 0 horizon =
      {ω | 0 ≤ horizon ∧ horizon < interarrival 0 ω} := by
  ext ω
  simp [canonicalFiniteArrivalEvent, canonicalSplitLastFiniteGaps, splitLastFiniteGaps,
    terminalSurvivalEvent, finiteGapPrefixCarrier, finiteGapPrefixTime,
    interarrivalBlock, Function.comp_apply]

/--
For a nonnegative deterministic horizon, the zero-arrival finite terminal
event is almost surely the zero renewal-count fiber.  Nonexplosion removes
the fallback branch in the definition of `canonicalRenewalCount`.
-/
theorem canonicalFiniteArrivalEvent_zero_ae_eq_renewalCountZero
    {rate horizon : ℝ} (hrate : 0 < rate) (horizon_nonneg : 0 ≤ horizon) :
    canonicalFiniteArrivalEvent 0 horizon =ᵐ[exponentialInterarrivalMeasure rate]
      {ω | canonicalRenewalCount horizon ω = 0} := by
  filter_upwards [ae_arrivalTime_tendsto_atTop hrate] with ω hdiv
  apply propext
  rw [canonicalFiniteArrivalEvent_zero_eq]
  change (0 ≤ horizon ∧ horizon < interarrival 0 ω) ↔
    canonicalRenewalCount horizon ω = 0
  rw [canonicalRenewalCount_eq_zero_iff]
  constructor
  · rintro ⟨_, hfirst⟩
    left
    simpa [arrivalTime_zero] using hfirst
  · intro hcount
    refine ⟨horizon_nonneg, ?_⟩
    rcases hcount with hfirst | hnone
    · simpa [arrivalTime_zero] using hfirst
    · exact (hnone (exists_arrivalTime_gt_of_tendsto_atTop ω hdiv horizon)).elim

/--
Apart from the canonical null set of malformed interarrival paths, the finite
terminal event with `m + 1` arrivals is the ordinary renewal-count fiber.
This is a finite deterministic-horizon identification, not a clock-time
strong-Markov statement.
-/
theorem canonicalFiniteArrivalEvent_succ_ae_eq_renewalCountSucc
    {rate horizon : ℝ} (hrate : 0 < rate) (m : ℕ) :
    canonicalFiniteArrivalEvent (m + 1) horizon =ᵐ[exponentialInterarrivalMeasure rate]
      {ω | canonicalRenewalCount horizon ω = m + 1} := by
  have hsplit : canonicalSplitLastFiniteGaps (m + 1) = canonicalPrefixTerminalBlock m :=
    canonicalSplitLastFiniteGaps_succ_eq_prefixTerminalBlock m
  have hset : canonicalFiniteArrivalEvent (m + 1) horizon =
      canonicalPrefixTerminalBlock m ⁻¹'
        terminalSurvivalEvent (finiteGapPrefixTime (m + 1))
          (finiteGapPrefixCarrier (m + 1) horizon) horizon := by
    unfold canonicalFiniteArrivalEvent
    rw [hsplit]
  rw [hset]
  filter_upwards [ae_all_interarrival_positive hrate] with ω hpos
  apply propext
  change
    canonicalPrefixTerminalBlock m ω ∈
      terminalSurvivalEvent (finiteGapPrefixTime (m + 1))
        (finiteGapPrefixCarrier (m + 1) horizon) horizon ↔
      canonicalRenewalCount horizon ω = m + 1
  simp only [canonicalPrefixTerminalBlock, interarrivalBlock, Nat.zero_add,
    terminalSurvivalEvent, finiteGapPrefixCarrier, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨_hnonneg, hprefix⟩, hterminal⟩
    apply (canonicalRenewalCount_eq_succ_iff horizon ω m).mpr
    refine ⟨?_, ?_⟩
    · rwa [finiteGapPrefixTime_add_terminal_interarrivalBlock_eq_arrivalTime] at hterminal
    · intro k hk
      have hkm : k ≤ m := Nat.le_of_lt_succ hk
      have hle : arrivalTime k ω ≤ arrivalTime m ω :=
        (arrivalTime_strictMono_of_positive ω hpos).monotone hkm
      have hmle : arrivalTime m ω ≤ horizon := by
        rw [finiteGapPrefixTime_interarrivalBlock_eq_arrivalTime] at hprefix
        exact hprefix
      exact not_lt_of_ge (hle.trans hmle)
  · intro hcount
    rw [canonicalRenewalCount_eq_succ_iff] at hcount
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i
      exact (hpos i).le
    · rw [finiteGapPrefixTime_interarrivalBlock_eq_arrivalTime]
      exact le_of_not_gt (hcount.2 m (Nat.lt_succ_self m))
    · rw [finiteGapPrefixTime_add_terminal_interarrivalBlock_eq_arrivalTime]
      exact hcount.1

/--
For a positive finite renewal count, cumulative arrival epochs have the exact
finite terminal density after restricting to the usual count fiber.
-/
theorem canonical_cumulativeArrival_restrict_renewalCountSucc_eq_withDensity
    {rate horizon : ℝ} (hrate : 0 < rate) (m : ℕ) :
    Measure.map (fun ω =>
      cumulativeArrivalVector (m + 1) (canonicalSplitLastFiniteGaps (m + 1) ω).1)
      ((exponentialInterarrivalMeasure rate).restrict
        {ω | canonicalRenewalCount horizon ω = m + 1}) =
      (volume : Measure (Fin (m + 1) → ℝ)).withDensity
        (finiteArrivalTerminalDensity rate horizon (m + 1)) := by
  rw [← Measure.restrict_congr_set
    (canonicalFiniteArrivalEvent_succ_ae_eq_renewalCountSucc hrate m)]
  exact canonical_cumulativeArrival_restrict_finiteTerminal_eq_withDensity hrate (m + 1)

/--
For every finite renewal count at a nonnegative deterministic horizon, the
finite terminal event agrees almost surely with the usual count fiber.
-/
theorem canonicalFiniteArrivalEvent_ae_eq_renewalCountFiber
    {rate horizon : ℝ} (hrate : 0 < rate) (horizon_nonneg : 0 ≤ horizon)
    (count : ℕ) :
    canonicalFiniteArrivalEvent count horizon =ᵐ[exponentialInterarrivalMeasure rate]
      {ω | canonicalRenewalCount horizon ω = count} := by
  cases count with
  | zero =>
      exact canonicalFiniteArrivalEvent_zero_ae_eq_renewalCountZero hrate horizon_nonneg
  | succ m =>
      exact canonicalFiniteArrivalEvent_succ_ae_eq_renewalCountSucc hrate m

/--
At a nonnegative deterministic horizon, every finite canonical renewal-count
fiber has the exact cumulative-arrival Lebesgue density.
-/
theorem canonical_cumulativeArrival_restrict_renewalCount_eq_withDensity
    {rate horizon : ℝ} (hrate : 0 < rate) (horizon_nonneg : 0 ≤ horizon)
    (count : ℕ) :
    Measure.map (fun ω =>
      cumulativeArrivalVector count (canonicalSplitLastFiniteGaps count ω).1)
      ((exponentialInterarrivalMeasure rate).restrict
        {ω | canonicalRenewalCount horizon ω = count}) =
      (volume : Measure (Fin count → ℝ)).withDensity
        (finiteArrivalTerminalDensity rate horizon count) := by
  rw [← Measure.restrict_congr_set
    (canonicalFiniteArrivalEvent_ae_eq_renewalCountFiber hrate horizon_nonneg count)]
  exact canonical_cumulativeArrival_restrict_finiteTerminal_eq_withDensity hrate count

end

end AppliedModelingLib.Probability.PoissonProcess
