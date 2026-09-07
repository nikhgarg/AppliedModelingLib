import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalBoundedStopping
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalRenewalCount
import AppliedModelingLib.Foundations.Probability.ExponentialMoments
import AppliedModelingLib.Foundations.Probability.IidStateWeightedStoppedReward

/-!
# Capped exit indices for canonical exponential interarrivals

This module gives a finite-prefix version of the first canonical arrival
strictly after a prescribed time.  The cap makes every level decision finite
and exposes the overflow event separately.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open Filter MeasureTheory ProbabilityTheory

noncomputable section

/-- Read the arrival time at `index` from a visible interarrival prefix through
`bound`. -/
def interarrivalPrefixArrivalTime (bound index : ℕ) (hindex : index ≤ bound) :
    (Finset.range (bound + 1) → ℝ) → ℝ :=
  fun visible => ∑ i : Finset.range (index + 1),
    visible ⟨i, Finset.mem_range.mpr (by
      exact Nat.lt_of_lt_of_le (Finset.mem_range.mp i.2) (Nat.succ_le_succ hindex))⟩

/-- The finite arrival-time read from a visible prefix is measurable. -/
theorem measurable_interarrivalPrefixArrivalTime (bound index : ℕ)
    (hindex : index ≤ bound) :
    Measurable (interarrivalPrefixArrivalTime bound index hindex) := by
  unfold interarrivalPrefixArrivalTime
  apply Finset.measurable_sum
  intro i _
  let j : Finset.range (bound + 1) := ⟨(i : ℕ), Finset.mem_range.mpr (by
    exact Nat.lt_of_lt_of_le (Finset.mem_range.mp i.2) (Nat.succ_le_succ hindex))⟩
  exact measurable_pi_apply j

/-- Reading an arrival time from a sufficiently long prefix agrees with the
literal arrival time on the original interarrival path. -/
theorem interarrivalPrefixArrivalTime_apply
    (bound index : ℕ) (hindex : index ≤ bound) (omega : ℕ → ℝ) :
    interarrivalPrefixArrivalTime bound index hindex (interarrivalPrefix bound omega) =
      arrivalTime index omega := by
  classical
  unfold interarrivalPrefixArrivalTime interarrivalPrefix arrivalTime interarrival
  simp [Finset.sum_attach]

/-- The first arrival index below `cap` that lies strictly after `time`, with
the cap itself returned when no such finite index exists. -/
noncomputable def cappedRenewalExitIndex (time : ℝ) (cap : ℕ) :
    (ℕ → ℝ) → ℕ := by
  classical
  exact fun omega => if h : ∃ index < cap, time < arrivalTime index omega
    then Nat.find h else cap

/-- A capped renewal exit never exceeds its finite cap. -/
theorem cappedRenewalExitIndex_le_cap (time : ℝ) (cap : ℕ) (omega : ℕ → ℝ) :
    cappedRenewalExitIndex time cap omega ≤ cap := by
  classical
  unfold cappedRenewalExitIndex
  split_ifs with h
  · exact Nat.le_of_lt (Nat.find_spec h).1
  · rfl

/-- Below the cap, the capped exit index has the usual first-exit
characterization. -/
theorem cappedRenewalExitIndex_eq_iff_of_lt
    (time : ℝ) (cap m : ℕ) (omega : ℕ → ℝ) (hm : m < cap) :
    cappedRenewalExitIndex time cap omega = m ↔
      time < arrivalTime m omega ∧
        ∀ index < m, ¬ time < arrivalTime index omega := by
  classical
  constructor
  · intro hindex
    by_cases hexit : ∃ index < cap, time < arrivalTime index omega
    · rw [cappedRenewalExitIndex, dif_pos hexit] at hindex
      rcases (Nat.find_eq_iff hexit).mp hindex with ⟨⟨_, hmexit⟩, hminimal⟩
      refine ⟨hmexit, ?_⟩
      intro index hindex_lt htime
      exact hminimal index hindex_lt ⟨Nat.lt_trans hindex_lt hm, htime⟩
    · rw [cappedRenewalExitIndex, dif_neg hexit] at hindex
      exact False.elim (Nat.ne_of_lt hm hindex.symm)
  · rintro ⟨hmexit, hminimal⟩
    have hexit : ∃ index < cap, time < arrivalTime index omega :=
      ⟨m, hm, hmexit⟩
    rw [cappedRenewalExitIndex, dif_pos hexit]
    apply (Nat.find_eq_iff hexit).mpr
    refine ⟨⟨hm, hmexit⟩, ?_⟩
    intro index hindex_lt hindex_exit
    exact hminimal index hindex_lt hindex_exit.2

/-- The capped index reaches its cap precisely when no earlier finite arrival
lies strictly after the prescribed time. -/
theorem cappedRenewalExitIndex_eq_cap_iff
    (time : ℝ) (cap : ℕ) (omega : ℕ → ℝ) :
    cappedRenewalExitIndex time cap omega = cap ↔
      ∀ index < cap, ¬ time < arrivalTime index omega := by
  classical
  constructor
  · intro hindex index hindex_lt htime
    have hexit : ∃ index < cap, time < arrivalTime index omega :=
      ⟨index, hindex_lt, htime⟩
    rw [cappedRenewalExitIndex, dif_pos hexit] at hindex
    have hfind_lt : Nat.find hexit < cap := (Nat.find_spec hexit).1
    exact (Nat.ne_of_lt hfind_lt hindex)
  · intro hnone
    have hexit : ¬ ∃ index < cap, time < arrivalTime index omega := by
      rintro ⟨index, hindex_lt, htime⟩
      exact hnone index hindex_lt htime
    rw [cappedRenewalExitIndex, dif_neg hexit]

/-- Whenever the full canonical renewal count falls below the cap, the capped
finite-prefix exit agrees exactly with that canonical count. -/
theorem cappedRenewalExitIndex_eq_canonicalRenewalCount_of_lt
    (time : ℝ) (cap : ℕ) (omega : ℕ → ℝ)
    (hfuture : ∃ index : ℕ, time < arrivalTime index omega)
    (hcap : canonicalRenewalCount time omega < cap) :
    cappedRenewalExitIndex time cap omega = canonicalRenewalCount time omega := by
  let count := canonicalRenewalCount time omega
  have hcount_exit : time < arrivalTime count omega := by
    simpa [count] using lt_arrivalTime_canonicalRenewalCount time omega hfuture
  have hcount_minimal : ∀ index < count, ¬ time < arrivalTime index omega := by
    intro index hindex htime
    exact (not_lt_of_ge
      (arrivalTime_le_of_lt_canonicalRenewalCount time omega hfuture hindex)) htime
  exact (cappedRenewalExitIndex_eq_iff_of_lt time cap count omega
    (by simpa [count] using hcap)).mpr ⟨hcount_exit, hcount_minimal⟩

/-- The capped first-exit rule is a bounded prefix stopping index.  Its
level event only inspects the interarrival coordinates through that level. -/
noncomputable def cappedRenewalExitBoundedPrefixStoppingIndex
    (time : ℝ) (cap : ℕ) : BoundedPrefixStoppingIndex cap where
  toFun := cappedRenewalExitIndex time cap
  le_bound := cappedRenewalExitIndex_le_cap time cap
  event_prefix_measurable := by
    intro level hlevel
    rcases Nat.lt_or_eq_of_le hlevel with hlt | rfl
    · let U : Set (Finset.range (level + 1) → ℝ) :=
        {visible | time < interarrivalPrefixArrivalTime level level (le_rfl) visible ∧
          ∀ index (hindex : index < level), ¬ time <
            interarrivalPrefixArrivalTime level index (Nat.le_of_lt hindex) visible}
      have hfirst : MeasurableSet
          {visible : Finset.range (level + 1) → ℝ |
            time < interarrivalPrefixArrivalTime level level (le_rfl) visible} :=
        measurableSet_lt measurable_const
          (measurable_interarrivalPrefixArrivalTime level level (le_rfl))
      have hprevious : ∀ index (hindex : index < level), MeasurableSet
          {visible : Finset.range (level + 1) → ℝ |
            time < interarrivalPrefixArrivalTime level index (Nat.le_of_lt hindex) visible} := by
        intro index hindex
        exact measurableSet_lt measurable_const
          (measurable_interarrivalPrefixArrivalTime level index (Nat.le_of_lt hindex))
      have hU : MeasurableSet U := by
        let V : Set (Finset.range (level + 1) → ℝ) := ⋂ index,
          ⋂ hindex : index < level,
            {visible | time < interarrivalPrefixArrivalTime level index
              (Nat.le_of_lt hindex) visible}ᶜ
        have hV : MeasurableSet V := by
          dsimp only [V]
          exact MeasurableSet.iInter fun index =>
            MeasurableSet.iInter fun hindex => (hprevious index hindex).compl
        have hUeq : U =
            {visible | time < interarrivalPrefixArrivalTime level level (le_rfl) visible} ∩ V := by
          ext visible
          simp only [U, V, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
            Set.mem_compl_iff]
        rw [hUeq]
        exact hfirst.inter hV
      refine ⟨U, hU, ?_⟩
      ext omega
      change
        (time < interarrivalPrefixArrivalTime level level (le_rfl)
            (interarrivalPrefix level omega) ∧
          ∀ index (hindex : index < level), ¬ time < interarrivalPrefixArrivalTime level index
            (Nat.le_of_lt hindex) (interarrivalPrefix level omega)) ↔
          cappedRenewalExitIndex time cap omega = level
      rw [cappedRenewalExitIndex_eq_iff_of_lt time cap level omega hlt]
      simp_rw [interarrivalPrefixArrivalTime_apply]
    · let U : Set (Finset.range (level + 1) → ℝ) :=
        {visible | ∀ index (hindex : index < level), ¬ time <
          interarrivalPrefixArrivalTime level index (Nat.le_of_lt hindex) visible}
      have hprevious : ∀ index (hindex : index < level), MeasurableSet
          {visible : Finset.range (level + 1) → ℝ |
            time < interarrivalPrefixArrivalTime level index (Nat.le_of_lt hindex) visible} := by
        intro index hindex
        exact measurableSet_lt measurable_const
          (measurable_interarrivalPrefixArrivalTime level index (Nat.le_of_lt hindex))
      have hU : MeasurableSet U := by
        let V : Set (Finset.range (level + 1) → ℝ) := ⋂ index,
          ⋂ hindex : index < level,
            {visible | time < interarrivalPrefixArrivalTime level index
              (Nat.le_of_lt hindex) visible}ᶜ
        have hV : MeasurableSet V := by
          dsimp only [V]
          exact MeasurableSet.iInter fun index =>
            MeasurableSet.iInter fun hindex => (hprevious index hindex).compl
        have hUeq : U = V := by
          ext visible
          simp only [U, V, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff]
        rw [hUeq]
        exact hV
      refine ⟨U, hU, ?_⟩
      ext omega
      change
        (∀ index (hindex : index < level), ¬ time < interarrivalPrefixArrivalTime level index
          (Nat.le_of_lt hindex) (interarrivalPrefix level omega)) ↔
          cappedRenewalExitIndex time level omega = level
      rw [cappedRenewalExitIndex_eq_cap_iff]
      simp_rw [interarrivalPrefixArrivalTime_apply]

/-- The capped renewal exit can be used as a state-plus-IID prefix stop while
retaining an arbitrary independent external state. -/
noncomputable def cappedRenewalExitStatePrefixStoppingIndex
    {σ : Type*} [MeasurableSpace σ] (time : ℝ) (cap : ℕ) :
    AppliedModelingLib.Probability.IIDStream.StatePrefixStoppingIndex (σ := σ) (α := ℝ) where
  toFun := fun z => cappedRenewalExitIndex time cap z.2
  event_prefix_measurable := by
    intro level
    by_cases hlevel : level ≤ cap
    · let bounded := cappedRenewalExitBoundedPrefixStoppingIndex time cap
      rcases bounded.event_prefix_measurable level hlevel with ⟨u, hu, hpre⟩
      refine ⟨Prod.snd ⁻¹' u, hu.preimage measurable_snd, ?_⟩
      ext z
      change
        AppliedModelingLib.Probability.IIDStream.stateStreamPrefix (σ := σ) (α := ℝ) level z ∈
            Prod.snd ⁻¹' u ↔
          cappedRenewalExitIndex time cap z.2 = level
      change interarrivalPrefix level z.2 ∈ u ↔
        cappedRenewalExitIndex time cap z.2 = level
      exact Set.ext_iff.mp hpre z.2
    · refine ⟨∅, MeasurableSet.empty, ?_⟩
      ext z
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, false_iff]
      exact Nat.ne_of_lt (lt_of_le_of_lt
        (cappedRenewalExitIndex_le_cap time cap z.2) (lt_of_not_ge hlevel))

/-- The lifted state-plus-IID stop leaves the capped renewal index unchanged. -/
theorem cappedRenewalExitStatePrefixStoppingIndex_apply
    {σ : Type*} [MeasurableSpace σ] (time : ℝ) (cap : ℕ)
    (z : σ × (ℕ → ℝ)) :
    cappedRenewalExitStatePrefixStoppingIndex (σ := σ) time cap z =
      cappedRenewalExitIndex time cap z.2 := rfl

/-- A uniformly bounded external coefficient has zero expected finite reward
when it is paired with rate-centered exponential holding times through a
capped renewal exit.  The estimate intentionally keeps the cap visible, so
the clock-overflow event can be controlled separately. -/
theorem integral_truncatedExternalWeightedStoppedReward_centeredExponential_eq_zero
    {σ : Type*} [MeasurableSpace σ] (ρ : Measure σ)
    [IsProbabilityMeasure ρ] {rate : ℝ} (hrate : 0 < rate)
    (time : ℝ) (cap : ℕ)
    (weight : ℕ → σ → ℝ) (hweight : ∀ n, Measurable (weight n))
    (bound : ℝ) (hbound_nonneg : 0 ≤ bound)
    (hbound : ∀ n state, ‖weight n state‖ ≤ bound) :
    ∫ z,
      AppliedModelingLib.Probability.IIDStream.StatePrefixStoppingIndex.truncatedExternalWeightedStoppedReward
          (cappedRenewalExitStatePrefixStoppingIndex (σ := σ) time cap)
          weight (fun x : ℝ => 1 - rate * x) cap z
        ∂(ρ.prod (AppliedModelingLib.Probability.IIDStream.measure
          (ProbabilityTheory.expMeasure rate))) = 0 := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure rate) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  have hreward : Measurable (fun x : ℝ => 1 - rate * x) :=
    measurable_const.sub (measurable_const.mul measurable_id)
  apply AppliedModelingLib.Probability.IIDStream.StatePrefixStoppingIndex.integral_truncatedExternalWeightedStoppedReward_eq_zero_of_integral_eq_zero
      ρ (ProbabilityTheory.expMeasure rate)
      (cappedRenewalExitStatePrefixStoppingIndex (σ := σ) time cap)
      weight (fun x : ℝ => 1 - rate * x) hweight hreward ?_ cap
  · exact AppliedModelingLib.Probability.integral_one_sub_mul_id_expMeasure hrate
  · intro n
    exact AppliedModelingLib.Probability.IIDStream.StatePrefixStoppingIndex.integrable_externalWeighted_continuationEvent_mul_coordinate_of_bound
        ρ (ProbabilityTheory.expMeasure rate)
        (cappedRenewalExitStatePrefixStoppingIndex (σ := σ) time cap) n
        (weight n) (hweight n) bound hbound_nonneg (hbound n)
        (fun x : ℝ => 1 - rate * x) hreward
        (AppliedModelingLib.Probability.integrable_one_sub_mul_id_expMeasure hrate)

end

end AppliedModelingLib.Probability.PoissonProcess
