import AppliedModelingLib.Foundations.Probability.IidStatePrefixStopping
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Predictable rewards before an IID-prefix stop

This module supplies the capped compensation identity for rewards attached to
IID coordinates that are accrued strictly before a stopping index.  The
decision to accrue coordinate `n` may use an arbitrary independent external
state and all earlier IID coordinates, but not coordinate `n` itself.  This
is the finite, discrete form appropriate for marked renewal arrivals.
-/

namespace AppliedModelingLib.Probability.IIDStream

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

variable {σ α : Type*} [MeasurableSpace σ] [MeasurableSpace α]

/-- A total index whose strict-continuation events are observable before the
corresponding IID reward coordinate. -/
structure PredictableStatePrefixIndex where
  toFun : σ × (ℕ → α) → ℕ
  continuation_zero_measurable :
    MeasurableSet[MeasurableSpace.comap (Prod.fst : σ × (ℕ → α) → σ)
      inferInstance] {z | 0 < toFun z}
  continuation_succ_prefix_measurable : ∀ n,
    MeasurableSet[MeasurableSpace.comap
      (stateStreamPrefix (σ := σ) (α := α) n) inferInstance]
      {z | n + 1 < toFun z}

namespace PredictableStatePrefixIndex

instance : CoeFun (PredictableStatePrefixIndex (σ := σ) (α := α))
    (fun _ => σ × (ℕ → α) → ℕ) := ⟨PredictableStatePrefixIndex.toFun⟩

/-- The predictable event on which coordinate `n` is accrued. -/
def continuationEvent (τ : PredictableStatePrefixIndex (σ := σ) (α := α))
    (n : ℕ) : Set (σ × (ℕ → α)) := {z | n < τ z}

/-- An IID-prefix index determined entirely by independent external data.
This is the generic interface for, for example, the number of arrivals in a
deterministic time window when the associated IID marks are carried in the
stream coordinate. -/
def ofExternalCount (count : σ → ℕ) (hcount : Measurable count) :
    PredictableStatePrefixIndex (σ := σ) (α := α) where
  toFun := fun z => count z.1
  continuation_zero_measurable := by
    let U : Set σ := {s | 0 < count s}
    have hU : MeasurableSet U := by
      change MeasurableSet (count ⁻¹' Set.Ioi 0)
      exact hcount measurableSet_Ioi
    refine MeasurableSpace.measurableSet_comap.2 ⟨U, hU, ?_⟩
    ext z
    rfl
  continuation_succ_prefix_measurable := fun n => by
    let U : Set (σ × (Finset.range (n + 1) → α)) :=
      {s | n + 1 < count s.1}
    have hU : MeasurableSet U := by
      change MeasurableSet ((fun s : σ × (Finset.range (n + 1) → α) =>
        count s.1) ⁻¹' Set.Ioi (n + 1))
      exact (hcount.comp measurable_fst) measurableSet_Ioi
    refine MeasurableSpace.measurableSet_comap.2 ⟨U, hU, ?_⟩
    ext z
    rfl

/-- The external-count constructor leaves the given count unchanged. -/
theorem ofExternalCount_apply (count : σ → ℕ) (hcount : Measurable count)
    (z : σ × (ℕ → α)) :
    ofExternalCount (σ := σ) (α := α) count hcount z = count z.1 := rfl

/-- The continuation event for an external-count index is the corresponding
external count-tail event. -/
theorem continuationEvent_ofExternalCount (count : σ → ℕ) (hcount : Measurable count)
    (n : ℕ) :
    (ofExternalCount (σ := σ) (α := α) count hcount).continuationEvent n =
      {z | n < count z.1} := rfl

/-- Every predictable continuation event is Borel measurable. -/
theorem measurableSet_continuationEvent
    (τ : PredictableStatePrefixIndex (σ := σ) (α := α)) (n : ℕ) :
    MeasurableSet (τ.continuationEvent n) := by
  cases n with
  | zero =>
      rcases τ.continuation_zero_measurable with ⟨u, hu, hpre⟩
      change MeasurableSet {z | 0 < τ z}
      rw [← hpre]
      exact measurable_fst hu
  | succ n =>
      rcases τ.continuation_succ_prefix_measurable n with ⟨u, hu, hpre⟩
      change MeasurableSet {z | n + 1 < τ z}
      rw [← hpre]
      exact (measurable_stateStreamPrefix (σ := σ) (α := α) n) hu

/-- The initial strict-continuation event remains observable after retaining
any longer state-plus-prefix observation. -/
theorem continuation_zero_statePrefix_measurable
    (τ : PredictableStatePrefixIndex (σ := σ) (α := α)) (N : ℕ) :
    MeasurableSet[MeasurableSpace.comap
      (stateStreamPrefix (σ := σ) (α := α) N) inferInstance]
      {z | 0 < τ z} := by
  rcases τ.continuation_zero_measurable with ⟨u, hu, hpre⟩
  refine ⟨Prod.fst ⁻¹' u, hu.preimage measurable_fst, ?_⟩
  change stateStreamPrefix (σ := σ) (α := α) N ⁻¹' (Prod.fst ⁻¹' u) =
    {z | 0 < τ z}
  rw [← hpre]
  ext z
  rfl

/-- A strict-continuation event visible after coordinate `m` remains visible
after every longer inspected prefix. -/
theorem continuation_succ_statePrefix_measurable
    (τ : PredictableStatePrefixIndex (σ := σ) (α := α))
    (m N : ℕ) (hmN : m ≤ N) :
    MeasurableSet[MeasurableSpace.comap
      (stateStreamPrefix (σ := σ) (α := α) N) inferInstance]
      {z | m + 1 < τ z} := by
  rcases τ.continuation_succ_prefix_measurable m with ⟨u, hu, hpre⟩
  refine ⟨(StatePrefixStoppingIndex.statePrefixRestriction (σ := σ) (α := α)
    m N hmN) ⁻¹' u,
    hu.preimage (StatePrefixStoppingIndex.measurable_statePrefixRestriction
      (σ := σ) (α := α) m N hmN), ?_⟩
  change stateStreamPrefix (σ := σ) (α := α) N ⁻¹'
      ((StatePrefixStoppingIndex.statePrefixRestriction (σ := σ) (α := α)
        m N hmN) ⁻¹' u) =
    {z | m + 1 < τ z}
  rw [← hpre]
  ext z
  change (StatePrefixStoppingIndex.statePrefixRestriction (σ := σ) (α := α)
    m N hmN ∘ stateStreamPrefix (σ := σ) (α := α) N) z ∈ u ↔
      stateStreamPrefix (σ := σ) (α := α) m z ∈ u
  rw [StatePrefixStoppingIndex.statePrefixRestriction_stateStreamPrefix]

/-- A predictable strict-continuation index is also a total prefix stopping
index.  This adapter exposes the complete IID restart law at its stopping
time; it does not add an independence claim from the stopped history. -/
def toStatePrefixStoppingIndex
    (τ : PredictableStatePrefixIndex (σ := σ) (α := α)) :
    StatePrefixStoppingIndex (σ := σ) (α := α) where
  toFun := τ
  event_prefix_measurable := by
    intro N
    cases N with
    | zero =>
        have hcont := τ.continuation_zero_statePrefix_measurable 0
        have hevent : {z : σ × (ℕ → α) | τ z = 0} = {z | 0 < τ z}ᶜ := by
          ext z
          simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
          omega
        rw [hevent]
        exact hcont.compl
    | succ N =>
        have hle : MeasurableSet[MeasurableSpace.comap
            (stateStreamPrefix (σ := σ) (α := α) (N + 1)) inferInstance]
            {z | N < τ z} := by
          cases N with
          | zero =>
              simpa using τ.continuation_zero_statePrefix_measurable 1
          | succ m =>
              simpa [Nat.succ_eq_add_one] using
                τ.continuation_succ_statePrefix_measurable m (m + 2)
                  (Nat.le_add_right m 2)
        have hgt : MeasurableSet[MeasurableSpace.comap
            (stateStreamPrefix (σ := σ) (α := α) (N + 1)) inferInstance]
            {z | N + 1 < τ z} := by
          simpa using τ.continuation_succ_statePrefix_measurable N (N + 1)
            (Nat.le_succ N)
        have hevent : {z : σ × (ℕ → α) | τ z = N + 1} =
            {z | N < τ z} \ {z | N + 1 < τ z} := by
          ext z
          simp only [Set.mem_diff, Set.mem_setOf_eq]
          omega
        rw [hevent]
        exact hle.diff hgt

/-- The stopping-index adapter leaves the underlying index function unchanged. -/
theorem toStatePrefixStoppingIndex_apply
    (τ : PredictableStatePrefixIndex (σ := σ) (α := α))
    (z : σ × (ℕ → α)) :
    τ.toStatePrefixStoppingIndex z = τ z := rfl

/-- A predictable strict-continuation index is Borel measurable as a
natural-valued function. -/
theorem measurable (τ : PredictableStatePrefixIndex (σ := σ) (α := α)) :
    Measurable τ := by
  simpa only [toStatePrefixStoppingIndex_apply] using τ.toStatePrefixStoppingIndex.measurable

/-- The reward accumulated strictly before a predictable index, truncated at
a deterministic coordinate cap. -/
def truncatedStrictStoppedReward
    (τ : PredictableStatePrefixIndex (σ := σ) (α := α))
    (reward : α → ℝ) (cap : ℕ) : σ × (ℕ → α) → ℝ :=
  fun z => ∑ n ∈ Finset.range (cap + 1),
    if n < τ z then reward (coordinate n z.2) else 0

/-- A finitely truncated predictable stopped reward is Borel whenever the
one-coordinate reward is Borel. -/
theorem measurable_truncatedStrictStoppedReward
    (τ : PredictableStatePrefixIndex (σ := σ) (α := α))
    (reward : α → ℝ) (hreward : Measurable reward) (cap : ℕ) :
    Measurable (truncatedStrictStoppedReward τ reward cap) := by
  unfold truncatedStrictStoppedReward
  apply Finset.measurable_fun_sum
  intro n _
  exact Measurable.ite (τ.measurableSet_continuationEvent n)
    (hreward.comp ((measurable_coordinate (α := α) n).comp measurable_snd))
    measurable_const

/-- When a predictable index is already bounded by the deterministic
truncation cap, its truncated constant reward is the accrued-coordinate count
times that constant. -/
theorem truncatedStrictStoppedReward_const_of_le_cap
    (τ : PredictableStatePrefixIndex (σ := σ) (α := α))
    (c : ℝ) (cap : ℕ) (z : σ × (ℕ → α)) (hcap : τ z ≤ cap) :
    truncatedStrictStoppedReward τ (fun _ => c) cap z = (τ z : ℝ) * c := by
  unfold truncatedStrictStoppedReward
  have hsubset : Finset.range (τ z) ⊆ Finset.range (cap + 1) := by
    rw [Finset.range_subset_range]
    omega
  calc
    (∑ n ∈ Finset.range (cap + 1), if n < τ z then c else 0) =
        (∑ n ∈ Finset.range (τ z), if n < τ z then c else 0) :=
      (Finset.sum_subset hsubset (by
        intro n _ hn
        have hnot : ¬ n < τ z := by
          simpa [Finset.mem_range] using hn
        simp [hnot])).symm
    _ = (∑ _n ∈ Finset.range (τ z), c) := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [Finset.mem_range.mp hn]
    _ = (τ z : ℝ) * c := by
      simp [Finset.sum_const, nsmul_eq_mul]

private theorem integral_continuationEvent_zero_indicator_mul_coordinate
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : PredictableStatePrefixIndex (σ := σ) (α := α))
    (reward : α → ℝ) (hreward : Measurable reward) :
    ∫ z, (τ.continuationEvent 0).indicator (fun _ => (1 : ℝ)) z *
        reward (coordinate 0 z.2) ∂(ρ.prod (measure μ)) =
      (ρ.prod (measure μ)).real (τ.continuationEvent 0) *
        ∫ x, reward x ∂μ := by
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  rcases τ.continuation_zero_measurable with ⟨u, hu, hpre⟩
  let F : σ → ℝ := u.indicator (fun _ => (1 : ℝ))
  have hF : Measurable F := measurable_const.indicator hu
  have hindep := indepFun_state_coordinate ρ μ 0
  have hfactor := hindep.integral_comp_mul_comp measurable_fst.aemeasurable
    ((measurable_coordinate (α := α) 0).comp measurable_snd).aemeasurable
    hF.aestronglyMeasurable hreward.aestronglyMeasurable
  have hleft :
      (fun z : σ × (ℕ → α) => F z.1 * reward (coordinate 0 z.2)) =
        fun z => (τ.continuationEvent 0).indicator (fun _ => (1 : ℝ)) z *
          reward (coordinate 0 z.2) := by
    funext z
    have hmem : z.1 ∈ u ↔ z ∈ τ.continuationEvent 0 := by
      change z ∈ (Prod.fst : σ × (ℕ → α) → σ) ⁻¹' u ↔
        0 < τ z
      rw [hpre]
      simp
    by_cases h : z.1 ∈ u
    · have hcont : z ∈ τ.continuationEvent 0 := hmem.mp h
      simp [F, Set.indicator, h, hcont]
    · have h' : z ∉ τ.continuationEvent 0 := by
        intro hcont
        exact h (hmem.mpr hcont)
      simp [F, Set.indicator, h, h']
  have hprefix :
      (∫ z : σ × (ℕ → α), F z.1 ∂(ρ.prod (measure μ))) =
        (ρ.prod (measure μ)).real (τ.continuationEvent 0) := by
    calc
      (∫ z : σ × (ℕ → α), F z.1 ∂(ρ.prod (measure μ))) =
          ∫ z : σ × (ℕ → α),
            (τ.continuationEvent 0).indicator (fun _ => (1 : ℝ)) z
              ∂(ρ.prod (measure μ)) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
            have hmem : z.1 ∈ u ↔ z ∈ τ.continuationEvent 0 := by
              change z ∈ (Prod.fst : σ × (ℕ → α) → σ) ⁻¹' u ↔
                0 < τ z
              rw [hpre]
              simp
            by_cases h : z.1 ∈ u
            · have hcont : z ∈ τ.continuationEvent 0 := hmem.mp h
              simp [F, Set.indicator, h, hcont]
            · have h' : z ∉ τ.continuationEvent 0 := by
                intro hcont
                exact h (hmem.mpr hcont)
              simp [F, Set.indicator, h, h']
      _ = (ρ.prod (measure μ)).real (τ.continuationEvent 0) := by
        rw [MeasureTheory.integral_indicator (τ.measurableSet_continuationEvent 0),
          MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
  have hrewardIntegral :
      (∫ z : σ × (ℕ → α), reward (coordinate 0 z.2)
        ∂(ρ.prod (measure μ))) = ∫ x, reward x ∂μ := by
    exact ((coordinate_measurePreserving μ 0).comp
      (measurePreserving_snd : MeasurePreserving Prod.snd
        (ρ.prod (measure μ)) (measure μ))).hasLaw.integral_comp
          hreward.aestronglyMeasurable
  calc
    ∫ z, (τ.continuationEvent 0).indicator (fun _ => (1 : ℝ)) z *
        reward (coordinate 0 z.2) ∂(ρ.prod (measure μ)) =
        ∫ z : σ × (ℕ → α), F z.1 * reward (coordinate 0 z.2)
          ∂(ρ.prod (measure μ)) := by rw [hleft]
    _ = (∫ z : σ × (ℕ → α), F z.1 ∂(ρ.prod (measure μ))) *
        ∫ z : σ × (ℕ → α), reward (coordinate 0 z.2)
          ∂(ρ.prod (measure μ)) := by
          simpa only [Function.comp_apply] using hfactor
    _ = (ρ.prod (measure μ)).real (τ.continuationEvent 0) *
        ∫ x, reward x ∂μ := by rw [hprefix, hrewardIntegral]

private theorem integral_continuationEvent_succ_indicator_mul_coordinate
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : PredictableStatePrefixIndex (σ := σ) (α := α)) (n : ℕ)
    (reward : α → ℝ) (hreward : Measurable reward) :
    ∫ z, (τ.continuationEvent (n + 1)).indicator (fun _ => (1 : ℝ)) z *
        reward (coordinate (n + 1) z.2) ∂(ρ.prod (measure μ)) =
      (ρ.prod (measure μ)).real (τ.continuationEvent (n + 1)) *
        ∫ x, reward x ∂μ := by
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  rcases τ.continuation_succ_prefix_measurable n with ⟨u, hu, hpre⟩
  let F : (σ × (Finset.range (n + 1) → α)) → ℝ :=
    u.indicator (fun _ => (1 : ℝ))
  let G : (Fin 1 → α) → ℝ := fun block => reward (block 0)
  have hF : Measurable F := measurable_const.indicator hu
  have hG : Measurable G := hreward.comp (measurable_pi_apply 0)
  have hindep := indepFun_state_streamPrefix_block ρ μ n 1
  have hfactor := hindep.integral_comp_mul_comp
    (measurable_stateStreamPrefix (σ := σ) (α := α) n).aemeasurable
    ((measurable_block (α := α) (n + 1) 1).comp measurable_snd).aemeasurable
    hF.aestronglyMeasurable hG.aestronglyMeasurable
  have hleft :
      (fun z : σ × (ℕ → α) => F (stateStreamPrefix (σ := σ) (α := α) n z) *
          G (block (α := α) (n + 1) 1 z.2)) =
        fun z => (τ.continuationEvent (n + 1)).indicator (fun _ => (1 : ℝ)) z *
          reward (coordinate (n + 1) z.2) := by
    funext z
    have hmem : stateStreamPrefix (σ := σ) (α := α) n z ∈ u ↔
        z ∈ τ.continuationEvent (n + 1) := by
      change z ∈ stateStreamPrefix (σ := σ) (α := α) n ⁻¹' u ↔
        n + 1 < τ z
      rw [hpre]
      simp
    by_cases h : stateStreamPrefix (σ := σ) (α := α) n z ∈ u
    · have hcont : z ∈ τ.continuationEvent (n + 1) := hmem.mp h
      simp [F, G, block, coordinate, Set.indicator, h, hcont]
    · have h' : z ∉ τ.continuationEvent (n + 1) := by
        intro hcont
        exact h (hmem.mpr hcont)
      simp [F, G, block, coordinate, Set.indicator, h, h']
  have hprefix :
      (∫ z : σ × (ℕ → α), F (stateStreamPrefix (σ := σ) (α := α) n z)
        ∂(ρ.prod (measure μ))) =
        (ρ.prod (measure μ)).real (τ.continuationEvent (n + 1)) := by
    calc
      (∫ z : σ × (ℕ → α), F (stateStreamPrefix (σ := σ) (α := α) n z)
          ∂(ρ.prod (measure μ))) =
          ∫ z : σ × (ℕ → α),
            (τ.continuationEvent (n + 1)).indicator (fun _ => (1 : ℝ)) z
              ∂(ρ.prod (measure μ)) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
            change u.indicator (fun _ => (1 : ℝ))
              (stateStreamPrefix (σ := σ) (α := α) n z) = _
            have hmem : stateStreamPrefix (σ := σ) (α := α) n z ∈ u ↔
                z ∈ τ.continuationEvent (n + 1) := by
              change z ∈ stateStreamPrefix (σ := σ) (α := α) n ⁻¹' u ↔
                n + 1 < τ z
              rw [hpre]
              simp
            by_cases h : stateStreamPrefix (σ := σ) (α := α) n z ∈ u
            · have hcont : z ∈ τ.continuationEvent (n + 1) := hmem.mp h
              simp [Set.indicator, h, hcont]
            · have h' : z ∉ τ.continuationEvent (n + 1) := by
                intro hcont
                exact h (hmem.mpr hcont)
              simp [Set.indicator, h, h']
      _ = (ρ.prod (measure μ)).real (τ.continuationEvent (n + 1)) := by
        rw [MeasureTheory.integral_indicator
          (τ.measurableSet_continuationEvent (n + 1)),
          MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
  have hrewardIntegral :
      (∫ z : σ × (ℕ → α), G (block (α := α) (n + 1) 1 z.2)
        ∂(ρ.prod (measure μ))) = ∫ x, reward x ∂μ := by
    exact ((coordinate_measurePreserving μ (n + 1)).comp
      (measurePreserving_snd : MeasurePreserving Prod.snd
        (ρ.prod (measure μ)) (measure μ))).hasLaw.integral_comp
          hreward.aestronglyMeasurable
  calc
    ∫ z, (τ.continuationEvent (n + 1)).indicator (fun _ => (1 : ℝ)) z *
        reward (coordinate (n + 1) z.2) ∂(ρ.prod (measure μ)) =
        ∫ z : σ × (ℕ → α), F (stateStreamPrefix (σ := σ) (α := α) n z) *
          G (block (α := α) (n + 1) 1 z.2) ∂(ρ.prod (measure μ)) := by
          rw [hleft]
    _ = (∫ z : σ × (ℕ → α), F (stateStreamPrefix (σ := σ) (α := α) n z)
          ∂(ρ.prod (measure μ))) *
          ∫ z : σ × (ℕ → α), G (block (α := α) (n + 1) 1 z.2)
            ∂(ρ.prod (measure μ)) := by
          simpa only [Function.comp_apply] using hfactor
    _ = (ρ.prod (measure μ)).real (τ.continuationEvent (n + 1)) *
          ∫ x, reward x ∂μ := by rw [hprefix, hrewardIntegral]

/-- The expected reward of one coordinate accrued before a predictable stop.
The event deciding whether coordinate `n` is accrued does not inspect that
coordinate. -/
theorem integral_continuationEvent_indicator_mul_coordinate
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : PredictableStatePrefixIndex (σ := σ) (α := α)) (n : ℕ)
    (reward : α → ℝ) (hreward : Measurable reward) :
    ∫ z, (if n < τ z then reward (coordinate n z.2) else 0)
      ∂(ρ.prod (measure μ)) =
      (ρ.prod (measure μ)).real (τ.continuationEvent n) * ∫ x, reward x ∂μ := by
  cases n with
  | zero =>
      simpa [continuationEvent, Set.indicator] using
        (integral_continuationEvent_zero_indicator_mul_coordinate
          ρ μ τ reward hreward)
  | succ n =>
      simpa [continuationEvent, Set.indicator] using
        (integral_continuationEvent_succ_indicator_mul_coordinate
          ρ μ τ n reward hreward)

/-- The finite predictable stopped-reward identity.  An unbounded result
requires a separate integrable limiting argument. -/
theorem integral_truncatedStrictStoppedReward
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : PredictableStatePrefixIndex (σ := σ) (α := α))
    (reward : α → ℝ) (hreward : Measurable reward)
    (hintegrable : Integrable reward μ) (cap : ℕ) :
    ∫ z, truncatedStrictStoppedReward τ reward cap z ∂(ρ.prod (measure μ)) =
      (∑ n ∈ Finset.range (cap + 1),
        (ρ.prod (measure μ)).real (τ.continuationEvent n)) * ∫ x, reward x ∂μ := by
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  unfold truncatedStrictStoppedReward
  rw [MeasureTheory.integral_finset_sum]
  · have htermIntegral (n : ℕ) :
        ∫ z, (if n < τ z then reward (coordinate n z.2) else 0)
          ∂(ρ.prod (measure μ)) =
          (ρ.prod (measure μ)).real (τ.continuationEvent n) * ∫ x, reward x ∂μ := by
      cases n with
      | zero =>
          have hterm := integral_continuationEvent_zero_indicator_mul_coordinate
            ρ μ τ reward hreward
          simpa [continuationEvent, Set.indicator] using hterm
      | succ n =>
          have hterm := integral_continuationEvent_succ_indicator_mul_coordinate
            ρ μ τ n reward hreward
          simpa [continuationEvent, Set.indicator] using hterm
    simp_rw [htermIntegral]
    rw [Finset.sum_mul]
  · intro n _
    have hcoord := StatePrefixStoppingIndex.integrable_state_coordinate
      ρ μ reward hintegrable n
    have hindicator := hcoord.indicator (τ.measurableSet_continuationEvent n)
    have heq :
        (fun z => if n < τ z then reward (coordinate n z.2) else 0) =
        (τ.continuationEvent n).indicator
          (fun z => reward (coordinate n z.2)) := by
      funext z
      simp [continuationEvent, Set.indicator]
    rw [heq]
    exact hindicator

/-- The total reward accrued strictly before a predictable index.  Its
integrability is not implicit in this definition; the theorem below states
the summability condition needed to interchange the infinite sum and the
integral. -/
noncomputable def strictStoppedReward
    (τ : PredictableStatePrefixIndex (σ := σ) (α := α))
    (reward : α → ℝ) : σ × (ℕ → α) → ℝ :=
  fun z => ∑' n, if n < τ z then reward (coordinate n z.2) else 0

/-- The unbounded predictable stopped-reward identity.  The explicit
summability premise prevents an unjustified interchange of the infinite sum
and integral; it is not inferred merely from a total stopping index. -/
theorem integral_strictStoppedReward
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : PredictableStatePrefixIndex (σ := σ) (α := α))
    (reward : α → ℝ) (hreward : Measurable reward)
    (hintegrable : Integrable reward μ)
    (hsummable : Summable fun n =>
      (ρ.prod (measure μ)).real (τ.continuationEvent n)) :
    ∫ z, strictStoppedReward τ reward z ∂(ρ.prod (measure μ)) =
      (∑' n, (ρ.prod (measure μ)).real (τ.continuationEvent n)) *
        ∫ x, reward x ∂μ := by
  let M : Measure (σ × (ℕ → α)) := ρ.prod (measure μ)
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  let F : ℕ → σ × (ℕ → α) → ℝ := fun n z =>
    if n < τ z then reward (coordinate n z.2) else 0
  have hF_integrable : ∀ n, Integrable (F n) M := by
    intro n
    have hcoordinate : Integrable (fun z : σ × (ℕ → α) =>
        reward (coordinate n z.2)) M := by
      simpa [M, Function.comp_def] using
        ((coordinate_measurePreserving μ n).comp
          (measurePreserving_snd : MeasurePreserving Prod.snd
            (ρ.prod (measure μ)) (measure μ))).integrable_comp_of_integrable hintegrable
    have hindicator := hcoordinate.indicator (τ.measurableSet_continuationEvent n)
    have heq : F n = (τ.continuationEvent n).indicator
        (fun z => reward (coordinate n z.2)) := by
      funext z
      simp [F, continuationEvent, Set.indicator]
    rw [heq]
    exact hindicator
  have hnormIntegral : ∀ n,
      ∫ z, ‖F n z‖ ∂M =
        M.real (τ.continuationEvent n) * ∫ x, ‖reward x‖ ∂μ := by
    intro n
    simpa [F, M, apply_ite] using
      (integral_continuationEvent_indicator_mul_coordinate
        ρ μ τ n (fun x => ‖reward x‖) hreward.norm)
  have hsumNorm : Summable fun n => ∫ z, ‖F n z‖ ∂M := by
    exact (hsummable.mul_right (∫ x, ‖reward x‖ ∂μ)).congr fun n =>
      (hnormIntegral n).symm
  calc
    ∫ z, strictStoppedReward τ reward z ∂M = ∫ z, ∑' n, F n z ∂M := by
      rfl
    _ = ∑' n, ∫ z, F n z ∂M := by
      exact (MeasureTheory.integral_tsum_of_summable_integral_norm
        hF_integrable hsumNorm).symm
    _ = ∑' n, M.real (τ.continuationEvent n) * ∫ x, reward x ∂μ := by
      apply tsum_congr
      intro n
      simpa [F, M] using
        (integral_continuationEvent_indicator_mul_coordinate
          ρ μ τ n reward hreward)
    _ = (∑' n, M.real (τ.continuationEvent n)) * ∫ x, reward x ∂μ := by
      rw [tsum_mul_right]

/-- The nonnegative reward accrued strictly before a predictable index.
Unlike the real-valued version, this extended nonnegative observable does not
silently require its expectation to be finite. -/
noncomputable def strictStoppedENNReward
    (τ : PredictableStatePrefixIndex (σ := σ) (α := α))
    (reward : α → ℝ≥0∞) : σ × (ℕ → α) → ℝ≥0∞ :=
  fun z => ∑' n, if n < τ z then reward (coordinate n z.2) else 0

private theorem lintegral_continuationEvent_zero_indicator_mul_coordinate
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : PredictableStatePrefixIndex (σ := σ) (α := α))
    (reward : α → ℝ≥0∞) (hreward : Measurable reward) :
    ∫⁻ z, (if 0 < τ z then reward (coordinate 0 z.2) else 0)
      ∂(ρ.prod (measure μ)) =
      (ρ.prod (measure μ)) (τ.continuationEvent 0) * ∫⁻ x, reward x ∂μ := by
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  rcases τ.continuation_zero_measurable with ⟨u, hu, hpre⟩
  let F : σ → ℝ≥0∞ := u.indicator (fun _ => (1 : ℝ≥0∞))
  have hF : Measurable F := measurable_const.indicator hu
  have hindep := indepFun_state_coordinate ρ μ 0
  have hfactor := ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    (hF.comp measurable_fst)
    (hreward.comp ((measurable_coordinate (α := α) 0).comp measurable_snd))
    (hindep.comp hF hreward)
  have hleft :
      (fun z : σ × (ℕ → α) => F z.1 * reward (coordinate 0 z.2)) =
        fun z => if 0 < τ z then reward (coordinate 0 z.2) else 0 := by
    funext z
    have hmem : z.1 ∈ u ↔ z ∈ τ.continuationEvent 0 := by
      change z ∈ (Prod.fst : σ × (ℕ → α) → σ) ⁻¹' u ↔ 0 < τ z
      rw [hpre]
      simp
    by_cases h : z.1 ∈ u
    · have hcont : 0 < τ z := hmem.mp h
      simp [F, h, hcont]
    · have hnot : ¬ 0 < τ z := by
        intro hcont
        exact h (hmem.mpr hcont)
      simp [F, h, hnot]
  have hprefix :
      (∫⁻ z : σ × (ℕ → α), F z.1 ∂(ρ.prod (measure μ))) =
        (ρ.prod (measure μ)) (τ.continuationEvent 0) := by
    calc
      (∫⁻ z : σ × (ℕ → α), F z.1 ∂(ρ.prod (measure μ))) =
          ∫⁻ z : σ × (ℕ → α),
            (τ.continuationEvent 0).indicator (fun _ => (1 : ℝ≥0∞)) z
              ∂(ρ.prod (measure μ)) := by
            apply MeasureTheory.lintegral_congr
            intro z
            have hmem : z.1 ∈ u ↔ z ∈ τ.continuationEvent 0 := by
              change z ∈ (Prod.fst : σ × (ℕ → α) → σ) ⁻¹' u ↔ 0 < τ z
              rw [hpre]
              simp
            by_cases h : z.1 ∈ u
            · have hcont : z ∈ τ.continuationEvent 0 := hmem.mp h
              simp [F, Set.indicator, h, hcont]
            · have hnot : z ∉ τ.continuationEvent 0 := by
                intro hcont
                exact h (hmem.mpr hcont)
              simp [F, Set.indicator, h, hnot]
      _ = (ρ.prod (measure μ)) (τ.continuationEvent 0) :=
        MeasureTheory.lintegral_indicator_one (τ.measurableSet_continuationEvent 0)
  have hrewardIntegral :
      (∫⁻ z : σ × (ℕ → α), reward (coordinate 0 z.2)
        ∂(ρ.prod (measure μ))) = ∫⁻ x, reward x ∂μ := by
    exact ((coordinate_measurePreserving μ 0).comp
      (measurePreserving_snd : MeasurePreserving Prod.snd
        (ρ.prod (measure μ)) (measure μ))).hasLaw.lintegral_comp hreward.aemeasurable
  calc
    ∫⁻ z, (if 0 < τ z then reward (coordinate 0 z.2) else 0)
        ∂(ρ.prod (measure μ)) =
        ∫⁻ z : σ × (ℕ → α), F z.1 * reward (coordinate 0 z.2)
          ∂(ρ.prod (measure μ)) := by rw [hleft]
    _ = (∫⁻ z : σ × (ℕ → α), F z.1 ∂(ρ.prod (measure μ))) *
          ∫⁻ z : σ × (ℕ → α), reward (coordinate 0 z.2)
            ∂(ρ.prod (measure μ)) := by
          simpa only [Function.comp_apply] using hfactor
    _ = (ρ.prod (measure μ)) (τ.continuationEvent 0) * ∫⁻ x, reward x ∂μ := by
          rw [hprefix, hrewardIntegral]

private theorem lintegral_continuationEvent_succ_indicator_mul_coordinate
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : PredictableStatePrefixIndex (σ := σ) (α := α)) (n : ℕ)
    (reward : α → ℝ≥0∞) (hreward : Measurable reward) :
    ∫⁻ z, (if n + 1 < τ z then reward (coordinate (n + 1) z.2) else 0)
      ∂(ρ.prod (measure μ)) =
      (ρ.prod (measure μ)) (τ.continuationEvent (n + 1)) * ∫⁻ x, reward x ∂μ := by
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  rcases τ.continuation_succ_prefix_measurable n with ⟨u, hu, hpre⟩
  let F : (σ × (Finset.range (n + 1) → α)) → ℝ≥0∞ :=
    u.indicator (fun _ => (1 : ℝ≥0∞))
  let G : (Fin 1 → α) → ℝ≥0∞ := fun block => reward (block 0)
  have hF : Measurable F := measurable_const.indicator hu
  have hG : Measurable G := hreward.comp (measurable_pi_apply 0)
  have hindep := indepFun_state_streamPrefix_block ρ μ n 1
  have hfactor := ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    (hF.comp (measurable_stateStreamPrefix (σ := σ) (α := α) n))
    (hG.comp ((measurable_block (α := α) (n + 1) 1).comp measurable_snd))
    (hindep.comp hF hG)
  have hleft :
      (fun z : σ × (ℕ → α) => F (stateStreamPrefix (σ := σ) (α := α) n z) *
          G (block (α := α) (n + 1) 1 z.2)) =
        fun z => if n + 1 < τ z then reward (coordinate (n + 1) z.2) else 0 := by
    funext z
    have hmem : stateStreamPrefix (σ := σ) (α := α) n z ∈ u ↔
        z ∈ τ.continuationEvent (n + 1) := by
      change z ∈ stateStreamPrefix (σ := σ) (α := α) n ⁻¹' u ↔ n + 1 < τ z
      rw [hpre]
      simp
    by_cases h : stateStreamPrefix (σ := σ) (α := α) n z ∈ u
    · have hcont : n + 1 < τ z := hmem.mp h
      simp [F, G, block, coordinate, h, hcont]
    · have hnot : ¬ n + 1 < τ z := by
        intro hcont
        exact h (hmem.mpr hcont)
      simp [F, G, block, coordinate, h, hnot]
  have hprefix :
      (∫⁻ z : σ × (ℕ → α), F (stateStreamPrefix (σ := σ) (α := α) n z)
        ∂(ρ.prod (measure μ))) =
        (ρ.prod (measure μ)) (τ.continuationEvent (n + 1)) := by
    calc
      (∫⁻ z : σ × (ℕ → α), F (stateStreamPrefix (σ := σ) (α := α) n z)
          ∂(ρ.prod (measure μ))) =
          ∫⁻ z : σ × (ℕ → α),
            (τ.continuationEvent (n + 1)).indicator (fun _ => (1 : ℝ≥0∞)) z
              ∂(ρ.prod (measure μ)) := by
            apply MeasureTheory.lintegral_congr
            intro z
            have hmem : stateStreamPrefix (σ := σ) (α := α) n z ∈ u ↔
                z ∈ τ.continuationEvent (n + 1) := by
              change z ∈ stateStreamPrefix (σ := σ) (α := α) n ⁻¹' u ↔ n + 1 < τ z
              rw [hpre]
              simp
            by_cases h : stateStreamPrefix (σ := σ) (α := α) n z ∈ u
            · have hcont : z ∈ τ.continuationEvent (n + 1) := hmem.mp h
              simp [F, Set.indicator, h, hcont]
            · have hnot : z ∉ τ.continuationEvent (n + 1) := by
                intro hcont
                exact h (hmem.mpr hcont)
              simp [F, Set.indicator, h, hnot]
      _ = (ρ.prod (measure μ)) (τ.continuationEvent (n + 1)) :=
        MeasureTheory.lintegral_indicator_one (τ.measurableSet_continuationEvent (n + 1))
  have hrewardIntegral :
      (∫⁻ z : σ × (ℕ → α), G (block (α := α) (n + 1) 1 z.2)
        ∂(ρ.prod (measure μ))) = ∫⁻ x, reward x ∂μ := by
    exact ((coordinate_measurePreserving μ (n + 1)).comp
      (measurePreserving_snd : MeasurePreserving Prod.snd
        (ρ.prod (measure μ)) (measure μ))).hasLaw.lintegral_comp hreward.aemeasurable
  calc
    ∫⁻ z, (if n + 1 < τ z then reward (coordinate (n + 1) z.2) else 0)
        ∂(ρ.prod (measure μ)) =
        ∫⁻ z : σ × (ℕ → α),
          F (stateStreamPrefix (σ := σ) (α := α) n z) *
            G (block (α := α) (n + 1) 1 z.2) ∂(ρ.prod (measure μ)) := by rw [hleft]
    _ = (∫⁻ z : σ × (ℕ → α), F (stateStreamPrefix (σ := σ) (α := α) n z)
          ∂(ρ.prod (measure μ))) *
          ∫⁻ z : σ × (ℕ → α), G (block (α := α) (n + 1) 1 z.2)
            ∂(ρ.prod (measure μ)) := by
          simpa only [Function.comp_apply] using hfactor
    _ = (ρ.prod (measure μ)) (τ.continuationEvent (n + 1)) * ∫⁻ x, reward x ∂μ := by
          rw [hprefix, hrewardIntegral]

/-- The nonnegative expected reward at one coordinate factors from the
predictable event deciding whether that coordinate is accrued. -/
theorem lintegral_continuationEvent_indicator_mul_coordinate
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : PredictableStatePrefixIndex (σ := σ) (α := α)) (n : ℕ)
    (reward : α → ℝ≥0∞) (hreward : Measurable reward) :
    ∫⁻ z, (if n < τ z then reward (coordinate n z.2) else 0)
      ∂(ρ.prod (measure μ)) =
      (ρ.prod (measure μ)) (τ.continuationEvent n) * ∫⁻ x, reward x ∂μ := by
  cases n with
  | zero =>
      simpa [continuationEvent] using
        (lintegral_continuationEvent_zero_indicator_mul_coordinate
          ρ μ τ reward hreward)
  | succ n =>
      simpa [continuationEvent] using
        (lintegral_continuationEvent_succ_indicator_mul_coordinate
          ρ μ τ n reward hreward)

/-- Tonelli's stopped-reward identity for a predictable IID index.  It holds
in `ℝ≥0∞` without a tail-summability hypothesis, so it can be used in a
finite-horizon or truncation argument before finite expectation is known. -/
theorem lintegral_strictStoppedENNReward
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : PredictableStatePrefixIndex (σ := σ) (α := α))
    (reward : α → ℝ≥0∞) (hreward : Measurable reward) :
    ∫⁻ z, strictStoppedENNReward τ reward z ∂(ρ.prod (measure μ)) =
      (∑' n, (ρ.prod (measure μ)) (τ.continuationEvent n)) * ∫⁻ x, reward x ∂μ := by
  let M : Measure (σ × (ℕ → α)) := ρ.prod (measure μ)
  let F : ℕ → σ × (ℕ → α) → ℝ≥0∞ := fun n z =>
    if n < τ z then reward (coordinate n z.2) else 0
  have hF_measurable : ∀ n, Measurable (F n) := by
    intro n
    have hcoordinate : Measurable (fun z : σ × (ℕ → α) =>
        reward (coordinate n z.2)) :=
      hreward.comp ((measurable_coordinate (α := α) n).comp measurable_snd)
    have hindicator := hcoordinate.indicator (τ.measurableSet_continuationEvent n)
    have heq : F n = (τ.continuationEvent n).indicator
        (fun z => reward (coordinate n z.2)) := by
      funext z
      simp [F, continuationEvent, Set.indicator]
    rw [heq]
    exact hindicator
  have hterm (n : ℕ) :
      ∫⁻ z, F n z ∂M = M (τ.continuationEvent n) * ∫⁻ x, reward x ∂μ := by
    cases n with
    | zero =>
        simpa [F, M] using
          (lintegral_continuationEvent_zero_indicator_mul_coordinate
            ρ μ τ reward hreward)
    | succ n =>
        simpa [F, M] using
          (lintegral_continuationEvent_succ_indicator_mul_coordinate
            ρ μ τ n reward hreward)
  calc
    ∫⁻ z, strictStoppedENNReward τ reward z ∂M = ∫⁻ z, ∑' n, F n z ∂M := by
      rfl
    _ = ∑' n, ∫⁻ z, F n z ∂M := by
      exact MeasureTheory.lintegral_tsum fun n => (hF_measurable n).aemeasurable
    _ = ∑' n, M (τ.continuationEvent n) * ∫⁻ x, reward x ∂μ := by
      apply tsum_congr
      exact hterm
    _ = (∑' n, M (τ.continuationEvent n)) * ∫⁻ x, reward x ∂μ := by
      rw [ENNReal.tsum_mul_right]

/-- With a constant nonnegative reward, the reward accrued strictly before a
predictable index is exactly the number of accrued coordinates times that
constant. -/
theorem strictStoppedENNReward_const
    (τ : PredictableStatePrefixIndex (σ := σ) (α := α))
    (c : ℝ≥0∞) (z : σ × (ℕ → α)) :
    strictStoppedENNReward τ (fun _ => c) z = (↑(τ z) : ℝ≥0∞) * c := by
  let N : ℕ := τ z
  have hzero : ∀ n ∉ Finset.range N,
      (if n < τ z then c else 0) = 0 := by
    intro n hn
    have hN : N ≤ n := Nat.le_of_not_gt (by simpa using hn)
    have hnot : ¬ n < τ z := by simpa [N] using hN
    simp [hnot]
  unfold strictStoppedENNReward
  rw [tsum_eq_sum hzero]
  have hterm : ∀ b ∈ Finset.range N,
      (if b < τ z then c else 0) = c := by
    intro b hb
    have hlt : b < N := Finset.mem_range.mp hb
    have hlt' : b < τ z := by simpa [N] using hlt
    simp [hlt']
  rw [Finset.sum_congr rfl hterm]
  simp [Finset.sum_const, nsmul_eq_mul, N]

/-- The extended expected number of coordinates accrued before a predictable
index is the tail sum of its strict-continuation probabilities. -/
theorem lintegral_coe_predictableIndex_eq_tsum_continuationEvent
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : PredictableStatePrefixIndex (σ := σ) (α := α)) :
    ∫⁻ z, (↑(τ z) : ℝ≥0∞) ∂(ρ.prod (measure μ)) =
      ∑' n, (ρ.prod (measure μ)) (τ.continuationEvent n) := by
  have h := lintegral_strictStoppedENNReward ρ μ τ
    (fun _ : α => (1 : ℝ≥0∞)) measurable_const
  calc
    ∫⁻ z, (↑(τ z) : ℝ≥0∞) ∂(ρ.prod (measure μ)) =
        ∫⁻ z, strictStoppedENNReward τ (fun _ : α => (1 : ℝ≥0∞)) z
          ∂(ρ.prod (measure μ)) := by
            apply MeasureTheory.lintegral_congr
            intro z
            simpa using (strictStoppedENNReward_const τ 1 z).symm
    _ = ∑' n, (ρ.prod (measure μ)) (τ.continuationEvent n) := by
      simpa using h

/-- A predictable IID-prefix index has a finite expected accrued-coordinate
count exactly when its real strict-continuation tail is summable.  This is the
generic finiteness handoff needed before using the real stopped-reward
identity. -/
theorem summable_measureReal_continuationEvent_iff_lintegral_coe_predictableIndex_ne_top
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : PredictableStatePrefixIndex (σ := σ) (α := α)) :
    (Summable fun n => (ρ.prod (measure μ)).real (τ.continuationEvent n)) ↔
      ∫⁻ z, (↑(τ z) : ℝ≥0∞) ∂(ρ.prod (measure μ)) ≠ ⊤ := by
  let M : Measure (σ × (ℕ → α)) := ρ.prod (measure μ)
  letI : IsProbabilityMeasure M := by
    dsimp [M, measure]
    infer_instance
  have htail : ∫⁻ z, (↑(τ z) : ℝ≥0∞) ∂M =
      ∑' n, M (τ.continuationEvent n) := by
    simpa [M] using lintegral_coe_predictableIndex_eq_tsum_continuationEvent
      ρ μ τ
  constructor
  · intro hsummable
    rw [htail]
    have hterm : ∀ n, ENNReal.ofReal (M.real (τ.continuationEvent n)) =
        M (τ.continuationEvent n) := by
      intro n
      exact ENNReal.ofReal_toReal (measure_ne_top M (τ.continuationEvent n))
    rw [← tsum_congr hterm]
    exact hsummable.tsum_ofReal_ne_top
  · intro hfinite
    rw [htail] at hfinite
    exact ENNReal.summable_toReal hfinite

end PredictableStatePrefixIndex

namespace StatePrefixStoppingIndex

/-- Shifting a total prefix stopping index by one turns rewards accrued
through its stopping coordinate into rewards accrued strictly before a
predictable index. -/
def toPredictableStatePrefixIndexSucc
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α)) :
    PredictableStatePrefixIndex (σ := σ) (α := α) where
  toFun := fun z => τ z + 1
  continuation_zero_measurable := by
    refine MeasurableSpace.measurableSet_comap.2 ⟨Set.univ, MeasurableSet.univ, ?_⟩
    ext z
    simp
  continuation_succ_prefix_measurable := fun n => by
    have hcontinuation := τ.continuationEvent_succ_prefix_measurable n
    rw [show {z : σ × (ℕ → α) | n + 1 < τ z + 1} = τ.continuationEvent (n + 1) by
      ext z
      simp [continuationEvent]]
    exact hcontinuation

/-- The nonnegative reward accrued through a total prefix stop. -/
noncomputable def stoppedENNReward
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α))
    (reward : α → ℝ≥0∞) : σ × (ℕ → α) → ℝ≥0∞ :=
  PredictableStatePrefixIndex.strictStoppedENNReward
    τ.toPredictableStatePrefixIndexSucc reward

/-- The real-valued reward accrued through a total prefix stop.  Its integral
is used only with the explicit finite expected-count hypothesis in
`integral_stoppedReward`. -/
noncomputable def stoppedReward
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α))
    (reward : α → ℝ) : σ × (ℕ → α) → ℝ :=
  PredictableStatePrefixIndex.strictStoppedReward
    τ.toPredictableStatePrefixIndexSucc reward

/-- For a constant nonnegative reward, the stopped reward is exactly the
number of coordinates inspected through the total prefix stop.  This is the
discrete renewal-count identity underlying cycle-count and cycle-time
accounting. -/
theorem stoppedENNReward_const
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α))
    (c : ℝ≥0∞) (z : σ × (ℕ → α)) :
    stoppedENNReward τ (fun _ => c) z = (↑(τ z + 1) : ℝ≥0∞) * c := by
  let N : ℕ := τ z + 1
  have hzero : ∀ n ∉ Finset.range N,
      (if n < τ.toPredictableStatePrefixIndexSucc z then c else 0) = 0 := by
    intro n hn
    have hN : N ≤ n := Nat.le_of_not_gt (by simpa using hn)
    have hnot : ¬ n < τ.toPredictableStatePrefixIndexSucc z := by
      simpa [N, toPredictableStatePrefixIndexSucc] using hN
    simp [hnot]
  unfold stoppedENNReward PredictableStatePrefixIndex.strictStoppedENNReward
  rw [tsum_eq_sum hzero]
  have hterm : ∀ b ∈ Finset.range (τ z + 1),
      (if b < τ.toPredictableStatePrefixIndexSucc z then c else 0) = c := by
    intro b hb
    have hlt : b < τ z + 1 := Finset.mem_range.mp hb
    have hlt' : b < τ.toPredictableStatePrefixIndexSucc z := by
      simpa [toPredictableStatePrefixIndexSucc] using hlt
    simp [hlt']
  rw [Finset.sum_congr rfl hterm]
  simp [Finset.sum_const, nsmul_eq_mul]

/-- Tonelli's stopped-reward identity through a total IID-prefix stop.  This
is the extended nonnegative Wald form: it does not presume a finite expected
stopping index. -/
theorem lintegral_stoppedENNReward
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α))
    (reward : α → ℝ≥0∞) (hreward : Measurable reward) :
    ∫⁻ z, stoppedENNReward τ reward z ∂(ρ.prod (measure μ)) =
      (∑' n, (ρ.prod (measure μ)) (τ.continuationEvent n)) * ∫⁻ x, reward x ∂μ := by
  have h := PredictableStatePrefixIndex.lintegral_strictStoppedENNReward
    ρ μ τ.toPredictableStatePrefixIndexSucc reward hreward
  simpa [stoppedENNReward, toPredictableStatePrefixIndexSucc,
    PredictableStatePrefixIndex.continuationEvent, continuationEvent,
    Nat.lt_succ_iff] using h

/-- The extended expected number of IID coordinates inspected through a total
prefix stop is the tail sum of its continuation probabilities.  It is a
counting form of the stopped-reward identity and does not assume integrability
of the stopping index. -/
theorem lintegral_coe_stop_succ_eq_tsum_continuationEvent
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α)) :
    ∫⁻ z, (↑(τ z + 1) : ℝ≥0∞) ∂(ρ.prod (measure μ)) =
      ∑' n, (ρ.prod (measure μ)) (τ.continuationEvent n) := by
  have h := lintegral_stoppedENNReward ρ μ τ (fun _ : α => (1 : ℝ≥0∞))
    measurable_const
  calc
    ∫⁻ z, (↑(τ z + 1) : ℝ≥0∞) ∂(ρ.prod (measure μ)) =
        ∫⁻ z, stoppedENNReward τ (fun _ : α => (1 : ℝ≥0∞)) z
          ∂(ρ.prod (measure μ)) := by
      apply MeasureTheory.lintegral_congr
      intro z
      simpa using (stoppedENNReward_const τ 1 z).symm
    _ = ∑' n, (ρ.prod (measure μ)) (τ.continuationEvent n) := by
      simpa using h

/-- A total IID-prefix stop has finite expected inspection count exactly when
its real continuation-probability tail is summable.  This is the reusable
finiteness handoff from a queue- or cycle-specific truncation bound to ordinary
real-valued stopped-reward identities. -/
theorem summable_measureReal_continuationEvent_iff_lintegral_coe_stop_succ_ne_top
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α)) :
    (Summable fun n => (ρ.prod (measure μ)).real (τ.continuationEvent n)) ↔
      ∫⁻ z, (↑(τ z + 1) : ℝ≥0∞) ∂(ρ.prod (measure μ)) ≠ ⊤ := by
  let M : Measure (σ × (ℕ → α)) := ρ.prod (measure μ)
  letI : IsProbabilityMeasure M := by
    dsimp [M, measure]
    infer_instance
  have htail : ∫⁻ z, (↑(τ z + 1) : ℝ≥0∞) ∂M =
      ∑' n, M (τ.continuationEvent n) := by
    simpa [M] using lintegral_coe_stop_succ_eq_tsum_continuationEvent ρ μ τ
  constructor
  · intro hsummable
    rw [htail]
    have hterm : ∀ n, ENNReal.ofReal (M.real (τ.continuationEvent n)) =
        M (τ.continuationEvent n) := by
      intro n
      exact ENNReal.ofReal_toReal (measure_ne_top M (τ.continuationEvent n))
    rw [← tsum_congr hterm]
    exact hsummable.tsum_ofReal_ne_top
  · intro hfinite
    rw [htail] at hfinite
    exact ENNReal.summable_toReal hfinite

/-- Real-valued Wald identity through a total IID-prefix stop.  A finite
extended expected inspection count is made explicit, so this theorem does not
silently exchange an infinite sum and an integral. -/
theorem integral_stoppedReward
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α))
    (reward : α → ℝ) (hreward : Measurable reward)
    (hintegrable : Integrable reward μ)
    (hfinite : ∫⁻ z, (↑(τ z + 1) : ℝ≥0∞) ∂(ρ.prod (measure μ)) ≠ ⊤) :
    ∫ z, stoppedReward τ reward z ∂(ρ.prod (measure μ)) =
      (∑' n, (ρ.prod (measure μ)).real (τ.continuationEvent n)) *
        ∫ x, reward x ∂μ := by
  have hsummable :=
    (summable_measureReal_continuationEvent_iff_lintegral_coe_stop_succ_ne_top
      ρ μ τ).mpr hfinite
  have hshifted : Summable fun n =>
      (ρ.prod (measure μ)).real
        (τ.toPredictableStatePrefixIndexSucc.continuationEvent n) := by
    simpa [toPredictableStatePrefixIndexSucc,
      PredictableStatePrefixIndex.continuationEvent, continuationEvent,
      Nat.lt_succ_iff] using hsummable
  simpa [stoppedReward, toPredictableStatePrefixIndexSucc,
    PredictableStatePrefixIndex.continuationEvent, continuationEvent,
    Nat.lt_succ_iff] using
    (PredictableStatePrefixIndex.integral_strictStoppedReward ρ μ
      τ.toPredictableStatePrefixIndexSucc reward hreward hintegrable hshifted)

end StatePrefixStoppingIndex

end

end AppliedModelingLib.Probability.IIDStream
