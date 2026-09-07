import AppliedModelingLib.Foundations.Probability.PalmArrivalPath
import AppliedModelingLib.Foundations.Probability.PalmArrivalPathNonexplosion
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalRenewalCount

/-!
# Stationary special flow for the Poisson base

This module constructs the standard suspension coordinates over the two-sided
iid exponential Palm-gap law, proves their real-time action and invariance on
the normalized roof measure, and isolates the full-measure good carrier on
which the action is literal.  The companion stationary-base module packages
these results as `ShiftInvariantProbabilityLaw`.  This module does not prove
the marked Campbell/Palm identity relating that untagged stationary base to a
separately tagged arrival law.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

/-- Jointly measurable version of the one-sided renewal count. -/
def jointCanonicalRenewalCount : (ℝ × (ℕ → ℝ)) → ℕ :=
  fun p => canonicalRenewalCount p.1 p.2

theorem measurable_jointCanonicalRenewalCount :
    Measurable jointCanonicalRenewalCount := by
  classical
  have htime : ∀ n : ℕ,
      MeasurableSet {p : ℝ × (ℕ → ℝ) | p.1 < arrivalTime n p.2} := fun n =>
    measurableSet_lt measurable_fst ((measurable_arrivalTime n).comp measurable_snd)
  have hfuture : MeasurableSet
      {p : ℝ × (ℕ → ℝ) | ∃ n : ℕ, p.1 < arrivalTime n p.2} := by
    simpa only [Set.setOf_exists] using
      (MeasurableSet.iUnion htime :
        MeasurableSet (⋃ n : ℕ, {p : ℝ × (ℕ → ℝ) | p.1 < arrivalTime n p.2}))
  refine measurable_to_countable' ?_
  intro n
  cases n with
  | zero =>
      have hpreimage : jointCanonicalRenewalCount ⁻¹' ({0} : Set ℕ) =
          {p : ℝ × (ℕ → ℝ) | p.1 < arrivalTime 0 p.2} ∪
            {p : ℝ × (ℕ → ℝ) | ¬ ∃ n : ℕ, p.1 < arrivalTime n p.2} := by
        ext p
        simpa only [jointCanonicalRenewalCount, Set.mem_preimage,
          Set.mem_singleton_iff, Set.mem_union, Set.mem_setOf_eq] using
          (canonicalRenewalCount_eq_zero_iff p.1 p.2)
      rw [hpreimage]
      exact (htime 0).union hfuture.compl
  | succ n =>
      have hpreimage : jointCanonicalRenewalCount ⁻¹' ({n + 1} : Set ℕ) =
          {p : ℝ × (ℕ → ℝ) | p.1 < arrivalTime (n + 1) p.2 ∧
            ∀ m < n + 1, ¬ p.1 < arrivalTime m p.2} := by
        ext p
        simpa only [jointCanonicalRenewalCount, Set.mem_preimage,
          Set.mem_singleton_iff, Set.mem_setOf_eq] using
          (canonicalRenewalCount_eq_succ_iff p.1 p.2 n)
      rw [hpreimage]
      simp only [Set.setOf_and, Set.setOf_forall, ← Set.compl_setOf]
      repeat' apply_rules [MeasurableSet.inter, MeasurableSet.iInter,
        MeasurableSet.compl, htime] <;> try intros

/-- The future half of a two-sided Palm gap sequence. -/
def suspensionFuturePath : (ℤ → ℝ) → ℕ → ℝ :=
  fun ω n => twoSidedGap (Int.ofNat n) ω

/-- The past half, listed from the nearest past gap outward. -/
def suspensionPastPath : (ℤ → ℝ) → ℕ → ℝ :=
  fun ω n => twoSidedGap (Int.negSucc n) ω

theorem measurable_suspensionFuturePath : Measurable suspensionFuturePath := by
  refine measurable_pi_iff.2 fun n => ?_
  simpa [suspensionFuturePath] using measurable_twoSidedGap (Int.ofNat n)

theorem measurable_suspensionPastPath : Measurable suspensionPastPath := by
  refine measurable_pi_iff.2 fun n => ?_
  simpa [suspensionPastPath] using measurable_twoSidedGap (Int.negSucc n)

/-- Measurability of a two-sided Palm epoch at a fixed integer index. -/
theorem measurable_candidatePalmArrival (i : ℤ) :
    Measurable (fun ω : ℤ → ℝ => candidatePalmArrival ω i) := by
  cases i with
  | ofNat n =>
      change Measurable (fun ω : ℤ → ℝ =>
        ∑ j ∈ Finset.range n, twoSidedGap (Int.ofNat j) ω)
      exact (Finset.range n).measurable_sum fun j _ =>
        measurable_twoSidedGap (Int.ofNat j)
  | negSucc n =>
      change Measurable (fun ω : ℤ → ℝ =>
        -∑ j ∈ Finset.range (n + 1), twoSidedGap (Int.negSucc j) ω)
      exact ((Finset.range (n + 1)).measurable_sum fun j _ =>
        measurable_twoSidedGap (Int.negSucc j)).neg

/-- Reindex a two-sided gap sequence at a deterministic arrival index. -/
def suspensionGapShift (k : ℤ) : (ℤ → ℝ) → ℤ → ℝ :=
  fun ω i => twoSidedGap (i + k) ω

theorem suspensionGapShift_comp
    (j k : ℤ) (ω : ℤ → ℝ) :
    suspensionGapShift j (suspensionGapShift k ω) =
      suspensionGapShift (j + k) ω := by
  funext i
  change ω ((i + j) + k) = ω (i + (j + k))
  rw [add_assoc]

/-- Each deterministic reindexing of the two-sided Palm gap coordinates is
measurable. -/
theorem measurable_suspensionGapShift (k : ℤ) :
    Measurable (suspensionGapShift k) := by
  exact measurable_pi_iff.2 fun i => measurable_twoSidedGap (i + k)

/-- A deterministic reindexing retains independence of the exponential gap
coordinates. -/
theorem iIndepFun_suspensionGapShift
    {rate : ℝ} (hrate : 0 < rate) (k : ℤ) :
    ProbabilityTheory.iIndepFun (fun i ω => twoSidedGap (i + k) ω)
      (twoSidedInterarrivalMeasure rate) := by
  exact ProbabilityTheory.iIndepFun.precomp
    (g := fun i : ℤ => i + k)
    (by intro a b hab; exact add_right_cancel hab)
    (iIndepFun_twoSidedGap hrate)

/-- The iid two-sided Palm gap law is invariant under every deterministic
arrival-index reindexing. -/
theorem suspensionGapShift_measurePreserving
    {rate : ℝ} (hrate : 0 < rate) (k : ℤ) :
    MeasurePreserving (suspensionGapShift k)
      (twoSidedInterarrivalMeasure rate) (twoSidedInterarrivalMeasure rate) := by
  refine ⟨measurable_suspensionGapShift k, ?_⟩
  change Measure.map (fun ω i => twoSidedGap (i + k) ω)
    (twoSidedInterarrivalMeasure rate) = twoSidedInterarrivalMeasure rate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  rw [ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun i => measurable_twoSidedGap (i + k)) |>.mp
    (iIndepFun_suspensionGapShift hrate k)]
  simp only [twoSidedInterarrivalMeasure]
  congr 1
  funext i
  exact (twoSidedGap_hasLaw hrate (i + k)).map_eq

/-- Recentered arrival epochs are exactly the original epochs relative to the
new tag. -/
theorem candidatePalmArrival_suspensionGapShift
    (ω : ℤ → ℝ) (k j : ℤ) :
    candidatePalmArrival (suspensionGapShift k ω) j =
      candidatePalmArrival ω (k + j) - candidatePalmArrival ω k := by
  simpa [suspensionGapShift, twoSidedGap] using candidatePalmArrival_recenter ω k j

/-- Phase membership in a half-open gap is equivalent to locating the clock
between the corresponding two consecutive Palm arrivals. -/
theorem candidatePalmArrival_phase_mem_iff
    (ω : ℤ → ℝ) (k : ℤ) (s : ℝ) :
    s - candidatePalmArrival ω k ∈ Set.Ico 0 (twoSidedGap k ω) ↔
      candidatePalmArrival ω k ≤ s ∧ s < candidatePalmArrival ω (k + 1) := by
  change s - candidatePalmArrival ω k ∈ Set.Ico 0 (ω k) ↔ _
  rw [candidatePalmArrival_add_one]
  constructor <;> intro h <;> rcases h with ⟨hleft, hright⟩ <;> constructor <;> linarith

/-- Strictly ordered half-open arrival intervals have unique integer labels. -/
theorem candidatePalmArrival_interval_index_unique
    (ω : ℤ → ℝ) (hstrict : StrictMono (candidatePalmArrival ω))
    {i j : ℤ} {s : ℝ}
    (hi : candidatePalmArrival ω i ≤ s ∧ s < candidatePalmArrival ω (i + 1))
    (hj : candidatePalmArrival ω j ≤ s ∧ s < candidatePalmArrival ω (j + 1)) :
    i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hsucc : i + 1 ≤ j := by omega
    have harrival : candidatePalmArrival ω (i + 1) ≤ candidatePalmArrival ω j :=
      hstrict.monotone hsucc
    linarith [hi.2, hj.1]
  · have hsucc : j + 1 ≤ i := by omega
    have harrival : candidatePalmArrival ω (j + 1) ≤ candidatePalmArrival ω i :=
      hstrict.monotone hsucc
    linarith [hj.2, hi.1]

/-- A measurable crossing-index convention for the special-flow formula.
Away from exact negative arrival epochs it is the index of the interval
containing `u + t`. At those null boundary points its strict-count convention
chooses the preceding index; a future `≤`-based inverse will repair that
pointwise action convention before flow laws are claimed. -/
def suspensionCrossingIndex (t : ℝ) : ((ℤ → ℝ) × ℝ) → ℤ :=
  fun p => if 0 ≤ p.2 + t then
    Int.ofNat (canonicalRenewalCount (p.2 + t) (suspensionFuturePath p.1))
  else
    Int.negSucc (canonicalRenewalCount (-(p.2 + t)) (suspensionPastPath p.1))

theorem measurable_suspensionCrossingIndex (t : ℝ) :
    Measurable (suspensionCrossingIndex t) := by
  have hforward : Measurable (fun p : (ℤ → ℝ) × ℝ =>
      canonicalRenewalCount (p.2 + t) (suspensionFuturePath p.1)) := by
    exact measurable_jointCanonicalRenewalCount.comp
      ((measurable_snd.add_const t).prodMk
        (measurable_suspensionFuturePath.comp measurable_fst))
  have hbackward : Measurable (fun p : (ℤ → ℝ) × ℝ =>
      canonicalRenewalCount (-(p.2 + t)) (suspensionPastPath p.1)) := by
    exact measurable_jointCanonicalRenewalCount.comp
      ((measurable_snd.add_const t).neg.prodMk
        (measurable_suspensionPastPath.comp measurable_fst))
  unfold suspensionCrossingIndex
  refine Measurable.ite
    (measurableSet_le measurable_const (measurable_snd.add_const t))
    ?_ ?_
  · exact (measurable_of_countable (Int.ofNat : ℕ → ℤ)).comp hforward
  · exact (measurable_of_countable (Int.negSucc : ℕ → ℤ)).comp hbackward

/-- Boundary-correct crossing index for the half-open carrier convention.
The future uses the first epoch strictly after the clock, whereas the reflected
past uses the first epoch at or after the reflected clock. -/
def suspensionCrossingIndexPastClosed (t : ℝ) : ((ℤ → ℝ) × ℝ) → ℤ :=
  fun p => if 0 ≤ p.2 + t then
    Int.ofNat (canonicalRenewalCount (p.2 + t) (suspensionFuturePath p.1))
  else
    Int.negSucc (canonicalRenewalCountLE (-(p.2 + t)) (suspensionPastPath p.1))

theorem measurable_suspensionCrossingIndexPastClosed (t : ℝ) :
    Measurable (suspensionCrossingIndexPastClosed t) := by
  have hforward : Measurable (fun p : (ℤ → ℝ) × ℝ =>
      canonicalRenewalCount (p.2 + t) (suspensionFuturePath p.1)) := by
    exact measurable_jointCanonicalRenewalCount.comp
      ((measurable_snd.add_const t).prodMk
        (measurable_suspensionFuturePath.comp measurable_fst))
  have hbackward : Measurable (fun p : (ℤ → ℝ) × ℝ =>
      canonicalRenewalCountLE (-(p.2 + t)) (suspensionPastPath p.1)) := by
    exact measurable_jointCanonicalRenewalCountLE.comp
      ((measurable_snd.add_const t).neg.prodMk
        (measurable_suspensionPastPath.comp measurable_fst))
  unfold suspensionCrossingIndexPastClosed
  refine Measurable.ite
    (measurableSet_le measurable_const (measurable_snd.add_const t))
    ?_ ?_
  · exact (measurable_of_countable (Int.ofNat : ℕ → ℤ)).comp hforward
  · exact (measurable_of_countable (Int.negSucc : ℕ → ℤ)).comp hbackward

theorem candidateFutureEpoch_succ_eq_arrivalTime_suspension
    (ω : ℤ → ℝ) (n : ℕ) :
    candidateFutureEpoch ω (n + 1) = arrivalTime n (suspensionFuturePath ω) := by
  simp [candidateFutureEpoch, arrivalTime, suspensionFuturePath, interarrival]

theorem candidateFutureEpoch_succ
    (ω : ℤ → ℝ) (n : ℕ) :
    candidateFutureEpoch ω (n + 1) =
      candidateFutureEpoch ω n + twoSidedGap (Int.ofNat n) ω := by
  simp [candidateFutureEpoch, Finset.sum_range_succ]

/-- On a divergent future half, the strict renewal inverse places the clock
in the claimed half-open Palm gap. -/
theorem forward_crossing_phase_mem
    (ω : ℤ → ℝ)
    (hdiv : Tendsto (fun n : ℕ => arrivalTime n (suspensionFuturePath ω)) atTop atTop)
    (s : ℝ) (hs : 0 ≤ s) :
    let n := canonicalRenewalCount s (suspensionFuturePath ω)
    s - candidateFutureEpoch ω n ∈ Set.Ico 0 (twoSidedGap (Int.ofNat n) ω) := by
  dsimp
  generalize hn : canonicalRenewalCount s (suspensionFuturePath ω) = n
  have hfuture : ∃ m : ℕ, s < arrivalTime m (suspensionFuturePath ω) :=
    exists_arrivalTime_gt_of_tendsto_atTop _ hdiv s
  have hupper : s < arrivalTime n (suspensionFuturePath ω) := by
    rw [← hn]
    exact lt_arrivalTime_canonicalRenewalCount s (suspensionFuturePath ω) hfuture
  have hlower : candidateFutureEpoch ω n ≤ s := by
    cases n with
    | zero => simp [candidateFutureEpoch, hs]
    | succ m =>
        have hm_lt : m < canonicalRenewalCount s (suspensionFuturePath ω) := by
          rw [hn]
          exact Nat.lt_succ_self m
        have hcompleted : arrivalTime m (suspensionFuturePath ω) ≤ s :=
          arrivalTime_le_of_lt_canonicalRenewalCount s (suspensionFuturePath ω)
            hfuture hm_lt
        rw [candidateFutureEpoch_succ_eq_arrivalTime_suspension]
        exact hcompleted
  have hupper' : s < candidateFutureEpoch ω (n + 1) := by
    rw [candidateFutureEpoch_succ_eq_arrivalTime_suspension]
    exact hupper
  rw [candidateFutureEpoch_succ] at hupper'
  have hupper'' : s < candidateFutureEpoch ω n + twoSidedGap (↑n : ℤ) ω := by
    simpa only [Int.ofNat_eq_natCast] using hupper'
  constructor
  · linarith
  · linarith

theorem candidatePastGapSum_succ_eq_arrivalTime_suspension
    (ω : ℤ → ℝ) (n : ℕ) :
    candidatePastGapSum ω (n + 1) = arrivalTime n (suspensionPastPath ω) := by
  simp [candidatePastGapSum, arrivalTime, suspensionPastPath, interarrival]

theorem candidatePastGapSum_succ
    (ω : ℤ → ℝ) (n : ℕ) :
    candidatePastGapSum ω (n + 1) =
      candidatePastGapSum ω n + twoSidedGap (Int.negSucc n) ω := by
  simp [candidatePastGapSum, Finset.sum_range_succ]

/-- On a divergent past half, the left-continuous reflected inverse places a
negative clock in the claimed half-open Palm gap, including exact arrivals. -/
theorem past_crossing_phase_mem
    (ω : ℤ → ℝ)
    (hdiv : Tendsto (fun n : ℕ => arrivalTime n (suspensionPastPath ω)) atTop atTop)
    (s : ℝ) (hs : s < 0) :
    let n := canonicalRenewalCountLE (-s) (suspensionPastPath ω)
    s - candidatePalmArrival ω (Int.negSucc n) ∈
      Set.Ico 0 (twoSidedGap (Int.negSucc n) ω) := by
  dsimp
  generalize hn : canonicalRenewalCountLE (-s) (suspensionPastPath ω) = n
  have hypos : 0 < -s := neg_pos.mpr hs
  have hfuture_strict : ∃ m : ℕ, -s < arrivalTime m (suspensionPastPath ω) :=
    exists_arrivalTime_gt_of_tendsto_atTop _ hdiv (-s)
  have hfuture : ∃ m : ℕ, -s ≤ arrivalTime m (suspensionPastPath ω) :=
    hfuture_strict.imp fun m hm => hm.le
  have hle : -s ≤ arrivalTime n (suspensionPastPath ω) := by
    rw [← hn]
    exact le_arrivalTime_canonicalRenewalCountLE (-s) (suspensionPastPath ω) hfuture
  have hle' : -s ≤ candidatePastGapSum ω (n + 1) := by
    rw [candidatePastGapSum_succ_eq_arrivalTime_suspension]
    exact hle
  have hphase_nonneg : 0 ≤ s + candidatePastGapSum ω (n + 1) := by
    linarith
  have hphase_lt : s + candidatePastGapSum ω (n + 1) <
      twoSidedGap (Int.negSucc n) ω := by
    cases n with
    | zero =>
        have hsum : candidatePastGapSum ω (0 + 1) =
            twoSidedGap (Int.negSucc 0) ω := by
          simp [candidatePastGapSum]
        rw [hsum]
        linarith
    | succ m =>
        have hm_lt : m < canonicalRenewalCountLE (-s) (suspensionPastPath ω) := by
          rw [hn]
          exact Nat.lt_succ_self m
        have hprev : arrivalTime m (suspensionPastPath ω) < -s :=
          arrivalTime_lt_of_lt_canonicalRenewalCountLE (-s) (suspensionPastPath ω)
            hfuture hm_lt
        have hprev' : candidatePastGapSum ω (m + 1) < -s := by
          rw [candidatePastGapSum_succ_eq_arrivalTime_suspension]
          exact hprev
        rw [show (m + 1 + 1 : ℕ) = (m + 1) + 1 by omega,
          candidatePastGapSum_succ]
        linarith
  rw [candidatePalmArrival_negSucc]
  constructor <;> linarith

/-- The unquotiented suspension strip: phase lies in the half-open roof
interval. -/
def suspensionCarrier : Set ((ℤ → ℝ) × ℝ) :=
  {p | 0 ≤ p.2 ∧ p.2 < twoSidedGap 0 p.1}

theorem measurableSet_suspensionCarrier : MeasurableSet suspensionCarrier := by
  exact (measurableSet_le measurable_const measurable_snd).inter
    (measurableSet_lt measurable_snd ((measurable_twoSidedGap 0).comp measurable_fst))

/-- The unnormalized suspension-strip mass is the mean Palm roof length. -/
theorem suspensionCarrier_mass (rate : ℝ) :
    ((twoSidedInterarrivalMeasure rate).prod volume) suspensionCarrier =
      ∫⁻ ω, ENNReal.ofReal (twoSidedGap 0 ω)
        ∂twoSidedInterarrivalMeasure rate := by
  rw [Measure.prod_apply measurableSet_suspensionCarrier]
  congr 1
  funext ω
  have hfiber : (fun u : ℝ => (ω, u)) ⁻¹' suspensionCarrier =
      Set.Ico 0 (twoSidedGap 0 ω) := by
    ext u
    simp [suspensionCarrier]
  rw [hfiber, Real.volume_Ico]
  simp

/-- The Palm roof coordinate has the usual finite exponential mean. -/
theorem integrable_twoSidedGap_zero
    {rate : ℝ} (hrate : 0 < rate) :
    Integrable (twoSidedGap 0) (twoSidedInterarrivalMeasure rate) := by
  let M : Exponential.Model := Exponential.Model.mk rate hrate
  have hExp : Integrable (fun x : ℝ => x) (ProbabilityTheory.expMeasure rate) := by
    simpa [Exponential.Model.measure, M] using M.integrable_id
  have hmap : Measure.map (twoSidedGap 0) (twoSidedInterarrivalMeasure rate) =
      ProbabilityTheory.expMeasure rate :=
    (twoSidedGap_hasLaw hrate 0).map_eq
  have hmapInt : Integrable (fun x : ℝ => x)
      (Measure.map (twoSidedGap 0) (twoSidedInterarrivalMeasure rate)) := by
    rw [hmap]
    exact hExp
  simpa [Function.comp_def] using
    (integrable_map_measure aestronglyMeasurable_id
      (measurable_twoSidedGap 0).aemeasurable).mp hmapInt

theorem integral_twoSidedGap_zero_eq_inv_rate
    {rate : ℝ} (hrate : 0 < rate) :
    (∫ ω, twoSidedGap 0 ω ∂twoSidedInterarrivalMeasure rate) = 1 / rate := by
  let M : Exponential.Model := Exponential.Model.mk rate hrate
  calc
    (∫ ω, twoSidedGap 0 ω ∂twoSidedInterarrivalMeasure rate) =
        ∫ x, x ∂ProbabilityTheory.expMeasure rate :=
      (twoSidedGap_hasLaw hrate 0).integral_eq
    _ = M.expectedMaxValue 1 := by
      simpa [Exponential.Model.measure, M] using M.integral_id_eq_expectedMaxValue_one
    _ = 1 / rate := by
      simp [Exponential.Model.expectedMaxValue,
        Exponential.expectedMaxValueOfRate_one, M]

/-- The strip has mass `1 / rate`; this normalizes the special-flow base
measure. -/
theorem suspensionCarrier_mass_eq_inv_rate
    {rate : ℝ} (hrate : 0 < rate) :
    ((twoSidedInterarrivalMeasure rate).prod volume) suspensionCarrier =
      ENNReal.ofReal (1 / rate) := by
  rw [suspensionCarrier_mass]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (integrable_twoSidedGap_zero hrate)]
  · rw [integral_twoSidedGap_zero_eq_inv_rate hrate]
  · filter_upwards [ae_all_twoSidedGap_positive hrate] with ω hω
    exact (hω 0).le

/-- Probability law on the unquotiented strip obtained by normalizing its
Palm-product measure at intensity `rate`. Its real-time invariance is proved
below by gluing the deterministic crossing-index branches. -/
def suspensionMeasure (rate : ℝ) : Measure ((ℤ → ℝ) × ℝ) :=
  ENNReal.ofReal rate •
    ((twoSidedInterarrivalMeasure rate).prod volume).restrict suspensionCarrier

theorem suspensionMeasure_univ
    {rate : ℝ} (hrate : 0 < rate) :
    suspensionMeasure rate Set.univ = 1 := by
  rw [suspensionMeasure, Measure.smul_apply, Measure.restrict_apply_univ,
    suspensionCarrier_mass_eq_inv_rate hrate]
  rw [show 1 / rate = rate⁻¹ by rw [one_div]]
  rw [ENNReal.ofReal_inv_of_pos hrate]
  rw [smul_eq_mul]
  exact ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr hrate)
    ENNReal.ofReal_ne_top

/-- The normalized suspension strip is a genuine probability law. -/
theorem isProbabilityMeasure_suspensionMeasure
    {rate : ℝ} (hrate : 0 < rate) :
    IsProbabilityMeasure (suspensionMeasure rate) :=
  ⟨suspensionMeasure_univ hrate⟩

/-- The real-time special-flow formula on the unquotiented suspension strip.
Its restriction to `suspensionCarrier` is the stationary Poisson shift;
measure preservation is proved below. -/
def suspensionFlow (t : ℝ) : ((ℤ → ℝ) × ℝ) → ((ℤ → ℝ) × ℝ) :=
  fun p =>
    let k := suspensionCrossingIndexPastClosed t p
    (suspensionGapShift k p.1,
      p.2 + t - candidatePalmArrival p.1 k)

theorem measurable_suspensionFlow (t : ℝ) : Measurable (suspensionFlow t) := by
  have hk := measurable_suspensionCrossingIndexPastClosed t
  have heval : Measurable (fun q : ℤ × (ℤ → ℝ) => twoSidedGap q.1 q.2) := by
    exact measurable_from_prod_countable_right fun i => measurable_twoSidedGap i
  have hshift : Measurable (fun p : (ℤ → ℝ) × ℝ =>
      suspensionGapShift (suspensionCrossingIndexPastClosed t p) p.1) := by
    refine measurable_pi_iff.2 fun i => ?_
    exact heval.comp ((measurable_const.add hk).prodMk measurable_fst)
  have harrivalEval : Measurable (fun q : ℤ × (ℤ → ℝ) =>
      candidatePalmArrival q.2 q.1) := by
    exact measurable_from_prod_countable_right fun i => measurable_candidatePalmArrival i
  unfold suspensionFlow
  exact hshift.prodMk ((measurable_snd.add_const t).sub
    (harrivalEval.comp (hk.prodMk measurable_fst)))

/-- The deterministic branch obtained when the crossing label is fixed in
advance. These branches preserve the Palm-gap product measure; the remaining
real-time invariance proof glues them along their random crossing slabs. -/
def suspensionFixedIndexFlow (t : ℝ) (k : ℤ) :
    ((ℤ → ℝ) × ℝ) → ((ℤ → ℝ) × ℝ) :=
  fun p => (suspensionGapShift k p.1,
    p.2 + t - candidatePalmArrival p.1 k)

theorem measurable_suspensionFixedIndexFlow (t : ℝ) (k : ℤ) :
    Measurable (suspensionFixedIndexFlow t k) := by
  unfold suspensionFixedIndexFlow
  exact (measurable_suspensionGapShift k).comp measurable_fst |>.prodMk
    ((measurable_snd.add_const t).sub
      ((measurable_candidatePalmArrival k).comp measurable_fst))

theorem suspensionFixedIndexFlow_neg_comp
    (t : ℝ) (k : ℤ) (p : (ℤ → ℝ) × ℝ) :
    suspensionFixedIndexFlow (-t) (-k) (suspensionFixedIndexFlow t k p) = p := by
  rcases p with ⟨ω, u⟩
  have hshift :
      suspensionGapShift (-k) (suspensionGapShift k ω) = ω := by
    funext i
    change ω ((i + -k) + k) = ω i
    congr 1
    omega
  have harr : candidatePalmArrival (suspensionGapShift k ω) (-k) =
      -candidatePalmArrival ω k := by
    rw [candidatePalmArrival_suspensionGapShift]
    simp [candidatePalmArrival]
  simp only [suspensionFixedIndexFlow, hshift, harr]
  ring_nf

theorem suspensionFixedIndexFlow_comp_neg
    (t : ℝ) (k : ℤ) (p : (ℤ → ℝ) × ℝ) :
    suspensionFixedIndexFlow t k (suspensionFixedIndexFlow (-t) (-k) p) = p := by
  rcases p with ⟨ω, u⟩
  have hshift :
      suspensionGapShift k (suspensionGapShift (-k) ω) = ω := by
    funext i
    change ω ((i + k) + -k) = ω i
    congr 1
    omega
  have harr : candidatePalmArrival (suspensionGapShift (-k) ω) k =
      -candidatePalmArrival ω (-k) := by
    rw [candidatePalmArrival_suspensionGapShift]
    simp [candidatePalmArrival]
  simp only [suspensionFixedIndexFlow, hshift, harr]
  ring_nf

/-- The fixed-label special-flow branch is a measurable equivalence with the
opposite time and opposite integer label as inverse. -/
def suspensionFixedIndexFlowEquiv (t : ℝ) (k : ℤ) :
    ((ℤ → ℝ) × ℝ) ≃ᵐ ((ℤ → ℝ) × ℝ) where
  toFun := suspensionFixedIndexFlow t k
  invFun := suspensionFixedIndexFlow (-t) (-k)
  left_inv := suspensionFixedIndexFlow_neg_comp t k
  right_inv := suspensionFixedIndexFlow_comp_neg t k
  measurable_toFun := measurable_suspensionFixedIndexFlow t k
  measurable_invFun := measurable_suspensionFixedIndexFlow (-t) (-k)

/-- A fixed-label branch preserves iid Palm gaps times Lebesgue phase
measure. -/
theorem suspensionFixedIndexFlow_measurePreserving
    {rate : ℝ} (hrate : 0 < rate) (t : ℝ) (k : ℤ) :
    MeasurePreserving (suspensionFixedIndexFlow t k)
      ((twoSidedInterarrivalMeasure rate).prod volume)
      ((twoSidedInterarrivalMeasure rate).prod volume) := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  refine MeasurePreserving.skew_product
    (suspensionGapShift_measurePreserving hrate k)
    (g := fun ω (u : ℝ) => u + t - candidatePalmArrival ω k) ?_ ?_
  · exact (measurable_snd.add_const t).sub
      ((measurable_candidatePalmArrival k).comp measurable_fst)
  · filter_upwards with ω
    simpa [sub_eq_add_neg, add_assoc] using
      (measurePreserving_add_right volume
        (t - candidatePalmArrival ω k)).map_eq

/-- On a crossing-index slab the random-label special flow is exactly the
corresponding deterministic branch. -/
theorem suspensionFlow_eq_suspensionFixedIndexFlow_of_crossing
    (t : ℝ) (k : ℤ) (p : (ℤ → ℝ) × ℝ)
    (hk : suspensionCrossingIndexPastClosed t p = k) :
    suspensionFlow t p = suspensionFixedIndexFlow t k p := by
  unfold suspensionFlow suspensionFixedIndexFlow
  simp only [hk]

/-- The measurable crossing-index slab for one real-time translation and
one integer label. -/
def suspensionCrossingSlab (t : ℝ) (k : ℤ) : Set ((ℤ → ℝ) × ℝ) :=
  {p | suspensionCrossingIndexPastClosed t p = k}

theorem measurableSet_suspensionCrossingSlab (t : ℝ) (k : ℤ) :
    MeasurableSet (suspensionCrossingSlab t k) := by
  change MeasurableSet ((suspensionCrossingIndexPastClosed t) ⁻¹' {k})
  exact (measurable_suspensionCrossingIndexPastClosed t) (measurableSet_singleton k)

/-- A single crossing slab is transported exactly to its fixed-branch image.
This is the local measure-preservation component of the suspension-flow
invariance proof. -/
theorem suspensionFlow_restrict_crossingSlab_measurePreserving
    {rate : ℝ} (hrate : 0 < rate) (t : ℝ) (k : ℤ) :
    MeasurePreserving (suspensionFlow t)
      (((twoSidedInterarrivalMeasure rate).prod volume).restrict
        (suspensionCrossingSlab t k))
      (((twoSidedInterarrivalMeasure rate).prod volume).restrict
        (suspensionFixedIndexFlow t k '' suspensionCrossingSlab t k)) := by
  refine ((suspensionFixedIndexFlow_measurePreserving hrate t k).restrict_image_emb
    (suspensionFixedIndexFlowEquiv t k).measurableEmbedding
      (suspensionCrossingSlab t k)).congr (measurable_suspensionFlow t) ?_
  filter_upwards [ae_restrict_mem (measurableSet_suspensionCrossingSlab t k)] with p hp
  exact (suspensionFlow_eq_suspensionFixedIndexFlow_of_crossing t k p hp).symm

/-- On a path whose two renewal halves diverge, the boundary-correct special
flow formula lands in the half-open suspension carrier at every real time. -/
theorem suspensionFlow_mem_suspensionCarrier
    (ω : ℤ → ℝ)
    (hfuture : Tendsto (fun n : ℕ => arrivalTime n (suspensionFuturePath ω)) atTop atTop)
    (hpast : Tendsto (fun n : ℕ => arrivalTime n (suspensionPastPath ω)) atTop atTop)
    (u t : ℝ) :
    suspensionFlow t (ω, u) ∈ suspensionCarrier := by
  by_cases hs : 0 ≤ u + t
  · have hphase := forward_crossing_phase_mem ω hfuture (u + t) hs
    simp only [suspensionFlow, suspensionCrossingIndexPastClosed, hs, ↓reduceIte,
      suspensionCarrier, candidatePalmArrival_ofNat]
    simpa [suspensionGapShift, twoSidedGap] using hphase
  · have hphase := past_crossing_phase_mem ω hpast (u + t) (lt_of_not_ge hs)
    simp only [suspensionFlow, suspensionCrossingIndexPastClosed, hs, ↓reduceIte,
      suspensionCarrier]
    simpa [suspensionGapShift, twoSidedGap] using hphase

/-- The crossing index used by the flow is precisely the candidate-arrival
interval label containing the translated clock. -/
theorem suspensionCrossingIndexPastClosed_interval
    (ω : ℤ → ℝ)
    (hfuture : Tendsto (fun n : ℕ => arrivalTime n (suspensionFuturePath ω)) atTop atTop)
    (hpast : Tendsto (fun n : ℕ => arrivalTime n (suspensionPastPath ω)) atTop atTop)
    (u t : ℝ) :
    let k := suspensionCrossingIndexPastClosed t (ω, u)
    candidatePalmArrival ω k ≤ u + t ∧ u + t < candidatePalmArrival ω (k + 1) := by
  dsimp
  generalize hk : suspensionCrossingIndexPastClosed t (ω, u) = k
  have hcarrier := suspensionFlow_mem_suspensionCarrier ω hfuture hpast u t
  have hphase : u + t - candidatePalmArrival ω k ∈ Set.Ico 0 (twoSidedGap k ω) := by
    rw [← hk]
    simpa [suspensionFlow, suspensionCarrier, suspensionGapShift, twoSidedGap] using hcarrier
  exact (candidatePalmArrival_phase_mem_iff ω k (u + t)).mp hphase

/-- Conditional cocycle for the crossing index. The only hypotheses beyond
the original path's divergence are the same two divergence facts for every
integer reindexing; proving that closure is the remaining path-space seam. -/
theorem suspensionCrossingIndexPastClosed_cocycle_of_reindex_divergence
    (ω : ℤ → ℝ)
    (hstrict : StrictMono (candidatePalmArrival ω))
    (hfuture : Tendsto (fun n : ℕ => arrivalTime n (suspensionFuturePath ω)) atTop atTop)
    (hpast : Tendsto (fun n : ℕ => arrivalTime n (suspensionPastPath ω)) atTop atTop)
    (hreindex : ∀ k : ℤ,
      Tendsto (fun n : ℕ =>
        arrivalTime n (suspensionFuturePath (suspensionGapShift k ω))) atTop atTop ∧
      Tendsto (fun n : ℕ =>
        arrivalTime n (suspensionPastPath (suspensionGapShift k ω))) atTop atTop)
    (u t r : ℝ) :
    suspensionCrossingIndexPastClosed r (suspensionFlow t (ω, u)) +
        suspensionCrossingIndexPastClosed t (ω, u) =
      suspensionCrossingIndexPastClosed (t + r) (ω, u) := by
  set k := suspensionCrossingIndexPastClosed t (ω, u) with hk
  set p := suspensionFlow t (ω, u) with hp
  set l := suspensionCrossingIndexPastClosed r p with hl
  set m := suspensionCrossingIndexPastClosed (t + r) (ω, u) with hm
  change l + k = m
  have hp' : p = (suspensionGapShift k ω,
      u + t - candidatePalmArrival ω k) := by
    rw [hp, hk]
    rfl
  rcases hreindex k with ⟨hfuture_k, hpast_k⟩
  have hl_interval_raw := suspensionCrossingIndexPastClosed_interval
    (suspensionGapShift k ω) hfuture_k hpast_k
      (u + t - candidatePalmArrival ω k) r
  have hl_interval :
      candidatePalmArrival (suspensionGapShift k ω) l ≤
          (u + t - candidatePalmArrival ω k) + r ∧
        (u + t - candidatePalmArrival ω k) + r <
          candidatePalmArrival (suspensionGapShift k ω) (l + 1) := by
    simpa only [hl, hp'] using hl_interval_raw
  rw [candidatePalmArrival_suspensionGapShift,
    candidatePalmArrival_suspensionGapShift] at hl_interval
  have hkl_interval :
      candidatePalmArrival ω (k + l) ≤ u + (t + r) ∧
        u + (t + r) < candidatePalmArrival ω ((k + l) + 1) := by
    constructor
    · linarith [hl_interval.1]
    · have hindex : k + (l + 1) = (k + l) + 1 := by ring
      rw [hindex] at hl_interval
      linarith [hl_interval.2]
  have hm_interval_raw := suspensionCrossingIndexPastClosed_interval ω hfuture hpast u (t + r)
  have hm_interval :
      candidatePalmArrival ω m ≤ u + (t + r) ∧
        u + (t + r) < candidatePalmArrival ω (m + 1) := by
    simpa only [hm] using hm_interval_raw
  have hkm : k + l = m :=
    candidatePalmArrival_interval_index_unique ω hstrict hkl_interval hm_interval
  linarith

/-- Conditional real-time special-flow law. The later good-path construction
discharges the reindexing hypotheses and supplies the pointwise action field
required by `ShiftInvariantProbabilityLaw`. -/
theorem suspensionFlow_add_of_reindex_divergence
    (ω : ℤ → ℝ)
    (hstrict : StrictMono (candidatePalmArrival ω))
    (hfuture : Tendsto (fun n : ℕ => arrivalTime n (suspensionFuturePath ω)) atTop atTop)
    (hpast : Tendsto (fun n : ℕ => arrivalTime n (suspensionPastPath ω)) atTop atTop)
    (hreindex : ∀ k : ℤ,
      Tendsto (fun n : ℕ =>
        arrivalTime n (suspensionFuturePath (suspensionGapShift k ω))) atTop atTop ∧
      Tendsto (fun n : ℕ =>
        arrivalTime n (suspensionPastPath (suspensionGapShift k ω))) atTop atTop)
    (u t r : ℝ) :
    suspensionFlow r (suspensionFlow t (ω, u)) =
      suspensionFlow (t + r) (ω, u) := by
  set k := suspensionCrossingIndexPastClosed t (ω, u) with hk
  set p := suspensionFlow t (ω, u) with hp
  set l := suspensionCrossingIndexPastClosed r p with hl
  set m := suspensionCrossingIndexPastClosed (t + r) (ω, u) with hm
  have hp' : p = (suspensionGapShift k ω,
      u + t - candidatePalmArrival ω k) := by
    rw [hp, hk]
    rfl
  have hcross : l + k = m := by
    have h := suspensionCrossingIndexPastClosed_cocycle_of_reindex_divergence
      ω hstrict hfuture hpast hreindex u t r
    simpa only [hl, hk, hm, hp] using h
  have hl' : suspensionCrossingIndexPastClosed r
      (suspensionGapShift k ω, u + t - candidatePalmArrival ω k) = l := by
    simp only [hl, hp']
  have hm' : suspensionCrossingIndexPastClosed (t + r) (ω, u) = m := by
    simp only [hm]
  rw [hp']
  simp only [suspensionFlow, hl', hm']
  apply Prod.ext
  · rw [suspensionGapShift_comp, hcross]
  · have hcross' : k + l = m := by linarith [hcross]
    rw [candidatePalmArrival_suspensionGapShift, hcross']
    ring

/-- Same conditional law in the composition order used by
`ShiftInvariantProbabilityLaw.shift_add`. -/
theorem suspensionFlow_action_of_reindex_divergence
    (ω : ℤ → ℝ)
    (hstrict : StrictMono (candidatePalmArrival ω))
    (hfuture : Tendsto (fun n : ℕ => arrivalTime n (suspensionFuturePath ω)) atTop atTop)
    (hpast : Tendsto (fun n : ℕ => arrivalTime n (suspensionPastPath ω)) atTop atTop)
    (hreindex : ∀ k : ℤ,
      Tendsto (fun n : ℕ =>
        arrivalTime n (suspensionFuturePath (suspensionGapShift k ω))) atTop atTop ∧
      Tendsto (fun n : ℕ =>
        arrivalTime n (suspensionPastPath (suspensionGapShift k ω))) atTop atTop)
    (u s t : ℝ) :
    suspensionFlow s (suspensionFlow t (ω, u)) =
      suspensionFlow (s + t) (ω, u) := by
  simpa [add_comm] using
    (suspensionFlow_add_of_reindex_divergence ω hstrict hfuture hpast hreindex u t s)

/-- Deterministic arrival-index reindexing preserves the almost-sure
nonexplosion of both renewal halves. Countability of `ℤ` makes this property
simultaneous in every deterministic reindex. -/
theorem ae_all_suspensionGapShift_nonexplosion
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ ω ∂twoSidedInterarrivalMeasure rate, ∀ k : ℤ,
      Tendsto (fun n : ℕ =>
        arrivalTime n (suspensionFuturePath (suspensionGapShift k ω))) atTop atTop ∧
      Tendsto (fun n : ℕ =>
        arrivalTime n (suspensionPastPath (suspensionGapShift k ω))) atTop atTop := by
  rw [ae_all_iff]
  intro k
  have hbase : ∀ᵐ ξ ∂twoSidedInterarrivalMeasure rate,
      Tendsto (fun n : ℕ => arrivalTime n (suspensionFuturePath ξ)) atTop atTop ∧
      Tendsto (fun n : ℕ => arrivalTime n (suspensionPastPath ξ)) atTop atTop := by
    filter_upwards [ae_candidateFutureEpoch_succ_tendsto_atTop hrate,
      ae_candidatePastGapSum_succ_tendsto_atTop hrate] with ξ hfuture hpast
    constructor
    · simpa only [← candidateFutureEpoch_succ_eq_arrivalTime_suspension] using hfuture
    · simpa only [← candidatePastGapSum_succ_eq_arrivalTime_suspension] using hpast
  have hmap : ∀ᵐ ξ ∂Measure.map (suspensionGapShift k)
      (twoSidedInterarrivalMeasure rate),
      Tendsto (fun n : ℕ => arrivalTime n (suspensionFuturePath ξ)) atTop atTop ∧
      Tendsto (fun n : ℕ => arrivalTime n (suspensionPastPath ξ)) atTop atTop := by
    rw [(suspensionGapShift_measurePreserving hrate k).map_eq]
    exact hbase
  exact ae_of_ae_map (measurable_suspensionGapShift k).aemeasurable hmap

/-- Almost every iid exponential Palm gap sequence gives a pointwise
special-flow action simultaneously for all phases and real times. -/
theorem ae_all_suspensionFlow_action
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ ω ∂twoSidedInterarrivalMeasure rate, ∀ u s t : ℝ,
      suspensionFlow s (suspensionFlow t (ω, u)) =
        suspensionFlow (s + t) (ω, u) := by
  filter_upwards [ae_all_twoSidedGap_positive hrate,
    ae_candidateFutureEpoch_succ_tendsto_atTop hrate,
    ae_candidatePastGapSum_succ_tendsto_atTop hrate,
    ae_all_suspensionGapShift_nonexplosion hrate] with ω hpositive hfuture hpast hreindex
  have hstrict : StrictMono (candidatePalmArrival ω) :=
    candidatePalmArrival_strictMono_of_positive ω hpositive
  have hfuture' :
      Tendsto (fun n : ℕ => arrivalTime n (suspensionFuturePath ω)) atTop atTop := by
    simpa only [← candidateFutureEpoch_succ_eq_arrivalTime_suspension] using hfuture
  have hpast' :
      Tendsto (fun n : ℕ => arrivalTime n (suspensionPastPath ω)) atTop atTop := by
    simpa only [← candidatePastGapSum_succ_eq_arrivalTime_suspension] using hpast
  intro u s t
  exact suspensionFlow_action_of_reindex_divergence ω hstrict hfuture' hpast' hreindex u s t

/-- A path on which every gap is positive and both renewal halves remain
nonexplosive after every integer reindexing. This is the full-measure carrier
on which the special flow is a literal pointwise action. -/
def suspensionGoodGapPath (ω : ℤ → ℝ) : Prop :=
  (∀ i : ℤ, 0 < twoSidedGap i ω) ∧
  ∀ k : ℤ,
    Tendsto (fun n : ℕ =>
      arrivalTime n (suspensionFuturePath (suspensionGapShift k ω))) atTop atTop ∧
    Tendsto (fun n : ℕ =>
      arrivalTime n (suspensionPastPath (suspensionGapShift k ω))) atTop atTop

/-- Good Palm-gap paths stay good after a deterministic change of arrival
label. -/
theorem suspensionGoodGapPath_shift (ω : ℤ → ℝ)
    (hω : suspensionGoodGapPath ω) (k : ℤ) :
    suspensionGoodGapPath (suspensionGapShift k ω) := by
  rcases hω with ⟨hpositive, hdiverge⟩
  constructor
  · intro i
    exact hpositive (i + k)
  · intro j
    rcases hdiverge (j + k) with ⟨hfuture, hpast⟩
    simpa only [suspensionGapShift_comp] using ⟨hfuture, hpast⟩

theorem suspensionGoodGapPath_strictMono (ω : ℤ → ℝ)
    (hω : suspensionGoodGapPath ω) :
    StrictMono (candidatePalmArrival ω) :=
  candidatePalmArrival_strictMono_of_positive ω hω.1

theorem suspensionGoodGapPath_future (ω : ℤ → ℝ)
    (hω : suspensionGoodGapPath ω) :
    Tendsto (fun n : ℕ => arrivalTime n (suspensionFuturePath ω)) atTop atTop := by
  simpa using (hω.2 0).1

theorem suspensionGoodGapPath_past (ω : ℤ → ℝ)
    (hω : suspensionGoodGapPath ω) :
    Tendsto (fun n : ℕ => arrivalTime n (suspensionPastPath ω)) atTop atTop := by
  simpa using (hω.2 0).2

/-- The iid exponential Palm-gap law is supported on the good-path set. -/
theorem ae_suspensionGoodGapPath {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ ω ∂twoSidedInterarrivalMeasure rate, suspensionGoodGapPath ω := by
  filter_upwards [ae_all_twoSidedGap_positive hrate,
    ae_all_suspensionGapShift_nonexplosion hrate] with ω hpositive hdiverge
  exact ⟨hpositive, hdiverge⟩

/-- On every good path, the boundary-correct special flow is a pointwise
real-time action for every phase. -/
theorem suspensionFlow_action_of_suspensionGoodGapPath
    (ω : ℤ → ℝ) (hω : suspensionGoodGapPath ω) (u s t : ℝ) :
    suspensionFlow s (suspensionFlow t (ω, u)) =
      suspensionFlow (s + t) (ω, u) := by
  exact suspensionFlow_action_of_reindex_divergence ω
    (suspensionGoodGapPath_strictMono ω hω)
    (suspensionGoodGapPath_future ω hω) (suspensionGoodGapPath_past ω hω) hω.2 u s t

/-- On a good path, every real-time translate lands back in the half-open
suspension carrier. -/
theorem suspensionFlow_mem_suspensionCarrier_of_suspensionGoodGapPath
    (ω : ℤ → ℝ) (hω : suspensionGoodGapPath ω) (u t : ℝ) :
    suspensionFlow t (ω, u) ∈ suspensionCarrier :=
  suspensionFlow_mem_suspensionCarrier ω (suspensionGoodGapPath_future ω hω)
    (suspensionGoodGapPath_past ω hω) u t

/-- If a carrier point crosses label `k` under a time translation, then the
inverse translation crosses label `-k` on the reindexed path. This is the
pathwise inverse-label fact required for the branch-image partition. -/
theorem suspensionCrossingIndexPastClosed_neg_eq_neg_of_suspensionGoodGapPath_carrier
    (ω : ℤ → ℝ) (hω : suspensionGoodGapPath ω) (u t : ℝ)
    (hu : (ω, u) ∈ suspensionCarrier)
    (k : ℤ) :
    suspensionCrossingIndexPastClosed (-t)
      (suspensionFixedIndexFlow t k (ω, u)) = -k := by
  have hshiftGood := suspensionGoodGapPath_shift ω hω k
  have hfuture_k := suspensionGoodGapPath_future (suspensionGapShift k ω) hshiftGood
  have hpast_k := suspensionGoodGapPath_past (suspensionGapShift k ω) hshiftGood
  have hstrict_k := suspensionGoodGapPath_strictMono (suspensionGapShift k ω) hshiftGood
  let q := suspensionFixedIndexFlow t k (ω, u)
  let l := suspensionCrossingIndexPastClosed (-t) q
  have hlinterval := suspensionCrossingIndexPastClosed_interval
    (suspensionGapShift k ω) hfuture_k hpast_k (u + t - candidatePalmArrival ω k) (-t)
  have hlinterval' :
      candidatePalmArrival (suspensionGapShift k ω) l ≤ u - candidatePalmArrival ω k ∧
        u - candidatePalmArrival ω k <
          candidatePalmArrival (suspensionGapShift k ω) (l + 1) := by
    change candidatePalmArrival (suspensionGapShift k ω)
          (suspensionCrossingIndexPastClosed (-t)
            (suspensionGapShift k ω, u + t - candidatePalmArrival ω k)) ≤
          u - candidatePalmArrival ω k ∧
        u - candidatePalmArrival ω k <
          candidatePalmArrival (suspensionGapShift k ω)
            (suspensionCrossingIndexPastClosed (-t)
              (suspensionGapShift k ω, u + t - candidatePalmArrival ω k) + 1)
    convert hlinterval using 1 <;> ring_nf
  have htargetinterval :
      candidatePalmArrival (suspensionGapShift k ω) (-k) ≤ u - candidatePalmArrival ω k ∧
        u - candidatePalmArrival ω k <
          candidatePalmArrival (suspensionGapShift k ω) ((-k) + 1) := by
    rw [candidatePalmArrival_suspensionGapShift,
      candidatePalmArrival_suspensionGapShift]
    rcases hu with ⟨hu0, hu1⟩
    constructor
    · have hzero : candidatePalmArrival ω 0 = 0 := by simp [candidatePalmArrival]
      rw [show k + -k = 0 by ring, hzero]
      linarith
    · have hindex : k + (-k + 1) = 1 := by ring
      rw [hindex]
      simpa [candidatePalmArrival] using
        (sub_lt_sub_right hu1 (candidatePalmArrival ω k))
  have hlabel : l = -k :=
    candidatePalmArrival_interval_index_unique (suspensionGapShift k ω) hstrict_k
      hlinterval' htargetinterval
  exact hlabel

/-- Under the two-sided exponential Palm-gap law, the special-flow formula
lands in its carrier simultaneously for every starting phase and time. -/
theorem ae_suspensionFlow_mem_suspensionCarrier
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ ω ∂twoSidedInterarrivalMeasure rate, ∀ u t : ℝ,
      suspensionFlow t (ω, u) ∈ suspensionCarrier := by
  filter_upwards [ae_candidateFutureEpoch_succ_tendsto_atTop hrate,
    ae_candidatePastGapSum_succ_tendsto_atTop hrate] with ω hfuture hpast
  have hfuture' :
      Tendsto (fun n : ℕ => arrivalTime n (suspensionFuturePath ω)) atTop atTop := by
    simpa only [← candidateFutureEpoch_succ_eq_arrivalTime_suspension] using hfuture
  have hpast' :
      Tendsto (fun n : ℕ => arrivalTime n (suspensionPastPath ω)) atTop atTop := by
    simpa only [← candidatePastGapSum_succ_eq_arrivalTime_suspension] using hpast
  intro u t
  exact suspensionFlow_mem_suspensionCarrier ω hfuture' hpast' u t

/-- The boundary-correct suspension formula is pointwise the identity at time
zero on the half-open carrier. -/
theorem suspensionFlow_zero_eq_on_carrier
    (p : (ℤ → ℝ) × ℝ) (hp : p ∈ suspensionCarrier) :
    suspensionFlow 0 p = p := by
  rcases p with ⟨ω, u⟩
  rcases hp with ⟨hu_nonneg, hu_roof⟩
  have htime : u < arrivalTime 0 (suspensionFuturePath ω) := by
    simpa [arrivalTime, suspensionFuturePath, interarrival] using hu_roof
  have hcount : canonicalRenewalCount u (suspensionFuturePath ω) = 0 :=
    (canonicalRenewalCount_eq_zero_iff u (suspensionFuturePath ω)).mpr (Or.inl htime)
  have hshift_zero : suspensionGapShift 0 ω = ω := by
    funext i
    simp [suspensionGapShift, twoSidedGap]
  simp [suspensionFlow, suspensionCrossingIndexPastClosed, hu_nonneg, hcount,
    hshift_zero, candidatePalmArrival]

/-- The full-measure good-gap property is measurable, so it can be used as
the carrier predicate of a literal special-flow state space. -/
theorem measurableSet_suspensionGoodGapPath :
    MeasurableSet {ω : ℤ → ℝ | suspensionGoodGapPath ω} := by
  have hpositive : MeasurableSet (⋂ i : ℤ, {ω : ℤ → ℝ | 0 < twoSidedGap i ω}) := by
    exact MeasurableSet.iInter fun i =>
      measurableSet_lt measurable_const (measurable_twoSidedGap i)
  have hfuture (k : ℤ) : MeasurableSet {ω : ℤ → ℝ |
      Tendsto (fun n : ℕ =>
        arrivalTime n (suspensionFuturePath (suspensionGapShift k ω))) atTop atTop} := by
    apply measurableSet_tendsto atTop
    intro n
    exact (measurable_arrivalTime n).comp
      (measurable_suspensionFuturePath.comp (measurable_suspensionGapShift k))
  have hpast (k : ℤ) : MeasurableSet {ω : ℤ → ℝ |
      Tendsto (fun n : ℕ =>
        arrivalTime n (suspensionPastPath (suspensionGapShift k ω))) atTop atTop} := by
    apply measurableSet_tendsto atTop
    intro n
    exact (measurable_arrivalTime n).comp
      (measurable_suspensionPastPath.comp (measurable_suspensionGapShift k))
  have hall : MeasurableSet (⋂ k : ℤ,
      {ω : ℤ → ℝ | Tendsto (fun n : ℕ =>
        arrivalTime n (suspensionFuturePath (suspensionGapShift k ω))) atTop atTop} ∩
      {ω : ℤ → ℝ | Tendsto (fun n : ℕ =>
        arrivalTime n (suspensionPastPath (suspensionGapShift k ω))) atTop atTop}) :=
    MeasurableSet.iInter fun k => (hfuture k).inter (hpast k)
  convert hpositive.inter hall using 1
  ext ω
  simp [suspensionGoodGapPath]

/-- The literal state space of the deterministic special flow: a phase in
the half-open roof above a good two-sided gap path. -/
def GoodSuspensionState :=
  {p : (ℤ → ℝ) × ℝ // p ∈ suspensionCarrier ∧ suspensionGoodGapPath p.1}

instance : MeasurableSpace GoodSuspensionState :=
  inferInstanceAs (MeasurableSpace
    {p : (ℤ → ℝ) × ℝ // p ∈ suspensionCarrier ∧ suspensionGoodGapPath p.1})

theorem measurableSet_goodSuspensionState :
    MeasurableSet {p : (ℤ → ℝ) × ℝ |
      p ∈ suspensionCarrier ∧ suspensionGoodGapPath p.1} :=
  measurableSet_suspensionCarrier.inter
    (measurableSet_suspensionGoodGapPath.preimage measurable_fst)

/-- The normalized raw suspension measure is supported on the good carrier. -/
theorem ae_goodSuspensionState
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ p ∂suspensionMeasure rate,
      p ∈ suspensionCarrier ∧ suspensionGoodGapPath p.1 := by
  have hprod_mem : ∀ᵐ p ∂(twoSidedInterarrivalMeasure rate).prod (volume : Measure ℝ),
      p.1 ∈ {ω : ℤ → ℝ | suspensionGoodGapPath ω} := by
    rw [Measure.ae_prod_iff_ae_ae
      (μ := twoSidedInterarrivalMeasure rate) (ν := (volume : Measure ℝ))
      (measurableSet_suspensionGoodGapPath.preimage measurable_fst)]
    filter_upwards [ae_suspensionGoodGapPath hrate] with ω hω
    exact ae_of_all (volume : Measure ℝ) (fun _ => hω)
  have hprod : ∀ᵐ p ∂(twoSidedInterarrivalMeasure rate).prod (volume : Measure ℝ),
      suspensionGoodGapPath p.1 := by simpa using hprod_mem
  unfold suspensionMeasure
  exact Measure.ae_smul_measure
    ((ae_restrict_mem measurableSet_suspensionCarrier).and (ae_restrict_of_ae hprod)) _

/-- The normalized suspension law, transported to the literal good-state
subtype. -/
def goodSuspensionMeasure (rate : ℝ) : Measure GoodSuspensionState :=
  Measure.comap Subtype.val (suspensionMeasure rate)

theorem goodSuspensionMeasure_apply
    (rate : ℝ) (t : Set GoodSuspensionState) (ht : MeasurableSet t) :
    goodSuspensionMeasure rate t =
      suspensionMeasure rate
        ((Subtype.val : GoodSuspensionState → ((ℤ → ℝ) × ℝ)) '' t) := by
  unfold goodSuspensionMeasure
  apply Measure.comap_apply
  · exact Subtype.val_injective
  · intro s hs
    exact (MeasurableEmbedding.subtype_coe
      measurableSet_goodSuspensionState).measurableSet_image' hs
  · exact ht

theorem goodSuspensionMeasure_univ
    {rate : ℝ} (hrate : 0 < rate) :
    goodSuspensionMeasure rate Set.univ = 1 := by
  rw [goodSuspensionMeasure_apply rate Set.univ MeasurableSet.univ]
  have himage :
      (Subtype.val : GoodSuspensionState → ((ℤ → ℝ) × ℝ)) '' Set.univ =
        {p : (ℤ → ℝ) × ℝ | p ∈ suspensionCarrier ∧ suspensionGoodGapPath p.1} := by
    ext p
    simp
  change suspensionMeasure rate
    ((Subtype.val : GoodSuspensionState → ((ℤ → ℝ) × ℝ)) '' Set.univ) = 1
  rw [himage]
  have hrestrict : (suspensionMeasure rate).restrict
      {p : (ℤ → ℝ) × ℝ | p ∈ suspensionCarrier ∧ suspensionGoodGapPath p.1} =
      suspensionMeasure rate :=
    Measure.restrict_eq_self_of_ae_mem (ae_goodSuspensionState hrate)
  calc
    suspensionMeasure rate {p : (ℤ → ℝ) × ℝ |
        p ∈ suspensionCarrier ∧ suspensionGoodGapPath p.1} =
        ((suspensionMeasure rate).restrict
          {p : (ℤ → ℝ) × ℝ | p ∈ suspensionCarrier ∧ suspensionGoodGapPath p.1}) Set.univ := by
          rw [Measure.restrict_apply_univ]
    _ = suspensionMeasure rate Set.univ := by rw [hrestrict]
    _ = 1 := suspensionMeasure_univ hrate

theorem isProbabilityMeasure_goodSuspensionMeasure
    {rate : ℝ} (hrate : 0 < rate) :
    IsProbabilityMeasure (goodSuspensionMeasure rate) :=
  ⟨goodSuspensionMeasure_univ hrate⟩

/-- The special-flow formula restricted to the deterministic good carrier. -/
def goodSuspensionFlow (t : ℝ) : GoodSuspensionState → GoodSuspensionState :=
  fun p =>
    ⟨suspensionFlow t p.1,
      ⟨suspensionFlow_mem_suspensionCarrier_of_suspensionGoodGapPath p.1.1 p.2.2 p.1.2 t,
       suspensionGoodGapPath_shift p.1.1 p.2.2
         (suspensionCrossingIndexPastClosed t p.1)⟩⟩

theorem goodSuspensionFlow_zero : goodSuspensionFlow 0 = id := by
  funext p
  apply Subtype.ext
  exact suspensionFlow_zero_eq_on_carrier p.1 p.2.1

theorem goodSuspensionFlow_add (s t : ℝ) :
    goodSuspensionFlow (s + t) = goodSuspensionFlow s ∘ goodSuspensionFlow t := by
  funext p
  apply Subtype.ext
  change suspensionFlow (s + t) p.1 = suspensionFlow s (suspensionFlow t p.1)
  exact (suspensionFlow_action_of_suspensionGoodGapPath p.1.1 p.2.2 p.1.2 s t).symm

theorem measurable_goodSuspensionFlow (t : ℝ) : Measurable (goodSuspensionFlow t) := by
  apply Measurable.subtype_mk
  exact (measurable_suspensionFlow t).comp measurable_subtype_coe

/-- Any raw special-flow invariance theorem transfers directly to the literal
good-state subtype. -/
theorem goodSuspensionFlow_measurePreserving_of_raw
    {rate : ℝ} (hrate : 0 < rate) (t : ℝ)
    (hraw : MeasurePreserving (suspensionFlow t)
      (suspensionMeasure rate) (suspensionMeasure rate)) :
    MeasurePreserving (goodSuspensionFlow t)
      (goodSuspensionMeasure rate) (goodSuspensionMeasure rate) := by
  let I : GoodSuspensionState → ((ℤ → ℝ) × ℝ) := Subtype.val
  have hI : MeasurableEmbedding I :=
    MeasurableEmbedding.subtype_coe measurableSet_goodSuspensionState
  have hmapI : Measure.map I (goodSuspensionMeasure rate) = suspensionMeasure rate := by
    change Measure.map I (Measure.comap I (suspensionMeasure rate)) = suspensionMeasure rate
    rw [hI.map_comap]
    apply Measure.restrict_eq_self_of_ae_mem
    filter_upwards [ae_goodSuspensionState hrate] with p hp
    exact ⟨⟨p, hp⟩, rfl⟩
  refine ⟨measurable_goodSuspensionFlow t, ?_⟩
  apply hI.map_injective
  calc
    Measure.map I (Measure.map (goodSuspensionFlow t) (goodSuspensionMeasure rate)) =
        Measure.map (I ∘ goodSuspensionFlow t) (goodSuspensionMeasure rate) :=
      Measure.map_map hI.measurable (measurable_goodSuspensionFlow t)
    _ = Measure.map (suspensionFlow t ∘ I) (goodSuspensionMeasure rate) := by
      rfl
    _ = Measure.map (suspensionFlow t)
        (Measure.map I (goodSuspensionMeasure rate)) :=
      (Measure.map_map (measurable_suspensionFlow t) hI.measurable).symm
    _ = Measure.map (suspensionFlow t) (suspensionMeasure rate) := by rw [hmapI]
    _ = suspensionMeasure rate := hraw.map_eq
    _ = Measure.map I (goodSuspensionMeasure rate) := hmapI.symm

/-- The full-measure carrier in the raw Palm-gaps-times-phase space. The
following branch-image identities are the deterministic core of the
real-time invariance argument. -/
def rawGoodCarrier : Set ((ℤ → ℝ) × ℝ) :=
  {p | p ∈ suspensionCarrier ∧ suspensionGoodGapPath p.1}

theorem measurableSet_rawGoodCarrier : MeasurableSet rawGoodCarrier :=
  measurableSet_suspensionCarrier.inter
    (measurableSet_suspensionGoodGapPath.preimage measurable_fst)

def rawGoodCarrierSlab (t : ℝ) (k : ℤ) : Set ((ℤ → ℝ) × ℝ) :=
  rawGoodCarrier ∩ suspensionCrossingSlab t k

theorem measurableSet_rawGoodCarrierSlab (t : ℝ) (k : ℤ) :
    MeasurableSet (rawGoodCarrierSlab t k) :=
  measurableSet_rawGoodCarrier.inter (measurableSet_suspensionCrossingSlab t k)

theorem suspensionFixedIndexFlow_mem_rawGoodCarrier_of_crossing
    (p : (ℤ → ℝ) × ℝ) (t : ℝ) (k : ℤ)
    (hp : p ∈ rawGoodCarrier)
    (hk : suspensionCrossingIndexPastClosed t p = k) :
    suspensionFixedIndexFlow t k p ∈ rawGoodCarrier := by
  rcases p with ⟨ω, u⟩
  rcases hp with ⟨hcarrier, hgood⟩
  constructor
  · rw [← suspensionFlow_eq_suspensionFixedIndexFlow_of_crossing t k (ω, u) hk]
    exact suspensionFlow_mem_suspensionCarrier_of_suspensionGoodGapPath ω hgood u t
  · change suspensionGoodGapPath (suspensionGapShift k ω)
    exact suspensionGoodGapPath_shift ω hgood k

/-- A deterministic branch carries each good crossing slab exactly to the
opposite-label good slab for the inverse time. -/
theorem rawGoodCarrier_image_eq_inverse_slab (t : ℝ) (k : ℤ) :
    suspensionFixedIndexFlow t k '' rawGoodCarrierSlab t k =
      rawGoodCarrierSlab (-t) (-k) := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases p with ⟨ω, u⟩
    constructor
    · exact suspensionFixedIndexFlow_mem_rawGoodCarrier_of_crossing (ω, u) t k hp.1 hp.2
    · simpa using
        (suspensionCrossingIndexPastClosed_neg_eq_neg_of_suspensionGoodGapPath_carrier
          ω hp.1.2 u t hp.1.1 k)
  · intro hx
    let p := suspensionFixedIndexFlow (-t) (-k) x
    have hp_good : p ∈ rawGoodCarrier := by
      rcases x with ⟨ω, u⟩
      exact suspensionFixedIndexFlow_mem_rawGoodCarrier_of_crossing (ω, u) (-t) (-k)
        hx.1 hx.2
    have hp_cross : suspensionCrossingIndexPastClosed t p = k := by
      rcases x with ⟨ω, u⟩
      simpa [p] using
        (suspensionCrossingIndexPastClosed_neg_eq_neg_of_suspensionGoodGapPath_carrier
          ω hx.1.2 u (-t) hx.1.1 (-k))
    refine ⟨p, ⟨hp_good, hp_cross⟩, ?_⟩
    exact suspensionFixedIndexFlow_comp_neg t k x

theorem rawGoodCarrier_eq_iUnion_slabs (t : ℝ) :
    rawGoodCarrier = ⋃ k : ℤ, rawGoodCarrierSlab t k := by
  ext p
  constructor
  · intro hp
    exact Set.mem_iUnion.2 ⟨suspensionCrossingIndexPastClosed t p, hp, rfl⟩
  · intro hp
    rcases Set.mem_iUnion.1 hp with ⟨k, hpk⟩
    exact hpk.1

theorem pairwiseDisjoint_rawGoodCarrierSlab (t : ℝ) :
    Pairwise (Function.onFun Disjoint (rawGoodCarrierSlab t)) := by
  intro i j hij
  apply Set.disjoint_left.2
  intro p hpi hpj
  apply hij
  exact hpi.2.symm.trans hpj.2

theorem rawGoodCarrier_image_iUnion_eq (t : ℝ) :
    ⋃ k : ℤ, suspensionFixedIndexFlow t k '' rawGoodCarrierSlab t k =
      rawGoodCarrier := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨k, hx⟩
    rw [rawGoodCarrier_image_eq_inverse_slab] at hx
    rw [rawGoodCarrier_eq_iUnion_slabs (-t)]
    exact Set.mem_iUnion.2 ⟨-k, hx⟩
  · intro hx
    rw [rawGoodCarrier_eq_iUnion_slabs (-t)] at hx
    rcases Set.mem_iUnion.1 hx with ⟨j, hx⟩
    refine Set.mem_iUnion.2 ⟨-j, ?_⟩
    rw [rawGoodCarrier_image_eq_inverse_slab]
    simpa using hx

theorem pairwiseDisjoint_rawGoodCarrier_images (t : ℝ) :
    Pairwise (Function.onFun Disjoint
      (fun k : ℤ => suspensionFixedIndexFlow t k '' rawGoodCarrierSlab t k)) := by
  intro i j hij
  change Disjoint (suspensionFixedIndexFlow t i '' rawGoodCarrierSlab t i)
    (suspensionFixedIndexFlow t j '' rawGoodCarrierSlab t j)
  rw [rawGoodCarrier_image_eq_inverse_slab, rawGoodCarrier_image_eq_inverse_slab]
  apply pairwiseDisjoint_rawGoodCarrierSlab (-t)
  intro h
  apply hij
  linarith

/-- The good carrier agrees almost everywhere with the full roof carrier
under the unnormalized Palm-gaps-times-Lebesgue measure. -/
theorem rawGoodCarrier_ae_eq_suspensionCarrier
    {rate : ℝ} (hrate : 0 < rate) :
    rawGoodCarrier =ᶠ[ae ((twoSidedInterarrivalMeasure rate).prod volume)]
      suspensionCarrier := by
  have hgood : ∀ᵐ p : (ℤ → ℝ) × ℝ ∂
      (twoSidedInterarrivalMeasure rate).prod volume,
      suspensionGoodGapPath p.1 :=
    (Measure.quasiMeasurePreserving_fst
      (μ := twoSidedInterarrivalMeasure rate) (ν := volume)).ae
        (ae_suspensionGoodGapPath hrate)
  filter_upwards [hgood] with p hp
  apply propext
  change (p ∈ suspensionCarrier ∧ suspensionGoodGapPath p.1) ↔ p ∈ suspensionCarrier
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, hp⟩

/-- The raw carrier split by the measurable crossing label. It agrees almost
everywhere with its good-path refinement. -/
def rawCarrierSlab (t : ℝ) (k : ℤ) : Set ((ℤ → ℝ) × ℝ) :=
  suspensionCarrier ∩ suspensionCrossingSlab t k

theorem measurableSet_rawCarrierSlab (t : ℝ) (k : ℤ) :
    MeasurableSet (rawCarrierSlab t k) :=
  measurableSet_suspensionCarrier.inter (measurableSet_suspensionCrossingSlab t k)

theorem rawGoodCarrierSlab_ae_eq_rawCarrierSlab
    {rate : ℝ} (hrate : 0 < rate) (t : ℝ) (k : ℤ) :
    rawGoodCarrierSlab t k =ᶠ[ae ((twoSidedInterarrivalMeasure rate).prod volume)]
      rawCarrierSlab t k := by
  filter_upwards [rawGoodCarrier_ae_eq_suspensionCarrier hrate] with p hp
  apply propext
  change (rawGoodCarrier p ∧ suspensionCrossingSlab t k p) ↔
    (suspensionCarrier p ∧ suspensionCrossingSlab t k p)
  rw [hp]

theorem nullMeasurableSet_rawGoodCarrierSlab
    {rate : ℝ} (hrate : 0 < rate) (t : ℝ) (k : ℤ) :
    NullMeasurableSet (rawGoodCarrierSlab t k)
      ((twoSidedInterarrivalMeasure rate).prod volume) := by
  exact (measurableSet_rawCarrierSlab t k).nullMeasurableSet.congr
    (rawGoodCarrierSlab_ae_eq_rawCarrierSlab hrate t k).symm

theorem nullMeasurableSet_rawGoodCarrier_image
    {rate : ℝ} (hrate : 0 < rate) (t : ℝ) (k : ℤ) :
    NullMeasurableSet
      (suspensionFixedIndexFlow t k '' rawGoodCarrierSlab t k)
      ((twoSidedInterarrivalMeasure rate).prod volume) := by
  rw [rawGoodCarrier_image_eq_inverse_slab]
  exact nullMeasurableSet_rawGoodCarrierSlab hrate (-t) (-k)

theorem restrict_rawGoodCarrier_eq_sum_rawGoodCarrierSlab
    {rate : ℝ} (hrate : 0 < rate) (t : ℝ) :
    ((twoSidedInterarrivalMeasure rate).prod volume).restrict rawGoodCarrier =
      Measure.sum fun k : ℤ =>
        ((twoSidedInterarrivalMeasure rate).prod volume).restrict
          (rawGoodCarrierSlab t k) := by
  rw [rawGoodCarrier_eq_iUnion_slabs]
  exact Measure.restrict_iUnion_ae
    (fun i j hij => (pairwiseDisjoint_rawGoodCarrierSlab t hij).aedisjoint)
    (nullMeasurableSet_rawGoodCarrierSlab hrate t)

theorem suspensionFlow_restrict_rawGoodCarrierSlab_measurePreserving
    {rate : ℝ} (hrate : 0 < rate) (t : ℝ) (k : ℤ) :
    MeasurePreserving (suspensionFlow t)
      (((twoSidedInterarrivalMeasure rate).prod volume).restrict
        (rawGoodCarrierSlab t k))
      (((twoSidedInterarrivalMeasure rate).prod volume).restrict
        (suspensionFixedIndexFlow t k '' rawGoodCarrierSlab t k)) := by
  refine ((suspensionFixedIndexFlow_measurePreserving hrate t k).restrict_image_emb
    (suspensionFixedIndexFlowEquiv t k).measurableEmbedding
      (rawGoodCarrierSlab t k)).congr (measurable_suspensionFlow t) ?_
  filter_upwards [ae_restrict_mem₀
    (nullMeasurableSet_rawGoodCarrierSlab hrate t k)] with p hp
  exact (suspensionFlow_eq_suspensionFixedIndexFlow_of_crossing t k p hp.2).symm

/-- The special-flow map preserves the unnormalized Palm-gap-times-Lebesgue
measure restricted to the good roof carrier. -/
theorem suspensionFlow_measurePreserving_rawGoodCarrier
    {rate : ℝ} (hrate : 0 < rate) (t : ℝ) :
    MeasurePreserving (suspensionFlow t)
      (((twoSidedInterarrivalMeasure rate).prod volume).restrict rawGoodCarrier)
      (((twoSidedInterarrivalMeasure rate).prod volume).restrict rawGoodCarrier) := by
  refine ⟨measurable_suspensionFlow t, ?_⟩
  calc
    Measure.map (suspensionFlow t)
        (((twoSidedInterarrivalMeasure rate).prod volume).restrict rawGoodCarrier) =
      Measure.map (suspensionFlow t)
        (Measure.sum fun k : ℤ =>
          ((twoSidedInterarrivalMeasure rate).prod volume).restrict
            (rawGoodCarrierSlab t k)) := by
        rw [restrict_rawGoodCarrier_eq_sum_rawGoodCarrierSlab hrate t]
    _ = Measure.sum fun k : ℤ =>
        Measure.map (suspensionFlow t)
          (((twoSidedInterarrivalMeasure rate).prod volume).restrict
            (rawGoodCarrierSlab t k)) :=
        Measure.map_sum (measurable_suspensionFlow t).aemeasurable
    _ = Measure.sum fun k : ℤ =>
        ((twoSidedInterarrivalMeasure rate).prod volume).restrict
          (suspensionFixedIndexFlow t k '' rawGoodCarrierSlab t k) := by
        simp_rw [fun k =>
          (suspensionFlow_restrict_rawGoodCarrierSlab_measurePreserving
            hrate t k).map_eq]
    _ = ((twoSidedInterarrivalMeasure rate).prod volume).restrict
        (⋃ k : ℤ, suspensionFixedIndexFlow t k '' rawGoodCarrierSlab t k) :=
      (Measure.restrict_iUnion_ae
        (fun i j hij => (pairwiseDisjoint_rawGoodCarrier_images t hij).aedisjoint)
        (nullMeasurableSet_rawGoodCarrier_image hrate t)).symm
    _ = ((twoSidedInterarrivalMeasure rate).prod volume).restrict rawGoodCarrier := by
      rw [rawGoodCarrier_image_iUnion_eq]

/-- The real-time special flow preserves the full unnormalized roof measure. -/
theorem suspensionFlow_measurePreserving_suspensionCarrier
    {rate : ℝ} (hrate : 0 < rate) (t : ℝ) :
    MeasurePreserving (suspensionFlow t)
      (((twoSidedInterarrivalMeasure rate).prod volume).restrict suspensionCarrier)
      (((twoSidedInterarrivalMeasure rate).prod volume).restrict suspensionCarrier) := by
  refine ⟨measurable_suspensionFlow t, ?_⟩
  have hrestrict :
      ((twoSidedInterarrivalMeasure rate).prod volume).restrict rawGoodCarrier =
        ((twoSidedInterarrivalMeasure rate).prod volume).restrict suspensionCarrier :=
    Measure.restrict_congr_set (rawGoodCarrier_ae_eq_suspensionCarrier hrate)
  calc
    Measure.map (suspensionFlow t)
        (((twoSidedInterarrivalMeasure rate).prod volume).restrict suspensionCarrier) =
      Measure.map (suspensionFlow t)
        (((twoSidedInterarrivalMeasure rate).prod volume).restrict rawGoodCarrier) := by
        rw [hrestrict]
    _ = ((twoSidedInterarrivalMeasure rate).prod volume).restrict rawGoodCarrier :=
      (suspensionFlow_measurePreserving_rawGoodCarrier hrate t).map_eq
    _ = ((twoSidedInterarrivalMeasure rate).prod volume).restrict suspensionCarrier := hrestrict

/-- The normalized special-flow law is invariant under every real-time
translation. -/
theorem suspensionFlow_measurePreserving_suspensionMeasure
    {rate : ℝ} (hrate : 0 < rate) (t : ℝ) :
    MeasurePreserving (suspensionFlow t) (suspensionMeasure rate) (suspensionMeasure rate) := by
  refine ⟨measurable_suspensionFlow t, ?_⟩
  unfold suspensionMeasure
  rw [Measure.map_smul,
    (suspensionFlow_measurePreserving_suspensionCarrier hrate t).map_eq]

end

end AppliedModelingLib.Probability.PoissonProcess
