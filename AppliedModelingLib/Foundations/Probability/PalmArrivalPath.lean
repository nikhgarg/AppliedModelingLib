import AppliedModelingLib.Foundations.Probability.PoissonStopping
import AppliedModelingLib.Foundations.Probability.Processes.Palm.Core
import Mathlib.Probability.Independence.InfinitePi

/-!
# Candidate two-sided Palm-tagged arrival path

This module constructs only a two-sided iid-exponential interarrival
product path, with a distinguished arrival at time zero.  It is not a
construction of a Palm measure or a proof of stationary Poisson increments.
-/

namespace AppliedModelingLib
namespace Probability
namespace PoissonProcess

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-- Product law for iid two-sided exponential gaps. -/
def twoSidedInterarrivalMeasure (rate : ℝ) : Measure (ℤ → ℝ) :=
  Measure.infinitePi (fun _ : ℤ => ProbabilityTheory.expMeasure rate)

theorem isProbabilityMeasure_twoSidedInterarrivalMeasure
    {rate : ℝ} (hrate : 0 < rate) :
    IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) := by
  letI : ∀ i : ℤ, IsProbabilityMeasure (ProbabilityTheory.expMeasure rate) :=
    fun _ => ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  simpa [twoSidedInterarrivalMeasure] using
    (inferInstance :
      IsProbabilityMeasure
        (Measure.infinitePi (fun _ : ℤ => ProbabilityTheory.expMeasure rate)))

/-- Coordinate gap on a candidate two-sided tagged path. -/
def twoSidedGap (i : ℤ) : (ℤ → ℝ) → ℝ := fun ω => ω i

theorem measurable_twoSidedGap (i : ℤ) : Measurable (twoSidedGap i) := by
  simpa [twoSidedGap] using
    (measurable_pi_apply i : Measurable (fun ω : ℤ → ℝ => ω i))

theorem twoSidedGap_hasLaw
    {rate : ℝ} (hrate : 0 < rate) (i : ℤ) :
    ProbabilityTheory.HasLaw (twoSidedGap i)
      (ProbabilityTheory.expMeasure rate) (twoSidedInterarrivalMeasure rate) := by
  exact (@measurePreserving_eval_infinitePi ℤ (fun _ : ℤ => ℝ)
    (fun _ => inferInstance)
    (fun _ : ℤ => ProbabilityTheory.expMeasure rate)
    (fun _ => ProbabilityTheory.isProbabilityMeasure_expMeasure hrate) i).hasLaw

theorem iIndepFun_twoSidedGap
    {rate : ℝ} (hrate : 0 < rate) :
    ProbabilityTheory.iIndepFun twoSidedGap (twoSidedInterarrivalMeasure rate) := by
  simpa [twoSidedGap] using
    (@ProbabilityTheory.iIndepFun_infinitePi ℤ (fun _ : ℤ => ℝ)
      (fun _ => inferInstance) (fun _ : ℤ => ℝ) (fun _ => inferInstance)
      (fun _ : ℤ => ProbabilityTheory.expMeasure rate)
      (fun _ => ProbabilityTheory.isProbabilityMeasure_expMeasure hrate)
      (fun _ : ℤ => id) (fun _ => measurable_id))

theorem ae_all_twoSidedGap_positive
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ ω ∂twoSidedInterarrivalMeasure rate, ∀ i : ℤ, 0 < twoSidedGap i ω := by
  rw [ae_all_iff]
  intro i
  have hp : Measurable (fun x : ℝ => 0 < x) := by fun_prop
  let M : Exponential.Model := Exponential.Model.mk rate hrate
  exact ((twoSidedGap_hasLaw hrate i).ae_iff hp).2 (by
    rw [MeasureTheory.ae_iff]
    simpa [Set.compl_setOf, M] using M.measure_Iic_zero)

/--
Candidate two-sided arrival epochs, indexed so that the tag has index `0` and
epoch `0`.  Positive indices sum future gaps; negative indices sum past gaps
with a negative sign.  This is not yet a Palm/Campbell construction.
-/
def candidatePalmArrival (ω : ℤ → ℝ) : ℤ → ℝ
  | Int.ofNat n => ∑ i ∈ Finset.range n, twoSidedGap (Int.ofNat i) ω
  | Int.negSucc n => -∑ i ∈ Finset.range (n + 1), twoSidedGap (Int.negSucc i) ω

/-- One-step telescoping for the two-sided candidate arrival path. -/
theorem candidatePalmArrival_add_one (g : ℤ → ℝ) (j : ℤ) :
    candidatePalmArrival g (j + 1) = candidatePalmArrival g j + g j := by
  cases j with
  | ofNat n =>
      have h : Int.ofNat n + 1 = Int.ofNat (n + 1) := by
        simpa [Int.ofNat_eq_natCast] using Int.ofNat_add_one_out n
      rw [h]
      simp [candidatePalmArrival, twoSidedGap, Finset.sum_range_succ]
  | negSucc n =>
      cases n with
      | zero =>
          have h : Int.negSucc 0 + 1 = 0 := by norm_num [Int.negSucc_eq]
          rw [h]
          norm_num [candidatePalmArrival, twoSidedGap, Int.negSucc_eq]
      | succ n =>
          rw [show Int.negSucc (n + 1) + 1 = Int.negSucc n by
            simp only [Int.negSucc_eq]
            omega]
          simp [candidatePalmArrival, twoSidedGap, Finset.sum_range_succ]

/-- Reindexing a two-sided gap sequence and recentering its arrival path
agree pathwise. -/
theorem candidatePalmArrival_recenter (g : ℤ → ℝ) (i j : ℤ) :
    candidatePalmArrival (fun k => g (k + i)) j =
      candidatePalmArrival g (i + j) - candidatePalmArrival g i := by
  induction j using Int.induction_on with
  | zero => simp [candidatePalmArrival]
  | succ n ih =>
      have hindex : i + (Int.ofNat n + 1) = (i + Int.ofNat n) + 1 := by ring
      have ih' : candidatePalmArrival (fun k => g (k + i)) (Int.ofNat n) =
          candidatePalmArrival g (i + Int.ofNat n) - candidatePalmArrival g i := by
        simpa [Int.ofNat_eq_natCast] using ih
      calc
        candidatePalmArrival (fun k => g (k + i)) (Int.ofNat n + 1) =
            candidatePalmArrival (fun k => g (k + i)) (Int.ofNat n) +
              g (Int.ofNat n + i) :=
          candidatePalmArrival_add_one _ _
        _ = (candidatePalmArrival g (i + Int.ofNat n) - candidatePalmArrival g i) +
              g (i + Int.ofNat n) := by
          rw [ih']
          congr 1
          exact congrArg g (add_comm _ _)
        _ = candidatePalmArrival g (i + (Int.ofNat n + 1)) - candidatePalmArrival g i := by
          rw [hindex, candidatePalmArrival_add_one]
          ring
  | pred n ih =>
      let k : ℤ := -Int.ofNat n - 1
      have hk : k + 1 = -Int.ofNat n := by
        dsimp [k]
        ring
      have hL := candidatePalmArrival_add_one (fun q => g (q + i)) k
      have hR := candidatePalmArrival_add_one g (i + k)
      change candidatePalmArrival (fun q => g (q + i)) k =
        candidatePalmArrival g (i + k) - candidatePalmArrival g i
      rw [hk] at hL
      have ih' : candidatePalmArrival (fun q => g (q + i)) (-Int.ofNat n) =
          candidatePalmArrival g (i + -Int.ofNat n) - candidatePalmArrival g i := by
        simpa [Int.ofNat_eq_natCast] using ih
      rw [ih'] at hL
      have harg : k + i = i + k := by ring
      rw [harg] at hL
      have hRarg : i + k + 1 = i + (-Int.ofNat n) := by
        dsimp [k]
        ring
      rw [hRarg] at hR
      linarith

/-- Future finite partial sums from the tagged epoch. -/
def candidateFutureEpoch (ω : ℤ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, twoSidedGap (Int.ofNat i) ω

/-- Magnitudes of finite past partial sums from the tagged epoch. -/
def candidatePastGapSum (ω : ℤ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, twoSidedGap (Int.negSucc i) ω

theorem candidatePalmArrival_ofNat (ω : ℤ → ℝ) (n : ℕ) :
    candidatePalmArrival ω (Int.ofNat n) = candidateFutureEpoch ω n :=
  rfl

theorem candidatePalmArrival_negSucc (ω : ℤ → ℝ) (n : ℕ) :
    candidatePalmArrival ω (Int.negSucc n) = -candidatePastGapSum ω (n + 1) :=
  rfl

theorem candidateFutureEpoch_mono_of_nonnegative
    (ω : ℤ → ℝ) (hω : ∀ i : ℤ, 0 ≤ twoSidedGap i ω) :
    Monotone (candidateFutureEpoch ω) := by
  intro n m hnm
  unfold candidateFutureEpoch
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · exact Finset.range_subset_range.mpr hnm
  · intro i _hi _hnot
    exact hω (Int.ofNat i)

theorem candidateFutureEpoch_strictMono_of_positive
    (ω : ℤ → ℝ) (hω : ∀ i : ℤ, 0 < twoSidedGap i ω) :
    StrictMono (candidateFutureEpoch ω) := by
  intro n m hnm
  have hmono : Monotone (candidateFutureEpoch ω) :=
    candidateFutureEpoch_mono_of_nonnegative ω (fun i => (hω i).le)
  calc
    candidateFutureEpoch ω n <
        candidateFutureEpoch ω n + twoSidedGap (Int.ofNat n) ω :=
      lt_add_of_pos_right _ (hω (Int.ofNat n))
    _ = candidateFutureEpoch ω (n + 1) := by
      simp [candidateFutureEpoch, Finset.sum_range_succ]
    _ ≤ candidateFutureEpoch ω m := hmono (Nat.succ_le_iff.mpr hnm)

theorem candidatePastGapSum_mono_of_nonnegative
    (ω : ℤ → ℝ) (hω : ∀ i : ℤ, 0 ≤ twoSidedGap i ω) :
    Monotone (candidatePastGapSum ω) := by
  intro n m hnm
  unfold candidatePastGapSum
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · exact Finset.range_subset_range.mpr hnm
  · intro i _hi _hnot
    exact hω (Int.negSucc i)

theorem candidatePastGapSum_strictMono_of_positive
    (ω : ℤ → ℝ) (hω : ∀ i : ℤ, 0 < twoSidedGap i ω) :
    StrictMono (candidatePastGapSum ω) := by
  intro n m hnm
  have hmono : Monotone (candidatePastGapSum ω) :=
    candidatePastGapSum_mono_of_nonnegative ω (fun i => (hω i).le)
  calc
    candidatePastGapSum ω n <
        candidatePastGapSum ω n + twoSidedGap (Int.negSucc n) ω :=
      lt_add_of_pos_right _ (hω (Int.negSucc n))
    _ = candidatePastGapSum ω (n + 1) := by
      simp [candidatePastGapSum, Finset.sum_range_succ]
    _ ≤ candidatePastGapSum ω m := hmono (Nat.succ_le_iff.mpr hnm)

theorem candidateFutureEpoch_nonnegative_of_nonnegative
    (ω : ℤ → ℝ) (hω : ∀ i : ℤ, 0 ≤ twoSidedGap i ω) (n : ℕ) :
    0 ≤ candidateFutureEpoch ω n := by
  unfold candidateFutureEpoch
  exact Finset.sum_nonneg fun i _ => hω (Int.ofNat i)

theorem candidatePastGapSum_positive_succ_of_positive
    (ω : ℤ → ℝ) (hω : ∀ i : ℤ, 0 < twoSidedGap i ω) (n : ℕ) :
    0 < candidatePastGapSum ω (n + 1) := by
  have hmono : Monotone (candidatePastGapSum ω) :=
    candidatePastGapSum_mono_of_nonnegative ω (fun i => (hω i).le)
  calc
    0 < twoSidedGap (Int.negSucc 0) ω := hω (Int.negSucc 0)
    _ = candidatePastGapSum ω 1 := by
      simp [candidatePastGapSum]
    _ ≤ candidatePastGapSum ω (n + 1) :=
      hmono (Nat.succ_le_succ (Nat.zero_le n))

/--
Strict ordering of the candidate two-sided tagged arrival path under strictly
positive gaps.  This is a pathwise statement only: it does not establish a
Palm/Campbell relation to an untagged stationary point process.
-/
theorem candidatePalmArrival_strictMono_of_positive
    (ω : ℤ → ℝ) (hω : ∀ i : ℤ, 0 < twoSidedGap i ω) :
    StrictMono (candidatePalmArrival ω) := by
  intro x y hxy
  cases x with
  | ofNat n =>
      cases y with
      | ofNat m =>
          rw [candidatePalmArrival_ofNat, candidatePalmArrival_ofNat]
          apply candidateFutureEpoch_strictMono_of_positive ω hω
          rw [Int.ofNat_eq_natCast, Int.ofNat_eq_natCast] at hxy
          omega
      | negSucc m =>
          exfalso
          rw [Int.ofNat_eq_natCast, Int.negSucc_eq] at hxy
          omega
  | negSucc n =>
      cases y with
      | ofNat m =>
          rw [candidatePalmArrival_negSucc, candidatePalmArrival_ofNat]
          exact lt_of_lt_of_le
            (neg_lt_zero.mpr
              (candidatePastGapSum_positive_succ_of_positive ω hω n))
            (candidateFutureEpoch_nonnegative_of_nonnegative ω
              (fun i => (hω i).le) m)
      | negSucc m =>
          rw [candidatePalmArrival_negSucc, candidatePalmArrival_negSucc]
          apply neg_lt_neg
          apply candidatePastGapSum_strictMono_of_positive ω hω
          have hmn : m < n := by
            rw [Int.negSucc_eq, Int.negSucc_eq] at hxy
            omega
          omega

theorem candidatePalmArrival_zero (ω : ℤ → ℝ) : candidatePalmArrival ω 0 = 0 := by
  simp [candidatePalmArrival]

/-- The candidate tagged arrival is at time zero, pointwise (hence almost surely). -/
theorem ae_candidatePalmArrival_tag_at_zero {rate : ℝ} :
    ∀ᵐ ω ∂twoSidedInterarrivalMeasure rate, candidatePalmArrival ω 0 = 0 :=
  Filter.Eventually.of_forall candidatePalmArrival_zero

/-- Positive iid gaps make the candidate two-sided epochs strictly ordered a.s. -/
theorem ae_candidatePalmArrival_strictMono
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ ω ∂twoSidedInterarrivalMeasure rate,
      StrictMono (candidatePalmArrival ω) :=
  (ae_all_twoSidedGap_positive hrate).mono
    (fun ω hω => candidatePalmArrival_strictMono_of_positive ω hω)

/--
Package the concrete two-sided exponential-gap path as a tagged arrival at
zero.  This constructs the path-level portion of the tagged-arrival interface
only; it does not establish a Campbell/Palm relation to a stationary untagged
point-process law.
-/
noncomputable def candidateTaggedArrivalAtZero
    (rate : ℝ) (hrate : 0 < rate) :
    AppliedModelingLib.Probability.Queueing.TaggedArrivalAtZero (ℤ → ℝ) where
  Ptag := twoSidedInterarrivalMeasure rate
  isProbability := isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  arrivals := candidatePalmArrival
  tag_at_zero := ae_candidatePalmArrival_tag_at_zero
  arrivals_strict := ae_candidatePalmArrival_strictMono hrate

end
end PoissonProcess
end Probability
end AppliedModelingLib
