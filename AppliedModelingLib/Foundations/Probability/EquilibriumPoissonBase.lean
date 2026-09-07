import AppliedModelingLib.Foundations.Probability.PalmArrivalPath
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalRenewalCountMarginal
import AppliedModelingLib.Foundations.Probability.PalmCampbell
import AppliedModelingLib.Foundations.Probability.PoissonMoments

/-!
# Origin-split equilibrium Poisson base

This module constructs the correct untagged equilibrium configuration seen at
a deterministic origin: independent exponential backward age and forward
residual clocks, followed by independent exponential gaps on both sides.  The
gap straddling zero is consequently Gamma/Erlang shape two, unlike the iid
Palm gaps of a configuration pinned at an arrival.

It establishes the real probability-space scaffolding and fixed-origin count
laws, but deliberately does not yet define the measurable real-time
suspension flow or prove a Campbell/Palm identity.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

/-- The forward and backward renewal half-paths of an equilibrium two-sided
Poisson configuration. Coordinate zero of the halves is respectively the
residual time and age at the deterministic origin. -/
def equilibriumTwoSidedBaseMeasure (rate : ℝ) : Measure ((ℕ → ℝ) × (ℕ → ℝ)) :=
  (exponentialInterarrivalMeasure rate).prod (exponentialInterarrivalMeasure rate)

theorem isProbabilityMeasure_equilibriumTwoSidedBaseMeasure
    {rate : ℝ} (hrate : 0 < rate) :
    IsProbabilityMeasure (equilibriumTwoSidedBaseMeasure rate) := by
  unfold equilibriumTwoSidedBaseMeasure
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  infer_instance

/-- The forward residual-and-future renewal path. -/
def equilibriumFuturePath : ((ℕ → ℝ) × (ℕ → ℝ)) → (ℕ → ℝ) := Prod.fst

/-- The backward age-and-past renewal path. -/
def equilibriumPastPath : ((ℕ → ℝ) × (ℕ → ℝ)) → (ℕ → ℝ) := Prod.snd

/-- Actual interarrival gaps of the origin-split stationary configuration.
The special gap at index zero straddles the deterministic origin and is the
sum of its backward age and forward residual. -/
def equilibriumBaseGap (ω : (ℕ → ℝ) × (ℕ → ℝ)) : ℤ → ℝ
  | Int.ofNat 0 => interarrival 0 (equilibriumPastPath ω) +
      interarrival 0 (equilibriumFuturePath ω)
  | Int.ofNat (n + 1) => interarrival (n + 1) (equilibriumFuturePath ω)
  | Int.negSucc n => interarrival (n + 1) (equilibriumPastPath ω)

/-- Ordered epochs of the untagged equilibrium configuration. Index zero is
the last arrival before time zero; index one is the first after it. -/
def equilibriumBaseArrival (ω : (ℕ → ℝ) × (ℕ → ℝ)) : ℤ → ℝ :=
  fun i => candidatePalmArrival (equilibriumBaseGap ω) i -
    interarrival 0 (equilibriumPastPath ω)

theorem measurable_equilibriumBaseGap (i : ℤ) :
    Measurable (fun ω : (ℕ → ℝ) × (ℕ → ℝ) => equilibriumBaseGap ω i) := by
  cases i with
  | ofNat n =>
      cases n with
      | zero =>
          change Measurable (fun ω : (ℕ → ℝ) × (ℕ → ℝ) =>
            interarrival 0 ω.2 + interarrival 0 ω.1)
          exact ((measurable_interarrival 0).comp measurable_snd).add
            ((measurable_interarrival 0).comp measurable_fst)
      | succ n =>
          change Measurable (fun ω : (ℕ → ℝ) × (ℕ → ℝ) => interarrival (n + 1) ω.1)
          exact (measurable_interarrival (n + 1)).comp measurable_fst
  | negSucc n =>
      change Measurable (fun ω : (ℕ → ℝ) × (ℕ → ℝ) => interarrival (n + 1) ω.2)
      exact (measurable_interarrival (n + 1)).comp measurable_snd

theorem measurable_candidatePalmArrival_equilibriumBaseGap (i : ℤ) :
    Measurable (fun ω : (ℕ → ℝ) × (ℕ → ℝ) =>
      candidatePalmArrival (equilibriumBaseGap ω) i) := by
  cases i with
  | ofNat n =>
      change Measurable (fun ω : (ℕ → ℝ) × (ℕ → ℝ) =>
        ∑ j ∈ Finset.range n, twoSidedGap (Int.ofNat j) (equilibriumBaseGap ω))
      exact (Finset.range n).measurable_sum fun j _ => by
        simpa [twoSidedGap] using measurable_equilibriumBaseGap (Int.ofNat j)
  | negSucc n =>
      change Measurable (fun ω : (ℕ → ℝ) × (ℕ → ℝ) =>
        -∑ j ∈ Finset.range (n + 1), twoSidedGap (Int.negSucc j) (equilibriumBaseGap ω))
      exact ((Finset.range (n + 1)).measurable_sum fun j _ => by
        simpa [twoSidedGap] using measurable_equilibriumBaseGap (Int.negSucc j)).neg

theorem measurable_equilibriumBaseArrival (i : ℤ) :
    Measurable (fun ω : (ℕ → ℝ) × (ℕ → ℝ) => equilibriumBaseArrival ω i) := by
  exact (measurable_candidatePalmArrival_equilibriumBaseGap i).sub
    ((measurable_interarrival 0).comp measurable_snd)

/-- The two-sided gap path seen from a selected indexed base arrival. -/
def equilibriumRecenterGap (i : ℤ) :
    ((ℕ → ℝ) × (ℕ → ℝ)) → ℤ → ℝ :=
  fun ω j => equilibriumBaseGap ω (j + i)

theorem measurable_equilibriumRecenterGap (i : ℤ) :
    Measurable (equilibriumRecenterGap i) := by
  exact measurable_pi_iff.2 fun j => measurable_equilibriumBaseGap (j + i)

/-- Recentered candidate arrivals agree pathwise with differences of the
untagged equilibrium epochs. Thus the arrival-algebra component of a future
Campbell/Palm recentering map is already concrete; identifying its law as the
Palm law remains separate. -/
theorem candidatePalmArrival_equilibriumRecenterGap
    (ω : (ℕ → ℝ) × (ℕ → ℝ)) (i j : ℤ) :
    candidatePalmArrival (equilibriumRecenterGap i ω) j =
      equilibriumBaseArrival ω (i + j) - equilibriumBaseArrival ω i := by
  simpa [equilibriumRecenterGap, equilibriumBaseArrival] using
    candidatePalmArrival_recenter (equilibriumBaseGap ω) i j

theorem equilibriumBaseArrival_zero (ω : (ℕ → ℝ) × (ℕ → ℝ)) :
    equilibriumBaseArrival ω 0 = -interarrival 0 (equilibriumPastPath ω) := by
  simp [equilibriumBaseArrival, candidatePalmArrival]

theorem equilibriumBaseArrival_one (ω : (ℕ → ℝ) × (ℕ → ℝ)) :
    equilibriumBaseArrival ω 1 = interarrival 0 (equilibriumFuturePath ω) := by
  simp [equilibriumBaseArrival, candidatePalmArrival,
    twoSidedGap, equilibriumBaseGap, equilibriumFuturePath, equilibriumPastPath]

/-- Nonnegative finite gap sums split into the fixed backward age and the
ordinary residual-and-future renewal sums. -/
theorem equilibriumBaseGap_sum_nonneg
    (ω : (ℕ → ℝ) × (ℕ → ℝ)) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), equilibriumBaseGap ω (Int.ofNat i)) =
      interarrival 0 ω.2 + ∑ i ∈ Finset.range (n + 1), interarrival i ω.1 := by
  induction n with
  | zero =>
      simp [equilibriumBaseGap, equilibriumFuturePath, equilibriumPastPath]
  | succ n ih =>
      change (∑ i ∈ Finset.range ((n + 1) + 1),
          equilibriumBaseGap ω (Int.ofNat i)) =
        interarrival 0 ω.2 + ∑ i ∈ Finset.range ((n + 1) + 1), interarrival i ω.1
      calc
        (∑ i ∈ Finset.range ((n + 1) + 1), equilibriumBaseGap ω (Int.ofNat i)) =
            (∑ i ∈ Finset.range (n + 1), equilibriumBaseGap ω (Int.ofNat i)) +
              equilibriumBaseGap ω (Int.ofNat (n + 1)) := by
          rw [Finset.sum_range_succ]
        _ = (interarrival 0 ω.2 + ∑ i ∈ Finset.range (n + 1), interarrival i ω.1) +
              interarrival (n + 1) ω.1 := by
          rw [ih]
          simp [equilibriumBaseGap, equilibriumFuturePath]
        _ = interarrival 0 ω.2 +
              ∑ i ∈ Finset.range ((n + 1) + 1), interarrival i ω.1 := by
          conv_rhs => arg 2; rw [Finset.sum_range_succ]
          ring

/-- The `(n+1)`st forward base arrival is the `n`th ordinary
residual-and-future renewal epoch. -/
theorem equilibriumBaseArrival_ofNat_succ
    (ω : (ℕ → ℝ) × (ℕ → ℝ)) (n : ℕ) :
    equilibriumBaseArrival ω (Int.ofNat (n + 1)) =
      arrivalTime n (equilibriumFuturePath ω) := by
  unfold equilibriumBaseArrival
  simp only [candidatePalmArrival]
  change (∑ i ∈ Finset.range (n + 1),
      equilibriumBaseGap ω (Int.ofNat i)) - interarrival 0 ω.2 =
    arrivalTime n ω.1
  rw [equilibriumBaseGap_sum_nonneg]
  simp [arrivalTime]

/-- The negative-index base epochs are the negatives of the ordinary
age-and-past renewal epochs. -/
theorem equilibriumBaseArrival_negSucc
    (ω : (ℕ → ℝ) × (ℕ → ℝ)) (n : ℕ) :
    equilibriumBaseArrival ω (Int.negSucc n) =
      -arrivalTime (n + 1) (equilibriumPastPath ω) := by
  unfold equilibriumBaseArrival
  rw [candidatePalmArrival_negSucc]
  change -(∑ i ∈ Finset.range (n + 1),
      equilibriumBaseGap ω (Int.negSucc i)) - interarrival 0 ω.2 =
    -arrivalTime (n + 1) ω.2
  simp only [equilibriumBaseGap, equilibriumPastPath]
  conv_rhs =>
    rw [arrivalTime, Finset.sum_range_succ' (fun i => interarrival i ω.2) (n + 1)]
  ring

/-- The deterministic origin lies strictly in the size-biased gap between
indexed arrivals zero and one almost surely. -/
theorem ae_equilibrium_origin_between_arrivals
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ ω ∂equilibriumTwoSidedBaseMeasure rate,
      equilibriumBaseArrival ω 0 < 0 ∧ 0 < equilibriumBaseArrival ω 1 := by
  let μ := exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hfuture : ∀ᵐ ω : (ℕ → ℝ) × (ℕ → ℝ) ∂μ.prod μ,
      0 < interarrival 0 (equilibriumFuturePath ω) := by
    refine ae_of_ae_map (μ := μ.prod μ) (f := Prod.fst)
      (p := fun ξ : ℕ → ℝ => 0 < interarrival 0 ξ)
      measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact (ae_all_interarrival_positive hrate).mono fun ξ hξ => hξ 0
  have hpast : ∀ᵐ ω : (ℕ → ℝ) × (ℕ → ℝ) ∂μ.prod μ,
      0 < interarrival 0 (equilibriumPastPath ω) := by
    refine ae_of_ae_map (μ := μ.prod μ) (f := Prod.snd)
      (p := fun ξ : ℕ → ℝ => 0 < interarrival 0 ξ)
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact (ae_all_interarrival_positive hrate).mono fun ξ hξ => hξ 0
  filter_upwards [hfuture, hpast] with ω hfuture hpast
  rw [equilibriumBaseArrival_zero, equilibriumBaseArrival_one]
  exact ⟨neg_lt_zero.mpr hpast, hfuture⟩

theorem ae_all_equilibriumBaseGap_positive
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ ω ∂equilibriumTwoSidedBaseMeasure rate,
      ∀ i : ℤ, 0 < equilibriumBaseGap ω i := by
  let μ := exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hfuture : ∀ᵐ ω : (ℕ → ℝ) × (ℕ → ℝ) ∂μ.prod μ,
      ∀ n : ℕ, 0 < interarrival n (equilibriumFuturePath ω) := by
    refine ae_of_ae_map (μ := μ.prod μ) (f := Prod.fst)
      (p := fun ξ : ℕ → ℝ => ∀ n : ℕ, 0 < interarrival n ξ)
      measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact ae_all_interarrival_positive hrate
  have hpast : ∀ᵐ ω : (ℕ → ℝ) × (ℕ → ℝ) ∂μ.prod μ,
      ∀ n : ℕ, 0 < interarrival n (equilibriumPastPath ω) := by
    refine ae_of_ae_map (μ := μ.prod μ) (f := Prod.snd)
      (p := fun ξ : ℕ → ℝ => ∀ n : ℕ, 0 < interarrival n ξ)
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact ae_all_interarrival_positive hrate
  filter_upwards [hfuture, hpast] with ω hfuture hpast
  intro i
  cases i with
  | ofNat n =>
      cases n with
      | zero =>
          exact add_pos (hpast 0) (hfuture 0)
      | succ n => exact hfuture (n + 1)
  | negSucc n => exact hpast (n + 1)

theorem ae_equilibriumBaseArrival_strictMono
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ ω ∂equilibriumTwoSidedBaseMeasure rate,
      StrictMono (equilibriumBaseArrival ω) := by
  filter_upwards [ae_all_equilibriumBaseGap_positive hrate] with ω hω
  intro i j hij
  exact sub_lt_sub_right
    (candidatePalmArrival_strictMono_of_positive (equilibriumBaseGap ω) hω hij) _

/-- Reindexing an iid two-sided Palm gap configuration by a deterministic
arrival index. -/
def twoSidedGapIndexShift (k : ℤ) : (ℤ → ℝ) → (ℤ → ℝ) :=
  fun ω i => twoSidedGap (i + k) ω

theorem measurable_twoSidedGapIndexShift (k : ℤ) :
    Measurable (twoSidedGapIndexShift k) := by
  exact measurable_pi_iff.2 fun i => measurable_twoSidedGap (i + k)

theorem iIndepFun_twoSidedGapIndexShift
    {rate : ℝ} (hrate : 0 < rate) (k : ℤ) :
    ProbabilityTheory.iIndepFun (fun i ω => twoSidedGap (i + k) ω)
      (twoSidedInterarrivalMeasure rate) := by
  exact ProbabilityTheory.iIndepFun.precomp
    (g := fun i : ℤ => i + k)
    (by intro a b hab; exact add_right_cancel hab)
    (iIndepFun_twoSidedGap hrate)

/-- The iid two-sided Palm gap law is invariant under every deterministic
arrival-index shift. -/
theorem twoSidedGapIndexShift_measurePreserving
    {rate : ℝ} (hrate : 0 < rate) (k : ℤ) :
    MeasurePreserving (twoSidedGapIndexShift k)
      (twoSidedInterarrivalMeasure rate) (twoSidedInterarrivalMeasure rate) := by
  refine ⟨measurable_twoSidedGapIndexShift k, ?_⟩
  change Measure.map (fun ω i => twoSidedGap (i + k) ω)
    (twoSidedInterarrivalMeasure rate) = twoSidedInterarrivalMeasure rate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  rw [ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun i => measurable_twoSidedGap (i + k)) |>.mp
    (iIndepFun_twoSidedGapIndexShift hrate k)]
  simp only [twoSidedInterarrivalMeasure]
  congr 1
  funext i
  exact (twoSidedGap_hasLaw hrate (i + k)).map_eq

/-- The number of equilibrium arrivals in `(0,t]` is the canonical renewal
count of the residual-and-future half. -/
def equilibriumForwardCount (t : ℝ) : ((ℕ → ℝ) × (ℕ → ℝ)) → ℕ :=
  fun ω => canonicalRenewalCount t (equilibriumFuturePath ω)

/-- A finite index enumerator for the base arrivals in `(0,t]`.  The
almost-everywhere correctness statement below is deliberately restricted to
the half-line from the deterministic origin; translating this enumeration to
arbitrary time windows is part of the remaining real-time suspension-flow
construction. -/
noncomputable def equilibriumForwardArrivalIndices (t : ℝ)
    (ω : (ℕ → ℝ) × (ℕ → ℝ)) : Finset ℤ :=
  (Finset.range (equilibriumForwardCount t ω)).image fun n => Int.ofNat (n + 1)

theorem mem_equilibriumForwardArrivalIndices_iff
    (t : ℝ) (ω : (ℕ → ℝ) × (ℕ → ℝ)) (i : ℤ) :
    i ∈ equilibriumForwardArrivalIndices t ω ↔
      ∃ n : ℕ, n < equilibriumForwardCount t ω ∧ Int.ofNat (n + 1) = i := by
  simp [equilibriumForwardArrivalIndices]

/-- The local finite enumerator has exactly the renewal-count cardinality. -/
theorem equilibriumForwardArrivalIndices_card
    (t : ℝ) (ω : (ℕ → ℝ) × (ℕ → ℝ)) :
    (equilibriumForwardArrivalIndices t ω).card = equilibriumForwardCount t ω := by
  rw [equilibriumForwardArrivalIndices, Finset.card_image_of_injective]
  · simp
  · intro a b hab
    apply Nat.succ.inj
    apply Int.ofNat.inj
    simpa using hab

/-- The forward finite enumerator identifies exactly the base arrivals in
`(0,t]` almost surely.  This provides the local-finiteness/enumeration piece
of a future Campbell certificate at the origin, but is not yet a
real-time-shift-invariant point-process construction. -/
theorem ae_mem_equilibriumForwardArrivalIndices_iff
    {rate : ℝ} (hrate : 0 < rate) (t : ℝ) :
    ∀ᵐ ω ∂equilibriumTwoSidedBaseMeasure rate, ∀ i : ℤ,
      i ∈ equilibriumForwardArrivalIndices t ω ↔
        0 < equilibriumBaseArrival ω i ∧ equilibriumBaseArrival ω i ≤ t := by
  let μ := exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hfutureCount : ∀ᵐ ω : (ℕ → ℝ) × (ℕ → ℝ) ∂μ.prod μ,
      ∀ u : ℝ, ∀ n : ℕ,
        n < canonicalRenewalCount u ω.1 ↔ arrivalTime n ω.1 ≤ u := by
    refine ae_of_ae_map (μ := μ.prod μ) (f := Prod.fst)
      (p := fun ξ : ℕ → ℝ => ∀ u : ℝ, ∀ n : ℕ,
        n < canonicalRenewalCount u ξ ↔ arrivalTime n ξ ≤ u)
      measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact ae_lt_canonicalRenewalCount_iff_arrivalTime_le hrate
  filter_upwards [ae_equilibrium_origin_between_arrivals hrate,
    ae_equilibriumBaseArrival_strictMono hrate, hfutureCount] with ω horigin hstrict hcount
  intro i
  constructor
  · intro hi
    obtain ⟨n, hn, rfl⟩ := (mem_equilibriumForwardArrivalIndices_iff t ω i).mp hi
    constructor
    · calc
        0 < equilibriumBaseArrival ω 1 := horigin.2
        _ ≤ equilibriumBaseArrival ω (Int.ofNat (n + 1)) :=
          hstrict.monotone (show Int.ofNat 1 ≤ Int.ofNat (n + 1) from
            Int.ofNat_le.mpr (Nat.succ_le_succ (Nat.zero_le n)))
    · rw [equilibriumBaseArrival_ofNat_succ]
      exact (hcount t n).mp hn
  · rintro ⟨hpositive, hle⟩
    cases i with
    | ofNat m =>
        cases m with
        | zero => exact (not_lt_of_ge horigin.1.le hpositive).elim
        | succ n =>
            apply (mem_equilibriumForwardArrivalIndices_iff t ω (Int.ofNat (n + 1))).mpr
            refine ⟨n, ?_, rfl⟩
            apply (hcount t n).mpr
            change arrivalTime n (equilibriumFuturePath ω) ≤ t
            rw [← equilibriumBaseArrival_ofNat_succ]
            exact hle
    | negSucc n =>
        have hneg : equilibriumBaseArrival ω (Int.negSucc n) < 0 := by
          calc
            equilibriumBaseArrival ω (Int.negSucc n) < equilibriumBaseArrival ω 0 :=
              hstrict (by omega)
            _ < 0 := horigin.1
        exact (not_lt_of_ge hneg.le hpositive).elim

/-- On one full-measure carrier, every forward equilibrium ledger has its
literal right-closed interval meaning.  The uniform-in-time form is what a
long-run marked-work argument needs. -/
theorem ae_all_mem_equilibriumForwardArrivalIndices_iff
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ ω ∂equilibriumTwoSidedBaseMeasure rate, ∀ t : ℝ, ∀ i : ℤ,
      i ∈ equilibriumForwardArrivalIndices t ω ↔
        0 < equilibriumBaseArrival ω i ∧ equilibriumBaseArrival ω i ≤ t := by
  let μ := exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hfutureCount : ∀ᵐ ω : (ℕ → ℝ) × (ℕ → ℝ) ∂μ.prod μ,
      ∀ u : ℝ, ∀ n : ℕ,
        n < canonicalRenewalCount u ω.1 ↔ arrivalTime n ω.1 ≤ u := by
    refine ae_of_ae_map (μ := μ.prod μ) (f := Prod.fst)
      (p := fun ξ : ℕ → ℝ => ∀ u : ℝ, ∀ n : ℕ,
        n < canonicalRenewalCount u ξ ↔ arrivalTime n ξ ≤ u)
      measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact ae_lt_canonicalRenewalCount_iff_arrivalTime_le hrate
  filter_upwards [ae_equilibrium_origin_between_arrivals hrate,
    ae_equilibriumBaseArrival_strictMono hrate, hfutureCount] with ω horigin hstrict hcount
  intro t i
  constructor
  · intro hi
    obtain ⟨n, hn, rfl⟩ := (mem_equilibriumForwardArrivalIndices_iff t ω i).mp hi
    constructor
    · calc
        0 < equilibriumBaseArrival ω 1 := horigin.2
        _ ≤ equilibriumBaseArrival ω (Int.ofNat (n + 1)) :=
          hstrict.monotone (show Int.ofNat 1 ≤ Int.ofNat (n + 1) from
            Int.ofNat_le.mpr (Nat.succ_le_succ (Nat.zero_le n)))
    · rw [equilibriumBaseArrival_ofNat_succ]
      exact (hcount t n).mp hn
  · rintro ⟨hpositive, hle⟩
    cases i with
    | ofNat m =>
        cases m with
        | zero => exact (not_lt_of_ge horigin.1.le hpositive).elim
        | succ n =>
            apply (mem_equilibriumForwardArrivalIndices_iff t ω (Int.ofNat (n + 1))).mpr
            refine ⟨n, ?_, rfl⟩
            apply (hcount t n).mpr
            change arrivalTime n (equilibriumFuturePath ω) ≤ t
            rw [← equilibriumBaseArrival_ofNat_succ]
            exact hle
    | negSucc n =>
        have hneg : equilibriumBaseArrival ω (Int.negSucc n) < 0 := by
          calc
            equilibriumBaseArrival ω (Int.negSucc n) < equilibriumBaseArrival ω 0 :=
              hstrict (by omega)
            _ < 0 := horigin.1
        exact (not_lt_of_ge hneg.le hpositive).elim

theorem measurable_equilibriumForwardCount (t : ℝ) :
    Measurable (equilibriumForwardCount t) := by
  exact (measurable_canonicalRenewalCount t).comp measurable_fst

/-- Every forward window from the deterministic origin has the Poisson
marginal under the origin-split equilibrium construction. -/
theorem equilibriumForwardCount_hasLaw_poisson
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    HasLaw (equilibriumForwardCount t)
      (ProbabilityTheory.poissonMeasure
        (⟨rate * t, mul_nonneg hrate.le ht⟩ : ℝ≥0))
      (equilibriumTwoSidedBaseMeasure rate) := by
  let μ := exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  refine ⟨(measurable_equilibriumForwardCount t).aemeasurable, ?_⟩
  change (μ.prod μ).map (fun ω => canonicalRenewalCount t ω.1) =
    ProbabilityTheory.poissonMeasure (⟨rate * t, mul_nonneg hrate.le ht⟩ : ℝ≥0)
  calc
    (μ.prod μ).map (fun ω => canonicalRenewalCount t ω.1) =
        ((μ.prod μ).map Prod.fst).map (canonicalRenewalCount t) := by
      symm
      simpa [Function.comp_def] using
        (Measure.map_map (μ := μ.prod μ) (measurable_canonicalRenewalCount t) measurable_fst)
    _ = μ.map (canonicalRenewalCount t) := by
      rw [Measure.map_fst_prod, measure_univ, one_smul]
    _ = ProbabilityTheory.poissonMeasure
        (⟨rate * t, mul_nonneg hrate.le ht⟩ : ℝ≥0) :=
      (canonicalRenewalCount_hasLaw_poisson hrate ht).map_eq

/-- The Poisson first moment in the nonnegative integral form used by a
Campbell formula. -/
theorem lintegral_nat_poissonMeasure (r : ℝ≥0) :
    ∫⁻ n : ℕ, (n : ℝ≥0∞) ∂ProbabilityTheory.poissonMeasure r = ENNReal.ofReal r := by
  rw [ProbabilityTheory.poissonMeasure, MeasureTheory.lintegral_sum_measure]
  simp_rw [MeasureTheory.lintegral_smul_measure, MeasureTheory.lintegral_dirac]
  simp only [smul_eq_mul]
  have hterm_nonneg : ∀ n : ℕ,
      0 ≤ Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ) * n := by
    intro n
    positivity
  have hsum := hasSum_poisson_firstMoment (r : ℝ)
  have hrewrite : (fun n : ℕ =>
      ENNReal.ofReal (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ)) *
        (n : ℝ≥0∞)) =
      (fun n : ℕ => ENNReal.ofReal
        (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ) * n)) := by
    funext n
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  rw [hrewrite, ← ENNReal.ofReal_tsum_of_nonneg hterm_nonneg hsum.summable]
  exact congrArg ENNReal.ofReal hsum.tsum_eq

/-- Intensity calibration in the exact `ℝ≥0∞` form of the unmarked Campbell
formula. -/
theorem lintegral_equilibriumForwardCount
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    ∫⁻ ω, (equilibriumForwardCount t ω : ℝ≥0∞) ∂equilibriumTwoSidedBaseMeasure rate =
      ENNReal.ofReal (rate * t) := by
  let r : ℝ≥0 := ⟨rate * t, mul_nonneg hrate.le ht⟩
  calc
    ∫⁻ ω, (equilibriumForwardCount t ω : ℝ≥0∞) ∂equilibriumTwoSidedBaseMeasure rate =
        ∫⁻ n : ℕ, (n : ℝ≥0∞) ∂ProbabilityTheory.poissonMeasure r := by
          simpa [r, Function.comp_def] using
            (equilibriumForwardCount_hasLaw_poisson hrate ht).lintegral_comp
              (f := fun n : ℕ => (n : ℝ≥0∞))
              (measurable_of_countable _).aemeasurable
    _ = ENNReal.ofReal r := lintegral_nat_poissonMeasure r
    _ = ENNReal.ofReal (rate * t) := rfl

/-- The forward finite enumerator has intensity-calibrated expected
cardinality in the exact nonnegative-integral form. -/
theorem lintegral_equilibriumForwardArrivalIndices_card
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    ∫⁻ ω, ((equilibriumForwardArrivalIndices t ω).card : ℝ≥0∞)
      ∂equilibriumTwoSidedBaseMeasure rate = ENNReal.ofReal (rate * t) := by
  simp_rw [equilibriumForwardArrivalIndices_card]
  exact lintegral_equilibriumForwardCount hrate ht

/-- Intensity calibration at the deterministic origin: the expected number
of equilibrium arrivals in `(0,t]` is `rate * t`. -/
theorem integral_equilibriumForwardCount
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    ∫ ω, (equilibriumForwardCount t ω : ℝ) ∂equilibriumTwoSidedBaseMeasure rate =
      rate * t := by
  let r : ℝ≥0 := ⟨rate * t, mul_nonneg hrate.le ht⟩
  calc
    ∫ ω, (equilibriumForwardCount t ω : ℝ) ∂equilibriumTwoSidedBaseMeasure rate =
        ∫ n : ℕ, (n : ℝ) ∂ProbabilityTheory.poissonMeasure r := by
          simpa [r, Function.comp_def] using
            (equilibriumForwardCount_hasLaw_poisson hrate ht).integral_comp
              (f := fun n : ℕ => (n : ℝ)) (by fun_prop)
    _ = r := integral_id_poissonMeasure r
    _ = rate * t := rfl

/-- The forward finite enumerator has intensity-calibrated expected
cardinality. -/
theorem integral_equilibriumForwardArrivalIndices_card
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    ∫ ω, ((equilibriumForwardArrivalIndices t ω).card : ℝ)
      ∂equilibriumTwoSidedBaseMeasure rate = rate * t := by
  simp_rw [equilibriumForwardArrivalIndices_card]
  exact integral_equilibriumForwardCount hrate ht

/-- The number of equilibrium arrivals in `[-t,0)` is the canonical renewal
count of the age-and-past half. -/
def equilibriumBackwardCount (t : ℝ) : ((ℕ → ℝ) × (ℕ → ℝ)) → ℕ :=
  fun ω => canonicalRenewalCount t (equilibriumPastPath ω)

/-- Enumeration of base-arrival indices on the negative-time side, ordered by
increasing distance from the deterministic origin. -/
def equilibriumBackwardArrivalIndex : ℕ → ℤ
  | 0 => 0
  | n + 1 => Int.negSucc n

theorem equilibriumBaseArrival_backwardIndex
    (ω : (ℕ → ℝ) × (ℕ → ℝ)) (n : ℕ) :
    equilibriumBaseArrival ω (equilibriumBackwardArrivalIndex n) =
      -arrivalTime n (equilibriumPastPath ω) := by
  cases n with
  | zero =>
      simp [equilibriumBackwardArrivalIndex, equilibriumBaseArrival_zero,
        arrivalTime_zero]
  | succ n =>
      simpa [equilibriumBackwardArrivalIndex] using
        equilibriumBaseArrival_negSucc ω n

/-- Finite indices of base arrivals in the backward half-window `[-t,0)`. -/
noncomputable def equilibriumBackwardArrivalIndices (t : ℝ)
    (ω : (ℕ → ℝ) × (ℕ → ℝ)) : Finset ℤ :=
  (Finset.range (equilibriumBackwardCount t ω)).image equilibriumBackwardArrivalIndex

theorem mem_equilibriumBackwardArrivalIndices_iff
    (t : ℝ) (ω : (ℕ → ℝ) × (ℕ → ℝ)) (i : ℤ) :
    i ∈ equilibriumBackwardArrivalIndices t ω ↔
      ∃ n : ℕ, n < equilibriumBackwardCount t ω ∧
        equilibriumBackwardArrivalIndex n = i := by
  simp [equilibriumBackwardArrivalIndices]

theorem equilibriumBackwardArrivalIndex_injective :
    Function.Injective equilibriumBackwardArrivalIndex := by
  intro m n h
  cases m <;> cases n <;> simp_all [equilibriumBackwardArrivalIndex]

/-- The backward finite enumerator has exactly the backward renewal-count
cardinality. -/
theorem equilibriumBackwardArrivalIndices_card
    (t : ℝ) (ω : (ℕ → ℝ) × (ℕ → ℝ)) :
    (equilibriumBackwardArrivalIndices t ω).card = equilibriumBackwardCount t ω := by
  rw [equilibriumBackwardArrivalIndices, Finset.card_image_of_injective]
  · simp
  · exact equilibriumBackwardArrivalIndex_injective

theorem measurable_equilibriumBackwardCount (t : ℝ) :
    Measurable (equilibriumBackwardCount t) := by
  exact (measurable_canonicalRenewalCount t).comp measurable_snd

theorem equilibriumBackwardCount_hasLaw_poisson
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    HasLaw (equilibriumBackwardCount t)
      (ProbabilityTheory.poissonMeasure
        (⟨rate * t, mul_nonneg hrate.le ht⟩ : ℝ≥0))
      (equilibriumTwoSidedBaseMeasure rate) := by
  let μ := exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  refine ⟨(measurable_equilibriumBackwardCount t).aemeasurable, ?_⟩
  change (μ.prod μ).map (fun ω => canonicalRenewalCount t ω.2) =
    ProbabilityTheory.poissonMeasure (⟨rate * t, mul_nonneg hrate.le ht⟩ : ℝ≥0)
  calc
    (μ.prod μ).map (fun ω => canonicalRenewalCount t ω.2) =
        ((μ.prod μ).map Prod.snd).map (canonicalRenewalCount t) := by
      symm
      simpa [Function.comp_def] using
        (Measure.map_map (μ := μ.prod μ) (measurable_canonicalRenewalCount t) measurable_snd)
    _ = μ.map (canonicalRenewalCount t) := by
      rw [Measure.map_snd_prod, measure_univ, one_smul]
    _ = ProbabilityTheory.poissonMeasure
        (⟨rate * t, mul_nonneg hrate.le ht⟩ : ℝ≥0) :=
      (canonicalRenewalCount_hasLaw_poisson hrate ht).map_eq

/-- On the full-measure positive-gap set, the backward finite enumerator is
exactly the point set of base arrivals in `[-t,0)`. -/
theorem ae_mem_equilibriumBackwardArrivalIndices_iff
    {rate : ℝ} (hrate : 0 < rate) (t : ℝ) :
    ∀ᵐ ω ∂equilibriumTwoSidedBaseMeasure rate, ∀ i : ℤ,
      i ∈ equilibriumBackwardArrivalIndices t ω ↔
        -t ≤ equilibriumBaseArrival ω i ∧ equilibriumBaseArrival ω i < 0 := by
  let μ := exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hpastCount : ∀ᵐ ω : (ℕ → ℝ) × (ℕ → ℝ) ∂μ.prod μ,
      ∀ u : ℝ, ∀ n : ℕ,
        n < canonicalRenewalCount u ω.2 ↔ arrivalTime n ω.2 ≤ u := by
    refine ae_of_ae_map (μ := μ.prod μ) (f := Prod.snd)
      (p := fun ξ : ℕ → ℝ => ∀ u : ℝ, ∀ n : ℕ,
        n < canonicalRenewalCount u ξ ↔ arrivalTime n ξ ≤ u)
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact ae_lt_canonicalRenewalCount_iff_arrivalTime_le hrate
  have hfuture : ∀ᵐ ω : (ℕ → ℝ) × (ℕ → ℝ) ∂μ.prod μ,
      ∀ n : ℕ, 0 < interarrival n ω.1 := by
    refine ae_of_ae_map (μ := μ.prod μ) (f := Prod.fst)
      (p := fun ξ : ℕ → ℝ => ∀ n : ℕ, 0 < interarrival n ξ)
      measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact ae_all_interarrival_positive hrate
  have hpast : ∀ᵐ ω : (ℕ → ℝ) × (ℕ → ℝ) ∂μ.prod μ,
      ∀ n : ℕ, 0 < interarrival n ω.2 := by
    refine ae_of_ae_map (μ := μ.prod μ) (f := Prod.snd)
      (p := fun ξ : ℕ → ℝ => ∀ n : ℕ, 0 < interarrival n ξ)
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact ae_all_interarrival_positive hrate
  filter_upwards [hpastCount, hfuture, hpast] with ω hcount hfuture hpast
  intro i
  constructor
  · intro hi
    obtain ⟨n, hn, rfl⟩ := (mem_equilibriumBackwardArrivalIndices_iff t ω i).mp hi
    have htime : arrivalTime n ω.2 ≤ t := (hcount t n).mp hn
    constructor
    · rw [equilibriumBaseArrival_backwardIndex]
      exact neg_le_neg htime
    · rw [equilibriumBaseArrival_backwardIndex]
      apply neg_lt_zero.mpr
      exact lt_of_lt_of_le (by simpa [arrivalTime_zero] using hpast 0)
        ((arrivalTime_strictMono_of_positive ω.2 hpast).monotone (Nat.zero_le n))
  · rintro ⟨hle, hneg⟩
    cases i with
    | ofNat m =>
        cases m with
        | zero =>
            apply (mem_equilibriumBackwardArrivalIndices_iff t ω 0).mpr
            refine ⟨0, ?_, rfl⟩
            apply (hcount t 0).mpr
            change -t ≤ equilibriumBaseArrival ω 0 at hle
            rw [equilibriumBaseArrival_zero] at hle
            change -t ≤ -interarrival 0 ω.2 at hle
            simpa [arrivalTime_zero] using (neg_le_neg_iff.mp hle)
        | succ n =>
            rw [equilibriumBaseArrival_ofNat_succ] at hneg
            have hpos : 0 < arrivalTime n ω.1 :=
              lt_of_lt_of_le (by simpa [arrivalTime_zero] using hfuture 0)
                ((arrivalTime_strictMono_of_positive ω.1 hfuture).monotone (Nat.zero_le n))
            exact (not_lt_of_ge hpos.le hneg).elim
    | negSucc n =>
        apply (mem_equilibriumBackwardArrivalIndices_iff t ω (Int.negSucc n)).mpr
        refine ⟨n + 1, ?_, by simp [equilibriumBackwardArrivalIndex]⟩
        apply (hcount t (n + 1)).mpr
        rw [equilibriumBaseArrival_negSucc] at hle
        exact neg_le_neg_iff.mp hle

/-- A finite candidate enumerator for base arrivals in an arbitrary bounded
left-open, right-closed interval. The filter records the endpoint convention
explicitly. -/
noncomputable def equilibriumIntervalArrivalIndices (a b : ℝ)
    (ω : (ℕ → ℝ) × (ℕ → ℝ)) : Finset ℤ :=
  ((equilibriumForwardArrivalIndices b ω) ∪
    (equilibriumBackwardArrivalIndices (-a) ω)).filter
      (fun i => a < equilibriumBaseArrival ω i ∧ equilibriumBaseArrival ω i ≤ b)

/-- The finite interval candidate enumerator is exactly the indexed
equilibrium point set in `(a,b]`, almost surely. -/
theorem ae_mem_equilibriumIntervalArrivalIndices_iff
    {rate : ℝ} (hrate : 0 < rate) (a b : ℝ) :
    ∀ᵐ ω ∂equilibriumTwoSidedBaseMeasure rate, ∀ i : ℤ,
      i ∈ equilibriumIntervalArrivalIndices a b ω ↔
        a < equilibriumBaseArrival ω i ∧ equilibriumBaseArrival ω i ≤ b := by
  filter_upwards [ae_mem_equilibriumForwardArrivalIndices_iff hrate b,
    ae_mem_equilibriumBackwardArrivalIndices_iff hrate (-a),
    ae_equilibrium_origin_between_arrivals hrate,
    ae_equilibriumBaseArrival_strictMono hrate] with ω hforward hbackward horigin hstrict
  intro i
  constructor
  · simp only [equilibriumIntervalArrivalIndices, Finset.mem_filter,
      Finset.mem_union]
    rintro ⟨_, hinterval⟩
    exact hinterval
  · intro hinterval
    have hsign : equilibriumBaseArrival ω i < 0 ∨ 0 < equilibriumBaseArrival ω i := by
      cases i with
      | ofNat n =>
          cases n with
          | zero => exact Or.inl horigin.1
          | succ n =>
              right
              exact lt_of_lt_of_le horigin.2
                (hstrict.monotone (show Int.ofNat 1 ≤ Int.ofNat (n + 1) from
                  Int.ofNat_le.mpr (Nat.succ_le_succ (Nat.zero_le n))))
      | negSucc n =>
          left
          exact lt_trans
            (hstrict (show Int.negSucc n < (0 : ℤ) by omega)) horigin.1
    simp only [equilibriumIntervalArrivalIndices, Finset.mem_filter,
      Finset.mem_union]
    refine ⟨?_, hinterval⟩
    rcases hsign with hneg | hpos
    · right
      apply (hbackward i).mpr
      constructor
      · simpa using (le_of_lt hinterval.1)
      · exact hneg
    · left
      exact (hforward i).mpr ⟨hpos, hinterval.2⟩

/-- A finite candidate enumerator for base arrivals in an arbitrary bounded
half-open interval. This is the endpoint convention used by the Campbell/Palm
certificate. -/
noncomputable def equilibriumHalfOpenIntervalArrivalIndices (a b : ℝ)
    (ω : (ℕ → ℝ) × (ℕ → ℝ)) : Finset ℤ :=
  ((equilibriumForwardArrivalIndices b ω) ∪
    (equilibriumBackwardArrivalIndices (-a) ω)).filter
      (fun i => a ≤ equilibriumBaseArrival ω i ∧ equilibriumBaseArrival ω i < b)

/-- The half-open finite candidate enumerator is exactly the indexed
equilibrium point set in `[a,b)`, almost surely. -/
theorem ae_mem_equilibriumHalfOpenIntervalArrivalIndices_iff
    {rate : ℝ} (hrate : 0 < rate) (a b : ℝ) :
    ∀ᵐ ω ∂equilibriumTwoSidedBaseMeasure rate, ∀ i : ℤ,
      i ∈ equilibriumHalfOpenIntervalArrivalIndices a b ω ↔
        a ≤ equilibriumBaseArrival ω i ∧ equilibriumBaseArrival ω i < b := by
  filter_upwards [ae_mem_equilibriumForwardArrivalIndices_iff hrate b,
    ae_mem_equilibriumBackwardArrivalIndices_iff hrate (-a),
    ae_equilibrium_origin_between_arrivals hrate,
    ae_equilibriumBaseArrival_strictMono hrate] with ω hforward hbackward horigin hstrict
  intro i
  constructor
  · simp only [equilibriumHalfOpenIntervalArrivalIndices, Finset.mem_filter,
      Finset.mem_union]
    rintro ⟨_, hinterval⟩
    exact hinterval
  · intro hinterval
    have hsign : equilibriumBaseArrival ω i < 0 ∨ 0 < equilibriumBaseArrival ω i := by
      cases i with
      | ofNat n =>
          cases n with
          | zero => exact Or.inl horigin.1
          | succ n =>
              right
              exact lt_of_lt_of_le horigin.2
                (hstrict.monotone (show Int.ofNat 1 ≤ Int.ofNat (n + 1) from
                  Int.ofNat_le.mpr (Nat.succ_le_succ (Nat.zero_le n))))
      | negSucc n =>
          left
          exact lt_trans
            (hstrict (show Int.negSucc n < (0 : ℤ) by omega)) horigin.1
    simp only [equilibriumHalfOpenIntervalArrivalIndices, Finset.mem_filter,
      Finset.mem_union]
    refine ⟨?_, hinterval⟩
    rcases hsign with hneg | hpos
    · right
      exact (hbackward i).mpr ⟨by simpa using hinterval.1, hneg⟩
    · left
      exact (hforward i).mpr ⟨hpos, hinterval.2.le⟩

/-- The endpoint conventions `[0,1)` and `(0,1]` enumerate the same
equilibrium arrivals almost surely. The only possible discrepancy is an
arrival at the deterministic right endpoint, which is null. -/
theorem ae_equilibriumHalfOpenIntervalArrivalIndices_zero_one_eq_forward
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ ω ∂equilibriumTwoSidedBaseMeasure rate,
      equilibriumHalfOpenIntervalArrivalIndices 0 1 ω =
        equilibriumForwardArrivalIndices 1 ω := by
  let μ := exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hfutureNoOne : ∀ᵐ ω : (ℕ → ℝ) × (ℕ → ℝ) ∂μ.prod μ,
      ∀ n : ℕ, arrivalTime n ω.1 ≠ 1 := by
    rw [ae_all_iff]
    intro n
    refine ae_of_ae_map (μ := μ.prod μ) (f := Prod.fst)
      (p := fun ξ : ℕ → ℝ => arrivalTime n ξ ≠ 1)
      measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul, ae_iff]
    simpa only [not_not] using arrivalTime_measure_singleton_eq_zero hrate n 1
  change ∀ᵐ ω : (ℕ → ℝ) × (ℕ → ℝ) ∂μ.prod μ,
    equilibriumHalfOpenIntervalArrivalIndices 0 1 ω =
      equilibriumForwardArrivalIndices 1 ω
  filter_upwards [ae_mem_equilibriumHalfOpenIntervalArrivalIndices_iff hrate 0 1,
    ae_mem_equilibriumForwardArrivalIndices_iff hrate 1,
    ae_equilibrium_origin_between_arrivals hrate,
    ae_equilibriumBaseArrival_strictMono hrate, hfutureNoOne] with
      ω hhalf hforward horigin hstrict hnoone
  apply Finset.ext
  intro i
  rw [hhalf i, hforward i]
  constructor
  · rintro ⟨hzero, hlt⟩
    refine ⟨?_, hlt.le⟩
    cases i with
    | ofNat m =>
        cases m with
        | zero => exact (not_lt_of_ge hzero horigin.1).elim
        | succ n =>
            exact lt_of_lt_of_le horigin.2
              (hstrict.monotone (show Int.ofNat 1 ≤ Int.ofNat (n + 1) from
                Int.ofNat_le.mpr (Nat.succ_le_succ (Nat.zero_le n))))
    | negSucc n =>
        have hneg : equilibriumBaseArrival ω (Int.negSucc n) < 0 := by
          calc
            equilibriumBaseArrival ω (Int.negSucc n) < equilibriumBaseArrival ω 0 :=
              hstrict (show Int.negSucc n < (0 : ℤ) by omega)
            _ < 0 := horigin.1
        exact (not_lt_of_ge hzero hneg).elim
  · rintro ⟨hpos, hle⟩
    refine ⟨hpos.le, ?_⟩
    cases i with
    | ofNat m =>
        cases m with
        | zero => exact lt_trans horigin.1 (by norm_num)
        | succ n =>
            rw [equilibriumBaseArrival_ofNat_succ] at hle ⊢
            exact lt_of_le_of_ne hle (hnoone n)
    | negSucc n =>
        have hneg : equilibriumBaseArrival ω (Int.negSucc n) < 0 := by
          calc
            equilibriumBaseArrival ω (Int.negSucc n) < equilibriumBaseArrival ω 0 :=
              hstrict (show Int.negSucc n < (0 : ℤ) by omega)
            _ < 0 := horigin.1
        exact lt_trans hneg (by norm_num)

/-- The unit half-open equilibrium window has expected cardinality exactly the
rate, in the `ℝ≥0∞` form required by the unmarked Campbell formula. -/
theorem lintegral_equilibriumHalfOpenIntervalArrivalIndices_zero_one_card
    {rate : ℝ} (hrate : 0 < rate) :
    ∫⁻ ω, ((equilibriumHalfOpenIntervalArrivalIndices 0 1 ω).card : ℝ≥0∞)
      ∂equilibriumTwoSidedBaseMeasure rate = ENNReal.ofReal rate := by
  calc
    ∫⁻ ω, ((equilibriumHalfOpenIntervalArrivalIndices 0 1 ω).card : ℝ≥0∞)
        ∂equilibriumTwoSidedBaseMeasure rate =
        ∫⁻ ω, ((equilibriumForwardArrivalIndices 1 ω).card : ℝ≥0∞)
          ∂equilibriumTwoSidedBaseMeasure rate := by
            apply MeasureTheory.lintegral_congr_ae
            filter_upwards [ae_equilibriumHalfOpenIntervalArrivalIndices_zero_one_eq_forward hrate]
              with ω hω
            rw [hω]
    _ = ENNReal.ofReal (rate * 1) :=
      lintegral_equilibriumForwardArrivalIndices_card hrate (by norm_num)
    _ = ENNReal.ofReal rate := by ring_nf

/-- Counts on the two sides of the deterministic origin are independent. -/
theorem equilibriumForwardCount_indep_backwardCount
    {rate s t : ℝ} (hrate : 0 < rate) :
    IndepFun (equilibriumForwardCount s) (equilibriumBackwardCount t)
      (equilibriumTwoSidedBaseMeasure rate) := by
  let μ := exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  change IndepFun (fun ω : (ℕ → ℝ) × (ℕ → ℝ) => canonicalRenewalCount s ω.1)
    (fun ω => canonicalRenewalCount t ω.2) (μ.prod μ)
  exact indepFun_prod (measurable_canonicalRenewalCount s)
    (measurable_canonicalRenewalCount t)

/-- Certificate-ready marked-count measurability: a countable measurable
description of the unit-window finite enumerator suffices for every
measurable recentering event. -/
theorem measurable_unitWindowCampbellCount_from_countable_parameter
    {Ωbase Ωtag κ : Type*} [MeasurableSpace Ωbase] [MeasurableSpace Ωtag]
    [MeasurableSpace κ] [Countable κ] [MeasurableSingletonClass κ]
    (arrivalsIn : ℝ → ℝ → Ωbase → Finset ℤ)
    (state : Ωbase → κ) (hstate : Measurable state)
    (indices : κ → Finset ℤ)
    (hunit : ∀ ω, arrivalsIn 0 1 ω = indices (state ω))
    (recenterAt : Ωbase → ℤ → Ωtag)
    (hrecenter : ∀ i, Measurable (fun ω => recenterAt ω i))
    (s : Set Ωtag) (hs : MeasurableSet s) :
    Measurable (fun ω => Palm.unitWindowCampbellCount arrivalsIn recenterAt s ω) := by
  classical
  let selected : Ωbase → ℤ → Bool := fun ω i => decide (recenterAt ω i ∈ s)
  have hselected : Measurable selected := by
    refine measurable_pi_iff.2 fun i => ?_
    change Measurable (fun ω => if recenterAt ω i ∈ s then true else false)
    exact Measurable.ite ((hrecenter i) hs) measurable_const measurable_const
  have hcount := Palm.measurable_count_from_countable_parameter state hstate indices
    selected hselected
  change Measurable (fun ω =>
    ((arrivalsIn 0 1 ω).filter fun i => recenterAt ω i ∈ s).card)
  convert hcount using 1
  funext ω
  rw [hunit]
  simp only [selected, decide_eq_true_eq]

/-- The equilibrium half-open enumerator has a measurable marked unit-window
count for every measurable Palm event. This closes the measurability field of
the Campbell certificate; the mass-transport identity remains separate. -/
theorem measurable_equilibriumMarkedUnitWindowCount_from_counts
    (s : Set (ℤ → ℝ)) (hs : MeasurableSet s) :
    Measurable (fun ω : (ℕ → ℝ) × (ℕ → ℝ) =>
      Palm.unitWindowCampbellCount equilibriumHalfOpenIntervalArrivalIndices
        (fun ω i => equilibriumRecenterGap i ω) s ω) := by
  classical
  let state : ((ℕ → ℝ) × (ℕ → ℝ)) → ℕ × ℕ := fun ω =>
    (equilibriumForwardCount 1 ω, equilibriumBackwardCount 0 ω)
  let indices : ℕ × ℕ → Finset ℤ := fun n =>
    ((Finset.range n.1).image fun k => Int.ofNat (k + 1)) ∪
      ((Finset.range n.2).image equilibriumBackwardArrivalIndex)
  have hstate : Measurable state := by
    exact (measurable_equilibriumForwardCount 1).prodMk
      (measurable_equilibriumBackwardCount 0)
  let selected : ((ℕ → ℝ) × (ℕ → ℝ)) → ℤ → Bool := fun ω i =>
    decide (0 ≤ equilibriumBaseArrival ω i ∧ equilibriumBaseArrival ω i < 1 ∧
      equilibriumRecenterGap i ω ∈ s)
  have hselected : Measurable selected := by
    refine measurable_pi_iff.2 fun i => ?_
    change Measurable (fun ω => if
      0 ≤ equilibriumBaseArrival ω i ∧ equilibriumBaseArrival ω i < 1 ∧
        equilibriumRecenterGap i ω ∈ s then true else false)
    have hleft : MeasurableSet {ω : (ℕ → ℝ) × (ℕ → ℝ) |
        (0 : ℝ) ≤ equilibriumBaseArrival ω i} :=
      measurableSet_le measurable_const (measurable_equilibriumBaseArrival i)
    have hright : MeasurableSet {ω : (ℕ → ℝ) × (ℕ → ℝ) |
        equilibriumBaseArrival ω i < (1 : ℝ)} :=
      measurableSet_lt (measurable_equilibriumBaseArrival i) measurable_const
    have hmark : MeasurableSet {ω : (ℕ → ℝ) × (ℕ → ℝ) |
        equilibriumRecenterGap i ω ∈ s} :=
      (measurable_equilibriumRecenterGap i) hs
    exact Measurable.ite (hleft.inter (hright.inter hmark))
      measurable_const measurable_const
  have hcount := Palm.measurable_count_from_countable_parameter state hstate indices
    selected hselected
  change Measurable (fun ω =>
    ((equilibriumHalfOpenIntervalArrivalIndices 0 1 ω).filter fun i =>
      equilibriumRecenterGap i ω ∈ s).card)
  convert hcount using 1
  funext ω
  simp only [state, indices, selected, equilibriumHalfOpenIntervalArrivalIndices,
    Finset.filter_filter, neg_zero, decide_eq_true_eq]
  congr 1
  apply Finset.filter_congr
  intro i hi
  constructor <;> intro h
  · exact ⟨h.1.1, h.1.2, h.2⟩
  · exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

/-- The nonnegative fixed-index summand of the marked unit-window count. -/
noncomputable def equilibriumMarkedUnitSummand
    (s : Set (ℤ → ℝ)) (i : ℤ) (ω : (ℕ → ℝ) × (ℕ → ℝ)) : ℝ≥0∞ := by
  classical
  exact if i ∈ equilibriumForwardArrivalIndices 1 ω ∪
      equilibriumBackwardArrivalIndices 0 ω ∧
      0 ≤ equilibriumBaseArrival ω i ∧ equilibriumBaseArrival ω i < 1 ∧
      equilibriumRecenterGap i ω ∈ s then 1 else 0

/-- Each fixed-index marked summand is measurable, again using only the two
renewal counts as a countable parameter. -/
theorem measurable_equilibriumMarkedUnitSummand
    (s : Set (ℤ → ℝ)) (hs : MeasurableSet s) (i : ℤ) :
    Measurable (equilibriumMarkedUnitSummand s i) := by
  classical
  let state : ((ℕ → ℝ) × (ℕ → ℝ)) → ℕ × ℕ := fun ω =>
    (equilibriumForwardCount 1 ω, equilibriumBackwardCount 0 ω)
  let indices : ℕ × ℕ → Finset ℤ := fun n =>
    ((Finset.range n.1).image fun k => Int.ofNat (k + 1)) ∪
      ((Finset.range n.2).image equilibriumBackwardArrivalIndex)
  have hstate : Measurable state := by
    exact (measurable_equilibriumForwardCount 1).prodMk
      (measurable_equilibriumBackwardCount 0)
  let member : ℕ × ℕ → Bool := fun n => decide (i ∈ indices n)
  have hmember : Measurable member := measurable_of_countable _
  have hmemberState : Measurable (fun ω => member (state ω)) := hmember.comp hstate
  have hmem : MeasurableSet {ω : (ℕ → ℝ) × (ℕ → ℝ) |
      i ∈ indices (state ω)} := by
    have hmemBool : MeasurableSet {ω : (ℕ → ℝ) × (ℕ → ℝ) |
        member (state ω) = true} :=
      hmemberState (MeasurableSet.singleton true)
    simpa [member] using hmemBool
  have hleft : MeasurableSet {ω : (ℕ → ℝ) × (ℕ → ℝ) |
      (0 : ℝ) ≤ equilibriumBaseArrival ω i} :=
    measurableSet_le measurable_const (measurable_equilibriumBaseArrival i)
  have hright : MeasurableSet {ω : (ℕ → ℝ) × (ℕ → ℝ) |
      equilibriumBaseArrival ω i < (1 : ℝ)} :=
    measurableSet_lt (measurable_equilibriumBaseArrival i) measurable_const
  have hmark : MeasurableSet {ω : (ℕ → ℝ) × (ℕ → ℝ) |
      equilibriumRecenterGap i ω ∈ s} :=
    (measurable_equilibriumRecenterGap i) hs
  have hbase : Measurable (fun ω => if
      i ∈ indices (state ω) ∧ 0 ≤ equilibriumBaseArrival ω i ∧
        equilibriumBaseArrival ω i < 1 ∧ equilibriumRecenterGap i ω ∈ s
      then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (hmem.inter (hleft.inter (hright.inter hmark)))
      measurable_const measurable_const
  have heq : equilibriumMarkedUnitSummand s i = fun ω => if
      i ∈ indices (state ω) ∧ 0 ≤ equilibriumBaseArrival ω i ∧
        equilibriumBaseArrival ω i < 1 ∧ equilibriumRecenterGap i ω ∈ s
      then 1 else 0 := by
    funext ω
    simp only [equilibriumMarkedUnitSummand, state, indices,
      equilibriumForwardArrivalIndices, equilibriumBackwardArrivalIndices]
    rfl
  rw [heq]
  exact hbase

/-- A pathwise finite-sum expansion of the marked unit-window count. -/
theorem equilibriumMarkedUnitWindowCount_eq_sum
    (s : Set (ℤ → ℝ)) (ω : (ℕ → ℝ) × (ℕ → ℝ)) :
    Palm.unitWindowCampbellCount equilibriumHalfOpenIntervalArrivalIndices
      (fun ω i => equilibriumRecenterGap i ω) s ω =
      (by
        classical
        exact ∑ i ∈ (equilibriumForwardArrivalIndices 1 ω ∪
          equilibriumBackwardArrivalIndices 0 ω),
          if 0 ≤ equilibriumBaseArrival ω i ∧ equilibriumBaseArrival ω i < 1 ∧
            equilibriumRecenterGap i ω ∈ s then 1 else 0) := by
  classical
  change ((equilibriumHalfOpenIntervalArrivalIndices 0 1 ω).filter fun i =>
    equilibriumRecenterGap i ω ∈ s).card = _
  simp only [equilibriumHalfOpenIntervalArrivalIndices, Finset.filter_filter,
    neg_zero]
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hp : 0 ≤ equilibriumBaseArrival ω i ∧ equilibriumBaseArrival ω i < 1
  · simp [hp]
  · have hfull : ¬(0 ≤ equilibriumBaseArrival ω i ∧ equilibriumBaseArrival ω i < 1 ∧
      equilibriumRecenterGap i ω ∈ s) := fun h => hp ⟨h.1, h.2.1⟩
    simp [hp, hfull]

/-- The finite marked count is the countable sum of fixed-index summands. -/
theorem equilibriumMarkedUnitWindowCount_coe_eq_tsum
    (s : Set (ℤ → ℝ)) (ω : (ℕ → ℝ) × (ℕ → ℝ)) :
    (Palm.unitWindowCampbellCount equilibriumHalfOpenIntervalArrivalIndices
      (fun ω i => equilibriumRecenterGap i ω) s ω : ℝ≥0∞) =
      ∑' i : ℤ, equilibriumMarkedUnitSummand s i ω := by
  classical
  rw [equilibriumMarkedUnitWindowCount_eq_sum]
  rw [tsum_eq_sum (s := equilibriumForwardArrivalIndices 1 ω ∪
    equilibriumBackwardArrivalIndices 0 ω)]
  · simp only [equilibriumMarkedUnitSummand]
    norm_cast
    apply Finset.sum_congr rfl
    intro i hi
    simp [hi]
  · intro i hi
    simp [equilibriumMarkedUnitSummand, hi]

/-- Tonelli reduces the marked unit-window Campbell integral to fixed-index
integrals for every measurable event. Identifying this sum with the tagged
Palm probability is the remaining mass-transport step. -/
theorem lintegral_equilibriumMarkedUnitWindowCount_eq_tsum
    {rate : ℝ} (s : Set (ℤ → ℝ)) (hs : MeasurableSet s) :
    ∫⁻ ω, (Palm.unitWindowCampbellCount equilibriumHalfOpenIntervalArrivalIndices
      (fun ω i => equilibriumRecenterGap i ω) s ω : ℝ≥0∞)
      ∂equilibriumTwoSidedBaseMeasure rate =
      ∑' i : ℤ, ∫⁻ ω, equilibriumMarkedUnitSummand s i ω
        ∂equilibriumTwoSidedBaseMeasure rate := by
  calc
    ∫⁻ ω, (Palm.unitWindowCampbellCount equilibriumHalfOpenIntervalArrivalIndices
        (fun ω i => equilibriumRecenterGap i ω) s ω : ℝ≥0∞)
        ∂equilibriumTwoSidedBaseMeasure rate =
        ∫⁻ ω, ∑' i : ℤ, equilibriumMarkedUnitSummand s i ω
          ∂equilibriumTwoSidedBaseMeasure rate := by
            apply MeasureTheory.lintegral_congr
            intro ω
            exact equilibriumMarkedUnitWindowCount_coe_eq_tsum s ω
    _ = ∑' i : ℤ, ∫⁻ ω, equilibriumMarkedUnitSummand s i ω
        ∂equilibriumTwoSidedBaseMeasure rate :=
      MeasureTheory.lintegral_tsum fun i =>
        (measurable_equilibriumMarkedUnitSummand s hs i).aemeasurable

end

end AppliedModelingLib.Probability.PoissonProcess
