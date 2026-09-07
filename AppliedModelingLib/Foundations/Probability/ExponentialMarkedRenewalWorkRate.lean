import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalRenewalRate
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalRenewalCountMarginal
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalMGF
import AppliedModelingLib.Foundations.Probability.MulticlassQueueingPrimitives
import AppliedModelingLib.Foundations.Probability.PalmCampbell
import Mathlib.Tactic

/-!
# Work rate of a marked canonical exponential renewal input

This module records only an input-process law of large numbers.  A canonical
rate-`rate` exponential renewal path is paired with an independent canonical
unit-exponential work-mark path, and cumulative work means the sum of marks
whose arrival indices are strictly before the canonical renewal count at the
specified time.  It does not introduce a queue, service discipline, reset, or
stability claim.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory Filter Finset
open scoped Topology ProbabilityTheory Function NNReal

noncomputable section

/-- Total work of the arrivals counted by the canonical renewal count before
time `t`.  The half-open convention is inherited from `canonicalRenewalCount`:
an arrival at exactly `t` is included when the count construction includes it. -/
def canonicalMarkedWork
    (arrivalGaps workMarks : Nat -> Real) (t : Real) : Real :=
  (Finset.range (canonicalRenewalCount t arrivalGaps)).sum
    fun n => interarrival n workMarks

/-- Conditional on a fixed arrival path, the expected unit-exponential work
in a finite canonical renewal window is exactly its renewal count.  The
random number of summands is fixed after conditioning on `arrivalGaps`; each
mark coordinate contributes mean one. -/
theorem integral_canonicalMarkedWork_over_marks
    (arrivalGaps : Nat -> Real) (t : Real) :
    ∫ workMarks, canonicalMarkedWork arrivalGaps workMarks t
      ∂exponentialInterarrivalMeasure (1 : Real) =
      (canonicalRenewalCount t arrivalGaps : Real) := by
  unfold canonicalMarkedWork
  rw [MeasureTheory.integral_finset_sum]
  · simp_rw [integral_interarrival_eq_inv_rate (by norm_num : (0 : Real) < 1)]
    simp
  · intro n _
    exact integrable_interarrival (by norm_num : (0 : Real) < 1) n

/-- For a fixed arrival path, the finite marked renewal sum is integrable in
the independent unit-exponential mark path. -/
theorem integrable_canonicalMarkedWork_over_marks
    (arrivalGaps : Nat -> Real) (t : Real) :
    Integrable (fun workMarks => canonicalMarkedWork arrivalGaps workMarks t)
      (exponentialInterarrivalMeasure (1 : Real)) := by
  unfold canonicalMarkedWork
  refine MeasureTheory.integrable_finset_sum _ ?_
  intro n _
  exact integrable_interarrival (by norm_num : (0 : Real) < 1) n

/-- Conditional on a fixed arrival path, the finite marked renewal work has a
finite positive exponential moment below the unit mark rate. -/
theorem integrable_exp_mul_canonicalMarkedWork_over_marks
    (arrivalGaps : Nat → Real) (t tilt : Real) (htilt : tilt < 1) :
    Integrable (fun workMarks => Real.exp
      (tilt * canonicalMarkedWork arrivalGaps workMarks t))
      (exponentialInterarrivalMeasure (1 : Real)) := by
  simpa [canonicalMarkedWork] using
    integrable_exp_mul_sum_interarrival (rate := (1 : Real)) (tilt := tilt)
      (by norm_num) htilt (Finset.range (canonicalRenewalCount t arrivalGaps))

/-- Conditional on a fixed arrival path, the marked renewal sum has the
finite-sum exponential moment determined by its renewal count. -/
theorem integral_exp_mul_canonicalMarkedWork_over_marks
    (arrivalGaps : Nat → Real) (t tilt : Real) (htilt : tilt < 1) :
    ∫ workMarks, Real.exp (tilt * canonicalMarkedWork arrivalGaps workMarks t)
      ∂exponentialInterarrivalMeasure (1 : Real) =
      (1 / (1 - tilt)) ^ canonicalRenewalCount t arrivalGaps := by
  simpa only [ProbabilityTheory.mgf, canonicalMarkedWork, Finset.card_range] using
    mgf_sum_interarrival (rate := (1 : Real)) (tilt := tilt)
      (by norm_num) htilt (Finset.range (canonicalRenewalCount t arrivalGaps))

/-- The marked canonical renewal sum is Borel measurable jointly in its gap
and work-mark paths.  A countable renewal-count state selects the finite
prefix, so no measurability structure on variable finite sets is assumed. -/
theorem measurable_canonicalMarkedWork (t : Real) :
    Measurable (fun z : (Nat -> Real) × (Nat -> Real) =>
      canonicalMarkedWork z.1 z.2 t) := by
  classical
  let state : (Nat -> Real) × (Nat -> Real) -> Nat :=
    fun z => canonicalRenewalCount t z.1
  let indices : Nat -> Finset Int :=
    fun n => (Finset.range n).image Int.ofNat
  let selected : ((Nat -> Real) × (Nat -> Real)) -> Int -> Bool :=
    fun _ _ => true
  let weight : ((Nat -> Real) × (Nat -> Real)) -> Int -> Real :=
    fun z k => interarrival k.toNat z.2
  have hstate : Measurable state :=
    (measurable_canonicalRenewalCount t).comp measurable_fst
  have hselected : Measurable selected := by
    refine measurable_pi_iff.2 fun _ => measurable_const
  have hweight : Measurable weight := by
    refine measurable_pi_iff.2 fun k =>
      (measurable_interarrival k.toNat).comp measurable_snd
  have hsum := Probability.Palm.measurable_sum_from_countable_parameter
    (Ω := (Nat -> Real) × (Nat -> Real)) (κ := Nat)
    state hstate indices selected hselected weight hweight
  convert hsum using 1
  funext z
  simp only [state, indices, selected, weight]
  rw [Finset.sum_image]
  · simp [canonicalMarkedWork]
  · intro a _ b _ hab
    exact Int.ofNat.inj hab

/-- Finite-horizon marked canonical renewal work is integrable under the
actual independent gap/mark product. -/
theorem integrable_canonicalMarkedWork
    {rate t : Real} (hrate : 0 < rate) (ht : 0 ≤ t) :
    Integrable (fun z : (Nat -> Real) × (Nat -> Real) =>
      canonicalMarkedWork z.1 z.2 t)
      ((exponentialInterarrivalMeasure rate).prod
        (exponentialInterarrivalMeasure (1 : Real))) := by
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (1 : Real)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  let f : (Nat -> Real) × (Nat -> Real) -> Real :=
    fun z => canonicalMarkedWork z.1 z.2 t
  have hmeas : Measurable f := by
    simpa [f] using measurable_canonicalMarkedWork t
  refine (MeasureTheory.integrable_prod_iff hmeas.aestronglyMeasurable).2 ?_
  constructor
  · filter_upwards with gaps
    simpa [f] using integrable_canonicalMarkedWork_over_marks gaps t
  · have hnorm : (fun gaps : Nat -> Real =>
        ∫ marks, ‖f (gaps, marks)‖ ∂exponentialInterarrivalMeasure (1 : Real)) =
        fun gaps => (canonicalRenewalCount t gaps : Real) := by
      funext gaps
      have hnonneg : ∀ᵐ marks ∂exponentialInterarrivalMeasure (1 : Real),
          0 ≤ canonicalMarkedWork gaps marks t := by
        filter_upwards [ae_all_interarrival_positive (by norm_num : (0 : Real) < 1)]
          with marks hmarks
        exact Finset.sum_nonneg fun n _ => (hmarks n).le
      calc
        ∫ marks, ‖f (gaps, marks)‖ ∂exponentialInterarrivalMeasure (1 : Real) =
            ∫ marks, f (gaps, marks) ∂exponentialInterarrivalMeasure (1 : Real) := by
              refine MeasureTheory.integral_congr_ae ?_
              filter_upwards [hnonneg] with marks hmarks
              simp [f, Real.norm_eq_abs, abs_of_nonneg hmarks]
        _ = (canonicalRenewalCount t gaps : Real) := by
              simpa [f] using integral_canonicalMarkedWork_over_marks gaps t
    refine (integrable_canonicalRenewalCount hrate ht).congr ?_
    filter_upwards with gaps
    exact (congrFun hnorm gaps).symm

/-- The expected finite-horizon marked canonical renewal work is its Poisson
exposure `rate * t`.  This is a genuine product-measure calculation, not an
asymptotic replacement. -/
theorem integral_canonicalMarkedWork
    {rate t : Real} (hrate : 0 < rate) (ht : 0 ≤ t) :
    ∫ z : (Nat -> Real) × (Nat -> Real), canonicalMarkedWork z.1 z.2 t
      ∂((exponentialInterarrivalMeasure rate).prod
        (exponentialInterarrivalMeasure (1 : Real))) = rate * t := by
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (1 : Real)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  have hint := integrable_canonicalMarkedWork hrate ht
  calc
    ∫ z : (Nat -> Real) × (Nat -> Real), canonicalMarkedWork z.1 z.2 t
        ∂((exponentialInterarrivalMeasure rate).prod
          (exponentialInterarrivalMeasure (1 : Real))) =
        ∫ gaps, ∫ marks, canonicalMarkedWork gaps marks t
          ∂exponentialInterarrivalMeasure (1 : Real)
          ∂exponentialInterarrivalMeasure rate := by
            exact MeasureTheory.integral_prod _ hint
    _ = ∫ gaps, (canonicalRenewalCount t gaps : Real)
          ∂exponentialInterarrivalMeasure rate := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with gaps
            exact integral_canonicalMarkedWork_over_marks gaps t
    _ = rate * t := integral_canonicalRenewalCount hrate ht

/-- Sum of squared work marks of the arrivals counted by a canonical renewal
window.  This is an input-process reward, with no queueing interpretation. -/
def canonicalMarkedSquareWork
    (arrivalGaps workMarks : Nat → Real) (t : Real) : Real :=
  (Finset.range (canonicalRenewalCount t arrivalGaps)).sum
    fun n => (interarrival n workMarks) ^ 2

/-- Conditional on a fixed arrival path, the expected squared-mark reward in
a finite renewal window is twice its renewal count. -/
theorem integral_canonicalMarkedSquareWork_over_marks
    (arrivalGaps : Nat → Real) (t : Real) :
    ∫ workMarks, canonicalMarkedSquareWork arrivalGaps workMarks t
      ∂exponentialInterarrivalMeasure (1 : Real) =
      2 * (canonicalRenewalCount t arrivalGaps : Real) := by
  unfold canonicalMarkedSquareWork
  rw [MeasureTheory.integral_finset_sum]
  · simp_rw [integral_sq_interarrival (by norm_num : (0 : Real) < 1)]
    simp
    ring
  · intro n _
    exact integrable_sq_interarrival (by norm_num : (0 : Real) < 1) n

/-- For a fixed arrival path, the finite squared-mark renewal reward is
integrable in the independent mark path. -/
theorem integrable_canonicalMarkedSquareWork_over_marks
    (arrivalGaps : Nat → Real) (t : Real) :
    Integrable (fun workMarks => canonicalMarkedSquareWork arrivalGaps workMarks t)
      (exponentialInterarrivalMeasure (1 : Real)) := by
  unfold canonicalMarkedSquareWork
  refine MeasureTheory.integrable_finset_sum _ ?_
  intro n _
  exact integrable_sq_interarrival (by norm_num : (0 : Real) < 1) n

/-- Finite-horizon squared-mark renewal reward is jointly Borel measurable. -/
theorem measurable_canonicalMarkedSquareWork (t : Real) :
    Measurable (fun z : (Nat → Real) × (Nat → Real) =>
      canonicalMarkedSquareWork z.1 z.2 t) := by
  classical
  let state : (Nat → Real) × (Nat → Real) → Nat :=
    fun z => canonicalRenewalCount t z.1
  let indices : Nat → Finset Int :=
    fun n => (Finset.range n).image Int.ofNat
  let selected : ((Nat → Real) × (Nat → Real)) → Int → Bool :=
    fun _ _ => true
  let weight : ((Nat → Real) × (Nat → Real)) → Int → Real :=
    fun z k => (interarrival k.toNat z.2) ^ 2
  have hstate : Measurable state :=
    (measurable_canonicalRenewalCount t).comp measurable_fst
  have hselected : Measurable selected := by
    refine measurable_pi_iff.2 fun _ => measurable_const
  have hweight : Measurable weight := by
    refine measurable_pi_iff.2 fun k =>
      ((measurable_interarrival k.toNat).comp measurable_snd).pow_const 2
  have hsum := Probability.Palm.measurable_sum_from_countable_parameter
    (Ω := (Nat → Real) × (Nat → Real)) (κ := Nat)
    state hstate indices selected hselected weight hweight
  convert hsum using 1
  funext z
  simp only [state, indices, selected, weight]
  rw [Finset.sum_image]
  · simp [canonicalMarkedSquareWork]
  · intro a _ b _ hab
    exact Int.ofNat.inj hab

/-- Finite-horizon squared-mark renewal reward is integrable under the
independent arrival-and-mark product law. -/
theorem integrable_canonicalMarkedSquareWork
    {rate t : Real} (hrate : 0 < rate) (ht : 0 ≤ t) :
    Integrable (fun z : (Nat → Real) × (Nat → Real) =>
      canonicalMarkedSquareWork z.1 z.2 t)
      ((exponentialInterarrivalMeasure rate).prod
        (exponentialInterarrivalMeasure (1 : Real))) := by
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (1 : Real)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  let f : (Nat → Real) × (Nat → Real) → Real :=
    fun z => canonicalMarkedSquareWork z.1 z.2 t
  have hmeas : Measurable f := by
    simpa [f] using measurable_canonicalMarkedSquareWork t
  refine (MeasureTheory.integrable_prod_iff hmeas.aestronglyMeasurable).2 ?_
  constructor
  · filter_upwards with gaps
    simpa [f] using integrable_canonicalMarkedSquareWork_over_marks gaps t
  · have hnorm : (fun gaps : Nat → Real =>
        ∫ marks, ‖f (gaps, marks)‖ ∂exponentialInterarrivalMeasure (1 : Real)) =
        fun gaps => 2 * (canonicalRenewalCount t gaps : Real) := by
      funext gaps
      have hnonneg : ∀ᵐ marks ∂exponentialInterarrivalMeasure (1 : Real),
          0 ≤ canonicalMarkedSquareWork gaps marks t := by
        filter_upwards with marks
        exact Finset.sum_nonneg fun n _ => sq_nonneg (interarrival n marks)
      calc
        ∫ marks, ‖f (gaps, marks)‖ ∂exponentialInterarrivalMeasure (1 : Real) =
            ∫ marks, f (gaps, marks) ∂exponentialInterarrivalMeasure (1 : Real) := by
              refine MeasureTheory.integral_congr_ae ?_
              filter_upwards [hnonneg] with marks hmarks
              simp [f, Real.norm_eq_abs, abs_of_nonneg hmarks]
        _ = 2 * (canonicalRenewalCount t gaps : Real) := by
              simpa [f] using
                integral_canonicalMarkedSquareWork_over_marks gaps t
    refine ((integrable_canonicalRenewalCount hrate ht).const_mul 2).congr ?_
    filter_upwards with gaps
    exact (congrFun hnorm gaps).symm

/-- The expected squared-mark reward in a finite canonical renewal window is
twice its Poisson exposure. -/
theorem integral_canonicalMarkedSquareWork
    {rate t : Real} (hrate : 0 < rate) (ht : 0 ≤ t) :
    ∫ z : (Nat → Real) × (Nat → Real), canonicalMarkedSquareWork z.1 z.2 t
      ∂((exponentialInterarrivalMeasure rate).prod
        (exponentialInterarrivalMeasure (1 : Real))) =
      2 * rate * t := by
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (1 : Real)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  have hint := integrable_canonicalMarkedSquareWork hrate ht
  calc
    ∫ z : (Nat → Real) × (Nat → Real), canonicalMarkedSquareWork z.1 z.2 t
        ∂((exponentialInterarrivalMeasure rate).prod
          (exponentialInterarrivalMeasure (1 : Real))) =
        ∫ gaps, ∫ marks, canonicalMarkedSquareWork gaps marks t
          ∂exponentialInterarrivalMeasure (1 : Real)
          ∂exponentialInterarrivalMeasure rate := by
            exact MeasureTheory.integral_prod _ hint
    _ = ∫ gaps, 2 * (canonicalRenewalCount t gaps : Real)
          ∂exponentialInterarrivalMeasure rate := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with gaps
            exact integral_canonicalMarkedSquareWork_over_marks gaps t
    _ = 2 * rate * t := by
      rw [MeasureTheory.integral_const_mul,
        integral_canonicalRenewalCount hrate ht]
      ring

/-- A deterministic random-index composition lemma for marked renewal input.
The first hypothesis is the time-indexed renewal-count rate; the second says
that the count itself tends to infinity, and the third is the ordinary
empirical-mean law for the marks. -/
theorem tendsto_canonicalMarkedWork_div_atTop_of_tendsto
    {rate : Real} (arrivalGaps workMarks : Nat -> Real)
    (hcount : Tendsto
      (fun t : Real => (canonicalRenewalCount t arrivalGaps : Real) / t)
      atTop (nhds rate))
    (hcount_atTop : Tendsto
      (fun t : Real => canonicalRenewalCount t arrivalGaps)
      atTop atTop)
    (hmarks : Tendsto
      (fun n : Nat =>
        (Finset.range n).sum (fun i => interarrival i workMarks) / n)
      atTop (nhds 1)) :
    Tendsto
      (fun t : Real => canonicalMarkedWork arrivalGaps workMarks t / t)
      atTop (nhds rate) := by
  have hmarks_at_count : Tendsto
      (fun t : Real =>
        (Finset.range (canonicalRenewalCount t arrivalGaps)).sum
          (fun i => interarrival i workMarks) /
          (canonicalRenewalCount t arrivalGaps : Real))
      atTop (nhds 1) :=
    hmarks.comp hcount_atTop
  have hprod := hmarks_at_count.mul hcount
  have heq :
      (fun t : Real =>
        ((Finset.range (canonicalRenewalCount t arrivalGaps)).sum
          (fun i => interarrival i workMarks) /
          (canonicalRenewalCount t arrivalGaps : Real)) *
          ((canonicalRenewalCount t arrivalGaps : Real) / t)) =ᶠ[atTop]
      fun t => canonicalMarkedWork arrivalGaps workMarks t / t := by
    filter_upwards [hcount_atTop.eventually (eventually_ge_atTop 1)] with t ht
    have hcount_ne : (canonicalRenewalCount t arrivalGaps : Real) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (by omega : 0 < canonicalRenewalCount t arrivalGaps))
    simp only [canonicalMarkedWork]
    field_simp [hcount_ne]
  simpa using hprod.congr' heq

/-- If canonical arrival epochs diverge and are monotone, then their canonical
renewal count tends to infinity as real time tends to infinity. -/
theorem tendsto_canonicalRenewalCount_atTop_of_arrivalTime_tendsto
    (arrivalGaps : Nat -> Real)
    (harrival : Tendsto (fun n : Nat => arrivalTime n arrivalGaps) atTop atTop)
    (hmono : Monotone (fun n : Nat => arrivalTime n arrivalGaps)) :
    Tendsto (fun t : Real => canonicalRenewalCount t arrivalGaps) atTop atTop := by
  refine tendsto_atTop.2 fun n => ?_
  exact (eventually_ge_atTop (arrivalTime n arrivalGaps)).mono fun t ht =>
    Nat.le_of_lt
      ((lt_canonicalRenewalCount_iff_arrivalTime_le_of_tendsto arrivalGaps
        harrival hmono t n).mpr ht)

/-- The concrete product carrier of a canonical exponential renewal path and
an independent canonical unit-exponential work-mark path. -/
def exponentialMarkedRenewalWorkMeasure (rate : Real) :
    Measure ((Nat -> Real) × (Nat -> Real)) :=
  (exponentialInterarrivalMeasure rate).prod (exponentialInterarrivalMeasure 1)

/-- The marked renewal product is a probability law at positive arrival rate. -/
theorem isProbabilityMeasure_exponentialMarkedRenewalWorkMeasure
    {rate : Real} (hrate : 0 < rate) :
    IsProbabilityMeasure (exponentialMarkedRenewalWorkMeasure rate) := by
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (1 : Real)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  simpa [exponentialMarkedRenewalWorkMeasure] using
    (inferInstance : IsProbabilityMeasure
      ((exponentialInterarrivalMeasure rate).prod (exponentialInterarrivalMeasure 1)))

/-- The empirical mean of the canonical unit-exponential work-mark path
converges almost surely to one.  This is the work-mark half of the marked
renewal input, before it is evaluated at a random arrival count. -/
theorem ae_tendsto_unitExponentialWorkMark_mean :
    ∀ᵐ workMarks ∂exponentialInterarrivalMeasure (1 : Real),
      Tendsto
        (fun n : Nat =>
          (Finset.range n).sum (fun i => interarrival i workMarks) / n)
        atTop (nhds 1) := by
  have hindep : Pairwise
      ((· ⟂ᵢ[exponentialInterarrivalMeasure (1 : Real)] ·) on interarrival) := by
    intro i j hij
    exact (iIndepFun_interarrival (by norm_num : 0 < (1 : Real))).indepFun hij
  have hident : ∀ i, ProbabilityTheory.IdentDistrib (interarrival i) (interarrival 0)
      (exponentialInterarrivalMeasure (1 : Real))
      (exponentialInterarrivalMeasure (1 : Real)) :=
    fun i => (interarrival_hasLaw (by norm_num : 0 < (1 : Real)) i).identDistrib
      (interarrival_hasLaw (by norm_num : 0 < (1 : Real)) 0)
  have hmean : (exponentialInterarrivalMeasure (1 : Real))[interarrival 0] = 1 := by
    simpa using integral_interarrival_zero_eq_inv_rate (rate := (1 : Real))
      (by norm_num)
  simpa [hmean] using
    (ProbabilityTheory.strong_law_ae_real interarrival
      (integrable_interarrival_zero (by norm_num : 0 < (1 : Real))) hindep hident)

/-- Combine the four source-input almost-sure facts needed for the marked
work-rate law.  This deliberately has no independence premise: independence
is used to construct the source carrier, while the conclusion only needs the
two verified marginal full-measure facts simultaneously. -/
theorem ae_tendsto_canonicalMarkedWork_div_atTop_of_ae_inputs
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} {rate : Real}
    (arrivalGaps workMarks : Omega -> Nat -> Real)
    (hcount : ∀ᵐ omega ∂P,
      Tendsto
        (fun t : Real => (canonicalRenewalCount t (arrivalGaps omega) : Real) / t)
        atTop (nhds rate))
    (harrival : ∀ᵐ omega ∂P,
      Tendsto (fun n : Nat => arrivalTime n (arrivalGaps omega)) atTop atTop)
    (hmono : ∀ᵐ omega ∂P,
      Monotone (fun n : Nat => arrivalTime n (arrivalGaps omega)))
    (hmarks : ∀ᵐ omega ∂P,
      Tendsto
        (fun n : Nat =>
          (Finset.range n).sum (fun i => interarrival i (workMarks omega)) / n)
        atTop (nhds 1)) :
    ∀ᵐ omega ∂P,
      Tendsto
        (fun t : Real =>
          canonicalMarkedWork (arrivalGaps omega) (workMarks omega) t / t)
        atTop (nhds rate) := by
  filter_upwards [hcount, harrival, hmono, hmarks]
    with omega hcount harrival hmono hmarks
  exact tendsto_canonicalMarkedWork_div_atTop_of_tendsto
    (arrivalGaps omega) (workMarks omega) hcount
    (tendsto_canonicalRenewalCount_atTop_of_arrivalTime_tendsto
      (arrivalGaps omega) harrival hmono)
    hmarks

/-- Transport the marked work-rate law through separately measure-preserving
arrival and work-mark coordinates.  This applies directly to source carriers
that expose the actual arrival and work paths as marginal factors. -/
theorem ae_tendsto_canonicalMarkedWork_div_atTop_of_marginal_measurePreserving
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} {rate : Real}
    (hrate : 0 < rate) (arrivalGaps workMarks : Omega -> Nat -> Real)
    (harrivalMeasure : MeasurePreserving arrivalGaps P
      (exponentialInterarrivalMeasure rate))
    (hworkMeasure : MeasurePreserving workMarks P
      (exponentialInterarrivalMeasure 1)) :
    ∀ᵐ omega ∂P,
      Tendsto
        (fun t : Real =>
          canonicalMarkedWork (arrivalGaps omega) (workMarks omega) t / t)
        atTop (nhds rate) := by
  have harrivalInput : ∀ᵐ arrivalGaps ∂exponentialInterarrivalMeasure rate,
      Tendsto
          (fun t : Real => (canonicalRenewalCount t arrivalGaps : Real) / t)
          atTop (nhds rate) ∧
        Tendsto (fun n : Nat => arrivalTime n arrivalGaps) atTop atTop ∧
        Monotone (fun n : Nat => arrivalTime n arrivalGaps) :=
    (ae_tendsto_canonicalRenewalCount_div_atTop hrate).and
      ((ae_arrivalTime_tendsto_atTop hrate).and (ae_arrivalTime_monotone hrate))
  have harrivalLift : ∀ᵐ omega ∂P,
      Tendsto
          (fun t : Real =>
            (canonicalRenewalCount t (arrivalGaps omega) : Real) / t)
          atTop (nhds rate) ∧
        Tendsto (fun n : Nat => arrivalTime n (arrivalGaps omega)) atTop atTop ∧
        Monotone (fun n : Nat => arrivalTime n (arrivalGaps omega)) := by
    refine ae_of_ae_map (μ := P) (f := arrivalGaps)
      (p := fun arrivalGaps : Nat -> Real =>
        Tendsto
            (fun t : Real => (canonicalRenewalCount t arrivalGaps : Real) / t)
            atTop (nhds rate) ∧
          Tendsto (fun n : Nat => arrivalTime n arrivalGaps) atTop atTop ∧
          Monotone (fun n : Nat => arrivalTime n arrivalGaps))
      harrivalMeasure.measurable.aemeasurable ?_
    rw [harrivalMeasure.map_eq]
    exact harrivalInput
  have hworkLift : ∀ᵐ omega ∂P,
      Tendsto
        (fun n : Nat =>
          (Finset.range n).sum (fun i => interarrival i (workMarks omega)) / n)
        atTop (nhds 1) := by
    refine ae_of_ae_map (μ := P) (f := workMarks)
      (p := fun workMarks : Nat -> Real =>
        Tendsto
          (fun n : Nat =>
            (Finset.range n).sum (fun i => interarrival i workMarks) / n)
          atTop (nhds 1))
      hworkMeasure.measurable.aemeasurable ?_
    rw [hworkMeasure.map_eq]
    exact ae_tendsto_unitExponentialWorkMark_mean
  filter_upwards [harrivalLift, hworkLift]
    with omega harrival hwork
  exact tendsto_canonicalMarkedWork_div_atTop_of_tendsto
    (arrivalGaps omega) (workMarks omega) harrival.1
    (tendsto_canonicalRenewalCount_atTop_of_arrivalTime_tendsto
      (arrivalGaps omega) harrival.2.1 harrival.2.2)
    hwork

/-- On the explicit independent product of a rate-`rate` canonical arrival
path and iid unit-exponential work marks, marked cumulative input work has
almost-sure long-run rate `rate`.  This is only a primitive input law. -/
theorem ae_tendsto_canonicalMarkedWork_div_atTop
    {rate : Real} (hrate : 0 < rate) :
    ∀ᵐ omega ∂exponentialMarkedRenewalWorkMeasure rate,
      Tendsto
        (fun t : Real => canonicalMarkedWork omega.1 omega.2 t / t)
        atTop (nhds rate) := by
  let μa : Measure (Nat -> Real) := exponentialInterarrivalMeasure rate
  let μw : Measure (Nat -> Real) := exponentialInterarrivalMeasure 1
  letI : IsProbabilityMeasure μa :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure μw :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  change ∀ᵐ omega : (Nat -> Real) × (Nat -> Real) ∂μa.prod μw,
    Tendsto
      (fun t : Real => canonicalMarkedWork omega.1 omega.2 t / t)
      atTop (nhds rate)
  exact ae_tendsto_canonicalMarkedWork_div_atTop_of_marginal_measurePreserving
    hrate Prod.fst Prod.snd measurePreserving_fst measurePreserving_snd

variable {Class : Type*} [Fintype Class]

/-- The actual arrival/work coordinates of one class in the reusable finite
class primitive carrier have their marked-work rate.  The theorem uses those
same source coordinates, not an independently substituted Poisson process. -/
theorem ae_tendsto_multiclassPrimitiveMarkedWork_div_atTop
    (arrivalRate : Class -> Real) (harrivalRate : ∀ i, 0 < arrivalRate i)
    (admissionProbability : Class -> ℝ≥0)
    (hadmissionProbability : ∀ i, admissionProbability i ≤ 1) (i : Class) :
    ∀ᵐ omega ∂multiclassForwardQueueingPrimitiveMeasure arrivalRate
      admissionProbability hadmissionProbability,
      Tendsto
        (fun t : Real =>
          canonicalMarkedWork
            (multiclassForwardQueueingPrimitiveRawInterarrivals i omega)
            (multiclassForwardQueueingPrimitiveWorkMarks i omega) t / t)
        atTop (nhds (arrivalRate i)) := by
  exact ae_tendsto_canonicalMarkedWork_div_atTop_of_marginal_measurePreserving
    (harrivalRate i)
    (multiclassForwardQueueingPrimitiveRawInterarrivals i)
    (multiclassForwardQueueingPrimitiveWorkMarks i)
    (measurePreserving_multiclassPrimitiveRawInterarrivals arrivalRate harrivalRate
      admissionProbability hadmissionProbability i)
    (measurePreserving_multiclassPrimitiveWorkMarks arrivalRate harrivalRate
      admissionProbability hadmissionProbability i)

end

end AppliedModelingLib.Probability.PoissonProcess
