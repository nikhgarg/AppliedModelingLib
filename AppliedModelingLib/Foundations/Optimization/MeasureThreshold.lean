import AppliedModelingLib.Foundations.Optimization.ThresholdExchange
import AppliedModelingLib.Foundations.Probability.RealDistribution
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Measure Threshold Attainment

Reusable bridge lemmas that combine real-distribution tail bracketing with
unit-interval interpolation.  These are useful for threshold-policy proofs
where boundary randomization must hit a target tail mass exactly.
-/

open MeasureTheory Set
open scoped ENNReal

namespace AppliedModelingLib
namespace Optimization

open AppliedModelingLib.Probability

noncomputable section

/-! ## Finite weighted sums of real score measures -/

/--
Finite weighted sum of score measures.

The weights are coerced through `ENNReal.ofReal`, so negative weights
contribute zero mass.  Most economic applications use the accompanying real
mass theorem under explicit nonnegative weights.
-/
def finiteWeightedMeasureSum {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (weight : ι → ℝ) (μ : ι → Measure X) : Measure X :=
  ∑ i : ι, ENNReal.ofReal (weight i) • μ i

/--
Real mass of a finite weighted sum of finite measures.

This is the measure-level analogue of distributing a finite expectation over
applicant-level score measures.
-/
theorem finiteWeightedMeasureSum_real
    {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (weight : ι → ℝ) (μ : ι → Measure X)
    [∀ i, IsFiniteMeasure (μ i)]
    (hweight : ∀ i, 0 ≤ weight i) (s : Set X) :
    (finiteWeightedMeasureSum weight μ).real s =
      ∑ i : ι, weight i * (μ i).real s := by
  classical
  letI : ∀ i, IsFiniteMeasure (ENNReal.ofReal (weight i) • μ i) :=
    fun i => Measure.smul_finite (μ i) (by simp)
  let step : Finset ι → Prop := fun I =>
    ((∑ i ∈ I, ENNReal.ofReal (weight i) • μ i) : Measure X).real s =
      ∑ i ∈ I, weight i * (μ i).real s
  have hstep : ∀ I, step I := by
    intro I
    refine Finset.induction_on I ?base ?insert
    · simp [step]
    · intro a I ha hI
      change
        ((∑ i ∈ insert a I, ENNReal.ofReal (weight i) • μ i) :
            Measure X).real s =
          ∑ i ∈ insert a I, weight i * (μ i).real s
      rw [show
          ((∑ i ∈ insert a I, ENNReal.ofReal (weight i) • μ i) :
              Measure X) =
            ENNReal.ofReal (weight a) • μ a +
              ∑ i ∈ I, ENNReal.ofReal (weight i) • μ i by
        rw [Finset.sum_insert ha]]
      rw [Finset.sum_insert ha]
      rw [measureReal_add_apply]
      rw [hI]
      simp [hweight a]
  simpa [finiteWeightedMeasureSum, step] using hstep (Finset.univ : Finset ι)

/-- Total real mass of a finite weighted sum of finite measures. -/
theorem finiteWeightedMeasureSum_real_univ
    {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (weight : ι → ℝ) (μ : ι → Measure X)
    [∀ i, IsFiniteMeasure (μ i)]
    (hweight : ∀ i, 0 ≤ weight i) :
    (finiteWeightedMeasureSum weight μ).real (Set.univ : Set X) =
      ∑ i : ι, weight i * (μ i).real (Set.univ : Set X) :=
  finiteWeightedMeasureSum_real weight μ hweight Set.univ

/-- Strict upper-tail mass of a finite weighted sum of real score measures. -/
theorem upperTailMass_finiteWeightedMeasureSum
    {ι : Type*} [Fintype ι]
    (weight : ι → ℝ) (μ : ι → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)]
    (hweight : ∀ i, 0 ≤ weight i) (t : ℝ) :
    upperTailMass (finiteWeightedMeasureSum weight μ) t =
      ∑ i : ι, weight i * upperTailMass (μ i) t := by
  simpa [upperTailMass] using
    finiteWeightedMeasureSum_real weight μ hweight (Set.Ioi t)

/-- Closed upper-tail mass of a finite weighted sum of real score measures. -/
theorem closedUpperTailMass_finiteWeightedMeasureSum
    {ι : Type*} [Fintype ι]
    (weight : ι → ℝ) (μ : ι → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)]
    (hweight : ∀ i, 0 ≤ weight i) (t : ℝ) :
    (finiteWeightedMeasureSum weight μ).real (Set.Ici t) =
      ∑ i : ι, weight i * (μ i).real (Set.Ici t) :=
  finiteWeightedMeasureSum_real weight μ hweight (Set.Ici t)

/--
Finite weighted sum of pushed-forward score measures.

This is the common score-distribution object for threshold policies: each
item has an outcome law and a real-valued score, and the aggregate measure is
the weighted sum of the score laws.
-/
def finiteWeightedScoreMeasureSum
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (weight : ι → ℝ) (law : ι → Measure Ω)
    (score : ι → Ω → ℝ) : Measure ℝ :=
  finiteWeightedMeasureSum weight (fun i => (law i).map (score i))

/-- Total real mass of a finite weighted sum of pushed-forward score laws. -/
theorem finiteWeightedScoreMeasureSum_real_univ
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (weight : ι → ℝ) (law : ι → Measure Ω)
    (score : ι → Ω → ℝ)
    [∀ i, IsFiniteMeasure (law i)]
    (hweight : ∀ i, 0 ≤ weight i) :
    (finiteWeightedScoreMeasureSum weight law score).real
        (Set.univ : Set ℝ) =
      ∑ i : ι, weight i * ((law i).map (score i)).real (Set.univ : Set ℝ) :=
  finiteWeightedMeasureSum_real_univ weight
    (fun i => (law i).map (score i)) hweight

/-- Strict upper-tail mass of a finite weighted sum of pushed-forward score laws. -/
theorem upperTailMass_finiteWeightedScoreMeasureSum
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (weight : ι → ℝ) (law : ι → Measure Ω)
    (score : ι → Ω → ℝ)
    [∀ i, IsFiniteMeasure (law i)]
    (hweight : ∀ i, 0 ≤ weight i) (t : ℝ) :
    upperTailMass (finiteWeightedScoreMeasureSum weight law score) t =
      ∑ i : ι,
        weight i * upperTailMass ((law i).map (score i)) t := by
  simpa [finiteWeightedScoreMeasureSum] using
    upperTailMass_finiteWeightedMeasureSum weight
      (fun i => (law i).map (score i)) hweight t

/-- Closed upper-tail mass of a finite weighted sum of pushed-forward score laws. -/
theorem closedUpperTailMass_finiteWeightedScoreMeasureSum
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (weight : ι → ℝ) (law : ι → Measure Ω)
    (score : ι → Ω → ℝ)
    [∀ i, IsFiniteMeasure (law i)]
    (hweight : ∀ i, 0 ≤ weight i) (t : ℝ) :
    (finiteWeightedScoreMeasureSum weight law score).real (Set.Ici t) =
      ∑ i : ι,
        weight i * ((law i).map (score i)).real (Set.Ici t) := by
  simpa [finiteWeightedScoreMeasureSum] using
    closedUpperTailMass_finiteWeightedMeasureSum weight
      (fun i => (law i).map (score i)) hweight t

/-! ## Value-weighted score measures -/

/--
The score measure weighted by a nonnegative real value function.

For a random outcome `ω`, a score `score ω`, and a nonnegative payoff
`value ω`, this pushes the measure with density `value` forward along the
score map.  Upper tails of this measure are the value accumulated by
threshold policies.
-/
def valueWeightedScoreMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (score : Ω → ℝ) (value : Ω → ℝ) : Measure ℝ :=
  (μ.withDensity fun ω => ENNReal.ofReal (value ω)).map score

theorem valueWeightedScoreMeasure_apply_Ioi
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {score : Ω → ℝ} (value : Ω → ℝ)
    (hscore : Measurable score) (t : ℝ) :
    valueWeightedScoreMeasure μ score value (Set.Ioi t) =
      ∫⁻ ω in {ω | t < score ω}, ENNReal.ofReal (value ω) ∂μ := by
  have hset : MeasurableSet {ω : Ω | t < score ω} :=
    hscore measurableSet_Ioi
  rw [valueWeightedScoreMeasure]
  rw [Measure.map_apply hscore measurableSet_Ioi]
  change
    (μ.withDensity fun ω => ENNReal.ofReal (value ω))
        {ω : Ω | t < score ω} =
      ∫⁻ ω in {ω | t < score ω}, ENNReal.ofReal (value ω) ∂μ
  rw [MeasureTheory.withDensity_apply _ hset]

theorem valueWeightedScoreMeasure_apply_Ici
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {score : Ω → ℝ} (value : Ω → ℝ)
    (hscore : Measurable score) (t : ℝ) :
    valueWeightedScoreMeasure μ score value (Set.Ici t) =
      ∫⁻ ω in {ω | t ≤ score ω}, ENNReal.ofReal (value ω) ∂μ := by
  have hset : MeasurableSet {ω : Ω | t ≤ score ω} :=
    hscore measurableSet_Ici
  rw [valueWeightedScoreMeasure]
  rw [Measure.map_apply hscore measurableSet_Ici]
  change
    (μ.withDensity fun ω => ENNReal.ofReal (value ω))
        {ω : Ω | t ≤ score ω} =
      ∫⁻ ω in {ω | t ≤ score ω}, ENNReal.ofReal (value ω) ∂μ
  rw [MeasureTheory.withDensity_apply _ hset]

theorem upperTailMass_valueWeightedScoreMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {score : Ω → ℝ} (value : Ω → ℝ)
    (hscore : Measurable score) (t : ℝ) :
    upperTailMass (valueWeightedScoreMeasure μ score value) t =
      (∫⁻ ω in {ω | t < score ω}, ENNReal.ofReal (value ω) ∂μ).toReal := by
  simp [upperTailMass, measureReal_def,
    valueWeightedScoreMeasure_apply_Ioi μ value hscore t]

theorem closedUpperTailMass_valueWeightedScoreMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {score : Ω → ℝ} (value : Ω → ℝ)
    (hscore : Measurable score) (t : ℝ) :
    (valueWeightedScoreMeasure μ score value).real (Set.Ici t) =
      (∫⁻ ω in {ω | t ≤ score ω}, ENNReal.ofReal (value ω) ∂μ).toReal := by
  simp [measureReal_def, valueWeightedScoreMeasure_apply_Ici μ value hscore t]

/--
Integral of a nonnegative value over a measurable indicator set as a real
Lebesgue integral.

This is a small bridge between Bochner integrals used for paper payoffs and
the `ENNReal` set integrals used by `withDensity` measures.
-/
theorem integral_indicator_value_eq_setLIntegral_ofReal_toReal
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {s : Set Ω} (hs : MeasurableSet s)
    {value : Ω → ℝ}
    (hvalue_int : Integrable value μ)
    (hvalue_nonneg : 0 ≤ᵐ[μ] value) :
    (∫ ω, (s.indicator value) ω ∂μ) =
      (∫⁻ ω in s, ENNReal.ofReal (value ω) ∂μ).toReal := by
  have hindicator_nonneg :
      0 ≤ᵐ[μ] fun ω => (s.indicator value) ω := by
    filter_upwards [hvalue_nonneg] with ω hω
    by_cases hmem : ω ∈ s
    · simpa [Set.indicator_of_mem hmem] using hω
    · simp [Set.indicator_of_notMem hmem]
  have hindicator_int : Integrable (s.indicator value) μ :=
    hvalue_int.indicator hs
  have hindicator_ofReal :
      (fun ω => ENNReal.ofReal ((s.indicator value) ω)) =
        s.indicator (fun ω => ENNReal.ofReal (value ω)) := by
    funext ω
    by_cases hmem : ω ∈ s
    · simp [Set.indicator_of_mem hmem]
    · simp [Set.indicator_of_notMem hmem]
  have h_ofReal :
      ENNReal.ofReal (∫ ω, (s.indicator value) ω ∂μ) =
        ∫⁻ ω in s, ENNReal.ofReal (value ω) ∂μ := by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      hindicator_int hindicator_nonneg]
    rw [hindicator_ofReal, lintegral_indicator hs]
  have h_integral_nonneg :
      0 ≤ ∫ ω, (s.indicator value) ω ∂μ :=
    MeasureTheory.integral_nonneg_of_ae hindicator_nonneg
  have h_toReal := congrArg ENNReal.toReal h_ofReal
  rwa [ENNReal.toReal_ofReal h_integral_nonneg] at h_toReal

/--
The total mass of a value-weighted score measure is the integral of the value.
-/
theorem valueWeightedScoreMeasure_real_univ_eq_integral
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {score : Ω → ℝ} (hscore : Measurable score)
    {value : Ω → ℝ}
    (hvalue_int : Integrable value μ)
    (hvalue_nonneg : 0 ≤ᵐ[μ] value) :
    (valueWeightedScoreMeasure μ score value).real (Set.univ : Set ℝ) =
      ∫ ω, value ω ∂μ := by
  calc
    (valueWeightedScoreMeasure μ score value).real (Set.univ : Set ℝ)
        =
        ((μ.withDensity fun ω => ENNReal.ofReal (value ω)).map score).real
          (Set.univ : Set ℝ) := rfl
    _ =
        (μ.withDensity fun ω => ENNReal.ofReal (value ω)).real
          (score ⁻¹' (Set.univ : Set ℝ)) := by
      rw [MeasureTheory.map_measureReal_apply hscore MeasurableSet.univ]
    _ =
        (μ.withDensity fun ω => ENNReal.ofReal (value ω)).real
          (Set.univ : Set Ω) := by
      simp
    _ =
        (∫⁻ ω in (Set.univ : Set Ω),
          ENNReal.ofReal (value ω) ∂μ).toReal := by
      rw [measureReal_def]
      rw [withDensity_apply (fun ω => ENNReal.ofReal (value ω))
        MeasurableSet.univ]
    _ =
        ∫ ω, ((Set.univ : Set Ω).indicator value) ω ∂μ := by
      exact
        (integral_indicator_value_eq_setLIntegral_ofReal_toReal
          μ MeasurableSet.univ hvalue_int hvalue_nonneg).symm
    _ = ∫ ω, value ω ∂μ := by
      simp

theorem integral_indicator_value_strictUpperTail_eq_valueWeightedScoreMeasure_real
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {score : Ω → ℝ} (hscore : Measurable score)
    {value : Ω → ℝ}
    (hvalue_int : Integrable value μ)
    (hvalue_nonneg : 0 ≤ᵐ[μ] value) (t : ℝ) :
    (∫ ω, ({ω | t < score ω}.indicator value) ω ∂μ) =
      (valueWeightedScoreMeasure μ score value).real (Set.Ioi t) := by
  have hset : MeasurableSet {ω : Ω | t < score ω} :=
    hscore measurableSet_Ioi
  rw [integral_indicator_value_eq_setLIntegral_ofReal_toReal
    μ hset hvalue_int hvalue_nonneg]
  rw [measureReal_def, valueWeightedScoreMeasure_apply_Ioi μ value hscore t]

theorem integral_indicator_value_closedUpperTail_eq_valueWeightedScoreMeasure_real
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {score : Ω → ℝ} (hscore : Measurable score)
    {value : Ω → ℝ}
    (hvalue_int : Integrable value μ)
    (hvalue_nonneg : 0 ≤ᵐ[μ] value) (t : ℝ) :
    (∫ ω, ({ω | t ≤ score ω}.indicator value) ω ∂μ) =
      (valueWeightedScoreMeasure μ score value).real (Set.Ici t) := by
  have hset : MeasurableSet {ω : Ω | t ≤ score ω} :=
    hscore measurableSet_Ici
  rw [integral_indicator_value_eq_setLIntegral_ofReal_toReal
    μ hset hvalue_int hvalue_nonneg]
  rw [measureReal_def, valueWeightedScoreMeasure_apply_Ici μ value hscore t]

theorem isFiniteMeasure_valueWeightedScoreMeasure_of_lintegral_ne_top
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (score : Ω → ℝ) (value : Ω → ℝ)
    (hfinite : (∫⁻ ω, ENNReal.ofReal (value ω) ∂μ) ≠ ∞) :
    IsFiniteMeasure (valueWeightedScoreMeasure μ score value) := by
  rw [valueWeightedScoreMeasure]
  haveI :
      IsFiniteMeasure
        (μ.withDensity fun ω => ENNReal.ofReal (value ω)) :=
    MeasureTheory.isFiniteMeasure_withDensity hfinite
  infer_instance

theorem isFiniteMeasure_valueWeightedScoreMeasure_of_hasFiniteIntegral
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (score : Ω → ℝ) (value : Ω → ℝ)
    (hfinite : HasFiniteIntegral value μ) :
    IsFiniteMeasure (valueWeightedScoreMeasure μ score value) := by
  rw [valueWeightedScoreMeasure]
  haveI :
      IsFiniteMeasure
        (μ.withDensity fun ω => ENNReal.ofReal (value ω)) :=
    MeasureTheory.isFiniteMeasure_withDensity_ofReal hfinite
  infer_instance

/--
Finite sum of value-weighted pushed-forward score measures.

This is the utility-measure analogue of `finiteWeightedScoreMeasureSum`:
each index has its own law, score, and nonnegative value density.
-/
def finiteValueWeightedScoreMeasureSum
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (law : ι → Measure Ω)
    (score : ι → Ω → ℝ) (value : ι → Ω → ℝ) : Measure ℝ :=
  finiteWeightedMeasureSum (fun _ : ι => (1 : ℝ))
    (fun i => valueWeightedScoreMeasure (law i) (score i) (value i))

/-- Total real mass of a finite sum of value-weighted score measures. -/
theorem finiteValueWeightedScoreMeasureSum_real_univ
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (law : ι → Measure Ω)
    (score : ι → Ω → ℝ) (value : ι → Ω → ℝ)
    [∀ i, IsFiniteMeasure
      (valueWeightedScoreMeasure (law i) (score i) (value i))] :
    (finiteValueWeightedScoreMeasureSum law score value).real
        (Set.univ : Set ℝ) =
      ∑ i : ι,
        (valueWeightedScoreMeasure (law i) (score i) (value i)).real
          (Set.univ : Set ℝ) := by
  simpa [finiteValueWeightedScoreMeasureSum] using
    finiteWeightedMeasureSum_real_univ
      (fun _ : ι => (1 : ℝ))
      (fun i => valueWeightedScoreMeasure (law i) (score i) (value i))
      (by intro i; norm_num)

/-- Strict upper-tail mass of a finite sum of value-weighted score measures. -/
theorem upperTailMass_finiteValueWeightedScoreMeasureSum
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (law : ι → Measure Ω)
    (score : ι → Ω → ℝ) (value : ι → Ω → ℝ)
    [∀ i, IsFiniteMeasure
      (valueWeightedScoreMeasure (law i) (score i) (value i))]
    (t : ℝ) :
    upperTailMass (finiteValueWeightedScoreMeasureSum law score value) t =
      ∑ i : ι,
        upperTailMass
          (valueWeightedScoreMeasure (law i) (score i) (value i)) t := by
  simpa [finiteValueWeightedScoreMeasureSum] using
    upperTailMass_finiteWeightedMeasureSum
      (fun _ : ι => (1 : ℝ))
      (fun i => valueWeightedScoreMeasure (law i) (score i) (value i))
      (by intro i; norm_num) t

/-- Closed upper-tail mass of a finite sum of value-weighted score measures. -/
theorem closedUpperTailMass_finiteValueWeightedScoreMeasureSum
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (law : ι → Measure Ω)
    (score : ι → Ω → ℝ) (value : ι → Ω → ℝ)
    [∀ i, IsFiniteMeasure
      (valueWeightedScoreMeasure (law i) (score i) (value i))]
    (t : ℝ) :
    (finiteValueWeightedScoreMeasureSum law score value).real (Set.Ici t) =
      ∑ i : ι,
        (valueWeightedScoreMeasure (law i) (score i) (value i)).real
          (Set.Ici t) := by
  simpa [finiteValueWeightedScoreMeasureSum] using
    closedUpperTailMass_finiteWeightedMeasureSum
      (fun _ : ι => (1 : ℝ))
      (fun i => valueWeightedScoreMeasure (law i) (score i) (value i))
      (by intro i; norm_num) t

/-! ## Score-map indicator integrals -/

/--
The integral of a strict upper-tail indicator equals the real mass of the
strict upper tail under the pushed-forward score measure.
-/
theorem integral_indicator_one_strictUpperTail_eq_map_real
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {score : Ω → ℝ} (hscore : Measurable score) (t : ℝ) :
    (∫ ω, ({ω | t < score ω}.indicator (fun _ : Ω => (1 : ℝ)) ω) ∂μ) =
      (μ.map score).real (Set.Ioi t) := by
  have hset : MeasurableSet {ω : Ω | t < score ω} :=
    hscore measurableSet_Ioi
  calc
    (∫ ω, ({ω | t < score ω}.indicator (fun _ : Ω => (1 : ℝ)) ω) ∂μ) =
        μ.real {ω : Ω | t < score ω} := by
      simpa using MeasureTheory.integral_indicator_one (μ := μ) hset
    _ = (μ.map score).real (Set.Ioi t) := by
      rw [MeasureTheory.map_measureReal_apply hscore measurableSet_Ioi]
      rfl

/--
The integral of a closed upper-tail indicator equals the real mass of the
closed upper tail under the pushed-forward score measure.
-/
theorem integral_indicator_one_closedUpperTail_eq_map_real
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {score : Ω → ℝ} (hscore : Measurable score) (t : ℝ) :
    (∫ ω, ({ω | t ≤ score ω}.indicator (fun _ : Ω => (1 : ℝ)) ω) ∂μ) =
      (μ.map score).real (Set.Ici t) := by
  have hset : MeasurableSet {ω : Ω | t ≤ score ω} :=
    hscore measurableSet_Ici
  calc
    (∫ ω, ({ω | t ≤ score ω}.indicator (fun _ : Ω => (1 : ℝ)) ω) ∂μ) =
        μ.real {ω : Ω | t ≤ score ω} := by
      simpa using MeasureTheory.integral_indicator_one (μ := μ) hset
    _ = (μ.map score).real (Set.Ici t) := by
      rw [MeasureTheory.map_measureReal_apply hscore measurableSet_Ici]
      rfl

/--
The integral of a constant strict upper-tail payoff equals the real mass of
the corresponding nonnegative scalar multiple of the pushed-forward score
measure.
-/
theorem integral_indicator_const_strictUpperTail_eq_smul_map_real
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {score : Ω → ℝ} (hscore : Measurable score)
    {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    (∫ ω, ({ω | t < score ω}.indicator (fun _ : Ω => c) ω) ∂μ) =
      (ENNReal.ofReal c • μ.map score).real (Set.Ioi t) := by
  have hset : MeasurableSet {ω : Ω | t < score ω} :=
    hscore measurableSet_Ioi
  calc
    (∫ ω, ({ω | t < score ω}.indicator (fun _ : Ω => c) ω) ∂μ) =
        μ.real {ω : Ω | t < score ω} * c := by
      simpa [smul_eq_mul] using
        MeasureTheory.integral_indicator_const (μ := μ) (e := c) hset
    _ = c * μ.real (score ⁻¹' Set.Ioi t) := by
      rw [show {ω : Ω | t < score ω} = score ⁻¹' Set.Ioi t by rfl]
      ring
    _ = (ENNReal.ofReal c • μ.map score).real (Set.Ioi t) := by
      rw [MeasureTheory.measureReal_ennreal_smul_apply]
      rw [MeasureTheory.map_measureReal_apply hscore measurableSet_Ioi]
      simp [hc]

theorem integral_indicator_const_strictUpperTail_eq_mul_map_real
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {score : Ω → ℝ} (hscore : Measurable score)
    {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    (∫ ω, ({ω | t < score ω}.indicator (fun _ : Ω => c) ω) ∂μ) =
      c * (μ.map score).real (Set.Ioi t) := by
  rw [integral_indicator_const_strictUpperTail_eq_smul_map_real
    μ hscore hc t]
  rw [MeasureTheory.measureReal_ennreal_smul_apply]
  simp [hc]

/--
The integral of a constant closed upper-tail payoff equals the real mass of
the corresponding nonnegative scalar multiple of the pushed-forward score
measure.
-/
theorem integral_indicator_const_closedUpperTail_eq_smul_map_real
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {score : Ω → ℝ} (hscore : Measurable score)
    {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    (∫ ω, ({ω | t ≤ score ω}.indicator (fun _ : Ω => c) ω) ∂μ) =
      (ENNReal.ofReal c • μ.map score).real (Set.Ici t) := by
  have hset : MeasurableSet {ω : Ω | t ≤ score ω} :=
    hscore measurableSet_Ici
  calc
    (∫ ω, ({ω | t ≤ score ω}.indicator (fun _ : Ω => c) ω) ∂μ) =
        μ.real {ω : Ω | t ≤ score ω} * c := by
      simpa [smul_eq_mul] using
        MeasureTheory.integral_indicator_const (μ := μ) (e := c) hset
    _ = c * μ.real (score ⁻¹' Set.Ici t) := by
      rw [show {ω : Ω | t ≤ score ω} = score ⁻¹' Set.Ici t by rfl]
      ring
    _ = (ENNReal.ofReal c • μ.map score).real (Set.Ici t) := by
      rw [MeasureTheory.measureReal_ennreal_smul_apply]
      rw [MeasureTheory.map_measureReal_apply hscore measurableSet_Ici]
      simp [hc]

theorem integral_indicator_const_closedUpperTail_eq_mul_map_real
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {score : Ω → ℝ} (hscore : Measurable score)
    {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    (∫ ω, ({ω | t ≤ score ω}.indicator (fun _ : Ω => c) ω) ∂μ) =
      c * (μ.map score).real (Set.Ici t) := by
  rw [integral_indicator_const_closedUpperTail_eq_smul_map_real
    μ hscore hc t]
  rw [MeasureTheory.measureReal_ennreal_smul_apply]
  simp [hc]

/--
Every target between zero and the total mass of a finite real measure is
attained by an extended upper-tail threshold and a unit boundary-randomization
coefficient.
-/
theorem exists_realThreshold_upperTailMass_interpolation_finite
    (μ : Measure ℝ) [IsFiniteMeasure μ] {target : ℝ}
    (htarget_nonneg : 0 ≤ target)
    (htarget_le_total : target ≤ μ.real (univ : Set ℝ)) :
    ∃ θ : RealThreshold,
      ∃ alpha : ℝ,
        0 ≤ alpha ∧ alpha ≤ 1 ∧
          θ.strictUpperTailMass μ +
              alpha *
                (θ.closedUpperTailMass μ -
                  θ.strictUpperTailMass μ) =
            target := by
  rcases exists_realThreshold_upperTailMass_bracket_finite
      μ htarget_nonneg htarget_le_total with
    ⟨θ, hstrict, hclosed⟩
  have hstrict_le_closed :
      θ.strictUpperTailMass μ ≤ θ.closedUpperTailMass μ :=
    hstrict.trans hclosed
  rcases exists_unit_interval_interpolation
      hstrict_le_closed hstrict hclosed with
    ⟨alpha, halpha_nonneg, halpha_le_one, halpha⟩
  exact ⟨θ, alpha, halpha_nonneg, halpha_le_one, halpha⟩

/--
Groupwise finite-measure threshold attainment: if every group target lies
between zero and its finite total mass, choose an extended threshold and
boundary-randomization coefficient for every group.
-/
theorem exists_group_realThreshold_upperTailMass_interpolation_finite
    {Group : Type*} [Fintype Group]
    (μ : Group → Measure ℝ) [∀ g, IsFiniteMeasure (μ g)]
    {target : Group → ℝ}
    (htarget_nonneg : ∀ g, 0 ≤ target g)
    (htarget_le_total :
      ∀ g, target g ≤ (μ g).real (univ : Set ℝ)) :
    ∃ θ : Group → RealThreshold,
      ∃ alpha : Group → ℝ,
        ∀ g,
          0 ≤ alpha g ∧ alpha g ≤ 1 ∧
            (θ g).strictUpperTailMass (μ g) +
                alpha g *
                  ((θ g).closedUpperTailMass (μ g) -
                    (θ g).strictUpperTailMass (μ g)) =
              target g := by
  classical
  have H :
      ∀ g : Group,
        ∃ θ : RealThreshold,
          ∃ alpha : ℝ,
            0 ≤ alpha ∧ alpha ≤ 1 ∧
              θ.strictUpperTailMass (μ g) +
                  alpha *
                    (θ.closedUpperTailMass (μ g) -
                      θ.strictUpperTailMass (μ g)) =
                target g := by
    intro g
    exact exists_realThreshold_upperTailMass_interpolation_finite
      (μ g) (htarget_nonneg g) (htarget_le_total g)
  choose θ Hθ using H
  choose alpha Halpha using Hθ
  exact ⟨θ, alpha, Halpha⟩

end

end Optimization
end AppliedModelingLib
