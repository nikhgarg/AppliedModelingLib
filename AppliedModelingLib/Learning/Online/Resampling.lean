import AppliedModelingLib.Foundations.Probability.UniformHoeffding
import AppliedModelingLib.Foundations.Probability.IndependentProduct
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.PAC
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.AdaptiveQueryInvariants
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic

/-!
# Finite resampling concentration

This module records the concentration step behind finite `k`-fold resampling
reductions.  A randomized learner exposes a PMF over bounded functions; the
downstream procedure uses the empirical mean of `k` independent draws.  The
result below compares that empirical predictor directly with its PMF mean.
-/

open scoped BigOperators ProbabilityTheory NNReal

namespace AppliedModelingLib.Learning.Online

open AppliedModelingLib
open AppliedModelingLib.PreferenceRL
open MeasureTheory ProbabilityTheory

/-- The empirical average of a finite resampling batch. -/
noncomputable def resamplingSampleAverage {Index Sample : Type*} [Fintype Index]
    (sample : Index → Sample) (score : Sample → ℝ) : ℝ :=
  (∑ index, score (sample index)) / (Fintype.card Index : ℝ)

/-- The function-valued uniform average represented by one finite resampling
batch.  Unlike a PMF expectation, this is a literal combination of the
`Fintype.card Index` sampled proper objects. -/
noncomputable def resamplingBatchAverage {Index Sample Value : Type*} [Fintype Index]
    [AddCommGroup Value] [Module ℝ Value]
    (sample : Index → Sample) (value : Sample → Value) : Value :=
  (Fintype.card Index : ℝ)⁻¹ • ∑ index, value (sample index)

/-- A point is represented by a convex combination with at most `count`
listed atoms.  Repeated atoms and zero coefficients are permitted, so this is
the convenient exact formal reading of the customary notation `conv_count`.
The finite list is retained instead of only asserting convex-hull membership;
algorithms using resampling need its support-size information. -/
def IsKConvexCombination {Atom Value : Type*} [AddCommMonoid Value] [Module ℝ Value]
    (count : ℕ) (value : Atom → Value) (point : Value) : Prop :=
  ∃ atoms : Fin count → Atom, ∃ weights : Fin count → ℝ,
    (∀ index, 0 ≤ weights index) ∧ (∑ index, weights index) = 1 ∧
      point = ∑ index, weights index • value (atoms index)

/-- A nonempty `k`-draw resampling batch is an explicit `k`-term convex
combination of the proper objects it drew.  This strengthens the usual
convex-hull conclusion by retaining the representation size used in
resampling-based proper-learning results. -/
theorem resamplingBatchAverage_isKConvexCombination
    {Sample Value : Type*} [AddCommGroup Value] [Module ℝ Value]
    {sampleCount : ℕ} (sampleCountPositive : 0 < sampleCount)
    (sample : Fin sampleCount → Sample) (value : Sample → Value) :
    IsKConvexCombination sampleCount value (resamplingBatchAverage sample value) := by
  refine ⟨sample, (fun _ => (sampleCount : ℝ)⁻¹), ?_, ?_, ?_⟩
  · intro index
    exact inv_nonneg.mpr (Nat.cast_nonneg sampleCount)
  · have hpositive : 0 < (sampleCount : ℝ) := by exact_mod_cast sampleCountPositive
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]
    exact mul_inv_cancel₀ hpositive.ne'
  · unfold resamplingBatchAverage
    simp only [Fintype.card_fin]
    rw [Finset.smul_sum]

/-- The function-valued batch average is the center of mass of its sampled
objects with equal weights. -/
theorem resamplingBatchAverage_eq_centerMass
    {Index Sample Value : Type*} [Fintype Index] [AddCommGroup Value] [Module ℝ Value]
    (sample : Index → Sample) (value : Sample → Value) :
    resamplingBatchAverage sample value =
      (Finset.univ : Finset Index).centerMass (fun _ => (1 : ℝ))
        (fun index => value (sample index)) := by
  simp [resamplingBatchAverage, Finset.centerMass]

/-- A nonempty resampling batch is a convex combination of the functions it
actually drew.  This is the representation bridge used when a resampled
proper learner is advertised as returning an element of `conv_k(C)`. -/
theorem resamplingBatchAverage_mem_convexHull
    {Index Sample Value : Type*} [Fintype Index] [AddCommGroup Value] [Module ℝ Value]
    (indexPositive : 0 < Fintype.card Index)
    (sample : Index → Sample) (value : Sample → Value) :
    resamplingBatchAverage sample value ∈ convexHull ℝ (Set.range value) := by
  rw [resamplingBatchAverage_eq_centerMass]
  apply Finset.centerMass_mem_convexHull
  · intro index _
    positivity
  · simpa using (show 0 < (Fintype.card Index : ℝ) by exact_mod_cast indexPositive)
  · intro index _
    exact ⟨sample index, rfl⟩

/-- For scalar scores, the function-valued and scalar batch averages agree. -/
theorem resamplingBatchAverage_eq_resamplingSampleAverage
    {Index Sample : Type*} [Fintype Index]
    (sample : Index → Sample) (score : Sample → ℝ) :
    resamplingBatchAverage sample score = resamplingSampleAverage sample score := by
  unfold resamplingBatchAverage resamplingSampleAverage
  rw [div_eq_inv_mul]
  simp only [smul_eq_mul]

/-- An empirical average remains in every interval that contains each sampled
score.  This deterministic fact is used both by resampling concentration and
by downstream adaptive procedures that consume a fresh batch average. -/
theorem resamplingSampleAverage_mem_Icc
    {Index Sample : Type*} [Fintype Index] (hindex : 0 < Fintype.card Index)
    (sample : Index → Sample) (score : Sample → ℝ) (lower upper : ℝ)
    (hscore : ∀ index, score (sample index) ∈ Set.Icc lower upper) :
    resamplingSampleAverage sample score ∈ Set.Icc lower upper := by
  unfold resamplingSampleAverage
  have hcard : 0 < (Fintype.card Index : ℝ) := by exact_mod_cast hindex
  constructor
  · apply (le_div_iff₀ hcard).2
    calc
      lower * (Fintype.card Index : ℝ) = ∑ _ : Index, lower := by simp [mul_comm]
      _ ≤ ∑ index, score (sample index) := by
        apply Finset.sum_le_sum
        intro index _
        exact (hscore index).1
  · apply (div_le_iff₀ hcard).2
    calc
      ∑ index, score (sample index) ≤ ∑ _ : Index, upper := by
        apply Finset.sum_le_sum
        intro index _
        exact (hscore index).2
      _ = upper * (Fintype.card Index : ℝ) := by simp [mul_comm]

/-- A nonempty function-valued resampling batch, evaluated at one coordinate,
stays in every interval containing every sampled coordinate value. -/
theorem resamplingBatchAverage_mem_Icc
    {Index Sample : Type*} [Fintype Index] (hindex : 0 < Fintype.card Index)
    (sample : Index → Sample) (score : Sample → ℝ) (lower upper : ℝ)
    (hscore : ∀ index, score (sample index) ∈ Set.Icc lower upper) :
    resamplingBatchAverage sample score ∈ Set.Icc lower upper := by
  rw [resamplingBatchAverage_eq_resamplingSampleAverage]
  exact resamplingSampleAverage_mem_Icc hindex sample score lower upper hscore

/-- The fixed-path simultaneous-move OWAL comparison.  The learner exposes a
PMF over predictors at each round, and the right side is its exact expected
correlation with the revealed context-label path. -/
def finiteRandomizedWeakAgnosticGuarantee
    {Context Sample : Type*} [Fintype Sample] [DecidableEq Sample] {roundCount : ℕ}
    (comparators : Set (Context → ℝ)) (laws : Fin roundCount → PMF Sample)
    (predictor : Sample → Context → ℝ) (contexts : Fin roundCount → Context)
    (labels : Fin roundCount → ℝ) (regret : ℝ) : Prop :=
  ∀ comparator ∈ comparators,
    (∑ round, comparator (contexts round) * labels round) ≤
      (∑ round, pmfExp (laws round)
        (fun sample => predictor sample (contexts round)) * labels round) + regret

/-- The delayed-label version of the same fixed-path OWAL comparison after a
batch average replaces each randomized prediction. -/
def finiteResampledWeakAgnosticGuarantee
    {Context Sample : Type*} {roundCount sampleCount : ℕ}
    (comparators : Set (Context → ℝ)) (batches : Fin roundCount → Fin sampleCount → Sample)
    (predictor : Sample → Context → ℝ) (contexts : Fin roundCount → Context)
    (labels : Fin roundCount → ℝ) (regret : ℝ) : Prop :=
  ∀ comparator ∈ comparators,
    (∑ round, comparator (contexts round) * labels round) ≤
      (∑ round,
        resamplingSampleAverage (batches round)
          (fun sample => predictor sample (contexts round)) * labels round) + regret

/-- A finite iid resampling batch concentrates around its exact PMF mean.
The bound is one-sided because the delayed-label-to-simultaneous-move
reduction only needs an upper comparison; applying the theorem to `-score`
gives the matching lower tail. -/
theorem pmfProb_resamplingSampleAverage_sub_expectation_ge_le
    {Sample : Type*} [Fintype Sample] [DecidableEq Sample]
    [MeasurableSpace Sample] [DiscreteMeasurableSpace Sample]
    {sampleCount : ℕ} (sampleCountPositive : 0 < sampleCount)
    (law : PMF Sample) (score : Sample → ℝ)
    (hscore : ∀ item, score item ∈ Set.Icc (-1 : ℝ) 1)
    (error : ℝ) (herror : 0 ≤ error) :
    pmfProb (pmfProduct (Fin sampleCount) Sample law)
      (fun sample => error ≤ resamplingSampleAverage sample score - pmfExp law score) ≤
      Real.exp (-(sampleCount : ℝ) * error ^ 2 / 2) := by
  let productLaw := pmfProduct (Fin sampleCount) Sample law
  let observation : Fin sampleCount → (Fin sampleCount → Sample) → ℝ :=
    fun index sample => (score (sample index) + 1) / 2
  have hcountPositive : 0 < (sampleCount : ℝ) := by exact_mod_cast sampleCountPositive
  have hmean : ∀ index : Fin sampleCount,
      productLaw.toMeasure[observation index] = (pmfExp law score + 1) / 2 := by
    intro index
    dsimp [productLaw, observation]
    rw [← pmfExp_eq_integral_toMeasure]
    calc
      pmfExp (pmfProduct (Fin sampleCount) Sample law)
          (fun sample => (score (sample index) + 1) / 2) =
          pmfExp law (fun item => (score item + 1) / 2) := by
            change pmfExp (pmfProduct (Fin sampleCount) Sample law)
              (fun sample => (fun item => (score item + 1) / 2) (sample index)) = _
            exact pmfExp_pmfProduct_eval law index (fun item => (score item + 1) / 2)
      _ = pmfExp law (fun item => (1 / 2) * score item + 1 / 2) := by
            congr 1
            funext item
            ring
      _ = (1 / 2) * pmfExp law score + 1 / 2 := by
            rw [pmfExp_add, pmfExp_const_mul, pmfExp_const]
      _ = (pmfExp law score + 1) / 2 := by ring
  have hindependent : iIndepFun observation productLaw.toMeasure := by
    simpa [productLaw, observation, Function.comp_def] using
      (iIndepFun_pmfProduct_eval law).comp
        (fun _ item => (score item + 1) / 2)
        (fun _ => measurable_of_finite _)
  have hmeasurable : ∀ index, Measurable (observation index) := by
    intro index
    exact measurable_of_finite _
  have hbounded : ∀ index, ∀ᵐ sample ∂productLaw.toMeasure,
      observation index sample ∈ Set.Icc (0 : ℝ) 1 := by
    intro index
    filter_upwards [] with sample
    dsimp [observation]
    have hvalue := hscore (sample index)
    constructor <;> linarith [hvalue.1, hvalue.2]
  have hsum : ∀ sample : Fin sampleCount → Sample,
      (∑ index, (observation index sample - productLaw.toMeasure[observation index])) =
        ((∑ index, score (sample index)) - (sampleCount : ℝ) * pmfExp law score) / 2 := by
    intro sample
    calc
      (∑ index, (observation index sample - productLaw.toMeasure[observation index])) =
          ∑ index, (score (sample index) - pmfExp law score) / 2 := by
            apply Finset.sum_congr rfl
            intro index _
            rw [hmean index]
            dsimp [observation]
            ring
      _ = ((∑ index, score (sample index)) -
          (sampleCount : ℝ) * pmfExp law score) / 2 := by
            rw [← Finset.sum_div]
            rw [Finset.sum_sub_distrib]
            simp
  have hevent : {sample | error ≤ resamplingSampleAverage sample score - pmfExp law score} =
      {sample | (sampleCount : ℝ) * error / 2 ≤
        ∑ index, (observation index sample - productLaw.toMeasure[observation index])} := by
    ext sample
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hsum]
    unfold resamplingSampleAverage
    simp only [Fintype.card_fin]
    have haverage :
        (∑ index, score (sample index)) / (sampleCount : ℝ) - pmfExp law score =
          ((∑ index, score (sample index)) -
            (sampleCount : ℝ) * pmfExp law score) / (sampleCount : ℝ) := by
      field_simp [hcountPositive.ne']
    rw [haverage]
    constructor
    · intro h
      have hscaled := (le_div_iff₀ hcountPositive).mp h
      nlinarith
    · intro h
      apply (le_div_iff₀ hcountPositive).2
      nlinarith
  rw [pmfProb_eq_toMeasure_real, hevent]
  have htail := Probability.boundedIIndep_centeredSum_upperTail_finset
    productLaw.toMeasure observation hindependent hmeasurable hbounded
    ((sampleCount : ℝ) * error / 2) (by positivity)
  calc
    productLaw.toMeasure.real
      {sample | (sampleCount : ℝ) * error / 2 ≤
        ∑ index, (observation index sample - productLaw.toMeasure[observation index])} ≤
        Real.exp (-((sampleCount : ℝ) * error / 2) ^ 2 /
          (2 * (Fintype.card (Fin sampleCount) : ℝ) * (1 / 4 : ℝ))) := htail
    _ = Real.exp (-(sampleCount : ℝ) * error ^ 2 / 2) := by
      congr 1
      simp
      field_simp [hcountPositive.ne']
      ring

/-- Negating the score negates the corresponding resampling average. -/
theorem resamplingSampleAverage_neg {Index Sample : Type*} [Fintype Index]
    (sample : Index → Sample) (score : Sample → ℝ) :
    resamplingSampleAverage sample (fun item => -score item) =
      -resamplingSampleAverage sample score := by
  unfold resamplingSampleAverage
  rw [Finset.sum_neg_distrib]
  ring

/-- The matching lower tail for a finite iid resampling batch. -/
theorem pmfProb_resamplingSampleAverage_lowerDeviation_ge_le
    {Sample : Type*} [Fintype Sample] [DecidableEq Sample]
    [MeasurableSpace Sample] [DiscreteMeasurableSpace Sample]
    {sampleCount : ℕ} (sampleCountPositive : 0 < sampleCount)
    (law : PMF Sample) (score : Sample → ℝ)
    (hscore : ∀ item, score item ∈ Set.Icc (-1 : ℝ) 1)
    (error : ℝ) (herror : 0 ≤ error) :
    pmfProb (pmfProduct (Fin sampleCount) Sample law)
      (fun sample => error ≤
        -(resamplingSampleAverage sample score - pmfExp law score)) ≤
      Real.exp (-(sampleCount : ℝ) * error ^ 2 / 2) := by
  have hnegScore : ∀ item, (fun item => -score item) item ∈ Set.Icc (-1 : ℝ) 1 := by
    intro item
    have hitem := hscore item
    constructor <;> linarith [hitem.1, hitem.2]
  calc
    pmfProb (pmfProduct (Fin sampleCount) Sample law)
      (fun sample => error ≤
        -(resamplingSampleAverage sample score - pmfExp law score)) =
        pmfProb (pmfProduct (Fin sampleCount) Sample law)
          (fun sample => error ≤
            resamplingSampleAverage sample (fun item => -score item) -
              pmfExp law (fun item => -score item)) := by
          apply pmfProb_congr
          intro sample
          rw [resamplingSampleAverage_neg, pmfExp_neg]
          ring_nf
    _ ≤ Real.exp (-(sampleCount : ℝ) * error ^ 2 / 2) :=
      pmfProb_resamplingSampleAverage_sub_expectation_ge_le sampleCountPositive
        law (fun item => -score item) hnegScore error herror

/-- A two-sided finite-resampling deviation bound.  This form is needed when
the resampling error is subsequently multiplied by a signed payoff. -/
theorem pmfProb_resamplingSampleAverage_abs_sub_expectation_ge_le
    {Sample : Type*} [Fintype Sample] [DecidableEq Sample]
    [MeasurableSpace Sample] [DiscreteMeasurableSpace Sample]
    {sampleCount : ℕ} (sampleCountPositive : 0 < sampleCount)
    (law : PMF Sample) (score : Sample → ℝ)
    (hscore : ∀ item, score item ∈ Set.Icc (-1 : ℝ) 1)
    (error : ℝ) (herror : 0 ≤ error) :
    pmfProb (pmfProduct (Fin sampleCount) Sample law)
      (fun sample => error ≤
        |resamplingSampleAverage sample score - pmfExp law score|) ≤
      2 * Real.exp (-(sampleCount : ℝ) * error ^ 2 / 2) := by
  calc
    pmfProb (pmfProduct (Fin sampleCount) Sample law)
      (fun sample => error ≤
        |resamplingSampleAverage sample score - pmfExp law score|) =
        pmfProb (pmfProduct (Fin sampleCount) Sample law)
          (fun sample => ∃ direction : Bool,
            if direction then
              error ≤ resamplingSampleAverage sample score - pmfExp law score
            else error ≤
              -(resamplingSampleAverage sample score - pmfExp law score)) := by
          apply pmfProb_congr
          intro sample
          rw [le_abs]
          constructor
          · intro h
            rcases h with hupper | hlower
            · exact ⟨true, hupper⟩
            · exact ⟨false, hlower⟩
          · rintro ⟨direction, h⟩
            cases direction <;> simp at h
            · exact Or.inr (by linarith)
            · exact Or.inl h
    _ ≤ (Fintype.card Bool : ℝ) *
        Real.exp (-(sampleCount : ℝ) * error ^ 2 / 2) := by
          apply pmfProb_exists_le_card_mul
          intro direction
          cases direction
          · simpa using
              (pmfProb_resamplingSampleAverage_lowerDeviation_ge_le
                sampleCountPositive law score hscore error herror)
          · simpa using
              (pmfProb_resamplingSampleAverage_sub_expectation_ge_le
                sampleCountPositive law score hscore error herror)
    _ = 2 * Real.exp (-(sampleCount : ℝ) * error ^ 2 / 2) := by norm_num

/--
Two-sided resampling concentration also holds when the bounded score is
chosen by an independent finite probe.  The batch is still iid conditional on
each probe value, so this is obtained by swapping the two finite expectations
rather than by a union bound over the probe space.

This is the appropriate finite interface for a delayed-label execution: a
learner can first draw a resampling batch, run arbitrary batch-dependent
postprocessing, and then evaluate that batch at one fresh independent datum.
-/
theorem pmfPairExp_resamplingSampleAverage_abs_sub_expectation_le
    {Sample Probe : Type*} [Fintype Sample] [DecidableEq Sample]
    [MeasurableSpace Sample] [DiscreteMeasurableSpace Sample]
    [Fintype Probe] [DecidableEq Probe]
    {sampleCount : ℕ} (sampleCountPositive : 0 < sampleCount)
    (law : PMF Sample) (probeLaw : PMF Probe) (score : Probe → Sample → ℝ)
    (hscore : ∀ probe item, score probe item ∈ Set.Icc (-1 : ℝ) 1)
    (error : ℝ) (herror : 0 ≤ error) :
    pmfPairExp (pmfProduct (Fin sampleCount) Sample law) probeLaw
      (fun batch probe => if error ≤
        |resamplingSampleAverage batch (score probe) - pmfExp law (score probe)|
        then (1 : ℝ) else 0) ≤
      2 * Real.exp (-(sampleCount : ℝ) * error ^ 2 / 2) := by
  rw [pmfPairExp_swap]
  apply pmfPairExp_le_of_forall_right
  intro probe
  simpa [pmfProb] using
    (pmfProb_resamplingSampleAverage_abs_sub_expectation_ge_le
      sampleCountPositive law (score probe) (hscore probe) error herror)

/-- Two-sided resampling concentration remains valid when the current law
and score are selected from the complete preceding adaptive state.  The
fresh batch is conditionally iid at each round; no independence between
rounds is assumed. -/
theorem adaptiveQuerySuccessProbability_twoSidedResampling_ge_one_sub_sum
    {State Sample : Type*} [Fintype State] [DecidableEq State]
    [Fintype Sample] [DecidableEq Sample]
    [MeasurableSpace Sample] [DiscreteMeasurableSpace Sample]
    {sampleCount : ℕ} (sampleCountPositive : 0 < sampleCount)
    (initialStateLaw : PMF State) (advance : AdaptiveStateUpdate State (Fin sampleCount → Sample))
    (laws : ℕ → State → PMF Sample) (scores : ℕ → State → Sample → ℝ)
    (hscores : ∀ queryIndex state item,
      scores queryIndex state item ∈ Set.Icc (-1 : ℝ) 1)
    (error : ℝ) (herror : 0 ≤ error) :
    ∀ queryCount,
      1 - ∑ queryIndex ∈ Finset.range queryCount,
        2 * Real.exp (-(sampleCount : ℝ) * error ^ 2 / 2) ≤
        pmfProb
          (adaptiveQueryStateLaw initialStateLaw
            (fun queryIndex state =>
              pmfProduct (Fin sampleCount) Sample (laws queryIndex state))
            advance
            (fun queryIndex state samples => error ≤
              |resamplingSampleAverage samples (scores queryIndex state) -
                pmfExp (laws queryIndex state) (scores queryIndex state)|)
            queryCount)
          (fun stateFailure => stateFailure.2 = false) := by
  intro queryCount
  apply adaptiveQuerySuccessProbability_ge_one_sub_sum_of_support
    initialStateLaw
    (fun queryIndex state =>
      pmfProduct (Fin sampleCount) Sample (laws queryIndex state))
    advance
    (fun queryIndex state samples => error ≤
      |resamplingSampleAverage samples (scores queryIndex state) -
        pmfExp (laws queryIndex state) (scores queryIndex state)|)
    (fun _ => 2 * Real.exp (-(sampleCount : ℝ) * error ^ 2 / 2))
  intro queryIndex stateFailure _
  exact pmfProb_resamplingSampleAverage_abs_sub_expectation_ge_le
    sampleCountPositive (laws queryIndex stateFailure.1) (scores queryIndex stateFailure.1)
    (hscores queryIndex stateFailure.1) error herror

/-- On a realized two-sided resampling event, replacing every conditional PMF
mean by the empirical batch average changes its signed cumulative correlation
by at most `roundCount * error`. -/
theorem resamplingSignedCorrelationError_le
    {Sample : Type*} [Fintype Sample] [DecidableEq Sample]
    {roundCount sampleCount : ℕ}
    (batches : Fin roundCount → Fin sampleCount → Sample)
    (laws : Fin roundCount → PMF Sample) (scores : Fin roundCount → Sample → ℝ)
    (labels : Fin roundCount → ℝ) (hlabels : ∀ round, |labels round| ≤ 1)
    (error : ℝ) (herror : 0 ≤ error)
    (hgood : ∀ round,
      |resamplingSampleAverage (batches round) (scores round) -
        pmfExp (laws round) (scores round)| ≤ error) :
    (∑ round,
      (resamplingSampleAverage (batches round) (scores round) -
        pmfExp (laws round) (scores round)) * labels round) ≤
      (roundCount : ℝ) * error := by
  calc
    (∑ round,
      (resamplingSampleAverage (batches round) (scores round) -
        pmfExp (laws round) (scores round)) * labels round) ≤
        ∑ _round : Fin roundCount, error := by
          apply Finset.sum_le_sum
          intro round _
          calc
            (resamplingSampleAverage (batches round) (scores round) -
              pmfExp (laws round) (scores round)) * labels round ≤
                |(resamplingSampleAverage (batches round) (scores round) -
                  pmfExp (laws round) (scores round)) * labels round| :=
              le_abs_self _
            _ = |resamplingSampleAverage (batches round) (scores round) -
                  pmfExp (laws round) (scores round)| * |labels round| := by
                  rw [abs_mul]
            _ ≤ error * 1 := by
                  exact mul_le_mul (hgood round) (hlabels round) (abs_nonneg _) herror
            _ = error := by ring
    _ = (roundCount : ℝ) * error := by simp

/-- A two-sided batch-accuracy event turns the simultaneous-move expected
OWAL comparison into its delayed-label empirical counterpart.  This is a
deterministic pathwise statement; the adaptive concentration theorem supplies
the displayed event for a protocol in which each current law is chosen from
the preceding history. -/
theorem finiteRandomizedWeakAgnosticGuarantee_to_resampled
    {Context Sample : Type*} [Fintype Sample] [DecidableEq Sample]
    {roundCount sampleCount : ℕ}
    (comparators : Set (Context → ℝ)) (batches : Fin roundCount → Fin sampleCount → Sample)
    (laws : Fin roundCount → PMF Sample) (predictor : Sample → Context → ℝ)
    (contexts : Fin roundCount → Context) (labels : Fin roundCount → ℝ)
    (hlabels : ∀ round, |labels round| ≤ 1)
    (regret error : ℝ) (herror : 0 ≤ error)
    (hweak : finiteRandomizedWeakAgnosticGuarantee comparators laws predictor contexts labels regret)
    (hresampling : ∀ round,
      |resamplingSampleAverage (batches round)
        (fun sample => predictor sample (contexts round)) -
          pmfExp (laws round) (fun sample => predictor sample (contexts round))| ≤ error) :
    finiteResampledWeakAgnosticGuarantee comparators batches predictor contexts labels
      (regret + (roundCount : ℝ) * error) := by
  intro comparator hcomparator
  have hnegLabels : ∀ round, |(-labels round)| ≤ 1 := by
    intro round
    simpa only [abs_neg] using hlabels round
  have hdeviation := resamplingSignedCorrelationError_le batches laws
    (fun round sample => predictor sample (contexts round))
    (fun round => -labels round) hnegLabels error herror hresampling
  have hsumDeviation :
      (∑ round,
        (resamplingSampleAverage (batches round)
            (fun sample => predictor sample (contexts round)) -
          pmfExp (laws round) (fun sample => predictor sample (contexts round))) *
          (-labels round)) =
        (∑ round, pmfExp (laws round)
          (fun sample => predictor sample (contexts round)) * labels round) -
          ∑ round, resamplingSampleAverage (batches round)
            (fun sample => predictor sample (contexts round)) * labels round := by
    calc
      (∑ round,
        (resamplingSampleAverage (batches round)
            (fun sample => predictor sample (contexts round)) -
          pmfExp (laws round) (fun sample => predictor sample (contexts round))) *
          (-labels round)) =
          ∑ round, (pmfExp (laws round)
              (fun sample => predictor sample (contexts round)) * labels round -
            resamplingSampleAverage (batches round)
              (fun sample => predictor sample (contexts round)) * labels round) := by
            apply Finset.sum_congr rfl
            intro round _
            ring
      _ = (∑ round, pmfExp (laws round)
            (fun sample => predictor sample (contexts round)) * labels round) -
          ∑ round, resamplingSampleAverage (batches round)
            (fun sample => predictor sample (contexts round)) * labels round :=
        Finset.sum_sub_distrib
          (fun round => pmfExp (laws round)
            (fun sample => predictor sample (contexts round)) * labels round)
          (fun round => resamplingSampleAverage (batches round)
            (fun sample => predictor sample (contexts round)) * labels round)
  rw [hsumDeviation] at hdeviation
  have hcomparison := hweak comparator hcomparator
  linarith

/-- Independent resampling batches at every round satisfy their upper
mean-comparison bounds simultaneously.  The laws and the bounded score may
vary by round, as they do in a delayed-label-to-simultaneous-move reduction. -/
theorem pmfProb_all_resamplingSampleAverages_succeed_ge
    {Sample : Type*} [Fintype Sample] [DecidableEq Sample]
    [MeasurableSpace Sample] [DiscreteMeasurableSpace Sample]
    {roundCount sampleCount : ℕ}
    (roundCountPositive : 0 < roundCount) (sampleCountPositive : 0 < sampleCount)
    (laws : Fin roundCount → PMF Sample) (scores : Fin roundCount → Sample → ℝ)
    (hscores : ∀ round item, scores round item ∈ Set.Icc (-1 : ℝ) 1)
    (error : ℝ) (herror : 0 ≤ error) :
    1 - (roundCount : ℝ) * Real.exp (-(sampleCount : ℝ) * error ^ 2 / 2) ≤
      pmfProbClassical (pmfPi fun round => pmfProduct (Fin sampleCount) Sample (laws round))
        (AllPACSucceed (fun round samples =>
          error ≤ resamplingSampleAverage (samples round) (scores round) -
            pmfExp (laws round) (scores round))) := by
  letI : Nonempty (Fin roundCount) := ⟨⟨0, roundCountPositive⟩⟩
  apply pmfProb_allPACSucceed_ge_one_sub
    (pmfPi fun round => pmfProduct (Fin sampleCount) Sample (laws round))
    (fun round samples =>
      error ≤ resamplingSampleAverage (samples round) (scores round) -
        pmfExp (laws round) (scores round))
    ((roundCount : ℝ) * Real.exp (-(sampleCount : ℝ) * error ^ 2 / 2))
  intro round
  rw [pmfProbClassical_eq_pmfProb]
  calc
    pmfProb (pmfPi fun round => pmfProduct (Fin sampleCount) Sample (laws round))
      (fun samples => error ≤ resamplingSampleAverage (samples round) (scores round) -
        pmfExp (laws round) (scores round)) =
        pmfProb (pmfProduct (Fin sampleCount) Sample (laws round))
          (fun samples => error ≤ resamplingSampleAverage samples (scores round) -
            pmfExp (laws round) (scores round)) := by
          exact pmfProb_pmfPi_eval_eq
            (fun sourceRound => pmfProduct (Fin sampleCount) Sample (laws sourceRound)) round
            (fun samples => error ≤ resamplingSampleAverage samples (scores round) -
              pmfExp (laws round) (scores round))
    _ ≤ Real.exp (-(sampleCount : ℝ) * error ^ 2 / 2) :=
      pmfProb_resamplingSampleAverage_sub_expectation_ge_le sampleCountPositive
        (laws round) (scores round) (hscores round) error herror
    _ = ((roundCount : ℝ) * Real.exp (-(sampleCount : ℝ) * error ^ 2 / 2)) /
        (Fintype.card (Fin roundCount) : ℝ) := by
          simp
          field_simp [show (roundCount : ℝ) ≠ 0 by
            exact_mod_cast Nat.ne_of_gt roundCountPositive]

/-- Independent resampling batches at every round satisfy their two-sided
mean-comparison bounds simultaneously.  The absolute-value form controls a
subsequent multiplication by an arbitrary payoff in `[-1, 1]`. -/
theorem pmfProb_all_resamplingSampleAverages_twoSided_succeed_ge
    {Sample : Type*} [Fintype Sample] [DecidableEq Sample]
    [MeasurableSpace Sample] [DiscreteMeasurableSpace Sample]
    {roundCount sampleCount : ℕ}
    (roundCountPositive : 0 < roundCount) (sampleCountPositive : 0 < sampleCount)
    (laws : Fin roundCount → PMF Sample) (scores : Fin roundCount → Sample → ℝ)
    (hscores : ∀ round item, scores round item ∈ Set.Icc (-1 : ℝ) 1)
    (error : ℝ) (herror : 0 ≤ error) :
    1 - (roundCount : ℝ) *
        (2 * Real.exp (-(sampleCount : ℝ) * error ^ 2 / 2)) ≤
      pmfProbClassical (pmfPi fun round => pmfProduct (Fin sampleCount) Sample (laws round))
        (AllPACSucceed (fun round samples =>
          error ≤ |resamplingSampleAverage (samples round) (scores round) -
            pmfExp (laws round) (scores round)|)) := by
  letI : Nonempty (Fin roundCount) := ⟨⟨0, roundCountPositive⟩⟩
  apply pmfProb_allPACSucceed_ge_one_sub
    (pmfPi fun round => pmfProduct (Fin sampleCount) Sample (laws round))
    (fun round samples =>
      error ≤ |resamplingSampleAverage (samples round) (scores round) -
        pmfExp (laws round) (scores round)|)
    ((roundCount : ℝ) * (2 * Real.exp (-(sampleCount : ℝ) * error ^ 2 / 2)))
  intro round
  rw [pmfProbClassical_eq_pmfProb]
  calc
    pmfProb (pmfPi fun round => pmfProduct (Fin sampleCount) Sample (laws round))
      (fun samples => error ≤
        |resamplingSampleAverage (samples round) (scores round) -
          pmfExp (laws round) (scores round)|) =
        pmfProb (pmfProduct (Fin sampleCount) Sample (laws round))
          (fun samples => error ≤
            |resamplingSampleAverage samples (scores round) -
              pmfExp (laws round) (scores round)|) := by
          exact pmfProb_pmfPi_eval_eq
            (fun sourceRound => pmfProduct (Fin sampleCount) Sample (laws sourceRound)) round
            (fun samples => error ≤
              |resamplingSampleAverage samples (scores round) -
                pmfExp (laws round) (scores round)|)
    _ ≤ 2 * Real.exp (-(sampleCount : ℝ) * error ^ 2 / 2) :=
      pmfProb_resamplingSampleAverage_abs_sub_expectation_ge_le
        sampleCountPositive (laws round) (scores round) (hscores round) error herror
    _ = ((roundCount : ℝ) *
          (2 * Real.exp (-(sampleCount : ℝ) * error ^ 2 / 2))) /
        (Fintype.card (Fin roundCount) : ℝ) := by
          simp
          field_simp [show (roundCount : ℝ) ≠ 0 by
            exact_mod_cast Nat.ne_of_gt roundCountPositive]

/-- The confidence radius for all `roundCount` independent resampling
batches at once. -/
noncomputable def resamplingConfidenceRadius (roundCount sampleCount : ℕ)
    (failureProbability : ℝ) : ℝ :=
  Real.sqrt (2 * Real.log (2 * (roundCount : ℝ) / failureProbability) / sampleCount)

theorem resamplingConfidenceRadius_sq {roundCount sampleCount : ℕ}
    {failureProbability : ℝ} (sampleCountPositive : 0 < (sampleCount : ℝ))
    (hlogNonneg : 0 ≤ Real.log (2 * (roundCount : ℝ) / failureProbability)) :
    resamplingConfidenceRadius roundCount sampleCount failureProbability ^ 2 =
      2 * Real.log (2 * (roundCount : ℝ) / failureProbability) / sampleCount := by
  unfold resamplingConfidenceRadius
  rw [Real.sq_sqrt]
  apply div_nonneg
  · positivity
  · exact sampleCountPositive.le

/-- At the confidence radius, the union-bound failure term for all rounds is
exactly `δ / 2`. -/
theorem resamplingConfidenceTail_eq {roundCount sampleCount : ℕ}
    (roundCountPositive : 0 < (roundCount : ℝ))
    (sampleCountPositive : 0 < (sampleCount : ℝ))
    {failureProbability : ℝ}
    (failurePositive : 0 < failureProbability) (failure_lt_one : failureProbability < 1) :
    (roundCount : ℝ) * Real.exp
      (-(sampleCount : ℝ) *
        resamplingConfidenceRadius roundCount sampleCount failureProbability ^ 2 / 2) =
      failureProbability / 2 := by
  have hroundOne : (1 : ℝ) ≤ (roundCount : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (by exact_mod_cast roundCountPositive))
  have hlogArgumentLarge : 1 < 2 * (roundCount : ℝ) / failureProbability := by
    apply (one_lt_div failurePositive).2
    nlinarith
  have hlogArgument : 0 < 2 * (roundCount : ℝ) / failureProbability := by linarith
  have hlog : 0 < Real.log (2 * (roundCount : ℝ) / failureProbability) :=
    Real.log_pos hlogArgumentLarge
  rw [resamplingConfidenceRadius_sq sampleCountPositive hlog.le]
  have hexponent :
      -(sampleCount : ℝ) *
        (2 * Real.log (2 * (roundCount : ℝ) / failureProbability) / sampleCount) / 2 =
        -Real.log (2 * (roundCount : ℝ) / failureProbability) := by
    field_simp [sampleCountPositive.ne']
  rw [hexponent, Real.exp_neg, Real.exp_log hlogArgument]
  field_simp [failurePositive.ne', roundCountPositive.ne']

/-- All finite resampling batches meet their upper mean-comparison bound with
probability at least `1 - δ/2` at the explicit confidence radius. -/
theorem pmfProb_all_resamplingSampleAverages_confidence_ge
    {Sample : Type*} [Fintype Sample] [DecidableEq Sample]
    [MeasurableSpace Sample] [DiscreteMeasurableSpace Sample]
    {roundCount sampleCount : ℕ}
    (roundCountPositive : 0 < roundCount) (sampleCountPositive : 0 < sampleCount)
    (laws : Fin roundCount → PMF Sample) (scores : Fin roundCount → Sample → ℝ)
    (hscores : ∀ round item, scores round item ∈ Set.Icc (-1 : ℝ) 1)
    {failureProbability : ℝ}
    (failurePositive : 0 < failureProbability) (failure_lt_one : failureProbability < 1) :
    1 - failureProbability / 2 ≤
      pmfProbClassical (pmfPi fun round => pmfProduct (Fin sampleCount) Sample (laws round))
        (AllPACSucceed (fun round samples =>
          resamplingConfidenceRadius roundCount sampleCount failureProbability ≤
            resamplingSampleAverage (samples round) (scores round) -
              pmfExp (laws round) (scores round))) := by
  have hroundPositive : 0 < (roundCount : ℝ) := by exact_mod_cast roundCountPositive
  have hsamplePositive : 0 < (sampleCount : ℝ) := by exact_mod_cast sampleCountPositive
  have hsuccess := pmfProb_all_resamplingSampleAverages_succeed_ge
    roundCountPositive sampleCountPositive laws scores hscores
    (resamplingConfidenceRadius roundCount sampleCount failureProbability)
    (Real.sqrt_nonneg _)
  calc
    1 - failureProbability / 2 =
        1 - (roundCount : ℝ) * Real.exp
          (-(sampleCount : ℝ) *
            resamplingConfidenceRadius roundCount sampleCount failureProbability ^ 2 / 2) := by
          rw [resamplingConfidenceTail_eq hroundPositive hsamplePositive
            failurePositive failure_lt_one]
    _ ≤ _ := hsuccess

/-- The confidence radius for a simultaneous two-sided comparison of all
`roundCount` finite resampling batches. -/
noncomputable def resamplingTwoSidedConfidenceRadius (roundCount sampleCount : ℕ)
    (failureProbability : ℝ) : ℝ :=
  Real.sqrt (2 * Real.log (4 * (roundCount : ℝ) / failureProbability) / sampleCount)

theorem resamplingTwoSidedConfidenceRadius_sq {roundCount sampleCount : ℕ}
    {failureProbability : ℝ} (sampleCountPositive : 0 < (sampleCount : ℝ))
    (hlogNonneg : 0 ≤ Real.log (4 * (roundCount : ℝ) / failureProbability)) :
    resamplingTwoSidedConfidenceRadius roundCount sampleCount failureProbability ^ 2 =
      2 * Real.log (4 * (roundCount : ℝ) / failureProbability) / sampleCount := by
  unfold resamplingTwoSidedConfidenceRadius
  rw [Real.sq_sqrt]
  apply div_nonneg
  · positivity
  · exact sampleCountPositive.le

/-- A batch size at least `2 T log (4T/δ)` makes the total two-sided
resampling error over `T` rounds at most `√T`.  This is the explicit
finite-sample calculation behind the usual `T log(T/δ)` resampling schedule;
the statement is deliberately conditional on the integer batch-size
inequality so callers may choose any convenient ceiling or larger schedule. -/
theorem roundCount_mul_resamplingTwoSidedConfidenceRadius_le_sqrt
    {roundCount sampleCount : ℕ} {failureProbability : ℝ}
    (roundCountPositive : 0 < (roundCount : ℝ))
    (sampleCountPositive : 0 < (sampleCount : ℝ))
    (hbatchSize : 2 * (roundCount : ℝ) *
      Real.log (4 * (roundCount : ℝ) / failureProbability) ≤ sampleCount) :
    (roundCount : ℝ) *
      resamplingTwoSidedConfidenceRadius roundCount sampleCount failureProbability ≤
        Real.sqrt (roundCount : ℝ) := by
  have hratio :
      2 * Real.log (4 * (roundCount : ℝ) / failureProbability) / sampleCount ≤
        1 / (roundCount : ℝ) := by
    apply (div_le_div_iff₀ sampleCountPositive roundCountPositive).2
    nlinarith [hbatchSize]
  have hroot :
      Real.sqrt (2 * Real.log (4 * (roundCount : ℝ) / failureProbability) / sampleCount) ≤
        Real.sqrt (1 / (roundCount : ℝ)) :=
    Real.sqrt_le_sqrt hratio
  have hscale :
      (roundCount : ℝ) * Real.sqrt (1 / (roundCount : ℝ)) =
        Real.sqrt (roundCount : ℝ) := by
    have hleftNonnegative :
        0 ≤ (roundCount : ℝ) * Real.sqrt (1 / (roundCount : ℝ)) := by positivity
    have hleftSquare :
        ((roundCount : ℝ) * Real.sqrt (1 / (roundCount : ℝ))) ^ 2 =
          (roundCount : ℝ) := by
      rw [mul_pow, Real.sq_sqrt]
      · field_simp [roundCountPositive.ne']
      · positivity
    have hrightSquare : Real.sqrt (roundCount : ℝ) ^ 2 = (roundCount : ℝ) :=
      Real.sq_sqrt roundCountPositive.le
    nlinarith [Real.sqrt_nonneg (roundCount : ℝ)]
  calc
    (roundCount : ℝ) *
        resamplingTwoSidedConfidenceRadius roundCount sampleCount failureProbability =
      (roundCount : ℝ) *
        Real.sqrt (2 * Real.log (4 * (roundCount : ℝ) / failureProbability) / sampleCount) := rfl
    _ ≤ (roundCount : ℝ) * Real.sqrt (1 / (roundCount : ℝ)) :=
      mul_le_mul_of_nonneg_left hroot roundCountPositive.le
    _ = Real.sqrt (roundCount : ℝ) := hscale

/-- At the two-sided confidence radius, the simultaneous failure term is
exactly `δ / 2`. -/
theorem resamplingTwoSidedConfidenceTail_eq {roundCount sampleCount : ℕ}
    (roundCountPositive : 0 < (roundCount : ℝ))
    (sampleCountPositive : 0 < (sampleCount : ℝ))
    {failureProbability : ℝ}
    (failurePositive : 0 < failureProbability) (failure_lt_one : failureProbability < 1) :
    (roundCount : ℝ) * (2 * Real.exp
      (-(sampleCount : ℝ) *
        resamplingTwoSidedConfidenceRadius roundCount sampleCount failureProbability ^ 2 / 2)) =
      failureProbability / 2 := by
  have hroundOne : (1 : ℝ) ≤ (roundCount : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (by exact_mod_cast roundCountPositive))
  have hlogArgumentLarge : 1 < 4 * (roundCount : ℝ) / failureProbability := by
    apply (one_lt_div failurePositive).2
    nlinarith
  have hlogArgument : 0 < 4 * (roundCount : ℝ) / failureProbability := by linarith
  have hlog : 0 < Real.log (4 * (roundCount : ℝ) / failureProbability) :=
    Real.log_pos hlogArgumentLarge
  rw [resamplingTwoSidedConfidenceRadius_sq sampleCountPositive hlog.le]
  have hexponent :
      -(sampleCount : ℝ) *
        (2 * Real.log (4 * (roundCount : ℝ) / failureProbability) / sampleCount) / 2 =
        -Real.log (4 * (roundCount : ℝ) / failureProbability) := by
    field_simp [sampleCountPositive.ne']
  rw [hexponent, Real.exp_neg, Real.exp_log hlogArgument]
  field_simp [failurePositive.ne', roundCountPositive.ne']; norm_num

/-- The adaptive-history version of the two-sided resampling confidence
event.  Each round may choose its law and score after seeing all earlier
resampling batches. -/
theorem adaptiveQuerySuccessProbability_twoSidedResampling_confidence_ge
    {State Sample : Type*} [Fintype State] [DecidableEq State]
    [Fintype Sample] [DecidableEq Sample]
    [MeasurableSpace Sample] [DiscreteMeasurableSpace Sample]
    {roundCount sampleCount : ℕ}
    (roundCountPositive : 0 < roundCount) (sampleCountPositive : 0 < sampleCount)
    (initialStateLaw : PMF State) (advance : AdaptiveStateUpdate State (Fin sampleCount → Sample))
    (laws : ℕ → State → PMF Sample) (scores : ℕ → State → Sample → ℝ)
    (hscores : ∀ queryIndex state item,
      scores queryIndex state item ∈ Set.Icc (-1 : ℝ) 1)
    {failureProbability : ℝ}
    (failurePositive : 0 < failureProbability) (failure_lt_one : failureProbability < 1) :
    1 - failureProbability / 2 ≤
      pmfProb
        (adaptiveQueryStateLaw initialStateLaw
          (fun queryIndex state =>
            pmfProduct (Fin sampleCount) Sample (laws queryIndex state))
          advance
          (fun queryIndex state samples =>
            resamplingTwoSidedConfidenceRadius roundCount sampleCount failureProbability ≤
              |resamplingSampleAverage samples (scores queryIndex state) -
                pmfExp (laws queryIndex state) (scores queryIndex state)|)
          roundCount)
        (fun stateFailure => stateFailure.2 = false) := by
  have hroundPositive : 0 < (roundCount : ℝ) := by exact_mod_cast roundCountPositive
  have hsamplePositive : 0 < (sampleCount : ℝ) := by exact_mod_cast sampleCountPositive
  have hsuccess := adaptiveQuerySuccessProbability_twoSidedResampling_ge_one_sub_sum
    sampleCountPositive initialStateLaw advance laws scores hscores
    (resamplingTwoSidedConfidenceRadius roundCount sampleCount failureProbability)
    (Real.sqrt_nonneg _) roundCount
  calc
    1 - failureProbability / 2 =
        1 - (roundCount : ℝ) * (2 * Real.exp
          (-(sampleCount : ℝ) *
            resamplingTwoSidedConfidenceRadius roundCount sampleCount failureProbability ^ 2 / 2)) := by
          rw [resamplingTwoSidedConfidenceTail_eq hroundPositive hsamplePositive
            failurePositive failure_lt_one]
    _ = 1 - ∑ queryIndex ∈ Finset.range roundCount,
        2 * Real.exp (-(sampleCount : ℝ) *
          resamplingTwoSidedConfidenceRadius roundCount sampleCount failureProbability ^ 2 / 2) := by
          simp
    _ ≤ _ := hsuccess

/-- All finite resampling batches meet their two-sided mean-comparison bound
with probability at least `1 - δ/2` at the explicit confidence radius. -/
theorem pmfProb_all_resamplingSampleAverages_twoSided_confidence_ge
    {Sample : Type*} [Fintype Sample] [DecidableEq Sample]
    [MeasurableSpace Sample] [DiscreteMeasurableSpace Sample]
    {roundCount sampleCount : ℕ}
    (roundCountPositive : 0 < roundCount) (sampleCountPositive : 0 < sampleCount)
    (laws : Fin roundCount → PMF Sample) (scores : Fin roundCount → Sample → ℝ)
    (hscores : ∀ round item, scores round item ∈ Set.Icc (-1 : ℝ) 1)
    {failureProbability : ℝ}
    (failurePositive : 0 < failureProbability) (failure_lt_one : failureProbability < 1) :
    1 - failureProbability / 2 ≤
      pmfProbClassical (pmfPi fun round => pmfProduct (Fin sampleCount) Sample (laws round))
        (AllPACSucceed (fun round samples =>
          resamplingTwoSidedConfidenceRadius roundCount sampleCount failureProbability ≤
            |resamplingSampleAverage (samples round) (scores round) -
              pmfExp (laws round) (scores round)|)) := by
  have hroundPositive : 0 < (roundCount : ℝ) := by exact_mod_cast roundCountPositive
  have hsamplePositive : 0 < (sampleCount : ℝ) := by exact_mod_cast sampleCountPositive
  have hsuccess := pmfProb_all_resamplingSampleAverages_twoSided_succeed_ge
    roundCountPositive sampleCountPositive laws scores hscores
    (resamplingTwoSidedConfidenceRadius roundCount sampleCount failureProbability)
    (Real.sqrt_nonneg _)
  calc
    1 - failureProbability / 2 =
        1 - (roundCount : ℝ) * (2 * Real.exp
          (-(sampleCount : ℝ) *
            resamplingTwoSidedConfidenceRadius roundCount sampleCount failureProbability ^ 2 / 2)) := by
          rw [resamplingTwoSidedConfidenceTail_eq hroundPositive hsamplePositive
            failurePositive failure_lt_one]
    _ ≤ _ := hsuccess

end AppliedModelingLib.Learning.Online
