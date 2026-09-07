import PRPKG24AccuracyDiversity.DecayingBernoulli
import AppliedModelingLib.Foundations.Probability.IndependentProduct
import AppliedModelingLib.Applications.RatingSystems.BinaryLargeDeviations
import PRPKG24AccuracyDiversity.SourcePreferenceMixture

/-!
# Theorem 2 rank-varying Bernoulli source model

This module gives the finite, literal probability model behind the two
rank-Bernoulli count objectives used in Theorem 2.  Each rank has its own
Bernoulli parameter, and `AppliedModelingLib.pmfPi` supplies independence across ranks.
The coordinate laws are deliberately not asserted to be identically
distributed.
-/

open scoped BigOperators

namespace PRPKG24AccuracyDiversity

open AppliedModelingLib
open AppliedModelingLib.Probability

/-- The finite independent rank-varying Bernoulli law for the first `q` ranks. -/
noncomputable def rankBernoulliFiniteLaw
    (success : ℕ → ℝ) (q : ℕ)
    (hvalid : ∀ i : Fin q, 0 ≤ success i.1 ∧ success i.1 ≤ 1) :
    PMF (Fin q → Bool) :=
  AppliedModelingLib.pmfPi (fun i : Fin q =>
    realBernoulliPMF (success i.1) (hvalid i).1 (hvalid i).2)

/-- The source law's atom formula, exposing the independent rank product directly. -/
theorem rankBernoulliFiniteLaw_apply_toReal
    (success : ℕ → ℝ) (q : ℕ)
    (hvalid : ∀ i : Fin q, 0 ≤ success i.1 ∧ success i.1 ≤ 1)
    (sample : Fin q → Bool) :
    (rankBernoulliFiniteLaw success q hvalid sample).toReal =
      ∏ i : Fin q,
        if sample i then success i.1 else 1 - success i.1 := by
  rw [rankBernoulliFiniteLaw, AppliedModelingLib.pmfPi_apply_toReal]
  refine Finset.prod_congr rfl ?_
  intro i _
  by_cases hsuccess : sample i
  · simp [hsuccess]
  · simp [hsuccess]

/-- The top-one value of a finite Boolean sample: `1` exactly when some rank succeeds. -/
def rankBernoulliFiniteTopOneSampleValue {q : ℕ} (sample : Fin q → Bool) : ℝ :=
  if ∀ i : Fin q, sample i = false then 0 else 1

/-- The all-consumed value of a finite Boolean sample. -/
def rankBernoulliFiniteAllConsumedSampleValue {q : ℕ} (sample : Fin q → Bool) : ℝ :=
  ∑ i : Fin q, binaryRatingScore (sample i)

/-- The all-failure sample has the expected finite product atom mass. -/
theorem rankBernoulliFiniteLaw_all_failure_mass
    (success : ℕ → ℝ) (q : ℕ)
    (hvalid : ∀ i : Fin q, 0 ≤ success i.1 ∧ success i.1 ≤ 1) :
    (rankBernoulliFiniteLaw success q hvalid (fun _ => false)).toReal =
      ∏ i : Fin q, (1 - success i.1) := by
  simp [rankBernoulliFiniteLaw]

/-- The finite independent source law realizes the top-one Bernoulli formula. -/
theorem rankBernoulliFiniteTopOne_expected
    (success : ℕ → ℝ) (q : ℕ)
    (hvalid : ∀ i : Fin q, 0 ≤ success i.1 ∧ success i.1 ≤ 1) :
    AppliedModelingLib.pmfExp (rankBernoulliFiniteLaw success q hvalid)
      rankBernoulliFiniteTopOneSampleValue =
      1 - ∏ i : Fin q, (1 - success i.1) := by
  classical
  let failure : Fin q → Bool := fun _ => false
  have hvalue :
      ∀ sample : Fin q → Bool,
        rankBernoulliFiniteTopOneSampleValue sample =
          if sample = failure then 0 else 1 := by
    intro sample
    by_cases hsample : sample = failure
    · subst sample
      simp [rankBernoulliFiniteTopOneSampleValue, failure]
    · have hnot_all_failure : ¬ ∀ i : Fin q, sample i = false := by
        intro hall
        apply hsample
        funext i
        simpa [failure] using hall i
      simp [rankBernoulliFiniteTopOneSampleValue, hsample, hnot_all_failure]
  rw [AppliedModelingLib.pmfExp_eq_prob_mul_add_one_sub_prob_mul_of_forall_eq_if
    (rankBernoulliFiniteLaw success q hvalid) (fun sample => sample = failure)
    rankBernoulliFiniteTopOneSampleValue 0 1 hvalue]
  rw [AppliedModelingLib.pmfProb_singleton]
  rw [rankBernoulliFiniteLaw_all_failure_mass]
  ring

/-- Each coordinate of the finite source law has its declared Bernoulli mean. -/
theorem rankBernoulliFiniteLaw_coordinate_expected
    (success : ℕ → ℝ) (q : ℕ)
    (hvalid : ∀ i : Fin q, 0 ≤ success i.1 ∧ success i.1 ≤ 1)
    (i : Fin q) :
    AppliedModelingLib.pmfExp (rankBernoulliFiniteLaw success q hvalid)
      (fun sample => binaryRatingScore (sample i)) = success i.1 := by
  classical
  let μ : Fin q → PMF Bool := fun j =>
    realBernoulliPMF (success j.1) (hvalid j).1 (hvalid j).2
  change AppliedModelingLib.pmfExp (AppliedModelingLib.pmfPi μ)
      (fun sample => binaryRatingScore (sample i)) = success i.1
  have hcoord : ∀ j : Fin q, ∑ b : Bool, (μ j b).toReal = 1 := by
    intro j
    exact AppliedModelingLib.pmfToRealSum (μ j)
  unfold AppliedModelingLib.pmfExp
  calc
    ∑ sample : Fin q → Bool,
        (AppliedModelingLib.pmfPi μ sample).toReal * binaryRatingScore (sample i)
        =
      ∑ sample : Fin q → Bool,
        ∏ j : Fin q,
          (μ j (sample j)).toReal *
            (if j = i then binaryRatingScore (sample j) else 1) := by
          refine Finset.sum_congr rfl ?_
          intro sample _
          rw [AppliedModelingLib.pmfPi_apply_toReal, Finset.prod_mul_distrib,
            Fintype.prod_ite_eq']
    _ =
      ∏ j : Fin q, ∑ b : Bool,
        (μ j b).toReal *
          (if j = i then binaryRatingScore b else 1) := by
          symm
          simpa using
            (Finset.prod_univ_sum
              (t := fun _j : Fin q => (Finset.univ : Finset Bool))
              (f := fun j b =>
                (μ j b).toReal *
                  (if j = i then binaryRatingScore b else 1)))
    _ = ∏ j : Fin q, if j = i then success i.1 else 1 := by
          refine Finset.prod_congr rfl ?_
          intro j _
          by_cases hji : j = i
          · subst j
            simp [μ, binaryRatingScore]
          · simp only [if_neg hji, mul_one]
            linarith [hcoord j]
    _ = success i.1 := by simp

/-- The finite independent source law realizes the all-consumed Bernoulli formula. -/
theorem rankBernoulliFiniteAllConsumed_expected
    (success : ℕ → ℝ) (q : ℕ)
    (hvalid : ∀ i : Fin q, 0 ≤ success i.1 ∧ success i.1 ≤ 1) :
    AppliedModelingLib.pmfExp (rankBernoulliFiniteLaw success q hvalid)
      rankBernoulliFiniteAllConsumedSampleValue =
      ∑ i : Fin q, success i.1 := by
  change AppliedModelingLib.pmfExp (rankBernoulliFiniteLaw success q hvalid)
      (fun sample => ∑ i : Fin q, binaryRatingScore (sample i)) = _
  rw [AppliedModelingLib.pmfExp_univ_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  exact rankBernoulliFiniteLaw_coordinate_expected success q hvalid i

/-- Existing top-one scalar values are expectations under the literal finite source law. -/
theorem rankBernoulliTopOneValue_eq_expected_independent_source
    (success : ℕ → ℝ) (q : ℕ)
    (hvalid : ∀ i : Fin q, 0 ≤ success i.1 ∧ success i.1 ≤ 1) :
    rankBernoulliTopOneValue success q =
      AppliedModelingLib.pmfExp (rankBernoulliFiniteLaw success q hvalid)
        rankBernoulliFiniteTopOneSampleValue := by
  rw [rankBernoulliFiniteTopOne_expected]
  unfold rankBernoulliTopOneValue
  rw [Finset.prod_range]

/-- Existing all-consumed scalar values are expectations under the literal finite source law. -/
theorem rankBernoulliAllConsumedValue_eq_expected_independent_source
    (success : ℕ → ℝ) (q : ℕ)
    (hvalid : ∀ i : Fin q, 0 ≤ success i.1 ∧ success i.1 ≤ 1) :
    rankBernoulliAllConsumedValue success q =
      AppliedModelingLib.pmfExp (rankBernoulliFiniteLaw success q hvalid)
        rankBernoulliFiniteAllConsumedSampleValue := by
  rw [rankBernoulliFiniteAllConsumed_expected]
  simp [rankBernoulliAllConsumedValue, Fin.sum_univ_eq_sum_range]

/-- The top-one consumption-model count value is a literal finite expectation. -/
theorem rankBernoulliTopOneConsumptionModel_value_eq_expected_independent_source
    {T : ℕ} (likelihood : ItemType T → ℝ) (success : ℕ → ℝ)
    (q : ℕ)
    (hvalid : ∀ i : Fin q, 0 ≤ success i.1 ∧ success i.1 ≤ 1)
    (t : ItemType T) :
    (rankBernoulliTopOneConsumptionModel likelihood success).valueOfCount t q =
      AppliedModelingLib.pmfExp (rankBernoulliFiniteLaw success q hvalid)
        rankBernoulliFiniteTopOneSampleValue := by
  simpa [rankBernoulliTopOneConsumptionModel] using
    rankBernoulliTopOneValue_eq_expected_independent_source success q hvalid

/-- The all-consumed consumption-model count value is a literal finite expectation. -/
theorem rankBernoulliAllConsumedConsumptionModel_value_eq_expected_independent_source
    {T : ℕ} (likelihood : ItemType T → ℝ) (success : ℕ → ℝ)
    (q : ℕ)
    (hvalid : ∀ i : Fin q, 0 ≤ success i.1 ∧ success i.1 ≤ 1)
    (t : ItemType T) :
    (rankBernoulliAllConsumedConsumptionModel likelihood success).valueOfCount t q =
      AppliedModelingLib.pmfExp (rankBernoulliFiniteLaw success q hvalid)
        rankBernoulliFiniteAllConsumedSampleValue := by
  simpa [rankBernoulliAllConsumedConsumptionModel] using
    rankBernoulliAllConsumedValue_eq_expected_independent_source success q hvalid

/-- Validity of the finite rank-varying Bernoulli law for the decaying source family. -/
theorem decayingBernoulliSuccess_finite_valid
    (c d alpha : ℝ) (q : ℕ)
    (hc_nonneg : 0 ≤ c) (hd_nonneg : 0 ≤ d) (halpha_nonneg : 0 ≤ alpha)
    (hfirst_le_one : decayingBernoulliSuccess c d alpha 0 ≤ 1) :
    ∀ i : Fin q,
      0 ≤ decayingBernoulliSuccess c d alpha i.1 ∧
        decayingBernoulliSuccess c d alpha i.1 ≤ 1 := by
  intro i
  exact ⟨decayingBernoulliSuccess_nonneg c d alpha hc_nonneg hd_nonneg i.1,
    decayingBernoulliSuccess_le_one_of_first_le_one
      c d alpha hc_nonneg hd_nonneg halpha_nonneg hfirst_le_one i.1⟩

/-- Literal finite product law for the decaying rank-Bernoulli source family. -/
noncomputable def decayingBernoulliFiniteLaw
    (c d alpha : ℝ) (q : ℕ)
    (hc_nonneg : 0 ≤ c) (hd_nonneg : 0 ≤ d) (halpha_nonneg : 0 ≤ alpha)
    (hfirst_le_one : decayingBernoulliSuccess c d alpha 0 ≤ 1) :
    PMF (Fin q → Bool) :=
  rankBernoulliFiniteLaw (decayingBernoulliSuccess c d alpha) q
    (decayingBernoulliSuccess_finite_valid c d alpha q hc_nonneg hd_nonneg
      halpha_nonneg hfirst_le_one)

/-- The decaying top-one model's count value is the corresponding finite source expectation. -/
theorem decayingBernoulliTopOneConsumptionModel_value_eq_expected_source
    {T : ℕ} (likelihood : ItemType T → ℝ) (c d alpha : ℝ) (q : ℕ)
    (hc_nonneg : 0 ≤ c) (hd_nonneg : 0 ≤ d) (halpha_nonneg : 0 ≤ alpha)
    (hfirst_le_one : decayingBernoulliSuccess c d alpha 0 ≤ 1)
    (t : ItemType T) :
    (decayingBernoulliTopOneConsumptionModel likelihood c d alpha).valueOfCount t q =
      AppliedModelingLib.pmfExp
        (decayingBernoulliFiniteLaw c d alpha q hc_nonneg hd_nonneg
          halpha_nonneg hfirst_le_one)
        rankBernoulliFiniteTopOneSampleValue := by
  exact rankBernoulliTopOneConsumptionModel_value_eq_expected_independent_source
    likelihood (decayingBernoulliSuccess c d alpha) q
    (decayingBernoulliSuccess_finite_valid c d alpha q hc_nonneg hd_nonneg
      halpha_nonneg hfirst_le_one) t

/-- The decaying all-consumed model's count value is the corresponding finite source expectation. -/
theorem decayingBernoulliAllConsumedConsumptionModel_value_eq_expected_source
    {T : ℕ} (likelihood : ItemType T → ℝ) (c d alpha : ℝ) (q : ℕ)
    (hc_nonneg : 0 ≤ c) (hd_nonneg : 0 ≤ d) (halpha_nonneg : 0 ≤ alpha)
    (hfirst_le_one : decayingBernoulliSuccess c d alpha 0 ≤ 1)
    (t : ItemType T) :
    (decayingBernoulliAllConsumedConsumptionModel likelihood c d alpha).valueOfCount t q =
      AppliedModelingLib.pmfExp
        (decayingBernoulliFiniteLaw c d alpha q hc_nonneg hd_nonneg
          halpha_nonneg hfirst_le_one)
        rankBernoulliFiniteAllConsumedSampleValue := by
  exact rankBernoulliAllConsumedConsumptionModel_value_eq_expected_independent_source
    likelihood (decayingBernoulliSuccess c d alpha) q
    (decayingBernoulliSuccess_finite_valid c d alpha q hc_nonneg hd_nonneg
      halpha_nonneg hfirst_le_one) t

/--
The Theorem 2 top-one objective is the finite source experiment which first
draws a preferred type and then draws the independent rank-varying Bernoulli
coordinates for that selected type.  It deliberately makes no claim about
independence between counterfactual type-specific samples.
-/
theorem decayingBernoulliTopOneModel_objective_eq_source_experiment
    {T : ℕ} (preferenceLaw : SourcePreferenceLaw T)
    (c d alpha : ℝ) (a : CountAllocation T)
    (hc_nonneg : 0 ≤ c) (hd_nonneg : 0 ≤ d) (halpha_nonneg : 0 ≤ alpha)
    (hfirst_le_one : decayingBernoulliSuccess c d alpha 0 ≤ 1) :
    (decayingBernoulliTopOneConsumptionModel
      (fun t => (preferenceLaw t).toReal) c d alpha).objective a =
      AppliedModelingLib.pmfExp preferenceLaw
        (fun t =>
          AppliedModelingLib.pmfExp
            (decayingBernoulliFiniteLaw c d alpha (a.count t) hc_nonneg
              hd_nonneg halpha_nonneg hfirst_le_one)
            rankBernoulliFiniteTopOneSampleValue) := by
  let M : ConsumptionModel T :=
    decayingBernoulliTopOneConsumptionModel
      (fun t => (preferenceLaw t).toReal) c d alpha
  calc
    M.objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t => M.valueOfCount t (a.count t)) :=
      ConsumptionModel.objective_eq_sourcePreferenceLaw_pmfExp M a
        preferenceLaw (by intro t; rfl)
    _ =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t =>
            AppliedModelingLib.pmfExp
              (decayingBernoulliFiniteLaw c d alpha (a.count t) hc_nonneg
                hd_nonneg halpha_nonneg hfirst_le_one)
              rankBernoulliFiniteTopOneSampleValue) := by
      refine AppliedModelingLib.pmfExp_congr preferenceLaw ?_
      intro t
      simpa [M] using
        decayingBernoulliTopOneConsumptionModel_value_eq_expected_source
          (fun t => (preferenceLaw t).toReal) c d alpha (a.count t)
          hc_nonneg hd_nonneg halpha_nonneg hfirst_le_one t

/--
The all-consumed Theorem 2 objective has the analogous finite two-stage
preferred-type and rank-varying-Bernoulli source semantics.
-/
theorem decayingBernoulliAllConsumedModel_objective_eq_source_experiment
    {T : ℕ} (preferenceLaw : SourcePreferenceLaw T)
    (c d alpha : ℝ) (a : CountAllocation T)
    (hc_nonneg : 0 ≤ c) (hd_nonneg : 0 ≤ d) (halpha_nonneg : 0 ≤ alpha)
    (hfirst_le_one : decayingBernoulliSuccess c d alpha 0 ≤ 1) :
    (decayingBernoulliAllConsumedConsumptionModel
      (fun t => (preferenceLaw t).toReal) c d alpha).objective a =
      AppliedModelingLib.pmfExp preferenceLaw
        (fun t =>
          AppliedModelingLib.pmfExp
            (decayingBernoulliFiniteLaw c d alpha (a.count t) hc_nonneg
              hd_nonneg halpha_nonneg hfirst_le_one)
            rankBernoulliFiniteAllConsumedSampleValue) := by
  let M : ConsumptionModel T :=
    decayingBernoulliAllConsumedConsumptionModel
      (fun t => (preferenceLaw t).toReal) c d alpha
  calc
    M.objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t => M.valueOfCount t (a.count t)) :=
      ConsumptionModel.objective_eq_sourcePreferenceLaw_pmfExp M a
        preferenceLaw (by intro t; rfl)
    _ =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t =>
            AppliedModelingLib.pmfExp
              (decayingBernoulliFiniteLaw c d alpha (a.count t) hc_nonneg
                hd_nonneg halpha_nonneg hfirst_le_one)
              rankBernoulliFiniteAllConsumedSampleValue) := by
      refine AppliedModelingLib.pmfExp_congr preferenceLaw ?_
      intro t
      simpa [M] using
        decayingBernoulliAllConsumedConsumptionModel_value_eq_expected_source
          (fun t => (preferenceLaw t).toReal) c d alpha (a.count t)
          hc_nonneg hd_nonneg halpha_nonneg hfirst_le_one t

end PRPKG24AccuracyDiversity
