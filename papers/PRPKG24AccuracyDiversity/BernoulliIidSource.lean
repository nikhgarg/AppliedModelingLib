import PRPKG24AccuracyDiversity.Theorem2RankBernoulliSource
import PRPKG24AccuracyDiversity.TailHomogeneity
import PRPKG24AccuracyDiversity.SourcePreferenceMixture

/-!
# Finite iid Bernoulli source bridges

This module records the literal finite probability experiment used by the
paper's Bernoulli count-value models.  Conditional on a selected type `t`, the
first `q` recommended items are iid Boolean draws with success probability
`B.successProb t`.  No independence between different selected types is
asserted or needed here.
-/

open scoped BigOperators

namespace PRPKG24AccuracyDiversity

open AppliedModelingLib

/-- The finite iid Bernoulli law for `q` recommendations with common success probability `p`. -/
noncomputable def iidBernoulliFiniteLaw
    (p : ℝ) (q : ℕ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    PMF (Fin q → Bool) :=
  rankBernoulliFiniteLaw (fun _ => p) q (fun _ => ⟨hp0, hp1⟩)

/-- The finite iid law realizes the top-one Bernoulli count-value formula. -/
theorem iidBernoulliFiniteTopOne_expected
    (p : ℝ) (q : ℕ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    AppliedModelingLib.pmfExp (iidBernoulliFiniteLaw p q hp0 hp1)
      rankBernoulliFiniteTopOneSampleValue =
      bernoulliAtLeastOneValue p q := by
  simpa [iidBernoulliFiniteLaw, bernoulliAtLeastOneValue] using
    (rankBernoulliFiniteTopOne_expected (fun _ => p) q
      (fun _ => ⟨hp0, hp1⟩))

/-- The finite iid law realizes the all-consumed Bernoulli count-value formula. -/
theorem iidBernoulliFiniteAllConsumed_expected
    (p : ℝ) (q : ℕ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    AppliedModelingLib.pmfExp (iidBernoulliFiniteLaw p q hp0 hp1)
      rankBernoulliFiniteAllConsumedSampleValue =
      (q : ℝ) * p := by
  simpa [iidBernoulliFiniteLaw] using
    (rankBernoulliFiniteAllConsumed_expected (fun _ => p) q
      (fun _ => ⟨hp0, hp1⟩))

/--
The Theorem 3/Corollary 3 top-one count value is the conditional expectation
of the stated finite iid Bernoulli experiment for the selected type.
-/
theorem bernoulliSatisfactionModel_value_eq_expected_iid_top_one_source
    {T : ℕ} (B : BernoulliSatisfactionModel T)
    (hvalid : B.SuccessProbabilitiesValid) (t : ItemType T) (q : ℕ) :
    B.toConsumptionModel.valueOfCount t q =
      AppliedModelingLib.pmfExp
        (iidBernoulliFiniteLaw (B.successProb t) q (hvalid t).1 (hvalid t).2)
        rankBernoulliFiniteTopOneSampleValue := by
  simpa [BernoulliSatisfactionModel.toConsumptionModel] using
    (iidBernoulliFiniteTopOne_expected (B.successProb t) q
      (hvalid t).1 (hvalid t).2).symm

/--
The all-consumed comparison model's count value is the conditional expectation
of the same finite iid Bernoulli experiment, scored by the number of
successes.
-/
theorem bernoulliAllConsumedModel_value_eq_expected_iid_all_consumed_source
    {T : ℕ} (B : BernoulliSatisfactionModel T)
    (hvalid : B.SuccessProbabilitiesValid) (t : ItemType T) (q : ℕ) :
    (bernoulliAllConsumedModel B).valueOfCount t q =
      AppliedModelingLib.pmfExp
        (iidBernoulliFiniteLaw (B.successProb t) q (hvalid t).1 (hvalid t).2)
        rankBernoulliFiniteAllConsumedSampleValue := by
  simpa [bernoulliAllConsumedModel, ConsumptionModel.linearized,
    ConsumptionModel.linearValueOfCount] using
    (iidBernoulliFiniteAllConsumed_expected (B.successProb t) q
      (hvalid t).1 (hvalid t).2).symm

/--
The top-one Bernoulli model realizes the source's two-stage experiment:
first select a preferred type from a PMF, then draw that type's finite iid
Bernoulli recommendations.  The identity does not introduce a joint law over
counterfactual outcomes of types that were not selected.
-/
theorem bernoulliSatisfactionModel_objective_eq_source_experiment
    {T : ℕ} (B : BernoulliSatisfactionModel T)
    (preferenceLaw : SourcePreferenceLaw T)
    (hpreference : ∀ t, B.likelihood t = (preferenceLaw t).toReal)
    (hvalid : B.SuccessProbabilitiesValid) (a : CountAllocation T) :
    B.toConsumptionModel.objective a =
      AppliedModelingLib.pmfExp preferenceLaw
        (fun t =>
          AppliedModelingLib.pmfExp
            (iidBernoulliFiniteLaw (B.successProb t) (a.count t)
              (hvalid t).1 (hvalid t).2)
            rankBernoulliFiniteTopOneSampleValue) := by
  calc
    B.toConsumptionModel.objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t => B.toConsumptionModel.valueOfCount t (a.count t)) :=
      ConsumptionModel.objective_eq_sourcePreferenceLaw_pmfExp
        B.toConsumptionModel a preferenceLaw (by
          intro t
          exact hpreference t)
    _ =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t =>
            AppliedModelingLib.pmfExp
              (iidBernoulliFiniteLaw (B.successProb t) (a.count t)
                (hvalid t).1 (hvalid t).2)
              rankBernoulliFiniteTopOneSampleValue) := by
      refine AppliedModelingLib.pmfExp_congr preferenceLaw ?_
      intro t
      exact bernoulliSatisfactionModel_value_eq_expected_iid_top_one_source
        B hvalid t (a.count t)

/--
The all-consumed Theorem 3 comparison model has the analogous selected-type
PMF and finite iid Bernoulli expectation semantics.
-/
theorem bernoulliAllConsumedModel_objective_eq_source_experiment
    {T : ℕ} (B : BernoulliSatisfactionModel T)
    (preferenceLaw : SourcePreferenceLaw T)
    (hpreference : ∀ t, B.likelihood t = (preferenceLaw t).toReal)
    (hvalid : B.SuccessProbabilitiesValid) (a : CountAllocation T) :
    (bernoulliAllConsumedModel B).objective a =
      AppliedModelingLib.pmfExp preferenceLaw
        (fun t =>
          AppliedModelingLib.pmfExp
            (iidBernoulliFiniteLaw (B.successProb t) (a.count t)
              (hvalid t).1 (hvalid t).2)
            rankBernoulliFiniteAllConsumedSampleValue) := by
  calc
    (bernoulliAllConsumedModel B).objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t => (bernoulliAllConsumedModel B).valueOfCount t (a.count t)) :=
      ConsumptionModel.objective_eq_sourcePreferenceLaw_pmfExp
        (bernoulliAllConsumedModel B) a preferenceLaw (by
          intro t
          exact hpreference t)
    _ =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t =>
            AppliedModelingLib.pmfExp
              (iidBernoulliFiniteLaw (B.successProb t) (a.count t)
                (hvalid t).1 (hvalid t).2)
              rankBernoulliFiniteAllConsumedSampleValue) := by
      refine AppliedModelingLib.pmfExp_congr preferenceLaw ?_
      intro t
      exact bernoulliAllConsumedModel_value_eq_expected_iid_all_consumed_source
        B hvalid t (a.count t)

end PRPKG24AccuracyDiversity
