import LG21TestOptionalPolicies.MainTheorems

/-!
# Theorem 3.2: randomized-policy scope and repaired theorem

The source allows the school's estimation function to be randomized, but the
proof of Theorem 3.2 later substitutes the affine Bayesian posterior mean.  A
randomized estimate law can depend on the reported score while having the same
expected estimate at every score.  Students then cannot profit from changing
their reporting decisions even though the policy is not test-blank.

This file records that issue in two parts:

* a finite abstract policy-surface diagnostic in which every pure feasible
  take/report pattern is an equilibrium, the policy is latent-skill and
  observably fair in every such equilibrium, and the policy is not test-blank;
* a repaired theorem.  The advertised implication is valid when estimate laws
  are identified by their expected estimate.  This includes deterministic
  point-estimate policies and is strictly more general than determinism.

The finite diagnostic is not assigned source-domain theorem credit because it
does not itself instantiate the inherited real Gaussian skill/test model.
`Theorem32GaussianCounterexample` supplies the Gaussian algebraic precursor,
and `Theorem32GaussianKernelCounterexample` closes the operational chain from
one estimator kernel to the induced population law.  The diagnostic and repair
here remain useful for isolating the missing hypothesis.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib
open AppliedModelingLib.Probability

/-! ## An abstract finite randomized-policy diagnostic -/

/-- Three school estimates used by the randomized counterexample. -/
inductive LG21RandomizedCounterexampleEstimate where
  | negative
  | zero
  | positive
deriving DecidableEq, Fintype, Repr

/-- The finite counterexample output space carries its discrete measurable structure. -/
instance : MeasurableSpace LG21RandomizedCounterexampleEstimate := ⊤

/-- The numerical estimate maximized by students. -/
def lg21RandomizedCounterexampleEstimateValue :
    LG21RandomizedCounterexampleEstimate → ℝ
  | .negative => -1
  | .zero => 0
  | .positive => 1

/-- The point mass at the zero estimate. -/
def lg21RandomizedCounterexampleZeroLaw :
    PMF LG21RandomizedCounterexampleEstimate :=
  PMF.pure .zero

/--
The genuinely randomized estimate law: equal probability on estimates
`-1` and `1`.  Its expected estimate is zero, just like the point mass at zero.
-/
noncomputable def lg21RandomizedCounterexampleSymmetricLaw :
    PMF LG21RandomizedCounterexampleEstimate :=
  lg21BinaryMixturePMF (1 / 2 : NNReal) (by norm_num)
    (PMF.pure .positive) (PMF.pure .negative)

/-- A binary mixture has mean zero when both component laws have mean zero. -/
theorem lg21_pmfExp_binaryMixture_eq_zero_of_component_means_zero
    {Estimate : Type*} [Fintype Estimate] [DecidableEq Estimate]
    (p : NNReal) (hp : p ≤ 1) (selected unselected : PMF Estimate)
    (value : Estimate → ℝ)
    (hselected : pmfExp selected value = 0)
    (hunselected : pmfExp unselected value = 0) :
    pmfExp (lg21BinaryMixturePMF p hp selected unselected) value = 0 := by
  change
    pmfExp (AppliedModelingLib.binaryMixturePMF p hp selected unselected) value = 0
  rw [AppliedModelingLib.binaryMixturePMF, pmfExp_bind]
  have hconditional :
      (fun selectedDraw : Bool =>
          pmfExp (if selectedDraw then selected else unselected) value) =
        fun _selectedDraw : Bool => 0 := by
    funext selectedDraw
    cases selectedDraw <;> simp [hselected, hunselected]
  rw [hconditional, pmfExp_zero]

@[simp] theorem lg21RandomizedCounterexampleZeroLaw_mean :
    pmfExp lg21RandomizedCounterexampleZeroLaw
      lg21RandomizedCounterexampleEstimateValue = 0 := by
  simp [lg21RandomizedCounterexampleZeroLaw,
    lg21RandomizedCounterexampleEstimateValue]

@[simp] theorem lg21RandomizedCounterexampleSymmetricLaw_mean :
    pmfExp lg21RandomizedCounterexampleSymmetricLaw
      lg21RandomizedCounterexampleEstimateValue = 0 := by
  classical
  unfold pmfExp
  rw [show
    (Finset.univ : Finset LG21RandomizedCounterexampleEstimate) =
      {.negative, .zero, .positive} by
        ext estimate
        cases estimate <;> simp]
  simp [lg21RandomizedCounterexampleSymmetricLaw,
    lg21BinaryMixturePMF_apply_toReal,
    lg21RandomizedCounterexampleEstimateValue, PMF.pure_apply]
  norm_num

/-- Both nonzero estimates have positive mass under the randomized law. -/
theorem lg21RandomizedCounterexampleSymmetricLaw_two_point_support :
    0 <
        (lg21RandomizedCounterexampleSymmetricLaw
          LG21RandomizedCounterexampleEstimate.negative).toReal ∧
      0 <
        (lg21RandomizedCounterexampleSymmetricLaw
          LG21RandomizedCounterexampleEstimate.positive).toReal := by
  have hnegativePositive :
      LG21RandomizedCounterexampleEstimate.negative ≠
        LG21RandomizedCounterexampleEstimate.positive := by
    decide
  have hpositiveNegative :
      LG21RandomizedCounterexampleEstimate.positive ≠
        LG21RandomizedCounterexampleEstimate.negative := by
    decide
  constructor <;>
    rw [lg21RandomizedCounterexampleSymmetricLaw,
      lg21BinaryMixturePMF_apply_toReal] <;>
    norm_num [PMF.pure_apply, hnegativePositive, hpositiveNegative]

/-- The randomized law is not the point mass at zero. -/
theorem lg21RandomizedCounterexampleSymmetricLaw_ne_zeroLaw :
    lg21RandomizedCounterexampleSymmetricLaw ≠
      lg21RandomizedCounterexampleZeroLaw := by
  intro h
  have hpositive :=
    lg21RandomizedCounterexampleSymmetricLaw_two_point_support.2
  rw [h] at hpositive
  simpa [lg21RandomizedCounterexampleZeroLaw, PMF.pure_apply] using hpositive

/-- Score-dependent randomized output law. -/
def lg21RandomizedCounterexampleReportedLaw
    (test : Bool) : PMF LG21RandomizedCounterexampleEstimate :=
  if test then
    lg21RandomizedCounterexampleSymmetricLaw
  else
    lg21RandomizedCounterexampleZeroLaw

@[simp] theorem lg21RandomizedCounterexampleReportedLaw_mean
    (test : Bool) :
    pmfExp (lg21RandomizedCounterexampleReportedLaw test)
      lg21RandomizedCounterexampleEstimateValue = 0 := by
  cases test <;>
    simp [lg21RandomizedCounterexampleReportedLaw]

/--
The aggregate reporter law under the two equiprobable test scores.  This is
the no-report/no-access resampling law in the all-report equilibrium.
-/
noncomputable def lg21RandomizedCounterexampleAggregateLaw :
    PMF LG21RandomizedCounterexampleEstimate :=
  lg21BinaryMixturePMF (1 / 2 : NNReal) (by norm_num)
    lg21RandomizedCounterexampleSymmetricLaw
    lg21RandomizedCounterexampleZeroLaw

@[simp] theorem lg21RandomizedCounterexampleAggregateLaw_mean :
    pmfExp lg21RandomizedCounterexampleAggregateLaw
      lg21RandomizedCounterexampleEstimateValue = 0 := by
  exact
    lg21_pmfExp_binaryMixture_eq_zero_of_component_means_zero
      (1 / 2 : NNReal) (by norm_num)
      lg21RandomizedCounterexampleSymmetricLaw
      lg21RandomizedCounterexampleZeroLaw
      lg21RandomizedCounterexampleEstimateValue
      lg21RandomizedCounterexampleSymmetricLaw_mean
      lg21RandomizedCounterexampleZeroLaw_mean

/-- The aggregate law differs from the low-score conditional output law. -/
theorem lg21RandomizedCounterexampleAggregateLaw_ne_zeroLaw :
    lg21RandomizedCounterexampleAggregateLaw ≠
      lg21RandomizedCounterexampleZeroLaw := by
  exact
    lg21BinaryMixturePMF_ne_noReporter_of_pos_of_ne
      (1 / 2 : NNReal) (by norm_num)
      lg21RandomizedCounterexampleSymmetricLaw
      lg21RandomizedCounterexampleZeroLaw
      (by norm_num)
      lg21RandomizedCounterexampleSymmetricLaw_ne_zeroLaw

/--
All pure feasible take/report patterns for the one-skill, one-base, two-score
counterexample.  `withhold` means take the test but report neither score.
-/
inductive LG21RandomizedCounterexampleEquilibrium where
  | noTake
  | withhold
  | reportLowOnly
  | reportHighOnly
  | reportAll
deriving DecidableEq, Fintype, Repr

/-- Test-taking decision in each pure pattern. -/
def lg21RandomizedCounterexampleTakes :
    LG21RandomizedCounterexampleEquilibrium → Bool
  | .noTake => false
  | .withhold => true
  | .reportLowOnly => true
  | .reportHighOnly => true
  | .reportAll => true

/-- Score-contingent reporting decision in each pure pattern. -/
def lg21RandomizedCounterexampleReports
    (e : LG21RandomizedCounterexampleEquilibrium) (test : Bool) : Bool :=
  match e, test with
  | .reportLowOnly, false => true
  | .reportHighOnly, true => true
  | .reportAll, _ => true
  | _, _ => false

/--
No-report law induced by the policy's resampling rule.  When there are
reporters, it is their aggregate output law; when there are none, the policy
uses the zero law.  Every listed law has expected estimate zero.
-/
def lg21RandomizedCounterexampleNoReportLaw
    (e : LG21RandomizedCounterexampleEquilibrium) :
    PMF LG21RandomizedCounterexampleEstimate :=
  match e with
  | .noTake => lg21RandomizedCounterexampleZeroLaw
  | .withhold => lg21RandomizedCounterexampleZeroLaw
  | .reportLowOnly => lg21RandomizedCounterexampleZeroLaw
  | .reportHighOnly => lg21RandomizedCounterexampleSymmetricLaw
  | .reportAll => lg21RandomizedCounterexampleAggregateLaw

@[simp] theorem lg21RandomizedCounterexampleNoReportLaw_mean
    (e : LG21RandomizedCounterexampleEquilibrium) :
    pmfExp (lg21RandomizedCounterexampleNoReportLaw e)
      lg21RandomizedCounterexampleEstimateValue = 0 := by
  cases e <;>
    simp [lg21RandomizedCounterexampleNoReportLaw]

/--
Estimate law of an access student with realized test score `test`: reported
scores use their score-dependent randomized law; nonreporters receive the
equilibrium's resampled no-report law.
-/
def lg21RandomizedCounterexampleOperationalLaw
    (e : LG21RandomizedCounterexampleEquilibrium) (test : Bool) :
    PMF LG21RandomizedCounterexampleEstimate :=
  if lg21RandomizedCounterexampleReports e test = true then
    lg21RandomizedCounterexampleReportedLaw test
  else
    lg21RandomizedCounterexampleNoReportLaw e

@[simp] theorem lg21RandomizedCounterexampleOperationalLaw_mean
    (e : LG21RandomizedCounterexampleEquilibrium) (test : Bool) :
    pmfExp (lg21RandomizedCounterexampleOperationalLaw e test)
      lg21RandomizedCounterexampleEstimateValue = 0 := by
  by_cases hreport :
      lg21RandomizedCounterexampleReports e test = true
  · simp [lg21RandomizedCounterexampleOperationalLaw, hreport]
  · simp [lg21RandomizedCounterexampleOperationalLaw, hreport]

/--
Actual access-side estimate law, averaging the operational law over the two
equiprobable scores when the test is taken.
-/
noncomputable def lg21RandomizedCounterexampleAccessLaw
    (e : LG21RandomizedCounterexampleEquilibrium) :
    PMF LG21RandomizedCounterexampleEstimate :=
  if lg21RandomizedCounterexampleTakes e = true then
    lg21BinaryMixturePMF (1 / 2 : NNReal) (by norm_num)
      (lg21RandomizedCounterexampleOperationalLaw e true)
      (lg21RandomizedCounterexampleOperationalLaw e false)
  else
    lg21RandomizedCounterexampleNoReportLaw e

/-- A half-and-half mixture of a law with itself is that law. -/
theorem lg21RandomizedCounterexample_half_mixture_self
    (law : PMF LG21RandomizedCounterexampleEstimate) :
    lg21BinaryMixturePMF (1 / 2 : NNReal) (by norm_num) law law = law :=
  lg21BinaryMixturePMF_eq_noReporter_of_eq
    (1 / 2 : NNReal) (by norm_num) law law rfl

/--
For every pure equilibrium pattern, the access law equals the resampled
no-access law.  This is the observable-fairness identity, not a stipulated
surface equality.
-/
theorem lg21RandomizedCounterexampleAccessLaw_eq_noReportLaw
    (e : LG21RandomizedCounterexampleEquilibrium) :
    lg21RandomizedCounterexampleAccessLaw e =
      lg21RandomizedCounterexampleNoReportLaw e := by
  cases e with
  | noTake => rfl
  | withhold =>
      simpa only [lg21RandomizedCounterexampleAccessLaw,
        lg21RandomizedCounterexampleTakes, if_true,
        lg21RandomizedCounterexampleOperationalLaw,
        lg21RandomizedCounterexampleReports,
        lg21RandomizedCounterexampleNoReportLaw, Bool.false_eq_true,
        if_false] using
          lg21RandomizedCounterexample_half_mixture_self
            lg21RandomizedCounterexampleZeroLaw
  | reportLowOnly =>
      simpa only [lg21RandomizedCounterexampleAccessLaw,
        lg21RandomizedCounterexampleTakes, if_true,
        lg21RandomizedCounterexampleOperationalLaw,
        lg21RandomizedCounterexampleReports,
        lg21RandomizedCounterexampleReportedLaw,
        lg21RandomizedCounterexampleNoReportLaw, Bool.false_eq_true,
        if_false] using
          lg21RandomizedCounterexample_half_mixture_self
            lg21RandomizedCounterexampleZeroLaw
  | reportHighOnly =>
      simpa only [lg21RandomizedCounterexampleAccessLaw,
        lg21RandomizedCounterexampleTakes, if_true,
        lg21RandomizedCounterexampleOperationalLaw,
        lg21RandomizedCounterexampleReports,
        lg21RandomizedCounterexampleReportedLaw,
        lg21RandomizedCounterexampleNoReportLaw, Bool.false_eq_true,
        if_false] using
          lg21RandomizedCounterexample_half_mixture_self
            lg21RandomizedCounterexampleSymmetricLaw
  | reportAll => rfl

/--
Definition 1 data for any pure pattern.  Payoff is the expected school
estimate under the randomized policy, exactly as required by the source's
equilibrium definition.
-/
def lg21RandomizedCounterexampleSourceEquilibriumData
    (e : LG21RandomizedCounterexampleEquilibrium) :
    LG21SourceEquilibriumData PUnit PUnit Bool where
  requirement := LG21AccessAction.optionalReportingRequirement
  takeDecision := fun _skill _base =>
    lg21RandomizedCounterexampleTakes e
  reportDecision := fun _base test =>
    lg21RandomizedCounterexampleReports e test
  payoff := fun info action =>
    if action.reportsScore = true then
      pmfExp (lg21RandomizedCounterexampleReportedLaw info.test)
        lg21RandomizedCounterexampleEstimateValue
    else
      pmfExp (lg21RandomizedCounterexampleNoReportLaw e)
        lg21RandomizedCounterexampleEstimateValue
  estimationConsistent := True

@[simp] theorem lg21RandomizedCounterexampleSourceEquilibriumData_payoff
    (e : LG21RandomizedCounterexampleEquilibrium)
    (info : LG21AccessStudentInfo PUnit PUnit Bool)
    (action : LG21AccessAction) :
    (lg21RandomizedCounterexampleSourceEquilibriumData e).payoff info action =
      0 := by
  simp [lg21RandomizedCounterexampleSourceEquilibriumData]

/-- Every pure feasible take/report pattern is a Definition 1 equilibrium. -/
theorem lg21RandomizedCounterexample_every_pattern_source_equilibrium
    (e : LG21RandomizedCounterexampleEquilibrium) :
    lg21SourceEquilibrium
      (lg21RandomizedCounterexampleSourceEquilibriumData e) := by
  rw [lg21SourceEquilibrium_iff]
  refine ⟨?_, ?_, trivial⟩
  · rintro ⟨⟨⟩, ⟨⟩, test⟩
    cases e <;> cases test <;>
      simp [lg21RandomizedCounterexampleSourceEquilibriumData,
        LG21AccessStudentInfo.chosenAction,
        LG21AccessAction.feasible,
        LG21AccessAction.reportImpliesTake,
        LG21AccessAction.optionalReportingRequirement,
        lg21RandomizedCounterexampleTakes,
        lg21RandomizedCounterexampleReports]
  · intro info action _hfeasible
    rw [lg21RandomizedCounterexampleSourceEquilibriumData_payoff]
    rw [lg21RandomizedCounterexampleSourceEquilibriumData_payoff]

/--
Policy surface generated by the counterexample's actual access and no-access
laws.  Its equilibrium type enumerates every pure feasible strategy pattern.
-/
noncomputable def lg21RandomizedPolicyCounterexampleSurface :
    LG21SourcePolicySurface
      PUnit PUnit Bool LG21RandomizedCounterexampleEstimate where
  Equilibrium := LG21RandomizedCounterexampleEquilibrium
  latentAccessEstimate := fun e _skill _base =>
    lg21RandomizedCounterexampleAccessLaw e
  latentNoAccessEstimate := fun e _skill _base =>
    lg21RandomizedCounterexampleNoReportLaw e
  observableAccessEstimate := fun e _base =>
    lg21RandomizedCounterexampleAccessLaw e
  observableNoAccessEstimate := fun e _base =>
    lg21RandomizedCounterexampleNoReportLaw e
  demographicAccessEstimate := fun e =>
    lg21RandomizedCounterexampleAccessLaw e
  demographicNoAccessEstimate := fun e =>
    lg21RandomizedCounterexampleNoReportLaw e
  baseOnlyEstimate := fun e _base =>
    lg21RandomizedCounterexampleNoReportLaw e
  fullFeatureEstimate := fun _e _base test =>
    lg21RandomizedCounterexampleReportedLaw test

/-- The policy is latent-skill fair in every pure equilibrium. -/
theorem lg21RandomizedPolicyCounterexample_latentSkillFair :
    lg21SourceLatentSkillFair lg21RandomizedPolicyCounterexampleSurface := by
  intro e _skill _base
  exact lg21RandomizedCounterexampleAccessLaw_eq_noReportLaw e

/-- The policy is observably fair in every pure equilibrium. -/
theorem lg21RandomizedPolicyCounterexample_observablyFair :
    lg21SourceObservablyFair lg21RandomizedPolicyCounterexampleSurface := by
  intro e _base
  exact lg21RandomizedCounterexampleAccessLaw_eq_noReportLaw e

/-- The policy is demographically fair in every pure equilibrium. -/
theorem lg21RandomizedPolicyCounterexample_demographicallyFair :
    lg21SourceDemographicallyFair
      lg21RandomizedPolicyCounterexampleSurface := by
  intro e
  exact lg21RandomizedCounterexampleAccessLaw_eq_noReportLaw e

/--
The policy is not test-blank: in the all-report equilibrium, the low-score
conditional law is the zero point mass, whereas the base-only law is the
nontrivial aggregate of the low- and high-score output laws.
-/
theorem lg21RandomizedPolicyCounterexample_not_testBlank :
    ¬ lg21SourceTestBlank lg21RandomizedPolicyCounterexampleSurface := by
  intro hblank
  have h := hblank
    LG21RandomizedCounterexampleEquilibrium.reportAll PUnit.unit false
  exact lg21RandomizedCounterexampleAggregateLaw_ne_zeroLaw h

/--
Abstract finite countermodel to the corresponding unrestricted policy-surface
implication.  This theorem deliberately carries no paper-facing `paper_`
prefix: the inherited Gaussian source-domain counterexample is proved only in
`Theorem32GaussianKernelCounterexample`.
-/
theorem lg21_abstract_finite_randomized_policy_countermodel :
    (∀ e : LG21RandomizedCounterexampleEquilibrium,
      lg21SourceEquilibrium
        (lg21RandomizedCounterexampleSourceEquilibriumData e)) ∧
      lg21SourceLatentSkillFair lg21RandomizedPolicyCounterexampleSurface ∧
      lg21SourceObservablyFair lg21RandomizedPolicyCounterexampleSurface ∧
      ¬ lg21SourceTestBlank lg21RandomizedPolicyCounterexampleSurface := by
  exact ⟨lg21RandomizedCounterexample_every_pattern_source_equilibrium,
    lg21RandomizedPolicyCounterexample_latentSkillFair,
    lg21RandomizedPolicyCounterexample_observablyFair,
    lg21RandomizedPolicyCounterexample_not_testBlank⟩

/-! ## Repaired theorem: expected estimates identify output laws -/

/--
Policy-local identifiability condition: equality of expected estimates between
the base-only and full-feature laws forces equality of the laws themselves.
Deterministic point-estimate policies satisfy this condition (under an
injective numerical encoding); unrestricted randomized policies need not.
-/
def LG21ExpectedEstimateIdentifiesPolicyLaw
    {Skill Base Test Estimate : Type*}
    [Fintype Estimate] [DecidableEq Estimate]
    (S : LG21SourcePolicySurface Skill Base Test Estimate)
    (estimateValue : Estimate → ℝ) : Prop :=
  ∀ e base test,
    pmfExp (S.baseOnlyEstimate e base) estimateValue =
        pmfExp (S.fullFeatureEstimate e base test) estimateValue →
      S.baseOnlyEstimate e base = S.fullFeatureEstimate e base test

/--
Dual of the standard strict finite-expectation lemma: if all values are at
least `c` and one positive-mass value is strictly larger, the expectation is
strictly larger than `c`.
-/
theorem lg21_pmfExp_gt_const_of_forall_ge_exists_gt
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (value : Outcome → ℝ) (c : ℝ)
    (hge : ∀ outcome, c ≤ value outcome)
    (hexists : ∃ outcome,
      0 < (law outcome).toReal ∧ c < value outcome) :
    c < pmfExp law value := by
  have hneg :
      pmfExp law (fun outcome => -value outcome) < -c :=
    pmfExp_lt_of_forall_le_exists_lt law (fun outcome => -value outcome) (-c)
      (fun outcome => neg_le_neg (hge outcome))
      (by
        rcases hexists with ⟨outcome, hmass, hstrict⟩
        exact ⟨outcome, hmass, neg_lt_neg hstrict⟩)
  rw [pmfExp_neg] at hneg
  linarith

/--
Corrected finite-policy Theorem 3.2.

The access estimate law is the mixture of the operational full-feature laws
over a full-support test law; the no-access law is the base-only law.  Weak
best response says every operational test outcome has expected estimate at
least the base-only estimate.  Observable fairness equates the average with
the base-only law, so no positive-mass test can have a strictly higher mean.
Mean-identifiability then upgrades equality of means to equality of laws,
which is exactly test-blankness.

Unlike the source proof, this theorem never replaces an arbitrary policy by
the Bayesian posterior formula.
-/
theorem paper_theorem3_2_observable_fair_implies_test_blank_of_mean_identifiable_policy
    {Skill Base Test Estimate : Type*}
    [Fintype Test] [DecidableEq Test]
    [Fintype Estimate] [DecidableEq Estimate]
    {S : LG21SourcePolicySurface Skill Base Test Estimate}
    (testLaw : S.Equilibrium → Base → PMF Test)
    (estimateValue : Estimate → ℝ)
    (hfullSupport :
      ∀ e base test, 0 < (testLaw e base test).toReal)
    (hAccessMixture :
      ∀ e base,
        S.observableAccessEstimate e base =
          (testLaw e base).bind (S.fullFeatureEstimate e base))
    (hNoAccessBaseOnly :
      ∀ e base,
        S.observableNoAccessEstimate e base =
          S.baseOnlyEstimate e base)
    (hWeakBestResponse :
      ∀ e base test,
        pmfExp (S.baseOnlyEstimate e base) estimateValue ≤
          pmfExp (S.fullFeatureEstimate e base test) estimateValue)
    (hIdentifies :
      LG21ExpectedEstimateIdentifiesPolicyLaw S estimateValue) :
    lg21SourceObservablyFair S → lg21SourceTestBlank S := by
  intro hfair e base test
  let baseMean := pmfExp (S.baseOnlyEstimate e base) estimateValue
  let fullMean : Test → ℝ := fun test =>
    pmfExp (S.fullFeatureEstimate e base test) estimateValue
  have hLawMixture :
      (testLaw e base).bind (S.fullFeatureEstimate e base) =
        S.baseOnlyEstimate e base := by
    calc
      (testLaw e base).bind (S.fullFeatureEstimate e base) =
          S.observableAccessEstimate e base :=
        (hAccessMixture e base).symm
      _ = S.observableNoAccessEstimate e base := hfair e base
      _ = S.baseOnlyEstimate e base := hNoAccessBaseOnly e base
  have hMeanMixture :
      pmfExp (testLaw e base) fullMean = baseMean := by
    calc
      pmfExp (testLaw e base) fullMean =
          pmfExp
            ((testLaw e base).bind (S.fullFeatureEstimate e base))
            estimateValue := by
        exact
          (pmfExp_bind (testLaw e base)
            (S.fullFeatureEstimate e base) estimateValue).symm
      _ = pmfExp (S.baseOnlyEstimate e base) estimateValue := by
        rw [hLawMixture]
      _ = baseMean := rfl
  have hbase_le : baseMean ≤ fullMean test :=
    hWeakBestResponse e base test
  have hfull_le : fullMean test ≤ baseMean := by
    by_contra hnot
    have hstrict : baseMean < fullMean test := lt_of_not_ge hnot
    have havg_strict : baseMean < pmfExp (testLaw e base) fullMean :=
      lg21_pmfExp_gt_const_of_forall_ge_exists_gt
        (testLaw e base) fullMean baseMean
        (hWeakBestResponse e base)
        ⟨test, hfullSupport e base test, hstrict⟩
    linarith
  exact hIdentifies e base test (le_antisymm hbase_le hfull_le)

/--
Deterministic point-estimate corollary of the repaired theorem.  Injectivity of
the numerical estimate encoding makes point-mass laws mean-identifiable.
-/
theorem paper_theorem3_2_observable_fair_implies_test_blank_of_deterministic_policy
    {Skill Base Test Estimate : Type*}
    [Fintype Test] [DecidableEq Test]
    [Fintype Estimate] [DecidableEq Estimate]
    {S : LG21SourcePolicySurface Skill Base Test Estimate}
    (testLaw : S.Equilibrium → Base → PMF Test)
    (estimateValue : Estimate → ℝ)
    (hvalueInjective : Function.Injective estimateValue)
    (baseValue : S.Equilibrium → Base → Estimate)
    (fullValue : S.Equilibrium → Base → Test → Estimate)
    (hBasePoint :
      ∀ e base,
        S.baseOnlyEstimate e base = PMF.pure (baseValue e base))
    (hFullPoint :
      ∀ e base test,
        S.fullFeatureEstimate e base test =
          PMF.pure (fullValue e base test))
    (hfullSupport :
      ∀ e base test, 0 < (testLaw e base test).toReal)
    (hAccessMixture :
      ∀ e base,
        S.observableAccessEstimate e base =
          (testLaw e base).bind (S.fullFeatureEstimate e base))
    (hNoAccessBaseOnly :
      ∀ e base,
        S.observableNoAccessEstimate e base =
          S.baseOnlyEstimate e base)
    (hWeakBestResponse :
      ∀ e base test,
        pmfExp (S.baseOnlyEstimate e base) estimateValue ≤
          pmfExp (S.fullFeatureEstimate e base test) estimateValue) :
    lg21SourceObservablyFair S → lg21SourceTestBlank S := by
  apply
    paper_theorem3_2_observable_fair_implies_test_blank_of_mean_identifiable_policy
      testLaw estimateValue hfullSupport hAccessMixture hNoAccessBaseOnly
      hWeakBestResponse
  intro e base test hmean
  have hvalue : baseValue e base = fullValue e base test := by
    apply hvalueInjective
    simpa [hBasePoint e base, hFullPoint e base test] using hmean
  rw [hBasePoint e base, hFullPoint e base test, hvalue]

/--
The counterexample pinpoints the missing repair hypothesis: its base-only and
low-score laws have the same expected estimate but are different laws.
-/
theorem lg21RandomizedPolicyCounterexample_not_mean_identifiable :
    ¬ LG21ExpectedEstimateIdentifiesPolicyLaw
      lg21RandomizedPolicyCounterexampleSurface
      lg21RandomizedCounterexampleEstimateValue := by
  intro hidentifies
  have heq := hidentifies
    LG21RandomizedCounterexampleEquilibrium.reportAll PUnit.unit false
    (by
      simp [lg21RandomizedPolicyCounterexampleSurface,
        lg21RandomizedCounterexampleNoReportLaw,
        lg21RandomizedCounterexampleReportedLaw])
  exact lg21RandomizedCounterexampleAggregateLaw_ne_zeroLaw heq

end

end LG21TestOptionalPolicies
