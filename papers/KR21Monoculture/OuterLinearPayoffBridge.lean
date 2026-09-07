import KR21Monoculture.Distributional
import KR21Monoculture.MallowsFamily
import AppliedModelingLib.Foundations.Probability.IndependentProduct

open AppliedModelingLib MeasureTheory

namespace KR21Monoculture

/-!
# Finite ranking-payoff bridge for the outer value distribution

For ranking laws that do not depend on the realized cardinal values (notably
the Mallows family in KR21), every finite PMF payoff is linear in the value
profile.  This module records the exact Fubini-free finite-sum interchange
needed to reduce an outer value distribution to its coordinatewise mean.

It deliberately proves only the linear finite-PMF bridge.  The source's
strict-order support and the subsequent Mallows crossing argument remain
separate obligations.
-/

/-- Coordinatewise mean of the paper's outer candidate-value distribution. -/
noncomputable def outerMeanValue {n : ℕ} (D : Measure (ValueProfile n)) :
    ValueProfile n :=
  fun c => ∫ value, value c ∂D

/-- Coordinatewise mean of a value profile sampled from an arbitrary outer
source space. -/
noncomputable def outerMeanValueOf {n : ℕ} {Omega : Type*}
    [MeasurableSpace Omega] (D : Measure Omega)
    (value : Omega → ValueProfile n) : ValueProfile n :=
  fun c => ∫ omega, value omega c ∂D

/-- A finite PMF expectation selecting one coordinate is integrable whenever
every value coordinate is integrable. -/
theorem integrable_pmfExp_valueSelection
    {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (D : Measure (ValueProfile n)) (mu : PMF α)
    (select : α → Candidate n)
    (hvalue : ∀ c : Candidate n, Integrable (fun value : ValueProfile n => value c) D) :
    Integrable (fun value => pmfExp mu (fun a => value (select a))) D := by
  unfold pmfExp
  refine MeasureTheory.integrable_finset_sum Finset.univ ?_
  intro a _
  exact (hvalue (select a)).const_mul _

/-- Finite PMF expectation commutes with the outer integral for a selected
candidate coordinate. -/
theorem integral_pmfExp_valueSelection_eq_outerMean
    {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (D : Measure (ValueProfile n)) (mu : PMF α)
    (select : α → Candidate n)
    (hvalue : ∀ c : Candidate n, Integrable (fun value : ValueProfile n => value c) D) :
    (∫ value, pmfExp mu (fun a => value (select a)) ∂D) =
      pmfExp mu (fun a => outerMeanValue D (select a)) := by
  unfold pmfExp outerMeanValue
  rw [MeasureTheory.integral_finset_sum]
  · refine Finset.sum_congr rfl ?_
    intro a _
    rw [MeasureTheory.integral_const_mul]
  · intro a _
    exact (hvalue (select a)).const_mul _

/-- A finite independent-pair PMF expectation selecting one value coordinate
is integrable under coordinatewise outer integrability. -/
theorem integrable_pmfPairExp_valueSelection
    {n : ℕ} {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (D : Measure (ValueProfile n)) (mu : PMF α) (nu : PMF β)
    (select : α → β → Candidate n)
    (hvalue : ∀ c : Candidate n, Integrable (fun value : ValueProfile n => value c) D) :
    Integrable (fun value => pmfPairExp mu nu (fun a b => value (select a b))) D := by
  have h := integrable_pmfExp_valueSelection D (AppliedModelingLib.pmfProd mu nu)
    (fun pair => select pair.1 pair.2) hvalue
  simpa only [AppliedModelingLib.pmfExp_pmfProd_eq_pairExp, Prod.fst, Prod.snd] using h

/-- Finite independent-pair PMF expectation commutes with the outer integral
for a selected candidate coordinate. -/
theorem integral_pmfPairExp_valueSelection_eq_outerMean
    {n : ℕ} {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (D : Measure (ValueProfile n)) (mu : PMF α) (nu : PMF β)
    (select : α → β → Candidate n)
    (hvalue : ∀ c : Candidate n, Integrable (fun value : ValueProfile n => value c) D) :
    (∫ value, pmfPairExp mu nu (fun a b => value (select a b)) ∂D) =
      pmfPairExp mu nu (fun a b => outerMeanValue D (select a b)) := by
  have h := integral_pmfExp_valueSelection_eq_outerMean D (AppliedModelingLib.pmfProd mu nu)
    (fun pair => select pair.1 pair.2) hvalue
  simpa only [AppliedModelingLib.pmfExp_pmfProd_eq_pairExp, Prod.fst, Prod.snd] using h

/-- The outer first-mover payoff under a fixed ranking law is exactly the
first-mover payoff of the coordinatewise mean profile. -/
theorem outerExpected_expectedFirstMoverUtility_eq_outerMean
    {n : ℕ} (D : Measure (ValueProfile n)) (mu : PMF (Ranking n))
    (hvalue : ∀ c : Candidate n, Integrable (fun value : ValueProfile n => value c) D) :
    DistributionalAccuracyFamily.outerExpected D
        (fun value => expectedFirstMoverUtility mu value) =
      expectedFirstMoverUtility mu (outerMeanValue D) := by
  exact integral_pmfExp_valueSelection_eq_outerMean D mu firstChoice hvalue

/-- The outer shared-second-mover payoff under a fixed ranking law is exactly
the shared payoff of the coordinatewise mean profile. -/
theorem outerExpected_expectedSecondMoverShared_eq_outerMean
    {n : ℕ} (D : Measure (ValueProfile n)) (mu : PMF (Ranking n))
    (hvalue : ∀ c : Candidate n, Integrable (fun value : ValueProfile n => value c) D) :
    DistributionalAccuracyFamily.outerExpected D
        (fun value => expectedSecondMoverShared mu value) =
      expectedSecondMoverShared mu (outerMeanValue D) := by
  exact integral_pmfExp_valueSelection_eq_outerMean D mu secondChoice hvalue

/-- The outer independent-second-mover payoff under fixed ranking laws is
exactly the independent payoff of the coordinatewise mean profile. -/
theorem outerExpected_expectedSecondMoverIndependent_eq_outerMean
    {n : ℕ} (D : Measure (ValueProfile n))
    (muSecond muFirst : PMF (Ranking n))
    (hvalue : ∀ c : Candidate n, Integrable (fun value : ValueProfile n => value c) D) :
    DistributionalAccuracyFamily.outerExpected D
        (fun value => expectedSecondMoverIndependent muSecond muFirst value) =
      expectedSecondMoverIndependent muSecond muFirst (outerMeanValue D) := by
  exact integral_pmfPairExp_valueSelection_eq_outerMean D muSecond muFirst
    (fun second first => bestRemainingAfter second (firstChoice first)) hvalue

/-- The generic outer-source form of finite selected-coordinate integrability. -/
theorem integrable_pmfExp_outerValueSelection
    {n : ℕ} {Omega α : Type*} [MeasurableSpace Omega]
    [Fintype α] [DecidableEq α]
    (D : Measure Omega) (value : Omega → ValueProfile n) (mu : PMF α)
    (select : α → Candidate n)
    (hvalue : ∀ c : Candidate n, Integrable (fun omega => value omega c) D) :
    Integrable (fun omega => pmfExp mu (fun a => value omega (select a))) D := by
  unfold pmfExp
  refine MeasureTheory.integrable_finset_sum Finset.univ ?_
  intro a _
  exact (hvalue (select a)).const_mul _

/-- The generic outer-source form of independent-pair selected-coordinate
integrability. -/
theorem integrable_pmfPairExp_outerValueSelection
    {n : ℕ} {Omega α β : Type*} [MeasurableSpace Omega]
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (D : Measure Omega) (value : Omega → ValueProfile n)
    (mu : PMF α) (nu : PMF β) (select : α → β → Candidate n)
    (hvalue : ∀ c : Candidate n, Integrable (fun omega => value omega c) D) :
    Integrable (fun omega =>
      pmfPairExp mu nu (fun a b => value omega (select a b))) D := by
  have h := integrable_pmfExp_outerValueSelection D value
    (AppliedModelingLib.pmfProd mu nu) (fun pair => select pair.1 pair.2) hvalue
  simpa only [AppliedModelingLib.pmfExp_pmfProd_eq_pairExp, Prod.fst, Prod.snd] using h

/-- A source-faithful outer-D Mallows condition bridge.  Fixed Mallows laws are
independent of the realized cardinal value profile, so coordinatewise
integrability alone discharges the four payoff-integrability obligations in the
existing D-averaged Theorem 3 comparison. -/
theorem theorem3_mallows_outer_conditions_of_coordinate_integrable
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (value : Omega → ValueProfile n) (C : MallowsComparison n)
    (D : Measure Omega) [IsProbabilityMeasure D]
    (hstrict : ∀ omega, C.StrictlyCenterOrdered (value omega))
    (hn : 0 < n)
    (halg_q_lt_one : C.algorithm.q < 1)
    (hhuman_q_lt_one : C.human.q < 1)
    (hq_lt : C.algorithm.q < C.human.q)
    (hvalue : ∀ c : Candidate n, Integrable (fun omega => value omega c) D) :
    (∫ omega, expectedSecondMoverShared C.algorithm.law (value omega) ∂D) <
        ∫ omega, expectedSecondMoverIndependent
          C.algorithm.law C.algorithm.law (value omega) ∂D ∧
      (∫ omega, expectedSecondMoverIndependent
          C.human.law C.algorithm.law (value omega) ∂D) <
        ∫ omega, expectedSecondMoverIndependent
          C.human.law C.human.law (value omega) ∂D := by
  constructor
  · exact AppliedModelingLib.integral_lt_integral_of_forall_lt D
      (integrable_pmfExp_outerValueSelection D value C.algorithm.law secondChoice hvalue)
      (integrable_pmfPairExp_outerValueSelection D value C.algorithm.law
        C.algorithm.law
        (fun second first => bestRemainingAfter second (firstChoice first)) hvalue)
      (fun omega =>
        (C.theorem3_pointwise_of_rankFactorization
          (hstrict omega) hn C.algorithm.rankFactorization C.human.rankFactorization
          halg_q_lt_one hhuman_q_lt_one hq_lt).1)
  · exact AppliedModelingLib.integral_lt_integral_of_forall_lt D
      (integrable_pmfPairExp_outerValueSelection D value C.human.law
        C.algorithm.law
        (fun second first => bestRemainingAfter second (firstChoice first)) hvalue)
      (integrable_pmfPairExp_outerValueSelection D value C.human.law
        C.human.law
        (fun second first => bestRemainingAfter second (firstChoice first)) hvalue)
      (fun omega =>
        (C.theorem3_pointwise_of_rankFactorization
          (hstrict omega) hn C.algorithm.rankFactorization C.human.rankFactorization
          halg_q_lt_one hhuman_q_lt_one hq_lt).2)

end KR21Monoculture
